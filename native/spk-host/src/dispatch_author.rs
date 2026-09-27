//! Fixed-participant authoring for the private Mini operator route. The Host
//! derives signing headers from the current image; this module compares every
//! source slot to an operator-pinned key before signing exact header bytes.
//! Neither an HTTP request nor a Host plan chooses a new signer.
#![allow(dead_code)] // Joined operator broker/supervisor route is in progress.

use crate::dispatch_inspection::{app_route_path, HttpProjection, Route};
use ed25519_dalek::{Signer, SigningKey};
use serde::Deserialize;
use serde_json::{json, Value};
use std::fs::{self, File};
use std::io::{self, Read};
use std::os::unix::fs::{MetadataExt, PermissionsExt};
use std::path::{Path, PathBuf};

fn invalid(reason: &'static str) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidData, reason)
}

fn canonical_decimal(value: &str) -> bool {
    !value.is_empty()
        && value.len() <= 128
        && (value == "0" || !value.starts_with('0'))
        && value.bytes().all(|byte| byte.is_ascii_digit())
}

fn hex(bytes: &[u8]) -> String {
    let mut result = String::with_capacity(bytes.len() * 2);
    for byte in bytes {
        use std::fmt::Write as _;
        write!(result, "{byte:02x}").expect("writing to String");
    }
    result
}

fn unhex(value: &str) -> io::Result<Vec<u8>> {
    if !value.len().is_multiple_of(2)
        || !value
            .bytes()
            .all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(&b))
    {
        return Err(invalid("noncanonical lowercase hex"));
    }
    value
        .as_bytes()
        .as_chunks::<2>()
        .0
        .iter()
        .map(|pair| {
            let text = std::str::from_utf8(pair).map_err(|_| invalid("invalid hex pair"))?;
            u8::from_str_radix(text, 16).map_err(|_| invalid("invalid hex pair"))
        })
        .collect()
}

fn field<'a>(value: &'a Value, name: &str) -> io::Result<&'a str> {
    value
        .get(name)
        .and_then(Value::as_str)
        .ok_or_else(|| invalid("source plan field missing or not text"))
}

#[derive(Clone, Debug, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub(crate) struct SignerPin {
    pub role: String,
    pub index: String,
    pub key_id: String,
    pub key_epoch: String,
    pub public_key_hex: String,
    pub seed_path: PathBuf,
}

#[derive(Clone, Debug, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub(crate) struct FixedAuthoring {
    pub protocol: String,
    pub app: String,
    pub subject: String,
    pub session: String,
    /// Fixed Mini session kind for this custodian, independent of token text.
    pub session_kind: String,
    pub issue_index: String,
    pub ticket_resource: String,
    pub package_manifest: String,
    pub snapshot_manifest: String,
    pub session_observe_capability: String,
    pub manifest_observe_capability: String,
    pub enrollment_observe_capability: String,
    pub signers: Vec<SignerPin>,
}

impl FixedAuthoring {
    pub(crate) fn validate(&self) -> io::Result<()> {
        if self.protocol != "mini-spk-human-dispatch-custody-v1"
            || !matches!(self.session_kind.as_str(), "web" | "api")
            || self.signers.is_empty()
            || self.signers.len() > 64
            || ![
                &self.app,
                &self.subject,
                &self.session,
                &self.issue_index,
                &self.ticket_resource,
                &self.package_manifest,
                &self.snapshot_manifest,
                &self.session_observe_capability,
                &self.manifest_observe_capability,
                &self.enrollment_observe_capability,
            ]
            .iter()
            .all(|value| canonical_decimal(value))
        {
            return Err(invalid("fixed dispatch authoring coordinate refused"));
        }
        for (index, pin) in self.signers.iter().enumerate() {
            if !canonical_decimal(&pin.role)
                || !canonical_decimal(&pin.index)
                || !canonical_decimal(&pin.key_id)
                || !canonical_decimal(&pin.key_epoch)
                || pin.public_key_hex.len() != 64
                || unhex(&pin.public_key_hex).is_err()
                || !pin.seed_path.is_absolute()
                || self.signers[..index]
                    .iter()
                    .any(|prior| prior.role == pin.role && prior.index == pin.index)
            {
                return Err(invalid("fixed dispatch signer pin refused"));
            }
        }
        Ok(())
    }

    /// The native `author application-dispatch-request` route encodes this
    /// strict JSON into the source-owned request codec before op36.
    pub(crate) fn request_json(
        &self,
        operation_id: &str,
        http: &HttpProjection<'_>,
    ) -> io::Result<Value> {
        self.validate()?;
        if !matches!(
            (self.session_kind.as_str(), http.route),
            ("web", Route::Browser) | ("api", Route::Api { .. })
        ) {
            return Err(invalid("HTTP route differs from fixed Mini session kind"));
        }
        if !canonical_decimal(operation_id) {
            return Err(invalid("physical operation ID is not canonical"));
        }
        let (path, query) = app_route_path(http)?;
        let headers: Vec<_> = http
            .ordered_headers
            .iter()
            .map(|(name, value)| {
                json!({"nameHex":hex(name.as_bytes()),"valueHex":hex(value.as_bytes()),
                    "generated":false})
            })
            .collect();
        Ok(json!({
            "issueIndex":self.issue_index,"ticketResource":self.ticket_resource,
            "packageManifest":self.package_manifest,"snapshotManifest":self.snapshot_manifest,
            "sessionObserveCapability":self.session_observe_capability,
            "manifestObserveCapability":self.manifest_observe_capability,
            "enrollmentObserveCapability":self.enrollment_observe_capability,
            "http":{"operationId":operation_id,"methodHex":hex(http.method.as_bytes()),
                "pathHex":hex(path.as_bytes()),"queryHex":hex(query.as_bytes()),
                "headers":headers,"bodyHex":hex(http.body)}
        }))
    }

    /// Mini's private inspector decodes the exact op36 plan. Check its exact
    /// plan echo and all signer slots before reading a seed or signing any
    /// header. The resulting JSON signature list goes through Host's strict
    /// `signatures` codec and op37; no local codec substitutes for Mini.
    pub(crate) fn sign_plan(
        &self,
        plan_bytes: &[u8],
        inspection: &[u8],
        request_bytes: &[u8],
        request: &Value,
    ) -> io::Result<Value> {
        self.validate()?;
        if plan_bytes.is_empty() || plan_bytes.len() >= 12_102_760 || inspection.len() > 96_822_080
        {
            return Err(invalid("source authoring plan bound refused"));
        }
        let plan: Value = serde_json::from_slice(inspection)?;
        let source_request = plan
            .get("request")
            .and_then(Value::as_object)
            .ok_or_else(|| invalid("source plan lacks decoded request"))?;
        let mut comparable_request = source_request.clone();
        let request_type = comparable_request.remove("type");
        let canonical_request = comparable_request.remove("canonicalRequest");
        if field(&plan, "type")? != "application-dispatch-author-plan-v1"
            || field(&plan, "canonicalPlan")? != hex(plan_bytes)
            || request_type.as_ref().and_then(Value::as_str)
                != Some("application-dispatch-author-request-v1")
            || canonical_request.as_ref().and_then(Value::as_str)
                != Some(hex(request_bytes).as_str())
            || Value::Object(comparable_request) != *request
            || field(&plan, "appResource")? != self.app
            || field(&plan, "sessionResource")? != self.session
            || field(&plan, "subject")? != self.subject
        {
            return Err(invalid("source plan differs from fixed dispatch request"));
        }
        let slots = plan
            .get("slots")
            .and_then(Value::as_array)
            .ok_or_else(|| invalid("source plan lacks ordered signing slots"))?;
        if slots.len() != self.signers.len() {
            return Err(invalid(
                "source signing slot count differs from custody pin",
            ));
        }
        let mut headers = Vec::with_capacity(slots.len());
        for (slot, pin) in slots.iter().zip(&self.signers) {
            let signing = slot
                .get("signing")
                .ok_or_else(|| invalid("source slot lacks signing inspection"))?;
            let header = field(slot, "header")?;
            if field(slot, "role")? != pin.role
                || field(slot, "index")? != pin.index
                || signing.get("decoded").and_then(Value::as_bool) != Some(true)
                || field(signing, "canonical")? != header
                || field(signing, "keyId")? != pin.key_id
                || field(signing, "keyEpoch")? != pin.key_epoch
                || field(signing, "algorithm")? != "1"
            {
                return Err(invalid("source slot differs from fixed signer pin"));
            }
            let bytes = unhex(header)?;
            if bytes.is_empty() || bytes.len() > 65_536 {
                return Err(invalid("source signing header length refused"));
            }
            headers.push(bytes);
        }
        let signatures = headers
            .iter()
            .zip(&self.signers)
            .map(|(header, pin)| {
                let key = private_signing_key(&pin.seed_path)?;
                if hex(&key.verifying_key().to_bytes()) != pin.public_key_hex {
                    return Err(invalid(
                        "private signer differs from fixed enrollment public key",
                    ));
                }
                Ok(Value::String(hex(&key.sign(header).to_bytes())))
            })
            .collect::<io::Result<Vec<_>>>()?;
        Ok(Value::Array(signatures))
    }
}

fn private_signing_key(path: &Path) -> io::Result<SigningKey> {
    let parent = path
        .parent()
        .ok_or_else(|| invalid("signer has no parent"))?;
    let dir = fs::symlink_metadata(parent)?;
    let named = fs::symlink_metadata(path)?;
    let mut file = File::open(path)?;
    let opened = file.metadata()?;
    let uid = unsafe { libc::geteuid() };
    if !path.is_absolute()
        || !dir.is_dir()
        || dir.uid() != uid
        || dir.permissions().mode() & 0o077 != 0
        || !named.is_file()
        || named.nlink() != 1
        || named.uid() != uid
        || named.permissions().mode() & 0o777 != 0o600
        || (named.dev(), named.ino()) != (opened.dev(), opened.ino())
        || opened.len() != 32
    {
        return Err(invalid("dispatch signer file custody refused"));
    }
    let mut seed = [0; 32];
    file.read_exact(&mut seed)?;
    Ok(SigningKey::from_bytes(&seed))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::dispatch_inspection::Route;
    use ed25519_dalek::{Signature, Verifier};
    use std::fs::{self, DirBuilder, OpenOptions};
    use std::os::unix::fs::{DirBuilderExt, OpenOptionsExt};
    use std::time::{SystemTime, UNIX_EPOCH};

    fn fixture() -> (PathBuf, FixedAuthoring) {
        let nonce = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_nanos();
        let root =
            std::env::temp_dir().join(format!("mini-spk-author-{}-{nonce}", std::process::id()));
        DirBuilder::new().mode(0o700).create(&root).unwrap();
        let seed_path = root.join("participant.seed");
        fs::write(&seed_path, [7u8; 32]).unwrap();
        fs::set_permissions(&seed_path, fs::Permissions::from_mode(0o600)).unwrap();
        let key = SigningKey::from_bytes(&[7u8; 32]);
        let custody = FixedAuthoring {
            protocol: "mini-spk-human-dispatch-custody-v1".into(),
            app: "6100".into(),
            subject: "9".into(),
            session: "6209".into(),
            session_kind: "api".into(),
            issue_index: "5".into(),
            ticket_resource: "6409".into(),
            package_manifest: "6101".into(),
            snapshot_manifest: "6102".into(),
            session_observe_capability: "311".into(),
            manifest_observe_capability: "312".into(),
            enrollment_observe_capability: "313".into(),
            signers: vec![SignerPin {
                role: "9".into(),
                index: "0".into(),
                key_id: "9009".into(),
                key_epoch: "1".into(),
                public_key_hex: hex(&key.verifying_key().to_bytes()),
                seed_path,
            }],
        };
        (root, custody)
    }

    #[test]
    fn signed_api_path_and_source_slot_are_exact() {
        let (root, custody) = fixture();
        let headers = vec![(
            "content-type".into(),
            "application/x-git-receive-pack-request".into(),
        )];
        let http = HttpProjection {
            method: "POST",
            path_and_query: "git-receive-pack?service=git-receive-pack",
            ordered_headers: &headers,
            body: b"0010want commit\n",
            route: Route::Api {
                signed_path: "/repo.git/",
            },
        };
        let request = custody.request_json("17", &http).unwrap();
        let browser_route = HttpProjection {
            route: Route::Browser,
            ..http
        };
        assert!(custody.request_json("18", &browser_route).is_err());
        assert_eq!(
            request["http"]["pathHex"],
            hex(b"repo.git/git-receive-pack")
        );
        assert_eq!(
            request["http"]["queryHex"],
            hex(b"service=git-receive-pack")
        );
        let header = b"Mini source-derived signing header";
        let plan_bytes = b"source-plan-fixture";
        let request_bytes = b"source-authored-request-fixture";
        let mut projected = request.as_object().unwrap().clone();
        projected.insert(
            "type".into(),
            json!("application-dispatch-author-request-v1"),
        );
        projected.insert("canonicalRequest".into(), json!(hex(request_bytes)));
        let plan = json!({
            "type":"application-dispatch-author-plan-v1",
            "canonicalPlan":hex(plan_bytes),"request":Value::Object(projected),
            "appResource":"6100","sessionResource":"6209","subject":"9",
            "slots":[{"role":"9","index":"0","header":hex(header),
                "signing":{"decoded":true,"canonical":hex(header),
                    "keyId":"9009","keyEpoch":"1","algorithm":"1"}}]
        });
        let signatures = custody
            .sign_plan(
                plan_bytes,
                &serde_json::to_vec(&plan).unwrap(),
                request_bytes,
                &request,
            )
            .unwrap();
        let bytes: [u8; 64] = unhex(signatures[0].as_str().unwrap())
            .unwrap()
            .try_into()
            .unwrap();
        SigningKey::from_bytes(&[7u8; 32])
            .verifying_key()
            .verify(header, &Signature::from_bytes(&bytes))
            .unwrap();

        let mut drift = plan.clone();
        drift["slots"][0]["signing"]["keyId"] = json!("9010");
        assert!(custody
            .sign_plan(
                plan_bytes,
                &serde_json::to_vec(&drift).unwrap(),
                request_bytes,
                &request
            )
            .is_err());
        let mut changed = request.clone();
        changed["http"]["pathHex"] = json!(hex(b"repo.git/other"));
        assert!(custody
            .sign_plan(
                plan_bytes,
                &serde_json::to_vec(&plan).unwrap(),
                request_bytes,
                &changed
            )
            .is_err());
        fs::remove_dir_all(root).unwrap();
    }

    #[test]
    fn wrong_form_api_target_and_private_key_mode_refuse() {
        let (root, custody) = fixture();
        let http = HttpProjection {
            method: "GET",
            path_and_query: "/info/refs",
            ordered_headers: &[],
            body: b"",
            route: Route::Api {
                signed_path: "/repo.git/",
            },
        };
        assert!(custody.request_json("1", &http).is_err());
        assert!(custody
            .request_json(
                "01",
                &HttpProjection {
                    path_and_query: "info/refs",
                    ..http
                }
            )
            .is_err());
        let seed = &custody.signers[0].seed_path;
        let file = OpenOptions::new()
            .read(true)
            .mode(0o600)
            .open(seed)
            .unwrap();
        drop(file);
        fs::set_permissions(seed, fs::Permissions::from_mode(0o644)).unwrap();
        assert!(private_signing_key(seed).is_err());
        fs::remove_dir_all(root).unwrap();
    }
}
