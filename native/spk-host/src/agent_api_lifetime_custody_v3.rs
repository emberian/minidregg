//! Protected stable lifetime route and the exact first GitWeb HTTP projection.
//! Current generations and physical roots come only from the op80 source plan.
#![allow(dead_code)] // Resident v3 listener is enabled in a later cut.

use crate::agent_api_lifetime_v3::{LifetimeBinding, LifetimeLineage};
use crate::agent_api_lifetime_wire_v3::Request;
use crate::dispatch_author::private_signing_key;
use crate::dispatch_author::SignerPin;
use crate::hostd::Record;
use ed25519_dalek::{Signature, Signer, Verifier, VerifyingKey};
use serde::Deserialize;
use serde_json::{json, Value};
use std::io;

fn refused(reason: &'static str) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidData, reason)
}

fn decimal(value: &str) -> bool {
    !value.is_empty()
        && value.len() <= 128
        && (value == "0" || !value.starts_with('0'))
        && value.bytes().all(|byte| byte.is_ascii_digit())
}

fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|byte| format!("{byte:02x}")).collect()
}

fn unhex(value: &str) -> io::Result<Vec<u8>> {
    if !value.len().is_multiple_of(2)
        || !value
            .bytes()
            .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
    {
        return Err(refused("lifetime signature hex refused"));
    }
    value
        .as_bytes()
        .as_chunks::<2>()
        .0
        .iter()
        .map(|pair| {
            u8::from_str_radix(
                std::str::from_utf8(pair).map_err(|_| refused("lifetime hex UTF-8"))?,
                16,
            )
            .map_err(|_| refused("lifetime hex byte"))
        })
        .collect()
}

fn field<'a>(value: &'a Value, name: &str) -> io::Result<&'a str> {
    value
        .get(name)
        .and_then(Value::as_str)
        .ok_or_else(|| refused("lifetime signing field absent"))
}

#[derive(Debug, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub(crate) struct PayerPin {
    pub role: String,
    pub index: String,
    pub key_id: String,
    pub key_epoch: String,
    pub public_key_hex: String,
}

#[derive(Debug, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub(crate) struct LifetimeCustodyV3 {
    pub protocol: String,
    pub lineage: LifetimeLineage,
    pub package_manifest: String,
    pub snapshot_manifest: String,
    pub session_observe_capability: String,
    pub manifest_observe_capability: String,
    pub enrollment_observe_capability: String,
    pub parent_capability: String,
    pub parent_observe: String,
    pub purse_capability: String,
    pub purse_observe: String,
    pub grant_observe_capability: String,
    pub payer_subject: String,
    pub reserve_amount: String,
    pub maximum_charge: String,
    pub app_signers: Vec<SignerPin>,
    pub grant_signer: SignerPin,
    pub payer_pins: Vec<PayerPin>,
}

impl LifetimeCustodyV3 {
    pub(crate) fn validate(&self) -> io::Result<()> {
        self.lineage.validate()?;
        if self.protocol != "mini-spk-agent-lifetime-custody-v3"
            || ![
                &self.package_manifest,
                &self.snapshot_manifest,
                &self.session_observe_capability,
                &self.manifest_observe_capability,
                &self.enrollment_observe_capability,
                &self.parent_capability,
                &self.parent_observe,
                &self.purse_capability,
                &self.purse_observe,
                &self.grant_observe_capability,
                &self.payer_subject,
                &self.reserve_amount,
                &self.maximum_charge,
            ]
            .into_iter()
            .all(|value| decimal(value))
            || self
                .reserve_amount
                .parse::<u128>()
                .ok()
                .is_none_or(|n| n == 0)
            || self
                .maximum_charge
                .parse::<u128>()
                .ok()
                .is_none_or(|n| n == 0 || n > self.reserve_amount.parse::<u128>().unwrap())
            || self.app_signers.is_empty()
            || self.app_signers.len() > 64
            || self.payer_pins.is_empty()
            || self.payer_pins.len() > 64
        {
            return Err(refused("lifetime protected route refused"));
        }
        for (index, pin) in self.app_signers.iter().enumerate() {
            if ![&pin.role, &pin.index, &pin.key_id, &pin.key_epoch]
                .into_iter()
                .all(|value| decimal(value))
                || pin.public_key_hex.len() != 64
                || !pin
                    .public_key_hex
                    .bytes()
                    .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
                || !pin.seed_path.is_absolute()
                || self.app_signers[..index]
                    .iter()
                    .any(|earlier| earlier.role == pin.role && earlier.index == pin.index)
            {
                return Err(refused("lifetime app/grant signer pin refused"));
            }
        }
        let grant = &self.grant_signer;
        if ![&grant.role, &grant.index, &grant.key_id, &grant.key_epoch]
            .into_iter()
            .all(|value| decimal(value))
            || grant.public_key_hex.len() != 64
            || unhex(&grant.public_key_hex).is_err()
            || !grant.seed_path.is_absolute()
            || self
                .app_signers
                .iter()
                .any(|pin| pin.role == grant.role && pin.index == grant.index)
        {
            return Err(refused("lifetime grant signer pin refused"));
        }
        for (index, pin) in self.payer_pins.iter().enumerate() {
            if ![&pin.role, &pin.index, &pin.key_id, &pin.key_epoch]
                .into_iter()
                .all(|value| decimal(value))
                || pin.public_key_hex.len() != 64
                || unhex(&pin.public_key_hex).is_err()
                || self.payer_pins[..index]
                    .iter()
                    .any(|earlier| earlier.role == pin.role && earlier.index == pin.index)
            {
                return Err(refused("lifetime payer public pin refused"));
            }
        }
        Ok(())
    }

    pub(crate) fn sign_app_slots(&self, inspection: &Value, plan: &[u8]) -> io::Result<Value> {
        self.validate()?;
        if field(inspection, "type")? != "application-agent-lifetime-paid-plan-v3"
            || field(inspection, "canonicalPlanHex")? != hex(plan)
        {
            return Err(refused("lifetime app signing plan differs from source"));
        }
        let slots = inspection
            .get("appSlots")
            .and_then(Value::as_array)
            .ok_or_else(|| refused("lifetime app/grant slots absent"))?;
        if slots.len() != self.app_signers.len() {
            return Err(refused("lifetime app/grant signer count drift"));
        }
        let mut signatures = Vec::with_capacity(slots.len());
        for (slot, pin) in slots.iter().zip(&self.app_signers) {
            let signing = slot
                .get("signing")
                .ok_or_else(|| refused("lifetime app signing header absent"))?;
            if field(slot, "role")? != pin.role
                || field(slot, "index")? != pin.index
                || signing.get("decoded").and_then(Value::as_bool) != Some(true)
                || field(signing, "keyId")? != pin.key_id
                || field(signing, "keyEpoch")? != pin.key_epoch
                || field(signing, "algorithm")? != "1"
            {
                return Err(refused("lifetime app/grant slot differs from fixed signer"));
            }
            let header = unhex(field(slot, "headerHex")?)?;
            if header.is_empty() || header.len() > 65_536 {
                return Err(refused("lifetime app/grant header bound"));
            }
            let key = private_signing_key(&pin.seed_path)?;
            if hex(&key.verifying_key().to_bytes()) != pin.public_key_hex {
                return Err(refused("lifetime app/grant seed differs from enrolled key"));
            }
            signatures.push(Value::String(hex(&key.sign(&header).to_bytes())));
        }
        Ok(Value::Array(signatures))
    }

    pub(crate) fn sign_grant_slot(&self, inspection: &Value, plan: &[u8]) -> io::Result<Vec<u8>> {
        self.validate()?;
        if field(inspection, "type")? != "application-agent-lifetime-paid-plan-v3"
            || field(inspection, "canonicalPlanHex")? != hex(plan)
        {
            return Err(refused("lifetime grant signing plan differs from source"));
        }
        let slot = inspection
            .get("grantObservationSlot")
            .ok_or_else(|| refused("lifetime grant observation slot absent"))?;
        let signing = slot
            .get("signing")
            .ok_or_else(|| refused("lifetime grant signing header absent"))?;
        let pin = &self.grant_signer;
        if field(slot, "role")? != pin.role
            || field(slot, "index")? != pin.index
            || signing.get("decoded").and_then(Value::as_bool) != Some(true)
            || field(signing, "keyId")? != pin.key_id
            || field(signing, "keyEpoch")? != pin.key_epoch
            || field(signing, "algorithm")? != "1"
        {
            return Err(refused("lifetime grant slot differs from fixed signer"));
        }
        let header = unhex(field(slot, "headerHex")?)?;
        if header.is_empty() || header.len() > 65_536 {
            return Err(refused("lifetime grant header bound"));
        }
        let key = private_signing_key(&pin.seed_path)?;
        if hex(&key.verifying_key().to_bytes()) != pin.public_key_hex {
            return Err(refused("lifetime grant seed differs from enrolled key"));
        }
        Ok(key.sign(&header).to_bytes().to_vec())
    }

    pub(crate) fn verify_payer_slots(
        &self,
        inspection: &Value,
        plan: &[u8],
        signatures: &[String],
    ) -> io::Result<()> {
        self.validate()?;
        if field(inspection, "type")? != "application-agent-lifetime-paid-plan-v3"
            || field(inspection, "canonicalPlanHex")? != hex(plan)
        {
            return Err(refused("lifetime payer plan differs from source"));
        }
        let slots = inspection
            .get("payerSlots")
            .and_then(Value::as_array)
            .ok_or_else(|| refused("lifetime payer slots absent"))?;
        if slots.len() != self.payer_pins.len() || signatures.len() != slots.len() {
            return Err(refused("lifetime payer slot count drift"));
        }
        for ((slot, pin), signature) in slots.iter().zip(&self.payer_pins).zip(signatures) {
            let signing = slot
                .get("signing")
                .ok_or_else(|| refused("lifetime payer signing header absent"))?;
            if field(slot, "role")? != pin.role
                || field(slot, "index")? != pin.index
                || signing.get("decoded").and_then(Value::as_bool) != Some(true)
                || field(signing, "keyId")? != pin.key_id
                || field(signing, "keyEpoch")? != pin.key_epoch
                || field(signing, "algorithm")? != "1"
            {
                return Err(refused("lifetime payer slot differs from fixed key"));
            }
            let header = unhex(field(slot, "headerHex")?)?;
            let key_bytes: [u8; 32] = unhex(&pin.public_key_hex)?
                .try_into()
                .map_err(|_| refused("lifetime payer key length"))?;
            let key = VerifyingKey::from_bytes(&key_bytes)
                .map_err(|_| refused("lifetime payer key invalid"))?;
            let signature_bytes: [u8; 64] = unhex(signature)?
                .try_into()
                .map_err(|_| refused("lifetime payer signature length"))?;
            key.verify(&header, &Signature::from_bytes(&signature_bytes))
                .map_err(|_| refused("lifetime payer signature differs from source slot"))?;
        }
        Ok(())
    }

    pub(crate) fn binding(
        &self,
        record: &Record,
        signed_api_path: &str,
    ) -> io::Result<LifetimeBinding> {
        self.validate()?;
        record.verify_running_instance()?;
        if record.app().to_string() != self.lineage.app_resource {
            return Err(refused("lifetime app differs from running incarnation"));
        }
        let binding = LifetimeBinding {
            protocol: "mini-spk-agent-lifetime-binding-v3".into(),
            lineage: self.lineage.clone(),
            signed_api_path: signed_api_path.to_owned(),
            host_unit: record.unit().to_owned(),
            host_invocation: record
                .invocation_id()
                .ok_or_else(|| refused("lifetime host invocation absent"))?
                .to_owned(),
        };
        binding.validate()?;
        Ok(binding)
    }

    /// Apply the signed API prefix to the exact relative request path. Header
    /// order and bytes are preserved exactly.
    pub(crate) fn fixed_reserve_request(
        &self,
        request: &Request,
        signed_api_path: &str,
    ) -> io::Result<(Value, Value)> {
        self.validate()?;
        Request::parse(&serde_json::to_vec(request)?)?;
        let Request::DispatchV3 {
            operation_id,
            method,
            path,
            query,
            headers,
            body_hex,
            ..
        } = request
        else {
            return Err(refused("lifetime fixed request requires dispatch"));
        };
        let ordered = headers
            .iter()
            .map(|header| {
                json!({"nameHex":hex(header.name.as_bytes()),
                    "valueHex":hex(header.value.as_bytes()),"generated":false})
            })
            .collect::<Vec<_>>();
        let http = json!({
            "operationId":operation_id,
            "methodHex":hex(method.as_bytes()),
            "pathHex":hex(minidregg_signed_api_path::route(signed_api_path, path)
                .map_err(refused)?.as_bytes()),
            "queryHex":hex(query.as_bytes()),
            "headers":ordered,
            "bodyHex":body_hex,
        });
        let fixed = json!({
            "fixed":{
                "base":{
                    "issueIndex":self.lineage.original_issue_index,
                    "ticketResource":self.lineage.ticket_resource,
                    "packageManifest":self.package_manifest,
                    "snapshotManifest":self.snapshot_manifest,
                    "sessionObserveCapability":self.session_observe_capability,
                    "manifestObserveCapability":self.manifest_observe_capability,
                    "enrollmentObserveCapability":self.enrollment_observe_capability,
                    "http":http,
                },
                "parentTask":self.lineage.parent_task,
                "parentCapability":self.parent_capability,
                "parentObserve":self.parent_observe,
                "purseTask":self.lineage.purse_task,
                "purseCapability":self.purse_capability,
                "purseObserve":self.purse_observe,
                "payerSubject":self.payer_subject,
                "reserveAmount":self.reserve_amount,
                "maximumCharge":self.maximum_charge,
                "reserveOperationId":"0",
            },
            "grantIssueIndex":self.lineage.grant_issue_index,
            "grantResource":self.lineage.grant_resource,
            "grantObserveCapability":self.grant_observe_capability,
        });
        Ok((fixed, http))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::agent_api_lifetime_wire_v3::OrdinaryHeader;
    use std::fs::{self, DirBuilder, OpenOptions};
    use std::io::Write;
    use std::os::unix::fs::{DirBuilderExt, OpenOptionsExt};
    use std::time::{SystemTime, UNIX_EPOCH};

    fn custody() -> LifetimeCustodyV3 {
        serde_json::from_value(json!({
            "protocol":"mini-spk-agent-lifetime-custody-v3",
            "lineage":{
                "appResource":"800","sessionResource":"801",
                "participantSubject":"8","ticketResource":"802",
                "originalParentTask":"700","originalParentGeneration":"1",
                "originalIssueIndex":"2",
                "originalIssueReceipt":{"transactionId":"11","eventId":"12",
                    "acceptedCount":"3","imageBoundary":"13"},
                "originalDescriptorSha256":"ab".repeat(32),
                "grantResource":"803","grantIssueIndex":"3",
                "grantDigest":"123","grantInitializedRoot":"456",
                "grantIssueReceipt":{"transactionId":"21","eventId":"22",
                    "acceptedCount":"4","imageBoundary":"23"},
                "parentTask":"700","purseTask":"701",
            },
            "packageManifest":"10","snapshotManifest":"11",
            "sessionObserveCapability":"12","manifestObserveCapability":"13",
            "enrollmentObserveCapability":"14","parentCapability":"15",
            "parentObserve":"16","purseCapability":"17","purseObserve":"18",
            "grantObserveCapability":"19","payerSubject":"20",
            "reserveAmount":"100","maximumCharge":"10",
            "appSigners":[{"role":"1","index":"0","keyId":"2","keyEpoch":"3",
                "publicKeyHex":"cd".repeat(32),"seedPath":"/operator/app.seed"}],
            "grantSigner":{"role":"2","index":"0","keyId":"4","keyEpoch":"5",
                "publicKeyHex":"ab".repeat(32),"seedPath":"/operator/grant.seed"},
            "payerPins":[{"role":"4","index":"0","keyId":"5","keyEpoch":"6",
                "publicKeyHex":"ef".repeat(32)}],
        }))
        .unwrap()
    }

    #[test]
    fn first_gitweb_http_has_exact_ordered_source_bytes_and_no_current_claims() {
        let custody = custody();
        let request = Request::DispatchV3 {
            protocol: "mini-spk-agent-api-v3".into(),
            operation_id: "9".into(),
            binding_sha256: "ef".repeat(32),
            method: "POST".into(),
            path: "git-receive-pack".into(),
            query: "service=git-receive-pack".into(),
            headers: vec![
                OrdinaryHeader {
                    name: "accept".into(),
                    value: "one".into(),
                },
                OrdinaryHeader {
                    name: "content-type".into(),
                    value: "two".into(),
                },
            ],
            body_hex: "abcd".into(),
        };
        let (fixed, http) = custody
            .fixed_reserve_request(&request, "/repo.git/")
            .unwrap();
        assert_eq!(fixed["fixed"]["base"]["http"], http);
        assert_eq!(http["pathHex"], hex(b"repo.git/git-receive-pack"));
        assert_eq!(http["headers"][0]["nameHex"], hex(b"accept"));
        assert_eq!(http["headers"][1]["valueHex"], hex(b"two"));
        assert_eq!(fixed["fixed"]["reserveOperationId"], "0");
        assert_eq!(fixed["grantIssueIndex"], "3");
        assert!(fixed.get("appGeneration").is_none());
        let (_, rooted) = custody.fixed_reserve_request(&request, "/").unwrap();
        assert_eq!(rooted["pathHex"], hex(b"git-receive-pack"));
        assert_eq!(rooted["queryHex"], http["queryHex"]);
        assert_eq!(rooted["bodyHex"], http["bodyHex"]);
        assert_eq!(rooted["headers"], http["headers"]);
        assert!(custody.fixed_reserve_request(&request, "/api//").is_err());
    }

    #[test]
    fn payer_signatures_cover_every_exact_ordered_source_slot() {
        let mut custody = custody();
        let first = ed25519_dalek::SigningKey::from_bytes(&[7u8; 32]);
        let second = ed25519_dalek::SigningKey::from_bytes(&[8u8; 32]);
        custody.payer_pins[0].public_key_hex = hex(&first.verifying_key().to_bytes());
        custody.payer_pins.push(PayerPin {
            role: "4".into(),
            index: "1".into(),
            key_id: "7".into(),
            key_epoch: "8".into(),
            public_key_hex: hex(&second.verifying_key().to_bytes()),
        });
        let plan = b"source paid plan";
        let inspection = json!({
            "type":"application-agent-lifetime-paid-plan-v3",
            "canonicalPlanHex":hex(plan),
            "payerSlots":[
                {"role":"4","index":"0","headerHex":hex(b"first"),
                    "signing":{"decoded":true,"keyId":"5","keyEpoch":"6","algorithm":"1"}},
                {"role":"4","index":"1","headerHex":hex(b"second"),
                    "signing":{"decoded":true,"keyId":"7","keyEpoch":"8","algorithm":"1"}},
            ],
        });
        let mut signatures = vec![
            hex(&first.sign(b"first").to_bytes()),
            hex(&second.sign(b"second").to_bytes()),
        ];
        custody
            .verify_payer_slots(&inspection, plan, &signatures)
            .unwrap();
        signatures.swap(0, 1);
        assert!(custody
            .verify_payer_slots(&inspection, plan, &signatures)
            .is_err());
        signatures.swap(0, 1);
        let mut altered = inspection;
        altered["payerSlots"][1]["headerHex"] = json!(hex(b"different"));
        assert!(custody
            .verify_payer_slots(&altered, plan, &signatures)
            .is_err());
    }

    #[test]
    fn grant_observation_uses_its_own_exact_source_slot_and_seed() {
        let nonce = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_nanos();
        let dir = std::env::temp_dir().join(format!(
            "mini-lifetime-grant-signer-{}-{nonce}",
            std::process::id()
        ));
        DirBuilder::new().mode(0o700).create(&dir).unwrap();
        let seed = dir.join("grant.seed");
        let mut file = OpenOptions::new()
            .write(true)
            .create_new(true)
            .mode(0o600)
            .open(&seed)
            .unwrap();
        file.write_all(&[9u8; 32]).unwrap();
        file.sync_all().unwrap();
        let key = ed25519_dalek::SigningKey::from_bytes(&[9u8; 32]);
        let mut custody = custody();
        custody.grant_signer.seed_path = seed.clone();
        custody.grant_signer.public_key_hex = hex(&key.verifying_key().to_bytes());
        let plan = b"exact source plan";
        let mut inspection = json!({
            "type":"application-agent-lifetime-paid-plan-v3",
            "canonicalPlanHex":hex(plan),
            "grantObservationSlot":{"role":"2","index":"0",
                "headerHex":hex(b"grant header"),
                "signing":{"decoded":true,"keyId":"4","keyEpoch":"5","algorithm":"1"}},
        });
        let signature = custody.sign_grant_slot(&inspection, plan).unwrap();
        key.verifying_key()
            .verify(
                b"grant header",
                &Signature::from_bytes(&signature.try_into().unwrap()),
            )
            .unwrap();
        inspection["grantObservationSlot"]["signing"]["keyEpoch"] = json!("6");
        assert!(custody.sign_grant_slot(&inspection, plan).is_err());
        fs::remove_file(seed).unwrap();
        fs::remove_dir(dir).unwrap();
    }
}
