//! Closed local source consumer. Only this module can construct the verified
//! recipient token; a parsed public record/readback is never current authority.
use super::*;

pub(crate) struct VerifiedCurrentRecipient {
    signing_public: [u8; 32],
    epoch: u32,
    custody_point: Value,
    exact_query: Vec<u8>,
    exact_record: Vec<u8>,
    source_identity: Value,
    key_id: String,
}
impl VerifiedCurrentRecipient {
    pub(crate) fn custody_point(&self) -> &Value {
        &self.custody_point
    }
    pub(crate) fn exact_query(&self) -> &[u8] {
        &self.exact_query
    }
    pub(crate) fn exact_record(&self) -> &[u8] {
        &self.exact_record
    }
    pub(crate) fn source_identity(&self) -> &Value {
        &self.source_identity
    }
    pub(crate) fn key_id(&self) -> &str {
        &self.key_id
    }

    pub(crate) fn signing_public(&self) -> [u8; 32] {
        self.signing_public
    }
    pub(crate) fn epoch(&self) -> u32 {
        self.epoch
    }
}
fn nat(value: &str) -> Result<Value> {
    decimal(value)?;
    serde_json::from_str(value).map_err(fail)
}
fn read_bytes(path: &Path, limit: usize) -> Result<Vec<u8>> {
    let f = OpenOptions::new()
        .read(true)
        .custom_flags(NOFOLLOW)
        .open(path)
        .map_err(fail)?;
    private_metadata(&f, false)?;
    if f.metadata().map_err(fail)?.len() > limit as u64 {
        return Err(fail("current recipient source output exceeds bound"));
    }
    let mut b = Vec::new();
    f.take((limit + 1) as u64)
        .read_to_end(&mut b)
        .map_err(fail)?;
    if b.is_empty() || b.len() > limit {
        return Err(fail("current recipient source output empty or oversized"));
    }
    Ok(b)
}
fn check_readback(
    view: &Value,
    query: &[u8],
    settings: &Settings,
    point: &Point,
    member: &str,
    room: &str,
    keys: &str,
    payload: &[u8],
) -> Result<VerifiedCurrentRecipient> {
    if payload.len() != 148 {
        return Err(fail("current recipient record must be148bytes"));
    }
    let public: [u8; 32] = payload[52..84].try_into().map_err(fail)?;
    let epoch = u32::from_be_bytes(payload[..4].try_into().map_err(fail)?);
    if view["queryHex"] != json!(crate::hex(query))
        || view["domain"] != settings.identity["domain"]
        || view["semantics"] != settings.identity["semantics"]
        || view["pointHeight"] != nat(&point.height)?
        || view["pointRoot"] != json!(point.world_root)
        || view["member"] != nat(member)?
        || view["room"] != nat(room)?
        || view["keysCell"] != nat(keys)?
        || view["publicKeyHex"] != json!(crate::hex(&public))
        || view["keyEpoch"] != json!(epoch)
    {
        return Err(fail(
            "current recipient local readback differs from exact custody request",
        ));
    }
    decimal(text(view, "keyID")?)?;
    Ok(VerifiedCurrentRecipient {
        signing_public: public,
        epoch,
        custody_point: point.json(),
        exact_query: query.to_vec(),
        exact_record: payload.to_vec(),
        source_identity: settings.identity.clone(),
        key_id: text(view, "keyID")?.to_owned(),
    })
}
/// The caller supplies only scope and exact member-signed record. The point is
/// selected HERE from authenticated custody under its existing lock. No remote
/// fallback or endpoint-selected point is accepted. This token is current-key
/// authentication, NOT authorization to publish an already-used room key.
pub(crate) fn current_recipient_source(
    root: &Path,
    workspace: &Value,
    room: &str,
    keys_cell: &str,
    member: &str,
    payload: &[u8],
) -> Result<VerifiedCurrentRecipient> {
    if payload.len() != 148 {
        return Err(fail("current recipient record must be148bytes"));
    }
    let custody = root.join(DIRECTORY);
    let _lock = lock(&custody)?;
    if read_json(&root.join("workspace.json"))? != *workspace {
        return Err(fail(
            "workspace changed before current recipient verification",
        ));
    }
    let settings = Settings::load(&custody)?;
    let config = workspace::member_path(workspace, "config")?;
    settings.check(&config)?;
    let point = anchor(&custody, &settings)?;
    let config_bytes = crate::agent_reserve::bounded(&config, MAX_JSON as usize)?;
    let input = json!({"pointHeight":nat(&point.height)?,"pointRoot":point.world_root,
        "member":nat(member)?,"room":nat(room)?,"keysCell":nat(keys_cell)?,"payloadHex":crate::hex(payload)});
    let attempts = root.join("attempts");
    directory(&attempts)?;
    let scratch = attempts.join(format!("current-recipient-{}", workspace::random_nonce()?));
    workspace::make_private_dir(&scratch)?;
    let input_path = scratch.join("input.json");
    let query_path = scratch.join("query.bin");
    let readback_path = scratch.join("readback.bin");
    let json_path = scratch.join("readback.json");
    create_file(&input_path, &serde_json::to_vec(&input).map_err(fail)?)?;
    for path in [&query_path, &readback_path, &json_path] {
        create_file(path, b"")?;
    }
    for (verb, kind, source, dest) in [
        (
            "author",
            "current-recipient-query",
            &input_path,
            &query_path,
        ),
        ("inspect", "current-recipient", &query_path, &readback_path),
        (
            "inspect",
            "current-recipient-readback",
            &readback_path,
            &json_path,
        ),
    ] {
        let status = Command::new(&settings.verifier)
            .arg(&config)
            .arg(verb)
            .arg(kind)
            .arg(source)
            .arg(dest)
            .stdout(std::process::Stdio::null())
            .stderr(std::process::Stdio::null())
            .status()
            .map_err(fail)?;
        if !status.success() {
            return Err(fail(format!("pinned local source refused {kind}")));
        }
    }
    // Recheck after all source operations, still holding the same custody lock.
    // Fresh output paths prevent an earlier successful result surviving failure.
    if crate::host_image_sha256(&settings.verifier)? != settings.verifier_sha256
        || crate::agent_reserve::bounded(&config, MAX_JSON as usize)? != config_bytes
        || read_json(&root.join("workspace.json"))? != *workspace
        || Settings::load(&custody)?.json() != settings.json()
        || anchor(&custody, &settings)? != point
    {
        return Err(fail(
            "current recipient custody inputs changed during source verification",
        ));
    }
    let query = read_bytes(&query_path, 4096)?;
    let _readback = read_bytes(&readback_path, 8192)?;
    let view: Value = serde_json::from_slice(&read_bytes(&json_path, 8192)?).map_err(fail)?;
    check_readback(
        &view, &query, &settings, &point, member, room, keys_cell, payload,
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn current_recipient_readback_binds_exact_locked_point_query_scope_and_key() {
        let settings = Settings {
            identity: json!({"domain":"3","semantics":"4"}),
            verifier: PathBuf::from("/source"),
            verifier_sha256: "pin".into(),
        };
        let point = Point {
            height: "18446744073709551619".into(),
            world_root: "340282366920938463463374607431768211457".into(),
            witness: None,
        };
        let mut payload = [0u8; 148];
        payload[..4].copy_from_slice(&7u32.to_be_bytes());
        payload[52..84].fill(6);
        let query = [1, 2, 3];
        let view = json!({"queryHex":"010203","domain":"3","semantics":"4","pointHeight":nat(&point.height).unwrap(),
            "pointRoot":point.world_root,"member":9,"room":10,"keysCell":11,"publicKeyHex":crate::hex(&payload[52..84]),"keyEpoch":7,"keyID":"12"});
        let token =
            check_readback(&view, &query, &settings, &point, "9", "10", "11", &payload).unwrap();
        assert_eq!(token.epoch(), 7);
        assert_eq!(token.signing_public(), [6; 32]);
        for field in [
            "queryHex",
            "domain",
            "semantics",
            "pointHeight",
            "pointRoot",
            "member",
            "room",
            "keysCell",
            "publicKeyHex",
            "keyEpoch",
            "keyID",
        ] {
            let mut wrong = view.clone();
            wrong[field] = json!("wrong");
            assert!(
                check_readback(&wrong, &query, &settings, &point, "9", "10", "11", &payload)
                    .is_err(),
                "{field}"
            );
        }
    }
}
