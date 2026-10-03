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
fn check_readback(
    view: &Value,
    query: &[u8],
    source_identity: &Value,
    point: &Value,
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
        || view["domain"] != source_identity["domain"]
        || view["semantics"] != source_identity["semantics"]
        || view["pointHeight"] != nat(text(point, "height")?)?
        || view["pointRoot"] != point["worldRoot"]
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
        custody_point: point.clone(),
        exact_query: query.to_vec(),
        exact_record: payload.to_vec(),
        source_identity: source_identity.clone(),
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
    let input = json!({"member":nat(member)?,"room":nat(room)?,"keysCell":nat(keys_cell)?,"payloadHex":crate::hex(payload)});
    with_current_source(
        root,
        workspace,
        CurrentSourceOperation::CurrentRecipient,
        input,
        |readback| {
            check_readback(
                readback.view(),
                readback.exact_query(),
                readback.source_identity(),
                readback.custody_point(),
                member,
                room,
                keys_cell,
                payload,
            )
        },
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
        let token = check_readback(
            &view,
            &query,
            &settings.identity,
            &point.json(),
            "9",
            "10",
            "11",
            &payload,
        )
        .unwrap();
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
                check_readback(
                    &wrong,
                    &query,
                    &settings.identity,
                    &point.json(),
                    "9",
                    "10",
                    "11",
                    &payload
                )
                .is_err(),
                "{field}"
            );
        }
    }
}
