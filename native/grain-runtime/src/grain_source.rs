//! Source identity belongs to a controller and authority, while journal IDs
//! remain small local counters. The native invocation marker is subject-wide.
use super::*;
use sha2::{Digest, Sha256};

pub(super) fn operation_id(controller: &str, task: &str, subject: &str, local: u64) -> String {
    let mut hash = Sha256::new();
    hash.update(b"DREGG/GRAIN-CONTROLLER/OPERATION/v1\0");
    for field in [controller, task, subject, &local.to_string()] {
        hash.update((field.len() as u64).to_be_bytes());
        hash.update(field.as_bytes());
    }
    // Native Nat JSON uses decimal, preserving all 256 digest bits.
    let mut digits = vec![0u16];
    for byte in hash.finalize() {
        let mut carry = u16::from(byte);
        for digit in &mut digits {
            let value = *digit * 256 + carry;
            *digit = value % 10;
            carry = value / 10;
        }
        while carry != 0 {
            digits.push(carry % 10);
            carry /= 10;
        }
    }
    digits
        .iter()
        .rev()
        .map(|v| char::from(b'0' + *v as u8))
        .collect()
}

/// Retained sources retain their exact old identity, never get rewritten.
/// Require both fields to match one complete scheme, not a mixture.
pub(super) fn retained_identity(
    source: &Value,
    controller: &str,
    task: &str,
    subject: &str,
    local: u64,
) -> bool {
    let Some(context) = source
        .pointer("/grain/context/operationId")
        .and_then(Value::as_str)
    else {
        return false;
    };
    let Some(nonce) = source.get("intentNonce").and_then(Value::as_str) else {
        return false;
    };
    context == nonce
        && (context == local.to_string()
            || context == operation_id(controller, task, subject, local))
}

pub(super) struct Transition<'a> {
    pub identity: &'a str,
    pub payload: &'a str,
    pub operation: Value,
    pub publications: Vec<Value>,
    pub parent_witness: Option<Value>,
    pub grants: Vec<Value>,
}

/// Used for initial authoring and exact retained-operation recovery alike.
pub(super) fn source(
    authority: &Authority,
    observed: &Value,
    transition: Transition<'_>,
) -> Result<Value> {
    let before = observed.get("grain").ok_or("missing observed grain")?;
    let mut grain = json!({"task":authority.task,"subject":authority.subject,
        "capability":authority.capability,"schemaVersion":"1",
        "expectedTargetRoot":observed.get("targetRoot").ok_or("missing target root")?,
        "context":{"operationId":transition.identity,"payload":transition.payload},
        "before":{"generation":before.get("generation"),"status":before.get("status"),
            "remaining":before.get("remaining"),"reserved":before.get("reserved")},
        "operation":transition.operation,"publications":transition.publications,
        "observeCapability":authority.query_capability});
    if let Some(route) = before.get("route") {
        grain["before"]["route"] = route.clone();
    }
    if let Some(witness) = transition.parent_witness {
        grain["parentWitness"] = witness;
    }
    Ok(json!({"grain":grain,"grants":transition.grants,"intentNonce":transition.identity}))
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn operation_namespace_separates_controllers_authorities_and_local_ids() {
        let id = operation_id("8911", "8911", "7", 6);
        decimal(&id, "namespace").unwrap();
        assert_eq!(id, operation_id("8911", "8911", "7", 6));
        for other in [
            operation_id("8921", "8921", "7", 6),
            operation_id("8911", "8914", "7", 6),
            operation_id("8911", "8911", "9", 6),
            operation_id("8911", "8911", "7", 7),
        ] {
            assert_ne!(id, other);
        }
    }
    #[test]
    fn retained_identity_accepts_exact_legacy_or_namespaced_pair_only() {
        for id in ["6".to_string(), operation_id("8911", "8914", "9", 6)] {
            let mut source = json!({"grain":{"context":{"operationId":id}},"intentNonce":id});
            assert!(retained_identity(&source, "8911", "8914", "9", 6));
            assert!(!retained_identity(&source, "8911", "8914", "9", 7));
            source["intentNonce"] = json!("wrong");
            assert!(!retained_identity(&source, "8911", "8914", "9", 6));
        }
    }
}
