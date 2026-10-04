//! Pinned completion-custodian preflight: the signer seed must be the key the
//! Mini Host's genesis-bound config names, with canonical semantics.

use crate::dispatch_author::private_signing_key;
use crate::dispatch_native::PrivateOperator;
use serde_json::Value;
use std::io;
use std::path::Path;

fn invalid(reason: &'static str) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidData, reason)
}

fn hex(bytes: &[u8]) -> String {
    let mut result = String::with_capacity(bytes.len() * 2);
    for byte in bytes {
        use std::fmt::Write as _;
        write!(result, "{byte:02x}").expect("writing to String");
    }
    result
}

fn canonical_decimal(value: &str) -> bool {
    !value.is_empty()
        && value.len() <= 128
        && (value == "0" || !value.starts_with('0'))
        && value.bytes().all(|byte| byte.is_ascii_digit())
}

fn pinned_context(
    operator: &PrivateOperator,
    seed: &Path,
    semantics: &str,
) -> io::Result<(String, String)> {
    // The Host's own config is the genesis-bound source of domain, semantics,
    // and completion custodian public key. A request cannot supply them.
    let config: Value = serde_json::from_slice(&operator.pinned_config()?)?;
    let object = config
        .as_object()
        .ok_or_else(|| invalid("Mini Host config is not an object"))?;
    let decimal = |name: &str| -> io::Result<String> {
        let value = object
            .get(name)
            .ok_or_else(|| invalid("Mini Host completion context absent"))?;
        let value = value
            .as_str()
            .map(str::to_owned)
            .or_else(|| value.as_u64().map(|number| number.to_string()))
            .ok_or_else(|| invalid("Mini Host completion context malformed"))?;
        if !canonical_decimal(&value) {
            return Err(invalid("Mini Host completion context noncanonical"));
        }
        Ok(value)
    };
    let key = object
        .get("completionCustodianKey")
        .and_then(Value::as_str)
        .ok_or_else(|| invalid("Mini Host completion custodian key absent"))?;
    let signer = private_signing_key(seed)?;
    if hex(&signer.verifying_key().to_bytes()) != key {
        return Err(invalid(
            "completion signer differs from genesis-bound Mini key",
        ));
    }
    if !canonical_decimal(semantics) {
        return Err(invalid("completion semantics noncanonical"));
    }
    // The source author validates this physical profile against BEGIN-v2.
    Ok((decimal("domain")?, semantics.to_owned()))
}

pub(crate) fn preflight_custodian(
    operator: &PrivateOperator,
    seed: &Path,
    semantics: &str,
) -> io::Result<()> {
    pinned_context(operator, seed, semantics).map(|_| ())
}
