//! Realm wells (lane K-WELL), minimal client. A well is an account born in a
//! realm (`well new` = `workspace create --kind account --in REALM`); its law is
//! the predicate it is born with. `well mint|burn` authors the command with the
//! Host (`author well-command`), asks the Host for the exact header to sign
//! (op 123), signs it with the workspace key, has the Host assemble the ingress
//! (op 124) and submits it (op 125). The Host decides everything; this module
//! only retains the bytes. `well ledger` is the operator-local `well-ledger`.

use crate::workspace;
use crate::{absolute, hex, path, process, session_invoke, Args, Result, SOCKET};
use ed25519_dalek::{Signer, SigningKey};
use serde_json::{json, Value};
use std::ffi::{OsStr, OsString};
use std::fs::{self, File};
use std::io::Read;
use std::path::{Path, PathBuf};

fn text(value: OsString, label: &str) -> Result<String> {
    value
        .into_string()
        .map_err(|_| format!("{label} is not UTF-8"))
}

fn member<'a>(value: &'a Value, key: &str) -> Result<&'a str> {
    value
        .get(key)
        .and_then(Value::as_str)
        .ok_or_else(|| format!("missing string field {key}"))
}

fn is_decimal(value: &str) -> bool {
    !value.is_empty()
        && value.len() <= 80
        && value.bytes().all(|b| b.is_ascii_digit())
        && (value.len() == 1 || !value.starts_with('0'))
}

/// A workspace reference name, or a decimal resource id.
fn resolve(root: &Path, name: &str) -> Result<(String, Option<Value>)> {
    if is_decimal(name) {
        return Ok((name.to_owned(), None));
    }
    let reference = workspace::reference(root, name)?;
    Ok((member(&reference, "target")?.to_owned(), Some(reference)))
}

fn reference_capability(reference: &Option<Value>, label: &str) -> Result<String> {
    let reference = reference
        .as_ref()
        .ok_or_else(|| format!("{label} is a bare id; pass --capability"))?;
    reference
        .get("operationCapability")
        .or_else(|| reference.get("observeCapability"))
        .and_then(Value::as_str)
        .map(str::to_owned)
        .ok_or_else(|| format!("{label} reference names no capability"))
}

fn signing_key(path: &Path) -> Result<SigningKey> {
    let mut bytes = Vec::new();
    File::open(path)
        .and_then(|mut file| file.by_ref().take(33).read_to_end(&mut bytes))
        .map_err(|error| format!("cannot read workspace key: {error}"))?;
    let raw: [u8; 32] = bytes
        .as_slice()
        .try_into()
        .map_err(|_| "workspace key must contain exactly 32 raw bytes")?;
    Ok(SigningKey::from_bytes(&raw))
}

fn nonce() -> Result<String> {
    let mut bytes = [0u8; 16];
    File::open("/dev/urandom")
        .and_then(|mut file| file.read_exact(&mut bytes))
        .map_err(|error| format!("cannot obtain nonce: {error}"))?;
    Ok(u128::from_be_bytes(bytes).to_string())
}

fn pair(first: &[u8], second: &[u8]) -> Result<Vec<u8>> {
    let length: u32 = first
        .len()
        .try_into()
        .map_err(|_| "well pair exceeds u32")?;
    let mut bytes = length.to_le_bytes().to_vec();
    bytes.extend_from_slice(first);
    bytes.extend_from_slice(second);
    Ok(bytes)
}

fn retain(path: &Path, bytes: &[u8]) -> Result<()> {
    fs::write(path, bytes).map_err(|error| format!("cannot retain {}: {error}", path.display()))
}

/// One host operation over the pinned session socket. A 255 reply is a
/// refusal whose encoded outcome is reported verbatim.
fn invoke(
    host: &Path,
    socket: &Path,
    config: &Path,
    operation: u8,
    payload: &[u8],
    label: &str,
) -> Result<Vec<u8>> {
    let reply = session_invoke(host, socket, config, operation, payload)?;
    match reply.split_first() {
        Some((&code, body)) if code == operation => Ok(body.to_vec()),
        Some((255, body)) => Err(format!(
            "host refused {label}; encoded refusal: {}",
            hex(body)
        )),
        _ => Err(format!("host returned an invalid frame for {label}")),
    }
}

fn command(root: &Path, mut args: Args, op: &str) -> Result<()> {
    let workspace = workspace::load(root)?;
    let (well, well_ref) = resolve(root, &text(args.required("well")?, "well")?)?;
    let (account, account_ref) = resolve(root, &text(args.required("account")?, "account")?)?;
    let amount = text(args.required("amount")?, "amount")?;
    if !is_decimal(&amount) {
        return Err("amount must be decimal".into());
    }
    let capability = match args.optional("capability") {
        Some(value) => text(value, "capability")?,
        None if op == "mint" => reference_capability(&well_ref, "well")?,
        None => reference_capability(&account_ref, "account")?,
    };
    if !is_decimal(&capability) {
        return Err("capability must be decimal".into());
    }
    let attempt = match args.optional("attempt") {
        Some(value) => absolute(&path(value))?,
        None => root.join("attempts").join(format!("well-{op}-{}", nonce()?)),
    };
    args.finish()?;
    if attempt.exists() {
        return Err(format!("refusing to reuse {}", attempt.display()));
    }
    fs::create_dir_all(&attempt).map_err(|error| error.to_string())?;
    let host = PathBuf::from(member(&workspace, "host")?);
    let config = PathBuf::from(member(&workspace, "config")?);
    let socket = SOCKET
        .get()
        .ok_or("well commands require a pinned persistent Host socket")?
        .clone();
    let source = json!({"subject":member(&workspace, "subject")?,"capability":capability,
        "well":well,"op":op,"account":account,"amount":amount,"nonce":nonce()?});
    let source_path = attempt.join("command.json");
    retain(
        &source_path,
        &serde_json::to_vec_pretty(&source).map_err(|error| error.to_string())?,
    )?;
    let command_path = attempt.join("command.bin");
    process(
        &host,
        &config,
        &[
            OsStr::new("author"),
            OsStr::new("well-command"),
            source_path.as_os_str(),
            command_path.as_os_str(),
        ],
    )?;
    let command = fs::read(&command_path).map_err(|error| error.to_string())?;
    let plan = invoke(&host, &socket, &config, 123, &command, "well plan")?;
    retain(&attempt.join("plan.bin"), &plan)?;
    let plan_json = attempt.join("plan.json");
    process(
        &host,
        &config,
        &[
            OsStr::new("inspect"),
            OsStr::new("well-plan"),
            attempt.join("plan.bin").as_os_str(),
            plan_json.as_os_str(),
        ],
    )?;
    let view: Value = serde_json::from_slice(&fs::read(&plan_json).map_err(|e| e.to_string())?)
        .map_err(|error| error.to_string())?;
    if member(&view, "commandBytes")? != hex(&command) {
        return Err("well plan names a different command".into());
    }
    let header = crate::decode_hex(member(&view, "header")?)?;
    let key = signing_key(Path::new(member(&workspace, "key")?))?;
    let signature = key.sign(&header).to_bytes();
    let ingress = invoke(
        &host,
        &socket,
        &config,
        124,
        &pair(&plan, &signature)?,
        "well assembly",
    )?;
    retain(&attempt.join("ingress.bin"), &ingress)?;
    let outcome = invoke(&host, &socket, &config, 125, &ingress, "well submit");
    let outcome = match outcome {
        Ok(bytes) => bytes,
        Err(error) => {
            retain(&attempt.join("refusal.txt"), error.as_bytes())?;
            return Err(error);
        }
    };
    retain(&attempt.join("outcome.bin"), &outcome)?;
    println!(
        "{}",
        json!({"type":"minidregg-well-outcome-v1","op":op,"well":well,"account":account,
            "amount":amount,"attempt":attempt,"outcome":hex(&outcome)})
    );
    Ok(())
}

fn ledger(root: &Path, mut args: Args) -> Result<()> {
    let output = absolute(&path(args.required("output")?))?;
    args.finish()?;
    let workspace = workspace::load(root)?;
    let host = PathBuf::from(member(&workspace, "host")?);
    let config = PathBuf::from(member(&workspace, "config")?);
    let result = std::process::Command::new(&host)
        .arg(&config)
        .arg("well-ledger")
        .arg(&output)
        .output()
        .map_err(|error| format!("cannot run {}: {error}", host.display()))?;
    if !result.status.success() {
        return Err(format!(
            "well-ledger failed: {}",
            String::from_utf8_lossy(&result.stderr).trim()
        ));
    }
    print!(
        "{}",
        fs::read_to_string(&output).map_err(|error| error.to_string())?
    );
    Ok(())
}

pub(crate) fn run(mut args: Args) -> Result<()> {
    let action = text(args.required("action")?, "well action")?;
    let root = absolute(&path(args.required("dir")?))?;
    match action.as_str() {
        "new" => {
            let name = text(args.required("name")?, "well name")?;
            let realm = text(args.required("in")?, "realm name")?;
            let law = path(args.required("law")?);
            args.finish()?;
            let workspace = workspace::load(&root)?;
            workspace::create(
                &root,
                &workspace,
                &name,
                "declared",
                &law,
                Some(&realm),
                "account",
                None,
            )
        }
        "mint" | "burn" => command(&root, args, &action),
        "ledger" => ledger(&root, args),
        _ => Err("well action must be new, mint, burn or ledger".into()),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn pair_prefixes_first_length() {
        assert_eq!(pair(&[1, 2], &[3]).unwrap(), vec![2, 0, 0, 0, 1, 2, 3]);
    }

    #[test]
    fn decimal_names_are_ids() {
        assert!(is_decimal("0"));
        assert!(is_decimal("1234"));
        assert!(!is_decimal("01"));
        assert!(!is_decimal("gold"));
    }
}
