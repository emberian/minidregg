//! `member-action`: the signed key-service exchange, served by the broker.
//!
//! The frames are the ssh key service's, verbatim, so a remote `mini key`
//! (through `mini-keys relay`, the ssh forced command) and a hosted one (on
//! the broker socket directly) run one protocol:
//!
//! 1. broker -> `{"type":"mini-member-provider-challenge-v1","nonce","hostSha256","configSha256","tableSha256"}`
//! 2. member -> `{"challenge","owner":{"subject","publicKey"},"action","signature"}`, the
//!    signature by the member's workspace key over `mini/member-provider-action/v1\0` ‖ JSON
//!    of the request without `signature`
//! 3. broker -> `{"type":"mini-member-provider-result-v1",...}` or
//!    `{"type":"mini-member-provider-refused-v1","error"}`
//!
//! Between 2 and 3 the broker asks the Store (operation 144, public socket)
//! whether the signing key is the subject's current, unrevoked key, before and
//! after provisioning the member's namespace, and acts only then. A peer reaches
//! step 1 only if the kernel says its uid or gid holds the `member` role.
use super::credentials::{self, CredentialSource, CredentialStore, Grant, Namespace, Owner, ProviderTable};
use super::{native, refuse, Broker, Note, Refusal};
use crate::peer::Peer;
use crate::wire;
use ed25519_dalek::{Signature, VerifyingKey};
use serde_json::{json, Value};
use std::os::unix::fs::PermissionsExt;
use std::os::unix::net::UnixStream;
use std::path::Path;
use std::process::{Command, Stdio};
use std::time::{Duration, Instant};

pub const CHALLENGE: &str = "mini-member-provider-challenge-v1";
pub const RESULT: &str = "mini-member-provider-result-v1";
pub const REFUSED: &str = "mini-member-provider-refused-v1";

pub fn signing_bytes(request: &Value) -> Result<Vec<u8>, String> {
    let mut out = b"mini/member-provider-action/v1\0".to_vec();
    out.extend_from_slice(&serde_json::to_vec(request).map_err(|_| "credential action encode failed")?);
    Ok(out)
}

pub fn scrub(request: &mut Value) {
    if let Some(Value::String(mut secret)) = request.as_object_mut().and_then(|m| m.remove("secret")) {
        // SAFETY: zero bytes are valid UTF-8.
        unsafe { secret.as_bytes_mut().fill(0) };
    }
}

fn required<'a>(value: &'a Value, key: &str) -> Result<&'a str, String> {
    value.get(key).and_then(Value::as_str).ok_or_else(|| format!("key action requires {key}"))
}

fn exact(value: &Value, fields: &[&str]) -> Result<(), String> {
    if value.as_object().is_none_or(|m| m.keys().any(|k| !fields.contains(&k.as_str()))) {
        return Err("unknown key action field".into());
    }
    Ok(())
}

/// The request is this challenge's, signed by the key it names.
pub fn authenticate(challenge: &Value, request: &Value) -> Result<(Owner, Value, String), String> {
    exact(request, &["challenge", "owner", "action", "signature"])?;
    if request.get("challenge") != Some(challenge) {
        return Err("credential challenge differs or was replayed".into());
    }
    let owner = request.get("owner").ok_or("credential owner absent")?;
    exact(owner, &["subject", "publicKey"])?;
    let owner = Owner::new(required(owner, "subject")?, required(owner, "publicKey")?)?;
    let signature = wire::unhex(required(request, "signature")?).ok().filter(|s| s.len() == 64).ok_or("invalid authentication encoding")?;
    let key_bytes: [u8; 32] = wire::unhex(&owner.public_key)?.try_into().map_err(|_| "key width")?;
    let key = VerifyingKey::from_bytes(&key_bytes).map_err(|_| "invalid member signing key")?;
    let mut unsigned = request.clone();
    unsigned.as_object_mut().unwrap().remove("signature");
    let mut bytes = signing_bytes(&unsigned)?;
    let verified = key
        .verify_strict(&bytes, &Signature::from_slice(&signature).map_err(|_| "signature width")?)
        .map_err(|_| "credential action signature refused".to_owned());
    let digest = native::sha256_hex(&bytes);
    wire::zero(&mut bytes);
    scrub(&mut unsigned["action"]);
    verified?;
    let action = request.get("action").filter(|v| v.is_object()).ok_or("credential action absent")?.clone();
    Ok((owner, action, digest))
}

pub fn catalogue(table: &ProviderTable) -> Value {
    let providers: Vec<Value> = table.rows.iter().map(|row| json!({
        "provider":row.name, "models":row.models, "credential":row.credential.route(),
        "memberKey":row.credential == CredentialSource::User,
    })).collect();
    json!({"type":"mini-provider-catalogue-v1", "providers":providers,"tableSha256":table.sha256,
        "custody":"Member keys are sealed by this box's key broker (account mini-keys); no session account can read them, and the broker calls the provider itself. Root on this box can still use them.",
        "selection":"A credential grant authorizes a provider/model; the controller must also be provisioned for that route.",
        "budget":"Credential caps limit output tokens and calls; Mini purse authority and credit remain separate."})
}

/// One member operation on the member's own namespace.
pub fn member_action(store: &CredentialStore, owner: &Owner, table: &ProviderTable, request: &Value, owner_epoch: &str) -> Result<Value, String> {
    let who = json!({"subject":owner.subject,"publicKey":owner.public_key});
    let provider = || required(request, "provider");
    let user_row = |name: &str| -> Result<(), String> {
        if table.rows.iter().any(|r| r.name == name && r.credential == CredentialSource::User) {
            Ok(())
        } else {
            Err("selected provider does not accept a member key".into())
        }
    };
    match required(request, "action")? {
        "providers" => {
            exact(request, &["action"])?;
            Ok(catalogue(table))
        }
        "ls" => {
            exact(request, &["action"])?;
            let mut v = store.list(Namespace::Owner(owner))?;
            v["owner"] = who;
            Ok(v)
        }
        "set" => {
            exact(request, &["action", "provider", "secret"])?;
            let provider = provider()?;
            user_row(provider)?;
            let secret = credentials::Secret::new(required(request, "secret")?.to_owned())?;
            store.set(Namespace::Owner(owner), provider, &secret)?;
            Ok(json!({"type":"mini-key-set-v1","owner":who,"provider":provider,"stored":"sealed","existingGrants":"preserved"}))
        }
        "grant" => {
            exact(request, &["action", "provider", "runner", "perCall", "perDay", "notAfter", "model"])?;
            let provider = provider()?;
            user_row(provider)?;
            let mut raw = request.clone();
            raw.as_object_mut().unwrap().remove("action");
            raw.as_object_mut().unwrap().remove("provider");
            raw["ownerEpoch"] = json!(owner_epoch);
            let grant = Grant::from_json(&raw)?;
            if let Some(model) = &grant.model {
                table.select(model, Some(provider))?;
            }
            store.grant(owner, provider, grant.clone())?;
            Ok(json!({"type":"mini-key-grant-v1","owner":who,"provider":provider,"grant":grant.to_json(),"budget":"Mini purse authority and credit are separate"}))
        }
        "revoke" => {
            exact(request, &["action", "provider", "runner"])?;
            let provider = provider()?;
            let runner = request.get("runner").map(|_| required(request, "runner")).transpose()?;
            let removed = store.revoke(Namespace::Owner(owner), provider, runner)?;
            Ok(json!({"type":"mini-key-revoke-v1","owner":who,"provider":provider,"runner":runner,"removed":removed,"effect":"Future reservations refuse; an already authorized request may finish."}))
        }
        "choose" => {
            exact(request, &["action", "choice"])?;
            let choice = credentials::choice::Choice::from_json(request.get("choice").ok_or("choice absent")?)?;
            if &choice.owner != owner {
                return Err("choice belongs to another member".into());
            }
            store.choose(&choice, table)?;
            Ok(json!({"type":"mini-provider-choice-stored-v1","choice":choice.to_json(),"choiceSha256":choice.digest(),"activation":"Fresh controller provisioning must consume this choice; existing controllers remain pinned."}))
        }
        _ => Err("unknown member key action".into()),
    }
}

/// The deployment the challenge named, captured once; rechecked before every
/// step that changes custody.
struct Binding {
    host_sha: String,
    config: Vec<u8>,
    table_sha: String,
    key_sha: String,
}

fn binding(broker: &Broker) -> Result<Binding, String> {
    let c = broker.config.credentials.as_ref().ok_or("credentials-not-configured")?;
    Ok(Binding {
        host_sha: native::host_sha256(&c.host)?,
        config: native::host_config(&c.host_config)?,
        table_sha: super::provider_table(&c.providers, broker.config.trust_owner)?.sha256,
        key_sha: native::sha256_hex(&std::fs::read(&c.key).map_err(|_| "credential key unavailable")?),
    })
}

fn still(broker: &Broker, captured: &Binding) -> Result<(), String> {
    let now = binding(broker)?;
    if now.host_sha != captured.host_sha || now.config != captured.config || now.table_sha != captured.table_sha || now.key_sha != captured.key_sha {
        return Err("credential service binding changed during exchange".into());
    }
    Ok(())
}

/// The namespace helper is root's (every ancestor root-owned, not group/other
/// writable), its bytes are the pinned image, and it is executable.
pub fn helper_pinned(path: &Path, sha: &str, trust_owner: u32) -> Result<(), String> {
    let bytes = crate::client::custody_file(path, trust_owner, 1 << 20)?;
    let mode = std::fs::metadata(path).map_err(|_| "namespace helper unavailable")?.permissions().mode();
    if native::sha256_hex(&bytes) != sha || mode & 0o111 == 0 {
        return Err("namespace helper root custody or image pin refused".into());
    }
    Ok(())
}

fn provision(helper: &Path, owner: &Owner, end: Instant) -> Result<(), String> {
    let mut child = Command::new("/usr/bin/sudo")
        .args(["-n", "--"])
        .arg(helper)
        .arg(&owner.subject)
        .arg(&owner.public_key)
        .env_clear()
        .stdin(Stdio::null())
        .stdout(Stdio::null())
        .stderr(Stdio::null())
        .spawn()
        .map_err(|_| "credential namespace provisioning unavailable")?;
    loop {
        match child.try_wait().map_err(|_| "credential namespace provisioning unavailable")? {
            Some(status) if status.success() => return Ok(()),
            Some(_) => return Err("credential namespace provisioning refused".into()),
            None if Instant::now() >= end => {
                let _ = child.kill();
                let _ = child.wait();
                return Err("credential namespace provisioning timed out".into());
            }
            None => std::thread::sleep(Duration::from_millis(10)),
        }
    }
}

/// Run one exchange on `stream`. The outcome's refusal is the audit line's.
pub fn exchange(broker: &Broker, _peer: &Peer, stream: &mut UnixStream, note: &mut Note) -> Result<(), Refusal> {
    let end = Instant::now() + super::EXCHANGE;
    let fail = |stream: &mut UnixStream, code: &str, error: String| -> Refusal {
        let _ = wire::send(stream, &json!({"type":REFUSED,"error":error}), end);
        refuse(code, error)
    };
    let Some(c) = broker.config.credentials.clone() else {
        return Err(fail(stream, "credentials-not-configured", "this broker holds no credential store".into()));
    };
    let captured = match binding(broker) {
        Ok(b) => b,
        Err(e) => return Err(fail(stream, "binding", e)),
    };
    let mut nonce = [0u8; 32];
    if ring::rand::SecureRandom::fill(&ring::rand::SystemRandom::new(), &mut nonce).is_err() {
        return Err(fail(stream, "entropy", "challenge entropy unavailable".into()));
    }
    let challenge = json!({"type":CHALLENGE,"nonce":wire::hex(&nonce),"hostSha256":captured.host_sha,
        "configSha256":native::sha256_hex(&captured.config),"tableSha256":captured.table_sha});
    wire::send(stream, &challenge, end).map_err(|e| refuse("member-io", e))?;
    let mut request = wire::recv(stream, wire::MEMBER_FRAME, end).map_err(|e| refuse("member-io", e))?;
    let answer: Result<Value, (String, String)> = (|| {
        let (owner, mut action, digest) = authenticate(&challenge, &request).map_err(|e| ("authentication".to_owned(), e))?;
        note.set("subject", owner.subject.clone());
        note.set("requestSha256", digest.clone());
        note.set("action", action.get("action").cloned().unwrap_or(Value::Null));
        if let Some(p) = action.get("provider") {
            note.set("provider", p.clone());
        }
        let response: Result<Value, String> = (|| {
            let store = CredentialStore::open(&c.root, &c.key)?;
            let table = super::provider_table(&c.providers, broker.config.trust_owner)?;
            if table.sha256 != captured.table_sha {
                return Err("credential service binding changed during exchange".into());
            }
            let _custody = store.member_service_lock_until(&owner, end)?;
            still(broker, &captured)?;
            let epoch = native::current_epoch(&native::key_status(&c.public_socket, &captured.config, &captured.host_sha, &owner, end)?, &owner)?;
            still(broker, &captured)?;
            if let Some((helper, sha)) = &c.namespace_helper {
                helper_pinned(helper, sha, broker.config.trust_owner)?;
                provision(helper, &owner, end)?;
                still(broker, &captured)?;
            }
            // Provisioning made metadata only: re-ask the Store immediately before any mutation.
            let epoch_now = native::current_epoch(&native::key_status(&c.public_socket, &captured.config, &captured.host_sha, &owner, end)?, &owner)?;
            if epoch_now != epoch {
                return Err("owner key epoch changed during exchange".into());
            }
            still(broker, &captured)?;
            let result = member_action(&store, &owner, &table, &action, &epoch)?;
            still(broker, &captured)?;
            Ok(json!({"type":RESULT,"result":result,
                "authentication":{"requestSha256":digest,"keyEpoch":epoch,"subject":owner.subject,"publicKey":owner.public_key}}))
        })();
        scrub(&mut action);
        response.map_err(|e| {
            let code = if e == "owner-not-current" { "owner-not-current" } else if e.starts_with(credentials::REFUSED) { "provider-refused" } else { "member-action" };
            (code.to_owned(), e)
        })
    })();
    scrub(&mut request["action"]);
    match answer {
        Ok(result) => wire::send(stream, &result, end).map_err(|e| refuse("member-io", e)),
        Err((code, error)) => Err(fail(stream, &code, error)),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ed25519_dalek::Signer;

    pub fn signed(action: Value) -> (Value, Value, Owner) {
        let key = ed25519_dalek::SigningKey::from_bytes(&[41; 32]);
        let owner = Owner::new("20", &wire::hex(key.verifying_key().as_bytes())).unwrap();
        let challenge = json!({"type":CHALLENGE,"nonce":"a".repeat(64),"hostSha256":"b".repeat(64),"configSha256":"c".repeat(64),"tableSha256":"d".repeat(64)});
        let mut request = json!({"challenge":challenge,"owner":{"subject":owner.subject,"publicKey":owner.public_key},"action":action});
        request["signature"] = json!(wire::hex(&key.sign(&signing_bytes(&request).unwrap()).to_bytes()));
        (challenge, request, owner)
    }

    #[test]
    fn action_signature_binds_secret_grant_route_owner_and_single_session_challenge() {
        let (challenge, request, _) = signed(json!({"action":"set","provider":"chutes","secret":"synthetic-wire-only"}));
        assert!(authenticate(&challenge, &request).is_ok());
        for (path, value) in [("secret", "other"), ("provider", "openrouter"), ("action", "revoke")] {
            let mut changed = request.clone();
            changed["action"][path] = json!(value);
            assert!(authenticate(&challenge, &changed).is_err());
        }
        let mut next = challenge.clone();
        next["nonce"] = json!("f".repeat(64));
        assert!(authenticate(&next, &request).is_err());
        let mut other = request.clone();
        other["owner"]["subject"] = json!("21");
        assert!(authenticate(&challenge, &other).is_err());
    }
}
