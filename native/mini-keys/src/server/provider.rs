//! The provider role (the Hermes controller) and the operator's pool key.
//!
//! The controller never holds a bearer. It asks for a TICKET at reserve time
//! (`provider-authorize`: the grant or pool caps are checked and today's call is
//! counted, exactly where the controller used to unseal the key), and later
//! hands the broker the exact request body with that ticket
//! (`provider-forward`): the broker checks the body is the one the ticket was
//! minted for, calls the provider with the bearer, and returns the response.
//! A ticket is single-use, expires, names the uid that minted it, and is bound
//! to one table row, one endpoint and one body digest. A homelab row carries no
//! bearer and needs no ticket.
use super::credentials::{self, Caps, CredentialSource, CredentialStore, Namespace, Owner, ProviderTable, Secret};
use super::{native, refuse, store_refusal, Broker, Note, Refusal, Ticket};
use crate::peer::Peer;
use crate::wire;
use serde_json::{json, Value};
use std::fs::{File, OpenOptions};
use std::io::{Read, Write};
use std::os::fd::AsRawFd;
use std::os::unix::fs::OpenOptionsExt;
use std::os::unix::net::UnixStream;
use std::os::unix::process::CommandExt;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::{Duration, Instant};

pub const TICKET_TTL: Duration = Duration::from_secs(600);
const MAX_HEADERS: usize = 65_536;
const MAX_TIMEOUT: Duration = Duration::from_secs(600);
static SEQ: AtomicU64 = AtomicU64::new(0);

fn exact(value: &Value, fields: &[&str]) -> Result<(), Refusal> {
    match value.as_object() {
        Some(m) if m.keys().all(|k| fields.contains(&k.as_str())) => Ok(()),
        _ => Err(refuse("bad-request", format!("request fields must be within {fields:?}"))),
    }
}

fn text<'a>(value: &'a Value, key: &str) -> Result<&'a str, Refusal> {
    value.get(key).and_then(Value::as_str).ok_or_else(|| refuse("bad-request", format!("{key} must be a string")))
}

fn number(value: &Value, key: &str) -> Result<u64, Refusal> {
    value.get(key).and_then(Value::as_u64).ok_or_else(|| refuse("bad-request", format!("{key} must be a natural number")))
}

fn optional_number(value: &Value, key: &str) -> Result<Option<u64>, Refusal> {
    match value.get(key) {
        None | Some(Value::Null) => Ok(None),
        Some(v) => v.as_u64().map(Some).ok_or_else(|| refuse("bad-request", format!("{key} must be a natural number or null"))),
    }
}

fn owner_of(value: &Value) -> Result<Owner, Refusal> {
    let o = value.get("owner").ok_or_else(|| refuse("bad-request", "owner absent"))?;
    exact(o, &["subject", "publicKey"])?;
    Owner::new(text(o, "subject")?, text(o, "publicKey")?).map_err(|e| refuse("bad-request", e))
}

fn sha_field(value: &Value, key: &str) -> Result<String, Refusal> {
    let s = text(value, key)?;
    if s.len() != 64 || wire::unhex(s).is_err() {
        return Err(refuse("bad-request", format!("{key} must be 64 lowercase hex")));
    }
    Ok(s.to_owned())
}

fn configured(broker: &Broker) -> Result<&super::Credentials, Refusal> {
    broker.config.credentials.as_ref().ok_or_else(|| refuse("credentials-not-configured", "this broker holds no credential store"))
}

fn table(broker: &Broker) -> Result<ProviderTable, Refusal> {
    let c = configured(broker)?;
    super::provider_table(&c.providers, broker.config.trust_owner).map_err(|e| refuse("provider-table", e))
}

fn store(broker: &Broker) -> Result<CredentialStore, Refusal> {
    let c = configured(broker)?;
    CredentialStore::open(&c.root, &c.key).map_err(store_refusal)
}

/// The broker's own observation of the owner's current key epoch: a caller's
/// claimed epoch is never authority.
fn observed_epoch(broker: &Broker, owner: &Owner) -> Result<String, Refusal> {
    let c = configured(broker)?;
    let end = Instant::now() + Duration::from_secs(15);
    let host_sha = native::host_sha256(&c.host).map_err(|e| refuse("binding", e))?;
    let config = native::host_config(&c.host_config).map_err(|e| refuse("binding", e))?;
    let view = native::key_status(&c.public_socket, &config, &host_sha, owner, end).map_err(|e| refuse("owner-status-unavailable", e))?;
    native::current_epoch(&view, owner).map_err(|_| refuse(&credentials::refused("owner-not-current"), "the Store does not say this key is the subject's current, unrevoked key"))
}

fn ticket_id() -> Result<String, Refusal> {
    let mut bytes = [0u8; 32];
    ring::rand::SecureRandom::fill(&ring::rand::SystemRandom::new(), &mut bytes).map_err(|_| refuse("entropy", "ticket entropy unavailable"))?;
    Ok(wire::hex(&bytes))
}

/// `provider-authorize`: check the grant (or the pool caps), count the call,
/// and mint a ticket for one forward of one exact body.
pub fn authorize(broker: &Broker, peer: &Peer, request: &Value, note: &mut Note) -> Result<Value, Refusal> {
    let kind = text(request, "kind")?;
    match kind {
        "pool" => exact(request, &["op", "provider", "runner", "kind", "maxTokens", "bodySha256"])?,
        "user" => exact(request, &["op", "provider", "runner", "kind", "maxTokens", "bodySha256", "owner", "model", "height"])?,
        _ => return Err(refuse("bad-request", "kind must be pool or user (a homelab row needs no ticket)")),
    }
    let provider = text(request, "provider")?.to_owned();
    let runner = text(request, "runner")?.to_owned();
    let max_tokens = optional_number(request, "maxTokens")?;
    let body_sha256 = sha_field(request, "bodySha256")?;
    note.set("provider", provider.clone());
    note.set("runner", runner.clone());
    note.set("kind", kind);
    note.set("bodySha256", body_sha256.clone());
    let table = table(broker)?;
    let row = table.rows.iter().find(|r| r.name == provider).ok_or_else(|| refuse("provider-row-unknown", format!("the provider table has no row {provider}")))?;
    if row.credential.route() != kind {
        return Err(refuse("provider-kind-mismatch", format!("row {provider} is a {} row, not {kind}", row.credential.route())));
    }
    let store = store(broker)?;
    let (secret, route, epoch) = match row.credential {
        CredentialSource::Pool => {
            let caps: Caps = row.caps.ok_or_else(|| refuse("provider-table", "pool row has no caps"))?;
            (store.pool(&provider, &runner, max_tokens, caps, credentials::utc_day()).map_err(store_refusal)?, "pool".to_owned(), None)
        }
        CredentialSource::User => {
            let owner = owner_of(request)?;
            let model = text(request, "model")?;
            let height = number(request, "height")?;
            note.set("subject", owner.subject.clone());
            let epoch = observed_epoch(broker, &owner)?;
            let secret = store
                .authorize_model_epoch(&owner, &provider, &runner, Some(model), Some(&epoch), height, max_tokens, credentials::utc_day())
                .map_err(store_refusal)?;
            (secret, format!("user:{}", owner.subject), Some(epoch))
        }
        CredentialSource::Homelab => unreachable!("kind checked against the row"),
    };
    let id = ticket_id()?;
    note.set("ticketSha256", native::sha256_hex(id.as_bytes())[..16].to_owned());
    let endpoint = row.endpoint.clone();
    let mut tickets = broker.tickets.lock().map_err(|_| refuse("internal", "ticket table poisoned"))?;
    let now = Instant::now();
    tickets.retain(|_, t| t.expires > now);
    tickets.insert(id.clone(), Ticket { peer: peer.uid, provider: provider.clone(), endpoint: endpoint.clone(), body_sha256, secret, expires: now + TICKET_TTL });
    Ok(json!({"ok":true,"ticket":id,"provider":provider,"endpoint":endpoint,"route":route,"ownerEpoch":epoch,"expiresInS":TICKET_TTL.as_secs()}))
}

/// What one forward resolved to: an endpoint and maybe a bearer.
struct Plan {
    endpoint: String,
    secret: Option<Secret>,
}

fn create_private(path: &Path, bytes: &[u8]) -> Result<(), String> {
    let mut f = OpenOptions::new().write(true).create_new(true).mode(0o600).custom_flags(libc::O_NOFOLLOW).open(path).map_err(|e| format!("spool: {e}"))?;
    f.write_all(bytes).and_then(|_| f.sync_all()).map_err(|e| format!("spool: {e}"))
}

fn read_bounded(path: &Path, bound: usize) -> Result<Vec<u8>, String> {
    let mut out = Vec::new();
    File::open(path).and_then(|f| f.take(bound as u64 + 1).read_to_end(&mut out)).map_err(|e| format!("spool: {e}"))?;
    if out.len() > bound {
        return Err("provider response exceeds its bound".into());
    }
    Ok(out)
}

fn header_config(secret: &Secret) -> String {
    let escaped = secret.expose().replace('\\', "\\\\").replace('"', "\\\"");
    format!("header = \"Authorization: Bearer {escaped}\"\n")
}

/// True once the caller has closed or shut down its end: nobody waits for this
/// response, so the provider call stops (the controller revokes a lease this way).
pub fn caller_gone(stream: &UnixStream) -> bool {
    let mut p = libc::pollfd { fd: stream.as_raw_fd(), events: libc::POLLIN, revents: 0 };
    if unsafe { libc::poll(&mut p, 1, 0) } <= 0 {
        return false;
    }
    if p.revents & (libc::POLLHUP | libc::POLLERR) != 0 {
        return true;
    }
    let mut byte = [0u8; 1];
    let n = unsafe { libc::recv(stream.as_raw_fd(), byte.as_mut_ptr() as *mut libc::c_void, 1, libc::MSG_PEEK | libc::MSG_DONTWAIT) };
    n == 0
}

enum Sent {
    Received { complete: bool, headers: Vec<u8>, body: Vec<u8> },
    Withheld,
    CallerGone,
}

fn send(spool: &Path, plan: &Plan, body: &[u8], timeout: Duration, max_response: usize, caller: &UnixStream) -> Result<Sent, Refusal> {
    let seq = SEQ.fetch_add(1, Ordering::SeqCst);
    let prefix = format!("forward-{}-{seq}", std::process::id());
    let request_path = spool.join(format!("{prefix}.request"));
    let body_path = spool.join(format!("{prefix}.response"));
    let header_path = spool.join(format!("{prefix}.headers"));
    let cleanup = |paths: &[&PathBuf]| {
        for p in paths {
            let _ = std::fs::remove_file(p);
        }
    };
    if let Err(e) = create_private(&request_path, body).and_then(|_| create_private(&body_path, b"")).and_then(|_| create_private(&header_path, b"")) {
        cleanup(&[&request_path, &body_path, &header_path]);
        return Err(refuse("not-sent", e));
    }
    let protocol = if plan.endpoint.starts_with("https://") { "=https" } else { "=http" };
    let mut command = Command::new(super::CURL);
    command
        .env_clear()
        .current_dir(spool)
        .arg("--disable")
        .args(["--silent", "--http1.1", "--request", "POST"])
        .args(["--proto", protocol, "--noproxy", "*", "--proxy", ""])
        .args(["--max-redirs", "0", "--connect-timeout", "10"])
        .args(["--max-time", &timeout.as_secs().max(1).to_string()])
        .args(["--max-filesize", &max_response.to_string()])
        .args(["--header", "Content-Type: application/json"])
        .args(["--header", "Accept-Encoding: identity"])
        .arg("--data-binary")
        .arg(format!("@{}", request_path.display()))
        .arg("--dump-header")
        .arg(&header_path)
        .arg("--output")
        .arg(&body_path)
        .arg("--url")
        .arg(&plan.endpoint)
        .args(["--config", "-"])
        .stdin(Stdio::piped())
        .stdout(Stdio::null())
        .stderr(Stdio::null());
    let file_limit = max_response.max(MAX_HEADERS) as libc::rlim_t;
    unsafe {
        command.pre_exec(move || {
            let limit = libc::rlimit { rlim_cur: file_limit, rlim_max: file_limit };
            let no_core = libc::rlimit { rlim_cur: 0, rlim_max: 0 };
            if libc::setrlimit(libc::RLIMIT_FSIZE, &limit) == 0 && libc::setrlimit(libc::RLIMIT_CORE, &no_core) == 0 {
                Ok(())
            } else {
                Err(std::io::Error::last_os_error())
            }
        });
    }
    let mut child = match command.spawn() {
        Ok(c) => c,
        Err(e) => {
            cleanup(&[&request_path, &body_path, &header_path]);
            return Err(refuse("not-sent", format!("provider transport spawn: {e}")));
        }
    };
    // The bearer reaches curl as config on stdin: never argv, never a file.
    let written = child.stdin.take().is_some_and(|mut stdin| match &plan.secret {
        Some(secret) => {
            let mut line = header_config(secret).into_bytes();
            let ok = stdin.write_all(&line).is_ok();
            wire::zero(&mut line);
            ok
        }
        None => true,
    });
    if !written {
        let _ = child.kill();
    }
    let started = Instant::now();
    let mut gone = false;
    let status = loop {
        match child.try_wait() {
            Ok(Some(status)) => break Some(status),
            Ok(None) => {}
            Err(_) => break None,
        }
        let oversized = [(&body_path, max_response), (&header_path, MAX_HEADERS)]
            .iter()
            .any(|(path, bound)| std::fs::metadata(path).is_ok_and(|m| m.len() > *bound as u64));
        if caller_gone(caller) {
            gone = true;
        }
        if oversized || gone || started.elapsed() > timeout {
            let _ = child.kill();
        }
        std::thread::sleep(Duration::from_millis(20));
    };
    let headers = read_bounded(&header_path, MAX_HEADERS);
    let response = read_bounded(&body_path, max_response);
    cleanup(&[&request_path, &body_path, &header_path]);
    if gone {
        return Ok(Sent::CallerGone);
    }
    let (headers, response) = match (headers, response) {
        (Ok(h), Ok(b)) => (h, b),
        _ => return Ok(Sent::Received { complete: false, headers: vec![], body: vec![] }),
    };
    if let Some(secret) = &plan.secret {
        let s = secret.expose().as_bytes();
        if headers.windows(s.len()).any(|w| w == s) || response.windows(s.len()).any(|w| w == s) {
            return Ok(Sent::Withheld);
        }
    }
    let complete = written && status.is_some_and(|s| s.success());
    Ok(Sent::Received { complete, headers, body: response })
}

/// `provider-forward`: one POST of the exact body the ticket names (or, for a
/// homelab row, of any body to that row's endpoint, without a bearer).
pub fn forward(broker: &Broker, peer: &Peer, request: &Value, stream: &mut UnixStream, note: &mut Note) -> Result<Value, Refusal> {
    exact(request, &["op", "ticket", "homelab", "body", "timeoutMs", "maxResponseBytes"])?;
    let body = wire::unhex(text(request, "body")?).map_err(|e| refuse("bad-request", e))?;
    if body.is_empty() || body.len() > wire::MAX_PROVIDER_REQUEST {
        return Err(refuse("bad-request", "body must be 1..1 MiB"));
    }
    let timeout = Duration::from_millis(number(request, "timeoutMs")?).min(MAX_TIMEOUT).max(Duration::from_secs(1));
    let max_response = (number(request, "maxResponseBytes")? as usize).min(wire::MAX_PROVIDER_RESPONSE);
    let body_sha256 = native::sha256_hex(&body);
    note.set("bodySha256", body_sha256.clone());
    let plan = match (request.get("ticket"), request.get("homelab")) {
        (Some(_), None) => {
            let id = text(request, "ticket")?;
            note.set("ticketSha256", native::sha256_hex(id.as_bytes())[..16].to_owned());
            let ticket = broker
                .tickets
                .lock()
                .map_err(|_| refuse("internal", "ticket table poisoned"))?
                .remove(id)
                .ok_or_else(|| refuse("ticket-unknown", "no live ticket by that id (used, expired, or minted before a broker restart): authorize again"))?;
            note.set("provider", ticket.provider.clone());
            if ticket.peer != peer.uid {
                return Err(refuse("ticket-not-yours", format!("the ticket was minted for uid {}", ticket.peer)));
            }
            if ticket.expires <= Instant::now() {
                return Err(refuse("ticket-expired", "authorize again"));
            }
            if ticket.body_sha256 != body_sha256 {
                return Err(refuse("ticket-body-mismatch", "the body differs from the one this ticket was minted for"));
            }
            Plan { endpoint: ticket.endpoint.clone(), secret: Some(ticket.secret) }
        }
        (None, Some(_)) => {
            let name = text(request, "homelab")?;
            note.set("provider", name);
            let table = table(broker)?;
            let row = table.rows.iter().find(|r| r.name == name).ok_or_else(|| refuse("provider-row-unknown", format!("the provider table has no row {name}")))?;
            if row.credential != CredentialSource::Homelab {
                return Err(refuse("provider-kind-mismatch", format!("row {name} carries a credential: authorize a ticket")));
            }
            Plan { endpoint: row.endpoint.clone(), secret: None }
        }
        _ => return Err(refuse("bad-request", "exactly one of ticket or homelab")),
    };
    credentials::validate_endpoint(&plan.endpoint).map_err(|e| refuse("provider-table", e))?;
    match send(&broker.config.spool, &plan, &body, timeout, max_response, stream)? {
        Sent::Received { complete, headers, body } => {
            note.set("complete", complete);
            note.set("responseBytes", body.len());
            Ok(json!({"ok":true,"complete":complete,"headers":wire::hex(&headers),"body":wire::hex(&body)}))
        }
        Sent::Withheld => {
            note.set("withheld", true);
            Ok(json!({"ok":true,"withheld":true}))
        }
        Sent::CallerGone => Err(refuse("caller-gone", "the caller closed the connection; the provider call was stopped")),
    }
}

/// `provider-verify-grant`: the member's grant for this runner/model at the
/// broker's own observation of the key epoch. No call is counted.
pub fn verify_grant(broker: &Broker, request: &Value, note: &mut Note) -> Result<Value, Refusal> {
    exact(request, &["op", "owner", "provider", "runner", "model", "epoch", "height"])?;
    let owner = owner_of(request)?;
    let provider = text(request, "provider")?;
    note.set("subject", owner.subject.clone());
    note.set("provider", provider);
    let epoch = observed_epoch(broker, &owner)?;
    if epoch != text(request, "epoch")? {
        return Err(refuse(&credentials::refused("owner-epoch-changed"), "the Store names another current key epoch"));
    }
    let grant = store(broker)?
        .verify_grant(&owner, provider, text(request, "runner")?, text(request, "model")?, &epoch, number(request, "height")?)
        .map_err(store_refusal)?;
    Ok(json!({"ok":true,"grant":grant.to_json()}))
}

/// `provider-selected-choice`: the member's signed provider choice for a task.
pub fn selected_choice(broker: &Broker, request: &Value, note: &mut Note) -> Result<Value, Refusal> {
    exact(request, &["op", "owner", "runner", "task"])?;
    let owner = owner_of(request)?;
    note.set("subject", owner.subject.clone());
    let table = table(broker)?;
    let choice = store(broker)?.selected(&owner, text(request, "runner")?, text(request, "task")?, &table).map_err(store_refusal)?;
    Ok(json!({"ok":true,"choice":choice.to_json()}))
}

/// `pool` (root only): the operator's own provider key.
pub fn pool(broker: &Broker, request: &Value, note: &mut Note) -> Result<Value, Refusal> {
    let action = text(request, "action")?.to_owned();
    note.set("action", action.clone());
    let store = store(broker)?;
    let result = match action.as_str() {
        "set" => {
            exact(request, &["op", "action", "provider", "secret"])?;
            let provider = text(request, "provider")?;
            note.set("provider", provider);
            let table = table(broker)?;
            if !table.rows.iter().any(|r| r.name == provider && r.credential == CredentialSource::Pool) {
                return Err(refuse("provider-kind-mismatch", format!("{provider} is not a pool row")));
            }
            let secret = Secret::new(text(request, "secret")?.to_owned()).map_err(|e| refuse("bad-request", e))?;
            store.set(Namespace::Pool, provider, &secret).map_err(store_refusal)?;
            json!({"type":"mini-key-set-v1","owner":"pool","provider":provider,"stored":"sealed","existingGrants":"preserved","next":"none: the purse gates pool spend"})
        }
        "revoke" => {
            exact(request, &["op", "action", "provider", "runner"])?;
            let provider = text(request, "provider")?;
            note.set("provider", provider);
            let runner = request.get("runner").map(|_| text(request, "runner")).transpose()?;
            let removed = store.revoke(Namespace::Pool, provider, runner).map_err(store_refusal)?;
            json!({"type":"mini-key-revoke-v1","owner":"pool","provider":provider,"runner":runner,"removed":removed,
                "effect":"Future reservations refuse; an already authorized request may finish."})
        }
        "ls" => {
            exact(request, &["op", "action"])?;
            let mut listed = store.list(Namespace::Pool).map_err(store_refusal)?;
            listed["owner"] = json!("pool");
            listed
        }
        _ => return Err(refuse("bad-request", "pool action must be set, revoke or ls")),
    };
    Ok(json!({"ok":true,"result":result}))
}
