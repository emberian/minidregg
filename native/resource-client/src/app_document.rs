//! A delegated app export is retained once, then written using this
//! participant's ordinary document authority. App response provenance is
//! explicitly host/TLS custody, not a kernel attestation of app state.
//!
//! Custody is the SDK's (`mini_sdk`), not a local state machine. The export fetch is an EXTERNAL
//! effect: `custody::Delivery` (a started, uncompleted fetch is UNKNOWN and is never repeated; only
//! the retained export completes it), persisted with `store::atomic_json`, phase markers with
//! `store::write_once`. The document write is a Mini call: its retained attempt directory is read
//! by `workspace::retained_attempt_outcome` (`store::AttemptDir::outcome`, one classification rule
//! shared by every client).
use super::*;
use mini_sdk::custody::{Delivery, DeliveryState};
use mini_sdk::store;
use chacha20poly1305::{
    aead::{Aead, Payload},
    ChaCha20Poly1305, KeyInit, Nonce,
};
use std::time::{Duration, Instant};
use zeroize::Zeroizing;

const FRAME: &[u8] = b"MINI/APP-DOCUMENT-CUSTODY/v1";
const MAX_EXPORT: usize = 128 * 1024;
const MAX_CAPTURE: u64 = MAX_SEEN * 2 + 1024 * 1024;

fn exact(v: &Value, fields: &[&str]) -> Result<()> {
    let o = v.as_object().ok_or("connector binding must be an object")?;
    if o.len() != fields.len() || fields.iter().any(|f| !o.contains_key(*f)) {
        return Err("connector binding has unexpected or missing fields".into());
    }
    Ok(())
}
fn validate(binding: &Value, workspace: &Value) -> Result<()> {
    exact(
        binding,
        &[
            "type",
            "subject",
            "appReference",
            "packageReference",
            "packageManifest",
            "sessionKind",
            "credentialKind",
            "app",
            "generation",
            "session",
            "sessionGeneration",
            "ticket",
            "document",
            "documentCapability",
            "taskReference",
            "task",
            "sheet",
            "endpoint",
            "apiPath",
            "token",
            "ca",
        ],
    )?;
    if binding["type"] != "mini-app-document-binding-v1"
        || binding["subject"] != workspace["subject"]
    {
        return Err("connector binding belongs to another participant".into());
    }
    for name in [
        "app",
        "packageManifest",
        "generation",
        "session",
        "sessionGeneration",
        "ticket",
        "documentCapability",
        "task",
    ] {
        field_decimal(member(binding, name)?, name)?;
    }
    for name in [
        "appReference",
        "packageReference",
        "document",
        "taskReference",
    ] {
        validate_ref_name(member(binding, name)?)?;
    }
    let sheet = member(binding, "sheet")?;
    if sheet.is_empty()
        || sheet.len() > 128
        || !sheet
            .bytes()
            .all(|b| b.is_ascii_alphanumeric() || b"-_".contains(&b))
    {
        return Err("sheet must be a simple EtherCalc sheet name".into());
    }
    let endpoint = member(binding, "endpoint")?;
    minidregg_pay_watcher::transport::validate_endpoint(endpoint)?;
    if !endpoint.starts_with("https://")
        || endpoint.contains(['?', '#'])
        || !endpoint.ends_with('/')
    {
        return Err("connector requires an HTTPS app route ending in slash".into());
    }
    match (
        binding["sessionKind"].as_str(),
        binding["credentialKind"].as_str(),
    ) {
        (Some("web"), Some("cookie")) if binding["apiPath"].is_null() => {}
        (Some("api"), Some("bearer"))
            if matches!(binding["apiPath"].as_str(), Some("/_/" | "/")) => {}
        _ => {
            return Err(
                "connector credential kind differs from its source session/interface".into(),
            )
        }
    }
    let token = member(binding, "token")?;
    if token.len() < 32
        || token.len() > 256
        || !token
            .bytes()
            .all(|b| b.is_ascii_alphanumeric() || b"-_".contains(&b))
    {
        return Err("connector requires its own app API credential".into());
    }
    if !binding["ca"].is_null() {
        let _ = absolute(&member_path(binding, "ca")?)?;
    }
    Ok(())
}
fn operation(root: &Path, id: &str) -> Result<PathBuf> {
    validate_name(id)?;
    Ok(root.join("app-documents").join(id))
}
fn store_key(root: &Path) -> Result<Zeroizing<[u8; 32]>> {
    let parent = root.join("app-documents");
    if !parent.exists() {
        make_private_dir(&parent)?;
    }
    private_dir(&parent)?;
    let _lock = crate::transport::service_lock(&parent.join("storage-key.lock"))?;
    let path = parent.join("storage.key");
    if !path.exists() {
        if fs::read_dir(&parent)
            .map_err(|e| e.to_string())?
            .any(|e| e.is_ok_and(|e| e.path().is_dir()))
        {
            return Err("connector custody key is missing; restore the complete workspace, no replacement key was created".into());
        }
        let mut seed = Zeroizing::new([0u8; 32]);
        crate::fsio::random_fill(&mut *seed)?;
        replace_private_file(&path, &*seed)?;
    }
    let secret = Zeroizing::new(crate::read_secret(&path)?.to_bytes());
    Ok(secret)
}
fn aad(workspace: &Value, id: &str) -> Result<Vec<u8>> {
    Ok([
        FRAME,
        b"\0",
        member(workspace, "subject")?.as_bytes(),
        b"\0",
        id.as_bytes(),
    ]
    .concat())
}
fn seal(root: &Path, workspace: &Value, id: &str, v: &Value) -> Result<()> {
    let key = store_key(root)?;
    let bytes = Zeroizing::new(serde_json::to_vec(v).map_err(|e| e.to_string())?);
    let nonce = crate::fsio::random::<12>()?;
    let cipher = ChaCha20Poly1305::new_from_slice(&*key)
        .map_err(|_| "invalid custody key")?
        .encrypt(
            Nonce::from_slice(&nonce),
            Payload {
                msg: &bytes,
                aad: &aad(workspace, id)?,
            },
        )
        .map_err(|_| "custody encryption failed")?;
    let path = operation(root, id)?.join("capture.enc");
    if path.exists() {
        return Err("complete export custody already exists; no replacement".into());
    }
    replace_private_file(&path, &[FRAME, &nonce, &cipher].concat())
}
fn opened(root: &Path, workspace: &Value, id: &str) -> Result<Value> {
    let path = operation(root, id)?.join("capture.enc");
    private_dir(path.parent().ok_or("missing operation directory")?)?;
    let bytes = fs::read(&path).map_err(|e| e.to_string())?;
    if bytes.len() as u64 > MAX_CAPTURE
        || !bytes.starts_with(FRAME)
        || bytes.len() < FRAME.len() + 12 + 16
    {
        return Err("encrypted connector custody has invalid framing".into());
    }
    let key = store_key(root)?;
    let nonce = &bytes[FRAME.len()..FRAME.len() + 12];
    let plain = Zeroizing::new(
        ChaCha20Poly1305::new_from_slice(&*key)
            .map_err(|_| "invalid custody key")?
            .decrypt(
                Nonce::from_slice(nonce),
                Payload {
                    msg: &bytes[FRAME.len() + 12..],
                    aad: &aad(workspace, id)?,
                },
            )
            .map_err(|_| "connector custody integrity failed")?,
    );
    let value = serde_json::from_slice(&plain).map_err(|e| e.to_string())?;
    Ok(value)
}
/// Immutable phase records are atomically published under their custody lock: written once, an
/// equal retry accepted, a different record refused (`store::write_once`).
fn save(path: &Path, v: &Value) -> Result<()> {
    Ok(store::write_once(path, v)?)
}

/// What a fetch IS, fixed before it starts: the same retained export is the same fetch.
fn fetch_binding(binding: &Value, document_target: &Value, id: &str) -> Value {
    json!({"type":"mini-app-document-fetch-v1","id":id,"subject":binding["subject"],"app":binding["app"],
        "generation":binding["generation"],"document":document_target})
}

/// The fetch's custody record for operation `id`, if it ever started.
fn fetch_delivery(dir: &Path, binding: Value) -> Result<Delivery> {
    Ok(Delivery::open(binding, store::read_json(&dir.join("fetch.json"))?)?)
}

fn unix_seconds() -> u64 {
    std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).map_or(0, |d| d.as_secs())
}

/// Discovery heads change when an admitted export or an unrelated write lands.
/// Keep target, authority and encryption custody stable; source admission checks
/// their current meaning again. Retained discovery observations remain evidence.
fn stable_refs(refs: &Value) -> Value {
    let mut result = json!({});
    for name in ["app", "package", "task", "document"] {
        let mut identity = json!({});
        for field in [
            "kind",
            "target",
            "observeCapability",
            "operationCapability",
            "controlCapability",
            "sealedIn",
            "sealedRoom",
            "private",
            "protectedDocument",
            "room",
        ] {
            if let Some(v) = refs[name].get(field) {
                identity[field] = v.clone();
            }
        }
        result[name] = identity;
    }
    result
}

fn read_refs(root: &Path, binding: &Value) -> Result<Value> {
    let app = reference(root, member(binding, "appReference")?)?;
    let task = reference(root, member(binding, "taskReference")?)?;
    let package = reference(root, member(binding, "packageReference")?)?;
    let doc = reference(root, member(binding, "document")?)?;
    if app["target"] != binding["app"]
        || task["target"] != binding["task"]
        || package["target"] != binding["packageManifest"]
        || doc["operationCapability"] != binding["documentCapability"]
        || [binding["app"].clone(), binding["task"].clone()].contains(&doc["target"])
    {
        return Err(
            "connector's explicit app/task/document grant binding differs from held references"
                .into(),
        );
    }
    Ok(json!({"app":app,"package":package,"task":task,"document":doc}))
}

/// Parse a completed response capture. Duplicate reserved headers, altered
/// source selectors, request coordinate or bytes are refused before a proposal.
fn checked_receipt(headers: &[u8], body: &[u8], binding: &Value, capture: &str) -> Result<Value> {
    if headers.len() > 64 * 1024 || body.len() > MAX_EXPORT {
        return Err("export exceeds connector bounds".into());
    }
    let head = std::str::from_utf8(headers).map_err(|_| "export headers are not text")?;
    if !head.starts_with("HTTP/1.1 200 ") {
        return Err("app export did not return a successful representation".into());
    }
    let receipts: Vec<_> = head
        .split("\r\n")
        .filter_map(|line| line.split_once(':'))
        .filter(|(name, _)| name.eq_ignore_ascii_case("x-mini-export-receipt"))
        .collect();
    if receipts.len() != 1 {
        return Err("app route supplied no unique admitted export receipt".into());
    }
    let bytes = mini_sdk::hex::decode(receipts[0].1.trim()).map_err(|e| e.0)?;
    if bytes.len() > 8192 {
        return Err("export receipt exceeds bound".into());
    }
    let receipt: Value = serde_json::from_slice(&bytes).map_err(|e| e.to_string())?;
    if receipt["type"] != "mini-spk-export-custody-v1"
        || receipt["capture"] != capture
        || receipt["method"] != "GET"
        || receipt["signedApiPath"] != binding["apiPath"]
        || receipt["query"] != ""
        || receipt["path"] != format!("_/{}/csv", member(binding, "sheet")?)
        || receipt["bodyBytes"] != body.len().to_string()
        || receipt["bodySha256"] != format!("{:x}", Sha256::digest(body))
    {
        return Err("export receipt differs from this exact request or response body".into());
    }
    for field in [
        "app",
        "packageManifest",
        "generation",
        "subject",
        "sessionKind",
        "credentialKind",
        "session",
        "sessionGeneration",
        "ticket",
    ] {
        if receipt[field] != binding[field] {
            return Err(format!(
                "export receipt {field} differs from the connector binding"
            ));
        }
    }
    for field in ["operation", "transaction", "event", "requestDigest"] {
        field_decimal(member(&receipt, field)?, field)?;
    }
    let digest = member(&receipt, "permitSha256")?;
    if digest.len() != 64
        || !mini_sdk::hex::is_lower(digest)
    {
        return Err("export source permit digest is malformed".into());
    }
    Ok(receipt)
}

/// Exactly one bounded HTTPS fetch, over the client's own TLS (rustls on aws-lc-rs), so the export
/// speaks the hybrid key exchange the browser entrance requires (`spk-browser-proxy` accepts
/// X25519MLKEM768 only) whatever OpenSSL the member's machine carries. Bounds: 10 s connect, 90 s
/// whole exchange, HTTP/1.1 GET, no redirect followed, headers within 64 KiB, body within
/// MAX_EXPORT. A status of 400 or more is a refusal. The credential never reaches argv or a file;
/// the export passes through memory into encrypted custody.
fn fetch(_dir: &Path, binding: &Value, capture: &str) -> Result<(Vec<u8>, Vec<u8>)> {
    let relative = if binding["apiPath"] == "/_/" {
        format!("{}/csv", member(binding, "sheet")?)
    } else {
        format!("_/{}/csv", member(binding, "sheet")?)
    };
    let url = format!("{}{relative}", member(binding, "endpoint")?);
    let target = ExportTarget::parse(&url)?;
    let credential = if binding["credentialKind"] == "cookie" {
        format!("Cookie: __Host-mini_spk_session={}", member(binding, "token")?)
    } else {
        format!("Authorization: Bearer {}", member(binding, "token")?)
    };
    for value in [credential.as_str(), capture] {
        if value.bytes().any(|b| b.is_ascii_control()) {
            return Err("unsafe export request header value".into());
        }
    }
    let ca = if binding["ca"].is_null() { None } else { Some(member(binding, "ca")?) };
    let request = Zeroizing::new(format!(
        "GET {} HTTP/1.1\r\nHost: {}\r\n{credential}\r\nX-Mini-Export-Capture: {capture}\r\nAccept-Encoding: identity\r\nConnection: close\r\n\r\n",
        target.path, target.authority
    ));
    let deadline = Instant::now() + Duration::from_secs(90);
    let raw = export_exchange(&target, ca, request.as_bytes(), deadline)
        .map_err(|why| format!("export did not complete ({why}); retain this exact operation as source-uncertain"))?;
    let (head, body) = split_export_response(&raw)?;
    Ok((head, body))
}

struct ExportTarget {
    host: String,
    port: u16,
    authority: String,
    path: String,
}

impl ExportTarget {
    fn parse(url: &str) -> Result<Self> {
        let rest = url.strip_prefix("https://").ok_or("export endpoint must be https")?;
        let (authority, path) = match rest.find('/') {
            Some(i) => (&rest[..i], &rest[i..]),
            None => (rest, "/"),
        };
        let (host, port) = match authority.rsplit_once(':') {
            Some((host, port)) => (host, port.parse::<u16>().map_err(|_| "export endpoint port is malformed")?),
            None => (authority, 443),
        };
        if host.is_empty()
            || !host.bytes().all(|b| b.is_ascii_alphanumeric() || b == b'.' || b == b'-')
            || !path.bytes().all(|b| b.is_ascii_graphic())
        {
            return Err("export endpoint host or path is malformed".into());
        }
        Ok(Self { host: host.to_ascii_lowercase(), port, authority: authority.to_owned(), path: path.to_owned() })
    }

    /// RFC 6761: a `localhost` name is loopback, never a resolver question (curl's rule too).
    fn addresses(&self) -> std::result::Result<Vec<std::net::SocketAddr>, String> {
        use std::net::ToSocketAddrs;
        if self.host == "localhost" || self.host.ends_with(".localhost") {
            return Ok(vec![std::net::SocketAddr::from(([127, 0, 0, 1], self.port))]);
        }
        (self.host.as_str(), self.port)
            .to_socket_addrs()
            .map(|a| a.collect())
            .map_err(|e| format!("resolve: {e}"))
    }
}

fn export_tls_config(ca: Option<&str>) -> std::result::Result<rustls::ClientConfig, String> {
    use rustls::crypto::aws_lc_rs::{self as provider, kx_group};
    let pem = match ca {
        Some(path) => std::fs::read(path).map_err(|e| format!("read CA {path}: {e}"))?,
        None => ["/etc/ssl/certs/ca-certificates.crt", "/etc/ssl/cert.pem", "/etc/pki/tls/certs/ca-bundle.crt"]
            .iter()
            .find_map(|path| std::fs::read(path).ok())
            .ok_or("no system CA bundle")?,
    };
    let mut roots = rustls::RootCertStore::empty();
    for cert in rustls_pemfile::certs(&mut std::io::Cursor::new(pem)) {
        let cert = cert.map_err(|e| format!("CA PEM: {e}"))?;
        let _ = roots.add(cert);
    }
    if roots.is_empty() {
        return Err("CA bundle holds no certificate".into());
    }
    let mut crypto = provider::default_provider();
    // The hybrid share first, so the entrance answers without a retry; classical groups after it
    // for an ordinary public endpoint.
    crypto.kx_groups = vec![kx_group::X25519MLKEM768, kx_group::X25519, kx_group::SECP256R1];
    Ok(rustls::ClientConfig::builder_with_provider(std::sync::Arc::new(crypto))
        .with_safe_default_protocol_versions()
        .map_err(|e| format!("TLS config: {e}"))?
        .with_root_certificates(roots)
        .with_no_client_auth())
}

/// The response, read until its framing is complete (Content-Length met, the chunked terminator
/// and trailer section seen) or, for a close-delimited body, to the server's close; within the
/// bound and the deadline. Resolution, every connect, the handshake, the request and each read
/// draw on the one deadline. A status of 400 or more ends the exchange as soon as the head is in.
fn export_exchange(target: &ExportTarget, ca: Option<&str>, request: &[u8], deadline: Instant) -> std::result::Result<Vec<u8>, String> {
    use std::io::{Read, Write};
    let remaining = || deadline.checked_duration_since(Instant::now()).filter(|d| !d.is_zero()).ok_or_else(|| "deadline".to_owned());
    let config = export_tls_config(ca)?;
    let addresses = {
        let (tx, rx) = std::sync::mpsc::channel();
        let lookup = ExportTarget { host: target.host.clone(), port: target.port, authority: String::new(), path: String::new() };
        std::thread::spawn(move || {
            let _ = tx.send(lookup.addresses());
        });
        rx.recv_timeout(remaining()?.min(Duration::from_secs(10))).map_err(|_| "resolve: deadline".to_owned())??
    };
    let mut tcp = None;
    let mut last = String::from("no address");
    for addr in addresses {
        match std::net::TcpStream::connect_timeout(&addr, remaining()?.min(Duration::from_secs(10))) {
            Ok(stream) => {
                tcp = Some(stream);
                break;
            }
            Err(e) => last = format!("connect {addr}: {e}"),
        }
    }
    let tcp = tcp.ok_or(last)?;
    let name = rustls::pki_types::ServerName::try_from(target.host.clone()).map_err(|e| format!("server name: {e}"))?;
    let connection = rustls::ClientConnection::new(std::sync::Arc::new(config), name).map_err(|e| format!("TLS: {e}"))?;
    let mut tls = rustls::StreamOwned::new(connection, tcp);
    let arm = |sock: &std::net::TcpStream| -> std::result::Result<(), String> {
        let left = remaining()?;
        sock.set_read_timeout(Some(left)).and_then(|_| sock.set_write_timeout(Some(left))).map_err(|e| e.to_string())
    };
    while tls.conn.is_handshaking() {
        arm(&tls.sock)?;
        tls.conn.complete_io(&mut tls.sock).map_err(|e| format!("TLS/handshake: {e}"))?;
    }
    arm(&tls.sock)?;
    tls.write_all(request).and_then(|_| tls.flush()).map_err(|e| format!("TLS/send: {e}"))?;
    // Chunk framing can exceed the decoded body several times over; the decoded body is bounded
    // again by split_export_response.
    let bound = 64 * 1024 + 4 * MAX_EXPORT;
    let mut raw = Zeroizing::new(Vec::new());
    let mut chunk = [0u8; 16 * 1024];
    loop {
        arm(&tls.sock)?;
        match tls.read(&mut chunk) {
            Ok(0) => break,
            Ok(n) => {
                raw.extend_from_slice(&chunk[..n]);
                if raw.len() > bound {
                    return Err("export response exceeds bound".into());
                }
                if let Some(code) = export_status(&raw) {
                    if code >= 400 {
                        return Err(format!("http={code}"));
                    }
                    if export_framed(&raw) && split_export_response(&raw).is_ok() {
                        break;
                    }
                }
            }
            // A server that closes without close_notify: split_export_response checks the framing.
            Err(e) if e.kind() == std::io::ErrorKind::UnexpectedEof => break,
            Err(e) if e.kind() == std::io::ErrorKind::Interrupted => continue,
            Err(e) => return Err(format!("TLS/receive: {e}")),
        }
    }
    match export_status(&raw) {
        Some(code) if code >= 400 => Err(format!("http={code}")),
        Some(_) => Ok(std::mem::take(&mut *raw)),
        None => Err("no complete HTTP head".into()),
    }
}

/// The status once the whole head has arrived.
fn export_status(raw: &[u8]) -> Option<u16> {
    raw.windows(4).position(|w| w == b"\r\n\r\n")?;
    let line = raw.split(|b| *b == b'\r').next()?;
    let line = std::str::from_utf8(line).ok()?;
    let mut parts = line.splitn(3, ' ');
    if parts.next()? != "HTTP/1.1" {
        return None;
    }
    parts.next()?.parse().ok()
}

/// Whether the body is length- or chunk-delimited (else it runs to the close).
fn export_framed(raw: &[u8]) -> bool {
    let Some(end) = raw.windows(4).position(|w| w == b"\r\n\r\n") else { return false };
    let head = String::from_utf8_lossy(&raw[..end]).to_ascii_lowercase();
    head.split("\r\n").skip(1).any(|l| l.starts_with("content-length:") || l.starts_with("transfer-encoding:"))
}

/// Head (through the blank line) and the body as delivered: chunked framing is decoded (the
/// terminal chunk and its trailer section are required), a Content-Length must be met exactly,
/// otherwise the body runs to the close. Head within 64 KiB, body within MAX_EXPORT.
fn split_export_response(raw: &[u8]) -> Result<(Vec<u8>, Vec<u8>)> {
    let end = raw.windows(4).position(|w| w == b"\r\n\r\n").ok_or("export response framing missing")?;
    if end + 4 > 64 * 1024 {
        return Err("export exceeds connector bounds".into());
    }
    let head = raw[..end + 4].to_vec();
    let rest = &raw[end + 4..];
    let text = std::str::from_utf8(&head).map_err(|_| "export headers are not text")?;
    let field = |name: &str| {
        text.split("\r\n").skip(1).filter_map(|l| l.split_once(':')).find(|(k, _)| k.trim().eq_ignore_ascii_case(name)).map(|(_, v)| v.trim().to_owned())
    };
    if let Some(coding) = field("transfer-encoding") {
        // Accept-Encoding: identity was asked; chunked is the only transfer coding accepted.
        if !coding.eq_ignore_ascii_case("chunked") {
            return Err("export transfer coding is not chunked alone".into());
        }
        let mut body = Vec::new();
        let mut at = 0usize;
        loop {
            let line_end = rest.get(at..).and_then(|r| r.windows(2).position(|w| w == b"\r\n")).ok_or("export chunk framing incomplete")? + at;
            let size_text = std::str::from_utf8(&rest[at..line_end]).map_err(|_| "export chunk size is not text")?;
            let size = usize::from_str_radix(size_text.split(';').next().unwrap_or("").trim(), 16).map_err(|_| "export chunk size is malformed")?;
            at = line_end + 2;
            if size == 0 {
                // The trailer section: header lines up to an empty line.
                let tail = rest.get(at..).ok_or("export chunk framing incomplete")?;
                if tail.starts_with(b"\r\n") || tail.windows(4).any(|w| w == b"\r\n\r\n") {
                    return Ok((head, body));
                }
                return Err("export chunk framing incomplete".into());
            }
            if size > MAX_EXPORT - body.len().min(MAX_EXPORT) {
                return Err("export exceeds connector bounds".into());
            }
            let data_end = at.checked_add(size).ok_or("export chunk size overflows")?;
            let crlf_end = data_end.checked_add(2).ok_or("export chunk size overflows")?;
            if rest.len() < crlf_end || &rest[data_end..crlf_end] != b"\r\n" {
                return Err("export chunk framing incomplete".into());
            }
            body.extend_from_slice(&rest[at..data_end]);
            at = crlf_end;
        }
    }
    if rest.len() > MAX_EXPORT {
        return Err("export exceeds connector bounds".into());
    }
    if let Some(length) = field("content-length") {
        let length: usize = length.parse().map_err(|_| "export Content-Length is malformed")?;
        if rest.len() != length {
            return Err("export body is shorter or longer than its Content-Length".into());
        }
    }
    Ok((head, rest.to_vec()))
}

fn occupied_capture(
    root: &Path,
    workspace: &Value,
    binding: &Value,
    id: &str,
) -> Result<Option<Value>> {
    let dir = operation(root, id)?;
    if dir.join("capture.enc").exists() {
        if opened(root, workspace, id)?["binding"] != *binding {
            return Err("capture identity already belongs to another binding".into());
        }
        return Ok(Some(status(root, workspace, id)?));
    }
    if dir.join("fetch.json").exists() {
        return Ok(Some(status(root, workspace, id)?));
    }
    Ok(None)
}

fn publishable_id(id: &str) -> Result<()> {
    validate_name(&format!("app-{id}"))
        .map_err(|_| "connector identity must contain 1..60 ASCII letters, digits or hyphens".to_owned())
}

pub(crate) fn capture(root: &Path, workspace: &Value, binding: &Value, id: &str) -> Result<Value> {
    validate_name(id)?;
    publishable_id(id)?;
    validate(binding, workspace)?;
    let dir = operation(root, id)?;
    let _key = store_key(root)?;
    if dir.exists() {
        let v = opened(root, workspace, id)?;
        if v["binding"] != *binding {
            return Err("capture identity already belongs to another binding".into());
        }
        return status(root, workspace, id);
    }
    let refs = read_refs(root, binding)?;
    // All discovery and reads run as the connector, never the app owner.
    let (app, app_challenge, _) = signed_view(root, workspace, &refs["app"], "resource")?;
    let generation = entries(&app)?
        .iter()
        .find(|e| e["key"]["field"] == "0")
        .map(|e| e["value"].clone());
    if generation != Some(binding["generation"].clone()) {
        return Err("source app is not the selected generation".into());
    }
    let (package, package_challenge, _) =
        signed_view(root, workspace, &refs["package"], "resource")?;
    let (task, task_challenge, _) = signed_view(root, workspace, &refs["task"], "resource")?;
    let read = rendered_document(root, workspace, member(binding, "document")?, None, None)?;
    let challenge = read.challenge.clone();
    let seen = seen_read_value(member(binding, "document")?, &read, &challenge);
    // Refuse an unsupported document before making the physical app request.
    let _ = pull_text(&seen)?;
    make_private_dir(&dir)?;
    let _lock = crate::transport::service_lock(&dir.join("operation.lock"))?;
    // Signed reads do not reserve the operation directory. A concurrent rebase
    // may have claimed it meanwhile: do not make a second physical request.
    if let Some(retained) = occupied_capture(root, workspace, binding, id)? {
        return Ok(retained);
    }
    let nonce = crate::fsio::random::<16>()?;
    let capture = hex(&nonce);
    // The fetch is an external effect: retain that it STARTED (naming the send) before any byte
    // leaves. From here, anything short of the retained export leaves it UNKNOWN, never repeated.
    let fetch_record = fetch_delivery(&dir, fetch_binding(binding, &refs["document"]["target"], id))?;
    store::atomic_json(&dir.join("fetch.json"), &fetch_record.start(json!({"capture":capture}), unix_seconds())?)?;
    let (headers, body) = fetch(&dir, binding, &capture)?;
    let receipt = checked_receipt(&headers, &body, binding, &capture)?;
    let _ = std::str::from_utf8(&body).map_err(|_| "sheet export is not UTF-8")?;
    if body.contains(&0) {
        return Err("sheet export contains NUL bytes".into());
    }
    let v = json!({"type":"mini-app-document-capture-v1","binding":binding,"refs":refs,"seen":seen,
        "appObservation":app,"appChallenge":app_challenge,"packageObservation":package,"packageChallenge":package_challenge,"taskObservation":task,"taskChallenge":task_challenge,
        "body":hex(&body),"receipt":receipt});
    seal(root, workspace, id, &v)?;
    // The retained export is the evidence; the completion marker follows it. A cut between the two
    // leaves a `started` marker beside a retained export, which `status` reads as captured (it reads
    // the export, not the marker).
    let started = fetch_delivery(&dir, fetch_binding(binding, &refs["document"]["target"], id))?;
    store::atomic_json(&dir.join("fetch.json"), &started.complete(json!({"bodySha256":receipt["bodySha256"],
        "operation":receipt["operation"],"transaction":receipt["transaction"],"event":receipt["event"]}), unix_seconds())?)?;
    status(root, workspace, id)
}

fn draft(v: &Value) -> Result<Vec<u8>> {
    let mut text = pull_text(&v["seen"])?;
    let b = &v["binding"];
    let r = &v["receipt"];
    text.extend(format!("\nSheet {} · app {} generation {} · exported by {}\nExport {} · operation {} · receipt {}\n",
        member(b,"sheet")?,member(b,"app")?,member(b,"generation")?,member(b,"subject")?,
        member(r,"bodySha256")?,member(r,"operation")?,member(r,"transaction")?).as_bytes());
    text.extend(mini_sdk::hex::decode(member(v, "body")?).map_err(|e| e.0)?);
    if !text.ends_with(b"\n") {
        text.push(b'\n');
    }
    Ok(text)
}
fn typed_refusal(decision: Option<crate::HostDecision>) -> Option<Value> {
    let value = match decision? {
        crate::HostDecision::Outcome(v) => v,
        crate::HostDecision::Frame {
            decoded: Some(v), ..
        } => v,
        _ => return None,
    };
    (value["type"] == "refused").then_some(value)
}
pub(crate) fn publish(root: &Path, workspace: &Value, id: &str) -> Result<Value> {
    let dir = operation(root, id)?;
    private_dir(&dir)?;
    let _lock = crate::transport::service_lock(&dir.join("operation.lock"))?;
    let v = opened(root, workspace, id)?;
    validate(&v["binding"], workspace)?;
    if stable_refs(&read_refs(root, &v["binding"])?) != stable_refs(&v["refs"]) {
        return Err("connector references changed; retained export cannot redirect".into());
    }
    if dir.join("submit-started.json").exists() {
        return status(root, workspace, id);
    }
    let plan = push_actions(&v["seen"], &draft(&v)?)?;
    let proposal = format!("app-{id}");
    validate_name(&proposal)?;
    let attempt = root.join("attempts").join(&proposal);
    save(
        &dir.join("submit-started.json"),
        &json!({"attempt":attempt,"proposal":proposal}),
    )?;
    let request = json!({"type":"minidregg-workspace-proposal-v1","action":"invoke","targets":[{
        "name":v["binding"]["document"],"payload":{"type":"content","actions":plan.actions}}]});
    crate::take_host_decision();
    let result =
        propose_request(root, workspace, &request, &proposal, None, false).and_then(|_| {
            submit_intent(
                root,
                workspace,
                &root.join("proposals").join(&proposal).join("intent.json"),
                "intent",
                false,
                Some(&attempt),
            )
        });
    if let Err(error) = result {
        let refusal = typed_refusal(crate::take_host_decision());
        save(
            &dir.join("result.json"),
            &json!({"status":if refusal.is_some(){"refused"}else if !attempt.join("call.bin").exists(){"failed"}else{"uncertain"},"message":error,"refusal":refusal}),
        )?;
    }
    status(root, workspace, id)
}
pub(crate) fn status(root: &Path, workspace: &Value, id: &str) -> Result<Value> {
    let dir = operation(root, id)?;
    private_dir(&dir)?;
    if !dir.join("capture.enc").exists() {
        let record = store::read_json(&dir.join("fetch.json"))?.ok_or("no export is retained for this operation")?;
        if record["binding"]["subject"] != workspace["subject"] {
            return Err("export belongs to another participant".into());
        }
        return match Delivery::open(record["binding"].clone(), Some(record.clone()))?.state() {
            DeliveryState::Unknown => Ok(
                json!({"type":"mini-app-document-result-v1","id":id,"status":"source-uncertain","capture":record,
                "message":"No complete export is retained. This operation cannot fetch again."})),
            DeliveryState::Completed(_) => Err("the fetch completed but its retained export is missing; restore the complete workspace custody".into()),
            // This fetch never records a destination refusal; a record that says so is not its.
            DeliveryState::Fresh | DeliveryState::Refused { .. } => Err("no export is retained for this operation".into()),
        };
    }
    let v = opened(root, workspace, id)?;
    let mut state = json!({"type":"mini-app-document-result-v1","id":id,"subject":v["binding"]["subject"],
        "status":"captured","document":v["binding"]["document"],"target":v["refs"]["document"]["target"],"receipt":v["receipt"],"custody":dir});
    if dir.join("submit-started.json").exists() {
        let start = bounded_json(&dir.join("submit-started.json"))?;
        let attempt = member_path(&start, "attempt")?;
        state["attempt"] = json!(attempt);
        state["status"] = json!("uncertain");
        if dir.join("result.json").exists() {
            let result = bounded_json(&dir.join("result.json"))?;
            state["status"] = result["status"].clone();
            state["message"] = result["message"].clone();
        }
        if attempt.exists() {
            match retained_attempt_outcome(&attempt)? {
                AttemptOutcome::Confirmed(_) => {
                    let out = accepted_outcome(&attempt)?.ok_or("confirmed attempt lost its retained outcome")?;
                    state["outcome"] = out;
                    state["status"] = json!("saved");
                }
                AttemptOutcome::Charged(value) => {
                    state["outcome"] = value;
                    state["status"] = json!("charged");
                }
                AttemptOutcome::Refused => state["status"] = json!("refused"),
                AttemptOutcome::Pending if attempt.join("call.bin").exists() => {
                    // A newer undecided reply supersedes any earlier refusal.
                    // The exact call remains held, so no fresh write is safe.
                    state["status"] = json!("uncertain");
                }
                AttemptOutcome::Pending => {},
            }
        }
    }
    Ok(state)
}

pub(crate) fn member_status(root: &Path, id: &str) -> Result<Value> {
    status(root, &load(root)?, id)
}
pub(crate) fn recover_exact(root: &Path, workspace: &Value, id: &str) -> Result<Value> {
    let dir = operation(root, id)?;
    private_dir(&dir)?;
    let _lock = crate::transport::service_lock(&dir.join("operation.lock"))?;
    let current = status(root, workspace, id)?;
    if current["status"] != "uncertain" {
        return Ok(current);
    }
    let start = bounded_json(&dir.join("submit-started.json"))?;
    let attempt = member_path(&start, "attempt")?;
    match fs::symlink_metadata(attempt.join("call.bin")) {
        Ok(_) => {
            let _ = recover(root, &attempt);
        }
        Err(e) if e.kind() == std::io::ErrorKind::NotFound => save(
            &dir.join("result.json"),
            &json!({"status":"failed","message":"Writer stopped before the call. Nothing submitted; export remains retained."}),
        )?,
        Err(e) => return Err(e.to_string()),
    }
    status(root, workspace, id)
}

/// An explicit repair after a proven no-effect outcome. Keep the original
/// app bytes/receipt; only the destination editing base is refreshed. Each
/// refused operation claims one successor before constructing it.
pub(crate) fn rebase(root: &Path, workspace: &Value, id: &str, next: &str) -> Result<Value> {
    validate_name(next)?;
    publishable_id(next)?;
    if id == next {
        return Err("rebase requires a fresh connector identity".into());
    }
    let dir = operation(root, id)?;
    let _lock = crate::transport::service_lock(&dir.join("operation.lock"))?;
    let current = status(root, workspace, id)?;
    if !matches!(current["status"].as_str(), Some("failed" | "refused")) {
        return Err(
            "only a definitively unsubmitted or refused document write can refresh its base".into(),
        );
    }
    let nextdir = operation(root, next)?;
    let claim = dir.join("rebase.json");
    if claim.exists() {
        if bounded_json(&claim)?["next"] != next {
            return Err("this export already claimed another successor".into());
        }
    } else {
        if nextdir.exists() {
            return Err("new successor identity is already occupied".into());
        }
        save(&claim, &json!({"next":next,"subject":workspace["subject"]}))?;
    }
    if nextdir.join("capture.enc").exists() && opened(root, workspace, next)?["rebasedFrom"] != id {
        return Err("successor belongs to another retained export".into());
    }
    if !nextdir.exists() {
        make_private_dir(&nextdir)?;
    }
    private_dir(&nextdir)?;
    let _next_lock = crate::transport::service_lock(&nextdir.join("operation.lock"))?;
    if nextdir.join("capture.enc").exists() {
        let prior = opened(root, workspace, next)?;
        if prior["rebasedFrom"] != id {
            return Err("successor belongs to another retained export".into());
        }
        return status(root, workspace, next);
    }
    if nextdir.join("fetch.json").exists() {
        return Err("successor is already an original source capture; no replacement".into());
    }
    let mut v = opened(root, workspace, id)?;
    if stable_refs(&read_refs(root, &v["binding"])?) != stable_refs(&v["refs"]) {
        return Err("connector references changed; rebase cannot redirect retained bytes".into());
    }
    let name = member(&v["binding"], "document")?;
    let read = rendered_document(root, workspace, name, None, None)?;
    let challenge = read.challenge.clone();
    v["seen"] = seen_read_value(name, &read, &challenge);
    v["rebasedFrom"] = json!(id);
    let _ = push_actions(&v["seen"], &draft(&v)?)?;
    if !nextdir.exists() {
        make_private_dir(&nextdir)?;
    }
    private_dir(&nextdir)?;
    seal(root, workspace, next, &v)?;
    status(root, workspace, next)
}

fn finish_result(op: &str, result: &Value) -> Result<()> {
    print_json(result)?;
    if op == "status" { return Ok(()); }
    let ending = match result["status"].as_str() {
        Some("refused") => crate::CommandEnding::Refused("retained document write was refused; export bytes remain held for an explicit rebase".into()),
        Some("uncertain") => crate::CommandEnding::Undecided("exact document call remains undecided; recover this operation without replacing its export".into()),
        Some("source-uncertain") => crate::CommandEnding::Undecided("source export remains uncertain; this operation cannot fetch again".into()),
        Some("failed") => crate::CommandEnding::Client("document writer failed before submitting a call; export bytes remain held for an explicit rebase".into()),
        _ => return Ok(()),
    };
    let (_, message) = ending.render();
    crate::note_command_ending(ending);
    Err(message.trim_end().to_owned())
}

pub(crate) fn run(root: &Path, workspace: &Value, mut args: Args) -> Result<()> {
    let op = os_string(args.required("op")?, "connector operation")?;
    let id = os_string(args.required("id")?, "connector identity")?;
    // The nested proposal/submit calls print their own native outcome; this command's one stdout document is the
    // operation result below (a caller parses exactly one JSON object).
    let quiet = super::app_lifecycle::QuietReplies(crate::QUIET_WORKER.swap(true, std::sync::atomic::Ordering::Relaxed));
    let result = match op.as_str() {
        "capture" => {
            let binding = bounded_json(&path(args.required("binding")?))?;
            args.finish()?;
            capture(root, workspace, &binding, &id)?
        }
        "publish" => {
            args.finish()?;
            publish(root, workspace, &id)?
        }
        "status" => {
            args.finish()?;
            status(root, workspace, &id)?
        }
        "recover" => {
            args.finish()?;
            recover_exact(root, workspace, &id)?
        }
        "rebase" => {
            let next = os_string(args.required("next")?, "new connector identity")?;
            args.finish()?;
            rebase(root, workspace, &id, &next)?
        }
        _ => return Err("connector op is capture, publish, status, recover or rebase".into()),
    };
    drop(quiet);
    finish_result(&op, &result)
}

#[cfg(test)]
mod tests {
    use super::*;

    const ENTRANCE_CERT: &[u8] = include_bytes!("../../spk-host/tests/fixtures/browser-proxy-test.crt");
    const ENTRANCE_KEY: &[u8] = include_bytes!("../../spk-host/tests/fixtures/browser-proxy-test.key");

    /// A one-shot TLS server shaped like the browser entrance: TLS 1.3, X25519MLKEM768 only.
    fn hybrid_only_entrance(reply: &'static [u8]) -> (u16, std::thread::JoinHandle<Vec<u8>>) {
        use std::io::{Read, Write};
        let certs: Vec<_> = rustls_pemfile::certs(&mut std::io::Cursor::new(ENTRANCE_CERT)).collect::<std::io::Result<_>>().unwrap();
        let key = rustls_pemfile::private_key(&mut std::io::Cursor::new(ENTRANCE_KEY)).unwrap().unwrap();
        let mut crypto = rustls::crypto::aws_lc_rs::default_provider();
        crypto.kx_groups = vec![rustls::crypto::aws_lc_rs::kx_group::X25519MLKEM768];
        let config = rustls::ServerConfig::builder_with_provider(std::sync::Arc::new(crypto))
            .with_protocol_versions(&[&rustls::version::TLS13]).unwrap()
            .with_no_client_auth().with_single_cert(certs, key).unwrap();
        let listener = std::net::TcpListener::bind("127.0.0.1:0").unwrap();
        let port = listener.local_addr().unwrap().port();
        let server = std::thread::spawn(move || {
            let (tcp, _) = listener.accept().unwrap();
            let conn = rustls::ServerConnection::new(std::sync::Arc::new(config)).unwrap();
            let mut tls = rustls::StreamOwned::new(conn, tcp);
            let mut request = Vec::new();
            let mut byte = [0u8; 1];
            while !request.ends_with(b"\r\n\r\n") {
                tls.read_exact(&mut byte).unwrap();
                request.push(byte[0]);
            }
            tls.write_all(reply).unwrap();
            tls.conn.send_close_notify();
            tls.flush().unwrap();
            request
        });
        (port, server)
    }

    fn entrance_ca(name: &str) -> PathBuf {
        let path = std::env::temp_dir().join(format!("mini-export-ca-{name}-{}.pem", std::process::id()));
        fs::write(&path, ENTRANCE_CERT).unwrap();
        path
    }

    #[test]
    fn the_export_speaks_the_hybrid_entrance_and_decodes_a_chunked_body() {
        let (port, server) = hybrid_only_entrance(b"HTTP/1.1 200 OK\r\nTransfer-Encoding: chunked\r\nX-Mini-Export-Receipt: 00\r\n\r\n3\r\nabc\r\n2\r\nde\r\n0\r\n\r\n");
        let ca = entrance_ca("chunked");
        let target = ExportTarget::parse(&format!("https://localhost:{port}/_/survey/csv")).unwrap();
        let raw = export_exchange(&target, Some(ca.to_str().unwrap()), b"GET /_/survey/csv HTTP/1.1\r\nHost: localhost\r\nX-Mini-Export-Capture: c1\r\nConnection: close\r\n\r\n", Instant::now() + Duration::from_secs(20)).unwrap();
        let (head, body) = split_export_response(&raw).unwrap();
        assert!(head.starts_with(b"HTTP/1.1 200 ") && head.ends_with(b"\r\n\r\n"));
        assert_eq!(body, b"abcde");
        assert!(String::from_utf8(server.join().unwrap()).unwrap().contains("X-Mini-Export-Capture: c1\r\n"));
        fs::remove_file(ca).unwrap();
    }

    #[test]
    fn an_export_refused_by_status_names_it_and_a_short_body_is_incomplete() {
        let (port, server) = hybrid_only_entrance(b"HTTP/1.1 403 Forbidden\r\nContent-Length: 0\r\n\r\n");
        let ca = entrance_ca("refused");
        let target = ExportTarget::parse(&format!("https://localhost:{port}/x")).unwrap();
        let refused = export_exchange(&target, Some(ca.to_str().unwrap()), b"GET /x HTTP/1.1\r\nHost: localhost\r\n\r\n", Instant::now() + Duration::from_secs(20)).unwrap_err();
        assert_eq!(refused, "http=403");
        server.join().unwrap();
        fs::remove_file(ca).unwrap();
        assert!(split_export_response(b"HTTP/1.1 200 OK\r\nContent-Length: 5\r\n\r\nabc").is_err());
        assert!(split_export_response(b"HTTP/1.1 200 OK\r\nTransfer-Encoding: chunked\r\n\r\n5\r\nab").is_err());
        assert_eq!(split_export_response(b"HTTP/1.1 200 OK\r\nContent-Length: 3\r\n\r\nabc").unwrap().1, b"abc");
        // A peer-chosen chunk size near usize::MAX is refused, never an overflow or a panic.
        assert!(split_export_response(b"HTTP/1.1 200 OK\r\nTransfer-Encoding: chunked\r\n\r\nffffffffffffffff\r\nab\r\n0\r\n\r\n").is_err());
        // The terminal chunk without its trailer section's blank line is incomplete.
        assert!(split_export_response(b"HTTP/1.1 200 OK\r\nTransfer-Encoding: chunked\r\n\r\n2\r\nab\r\n0\r\n").is_err());
        assert!(split_export_response(b"HTTP/1.1 200 OK\r\nTransfer-Encoding: gzip, chunked\r\n\r\n0\r\n\r\n").is_err());
    }

    #[test]
    fn export_endpoints_are_https_and_localhost_names_are_loopback() {
        assert!(ExportTarget::parse("http://app.example/").is_err());
        assert!(ExportTarget::parse("https://user@app.example/").is_err());
        let t = ExportTarget::parse("https://connector.jw22943.localhost:22943/_/jd3/csv").unwrap();
        assert_eq!((t.host.as_str(), t.port, t.path.as_str()), ("connector.jw22943.localhost", 22943, "/_/jd3/csv"));
        assert_eq!(t.addresses().unwrap(), vec![std::net::SocketAddr::from(([127, 0, 0, 1], 22943))]);
        assert_eq!(ExportTarget::parse("https://app.example/").unwrap().port, 443);
    }
    fn binding() -> Value {
        json!({"type":"mini-app-document-binding-v1","subject":"8","appReference":"sheet","packageReference":"package","packageManifest":"11","sessionKind":"api","credentialKind":"bearer","app":"7","generation":"3","session":"9","sessionGeneration":"2","ticket":"10","document":"paper","documentCapability":"11","taskReference":"job","task":"12","sheet":"survey","endpoint":"https://app.example/","apiPath":"/_/","token":"a".repeat(32),"ca":null})
    }
    fn receipt() -> Value {
        json!({"type":"mini-spk-export-custody-v1","capture":"a".repeat(32),"method":"GET","signedApiPath":"/_/","path":"_/survey/csv","query":"","bodyBytes":"3","bodySha256":format!("{:x}",Sha256::digest(b"abc")),"app":"7","generation":"3","subject":"8","sessionKind":"api","credentialKind":"bearer","packageManifest":"11","session":"9","sessionGeneration":"2","ticket":"10","operation":"17","transaction":"18","event":"19","requestDigest":"20","permitSha256":"b".repeat(64)})
    }
    fn headers(r: &Value) -> Vec<u8> {
        format!(
            "HTTP/1.1 200 OK\r\nX-Mini-Export-Receipt: {}\r\n\r\n",
            hex(&serde_json::to_vec(r).unwrap())
        )
        .into_bytes()
    }
    #[test]
    fn effect_endings_are_typed_but_status_is_successful() {
        for (state, code) in [("refused", 3), ("uncertain", 4), ("source-uncertain", 4), ("failed", 1)] {
            let value = json!({"type":"mini-app-document-result-v1","status":state});
            let _ = crate::take_command_ending();
            assert!(finish_result("publish", &value).is_err());
            assert_eq!(crate::take_command_ending().unwrap().render().0, code);
            assert!(finish_result("status", &value).is_ok());
            assert!(crate::take_command_ending().is_none());
        }
        assert!(finish_result("publish", &json!({"status":"saved"})).is_ok());
        assert!(crate::take_command_ending().is_none());
    }
    #[test]
    fn status_uses_latest_retry_instead_of_original_refusal() {
        for (initial, newest, expected) in [("uncertain", "refused", "refused"), ("refused", "uncertain", "uncertain"), ("refused", "unavailable", "uncertain")] {
            let root = std::env::temp_dir().join(format!("app-doc-retry-status-{}", random_nonce().unwrap()));
            make_private_dir(&root).unwrap();
            let ws = json!({"subject":"8"});
            store_key(&root).unwrap();
            let dir = operation(&root, "export").unwrap();
            make_private_dir(&dir).unwrap();
            seal(&root, &ws, "export", &json!({"binding":binding(),"body":"616263","receipt":receipt(),"refs":{"document":{"target":"22"}}})).unwrap();
            let attempt = root.join("write");
            make_private_dir(&attempt).unwrap();
            create_private(&attempt.join("call.bin"), b"exact retained call").unwrap();
            save(&dir.join("submit-started.json"), &json!({"attempt":attempt,"proposal":"app-export"})).unwrap();
            save(&dir.join("result.json"), &json!({"status":if initial == "refused" {"refused"} else {"uncertain"},"message":"retained original result"})).unwrap();
            save(&attempt.join("outcome.json"), &json!({"type":initial})).unwrap();
            save(&attempt.join("retry-0001.json"), &json!({"type":newest})).unwrap();
            assert_eq!(status(&root, &ws, "export").unwrap()["status"], expected);
            std::fs::remove_dir_all(root).unwrap();
        }
    }
    #[test]
    fn unpublishable_id_refuses_before_export_custody() {
        let root = std::env::temp_dir().join(format!("app-doc-long-id-{}", random_nonce().unwrap()));
        make_private_dir(&root).unwrap();
        let error = capture(&root, &json!({"subject":"8"}), &binding(), &"a".repeat(61)).unwrap_err();
        assert!(error.contains("1..60"));
        assert!(!root.join("app-documents").exists());
        let error = rebase(&root, &json!({"subject":"8"}), "old", &"a".repeat(61)).unwrap_err();
        assert!(error.contains("1..60"));
        assert!(!root.join("app-documents").exists());
        std::fs::remove_dir(&root).unwrap();
    }
    #[test]
    fn occupied_rebase_successor_prevents_any_new_physical_capture() {
        let root = std::env::temp_dir().join(format!("app-doc-race-{}", random_nonce().unwrap()));
        make_private_dir(&root).unwrap();
        let ws = json!({"subject":"8"});
        store_key(&root).unwrap();
        let dir = operation(&root, "next").unwrap();
        make_private_dir(&dir).unwrap();
        let v = json!({"binding":binding(),"rebasedFrom":"old","body":"616263","receipt":receipt(),"refs":{"document":{"target":"22"}}});
        seal(&root, &ws, "next", &v).unwrap();
        assert!(occupied_capture(&root, &ws, &binding(), "next")
            .unwrap()
            .is_some());
        let mut wrong = binding();
        wrong["document"] = json!("other");
        assert!(occupied_capture(&root, &ws, &wrong, "next").is_err());
        assert!(!dir.join("fetch.json").exists());
        fs::remove_dir_all(root).unwrap();
    }
    #[test]
    fn a_started_fetch_without_an_export_is_source_uncertain_and_is_never_repeated() {
        let root = std::env::temp_dir().join(format!("app-doc-unknown-{}", random_nonce().unwrap()));
        make_private_dir(&root).unwrap();
        let ws = json!({"subject":"8"});
        store_key(&root).unwrap();
        let dir = operation(&root, "one").unwrap();
        make_private_dir(&dir).unwrap();
        let fetch = fetch_delivery(&dir, fetch_binding(&binding(), &json!("22"), "one")).unwrap();
        assert_eq!(fetch.state(), DeliveryState::Fresh);
        store::atomic_json(&dir.join("fetch.json"), &fetch.start(json!({"capture":"ab"}), 5).unwrap()).unwrap();
        // The crash happened mid-fetch: the operation is occupied, reports UNKNOWN, names the send.
        let held = occupied_capture(&root, &ws, &binding(), "one").unwrap().expect("a started fetch occupies the operation");
        assert_eq!(held["status"], "source-uncertain");
        assert_eq!(held["capture"]["request"], json!({"capture":"ab"}));
        // Another participant's workspace never reads it.
        assert!(status(&root, &json!({"subject":"9"}), "one").is_err());
        // The Delivery discipline itself refuses a second start.
        let again = fetch_delivery(&dir, fetch_binding(&binding(), &json!("22"), "one")).unwrap();
        assert_eq!(again.state(), DeliveryState::Unknown);
        assert!(again.start(json!({"capture":"cd"}), 6).unwrap_err().0.contains("UNKNOWN"));
        // A fetch bound to a different source or destination refuses to open this record.
        assert!(fetch_delivery(&dir, fetch_binding(&binding(), &json!("23"), "one")).is_err());
        fs::remove_dir_all(root).unwrap();
    }
    #[test]
    fn a_completed_fetch_beside_a_missing_export_is_a_refusal_not_a_refetch() {
        let root = std::env::temp_dir().join(format!("app-doc-lost-{}", random_nonce().unwrap()));
        make_private_dir(&root).unwrap();
        let ws = json!({"subject":"8"});
        store_key(&root).unwrap();
        let dir = operation(&root, "one").unwrap();
        make_private_dir(&dir).unwrap();
        let fetch = fetch_delivery(&dir, fetch_binding(&binding(), &json!("22"), "one")).unwrap();
        store::atomic_json(&dir.join("fetch.json"), &fetch.start(json!({"capture":"ab"}), 5).unwrap()).unwrap();
        let started = fetch_delivery(&dir, fetch_binding(&binding(), &json!("22"), "one")).unwrap();
        store::atomic_json(&dir.join("fetch.json"), &started.complete(json!({"bodySha256":"x"}), 6).unwrap()).unwrap();
        let error = status(&root, &ws, "one").unwrap_err();
        assert!(error.contains("restore the complete workspace custody"), "{error}");
        fs::remove_dir_all(root).unwrap();
    }
    #[test]
    fn shared_discovery_head_changes_preserve_exact_grants_but_redirects_refuse() {
        let before = json!({"document":{"target":"7","kind":"object","observeCapability":"8","operationCapability":"9","sealedIn":"private-room","sharedName":{"height":"10","worldRoot":"11"}}});
        let mut after = before.clone();
        after["document"]["sharedName"] = json!({"height":"12","worldRoot":"13"});
        assert_eq!(stable_refs(&before), stable_refs(&after));
        for field in [
            "target",
            "kind",
            "observeCapability",
            "operationCapability",
            "sealedIn",
        ] {
            let mut redirected = after.clone();
            redirected["document"][field] = json!("different");
            assert_ne!(stable_refs(&before), stable_refs(&redirected), "{field}");
        }
    }
    #[test]
    fn interrupted_phase_before_document_call_recovers_without_losing_export() {
        let root = std::env::temp_dir().join(format!("app-doc-cut-{}", random_nonce().unwrap()));
        make_private_dir(&root).unwrap();
        let ws = json!({"subject":"8"});
        store_key(&root).unwrap();
        let dir = operation(&root, "one").unwrap();
        make_private_dir(&dir).unwrap();
        let captured = json!({"binding":binding(),"body":"616263","receipt":receipt(),"refs":{"document":{"target":"22"}}});
        seal(&root, &ws, "one", &captured).unwrap();
        fs::write(dir.join(".write-crash-cut"), b"{partial").unwrap();
        let attempt = root.join("attempts/app-one");
        let marker = json!({"attempt":attempt,"proposal":"app-one"});
        save(&dir.join("submit-started.json"), &marker).unwrap();
        save(&dir.join("submit-started.json"), &marker).unwrap();
        assert!(save(
            &dir.join("submit-started.json"),
            &json!({"attempt":"another"})
        )
        .is_err());
        assert_eq!(status(&root, &ws, "one").unwrap()["status"], "uncertain");
        assert_eq!(
            recover_exact(&root, &ws, "one").unwrap()["status"],
            "failed"
        );
        assert_eq!(opened(&root, &ws, "one").unwrap(), captured);
        assert!(!attempt.join("call.bin").exists());
        fs::remove_dir_all(root).unwrap();
    }
    #[test]
    fn only_exact_typed_refusal_permits_new_document_attempt() {
        assert!(typed_refusal(Some(crate::HostDecision::Outcome(
            json!({"type":"unknown"})
        )))
        .is_none());
        assert!(typed_refusal(Some(crate::HostDecision::Frame {
            command: "call".into(),
            byte: 0,
            encoded: vec![],
            decoded: None
        }))
        .is_none());
        assert!(typed_refusal(Some(crate::HostDecision::Outcome(
            json!({"type":"refused","phase":"admission"})
        )))
        .is_some());
    }
    #[test]
    fn export_receipt_binds_bytes_subject_generation_and_session() {
        let b = binding();
        let r = receipt();
        let id = "a".repeat(32);
        checked_receipt(&headers(&r), b"abc", &b, &id).unwrap();
        for field in [
            "app",
            "packageManifest",
            "sessionKind",
            "credentialKind",
            "generation",
            "subject",
            "session",
            "sessionGeneration",
            "ticket",
            "capture",
            "path",
            "bodySha256",
        ] {
            let mut bad = r.clone();
            bad[field] = json!("21");
            assert!(
                checked_receipt(&headers(&bad), b"abc", &b, &id).is_err(),
                "{field}"
            );
        }
        assert!(checked_receipt(&headers(&r), b"abd", &b, &id).is_err());
        let mut duplicate = headers(&r);
        let extra = format!(
            "X-Mini-Export-Receipt: {}\r\n",
            hex(&serde_json::to_vec(&r).unwrap())
        );
        duplicate.splice(0..0, extra.bytes());
        assert!(checked_receipt(&duplicate, b"abc", &b, &id).is_err());
    }
    #[test]
    fn binding_has_no_operator_or_unbounded_route_escape() {
        let b = binding();
        validate(&b, &json!({"subject":"8"})).unwrap();
        let mut web = b.clone();
        web["sessionKind"] = json!("web");
        web["credentialKind"] = json!("cookie");
        web["apiPath"] = Value::Null;
        validate(&web, &json!({"subject":"8"})).unwrap();
        web["credentialKind"] = json!("bearer");
        assert!(validate(&web, &json!({"subject":"8"})).is_err());
        assert!(validate(&b, &json!({"subject":"9"})).is_err());
        for (field, value) in [
            ("endpoint", "http://127.0.0.1/"),
            ("sheet", "../owner"),
            ("token", "short"),
        ] {
            let mut bad = b.clone();
            bad[field] = json!(value);
            assert!(validate(&bad, &json!({"subject":"8"})).is_err());
        }
        let mut extra = b;
        extra["operatorKey"] = json!("secret");
        assert!(validate(&extra, &json!({"subject":"8"})).is_err());
    }
    #[test]
    fn encrypted_capture_binds_subject_operation_and_retains_no_plaintext() {
        let root = std::env::temp_dir().join(format!("app-doc-test-{}", random_nonce().unwrap()));
        make_private_dir(&root).unwrap();
        let ws = json!({"subject":"8"});
        store_key(&root).unwrap();
        make_private_dir(&operation(&root, "one").unwrap()).unwrap();
        let v = json!({"body":"SECRET","binding":binding()});
        seal(&root, &ws, "one", &v).unwrap();
        assert_eq!(opened(&root, &ws, "one").unwrap(), v);
        assert!(opened(&root, &json!({"subject":"9"}), "one").is_err());
        let bytes = fs::read(operation(&root, "one").unwrap().join("capture.enc")).unwrap();
        assert!(!bytes.windows(6).any(|w| w == b"SECRET"));
        make_private_dir(&operation(&root, "two").unwrap()).unwrap();
        fs::write(operation(&root, "two").unwrap().join("capture.enc"), bytes).unwrap();
        assert!(opened(&root, &ws, "two").is_err());
        fs::remove_dir_all(root).unwrap();
    }
}
