//! A delegated app export is retained once, then written using this
//! participant's ordinary document authority. App response provenance is
//! explicitly host/TLS custody, not a kernel attestation of app state.
use super::*;
use chacha20poly1305::{
    aead::{Aead, Payload},
    ChaCha20Poly1305, KeyInit, Nonce,
};
use std::{
    process::{Command, Stdio},
    time::{Duration, Instant},
};
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
        File::open("/dev/urandom")
            .and_then(|mut f| f.read_exact(&mut *seed))
            .map_err(|e| e.to_string())?;
        replace_private_file(&path, &*seed)?;
    }
    let secret = Zeroizing::new(crate::read_secret(&path)?.to_bytes());
    File::open(&parent)
        .and_then(|f| f.sync_all())
        .map_err(|e| e.to_string())?;
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
    let mut nonce = [0u8; 12];
    File::open("/dev/urandom")
        .and_then(|mut f| f.read_exact(&mut nonce))
        .map_err(|e| e.to_string())?;
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
    File::open(path.parent().ok_or("capture parent absent")?)
        .and_then(|f| f.sync_all())
        .map_err(|e| e.to_string())?;
    Ok(value)
}
/// Immutable phase records are atomically published under their custody lock.
fn save(path: &Path, v: &Value) -> Result<()> {
    if path.exists() {
        if bounded_json(path)? == *v {
            File::open(path.parent().ok_or("phase parent absent")?)
                .and_then(|f| f.sync_all())
                .map_err(|e| e.to_string())?;
            return Ok(());
        }
        return Err("retained connector phase differs; no replacement".into());
    }
    replace_private_file(path, &serde_json::to_vec(v).map_err(|e| e.to_string())?)
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
    let bytes = crate::decode_hex(receipts[0].1.trim())?;
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

/// Exactly one bounded HTTPS fetch. Credential/config reaches curl on stdin,
/// never argv. The export passes through memory into encrypted custody.
fn fetch(dir: &Path, binding: &Value, capture: &str) -> Result<(Vec<u8>, Vec<u8>)> {
    let relative = if binding["apiPath"] == "/_/" {
        format!("{}/csv", member(binding, "sheet")?)
    } else {
        format!("_/{}/csv", member(binding, "sheet")?)
    };
    let url = format!("{}{relative}", member(binding, "endpoint")?);
    let quote = |s: &str| -> Result<String> {
        if s.bytes()
            .any(|b| b.is_ascii_control() || b == b'"' || b == b'\\')
        {
            Err("unsafe curl configuration value".into())
        } else {
            Ok(format!("\"{s}\""))
        }
    };
    let mut config = format!(
        "url = {}\nheader = {}\nheader = {}\n",
        quote(&url)?,
        quote(&if binding["credentialKind"] == "cookie" {
            format!(
                "Cookie: __Host-mini_spk_session={}",
                member(binding, "token")?
            )
        } else {
            format!("Authorization: Bearer {}", member(binding, "token")?)
        })?,
        quote(&format!("X-Mini-Export-Capture: {capture}"))?
    );
    if !binding["ca"].is_null() {
        config.push_str(&format!("cacert = {}\n", quote(member(binding, "ca")?)?));
    }
    let mut child = Command::new("/usr/bin/curl")
        .env_clear()
        .current_dir(dir)
        .args([
            "--disable",
            "--silent",
            "--fail",
            "--http1.1",
            "--request",
            "GET",
            "--proto",
            "=https",
            "--max-redirs",
            "0",
            "--noproxy",
            "*",
            "--proxy",
            "",
            "--connect-timeout",
            "10",
            "--max-time",
            "90",
            "--max-filesize",
            "131072",
            "--header",
            "Accept-Encoding: identity",
        ])
        .arg("--include")
        .args(["--config", "-"])
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::null())
        .spawn()
        .map_err(|e| e.to_string())?;
    let stdout = child.stdout.take().ok_or("export response pipe missing")?;
    let reader = std::thread::spawn(move || {
        let mut bytes = Zeroizing::new(Vec::new());
        stdout
            .take((MAX_EXPORT + 64 * 1024 + 1) as u64)
            .read_to_end(&mut bytes)
            .map_err(|e| e.to_string())?;
        if bytes.len() > MAX_EXPORT + 64 * 1024 {
            return Err("export response exceeds bound".to_owned());
        }
        Ok(bytes)
    });
    if child
        .stdin
        .take()
        .is_none_or(|mut stdin| stdin.write_all(config.as_bytes()).is_err())
    {
        let _ = child.kill();
        let _ = child.wait();
        return Err("export transport could not receive its private configuration".into());
    }
    let started = Instant::now();
    let result = loop {
        if let Some(status) = child.try_wait().map_err(|e| e.to_string())? {
            break status.success();
        }
        if started.elapsed() > Duration::from_secs(91) {
            let _ = child.kill();
            let _ = child.wait();
            break false;
        }
        std::thread::sleep(Duration::from_millis(20));
    };
    let bytes = reader
        .join()
        .map_err(|_| "export response capture stopped")??;
    if !result {
        return Err(
            "export did not complete; retain this exact operation as source-uncertain".into(),
        );
    }
    let end = bytes
        .windows(4)
        .position(|w| w == b"\r\n\r\n")
        .ok_or("export response framing missing")?;
    Ok((bytes[..end + 4].to_vec(), bytes[end + 4..].to_vec()))
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
    if dir.join("fetch-started.json").exists() {
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
    let challenge = bounded_json(&read.attempt.join("challenge.json"))?;
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
    let mut nonce = [0u8; 16];
    File::open("/dev/urandom")
        .and_then(|mut f| f.read_exact(&mut nonce))
        .map_err(|e| e.to_string())?;
    let capture = hex(&nonce);
    save(
        &dir.join("fetch-started.json"),
        &json!({"type":"mini-app-document-fetch-v1","capture":capture,"subject":binding["subject"],"app":binding["app"],"generation":binding["generation"],"document":refs["document"]["target"]}),
    )?;
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
    status(root, workspace, id)
}

fn draft(v: &Value) -> Result<Vec<u8>> {
    let mut text = pull_text(&v["seen"])?;
    let b = &v["binding"];
    let r = &v["receipt"];
    text.extend(format!("\nSheet {} · app {} generation {} · exported by {}\nExport {} · operation {} · receipt {}\n",
        member(b,"sheet")?,member(b,"app")?,member(b,"generation")?,member(b,"subject")?,
        member(r,"bodySha256")?,member(r,"operation")?,member(r,"transaction")?).as_bytes());
    text.extend(crate::decode_hex(member(v, "body")?)?);
    if !text.ends_with(b"\n") {
        text.push(b'\n');
    }
    Ok(text)
}
fn typed_refusal(decision: Option<crate::HostDecision>) -> Option<Value> {
    let value = match decision? {
        crate::HostDecision::Outcome(v) => v,
        crate::HostDecision::RefusedFrame {
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
        let started = bounded_json(&dir.join("fetch-started.json"))?;
        if started["subject"] != workspace["subject"] {
            return Err("export belongs to another participant".into());
        }
        return Ok(
            json!({"type":"mini-app-document-result-v1","id":id,"status":"source-uncertain","capture":started,
            "message":"No complete export is retained. This operation cannot fetch again."}),
        );
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
            &json!({"status":"failed","message":"Writer stopped before the fsynced call. Nothing submitted; export remains retained."}),
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
    if nextdir.join("fetch-started.json").exists() {
        return Err("successor is already an original source capture; no replacement".into());
    }
    let mut v = opened(root, workspace, id)?;
    if stable_refs(&read_refs(root, &v["binding"])?) != stable_refs(&v["refs"]) {
        return Err("connector references changed; rebase cannot redirect retained bytes".into());
    }
    let name = member(&v["binding"], "document")?;
    let read = rendered_document(root, workspace, name, None, None)?;
    let challenge = bounded_json(&read.attempt.join("challenge.json"))?;
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
    finish_result(&op, &result)
}

#[cfg(test)]
mod tests {
    use super::*;
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
        assert!(!dir.join("fetch-started.json").exists());
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
        assert!(typed_refusal(Some(crate::HostDecision::RefusedFrame {
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
