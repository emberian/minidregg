//! Authenticated, retained event28 reenrollment after a checked app upgrade.
//! Capture is a participant's pre-quiesce intent. Resume never invents that
//! intent from a closed session and never retransmits an uncertain mutation.
use super::agent_reserve::{bounded, digest, field, private_bytes, private_socket, retain_json};
use super::*;
use mini_sdk::lock::{Create, Lease, LockError, Wait};
use std::os::unix::fs::DirBuilderExt;

const FORMAT: &str = "minidregg-session-reenroll-v1";
const LIMIT: usize = 8 * transport::HOST_MAX_FRAME;

fn read(path: &Path) -> Result<Value> {
    serde_json::from_slice(&private_bytes(path, LIMIT)?).map_err(|e| e.to_string())
}
fn number(value: &Value, name: &str) -> Result<u64> {
    let text = field(value, name)?;
    if text.is_empty()
        || (text.len() > 1 && text.starts_with('0'))
        || !text.bytes().all(|b| b.is_ascii_digit())
    {
        return Err(format!("noncanonical reenrollment {name}"));
    }
    text.parse()
        .map_err(|_| format!("reenrollment {name} exceeds client bound"))
}
fn path_field(value: &Value, name: &str) -> Result<PathBuf> {
    let path = PathBuf::from(field(value, name)?);
    if !path.is_absolute() {
        return Err(format!("reenrollment {name} must be absolute"));
    }
    Ok(path)
}
fn contract(value: &Value) -> Result<()> {
    let object = value
        .as_object()
        .ok_or("reenrollment contract is not an object")?;
    let names = [
        "type",
        "host",
        "config",
        "publicSocket",
        "operatorSocket",
        "priorEnrollment",
        "participantKey",
        "participantPublicKey",
        "inspectorHost",
        "inspectorSha256",
        "signers",
        "app",
        "oldGeneration",
        "session",
        "subject",
        "appObserveCapability",
        "nonce",
    ];
    if object.len() != names.len()
        || names.iter().any(|name| !object.contains_key(*name))
        || field(value, "type")? != FORMAT
    {
        return Err("reenrollment contract fields differ".into());
    }
    for name in [
        "host",
        "config",
        "publicSocket",
        "operatorSocket",
        "priorEnrollment",
        "participantKey",
        "inspectorHost",
    ] {
        path_field(value, name)?;
    }
    for name in [
        "app",
        "oldGeneration",
        "session",
        "subject",
        "appObserveCapability",
        "nonce",
    ] {
        number(value, name)?;
    }
    if number(value, "app")? == number(value, "session")? {
        return Err("reenrollment requires distinct app/session".into());
    }
    number(value, "nonce")?
        .checked_add(100_000)
        .ok_or("reenrollment nonce range overflows")?;
    let signers = value["signers"]
        .as_array()
        .ok_or("reenrollment signers absent")?;
    if signers.is_empty() || signers.len() > 16 {
        return Err("reenrollment signer count invalid".into());
    }
    for (index, signer) in signers.iter().enumerate() {
        if signer.as_object().is_none_or(|o| o.len() != 4) {
            return Err("reenrollment signer fields differ".into());
        }
        number(signer, "keyId")?;
        number(signer, "keyEpoch")?;
        path_field(signer, "keyPath")?;
        field(signer, "publicKey")?;
        if signers[..index]
            .iter()
            .any(|old| old["keyId"] == signer["keyId"] && old["keyEpoch"] == signer["keyEpoch"])
        {
            return Err("duplicate reenrollment signer identity".into());
        }
    }
    Ok(())
}
fn check_keys(value: &Value) -> Result<()> {
    if host_image_sha256(&path_field(value, "inspectorHost")?)? != field(value, "inspectorSha256")?
    {
        return Err("pure source inspector pin changed".into());
    }
    let key = path_field(value, "participantKey")?;
    private_bytes(&key, 32)?;
    if hex(&read_secret(&key)?.verifying_key().to_bytes()) != field(value, "participantPublicKey")?
    {
        return Err("participant key differs from retained identity".into());
    }
    for signer in value["signers"].as_array().ok_or("signers absent")? {
        let key = path_field(signer, "keyPath")?;
        private_bytes(&key, 32)?;
        if hex(&read_secret(&key)?.verifying_key().to_bytes()) != field(signer, "publicKey")? {
            return Err("enrollment signer key differs from retained identity".into());
        }
    }
    Ok(())
}
fn lock(directory: &Path) -> Result<Lease> {
    Lease::acquire(&directory.join("lock"), Create::Yes, Wait::No).map_err(|error| match error {
        LockError::Busy => "reenrollment attempt is already running".to_owned(),
        LockError::Unsafe => "reenrollment lock is not an owner-private single-link regular file".to_owned(),
        LockError::Io(error) => error.to_string(),
    })
}
fn retained_identity(value: &Value, directory: &Path) -> Result<(Value, Value)> {
    let original = read(&directory.join("contract.json"))?;
    let mut identity = value.clone();
    if value.get("newGeneration").is_some() {
        for name in [
            "host",
            "config",
            "inspectorHost",
            "inspectorSha256",
            "publicSocket",
            "operatorSocket",
        ] {
            identity[name] = original[name].clone();
        }
        identity
            .as_object_mut()
            .ok_or("input object absent")?
            .remove("newGeneration");
    }
    if original != identity {
        return Err("retained reenrollment input identity changed".into());
    }
    let pin = read(&directory.join("pin.json"))?;
    if field(&pin, "contractSha256")?
        != digest(&private_bytes(&directory.join("contract.json"), LIMIT)?)
        || field(&pin, "configSha256")?
            != digest(&private_bytes(&directory.join("config.json"), 65_536)?)
    {
        return Err("reenrollment Host/config/input pin changed".into());
    }
    Ok((original, pin))
}
/// The source bytes may have been replaced at the same pathname. Only capture
/// reads that live image; resume binds historical pins to a root-authenticated
/// admission, while check_execution independently validates the live target.
enum SourceImage<'a> {
    CaptureLive,
    Admitted(&'a compatible_upgrade_custody::Candidate),
}
fn source_image(original: &Value, pin: &Value, source: SourceImage<'_>) -> Result<()> {
    match source {
        SourceImage::CaptureLive => {
            if field(pin, "hostSha256")? != host_image_sha256(&path_field(original, "host")?)? {
                return Err("capture Host image pin changed".into());
            }
        }
        SourceImage::Admitted(source) => {
            let (host, sha) = compatible_upgrade_custody::image(&source.manifest, "host")
                .map_err(|e| e.to_string())?;
            if path_field(original, "host")? != host
                || field(pin, "hostSha256")? != sha
                || field(pin, "configSha256")? != source.config_sha256
            {
                return Err("compatible admission does not start from captured Host/config".into());
            }
        }
    }
    Ok(())
}
fn pinned(value: &Value, directory: &Path) -> Result<()> {
    let (original, pin) = retained_identity(value, directory)?;
    if value.get("newGeneration").is_none() {
        source_image(&original, &pin, SourceImage::CaptureLive)?;
    }
    let socket = path_field(value, "publicSocket")?;
    if SOCKET.get() != Some(&socket) {
        return Err("--socket differs from retained public socket".into());
    }
    private_socket(&path_field(value, "operatorSocket")?)?;
    if value.get("newGeneration").is_some() {
        check_execution(value, directory)?;
    }
    check_keys(value)
}
/// Resume can use private public-operation transport only when the root
/// admission explicitly binds the topology and the captured public endpoint.
fn management_transport(
    original: &Value,
    management: Option<&Path>,
    public: Option<&Path>,
) -> Result<PathBuf> {
    let management = management.ok_or("compatible admission lacks management socket topology")?;
    let public = public.ok_or("compatible admission lacks public socket topology")?;
    if !compatible_upgrade_custody::canonical(management)
        || !compatible_upgrade_custody::canonical(public)
        || management == public
        || path_field(original, "publicSocket")? != public
    {
        return Err("admitted socket topology differs from captured public ingress".into());
    }
    Ok(management.to_path_buf())
}
fn execution_config(value: &Value, directory: &Path) -> PathBuf {
    directory.join(if value.get("newGeneration").is_some() {
        "execution-config.json"
    } else {
        "config.json"
    })
}
fn check_execution(value: &Value, directory: &Path) -> Result<()> {
    let execution = read(&directory.join("execution.json"))?;
    if field(&execution, "captureSha256")?
        != digest(&private_bytes(&directory.join("capture.json"), LIMIT)?)
    {
        return Err("bound pre-quiesce capture changed".into());
    }
    let admission_path = path_field(&execution, "admissionPath")?;
    let admission = compatible_upgrade_custody::load(&admission_path).map_err(|e| e.to_string())?;
    let (original, pin) = retained_identity(value, directory)?;
    source_image(&original, &pin, SourceImage::Admitted(&admission.source))?;
    let management = management_transport(
        &original,
        admission.management_socket.as_deref(),
        admission.public_socket.as_deref(),
    )?;
    if path_field(value, "publicSocket")? != management
        || path_field(value, "operatorSocket")? != management
        || path_field(&execution, "managementSocket")? != management
        || path_field(&execution, "publicSocket")? != path_field(&original, "publicSocket")?
    {
        return Err("reenrollment execution socket topology changed".into());
    }
    if digest(
        &compatible_upgrade_custody::root_bytes(&admission_path, 4 * 1024 * 1024)
            .map_err(|e| e.to_string())?,
    ) != field(&execution, "admissionSha256")?
    {
        return Err("compatible admission changed after reenrollment binding".into());
    }
    let (host, sha) = compatible_upgrade_custody::image(&admission.target.manifest, "host")
        .map_err(|e| e.to_string())?;
    if path_field(value, "host")? != host
        || field(&execution, "hostSha256")? != sha
        || host_image_sha256(&host)? != sha
        || value["newGeneration"] != execution["newGeneration"]
        || path_field(value, "config")? != admission.target.config_path
        || digest(&private_bytes(&execution_config(value, directory), 65_536)?)
            != admission.target.config_sha256
    {
        return Err("reenrollment target execution pins changed".into());
    }
    Ok(())
}
fn bind_execution(
    original: &Value,
    directory: &Path,
    admission_path: &Path,
    generation: &str,
) -> Result<Value> {
    let admission_path = absolute(admission_path)?;
    let admission = compatible_upgrade_custody::load(&admission_path).map_err(|e| e.to_string())?;
    let (retained, original_pin) = retained_identity(original, directory)?;
    source_image(
        &retained,
        &original_pin,
        SourceImage::Admitted(&admission.source),
    )?;
    let management = management_transport(
        &retained,
        admission.management_socket.as_deref(),
        admission.public_socket.as_deref(),
    )?;
    let (host, sha) = compatible_upgrade_custody::image(&admission.target.manifest, "host")
        .map_err(|e| e.to_string())?;
    if host_image_sha256(&host)? != sha {
        return Err("target Host image digest differs".into());
    }
    let mut value = original.clone();
    value["host"] = json!(utf8_path(&host)?);
    value["config"] = json!(utf8_path(&admission.target.config_path)?);
    value["inspectorHost"] = value["host"].clone();
    value["inspectorSha256"] = json!(sha);
    value["publicSocket"] = json!(utf8_path(&management)?);
    value["operatorSocket"] = value["publicSocket"].clone();
    value["newGeneration"] = json!(generation);
    if number(&value, "newGeneration")? <= number(&value, "oldGeneration")? {
        return Err("target generation must advance captured app generation".into());
    }
    let execution = json!({"type":FORMAT,"admissionPath":utf8_path(&admission_path)?,"admissionSha256":digest(&compatible_upgrade_custody::root_bytes(&admission_path, 4 * 1024 * 1024).map_err(|e| e.to_string())?),"host":value["host"],"hostSha256":sha,"configSha256":admission.target.config_sha256,"newGeneration":generation,"captureSha256":digest(&private_bytes(&directory.join("capture.json"), LIMIT)?),"managementSocket":utf8_path(&management)?,"publicSocket":original["publicSocket"]});
    let pin = directory.join("execution.json");
    let config_path = execution_config(&value, directory);
    let config = bounded(&admission.target.config_path, 65_536)?;
    if pin.exists() {
        if read(&pin)? != execution || private_bytes(&config_path, 65_536)? != config {
            return Err("resume differs from immutably bound upgrade/generation".into());
        }
    } else {
        if config_path.exists() {
            if private_bytes(&config_path, 65_536)? != config {
                return Err("partial target config differs".into());
            }
        } else {
            create_private(&config_path, &config)?;
        }
        retain_json(&pin, &execution)?;
    }
    check_execution(&value, directory)?;
    Ok(value)
}
fn unique(directory: &Path, prefix: &str) -> Result<PathBuf> {
    for index in 0..10_000 {
        let path = directory.join(format!("{prefix}-{index:04}"));
        if !path.exists() && !path.with_extension("json").exists() {
            return Ok(path);
        }
    }
    Err("reenrollment read evidence names exhausted".into())
}
fn query(value: &Value, directory: &Path, target: &str, capability: &str) -> Result<Value> {
    pinned(value, directory)?;
    let target_dir = unique(directory, "read")?;
    let index: u64 = target_dir
        .file_name()
        .and_then(OsStr::to_str)
        .and_then(|s| s.strip_prefix("read-"))
        .ok_or("read index absent")?
        .parse()
        .map_err(|_| "read index invalid")?;
    let nonce = (number(value, "nonce")? + 100 + index).to_string();
    let intent = json!({"subject":value["subject"],"nonce":nonce,"purpose":{"type":"query","kind":"object","target":target,"view":"resource"},"grants":[{"kind":"object","target":target,"capability":capability}]});
    let source = target_dir.with_extension("json");
    retain_json(&source, &intent)?;
    let result = query_retained(
        &path_field(value, "host")?,
        &execution_config(value, directory),
        &source,
        OsStr::new("intent"),
        &path_field(value, "participantKey")?,
        "view-resource",
        &target_dir,
    )?;
    // Generated directories inherit private umask set by the command.
    pinned(value, directory)?;
    Ok(result)
}
fn coordinate(view: &Value, resource: &str, field_number: &str) -> Result<String> {
    let entries = view["cell"]["entries"]
        .as_array()
        .ok_or("authenticated resource view lacks scalar cell")?;
    let matching: Vec<&Value> = entries
        .iter()
        .filter(|entry| {
            entry["key"]["type"] == "object"
                && entry["key"]["field"] == field_number
                && entry["key"]["resource"] == resource
        })
        .collect();
    if matching.len() != 1 {
        return Err("authenticated view lacks exact unique resource field".into());
    }
    Ok(field(matching[0], "value")?.to_owned())
}
fn root(view: &Value) -> Result<&str> {
    field(&view["cell"], "root")
}
fn validate_enrollment(value: &Value, view: &Value, generation: &str) -> Result<Value> {
    let enrollment = view
        .get("enrollment")
        .ok_or("pinned Host must expose source-decoded enrollment bindings")?;
    for name in ["app", "session", "subject"] {
        if enrollment[name] != value[name] {
            return Err(format!("source enrollment {name} differs from intent"));
        }
    }
    if field(enrollment, "appGeneration")? != generation {
        return Err("source enrollment app generation differs from intent".into());
    }
    if enrollment["role"] != view["request"]["role"] {
        return Err("source enrollment role differs from source request".into());
    }
    Ok(enrollment.clone())
}
fn active_snapshot(
    value: &Value,
    app: &Value,
    session: &Value,
    enrollment: &Value,
    generation: &str,
) -> Result<()> {
    let app_id = field(value, "app")?;
    let session_id = field(value, "session")?;
    if coordinate(app, app_id, "0")? != generation || coordinate(app, app_id, "1")? != "4" {
        return Err("app is not serving the exact expected generation".into());
    }
    let status = coordinate(session, session_id, "3")?;
    let expected_status = match field(enrollment, "kind")? {
        "web" => "1",
        "api" => "5",
        _ => return Err("source enrollment kind invalid".into()),
    };
    if coordinate(session, session_id, "0")? != app_id
        || coordinate(session, session_id, "1")? != generation
        || coordinate(session, session_id, "2")? != field(enrollment, "sessionGeneration")?
        || status != expected_status
    {
        return Err("session is not the exact active enrolled generation".into());
    }
    Ok(())
}
fn capture(value: &Value, directory: &Path) -> Result<Value> {
    if directory.join("capture.json").exists() {
        pinned(value, directory)?;
        if field(&read(&directory.join("capture-pin.json"))?, "sha256")?
            != digest(&private_bytes(&directory.join("capture.json"), LIMIT)?)
        {
            return Err("pre-quiesce capture incomplete or changed".into());
        }
        return Ok(json!({"status":"pending","phase":"captured"}));
    }
    if directory.join("capture-started.json").exists() {
        return Err("capture incomplete; retain attempt and select a new explicit intent".into());
    }
    retain_json(
        &directory.join("capture-started.json"),
        &json!({"type":FORMAT}),
    )?;
    let prior = path_field(value, "priorEnrollment")?;
    let anchor = session_enrollment::authenticated_anchor(
        &prior,
        &path_field(value, "host")?,
        &execution_config(value, directory),
        &path_field(value, "operatorSocket")?,
        &path_field(value, "inspectorHost")?,
    )?;
    let enrollment = validate_enrollment(value, &anchor, field(value, "oldGeneration")?)?;
    let app = query(
        value,
        directory,
        field(value, "app")?,
        field(value, "appObserveCapability")?,
    )?;
    let session = query(
        value,
        directory,
        field(value, "session")?,
        field(&anchor["request"], "sessionObserveCapability")?,
    )?;
    active_snapshot(
        value,
        &app,
        &session,
        &enrollment,
        field(value, "oldGeneration")?,
    )?;
    retain_json(
        &directory.join("capture.json"),
        &json!({"type":FORMAT,"prior":anchor,"app":app,"session":session,"enrollment":enrollment}),
    )?;
    retain_json(
        &directory.join("capture-pin.json"),
        &json!({"sha256":digest(&private_bytes(&directory.join("capture.json"), LIMIT)?)}),
    )?;
    Ok(json!({"status":"pending","phase":"captured"}))
}
fn request_from_prior(prior: &Value, nonce: u64) -> Result<Value> {
    let original = &prior["request"];
    let mut request = serde_json::Map::new();
    for name in [
        "issueIndex",
        "ticketResource",
        "packageManifest",
        "descriptorCapability",
        "sessionObserveCapability",
        "descriptorObserveCapability",
        "manifestObserveCapability",
    ] {
        request.insert(
            name.into(),
            Value::String(field(original, name)?.to_owned()),
        );
    }
    let mut role = original["role"].clone();
    let object = role.as_object_mut().ok_or("prior role absent")?;
    for (encoded, plain) in [("addedHex", "added"), ("removedHex", "removed")] {
        let values = object
            .remove(encoded)
            .ok_or("prior role byte list absent")?;
        let decoded = values
            .as_array()
            .ok_or("prior role byte list invalid")?
            .iter()
            .map(|v| {
                let bytes = decode_hex(v.as_str().ok_or("prior permission is not hex")?)?;
                String::from_utf8(bytes).map(Value::String).map_err(|_| {
                    "prior permission is not UTF-8; cannot reauthor losslessly".to_owned()
                })
            })
            .collect::<Result<Vec<_>>>()?;
        object.insert(plain.into(), Value::Array(decoded));
    }
    request.insert("role".into(), role);
    request.insert("nonce".into(), json!(nonce.to_string()));
    Ok(Value::Object(request))
}
fn approval(value: &Value, directory: &Path, plan: &Value) -> Result<Value> {
    let signers = plan["slots"]
        .as_array()
        .ok_or("source enrollment signing slots absent")?
        .iter()
        .map(|slot| {
            let matching = value["signers"]
                .as_array()
                .ok_or("signers absent")?
                .iter()
                .filter(|s| {
                    s["keyId"] == slot["signing"]["keyId"]
                        && s["keyEpoch"] == slot["signing"]["keyEpoch"]
                })
                .collect::<Vec<_>>();
            if matching.len() != 1 {
                return Err("source enrollment requires an unavailable retained signer".into());
            }
            let mut signer = matching[0].clone();
            let obj = signer.as_object_mut().ok_or("signer invalid")?;
            obj.insert("role".into(), slot["role"].clone());
            obj.insert("index".into(), slot["index"].clone());
            obj.insert(
                "headerSha256".into(),
                json!(digest(&decode_hex(field(slot, "headerHex")?)?)),
            );
            Ok(signer)
        })
        .collect::<Result<Vec<_>>>()?;
    Ok(
        json!({"type":"minidregg-session-enrollment-approval-v1","requestSha256":digest(&private_bytes(&directory.join("request.bin"), LIMIT)?),"planSha256":digest(&private_bytes(&directory.join("plan.bin"), LIMIT)?),"planInspectionSha256":digest(&private_bytes(&directory.join("plan-inspected.json"), LIMIT)?),"signers":signers}),
    )
}
fn send_close_once<F>(directory: &Path, call: &[u8], send: F) -> Result<()>
where
    F: FnOnce() -> Result<()>,
{
    if directory.join("submit-marker.json").exists() {
        return Err("close submit already attempted; exact lookup required".into());
    }
    retain_json(
        &directory.join("submit-marker.json"),
        &json!({"callSha256":digest(call)}),
    )?;
    send()
}
fn close_lookup(value: &Value, directory: &Path) -> Result<Value> {
    let close = directory.join("close");
    let call = close.join("call.bin");
    let marker = read(&close.join("submit-marker.json"))?;
    if field(&marker, "callSha256")? != digest(&private_bytes(&call, transport::HOST_MAX_FRAME)?) {
        return Err("retained close call changed".into());
    }
    let output = unique(&close, "lookup")?;
    // The public Host lookup authenticates the exact retained signed call.
    host_files(
        &path_field(value, "host")?,
        &execution_config(value, directory),
        &[Path::new("lookup"), &call, &output],
    )?;
    let result = inspect(
        &path_field(value, "host")?,
        &execution_config(value, directory),
        "outcome",
        &output,
        &output.with_extension("json"),
    )?;
    if field(&result, "type")? != "confirmed" || field(&result, "confirmation")? != "replayed" {
        return Err("close exact lookup did not select accepted original".into());
    }
    Ok(result)
}
fn ensure_closed(value: &Value, directory: &Path, captured: &Value, current: &Value) -> Result<()> {
    let close = directory.join("close");
    if close.join("submit-marker.json").exists() {
        close_lookup(value, directory)?;
        return Ok(());
    }
    if close.exists() {
        return Err("close preparation incomplete; retained attempt requires analysis".into());
    }
    let sid = field(value, "session")?;
    let old = &captured["session"];
    if root(current)? != root(old)? {
        return Err("session changed since pre-quiesce intent; refusing revival".into());
    }
    let generation: u64 = coordinate(old, sid, "2")?
        .parse()
        .map_err(|_| "session generation out of bound")?;
    let next_generation = generation
        .checked_add(1)
        .ok_or("session generation overflow")?;
    let status: u64 = coordinate(old, sid, "3")?
        .parse()
        .map_err(|_| "session status invalid")?;
    if !matches!(status, 1 | 5) {
        return Err("pre-quiesce session was not active".into());
    }
    let capability = field(&captured["enrollment"], "capability")?;
    let observe = field(&captured["prior"]["request"], "sessionObserveCapability")?;
    let nonce = (number(value, "nonce")? + 1).to_string();
    let intent = json!({"subject":value["subject"],"nonce":nonce,"grants":[{"kind":"object","target":sid,"capability":observe}],"purpose":{"type":"prepare","draft":{"type":"invoke","command":{"subject":value["subject"],"nonce":nonce,"targets":[{"kind":"object","target":sid,"capability":capability,"observeCapability":observe,"schemaVersion":"1","expectedTargetRoot":root(current)?,"payload":{"type":"scalar","actions":[{"type":"write","key":{"type":"object","resource":sid,"field":"2"},"expected":generation.to_string(),"value":next_generation.to_string()},{"type":"write","key":{"type":"object","resource":sid,"field":"3"},"expected":status.to_string(),"value":(status+1).to_string()}]}}]}}}});
    let source = directory.join("close-intent.json");
    if source.exists() {
        if read(&source)? != intent {
            return Err("retained close intent differs".into());
        }
    } else {
        retain_json(&source, &intent)?;
    }
    submit(
        &path_field(value, "host")?,
        &execution_config(value, directory),
        &source,
        OsStr::new("intent"),
        &path_field(value, "participantKey")?,
        &close,
        true,
    )?;
    pinned(value, directory)?;
    // Marker is durable before entering the only mutating close operation.
    let _ = send_close_once(
        &close,
        &private_bytes(&close.join("call.bin"), transport::HOST_MAX_FRAME)?,
        || {
            host_files(
                &path_field(value, "host")?,
                &execution_config(value, directory),
                &[
                    Path::new("submit"),
                    &close.join("call.bin"),
                    &close.join("submit.outcome.bin"),
                ],
            )
        },
    );
    close_lookup(value, directory)?;
    Ok(())
}
fn resume(value: &Value, directory: &Path) -> Result<Value> {
    pinned(value, directory)?;
    let captured = read(&directory.join("capture.json"))?;
    if field(&read(&directory.join("capture-pin.json"))?, "sha256")?
        != digest(&private_bytes(&directory.join("capture.json"), LIMIT)?)
    {
        return Err("pre-quiesce capture changed".into());
    }
    let enrollment_dir = directory.join("enrollment");
    let app = query(
        value,
        directory,
        field(value, "app")?,
        field(value, "appObserveCapability")?,
    )?;
    if coordinate(&app, field(value, "app")?, "0")? != field(value, "newGeneration")?
        || coordinate(&app, field(value, "app")?, "1")? != "4"
    {
        return Err("app is not serving expected new generation".into());
    }
    let session = query(
        value,
        directory,
        field(value, "session")?,
        field(&captured["prior"]["request"], "sessionObserveCapability")?,
    )?;
    if !enrollment_dir.join("submit-marker.json").exists() {
        ensure_closed(value, directory, &captured, &session)?;
        let closed = query(
            value,
            directory,
            field(value, "session")?,
            field(&captured["prior"]["request"], "sessionObserveCapability")?,
        )?;
        let sid = field(value, "session")?;
        let old_generation: u64 = coordinate(&captured["session"], sid, "2")?
            .parse()
            .map_err(|_| "session generation invalid")?;
        let old_status: u64 = coordinate(&captured["session"], sid, "3")?
            .parse()
            .map_err(|_| "session status invalid")?;
        if coordinate(&closed, sid, "0")? != field(value, "app")?
            || coordinate(&closed, sid, "1")? != field(value, "oldGeneration")?
            || coordinate(&closed, sid, "2")?
                != old_generation
                    .checked_add(1)
                    .ok_or("session generation overflow")?
                    .to_string()
            || coordinate(&closed, sid, "3")? != (old_status + 1).to_string()
        {
            return Err("session differs from our exact authenticated close".into());
        }

        let request = request_from_prior(&captured["prior"], number(value, "nonce")? + 2)?;
        let source = directory.join("request.json");
        if source.exists() {
            if read(&source)? != request {
                return Err("reenrollment request changed".into());
            }
        } else {
            retain_json(&source, &request)?;
        }
        if !enrollment_dir.exists() {
            session_enrollment::plan(
                &path_field(value, "host")?,
                &execution_config(value, directory),
                &path_field(value, "operatorSocket")?,
                &source,
                &enrollment_dir,
            )?;
        }
        let plan = session_enrollment::inspect_plan_exact(&enrollment_dir)?;
        let bound = validate_enrollment(value, &plan, field(value, "newGeneration")?)?;
        if number(&bound, "sessionGeneration")?
            != number(&captured["enrollment"], "sessionGeneration")?
                .checked_add(2)
                .ok_or("session generation overflow")?
        {
            return Err(
                "source plan does not immediately follow captured session and our close".into(),
            );
        }
        if bound["role"] != captured["enrollment"]["role"]
            || plan["request"]["role"] != captured["prior"]["request"]["role"]
        {
            return Err("reenrollment changed retained participant role".into());
        }
        if !enrollment_dir.join("seal.json").exists() {
            let approval_path = directory.join("approval.json");
            let approved = approval(value, &enrollment_dir, &plan)?;
            if approval_path.exists() {
                if read(&approval_path)? != approved {
                    return Err("retained reenrollment approval changed".into());
                }
            } else {
                retain_json(&approval_path, &approved)?;
            }
            session_enrollment::seal(&enrollment_dir, &approval_path)?;
        }
        pinned(value, directory)?;
        let _ = session_enrollment::submit(&enrollment_dir);
    }
    let accepted = session_enrollment::authenticated_anchor(
        &enrollment_dir,
        &path_field(value, "host")?,
        &execution_config(value, directory),
        &path_field(value, "operatorSocket")?,
        &path_field(value, "inspectorHost")?,
    )?;
    let bound = validate_enrollment(value, &accepted, field(value, "newGeneration")?)?;
    if bound["role"] != captured["enrollment"]["role"] {
        return Err("accepted reenrollment role differs".into());
    }
    let app = query(
        value,
        directory,
        field(value, "app")?,
        field(value, "appObserveCapability")?,
    )?;
    let session = query(
        value,
        directory,
        field(value, "session")?,
        field(&accepted["request"], "sessionObserveCapability")?,
    )?;
    active_snapshot(
        value,
        &app,
        &session,
        &bound,
        field(value, "newGeneration")?,
    )?;
    pinned(value, directory)?;
    Ok(
        json!({"status":"completed","phase":"authenticated-current","receiptPath":utf8_path(&enrollment_dir.join("receipt.json"))?,"enrollment":bound}),
    )
}

fn run_inner(
    phase: &str,
    source: &Path,
    directory: &Path,
    admission: Option<&Path>,
    generation: Option<&str>,
) -> Result<()> {
    if !matches!(phase, "capture" | "resume") {
        return Err("session-reenroll phase must be capture or resume".into());
    }
    let value = read(source)?;
    contract(&value)?;
    let directory = absolute(directory)?;
    // Existing query/submit helpers create child directories; restrict all their
    // retained participant material before they create anything.
    unsafe extern "C" {
        fn umask(mask: u32) -> u32;
    }
    let old_mask = unsafe { umask(0o077) };
    struct Mask(u32);
    impl Drop for Mask {
        fn drop(&mut self) {
            unsafe {
                umask(self.0);
            }
        }
    }
    let _mask = Mask(old_mask);
    if !directory.exists() {
        if phase != "capture" {
            return Err("resume requires captured pre-quiesce intent".into());
        }
        fs::DirBuilder::new()
            .mode(0o700)
            .create(&directory)
            .map_err(|e| e.to_string())?;
    }
    drain::private_dir(&directory)?;
    let _lock = lock(&directory)?;
    if !directory.join("pin.json").exists() {
        if phase != "capture" || directory.join("contract.json").exists() {
            return Err("reenrollment initial pin incomplete".into());
        }
        check_keys(&value)?;
        retain_json(&directory.join("contract.json"), &value)?;
        let config = bounded(&path_field(&value, "config")?, 65_536)?;
        create_private(&directory.join("config.json"), &config)?;
        retain_json(
            &directory.join("pin.json"),
            &json!({"contractSha256":digest(&private_bytes(&directory.join("contract.json"), LIMIT)?),"hostSha256":host_image_sha256(&path_field(&value, "host")?)?,"configSha256":digest(&config)}),
        )?;
    }
    retained_identity(&value, &directory)?;
    let value = match phase {
        "capture" => {
            if admission.is_some() || generation.is_some() {
                return Err("capture does not bind a future execution generation".into());
            }
            value
        }
        _ => bind_execution(
            &value,
            &directory,
            admission.ok_or("resume requires --admission")?,
            generation.ok_or("resume requires --new-generation")?,
        )?,
    };
    pinned(&value, &directory)?;
    let was_quiet = QUIET_WORKER.swap(true, Ordering::Relaxed);
    let result = if phase == "capture" {
        capture(&value, &directory)
    } else {
        resume(&value, &directory)
    };
    QUIET_WORKER.store(was_quiet, Ordering::Relaxed);
    let mut output = match result {
        Ok(output) => output,
        Err(error) => {
            let uncertain = directory.join("close/submit-marker.json").exists()
                || directory.join("enrollment/submit-marker.json").exists();
            json!({"status":if uncertain {"uncertain"} else {"refused"},"phase":phase,"detail":error})
        }
    };
    for name in [
        "app",
        "oldGeneration",
        "newGeneration",
        "session",
        "subject",
    ] {
        output[name] = value[name].clone();
    }
    if output.get("receiptPath").is_none() {
        output["receiptPath"] = Value::Null;
    }
    output["type"] = json!(FORMAT);
    output["attempt"] = json!(utf8_path(&directory)?);
    let verdict = unique(&directory, "verdict")?.with_extension("json");
    retain_json(&verdict, &output)?;
    print_json(&output)
}

pub(super) fn run(
    phase: &str,
    source: &Path,
    directory: &Path,
    admission: Option<&Path>,
    generation: Option<&str>,
) -> Result<()> {
    match run_inner(phase, source, directory, admission, generation) {
        Ok(()) => Ok(()),
        Err(error) => {
            let value = read(source).unwrap_or(Value::Null);
            let uncertain = directory.join("close/submit-marker.json").exists()
                || directory.join("enrollment/submit-marker.json").exists();
            let mut output = json!({"type":FORMAT,"status":if uncertain {"uncertain"} else {"refused"},"phase":phase,"detail":error,"receiptPath":Value::Null,"attempt":directory.to_string_lossy(),"newGeneration":generation});
            for name in ["app", "oldGeneration", "session", "subject"] {
                output[name] = value[name].clone();
            }
            print_json(&output)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn admitted_source_survives_old_image_replacement_or_removal_but_capture_does_not() {
        let stamp = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_nanos();
        let directory = env::temp_dir().join(format!(
            "mini-reenroll-source-{}-{stamp}",
            std::process::id()
        ));
        fs::DirBuilder::new()
            .mode(0o700)
            .create(&directory)
            .unwrap();
        let host = directory.join("current-Host");
        create_private(&host, b"captured image").unwrap();
        let sha = host_image_sha256(&host).unwrap();
        let config_sha = digest(b"captured config");
        let original = json!({"host":host});
        let pin = json!({"hostSha256":sha,"configSha256":config_sha});
        // This seam receives Candidate only after production load() has
        // authenticated root admission. Test the subsequent source-pin rule.
        let mut source = compatible_upgrade_custody::Candidate {
            manifest: json!({"host":host,"sha256":{"host":sha}}),
            config_path: directory.join("old-config"),
            config_sha256: config_sha,
            config: Value::Null,
            profile: Value::Null,
        };
        source_image(&original, &pin, SourceImage::CaptureLive).unwrap();
        source_image(&original, &pin, SourceImage::Admitted(&source)).unwrap();
        fs::write(&host, b"replacement target image").unwrap();
        assert!(source_image(&original, &pin, SourceImage::CaptureLive).is_err());
        source_image(&original, &pin, SourceImage::Admitted(&source)).unwrap();
        fs::remove_file(&host).unwrap();
        assert!(source_image(&original, &pin, SourceImage::CaptureLive).is_err());
        source_image(&original, &pin, SourceImage::Admitted(&source)).unwrap();
        source.manifest["sha256"]["host"] = json!(digest(b"different history"));
        assert!(source_image(&original, &pin, SourceImage::Admitted(&source)).is_err());
        source.manifest["sha256"]["host"] = pin["hostSha256"].clone();
        source.config_sha256 = digest(b"different config");
        assert!(source_image(&original, &pin, SourceImage::Admitted(&source)).is_err());
        fs::remove_dir_all(directory).unwrap();
    }
    #[test]
    fn lock_rejects_symlink_hardlink_and_nonprivate_file() {
        use std::os::unix::fs::{symlink, PermissionsExt};
        let stamp = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_nanos();
        let directory =
            env::temp_dir().join(format!("mini-reenroll-lock-{}-{stamp}", std::process::id()));
        fs::DirBuilder::new()
            .mode(0o700)
            .create(&directory)
            .unwrap();
        let target = directory.join("target");
        create_private(&target, b"retained").unwrap();
        let name = directory.join("lock");
        symlink(&target, &name).unwrap();
        assert!(lock(&directory).is_err());
        fs::remove_file(&name).unwrap();
        fs::hard_link(&target, &name).unwrap();
        assert!(lock(&directory).is_err());
        fs::remove_file(&name).unwrap();
        create_private(&name, b"").unwrap();
        fs::set_permissions(&name, fs::Permissions::from_mode(0o644)).unwrap();
        assert!(lock(&directory).is_err());
        fs::set_permissions(&name, fs::Permissions::from_mode(0o600)).unwrap();
        let held = lock(&directory).unwrap();
        assert!(lock(&directory).is_err());
        drop(held);
        drop(lock(&directory).unwrap());
        assert_eq!(fs::read(&target).unwrap(), b"retained");
        fs::remove_dir_all(directory).unwrap();
    }
    #[test]
    fn management_transport_requires_explicit_exact_admitted_topology() {
        let original = json!({"publicSocket":"/run/mini/public.sock"});
        let public = Path::new("/run/mini/public.sock");
        let management = Path::new("/run/mini/operator.sock");
        assert_eq!(
            management_transport(&original, Some(management), Some(public)).unwrap(),
            management
        );
        assert!(management_transport(&original, None, None).is_err());
        assert!(management_transport(&original, Some(management), None).is_err());
        assert!(management_transport(&original, None, Some(public)).is_err());
        assert!(management_transport(&original, Some(public), Some(public)).is_err());
        assert!(management_transport(
            &original,
            Some(management),
            Some(Path::new("/run/another/public.sock"))
        )
        .is_err());
        assert!(management_transport(
            &original,
            Some(Path::new("/run/mini/../operator.sock")),
            Some(public)
        )
        .is_err());
    }
    #[test]
    fn request_keeps_restrictive_role_exactly() {
        let prior = json!({"request":{"issueIndex":"7","ticketResource":"8","packageManifest":"9","descriptorCapability":"10","sessionObserveCapability":"11","descriptorObserveCapability":"12","manifestObserveCapability":"13","role":{"basis":{"type":"role","id":"1"},"addedHex":["72656164"],"removedHex":["7772697465"],"roleSchemaRoot":"99","roleVersion":"2"}}});
        let request = request_from_prior(&prior, 42).unwrap();
        assert_eq!(request["role"]["basis"], prior["request"]["role"]["basis"]);
        assert_eq!(request["role"]["removed"], json!(["write"]));
        assert_eq!(request["nonce"], "42");
        let mut bad = prior;
        bad["request"]["role"]["addedHex"] = json!(["ff"]);
        assert!(request_from_prior(&bad, 42).is_err());
    }
    #[test]
    fn historical_anchor_must_match_identity_and_generation() {
        let intent = json!({"app":"1","session":"2","subject":"3"});
        let mut view = json!({"enrollment":{"app":"1","session":"2","subject":"3","appGeneration":"4","role":{"basis":"restricted"}},"request":{"role":{"basis":"restricted"}}});
        validate_enrollment(&intent, &view, "4").unwrap();
        for name in ["app", "session", "subject", "appGeneration"] {
            let mut bad = view.clone();
            bad["enrollment"][name] = json!("7");
            assert!(validate_enrollment(&intent, &bad, "4").is_err());
        }
        view["enrollment"]["role"] = json!({"basis":"allAccess"});
        assert!(validate_enrollment(&intent, &view, "4").is_err());
    }
    #[test]
    fn lost_close_response_never_transmits_again() {
        use std::cell::Cell;
        let stamp = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_nanos();
        let directory = env::temp_dir().join(format!(
            "mini-reenroll-close-{}-{stamp}",
            std::process::id()
        ));
        fs::DirBuilder::new()
            .mode(0o700)
            .create(&directory)
            .unwrap();
        let sends = Cell::new(0);
        assert!(send_close_once(&directory, b"exact signed call", || {
            sends.set(sends.get() + 1);
            Err("lost response".into())
        })
        .is_err());
        assert!(send_close_once(&directory, b"exact signed call", || {
            sends.set(sends.get() + 1);
            Ok(())
        })
        .is_err());
        assert!(send_close_once(&directory, b"different call", || {
            sends.set(sends.get() + 1);
            Ok(())
        })
        .is_err());
        assert_eq!(sends.get(), 1);
        assert_eq!(
            field(
                &read(&directory.join("submit-marker.json")).unwrap(),
                "callSha256"
            )
            .unwrap(),
            digest(b"exact signed call")
        );
        fs::remove_dir_all(directory).unwrap();
    }
    fn scalar(resource: &str, values: &[&str]) -> Value {
        json!({"cell":{"root":"123", "entries":values.iter().enumerate().map(|(i,v)| json!({"key":{"type":"object","resource":resource,"field":i.to_string()},"value":v})).collect::<Vec<_>>()}})
    }
    #[test]
    fn pre_quiesce_capture_rejects_closed_revoked_or_other_generations() {
        let intent = json!({"app":"1","session":"2"});
        let enrollment = json!({"sessionGeneration":"7","kind":"web"});
        let app = scalar("1", &["9", "4", "1", "0"]);
        let session = scalar("2", &["1", "9", "7", "1"]);
        active_snapshot(&intent, &app, &session, &enrollment, "9").unwrap();
        for tag in ["0", "2", "3", "4", "6", "7"] {
            assert!(active_snapshot(
                &intent,
                &app,
                &scalar("2", &["1", "9", "7", tag]),
                &enrollment,
                "9"
            )
            .is_err());
        }
        for (field, value) in [(0, "3"), (1, "8"), (2, "8")] {
            let mut changed = session.clone();
            changed["cell"]["entries"][field]["value"] = json!(value);
            assert!(active_snapshot(&intent, &app, &changed, &enrollment, "9").is_err());
        }
        assert!(active_snapshot(
            &intent,
            &scalar("1", &["10", "4", "1", "0"]),
            &session,
            &enrollment,
            "9"
        )
        .is_err());
        assert!(active_snapshot(
            &intent,
            &scalar("1", &["9", "2", "1", "0"]),
            &session,
            &enrollment,
            "9"
        )
        .is_err());
    }
    #[test]
    fn resource_coordinates_reject_duplicates_or_other_resources() {
        let mut view = json!({"cell":{"entries":[{"key":{"type":"object","resource":"1","field":"3"},"value":"1"}]}});
        assert_eq!(coordinate(&view, "1", "3").unwrap(), "1");
        assert!(coordinate(&view, "2", "3").is_err());
        let entry = view["cell"]["entries"][0].clone();
        view["cell"]["entries"].as_array_mut().unwrap().push(entry);
        assert!(coordinate(&view, "1", "3").is_err());
    }
}
