//! Explicit commitment adoption for an existing, uncommitted current key.
//! Lean owns the full KeyRecord, command codec and two distinct signing frames.
//! Rust retains exact source bytes, signs once, and looks up uncertain submissions.
//! Adoption changes only the commitment: the current key, epoch and SSH pin stay put.
use crate::agent_reserve::{bounded, digest, field, private_bytes};
use crate::participant_enrollment::{
    decimal, json_private, key, pair, retain_exact, save_json_staged,
};
use crate::*;
use ed25519_dalek::Signer;

const LIMIT: usize = 256 * 1024;
const FORMAT: &str = "minidregg-key-adoption-attempt-v1";

trait Source {
    fn invoke(&mut self, opcode: u8, payload: &[u8]) -> Result<Vec<u8>>;
    fn inspect_signed(&mut self, kind: &str, bytes: &[u8]) -> Result<Value>;
}
struct Connection {
    host: PathBuf,
    socket: PathBuf,
    config: PathBuf,
    trusted: Option<(PathBuf, Value, Value)>,
}
impl Source for Connection {
    fn invoke(&mut self, opcode: u8, payload: &[u8]) -> Result<Vec<u8>> {
        session_invoke(&self.host, &self.socket, &self.config, opcode, payload)
    }
    fn inspect_signed(&mut self, kind: &str, bytes: &[u8]) -> Result<Value> {
        use receipt_continuity::KeySourceOperation;
        let operation = match kind {
            "subject-key-adoption-plan" => KeySourceOperation::AdoptionPlan,
            "subject-key-adoption-ingress" => KeySourceOperation::AdoptionIngress,
            _ => return Err("unsupported local adoption inspection".into()),
        };
        let (root, workspace, identity) = self
            .trusted
            .as_ref()
            .ok_or("adoption lacks local verifier custody")?;
        let output = receipt_continuity::key_source(root, workspace, identity, operation, bytes)?;
        serde_json::from_slice(&output)
            .map_err(|error| format!("invalid local adoption inspection: {error}"))
    }
}
fn reply(frame: &[u8], opcode: u8) -> Result<Vec<u8>> {
    match frame {
        [actual, body @ ..] if *actual == opcode && !body.is_empty() => Ok(body.to_vec()),
        [254 | 255, ..] => Err(format!(
            "Host refused adopt-next-key op{opcode}; retained attempt is unchanged"
        )),
        _ => Err(format!("invalid adoption op{opcode} response")),
    }
}
fn call(source: &mut impl Source, opcode: u8, payload: &[u8]) -> Result<Vec<u8>> {
    reply(&source.invoke(opcode, payload)?, opcode)
}
fn inspect(source: &mut impl Source, kind: &str, bytes: &[u8]) -> Result<Value> {
    let mut payload = (kind.len() as u16).to_le_bytes().to_vec();
    payload.extend_from_slice(kind.as_bytes());
    payload.extend_from_slice(bytes);
    serde_json::from_slice(&call(source, 8, &payload)?)
        .map_err(|e| format!("invalid adoption inspection: {e}"))
}
fn json_call(source: &mut impl Source, opcode: u8, value: &Value) -> Result<Value> {
    let bytes = serde_json::to_vec(value).map_err(|e| e.to_string())?;
    serde_json::from_slice(&call(source, opcode, &bytes)?).map_err(|e| e.to_string())
}
fn hex_bytes(value: &Value, name: &str, length: Option<usize>) -> Result<Vec<u8>> {
    let text = field(value, name)?;
    if text.is_empty()
        || text.len() > LIMIT * 2
        || text.len() % 2 != 0
        || !mini_sdk::hex::is_lower(text)
    {
        return Err(format!("adoption {name} is not bounded lowercase hex"));
    }
    let bytes = crate::decode_hex(text)?;
    if length.is_some_and(|length| bytes.len() != length) {
        return Err(format!("adoption {name} has the wrong length"));
    }
    Ok(bytes)
}
fn public(value: &Value, name: &str) -> Result<[u8; 32]> {
    hex_bytes(value, name, Some(32))?
        .try_into()
        .map_err(|_| "invalid public key".into())
}
fn status(source: &mut impl Source, subject: &Value, public: &Value) -> Result<Value> {
    json_call(source, 144, &json!({"subject":subject,"publicKey":public}))
}
fn current(view: &Value, subject: &Value) -> Result<()> {
    if view["type"] != "subject-key-status-v1"
        || &view["subject"] != subject
        || view["isCurrent"] != true
        || view["currentRevoked"] != false
    {
        return Err("adoption requires this subject's unrevoked current key".into());
    }
    for name in ["keyId", "keyEpoch"] {
        decimal(field(view, name)?, name)?;
    }
    Ok(())
}
fn check_plan(plan: &Value, request: &Value, initial: &Value, profile: &Value) -> Result<()> {
    if plan["type"] != "subject-key-adoption-plan-v1" {
        return Err("wrong adoption plan type".into());
    }
    for name in ["domain", "semantics"] {
        decimal(field(plan, name)?, name)?;
        if plan[name] != profile[name] {
            return Err(format!("adoption plan changed {name}"));
        }
    }
    let command = &plan["command"];
    if command["subject"] != request["subject"]
        || command["nonce"] != request["nonce"]
        || command["nextPublicKey"] != request["nextPublicKey"]
    {
        return Err("adoption plan changed the requested subject, nonce or next key".into());
    }
    let record = &command["expectedCurrent"];
    for name in [
        "keyId",
        "keyEpoch",
        "algorithm",
        "subject",
        "activeFrom",
        "activeUntil",
    ] {
        decimal(field(record, name)?, name)?;
    }
    if record["keyId"] != initial["keyId"]
        || record["keyEpoch"] != initial["keyEpoch"]
        || record["subject"] != request["subject"]
        || record["publicKey"] != request["currentPublicKey"]
        || record["algorithm"] != "1"
        || record.get("nextKeyDigest") != Some(&Value::Null)
    {
        return Err("adoption plan changed the exact uncommitted current key record".into());
    }
    hex_bytes(plan, "commandBytes", None)?;
    let current = hex_bytes(plan, "currentAuthorizationHeader", None)?;
    let next = hex_bytes(plan, "nextPossessionHeader", None)?;
    if current == next {
        return Err("adoption signing purposes must be distinct".into());
    }
    Ok(())
}
fn check_ingress(view: &Value, plan: &Value, current: &[u8], next: &[u8]) -> Result<()> {
    if view["type"] != "subject-key-adoption-ingress-v1"
        || view["command"] != plan["command"]
        || view["commandBytes"] != plan["commandBytes"]
        || hex_bytes(view, "currentSignature", Some(64))? != current
        || hex_bytes(view, "nextPossessionSignature", Some(64))? != next
    {
        return Err("assembled adoption ingress differs from the signed plan".into());
    }
    Ok(())
}
fn verify_signature(public: &[u8; 32], header: &[u8], signature: &[u8]) -> Result<()> {
    let bytes: [u8; 64] = signature
        .try_into()
        .map_err(|_| "wrong adoption signature length")?;
    ed25519_dalek::VerifyingKey::from_bytes(public)
        .map_err(|e| e.to_string())?
        .verify_strict(header, &ed25519_dalek::Signature::from_bytes(&bytes))
        .map_err(|_| "retained adoption signature does not match the source plan".into())
}
fn stored_call(
    source: &mut impl Source,
    attempt: &Path,
    name: &str,
    opcode: u8,
    payload: &[u8],
) -> Result<Vec<u8>> {
    let path = attempt.join(format!("{name}.frame"));
    let frame = if path.exists() {
        private_bytes(&path, LIMIT)?
    } else {
        let frame = source.invoke(opcode, payload)?;
        retain_exact(&path, &frame)?;
        frame
    };
    let body = reply(&frame, opcode)?;
    retain_exact(&attempt.join(format!("{name}.bin")), &body)?;
    Ok(body)
}
fn seal(
    source: &mut impl Source,
    attempt: &Path,
    pin: &Value,
    daily: &Path,
    next: Option<&Path>,
) -> Result<Vec<u8>> {
    let request = &pin["request"];
    let bytes = serde_json::to_vec(request).map_err(|e| e.to_string())?;
    let plan = stored_call(source, attempt, "plan", 187, &bytes)?;
    let view = source.inspect_signed("subject-key-adoption-plan", &plan)?;
    check_plan(&view, request, &pin["initialStatus"], &pin["profile"])?;
    save_json_staged(&attempt.join("plan.json"), &view)?;
    let current_header = hex_bytes(&view, "currentAuthorizationHeader", None)?;
    let next_header = hex_bytes(&view, "nextPossessionHeader", None)?;
    let current_public = public(request, "currentPublicKey")?;
    let next_public = public(request, "nextPublicKey")?;
    let signing = [
        ("current.sig", daily, current_public, &current_header),
        (
            "next.sig",
            next.unwrap_or(Path::new("")),
            next_public,
            &next_header,
        ),
    ];
    let mut signatures = Vec::new();
    for (name, key_path, public, header) in signing {
        let file = attempt.join(name);
        let signature = if file.exists() {
            private_bytes(&file, 64)?
        } else {
            if attempt.join("submit-marker.json").exists() {
                return Err(
                    "submitted adoption lost a retained signature; refusing to sign again".into(),
                );
            }
            if key_path.as_os_str().is_empty() {
                return Err("--next-key is required to seal this adoption".into());
            }
            let signer = key(key_path)?;
            if signer.verifying_key().to_bytes() != public {
                return Err("adoption signer differs from retained request".into());
            }
            let signature = signer.sign(header).to_bytes().to_vec();
            retain_exact(&file, &signature)?;
            signature
        };
        verify_signature(&public, header, &signature)?;
        signatures.push(signature);
    }
    let ingress = stored_call(
        source,
        attempt,
        "ingress",
        188,
        &pair(&plan, &pair(&signatures[0], &signatures[1])?)?,
    )?;
    let decoded = source.inspect_signed("subject-key-adoption-ingress", &ingress)?;
    check_ingress(&decoded, &view, &signatures[0], &signatures[1])?;
    save_json_staged(&attempt.join("ingress.json"), &decoded)?;
    save_json_staged(
        &attempt.join("sealed.json"),
        &json!({"type":FORMAT,
        "planSha256":digest(&plan),"ingressSha256":digest(&ingress)}),
    )?;
    Ok(ingress)
}
fn same_receipt(left: &Value, right: &Value) -> bool {
    [
        "type",
        "transactionId",
        "eventId",
        "acceptedCount",
        "worldRoot",
    ]
    .iter()
    .all(|name| left.get(name).is_some() && left.get(name) == right.get(name))
}
fn outcome(
    source: &mut impl Source,
    attempt: &Path,
    stem: &str,
    opcode: u8,
    ingress: &[u8],
) -> Result<Value> {
    let bytes = stored_call(source, attempt, stem, opcode, ingress)?;
    let value = inspect(source, "outcome", &bytes)?;
    save_json_staged(&attempt.join(format!("{stem}.json")), &value)?;
    Ok(value)
}
/// The marker precedes the sole submit. Subsequent calls perform lookup only,
/// including after an absent or refused lookup. Exact bytes remain recoverable.
fn resolve(
    source: &mut impl Source,
    attempt: &Path,
    ingress: &[u8],
    lookup: bool,
) -> Result<Value> {
    let marker = attempt.join("submit-marker.json");
    let expected =
        json!({"type":FORMAT,"ingressSha256":digest(ingress),"status":"may-have-submitted"});
    if marker.exists() {
        if json_private(&marker)? != expected {
            return Err("adoption submit marker differs from sealed ingress".into());
        }
    } else if lookup {
        return Err("adoption has no submitted or uncertain attempt".into());
    } else {
        save_json_staged(&marker, &expected)?;
        if let Ok(value) = outcome(source, attempt, "submit", 189, ingress) {
            if value["type"] == "confirmed" {
                return Ok(value);
            }
        }
    }
    let stem = format!("lookup-{}", participant_enrollment::nonce()?);
    outcome(source, attempt, &stem, 190, ingress)
}
fn uncommitted_manifest(manifest: &Value) -> bool {
    manifest["prerotation"] == false
        || (manifest.get("prerotation").is_none() && manifest.get("nextPublicKey").is_none())
}
fn finalize(
    source: &mut impl Source,
    root: &Path,
    attempt: &Path,
    pin: &Value,
    receipt: &Value,
) -> Result<Value> {
    if receipt["type"] != "confirmed" {
        return Err("adoption is not confirmed; exact attempt retained for lookup".into());
    }
    let result_path = attempt.join("result.json");
    if result_path.exists() {
        let prior = json_private(&result_path)?;
        if prior["type"] != "minidregg-key-adoption-result-v1"
            || prior["request"] != pin["request"]
            || !same_receipt(&prior["outcome"], receipt)
        {
            return Err("adoption replay differs from retained original receipt".into());
        }
        // A later rotation is allowed. Never reinstall an obsolete commitment.
        return Ok(prior);
    }
    let request = &pin["request"];
    let view = status(source, &request["subject"], &request["currentPublicKey"])?;
    current(&view, &request["subject"])?;
    if view["keyId"] != pin["initialStatus"]["keyId"]
        || view["keyEpoch"] != pin["initialStatus"]["keyEpoch"]
        || view["prerotated"] != true
    {
        return Err("adoption receipt is retained, but current key changed; refusing stale workspace finalization".into());
    }
    let next = status(source, &request["subject"], &request["nextPublicKey"])?;
    if next["type"] != "subject-key-status-v1"
        || next["subject"] != request["subject"]
        || next["keyId"] != view["keyId"]
        || next["keyEpoch"] != view["keyEpoch"]
        || next["isCommittedNext"] != true
        || next["prerotated"] != true
        || next["currentRevoked"] != false
    {
        return Err("source has not confirmed the retained next-key commitment".into());
    }
    let manifest = json_private(&root.join("workspace.json"))?;
    if manifest["subject"] != request["subject"]
        || manifest["key"] != pin["context"]["key"]
        || !(uncommitted_manifest(&manifest)
            || (manifest["prerotation"] == true
                && manifest["nextPublicKey"] == request["nextPublicKey"]))
    {
        return Err("workspace commitment changed while adoption was pending".into());
    }
    let result = json!({"type":"minidregg-key-adoption-result-v1","request":request,
        "keyId":view["keyId"],"keyEpoch":view["keyEpoch"],"outcome":receipt});
    // A crash after the manifest rename is repaired by another exact lookup.
    // Final result is durable only after the commitment is durably installed.
    workspace::record_next_public(root, &public(request, "nextPublicKey")?)?;
    save_json_staged(&result_path, &result)?;
    Ok(result)
}
pub(crate) fn run(mut args: Args) -> Result<()> {
    let root = absolute(&path(args.required("workspace")?))?;
    let action = args.optional("action").unwrap_or_else(|| "submit".into());
    let action = action.to_str().ok_or("adoption action must be UTF-8")?;
    if !matches!(action, "prepare" | "submit" | "lookup") {
        return Err("adoption action must be prepare, submit or lookup".into());
    }
    let next_path = args
        .optional("next-key")
        .map(|v| absolute(&path(v)))
        .transpose()?;
    let named = args.optional("attempt");
    args.finish()?;
    workspace::private_dir(&root)?;
    let _transition = transport::service_lock(&root.join("key-transition.lock"))?;
    let ws = workspace::load_for_key_transition(&root)?;
    let identity = receipt_continuity::key_transition_identity(&root, &ws)?;
    let host = workspace::workspace_host(&ws)?;
    let config = participant_enrollment::member_path(&ws, "config")?;
    let daily = participant_enrollment::member_path(&ws, "key")?;
    let socket = SOCKET
        .get()
        .ok_or("adoption workspace requires a pinned socket")?
        .clone();
    let context = json!({"subject":ws["subject"],"key":daily,"host":ws["host"],
        "hostSha256":host_image_sha256(&host)?,"config":config,
        "configSha256":digest(&bounded(&config, 1024 * 1024)?),"socket":socket});
    let mut source = Connection {
        host,
        socket,
        config,
        trusted: Some((root.clone(), ws.clone(), identity.clone())),
    };
    let profile: Value =
        serde_json::from_slice(&call(&mut source, 6, &[])?).map_err(|e| e.to_string())?;
    let profile = json!({"domain":profile["domain"],"semantics":profile["semantics"],"expectedSeed":profile["expectedSeed"]});
    for name in ["domain", "semantics", "expectedSeed"] {
        if profile[name] != identity[name] {
            return Err(format!(
                "adoption endpoint profile differs from locally pinned {name}"
            ));
        }
    }
    for name in ["domain", "semantics"] {
        decimal(field(&profile, name)?, name)?;
    }
    let mut initial = None;
    let name = if let Some(name) = named {
        name.into_string()
            .map_err(|_| "attempt name must be UTF-8")?
    } else {
        if action == "lookup" {
            return Err("lookup requires --attempt CHILD (no signing keys required)".into());
        }
        let public = hex(&key(&daily)?.verifying_key().to_bytes());
        let view = status(&mut source, &ws["subject"], &json!(public))?;
        current(&view, &ws["subject"])?;
        let name = format!(
            "adopt-next-{}-{}",
            field(&view, "keyId")?,
            field(&view, "keyEpoch")?
        );
        initial = Some((public, view));
        name
    };
    if name.is_empty()
        || name.len() > 180
        || !name
            .bytes()
            .all(|b| b.is_ascii_alphanumeric() || b == b'-' || b == b'_')
    {
        return Err("adoption attempt must be one simple child name".into());
    }
    let attempt = root.join("attempts").join(&name);
    if !attempt.exists() {
        if action == "lookup" {
            return Err("adoption attempt does not exist".into());
        }
        workspace::make_private_dir(&attempt)?;
    }
    workspace::private_dir(&attempt)?;
    let _lock = transport::service_lock(&attempt.join("adoption.lock"))?;
    let pin_path = attempt.join("attempt.json");
    let pin = if pin_path.exists() {
        let pin = json_private(&pin_path)?;
        let mut old_context = pin["context"].clone();
        let mut selected_context = context.clone();
        if action == "lookup" && attempt.join("result.json").exists() {
            let prior = json_private(&attempt.join("result.json"))?;
            if prior["type"] != "minidregg-key-adoption-result-v1"
                || prior["request"] != pin["request"]
            {
                return Err("invalid completed adoption custody".into());
            }
            // Completed adoption is receipt-only history. A later local key path
            // may change; deployment, transport, subject and original signatures may not.
            old_context
                .as_object_mut()
                .ok_or("invalid retained adoption context")?
                .remove("key");
            selected_context
                .as_object_mut()
                .ok_or("invalid selected adoption context")?
                .remove("key");
        }
        if pin["type"] != FORMAT || old_context != selected_context || pin["profile"] != profile {
            return Err(
                "adoption custody no longer matches pinned workspace transport/profile".into(),
            );
        }
        if let Some(next) = &next_path {
            if hex(&key(next)?.verifying_key().to_bytes())
                != field(&pin["request"], "nextPublicKey")?
            {
                return Err("next key differs from retained adoption attempt".into());
            }
        }
        pin
    } else {
        if action == "lookup" || attempt.join("submit-marker.json").exists() {
            return Err("adoption custody is missing; refusing to reconstruct it".into());
        }
        if !uncommitted_manifest(&ws) {
            return Err("workspace already records a next key; use rotate-key".into());
        }
        let next = next_path
            .as_deref()
            .ok_or("--next-key is required for a new adoption")?;
        let next_public = hex(&key(next)?.verifying_key().to_bytes());
        let (current_public, view) = match initial {
            Some(initial) => initial,
            None => {
                let public = hex(&key(&daily)?.verifying_key().to_bytes());
                let view = status(&mut source, &ws["subject"], &json!(public))?;
                (public, view)
            }
        };
        current(&view, &ws["subject"])?;
        if view["prerotated"] != false {
            return Err("source already commits to a next key; adoption cannot replace it".into());
        }
        if current_public == next_public {
            return Err("next key must differ from current key".into());
        }
        let request = json!({"subject":ws["subject"],"nonce":participant_enrollment::nonce()?,
            "currentPublicKey":current_public,"nextPublicKey":next_public});
        let pin = json!({"type":FORMAT,"context":context,"profile":profile,"request":request,"initialStatus":view});
        save_json_staged(&pin_path, &pin)?;
        pin
    };
    // Missing pieces after submission never trigger source planning/assembly.
    if attempt.join("submit-marker.json").exists() || action == "lookup" {
        for name in [
            "plan.frame",
            "plan.bin",
            "plan.json",
            "current.sig",
            "next.sig",
            "ingress.frame",
            "ingress.bin",
            "ingress.json",
            "sealed.json",
        ] {
            private_bytes(&attempt.join(name), LIMIT)?;
        }
    }
    let ingress = seal(&mut source, &attempt, &pin, &daily, next_path.as_deref())?;
    if action == "prepare" {
        println!(
            "{}",
            json!({"type":FORMAT,"attempt":name,"status":"sealed","request":pin["request"]})
        );
        return Ok(());
    }
    if receipt_continuity::key_transition_identity(&root, &ws)? != identity {
        return Err("adoption lineage changed before submission; exact attempt retained".into());
    }
    let ticket = receipt_continuity::begin_attempt(&attempt)?;
    let receipt = resolve(&mut source, &attempt, &ingress, action == "lookup")?;
    if receipt["type"] != "confirmed" {
        note_host_decision(HostDecision::Outcome(receipt));
        return Err(format!("adoption not confirmed; use adopt-next-key --workspace {} --action lookup --attempt {name}", root.display()));
    }
    receipt_continuity::finish_attempt(
        ticket,
        &receipt,
        action == "lookup" || receipt["confirmation"] == "replayed",
    )?;
    let result = finalize(&mut source, &root, &attempt, &pin, &receipt)?;
    println!(
        "{}",
        serde_json::to_string_pretty(&result).map_err(|e| e.to_string())?
    );
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::os::unix::fs::PermissionsExt;

    struct Fixture {
        root: PathBuf,
        daily: PathBuf,
        next: PathBuf,
        pin: Value,
    }
    impl Fixture {
        fn new() -> Self {
            let root = env::temp_dir().join(format!(
                "mini-adopt-test-{}-{}",
                std::process::id(),
                participant_enrollment::nonce().unwrap()
            ));
            workspace::make_private_dir(&root).unwrap();
            let daily = root.join("daily.key");
            let next = root.join("next.key");
            crate::create_private(&daily, &[17; 32]).unwrap();
            crate::create_private(&next, &[29; 32]).unwrap();
            let request = json!({"subject":"7","nonce":"9",
                "currentPublicKey":hex(&key(&daily).unwrap().verifying_key().to_bytes()),
                "nextPublicKey":hex(&key(&next).unwrap().verifying_key().to_bytes())});
            let pin = json!({"type":FORMAT,"context":{"key":daily},"profile":{"domain":"1","semantics":"2","expectedSeed":"3"},
                "request":request,"initialStatus":{"type":"subject-key-status-v1","subject":"7","keyId":"11","keyEpoch":"5","isCurrent":true,"currentRevoked":false,"prerotated":false}});
            Self {
                root,
                daily,
                next,
                pin,
            }
        }
        fn plan(&self) -> Value {
            json!({"type":"subject-key-adoption-plan-v1","domain":"1","semantics":"2",
                "command":{"subject":"7","nonce":"9","nextPublicKey":self.pin["request"]["nextPublicKey"],
                    "expectedCurrent":{"keyId":"11","keyEpoch":"5","algorithm":"1","subject":"7",
                        "publicKey":self.pin["request"]["currentPublicKey"],"activeFrom":"0","activeUntil":"999","nextKeyDigest":null}},
                "commandBytes":"010203","currentAuthorizationHeader":"aabb01","nextPossessionHeader":"aabb02"})
        }
        fn attempt(&self) -> PathBuf {
            let path = self.root.join("attempt");
            workspace::make_private_dir(&path).unwrap();
            path
        }
    }
    impl Drop for Fixture {
        fn drop(&mut self) {
            let _ = fs::remove_dir_all(&self.root);
        }
    }
    /// Injected source codecs test client custody only; native semantics and real
    /// source frames are exercised by the separate receiving journey.
    struct Fake {
        plan: Value,
        calls: Vec<(u8, Vec<u8>)>,
        receipt: Value,
        uncertain: bool,
        statuses: Vec<Value>,
    }
    fn confirmed() -> Value {
        json!({"type":"confirmed","confirmation":"replayed","transactionId":"4","eventId":"5","acceptedCount":"6","worldRoot":"7"})
    }
    impl Fake {
        fn new(plan: Value) -> Self {
            Self {
                plan,
                calls: vec![],
                receipt: confirmed(),
                uncertain: false,
                statuses: vec![],
            }
        }
    }
    fn split(bytes: &[u8]) -> (&[u8], &[u8]) {
        let length = u32::from_le_bytes(bytes[..4].try_into().unwrap()) as usize;
        (&bytes[4..4 + length], &bytes[4 + length..])
    }
    impl Source for Fake {
        fn inspect_signed(&mut self, kind: &str, bytes: &[u8]) -> Result<Value> {
            let value: Value = serde_json::from_slice(bytes).map_err(|e| e.to_string())?;
            if kind == "subject-key-adoption-plan"
                && (value["currentAuthorizationHeader"] != "aabb01"
                    || value["nextPossessionHeader"] != "aabb02")
            {
                return Err("fixture local source rejected changed purpose/frame".into());
            }
            Ok(value)
        }
        fn invoke(&mut self, opcode: u8, payload: &[u8]) -> Result<Vec<u8>> {
            self.calls.push((opcode, payload.to_vec()));
            let body = match opcode {
                187 => {
                    let request: Value = serde_json::from_slice(payload).unwrap();
                    assert_eq!(
                        request["currentPublicKey"],
                        self.plan["command"]["expectedCurrent"]["publicKey"]
                    );
                    serde_json::to_vec(&self.plan).unwrap()
                }
                188 => {
                    let (plan, signatures) = split(payload);
                    let plan: Value = serde_json::from_slice(plan).unwrap();
                    let (current, next) = split(signatures);
                    serde_json::to_vec(&json!({"type":"subject-key-adoption-ingress-v1","command":plan["command"],
                        "commandBytes":plan["commandBytes"],"currentSignature":hex(current),"nextPossessionSignature":hex(next)})).unwrap()
                }
                8 => {
                    let length = u16::from_le_bytes(payload[..2].try_into().unwrap()) as usize;
                    payload[2 + length..].to_vec()
                }
                189 if self.uncertain => return Err("fixture lost reply after accepting".into()),
                189 | 190 => serde_json::to_vec(&self.receipt).unwrap(),
                144 => serde_json::to_vec(&self.statuses.remove(0)).unwrap(),
                _ => panic!("unexpected opcode {opcode}"),
            };
            Ok([vec![opcode], body].concat())
        }
    }
    #[test]
    fn plan_binds_identity_subject_nonce_current_record_and_next() {
        let f = Fixture::new();
        let plan = f.plan();
        let check = |p: &Value| {
            check_plan(
                p,
                &f.pin["request"],
                &f.pin["initialStatus"],
                &f.pin["profile"],
            )
        };
        check(&plan).unwrap();
        for pointer in [
            "/domain",
            "/semantics",
            "/command/subject",
            "/command/nonce",
            "/command/nextPublicKey",
            "/command/expectedCurrent/keyId",
            "/command/expectedCurrent/keyEpoch",
            "/command/expectedCurrent/publicKey",
            "/command/expectedCurrent/algorithm",
            "/command/expectedCurrent/subject",
            "/command/expectedCurrent/nextKeyDigest",
        ] {
            let mut wrong = plan.clone();
            *wrong.pointer_mut(pointer).unwrap() = json!("88");
            assert!(check(&wrong).is_err(), "accepted changed {pointer}");
        }
        let mut wrong = plan.clone();
        wrong["nextPossessionHeader"] = wrong["currentAuthorizationHeader"].clone();
        assert!(check(&wrong).is_err());
    }
    #[test]
    fn sealing_retains_exact_frames_and_reopens_without_either_secret() {
        let f = Fixture::new();
        let attempt = f.attempt();
        let mut source = Fake::new(f.plan());
        let ingress = seal(&mut source, &attempt, &f.pin, &f.daily, Some(&f.next)).unwrap();
        fs::remove_file(&f.daily).unwrap();
        fs::remove_file(&f.next).unwrap();
        assert_eq!(
            seal(&mut source, &attempt, &f.pin, &f.daily, None).unwrap(),
            ingress
        );
        assert_eq!(source.calls.iter().filter(|(op, _)| *op == 187).count(), 1);
        assert_eq!(source.calls.iter().filter(|(op, _)| *op == 188).count(), 1);
        assert_eq!(
            private_bytes(&attempt.join("ingress.bin"), LIMIT).unwrap(),
            ingress
        );
        assert_eq!(
            fs::metadata(attempt.join("current.sig"))
                .unwrap()
                .permissions()
                .mode()
                & 0o077,
            0
        );
        let mut wrong = json_private(&attempt.join("ingress.json")).unwrap();
        wrong["nextPossessionSignature"] = json!("00".repeat(64));
        assert!(check_ingress(
            &wrong,
            &f.plan(),
            &private_bytes(&attempt.join("current.sig"), 64).unwrap(),
            &private_bytes(&attempt.join("next.sig"), 64).unwrap()
        )
        .is_err());
    }
    #[test]
    fn submitted_attempt_never_signs_a_lost_signature_again() {
        let f = Fixture::new();
        let attempt = f.attempt();
        let mut source = Fake::new(f.plan());
        seal(&mut source, &attempt, &f.pin, &f.daily, Some(&f.next)).unwrap();
        crate::create_private(&attempt.join("submit-marker.json"), b"{}").unwrap();
        fs::remove_file(attempt.join("current.sig")).unwrap();
        assert!(seal(&mut source, &attempt, &f.pin, &f.daily, Some(&f.next))
            .unwrap_err()
            .contains("refusing to sign again"));
        assert!(!attempt.join("current.sig").exists());
    }
    #[test]
    fn uncertain_submit_and_every_retry_only_lookup_exact_ingress() {
        let f = Fixture::new();
        let attempt = f.attempt();
        let mut source = Fake::new(f.plan());
        source.uncertain = true;
        let ingress = seal(&mut source, &attempt, &f.pin, &f.daily, Some(&f.next)).unwrap();
        let before = fs::read(attempt.join("ingress.bin")).unwrap();
        assert_eq!(
            resolve(&mut source, &attempt, &ingress, false).unwrap(),
            confirmed()
        );
        source.receipt = json!({"type":"absent"});
        assert_eq!(
            resolve(&mut source, &attempt, &ingress, false).unwrap()["type"],
            "absent"
        );
        source.receipt = confirmed();
        resolve(&mut source, &attempt, &ingress, true).unwrap();
        assert_eq!(source.calls.iter().filter(|(op, _)| *op == 189).count(), 1);
        assert_eq!(source.calls.iter().filter(|(op, _)| *op == 190).count(), 3);
        assert!(source
            .calls
            .iter()
            .filter(|(op, _)| matches!(op, 189 | 190))
            .all(|(_, bytes)| bytes == &ingress));
        assert_eq!(fs::read(attempt.join("ingress.bin")).unwrap(), before);
        assert!(resolve(&mut source, &attempt, b"different", true).is_err());
    }
    #[test]
    fn durable_marker_before_any_submit_repairs_by_lookup() {
        let f = Fixture::new();
        let attempt = f.attempt();
        let mut source = Fake::new(f.plan());
        let ingress = b"exact sealed adoption";
        assert!(resolve(&mut source, &attempt, ingress, true).is_err());
        save_json_staged(
            &attempt.join("submit-marker.json"),
            &json!({"type":FORMAT,"ingressSha256":digest(ingress),"status":"may-have-submitted"}),
        )
        .unwrap();
        resolve(&mut source, &attempt, ingress, false).unwrap();
        assert_eq!(
            source.calls.iter().map(|c| c.0).collect::<Vec<_>>(),
            vec![190, 8]
        );
    }
    fn statuses(f: &Fixture) -> Vec<Value> {
        let mut current = f.pin["initialStatus"].clone();
        current["prerotated"] = json!(true);
        let mut next = current.clone();
        next["isCurrent"] = json!(false);
        next["isCommittedNext"] = json!(true);
        vec![current, next]
    }
    #[test]
    fn legacy_manifest_adoption_preserves_key_identity_and_unrelated_provenance() {
        let f = Fixture::new();
        let attempt = f.attempt();
        let mut source = Fake::new(f.plan());
        source.statuses = statuses(&f);
        let manifest = json!({"subject":"7","key":f.daily,"freshContinuity":{"id":"untouched"},"sshBinding":"unchanged"});
        save_json_staged(&f.root.join("workspace.json"), &manifest).unwrap();
        let key_before = fs::read(&f.daily).unwrap();
        let result = finalize(&mut source, &f.root, &attempt, &f.pin, &confirmed()).unwrap();
        let after = json_private(&f.root.join("workspace.json")).unwrap();
        for name in ["subject", "key", "freshContinuity", "sshBinding"] {
            assert_eq!(after[name], manifest[name]);
        }
        assert_eq!(after["nextPublicKey"], f.pin["request"]["nextPublicKey"]);
        assert_eq!(after["prerotation"], true);
        assert_eq!(fs::read(&f.daily).unwrap(), key_before);
        assert_eq!(json_private(&attempt.join("result.json")).unwrap(), result);
        // A later rotation's commitment must survive historical adoption replay.
        let mut later = after;
        later["nextPublicKey"] = json!("ff".repeat(32));
        fs::write(
            f.root.join("workspace.json"),
            serde_json::to_vec(&later).unwrap(),
        )
        .unwrap();
        assert_eq!(
            finalize(&mut source, &f.root, &attempt, &f.pin, &confirmed()).unwrap(),
            result
        );
        assert_eq!(json_private(&f.root.join("workspace.json")).unwrap(), later);
    }
    #[test]
    fn crash_after_commitment_rename_finishes_without_replacing_current_key() {
        let f = Fixture::new();
        let attempt = f.attempt();
        let mut source = Fake::new(f.plan());
        source.statuses = statuses(&f);
        save_json_staged(
            &f.root.join("workspace.json"),
            &json!({"subject":"7","key":f.daily,"prerotation":false}),
        )
        .unwrap();
        workspace::record_next_public(
            &f.root,
            &public(&f.pin["request"], "nextPublicKey").unwrap(),
        )
        .unwrap();
        assert!(!attempt.join("result.json").exists());
        finalize(&mut source, &f.root, &attempt, &f.pin, &confirmed()).unwrap();
        assert!(attempt.join("result.json").exists());
    }
    #[test]
    fn stale_or_wrong_commitment_does_not_publish_local_metadata() {
        for stale in [true, false] {
            let f = Fixture::new();
            let attempt = f.attempt();
            let mut source = Fake::new(f.plan());
            source.statuses = statuses(&f);
            if stale {
                source.statuses[0]["keyEpoch"] = json!("6");
            } else {
                source.statuses[1]["isCommittedNext"] = json!(false);
            }
            save_json_staged(
                &f.root.join("workspace.json"),
                &json!({"subject":"7","key":f.daily,"prerotation":false}),
            )
            .unwrap();
            let before = fs::read(f.root.join("workspace.json")).unwrap();
            assert!(finalize(&mut source, &f.root, &attempt, &f.pin, &confirmed()).is_err());
            assert_eq!(fs::read(f.root.join("workspace.json")).unwrap(), before);
            assert!(!attempt.join("result.json").exists());
        }
    }
    #[test]
    fn adoption_connection_sends_pinned_socket_envelope_and_exact_lookup_bytes() {
        use std::os::unix::net::UnixListener;
        let f = Fixture::new();
        let attempt = f.attempt();
        let host = f.root.join("host");
        let config = f.root.join("config.json");
        let socket = f.root.join("socket");
        crate::create_private(&host, b"fixture host image, never executed").unwrap();
        crate::create_private(&config, b"{}").unwrap();
        let host_digest =
            crate::decode_hex(&host_image_sha256(&host).unwrap()).unwrap();
        let listener = UnixListener::bind(&socket).unwrap();
        let ingress = b"exact signed ingress including zero\0byte".to_vec();
        let expected = ingress.clone();
        let server = std::thread::spawn(move || {
            for opcode in [189, 190, 8, 190, 8] {
                let (mut stream, _) = listener.accept().unwrap();
                let frame = transport::read_frame(&mut stream).unwrap().unwrap();
                assert_eq!(frame[0], 2);
                assert_eq!(u32::from_le_bytes(frame[1..5].try_into().unwrap()), 2);
                assert_eq!(&frame[5..7], b"{}");
                assert_eq!(&frame[7..39], host_digest.as_slice());
                assert_eq!(frame[39], opcode);
                if opcode == 189 || opcode == 190 {
                    assert_eq!(&frame[40..], expected.as_slice());
                }
                if opcode == 189 {
                    continue;
                } // receipt lost after accept
                let body = serde_json::to_vec(&confirmed()).unwrap();
                transport::write_frame(&mut stream, &[vec![opcode], body].concat()).unwrap();
            }
        });
        let mut source = Connection {
            host,
            config,
            socket,
            trusted: None,
        };
        resolve(&mut source, &attempt, &ingress, false).unwrap();
        resolve(&mut source, &attempt, &ingress, false).unwrap();
        server.join().unwrap();
        assert!(attempt.join("submit-marker.json").exists());
    }
    #[test]
    fn legacy_or_missing_enabled_custody_cannot_authorize_adoption() {
        for enabled in [false, true] {
            let f = Fixture::new();
            let mut manifest =
                json!({"type":"minidregg-participant-workspace-v1","subject":"7","key":f.daily});
            if enabled {
                manifest["receiptContinuity"] = json!("minidregg-continuity-v1");
            }
            save_json_staged(&f.root.join("workspace.json"), &manifest).unwrap();
            assert!(receipt_continuity::key_transition_identity(&f.root, &manifest).is_err());
            assert!(!f.root.join("receipt-continuity").exists());
            assert_eq!(
                json_private(&f.root.join("workspace.json")).unwrap(),
                manifest
            );
        }
    }

    #[test]
    fn adoption_run_recovers_completed_receipt_after_current_key_path_changes() {
        let output = Command::new(env::current_exe().unwrap())
            .args([
                "--exact",
                "key_adoption::tests::adoption_run_fixture_child",
                "--nocapture",
            ])
            .env("MINI_ADOPTION_CHILD", "lookup")
            .output()
            .unwrap();
        assert!(
            output.status.success(),
            "{}\n{}",
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        );
    }
    #[test]
    fn adoption_remote_workspace_uses_pinned_host_without_local_executable() {
        let output = Command::new(env::current_exe().unwrap())
            .args([
                "--exact",
                "key_adoption::tests::adoption_run_fixture_child",
                "--nocapture",
            ])
            .env("MINI_ADOPTION_CHILD", "remote")
            .output()
            .unwrap();
        assert!(
            output.status.success(),
            "{}\n{}",
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        );
    }
    #[test]
    fn adoption_run_fixture_child() {
        let Ok(mode) = env::var("MINI_ADOPTION_CHILD") else {
            return;
        };
        let mut f = Fixture::new();
        for name in ["refs", "attempts", "sources", "proposals"] {
            workspace::make_private_dir(&f.root.join(name)).unwrap();
        }
        let config = f.root.join("config.json");
        crate::create_private(&config, b"{}").unwrap();
        if mode == "remote" {
            let manifest = json!({"type":"minidregg-participant-workspace-v1","subject":"7","key":f.daily,
                "config":config,"host":null,"hostSha256":"11".repeat(32),"socket":"ssh:member@example.test"});
            save_json_staged(&f.root.join("workspace.json"), &manifest).unwrap();
            let loaded = workspace::load_for_key_transition(&f.root).unwrap();
            let host = workspace::workspace_host(&loaded).unwrap();
            assert!(host.as_os_str().is_empty());
            assert_eq!(host_image_sha256(&host).unwrap(), "11".repeat(32));
            return;
        }
        use std::os::unix::net::UnixListener;
        let host = f.root.join("fixture-verifier");
        // Injected pure local source codec, not a native semantic claim. The
        // endpoint is forbidden from supplying plan/ingress interpretation.
        crate::create_private(
            &host,
            br#"#!/usr/bin/env python3
import json, sys
if sys.argv[2] == 'profile':
    print('{"domain":"1","semantics":"2","expectedSeed":"3"}')
elif sys.argv[2] == 'author':
    kind = sys.argv[3]
    assert kind in ('signing-key-next-digest', 'subject-key-rotation')
    value = json.load(open(sys.argv[4]))
    with open(sys.argv[5], 'wb') as output:
        output.write(b'777' if kind == 'signing-key-next-digest' else bytes([1,2]))
else:
    assert sys.argv[2] == 'inspect'
    kind = sys.argv[3]
    assert kind in ('subject-key-adoption-plan', 'subject-key-adoption-ingress', 'subject-key-rotation-plan')
    value = json.load(open(sys.argv[4]))
    if kind == 'subject-key-adoption-plan':
        assert value['currentAuthorizationHeader'] == 'aabb01'
        assert value['nextPossessionHeader'] == 'aabb02'
    if kind == 'subject-key-rotation-plan':
        assert value['possessionHeader'] == 'aabb03'
        value['possessionFrameValidated'] = True
    with open(sys.argv[5], 'w') as output:
        json.dump(value, output)
"#,
        )
        .unwrap();
        fs::set_permissions(&host, fs::Permissions::from_mode(0o700)).unwrap();
        let host_digest = host_image_sha256(&host).unwrap();
        let socket = f.root.join("socket");
        let current_path = f.root.join("rotated-current.key");
        crate::create_private(&current_path, &[47; 32]).unwrap();
        let manifest = json!({"type":"minidregg-participant-workspace-v1","subject":"7","key":current_path,
            "config":config,"host":host,"hostSha256":host_digest,"socket":socket,
            "prerotation":true,"nextPublicKey":"ff".repeat(32),"receiptContinuity":"minidregg-continuity-v1"});
        save_json_staged(&f.root.join("workspace.json"), &manifest).unwrap();
        let custody = f.root.join("receipt-continuity");
        workspace::make_private_dir(&custody).unwrap();
        let identity = json!({"algorithm":"minidregg-continuity-v1","domain":"1","semantics":"2","expectedSeed":"3"});
        save_json_staged(
            &custody.join("enabled.json"),
            &json!({"type":"minidregg-receipt-continuity-custody-v1",
            "identity":identity,"verifier":host,"verifierSha256":host_digest}),
        )
        .unwrap();
        save_json_staged(
            &custody.join("anchor.json"),
            &json!({"identity":identity,
            "point":{"height":"6","worldRoot":"7"},"chain":"0","siblings":[]}),
        )
        .unwrap();
        f.pin["context"] = json!({"subject":"7","key":f.daily,"host":host,"hostSha256":host_digest,
            "config":config,"configSha256":digest(b"{}"),"socket":socket});
        if mode == "reject-local" {
            let mut connection = Connection {
                host: host.clone(),
                config: config.clone(),
                socket: socket.clone(),
                trusted: Some((f.root.clone(), manifest.clone(), identity.clone())),
            };
            let good = f.plan();
            connection
                .inspect_signed(
                    "subject-key-adoption-plan",
                    &serde_json::to_vec(&good).unwrap(),
                )
                .unwrap();
            let mut wrong = good.clone();
            wrong["currentAuthorizationHeader"] = json!("ff0011");
            assert!(connection
                .inspect_signed(
                    "subject-key-adoption-plan",
                    &serde_json::to_vec(&wrong).unwrap()
                )
                .unwrap_err()
                .contains("pinned local verifier refused"));
            assert!(connection.inspect_signed("outcome", b"anything").is_err());
            let mut wrong_identity = identity.clone();
            wrong_identity["semantics"] = json!("99");
            assert!(receipt_continuity::key_source(
                &f.root,
                &manifest,
                &wrong_identity,
                receipt_continuity::KeySourceOperation::AdoptionPlan,
                b"{}"
            )
            .is_err());
            let mut wrong_manifest = manifest.clone();
            wrong_manifest["subject"] = json!("99");
            assert!(receipt_continuity::key_source(
                &f.root,
                &wrong_manifest,
                &identity,
                receipt_continuity::KeySourceOperation::AdoptionPlan,
                b"{}"
            )
            .is_err());
            assert!(connection
                .inspect_signed("subject-key-adoption-plan", &vec![1; LIMIT + 1])
                .is_err());
            OpenOptions::new()
                .append(true)
                .open(&host)
                .unwrap()
                .write_all(b"\n# changed artifact\n")
                .unwrap();
            assert!(connection
                .inspect_signed(
                    "subject-key-adoption-plan",
                    &serde_json::to_vec(&good).unwrap()
                )
                .unwrap_err()
                .contains("verifier image changed"));
            assert_eq!(
                json_private(&f.root.join("workspace.json")).unwrap(),
                manifest
            );
            return;
        }
        if mode == "rotation-reject" {
            let listener = UnixListener::bind(&socket).unwrap();
            let server = std::thread::spawn(move || {
                for opcode in [144, 140] {
                    let (mut stream, _) = listener.accept().unwrap();
                    let frame = transport::read_frame(&mut stream).unwrap().unwrap();
                    assert_eq!(
                        frame[39], opcode,
                        "rotation must use local digest/command author and local inspector"
                    );
                    let response = if opcode == 144 {
                        json!({"keyId":"11","keyEpoch":"5","isCommittedNext":true,"prerotated":true})
                    } else {
                        assert_eq!(&frame[40..], &[1, 2]);
                        json!({"type":"subject-key-rotation-plan-v1","domain":"1","semantics":"2",
                                "commandBytes":"0102","possessionHeader":"ff0011","possessionFrameValidated":true})
                    };
                    transport::write_frame(
                        &mut stream,
                        &[vec![opcode], serde_json::to_vec(&response).unwrap()].concat(),
                    )
                    .unwrap();
                }
            });
            let before = fs::read(f.root.join("workspace.json")).unwrap();
            let error = key_rotation::rotate_key(Args {
                command: "rotate-key".into(),
                values: vec![
                    ("--workspace".into(), f.root.as_os_str().to_owned()),
                    ("--next-key".into(), f.next.as_os_str().to_owned()),
                ],
            })
            .unwrap_err();
            server.join().unwrap();
            assert!(
                error.contains("pinned local verifier refused subject-key-rotation-plan"),
                "{error}"
            );
            assert!(!f.root.join("attempts/rotate-6/ingress.bin").exists());
            assert_eq!(fs::read(f.root.join("workspace.json")).unwrap(), before);
            return;
        }

        let attempt = f.root.join("attempts").join("adopt-next-11-5");
        workspace::make_private_dir(&attempt).unwrap();
        save_json_staged(&attempt.join("attempt.json"), &f.pin).unwrap();
        let mut fake = Fake::new(f.plan());
        let ingress = seal(&mut fake, &attempt, &f.pin, &f.daily, Some(&f.next)).unwrap();
        save_json_staged(
            &attempt.join("submit-marker.json"),
            &json!({"type":FORMAT,"ingressSha256":digest(&ingress),"status":"may-have-submitted"}),
        )
        .unwrap();
        save_json_staged(&attempt.join("result.json"),&json!({"type":"minidregg-key-adoption-result-v1","request":f.pin["request"],"outcome":confirmed()})).unwrap();
        fs::remove_file(&f.daily).unwrap();
        fs::remove_file(&f.next).unwrap();
        let manifest_before = fs::read(f.root.join("workspace.json")).unwrap();
        let listener = UnixListener::bind(&socket).unwrap();
        let server = std::thread::spawn(move || {
            for expected in [6, 190, 8] {
                let (mut stream, _) = listener.accept().unwrap();
                let frame = transport::read_frame(&mut stream).unwrap().unwrap();
                assert_eq!(
                    frame[39], expected,
                    "completed lookup must not replan, sign, submit or query current key"
                );
                let response = if expected == 6 {
                    [
                        vec![6],
                        br#"{"domain":"1","semantics":"2","expectedSeed":"3"}"#.to_vec(),
                    ]
                    .concat()
                } else {
                    fake.invoke(expected, &frame[40..]).unwrap()
                };
                transport::write_frame(&mut stream, &response).unwrap();
            }
        });
        run(Args {
            command: "adopt-next-key".into(),
            values: vec![
                ("--workspace".into(), f.root.as_os_str().to_owned()),
                ("--action".into(), "lookup".into()),
                ("--attempt".into(), "adopt-next-11-5".into()),
            ],
        })
        .unwrap();
        server.join().unwrap();
        assert_eq!(
            fs::read(f.root.join("workspace.json")).unwrap(),
            manifest_before
        );
        assert_eq!(fs::read(current_path).unwrap(), vec![47; 32]);
    }
    #[test]
    fn endpoint_inspection_cannot_authorize_changed_signing_purpose() {
        let f = Fixture::new();
        let attempt = f.attempt();
        let mut altered = f.plan();
        altered["currentAuthorizationHeader"] = json!("ff0011");
        let mut source = Fake::new(altered);
        assert!(seal(&mut source, &attempt, &f.pin, &f.daily, Some(&f.next))
            .unwrap_err()
            .contains("local source rejected"));
        assert!(!attempt.join("current.sig").exists());
        assert!(!attempt.join("next.sig").exists());
        assert!(!attempt.join("submit-marker.json").exists());
        assert_eq!(
            source.calls.iter().map(|(op, _)| *op).collect::<Vec<_>>(),
            vec![187]
        );
    }
    #[test]
    fn adoption_pinned_local_source_checks_frames_identity_manifest_and_artifact() {
        let output = Command::new(env::current_exe().unwrap())
            .args([
                "--exact",
                "key_adoption::tests::adoption_run_fixture_child",
                "--nocapture",
            ])
            .env("MINI_ADOPTION_CHILD", "reject-local")
            .output()
            .unwrap();
        assert!(
            output.status.success(),
            "{}\n{}",
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        );
    }
    #[test]
    fn adoption_protected_rotation_uses_local_authors_and_refuses_forged_frame() {
        let output = Command::new(env::current_exe().unwrap())
            .args([
                "--exact",
                "key_adoption::tests::adoption_run_fixture_child",
                "--nocapture",
            ])
            .env("MINI_ADOPTION_CHILD", "rotation-reject")
            .output()
            .unwrap();
        assert!(
            output.status.success(),
            "{}\n{}",
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        );
    }
}
