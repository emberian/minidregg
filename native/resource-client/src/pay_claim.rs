//! One retained signed claim ingress, submitted at most once by this client.
//! Source ops 183/184 construct and inspect bytes; 185 submits; 186 only looks up.
//! A pre-existing operation directory never plans, quotes, signs, or submits.
//! Even an incomplete directory is retained and refused, not silently restarted.
use super::*;
use crate::workspace;

const RECORD_TYPE: &str = "minidregg-pay-claim-operation-v1";

trait Backend {
    fn call(&mut self, operation: u8, payload: &[u8]) -> Result<Vec<u8>>;
    fn inspect(&mut self, kind: &str, input: &Path, output: &Path) -> Result<Value>;
}

enum Endpoint {
    Socket(PathBuf),
    Bootstrap(String),
}

struct Session {
    host: PathBuf,
    config: PathBuf,
    endpoint: Endpoint,
    sha: String,
    config_sha: String,
    record: PathBuf,
    metadata_checked: bool,
    context: Option<crate::paid_context::Context>,
}

fn bootstrap_url(base: &str) -> Result<()> {
    minidregg_pay_watcher::transport::validate_endpoint(base)?;
    if !base.ends_with("/mini/v2") || base.contains('?') || base.contains('#') {
        return Err("claim bootstrap URL must end in /mini/v2 without query or fragment".into());
    }
    Ok(())
}

fn claim_route(operation: u8) -> Result<(&'static str, &'static str)> {
    match operation {
        183 => Ok(("/claim/plan", "canonicalPlan")),
        184 => Ok(("/claim/assemble", "canonicalIngress")),
        185 => Ok(("/claim/submit", "canonicalOutcome")),
        186 => Ok(("/claim/lookup", "canonicalOutcome")),
        _ => Err("claim HTTP transport has no generic operation route".into()),
    }
}

fn decode_claim_wire(operation: u8, bytes: &[u8]) -> Result<Vec<u8>> {
    if bytes.len() > 16 * 1024 {
        return Err("claim HTTP response exceeds bound".into());
    }
    let value: Value =
        serde_json::from_slice(bytes).map_err(|e| format!("claim HTTP JSON: {e}"))?;
    let (_, field) = claim_route(operation)?;
    require_type(&value, "payClaimWire")?;
    if text(&value, "operation")? != operation.to_string()
        || value.as_object().is_none_or(|fields| fields.len() != 3)
    {
        return Err("claim HTTP response operation/shape differs".into());
    }
    let raw = text(&value, field)?;
    if raw.is_empty()
        || raw.len() > 8192
        || raw.len() % 2 != 0
        || !mini_sdk::hex::is_lower(raw)
    {
        return Err(
            "claim HTTP canonical response must be 1..4096 lowercase hexadecimal bytes".into(),
        );
    }
    let mut frame = vec![operation];
    frame.extend_from_slice(&decode_hex(raw)?);
    Ok(frame)
}

fn profile_number(value: &Value, name: &str) -> Result<String> {
    if value.get(name).is_some_and(Value::is_string) {
        return decimal(value, name);
    }
    value
        .get(name)
        .and_then(Value::as_u64)
        .map(|n| n.to_string())
        .ok_or_else(|| format!("profile/metadata {name} must be an unsigned exact integer"))
}

// Decimal-to-fixed-little-endian representation only. The pinned local
// profile owns the values; this does not derive or evaluate any policy.
fn profile_digest(profile: &Value, name: &str) -> Result<Vec<u8>> {
    let number = profile_number(profile, name)?;
    let mut bytes = vec![0u8; 32];
    for digit in number.bytes() {
        let mut carry = u16::from(digit - b'0');
        for byte in &mut bytes {
            let next = u16::from(*byte) * 10 + carry;
            *byte = next as u8;
            carry = next >> 8;
        }
        if carry != 0 {
            return Err(format!("profile {name} exceeds 256 bits"));
        }
    }
    Ok(bytes)
}

fn validate_plan_profile(plan: &Value, profile: &Value) -> Result<()> {
    for name in ["domain", "semantics"] {
        if exact_hex(plan, name, 32)? != profile_digest(profile, name)? {
            return Err(format!(
                "claim plan {name} differs from pinned local profile"
            ));
        }
    }
    Ok(())
}

fn validate_metadata(metadata: &Value, profile: &Value, sha: &str) -> Result<()> {
    require_type(metadata, "minidregg-enrollment-bootstrap-v2")?;
    if text(metadata, "hostSha256")? != sha
        || profile_number(metadata, "domain")? != profile_number(profile, "domain")?
        || profile_number(metadata, "semantics")? != profile_number(profile, "semantics")?
        || text(metadata, "quoteType")? != "payQuote"
        || text(metadata, "statusType")? != "payStatus"
        || text(metadata, "expiryClock")? != "processingChainHour"
        || text(metadata, "recovery")? != "acceptCurrentQuote"
        || !metadata
            .get("memoVersions")
            .and_then(Value::as_array)
            .is_some_and(|versions| {
                versions
                    .iter()
                    .any(|version| version.as_str() == Some("enrol:v2"))
            })
    {
        return Err(
            "claim bootstrap metadata differs from pinned Host/profile or v2 contract".into(),
        );
    }
    Ok(())
}

impl Session {
    fn check_pins(&self) -> Result<()> {
        if self.host.as_os_str().is_empty() || host_image_sha256(&self.host)? != self.sha {
            return Err("claim requires its original pinned local Host inspector".into());
        }
        if digest(&crate::fsio::read_bounded_or_empty(&self.config, 1024 * 1024)?) != self.config_sha {
            return Err("claim inspector config differs from original profile pin".into());
        }
        Ok(())
    }

    // Deliberately bypasses process()/SOCKET: the pinned local source owns all
    // decoding and expected receipt identities, even when bytes came over HTTPS.
    fn local(&self, args: &[&OsStr]) -> Result<Output> {
        self.check_pins()?;
        let output = Command::new(&self.host)
            .arg(&self.config)
            .args(args)
            .output()
            .map_err(|e| format!("cannot run local claim inspector: {e}"))?;
        self.check_pins()?;
        if !output.status.success() {
            return Err(format!(
                "local source claim inspection refused ({})",
                output.status
            ));
        }
        Ok(output)
    }

    fn http_metadata(&mut self) -> Result<(String, PathBuf)> {
        let Endpoint::Bootstrap(base) = &self.endpoint else {
            return Err("not HTTP".into());
        };
        let base = base.clone();
        bootstrap_url(&base)?;
        let spool = self.record.join("http-spool");
        if !spool.exists() {
            workspace::make_private_dir(&spool)?;
        }
        workspace::private_dir(&spool)?;
        if !self.metadata_checked {
            let profile = self.local(&[OsStr::new("profile")])?;
            if profile.stdout.len() > 16 * 1024 {
                return Err("local source profile exceeds bound".into());
            }
            let profile: Value =
                serde_json::from_slice(&profile.stdout).map_err(|e| e.to_string())?;
            let transport = minidregg_pay_watcher::CurlTransport::new(
                "claim-metadata",
                format!("{base}/metadata"),
                &spool,
            )?
            .with_bounds(std::time::Duration::from_secs(5), 16 * 1024);
            let bytes = transport
                .request("GET", None)
                .map_err(|e| format!("claim metadata: {e}"))?;
            let metadata: Value = serde_json::from_slice(&bytes).map_err(|e| e.to_string())?;
            validate_metadata(&metadata, &profile, &self.sha)?;
            let retained = self.record.join("bootstrap-metadata.json");
            if !retained.exists() {
                retain_json(&retained, &metadata)?;
                sync_directory_ancestors(&self.record)?;
            }
            self.metadata_checked = true;
        }
        Ok((base, spool))
    }

    fn quote(&mut self, request: &Value) -> Result<Value> {
        self.check_pins()?;
        let payload = serde_json::to_vec(request).map_err(|e| e.to_string())?;
        if payload.len() > 4096 {
            return Err("claim quote request exceeds bound".into());
        }
        let bytes = match &self.endpoint {
            Endpoint::Socket(socket) => {
                let reply =
                    transport::invoke_pinned(socket, &self.config, &self.sha, 182, &payload)?;
                if reply.first() != Some(&182) {
                    return Err("source claim quote refused".into());
                }
                reply[1..].to_vec()
            }
            Endpoint::Bootstrap(_) => {
                let (base, spool) = self.http_metadata()?;
                minidregg_pay_watcher::CurlTransport::new(
                    "claim-quote",
                    format!("{base}/quote"),
                    &spool,
                )?
                .with_bounds(std::time::Duration::from_secs(5), 16 * 1024)
                .request("POST", Some(&payload))
                .map_err(|e| format!("claim quote HTTP: {e}"))?
            }
        };
        self.check_pins()?;
        if bytes.len() > 16 * 1024 {
            return Err("source quote exceeds bound".into());
        }
        serde_json::from_slice(&bytes).map_err(|e| format!("source quote JSON: {e}"))
    }

    fn http(&mut self, operation: u8, payload: &[u8]) -> Result<Vec<u8>> {
        let (route, _) = claim_route(operation)?;
        if payload.is_empty() || payload.len() > 4096 {
            return Err("claim HTTP payload exceeds bound".into());
        }
        let (base, spool) = self.http_metadata()?;
        let transport = minidregg_pay_watcher::CurlTransport::new(
            "claim-wire",
            format!("{base}{route}"),
            &spool,
        )?
        .with_bounds(std::time::Duration::from_secs(5), 16 * 1024);
        let bytes = transport
            .post_binary(payload)
            .map_err(|e| format!("claim HTTP: {e}"))?;
        decode_claim_wire(operation, &bytes)
    }
}

impl Backend for Session {
    fn call(&mut self, operation: u8, payload: &[u8]) -> Result<Vec<u8>> {
        self.check_pins()?;
        match &self.endpoint {
            Endpoint::Socket(socket) => {
                transport::invoke_pinned_with_local(&self.host, socket, &self.config, &self.sha, operation, payload)
            }
            Endpoint::Bootstrap(_) => {
                let reply = self.http(operation, payload)?;
                if crate::client_consent::plan_operation(operation) && reply.first() == Some(&operation) {
                    crate::client_consent::operator_plan(&self.host, &self.config, operation, payload, &reply[1..])?;
                }
                Ok(reply)
            },
        }
    }
    fn inspect(&mut self, kind: &str, input: &Path, output: &Path) -> Result<Value> {
        if output.exists() {
            return Err("claim inspection output already exists".into());
        }
        self.local(&[
            OsStr::new("inspect"),
            OsStr::new(kind),
            input.as_os_str(),
            output.as_os_str(),
        ])?;
        let bytes = crate::fsio::read_bounded_or_empty(output, 16 * 1024)?;
        let value: Value = serde_json::from_slice(&bytes)
            .map_err(|e| format!("local source inspection JSON: {e}"))?;
        if let (Some(context), Some(command)) = (&self.context, value.get("command")) {
            context.validate_source_command(command)?;
        }
        if kind == "pay-claim-plan" {
            let output = self.local(&[OsStr::new("profile")])?;
            if output.stdout.len() > 16 * 1024 {
                return Err("local source profile exceeds bound".into());
            }
            let profile: Value =
                serde_json::from_slice(&output.stdout).map_err(|e| e.to_string())?;
            validate_plan_profile(&value, &profile)?;
        }
        sync_retained_call(
            output.parent().ok_or("inspection output parent missing")?,
            output,
        )?;
        Ok(value)
    }
}


fn text<'a>(value: &'a Value, name: &str) -> Result<&'a str> {
    value
        .get(name)
        .and_then(Value::as_str)
        .ok_or_else(|| format!("source view lacks {name}"))
}

fn require_type(value: &Value, kind: &str) -> Result<()> {
    if text(value, "type")? != kind {
        return Err(format!("expected source {kind} view"));
    }
    Ok(())
}

fn exact_hex(value: &Value, field: &str, size: usize) -> Result<Vec<u8>> {
    let raw = text(value, field)?;
    if raw.len() != size * 2
        || !mini_sdk::hex::is_lower(raw)
    {
        return Err(format!(
            "source {field} must be {size} lowercase hexadecimal bytes"
        ));
    }
    decode_hex(raw)
}

fn canonical_matches(value: &Value, field: &str, bytes: &[u8]) -> Result<()> {
    if text(value, field)? != hex(bytes) {
        return Err(format!("source {field} differs from retained bytes"));
    }
    Ok(())
}

fn digest(bytes: &[u8]) -> String {
    hex(&sha2::Sha256::digest(bytes))
}

fn frame_body(frame: &[u8], operation: u8, bound: usize) -> Result<&[u8]> {
    match frame {
        [actual, body @ ..] if *actual == operation && !body.is_empty() && body.len() <= bound => {
            Ok(body)
        }
        [255, ..] => Err(format!(
            "Host refused claim op{operation}; no automatic rebase or retry"
        )),
        _ => Err(format!("invalid or oversized claim op{operation} response")),
    }
}

fn command_action(command: &Value, action: &str) -> Result<Vec<u8>> {
    exact_hex(command, "expectedAuthorityRoot", 32)?;
    exact_hex(command, "expectedPayRoot", 32)?;
    let source = command.get("action").ok_or("source command lacks action")?;
    exact_hex(source, "identityKey", 32)?;
    match (action, text(source, "action")?) {
        ("accept", "acceptCurrentQuote") => exact_hex(source, "authorizingKey", 32),
        ("rotate", "rotatePendingOwner") => exact_hex(source, "successorKey", 32),
        _ => Err("requested action differs from canonical source command".into()),
    }
}

fn decimal(value: &Value, field: &str) -> Result<String> {
    let value = text(value, field)?;
    if !mini_sdk::decimal::is_canonical_max(value, 78)
    {
        return Err(format!("source {field} is not a bounded canonical decimal"));
    }
    Ok(value.to_owned())
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct ExpectedReceipt {
    transaction: String,
    event: String,
}

impl ExpectedReceipt {
    fn source(value: &Value) -> Result<Self> {
        Ok(Self {
            transaction: decimal(value, "transactionId")?,
            event: decimal(value, "eventId")?,
        })
    }
    fn json(&self) -> Value {
        json!({"transactionId":self.transaction,"eventId":self.event})
    }
}

#[derive(Debug, PartialEq, Eq)]
enum Decision {
    Confirmed(Value),
    Refused(Value),
    Absent(Value),
    Contention(Value),
    Unavailable(Value),
    Uncertain(Value),
}

impl Decision {
    fn source(value: Value, expected: &ExpectedReceipt) -> Result<Self> {
        match text(&value, "type")? {
            "confirmed" => {
                if ExpectedReceipt::source(&value)? != *expected {
                    return Err("confirmed claim receipt differs from exact source ingress".into());
                }
                if !matches!(
                    text(&value, "confirmation")?,
                    "installed" | "recoveredAfterUncertainResponse" | "replayed"
                ) {
                    return Err("unknown claim confirmation kind".into());
                }
                decimal(&value, "acceptedCount")?;
                decimal(&value, "worldRoot")?;
                Ok(Self::Confirmed(value))
            }
            "refused" => {
                text(&value, "reason")?;
                Ok(Self::Refused(value))
            }
            "absent" => Ok(Self::Absent(value)),
            "contention" => Ok(Self::Contention(value)),
            "unavailable" => Ok(Self::Unavailable(value)),
            "uncertain" => Ok(Self::Uncertain(value)),
            _ => Err("unknown source claim outcome".into()),
        }
    }
    fn finish(self) -> Result<()> {
        let value = match self {
            Self::Confirmed(v)
            | Self::Refused(v)
            | Self::Absent(v)
            | Self::Contention(v)
            | Self::Unavailable(v)
            | Self::Uncertain(v) => v,
        };
        print_confirmed_outcome(&value)
    }
}

fn inspect_unique<B: Backend>(
    backend: &mut B,
    dir: &Path,
    kind: &str,
    input: &Path,
) -> Result<Value> {
    // Use the common retained-evidence allocator, including for repeated lookup inspections.
    let (_, output) = next_retry(dir)?;
    let value = backend.inspect(kind, input, &output)?;
    // Real inspect persists its source rendering; test backends follow the same contract.
    sync_directory_ancestors(dir)?;
    Ok(value)
}

fn exchange_outcome<B: Backend>(
    backend: &mut B,
    dir: &Path,
    operation: u8,
    ingress: &[u8],
    expected: &ExpectedReceipt,
) -> Result<Decision> {
    let (binary, json_path) = next_retry(dir)?;
    let frame = match backend.call(operation, ingress) {
        Ok(frame) => frame,
        Err(error) => {
            retain_json(
                &json_path,
                &json!({"type":"claimTransportUncertain","operation":operation,
                "detail":error,"recovery":"exact lookup only"}),
            )?;
            sync_directory_ancestors(dir)?;
            return Err(
                "claim reply unavailable; retained operation permits exact lookup only".into(),
            );
        }
    };
    let body = frame_body(&frame, operation, 8192)?;
    create_private(&binary, body)?;
    sync_directory_ancestors(dir)?;
    let outcome = backend.inspect("outcome", &binary, &json_path)?;
    Decision::source(outcome, expected)
}

fn validate_ingress(
    view: &Value,
    command: &[u8],
    canonical_ingress: &[u8],
    signature: &[u8],
    command_view: &Value,
) -> Result<ExpectedReceipt> {
    require_type(view, "payClaimIngress")?;
    canonical_matches(view, "canonicalCommand", command)?;
    canonical_matches(view, "canonicalIngress", canonical_ingress)?;
    canonical_matches(view, "signature", signature)?;
    if view.get("command") != Some(command_view) {
        return Err("assembled claim command differs from retained source command".into());
    }
    ExpectedReceipt::source(
        view.get("expectedReceipt")
            .ok_or("source ingress lacks expectedReceipt")?,
    )
}

fn recover<B: Backend>(
    backend: &mut B,
    dir: &Path,
    binding: &Value,
    action: &str,
    supplied: Option<&[u8]>,
    config: &[u8],
) -> Result<Decision> {
    workspace::private_dir(dir)?;
    let record = workspace::bounded_json(&dir.join("operation.json")).map_err(|e| {
        format!("incomplete claim operation; it cannot be replanned or resigned: {e}")
    })?;
    require_type(&record, RECORD_TYPE)?;
    if record.get("binding") != Some(binding) {
        return Err("claim operation workspace/config/Host/transport pin differs".into());
    }
    if action != "lookup" && text(&record, "action")? != action {
        return Err(
            "claim operation action differs; retained operation allows only exact lookup".into(),
        );
    }
    let command = crate::fsio::read_bounded_or_empty(&dir.join("command.bin"), 2048)?;
    if supplied.is_some_and(|bytes| bytes != command) {
        return Err("claim operation command or authority differs; refusing rebase".into());
    }
    let retained_config = crate::fsio::read_bounded_or_empty(&dir.join("config.json"), 1024 * 1024)?;
    if config != retained_config {
        return Err("claim operation config differs from original profile pin".into());
    }
    let plan = crate::fsio::read_bounded_or_empty(&dir.join("plan.bin"), 3072)?;
    let signature = crate::fsio::read_bounded_or_empty(&dir.join("signature.bin"), 64)?;
    let ingress = crate::fsio::read_bounded_or_empty(&dir.join("ingress.bin"), 4096)?;
    for (field, bytes) in [
        ("commandSha256", command.as_slice()),
        ("planSha256", plan.as_slice()),
        ("signatureSha256", signature.as_slice()),
        ("ingressSha256", ingress.as_slice()),
        ("configSha256", retained_config.as_slice()),
    ] {
        if text(&record, field)? != digest(bytes) {
            return Err(format!("claim retained {field} changed"));
        }
    }
    let command_view = record
        .get("command")
        .ok_or("claim record lacks source command")?;
    command_action(command_view, text(&record, "action")?)?;
    let plan_view = inspect_unique(backend, dir, "pay-claim-plan", &dir.join("plan.bin"))?;
    require_type(&plan_view, "payClaimSigningPlan")?;
    canonical_matches(&plan_view, "canonicalPlan", &plan)?;
    canonical_matches(&plan_view, "canonicalCommand", &command)?;
    if plan_view.get("command") != Some(command_view)
        || record.get("profile")
            != Some(&json!({"domain":text(&plan_view,"domain")?,
            "semantics":text(&plan_view,"semantics")?}))
    {
        return Err("retained claim source plan/profile differs".into());
    }
    let view = inspect_unique(backend, dir, "pay-claim-ingress", &dir.join("ingress.bin"))?;
    let expected = validate_ingress(&view, &command, &ingress, &signature, command_view)?;
    if record.get("expectedReceipt") != Some(&expected.json()) {
        return Err("retained expected receipt differs from original source ingress".into());
    }
    exchange_outcome(backend, dir, 186, &ingress, &expected)
}

fn execute<B, S, I>(
    backend: &mut B,
    dir: &Path,
    binding: &Value,
    action: &str,
    command: Option<&[u8]>,
    config: &[u8],
    initialize: I,
    sign: &mut S,
) -> Result<Decision>
where
    B: Backend,
    S: FnMut(&[u8], &[u8]) -> Result<Vec<u8>>,
    I: FnOnce(&Path) -> Result<()>,
{
    if fs::symlink_metadata(dir).is_ok() {
        return recover(backend, dir, binding, action, command, config);
    }
    if action == "lookup" {
        return Err("claim operation record does not exist; lookup never creates one".into());
    }
    let command = command.ok_or("new claim action requires --command canonical source binary")?;
    if command.is_empty() || command.len() > 2048 {
        return Err("claim command must contain 1..2048 canonical source bytes".into());
    }
    // Atomic reservation prevents concurrent callers from signing/submitting twice.
    workspace::make_private_dir(dir)?;
    sync_directory_ancestors(dir)?;
    create_private(&dir.join("config.json"), config)?;
    initialize(dir)?;
    create_private(&dir.join("command.bin"), command)?;
    let source = backend.inspect(
        "pay-claim-command",
        &dir.join("command.bin"),
        &dir.join("command.json"),
    )?;
    require_type(&source, "payClaimCommand")?;
    canonical_matches(&source, "canonicalCommand", command)?;
    let command_view = source
        .get("command")
        .ok_or("source command view lacks command")?;
    let signing_key = command_action(command_view, action)?;
    let frame = backend.call(183, command)?;
    let plan = frame_body(&frame, 183, 3072)?;
    create_private(&dir.join("plan.bin"), plan)?;
    let view = backend.inspect(
        "pay-claim-plan",
        &dir.join("plan.bin"),
        &dir.join("plan.json"),
    )?;
    require_type(&view, "payClaimSigningPlan")?;
    canonical_matches(&view, "canonicalPlan", plan)?;
    canonical_matches(&view, "canonicalCommand", command)?;
    if view.get("command") != Some(command_view) {
        return Err("claim plan changed retained command/authority; refusing rebase".into());
    }
    exact_hex(&view, "domain", 32)?;
    exact_hex(&view, "semantics", 32)?;
    let message_hex = text(&view, "signingMessage")?;
    if message_hex.is_empty() || message_hex.len() > 8192 {
        return Err("source claim signing message exceeds bound".into());
    }
    let message = decode_hex(message_hex)?;
    eprintln!(
        "Paid claim action (source command; exact origin and selected terms):\n{}",
        serde_json::to_string_pretty(command_view).map_err(|e| e.to_string())?
    );
    let signature = sign(&signing_key, &message)?;
    if signature.len() != 64 {
        return Err("claim signer returned a non-Ed25519 signature".into());
    }
    create_private(&dir.join("signature.bin"), &signature)?;
    let mut pair = (plan.len() as u32).to_le_bytes().to_vec();
    pair.extend_from_slice(plan);
    pair.extend_from_slice(&signature);
    let frame = backend.call(184, &pair)?;
    let ingress = frame_body(&frame, 184, 4096)?;
    create_private(&dir.join("ingress.bin"), ingress)?;
    let view_ingress = backend.inspect(
        "pay-claim-ingress",
        &dir.join("ingress.bin"),
        &dir.join("ingress.json"),
    )?;
    let expected = validate_ingress(&view_ingress, command, ingress, &signature, command_view)?;
    let record = json!({
        "type":RECORD_TYPE,"binding":binding,"action":action,"command":command_view,
        "originClaimId":command_view.get("action").and_then(|v|v.get("claimId")).cloned().unwrap_or(Value::Null),
        "profile":{"domain":text(&view,"domain")?,"semantics":text(&view,"semantics")?},
        "expectedReceipt":expected.json(),"commandSha256":digest(command),
        "planSha256":digest(plan),"signatureSha256":digest(&signature),
        "ingressSha256":digest(ingress),"configSha256":digest(config)
    });
    // This immutable durable record arms exactly one initial submit. A crash
    // immediately after it, even before the send, is lookup-only recovery.
    retain_json(&dir.join("operation.json"), &record)?;
    sync_retained_call(dir, &dir.join("ingress.bin"))?;
    exchange_outcome(backend, dir, 185, ingress, &expected)
}

fn quote_natural(args: &mut Args, name: &str) -> Result<String> {
    let raw = args
        .required(name)?
        .into_string()
        .map_err(|_| format!("{name} must be decimal"))?;
    let n = raw
        .parse::<u64>()
        .map_err(|_| format!("{name} must be an unsigned 64-bit integer"))?;
    if n.to_string() != raw {
        return Err(format!("{name} must be canonical decimal"));
    }
    Ok(raw)
}

fn validate_quote_command(
    quote: &Value,
    request: &Value,
    inspected: &Value,
    canonical: &[u8],
    identity: &[u8; 32],
) -> Result<()> {
    require_type(quote, "payQuote")?;
    require_type(inspected, "payClaimCommand")?;
    canonical_matches(inspected, "canonicalCommand", canonical)?;
    let signing = quote
        .get("signing")
        .ok_or("quote lacks source signing material")?;
    if text(signing, "kind")? != "claim" || signing.get("command") != inspected.get("command") {
        return Err("quote presentation differs from locally decoded source command".into());
    }
    let command = inspected.get("command").ok_or("source command missing")?;
    let action = command.get("action").ok_or("source action missing")?;
    let owner = quote.get("owner").ok_or("source owner missing")?;
    if text(action, "action")? != "acceptCurrentQuote"
        || exact_hex(action, "identityKey", 32)? != identity
        || exact_hex(owner, "identityKey", 32)? != identity
        || exact_hex(action, "authorizingKey", 32)? != exact_hex(owner, "authorizingKey", 32)?
        || decimal(action, "authorityEpoch")? != decimal(owner, "authorityEpoch")?
        || exact_hex(command, "expectedAuthorityRoot", 32)?
            != exact_hex(quote, "authorityRoot", 32)?
        || exact_hex(command, "expectedPayRoot", 32)? != exact_hex(quote, "payRoot", 32)?
        || exact_hex(action, "claimId", 102)? != exact_hex(request, "claimId", 102)?
    {
        return Err("source claim quote changed exact origin, owner, or authority roots".into());
    }
    for (field, requested) in [
        ("mode", "mode"),
        ("weeks", "weeks"),
        ("minimumStarterCredit", "starter"),
        ("expiryHour", "expiryHour"),
        ("nonce", "nonce"),
    ] {
        if action.get(field) != request.get(requested) {
            return Err(format!("source claim quote changed requested {requested}"));
        }
    }
    exact_hex(action, "pricingCommitment", 32)?;
    let split = quote.get("split").ok_or("source quote split missing")?;
    for field in [
        "amountAtomic",
        "mintedCredit",
        "birthFee",
        "weeks",
        "membershipCredit",
        "creditedRemainder",
        "minimumStarterCredit",
    ] {
        decimal(split, field)?;
    }
    if split.get("weeks") != request.get("weeks")
        || split.get("minimumStarterCredit") != request.get("starter")
        || quote.get("priceReserved") != Some(&Value::Bool(false))
    {
        return Err("source quote split/request contract differs".into());
    }
    Ok(())
}

/// Preparation is deliberately unsigned. An explicit subsequent accept is the
/// user's chosen action; the source remains responsible for price/admission.
fn run_quote(mut args: Args) -> Result<()> {
    let root = absolute(&path(args.required("join-dir")?))?;
    let output = path(args.required("output")?);
    if !output.is_absolute() {
        return Err("--output must be an absolute new file".into());
    }
    let mode = args
        .optional("mode")
        .unwrap_or_else(|| OsString::from("enrol"))
        .into_string()
        .map_err(|_| "mode must be UTF-8")?;
    if !matches!(mode.as_str(), "enrol" | "renew") {
        return Err("quote mode must be enrol or renew".into());
    }
    let weeks = quote_natural(&mut args, "weeks")?;
    let starter = quote_natural(&mut args, "starter-credit")?;
    let expiry = quote_natural(&mut args, "expiry-hour")?;
    let nonce = quote_natural(&mut args, "nonce")?;
    let options = crate::paid_context::Options {
        host: Some(path(args.required("host")?)),
        config: Some(path(args.required("config")?)),
        bootstrap: args
            .optional("bootstrap-url")
            .map(|v| v.into_string().map_err(|_| "URL must be UTF-8"))
            .transpose()?,
        key: None,
        payment_record: args.optional("payment-record").map(path),
    };
    args.finish()?;
    let context = crate::paid_context::fresh_join(
        &root,
        &options,
        crate::paid_context::SigningIntent::Current,
    )?;
    context.pin_transport()?;
    let request = json!({"kind":"claim","claimId":hex(context.origin_claim_id()?),
        "mode":mode,"weeks":weeks,"starter":starter,"expiryHour":expiry,"nonce":nonce});
    let mut sidecar_name = output.as_os_str().to_owned();
    sidecar_name.push(".quote.json");
    let sidecar = PathBuf::from(sidecar_name);
    let mut evidence_name = output.as_os_str().to_owned();
    evidence_name.push(".evidence");
    let record = PathBuf::from(evidence_name);
    for path in [&output, &sidecar, &record] {
        if fs::symlink_metadata(path).is_ok() {
            return Err("quote output/evidence already exists; choose a new output".into());
        }
    }
    workspace::make_private_dir(&record)?;
    create_private(&record.join("config.json"), context.config())?;
    context.retain_origin(&record)?;
    retain_json(&record.join("request.json"), &request)?;
    let endpoint = match context.bootstrap() {
        Some(base) => Endpoint::Bootstrap(base.to_owned()),
        None => Endpoint::Socket(
            context
                .socket()
                .ok_or("quote transport missing")?
                .to_path_buf(),
        ),
    };
    let mut session = Session {
        host: context.host().to_path_buf(),
        config: record.join("config.json"),
        endpoint,
        sha: context.host_sha().to_owned(),
        config_sha: digest(context.config()),
        record: record.clone(),
        metadata_checked: false,
        context: Some(context.clone()),
    };
    let quote = session.quote(&request)?;
    retain_json(&record.join("quote.json"), &quote)?;
    require_type(&quote, "payQuote")?;
    let signing = quote
        .get("signing")
        .ok_or("quote signing material missing")?;
    let raw = text(signing, "canonicalCommand")?;
    if raw.is_empty()
        || raw.len() > 4096
        || raw.len() % 2 != 0
        || !mini_sdk::hex::is_lower(raw)
    {
        return Err("quote canonical command exceeds source bound or is malformed".into());
    }
    let canonical = decode_hex(raw)?;
    let input = record.join("command.bin");
    create_private(&input, &canonical)?;
    let inspected = session.inspect("pay-claim-command", &input, &record.join("command.json"))?;
    validate_quote_command(
        &quote,
        &request,
        &inspected,
        &canonical,
        context.identity_key()?,
    )?;
    let summary = json!({"type":"minidregg-pay-claim-quote-v1","binding":context.binding()?,
        "originClaimId":hex(context.origin_claim_id()?),"request":request,"quote":quote,
        "command":inspected["command"],"canonicalCommandSha256":digest(&canonical),
        "output":utf8_path(&output)?});
    // Publish the sidecar before its command. A crash never leaves an apparently
    // complete unsigned command without the retained terms and origin.
    retain_json(&sidecar, &summary)?;
    sync_directory_ancestors(sidecar.parent().ok_or("quote output parent missing")?)?;
    create_private(&output, &canonical)?;
    sync_retained_call(&record, &output)?;
    println!(
        "{}",
        serde_json::to_string_pretty(&summary).map_err(|e| e.to_string())?
    );
    Ok(())
}

pub(crate) fn run(mut args: Args) -> Result<()> {
    let action = args
        .required("action")?
        .into_string()
        .map_err(|_| "claim action must be UTF-8")?;
    if action == "quote" {
        return run_quote(args);
    }
    if !matches!(action.as_str(), "accept" | "rotate" | "lookup") {
        return Err("pay-claim --action must be quote, accept, rotate, or lookup".into());
    }
    let workspace_dir = args.optional("dir").map(path);
    let join_dir = args.optional("join-dir").map(path);
    let (root, source) = match (workspace_dir, join_dir) {
        (Some(root), None) => (absolute(&root)?, crate::paid_context::Source::Workspace),
        (None, Some(root)) => (absolute(&root)?, crate::paid_context::Source::Join),
        _ => return Err("choose --dir WORKSPACE or --join-dir JOIN-DIR".into()),
    };
    let record = path(args.required("operation-record")?);
    if !record.is_absolute() {
        return Err("--operation-record must be an absolute fresh private directory or retained record directory".into());
    }
    let command_path = args.optional("command").map(path);
    let local_host = args.optional("host").map(path);
    let local_config = args.optional("config").map(path);
    let selected_key = args.optional("key").map(path);
    let payment_record = args.optional("payment-record").map(path);
    let selected_bootstrap = args
        .optional("bootstrap-url")
        .map(|value| {
            value
                .into_string()
                .map_err(|_| "bootstrap URL must be UTF-8")
        })
        .transpose()?;
    args.finish()?;
    if action != "lookup" && command_path.is_none() {
        return Err("accept/rotate requires --command with canonical source binary".into());
    }
    let options = crate::paid_context::Options {
        host: local_host,
        config: local_config,
        bootstrap: selected_bootstrap,
        key: selected_key,
        payment_record,
    };
    // This branch precedes any signing-ready workspace load. Existing records
    // must survive missing/rotated keys and changed current registry authority.
    let context = if action == "lookup" || fs::symlink_metadata(&record).is_ok() {
        crate::paid_context::retained_lookup(&root, source, &record, &options)?
    } else {
        match source {
            crate::paid_context::Source::Workspace => {
                crate::paid_context::fresh_workspace(&root, &options)?
            }
            crate::paid_context::Source::Join => crate::paid_context::fresh_join(
                &root,
                &options,
                if action == "rotate" {
                    crate::paid_context::SigningIntent::Next
                } else {
                    crate::paid_context::SigningIntent::Current
                },
            )?,
        }
    };
    context.pin_transport()?;
    let host = context.host().to_path_buf();
    let config = context.config().to_vec();
    let command = command_path
        .as_ref()
        .map(|p| crate::fsio::read_bounded_or_empty(p, 2048))
        .transpose()?;
    let binding = context.binding()?;
    let endpoint = match context.bootstrap() {
        Some(base) => Endpoint::Bootstrap(base.to_owned()),
        None => Endpoint::Socket(
            context
                .socket()
                .ok_or("paid context lacks transport")?
                .to_path_buf(),
        ),
    };
    let mut session = Session {
        host: host.clone(),
        config: record.join("config.json"),
        endpoint,
        sha: context.host_sha().to_owned(),
        config_sha: digest(&config),
        record: record.clone(),
        metadata_checked: false,
        context: Some(context.clone()),
    };
    let mut signer = |expected: &[u8], message: &[u8]| {
        let signing = read_secret(context.key()?)?;
        if signing.verifying_key().as_bytes().as_slice() != expected {
            return Err(
                "workspace signing key differs from source claim authorizing/successor key".into(),
            );
        }
        Ok(signing.sign(message).to_bytes().to_vec())
    };
    execute(
        &mut session,
        &record,
        &binding,
        &action,
        command.as_deref(),
        &config,
        |dir| {
            write_manifest(dir, &host, &dir.join("config.json"), "pay-claim")?;
            context.retain_origin(dir)
        },
        &mut signer,
    )?
    .finish()
}

#[cfg(test)]
mod tests {
    use super::*;

    struct Scratch(PathBuf);
    impl Scratch {
        fn new() -> Self {
            let root = env::temp_dir().join(format!(
                "mini-claim-{}-{}",
                std::process::id(),
                SystemTime::now()
                    .duration_since(UNIX_EPOCH)
                    .unwrap()
                    .as_nanos()
            ));
            workspace::make_private_dir(&root).unwrap();
            Self(root)
        }
        fn record(&self) -> PathBuf {
            self.0.join("operation")
        }
    }
    impl Drop for Scratch {
        fn drop(&mut self) {
            let _ = fs::remove_dir_all(&self.0);
        }
    }

    fn source_command(rotation: bool) -> Value {
        let action = if rotation {
            json!({"action":"rotatePendingOwner","identityKey":hex(&[1;32]),
                "expectedEpoch":"2","nonce":"8","successorKey":hex(&[8;32]),
                "successorNextKeyDigest":hex(&[6;32])})
        } else {
            json!({"action":"acceptCurrentQuote","identityKey":hex(&[1;32]),
                "authorizingKey":hex(&[7;32]),"authorityEpoch":"2","nonce":"8"})
        };
        json!({"expectedAuthorityRoot":hex(&[2;32]),"expectedPayRoot":hex(&[3;32]),"action":action})
    }

    struct FakeHost {
        dir: PathBuf,
        calls: Vec<u8>,
        inspect_calls: Vec<String>,
        lose_submit: bool,
        stale_plan: bool,
        wrong_plan: bool,
        wrong_signature: bool,
        receipt_event: &'static str,
        outcome: &'static str,
        rotation: bool,
    }
    impl FakeHost {
        fn new(dir: PathBuf) -> Self {
            Self {
                dir,
                calls: vec![],
                inspect_calls: vec![],
                lose_submit: false,
                stale_plan: false,
                wrong_plan: false,
                wrong_signature: false,
                receipt_event: "22",
                outcome: "confirmed",
                rotation: false,
            }
        }
        fn command(&self) -> &'static [u8] {
            if self.rotation {
                b"R"
            } else {
                b"C"
            }
        }
    }
    impl Backend for FakeHost {
        fn call(&mut self, operation: u8, _payload: &[u8]) -> Result<Vec<u8>> {
            self.calls.push(operation);
            let body = match operation {
                183 if self.stale_plan => return Err("fixture source: roots changed".into()),
                183 => b"PLAN".to_vec(),
                184 => b"INGRESS".to_vec(),
                185 | 186 => {
                    // Every external submission/lookup has the completed durable record.
                    let record = workspace::bounded_json(&self.dir.join("operation.json"))?;
                    assert_eq!(record["type"], RECORD_TYPE);
                    assert_eq!(fs::read(self.dir.join("ingress.bin")).unwrap(), b"INGRESS");
                    if operation == 185 && self.lose_submit {
                        return Err("fixture lost reply after receiving".into());
                    }
                    let outcome = if self.outcome == "confirmed" {
                        json!({"type":"confirmed","confirmation":if operation==185 {"installed"} else {"replayed"},
                            "transactionId":"11","eventId":self.receipt_event,"acceptedCount":"1","worldRoot":"33"})
                    } else {
                        json!({"type":self.outcome,"reason":"fixture"})
                    };
                    serde_json::to_vec(&outcome).unwrap()
                }
                _ => panic!("unpermitted operation {operation}"),
            };
            Ok([vec![operation], body].concat())
        }

        fn inspect(&mut self, kind: &str, input: &Path, output: &Path) -> Result<Value> {
            self.inspect_calls.push(kind.to_owned());
            let bytes = fs::read(input).unwrap();
            let command = source_command(self.rotation);
            let value = match kind {
                "pay-claim-command" => json!({"type":"payClaimCommand","command":command,
                    "canonicalCommand":hex(&bytes)}),
                "pay-claim-plan" => {
                    let canonical = if self.wrong_plan {
                        b"OTHER".as_slice()
                    } else {
                        self.command()
                    };
                    json!({"type":"payClaimSigningPlan","command":command,
                        "canonicalCommand":hex(canonical),"canonicalPlan":hex(&bytes),
                        "signingMessage":hex(b"SOURCE-POSSESSION-FRAME"),
                        "domain":hex(&[4;32]),"semantics":hex(&[5;32])})
                }
                "pay-claim-ingress" => json!({"type":"payClaimIngress","command":command,
                    "canonicalCommand":hex(self.command()),"canonicalIngress":hex(&bytes),
                    "signature":hex(&[if self.wrong_signature {10} else {9};64]),
                    "expectedReceipt":{"transactionId":"11","eventId":"22"}}),
                "outcome" => serde_json::from_slice(&bytes).unwrap(),
                _ => panic!("unexpected inspector {kind}"),
            };
            retain_json(output, &value)?;
            Ok(value)
        }
    }

    fn binding() -> Value {
        json!({"workspace":"/fixture","subject":"4","hostSha256":"pinned","socket":"/fixture.sock",
            "configSha256":digest(b"CONFIG")})
    }
    fn initialize(dir: &Path) -> Result<()> {
        retain_json(&dir.join("attempt.json"), &json!({"operation":"pay-claim"}))
    }

    #[test]
    fn lost_reply_recovers_exact_ingress_without_quote_resign_or_resubmit() {
        let scratch = Scratch::new();
        let dir = scratch.record();
        let mut host = FakeHost::new(dir.clone());
        host.lose_submit = true;
        let mut signs = 0;
        let mut signer = |key: &[u8], message: &[u8]| {
            signs += 1;
            assert_eq!(key, &[7; 32]);
            assert_eq!(message, b"SOURCE-POSSESSION-FRAME");
            Ok(vec![9; 64])
        };
        assert!(execute(
            &mut host,
            &dir,
            &binding(),
            "accept",
            Some(b"C"),
            b"CONFIG",
            initialize,
            &mut signer
        )
        .is_err());
        assert!(dir.join("operation.json").is_file());
        host.lose_submit = false;
        let answer = execute(
            &mut host,
            &dir,
            &binding(),
            "accept",
            Some(b"C"),
            b"CONFIG",
            initialize,
            &mut signer,
        )
        .unwrap();
        assert!(matches!(answer, Decision::Confirmed(_)));
        assert_eq!(host.calls, vec![183, 184, 185, 186]);
        assert_eq!(signs, 1);
    }

    #[test]
    fn repeat_changed_command_authority_action_or_pin_refuses_before_host() {
        let scratch = Scratch::new();
        let dir = scratch.record();
        let mut host = FakeHost::new(dir.clone());
        let mut signer = |_: &[u8], _: &[u8]| Ok(vec![9; 64]);
        execute(
            &mut host,
            &dir,
            &binding(),
            "accept",
            Some(b"C"),
            b"CONFIG",
            initialize,
            &mut signer,
        )
        .unwrap();
        let calls = host.calls.clone();
        assert!(execute(
            &mut host,
            &dir,
            &binding(),
            "accept",
            Some(b"NEW-AUTHORITY"),
            b"CONFIG",
            initialize,
            &mut signer
        )
        .is_err());
        assert!(execute(
            &mut host,
            &dir,
            &binding(),
            "rotate",
            Some(b"C"),
            b"CONFIG",
            initialize,
            &mut signer
        )
        .is_err());
        let mut changed = binding();
        changed["hostSha256"] = json!("changed");
        assert!(execute(
            &mut host,
            &dir,
            &changed,
            "lookup",
            None,
            b"CONFIG",
            initialize,
            &mut signer
        )
        .is_err());
        assert!(execute(
            &mut host,
            &dir,
            &binding(),
            "lookup",
            None,
            b"NEW-CONFIG",
            initialize,
            &mut signer
        )
        .is_err());
        assert_eq!(host.calls, calls);
    }

    #[test]
    fn stale_command_is_not_rebased_and_incomplete_record_is_not_restarted() {
        let scratch = Scratch::new();
        let dir = scratch.record();
        let mut host = FakeHost::new(dir.clone());
        host.stale_plan = true;
        let mut signer =
            |_: &[u8], _: &[u8]| -> Result<Vec<u8>> { panic!("stale command must not sign") };
        assert!(execute(
            &mut host,
            &dir,
            &binding(),
            "accept",
            Some(b"C"),
            b"CONFIG",
            initialize,
            &mut signer
        )
        .is_err());
        host.stale_plan = false;
        let error = execute(
            &mut host,
            &dir,
            &binding(),
            "accept",
            Some(b"C"),
            b"CONFIG",
            initialize,
            &mut signer,
        )
        .unwrap_err();
        assert!(error.contains("incomplete"));
        assert_eq!(host.calls, vec![183]);
    }

    #[test]
    fn plan_rebase_and_changed_assembly_refuse_before_submit() {
        for wrong_plan in [true, false] {
            let scratch = Scratch::new();
            let dir = scratch.record();
            let mut host = FakeHost::new(dir.clone());
            host.wrong_plan = wrong_plan;
            host.wrong_signature = !wrong_plan;
            let mut signs = 0;
            let mut signer = |_: &[u8], _: &[u8]| {
                signs += 1;
                Ok(vec![9; 64])
            };
            assert!(execute(
                &mut host,
                &dir,
                &binding(),
                "accept",
                Some(b"C"),
                b"CONFIG",
                initialize,
                &mut signer
            )
            .is_err());
            assert!(!host.calls.contains(&185));
            assert!(!dir.join("operation.json").exists());
            assert_eq!(signs, if wrong_plan { 0 } else { 1 });
        }
    }

    #[test]
    fn confirmation_requires_exact_source_receipt_identity() {
        let expected = ExpectedReceipt {
            transaction: "11".into(),
            event: "22".into(),
        };
        for (tx, event) in [("12", "22"), ("11", "23")] {
            let value = json!({"type":"confirmed","confirmation":"installed","transactionId":tx,
                "eventId":event,"acceptedCount":"1","worldRoot":"33"});
            assert!(Decision::source(value, &expected).is_err());
        }
        assert!(Decision::source(json!({"type":"confirmed"}), &expected).is_err());
        assert!(Decision::source(json!({"type":"success"}), &expected).is_err());
    }

    #[test]
    fn absent_uncertain_contention_and_unavailable_are_never_confirmation() {
        let expected = ExpectedReceipt {
            transaction: "11".into(),
            event: "22".into(),
        };
        for kind in [
            "absent",
            "uncertain",
            "contention",
            "unavailable",
            "refused",
        ] {
            let answer =
                Decision::source(json!({"type":kind,"reason":"fixture"}), &expected).unwrap();
            assert!(!matches!(answer, Decision::Confirmed(_)));
        }
        let scratch = Scratch::new();
        let dir = scratch.record();
        let mut host = FakeHost::new(dir.clone());
        let mut signer = |_: &[u8], _: &[u8]| Ok(vec![9; 64]);
        execute(
            &mut host,
            &dir,
            &binding(),
            "accept",
            Some(b"C"),
            b"CONFIG",
            initialize,
            &mut signer,
        )
        .unwrap();
        host.outcome = "absent";
        let mut never_sign =
            |_: &[u8], _: &[u8]| -> Result<Vec<u8>> { panic!("lookup never signs") };
        assert!(matches!(
            execute(
                &mut host,
                &dir,
                &binding(),
                "lookup",
                None,
                b"CONFIG",
                initialize,
                &mut never_sign
            )
            .unwrap(),
            Decision::Absent(_)
        ));
        assert_eq!(host.calls, vec![183, 184, 185, 186]);
    }

    #[test]
    fn pending_rotation_signs_successor_and_recovery_needs_no_key() {
        let scratch = Scratch::new();
        let dir = scratch.record();
        let mut host = FakeHost::new(dir.clone());
        host.rotation = true;
        let mut signer = |key: &[u8], _: &[u8]| {
            assert_eq!(key, &[8; 32]);
            Ok(vec![9; 64])
        };
        assert!(matches!(
            execute(
                &mut host,
                &dir,
                &binding(),
                "rotate",
                Some(b"R"),
                b"CONFIG",
                initialize,
                &mut signer
            )
            .unwrap(),
            Decision::Confirmed(_)
        ));
        let mut no_key =
            |_: &[u8], _: &[u8]| -> Result<Vec<u8>> { Err("original secret gone".into()) };
        assert!(matches!(
            execute(
                &mut host,
                &dir,
                &binding(),
                "lookup",
                None,
                b"CONFIG",
                initialize,
                &mut no_key
            )
            .unwrap(),
            Decision::Confirmed(_)
        ));
        assert_eq!(host.calls, vec![183, 184, 185, 186]);
    }

    #[test]
    fn damaged_retained_ingress_and_missing_record_never_submit() {
        let scratch = Scratch::new();
        let dir = scratch.record();
        let mut host = FakeHost::new(dir.clone());
        let mut signer = |_: &[u8], _: &[u8]| Ok(vec![9; 64]);
        assert!(execute(
            &mut host,
            &dir,
            &binding(),
            "lookup",
            None,
            b"CONFIG",
            initialize,
            &mut signer
        )
        .is_err());
        assert!(host.calls.is_empty());
        assert!(!dir.exists());
        execute(
            &mut host,
            &dir,
            &binding(),
            "accept",
            Some(b"C"),
            b"CONFIG",
            initialize,
            &mut signer,
        )
        .unwrap();
        fs::write(dir.join("ingress.bin"), b"CHANGED").unwrap();
        assert!(execute(
            &mut host,
            &dir,
            &binding(),
            "lookup",
            None,
            b"CONFIG",
            initialize,
            &mut signer
        )
        .is_err());
        assert_eq!(host.calls, vec![183, 184, 185]);
    }

    #[test]
    fn https_routes_and_wire_reply_are_closed_and_bounded() {
        for operation in 183..=186 {
            let (_, field) = claim_route(operation).unwrap();
            let value = json!({"type":"payClaimWire","operation":operation.to_string(),field:"00"});
            assert_eq!(
                decode_claim_wire(operation, &serde_json::to_vec(&value).unwrap()).unwrap(),
                vec![operation, 0]
            );
            let mut wrong = value.clone();
            wrong["operation"] = json!("187");
            assert!(decode_claim_wire(operation, &serde_json::to_vec(&wrong).unwrap()).is_err());
            let mut extra = value.clone();
            extra["genericExec"] = json!("no");
            assert!(decode_claim_wire(operation, &serde_json::to_vec(&extra).unwrap()).is_err());
            for text in ["", "0", "GG", "Aa"] {
                let mut invalid = value.clone();
                invalid[field] = json!(text);
                assert!(
                    decode_claim_wire(operation, &serde_json::to_vec(&invalid).unwrap()).is_err()
                );
            }
            let mut maximum = value.clone();
            maximum[field] = json!("00".repeat(4096));
            assert_eq!(
                decode_claim_wire(operation, &serde_json::to_vec(&maximum).unwrap())
                    .unwrap()
                    .len(),
                4097
            );
            maximum[field] = json!("00".repeat(4097));
            assert!(decode_claim_wire(operation, &serde_json::to_vec(&maximum).unwrap()).is_err());
        }
        for op in [0, 117, 121, 182, 187, 255] {
            assert!(claim_route(op).is_err());
        }
        assert!(decode_claim_wire(183, &vec![b' '; 16385]).is_err());
        for url in [
            "https://node.test/mini/v2",
            "http://127.0.0.1:8080/mini/v2",
            "http://[::1]:8080/mini/v2",
        ] {
            assert!(bootstrap_url(url).is_ok());
        }
        for url in [
            "http://node.test/mini/v2",
            "https://node.test/mini/v1",
            "https://user@node.test/mini/v2",
            "https://node.test/mini/v2?x",
            "https://node.test/mini/v2#x",
            "https://node.test/mini/v2/claim/submit",
        ] {
            assert!(bootstrap_url(url).is_err());
        }
    }

    #[test]
    fn metadata_requires_exact_local_host_domain_semantics_and_v2_contract() {
        let profile = json!({"domain":"12","semantics":"34"});
        let metadata = json!({"type":"minidregg-enrollment-bootstrap-v2","hostSha256":"abc",
            "domain":"12","semantics":34,"memoVersions":["enrol:v2"],"quoteType":"payQuote",
            "statusType":"payStatus","expiryClock":"processingChainHour","recovery":"acceptCurrentQuote"});
        validate_metadata(&metadata, &profile, "abc").unwrap();
        for field in [
            "type",
            "hostSha256",
            "domain",
            "semantics",
            "quoteType",
            "statusType",
            "expiryClock",
            "recovery",
        ] {
            let mut wrong = metadata.clone();
            wrong[field] = json!("changed");
            assert!(
                validate_metadata(&wrong, &profile, "abc").is_err(),
                "{field}"
            );
        }
        let mut wrong = metadata.clone();
        wrong["memoVersions"] = json!(["enrol:v1"]);
        assert!(validate_metadata(&wrong, &profile, "abc").is_err());
    }

    #[test]
    fn local_inspection_executes_pinned_host_and_rejects_config_change() {
        use std::os::unix::fs::PermissionsExt;
        for mutate in [false, true] {
            let scratch = Scratch::new();
            let host = scratch.0.join("Host");
            let config = scratch.0.join("config");
            let input = scratch.0.join("input");
            let output = scratch.0.join("output");
            fs::write(&config, b"CONFIG").unwrap();
            fs::write(&input, b"canonical").unwrap();
            let script = if mutate {
                "#!/bin/sh\nprintf '{\"type\":\"fixtureSource\"}' > \"$5\"\nprintf 'changed' > \"$1\"\n"
            } else {
                "#!/bin/sh\n[ \"$2\" = inspect ] && [ \"$3\" = fixture-kind ] || exit 3\nprintf '{\"type\":\"fixtureSource\"}' > \"$5\"\n"
            };
            fs::write(&host, script).unwrap();
            fs::set_permissions(&host, fs::Permissions::from_mode(0o700)).unwrap();
            let sha = host_image_sha256(&host).unwrap();
            let mut session = Session {
                host,
                config,
                endpoint: Endpoint::Socket(scratch.0.join("never-opened.sock")),
                sha,
                config_sha: digest(b"CONFIG"),
                record: scratch.0.clone(),
                metadata_checked: false,
                context: None,
            };
            let result = session.inspect("fixture-kind", &input, &output);
            if mutate {
                assert!(result.unwrap_err().contains("config differs"));
            } else {
                assert_eq!(result.unwrap()["type"], "fixtureSource");
            }
        }
    }
    #[test]
    fn plan_profile_binding_is_exact_including_full_width_digests() {
        let profile = json!({"domain":"12","semantics":"115792089237316195423570985008687907853269984665640564039457584007913129639935"});
        let mut domain = vec![0; 32];
        domain[0] = 12;
        let plan = json!({"domain":hex(&domain),"semantics":hex(&[255;32])});
        validate_plan_profile(&plan, &profile).unwrap();
        let mut wrong = plan.clone();
        wrong["domain"] = json!(hex(&[1; 32]));
        assert!(validate_plan_profile(&wrong, &profile).is_err());
        let mut wrong = plan.clone();
        wrong["semantics"] = json!(hex(&[0; 32]));
        assert!(validate_plan_profile(&wrong, &profile).is_err());
        let overflow = json!({"domain":"115792089237316195423570985008687907853269984665640564039457584007913129639936"});
        assert!(profile_digest(&overflow, "domain").is_err());
        assert!(profile_digest(&json!({"domain":"012"}), "domain").is_err());
        assert!(profile_digest(&json!({"domain":12.5}), "domain").is_err());
    }
    #[test]
    fn cli_retained_lookup_survives_missing_key_and_changed_authority() {
        let output = Command::new(env::current_exe().unwrap())
            .args([
                "--exact",
                "pay_claim::tests::cli_retained_lookup_child",
                "--ignored",
                "--nocapture",
            ])
            .output()
            .unwrap();
        assert!(
            output.status.success(),
            "{}",
            String::from_utf8_lossy(&output.stderr)
        );
        assert!(String::from_utf8_lossy(&output.stdout).contains("EXACT_LOOKUP_ONLY"));
    }

    // Separate process isolates global transport pins while exercising run(),
    // the real typed loader, local Host invocations and Unix wire transport.
    #[test]
    #[ignore]
    fn cli_retained_lookup_child() {
        use std::os::unix::fs::PermissionsExt;
        use std::os::unix::net::UnixListener;
        let scratch = Scratch::new();
        let root = &scratch.0;
        for name in ["refs", "attempts", "sources", "proposals"] {
            workspace::make_private_dir(&root.join(name)).unwrap();
        }
        let dir = scratch.record();
        let config = br#"{"domain":"4","expectedSeed":"77"}"#;
        create_private(&root.join("public.config"), config).unwrap();
        let host = root.join("Host");
        let script = format!(
            r#"#!/bin/sh
printf '%s %s\n' "$2" "$3" >> '{root}/local-calls'
case "$2:$3" in
 profile:) cat '{root}/profile.json' ;;
 inspect:pay-claim-plan) cp '{dir}/plan.json' "$5" ;;
 inspect:pay-claim-ingress) cp '{dir}/ingress.json' "$5" ;;
 inspect:outcome) cp "$4" "$5" ;;
 *) exit 73 ;;
esac
"#,
            root = root.display(),
            dir = dir.display()
        );
        create_private(&host, script.as_bytes()).unwrap();
        fs::set_permissions(&host, fs::Permissions::from_mode(0o700)).unwrap();
        retain_json(&root.join("profile.json"),&json!({
            "domain":"1816346497840254045859937019744124044757176230049263749638550337379029484548", "semantics":"2270433122300317557324921274680155055946470287561579687048187921723786855685"
        })).unwrap();
        let sha = host_image_sha256(&host).unwrap();
        let socket = root.join("lookup.sock");
        retain_json(
            &root.join("workspace.json"),
            &json!({
                "type":"minidregg-participant-workspace-v1","subject":"4",
                "config":root.join("public.config"),"host":host,"hostSha256":sha,
                "socket":socket,"key":root.join("missing-private-key"),
                "prerotation":true,"nextPublicKey":hex(&[222;32])
            }),
        )
        .unwrap();
        let binding = json!({"workspace":root,"subject":"4","hostSha256":sha,
            "socket":transport::pinned_address(&socket).unwrap(),"bootstrapUrl":null,
            "configSha256":digest(config),"genesisExpectedSeed":"77"});
        let mut backend = FakeHost::new(dir.clone());
        let mut signer = |_: &[u8], _: &[u8]| Ok(vec![9; 64]);
        execute(
            &mut backend,
            &dir,
            &binding,
            "accept",
            Some(b"C"),
            config,
            initialize,
            &mut signer,
        )
        .unwrap();
        let listener = UnixListener::bind(&socket).unwrap();
        listener.set_nonblocking(true).unwrap();
        let expected_sha = decode_hex(&sha).unwrap();
        let thread = std::thread::spawn(move || {
            let until = std::time::Instant::now() + std::time::Duration::from_secs(5);
            let mut stream = loop {
                match listener.accept() {
                    Ok((s, _)) => break s,
                    Err(e) if e.kind() == std::io::ErrorKind::WouldBlock => {
                        assert!(
                            std::time::Instant::now() < until,
                            "lookup never reached socket"
                        );
                        std::thread::sleep(std::time::Duration::from_millis(10));
                    }
                    Err(e) => panic!("{e}"),
                }
            };
            stream
                .set_read_timeout(Some(std::time::Duration::from_secs(2)))
                .unwrap();
            let frame = transport::read_frame(&mut stream).unwrap().unwrap();
            assert_eq!(frame[0], 2);
            let len = u32::from_le_bytes(frame[1..5].try_into().unwrap()) as usize;
            assert_eq!(&frame[5..5 + len], config);
            assert_eq!(&frame[5 + len..37 + len], &expected_sha);
            // Any current registry query, re-plan, or re-submit fails here.
            assert_eq!(frame[37 + len], 186);
            assert_eq!(&frame[38 + len..], b"INGRESS");
            let reply = json!({"type":"confirmed","confirmation":"replayed","transactionId":"11",
                "eventId":"22","acceptedCount":"1","worldRoot":"33"});
            transport::write_frame(
                &mut stream,
                &[vec![186], serde_json::to_vec(&reply).unwrap()].concat(),
            )
            .unwrap();
        });
        let args = Args {
            command: OsString::from("pay-claim"),
            values: vec![
                (OsString::from("--action"), OsString::from("lookup")),
                (OsString::from("--dir"), root.as_os_str().to_owned()),
                (
                    OsString::from("--operation-record"),
                    dir.as_os_str().to_owned(),
                ),
            ],
        };
        run(args).unwrap();
        thread.join().unwrap();
        assert!(!root.join("missing-private-key").exists());
        let calls = fs::read_to_string(root.join("local-calls")).unwrap();
        assert!(calls.contains("inspect pay-claim-plan"));
        assert!(calls.contains("inspect pay-claim-ingress"));
        assert!(!calls.contains("author"));
        // A changed genesis/config pin must refuse before any second network use.
        fs::write(
            root.join("public.config"),
            br#"{"domain":"4","expectedSeed":"78"}"#,
        )
        .unwrap();
        assert!(crate::paid_context::retained_lookup(
            root,
            crate::paid_context::Source::Workspace,
            &dir,
            &crate::paid_context::Options::default()
        )
        .is_err());
        println!("EXACT_LOOKUP_ONLY");
    }

    #[test]
    fn quote_origin_owner_terms_and_source_roots_are_bound_before_publication() {
        let request = json!({"kind":"claim","claimId":hex(&[9;102]),"mode":"enrol",
            "weeks":"2","starter":"347","expiryHour":"100","nonce":"8"});
        let action = json!({"action":"acceptCurrentQuote","claimId":request["claimId"],
            "identityKey":hex(&[1;32]),"authorizingKey":hex(&[7;32]),"authorityEpoch":"2",
            "pricingCommitment":hex(&[6;32]),"mode":"enrol","weeks":"2",
            "minimumStarterCredit":"347","expiryHour":"100","nonce":"8"});
        let command = json!({"expectedAuthorityRoot":hex(&[2;32]),"expectedPayRoot":hex(&[3;32]),"action":action});
        let inspected = json!({"type":"payClaimCommand","command":command,"canonicalCommand":hex(b"CANONICAL")});
        let quote = json!({"type":"payQuote","authorityRoot":hex(&[2;32]),"payRoot":hex(&[3;32]),"priceReserved":false,
            "owner":{"identityKey":hex(&[1;32]),"authorizingKey":hex(&[7;32]),"authorityEpoch":"2"},
            "split":{"amountAtomic":"12","mintedCredit":"10000","birthFee":"100","weeks":"2",
                "membershipCredit":"200","creditedRemainder":"9700","minimumStarterCredit":"347"},
            "signing":{"kind":"claim","command":command,"canonicalCommand":hex(b"CANONICAL")}});
        validate_quote_command(&quote, &request, &inspected, b"CANONICAL", &[1; 32]).unwrap();
        // Large remainder is intentionally valid: v2 purchases exact weeks.
        for field in ["claimId", "weeks", "starter", "expiryHour", "nonce", "mode"] {
            let mut changed = request.clone();
            changed[field] = json!("changed");
            assert!(
                validate_quote_command(&quote, &changed, &inspected, b"CANONICAL", &[1; 32])
                    .is_err(),
                "{field}"
            );
        }
        for field in ["identityKey", "authorizingKey", "authorityEpoch"] {
            let mut changed = quote.clone();
            changed["owner"][field] = json!("changed");
            assert!(
                validate_quote_command(&changed, &request, &inspected, b"CANONICAL", &[1; 32])
                    .is_err(),
                "{field}"
            );
        }
        let mut changed = quote.clone();
        changed["authorityRoot"] = json!(hex(&[8; 32]));
        assert!(
            validate_quote_command(&changed, &request, &inspected, b"CANONICAL", &[1; 32]).is_err()
        );
        assert!(validate_quote_command(&quote, &request, &inspected, b"OTHER", &[1; 32]).is_err());
    }
}
