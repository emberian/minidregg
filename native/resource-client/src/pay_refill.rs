//! `mini pay refill`: the owner of a Book account funds an AgentGrain purse
//! (PAY P6). The Host authors every byte (`author pay-refill`), decides the
//! joint turn and names the signing header (op113); Rust retains each exact
//! frame in a fresh directory, signs the header with the owner's key, and
//! submits once (op115). A retained directory is never resubmitted: an
//! uncertain submission is resolved only by the receipt-only lookup (op116).
use crate::agent_reserve::{bounded, private_bytes};
use crate::*;
use serde_json::{json, Value};
use std::os::unix::fs::DirBuilderExt;

const LIMIT: usize = transport::HOST_MAX_FRAME - 1;

fn reply(frame: &[u8], operation: u8) -> Result<&[u8]> {
    match frame {
        [actual, body @ ..] if *actual == operation && !body.is_empty() => Ok(body),
        _ => Err(format!("pay refill: Host refused op{operation}; exact frame retained")),
    }
}

fn retain(directory: &Path, name: &str, bytes: &[u8]) -> Result<()> {
    create_private(&directory.join(name), bytes)
}

fn invoke(ctx: &Context, stem: &str, operation: u8, payload: &[u8]) -> Result<Vec<u8>> {
    let frame = session_invoke(&ctx.host, &ctx.socket, &ctx.config, operation, payload)?;
    retain(&ctx.dir, &format!("{stem}.frame"), &frame)?;
    Ok(reply(&frame, operation)?.to_vec())
}

fn kinded(kind: &str, body: &[u8]) -> Result<Vec<u8>> {
    let length: u16 = kind.len().try_into().map_err(|_| "Host kind too long")?;
    let mut payload = length.to_le_bytes().to_vec();
    payload.extend_from_slice(kind.as_bytes());
    payload.extend_from_slice(body);
    Ok(payload)
}

fn inspect(ctx: &Context, stem: &str, kind: &str, bytes: &[u8]) -> Result<Value> {
    let body = invoke(ctx, stem, 8, &kinded(kind, bytes)?)?;
    serde_json::from_slice(&body).map_err(|error| format!("invalid {kind} inspection: {error}"))
}

fn pair(first: &[u8], second: &[u8]) -> Result<Vec<u8>> {
    let length: u32 = first.len().try_into().map_err(|_| "pair exceeds u32")?;
    let mut bytes = length.to_le_bytes().to_vec();
    bytes.extend_from_slice(first);
    bytes.extend_from_slice(second);
    if first.is_empty() || second.is_empty() || bytes.len() >= transport::HOST_MAX_FRAME {
        return Err("pay refill pair exceeds Host bound or has an empty component".into());
    }
    Ok(bytes)
}

fn decimal(args: &mut Args, name: &str) -> Result<String> {
    canonical(args.required(name)?, name)
}

fn canonical(value: OsString, name: &str) -> Result<String> {
    let value = value
        .into_string()
        .map_err(|_| format!("--{name} must be UTF-8"))?;
    if value.is_empty()
        || value.len() > 80
        || !value.bytes().all(|byte| byte.is_ascii_digit())
        || (value.len() > 1 && value.starts_with('0'))
    {
        return Err(format!("--{name} must be a canonical decimal"));
    }
    Ok(value)
}

fn nonce() -> Result<String> {
    let mut bytes = [0u8; 16];
    File::open("/dev/urandom")
        .and_then(|mut file| file.read_exact(&mut bytes))
        .map_err(|error| format!("cannot obtain refill nonce: {error}"))?;
    Ok(u128::from_be_bytes(bytes).to_string())
}

struct Context {
    host: PathBuf,
    config: PathBuf,
    socket: PathBuf,
    dir: PathBuf,
}

fn outcome(ctx: &Context, stem: &str, body: &[u8]) -> Result<()> {
    let view = inspect(ctx, &format!("{stem}-inspect"), "outcome", body)?;
    retain(&ctx.dir, &format!("{stem}.json"), view.to_string().as_bytes())?;
    print_json(&view)
}

fn submit(mut args: Args) -> Result<()> {
    let host = path(args.required("host")?);
    let config = path(args.required("config")?);
    let key_path = path(args.required("key")?);
    let dir = path(args.required("dir")?);
    let subject = decimal(&mut args, "subject")?;
    let capability = decimal(&mut args, "capability")?;
    let account = decimal(&mut args, "account")?;
    let task = decimal(&mut args, "task")?;
    let amount = decimal(&mut args, "amount")?;
    let gain = match args.optional("gain") {
        Some(value) => canonical(value, "gain")?,
        None => amount.clone(),
    };
    args.finish()?;
    let socket = SOCKET.get().ok_or("pay refill requires --socket")?.clone();
    fs::DirBuilder::new()
        .mode(0o700)
        .create(&dir)
        .map_err(|error| format!("pay refill --dir must be new ({}): {error}", dir.display()))?;
    let ctx = Context { host, config, socket, dir };
    let mut raw: [u8; 32] = private_bytes(&key_path, 32)?
        .try_into()
        .map_err(|_| "refill key must contain exactly 32 raw bytes")?;
    let signing = SigningKey::from_bytes(&raw);
    raw.fill(0);

    let view_bytes = invoke(&ctx, "pay-view", 107, &[])?;
    let view = inspect(&ctx, "pay-view-inspect", "pay-view", &view_bytes)?;
    let authority_root = view
        .get("authorityRoot")
        .and_then(Value::as_str)
        .ok_or("pay view lacks authorityRoot")?;
    let command = json!({"subject":subject,"capability":capability,"account":account,
        "task":task,"amount":amount,"gain":gain,"nonce":nonce()?,
        "expectedAuthorityRoot":authority_root});
    let command_bytes = invoke(&ctx, "command", 7, &kinded("pay-refill", command.to_string().as_bytes())?)?;
    retain(&ctx.dir, "command.bin", &command_bytes)?;
    let plan = invoke(&ctx, "plan", 113, &command_bytes)?;
    retain(&ctx.dir, "plan.bin", &plan)?;
    let plan_view = inspect(&ctx, "plan-inspect", "pay-plan", &plan)?;
    if plan_view.pointer("/command/canonical").and_then(Value::as_str) != Some(&hex(&command_bytes)) {
        return Err("refill plan does not carry the authored command".into());
    }
    let header = plan_view
        .pointer("/header/canonical")
        .and_then(Value::as_str)
        .ok_or("refill plan lacks a canonical header")?;
    let header = crate::decode_hex(header)?;
    let signature = signing.sign(&header).to_bytes();
    let ingress = invoke(&ctx, "ingress", 114, &pair(&plan, &signature)?)?;
    retain(&ctx.dir, "ingress.bin", &ingress)?;
    let result = invoke(&ctx, "submit", 115, &ingress)?;
    outcome(&ctx, "outcome", &result)
}

fn lookup(mut args: Args) -> Result<()> {
    let host = path(args.required("host")?);
    let config = path(args.required("config")?);
    let dir = path(args.required("dir")?);
    args.finish()?;
    let socket = SOCKET.get().ok_or("pay refill requires --socket")?.clone();
    let ingress = bounded(&dir.join("ingress.bin"), LIMIT)?;
    let stem = format!("lookup-{}", nonce()?);
    let ctx = Context { host, config, socket, dir };
    let result = invoke(&ctx, &stem, 116, &ingress)?;
    outcome(&ctx, &stem, &result)
}

/// `mini pay refill --mode submit|lookup ...`, reached from `pay::run`.
pub(crate) fn run(mut args: Args) -> Result<()> {
    let mode = args
        .required("mode")?
        .into_string()
        .map_err(|_| "pay refill --mode must be UTF-8")?;
    match mode.as_str() {
        "submit" => submit(args),
        "lookup" => lookup(args),
        _ => Err("pay refill --mode must be submit or lookup".into()),
    }
}
