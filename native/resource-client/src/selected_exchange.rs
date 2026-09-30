//! One explicitly selected public Mini content version through fn to another Mini.
//! The pinned Lean Host owns selection, wire bytes, source and recipient admission.
//! This module only joins its existing commands and retains exact recovery state.
use super::*;
use sha2::{Digest, Sha256};
use std::os::unix::fs::{DirBuilderExt, PermissionsExt};

const FORMAT: &str = "minidregg-selected-exchange-v1";
const MAX_FILE: usize = 1_500_000;

fn digest(bytes: &[u8]) -> String {
    hex(&Sha256::digest(bytes))
}

fn digest_file(path: &Path) -> Result<String> {
    let mut file = File::open(path).map_err(|e| format!("{}: {e}", path.display()))?;
    let mut hash = Sha256::new();
    let mut buffer = [0u8; 64 * 1024];
    loop {
        let count = file.read(&mut buffer).map_err(|e| e.to_string())?;
        if count == 0 {
            return Ok(hex(&hash.finalize()));
        }
        hash.update(&buffer[..count]);
    }
}

fn bounded(path: &Path, max: usize) -> Result<Vec<u8>> {
    let file = File::open(path).map_err(|e| format!("{}: {e}", path.display()))?;
    let mut bytes = Vec::new();
    file.take((max + 1) as u64)
        .read_to_end(&mut bytes)
        .map_err(|e| e.to_string())?;
    if bytes.is_empty() || bytes.len() > max {
        return Err(format!(
            "{} is empty or exceeds {max} bytes",
            path.display()
        ));
    }
    Ok(bytes)
}

fn read_json(path: &Path) -> Result<Value> {
    serde_json::from_slice(&bounded(path, MAX_FILE)?)
        .map_err(|e| format!("{}: {e}", path.display()))
}

fn field<'a>(value: &'a Value, name: &str) -> Result<&'a str> {
    value
        .get(name)
        .and_then(Value::as_str)
        .filter(|v| !v.is_empty())
        .ok_or_else(|| format!("selected exchange lacks {name}"))
}

fn decimal<'a>(value: &'a Value, name: &str) -> Result<&'a str> {
    let value = field(value, name)?;
    if value.len() > 80
        || !value.bytes().all(|b| b.is_ascii_digit())
        || (value.len() > 1 && value.starts_with('0'))
    {
        return Err(format!("selected exchange {name} is not canonical decimal"));
    }
    Ok(value)
}

fn named_path(value: &Value, name: &str) -> Result<PathBuf> {
    let path = PathBuf::from(field(value, name)?);
    if !path.is_absolute() {
        return Err(format!("{name} must be absolute"));
    }
    Ok(path)
}

fn put_json(path: &Path, value: &Value) -> Result<()> {
    let mut bytes = serde_json::to_vec_pretty(value).map_err(|e| e.to_string())?;
    bytes.push(b'\n');
    create_private(path, &bytes)?;
    sync_directory_ancestors(path.parent().ok_or("exchange output has no parent")?)
}

fn host(config: &Value) -> Result<PathBuf> {
    named_path(config, "host")
}
fn source_config(config: &Value) -> Result<PathBuf> {
    named_path(config, "sourceConfig")
}
fn recipient_config(config: &Value) -> Result<PathBuf> {
    named_path(config, "recipientConfig")
}

fn host_call(config: &Value, recipient: bool, command: &str, args: &[&OsStr]) -> Result<()> {
    let host = host(config)?;
    let config = if recipient {
        recipient_config(config)?
    } else {
        source_config(config)?
    };
    let mut argv = Vec::with_capacity(args.len() + 1);
    argv.push(OsStr::new(command));
    argv.extend_from_slice(args);
    process(&host, &config, &argv)?;
    Ok(())
}

fn file_pins(config: &Value) -> Result<Value> {
    let mut pins = serde_json::Map::new();
    for key in [
        "host",
        "sourceConfig",
        "recipientConfig",
        "sourceSignedQuery",
        "selectedPayload",
        "privatePostConfig",
        "fnBinary",
        "fnRuntimeImage",
        "fnScope",
        "recipientQueryIntent",
        "ownerKey",
        "gatewayKey",
        "recipientQueryKey",
    ] {
        let path = named_path(config, key)?;
        pins.insert(key.to_owned(), Value::String(digest_file(&path)?));
    }
    Ok(Value::Object(pins))
}

fn pin(config_path: &Path, config: &Value, state: &Path, first: bool) -> Result<()> {
    let current = json!({"format":FORMAT,
        "contractSha256":digest(&bounded(config_path, 65_536)?),
        "clientSha256":digest_file(&env::current_exe().map_err(|e| e.to_string())?)?,
        "files":file_pins(config)?});
    let path = state.join("pin.json");
    if first {
        put_json(&path, &current)
    } else if read_json(&path)? == current {
        Ok(())
    } else {
        Err("selected exchange contract or pinned input changed".into())
    }
}

fn private_state(state: &Path) -> Result<()> {
    let meta = fs::symlink_metadata(state).map_err(|e| e.to_string())?;
    if !meta.file_type().is_dir() || meta.permissions().mode() & 0o077 != 0 {
        return Err("selected exchange state must be a private, nonsymlink directory".into());
    }
    Ok(())
}

fn checked_receipt(value: &Value) -> Result<()> {
    if value.get("type").and_then(Value::as_str) != Some("confirmed")
        || !matches!(
            value.get("confirmation").and_then(Value::as_str),
            Some("installed" | "replayed")
        )
    {
        return Err("latest Mini result is not a confirmed receipt".into());
    }
    for key in ["transactionId", "eventId", "acceptedCount", "worldRoot"] {
        decimal(value, key)?;
    }
    Ok(())
}

fn receipt_fields(value: &Value) -> Result<()> {
    for key in ["transactionId", "eventId", "acceptedCount", "worldRoot"] {
        decimal(value, key)?;
    }
    Ok(())
}

fn recipient_receipt(state: &Path) -> Result<Value> {
    let directory = state.join("recipient-attempt");
    let mut outcomes = fs::read_dir(directory)
        .map_err(|e| e.to_string())?
        .map(|entry| entry.map(|e| e.path()).map_err(|e| e.to_string()))
        .collect::<Result<Vec<_>>>()?;
    outcomes.retain(|p| {
        p.file_name()
            .and_then(|v| v.to_str())
            .map(|s| s.starts_with("request-") && s.ends_with(".outcome.json"))
            .unwrap_or(false)
    });
    outcomes.sort();
    let mut original: Option<Value> = None;
    let mut latest = None;
    for path in outcomes {
        let value = read_json(&path)?;
        if checked_receipt(&value).is_ok() {
            if let Some(first) = &original {
                for key in ["transactionId", "eventId", "acceptedCount", "worldRoot"] {
                    if first.get(key) != value.get(key) {
                        return Err("recipient lookup changed original Mini receipt".into());
                    }
                }
            } else {
                original = Some(value.clone());
            }
        }
        latest = Some(value);
    }
    let latest = latest.ok_or("recipient has no retained Mini outcome")?;
    checked_receipt(&latest)?;
    let original = original.ok_or("recipient has no confirmed original receipt")?;
    Ok(original)
}

fn selected_poll(state: &Path) -> Result<PathBuf> {
    let name =
        String::from_utf8(bounded(&state.join("poll-selected"), 32)?).map_err(|e| e.to_string())?;
    let name = name.trim();
    if name.len() != 9
        || !name.starts_with("poll-")
        || !name[5..].bytes().all(|b| b.is_ascii_digit())
    {
        return Err("retained selected poll name is invalid".into());
    }
    let poll = state.join(name);
    private_state(&poll)?;
    let report = read_json(&poll.join("fn-poll.json"))?;
    if report.get("type").and_then(Value::as_str) != Some("selected-release-fn-poll-v1")
        || report.get("status").and_then(Value::as_str) != Some("candidate-unacknowledged")
        || bounded(&poll.join("source.eml"), MAX_FILE)?
            != bounded(&state.join("article.eml"), MAX_FILE)?
        || bounded(&poll.join("received-packet.bin"), MAX_FILE)?
            != bounded(&state.join("packet.bin"), MAX_FILE)?
    {
        return Err("fn poll did not project the exact selected owner packet".into());
    }
    Ok(poll)
}

fn prepared(state: &Path) -> Result<()> {
    let value = read_json(&state.join("prepared.json"))?;
    if value.get("type").and_then(Value::as_str) != Some("minidregg-selected-exchange-prepared-v1")
        || value.get("ownerPacketSha256").and_then(Value::as_str)
            != Some(digest(&bounded(&state.join("packet.bin"), MAX_FILE)?).as_str())
        || value.get("articleSha256").and_then(Value::as_str)
            != Some(digest(&bounded(&state.join("article.eml"), MAX_FILE)?).as_str())
    {
        return Err("retained selected owner packet or article changed".into());
    }
    Ok(())
}

fn next_name(state: &Path, prefix: &str, suffix: &str) -> Result<PathBuf> {
    for number in 1..=8 {
        let path = state.join(format!("{prefix}-{number:04}{suffix}"));
        if !path.exists() {
            return Ok(path);
        }
    }
    Err(format!("{prefix} reconciliation attempt bound exhausted"))
}

fn prepare(config: &Value, state: &Path) -> Result<()> {
    let query = named_path(config, "sourceSignedQuery")?;
    let payload = named_path(config, "selectedPayload")?;
    if digest(&bounded(&payload, 1_000_000)?) != field(config, "selectedPayloadSha256")? {
        return Err("selected payload digest differs from contract".into());
    }
    host_call(
        config,
        false,
        "query",
        &[query.as_os_str(), state.join("source-view.bin").as_os_str()],
    )?;
    let view = inspect(
        &host(config)?,
        &source_config(config)?,
        "view-resource",
        &state.join("source-view.bin"),
        &state.join("source-view.json"),
    )?;
    let payload_hex = hex(&bounded(&payload, 1_000_000)?);
    let atom = decimal(config, "sourceAtom")?;
    let entries = view
        .pointer("/cell/entries")
        .and_then(Value::as_array)
        .ok_or("signed current source view has no content entries")?;
    if entries
        .iter()
        .filter(|entry| {
            entry.get("type").and_then(Value::as_str) == Some("atom")
                && entry.get("id").and_then(Value::as_str) == Some(atom)
                && entry.get("payload").and_then(Value::as_str) == Some(payload_hex.as_str())
                && entry
                    .get("tombstonedAt")
                    .map(Value::is_null)
                    .unwrap_or(true)
        })
        .count()
        != 1
    {
        return Err("signed current Mini view does not contain exact selected atom bytes".into());
    }
    let mut request = serde_json::Map::new();
    request.insert(
        "signedQueryHex".into(),
        Value::String(hex(&bounded(&query, 65_536)?)),
    );
    for key in [
        "atom",
        "destinationDomain",
        "destinationSemantics",
        "destinationTarget",
        "group",
        "messageId",
        "policyRoot",
        "keysetRoot",
        "epoch",
        "ownerSubject",
        "ownerNonce",
        "expiresAt",
        "from",
        "date",
        "subject",
    ] {
        let value = if key == "atom" {
            atom
        } else if ["group", "messageId", "from", "date", "subject"].contains(&key) {
            field(config, key)?
        } else {
            decimal(config, key)?
        };
        request.insert(key.to_owned(), Value::String(value.to_owned()));
    }
    put_json(&state.join("request.json"), &Value::Object(request))?;
    host_call(
        config,
        false,
        "selected-release-prepare",
        &[
            state.join("request.json").as_os_str(),
            state.join("preimage.bin").as_os_str(),
        ],
    )?;
    // The same signed query must still name the exact view after authoring.
    host_call(
        config,
        false,
        "query",
        &[
            query.as_os_str(),
            state.join("source-view-after.bin").as_os_str(),
        ],
    )?;
    if bounded(&state.join("source-view.bin"), MAX_FILE)?
        != bounded(&state.join("source-view-after.bin"), MAX_FILE)?
    {
        return Err("selected Mini source changed during authoring".into());
    }
    selected_release_sign(
        &host(config)?,
        &source_config(config)?,
        &state.join("preimage.bin"),
        &named_path(config, "ownerKey")?,
        &state.join("signature.bin"),
    )?;
    host_call(
        config,
        false,
        "selected-release-assemble",
        &[
            state.join("preimage.bin").as_os_str(),
            state.join("signature.bin").as_os_str(),
            OsStr::new(field(config, "from")?),
            OsStr::new(field(config, "date")?),
            OsStr::new(field(config, "subject")?),
            state.join("packet.bin").as_os_str(),
            state.join("article.eml").as_os_str(),
        ],
    )?;
    if bounded(&state.join("article.eml"), 1_048_576).is_err() {
        return Err("selected article exceeds explicitly supported fn 1 MiB profile".into());
    }
    selected_publisher::sign_source(
        &host(config)?,
        &source_config(config)?,
        &state.join("packet.bin"),
        decimal(config, "sourceDelegateCapability")?,
        &named_path(config, "ownerKey")?,
        &state.join("source-sign"),
    )?;
    host_call(
        config,
        false,
        "selected-release-source-check",
        &[
            state.join("source-sign/ingress.bin").as_os_str(),
            state.join("article.eml").as_os_str(),
        ],
    )?;
    put_json(
        &state.join("prepared.json"),
        &json!({"type":"minidregg-selected-exchange-prepared-v1",
        "sourceAtom":atom,"selectedPayloadSha256":digest(&bounded(&payload, 1_000_000)?),
        "ownerPacketSha256":digest(&bounded(&state.join("packet.bin"), MAX_FILE)?),
        "articleSha256":digest(&bounded(&state.join("article.eml"), MAX_FILE)?)}),
    )?;
    Ok(())
}

fn publish(config: &Value, state: &Path) -> Result<()> {
    prepared(state)?;
    selected_publisher::publish(
        &host(config)?,
        &source_config(config)?,
        &state.join("source-sign/ingress.bin"),
        &state.join("article.eml"),
        &state.join("source-publish"),
        &named_path(config, "privatePostConfig")?,
    )?;
    let post = read_json(&state.join("source-publish/fn-post-result.json"))?;
    if !matches!(
        post.get("status").and_then(Value::as_str),
        Some("accepted" | "already-stored")
    ) {
        return Err("fn POST lacks retained acceptance; Mini recipient remains untouched".into());
    }
    Ok(())
}

fn receive(config: &Value, state: &Path) -> Result<()> {
    prepared(state)?;
    let post = read_json(&state.join("source-publish/fn-post-result.json"))?;
    if !matches!(
        post.get("status").and_then(Value::as_str),
        Some("accepted" | "already-stored")
    ) {
        return Err("fn POST has no retained acceptance".into());
    }
    let recipient = state.join("recipient-attempt");
    if !recipient.exists() && !state.join("poll-selected").exists() {
        let poll = next_name(state, "poll", "")?;
        fs::DirBuilder::new()
            .mode(0o700)
            .create(&poll)
            .map_err(|e| e.to_string())?;
        host_call(
            config,
            true,
            "selected-release-fn-poll",
            &[
                named_path(config, "fnBinary")?.as_os_str(),
                named_path(config, "fnScope")?.as_os_str(),
                named_path(config, "fnControl")?.as_os_str(),
                OsStr::new(decimal(config, "recipientCapability")?),
                OsStr::new(decimal(config, "recipientTargetRoot")?),
                poll.join("cursor.fncu").as_os_str(),
                poll.join("report.fn-e").as_os_str(),
                poll.join("source.eml").as_os_str(),
                poll.join("received-packet.bin").as_os_str(),
                poll.join("received-ingress.bin").as_os_str(),
                poll.join("fn-poll.json").as_os_str(),
            ],
        )?;
        if bounded(&poll.join("source.eml"), MAX_FILE)?
            != bounded(&state.join("article.eml"), MAX_FILE)?
        {
            return Err("fn projected carrier differs from exact selected article".into());
        }
        let name = poll
            .file_name()
            .ok_or("poll path has no name")?
            .to_string_lossy();
        create_private(&state.join("poll-selected"), name.as_bytes())?;
    }
    let poll = selected_poll(state)?;
    if recipient.exists() {
        selected_release::lookup(&recipient, None)?;
    } else {
        selected_release::submit(
            &host(config)?,
            &recipient_config(config)?,
            &named_path(config, "recipientSocket")?,
            &poll.join("received-ingress.bin"),
            &recipient,
        )?;
    }
    recipient_receipt(state)?;
    Ok(())
}

fn transport_article(state: &Path) -> Result<PathBuf> {
    let transport = state.join("transport");
    let name =
        String::from_utf8(bounded(&transport.join("selected"), 32)?).map_err(|e| e.to_string())?;
    if name.len() != 16
        || !name.starts_with("legacy-poll-")
        || !name[12..].bytes().all(|b| b.is_ascii_digit())
    {
        return Err("retained legacy poll name is invalid".into());
    }
    let poll = transport.join(name);
    private_state(&poll)?;
    let report = read_json(&poll.join("result.json"))?;
    if report.get("type").and_then(Value::as_str) != Some("selected-release-fn-legacy-poll-v1")
        || report.get("mode").and_then(Value::as_str) != Some("fn-r-transport-only")
        || report.get("status").and_then(Value::as_str) != Some("candidate-unacknowledged")
    {
        return Err("retained fn-r poll has no selected transport candidate".into());
    }
    let stored = bounded(&poll.join("stored.eml"), 1_516_384)?;
    let authored = bounded(&state.join("article.eml"), 1_048_576)?;
    if !stored.ends_with(&authored) {
        return Err("fn-r stored article does not carry exact selected owner article".into());
    }
    if bounded(&poll.join("packet.bin"), MAX_FILE)? != bounded(&state.join("packet.bin"), MAX_FILE)?
    {
        return Err("fn-r projected owner packet differs from prepared packet".into());
    }
    let evidence = read_json(&transport.join("retrieval.json"))?;
    if evidence.get("type").and_then(Value::as_str)
        != Some("minidregg-selected-exchange-transport-v1")
        || evidence.get("storedSha256").and_then(Value::as_str) != Some(digest(&stored).as_str())
        || evidence.get("authoredSha256").and_then(Value::as_str)
            != Some(digest(&authored).as_str())
    {
        return Err("retained fn-r transport evidence changed".into());
    }
    Ok(poll)
}

fn receive_transport(config: &Value, state: &Path) -> Result<()> {
    prepared(state)?;
    let post = read_json(&state.join("source-publish/fn-post-result.json"))?;
    if !matches!(
        post.get("status").and_then(Value::as_str),
        Some("accepted" | "already-stored")
    ) {
        return Err("fn POST has no retained acceptance".into());
    }
    let transport = state.join("transport");
    if !transport.exists() {
        fs::DirBuilder::new()
            .mode(0o700)
            .create(&transport)
            .map_err(|e| e.to_string())?;
        sync_directory_ancestors(state)?;
    }
    private_state(&transport)?;
    if !transport.join("selected").exists() {
        let poll = next_name(&transport, "legacy-poll", "")?;
        fs::DirBuilder::new()
            .mode(0o700)
            .create(&poll)
            .map_err(|e| e.to_string())?;
        host_call(
            config,
            true,
            "selected-release-fn-legacy-poll",
            &[
                named_path(config, "fnBinary")?.as_os_str(),
                named_path(config, "fnScope")?.as_os_str(),
                named_path(config, "fnControl")?.as_os_str(),
                state.join("article.eml").as_os_str(),
                OsStr::new(decimal(config, "recipientCapability")?),
                OsStr::new(decimal(config, "recipientTargetRoot")?),
                poll.join("cursor.fncu").as_os_str(),
                poll.join("report.fn-r").as_os_str(),
                poll.join("stored.eml").as_os_str(),
                poll.join("packet.bin").as_os_str(),
                poll.join("ingress.bin").as_os_str(),
                poll.join("result.json").as_os_str(),
            ],
        )?;
        if bounded(&poll.join("packet.bin"), MAX_FILE)?
            != bounded(&state.join("packet.bin"), MAX_FILE)?
        {
            return Err("fn-r projected packet differs from selected owner packet".into());
        }
        let stored = bounded(&poll.join("stored.eml"), 1_516_384)?;
        let authored = bounded(&state.join("article.eml"), 1_048_576)?;
        if !stored.ends_with(&authored) {
            return Err("fn-r stored article differs from selected owner article".into());
        }
        let name = poll
            .file_name()
            .ok_or("legacy poll has no name")?
            .to_string_lossy();
        create_private(&transport.join("selected"), name.as_bytes())?;
        sync_directory_ancestors(&transport)?;
    }
    if !transport.join("retrieval.json").exists() {
        let name = String::from_utf8(bounded(&transport.join("selected"), 32)?)
            .map_err(|e| e.to_string())?;
        if name.len() != 16 || !name.starts_with("legacy-poll-") {
            return Err("retained legacy poll name is invalid".into());
        }
        let poll = transport.join(&name);
        let stored = bounded(&poll.join("stored.eml"), 1_516_384)?;
        let authored = bounded(&state.join("article.eml"), 1_048_576)?;
        if !stored.ends_with(&authored)
            || bounded(&poll.join("packet.bin"), MAX_FILE)?
                != bounded(&state.join("packet.bin"), MAX_FILE)?
        {
            return Err("fn-r retained article or packet differs from selected release".into());
        }
        put_json(
            &transport.join("retrieval.json"),
            &json!({"type":"minidregg-selected-exchange-transport-v1",
                "mode":"fn-r-transport-only", "poll":name,
                "messageId":field(config,"messageId")?,
                "storedSha256":digest(&stored),
                "authoredSha256":digest(&authored),
                "claim":"authenticated local fn poll and ACL2 fn-r decode; no fn-e verdict or cursor ACK"}),
        )?;
    }
    let poll = transport_article(state)?;
    let recipient = state.join("recipient-attempt");
    if recipient.exists() {
        selected_release::lookup(&recipient, None)?;
    } else {
        selected_release::submit(
            &host(config)?,
            &recipient_config(config)?,
            &named_path(config, "recipientSocket")?,
            &poll.join("ingress.bin"),
            &recipient,
        )?;
    }
    recipient_receipt(state)?;
    Ok(())
}

fn cover_plan(config: &Value, state: &Path) -> Result<()> {
    prepared(state)?;
    let poll = selected_poll(state)?;
    let receipt = recipient_receipt(state)?;
    fn_frontier::plan(
        &host(config)?,
        &recipient_config(config)?,
        &named_path(config, "recipientOperatorSocket")?,
        "selected",
        decimal(&receipt, "transactionId")?,
        &state.join("frontier"),
    )?;
    if bounded(&state.join("frontier/source.eml"), MAX_FILE)?
        != bounded(&poll.join("source.eml"), MAX_FILE)?
    {
        return Err("frontier plan source differs from selected poll".into());
    }
    Ok(())
}

fn cover_advance(config: &Value, state: &Path, approval: &Path) -> Result<()> {
    prepared(state)?;
    selected_poll(state)?;
    recipient_receipt(state)?;
    fn_frontier::advance(
        &state.join("frontier"),
        &named_path(config, "gatewayKey")?,
        approval,
    )
}

fn ack(config: &Value, state: &Path) -> Result<()> {
    prepared(state)?;
    let poll = selected_poll(state)?;
    let receipt = recipient_receipt(state)?;
    let frontier = read_json(&state.join("frontier/confirmed.json"))?;
    receipt_fields(&frontier)?;
    let output = next_name(state, "ack", ".json")?;
    host_call(
        config,
        true,
        "selected-release-fn-ack",
        &[
            poll.join("cursor.fncu").as_os_str(),
            poll.join("report.fn-e").as_os_str(),
            OsStr::new(decimal(&receipt, "transactionId")?),
            state.join("frontier/ingress.bin").as_os_str(),
            output.as_os_str(),
        ],
    )?;
    let result = read_json(&output)?;
    if !matches!(
        result.get("fnAck").and_then(Value::as_str),
        Some("durable-accepted" | "covered-by-durable-frontier")
    ) {
        return Err("fn cursor ACK did not confirm exact Mini coverage".into());
    }
    Ok(())
}

fn verify(config: &Value, state: &Path, transport_only: bool) -> Result<()> {
    prepared(state)?;
    let receipt = recipient_receipt(state)?;
    if transport_only {
        transport_article(state)?;
    } else {
        let _poll = selected_poll(state)?;
        let mut acked = false;
        for entry in fs::read_dir(state).map_err(|e| e.to_string())? {
            let path = entry.map_err(|e| e.to_string())?.path();
            if path
                .file_name()
                .and_then(|s| s.to_str())
                .map(|s| s.starts_with("ack-") && s.ends_with(".json"))
                .unwrap_or(false)
            {
                let value = read_json(&path)?;
                acked |= matches!(
                    value.get("fnAck").and_then(Value::as_str),
                    Some("durable-accepted" | "covered-by-durable-frontier")
                );
            }
        }
        if !acked {
            return Err("no retained fn ACK over accepted Mini event13/event17".into());
        }
    }
    let intent = read_json(&named_path(config, "recipientQueryIntent")?)?;
    let target = decimal(config, "destinationTarget")?;
    let capability = decimal(config, "recipientCapability")?;
    if intent.pointer("/purpose/type").and_then(Value::as_str) != Some("query")
        || intent.pointer("/purpose/kind").and_then(Value::as_str) != Some("object")
        || intent.pointer("/purpose/target").and_then(Value::as_str) != Some(target)
        || intent.pointer("/purpose/view").and_then(Value::as_str) != Some("resource")
        || !intent
            .get("grants")
            .and_then(Value::as_array)
            .map(|g| {
                g.iter().any(|entry| {
                    entry.get("kind").and_then(Value::as_str) == Some("object")
                        && entry.get("target").and_then(Value::as_str) == Some(target)
                        && entry.get("capability").and_then(Value::as_str) == Some(capability)
                })
            })
            .unwrap_or(false)
    {
        return Err("recipient query does not name exact target and capability".into());
    }
    let output = next_name(state, "readback", "")?;
    query(
        &host(config)?,
        &recipient_config(config)?,
        &named_path(config, "recipientQueryIntent")?,
        OsStr::new("intent"),
        &named_path(config, "recipientQueryKey")?,
        "view-resource",
        &output,
    )?;
    let view = read_json(&output.join("view.json"))?;
    let packet = hex(&bounded(&state.join("packet.bin"), MAX_FILE)?);
    let atom = decimal(&receipt, "transactionId")?;
    let entries = view
        .pointer("/cell/entries")
        .and_then(Value::as_array)
        .ok_or("signed recipient view has no content entries")?;
    if entries
        .iter()
        .filter(|entry| {
            entry.get("type").and_then(Value::as_str) == Some("atom")
                && entry.get("id").and_then(Value::as_str) == Some(atom)
                && entry.pointer("/kind/type").and_then(Value::as_str) == Some("inlineObject")
                && entry.pointer("/kind/schema").and_then(Value::as_str) == Some("11")
                && entry
                    .get("tombstonedAt")
                    .map(Value::is_null)
                    .unwrap_or(true)
                && entry.get("payload").and_then(Value::as_str) == Some(packet.as_str())
        })
        .count()
        != 1
    {
        return Err("signed recipient view lacks exact event13 owner packet".into());
    }
    put_json(
        &output.join("selected-exchange.json"),
        &json!({
        "type":"minidregg-selected-exchange-verified-v1", "recipientReceipt":receipt,
        "claim":"selected public content bytes admitted at recipient; no app install implied",
        "transportOnly":transport_only}),
    )?;
    Ok(())
}

fn status(state: &Path) -> Result<()> {
    let present = |name: &str| state.join(name).exists();
    let prepared_result = if present("prepared.json") {
        Some(prepared(state).is_ok())
    } else {
        None
    };
    let receipt = if present("recipient-attempt") {
        recipient_receipt(state).ok()
    } else {
        None
    };
    print_json(&json!({
        "type":"minidregg-selected-exchange-status-v1",
        "pinned":present("pin.json"),
        "preparationComplete":prepared_result,
        "sourcePublicationAttempt":present("source-publish/source-submit-attempt.json"),
        "fnPostAttempt":present("source-publish/fn-post-attempt.json"),
        "fnPostOutcome":present("source-publish/fn-post-result.json"),
        "recipientAttempt":present("recipient-attempt/attempt.json"),
        "recipientConfirmedReceipt":receipt,
        "transportArticle":present("transport/retrieval.json"),
        "frontierAttempt":present("frontier/plan-attempt.json"),
        "frontierConfirmed":present("frontier/confirmed.json"),
        "meaning":"retained local evidence only; not a fresh authorization or fn delivery claim"
    }))
}

pub(super) fn run(
    phase: &str,
    contract: &Path,
    state: &Path,
    approval: Option<&Path>,
) -> Result<()> {
    if SOCKET.get().is_some() {
        return Err("selected exchange uses its pinned direct Host and explicit sockets".into());
    }
    let contract = absolute(contract)?;
    let state = absolute(state)?;
    let config = read_json(&contract)?;
    if field(&config, "type")? != FORMAT
        || field(&config, "releaseProfile")? != "public-peerable-v2"
    {
        return Err("unsupported selected exchange contract or release profile".into());
    }
    if !matches!(
        phase,
        "prepare"
            | "status"
            | "publish"
            | "receive"
            | "receive-transport"
            | "cover-plan"
            | "cover-advance"
            | "ack"
            | "verify"
            | "verify-transport"
    ) {
        return Err(
            "expected prepare|status|publish|receive|receive-transport|cover-plan|cover-advance|ack|verify|verify-transport".into(),
        );
    }
    if approval.is_some() && phase != "cover-advance" {
        return Err("approval applies only to cover-advance".into());
    }
    if phase == "prepare" {
        if state.exists() {
            return Err("selected exchange state already exists".into());
        }
        fs::DirBuilder::new()
            .mode(0o700)
            .create(&state)
            .map_err(|e| e.to_string())?;
        sync_directory_ancestors(&state)?;
        let _owner = transport::service_lock(&state.join("selected-exchange.lock"))?;
        pin(&contract, &config, &state, true)?;
        prepare(&config, &state)
    } else {
        private_state(&state)?;
        let _owner = transport::service_lock(&state.join("selected-exchange.lock"))?;
        if state.join("pin.json").exists() {
            pin(&contract, &config, &state, false)?;
        } else if phase != "status" {
            return Err("preparation stopped before contract pin; inspect retained state".into());
        }
        match phase {
            "status" => status(&state),
            "publish" => publish(&config, &state),
            "receive" => receive(&config, &state),
            "receive-transport" => receive_transport(&config, &state),
            "cover-plan" => cover_plan(&config, &state),
            "cover-advance" => cover_advance(
                &config,
                &state,
                approval.ok_or("cover-advance requires an exact private approval")?,
            ),
            "ack" => ack(&config, &state),
            "verify" => verify(&config, &state, false),
            "verify-transport" => verify(&config, &state, true),
            _ => unreachable!("phase validated before entering state"),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn scratch() -> PathBuf {
        let path = std::env::temp_dir().join(format!(
            "mini-selected-exchange-{}-{}",
            std::process::id(),
            SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        ));
        fs::DirBuilder::new().mode(0o700).create(&path).unwrap();
        path
    }

    #[test]
    fn latest_recipient_lookup_must_confirm_original_receipt() {
        let state = scratch();
        let attempt = state.join("recipient-attempt");
        fs::DirBuilder::new().mode(0o700).create(&attempt).unwrap();
        let confirmed = json!({"type":"confirmed","confirmation":"installed",
            "transactionId":"2","eventId":"3","acceptedCount":"4","worldRoot":"5"});
        put_json(&attempt.join("request-0000.outcome.json"), &confirmed).unwrap();
        assert_eq!(recipient_receipt(&state).unwrap(), confirmed);
        put_json(
            &attempt.join("request-0001.outcome.json"),
            &json!({"type":"absent"}),
        )
        .unwrap();
        assert!(recipient_receipt(&state).is_err());
        fs::remove_file(attempt.join("request-0001.outcome.json")).unwrap();
        let conflicting = json!({"type":"confirmed","confirmation":"replayed",
            "transactionId":"2","eventId":"3","acceptedCount":"4","worldRoot":"6"});
        put_json(&attempt.join("request-0001.outcome.json"), &conflicting).unwrap();
        assert!(recipient_receipt(&state)
            .unwrap_err()
            .contains("changed original"));
        fs::remove_dir_all(state).unwrap();
    }

    #[test]
    fn contract_version_and_public_profile_refuse_before_mutation() {
        let state = scratch();
        let contract = state.join("contract.json");
        let output = state.join("new-state");
        put_json(
            &contract,
            &json!({"type":FORMAT,"releaseProfile":"encrypted-v1"}),
        )
        .unwrap();
        assert!(run("prepare", &contract, &output, None)
            .unwrap_err()
            .contains("unsupported"));
        assert!(!output.exists());
        fs::remove_dir_all(state).unwrap();
    }

    #[test]
    fn retained_article_mutation_refuses_before_any_publication() {
        let state = scratch();
        create_private(&state.join("packet.bin"), b"packet").unwrap();
        create_private(&state.join("article.eml"), b"article").unwrap();
        put_json(
            &state.join("prepared.json"),
            &json!({
            "type":"minidregg-selected-exchange-prepared-v1",
            "ownerPacketSha256":digest(b"packet"),
            "articleSha256":digest(b"article")}),
        )
        .unwrap();
        prepared(&state).unwrap();
        fs::write(state.join("article.eml"), b"changed").unwrap();
        assert!(prepared(&state).unwrap_err().contains("changed"));
        fs::remove_dir_all(state).unwrap();
    }

    #[test]
    fn exchange_lock_refuses_a_concurrent_phase() {
        let state = scratch();
        let lock = state.join("selected-exchange.lock");
        let first = transport::service_lock(&lock).unwrap();
        assert!(transport::service_lock(&lock)
            .unwrap_err()
            .contains("another service owns"));
        drop(first);
        transport::service_lock(&lock).unwrap();
        fs::remove_dir_all(state).unwrap();
    }

    #[test]
    fn unknown_phase_refuses_without_creating_attempt_state() {
        let state = scratch();
        let contract = state.join("contract.json");
        let output = state.join("new-state");
        put_json(
            &contract,
            &json!({"type":FORMAT,"releaseProfile":"public-peerable-v2"}),
        )
        .unwrap();
        assert!(run("resubmit", &contract, &output, None)
            .unwrap_err()
            .contains("expected"));
        assert!(!output.exists());
        fs::remove_dir_all(state).unwrap();
    }
}
