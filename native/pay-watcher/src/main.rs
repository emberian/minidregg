//! pay-watcher --config FILE --out DIR [--rpc-fixture DIR]... [--spool DIR]
//!
//! Live mode (no `--rpc-fixture`): endpoints come from `PAY_RPC_ENDPOINTS` (whitespace- or
//! comma-separated URLs; docs/PAY.md §3.5 keeps them in `/etc/mini/pay/rpc.env`), each reached with
//! `/usr/bin/curl` through a private spool (`--spool`, default `--out`). Fixture mode: each
//! `--rpc-fixture DIR` is one endpoint answered from files (see `transport::fixture_key`).
//!
//! Writes `DIR/observations.json` and `DIR/events.json` (each atomically), then, when the
//! config has an `enrol` row, the advanced enrollment cursor to `enrol.cursorFile` (read at
//! start; absent = page the whole history). Prints one summary line on stdout; every event is
//! also one line on stderr.
//!
//! Exit: 0 = written, nothing refused; 3 = written, at least one refusal (the observations
//! that were emitted are still sound); 2 = nothing written (usage, config, receipts, or no
//! agreed tip). With --durable-ticks, errors may leave a recovery record; never delete it.
//! --ack-tick ID archives a settled pending tick; see README.md.
//! --quarantine-tick ID --reason TEXT moves an undecidable pending tick aside (the operator's
//! verb when `mini pay observe` cannot settle it); nothing it held is lost, see README.md.

use std::io::Write;
use std::os::fd::AsRawFd;
use std::os::unix::fs::OpenOptionsExt;
use serde_json::{json, Value};
use std::path::{Path, PathBuf};
use std::process::ExitCode;

use minidregg_pay_watcher::transport::{CurlTransport, FixtureTransport, Transport};
use minidregg_pay_watcher::{cursor_json, load_cursor, load_receipts, run, Config, Cursor};

struct Args {
    config: PathBuf,
    out: PathBuf,
    fixtures: Vec<PathBuf>,
    spool: Option<PathBuf>,
    durable: bool,
    ack_tick: Option<String>,
    quarantine: Option<(String, String)>,
}

fn parse_args() -> Result<Args, String> {
    let mut config = None;
    let mut out = None;
    let mut fixtures = Vec::new();
    let mut spool = None;
    let mut durable = false;
    let mut ack_tick = None;
    let mut quarantine_tick = None;
    let mut reason = None;
    let mut it = std::env::args_os().skip(1);
    while let Some(arg) = it.next() {
        let mut value = || {
            it.next()
                .map(PathBuf::from)
                .ok_or_else(|| format!("{} needs a value", arg.to_string_lossy()))
        };
        match arg.to_str() {
            Some("--config") => config = Some(value()?),
            Some("--out") => out = Some(value()?),
            Some("--rpc-fixture") => fixtures.push(value()?),
            Some("--spool") => spool = Some(value()?),
            Some("--durable-ticks") => durable = true,
            Some("--ack-tick") => ack_tick = Some(value()?.to_str().ok_or("tick ID must be UTF-8")?.to_owned()),
            Some("--quarantine-tick") => quarantine_tick = Some(value()?.to_str().ok_or("tick ID must be UTF-8")?.to_owned()),
            Some("--reason") => reason = Some(value()?.to_str().ok_or("--reason must be UTF-8")?.to_owned()),
            _ => return Err(format!("unknown argument {}", arg.to_string_lossy())),
        }
    }
    let quarantine = match (quarantine_tick, reason) {
        (Some(id), Some(reason)) => {
            if reason.is_empty() || reason.len() > 200 || reason.chars().any(char::is_control) {
                return Err("--reason is 1..200 characters with no control character".into());
            }
            Some((id, reason))
        }
        (None, None) => None,
        _ => return Err("--quarantine-tick and --reason go together".into()),
    };
    if quarantine.is_some() && ack_tick.is_some() {
        return Err("--ack-tick and --quarantine-tick are separate acts".into());
    }
    Ok(Args {
        quarantine,
        config: config.ok_or("--config is required")?,
        out: out.ok_or("--out is required")?,
        fixtures,
        spool,
        durable,
        ack_tick,
    })
}

fn write_atomic(dir: &Path, name: &str, bytes: &[u8]) -> Result<(), String> {
    let tmp = dir.join(format!(".{name}.tmp"));
    let dest = dir.join(name);
    let mut file = std::fs::File::create(&tmp).map_err(|e| format!("{}: {e}", tmp.display()))?;
    file.write_all(bytes)
        .map_err(|e| format!("{}: {e}", tmp.display()))?;
    std::fs::rename(&tmp, &dest).map_err(|e| format!("{}: {e}", dest.display()))?;
    Ok(())
}



fn config_identity(cfg: &Config) -> Value {
    json!({"mint":cfg.asset.mint.to_vec(),"tokenProgram":cfg.asset.token_program.to_vec(),
        "receiptsDir":cfg.receipts_dir,"enrolIndex":cfg.enrol.as_ref().map(|e|e.index)})
}

fn durable_lock(out: &Path) -> Result<std::fs::File, String> {
    let file = std::fs::OpenOptions::new().read(true).write(true).create(true)
        .mode(0o600).custom_flags(libc::O_NOFOLLOW).open(out.join(".tick.lock"))
        .map_err(|e| format!("tick lock: {e}"))?;
    if unsafe { libc::flock(file.as_raw_fd(), libc::LOCK_EX | libc::LOCK_NB) } != 0 {
        return Err("another watcher is using this durable tick directory".into());
    }
    Ok(file)
}

fn tick_id(value: &str) -> Result<u64, String> {
    let id: u64 = value.parse().map_err(|_| "invalid tick ID")?;
    if id == 0 || format!("{id:020}") != value { return Err("invalid tick ID".into()); }
    Ok(id)
}

fn read_tick(path: &Path) -> Result<Value, String> {
    let metadata = std::fs::symlink_metadata(path).map_err(|e| format!("{}: {e}", path.display()))?;
    if !metadata.file_type().is_file() || metadata.len() > 64 * 1024 * 1024 {
        return Err("pending tick must be a bounded regular file".into());
    }
    let value: Value = serde_json::from_slice(&std::fs::read(path).map_err(|e| e.to_string())?)
        .map_err(|e| format!("tick JSON: {e}"))?;
    if value["type"] != "minidregg-pay-watcher-tick-v1"
        || !value["observations"]["observations"].is_array()
        || !value["observations"]["tip"].is_object() || !value["events"].is_array()
        || !matches!(value["exit"].as_u64(), Some(0 | 3)) {
        return Err("invalid durable tick".into());
    }
    tick_id(value["id"].as_str().ok_or("tick lacks ID")?)?;
    Ok(value)
}

fn next_tick_id(out: &Path) -> Result<String, String> {
    let archive = out.join("ticks");
    std::fs::create_dir_all(&archive).map_err(|e| e.to_string())?;
    let mut highest = 0;
    // A quarantined tick keeps its ID: the next one never reuses it.
    for dir in [archive, out.join("quarantine")] {
        if !dir.exists() { continue; }
        for entry in std::fs::read_dir(dir).map_err(|e| e.to_string())? {
            let entry = entry.map_err(|e| e.to_string())?;
            let name = entry.file_name().into_string().map_err(|_| "invalid tick archive name")?;
            if let Some(id) = name.strip_suffix(".json") { highest = highest.max(tick_id(id)?); }
        }
    }
    Ok(format!("{:020}", highest.checked_add(1).ok_or("tick ID exhausted")?))
}

/// Pending is durable before any cursor advance. It contains both cursor
/// states and the complete audit events; reloading it needs no RPC answers.
fn publish_tick(out: &Path, cfg: &Config, tick: &Value) -> Result<ExitCode, String> {
    if tick["identity"] != config_identity(cfg) {
        return Err("pending tick asset, observer receipts or enrollment identity changed".into());
    }
    let cursor_path = cfg.enrol.as_ref().map(|e| &e.cursor_file);
    match cursor_path {
        Some(path) => {
            if tick["cursor"]["path"].as_str() != path.to_str() { return Err("pending tick cursor path changed".into()); }
            let current: Value = serde_json::from_slice(&cursor_json(&load_cursor(path)?)).map_err(|e| e.to_string())?;
            if current != tick["cursor"]["before"] && current != tick["cursor"]["after"] {
                return Err("cursor diverged from pending tick; refusing rollback".into());
            }
        }
        None if !tick["cursor"].is_null() => return Err("pending tick enrollment configuration changed".into()),
        None => {}
    }
    write_atomic(out, "observations.json", &serde_json::to_vec_pretty(&tick["observations"]).map_err(|e| e.to_string())?)?;
    write_atomic(out, "events.json", &serde_json::to_vec_pretty(&tick["events"]).map_err(|e| e.to_string())?)?;
    if let Some(path) = cursor_path {
        let (dir, name) = split_path(path)?;
        write_atomic(dir, name, &serde_json::to_vec_pretty(&tick["cursor"]["after"]).map_err(|e| e.to_string())?)?;
    }
    for event in tick["events"].as_array().unwrap() { eprintln!("{event}"); }
    println!("tick={} observations={} events={} tip.slot={}", tick["id"].as_str().unwrap(),
        tick["observations"]["observations"].as_array().unwrap().len(),
        tick["events"].as_array().unwrap().len(), tick["observations"]["tip"]["slot"]);
    Ok(ExitCode::from(tick["exit"].as_u64().unwrap() as u8))
}

/// The service acknowledges only after its exact observer has settled. Rename
/// retains the complete immutable tick once; repeated acknowledgements are safe.
fn acknowledge_tick(out: &Path, id: &str) -> Result<ExitCode, String> {
    tick_id(id)?;
    let pending = out.join("pending.json");
    let archive = out.join("ticks");
    std::fs::create_dir_all(&archive).map_err(|e| e.to_string())?;
    let destination = archive.join(format!("{id}.json"));
    if !pending.exists() {
        let old = read_tick(&destination)?;
        if old["id"] != id { return Err("archived tick ID differs".into()); }
        return Ok(ExitCode::SUCCESS);
    }
    let value = read_tick(&pending)?;
    if value["id"] != id { return Err("acknowledgement names a different pending tick".into()); }
    if destination.exists() { return Err("tick archive collision; preserving both records".into()); }
    std::fs::rename(&pending, &destination).map_err(|e| e.to_string())?;
    println!("archived tick={id}");
    Ok(ExitCode::SUCCESS)
}

/// The operator's way out of a pending tick `mini pay observe` cannot settle (it exits 4, or
/// anything outside 0/3, every tick, and every later payment waits behind it). The bundle is
/// moved whole to `quarantine/ID.json` with the operator's reason and the time; nothing is
/// deleted. Nothing is lost either: the enrollment cursor (written when the tick was
/// published) only ever passes settled listings, and every unreceipted transfer of the
/// quarantined tick is listed and emitted again by the next tick, at a fresh tip.
fn quarantine_tick(out: &Path, id: &str, reason: &str) -> Result<ExitCode, String> {
    tick_id(id)?;
    let pending = out.join("pending.json");
    if !pending.exists() { return Err("no pending tick to quarantine".into()); }
    let value = read_tick(&pending)?;
    if value["id"] != id { return Err("quarantine names a different pending tick".into()); }
    let dir = out.join("quarantine");
    std::fs::create_dir_all(&dir).map_err(|e| e.to_string())?;
    let name = format!("{id}.json");
    if dir.join(&name).exists() { return Err("quarantine collision; preserving both records".into()); }
    let record = json!({"type":"minidregg-pay-watcher-quarantine-v1","id":id,"reason":reason,
        "at":std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).map(|d| d.as_secs()).unwrap_or(0),
        "tick":value});
    write_atomic(&dir, &name, &serde_json::to_vec_pretty(&record).map_err(|e| e.to_string())?)?;
    std::fs::remove_file(&pending).map_err(|e| e.to_string())?;
    println!("quarantined tick={id}");
    Ok(ExitCode::SUCCESS)
}

fn split_path(path: &Path) -> Result<(&Path, &str), String> {
    let name = path
        .file_name()
        .and_then(|n| n.to_str())
        .ok_or_else(|| format!("cursor file {} has no file name", path.display()))?;
    Ok((path.parent().unwrap_or(Path::new(".")), name))
}

fn main() -> ExitCode {
    match real_main() {
        Ok(code) => code,
        Err(message) => {
            eprintln!("pay-watcher: {message}");
            ExitCode::from(2)
        }
    }
}

fn real_main() -> Result<ExitCode, String> {
    let args = parse_args()?;
    let _lock = if args.durable || args.ack_tick.is_some() || args.quarantine.is_some() { Some(durable_lock(&args.out)?) } else { None };
    if let Some(id) = &args.ack_tick { return acknowledge_tick(&args.out, id); }
    if let Some((id, reason)) = &args.quarantine { return quarantine_tick(&args.out, id, reason); }
    let cfg = Config::load(&args.config)?;
    if args.durable && args.out.join("pending.json").exists() {
        return publish_tick(&args.out, &cfg, &read_tick(&args.out.join("pending.json"))?);
    }
    let live = std::env::var("PAY_RPC_ENDPOINTS").ok().filter(|v| !v.trim().is_empty());
    let mut owned: Vec<Box<dyn Transport>> = Vec::new();
    if !args.fixtures.is_empty() {
        if live.is_some() {
            return Err("--rpc-fixture and PAY_RPC_ENDPOINTS are both set; refusing to guess".into());
        }
        for dir in &args.fixtures {
            owned.push(Box::new(FixtureTransport::new(dir)));
        }
    } else {
        let urls = live.ok_or("no endpoints: set PAY_RPC_ENDPOINTS or pass --rpc-fixture")?;
        let spool = args.spool.clone().unwrap_or_else(|| args.out.clone());
        for (i, url) in urls
            .split(|c: char| c.is_whitespace() || c == ',')
            .filter(|u| !u.is_empty())
            .enumerate()
        {
            let transport = CurlTransport::new(format!("endpoint{i}"), url, &spool)
                .map_err(|e| format!("endpoint{i}: {e}"))?;
            owned.push(Box::new(transport));
        }
    }
    let transports: Vec<&dyn Transport> = owned.iter().map(|b| b.as_ref()).collect();
    let (receipts, receipt_events) = load_receipts(&cfg.receipts_dir)?;
    let cursor = match &cfg.enrol {
        Some(e) => load_cursor(&e.cursor_file)?,
        None => Cursor::new(),
    };
    let mut report = run(&cfg, &transports, &receipts, &cursor).map_err(|r| r.to_string())?;
    report.events.splice(0..0, receipt_events);

    if args.durable {
        let cursor = cfg.enrol.as_ref().map(|e| json!({"path":e.cursor_file,
            "before":serde_json::from_slice::<Value>(&cursor_json(&cursor)).expect("cursor JSON"),
            "after":serde_json::from_slice::<Value>(&cursor_json(&report.cursor)).expect("cursor JSON")}));
        let tick = json!({"type":"minidregg-pay-watcher-tick-v1","id":next_tick_id(&args.out)?,
            "identity":config_identity(&cfg),
            "observations":serde_json::from_slice::<Value>(&report.observations_json()).expect("report JSON"),
            "events":serde_json::from_slice::<Value>(&report.events_json()).expect("events JSON"),
            "cursor":cursor,"exit":if report.refused() {3} else {0}});
        let bytes = serde_json::to_vec_pretty(&tick).map_err(|e| e.to_string())?;
        if bytes.len() > 64 * 1024 * 1024 { return Err("durable tick exceeds 64 MiB; cursor not advanced".into()); }
        write_atomic(&args.out, "pending.json", &bytes)?;
        return publish_tick(&args.out, &cfg, &tick);
    }
    write_atomic(&args.out, "observations.json", &report.observations_json())?;
    write_atomic(&args.out, "events.json", &report.events_json())?;
    // Last: a crash before this line leaves the old cursor, which re-derives the same run.
    if let Some(e) = &cfg.enrol {
        let (dir, name) = split_path(&e.cursor_file)?;
        write_atomic(dir, name, &cursor_json(&report.cursor))?;
    }
    for e in &report.events {
        eprintln!("{}", e.to_json());
    }
    let refusals = report.events.iter().filter(|e| e.reason.is_refusal()).count();
    println!(
        "observations={} refusals={} skips={} tip.slot={}",
        report.observations.len(),
        refusals,
        report.events.len() - refusals,
        report.tip.slot
    );
    Ok(if report.refused() {
        ExitCode::from(3)
    } else {
        ExitCode::SUCCESS
    })
}
