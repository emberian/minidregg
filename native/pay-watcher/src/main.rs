//! pay-watcher --config FILE --out DIR [--rpc-fixture DIR]... [--spool DIR]
//!
//! Live mode (no `--rpc-fixture`): endpoints come from `PAY_RPC_ENDPOINTS` (whitespace- or
//! comma-separated URLs; PAY.md §3.5 keeps them in `/etc/mini/pay/rpc.env`), each reached with
//! `/usr/bin/curl` through a private spool (`--spool`, default `--out`). Fixture mode: each
//! `--rpc-fixture DIR` is one endpoint answered from files (see `transport::fixture_key`).
//!
//! Writes `DIR/observations.json` and `DIR/events.json` (each atomically) and prints one
//! summary line on stdout; every event is also one line on stderr.
//!
//! Exit: 0 = written, nothing refused; 3 = written, at least one refusal (the observations
//! that were emitted are still sound); 2 = nothing written (usage, config, receipts, or no
//! agreed tip).

use std::io::Write;
use std::path::{Path, PathBuf};
use std::process::ExitCode;

use minidregg_pay_watcher::transport::{CurlTransport, FixtureTransport, Transport};
use minidregg_pay_watcher::{load_receipts, run, Config};

struct Args {
    config: PathBuf,
    out: PathBuf,
    fixtures: Vec<PathBuf>,
    spool: Option<PathBuf>,
}

fn parse_args() -> Result<Args, String> {
    let mut config = None;
    let mut out = None;
    let mut fixtures = Vec::new();
    let mut spool = None;
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
            _ => return Err(format!("unknown argument {}", arg.to_string_lossy())),
        }
    }
    Ok(Args {
        config: config.ok_or("--config is required")?,
        out: out.ok_or("--out is required")?,
        fixtures,
        spool,
    })
}

fn write_atomic(dir: &Path, name: &str, bytes: &[u8]) -> Result<(), String> {
    let tmp = dir.join(format!(".{name}.tmp"));
    let dest = dir.join(name);
    let mut file = std::fs::File::create(&tmp).map_err(|e| format!("{}: {e}", tmp.display()))?;
    file.write_all(bytes)
        .and_then(|_| file.sync_all())
        .map_err(|e| format!("{}: {e}", tmp.display()))?;
    std::fs::rename(&tmp, &dest).map_err(|e| format!("{}: {e}", dest.display()))
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
    let cfg = Config::load(&args.config)?;
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
    let mut report = run(&cfg, &transports, &receipts).map_err(|r| r.to_string())?;
    report.events.splice(0..0, receipt_events);

    write_atomic(&args.out, "observations.json", &report.observations_json())?;
    write_atomic(&args.out, "events.json", &report.events_json())?;
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
