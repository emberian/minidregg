use minidregg_inference_scheduler::{core::Config, operate, service::Service, Command};
use std::os::unix::fs::MetadataExt;
use std::path::Path;
use std::time::{Duration, Instant};

fn config(path: &str, owner: u32) -> Result<Config, String> {
    let meta = std::fs::symlink_metadata(path).map_err(|e| e.to_string())?;
    if !meta.is_file() || meta.uid() != owner || meta.mode() & 0o022 != 0 || meta.len() > 65_536 {
        return Err("scheduler config must be root-owned regular file, not writable by group/other, <=64KiB".into());
    }
    let config: Config = serde_json::from_slice(&std::fs::read(path).map_err(|e| e.to_string())?)
        .map_err(|e| e.to_string())?;
    config.validate()?;
    Ok(config)
}

fn run() -> Result<(), String> {
    let args: Vec<_> = std::env::args().skip(1).collect();
    match args.iter().map(String::as_str).collect::<Vec<_>>().as_slice() {
        ["check", path] => { config(path, unsafe { libc::geteuid() })?; println!("valid inference configuration"); Ok(()) }
        ["status", socket] | ["status", socket, _] => {
            let after = args.get(2).cloned();
            let status = operate(Path::new(socket), &Command::Status { after, limit: 32 })?;
            println!("{}", serde_json::to_string_pretty(&status).map_err(|e| e.to_string())?); Ok(())
        }
        ["status-groups", socket] | ["status-groups", socket, _] => {
            let status = operate(Path::new(socket), &Command::StatusGroups { after: args.get(2).cloned() })?;
            println!("{}", serde_json::to_string_pretty(&status).map_err(|e| e.to_string())?); Ok(())
        }
        [verb @ ("drain" | "resume"), socket] | [verb @ ("drain" | "resume"), socket, _] => {
            let wait: u64 = args.get(2).map(|value| value.parse().map_err(|_| "wait must be integer seconds")).transpose()?.unwrap_or(0);
            if wait > 3600 || (*verb == "resume" && wait != 0) { return Err("drain wait must be 0..3600 seconds; resume takes no wait".into()); }
            let mut status = operate(Path::new(socket), &Command::Drain { enabled: *verb == "drain" })?;
            let deadline = Instant::now() + Duration::from_secs(wait);
            while wait != 0 && !status.quiescent && Instant::now() < deadline {
                std::thread::sleep(Duration::from_millis(100));
                status = operate(Path::new(socket), &Command::Status { after: None, limit: 32 })?;
            }
            println!("{}", serde_json::to_string_pretty(&status).map_err(|e| e.to_string())?);
            if wait != 0 && !status.quiescent { return Err("drain is durable; running or uncertain work remains (no capacity was erased)".into()); }
            Ok(())
        }
        ["resolve", socket, id] => {
            // The operator attests the job's physical execution is over.
            let status = operate(Path::new(socket), &Command::Resolve { id: (*id).to_owned() })?;
            println!("{}", serde_json::to_string_pretty(&status).map_err(|e| e.to_string())?); Ok(())
        }
        [path, state, socket] => Service::open(config(path, 0)?, Path::new(state))?.serve(Path::new(socket)),
        _ => Err("usage: mini-inference-scheduler CONFIG STATE_DIR SOCKET | check CONFIG | status SOCKET [AFTER_ID] | status-groups SOCKET [AFTER_GROUP] | drain SOCKET [WAIT_SECONDS] | resume SOCKET | resolve SOCKET JOB_ID".into()),
    }
}

fn main() {
    if let Err(error) = run() {
        eprintln!("{error}");
        std::process::exit(1);
    }
}
