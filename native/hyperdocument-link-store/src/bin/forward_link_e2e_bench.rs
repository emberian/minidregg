//! Process-boundary benchmark for the bounded opaque forward-link byte store.
//!
//! This measures the real `LocalLinkStore` implementation and deliberately
//! does not parse or validate Hyperdocument semantics.  Each lifecycle stage
//! runs in a fresh child process.  The successful install response is ignored,
//! then a new process reads, an exact retry runs in another process, and a
//! final process reopens the record.  `LocalLinkStore` remains the only storage
//! implementation used by both the CLI and this harness.

use minidregg_hyperdocument_link_store::{
    LocalLinkStore, PublishStatus, StageStatus, MAX_RECORD_BYTES,
};
use std::env;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, ExitCode, Output};
use std::time::{Instant, SystemTime, UNIX_EPOCH};

const SCHEMA: &str = "minidregg/forward-link-e2e/v1";
const FIXTURE: &[u8] = include_bytes!("../../fixtures/hyperdocument-link-recovery-v1.bin");
const DEFAULT_SAMPLES: usize = 31;
const DEFAULT_WARMUPS: usize = 3;

#[derive(Clone, Copy)]
struct Stage {
    name: &'static str,
    request_bytes: usize,
    verified_response_bytes: usize,
}

const STAGES: [Stage; 6] = [
    Stage {
        name: "submit_stage_bound_conflict",
        request_bytes: FIXTURE.len(),
        verified_response_bytes: 0,
    },
    Stage {
        name: "install_lost_response",
        request_bytes: 0,
        verified_response_bytes: 0,
    },
    Stage {
        name: "restart_read_exact",
        request_bytes: 0,
        verified_response_bytes: FIXTURE.len(),
    },
    Stage {
        name: "exact_retry",
        request_bytes: FIXTURE.len(),
        verified_response_bytes: 0,
    },
    Stage {
        name: "reopen_read_exact",
        request_bytes: 0,
        verified_response_bytes: FIXTURE.len(),
    },
    Stage {
        name: "full_process_lifecycle",
        request_bytes: FIXTURE.len() * 2,
        verified_response_bytes: FIXTURE.len() * 2,
    },
];

struct TempRoot(PathBuf);

impl TempRoot {
    fn new(sample: usize) -> Result<Self, String> {
        let nonce = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .map_err(|error| format!("clock before epoch: {error}"))?
            .as_nanos();
        let path = env::temp_dir().join(format!(
            "minidregg-forward-link-bench-{}-{nonce}-{sample}",
            std::process::id()
        ));
        fs::create_dir(&path)
            .map_err(|error| format!("create {}: {error}", path.display()))?;
        Ok(Self(path))
    }

    fn path(&self) -> &Path {
        &self.0
    }
}

impl Drop for TempRoot {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

fn parse_count(name: &str, default: usize) -> Result<usize, String> {
    match env::var(name) {
        Ok(value) => {
            let parsed = value
                .parse::<usize>()
                .map_err(|_| format!("{name} must be a positive integer"))?;
            if parsed == 0 {
                Err(format!("{name} must be positive"))
            } else {
                Ok(parsed)
            }
        }
        Err(env::VarError::NotPresent) => Ok(default),
        Err(error) => Err(format!("cannot read {name}: {error}")),
    }
}

fn worker(command: &str, root: &Path) -> Result<(), String> {
    if FIXTURE.len() > MAX_RECORD_BYTES {
        return Err("compiled fixture exceeds the store bound".to_owned());
    }
    let store = LocalLinkStore::open(root).map_err(|error| error.to_string())?;
    match command {
        "worker-stage" => match store.stage(FIXTURE).map_err(|error| error.to_string())? {
            StageStatus::Staged => Ok(()),
            StageStatus::AlreadyPresent => Err("fresh stage was already present".to_owned()),
        },
        "worker-install" => {
            match store.install_staged().map_err(|error| error.to_string())? {
                PublishStatus::Installed => Ok(()),
                PublishStatus::AlreadyPresent => {
                    Err("fresh install was already present".to_owned())
                }
            }
        }
        "worker-read" => {
            let bytes = store.read().map_err(|error| error.to_string())?;
            if bytes == FIXTURE {
                // Binary stdout is the caller-observed opaque read result.
                use std::io::Write;
                std::io::stdout()
                    .write_all(&bytes)
                    .map_err(|error| error.to_string())
            } else {
                Err("read bytes differ from the compiled Lean-authored fixture".to_owned())
            }
        }
        "worker-retry" => match store.publish(FIXTURE).map_err(|error| error.to_string())? {
            PublishStatus::AlreadyPresent => Ok(()),
            PublishStatus::Installed => Err("exact retry performed a fresh install".to_owned()),
        },
        _ => Err(format!("unknown worker command {command}")),
    }
}

fn run_child(executable: &Path, command: &str, root: &Path) -> Result<Output, String> {
    let output = Command::new(executable)
        .arg(command)
        .arg(root)
        .output()
        .map_err(|error| format!("launch {command}: {error}"))?;
    if output.status.success() {
        Ok(output)
    } else {
        Err(format!(
            "{command} failed with {}: {}",
            output.status,
            String::from_utf8_lossy(&output.stderr)
        ))
    }
}

fn timed_child(
    executable: &Path,
    command: &str,
    root: &Path,
) -> Result<(u128, Output), String> {
    let started = Instant::now();
    let output = run_child(executable, command, root)?;
    Ok((started.elapsed().as_nanos(), output))
}

fn checked_read(output: &Output, stage: &str) -> Result<(), String> {
    if output.stdout == FIXTURE {
        Ok(())
    } else {
        Err(format!(
            "{stage} returned {} bytes instead of the exact {}-byte fixture",
            output.stdout.len(),
            FIXTURE.len()
        ))
    }
}

fn lifecycle(executable: &Path, sample: usize) -> Result<[u128; 6], String> {
    let root = TempRoot::new(sample)?;
    let full_started = Instant::now();

    let (stage_ns, _) = timed_child(executable, "worker-stage", root.path())?;

    // The child completed the no-overwrite install and sync calls.  Its
    // successful response is intentionally not inspected: this is the lost
    // response point.  The next observation comes from a new process.
    let (install_ns, _lost_response) =
        timed_child(executable, "worker-install", root.path())?;

    let (restart_read_ns, restart_read) =
        timed_child(executable, "worker-read", root.path())?;
    checked_read(&restart_read, "restart read")?;

    let (retry_ns, _) = timed_child(executable, "worker-retry", root.path())?;

    let (reopen_ns, reopened) = timed_child(executable, "worker-read", root.path())?;
    checked_read(&reopened, "reopen read")?;

    let full_ns = full_started.elapsed().as_nanos();
    Ok([
        stage_ns,
        install_ns,
        restart_read_ns,
        retry_ns,
        reopen_ns,
        full_ns,
    ])
}

fn nearest_rank(sorted: &[u128], percentile: usize) -> u128 {
    let rank = (percentile * sorted.len()).div_ceil(100);
    sorted[rank.saturating_sub(1)]
}

fn benchmark() -> Result<(), String> {
    let samples = parse_count("MINIDREGG_LINK_BENCH_SAMPLES", DEFAULT_SAMPLES)?;
    let warmups = parse_count("MINIDREGG_LINK_BENCH_WARMUPS", DEFAULT_WARMUPS)?;
    let executable = env::current_exe().map_err(|error| error.to_string())?;

    if FIXTURE != [162, 74, 30, 216, 1, 72, 89, 80, 69, 82, 76, 78, 75, 110] {
        return Err("compiled fixture is not the pinned Lean-authored recovery record".to_owned());
    }

    println!("benchmark={SCHEMA}");
    println!("samples={samples}");
    println!("warmups={warmups}");
    println!("fixture_bytes={}", FIXTURE.len());
    println!("store_max_record_bytes={MAX_RECORD_BYTES}");
    println!("timing=std::time::Instant around a fresh child process per stage");
    println!("filesystem_cache_state=uncontrolled; no cold-cache or stable-media claim");
    println!("sample_directory=fresh per lifecycle; warmups precede all measured samples");
    println!("memory=not_reported; child-process peak RSS is not attributed reliably per stage");
    println!("semantic_boundary=opaque bytes only; Lean validation/reopen/query are separate");
    println!("record,schema,phase,sample,stage,elapsed_ns,request_bytes,verified_response_bytes");

    for warmup in 0..warmups {
        lifecycle(&executable, usize::MAX - warmup)?;
    }

    let mut observations: [Vec<u128>; 6] = std::array::from_fn(|_| Vec::with_capacity(samples));
    for sample in 0..samples {
        let elapsed = lifecycle(&executable, sample)?;
        let phase = if sample == 0 {
            "first_measured_after_warmup"
        } else {
            "repeated_after_warmup"
        };
        for (index, stage) in STAGES.iter().enumerate() {
            observations[index].push(elapsed[index]);
            println!(
                "sample,{SCHEMA},{phase},{sample},{},{},{},{}",
                stage.name,
                elapsed[index],
                stage.request_bytes,
                stage.verified_response_bytes
            );
        }
    }

    println!("record,schema,stage,samples,p50_ns,p95_ns,p99_ns,min_ns,max_ns,request_bytes,verified_response_bytes");
    for (index, stage) in STAGES.iter().enumerate() {
        let mut sorted = observations[index].clone();
        sorted.sort_unstable();
        println!(
            "summary,{SCHEMA},{},{},{},{},{},{},{},{},{}",
            stage.name,
            sorted.len(),
            nearest_rank(&sorted, 50),
            nearest_rank(&sorted, 95),
            nearest_rank(&sorted, 99),
            sorted[0],
            sorted[sorted.len() - 1],
            stage.request_bytes,
            stage.verified_response_bytes
        );
    }
    println!("native_lifecycle_status=PASS");
    Ok(())
}

fn run() -> Result<(), String> {
    let args: Vec<_> = env::args_os().skip(1).collect();
    if let Some(command) = args.first().and_then(|value| value.to_str()) {
        if command.starts_with("worker-") {
            let root = args
                .get(1)
                .ok_or_else(|| format!("{command} requires ROOT"))?;
            if args.len() != 2 {
                return Err(format!("{command} requires exactly one ROOT"));
            }
            return worker(command, Path::new(root));
        }
        return Err(format!("unexpected argument {command}"));
    }
    benchmark()
}

fn main() -> ExitCode {
    match run() {
        Ok(()) => ExitCode::SUCCESS,
        Err(error) => {
            eprintln!("forward-link benchmark error: {error}");
            ExitCode::FAILURE
        }
    }
}
