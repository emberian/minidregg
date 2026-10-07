use minidregg_hyperdocument_link_sqlite_store::{
    decode_history_request, decode_nodes, encode_durable_read, encode_history_read, encode_journal_read, PublishPhase, SqliteLinkStore, StoreError, MAX_RECORD_BYTES,
};
use std::env;
use std::fs::{self, File};
use std::io::{self, Read, Write};
use std::path::Path;
use std::process::ExitCode;
use std::thread;
use std::time::Duration;

fn read_input(path: &Path) -> Result<Vec<u8>, StoreError> {
    let file = File::open(path)?;
    let mut bytes = Vec::new();
    file.take((MAX_RECORD_BYTES + 1) as u64)
        .read_to_end(&mut bytes)?;
    if bytes.len() > MAX_RECORD_BYTES {
        return Err(StoreError::TooLarge {
            actual: bytes.len(),
            maximum: MAX_RECORD_BYTES,
        });
    }
    Ok(bytes)
}

const USAGE: &str = "usage:\n  minidregg-link-sqlite-store read ROOT\n  minidregg-link-sqlite-store read-to ROOT OUTPUT\n  minidregg-link-sqlite-store publish ROOT INPUT\n  minidregg-link-sqlite-store cas ROOT EXPECTED|- INPUT\n  minidregg-link-sqlite-store cas-crash ROOT EXPECTED|- INPUT after-begin|after-insert|after-commit\n  minidregg-link-sqlite-store publish-crash ROOT INPUT after-begin|after-insert|after-commit\n  minidregg-link-sqlite-store publish-hold ROOT INPUT READY RELEASE\n  minidregg-link-sqlite-store database-path ROOT\n  minidregg-link-sqlite-store durable-anchor-enroll ROOT\n  minidregg-link-sqlite-store durable-init ROOT SEED\n  minidregg-link-sqlite-store durable-read ROOT FROM 0|1|2 OUTPUT\n  minidregg-link-sqlite-store durable-history ROOT REQUEST OUTPUT\n  minidregg-link-sqlite-store durable-seed ROOT OUTPUT\n  minidregg-link-sqlite-store durable-append ROOT HEIGHT RECORD TAG NODES\n  minidregg-link-sqlite-store durable-append-crash ROOT HEIGHT RECORD TAG NODES after-begin|after-insert|after-commit\n  minidregg-link-sqlite-store durable-checkpoint ROOT HEIGHT INPUT\n  minidregg-link-sqlite-store durable-checkpoint-at ROOT HEIGHT OUTPUT\n  minidregg-link-sqlite-store journal-read ROOT FROM OUTPUT\n  minidregg-link-sqlite-store journal-append ROOT SEQ RECORD TAG\n  minidregg-link-sqlite-store journal-append-crash ROOT SEQ RECORD TAG after-begin|after-insert|after-commit|after-anchor-prepare|after-anchor-rename|after-anchor\n  minidregg-link-sqlite-store serve";

/// The CLI could not run: usage (exit 2) or a store error.
enum Failure {
    Usage,
    Store(StoreError),
}

impl From<StoreError> for Failure {
    fn from(error: StoreError) -> Self {
        Failure::Store(error)
    }
}

impl From<std::io::Error> for Failure {
    fn from(error: std::io::Error) -> Self {
        Failure::Store(StoreError::from(error))
    }
}


fn crash_phase(name: &str) -> Option<(PublishPhase, i32)> {
    match name {
        "after-begin" => Some((PublishPhase::Begun, 86)),
        "after-insert" => Some((PublishPhase::Inserted, 87)),
        "after-commit" => Some((PublishPhase::Committed, 88)),
        "after-anchor-prepare" => Some((PublishPhase::AnchorPrepared, 90)),
        "after-anchor-rename" => Some((PublishPhase::AnchorRenamed, 91)),
        "after-anchor" => Some((PublishPhase::Anchored, 89)),
        _ => None,
    }
}

fn parse_height(value: &std::ffi::OsStr) -> Result<u64, StoreError> {
    value
        .to_str()
        .and_then(|text| text.parse::<u64>().ok())
        .filter(|height| *height <= i64::MAX as u64)
        .ok_or(StoreError::InvalidPath)
}

fn run(mut arguments: Vec<std::ffi::OsString>, out: &mut Vec<u8>) -> Result<(), Failure> {
    let identity = if arguments
        .first()
        .is_some_and(|arg| arg == "--anchor-identity")
    {
        if arguments.len() < 3 {
            return Err(Failure::Usage);
        }
        let identity = arguments[1].clone().into_encoded_bytes();
        arguments.drain(..2);
        identity
    } else {
        Vec::new()
    };
    let Some(command) = arguments.first().and_then(|value| value.to_str()) else {
        return Err(Failure::Usage);
    };
    match (command, &arguments[1..]) {
        ("read", [root]) => {
            let store = SqliteLinkStore::open_with_identity(root, &identity)?;
            out.extend_from_slice(&store.read()?);
        }
        ("read-to", [root, output]) => {
            let store = SqliteLinkStore::open_with_identity(root, &identity)?;
            let bytes = store.read()?;
            fs::write(output, bytes)?;
        }
        ("cas", [root, expected, input]) => {
            let store = SqliteLinkStore::open_with_identity(root, &identity)?;
            let expected = if expected == "-" {
                None
            } else {
                Some(read_input(Path::new(expected))?)
            };
            writeln!(out, 
                "{:?}",
                store.compare_exchange(expected.as_deref(), &read_input(Path::new(input))?)?
            )?;
        }
        ("cas-crash", [root, expected, input, phase]) => {
            let Some((target, exit_code)) = phase.to_str().and_then(crash_phase) else {
                return Err(Failure::Usage);
            };
            let store = SqliteLinkStore::open_with_identity(root, &identity)?;
            let expected = if expected == "-" {
                None
            } else {
                Some(read_input(Path::new(expected))?)
            };
            let proposed = read_input(Path::new(input))?;
            let _ =
                store.compare_exchange_with_hook(expected.as_deref(), &proposed, |observed| {
                    if observed == target {
                        std::process::exit(exit_code);
                    }
                })?;
        }
        ("publish", [root, input]) => {
            let store = SqliteLinkStore::open_with_identity(root, &identity)?;
            writeln!(out, "{:?}", store.publish(&read_input(Path::new(input))?)?)?;
        }
        ("publish-crash", [root, input, phase]) => {
            let Some((target, exit_code)) = phase.to_str().and_then(crash_phase) else {
                return Err(Failure::Usage);
            };
            let store = SqliteLinkStore::open_with_identity(root, &identity)?;
            let bytes = read_input(Path::new(input))?;
            let _ = store.publish_with_hook(&bytes, |observed| {
                if observed == target {
                    // `_exit`-like behavior: no response and no normal Rust
                    // unwinding.  SQLite/OS recovery owns the next open.
                    std::process::exit(exit_code);
                }
            })?;
        }
        ("publish-hold", [root, input, ready, release]) => {
            let store = SqliteLinkStore::open_with_identity(root, &identity)?;
            let bytes = read_input(Path::new(input))?;
            let ready = Path::new(ready);
            let release = Path::new(release);
            writeln!(out, 
                "{:?}",
                store.publish_with_hook(&bytes, |phase| {
                    if phase == PublishPhase::Inserted {
                        fs::write(ready, b"inserted-not-committed\n")
                            .expect("publish-hold ready marker");
                        while !release.exists() {
                            thread::sleep(Duration::from_millis(10));
                        }
                    }
                })?
            )?;
        }
        ("durable-anchor-enroll", [root]) => {
            let store = SqliteLinkStore::open_with_identity(root, &identity)?;
            store.durable_anchor_enroll()?;
            writeln!(out, "Enrolled")?;
        }
        ("durable-init", [root, seed]) => {
            let store = SqliteLinkStore::open_with_identity(root, &identity)?;
            writeln!(out, "{:?}", store.durable_init(&read_input(Path::new(seed))?)?)?;
        }
        ("durable-read", [root, from, with_base, output]) => {
            let from = parse_height(from)?;
            let store = SqliteLinkStore::open_with_identity(root, &identity)?;
            let read = match with_base.to_str() {
                Some("0") => store.durable_read(from, false)?,
                Some("1") => store.durable_read(from, true)?,
                // The open's read: base and the entries from the checkpoint.
                Some("2") => store.durable_read_from_checkpoint()?,
                _ => return Err(Failure::Usage),
            };
            fs::write(output, encode_durable_read(&read))?;
        }
        ("durable-history", [root, request, output]) => {
            let (at, heights, nodes) = decode_history_request(&read_input(Path::new(request))?)?;
            let store = SqliteLinkStore::open_with_identity(root, &identity)?;
            fs::write(
                output,
                encode_history_read(&store.durable_history(at, &heights, &nodes)?),
            )?;
        }
        ("durable-seed", [root, output]) => {
            let store = SqliteLinkStore::open_with_identity(root, &identity)?;
            fs::write(output, store.durable_seed_bytes()?)?;
        }
        ("durable-append", [root, height, record, tag, nodes]) => {
            let height = parse_height(height)?;
            let store = SqliteLinkStore::open_with_identity(root, &identity)?;
            writeln!(out, 
                "{:?}",
                store.durable_append(
                    height,
                    &read_input(Path::new(record))?,
                    &read_input(Path::new(tag))?,
                    &decode_nodes(&read_input(Path::new(nodes))?)?
                )?
            )?;
        }
        ("durable-append-crash", [root, height, record, tag, nodes, phase]) => {
            let Some((target, exit_code)) = phase.to_str().and_then(crash_phase) else {
                return Err(Failure::Usage);
            };
            let height = parse_height(height)?;
            let store = SqliteLinkStore::open_with_identity(root, &identity)?;
            let record = read_input(Path::new(record))?;
            let tag = read_input(Path::new(tag))?;
            let nodes = decode_nodes(&read_input(Path::new(nodes))?)?;
            let _ = store.durable_append_with_hook(height, &record, &tag, &nodes, |observed| {
                if observed == target {
                    std::process::exit(exit_code);
                }
            })?;
        }
        ("journal-read", [root, from, output]) => {
            let from = parse_height(from)?;
            let store = SqliteLinkStore::open_with_identity(root, &identity)?;
            fs::write(output, encode_journal_read(&store.journal_read(from)?))?;
        }
        ("journal-append", [root, seq, record, tag]) => {
            let seq = parse_height(seq)?;
            let store = SqliteLinkStore::open_with_identity(root, &identity)?;
            writeln!(
                out,
                "{:?}",
                store.journal_append(
                    seq,
                    &read_input(Path::new(record))?,
                    &read_input(Path::new(tag))?
                )?
            )?;
        }
        ("journal-append-crash", [root, seq, record, tag, phase]) => {
            let Some((target, exit_code)) = phase.to_str().and_then(crash_phase) else {
                return Err(Failure::Usage);
            };
            let seq = parse_height(seq)?;
            let store = SqliteLinkStore::open_with_identity(root, &identity)?;
            let record = read_input(Path::new(record))?;
            let tag = read_input(Path::new(tag))?;
            let _ = store.journal_append_with_hook(seq, &record, &tag, |observed| {
                if observed == target {
                    std::process::exit(exit_code);
                }
            })?;
        }
        ("durable-checkpoint-at", [root, height, output]) => {
            let height = parse_height(height)?;
            let store = SqliteLinkStore::open_with_identity(root, &identity)?;
            let mut bytes = Vec::new();
            match store.durable_checkpoint_at(height)? {
                None => bytes.extend_from_slice(&0u64.to_be_bytes()),
                Some((found, checkpoint)) => {
                    bytes.extend_from_slice(&1u64.to_be_bytes());
                    bytes.extend_from_slice(&found.to_be_bytes());
                    bytes.extend_from_slice(&(checkpoint.len() as u64).to_be_bytes());
                    bytes.extend_from_slice(&checkpoint);
                }
            }
            fs::write(output, bytes)?;
        }
        ("durable-checkpoint", [root, height, input]) => {
            let height = parse_height(height)?;
            let store = SqliteLinkStore::open_with_identity(root, &identity)?;
            store.durable_checkpoint(height, &read_input(Path::new(input))?)?;
        }
        ("database-path", [root]) => {
            let store = SqliteLinkStore::open_with_identity(root, &identity)?;
            writeln!(out, "{}", store.database_path().display())?;
        }
        _ => return Err(Failure::Usage),
    }
    Ok(())
}

/// One one-shot invocation: exit code, stdout, stderr. `main` writes them;
/// `serve` frames them. Both run exactly this function.
fn invoke(arguments: Vec<std::ffi::OsString>) -> (u32, Vec<u8>, Vec<u8>) {
    let mut out = Vec::new();
    match run(arguments, &mut out) {
        Ok(()) => (0, out, Vec::new()),
        Err(Failure::Usage) => (2, out, format!("{USAGE}\n").into_bytes()),
        Err(Failure::Store(error)) => {
            let code = match error {
                StoreError::Missing => 3,
                StoreError::Conflict => 4,
                StoreError::RetiredImage | StoreError::RetiredSchema(_) => 5,
                _ => 1,
            };
            (code, out, format!("sqlite-store error: {error}\n").into_bytes())
        }
    }
}

/// Fixture commands that end the process mid-operation (crash phases) or
/// hold it for another process; they keep their own child under `serve`.
fn needs_own_process(arguments: &[std::ffi::OsString]) -> bool {
    let command = if arguments.first().is_some_and(|a| a == "--anchor-identity") { arguments.get(2) } else { arguments.first() };
    command.is_some_and(|c| matches!(c.to_str(), Some("cas-crash" | "publish-crash" | "durable-append-crash" | "journal-append-crash" | "publish-hold")))
}

fn main() -> ExitCode {
    let arguments: Vec<_> = env::args_os().skip(1).collect();
    if arguments.len() == 1 && arguments[0] == "serve" {
        return serve();
    }
    let (code, stdout, stderr) = invoke(arguments);
    let _ = io::stdout().lock().write_all(&stdout).and_then(|()| io::stdout().lock().flush());
    let _ = io::stderr().lock().write_all(&stderr);
    ExitCode::from(code as u8)
}

/// `serve`: the long-lived form a Lean Host keeps for its whole lifetime
/// (`Compiler.NativeCoprocess`). Each request frame on stdin is one argv for
/// this same executable, answered by the one-shot invocation's own function
/// in this process, so its files, stdout, stderr and exit code are exactly
/// the one-shot invocation's. Crash and hold fixtures alone still run as
/// their own child, because they end or suspend their process on purpose.
/// Frames: request `u32 argc, (u32 len, bytes)*`; reply `u32 code,
/// u64 len, stdout, u64 len, stderr`; integers big-endian. EOF ends it.
fn serve() -> ExitCode {
    use std::ffi::OsString;
    use std::io::{BufReader, BufWriter, ErrorKind};
    use std::os::unix::ffi::OsStringExt;
    use std::os::unix::process::ExitStatusExt;
    use std::process::{Command, Stdio};
    const MAX_ARGS: usize = 64;
    const MAX_ARG_BYTES: usize = 64 * 1024;
    let Ok(executable) = env::current_exe() else {
        return ExitCode::from(2);
    };
    let mut input = BufReader::new(io::stdin().lock());
    let mut output = BufWriter::new(io::stdout().lock());
    let mut word = [0u8; 4];
    loop {
        match input.read_exact(&mut word) {
            Ok(()) => {}
            Err(error) if error.kind() == ErrorKind::UnexpectedEof => return ExitCode::SUCCESS,
            Err(_) => return ExitCode::FAILURE,
        }
        let count = u32::from_be_bytes(word) as usize;
        if count == 0 || count > MAX_ARGS {
            return ExitCode::FAILURE;
        }
        let mut arguments = Vec::with_capacity(count);
        for _ in 0..count {
            if input.read_exact(&mut word).is_err() {
                return ExitCode::FAILURE;
            }
            let length = u32::from_be_bytes(word) as usize;
            if length > MAX_ARG_BYTES {
                return ExitCode::FAILURE;
            }
            let mut bytes = vec![0u8; length];
            if input.read_exact(&mut bytes).is_err() {
                return ExitCode::FAILURE;
            }
            arguments.push(OsString::from_vec(bytes));
        }
        // A request names a one-shot command, never another server.
        if arguments[0] == "serve" {
            return ExitCode::FAILURE;
        }
        let (code, stdout, stderr) = if needs_own_process(&arguments) {
            let Ok(result) = Command::new(&executable)
                .args(&arguments)
                .stdin(Stdio::null())
                .output()
            else {
                return ExitCode::FAILURE;
            };
            let code: u32 = match (result.status.code(), result.status.signal()) {
                (Some(code), _) => code as u32,
                (None, Some(signal)) => 128 + signal as u32,
                (None, None) => 255,
            };
            (code, result.stdout, result.stderr)
        } else {
            std::panic::catch_unwind(|| invoke(arguments))
                .unwrap_or_else(|_| (101, Vec::new(), b"sqlite-store error: panicked\n".to_vec()))
        };
        let written = output
            .write_all(&code.to_be_bytes())
            .and_then(|()| output.write_all(&(stdout.len() as u64).to_be_bytes()))
            .and_then(|()| output.write_all(&stdout))
            .and_then(|()| output.write_all(&(stderr.len() as u64).to_be_bytes()))
            .and_then(|()| output.write_all(&stderr))
            .and_then(|()| output.flush());
        if written.is_err() {
            return ExitCode::FAILURE;
        }
    }
}
