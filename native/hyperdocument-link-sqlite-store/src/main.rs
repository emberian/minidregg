use minidregg_hyperdocument_link_sqlite_store::{
    encode_durable_read, PublishPhase, SqliteLinkStore, StoreError, MAX_RECORD_BYTES,
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

fn usage() -> ! {
    eprintln!(
        "usage:\n  minidregg-link-sqlite-store read ROOT\n  minidregg-link-sqlite-store read-to ROOT OUTPUT\n  minidregg-link-sqlite-store publish ROOT INPUT\n  minidregg-link-sqlite-store cas ROOT EXPECTED|- INPUT\n  minidregg-link-sqlite-store cas-crash ROOT EXPECTED|- INPUT after-begin|after-insert|after-commit\n  minidregg-link-sqlite-store publish-crash ROOT INPUT after-begin|after-insert|after-commit\n  minidregg-link-sqlite-store publish-hold ROOT INPUT READY RELEASE\n  minidregg-link-sqlite-store database-path ROOT\n  minidregg-link-sqlite-store durable-init ROOT SEED\n  minidregg-link-sqlite-store durable-read ROOT FROM 0|1 OUTPUT\n  minidregg-link-sqlite-store durable-append ROOT HEIGHT RECORD TAG\n  minidregg-link-sqlite-store durable-append-crash ROOT HEIGHT RECORD TAG after-begin|after-insert|after-commit\n  minidregg-link-sqlite-store durable-checkpoint ROOT HEIGHT INPUT\n  minidregg-link-sqlite-store serve"
    );
    std::process::exit(2)
}

fn crash_phase(name: &str) -> Option<(PublishPhase, i32)> {
    match name {
        "after-begin" => Some((PublishPhase::Begun, 86)),
        "after-insert" => Some((PublishPhase::Inserted, 87)),
        "after-commit" => Some((PublishPhase::Committed, 88)),
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

fn run() -> Result<(), StoreError> {
    let arguments: Vec<_> = env::args_os().skip(1).collect();
    let Some(command) = arguments.first().and_then(|value| value.to_str()) else {
        usage()
    };
    match (command, &arguments[1..]) {
        ("read", [root]) => {
            let store = SqliteLinkStore::open(root)?;
            io::stdout().write_all(&store.read()?)?;
        }
        ("read-to", [root, output]) => {
            let store = SqliteLinkStore::open(root)?;
            let bytes = store.read()?;
            fs::write(output, bytes)?;
        }
        ("cas", [root, expected, input]) => {
            let store = SqliteLinkStore::open(root)?;
            let expected = if expected == "-" {
                None
            } else {
                Some(read_input(Path::new(expected))?)
            };
            println!(
                "{:?}",
                store.compare_exchange(expected.as_deref(), &read_input(Path::new(input))?)?
            );
        }
        ("cas-crash", [root, expected, input, phase]) => {
            let Some((target, exit_code)) = phase.to_str().and_then(crash_phase) else {
                usage()
            };
            let store = SqliteLinkStore::open(root)?;
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
            let store = SqliteLinkStore::open(root)?;
            println!("{:?}", store.publish(&read_input(Path::new(input))?)?);
        }
        ("publish-crash", [root, input, phase]) => {
            let Some((target, exit_code)) = phase.to_str().and_then(crash_phase) else {
                usage()
            };
            let store = SqliteLinkStore::open(root)?;
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
            let store = SqliteLinkStore::open(root)?;
            let bytes = read_input(Path::new(input))?;
            let ready = Path::new(ready);
            let release = Path::new(release);
            println!(
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
            );
        }
        ("durable-init", [root, seed]) => {
            let store = SqliteLinkStore::open(root)?;
            println!("{:?}", store.durable_init(&read_input(Path::new(seed))?)?);
        }
        ("durable-read", [root, from, with_base, output]) => {
            let from = parse_height(from)?;
            let with_base = match with_base.to_str() {
                Some("0") => false,
                Some("1") => true,
                _ => usage(),
            };
            let store = SqliteLinkStore::open(root)?;
            fs::write(output, encode_durable_read(&store.durable_read(from, with_base)?))?;
        }
        ("durable-append", [root, height, record, tag]) => {
            let height = parse_height(height)?;
            let store = SqliteLinkStore::open(root)?;
            println!(
                "{:?}",
                store.durable_append(
                    height,
                    &read_input(Path::new(record))?,
                    &read_input(Path::new(tag))?
                )?
            );
        }
        ("durable-append-crash", [root, height, record, tag, phase]) => {
            let Some((target, exit_code)) = phase.to_str().and_then(crash_phase) else {
                usage()
            };
            let height = parse_height(height)?;
            let store = SqliteLinkStore::open(root)?;
            let record = read_input(Path::new(record))?;
            let tag = read_input(Path::new(tag))?;
            let _ = store.durable_append_with_hook(height, &record, &tag, |observed| {
                if observed == target {
                    std::process::exit(exit_code);
                }
            })?;
        }
        ("durable-checkpoint", [root, height, input]) => {
            let height = parse_height(height)?;
            let store = SqliteLinkStore::open(root)?;
            store.durable_checkpoint(height, &read_input(Path::new(input))?)?;
        }
        ("database-path", [root]) => {
            let store = SqliteLinkStore::open(root)?;
            println!("{}", store.database_path().display());
        }
        _ => usage(),
    }
    Ok(())
}

fn main() -> ExitCode {
    let arguments: Vec<_> = env::args_os().skip(1).collect();
    if arguments.len() == 1 && arguments[0] == "serve" {
        return serve();
    }
    match run() {
        Ok(()) => ExitCode::SUCCESS,
        Err(error) => {
            eprintln!("sqlite-store error: {error}");
            ExitCode::from(match error {
                StoreError::Missing => 3,
                StoreError::Conflict => 4,
                StoreError::RetiredImage => 5,
                _ => 1,
            })
        }
    }
}

/// `serve`: the long-lived form a Lean Host keeps for its whole lifetime
/// (`Compiler.NativeCoprocess`). Each request frame on stdin is one argv for
/// this same executable; it runs as its own child process, so its files, its
/// stdout, its stderr and its exit code are exactly the one-shot invocation's.
/// The reply frame carries those three. The Host forks this small process
/// once instead of forking its own large address space for every call.
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
        let written = output
            .write_all(&code.to_be_bytes())
            .and_then(|()| output.write_all(&(result.stdout.len() as u64).to_be_bytes()))
            .and_then(|()| output.write_all(&result.stdout))
            .and_then(|()| output.write_all(&(result.stderr.len() as u64).to_be_bytes()))
            .and_then(|()| output.write_all(&result.stderr))
            .and_then(|()| output.flush());
        if written.is_err() {
            return ExitCode::FAILURE;
        }
    }
}
