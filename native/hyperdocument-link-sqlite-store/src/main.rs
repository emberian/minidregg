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
        "usage:\n  minidregg-link-sqlite-store read ROOT\n  minidregg-link-sqlite-store read-to ROOT OUTPUT\n  minidregg-link-sqlite-store publish ROOT INPUT\n  minidregg-link-sqlite-store cas ROOT EXPECTED|- INPUT\n  minidregg-link-sqlite-store cas-crash ROOT EXPECTED|- INPUT after-begin|after-insert|after-commit\n  minidregg-link-sqlite-store publish-crash ROOT INPUT after-begin|after-insert|after-commit\n  minidregg-link-sqlite-store publish-hold ROOT INPUT READY RELEASE\n  minidregg-link-sqlite-store database-path ROOT\n  minidregg-link-sqlite-store durable-init ROOT SEED\n  minidregg-link-sqlite-store durable-read ROOT FROM 0|1 OUTPUT\n  minidregg-link-sqlite-store durable-append ROOT HEIGHT RECORD TAG\n  minidregg-link-sqlite-store durable-append-crash ROOT HEIGHT RECORD TAG after-begin|after-insert|after-commit\n  minidregg-link-sqlite-store durable-checkpoint ROOT HEIGHT INPUT"
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
