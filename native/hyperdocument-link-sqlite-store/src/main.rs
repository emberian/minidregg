use minidregg_hyperdocument_link_sqlite_store::{
    PublishPhase, SqliteLinkStore, StoreError, MAX_RECORD_BYTES,
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
        "usage:\n  minidregg-link-sqlite-store read ROOT\n  minidregg-link-sqlite-store publish ROOT INPUT\n  minidregg-link-sqlite-store publish-crash ROOT INPUT after-begin|after-insert|after-commit\n  minidregg-link-sqlite-store publish-hold ROOT INPUT READY RELEASE\n  minidregg-link-sqlite-store database-path ROOT"
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
            ExitCode::from(1)
        }
    }
}
