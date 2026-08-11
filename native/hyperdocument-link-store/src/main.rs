use minidregg_hyperdocument_link_store::{LocalLinkStore, StoreError, MAX_RECORD_BYTES};
use std::env;
use std::fs::File;
use std::io::{self, Read, Write};
use std::path::Path;
use std::process::ExitCode;

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
        "usage:\n  minidregg-link-store read ROOT\n  minidregg-link-store stage ROOT INPUT\n  minidregg-link-store install ROOT\n  minidregg-link-store publish ROOT INPUT\n  minidregg-link-store discard-stage ROOT"
    );
    std::process::exit(2)
}

fn run() -> Result<(), StoreError> {
    let args: Vec<_> = env::args_os().skip(1).collect();
    let Some(command) = args.first().and_then(|value| value.to_str()) else {
        usage()
    };
    match (command, &args[1..]) {
        ("read", [root]) => {
            let store = LocalLinkStore::open(root)?;
            let bytes = store.read()?;
            io::stdout().write_all(&bytes)?;
        }
        ("stage", [root, input]) => {
            let store = LocalLinkStore::open(root)?;
            let bytes = read_input(Path::new(input))?;
            println!("{:?}", store.stage(&bytes)?);
        }
        ("install", [root]) => {
            let store = LocalLinkStore::open(root)?;
            println!("{:?}", store.install_staged()?);
        }
        ("publish", [root, input]) => {
            let store = LocalLinkStore::open(root)?;
            let bytes = read_input(Path::new(input))?;
            println!("{:?}", store.publish(&bytes)?);
        }
        ("discard-stage", [root]) => {
            let store = LocalLinkStore::open(root)?;
            store.discard_staged()?;
        }
        _ => usage(),
    }
    Ok(())
}

fn main() -> ExitCode {
    match run() {
        Ok(()) => ExitCode::SUCCESS,
        Err(error) => {
            eprintln!("link-store error: {error}");
            ExitCode::from(1)
        }
    }
}
