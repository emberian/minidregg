//! The Store helper's CLI and `serve` coprocess: the production verbs only.
//! The crash and hold fixtures the lifecycle tests drive live in the tests
//! (`tests/support`), never in this binary, so no caller of the deployed
//! coprocess can end or suspend it mid-transaction.
use minidregg_hyperdocument_link_sqlite_store::{
    decode_history_request, decode_nodes, encode_durable_read, encode_history_read, encode_journal_read, SqliteLinkStore, StoreError, MAX_RECORD_BYTES,
};
use std::env;
use std::fs::{self, File};
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

const USAGE: &str = "usage:\n  minidregg-link-sqlite-store read ROOT\n  minidregg-link-sqlite-store read-to ROOT OUTPUT\n  minidregg-link-sqlite-store publish ROOT INPUT\n  minidregg-link-sqlite-store cas ROOT EXPECTED|- INPUT\n  minidregg-link-sqlite-store database-path ROOT\n  minidregg-link-sqlite-store durable-anchor-enroll ROOT\n  minidregg-link-sqlite-store durable-init ROOT SEED\n  minidregg-link-sqlite-store durable-read ROOT FROM 0|1|2 OUTPUT\n  minidregg-link-sqlite-store durable-history ROOT REQUEST OUTPUT\n  minidregg-link-sqlite-store durable-seed ROOT OUTPUT\n  minidregg-link-sqlite-store durable-append ROOT HEIGHT RECORD TAG NODES\n  minidregg-link-sqlite-store durable-checkpoint ROOT HEIGHT INPUT\n  minidregg-link-sqlite-store durable-checkpoint-at ROOT HEIGHT OUTPUT\n  minidregg-link-sqlite-store journal-read ROOT FROM OUTPUT\n  minidregg-link-sqlite-store journal-append ROOT SEQ RECORD TAG\n  minidregg-link-sqlite-store serve";

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


/// The open Store of `root` under `identity`: kept for the life of this process (a `serve`
/// helper answers every request of its Host), reopened only when the database file at the root
/// is no longer the inode it opened.
fn open(root: &std::ffi::OsStr, identity: &[u8]) -> Result<std::rc::Rc<SqliteLinkStore>, StoreError> {
    use std::os::unix::fs::MetadataExt;
    thread_local! {
        static OPEN: std::cell::RefCell<Vec<(std::ffi::OsString, Vec<u8>, (u64, u64), std::rc::Rc<SqliteLinkStore>)>> =
            const { std::cell::RefCell::new(Vec::new()) };
    }
    let held = OPEN.with(|open| {
        open.borrow().iter().find(|(r, i, _, _)| r.as_os_str() == root && i.as_slice() == identity)
            .map(|(_, _, inode, store)| (*inode, store.clone()))
    });
    if let Some((inode, store)) = held {
        if fs::metadata(store.database_path()).is_ok_and(|m| (m.dev(), m.ino()) == inode) {
            return Ok(store);
        }
    }
    let store = std::rc::Rc::new(SqliteLinkStore::open_with_identity(root, identity)?);
    let meta = fs::metadata(store.database_path())?;
    OPEN.with(|open| {
        let mut open = open.borrow_mut();
        open.retain(|(r, i, _, _)| !(r.as_os_str() == root && i.as_slice() == identity));
        open.push((root.to_owned(), identity.to_vec(), (meta.dev(), meta.ino()), store.clone()));
    });
    Ok(store)
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
            let store = open(root, &identity)?;
            out.extend_from_slice(&store.read()?);
        }
        ("read-to", [root, output]) => {
            let store = open(root, &identity)?;
            let bytes = store.read()?;
            fs::write(output, bytes)?;
        }
        ("cas", [root, expected, input]) => {
            let store = open(root, &identity)?;
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
        ("publish", [root, input]) => {
            let store = open(root, &identity)?;
            writeln!(out, "{:?}", store.publish(&read_input(Path::new(input))?)?)?;
        }
        ("durable-anchor-enroll", [root]) => {
            let store = open(root, &identity)?;
            store.durable_anchor_enroll()?;
            writeln!(out, "Enrolled")?;
        }
        ("durable-init", [root, seed]) => {
            let store = open(root, &identity)?;
            writeln!(out, "{:?}", store.durable_init(&read_input(Path::new(seed))?)?)?;
        }
        ("durable-read", [root, from, with_base, output]) => {
            let from = parse_height(from)?;
            let store = open(root, &identity)?;
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
            let store = open(root, &identity)?;
            fs::write(
                output,
                encode_history_read(&store.durable_history(at, &heights, &nodes)?),
            )?;
        }
        ("durable-seed", [root, output]) => {
            let store = open(root, &identity)?;
            fs::write(output, store.durable_seed_bytes()?)?;
        }
        ("durable-append", [root, height, record, tag, nodes]) => {
            let height = parse_height(height)?;
            let store = open(root, &identity)?;
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
        ("journal-read", [root, from, output]) => {
            let from = parse_height(from)?;
            let store = open(root, &identity)?;
            fs::write(output, encode_journal_read(&store.journal_read(from)?))?;
        }
        ("journal-append", [root, seq, record, tag]) => {
            let seq = parse_height(seq)?;
            let store = open(root, &identity)?;
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
        ("durable-checkpoint-at", [root, height, output]) => {
            let height = parse_height(height)?;
            let store = open(root, &identity)?;
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
            let store = open(root, &identity)?;
            store.durable_checkpoint(height, &read_input(Path::new(input))?)?;
        }
        ("database-path", [root]) => {
            let store = open(root, &identity)?;
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
                // A bound violation is not contention (4): retrying refuses again.
                StoreError::Bound(_) => 6,
                // Full or read-only disk: distinguishable from absent (3) and opaque (1).
                StoreError::Unwritable(_) => 7,
                _ => 1,
            };
            (code, out, format!("sqlite-store error: {error}\n").into_bytes())
        }
    }
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
/// the one-shot invocation's.
/// Frames: request `u32 argc, (u32 len, bytes)*`; reply `REPLY_TAG`
/// (`MDCOPRC1`), `u32 code, u64 len, stdout, u64 len, stderr`; integers
/// big-endian. EOF ends it. The tag lets the Host refuse, by name, bytes
/// that are not a reply (`NativeCoprocess.replyTag`).
fn serve() -> ExitCode {
    use std::ffi::OsString;
    use std::io::{BufReader, BufWriter, ErrorKind};
    use std::os::unix::ffi::OsStringExt;
    const MAX_ARGS: usize = 64;
    const REPLY_TAG: &[u8; 8] = b"MDCOPRC1";
    const MAX_ARG_BYTES: usize = 64 * 1024;
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
        let (code, stdout, stderr) = std::panic::catch_unwind(|| invoke(arguments))
            .unwrap_or_else(|_| (101, Vec::new(), b"sqlite-store error: panicked\n".to_vec()));
        let written = output
            .write_all(REPLY_TAG)
            .and_then(|()| output.write_all(&code.to_be_bytes()))
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
