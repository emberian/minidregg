//! Long-lived per-replica helper session for the Lean Simplex participant.
//!
//! One process per replica. The Lean participant is the only client; it drives
//! a strict request/response protocol over the helper's stdin/stdout:
//!
//!   request  = op:u8  len:u32be body
//!   response = status:u8 len:u32be body      status 0 ok, 1 negative, 2 error
//!   blob     = len:u32be bytes                u32/u64 fields are big-endian
//!
//! It keeps the ML-DSA-65 signing key and the pairwise HMAC keys loaded, owns
//! the replica's append-only agreement journal under an exclusive lock for its
//! whole lifetime, and maintains persistent TCP connections to the peers.
//! It never parses protocol messages, counts quorums, or decides delivery:
//! inbound frames are queued verbatim and authenticated by the Lean adapter.
use crate::{mac, verify_mac, CTX, MAX_FRAME};
use fips204::{
    ml_dsa_65 as dsa,
    traits::{SerDes, Signer, Verifier},
};
use fs2::FileExt;
use std::collections::{HashMap, VecDeque};
use std::fs::{self, File, OpenOptions};
use std::io::{self, BufReader, BufWriter, Read, Seek, SeekFrom, Write};
use std::net::{TcpListener, TcpStream};
use std::os::unix::fs::OpenOptionsExt;
use std::path::{Path, PathBuf};
use std::sync::mpsc::{sync_channel, Receiver, SyncSender, TrySendError};
use std::sync::{Arc, Mutex};
use std::thread;
use std::time::Duration;

type Error = Box<dyn std::error::Error>;

const INBOUND_LIMIT: usize = 16384;
const OUTBOUND_LIMIT: usize = 4096;

pub const OP_SIGN: u8 = 1;
pub const OP_VERIFY: u8 = 2;
pub const OP_MAC: u8 = 3;
pub const OP_VERIFY_MAC: u8 = 4;
pub const OP_OPEN: u8 = 5;
pub const OP_APPEND: u8 = 6;
pub const OP_SEND: u8 = 7;
pub const OP_RECV: u8 = 8;
pub const OP_CREATE: u8 = 9;
pub const OP_REPLACE: u8 = 10;
/// Bound on one session request: a checkpoint image travels in one request.
const MAX_REQUEST: usize = 1 << 30;

struct Config {
    signing: Option<PathBuf>,
    journal: Option<PathBuf>,
    listen: Option<String>,
    peers: HashMap<u32, String>,
    pairs: HashMap<u32, PathBuf>,
}

fn parse(args: &[String]) -> Result<Config, Error> {
    let mut c = Config {
        signing: None,
        journal: None,
        listen: None,
        peers: HashMap::new(),
        pairs: HashMap::new(),
    };
    let mut i = 0;
    while i < args.len() {
        let flag = args[i].as_str();
        let value = args.get(i + 1).ok_or("session flag without value")?;
        match flag {
            "--sk" => c.signing = Some(PathBuf::from(value)),
            "--journal" => c.journal = Some(PathBuf::from(value)),
            "--listen" => c.listen = Some(value.clone()),
            "--peer" | "--pair" => {
                let (index, rest) = value.split_once('=').ok_or("expected INDEX=VALUE")?;
                let index: u32 = index.parse()?;
                if flag == "--peer" {
                    if c.peers.insert(index, rest.to_string()).is_some() {
                        return Err("duplicate peer".into());
                    }
                } else if c.pairs.insert(index, PathBuf::from(rest)).is_some() {
                    return Err("duplicate pair key".into());
                }
            }
            _ => return Err(format!("unknown session flag {flag}").into()),
        }
        i += 2;
    }
    Ok(c)
}

struct Cursor<'a> {
    bytes: &'a [u8],
}
impl<'a> Cursor<'a> {
    fn take(&mut self, n: usize) -> Result<&'a [u8], Error> {
        if self.bytes.len() < n {
            return Err("truncated request".into());
        }
        let (head, tail) = self.bytes.split_at(n);
        self.bytes = tail;
        Ok(head)
    }
    fn u32(&mut self) -> Result<u32, Error> {
        Ok(u32::from_be_bytes(self.take(4)?.try_into()?))
    }
    fn u64(&mut self) -> Result<u64, Error> {
        Ok(u64::from_be_bytes(self.take(8)?.try_into()?))
    }
    fn blob(&mut self) -> Result<&'a [u8], Error> {
        let n = self.u32()? as usize;
        if n > MAX_FRAME {
            return Err("oversize blob".into());
        }
        self.take(n)
    }
    fn rest(&mut self) -> &'a [u8] {
        std::mem::take(&mut self.bytes)
    }
    fn end(&self) -> Result<(), Error> {
        if self.bytes.is_empty() {
            Ok(())
        } else {
            Err("trailing request bytes".into())
        }
    }
}

fn blob(out: &mut Vec<u8>, b: &[u8]) {
    out.extend_from_slice(&(b.len() as u32).to_be_bytes());
    out.extend_from_slice(b);
}

/// Exclusive single-writer journal. Every acknowledged append is fsynced.
struct Journal {
    path: PathBuf,
    file: File,
    _lock: File,
    length: u64,
    poisoned: bool,
}

fn lock_for(path: &Path) -> Result<File, Error> {
    let lock = OpenOptions::new()
        .read(true)
        .write(true)
        .create(true)
        .truncate(false)
        .mode(0o600)
        .open(path.with_extension("lock"))?;
    lock.try_lock_exclusive()
        .map_err(|_| "agreement journal is held by another writer")?;
    Ok(lock)
}

fn sync_parent(path: &Path) -> Result<(), Error> {
    let dir = path.parent().ok_or("journal without parent")?;
    File::open(dir)?.sync_all()?;
    Ok(())
}

impl Journal {
    /// Open after the Lean reader decoded `observed` bytes, of which `valid`
    /// are complete frames. Only an unacknowledged torn tail is removed: the
    /// Lean reader classifies it, and the length must not have moved since.
    fn open(path: &Path, observed: u64, valid: u64) -> Result<Journal, Error> {
        if valid > observed {
            return Err("valid prefix exceeds observed journal".into());
        }
        let lock = lock_for(path)?;
        let file = OpenOptions::new().read(true).write(true).open(path)?;
        let length = file.metadata()?.len();
        if length != observed {
            return Err("journal changed between read and lock".into());
        }
        if valid < observed {
            file.set_len(valid)?;
            file.sync_all()?;
        }
        Ok(Journal { path: path.to_path_buf(), file, _lock: lock, length: valid, poisoned: false })
    }

    fn create(path: &Path, bytes: &[u8]) -> Result<Journal, Error> {
        let lock = lock_for(path)?;
        let mut file = OpenOptions::new()
            .read(true)
            .write(true)
            .create_new(true)
            .mode(0o600)
            .open(path)?;
        file.write_all(bytes)?;
        file.sync_all()?;
        sync_parent(path)?;
        Ok(Journal { path: path.to_path_buf(), file, _lock: lock, length: bytes.len() as u64, poisoned: false })
    }

    /// Checkpoint: atomically replace the whole image if its length is still
    /// `expected`. The new image is written and fsynced beside the journal,
    /// the replaced image is kept as `<journal>.upto-<length>` (a hard link:
    /// the previous segment of the input history), then the new image is
    /// renamed over the journal and the directory fsynced. The writer lock is
    /// held throughout. Any failure after the link poisons the session.
    fn replace(&mut self, expected: u64, image: &[u8]) -> Result<bool, Error> {
        if self.poisoned {
            return Err("journal session poisoned; reopen".into());
        }
        let actual = self.file.metadata()?.len();
        if expected != self.length || actual != self.length {
            return Ok(false);
        }
        let staged = self.path.with_extension("checkpoint");
        let mut file = OpenOptions::new()
            .read(true)
            .write(true)
            .create(true)
            .truncate(true)
            .mode(0o600)
            .open(&staged)?;
        file.write_all(image)?;
        file.sync_all()?;
        let mut segment = self.path.clone().into_os_string();
        segment.push(format!(".upto-{}", self.length));
        let segment = PathBuf::from(segment);
        if !segment.exists() {
            fs::hard_link(&self.path, &segment)?;
        }
        let result = (|| -> io::Result<()> {
            fs::rename(&staged, &self.path)?;
            let dir = self.path.parent().ok_or_else(|| io::Error::other("journal without parent"))?;
            File::open(dir)?.sync_all()
        })();
        if let Err(e) = result {
            self.poisoned = true;
            return Err(format!("journal checkpoint uncertain at {}: {e}", self.path.display()).into());
        }
        self.file = file;
        self.length = image.len() as u64;
        Ok(true)
    }

    /// Compare-length-and-append. A failed or partial write poisons the
    /// session: the caller must reopen and re-read the durable image.
    fn append(&mut self, expected: u64, frame: &[u8]) -> Result<bool, Error> {
        if self.poisoned {
            return Err("journal session poisoned; reopen".into());
        }
        let actual = self.file.metadata()?.len();
        if expected != self.length || actual != self.length {
            return Ok(false);
        }
        let result = (|| -> io::Result<()> {
            self.file.seek(SeekFrom::Start(self.length))?;
            self.file.write_all(frame)?;
            self.file.sync_data()
        })();
        if let Err(e) = result {
            self.poisoned = true;
            return Err(format!("journal append uncertain at {}: {e}", self.path.display()).into());
        }
        self.length += frame.len() as u64;
        Ok(true)
    }
}

fn read_frame(stream: &mut impl Read) -> io::Result<Vec<u8>> {
    let mut length = [0; 8];
    stream.read_exact(&mut length)?;
    let n = u64::from_be_bytes(length) as usize;
    if n > MAX_FRAME {
        return Err(io::Error::new(io::ErrorKind::InvalidData, "oversize frame"));
    }
    let mut frame = vec![0; n];
    stream.read_exact(&mut frame)?;
    Ok(frame)
}

fn write_frame(stream: &mut impl Write, frame: &[u8]) -> io::Result<()> {
    stream.write_all(&(frame.len() as u64).to_be_bytes())?;
    stream.write_all(frame)?;
    stream.flush()
}

type Inbound = Arc<Mutex<VecDeque<Vec<u8>>>>;

fn listen(address: &str, inbound: Inbound) -> Result<(), Error> {
    let listener = TcpListener::bind(address)?;
    thread::spawn(move || {
        for stream in listener.incoming() {
            let Ok(stream) = stream else { continue };
            let inbound = inbound.clone();
            thread::spawn(move || {
                let _ = stream.set_nodelay(true);
                let mut reader = BufReader::new(stream);
                while let Ok(frame) = read_frame(&mut reader) {
                    let mut queue = inbound.lock().unwrap();
                    // A full queue drops; the sender's retry rounds resend
                    // every retained obligation. Memory stays bounded.
                    if queue.len() < INBOUND_LIMIT {
                        queue.push_back(frame);
                    }
                }
            });
        }
    });
    Ok(())
}

/// One persistent outbound connection per peer, reconnected on failure. A
/// frame lost with a broken connection is not an acknowledgement failure:
/// the durable outbox is resent by the participant's retry schedule.
fn sender(address: String, frames: Receiver<Vec<u8>>) {
    thread::spawn(move || {
        let mut connection: Option<BufWriter<TcpStream>> = None;
        for frame in frames {
            for _attempt in 0..2 {
                if connection.is_none() {
                    let resolved = address.parse().ok();
                    let stream = resolved.and_then(|a| {
                        TcpStream::connect_timeout(&a, Duration::from_secs(2)).ok()
                    });
                    match stream {
                        Some(s) => {
                            let _ = s.set_nodelay(true);
                            let _ = s.set_write_timeout(Some(Duration::from_secs(10)));
                            connection = Some(BufWriter::new(s));
                        }
                        None => {
                            thread::sleep(Duration::from_millis(200));
                            continue;
                        }
                    }
                }
                if let Some(c) = connection.as_mut() {
                    if write_frame(c, &frame).is_ok() {
                        break;
                    }
                }
                connection = None;
            }
        }
    });
}

struct Session {
    signing: Option<dsa::PrivateKey>,
    pairs: HashMap<u32, Vec<u8>>,
    journal: Option<Journal>,
    journal_path: Option<PathBuf>,
    outbound: HashMap<u32, SyncSender<Vec<u8>>>,
    inbound: Inbound,
}

impl Session {
    fn pair(&self, peer: u32) -> Result<&[u8], Error> {
        self.pairs.get(&peer).map(|k| k.as_slice()).ok_or_else(|| "no pair key for peer".into())
    }

    fn handle(&mut self, op: u8, body: &[u8]) -> Result<(u8, Vec<u8>), Error> {
        let mut c = Cursor { bytes: body };
        let mut out = Vec::new();
        match op {
            OP_SIGN => {
                let frame = c.blob()?;
                c.end()?;
                let sk = self.signing.as_ref().ok_or("session has no signing key")?;
                let sig = sk.try_sign(frame, CTX)?;
                out.extend_from_slice(&sig);
                Ok((0, out))
            }
            OP_VERIFY => {
                let (pk, frame, sig) = (c.blob()?, c.blob()?, c.blob()?);
                c.end()?;
                let ok = (|| -> Option<bool> {
                    let pk = dsa::PublicKey::try_from_bytes(pk.try_into().ok()?).ok()?;
                    let sig: [u8; dsa::SIG_LEN] = sig.try_into().ok()?;
                    Some(pk.verify(frame, &sig, CTX))
                })()
                .unwrap_or(false);
                Ok((if ok { 0 } else { 1 }, out))
            }
            OP_MAC => {
                let peer = c.u32()?;
                let frame = c.blob()?;
                c.end()?;
                out.extend_from_slice(&mac(self.pair(peer)?, frame)?);
                Ok((0, out))
            }
            OP_VERIFY_MAC => {
                let peer = c.u32()?;
                let (frame, tag) = (c.blob()?, c.blob()?);
                c.end()?;
                let ok = match self.pairs.get(&peer) {
                    Some(key) => verify_mac(key, frame, tag)?,
                    None => false,
                };
                Ok((if ok { 0 } else { 1 }, out))
            }
            OP_OPEN | OP_CREATE => {
                if self.journal.is_some() {
                    return Err("journal already open in this session".into());
                }
                let path = self.journal_path.clone().ok_or("session has no journal")?;
                let journal = if op == OP_OPEN {
                    let (observed, valid) = (c.u64()?, c.u64()?);
                    c.end()?;
                    Journal::open(&path, observed, valid)?
                } else {
                    let bytes = c.blob()?;
                    c.end()?;
                    Journal::create(&path, bytes)?
                };
                self.journal = Some(journal);
                Ok((0, out))
            }
            OP_REPLACE => {
                let expected = c.u64()?;
                let image = c.rest();
                let journal = self.journal.as_mut().ok_or("journal not open")?;
                Ok((if journal.replace(expected, image)? { 0 } else { 1 }, out))
            }
            OP_APPEND => {
                let expected = c.u64()?;
                let frame = c.blob()?;
                c.end()?;
                let journal = self.journal.as_mut().ok_or("journal not open")?;
                Ok((if journal.append(expected, frame)? { 0 } else { 1 }, out))
            }
            OP_SEND => {
                let peer = c.u32()?;
                let packet = c.blob()?;
                c.end()?;
                let channel = self.outbound.get(&peer).ok_or("no peer address")?;
                match channel.try_send(packet.to_vec()) {
                    Ok(()) | Err(TrySendError::Full(_)) => Ok((0, out)),
                    Err(TrySendError::Disconnected(_)) => Err("peer sender stopped".into()),
                }
            }
            OP_RECV => {
                let max = c.u32()? as usize;
                c.end()?;
                let mut queue = self.inbound.lock().unwrap();
                let count = queue.len().min(max);
                out.extend_from_slice(&(count as u32).to_be_bytes());
                for frame in queue.drain(..count) {
                    blob(&mut out, &frame);
                }
                Ok((0, out))
            }
            _ => Err("unknown session operation".into()),
        }
    }
}

pub fn run(args: &[String]) -> Result<(), Error> {
    let config = parse(args)?;
    let signing = match &config.signing {
        Some(p) => Some(dsa::PrivateKey::try_from_bytes(
            fs::read(p)?.try_into().map_err(|_| "secret length")?,
        )?),
        None => None,
    };
    let mut pairs = HashMap::new();
    for (index, path) in &config.pairs {
        let key = fs::read(path)?;
        if key.len() != 32 {
            return Err("pair key must be 32 bytes".into());
        }
        pairs.insert(*index, key);
    }
    let inbound: Inbound = Arc::new(Mutex::new(VecDeque::new()));
    if let Some(address) = &config.listen {
        listen(address, inbound.clone())?;
    }
    let mut outbound = HashMap::new();
    for (index, address) in &config.peers {
        let (tx, rx) = sync_channel(OUTBOUND_LIMIT);
        sender(address.clone(), rx);
        outbound.insert(*index, tx);
    }
    let mut session = Session {
        signing,
        pairs,
        journal: None,
        journal_path: config.journal.clone(),
        outbound,
        inbound,
    };
    let stdin = io::stdin();
    let stdout = io::stdout();
    let mut input = stdin.lock();
    let mut output = BufWriter::new(stdout.lock());
    loop {
        let mut header = [0u8; 5];
        match input.read_exact(&mut header) {
            Ok(()) => {}
            Err(e) if e.kind() == io::ErrorKind::UnexpectedEof => return Ok(()),
            Err(e) => return Err(e.into()),
        }
        let n = u32::from_be_bytes(header[1..5].try_into()?) as usize;
        if n > MAX_REQUEST {
            return Err("oversize session request".into());
        }
        let mut body = vec![0; n];
        input.read_exact(&mut body)?;
        let (status, reply) = match session.handle(header[0], &body) {
            Ok(r) => r,
            Err(e) => (2, e.to_string().into_bytes()),
        };
        output.write_all(&[status])?;
        output.write_all(&(reply.len() as u32).to_be_bytes())?;
        output.write_all(&reply)?;
        output.flush()?;
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn append_is_length_checked_durable_and_exclusive() {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("agreement.log");
        let mut journal = Journal::create(&path, b"head").unwrap();
        assert!(Journal::open(&path, 4, 4).is_err(), "second writer acquired the lock");
        assert!(journal.append(4, b"-one").unwrap());
        assert!(!journal.append(4, b"-stale").unwrap(), "stale expected length accepted");
        assert!(journal.append(8, b"-two").unwrap());
        drop(journal);
        assert_eq!(fs::read(&path).unwrap(), b"head-one-two");
        // A torn tail beyond the reader's valid prefix is removed on open only.
        fs::OpenOptions::new().append(true).open(&path).unwrap().write_all(b"-to").unwrap();
        let reopened = Journal::open(&path, 15, 12).unwrap();
        assert_eq!(reopened.length, 12);
        drop(reopened);
        assert_eq!(fs::read(&path).unwrap(), b"head-one-two");
        assert!(Journal::open(&path, 11, 11).is_err(), "moved journal accepted");
    }

    #[test]
    fn replace_is_length_checked_atomic_and_keeps_the_segment() {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("agreement.log");
        let mut journal = Journal::create(&path, b"head").unwrap();
        assert!(journal.append(4, b"-one").unwrap());
        assert!(!journal.replace(4, b"stale").unwrap(), "stale expected length accepted");
        assert!(journal.replace(8, b"snap").unwrap());
        assert_eq!(fs::read(&path).unwrap(), b"snap");
        assert_eq!(fs::read(dir.path().join("agreement.log.upto-8")).unwrap(), b"head-one");
        // The session keeps writing to the new image, at its new length.
        assert!(!journal.append(8, b"-x").unwrap(), "old length accepted after replace");
        assert!(journal.append(4, b"-two").unwrap());
        drop(journal);
        assert_eq!(fs::read(&path).unwrap(), b"snap-two");
        assert!(!dir.path().join("agreement.checkpoint").exists(), "staged image left behind");
        let reopened = Journal::open(&path, 8, 8).unwrap();
        assert_eq!(reopened.length, 8);
    }

    #[test]
    fn persistent_transport_delivers_verbatim_frames() {
        let inbound: Inbound = Arc::new(Mutex::new(VecDeque::new()));
        let probe = TcpListener::bind("127.0.0.1:0").unwrap();
        let address = probe.local_addr().unwrap().to_string();
        drop(probe);
        listen(&address, inbound.clone()).unwrap();
        let (tx, rx) = sync_channel(16);
        sender(address, rx);
        for i in 0..5u8 {
            tx.send(vec![i, 255, i]).unwrap();
        }
        for _ in 0..100 {
            if inbound.lock().unwrap().len() == 5 {
                break;
            }
            thread::sleep(Duration::from_millis(20));
        }
        let got: Vec<Vec<u8>> = inbound.lock().unwrap().drain(..).collect();
        assert_eq!(got, (0..5u8).map(|i| vec![i, 255, i]).collect::<Vec<_>>());
    }

    #[test]
    fn session_crypto_matches_one_shot_helpers() {
        let (pk, sk) = dsa::try_keygen().unwrap();
        let pk = pk.into_bytes();
        let mut s = Session {
            signing: Some(sk),
            pairs: HashMap::from([(1u32, vec![7u8; 32])]),
            journal: None,
            journal_path: None,
            outbound: HashMap::new(),
            inbound: Arc::new(Mutex::new(VecDeque::new())),
        };
        let mut body = Vec::new();
        blob(&mut body, b"statement");
        let (status, sig) = s.handle(OP_SIGN, &body).unwrap();
        assert_eq!(status, 0);
        let mut v = Vec::new();
        blob(&mut v, &pk);
        blob(&mut v, b"statement");
        blob(&mut v, &sig);
        assert_eq!(s.handle(OP_VERIFY, &v).unwrap().0, 0);
        let mut w = Vec::new();
        blob(&mut w, &pk);
        blob(&mut w, b"statemenT");
        blob(&mut w, &sig);
        assert_eq!(s.handle(OP_VERIFY, &w).unwrap().0, 1);
        let mut m = 1u32.to_be_bytes().to_vec();
        blob(&mut m, b"frame");
        let (_, tag) = s.handle(OP_MAC, &m).unwrap();
        assert_eq!(tag, mac(&[7u8; 32], b"frame").unwrap());
        let mut vm = 1u32.to_be_bytes().to_vec();
        blob(&mut vm, b"frame");
        blob(&mut vm, &tag);
        assert_eq!(s.handle(OP_VERIFY_MAC, &vm).unwrap().0, 0);
        let mut wrong = 2u32.to_be_bytes().to_vec();
        blob(&mut wrong, b"frame");
        blob(&mut wrong, &tag);
        assert_eq!(s.handle(OP_VERIFY_MAC, &wrong).unwrap().0, 1, "unknown peer verified");
    }
}
