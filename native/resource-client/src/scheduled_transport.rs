//! Fixed-shape native RPC transport. This is a public-endpoint association-privacy
//! profile, NOT source anonymity. Lean still admits exact Host requests and replies.
//! A dispatch tombstone fences unknown outcomes; transport never invents a verdict.
use crate::transport;
use crate::{Args, Result};
use chacha20poly1305::{
    aead::{Aead, Payload},
    Key, KeyInit, XChaCha20Poly1305, XNonce,
};
use ring::hmac;
use sha2::{Digest, Sha256};
use std::collections::{HashMap, VecDeque};
use std::fs::{self, File, OpenOptions};
use std::io::{Read, Write};
use std::net::{TcpListener, TcpStream};
use std::os::unix::fs::{DirBuilderExt, MetadataExt, OpenOptionsExt, PermissionsExt};
use std::os::unix::net::UnixListener;
use std::path::{Path, PathBuf};
use std::sync::{
    atomic::{AtomicUsize, Ordering},
    mpsc::{self, Receiver, SyncSender},
    Arc, Mutex,
};
use std::time::{Duration, Instant};

#[path = "async_dispatch.rs"]
mod async_dispatch;
pub(crate) use async_dispatch::{AsyncDispatch, DispatchState};

const DOMAIN: &[u8] = b"Mini/native-scheduled-transport/v1";
const HEADER: usize = 42;
const TAG: usize = 16;
const MAX_ENVELOPE: usize = transport::CARRIED_LOOKUP_MAX_FRAME + transport::MAX_CONFIG + 38;
const UNCERTAIN: &[u8] = b"transport dispatch outcome uncertain; recover using native exact lookup";
// Public cycle: two application, one control, one recovery opportunity.
const SCHEDULE: [usize; 4] = [0, 0, 1, 2];

#[derive(Clone)]
struct Profile {
    cell: usize,
    tick: Duration,
    pending: usize,
    retained: usize,
    max_body: usize,
}
impl Profile {
    fn check(&self) -> Result<()> {
        if !(1024..=1024 * 1024).contains(&self.cell)
            || self.tick < Duration::from_millis(10)
            || self.tick > Duration::from_secs(60)
            || self.pending == 0
            || self.pending > 256
            || self.retained < self.pending * 4
            || self.max_body == 0
            || self.max_body > MAX_ENVELOPE
            || self.retained > 1_000_000
        {
            return Err("invalid public traffic capacity profile".into());
        }
        let cells = self.max_body.div_ceil(self.capacity()) as u64;
        // Two worst-size directions, one reserved slot in four; 30s headroom
        // under the existing native caller's public 600s deadline.
        if self
            .tick
            .as_millis()
            .checked_mul(cells as u128 * 8)
            .is_none_or(|ms| ms > 570_000)
        {
            return Err("public traffic profile exceeds native caller transfer deadline".into());
        }
        Ok(())
    }
    fn capacity(&self) -> usize {
        self.cell - HEADER - TAG
    }
    fn context(&self) -> Vec<u8> {
        let mut v = DOMAIN.to_vec();
        v.extend_from_slice(&(self.cell as u64).to_le_bytes());
        v.extend_from_slice(&(self.tick.as_millis() as u64).to_le_bytes());
        for n in [self.pending, self.retained, self.max_body] {
            v.extend_from_slice(&(n as u64).to_le_bytes());
        }
        v
    }
}
fn retained_quotas(total: usize) -> [usize; 3] {
    [total / 2, total / 4, total - total / 2 - total / 4]
}
fn scheduled_at(start: Instant, tick: Duration, index: usize) -> Result<Instant> {
    let nanos = tick
        .as_nanos()
        .checked_mul(index as u128)
        .ok_or("traffic schedule lifetime exhausted")?;
    let seconds =
        u64::try_from(nanos / 1_000_000_000).map_err(|_| "traffic schedule lifetime exhausted")?;
    start
        .checked_add(Duration::new(seconds, (nanos % 1_000_000_000) as u32))
        .ok_or_else(|| "traffic clock lifetime exhausted".into())
}

pub(crate) fn random<const N: usize>() -> Result<[u8; N]> {
    let mut v = [0; N];
    File::open("/dev/urandom")
        .and_then(|mut f| f.read_exact(&mut v))
        .map_err(|e| e.to_string())?;
    Ok(v)
}
fn id_text(id: &[u8; 16]) -> String {
    crate::hex(id)
}
pub(crate) fn directory(path: &Path) -> Result<()> {
    if !path.exists() {
        fs::DirBuilder::new()
            .recursive(true)
            .mode(0o700)
            .create(path)
            .map_err(|e| e.to_string())?;
    }
    let m = fs::symlink_metadata(path).map_err(|e| e.to_string())?;
    if !m.is_dir() || m.uid() != transport::effective_uid() || m.mode() & 0o077 != 0 {
        return Err("traffic state must be an owner-private directory".into());
    }
    Ok(())
}
pub(crate) fn read_private(path: &Path, limit: usize) -> Result<Vec<u8>> {
    let f = OpenOptions::new()
        .read(true)
        .custom_flags(libc::O_NOFOLLOW)
        .open(path)
        .map_err(|e| e.to_string())?;
    let m = f.metadata().map_err(|e| e.to_string())?;
    if !m.is_file()
        || m.uid() != transport::effective_uid()
        || m.mode() & 0o077 != 0
        || m.len() > limit as u64
    {
        return Err("traffic retained file is not bounded owner-private material".into());
    }
    let mut v = Vec::new();
    f.take((limit + 1) as u64)
        .read_to_end(&mut v)
        .map_err(|e| e.to_string())?;
    if v.len() > limit {
        return Err("traffic retained file exceeds bound".into());
    }
    Ok(v)
}
pub(crate) fn persist(path: &Path, bytes: &[u8]) -> Result<()> {
    let parent = path.parent().ok_or("traffic file has no parent")?;
    let temp = parent.join(format!(".traffic-write-{}", id_text(&random()?)));
    crate::create_private(&temp, bytes)?;
    // Publish only a fully written/fsynced file, without replacing a prior
    // immutable ticket/claim/reply. Crash-left temp files are never receipts.
    fs::hard_link(&temp, path).map_err(|e| e.to_string())?;
    fs::remove_file(&temp).map_err(|e| e.to_string())?;
    File::open(parent)
        .and_then(|f| f.sync_all())
        .map_err(|e| e.to_string())
}
fn key(path: &Path) -> Result<[u8; 32]> {
    read_private(path, 32)?
        .try_into()
        .map_err(|_| "traffic key must contain exactly 32 raw bytes".into())
}

struct Codec {
    cipher: XChaCha20Poly1305,
    seq: u64,
    size: usize,
    context: Vec<u8>,
    max_body: usize,
}
#[derive(Clone, Debug, PartialEq, Eq)]
struct Fragment {
    class: usize,
    id: [u8; 16],
    total: usize,
    offset: usize,
    bytes: Vec<u8>,
}
impl Codec {
    fn new(
        secret: &[u8; 32],
        server: &[u8; 32],
        client: &[u8; 32],
        direction: u8,
        profile: &Profile,
    ) -> Self {
        let mut context = profile.context();
        context.extend_from_slice(server);
        context.extend_from_slice(client);
        context.push(direction);
        let derived = hmac::sign(&hmac::Key::new(hmac::HMAC_SHA256, secret), &context);
        Self {
            cipher: XChaCha20Poly1305::new(Key::from_slice(derived.as_ref())),
            seq: 0,
            size: profile.cell,
            context,
            max_body: profile.max_body + 1,
        }
    }
    fn nonce(&self) -> [u8; 24] {
        let mut n = [0; 24];
        n[16..].copy_from_slice(&self.seq.to_le_bytes());
        n
    }
    fn seal(&mut self, class: usize, f: Option<&Fragment>) -> Result<Vec<u8>> {
        let mut p = vec![0; self.size - TAG];
        p[..4].copy_from_slice(b"MTC1");
        p[4..12].copy_from_slice(&self.seq.to_le_bytes());
        p[13] = class as u8;
        if let Some(f) = f {
            if f.class != class
                || class >= 3
                || f.total == 0
                || f.total > self.max_body
                || f.offset
                    .checked_add(f.bytes.len())
                    .is_none_or(|e| e > f.total)
                || f.bytes.is_empty()
                || f.bytes.len() > p.len() - HEADER
            {
                return Err("invalid traffic fragment before seal".into());
            }
            p[12] = 1;
            p[14..30].copy_from_slice(&f.id);
            p[30..34].copy_from_slice(&(f.total as u32).to_le_bytes());
            p[34..38].copy_from_slice(&(f.offset as u32).to_le_bytes());
            p[38..42].copy_from_slice(&(f.bytes.len() as u32).to_le_bytes());
            p[HEADER..HEADER + f.bytes.len()].copy_from_slice(&f.bytes);
        }
        let out = self
            .cipher
            .encrypt(
                XNonce::from_slice(&self.nonce()),
                Payload {
                    msg: &p,
                    aad: &self.context,
                },
            )
            .map_err(|_| "traffic seal failed")?;
        self.seq = self
            .seq
            .checked_add(1)
            .ok_or("traffic sequence exhausted")?;
        Ok(out)
    }
    fn open(&mut self, class: usize, cell: &[u8]) -> Result<Option<Fragment>> {
        if cell.len() != self.size {
            return Err("traffic cell length mismatch".into());
        }
        let p = self
            .cipher
            .decrypt(
                XNonce::from_slice(&self.nonce()),
                Payload {
                    msg: cell,
                    aad: &self.context,
                },
            )
            .map_err(|_| "traffic authentication, epoch or sequence refused")?;
        if p.get(..4) != Some(b"MTC1")
            || u64::from_le_bytes(p[4..12].try_into().unwrap()) != self.seq
            || p[13] as usize != class
            || class >= 3
        {
            return Err("traffic profile/sequence/class mismatch".into());
        }
        let out = match p[12] {
            0 if p[14..].iter().all(|b| *b == 0) => None,
            1 => {
                let total = u32::from_le_bytes(p[30..34].try_into().unwrap()) as usize;
                let offset = u32::from_le_bytes(p[34..38].try_into().unwrap()) as usize;
                let len = u32::from_le_bytes(p[38..42].try_into().unwrap()) as usize;
                if total == 0
                    || total > self.max_body
                    || len == 0
                    || len > p.len() - HEADER
                    || offset.checked_add(len).is_none_or(|e| e > total)
                    || p[HEADER + len..].iter().any(|b| *b != 0)
                {
                    return Err("traffic fragment bounds/padding refused before allocation".into());
                }
                Some(Fragment {
                    class,
                    id: p[14..30].try_into().unwrap(),
                    total,
                    offset,
                    bytes: p[HEADER..HEADER + len].to_vec(),
                })
            }
            _ => return Err("traffic cell kind/padding refused".into()),
        };
        self.seq = self
            .seq
            .checked_add(1)
            .ok_or("traffic sequence exhausted")?;
        Ok(out)
    }
}

#[derive(Default)]
struct Assembly {
    id: Option<[u8; 16]>,
    total: usize,
    bytes: Vec<u8>,
}
impl Assembly {
    fn push(&mut self, f: Fragment) -> Result<Option<([u8; 16], Vec<u8>)>> {
        if f.total == 0
            || f.total > MAX_ENVELOPE
            || f.bytes.is_empty()
            || f.offset
                .checked_add(f.bytes.len())
                .is_none_or(|e| e > f.total)
        {
            return Err("assembly bounds refused".into());
        }
        if self.id != Some(f.id) {
            if f.offset != 0 {
                return Err("fragment starts outside first offset".into());
            }
            self.id = Some(f.id);
            self.total = f.total;
            self.bytes.clear();
        }
        if self.total != f.total {
            return Err("fragment total changed".into());
        }
        if f.offset < self.bytes.len() {
            if self.bytes.get(f.offset..f.offset + f.bytes.len()) != Some(f.bytes.as_slice()) {
                return Err("duplicate fragment changed bytes".into());
            }
        } else if f.offset == self.bytes.len() {
            self.bytes.extend_from_slice(&f.bytes);
        } else {
            return Err("fragment gap refused".into());
        }
        if self.bytes.len() == self.total {
            let out = (f.id, std::mem::take(&mut self.bytes));
            self.id = None;
            self.total = 0;
            Ok(Some(out))
        } else {
            Ok(None)
        }
    }
}
fn fragment(class: usize, id: [u8; 16], bytes: &[u8], offset: &mut usize, cap: usize) -> Fragment {
    let end = (*offset + cap).min(bytes.len());
    let f = Fragment {
        class,
        id,
        total: bytes.len(),
        offset: *offset,
        bytes: bytes[*offset..end].to_vec(),
    };
    *offset = if end == bytes.len() { 0 } else { end };
    f
}

// Record files are immutable. The marker is fsynced BEFORE any backend effect.
// A marker without exact reply never authorizes re-dispatch, even after restart.
pub(crate) struct Journal {
    root: PathBuf,
    max: [usize; 3],
    count: [usize; 3],
}
#[derive(Debug, PartialEq, Eq)]
pub(crate) enum Admission {
    Fresh,
    Cached(Vec<u8>),
    Uncertain,
}
impl Journal {
    pub(crate) fn open(root: &Path, total: usize) -> Result<Self> {
        directory(root)?;
        let max = retained_quotas(total);
        let mut count = [0; 3];
        for e in fs::read_dir(root).map_err(|e| e.to_string())? {
            let e = e.map_err(|e| e.to_string())?;
            let name = e.file_name().to_string_lossy().into_owned();
            if let Some(stem) = name.strip_suffix(".request") {
                let class = read_private(&root.join(format!("{stem}.class")), 1)?;
                if class.len() != 1 || class[0] >= 3 {
                    return Err("retained request missing immutable class; preserve old obligations before migration".into());
                }
                count[class[0] as usize] += 1;
            }
        }
        if (0..3).any(|i| count[i] > max[i]) {
            return Err("retained traffic obligations exceed class reservation".into());
        }
        Ok(Self {
            root: root.into(),
            max,
            count,
        })
    }
    fn path(&self, id: &[u8; 16], suffix: &str) -> PathBuf {
        self.root.join(format!("{}.{}", id_text(id), suffix))
    }
    pub(crate) fn admit(&mut self, class: usize, id: &[u8; 16], bytes: &[u8]) -> Result<Admission> {
        if class >= 3 || bytes.is_empty() || bytes.len() > MAX_ENVELOPE {
            return Err("native envelope exceeds traffic admission bound".into());
        }
        let request = self.path(id, "request");
        let class_path = self.path(id, "class");
        if request.exists() {
            if read_private(&request, MAX_ENVELOPE)? != bytes
                || read_private(&class_path, 1)? != [class as u8]
            {
                return Err("traffic ticket conflicts with retained exact envelope/class".into());
            }
        } else {
            if self.count[class] >= self.max[class] {
                return Err("traffic retained class capacity exhausted before dispatch".into());
            }
            if class_path.exists() {
                if read_private(&class_path, 1)? != [class as u8] {
                    return Err("traffic retained class conflict".into());
                }
            } else {
                persist(&class_path, &[class as u8])?;
            }
            persist(&request, bytes)?;
            self.count[class] += 1;
        }
        let reply = self.path(id, "reply");
        if reply.exists() {
            return Ok(Admission::Cached(read_private(&reply, MAX_ENVELOPE + 1)?));
        }
        if self.path(id, "dispatch").exists() {
            return Ok(Admission::Uncertain);
        }
        Ok(Admission::Fresh)
    }
    pub(crate) fn claim(&self, id: &[u8; 16], bytes: &[u8]) -> Result<()> {
        persist(&self.path(id, "dispatch"), &Sha256::digest(bytes))
    }
    pub(crate) fn finish(&self, id: &[u8; 16], bytes: &[u8]) -> Result<()> {
        persist(&self.path(id, "reply"), bytes)
    }
}

struct Backend {
    journal: Journal,
    active: HashMap<[u8; 16], ()>,
    jobs: SyncSender<([u8; 16], Vec<u8>)>,
}
// A transport outcome is separate from the original Host frame. Code 0 is exact
// Host bytes, 1 is uncertain, 2 is pre-dispatch refusal. No proxy Pending verdict.
fn outcome(kind: u8, bytes: &[u8]) -> Vec<u8> {
    let mut out = vec![kind];
    out.extend_from_slice(bytes);
    out
}
fn backend_offer(
    state: &Arc<Mutex<Backend>>,
    id: [u8; 16],
    body: Vec<u8>,
    class: usize,
) -> Result<Option<Vec<u8>>> {
    let mut s = state.lock().map_err(|_| "traffic state poisoned")?;
    if s.active.contains_key(&id) {
        if read_private(&s.journal.path(&id, "request"), MAX_ENVELOPE)? != body
            || read_private(&s.journal.path(&id, "class"), 1)? != [class as u8]
        {
            return Err("active traffic ticket conflicts".into());
        }
        return Ok(None);
    }
    match s.journal.admit(class, &id, &body)? {
        Admission::Cached(bytes) => Ok(Some(bytes)),
        Admission::Uncertain => Ok(Some(outcome(1, UNCERTAIN))),
        Admission::Fresh => {
            // Queued work remains unclaimed until the worker durably marks it.
            match s.jobs.try_send((id, body)) {
                Ok(()) => {
                    s.active.insert(id, ());
                    Ok(None)
                }
                Err(mpsc::TrySendError::Full(_)) => Ok(None),
                Err(mpsc::TrySendError::Disconnected(_)) => {
                    Err("traffic backend worker stopped".into())
                }
            }
        }
    }
}
fn spawn_backend(
    root: &Path,
    profile: &Profile,
    target: &Path,
    config: &[u8],
) -> Result<Arc<Mutex<Backend>>> {
    let (jobs, rx) = mpsc::sync_channel(profile.pending);
    let state = Arc::new(Mutex::new(Backend {
        journal: Journal::open(root, profile.retained)?,
        active: HashMap::new(),
        jobs,
    }));
    let target = target.to_path_buf();
    let max_body = profile.max_body;
    let config = config.to_vec();
    let state2 = state.clone();
    std::thread::spawn(move || {
        while let Ok((id, body)) = rx.recv() {
            let claimed = state2.lock().map_err(|_| "state poisoned").and_then(|s| {
                s.journal
                    .claim(&id, &body)
                    .map_err(|_| "dispatch persistence failed")
            });
            if claimed.is_err() {
                break;
            }
            // Same public envelope gate as the native byte proxy, then the same
            // exact socket request. A transport key grants NO Mini authority.
            let reply = match transport::catalog_enabled(&config).and_then(|catalog| {
                transport::public_envelope(&body, &config, catalog).map_err(str::to_owned)
            }) {
                Err(e) => outcome(2, e.as_bytes()),
                Ok(()) => match transport::exchange_unix(&target, &body) {
                    Ok(v) if v.len() <= max_body => outcome(0, &v),
                    Ok(_) => outcome(1, UNCERTAIN),
                    Err(_) => outcome(1, UNCERTAIN),
                },
            };
            let Ok(mut s) = state2.lock() else {
                break;
            };
            if s.journal.finish(&id, &reply).is_err() {
                break;
            }
            s.active.remove(&id);
        }
    });
    Ok(state)
}

/// Called under the mailbox's private service lock. Shares the original native
/// admission gate and dispatch journal, not an alternate authority surface.
pub(crate) fn dispatch_once(
    root: &Path,
    target: &Path,
    config: &[u8],
    class: usize,
    id: [u8; 16],
    body: &[u8],
    max_reply: usize,
) -> Result<Vec<u8>> {
    let mut j = Journal::open(root, 4096)?;
    match j.admit(class, &id, body)? {
        Admission::Cached(v) => return Ok(v),
        Admission::Uncertain => return Ok(outcome(1, UNCERTAIN)),
        Admission::Fresh => (),
    }
    j.claim(&id, body)?;
    let v = match transport::catalog_enabled(config)
        .and_then(|c| transport::public_envelope(body, config, c).map_err(str::to_owned))
    {
        Err(e) => outcome(2, e.as_bytes()),
        Ok(()) => match transport::exchange_unix(target, body) {
            Ok(v) if v.len() <= max_reply => outcome(0, &v),
            _ => outcome(1, UNCERTAIN),
        },
    };
    j.finish(&id, &v)?;
    Ok(v)
}

fn handshake(
    stream: &mut TcpStream,
    secret: &[u8; 32],
    profile: &Profile,
    server_side: bool,
) -> Result<(Codec, Codec)> {
    let mut server = [0; 32];
    let mut client = [0; 32];
    if server_side {
        server = random()?;
        stream.write_all(&server).map_err(|e| e.to_string())?;
        stream.read_exact(&mut client).map_err(|e| e.to_string())?;
    } else {
        stream.read_exact(&mut server).map_err(|e| e.to_string())?;
        client = random()?;
        stream.write_all(&client).map_err(|e| e.to_string())?;
    }
    Ok((
        Codec::new(secret, &server, &client, u8::from(server_side), profile),
        Codec::new(secret, &server, &client, u8::from(!server_side), profile),
    ))
}
fn sleep_until(at: Instant) {
    if let Some(d) = at.checked_duration_since(Instant::now()) {
        std::thread::sleep(d);
    }
}
fn network(stream: &TcpStream, profile: &Profile) -> Result<()> {
    stream.set_nodelay(true).map_err(|e| e.to_string())?;
    stream
        .set_read_timeout(Some(profile.tick * 2 + Duration::from_secs(5)))
        .map_err(|e| e.to_string())?;
    stream
        .set_write_timeout(Some(profile.tick * 2 + Duration::from_secs(5)))
        .map_err(|e| e.to_string())
}
fn server_session(
    mut stream: TcpStream,
    secret: &[u8; 32],
    profile: &Profile,
    backend: &Arc<Mutex<Backend>>,
    ticks: Option<usize>,
) -> Result<()> {
    network(&stream, profile)?;
    let (mut tx, mut rx) = handshake(&mut stream, secret, profile, true)?;
    let mut assemblies: [Assembly; 3] = std::array::from_fn(|_| Assembly::default());
    let mut queries: [Option<([u8; 16], Vec<u8>)>; 3] = std::array::from_fn(|_| None);
    let mut replies: [Option<([u8; 16], Vec<u8>, usize)>; 3] = std::array::from_fn(|_| None);
    let start = Instant::now();
    let mut last_emit: Option<Instant> = None;
    for tick in 0..ticks.unwrap_or(usize::MAX) {
        let class = SCHEDULE[tick % SCHEDULE.len()];
        let at = scheduled_at(start, profile.tick, tick)?;
        let mut cell = vec![0; profile.cell];
        stream.read_exact(&mut cell).map_err(|e| e.to_string())?;
        if let Some(f) = rx.open(class, &cell)? {
            if queries[class].as_ref().is_some_and(|q| q.0 != f.id) {
                queries[class] = None;
                replies[class] = None;
            }
            if let Some((id, body)) = assemblies[class].push(f)? {
                queries[class] = Some((id, body));
            }
        }
        if let Some((id, body)) = &queries[class] {
            if replies[class].as_ref().is_none_or(|r| r.0 != *id) {
                match backend_offer(backend, *id, body.clone(), class) {
                    Ok(Some(v)) => replies[class] = Some((*id, v, 0)),
                    Ok(None) => {}
                    Err(_) => replies[class] = Some((*id, outcome(1, UNCERTAIN), 0)),
                }
            }
        }
        let f = replies[class]
            .as_mut()
            .map(|(id, body, off)| fragment(class, *id, body, off, profile.capacity()));
        // Backend completion cannot trigger an early frame or a new connection.
        let planned = at + profile.tick / 2;
        sleep_until(last_emit.map_or(planned, |last| planned.max(last + profile.tick)));
        stream
            .write_all(&tx.seal(class, f.as_ref())?)
            .map_err(|e| e.to_string())?;
        last_emit = Some(Instant::now());
    }
    Ok(())
}

struct LocalJob {
    id: [u8; 16],
    body: Vec<u8>,
    offset: usize,
    answer: Option<mpsc::Sender<Vec<u8>>>,
}
fn local_accept(
    listener: UnixListener,
    class: usize,
    root: PathBuf,
    sender: SyncSender<LocalJob>,
    max: usize,
    live: Arc<AtomicUsize>,
    retained: Arc<AtomicUsize>,
    retained_max: usize,
    max_body: usize,
) {
    for socket in listener.incoming() {
        let Ok(mut socket) = socket else {
            break;
        };
        if live.fetch_add(1, Ordering::SeqCst) >= max {
            live.fetch_sub(1, Ordering::SeqCst);
            let _ =
                transport::write_frame(&mut socket, b"\xfe traffic queue full before transmission");
            continue;
        }
        let live = live.clone();
        let retained = retained.clone();
        let sender = sender.clone();
        let root = root.clone();
        std::thread::spawn(move || {
            let mut handed_off = false;
            let mut work = || -> Result<()> {
                if transport::peer_uid(&socket)? != transport::effective_uid() {
                    return Err("traffic facade requires same-UID caller".into());
                }
                socket
                    .set_read_timeout(Some(Duration::from_secs(10)))
                    .map_err(|e| e.to_string())?;
                let body = transport::read_frame_bounded(&mut socket, max_body)
                    .map_err(|e| e.to_string())?
                    .ok_or("traffic facade closed")?;
                let id = random()?;
                if retained
                    .fetch_update(Ordering::SeqCst, Ordering::SeqCst, |n| {
                        (n < retained_max).then_some(n + 1)
                    })
                    .is_err()
                {
                    transport::write_frame(
                        &mut socket,
                        b"\xfe traffic retention full before transmission",
                    )
                    .map_err(|e| e.to_string())?;
                    return Ok(());
                }
                let mut record = vec![class as u8];
                record.extend_from_slice(&body);
                persist(&root.join(format!("{}.request", id_text(&id))), &record)?;
                let (answer, rx) = mpsc::channel();
                // A queued exact envelope survives local caller loss; no timeout
                // cancels a possibly admitted call or manufactures a new one.
                sender
                    .try_send(LocalJob {
                        id,
                        body,
                        offset: 0,
                        answer: Some(answer),
                    })
                    .map_err(|_| "traffic admission queue full before transmission")?;
                handed_off = true;
                let v = rx.recv().map_err(|_| "traffic stream uncertain")?;
                match v.first() {
                    Some(0) => {
                        transport::write_frame(&mut socket, &v[1..]).map_err(|e| e.to_string())
                    }
                    Some(2) => {
                        let mut refusal = vec![254];
                        refusal.extend_from_slice(&v[1..]);
                        transport::write_frame(&mut socket, &refusal).map_err(|e| e.to_string())
                    }
                    // Close, never return a synthetic Host refusal/absence when
                    // the backend dispatch may already have happened.
                    _ => Err("traffic backend outcome uncertain; native lookup required".into()),
                }
            };
            let _ = work();
            if !handed_off {
                live.fetch_sub(1, Ordering::SeqCst);
            }
        });
    }
}
fn recover_local(root: &Path, profile: &Profile) -> Result<[VecDeque<LocalJob>; 3]> {
    let mut queues: [VecDeque<LocalJob>; 3] = std::array::from_fn(|_| VecDeque::new());
    let mut entries: Vec<_> = fs::read_dir(root)
        .map_err(|e| e.to_string())?
        .filter_map(|e| e.ok())
        .filter(|e| e.file_name().to_string_lossy().ends_with(".request"))
        .collect();
    entries.sort_by_key(|e| e.file_name());
    if entries.len() > profile.retained {
        return Err("traffic local retention bound exceeded".into());
    }
    for entry in entries {
        let stem = entry
            .file_name()
            .to_string_lossy()
            .trim_end_matches(".request")
            .to_owned();
        let bytes = crate::decode_hex(&stem)?;
        let id: [u8; 16] = bytes.try_into().map_err(|_| "invalid retained ticket")?;
        if root.join(format!("{stem}.reply")).exists() {
            continue;
        }
        let record = read_private(&entry.path(), profile.max_body + 1)?;
        let (&class, body) = record.split_first().ok_or("empty retained request")?;
        if class >= 3 || queues[class as usize].len() >= profile.pending {
            return Err("traffic recovery queue exceeds reserved capacity".into());
        }
        queues[class as usize].push_back(LocalJob {
            id,
            body: body.to_vec(),
            offset: 0,
            answer: None,
        });
    }
    Ok(queues)
}
fn client_session(
    mut stream: TcpStream,
    secret: &[u8; 32],
    profile: &Profile,
    root: &Path,
    receivers: [Receiver<LocalJob>; 3],
    ticks: Option<usize>,
    live: &[Arc<AtomicUsize>; 3],
    mut queues: [VecDeque<LocalJob>; 3],
) -> Result<()> {
    network(&stream, profile)?;
    let (mut tx, mut rx) = handshake(&mut stream, secret, profile, false)?;
    let mut assemblies: [Assembly; 3] = std::array::from_fn(|_| Assembly::default());
    let start = Instant::now();
    let mut last_emit: Option<Instant> = None;
    for tick in 0..ticks.unwrap_or(usize::MAX) {
        let class = SCHEDULE[tick % SCHEDULE.len()];
        while queues[class].len() < profile.pending {
            match receivers[class].try_recv() {
                Ok(j) => queues[class].push_back(j),
                Err(_) => break,
            }
        }
        let f = queues[class]
            .front_mut()
            .map(|j| fragment(class, j.id, &j.body, &mut j.offset, profile.capacity()));
        let planned = scheduled_at(start, profile.tick, tick)?;
        sleep_until(last_emit.map_or(planned, |last| planned.max(last + profile.tick)));
        stream
            .write_all(&tx.seal(class, f.as_ref())?)
            .map_err(|e| e.to_string())?;
        last_emit = Some(Instant::now());
        let mut cell = vec![0; profile.cell];
        stream.read_exact(&mut cell).map_err(|e| e.to_string())?;
        if let Some(f) = rx.open(class, &cell)? {
            // An already-completed ticket may remain in the server's fixed
            // response slot until the next request arrives. Ignore it; never
            // attach its bytes to a new native request or change wire cadence.
            if queues[class].front().is_none_or(|j| j.id != f.id) {
                continue;
            }
            if let Some((id, reply)) = assemblies[class].push(f)? {
                persist(&root.join(format!("{}.reply", id_text(&id))), &reply)?;
                let j = queues[class]
                    .pop_front()
                    .ok_or("reply without active request")?;
                live[class].fetch_sub(1, Ordering::SeqCst);
                if let Some(answer) = j.answer {
                    let _ = answer.send(reply);
                }
            }
        }
    }
    Ok(())
}

fn number(args: &mut Args, name: &str, default: usize) -> Result<usize> {
    args.optional(name)
        .map(|v| {
            v.to_string_lossy()
                .parse()
                .map_err(|_| format!("invalid --{name}"))
        })
        .unwrap_or(Ok(default))
}
pub(crate) fn run(mut args: Args) -> Result<()> {
    let action = args
        .required("action")?
        .into_string()
        .map_err(|_| "invalid traffic action")?;
    let state = PathBuf::from(args.required("state")?);
    directory(&state)?;
    let _guard = transport::service_lock(&state.join("service.lock"))?;
    let secret_path = PathBuf::from(args.required("key")?);
    if action == "key" {
        args.finish()?;
        return persist(&secret_path, &random::<32>()?);
    }
    let secret = key(&secret_path)?;
    let profile = Profile {
        cell: number(&mut args, "cell-bytes", 65_536)?,
        tick: Duration::from_millis(number(&mut args, "tick-ms", 1000)? as u64),
        pending: number(&mut args, "pending", 16)?,
        retained: number(&mut args, "retained", 4096)?,
        max_body: number(&mut args, "max-envelope-bytes", 65_536)?,
    };
    profile.check()?;
    let ticks = args
        .optional("ticks")
        .map(|v| {
            v.to_string_lossy()
                .parse::<usize>()
                .map_err(|_| "invalid --ticks".to_owned())
        })
        .transpose()?;
    match action.as_str() {
        "server" => {
            let listen = args
                .required("listen")?
                .into_string()
                .map_err(|_| "invalid listen address")?;
            let target = PathBuf::from(args.required("target")?);
            let config = transport::read_config(&PathBuf::from(args.required("config")?))?;
            args.finish()?;
            let backend = spawn_backend(&state, &profile, &target, &config)?;
            let listener = TcpListener::bind(&listen).map_err(|e| e.to_string())?;
            // One independently provisioned peer/profile per listener. Many
            // profiles compose as separate services; no shared cohort PSK.
            for stream in listener.incoming() {
                let stream = stream.map_err(|e| e.to_string())?;
                if let Err(error) = server_session(stream, &secret, &profile, &backend, ticks) {
                    eprintln!("traffic session closed: {error}");
                }
                if ticks.is_some() {
                    break;
                }
            }
            Ok(())
        }
        "client" => {
            let connect = args
                .required("connect")?
                .into_string()
                .map_err(|_| "invalid connect address")?;
            let socket = PathBuf::from(args.required("local-socket")?);
            args.finish()?;
            let queues = recover_local(&state, &profile)?;
            let live: [Arc<AtomicUsize>; 3] =
                std::array::from_fn(|class| Arc::new(AtomicUsize::new(queues[class].len())));
            let mut retained_count = [0; 3];
            for entry in fs::read_dir(&state).map_err(|e| e.to_string())? {
                let entry = entry.map_err(|e| e.to_string())?;
                if entry.file_name().to_string_lossy().ends_with(".request") {
                    let record = read_private(&entry.path(), profile.max_body + 1)?;
                    let class = *record.first().ok_or("empty retained request")? as usize;
                    if class >= 3 {
                        return Err("invalid retained class".into());
                    }
                    retained_count[class] += 1;
                }
            }
            let quotas = retained_quotas(profile.retained);
            if (0..3).any(|c| retained_count[c] > quotas[c]) {
                return Err("retained local class exceeds profile; preserve obligations".into());
            }
            let retained: [Arc<AtomicUsize>; 3] =
                std::array::from_fn(|c| Arc::new(AtomicUsize::new(retained_count[c])));
            let mut receivers = Vec::new();
            for class in 0..3 {
                let address = if class == 0 {
                    socket.clone()
                } else {
                    PathBuf::from(format!(
                        "{}.{}",
                        socket.display(),
                        if class == 1 { "control" } else { "repair" }
                    ))
                };
                transport::clear_stale_socket(&address)?;
                let listener = UnixListener::bind(&address).map_err(|e| e.to_string())?;
                fs::set_permissions(&address, fs::Permissions::from_mode(0o600))
                    .map_err(|e| e.to_string())?;
                let (tx, rx) = mpsc::sync_channel(profile.pending);
                receivers.push(rx);
                let root = state.clone();
                let max = profile.pending;
                let live_class = live[class].clone();
                let retained = retained[class].clone();
                let retained_max = quotas[class];
                let max_body = profile.max_body;
                std::thread::spawn(move || {
                    local_accept(
                        listener,
                        class,
                        root,
                        tx,
                        max,
                        live_class,
                        retained,
                        retained_max,
                        max_body,
                    )
                });
            }
            let stream = TcpStream::connect(connect).map_err(|e| e.to_string())?;
            client_session(
                stream,
                &secret,
                &profile,
                &state,
                receivers.try_into().map_err(|_| "receiver count")?,
                ticks,
                &live,
                queues,
            )
        }
        _ => Err("traffic --action must be key, server or client".into()),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    fn profile() -> Profile {
        Profile {
            cell: 1024,
            tick: Duration::from_millis(10),
            pending: 4,
            retained: 32,
            max_body: 65_536,
        }
    }
    fn codecs(direction: u8) -> (Codec, Codec) {
        (
            Codec::new(&[5; 32], &[1; 32], &[2; 32], direction, &profile()),
            Codec::new(&[5; 32], &[1; 32], &[2; 32], direction, &profile()),
        )
    }
    fn scratch() -> PathBuf {
        let p = std::env::temp_dir().join(format!(
            "mini-traffic-{}-{}",
            std::process::id(),
            id_text(&random().unwrap())
        ));
        directory(&p).unwrap();
        p
    }
    #[test]
    fn long_resident_schedule_and_deadline_profile_refuse_without_wrap() {
        let start = Instant::now();
        let n = u32::MAX as usize + 9;
        assert_eq!(
            scheduled_at(start, Duration::from_millis(10), n)
                .unwrap()
                .duration_since(start),
            Duration::from_millis(10 * n as u64)
        );
        let mut p = profile();
        p.check().unwrap();
        p.max_body = MAX_ENVELOPE;
        assert!(p.check().is_err());
        p.cell = 65_536;
        p.check().unwrap();
        p.tick = Duration::from_secs(1);
        assert!(p.check().is_err());
    }
    #[test]
    fn application_retention_cannot_consume_control_or_recovery() {
        let root = scratch();
        let mut j = Journal::open(&root, 8).unwrap();
        for i in 0..4 {
            j.admit(0, &[i; 16], b"body").unwrap();
        }
        assert!(j.admit(0, &[9; 16], b"new").is_err());
        assert_eq!(j.admit(1, &[10; 16], b"control").unwrap(), Admission::Fresh);
        assert_eq!(
            j.admit(2, &[11; 16], b"recovery").unwrap(),
            Admission::Fresh
        );
        drop(j);
        Journal::open(&root, 8).unwrap();
        fs::remove_dir_all(root).unwrap();
    }
    #[test]
    fn equal_shape_active_cells_replay_tamper_direction_and_epoch_refuse() {
        let (mut tx, mut rx) = codecs(0);
        let f = Fragment {
            class: 0,
            id: [3; 16],
            total: 3,
            offset: 0,
            bytes: b"abc".to_vec(),
        };
        let pad = tx.seal(0, None).unwrap();
        let real = tx.seal(0, Some(&f)).unwrap();
        assert_eq!(pad.len(), real.len());
        assert_eq!(rx.open(0, &pad).unwrap(), None);
        assert_eq!(rx.open(0, &real).unwrap(), Some(f));
        assert!(rx.open(0, &real).is_err());
        let mut wrong_direction = Codec::new(&[5; 32], &[1; 32], &[2; 32], 1, &profile());
        assert!(wrong_direction.open(0, &pad).is_err());
        let mut old_epoch = Codec::new(&[5; 32], &[9; 32], &[2; 32], 0, &profile());
        assert!(old_epoch.open(0, &pad).is_err());
        let (_, mut fresh) = codecs(0);
        let mut bad = pad;
        bad[50] ^= 1;
        assert!(fresh.open(0, &bad).is_err());
    }
    #[test]
    fn fragment_bounds_conflict_and_full_native_bytes() {
        let body: Vec<u8> = (0..65_600).map(|i| (i % 251) as u8).collect();
        let mut offset = 0;
        let mut a = Assembly::default();
        loop {
            let f = fragment(2, [4; 16], &body, &mut offset, profile().capacity());
            if let Some((id, out)) = a.push(f).unwrap() {
                assert_eq!(id, [4; 16]);
                assert_eq!(out, body);
                break;
            }
        }
        let mut a = Assembly::default();
        let f = Fragment {
            class: 0,
            id: [2; 16],
            total: 8,
            offset: 0,
            bytes: b"abcd".to_vec(),
        };
        a.push(f.clone()).unwrap();
        assert!(a
            .push(Fragment {
                bytes: b"abce".to_vec(),
                ..f
            })
            .is_err());
        assert!(a
            .push(Fragment {
                class: 0,
                id: [9; 16],
                total: MAX_ENVELOPE + 1,
                offset: 0,
                bytes: vec![1]
            })
            .is_err());
    }
    #[test]
    fn durable_dispatch_marker_never_authorizes_second_effect() {
        let root = scratch();
        let id = [4; 16];
        let body = b"exact native signed ingress";
        let mut j = Journal::open(&root, 8).unwrap();
        assert_eq!(j.admit(0, &id, body).unwrap(), Admission::Fresh);
        j.claim(&id, body).unwrap();
        drop(j);
        let mut restored = Journal::open(&root, 8).unwrap();
        assert_eq!(restored.admit(0, &id, body).unwrap(), Admission::Uncertain);
        assert!(restored.admit(0, &id, b"changed body").is_err());
        let exact = outcome(0, b"exact native receipt");
        restored.finish(&id, &exact).unwrap();
        drop(restored);
        assert_eq!(
            Journal::open(&root, 8)
                .unwrap()
                .admit(0, &id, body)
                .unwrap(),
            Admission::Cached(exact)
        );
        fs::remove_dir_all(root).unwrap();
    }
    #[test]
    fn native_public_gate_and_cached_backend_reply_are_preserved() {
        let root = scratch();
        let target = root.join("backend.sock");
        let listener = UnixListener::bind(&target).unwrap();
        let config = b"{}";
        let calls = Arc::new(AtomicUsize::new(0));
        let counted = calls.clone();
        let fake = std::thread::spawn(move || {
            let (mut s, _) = listener.accept().unwrap();
            let frame = transport::read_frame(&mut s).unwrap().unwrap();
            assert_eq!(
                frame,
                [vec![1, 2, 0, 0, 0], b"{}".to_vec(), vec![12]].concat()
            );
            counted.fetch_add(1, Ordering::SeqCst);
            transport::write_frame(&mut s, b"\x0csource-owned-reply").unwrap();
        });
        let state = spawn_backend(&root, &profile(), &target, config).unwrap();
        let id = [1; 16];
        let body = [vec![1, 2, 0, 0, 0], config.to_vec(), vec![12]].concat();
        assert_eq!(backend_offer(&state, id, body.clone(), 0).unwrap(), None);
        let result = loop {
            if let Some(v) = backend_offer(&state, id, body.clone(), 0).unwrap() {
                break v;
            }
            std::thread::sleep(Duration::from_millis(1));
        };
        assert_eq!(result, outcome(0, b"\x0csource-owned-reply"));
        assert_eq!(backend_offer(&state, id, body, 0).unwrap(), Some(result));
        fake.join().unwrap();
        assert_eq!(calls.load(Ordering::SeqCst), 1);
        drop(state);
        fs::remove_dir_all(root).unwrap();
    }
    #[test]
    fn repair_slots_are_reserved_even_with_application_backlog() {
        assert_eq!(SCHEDULE.iter().filter(|c| **c == 0).count(), 2);
        assert_eq!(SCHEDULE.iter().filter(|c| **c == 1).count(), 1);
        assert_eq!(SCHEDULE.iter().filter(|c| **c == 2).count(), 1);
        let (mut tx, mut rx) = codecs(0);
        for class in SCHEDULE.into_iter().cycle().take(40) {
            let f = Fragment {
                class,
                id: [class as u8; 16],
                total: 1,
                offset: 0,
                bytes: vec![1],
            };
            let cell = tx.seal(class, Some(&f)).unwrap();
            assert_eq!(rx.open(class, &cell).unwrap(), Some(f));
        }
    }
    #[test]
    fn native_duplex_round_trip_all_three_classes_and_idle_tail() {
        let root = scratch();
        let server_root = root.join("server");
        let client_root = root.join("client");
        directory(&server_root).unwrap();
        directory(&client_root).unwrap();
        let target = root.join("host.sock");
        let listener = UnixListener::bind(&target).unwrap();
        let expected: Vec<Vec<u8>> = (0..3)
            .map(|class| {
                let mut body = vec![2, 2, 0, 0, 0];
                body.extend_from_slice(b"{}");
                body.extend_from_slice(&[7; 32]);
                body.push(0);
                body.extend((0..2500 + class).map(|i| (i % 251) as u8));
                body
            })
            .collect();
        let copies = expected.clone();
        let host = std::thread::spawn(move || {
            for _ in 0..3 {
                let (mut s, _) = listener.accept().unwrap();
                let body = transport::read_frame(&mut s).unwrap().unwrap();
                assert!(copies.contains(&body));
                let mut reply = vec![0];
                reply.extend_from_slice(&body);
                transport::write_frame(&mut s, &reply).unwrap();
            }
        });
        let p = Profile {
            cell: 1024,
            tick: Duration::from_millis(10),
            pending: 4,
            retained: 32,
            max_body: 65_536,
        };
        let backend = spawn_backend(&server_root, &p, &target, b"{}").unwrap();
        let tcp = TcpListener::bind("127.0.0.1:0").unwrap();
        let address = tcp.local_addr().unwrap();
        let server_p = p.clone();
        let server = std::thread::spawn(move || {
            let (stream, _) = tcp.accept().unwrap();
            server_session(stream, &[8; 32], &server_p, &backend, Some(40)).unwrap();
        });
        let mut receivers = Vec::new();
        let mut answers = Vec::new();
        let queues = std::array::from_fn(|_| VecDeque::new());
        let live = std::array::from_fn(|_| Arc::new(AtomicUsize::new(1)));
        for (class, body) in expected.iter().enumerate() {
            let (tx, rx) = mpsc::sync_channel(4);
            let (answer, wait) = mpsc::channel();
            let id = [class as u8 + 1; 16];
            let mut record = vec![class as u8];
            record.extend_from_slice(body);
            persist(
                &client_root.join(format!("{}.request", id_text(&id))),
                &record,
            )
            .unwrap();
            tx.send(LocalJob {
                id,
                body: body.clone(),
                offset: 0,
                answer: Some(answer),
            })
            .unwrap();
            receivers.push(rx);
            answers.push(wait);
        }
        client_session(
            TcpStream::connect(address).unwrap(),
            &[8; 32],
            &p,
            &client_root,
            receivers.try_into().ok().unwrap(),
            Some(40),
            &live,
            queues,
        )
        .unwrap();
        for (class, wait) in answers.into_iter().enumerate() {
            let result = wait.recv().unwrap();
            let mut exact = vec![0, 0];
            exact.extend_from_slice(&expected[class]);
            assert_eq!(result, exact);
            assert_eq!(live[class].load(Ordering::SeqCst), 0);
        }
        host.join().unwrap();
        server.join().unwrap();
        fs::remove_dir_all(root).unwrap();
    }
    #[test]
    fn retention_pressure_never_erases_accepted_dispatch() {
        let root = scratch();
        let mut j = Journal::open(&root, 2).unwrap();
        let id = [1; 16];
        j.admit(0, &id, b"accepted").unwrap();
        j.claim(&id, b"accepted").unwrap();
        assert!(j.admit(0, &[2; 16], b"new").is_err());
        assert_eq!(j.admit(0, &id, b"accepted").unwrap(), Admission::Uncertain);
        fs::remove_dir_all(root).unwrap();
    }
}
