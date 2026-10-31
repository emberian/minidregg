//! External monotonic anchor: must be a separate rollback authority, not another
//! path controlled by the snapshot owner. The local Unix service tests IO only.
use crate::codec::*;
use crate::transition_journal as wal;
use sha2::{Digest, Sha256};
use std::fs::{self, File, OpenOptions};
use std::io::{Error, Read, Result, Write};
use std::sync::atomic::{AtomicBool, Ordering};
use std::os::unix::{
    fs::{OpenOptionsExt, PermissionsExt},
    io::AsRawFd,
    net::{UnixListener, UnixStream},
};
use std::path::Path;
pub fn hash(b: &[u8]) -> [u8; 32] {
    Sha256::digest(b).into()
}
fn create(p: &Path) -> Result<File> {
    OpenOptions::new()
        .write(true)
        .create_new(true)
        .mode(0o600)
        .open(p)
}
fn nonce() -> Result<u64> {
    let mut b = [0; 8];
    crate::entropy::os_fill(&mut b)?;
    Ok(u64::from_le_bytes(b))
}
pub(crate) fn snapshot(p: &Path, b: &[u8]) -> Result<()> {
    let tmp = p.with_extension(format!("pending-{}-{}", std::process::id(), nonce()?));
    let mut f = create(&tmp)?;
    f.write_all(b)?;
    fs::rename(&tmp, p)?;
    Ok(())
}
pub(crate) fn read_packet(s: &mut UnixStream) -> Result<Vec<u8>> {
    let mut l = [0; 4];
    s.read_exact(&mut l)?;
    let n = u32::from_le_bytes(l) as usize;
    if n > MAX {
        return Err(bad("packet bound"));
    }
    let mut b = vec![0; n];
    s.read_exact(&mut b)?;
    Ok(b)
}
pub(crate) fn write_packet(s: &mut UnixStream, b: &[u8]) -> Result<()> {
    if b.len() > MAX {
        return Err(bad("packet bound"));
    }
    s.write_all(&(b.len() as u32).to_le_bytes())?;
    s.write_all(b)?;
    s.flush()
}
pub(crate) fn lock(p: &Path) -> Result<File> {
    let f = OpenOptions::new()
        .read(true)
        .write(true)
        .create(true)
        .truncate(false)
        .mode(0o600)
        .open(p)?;
    if unsafe { libc::flock(f.as_raw_fd(), libc::LOCK_EX | libc::LOCK_NB) } != 0 {
        return Err(Error::last_os_error());
    }
    Ok(f)
}
/// The anchor's state machine: events are canonical batch reservation
/// requests, the outbox is the digest of the resulting journal. The WAL record
/// is therefore linear in the request, never the whole journal.
#[derive(Clone, Default)]
struct AnchorMachine {
    journal: Journal,
}
impl wal::Machine for AnchorMachine {
    fn apply(&mut self, event: &[u8]) -> Result<Vec<u8>> {
        let (ids, g, p) = parse_batch_request(event)?;
        if batch_request(&ids, &g, p) != event {
            return Err(bad("authority request canonical"));
        }
        self.journal = self.journal.reserve_batch(&ids, g, p)?;
        Ok(hash(&self.journal.encode()).to_vec())
    }
}
pub struct Anchor {
    wal: wal::Journal<AnchorMachine>,
}
impl Anchor {
    pub fn open(root: &Path) -> Result<Self> {
        fs::create_dir_all(root)?;
        fs::set_permissions(root, fs::Permissions::from_mode(0o700))?;
        Ok(Self {
            wal: wal::Journal::open(
                &root.join("authority.log"),
                b"DREGG.PRIVATE.ANCHOR.WAL.V2",
                AnchorMachine::default(),
            )?,
        })
    }
    pub fn journal(&self) -> &Journal {
        &self.wal.state().journal
    }
    /// The final record recovery dropped as a crash tear, if any. It was never
    /// answered: a reply follows the completed write.
    pub fn torn_tail(&self) -> Option<&wal::TornTail> {
        self.wal.torn_tail()
    }
    pub fn reserve(&mut self, id: Correlation, g: Generation, p: Purpose) -> Result<Vec<u8>> {
        self.reserve_batch(&[id], g, p)
    }
    pub fn reserve_batch(
        &mut self,
        ids: &[Correlation],
        g: Generation,
        p: Purpose,
    ) -> Result<Vec<u8>> {
        self.wal.append(&batch_request(ids, &g, p))?;
        Ok(self.journal().encode())
    }
    pub fn handle(&mut self, b: &[u8]) -> Result<Vec<u8>> {
        if self.wal.is_poisoned() {
            return Err(bad("authority uncertain"));
        }
        match b.split_first() {
            Some((0, [])) => Ok(self.journal().encode()),
            Some((1, b)) => {
                let (id, g, p) = parse_request(b)?;
                self.reserve(id, g, p)
            }
            Some((2, b)) => {
                let (ids, g, p) = parse_batch_request(b)?;
                self.reserve_batch(&ids, g, p)
            }
            _ => Err(bad("anchor request")),
        }
    }
}
/// The one reserve-and-receipt step behind a preparation burn and a one-use
/// output reservation, recoverable after a lost reply the way a transition
/// journal step is. Under `lock_path`: persist the exact request (`receipt`
/// prefix and `request`) at `local.intent` before sending it; read the anchor.
/// If the anchor already holds this batch for exactly this generation and
/// purpose AND the retained intent is this very request, the earlier reply was
/// lost: the anchor's own journal is the answer and nothing is sent or recorded
/// again. A batch held without a matching retained intent is somebody else's
/// (a replaced descriptor, a relabel) and refuses as before. A retained intent
/// that differs, with nothing yet reserved, is superseded. Then check the
/// journal retains every row unconsumed and only extends what was read,
/// persist `prefix || journal` at `local`, read it back, and re-read the anchor.
pub(crate) fn reserve_with_receipt(
    lock_path: &Path,
    request: &[u8],
    ids: &[Correlation],
    g: &Generation,
    purpose: Purpose,
    mut receipt: Vec<u8>,
    anchor: &Path,
    local: &Path,
    what: &str,
) -> Result<(Journal, Vec<u8>)> {
    let _guard = lock(lock_path)?;
    let intent_path = local.with_extension("intent");
    let mut intent = receipt.clone();
    bytes(request, &mut intent);
    let retained = fs::read(&intent_path).ok();
    let before = Journal::decode(&rpc(anchor, &[0])?)?;
    let held = before.holds_batch(ids, g, purpose);
    let confirmed = if held && retained.as_deref() == Some(&intent[..]) {
        before.clone()
    } else {
        if !held {
            if retained.as_deref() != Some(&intent[..]) {
                snapshot(&intent_path, &intent)?;
            }
        }
        before.reserve_batch(ids, g.clone(), purpose)?;
        Journal::decode(&rpc(anchor, request)?)?
    };
    let indexed = confirmed
        .allocations
        .iter()
        .map(|a| (&a.id, a))
        .collect::<std::collections::BTreeMap<_, _>>();
    if !confirmed.extends(&before)
        || !confirmed.preserves_allocations(&before)
        || ids.iter().any(|id| {
            indexed
                .get(id)
                .is_none_or(|a| a.generation != *g || a.purpose != purpose || a.consumed)
        })
    {
        return Err(bad(&format!("{what} allocation binding/retention")));
    }
    bytes(&confirmed.encode(), &mut receipt);
    snapshot(local, &receipt)?;
    if fs::read(local)? != receipt {
        return Err(bad(&format!("{what} durable readback")));
    }
    let latest = Journal::decode(&rpc(anchor, &[0])?)?;
    if !latest.extends(&confirmed) || !latest.preserves_allocations(&confirmed) {
        return Err(bad(&format!("{what} anchor regression")));
    }
    Ok((confirmed, receipt))
}
/// The one anchor loop. Accept blocks; `stop` is checked after every accept, so
/// a stopper sets it and then connects once to the listener's own address (the
/// wake connection is dropped unread). On return the Anchor, and with it the
/// authority lock, is dropped.
pub fn serve(mut a: Anchor, listener: UnixListener, stop: &AtomicBool) -> Result<()> {
    loop {
        let (mut s, _) = listener.accept()?;
        if stop.load(Ordering::SeqCst) {
            return Ok(());
        }
        s.set_read_timeout(Some(std::time::Duration::from_secs(10)))?;
        s.set_write_timeout(Some(std::time::Duration::from_secs(10)))?;
        let answer = (|| {
            let b = read_packet(&mut s)?;
            a.handle(&b)
        })();
        let mut response = vec![];
        match answer {
            Ok(b) => {
                response.push(0);
                response.extend(b)
            }
            Err(e) => {
                response.push(1);
                response.extend(e.to_string().as_bytes());
            }
        }
        let _ = write_packet(&mut s, &response);
    }
}
pub fn run_anchor(root: &Path, socket: &Path) -> Result<()> {
    let a = Anchor::open(root)?;
    let listener = UnixListener::bind(socket)?;
    fs::set_permissions(socket, fs::Permissions::from_mode(0o600))?;
    serve(a, listener, &AtomicBool::new(false))
}
pub(crate) fn rpc(socket: &Path, b: &[u8]) -> Result<Vec<u8>> {
    let mut s = UnixStream::connect(socket)?;
    s.set_read_timeout(Some(std::time::Duration::from_secs(10)))?;
    s.set_write_timeout(Some(std::time::Duration::from_secs(10)))?;
    write_packet(&mut s, b)?;
    let a = read_packet(&mut s)?;
    match a.split_first() {
        Some((0, b)) => Ok(b.to_vec()),
        Some((1, b)) => Err(Error::other(String::from_utf8_lossy(b).to_string())),
        _ => Err(bad("anchor reply")),
    }
}
/// In-process anchor for tests: the real `serve` loop on a thread. Drop sets
/// `stop`, wakes the blocked accept with one connection to the socket, and joins,
/// so the authority lock frees for a reopen. Fault that must turn this red: remove
/// the wake connect and drop hangs in join, so the kill9 and Cluster::open reopen
/// tests time out.
#[cfg(any(test, feature = "demo"))]
pub(crate) struct AnchorHandle {
    sock: std::path::PathBuf,
    stop: std::sync::Arc<AtomicBool>,
    task: Option<std::thread::JoinHandle<()>>,
}
#[cfg(any(test, feature = "demo"))]
impl AnchorHandle {
    /// Serve the authority kept under `root`/authority on `root`/anchor.sock. A
    /// socket file left by a killed predecessor is removed first.
    pub(crate) fn new(root: &Path) -> Self {
        let sock = root.join("anchor.sock");
        let _ = fs::remove_file(&sock);
        let a = Anchor::open(&root.join("authority")).unwrap();
        let listener = UnixListener::bind(&sock).unwrap();
        let stop = std::sync::Arc::new(AtomicBool::new(false));
        let halt = stop.clone();
        let task = std::thread::spawn(move || serve(a, listener, &halt).unwrap());
        Self {
            sock,
            stop,
            task: Some(task),
        }
    }
    pub(crate) fn socket(&self) -> &Path {
        &self.sock
    }
}
#[cfg(any(test, feature = "demo"))]
impl Drop for AnchorHandle {
    fn drop(&mut self) {
        self.stop.store(true, Ordering::SeqCst);
        let _ = UnixStream::connect(&self.sock);
        self.task.take().unwrap().join().unwrap();
    }
}
#[cfg(test)]
mod tests {
    use super::*;
    use std::path::PathBuf;
    fn temp(label: &str) -> PathBuf {
        std::env::temp_dir().join(format!(
            "mini-backend-{label}-{}-{}",
            std::process::id(),
            nonce().unwrap()
        ))
    }
    fn g() -> Generation {
        Generation {
            invocation: Nat::new(7),
            command: vec![9],
            attempt: Nat::new(0),
            generation: Nat::new(1),
            configuration: Nat::new(2),
        }
    }
    #[test]
    fn full_controller_sized_batch_is_single_durable_record_and_preserves_old_rows() {
        let p = temp("batch-9418");
        let old = Correlation {
            pool: Nat::new(9),
            row: Nat::new(0),
        };
        let rows = (0..9418)
            .map(|i| Correlation {
                pool: Nat::new(42),
                row: Nat::new(i),
            })
            .collect::<Vec<_>>();
        let (first_len, full_len, expected);
        {
            let mut a = Anchor::open(&p).unwrap();
            let first = a.reserve(old.clone(), g(), Purpose::Coin).unwrap();
            first_len = first.len();
            let log_before = fs::metadata(p.join("authority.log")).unwrap().len();
            let mut req = vec![2];
            req.extend(batch_request(&rows, &g(), Purpose::Triple));
            let full = a.handle(&req).unwrap();
            full_len = full.len();
            expected = Journal::decode(&full).unwrap();
            assert_eq!(expected.spent.len(), 9419);
            assert_eq!(
                &expected.spent[..9418],
                rows.iter().rev().cloned().collect::<Vec<_>>()
            );
            let _ = (first_len, full_len);
            let grown = fs::metadata(p.join("authority.log")).unwrap().len() - log_before;
            let mut record = vec![];
            bytes(&batch_request(&rows, &g(), Purpose::Triple), &mut record);
            bytes(&hash(&full), &mut record);
            assert_eq!(
                grown as usize,
                8 + record.len() + 32,
                "one complete append for the whole fixed Plan, linear in the request: \
                 the record never carries the journal"
            );
            let before = a.journal().clone();
            assert!(a
                .reserve_batch(
                    &[
                        Correlation {
                            pool: Nat::new(43),
                            row: Nat::new(0)
                        },
                        rows[0].clone()
                    ],
                    g(),
                    Purpose::AudiencePad
                )
                .is_err());
            assert_eq!(
                a.journal(), &before,
                "all-row preflight must not partially consume a refused batch"
            );
        }
        let mut a = Anchor::open(&p).unwrap();
        assert_eq!(
            a.journal(), &expected,
            "lost response/restart preserves exact completed batch"
        );
        assert!(a.reserve_batch(&rows, g(), Purpose::Triple).is_err());
        assert!(a.reserve(old, g(), Purpose::Triple).is_err());
        drop(a);
        // A checksum fault inside an EARLIER record is damage to published
        // history, never a tear: hard refusal, file untouched.
        let log = fs::read(p.join("authority.log")).unwrap();
        let mut last = vec![];
        bytes(&batch_request(&rows, &g(), Purpose::Triple), &mut last);
        bytes(&hash(&expected.encode()), &mut last);
        let first_checksum_end = log.len() - (8 + last.len() + 32);
        let mut bad = log.clone();
        bad[first_checksum_end - 1] ^= 1;
        fs::write(p.join("authority.log"), &bad).unwrap();
        assert!(Anchor::open(&p).is_err(), "interior checksum fault refuses");
        assert_eq!(fs::read(p.join("authority.log")).unwrap(), bad);
        // The same fault in the FINAL record is the tear shape: dropped and
        // reported, the earlier reservation survives.
        let mut tail = log.clone();
        *tail.last_mut().unwrap() ^= 1;
        fs::write(p.join("authority.log"), &tail).unwrap();
        let a = Anchor::open(&p).unwrap();
        assert!(a.torn_tail().is_some());
        assert_eq!(a.journal().spent.len(), 1);
    }
    #[test]
    fn lost_reply_and_relabel() {
        let p = temp("anchor");
        let id = Correlation {
            pool: Nat::new(42),
            row: Nat::new(0),
        };
        {
            let mut a = Anchor::open(&p).unwrap();
            a.reserve(id.clone(), g(), Purpose::Triple).unwrap();
        }
        let mut a = Anchor::open(&p).unwrap();
        let mut other = g();
        other.attempt = Nat::new(77);
        assert!(a.reserve(id, other, Purpose::AudiencePad).is_err());
        assert_eq!(a.journal().spent.len(), 1);
    }
    #[test]
    fn torn_anchor_tail_recovers_at_every_cut_and_the_anchor_keeps_serving() {
        let p = temp("torn");
        let id = |n: u64| Correlation {
            pool: Nat::new(42),
            row: Nat::new(n),
        };
        let (prefix, full);
        {
            let mut a = Anchor::open(&p).unwrap();
            a.reserve(id(0), g(), Purpose::Triple).unwrap();
            prefix = fs::read(p.join("authority.log")).unwrap();
            a.reserve(id(1), g(), Purpose::Triple).unwrap();
            full = fs::read(p.join("authority.log")).unwrap();
        }
        for cut in prefix.len()..full.len() {
            let q = temp("torn-cut");
            fs::create_dir_all(&q).unwrap();
            fs::write(q.join("authority.log"), &full[..cut]).unwrap();
            let mut a = Anchor::open(&q).unwrap();
            assert_eq!(a.journal().spent.len(), 1, "cut {cut}");
            assert_eq!(a.torn_tail().is_some(), cut > prefix.len(), "cut {cut}");
            // The torn reservation was never answered, so it is free again.
            a.reserve(id(1), g(), Purpose::Triple).unwrap();
            drop(a);
            assert_eq!(Anchor::open(&q).unwrap().journal().spent.len(), 2);
        }
    }
    #[test]
    fn singleton_authority() {
        let p = temp("lock");
        let _a = Anchor::open(&p).unwrap();
        assert!(Anchor::open(&p).is_err());
    }
    fn ids(n: u64) -> Vec<Correlation> {
        (0..n)
            .map(|row| Correlation {
                pool: Nat::new(42),
                row: Nat::new(row),
            })
            .collect()
    }
    /// A reserve whose reply was lost leaves the anchor holding the batch and
    /// the caller without a receipt. Resubmitting the retained request returns
    /// the same receipt and records nothing again, for a batch burn and for a
    /// single one-use reserve. Fault that must turn this red: make the held
    /// batch fall through to `reserve_batch` (the old unconditional preflight).
    fn lost_reply_case(label: &str, rows: Vec<Correlation>, purpose: Purpose, single: bool) {
        let root = temp("lost-reply");
        fs::create_dir_all(&root).unwrap();
        let anchor = AnchorHandle::new(&root);
        {
            let local = root.join(label);
            let mut req = vec![if single { 1 } else { 2 }];
            req.extend(if single {
                request(&rows[0], &g(), purpose)
            } else {
                batch_request(&rows, &g(), purpose)
            });
            let go = || {
                reserve_with_receipt(
                    &root.join(format!("{label}.lock")),
                    &req,
                    &rows,
                    &g(),
                    purpose,
                    b"PREFIX".to_vec(),
                    anchor.socket(),
                    &local,
                    label,
                )
            };
            let (_, first) = go().unwrap();
            let spent = Journal::decode(&rpc(anchor.socket(), &[0]).unwrap()).unwrap().spent.len();
            // The reply never reached the caller: no receipt on disk.
            fs::remove_file(&local).unwrap();
            let (_, again) = go().unwrap();
            assert_eq!(again, first, "{label}: the same receipt");
            assert_eq!(fs::read(&local).unwrap(), first);
            let after = Journal::decode(&rpc(anchor.socket(), &[0]).unwrap()).unwrap();
            assert_eq!(after.spent.len(), spent, "{label}: nothing recorded twice");
            // A held batch with no matching retained request is not ours.
            fs::remove_file(local.with_extension("intent")).unwrap();
            fs::remove_file(&local).unwrap();
            assert!(go().is_err(), "{label}: held without a retained request refuses");
            // Nor is a relabelled generation.
            let mut other = g();
            other.attempt = Nat::new(77);
            let mut relabelled = vec![req[0]];
            relabelled.extend(if single {
                request(&rows[0], &other, purpose)
            } else {
                batch_request(&rows, &other, purpose)
            });
            assert!(reserve_with_receipt(
                &root.join(format!("{label}.lock")),
                &relabelled,
                &rows,
                &other,
                purpose,
                b"PREFIX".to_vec(),
                anchor.socket(),
                &local,
                label,
            )
            .is_err());
        }
    }
    #[test]
    fn lost_reply_on_burn_is_recovered_without_a_second_record() {
        lost_reply_case("burn", ids(3), Purpose::Triple, false);
    }
    #[test]
    fn lost_reply_on_reserve_is_recovered_without_a_second_record() {
        let one = vec![Correlation { pool: Nat::new(77), row: Nat::new(0) }];
        lost_reply_case("reserve", one, Purpose::HolderPad, true);
    }
}
