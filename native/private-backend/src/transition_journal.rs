//! Reusable deterministic transition WAL. Storage premise: honest crash domain;
//! an unkeyed checksum detects tears, not malicious rollback/authentication.
//! Each event and exact replay-checked outbox are written before publication.
//! A partial FINAL frame is truncated on recovery, and so is a
//! full-length FINAL frame whose checksum fails: a crash between the length
//! extension and the data reaching disk leaves exactly that shape, and the
//! frame was never published (publication requires the completed write).
//! Dropping it is never silent: `Journal::torn_tail` reports the offset and
//! the dropped bytes, so a machine that must not re-issue a step can refuse.
//! A bad checksum on any EARLIER frame, a length word that points past EOF
//! while a complete checksum-valid record sits at that position (interior
//! damage, not a tear), or a wrong identity, refuses.
//! Published records require completed write.
//! This assumes crash-prefix storage; arbitrary disk corruption is not repaired.
//! This is not an independent anti-rollback anchor and cannot mint source authority.
use crate::{
    codec::{bad, bytes},
    consensus_wire::Cursor,
    custody::hash,
};
use std::{
    fs::{File, OpenOptions},
    io::{Error, Read, Result, Seek, SeekFrom, Write},
    os::unix::{fs::OpenOptionsExt, io::AsRawFd},
    path::Path,
};
pub trait Machine: Clone {
    fn apply(&mut self, event: &[u8]) -> Result<Vec<u8>>;
}
/// The final record recovery dropped: its start offset in the WAL and the
/// bytes that were removed (length word included).
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct TornTail {
    pub offset: u64,
    pub dropped: Vec<u8>,
}
pub struct Journal<M: Machine> {
    file: File,
    torn: Option<TornTail>,
    state: M,
    outbox: Vec<Vec<u8>>,
    poisoned: bool,
    _lock: File,
}
/// A record whose length word points past EOF is a tear only if no complete,
/// checksum-valid record is present at that position. `rest` is everything
/// after the length word. A rotted interior length leaves the real record
/// intact behind it; its own event/outbox framing gives its true length.
fn complete_record_behind(rest: &[u8]) -> bool {
    let Ok(mut c) = Cursor::new(&rest[..rest.len().min(crate::codec::MAX)]) else {
        return false;
    };
    if c.bytes().is_err() || c.bytes().is_err() {
        return false;
    }
    let n = c.consumed();
    rest.len() >= n + 32 && hash(&rest[..n]) == rest[n..n + 32]
}
fn record(e: &[u8], out: &[u8]) -> Vec<u8> {
    let mut b = vec![];
    bytes(e, &mut b);
    bytes(out, &mut b);
    b
}
impl<M: Machine> Journal<M> {
    pub fn open(path: &Path, identity: &[u8], initial: M) -> Result<Self> {
        if identity.len() > crate::codec::MAX {
            return Err(bad("transition identity bound"));
        }
        let lock_path = path.with_extension("lock");
        let lock = OpenOptions::new()
            .read(true)
            .write(true)
            .create(true)
            .mode(0o600)
            .open(lock_path)?;
        if unsafe { libc::flock(lock.as_raw_fd(), libc::LOCK_EX | libc::LOCK_NB) } != 0 {
            return Err(Error::last_os_error());
        }
        let mut file = OpenOptions::new()
            .read(true)
            .write(true)
            .create(true)
            .mode(0o600)
            .open(path)?;
        let mut header = b"DREGG.TRANSITION.WAL\x01".to_vec();
        bytes(identity, &mut header);
        header.extend(hash(&header));
        if file.metadata()?.len() == 0 {
            file.write_all(&header)?;
        }
        file.seek(SeekFrom::Start(0))?;
        let mut all = vec![];
        file.read_to_end(&mut all)?;
        // Header creation itself may tear before any event/outbox exists.
        if all.len() < header.len() && header.starts_with(&all) {
            file.set_len(0)?;
            file.seek(SeekFrom::Start(0))?;
            file.write_all(&header)?;
            all = header.clone();
        }
        if !all.starts_with(&header) {
            return Err(bad("transition exact identity/version"));
        }
        let mut i = header.len();
        let mut state = initial;
        let mut outbox = vec![];
        let mut torn = None;
        let mut drop_tail = |file: &mut File, at: usize| -> Result<()> {
            torn = Some(TornTail {
                offset: at as u64,
                dropped: all[at..].to_vec(),
            });
            file.set_len(at as u64)?;
            Ok(())
        };
        while i < all.len() {
            let record_start = i;
            if all.len() - i < 8 {
                drop_tail(&mut file, record_start)?;
                break;
            }
            let n = u64::from_le_bytes(all[i..i + 8].try_into().unwrap());
            i += 8;
            if n as u128 > crate::codec::MAX as u128 {
                return Err(bad("transition frame capacity"));
            }
            let n = n as usize;
            let end = i
                .checked_add(n)
                .and_then(|j| j.checked_add(32))
                .ok_or_else(|| bad("transition length overflow"))?;
            if end > all.len() {
                if complete_record_behind(&all[i..]) {
                    return Err(bad("transition interior length damage"));
                }
                drop_tail(&mut file, record_start)?;
                break;
            }
            let b = &all[i..i + n];
            if hash(b) != all[i + n..end] {
                if end == all.len() {
                    // Torn final frame: never written, never published.
                    drop_tail(&mut file, record_start)?;
                    break;
                }
                return Err(bad("transition checksum"));
            }
            let mut c = Cursor::new(b)?;
            let event = c.bytes()?;
            let expected = c.bytes()?;
            c.finish()?;
            let actual = state.apply(&event)?;
            if actual != expected {
                return Err(bad("transition outbox replay mismatch"));
            }
            outbox.push(actual);
            i = end;
        }
        file.seek(SeekFrom::End(0))?;
        Ok(Self {
            file,
            torn,
            state,
            outbox,
            poisoned: false,
            _lock: lock,
        })
    }
    /// The final record this open dropped as torn, if any.
    pub fn torn_tail(&self) -> Option<&TornTail> {
        self.torn.as_ref()
    }
    /// After an uncertain write the in-memory state may trail the disk; every
    /// append refuses until the journal is reopened.
    pub fn is_poisoned(&self) -> bool {
        self.poisoned
    }
    pub fn state(&self) -> &M {
        &self.state
    }
    pub fn replay_outboxes(&self) -> &[Vec<u8>] {
        &self.outbox
    }
    pub fn append(&mut self, event: &[u8]) -> Result<Vec<u8>> {
        if self.poisoned {
            return Err(bad("uncertain transition persistence; restart required"));
        }
        let mut next = self.state.clone();
        let out = next.apply(event)?;
        let b = record(event, &out);
        if b.len() > crate::codec::MAX {
            return Err(bad("transition frame capacity"));
        }
        let persisted = (|| {
            self.file.write_all(&(b.len() as u64).to_le_bytes())?;
            self.file.write_all(&b)?;
            self.file.write_all(&hash(&b))?;
            Ok(())
        })();
        if let Err(e) = persisted {
            self.poisoned = true;
            return Err(e);
        }
        self.state = next;
        self.outbox.push(out.clone());
        Ok(out)
    }
}
#[cfg(test)]
mod tests {
    use super::*;
    use std::{
        fs,
        time::{SystemTime, UNIX_EPOCH},
    };
    #[derive(Clone)]
    struct Counter(u64);
    impl Machine for Counter {
        fn apply(&mut self, b: &[u8]) -> Result<Vec<u8>> {
            if b.len() != 8 {
                return Err(bad("counter event"));
            }
            self.0 += u64::from_le_bytes(b.try_into().unwrap());
            Ok(self.0.to_le_bytes().to_vec())
        }
    }
    fn path(label: &str) -> std::path::PathBuf {
        let p = std::env::temp_dir().join(format!(
            "mini-transition-{}-{}-{}",
            label,
            std::process::id(),
            SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        ));
        fs::create_dir(&p).unwrap();
        p.join("journal")
    }
    #[test]
    fn replay_preserves_exact_outbox_and_recovers_incomplete_tail() {
        let p = path("replay");
        let expected;
        {
            let mut j = Journal::open(&p, b"epoch1", Counter(0)).unwrap();
            expected = j.append(&7u64.to_le_bytes()).unwrap();
            assert_eq!(j.state().0, 7);
        }
        {
            let j = Journal::open(&p, b"epoch1", Counter(0)).unwrap();
            assert_eq!(j.replay_outboxes(), &[expected]);
            assert_eq!(j.state().0, 7);
        }
        assert!(Journal::open(&p, b"epoch2", Counter(0)).is_err());
        let n = fs::metadata(&p).unwrap().len();
        OpenOptions::new()
            .write(true)
            .open(&p)
            .unwrap()
            .set_len(n - 1)
            .unwrap();
        let recovered = Journal::open(&p, b"epoch1", Counter(0)).unwrap();
        assert_eq!(recovered.state().0, 0);
        assert!(recovered.replay_outboxes().is_empty());
    }
    fn three_records() -> (Vec<u8>, usize, usize) {
        let p = path("three-base");
        let mut j = Journal::open(&p, b"epoch1", Counter(0)).unwrap();
        j.append(&1u64.to_le_bytes()).unwrap();
        let one = fs::read(&p).unwrap().len();
        j.append(&2u64.to_le_bytes()).unwrap();
        let two = fs::read(&p).unwrap().len();
        j.append(&4u64.to_le_bytes()).unwrap();
        (fs::read(&p).unwrap(), one, two)
    }
    #[test]
    fn interior_length_damage_is_refused_never_truncated() {
        let (full, one, _) = three_records();
        // Record two's length word rots to a value that points past EOF while
        // its record and record three sit intact behind it.
        for rotted in [full.len() as u64, full.len() as u64 * 2, (1 << 20)] {
            let mut damaged = full.clone();
            damaged[one..one + 8].copy_from_slice(&rotted.to_le_bytes());
            let q = path("interior");
            fs::write(&q, &damaged).unwrap();
            let err = Journal::open(&q, b"epoch1", Counter(0)).err().expect("refused");
            assert!(err.to_string().contains("interior"), "{err}");
            assert_eq!(fs::read(&q).unwrap(), damaged, "refusal must not truncate");
        }
    }
    #[test]
    fn final_torn_record_is_reported_and_recovery_resumes_from_last_complete_record() {
        let (full, _, two) = three_records();
        for cut in two + 1..full.len() {
            let q = path("final-torn");
            fs::write(&q, &full[..cut]).unwrap();
            let mut j = Journal::open(&q, b"epoch1", Counter(0)).unwrap();
            let torn = j.torn_tail().expect("tear reported");
            assert_eq!(torn.offset as usize, two, "cut {cut}");
            assert_eq!(torn.dropped, full[two..cut], "cut {cut}");
            assert_eq!(j.state().0, 3);
            assert_eq!(j.replay_outboxes().len(), 2);
            j.append(&8u64.to_le_bytes()).unwrap();
            drop(j);
            let j = Journal::open(&q, b"epoch1", Counter(0)).unwrap();
            assert!(j.torn_tail().is_none());
            assert_eq!(j.state().0, 11);
        }
        let q = path("no-tear");
        fs::write(&q, &full).unwrap();
        assert!(Journal::open(&q, b"epoch1", Counter(0)).unwrap().torn_tail().is_none());
    }
    #[test]
    fn invalid_event_has_no_effect_or_outbox() {
        let p = path("invalid");
        let mut j = Journal::open(&p, b"epoch1", Counter(0)).unwrap();
        let n = j.file.metadata().unwrap().len();
        assert!(j.append(&[1]).is_err());
        assert_eq!(j.file.metadata().unwrap().len(), n);
        assert_eq!(j.state().0, 0);
    }
    #[test]
    fn every_append_crash_cut_recovers_prior_prefix_and_replays_complete_record() {
        let p = path("cuts-base");
        let prefix;
        let full;
        {
            let mut j = Journal::open(&p, b"epoch1", Counter(0)).unwrap();
            j.append(&7u64.to_le_bytes()).unwrap();
            prefix = fs::read(&p).unwrap();
            j.append(&11u64.to_le_bytes()).unwrap();
            full = fs::read(&p).unwrap();
        }
        for cut in prefix.len()..=full.len() {
            let q = path("cut");
            fs::write(&q, &full[..cut]).unwrap();
            let mut j = Journal::open(&q, b"epoch1", Counter(0)).unwrap();
            let expected = if cut == full.len() { 18 } else { 7 };
            assert_eq!(j.state().0, expected, "cut {cut}");
            assert_eq!(
                j.replay_outboxes().len(),
                if cut == full.len() { 2 } else { 1 }
            );
            assert_eq!(
                fs::metadata(&q).unwrap().len() as usize,
                if cut == full.len() {
                    full.len()
                } else {
                    prefix.len()
                }
            );
            j.append(&5u64.to_le_bytes()).unwrap();
            drop(j);
            assert_eq!(
                Journal::open(&q, b"epoch1", Counter(0)).unwrap().state().0,
                expected + 5
            );
        }
        // A bad checksum on an EARLIER frame is not a tear: refuse.
        let q = path("bad-checksum-interior");
        let mut corrupted = full.clone();
        corrupted[prefix.len() - 1] ^= 1;
        fs::write(&q, corrupted).unwrap();
        assert!(Journal::open(&q, b"epoch1", Counter(0)).is_err());
    }
    #[test]
    fn zeroed_final_record_body_truncates_to_one_less_record() {
        let p = path("zeroed-tail-base");
        let prefix;
        let full;
        {
            let mut j = Journal::open(&p, b"epoch1", Counter(0)).unwrap();
            j.append(&7u64.to_le_bytes()).unwrap();
            prefix = fs::read(&p).unwrap();
            j.append(&11u64.to_le_bytes()).unwrap();
            full = fs::read(&p).unwrap();
        }
        // Full length on disk, body (and checksum) never reached it: zeros
        // after the 8-byte length word of the final record.
        let mut torn = full.clone();
        for byte in &mut torn[prefix.len() + 8..] {
            *byte = 0;
        }
        assert_ne!(torn, full);
        let q = path("zeroed-tail");
        fs::write(&q, &torn).unwrap();
        let mut j = Journal::open(&q, b"epoch1", Counter(0)).unwrap();
        assert_eq!(j.replay_outboxes().len(), 1);
        assert_eq!(j.state().0, 7);
        assert_eq!(fs::read(&q).unwrap(), prefix);
        j.append(&5u64.to_le_bytes()).unwrap();
        drop(j);
        let j = Journal::open(&q, b"epoch1", Counter(0)).unwrap();
        assert_eq!(j.state().0, 12);
        assert_eq!(j.replay_outboxes().len(), 2);
        // A flipped checksum byte on the final record is the same tear shape.
        let mut flipped = full;
        *flipped.last_mut().unwrap() ^= 1;
        let r = path("flipped-tail");
        fs::write(&r, flipped).unwrap();
        let j = Journal::open(&r, b"epoch1", Counter(0)).unwrap();
        assert_eq!(j.state().0, 7);
        assert_eq!(fs::read(&r).unwrap(), prefix);
    }
    #[test]
    fn partial_initial_header_recovers_but_wrong_identity_refuses() {
        let p = path("header-base");
        drop(Journal::open(&p, b"epoch1", Counter(0)).unwrap());
        let header = fs::read(&p).unwrap();
        for cut in 0..header.len() {
            let q = path("header-cut");
            fs::write(&q, &header[..cut]).unwrap();
            let j = Journal::open(&q, b"epoch1", Counter(0)).unwrap();
            assert_eq!(j.state().0, 0);
            assert_eq!(fs::read(q).unwrap(), header);
        }
        assert!(Journal::open(&p, b"epoch2", Counter(0)).is_err());
    }
}
