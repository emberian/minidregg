//! Reusable deterministic transition WAL. Storage premise: honest crash domain;
//! an unkeyed checksum detects tears, not malicious rollback/authentication.
//! Each event and exact replay-checked outbox are fsynced before publication.
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
pub struct Journal<M: Machine> {
    file: File,
    state: M,
    outbox: Vec<Vec<u8>>,
    poisoned: bool,
    _lock: File,
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
            file.sync_all()?;
            File::open(path.parent().ok_or_else(|| bad("WAL parent"))?)?.sync_all()?;
        }
        file.seek(SeekFrom::Start(0))?;
        let mut all = vec![];
        file.read_to_end(&mut all)?;
        if !all.starts_with(&header) {
            return Err(bad("transition exact identity/version"));
        }
        let mut i = header.len();
        let mut state = initial;
        let mut outbox = vec![];
        while i < all.len() {
            if all.len() - i < 8 {
                return Err(bad("torn transition length"));
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
                return Err(bad("torn transition record"));
            }
            let b = &all[i..i + n];
            if hash(b) != all[i + n..end] {
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
            state,
            outbox,
            poisoned: false,
            _lock: lock,
        })
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
            self.file.sync_all()
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
    fn replay_preserves_exact_outbox_and_rejects_identity_or_tear() {
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
        assert!(Journal::open(&p, b"epoch1", Counter(0)).is_err());
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
}
