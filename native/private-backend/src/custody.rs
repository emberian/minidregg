//! External monotonic anchor: must be a separate rollback authority, not another
//! path controlled by the snapshot owner. The local Unix service tests IO only.
use crate::codec::*;
use sha2::{Digest, Sha256};
use std::fs::{self, File, OpenOptions};
use std::io::{Error, ErrorKind, Read, Result, Write};
use std::os::unix::{
    fs::{OpenOptionsExt, PermissionsExt},
    io::AsRawFd,
    net::{UnixListener, UnixStream},
};
use std::path::{Path, PathBuf};
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
fn parent_sync(p: &Path) -> Result<()> {
    File::open(p.parent().ok_or_else(|| bad("parent"))?)?.sync_all()
}
fn nonce() -> Result<u64> {
    let mut b = [0; 8];
    File::open("/dev/urandom")?.read_exact(&mut b)?;
    Ok(u64::from_le_bytes(b))
}
fn snapshot(p: &Path, b: &[u8]) -> Result<()> {
    let tmp = p.with_extension(format!("pending-{}-{}", std::process::id(), nonce()?));
    let mut f = create(&tmp)?;
    f.write_all(b)?;
    f.sync_all()?;
    fs::rename(&tmp, p)?;
    parent_sync(p)
}
fn read_packet(s: &mut UnixStream) -> Result<Vec<u8>> {
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
fn write_packet(s: &mut UnixStream, b: &[u8]) -> Result<()> {
    if b.len() > MAX {
        return Err(bad("packet bound"));
    }
    s.write_all(&(b.len() as u32).to_le_bytes())?;
    s.write_all(b)?;
    s.flush()
}
fn lock(p: &Path) -> Result<File> {
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
pub struct Anchor {
    log: File,
    pub journal: Journal,
    _lock: File,
    poisoned: bool,
}
impl Anchor {
    pub fn open(root: &Path) -> Result<Self> {
        fs::create_dir_all(root)?;
        fs::set_permissions(root, fs::Permissions::from_mode(0o700))?;
        let guard = lock(&root.join("authority.lock"))?;
        let p = root.join("authority.log");
        let existed = p.exists();
        let mut log = OpenOptions::new()
            .read(true)
            .append(true)
            .create(true)
            .mode(0o600)
            .open(&p)?;
        if !existed {
            log.sync_all()?;
            parent_sync(&p)?;
        }
        let mut journal = Journal::default();
        loop {
            let mut len = [0; 4];
            if log.read(&mut len[..1])? == 0 {
                break;
            }
            log.read_exact(&mut len[1..])?;
            let n = u32::from_le_bytes(len) as usize;
            if n > MAX {
                return Err(bad("authority record bound"));
            }
            let mut b = vec![0; n];
            log.read_exact(&mut b)?;
            let mut h = [0; 32];
            log.read_exact(&mut h)?;
            if hash(&b) != h {
                return Err(bad("authority checksum"));
            }
            let next = Journal::decode(&b)?;
            if next.allocations.len() != journal.allocations.len() + 1 {
                return Err(bad("authority discontinuity"));
            }
            let a = &next.allocations[0];
            if a.consumed || journal.reserve(a.id.clone(), a.generation.clone(), a.purpose)? != next
            {
                return Err(bad("authority transition"));
            }
            journal = next;
        }
        Ok(Self {
            log,
            journal,
            _lock: guard,
            poisoned: false,
        })
    }
    pub fn reserve(&mut self, id: Correlation, g: Generation, p: Purpose) -> Result<Vec<u8>> {
        if self.poisoned {
            return Err(bad("authority poisoned by uncertain IO"));
        }
        let next = self.journal.reserve(id, g, p)?;
        let b = next.encode();
        let append = (|| {
            self.log.write_all(&(b.len() as u32).to_le_bytes())?;
            self.log.write_all(&b)?;
            self.log.write_all(&hash(&b))?;
            self.log.sync_all()
        })();
        if let Err(e) = append {
            self.poisoned = true;
            return Err(e);
        }
        self.journal = next;
        Ok(b)
    }
}
pub fn run_anchor(root: &Path, socket: &Path) -> Result<()> {
    let mut a = Anchor::open(root)?;
    let listener = UnixListener::bind(socket)?;
    fs::set_permissions(socket, fs::Permissions::from_mode(0o600))?;
    for incoming in listener.incoming() {
        let mut s = incoming?;
        s.set_read_timeout(Some(std::time::Duration::from_secs(10)))?;
        s.set_write_timeout(Some(std::time::Duration::from_secs(10)))?;
        let answer = (|| {
            let b = read_packet(&mut s)?;
            if a.poisoned {
                return Err(bad("authority uncertain"));
            }
            match b.split_first() {
                Some((0, [])) => Ok(a.journal.encode()),
                Some((1, b)) => {
                    let (id, g, p) = parse_request(b)?;
                    a.reserve(id, g, p)
                }
                _ => Err(bad("anchor request")),
            }
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
    Ok(())
}
fn rpc(socket: &Path, b: &[u8]) -> Result<Vec<u8>> {
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
pub struct Pool {
    root: PathBuf,
    pub id: Nat,
    row_hashes: Vec<[u8; 32]>,
}
impl Pool {
    pub fn provision(root: &Path, rows: &[Vec<u8>]) -> Result<Self> {
        if rows.is_empty() || rows.iter().any(Vec::is_empty) {
            return Err(bad("empty pool/row"));
        }
        fs::create_dir(root)?;
        fs::set_permissions(root, fs::Permissions::from_mode(0o700))?;
        let mut m = b"DREGG.PRIVATE.IMMUTABLE.POOL\x01".to_vec();
        m.extend((rows.len() as u64).to_le_bytes());
        for (i, row) in rows.iter().enumerate() {
            let mut f = create(&root.join(format!("row-{i}")))?;
            f.write_all(row)?;
            f.sync_all()?;
            m.extend(hash(row));
        }
        let p = root.join("manifest");
        let mut f = create(&p)?;
        f.write_all(&m)?;
        f.sync_all()?;
        parent_sync(&p)?;
        Self::open(root)
    }
    pub fn open(root: &Path) -> Result<Self> {
        let m = fs::read(root.join("manifest"))?;
        let prefix = b"DREGG.PRIVATE.IMMUTABLE.POOL\x01";
        if !m.starts_with(prefix) || m.len() < prefix.len() + 8 {
            return Err(bad("pool manifest"));
        }
        let n = u64::from_le_bytes(m[prefix.len()..prefix.len() + 8].try_into().unwrap());
        let rest = &m[prefix.len() + 8..];
        if n == 0 || n as u128 * 32 != rest.len() as u128 {
            return Err(bad("pool count"));
        }
        let row_hashes = rest
            .chunks_exact(32)
            .map(|x| x.try_into().unwrap())
            .collect();
        Ok(Self {
            root: root.into(),
            id: Nat::from_be(&hash(&m)),
            row_hashes,
        })
    }
    fn row(&self, row: u64) -> Result<Vec<u8>> {
        let i = usize::try_from(row).map_err(|_| bad("row overflow"))?;
        let h = self.row_hashes.get(i).ok_or_else(|| {
            Error::new(
                ErrorKind::UnexpectedEof,
                "stock exhausted: independent refill required",
            )
        })?;
        let b = fs::read(self.root.join(format!("row-{row}")))?;
        if b.is_empty() || hash(&b) != *h {
            return Err(bad("physical row substitution"));
        }
        Ok(b)
    }
    pub fn row_commitment(&self, row: u64) -> Result<[u8; 32]> {
        let i = usize::try_from(row).map_err(|_| bad("row overflow"))?;
        self.row_hashes
            .get(i)
            .copied()
            .ok_or_else(|| bad("pool row commitment range"))
    }
    pub fn len(&self) -> usize {
        self.row_hashes.len()
    }
    pub fn is_empty(&self) -> bool {
        self.row_hashes.is_empty()
    }
}
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Cut {
    None,
    BeforeAnchor,
    AfterAnchor,
    AfterSnapshot,
    AfterSecretRead,
}
fn cut(x: Cut, y: Cut) {
    if x == y {
        std::process::exit(70);
    }
}
pub fn reserve_release(
    pool: &Pool,
    row: u64,
    g: Generation,
    p: Purpose,
    anchor: &Path,
    local: &Path,
    crash: Cut,
) -> Result<Vec<u8>> {
    let _guard = lock(&local.with_extension("reservation.lock"))?;
    if row as u128 >= pool.len() as u128 {
        return Err(Error::new(
            ErrorKind::UnexpectedEof,
            "stock exhausted: independent refill required",
        ));
    }
    let before = Journal::decode(&rpc(anchor, &[0])?)?;
    let id = Correlation {
        pool: pool.id.clone(),
        row: Nat::new(row),
    };
    before.reserve(id.clone(), g.clone(), p)?;
    cut(crash, Cut::BeforeAnchor);
    let mut req = vec![1];
    req.extend(request(&id, &g, p));
    let b = rpc(anchor, &req)?;
    let confirmed = Journal::decode(&b)?;
    if !confirmed.extends(&before)
        || !confirmed
            .allocations
            .iter()
            .any(|a| a.id == id && a.generation == g && a.purpose == p && !a.consumed)
    {
        return Err(bad("anchor allocation binding"));
    }
    cut(crash, Cut::AfterAnchor);
    snapshot(local, &b)?;
    if fs::read(local)? != b {
        return Err(bad("snapshot readback"));
    }
    let latest = Journal::decode(&rpc(anchor, &[0])?)?;
    if !latest.extends(&confirmed) {
        return Err(bad("anchor rollback"));
    }
    cut(crash, Cut::AfterSnapshot);
    let secret = pool.row(row)?;
    cut(crash, Cut::AfterSecretRead);
    Ok(secret)
}
pub fn recover_snapshot(anchor: &Path, local: &Path) -> Result<Journal> {
    let _guard = lock(&local.with_extension("reservation.lock"))?;
    let b = rpc(anchor, &[0])?;
    let authoritative = Journal::decode(&b)?;
    if local.exists() {
        let stale = Journal::decode(&fs::read(local)?)?;
        if !authoritative.extends(&stale) {
            return Err(bad("anchor behind local"));
        }
    }
    snapshot(local, &b)?;
    if fs::read(local)? != b {
        return Err(bad("recovery readback"));
    }
    Ok(authoritative)
}
#[cfg(test)]
mod tests {
    use super::*;
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
        assert_eq!(a.journal.spent.len(), 1);
    }
    #[test]
    fn torn_anchor_refuses() {
        let p = temp("torn");
        {
            Anchor::open(&p).unwrap();
        }
        OpenOptions::new()
            .append(true)
            .open(p.join("authority.log"))
            .unwrap()
            .write_all(&[100, 0])
            .unwrap();
        assert!(Anchor::open(&p).is_err());
    }
    #[test]
    fn row_substitution_and_exhaustion() {
        let p = temp("pool");
        let pool = Pool::provision(&p, &[vec![1, 2, 3]]).unwrap();
        assert_eq!(pool.row(0).unwrap(), vec![1, 2, 3]);
        assert!(pool.row(1).is_err());
        fs::write(p.join("row-0"), [7, 8, 9]).unwrap();
        assert!(pool.row(0).is_err());
    }
    #[test]
    fn singleton_authority() {
        let p = temp("lock");
        let _a = Anchor::open(&p).unwrap();
        assert!(Anchor::open(&p).is_err());
    }
}
