//! Durable ASKS event+outbox replay, under one party's honest crash-storage
//! authority. External monotonic checkpoint anchoring / channel authentication
//! are source receiving joins, not supplied by an unkeyed local checksum.
use crate::{
    asks::{self, Asks, Message, Send},
    codec::{bad, Generation},
    custody::hash,
    reconstruction::Field,
};
use std::{
    fs::{self, File, OpenOptions},
    io::{Error, Read, Result, Seek, SeekFrom, Write},
    os::unix::{fs::OpenOptionsExt, io::AsRawFd},
    path::Path,
};
#[derive(Clone)]
enum Event {
    Dealer(Vec<Vec<Field>>),
    Receive(u16, Message),
    Reconstruct,
}
fn encode_event(event: &Event) -> Vec<u8> {
    let mut o = vec![];
    match event {
        Event::Dealer(ps) => {
            o.push(0);
            crate::codec::Nat::new(ps.len() as u64).put(&mut o);
            for p in ps {
                crate::codec::Nat::new(p.len() as u64).put(&mut o);
                for w in p {
                    o.extend(w.0.to_le_bytes());
                }
            }
        }
        Event::Receive(sender, m) => {
            o.push(1);
            o.extend(sender.to_le_bytes());
            crate::codec::bytes(&asks::encode_message(m), &mut o);
        }
        Event::Reconstruct => o.push(2),
    }
    o
}
fn decode_event(b: &[u8], f: usize) -> Result<Event> {
    match b.first() {
        Some(0) => {
            // Supported suite has exactly two independent coordinate polynomials.
            let prefix = vec![0, 2, 255];
            if !b.starts_with(&prefix) {
                return Err(bad("dealer transcript dimensions"));
            }
            let mut pos = 3;
            let mut ps = vec![];
            for _ in 0..2 {
                let mut r = crate::codec::Reader::new(&b[pos..])?;
                let count = r.nat()?.value()? as usize;
                if count != f + 1 || count >= 255 {
                    return Err(bad("dealer transcript degree"));
                }
                pos += 2;
                let end = pos
                    .checked_add(count * 16)
                    .ok_or_else(|| bad("transcript overflow"))?;
                if end > b.len() {
                    return Err(bad("short dealer transcript"));
                }
                ps.push(
                    b[pos..end]
                        .chunks_exact(16)
                        .map(|x| Field(u128::from_le_bytes(x.try_into().unwrap())))
                        .collect(),
                );
                pos = end;
            }
            if pos != b.len() {
                return Err(bad("dealer transcript trailing"));
            }
            Ok(Event::Dealer(ps))
        }
        Some(1) if b.len() >= 3 => {
            let sender = u16::from_le_bytes(b[1..3].try_into().unwrap());
            let mut r = crate::codec::Reader::new(&b[3..])?;
            let m = asks::decode_message(&r.bytes()?)?;
            r.finish()?;
            Ok(Event::Receive(sender, m))
        }
        Some(2) if b.len() == 1 => Ok(Event::Reconstruct),
        _ => Err(bad("protocol transcript event")),
    }
}
fn encode_outbox(out: &[Send]) -> Vec<u8> {
    let mut o = vec![];
    crate::codec::Nat::new(out.len() as u64).put(&mut o);
    for s in out {
        o.extend(s.recipient.to_le_bytes());
        crate::codec::bytes(&asks::encode_message(&s.message), &mut o);
    }
    o
}
fn apply(state: &mut Asks, event: &Event, dealer_started: &mut bool) -> Result<Vec<Send>> {
    match event {
        Event::Dealer(ps) => {
            if *dealer_started {
                return Err(bad("dealer cannot regenerate same instance"));
            }
            let out = state.dealer_with_coefficients(ps)?;
            *dealer_started = true;
            Ok(out)
        }
        Event::Receive(sender, m) => state.receive(*sender, m.clone()),
        Event::Reconstruct => state.start_reconstruction(),
    }
}
pub struct Store {
    file: File,
    state: Asks,
    started: bool,
    outbox: Vec<Send>,
    poisoned: bool,
    _lock: File,
    bytes: usize,
}
impl Store {
    pub fn open(
        root: &Path,
        me: u16,
        dealer: u16,
        n: usize,
        f: usize,
        g: &Generation,
    ) -> Result<Self> {
        fs::create_dir_all(root)?;
        let guard = OpenOptions::new()
            .read(true)
            .write(true)
            .create(true)
            .truncate(false)
            .mode(0o600)
            .open(root.join("protocol.lock"))?;
        if unsafe { libc::flock(guard.as_raw_fd(), libc::LOCK_EX | libc::LOCK_NB) } != 0 {
            return Err(Error::last_os_error());
        }
        let mut header = b"DREGG.ASKS.TRANSCRIPT\x02".to_vec();
        g.put(&mut header);
        header.extend(me.to_le_bytes());
        header.extend(dealer.to_le_bytes());
        header.extend((n as u64).to_le_bytes());
        header.extend((f as u64).to_le_bytes());
        let path = root.join("transcript");
        let existed = path.exists();
        let mut file = OpenOptions::new()
            .read(true)
            .append(true)
            .create(true)
            .mode(0o600)
            .open(&path)?;
        if !existed {
            file.write_all(&(header.len() as u32).to_le_bytes())?;
            file.write_all(&header)?;
            file.sync_all()?;
            File::open(root)?.sync_all()?;
        }
        file.seek(SeekFrom::Start(0))?;
        let mut len = [0; 4];
        file.read_exact(&mut len)?;
        let size = u32::from_le_bytes(len) as usize;
        if size > crate::codec::MAX {
            return Err(bad("header bound"));
        }
        let mut got = vec![0; size];
        file.read_exact(&mut got)?;
        if got != header {
            return Err(bad("exact generation/party/access structure mismatch"));
        }
        let mut state = Asks::new(me, dealer, n, f, g)?;
        let (mut started, mut outbox) = (false, vec![]);
        let mut bytes = 4 + size;
        loop {
            let mut len = [0; 4];
            if file.read(&mut len[..1])? == 0 {
                break;
            }
            file.read_exact(&mut len[1..])?;
            let size = u32::from_le_bytes(len) as usize;
            if size > crate::codec::MAX {
                return Err(bad("event bound"));
            }
            let mut record = vec![0; size];
            file.read_exact(&mut record)?;
            let mut h = [0; 32];
            file.read_exact(&mut h)?;
            if hash(&record) != h {
                return Err(bad("protocol checksum"));
            }
            let mut r = crate::codec::Reader::new(&record)?;
            let event_bytes = r.bytes()?;
            let emitted = r.bytes()?;
            r.finish()?;
            let event = decode_event(&event_bytes, f)?;
            if encode_event(&event) != event_bytes {
                return Err(bad("event canonical"));
            }
            let out = apply(&mut state, &event, &mut started)?;
            if encode_outbox(&out) != emitted {
                return Err(bad("recorded outbox disagrees with native protocol replay"));
            }
            outbox.extend(out);
            bytes += 4 + size + 32;
            if bytes > crate::codec::MAX {
                return Err(bad("retained protocol transcript bound"));
            }
        }
        Ok(Self {
            file,
            state,
            started,
            outbox,
            poisoned: false,
            _lock: guard,
            bytes,
        })
    }
    fn append(&mut self, event: Event) -> Result<Vec<Send>> {
        if self.poisoned {
            return Err(bad("protocol uncertain IO"));
        }
        let mut next = self.state.clone();
        let mut started = self.started;
        let out = apply(&mut next, &event, &mut started)?;
        let mut record = vec![];
        crate::codec::bytes(&encode_event(&event), &mut record);
        crate::codec::bytes(&encode_outbox(&out), &mut record);
        if self.bytes + record.len() + 36 > crate::codec::MAX {
            return Err(bad("protocol retention exhausted; source close required"));
        }
        let write = (|| {
            self.file.write_all(&(record.len() as u32).to_le_bytes())?;
            self.file.write_all(&record)?;
            self.file.write_all(&hash(&record))?;
            self.file.sync_all()
        })();
        if let Err(e) = write {
            self.poisoned = true;
            return Err(e);
        }
        self.bytes += record.len() + 36;
        self.state = next;
        self.started = started;
        self.outbox.extend(out.clone());
        Ok(out)
    }
    /// A retry returns only the SAME retained outbound transcript. Never fresh
    /// polynomial/randomness at the same generation/instance.
    pub fn dealer_start(&mut self) -> Result<Vec<Send>> {
        if self.started {
            return Ok(self.outbox.clone());
        }
        let mut random = File::open("/dev/urandom")?;
        let mut ps = vec![vec![Field(0); self.state.f + 1]; 2];
        for p in &mut ps {
            for x in p {
                let mut b = [0; 16];
                random.read_exact(&mut b)?;
                *x = Field(u128::from_le_bytes(b));
            }
        }
        self.append(Event::Dealer(ps))
    }
    pub fn receive(&mut self, authenticated_sender: u16, message: Message) -> Result<Vec<Send>> {
        self.append(Event::Receive(authenticated_sender, message))
    }
    pub fn start_reconstruction(&mut self) -> Result<Vec<Send>> {
        self.append(Event::Reconstruct)
    }
    pub fn resend(&self) -> &[Send] {
        &self.outbox
    }
    pub fn state(&self) -> &Asks {
        &self.state
    }
}
#[cfg(test)]
mod tests {
    use super::*;
    use crate::codec::Nat;
    fn g() -> Generation {
        Generation {
            invocation: Nat::new(9),
            command: vec![1, 2, 3],
            attempt: Nat::new(1),
            generation: Nat::new(2),
            configuration: Nat::new(5),
        }
    }
    fn temp(label: &str) -> std::path::PathBuf {
        std::env::temp_dir().join(format!(
            "mini-asks-store-{label}-{}-{}",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        ))
    }
    #[test]
    fn dealer_dropped_reply_restores_identical_randomness() {
        let p = temp("replay");
        let original;
        {
            let mut store = Store::open(&p, 0, 0, 4, 1, &g()).unwrap();
            original = store.dealer_start().unwrap();
        }
        let mut recovered = Store::open(&p, 0, 0, 4, 1, &g()).unwrap();
        assert_eq!(recovered.resend(), original);
        assert_eq!(recovered.dealer_start().unwrap(), original);
    }
    #[test]
    fn generation_changes_cannot_restore() {
        let p = temp("generation");
        {
            Store::open(&p, 0, 0, 4, 1, &g()).unwrap();
        }
        let mut different = g();
        different.generation = Nat::new(3);
        assert!(Store::open(&p, 0, 0, 4, 1, &different).is_err());
    }
    #[test]
    fn truncated_transcript_fails_closed() {
        let p = temp("torn");
        {
            Store::open(&p, 0, 0, 4, 1, &g()).unwrap();
        }
        OpenOptions::new()
            .append(true)
            .open(p.join("transcript"))
            .unwrap()
            .write_all(&[7])
            .unwrap();
        assert!(Store::open(&p, 0, 0, 4, 1, &g()).is_err());
    }
}
