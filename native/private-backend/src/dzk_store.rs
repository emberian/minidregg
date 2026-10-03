//! Crash-durable dZK: retained source polynomials/random seed, environment request,
//! authenticated receives and recipient-bound proof transfers. Exact events and
//! outboxes precede publication. Honest crash-storage premise; no rollback anchor,
//! enrolled-credential authority or public-release permission is manufactured.
use crate::{
    asks::PhaseMessage,
    codec::{bad, bytes, Generation, Nat},
    consensus_wire::Cursor,
    dzk::{Body, Dzk, Message, OpenProof, Send, Transferred, Verification},
    private_send_store,
    reconstruction::Field,
    transition_journal::{Journal, Machine},
};
use std::{
    fs::File,
    io::{Read, Result},
    path::Path,
};
fn put_phase(p: &PhaseMessage, b: &mut Vec<u8>) {
    let (tag, v) = match p {
        PhaseMessage::Init(v) => (0, v),
        PhaseMessage::Echo(v) => (1, v),
        PhaseMessage::Ready(v) => (2, v),
    };
    b.push(tag);
    bytes(v, b);
}
fn phase(c: &mut Cursor) -> Result<PhaseMessage> {
    let tag = c.byte()?;
    let v = c.bytes()?;
    match tag {
        0 => Ok(PhaseMessage::Init(v)),
        1 => Ok(PhaseMessage::Echo(v)),
        2 => Ok(PhaseMessage::Ready(v)),
        _ => Err(bad("dZK phase")),
    }
}
fn put_fields(xs: &[Field], b: &mut Vec<u8>) {
    Nat::new(xs.len() as u64).put(b);
    for x in xs {
        b.extend(x.0.to_le_bytes());
    }
}
fn count(c: &mut Cursor) -> Result<usize> {
    let mut b = vec![];
    loop {
        let x = c.byte()?;
        b.push(x);
        if x == 255 {
            break;
        }
    }
    let mut r = crate::codec::Reader::new(&b)?;
    let n = r.count()?;
    r.finish()?;
    Ok(n)
}
fn fields(c: &mut Cursor) -> Result<Vec<Field>> {
    let n = count(c)?;
    if n > 128 {
        return Err(bad("dZK field vector bound"));
    }
    (0..n)
        .map(|_| Ok(Field(u128::from_le_bytes(c.take(16)?.try_into().unwrap()))))
        .collect()
}
pub fn encode_message(m: &Message) -> Vec<u8> {
    let mut b = b"DREGG.DZK.WIRE\x01".to_vec();
    b.extend(m.context);
    match &m.body {
        Body::Public(p) => {
            b.push(0);
            put_phase(p, &mut b);
        }
        Body::Private { holder, message } => {
            b.push(1);
            b.extend(holder.to_le_bytes());
            bytes(&private_send_store::encode_message(message), &mut b);
        }
        Body::Transfer {
            receiver,
            holder,
            values,
            proof,
        } => {
            b.push(2);
            b.extend(receiver.to_le_bytes());
            b.extend(holder.to_le_bytes());
            put_fields(values, &mut b);
            bytes(proof, &mut b);
        }
    }
    b
}
pub fn decode_message(b: &[u8]) -> Result<Message> {
    let mut c = Cursor::new(b)?;
    let domain = b"DREGG.DZK.WIRE\x01";
    if c.take(domain.len())? != domain {
        return Err(bad("dZK wire domain"));
    }
    let context = c.fixed32()?;
    let body = match c.byte()? {
        0 => Body::Public(phase(&mut c)?),
        1 => Body::Private {
            holder: c.u16()?,
            message: private_send_store::decode_message(&c.bytes()?)?,
        },
        2 => Body::Transfer {
            receiver: c.u16()?,
            holder: c.u16()?,
            values: fields(&mut c)?,
            proof: c.bytes()?,
        },
        _ => return Err(bad("dZK wire tag")),
    };
    c.finish()?;
    let m = Message { context, body };
    if encode_message(&m) != b {
        return Err(bad("dZK wire canonical"));
    }
    Ok(m)
}
fn outbox(ps: &[Send]) -> Vec<u8> {
    let mut b = vec![];
    Nat::new(ps.len() as u64).put(&mut b);
    for s in ps {
        b.extend(s.to.to_le_bytes());
        bytes(&encode_message(&s.message), &mut b);
    }
    b
}
fn parse_outbox(b: &[u8], n: usize) -> Result<Vec<Send>> {
    let mut c = Cursor::new(b)?;
    let count = count(&mut c)?;
    if count > crate::codec::MAX / 40 {
        return Err(bad("dZK outbox capacity"));
    }
    let mut out = vec![];
    for _ in 0..count {
        let to = c.u16()?;
        if to as usize >= n {
            return Err(bad("dZK outbox recipient"));
        }
        out.push(Send {
            to,
            message: decode_message(&c.bytes()?)?,
        });
    }
    c.finish()?;
    if outbox(&out) != b {
        return Err(bad("dZK outbox canonical"));
    }
    Ok(out)
}
#[derive(Clone)]
pub struct DzkMachine {
    pub state: Dzk,
}
impl Machine for DzkMachine {
    fn apply(&mut self, event: &[u8]) -> Result<Vec<u8>> {
        let mut c = Cursor::new(event)?;
        let out = match c.byte()? {
            0 => {
                let seed = c.fixed32()?;
                let n = count(&mut c)?;
                if n != self.state.profile.count {
                    return Err(bad("dZK event polynomial count"));
                }
                let mut polys = vec![];
                for _ in 0..n {
                    let p = fields(&mut c)?;
                    if p.len() != self.state.profile.degree + 1 {
                        return Err(bad("dZK event polynomial degree"));
                    }
                    polys.push(p);
                }
                c.finish()?;
                self.state.dealer(&polys, seed)?
            }
            1 => {
                let holder = c.u16()?;
                let receiver = c.u16()?;
                c.finish()?;
                self.state.authorize_verification(holder, receiver)?
            }
            2 => {
                let sender = c.u16()?;
                let message = decode_message(&c.bytes()?)?;
                c.finish()?;
                self.state.receive(sender, message)?
            }
            3 => {
                let receiver = c.u16()?;
                let values = fields(&mut c)?;
                c.finish()?;
                self.state.transfer(receiver, &values)?.1
            }
            _ => return Err(bad("dZK event tag")),
        };
        Ok(outbox(&out))
    }
}
pub struct Store {
    journal: Journal<DzkMachine>,
}
impl Store {
    pub fn open(
        path: &Path,
        me: u16,
        dealer: u16,
        n: usize,
        f: usize,
        g: &Generation,
        polynomial_count: usize,
        degree: usize,
    ) -> Result<Self> {
        let state = Dzk::new(me, dealer, n, f, g, polynomial_count, degree)?;
        let mut identity = b"DREGG.DZK.PARTY.WAL.V1".to_vec();
        g.put(&mut identity);
        identity.extend(state.profile.context);
        identity.extend(me.to_le_bytes());
        Ok(Self {
            journal: Journal::open(path, &identity, DzkMachine { state })?,
        })
    }
    pub fn state(&self) -> &Dzk {
        &self.journal.state().state
    }
    fn apply(&mut self, event: &[u8]) -> Result<Vec<Send>> {
        let b = self.journal.append(event)?;
        parse_outbox(&b, self.state().profile.n)
    }
    /// Exact retry replays retained packets and NEVER regenerates proof randomness.
    pub fn dealer(&mut self, polys: &[Vec<Field>]) -> Result<Vec<Send>> {
        if let Some(original) = self.state().dealer_inputs() {
            if polys != original {
                return Err(bad("dZK changed dealer replay"));
            }
            return self.replay_outboxes();
        }
        if self.state().me != self.state().profile.dealer {
            return Err(bad("dZK not dealer"));
        }
        let mut seed = [0; 32];
        File::open("/dev/urandom")?.read_exact(&mut seed)?;
        let mut event = vec![0];
        event.extend(seed);
        Nat::new(polys.len() as u64).put(&mut event);
        for p in polys {
            put_fields(p, &mut event);
        }
        self.apply(&event)
    }
    pub fn authorize_verification(&mut self, holder: u16, receiver: u16) -> Result<Vec<Send>> {
        let mut e = vec![1];
        e.extend(holder.to_le_bytes());
        e.extend(receiver.to_le_bytes());
        self.apply(&e)
    }
    pub fn receive(&mut self, sender: u16, m: &Message) -> Result<Vec<Send>> {
        let mut e = vec![2];
        e.extend(sender.to_le_bytes());
        bytes(&encode_message(m), &mut e);
        self.apply(&e)
    }
    pub fn transfer(
        &mut self,
        receiver: u16,
        values: &[Field],
    ) -> Result<(Transferred, Vec<Send>)> {
        let receipt = self.state().transfer(receiver, values)?.0;
        let mut e = vec![3];
        e.extend(receiver.to_le_bytes());
        put_fields(values, &mut e);
        Ok((receipt, self.apply(&e)?))
    }
    pub fn verify_private(&self, holder: u16, values: &[Field]) -> Result<Verification> {
        self.state().verify_private(holder, values)
    }
    pub fn open_proof(&self, holder: u16, values: &[Field]) -> Result<OpenProof> {
        self.state().open_proof(holder, values)
    }
    pub fn replay_outboxes(&self) -> Result<Vec<Send>> {
        let mut out = vec![];
        for b in self.journal.replay_outboxes() {
            out.extend(parse_outbox(b, self.state().profile.n)?);
        }
        Ok(out)
    }
}
#[cfg(test)]
mod tests {
    use super::*;
    use std::{
        collections::VecDeque,
        fs,
        time::{SystemTime, UNIX_EPOCH},
    };
    fn g() -> Generation {
        Generation {
            invocation: Nat::new(91),
            command: vec![9],
            attempt: Nat::new(0),
            generation: Nat::new(1),
            configuration: Nat::new(7),
        }
    }
    fn root() -> std::path::PathBuf {
        let p = std::env::temp_dir().join(format!(
            "mini-dzk-{}-{}",
            std::process::id(),
            SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        ));
        fs::create_dir(&p).unwrap();
        p
    }
    #[test]
    fn store_retains_proof_randomness_and_outboxes_and_refuses_changed_identity() {
        let root = root();
        let path = root.join("wal");
        let polynomials = vec![vec![Field(42), Field(17)]];
        let first;
        {
            let mut store = Store::open(&path, 0, 0, 4, 1, &g(), 1, 1).unwrap();
            first = store.dealer(&polynomials).unwrap();
            assert_eq!(store.dealer(&polynomials).unwrap(), first);
            assert!(store.dealer(&[vec![Field(99), Field(17)]]).is_err());
        }
        let mut store = Store::open(&path, 0, 0, 4, 1, &g(), 1, 1).unwrap();
        assert_eq!(store.dealer(&polynomials).unwrap(), first);
        assert_eq!(store.replay_outboxes().unwrap(), first);
        drop(store);
        let mut changed = g();
        changed.generation = Nat::new(2);
        assert!(Store::open(&path, 0, 0, 4, 1, &changed, 1, 1).is_err());
        assert!(Store::open(&path, 1, 0, 4, 1, &g(), 1, 1).is_err());
        std::fs::OpenOptions::new()
            .append(true)
            .open(&path)
            .unwrap()
            .write_all(&[7])
            .unwrap();
        assert!(Store::open(&path, 0, 0, 4, 1, &g(), 1, 1).is_err());
    }
    use std::io::Write;
    #[test]
    fn canonical_wire_and_durable_recipient_transfer_replay() {
        let root = root();
        let polys = vec![vec![Field(42), Field(17)]];
        let mut stores: Vec<_> = (0..4)
            .map(|i| Store::open(&root.join(format!("party{i}")), i, 0, 4, 1, &g(), 1, 1).unwrap())
            .collect();
        let mut q: VecDeque<_> = stores[0]
            .dealer(&polys)
            .unwrap()
            .into_iter()
            .map(|s| (0, s))
            .collect();
        let mut events = 0;
        while let Some((sender, s)) = q.pop_back() {
            events += 1;
            assert!(events < 50000);
            let frame = encode_message(&s.message);
            assert_eq!(decode_message(&frame).unwrap(), s.message);
            let mut long = frame.clone();
            long.push(0);
            assert!(decode_message(&long).is_err());
            let out = stores[s.to as usize].receive(sender, &s.message).unwrap();
            q.extend(out.into_iter().map(|p| (s.to, p)));
        }
        assert!(stores.iter().all(|s| s.state().delivered().is_some()));
        let values = vec![Field(42).add(Field(17).mul(Field(2)))];
        let (_, ps) = stores[1].transfer(2, &values).unwrap();
        for s in ps {
            stores[2].receive(1, &s.message).unwrap();
        }
        assert_eq!(stores[2].state().transferred(1).unwrap().values(), values);
        let expected = stores[2].replay_outboxes().unwrap();
        drop(stores);
        let reopened = Store::open(&root.join("party2"), 2, 0, 4, 1, &g(), 1, 1).unwrap();
        assert_eq!(reopened.replay_outboxes().unwrap(), expected);
        assert_eq!(reopened.state().transferred(1).unwrap().values(), values);
    }
}
