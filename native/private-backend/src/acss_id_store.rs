//! Crash-durable ACSS-Id: fixed input polynomials/seed, actual messages,
//! source-environment public reconstruction/open requests, exact outbox replay.
//! Honest crash disk only; this store does not authorize declassification.
use crate::{
    acss_id::{AcssId, Body, Message, Send},
    asks::PhaseMessage,
    codec::{bad, bytes, Generation, Nat, Reader},
    consensus_wire::Cursor,
    dzk_store, private_send_store,
    reconstruction::Field,
    transition_journal::{Journal, Machine},
};
use std::{
    fs::File,
    io::{Read, Result},
    path::Path,
};
pub(crate) fn count(c: &mut Cursor<'_>) -> Result<usize> {
    let mut b = vec![];
    loop {
        let v = c.byte()?;
        b.push(v);
        if v == 255 {
            break;
        }
    }
    let mut r = Reader::new(&b)?;
    let n = r.count()?;
    r.finish()?;
    Ok(n)
}
fn put_phase(p: &PhaseMessage, b: &mut Vec<u8>) {
    let (t, v) = match p {
        PhaseMessage::Init(v) => (0, v),
        PhaseMessage::Echo(v) => (1, v),
        PhaseMessage::Ready(v) => (2, v),
    };
    b.push(t);
    bytes(v, b);
}
fn phase(c: &mut Cursor<'_>) -> Result<PhaseMessage> {
    let t = c.byte()?;
    let v = c.bytes()?;
    match t {
        0 => Ok(PhaseMessage::Init(v)),
        1 => Ok(PhaseMessage::Echo(v)),
        2 => Ok(PhaseMessage::Ready(v)),
        _ => Err(bad("ACSS phase")),
    }
}
pub fn encode_message(m: &Message) -> Vec<u8> {
    let mut b = b"DREGG.ACSS.ID.WIRE\x01".to_vec();
    b.extend(m.context);
    match &m.body {
        Body::Row { holder, message } => {
            b.push(0);
            b.extend(holder.to_le_bytes());
            bytes(&private_send_store::encode_message(message), &mut b);
        }
        Body::Column { column, message } => {
            b.push(1);
            b.extend(column.to_le_bytes());
            bytes(&dzk_store::encode_message(message), &mut b);
        }
        Body::Termination(p) => {
            b.push(2);
            put_phase(p, &mut b);
        }
        Body::Complaint { holder, phase } => {
            b.push(3);
            b.extend(holder.to_le_bytes());
            put_phase(phase, &mut b);
        }
        Body::OpenRequest {
            holder,
            requester,
            phase,
        } => {
            b.push(4);
            b.extend(holder.to_le_bytes());
            b.extend(requester.to_le_bytes());
            put_phase(phase, &mut b);
        }
        Body::ReconstructionRequest { requester, phase } => {
            b.push(5);
            b.extend(requester.to_le_bytes());
            put_phase(phase, &mut b);
        }
        Body::PublicColumn { column, values } => {
            b.push(6);
            b.extend(column.to_le_bytes());
            Nat::new(values.len() as u64).put(&mut b);
            for v in values {
                b.extend(v.0.to_le_bytes());
            }
        }
    }
    b
}
pub fn decode_message(b: &[u8]) -> Result<Message> {
    let mut c = Cursor::new(b)?;
    let frame = b"DREGG.ACSS.ID.WIRE\x01";
    if c.take(frame.len())? != frame {
        return Err(bad("ACSS wire domain"));
    }
    let context = c.fixed32()?;
    let body = match c.byte()? {
        0 => Body::Row {
            holder: c.u16()?,
            message: private_send_store::decode_message(&c.bytes()?)?,
        },
        1 => Body::Column {
            column: c.u16()?,
            message: dzk_store::decode_message(&c.bytes()?)?,
        },
        2 => Body::Termination(phase(&mut c)?),
        3 => Body::Complaint {
            holder: c.u16()?,
            phase: phase(&mut c)?,
        },
        4 => Body::OpenRequest {
            holder: c.u16()?,
            requester: c.u16()?,
            phase: phase(&mut c)?,
        },
        5 => Body::ReconstructionRequest {
            requester: c.u16()?,
            phase: phase(&mut c)?,
        },
        6 => {
            let column = c.u16()?;
            let n = count(&mut c)?;
            if n > 128 {
                return Err(bad("public column vector bound"));
            }
            let values = (0..n)
                .map(|_| Ok(Field(u128::from_le_bytes(c.take(16)?.try_into().unwrap()))))
                .collect::<Result<_>>()?;
            Body::PublicColumn { column, values }
        }
        _ => return Err(bad("ACSS wire tag")),
    };
    c.finish()?;
    let m = Message { context, body };
    if encode_message(&m) != b {
        return Err(bad("ACSS canonical wire"));
    }
    Ok(m)
}
fn outbox(ps: &[Send]) -> Vec<u8> {
    let mut b = vec![];
    Nat::new(ps.len() as u64).put(&mut b);
    for p in ps {
        b.extend(p.to.to_le_bytes());
        bytes(&encode_message(&p.message), &mut b);
    }
    b
}
pub(crate) fn parse_outbox(b: &[u8], n: usize) -> Result<Vec<Send>> {
    let mut c = Cursor::new(b)?;
    let len = count(&mut c)?;
    if len > crate::codec::MAX / 40 {
        return Err(bad("ACSS outbox bound"));
    }
    let mut out = vec![];
    for _ in 0..len {
        let to = c.u16()?;
        if to as usize >= n {
            return Err(bad("ACSS outbox recipient"));
        }
        out.push(Send {
            to,
            message: decode_message(&c.bytes()?)?,
        });
    }
    c.finish()?;
    if outbox(&out) != b {
        return Err(bad("ACSS outbox canonical"));
    }
    Ok(out)
}
/// The journaled dealer event: tag 0, the dealing seed, and every input polynomial.
pub(crate) fn dealer_event(seed: [u8; 32], polys: &[Vec<Field>]) -> Vec<u8> {
    let mut e = vec![0];
    e.extend(seed);
    Nat::new(polys.len() as u64).put(&mut e);
    for p in polys {
        for v in p {
            e.extend(v.0.to_le_bytes());
        }
    }
    e
}
#[derive(Clone)]
pub struct AcssMachine {
    pub state: AcssId,
}
impl Machine for AcssMachine {
    fn apply(&mut self, e: &[u8]) -> Result<Vec<u8>> {
        let mut c = Cursor::new(e)?;
        let out = match c.byte()? {
            0 => {
                let seed = c.fixed32()?;
                let n = count(&mut c)?;
                if n != self.state.count {
                    return Err(bad("ACSS dealer polynomial count"));
                }
                let mut polys = vec![];
                for _ in 0..n {
                    let mut p = vec![];
                    for _ in 0..=self.state.f {
                        p.push(Field(u128::from_le_bytes(c.take(16)?.try_into().unwrap())));
                    }
                    polys.push(p);
                }
                c.finish()?;
                self.state.dealer(&polys, seed)?
            }
            1 => {
                let holder = c.u16()?;
                c.finish()?;
                self.state.request_open(holder)?
            }
            2 => {
                let sender = c.u16()?;
                let m = decode_message(&c.bytes()?)?;
                c.finish()?;
                self.state.receive(sender, m)?
            }
            3 => {
                c.finish()?;
                self.state.request_public_reconstruction()?
            }
            _ => return Err(bad("ACSS event tag")),
        };
        Ok(outbox(&out))
    }
}
pub struct Store {
    journal: Journal<AcssMachine>,
}
impl Store {
    pub fn open(
        path: &Path,
        me: u16,
        dealer: u16,
        n: usize,
        f: usize,
        g: &Generation,
        count: usize,
    ) -> Result<Self> {
        let state = AcssId::new(me, dealer, n, f, g, count)?;
        let mut id = b"DREGG.ACSS.ID.PARTY.WAL.V1".to_vec();
        g.put(&mut id);
        id.extend(state.context);
        id.extend(me.to_le_bytes());
        Ok(Self {
            journal: Journal::open(path, &id, AcssMachine { state })?,
        })
    }
    pub fn state(&self) -> &AcssId {
        &self.journal.state().state
    }
    fn apply(&mut self, e: &[u8]) -> Result<Vec<Send>> {
        let b = self.journal.append(e)?;
        parse_outbox(&b, self.state().n)
    }
    pub fn dealer(&mut self, polys: &[Vec<Field>]) -> Result<Vec<Send>> {
        if polys.len() != self.state().count || polys.iter().any(|p| p.len() != self.state().f + 1)
        {
            return Err(bad("ACSS dealer inputs"));
        }
        let mut seed = [0; 32];
        File::open("/dev/urandom")?.read_exact(&mut seed)?;
        let e = dealer_event(seed, polys);
        self.apply(&e)
    }
    pub fn request_open(&mut self, holder: u16) -> Result<Vec<Send>> {
        let mut e = vec![1];
        e.extend(holder.to_le_bytes());
        self.apply(&e)
    }
    pub fn request_public_reconstruction(&mut self) -> Result<Vec<Send>> {
        self.apply(&[3])
    }
    pub fn receive(&mut self, sender: u16, m: &Message) -> Result<Vec<Send>> {
        let mut e = vec![2];
        e.extend(sender.to_le_bytes());
        bytes(&encode_message(m), &mut e);
        self.apply(&e)
    }
    pub fn replay_outboxes(&self) -> Result<Vec<Send>> {
        let mut out = vec![];
        for b in self.journal.replay_outboxes() {
            out.extend(parse_outbox(b, self.state().n)?);
        }
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
    fn g() -> Generation {
        Generation {
            invocation: Nat::from_be(&[255; 32]),
            command: vec![7],
            attempt: Nat::new(0),
            generation: Nat::new(1),
            configuration: Nat::new(8),
        }
    }
    fn path() -> std::path::PathBuf {
        let p = std::env::temp_dir().join(format!(
            "mini-acss-store-{}-{}",
            std::process::id(),
            SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        ));
        fs::create_dir(&p).unwrap();
        p.join("wal")
    }
    #[test]
    fn dropped_dealer_reply_replays_all_exact_private_rows_and_proofs() {
        let p = path();
        let out;
        {
            let mut s = Store::open(&p, 0, 0, 4, 1, &g(), 2).unwrap();
            out = s
                .dealer(&[vec![Field(42), Field(7)], vec![Field(91), Field(11)]])
                .unwrap();
            assert!(!out.is_empty());
        }
        let mut s = Store::open(&p, 0, 0, 4, 1, &g(), 2).unwrap();
        assert_eq!(s.replay_outboxes().unwrap(), out);
        assert!(s
            .dealer(&[vec![Field(1), Field(2)], vec![Field(3), Field(4)]])
            .is_err());
        drop(s);
        let mut wrong = g();
        wrong.command.push(1);
        assert!(Store::open(&p, 0, 0, 4, 1, &wrong, 2).is_err());
    }
    #[test]
    fn canonical_public_column_and_early_permission_refusals() {
        let m = Message {
            context: [9; 32],
            body: Body::PublicColumn {
                column: 3,
                values: vec![Field(u128::MAX), Field(4)],
            },
        };
        let b = encode_message(&m);
        assert_eq!(decode_message(&b).unwrap(), m);
        let mut t = b;
        t.push(0);
        assert!(decode_message(&t).is_err());
        let p = path();
        let mut s = Store::open(&p, 1, 0, 4, 1, &g(), 2).unwrap();
        let len = fs::metadata(&p).unwrap().len();
        assert!(s.request_open(0).is_err());
        assert!(s.request_public_reconstruction().is_err());
        assert_eq!(fs::metadata(&p).unwrap().len(), len);
    }
}
