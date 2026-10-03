//! Crash-durable recipient-private delivery driver. Generic transition WAL stores
//! coefficients/plaintext/recipient requests and exact outbox before sending.
//! Honest crash storage + confidential authenticated channel + actual external
//! source authorization are premises; this file is not the native authority join.
use crate::{
    asks::{self, PhaseMessage},
    codec::{bad, bytes, Generation, Nat},
    consensus_wire::Cursor,
    private_send::{Body, Message, PrivateSend, Send},
    reconstruction::Field,
    transition_journal::{Journal, Machine},
};
use std::{
    fs::File,
    io::{Read, Result},
    path::Path,
};
fn put_phase(p: &PhaseMessage, b: &mut Vec<u8>) {
    let (t, v) = match p {
        PhaseMessage::Init(v) => (0, v),
        PhaseMessage::Echo(v) => (1, v),
        PhaseMessage::Ready(v) => (2, v),
    };
    b.push(t);
    bytes(v, b)
}
fn get_phase(c: &mut Cursor) -> Result<PhaseMessage> {
    let t = c.byte()?;
    let v = c.bytes()?;
    match t {
        0 => Ok(PhaseMessage::Init(v)),
        1 => Ok(PhaseMessage::Echo(v)),
        2 => Ok(PhaseMessage::Ready(v)),
        _ => Err(bad("private phase")),
    }
}
pub fn encode_message(m: &Message) -> Vec<u8> {
    let mut b = b"DREGG.PRIVATE.SEND.WIRE\x01".to_vec();
    b.extend(m.context);
    match &m.body {
        Body::Key(p) => {
            b.push(0);
            bytes(&asks::encode_message(p), &mut b)
        }
        Body::Cipher(p) => {
            b.push(1);
            put_phase(p, &mut b)
        }
        Body::Request {
            receiver,
            requester,
            phase,
        } => {
            b.push(2);
            b.extend(receiver.to_le_bytes());
            b.extend(requester.to_le_bytes());
            put_phase(phase, &mut b)
        }
        Body::Transfer { receiver, share } => {
            b.push(3);
            b.extend(receiver.to_le_bytes());
            Nat::new(share.len() as u64).put(&mut b);
            for w in share {
                b.extend(w.0.to_le_bytes());
            }
        }
    }
    b
}
pub fn decode_message(b: &[u8]) -> Result<Message> {
    let mut c = Cursor::new(b)?;
    let frame = b"DREGG.PRIVATE.SEND.WIRE\x01";
    if c.take(frame.len())? != frame {
        return Err(bad("private wire domain"));
    }
    let context = c.fixed32()?;
    let body = match c.byte()? {
        0 => Body::Key(asks::decode_message(&c.bytes()?)?),
        1 => Body::Cipher(get_phase(&mut c)?),
        2 => Body::Request {
            receiver: c.u16()?,
            requester: c.u16()?,
            phase: get_phase(&mut c)?,
        },
        3 => {
            let receiver = c.u16()?;
            if c.take(2)? != [2, 255] {
                return Err(bad("private opening coordinate count"));
            }
            let share = vec![
                Field(u128::from_le_bytes(c.take(16)?.try_into().unwrap())),
                Field(u128::from_le_bytes(c.take(16)?.try_into().unwrap())),
            ];
            Body::Transfer { receiver, share }
        }
        _ => return Err(bad("private wire tag")),
    };
    c.finish()?;
    let m = Message { context, body };
    if encode_message(&m) != b {
        return Err(bad("private wire canonical"));
    }
    Ok(m)
}
fn outbox(ps: &[Send]) -> Vec<u8> {
    let mut b = vec![];
    Nat::new(ps.len() as u64).put(&mut b);
    for p in ps {
        b.extend(p.to.to_le_bytes());
        bytes(&encode_message(&p.message), &mut b)
    }
    b
}
fn parse_outbox(b: &[u8], n: usize) -> Result<Vec<Send>> {
    let mut c = Cursor::new(b)?;
    let mut digits = vec![];
    loop {
        let x = c.byte()?;
        digits.push(x);
        if x == 255 {
            break;
        }
    }
    let mut r = crate::codec::Reader::new(&digits)?;
    let count = r.count()?;
    r.finish()?;
    if count > crate::codec::MAX / 50 {
        return Err(bad("private outbox count"));
    }
    let mut ps = vec![];
    for _ in 0..count {
        let to = c.u16()?;
        if to as usize >= n {
            return Err(bad("private outbox recipient"));
        }
        ps.push(Send {
            to,
            message: decode_message(&c.bytes()?)?,
        })
    }
    c.finish()?;
    if outbox(&ps) != b {
        return Err(bad("private outbox canonical"));
    }
    Ok(ps)
}
#[derive(Clone)]
pub struct DeliveryMachine {
    pub state: PrivateSend,
}
impl Machine for DeliveryMachine {
    fn apply(&mut self, event: &[u8]) -> Result<Vec<u8>> {
        let mut c = Cursor::new(event)?;
        let ps = match c.byte()? {
            0 => {
                let m = c.bytes()?;
                let mut ps = vec![];
                for _ in 0..2 {
                    let mut p = vec![];
                    for _ in 0..=self.state.f {
                        p.push(Field(u128::from_le_bytes(c.take(16)?.try_into().unwrap())))
                    }
                    ps.push(p)
                }
                c.finish()?;
                self.state.dealer_with_coefficients(&m, &ps)?
            }
            1 => {
                let receiver = c.u16()?;
                c.finish()?;
                self.state.request_delivery(receiver)?
            }
            2 => {
                let sender = c.u16()?;
                let m = decode_message(&c.bytes()?)?;
                c.finish()?;
                self.state.receive(sender, m)?
            }
            _ => return Err(bad("private delivery event")),
        };
        Ok(outbox(&ps))
    }
}
pub struct Store {
    journal: Journal<DeliveryMachine>,
}
impl Store {
    pub fn open(
        path: &Path,
        me: u16,
        dealer: u16,
        n: usize,
        f: usize,
        g: &Generation,
        length: usize,
    ) -> Result<Self> {
        let state = PrivateSend::new(me, dealer, n, f, g, length)?;
        let mut identity = b"DREGG.PRIVATE.DELIVERY.PARTY.V1".to_vec();
        g.put(&mut identity);
        identity.extend(me.to_le_bytes());
        identity.extend(dealer.to_le_bytes());
        identity.extend((n as u64).to_le_bytes());
        identity.extend((f as u64).to_le_bytes());
        identity.extend((length as u64).to_le_bytes());
        Ok(Self {
            journal: Journal::open(path, &identity, DeliveryMachine { state })?,
        })
    }
    pub fn state(&self) -> &PrivateSend {
        &self.journal.state().state
    }
    fn apply(&mut self, event: &[u8]) -> Result<Vec<Send>> {
        let b = self.journal.append(event)?;
        parse_outbox(&b, self.state().n)
    }
    pub fn dealer(&mut self, m: &[u8]) -> Result<Vec<Send>> {
        let mut b = vec![0];
        bytes(m, &mut b);
        let mut coeff = vec![0u8; 2 * (self.state().f + 1) * 16];
        File::open("/dev/urandom")?.read_exact(&mut coeff)?;
        b.extend(coeff);
        self.apply(&b)
    }
    pub fn request_delivery(&mut self, r: u16) -> Result<Vec<Send>> {
        let mut b = vec![1];
        b.extend(r.to_le_bytes());
        self.apply(&b)
    }
    pub fn receive(&mut self, sender: u16, m: &Message) -> Result<Vec<Send>> {
        let mut b = vec![2];
        b.extend(sender.to_le_bytes());
        bytes(&encode_message(m), &mut b);
        self.apply(&b)
    }
    pub fn replay_outboxes(&self) -> Result<Vec<Send>> {
        let mut ps = vec![];
        for b in self.journal.replay_outboxes() {
            ps.extend(parse_outbox(b, self.state().n)?)
        }
        Ok(ps)
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
            command: vec![9],
            attempt: Nat::new(0),
            generation: Nat::new(1),
            configuration: Nat::new(7),
        }
    }
    fn path() -> std::path::PathBuf {
        let p = std::env::temp_dir().join(format!(
            "mini-private-delivery-{}-{}",
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
    fn dropped_reply_replays_identical_ciphertext_and_key_shares() {
        let p = path();
        let original;
        {
            let mut s = Store::open(&p, 0, 0, 4, 1, &g(), 64).unwrap();
            original = s.dealer(&[61; 64]).unwrap();
        }
        let mut s = Store::open(&p, 0, 0, 4, 1, &g(), 64).unwrap();
        assert_eq!(s.replay_outboxes().unwrap(), original);
        assert!(s.dealer(&[62; 64]).is_err());
    }
    #[test]
    fn transfer_wire_roundtrip_and_trailing_rejection() {
        let m = Message {
            context: [7; 32],
            body: Body::Transfer {
                receiver: 2,
                share: vec![Field(u128::MAX), Field(7)],
            },
        };
        assert_eq!(decode_message(&encode_message(&m)).unwrap(), m);
        let mut b = encode_message(&m);
        b.push(0);
        assert!(decode_message(&b).is_err());
    }
}
