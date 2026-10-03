//! Strict bounded canonical transport encoding. Sender identity comes only
//! from the authenticated channel, never from a payload's claimed broadcaster.
use crate::{
    acs,
    asks::{self, PhaseMessage},
    codec::{bad, bytes},
    gather, vaba,
};
use std::io::Result;
pub(crate) struct Cursor<'a> {
    b: &'a [u8],
    i: usize,
}
impl<'a> Cursor<'a> {
    pub fn new(b: &'a [u8]) -> Result<Self> {
        if b.len() > crate::codec::MAX {
            return Err(bad("wire capacity"));
        }
        Ok(Self { b, i: 0 })
    }
    pub fn take(&mut self, n: usize) -> Result<&'a [u8]> {
        let end = self.i.checked_add(n).ok_or_else(|| bad("wire length"))?;
        if end > self.b.len() {
            return Err(bad("short wire"));
        }
        let b = &self.b[self.i..end];
        self.i = end;
        Ok(b)
    }
    pub fn byte(&mut self) -> Result<u8> {
        Ok(self.take(1)?[0])
    }
    pub fn u16(&mut self) -> Result<u16> {
        Ok(u16::from_le_bytes(self.take(2)?.try_into().unwrap()))
    }
    pub fn u64(&mut self) -> Result<u64> {
        Ok(u64::from_le_bytes(self.take(8)?.try_into().unwrap()))
    }
    pub fn fixed32(&mut self) -> Result<[u8; 32]> {
        Ok(self.take(32)?.try_into().unwrap())
    }
    pub fn bytes(&mut self) -> Result<Vec<u8>> {
        let start = self.i;
        while self.byte()? != 255 {}
        let mut r = crate::codec::Reader::new(&self.b[start..self.i])?;
        let n = r.count()?;
        r.finish()?;
        Ok(self.take(n)?.to_vec())
    }
    pub fn finish(self) -> Result<()> {
        if self.i != self.b.len() {
            return Err(bad("wire trailing bytes"));
        }
        Ok(())
    }
}
fn put_phase(p: &PhaseMessage, o: &mut Vec<u8>) {
    match p {
        PhaseMessage::Init(b) => {
            o.push(0);
            bytes(b, o)
        }
        PhaseMessage::Echo(b) => {
            o.push(1);
            bytes(b, o)
        }
        PhaseMessage::Ready(b) => {
            o.push(2);
            bytes(b, o)
        }
    }
}
fn phase(c: &mut Cursor) -> Result<PhaseMessage> {
    let t = c.byte()?;
    let b = c.bytes()?;
    match t {
        0 => Ok(PhaseMessage::Init(b)),
        1 => Ok(PhaseMessage::Echo(b)),
        2 => Ok(PhaseMessage::Ready(b)),
        _ => Err(bad("wire phase")),
    }
}
fn put_set(s: &vaba::Set, o: &mut Vec<u8>) {
    bytes(&acs::set_bytes(s), o)
}
fn set(c: &mut Cursor, n: usize) -> Result<vaba::Set> {
    acs::read_set(&c.bytes()?, n)
}
fn put_cover(m: &gather::Message, o: &mut Vec<u8>) {
    o.extend(m.context);
    match &m.body {
        gather::Body::Gather(g) => {
            o.push(0);
            match g {
                gather::IgBody::Inform(s) => {
                    o.push(0);
                    put_set(s, o)
                }
                gather::IgBody::Ack => o.push(1),
                gather::IgBody::Prepare(s) => {
                    o.push(2);
                    put_set(s, o)
                }
            }
        }
        gather::Body::Ra(j, p) => {
            o.push(1);
            o.extend(j.to_le_bytes());
            put_phase(p, o)
        }
        gather::Body::Withdraw => o.push(2),
    }
}
fn cover(c: &mut Cursor, n: usize) -> Result<gather::Message> {
    let context = c.fixed32()?;
    let body = match c.byte()? {
        0 => gather::Body::Gather(match c.byte()? {
            0 => gather::IgBody::Inform(set(c, n)?),
            1 => gather::IgBody::Ack,
            2 => gather::IgBody::Prepare(set(c, n)?),
            _ => return Err(bad("gather tag")),
        }),
        1 => gather::Body::Ra(c.u16()?, phase(c)?),
        2 => gather::Body::Withdraw,
        _ => return Err(bad("cover tag")),
    };
    Ok(gather::Message { context, body })
}
pub fn encode_vaba(m: &vaba::Message) -> Vec<u8> {
    let mut o = b"DREGG.VABA.WIRE\x01".to_vec();
    o.extend(m.context);
    o.extend(m.view.to_le_bytes());
    match &m.body {
        vaba::Body::Asks(j, p) => {
            o.push(0);
            o.extend(j.to_le_bytes());
            bytes(&asks::encode_message(p), &mut o)
        }
        vaba::Body::Pre(j, p) => {
            o.push(1);
            o.extend(j.to_le_bytes());
            put_phase(p, &mut o)
        }
        vaba::Body::Vote(j, p) => {
            o.push(2);
            o.extend(j.to_le_bytes());
            put_phase(p, &mut o)
        }
        vaba::Body::Cover(p) => {
            o.push(3);
            put_cover(p, &mut o)
        }
        vaba::Body::Final(p) => {
            o.push(4);
            put_phase(p, &mut o)
        }
    }
    o
}
pub fn decode_vaba(b: &[u8], n: usize) -> Result<vaba::Message> {
    let mut c = Cursor::new(b)?;
    let prefix = b"DREGG.VABA.WIRE\x01";
    if c.take(prefix.len())? != prefix {
        return Err(bad("VABA wire version"));
    }
    let context = c.fixed32()?;
    let view = c.u64()?;
    let body = match c.byte()? {
        0 => vaba::Body::Asks(c.u16()?, asks::decode_message(&c.bytes()?)?),
        1 => vaba::Body::Pre(c.u16()?, phase(&mut c)?),
        2 => vaba::Body::Vote(c.u16()?, phase(&mut c)?),
        3 => vaba::Body::Cover(cover(&mut c, n)?),
        4 => vaba::Body::Final(phase(&mut c)?),
        _ => return Err(bad("VABA body tag")),
    };
    c.finish()?;
    let m = vaba::Message {
        context,
        view,
        body,
    };
    if encode_vaba(&m) != b {
        return Err(bad("noncanonical VABA wire"));
    }
    Ok(m)
}
pub fn encode_acs(m: &acs::Message) -> Vec<u8> {
    let mut o = b"DREGG.ACS.WIRE\x01".to_vec();
    o.extend(m.context);
    match &m.body {
        acs::Body::Selector(j, p) => {
            o.push(0);
            o.extend(j.to_le_bytes());
            put_phase(p, &mut o)
        }
        acs::Body::Vaba(p) => {
            o.push(1);
            bytes(&encode_vaba(p), &mut o)
        }
    }
    o
}
pub fn decode_acs(b: &[u8], n: usize) -> Result<acs::Message> {
    let mut c = Cursor::new(b)?;
    let prefix = b"DREGG.ACS.WIRE\x01";
    if c.take(prefix.len())? != prefix {
        return Err(bad("ACS wire version"));
    }
    let context = c.fixed32()?;
    let body = match c.byte()? {
        0 => acs::Body::Selector(c.u16()?, phase(&mut c)?),
        1 => acs::Body::Vaba(decode_vaba(&c.bytes()?, n)?),
        _ => return Err(bad("ACS body tag")),
    };
    c.finish()?;
    let m = acs::Message { context, body };
    if encode_acs(&m) != b {
        return Err(bad("noncanonical ACS wire"));
    }
    Ok(m)
}
pub fn encode_outbox(ps: &[acs::Send]) -> Vec<u8> {
    let mut o = vec![];
    crate::codec::Nat::new(ps.len() as u64).put(&mut o);
    for p in ps {
        o.extend(p.to.to_le_bytes());
        bytes(&encode_acs(&p.message), &mut o)
    }
    o
}
pub fn decode_outbox(b: &[u8], n: usize) -> Result<Vec<acs::Send>> {
    // Output is trusted local machine data but remains bounded and canonical.
    let mut c = Cursor::new(b)?;
    let start = c.i;
    while c.byte()? != 255 {}
    let mut r = crate::codec::Reader::new(&b[start..c.i])?;
    let count = r.count()?;
    r.finish()?;
    if count > crate::codec::MAX / 48 {
        return Err(bad("outbox packet bound"));
    }
    let mut out = vec![];
    for _ in 0..count {
        let to = c.u16()?;
        if to as usize >= n {
            return Err(bad("outbox recipient"));
        }
        out.push(acs::Send {
            to,
            message: decode_acs(&c.bytes()?, n)?,
        })
    }
    c.finish()?;
    if encode_outbox(&out) != b {
        return Err(bad("outbox canonical"));
    }
    Ok(out)
}
#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn every_boundary_roundtrips_and_trailing_refuses() {
        let vs = [
            vaba::Body::Pre(1, PhaseMessage::Echo(vec![1, 0, 2, 1, 0, 2, 0, 0])),
            vaba::Body::Cover(gather::Message {
                context: [8; 32],
                body: gather::Body::Gather(gather::IgBody::Inform(vaba::Set::from([1, 2, 3]))),
            }),
            vaba::Body::Final(PhaseMessage::Ready(vec![0, 0])),
        ];
        for body in vs {
            let m = acs::Message {
                context: [7; 32],
                body: acs::Body::Vaba(vaba::Message {
                    context: [9; 32],
                    view: 254,
                    body,
                }),
            };
            let b = encode_acs(&m);
            assert_eq!(decode_acs(&b, 4).unwrap(), m);
            let mut bad = b;
            bad.push(0);
            assert!(decode_acs(&bad, 4).is_err());
        }
    }
}
