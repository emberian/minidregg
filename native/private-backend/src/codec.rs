//! Canonical subset of Compiler.PrivateSuccessorCustodyCodec.
use std::io::{Error, ErrorKind, Result};
pub const MAX: usize = 16 * 1024 * 1024;
pub fn bad(s: &str) -> Error {
    Error::new(ErrorKind::InvalidData, s)
}
#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd)]
pub struct Nat(Vec<u8>);
impl Nat {
    pub fn digits(&self) -> &[u8] {
        &self.0
    }
    pub fn new(mut n: u64) -> Self {
        let mut d = vec![];
        while n > 0 {
            d.push((n % 255) as u8);
            n /= 255;
        }
        Self(d)
    }
    pub fn from_be(b: &[u8]) -> Self {
        let mut d: Vec<u8> = vec![];
        for v in b {
            let mut c = *v as u32;
            for x in &mut d {
                let n = *x as u32 * 256 + c;
                *x = (n % 255) as u8;
                c = n / 255;
            }
            while c > 0 {
                d.push((c % 255) as u8);
                c /= 255;
            }
        }
        Self(d)
    }
    pub fn put(&self, o: &mut Vec<u8>) {
        o.extend(&self.0);
        o.push(255);
    }
    pub fn value(&self) -> Result<u64> {
        self.0.iter().rev().try_fold(0u64, |n, b| {
            n.checked_mul(255)
                .and_then(|x| x.checked_add(*b as u64))
                .ok_or_else(|| bad("physical Nat bound"))
        })
    }
}
pub fn bytes(b: &[u8], o: &mut Vec<u8>) {
    Nat::new(b.len() as u64).put(o);
    o.extend(b);
}
pub struct Reader<'a> {
    b: &'a [u8],
    i: usize,
}
impl<'a> Reader<'a> {
    pub fn new(b: &'a [u8]) -> Result<Self> {
        if b.len() > MAX {
            return Err(bad("frame bound"));
        }
        Ok(Self { b, i: 0 })
    }
    pub fn nat(&mut self) -> Result<Nat> {
        let s = self.i;
        while self.i < self.b.len() && self.b[self.i] != 255 {
            self.i += 1;
        }
        if self.i == self.b.len() {
            return Err(bad("Nat terminator"));
        }
        let d = self.b[s..self.i].to_vec();
        self.i += 1;
        if d.last() == Some(&0) {
            return Err(bad("noncanonical Nat"));
        }
        Ok(Nat(d))
    }
    pub fn bytes(&mut self) -> Result<Vec<u8>> {
        let n = self.count()?;
        let e = self
            .i
            .checked_add(n)
            .ok_or_else(|| bad("length overflow"))?;
        if e > self.b.len() {
            return Err(bad("short bytes"));
        }
        let b = self.b[self.i..e].to_vec();
        self.i = e;
        Ok(b)
    }
    pub fn count(&mut self) -> Result<usize> {
        let n = usize::try_from(self.nat()?.value()?).map_err(|_| bad("length overflow"))?;
        if n > MAX {
            return Err(bad("count bound"));
        }
        Ok(n)
    }
    pub fn finish(self) -> Result<()> {
        if self.i == self.b.len() {
            Ok(())
        } else {
            Err(bad("trailing data"))
        }
    }
}
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Generation {
    pub invocation: Nat,
    pub command: Vec<u8>,
    pub attempt: Nat,
    pub generation: Nat,
    pub configuration: Nat,
}
impl Generation {
    pub fn put(&self, o: &mut Vec<u8>) {
        self.invocation.put(o);
        bytes(&self.command, o);
        self.attempt.put(o);
        self.generation.put(o);
        self.configuration.put(o);
    }
    pub fn get(r: &mut Reader<'_>) -> Result<Self> {
        Ok(Self {
            invocation: r.nat()?,
            command: r.bytes()?,
            attempt: r.nat()?,
            generation: r.nat()?,
            configuration: r.nat()?,
        })
    }
}
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Correlation {
    pub pool: Nat,
    pub row: Nat,
}
impl Correlation {
    pub fn put(&self, o: &mut Vec<u8>) {
        self.pool.put(o);
        self.row.put(o);
    }
    pub fn get(r: &mut Reader<'_>) -> Result<Self> {
        Ok(Self {
            pool: r.nat()?,
            row: r.nat()?,
        })
    }
}
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Purpose {
    Triple = 0,
    Coin = 1,
    HolderPad = 2,
    AudiencePad = 3,
}
fn purpose(n: u64) -> Result<Purpose> {
    match n {
        0 => Ok(Purpose::Triple),
        1 => Ok(Purpose::Coin),
        2 => Ok(Purpose::HolderPad),
        3 => Ok(Purpose::AudiencePad),
        _ => Err(bad("purpose code")),
    }
}
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Allocation {
    pub id: Correlation,
    pub generation: Generation,
    pub purpose: Purpose,
    pub consumed: bool,
}
#[derive(Clone, Debug, Eq, PartialEq, Default)]
pub struct Journal {
    pub spent: Vec<Correlation>,
    pub allocations: Vec<Allocation>,
}
impl Journal {
    pub fn encode(&self) -> Vec<u8> {
        let mut o = vec![];
        bytes(b"DREGG.PRIVATE.CORRELATIONS\x01", &mut o);
        Nat::new(self.spent.len() as u64).put(&mut o);
        for id in &self.spent {
            id.put(&mut o);
        }
        Nat::new(self.allocations.len() as u64).put(&mut o);
        for a in &self.allocations {
            a.id.put(&mut o);
            a.generation.put(&mut o);
            Nat::new(a.purpose as u64).put(&mut o);
            Nat::new(a.consumed as u64).put(&mut o);
        }
        o
    }
    pub fn decode(b: &[u8]) -> Result<Self> {
        let mut r = Reader::new(b)?;
        if r.bytes()? != b"DREGG.PRIVATE.CORRELATIONS\x01" {
            return Err(bad("journal domain/version"));
        }
        let mut j = Self::default();
        for _ in 0..r.count()? {
            j.spent.push(Correlation::get(&mut r)?);
        }
        for _ in 0..r.count()? {
            let id = Correlation::get(&mut r)?;
            let generation = Generation::get(&mut r)?;
            let purpose = purpose(r.nat()?.value()?)?;
            let consumed = match r.nat()?.value()? {
                0 => false,
                1 => true,
                _ => return Err(bad("consumption code")),
            };
            j.allocations.push(Allocation {
                id,
                generation,
                purpose,
                consumed,
            });
        }
        r.finish()?;
        if j.encode() != b
            || j.spent.len() != j.allocations.len()
            || j.allocations.iter().any(|a| !j.spent.contains(&a.id))
            || j.spent
                .iter()
                .enumerate()
                .any(|(i, x)| j.spent[..i].contains(x))
            || j.allocations
                .iter()
                .enumerate()
                .any(|(i, x)| j.allocations[..i].iter().any(|y| x.id == y.id))
        {
            return Err(bad("not canonical reachable journal"));
        }
        Ok(j)
    }
    pub fn reserve(
        &self,
        id: Correlation,
        generation: Generation,
        purpose: Purpose,
    ) -> Result<Self> {
        if self.spent.contains(&id) {
            return Err(Error::new(ErrorKind::AlreadyExists, "spent physical row"));
        }
        let mut j = self.clone();
        j.spent.insert(0, id.clone());
        j.allocations.insert(
            0,
            Allocation {
                id,
                generation,
                purpose,
                consumed: false,
            },
        );
        if j.encode().len() > MAX {
            return Err(bad("journal exhausted: source retirement proof required"));
        }
        Ok(j)
    }
    pub fn extends(&self, old: &Self) -> bool {
        old.spent.iter().all(|id| self.spent.contains(id))
    }
}
pub fn request(id: &Correlation, g: &Generation, p: Purpose) -> Vec<u8> {
    let mut b = vec![];
    id.put(&mut b);
    g.put(&mut b);
    Nat::new(p as u64).put(&mut b);
    b
}
pub fn parse_request(b: &[u8]) -> Result<(Correlation, Generation, Purpose)> {
    let mut r = Reader::new(b)?;
    let id = Correlation::get(&mut r)?;
    let g = Generation::get(&mut r)?;
    let p = purpose(r.nat()?.value()?)?;
    r.finish()?;
    Ok((id, g, p))
}
#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn nat_and_noncanonical() {
        for n in [0, 1, 254, 255, 256, u64::MAX] {
            let mut b = vec![];
            Nat::new(n).put(&mut b);
            assert_eq!(Reader::new(&b).unwrap().nat().unwrap().value().unwrap(), n);
        }
        assert!(Reader::new(&[0, 255]).unwrap().nat().is_err());
    }
    #[test]
    fn lean_empty_fixture() {
        let mut expected = vec![27, 255];
        expected.extend(b"DREGG.PRIVATE.CORRELATIONS\x01");
        expected.extend([255, 255]);
        assert_eq!(Journal::default().encode(), expected);
        assert_eq!(Journal::decode(&expected).unwrap(), Journal::default());
    }
    #[test]
    fn malformed_refuses() {
        let mut b = Journal::default().encode();
        b.push(1);
        assert!(Journal::decode(&b).is_err());
        assert!(Journal::decode(&[]).is_err());
    }
}
