//! Hash-bound reconstruction of an already committed, coherently shared vector.
//! This is NOT AVSS qualification, a common coin, or an AMPC implementation:
//! those protocols must establish binding, hiding and availability of the exact
//! manifest before admitting it. Exhaustive subsets are bounded to n<=16.
use crate::{
    codec::{bad, Generation},
    custody::hash,
};
use std::io::{Error, ErrorKind, Result};
/// GF(2^128), reduction x^128+x^7+x^2+x+1. This reference arithmetic is
/// functional, not a constant-time implementation for online secret computation.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Field(pub u128);
impl Field {
    pub fn add(self, b: Self) -> Self {
        Self(self.0 ^ b.0)
    }
    pub fn mul(self, b: Self) -> Self {
        let (mut a, mut b, mut z) = (self.0, b.0, 0u128);
        for _ in 0..128 {
            if b & 1 != 0 {
                z ^= a;
            }
            let high = a >> 127;
            a <<= 1;
            if high != 0 {
                a ^= 0x87;
            }
            b >>= 1;
        }
        Self(z)
    }
    pub fn inv(self) -> Result<Self> {
        if self.0 == 0 {
            return Err(bad("zero inverse"));
        }
        let mut x = Self(1);
        let mut a = self;
        let mut e = u128::MAX - 1;
        while e > 0 {
            if e & 1 != 0 {
                x = x.mul(a);
            }
            a = a.mul(a);
            e >>= 1;
        }
        Ok(x)
    }
}
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Share {
    pub generation: Generation,
    pub holder: u16,
    pub words: Vec<Field>,
}
/// The complete native descriptor remains exact opaque source canonical bytes;
/// its cryptographic fingerprint is not used as equality or authority.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RecoveryBinding {
    pub generation: Generation,
    pub descriptor_bytes: Vec<u8>,
    pub holders: Vec<u16>,
    pub f: usize,
    pub word_count: usize,
    pub secret_commitment: [u8; 32],
}
impl RecoveryBinding {
    pub fn validate(&self) -> Result<()> {
        let n = self.holders.len();
        if n != 3 * self.f + 1
            || n > 16
            || self.word_count < 2
            || self.word_count > 4096
            || self.descriptor_bytes.is_empty()
            || self
                .holders
                .iter()
                .enumerate()
                .any(|(i, x)| self.holders[..i].contains(x))
        {
            return Err(bad("unsupported/invalid recovery access structure"));
        }
        Ok(())
    }
    fn commitment(&self, words: &[Field]) -> [u8; 32] {
        let mut b = b"DREGG.PRIVATE.COMMITTED.VECTOR\x01".to_vec();
        self.generation.put(&mut b);
        crate::codec::bytes(&self.descriptor_bytes, &mut b);
        b.extend((self.f as u64).to_le_bytes());
        b.extend((self.holders.len() as u64).to_le_bytes());
        for h in &self.holders {
            b.extend(h.to_le_bytes());
        }
        b.extend((words.len() as u64).to_le_bytes());
        for w in words {
            b.extend(w.0.to_le_bytes());
        }
        hash(&b)
    }
}
/// Used by provisioning experiments only. The coefficients must come from a real
/// jointly generated high-entropy sharing before this can qualify private custody.
pub fn dealer_shares(
    binding: &mut RecoveryBinding,
    polynomials: &[Vec<Field>],
) -> Result<Vec<Share>> {
    binding.validate()?;
    if polynomials.len() != binding.word_count
        || polynomials.iter().any(|p| p.len() != binding.f + 1)
    {
        return Err(bad("polynomial dimensions"));
    }
    let secret: Vec<_> = polynomials.iter().map(|p| p[0]).collect();
    binding.secret_commitment = binding.commitment(&secret);
    Ok(binding
        .holders
        .iter()
        .map(|h| {
            let x = Field(*h as u128 + 1); // Never the dangerous zero-based replica seam.
            let words = polynomials
                .iter()
                .map(|p| p.iter().rev().fold(Field(0), |z, c| z.mul(x).add(*c)))
                .collect();
            Share {
                generation: binding.generation.clone(),
                holder: *h,
                words,
            }
        })
        .collect())
}
fn interpolate(shares: &[&Share], words: usize) -> Result<Vec<Field>> {
    let mut out = vec![Field(0); words];
    for (i, s) in shares.iter().enumerate() {
        let xi = Field(s.holder as u128 + 1);
        let mut coefficient = Field(1);
        for (j, t) in shares.iter().enumerate() {
            if i != j {
                let xj = Field(t.holder as u128 + 1);
                coefficient = coefficient.mul(xj).mul(xi.add(xj).inv()?);
            }
        }
        for (k, w) in s.words.iter().enumerate() {
            out[k] = out[k].add(coefficient.mul(*w));
        }
    }
    Ok(out)
}
/// Unique committed payload from n-f arrivals tolerates f arbitrary corrupt
/// vectors IF at least f+1 honest arrivals lie on the same degree-f sharing.
/// Collision resistance binds payload; it does not manufacture that premise.
/// The first two words are secret entropy for hiding (256-bit random salt), not
/// an omitted/default-zero pad. Qualified generation must certify that entropy.
pub fn recover(binding: &RecoveryBinding, shares: &[Share]) -> Result<Vec<Field>> {
    binding.validate()?;
    let n = binding.holders.len();
    if shares.len() < n - binding.f {
        return Err(Error::new(
            ErrorKind::WouldBlock,
            "recover same generation: wait for n-f shares",
        ));
    }
    if shares.len() > n {
        return Err(bad("too many holders"));
    }
    for (i, s) in shares.iter().enumerate() {
        if s.generation != binding.generation
            || s.words.len() != binding.word_count
            || !binding.holders.contains(&s.holder)
            || shares[..i].iter().any(|t| t.holder == s.holder)
        {
            return Err(bad(
                "mixed generation, dimensions, or duplicate/foreign holder",
            ));
        }
    }
    let threshold = binding.f + 1;
    let mut recovered = None;
    // Finite physical bound. No first-threshold raw interpolation.
    for mask in 0u32..(1u32 << shares.len()) {
        if mask.count_ones() as usize != threshold {
            continue;
        }
        let subset: Vec<_> = shares
            .iter()
            .enumerate()
            .filter_map(|(i, s)| if mask & (1 << i) != 0 { Some(s) } else { None })
            .collect();
        let candidate = interpolate(&subset, binding.word_count)?;
        if binding.commitment(&candidate) == binding.secret_commitment {
            if recovered.as_ref().is_some_and(|old| old != &candidate) {
                return Err(bad("commitment collision/equivocation"));
            }
            recovered = Some(candidate);
        }
    }
    recovered.ok_or_else(|| bad("no coherent committed secret; custody not qualified"))
}
/// Stock exhaustion is explicit. Refresh/repair never becomes a new generation
/// simply by relabeling the same binding or spent correlation.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum StockState {
    Available,
    AwaitIndependentRefill,
}
pub fn stock_state(unspent: usize) -> StockState {
    if unspent == 0 {
        StockState::AwaitIndependentRefill
    } else {
        StockState::Available
    }
}
#[cfg(test)]
mod tests {
    use super::*;
    use crate::codec::Nat;
    fn fixture() -> (RecoveryBinding, Vec<Share>, Vec<Field>) {
        let g = Generation {
            invocation: Nat::new(7),
            command: vec![9],
            attempt: Nat::new(2),
            generation: Nat::new(3),
            configuration: Nat::new(4),
        };
        let mut b = RecoveryBinding {
            generation: g,
            descriptor_bytes: vec![5, 6, 7],
            holders: vec![0, 1, 2, 3],
            f: 1,
            word_count: 3,
            secret_commitment: [0; 32],
        };
        let secret = vec![Field(0x1234567), Field(0x898989), Field(42)];
        let p = vec![
            vec![secret[0], Field(1)],
            vec![secret[1], Field(7)],
            vec![secret[2], Field(17)],
        ];
        let shares = dealer_shares(&mut b, &p).unwrap();
        (b, shares, secret)
    }
    #[test]
    fn field_inverse_and_points() {
        for v in [1, 2, 7, 255, u128::MAX] {
            assert_eq!(Field(v).mul(Field(v).inv().unwrap()), Field(1));
        }
        assert!(Field(0).inv().is_err());
    }
    #[test]
    fn vanished_dealer_and_byzantine_withhold() {
        let (b, s, secret) = fixture();
        assert_eq!(recover(&b, &s[1..]).unwrap(), secret);
    }
    #[test]
    fn corrupt_first_share_refused_or_corrected() {
        let (b, mut s, secret) = fixture();
        s[0].words[2] = Field(100);
        let raw = interpolate(&[&s[0], &s[1]], 3).unwrap();
        assert_ne!(raw, secret);
        assert_eq!(recover(&b, &s[..3]).unwrap(), secret);
    }
    #[test]
    fn mixed_generation_and_descriptor_refuse() {
        let (b, mut s, _) = fixture();
        s[0].generation.generation = Nat::new(4);
        assert!(recover(&b, &s[..3]).is_err());
        let (b, s, _) = fixture();
        let mut different = b.clone();
        different.descriptor_bytes.push(8);
        assert!(recover(&different, &s[..3]).is_err());
    }
    #[test]
    fn omitted_or_default_zero_pad_refuses() {
        let (b, mut s, _) = fixture();
        s[0].words.clear();
        assert!(recover(&b, &s[..3]).is_err());
        let (b, mut s, _) = fixture();
        for share in &mut s {
            share.words = vec![Field(0); 3];
        }
        assert!(recover(&b, &s[..3]).is_err());
        assert_eq!(stock_state(0), StockState::AwaitIndependentRefill);
    }
    #[test]
    fn zero_based_coin_is_replica_zero_share() {
        let (b, s, secret) = fixture();
        let wrong = s[0].words.clone();
        assert_ne!(wrong, secret);
        assert_eq!(wrong[2], secret[2].add(Field(17)));
        assert_eq!(recover(&b, &s[..3]).unwrap(), secret);
    }
    #[test]
    fn duplicate_and_waiting_are_explicit() {
        let (b, s, _) = fixture();
        assert_eq!(
            recover(&b, &s[..2]).unwrap_err().kind(),
            ErrorKind::WouldBlock
        );
        assert!(recover(&b, &[s[0].clone(), s[0].clone(), s[1].clone()]).is_err());
    }
}
