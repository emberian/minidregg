//! Party-local randomness for dealing and preprocessing.
//!
//! One `Entropy` is one party's private stream: a 32-byte key read from the OS
//! (`/dev/urandom`) or, for a reproducible run, a supplied seed. Output blocks are
//! SHA-256(domain || key || counter) — a classical random-oracle PRG, the same
//! assumption the rest of this reference profile already makes. A fork derives an
//! independent child key, so each dealer, instance and role draws from its own
//! stream and no stream is ever a function of a secret input value.
//!
//! The reproducibility seed is a test/operator knob over the KEY, never over the
//! values being shared: re-running with the printed seed replays the same sharing
//! randomness for whatever inputs the parties hold.
use crate::{custody::hash, reconstruction::Field};
use std::{fs::File, io::Read, io::Result};

const STREAM: &[u8] = b"DREGG.PRIVATE.ENTROPY.STREAM.V1";
const FORK: &[u8] = b"DREGG.PRIVATE.ENTROPY.FORK.V1";

pub struct Entropy {
    key: [u8; 32],
    counter: u64,
}
impl Entropy {
    /// A fresh key from the operating system.
    pub fn os() -> Result<Self> {
        let mut key = [0; 32];
        File::open("/dev/urandom")?.read_exact(&mut key)?;
        Ok(Self::from_seed(key))
    }
    /// A reproducible stream. The seed must itself be secret randomness when the
    /// run is meant to hide anything; a public seed makes every value public.
    pub fn from_seed(key: [u8; 32]) -> Self {
        Self { key, counter: 0 }
    }
    /// An independent child stream for `label`. Forking does not advance `self`.
    pub fn fork(&self, label: &[u8]) -> Self {
        let mut b = FORK.to_vec();
        b.extend(self.key);
        crate::codec::bytes(label, &mut b);
        Self::from_seed(hash(&b))
    }
    pub fn bytes32(&mut self) -> [u8; 32] {
        let mut b = STREAM.to_vec();
        b.extend(self.key);
        b.extend(self.counter.to_le_bytes());
        self.counter += 1;
        hash(&b)
    }
    /// A uniform GF(2^128) element.
    pub fn field(&mut self) -> Field {
        Field(u128::from_le_bytes(self.bytes32()[..16].try_into().unwrap()))
    }
}

/// Process-wide root for tests. `MINI_PRIVATE_TEST_ENTROPY=<64 hex>` replays a
/// run; otherwise the key comes from the OS and is printed once so a failing run
/// can be reproduced. Neither path derives anything from a party's input value.
#[cfg(test)]
pub(crate) fn test_root() -> Entropy {
    use std::sync::OnceLock;
    static ROOT: OnceLock<[u8; 32]> = OnceLock::new();
    let key = ROOT.get_or_init(|| {
        let key = match std::env::var("MINI_PRIVATE_TEST_ENTROPY") {
            Ok(hex) => {
                assert_eq!(hex.len(), 64, "MINI_PRIVATE_TEST_ENTROPY is 64 hex digits");
                let mut key = [0u8; 32];
                for (i, k) in key.iter_mut().enumerate() {
                    *k = u8::from_str_radix(&hex[2 * i..2 * i + 2], 16).unwrap();
                }
                key
            }
            Err(_) => Entropy::os().unwrap().key,
        };
        let hex = key.iter().map(|b| format!("{b:02x}")).collect::<String>();
        eprintln!("private-backend test entropy: MINI_PRIVATE_TEST_ENTROPY={hex}");
        key
    });
    Entropy::from_seed(*key)
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn entropy_forks_are_independent_and_seeded_streams_replay() {
        let root = Entropy::from_seed([5; 32]);
        let (mut a, mut b) = (root.fork(b"dealer/0"), root.fork(b"dealer/1"));
        let (x, y) = (a.bytes32(), b.bytes32());
        assert_ne!(x, y);
        assert_eq!(Entropy::from_seed([5; 32]).fork(b"dealer/0").bytes32(), x);
        assert_ne!(a.bytes32(), x, "a stream never repeats a block");
        let (mut s, mut t) = (Entropy::os().unwrap(), Entropy::os().unwrap());
        assert_ne!(s.bytes32(), t.bytes32());
    }
}
