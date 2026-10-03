//! Clone-safe randomness for the pinned P3 hiding commitment APIs.
//!
//! Clones share a single advancing cryptographic stream. This satisfies P3's
//! Clone requirement without cloning a PRNG state into overlapping streams.
//! This adapter does not establish the PCS's masking or soundness bounds.
use core::convert::Infallible;
use rand::{SeedableRng, TryCryptoRng, TryRng, rngs::StdRng};
use std::sync::{Arc, Mutex, MutexGuard};

#[derive(Clone)]
pub struct ProofRng {
    state: Arc<Mutex<StdRng>>,
    process: u32,
}

impl ProofRng {
    /// Obtain a fresh 256-bit seed. Entropy failure returns an error, never a
    /// deterministic fallback. Construct independently for each proof invocation.
    pub fn from_os() -> Result<Self, getrandom::Error> {
        let mut seed = [0u8; 32];
        getrandom::fill(&mut seed)?;
        Ok(Self::from_private_seed(seed))
    }

    fn from_private_seed(seed: [u8; 32]) -> Self {
        Self { state: Arc::new(Mutex::new(StdRng::from_seed(seed))), process: std::process::id() }
    }

    fn state(&self) -> MutexGuard<'_, StdRng> {
        // Fork duplicates even shared process memory. Refuse inherited configs;
        // the child must construct a fresh configuration before proving.
        assert_eq!(self.process, std::process::id(), "proof RNG inherited across fork");
        self.state.lock().expect("proof RNG state poisoned")
    }
}

impl TryRng for ProofRng {
    type Error = Infallible;
    fn try_next_u32(&mut self) -> Result<u32, Infallible> { self.state().try_next_u32() }
    fn try_next_u64(&mut self) -> Result<u64, Infallible> { self.state().try_next_u64() }
    fn try_fill_bytes(&mut self, dst: &mut [u8]) -> Result<(), Infallible> {
        self.state().try_fill_bytes(dst)
    }
}
impl TryCryptoRng for ProofRng {}

#[cfg(test)]
mod tests {
    use super::*;
    use rand::{CryptoRng, Rng};

    fn p3_required_bounds<T: Rng + CryptoRng + Clone + Send + Sync>() {}

    #[test]
    fn cloned_handles_consume_successive_stream_segments() {
        p3_required_bounds::<ProofRng>();
        let seed = [73u8; 32];
        let mut expected = StdRng::from_seed(seed);
        let mut first = ProofRng::from_private_seed(seed);
        let mut second = first.clone();
        let mut third = second.clone();
        assert!(Arc::ptr_eq(&first.state, &second.state));
        for _ in 0..257 {
            assert_eq!(first.next_u32(), expected.next_u32());
            assert_eq!(second.next_u64(), expected.next_u64());
            let mut actual = [0u8; 91];
            let mut wanted = [0u8; 91];
            third.fill_bytes(&mut actual);
            expected.fill_bytes(&mut wanted);
            assert_eq!(actual, wanted);
        }
    }

    #[test]
    fn thread_clone_continues_parent_stream() {
        let seed = [19u8; 32];
        let mut expected = StdRng::from_seed(seed);
        let mut parent = ProofRng::from_private_seed(seed);
        let mut child = parent.clone();
        let received = std::thread::spawn(move || child.next_u64()).join().unwrap();
        assert_eq!(received, expected.next_u64());
        assert_eq!(parent.next_u64(), expected.next_u64());
    }

    #[test]
    #[should_panic(expected = "proof RNG inherited across fork")]
    fn inherited_process_identity_refuses_before_rng_lock() {
        let mut inherited = ProofRng::from_private_seed([1u8; 32]);
        inherited.process = inherited.process.wrapping_add(1);
        let _ = inherited.next_u64();
    }
}
