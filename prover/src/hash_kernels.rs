//! Raw cSHAKE256 native compute.
//!
//! The caller supplies the complete customization string, input bytes, and
//! output width. This module owns no framing, tree layout, authentication path,
//! semantic domain, expected-root comparison, or verifier verdict.

use sha3::{
    digest::{ExtendableOutput, Update, XofReader},
    CShake256, CShake256Core,
};

/// Read exactly `output_len` bytes from cSHAKE256.
pub fn cshake256_xof(customization: &[u8], input: &[u8], output_len: usize) -> Vec<u8> {
    let core = CShake256Core::new(customization);
    let mut hasher = CShake256::from_core(core);
    hasher.update(input);
    let mut reader = hasher.finalize_xof();
    let mut output = vec![0u8; output_len];
    reader.read(&mut output);
    output
}
