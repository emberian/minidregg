//! mini-kernels: the Rust kernels the compiled Lean host calls through `@[extern]`.
//!
//! The Everest pattern (docs/HOT-PATH-2026-10-27.md §2d; SYNTHESIS §E.6): Lean keeps the
//! reference definition and every theorem is about it
//! (`Theory/Sp800185Cshake256Spec.lean` `cshake256Bytes`, `Compiler/Sp800185Kmac256.lean`
//! `kmac256Bytes`); this crate is the implementation that the compiled Host runs
//! (`Theory/Sp800185Cshake256Native.lean`, `@[extern "mini_cshake256_32"]` and
//! `@[extern "mini_kmac256_32"]`); the Lean-authored vectors (`testdata/lean-vectors.json`,
//! `tests/conformance.rs`) and the Lean conformance theorems, which evaluate the kernel at
//! every build once the dynlib is loaded, pin the equality.
//!
//! Hash kernels compute bytes; signature kernels return only a cryptographic verdict. Neither
//! selects authority, parses a semantic request, or makes an admission decision. The Lean object
//! marshalling lives in `shim/mini_kernels_lean.c`, compiled against the toolchain's `lean.h`;
//! this crate never sees a `lean_object`.

use ed25519_dalek::{Signature, VerifyingKey};
use sha2::{Digest, Sha512};
// Vendored under the adjacent QSAG MIT license. The source digest is pinned in conformance.rs.
#[allow(dead_code)]
#[path = "qsag/keccak.rs"]
mod qsag_keccak;
use qsag_keccak::Shake256Sponge;
pub use qsag_keccak::{cshake256_32, SHAKE256_RATE_BYTES as RATE_BYTES};
/// Every kernel here squeezes exactly 32 bytes (`outputBytes` in the Lean spec).
pub const OUTPUT_BYTES: usize = 32;

/// SP 800-185 §3.3 for named functions, including KMAC. The Lean cSHAKE root uses
/// QSAG's empty-function-name entry point directly.
fn named_sponge(name: &[u8], customization: &[u8]) -> Shake256Sponge {
    if name.is_empty() {
        return Shake256Sponge::new_cshake256(customization);
    }
    let mut sponge = Shake256Sponge::new_shake256();
    sponge.suffix = 0x04;
    let mut names = encode_string(name);
    names.extend_from_slice(&encode_string(customization));
    sponge.absorb(&bytepad(&names, RATE_BYTES));
    sponge
}

/// The size of a cSHAKE256 midstate's fixed part: the 25 Keccak lanes, little-endian, then the
/// padding suffix byte (`0x1f` for SHAKE256, `0x04` for cSHAKE256). The unabsorbed tail follows.
pub const MIDSTATE_FIXED_BYTES: usize = 201;
/// The longest midstate `cshake256_absorb` writes: the fixed part and fewer than one rate block.
pub const MIDSTATE_MAX_BYTES: usize = MIDSTATE_FIXED_BYTES + RATE_BYTES - 1;

/// cSHAKE256's absorbed prefix, as bytes: `cshake256AbsorbKernel` in
/// `Theory/Sp800185Cshake256Midstate.lean`. The framed input (the SP 800-185 customization block,
/// absent for an empty customization, then `prefix`) is absorbed block by block; the result is
/// the 25 lanes (200 bytes, little-endian), the padding suffix byte, and the unabsorbed tail
/// (fewer than 136 bytes). `cshake256_finish_32(&cshake256_absorb(c, p), s)` is
/// `cshake256_32(c, p ++ s)`.
pub fn cshake256_absorb(customization: &[u8], prefix: &[u8]) -> Vec<u8> {
    let mut sponge = Shake256Sponge::new_cshake256(customization);
    sponge.absorb(prefix);
    let mut out = Vec::with_capacity(MIDSTATE_FIXED_BYTES + sponge.buf_len);
    for lane in sponge.state {
        out.extend_from_slice(&lane.to_le_bytes());
    }
    out.push(sponge.suffix);
    out.extend_from_slice(&sponge.buf[..sponge.buf_len]);
    out
}

/// Finish a midstate with `suffix`: `cshake256FinishKernel` in
/// `Theory/Sp800185Cshake256Midstate.lean`. Total on every byte string, as the Lean body is: a
/// midstate shorter than 201 bytes reads as zero-filled, and a tail of any length is absorbed.
pub fn cshake256_finish_32(midstate: &[u8], suffix: &[u8]) -> [u8; OUTPUT_BYTES] {
    let mut fixed = [0u8; MIDSTATE_FIXED_BYTES];
    let take = midstate.len().min(MIDSTATE_FIXED_BYTES);
    fixed[..take].copy_from_slice(&midstate[..take]);
    let mut sponge = Shake256Sponge::new_shake256();
    for (i, lane) in sponge.state.iter_mut().enumerate() {
        let mut word = [0u8; 8];
        word.copy_from_slice(&fixed[8 * i..8 * i + 8]);
        *lane = u64::from_le_bytes(word);
    }
    sponge.suffix = fixed[200];
    sponge.absorb(midstate.get(MIDSTATE_FIXED_BYTES..).unwrap_or_default());
    sponge.absorb(suffix);
    let mut output = [0u8; OUTPUT_BYTES];
    sponge.squeeze(&mut output);
    output
}

/// SP 800-185 `left_encode`: the minimal big-endian bytes of `value`, preceded by their count.
fn left_encode(value: u128) -> Vec<u8> {
    let bytes = minimal_be(value);
    let mut out = Vec::with_capacity(bytes.len() + 1);
    out.push(bytes.len() as u8);
    out.extend_from_slice(&bytes);
    out
}

/// SP 800-185 `right_encode`: the minimal big-endian bytes of `value`, followed by their count.
fn right_encode(value: usize) -> Vec<u8> {
    let mut bytes = minimal_be(value as u128);
    bytes.push(bytes.len() as u8);
    bytes
}

/// The minimal big-endian bytes of `value`; `0` is the one byte `00` (`natBytesBE` in Lean).
fn minimal_be(value: u128) -> Vec<u8> {
    let mut bytes: Vec<u8> = value.to_be_bytes().to_vec();
    while bytes.len() > 1 && bytes[0] == 0 {
        bytes.remove(0);
    }
    bytes
}

/// SP 800-185 `encode_string`: `left_encode(bit length) || bytes` (`encodeString` in Lean).
fn encode_string(bytes: &[u8]) -> Vec<u8> {
    let mut out = left_encode((bytes.len() as u128) * 8);
    out.extend_from_slice(bytes);
    out
}

/// SP 800-185 `bytepad(X, w)`: `left_encode(w) || X`, zero-padded to a multiple of `w`
/// (`bytepad` in Lean).
fn bytepad(bytes: &[u8], width: usize) -> Vec<u8> {
    let mut out = left_encode(width as u128);
    out.extend_from_slice(bytes);
    while out.len() % width != 0 {
        out.push(0);
    }
    out
}

/// KMAC256 with a 32-byte tag: `kmac256Bytes` in `Compiler/Sp800185Kmac256.lean`,
/// `cSHAKE256(bytepad(encode_string(K), 136) || X || right_encode(256), 256, "KMAC", S)`.
pub fn kmac256_32(key: &[u8], customization: &[u8], input: &[u8]) -> [u8; OUTPUT_BYTES] {
    let mut sponge = named_sponge(b"KMAC", customization);
    sponge.absorb(&bytepad(&encode_string(key), RATE_BYTES));
    sponge.absorb(input);
    sponge.absorb(&right_encode(OUTPUT_BYTES * 8));
    let mut output = [0u8; OUTPUT_BYTES];
    sponge.squeeze(&mut output);
    output
}

/// Strict Ed25519 verification over an opaque frame. Malformed keys and wrong-length inputs are
/// input errors; a well-formed signature that does not verify is an ordinary negative verdict.
pub fn verify_ed25519(public_key: &[u8], frame: &[u8], signature: &[u8]) -> Result<bool, String> {
    let key_bytes: &[u8; 32] = public_key
        .try_into()
        .map_err(|_| "public key must be exactly 32 bytes".to_owned())?;
    let signature_bytes: &[u8; 64] = signature
        .try_into()
        .map_err(|_| "signature must be exactly 64 bytes".to_owned())?;
    let key = VerifyingKey::from_bytes(key_bytes)
        .map_err(|_| "public key point decoding failed".to_owned())?;
    Ok(key
        .verify_strict(frame, &Signature::from_bytes(signature_bytes))
        .is_ok())
}

/// An SSH `string`: a big-endian u32 length, then the bytes.
fn ssh_string(out: &mut Vec<u8>, bytes: &[u8]) -> Result<(), String> {
    let length =
        u32::try_from(bytes.len()).map_err(|_| "SSH string exceeds 2^32 bytes".to_owned())?;
    out.extend_from_slice(&length.to_be_bytes());
    out.extend_from_slice(bytes);
    Ok(())
}

/// OpenSSH PROTOCOL.sshsig: `"SSHSIG" || string namespace || string "" ||
/// string "sha512" || string SHA-512(message)`. Lean pins the non-hash framing in
/// `Kernel.PayEnrolMemo.sshsigSignedData`.
fn sshsig_signed_data(namespace: &[u8], message: &[u8]) -> Result<Vec<u8>, String> {
    if namespace.is_empty() {
        return Err("SSHSIG namespace must not be empty".to_owned());
    }
    let digest = Sha512::digest(message);
    let mut signed = b"SSHSIG".to_vec();
    ssh_string(&mut signed, namespace)?;
    ssh_string(&mut signed, b"")?;
    ssh_string(&mut signed, b"sha512")?;
    ssh_string(&mut signed, &digest)?;
    Ok(signed)
}

/// SSHSIG signed-data construction, including SHA-512, followed by strict Ed25519 verification.
pub fn verify_sshsig(
    public_key: &[u8],
    namespace: &[u8],
    message: &[u8],
    signature: &[u8],
) -> Result<bool, String> {
    let signed = sshsig_signed_data(namespace, message)?;
    verify_ed25519(public_key, &signed, signature)
}

/// A byte slice from a (pointer, length) pair the C shim hands over; a null pointer with
/// length zero is the empty slice (Lean's empty `ByteArray` may hand one over).
///
/// # Safety
/// `ptr` must be valid for `len` bytes for the duration of the call, or `len` must be 0.
unsafe fn slice<'a>(ptr: *const u8, len: usize) -> &'a [u8] {
    if len == 0 {
        &[]
    } else {
        std::slice::from_raw_parts(ptr, len)
    }
}

/// C ABI: `cshake256_32` into the caller's 32-byte buffer.
///
/// # Safety
/// `customization`/`input` must be valid for their lengths (or the length 0); `output` must be
/// valid for 32 writable bytes.
#[no_mangle]
pub unsafe extern "C" fn mini_kernels_cshake256_32(
    customization: *const u8,
    customization_len: usize,
    input: *const u8,
    input_len: usize,
    output: *mut u8,
) {
    let digest = cshake256_32(slice(customization, customization_len), slice(input, input_len));
    std::ptr::copy_nonoverlapping(digest.as_ptr(), output, OUTPUT_BYTES);
}

/// C ABI: `cshake256_absorb` into the caller's buffer of `MIDSTATE_MAX_BYTES`; returns the
/// number of bytes written.
///
/// # Safety
/// `customization`/`prefix` must be valid for their lengths (or the length 0); `output` must be
/// valid for `MIDSTATE_MAX_BYTES` writable bytes.
#[no_mangle]
pub unsafe extern "C" fn mini_kernels_cshake256_absorb(
    customization: *const u8,
    customization_len: usize,
    prefix: *const u8,
    prefix_len: usize,
    output: *mut u8,
) -> usize {
    let midstate = cshake256_absorb(slice(customization, customization_len), slice(prefix, prefix_len));
    debug_assert!(midstate.len() <= MIDSTATE_MAX_BYTES);
    std::ptr::copy_nonoverlapping(midstate.as_ptr(), output, midstate.len());
    midstate.len()
}

/// C ABI: `cshake256_finish_32` into the caller's 32-byte buffer.
///
/// # Safety
/// `midstate`/`suffix` must be valid for their lengths (or the length 0); `output` must be valid
/// for 32 writable bytes.
#[no_mangle]
pub unsafe extern "C" fn mini_kernels_cshake256_finish_32(
    midstate: *const u8,
    midstate_len: usize,
    suffix: *const u8,
    suffix_len: usize,
    output: *mut u8,
) {
    let digest = cshake256_finish_32(slice(midstate, midstate_len), slice(suffix, suffix_len));
    std::ptr::copy_nonoverlapping(digest.as_ptr(), output, OUTPUT_BYTES);
}

/// C ABI: `kmac256_32` into the caller's 32-byte buffer.
///
/// # Safety
/// As `mini_kernels_cshake256_32`, with `key` valid for `key_len` bytes.
#[no_mangle]
pub unsafe extern "C" fn mini_kernels_kmac256_32(
    key: *const u8,
    key_len: usize,
    customization: *const u8,
    customization_len: usize,
    input: *const u8,
    input_len: usize,
    output: *mut u8,
) {
    let tag = kmac256_32(
        slice(key, key_len),
        slice(customization, customization_len),
        slice(input, input_len),
    );
    std::ptr::copy_nonoverlapping(tag.as_ptr(), output, OUTPUT_BYTES);
}

/// C ABI verdicts shared with `Compiler.CredentialSignatureIO`: verified, invalid, input error.
const VERDICT_VERIFIED: u8 = 0;
const VERDICT_INVALID: u8 = 1;
const VERDICT_INPUT_ERROR: u8 = 2;

fn verification_verdict(result: Result<bool, String>) -> u8 {
    match result {
        Ok(true) => VERDICT_VERIFIED,
        Ok(false) => VERDICT_INVALID,
        Err(_) => VERDICT_INPUT_ERROR,
    }
}

/// C ABI: strict Ed25519 verification over borrowed byte slices.
///
/// # Safety
/// Every pointer must be valid for its length (or the length must be 0).
#[no_mangle]
pub unsafe extern "C" fn mini_kernels_ed25519_verify(
    public_key: *const u8,
    public_key_len: usize,
    frame: *const u8,
    frame_len: usize,
    signature: *const u8,
    signature_len: usize,
) -> u8 {
    verification_verdict(verify_ed25519(
        slice(public_key, public_key_len),
        slice(frame, frame_len),
        slice(signature, signature_len),
    ))
}

/// C ABI: SSHSIG signed-data construction and strict Ed25519 verification.
///
/// # Safety
/// Every pointer must be valid for its length (or the length must be 0).
#[no_mangle]
pub unsafe extern "C" fn mini_kernels_sshsig_verify(
    public_key: *const u8,
    public_key_len: usize,
    namespace: *const u8,
    namespace_len: usize,
    message: *const u8,
    message_len: usize,
    signature: *const u8,
    signature_len: usize,
) -> u8 {
    verification_verdict(verify_sshsig(
        slice(public_key, public_key_len),
        slice(namespace, namespace_len),
        slice(message, message_len),
        slice(signature, signature_len),
    ))
}

#[cfg(test)]
mod framing {
    use super::*;

    #[test]
    fn named_sponge_matches_rustcrypto_at_rate_boundaries() {
        use sha3::digest::{ExtendableOutput, Update, XofReader};
        for name in [&b""[..], b"KMAC"] {
            for custom in [&b""[..], b"Email Signature", &[42; 129], &[43; 130]] {
                for len in [0usize, 1, 134, 135, 136, 137, 271, 272, 273] {
                    let input: Vec<u8> = (0..len).map(|i| (7 * i + 3) as u8).collect();
                    let mut oracle = sha3::CShake256::from_core(
                        sha3::CShake256Core::new_with_function_name(name, custom),
                    );
                    oracle.update(&input);
                    // Two complete squeeze blocks and the first byte of the third.
                    let mut expected = [0; 2 * RATE_BYTES + 1];
                    oracle.finalize_xof().read(&mut expected);
                    let mut sponge = named_sponge(name, custom);
                    sponge.absorb(&input);

                    let mut wrong_domain = sponge.clone();
                    wrong_domain.suffix ^= 1;
                    let mut output = [0; 2 * RATE_BYTES + 1];
                    wrong_domain.squeeze(&mut output);
                    assert_ne!(output, expected);

                    // Cancel the final block's 0x80 XOR at byte 135. At len % 136
                    // == 135 this bit shares a byte with the domain suffix.
                    let mut missing_pad_bit = sponge.clone();
                    missing_pad_bit.state[RATE_BYTES / 8 - 1] ^= 1u64 << 63;
                    missing_pad_bit.squeeze(&mut output);
                    assert_ne!(output, expected);
                    sponge.squeeze(&mut output[..RATE_BYTES]);
                    sponge.squeeze(&mut output[RATE_BYTES..]);
                    assert_eq!(output, expected, "len={len}, N={name:?}, |S|={}", custom.len());
                    if name.is_empty() {
                        assert_eq!(cshake256_32(custom, &input), expected[..OUTPUT_BYTES]);
                    }
                }
            }
        }
    }

    /// NIST cSHAKE samples 3 and 4 request 512 output bits with S="Email Signature".
    /// https://csrc.nist.gov/CSRC/media/Projects/Cryptographic-Standards-and-Guidelines/documents/examples/cSHAKE_samples.pdf
    #[test]
    fn nist_cshake256_full_outputs() {
        for (len, expected) in [
            (4, concat!("d008828e2b80ac9d2218ffee1d070c48b8e4c87bff32c9699d5b6896eee0edd1",
                        "64020e2be0560858d9c00c037e34a96937c561a74c412bb4c746469527281c8c")),
            (200, concat!("07dc27b11e51fbac75bc7b3c1d983e8b4b85fb1defaf218912ac864302730917",
                          "27f42b17ed1df63e8ec118f04b23633c1dfb1574c8fb55cb45da8e25afb092bb")),
        ] {
            let input: Vec<u8> = (0..len).collect();
            let mut sponge = named_sponge(b"", b"Email Signature");
            sponge.absorb(&input);
            let mut output = [0; 64];
            sponge.squeeze(&mut output);
            let actual: String = output.iter().map(|byte| format!("{byte:02x}")).collect();
            assert_eq!(actual, expected);
            assert_eq!(cshake256_32(b"Email Signature", &input), output[..OUTPUT_BYTES]);
        }
    }

    /// The Lean `@[simp]` facts in `Compiler/Sp800185Cshake256.lean`: `leftEncode 0 = [1, 0]`,
    /// `leftEncode 65536 = [3, 1, 0, 0]`, `encodeString [] = [1, 0]`, `bytepad [] 4 = [1, 4, 0, 0]`.
    #[test]
    fn framing_matches_the_lean_simp_facts() {
        assert_eq!(left_encode(0), vec![1, 0]);
        assert_eq!(left_encode(65536), vec![3, 1, 0, 0]);
        assert_eq!(encode_string(&[]), vec![1, 0]);
        assert_eq!(bytepad(&[], 4), vec![1, 4, 0, 0]);
        assert_eq!(right_encode(256), vec![1, 0, 2]);
    }
}
