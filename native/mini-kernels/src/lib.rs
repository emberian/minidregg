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
use sha3::{
    digest::{ExtendableOutput, Update, XofReader},
    CShake256, CShake256Core,
};

/// The Keccak-f[1600] rate of cSHAKE256/KMAC256 in bytes (`rateBytes` in the Lean spec).
pub const RATE_BYTES: usize = 136;
/// Every kernel here squeezes exactly 32 bytes (`outputBytes` in the Lean spec).
pub const OUTPUT_BYTES: usize = 32;

/// cSHAKE256 with an EMPTY function name and a 32-byte output: `cshake256Bytes` in
/// `Theory/Sp800185Cshake256Spec.lean`. An empty customization is SHAKE256 (the `0x1f`
/// suffix), as in the spec's `cshake256Bytes` and in SP 800-185 §3.3.
pub fn cshake256_32(customization: &[u8], input: &[u8]) -> [u8; OUTPUT_BYTES] {
    let core = CShake256Core::new(customization);
    let mut hasher = CShake256::from_core(core);
    hasher.update(input);
    let mut reader = hasher.finalize_xof();
    let mut output = [0u8; OUTPUT_BYTES];
    reader.read(&mut output);
    output
}

/// The size of a cSHAKE256 midstate's fixed part: the 25 Keccak lanes, little-endian, then the
/// padding suffix byte (`0x1f` for SHAKE256, `0x04` for cSHAKE256). The unabsorbed tail follows.
pub const MIDSTATE_FIXED_BYTES: usize = 201;
/// The longest midstate `cshake256_absorb` writes: the fixed part and fewer than one rate block.
pub const MIDSTATE_MAX_BYTES: usize = MIDSTATE_FIXED_BYTES + RATE_BYTES - 1;

fn xor_block(state: &mut [u64; 25], block: &[u8]) {
    for (lane, chunk) in state.iter_mut().zip(block.chunks(8)).take(RATE_BYTES / 8) {
        let mut word = [0u8; 8];
        word[..chunk.len()].copy_from_slice(chunk);
        *lane ^= u64::from_le_bytes(word);
    }
}

/// Absorb every full rate block of `bytes` into `state`; return the unabsorbed tail.
fn absorb_blocks<'a>(state: &mut [u64; 25], bytes: &'a [u8]) -> &'a [u8] {
    let full = bytes.len() / RATE_BYTES;
    for block in bytes.chunks_exact(RATE_BYTES).take(full) {
        xor_block(state, block);
        keccak::f1600(state);
    }
    &bytes[full * RATE_BYTES..]
}

/// cSHAKE256's absorbed prefix, as bytes: `cshake256AbsorbKernel` in
/// `Theory/Sp800185Cshake256Midstate.lean`. The framed input (the SP 800-185 customization block,
/// absent for an empty customization, then `prefix`) is absorbed block by block; the result is
/// the 25 lanes (200 bytes, little-endian), the padding suffix byte, and the unabsorbed tail
/// (fewer than 136 bytes). `cshake256_finish_32(&cshake256_absorb(c, p), s)` is
/// `cshake256_32(c, p ++ s)`.
pub fn cshake256_absorb(customization: &[u8], prefix: &[u8]) -> Vec<u8> {
    let mut framed = if customization.is_empty() {
        Vec::with_capacity(prefix.len())
    } else {
        let mut names = encode_string(&[]);
        names.extend_from_slice(&encode_string(customization));
        bytepad(&names, RATE_BYTES)
    };
    framed.extend_from_slice(prefix);
    let suffix: u8 = if customization.is_empty() { 0x1f } else { 0x04 };
    let mut state = [0u64; 25];
    let tail = absorb_blocks(&mut state, &framed);
    let mut out = Vec::with_capacity(MIDSTATE_FIXED_BYTES + tail.len());
    for lane in state {
        out.extend_from_slice(&lane.to_le_bytes());
    }
    out.push(suffix);
    out.extend_from_slice(tail);
    out
}

/// Finish a midstate with `suffix`: `cshake256FinishKernel` in
/// `Theory/Sp800185Cshake256Midstate.lean`. Total on every byte string, as the Lean body is: a
/// midstate shorter than 201 bytes reads as zero-filled, and a tail of any length is absorbed.
pub fn cshake256_finish_32(midstate: &[u8], suffix: &[u8]) -> [u8; OUTPUT_BYTES] {
    let mut fixed = [0u8; MIDSTATE_FIXED_BYTES];
    let take = midstate.len().min(MIDSTATE_FIXED_BYTES);
    fixed[..take].copy_from_slice(&midstate[..take]);
    let mut state = [0u64; 25];
    for (i, lane) in state.iter_mut().enumerate() {
        let mut word = [0u8; 8];
        word.copy_from_slice(&fixed[8 * i..8 * i + 8]);
        *lane = u64::from_le_bytes(word);
    }
    let delimiter = fixed[200];
    let pending = if midstate.len() > MIDSTATE_FIXED_BYTES { &midstate[MIDSTATE_FIXED_BYTES..] } else { &[] };
    let mut tail = Vec::with_capacity(pending.len() + suffix.len() + RATE_BYTES);
    tail.extend_from_slice(pending);
    tail.extend_from_slice(suffix);
    // `padForRate`: the delimiter, zeros, and a final 0x80, merged when one byte is left.
    let count = RATE_BYTES - tail.len() % RATE_BYTES;
    if count == 1 {
        tail.push(delimiter ^ 0x80);
    } else {
        tail.push(delimiter);
        tail.resize(tail.len() + count - 2, 0);
        tail.push(0x80);
    }
    let rest = absorb_blocks(&mut state, &tail);
    debug_assert!(rest.is_empty());
    let mut output = [0u8; OUTPUT_BYTES];
    for (k, byte) in output.iter_mut().enumerate() {
        *byte = (state[k / 8] >> (8 * (k % 8))) as u8;
    }
    output
}

/// SP 800-185 `left_encode`: the minimal big-endian bytes of `value`, preceded by their count.
fn left_encode(value: usize) -> Vec<u8> {
    let bytes = minimal_be(value);
    let mut out = Vec::with_capacity(bytes.len() + 1);
    out.push(bytes.len() as u8);
    out.extend_from_slice(&bytes);
    out
}

/// SP 800-185 `right_encode`: the minimal big-endian bytes of `value`, followed by their count.
fn right_encode(value: usize) -> Vec<u8> {
    let mut bytes = minimal_be(value);
    bytes.push(bytes.len() as u8);
    bytes
}

/// The minimal big-endian bytes of `value`; `0` is the one byte `00` (`natBytesBE` in Lean).
fn minimal_be(value: usize) -> Vec<u8> {
    let mut bytes: Vec<u8> = value.to_be_bytes().to_vec();
    while bytes.len() > 1 && bytes[0] == 0 {
        bytes.remove(0);
    }
    bytes
}

/// SP 800-185 `encode_string`: `left_encode(bit length) || bytes` (`encodeString` in Lean).
fn encode_string(bytes: &[u8]) -> Vec<u8> {
    let mut out = left_encode(bytes.len() * 8);
    out.extend_from_slice(bytes);
    out
}

/// SP 800-185 `bytepad(X, w)`: `left_encode(w) || X`, zero-padded to a multiple of `w`
/// (`bytepad` in Lean).
fn bytepad(bytes: &[u8], width: usize) -> Vec<u8> {
    let mut out = left_encode(width);
    out.extend_from_slice(bytes);
    while out.len() % width != 0 {
        out.push(0);
    }
    out
}

/// KMAC256 with a 32-byte tag: `kmac256Bytes` in `Compiler/Sp800185Kmac256.lean`,
/// `cSHAKE256(bytepad(encode_string(K), 136) || X || right_encode(256), 256, "KMAC", S)`.
pub fn kmac256_32(key: &[u8], customization: &[u8], input: &[u8]) -> [u8; OUTPUT_BYTES] {
    let core = CShake256Core::new_with_function_name(b"KMAC", customization);
    let mut hasher = CShake256::from_core(core);
    hasher.update(&bytepad(&encode_string(key), RATE_BYTES));
    hasher.update(input);
    hasher.update(&right_encode(OUTPUT_BYTES * 8));
    let mut reader = hasher.finalize_xof();
    let mut output = [0u8; OUTPUT_BYTES];
    reader.read(&mut output);
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
