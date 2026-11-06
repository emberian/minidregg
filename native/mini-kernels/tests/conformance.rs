//! Conformance of the kernels against the Lean reference, on the Lean-authored vectors
//! (`testdata/lean-vectors.json`: the tree's conformance constants plus the seeded rows
//! `scripts/kernel-vectors.lean` writes from the Lean fast path) and on the C ABI the Lean shim
//! calls. Run filtered: `cargo test --release --locked -p mini-kernels --test conformance`.

use mini_kernels::{
    cshake256_32, cshake256_absorb, cshake256_finish_32, kmac256_32, mini_kernels_cshake256_32,
    mini_kernels_cshake256_absorb, mini_kernels_cshake256_finish_32, mini_kernels_kmac256_32,
    MIDSTATE_MAX_BYTES,
};
use serde::Deserialize;

#[derive(Deserialize)]
struct Vectors {
    cshake256: Vec<CshakeRow>,
    kmac256: Vec<KmacRow>,
    cshake256_midstate: Vec<MidstateRow>,
}

#[derive(Deserialize)]
struct MidstateRow {
    name: String,
    customization: String,
    prefix: String,
    suffix: String,
    midstate: String,
    output: String,
}

#[derive(Deserialize)]
struct CshakeRow {
    name: String,
    customization: String,
    input: String,
    output: String,
}

#[derive(Deserialize)]
struct KmacRow {
    name: String,
    key: String,
    customization: String,
    input: String,
    output: String,
}

fn hex(text: &str) -> Vec<u8> {
    assert!(text.len() % 2 == 0, "odd hex length in {text}");
    (0..text.len() / 2)
        .map(|i| u8::from_str_radix(&text[2 * i..2 * i + 2], 16).expect("hex"))
        .collect()
}

fn vectors() -> Vectors {
    let path = concat!(env!("CARGO_MANIFEST_DIR"), "/testdata/lean-vectors.json");
    let text = std::fs::read_to_string(path).expect("testdata/lean-vectors.json");
    serde_json::from_str(&text).expect("lean-vectors.json parses")
}

#[test]
fn cshake256_matches_every_lean_vector() {
    let vectors = vectors();
    assert!(vectors.cshake256.len() >= 2, "the two fixed Lean cSHAKE rows must be present");
    for row in &vectors.cshake256 {
        let got = cshake256_32(&hex(&row.customization), &hex(&row.input));
        assert_eq!(got.to_vec(), hex(&row.output), "cshake256 vector {}", row.name);
    }
}

#[test]
fn kmac256_matches_every_lean_vector() {
    let vectors = vectors();
    assert!(vectors.kmac256.len() >= 2, "the two fixed Lean KMAC rows must be present");
    for row in &vectors.kmac256 {
        let got = kmac256_32(&hex(&row.key), &hex(&row.customization), &hex(&row.input));
        assert_eq!(got.to_vec(), hex(&row.output), "kmac256 vector {}", row.name);
    }
}

/// The C ABI the Lean shim calls computes the same bytes as the Rust functions, including on
/// empty inputs handed over as null pointers with length zero (an empty Lean ByteArray).
#[test]
fn c_abi_is_the_rust_function_including_empty_inputs() {
    let vectors = vectors();
    for row in &vectors.cshake256 {
        let customization = hex(&row.customization);
        let input = hex(&row.input);
        let mut out = [0u8; 32];
        let cp = if customization.is_empty() { std::ptr::null() } else { customization.as_ptr() };
        let ip = if input.is_empty() { std::ptr::null() } else { input.as_ptr() };
        unsafe { mini_kernels_cshake256_32(cp, customization.len(), ip, input.len(), out.as_mut_ptr()) };
        assert_eq!(out.to_vec(), hex(&row.output), "C ABI cshake256 {}", row.name);
    }
    for row in &vectors.kmac256 {
        let key = hex(&row.key);
        let customization = hex(&row.customization);
        let input = hex(&row.input);
        let mut out = [0u8; 32];
        unsafe {
            mini_kernels_kmac256_32(
                key.as_ptr(), key.len(),
                customization.as_ptr(), customization.len(),
                input.as_ptr(), input.len(),
                out.as_mut_ptr(),
            )
        };
        assert_eq!(out.to_vec(), hex(&row.output), "C ABI kmac256 {}", row.name);
    }
}

/// Rate boundaries are where a sponge implementation goes wrong: inputs of 0, 1, 135, 136, 137,
/// 271, 272, 273 bytes must all agree between the one-shot kernel and a byte-at-a-time absorb
/// through the same primitive. This is a self-consistency row; the Lean rows above are the
/// reference.
#[test]
fn rate_boundaries_are_consistent_with_incremental_absorption() {
    use sha3::digest::{ExtendableOutput, Update, XofReader};
    for len in [0usize, 1, 135, 136, 137, 271, 272, 273, 4096] {
        let input: Vec<u8> = (0..len).map(|i| (i * 7 + 3) as u8).collect();
        let customization = b"DREGG.CELL.LIFECYCLE/v1";
        let one_shot = cshake256_32(customization, &input);
        let mut hasher = sha3::CShake256::from_core(sha3::CShake256Core::new(customization));
        for byte in &input {
            hasher.update(std::slice::from_ref(byte));
        }
        let mut incremental = [0u8; 32];
        hasher.finalize_xof().read(&mut incremental);
        assert_eq!(one_shot, incremental, "rate boundary at {len} bytes");
    }
}

/// The absorbed-prefix kernels against the Lean bodies (`absorbFast`, `finishFast` in
/// `Theory/Sp800185Cshake256Midstate.lean`): the midstate bytes themselves, not only the final
/// digest, are Lean's; and finishing is the one-shot hash of `prefix ++ suffix`
/// (`cshake256_cached`), through the Rust functions and through the C ABI.
#[test]
fn midstate_matches_every_lean_vector() {
    let vectors = vectors();
    assert!(vectors.cshake256_midstate.len() >= 20, "the seeded Lean midstate rows must be present");
    for row in &vectors.cshake256_midstate {
        let customization = hex(&row.customization);
        let prefix = hex(&row.prefix);
        let suffix = hex(&row.suffix);
        let midstate = cshake256_absorb(&customization, &prefix);
        assert_eq!(midstate, hex(&row.midstate), "midstate {}", row.name);
        assert_eq!(cshake256_finish_32(&midstate, &suffix).to_vec(), hex(&row.output), "finish {}", row.name);
        let mut whole = prefix.clone();
        whole.extend_from_slice(&suffix);
        assert_eq!(cshake256_32(&customization, &whole).to_vec(), hex(&row.output), "one-shot {}", row.name);
        let mut buffer = [0u8; MIDSTATE_MAX_BYTES];
        let cp = if customization.is_empty() { std::ptr::null() } else { customization.as_ptr() };
        let pp = if prefix.is_empty() { std::ptr::null() } else { prefix.as_ptr() };
        let written = unsafe { mini_kernels_cshake256_absorb(cp, customization.len(), pp, prefix.len(), buffer.as_mut_ptr()) };
        assert_eq!(buffer[..written].to_vec(), midstate, "C ABI absorb {}", row.name);
        let mut out = [0u8; 32];
        let sp = if suffix.is_empty() { std::ptr::null() } else { suffix.as_ptr() };
        unsafe { mini_kernels_cshake256_finish_32(midstate.as_ptr(), midstate.len(), sp, suffix.len(), out.as_mut_ptr()) };
        assert_eq!(out.to_vec(), hex(&row.output), "C ABI finish {}", row.name);
    }
}

/// Teeth: the finish reads every part of the midstate. Flipping one lane byte, the delimiter, or
/// dropping the carried tail each changes the digest.
#[test]
fn midstate_finish_reads_lanes_delimiter_and_tail() {
    let customization = b"DREGG.CELL.LIFECYCLE/v1";
    let prefix: Vec<u8> = (0..300usize).map(|i| (i * 13 + 5) as u8).collect();
    let midstate = cshake256_absorb(customization, &prefix);
    assert!(midstate.len() > 201, "this prefix leaves a carried tail");
    let honest = cshake256_finish_32(&midstate, b"q");
    let mut lane = midstate.clone();
    lane[17] ^= 1;
    assert_ne!(cshake256_finish_32(&lane, b"q"), honest);
    let mut delimiter = midstate.clone();
    delimiter[200] ^= 0x1b;
    assert_ne!(cshake256_finish_32(&delimiter, b"q"), honest);
    assert_ne!(cshake256_finish_32(&midstate[..201], b"q"), honest);
}

/// Self-consistency at the rate boundaries: absorbing a prefix and finishing with a suffix is the
/// one-shot hash of their concatenation, for empty and non-empty customizations (the latter
/// including one longer than a rate block). The Lean rows above are the reference.
#[test]
fn midstate_split_is_the_one_shot_hash_at_rate_boundaries() {
    let long: Vec<u8> = (0..200usize).map(|i| (i * 31 + 7) as u8).collect();
    let customizations: [&[u8]; 3] = [b"", b"DREGG.CELL.LIFECYCLE/v1", &long];
    for customization in customizations {
        for prefix_len in [0usize, 1, 135, 136, 137, 271, 272, 273, 1000] {
            for suffix_len in [0usize, 1, 134, 135, 136, 137, 300] {
                let input: Vec<u8> = (0..prefix_len + suffix_len).map(|i| (i * 7 + 3) as u8).collect();
                let midstate = cshake256_absorb(customization, &input[..prefix_len]);
                assert_eq!(
                    cshake256_finish_32(&midstate, &input[prefix_len..]),
                    cshake256_32(customization, &input),
                    "split at {prefix_len}+{suffix_len}, customization {} bytes",
                    customization.len()
                );
            }
        }
    }
}
