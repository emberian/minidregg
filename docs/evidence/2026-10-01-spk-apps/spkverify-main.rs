// spkverify: reads the xz-DEcompressed body of an .spk on stdin (magic stripped),
// decodes the capnp Signature message (single segment), checks SHA-512 of the archive
// against the embedded hash, and verifies the Ed25519 signature with verify_strict.
use ed25519_dalek::{Signature, VerifyingKey};
use sha2::{Digest, Sha512};
use std::io::Read;
fn w(b: &[u8], i: usize) -> u64 { u64::from_le_bytes(b[i*8..i*8+8].try_into().unwrap()) }
fn data(seg: &[u8], ptr_word: usize) -> &[u8] {
    let p = w(seg, ptr_word);
    assert_eq!(p & 3, 1, "not a list pointer");
    let off = ((p as u32 as i32) >> 2) as isize;
    assert_eq!((p >> 32) & 7, 2, "not a byte list");
    let n = (p >> 35) as usize;
    let start = (ptr_word as isize + 1 + off) as usize * 8;
    &seg[start..start + n]
}
fn main() {
    let mut plain = Vec::new();
    std::io::stdin().read_to_end(&mut plain).unwrap();
    let nseg = u32::from_le_bytes(plain[0..4].try_into().unwrap()) as usize + 1;
    assert_eq!(nseg, 1, "multi-segment signature message");
    let seglen = u32::from_le_bytes(plain[4..8].try_into().unwrap()) as usize * 8;
    let seg = &plain[8..8 + seglen];
    let consumed = 8 + seglen;
    let root = w(seg, 0);
    assert_eq!(root & 3, 0);
    let off = ((root as u32 as i32) >> 2) as usize; // root struct at word 1+off
    let dwords = ((root >> 32) & 0xffff) as usize;
    let s = 1 + off;
    let pk = data(seg, s + dwords);
    let sigf = data(seg, s + dwords + 1);
    assert!(pk.len() == 32 && sigf.len() == 128, "bad key/sig lengths");
    let archive = &plain[consumed..];
    let h = Sha512::digest(archive);
    let ok_hash = &sigf[64..] == h.as_slice();
    let vk = VerifyingKey::from_bytes(pk.try_into().unwrap()).expect("key");
    let sig = Signature::from_bytes(sigf[..64].try_into().unwrap());
    let strict = vk.verify_strict(&sigf[64..], &sig).is_ok();
    println!("pubkey={} archiveBytes={} hashOk={} verifyStrict={}",
        pk.iter().map(|b| format!("{b:02x}")).collect::<String>(), archive.len(), ok_hash, strict);
    if !(ok_hash && strict) { std::process::exit(1) }
}
