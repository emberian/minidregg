//! `verify-sshsig`: OpenSSH SSHSIG (PROTOCOL.sshsig) over an ssh-ed25519 key.
//!
//! The vector is a real run on persvati (2026-09-30): `ssh-keygen -t ed25519`,
//! then `ssh-keygen -Y sign -n dregg-enrol@v1 -f key message.bin` over
//! `mint(32) || enrolAddress(32) || miniKey(32)` (PAY §11.3), checked with
//! `ssh-keygen -Y check-novalidate`. Only the public key, the message and the
//! armoured signature are committed; the private key was deleted.
use ed25519_dalek::{Signature, Verifier, VerifyingKey};
use sha2::{Digest, Sha512};
use std::fs;
use std::path::PathBuf;
use std::process::{Command, Output};
use std::sync::atomic::{AtomicU64, Ordering};

const BINARY: &str = env!("CARGO_BIN_EXE_minidregg-credential-signature-verifier");
static NEXT_FIXTURE: AtomicU64 = AtomicU64::new(0);

/// `ssh-ed25519 AAAAC3NzaC1lZDI1NTE5AAAAIG07ssw/nVQyEp4fbo6x0DefttH5CdsmuUI28/nc/UkK p3b1-vector`
const SSH_BLOB: &str = "0000000b7373682d65643235353139000000206d3bb2cc3f9d5432129e1f6e8eb1d0379fb6d1f909db26b94236f3f9dcfd490a";
const MINT: &str = "8525966c00f39ff54ef5e537a4736af436494d1f1681c659bd98e37ac28beff1";
const ENROL_ADDRESS: &str = "16946aa663362d557dd21ee08e8da60c2ea8a73467713c7c5205991e36634af5";
const MINI_KEY: &str = "197f6b23e16c8532c6abc838facd5ea789be0c76b2920334039bfa8b3d368d61";
/// The base64-decoded body of `message.bin.sig` (the armoured SSHSIG).
const SSHSIG_ARMOURED_BODY: &str = "53534853494700000001000000330000000b7373682d65643235353139000000206d3bb2cc3f9d5432129e1f6e8eb1d0379fb6d1f909db26b94236f3f9dcfd490a0000000e64726567672d656e726f6c4076310000000000000006736861353132000000530000000b7373682d6564323535313900000040e3024a122f7f20335c168b22d428617cbcfb4dc6d0b68f26dae8e2c2038641fd40d672e739b8a1d1a681f6d8488f46046985570f0ee30db01ae361309ff21f09";
/// `Kernel.PayEnrolMemo.sshsig_signed_data_fixture` pins the same bytes in Lean.
const SIGNED_DATA: &str = "5353485349470000000e64726567672d656e726f6c4076310000000000000006736861353132000000401830df88475cac61066ee69f5017b289c289bde449ad702c566dc5a6d1983da97a04b71874d48a7f0d79edef1d352333d64253f6585c5d5a0a9aac132bc75902";
const NAMESPACE: &[u8] = b"dregg-enrol@v1";
/// The memo's `mini-sig` (PyNaCl, seed `[42; 32]`) over `Kernel.PayEnrolMemo.miniFrame`.
const MINI_SIG: &str = "1a89a4544250df3be16bd701357d114ccb00dabd79da77f35c8a394875cf78d8ef66b47d8a3cde4c21efd6c9aefd2fe7430adc047d67746498280c274adae202";

fn hex(text: &str) -> Vec<u8> {
    assert!(text.len() % 2 == 0);
    (0..text.len())
        .step_by(2)
        .map(|i| u8::from_str_radix(&text[i..i + 2], 16).unwrap())
        .collect()
}

fn message() -> Vec<u8> {
    [hex(MINT), hex(ENROL_ADDRESS), hex(MINI_KEY)].concat()
}

/// Reads one SSH `string` from `bytes` at `*at`.
fn take_string<'a>(bytes: &'a [u8], at: &mut usize) -> &'a [u8] {
    let length = u32::from_be_bytes(bytes[*at..*at + 4].try_into().unwrap()) as usize;
    let value = &bytes[*at + 4..*at + 4 + length];
    *at += 4 + length;
    value
}

/// The armoured SSHSIG, parsed per PROTOCOL.sshsig: returns (public key blob,
/// namespace, hash algorithm, raw 64-byte Ed25519 signature).
fn parse_armoured() -> (Vec<u8>, Vec<u8>, Vec<u8>, Vec<u8>) {
    let body = hex(SSHSIG_ARMOURED_BODY);
    assert_eq!(&body[..6], b"SSHSIG");
    assert_eq!(u32::from_be_bytes(body[6..10].try_into().unwrap()), 1);
    let mut at = 10;
    let public_key = take_string(&body, &mut at).to_vec();
    let namespace = take_string(&body, &mut at).to_vec();
    let reserved = take_string(&body, &mut at).to_vec();
    assert!(reserved.is_empty());
    let hash = take_string(&body, &mut at).to_vec();
    let signature_blob = take_string(&body, &mut at).to_vec();
    assert_eq!(at, body.len());
    let mut inner = 0;
    assert_eq!(take_string(&signature_blob, &mut inner), b"ssh-ed25519");
    let raw = take_string(&signature_blob, &mut inner).to_vec();
    assert_eq!(inner, signature_blob.len());
    (public_key, namespace, hash, raw)
}

struct Fixture {
    directory: PathBuf,
}

impl Fixture {
    fn run(key: &[u8], namespace: &[u8], message: &[u8], signature: &[u8]) -> Output {
        let directory = std::env::temp_dir().join(format!(
            "minidregg-sshsig-{}-{}",
            std::process::id(),
            NEXT_FIXTURE.fetch_add(1, Ordering::Relaxed)
        ));
        fs::create_dir(&directory).unwrap();
        let fixture = Fixture { directory };
        let path = |name: &str| fixture.directory.join(name);
        fs::write(path("key"), key).unwrap();
        fs::write(path("namespace"), namespace).unwrap();
        fs::write(path("message"), message).unwrap();
        fs::write(path("signature"), signature).unwrap();
        Command::new(BINARY)
            .arg("verify-sshsig")
            .arg(path("key"))
            .arg(path("namespace"))
            .arg(path("message"))
            .arg(path("signature"))
            .output()
            .unwrap()
    }
}

impl Drop for Fixture {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.directory);
    }
}

fn verdict(output: Output, expected: &[u8]) {
    assert_eq!(output.status.code(), Some(0), "{output:?}");
    assert!(output.stderr.is_empty(), "{output:?}");
    assert_eq!(output.stdout, expected, "{output:?}");
}

fn key() -> Vec<u8> {
    hex(SSH_BLOB)[19..].to_vec()
}

#[test]
fn sshsig_armour_is_raw_ed25519_over_the_standard_blob() {
    let (public_key, namespace, hash, raw) = parse_armoured();
    assert_eq!(public_key, hex(SSH_BLOB));
    assert_eq!(namespace, NAMESPACE);
    assert_eq!(hash, b"sha512");
    assert_eq!(raw.len(), 64);
    // The signed data, rebuilt independently of the binary, is the Lean-pinned bytes.
    let mut signed = b"SSHSIG".to_vec();
    for field in [NAMESPACE, b"".as_slice(), b"sha512".as_slice(), &Sha512::digest(message())] {
        signed.extend_from_slice(&(field.len() as u32).to_be_bytes());
        signed.extend_from_slice(field);
    }
    assert_eq!(signed, hex(SIGNED_DATA));
    let verifying = VerifyingKey::from_bytes(&key().try_into().unwrap()).unwrap();
    let signature = Signature::from_bytes(&raw.try_into().unwrap());
    verifying.verify(&signed, &signature).unwrap();
}

#[test]
fn sshsig_real_vector_verifies() {
    let (_, _, _, raw) = parse_armoured();
    verdict(Fixture::run(&key(), NAMESPACE, &message(), &raw), b"verified\n");
}

#[test]
fn sshsig_other_message_invalid() {
    let (_, _, _, raw) = parse_armoured();
    let mut other = message();
    other[95] ^= 1;
    verdict(Fixture::run(&key(), NAMESPACE, &other, &raw), b"invalid\n");
}

#[test]
fn sshsig_other_namespace_invalid() {
    let (_, _, _, raw) = parse_armoured();
    verdict(Fixture::run(&key(), b"dregg-enrol", &message(), &raw), b"invalid\n");
}

#[test]
fn sshsig_other_signature_invalid() {
    let (_, _, _, mut raw) = parse_armoured();
    raw[0] ^= 1;
    verdict(Fixture::run(&key(), NAMESPACE, &message(), &raw), b"invalid\n");
}

#[test]
fn sshsig_other_key_invalid() {
    let (_, _, _, raw) = parse_armoured();
    // The Mini key of the same memo is a valid Ed25519 point but not the signer.
    verdict(Fixture::run(&hex(MINI_KEY), NAMESPACE, &message(), &raw), b"invalid\n");
}

#[test]
fn sshsig_plain_ed25519_verb_refuses_it() {
    // The same signature is not a plain Ed25519 signature over the message.
    let (_, _, _, raw) = parse_armoured();
    let verifying = VerifyingKey::from_bytes(&key().try_into().unwrap()).unwrap();
    let signature = Signature::from_bytes(&raw.try_into().unwrap());
    assert!(verifying.verify_strict(&message(), &signature).is_err());
}

#[test]
fn sshsig_empty_namespace_is_an_input_error() {
    let (_, _, _, raw) = parse_armoured();
    let output = Fixture::run(&key(), b"", &message(), &raw);
    assert_eq!(output.status.code(), Some(1), "{output:?}");
    assert!(output.stdout.is_empty());
}

#[test]
fn sshsig_short_signature_is_an_input_error() {
    let (_, _, _, raw) = parse_armoured();
    let output = Fixture::run(&key(), NAMESPACE, &message(), &raw[..63]);
    assert_eq!(output.status.code(), Some(1), "{output:?}");
    assert!(output.stdout.is_empty());
}

#[test]
fn sshsig_wrong_arity_is_usage() {
    let output = Command::new(BINARY).arg("verify-sshsig").arg("a").output().unwrap();
    assert_eq!(output.status.code(), Some(2), "{output:?}");
}

#[test]
fn sshsig_fixture_mini_sig_verifies_over_the_possession_frame() {
    // The other half of the Lean fixture memo (`PayEnrolMemo.fixtureBytes`):
    // plain Ed25519 by the Mini key over "DREGG/PAY/ENROL/POSSESSION/v1" || mint || address || ssh blob.
    let frame = [
        b"DREGG/PAY/ENROL/POSSESSION/v1".to_vec(),
        hex(MINT),
        hex(ENROL_ADDRESS),
        hex(SSH_BLOB),
    ]
    .concat();
    let directory = std::env::temp_dir().join(format!("minidregg-sshsig-mini-{}", std::process::id()));
    fs::create_dir_all(&directory).unwrap();
    fs::write(directory.join("key"), hex(MINI_KEY)).unwrap();
    fs::write(directory.join("frame"), &frame).unwrap();
    fs::write(directory.join("signature"), hex(MINI_SIG)).unwrap();
    let output = Command::new(BINARY)
        .arg("verify")
        .arg(directory.join("key"))
        .arg(directory.join("frame"))
        .arg(directory.join("signature"))
        .output()
        .unwrap();
    let _ = fs::remove_dir_all(&directory);
    verdict(output, b"verified\n");
}
