use ed25519_dalek::{Signature, Signer, SigningKey, Verifier, VerifyingKey};
use std::fs;
use std::path::PathBuf;
use std::process::{Command, Output};
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::{SystemTime, UNIX_EPOCH};

const BINARY: &str = env!("CARGO_BIN_EXE_minidregg-credential-signature-verifier");
static NEXT_FIXTURE: AtomicU64 = AtomicU64::new(0);

struct Fixture {
    directory: PathBuf,
    key: PathBuf,
    frame: PathBuf,
    signature: PathBuf,
}

impl Fixture {
    fn new(key: &[u8], frame: &[u8], signature: &[u8]) -> Self {
        let nonce = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_nanos();
        let directory = std::env::temp_dir().join(format!(
            "minidregg-ed25519-{}-{nonce}-{}",
            std::process::id(),
            NEXT_FIXTURE.fetch_add(1, Ordering::Relaxed)
        ));
        fs::create_dir(&directory).unwrap();
        let fixture = Self {
            key: directory.join("public key.raw"),
            frame: directory.join("opaque frame.raw"),
            signature: directory.join("signature.raw"),
            directory,
        };
        fs::write(&fixture.key, key).unwrap();
        fs::write(&fixture.frame, frame).unwrap();
        fs::write(&fixture.signature, signature).unwrap();
        fixture
    }

    fn signed(frame: &[u8]) -> Self {
        // Public deterministic test seed, never production credential material.
        let key = SigningKey::from_bytes(&[41; 32]);
        Self::new(
            &key.verifying_key().to_bytes(),
            frame,
            &key.sign(frame).to_bytes(),
        )
    }

    fn verify(&self) -> Output {
        Command::new(BINARY)
            .arg("verify")
            .arg(&self.key)
            .arg(&self.frame)
            .arg(&self.signature)
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
    assert_eq!(output.stdout, expected);
    assert!(output.stderr.is_empty(), "{output:?}");
}

fn failure(output: Output, expected_code: i32) {
    assert_eq!(output.status.code(), Some(expected_code), "{output:?}");
    assert!(output.stdout.is_empty(), "{output:?}");
    assert!(!output.stderr.is_empty(), "{output:?}");
}

fn hex(value: &str) -> Vec<u8> {
    assert_eq!(value.len() % 2, 0);
    value
        .as_bytes()
        .chunks_exact(2)
        .map(|pair| u8::from_str_radix(std::str::from_utf8(pair).unwrap(), 16).unwrap())
        .collect()
}

#[test]
fn protocol_rfc8032_vectors() {
    // RFC 8032 section 7.1, TEST 1 and TEST 2:
    // https://www.rfc-editor.org/rfc/rfc8032.txt
    let vectors = [
        (
            "d75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f707511a",
            "",
            concat!(
                "e5564300c360ac729086e2cc806e828a84877f1eb8e5d974d873e06522490155",
                "5fb8821590a33bacc61e39701cf9b46bd25bf5f0595bbe24655141438e7a100b"
            ),
        ),
        (
            "3d4017c3e843895a92b70aa74d1b7ebc9c982ccf2ec4968cc0cd55f12af4660c",
            "72",
            concat!(
                "92a009a9f0d4cab8720e820b5f642540a2b27b5416503f8fb3762223ebdb69da",
                "085ac1e43e15996e458f3613d0f11d8c387b2eaeb4302aeeb00d291612bb0c00"
            ),
        ),
    ];
    for (key, frame, signature) in vectors {
        let fixture = Fixture::new(&hex(key), &hex(frame), &hex(signature));
        verdict(fixture.verify(), b"verified\n");
    }
}

#[test]
fn protocol_opaque_binary_frame_and_modified_frame() {
    let frame = b"\x00\xffLean frame\r\n\x80\x00";
    let fixture = Fixture::signed(frame);
    verdict(fixture.verify(), b"verified\n");
    let mut modified = frame.to_vec();
    modified[0] ^= 1;
    fs::write(&fixture.frame, modified).unwrap();
    verdict(fixture.verify(), b"invalid\n");
}

#[test]
fn protocol_wrong_key() {
    let fixture = Fixture::signed(b"key is part of the verification input");
    verdict(fixture.verify(), b"verified\n");
    let other = SigningKey::from_bytes(&[42; 32]);
    fs::write(&fixture.key, other.verifying_key().to_bytes()).unwrap();
    verdict(fixture.verify(), b"invalid\n");
}

#[test]
fn protocol_modified_signature() {
    let fixture = Fixture::signed(b"signature is part of the verification input");
    verdict(fixture.verify(), b"verified\n");
    let mut signature = fs::read(&fixture.signature).unwrap();
    signature[32] ^= 1;
    fs::write(&fixture.signature, signature).unwrap();
    verdict(fixture.verify(), b"invalid\n");
}

#[test]
fn protocol_wrong_lengths() {
    let fixture = Fixture::signed(b"exact length framing");
    let key = fs::read(&fixture.key).unwrap();
    for length in [0, 1, 31, 33, 1024] {
        fs::write(&fixture.key, vec![0; length]).unwrap();
        failure(fixture.verify(), 1);
    }
    fs::write(&fixture.key, key).unwrap();
    for length in [0, 1, 63, 65, 1024] {
        fs::write(&fixture.signature, vec![0; length]).unwrap();
        failure(fixture.verify(), 1);
    }
}

fn malformed_point() -> [u8; 32] {
    // Ask the pinned point decoder for a malformed fixture. This is test data
    // selection, not an independent or production point implementation.
    (0..=u8::MAX)
        .map(|byte| [byte; 32])
        .find(|bytes| VerifyingKey::from_bytes(bytes).is_err())
        .expect("a repeated-byte point fixture must fail decompression")
}

#[test]
fn protocol_malformed_public_key() {
    let fixture = Fixture::signed(b"public key parser errors are input failures");
    fs::write(&fixture.key, malformed_point()).unwrap();
    failure(fixture.verify(), 1);
}

#[test]
fn protocol_malformed_signature_point_and_scalar() {
    let fixture = Fixture::signed(b"strict verification owns signature validation");
    let original = fs::read(&fixture.signature).unwrap();
    let mut malformed_r = original.clone();
    malformed_r[..32].copy_from_slice(&malformed_point());
    fs::write(&fixture.signature, malformed_r).unwrap();
    verdict(fixture.verify(), b"invalid\n");
    let mut malformed_s = original;
    malformed_s[32..].fill(0xff);
    fs::write(&fixture.signature, malformed_s).unwrap();
    verdict(fixture.verify(), b"invalid\n");
}

#[test]
fn protocol_weak_key_and_small_order_r() {
    let mut identity = [0; 32];
    identity[0] = 1;
    let mut signature = [0; 64];
    signature[..32].copy_from_slice(&identity);
    let frame = b"the ordinary verifier accepts this universal weak-key forgery";
    let weak = VerifyingKey::from_bytes(&identity).unwrap();
    assert!(weak.is_weak());
    assert!(weak
        .verify(frame, &Signature::from_bytes(&signature))
        .is_ok());
    let fixture = Fixture::new(&identity, frame, &signature);
    verdict(fixture.verify(), b"invalid\n");
    let strong = SigningKey::from_bytes(&[41; 32]).verifying_key();
    assert!(!strong.is_weak());
    fs::write(&fixture.key, strong.to_bytes()).unwrap();
    verdict(fixture.verify(), b"invalid\n");
}

#[test]
fn protocol_io_failures() {
    let fixture = Fixture::signed(b"missing inputs never emit a verdict");
    for path in [&fixture.key, &fixture.frame, &fixture.signature] {
        let bytes = fs::read(path).unwrap();
        fs::remove_file(path).unwrap();
        failure(fixture.verify(), 1);
        fs::write(path, bytes).unwrap();
    }
}

#[test]
fn protocol_exact_arguments_and_no_sign_operation() {
    let cases: &[&[&str]] = &[
        &[],
        &["verify"],
        &["verify", "one", "two"],
        &["verify", "one", "two", "three", "four"],
        &["sign", "one", "two", "three"],
        &["--help"],
    ];
    for arguments in cases {
        failure(Command::new(BINARY).args(*arguments).output().unwrap(), 2);
    }
}
