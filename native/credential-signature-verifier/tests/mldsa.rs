//! `verify-mldsa`: the ML-DSA-65 half of the hybrid scheme, by the CLI. The Ed25519 half is `verify`
//! (tests/protocol.rs); the conjunction is Lean's (`CredentialSignatureIO.combineHalves`).
use fips204::ml_dsa_65;
use fips204::traits::{KeyGen, SerDes, Signer};
use std::fs;
use std::path::PathBuf;
use std::process::Command;
use std::sync::atomic::{AtomicU64, Ordering};

const BINARY: &str = env!("CARGO_BIN_EXE_minidregg-credential-signature-verifier");
const CONTEXT: &[u8] = b"MINI/SDK/HYBRID/ML-DSA-65/v1";
static NEXT: AtomicU64 = AtomicU64::new(0);

fn directory() -> PathBuf {
    let directory = std::env::temp_dir().join(format!(
        "minidregg-mldsa-{}-{}",
        std::process::id(),
        NEXT.fetch_add(1, Ordering::Relaxed)
    ));
    fs::create_dir(&directory).unwrap();
    directory
}

/// A public deterministic test key (never production material) and its signature over `frame`.
fn signed(frame: &[u8]) -> (Vec<u8>, Vec<u8>) {
    let (public, secret) = ml_dsa_65::KG::keygen_from_seed(&[9; 32]);
    let signature = secret.try_sign_with_seed(&[0; 32], frame, CONTEXT).unwrap();
    (public.into_bytes().to_vec(), signature.to_vec())
}

fn run(key: &[u8], context: &[u8], frame: &[u8], signature: &[u8]) -> (i32, String, String) {
    let dir = directory();
    for (name, bytes) in [("key", key), ("context", context), ("frame", frame), ("signature", signature)] {
        fs::write(dir.join(name), bytes).unwrap();
    }
    let output = Command::new(BINARY)
        .arg("verify-mldsa")
        .args(["key", "context", "frame", "signature"].map(|n| dir.join(n)))
        .output()
        .unwrap();
    let _ = fs::remove_dir_all(&dir);
    (
        output.status.code().unwrap(),
        String::from_utf8(output.stdout).unwrap(),
        String::from_utf8(output.stderr).unwrap(),
    )
}

#[test]
fn a_good_signature_is_verified_and_every_change_is_invalid() {
    let frame = b"an opaque Lean frame";
    let (key, signature) = signed(frame);
    assert_eq!(run(&key, CONTEXT, frame, &signature), (0, "verified\n".into(), String::new()));
    // Wrong frame, wrong context (domain separation), flipped signature bit: invalid, exit 0, no stderr.
    assert_eq!(run(&key, CONTEXT, b"another frame", &signature).1, "invalid\n");
    assert_eq!(run(&key, b"MINI/SDK/HYBRID/OTHER/v1", frame, &signature).1, "invalid\n");
    let mut flipped = signature.clone();
    flipped[100] ^= 1;
    assert_eq!(run(&key, CONTEXT, frame, &flipped).1, "invalid\n");
    // A signature by another key does not verify under this one.
    let (other_key, _) = {
        let (public, _) = ml_dsa_65::KG::keygen_from_seed(&[10; 32]);
        (public.into_bytes().to_vec(), ())
    };
    assert_eq!(run(&other_key, CONTEXT, frame, &signature).1, "invalid\n");
}

#[test]
fn wrong_widths_are_refused_by_name_and_never_answer_verified() {
    let frame = b"f";
    let (key, signature) = signed(frame);
    for (k, s, what) in [(&key[..1951], &signature[..], "public key"), (&key[..], &signature[..3308], "signature"),
        (&key[..], &signature[..64], "signature"), (&[0u8; 32][..], &signature[..], "public key")] {
        let (code, stdout, stderr) = run(k, CONTEXT, frame, s);
        assert_eq!((code, stdout.as_str()), (1, ""), "{what}");
        assert!(stderr.contains(what) && stderr.contains("must contain exactly"), "{stderr}");
    }
    let (code, _, stderr) = run(&key, &[b'x'; 256], frame, &signature);
    assert_eq!(code, 1);
    assert!(stderr.contains("context"), "{stderr}");
}
