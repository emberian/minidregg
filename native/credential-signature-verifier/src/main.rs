use ed25519_dalek::{Signature, VerifyingKey, PUBLIC_KEY_LENGTH, SIGNATURE_LENGTH};
use std::env;
use std::ffi::OsStr;
use std::fs::{self, File};
use std::io::{self, Read, Write};
use std::path::Path;
use std::process::ExitCode;

fn read_fixed<const N: usize>(path: &Path, role: &str) -> Result<[u8; N], String> {
    let file = File::open(path).map_err(|error| format!("cannot open {role}: {error}"))?;
    let mut bytes = Vec::with_capacity(N + 1);
    file.take((N + 1) as u64)
        .read_to_end(&mut bytes)
        .map_err(|error| format!("cannot read {role}: {error}"))?;
    bytes
        .try_into()
        .map_err(|_| format!("{role} must contain exactly {N} raw bytes"))
}

fn verify(key_path: &Path, frame_path: &Path, signature_path: &Path) -> Result<(), String> {
    let key_bytes = read_fixed::<PUBLIC_KEY_LENGTH>(key_path, "public key")?;
    let signature_bytes = read_fixed::<SIGNATURE_LENGTH>(signature_path, "signature")?;
    let key = VerifyingKey::from_bytes(&key_bytes)
        .map_err(|_| "public key point decoding failed".to_owned())?;
    let frame = fs::read(frame_path).map_err(|error| format!("cannot read frame: {error}"))?;
    let signature = Signature::from_bytes(&signature_bytes);

    // The frame is opaque. Domain separation, key selection, request binding,
    // revocation, and authority are the Lean caller's responsibility.
    let response: &[u8] = if key.verify_strict(&frame, &signature).is_ok() {
        b"verified\n"
    } else {
        b"invalid\n"
    };
    let mut stdout = io::stdout().lock();
    stdout
        .write_all(response)
        .and_then(|()| stdout.flush())
        .map_err(|error| format!("cannot write response: {error}"))
}

fn main() -> ExitCode {
    let arguments: Vec<_> = env::args_os().skip(1).collect();
    let [command, public_key, frame, signature] = arguments.as_slice() else {
        eprintln!("usage: minidregg-credential-signature-verifier verify <public-key-file> <frame-file> <signature-file>");
        return ExitCode::from(2);
    };
    if command != OsStr::new("verify") {
        eprintln!("usage: minidregg-credential-signature-verifier verify <public-key-file> <frame-file> <signature-file>");
        return ExitCode::from(2);
    }
    match verify(
        Path::new(public_key),
        Path::new(frame),
        Path::new(signature),
    ) {
        Ok(()) => ExitCode::SUCCESS,
        Err(error) => {
            eprintln!("credential signature verifier: {error}");
            ExitCode::FAILURE
        }
    }
}
