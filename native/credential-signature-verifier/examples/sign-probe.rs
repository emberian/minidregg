//! PUBLIC TEST KEYS ONLY: the seed is one public byte repeated 32 times.
//! This fixture helper is an example, never an operation of the verifier binary.

use ed25519_dalek::{Signer, SigningKey};
use std::env;
use std::fs;
use std::process::ExitCode;

fn run() -> Result<(), String> {
    let arguments: Vec<_> = env::args_os().skip(1).collect();
    let [seed, frame_path, key_path, signature_path] = arguments.as_slice() else {
        return Err(
            "usage: sign-probe <seed-byte 0..255> <frame-file> <public-key-file> <signature-file>"
                .to_owned(),
        );
    };
    let seed_byte = seed
        .to_str()
        .filter(|value| !value.is_empty() && value.bytes().all(|byte| byte.is_ascii_digit()))
        .and_then(|value| value.parse::<u8>().ok())
        .ok_or("seed-byte must be an unsigned decimal byte in 0..255")?;
    eprintln!("PUBLIC TEST KEY: seed = [{seed_byte}; 32]; anyone can reproduce this signing key.");
    let frame = fs::read(frame_path).map_err(|error| format!("cannot read frame: {error}"))?;
    let key = SigningKey::from_bytes(&[seed_byte; 32]);
    let signature = key.sign(&frame);
    fs::write(key_path, key.verifying_key().to_bytes())
        .map_err(|error| format!("cannot write public test key: {error}"))?;
    fs::write(signature_path, signature.to_bytes())
        .map_err(|error| format!("cannot write test signature: {error}"))?;
    Ok(())
}

fn main() -> ExitCode {
    match run() {
        Ok(()) => ExitCode::SUCCESS,
        Err(error) => {
            eprintln!("sign-probe: {error}");
            ExitCode::FAILURE
        }
    }
}
