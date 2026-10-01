use ed25519_dalek::{Signature, VerifyingKey, PUBLIC_KEY_LENGTH, SIGNATURE_LENGTH};
use sha2::{Digest, Sha512};
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
    respond(response)
}

fn respond(response: &[u8]) -> Result<(), String> {
    let mut stdout = io::stdout().lock();
    stdout
        .write_all(response)
        .and_then(|()| stdout.flush())
        .map_err(|error| format!("cannot write response: {error}"))
}

/// An SSH `string`: a big-endian u32 length, then the bytes.
fn ssh_string(out: &mut Vec<u8>, bytes: &[u8]) -> Result<(), String> {
    let length = u32::try_from(bytes.len()).map_err(|_| "SSH string exceeds 2^32 bytes".to_owned())?;
    out.extend_from_slice(&length.to_be_bytes());
    out.extend_from_slice(bytes);
    Ok(())
}

/// OpenSSH PROTOCOL.sshsig: the bytes an SSHSIG signature is over,
/// `"SSHSIG" || string namespace || string "" || string "sha512" || string SHA-512(message)`.
/// This is the only hash computed here; Lean fixes every other byte
/// (`Kernel.PayEnrolMemo.sshsigSignedData`).
fn sshsig_signed_data(namespace: &[u8], message: &[u8]) -> Result<Vec<u8>, String> {
    let digest = Sha512::digest(message);
    let mut signed = b"SSHSIG".to_vec();
    ssh_string(&mut signed, namespace)?;
    ssh_string(&mut signed, b"")?;
    ssh_string(&mut signed, b"sha512")?;
    ssh_string(&mut signed, &digest)?;
    Ok(signed)
}

fn verify_sshsig(
    key_path: &Path,
    namespace_path: &Path,
    message_path: &Path,
    signature_path: &Path,
) -> Result<(), String> {
    let key_bytes = read_fixed::<PUBLIC_KEY_LENGTH>(key_path, "public key")?;
    let signature_bytes = read_fixed::<SIGNATURE_LENGTH>(signature_path, "signature")?;
    let key = VerifyingKey::from_bytes(&key_bytes)
        .map_err(|_| "public key point decoding failed".to_owned())?;
    let namespace =
        fs::read(namespace_path).map_err(|error| format!("cannot read namespace: {error}"))?;
    if namespace.is_empty() {
        return Err("SSHSIG namespace must not be empty".to_owned());
    }
    let message = fs::read(message_path).map_err(|error| format!("cannot read message: {error}"))?;
    let signed = sshsig_signed_data(&namespace, &message)?;
    let signature = Signature::from_bytes(&signature_bytes);
    let response: &[u8] = if key.verify_strict(&signed, &signature).is_ok() {
        b"verified\n"
    } else {
        b"invalid\n"
    };
    respond(response)
}

const USAGE: &str = "usage: minidregg-credential-signature-verifier verify <public-key-file> <frame-file> <signature-file>\n       minidregg-credential-signature-verifier verify-sshsig <public-key-file> <namespace-file> <message-file> <signature-file>";

fn main() -> ExitCode {
    let arguments: Vec<_> = env::args_os().skip(1).collect();
    let result = match arguments.as_slice() {
        [command, public_key, frame, signature] if command == OsStr::new("verify") => {
            verify(Path::new(public_key), Path::new(frame), Path::new(signature))
        }
        [command, public_key, namespace, message, signature]
            if command == OsStr::new("verify-sshsig") =>
        {
            verify_sshsig(
                Path::new(public_key),
                Path::new(namespace),
                Path::new(message),
                Path::new(signature),
            )
        }
        _ => {
            eprintln!("{USAGE}");
            return ExitCode::from(2);
        }
    };
    match result {
        Ok(()) => ExitCode::SUCCESS,
        Err(error) => {
            eprintln!("credential signature verifier: {error}");
            ExitCode::FAILURE
        }
    }
}
