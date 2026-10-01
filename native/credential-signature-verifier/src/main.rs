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

const USAGE: &str = "usage: minidregg-credential-signature-verifier verify <public-key-file> <frame-file> <signature-file>\n       minidregg-credential-signature-verifier verify-sshsig <public-key-file> <namespace-file> <message-file> <signature-file>\n       minidregg-credential-signature-verifier serve";

fn main() -> ExitCode {
    let arguments: Vec<_> = env::args_os().skip(1).collect();
    if arguments.len() == 1 && arguments[0] == "serve" {
        return serve();
    }
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

/// `serve`: the long-lived form a Lean Host keeps for its whole lifetime
/// (`Compiler.NativeCoprocess`). Each request frame on stdin is one argv for
/// this same executable; it runs as its own child process, so its files, its
/// stdout, its stderr and its exit code are exactly the one-shot invocation's.
/// The reply frame carries those three. The Host forks this small process
/// once instead of forking its own large address space for every call.
/// Frames: request `u32 argc, (u32 len, bytes)*`; reply `u32 code,
/// u64 len, stdout, u64 len, stderr`; integers big-endian. EOF ends it.
fn serve() -> ExitCode {
    use std::ffi::OsString;
    use std::io::{BufReader, BufWriter, ErrorKind};
    use std::os::unix::ffi::OsStringExt;
    use std::os::unix::process::ExitStatusExt;
    use std::process::{Command, Stdio};
    const MAX_ARGS: usize = 64;
    const MAX_ARG_BYTES: usize = 64 * 1024;
    let Ok(executable) = env::current_exe() else {
        return ExitCode::from(2);
    };
    let mut input = BufReader::new(io::stdin().lock());
    let mut output = BufWriter::new(io::stdout().lock());
    let mut word = [0u8; 4];
    loop {
        match input.read_exact(&mut word) {
            Ok(()) => {}
            Err(error) if error.kind() == ErrorKind::UnexpectedEof => return ExitCode::SUCCESS,
            Err(_) => return ExitCode::FAILURE,
        }
        let count = u32::from_be_bytes(word) as usize;
        if count == 0 || count > MAX_ARGS {
            return ExitCode::FAILURE;
        }
        let mut arguments = Vec::with_capacity(count);
        for _ in 0..count {
            if input.read_exact(&mut word).is_err() {
                return ExitCode::FAILURE;
            }
            let length = u32::from_be_bytes(word) as usize;
            if length > MAX_ARG_BYTES {
                return ExitCode::FAILURE;
            }
            let mut bytes = vec![0u8; length];
            if input.read_exact(&mut bytes).is_err() {
                return ExitCode::FAILURE;
            }
            arguments.push(OsString::from_vec(bytes));
        }
        // A request names a one-shot command, never another server.
        if arguments[0] == "serve" {
            return ExitCode::FAILURE;
        }
        let Ok(result) = Command::new(&executable)
            .args(&arguments)
            .stdin(Stdio::null())
            .output()
        else {
            return ExitCode::FAILURE;
        };
        let code: u32 = match (result.status.code(), result.status.signal()) {
            (Some(code), _) => code as u32,
            (None, Some(signal)) => 128 + signal as u32,
            (None, None) => 255,
        };
        let written = output
            .write_all(&code.to_be_bytes())
            .and_then(|()| output.write_all(&(result.stdout.len() as u64).to_be_bytes()))
            .and_then(|()| output.write_all(&result.stdout))
            .and_then(|()| output.write_all(&(result.stderr.len() as u64).to_be_bytes()))
            .and_then(|()| output.write_all(&result.stderr))
            .and_then(|()| output.flush());
        if written.is_err() {
            return ExitCode::FAILURE;
        }
    }
}
