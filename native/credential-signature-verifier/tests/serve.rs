//! `serve` answers every request with exactly the one-shot invocation's
//! exit code, stdout and stderr, many requests per process.
use ed25519_dalek::{Signer, SigningKey};
use std::fs;
use std::io::{Read, Write};
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};

const BINARY: &str = env!("CARGO_BIN_EXE_minidregg-credential-signature-verifier");

fn frame(arguments: &[&[u8]]) -> Vec<u8> {
    let mut out = (arguments.len() as u32).to_be_bytes().to_vec();
    for argument in arguments {
        out.extend_from_slice(&(argument.len() as u32).to_be_bytes());
        out.extend_from_slice(argument);
    }
    out
}

fn reply(stream: &mut impl Read) -> (u32, Vec<u8>, Vec<u8>) {
    let mut tag = [0u8; 8];
    stream.read_exact(&mut tag).unwrap();
    assert_eq!(&tag, b"MDCOPRC1", "every serve reply opens with the reply tag");
    let mut word = [0u8; 4];
    stream.read_exact(&mut word).unwrap();
    let code = u32::from_be_bytes(word);
    let mut long = [0u8; 8];
    stream.read_exact(&mut long).unwrap();
    let mut stdout = vec![0u8; u64::from_be_bytes(long) as usize];
    stream.read_exact(&mut stdout).unwrap();
    stream.read_exact(&mut long).unwrap();
    let mut stderr = vec![0u8; u64::from_be_bytes(long) as usize];
    stream.read_exact(&mut stderr).unwrap();
    (code, stdout, stderr)
}

fn path(p: &Path) -> &[u8] {
    p.to_str().unwrap().as_bytes()
}

#[test]
fn serve_answers_many_requests_exactly_as_one_shot_invocations() {
    let directory: PathBuf = std::env::temp_dir().join(format!("minidregg-serve-{}", std::process::id()));
    let _ = fs::remove_dir_all(&directory);
    fs::create_dir(&directory).unwrap();
    let key = SigningKey::from_bytes(&[41; 32]);
    let message = b"opaque frame";
    let (public, data, good, bad) = (directory.join("key"), directory.join("frame"), directory.join("good"), directory.join("bad"));
    fs::write(&public, key.verifying_key().to_bytes()).unwrap();
    fs::write(&data, message).unwrap();
    fs::write(&good, key.sign(message).to_bytes()).unwrap();
    let mut wrong = key.sign(message).to_bytes();
    wrong[0] ^= 1;
    fs::write(&bad, wrong).unwrap();
    let missing = directory.join("absent");
    let requests: Vec<Vec<&[u8]>> = vec![
        vec![b"verify", path(&public), path(&data), path(&good)],
        vec![b"verify", path(&public), path(&data), path(&bad)],
        vec![b"verify", path(&public), path(&data), path(&missing)],
        vec![b"verify", path(&public)],
        vec![b"verify", path(&public), path(&data), path(&good)],
    ];
    let mut server = Command::new(BINARY).arg("serve").stdin(Stdio::piped()).stdout(Stdio::piped()).spawn().unwrap();
    let mut input = server.stdin.take().unwrap();
    let mut output = server.stdout.take().unwrap();
    for request in &requests {
        input.write_all(&frame(request)).unwrap();
        input.flush().unwrap();
        let served = reply(&mut output);
        let one_shot = Command::new(BINARY)
            .args(request.iter().map(|a| std::str::from_utf8(a).unwrap()))
            .stdin(Stdio::null())
            .output()
            .unwrap();
        assert_eq!(served, (one_shot.status.code().unwrap() as u32, one_shot.stdout, one_shot.stderr));
    }
    // A request may not start another server.
    input.write_all(&frame(&[b"serve"])).unwrap();
    drop(input);
    assert!(!server.wait().unwrap().success());
    fs::remove_dir_all(&directory).unwrap();
}
