use std::env;
use std::fs::{self, File};
use std::io::{Read, Write};
use std::process::{Command, Stdio};
use std::time::Instant;

fn exchange(stdin: &mut impl Write, stdout: &mut impl Read, op: u8, call: &[u8]) -> Vec<u8> {
    let len = u32::try_from(call.len() + 1).unwrap();
    stdin.write_all(&len.to_le_bytes()).unwrap();
    stdin.write_all(&[op]).unwrap();
    stdin.write_all(call).unwrap();
    stdin.flush().unwrap();
    let mut header = [0u8; 4];
    stdout.read_exact(&mut header).unwrap();
    let len = u32::from_le_bytes(header) as usize;
    assert!((1..=12_102_760).contains(&len));
    let mut response = vec![0u8; len];
    stdout.read_exact(&mut response).unwrap();
    assert_eq!(response[0], op, "Host returned failure opcode");
    response[1..].to_vec()
}

fn main() {
    let args: Vec<String> = env::args().collect();
    assert_eq!(args.len(), 6, "HOST CONFIG CALL OUTPUT_DIR STDERR");
    let call = fs::read(&args[3]).unwrap();
    let stderr = File::create(&args[5]).unwrap();
    let mut child = Command::new(&args[1])
        .arg(&args[2]).arg("stdio")
        .stdin(Stdio::piped()).stdout(Stdio::piped()).stderr(Stdio::from(stderr))
        .spawn().unwrap();
    let mut stdin = child.stdin.take().unwrap();
    let mut stdout = child.stdout.take().unwrap();
    let started = Instant::now();
    let submit = exchange(&mut stdin, &mut stdout, 2, &call);
    eprintln!("stdio-submit-ms={}", started.elapsed().as_millis());
    fs::write(format!("{}/outcome.bin", args[4]), submit).unwrap();
    let started = Instant::now();
    let lookup = exchange(&mut stdin, &mut stdout, 3, &call);
    eprintln!("same-session-lookup-ms={}", started.elapsed().as_millis());
    fs::write(format!("{}/lookup.bin", args[4]), lookup).unwrap();
    drop(stdin);
    assert!(child.wait().unwrap().success());
}
