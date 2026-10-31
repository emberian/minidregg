//! A reader that closes `mini`'s standard output early (`mini --help | grep -q ...`,
//! `... | head -c1`) ends `mini` quietly with 141, never a panic (`src/streams.rs`).
use std::process::{Command, Stdio};

#[test]
fn a_closed_stdout_ends_mini_with_141_and_no_panic() {
    for round in 0..20 {
        let mut child = Command::new(env!("CARGO_BIN_EXE_mini"))
            .arg("--help")
            .stdin(Stdio::null())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .expect("mini starts");
        // The read end is closed before `mini` writes a byte: its write always meets EPIPE.
        drop(child.stdout.take());
        let output = child.wait_with_output().expect("mini ends");
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert!(!stderr.contains("panicked"), "round {round}: {stderr}");
        assert_eq!(output.status.code(), Some(141), "round {round}: {:?} {stderr}", output.status);
    }
}
