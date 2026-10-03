//! Actual bounded-length cSHAKE graph proof; full-transcript hiding is not asserted.
use std::{fs, path::PathBuf, process::Command};

#[test]
fn bounded_cshake_proof_binds_digest_and_validity() {
    let fixture = PathBuf::from(std::env::var("BEND_COMMITMENT_FIXTURE")
        .expect("set BEND_COMMITMENT_FIXTURE to the checked Lean producer output"));
    let output = PathBuf::from(std::env::var("BEND_COMMITMENT_PROOF_OUTPUT")
        .expect("set a private owned proof-output directory"));
    fs::create_dir_all(&output).unwrap();
    let proof = output.join("bounded-commitment-proof.bin");
    let binary = env!("CARGO_BIN_EXE_bend-ir2-proof");
    let result = Command::new(binary).arg("prove")
        .arg(fixture.join("descriptor.json")).arg(fixture.join("public.csv"))
        .arg(fixture.join("trace.csv")).arg(&proof).output().unwrap();
    assert!(result.status.success(), "actual proof production failed: {}",
        String::from_utf8_lossy(&result.stderr));
    for (public, expected) in [("public.csv", true), ("wrong-digest.csv", false),
        ("wrong-validity.csv", false)] {
        let result = Command::new(binary).arg("verify")
            .arg(fixture.join("descriptor.json")).arg(fixture.join(public)).arg(&proof)
            .output().unwrap();
        assert_eq!(result.status.success(), expected, "public binding {public}: {}",
            String::from_utf8_lossy(&result.stderr));
    }
    assert!(fs::metadata(proof).unwrap().len() > 0);
}

/// Mutate only an owned witness COPY. The prover/verifier and original fixture
/// stay unchanged. Private input bit0 no longer agrees with the constrained XOR
/// output and shared commitment payload, so no valid proof should be released.
#[test]
fn shared_execution_rejects_inconsistent_private_wire() {
    use std::io::Write;
    use std::os::unix::fs::OpenOptionsExt;
    let fixture = PathBuf::from(std::env::var("BEND_COMMITMENT_FIXTURE")
        .expect("set checked shared execution fixture"));
    let output = PathBuf::from(std::env::var("BEND_COMMITMENT_PROOF_OUTPUT")
        .expect("set an owned private output directory"));
    fs::create_dir_all(&output).unwrap();
    let original = fs::read_to_string(fixture.join("trace.csv")).unwrap();
    let mut row: Vec<&str> = original.trim_end_matches('\n').split(',').collect();
    row[0] = match row[0] { "0" => "1", "1" => "0", _ => panic!("expected binary input wire") };
    let bad_trace = output.join(format!("bad-private-wire-{}.csv", std::process::id()));
    let mut file = fs::OpenOptions::new().write(true).create_new(true).mode(0o600)
        .open(&bad_trace).unwrap();
    file.write_all((row.join(",") + "\n").as_bytes()).unwrap();
    file.sync_all().unwrap();
    let bad_proof = output.join(format!("bad-private-wire-{}.proof", std::process::id()));
    let result = Command::new(env!("CARGO_BIN_EXE_bend-ir2-proof")).arg("prove")
        .arg(fixture.join("descriptor.json")).arg(fixture.join("public.csv"))
        .arg(bad_trace).arg(&bad_proof).output().unwrap();
    assert!(!result.status.success(), "inconsistent private wire incorrectly produced a verified proof");
    assert!(!bad_proof.exists(), "failed proof was released");
}
