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
