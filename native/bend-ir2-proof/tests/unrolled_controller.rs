//! Actual source-admitted full controller, unrolled and emitted by Lean.
//! This is a public-program conformance test, not a hiding claim.
use std::{fs, path::PathBuf, process::Command};

#[test]
fn source_admitted_full_controller_proof_binds_input_handled_and_output() {
    let fixture = PathBuf::from(std::env::var("BEND_UNROLLED_FIXTURE")
        .expect("set BEND_UNROLLED_FIXTURE to the checked Lean producer output"));
    let output = PathBuf::from(std::env::var("BEND_UNROLLED_PROOF_OUTPUT")
        .expect("set a private owned proof-output directory"));
    fs::create_dir_all(&output).unwrap();
    let proof = output.join("unrolled-controller-proof.bin");
    let binary = env!("CARGO_BIN_EXE_bend-ir2-proof");
    let result = Command::new(binary).arg("prove")
        .arg(fixture.join("descriptor.json")).arg(fixture.join("public.csv"))
        .arg(fixture.join("trace.csv")).arg(&proof).output().unwrap();
    assert!(result.status.success(), "actual proof production failed: {}",
        String::from_utf8_lossy(&result.stderr));
    for (public, expected) in [("public.csv", true), ("wrong-input.csv", false),
        ("wrong-handled.csv", false), ("wrong-output.csv", false)] {
        let result = Command::new(binary).arg("verify")
            .arg(fixture.join("descriptor.json")).arg(fixture.join(public)).arg(&proof)
            .output().unwrap();
        assert_eq!(result.status.success(), expected, "public binding {public}: {}",
            String::from_utf8_lossy(&result.stderr));
    }
    assert!(fs::metadata(proof).unwrap().len() > 0);
}
