//! Full admitted two-tick controller and salted raw-state commitment in one
//! actual proof. Diagnostic Context/raw codec do not authorize world admission.
use std::{fs, path::PathBuf, process::Command};

#[test]
fn admitted_controller_and_private_salt_share_one_proof() {
    let fixture = PathBuf::from(std::env::var("BEND_CONTROLLER_COMMITMENT_FIXTURE").unwrap());
    let output = PathBuf::from(std::env::var("BEND_CONTROLLER_COMMITMENT_OUTPUT").unwrap());
    fs::create_dir_all(&output).unwrap();
    let proof = output.join("controller-commitment.bin");
    let binary = env!("CARGO_BIN_EXE_bend-ir2-proof");
    let produced = Command::new(binary).arg("prove").arg(fixture.join("descriptor.json"))
        .arg(fixture.join("public.csv")).arg(fixture.join("trace.csv")).arg(&proof)
        .output().unwrap();
    assert!(produced.status.success(), "proof production failed: {}",
        String::from_utf8_lossy(&produced.stderr));
    for (public, expected) in [("public.csv", true), ("wrong-digest.csv", false),
        ("wrong-validity.csv", false), ("wrong-input.csv", false)] {
        let verified = Command::new(binary).arg("verify").arg(fixture.join("descriptor.json"))
            .arg(fixture.join(public)).arg(&proof).output().unwrap();
        assert_eq!(verified.status.success(), expected, "binding {public}: {}",
            String::from_utf8_lossy(&verified.stderr));
    }
    assert!(fs::metadata(proof).unwrap().len() > 0);
}
