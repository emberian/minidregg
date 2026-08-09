//! The work-9101 performance comparison is intentionally manual.  Ordinary
//! correctness tests never turn wall-clock behavior into a semantic gate.

use std::process::Command;

#[test]
#[ignore = "manual performance evidence; run the native_dispatch_bench release binary"]
fn generated_work_9101_dispatch_overhead() {
    let status = Command::new(env!("CARGO_BIN_EXE_native_dispatch_bench"))
        .status()
        .expect("native dispatch benchmark binary must launch");
    assert!(status.success());
}
