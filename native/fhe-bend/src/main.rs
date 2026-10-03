use minidregg_fhe_bend::{canonical, check, evaluate, read, Completion, Request, Result};
use std::{env, path::Path};
fn main() -> Result<()> {
    let a: Vec<String> = env::args().collect();
    if a.len() != 6 {
        return Err(
            "usage: fhe-bend evaluate|check ARTIFACT REQUEST COMPLETION EXPECTED_ARTIFACT_SHA256"
                .into(),
        );
    }
    let artifact = read(Path::new(&a[2]))?;
    let request: Request = serde_json::from_slice(&read(Path::new(&a[3]))?)?;
    match a[1].as_str() {
        "evaluate" => {
            let out = evaluate(&artifact, &a[5], &request)?;
            std::fs::write(&a[4], canonical(&out)?)?;
        }
        "check" => {
            let candidate: Completion = serde_json::from_slice(&read(Path::new(&a[4]))?)?;
            check(&artifact, &a[5], &request, &candidate)?;
            println!("FHE-BEND-CIPHERTEXT-REPLAY: PASS");
        }
        _ => return Err("unknown command".into()),
    }
    Ok(())
}
