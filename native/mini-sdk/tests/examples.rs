//! The worked example's output is asserted: `examples/intent.rs` runs (offline core only, no Host)
//! and prints exactly `examples/intent.expected`, the same text the TypeScript example prints; and
//! the intent bytes it prints are the bytes LEAN emitted for the same intent.
use std::process::Command;

use mini_sdk::hex;
use serde_json::Value;

fn run_example() -> String {
    let manifest = concat!(env!("CARGO_MANIFEST_DIR"), "/Cargo.toml");
    let out = Command::new(env!("CARGO"))
        .args(["run", "--offline", "--locked", "--quiet", "--example", "intent", "--manifest-path", manifest])
        .output()
        .expect("cargo runs");
    assert!(out.status.success(), "example failed: {}", String::from_utf8_lossy(&out.stderr));
    String::from_utf8(out.stdout).unwrap()
}

#[test]
fn the_intent_example_prints_exactly_its_pinned_output() {
    let expected = std::fs::read_to_string(concat!(env!("CARGO_MANIFEST_DIR"), "/examples/intent.expected")).unwrap();
    assert_eq!(run_example(), expected);
}

#[test]
fn the_examples_intent_bytes_are_leans() {
    let lean: Value = serde_json::from_str(
        &std::fs::read_to_string(concat!(env!("CARGO_MANIFEST_DIR"), "/golden/lean-intents.json"))
            .expect("lean-intents.json (emitted by Kernel/Contracts/IntentVectors.lean)")).unwrap();
    let row = lean["vectors"].as_array().unwrap().iter().find(|r| r["name"] == "example-invoke").expect("example-invoke row");
    assert_eq!(row["result"], "ok");
    let printed = run_example();
    let line = printed.lines().skip_while(|l| !l.starts_with("intent bytes")).nth(1).unwrap().trim();
    assert_eq!(line, row["bytes"].as_str().unwrap());
    let id = printed.lines().find_map(|l| l.strip_prefix("invocation id  ")).unwrap();
    let preimage = hex::decode(row["idPreimage"].as_str().unwrap()).unwrap();
    assert_eq!(id, hex::encode(&mini_sdk::sha256(&preimage)), "the printed digest is SHA-256 of Lean's id preimage");
}
