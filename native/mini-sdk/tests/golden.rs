//! Golden vectors: `golden/vectors.json` holds hand-written inputs and the offline core's
//! outputs under `"expect"`. `MINI_SDK_REGEN=1` rewrites `"expect"`; otherwise every value must
//! match. The TS SDK checks the same file and the wasm build, so the three agree or all fail.
use mini_sdk::contracts::{canonical_json, spelling};
use mini_sdk::explain::{explain, Bound};
use mini_sdk::{hex, profile, sha256};
use serde_json::{json, Map, Value};

const PATH: &str = concat!(env!("CARGO_MANIFEST_DIR"), "/golden/vectors.json");

fn h32(v: &Value) -> [u8; 32] {
    hex::decode(v.as_str().unwrap()).unwrap().try_into().unwrap()
}

fn compute(g: &Value) -> Value {
    use ed25519_dalek::Signer;
    let seed: [u8; 64] = hex::decode(g["seed"].as_str().unwrap()).unwrap().try_into().unwrap();
    let mut out = Map::new();
    out.insert("derive".into(), g["derive"].as_array().unwrap().iter().map(|d| {
        json!(hex::encode(profile::derive(&seed, d["path"].as_str().unwrap()).verifying_key().as_bytes()))
    }).collect());
    out.insert("sign".into(), g["sign"].as_array().unwrap().iter().map(|s| {
        let key = profile::derive(&seed, s["path"].as_str().unwrap());
        json!(hex::encode(&key.sign(&hex::decode(s["message"].as_str().unwrap()).unwrap()).to_bytes()))
    }).collect());
    out.insert("canonicalJson".into(), g["canonicalJson"].as_array().unwrap().iter()
        .map(|c| json!(canonical_json(&c["input"]).unwrap())).collect());
    let mut intents = Map::new();
    for row in g["intents"].as_array().unwrap() {
        let i = spelling::intent(&row["intent"]).unwrap();
        intents.insert(row["name"].as_str().unwrap().into(), json!({
            "bytes": hex::encode(&i.canonical_bytes().unwrap()), "invocationId": i.invocation_id().unwrap().hex()}));
    }
    out.insert("intents".into(), Value::Object(intents));
    let low = &g["lowering"];
    let row = g["intents"].as_array().unwrap().iter().find(|r| r["name"] == low["intent"]).unwrap();
    let lowered = spelling::intent(&row["intent"]).unwrap().lower(&spelling::lowering(&low["context"]).unwrap()).unwrap();
    out.insert("lowering".into(), json!(canonical_json(&lowered).unwrap()));
    out.insert("headers".into(), g["headers"].as_array().unwrap().iter().map(|l| {
        let hs: Vec<Vec<u8>> = l.as_array().unwrap().iter().map(|h| hex::decode(h.as_str().unwrap()).unwrap()).collect();
        json!(hex::encode(&mini_sdk::confirm::headers_digest(&hs).unwrap()))
    }).collect());
    let e = &g["explain"];
    let text = explain(&fixture("intent.json"), &fixture("plan.json"), &Bound {
        intent_sha256: h32(&e["intentSha256"]), plan_sha256: h32(&e["planSha256"]), headers_sha256: h32(&e["headersSha256"]) }).text;
    out.insert("explain".into(), json!({"text": text, "sha256": hex::encode(&sha256(text.as_bytes()))}));
    let c = &g["confirm"];
    let nonce: [u8; 16] = hex::decode(c["nonce"].as_str().unwrap()).unwrap().try_into().unwrap();
    out.insert("confirm".into(), json!(hex::encode(&mini_sdk::confirm::confirm_digest(
        &mini_sdk::InvocationId(h32(&c["invocation"])), c["attempt"].as_u64().unwrap() as u32, &h32(&c["intentSha256"]),
        &h32(&c["planSha256"]), &h32(&c["headersSha256"]), &h32(&c["explanationSha256"]), &nonce).unwrap())));
    Value::Object(out)
}

fn fixture(name: &str) -> Value {
    serde_json::from_str(&std::fs::read_to_string(format!("{}/tests/fixtures/{name}", env!("CARGO_MANIFEST_DIR"))).unwrap()).unwrap()
}

#[test]
fn golden_vectors_match_the_offline_core() {
    let mut g: Value = serde_json::from_str(&std::fs::read_to_string(PATH).unwrap()).unwrap();
    let computed = compute(&g);
    if std::env::var_os("MINI_SDK_REGEN").is_some() {
        g["expect"] = computed;
        std::fs::write(PATH, serde_json::to_string_pretty(&g).unwrap() + "\n").unwrap();
        return;
    }
    assert_eq!(g["expect"], computed, "golden vectors drifted; regenerate only for an intended, announced format change");
}

/// External pin 1: this derivation IS Bread's (`sdk/src/profiles.rs` golden vector).
#[test]
fn bread_dregg0_vector_is_reproduced() {
    let g: Value = serde_json::from_str(&std::fs::read_to_string(PATH).unwrap()).unwrap();
    assert_eq!(compute(&g)["derive"][0], g["derive"][0]["expect"]);
}

/// External pin 2: lowering the typed intent reproduces a REAL retained `intent.json` that the
/// native Host authored and admitted (`receiving-oo-world/.../attempts/perf-pair`, confirmed
/// `installed`), so the SDK's wire is the wire, not a reconstruction of it.
#[test]
fn lowering_reproduces_a_real_admitted_intent() {
    let g: Value = serde_json::from_str(&std::fs::read_to_string(PATH).unwrap()).unwrap();
    let lowered: Value = serde_json::from_str(compute(&g)["lowering"].as_str().unwrap()).unwrap();
    assert_eq!(lowered, fixture("intent.json"));
    assert_eq!(fixture("outcome.json")["confirmation"], "installed");
}
