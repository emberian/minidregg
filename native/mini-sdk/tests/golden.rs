//! Golden vectors. `golden/vectors.json` holds hand-written inputs and the offline core's
//! outputs under `"expect"` (`MINI_SDK_REGEN=1` rewrites `"expect"`; otherwise every value must
//! match). Intent bytes are not in it: they are LEAN's. `golden/intents.json` holds the intent
//! inputs and `golden/lean-intents.json` the bytes (or refusals) that
//! `Kernel/Contracts/IntentVectors.lean` printed by running its exported entry points over them;
//! [`lean_vectors_are_reproduced_byte_for_byte`] requires this crate's single encoder to equal
//! Lean's on every admitted row and to refuse every refused row. The TS SDK checks the same
//! files through the wasm build of this crate.
use mini_sdk::contracts::{canonical_json, spelling};
use mini_sdk::explain::{explain, Bound};
use mini_sdk::signer::{verify, Scheme};
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
    let low = &g["lowering"];
    let rows = read("intents.json");
    let row = rows.as_array().unwrap().iter().find(|r| r["name"] == low["intent"]).unwrap();
    let intent: Value = serde_json::from_str(row["text"].as_str().unwrap()).unwrap();
    let lowered = spelling::intent(&intent).unwrap().lower(&spelling::lowering(&low["context"]).unwrap()).unwrap();
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
    // The signer schemes: Ed25519 and the Ed25519 + ML-DSA-65 hybrid, from the profile seed.
    let signers = &g["signers"];
    let profile = mini_sdk::Profile::from_seed("golden", seed).unwrap();
    let generation = signers["generation"].as_u64().unwrap() as u32;
    let message = hex::decode(signers["message"].as_str().unwrap()).unwrap();
    let mut sg = Map::new();
    for (name, scheme) in [("ed25519", Scheme::Ed25519), ("hybrid", Scheme::HybridEd25519MlDsa65)] {
        let signer = profile.mini_signer(generation, scheme);
        let (pk, sig) = (signer.public_key(), signer.sign(&message).unwrap());
        verify(scheme, &pk, &message, &sig).unwrap();
        sg.insert(name.into(), json!({"publicKey": hex::encode(&pk[..32]), "publicKeySha256": hex::encode(&sha256(&pk)),
            "signatureEd": hex::encode(&sig[..64]), "signatureSha256": hex::encode(&sha256(&sig)),
            "publicKeyLen": pk.len(), "signatureLen": sig.len()}));
    }
    out.insert("signers".into(), Value::Object(sg));
    Value::Object(out)
}

fn read(name: &str) -> Value {
    serde_json::from_str(&std::fs::read_to_string(format!("{}/golden/{name}", env!("CARGO_MANIFEST_DIR"))).unwrap_or_else(|e| panic!("{name}: {e}"))).unwrap()
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

/// The pin that makes Lean the source of truth: every row of `lean-intents.json` (emitted by
/// Lean running the exported `minidregg_intent_encode` / `minidregg_intent_id_preimage` entry
/// points on the row's exact SOURCE TEXT) is reproduced by this crate's encoder, byte for byte,
/// and every row Lean refused is refused here. The echoed text must equal `intents.json` byte for
/// byte (a stale vector file fails), and Lean's rows must cover every input.
#[test]
fn lean_vectors_are_reproduced_byte_for_byte() {
    let inputs = read("intents.json");
    let lean = read("lean-intents.json");
    let rows = lean["vectors"].as_array().expect("lean-intents.json has no vectors; regenerate it with Lean");
    let inputs = inputs.as_array().unwrap();
    assert_eq!(rows.len(), inputs.len(), "lean-intents.json does not cover intents.json; re-emit it");
    let (mut admitted, mut refused) = (0, 0);
    for (row, input) in rows.iter().zip(inputs) {
        let name = row["name"].as_str().unwrap();
        assert_eq!(row["name"], input["name"], "{name}: row order drifted");
        assert_eq!(row["text"], input["text"], "{name}: lean-intents.json was emitted from a different input; re-emit it");
        let ours = serde_json::from_str::<Value>(row["text"].as_str().unwrap())
            .map_err(|e| mini_sdk::Error(e.to_string()))
            .and_then(|v| spelling::intent(&v))
            .and_then(|i| Ok((i.canonical_bytes()?, i.id_preimage()?)));
        match row["result"].as_str().unwrap() {
            "ok" => {
                let (bytes, pre) = ours.unwrap_or_else(|e| panic!("{name}: Lean admits it, this crate refuses: {e}"));
                assert_eq!(hex::encode(&bytes), row["bytes"].as_str().unwrap(), "{name}: canonical bytes");
                assert_eq!(hex::encode(&pre), row["idPreimage"].as_str().unwrap(), "{name}: id preimage");
                admitted += 1;
            }
            "refused" => {
                assert!(ours.is_err(), "{name}: Lean refuses ({}), this crate admits it", row["reason"]);
                refused += 1;
            }
            other => panic!("{name}: unknown result {other}"),
        }
    }
    assert!(admitted >= 25 && refused >= 25, "the vector set lost its teeth: {admitted} admitted, {refused} refused");
}
