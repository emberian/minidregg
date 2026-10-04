//! The SDK's intent encoder against LEAN, live: every row of `golden/intents.json` is sent to the
//! exported `minidregg_intent_encode` / `minidregg_intent_id_preimage` of the Lean archive
//! `libminidregg-intents.so` (`lean-codec/build.sh`), and this crate must give the same bytes, the same
//! `InvocationId` preimage and the same refusals. `golden.rs` holds the crate to Lean's PRINTED
//! vectors; this holds it to Lean's CODE, and checks the printed vectors were not stale.
//!
//! Run (the library path is required; with the feature on and no library the test FAILS, it does
//! not skip):
//!   MINI_SDK_LEAN_CODEC_LIB=/path/libminidregg-intents.so cargo test --features lean-codec --test lean_codec
//! The same test plants a one-bit difference in this crate's side and requires the comparison to go red.
#![cfg(feature = "lean-codec")]
use mini_sdk::contracts::{spelling, INTENT_ID_FRAME};
use mini_sdk::lean_codec::{Answer, LeanCodec};
use serde_json::Value;

fn read(name: &str) -> Value {
    serde_json::from_str(&std::fs::read_to_string(format!("{}/golden/{name}", env!("CARGO_MANIFEST_DIR"))).unwrap()).unwrap()
}

fn lean() -> LeanCodec {
    let lib = std::env::var("MINI_SDK_LEAN_CODEC_LIB")
        .expect("MINI_SDK_LEAN_CODEC_LIB must name libminidregg-intents.so (native/mini-sdk/lean-codec/build.sh)");
    LeanCodec::load(std::path::Path::new(&lib)).unwrap()
}

/// This crate's answers on one spelling, in Lean's shape.
fn ours(text: &str) -> Result<(Vec<u8>, Vec<u8>), String> {
    let v: Value = serde_json::from_str(text).map_err(|e| e.to_string())?;
    let intent = spelling::intent(&v).map_err(|e| e.0)?;
    Ok((intent.canonical_bytes().map_err(|e| e.0)?, intent.id_preimage().map_err(|e| e.0)?))
}

fn compare(lean: &LeanCodec, mutate: bool) -> (usize, usize) {
    let inputs = read("intents.json");
    let printed = read("lean-intents.json");
    let printed = printed["vectors"].as_array().unwrap();
    let (mut admitted, mut refused) = (0, 0);
    for (i, row) in inputs.as_array().unwrap().iter().enumerate() {
        let (name, text) = (row["name"].as_str().unwrap(), row["text"].as_str().unwrap());
        let live_bytes = lean.encode(text).unwrap();
        let live_pre = lean.id_preimage(text).unwrap();
        // The printed vector file is Lean's output on this exact text: it must equal Lean's code now.
        assert_eq!(printed[i]["text"], row["text"], "{name}: lean-intents.json is stale");
        match (&live_bytes, &live_pre) {
            (Answer::Bytes(bytes), Answer::Bytes(pre)) => {
                assert_eq!(printed[i]["result"], "ok", "{name}: Lean admits it, the printed vector says refused");
                assert_eq!(hex(bytes), printed[i]["bytes"].as_str().unwrap(), "{name}: printed bytes differ from Lean's code");
                assert_eq!(&[INTENT_ID_FRAME, bytes.as_slice()].concat(), pre, "{name}: preimage is not frame ‖ bytes");
                let (mut b, p) = ours(text).unwrap_or_else(|e| panic!("{name}: Lean admits it, this crate refuses: {e}"));
                if mutate {
                    b[0] ^= 1;
                }
                assert_eq!(&b, bytes, "{name}: canonical bytes differ from Lean's export");
                assert_eq!(&p, pre, "{name}: id preimage differs from Lean's export");
                admitted += 1;
            }
            (Answer::Refused(why), Answer::Refused(_)) => {
                assert_eq!(printed[i]["result"], "refused", "{name}: Lean refuses ({why}), the printed vector says ok");
                assert!(ours(text).is_err(), "{name}: Lean refuses ({why}), this crate admits it");
                refused += 1;
            }
            other => panic!("{name}: Lean's two entry points disagree: {other:?}"),
        }
    }
    (admitted, refused)
}

fn hex(b: &[u8]) -> String {
    mini_sdk::hex::encode(b)
}

/// One test, one initialisation: the Lean runtime initialises once per process and every call is
/// on the loading thread.
#[test]
fn the_sdk_encoder_equals_leans_exported_codec_on_every_golden_row() {
    let lean = lean();
    let (admitted, refused) = compare(&lean, false);
    assert!(admitted >= 25 && refused >= 25, "the vector set lost its teeth: {admitted} admitted, {refused} refused");
    eprintln!("lean-codec: {admitted} admitted rows and {refused} refusals agree with minidregg_intent_encode");

    // The check can go red: an encoder whose first byte is flipped is caught by the same comparison.
    let hook = std::panic::take_hook();
    std::panic::set_hook(Box::new(|_| {})); // the planted failure's byte dump is not evidence
    let planted = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| compare(&lean, true)));
    std::panic::set_hook(hook);
    let message = *planted.expect_err("a planted one-bit difference was not caught").downcast::<String>().unwrap();
    assert!(message.contains("canonical bytes differ from Lean's export"), "{message}");

    // Lean refuses what is not an intent spelling.
    assert!(matches!(lean.encode("{"), Ok(Answer::Refused(_))));
    assert!(matches!(lean.id_preimage("{}"), Ok(Answer::Refused(_))));
}
