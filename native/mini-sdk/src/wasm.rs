//! wasm-bindgen exports of the offline core: the oracle the TS SDK is differentially tested
//! against (`native/mini-sdk-ts/test/differential.test.ts`). Strings in, strings out; every
//! refusal is a thrown string.
use serde_json::Value;
use wasm_bindgen::prelude::*;

use crate::contracts::{canonical_json, spelling};
use crate::explain::{explain, Bound};
use crate::{hex, profile, Error};

fn js(e: Error) -> JsValue {
    JsValue::from_str(&e.0)
}
fn parse(text: &str) -> Result<Value, JsValue> {
    serde_json::from_str(text).map_err(|e| JsValue::from_str(&e.to_string()))
}
fn h32(text: &str) -> Result<[u8; 32], JsValue> {
    hex::decode(text).map_err(js)?.try_into().map_err(|_| JsValue::from_str("expected 32 bytes"))
}

#[wasm_bindgen(js_name = derivePublic)]
pub fn derive_public(seed_hex: &str, path: &str) -> Result<String, JsValue> {
    let seed: [u8; 64] = hex::decode(seed_hex).map_err(js)?.try_into().map_err(|_| JsValue::from_str("seed must be 64 bytes"))?;
    Ok(hex::encode(profile::derive(&seed, path).verifying_key().as_bytes()))
}

#[wasm_bindgen(js_name = signRaw)]
pub fn sign_raw(seed_hex: &str, path: &str, message_hex: &str) -> Result<String, JsValue> {
    use ed25519_dalek::Signer;
    let seed: [u8; 64] = hex::decode(seed_hex).map_err(js)?.try_into().map_err(|_| JsValue::from_str("seed must be 64 bytes"))?;
    let msg = hex::decode(message_hex).map_err(js)?;
    Ok(hex::encode(&profile::derive(&seed, path).sign(&msg).to_bytes()))
}

#[wasm_bindgen(js_name = canonicalJson)]
pub fn canonical_json_js(json: &str) -> Result<String, JsValue> {
    canonical_json(&parse(json)?).map_err(js)
}

#[wasm_bindgen(js_name = intentBytes)]
pub fn intent_bytes(intent: &str) -> Result<String, JsValue> {
    Ok(hex::encode(&spelling::intent(&parse(intent)?).map_err(js)?.canonical_bytes().map_err(js)?))
}

#[wasm_bindgen(js_name = invocationId)]
pub fn invocation_id(intent: &str) -> Result<String, JsValue> {
    Ok(spelling::intent(&parse(intent)?).map_err(js)?.invocation_id().map_err(js)?.hex())
}

#[wasm_bindgen(js_name = lowerIntent)]
pub fn lower_intent(intent: &str, lowering: &str) -> Result<String, JsValue> {
    let i = spelling::intent(&parse(intent)?).map_err(js)?;
    canonical_json(&i.lower(&spelling::lowering(&parse(lowering)?).map_err(js)?).map_err(js)?).map_err(js)
}

#[wasm_bindgen(js_name = headersDigest)]
pub fn headers_digest(headers_json: &str) -> Result<String, JsValue> {
    let list = parse(headers_json)?;
    let headers = list.as_array().ok_or_else(|| JsValue::from_str("expected a list"))?
        .iter().map(|h| hex::decode(h.as_str().unwrap_or("?")).map_err(js)).collect::<Result<Vec<_>, _>>()?;
    Ok(hex::encode(&crate::confirm::headers_digest(&headers).map_err(js)?))
}

#[wasm_bindgen(js_name = explainText)]
pub fn explain_text(intent_json: &str, plan_json: &str, intent_sha: &str, plan_sha: &str, headers_sha: &str) -> Result<String, JsValue> {
    let bound = Bound { intent_sha256: h32(intent_sha)?, plan_sha256: h32(plan_sha)?, headers_sha256: h32(headers_sha)? };
    Ok(explain(&parse(intent_json)?, &parse(plan_json)?, &bound).text)
}

#[wasm_bindgen(js_name = confirmDigest)]
pub fn confirm_digest(invocation: &str, attempt: u32, intent_sha: &str, plan_sha: &str, headers_sha: &str,
    explanation_sha: &str, nonce_hex: &str) -> Result<String, JsValue> {
    let nonce: [u8; 16] = hex::decode(nonce_hex).map_err(js)?.try_into().map_err(|_| JsValue::from_str("nonce must be 16 bytes"))?;
    let d = crate::confirm::confirm_digest(&crate::contracts::InvocationId(h32(invocation)?), attempt, &h32(intent_sha)?,
        &h32(plan_sha)?, &h32(headers_sha)?, &h32(explanation_sha)?, &nonce).map_err(js)?;
    Ok(hex::encode(&d))
}
