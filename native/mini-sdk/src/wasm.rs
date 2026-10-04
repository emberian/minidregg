//! wasm-bindgen exports of the offline core. The TS SDK (`native/mini-sdk-ts`) reaches the
//! intent encoder, the canonical JSON, the lowering and the hybrid ML-DSA-65 scheme ONLY through
//! this module (one implementation), and is differentially tested against it for the pieces it
//! still carries natively (derivation, Ed25519, explain, digests). Strings in, strings out;
//! every refusal is a thrown string.
use serde_json::Value;
use wasm_bindgen::prelude::*;

use crate::contracts::{canonical_json, spelling};
use crate::explain::{explain, Bound};
use crate::signer::{verify, Scheme};
use crate::{hex, profile, Error, Profile};

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

/// The bytes hashed into the `InvocationId` (`intentIdPreimage` in Lean), hex.
#[wasm_bindgen(js_name = intentIdPreimage)]
pub fn intent_id_preimage(intent: &str) -> Result<String, JsValue> {
    Ok(hex::encode(&spelling::intent(&parse(intent)?).map_err(js)?.id_preimage().map_err(js)?))
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

fn scheme(code: u8) -> Result<Scheme, JsValue> {
    Scheme::from_code(code).map_err(js)
}
fn profile_seed(seed_hex: &str) -> Result<[u8; 64], JsValue> {
    hex::decode(seed_hex).map_err(js)?.try_into().map_err(|_| JsValue::from_str("seed must be 64 bytes"))
}

/// The public key of the profile's Mini signer (`scheme` 1 = Ed25519, 2 = hybrid), hex.
#[wasm_bindgen(js_name = signerPublic)]
pub fn signer_public(seed_hex: &str, generation: u32, scheme_code: u8) -> Result<String, JsValue> {
    let p = Profile::from_seed("wasm", profile_seed(seed_hex)?).map_err(js)?;
    Ok(hex::encode(&p.mini_signer(generation, scheme(scheme_code)?).public_key()))
}

/// A signature over `message` by the profile's Mini signer, hex.
#[wasm_bindgen(js_name = signerSign)]
pub fn signer_sign(seed_hex: &str, generation: u32, scheme_code: u8, message_hex: &str) -> Result<String, JsValue> {
    let p = Profile::from_seed("wasm", profile_seed(seed_hex)?).map_err(js)?;
    let sig = p.mini_signer(generation, scheme(scheme_code)?).sign(&hex::decode(message_hex).map_err(js)?).map_err(js)?;
    Ok(hex::encode(&sig))
}

/// Verify a signature in the scheme's wire layout; a thrown string names the failing half.
#[wasm_bindgen(js_name = signerVerify)]
pub fn signer_verify(scheme_code: u8, public_hex: &str, message_hex: &str, signature_hex: &str) -> Result<(), JsValue> {
    verify(scheme(scheme_code)?, &hex::decode(public_hex).map_err(js)?, &hex::decode(message_hex).map_err(js)?,
        &hex::decode(signature_hex).map_err(js)?).map_err(js)
}
