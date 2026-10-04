//! What the member saw, and the nonce-bound confirmation that releases signatures.
//!
//! ```text
//! headers digest := SHA-256("MINI/SDK/HEADERS/v1" ‖ u32(n) ‖ (u32(len) ‖ header)…)
//! confirm digest := SHA-256("MINI/SDK/CONFIRM/v1" ‖ invocationId[32] ‖ u32(attempt)
//!                     ‖ sha256(intent.bin) ‖ sha256(plan.bin) ‖ headers digest
//!                     ‖ sha256(explanation text) ‖ nonce[16])
//! ```
use serde_json::Value;

use crate::contracts::InvocationId;
use crate::explain::{explain, Bound, Explanation};
use crate::{sha256, Error, Result};

pub const HEADERS_DOMAIN: &[u8] = b"MINI/SDK/HEADERS/v1";
pub const CONFIRM_DOMAIN: &[u8] = b"MINI/SDK/CONFIRM/v1";

pub fn headers_digest(headers: &[Vec<u8>]) -> Result<[u8; 32]> {
    let mut pre = HEADERS_DOMAIN.to_vec();
    let n: u32 = headers.len().try_into().map_err(|_| "too many headers")?;
    pre.extend_from_slice(&n.to_le_bytes());
    for h in headers {
        let len: u32 = h.len().try_into().map_err(|_| "header too long")?;
        pre.extend_from_slice(&len.to_le_bytes());
        pre.extend_from_slice(h);
    }
    Ok(sha256(&pre))
}

/// Everything a signature would be over, as the member's own consent process returned it,
/// with the reading rendered from the member's own Host presentations.
#[derive(Debug, Clone)]
pub struct Presented {
    pub invocation: InvocationId,
    pub attempt: u32,
    pub intent_bin: Vec<u8>,
    pub plan_bin: Vec<u8>,
    /// The ordered headers consent op 222 returned for exactly (intent_bin, plan_bin). These,
    /// and only these, are what a key signs.
    pub headers: Vec<Vec<u8>>,
    pub explanation: Explanation,
}

impl Presented {
    /// Bind the reading to the bytes. `intent_json` is the retained authoring JSON the Host
    /// authored `intent_bin` from; `plan_json` is the local Host's `inspect plan` of `plan_bin`.
    pub fn new(invocation: InvocationId, attempt: u32, intent_json: &Value, intent_bin: Vec<u8>,
        plan_json: &Value, plan_bin: Vec<u8>, headers: Vec<Vec<u8>>) -> Result<Self> {
        if headers.is_empty() {
            return Err("consent returned no headers; nothing to sign".into());
        }
        let bound = Bound { intent_sha256: sha256(&intent_bin), plan_sha256: sha256(&plan_bin),
            headers_sha256: headers_digest(&headers)? };
        let explanation = explain(intent_json, plan_json, &bound);
        Ok(Presented { invocation, attempt, intent_bin, plan_bin, headers, explanation })
    }

    pub fn digest(&self, nonce: &[u8; 16]) -> Result<[u8; 32]> {
        confirm_digest(&self.invocation, self.attempt, &sha256(&self.intent_bin), &sha256(&self.plan_bin),
            &headers_digest(&self.headers)?, &sha256(self.explanation.text.as_bytes()), nonce)
    }

    /// The member accepted this reading under a fresh one-shot `nonce` (from the UI that showed
    /// it). The returned confirmation releases signatures for exactly this presentation.
    pub fn confirm(&self, nonce: [u8; 16]) -> Result<Confirmation> {
        Ok(Confirmation { digest: self.digest(&nonce)?, nonce })
    }
}

pub fn confirm_digest(invocation: &InvocationId, attempt: u32, intent_sha: &[u8; 32], plan_sha: &[u8; 32],
    headers_sha: &[u8; 32], explanation_sha: &[u8; 32], nonce: &[u8; 16]) -> Result<[u8; 32]> {
    let mut pre = CONFIRM_DOMAIN.to_vec();
    pre.extend_from_slice(&invocation.0);
    pre.extend_from_slice(&attempt.to_le_bytes());
    for d in [intent_sha, plan_sha, headers_sha, explanation_sha] {
        pre.extend_from_slice(d);
    }
    pre.extend_from_slice(nonce);
    Ok(sha256(&pre))
}

/// A member's acceptance of one exact presentation.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Confirmation {
    pub digest: [u8; 32],
    pub nonce: [u8; 16],
}

impl Confirmation {
    pub fn check(&self, presented: &Presented) -> Result<()> {
        if presented.digest(&self.nonce)? != self.digest {
            return Err(Error("confirmation is for a different presentation; nothing signed".into()));
        }
        Ok(())
    }
}
