//! Enrolment memos (PAY.md §11): the SPL Memo bytes carried by a payment to the ENROLLMENT
//! index, reported to the kernel verbatim.
//!
//! The watcher does not parse the memo. PAY.md §11.3/§11.4: the kernel's
//! `PayEnrollmentReceiver` parses it, verifies both signatures, and journals every refusal. A
//! Rust reading of the grammar here would be a second parser that agrees with Lean's today and
//! not tomorrow. The watcher decides only chain facts: how many memo instructions the
//! transaction carried, and whether the one memo is UTF-8 within `MEMO_MAX` ([`bind`]).
//!
//! Extraction reads the `jsonParsed` transaction: every instruction whose `programId` is SPL Memo
//! v2 (`MemoSq4…`) or the legacy v1 program (`Memo1Uhk…`), top-level and inner (CPI), in
//! execution order: top-level instruction `i`, then the inner instructions recorded under
//! `index: i`, then `i + 1`. A memo the RPC parsed arrives as `parsed: "<text>"` (its UTF-8
//! bytes are the memo); one it could not parse arrives as `data: <base58>` and is decoded here.

use serde_json::Value;

use crate::model::{MemoError, Refusal};

/// The most memo bytes an enrollment observation carries (PAY.md §11.9: the room left in a
/// one-transfer transaction). A longer memo is `memoInvalid`.
pub const MEMO_MAX: usize = 566;

/// The memo an enrollment observation carries, from ALL the transaction's memo instructions:
/// none → `(None, None)`; exactly one, UTF-8 and within `MEMO_MAX` → its bytes; one otherwise →
/// `memoInvalid`; two or more → `memoUnbound`.
pub fn bind(memos: &[Vec<u8>]) -> (Option<Vec<u8>>, Option<MemoError>) {
    match memos {
        [] => (None, None),
        [one] if one.len() <= MEMO_MAX && std::str::from_utf8(one).is_ok() => (Some(one.clone()), None),
        [_] => (None, Some(MemoError::Invalid)),
        _ => (None, Some(MemoError::Unbound)),
    }
}

/// SPL Memo v2 and the legacy v1 program. Both are parsed by the RPC as `spl-memo`.
pub const MEMO_PROGRAMS: [&str; 2] = [
    "MemoSq4gqABAXKb96qnH8TysNcWxMyWCqXgDLGmfcHr",
    "Memo1UhkJRfHyvLMcVucJwxXeuD728EqVDDwQDxFMNo",
];

/// Every SPL Memo instruction's bytes, in execution order. Empty = the transaction carries no
/// memo (the kernel's `memoMissing`); more than one is the kernel's `memoUnbound`.
pub fn memos(result: &Value) -> Result<Vec<Vec<u8>>, Refusal> {
    let top = result
        .pointer("/transaction/message/instructions")
        .and_then(Value::as_array)
        .ok_or_else(|| {
            Refusal::malformed("getTransaction missing `transaction.message.instructions`")
        })?;
    let mut inner: Vec<(u64, &Vec<Value>)> = Vec::new();
    if let Some(list) = result.pointer("/meta/innerInstructions").filter(|v| !v.is_null()) {
        for group in list
            .as_array()
            .ok_or_else(|| Refusal::malformed("meta.innerInstructions not an array"))?
        {
            let index = group
                .get("index")
                .and_then(Value::as_u64)
                .ok_or_else(|| Refusal::malformed("innerInstructions entry missing `index`"))?;
            if index as usize >= top.len() {
                return Err(Refusal::malformed(format!(
                    "innerInstructions index {index} past {} top-level instructions",
                    top.len()
                )));
            }
            if inner.iter().any(|(i, _)| *i == index) {
                return Err(Refusal::malformed(format!(
                    "innerInstructions lists index {index} twice"
                )));
            }
            let ixs = group
                .get("instructions")
                .and_then(Value::as_array)
                .ok_or_else(|| Refusal::malformed("innerInstructions entry missing `instructions`"))?;
            inner.push((index, ixs));
        }
    }
    let mut out = Vec::new();
    for (i, ix) in top.iter().enumerate() {
        out.extend(memo_of(ix)?);
        if let Some((_, ixs)) = inner.iter().find(|(k, _)| *k == i as u64) {
            for ix in ixs.iter() {
                out.extend(memo_of(ix)?);
            }
        }
    }
    Ok(out)
}

/// One instruction's memo bytes, if it is a memo instruction.
fn memo_of(ix: &Value) -> Result<Option<Vec<u8>>, Refusal> {
    let program = ix
        .get("programId")
        .and_then(Value::as_str)
        .ok_or_else(|| Refusal::malformed("instruction missing `programId` (not jsonParsed?)"))?;
    if !MEMO_PROGRAMS.contains(&program) {
        return Ok(None);
    }
    match (ix.get("parsed"), ix.get("data")) {
        (Some(Value::String(text)), None) => Ok(Some(text.as_bytes().to_vec())),
        (None, Some(Value::String(data))) => bs58::decode(data)
            .into_vec()
            .map(Some)
            .map_err(|_| Refusal::malformed("memo instruction `data` is not base58")),
        _ => Err(Refusal::malformed(
            "memo instruction has neither a string `parsed` nor a base58 `data`",
        )),
    }
}

/// A memo for a log line: its text as a JSON string when it is UTF-8, else `hex:<bytes>`.
pub fn describe(memo: &[u8]) -> String {
    match std::str::from_utf8(memo) {
        Ok(text) => Value::String(text.to_owned()).to_string(),
        Err(_) => format!("hex:{}", crate::model::hex(memo)),
    }
}
