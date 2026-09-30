//! Records, reasons, and the byte encodings the watcher emits.
//!
//! Every 32- and 64-byte value leaves this process as lowercase hex of its RAW bytes. Base58 is
//! how Solana RPC spells them and is accepted only on input; it is never the canonical form.

use serde_json::{json, Value};

pub type Key = [u8; 32];
pub type Sig = [u8; 64];

/// Why a transfer was not emitted. `is_refusal` separates the fail-closed refusals (the run
/// exits 3 and an operator should look) from ordinary skips (nothing was paid).
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Reason {
    // refusals
    Transport,
    RpcError,
    MalformedResponse,
    WrongTokenProgram,
    WrongMint,
    WrongTokenOwner,
    BalanceEntriesDisagree,
    AccountIndexOutOfRange,
    SignatureMismatch,
    SlotMismatch,
    PrunedTransaction,
    EndpointsDisagree,
    // skips
    FailedTransaction,
    ZeroDelta,
    NetDebit,
    AlreadyRetained,
    DuplicateSignature,
    NoTokenAccount,
    PageBound,
    IgnoredReceiptName,
}

impl Reason {
    pub fn name(self) -> &'static str {
        match self {
            Reason::Transport => "transport",
            Reason::RpcError => "rpcError",
            Reason::MalformedResponse => "malformedResponse",
            Reason::WrongTokenProgram => "wrongTokenProgram",
            Reason::WrongMint => "wrongMint",
            Reason::WrongTokenOwner => "wrongTokenOwner",
            Reason::BalanceEntriesDisagree => "balanceEntriesDisagree",
            Reason::AccountIndexOutOfRange => "accountIndexOutOfRange",
            Reason::SignatureMismatch => "signatureMismatch",
            Reason::SlotMismatch => "slotMismatch",
            Reason::PrunedTransaction => "prunedTransaction",
            Reason::EndpointsDisagree => "endpointsDisagree",
            Reason::FailedTransaction => "failedTransaction",
            Reason::ZeroDelta => "zeroDelta",
            Reason::NetDebit => "netDebit",
            Reason::AlreadyRetained => "alreadyRetained",
            Reason::DuplicateSignature => "duplicateSignature",
            Reason::NoTokenAccount => "noTokenAccount",
            Reason::PageBound => "pageBound",
            Reason::IgnoredReceiptName => "ignoredReceiptName",
        }
    }

    pub fn is_refusal(self) -> bool {
        matches!(
            self,
            Reason::Transport
                | Reason::RpcError
                | Reason::MalformedResponse
                | Reason::WrongTokenProgram
                | Reason::WrongMint
                | Reason::WrongTokenOwner
                | Reason::BalanceEntriesDisagree
                | Reason::AccountIndexOutOfRange
                | Reason::SignatureMismatch
                | Reason::SlotMismatch
                | Reason::PrunedTransaction
                | Reason::EndpointsDisagree
        )
    }
}

/// A named refusal with the detail an operator needs.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Refusal {
    pub reason: Reason,
    pub detail: String,
}

impl Refusal {
    pub fn new(reason: Reason, detail: impl Into<String>) -> Self {
        Refusal {
            reason,
            detail: detail.into(),
        }
    }
    pub fn malformed(detail: impl Into<String>) -> Self {
        Refusal::new(Reason::MalformedResponse, detail)
    }
}

impl std::fmt::Display for Refusal {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}: {}", self.reason.name(), self.detail)
    }
}

/// The finalized tip the observer saw (`Clock` in PAY.md §2.4).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Clock {
    pub slot: u64,
    pub block_time: u64,
}

/// One PAY.md §2.4 `Observation`: a finalized transfer that added `amount` atomic units of
/// `mint` to token accounts owned by book `address`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Observation {
    pub index: u64,
    pub address: Key,
    pub signature: Sig,
    pub slot: u64,
    pub block_time: u64,
    pub amount: u64,
    pub mint: Key,
    pub token_program: Key,
}

impl Observation {
    pub fn to_json(&self) -> Value {
        json!({
            "index": self.index,
            "address": hex(&self.address),
            "signature": hex(&self.signature),
            "slot": self.slot,
            "blockTime": self.block_time,
            "amount": self.amount,
            "mint": hex(&self.mint),
            "tokenProgram": hex(&self.token_program),
        })
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum EventKind {
    Refused,
    Skipped,
}

/// Everything the run decided not to emit, and why.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Event {
    pub kind: EventKind,
    pub reason: Reason,
    pub index: Option<u64>,
    pub signature: Option<Sig>,
    /// Which endpoint said so; absent when every endpoint agreed on the outcome.
    pub endpoint: Option<String>,
    pub detail: String,
}

impl Event {
    pub fn of(
        reason: Reason,
        index: Option<u64>,
        signature: Option<Sig>,
        endpoint: Option<&str>,
        detail: impl Into<String>,
    ) -> Self {
        Event {
            kind: if reason.is_refusal() {
                EventKind::Refused
            } else {
                EventKind::Skipped
            },
            reason,
            index,
            signature,
            endpoint: endpoint.map(str::to_owned),
            detail: detail.into(),
        }
    }

    pub fn to_json(&self) -> Value {
        json!({
            "kind": match self.kind { EventKind::Refused => "refused", EventKind::Skipped => "skipped" },
            "reason": self.reason.name(),
            "index": self.index,
            "signature": self.signature.as_ref().map(|s| hex(s)),
            "endpoint": self.endpoint,
            "detail": self.detail,
        })
    }
}

pub fn hex(bytes: &[u8]) -> String {
    const DIGITS: &[u8; 16] = b"0123456789abcdef";
    let mut out = String::with_capacity(bytes.len() * 2);
    for b in bytes {
        out.push(DIGITS[(b >> 4) as usize] as char);
        out.push(DIGITS[(b & 15) as usize] as char);
    }
    out
}

/// Lowercase-or-uppercase hex of exactly `N` bytes.
pub fn unhex<const N: usize>(text: &str) -> Option<[u8; N]> {
    let raw = text.as_bytes();
    if raw.len() != 2 * N {
        return None;
    }
    let nibble = |c: u8| match c {
        b'0'..=b'9' => Some(c - b'0'),
        b'a'..=b'f' => Some(c - b'a' + 10),
        b'A'..=b'F' => Some(c - b'A' + 10),
        _ => None,
    };
    let mut out = [0u8; N];
    for (i, pair) in raw.chunks_exact(2).enumerate() {
        out[i] = (nibble(pair[0])? << 4) | nibble(pair[1])?;
    }
    Some(out)
}

/// Base58 of exactly `N` bytes. Base58 is a bijection between byte strings and texts, so a
/// text naming the same `N` bytes is the same text; one with an extra leading `1` names `N+1`
/// bytes and is refused here, never truncated.
pub fn unbase58<const N: usize>(text: &str) -> Option<[u8; N]> {
    let bytes = bs58::decode(text).into_vec().ok()?;
    <[u8; N]>::try_from(bytes).ok()
}

pub fn base58(bytes: &[u8]) -> String {
    bs58::encode(bytes).into_string()
}

/// A base58 32-byte key from an RPC answer, or a named malformed-response refusal.
pub fn parse_key(raw: &str, what: &str) -> Result<Key, Refusal> {
    unbase58::<32>(raw)
        .ok_or_else(|| Refusal::malformed(format!("{what} is not a 32-byte base58 key: {raw}")))
}

/// A base58 64-byte transaction signature from an RPC answer, or a named refusal.
pub fn parse_sig(raw: &str, what: &str) -> Result<Sig, Refusal> {
    unbase58::<64>(raw).ok_or_else(|| {
        Refusal::malformed(format!("{what} is not a 64-byte base58 signature: {raw}"))
    })
}
