//! Decoding the three RPC answers. Ported from Bread's `discord-bot/src/pay.rs`
//! (`token_account_pubkey`, `signatures_of`, `credited_amount`, `token_balance_at`,
//! `account_keys`) with these changes, each a refusal where Bread was silent:
//!
//! * the token program is `asset.token_program` (Bread passed the legacy constant);
//! * an attribution mismatch on the watched account's POST entry is a named refusal
//!   (Bread returned `Ok(None)`, "added nothing", which is how Token-2022 credited nothing);
//! * the account list is every token account the owner holds for the mint, each attributed
//!   (Bread took `value.first()`, whose order is the RPC's choice);
//! * every balance entry's `accountIndex` is range-checked and an account may appear once
//!   (Bread returned at the first match and checked nothing after it);
//! * PRE and POST must agree on program as well as mint and owner;
//! * the returned transaction must carry the requested signature and the listed slot, and a
//!   signature-list entry must have a slot (Bread defaulted a missing slot to 0).

use serde_json::Value;

use crate::config::Asset;
use crate::model::{parse_key, parse_sig, Key, Reason, Refusal, Sig};

/// Highest transaction format decoded below; also used by RPC and fixture requests.
/// Verified 2026-10-02 against https://solana.com/docs/rpc/json-structures
/// and https://solana.com/upgrades/larger-transaction-sizes.
pub const MAX_SUPPORTED_TRANSACTION_VERSION: u64 = 1;

/// Validate the version-dependent JSON shape before trusting any chain facts.
/// The official RPC schema gives v1 a four-field transactionConfig, omits
/// addressTableLookups, and says v1 has no lookup tables. Resource settings are
/// checked structurally, never interpreted as payment or compute-price semantics.
///
/// An omitted version remains accepted for old legacy captures: the RPC schema
/// documents undefined version information, and our historical fixtures use it.
/// It cannot carry the v1 config marker. Explicit null/unknown versions refuse.
fn transaction_version(result: &Value) -> Result<(), Refusal> {
    let version = match result.get("version") {
        None => None,
        Some(Value::String(name)) if name == "legacy" => None,
        Some(Value::Number(number)) => Some(number.as_u64()
            .filter(|n| *n <= MAX_SUPPORTED_TRANSACTION_VERSION)
            .ok_or_else(|| Refusal::malformed("unsupported transaction version"))?),
        _ => return Err(Refusal::malformed("unsupported transaction version")),
    };
    let message = result.pointer("/transaction/message")
        .and_then(Value::as_object)
        .ok_or_else(|| Refusal::malformed("transaction message is not an object"))?;
    if version != Some(1) {
        if message.contains_key("transactionConfig") {
            return Err(Refusal::malformed("transactionConfig is only valid for v1"));
        }
        return Ok(());
    }
    let config = message.get("transactionConfig").and_then(Value::as_object)
        .ok_or_else(|| Refusal::malformed("v1 transactionConfig must be an object"))?;
    let fields = ["computeUnitLimit", "heapSize", "loadedAccountsDataSizeLimit", "priorityFee"];
    if config.len() != fields.len() || fields.iter().any(|field|
        !config.get(*field).is_some_and(|value| value.is_null() || value.as_u64().is_some())) {
        return Err(Refusal::malformed("v1 transactionConfig requires four nullable integer fields"));
    }
    if message.contains_key("addressTableLookups") {
        return Err(Refusal::malformed("v1 omits addressTableLookups"));
    }
    // jsonParsed includes resolved keys directly; v1 has only transaction keys.
    let keys = message.get("accountKeys").and_then(Value::as_array)
        .ok_or_else(|| Refusal::malformed("v1 accountKeys must be a parsed array"))?;
    if keys.iter().any(|key| key.get("source").and_then(Value::as_str) != Some("transaction")) {
        return Err(Refusal::malformed("v1 account key must come from the transaction"));
    }
    // Some older fixture/providers retain the empty metadata object. Accept
    // those empty lists, but never append lookup addresses to a v1 key list.
    if let Some(loaded) = result.pointer("/meta/loadedAddresses").filter(|v| !v.is_null()) {
        let object = loaded.as_object()
            .ok_or_else(|| Refusal::malformed("v1 loadedAddresses must be absent or empty"))?;
        if object.len() != 2 || ["writable","readonly"].iter().any(|field|
            !object.get(*field).and_then(Value::as_array).is_some_and(Vec::is_empty)) {
            return Err(Refusal::malformed("v1 cannot contain loaded addresses"));
        }
    }
    Ok(())
}

fn wrong(reason: Reason, what: &str, got: &Key, want: &Key) -> Refusal {
    Refusal::new(
        reason,
        format!(
            "{what}: got {}, configured {}",
            crate::model::base58(got),
            crate::model::base58(want)
        ),
    )
}

/// `getTokenAccountsByOwner` (`jsonParsed`) → the owner's token accounts for the mint, sorted
/// by pubkey. Empty = nothing has ever landed; not an error. Each entry must be owned by the
/// asset's token program and parse to the asset's mint and the book address.
pub fn token_accounts(result: &Value, asset: &Asset, owner: &Key) -> Result<Vec<Key>, Refusal> {
    let value = result
        .get("value")
        .and_then(Value::as_array)
        .ok_or_else(|| Refusal::malformed("getTokenAccountsByOwner missing `value` array"))?;
    let mut out = Vec::with_capacity(value.len());
    for entry in value {
        let pubkey = parse_key(
            entry
                .get("pubkey")
                .and_then(Value::as_str)
                .ok_or_else(|| Refusal::malformed("token account entry missing `pubkey`"))?,
            "token account `pubkey`",
        )?;
        let program = parse_key(
            entry
                .pointer("/account/owner")
                .and_then(Value::as_str)
                .ok_or_else(|| Refusal::malformed("token account entry missing `account.owner`"))?,
            "token account `account.owner`",
        )?;
        if program != asset.token_program {
            return Err(wrong(
                Reason::WrongTokenProgram,
                "token account owner program",
                &program,
                &asset.token_program,
            ));
        }
        let info = entry.pointer("/account/data/parsed/info").ok_or_else(|| {
            Refusal::malformed("token account entry not jsonParsed (`account.data.parsed.info`)")
        })?;
        let mint = parse_key(
            info.get("mint")
                .and_then(Value::as_str)
                .ok_or_else(|| Refusal::malformed("token account info missing `mint`"))?,
            "token account `mint`",
        )?;
        if mint != asset.mint {
            return Err(wrong(Reason::WrongMint, "token account mint", &mint, &asset.mint));
        }
        let holder = parse_key(
            info.get("owner")
                .and_then(Value::as_str)
                .ok_or_else(|| Refusal::malformed("token account info missing `owner`"))?,
            "token account `owner`",
        )?;
        if &holder != owner {
            return Err(wrong(Reason::WrongTokenOwner, "token account owner", &holder, owner));
        }
        out.push(pubkey);
    }
    out.sort();
    let before = out.len();
    out.dedup();
    if out.len() != before {
        return Err(Refusal::malformed("getTokenAccountsByOwner lists an account twice"));
    }
    Ok(out)
}

/// One `getSignaturesForAddress` entry.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SigEntry {
    pub signature: Sig,
    pub slot: u64,
    /// `err` non-null: the transaction failed and moved nothing.
    pub failed: bool,
}

/// `getSignaturesForAddress` → entries, newest first, INCLUDING failed ones (the caller skips
/// them, but still needs them to page with `before`). A missing signature or slot is malformed.
pub fn signatures_of(result: &Value) -> Result<Vec<SigEntry>, Refusal> {
    let value = result
        .as_array()
        .ok_or_else(|| Refusal::malformed("getSignaturesForAddress `result` not an array"))?;
    let mut out = Vec::with_capacity(value.len());
    for entry in value {
        let failed = !matches!(entry.get("err"), None | Some(Value::Null));
        let signature = parse_sig(
            entry
                .get("signature")
                .and_then(Value::as_str)
                .ok_or_else(|| Refusal::malformed("signature entry missing `signature`"))?,
            "signature entry",
        )?;
        let slot = entry
            .get("slot")
            .and_then(Value::as_u64)
            .ok_or_else(|| Refusal::malformed("signature entry missing `slot`"))?;
        if let Some(status) = entry.get("confirmationStatus") {
            if status.as_str() != Some("finalized") {
                return Err(Refusal::malformed(format!(
                    "signature entry at finalized commitment reports confirmationStatus {status}"
                )));
            }
        }
        out.push(SigEntry {
            signature,
            slot,
            failed,
        });
    }
    Ok(out)
}

/// What one `getTransaction` answer says about the watched accounts.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TxOutcome {
    /// `result: null`: the endpoint no longer (or not yet) serves this transaction.
    Pruned,
    /// `meta.err` non-null.
    Failed,
    /// Landed; `delta` = Σ over the watched accounts of (post − pre).
    Landed { slot: u64, block_time: u64, delta: i128 },
}

/// `getTransaction` (`jsonParsed`) → the net amount this transaction added to the watched
/// token accounts of `owner`. `list_slot` is the slot `getSignaturesForAddress` reported.
pub fn transaction_credit(
    result: &Value,
    signature: &Sig,
    list_slot: u64,
    accounts: &[Key],
    asset: &Asset,
    owner: &Key,
) -> Result<TxOutcome, Refusal> {
    if result.is_null() {
        return Ok(TxOutcome::Pruned);
    }
    transaction_version(result)?;
    let first = result
        .pointer("/transaction/signatures/0")
        .and_then(Value::as_str)
        .ok_or_else(|| Refusal::malformed("getTransaction missing `transaction.signatures[0]`"))?;
    if &parse_sig(first, "transaction signature")? != signature {
        return Err(Refusal::new(
            Reason::SignatureMismatch,
            format!("asked for one transaction, got {first}"),
        ));
    }
    let slot = result
        .get("slot")
        .and_then(Value::as_u64)
        .ok_or_else(|| Refusal::malformed("getTransaction missing `slot`"))?;
    if slot != list_slot {
        return Err(Refusal::new(
            Reason::SlotMismatch,
            format!("signature list says slot {list_slot}, transaction says {slot}"),
        ));
    }
    let meta = result
        .get("meta")
        .ok_or_else(|| Refusal::malformed("getTransaction result missing `meta`"))?;
    if !matches!(meta.get("err"), None | Some(Value::Null)) {
        return Ok(TxOutcome::Failed);
    }
    let block_time = result
        .get("blockTime")
        .and_then(Value::as_u64)
        .ok_or_else(|| Refusal::malformed("getTransaction missing `blockTime`"))?;
    let keys = account_keys(result)?;
    let pre = balances(meta.get("preTokenBalances"), &keys, "preTokenBalances")?;
    let post = balances(meta.get("postTokenBalances"), &keys, "postTokenBalances")?;
    let mut delta: i128 = 0;
    for account in accounts {
        delta += account_delta(account, &keys, &pre, &post, asset, owner)?;
    }
    Ok(TxOutcome::Landed {
        slot,
        block_time,
        delta,
    })
}

/// `credited_amount` for one watched account, signed.
fn account_delta(
    account: &Key,
    keys: &[Key],
    pre: &[(usize, TokenBalanceEntry)],
    post: &[(usize, TokenBalanceEntry)],
    asset: &Asset,
    owner: &Key,
) -> Result<i128, Refusal> {
    // Not in this transaction's key list: no entry can be ours.
    let Some(index) = keys.iter().position(|k| k == account) else {
        return Ok(0);
    };
    let at = |list: &[(usize, TokenBalanceEntry)]| {
        list.iter().find(|(i, _)| *i == index).map(|(_, e)| e.clone())
    };
    // Absent from POST: the account received nothing here (a closed token account held 0).
    let Some(post) = at(post) else {
        return Ok(0);
    };
    // Attribution on the POST entry, the one whose amount we are about to believe, in
    // `SignatureWatcher::poll`'s order.
    if post.program_id != asset.token_program {
        return Err(wrong(
            Reason::WrongTokenProgram,
            "POST balance programId",
            &post.program_id,
            &asset.token_program,
        ));
    }
    if post.mint != asset.mint {
        return Err(wrong(Reason::WrongMint, "POST balance mint", &post.mint, &asset.mint));
    }
    if &post.owner != owner {
        return Err(wrong(Reason::WrongTokenOwner, "POST balance owner", &post.owner, owner));
    }
    let pre_amount = match at(pre) {
        Some(p) if p.mint != post.mint || p.owner != post.owner || p.program_id != post.program_id => {
            return Err(Refusal::new(
                Reason::BalanceEntriesDisagree,
                format!(
                    "PRE and POST token balances disagree about account {}",
                    crate::model::base58(account)
                ),
            ));
        }
        Some(p) => p.amount,
        // Absent from PRE: this transaction created the account.
        None => 0,
    };
    Ok(post.amount as i128 - pre_amount as i128)
}

#[derive(Clone, Debug)]
struct TokenBalanceEntry {
    mint: Key,
    owner: Key,
    program_id: Key,
    amount: u64,
}

/// Every entry of a `pre`/`postTokenBalances` list, each index range-checked and appearing once.
/// A missing list is empty; an out-of-range index refuses (refusing beats guessing).
fn balances(
    list: Option<&Value>,
    keys: &[Key],
    what: &str,
) -> Result<Vec<(usize, TokenBalanceEntry)>, Refusal> {
    let Some(list) = list.filter(|l| !l.is_null()) else {
        return Ok(Vec::new());
    };
    let entries = list
        .as_array()
        .ok_or_else(|| Refusal::malformed(format!("{what} not an array")))?;
    let mut out: Vec<(usize, TokenBalanceEntry)> = Vec::with_capacity(entries.len());
    for entry in entries {
        let index = entry
            .get("accountIndex")
            .and_then(Value::as_u64)
            .ok_or_else(|| Refusal::malformed(format!("{what} entry missing `accountIndex`")))?
            as usize;
        if index >= keys.len() {
            return Err(Refusal::new(
                Reason::AccountIndexOutOfRange,
                format!(
                    "{what} accountIndex {index} out of range for {} account keys",
                    keys.len()
                ),
            ));
        }
        if out.iter().any(|(i, _)| *i == index) {
            return Err(Refusal::malformed(format!(
                "{what} lists accountIndex {index} twice"
            )));
        }
        let field = |name: &str| -> Result<Key, Refusal> {
            let raw = entry.get(name).and_then(Value::as_str).ok_or_else(|| {
                // `owner` and `programId` are REQUIRED: an RPC that cannot report them cannot
                // attribute a transfer, and an unattributable transfer is not credited.
                Refusal::malformed(format!(
                    "{what} entry missing `{name}`: this RPC cannot attribute a transfer"
                ))
            })?;
            parse_key(raw, &format!("{what} `{name}`"))
        };
        let parsed = TokenBalanceEntry {
            mint: field("mint")?,
            owner: field("owner")?,
            program_id: field("programId")?,
            amount: entry
                .pointer("/uiTokenAmount/amount")
                .and_then(Value::as_str)
                .ok_or_else(|| {
                    Refusal::malformed(format!("{what} entry missing `uiTokenAmount.amount`"))
                })?
                .parse::<u64>()
                .map_err(|e| Refusal::malformed(format!("{what} amount not a u64: {e}")))?,
        };
        out.push((index, parsed));
    }
    Ok(out)
}

/// The transaction's account keys in `accountIndex` order: `message.accountKeys`, then the
/// lookup-table-loaded writable keys, then the loaded readonly keys (Bread's `account_keys`).
fn account_keys(result: &Value) -> Result<Vec<Key>, Refusal> {
    let mut keys = Vec::new();
    let listed = result
        .pointer("/transaction/message/accountKeys")
        .and_then(Value::as_array)
        .ok_or_else(|| {
            Refusal::malformed("getTransaction missing `transaction.message.accountKeys`")
        })?;
    for key in listed {
        let raw = key
            .as_str()
            .or_else(|| key.get("pubkey").and_then(Value::as_str))
            .ok_or_else(|| Refusal::malformed("account key entry has no pubkey"))?;
        keys.push(parse_key(raw, "account key")?);
    }
    for field in ["writable", "readonly"] {
        let Some(loaded) = result
            .pointer(&format!("/meta/loadedAddresses/{field}"))
            .and_then(Value::as_array)
        else {
            continue;
        };
        for key in loaded {
            let raw = key.as_str().ok_or_else(|| {
                Refusal::malformed(format!("loadedAddresses.{field} entry not a string"))
            })?;
            keys.push(parse_key(raw, "loaded address")?);
        }
    }
    Ok(keys)
}
