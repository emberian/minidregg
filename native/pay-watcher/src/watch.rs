//! One run: tip, then per book index per endpoint a view of the index's recent finalized
//! transfers, then N-endpoint agreement (PAY.md §3.3) over those views.
//!
//! Every index is stateless except the ENROLLMENT index (PAY.md §11.9), which pages back to a
//! persistent [`Cursor`] instead of a `maxPages` window. A per-payer address sees a handful of
//! transfers; the enrollment address is public, a shared queue anyone can fill with memo-bearing
//! dust, and a newest-N window there is §2.2's dust hole: enough dust pushes a real enrollment
//! out of the window for good. So index 0 is read to the end of what is not yet SETTLED, and the
//! cursor records how far that is.

use std::collections::{BTreeMap, BTreeSet};
use std::path::Path;

use serde_json::{json, Value};

use crate::config::{BookEntry, Config};
use crate::decode::{signatures_of, token_accounts, transaction_credit, SigEntry, TxOutcome};
use crate::decode::MAX_SUPPORTED_TRANSACTION_VERSION;
use crate::memo;
use crate::model::{
    base58, hex, unbase58, unhex, Clock, Event, Key, Observation, Reason, Refusal, Sig,
};

/// The enrollment index's paging state: per token account, the newest signature at and below
/// which every listing is SETTLED, and is therefore never listed or fetched again (it is
/// passed as `until`). Settled = retained by a receipt, or an agreed permanent skip (failed,
/// zero delta, net debit, below the journal floor). An emitted-but-unreceipted credit, a
/// refusal or a disagreement is NOT settled and holds the cursor below it, so it is read again
/// next run: the cursor can lose nothing that the stateless rule would have retried.
pub type Cursor = BTreeMap<Key, Sig>;

/// `{"cursors": {"<token account hex>": "<signature hex>"}}`. An absent file is an empty cursor.
pub fn load_cursor(path: &Path) -> Result<Cursor, String> {
    let bytes = match std::fs::read(path) {
        Ok(b) => b,
        Err(e) if e.kind() == std::io::ErrorKind::NotFound => return Ok(Cursor::new()),
        Err(e) => return Err(format!("cursor {}: {e}", path.display())),
    };
    let value: Value = serde_json::from_slice(&bytes)
        .map_err(|e| format!("cursor {}: not JSON: {e}", path.display()))?;
    let object = value.as_object().ok_or("cursor is not an object")?;
    if object.keys().any(|k| k != "cursors") {
        return Err(format!("cursor {}: unknown field", path.display()));
    }
    let map = value
        .get("cursors")
        .and_then(Value::as_object)
        .ok_or_else(|| format!("cursor {}: missing `cursors` object", path.display()))?;
    let mut cursor = Cursor::new();
    for (account, sig) in map {
        let account = unhex::<32>(account)
            .ok_or_else(|| format!("cursor {}: account {account} is not 64 hex", path.display()))?;
        let sig = sig
            .as_str()
            .and_then(unhex::<64>)
            .ok_or_else(|| format!("cursor {}: signature is not 128 hex", path.display()))?;
        cursor.insert(account, sig);
    }
    Ok(cursor)
}

pub fn cursor_json(cursor: &Cursor) -> Vec<u8> {
    let map: serde_json::Map<String, Value> = cursor
        .iter()
        .map(|(a, s)| (hex(a), Value::String(hex(s))))
        .collect();
    pretty(&json!({ "cursors": map }))
}
use crate::transport::Transport;

pub struct Report {
    pub tip: Clock,
    pub observations: Vec<Observation>,
    pub events: Vec<Event>,
    /// The enrollment cursor after this run (the input cursor where nothing advanced).
    pub cursor: Cursor,
}

impl Report {
    /// `observations.json`: `{ "observations": [Observation…], "tip": {slot, blockTime} }`.
    /// Keys sort (serde_json's map is ordered) and observations sort by (index, slot,
    /// signature bytes), so a rerun on the same answers is byte-identical.
    pub fn observations_json(&self) -> Vec<u8> {
        let value = json!({
            "observations": self.observations.iter().map(Observation::to_json).collect::<Vec<_>>(),
            "tip": { "slot": self.tip.slot, "blockTime": self.tip.block_time },
        });
        pretty(&value)
    }

    /// `events.json`: every refusal and skip, in decision order.
    pub fn events_json(&self) -> Vec<u8> {
        pretty(&Value::Array(self.events.iter().map(Event::to_json).collect()))
    }

    pub fn refused(&self) -> bool {
        self.events.iter().any(|e| e.reason.is_refusal())
    }
}

fn pretty(value: &Value) -> Vec<u8> {
    let mut bytes = serde_json::to_vec_pretty(value).expect("JSON values serialize");
    bytes.push(b'\n');
    bytes
}

/// One retained receipt: a transfer the kernel has decided, named by the same pair its
/// nullifier binds (`"soltx:" ‖ signature ‖ address`, PAY §10). One transaction can pay two
/// book addresses, and a receipt for one of them must not stop the other from being read.
pub type Receipt = (Sig, Key);

/// The retained receipts: one directory entry per decided transfer, named
/// `SIGNATURE.ADDRESS`, each part as base58 (Solana's spelling) or as lowercase hex of the raw
/// bytes (128 and 64 digits). Only the bytes are compared. The entry's contents are the
/// writer's (the client makes each one a symlink to the attempt that decided it); only the
/// name is read here. Dotfiles are ignored silently; any other name, including a bare
/// signature, is reported and ignored (a lost receipt costs one kernel refusal of a
/// resubmission, never a second credit).
pub fn load_receipts(dir: &Path) -> Result<(BTreeSet<Receipt>, Vec<Event>), String> {
    let mut receipts = BTreeSet::new();
    let mut events = Vec::new();
    let entries =
        std::fs::read_dir(dir).map_err(|e| format!("receipts {}: {e}", dir.display()))?;
    let mut names: Vec<String> = Vec::new();
    for entry in entries {
        let entry = entry.map_err(|e| format!("receipts {}: {e}", dir.display()))?;
        names.push(entry.file_name().to_string_lossy().into_owned());
    }
    names.sort();
    for name in names {
        if name.starts_with('.') {
            continue;
        }
        match receipt_name(&name) {
            Some(receipt) => {
                receipts.insert(receipt);
            }
            None => events.push(Event::of(
                Reason::IgnoredReceiptName,
                None,
                None,
                None,
                format!(
                    "receipt name is not SIGNATURE.ADDRESS (64-byte signature, 32-byte address, \
                     each base58 or hex): {name}"
                ),
            )),
        }
    }
    Ok((receipts, events))
}

fn receipt_name(name: &str) -> Option<Receipt> {
    let (signature, address) = name.split_once('.')?;
    let signature = unhex::<64>(signature).or_else(|| unbase58::<64>(signature))?;
    let address = unhex::<32>(address).or_else(|| unbase58::<32>(address))?;
    Some((signature, address))
}

/// The finalized tip every endpoint has reached: the least finalized slot across endpoints,
/// and that slot's block time, which every endpoint must report identically.
pub fn common_tip(transports: &[&dyn Transport]) -> Result<Clock, Refusal> {
    let mut slot = u64::MAX;
    for t in transports {
        let s = t
            .call("getSlot", json!([{ "commitment": "finalized" }]))?
            .as_u64()
            .ok_or_else(|| Refusal::malformed(format!("{}: getSlot not an integer", t.label())))?;
        slot = slot.min(s);
    }
    let mut times = Vec::with_capacity(transports.len());
    for t in transports {
        let time = t.call("getBlockTime", json!([slot]))?.as_u64().ok_or_else(|| {
            Refusal::malformed(format!("{}: no block time for tip slot {slot}", t.label()))
        })?;
        times.push((t.label().to_owned(), time));
    }
    if times.iter().any(|(_, t)| *t != times[0].1) {
        return Err(Refusal::new(
            Reason::EndpointsDisagree,
            format!(
                "block time of tip slot {slot}: {}",
                times
                    .iter()
                    .map(|(l, t)| format!("{l}={t}"))
                    .collect::<Vec<_>>()
                    .join(", ")
            ),
        ));
    }
    Ok(Clock {
        slot,
        block_time: times[0].1,
    })
}

/// One endpoint's verdict on one transfer.
#[derive(Clone, Debug, PartialEq, Eq)]
enum Outcome {
    /// `memos`: every memo instruction's bytes, read for the enrollment index only (`None`
    /// elsewhere). Endpoints must agree on the BYTES: the watcher never picks one endpoint's.
    Credit { slot: u64, block_time: u64, amount: u64, memos: Option<Vec<Vec<u8>>> },
    Skip(Reason, String),
    Refused(Reason, String),
}

impl Outcome {
    fn describe(&self) -> String {
        match self {
            Outcome::Credit {
                slot,
                block_time,
                amount,
                memos,
            } => {
                let base = format!("credit slot={slot} blockTime={block_time} amount={amount}");
                match memos {
                    Some(m) => format!(
                        "{base} memos=[{}]",
                        m.iter().map(|b| memo::describe(b)).collect::<Vec<_>>().join(", ")
                    ),
                    None => base,
                }
            }
            Outcome::Skip(r, d) | Outcome::Refused(r, d) => format!("{} ({d})", r.name()),
        }
    }

    /// A permanent decision: the cursor may pass it.
    fn settled(&self) -> bool {
        matches!(
            self,
            Outcome::Skip(
                Reason::FailedTransaction
                    | Reason::ZeroDelta
                    | Reason::NetDebit
                    | Reason::BelowJournalFloor,
                _
            )
        )
    }
}

struct IndexView {
    outcomes: BTreeMap<Sig, Outcome>,
    notes: Vec<(Reason, Option<Sig>, String)>,
    /// Enrollment index only: per token account, the listing at or below the tip, newest first.
    listed: Vec<(Key, Vec<Sig>)>,
}

/// One endpoint's view of one book index. An `Err` refuses the whole index for this run, as
/// `SignatureWatcher::poll` fails the whole poll: it means this endpoint contradicted the
/// configuration or itself, and nothing it said about this address is believed.
fn view_index(
    t: &dyn Transport,
    cfg: &Config,
    entry: &BookEntry,
    receipts: &BTreeSet<Sig>,
    tip: Clock,
    cursor: &Cursor,
) -> Result<IndexView, Refusal> {
    let enrol = cfg.enrol.as_ref().filter(|e| e.index == entry.index);
    let mut view = IndexView {
        outcomes: BTreeMap::new(),
        notes: Vec::new(),
        listed: Vec::new(),
    };
    let accounts = token_accounts(
        &t.call(
            "getTokenAccountsByOwner",
            json!([
                base58(&entry.address),
                { "mint": base58(&cfg.asset.mint) },
                { "encoding": "jsonParsed", "commitment": "finalized" },
            ]),
        )?,
        &cfg.asset,
        &entry.address,
    )?;
    if accounts.is_empty() {
        view.notes
            .push((Reason::NoTokenAccount, None, "no token account for the mint".into()));
        return Ok(view);
    }

    // Signatures across every watched account, newest first per account, deduplicated by the
    // 64 raw bytes: one transaction touching two of the owner's accounts is one transfer.
    let mut seen: BTreeMap<Sig, SigEntry> = BTreeMap::new();
    for account in &accounts {
        let mut before: Option<Sig> = None;
        let until = enrol.and_then(|_| cursor.get(account));
        let mut listed: Vec<Sig> = Vec::new();
        let mut listed_set: BTreeSet<Sig> = BTreeSet::new();
        let mut page = 0usize;
        loop {
            let mut opts = json!({ "commitment": "finalized", "limit": cfg.page_size });
            if let Some(b) = before {
                opts["before"] = Value::String(base58(&b));
            }
            if let Some(u) = until {
                opts["until"] = Value::String(base58(u));
            }
            let entries = signatures_of(
                &t.call("getSignaturesForAddress", json!([base58(account), opts]))?,
            )?;
            for e in &entries {
                if enrol.is_some() && e.slot <= tip.slot && listed_set.insert(e.signature) {
                    listed.push(e.signature);
                }
                // A receipt saves this signature's getTransaction, and nothing else: paging
                // continues, because an OLDER transfer that was not emitted on an earlier run
                // (endpoints disagreed, or it was pruned) has no receipt and must be read
                // again. Stopping at the first receipt would lose it for good.
                if receipts.contains(&e.signature) {
                    view.notes.push((
                        Reason::AlreadyRetained,
                        Some(e.signature),
                        "a receipt is retained; not fetched".into(),
                    ));
                    continue;
                }
                // Not yet under the common tip: another endpoint may not have it. Next run.
                if e.slot > tip.slot {
                    continue;
                }
                match seen.get(&e.signature) {
                    Some(prior) if prior.slot != e.slot => {
                        return Err(Refusal::new(
                            Reason::SlotMismatch,
                            format!(
                                "signature {} listed at slots {} and {}",
                                base58(&e.signature),
                                prior.slot,
                                e.slot
                            ),
                        ));
                    }
                    Some(_) => view.notes.push((
                        Reason::DuplicateSignature,
                        Some(e.signature),
                        "listed more than once; observed once".into(),
                    )),
                    None => {
                        seen.insert(e.signature, e.clone());
                    }
                }
            }
            if entries.len() < cfg.page_size {
                break;
            }
            let next = entries.last().map(|e| e.signature);
            if next == before {
                return Err(Refusal::malformed(format!(
                    "account {}: paging did not advance",
                    base58(account)
                )));
            }
            before = next;
            page += 1;
            // The enrollment index pages to the cursor or the end of history (module doc).
            if enrol.is_none() && page == cfg.max_pages {
                view.notes.push((
                    Reason::PageBound,
                    None,
                    format!(
                        "account {}: {} pages of {} read; older history not read",
                        base58(account),
                        cfg.max_pages,
                        cfg.page_size
                    ),
                ));
                break;
            }
        }
        if enrol.is_some() {
            view.listed.push((*account, listed));
        }
    }

    for (sig, e) in &seen {
        let outcome = if e.failed {
            Outcome::Skip(Reason::FailedTransaction, "signature list reports err".into())
        } else {
            let result = t.call(
                "getTransaction",
                json!([
                    base58(sig),
                    {
                        "encoding": "jsonParsed",
                        "commitment": "finalized",
                        "maxSupportedTransactionVersion": MAX_SUPPORTED_TRANSACTION_VERSION,
                    },
                ]),
            )?;
            match transaction_credit(&result, sig, e.slot, &accounts, &cfg.asset, &entry.address)? {
                TxOutcome::Pruned => Outcome::Refused(
                    Reason::PrunedTransaction,
                    "getTransaction result is null for a listed finalized signature".into(),
                ),
                TxOutcome::Failed => {
                    Outcome::Skip(Reason::FailedTransaction, "meta.err is non-null".into())
                }
                TxOutcome::Landed {
                    slot,
                    block_time,
                    delta,
                } => {
                    if delta > 0 {
                        let amount = u64::try_from(delta).map_err(|_| {
                            Refusal::malformed(format!("credited amount {delta} exceeds u64"))
                        })?;
                        match enrol {
                            // Dust is recorded here and never submitted (PAY.md §11.7).
                            Some(e) if amount < e.journal_floor => Outcome::Skip(
                                Reason::BelowJournalFloor,
                                format!("amount {amount} < journalFloor {}", e.journal_floor),
                            ),
                            // Only the memos of the transaction that made the credit: a memo
                            // in any other transaction is never joined to it.
                            Some(_) => Outcome::Credit {
                                slot,
                                block_time,
                                amount,
                                memos: Some(memo::memos(&result)?),
                            },
                            None => Outcome::Credit {
                                slot,
                                block_time,
                                amount,
                                memos: None,
                            },
                        }
                    } else if delta == 0 {
                        Outcome::Skip(Reason::ZeroDelta, "added nothing to the watched accounts".into())
                    } else {
                        Outcome::Skip(Reason::NetDebit, format!("net change {delta}"))
                    }
                }
            }
        };
        view.outcomes.insert(*sig, outcome);
    }
    Ok(view)
}

/// The whole run. `Err` only when no tip could be agreed (nothing is emitted, not even a
/// heartbeat); every per-index or per-transfer problem is an event in the report.
pub fn run(
    cfg: &Config,
    transports: &[&dyn Transport],
    receipts: &BTreeSet<Receipt>,
    cursor: &Cursor,
) -> Result<Report, Refusal> {
    if transports.len() < cfg.min_endpoints {
        return Err(Refusal::new(
            Reason::Transport,
            format!(
                "{} endpoints configured; minEndpoints is {}",
                transports.len(),
                cfg.min_endpoints
            ),
        ));
    }
    let tip = common_tip(transports)?;
    let mut observations = Vec::new();
    let mut events = Vec::new();
    let mut next_cursor = cursor.clone();

    for entry in &cfg.book {
        let idx = Some(entry.index);
        // The receipts for THIS address: a transfer decided for another book row is not one
        // decided here, even when the transaction is the same.
        let retained: BTreeSet<Sig> = receipts
            .iter()
            .filter(|(_, address)| *address == entry.address)
            .map(|(signature, _)| *signature)
            .collect();
        let views: Vec<(&str, Result<IndexView, Refusal>)> = transports
            .iter()
            .map(|t| (t.label(), view_index(*t, cfg, entry, &retained, tip, cursor)))
            .collect();

        let refusals: Vec<Event> = views
            .iter()
            .filter_map(|(label, v)| v.as_ref().err().map(|r| (label, r)))
            .map(|(label, r)| Event::of(r.reason, idx, None, Some(label), r.detail.clone()))
            .collect();
        if !refusals.is_empty() {
            events.extend(refusals);
            continue;
        }
        let views: Vec<(&str, IndexView)> = views
            .into_iter()
            .map(|(l, v)| (l, v.expect("refusals handled above")))
            .collect();

        for (label, view) in &views {
            for (reason, sig, detail) in &view.notes {
                events.push(Event::of(*reason, idx, *sig, Some(label), detail.clone()));
            }
        }
        let sigs: BTreeSet<Sig> = views
            .iter()
            .flat_map(|(_, v)| v.outcomes.keys().copied())
            .collect();
        // Signatures whose agreed outcome is a permanent decision (see `Cursor`).
        let mut settled: BTreeSet<Sig> = retained.clone();
        for sig in sigs {
            let answers: Vec<Option<&Outcome>> =
                views.iter().map(|(_, v)| v.outcomes.get(&sig)).collect();
            let first = answers[0];
            if first.is_some() && answers.iter().all(|a| *a == first) {
                if first.expect("checked").settled() {
                    settled.insert(sig);
                }
                match first.expect("checked") {
                    Outcome::Credit {
                        slot,
                        block_time,
                        amount,
                        memos,
                    } => {
                        let (memo, memo_error) = match memos {
                            Some(m) => memo::bind(m),
                            None => (None, None),
                        };
                        if let (Some(e), Some(m)) = (memo_error, memos) {
                            events.push(Event::of(
                                e.reason(),
                                idx,
                                Some(sig),
                                None,
                                format!(
                                    "{} memo instruction(s); memo emitted as null: [{}]",
                                    m.len(),
                                    m.iter().map(|b| memo::describe(b)).collect::<Vec<_>>().join(", ")
                                ),
                            ));
                        }
                        observations.push(Observation {
                            index: entry.index,
                            address: entry.address,
                            signature: sig,
                            slot: *slot,
                            block_time: *block_time,
                            amount: *amount,
                            mint: cfg.asset.mint,
                            token_program: cfg.asset.token_program,
                            memo,
                            memo_error,
                        })
                    }
                    Outcome::Skip(r, d) | Outcome::Refused(r, d) => {
                        events.push(Event::of(*r, idx, Some(sig), None, d.clone()))
                    }
                }
            } else {
                let detail = views
                    .iter()
                    .zip(&answers)
                    .map(|((label, _), a)| {
                        format!("{label}: {}", a.map_or("absent".into(), Outcome::describe))
                    })
                    .collect::<Vec<_>>()
                    .join("; ");
                events.push(Event::of(Reason::EndpointsDisagree, idx, Some(sig), None, detail));
            }
        }
        advance_cursor(&views, &settled, idx, &mut next_cursor, &mut events);
    }
    observations.sort_by(|a, b| {
        (a.index, a.slot, a.signature).cmp(&(b.index, b.slot, b.signature))
    });
    Ok(Report {
        tip,
        observations,
        events,
        cursor: next_cursor,
    })
}

/// Per enrollment token account: walk the agreed listing from the oldest entry and move the
/// cursor over every settled signature, stopping at the first that is not. The listing order is
/// the RPC's (a slot can hold several of the account's transactions, and `until` cuts at a
/// position, not a slot), so the endpoints must list the account identically or it holds.
fn advance_cursor(
    views: &[(&str, IndexView)],
    settled: &BTreeSet<Sig>,
    idx: Option<u64>,
    cursor: &mut Cursor,
    events: &mut Vec<Event>,
) {
    let Some((_, first)) = views.first() else { return };
    for (account, listed) in &first.listed {
        let agreed = views.iter().all(|(_, v)| {
            v.listed.iter().any(|(a, l)| a == account && l == listed)
        });
        if !agreed {
            events.push(Event::of(
                Reason::CursorHeld,
                idx,
                None,
                None,
                format!("account {}: endpoints list it differently", base58(account)),
            ));
            continue;
        }
        if let Some(newest_settled) = listed
            .iter()
            .rev()
            .take_while(|s| settled.contains(*s))
            .last()
        {
            cursor.insert(*account, *newest_settled);
        }
    }
}
