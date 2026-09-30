//! One stateless run: tip, then per book index per endpoint a view of the index's recent
//! finalized transfers, then N-endpoint agreement (PAY.md §3.3) over those views.

use std::collections::{BTreeMap, BTreeSet};
use std::path::Path;

use serde_json::{json, Value};

use crate::config::{BookEntry, Config};
use crate::decode::{signatures_of, token_accounts, transaction_credit, SigEntry, TxOutcome};
use crate::model::{
    base58, unbase58, unhex, Clock, Event, Observation, Reason, Refusal, Sig,
};
use crate::transport::Transport;

pub struct Report {
    pub tip: Clock,
    pub observations: Vec<Observation>,
    pub events: Vec<Event>,
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

/// The retained receipts: one file per credited signature, named by the signature as base58
/// (Solana's spelling) or as 128 hex digits. Both decode to the 64 raw bytes, which is the only
/// thing compared. Dotfiles are ignored silently; any other name is reported and ignored (a
/// lost receipt costs one kernel refusal of a resubmission, never a second credit).
pub fn load_receipts(dir: &Path) -> Result<(BTreeSet<Sig>, Vec<Event>), String> {
    let mut sigs = BTreeSet::new();
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
        match unhex::<64>(&name).or_else(|| unbase58::<64>(&name)) {
            Some(sig) => {
                sigs.insert(sig);
            }
            None => events.push(Event::of(
                Reason::IgnoredReceiptName,
                None,
                None,
                None,
                format!("receipt name is neither a base58 nor a hex 64-byte signature: {name}"),
            )),
        }
    }
    Ok((sigs, events))
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
    Credit { slot: u64, block_time: u64, amount: u64 },
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
            } => format!("credit slot={slot} blockTime={block_time} amount={amount}"),
            Outcome::Skip(r, d) | Outcome::Refused(r, d) => format!("{} ({d})", r.name()),
        }
    }
}

struct IndexView {
    outcomes: BTreeMap<Sig, Outcome>,
    notes: Vec<(Reason, Option<Sig>, String)>,
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
) -> Result<IndexView, Refusal> {
    let mut view = IndexView {
        outcomes: BTreeMap::new(),
        notes: Vec::new(),
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
        'pages: for page in 0..cfg.max_pages {
            let mut opts = json!({ "commitment": "finalized", "limit": cfg.page_size });
            if let Some(b) = before {
                opts["before"] = Value::String(base58(&b));
            }
            let entries = signatures_of(
                &t.call("getSignaturesForAddress", json!([base58(account), opts]))?,
            )?;
            for e in &entries {
                if receipts.contains(&e.signature) {
                    view.notes.push((
                        Reason::AlreadyRetained,
                        Some(e.signature),
                        "a receipt is retained; older history is not read".into(),
                    ));
                    break 'pages;
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
            before = entries.last().map(|e| e.signature);
            if page + 1 == cfg.max_pages {
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
            }
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
                        "maxSupportedTransactionVersion": 0,
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
                        Outcome::Credit {
                            slot,
                            block_time,
                            amount,
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
    receipts: &BTreeSet<Sig>,
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

    for entry in &cfg.book {
        let idx = Some(entry.index);
        let views: Vec<(&str, Result<IndexView, Refusal>)> = transports
            .iter()
            .map(|t| (t.label(), view_index(*t, cfg, entry, receipts, tip)))
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
        for sig in sigs {
            let answers: Vec<Option<&Outcome>> =
                views.iter().map(|(_, v)| v.outcomes.get(&sig)).collect();
            let first = answers[0];
            if first.is_some() && answers.iter().all(|a| *a == first) {
                match first.expect("checked") {
                    Outcome::Credit {
                        slot,
                        block_time,
                        amount,
                    } => observations.push(Observation {
                        index: entry.index,
                        address: entry.address,
                        signature: sig,
                        slot: *slot,
                        block_time: *block_time,
                        amount: *amount,
                        mint: cfg.asset.mint,
                        token_program: cfg.asset.token_program,
                    }),
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
    }
    observations.sort_by(|a, b| {
        (a.index, a.slot, a.signature).cmp(&(b.index, b.slot, b.signature))
    });
    Ok(Report {
        tip,
        observations,
        events,
    })
}
