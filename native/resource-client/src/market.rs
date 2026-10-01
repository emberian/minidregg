//! The sealed-bid market (PRIVACY §3.4, MUD §2.7/§2.8): one declared cell under
//! the law `deploy/shell/templates/market/sealed/law.market`, a founder who sells
//! `supply` units at one uniform price, and up to four sealed bids.
//!
//! A bid is a COMMIT to the tuple (price, qty) under a fresh 32-byte blinder
//! (`Pred.hashEq`, `Pred/HashEq.lean`): before the close height the cell holds the
//! bidder's subject and the commitment only, so neither the Store nor any signed
//! read carries the price. From the close height until the reveal end a bidder
//! writes the opening, and the law admits it iff it opens the commitment. From
//! the reveal end the founder settles: the runner here reads the revealed tuples
//! (the kernel already judged every opening on the Store, so there is no
//! `valid` field to trust), allocates `supply` by price then slot, and writes
//! each slot's fill and the clearing price once. An unrevealed bid fills
//! nothing; the law refuses a fill above a slot's revealed quantity, so an
//! unrevealed slot (quantity 0) can only be skipped.
//!
//! The kernel judges the opening and the phase rules; the allocation itself is
//! accountable, not judged: anyone holding a read recomputes it with
//! `market-bids`.
//!
//! DEPOSIT: a bid's deposit belongs in a Book account named by the bid (C3
//! K-JOB-MONEY's held-account design), returned at reveal and forfeit to the
//! market's well on a missed reveal. That receiver is not on this tree, so a
//! market with a deposit is refused by name (`depositUnavailable`) and every
//! market here takes none. See `DEPOSIT_UNAVAILABLE`.

use crate::workspace::{self, member};
use crate::Result;
use serde_json::{json, Value};
use sha3::digest::{core_api::CoreWrapper, ExtendableOutput, Update, XofReader};
use sha3::CShake256Core;
use std::fs::{self, File};
use std::io::Read;
use std::os::unix::fs::DirBuilderExt;
use std::path::{Path, PathBuf};

/// The sealed-market law in the shell grammar, with placeholders.
pub(crate) const LAW_TEMPLATE: &str = include_str!(concat!(
    env!("CARGO_MANIFEST_DIR"),
    "/../../deploy/shell/templates/market/sealed/law.market"
));

/// The refusal a deposit gets until the bid-deposit receiver exists.
pub(crate) const DEPOSIT_UNAVAILABLE: &str = "depositUnavailable: a bid deposit is credit held in a Book account named by the bid (C3's held-account receiver), returned at reveal and forfeit on a missed reveal; that receiver is not on this tree (cv task 01a0f81a-386d), so this market takes no deposit";

/// `Pred.HashEqDigest.customization`.
const CUSTOMIZATION: &[u8] = b"DREGG.PRED.HASHEQ/v2";

pub(crate) const SLOTS: u64 = 4;
pub(crate) const FIELD_SETTLED: u64 = 1;
pub(crate) const FIELD_CLOSE: u64 = 2;
pub(crate) const FIELD_REVEAL_END: u64 = 3;
pub(crate) const FIELD_SUPPLY: u64 = 4;
pub(crate) const FIELD_PRICE: u64 = 5;

/// Slot `k`'s fields: who, commit, price, qty, blinder, filled at `16 + 8k + 0..5`.
#[derive(Clone, Copy, Debug, PartialEq)]
pub(crate) struct SlotFields {
    pub who: u64,
    pub commit: u64,
    pub price: u64,
    pub qty: u64,
    pub blinder: u64,
    pub filled: u64,
}

pub(crate) fn slot_fields(k: u64) -> SlotFields {
    let base = 16 + 8 * k;
    SlotFields { who: base, commit: base + 1, price: base + 2, qty: base + 3, blinder: base + 4, filled: base + 5 }
}

fn field_slot(n: u64) -> String {
    format!("resource/field/{n}/after")
}

/// The law for one market: the template with its placeholders bound, comment
/// lines (`--`) dropped, parsed by the shell grammar.
pub(crate) fn law(founder: &str, close: u64, reveal_end: u64, supply: i128) -> Result<Value> {
    if close == 0 || reveal_end <= close {
        return Err("a market needs 0 < CLOSE < REVEAL-END (block heights)".into());
    }
    if supply <= 0 {
        return Err("a market sells a positive SUPPLY".into());
    }
    let text = LAW_TEMPLATE
        .lines()
        .filter(|line| !line.trim_start().starts_with("--"))
        .collect::<Vec<_>>()
        .join("\n")
        .replace("{FOUNDER}", founder)
        .replace("{LAST_SEALED}", &(close - 1).to_string())
        .replace("{LAST_REVEAL}", &(reveal_end - 1).to_string())
        .replace("{CLOSE}", &close.to_string())
        .replace("{REVEAL_END}", &reveal_end.to_string())
        .replace("{SUPPLY}", &supply.to_string());
    crate::shell::law::parse(&text).map_err(|error| format!("market law template: {error}"))
}

// ------------------------------------------------------------ the commitment

fn name(out: &mut Vec<u8>, slot: &str) {
    out.extend_from_slice(&(slot.len() as u32).to_be_bytes());
    out.extend_from_slice(slot.as_bytes());
}

/// `value + 2^255` as 32 big-endian bytes: the 256-bit two's complement of the
/// value with its top bit flipped.
fn word(value: i128) -> [u8; 32] {
    let mut out = if value < 0 { [0xffu8; 32] } else { [0u8; 32] };
    out[16..].copy_from_slice(&value.to_be_bytes());
    out[0] ^= 0x80;
    out
}

/// The canonical preimage of `Pred.HashEqDigest.Opening.preimage`.
pub(crate) fn preimage(cell: u64, values: &[(String, i128)], blinder_slot: &str, commit_slot: &str, blinder: &[u8; 32]) -> Vec<u8> {
    let mut out = Vec::new();
    out.extend_from_slice(&cell.to_be_bytes());
    out.extend_from_slice(&(values.len() as u32).to_be_bytes());
    for (slot, _) in values {
        name(&mut out, slot);
    }
    name(&mut out, blinder_slot);
    name(&mut out, commit_slot);
    for (_, value) in values {
        out.extend_from_slice(&word(*value));
    }
    out.extend_from_slice(blinder);
    out
}

/// `digestWith deployed`: cSHAKE256(N = "", S = "DREGG.PRED.HASHEQ/v2"), 32 bytes.
pub(crate) fn digest(preimage: &[u8]) -> [u8; 32] {
    let mut hasher = CoreWrapper::from_core(CShake256Core::new(CUSTOMIZATION));
    hasher.update(preimage);
    let mut output = [0u8; 32];
    XofReader::read(&mut hasher.finalize_xof(), &mut output);
    output
}

/// A big-endian natural as a decimal string.
pub(crate) fn decimal(bytes: &[u8]) -> String {
    let mut digits = Vec::new();
    let mut n: Vec<u8> = bytes.iter().copied().skip_while(|b| *b == 0).collect();
    while !n.is_empty() {
        let mut rem = 0u32;
        let mut next = Vec::with_capacity(n.len());
        for byte in &n {
            let acc = rem * 256 + u32::from(*byte);
            let q = acc / 10;
            rem = acc % 10;
            if !(next.is_empty() && q == 0) {
                next.push(q as u8);
            }
        }
        digits.push(b'0' + rem as u8);
        n = next;
    }
    if digits.is_empty() {
        return "0".into();
    }
    digits.reverse();
    String::from_utf8(digits).expect("ASCII digits")
}

/// The commitment slot `k` of the market cell `cell` carries for (price, qty).
pub(crate) fn commitment(cell: u64, k: u64, price: i128, qty: i128, blinder: &[u8; 32]) -> String {
    let f = slot_fields(k);
    let pre = preimage(
        cell,
        &[(field_slot(f.price), price), (field_slot(f.qty), qty)],
        &field_slot(f.blinder),
        &field_slot(f.commit),
        blinder,
    );
    decimal(&digest(&pre))
}

fn random32() -> Result<[u8; 32]> {
    let mut bytes = [0u8; 32];
    File::open("/dev/urandom")
        .and_then(|mut file| file.read_exact(&mut bytes))
        .map_err(|error| format!("cannot obtain operating-system randomness: {error}"))?;
    Ok(bytes)
}

// ------------------------------------------------------------ reading a market

/// One market cell as a signed read showed it.
#[derive(Debug)]
pub(crate) struct Market {
    pub height: u64,
    pub fields: std::collections::BTreeMap<u64, String>,
}

impl Market {
    fn get(&self, field: u64) -> Option<&str> {
        self.fields.get(&field).map(String::as_str)
    }
    fn int(&self, field: u64) -> Result<i128> {
        let text = self.get(field).ok_or_else(|| format!("the market has no field {field} (not set up?)"))?;
        text.parse::<i128>().map_err(|_| format!("market field {field} is not a 128-bit integer: {text}"))
    }
    fn height_param(&self, field: u64) -> Result<u64> {
        let v = self.int(field)?;
        u64::try_from(v).map_err(|_| format!("market field {field} is not a height: {v}"))
    }
    pub(crate) fn close(&self) -> Result<u64> {
        self.height_param(FIELD_CLOSE)
    }
    pub(crate) fn reveal_end(&self) -> Result<u64> {
        self.height_param(FIELD_REVEAL_END)
    }
    fn is_zero(&self, field: u64) -> bool {
        self.get(field) == Some("0")
    }
    /// A slot's bid, if a bidder holds it.
    fn bid(&self, k: u64) -> Option<Bid> {
        let f = slot_fields(k);
        let who = self.get(f.who)?;
        if who == "0" {
            return None;
        }
        let revealed = !self.is_zero(f.blinder);
        Some(Bid {
            slot: k,
            who: who.to_owned(),
            commit: self.get(f.commit).unwrap_or("absent").to_owned(),
            price: self.get(f.price).and_then(|v| v.parse().ok()).unwrap_or(0),
            qty: self.get(f.qty).and_then(|v| v.parse().ok()).unwrap_or(0),
            revealed,
            filled: self.get(f.filled).and_then(|v| v.parse().ok()).unwrap_or(0),
        })
    }
}

#[derive(Debug, Clone, PartialEq)]
pub(crate) struct Bid {
    pub slot: u64,
    pub who: String,
    pub commit: String,
    pub price: i128,
    pub qty: i128,
    pub revealed: bool,
    pub filled: i128,
}

pub(crate) fn parse_view(view: &Value, height: u64) -> Result<Market> {
    let entries = view
        .get("cell")
        .and_then(|cell| cell.get("entries"))
        .and_then(Value::as_array)
        .ok_or("the market read is not a declared cell")?;
    let mut fields = std::collections::BTreeMap::new();
    for entry in entries {
        let key = entry.get("key").ok_or("cell entry lacks key")?;
        if key.get("type").and_then(Value::as_str) != Some("object") {
            continue;
        }
        let field = key
            .get("field")
            .and_then(Value::as_str)
            .and_then(|f| f.parse::<u64>().ok())
            .ok_or("cell entry field is not a number")?;
        let value = entry.get("value").and_then(Value::as_str).ok_or("cell entry value is not a string")?;
        fields.insert(field, value.to_owned());
    }
    Ok(Market { height, fields })
}

fn read_market(root: &Path, ws: &Value, name: &str) -> Result<(Market, Value)> {
    let reference = workspace::reference(root, name)?;
    let (view, challenge, _) = workspace::signed_view(root, ws, &reference, "resource")?;
    let height = member(&challenge, "height")?
        .parse::<u64>()
        .map_err(|_| "signed read height is not a number".to_string())?;
    Ok((parse_view(&view, height)?, reference))
}

fn cell_id(reference: &Value) -> Result<u64> {
    member(reference, "target")?
        .parse::<u64>()
        .map_err(|_| "the market cell id is not below 2^64, so no commitment can name it".into())
}

// ------------------------------------------------------------ settlement

/// The runner's allocation: `supply` to revealed bids by price (high first),
/// then slot (earlier first); the clearing price is the lowest price that
/// received a fill. Unrevealed bids, and bids with a non-positive price or
/// quantity, fill nothing.
pub(crate) fn clear(supply: i128, bids: &[Bid]) -> (i128, Vec<(u64, i128)>) {
    let mut live: Vec<&Bid> = bids.iter().filter(|b| b.revealed && b.price > 0 && b.qty > 0).collect();
    live.sort_by(|a, b| b.price.cmp(&a.price).then(a.slot.cmp(&b.slot)));
    let mut left = supply.max(0);
    let mut price = 0;
    let mut fills = Vec::new();
    for bid in live {
        let take = bid.qty.min(left);
        if take > 0 {
            fills.push((bid.slot, take));
            left -= take;
            price = bid.price;
        }
    }
    (price, fills)
}

// ------------------------------------------------------------ actions

fn scalar(field: u64, value: &str, expected: Option<&str>) -> Value {
    let mut action = json!({"type": if expected.is_some() {"write"} else {"create"},
        "key":{"type":"object","field":field.to_string()},"value":value});
    if let Some(expected) = expected {
        action["expected"] = json!(expected);
    }
    action
}

fn propose_writes(root: &Path, ws: &Value, name: &str, id: &str, actions: Vec<Value>) -> Result<()> {
    let request = json!({"type":"minidregg-workspace-proposal-v1","action":"invoke",
        "targets":[{"name":name,"payload":{"type":"scalar","actions":actions}}]});
    let path = root.join("sources").join(format!("market-{id}.json"));
    workspace::private_file(&path, &serde_json::to_vec(&request).map_err(|e| e.to_string())?)?;
    workspace::propose(root, ws, &path, id, None)
}

fn openings_dir(root: &Path, name: &str) -> Result<PathBuf> {
    let dir = root.join("market").join(name);
    fs::DirBuilder::new()
        .recursive(true)
        .mode(0o700)
        .create(&dir)
        .map_err(|error| format!("cannot create {}: {error}", dir.display()))?;
    Ok(dir)
}

fn int_arg(value: &str, label: &str) -> Result<i128> {
    let v = value.parse::<i128>().map_err(|_| format!("{label} must be an integer"))?;
    if v.unsigned_abs() >= 1u128 << 120 {
        return Err(format!("{label} is out of range"));
    }
    Ok(v)
}

/// `market-open`: birth the market cell under its law, then set it up (the
/// parameters and every slot at 0) in one signed write.
pub(crate) fn open(root: &Path, ws: &Value, name: &str, close: &str, reveal_end: &str, supply: &str, deposit: &str) -> Result<()> {
    workspace::validate_name(name)?;
    if deposit != "0" {
        return Err(DEPOSIT_UNAVAILABLE.into());
    }
    let close = close.parse::<u64>().map_err(|_| "CLOSE must be a block height")?;
    let reveal_end = reveal_end.parse::<u64>().map_err(|_| "REVEAL-END must be a block height")?;
    let supply = int_arg(supply, "SUPPLY")?;
    let founder = member(ws, "subject")?.to_owned();
    let predicate = law(&founder, close, reveal_end, supply)?;
    let law_path = root.join("sources").join(format!("market-law-{name}-{}.json", workspace::random_nonce()?));
    workspace::private_file(&law_path, &serde_json::to_vec(&predicate).map_err(|e| e.to_string())?)?;
    workspace::create(root, ws, name, "declared", &law_path, None, "object", None, None)?;
    let mut actions = vec![
        scalar(FIELD_CLOSE, &close.to_string(), None),
        scalar(FIELD_REVEAL_END, &reveal_end.to_string(), None),
        scalar(FIELD_SUPPLY, &supply.to_string(), None),
        scalar(FIELD_PRICE, "0", None),
    ];
    for k in 0..SLOTS {
        let f = slot_fields(k);
        for field in [f.who, f.commit, f.price, f.qty, f.blinder, f.filled] {
            actions.push(scalar(field, "0", None));
        }
    }
    let id = format!("open-{name}");
    propose_writes(root, ws, name, &id, actions)?;
    workspace::submit_intent(
        root,
        ws,
        &root.join("proposals").join(&id).join("intent.json"),
        "intent",
        false,
        Some(&root.join("attempts").join(&id)),
    )?;
    eprintln!("market {name}: bids sealed through height {}, reveals at heights {close}..{}, settlement from {reveal_end}; supply {supply}; {SLOTS} bid slots; deposit none", close - 1, reveal_end - 1);
    Ok(())
}

/// `market-bid`: commit to (price, qty) in the first free slot. The opening is
/// kept in WORKSPACE/market/NAME/, owner-private; nothing but the subject and
/// the commitment is proposed.
pub(crate) fn bid(root: &Path, ws: &Value, name: &str, price: &str, qty: &str, id: &str) -> Result<()> {
    workspace::validate_name(name)?;
    let price = int_arg(price, "PRICE")?;
    let qty = int_arg(qty, "QTY")?;
    let (market, reference) = read_market(root, ws, name)?;
    let cell = cell_id(&reference)?;
    let k = (0..SLOTS)
        .find(|k| market.get(slot_fields(*k).who) == Some("0"))
        .ok_or_else(|| format!("market {name} has no free bid slot ({SLOTS} taken)"))?;
    let blinder = random32()?;
    let commit = commitment(cell, k, price, qty, &blinder);
    let opening = json!({"type":"minidregg-sealed-bid-opening-v1","market":name,"cell":cell.to_string(),
        "slot":k,"price":price.to_string(),"qty":qty.to_string(),"blinder":decimal(&blinder),
        "commit":commit,"proposal":id});
    let path = openings_dir(root, name)?.join(format!("{id}.json"));
    workspace::private_file(&path, &serde_json::to_vec_pretty(&opening).map_err(|e| e.to_string())?)?;
    let me = member(ws, "subject")?;
    let f = slot_fields(k);
    propose_writes(root, ws, name, id, vec![
        scalar(f.who, me, Some("0")),
        scalar(f.commit, &commit, Some("0")),
    ])?;
    eprintln!("bid {id}: slot {k} of {name}, commitment {}…; the opening (price, qty, blinder) stays in {}; deposit: none (depositUnavailable)", &commit[..commit.len().min(16)], path.display());
    Ok(())
}

fn openings(root: &Path, name: &str) -> Result<Vec<Value>> {
    let dir = root.join("market").join(name);
    let mut out = Vec::new();
    if let Ok(entries) = fs::read_dir(&dir) {
        for entry in entries.flatten() {
            if let Ok(opening) = workspace::bounded_json(&entry.path()) {
                out.push(opening);
            }
        }
    }
    Ok(out)
}

/// `market-reveal`: write the opening of every slot this subject holds whose
/// commitment matches an opening kept here.
pub(crate) fn reveal(root: &Path, ws: &Value, name: &str, id: &str) -> Result<()> {
    workspace::validate_name(name)?;
    let (market, _) = read_market(root, ws, name)?;
    let me = member(ws, "subject")?;
    let kept = openings(root, name)?;
    let mut actions = Vec::new();
    let mut slots = Vec::new();
    for k in 0..SLOTS {
        let f = slot_fields(k);
        if market.get(f.who) != Some(me) || !market.is_zero(f.blinder) {
            continue;
        }
        let commit = market.get(f.commit).unwrap_or("");
        if let Some(opening) = kept.iter().find(|o| o["commit"].as_str() == Some(commit) && o["slot"].as_u64() == Some(k)) {
            actions.push(scalar(f.price, member(opening, "price")?, Some("0")));
            actions.push(scalar(f.qty, member(opening, "qty")?, Some("0")));
            actions.push(scalar(f.blinder, member(opening, "blinder")?, Some("0")));
            slots.push(k);
        }
    }
    if actions.is_empty() {
        return Err(format!("nothing to reveal in {name}: no unrevealed slot of this subject matches an opening kept in {}", root.join("market").join(name).display()));
    }
    propose_writes(root, ws, name, id, actions)?;
    eprintln!("reveal {id}: slot(s) {slots:?} of {name}");
    Ok(())
}

/// `market-bids`: what a signed read of the market shows, by phase.
pub(crate) fn show(root: &Path, ws: &Value, name: &str) -> Result<()> {
    workspace::validate_name(name)?;
    let (market, _) = read_market(root, ws, name)?;
    let close = market.close()?;
    let reveal_end = market.reveal_end()?;
    let supply = market.int(FIELD_SUPPLY)?;
    let settled = market.get(FIELD_SETTLED) == Some("1");
    let phase = if settled {
        "settled"
    } else if market.height < close {
        "sealed"
    } else if market.height < reveal_end {
        "reveal"
    } else {
        "settle"
    };
    println!("# market {name} at height {}: phase {phase}; sealed through {}, reveals {close}..{}, settle from {reveal_end}; supply {supply}; clearing price {}",
        market.height, close - 1, reveal_end - 1, market.get(FIELD_PRICE).unwrap_or("absent"));
    println!("slot\tbidder\tcommit\tprice\tqty\tfilled");
    for k in 0..SLOTS {
        match market.bid(k) {
            None => println!("{k}\t-\t-\t-\t-\t-"),
            Some(b) => {
                let short = &b.commit[..b.commit.len().min(16)];
                if b.revealed {
                    println!("{k}\t{}\t{short}…\t{}\t{}\t{}", b.who, b.price, b.qty, b.filled);
                } else {
                    println!("{k}\t{}\t{short}…\tsealed\tsealed\t{}", b.who, b.filled);
                }
            }
        }
    }
    Ok(())
}

/// `market-settle`: the runner. Reads the market at or after the reveal end,
/// when no reveal can land any more, and proposes the fills and the clearing
/// price in one write.
pub(crate) fn settle(root: &Path, ws: &Value, name: &str, id: &str) -> Result<()> {
    workspace::validate_name(name)?;
    let (market, _) = read_market(root, ws, name)?;
    let reveal_end = market.reveal_end()?;
    if market.height < reveal_end {
        return Err(format!("market {name} still admits reveals through height {}; settle from height {reveal_end} (this read is at {})", reveal_end - 1, market.height));
    }
    if market.get(FIELD_SETTLED) != Some("0") {
        return Err(format!("market {name} is already settled"));
    }
    let supply = market.int(FIELD_SUPPLY)?;
    let bids: Vec<Bid> = (0..SLOTS).filter_map(|k| market.bid(k)).collect();
    let (price, fills) = clear(supply, &bids);
    let mut actions = vec![scalar(FIELD_SETTLED, "1", Some("0")), scalar(FIELD_PRICE, &price.to_string(), Some("0"))];
    for (k, take) in &fills {
        actions.push(scalar(slot_fields(*k).filled, &take.to_string(), Some("0")));
    }
    propose_writes(root, ws, name, id, actions)?;
    for b in &bids {
        let fill = fills.iter().find(|(k, _)| *k == b.slot).map_or(0, |(_, t)| *t);
        if b.revealed {
            eprintln!("settle {id}: slot {} ({}) price {} qty {} fills {fill}", b.slot, b.who, b.price, b.qty);
        } else {
            eprintln!("settle {id}: slot {} ({}) never revealed: skipped; deposit forfeit: {}", b.slot, b.who, DEPOSIT_UNAVAILABLE.split(':').next().unwrap_or(""));
        }
    }
    eprintln!("settle {id}: clearing price {price}, {} unit(s) of {supply} filled", fills.iter().map(|(_, t)| t).sum::<i128>());
    Ok(())
}

/// `law-show`: the installed law of a resource, as the Host renders it in the
/// shell grammar (`LawLeaf.renderClause`), so it parses back to the same law.
pub(crate) fn law_show(root: &Path, ws: &Value, name: &str) -> Result<()> {
    let reference = workspace::reference(root, name)?;
    let (view, _, _) = workspace::signed_view(root, ws, &reference, "policy")?;
    let text = view.get("text").and_then(Value::as_str).ok_or("the Host's policy view carries no rendered text")?;
    println!("{text}");
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn word_is_value_plus_two_to_the_255() {
        let mut zero = [0u8; 32];
        zero[0] = 0x80;
        assert_eq!(word(0), zero);
        let mut minus_one = [0xffu8; 32];
        minus_one[0] = 0x7f;
        assert_eq!(word(-1), minus_one);
        let mut five = zero;
        five[31] = 5;
        assert_eq!(word(5), five);
    }

    #[test]
    fn decimal_reads_big_endian() {
        assert_eq!(decimal(&[0, 0]), "0");
        assert_eq!(decimal(&[1, 0]), "256");
        assert_eq!(decimal(&[0xff; 32]), "115792089237316195423570985008687907853269984665640564039457584007913129639935");
    }

    /// The tuple encoding spelled byte by byte as `Pred/HashEqDigest.lean`
    /// `Opening.preimage` writes it, and its digest against an independent
    /// cSHAKE256 (pycryptodome 3.x, `cSHAKE256.new(data=pre,
    /// custom=b"DREGG.PRED.HASHEQ/v2").read(32)` read big-endian).
    #[test]
    fn preimage_is_the_lean_encoding() {
        let pre = preimage(7, &[("a".into(), 1), ("bc".into(), -2)], "r", "c", &[3u8; 32]);
        let mut want = vec![0, 0, 0, 0, 0, 0, 0, 7, 0, 0, 0, 2];
        want.extend([0, 0, 0, 1, b'a', 0, 0, 0, 2, b'b', b'c', 0, 0, 0, 1, b'r', 0, 0, 0, 1, b'c']);
        want.extend(word(1));
        want.extend(word(-2));
        want.extend([3u8; 32]);
        assert_eq!(pre, want);
        assert_eq!(
            decimal(&digest(&pre)),
            "80492377833301751961603678476176884904340112729930557653076777446549259047381"
        );
        assert_eq!(
            commitment(42, 0, 30, 5, &[9u8; 32]),
            "12055981034310026308302707111410730141128304386596676092732137171988717834915"
        );
    }

    #[test]
    fn commitment_binds_slot_values_and_blinder() {
        let r = [9u8; 32];
        let c = commitment(42, 0, 30, 5, &r);
        assert_eq!(c, commitment(42, 0, 30, 5, &r));
        assert_ne!(c, commitment(42, 0, 31, 5, &r));
        assert_ne!(c, commitment(42, 0, 30, 6, &r));
        assert_ne!(c, commitment(42, 0, 5, 30, &r));
        assert_ne!(c, commitment(42, 1, 30, 5, &r));
        assert_ne!(c, commitment(43, 0, 30, 5, &r));
        assert_ne!(c, commitment(42, 0, 30, 5, &[8u8; 32]));
    }

    fn b(slot: u64, price: i128, qty: i128, revealed: bool) -> Bid {
        Bid { slot, who: "1".into(), commit: "1".into(), price, qty, revealed, filled: 0 }
    }

    #[test]
    fn clearing_fills_by_price_then_slot_and_skips_the_sealed() {
        // supply 8: slot 2 (40 x 5) fills 5, slot 0 (30 x 5) fills 3, slot 3 unrevealed skips,
        // slot 1 (30 x 4) loses the tie to slot 0 and gets nothing; price = 30.
        let bids = [b(0, 30, 5, true), b(1, 30, 4, true), b(2, 40, 5, true), b(3, 99, 9, false)];
        assert_eq!(clear(8, &bids), (30, vec![(2, 5), (0, 3)]));
        assert_eq!(clear(100, &bids), (30, vec![(2, 5), (0, 5), (1, 4)]));
        assert_eq!(clear(5, &[b(0, 99, 9, false)]), (0, vec![]));
        assert_eq!(clear(5, &[b(0, 0, 9, true), b(1, 7, 0, true)]), (0, vec![]));
    }

    #[test]
    fn the_law_template_parses_for_every_binding() {
        let bound = law("77", 30, 40, 8).expect("the market law parses");
        let clauses = bound["predicates"].as_array().expect("a clause list");
        assert_eq!(clauses.len(), 3 + 4 * SLOTS as usize);
        let text = serde_json::to_string(&bound).unwrap();
        for k in 0..SLOTS {
            let f = slot_fields(k);
            let atom = json!({"type":"hashEq","values":[field_slot(f.price), field_slot(f.qty)],
                "blinder":field_slot(f.blinder),"commit":field_slot(f.commit)});
            assert!(text.contains(&serde_json::to_string(&atom).unwrap()), "slot {k} opens its own commit");
        }
        let height = |v: &str| json!({"type":"le","slot":"request/height","value":v});
        assert!(text.contains(&serde_json::to_string(&height("29")).unwrap()), "bids sealed through CLOSE - 1");
        assert!(text.contains(&serde_json::to_string(&height("39")).unwrap()), "reveals through REVEAL-END - 1");
        assert!(!text.contains("{FOUNDER}") && !text.contains("{CLOSE}") && !text.contains("{SUPPLY}"));
        assert!(text.contains(r#""value":"77""#), "the founder is bound");
        assert!(law("77", 30, 30, 8).is_err());
        assert!(law("77", 30, 40, 0).is_err());
    }

    #[test]
    fn fields_json_is_the_layout() {
        let file = std::fs::read_to_string(concat!(env!("CARGO_MANIFEST_DIR"), "/../../deploy/shell/templates/market/sealed/fields.json")).unwrap();
        let fields: Value = serde_json::from_str(&file).unwrap();
        let m = &fields["fields"];
        assert_eq!(m["settled"], json!(FIELD_SETTLED.to_string()));
        assert_eq!(m["close"], json!(FIELD_CLOSE.to_string()));
        assert_eq!(m["revealEnd"], json!(FIELD_REVEAL_END.to_string()));
        assert_eq!(m["supply"], json!(FIELD_SUPPLY.to_string()));
        assert_eq!(m["price"], json!(FIELD_PRICE.to_string()));
        for k in 0..SLOTS {
            let f = slot_fields(k);
            for (n, v) in [("who", f.who), ("commit", f.commit), ("price", f.price), ("qty", f.qty), ("blinder", f.blinder), ("filled", f.filled)] {
                assert_eq!(m[format!("b{k}-{n}")], json!(v.to_string()), "b{k}-{n}");
            }
        }
    }
}
