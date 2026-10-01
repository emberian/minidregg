//! The watcher's configuration: the asset, the book, the paging bound, where receipts live.
//!
//! ```json
//! { "asset": { "mint": "<base58>", "tokenProgram": "<base58>" },
//!   "book": [ { "index": 0, "address": "<base58>" } ],
//!   "enrol": { "index": 0, "journalFloor": 1000000, "cursorFile": "enrol-cursor.json" },
//!   "maxPages": 4, "pageSize": 25, "minEndpoints": 2,
//!   "receiptsDir": "receipts" }
//! ```
//!
//! `enrol` (optional; PAY.md §11.2/§11.9) names the book row reserved for first contact. Its
//! observations carry the transaction's memo; a credit under `journalFloor` (atomic units; PAY
//! §11.8 sets 1 DREGG) is not emitted. It is paged WITHOUT the `maxPages` bound, back to a
//! persistent cursor kept in `cursorFile` (default `enrol-cursor.json`, relative to this
//! file's directory). `index` must name a row of `book`: the address has one home.
//!
//! RPC endpoints are deliberately NOT here: they carry provider credentials and come from the
//! `PAY_RPC_ENDPOINTS` environment (PAY.md §3.5), or from `--rpc-fixture` in fixture mode.
//! A relative `receiptsDir` resolves against the config file's directory.

use std::collections::BTreeSet;
use std::path::{Path, PathBuf};

use serde_json::Value;

use crate::model::{unbase58, Key};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Asset {
    pub mint: Key,
    /// The program that owns the asset's token accounts. DATA, per asset: the legacy SPL Token
    /// program and Token-2022 are different values and neither is assumed.
    pub token_program: Key,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BookEntry {
    pub index: u64,
    pub address: Key,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Enrol {
    pub index: u64,
    /// Atomic units; an enrollment credit below it is never emitted.
    pub journal_floor: u64,
    pub cursor_file: PathBuf,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Config {
    pub asset: Asset,
    pub book: Vec<BookEntry>,
    pub enrol: Option<Enrol>,
    pub max_pages: usize,
    pub page_size: usize,
    pub min_endpoints: usize,
    pub receipts_dir: PathBuf,
}

/// `getSignaturesForAddress` accepts at most 1000 per page.
pub const MAX_PAGE_SIZE: usize = 1000;

impl Config {
    pub fn load(path: &Path) -> Result<Config, String> {
        let bytes = std::fs::read(path).map_err(|e| format!("config {}: {e}", path.display()))?;
        let value: Value = serde_json::from_slice(&bytes)
            .map_err(|e| format!("config {}: not JSON: {e}", path.display()))?;
        let base = path.parent().unwrap_or(Path::new("."));
        Config::from_json(&value, base)
    }

    pub fn from_json(value: &Value, base: &Path) -> Result<Config, String> {
        let object = value.as_object().ok_or("config is not an object")?;
        for key in object.keys() {
            if !matches!(
                key.as_str(),
                "asset" | "book" | "enrol" | "maxPages" | "pageSize" | "minEndpoints" | "receiptsDir"
            ) {
                return Err(format!("config has unknown field `{key}`"));
            }
        }
        let asset = value.get("asset").ok_or("config missing `asset`")?;
        let asset = Asset {
            mint: key_field(asset, "mint")?,
            token_program: key_field(asset, "tokenProgram")?,
        };
        let book_json = value
            .get("book")
            .and_then(Value::as_array)
            .ok_or("config missing `book` array")?;
        let mut book = Vec::with_capacity(book_json.len());
        let mut indices = BTreeSet::new();
        let mut addresses = BTreeSet::new();
        for row in book_json {
            let index = row
                .get("index")
                .and_then(Value::as_u64)
                .ok_or("book row missing integer `index`")?;
            let address = key_field(row, "address")?;
            if !indices.insert(index) {
                return Err(format!("book index {index} appears twice"));
            }
            // Two indices on one address would observe every transfer to it twice.
            if !addresses.insert(address) {
                return Err(format!("book address at index {index} appears twice"));
            }
            book.push(BookEntry { index, address });
        }
        book.sort_by_key(|e| e.index);
        let enrol = match value.get("enrol") {
            None => None,
            Some(e) => {
                let fields = e.as_object().ok_or("config `enrol` is not an object")?;
                if let Some(k) = fields
                    .keys()
                    .find(|k| !matches!(k.as_str(), "index" | "journalFloor" | "cursorFile"))
                {
                    return Err(format!("config `enrol` has unknown field `{k}`"));
                }
                let index = e
                    .get("index")
                    .and_then(Value::as_u64)
                    .ok_or("config `enrol.index` is not a non-negative integer")?;
                if !indices.contains(&index) {
                    return Err(format!("config `enrol.index` {index} names no book row"));
                }
                // No default: a money threshold comes from the tariff, never from here.
                let journal_floor = e
                    .get("journalFloor")
                    .and_then(Value::as_u64)
                    .ok_or("config `enrol.journalFloor` is not a non-negative integer")?;
                let cursor = match e.get("cursorFile") {
                    None => "enrol-cursor.json",
                    Some(v) => v.as_str().ok_or("config `enrol.cursorFile` is not a string")?,
                };
                Some(Enrol {
                    index,
                    journal_floor,
                    cursor_file: base.join(cursor),
                })
            }
        };
        let max_pages = usize_field(value, "maxPages", 4)?;
        let page_size = usize_field(value, "pageSize", 25)?;
        let min_endpoints = usize_field(value, "minEndpoints", 2)?;
        if max_pages == 0 {
            return Err("maxPages must be at least 1".into());
        }
        if page_size == 0 || page_size > MAX_PAGE_SIZE {
            return Err(format!("pageSize must be in 1..={MAX_PAGE_SIZE}"));
        }
        if min_endpoints == 0 {
            return Err("minEndpoints must be at least 1".into());
        }
        let receipts = value
            .get("receiptsDir")
            .and_then(Value::as_str)
            .ok_or("config missing `receiptsDir`")?;
        let receipts_dir = base.join(receipts);
        Ok(Config {
            asset,
            book,
            enrol,
            max_pages,
            page_size,
            min_endpoints,
            receipts_dir,
        })
    }
}

fn key_field(value: &Value, name: &str) -> Result<Key, String> {
    let raw = value
        .get(name)
        .and_then(Value::as_str)
        .ok_or_else(|| format!("config missing `{name}`"))?;
    unbase58::<32>(raw).ok_or_else(|| format!("config `{name}` is not a 32-byte base58 key"))
}

fn usize_field(value: &Value, name: &str, default: usize) -> Result<usize, String> {
    match value.get(name) {
        None => Ok(default),
        Some(v) => v
            .as_u64()
            .map(|n| n as usize)
            .ok_or_else(|| format!("config `{name}` is not a non-negative integer")),
    }
}
