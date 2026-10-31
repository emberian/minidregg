//! `mini apps`: the app market (docs/APP-MARKET-2026-10-27.md).
//!
//! The catalogue is a cached copy of the Sandstorm app index that `mini-market`
//! refreshes (`deploy/market/mini-market-fetch`); it is data, never
//! instructions. Identity comes from the signed package (the appId is the
//! signing key's hash, the packageId the first 16 bytes of the SPK's SHA-256),
//! so the catalogue shows the index's claims beside Mini's own verdict, written
//! by the worker's real ingest, and never calls a package verified by itself.
//!
//! The lifecycle verbs talk to the worker over its authenticated Unix socket
//! (`SO_PEERCRED` names the member); every reply is a decoded outcome: decided
//! or undecided with its exact retry, never a spinner that lies.

#[path = "apps_qualification.rs"]
mod qualification;

#[path = "apps_front.rs"]
pub(crate) mod front;
#[path = "apps_worker.rs"]
pub(crate) mod worker;

use crate::participant_namespace::{self, IdKind, Role};
mod interfaces;

use crate::{absolute, hex, path, Args, Result};
use serde_json::{json, Map, Value};
use std::collections::BTreeMap;
use std::fs;
use std::io::{BufRead, BufReader, Read, Write};
use std::path::{Path, PathBuf};
use std::sync::OnceLock;

pub(crate) const DEFAULT_INDEX: &str = "/var/lib/mini-market/index.json";
pub(crate) const DEFAULT_META: &str = "/var/lib/mini-market/meta";
pub(crate) const DEFAULT_VERDICTS: &str = "/var/lib/mini-apps/verdicts";
/// The running worker's ingest identity, beside the verdicts: the SHA-256 of the spk-host binary it drives.
/// A verdict is the ingest's answer, so it is valid only for the ingest that wrote it (`ingestKey`).
pub(crate) const INGEST_KEY_FILE: &str = "ingest-key";
pub(crate) const DEFAULT_WORKER_SOCKET: &str = "/run/mini-apps/worker.sock";
pub(crate) const INDEX_URL: &str = "https://app-index.sandstorm.io/apps/index.json";
pub(crate) const PACKAGE_URL: &str = "https://app-index.sandstorm.io/packages/";
pub(crate) const WORKER_PROTOCOL: &str = "mini-apps-worker-v1";
/// The index is 67 KiB today; a 4 MiB bound leaves room and refuses a flood.
const MAX_INDEX: usize = 4 * 1024 * 1024;
const MAX_REPLY: usize = 64 * 1024;
/// The standard import profile's raw bound (`spk-package-stream` `standard-v1`).
pub(crate) const STANDARD_RAW_BYTES: u64 = 256 * 1024 * 1024;
const MAX_TEXT: usize = 512;
const WORKER_VERBS: &[&str] = &[
    "list", "status", "install", "retry", "open", "stop", "start", "share", "export", "delete", "renew",
    "identities", "revoke-identity",
];

/// The flag a grammar positional is spelled as on the CLI (`mini apps share a4501 bob` is
/// `--grain a4501 --to bob`): one table for the CLI's positional reader, so the shell and the
/// command line take the same words.
pub(crate) fn positional_flag(argument: &str) -> &'static str {
    match argument {
        "TERM" => "term",
        "APP-ID|PACKAGE-ID" => "app",
        "REQUEST-ID" => "request-id",
        "GRAIN" => "grain",
        "MEMBER" => "to",
        "FILE" => "out",
        "TOKEN" => "token",
        _ => "arg",
    }
}

/// One catalogue entry: the index's claims about one app, bounded and typed.
#[derive(Clone, Debug, PartialEq)]
pub(crate) struct Entry {
    pub app_id: String,
    pub package_id: String,
    pub name: String,
    pub version: String,
    pub version_number: u64,
    pub author: String,
    pub upstream_author: String,
    pub short_description: String,
    pub categories: Vec<String>,
    pub web_link: String,
    pub code_link: String,
    pub created_at: String,
    /// Actual package build time and upstream release, recorded by our pinned
    /// packages. The store's createdAt is neither; old entries stay explicit
    /// "not reported" in the CLI and web instead of borrowing that timestamp.
    pub package_built_at: String,
    pub upstream_version: String,
    pub open_source: bool,
    /// Operator-pinned entries only (`index-check --local`): the whole raw
    /// SHA-256 of the package, the URL it is fetched from when it is not
    /// adopted from a box-local file, and the class the operator sized it to.
    pub pinned: Option<Pinned>,
}

/// What an operator-pinned entry carries beyond the index's claims. The
/// package identity is still the signed package's; the pin only says which
/// exact bytes the fetcher may put in the quarantine under this packageId.
#[derive(Clone, Debug, PartialEq)]
pub(crate) struct Pinned {
    pub sha256: String,
    pub package_url: Option<String>,
    pub class: Option<String>,
}

fn parse_pinned(value: &Value, package_id: &str) -> Result<Option<Pinned>> {
    let sha256 = match value.get("sha256") {
        None | Some(Value::Null) => return Ok(None),
        Some(Value::String(text)) if mini_sdk::hex::is_canonical_len(text, 32) => text.clone(),
        _ => return Err("pinned sha256 is not 64 lowercase hex digits".into()),
    };
    if !sha256.starts_with(package_id) {
        return Err(format!("pinned sha256 {sha256} does not start with packageId {package_id}"));
    }
    let package_url = match value.get("packageUrl") {
        None | Some(Value::Null) => None,
        Some(Value::String(url)) if url.starts_with("https://") && url.len() <= MAX_TEXT && !url.bytes().any(|b| b <= 0x20 || b == b'"') => Some(url.clone()),
        _ => return Err("pinned packageUrl must be a bounded https URL".into()),
    };
    let class = match value.get("class") {
        None | Some(Value::Null) => None,
        Some(Value::String(c)) if matches!(c.as_str(), "S" | "M" | "L") => Some(c.clone()),
        _ => return Err("pinned class is S, M or L".into()),
    };
    Ok(Some(Pinned { sha256, package_url, class }))
}

/// A Sandstorm appId: 52 base32 digits (`sandstorm_package::spk::base32`).
pub(crate) fn valid_app_id(text: &str) -> bool {
    text.len() == 52 && text.bytes().all(|b| b.is_ascii_lowercase() || b.is_ascii_digit())
}

/// A packageId: the first 16 bytes of the SPK's SHA-256, lowercase hex.
pub(crate) fn valid_package_id(text: &str) -> bool {
    mini_sdk::hex::is_canonical_len(text, 16)
}

fn bounded_text(value: &Value, key: &str, required: bool) -> Result<String> {
    match value.get(key) {
        None | Some(Value::Null) if !required => Ok(String::new()),
        // The index's own data has trailing newlines in versions: whitespace is
        // trimmed; any other control byte refuses the entry.
        Some(Value::String(text)) if text.len() <= MAX_TEXT && !text.trim().bytes().any(|b| b < 0x20) => {
            Ok(text.trim().to_owned())
        }
        Some(Value::String(_)) => Err(format!("index entry {key} is over {MAX_TEXT} bytes or holds control bytes")),
        _ => Err(format!("index entry lacks {key}")),
    }
}

fn parse_entry(value: &Value) -> Result<Entry> {
    let app_id = bounded_text(value, "appId", true)?;
    if !valid_app_id(&app_id) {
        return Err(format!("index appId {app_id:?} is not 52 base32 digits"));
    }
    let package_id = bounded_text(value, "packageId", true)?;
    if !valid_package_id(&package_id) {
        return Err(format!("index packageId {package_id:?} is not 32 lowercase hex digits"));
    }
    let name = bounded_text(value, "name", true)?;
    if name.is_empty() {
        return Err("index entry has an empty name".into());
    }
    let version_number = match value.get("versionNumber") {
        Some(Value::Number(n)) => n.as_u64().ok_or("index versionNumber is not a natural")?,
        _ => return Err("index entry lacks versionNumber".into()),
    };
    let author = match value.get("author") {
        Some(Value::Object(author)) => bounded_text(&Value::Object(author.clone()), "name", false)?,
        _ => String::new(),
    };
    let mut categories = Vec::new();
    if let Some(Value::Array(list)) = value.get("categories") {
        if list.len() > 16 {
            return Err("index entry names over 16 categories".into());
        }
        for item in list {
            match item {
                Value::String(text) if text.len() <= 64 => categories.push(text.clone()),
                _ => return Err("index category is not a short string".into()),
            }
        }
    }
    let pinned = parse_pinned(value, &package_id)?;
    Ok(Entry {
        app_id,
        package_id,
        name,
        version: bounded_text(value, "version", false)?,
        version_number,
        author,
        upstream_author: bounded_text(value, "upstreamAuthor", false)?,
        short_description: bounded_text(value, "shortDescription", false)?,
        categories,
        web_link: bounded_text(value, "webLink", false)?,
        code_link: bounded_text(value, "codeLink", false)?,
        created_at: bounded_text(value, "createdAt", false)?,
        package_built_at: bounded_text(value, "packageBuiltAt", false)?,
        upstream_version: bounded_text(value, "upstreamVersion", false)?,
        open_source: value.get("isOpenSource").and_then(Value::as_bool).unwrap_or(false),
        pinned,
    })
}

/// The index as the market serves it: `{"apps":[...]}`. Unknown keys are
/// ignored (the index may grow); a malformed entry refuses the whole file, so
/// a half-good index is never shown as the catalogue.
pub(crate) fn parse_index(bytes: &[u8]) -> Result<Vec<Entry>> {
    if bytes.len() > MAX_INDEX {
        return Err(format!("index exceeds {MAX_INDEX} bytes"));
    }
    let value: Value = serde_json::from_slice(bytes).map_err(|e| format!("index is not JSON: {e}"))?;
    let apps = value
        .get("apps")
        .and_then(Value::as_array)
        .ok_or("index lacks the apps array")?;
    let mut entries = Vec::with_capacity(apps.len());
    let mut seen = BTreeMap::new();
    for (position, app) in apps.iter().enumerate() {
        let entry = parse_entry(app).map_err(|e| format!("index entry {position}: {e}"))?;
        if let Some(first) = seen.insert(entry.package_id.clone(), position) {
            return Err(format!("index names packageId {} twice (entries {first} and {position})", entry.package_id));
        }
        entries.push(entry);
    }
    Ok(entries)
}

/// The exact known fields, re-serialised: what `index-check` writes. A pinned
/// entry carries its pin (`sha256`, `packageUrl`, `class`) so the fetcher and
/// the catalogue read it from the one index file.
pub(crate) fn render_index(entries: &[Entry]) -> Value {
    json!({"format":"mini-market-index-v1","source":INDEX_URL,"pinned":entries.iter().filter(|e| e.pinned.is_some()).count(),
        "apps":entries.iter().map(|e| {
        let mut app = json!({
        "appId":e.app_id,"packageId":e.package_id,"name":e.name,"version":e.version,
        "versionNumber":e.version_number,"author":{"name":e.author},"upstreamAuthor":e.upstream_author,
        "shortDescription":e.short_description,"categories":e.categories,"webLink":e.web_link,
        "codeLink":e.code_link,"createdAt":e.created_at,"packageBuiltAt":e.package_built_at,
        "upstreamVersion":e.upstream_version,"isOpenSource":e.open_source});
        if let Some(pin) = &e.pinned {
            app["sha256"] = json!(pin.sha256);
            if let Some(url) = &pin.package_url { app["packageUrl"] = json!(url); }
            if let Some(class) = &pin.class { app["class"] = json!(class); }
        }
        app
    }).collect::<Vec<_>>()})
}

/// `index-check --local`: the operator's pinned entries, merged after the
/// upstream index. Every local entry carries a `sha256`; a packageId the
/// upstream index already names is refused (the pin would shadow a public
/// package), so the one catalogue file never shows two sources for one id.
pub(crate) fn merge_local(upstream: Vec<Entry>, local: Vec<Entry>) -> Result<Vec<Entry>> {
    let mut entries = upstream;
    for entry in local {
        if entry.pinned.is_none() {
            return Err(format!("local entry {} ({}) carries no sha256 pin", entry.name, entry.package_id));
        }
        if let Some(first) = entries.iter().find(|e| e.package_id == entry.package_id) {
            return Err(format!("local entry {} collides with the index's {} ({})", entry.package_id, first.name, first.app_id));
        }
        entries.push(entry);
    }
    Ok(entries)
}

pub(crate) fn load_index(path: &Path) -> Result<Vec<Entry>> {
    let bytes = crate::fsio::read_bounded(path, MAX_INDEX)
        .map_err(|e| format!("no market index at {} ({e}); mini-market refreshes it", path.display()))?;
    parse_index(&bytes)
}

/// Resolve one entry by appId or packageId; `unknownApp` names the refusal.
pub(crate) fn resolve<'a>(entries: &'a [Entry], selector: &str) -> Result<&'a Entry> {
    let found = if valid_app_id(selector) {
        entries.iter().find(|e| e.app_id == selector)
    } else if valid_package_id(selector) {
        entries.iter().find(|e| e.package_id == selector)
    } else {
        return Err(format!("unknownApp: {selector:?} is neither a 52-digit appId nor a 32-hex packageId"));
    };
    found.ok_or_else(|| format!("unknownApp: {selector} is not in the market index"))
}

/// Case-insensitive substring search over the index's text fields.
/// The demo's featured set (docs/APP-MARKET-2026-10-27.md section 2a), in the
/// order the market shows it: apps chosen for the data model and the scriptable
/// capabilities. Ordering alone makes no claim about an installed attachment.
/// App IDs determine curated order only; typed capabilities come from declarations.
pub(crate) const FEATURED: &[&str] = &[
    "ksyn7qa4szjwa14v89r7znxwrpjs0dez5q2u8s810d0awnuswmfh",
    "umpy9re0saa7vtckd6mnprv6mc5vjgr0qh5qucs4na3qjrxrrzch",
    "a0wt1wk03g737k60grvphm2rxy9yjnkev8g4jjj9zgu9mm3ggay0",
    "g9vdgqnn4dnj6r7tyaw9duydgmgskxzq9564fxceekqhvcds33zh",
    "f3s5vv8g7xuay08e3x1g5zwuaycz0mt7170nmz3kf5e1g1q9ytr0",
    "k2drffaa4xx1mq1gz6hh5cnw2kfqr6mkpvz51h54xkp4eawx6wn0",
    "f3c9rjszvmqgvnhan8c6m5cpwkqmwu6t6de0qxa8vnx0rqreafqh",
    "j4jvn386t7un76qu6yyw1vwc5ke50t07e38r82kzy4qqg6qq7msh",
    "3g05nj7mpryyd3a0erndy30my7fsr72s3xghnhewkqw7km08g34h",
    "894fztp7d6e4u8fgw2qtm8jv904jw6w19frfqgc0pwytj0q10s80",
    "vku2z06we4n4cfpvn28y6159fsgft9nttvvfeg1wndu8szvrtm3h",
    "wpe8yvzdpjsst9314ucecmpmyzju0830ujm815ew5mjuen173kg0",
    "1mvdqjv5z596dtyg5fh0p9573x32u5anrfze9rs6wpxthhyejk50",
    "1124qk4mm5zvx294gwn9w23gn2pt96mds6pqkxpn9sxr8w2uwr70",
    "xm16d84ksseg44ef58z7n2aw7qt1n6psk0cewzr0e0arfjk5r4fh",
    "7xx4myv7aafdqtm4rh4fj3ju1eck9dfqnnjca3y6513gradphzv0",
    "cvs53nmnfn463htz3yyyr8zunufczacrdg31n14j61n7g4dpeadh",
    "1xs63fcv99c08dv2tgv0dcehjka9141e1egcafffuu0txskvzmq0",
    "reh7pa3e7jt8ryvjgje97ke5rkyztfg70grru8dewevmunj6ugn0",
    "vhq5azzdxf68v536fh0je6ckz6wp56f82t3swt2ws3x91nwk19ch",
    "cd6fk64x5ndeem7ya2t3qfjkjsjjhts5y2eg54jpdy0g0whtwx40",
];

pub(crate) fn featured(app_id: &str) -> Option<usize> {
    FEATURED.iter().position(|id| *id == app_id).map(|rank| rank + 1)
}

/// Matching entries, the featured set first in its order, then the rest of the
/// store in index order.
pub(crate) fn search<'a>(entries: &'a [Entry], term: &str, category: Option<&str>) -> Vec<&'a Entry> {
    let mut found = search_unordered(entries, term, category);
    found.sort_by_key(|e| featured(&e.app_id).unwrap_or(usize::MAX));
    found
}

fn search_unordered<'a>(entries: &'a [Entry], term: &str, category: Option<&str>) -> Vec<&'a Entry> {
    let term = term.to_lowercase();
    entries
        .iter()
        .filter(|e| {
            category.is_none_or(|c| e.categories.iter().any(|k| k.eq_ignore_ascii_case(c)))
        })
        .filter(|e| {
            term.is_empty()
                || [&e.name, &e.short_description, &e.author, &e.upstream_author, &e.app_id, &e.package_id]
                    .iter()
                    .any(|field| field.to_lowercase().contains(&term))
        })
        .collect()
}

/// Mini's verdict on a package: what the worker's real ingest recorded, or
/// `unverified` when this box has never parsed it. The fetcher's meta file adds
/// the raw size when the package was fetched.
#[derive(Clone, Debug, PartialEq)]
pub(crate) struct Verdict {
    pub state: String,
    pub reason: Option<String>,
    pub raw_bytes: Option<u64>,
    pub signed_app_id: Option<String>,
    pub running: u64,
}

pub(crate) fn verdict(verdicts: &Path, meta: &Path, package_id: &str) -> Verdict {
    let mut out = Verdict { state: "unverified".into(), reason: None, raw_bytes: None, signed_app_id: None, running: 0 };
    if let Ok(bytes) = crate::fsio::read_bounded(&meta.join(format!("{package_id}.json")), 16 * 1024) {
        if let Ok(value) = serde_json::from_slice::<Value>(&bytes) {
            out.raw_bytes = value.get("bytes").and_then(Value::as_u64);
            if out.raw_bytes.is_some_and(|b| b > STANDARD_RAW_BYTES) {
                out.state = "refused".into();
                out.reason = Some("sizeOverProfile".into());
            }
        }
    }
    // The worker publishes the key of the ingest it runs; a verdict written by another ingest (an older
    // candidate's refusal that survived a re-genesis) is absent, so the install is attempted again.
    // With no key published yet (no worker has started here) every verdict is read as before.
    let current = crate::fsio::read_bounded(&verdicts.join(INGEST_KEY_FILE), 128)
        .ok()
        .and_then(|bytes| String::from_utf8(bytes).ok())
        .map(|text| text.trim().to_owned())
        .filter(|text| !text.is_empty());
    if let Ok(bytes) = crate::fsio::read_bounded(&verdicts.join(format!("{package_id}.json")), 16 * 1024) {
        if let Ok(value) = serde_json::from_slice::<Value>(&bytes) {
            let written_by_this_ingest = current.as_deref().map_or(true, |key| value.get("ingestKey").and_then(Value::as_str) == Some(key));
            if !written_by_this_ingest {
                return out;
            }
            if let Some(state) = value.get("verdict").and_then(Value::as_str) {
                out.state = state.to_owned();
            }
            out.reason = value.get("reason").and_then(Value::as_str).map(str::to_owned);
            out.signed_app_id = value.get("signedAppId").and_then(Value::as_str).map(str::to_owned);
            out.running = value.get("running").and_then(Value::as_u64).unwrap_or(0);
        }
    }
    out
}

/// The broker's size class the worker would pick from the raw size: S under
/// 64 MiB, M under 256 MiB (the standard profile's whole budget), else L.
pub(crate) fn suggested_class(raw_bytes: Option<u64>) -> &'static str {
    match raw_bytes {
        None => "unknown until fetched",
        Some(b) if b < 64 * 1024 * 1024 => "S",
        Some(b) if b <= STANDARD_RAW_BYTES => "M",
        Some(_) => "refused: sizeOverProfile",
    }
}

pub(crate) fn entry_json(entry: &Entry, verdict: &Verdict) -> Value {
    let mut interface = typed_interface(entry);
    interface["says"] = json!(tools_says(interface["status"].as_str().unwrap_or("unavailable")));
    json!({
        "appId":entry.app_id,"packageId":entry.package_id,"name":entry.name,"version":entry.version,
        "interface":interfaces::summary(&entry.app_id, &entry.package_id),
        "versionNumber":entry.version_number,"publisher":entry.author,"upstreamAuthor":entry.upstream_author,
        "packageBuiltAt":entry.package_built_at,"upstreamVersion":entry.upstream_version,
        "shortDescription":entry.short_description,"categories":entry.categories,"webLink":entry.web_link,
        "codeLink":entry.code_link,"packageUrl":package_url(entry),
        "verdict":{"state":verdict.state,"reason":verdict.reason,"rawBytes":verdict.raw_bytes,
            "signedAppId":verdict.signed_app_id,"running":verdict.running,"says":verdict_says(verdict)},
        "suggestedClass":entry.pinned.as_ref().and_then(|p| p.class.as_deref()).unwrap_or_else(|| suggested_class(verdict.raw_bytes)),
        "pinned":entry.pinned.as_ref().map(|p| json!({"sha256":p.sha256,"packageUrl":p.package_url,"class":p.class})),
        "featured":featured(&entry.app_id).map(|rank| json!({"rank":rank})),
        "typedInterface":interface,
        "claims":"name, version, publisher and links are the index's claims; identity is the signed package's"
    })
}

fn qualified_entry_json(entry: &Entry, verdict: &Verdict, qualification: &qualification::Qualification) -> Value {
    let mut value = entry_json(entry, verdict);
    value["qualification"] = qualification.get(entry).cloned().unwrap_or(Value::Null);
    value
}

fn typed_interface(entry: &Entry) -> Value {
    let mut packages = Vec::new();
    for (source, value) in interfaces::declarations() {
        if value["format"] != "mini-app-interface-v1" || value["appId"] != entry.app_id {
            continue;
        }
        if let Some(package) = value["packageId"].as_str() { packages.push(package.to_owned()); }
        if value["packageId"] != entry.package_id { continue; }
        let declaration = match mini_sdk::app_interface::Declaration::load(source.as_bytes()) {
            Ok(declaration) => declaration,
            Err(_) => return json!({"status":"declaration-invalid","schemaAvailable":false}),
        };
        let tools = match declaration.tools() {
            Ok(tools) => tools,
            Err(_) => return json!({"status":"declaration-invalid","schemaAvailable":false}),
        };
        return json!({"status":"native-attachment-required","schemaAvailable":true,
            "name":value["name"],"packageId":declaration.package_id,
            "interfaceSha256":declaration.sha256,"tools":tools});
    }
    if packages.is_empty() {
        json!({"status":"declaration-unavailable","schemaAvailable":false})
    } else {
        json!({"status":"package-mismatch","schemaAvailable":false,"declaredPackageIds":packages})
    }
}
fn interface_summary(entry: &Entry) -> String {
    let interface = typed_interface(entry);
    match interface["tools"].as_array() {
        Some(tools) => format!("\n      {} typed tools; native attachment required", tools.len()),
        None => format!("\n      {}", tools_says(interface["status"].as_str().unwrap_or("unavailable"))),
    }
}
fn print_interface(entry: &Entry) {
    let interface = typed_interface(entry);
    println!("  typed tools {}", interface["status"].as_str().unwrap_or("unavailable"));
    if let Some(tools) = interface["tools"].as_array() {
        println!("  interface {} (package {})", interface["interfaceSha256"].as_str().unwrap_or(""), entry.package_id);
        for tool in tools {
            println!("    {}: {}", tool["operation"].as_str().unwrap_or(""), tool["description"].as_str().unwrap_or(""));
        }
        println!("  Attach this package on a live grain under current member grants to use its tools.");
    }
}

/// Where the fetcher takes the package from: the pin's URL, the market's
/// package URL, or (a pin without a URL) a box-local file the operator adopts.
fn package_url(entry: &Entry) -> String {
    match &entry.pinned {
        Some(Pinned { package_url: Some(url), .. }) => url.clone(),
        Some(_) => format!("file: adopted by the operator (mini-market-fetch adopt {} SHA256 FILE)", entry.package_id),
        None => format!("{PACKAGE_URL}{}", entry.package_id),
    }
}

/// The verdict as a member reads it, with what they can do. `unverified` is not a fault: nothing on
/// this box has parsed the package yet, and the install is what checks it (signature, signed app id,
/// size) before anything runs, so it can be installed now. `refused` keeps its reason.
pub(crate) fn verdict_says(verdict: &Verdict) -> String {
    match verdict.state.as_str() {
        "unverified" => "not checked on this box yet: installing it checks its signature and size first (`apps install`)".into(),
        "refused" => format!("refused here{}: an install is refused the same way",
            verdict.reason.as_deref().map(|r| format!(" ({r})")).unwrap_or_default()),
        _ => verdict_line(verdict),
    }
}

/// The typed-tools status as a member reads it: an app without a declaration is used through its
/// own web page (an agent cannot call typed tools on it), never broken.
pub(crate) fn tools_says(status: &str) -> String {
    match status {
        "declaration-unavailable" => "no typed tools declared: use it through its own page; agents cannot call it as tools".into(),
        "package-mismatch" => "typed tools are declared for another version of this package, not this one".into(),
        "declaration-invalid" => "its typed-tool declaration does not parse here; use it through its own page".into(),
        "native-attachment-required" => "typed tools declared; an agent can call them once the app is installed and attached".into(),
        other => other.to_owned(),
    }
}

fn verdict_line(verdict: &Verdict) -> String {
    let mut line = verdict.state.clone();
    if let Some(reason) = &verdict.reason {
        line.push_str(": ");
        line.push_str(reason);
    }
    if verdict.running > 0 {
        line.push_str(&format!(", running {}", verdict.running));
    }
    line
}

struct Paths {
    qualification: Option<PathBuf>,
    index: PathBuf,
    meta: PathBuf,
    verdicts: PathBuf,
    socket: PathBuf,
    config: PathBuf,
}

fn paths(args: &mut Args) -> Paths {
    let from = |args: &mut Args, flag: &str, env: &str, default: &str| {
        args.optional(flag)
            .map(PathBuf::from)
            .or_else(|| std::env::var_os(env).map(PathBuf::from))
            .unwrap_or_else(|| PathBuf::from(default))
    };
    Paths {
        qualification: args.optional("qualification").map(PathBuf::from)
            .or_else(|| std::env::var_os("MINI_APPS_QUALIFICATION").map(PathBuf::from)),
        index: from(args, "index", "MINI_MARKET_INDEX", DEFAULT_INDEX),
        meta: from(args, "meta", "MINI_MARKET_META", DEFAULT_META),
        verdicts: from(args, "verdicts", "MINI_APPS_VERDICTS", DEFAULT_VERDICTS),
        socket: from(args, "worker-socket", "MINI_APPS_WORKER_SOCKET", DEFAULT_WORKER_SOCKET),
        config: from(args, "apps-config", "MINI_APPS_CONFIG", DEFAULT_APPS_CONFIG),
    }
}

fn text_flag(args: &mut Args, name: &str) -> Result<Option<String>> {
    args.optional(name)
        .map(|v| v.into_string().map_err(|_| format!("--{name} must be UTF-8")))
        .transpose()
}

/// One request to the worker, one bounded reply line. The worker names the
/// member by `SO_PEERCRED`; nothing in the request claims an identity.
pub(crate) fn worker_call(socket: &Path, request: &Value) -> Result<Value> {
    let mut stream = std::os::unix::net::UnixStream::connect(socket).map_err(|e| {
        format!("appsWorkerUnavailable: {} ({e}); the install is not started, retry when the worker is up", socket.display())
    })?;
    stream
        .set_read_timeout(Some(std::time::Duration::from_secs(120)))
        .map_err(|e| e.to_string())?;
    let mut line = serde_json::to_vec(request).map_err(|e| e.to_string())?;
    line.push(b'\n');
    stream.write_all(&line).map_err(|e| format!("worker request not delivered: {e}"))?;
    let mut reader = BufReader::new(stream);
    let mut reply = Vec::new();
    reader
        .by_ref()
        .take(MAX_REPLY as u64 + 1)
        .read_until(b'\n', &mut reply)
        .map_err(|e| format!("worker reply lost after the request was sent; the outcome is undecided: retry the same request id ({e})"))?;
    if reply.len() > MAX_REPLY {
        return Err("worker reply exceeds 64 KiB".into());
    }
    if reply.is_empty() {
        return Err("worker closed without a reply; the outcome is undecided: retry the same request id".into());
    }
    let value: Value = serde_json::from_slice(&reply).map_err(|e| format!("worker reply is not JSON: {e}"))?;
    if value.get("protocol").and_then(Value::as_str) != Some(WORKER_PROTOCOL) {
        return Err("worker reply carries another protocol".into());
    }
    Ok(value)
}

/// Render a worker reply as a decoded outcome. Exit status: 0 decided and
/// performed, 1 decided refused, 3 undecided (the exact retry is printed).
/// The amount this install actually reserved on the world's tool task (set once the reservation
/// is confirmed); the receipt's `budget` line.
static INSTALL_BUDGET: std::sync::OnceLock<String> = std::sync::OnceLock::new();

fn report(reply: &Value, as_json: bool) -> Result<()> {
    let mut reply = reply.clone();
    if let (Some(amount), Some(object)) = (INSTALL_BUDGET.get(), reply.as_object_mut()) {
        if object.contains_key("receipt") {
            object.insert("budget".into(), json!({"toolReservation":amount,"from":"the world's metered tool task (released by settle 0 if the birth is refused)",
                "birthFee":"debited from the member's own account by the Host's resource-birth tariff"}));
        }
    }
    let reply = &reply;
    if as_json {
        println!("{}", serde_json::to_string_pretty(reply).map_err(|e| e.to_string())?);
    }
    let decided = reply.get("decided").and_then(Value::as_bool);
    let state = reply.get("state").and_then(Value::as_str).unwrap_or("?");
    let detail = reply.get("detail").and_then(Value::as_str).unwrap_or("");
    match decided {
        Some(true) if reply.get("refused").and_then(Value::as_str).is_none() => {
            if !as_json {
                println!("{state}: {detail}");
                if let Some(receipt) = reply.get("receipt") {
                    println!("receipt: {receipt}");
                }
                if let Some(amount) = INSTALL_BUDGET.get() {
                    println!("budget: {amount} units reserved on the world's tool task; the birth fee came from your own account");
                }
            }
            Ok(())
        }
        Some(true) => {
            let reason = reply.get("refused").and_then(Value::as_str).unwrap_or("refused");
            Err(format!("{reason}: {detail}"))
        }
        _ => {
            let retry = reply.get("exactRetry").and_then(Value::as_str).unwrap_or("mini apps status");
            Err(format!("undecided: {state} {detail}; exact retry: {retry}"))
        }
    }
}

fn request_id() -> Result<String> {
    Ok(hex(&crate::fsio::random::<16>()?))
}

/// `install`: the member's choice, retained under the workspace before it is
/// sent, so a lost reply is answered by the exact retry of the same id.
fn install(mut args: Args, paths: &Paths, as_json: bool, dir: Option<std::ffi::OsString>) -> Result<()> {
    let selector = text_flag(&mut args, "app")?.ok_or("install requires --app APP-ID|PACKAGE-ID")?;
    let class = text_flag(&mut args, "class")?.unwrap_or_else(|| "auto".into());
    if !matches!(class.as_str(), "S" | "M" | "L" | "auto") {
        return Err("classRefused: --class takes S, M or L".into());
    }
    let root = absolute(&path(dir.ok_or("missing --dir")?))?;
    // The member's session home (the shell passes it): HOME/inbox holds the delegated
    // references the frame leaves at enrolment.
    let home = args.optional("home").map(|v| absolute(&path(v))).transpose()?
        .or_else(|| std::env::var_os("MINI_HOME").map(PathBuf::from));
    let retry = text_flag(&mut args, "retry")?;
    let birth_source = args.optional("birth-source").map(|v| absolute(&path(v))).transpose()?;
    let birth_receipt = args.optional("birth-receipt").map(|v| absolute(&path(v))).transpose()?;
    let delegation = args.optional("delegation").map(|v| absolute(&path(v))).transpose()?;
    args.finish()?;
    let entries = load_index(&paths.index)?;
    let entry = resolve(&entries, &selector)?;
    let verdict = verdict(&paths.verdicts, &paths.meta, &entry.package_id);
    if verdict.state == "refused" {
        return Err(format!(
            "{}: {} {} was refused by this box's ingest; nothing to install",
            verdict.reason.as_deref().unwrap_or("refused"),
            entry.name,
            entry.package_id
        ));
    }
    let requests = root.join("apps").join("requests");
    crate::fsio::ensure_private_dir_all(&requests)?;
    let is_retry = retry.is_some();
    let (id, retained) = match retry {
        Some(id) => {
            if !mini_sdk::hex::is_canonical_len(&id, 16) {
                return Err("--retry takes the 32-hex request id the first attempt printed".into());
            }
            let retained = crate::workspace::bounded_json(&requests.join(format!("{id}.json")))?;
            (id, retained)
        }
        None => {
            let id = request_id()?;
            let apps_dir = root.join("apps").join(&entry.app_id);
            let mut source = birth_source.unwrap_or_else(|| apps_dir.join("birth").join("source.json"));
            let mut receipt = birth_receipt.unwrap_or_else(|| apps_dir.join("birth").join("outcome.json"));
            let mut delegation = delegation.unwrap_or_else(|| apps_dir.join("delegation.json"));
            // The member turn (§3 steps 1 and 2): the application birth as the member's own op 30
            // and the hosting delegation to the manager, unless retained documents are supplied.
            if !(source.is_file() && receipt.is_file() && delegation.is_file()) {
                let config = apps_config(&paths.config)?;
                let ws = crate::workspace::load(&root)?;
                // The birth is named by the catalog application, not by this request: a retry after an
                // attempt that stopped between the birth and the hosting delegation must resume that
                // birth, not make a second one whose delegation is then filed beside the first one's
                // source (the worker refuses such a pair: "lifecycle delegation differs from application
                // birth"). The hosting delegation's request id follows the same rule.
                let stem = &entry.app_id[..entry.app_id.len().min(12)];
                let name = format!("app-{stem}");
                let (born_source, born_receipt) = app_birth(&root, &ws, home.as_deref(), &name, &config)?;
                crate::fsio::ensure_private_dir_all(&apps_dir.join("birth"))?;
                source = apps_dir.join("birth").join("source.json");
                receipt = apps_dir.join("birth").join("outcome.json");
                // The three documents travel as one set for ONE birth. Files retained from another
                // birth (a legacy attempt named by its request) are replaced, never mixed in.
                let same_birth = retained_birth_is(&source, &receipt, &born_source);
                for (file, value) in [(&source, &born_source), (&receipt, &born_receipt)] {
                    if !same_birth || !file.exists() {
                        crate::fsio::replace_private(file, &serde_json::to_vec_pretty(value).map_err(|e| e.to_string())?)?;
                    }
                }
                let selector = delegate_lifecycle(&root, &name, &format!("apps-{stem}"), &config.management_subject)?;
                let selector_doc: Value = serde_json::from_slice(&crate::fsio::read_bounded(&selector, 64 * 1024)?)
                    .map_err(|e| format!("{}: {e}", selector.display()))?;
                delegation = apps_dir.join("delegation.json");
                let delegation_current = delegation_names_app(&delegation, &selector_doc);
                let delegation_stale = delegation.is_file() && !delegation_current;
                if !delegation_current {
                    crate::fsio::replace_private(&delegation, &serde_json::to_vec_pretty(&selector_doc).map_err(|e| e.to_string())?)?;
                }
                // The manager issues share tickets, so it must hold a delegate-capable child of the owner's
                // app capability; the member delegates it now and the worker issues under it.
                let share = apps_dir.join("share-delegation.json");
                if !share.exists() || !same_birth || delegation_stale {
                    let max = born_source.pointer("/applicationGrainBirth/applicationBirth/template/ownerBudget").and_then(Value::as_str).unwrap_or("100000").to_owned();
                    let child = delegate_share(&root, &ws, &name, &config.management_subject, &max)?;
                    crate::fsio::replace_private(&share, &serde_json::to_vec_pretty(&child).map_err(|e| e.to_string())?)?;
                }
            }
            // The worker cannot read a member's 0700 home: the three documents travel
            // in the request (bounded), and the worker re-checks them against the Store.
            let document = |file: &Path| -> Result<Value> {
                let bytes = crate::fsio::read_bounded(file, 64 * 1024)?;
                serde_json::from_slice(&bytes).map_err(|e| format!("{}: {e}", file.display()))
            };
            let delegation_doc = document(&delegation)?;
            // The member's signed choice: the request cell under law.apps (§3 step 3),
            // its manager the delegation's. A class of auto is recorded once the worker
            // sizes it, so the cell takes S/M/L only; auto births it after the receipt.
            let manager = delegation_doc.get("managementSubject").and_then(Value::as_str).ok_or("delegationRefused: the delegation names no managementSubject")?.to_owned();
            let request_cell_name = format!("apps-{}", &id[..12]);
            let cell = if class == "auto" { Value::Null } else {
                let ws = crate::workspace::load(&root)?;
                request_cell(&root, &ws, &request_cell_name, &entry.package_id, &entry.app_id, &class, &manager)?
            };
            let retained = json!({
                "protocol":WORKER_PROTOCOL,"verb":"install","requestId":id,
                "appId":entry.app_id,"packageId":entry.package_id,"class":class,
                "birthSource":document(&source)?,"birthReceipt":document(&receipt)?,"delegation":delegation_doc,
                "shareDelegation":document(&delegation.with_file_name("share-delegation.json"))?,
                "requestCell":cell,"indexName":entry.name,"indexVersion":entry.version
            });
            let file = requests.join(format!("{id}.json"));
            crate::workspace::atomic_json(&file, &retained, None)?;
            (id, retained)
        }
    };
    let mut request = retained.clone();
    request["verb"] = json!(if is_retry { "retry" } else { "install" });
    // The worker answers an install at once (`pending` while it runs); a reply lost after the
    // request was sent leaves the request with the worker, so the member is shown its follow-up.
    let reply = worker_call(&paths.socket, &request).map_err(|error| {
        if error.starts_with("worker reply lost") || error.starts_with("worker closed without") {
            format!("undecided: request {id} was sent and the worker may be running it; it continues without this command ({error}); exact retry: mini apps install --app {} --retry {id}", entry.app_id)
        } else {
            error
        }
    })?;
    let outcome = requests.join(format!("{id}.outcome.json"));
    crate::workspace::atomic_json(&outcome, &reply, None).or_else(|_| {
        // A second reply for the same id (the exact retry) replaces nothing:
        // the first retained outcome stands and this one is kept beside it.
        crate::workspace::atomic_json(&requests.join(format!("{id}.outcome.{}.json", request_id()?)), &reply, None)
    })?;
    if !as_json {
        println!("request {id}: {} {} ({})", entry.name, entry.version, entry.package_id);
    }
    report(&reply, as_json)
}


fn catalogue(action: &str, mut args: Args, paths: &Paths, as_json: bool) -> Result<()> {
    // Every flag is consumed before the index is read: an unconsumed one is a usage error first.
    let (term, category, selector) = match action {
        "search" => (text_flag(&mut args, "term")?.unwrap_or_default(), text_flag(&mut args, "category")?, None),
        _ => (String::new(), None, Some(text_flag(&mut args, "app")?.ok_or("show requires --app APP-ID|PACKAGE-ID")?)),
    };
    args.finish()?;
    let entries = load_index(&paths.index)?;
    let qualification = qualification::Qualification::load(paths.qualification.as_deref())?;
    match action {
        "search" => {
            let found = search(&entries, &term, category.as_deref());
            if as_json {
                let list: Vec<Value> = found
                    .iter()
                    .map(|e| qualified_entry_json(e, &verdict(&paths.verdicts, &paths.meta, &e.package_id), &qualification))
                    .collect();
                println!("{}", serde_json::to_string_pretty(&json!({"apps":list,"total":entries.len()})).map_err(|e| e.to_string())?);
                return Ok(());
            }
            println!("{} of {} apps ({}):", found.len(), entries.len(), paths.index.display());
            let mut rest_heading = false;
            for e in found {
                let v = verdict(&paths.verdicts, &paths.meta, &e.package_id);
                let rank = featured(&e.app_id);
                if rank.is_none() && !rest_heading {
                    println!("  -- the rest of the store --");
                    rest_heading = true;
                }
                println!(
                    "  {}{:<28} {:<22} {:<24} {} [{}]{}",
                    if rank.is_some() { "featured " } else { "" },
                    truncate(&e.name, 28),
                    truncate(&e.version, 22),
                    truncate(&e.author, 24),
                    e.app_id,
                    format!("{}; {}", verdict_says(&v), qualification::line(qualification.get(e))),
                    interface_summary(e)
                );
            }
            Ok(())
        }
        "show" => {
            let selector = selector.unwrap_or_default();
            let entry = resolve(&entries, &selector)?;
            let v = verdict(&paths.verdicts, &paths.meta, &entry.package_id);
            let value = qualified_entry_json(entry, &v, &qualification);
            if as_json {
                println!("{}", serde_json::to_string_pretty(&value).map_err(|e| e.to_string())?);
                return Ok(());
            }
            println!("{} {} (index claim; the signed manifest decides)", entry.name, entry.version);
            println!("  appId      {}", entry.app_id);
            println!("  packageId  {}  ({})", entry.package_id, package_url(entry));
            println!("  publisher  {}  upstream {}", entry.author, entry.upstream_author);
            println!("  built      {}  upstream version {}",
                if entry.package_built_at.is_empty() { "not reported" } else { &entry.package_built_at },
                if entry.upstream_version.is_empty() { "not reported" } else { &entry.upstream_version });
            println!("  about      {}", entry.short_description);
            println!("  categories {}", entry.categories.join(", "));
            println!("  links      {}  {}", entry.web_link, entry.code_link);
            println!("  verdict    {}", verdict_line(&v));
            println!("  sweep      {}", qualification::line(qualification.get(entry)));
            println!("  size       {}", v.raw_bytes.map_or("not fetched here".to_owned(), |b| format!("{b} bytes raw")));
            match &entry.pinned {
                Some(pin) => println!("  class      {}  (operator-pinned; sha256 {})", pin.class.as_deref().unwrap_or(suggested_class(v.raw_bytes)), pin.sha256),
                None => println!("  class      {}", suggested_class(v.raw_bytes)),
            }
            print_interface(entry);
            println!("  refusals an install can meet: unknownApp, sizeOverProfile, unverifiedSignature, appIdMismatch, unsupportedBridge, funding, classRefused");
            Ok(())
        }
        _ => unreachable!(),
    }
}

fn truncate(text: &str, width: usize) -> String {
    if text.chars().count() <= width {
        text.to_owned()
    } else {
        let mut out: String = text.chars().take(width - 1).collect();
        out.push('…');
        out
    }
}

/// `index-check --in RAW --out INDEX`: the fetcher's validation step. The raw
/// download is parsed, the known fields re-serialised and published by rename,
/// so the catalogue file is always one Mini re-rendered the way it reads it.
fn index_check(mut args: Args) -> Result<()> {
    let input = absolute(&path(args.required("in")?))?;
    let output = absolute(&path(args.required("out")?))?;
    let local = args.optional("local").map(|v| absolute(&path(v))).transpose()?;
    args.finish()?;
    let bytes = crate::fsio::read_bounded(&input, MAX_INDEX)?;
    let mut entries = parse_index(&bytes)?;
    if let Some(local) = local {
        let pinned = parse_index(&crate::fsio::read_bounded(&local, MAX_INDEX)?)
            .map_err(|e| format!("local index {}: {e}", local.display()))?;
        entries = merge_local(entries, pinned)?;
    }
    let rendered = render_index(&entries);
    let mut text = serde_json::to_vec_pretty(&rendered).map_err(|e| e.to_string())?;
    text.push(b'\n');
    let temp = output.with_extension("json.new");
    fs::write(&temp, &text).map_err(|e| format!("cannot write {}: {e}", temp.display()))?;
    fs::rename(&temp, &output).map_err(|e| format!("cannot publish {}: {e}", output.display()))?;
    println!("index-check: {} apps ({} pinned), {} bytes -> {}", entries.len(), entries.iter().filter(|e| e.pinned.is_some()).count(), text.len(), output.display());
    Ok(())
}

pub(crate) fn run(mut args: Args) -> Result<()> {
    let action = args
        .required("action")?
        .into_string()
        .map_err(|_| "action must be UTF-8".to_owned())?;
    let as_json = args.optional("json").is_some();
    let paths = paths(&mut args);
    // The shell passes the member's workspace to every apps verb; only bootstrap and install use it,
    // and no verb may leave it unconsumed (`unknown or duplicate option --dir`).
    let dir = args.optional("dir");
    match action.as_str() {
        "index-check" => index_check(args),
        "bootstrap" => {
            let root = absolute(&path(dir.ok_or("missing --dir")?))?;
            let budget = text_flag(&mut args, "budget")?.unwrap_or_else(|| "100000".into());
            let tool_ref = text_flag(&mut args, "tool-ref")?.unwrap_or_else(|| "tool".into());
            let parent_ref = text_flag(&mut args, "parent-ref")?.unwrap_or_else(|| "parent".into());
            args.finish()?;
            let ws = crate::workspace::load(&root)?;
            let report = bootstrap(&root, &ws, &budget, &tool_ref, &parent_ref)?;
            println!("{}", serde_json::to_string_pretty(&report).map_err(|e| e.to_string())?);
            if !as_json {
                eprintln!("apps bootstrap: tool task {} parent task {}; the sponsor imports: {}; write the appsConfig above to /etc/mini/apps.json",
                    report["toolTask"], report["parentTask"], report["sponsorImports"].as_array().map(|l| l.iter().filter_map(Value::as_str).collect::<Vec<_>>().join(" ; ")).unwrap_or_default());
            }
            Ok(())
        }
        "search" | "show" => catalogue(&action, args, &paths, as_json),
        "install" => install(args, &paths, as_json, dir),
        verb if WORKER_VERBS.contains(&verb) => {
            let mut request = Map::new();
            request.insert("protocol".into(), json!(WORKER_PROTOCOL));
            request.insert("verb".into(), json!(verb));
            for flag in ["grain", "to", "out", "request-id", "token"] {
                if let Some(value) = text_flag(&mut args, flag)? {
                    if flag == "grain" && !valid_grain(&value) {
                        return Err(format!("grainRefused: {value:?} is not a grain id of the form a<app>"));
                    }
                    request.insert(camel(flag), json!(value));
                }
            }
            args.finish()?;
            if matches!(verb, "open" | "stop" | "start" | "share" | "export" | "delete" | "status" | "renew" | "identities" | "revoke-identity") && !request.contains_key("grain") {
                return Err(format!("{verb} requires --grain a<app>"));
            }
            if verb == "revoke-identity" && !request.contains_key("token") {
                return Err("revoke-identity requires --token TOKEN".into());
            }
            if verb == "share" && !request.contains_key("to") {
                return Err("share requires --to MEMBER".into());
            }
            let reply = worker_call(&paths.socket, &Value::Object(request))?;
            report(&reply, as_json)
        }
        other => Err(format!(
            "mini apps: unknown action {other}; actions: search, show, index-check, {}",
            WORKER_VERBS.join(", ")
        )),
    }
}



// -------------------------------------------- the member's application birth

pub(crate) const DEFAULT_APPS_CONFIG: &str = "/etc/mini/apps.json";

/// What a member needs to know about the world to install an app, written by
/// the operator (world-readable): the hosting manager's subject, the names of
/// the member's references to the world's metered parent and tool tasks (the
/// operator delegates those; L1b's tariff says who pays), and the grain birth
/// tariff the Host pins.
#[derive(Clone, Debug, PartialEq)]
pub(crate) struct AppsConfig {
    pub management_subject: String,
    pub tool_ref: String,
    pub parent_ref: String,
    pub tariff: Value,
}

pub(crate) fn apps_config(path: &Path) -> Result<AppsConfig> {
    let bytes = crate::fsio::read_bounded(path, 16 * 1024)
        .map_err(|e| format!("appsConfigUnavailable: {} ({e}); the operator writes it (deploy/market/INSTALL.md §4)", path.display()))?;
    let value: Value = serde_json::from_slice(&bytes).map_err(|e| format!("{}: {e}", path.display()))?;
    if value.get("protocol").and_then(Value::as_str) != Some("mini-apps-config-v1") {
        return Err(format!("{} is not mini-apps-config-v1", path.display()));
    }
    let text = |key: &str, default: &str| value.get(key).and_then(Value::as_str).unwrap_or(default).to_owned();
    let management_subject = text("managementSubject", "");
    crate::workspace::decimal(&management_subject, "managementSubject")?;
    Ok(AppsConfig {
        management_subject,
        tool_ref: text("toolRef", "tool"),
        parent_ref: text("parentRef", "parent"),
        tariff: value.get("tariff").cloned().unwrap_or(json!({"base":"2","perBirth":"1"})),
    })
}

/// One metered peer as the Host's `grainBirthPeer` wants it: the task, the
/// member's capability on it, its current root and grain state (a signed read).
pub(crate) fn birth_peer(reference: &Value, view: &Value) -> Result<Value> {
    let task = crate::workspace::member(reference, "target")?;
    let capability = reference.get("operationCapability").and_then(Value::as_str).map_or_else(|| crate::workspace::member(reference, "observeCapability"), Ok)?;
    let observe = crate::workspace::member(reference, "observeCapability")?;
    let grain = view.pointer("/cell/grain").ok_or("the task's signed view has no grain state")?;
    Ok(json!({"task":task,"capability":capability,"observeCapability":observe,
        "targetRoot":view.pointer("/cell/root").cloned().ok_or("the task's signed view has no root")?,
        "before":{"generation":grain["generation"],"status":grain["status"],"remaining":grain["remaining"],"reserved":grain["reserved"]}}))
}

/// The op 30 source (`Host/Json.lean` `grainBirthIntentFrom "applicationGrainBirth" "applicationBirth"`,
/// `applicationBirthContext`, `applicationSpec`): the member is creator, owner and fee payer; the
/// nine ids come from the member's own namespace reservation.
/// The retained source and receipt are the ones of this birth (same application ids).
fn retained_birth_is(source: &Path, receipt: &Path, born_source: &Value) -> bool {
    const APPLICATION: &str = "/applicationGrainBirth/applicationBirth/application";
    source.is_file() && receipt.is_file()
        && crate::workspace::bounded_json(source).ok().and_then(|v| v.pointer(APPLICATION).cloned())
            == born_source.pointer(APPLICATION).cloned()
        && born_source.pointer(APPLICATION).is_some()
}

/// The retained delegation selects the same application as the freshly completed one.
fn delegation_names_app(delegation: &Path, selector_doc: &Value) -> bool {
    let app = selector_doc.pointer("/selector/app");
    delegation.is_file() && app.is_some()
        && crate::workspace::bounded_json(delegation).ok().and_then(|v| v.pointer("/selector/app").cloned()).as_ref() == app
}

pub(crate) fn app_birth_source(subject: &str, nonce: &str, context: &Value, ids: &std::collections::BTreeMap<String, String>, tool: &Value, parent: &Value, tariff: &Value) -> Result<Value> {
    let id = |role: &str| -> Result<&str> { ids.get(role).map(String::as_str).ok_or_else(|| format!("reservation lacks {role}")) };
    let mut grants = context.get("grants").and_then(Value::as_array).cloned().ok_or("birth context lacks grants")?;
    for peer in [tool, parent] {
        grants.push(json!({"kind":"object","target":peer["task"],"capability":peer["capability"]}));
    }
    Ok(json!({"subject":subject,"nonce":nonce,
        "applicationGrainBirth":{"tariff":tariff,
            "applicationBirth":{"genesis":context["genesis"],"template":context["template"],"creator":subject,"nonce":nonce,
                "application":{"app":id("app")?,"packageManifest":id("packageManifest")?,"snapshotManifest":id("snapshotManifest")?,"owner":subject,
                    "appOwnerCapability":id("appOwnerCapability")?,"appControlCapability":id("appControlCapability")?,
                    "packageOwnerCapability":id("packageOwnerCapability")?,"packageControlCapability":id("packageControlCapability")?,
                    "snapshotOwnerCapability":id("snapshotOwnerCapability")?,"snapshotControlCapability":id("snapshotControlCapability")?},
                "sourceCapabilities":context["sourceCapabilities"],"funding":context["funding"],"feePayer":context["feePayer"]},
            "tool":tool,"parent":parent},
        "grants":grants}))
}

/// The reservation one application birth consumes on the tool task: the tariff's base plus its
/// per-birth unit for each of the three resources (app, package manifest, snapshot manifest).
pub(crate) fn birth_reserve_amount(tariff: &Value) -> Result<String> {
    let unit = |key: &str| -> Result<u64> {
        tariff.get(key).and_then(Value::as_str).and_then(|v| v.parse::<u64>().ok()).ok_or_else(|| format!("tariff.{key} must be a decimal string"))
    };
    unit("perBirth")?.checked_mul(3).and_then(|v| v.checked_add(unit("base").ok()?)).map(|v| v.to_string()).ok_or_else(|| "tariff overflows".into())
}

/// The grain-intent that reserves AMOUNT on the tool task, as `grain-journey.sh`'s `grain_op`
/// shapes it, from a signed read of the task.
pub(crate) fn reserve_intent(subject: &str, nonce: &str, name: &str, tool_ref: &Value, view: &Value, amount: &str) -> Result<Value> {
    tool_intent(subject, nonce, name, tool_ref, view, json!({"type":"reserve","amount":amount}))
}

/// One grain operation on the tool task (reserve, settle) from a signed read of it.
pub(crate) fn tool_intent(subject: &str, nonce: &str, name: &str, tool_ref: &Value, view: &Value, operation: Value) -> Result<Value> {
    let peer = birth_peer(tool_ref, view)?;
    Ok(json!({"grain":{"task":peer["task"],"subject":subject,"capability":peer["capability"],"observeCapability":peer["observeCapability"],
        "schemaVersion":"1","expectedTargetRoot":peer["targetRoot"],
        "context":{"operationId":nonce,"payload":format!("mini apps install {name}")},
        "before":peer["before"],"operation":operation,"publications":[]},
        "grants":[{"kind":"object","target":peer["task"],"capability":peer["capability"]}],"intentNonce":nonce}))
}

/// Reserve on the tool task once per install name: a retained attempt, recovered exactly
/// (accepted outcome, else lookup) and never submitted twice.
fn reserve_tool(root: &Path, ws: &Value, name: &str, subject: &str, tool_ref: &Value, amount: &str) -> Result<()> {
    use crate::workspace::{self as w, member_path};
    let attempt = root.join("attempts").join(format!("apps-reserve-{}", w::ref_file(name)));
    let reserved = || {
        let retained = root.join("sources").join(format!("apps-reserve-{}.json", w::ref_file(name)));
        if let Some(amount) = w::bounded_json(&retained).ok().and_then(|v| v.pointer("/grain/operation/amount").and_then(Value::as_str).map(str::to_owned)) {
            let _ = INSTALL_BUDGET.set(amount);
        }
    };
    if attempt.exists() {
        if w::accepted_outcome(&attempt)?.is_some() {
            reserved();
            return Ok(());
        }
        if attempt.join("call.bin").is_file() {
            crate::retry(&attempt, "lookup", false)?;
            if w::accepted_outcome(&attempt)?.is_some() {
                return Ok(());
            }
        }
        return Err(format!("toolReservationUndecided: the tool reservation for {name} is neither confirmed nor refused; inspect {}", attempt.display()));
    }
    let (view, _, _) = w::signed_view(root, ws, tool_ref, "resource")?;
    let intent = reserve_intent(subject, &w::random_nonce()?, name, tool_ref, &view, amount)?;
    let intent_path = root.join("sources").join(format!("apps-reserve-{}.json", w::ref_file(name)));
    let _ = fs::remove_file(&intent_path); // no attempt exists: an older unsubmitted intent is stale
    crate::create_private(&intent_path, &serde_json::to_vec_pretty(&intent).map_err(|e| e.to_string())?)?;
    eprintln!("apps tool reservation attempt: {}", attempt.display());
    crate::submit(&w::workspace_host(ws)?, &member_path(ws, "config")?, &intent_path, std::ffi::OsStr::new("grain-intent"), &member_path(ws, "key")?, &attempt, false)?;
    w::accepted_outcome(&attempt)?.ok_or_else(|| format!("toolReservationRefused: see {}", attempt.display()))?;
    reserved();
    Ok(())
}

/// Release this install's tool reservation after its birth was definitely refused, so one failed
/// install never holds the world's tool task: a retained settle with charge 0 (status 3 -> 1,
/// the reserve returned to `remaining`; never `cancel`, which cancels the task itself), recovered
/// exactly, then both attempt directories are retired so a later install reserves afresh.
/// Nothing to do without a confirmed reservation.
fn release_reservation(root: &Path, ws: &Value, name: &str, subject: &str, tool_ref: &Value) -> Result<()> {
    use crate::workspace::{self as w, member_path};
    let reserve = root.join("attempts").join(format!("apps-reserve-{}", w::ref_file(name)));
    if !reserve.exists() || w::accepted_outcome(&reserve)?.is_none() {
        return Ok(());
    }
    let cancel = root.join("attempts").join(format!("apps-reserve-release-{}", w::ref_file(name)));
    let confirmed = if cancel.exists() {
        if w::accepted_outcome(&cancel)?.is_none() && cancel.join("call.bin").is_file() {
            crate::retry(&cancel, "lookup", false)?;
        }
        w::accepted_outcome(&cancel)?.is_some()
    } else {
        let (view, _, _) = w::signed_view(root, ws, tool_ref, "resource")?;
        let intent = tool_intent(subject, &w::random_nonce()?, name, tool_ref, &view, json!({"type":"settle","charge":"0"}))?;
        let intent_path = root.join("sources").join(format!("apps-reserve-release-{}.json", w::ref_file(name)));
        let _ = fs::remove_file(&intent_path);
        crate::create_private(&intent_path, &serde_json::to_vec_pretty(&intent).map_err(|e| e.to_string())?)?;
        eprintln!("apps tool reservation release attempt: {}", cancel.display());
        crate::submit(&w::workspace_host(ws)?, &member_path(ws, "config")?, &intent_path, std::ffi::OsStr::new("grain-intent"), &member_path(ws, "key")?, &cancel, false)?;
        w::accepted_outcome(&cancel)?.is_some()
    };
    if !confirmed {
        return Err(format!("toolReservationReleaseUndecided: inspect {}", cancel.display()));
    }
    let stamp = w::random_nonce()?;
    for dir in [&reserve, &cancel] {
        let retired = dir.with_file_name(format!("{}.released-{stamp}", dir.file_name().and_then(|n| n.to_str()).unwrap_or("attempt")));
        fs::rename(dir, &retired).map_err(|e| format!("cannot retire {}: {e}", dir.display()))?;
    }
    Ok(())
}

const APP_ROLES: [(&str, IdKind); 9] = [
    ("app", IdKind::Resource), ("packageManifest", IdKind::Resource), ("snapshotManifest", IdKind::Resource),
    ("appOwnerCapability", IdKind::Capability), ("appControlCapability", IdKind::Capability),
    ("packageOwnerCapability", IdKind::Capability), ("packageControlCapability", IdKind::Capability),
    ("snapshotOwnerCapability", IdKind::Capability), ("snapshotControlCapability", IdKind::Capability),
];

/// Birth the application, package-manifest and snapshot-manifest resources as the member's own
/// turn (op 30), the way `workspace create` births a resource: reserve the nine ids in the
/// member's namespace, retain the exact source, author through the Host, submit once with exact
/// recovery, then register three references `NAME`, `NAME-package`, `NAME-snapshot`.
/// `HOME/inbox/<name>.json`: where the frame leaves a delegated reference for the member
/// (the shell's `inbox` lists that directory; `import NAME @FILE` takes such a file).
pub(crate) fn inbox_file(home: &Path, name: &str) -> PathBuf {
    home.join("inbox").join(format!("{}.json", crate::workspace::ref_file(name)))
}

/// The member's reference to one of the world's metered tasks: already imported, or
/// imported now from the inbox file the frame left at enrolment (`mini-reenroll`'s
/// `apps_member_grants`), so a door member never runs an import by hand. Refuses by
/// name, saying where the file was looked for, when neither exists.
pub(crate) fn metered_reference(root: &Path, ws: &Value, home: Option<&Path>, name: &str, role: &str) -> Result<Value> {
    if let Ok(reference) = crate::workspace::reference(root, name) {
        return Ok(reference);
    }
    let inbox = home.map(|h| inbox_file(h, name));
    if let Some(file) = inbox.as_ref().filter(|f| f.is_file()) {
        crate::workspace::import_delegated(root, ws, name, file)
            .map_err(|e| format!("meteredGrantRequired: the delegated reference {} for the {role} task did not import: {e}", file.display()))?;
        return crate::workspace::reference(root, name);
    }
    Err(format!(
        "meteredGrantRequired: no reference {name:?} to the world's metered {role} task and no delivered reference at {}; the operator delegates observe and the grain operation on it at enrolment (mini-reenroll apps_member_grants; L1b decides who pays)",
        inbox.map(|f| f.display().to_string()).unwrap_or_else(|| "HOME/inbox (no --home given)".into())
    ))
}

pub(crate) fn app_birth(root: &Path, ws: &Value, home: Option<&Path>, name: &str, config: &AppsConfig) -> Result<(Value, Value)> {
    use crate::workspace::{self as w, member, member_path};
    w::validate_ref_name(name)?;
    let subject = member(ws, "subject")?.to_owned();
    let context = w::bounded_json(&member_path(ws, "birthContext")?)?;
    if member(&context, "type")? != "minidregg-participant-birth-context-v1" {
        return Err("unknown birth context version".into());
    }
    let tool_ref = metered_reference(root, ws, home, &config.tool_ref, "tool")?;
    let parent_ref = metered_reference(root, ws, home, &config.parent_ref, "parent")?;
    let namespace_root = w::namespace_root(root, ws)?;
    let request_path = root.join("sources").join(format!("apps-birth-{}.request.json", w::ref_file(name)));
    let core = json!({"type":"minidregg-apps-birth-request-v1","name":name,"subject":subject,"context":context,
        "tool":member(&tool_ref,"target")?,"parent":member(&parent_ref,"target")?});
    let request = if request_path.exists() {
        let saved = w::bounded_json(&request_path)?;
        let mut expected = core.clone();
        expected["nonce"] = saved["nonce"].clone();
        if saved != expected {
            return Err("existing apps birth request differs; use a new name".into());
        }
        saved
    } else {
        let mut requested = core;
        requested["nonce"] = json!(w::random_nonce()?);
        crate::create_private(&request_path, &serde_json::to_vec(&requested).map_err(|e| e.to_string())?)?;
        requested
    };
    let stable = serde_json::to_vec(&request).map_err(|e| e.to_string())?;
    let roles: Vec<Role> = APP_ROLES.iter().map(|(label, kind)| Role { label: (*label).into(), kind: *kind }).collect();
    let reservation = participant_namespace::reserve(&namespace_root, member(&context["genesis"], "domain")?, &subject, name, &stable, &roles)?;
    let attempt = root.join("attempts").join(format!("apps-birth-{}", w::ref_file(name)));
    // The metered composite consumes a reservation on the tool task; the member makes it first,
    // under its delegated capability, unless the birth attempt already exists (it was made then).
    if !attempt.exists() {
        reserve_tool(root, ws, name, &subject, &tool_ref, &birth_reserve_amount(&config.tariff)?)?;
    }
    // The peers' current state: signed reads under the member's own grants.
    let (tool_view, _, _) = w::signed_view(root, ws, &tool_ref, "resource")?;
    let (parent_view, _, _) = w::signed_view(root, ws, &parent_ref, "resource")?;
    let nonce = member(&request, "nonce")?;
    let expected_source = app_birth_source(&subject, nonce, &context, &reservation.ids, &birth_peer(&tool_ref, &tool_view)?, &birth_peer(&parent_ref, &parent_view)?, &config.tariff)?;
    let source_path = root.join("sources").join(format!("apps-birth-{}.json", w::ref_file(name)));
    let source = if source_path.exists() {
        let saved = w::bounded_json(&source_path)?;
        // The peers' state moves between attempts; the identity (ids, subject, nonce) may not.
        if saved["applicationGrainBirth"]["applicationBirth"]["application"] != expected_source["applicationGrainBirth"]["applicationBirth"]["application"] || saved["nonce"] != expected_source["nonce"] {
            return Err("retained apps birth source differs from the namespace reservation".into());
        }
        saved
    } else {
        crate::create_private(&source_path, &serde_json::to_vec_pretty(&expected_source).map_err(|e| e.to_string())?)?;
        expected_source
    };
    let socket = crate::SOCKET.get().ok_or("apps install requires a pinned persistent Host socket")?;
    let authoring = root.join("sources").join(format!("apps-birth-{}.authoring", w::ref_file(name)));
    let host = w::workspace_host(ws)?;
    let host_config = member_path(ws, "config")?;
    if attempt.exists() && w::attempt_definitely_unadmitted(&attempt)? {
        let retired = w::release_unadmitted_attempt(&authoring, &attempt, &reservation)?;
        eprintln!("apps birth attempt definitely unadmitted; retained as {}", retired.display());
        release_reservation(root, ws, name, &subject, &tool_ref)?;
        reserve_tool(root, ws, name, &subject, &tool_ref, &birth_reserve_amount(&config.tariff)?)?;
    }
    let author_dir = if attempt.exists() {
        w::authoring_generations(&authoring)?.last().cloned().ok_or("apps birth attempt exists without an authoring generation")?
    } else {
        w::author_generations(&authoring, &reservation,
            || Ok(PathBuf::new()),
            |generation, _| crate::current_birth::author(&host, &host_config, socket, &source_path, None, generation, crate::current_birth::Route::Application),
            |generation| crate::observation_stale(&host, &host_config, generation))?
    };
    let intent_path = crate::current_birth::retained_intent(&author_dir, crate::current_birth::Route::Application)?;
    let source_sha = {
        use sha2::Digest;
        hex(&sha2::Sha256::digest(fs::read(&intent_path).map_err(|e| format!("cannot hash the retained intent: {e}"))?))
    };
    participant_namespace::bind_attempt(&reservation, &attempt, &source_sha)?;
    let receipt = if attempt.exists() {
        if !attempt.join("call.bin").is_file() {
            return Err(format!("apps birth preparation interrupted before the exact call; inspect {}", attempt.display()));
        }
        match w::accepted_outcome(&attempt)? {
            Some(receipt) => receipt,
            None => {
                crate::retry(&attempt, "lookup", false)?;
                w::accepted_outcome(&attempt)?.ok_or("apps birth lookup did not confirm the installed birth")?
            }
        }
    } else {
        eprintln!("apps birth attempt: {}", attempt.display());
        if let Err(refusal) = crate::submit(&host, &host_config, &intent_path, std::ffi::OsStr::new("binary"), &member_path(ws, "key")?, &attempt, false) {
            if w::attempt_definitely_unadmitted(&attempt).unwrap_or(false) {
                if let Err(cancel) = release_reservation(root, ws, name, &subject, &tool_ref) {
                    return Err(format!("{refusal}; and the tool reservation was not released: {cancel}"));
                }
            }
            return Err(refusal);
        }
        w::accepted_outcome(&attempt)?.ok_or("apps birth returned without an installed receipt")?
    };
    let ids = &reservation.ids;
    for (suffix, target, owner, control) in [("", "app", "appOwnerCapability", "appControlCapability"), ("-package", "packageManifest", "packageOwnerCapability", "packageControlCapability"), ("-snapshot", "snapshotManifest", "snapshotOwnerCapability", "snapshotControlCapability")] {
        let reference_name = format!("{name}{suffix}");
        let reference_path = root.join("refs").join(format!("{}.json", w::ref_file(&reference_name)));
        if reference_path.exists() {
            continue;
        }
        let value = json!({"type":"minidregg-participant-reference-v1","name":reference_name,"kind":"object","target":ids[target],
            "observeCapability":ids[owner],"operationCapability":ids[owner],"controlCapability":ids[control],
            "provenance":{"birthReceipt":receipt,"reservationDigest":reservation.request_digest,"reservationRecord":reservation.record_path,"applicationBirth":name},
            "authority":"hint-only"});
        crate::create_private(&reference_path, &serde_json::to_vec_pretty(&value).map_err(|e| e.to_string())?)?;
    }
    Ok((source, receipt))
}

/// The member delegates the manager a child of the app owner capability with the verbs a share ticket's
/// issuer needs (observe, mutate, delegate, append, place), through the shell's own propose, submit and
/// publish-delegation, and returns the recipient reference (which names the child capability).
fn delegate_share(root: &Path, ws: &Value, app_ref: &str, manager: &str, max_cost: &str) -> Result<Value> {
    use crate::workspace as w;
    let id = format!("share-{app_ref}");
    let proposal = root.join("sources").join(format!("{id}.request.json"));
    let request = json!({"type":"minidregg-workspace-proposal-v1","action":"delegate","name":app_ref,"recipient":manager,
        "verbs":["observe","mutate","delegate","append","place"],"maxCost":max_cost});
    let _ = fs::remove_file(&proposal);
    crate::create_private(&proposal, &serde_json::to_vec_pretty(&request).map_err(|e| e.to_string())?)?;
    let mini = std::env::current_exe().map_err(|e| e.to_string())?;
    let _ = ws;
    let run = |args: &[&str]| -> Result<()> {
        let out = std::process::Command::new(&mini).args(["workspace", "--action"]).args(args).output().map_err(|e| e.to_string())?;
        if out.status.success() { Ok(()) } else { Err(format!("shareDelegationRefused: workspace {}: {}", args.first().unwrap_or(&""), String::from_utf8_lossy(&out.stderr).trim())) }
    };
    let dir = root.to_str().ok_or("workspace path is not UTF-8")?;
    let attempt = root.join("attempts").join(&id);
    let intent = root.join("proposals").join(&id).join("intent.json");
    let (attempt_s, intent_s, proposal_s) = (attempt.to_string_lossy().into_owned(), intent.to_string_lossy().into_owned(), proposal.to_string_lossy().into_owned());
    run(&["propose", "--dir", dir, "--request", &proposal_s, "--proposal-id", &id])?;
    run(&["submit", "--dir", dir, "--intent", &intent_s, "--attempt", &attempt_s])?;
    run(&["publish-delegation", "--dir", dir, "--proposal-id", &id, "--attempt", &attempt_s])?;
    w::bounded_json(&root.join("proposals").join(&id).join("recipient-reference.json"))
}

/// The hosting delegation to the manager through the shell's own verb
/// (`app delegate-lifecycle`, six ordinary proposals), run to completion;
/// returns the management selector `spk-host grain install` consumes.
pub(crate) fn delegate_lifecycle(root: &Path, name: &str, request_id: &str, manager: &str) -> Result<PathBuf> {
    // Each round is one `workspace --action app-lifecycle` run in this process, its output
    // captured (`crate::capture::command`), as `chat::client` runs workspace actions.
    let run = |op: &str, with_names: bool| -> Result<Value> {
        let os = |v: &str| std::ffi::OsString::from(v);
        let mut flags = vec![("action", os("app-lifecycle")), ("dir", root.as_os_str().to_owned()), ("request-id", os(request_id)), ("op", os(op))];
        if with_names {
            flags.extend([("name", os(name)), ("package-name", os(&format!("{name}-package"))),
                ("snapshot-name", os(&format!("{name}-snapshot"))), ("manager", os(manager))]);
        }
        let (code, stdout, stderr) = crate::capture::command("workspace", &flags).map_err(|e| e.to_string())?;
        if code != 0 {
            return Err(format!("app delegate-lifecycle {op}: {}", String::from_utf8_lossy(&stderr).trim()));
        }
        Ok(serde_json::from_slice(&stdout).unwrap_or(Value::Null))
    };
    let mut status = run("status", true)?;
    let mut rounds = 0;
    while status.get("complete") != Some(&json!(true)) {
        rounds += 1;
        if rounds > 14 {
            return Err(format!("the hosting delegation did not complete in 14 rounds; last status {status}"));
        }
        match status.get("nextAction").and_then(Value::as_str) {
            Some("prepare") => { run("prepare", false)?; }
            Some("submit") => { run("submit", false)?; }
            Some("recover") => { run("recover", false)?; }
            other => return Err(format!("the hosting delegation names no next action ({other:?}); status {status}")),
        }
        status = run("status", false)?;
    }
    status.get("managementSelector").and_then(Value::as_str).map(PathBuf::from)
        .ok_or_else(|| "the hosting delegation is complete but its selector is not published yet (status: recover)".into())
}


// ------------------------------------------ the world's metered tasks (bootstrap)

const BOOTSTRAP_ROLES: [(&str, IdKind); 6] = [
    ("parentTask", IdKind::Resource), ("toolTask", IdKind::Resource),
    ("parentOwnerCapability", IdKind::Capability), ("parentControlCapability", IdKind::Capability),
    ("toolOwnerCapability", IdKind::Capability), ("toolControlCapability", IdKind::Capability),
];

/// The op 91 `birth-intent` for the two metered tasks an apps world needs, as the workroom
/// provisioner births them at genesis (`scripts/workroom/provision.sh`): two `grain` resources
/// owned by the operator's subject with explicit budgets, the parent under the holder form (any
/// holder of a delegated grant may make a birth's witness no-op; only the owner manages it).
/// Budget is an explicit operator allocation, never a metered claim.
pub(crate) fn bootstrap_source(subject: &str, nonce: &str, context: &Value, ids: &std::collections::BTreeMap<String, String>, budget: &str) -> Result<Value> {
    let id = |role: &str| -> Result<&str> { ids.get(role).map(String::as_str).ok_or_else(|| format!("reservation lacks {role}")) };
    let mut birth = json!({"genesis":context["genesis"],"template":context["template"],"creator":subject,"nonce":nonce,
        "resources":[
            {"kind":"object","storage":"grain","target":id("parentTask")?,"owner":subject,
             "ownerCapability":id("parentOwnerCapability")?,"controlCapability":id("parentControlCapability")?,
             "budget":budget,"holderWitnessGeneration":"1"},
            {"kind":"object","storage":"grain","target":id("toolTask")?,"owner":subject,
             "ownerCapability":id("toolOwnerCapability")?,"controlCapability":id("toolControlCapability")?,
             "budget":budget}],
        "sourceCapabilities":context["sourceCapabilities"],"funding":context["funding"],"feePayer":context["feePayer"]});
    if let Some(tariff) = context.get("grainBirthTariff") {
        birth["grainBirthTariff"] = tariff.clone();
    }
    Ok(json!({"subject":subject,"nonce":nonce,"birth":birth,"grants":context["grants"]}))
}

/// `mini apps bootstrap --dir OPERATOR-WORKSPACE [--budget N] [--tool-ref tool] [--parent-ref parent]`:
/// once per world, by the operator (mini-core), before `/etc/mini/apps.json` is written. Births the
/// world's metered parent and tool tasks under the operator's own capabilities (ids from the
/// operator's namespace), registers them as references and prints their ids and the sponsor's two
/// import lines. Idempotent: a second run finds the references and prints the same lines.
pub(crate) fn bootstrap(root: &Path, ws: &Value, budget: &str, tool_ref: &str, parent_ref: &str) -> Result<Value> {
    use crate::workspace::{self as w, member, member_path};
    crate::workspace::decimal(budget, "budget")?;
    w::validate_ref_name(tool_ref)?;
    w::validate_ref_name(parent_ref)?;
    let subject = member(ws, "subject")?.to_owned();
    let report = |tool: &Value, parent: &Value| -> Value {
        let line = |name: &str, r: &Value| format!("import {name} object {} {} {}", r["target"].as_str().unwrap_or("?"), r["observeCapability"].as_str().unwrap_or("?"), r["operationCapability"].as_str().unwrap_or("?"));
        json!({"type":"mini-apps-bootstrap-v1","subject":subject,"toolTask":tool["target"],"parentTask":parent["target"],
            "toolRef":tool_ref,"parentRef":parent_ref,
            "sponsorImports":[line(tool_ref, tool), line(parent_ref, parent)],
            "appsConfig":{"protocol":"mini-apps-config-v1","managementSubject":subject,"toolRef":tool_ref,"parentRef":parent_ref,"tariff":{"base":"2","perBirth":"1"}}})
    };
    if let (Ok(tool), Ok(parent)) = (w::reference(root, tool_ref), w::reference(root, parent_ref)) {
        // A world bootstrapped before the tasks were activated is repaired by a rerun.
        activate_tasks(root, ws, &subject, &tool, &parent)?;
        return Ok(report(&tool, &parent));
    }
    let context = w::bounded_json(&member_path(ws, "birthContext")?)?;
    if member(&context, "type")? != "minidregg-participant-birth-context-v1" {
        return Err("unknown birth context version".into());
    }
    let namespace_root = w::namespace_root(root, ws)?;
    let name = "apps-bootstrap";
    let request_path = root.join("sources").join("apps-bootstrap.request.json");
    let core = json!({"type":"minidregg-apps-bootstrap-request-v1","subject":subject,"context":context,"budget":budget,"toolRef":tool_ref,"parentRef":parent_ref});
    let request = if request_path.exists() {
        let saved = w::bounded_json(&request_path)?;
        let mut expected = core.clone();
        expected["nonce"] = saved["nonce"].clone();
        if saved != expected {
            return Err("existing apps bootstrap request differs (budget or names changed); it is one per world".into());
        }
        saved
    } else {
        let mut requested = core;
        requested["nonce"] = json!(w::random_nonce()?);
        crate::create_private(&request_path, &serde_json::to_vec(&requested).map_err(|e| e.to_string())?)?;
        requested
    };
    let stable = serde_json::to_vec(&request).map_err(|e| e.to_string())?;
    let roles: Vec<Role> = BOOTSTRAP_ROLES.iter().map(|(label, kind)| Role { label: (*label).into(), kind: *kind }).collect();
    let reservation = participant_namespace::reserve(&namespace_root, member(&context["genesis"], "domain")?, &subject, name, &stable, &roles)?;
    let nonce = member(&request, "nonce")?;
    let source = bootstrap_source(&subject, nonce, &context, &reservation.ids, budget)?;
    let source_path = root.join("sources").join("apps-bootstrap.json");
    if source_path.exists() {
        if w::bounded_json(&source_path)? != source {
            return Err("retained apps bootstrap source differs from the namespace reservation".into());
        }
    } else {
        crate::create_private(&source_path, &serde_json::to_vec_pretty(&source).map_err(|e| e.to_string())?)?;
    }
    let attempt = root.join("attempts").join("apps-bootstrap");
    let host = w::workspace_host(ws)?;
    let host_config = member_path(ws, "config")?;
    let receipt = match w::accepted_outcome(&attempt).ok().flatten() {
        Some(receipt) => receipt,
        None => {
            if attempt.exists() {
                crate::retry(&attempt, "lookup", false)?;
            } else {
                // The Host authors the birth at the current height against a sponsor-signed read of
                // the factory (`current-resource-intent`, as `workspace create` does): a birth-intent
                // authored from the genesis is refused birthStale once the World is past genesis plus
                // the 64-height window, which any world a few transactions old is.
                let socket = crate::SOCKET.get().ok_or("apps bootstrap requires a pinned persistent Host socket")?;
                let factory = member(&context["genesis"], "factoryId")?;
                let observe_capability = context["grants"].as_array().into_iter().flatten()
                    .find(|grant| grant["kind"] == "object" && grant["target"] == factory)
                    .and_then(|grant| grant["capability"].as_str())
                    .ok_or("birth context needs one factory resource observation grant")?;
                let factory_ref = json!({"kind":"object","target":factory,"observeCapability":observe_capability});
                let authoring = root.join("sources").join("apps-bootstrap.authoring");
                let author_dir = w::author_generations(&authoring, &reservation,
                    || Ok(w::signed_view(root, ws, &factory_ref, "resource")?.2),
                    |generation, observation| crate::current_birth::author(&host, &host_config, socket, &source_path, observation, generation, crate::current_birth::Route::Resource),
                    |generation| crate::observation_stale(&host, &host_config, generation))?;
                let intent_path = crate::current_birth::retained_intent(&author_dir, crate::current_birth::Route::Resource)?;
                let source_sha = {
                    use sha2::Digest;
                    hex(&sha2::Sha256::digest(fs::read(&intent_path).map_err(|e| format!("cannot hash the retained intent: {e}"))?))
                };
                participant_namespace::bind_attempt(&reservation, &attempt, &source_sha)?;
                eprintln!("apps bootstrap attempt: {}", attempt.display());
                crate::submit(&host, &host_config, &intent_path, std::ffi::OsStr::new("binary"), &member_path(ws, "key")?, &attempt, false)?;
            }
            w::accepted_outcome(&attempt)?.ok_or("apps bootstrap birth is not confirmed; retained for exact recovery")?
        }
    };
    let ids = &reservation.ids;
    for (reference_name, target, owner, control) in [(tool_ref, "toolTask", "toolOwnerCapability", "toolControlCapability"), (parent_ref, "parentTask", "parentOwnerCapability", "parentControlCapability")] {
        let reference_path = root.join("refs").join(format!("{}.json", w::ref_file(reference_name)));
        if reference_path.exists() {
            continue;
        }
        let value = json!({"type":"minidregg-participant-reference-v1","name":reference_name,"kind":"object","target":ids[target],
            "observeCapability":ids[owner],"operationCapability":ids[owner],"controlCapability":ids[control],
            "provenance":{"birthReceipt":receipt,"reservationDigest":reservation.request_digest,"reservationRecord":reservation.record_path,"appsBootstrap":true},
            "authority":"hint-only"});
        crate::create_private(&reference_path, &serde_json::to_vec_pretty(&value).map_err(|e| e.to_string())?)?;
    }
    let (tool, parent) = (w::reference(root, tool_ref)?, w::reference(root, parent_ref)?);
    activate_tasks(root, ws, &subject, &tool, &parent)?;
    Ok(report(&tool, &parent))
}

/// A task `apps bootstrap` has just birthed is idle (status 0): in the grain-task law only an attach
/// leaves status 0 (to 1, generation +1), and a reserve is legal only from an attached task. So every
/// member's first install reservation was law-denied. The workroom fixture's `workroom_ready` does
/// exactly this: attach the tool; attach the metered birth parent and reserve 1 on it. Each step is
/// one retained grain-intent attempt, recovered exactly and never submitted twice, and a task already
/// past the step is left alone (a rerun of bootstrap finds it done).
fn activate_tasks(root: &Path, ws: &Value, subject: &str, tool: &Value, parent: &Value) -> Result<()> {
    for (name, task) in ACTIVATION_STEPS {
        let (reference, operation) = match name {
            "tool-attach" => (tool, json!({"type":"attach","soft":false})),
            "parent-attach" => (parent, json!({"type":"attach","soft":false})),
            _ => (parent, json!({"type":"reserve","amount":"1"})),
        };
        let _ = task;
        activate_step(root, ws, subject, name, reference, operation)?;
    }
    Ok(())
}

/// The activation steps in the order the law permits them (name, which task).
const ACTIVATION_STEPS: [(&str, &str); 3] = [("tool-attach", "tool"), ("parent-attach", "parent"), ("parent-reserve", "parent")];

/// Whether a step is still needed given the task's grain state (status and reserved as the signed
/// view prints them): attach only leaves status 0, and the parent's one-unit reserve is legal only once
/// attached (status 1) with nothing reserved.
pub(crate) fn activation_needed(step: &str, grain: &Value) -> bool {
    match step {
        "tool-attach" | "parent-attach" => grain["status"] == "0",
        "parent-reserve" => grain["status"] == "1" && grain["reserved"] == "0",
        _ => false,
    }
}

fn activate_step(root: &Path, ws: &Value, subject: &str, name: &str, task: &Value, operation: Value) -> Result<()> {
    use crate::workspace::{self as w, member_path};
    let attempt = root.join("attempts").join(format!("apps-activate-{name}"));
    if attempt.exists() {
        if w::accepted_outcome(&attempt)?.is_none() && attempt.join("call.bin").is_file() {
            crate::retry(&attempt, "lookup", false)?;
        }
        return w::accepted_outcome(&attempt)?.map(|_| ()).ok_or_else(|| format!("taskActivationUndecided: {name} is neither confirmed nor refused; inspect {}", attempt.display()));
    }
    let (view, _, _) = w::signed_view(root, ws, task, "resource")?;
    let grain = view.pointer("/cell/grain").ok_or("the task's signed view has no grain state")?;
    if !activation_needed(name, grain) {
        return Ok(());
    }
    let intent = tool_intent(subject, &w::random_nonce()?, name, task, &view, operation)?;
    let intent_path = root.join("sources").join(format!("apps-activate-{name}.json"));
    let _ = fs::remove_file(&intent_path);
    crate::create_private(&intent_path, &serde_json::to_vec_pretty(&intent).map_err(|e| e.to_string())?)?;
    eprintln!("apps task activation attempt: {}", attempt.display());
    crate::submit(&w::workspace_host(ws)?, &member_path(ws, "config")?, &intent_path, std::ffi::OsStr::new("grain-intent"), &member_path(ws, "key")?, &attempt, false)?;
    w::accepted_outcome(&attempt)?.map(|_| ()).ok_or_else(|| format!("taskActivationRefused: {name}; see {}", attempt.display()))
}

// ------------------------------------------------ the request cell (law.apps)

/// The app-install request law in the shell grammar, rendered from
/// `Kernel/AppsRequest.lean` by `scripts/AppsRequestTemplate.lean`.
pub(crate) const LAW_TEMPLATE: &str = include_str!(concat!(env!("CARGO_MANIFEST_DIR"), "/templates/apps/request/law.apps"));
pub(crate) const FIELD_STATE: u64 = 1;
pub(crate) const FIELD_PACKAGE_HI: u64 = 2;
pub(crate) const FIELD_PACKAGE_LO: u64 = 3;
pub(crate) const FIELD_APP0: u64 = 4;
pub(crate) const FIELD_CLASS: u64 = 8;
pub(crate) const FIELD_GRAIN: u64 = 9;
pub(crate) const FIELD_GENERATION: u64 = 10;

/// The law for one request: the template with its two placeholders bound,
/// comment lines dropped, parsed by the shell grammar.
pub(crate) fn law(requester: &str, manager: &str) -> Result<Value> {
    for (label, subject) in [("requester", requester), ("manager", manager)] {
        crate::workspace::decimal(subject, label)?;
    }
    let text = LAW_TEMPLATE
        .lines()
        .filter(|line| !line.trim_start().starts_with("--"))
        .collect::<Vec<_>>()
        .join("\n")
        .replace("{REQUESTER}", requester)
        .replace("{MANAGER}", manager);
    crate::shell::law::parse(&text).map_err(|error| format!("apps request law template: {error}"))
}

/// A 32-hex packageId as two 64-bit words: the cell's integer fields 2 and 3.
pub(crate) fn package_words(package_id: &str) -> Result<[u64; 2]> {
    if !valid_package_id(package_id) {
        return Err("packageId is not 32 lowercase hex digits".into());
    }
    Ok([
        u64::from_str_radix(&package_id[..16], 16).map_err(|e| e.to_string())?,
        u64::from_str_radix(&package_id[16..], 16).map_err(|e| e.to_string())?,
    ])
}

const BASE32: &[u8; 32] = b"0123456789acdefghjkmnpqrstuvwxyz";

/// A 52-digit appId (Sandstorm's base32 alphabet `0123456789acdefghjkmnpqrstuvwxyz`) as 32
/// bytes: 5 bits per digit, little-endian bit order, the four padding bits dropped. The
/// member verb and the worker both derive the cell's four words this way, so the encoding
/// is one injective naming of the appId in the kernel's record; it is not claimed to equal
/// the signing key's hash byte for byte (that identity is the signed package's, checked by
/// the ingest).
pub(crate) fn app_bytes(app_id: &str) -> Result<[u8; 32]> {
    if !valid_app_id(app_id) {
        return Err("appId is not 52 base32 digits".into());
    }
    let mut bytes = [0_u8; 32];
    let mut bit = 0_usize;
    for digit in app_id.bytes() {
        let value = BASE32.iter().position(|b| *b == digit).ok_or("appId holds a digit outside Sandstorm's base32 alphabet")? as u32;
        for k in 0..5 {
            let position = bit + k;
            if position < 256 && (value >> k) & 1 == 1 {
                bytes[position / 8] |= 1 << (position % 8);
            }
        }
        bit += 5;
    }
    Ok(bytes)
}

pub(crate) fn app_words(app_id: &str) -> Result<[u64; 4]> {
    let bytes = app_bytes(app_id)?;
    let mut words = [0_u64; 4];
    for (i, word) in words.iter_mut().enumerate() {
        *word = u64::from_be_bytes(bytes[i * 8..i * 8 + 8].try_into().map_err(|_| "word")?);
    }
    Ok(words)
}

pub(crate) fn class_code(class: &str) -> Result<u64> {
    match class {
        "S" => Ok(1),
        "M" => Ok(2),
        "L" => Ok(3),
        _ => Err("classRefused: the request cell records S, M or L".into()),
    }
}

/// `apps-<id>`: the member's signed package choice, born under `law.apps` and
/// set up in one write (state 0, the words, the class, grain and generation 0).
/// Idempotent on the reference: an existing cell is not born twice.
pub(crate) fn request_cell(root: &Path, ws: &Value, name: &str, package_id: &str, app_id: &str, class: &str, manager: &str) -> Result<Value> {
    crate::workspace::validate_name(name)?;
    if let Ok(reference) = crate::workspace::reference(root, name) {
        return Ok(reference);
    }
    let requester = crate::workspace::member(ws, "subject")?.to_owned();
    let predicate = law(&requester, manager)?;
    let law_path = root.join("sources").join(format!("apps-law-{name}-{}.json", crate::workspace::random_nonce()?));
    crate::create_private(&law_path, &serde_json::to_vec(&predicate).map_err(|e| e.to_string())?)?;
    crate::workspace::create(root, ws, name, "declared", &law_path, None, "object", None, None, Some(&format!("{FIELD_STATE}-{FIELD_GENERATION}")))?;
    let [hi, lo] = package_words(package_id)?;
    let app = app_words(app_id)?;
    let mut actions = vec![
        crate::market::scalar(FIELD_STATE, "0", None),
        crate::market::scalar(FIELD_PACKAGE_HI, &hi.to_string(), None),
        crate::market::scalar(FIELD_PACKAGE_LO, &lo.to_string(), None),
    ];
    for (i, word) in app.iter().enumerate() {
        actions.push(crate::market::scalar(FIELD_APP0 + i as u64, &word.to_string(), None));
    }
    actions.push(crate::market::scalar(FIELD_CLASS, &class_code(class)?.to_string(), None));
    actions.push(crate::market::scalar(FIELD_GRAIN, "0", None));
    actions.push(crate::market::scalar(FIELD_GENERATION, "0", None));
    let id = format!("setup-{name}");
    crate::market::propose_writes(root, ws, name, &id, actions)?;
    crate::workspace::submit_intent(root, ws, &root.join("proposals").join(&id).join("intent.json"), "intent", false, Some(&root.join("attempts").join(&id)))?;
    crate::workspace::reference(root, name)
}

/// A grain id is `a<app>`: the app resource's canonical decimal, DNS-safe.
pub(crate) fn valid_grain(text: &str) -> bool {
    text.len() >= 2
        && text.len() <= 40
        && text.as_bytes()[0] == b'a'
        && text.as_bytes()[1] != b'0'
        && text.bytes().skip(1).all(|b| b.is_ascii_digit())
}

fn camel(flag: &str) -> String {
    let mut out = String::new();
    let mut upper = false;
    for c in flag.chars() {
        if c == '-' {
            upper = true;
        } else if upper {
            out.extend(c.to_uppercase());
            upper = false;
        } else {
            out.push(c);
        }
    }
    out
}

#[cfg(test)]
mod tests {

    #[test]
    fn a_freshly_bootstrapped_world_activates_its_tasks_before_any_reservation() {
        // `apps bootstrap` births both tasks idle: status 0, nothing reserved. The grain-task law lets
        // only an attach leave status 0, and a reserve only follows an attach, so the first install's
        // reservation on an unactivated task is law-denied. The steps the bootstrap now takes:
        let idle = json!({"generation":"0","status":"0","remaining":"1000000","reserved":"0"});
        let attached = json!({"generation":"1","status":"1","remaining":"1000000","reserved":"0"});
        let reserved = json!({"generation":"2","status":"3","remaining":"999999","reserved":"1"});
        assert!(activation_needed("tool-attach", &idle) && activation_needed("parent-attach", &idle));
        assert!(!activation_needed("parent-reserve", &idle), "a reserve before the attach is the law-denied step");
        assert!(activation_needed("parent-reserve", &attached));
        // A rerun finds every step done and submits nothing.
        for step in ["tool-attach", "parent-attach", "parent-reserve"] {
            assert!(!activation_needed(step, &reserved), "{step}");
        }
        assert!(!activation_needed("tool-attach", &attached), "an attached tool is left alone");
        assert_eq!(ACTIVATION_STEPS.iter().map(|s| s.0).collect::<Vec<_>>(), ["tool-attach", "parent-attach", "parent-reserve"], "attach precedes reserve");
    }
    use super::*;

    const FIXTURE: &[u8] = include_bytes!("../tests/fixtures/sandstorm-index-2026-10-27.json");

    fn scratch(name: &str) -> PathBuf {
        let dir = std::env::temp_dir().join(format!("mini-apps-{name}-{}", std::process::id()));
        let _ = fs::remove_dir_all(&dir);
        fs::create_dir_all(&dir).unwrap();
        dir
    }

    fn fixture() -> Vec<Entry> {
        parse_index(FIXTURE).unwrap()
    }

    #[test]
    fn apps_fixture_parses_whole_with_the_known_apps() {
        let entries = fixture();
        assert_eq!(entries.len(), 98);
        let slides = resolve(&entries, "7qvcjh7gk0rzdx1s3c8gufd288sesf6vvdt297756xcv4q8xxvhh").unwrap();
        assert_eq!(slides.name, "Hacker Slides");
        assert_eq!(slides.package_id, "f0277a5dce2e1c6af0cce188241411a4");
        assert_eq!(slides.version, "0.4.0");
        let todos = resolve(&entries, "5830d70137cdae158118884da8790870").unwrap();
        assert_eq!(todos.name, "Simple Todos");
        assert_eq!(todos.app_id, "0dp7n6ehj8r5ttfc0fj0au6gxkuy1nhw2kx70wussfa1mqj8tf80");
        assert_eq!(todos.author, "Asheesh Laroia");
        assert!(todos.categories.contains(&"Productivity".to_owned()));
    }

    #[test]
    fn apps_unknown_and_malformed_selectors_refuse_by_name() {
        let entries = fixture();
        let missing = resolve(&entries, "zzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzz").unwrap_err();
        assert!(missing.starts_with("unknownApp:"), "{missing}");
        let short = resolve(&entries, "etherpad").unwrap_err();
        assert!(short.starts_with("unknownApp:"), "{short}");
        assert!(resolve(&entries, "F0277A5DCE2E1C6AF0CCE188241411A4").unwrap_err().starts_with("unknownApp:"));
    }

    #[test]
    fn apps_search_shows_the_featured_set_first_with_its_typed_tools() {
        let entries = demo_index();
        let all = search(&entries, "", None);
        assert_eq!(all.len(), entries.len());
        let names: Vec<&str> = all.iter().take(FEATURED.len()).map(|e| e.name.as_str()).collect();
        assert_eq!(names[0], "Etherpad");
        assert_eq!(names.len(), FEATURED.len(), "search shows the whole featured set first: {names:?}");
        assert!(all[FEATURED.len()..].iter().all(|e| featured(&e.app_id).is_none()));
        let pad = entry_json(all[0], &Verdict { state: "unverified".into(), reason: None, raw_bytes: None, signed_app_id: None, running: 0 });
        assert_eq!(pad["featured"]["rank"], 1);
        assert_eq!(pad["packageBuiltAt"], "2026-10-29T10:27:05Z", "a fresh package reports its recorded build time");
        assert_eq!(pad["upstreamVersion"], "3.3.12-1");
        assert!(pad["featured"].get("agentHook").is_none());
        assert_eq!(pad["typedInterface"]["status"], "native-attachment-required", "the pinned package is the declared one");
        assert!(pad["typedInterface"]["tools"].as_array().unwrap().iter().any(|tool| tool["operation"] == "document.replace"));
        let old = all.iter().find(|e| e.pinned.is_none()).unwrap();
        let old = entry_json(old, &Verdict { state: "unverified".into(), reason: None, raw_bytes: None, signed_app_id: None, running: 0 });
        assert_eq!(old["packageBuiltAt"], "", "the store createdAt is never promoted to a build time");
        assert_eq!(old["upstreamVersion"], "");
    }

    #[test]
    fn apps_typed_discovery_requires_the_declared_package_and_hides_internal_tools() {
        // Any declaration carrying an internal operation (packages get repackaged under new ids, so
        // the entry is the market's entry for that declaration, not a pinned index row).
        let (_, declared) = interfaces::declarations().iter()
            .find(|(_, d)| d["operations"].as_object().unwrap().values().any(|op| op["internal"] == true))
            .expect("a declaration with an internal operation");
        let internal: Vec<&String> = declared["operations"].as_object().unwrap().iter()
            .filter(|(_, op)| op["internal"] == true).map(|(name, _)| name).collect();
        let mut entry = fixture()[0].clone();
        entry.app_id = declared["appId"].as_str().unwrap().to_owned();
        entry.package_id = declared["packageId"].as_str().unwrap().to_owned();
        let verdict = Verdict { state: "unverified".into(), reason: None, raw_bytes: None, signed_app_id: None, running: 0 };
        let shown = entry_json(&entry, &verdict);
        let interface = &shown["typedInterface"];
        assert_eq!(interface["status"], "native-attachment-required");
        let tools = interface["tools"].as_array().unwrap();
        assert!(!tools.is_empty());
        assert!(tools.iter().all(|tool| !internal.iter().any(|name| tool["operation"] == name.as_str())), "internal operations are never tools");
        assert!(tools.iter().all(|tool| tool["inputSchema"].is_object() && tool["outputSchema"].is_object()));
        entry.package_id = "00000000000000000000000000000000".into();
        let shown = entry_json(&entry, &verdict);
        let mismatch = &shown["typedInterface"];
        assert_eq!(mismatch["status"], "package-mismatch");
        assert_eq!(mismatch["schemaAvailable"], false);
        assert!(mismatch.get("tools").is_none());
    }

    const FRESH: &[u8] = include_bytes!("../tests/fixtures/fresh-local-index-2026-10-29.json");

    /// The index the demo box serves: the upstream index with the operator's pinned entries for the
    /// packages we build ourselves merged in (deploy/market/fresh-index.py writes them; the fixture is
    /// its output for the packages built so far).
    fn demo_index() -> Vec<Entry> {
        merge_local(fixture(), parse_index(FRESH).unwrap()).unwrap()
    }

    #[test]
    fn apps_every_featured_app_id_resolves_to_an_installable_package() {
        // Installable: the entry exists in the merged index AND its bytes have a source, either the
        // upstream store's package URL (an unpinned entry) or an operator pin that names the whole
        // SHA-256 (which must begin with the packageId, the package's identity); a pin with no URL is
        // adopted from a box-local file (deploy/market/fresh-adopt). A featured appId that no index lists cannot be searched or installed.
        let entries = demo_index();
        let mut unresolved = Vec::new();
        for app_id in FEATURED {
            match entries.iter().find(|e| e.app_id == *app_id) {
                None => unresolved.push(format!("{app_id}: in neither the upstream index nor the operator pins")),
                Some(e) => match &e.pinned {
                    None => {}
                    Some(pin) if !pin.sha256.starts_with(&e.package_id) => {
                        unresolved.push(format!("{app_id}: pin {} does not begin with packageId {}", pin.sha256, e.package_id))
                    }
                    Some(_) => {}
                },
            }
        }
        assert!(unresolved.is_empty(), "featured appIds that cannot be installed:\n{}", unresolved.join("\n"));
    }

    #[test]
    fn apps_fresh_pins_are_listed_searched_and_resolved_beside_the_upstream_index() {
        let entries = demo_index();
        let fresh = parse_index(FRESH).unwrap();
        assert!(!fresh.is_empty());
        for pinned in &fresh {
            let found = resolve(&entries, &pinned.package_id).unwrap();
            assert_eq!(found.app_id, pinned.app_id);
            let pin = found.pinned.as_ref().expect("a fresh package is operator-pinned");
            assert!(pin.sha256.starts_with(&pinned.package_id), "the pin is the package's own SHA-256");
            assert!(pin.package_url.is_none(), "adopt mode: the demo box has no egress to the build host");
            assert!(!found.package_built_at.is_empty(), "{}: a fresh package reports its real build time", found.name);
            assert!(search(&entries, &found.name, None).iter().any(|e| e.package_id == pinned.package_id), "{} is searchable", found.name);
        }
        assert_eq!(entries.len(), 98 + fresh.len());
    }

    #[test]
    fn apps_unmaintained_duplicates_stay_out_of_the_featured_set() {
        // docs/SPK-FRESH-2026-10-29.md records the upstream evidence and the
        // maintained surface (where one exists) for each removal.
        for app_id in [
            "f5z8uwz7ynf89c286f9d5tse5dwjknv32nyd78qzsyema3zf9m8h", // SandCal
            "1gda5n8p8zsc0r9pcana2yjgtvsq169068k4ve8mk68z4x9fvzuh", // EtherDraw
            "nn7axgy3y8kvd0m1mtk3cwca34t916p5d7m4j1j2e874nuz3t8y0", // FileDrop
            "70xjeuj6t85v3s9a3up583q97wu044mnt8aekf3pqs41e3ct2v70", // Tube
            "u0yh8xndrzewsfx7z0jemv9scvyxtkwr2qzepgg93hm6r77m6580", // 2048
            "yp9xt15y8s0rsuntnhgnr510qpcvm2tatd9mn1gzwr2au8h2n4p0", // Simple Chat
        ] {
            assert!(featured(app_id).is_none(), "{app_id} returned without fresh packaging evidence");
        }
    }

    #[test]
    fn apps_search_is_case_insensitive_over_text_and_filters_categories() {
        let entries = fixture();
        let pads = search(&entries, "ETHERPAD", None);
        assert!(pads.iter().any(|e| e.package_id == "aee0806c9547d1f53c1ccef38ac195ba"));
        let rss = search(&entries, "tiny tiny", None);
        assert_eq!(rss.len(), 1);
        assert_eq!(rss[0].package_id, "ac6dfded255f6ea86172fb62064772fc");
        let office = search(&entries, "", Some("office"));
        assert!(office.iter().any(|e| e.name == "Simple Todos"));
        assert!(office.iter().all(|e| e.categories.iter().any(|c| c.eq_ignore_ascii_case("Office"))));
        assert!(search(&entries, "no such app anywhere", None).is_empty());
        assert_eq!(search(&entries, "", None).len(), 98);
    }

    #[test]
    fn apps_index_is_data_a_malformed_entry_refuses_the_file() {
        let mut value: Value = serde_json::from_slice(FIXTURE).unwrap();
        value["apps"][3]["packageId"] = json!("not-hex");
        let error = parse_index(&serde_json::to_vec(&value).unwrap()).unwrap_err();
        assert!(error.contains("index entry 3") && error.contains("packageId"), "{error}");
        let mut value: Value = serde_json::from_slice(FIXTURE).unwrap();
        value["apps"][0]["appId"] = json!("Short");
        assert!(parse_index(&serde_json::to_vec(&value).unwrap()).is_err());
        let mut value: Value = serde_json::from_slice(FIXTURE).unwrap();
        value["apps"][1]["name"] = json!("evil\u{7}bell");
        assert!(parse_index(&serde_json::to_vec(&value).unwrap()).unwrap_err().contains("control bytes"));
        let mut value: Value = serde_json::from_slice(FIXTURE).unwrap();
        let dup = value["apps"][0].clone();
        value["apps"].as_array_mut().unwrap().push(dup);
        assert!(parse_index(&serde_json::to_vec(&value).unwrap()).unwrap_err().contains("twice"));
        assert!(parse_index(br#"{"notapps":[]}"#).unwrap_err().contains("apps array"));
        assert!(parse_index(&vec![b' '; MAX_INDEX + 1]).unwrap_err().contains("exceeds"));
    }

    #[test]
    fn apps_index_check_round_trips_the_known_fields_only() {
        let entries = fixture();
        let rendered = render_index(&entries);
        let again = parse_index(&serde_json::to_vec(&rendered).unwrap()).unwrap();
        assert_eq!(again, entries);
        assert_eq!(rendered["format"], "mini-market-index-v1");
        // The index's author pictures and usernames are not carried: data we do not show.
        assert!(rendered["apps"][0]["author"].get("picture").is_none());
    }

    #[test]
    fn apps_index_check_merges_operator_pinned_entries_and_refuses_collisions() {
        let upstream = fixture();
        let oracle = json!({"apps":[{
            "appId":"ephaf4h4cx8f9s36hmukm4yzkznyhqjhvj8efp3at9cru2zn10mh","packageId":"bded240f916b93d51ad5e90ffc12d8a8",
            "name":"veri7vn oracle","version":"4","versionNumber":4,"author":{"name":"ember"},
            "packageBuiltAt":"2026-10-29T05:00:00Z","upstreamVersion":"1.2.3",
            "sha256":"bded240f916b93d51ad5e90ffc12d8a8cc9985e35306105eff69f926b3333ed0","class":"L"}]});
        let local = parse_index(&serde_json::to_vec(&oracle).unwrap()).unwrap();
        let pin = local[0].pinned.clone().unwrap();
        assert_eq!((pin.class.as_deref(), pin.package_url), (Some("L"), None));
        let merged = merge_local(upstream.clone(), local.clone()).unwrap();
        assert_eq!(merged.len(), 99);
        let rendered = render_index(&merged);
        assert_eq!(rendered["pinned"], 1);
        let again = parse_index(&serde_json::to_vec(&rendered).unwrap()).unwrap();
        assert_eq!(again, merged, "the pin survives the round trip");
        let shown = entry_json(&merged[98], &verdict(Path::new("/nonexistent"), Path::new("/nonexistent"), "bded240f916b93d51ad5e90ffc12d8a8"));
        assert_eq!(shown["suggestedClass"], "L");
        assert_eq!(shown["packageBuiltAt"], "2026-10-29T05:00:00Z");
        assert_eq!(shown["upstreamVersion"], "1.2.3");
        assert!(shown["packageUrl"].as_str().unwrap().starts_with("file: adopted"));
        // A pin whose sha256 does not start with its packageId, or without a pin at all, refuses.
        let mut bad = oracle.clone();
        bad["apps"][0]["sha256"] = json!("0000000000000000000000000000000000000000000000000000000000000000");
        assert!(parse_index(&serde_json::to_vec(&bad).unwrap()).unwrap_err().contains("does not start with packageId"));
        let unpinned = parse_index(&serde_json::to_vec(&json!({"apps":[serde_json::from_slice::<Value>(FIXTURE).unwrap()["apps"][0]]})).unwrap()).unwrap();
        assert!(merge_local(upstream.clone(), unpinned).unwrap_err().contains("no sha256 pin"));
        // A pinned packageId the upstream index already names is refused by name.
        let mut shadow = oracle;
        shadow["apps"][0]["packageId"] = json!("5830d70137cdae158118884da8790870");
        shadow["apps"][0]["sha256"] = json!("5830d70137cdae158118884da879087000000000000000000000000000000000");
        let shadow = parse_index(&serde_json::to_vec(&shadow).unwrap()).unwrap();
        assert!(merge_local(upstream, shadow).unwrap_err().contains("collides"));
    }

    #[test]
    fn a_listing_says_what_each_state_means_and_what_a_member_can_do() {
        let v = |state: &str, reason: Option<&str>| Verdict { state: state.into(), reason: reason.map(str::to_owned), raw_bytes: None, signed_app_id: None, running: 0 };
        let fresh = verdict_says(&v("unverified", None));
        assert!(fresh.contains("not checked on this box yet") && fresh.contains("`apps install`") && !fresh.contains("unverified"), "{fresh}");
        assert_eq!(verdict_says(&v("refused", Some("sizeOverProfile"))), "refused here (sizeOverProfile): an install is refused the same way");
        assert!(tools_says("declaration-unavailable").starts_with("no typed tools declared: use it through its own page"));
        assert!(!tools_says("declaration-unavailable").contains("unavailable"), "the state reads as a choice, not a failure");
        assert_eq!(qualification::line(None), "its lifecycle not yet tried on this box");
        let entry = parse_index(include_bytes!("../tests/fixtures/sandstorm-index-2026-10-27.json")).unwrap().remove(0);
        let shown = entry_json(&entry, &v("unverified", None));
        assert_eq!(shown["verdict"]["state"], "unverified", "the JSON keeps the machine state");
        assert!(shown["verdict"]["says"].as_str().unwrap().contains("installing it checks"));
        assert!(shown["typedInterface"]["says"].as_str().is_some());
    }

    #[test]
    fn apps_verdict_defaults_to_unverified_and_reads_meta_and_ingest() {
        let dir = scratch("verdict");
        let meta = dir.join("meta");
        let verdicts = dir.join("verdicts");
        fs::create_dir_all(&meta).unwrap();
        fs::create_dir_all(&verdicts).unwrap();
        let unknown = verdict(&verdicts, &meta, "f0277a5dce2e1c6af0cce188241411a4");
        assert_eq!(unknown.state, "unverified");
        assert_eq!(suggested_class(unknown.raw_bytes), "unknown until fetched");
        fs::write(meta.join("f0277a5dce2e1c6af0cce188241411a4.json"), br#"{"bytes":16778192}"#).unwrap();
        let fetched = verdict(&verdicts, &meta, "f0277a5dce2e1c6af0cce188241411a4");
        assert_eq!((fetched.state.as_str(), suggested_class(fetched.raw_bytes)), ("unverified", "S"));
        fs::write(meta.join("2a2c05041cb4285da884d114e4820298.json"), br#"{"bytes":300000000}"#).unwrap();
        let big = verdict(&verdicts, &meta, "2a2c05041cb4285da884d114e4820298");
        assert_eq!((big.state.as_str(), big.reason.as_deref()), ("refused", Some("sizeOverProfile")));
        fs::write(
            verdicts.join("aee0806c9547d1f53c1ccef38ac195ba.json"),
            br#"{"verdict":"refused","reason":"unsupportedBridge: apiPath \"../x\"","signedAppId":"h37dm17aa89yrd8zuqpdn36p6zntumtv08fjpu8a8zrte7q1cn60"}"#,
        )
        .unwrap();
        let pad = verdict(&verdicts, &meta, "aee0806c9547d1f53c1ccef38ac195ba");
        assert_eq!(verdict_line(&pad), "refused: unsupportedBridge: apiPath \"../x\"");
        fs::write(verdicts.join("5830d70137cdae158118884da8790870.json"), br#"{"verdict":"verified","running":2}"#).unwrap();
        assert_eq!(verdict_line(&verdict(&verdicts, &meta, "5830d70137cdae158118884da8790870")), "verified, running 2");
    }


    #[test]
    fn apps_verdict_is_valid_only_for_the_ingest_that_wrote_it() {
        let dir = scratch("verdict-key");
        let meta = dir.join("meta");
        let verdicts = dir.join("verdicts");
        fs::create_dir_all(&meta).unwrap();
        fs::create_dir_all(&verdicts).unwrap();
        let package = "aee0806c9547d1f53c1ccef38ac195ba";
        let refused_by = |key: &str| format!(r#"{{"verdict":"refused","reason":"installRefused: x","ingestKey":"{key}"}}"#);
        fs::write(verdicts.join(format!("{package}.json")), refused_by("aaaa")).unwrap();
        // Ingest A is running: its own refusal is reused.
        fs::write(verdicts.join(INGEST_KEY_FILE), "aaaa\n").unwrap();
        assert_eq!(verdict(&verdicts, &meta, package).state, "refused");
        // A re-genesis onto ingest B: the same file is another ingest's answer, so the app is unverified again.
        fs::write(verdicts.join(INGEST_KEY_FILE), "bbbb\n").unwrap();
        let b = verdict(&verdicts, &meta, package);
        assert_eq!((b.state.as_str(), b.reason.as_deref()), ("unverified", None));
        // A verdict with no key at all (written before keys existed) is also not B's.
        fs::write(verdicts.join(format!("{package}.json")), br#"{"verdict":"verified","running":1}"#).unwrap();
        assert_eq!(verdict(&verdicts, &meta, package).state, "unverified");
        // B's own verdict is read.
        fs::write(verdicts.join(format!("{package}.json")), refused_by("bbbb")).unwrap();
        assert_eq!(verdict(&verdicts, &meta, package).state, "refused");
    }

    #[test]
    fn apps_request_law_renders_from_lean_and_binds_its_two_placeholders() {
        let bound = law("12648853121532543039", "8").unwrap();
        let text = serde_json::to_string(&bound).unwrap();
        assert!(!text.contains("{REQUESTER}") && !text.contains("{MANAGER}"));
        assert!(LAW_TEMPLATE.contains("Written by scripts/AppsRequestTemplate.lean"));
        assert_eq!(LAW_TEMPLATE.lines().filter(|l| !l.trim_start().starts_with("--")).count(), 3, "three clauses: management, setup, outcome");
        assert!(law("12", "x").is_err());
    }

    #[test]
    fn apps_request_words_encode_the_package_and_app_identity() {
        let [hi, lo] = package_words("f0277a5dce2e1c6af0cce188241411a4").unwrap();
        assert_eq!(hi, 0xf0277a5dce2e1c6a);
        assert_eq!(lo, 0xf0cce188241411a4);
        assert!(package_words("F0277a5dce2e1c6af0cce188241411a4").is_err());
        let words = app_words("7qvcjh7gk0rzdx1s3c8gufd288sesf6vvdt297756xcv4q8xxvhh").unwrap();
        assert!(words.iter().any(|w| *w != 0));
        assert_ne!(words, app_words("0dp7n6ehj8r5ttfc0fj0au6gxkuy1nhw2kx70wussfa1mqj8tf80").unwrap());
        assert!(app_bytes("bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb").is_err(), "b is outside Sandstorm's alphabet");
        assert_eq!(class_code("M").unwrap(), 2);
        assert!(class_code("auto").is_err());
    }


    #[test]
    fn apps_birth_source_matches_the_host_decoder_key_sets() {
        // Host/Json.lean: grainBirthIntentFrom ["subject","nonce","applicationGrainBirth","grants"];
        // the composite ["tariff","applicationBirth","tool","parent"]; applicationBirthContext
        // ["genesis","template","creator","nonce","application","sourceCapabilities","funding","feePayer"];
        // applicationSpec (ten keys); grainBirthPeer ["task","capability","observeCapability","targetRoot","before"].
        let context = json!({"type":"minidregg-participant-birth-context-v1","genesis":{"domain":"1","factoryId":"10"},"template":{"issuer":"5"},
            "sourceCapabilities":["42"],"funding":[],"feePayer":"77","grants":[{"kind":"object","target":"10","capability":"55"},{"kind":"account","target":"77","capability":"42"}]});
        let ids: std::collections::BTreeMap<String, String> = [("app","9001"),("packageManifest","9002"),("snapshotManifest","9003"),("appOwnerCapability","9101"),("appControlCapability","9102"),("packageOwnerCapability","9103"),("packageControlCapability","9104"),("snapshotOwnerCapability","9105"),("snapshotControlCapability","9106")].iter().map(|(k,v)| (k.to_string(), v.to_string())).collect();
        let tool_ref = json!({"target":"7902","observeCapability":"8101","operationCapability":"8102"});
        let view = json!({"cell":{"root":"abc","grain":{"generation":"1","status":"1","remaining":"50","reserved":"0"}}});
        assert_eq!(birth_reserve_amount(&json!({"base":"2","perBirth":"1"})).unwrap(), "5");
        assert!(birth_reserve_amount(&json!({"base":"2"})).is_err());
        let reserve = reserve_intent("9", "77", "slides", &json!({"target":"7902","observeCapability":"8101","operationCapability":"8102"}), &view, "5").unwrap();
        assert_eq!(reserve["grain"]["operation"], json!({"type":"reserve","amount":"5"}));
        assert_eq!(reserve["grain"]["capability"], "8102");
        assert_eq!(reserve["grain"]["expectedTargetRoot"], "abc");
        assert_eq!(reserve["grain"]["before"]["reserved"], "0");
        assert_eq!(reserve["grants"], json!([{"kind":"object","target":"7902","capability":"8102"}]));
        let tool = birth_peer(&tool_ref, &view).unwrap();
        let parent = birth_peer(&json!({"target":"7901","observeCapability":"8201"}), &view).unwrap();
        assert_eq!(tool["capability"], "8102");
        assert_eq!(parent["capability"], "8201", "observe stands in when no operation capability is held");
        let source = app_birth_source("77", "123", &context, &ids, &tool, &parent, &json!({"base":"2","perBirth":"1"})).unwrap();
        let keys = |v: &Value| -> Vec<String> { let mut k: Vec<String> = v.as_object().unwrap().keys().cloned().collect(); k.sort(); k };
        assert_eq!(keys(&source), ["applicationGrainBirth","grants","nonce","subject"]);
        let composite = &source["applicationGrainBirth"];
        assert_eq!(keys(composite), ["applicationBirth","parent","tariff","tool"]);
        assert_eq!(keys(&composite["applicationBirth"]), ["application","creator","feePayer","funding","genesis","nonce","sourceCapabilities","template"]);
        assert_eq!(keys(&composite["applicationBirth"]["application"]), ["app","appControlCapability","appOwnerCapability","owner","packageControlCapability","packageManifest","packageOwnerCapability","snapshotControlCapability","snapshotManifest","snapshotOwnerCapability"]);
        assert_eq!(keys(&composite["tool"]), ["before","capability","observeCapability","targetRoot","task"]);
        assert_eq!(composite["applicationBirth"]["application"]["owner"], "77");
        assert_eq!(composite["applicationBirth"]["creator"], "77");
        assert_eq!(composite["applicationBirth"]["application"]["app"], "9001");
        assert_eq!(source["grants"].as_array().unwrap().len(), 4, "the context's grants plus the tool and parent grants");
        assert_eq!(source["grants"][2]["target"], "7902");
    }

    #[test]
    fn retained_install_documents_must_belong_to_one_birth() {
        let dir = scratch("one-birth");
        let born = |app: &str| json!({"applicationGrainBirth":{"applicationBirth":{"application":{"app":app,"packageManifest":"2"}}}});
        let (source, receipt, delegation) = (dir.join("source.json"), dir.join("outcome.json"), dir.join("delegation.json"));
        assert!(!retained_birth_is(&source, &receipt, &born("11")), "nothing retained");
        std::fs::write(&source, born("11").to_string()).unwrap();
        std::fs::write(&receipt, "{}").unwrap();
        assert!(retained_birth_is(&source, &receipt, &born("11")));
        assert!(!retained_birth_is(&source, &receipt, &born("12")), "a retry that births again must not keep the first source");
        let selector = |app: &str| json!({"selector":{"app":app}});
        assert!(!delegation_names_app(&delegation, &selector("11")), "absent");
        std::fs::write(&delegation, selector("11").to_string()).unwrap();
        assert!(delegation_names_app(&delegation, &selector("11")));
        assert!(!delegation_names_app(&delegation, &selector("12")), "a delegation for another birth is replaced");
        assert!(!delegation_names_app(&delegation, &json!({})), "a selector without an app never matches");
    }

    #[test]
    fn apps_config_names_the_manager_and_the_metered_references() {
        let dir = scratch("config");
        let path = dir.join("apps.json");
        fs::write(&path, br#"{"protocol":"mini-apps-config-v1","managementSubject":"8","toolRef":"world-tool","parentRef":"world-parent"}"#).unwrap();
        let config = apps_config(&path).unwrap();
        assert_eq!((config.management_subject.as_str(), config.tool_ref.as_str(), config.parent_ref.as_str()), ("8", "world-tool", "world-parent"));
        assert_eq!(config.tariff, json!({"base":"2","perBirth":"1"}));
        assert!(apps_config(&dir.join("none.json")).unwrap_err().starts_with("appsConfigUnavailable"));
        fs::write(&path, br#"{"protocol":"other"}"#).unwrap();
        assert!(apps_config(&path).is_err());
    }


    #[test]
    fn apps_metered_reference_names_the_inbox_file_it_looked_for() {
        let dir = scratch("inbox");
        let root = dir.join("ws");
        let home = dir.join("home");
        fs::create_dir_all(root.join("refs")).unwrap();
        fs::create_dir_all(home.join("inbox")).unwrap();
        assert_eq!(inbox_file(&home, "tool"), home.join("inbox").join("tool.json"));
        let ws = json!({"subject":"77"});
        let refused = metered_reference(&root, &ws, Some(&home), "tool", "tool").unwrap_err();
        assert!(refused.starts_with("meteredGrantRequired:") && refused.contains("inbox/tool.json"), "{refused}");
        let no_home = metered_reference(&root, &ws, None, "parent", "parent").unwrap_err();
        assert!(no_home.contains("no --home given"), "{no_home}");
        // An imported reference is found without touching the inbox.
        fs::write(root.join("refs").join("tool.json"), br#"{"type":"minidregg-participant-reference-v1","name":"tool","kind":"object","target":"7902","observeCapability":"8101","operationCapability":"8101","controlCapability":"8102"}"#).unwrap();
        assert_eq!(metered_reference(&root, &ws, Some(&home), "tool", "tool").unwrap()["target"], "7902");
    }


    #[test]
    fn apps_bootstrap_source_is_the_workroom_birth_of_two_grain_tasks() {
        let context = json!({"type":"minidregg-participant-birth-context-v1","genesis":{"domain":"1","factoryId":"10"},"template":{"issuer":"5","ownerBudget":"100000","lifetime":"10000"},
            "sourceCapabilities":["42"],"funding":[],"feePayer":"8","grants":[{"kind":"object","target":"10","capability":"55"},{"kind":"account","target":"8","capability":"42"}],
            "grainBirthTariff":{"base":"2","perBirth":"1"}});
        let ids: std::collections::BTreeMap<String, String> = [("parentTask","7901"),("toolTask","7902"),("parentOwnerCapability","71"),("parentControlCapability","72"),("toolOwnerCapability","81"),("toolControlCapability","82")].iter().map(|(k,v)| (k.to_string(), v.to_string())).collect();
        let source = bootstrap_source("8", "22000", &context, &ids, "100000").unwrap();
        let keys = |v: &Value| -> Vec<String> { let mut k: Vec<String> = v.as_object().unwrap().keys().cloned().collect(); k.sort(); k };
        assert_eq!(keys(&source), ["birth","grants","nonce","subject"]);
        assert_eq!(keys(&source["birth"]), ["creator","feePayer","funding","genesis","grainBirthTariff","nonce","resources","sourceCapabilities","template"]);
        let resources = source["birth"]["resources"].as_array().unwrap();
        assert_eq!(resources.len(), 2);
        assert_eq!(resources[0]["storage"], "grain");
        assert_eq!(resources[0]["target"], "7901");
        // The holder form (AgentGrain.holderPolicy, ruling Option A): any holder of a delegated
        // grant may make the birth witness; no worker subject is named.
        assert_eq!(resources[0]["holderWitnessGeneration"], "1");
        assert!(resources[0].get("workerSubject").is_none());
        assert_eq!(resources[0]["budget"], "100000");
        assert_eq!(resources[1]["target"], "7902");
        assert!(resources[1].get("workerSubject").is_none(), "the tool names no worker, as the workroom births it");
        assert_eq!(source["birth"]["feePayer"], "8");
    }

    #[test]
    fn apps_grain_ids_are_decimal_app_resources() {
        assert!(valid_grain("a4501"));
        assert!(valid_grain("a1"));
        assert!(!valid_grain("a0501"));
        assert!(!valid_grain("4501"));
        assert!(!valid_grain("a"));
        assert!(!valid_grain("a45x1"));
        assert_eq!(camel("request-id"), "requestId");
    }

    #[test]
    fn apps_worker_reply_decodes_to_three_outcomes() {
        assert!(report(&json!({"decided":true,"state":"running","detail":"a4501"}), false).is_ok());
        let refused = report(&json!({"decided":true,"refused":"funding","detail":"purse 3 < tariff 5"}), false).unwrap_err();
        assert!(refused.starts_with("funding:"));
        let undecided = report(&json!({"decided":false,"state":"stopping","detail":"since 12:00","exactRetry":"mini apps status --grain a4501"}), false).unwrap_err();
        assert!(undecided.starts_with("undecided:") && undecided.ends_with("mini apps status --grain a4501"), "{undecided}");
    }

    #[test]
    fn apps_worker_call_refuses_an_absent_socket_by_name() {
        let dir = scratch("socket");
        let error = worker_call(&dir.join("none.sock"), &json!({"protocol":WORKER_PROTOCOL,"verb":"list"})).unwrap_err();
        assert!(error.starts_with("appsWorkerUnavailable:"), "{error}");
    }
}
