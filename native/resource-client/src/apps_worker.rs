//! `mini apps-worker`: the operator-side custodian of the app market
//! (docs/APP-MARKET-2026-10-27.md §4). It runs as the grain world's operator (a
//! system unit, User=mini-core), reaches the SPK broker in mini-core's user manager, and acts on admitted install
//! requests through `spk-host grain` and the ordinary `mini` client verbs, the
//! way `scripts/spk-platform/grain-journey.sh` does by hand. It holds no member
//! key; the member is named by the socket peer (`SO_PEERCRED`), never by a
//! field of the request.
//!
//! Two sockets:
//! - `worker.sock` (0660, group `mini-sessions`): members' verbs, one JSON line
//!   each way, bounded. Every reply is a decoded outcome: `decided` with a
//!   receipt or a refusal by name, or `undecided` with its exact retry.
//! - `edge.sock` (0660, group `mini-edge`): the grain front asks `connect` for a
//!   (grain, route) and receives the connected custodian socket over
//!   `SCM_RIGHTS`. Route sockets live under the operator's 0700 state root; the
//!   worker is the one process that reaches them, and it adds no authority: the
//!   custodian still checks the token the browser presents.
//!
//! Every step is idempotent on its retained artifact (`requests/<id>.json`
//! phases; `spk-host grain`'s own one-shot markers), so a lost reply is answered
//! by the exact retry of the same request id and a second install is never
//! issued (SPK-LIFECYCLE).

use crate::{absolute, hex, path, Args, Result};
use serde_json::{json, Map, Value};
use std::fs;
use std::io::{BufRead, BufReader, Read, Write};
use std::os::unix::fs::{DirBuilderExt, OpenOptionsExt, PermissionsExt};
use std::os::unix::io::{AsRawFd, FromRawFd, IntoRawFd};
use std::os::unix::net::{UnixListener, UnixStream};
use std::path::{Path, PathBuf};
use std::process::Command;
use std::collections::HashMap;
use std::sync::{mpsc, Arc, Mutex};
use std::time::{Duration, SystemTime, UNIX_EPOCH};

use super::{valid_app_id, valid_grain, valid_package_id, WORKER_PROTOCOL};

const MAX_LINE: usize = 256 * 1024;
const MAX_DOCUMENT: usize = 64 * 1024;
const MEMBER_PREFIX: &str = "mini-s-";
pub(crate) const IDENTITY_NOTICE: &str = "v1: this grain signs for every member it is shared with as one guest subject; members are told apart by route, token and receipt, not by the app (per-member subjects are v2)";

fn now() -> String {
    SystemTime::now().duration_since(UNIX_EPOCH).map(|d| d.as_secs().to_string()).unwrap_or_default()
}

fn text<'a>(value: &'a Value, key: &str) -> Result<&'a str> {
    value.get(key).and_then(Value::as_str).ok_or_else(|| format!("request lacks {key}"))
}

fn private_dir(path: &Path) -> Result<()> {
    if path.is_dir() {
        return Ok(());
    }
    fs::DirBuilder::new().mode(0o700).recursive(true).create(path).map_err(|e| format!("{}: {e}", path.display()))
}

fn write_json(path: &Path, value: &Value) -> Result<()> {
    let bytes = serde_json::to_vec_pretty(value).map_err(|e| e.to_string())?;
    let temp = path.with_extension("json.new");
    let _ = fs::remove_file(&temp);
    let mut file = fs::OpenOptions::new().write(true).create_new(true).mode(0o600).open(&temp).map_err(|e| format!("{}: {e}", temp.display()))?;
    file.write_all(&bytes).map_err(|e| e.to_string())?;
    fs::rename(&temp, path).map_err(|e| e.to_string())
}

fn read_json(path: &Path) -> Result<Value> {
    let bytes = crate::fsio::read_bounded(path, MAX_LINE)?;
    serde_json::from_slice(&bytes).map_err(|e| format!("{}: {e}", path.display()))
}

// ------------------------------------------------------------- the world

pub(crate) struct Installed {
    pub app: String,
    pub raw_sha256: String,
    pub signed_app_id: String,
    pub app_version: String,
}

pub(crate) struct RouteBound {
    pub directory: PathBuf,
    pub socket: PathBuf,
    pub browser_token_sha256: String,
    pub bootstrap_token_sha256: String,
    pub api_token_sha256: String,
    /// What a later enrollment needs, retained with the route: the guest session, its
    /// capability, the ticket and the issue anchor, the app and package observe capabilities.
    pub enrollment: Value,
}

/// The result of bringing a route's session enrollment up to the app's serving generation.
#[derive(Debug, PartialEq)]
pub(crate) enum Enrolled {
    /// The session already names the serving generation: nothing was submitted.
    Current(String),
    /// A new enrollment against the serving generation was accepted.
    Renewed(String),
}

/// The lifecycle outcome `spk-host grain` reports: STOP is minutes long.
#[derive(Debug, PartialEq)]
pub(crate) enum Lifecycle {
    Done,
    Undecided(String),
}

/// What the worker needs from the box. The process-backed world drives
/// `spk-host grain` and `mini`; tests supply a fake.
pub(crate) trait World {
    fn package(&self, package_id: &str) -> Result<Option<(PathBuf, String, u64)>>;
    fn want(&self, package_id: &str) -> Result<()>;
    /// `carry`: a previous world's grain export and the exporting Store's completion key: the new
    /// grain's /var starts as those exact bytes (`spk-host grain install --import`).
    fn install(&self, work: &Path, source: &Path, receipt: &Path, spk: &Path, class: &str, delegation: &Path, carry: Option<(&Path, &str)>) -> Result<Installed>;
    fn start(&self, app: &str) -> Result<Lifecycle>;
    fn stop(&self, app: &str) -> Result<Lifecycle>;
    fn status(&self, app: &str) -> Result<Value>;
    /// A participant route for `member` on `app` with `expected_host`: the
    /// session birth, the ticket under the delegated capability, the
    /// enrollment and `spk-host grain route`.
    fn route(&self, work: &Path, app: &str, member: &str, expected_host: &str) -> Result<RouteBound>;
    /// Enroll the route's guest session against the app's CURRENT serving generation (event28),
    /// closing a session still active for an older generation first. Idempotent per generation.
    fn enroll(&self, work: &Path, app: &str, member: &str, enrollment: &Value) -> Result<Enrolled>;
    fn export(&self, app: &str, out: &Path) -> Result<()>;
    fn identities(&self, app: &str) -> Result<Vec<Value>>;
    fn revoke_identity(&self, app: &str, token: &str) -> Result<()>;
    fn verdict(&self, package_id: &str, verdict: &Value) -> Result<()>;
    fn domain(&self) -> &str;
}

// --------------------------------------------------------------- the state

/// Open member connections one member may hold at once, and in all: a member cannot exhaust the box.
const MEMBER_CONNECTIONS: usize = 4;
const ALL_CONNECTIONS: usize = 64;
/// Install runs in flight per member and in all (each is an spk-ingest and a grain birth).
const MEMBER_INSTALLS: usize = 2;
const ALL_INSTALLS: usize = 4;
/// How long an install's handler waits for its run before answering `pending`: fast outcomes
/// (a refusal, `fetching`, an already-complete grain) are answered inline, a real install is not.
const INSTALL_GRACE: Duration = Duration::from_secs(5);

pub(crate) struct Worker {
    state: PathBuf,
    world: Box<dyn World + Send + Sync>,
    /// The management subject's nonce allocator and the world's one tool task, whose AgentGrain
    /// law admits one reserve at a time (Kernel/AgentGrain.lean): held around `World::route` and
    /// `World::enroll`, the only calls that allocate nonces or reserve, and nothing else.
    submit: Mutex<()>,
    /// One lock per grain record (`grains/<g>.json` and its origin table): a member verb that
    /// rewrites the record takes it without waiting; an install's start/route phases wait for it.
    grains: Mutex<HashMap<String, Arc<Mutex<()>>>>,
    /// Install runs in flight: request id -> member. Admission and run start happen under it,
    /// so one request id never has two runs.
    installs: Mutex<HashMap<String, String>>,
    install_grace: Duration,
}

fn request_file(state: &Path, id: &str) -> PathBuf {
    state.join("requests").join(format!("{id}.json"))
}

fn grain_file(state: &Path, grain: &str) -> PathBuf {
    state.join("grains").join(format!("{grain}.json"))
}

/// The generation of the latest begun run when that run is stopped (spk-host `grain status`'s
/// `runs[]`, the run `grain export` exports); `None` while it runs or is uncertain.
fn latest_stopped_generation(status: &Value) -> Option<String> {
    let runs = status.get("runs")?.as_array()?;
    let latest = runs.iter()
        .filter(|run| run.get("state").and_then(Value::as_str) != Some("never-begun"))
        .max_by_key(|run| run.get("generation").and_then(Value::as_str).and_then(|g| g.parse::<u64>().ok()).unwrap_or(0))?;
    (latest.get("state")?.as_str()? == "stopped").then(|| latest.get("generation")?.as_str().map(str::to_owned)).flatten()
}

fn refused(name: &str, detail: impl Into<String>) -> Value {
    json!({"protocol":WORKER_PROTOCOL,"decided":true,"refused":name,"state":"refused","detail":detail.into()})
}

fn undecided(state: &str, detail: impl Into<String>, retry: &str) -> Value {
    json!({"protocol":WORKER_PROTOCOL,"decided":false,"state":state,"detail":detail.into(),"exactRetry":retry})
}

fn performed(state: &str, detail: impl Into<String>, receipt: Value) -> Value {
    json!({"protocol":WORKER_PROTOCOL,"decided":true,"state":state,"detail":detail.into(),"receipt":receipt})
}

/// The exact retry of an install: the CLI's `--retry` takes the request id and the app it named.
fn install_retry(retained: &Value, id: &str) -> String {
    match retained.get("appId").and_then(Value::as_str) {
        Some(app) => format!("mini apps install --app {app} --retry {id}"),
        None => format!("mini apps retry --request-id {id}"),
    }
}

/// An install accepted and running in the worker: its retry answers the outcome once decided.
fn pending(id: &str, retained: &Value) -> Value {
    let since = retained.pointer("/run/since").and_then(Value::as_str).unwrap_or("");
    undecided("pending", format!("install {id} was accepted and runs in the worker (since {since}; the package ingest and the grain birth can take about half an hour); it continues if this command ends. Its exact retry answers pending until the outcome is decided, and never starts a second install"), &install_retry(retained, id))
}

/// The exact retry of a grain verb: the same verb with the same arguments.
fn verb_retry(request: &Value) -> String {
    let mut line = format!("mini apps {}", request.get("verb").and_then(Value::as_str).unwrap_or("status"));
    for key in ["grain", "to", "token"] {
        if let Some(value) = request.get(key).and_then(Value::as_str) {
            line.push_str(&format!(" --{key} {value}"));
        }
    }
    line
}

fn valid_member(name: &str) -> bool {
    !name.is_empty() && name.len() <= 32 && name.bytes().all(|b| b.is_ascii_lowercase() || b.is_ascii_digit() || b == b'-')
}

fn valid_class(class: &str) -> bool {
    matches!(class, "S" | "M" | "L" | "auto")
}

impl Worker {
    pub(crate) fn open(state: PathBuf, world: Box<dyn World + Send + Sync>) -> Result<Self> {
        for sub in ["requests", "grains", "work", "exports"] {
            private_dir(&state.join(sub))?;
        }
        Ok(Self {
            state, world, submit: Mutex::new(()), grains: Mutex::new(HashMap::new()),
            installs: Mutex::new(HashMap::new()), install_grace: INSTALL_GRACE,
        })
    }

    fn grain_lock(&self, grain: &str) -> Arc<Mutex<()>> {
        let mut grains = self.grains.lock().unwrap_or_else(|p| p.into_inner());
        grains.entry(grain.to_owned()).or_default().clone()
    }

    /// `World::route` under the submit lock: a session birth and a ticket issue each reserve on the tool task.
    fn bind_route(&self, work: &Path, app: &str, member: &str, host: &str) -> Result<RouteBound> {
        let _submit = self.submit.lock().unwrap_or_else(|p| p.into_inner());
        self.world.route(work, app, member, host)
    }

    fn grain_record(&self, grain: &str) -> Result<Option<Value>> {
        let path = grain_file(&self.state, grain);
        if !path.exists() {
            return Ok(None);
        }
        read_json(&path).map(Some)
    }

    fn owned_grain(&self, member: &str, grain: &str, allow_shared: bool) -> std::result::Result<Value, Value> {
        if !valid_grain(grain) {
            return Err(refused("grainRefused", format!("{grain:?} is not a grain id of the form a<app>")));
        }
        let Some(record) = self.grain_record(grain).map_err(|e| refused("stateUnavailable", e))? else {
            return Err(refused("unknownGrain", format!("{grain} is not a grain of this world")));
        };
        let owner = record.get("owner").and_then(Value::as_str).unwrap_or("");
        let shared = record.get("routes").and_then(Value::as_object).is_some_and(|r| r.contains_key(member));
        if owner != member && !(allow_shared && shared) {
            return Err(refused("notOwner", format!("{grain} belongs to another member")));
        }
        Ok(record)
    }

    /// One request: dispatch by verb, the member named by the peer.
    pub(crate) fn handle(self: &Arc<Self>, member: &str, request: &Value) -> Value {
        if request.get("protocol").and_then(Value::as_str) != Some(WORKER_PROTOCOL) {
            return refused("protocolRefused", "the request carries another protocol");
        }
        if !valid_member(member) {
            return refused("memberRefused", "the peer is not a member account");
        }
        let verb = request.get("verb").and_then(Value::as_str).unwrap_or("");
        match verb {
            "install" | "retry" => self.install(member, request),
            "list" => self.list(member),
            "status" => self.with_grain(member, request, true, |w, g, r| w.status(g, &r)),
            "open" => self.with_grain(member, request, true, |w, g, r| w.open_route(member, g, r)),
            "stop" => self.with_grain(member, request, false, |w, g, r| w.lifecycle(g, r, false)),
            "start" => self.with_grain(member, request, false, |w, g, r| w.lifecycle(g, r, true)),
            "share" => self.with_grain(member, request, false, |w, g, r| w.share(g, r, request)),
            "export" => self.with_grain(member, request, false, |w, g, r| w.export(g, r)),
            "delete" => self.with_grain(member, request, false, |w, g, r| w.delete(g, r)),
            "identities" => self.with_grain(member, request, true, |w, g, r| w.identities(g, &r)),
            "revoke-identity" => self.with_grain(member, request, false, |w, g, r| w.revoke_identity(g, r, request)),
            "renew" => self.with_grain(member, request, false, |w, g, r| w.renew(g, r)),
            other => refused("unknownVerb", format!("{other:?}")),
        }
    }

    /// A grain verb. The owner-only verbs rewrite the grain's record, so they hold its lock; one
    /// that finds another operation on the grain running answers `grainBusy` with its exact retry
    /// rather than waiting. The read verbs (shared too) take no lock: records are renamed whole.
    fn with_grain(&self, member: &str, request: &Value, allow_shared: bool, f: impl FnOnce(&Self, &str, Value) -> Value) -> Value {
        let grain = request.get("grain").and_then(Value::as_str).unwrap_or("");
        let lock = (!allow_shared && valid_grain(grain)).then(|| self.grain_lock(grain));
        let _held = match &lock {
            Some(lock) => match lock.try_lock() {
                Ok(guard) => Some(guard),
                Err(std::sync::TryLockError::Poisoned(p)) => Some(p.into_inner()),
                Err(std::sync::TryLockError::WouldBlock) => {
                    return undecided("grainBusy", format!("another operation on {grain} is running (a lifecycle step, a share, or its install's start and route); nothing was done"), &verb_retry(request));
                }
            },
            None => None,
        };
        match self.owned_grain(member, grain, allow_shared) {
            Ok(record) => f(self, grain, record),
            Err(refusal) => refusal,
        }
    }

    fn list(&self, member: &str) -> Value {
        let mut grains = Vec::new();
        if let Ok(entries) = fs::read_dir(self.state.join("grains")) {
            for entry in entries.flatten() {
                let Ok(record) = read_json(&entry.path()) else { continue };
                let owner = record.get("owner").and_then(Value::as_str).unwrap_or("");
                let shared = record.get("routes").and_then(Value::as_object).is_some_and(|r| r.contains_key(member));
                if owner == member || shared {
                    grains.push(json!({
                        "grain":record["grain"],"owner":owner,"shared":owner != member,"appId":record["appId"],
                        "indexName":record["indexName"],"class":record["class"],"state":record["state"],
                        "carriedFrom":record.get("carriedFrom").cloned().unwrap_or(Value::Null),
                        "carriedImageSha256":record.get("carriedImageSha256").cloned().unwrap_or(Value::Null),
                        "origin":record["origin"],"routes":record.get("routes").and_then(Value::as_object).map(|r| r.keys().cloned().collect::<Vec<_>>()).unwrap_or_default(),
                    }));
                }
            }
        }
        grains.sort_by(|a, b| a["grain"].as_str().cmp(&b["grain"].as_str()));
        performed("listed", format!("{} grain(s)", grains.len()), json!({"grains":grains,"identityNotice":IDENTITY_NOTICE}))
    }

    fn status(&self, grain: &str, record: &Value) -> Value {
        let app = record["app"].as_str().unwrap_or("");
        let live = match self.world.status(app) {
            Ok(status) => status,
            Err(error) => return undecided("statusUnavailable", error, &format!("mini apps status --grain {grain}")),
        };
        let identities = self.world.identities(app).unwrap_or_default();
        let runs = live.get("runs").and_then(Value::as_array).cloned().unwrap_or_default();
        let latest = runs.last().cloned().unwrap_or(Value::Null);
        let state = latest.get("state").and_then(Value::as_str).unwrap_or(record["state"].as_str().unwrap_or("unknown")).to_owned();
        performed(&state, format!("{grain} generation {}", latest.get("generation").and_then(Value::as_str).unwrap_or("?")), json!({
            "grain":grain,"origin":record["origin"],"class":record["class"],"appId":record["appId"],
            "indexName":record["indexName"],"owner":record["owner"],
            "routes":record.get("routes").and_then(Value::as_object).map(|r| r.keys().cloned().collect::<Vec<_>>()).unwrap_or_default(),
            "runs":runs,"identities":identities,"identityNotice":IDENTITY_NOTICE,
        }))
    }

    fn open_route(&self, member: &str, grain: &str, mut record: Value) -> Value {
        let lock = self.grain_lock(grain);
        let _guard = lock.lock().unwrap_or_else(|p| p.into_inner());
        if let Ok(Some(fresh)) = self.grain_record(grain) {
            record = fresh;
        }
        if record.pointer(&format!("/routes/{member}")).is_none() {
            return refused("noRoute", format!("{member} has no route on {grain}; the owner shares it with `mini apps share --grain {grain} --to {member}`"));
        }
        let app = record["app"].as_str().unwrap_or("").to_owned();
        let live_running = self.world.status(&app).ok().and_then(|s| {
            s.get("runs")?.as_array()?.last()?.get("state")?.as_str().map(|st| st == "running")
        });
        let needs_start = record["state"].as_str() != Some("running") || live_running == Some(false);
        if needs_start && record["state"].as_str() != Some("deleted") {
            let start_res = {
                let _submit = self.submit.lock().unwrap_or_else(|p| p.into_inner());
                self.world.start(&app)
            };
            match start_res {
                Ok(Lifecycle::Done) => {
                    record["state"] = json!("running");
                    record["lifecycleAt"] = json!(now());
                    if let Err(e) = write_json(&grain_file(&self.state, grain), &record).and_then(|_| self.publish_origin(grain, &record)) {
                        return undecided("stateUnavailable", e, &format!("mini apps open --grain {grain}"));
                    }
                    if let Err(error) = self.enroll_routes(grain, &record, None) {
                        return undecided("enrolling", format!("{grain} started, but its routes are not enrolled against the new generation: {error}"), &format!("mini apps renew --grain {grain}"));
                    }
                }
                Ok(Lifecycle::Undecided(detail)) => {
                    record["state"] = json!("starting");
                    let _ = write_json(&grain_file(&self.state, grain), &record);
                    return undecided("starting", detail, &format!("mini apps open --grain {grain}"));
                }
                Err(error) => {
                    return undecided("start", format!("start did not complete: {error}; the lifecycle's own markers decide, nothing is repeated"), &format!("mini apps status --grain {grain}"));
                }
            }
        }
        let Some(route) = record.pointer(&format!("/routes/{member}")).cloned() else {
            return refused("noRoute", format!("{member} has no route on {grain}; the owner shares it with `mini apps share --grain {grain} --to {member}`"));
        };
        let directory = PathBuf::from(route["directory"].as_str().unwrap_or(""));
        let used_path = directory.join("bootstrap.used");
        let token_path = directory.join("bootstrap.token");
        let was_used = used_path.exists();
        if was_used {
            let _ = fs::remove_file(&used_path);
        }
        let token = match crate::fsio::read_bounded(&token_path, 128)
            .ok()
            .map(|bytes| String::from_utf8_lossy(&bytes).trim().to_owned())
            .filter(|t| t.len() == 64 && !(was_used && !directory.join("custodian.json").exists()))
        {
            Some(existing) => existing,
            None => match self.mint_bootstrap_token(grain, member, &mut record, &directory) {
                Ok(fresh) => fresh,
                Err(error) => return undecided("routeUnavailable", format!("the route's bootstrap token is not readable: {error}"), &format!("mini apps open --grain {grain}")),
            },
        };
        performed("open", format!("{grain}: visit {}/__mini/bootstrap and paste the one-time token", record["origin"].as_str().unwrap_or("")), json!({
            "grain":grain,"origin":record["origin"],"bootstrapPath":"/__mini/bootstrap","bootstrapToken":token,
            "identityNotice":IDENTITY_NOTICE}))
    }

    fn mint_bootstrap_token(&self, grain: &str, member: &str, record: &mut Value, directory: &Path) -> Result<String> {
        private_dir(directory)?;
        let token = hex(&crate::fsio::random::<32>()?);
        use sha2::Digest;
        let token_sha = hex(&sha2::Sha256::digest(token.as_bytes()));
        let token_path = directory.join("bootstrap.token");
        fs::write(&token_path, token.as_bytes()).map_err(|e| e.to_string())?;
        fs::set_permissions(&token_path, fs::Permissions::from_mode(0o600)).map_err(|e| e.to_string())?;
        let _ = fs::remove_file(directory.join("bootstrap.used"));
        let custodian_path = directory.join("custodian.json");
        if let Ok(mut custodian) = read_json(&custodian_path) {
            custodian["bootstrapTokenSha256"] = json!(token_sha);
            let _ = write_json(&custodian_path, &custodian);
        }
        if let Some(route) = record.pointer_mut(&format!("/routes/{member}")) {
            route["bootstrapTokenSha256"] = json!(token_sha);
        }
        write_json(&grain_file(&self.state, grain), record)?;
        self.publish_origin(grain, record)?;
        Ok(token)
    }

    /// Bring every route's session enrollment up to the app's serving generation. Returns the
    /// generations renewed per member and the count already current.
    fn enroll_routes(&self, grain: &str, record: &Value, only: Option<&str>) -> Result<(Vec<(String, String)>, usize)> {
        let app = record["app"].as_str().unwrap_or("");
        let (mut renewed, mut current) = (Vec::new(), 0usize);
        let Some(routes) = record.get("routes").and_then(Value::as_object) else { return Ok((renewed, current)) };
        for (member, route) in routes {
            if only.is_some_and(|m| m != member) { continue; }
            let work = self.state.join("work").join(grain).join(format!("enroll-{member}"));
            private_dir(&work)?;
            let enrolled = {
                let _submit = self.submit.lock().unwrap_or_else(|p| p.into_inner());
                self.world.enroll(&work, app, member, &route["enrollment"])?
            };
            match enrolled {
                Enrolled::Current(_) => current += 1,
                Enrolled::Renewed(generation) => renewed.push((member.clone(), generation)),
            }
        }
        Ok((renewed, current))
    }

    /// `renew`: re-enroll the grain's routes against the generation it now serves. A restart moves
    /// the app to a new generation and a session's enrollment names the old one, so a route refuses
    /// until it is renewed; START renews on its own, and this is the explicit form.
    fn renew(&self, grain: &str, record: Value) -> Value {
        if record["state"].as_str() != Some("running") {
            return refused("notRunning", format!("{grain} is {}; only a running grain serves a generation to enroll against: `mini apps start --grain {grain}`", record["state"].as_str().unwrap_or("not running")));
        }
        let enrolled = self.enroll_routes(grain, &record, None);
        if enrolled.is_ok() {
            if let Err(e) = self.publish_origin(grain, &record) {   // renew also repairs a missing front table
                return undecided("stateUnavailable", e, &format!("mini apps renew --grain {grain}"));
            }
        }
        match enrolled {
            Ok((renewed, current)) if renewed.is_empty() => performed("current", format!("{grain}: every route already names the serving generation ({current} checked); nothing was submitted"), json!({"grain":grain,"renewed":[],"current":current})),
            Ok((renewed, current)) => performed("renewed", format!("{grain}: {} route(s) enrolled against the serving generation", renewed.len()), json!({"grain":grain,"renewed":renewed.iter().map(|(m, g)| json!({"member":m,"generation":g})).collect::<Vec<_>>(),"current":current})),
            Err(error) => undecided("enrolling", format!("the enrollment did not complete: {error}; nothing is repeated blindly"), &format!("mini apps renew --grain {grain}")),
        }
    }

    fn lifecycle(&self, grain: &str, mut record: Value, start: bool) -> Value {
        let app = record["app"].as_str().unwrap_or("").to_owned();
        let verb = if start { "start" } else { "stop" };
        let outcome = {
            let _submit = self.submit.lock().unwrap_or_else(|p| p.into_inner());
            if start { self.world.start(&app) } else { self.world.stop(&app) }
        };
        match outcome {
            Ok(Lifecycle::Done) => {
                record["state"] = json!(if start { "running" } else { "stopped" });
                record["lifecycleAt"] = json!(now());
                if let Err(e) = write_json(&grain_file(&self.state, grain), &record) {
                    return undecided("stateUnavailable", e, &format!("mini apps status --grain {grain}"));
                }
                if start {
                    // The restart moved the app to a new serving generation: renew each route's enrollment.
                    if let Err(error) = self.enroll_routes(grain, &record, None) {
                        return undecided("enrolling", format!("{grain} started, but its routes are not enrolled against the new generation: {error}"), &format!("mini apps renew --grain {grain}"));
                    }
                    // The front's table: a start that follows a genesis or a candidate switch is the first thing that
                    // publishes it for a grain whose install happened before (demo-dry 2026-11-06: three running grains
                    // the front answered `no such grain` for).
                    if let Err(e) = self.publish_origin(grain, &record) {
                        return undecided("stateUnavailable", e, &format!("mini apps start --grain {grain}"));
                    }
                }
                performed(record["state"].as_str().unwrap_or(verb), format!("{grain} {verb} completed through Mini"), json!({"grain":grain,"state":record["state"]}))
            }
            Ok(Lifecycle::Undecided(detail)) => {
                record["state"] = json!(if start { "starting" } else { "stopping" });
                let _ = write_json(&grain_file(&self.state, grain), &record);
                undecided(record["state"].as_str().unwrap_or(verb), detail, &format!("mini apps status --grain {grain}"))
            }
            Err(error) => undecided(verb, format!("{verb} did not complete: {error}; the lifecycle's own markers decide, nothing is repeated"), &format!("mini apps status --grain {grain}")),
        }
    }

    fn share(&self, grain: &str, mut record: Value, request: &Value) -> Value {
        let to = request.get("to").and_then(Value::as_str).unwrap_or("");
        if !valid_member(to) {
            return refused("memberRefused", format!("{to:?} is not a member name"));
        }
        if record.pointer(&format!("/routes/{to}")).is_some() {
            return performed("shared", format!("{grain} is already shared with {to}"), json!({"grain":grain,"member":to,"identityNotice":IDENTITY_NOTICE}));
        }
        let app = record["app"].as_str().unwrap_or("").to_owned();
        let work = self.state.join("work").join(grain).join(format!("share-{to}"));
        if let Err(e) = private_dir(&work).and_then(|_| prepare_route_work(&self.state, grain, &record, &work)) {
            return undecided("stateUnavailable", e, &format!("mini apps share --grain {grain} --to {to}"));
        }
        let host = format!("{grain}.{}", self.world.domain());
        match self.bind_route(&work, &app, to, &host) {
            Ok(bound) => {
                record["routes"][to] = route_json(&bound, to);
                if let Err(e) = write_json(&grain_file(&self.state, grain), &record).and_then(|_| self.publish_origin(grain, &record)) {
                    return undecided("stateUnavailable", e, &format!("mini apps share --grain {grain} --to {to}"));
                }
                if record["state"].as_str() == Some("running") {
                    if let Err(error) = self.enroll_routes(grain, &record, Some(to)) {
                        return undecided("enrolling", format!("the route for {to} is bound but not enrolled against the serving generation: {error}"), &format!("mini apps renew --grain {grain}"));
                    }
                }
                performed("shared", format!("{grain} shared with {to}: they open it with `mini apps open --grain {grain}`"), json!({"grain":grain,"member":to,"origin":record["origin"],"identityNotice":IDENTITY_NOTICE}))
            }
            Err(error) => undecided("sharing", format!("the route for {to} is not bound yet: {error}"), &format!("mini apps share --grain {grain} --to {to}")),
        }
    }

    fn export(&self, grain: &str, record: Value) -> Value {
        let app = record["app"].as_str().unwrap_or("").to_owned();
        let out = self.state.join("exports").join(grain);
        // A retained export answers only for the STOP that fenced it: the latest begun run must be
        // stopped at the generation its manifest names. Otherwise it is moved aside and exported afresh.
        let latest_stopped = match self.world.status(&app) {
            Ok(status) => latest_stopped_generation(&status),
            Err(error) => return undecided("statusUnavailable", error, &format!("mini apps export --grain {grain}")),
        };
        if out.join("manifest.sig").exists() {
            let retained = read_json(&out.join("manifest.json")).ok()
                .and_then(|m| m.get("stopGeneration").and_then(Value::as_str).map(str::to_owned));
            if retained.is_some() && retained == latest_stopped {
                return performed("exported", format!("{grain} export retained (generation {})", retained.unwrap_or_default()),
                    json!({"grain":grain,"export":out,"files":["var.ext4","manifest.json","manifest.sig"]}));
            }
            let aside = self.state.join("exports").join(format!("{grain}.stale-{}", retained.as_deref().unwrap_or("unknown")));
            if aside.exists() {
                return refused("exportRefused", format!("the stale export {} must move to {}, which already exists", out.display(), aside.display()));
            }
            if let Err(e) = fs::rename(&out, &aside) {
                return undecided("stateUnavailable", format!("move the stale export aside to {}: {e}", aside.display()), &format!("mini apps export --grain {grain}"));
            }
        }
        match self.world.export(&app, &out) {
            Ok(()) => performed("exported", format!("{grain} exported (the stopped app's /var, its manifest and the Store's completion signature)"), json!({"grain":grain,"export":out,"files":["var.ext4","manifest.json","manifest.sig"]})),
            Err(error) => refused("exportRefused", format!("{error}; export needs the app's latest generation STOPped by a completed STOP")),
        }
    }

    fn delete(&self, grain: &str, mut record: Value) -> Value {
        let app = record["app"].as_str().unwrap_or("").to_owned();
        if record["state"] != "stopped" {
            match self.world.stop(&app) {
                Ok(Lifecycle::Done) => {}
                Ok(Lifecycle::Undecided(detail)) => return undecided("stopping", format!("{detail}; delete continues after the STOP completes"), &format!("mini apps delete --grain {grain}")),
                Err(error) => return undecided("stopping", error, &format!("mini apps delete --grain {grain}")),
            }
        }
        record["state"] = json!("deleted");
        record["deletedAt"] = json!(now());
        record["routes"] = json!({});
        if let Err(e) = write_json(&grain_file(&self.state, grain), &record) {
            return undecided("stateUnavailable", e, &format!("mini apps delete --grain {grain}"));
        }
        let _ = fs::remove_file(self.origin_path(grain));
        performed("deleted", format!("{grain} stopped and its routes withdrawn; its /var volume is retained by the broker (volumeRetained: the broker has no destroy verb yet)"), json!({"grain":grain,"volumeRetained":true}))
    }

    fn identities(&self, grain: &str, record: &Value) -> Value {
        let app = record["app"].as_str().unwrap_or("");
        match self.world.identities(app) {
            Ok(list) => performed("listed", format!("{} identity record(s) held by {grain}", list.len()), json!({"grain":grain,"identities":list,"identityNotice":IDENTITY_NOTICE})),
            Err(error) => undecided("statusUnavailable", error, &format!("mini apps identities --grain {grain}")),
        }
    }

    fn revoke_identity(&self, grain: &str, record: Value, request: &Value) -> Value {
        let token = request.get("token").and_then(Value::as_str).unwrap_or("");
        if !mini_sdk::hex::is_canonical_len(token, 32) {
            return refused("tokenRefused", "a saved-identity token is 64 lowercase hex digits (mini apps identities)");
        }
        let app = record["app"].as_str().unwrap_or("");
        match self.world.revoke_identity(app, token) {
            Ok(()) => performed("revoked", format!("{grain} can no longer restore identity {}…; the record stays, marked", &token[..8]), json!({"grain":grain,"token":token})),
            Err(error) => refused("revokeRefused", error),
        }
    }

    // ------------------------------------------------------------- install

    /// `install` and `retry`: the request is retained (`requests/<id>.json`) and run on its own
    /// thread; the handler answers the run's outcome if it comes within the grace, else
    /// `pending` with the exact retry. A run in flight is never started twice, and a decided
    /// outcome is answered as retained, never run again.
    fn install(self: &Arc<Self>, member: &str, request: &Value) -> Value {
        let Some(id) = request.get("requestId").and_then(Value::as_str) else {
            return refused("requestRefused", "install needs a 32-hex requestId");
        };
        if !mini_sdk::hex::is_canonical_len(id, 16) {
            return refused("requestRefused", "requestId is not 32 hex digits");
        }
        let file = request_file(&self.state, id);
        let (notify, outcome) = mpsc::channel();
        let app_id = {
            let mut installs = self.installs.lock().unwrap_or_else(|p| p.into_inner());
            let existing = read_json(&file).ok();
            if existing.as_ref().is_some_and(|r| r["member"] != member) {
                return refused("notOwner", "this request id belongs to another member");
            }
            if installs.contains_key(id) {
                return pending(id, existing.as_ref().unwrap_or(request));
            }
            if let Some(decided) = existing.as_ref().map(|r| &r["lastOutcome"]).filter(|o| o["decided"] == true) {
                return decided.clone();
            }
            if existing.is_none() && request["verb"] == "retry" {
                return refused("unknownRequest", format!("no request {id} is retained for {member}; the first install was never received"));
            }
            let mine = installs.values().filter(|m| m.as_str() == member).count();
            if mine >= MEMBER_INSTALLS || installs.len() >= ALL_INSTALLS {
                let detail = format!("{mine} of your installs are running (at most {MEMBER_INSTALLS}), {} in all (at most {ALL_INSTALLS}); nothing was started", installs.len());
                return match &existing {
                    Some(retained) => undecided("installsBusy", detail, &install_retry(retained, id)),
                    None => refused("installsBusy", format!("{detail}; install again once one has finished")),
                };
            }
            let mut retained = match existing {
                Some(retained) => retained,
                None => match self.admit(member, request) {
                    Ok(retained) => retained,
                    Err(refusal) => return refusal,
                },
            };
            retained["run"] = json!({"state":"running","since":now()});
            if let Err(e) = write_json(&file, &retained) {
                return undecided("stateUnavailable", e, &install_retry(&retained, id));
            }
            let app_id = retained["appId"].clone();
            installs.insert(id.to_owned(), member.to_owned());
            if let Err(e) = self.spawn_run(id.to_owned(), retained, Some(notify)) {
                installs.remove(id);
                return undecided("workerBusy", format!("the install could not start: {e}"), &install_retry(request, id));
            }
            app_id
        };
        match outcome.recv_timeout(self.install_grace) {
            Ok(outcome) => outcome,
            Err(_) => pending(id, &json!({"appId":app_id,"run":{"since":now()}})),
        }
    }

    /// One install run on its own thread: `advance`, then the outcome retained beside the
    /// request and the run marked done. The in-flight entry is removed however the run ends.
    fn spawn_run(self: &Arc<Self>, id: String, mut retained: Value, notify: Option<mpsc::Sender<Value>>) -> std::io::Result<()> {
        struct InFlight(Arc<Worker>, String);
        impl Drop for InFlight {
            fn drop(&mut self) {
                self.0.installs.lock().unwrap_or_else(|p| p.into_inner()).remove(&self.1);
            }
        }
        let flight = InFlight(self.clone(), id.clone());
        std::thread::Builder::new().name(format!("mini-apps-install-{}", &id[..8])).spawn(move || {
            let worker = flight.0.clone();
            let outcome = worker.advance(&mut retained);
            retained["lastOutcome"] = outcome.clone();
            retained["run"] = json!({"state":"done","at":now()});
            let _ = write_json(&request_file(&worker.state, &id), &retained);
            drop(flight);
            if let Some(notify) = notify {
                let _ = notify.send(outcome);
            }
        }).map(|_| ())
    }

    /// After a restart: every request whose run the previous process did not finish
    /// (`run.state` still `running`) is resumed by the same `advance` an exact retry runs.
    pub(crate) fn resume(self: &Arc<Self>) -> Vec<String> {
        let mut resumed = Vec::new();
        let Ok(entries) = fs::read_dir(self.state.join("requests")) else { return resumed };
        for entry in entries.flatten() {
            let path = entry.path();
            if path.extension().and_then(|e| e.to_str()) != Some("json") {
                continue;
            }
            let Ok(retained) = read_json(&path) else { continue };
            if retained.pointer("/run/state").and_then(Value::as_str) != Some("running") {
                continue;
            }
            let (Some(id), Some(member)) = (retained["requestId"].as_str().map(str::to_owned), retained["member"].as_str().map(str::to_owned)) else { continue };
            if !mini_sdk::hex::is_canonical_len(&id, 16) || path != request_file(&self.state, &id) {
                continue;
            }
            let mut installs = self.installs.lock().unwrap_or_else(|p| p.into_inner());
            if installs.contains_key(&id) {
                continue;
            }
            installs.insert(id.clone(), member);
            if self.spawn_run(id.clone(), retained, None).is_ok() {
                resumed.push(id);
            } else {
                installs.remove(&id);
            }
        }
        resumed.sort();
        resumed
    }

    /// The request as retained: the member's choice and the three documents.
    fn admit(&self, member: &str, request: &Value) -> std::result::Result<Value, Value> {
        let app_id = text(request, "appId").map_err(|e| refused("requestRefused", e))?;
        let package_id = text(request, "packageId").map_err(|e| refused("requestRefused", e))?;
        if !valid_app_id(app_id) || !valid_package_id(package_id) {
            return Err(refused("unknownApp", "appId or packageId malformed"));
        }
        let class = request.get("class").and_then(Value::as_str).unwrap_or("auto");
        if !valid_class(class) {
            return Err(refused("classRefused", "class is S, M, L or auto"));
        }
        let mut docs = Map::new();
        for key in ["birthSource", "birthReceipt", "delegation", "shareDelegation"] {
            let Some(doc) = request.get(key).filter(|d| d.is_object()) else {
                return Err(refused("birthRequired", format!("the request carries no {key} document; the install is a member turn (docs/APP-MARKET-2026-10-27.md §3)")));
            };
            if serde_json::to_vec(doc).map(|b| b.len()).unwrap_or(usize::MAX) > MAX_DOCUMENT {
                return Err(refused("requestRefused", format!("{key} exceeds 64 KiB")));
            }
            docs.insert(key.into(), doc.clone());
        }
        if docs["delegation"].get("protocol").and_then(Value::as_str) != Some("mini-spk-grain-lifecycle-delegation-v1") {
            return Err(refused("delegationRefused", "the hosting delegation is not mini-spk-grain-lifecycle-delegation-v1 (mini shell: app delegate-lifecycle)"));
        }
        if docs["birthReceipt"].get("type").and_then(Value::as_str) != Some("confirmed") {
            return Err(refused("birthRequired", "the application birth receipt is not confirmed"));
        }
        let carry = match request.get("carry").filter(|c| !c.is_null()) {
            None => Value::Null,
            Some(grain) => self.carried(member, app_id, grain.as_str().unwrap_or(""), text(request, "requestId").unwrap_or(""))?,
        };
        let class = carry.get("class").and_then(Value::as_str).unwrap_or(class);
        Ok(json!({
            "protocol":WORKER_PROTOCOL,"requestId":text(request,"requestId").unwrap_or(""),"member":member,
            "appId":app_id,"packageId":package_id,"class":class,
            "indexName":request.get("indexName").cloned().unwrap_or(Value::Null),
            "indexVersion":request.get("indexVersion").cloned().unwrap_or(Value::Null),
            "documents":docs,"phases":{},"receivedAt":now(),"carry":carry,
        }))
    }

    /// The carried grain `grain` (`carried/<grain>/`, placed by the operator's migration:
    /// `carry.json` and the export it names) for `member`'s install of `app_id`. Only its owner
    /// carries it, only into the same application, at its own class, and into one new grain: the
    /// first request claims it (`claimed`) and any other request is refused.
    fn carried(&self, member: &str, app_id: &str, grain: &str, request_id: &str) -> std::result::Result<Value, Value> {
        if !crate::apps::valid_grain(grain) {
            return Err(refused("carryRefused", format!("{grain:?} is not a grain id of the form a<app>")));
        }
        let dir = self.state.join("carried").join(grain);
        let record = read_json(&dir.join("carry.json"))
            .map_err(|_| refused("carryRefused", format!("no grain {grain} was carried from the previous world")))?;
        let field = |k: &str| record.get(k).and_then(Value::as_str).unwrap_or("");
        if field("protocol") != "mini-apps-carried-grain-v1" || field("grain") != grain {
            return Err(refused("carryRefused", format!("the carry record of {grain} is not mini-apps-carried-grain-v1")));
        }
        if field("owner") != member {
            return Err(refused("notOwner", format!("{grain} was carried for its owner, not for {member}")));
        }
        if field("appId") != app_id {
            return Err(refused("carryRefused", format!("{grain} is a grain of {}, not of {app_id}", field("appId"))));
        }
        if !valid_class(field("class")) || field("class") == "auto" || !mini_sdk::hex::is_canonical_len(field("exporterKey"), 32) {
            return Err(refused("carryRefused", format!("the carry record of {grain} names no class or exporter key")));
        }
        let manifest = read_json(&dir.join("export").join("manifest.json"))
            .map_err(|_| refused("carryRefused", format!("the export of {grain} is missing")))?;
        let image = manifest.pointer("/image/sha256").and_then(Value::as_str).unwrap_or("");
        if !mini_sdk::hex::is_canonical_len(image, 32) {
            return Err(refused("carryRefused", format!("the export of {grain} names no image digest")));
        }
        let claimed = dir.join("claimed");
        match fs::read_to_string(&claimed) {
            Ok(by) if by.trim() != request_id => {
                return Err(refused("carryClaimed", format!("{grain} is already carried by request {}", by.trim())));
            }
            Ok(_) => {}
            Err(_) => {
                // A member's install of an application it already holds reuses that application's birth,
                // which spk-host refuses as a changed instance record: a carry lands only in a new grain,
                // so it is refused here, before the claim, rather than by an install that cannot complete.
                if let Some(held) = self.held_grain(member, app_id) {
                    return Err(refused("carryRefused", format!("{member} already holds {held}, a grain of {app_id}; {grain} carries only into an owner who holds none of that application")));
                }
                fs::write(&claimed, request_id).map_err(|e| undecided("stateUnavailable", e.to_string(), &format!("mini apps install --carry {grain}")))?
            }
        }
        Ok(json!({"grain":grain,"class":field("class"),"exporterKey":field("exporterKey"),"imageSha256":image,
            "export":dir.join("export")}))
    }

    /// A grain of `app_id` that `member` owns (in any state: a deleted grain keeps its instance record).
    fn held_grain(&self, member: &str, app_id: &str) -> Option<String> {
        let entries = fs::read_dir(self.state.join("grains")).ok()?;
        entries.flatten().filter_map(|entry| read_json(&entry.path()).ok()).find_map(|record| {
            (record.get("owner").and_then(Value::as_str) == Some(member) && record.get("appId").and_then(Value::as_str) == Some(app_id))
                .then(|| record.get("grain").and_then(Value::as_str).unwrap_or("?").to_owned())
        })
    }

    /// Run the next phases of a retained request; each retains its result
    /// before the next starts, so a retry resumes where the last one stopped.
    fn advance(&self, retained: &mut Value) -> Value {
        let id = retained["requestId"].as_str().unwrap_or("").to_owned();
        let member = retained["member"].as_str().unwrap_or("").to_owned();
        let package_id = retained["packageId"].as_str().unwrap_or("").to_owned();
        let retry = install_retry(retained, &id);
        let work = self.state.join("work").join(&id);
        if let Err(e) = private_dir(&work) {
            return undecided("stateUnavailable", e, &retry);
        }
        // Phase 1: the package, from the quarantine (or wanted).
        let spk = match self.world.package(&package_id) {
            Err(e) => return undecided("fetching", e, &retry),
            Ok(None) => {
                if let Err(e) = self.world.want(&package_id) {
                    return undecided("fetching", e, &retry);
                }
                retained["phases"]["package"] = json!({"state":"wanted","at":now()});
                return undecided("fetching", format!("package {package_id} is not in the quarantine yet; mini-market fetches it"), &retry);
            }
            Ok(Some((path, sha, bytes))) => {
                if !sha.starts_with(&package_id) {
                    return refused("packageIdMismatch", format!("quarantine copy hashes to {sha}"));
                }
                retained["phases"]["package"] = json!({"state":"present","path":path,"sha256":sha,"bytes":bytes});
                path
            }
        };
        // Phase 2: install through spk-host (its own one-shot markers make a resume exact).
        let installed = match retained["phases"]["install"].get("app").and_then(Value::as_str) {
            Some(app) => Installed {
                app: app.to_owned(),
                raw_sha256: retained["phases"]["install"]["rawSha256"].as_str().unwrap_or("").to_owned(),
                signed_app_id: retained["phases"]["install"]["signedAppId"].as_str().unwrap_or("").to_owned(),
                app_version: retained["phases"]["install"]["appVersion"].as_str().unwrap_or("").to_owned(),
            },
            None => {
                let docs = &retained["documents"];
                let source = work.join("birth-source.json");
                let receipt = work.join("birth-outcome.json");
                let delegation = work.join("delegation.json");
                let share = work.join("share-delegation.json");
                for (path, doc) in [(&source, &docs["birthSource"]), (&receipt, &docs["birthReceipt"]), (&delegation, &docs["delegation"]), (&share, &docs["shareDelegation"])] {
                    if !path.exists() {
                        if let Err(e) = write_json(path, doc) {
                            return undecided("stateUnavailable", e, &retry);
                        }
                    }
                }
                let carry = retained["carry"].clone();
                let class: String = match retained["class"].as_str().unwrap_or("auto") {
                    "auto" => {
                        let bytes = retained["phases"]["package"]["bytes"].as_u64().unwrap_or(0);
                        if bytes < 64 * 1024 * 1024 { "S".into() } else { "M".into() }
                    }
                    c => c.to_owned(),
                };
                retained["class"] = json!(class);
                let _ = write_json(&request_file(&self.state, &id), retained);
                let install_res = {
                    let _submit = self.submit.lock().unwrap_or_else(|p| p.into_inner());
                    let export = carry.get("export").and_then(Value::as_str).map(PathBuf::from);
                    let key = carry.get("exporterKey").and_then(Value::as_str).unwrap_or("");
                    self.world.install(&work, &source, &receipt, &spk, &class, &delegation, export.as_deref().map(|e| (e, key)))
                };
                match install_res {
                    Ok(installed) => {
                        if installed.signed_app_id != retained["appId"] {
                            let _ = self.world.verdict(&package_id, &json!({"verdict":"refused","reason":"appIdMismatch","signedAppId":installed.signed_app_id}));
                            return refused("appIdMismatch", format!("the signed appId {} differs from the catalogue's", installed.signed_app_id));
                        }
                        retained["phases"]["install"] = json!({"app":installed.app,"rawSha256":installed.raw_sha256,"signedAppId":installed.signed_app_id,"appVersion":installed.app_version,"at":now()});
                        let _ = self.world.verdict(&package_id, &json!({"verdict":"verified","signedAppId":installed.signed_app_id,"rawSha256":installed.raw_sha256,"running":1}));
                        installed
                    }
                    Err(error) => {
                        let non_timing: String = error
                            .lines()
                            .filter(|l| !l.contains("tool-timing") && !l.contains("op-timing"))
                            .collect::<Vec<_>>()
                            .join("\n");
                        let name = if non_timing.contains("unsupported physical profile") || non_timing.contains("apiPath") {
                            "unsupportedBridge"
                        } else if non_timing.contains("signature") || non_timing.contains("Signature") {
                            "unverifiedSignature"
                        } else if non_timing.contains("UNRESOLVED") || non_timing.contains("uncertain") || non_timing.contains("currentWorldRoot") || non_timing.contains("pinned executable refused") {
                            return undecided("installing", error, &retry);
                        } else if non_timing.contains("derived file differs from retained instance record") {
                            // This member's birth of the application already names an instance (an install of
                            // an application it holds): a fault of the request, never of the package, so the
                            // package's verdict is left as it is.
                            return refused("instanceHeld", format!("{member} already holds an instance of this application's birth; nothing was installed: {error}"));
                        } else {
                            "installRefused"
                        };
                        let _ = self.world.verdict(&package_id, &json!({"verdict":"refused","reason":format!("{name}: {error}")}));
                        return refused(name, error);
                    }
                }
            }
        };
        let grain = format!("a{}", installed.app);
        let origin = format!("https://{grain}.{}", self.world.domain());
        // The grain's record is the grain lock's: phases 3 and 4 wait for a member verb on it to end.
        let grain_lock = self.grain_lock(&grain);
        let _grain = grain_lock.lock().unwrap_or_else(|p| p.into_inner());
        // Phase 3: the owner's route on the grain's own origin. `spk-host grain start` refuses an
        // application that has no entrance bound (grain.rs), so the route comes before START; its
        // enrollment against the serving generation is after it.
        let mut record = self.grain_record(&grain).ok().flatten().unwrap_or_else(|| json!({
            "protocol":"mini-apps-grain-v1","grain":grain,"app":installed.app,"owner":member,"appId":retained["appId"],
            "packageId":package_id,"rawSha256":installed.raw_sha256,"appVersion":installed.app_version,
            "indexName":retained["indexName"],"class":retained["class"],"origin":origin,"requestId":id,
            "state":"running","routes":{},"createdAt":now(),
            "carriedFrom":retained["carry"].get("grain").cloned().unwrap_or(Value::Null),
            "carriedImageSha256":retained["carry"].get("imageSha256").cloned().unwrap_or(Value::Null),
        }));
        if record.pointer(&format!("/routes/{member}")).is_none() {
            if let Err(e) = prepare_route_work(&self.state, &grain, &record, &work) {
                return undecided("stateUnavailable", e, &retry);
            }
            let host = format!("{grain}.{}", self.world.domain());
            match self.bind_route(&work, &installed.app, &member, &host) {
                Ok(bound) => {
                    record["routes"][member.as_str()] = route_json(&bound, &member);
                    if let Err(e) = write_json(&grain_file(&self.state, &grain), &record) {
                        return undecided("stateUnavailable", e, &retry);
                    }
                }
                Err(error) => {
                    let _ = write_json(&grain_file(&self.state, &grain), &record);
                    return undecided("routing", format!("the owner's route is not bound yet: {error}"), &retry);
                }
            }
        }
        // Phase 4: START.
        if retained["phases"]["start"].get("state") != Some(&json!("running")) {
            let start_res = {
                let _submit = self.submit.lock().unwrap_or_else(|p| p.into_inner());
                self.world.start(&installed.app)
            };
            match start_res {
                Ok(Lifecycle::Done) => retained["phases"]["start"] = json!({"state":"running","at":now()}),
                Ok(Lifecycle::Undecided(detail)) => {
                    retained["phases"]["start"] = json!({"state":"starting","at":now()});
                    return undecided("starting", detail, &retry);
                }
                Err(error) => return undecided("starting", format!("START did not complete: {error}; nothing is repeated"), &retry),
            }
        }
        record["state"] = json!("running");
        if let Err(e) = write_json(&grain_file(&self.state, &grain), &record).and_then(|_| self.publish_origin(&grain, &record)) {
            return undecided("stateUnavailable", e, &retry);
        }
        if let Err(error) = self.enroll_routes(&grain, &record, Some(&member)) {
            return undecided("enrolling", format!("the owner's route is bound but not enrolled against the serving generation: {error}"), &retry);
        }
        retained["phases"]["route"] = json!({"state":"bound","at":now()});
        retained["state"] = json!("running");
        performed("running", format!("{} installed as {grain}; open it with `mini apps open --grain {grain}`", retained["indexName"].as_str().unwrap_or("the app")), json!({
            "requestId":id,"grain":grain,"origin":origin,"class":retained["class"],"rawSha256":installed.raw_sha256,
            "signedAppId":installed.signed_app_id,"appVersion":installed.app_version,"identityNotice":IDENTITY_NOTICE,
        }))
    }

    fn origin_path(&self, grain: &str) -> PathBuf {
        self.state.join("origins").join(format!("{grain}.json"))
    }

    /// The front's table for this grain: the routes, their token hashes and
    /// the connector they are reached through. Token hashes are not secrets.
    fn publish_origin(&self, grain: &str, record: &Value) -> Result<()> {
        let dir = self.state.join("origins");
        if !dir.is_dir() {
            fs::DirBuilder::new().mode(0o755).create(&dir).map_err(|e| e.to_string())?;
        }
        let routes: Vec<Value> = record.get("routes").and_then(Value::as_object).map(|r| r.values().cloned().map(|v| json!({
            "member":v["member"],"socket":v["socket"],"browserTokenSha256":v["browserTokenSha256"],
            "bootstrapTokenSha256":v["bootstrapTokenSha256"],"apiTokenSha256":v["apiTokenSha256"],
        })).collect()).unwrap_or_default();
        let table = json!({"protocol":"mini-apps-origin-v1","grain":grain,"connector":self.state.join("edge.sock"),"routes":routes});
        let path = self.origin_path(grain);
        let bytes = serde_json::to_vec_pretty(&table).map_err(|e| e.to_string())?;
        let temp = path.with_extension("json.new");
        fs::write(&temp, &bytes).map_err(|e| e.to_string())?;
        fs::set_permissions(&temp, fs::Permissions::from_mode(0o644)).map_err(|e| e.to_string())?;
        fs::rename(&temp, &path).map_err(|e| e.to_string())
    }

    /// The edge connector: connect to a route's custodian socket for the front.
    fn connect_route(&self, grain: &str, member: &str) -> std::result::Result<UnixStream, Value> {
        if !valid_grain(grain) || !valid_member(member) {
            return Err(refused("routeRefused", "grain or member malformed"));
        }
        let Some(record) = self.grain_record(grain).map_err(|e| refused("stateUnavailable", e))? else {
            return Err(refused("unknownGrain", grain.to_owned()));
        };
        let Some(route) = record.pointer(&format!("/routes/{member}")) else {
            return Err(refused("noRoute", format!("{member} has no route on {grain}")));
        };
        let socket = PathBuf::from(route["socket"].as_str().unwrap_or(""));
        UnixStream::connect(&socket).map_err(|e| refused("routeUnavailable", format!("{}: {e}", socket.display())))
    }

    /// The edge connector's publishing verb: the grain's `www.sock`, which the
    /// resident binds in the app's state directory, the grandparent of every
    /// route directory (`apps/<app>/routes/<route>`).
    fn connect_www(&self, grain: &str) -> std::result::Result<UnixStream, Value> {
        if !valid_grain(grain) {
            return Err(refused("routeRefused", "grain malformed"));
        }
        let Some(record) = self.grain_record(grain).map_err(|e| refused("stateUnavailable", e))? else {
            return Err(refused("unknownGrain", grain.to_owned()));
        };
        let route = record.get("routes").and_then(Value::as_object).and_then(|routes| routes.values().next())
            .ok_or_else(|| refused("noRoute", format!("{grain} has no route yet")))?;
        let route_dir = route.get("directory").and_then(Value::as_str).filter(|s| !s.trim().is_empty()).map(PathBuf::from)
            .or_else(|| route.get("socket").and_then(Value::as_str).and_then(|s| Path::new(s).parent().map(Path::to_path_buf)))
            .ok_or_else(|| refused("noRoute", format!("{grain} has no route yet")))?;
        let routes_dir = route_dir.parent()
            .filter(|dir| dir.file_name().is_some_and(|name| name == "routes"))
            .ok_or_else(|| refused("stateUnavailable", format!("{} is not under a routes directory", route_dir.display())))?;
        let www = routes_dir.parent().ok_or_else(|| refused("stateUnavailable", "routes directory has no app directory"))?.join("www.sock");
        UnixStream::connect(&www).map_err(|e| refused("grainStopped", format!("{}: {e}", www.display())))
    }
}

/// Copy or materialize `birth-source.json`, `delegation.json`, and `share-delegation.json`
/// from the grain's install work directory or retained request into `work` before `route(...)`.
pub(crate) fn prepare_route_work(state: &Path, grain: &str, record: &Value, work: &Path) -> Result<()> {
    let request_id = record.get("requestId").and_then(Value::as_str).unwrap_or("");
    let retained_docs = (!request_id.is_empty())
        .then(|| read_json(&request_file(state, request_id)).ok())
        .flatten()
        .and_then(|r| r.get("documents").cloned());
    for (filename, doc_key) in [
        ("birth-source.json", "birthSource"),
        ("delegation.json", "delegation"),
        ("share-delegation.json", "shareDelegation"),
    ] {
        let dst = work.join(filename);
        if dst.exists() {
            continue;
        }
        let mut candidates = Vec::new();
        if !request_id.is_empty() {
            candidates.push(state.join("work").join(request_id).join(filename));
        }
        candidates.push(state.join("work").join(grain).join(filename));
        if let Some(app) = record.get("app").and_then(Value::as_str).filter(|a| !a.is_empty()) {
            candidates.push(state.join("work").join(app).join(filename));
        }
        if let Some(src) = candidates.into_iter().find(|p| p.exists()) {
            let doc = read_json(&src)?;
            write_json(&dst, &doc)?;
            continue;
        }
        if let Some(doc) = retained_docs.as_ref().and_then(|d| d.get(doc_key)).filter(|d| d.is_object()) {
            write_json(&dst, doc)?;
        }
    }
    Ok(())
}

/// Load or persist the `(base, session, ticket, cap)` tuple for one route bind in `{work}/{label}-nonce.json`
/// so retrying a partial share reuses the exact same `session` and `ticket` as `{label}-session-attempt`.
pub(crate) fn route_nonce(work: &Path, label: &str, alloc: impl FnOnce() -> Result<u64>) -> Result<(u64, u64, u64, u64)> {
    let nonce_path = work.join(format!("{label}-nonce.json"));
    if nonce_path.exists() {
        let saved = read_json(&nonce_path)?;
        let base = saved
            .get("base")
            .and_then(|v| v.as_u64().or_else(|| v.as_str()?.parse().ok()))
            .ok_or("corrupt route nonce")?;
        let (session, ticket) = share_ids(base)?;
        let cap = 300_000 + (base % 100_000) * 10;
        return Ok((base, session, ticket, cap));
    }
    let recovered = read_json(&work.join(format!("{label}-session-source.json")))
        .ok()
        .and_then(|src| src.get("nonce")?.as_str()?.parse::<u64>().ok())
        .and_then(|n| n.checked_sub(100));
    let base = match recovered {
        Some(base) => {
            let (_, expected_ticket) = share_ids(base)?;
            let ticket_req = work.join(format!("{label}-ticket")).join("request.json");
            let ticket_matches = !ticket_req.exists()
                || read_json(&ticket_req)
                    .ok()
                    .and_then(|r| r.pointer("/spec/ticket/resource")?.as_str().map(|s| s == expected_ticket.to_string()))
                    .unwrap_or(false);
            if ticket_matches {
                base
            } else {
                for suffix in ["session-attempt", "session-author", "ticket"] {
                    let _ = fs::remove_dir_all(work.join(format!("{label}-{suffix}")));
                }
                let _ = fs::remove_file(work.join(format!("{label}-session-source.json")));
                alloc()?
            }
        }
        None => alloc()?,
    };
    let (session, ticket) = share_ids(base)?;
    let cap = 300_000 + (base % 100_000) * 10;
    write_json(
        &nonce_path,
        &json!({
            "base": base,
            "session": session.to_string(),
            "ticket": ticket.to_string(),
            "cap": cap.to_string(),
        }),
    )?;
    Ok((base, session, ticket, cap))
}

/// The owner's role basis for one grain: the world's basis (`allAccess` on the
/// box) when the signed bridge declares no roles, role 0 when it does, as the
/// journey's `basis()` picks it. A bridge that declares roles (the oracle: role 0
/// `Researcher`, permission `query`) refuses a session whose permissions are not
/// exactly its declared one, so `allAccess` would be refused at enrolment.
fn role_basis(world: &Value, schema: &Value) -> Value {
    let declares_roles = schema.get("roles").and_then(Value::as_array).is_some_and(|r| !r.is_empty());
    if declares_roles && world.get("type").and_then(Value::as_str) == Some("allAccess") {
        json!({"type":"role","id":"0"})
    } else {
        world.clone()
    }
}

fn route_json(bound: &RouteBound, member: &str) -> Value {
    json!({"member":member,"directory":bound.directory,"socket":bound.socket,
        "browserTokenSha256":bound.browser_token_sha256,"bootstrapTokenSha256":bound.bootstrap_token_sha256,
        "apiTokenSha256":bound.api_token_sha256,"enrollment":bound.enrollment,"boundAt":now()})
}

// ---------------------------------------------------------- the sockets

/// The peer's uid and gid.
fn peer(stream: &UnixStream) -> Result<(u32, u32)> {
    #[cfg(target_os = "linux")]
    {
        let mut credential = unsafe { std::mem::zeroed::<libc::ucred>() };
        let mut length = std::mem::size_of::<libc::ucred>() as libc::socklen_t;
        let rc = unsafe {
            libc::getsockopt(stream.as_raw_fd(), libc::SOL_SOCKET, libc::SO_PEERCRED, (&mut credential as *mut libc::ucred).cast(), &mut length)
        };
        if rc != 0 {
            return Err("SO_PEERCRED unavailable".into());
        }
        Ok((credential.uid, credential.gid))
    }
    #[cfg(not(target_os = "linux"))]
    {
        let mut uid: libc::uid_t = 0;
        let mut gid: libc::gid_t = 0;
        if unsafe { libc::getpeereid(stream.as_raw_fd(), &mut uid, &mut gid) } != 0 {
            return Err("getpeereid unavailable".into());
        }
        Ok((uid, gid))
    }
}

/// The member name of a uid: the account `mini-s-NAME`.
fn member_of_uid(uid: u32) -> Option<String> {
    let entry = unsafe { libc::getpwuid(uid) };
    if entry.is_null() {
        return None;
    }
    let name = unsafe { std::ffi::CStr::from_ptr((*entry).pw_name) }.to_str().ok()?;
    name.strip_prefix(MEMBER_PREFIX).map(str::to_owned)
}

fn read_line(stream: &mut UnixStream) -> Result<Value> {
    stream.set_read_timeout(Some(Duration::from_secs(10))).map_err(|e| e.to_string())?;
    let mut reader = BufReader::new(stream.try_clone().map_err(|e| e.to_string())?);
    let mut line = Vec::new();
    reader.by_ref().take(MAX_LINE as u64 + 1).read_until(b'\n', &mut line).map_err(|e| e.to_string())?;
    if line.len() > MAX_LINE {
        return Err("request exceeds 256 KiB".into());
    }
    serde_json::from_slice(&line).map_err(|e| format!("request is not JSON: {e}"))
}

fn write_line(stream: &mut UnixStream, value: &Value) {
    let mut bytes = serde_json::to_vec(value).unwrap_or_default();
    bytes.push(b'\n');
    let _ = stream.set_write_timeout(Some(Duration::from_secs(10)));
    let _ = stream.write_all(&bytes);
}

/// One JSON line plus one file descriptor, `SCM_RIGHTS`.
pub(crate) fn send_with_fd(stream: &UnixStream, value: &Value, fd: std::os::unix::io::RawFd) -> Result<()> {
    let mut bytes = serde_json::to_vec(value).map_err(|e| e.to_string())?;
    bytes.push(b'\n');
    let mut iov = libc::iovec { iov_base: bytes.as_mut_ptr().cast(), iov_len: bytes.len() };
    let space = unsafe { libc::CMSG_SPACE(std::mem::size_of::<libc::c_int>() as u32) } as usize;
    let mut control = vec![0_u8; space];
    let mut msg: libc::msghdr = unsafe { std::mem::zeroed() };
    msg.msg_iov = &mut iov;
    msg.msg_iovlen = 1;
    msg.msg_control = control.as_mut_ptr().cast();
    msg.msg_controllen = space as _;
    unsafe {
        let header = libc::CMSG_FIRSTHDR(&msg);
        (*header).cmsg_level = libc::SOL_SOCKET;
        (*header).cmsg_type = libc::SCM_RIGHTS;
        (*header).cmsg_len = libc::CMSG_LEN(std::mem::size_of::<libc::c_int>() as u32) as _;
        std::ptr::write_unaligned(libc::CMSG_DATA(header).cast::<libc::c_int>(), fd);
    }
    let sent = unsafe { libc::sendmsg(stream.as_raw_fd(), &msg, 0) };
    if sent < 0 {
        return Err(format!("sendmsg: {}", std::io::Error::last_os_error()));
    }
    Ok(())
}

/// The front's side: one JSON line and, with it, the connected socket.
pub(crate) fn receive_with_fd(stream: &UnixStream) -> Result<(Value, Option<UnixStream>)> {
    let mut bytes = vec![0_u8; 16 * 1024];
    let mut iov = libc::iovec { iov_base: bytes.as_mut_ptr().cast(), iov_len: bytes.len() };
    let space = unsafe { libc::CMSG_SPACE(std::mem::size_of::<libc::c_int>() as u32) } as usize;
    let mut control = vec![0_u8; space];
    let mut msg: libc::msghdr = unsafe { std::mem::zeroed() };
    msg.msg_iov = &mut iov;
    msg.msg_iovlen = 1;
    msg.msg_control = control.as_mut_ptr().cast();
    msg.msg_controllen = space as _;
    let received = unsafe { libc::recvmsg(stream.as_raw_fd(), &mut msg, 0) };
    if received < 0 {
        return Err(format!("recvmsg: {}", std::io::Error::last_os_error()));
    }
    let value: Value = serde_json::from_slice(&bytes[..received as usize]).map_err(|e| format!("connector reply is not JSON: {e}"))?;
    let mut fd = None;
    unsafe {
        let header = libc::CMSG_FIRSTHDR(&msg);
        if !header.is_null() && (*header).cmsg_level == libc::SOL_SOCKET && (*header).cmsg_type == libc::SCM_RIGHTS {
            let raw = std::ptr::read_unaligned(libc::CMSG_DATA(header).cast::<libc::c_int>());
            if raw >= 0 {
                fd = Some(UnixStream::from_raw_fd(raw));
            }
        }
    }
    Ok((value, fd))
}

/// The gid of a group name, from the passwd database.
fn group_id(name: &str) -> Result<u32> {
    let c = std::ffi::CString::new(name).map_err(|_| "group name".to_owned())?;
    let entry = unsafe { libc::getgrnam(c.as_ptr()) };
    if entry.is_null() {
        return Err(format!("groupUnavailable: no group {name:?} on this host"));
    }
    Ok(unsafe { (*entry).gr_gid })
}

/// Bind a socket with its mode and, when a group is named, that group (the
/// unit's SupplementaryGroups makes the chgrp possible; a group this process
/// cannot resolve refuses the start, never a silently private socket).
fn bind(path: &Path, mode: u32, group: Option<&str>) -> Result<UnixListener> {
    let _ = fs::remove_file(path);
    let listener = UnixListener::bind(path).map_err(|e| format!("cannot bind {}: {e}", path.display()))?;
    if let Some(group) = group {
        let gid = group_id(group)?;
        std::os::unix::fs::chown(path, None, Some(gid)).map_err(|e| format!("cannot give {} to group {group}: {e} (the unit needs SupplementaryGroups={group})", path.display()))?;
    }
    fs::set_permissions(path, fs::Permissions::from_mode(mode)).map_err(|e| e.to_string())?;
    Ok(listener)
}

/// The peer receives the reply unchanged; the worker's journal (the operator's log) keeps every
/// refusal by name and every undecided outcome, with who asked and for what.
fn log_unsettled(socket: &str, member: &str, request: Option<&Value>, reply: &Value) {
    let decided = reply.get("decided").and_then(Value::as_bool).unwrap_or(true);
    let Some(name) = reply.get("refused").and_then(Value::as_str).or(if decided { None } else { Some("undecided") }) else {
        return;
    };
    let field = |key: &str| request.and_then(|r| r.get(key)).and_then(Value::as_str).unwrap_or("-");
    let (verb, grain) = (field("verb"), field("grain"));
    let detail = reply.get("detail").and_then(Value::as_str).unwrap_or("");
    eprintln!("mini apps-worker: {socket} {member} {verb} {grain}: {name}: {detail}");
}

/// Serve both sockets until the process ends.
pub(crate) fn serve(worker: Arc<Worker>, members: UnixListener, edge: UnixListener, dev_member: Option<String>) -> Result<()> {
    let edge_worker = worker.clone();
    std::thread::Builder::new().name("mini-apps-edge".into()).spawn(move || {
        for stream in edge.incoming() {
            let Ok(mut stream) = stream else { continue };
            let request = match read_line(&mut stream) {
                Ok(request) => request,
                Err(e) => {
                    let reply = refused("requestRefused", e);
                    log_unsettled("edge", "-", None, &reply);
                    write_line(&mut stream, &reply);
                    continue;
                }
            };
            let grain = request.get("grain").and_then(Value::as_str).unwrap_or("");
            let member = request.get("route").and_then(Value::as_str).unwrap_or("");
            let connected = match request.get("verb").and_then(Value::as_str) {
                Some("connect") => edge_worker.connect_route(grain, member),
                Some("www") => edge_worker.connect_www(grain),
                _ => {
                    let reply = refused("unknownVerb", "the edge socket serves connect and www only");
                    log_unsettled("edge", "-", Some(&request), &reply);
                    write_line(&mut stream, &reply);
                    continue;
                }
            };
            match connected {
                Ok(route) => {
                    let fd = route.into_raw_fd();
                    let reply = json!({"protocol":WORKER_PROTOCOL,"decided":true,"state":"connected","detail":format!("{grain}/{member}")});
                    let _ = send_with_fd(&stream, &reply, fd);
                    unsafe { libc::close(fd) };
                }
                Err(refusal) => {
                    log_unsettled("edge", if member.is_empty() { "-" } else { member }, Some(&request), &refusal);
                    write_line(&mut stream, &refusal)
                }
            }
        }
    }).map_err(|e| e.to_string())?;
    // A thread per member connection, bounded per member and in all; over a bound the
    // connection is answered at once, never queued behind another member's request.
    let open: Arc<Mutex<HashMap<String, usize>>> = Arc::default();
    struct Slot(Arc<Mutex<HashMap<String, usize>>>, String);
    impl Drop for Slot {
        fn drop(&mut self) {
            let mut open = self.0.lock().unwrap_or_else(|p| p.into_inner());
            if let Some(count) = open.get_mut(&self.1) {
                *count -= 1;
                if *count == 0 {
                    open.remove(&self.1);
                }
            }
        }
    }
    for stream in members.incoming() {
        let Ok(mut stream) = stream else { continue };
        let member = match &dev_member {
            Some(name) => Some(name.clone()),
            None => match peer(&stream) {
                Ok((uid, _)) => {
                    let member = member_of_uid(uid);
                    if member.is_none() {
                        eprintln!("mini apps-worker: member socket peer uid {uid} is not a member account");
                    }
                    member
                }
                Err(e) => {
                    eprintln!("mini apps-worker: member socket peer credential unavailable: {e}");
                    None
                }
            },
        };
        let Some(member) = member else {
            let reply = refused("memberRefused", "the peer is not a member account (mini-s-NAME)");
            log_unsettled("member", "-", None, &reply);
            write_line(&mut stream, &reply);
            continue;
        };
        let slot = {
            let mut counts = open.lock().unwrap_or_else(|p| p.into_inner());
            let (mine, all) = (counts.get(&member).copied().unwrap_or(0), counts.values().sum::<usize>());
            if mine >= MEMBER_CONNECTIONS || all >= ALL_CONNECTIONS {
                None
            } else {
                *counts.entry(member.clone()).or_default() += 1;
                Some(Slot(open.clone(), member.clone()))
            }
        };
        let Some(slot) = slot else {
            let reply = undecided("workerBusy", format!("{member} has {MEMBER_CONNECTIONS} requests open at the worker, or the worker holds {ALL_CONNECTIONS}; nothing was done"), "the same command, once an earlier one has answered");
            log_unsettled("member", &member, None, &reply);
            write_line(&mut stream, &reply);
            continue;
        };
        let worker = worker.clone();
        // A failed spawn drops the closure, its slot and its stream: the member sees the connection close.
        let _ = std::thread::Builder::new().name("mini-apps-member".into()).spawn(move || {
            let _slot = slot;
            let (request, reply) = match read_line(&mut stream) {
                Ok(request) => {
                    let reply = worker.handle(&member, &request);
                    (Some(request), reply)
                }
                Err(e) => (None, refused("requestRefused", e)),
            };
            log_unsettled("member", &member, request.as_ref(), &reply);
            write_line(&mut stream, &reply);
        });
    }
    Ok(())
}

// --------------------------------------------- the process-backed world

/// The world file the operator writes (0600): where everything is.
pub(crate) struct ProcessWorld {
    pub profile: PathBuf,
    pub spk_host: PathBuf,
    pub mini: PathBuf,
    pub host: PathBuf,
    pub config: PathBuf,
    pub operator_socket: PathBuf,
    pub public_socket: PathBuf,
    pub management_subject: String,
    pub management_key_id: String,
    pub management_key_epoch: String,
    pub management_seed: PathBuf,
    pub management_public_hex: String,
    pub tool_task: String,
    pub tool_capability: String,
    pub parent_task: String,
    pub parent_capability: String,
    pub genesis: PathBuf,
    pub quarantine: PathBuf,
    pub wanted: PathBuf,
    pub verdicts: PathBuf,
    /// SHA-256 of the spk-host binary this worker drives: the ingest every verdict it writes is keyed by.
    pub ingest_key: String,
    pub identities_root: PathBuf,
    pub domain: String,
    pub nonce_file: PathBuf,
    pub role_basis: Value,
    /// Quarantined packages already hashed, by file identity: an install's retry, a second grain of
    /// the same package and a re-fetch that left the file in place are not re-hashed whole.
    pub hashed: Mutex<HashMap<PathBuf, (FileIdentity, String)>>,
    /// The client commands of route binds, enrollments and share issues run in two resident
    /// `mini client-resident` processes, not a `mini` process each: one pinned to the public
    /// socket (`query`, `submit`, `current-session-intent`), one for the commands that name the
    /// operator socket themselves. A resident pins one Host socket, so they are two.
    pub residents: [Mutex<crate::client_resident::Resident>; 2],
}

/// A file's identity for a retained digest: device, inode, length and both times. A rewrite in
/// place changes the ctime (which no writer can set back), a replacement the inode.
pub(crate) type FileIdentity = (u64, u64, u64, i64, i64, i64, i64);

fn file_identity(meta: &fs::Metadata) -> FileIdentity {
    use std::os::unix::fs::MetadataExt;
    (meta.dev(), meta.ino(), meta.len(), meta.mtime(), meta.mtime_nsec(), meta.ctime(), meta.ctime_nsec())
}

impl ProcessWorld {
    pub(crate) fn load(path: &Path) -> Result<Self> {
        let w = read_json(path)?;
        if w.get("protocol").and_then(Value::as_str) != Some("mini-apps-world-v1") {
            return Err("world file is not mini-apps-world-v1".into());
        }
        let p = |k: &str| -> Result<PathBuf> { Ok(PathBuf::from(text(&w, k)?)) };
        let s = |k: &str| -> Result<String> { Ok(text(&w, k)?.to_owned()) };
        let profile = p("profile")?;
        let prof = read_json(&profile)?;
        let spk_host = PathBuf::from(text(&prof, "spkHost")?);
        let ingest_key = {
            use sha2::{Digest, Sha256};
            let binary = fs::read(&spk_host).map_err(|e| format!("ingest identity: {}: {e}", spk_host.display()))?;
            format!("{:x}", Sha256::digest(&binary))
        };
        Ok(Self {
            spk_host,
            ingest_key,
            mini: p("mini")?,
            host: PathBuf::from(text(&prof, "miniHost")?),
            config: PathBuf::from(text(&prof, "miniConfig")?),
            operator_socket: PathBuf::from(text(&prof, "miniOperatorSocket")?),
            public_socket: p("publicSocket")?,
            management_subject: text(&prof, "managementSubject")?.to_owned(),
            management_key_id: s("managementKeyId")?,
            management_key_epoch: text(&prof, "managementKeyEpoch")?.to_owned(),
            management_seed: PathBuf::from(text(&prof, "managementSeed")?),
            management_public_hex: text(&prof, "managementPublicKeyHex")?.to_owned(),
            tool_task: s("toolTask")?,
            tool_capability: s("toolCapability")?,
            parent_task: s("parentTask")?,
            parent_capability: s("parentCapability")?,
            genesis: p("genesis")?,
            quarantine: p("quarantine")?,
            wanted: p("wanted")?,
            verdicts: p("verdicts")?,
            identities_root: PathBuf::from(text(&prof, "stateRoot")?).join("apps"),
            domain: s("domain")?,
            nonce_file: p("nonceFile")?,
            role_basis: w.get("roleBasis").cloned().unwrap_or(json!({"type":"allAccess"})),
            hashed: Mutex::new(HashMap::new()),
            residents: [Mutex::new(crate::client_resident::Resident::new(&p("mini")?)), Mutex::new(crate::client_resident::Resident::new(&p("mini")?))],
            profile,
        })
    }

    /// Say which ingest this worker is, beside the verdicts, so a reader treats another ingest's verdicts as absent.
    pub(crate) fn publish_ingest_key(&self) -> Result<()> {
        if !self.verdicts.is_dir() {
            fs::DirBuilder::new().mode(0o755).recursive(true).create(&self.verdicts).map_err(|e| e.to_string())?;
        }
        let path = self.verdicts.join(crate::apps::INGEST_KEY_FILE);
        if fs::read_to_string(&path).map(|t| t.trim() == self.ingest_key).unwrap_or(false) {
            return Ok(());
        }
        let temp = path.with_extension("new");
        fs::write(&temp, format!("{}\n", self.ingest_key)).map_err(|e| e.to_string())?;
        fs::set_permissions(&temp, fs::Permissions::from_mode(0o644)).map_err(|e| e.to_string())?;
        fs::rename(&temp, &path).map_err(|e| e.to_string())
    }

    /// What the worker's own session births need from the world, read from its genesis (never constants):
    /// the factory and the management enrollment's grants, the platform template and the grain birth tariff.
    fn world_shape(&self, genesis: &Value) -> Result<WorldShape> {
        shape_of(genesis, &self.management_key_id, &self.management_subject)
    }

    fn nonce(&self) -> Result<u64> {
        let current = fs::read_to_string(&self.nonce_file).ok().and_then(|t| t.trim().parse::<u64>().ok()).unwrap_or(70_000_000);
        let next = current + 1000;
        fs::write(&self.nonce_file, next.to_string()).map_err(|e| e.to_string())?;
        Ok(next)
    }

    fn run(&self, program: &Path, args: &[&str], stdout: &Path) -> Result<Value> {
        let output = Command::new(program).args(args).output().map_err(|e| format!("{}: {e}", program.display()))?;
        let _ = fs::write(stdout, &output.stdout);
        let _ = fs::write(stdout.with_extension("stderr"), &output.stderr);
        if !output.status.success() {
            return Err(format!("{} {}: {}", program.display(), args.first().unwrap_or(&""), String::from_utf8_lossy(&output.stderr).trim()));
        }
        Ok(serde_json::from_slice(&output.stdout).unwrap_or(Value::Null))
    }

    /// `mini ARGS...` in the resident for its socket; its stdout and stderr are kept beside the
    /// work as a child's were, and a nonzero exit refuses with the command's stderr.
    fn mini(&self, work: &Path, label: &str, args: &[&str]) -> Result<Value> {
        let public = args.windows(2).any(|pair| pair[0] == "--socket" && Path::new(pair[1]) == self.public_socket);
        let resident = &self.residents[usize::from(!public)];
        let (code, stdout, stderr) = resident.lock().map_err(|_| "client resident lock poisoned")?.run(args)?;
        let kept = work.join(format!("{label}.stdout"));
        let _ = fs::write(&kept, &stdout);
        let _ = fs::write(kept.with_extension("stderr"), &stderr);
        if code != 0 {
            return Err(format!("{} {}: {}", self.mini.display(), args.first().unwrap_or(&""), String::from_utf8_lossy(&stderr).trim()));
        }
        Ok(serde_json::from_slice(&stdout).unwrap_or(Value::Null))
    }

    fn confirmed(path: &Path) -> Result<Value> {
        let outcome = read_json(path)?;
        if outcome.get("type").and_then(Value::as_str) == Some("confirmed") && matches!(outcome.get("confirmation").and_then(Value::as_str), Some("installed" | "replayed")) {
            Ok(outcome)
        } else {
            Err(format!("attempt {} is not confirmed: {}", path.display(), outcome.get("type").and_then(Value::as_str).unwrap_or("?")))
        }
    }

    /// `query NAME SUBJECT TASK CAP NONCE [VIEW]`: one signed read as the management subject.
    fn query(&self, work: &Path, name: &str, task: &str, cap: &str, nonce: u64, view: &str) -> Result<(Value, Value)> {
        let intent = json!({"subject":self.management_subject,"nonce":nonce.to_string(),
            "purpose":{"type":"query","kind":"object","target":task,"view":view},
            "grants":[{"kind":"object","target":task,"capability":cap}]});
        let intent_path = work.join(format!("{name}-intent.json"));
        write_json(&intent_path, &intent)?;
        let dir = work.join(name);
        let _ = fs::remove_dir_all(&dir);
        let [h, c, s, i, k, d] = [self.host.to_str().unwrap_or(""), self.config.to_str().unwrap_or(""), self.public_socket.to_str().unwrap_or(""), intent_path.to_str().unwrap_or(""), self.management_seed.to_str().unwrap_or(""), dir.to_str().unwrap_or("")];
        self.mini(work, name, &["query", "--host", h, "--config", c, "--socket", s, "--intent", i, "--key", k, "--view", view, "--dir", d])?;
        Ok((read_json(&dir.join("view.json"))?, read_json(&dir.join("challenge.json"))?))
    }

    /// `grain_op`: a reserve on the metered tool, as the journey does before a birth.
    fn grain_op(&self, work: &Path, name: &str, task: &str, cap: &str, nonce: u64, operation: Value) -> Result<()> {
        let attempt = work.join(format!("{name}-attempt"));
        if attempt.join("outcome.json").exists() {
            return Self::confirmed(&attempt.join("outcome.json")).map(|_| ());
        }
        let (view, _) = self.query(work, &format!("{name}-before"), task, cap, nonce + 1, "resource")?;
        let intent = json!({"grain":{"task":task,"subject":self.management_subject,"capability":cap,"observeCapability":cap,
            "schemaVersion":"1","expectedTargetRoot":view["cell"]["root"],
            "context":{"operationId":nonce.to_string(),"payload":"mini apps-worker"},
            "before":{"generation":view["cell"]["grain"]["generation"],"status":view["cell"]["grain"]["status"],"remaining":view["cell"]["grain"]["remaining"],"reserved":view["cell"]["grain"]["reserved"]},
            "operation":operation,"publications":[]},
            "grants":[{"kind":"object","target":task,"capability":cap}],"intentNonce":nonce.to_string()});
        let intent_path = work.join(format!("{name}-intent.json"));
        write_json(&intent_path, &intent)?;
        let [h, c, s, i, k, d] = [self.host.to_str().unwrap_or(""), self.config.to_str().unwrap_or(""), self.public_socket.to_str().unwrap_or(""), intent_path.to_str().unwrap_or(""), self.management_seed.to_str().unwrap_or(""), attempt.to_str().unwrap_or("")];
        self.mini(work, name, &["submit", "--host", h, "--config", c, "--socket", s, "--intent", i, "--intent-kind", "grain-intent", "--key", k, "--dir", d])?;
        Self::confirmed(&attempt.join("outcome.json")).map(|_| ())
    }

    /// `birth_session`: the guest subject's session for one route.
    fn birth_session(&self, work: &Path, name: &str, app: &str, session: u64, kind: &str, cap: u64, nonce: u64) -> Result<Value> {
        let attempt = work.join(format!("{name}-attempt"));
        if attempt.join("outcome.json").exists() {
            return Self::confirmed(&attempt.join("outcome.json"));
        }
        if attempt.exists() {
            return Err(format!("birth {name} attempt is uncertain; exact recovery first"));
        }
        self.with_reserve(work, name, "5", nonce, || self.birth_session_reserved(work, name, app, session, kind, cap, nonce))
    }

    /// A reserve on the metered tool task that a refused turn gives back. The reserve law refuses a second
    /// reserve while one is outstanding on the world's only tool task, so a decided refusal after the reserve
    /// settles it for 0 and retires the reserve and turn attempts, and the retry plans the turn afresh.
    fn with_reserve<T>(&self, work: &Path, name: &str, amount: &str, nonce: u64, turn: impl FnOnce() -> Result<T>) -> Result<T> {
        let (reserve, settle) = (format!("{name}-reserve"), format!("{name}-release"));
        guarded_reserve(
            || self.grain_op(work, &reserve, &self.tool_task, &self.tool_capability, nonce, json!({"type":"reserve","amount":amount})),
            turn,
            || self.grain_op(work, &settle, &self.tool_task, &self.tool_capability, nonce + 700, json!({"type":"settle","charge":"0"})),
            || for dir in [&reserve, &settle, &format!("{name}-submit"), &name.to_owned()] { let _ = fs::remove_dir_all(work.join(format!("{dir}-attempt"))); },
        )
    }

    fn birth_session_reserved(&self, work: &Path, name: &str, app: &str, session: u64, kind: &str, cap: u64, nonce: u64) -> Result<Value> {
        let attempt = work.join(format!("{name}-attempt"));
        let (tool, _) = self.query(work, &format!("{name}-tool"), &self.tool_task, &self.tool_capability, nonce + 101, "resource")?;
        let (parent, _) = self.query(work, &format!("{name}-parent"), &self.parent_task, &self.parent_capability, nonce + 102, "resource")?;
        let genesis = read_json(&self.genesis)?;
        let shape = self.world_shape(&genesis)?;
        let m = &self.management_subject;
        let source = json!({"subject":m,"nonce":(nonce + 100).to_string(),
            "grants":[{"kind":"object","target":shape.factory,"capability":shape.factory_observe},{"kind":"account","target":m,"capability":shape.spend},
                {"kind":"object","target":self.tool_task,"capability":self.tool_capability},{"kind":"object","target":self.parent_task,"capability":self.parent_capability}],
            "applicationSessionGrainBirth":{"tariff":shape.tariff,
                "applicationSessionBirth":{"genesis":genesis,"template":shape.template,
                    "creator":m,"nonce":(nonce + 100).to_string(),"sourceCapabilities":[shape.spend],"funding":[],"feePayer":m,
                    "session":{"app":app,"session":session.to_string(),"descriptor":(session + 1).to_string(),"participant":m,"kind":kind,
                        "sessionOwnerCapability":cap.to_string(),"sessionControlCapability":(cap + 1).to_string(),
                        "descriptorOwnerCapability":(cap + 2).to_string(),"descriptorControlCapability":(cap + 3).to_string()}},
                "tool":{"task":self.tool_task,"capability":self.tool_capability,"observeCapability":self.tool_capability,"targetRoot":tool["cell"]["root"],
                    "before":{"generation":tool["cell"]["grain"]["generation"],"status":tool["cell"]["grain"]["status"],"remaining":tool["cell"]["grain"]["remaining"],"reserved":tool["cell"]["grain"]["reserved"]}},
                "parent":{"task":self.parent_task,"capability":self.parent_capability,"observeCapability":self.parent_capability,"targetRoot":parent["cell"]["root"],
                    "before":{"generation":parent["cell"]["grain"]["generation"],"status":parent["cell"]["grain"]["status"],"remaining":parent["cell"]["grain"]["remaining"],"reserved":parent["cell"]["grain"]["reserved"]}}}});
        let source_path = work.join(format!("{name}-source.json"));
        write_json(&source_path, &source)?;
        let author = work.join(format!("{name}-author"));
        let _ = fs::remove_dir_all(&author);
        let [h, c, s, k] = [self.host.to_str().unwrap_or(""), self.config.to_str().unwrap_or(""), self.public_socket.to_str().unwrap_or(""), self.management_seed.to_str().unwrap_or("")];
        self.mini(work, &format!("{name}-author"), &["current-session-intent", "--host", h, "--config", c, "--socket", s, "--source", source_path.to_str().unwrap_or(""), "--dir", author.to_str().unwrap_or("")])?;
        self.mini(work, &format!("{name}-submit"), &["submit", "--host", h, "--config", c, "--socket", s, "--intent", author.join("intent.bin").to_str().unwrap_or(""), "--intent-kind", "binary", "--key", k, "--dir", attempt.to_str().unwrap_or("")])?;
        Self::confirmed(&attempt.join("outcome.json"))
    }

    /// Signed-slot approval over an inspected plan: every slot must name the management key.
    fn approve(&self, plan: &Value, header: &str, base: Value) -> Result<Value> {
        let mut signers = Vec::new();
        for slot in plan.get("slots").and_then(Value::as_array).ok_or("plan has no slots")? {
            let key_id = slot.pointer("/signing/keyId").and_then(Value::as_str).unwrap_or("");
            if key_id != self.management_key_id {
                return Err(format!("signerUnavailable: the plan asks key {key_id}; the worker holds the management key {} only", self.management_key_id));
            }
            let header_hex = slot.get(header).and_then(Value::as_str).ok_or("slot lacks its header")?;
            let header_bytes = mini_sdk::hex::decode(header_hex).map_err(|e| e.0)?;
            use sha2::Digest;
            signers.push(json!({"role":slot["role"],"index":slot["index"],"keyId":key_id,"keyEpoch":slot["signing"]["keyEpoch"],
                "publicKey":self.management_public_hex,"headerSha256":hex(&sha2::Sha256::digest(&header_bytes)),"keyPath":self.management_seed}));
        }
        let mut out = base;
        out["signers"] = json!(signers);
        Ok(out)
    }

    fn sha_file(path: &Path) -> Result<String> {
        use sha2::Digest;
        Ok(hex(&sha2::Sha256::digest(fs::read(path).map_err(|e| e.to_string())?)))
    }

    /// `delegate_observe`: the owner of `target` delegates an observe-only child capability
    /// (ordinary signed delegation). Event22 (`grain-share-issue`) does not mint the participant's
    /// ticket observation capability (`tcap + 2`), so it is delegated from `tcap` before enrollment.
    fn delegate_observe(&self, work: &Path, name: &str, target: &str, parent_cap: &str, child_cap: &str, holder: &str, nonce: u64) -> Result<()> {
        let d = format!("{name}-delegate-{child_cap}");
        let attempt = work.join(format!("{d}-attempt"));
        if attempt.join("outcome.json").exists() {
            return Self::confirmed(&attempt.join("outcome.json")).map(|_| ());
        }
        let _ = fs::remove_dir_all(&attempt);
        let _ = self.query(work, &format!("{d}-parent"), target, parent_cap, nonce, "capability")?;
        let parent_dir = work.join(format!("{d}-parent"));
        let head_path = parent_dir.join("head.json");
        let [h, c, s, k] = [
            self.host.to_str().unwrap_or(""),
            self.config.to_str().unwrap_or(""),
            self.public_socket.to_str().unwrap_or(""),
            self.management_seed.to_str().unwrap_or(""),
        ];
        let inspect = Command::new(&self.host)
            .args([c, "inspect", "view-object-capability", parent_dir.join("view.bin").to_str().unwrap_or(""), head_path.to_str().unwrap_or("")])
            .output()
            .map_err(|e| e.to_string())?;
        if !inspect.status.success() {
            return Err(format!("inspect view-object-capability failed: {}", String::from_utf8_lossy(&inspect.stderr).trim()));
        }
        let cap_head = read_json(&head_path)?;
        let (resource_view, current) = self.query(work, &format!("{d}-owner"), target, parent_cap, nonce + 1, "resource")?;
        let mut child = cap_head.get("head").cloned().ok_or("capability inspection lacks head")?;
        let parent_id = child.get("id").and_then(Value::as_str).ok_or("capability head lacks id")?.to_owned();
        let mut ancestors: Vec<Value> = child.get("ancestors").and_then(Value::as_array).cloned().unwrap_or_default();
        if !ancestors.iter().any(|a| a.as_str() == Some(&parent_id)) {
            ancestors.push(json!(parent_id));
        }
        let child_obj = child.as_object_mut().ok_or("capability head is not an object")?;
        child_obj.insert("id".to_owned(), json!(child_cap));
        child_obj.insert("parent".to_owned(), json!(parent_id));
        child_obj.insert("holder".to_owned(), json!({"type":"subject","subject":holder}));
        child_obj.insert("targets".to_owned(), json!([target]));
        child_obj.insert("verbs".to_owned(), json!(["observe"]));
        child_obj.insert("ancestors".to_owned(), json!(ancestors));
        let intent = json!({
            "subject": self.management_subject,
            "nonce": (nonce + 2).to_string(),
            "purpose": {
                "type": "prepare",
                "draft": {
                    "type": "delegate-source",
                    "command": {
                        "kind": "object",
                        "domain": current["domain"],
                        "semantics": current["semantics"],
                        "subject": self.management_subject,
                        "nonce": (nonce + 3).to_string(),
                        "expectedTargetRoot": resource_view["cell"]["root"],
                        "parentId": parent_id,
                        "target": target,
                        "child": child,
                    }
                }
            },
            "grants": [{"kind": "object", "target": target, "capability": parent_id}]
        });
        let intent_path = work.join(format!("{d}-intent.json"));
        write_json(&intent_path, &intent)?;
        if let Err(err) = self.mini(work, &d, &["submit", "--host", h, "--config", c, "--socket", s, "--intent", intent_path.to_str().unwrap_or(""), "--key", k, "--dir", attempt.to_str().unwrap_or("")]) {
            if err.contains("capability-delegation-controller: descent")
                && self.query(work, &format!("{d}-existing"), target, child_cap, nonce + 4, "capability").is_ok()
            {
                return Ok(());
            }
            return Err(err);
        }
        Self::confirmed(&attempt.join("outcome.json")).map(|_| ())
    }

    /// A route bound after START is served only once the running resident admits it through its
    /// own route-control socket (`spk-host grain register-route`).
    fn register_hot_route(&self, work: &Path, app: &str, member: &str, generation: &str, enroll_attempt: &Path) -> Result<()> {
        let state_app = self.identities_root.join(app);
        let control_sock = state_app.join(format!("g{generation}")).join("route-control.sock");
        let route_dir = state_app.join("routes").join(format!("member-{member}"));
        if !control_sock.exists() || route_dir.join("http.sock").exists() || !route_dir.join("dispatch-custody.json").exists() {
            return Ok(());
        }
        let reg_dir = work.join(format!("register-{member}-g{generation}"));
        private_dir(&reg_dir)?;
        let req_path = reg_dir.join("request.json");
        if !req_path.exists() {
            let inspected = read_json(&enroll_attempt.join("plan-inspected.json"))?;
            let sgen = inspected
                .pointer("/enrollment/sessionGeneration")
                .and_then(Value::as_str)
                .ok_or("enrollment plan lacks sessionGeneration")?;
            let custody = route_dir.join("dispatch-custody.json");
            let custodian = route_dir.join("custodian.json");
            let req = json!({
                "protocol": "mini-spk-route-register-v1",
                "registrationNonceHex": hex(&crate::fsio::random::<32>()?),
                "expectedApp": app,
                "expectedAppGeneration": generation,
                "expectedSessionGeneration": sgen,
                "directory": route_dir,
                "dispatchCustody": custody,
                "dispatchCustodySha256": Self::sha_file(&custody)?,
                "custodianSha256": Self::sha_file(&custodian)?,
                "displayName": member,
                "preferredHandle": member,
            });
            write_json(&req_path, &req)?;
        }
        self.run(
            &self.spk_host,
            &[
                "grain",
                "register-route",
                "--socket",
                control_sock.to_str().unwrap_or(""),
                "--request",
                req_path.to_str().unwrap_or(""),
            ],
            &reg_dir.join("reply.json"),
        )?;
        Ok(())
    }
}

/// The capability a share ticket is issued under. The issuer is the management subject (the dispatch
/// admission requires it), so the capability must be HELD by the manager: the child of the member's
/// app owner capability that the member delegated to the manager at install, not the owner capability
/// itself (the member holds that one).
pub(crate) fn share_delegate_capability(delegated: &Value, app: &str, manager: &str) -> Result<String> {
    let field = |k: &str| delegated.get(k).and_then(Value::as_str).unwrap_or("");
    if field("type") != "minidregg-delegated-reference-v1" || field("target") != app || field("recipient") != manager || field("capability").is_empty() {
        return Err(format!("shareDelegationRefused: the retained delegation must be a minidregg-delegated-reference-v1 of app {app} to the manager {manager}"));
    }
    Ok(field("capability").to_owned())
}

/// Reserve, run the turn, and on a refusal give the reserve back (settle for 0) and retire the attempts so a
/// retry plans afresh. A failed release is reported by name and nothing is retired.
pub(crate) fn guarded_reserve<T>(reserve: impl FnOnce() -> Result<()>, turn: impl FnOnce() -> Result<T>, release: impl FnOnce() -> Result<()>, retire: impl FnOnce()) -> Result<T> {
    reserve()?;
    match turn() {
        Ok(done) => Ok(done),
        Err(error) => match release() {
            Ok(()) => { retire(); Err(format!("{error}; the tool reservation was released")) }
            Err(failed) => Err(format!("{error}; toolReservationReleaseUndecided: {failed}")),
        },
    }
}

/// The genesis facts a worker session birth cites.
#[derive(Debug, PartialEq)]
pub(crate) struct WorldShape { pub factory: String, pub factory_observe: String, pub spend: String, pub template: Value, pub tariff: Value }

pub(crate) fn shape_of(genesis: &Value, management_key_id: &str, management_subject: &str) -> Result<WorldShape> {
    let text = |v: &Value, k: &str| v.get(k).and_then(Value::as_str).map(str::to_owned).ok_or_else(|| format!("worldShapeUnreadable: genesis lacks {k}"));
    let enrollment = genesis.get("enrollments").and_then(Value::as_array)
        .and_then(|list| list.iter().find(|e| e.pointer("/key/keyId").and_then(Value::as_str) == Some(management_key_id)))
        .ok_or_else(|| format!("worldShapeUnreadable: genesis enrolls no key {management_key_id}"))?;
    if text(enrollment, "accountId")? != management_subject {
        return Err(format!("worldShapeUnreadable: key {management_key_id} is not the account of management subject {management_subject}"));
    }
    let platform = genesis.get("platform").ok_or("worldShapeUnreadable: genesis lacks platform")?;
    Ok(WorldShape {
        factory: text(genesis, "factoryId")?, factory_observe: text(enrollment, "factoryObserveCapabilityId")?, spend: text(enrollment, "spendCapabilityId")?,
        template: json!({"issuer":"5","ownerBudget":text(platform, "ownerBudget")?,"lifetime":text(platform, "lifetime")?}),
        tariff: platform.get("grainBirthTariff").cloned().ok_or("worldShapeUnreadable: genesis lacks platform.grainBirthTariff")?,
    })
}

/// The session, descriptor and ticket resource ids of one share, derived from the world's nonce counter
/// (unique per call, never repeated). They live above 2^62 and below 2^63: clear of the workroom's small
/// fixture ids and of every participant-namespace id (at least 2^63), so a share can never collide with
/// either, and the block of 16 consecutive ids per call (session, session + 1 the descriptor, ticket) is
/// injective in the counter. The old `app * 100 + 10` overflowed for a namespace app id.
pub(crate) fn share_ids(base: u64) -> Result<(u64, u64)> {
    const SHARE_ID_FLOOR: u64 = 1 << 62;
    let block = base.checked_mul(16).and_then(|b| SHARE_ID_FLOOR.checked_add(b)).filter(|b| *b < 1 << 63 && b.checked_add(15).is_some())
        .ok_or_else(|| format!("shareIdsExhausted: nonce {base} leaves no share id block below 2^63"))?;
    Ok((block, block + 2))
}

impl World for ProcessWorld {
    fn package(&self, package_id: &str) -> Result<Option<(PathBuf, String, u64)>> {
        let path = self.quarantine.join(format!("{package_id}.spk"));
        if !path.is_file() {
            return Ok(None);
        }
        // The digest is taken over the opened descriptor and kept for that file identity only.
        let mut file = fs::File::open(&path).map_err(|e| format!("{}: {e}", path.display()))?;
        let opened = file_identity(&file.metadata().map_err(|e| e.to_string())?);
        if let Some((identity, sha)) = self.hashed.lock().map_err(|_| "package digest cache poisoned")?.get(&path) {
            if *identity == opened {
                return Ok(Some((path.clone(), sha.clone(), opened.2)));
            }
        }
        use sha2::Digest;
        let mut digest = sha2::Sha256::new();
        std::io::copy(&mut file, &mut digest).map_err(|e| format!("{}: {e}", path.display()))?;
        if file_identity(&file.metadata().map_err(|e| e.to_string())?) != opened {
            return Err(format!("{} changed while it was hashed", path.display()));
        }
        let sha = hex(&digest.finalize());
        self.hashed.lock().map_err(|_| "package digest cache poisoned")?.insert(path.clone(), (opened, sha.clone()));
        Ok(Some((path.clone(), sha, opened.2)))
    }
    fn want(&self, package_id: &str) -> Result<()> {
        fs::write(self.wanted.join(package_id), b"").map_err(|e| format!("cannot flag {package_id} as wanted: {e}"))
    }
    fn install(&self, work: &Path, source: &Path, receipt: &Path, spk: &Path, class: &str, delegation: &Path, carry: Option<(&Path, &str)>) -> Result<Installed> {
        let [p, s, r, k, d] = [self.profile.to_str().unwrap_or(""), source.to_str().unwrap_or(""), receipt.to_str().unwrap_or(""), spk.to_str().unwrap_or(""), delegation.to_str().unwrap_or("")];
        let mut args = vec!["grain", "install", p, s, r, k, "--class", class, "--management-selector", d];
        if let Some((export, key)) = carry {
            args.extend(["--import", export.to_str().unwrap_or(""), "--exporter-key", key]);
        }
        let out = self.run(&self.spk_host, &args, &work.join("install.stdout"))?;
        let delegation_doc = read_json(delegation)?;
        let app = delegation_doc.pointer("/selector/app").and_then(Value::as_str).ok_or("delegation lacks selector.app")?.to_owned();
        Ok(Installed {
            app,
            raw_sha256: out.get("rawSha256").and_then(Value::as_str).unwrap_or("").to_owned(),
            signed_app_id: out.get("signedAppId").and_then(Value::as_str).unwrap_or("").to_owned(),
            app_version: out.get("signedAppVersion").and_then(Value::as_str).unwrap_or("").to_owned(),
        })
    }
    fn start(&self, app: &str) -> Result<Lifecycle> {
        let out = Command::new(&self.spk_host).args(["grain", "start", self.profile.to_str().unwrap_or(""), app]).output().map_err(|e| e.to_string())?;
        let text = String::from_utf8_lossy(&out.stderr).into_owned();
        if out.status.success() { Ok(Lifecycle::Done) } else if text.contains("UNRESOLVED") { Ok(Lifecycle::Undecided(text.trim().to_owned())) } else { Err(text.trim().to_owned()) }
    }
    fn stop(&self, app: &str) -> Result<Lifecycle> {
        let out = Command::new(&self.spk_host).args(["grain", "stop", self.profile.to_str().unwrap_or(""), app]).output().map_err(|e| e.to_string())?;
        let text = String::from_utf8_lossy(&out.stderr).into_owned();
        if out.status.success() { Ok(Lifecycle::Done) } else if text.contains("UNRESOLVED") || text.contains("uncertain") { Ok(Lifecycle::Undecided(text.trim().to_owned())) } else { Err(text.trim().to_owned()) }
    }
    fn status(&self, app: &str) -> Result<Value> {
        let out = Command::new(&self.spk_host).args(["grain", "status", self.profile.to_str().unwrap_or(""), app]).output().map_err(|e| e.to_string())?;
        if !out.status.success() {
            return Err(String::from_utf8_lossy(&out.stderr).trim().to_owned());
        }
        serde_json::from_slice(&out.stdout).map_err(|e| e.to_string())
    }
    fn route(&self, work: &Path, app: &str, member: &str, expected_host: &str) -> Result<RouteBound> {
        // The journey's share(): validate retained documents first, persist the route's nonce,
        // then session birth, ticket issue, observe delegation, route; then enroll.
        let state_app = self.identities_root.join(app);
        let pkgdir = state_app.join("install").join("launch-descriptor").join("package-v1");
        let schema = read_json(&pkgdir.join("schema-inspection.json"))?;
        let launch = read_json(&state_app.join("install").join("launch-descriptor").join("launch-inspection.json"))?;
        let birth_source = read_json(&work.join("birth-source.json"))?;
        let delegation_doc = read_json(&work.join("delegation.json"))?;
        if delegation_doc.get("protocol").and_then(Value::as_str) != Some("mini-spk-grain-lifecycle-delegation-v1") {
            return Err("delegationRefused: the hosting delegation is not mini-spk-grain-lifecycle-delegation-v1".into());
        }
        // The management subject observes the app and its package through the owner's lifecycle delegation;
        // the owner capabilities in the birth source are the member's own (they are the manager's only when it is the owner).
        let delegated = (delegation_doc.get("appOwner").and_then(Value::as_str).is_some_and(|o| o != self.management_subject)).then_some(delegation_doc);
        let observed = |field: &str| delegated.as_ref().and_then(|d| d.pointer(&format!("/selector/{field}"))).and_then(Value::as_str).map(str::to_owned);
        let appcap = match observed("appObserveCapability") {
            Some(cap) => cap,
            None => birth_source.pointer("/applicationGrainBirth/applicationBirth/application/appOwnerCapability").and_then(Value::as_str).ok_or("birth source lacks appOwnerCapability")?.to_owned(),
        };
        let app_delegate = share_delegate_capability(&read_json(&work.join("share-delegation.json")).map_err(|e| format!("shareDelegationRequired: the install retained no share delegation ({e}); reinstall"))?, app, &self.management_subject)?;
        let pkgcap = match observed("packageObserveCapability") {
            Some(cap) => cap,
            None => birth_source.pointer("/applicationGrainBirth/applicationBirth/application/packageOwnerCapability").and_then(Value::as_str).ok_or("birth source lacks packageOwnerCapability")?.to_owned(),
        };
        let package_manifest = birth_source.pointer("/applicationGrainBirth/applicationBirth/application/packageManifest").and_then(Value::as_str).ok_or("birth source lacks packageManifest")?.to_owned();
        let label = format!("route-{member}");
        let (base, session, ticket, cap) = route_nonce(work, &label, || self.nonce())?;
        if let Err(err) = self.birth_session(work, &format!("{label}-session"), app, session, "web", cap, base) {
            if !work.join(format!("{label}-session-attempt")).exists() {
                let _ = fs::remove_file(work.join(format!("{label}-nonce.json")));
            }
            return Err(err);
        }
        let (app_state, _) = self.query(work, &format!("{label}-app-state"), app, &appcap, base + 300, "resource")?;
        let pversion = app_state["cell"]["entries"].as_array().and_then(|e| e.iter().find(|x| x["key"]["field"] == "2")).and_then(|x| x["value"].as_str()).unwrap_or("0").to_owned();
        let t = work.join(format!("{label}-ticket"));
        private_dir(&t)?;
        if !t.join("issue").join("receipt-anchor.json").exists() {
            self.with_reserve(work, &format!("{label}-ticket"), "3", base + 400, || -> Result<()> {
            let descriptor = read_json(&pkgdir.join("descriptor-inspection.json"))?;
            let interface = descriptor["interfaces"].as_array().and_then(|i| i.iter().find(|x| x["kind"] == "web")).cloned().ok_or("package descriptor has no web interface")?;
            let m = &self.management_subject;
            let tcap = cap + ticket % 100;
            let request = json!({"spec":{"ticket":{"resource":ticket.to_string(),"scope":{"app":app,"packageVersion":pversion,
                    "packageRoot":launch["root"],"interfaceId":interface["id"],"interfaceVersion":interface["version"],"interfaceRoot":interface["root"],
                    "schemaRoot":schema["root"],"schemaVersion":schema["version"]},
                "participant":{"session":session.to_string(),"descriptorResource":(session + 1).to_string(),"kind":"web","subject":m,"origin":{"type":"human"},
                    "sessionCapability":cap.to_string(),"appObserveCapability":appcap,"ticketObserveCapability":(tcap + 2).to_string()},
                "ceiling":{"basis":role_basis(&self.role_basis, &schema),"added":[],"removed":[],"roleSchemaRoot":schema["root"],"roleVersion":schema["version"]},
                "issueNonce":(base + 500).to_string(),"notAfter":"1000000000"},
                "issuer":m,"appDelegateCapability":app_delegate,"ticketOwnerCapability":tcap.to_string(),"ticketControlCapability":(tcap + 1).to_string()},
                "payer":m,"funding":[],"sourceCapabilities":[self.world_shape(&read_json(&self.genesis)?)?.spend],
                "tool":{"task":self.tool_task,"capability":self.tool_capability,"observeCapability":self.tool_capability},
                "parent":{"task":self.parent_task,"capability":self.parent_capability,"observeCapability":self.parent_capability}});
            write_json(&t.join("request.json"), &request)?;
            let _ = fs::remove_dir_all(t.join("preview"));
            let [h, c, o] = [self.host.to_str().unwrap_or(""), self.config.to_str().unwrap_or(""), self.operator_socket.to_str().unwrap_or("")];
            self.mini(work, &format!("{label}-ticket-plan"), &["grain-share-issue-plan", "--host", h, "--config", c, "--socket", o, "--request", t.join("request.json").to_str().unwrap_or(""), "--dir", t.join("preview").to_str().unwrap_or("")])?;
            let plan = read_json(&t.join("preview").join("plan-inspected.json"))?;
            let inspected = read_json(&t.join("preview").join("request-inspected.json"))?;
            let approval = self.approve(&plan, "header", json!({"type":"minidregg-grain-share-issue-approval-v1","requestSha256":Self::sha_file(&t.join("preview").join("request.bin"))?,
                "canonicalSpec":inspected["canonicalSpec"],"issuer":inspected["spec"]["issuer"],"participantSubject":inspected["spec"]["ticket"]["participant"]["subject"],
                "appDelegateCapability":inspected["spec"]["appDelegateCapability"],"ticketResource":inspected["spec"]["ticket"]["resource"],
                "payer":inspected["payer"],"funding":inspected["funding"],"sourceCapabilities":inspected["sourceCapabilities"],"tool":inspected["tool"],"parent":inspected["parent"]}))?;
            write_json(&t.join("approval.json"), &approval)?;
            if !t.join("issue").exists() {
                self.mini(work, &format!("{label}-ticket-prepare"), &["grain-share-issue-prepare", "--host", h, "--config", c, "--socket", o, "--request", t.join("request.json").to_str().unwrap_or(""), "--approval", t.join("approval.json").to_str().unwrap_or(""), "--dir", t.join("issue").to_str().unwrap_or("")])?;
            }
            if !t.join("issue").join("submit-marker.json").exists() {
                let _ = self.mini(work, &format!("{label}-ticket-submit"), &["grain-share-issue-submit", "--socket", o, "--attempt", t.join("issue").to_str().unwrap_or("")]);
            }
            self.mini(work, &format!("{label}-ticket-lookup"), &["grain-share-issue-lookup", "--socket", o, "--attempt", t.join("issue").to_str().unwrap_or("")])?;
            Ok(())
            }).map_err(|e| { if !t.join("issue").join("submit-marker.json").exists() { let _ = fs::remove_dir_all(t.join("issue")); } e })?;
        }
        // The route request: the management key signs for the grain's guest subject (v1).
        let session_source = work.join(format!("{label}-session-author")).join("source.json");
        let session_receipt = work.join(format!("{label}-session-attempt")).join("outcome.json");
        let route_name = format!("member-{member}");
        let request = json!({"protocol":"mini-spk-grain-route-request-v1","name":route_name,"expectedHost":expected_host,
            "displayName":member,"preferredHandle":member,"sessionSource":session_source,"sessionReceipt":session_receipt,
            "ticketIssue":t.join("issue"),
            "participantKey":{"keyId":self.management_key_id,"keyEpoch":self.management_key_epoch,"publicKeyHex":self.management_public_hex,"seedPath":self.management_seed}});
        let request_path = work.join(format!("{label}-route-request.json"));
        write_json(&request_path, &request)?;
        let bound = self.run(&self.spk_host, &["grain", "route", self.profile.to_str().unwrap_or(""), app, request_path.to_str().unwrap_or("")], &work.join(format!("{label}-route.stdout")))?;
        let directory = PathBuf::from(bound.get("directory").and_then(Value::as_str).ok_or("grain route reported no directory")?);
        let custodian = read_json(&directory.join("custodian.json"))?;
        Ok(RouteBound {
            socket: PathBuf::from(bound.get("socket").and_then(Value::as_str).unwrap_or("")),
            browser_token_sha256: text(&custodian, "browserTokenSha256")?.to_owned(),
            bootstrap_token_sha256: text(&custodian, "bootstrapTokenSha256")?.to_owned(),
            api_token_sha256: text(&custodian, "apiTokenSha256")?.to_owned(),
            enrollment: json!({"session":session.to_string(),"cap":cap.to_string(),"ticket":ticket.to_string(),
                "appObserveCapability":appcap,"packageObserveCapability":pkgcap,
                "packageManifest":package_manifest,
                "ticketIssue":t.join("issue")}),
            directory,
        })
    }
    fn enroll(&self, work: &Path, app: &str, member: &str, enrollment: &Value) -> Result<Enrolled> {
        let [session, cap, ticket, appcap, pkgcap, manifest] = ["session", "cap", "ticket", "appObserveCapability", "packageObserveCapability", "packageManifest"]
            .map(|k| enrollment.get(k).and_then(Value::as_str).unwrap_or("").to_owned());
        if [&session, &cap, &ticket, &appcap, &pkgcap, &manifest].iter().any(|v| v.is_empty()) {
            return Err(format!("routeUnenrollable: the route for {member} was bound before enrollment facts were retained; it needs a new share"));
        }
        let issue = PathBuf::from(enrollment.get("ticketIssue").and_then(Value::as_str).unwrap_or(""));
        let (session_n, cap_n, ticket_n): (u64, u64, u64) = (
            session.parse().map_err(|_| "session is not decimal")?,
            cap.parse().map_err(|_| "cap is not decimal")?,
            ticket.parse().map_err(|_| "ticket is not decimal")?,
        );
        let label = format!("enroll-{member}");
        let base = self.nonce()?;
        let tcap = cap_n + ticket_n % 100;
        self.delegate_observe(
            work,
            &format!("route-{member}-ticket"),
            &ticket,
            &tcap.to_string(),
            &(tcap + 2).to_string(),
            &self.management_subject,
            base + 10,
        )?;
        // The serving generation: the app cell's field 0.
        let (app_cell, _) = self.query(work, &format!("{label}-app-{base}"), app, &appcap, base, "resource")?;
        let generation = app_cell["cell"]["entries"].as_array().and_then(|e| e.iter().find(|x| x["key"]["field"] == "0")).and_then(|x| x["value"].as_str())
            .ok_or("the app cell carries no generation")?.to_owned();
        let attempt = work.join(format!("{label}-g{generation}"));
        if fs::metadata(attempt.join("receipt.json")).map(|m| m.len() > 0).unwrap_or(false) {
            self.register_hot_route(work, app, member, &generation, &attempt)?;
            return Ok(Enrolled::Current(generation));
        }
        let [h, c, o, s] = [self.host.to_str().unwrap_or(""), self.config.to_str().unwrap_or(""), self.operator_socket.to_str().unwrap_or(""), self.public_socket.to_str().unwrap_or("")];
        let k = self.management_seed.to_str().unwrap_or("");
        // A session still active for an older generation is closed by its owner first.
        let (sview, challenge) = self.query(work, &format!("{label}-session-{base}"), &session, &cap, base + 1, "resource")?;
        let field = |name: &str| sview["cell"]["entries"].as_array().and_then(|e| e.iter().find(|x| x["key"]["field"] == name)).and_then(|x| x["value"].as_str()).and_then(|v| v.parse::<i64>().ok());
        let (sgen, status) = (field("2").ok_or("the session cell carries no generation")?, field("3").ok_or("the session cell carries no status")?);
        if status == 5 || status == 1 {
            let n = (base + 2).to_string();
            let intent = json!({"subject":self.management_subject,"nonce":n,"grants":[{"kind":"object","target":session,"capability":cap}],
                "purpose":{"type":"prepare","draft":{"type":"invoke","command":{"subject":self.management_subject,"nonce":n,
                    "targets":[{"kind":"object","target":session,"capability":cap,"observeCapability":cap,"schemaVersion":"1",
                        "expectedTargetRoot":sview["cell"]["root"],
                        "payload":{"type":"scalar","actions":[
                            {"type":"write","key":{"type":"object","resource":session,"field":"2"},"expected":sgen.to_string(),"value":(sgen + 1).to_string()},
                            {"type":"write","key":{"type":"object","resource":session,"field":"3"},"expected":status.to_string(),"value":(status + 1).to_string()}]}}]}}}});
            let _ = challenge;
            let close = work.join(format!("{label}-close-g{generation}-intent.json"));
            write_json(&close, &intent)?;
            let closed = work.join(format!("{label}-close-g{generation}-attempt"));
            let _ = fs::remove_dir_all(&closed);
            self.mini(work, &format!("{label}-close-g{generation}"), &["submit", "--host", h, "--config", c, "--socket", s, "--intent", close.to_str().unwrap_or(""), "--key", k, "--dir", closed.to_str().unwrap_or("")])?;
            if read_json(&closed.join("outcome.json"))?.get("type").and_then(Value::as_str) != Some("confirmed") {
                return Err(format!("the stale session {session} was not closed (attempt {})", closed.display()));
            }
        }
        let anchor = read_json(&issue.join("receipt-anchor.json")).map_err(|e| format!("the ticket's issue receipt anchor is missing: {e}"))?;
        let count: i64 = anchor.pointer("/receipt/acceptedCount").and_then(Value::as_str).and_then(|v| v.parse().ok()).ok_or("the issue anchor has no acceptedCount")?;
        let pkgdir = self.identities_root.join(app).join("install").join("launch-descriptor").join("package-v1");
        let schema = read_json(&pkgdir.join("schema-inspection.json"))?;
        let request = json!({"issueIndex":(count - 1).to_string(),"ticketResource":ticket,"packageManifest":manifest,
            "role":{"basis":role_basis(&self.role_basis, &schema),"added":[],"removed":[],"roleSchemaRoot":schema["root"],"roleVersion":schema["version"]},
            "descriptorCapability":(cap_n + 2).to_string(),"sessionObserveCapability":cap,"descriptorObserveCapability":(cap_n + 2).to_string(),
            "manifestObserveCapability":pkgcap,"nonce":(base + 3).to_string()});
        let _ = session_n;
        let request_path = work.join(format!("{label}-g{generation}-request.json"));
        write_json(&request_path, &request)?;
        for retry in 0..4 {
            let _ = fs::remove_dir_all(&attempt);
            let plan_args = ["session-enrollment-plan", "--host", h, "--config", c, "--operator-socket", o, "--request", request_path.to_str().unwrap_or(""), "--dir", attempt.to_str().unwrap_or("")];
            self.mini(work, &format!("{label}-g{generation}-plan-r{retry}"), &plan_args)
                .map_err(|e| format!("session-enrollment-plan was refused: {e}"))?;
            for part in ["plan.bin", "plan-inspected.json", "request.bin"] {
                if !attempt.join(part).is_file() {
                    return Err(format!("session-enrollment-plan wrote no {part}"));
                }
            }
            let inspected = read_json(&attempt.join("plan-inspected.json"))?;
            let approval = self.approve(&inspected, "headerHex", json!({"type":"minidregg-session-enrollment-approval-v1",
                "requestSha256":Self::sha_file(&attempt.join("request.bin"))?,"planSha256":Self::sha_file(&attempt.join("plan.bin"))?,
                "planInspectionSha256":Self::sha_file(&attempt.join("plan-inspected.json"))?}))?;
            let approval_path = work.join(format!("{label}-g{generation}-approval.json"));
            write_json(&approval_path, &approval)?;
            match self.mini(work, &format!("{label}-g{generation}-seal-r{retry}"), &["session-enrollment-seal", "--attempt", attempt.to_str().unwrap_or(""), "--approval", approval_path.to_str().unwrap_or("")]) {
                Ok(out) => {
                    let _ = out;
                    break;
                }
                Err(err) if retry < 3 && err.contains("no longer current") => continue,
                Err(err) => return Err(err),
            }
        }
        if !attempt.join("submit-marker.json").exists() {
            // An uncertain submit is never repeated; the exact lookup decides.
            let _ = self.mini(work, &format!("{label}-g{generation}-submit"), &["session-enrollment-submit", "--attempt", attempt.to_str().unwrap_or("")]);
        }
        self.mini(work, &format!("{label}-g{generation}-lookup"), &["session-enrollment-lookup", "--attempt", attempt.to_str().unwrap_or("")])?;
        if !fs::metadata(attempt.join("receipt.json")).map(|m| m.len() > 0).unwrap_or(false) {
            return Err(format!("the enrollment for generation {generation} has no receipt (attempt {})", attempt.display()));
        }
        self.register_hot_route(work, app, member, &generation, &attempt)?;
        Ok(Enrolled::Renewed(generation))
    }
    fn export(&self, app: &str, out: &Path) -> Result<()> {
        let output = Command::new(&self.spk_host).args(["grain", "export", self.profile.to_str().unwrap_or(""), app, out.to_str().unwrap_or("")]).output().map_err(|e| e.to_string())?;
        if output.status.success() { Ok(()) } else { Err(String::from_utf8_lossy(&output.stderr).trim().to_owned()) }
    }
    fn identities(&self, app: &str) -> Result<Vec<Value>> {
        let dir = self.identities_root.join(app).join("identities");
        let mut out = Vec::new();
        let Ok(entries) = fs::read_dir(&dir) else { return Ok(out) };
        for entry in entries.flatten() {
            let name = entry.file_name().to_string_lossy().into_owned();
            let Some(token) = name.strip_suffix(".json") else { continue };
            if token.len() != 64 { continue; }
            let record = read_json(&entry.path())?;
            if record.get("protocol").and_then(Value::as_str) != Some("mini-spk-saved-identity-v1") { continue; }
            out.push(json!({"token":token,"identityId":record["identityId"],"displayName":record["displayName"],"preferredHandle":record["preferredHandle"],
                "savedAt":record["savedAt"],"revoked":record.get("revoked").and_then(Value::as_bool).unwrap_or(false)}));
        }
        out.sort_by(|a, b| a["token"].as_str().cmp(&b["token"].as_str()));
        Ok(out)
    }
    fn revoke_identity(&self, app: &str, token: &str) -> Result<()> {
        let path = self.identities_root.join(app).join("identities").join(format!("{token}.json"));
        let mut record = read_json(&path).map_err(|_| format!("unknownToken: {app} holds no identity {}…", &token[..8]))?;
        record["revoked"] = json!(true);
        record["revokedAt"] = json!(now());
        write_json(&path, &record)
    }
    fn verdict(&self, package_id: &str, verdict: &Value) -> Result<()> {
        if !self.verdicts.is_dir() {
            fs::DirBuilder::new().mode(0o755).recursive(true).create(&self.verdicts).map_err(|e| e.to_string())?;
        }
        self.publish_ingest_key()?;
        let mut keyed = verdict.clone();
        keyed["ingestKey"] = json!(self.ingest_key);
        let path = self.verdicts.join(format!("{package_id}.json"));
        let temp = path.with_extension("json.new");
        fs::write(&temp, serde_json::to_vec_pretty(&keyed).map_err(|e| e.to_string())?).map_err(|e| e.to_string())?;
        fs::set_permissions(&temp, fs::Permissions::from_mode(0o644)).map_err(|e| e.to_string())?;
        fs::rename(&temp, &path).map_err(|e| e.to_string())
    }
    fn domain(&self) -> &str {
        &self.domain
    }
}

/// `mini apps-worker --state DIR --world WORLD.json [--member-socket PATH] [--edge-socket PATH]
/// [--member-group mini-sessions] [--edge-group mini-edge] [--dev-member NAME]`
pub(crate) fn run(mut args: Args) -> Result<()> {
    let state = absolute(&path(args.required("state")?))?;
    let world_path = absolute(&path(args.required("world")?))?;
    // `--socket` is the client's Host-socket option, consumed before dispatch: the member socket has its own name.
    let socket = args.optional("member-socket").map(|v| absolute(&path(v))).transpose()?.unwrap_or_else(|| PathBuf::from("/run/mini-apps/worker.sock"));
    let edge = args.optional("edge-socket").map(|v| absolute(&path(v))).transpose()?.unwrap_or_else(|| state.join("edge.sock"));
    let dev_member = args.optional("dev-member").map(|v| v.into_string().map_err(|_| "--dev-member must be UTF-8".to_owned())).transpose()?;
    let member_group = args.optional("member-group").map(|v| v.into_string().map_err(|_| "--member-group must be UTF-8".to_owned())).transpose()?;
    let edge_group = args.optional("edge-group").map(|v| v.into_string().map_err(|_| "--edge-group must be UTF-8".to_owned())).transpose()?;
    args.finish()?;
    private_dir(&state)?;
    let world = ProcessWorld::load(&world_path)?;
    world.publish_ingest_key()?;
    let worker = Arc::new(Worker::open(state, Box::new(world))?);
    let members = bind(&socket, 0o660, member_group.as_deref())?;
    let edge_listener = bind(&edge, 0o660, edge_group.as_deref())?;
    let resumed = worker.resume();
    println!("mini apps-worker: members at {}, edge connector at {}; {} unfinished install(s) resumed{}", socket.display(), edge.display(), resumed.len(),
        if resumed.is_empty() { String::new() } else { format!(": {}", resumed.join(" ")) });
    std::io::stdout().flush().map_err(|e| e.to_string())?;
    serve(worker, members, edge_listener, dev_member)
}

#[cfg(test)]
mod tests {

    #[test]
    fn a_refused_turn_gives_its_reservation_back_and_a_failed_release_is_named() {
        use std::cell::Cell;
        let (released, retired) = (Cell::new(0), Cell::new(0));
        let refused: super::Result<()> = super::guarded_reserve(|| Ok(()), || Err("law-denied".into()), || { released.set(released.get() + 1); Ok(()) }, || retired.set(retired.get() + 1));
        assert!(refused.unwrap_err().contains("law-denied; the tool reservation was released"));
        assert_eq!((released.get(), retired.get()), (1, 1));
        let ok = super::guarded_reserve(|| Ok(()), || Ok(7), || panic!("no release on success"), || panic!("no retire on success"));
        assert_eq!(ok, Ok(7));
        let stuck: super::Result<()> = super::guarded_reserve(|| Ok(()), || Err("refused".into()), || Err("undecided".into()), || panic!("nothing retired when the release failed"));
        assert!(stuck.unwrap_err().contains("toolReservationReleaseUndecided: undecided"));
        let not_reserved: super::Result<()> = super::guarded_reserve(|| Err("reserve refused".into()), || panic!("no turn"), || panic!("no release"), || {});
        assert_eq!(not_reserved.unwrap_err(), "reserve refused");
    }

    #[test]
    fn a_share_is_issued_under_the_capability_the_manager_holds() {
        let delegated = json!({"type":"minidregg-delegated-reference-v1","recipient":"8","kind":"object","target":"13827490942341725565","capability":"777"});
        assert_eq!(super::share_delegate_capability(&delegated, "13827490942341725565", "8").unwrap(), "777");
        for (wrong_app, wrong_manager) in [("1", "8"), ("13827490942341725565", "9")] {
            assert!(super::share_delegate_capability(&delegated, wrong_app, wrong_manager).unwrap_err().starts_with("shareDelegationRefused"));
        }
        assert!(super::share_delegate_capability(&json!({"type":"minidregg-delegated-reference-v1","recipient":"8","target":"1"}), "1", "8").is_err());
    }

    #[test]
    fn world_shape_is_read_from_the_genesis_not_the_workroom_constants() {
        let genesis = |factory: &str, fobs: &str, spend: &str, life: &str| json!({"factoryId":factory,"platform":{"ownerBudget":"100000","lifetime":life,"grainBirthTariff":{"base":"2","perBirth":"1"}},
            "enrollments":[{"accountId":"7","spendCapabilityId":"41","factoryObserveCapabilityId":"54","key":{"keyId":"7007"}},{"accountId":"8","spendCapabilityId":spend,"factoryObserveCapabilityId":fobs,"key":{"keyId":"8008"}}]});
        let workroom = super::shape_of(&genesis("10", "55", "42", "10000"), "8008", "8").unwrap();
        assert_eq!((workroom.factory.as_str(), workroom.factory_observe.as_str(), workroom.spend.as_str()), ("10", "55", "42"));
        let demo = super::shape_of(&genesis("900", "7777", "6006", "200000"), "8008", "8").unwrap();
        assert_eq!((demo.factory.as_str(), demo.factory_observe.as_str(), demo.spend.as_str(), demo.template["lifetime"].as_str()), ("900", "7777", "6006", Some("200000")));
        assert!(super::shape_of(&genesis("10", "55", "42", "10000"), "9999", "8").unwrap_err().starts_with("worldShapeUnreadable"));
    }

    #[test]
    fn share_ids_are_injective_clear_of_namespace_ids_and_never_overflow() {
        use super::share_ids;
        let (s0, t0) = share_ids(70_001_000).unwrap();
        let (s1, t1) = share_ids(70_002_000).unwrap();
        assert_eq!((t0 - s0, t1 - s1), (2, 2));
        assert!(s1 > t0, "consecutive shares never overlap");
        for base in [1u64, 70_001_000, (1 << 58) - 1] {
            let (session, ticket) = share_ids(base).unwrap();
            assert!(session >= 1 << 62 && ticket + 13 < 1 << 63, "above the fixtures, below every namespace id (2^63)");
        }
        assert!(share_ids(1 << 58).unwrap_err().starts_with("shareIdsExhausted"), "past 2^63 refuses by name");
        assert!(share_ids(u64::MAX).unwrap_err().starts_with("shareIdsExhausted"), "no wrap at u64::MAX");
    }
    use super::*;
    use std::sync::Mutex as StdMutex;

    struct FakeWorld {
        quarantine: PathBuf,
        wanted: StdMutex<Vec<String>>,
        installs: StdMutex<u32>,
        stops: StdMutex<u32>,
        routes: StdMutex<Vec<String>>,
        stop_undecided: StdMutex<bool>,
        identities: StdMutex<Vec<Value>>,
        verdicts: StdMutex<Vec<(String, Value)>>,
        route_dir: PathBuf,
        enrolled: StdMutex<Vec<(String, String)>>,
        generation: StdMutex<u32>,
        /// How long `install` takes, and whether one is running now.
        install_delay: StdMutex<Duration>,
        installing: std::sync::atomic::AtomicBool,
        /// The export and exporter key the last install carried.
        carried: StdMutex<Option<(PathBuf, String)>>,
        /// The latest run's state as `status` reports it: START makes it running, a decided STOP stopped.
        run_state: StdMutex<&'static str>,
        /// What spk-host's install answers instead of installing, when set.
        install_error: StdMutex<Option<String>>,
    }

    impl World for FakeWorld {
        fn package(&self, package_id: &str) -> Result<Option<(PathBuf, String, u64)>> {
            let path = self.quarantine.join(format!("{package_id}.spk"));
            if !path.exists() { return Ok(None); }
            Ok(Some((path, format!("{package_id}{}", "0".repeat(32)), 1000)))
        }
        fn want(&self, package_id: &str) -> Result<()> { self.wanted.lock().unwrap().push(package_id.into()); Ok(()) }
        fn install(&self, _: &Path, source: &Path, receipt: &Path, _: &Path, class: &str, delegation: &Path, carry: Option<(&Path, &str)>) -> Result<Installed> {
            *self.installs.lock().unwrap() += 1;
            *self.carried.lock().unwrap() = carry.map(|(e, k)| (e.to_path_buf(), k.to_owned()));
            if let Some(error) = self.install_error.lock().unwrap().clone() { return Err(error); }
            self.installing.store(true, std::sync::atomic::Ordering::SeqCst);
            std::thread::sleep(*self.install_delay.lock().unwrap());
            self.installing.store(false, std::sync::atomic::Ordering::SeqCst);
            assert!(source.exists() && receipt.exists() && delegation.exists());
            assert_eq!(class, "S");
            Ok(Installed { app: "4501".into(), raw_sha256: "ab".repeat(32), signed_app_id: "7qvcjh7gk0rzdx1s3c8gufd288sesf6vvdt297756xcv4q8xxvhh".into(), app_version: "5".into() })
        }
        fn start(&self, _: &str) -> Result<Lifecycle> { *self.run_state.lock().unwrap() = "running"; Ok(Lifecycle::Done) }
        fn stop(&self, _: &str) -> Result<Lifecycle> {
            *self.stops.lock().unwrap() += 1;
            if *self.stop_undecided.lock().unwrap() { return Ok(Lifecycle::Undecided("STOP in progress".into())); }
            *self.run_state.lock().unwrap() = "stopped";
            Ok(Lifecycle::Done)
        }
        fn status(&self, _: &str) -> Result<Value> {
            Ok(json!({"runs":[{"generation":"1","state":"stopped"},{"generation":self.generation.lock().unwrap().to_string(),"state":*self.run_state.lock().unwrap()}]}))
        }
        fn route(&self, _: &Path, _: &str, member: &str, host: &str) -> Result<RouteBound> {
            self.routes.lock().unwrap().push(format!("{member}@{host}"));
            let dir = self.route_dir.join(member);
            fs::create_dir_all(&dir).unwrap();
            fs::write(dir.join("bootstrap.token"), "b0".repeat(32)).unwrap();
            Ok(RouteBound { directory: dir.clone(), socket: dir.join("http.sock"), browser_token_sha256: "1".repeat(64), bootstrap_token_sha256: "2".repeat(64), api_token_sha256: "3".repeat(64), enrollment: json!({"session":"450110"}) })
        }
        fn enroll(&self, _: &Path, app: &str, member: &str, _: &Value) -> Result<Enrolled> {
            let mut done = self.enrolled.lock().unwrap();
            let generation = self.generation.lock().unwrap().to_string();
            if done.iter().any(|(m, g)| m == member && *g == generation) { return Ok(Enrolled::Current(generation)); }
            let _ = app;
            done.push((member.to_owned(), generation.clone()));
            Ok(Enrolled::Renewed(generation))
        }
        fn export(&self, _: &str, out: &Path) -> Result<()> {
            if *self.run_state.lock().unwrap() != "stopped" { return Err("export refused: the latest generation is not stopped by a completed STOP".into()); }
            fs::create_dir(out).map_err(|e| e.to_string())?;
            fs::write(out.join("manifest.json"), json!({"stopGeneration":self.generation.lock().unwrap().to_string()}).to_string()).unwrap();
            fs::write(out.join("manifest.sig"), b"sig").unwrap();
            Ok(())
        }
        fn identities(&self, _: &str) -> Result<Vec<Value>> { Ok(self.identities.lock().unwrap().clone()) }
        fn revoke_identity(&self, _: &str, token: &str) -> Result<()> {
            let mut list = self.identities.lock().unwrap();
            let Some(record) = list.iter_mut().find(|r| r["token"] == token) else { return Err("unknownToken".into()) };
            record["revoked"] = json!(true);
            Ok(())
        }
        fn verdict(&self, package_id: &str, verdict: &Value) -> Result<()> { self.verdicts.lock().unwrap().push((package_id.into(), verdict.clone())); Ok(()) }
        fn domain(&self) -> &str { "demo.test" }
    }

    static SERIAL: StdMutex<()> = StdMutex::new(());

    fn scratch(name: &str) -> PathBuf {
        let dir = std::env::temp_dir().join(format!("mini-apps-worker-{name}-{}", std::process::id()));
        let _ = fs::remove_dir_all(&dir);
        fs::create_dir_all(&dir).unwrap();
        dir
    }

    const PKG: &str = "f0277a5dce2e1c6af0cce188241411a4";
    const APP: &str = "7qvcjh7gk0rzdx1s3c8gufd288sesf6vvdt297756xcv4q8xxvhh";

    fn install_request(id: &str) -> Value {
        json!({"protocol":WORKER_PROTOCOL,"verb":"install","requestId":id,"appId":APP,"packageId":PKG,"class":"auto","indexName":"Hacker Slides",
            "birthSource":{"applicationGrainBirth":{"applicationBirth":{"application":{"appOwnerCapability":"976001"}}}},
            "birthReceipt":{"type":"confirmed","confirmation":"installed","acceptedCount":"40"},
            "delegation":{"protocol":"mini-spk-grain-lifecycle-delegation-v1","appOwner":"12","managementSubject":"8","selector":{"app":"4501"}},
            "shareDelegation":{"type":"minidregg-delegated-reference-v1","recipient":"8","kind":"object","target":"4501","capability":"777"}})
    }

    fn worker(name: &str) -> (Arc<Worker>, PathBuf) {
        worker_with(name, Duration::from_secs(30), Duration::ZERO)
    }

    fn worker_with(name: &str, grace: Duration, install_delay: Duration) -> (Arc<Worker>, PathBuf) {
        let root = scratch(name);
        let quarantine = root.join("quarantine");
        fs::create_dir_all(&quarantine).unwrap();
        let world = FakeWorld { quarantine: quarantine.clone(), wanted: StdMutex::new(vec![]), installs: StdMutex::new(0), stops: StdMutex::new(0), routes: StdMutex::new(vec![]), stop_undecided: StdMutex::new(false), identities: StdMutex::new(vec![json!({"token":"c".repeat(64),"displayName":"alice","revoked":false})]), verdicts: StdMutex::new(vec![]), route_dir: root.join("routes"), enrolled: StdMutex::new(vec![]), generation: StdMutex::new(2), install_delay: StdMutex::new(install_delay), installing: Default::default(), carried: StdMutex::new(None), run_state: StdMutex::new("running"), install_error: StdMutex::new(None) };
        let mut w = Worker::open(root.join("state"), Box::new(world)).unwrap();
        w.install_grace = grace;
        (Arc::new(w), root)
    }

    fn fake(w: &Worker) -> &FakeWorld {
        // The test world is the only World this test built.
        unsafe { &*(w.world.as_ref() as *const dyn World as *const FakeWorld) }
    }

    #[test]
    fn apps_worker_renew_enrolls_once_per_generation_and_says_so_when_nothing_is_stale() {
        let _serial = SERIAL.lock().unwrap();
        let (w, root) = worker("renew");
        let id = "0".repeat(32);
        let _ = w.handle("alice", &install_request(&id));
        fs::write(root.join("quarantine").join(format!("{PKG}.spk")), b"spk").unwrap();
        let retry = w.handle("alice", &json!({"protocol":WORKER_PROTOCOL,"verb":"retry","requestId":id}));
        assert_eq!(retry["state"], "running", "{retry}");
        // The install enrolled the owner's route against generation 2.
        assert_eq!(fake(&w).enrolled.lock().unwrap().as_slice(), [("alice".to_owned(), "2".to_owned())]);
        // Nothing is stale: renew says so and submits nothing.
        let renew = |w: &Arc<Worker>| w.handle("alice", &json!({"protocol":WORKER_PROTOCOL,"verb":"renew","grain":"a4501"}));
        let same = renew(&w);
        assert_eq!(same["state"], "current", "{same}");
        assert_eq!(fake(&w).enrolled.lock().unwrap().len(), 1);
        // A restart moved the serving generation: START renews on its own.
        *fake(&w).generation.lock().unwrap() = 4;
        let started = w.handle("alice", &json!({"protocol":WORKER_PROTOCOL,"verb":"start","grain":"a4501"}));
        assert_eq!(started["state"], "running", "{started}");
        assert_eq!(fake(&w).enrolled.lock().unwrap().last().unwrap(), &("alice".to_owned(), "4".to_owned()));
        // And the explicit verb renews a generation START did not (a later move).
        *fake(&w).generation.lock().unwrap() = 6;
        let renewed = renew(&w);
        assert_eq!(renewed["state"], "renewed", "{renewed}");
        assert_eq!(renewed["receipt"]["renewed"][0]["generation"], "6");
        // A stopped grain has no generation to enroll against: refused by name.
        let _ = w.handle("alice", &json!({"protocol":WORKER_PROTOCOL,"verb":"stop","grain":"a4501"}));
        assert_eq!(renew(&w)["refused"], "notRunning");
        // Another member cannot renew the owner's grain.
        assert_eq!(w.handle("bob", &json!({"protocol":WORKER_PROTOCOL,"verb":"renew","grain":"a4501"}))["refused"], "notOwner");
    }

    /// A grain carried from the previous world (world-migrate) is installed only by its owner,
    /// only as the same app, at its own class, once, and from its export; the new grain's
    /// record names what it carried (world-migrate verify compares the image digest).
    #[test]
    fn apps_worker_install_carries_a_previous_worlds_grain_for_its_owner_once() {
        let _serial = SERIAL.lock().unwrap();
        let (w, root) = worker("carry");
        fs::write(root.join("quarantine").join(format!("{PKG}.spk")), b"spk").unwrap();
        let carried = root.join("state").join("carried").join("a9001");
        fs::create_dir_all(carried.join("export")).unwrap();
        let image = "e".repeat(64);
        fs::write(carried.join("export").join("manifest.json"), json!({"protocol":"mini-spk-grain-export-v1","image":{"file":"var.ext4","sha256":image}}).to_string()).unwrap();
        let key = "d".repeat(64);
        fs::write(carried.join("carry.json"), json!({"protocol":"mini-apps-carried-grain-v1","grain":"a9001","owner":"alice","appId":APP,"class":"S","exporterKey":key}).to_string()).unwrap();
        let with_carry = |id: &str, grain: &str| { let mut r = install_request(id); r["carry"] = json!(grain); r };
        // Not the owner, an unknown grain: refused by name, nothing installed.
        assert_eq!(w.handle("bob", &with_carry(&"1".repeat(32), "a9001"))["refused"], "notOwner");
        assert_eq!(w.handle("alice", &with_carry(&"2".repeat(32), "a9002"))["refused"], "carryRefused");
        assert_eq!(*fake(&w).installs.lock().unwrap(), 0);
        let first = "3".repeat(32);
        let done = w.handle("alice", &with_carry(&first, "a9001"));
        assert_eq!(done["state"], "running", "{done}");
        assert_eq!(fake(&w).carried.lock().unwrap().clone(), Some((carried.join("export"), key)));
        let listed = w.handle("alice", &json!({"protocol":WORKER_PROTOCOL,"verb":"list"}));
        assert_eq!(listed["receipt"]["grains"][0]["carriedFrom"], "a9001", "{listed}");
        assert_eq!(listed["receipt"]["grains"][0]["carriedImageSha256"], image);
        // One carry, one grain: another request is refused, the first one's retry is not.
        assert_eq!(w.handle("alice", &with_carry(&"4".repeat(32), "a9001"))["refused"], "carryClaimed");
        // A second carried grain of the same application: alice now holds a4501, so it is refused before
        // any claim or install.
        let second = root.join("state").join("carried").join("a9003");
        fs::create_dir_all(second.join("export")).unwrap();
        fs::copy(carried.join("export").join("manifest.json"), second.join("export").join("manifest.json")).unwrap();
        fs::write(second.join("carry.json"), json!({"protocol":"mini-apps-carried-grain-v1","grain":"a9003","owner":"alice","appId":APP,"class":"S","exporterKey":"d".repeat(64)}).to_string()).unwrap();
        let installs = *fake(&w).installs.lock().unwrap();
        let held = w.handle("alice", &with_carry(&"6".repeat(32), "a9003"));
        assert_eq!(held["refused"], "carryRefused", "{held}");
        assert!(held["detail"].as_str().unwrap_or("").contains("already holds a4501"), "{held}");
        assert!(!second.join("claimed").exists());
        assert_eq!(*fake(&w).installs.lock().unwrap(), installs);
        // A plain install carries nothing.
        let _ = w.handle("alice", &install_request(&"5".repeat(32)));
        assert_eq!(fake(&w).carried.lock().unwrap().clone(), None);
    }

    #[test]
    fn apps_worker_install_waits_for_the_package_then_installs_once_and_routes_the_owner() {
        let _serial = SERIAL.lock().unwrap();
        let (w, root) = worker("install");
        let id = "0".repeat(32);
        // No package yet: undecided, the fetcher is asked, the request is retained.
        let first = w.handle("alice", &install_request(&id));
        assert_eq!(first["decided"], false);
        assert_eq!(first["state"], "fetching");
        assert_eq!(fake(&w).wanted.lock().unwrap().as_slice(), [PKG]);
        assert!(request_file(&w.state, &id).exists());
        // The package arrives; the exact retry completes: install once, start, the owner's route, the origin table.
        fs::write(root.join("quarantine").join(format!("{PKG}.spk")), b"spk").unwrap();
        let retry = w.handle("alice", &json!({"protocol":WORKER_PROTOCOL,"verb":"retry","requestId":id}));
        assert_eq!(retry["decided"], true, "{retry}");
        assert_eq!(retry["state"], "running");
        assert_eq!(retry["receipt"]["grain"], "a4501");
        assert_eq!(retry["receipt"]["origin"], "https://a4501.demo.test");
        assert_eq!(retry["receipt"]["identityNotice"], IDENTITY_NOTICE);
        assert_eq!(*fake(&w).installs.lock().unwrap(), 1);
        assert_eq!(fake(&w).routes.lock().unwrap().as_slice(), ["alice@a4501.demo.test"]);
        let origin = read_json(&w.state.join("origins").join("a4501.json")).unwrap();
        assert_eq!(origin["routes"][0]["member"], "alice");
        assert_eq!(origin["routes"][0]["bootstrapTokenSha256"], "2".repeat(64));
        assert_eq!(fake(&w).verdicts.lock().unwrap()[0].1["verdict"], "verified");
        // A second retry of the same id repeats nothing.
        let again = w.handle("alice", &json!({"protocol":WORKER_PROTOCOL,"verb":"retry","requestId":id}));
        assert_eq!(again["state"], "running");
        assert_eq!(*fake(&w).installs.lock().unwrap(), 1);
        assert_eq!(fake(&w).routes.lock().unwrap().len(), 1);
        // Another member cannot retry alice's request or act on her grain.
        let bob = w.handle("bob", &json!({"protocol":WORKER_PROTOCOL,"verb":"retry","requestId":id}));
        assert_eq!(bob["refused"], "notOwner");
        assert_eq!(w.handle("bob", &json!({"protocol":WORKER_PROTOCOL,"verb":"stop","grain":"a4501"}))["refused"], "notOwner");
        assert_eq!(w.handle("bob", &json!({"protocol":WORKER_PROTOCOL,"verb":"open","grain":"a4501"}))["refused"], "notOwner");
        // open hands the owner the one-time bootstrap token; list and status show the grain.
        let open = w.handle("alice", &json!({"protocol":WORKER_PROTOCOL,"verb":"open","grain":"a4501"}));
        assert_eq!(open["receipt"]["bootstrapToken"], "b0".repeat(32));
        let list = w.handle("alice", &json!({"protocol":WORKER_PROTOCOL,"verb":"list"}));
        assert_eq!(list["receipt"]["grains"][0]["grain"], "a4501");
        assert!(w.handle("bob", &json!({"protocol":WORKER_PROTOCOL,"verb":"list"}))["receipt"]["grains"].as_array().unwrap().is_empty());
        let status = w.handle("alice", &json!({"protocol":WORKER_PROTOCOL,"verb":"status","grain":"a4501"}));
        assert_eq!(status["state"], "running");
        assert_eq!(status["receipt"]["identities"][0]["displayName"], "alice");
        // share gives bob his own route; then bob may open and read status but not stop.
        let share = w.handle("alice", &json!({"protocol":WORKER_PROTOCOL,"verb":"share","grain":"a4501","to":"bob"}));
        assert_eq!(share["state"], "shared", "{share}");
        assert_eq!(fake(&w).routes.lock().unwrap().len(), 2);
        assert_eq!(w.handle("bob", &json!({"protocol":WORKER_PROTOCOL,"verb":"open","grain":"a4501"}))["state"], "open");
        assert_eq!(w.handle("bob", &json!({"protocol":WORKER_PROTOCOL,"verb":"stop","grain":"a4501"}))["refused"], "notOwner");
        assert_eq!(read_json(&w.state.join("origins").join("a4501.json")).unwrap()["routes"].as_array().unwrap().len(), 2);
        // identities and revoke by token; a malformed token refused by name.
        assert_eq!(w.handle("alice", &json!({"protocol":WORKER_PROTOCOL,"verb":"revoke-identity","grain":"a4501","token":"zz"}))["refused"], "tokenRefused");
        let revoked = w.handle("alice", &json!({"protocol":WORKER_PROTOCOL,"verb":"revoke-identity","grain":"a4501","token":"c".repeat(64)}));
        assert_eq!(revoked["state"], "revoked");
        assert_eq!(w.handle("alice", &json!({"protocol":WORKER_PROTOCOL,"verb":"identities","grain":"a4501"}))["receipt"]["identities"][0]["revoked"], true);
        // STOP is honest: undecided with its exact retry while the lifecycle runs; decided afterwards.
        *fake(&w).stop_undecided.lock().unwrap() = true;
        let stopping = w.handle("alice", &json!({"protocol":WORKER_PROTOCOL,"verb":"stop","grain":"a4501"}));
        assert_eq!(stopping["decided"], false);
        assert_eq!(stopping["exactRetry"], "mini apps status --grain a4501");
        *fake(&w).stop_undecided.lock().unwrap() = false;
        assert_eq!(w.handle("alice", &json!({"protocol":WORKER_PROTOCOL,"verb":"stop","grain":"a4501"}))["state"], "stopped");
        let export = w.handle("alice", &json!({"protocol":WORKER_PROTOCOL,"verb":"export","grain":"a4501"}));
        assert_eq!(export["state"], "exported");
        let delete = w.handle("alice", &json!({"protocol":WORKER_PROTOCOL,"verb":"delete","grain":"a4501"}));
        assert_eq!(delete["state"], "deleted");
        assert_eq!(delete["receipt"]["volumeRetained"], true);
        assert!(!w.state.join("origins").join("a4501.json").exists());
        assert_eq!(w.handle("alice", &json!({"protocol":WORKER_PROTOCOL,"verb":"open","grain":"a4501"}))["refused"], "noRoute");
        let _ = fs::remove_dir_all(&root);
    }

    #[test]
    fn apps_worker_an_instance_conflict_refuses_the_request_not_the_package() {
        let _serial = SERIAL.lock().unwrap();
        let (w, root) = worker("instance-held");
        fs::write(root.join("quarantine").join(format!("{PKG}.spk")), b"spk").unwrap();
        *fake(&w).install_error.lock().unwrap() = Some("spk-host: grain refused: derived file differs from retained instance record: /h/apps/4501/install/install.json".into());
        let held = w.handle("alice", &install_request(&"7".repeat(32)));
        assert_eq!(held["refused"], "instanceHeld", "{held}");
        assert!(fake(&w).verdicts.lock().unwrap().is_empty(), "an instance conflict wrote a package verdict");
        // A refusal of the package itself still records the package's verdict.
        *fake(&w).install_error.lock().unwrap() = Some("spk-host: ingest refused: malformed archive".into());
        let bad = w.handle("alice", &install_request(&"8".repeat(32)));
        assert_eq!(bad["refused"], "installRefused", "{bad}");
        assert_eq!(fake(&w).verdicts.lock().unwrap().last().map(|(_, v)| v["verdict"].clone()), Some(json!("refused")));
        let _ = fs::remove_dir_all(&root);
    }

    #[test]
    fn apps_worker_export_answers_only_for_the_stop_that_fenced_it() {
        let _serial = SERIAL.lock().unwrap();
        let (w, root) = worker("export-stale");
        let id = "6".repeat(32);
        fs::write(root.join("quarantine").join(format!("{PKG}.spk")), b"spk").unwrap();
        assert_eq!(w.handle("alice", &install_request(&id))["state"], "running");
        let export = |w: &Arc<Worker>| w.handle("alice", &json!({"protocol":WORKER_PROTOCOL,"verb":"export","grain":"a4501"}));
        let manifest_generation = |w: &Arc<Worker>| read_json(&w.state.join("exports/a4501/manifest.json")).unwrap()["stopGeneration"].clone();
        // While generation 2 runs there is nothing to export.
        assert_eq!(export(&w)["refused"], "exportRefused");
        assert_eq!(w.handle("alice", &json!({"protocol":WORKER_PROTOCOL,"verb":"stop","grain":"a4501"}))["state"], "stopped");
        let first = export(&w);
        assert_eq!(first["state"], "exported", "{first}");
        assert_eq!(manifest_generation(&w), "2");
        // The same STOP: the export is retained.
        let again = export(&w);
        assert!(again["detail"].as_str().unwrap_or("").contains("retained"), "{again}");
        // A later run and its STOP: the generation-2 export moves aside (kept) and generation 3 is exported.
        assert_eq!(w.handle("alice", &json!({"protocol":WORKER_PROTOCOL,"verb":"start","grain":"a4501"}))["state"], "running");
        *fake(&w).generation.lock().unwrap() = 3;
        // Running again: the retained generation-2 export no longer answers.
        assert_eq!(export(&w)["refused"], "exportRefused");
        assert!(w.state.join("exports/a4501.stale-2/manifest.sig").exists());
        assert_eq!(w.handle("alice", &json!({"protocol":WORKER_PROTOCOL,"verb":"stop","grain":"a4501"}))["state"], "stopped");
        let fresh = export(&w);
        assert_eq!(fresh["state"], "exported", "{fresh}");
        assert!(!fresh["detail"].as_str().unwrap_or("").contains("retained"), "{fresh}");
        assert_eq!(manifest_generation(&w), "3");
        let _ = fs::remove_dir_all(&root);
    }

    #[test]
    fn apps_worker_refuses_by_name_before_any_effect() {
        let _serial = SERIAL.lock().unwrap();
        let (w, root) = worker("refusals");
        let id = "1".repeat(32);
        let mut no_docs = install_request(&id);
        no_docs.as_object_mut().unwrap().remove("delegation");
        assert_eq!(w.handle("alice", &no_docs)["refused"], "birthRequired");
        let mut bad_app = install_request(&id);
        bad_app["appId"] = json!("short");
        assert_eq!(w.handle("alice", &bad_app)["refused"], "unknownApp");
        let mut bad_class = install_request(&id);
        bad_class["class"] = json!("XL");
        assert_eq!(w.handle("alice", &bad_class)["refused"], "classRefused");
        let mut unconfirmed = install_request(&id);
        unconfirmed["birthReceipt"] = json!({"type":"refused"});
        assert_eq!(w.handle("alice", &unconfirmed)["refused"], "birthRequired");
        assert_eq!(w.handle("alice", &json!({"protocol":"other","verb":"list"}))["refused"], "protocolRefused");
        assert_eq!(w.handle("alice", &json!({"protocol":WORKER_PROTOCOL,"verb":"dance"}))["refused"], "unknownVerb");
        assert_eq!(w.handle("alice", &json!({"protocol":WORKER_PROTOCOL,"verb":"retry","requestId":id}))["refused"], "unknownRequest");
        assert_eq!(w.handle("alice", &json!({"protocol":WORKER_PROTOCOL,"verb":"status","grain":"4501"}))["refused"], "grainRefused");
        assert_eq!(w.handle("alice", &json!({"protocol":WORKER_PROTOCOL,"verb":"status","grain":"a9"}))["refused"], "unknownGrain");
        assert_eq!(w.handle("Bad Name", &json!({"protocol":WORKER_PROTOCOL,"verb":"list"}))["refused"], "memberRefused");
        assert_eq!(*fake(&w).installs.lock().unwrap(), 0);
        assert!(fake(&w).wanted.lock().unwrap().is_empty());
        let _ = fs::remove_dir_all(&root);
    }

    #[test]
    fn apps_worker_edge_connector_hands_the_route_socket_over_scm_rights() {
        let _serial = SERIAL.lock().unwrap();
        let (w, root) = worker("edge");
        let id = "2".repeat(32);
        fs::write(root.join("quarantine").join(format!("{PKG}.spk")), b"spk").unwrap();
        assert_eq!(w.handle("alice", &install_request(&id))["state"], "running");
        // A fake custodian listens where the route record says.
        let socket = root.join("routes").join("alice").join("http.sock");
        let custodian = UnixListener::bind(&socket).unwrap();
        let worker = w;
        let edge_path = root.join("edge.sock");
        let members_path = root.join("worker.sock");
        let edge = bind(&edge_path, 0o600, None).unwrap();
        let members = bind(&members_path, 0o600, None).unwrap();
        assert!(bind(&root.join("none.sock"), 0o600, Some("no-such-group-anywhere")).unwrap_err().starts_with("groupUnavailable"));
        let served = worker.clone();
        std::thread::spawn(move || { let _ = serve(served, members, edge, Some("alice".into())); });
        // The front asks for alice's route and receives a connected socket.
        let mut front = UnixStream::connect(&edge_path).unwrap();
        front.write_all(br#"{"verb":"connect","grain":"a4501","route":"alice"}"#).unwrap();
        front.write_all(b"\n").unwrap();
        let (reply, fd) = receive_with_fd(&front).unwrap();
        assert_eq!(reply["state"], "connected", "{reply}");
        let mut handed = fd.expect("a socket arrived with the reply");
        let (mut app_side, _) = custodian.accept().unwrap();
        handed.write_all(b"GET / HTTP/1.1\r\n\r\n").unwrap();
        let mut head = [0_u8; 18];
        app_side.read_exact(&mut head).unwrap();
        assert_eq!(&head, b"GET / HTTP/1.1\r\n\r\n");
        // The publishing verb reaches the app directory's www.sock, the routes
        // directory's parent; with the resident gone it is grainStopped by name.
        let mut front = UnixStream::connect(&edge_path).unwrap();
        front.write_all(b"{\"verb\":\"www\",\"grain\":\"a4501\"}\n").unwrap();
        let (reply, fd) = receive_with_fd(&front).unwrap();
        assert_eq!(reply["refused"], "grainStopped", "{reply}");
        assert!(fd.is_none());
        let publishing = UnixListener::bind(root.join("www.sock")).unwrap();
        let mut front = UnixStream::connect(&edge_path).unwrap();
        front.write_all(b"{\"verb\":\"www\",\"grain\":\"a4501\"}\n").unwrap();
        let (reply, fd) = receive_with_fd(&front).unwrap();
        assert_eq!(reply["state"], "connected", "{reply}");
        let mut handed = fd.expect("the publishing socket arrived");
        let (mut site, _) = publishing.accept().unwrap();
        handed.write_all(b"HEAD / HTTP/1.0\r\n\r\n").unwrap();
        let mut head = [0_u8; 19];
        site.read_exact(&mut head).unwrap();
        assert_eq!(&head, b"HEAD / HTTP/1.0\r\n\r\n");
        // An unknown route is refused by name with no socket.
        let mut front = UnixStream::connect(&edge_path).unwrap();
        front.write_all(br#"{"verb":"connect","grain":"a4501","route":"mallory"}"#).unwrap();
        front.write_all(b"\n").unwrap();
        let (reply, fd) = receive_with_fd(&front).unwrap();
        assert_eq!(reply["refused"], "noRoute");
        assert!(fd.is_none());
        // The member socket in --dev-member mode answers a list.
        let mut member = UnixStream::connect(&members_path).unwrap();
        member.write_all(format!("{}\n", json!({"protocol":WORKER_PROTOCOL,"verb":"list"})).as_bytes()).unwrap();
        let mut reader = BufReader::new(member);
        let mut line = String::new();
        reader.read_line(&mut line).unwrap();
        let listed: Value = serde_json::from_str(&line).unwrap();
        assert_eq!(listed["receipt"]["grains"][0]["grain"], "a4501");
        let _ = fs::remove_dir_all(&root);
    }

    /// The member socket's client side: one request line, one reply line, and how long it took.
    fn call(socket: &Path, request: &Value) -> (Value, Duration) {
        let started = std::time::Instant::now();
        let mut stream = UnixStream::connect(socket).unwrap();
        stream.write_all(format!("{request}\n").as_bytes()).unwrap();
        let mut line = String::new();
        BufReader::new(stream).read_line(&mut line).unwrap();
        (serde_json::from_str(&line).unwrap(), started.elapsed())
    }

    fn wait_for(what: &str, mut done: impl FnMut() -> bool) {
        let deadline = std::time::Instant::now() + Duration::from_secs(15);
        while !done() {
            assert!(std::time::Instant::now() < deadline, "timed out waiting for {what}");
            std::thread::sleep(Duration::from_millis(50));
        }
    }

    #[test]
    fn apps_worker_concurrency_list_answers_while_an_install_runs() {
        let _serial = SERIAL.lock().unwrap();
        let (w, root) = worker_with("overlap", Duration::from_secs(2), Duration::from_secs(4));
        fs::write(root.join("quarantine").join(format!("{PKG}.spk")), b"spk").unwrap();
        let (members_path, edge_path) = (root.join("worker.sock"), root.join("edge.sock"));
        let (members, edge) = (bind(&members_path, 0o600, None).unwrap(), bind(&edge_path, 0o600, None).unwrap());
        let served = w.clone();
        std::thread::spawn(move || { let _ = serve(served, members, edge, Some("alice".into())); });
        let id = "3".repeat(32);
        let socket = members_path.clone();
        let request = install_request(&id);
        let installer = std::thread::spawn(move || call(&socket, &request));
        wait_for("the install to start", || fake(&w).installing.load(std::sync::atomic::Ordering::SeqCst));
        // Another connection's read answers at once while the install runs.
        let (listed, took) = call(&members_path, &json!({"protocol":WORKER_PROTOCOL,"verb":"list"}));
        assert_eq!(listed["state"], "listed", "{listed}");
        assert!(took < Duration::from_secs(1), "list took {took:?} behind a running install");
        // The install's own connection is answered `pending` with its exact retry, the install still running.
        let (reply, took) = installer.join().unwrap();
        assert!(fake(&w).installing.load(std::sync::atomic::Ordering::SeqCst), "the install finished before its reply ({took:?})");
        assert_eq!((reply["decided"].clone(), reply["state"].clone()), (json!(false), json!("pending")), "{reply}");
        assert_eq!(reply["exactRetry"], format!("mini apps install --app {APP} --retry {id}"));
        // The exact retry answers the outcome once decided; the install ran once.
        let retry = json!({"protocol":WORKER_PROTOCOL,"verb":"retry","requestId":id});
        wait_for("the install to be decided", || call(&members_path, &retry).0["state"] == "running");
        assert_eq!(*fake(&w).installs.lock().unwrap(), 1);
        let _ = fs::remove_dir_all(&root);
    }

    #[test]
    fn apps_worker_concurrency_second_install_of_a_pending_request_starts_no_second_run() {
        let _serial = SERIAL.lock().unwrap();
        let (w, root) = worker_with("pending", Duration::from_millis(100), Duration::from_millis(1500));
        fs::write(root.join("quarantine").join(format!("{PKG}.spk")), b"spk").unwrap();
        let id = "4".repeat(32);
        let retry = json!({"protocol":WORKER_PROTOCOL,"verb":"retry","requestId":id});
        assert_eq!(w.handle("alice", &install_request(&id))["state"], "pending");
        // The same install again, and its exact retry, while the run is in flight: pending, no second run.
        let again = w.handle("alice", &install_request(&id));
        assert_eq!((again["decided"].clone(), again["state"].clone()), (json!(false), json!("pending")), "{again}");
        assert_eq!(w.handle("alice", &retry)["state"], "pending");
        assert_eq!(w.handle("bob", &retry)["refused"], "notOwner");
        assert_eq!(request_file(&w.state, &id).exists(), true);
        wait_for("the install to be decided", || w.handle("alice", &retry)["state"] == "running");
        assert_eq!(*fake(&w).installs.lock().unwrap(), 1);
        // Decided is retained: another install of the id answers it and runs nothing.
        assert_eq!(w.handle("alice", &install_request(&id))["state"], "running");
        assert_eq!(*fake(&w).installs.lock().unwrap(), 1);
        let retained = read_json(&request_file(&w.state, &id)).unwrap();
        assert_eq!(retained["run"]["state"], "done");
        let _ = fs::remove_dir_all(&root);
    }

    #[test]
    fn apps_worker_concurrency_restart_resumes_an_unfinished_install() {
        let _serial = SERIAL.lock().unwrap();
        let (w, root) = worker_with("restart", Duration::from_millis(100), Duration::ZERO);
        fs::write(root.join("quarantine").join(format!("{PKG}.spk")), b"spk").unwrap();
        let id = "5".repeat(32);
        // What a worker that died mid-run leaves: an admitted request whose run never finished.
        let mut retained = w.admit("alice", &install_request(&id)).unwrap();
        retained["run"] = json!({"state":"running","since":"1"});
        write_json(&request_file(&w.state, &id), &retained).unwrap();
        // The restarted worker resumes it by name, with no member call.
        assert_eq!(w.resume(), vec![id.clone()]);
        wait_for("the resumed run to be decided", || read_json(&request_file(&w.state, &id)).is_ok_and(|r| r["lastOutcome"]["state"] == "running"));
        assert_eq!(*fake(&w).installs.lock().unwrap(), 1);
        assert_eq!(read_json(&request_file(&w.state, &id)).unwrap()["run"]["state"], "done");
        // Nothing is left to resume, and the member's exact retry answers the retained outcome.
        assert!(w.resume().is_empty());
        let retry = w.handle("alice", &json!({"protocol":WORKER_PROTOCOL,"verb":"retry","requestId":id}));
        assert_eq!(retry["state"], "running", "{retry}");
        assert_eq!(*fake(&w).installs.lock().unwrap(), 1);
        let _ = fs::remove_dir_all(&root);
    }

    #[test]
    fn apps_worker_share_copies_install_docs_reuses_route_nonce_reissues_bootstrap_and_wakes_stopped_grain() {
        let _serial = SERIAL.lock().unwrap();
        let (w, root) = worker("bug6");
        let id = "6".repeat(32);
        fs::write(root.join("quarantine").join(format!("{PKG}.spk")), b"spk").unwrap();
        let installed = w.handle("alice", &install_request(&id));
        assert_eq!(installed["state"], "running", "{installed}");

        // 1. Sharing copies birth-source.json, delegation.json, and share-delegation.json into state/work/<grain>/share-<to>/
        let shared = w.handle("alice", &json!({"protocol":WORKER_PROTOCOL,"verb":"share","grain":"a4501","to":"bob"}));
        assert_eq!(shared["state"], "shared", "{shared}");
        let share_work = w.state.join("work").join("a4501").join("share-bob");
        for name in ["birth-source.json", "delegation.json", "share-delegation.json"] {
            assert!(share_work.join(name).is_file(), "missing {name} in {}", share_work.display());
        }

        // 2. route_nonce persists {label}-nonce.json so retrying a partial share reuses the exact same (base, session, ticket, cap)
        let partial_work = root.join("partial-share");
        private_dir(&partial_work).unwrap();
        let counter = std::cell::Cell::new(70_000_000_u64);
        let first_nonce = route_nonce(&partial_work, "route-carol", || {
            let next = counter.get() + 1000;
            counter.set(next);
            Ok(next)
        })
        .unwrap();
        assert!(partial_work.join("route-carol-nonce.json").is_file());
        let retry_nonce = route_nonce(&partial_work, "route-carol", || {
            panic!("route_nonce must reuse the persisted nonce instead of allocating a new one")
        })
        .unwrap();
        assert_eq!(first_nonce, retry_nonce);
        assert_eq!(counter.get(), 70_001_000);

        // 3. When bootstrap.used exists (or bootstrap.token was consumed), open_route re-arms/mints a usable bootstrap token
        let alice_dir = root.join("routes").join("alice");
        fs::write(alice_dir.join("bootstrap.used"), b"used\n").unwrap();
        let reopened = w.handle("alice", &json!({"protocol":WORKER_PROTOCOL,"verb":"open","grain":"a4501"}));
        assert_eq!(reopened["state"], "open", "{reopened}");
        assert!(!alice_dir.join("bootstrap.used").exists());
        let fresh_token = reopened["receipt"]["bootstrapToken"].as_str().expect("bootstrapToken returned");
        assert_eq!(fresh_token.len(), 64);
        assert_eq!(fs::metadata(alice_dir.join("bootstrap.token")).unwrap().len(), 64);
        assert_ne!(fresh_token, "b0".repeat(32));

        // 4. With custodian.json present (live spk-host route), open_route removes bootstrap.used and preserves the custodian-bound token
        let bob_dir = root.join("routes").join("bob");
        fs::write(bob_dir.join("custodian.json"), br#"{"bootstrapTokenSha256":"2222222222222222222222222222222222222222222222222222222222222222"}"#).unwrap();
        fs::write(bob_dir.join("bootstrap.used"), b"used\n").unwrap();
        let bob_open = w.handle("bob", &json!({"protocol":WORKER_PROTOCOL,"verb":"open","grain":"a4501"}));
        assert_eq!(bob_open["state"], "open", "{bob_open}");
        assert!(!bob_dir.join("bootstrap.used").exists());
        assert_eq!(bob_open["receipt"]["bootstrapToken"], "b0".repeat(32));

        // 5. Stopping the grain and then calling open auto-wakes the grain and re-enrolls its routes against the new generation
        assert_eq!(w.handle("alice", &json!({"protocol":WORKER_PROTOCOL,"verb":"stop","grain":"a4501"}))["state"], "stopped");
        *fake(&w).generation.lock().unwrap() = 9;
        let woken = w.handle("bob", &json!({"protocol":WORKER_PROTOCOL,"verb":"open","grain":"a4501"}));
        assert_eq!(woken["state"], "open", "{woken}");
        assert!(woken["receipt"]["bootstrapToken"].is_string());
        let record = read_json(&grain_file(&w.state, "a4501")).unwrap();
        assert_eq!(record["state"], "running");
        let enrolled = fake(&w).enrolled.lock().unwrap().clone();
        assert!(enrolled.contains(&("alice".to_owned(), "9".to_owned())));
        assert!(enrolled.contains(&("bob".to_owned(), "9".to_owned())));

        let _ = fs::remove_dir_all(&root);
    }
}
