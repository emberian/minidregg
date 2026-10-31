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
    fn install(&self, work: &Path, source: &Path, receipt: &Path, spk: &Path, class: &str, delegation: &Path) -> Result<Installed>;
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

    fn open_route(&self, member: &str, grain: &str, record: Value) -> Value {
        let Some(route) = record.pointer(&format!("/routes/{member}")) else {
            return refused("noRoute", format!("{member} has no route on {grain}; the owner shares it with `mini apps share --grain {grain} --to {member}`"));
        };
        let directory = PathBuf::from(route["directory"].as_str().unwrap_or(""));
        if directory.join("bootstrap.used").exists() {
            return performed("open", format!("{grain}: the bootstrap for this route was used; the browser holds the cookie. A fresh route needs a new share"), json!({
                "grain":grain,"origin":record["origin"],"bootstrapUsed":true,"identityNotice":IDENTITY_NOTICE}));
        }
        let token = match crate::fsio::read_bounded(&directory.join("bootstrap.token"), 128) {
            Ok(bytes) => String::from_utf8_lossy(&bytes).trim().to_owned(),
            Err(error) => return undecided("routeUnavailable", format!("the route's bootstrap token is not readable: {error}"), &format!("mini apps open --grain {grain}")),
        };
        performed("open", format!("{grain}: visit {}/__mini/bootstrap and paste the one-time token", record["origin"].as_str().unwrap_or("")), json!({
            "grain":grain,"origin":record["origin"],"bootstrapPath":"/__mini/bootstrap","bootstrapToken":token,
            "identityNotice":IDENTITY_NOTICE}))
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
        match self.enroll_routes(grain, &record, None) {
            Ok((renewed, current)) if renewed.is_empty() => performed("current", format!("{grain}: every route already names the serving generation ({current} checked); nothing was submitted"), json!({"grain":grain,"renewed":[],"current":current})),
            Ok((renewed, current)) => performed("renewed", format!("{grain}: {} route(s) enrolled against the serving generation", renewed.len()), json!({"grain":grain,"renewed":renewed.iter().map(|(m, g)| json!({"member":m,"generation":g})).collect::<Vec<_>>(),"current":current})),
            Err(error) => undecided("enrolling", format!("the enrollment did not complete: {error}; nothing is repeated blindly"), &format!("mini apps renew --grain {grain}")),
        }
    }

    fn lifecycle(&self, grain: &str, mut record: Value, start: bool) -> Value {
        let app = record["app"].as_str().unwrap_or("").to_owned();
        let verb = if start { "start" } else { "stop" };
        let outcome = if start { self.world.start(&app) } else { self.world.stop(&app) };
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
        if let Err(e) = private_dir(&work) {
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
        if out.join("manifest.sig").exists() {
            return performed("exported", format!("{grain} export retained"), json!({"grain":grain,"export":out,"files":["var.ext4","manifest.json","manifest.sig"]}));
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
        Ok(json!({
            "protocol":WORKER_PROTOCOL,"requestId":text(request,"requestId").unwrap_or(""),"member":member,
            "appId":app_id,"packageId":package_id,"class":class,
            "indexName":request.get("indexName").cloned().unwrap_or(Value::Null),
            "indexVersion":request.get("indexVersion").cloned().unwrap_or(Value::Null),
            "documents":docs,"phases":{},"receivedAt":now(),
        }))
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
                let class: String = match retained["class"].as_str().unwrap_or("auto") {
                    "auto" => {
                        let bytes = retained["phases"]["package"]["bytes"].as_u64().unwrap_or(0);
                        if bytes < 64 * 1024 * 1024 { "S".into() } else { "M".into() }
                    }
                    c => c.to_owned(),
                };
                retained["class"] = json!(class);
                let _ = write_json(&request_file(&self.state, &id), retained);
                match self.world.install(&work, &source, &receipt, &spk, &class, &delegation) {
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
                        let name = if error.contains("unsupported physical profile") || error.contains("apiPath") { "unsupportedBridge" } else if error.contains("signature") || error.contains("Signature") { "unverifiedSignature" } else if error.contains("UNRESOLVED") || error.contains("uncertain") { return undecided("installing", error, &retry) } else { "installRefused" };
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
        }));
        if record.pointer(&format!("/routes/{member}")).is_none() {
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
            match self.world.start(&installed.app) {
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
    /// route directory (`apps/<app>/routes/<route>/http.sock`).
    fn connect_www(&self, grain: &str) -> std::result::Result<UnixStream, Value> {
        if !valid_grain(grain) {
            return Err(refused("routeRefused", "grain malformed"));
        }
        let Some(record) = self.grain_record(grain).map_err(|e| refused("stateUnavailable", e))? else {
            return Err(refused("unknownGrain", grain.to_owned()));
        };
        let socket = record.get("routes").and_then(Value::as_object).and_then(|routes| routes.values().next())
            .and_then(|route| route["socket"].as_str()).map(PathBuf::from)
            .ok_or_else(|| refused("noRoute", format!("{grain} has no route yet")))?;
        let routes_dir = socket.parent().and_then(Path::parent)
            .filter(|dir| dir.file_name().is_some_and(|name| name == "routes"))
            .ok_or_else(|| refused("stateUnavailable", format!("{} is not under a routes directory", socket.display())))?;
        let www = routes_dir.parent().ok_or_else(|| refused("stateUnavailable", "routes directory has no app directory"))?.join("www.sock");
        UnixStream::connect(&www).map_err(|e| refused("grainStopped", format!("{}: {e}", www.display())))
    }
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

    fn mini(&self, work: &Path, label: &str, args: &[&str]) -> Result<Value> {
        let owned: Vec<String> = args.iter().map(|s| s.to_string()).collect();
        let refs: Vec<&str> = owned.iter().map(String::as_str).collect();
        self.run(&self.mini, &refs, &work.join(format!("{label}.stdout")))
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
        let meta = fs::metadata(&path).map_err(|e| e.to_string())?;
        Ok(Some((path.clone(), Self::sha_file(&path)?, meta.len())))
    }
    fn want(&self, package_id: &str) -> Result<()> {
        fs::write(self.wanted.join(package_id), b"").map_err(|e| format!("cannot flag {package_id} as wanted: {e}"))
    }
    fn install(&self, work: &Path, source: &Path, receipt: &Path, spk: &Path, class: &str, delegation: &Path) -> Result<Installed> {
        let [p, s, r, k, d] = [self.profile.to_str().unwrap_or(""), source.to_str().unwrap_or(""), receipt.to_str().unwrap_or(""), spk.to_str().unwrap_or(""), delegation.to_str().unwrap_or("")];
        let out = self.run(&self.spk_host, &["grain", "install", p, s, r, k, "--class", class, "--management-selector", d], &work.join("install.stdout"))?;
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
        // The journey's share(): session birth, ticket issue, observe delegation, route; then enroll.
        let base = self.nonce()?;
        let (session, ticket) = share_ids(base)?;
        let cap = 300_000 + (base % 100_000) * 10;
        let label = format!("route-{member}");
        self.birth_session(work, &format!("{label}-session"), app, session, "web", cap, base)?;
        let state_app = self.identities_root.join(app);
        let pkgdir = state_app.join("install").join("launch-descriptor").join("package-v1");
        let schema = read_json(&pkgdir.join("schema-inspection.json"))?;
        let launch = read_json(&state_app.join("install").join("launch-descriptor").join("launch-inspection.json"))?;
        let birth_source = read_json(&work.join("birth-source.json"))?;
        let appcap = birth_source.pointer("/applicationGrainBirth/applicationBirth/application/appOwnerCapability").and_then(Value::as_str).ok_or("birth source lacks appOwnerCapability")?.to_owned();
        let app_delegate = share_delegate_capability(&read_json(&work.join("share-delegation.json")).map_err(|e| format!("shareDelegationRequired: the install retained no share delegation ({e}); reinstall"))?, app, &self.management_subject)?;
        let pkgcap = birth_source.pointer("/applicationGrainBirth/applicationBirth/application/packageOwnerCapability").and_then(Value::as_str).ok_or("birth source lacks packageOwnerCapability")?.to_owned();
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
                "packageManifest":birth_source.pointer("/applicationGrainBirth/applicationBirth/application/packageManifest").and_then(Value::as_str).ok_or("birth source lacks packageManifest")?,
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
        let (session_n, cap_n): (u64, u64) = (session.parse().map_err(|_| "session is not decimal")?, cap.parse().map_err(|_| "cap is not decimal")?);
        let label = format!("enroll-{member}");
        let base = self.nonce()?;
        // The serving generation: the app cell's field 0.
        let (app_cell, _) = self.query(work, &format!("{label}-app-{base}"), app, &appcap, base, "resource")?;
        let generation = app_cell["cell"]["entries"].as_array().and_then(|e| e.iter().find(|x| x["key"]["field"] == "0")).and_then(|x| x["value"].as_str())
            .ok_or("the app cell carries no generation")?.to_owned();
        let attempt = work.join(format!("{label}-g{generation}"));
        if fs::metadata(attempt.join("receipt.json")).map(|m| m.len() > 0).unwrap_or(false) {
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
        let _ = fs::remove_dir_all(&attempt);
        let plan_args = ["session-enrollment-plan", "--host", h, "--config", c, "--operator-socket", o, "--request", request_path.to_str().unwrap_or(""), "--dir", attempt.to_str().unwrap_or("")];
        self.mini(work, &format!("{label}-g{generation}-plan"), &plan_args)
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
        self.mini(work, &format!("{label}-g{generation}-seal"), &["session-enrollment-seal", "--attempt", attempt.to_str().unwrap_or(""), "--approval", approval_path.to_str().unwrap_or("")])?;
        if !attempt.join("submit-marker.json").exists() {
            // An uncertain submit is never repeated; the exact lookup decides.
            let _ = self.mini(work, &format!("{label}-g{generation}-submit"), &["session-enrollment-submit", "--attempt", attempt.to_str().unwrap_or("")]);
        }
        self.mini(work, &format!("{label}-g{generation}-lookup"), &["session-enrollment-lookup", "--attempt", attempt.to_str().unwrap_or("")])?;
        if !fs::metadata(attempt.join("receipt.json")).map(|m| m.len() > 0).unwrap_or(false) {
            return Err(format!("the enrollment for generation {generation} has no receipt (attempt {})", attempt.display()));
        }
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
    }

    impl World for FakeWorld {
        fn package(&self, package_id: &str) -> Result<Option<(PathBuf, String, u64)>> {
            let path = self.quarantine.join(format!("{package_id}.spk"));
            if !path.exists() { return Ok(None); }
            Ok(Some((path, format!("{package_id}{}", "0".repeat(32)), 1000)))
        }
        fn want(&self, package_id: &str) -> Result<()> { self.wanted.lock().unwrap().push(package_id.into()); Ok(()) }
        fn install(&self, _: &Path, source: &Path, receipt: &Path, _: &Path, class: &str, delegation: &Path) -> Result<Installed> {
            *self.installs.lock().unwrap() += 1;
            self.installing.store(true, std::sync::atomic::Ordering::SeqCst);
            std::thread::sleep(*self.install_delay.lock().unwrap());
            self.installing.store(false, std::sync::atomic::Ordering::SeqCst);
            assert!(source.exists() && receipt.exists() && delegation.exists());
            assert_eq!(class, "S");
            Ok(Installed { app: "4501".into(), raw_sha256: "ab".repeat(32), signed_app_id: "7qvcjh7gk0rzdx1s3c8gufd288sesf6vvdt297756xcv4q8xxvhh".into(), app_version: "5".into() })
        }
        fn start(&self, _: &str) -> Result<Lifecycle> { Ok(Lifecycle::Done) }
        fn stop(&self, _: &str) -> Result<Lifecycle> {
            *self.stops.lock().unwrap() += 1;
            if *self.stop_undecided.lock().unwrap() { Ok(Lifecycle::Undecided("STOP in progress".into())) } else { Ok(Lifecycle::Done) }
        }
        fn status(&self, _: &str) -> Result<Value> { Ok(json!({"runs":[{"generation":"2","state":"running"}]})) }
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
        fn export(&self, _: &str, out: &Path) -> Result<()> { fs::create_dir_all(out).unwrap(); fs::write(out.join("manifest.sig"), b"sig").unwrap(); Ok(()) }
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
        let world = FakeWorld { quarantine: quarantine.clone(), wanted: StdMutex::new(vec![]), installs: StdMutex::new(0), stops: StdMutex::new(0), routes: StdMutex::new(vec![]), stop_undecided: StdMutex::new(false), identities: StdMutex::new(vec![json!({"token":"c".repeat(64),"displayName":"alice","revoked":false})]), verdicts: StdMutex::new(vec![]), route_dir: root.join("routes"), enrolled: StdMutex::new(vec![]), generation: StdMutex::new(2), install_delay: StdMutex::new(install_delay), installing: Default::default() };
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
}
