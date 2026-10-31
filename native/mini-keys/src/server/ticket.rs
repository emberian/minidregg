//! Durable provider tickets and the forward journal.
//!
//! A ticket is written to disk (`SPOOL/tickets/ID.json`, broker 0600
//! file and directory) BEFORE the day's call is counted, and it never holds the
//! bearer: `provider-forward` unseals the namespace's secret itself. So:
//!
//! * a lost `provider-authorize` reply is recovered by asking again with the
//!   same request: the broker answers with the same live ticket and counts
//!   nothing ([`Tickets::find_request`]);
//! * a broker restart strands no ticket;
//! * a forward is journaled: the ticket moves to `sending` before curl starts,
//!   and the provider's answer is retained (`ID.answer`) before the ticket moves
//!   to `answered`. Presenting the same ticket and body again replays that
//!   answer; a ticket left in `sending` by a crash, or stopped mid-call, is
//!   `uncertain` and is refused `forward-uncertain`. A retry is never a second
//!   provider call.
//!
//! The one window this does not close: a crash after the ticket is minted and
//! before it is marked counted re-counts on the retry (over by one, never under).
//! Answers are retained [`ANSWER_RETAIN_S`] after they settle and then swept;
//! the answer file holds the provider's response in plaintext in the broker's
//! 0700 spool for that long.
use crate::credentials::Owner;
use crate::wire;
use serde_json::{json, Value};
use std::collections::HashSet;
use std::fs::OpenOptions;
use std::io::{Read, Write};
use std::os::unix::fs::{DirBuilderExt, MetadataExt, OpenOptionsExt};
use std::path::{Path, PathBuf};
use std::sync::Mutex;

/// A minted ticket is good for this long.
pub const TICKET_TTL_S: u64 = 600;
/// A settled forward's answer stays replayable for this long.
pub const ANSWER_RETAIN_S: u64 = 3600;
/// Live (minted or counted) tickets one uid may hold at once.
pub const MAX_LIVE_PER_PEER: usize = 64;
const MAX_TICKET: u64 = 16_384;
const MAX_ANSWER: u64 = 2 * (wire::MAX_PROVIDER_RESPONSE as u64 + 65_536) + 4096;

pub fn now() -> u64 {
    std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).map(|d| d.as_secs()).unwrap_or(0)
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum State {
    /// Written; the day's call may or may not be counted yet.
    Minted,
    /// Counted and handed to the caller; not yet presented.
    Counted,
    /// The forward started; the provider may have been called.
    Sending,
    /// The forward finished and its answer is retained.
    Answered,
    /// The forward stopped where the provider may have been called.
    Uncertain,
    /// Presented with a body it may not carry; spent, nothing sent.
    Refused,
}

impl State {
    fn name(self) -> &'static str {
        match self {
            State::Minted => "minted",
            State::Counted => "counted",
            State::Sending => "sending",
            State::Answered => "answered",
            State::Uncertain => "uncertain",
            State::Refused => "refused",
        }
    }
    fn parse(name: &str) -> Option<Self> {
        Some(match name {
            "minted" => State::Minted,
            "counted" => State::Counted,
            "sending" => State::Sending,
            "answered" => State::Answered,
            "uncertain" => State::Uncertain,
            "refused" => State::Refused,
            _ => return None,
        })
    }
    pub fn live(self) -> bool {
        matches!(self, State::Minted | State::Counted)
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Ticket {
    pub id: String,
    pub peer: u32,
    /// Digest of the authorize request (uid, kind, provider, runner, owner, body digest).
    pub request: String,
    pub provider: String,
    pub endpoint: String,
    /// The provider row's models: the body's `model` must be one of them.
    pub models: Vec<String>,
    /// The grant's model, when the grant names one.
    pub model: Option<String>,
    /// The grant's (or the pool row's) per-call output-token ceiling.
    pub per_call: u64,
    pub body_sha256: String,
    /// The member namespace; `None` is the pool.
    pub owner: Option<Owner>,
    pub route: String,
    pub owner_epoch: Option<String>,
    pub expires: u64,
    pub state: State,
    /// When the forward settled (answered, uncertain or refused).
    pub settled: u64,
}

impl Ticket {
    fn to_json(&self) -> Value {
        json!({"type":"mini-keys-ticket-v1","id":self.id,"peer":self.peer,"request":self.request,
            "provider":self.provider,"endpoint":self.endpoint,"models":self.models,"model":self.model,
            "perCall":self.per_call,"bodySha256":self.body_sha256,
            "owner":self.owner.as_ref().map(|o| json!({"subject":o.subject,"publicKey":o.public_key})),
            "route":self.route,"ownerEpoch":self.owner_epoch,"expires":self.expires,"state":self.state.name(),"settled":self.settled})
    }

    fn from_json(v: &Value) -> Option<Self> {
        if v["type"] != "mini-keys-ticket-v1" {
            return None;
        }
        let s = |k: &str| v.get(k).and_then(Value::as_str).map(str::to_owned);
        let n = |k: &str| v.get(k).and_then(Value::as_u64);
        let owner = match v.get("owner") {
            Some(Value::Null) | None => None,
            Some(o) => Some(Owner::new(o.get("subject")?.as_str()?, o.get("publicKey")?.as_str()?).ok()?),
        };
        Some(Ticket {
            id: s("id")?,
            peer: u32::try_from(n("peer")?).ok()?,
            request: s("request")?,
            provider: s("provider")?,
            endpoint: s("endpoint")?,
            models: v.get("models")?.as_array()?.iter().map(|m| m.as_str().map(str::to_owned)).collect::<Option<_>>()?,
            model: s("model"),
            per_call: n("perCall")?,
            body_sha256: s("bodySha256")?,
            owner,
            route: s("route")?,
            owner_epoch: s("ownerEpoch"),
            expires: n("expires")?,
            state: State::parse(v.get("state")?.as_str()?)?,
            settled: n("settled")?,
        })
    }
}

/// The digest an authorize retry must reproduce to get its ticket back.
pub fn request_key(peer: u32, kind: &str, provider: &str, runner: &str, owner: Option<&Owner>, body_sha256: &str) -> String {
    let owner = owner.map(|o| format!("{}:{}", o.subject, o.public_key)).unwrap_or_default();
    super::native::sha256_hex(format!("mini-keys-ticket-request-v1\0{peer}\0{kind}\0{provider}\0{runner}\0{owner}\0{body_sha256}").as_bytes())
}

fn valid_id(id: &str) -> bool {
    id.len() == 64 && wire::unhex(id).is_ok()
}

pub struct Tickets {
    dir: PathBuf,
    /// Serializes read-modify-write of ticket files within this process.
    lock: Mutex<()>,
    /// Tickets whose forward is running in this process now.
    in_flight: Mutex<HashSet<String>>,
}

impl Tickets {
    /// `SPOOL/tickets`, created 0700 and owned by the broker; expired records swept.
    pub fn open(spool: &Path) -> Result<Self, String> {
        let dir = spool.join("tickets");
        match std::fs::DirBuilder::new().mode(0o700).create(&dir) {
            Ok(()) => {}
            Err(e) if e.kind() == std::io::ErrorKind::AlreadyExists => {}
            Err(e) => return Err(format!("ticket journal {}: {e}", dir.display())),
        }
        let meta = std::fs::symlink_metadata(&dir).map_err(|e| e.to_string())?;
        if !meta.is_dir() || meta.uid() != crate::peer::euid() || meta.mode() & 0o077 != 0 {
            return Err(format!("ticket journal {} must be the broker's 0700 directory", dir.display()));
        }
        let tickets = Tickets { dir, lock: Mutex::new(()), in_flight: Mutex::new(HashSet::new()) };
        tickets.sweep()?;
        Ok(tickets)
    }

    pub fn guard(&self) -> std::sync::MutexGuard<'_, ()> {
        self.lock.lock().unwrap_or_else(|p| p.into_inner())
    }

    fn path(&self, id: &str, ext: &str) -> PathBuf {
        self.dir.join(format!("{id}.{ext}"))
    }

    fn write_durable(&self, name: &Path, bytes: &[u8]) -> Result<(), String> {
        let tmp = name.with_extension("tmp");
        let _ = std::fs::remove_file(&tmp);
        let result = (|| -> std::io::Result<()> {
            let mut f = OpenOptions::new().write(true).create_new(true).mode(0o600).custom_flags(libc::O_NOFOLLOW).open(&tmp)?;
            f.write_all(bytes)?;
            std::fs::rename(&tmp, name)?;
            Ok(())
        })();
        result.map_err(|e| {
            let _ = std::fs::remove_file(&tmp);
            format!("ticket journal: {e}")
        })
    }

    fn read_bounded(path: &Path, bound: u64) -> Result<Option<Vec<u8>>, String> {
        let f = match OpenOptions::new().read(true).custom_flags(libc::O_NOFOLLOW).open(path) {
            Ok(f) => f,
            Err(e) if e.kind() == std::io::ErrorKind::NotFound => return Ok(None),
            Err(e) => return Err(format!("ticket journal: {e}")),
        };
        let mut out = Vec::new();
        f.take(bound + 1).read_to_end(&mut out).map_err(|e| format!("ticket journal: {e}"))?;
        if out.len() as u64 > bound {
            return Err("ticket journal record exceeds its bound".into());
        }
        Ok(Some(out))
    }

    pub fn put(&self, ticket: &Ticket) -> Result<(), String> {
        let bytes = serde_json::to_vec(&ticket.to_json()).map_err(|e| e.to_string())?;
        self.write_durable(&self.path(&ticket.id, "json"), &bytes)
    }

    pub fn get(&self, id: &str) -> Result<Option<Ticket>, String> {
        if !valid_id(id) {
            return Ok(None);
        }
        match Self::read_bounded(&self.path(id, "json"), MAX_TICKET)? {
            None => Ok(None),
            Some(bytes) => {
                let value: Value = serde_json::from_slice(&bytes).map_err(|_| "ticket journal record is not JSON")?;
                Ticket::from_json(&value).filter(|t| t.id == id).map(Some).ok_or_else(|| "ticket journal record is malformed".into())
            }
        }
    }

    pub fn remove(&self, id: &str) {
        let _ = std::fs::remove_file(self.path(id, "json"));
        let _ = std::fs::remove_file(self.path(id, "answer"));
    }

    pub fn put_answer(&self, id: &str, answer: &Value) -> Result<(), String> {
        let mut bytes = serde_json::to_vec(answer).map_err(|e| e.to_string())?;
        let result = self.write_durable(&self.path(id, "answer"), &bytes);
        wire::zero(&mut bytes);
        result
    }

    pub fn answer(&self, id: &str) -> Result<Option<Value>, String> {
        match Self::read_bounded(&self.path(id, "answer"), MAX_ANSWER)? {
            None => Ok(None),
            Some(bytes) => serde_json::from_slice(&bytes).map(Some).map_err(|_| "retained answer is not JSON".into()),
        }
    }

    fn all(&self) -> Result<Vec<Ticket>, String> {
        let mut out = Vec::new();
        for entry in std::fs::read_dir(&self.dir).map_err(|e| format!("ticket journal: {e}"))? {
            let path = entry.map_err(|e| e.to_string())?.path();
            let Some(id) = path.file_name().and_then(|n| n.to_str()).and_then(|n| n.strip_suffix(".json")) else { continue };
            if let Ok(Some(t)) = self.get(id) {
                out.push(t);
            }
        }
        Ok(out)
    }

    /// A live ticket this uid already holds for exactly this request.
    pub fn find_request(&self, peer: u32, request: &str) -> Result<Option<Ticket>, String> {
        let now = now();
        Ok(self.all()?.into_iter().find(|t| t.peer == peer && t.request == request && t.state.live() && t.expires > now))
    }

    pub fn live_for(&self, peer: u32) -> Result<usize, String> {
        let now = now();
        Ok(self.all()?.iter().filter(|t| t.peer == peer && t.state.live() && t.expires > now).count())
    }

    /// Drop expired live tickets, answers past retention, and stray temp files.
    pub fn sweep(&self) -> Result<(), String> {
        let now = now();
        for entry in std::fs::read_dir(&self.dir).map_err(|e| format!("ticket journal: {e}"))? {
            let path = entry.map_err(|e| e.to_string())?.path();
            let name = path.file_name().and_then(|n| n.to_str()).unwrap_or("").to_owned();
            if name.ends_with(".tmp") {
                let _ = std::fs::remove_file(&path);
                continue;
            }
            let Some(id) = name.strip_suffix(".json").or_else(|| name.strip_suffix(".answer")) else { continue };
            match self.get(id) {
                Ok(Some(t)) => {
                    let gone = if t.state.live() { t.expires <= now } else { t.state != State::Sending && t.settled + ANSWER_RETAIN_S <= now };
                    if gone && !self.flying(id) {
                        self.remove(id);
                    }
                }
                // An answer whose ticket is gone, or a record nobody can read: nothing points at it.
                Ok(None) | Err(_) if name.ends_with(".answer") || !valid_id(id) => {
                    let _ = std::fs::remove_file(&path);
                }
                _ => {}
            }
        }
        Ok(())
    }

    pub fn flying(&self, id: &str) -> bool {
        self.in_flight.lock().map(|s| s.contains(id)).unwrap_or(true)
    }

    pub fn take_flight(&self, id: &str) -> bool {
        self.in_flight.lock().map(|mut s| s.insert(id.to_owned())).unwrap_or(false)
    }

    pub fn land(&self, id: &str) {
        if let Ok(mut s) = self.in_flight.lock() {
            s.remove(id);
        }
    }
}

/// The forwarded body, held to the ticket's grant: one JSON object, no
/// duplicate top-level key (an upstream that keeps the first of two
/// `max_tokens` must not see a different value than this check), a `model`
/// on the row (and the grant's model when it names one), `max_tokens` within
/// the per-call ceiling (and every other output-token field the
/// OpenAI-compatible APIs read, when present), and `n` absent or 1.
pub fn body_within_grant(ticket: &Ticket, body: &[u8]) -> Result<(), String> {
    let object = unique_object(body)?;
    let model = object.get("model").and_then(Value::as_str).ok_or("the forwarded body names no model")?;
    if !ticket.models.iter().any(|m| m == model) {
        return Err(format!("model {model:?} is not on provider row {}", ticket.provider));
    }
    if ticket.model.as_deref().is_some_and(|granted| granted != model) {
        return Err(format!("model {model:?} is not the granted model"));
    }
    let tokens = object.get("max_tokens").ok_or("the forwarded body carries no max_tokens")?;
    for (key, value) in std::iter::once(("max_tokens", tokens)).chain(
        ["max_completion_tokens", "max_output_tokens"].iter().filter_map(|k| object.get(*k).map(|v| (*k, v))),
    ) {
        match value.as_u64() {
            Some(n) if n <= ticket.per_call => {}
            Some(n) => return Err(format!("{key} {n} exceeds the per-call ceiling {}", ticket.per_call)),
            None => return Err(format!("{key} must be a natural number")),
        }
    }
    if object.get("n").is_some_and(|n| n.as_u64() != Some(1)) {
        return Err("n must be absent or 1: each choice is a separate completion".into());
    }
    Ok(())
}

fn unique_object(body: &[u8]) -> Result<serde_json::Map<String, Value>, String> {
    use serde::de::{Deserializer, MapAccess, Visitor};
    struct Unique;
    impl<'de> Visitor<'de> for Unique {
        type Value = serde_json::Map<String, Value>;
        fn expecting(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
            f.write_str("one JSON object without duplicate keys")
        }
        fn visit_map<A: MapAccess<'de>>(self, mut map: A) -> Result<Self::Value, A::Error> {
            let mut out = serde_json::Map::new();
            while let Some(key) = map.next_key::<String>()? {
                let value: Value = map.next_value()?;
                if out.insert(key, value).is_some() {
                    return Err(serde::de::Error::custom("duplicate key"));
                }
            }
            Ok(out)
        }
    }
    let mut de = serde_json::Deserializer::from_slice(body);
    let object = (&mut de).deserialize_map(Unique).map_err(|_| "the forwarded body is not one JSON object with unique keys")?;
    de.end().map_err(|_| "the forwarded body has trailing bytes")?;
    Ok(object)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn ticket() -> Ticket {
        Ticket {
            id: "a".repeat(64),
            peer: 1,
            request: "b".repeat(64),
            provider: "openrouter".into(),
            endpoint: "https://x/v1/chat/completions".into(),
            models: vec!["m1".into(), "m2".into()],
            model: Some("m1".into()),
            per_call: 64,
            body_sha256: "c".repeat(64),
            owner: None,
            route: "pool".into(),
            owner_epoch: None,
            expires: 1,
            state: State::Counted,
            settled: 0,
        }
    }

    #[test]
    fn the_forwarded_body_is_held_to_the_grant_not_to_the_claim() {
        let t = ticket();
        assert!(body_within_grant(&t, br#"{"model":"m1","max_tokens":64,"messages":[]}"#).is_ok());
        for (body, why) in [
            (&br#"{"model":"m1","max_tokens":65}"#[..], "exceeds"),
            (br#"{"model":"m2","max_tokens":8}"#, "granted model"),
            (br#"{"model":"m9","max_tokens":8}"#, "not on provider row"),
            (br#"{"model":"m1"}"#, "no max_tokens"),
            (br#"{"model":"m1","max_tokens":8,"max_completion_tokens":1000}"#, "max_completion_tokens"),
            (br#"{"model":"m1","max_tokens":8,"n":4}"#, "n must be"),
            (br#"{"model":"m1","max_tokens":100000,"max_tokens":8}"#, "unique keys"),
            (br#"{"model":"m1","max_tokens":8} {}"#, "trailing"),
            (br#"[1]"#, "unique keys"),
        ] {
            let e = body_within_grant(&t, body).unwrap_err();
            assert!(e.contains(why), "{}: {e}", String::from_utf8_lossy(body));
        }
        let mut free = t.clone();
        free.model = None;
        assert!(body_within_grant(&free, br#"{"model":"m2","max_tokens":8}"#).is_ok());
    }

    #[test]
    fn a_ticket_round_trips_and_an_answer_is_retained_until_swept() {
        let dir = std::env::temp_dir().join(format!("mk-tickets-{}-{}", std::process::id(), now()));
        std::fs::create_dir_all(&dir).unwrap();
        let tickets = Tickets::open(&dir).unwrap();
        let mut t = ticket();
        t.expires = now() + 60;
        t.owner = Some(Owner::new("20", &"ab".repeat(32)).unwrap());
        tickets.put(&t).unwrap();
        assert_eq!(tickets.get(&t.id).unwrap().unwrap(), t);
        assert_eq!(tickets.find_request(1, &t.request).unwrap().unwrap().id, t.id);
        assert!(tickets.find_request(2, &t.request).unwrap().is_none());
        assert_eq!(tickets.live_for(1).unwrap(), 1);
        assert!(tickets.get("../etc").unwrap().is_none());
        tickets.put_answer(&t.id, &json!({"ok":true,"body":"00"})).unwrap();
        t.state = State::Answered;
        t.settled = now() - ANSWER_RETAIN_S - 1;
        tickets.put(&t).unwrap();
        assert_eq!(tickets.answer(&t.id).unwrap().unwrap()["body"], "00");
        tickets.sweep().unwrap();
        assert!(tickets.get(&t.id).unwrap().is_none() && tickets.answer(&t.id).unwrap().is_none());
        std::fs::remove_dir_all(&dir).unwrap();
    }
}
