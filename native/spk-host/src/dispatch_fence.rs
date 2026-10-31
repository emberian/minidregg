//! The human dispatch fence, scoped to one signed call.
//!
//! Lean's exactly-once unit is the signed call: its transaction identity is
//! derived from the call's own operation ID (`Kernel/ApplicationDispatchReceiver
//! .lean`, `receiveAdmitted`, the `findIdx?` on `transactionId`), and every new
//! human request is authored under a fresh operation ID
//! (`hostd::Journal::allocate_dispatch_operation`). One call's unknown outcome
//! therefore never makes another call unsafe, and nothing here pauses the
//! grain for every member when one call is undecided.
//!
//! Each call's attempt directory `dispatch-op-<N>/` carries:
//! - `submit-requested.json`, written once before op34/164 and never removed
//!   while the directory exists, so the same attempt can never be resent;
//! - `submit-active.json`, the same bytes, present while the call is
//!   undecided. Its removal is the resolution, recorded in `resolution.json`.
//!
//! An undecided call is settled from Lean's own answers only: the positive
//! `NO_RECORD` frame, a `confirmed` outcome, or the receipt-only op35 lookup
//! (`APPLICATION_DISPATCH_LOOKUP`, `Host/Main.lean` `applicationDispatchLookupSession`,
//! `Kernel/ApplicationDispatchLookup.lookupVerified`) on the exact retained
//! ingress. A lookup never mints a delivery permit and never resubmits.
//!
//! `absent` settles "no record" only when the Host answered the submit with
//! an outcome frame. After a LOST reply, `absent` leaves the call UNDECIDED
//! (ruling 2026-10-26): reading absence as never-happened would rest on an
//! ordering property of the operator socket that no theorem states. That
//! branch switches to "settled by Lean's frame" when the Host answers every
//! proven no-append outcome with the positive `NO_RECORD` frame (L1 item b).
//! A lookup that cannot be answered (Host down, 255, malformed) settles
//! nothing either.
//!
//! Undecided calls are bounded: past `MAX_UNDECIDED` a new call is refused
//! (`uncertain-backlog`) until lookups settle older ones. Settled directories
//! keep only their small markers, and at most `MAX_SETTLED` are retained.
//! The physical fd3 slot (`dispatch-active.json`, hostd) is a separate fence
//! and is not touched here.

use crate::io_context::IoContext;
use crate::dispatch_native::{write_new, PrivateOperator};
use crate::lifecycle_receipt_lookup::{retained, OUTCOME_TAG};
use crate::host_operations::{RESPONSE_HOST_OUTCOME, RESPONSE_NO_RECORD};
use crate::lifecycle_v3_native::{framed_payload, hex};
use serde_json::{json, Value};
use sha2::{Digest, Sha256};
use std::fmt;
use std::fs::{self, File, OpenOptions};
use std::io::{self, Read, Write};
use std::os::unix::fs::{DirBuilderExt, OpenOptionsExt};
use std::path::{Path, PathBuf};
use std::time::{Duration, Instant};

pub(crate) const SUBMIT_REQUESTED: &str = "submit-requested.json";
pub(crate) const SUBMIT_ACTIVE: &str = "submit-active.json";
pub(crate) const RESOLUTION: &str = "resolution.json";
/// Undecided calls per generation journal before new calls are refused.
/// In the week-1 shape every stranger is one guest session, so this is also
/// the per-session bound.
pub(crate) const MAX_UNDECIDED: usize = 8;
/// Settled attempt directories retained (markers only) per journal.
pub(crate) const MAX_SETTLED: usize = 256;
const LOOKUP_DEADLINE: Duration = Duration::from_secs(60);
const ATTEMPT_PREFIX: &str = "dispatch-op-";
const MAX_FRAME: u64 = 12_102_760;
const MAX_MARKER: u64 = 4096;

fn invalid(reason: &'static str) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidData, reason)
}

/// What the member is told about one signed call that did not reach the app.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum Status {
    /// Lean refused the call; it holds no record of it.
    Refused,
    /// The Store tip moved under the call; no record.
    Contention,
    /// The Host could not take the call now; no record.
    Unavailable,
    /// Lean recorded the call and issued no delivery permit, or the permit
    /// could not be inspected; the app never saw it.
    RecordedUndelivered,
    /// Neither Lean's reply nor its lookup decided the call yet.
    Uncertain,
    /// Too many undecided calls; no new call was authored.
    Backlog,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct DispatchOutcome {
    pub operation: Option<String>,
    pub status: Status,
    /// Lean's own outcome `type` and `reason`, when it gave one.
    pub lean: Option<String>,
}

impl DispatchOutcome {
    pub(crate) fn status_word(&self) -> &'static str {
        match self.status {
            Status::Refused => "refused",
            Status::Contention => "contention",
            Status::Unavailable => "unavailable",
            Status::RecordedUndelivered => "recorded-undelivered",
            Status::Uncertain => "undecided",
            Status::Backlog => "uncertain-backlog",
        }
    }
    /// `recorded` is Lean's answer about this call's Store record.
    fn recorded(&self) -> &'static str {
        match self.status {
            Status::Refused | Status::Contention | Status::Unavailable => "no",
            Status::RecordedUndelivered => "yes",
            Status::Uncertain => "unknown",
            Status::Backlog => "not-submitted",
        }
    }
    /// The exact retry. A settled call's retry is a new request (a new signed
    /// call). An undecided call's is the same call: its outcome is still
    /// owed by Lean's lookup, and the host never resends it.
    fn retry(&self) -> &'static str {
        match self.status {
            Status::Backlog => "later",
            Status::Uncertain => "same-call",
            _ => "new-request",
        }
    }
    fn http_status(&self) -> &'static str {
        match self.status {
            Status::Refused => "403 Forbidden",
            Status::RecordedUndelivered => "502 Bad Gateway",
            _ => "503 Service Unavailable",
        }
    }
    fn retry_after(&self) -> Option<u32> {
        match self.status {
            Status::Contention => Some(1),
            Status::Unavailable | Status::Uncertain => Some(5),
            Status::Backlog => Some(30),
            _ => None,
        }
    }
    pub(crate) fn into_error(self) -> io::Error {
        io::Error::other(self)
    }
    pub(crate) fn of(error: &io::Error) -> Option<&DispatchOutcome> {
        error.get_ref()?.downcast_ref::<DispatchOutcome>()
    }
    /// The full HTTP/1.1 response; HEAD omits the body.
    pub(crate) fn http_response(&self, head: bool) -> Vec<u8> {
        let mut body = json!({"protocol":"mini-spk-dispatch-outcome-v1",
            "status":self.status_word(),"recorded":self.recorded(),"retry":self.retry()});
        if let Some(operation) = &self.operation {
            body["operation"] = json!(operation);
        }
        if let Some(lean) = &self.lean {
            body["lean"] = json!(lean);
        }
        let body = format!("{body}\n");
        let retry_after = self
            .retry_after()
            .map(|seconds| format!("Retry-After: {seconds}\r\n"))
            .unwrap_or_default();
        let mut bytes = format!(
            "HTTP/1.1 {}\r\nContent-Length: {}\r\nContent-Type: application/json\r\nCache-Control: no-store\r\n{retry_after}Connection: close\r\n\r\n",
            self.http_status(),
            body.len()
        )
        .into_bytes();
        if !head {
            bytes.extend_from_slice(body.as_bytes());
        }
        bytes
    }
}

impl fmt::Display for DispatchOutcome {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "SPK dispatch {}", self.status_word())?;
        if let Some(operation) = &self.operation {
            write!(f, " (operation {operation})")?;
        }
        if let Some(lean) = &self.lean {
            write!(f, ": {lean}")?;
        }
        Ok(())
    }
}

impl std::error::Error for DispatchOutcome {}

fn attempt_number(name: &str) -> Option<u64> {
    let digits = name.strip_prefix(ATTEMPT_PREFIX)?;
    if digits.is_empty() || digits.len() > 19 || !digits.bytes().all(|b| b.is_ascii_digit()) {
        return None;
    }
    digits.parse().ok()
}

fn present(path: &Path) -> io::Result<bool> {
    match fs::symlink_metadata(path) {
        Ok(_) => Ok(true),
        Err(error) if error.kind() == io::ErrorKind::NotFound => Ok(false),
        Err(error) => Err(error),
    }
}

/// Every `dispatch-op-<N>` attempt directory under `parent`, oldest first.
/// hostd's `dispatch-op-<key>.json` tombstones are files and are skipped.
fn attempts(parent: &Path) -> io::Result<Vec<(u64, PathBuf)>> {
    let mut found = Vec::new();
    for entry in fs::read_dir(&parent).ctx("list", &parent)? {
        let entry = entry?;
        let Some(number) = entry.file_name().to_str().and_then(attempt_number) else {
            continue;
        };
        if entry.file_type()?.is_dir() {
            found.push((number, entry.path()));
        }
    }
    found.sort();
    Ok(found)
}

/// One attempt directory and whether its call is undecided (`submit-active.json` present).
struct Attempt {
    path: PathBuf,
    undecided: bool,
}

/// One pass over the journal: every attempt, oldest first, with its undecided state.
fn scan(parent: &Path) -> io::Result<Vec<Attempt>> {
    let mut found = Vec::new();
    for (_, path) in attempts(parent)? {
        let undecided = present(&path.join(SUBMIT_ACTIVE))?;
        found.push(Attempt { path, undecided });
    }
    Ok(found)
}

/// The undecided calls of this journal, oldest first.
pub(crate) fn undecided(parent: &Path) -> io::Result<Vec<PathBuf>> {
    Ok(scan(parent)?
        .into_iter()
        .filter(|attempt| attempt.undecided)
        .map(|attempt| attempt.path)
        .collect())
}

/// Write the per-call markers before op34/164. Both are create-new
/// with their directory; a second submit of the same attempt refuses.
pub(crate) fn arm(attempt_dir: &Path, marker: &[u8]) -> io::Result<PathBuf> {
    write_new(attempt_dir, SUBMIT_REQUESTED, marker)?;
    write_new(attempt_dir, SUBMIT_ACTIVE, marker)
}

/// Settle one call: record the resolution, remove `submit-active.json` only
/// if it still holds the armed bytes, then drop the call's body-bearing
/// artifacts. The removal is written before the artifacts go.
pub(crate) fn settle(active: &Path, expected: &[u8], resolution: &Value) -> io::Result<()> {
    if retained(active, MAX_MARKER)? != expected {
        return Err(invalid("dispatch submit marker drift before settlement"));
    }
    let attempt_dir = active
        .parent()
        .ok_or_else(|| invalid("dispatch submit marker parent absent"))?;
    let _ = fs::remove_file(attempt_dir.join(RESOLUTION)).ctx("remove", &(attempt_dir.join(RESOLUTION)));
    write_new(attempt_dir, RESOLUTION, &serde_json::to_vec(resolution)?)?;
    fs::remove_file(&active).ctx("remove", &active)?;
    strip(attempt_dir).map(|_| ())
}

/// Lean's refusal reasons, kept with the markers: a helper's bounded
/// `*.stderr` and a refused plan or assembly frame (`op36`/`op37`).
fn refusal_evidence(name: &std::ffi::OsStr) -> bool {
    name.to_str()
        .is_some_and(|name| name.ends_with(".stderr") || name.ends_with("-refused-frame.bin"))
}

/// Keep `submit-requested.json`, `resolution.json` and refusal evidence;
/// remove the request body, plan, ingress, permit, inspection and lookups.
/// Returns whether anything was removed.
fn strip(attempt_dir: &Path) -> io::Result<bool> {
    if present(&attempt_dir.join(SUBMIT_ACTIVE))? {
        return Err(invalid("undecided dispatch attempt is never stripped"));
    }
    let mut removed = false;
    for entry in fs::read_dir(&attempt_dir).ctx("list", &attempt_dir)? {
        let entry = entry?;
        let name = entry.file_name();
        if name == SUBMIT_REQUESTED || name == RESOLUTION || refusal_evidence(&name) {
            continue;
        }
        if entry.file_type()?.is_dir() {
            fs::remove_dir_all(entry.path()).ctx("remove", &(entry.path()))?;
        } else {
            fs::remove_file(entry.path()).ctx("remove", &(entry.path()))?;
        }
        removed = true;
    }
    Ok(removed)
}

/// Bound this journal's dispatch evidence. Settled attempts, and attempts
/// that never armed a submit (authoring refused, or the process died before
/// op34/164: no Store effect), keep only their markers and refusal evidence,
/// and at most `MAX_SETTLED` of them are retained, newest first. Undecided
/// attempts are never touched. Runs between calls on the resident's single
/// dispatch thread, so no attempt is in authoring while it runs.
#[cfg(test)]
pub(crate) fn collect(parent: &Path) -> io::Result<()> {
    collect_scanned(&scan(parent)?)
}

/// `collect` over a scan the caller already holds.
fn collect_scanned(scanned: &[Attempt]) -> io::Result<()> {
    let mut settled = Vec::new();
    for attempt in scanned.iter().filter(|attempt| !attempt.undecided) {
        strip(&attempt.path)?;
        settled.push(&attempt.path);
    }
    let excess = settled.len().saturating_sub(MAX_SETTLED);
    for path in settled.into_iter().take(excess) {
        fs::remove_dir_all(path).ctx("remove", path)?;
    }
    Ok(())
}

/// A plan (op36) or assembly (op37) refusal: no submit was armed, so the
/// call has no Store effect. The frame is retained as refusal evidence and
/// Lean's decoded reason goes to the member.
pub(crate) fn refused_before_submit(
    operator: &PrivateOperator,
    attempt_dir: &Path,
    operation_id: &str,
    opcode: u8,
    frame: &[u8],
) -> io::Error {
    let _ = write_new(attempt_dir, &format!("op{opcode}-refused-frame.bin"), frame);
    // Ops 36 and 37 are append-free by the registry (`NO_APPEND_OPERATIONS`),
    // so a reply under either marker, decided (NO_RECORD) or undecided
    // (HOST_OUTCOME), left no record: the member is refused and authors a new
    // request.
    let lean = framed_payload("dispatch outcome", frame, RESPONSE_NO_RECORD, OUTCOME_TAG)
        .or_else(|_| framed_payload("dispatch outcome", frame, RESPONSE_HOST_OUTCOME, OUTCOME_TAG))
        .ok()
        .and_then(|payload| {
            let directory = attempt_dir.join(format!("op{opcode}-refusal"));
            fs::DirBuilder::new().mode(0o700).create(&directory).ok()?;
            inspect_outcome(operator, &directory, payload, Instant::now() + LOOKUP_DEADLINE)
                .inspect_err(|error| {
                    eprintln!("spk-host: op{operation_id} op{opcode} refusal inspection failed: {error}")
                })
                .ok()
                .map(|view| refusal_words(&view))
        });
    DispatchOutcome {
        operation: (operation_id != "0").then(|| operation_id.to_owned()),
        status: Status::Refused,
        lean: Some(format!("op{opcode} {}", lean.unwrap_or_else(|| "refused".into()))),
    }
    .into_error()
}

/// `type reason` plus the UTF-8 of Lean's hex `detail`, clipped.
pub(crate) fn refusal_words(view: &Value) -> String {
    let mut words = outcome_words(view);
    if let Some(detail) = view.get("detail").and_then(Value::as_str) {
        let bytes: Vec<u8> = (0..detail.len() / 2)
            .filter_map(|i| u8::from_str_radix(detail.get(i * 2..i * 2 + 2)?, 16).ok())
            .collect();
        let text = String::from_utf8_lossy(&bytes);
        let clipped: String = text.chars().filter(|c| !c.is_control()).take(200).collect();
        if !clipped.is_empty() {
            words.push_str(": ");
            words.push_str(&clipped);
        }
    }
    words
}

/// Lean's decoded answer to one outcome frame, through the pinned Host's
/// `inspect outcome` helper; Rust never decodes the outcome codec itself.
fn inspect_outcome(
    operator: &PrivateOperator,
    directory: &Path,
    payload: &[u8],
    deadline: Instant,
) -> io::Result<Value> {
    let input = write_new(directory, "outcome.bin", payload)?;
    let inspected =
        operator.tool_until("inspect", "outcome", &input, &directory.join("outcome.json"), deadline)?;
    Ok(serde_json::from_slice(&inspected)?)
}

fn outcome_words(view: &Value) -> String {
    let kind = view.get("type").and_then(Value::as_str).unwrap_or("?");
    match view.get("reason").and_then(Value::as_str) {
        Some(reason) => format!("{kind} {reason}"),
        None => kind.to_owned(),
    }
}

fn receipt_fields(view: &Value) -> Value {
    json!({"transactionId":view.get("transactionId"),"eventId":view.get("eventId"),
        "acceptedCount":view.get("acceptedCount"),"worldRoot":view.get("worldRoot")})
}

/// One receipt-only op35 lookup of the exact retained ingress, in its own
/// fresh directory under the attempt. `Ok(Some(view))` is Lean's decoded
/// answer; `Ok(None)` means no usable answer (lost reply, 255, refused).
fn lookup(operator: &PrivateOperator, attempt_dir: &Path, ingress: &[u8]) -> io::Result<Option<Value>> {
    let deadline = Instant::now() + LOOKUP_DEADLINE;
    let mut nonce = [0u8; 16];
    File::open("/dev/urandom").ctx("open", &"/dev/urandom")?.read_exact(&mut nonce)?;
    let directory = attempt_dir.join(format!("op35-lookup-{}", hex(&nonce)));
    fs::DirBuilder::new().mode(0o700).create(&directory)?;
    let reply = match operator.invoke_until(crate::host_operations::APPLICATION_DISPATCH_LOOKUP, ingress, deadline) {
        Ok(reply) => reply,
        Err(error) => {
            note(&directory, &format!("op35 transport: {error}"))?;
            return Ok(None);
        }
    };
    write_new(&directory, "frame.bin", &reply)?;
    let Ok(payload) = framed_payload("dispatch lookup", &reply, crate::host_operations::APPLICATION_DISPATCH_LOOKUP, OUTCOME_TAG) else {
        note(&directory, "op35 reply was not an op35 outcome frame")?;
        return Ok(None);
    };
    let view = inspect_outcome(operator, &directory, payload, deadline)?;
    match view.get("type").and_then(Value::as_str) {
        Some("absent") => Ok(Some(view)),
        Some("confirmed") if view.get("confirmation").and_then(Value::as_str) == Some("replayed") => {
            Ok(Some(view))
        }
        _ => Ok(None),
    }
}

fn note(directory: &Path, text: &str) -> io::Result<()> {
    let mut file = OpenOptions::new()
        .write(true)
        .create_new(true)
        .mode(0o600)
        .custom_flags(libc::O_NOFOLLOW)
        .open(directory.join("note.txt")).ctx("open", &(directory.join("note.txt")))?;
    file.write_all(text.as_bytes())?;
    Ok(())
}

/// The reply op34/164 gave, as far as the transport saw it.
pub(crate) enum Reply<'a> {
    /// A whole frame the transport admitted: the operation's own outcome (34),
    /// NO_RECORD (253, decided no-append) or HOST_OUTCOME (255, undecided).
    Frame(&'a [u8]),
    /// No frame: write/read failure, deadline, EOF, or a refused frame shape.
    Lost,
}

/// Decide one call that did not yield a committed permit, from Lean's
/// answers, and settle it when Lean decided it. Returns what the member is
/// told. Never resubmits and never authorizes delivery.
pub(crate) fn decide(
    operator: &PrivateOperator,
    active: &Path,
    expected: &[u8],
    operation_id: &str,
    ingress: &[u8],
    reply: Reply<'_>,
) -> DispatchOutcome {
    let attempt_dir = active.parent().unwrap_or(Path::new("/"));
    let undecided = |lean: Option<String>| DispatchOutcome {
        operation: Some(operation_id.to_owned()),
        status: Status::Uncertain,
        lean,
    };
    let deadline = Instant::now() + LOOKUP_DEADLINE;
    // Lean's own reading of the original frame, when there was one, and the
    // marker it came under.
    let (marker, original) = match &reply {
        Reply::Frame(frame) => {
            let payload = framed_payload("dispatch submit", frame, crate::host_operations::APPLICATION_DISPATCH_SUBMIT, OUTCOME_TAG)
                .or_else(|_| framed_payload("dispatch outcome", frame, RESPONSE_NO_RECORD, OUTCOME_TAG))
                .or_else(|_| framed_payload("dispatch outcome", frame, RESPONSE_HOST_OUTCOME, OUTCOME_TAG));
            let view = match payload {
                Ok(payload) => {
                    let directory = attempt_dir.join("submit-outcome");
                    match fs::DirBuilder::new()
                        .mode(0o700)
                        .create(&directory)
                        .and_then(|()| inspect_outcome(operator, &directory, payload, deadline))
                    {
                        Ok(view) => Some(view),
                        Err(error) => {
                            eprintln!("spk-host: op{operation_id} outcome inspection failed: {error}");
                            None
                        }
                    }
                }
                Err(error) => {
                    eprintln!("spk-host: op{operation_id} reply frame is no dispatch outcome: {error}");
                    None
                }
            };
            (frame.get(4).copied(), view)
        }
        Reply::Lost => (None, None),
    };
    let lean = original.as_ref().map(outcome_words);
    // NO_RECORD is Lean's positive no-append frame (Host/RequestRefusal.lean
    // `returnedMarker_noRecord_sound`: the payload is a refused, contention or
    // unavailable outcome decided before any append). The call settles on it
    // without a lookup. HOST_OUTCOME is the undecided envelope: it says
    // nothing about the record, so below it counts as no answer at all.
    if marker == Some(RESPONSE_NO_RECORD) {
        let status = match original.as_ref().and_then(|view| view.get("type")).and_then(Value::as_str) {
            Some("contention") => Status::Contention,
            Some("refused") => Status::Refused,
            // Unavailable, or a payload this host could not inspect: the marker
            // alone proves no record; the member authors a new request.
            _ => Status::Unavailable,
        };
        let resolution = json!({"protocol":"mini-spk-dispatch-resolution-v1",
            "status":"no-record","by":"no-record-marker","original":lean});
        return match settle(active, expected, &resolution) {
            Ok(()) => DispatchOutcome {
                operation: Some(operation_id.to_owned()),
                status,
                lean,
            },
            Err(error) => {
                eprintln!("spk-host: op{operation_id} settlement failed: {error}");
                undecided(lean)
            }
        };
    }
    let answered = marker == Some(34);
    if let Some(view) = &original {
        if view.get("type").and_then(Value::as_str) == Some("confirmed") {
            let resolution = json!({"protocol":"mini-spk-dispatch-resolution-v1",
                "status":"recorded-undelivered","by":"submit-outcome",
                "confirmation":view.get("confirmation"),"receipt":receipt_fields(view)});
            return match settle(active, expected, &resolution) {
                Ok(()) => DispatchOutcome {
                    operation: Some(operation_id.to_owned()),
                    status: Status::RecordedUndelivered,
                    lean,
                },
                Err(error) => {
                    eprintln!("spk-host: op{operation_id} settlement failed: {error}");
                    undecided(lean)
                }
            };
        }
    }
    let looked = match lookup(operator, attempt_dir, ingress) {
        Ok(looked) => looked,
        Err(error) => {
            eprintln!("spk-host: op{operation_id} op35 lookup failed: {error}");
            None
        }
    };
    let status = match &looked {
        Some(view) if view.get("type").and_then(Value::as_str) == Some("confirmed") => {
            let resolution = json!({"protocol":"mini-spk-dispatch-resolution-v1",
                "status":"recorded-undelivered","by":"op35","original":lean,
                "receipt":receipt_fields(view)});
            settle(active, expected, &resolution).map(|()| Status::RecordedUndelivered)
        }
        // Lost reply or the undecided envelope (255), then absent: UNDECIDED
        // (ruling 2026-10-26). Lean's positive no-append frame is NO_RECORD,
        // settled above without this lookup.
        Some(_) if !answered => Ok(Status::Uncertain),
        Some(_) => {
            // The Host answered this submit with an outcome frame and Lean
            // now holds no record of the exact call.
            let status = match original
                .as_ref()
                .and_then(|view| view.get("type"))
                .and_then(Value::as_str)
            {
                Some("contention") => Status::Contention,
                Some("refused") => Status::Refused,
                // Unavailable, uncertain or uninspectable, then absent.
                _ => Status::Unavailable,
            };
            let resolution = json!({"protocol":"mini-spk-dispatch-resolution-v1",
                "status":"no-record","by":"op35-absent-after-reply","original":lean});
            settle(active, expected, &resolution).map(|()| status)
        }
        None => Ok(Status::Uncertain),
    };
    match status {
        Ok(status) => DispatchOutcome {
            operation: Some(operation_id.to_owned()),
            status,
            lean,
        },
        Err(error) => {
            eprintln!("spk-host: op{operation_id} settlement failed: {error}");
            undecided(lean)
        }
    }
}

/// Settle `active` as Lean's positive no-record refusal (op164 frame
/// `DREGG/APPLICATION/DISPATCH-NO-RECORD-REFUSAL/v1`).
pub(crate) fn no_record(
    active: &Path,
    expected: &[u8],
    operation_id: &str,
) -> io::Result<DispatchOutcome> {
    let resolution = json!({"protocol":"mini-spk-dispatch-resolution-v1",
        "status":"no-record","by":"no-record-frame"});
    settle(active, expected, &resolution)?;
    Ok(DispatchOutcome {
        operation: Some(operation_id.to_owned()),
        status: Status::Refused,
        lean: Some("no-record refusal".into()),
    })
}

/// Before a new call: try to settle the oldest undecided call with one op35
/// lookup, bound the journal's evidence, and refuse the new call only when
/// `MAX_UNDECIDED` calls remain undecided. Calls whose permit was committed
/// (`committed-payload.bin`) belong to hostd's delivery journal and are not
/// looked up here; they still count toward the bound.
pub(crate) fn admit_new_call(operator: &PrivateOperator, parent: &Path) -> io::Result<()> {
    let mut scanned = scan(parent)?;
    let oldest = scanned
        .iter()
        .position(|attempt| attempt.undecided && !attempt.path.join("committed-payload.bin").exists());
    if let Some(index) = oldest {
        let oldest = &mut scanned[index];
        if let Err(error) = settle_retained(operator, &oldest.path) {
            eprintln!(
                "spk-host: undecided dispatch {} not settled: {error}",
                oldest.path.display()
            );
        }
        // Only this attempt can have changed state since the scan.
        oldest.undecided = present(&oldest.path.join(SUBMIT_ACTIVE))?;
    }
    collect_scanned(&scanned)?;
    if scanned.iter().filter(|attempt| attempt.undecided).count() >= MAX_UNDECIDED {
        return Err(DispatchOutcome {
            operation: None,
            status: Status::Backlog,
            lean: None,
        }
        .into_error());
    }
    Ok(())
}

/// Look up one retained undecided call; settle it on `confirmed`, or on
/// `absent` only when its submit was answered (`op<N>-frame.bin` retained).
fn settle_retained(operator: &PrivateOperator, attempt_dir: &Path) -> io::Result<()> {
    let active = attempt_dir.join(SUBMIT_ACTIVE);
    let expected = retained(&active, MAX_MARKER)?;
    let marker: Value = serde_json::from_slice(&expected)?;
    let ingress = retained(&attempt_dir.join("ingress.bin"), MAX_FRAME)?;
    if marker.get("ingressSha256").and_then(Value::as_str) != Some(&hex(&Sha256::digest(&ingress))) {
        return Err(invalid("retained dispatch ingress differs from its submit marker"));
    }
    let opcode = marker
        .get("submitOpcode")
        .and_then(Value::as_u64)
        .ok_or_else(|| invalid("dispatch submit marker lacks opcode"))?;
    let answered = present(&attempt_dir.join(format!("op{opcode}-frame.bin")))?;
    let Some(view) = lookup(operator, attempt_dir, &ingress)? else {
        return Ok(());
    };
    let resolution = match view.get("type").and_then(Value::as_str) {
        Some("confirmed") => json!({"protocol":"mini-spk-dispatch-resolution-v1",
            "status":"recorded-undelivered","by":"op35-sweep","receipt":receipt_fields(&view)}),
        // Lost reply, then absent: undecided (ruling 2026-10-26).
        Some("absent") if answered => json!({"protocol":"mini-spk-dispatch-resolution-v1",
            "status":"no-record","by":"op35-sweep-absent-after-reply"}),
        _ => return Ok(()),
    };
    settle(&active, &expected, &resolution)
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::fs::DirBuilder;
    use std::time::{SystemTime, UNIX_EPOCH};

    struct Root(PathBuf);
    impl Root {
        fn new() -> Self {
            let nonce = SystemTime::now().duration_since(UNIX_EPOCH).unwrap().as_nanos();
            let path = std::env::temp_dir().join(format!("dispatch-fence-{}-{nonce}", std::process::id()));
            DirBuilder::new().mode(0o700).create(&path).unwrap();
            Self(path)
        }
        fn attempt(&self, number: u64) -> PathBuf {
            let path = self.0.join(format!("dispatch-op-{number}"));
            DirBuilder::new().mode(0o700).create(&path).unwrap();
            path
        }
    }
    impl Drop for Root {
        fn drop(&mut self) {
            let _ = fs::remove_dir_all(&self.0);
        }
    }

    #[test]
    fn fence_markers_are_per_call_and_settlement_strips_bodies() {
        let root = Root::new();
        let a = root.attempt(1);
        write_new(&a, "request.json", b"{\"body\":\"secret\"}").unwrap();
        write_new(&a, "inspection.json.stderr", b"refusal reason").unwrap();
        let active = arm(&a, b"marker-a").unwrap();
        // A second arm of the same attempt refuses: it can never be resent.
        assert!(arm(&a, b"marker-a").is_err());
        let b = root.attempt(2);
        arm(&b, b"marker-b").unwrap();
        assert_eq!(undecided(&root.0).unwrap(), vec![a.clone(), b.clone()]);
        // No journal-wide marker exists for B to wait on.
        assert!(!root.0.join("native-dispatch-active.json").exists());
        assert!(settle(&active, b"other", &json!({})).is_err());
        settle(&active, b"marker-a", &json!({"status":"no-record"})).unwrap();
        assert_eq!(undecided(&root.0).unwrap(), vec![b.clone()]);
        assert!(a.join(SUBMIT_REQUESTED).exists());
        assert!(a.join(RESOLUTION).exists());
        assert!(!a.join("request.json").exists());
        assert!(a.join("inspection.json.stderr").exists());
        assert!(arm(&a, b"marker-a").is_err());
    }

    #[test]
    fn collection_bounds_settled_and_never_touches_undecided() {
        let root = Root::new();
        // hostd tombstone files share the prefix and are never collected.
        fs::write(root.0.join("dispatch-op-abc.json"), b"{}").unwrap();
        let unsubmitted = root.attempt(1);
        write_new(&unsubmitted, "request.json", b"x").unwrap();
        write_new(&unsubmitted, "op36-refused-frame.bin", b"refusal").unwrap();
        write_new(&unsubmitted, "request.bin.stderr", b"reason").unwrap();
        let open = root.attempt(2);
        write_new(&open, "ingress.bin", b"ingress").unwrap();
        arm(&open, b"m").unwrap();
        for number in 3..(3 + MAX_SETTLED as u64 + 5) {
            let path = root.attempt(number);
            write_new(&path, "inspection.json", b"big").unwrap();
            let active = arm(&path, b"m").unwrap();
            settle(&active, b"m", &json!({})).unwrap();
        }
        collect(&root.0).unwrap();
        // The unsubmitted attempt is the oldest: past the cap, it went.
        assert!(!unsubmitted.exists());
        assert!(open.join("ingress.bin").exists());
        assert!(open.join(SUBMIT_ACTIVE).exists());
        assert!(root.0.join("dispatch-op-abc.json").exists());
        let settled: Vec<_> = attempts(&root.0)
            .unwrap()
            .into_iter()
            .filter(|(_, path)| !path.join(SUBMIT_ACTIVE).exists())
            .collect();
        assert_eq!(settled.len(), MAX_SETTLED);
        // The oldest settled attempts went first.
        assert!(!root.0.join("dispatch-op-3").exists());
        assert!(root.0.join(format!("dispatch-op-{}", 2 + MAX_SETTLED as u64 + 5)).exists());
    }

    #[test]
    fn outcome_response_names_status_record_and_exact_retry() {
        let outcome = DispatchOutcome {
            operation: Some("41".into()),
            status: Status::Contention,
            lean: Some("contention".into()),
        };
        let error = outcome.clone().into_error();
        assert_eq!(DispatchOutcome::of(&error), Some(&outcome));
        let text = String::from_utf8(outcome.http_response(false)).unwrap();
        assert!(text.starts_with("HTTP/1.1 503 "));
        assert!(text.contains("Retry-After: 1\r\n"));
        assert!(text.contains("\"status\":\"contention\""));
        assert!(text.contains("\"recorded\":\"no\""));
        assert!(text.contains("\"retry\":\"new-request\""));
        assert!(text.contains("\"operation\":\"41\""));
        let refused = DispatchOutcome {
            operation: None,
            status: Status::Refused,
            lean: None,
        };
        let head = String::from_utf8(refused.http_response(true)).unwrap();
        assert!(head.starts_with("HTTP/1.1 403 "));
        assert!(head.ends_with("\r\n\r\n"));
        let backlog = DispatchOutcome {
            operation: None,
            status: Status::Backlog,
            lean: None,
        };
        assert!(String::from_utf8(backlog.http_response(false))
            .unwrap()
            .contains("\"retry\":\"later\""));
        assert_eq!(attempt_number("dispatch-op-12"), Some(12));
        assert_eq!(attempt_number("dispatch-op-12.json"), None);
        assert_eq!(attempt_number("agent-dispatch-op-12"), None);
        assert_eq!(attempt_number("dispatch-op-"), None);
    }

    use crate::grain_export::tests::FakeHost;

    /// One armed call as `submit_once` leaves it: the exact ingress, the
    /// marker naming its digest, and (when the Host answered) its frame.
    fn armed(journal: &Path, number: u64, frame: Option<&[u8]>) -> (PathBuf, Vec<u8>, Vec<u8>) {
        let attempt = journal.join(format!("dispatch-op-{number}"));
        DirBuilder::new().mode(0o700).create(&attempt).unwrap();
        let ingress = format!("ingress {number}").into_bytes();
        write_new(&attempt, "ingress.bin", &ingress).unwrap();
        let marker = serde_json::to_vec(&json!({"protocol":"mini-spk-dispatch-submit-requested-v1",
            "operationId":number.to_string(),"ingressSha256":hex(&Sha256::digest(&ingress)),
            "submitOpcode":34,"submissionSha256":"0".repeat(64)}))
        .unwrap();
        let active = arm(&attempt, &marker).unwrap();
        if let Some(frame) = frame {
            write_new(&attempt, "op34-frame.bin", frame).unwrap();
        }
        (active, marker, ingress)
    }

    fn outcome_frame(opcode: u8, word: &str) -> Vec<u8> {
        let mut body = vec![opcode];
        body.extend_from_slice(OUTCOME_TAG);
        body.extend_from_slice(word.as_bytes());
        let mut frame = (body.len() as u32).to_le_bytes().to_vec();
        frame.extend_from_slice(&body);
        frame
    }

    /// Lean's NO_RECORD frame (253) settles the call by itself: no lookup,
    /// and the member is told the decided class it carries.
    #[test]
    fn decide_no_record_marker_settles_without_lookup() {
        // Lean's words are `type reason`; the fake inspector gives `refused` a reason.
        for (word, status, words) in [
            ("contention", Status::Contention, "contention"),
            ("refused", Status::Refused, "refused operationRejected"),
            ("unavailable", Status::Unavailable, "unavailable"),
        ] {
            let fake = FakeHost::new(&format!("fence-no-record-{word}"));
            let frame = outcome_frame(RESPONSE_NO_RECORD, word);
            let (active, marker, ingress) = armed(&fake.root, 1, Some(&frame));
            // No reply is scripted: a lookup would find the socket refusing.
            assert!(fake.serve(vec![]).join().unwrap().is_empty());
            let outcome = decide(&fake.operator, &active, &marker, "1", &ingress, Reply::Frame(&frame));
            assert_eq!(outcome.status, status, "{word}");
            assert_eq!(outcome.lean.as_deref(), Some(words));
            assert!(!active.exists(), "{word}: settled on the frame");
            assert!(!fake.root.join("dispatch-op-1").read_dir().unwrap().any(|e| {
                e.unwrap().file_name().to_string_lossy().starts_with("op35-lookup-")
            }), "{word}: no op35 lookup");
            let resolution: Value =
                serde_json::from_slice(&fs::read(fake.root.join("dispatch-op-1").join(RESOLUTION)).unwrap()).unwrap();
            assert_eq!(resolution["status"], "no-record");
            assert_eq!(resolution["by"], "no-record-marker");
            let body = String::from_utf8(outcome.http_response(false)).unwrap();
            assert!(body.contains(&format!("\"status\":\"{word}\"")), "{body}");
            assert!(body.contains("\"recorded\":\"no\""), "{body}");
            assert!(body.contains("\"retry\":\"new-request\""), "{body}");
        }
    }

    /// HOST_OUTCOME (255) is the undecided envelope: inspected and followed by
    /// `absent`, the call stays undecided with the same-call retry.
    #[test]
    fn decide_host_outcome_marker_stays_undecided_after_absent() {
        let fake = FakeHost::new("fence-host-outcome");
        let frame = outcome_frame(RESPONSE_HOST_OUTCOME, "uncertain");
        let (active, marker, ingress) = armed(&fake.root, 1, Some(&frame));
        let served = fake.serve(vec!["absent"]);
        let outcome = decide(&fake.operator, &active, &marker, "1", &ingress, Reply::Frame(&frame));
        assert_eq!(outcome.status, Status::Uncertain);
        assert_eq!(outcome.lean.as_deref(), Some("uncertain"));
        assert_eq!(served.join().unwrap(), vec![(35, ingress)]);
        assert!(active.exists());
        let body = String::from_utf8(outcome.http_response(false)).unwrap();
        assert!(body.contains("\"status\":\"undecided\""), "{body}");
        assert!(body.contains("\"retry\":\"same-call\""), "{body}");
        assert!(body.contains("\"recorded\":\"unknown\""), "{body}");
    }

    /// Before submit (ops 36/37, append-free by the registry), a reply under
    /// either marker is the refusal it carries; nothing was recorded.
    #[test]
    fn refused_before_submit_reads_both_markers_as_the_refusal() {
        for op in [36u8, 37] {
            assert!(crate::host_operations::NO_APPEND_OPERATIONS.contains(&op), "op{op} is append-free");
        }
        for marker in [RESPONSE_NO_RECORD, RESPONSE_HOST_OUTCOME] {
            let fake = FakeHost::new(&format!("fence-before-submit-{marker}"));
            // The operator's pin is its socket; bind it, serve nothing.
            assert!(fake.serve(vec![]).join().unwrap().is_empty());
            let attempt = fake.root.join("dispatch-op-1");
            DirBuilder::new().mode(0o700).create(&attempt).unwrap();
            let frame = outcome_frame(marker, "refused");
            let error = refused_before_submit(&fake.operator, &attempt, "1", crate::host_operations::APPLICATION_DISPATCH_PLAN, &frame);
            let outcome = DispatchOutcome::of(&error).unwrap();
            assert_eq!(outcome.status, Status::Refused, "marker {marker}");
            assert_eq!(outcome.lean.as_deref(), Some("op36 refused operationRejected"));
        }
    }

    /// The transport admits the Host's two response markers for any operation
    /// and still refuses a stray opcode.
    #[test]
    fn invoke_admits_both_response_markers_and_refuses_a_stray_opcode() {
        let fake = FakeHost::new("fence-markers");
        let served = fake.serve_marked(vec![
            (Some(RESPONSE_NO_RECORD), "contention"),
            (Some(RESPONSE_HOST_OUTCOME), "uncertain"),
            (Some(7), "refused"),
        ]);
        let deadline = || Instant::now() + Duration::from_secs(10);
        let no_record = fake.operator.invoke_until(crate::host_operations::APPLICATION_DISPATCH_SUBMIT, b"submit", deadline()).unwrap();
        assert_eq!(no_record[4], RESPONSE_NO_RECORD);
        let undecided = fake.operator.invoke_until(crate::host_operations::APPLICATION_DISPATCH_PLAN, b"plan", deadline()).unwrap();
        assert_eq!(undecided[4], RESPONSE_HOST_OUTCOME);
        let stray = fake.operator.invoke_until(crate::host_operations::APPLICATION_DISPATCH_SUBMIT, b"submit", deadline()).unwrap_err();
        assert_eq!(stray.to_string(), "Mini operator reply opcode mismatch");
        let opcodes: Vec<u8> = served.join().unwrap().into_iter().map(|(op, _)| op).collect();
        assert_eq!(opcodes, vec![34, 36, 34]);
    }

    /// Answered `contention` under op 34's own frame, then op35 `absent`: Lean
    /// holds no record of this call, so it settles and the member is told contention.
    #[test]
    fn decide_answered_contention_then_absent_settles_no_record() {
        let fake = FakeHost::new("fence-contention");
        let frame = outcome_frame(crate::host_operations::APPLICATION_DISPATCH_SUBMIT, "contention");
        let (active, marker, ingress) = armed(&fake.root, 1, Some(&frame));
        let served = fake.serve(vec!["absent"]);
        let outcome = decide(&fake.operator, &active, &marker, "1", &ingress, Reply::Frame(&frame));
        assert_eq!(outcome.status, Status::Contention);
        assert_eq!(served.join().unwrap(), vec![(35, ingress)]);
        assert!(!active.exists());
        let resolution: Value =
            serde_json::from_slice(&fs::read(fake.root.join("dispatch-op-1").join(RESOLUTION)).unwrap()).unwrap();
        assert_eq!(resolution["status"], "no-record");
    }

    /// A lost reply then `absent` stays UNDECIDED (ruling 2026-10-26: no
    /// positive no-append frame yet), with the same-call retry named; a lost
    /// reply then `confirmed replayed` is recorded-undelivered. An
    /// unanswerable lookup settles nothing.
    #[test]
    fn decide_lost_reply_settles_only_on_a_confirmed_lookup() {
        let fake = FakeHost::new("fence-lost");
        let (active, marker, ingress) = armed(&fake.root, 1, None);
        let (other, other_marker, other_ingress) = armed(&fake.root, 2, None);
        let served = fake.serve(vec!["absent", "replayed"]);
        let first = decide(&fake.operator, &active, &marker, "1", &ingress, Reply::Lost);
        assert_eq!(first.status, Status::Uncertain);
        assert!(active.exists());
        let body = String::from_utf8(first.http_response(false)).unwrap();
        assert!(body.contains("\"status\":\"undecided\""));
        assert!(body.contains("\"retry\":\"same-call\""));
        assert!(body.contains("\"recorded\":\"unknown\""));
        let second = decide(&fake.operator, &other, &other_marker, "2", &other_ingress, Reply::Lost);
        assert_eq!(second.status, Status::RecordedUndelivered);
        assert!(!other.exists());
        assert_eq!(served.join().unwrap().len(), 2);
        // With no operator socket the lookup cannot be answered.
        let (third, third_marker, third_ingress) = armed(&fake.root, 3, None);
        let undecided_call = decide(&fake.operator, &third, &third_marker, "3", &third_ingress, Reply::Lost);
        assert_eq!(undecided_call.status, Status::Uncertain);
        assert!(third.exists());
    }

    /// Calls whose permit was committed belong to hostd's delivery journal: no lookup is made for
    /// them, they count toward the bound, and a settled attempt is stripped by the same single pass.
    #[test]
    fn admit_new_call_counts_committed_calls_without_a_lookup_and_strips_settled_ones() {
        let fake = FakeHost::new("fence-committed");
        for number in 1..MAX_UNDECIDED as u64 {
            let (active, _, _) = armed(&fake.root, number, None);
            write_new(active.parent().unwrap(), "committed-payload.bin", b"permit").unwrap();
        }
        let settled = fake.root.join("dispatch-op-100");
        DirBuilder::new().mode(0o700).create(&settled).unwrap();
        write_new(&settled, "request.json", b"scratch").unwrap();
        write_new(&settled, "op36-refused-frame.bin", b"refusal").unwrap();
        admit_new_call(&fake.operator, &fake.root).unwrap();
        assert!(!settled.join("request.json").exists());
        assert!(settled.join("op36-refused-frame.bin").exists());
        let (active, _, _) = armed(&fake.root, MAX_UNDECIDED as u64, None);
        write_new(active.parent().unwrap(), "committed-payload.bin", b"permit").unwrap();
        let refused = admit_new_call(&fake.operator, &fake.root).unwrap_err();
        assert_eq!(DispatchOutcome::of(&refused).unwrap().status, Status::Backlog);
        assert_eq!(undecided(&fake.root).unwrap().len(), MAX_UNDECIDED);
    }

    /// Below the bound a new call is admitted beside undecided ones; at the
    /// bound it is refused until a lookup settles the oldest.
    #[test]
    fn admit_new_call_refuses_only_at_the_undecided_bound() {
        let fake = FakeHost::new("fence-bound");
        for number in 1..MAX_UNDECIDED as u64 {
            armed(&fake.root, number, None);
        }
        // The first sweep's lookup goes unanswered (refused), so nothing settles.
        let served = fake.serve(vec!["refused", "refused", "replayed"]);
        admit_new_call(&fake.operator, &fake.root).unwrap();
        armed(&fake.root, MAX_UNDECIDED as u64, None);
        let refused = admit_new_call(&fake.operator, &fake.root).unwrap_err();
        assert_eq!(DispatchOutcome::of(&refused).unwrap().status, Status::Backlog);
        admit_new_call(&fake.operator, &fake.root).unwrap();
        assert!(!fake.root.join("dispatch-op-1").join(SUBMIT_ACTIVE).exists());
        assert_eq!(undecided(&fake.root).unwrap().len(), MAX_UNDECIDED - 1);
        assert!(served.join().unwrap().iter().all(|(opcode, _)| *opcode == 35));
    }
}
