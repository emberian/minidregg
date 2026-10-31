use ed25519_dalek::{Signer, SigningKey};
use serde_json::{json, Value};
use sha2::Digest;
use std::env;
use std::ffi::{OsStr, OsString};
use std::fs::{self, File, OpenOptions};
use std::io::{self, Read, Write};
use std::path::{Path, PathBuf};
use std::process::{Command, ExitCode, Output};
use std::sync::atomic::{AtomicBool, AtomicU8, Ordering};
use std::sync::{Mutex, OnceLock};
use std::time::{SystemTime, UNIX_EPOCH};

#[cfg(unix)]
mod app_interface;
mod attempt_state;
mod bounds;
mod fsio;
pub(crate) use fsio::{copy_new, create_private, create_public, read_secret, retain_json, sync_directory_ancestors};
#[cfg(unix)]
mod agent_lifetime_grant;
mod trace;
#[cfg(unix)]
mod capture;
#[cfg(unix)]
mod key_rotation;
#[cfg(unix)]
mod key_adoption;
#[cfg(unix)]
mod agent_payer;
#[cfg(unix)]
mod operator_peer;
#[cfg(unix)]
mod agent_reserve;
#[cfg(unix)]
mod current_birth;
#[cfg(unix)]
mod fleet;
#[cfg(unix)]
mod apps;
#[cfg(unix)]
mod append_proof;
#[cfg(unix)]
mod fleet_sign;
#[cfg(unix)]
mod objective_invoke;
#[cfg(unix)]
mod grain_share_issue;
mod hiding;
#[cfg(unix)]
mod historical_call_receipt;
#[cfg(unix)]
mod meter;
#[cfg(unix)]
mod market;
mod checkpoint;
mod world_export;
#[cfg(unix)]
mod clock;
mod participant_enrollment;
mod pay_refill;
#[cfg(unix)]
mod pay;
#[cfg(unix)]
mod participant_namespace;
#[cfg(unix)]
mod participant_provisioning;
#[cfg(unix)]
mod prepare_refusal;
#[cfg(unix)]
mod query_refusal;
#[cfg(unix)]
mod provider_continuity;
mod replan;
#[cfg(unix)]
mod proxy;
#[cfg(unix)]
mod public_proxy;
#[cfg(unix)]
mod operator_drain;
#[cfg(unix)]
mod scheduled_transport;
#[path = "../../hybrid_kem.rs"]
mod hybrid_kem;
// Shared with private-backend; only the sealed-snapshot primitive is used here.
#[allow(dead_code)]
#[path = "../../pinned_execution.rs"]
mod pinned_execution;
#[cfg(unix)]
#[path = "../../crypto_transit.rs"]
mod crypto_transit;
#[cfg(unix)]
mod pq_mailbox;
#[cfg(unix)]
mod cohort_tcp;
#[cfg(unix)]
mod selected_exchange;
#[cfg(unix)]
mod selected_publisher;
#[cfg(unix)]
mod selected_release;
#[cfg(unix)]
mod session_enrollment;
#[cfg(unix)]
mod render;
#[cfg(unix)]
mod share_issue;
#[cfg(unix)]
mod share_issue_receipt;
#[cfg(unix)]
mod join_solana;
#[cfg(unix)]
mod join_solana_v2;
#[cfg(unix)]
mod pay_memo_v2;
mod pay_status;
#[cfg(unix)]
mod pay_claim;
#[cfg(unix)]
mod paid_context;
mod paid_onboarding;
#[cfg(unix)]
mod enrollment_bootstrap;
#[cfg(unix)]
mod chat;
#[cfg(unix)]
mod hermes;
#[cfg(unix)]
mod hermes_handoff;
mod room_schema;
#[cfg(unix)]
mod credit;
#[cfg(unix)]
mod story;
#[cfg(unix)]
mod keys;
#[cfg(unix)]
mod job;
mod activity;
#[cfg(unix)]
mod private_compute;
mod bend;
mod seat;
#[cfg(unix)]
mod shell;
mod shell_grammar;
#[cfg(unix)]
mod member;
#[cfg(unix)]
mod serve_queue;
mod transport;
#[cfg(unix)]
mod worker;
#[cfg(unix)]
mod web;
#[cfg(unix)]
mod receipt_continuity;
#[cfg(unix)]
mod client_consent;
#[cfg(unix)]
mod consent_proxy;
mod workspace;
#[cfg(unix)]
#[path="protected_object/object_keys.rs"]
mod object_keys;
#[cfg(unix)]
#[path="protected_object/object_keys_hybrid.rs"]
mod object_keys_hybrid;
#[cfg(unix)]
#[path="protected_object/object_messages.rs"]
mod object_messages;
#[cfg(unix)]
#[path="protected_object/object_cli.rs"]
mod object_cli;
#[cfg(unix)]
#[path="protected_object/object_epoch_cli.rs"]
mod object_epoch_cli;
#[cfg(unix)]
#[path="protected_object/object_epoch_packages.rs"]
mod object_epoch_packages;
#[cfg(unix)]
mod well;
#[cfg(test)]
mod signing_wire_tests;

static SOCKET: OnceLock<PathBuf> = OnceLock::new();
static SSH_IDENTITY: OnceLock<PathBuf> = OnceLock::new();
#[cfg(unix)]
static EXPECTED_HOST_SHA: OnceLock<String> = OnceLock::new();
/// The local Host image a workspace (or an attempt it wrote) pinned at `workspace init`, and the
/// digest it pinned: `host_image_sha256` of that exact path answers the pin instead of re-hashing
/// ~170 MB in every `mini` process. What checks the bytes: `serve` hashes the sealed snapshot it
/// executes (`transport::HostProcess::checked_image`) and the serving Host refuses an envelope that
/// names another digest (`transport::request_from_envelope`, "host image pin mismatch"). So a Host
/// file replaced under an unchanged pin is refused at the next `serve` start, on its first request.
/// `--verify-host` (or MINI_VERIFY_HOST=1) hashes the file anyway and refuses a mismatch here.
#[cfg(unix)]
static WORKSPACE_HOST_PIN: OnceLock<(PathBuf, String)> = OnceLock::new();
static VERIFY_HOST: AtomicBool = AtomicBool::new(false);
static QUIET_WORKER: AtomicBool = AtomicBool::new(false);
/// The exit status a verb chose besides success (1): 3 = the Host refused, 4 = the Host did
/// not decide (M4's shell contract). The highest one set wins.
static EXIT_STATUS: AtomicU8 = AtomicU8::new(0);

fn set_exit(code: u8) {
    EXIT_STATUS.fetch_max(code, Ordering::Relaxed);
}

/// A command's typed ending from retained client custody. This is distinct
/// from a newly received Host verdict: an absent response is never invented.
#[derive(Clone, Debug, PartialEq)]
pub(crate) enum CommandEnding {
    Client(String),
    Refused(String),
    Undecided(String),
}
impl CommandEnding {
    pub(crate) fn render(&self) -> (u8, String) {
        match self {
            Self::Client(message) => (1, format!("error: {message}\n")),
            Self::Refused(message) => (3, format!("refused: {message}\n")),
            Self::Undecided(message) => (4, format!("undecided: {message}\n")),
        }
    }
}
thread_local! {
    static COMMAND_ENDING: std::cell::RefCell<Option<CommandEnding>> = const { std::cell::RefCell::new(None) };
}
pub(crate) fn note_command_ending(ending: CommandEnding) {
    COMMAND_ENDING.with(|slot| *slot.borrow_mut() = Some(ending));
}
pub(crate) fn take_command_ending() -> Option<CommandEnding> {
    COMMAND_ENDING.with(|slot| slot.borrow_mut().take())
}

/// The Host's own verdict on the latest request, retained as data at the point
/// where the Host answered, so a caller (`mini shell`) can tell a Host decision
/// from a client error without reading error prose.
#[derive(Clone, Debug, PartialEq)]
pub(crate) enum HostDecision {
    /// The Host session reply carried an outcome marker (`byte`: `NO_RECORD` 253 or
    /// `HOST_OUTCOME` 255, see [`is_outcome_frame`]; 254 when a caller records a never-forwarded
    /// reply); `encoded` is the rest of the frame (an outcome encoded by the Host's own codec).
    /// `decoded` is the Host's own `inspect outcome` of that frame over the same session, when it
    /// could be asked; the client never decodes the frame itself.
    Frame {
        command: String,
        byte: u8,
        encoded: Vec<u8>,
        decoded: Option<Value>,
    },
    /// The Host returned a decoded outcome whose type is not `confirmed`.
    Outcome(Value),
}

impl HostDecision {
    /// The Host's own decoding of its answer, when there is one.
    pub(crate) fn outcome(&self) -> Option<&Value> {
        match self {
            HostDecision::Frame { decoded, .. } => decoded.as_ref(),
            HostDecision::Outcome(outcome) => Some(outcome),
        }
    }

    /// Whether the Host DECIDED that the request left nothing behind (the refusal class).
    ///
    /// - A frame under `NO_RECORD` (253) is that decision by construction: the Host answers it
    ///   only for an outcome a receiver decided before any append (`refused`, `contention` or
    ///   `unavailable`, never `uncertain`; `Host/RequestRefusal.lean`), so a fresh attempt is safe.
    /// - A frame under `HOST_OUTCOME` (255) is NEVER a refusal, whatever it decodes to: it is the
    ///   envelope of an outcome the Host has not proven no-append (`uncertain`, `unavailable`,
    ///   `contention`, a handler that threw after dispatch). It is undecided: the exact retained
    ///   call is looked up, and nothing licenses a second operation.
    /// - A decoded `refused` that came back as an operation's own answer (not a marker frame) is
    ///   the receiver's decision too.
    ///
    /// Q1 (can a handler commit and then answer?) is answered on the Host side by this split: a
    /// handler that throws after dispatch on an append operation answers under 255.
    pub(crate) fn is_refusal(&self) -> bool {
        match self {
            HostDecision::Frame { byte, .. } => *byte == RESPONSE_NO_RECORD,
            HostDecision::Outcome(outcome) => outcome.get("type").and_then(Value::as_str) == Some("refused"),
        }
    }
}

/// The registry's reply markers, by name (`protocol/host-operations.json`, generated).
pub(crate) use mini_sdk::host_operations::{RESPONSE_HOST_OUTCOME, RESPONSE_NEVER_FORWARDED, RESPONSE_NO_RECORD};

/// Whether a reply's first byte carries a Host outcome to decode: `NO_RECORD` (253, proven
/// no-append: the refusal class) or `HOST_OUTCOME` (255, undecided).
pub(crate) fn is_outcome_frame(byte: u8) -> bool {
    byte == RESPONSE_NO_RECORD || byte == RESPONSE_HOST_OUTCOME
}

/// The Host's decoded outcome type, or `undecoded`.
pub(crate) fn outcome_type(outcome: Option<&Value>) -> &str {
    outcome.and_then(|o| o.get("type")).and_then(Value::as_str).unwrap_or("undecoded")
}

// Request scratch belongs to its caller. Concurrent browser/native views
// must not consume another caller's refusal and change their recovery class.
thread_local! {
    static HOST_DECISION: std::cell::RefCell<Option<HostDecision>> = const { std::cell::RefCell::new(None) };
}

pub(crate) fn note_host_decision(decision: HostDecision) {
    HOST_DECISION.with(|slot| *slot.borrow_mut() = Some(decision));
}

pub(crate) fn take_host_decision() -> Option<HostDecision> {
    HOST_DECISION.with(|slot| slot.borrow_mut().take())
}

/// Who signed the latest observation this process made: what a `bad-signature`
/// refusal needs to ask the Host whether that key is still the subject's
/// current one (`not_current_key_note`). Recorded where the observation is signed.
#[derive(Clone, Debug)]
struct SignerContext {
    host: PathBuf,
    config: PathBuf,
    subject: String,
    public: [u8; 32],
}

thread_local! {
    static SIGNER: std::cell::RefCell<Option<SignerContext>> = const { std::cell::RefCell::new(None) };
}

/// Record the signer of an observation about to be made. Only an intent that
/// names its `subject` in JSON is recorded; a binary intent clears the record,
/// so an older observation's signer is never blamed for a newer refusal.
fn note_signer(host: &Path, config: &Path, intent: &Path, intent_kind: &OsStr, signing: &SigningKey) {
    let subject = (intent_kind != OsStr::new("binary"))
        .then(|| fs::read(intent).ok())
        .flatten()
        .and_then(|bytes| serde_json::from_slice::<Value>(&bytes).ok())
        .and_then(|intent| intent.get("subject").and_then(Value::as_str).map(str::to_owned));
    SIGNER.with(|slot| {
        *slot.borrow_mut() = subject.map(|subject| SignerContext {
            host: host.to_path_buf(),
            config: config.to_path_buf(),
            subject,
            public: signing.verifying_key().to_bytes(),
        });
    });
}

/// The friend-facing name of the refusal a request signed by a key that is not
/// the subject's current one gets. The Host verifies against the subject's
/// CURRENT key, so after a rotation the old key's signature simply does not
/// verify and the Host can only say `bad-signature`. Its key status for the key
/// the client signed with says why: `keyEpoch` is the CURRENT key's epoch
/// (`Kernel.SubjectKeyRotation.status`), `isCurrent` whether the presented key
/// is that key, `isCommittedNext` whether it is the next key not yet adopted.
/// The old key is proved revoked and not current by
/// `Theory.KeyPreRotation.old_key_refused_after_rotation`. A key the Host never
/// enrolled looks the same as a rotated-away one, so the note says what the
/// status shows and does not claim the key was once ours.
fn not_current_key_note(status: &Value) -> Option<String> {
    if status.get("isCurrent").and_then(Value::as_bool) != Some(false) {
        return None;
    }
    let epoch = status.get("keyEpoch").and_then(Value::as_str)?;
    if status.get("isCommittedNext").and_then(Value::as_bool) == Some(true) {
        return Some(format!(
            "\n  this key is the committed NEXT key, not yet adopted (epoch {epoch} is current): \
             rotate to it before signing with it"
        ));
    }
    Some(format!(
        "\n  this key is not the subject's current key (epoch {epoch} is current); if you rotated keys, \
         this one was rotated away: sign with the key you rotated to"
    ))
}

/// For a `bad-signature` refusal of a request this process signed, ask the Host
/// (key status, op 144) whether the signing key is still current, and say so by
/// name if it is not. Best effort: any failure to ask adds nothing.
fn bad_signature_explanation(outcome: &Value) -> String {
    let context = SIGNER.with(|slot| slot.borrow().clone());
    explain_bad_signature(outcome, context.as_ref(), |context| {
        let socket = SOCKET.get()?;
        key_rotation::status_if_enrolled(&context.host, socket, &context.config, &context.subject, &context.public)
            .ok()
            .flatten()
    })
}

/// `bad_signature_explanation` with the Host's key status supplied by the
/// caller: asked only for a `bad-signature` refusal, and only of a recorded signer.
fn explain_bad_signature(
    outcome: &Value,
    signer: Option<&SignerContext>,
    status: impl FnOnce(&SignerContext) -> Option<Value>,
) -> String {
    if outcome.get("reason").and_then(Value::as_str) != Some("bad-signature") {
        return String::new();
    }
    signer
        .and_then(status)
        .and_then(|status| not_current_key_note(&status))
        .unwrap_or_default()
}

/// A refused `doc push`'s diagnosis: which pulled lines changed since the
/// pull (`workspace::stale_lines`). The shell prints it as the refusal's first
/// line, above the Host's own decoding of the same refusal.
thread_local! {
    static LINE_REFUSAL: std::cell::RefCell<Option<String>> = const { std::cell::RefCell::new(None) };
}

pub(crate) fn note_line_refusal(lines: String) {
    LINE_REFUSAL.with(|slot| *slot.borrow_mut() = Some(lines));
}

pub(crate) fn take_line_refusal() -> Option<String> {
    LINE_REFUSAL.with(|slot| slot.borrow_mut().take())
}

/// Exit code for a request the Host refused.
pub(crate) const EXIT_REFUSED: u8 = 3;

/// A hex field of a Host outcome JSON as text, or `hex …` when it is not
/// printable UTF-8.
pub(crate) fn outcome_text(value: Option<&Value>) -> String {
    let Some(hex) = value.and_then(Value::as_str) else {
        return "(absent)".into();
    };
    // A controller's nested `Reject` is printed by Lean's `repr` across lines;
    // line breaks and tabs become single spaces. Any other control character
    // keeps the text out of the terminal: it is shown as hex.
    match mini_sdk::hex::decode(hex).map_err(|e| e.0)
        .ok()
        .and_then(|bytes| String::from_utf8(bytes).ok())
    {
        Some(text)
            if !text
                .chars()
                .any(|c| c.is_control() && !matches!(c, '\n' | '\t')) =>
        {
            text.split_whitespace().collect::<Vec<_>>().join(" ")
        }
        _ => format!("hex {hex}"),
    }
}

/// `refused: <reason>: <text>` for a Host outcome of type `refused`. The
/// reason is the Host's named `RefusalReason`, read from the Host's own
/// decoding; it is never inferred from the text.
pub(crate) fn refusal_line(outcome: &Value) -> Option<String> {
    if outcome.get("type").and_then(Value::as_str) != Some("refused") {
        return None;
    }
    let reason = outcome
        .get("reason")
        .and_then(Value::as_str)
        .unwrap_or("unnamed");
    // A law refusal carries the Host's own rendering of the failing clause.
    if let Some(explain) = outcome.get("explain").and_then(Value::as_str) {
        return Some(format!("refused: {reason}: {explain}"));
    }
    let detail = outcome_text(outcome.get("detail"));
    // The Host's per-subject request rate (`Kernel.SubjectRate`): the detail is
    // `rate-limited retry-after-ms N`; say when the subject may try again.
    if reason == "rate-limited" {
        if let Some(ms) = detail
            .strip_prefix("rate-limited retry-after-ms ")
            .and_then(|n| n.parse::<u64>().ok())
        {
            return Some(format!(
                "refused: rate-limited: this subject has used its request rate for now; retry in {} s (phase {})",
                ms.div_ceil(1000),
                outcome_text(outcome.get("phase"))
            ));
        }
    }
    let hint = refusal_hint(&detail);
    Some(format!(
        "refused: {reason}: {detail} (phase {}){hint}",
        outcome_text(outcome.get("phase"))
    ))
}

/// What to do about a refusal whose name alone does not say (JDISCLOSE row
/// d8). A delegation's `descent` check reads the authority as it
/// stood when the proposal was authored (its root, the issuer and policy
/// epochs, a fresh child id, an unspent nullifier); most often the authority
/// has moved since, and the cure is a new proposal.
fn refusal_hint(detail: &str) -> &'static str {
    if detail.contains("CapabilityDelegationController.Reject.descent") {
        "\n  hint: this delegation was authored against the authority as it stood then; it has moved since \
         (or the proposal was already used). Propose it again under a new ID and submit that."
    } else {
        ""
    }
}

/// The exit code and line `mini` prints for the Host's recorded decision: `refused` (exit 3)
/// only for a decoded refusal; any other decoded type, or a frame the Host could not decode, is
/// `undecided` (exit 4), never a refusal (`HostDecision::is_refusal`). A charged failure is its
/// own line (exit 3: decided, and not done).
pub(crate) fn host_ending(decision: &HostDecision) -> Option<(u8, String)> {
    if decision.is_refusal() {
        return Some((EXIT_REFUSED, match (decision, decision.outcome()) {
            (HostDecision::Frame { command, byte, .. }, outcome) => format!(
                "{}{}\n  Host refused {command} with no record, reply byte {byte}",
                no_record_line(outcome),
                outcome.map(bad_signature_explanation).unwrap_or_default()),
            (HostDecision::Outcome(outcome), _) => format!("{}{}",
                refusal_line(outcome).unwrap_or_else(|| "refused: unnamed".into()), bad_signature_explanation(outcome)),
        }));
    }
    if let Some(line) = decision.outcome().and_then(charged_line) {
        return Some((EXIT_REFUSED, line));
    }
    if matches!(decision, HostDecision::Outcome(_)) && outcome_type(decision.outcome()) == "confirmed" {
        return None; // a confirmation is no Host verdict against the command; the client error stands
    }
    let kind = outcome_type(decision.outcome());
    Some((EXIT_UNDECIDED, match decision {
        HostDecision::Frame { command, byte, .. } => format!(
            "undecided: Host answered {command} with reply byte {byte} and outcome {kind}; the effect is unknown, \
             so do not repeat the operation: look up the exact retained call"),
        HostDecision::Outcome(_) => format!(
            "undecided: Host outcome {kind}; the effect is unknown, so do not repeat the operation: look up the exact retained call"),
    }))
}

/// The line for a `NO_RECORD` (253) frame: the Host decided before any append, so nothing
/// happened and a fresh attempt is safe. A decoded `refused` names its reason; `contention` and
/// `unavailable` say so.
pub(crate) fn no_record_line(outcome: Option<&Value>) -> String {
    match outcome {
        Some(outcome) if outcome_type(Some(outcome)) == "refused" => refusal_line(outcome).unwrap_or_else(|| "refused: unnamed".into()),
        outcome => format!("refused: no record: the Host answered {} before any append; nothing happened, a fresh attempt is safe",
            outcome_type(outcome)),
    }
}

/// The registry's never-forwarded marker (254).
pub(crate) fn host_operations_never_forwarded() -> u8 {
    RESPONSE_NEVER_FORWARDED
}

/// Exit code for a request whose effect is unknown (`mini retry --mode lookup` asks again).
pub(crate) const EXIT_UNDECIDED: u8 = 4;

/// `charged: ...` for a confirmed outcome whose disposition is `charged`: the call is admitted and
/// only its price was posted; nothing else was written (`mini_sdk::custody::Outcome::Charged`).
pub(crate) fn charged_line(outcome: &Value) -> Option<String> {
    match mini_sdk::custody::outcome_of(outcome) {
        mini_sdk::custody::Outcome::Charged { cause, .. } => Some(format!(
            "charged: the Host admitted the call and posted only its price; nothing else was written (cause {})",
            match cause.as_str() { Some(hex) => outcome_text(Some(&Value::String(hex.to_owned()))), None => cause.to_string() })),
        _ => None,
    }
}

/// The identity of one Host image file as the kernel reports it: device, inode,
/// size, and both modification and status-change times. Replacing the file
/// (new inode) or writing it in place (ctime moves, and no caller can set ctime)
/// changes it.
#[cfg(unix)]
type HostImageIdentity = (u64, u64, u64, i64, i64, i64, i64);

/// The SHA-256 of each Host image this process has hashed, with the identity
/// of the file it hashed. A read is several Host requests and each binds the
/// image's digest; the image is ~150 MB, so re-hashing it per request was most
/// of a warm read (COLD-READ, 2026-10-01: 7 requests, ~0.1 s of hashing each).
#[cfg(unix)]
static HOST_IMAGE_SHA256: Mutex<Vec<(PathBuf, HostImageIdentity, String)>> = Mutex::new(Vec::new());

#[cfg(unix)]
fn host_image_identity(metadata: &fs::Metadata) -> HostImageIdentity {
    use std::os::unix::fs::MetadataExt;
    (
        metadata.dev(),
        metadata.ino(),
        metadata.size(),
        metadata.mtime(),
        metadata.mtime_nsec(),
        metadata.ctime(),
        metadata.ctime_nsec(),
    )
}

/// The digest of the selected Host image, hashed once per file identity per
/// process. The identity is read from the open handle, before and after the
/// hash; a file that changed while it was hashed is refused, and a later call
/// that sees a different identity hashes again.
///
/// A remote client has no Host image: its Host is named by an empty path and known only by the digest
/// it pinned, which every v2 envelope carries and the box's socket checks.
#[cfg(unix)]
fn host_image_sha256(host: &Path) -> Result<String> {
    if host.as_os_str().is_empty() {
        return match (SOCKET.get().map(|s| transport::is_remote(s)), EXPECTED_HOST_SHA.get()) {
            (Some(true), Some(sha)) => Ok(sha.clone()),
            (Some(true), None) => Err("a remote workspace must pin the Host SHA-256 (--host-sha256)".into()),
            _ => Err("no Host image: only a remote client (--remote) may omit --host".into()),
        };
    }
    let pinned = WORKSPACE_HOST_PIN.get().filter(|(path, _)| path == host).map(|(_, sha)| sha);
    if let Some(sha) = pinned {
        if !verify_host() {
            return Ok(sha.clone());
        }
    }
    let mut file = File::open(host).map_err(|error| {
        format!(
            "cannot open selected Host image {}: {error}",
            host.display()
        )
    })?;
    let inspect = |file: &File| {
        file.metadata().map_err(|error| {
            format!(
                "cannot inspect selected Host image {}: {error}",
                host.display()
            )
        })
    };
    let metadata = inspect(&file)?;
    if !metadata.is_file() {
        return Err("selected Host image is not a regular file".into());
    }
    let identity = host_image_identity(&metadata);
    let mut cache = HOST_IMAGE_SHA256
        .lock()
        .map_err(|_| "Host image digest cache poisoned".to_owned())?;
    if let Some((_, _, sha)) = cache
        .iter()
        .find(|(path, seen, _)| path == host && *seen == identity)
    {
        return Ok(sha.clone());
    }
    let mut digest = sha2::Sha256::new();
    let mut buffer = [0u8; 64 * 1024];
    loop {
        let count = file.read(&mut buffer).map_err(|error| {
            format!(
                "cannot hash selected Host image {}: {error}",
                host.display()
            )
        })?;
        if count == 0 {
            break;
        }
        digest.update(&buffer[..count]);
    }
    if host_image_identity(&inspect(&file)?) != identity {
        return Err(format!(
            "selected Host image {} changed while it was hashed",
            host.display()
        ));
    }
    let sha = hex(&digest.finalize());
    if pinned.is_some_and(|pin| pin != &sha) {
        return Err(format!(
            "selected Host image {} differs from the workspace's pinned hostSha256",
            host.display()
        ));
    }
    cache.retain(|(path, _, _)| path != host);
    cache.push((host.to_path_buf(), identity, sha.clone()));
    Ok(sha)
}

/// Whether this process hashes a pinned Host image anyway (`mini --verify-host ...`, MINI_VERIFY_HOST=1).
fn verify_host() -> bool {
    VERIFY_HOST.load(Ordering::Relaxed) || env::var_os("MINI_VERIFY_HOST").as_deref() == Some(OsStr::new("1"))
}

/// Pins, for this process, the digest a local workspace (or attempt) recorded for its Host image
/// path at `workspace init`. A second, different pin within one process is refused.
#[cfg(unix)]
pub(crate) fn pin_workspace_host(host: &Path, sha: &str) -> Result<()> {
    if sha.len() != 64 || !mini_sdk::hex::is_lower(sha) {
        return Err("workspace hostSha256 must be 64 lowercase hex digits".into());
    }
    let pin = (host.to_path_buf(), sha.to_owned());
    match WORKSPACE_HOST_PIN.get() {
        Some(existing) if existing != &pin => Err("pinned workspace Host image differs within one process".into()),
        Some(_) => Ok(()),
        None => WORKSPACE_HOST_PIN.set(pin).map_err(|_| "cannot pin the workspace Host image".into()),
    }
}

/// The pin a local attempt manifest records beside its Host path: the workspace's, when one is
/// loaded for that path (so the manifest and the workspace name the same digest), else none.
#[cfg(unix)]
fn workspace_host_pin(host: &Path) -> Option<String> {
    WORKSPACE_HOST_PIN.get().filter(|(path, _)| path == host).map(|(_, sha)| sha.clone())
}

/// The op-8 inspect kinds that read the admitted history (`object-audience`,
/// `object-audience-roster`): the Host session answers these frames from its
/// walked history, and the storeless codec refuses them
/// (`Host.Main.sessionInspectKind`). They travel the same `u16(len) ‖ kind ‖
/// source` framing as codec frames, addressed to the session itself.
#[cfg(unix)]
fn session_inspect_kind(operation: u8, payload: &[u8]) -> bool {
    if operation != mini_sdk::host_operations::INSPECT {
        return false;
    }
    let Some(header) = payload.get(..2).and_then(|bytes| <[u8; 2]>::try_from(bytes).ok()) else {
        return false;
    };
    let width = usize::from(u16::from_le_bytes(header));
    let kind = payload.get(2..2 + width).and_then(|bytes| std::str::from_utf8(bytes).ok());
    matches!(kind, Some("object-audience") | Some("object-audience-roster"))
}

#[cfg(unix)]
fn session_invoke(
    host: &Path,
    socket: &Path,
    config: &Path,
    operation: u8,
    payload: &[u8],
) -> Result<Vec<u8>> {
    if (7..=11).contains(&operation) && !session_inspect_kind(operation, payload) {
        return client_consent::codec_frame(host, config, operation, payload);
    }
    let selected_sha = host_image_sha256(host)?;
    if let Some(sha) = EXPECTED_HOST_SHA.get() {
        if sha != &selected_sha {
            return Err("selected Host image differs from durable worker pin".into());
        }
    }
    transport::invoke_pinned_with_local(host, socket, config, &selected_sha, operation, payload)
}

const USAGE: &str = r#"mini — custody and exact-retry client for minidregg-host

usage:
  mini consent-full-ready --host HOST --config CONFIG.json
  mini [--verify-host] [--remote DEST] COMMAND [options] [--replan-window SECONDS] [--replan-max N]
    --verify-host (or MINI_VERIFY_HOST=1): hash the local Host image even when the workspace pinned
    its hostSha256 at init, and refuse a mismatch before any request.
    --replan-window SECONDS: when a tick, certify or another write lands between an observation and
    its use (the Host's stale-root, or a document append's moved target), mini observes again,
    after a random pause of up to a few of its own attempt times, until SECONDS have passed
    (default 600; MINI_REPLAN_WINDOW when the flag is absent). Each such refusal is the Host's
    proof that another write landed first.
    --replan-max N: an explicit ceiling of N re-plans inside the window (none by default; 0 is a
    single observation; MINI_REPLAN_MAX when the flag is absent).
  mini private-compute --left 0..=255 --right 0..=255   (research demonstration: a local four-party MPC computation, never an admission; needs the mini-private-compute binary beside mini)
  mini keygen --secret KEY --public PUBLIC [--next-to NEXT-KEY | --no-prerotation] [--escrow-to-sponsor @FILE|HEX --escrow-subject SUBJECT]
  mini adopt-next-key --workspace WORKSPACE [--next-key NEXT-KEY] [--attempt CHILD] [--action prepare|submit|lookup]
  mini rotate-key --workspace WORKSPACE --next-key NEXT-KEY [--next-to PATH]
  mini key-status --workspace WORKSPACE [--next-public-key NEXT.pub]
  mini join --key KEY
  mini join --remote DEST --key KEY --sponsor-plan PLAN.json --dir JOIN-ROOT
  mini join --remote DEST --key KEY --welcome WELCOME.json --dir JOIN-ROOT --verifier LOCAL-HOST
  mini shell --remote DEST --workspace JOIN-ROOT/workspace --home SESSION-HOME [--line LINE]
  mini socket-proxy --socket PUBLIC-SOCKET
  mini verify-view --view VIEW.json
  mini key --action cell-blinding --secret KEY --cell CELL [--storage declared|content --heights H1,H2,...]
  mini key --action derive-salt --secret KEY --cell CELL --storage declared|content [--heights H1,H2,...] --entry HEX
  mini workspace --action init|import|list|describe|read|submit|recover|create|propose|publish-delegation --dir WORKSPACE [action options]
  mini workspace --action init ... --continuity-ref '{"name":"account","kind":"account","target":"ID","observeCapability":"CAP"}' [--verifier LOCAL-HOST]
  mini workspace --action onboard --dir WORKSPACE
  mini workspace --action continuity-init --dir WORKSPACE --name REF [--verifier LOCAL-HOST]
  mini workspace --action continuity-verifier --dir WORKSPACE --verifier LOCAL-HOST
  mini workspace --action continuity-carry-authority --dir WORKSPACE --operator-key HEX64
  mini workspace --action continuity-carry-verifier --dir WORKSPACE --verifier ABSOLUTE-PORTABLE-VERIFIER --sha256 HEX64
  mini workspace --action continuity-carry --dir WORKSPACE --edge MANIFEST --source-capsule PATH --new-config CONFIG --new-verifier HOST
  mini workspace --action continuity-check --dir WORKSPACE --attempt RETAINED [--historical true|false]
  mini operation-proof --dir WORKSPACE --operation-record ABSOLUTE-FILE
  mini pay address|status --dir WORKSPACE [--account REF]
  mini pay book --dir OPERATOR-WORKSPACE --source {"control","book":[ADDRESS...],"tariff":{...}|null}.json
  mini pay watch-config --dir OBSERVER-WORKSPACE --out CONFIG.json [--min-endpoints N] [--max-pages N] [--page-size N] [--enrol tariff]
  mini pay observe --dir OBSERVER-WORKSPACE --capability CAP [--enrol-capability C_ENROL --operator-socket OPERATOR-SOCKET] (--from OBSERVATIONS.json|- [--hold true] | --resume ATTEMPT)
  mini pay heartbeat --dir OBSERVER-WORKSPACE --capability CAP --slot SLOT --block-time TIME
  mini bend --action publish --dir WORKSPACE --name NAME --source FILE.obend [--entry DEF] [--account REF]   an Objective Bend, captured and lowered by the Host's front end, then published
  mini bend --action run --dir WORKSPACE --name NAME --object REF [--seed JSON] [--input JSON] [--deposit N] [--state-type JSON] [--account REF]   create REF pinning the bend when it has no record, then birth its activity
  mini bend --action show --dir WORKSPACE --object REF
  mini bend --action lookup|retry --dir WORKSPACE --name NAME   the receipt-only lookup of, or the exact retry of, NAME's last retained attempt
  mini job --action post --dir WORKSPACE --room REF --program ID --input N --price P --deadline SECONDS --account REF [--window SECONDS] [--name NAME]
  mini job --action claim --dir WORKSPACE --job ID --room REF --bond B --account REF [--name NAME]
  mini job --action answer|check|settle|show --dir WORKSPACE --name NAME [--output N --steps N]
  mini job --action list --dir WORKSPACE --room REF
  mini pay audit --dir OBSERVER-WORKSPACE [--offline true] [--operator-socket OPERATOR-SOCKET]
  mini pay refill --mode submit --host HOST --config PINNED-CONFIG.json --socket SOCKET --key OWNER.key --dir NEW-ATTEMPT --subject S --capability C --account A --task T --amount N [--gain G]
  mini join --memo-version v2 --solana --host HOST --config CONFIG --bootstrap-url HTTPS/mini/v2 --enrol ENROL-V2.json --dir NEW-JOIN-DIR [--weeks N --starter-credit N]
  mini join --memo-version v2 --solana ... --key BOX-HELD.key --ssh-public LOGIN.pub [--ssh-signature SSHSIG]   (detached: the first run prints the statement to sign, the second takes the signature)
  mini join --memo-version v2 --renew|--wait --host HOST --config CONFIG --dir JOIN-DIR [--signature TX --key CURRENT-SECRET --next-public NEXT.pub]
  mini pay-claim --action quote --join-dir JOIN --host LOCAL-HOST --config CONFIG --weeks N --starter-credit N --expiry-hour N --nonce N --output ABS.bin [--mode enrol|renew --payment-record ABS.json]
  mini pay-claim --action accept|rotate|lookup (--dir WORKSPACE | --join-dir JOIN) --operation-record ABS-DIR [--command SOURCE.bin --host LOCAL-HOST --config CONFIG --bootstrap-url HTTPS/mini/v2 --payment-record ABS.json --key SECRET]
  mini enrollment-bootstrap --host HOST --config PUBLIC-CONFIG --socket PUBLIC-SOCKET --listen 127.0.0.1:8794 --metadata PUBLIC-BOOTSTRAP.json [--trusted-proxy IP]
  mini enrollment-view --socket SOCKET [--config CONFIG] (--host HOST | --host-sha256 HEX)
  mini join --solana --host HOST --config PINNED-CONFIG.json (--socket SOCKET | --bootstrap-url HTTPS-BASE | --quote QUOTE.json) --enrol ENROL.json --dir NEW-JOIN-DIR [--key MINI.key] [--ssh-key SSH-KEY] [--name NAME] [--weeks N] [--starter-credit N]
  mini join --wait --host HOST --config PINNED-CONFIG.json [--socket SOCKET | --bootstrap-url HTTPS-BASE] --dir JOIN-DIR [--signature TX --key CURRENT-SECRET --next-public NEXT.pub] [--timeout SECONDS] [--interval SECONDS] [--birth-context CONTEXT.json]
  mini join --renew --host HOST --config PINNED-CONFIG.json (--socket SOCKET | --bootstrap-url HTTPS-BASE | --quote QUOTE.json) --enrol ENROL.json --dir JOIN-DIR
  mini pay refill --mode lookup --host HOST --config PINNED-CONFIG.json --socket SOCKET --dir ATTEMPT
  mini enc-public --secret KEY     the hybrid (X25519 + ML-KEM-768) public key, for --escrow-to-sponsor
  mini enc-key-id --secret KEY     its 32-byte id (what whoami prints)
  mini escrow-recover --escrow PUBLIC.escrow --sponsor-secret KEY --subject SUBJECT --secret NEW-KEY
  mini workspace --action init|import|list|describe|read|tail|submit|recover|create|propose|publish-delegation --dir WORKSPACE [action options]
  mini workspace --action room-key --op found|sync|invite|invite-check|transition|rotate|kick|register|rewrap|pin-member|list|open|forget --dir WORKSPACE --name ROOM [op options]
  mini workspace --action room-key --op wrap-atom --dir WORKSPACE --epoch E --gen G --member SUBJECT   (the atom a wrap lands at: Kernel/PrivateRoomKeys.lean wrapAtomId)
      private rooms: DEVNET QUALITY; PRIVACY NOT AUDITED (hybrid X25519 + ML-KEM-768 wraps; docs/PRIVATE-ROOMS-DESIGN.txt)
  mini enroll --action plan --sponsor-workspace WORKSPACE --factory-ref NAME --name REQUEST-LABEL --new-key KEY [--next-public-key KEY.next.pub | --no-prerotation] --dir ATTEMPT [--operator-socket PRIVATE-SOCKET]
  mini web --dir WORKSPACE --listen 127.0.0.1:PORT [--home H]   (loopback hypertext over this workspace's signed reads, with the document edit/create POST forms; the developer's and the journeys' direct face)
  mini --socket SOCKET web --body --listen-fd 3 --dir WORKSPACE --home HOME --host HOST --config CONFIG [--anonymous]   (the web front end's body: stage fragments and verb actions for the gateway, over the inherited listener; mini-web-spawn starts it as the member)
  mini workspace --action doc-show|doc-outline --dir WORKSPACE --name DOC [--format text|raw|json|html]
  mini workspace --action doc-insert|doc-move|doc-remove|mark|unmark|transclude|transclusions|follow|doc-backlinks|doc-links --dir WORKSPACE --name DOC [action options]
  mini enroll --action plan --sponsor-workspace WORKSPACE --factory-ref NAME --name REQUEST-LABEL --new-public-key PUBLIC [--home-subject N] --dir ATTEMPT
  mini enroll --action offer|welcome --dir ATTEMPT [--birth-context CONTEXT.json]
  mini enroll --action possess --dir ATTEMPT --key KEY --subject N --output SIGNATURE.bin
  mini enroll --action seal --dir ATTEMPT [--possession-signature SIGNATURE.bin]
  mini enroll --action submit|lookup --dir ATTEMPT
  mini key --action providers|choose|set|grant|revoke|ls (--dir WORKSPACE | --pool true) [--provider NAME] [--secret FILE|-] [--runner SUBJECT --per-call TOKENS --per-day CALLS --until HEIGHT --model MODEL] [--task TASK] [--broker CLIENT_CONFIG]
  mini shell --socket SOCKET --host HOST --config CONFIG.json --workspace WORKSPACE --home SESSION-HOME [--line LINE]
  mini apps search [--term TEXT] [--category C] [--qualification FILE] [--json]   the Sandstorm app market and recorded lifecycle verdicts
  mini apps show --app APP-ID|PACKAGE-ID [--qualification FILE] [--json]
  mini apps install --app APP-ID|PACKAGE-ID --dir WORKSPACE [--class S|M|L] [--retry REQUEST-ID]   a member turn: birth + delegation, then the worker
  mini apps list|status|open|stop|start|share|export|delete [--grain a<APP>] [--to MEMBER] [--out FILE]   decoded outcomes over the worker socket
  mini apps index-check --in RAW.json --out INDEX.json              the fetcher's validation of the downloaded index
  mini apps bootstrap --dir OPERATOR-WORKSPACE [--budget N] [--tool-ref tool] [--parent-ref parent]   operator, once per world: the metered tasks
  mini apps-front --listen 127.0.0.1:8797 --origins DIR [--domain demo.dregg.online]   the grain entrance behind Caddy
  mini apps-worker --state DIR --world WORLD.json [--member-socket PATH] [--edge-socket PATH] [--member-group G] [--edge-group G]   the operator custodian
  mini fleet --action join --sponsor-workspace WORKSPACE --factory-ref NAME --name LABEL --new-key KEY --enroll-dir ATTEMPT --dir NEW-WORKSPACE --fund AMOUNT [--account-name NAME]
  mini fleet --action send|publish --dir WORKSPACE --account NAME --topic TOPIC (--payload TEXT|--payload-hex HEX) [--to ACCOUNT --amount N [--asset ID]]
  mini fleet --action transfer --dir WORKSPACE --account NAME --to ACCOUNT --amount N [--asset ID]
  mini fleet --action receipt --dir WORKSPACE (--transaction ID|--head-of NAME)
  mini fleet --action lookup --dir WORKSPACE --attempt WORKSPACE/attempts/a-NONCE
  mini fleet --action incoming --dir WORKSPACE --account NAME [--topic TOPIC] [--since HEIGHT] [--limit N]
  mini credit --action balance|room|tariff|pay|topup|renew|status|ledger|install|adopt --dir WORKSPACE [--room REF] … (PLACE §2.10; `mini shell` spells them credit / pay ROOM week / tariff / topup / room status|renew|concierge)
    pay, topup and refund keep one operation record per request (or --operation-record PATH): a rerun
    recovers it and never pays twice; --again true pays once more after a decided one
  mini fleet --action poll --dir WORKSPACE --account NAME --topic TOPIC [--since CURSOR] [--limit N]
  mini fleet --action feed --dir WORKSPACE --accounts NAME[,NAME...] --topic TOPIC   (one topic, several authors: one feed ordered by admission height)
  mini well --action new --dir WORKSPACE --name NAME --in REALM --law LAW.json
  mini well --action mint|burn|floor --dir WORKSPACE --well NAME|ID --account NAME|ID --amount N [--capability ID] [--attempt NEW-DIR] [--again true]
    one attempt chain per request: a rerun reports the retained attempt and authors nothing new
  mini well --action resubmit --dir WORKSPACE --attempt ATTEMPT   (the SAME retained ingress, decoded outcome)
  mini well --action ledger --dir WORKSPACE --output LEDGER.json
  mini fleet-sign join|send|transfer|receipt|incoming|retry [--profile P] ...   (dregg-client-sign's verbs on Mini, plus `incoming` for the helm adapter; `mini fleet-sign --help`)
  mini app-interface --action tools|prepare|call|qualify --declaration FILE [--operation OP --args FILE --context FILE] [--attachment ALIAS --tool NAME --runtime BIN --controller-socket SOCKET --dir NEW_ATTEMPT]
  mini member --dir WORKSPACE [--name REF] [--home H] [--json true|false] [--action workspace|app-status]   (what `home` prints: your resources and exact recovery actions)
  mini clock --action init ... | view|tick --workspace WORKSPACE [--capability CAP]
  mini checkpoint --action view|certify --workspace WORKSPACE [--control CAP --min-tail N]
  mini activity --action submit|quote|resubmit|lookup|view --workspace WORKSPACE [action options]
  mini seat --action submit|resubmit|lookup|view --workspace WORKSPACE [action options]
  mini hermes-handoff --action registration|activation|registry|dispatch [action options]   (Hermes's task registrations and dispatch bundles)
  mini story-law --table TABLE.txt [--player SUBJECT]   (the story law a table of rooms and ways compiles to, printed; installs nothing)
  mini mix --action registrar-key|native-key|key|seal|batch|scan --state DIR [action options]   (the post-quantum mailbox mix)
  mini mix-live --action cover|registrar|relay|mailbox|scan|send|receive --state DIR --generation HEX --origin-ms MS --records DIR [action options]
  mini consent-resident --consent PATH --settings PATH     the resident consent component for this user's `mini` processes
  mini codec-resident --host HOST --settings PATH          the storeless resident codec Host for this user's `mini` processes
  mini selected-exchange --phase prepare|status|publish|receive-transport|verify-transport --contract CONTRACT.json --state-dir PRIVATE-STATE
  mini profile --host HOST --config CONFIG.json [--socket SOCKET]
  mini describe --host HOST --config CONFIG.json [--socket SOCKET]
  mini bootstrap --host HOST --config OPERATOR.json --source GENESIS.json --dir DEPLOYMENT
  mini audit --host HOST --config PINNED.json
  mini store audit --host HOST --config PINNED.json [--receipts FILE]
    re-derive the Store from genesis (chain, tags, accumulator, spent map, checkpoints, head root), then re-admit
    every signed ingress (the audit above); the Host's stdout, stderr and exit status pass through unchanged
  mini author --host HOST --config CONFIG.json --kind KIND --input INPUT.json --output OUTPUT.bin
  mini current-application-intent --host HOST --config CONFIG.json --socket SOCKET --source SOURCE.json --dir NEW-PRIVATE-DIR
  mini current-session-intent --host HOST --config CONFIG.json --socket SOCKET --source SOURCE.json --dir NEW-PRIVATE-DIR
  mini current-resource-intent --host HOST --config CONFIG.json --socket SOCKET --source SOURCE.json --signed-observation SIGNED-FACTORY.bin --dir NEW-PRIVATE-DIR
  mini agent-reserve-plan --host HOST --config CONFIG.json --operator-socket PRIVATE-SOCKET --public-socket PUBLIC-SOCKET --request SOURCE.json --dir NEW-PRIVATE-DIR
  mini agent-reserve-seal --attempt PRIVATE-DIR --approval OPERATOR-PRIVATE-APPROVAL.json
  mini agent-reserve-submit --attempt PRIVATE-DIR
  mini agent-reserve-lookup --attempt PRIVATE-DIR
  mini agent-lifetime-reserve-plan --host HOST --config CONFIG.json --operator-socket PRIVATE-SOCKET --public-socket PUBLIC-SOCKET --request SOURCE.json --dir NEW-PRIVATE-DIR
  mini agent-lifetime-reserve-seal --attempt PRIVATE-DIR --approval OPERATOR-PRIVATE-APPROVAL.json
  mini agent-lifetime-reserve-submit --attempt PRIVATE-DIR
  mini agent-lifetime-reserve-lookup --attempt PRIVATE-DIR
  mini agent-lifetime-paid-plan --reserve-attempt PRIVATE-DIR --grant-attempt PRIVATE-DIR --dir NEW-PRIVATE-DIR
  mini agent-lifetime-paid-payer-sign --attempt PRIVATE-DIR --approval PAYER-ONLY-APPROVAL.json
  mini agent-lifetime-paid-seal --attempt PRIVATE-DIR --approval OPERATOR-PRIVATE-APPROVAL.json
  mini agent-lifetime-paid-submit --attempt PRIVATE-DIR
  mini agent-lifetime-paid-lookup --attempt PRIVATE-DIR
  mini agent-lifetime-grant-plan --host HOST --config CONFIG.json --operator-socket PRIVATE-SOCKET --request SOURCE.json --dir NEW-PRIVATE-DIR
  mini agent-lifetime-grant-seal --attempt PRIVATE-DIR --approval OPERATOR-PRIVATE-APPROVAL.json
  mini agent-lifetime-grant-submit --attempt PRIVATE-DIR
  mini agent-lifetime-grant-inspect --host HOST --config CONFIG --operator-socket SOCKET --ingress CALL.bin --output NEW.json
  mini agent-lifetime-grant-lookup --attempt PRIVATE-DIR
  mini session-enrollment-plan --host HOST --config CONFIG.json --operator-socket PRIVATE-SOCKET --request SOURCE.json --dir NEW-PRIVATE-DIR
  mini session-enrollment-seal --attempt PRIVATE-DIR --approval OPERATOR-PRIVATE-APPROVAL.json
  mini session-enrollment-submit --attempt PRIVATE-DIR
  mini session-enrollment-lookup --attempt PRIVATE-DIR
  mini agent-payer-sign --host HOST --config CONFIG.json --operator-socket PRIVATE-SOCKET --reserve-attempt ORIGINAL-RESERVE-DIR --plan PAID-PLAN.bin --approval OPERATOR-PRIVATE-APPROVAL.json --key PAYER-SEED.bin --dir NEW-PRIVATE-DIR
  mini inspect --host HOST --config CONFIG.json [--socket SOCKET] --kind fn-inbox-resource|application-permission-schema --input VIEW.bin --output RESULT.json
  mini objective-invoke --host LOCAL-HOST --config CONFIG.json --request REQUEST.json --intent-nonce N --key KEY --dir NEW-ATTEMPT [--prepare-only true]   (lost reply: mini retry --attempt DIR --mode lookup)
  mini submit --host HOST --config CONFIG.json --intent INTENT.json [--intent-kind KIND] [--prepare-only true] [--provider-continuity DESCRIPTOR.json] --key KEY --dir ATTEMPT
  mini query (--workspace WORKSPACE | --host HOST --config CONFIG.json --key KEY) --intent INTENT.json [--intent-kind KIND] --view resource|policy|capability|at [--presentation fn-inbox-resource] --dir ATTEMPT
    --workspace takes the Host, config, key and socket from the workspace: the challenge and the query
    are answered by its serving session (ops 4/5), not by two cold Host opens of the Store.
  mini retry --attempt ATTEMPT [--mode submit|lookup] [--socket SOCKET|--direct true]
  mini attempt-state --attempt ATTEMPT [--file outcome.json|retry-NNNN.json] [--json]   (local: the retained state, repaired from seal.record)
  mini selected-release-submit --host HOST --config CONFIG.json --socket SOCKET --ingress INGRESS.bin --dir NEW-ATTEMPT
  mini selected-release-sign --host HOST --config SOURCE-CONFIG.json --preimage PREIMAGE.bin --key OWNER.key --output SIGNATURE.bin
  mini selected-source-sign --host HOST --config SOURCE-CONFIG.json --packet PACKET.bin --delegate-capability DECIMAL --key OWNER.key --dir NEW-PRIVATE-DIR
  mini selected-source-publish --host HOST --config SOURCE-CONFIG.json --ingress INGRESS.bin --article ARTICLE.eml --state-dir PRIVATE-DIR --post-config PRIVATE-POST.json
  mini selected-release-lookup --attempt ATTEMPT [--socket SOCKET]
  mini export-evidence --host HOST --config CONFIG.json --call CALL.bin --output PACKAGE.bin
  mini verify-evidence --host HOST --config INDEPENDENT-PIN.json --package PACKAGE.bin --output RESULT.json
  mini export-world --workspace WORKSPACE --home SESSION-HOME --out NEW-ARCHIVE     the member's world, taken with them (one per member per cooldown)
  mini serve --host HOST --config CONFIG.json --socket PRIVATE-DIR/mini.sock
  mini operator-status --socket PRIVATE --host HOST --config CONFIG.json
  mini drain-operator --socket PRIVATE --host HOST --config CONFIG.json --instance ID --pid PID --timeout-seconds 600
  mini serve-resident-operator-proxy --socket RESIDENT-PRIVATE/mini.sock --upstream PRIVATE --config CONFIG.json --resident-uid UID
                         requires two systemd-activated listeners (mini.sock, mini.control); the resident's host
                         operations and the status action only; resident clients pin MINI_OPERATOR_PEER_UID
  mini serve-agent-operator-proxy --socket CONTROLLER-PRIVATE-SOCKET --upstream PRIVATE --config CONFIG.json --controller-uid UID
                         requires one systemd-activated listener; controller clients pin --operator-peer-uid
  mini serve-controller-consent --socket CLIENT-PRIVATE-SOCKET --consent PROVIDER --config CONFIG.json --anchors PRIVATE-DIR --consent-sha256 HEX --config-sha256 HEX --controller-uid UID [--idle-seconds 600]
                         delegated full consent for one client UID that cannot read the Store (a controller, a
                         split-tenancy member); requires one systemd-activated listener; ends after --idle-seconds
                         with no connection; clients pin MINI_CONSENT_SOCKET/_PEER_UID/_SHA256/_CONFIG_SHA256
  mini serve-public-proxy --socket PUBLIC --upstream PRIVATE --config CONFIG.json [--socket-gid GID | --controller-uid UID]
                         --socket-gid: the public socket's directory may be group GID, mode 0710/0750
                         (never group-writable, never other-accessible); the socket becomes 0660 GID
                         --controller-uid: exact controller traversal/socket ACLs, retained across restart
  mini serve-operator --host HOST --config CONFIG.json --socket OPERATOR-PRIVATE-DIR/mini.sock [--peer-uid UID]...
                         admitted peers: this service's uid plus each --peer-uid (never a session uid)
  mini share-issue-prepare --host HOST --config CONFIG.json --socket OPERATOR-SOCKET --request REQUEST.json --approval OPERATOR-PRIVATE-APPROVAL.json --dir NEW-PRIVATE-DIR
  mini share-issue-submit --socket OPERATOR-SOCKET --attempt PREPARED-DIR
  mini share-issue-lookup --socket OPERATOR-OR-PUBLIC-SOCKET --attempt PREPARED-DIR
  mini share-issue-receipt-lookup --host HOST --config CONFIG.json --socket PUBLIC-SOCKET --ingress EXACT.bin --transaction-id TX --event-id EVENT --accepted-count COUNT --world-root BOUNDARY --dir NEW-PRIVATE-DIR
  mini grain-share-issue-plan --host HOST --config CONFIG.json --socket OPERATOR-SOCKET --request REQUEST.json --dir NEW-PRIVATE-DIR
  mini grain-share-issue-prepare --host HOST --config CONFIG.json --socket OPERATOR-SOCKET --request REQUEST.json --approval OPERATOR-PRIVATE-APPROVAL.json --dir NEW-PRIVATE-DIR
  mini grain-share-issue-submit --socket OPERATOR-SOCKET --attempt PREPARED-DIR
  mini grain-share-issue-lookup --socket OPERATOR-SOCKET --attempt PREPARED-DIR
  mini grain-share-issue-receipt-lookup --host HOST --config CONFIG.json --socket PUBLIC-SOCKET --ingress EXACT.bin --transaction-id TX --event-id EVENT --accepted-count COUNT --world-root BOUNDARY --dir NEW-PRIVATE-DIR
  mini historical-call-receipt-lookup --host HOST --config CONFIG.json --socket PUBLIC-SOCKET --call EXACT.bin --transaction-id TX --event-id EVENT --accepted-count COUNT --world-root BOUNDARY --dir NEW-PRIVATE-DIR
  mini provider-continuity --host HOST --config CONFIG.json --socket SOCKET --guarded-attempt ATTEMPT --dir NEW-PROOF
  mini continuity --host HOST --config CONFIG.json --socket SOCKET --call RESERVE/call.bin --outcome RESERVE/outcome.bin --dir NEW-ATTEMPT
  mini meter --host HOST --config CONFIG.json --socket SOCKET --metadata META.json --request REQUEST.bin --response RESPONSE.bin --dir NEW-ATTEMPT

Add --socket PRIVATE-DIR/mini.sock to author, submit, query, retry, and other
supported host commands to use one persistent Lean host session.

--remote DEST (an ssh destination: user@host or an ssh config Host alias) is
--socket ssh:DEST: every request goes through `ssh -T DEST` to the box's byte
proxy (mini socket-proxy) instead of a local socket, so keys, workspace and
signing stay on this machine. A remote workspace has no Host image; it pins
the Host's SHA-256 (--host-sha256, or from the sponsor's plan via join).
MINI_SSH names another ssh program.

The Lean host authors and decodes every semantic value. This client owns only
private-key custody, process transport, retained attempts, and exact retries.
"#;

type Result<T> = std::result::Result<T, String>;

/// The commands that run over `--remote`: the participant's own surface.
/// Operator and worker commands keep local sockets, service locks and Host
/// images, and the proxy never reaches the operator socket anyway.
#[cfg(unix)]
const REMOTE_COMMANDS: &[&str] = &[
    "workspace", "enroll", "join", "pay-claim", "shell", "submit", "query", "retry", "author", "inspect",
    "describe", "profile",
];

#[derive(Debug)]
struct Args {
    command: OsString,
    values: Vec<(OsString, OsString)>,
}

impl Args {
    fn parse() -> Result<Self> {
        Self::parse_from(env::args_os().skip(1))
    }

    fn parse_from(raw: impl IntoIterator<Item = OsString>) -> Result<Self> {
        let mut raw = raw.into_iter();
        let mut values = Vec::new();
        let no_command = || format!("no command given\n\n{USAGE}");
        let mut command = raw.next().ok_or_else(no_command)?;
        if command == OsStr::new("--verify-host") {
            VERIFY_HOST.store(true, Ordering::Relaxed);
            command = raw.next().ok_or_else(no_command)?;
        }
        if command == OsStr::new("--remote") {
            let destination = raw.next().ok_or("missing value for --remote")?;
            values.push((command, destination));
            command = raw.next().ok_or_else(no_command)?;
        }
        if command == OsStr::new("--help") || command == OsStr::new("-h") {
            return Err(USAGE.to_owned());
        }
        let mut raw = raw.peekable();
        // `mini pay ACTION ...` (docs/PAY.md §5 spells the verbs this way) is `mini pay --action ACTION ...`.
        if command == OsStr::new("pay") || command == OsStr::new("store") || command == OsStr::new("apps") {
            if let Some(action) = raw.next_if(|next| !next.to_string_lossy().starts_with("--")) {
                // `mini apps share a4501 bob`: the grammar leaf's positionals are the flags
                // `--grain a4501 --to bob` (the same words the shell takes).
                let leaf = (command == OsStr::new("apps")).then(|| action.to_str()).flatten()
                    .and_then(|name| shell_grammar::leaf(&shell_grammar::APPS, &["apps", name]));
                values.push((OsString::from("--action"), action));
                for argument in leaf.map(|l| l.args).unwrap_or(&[]) {
                    match raw.next_if(|next| !next.to_string_lossy().starts_with("--")) {
                        Some(value) => values.push((OsString::from(format!("--{}", apps::positional_flag(argument.name))), value)),
                        None => break,
                    }
                }
            }
        }
        while let Some(flag) = raw.next() {
            let rendered = flag.to_string_lossy();
            // `mini join --solana|--wait|--renew` (docs/PAY.md §11.6) is `mini join --mode MODE`.
            if command == OsStr::new("join")
                && matches!(rendered.as_ref(), "--solana" | "--wait" | "--renew")
            {
                values.push((OsString::from("--mode"), OsString::from(&rendered[2..])));
                continue;
            }
            if !rendered.starts_with("--") || rendered.len() == 2 {
                return Err(format!("unexpected argument {rendered}\n\n{USAGE}"));
            }
            // The valueless switches: opting out of pre-rotation is a
            // deliberate act and reads as one; `web --body` / `--anonymous` name a face; `apps --json` a shape.
            if rendered == "--no-prerotation" || command == OsStr::new("web") && matches!(rendered.as_ref(), "--body" | "--anonymous")
                || matches!(command.to_str(), Some("apps" | "attempt-state")) && rendered == "--json" || command == OsStr::new("shell") && rendered == "--plan" {
                values.push((flag, OsString::from("yes")));
                continue;
            }
            let value = raw
                .next()
                .ok_or_else(|| format!("missing value for {rendered}"))?;
            values.push((flag, value));
        }
        Ok(Self { command, values })
    }

    fn required(&mut self, name: &str) -> Result<OsString> {
        let flag = OsString::from(format!("--{name}"));
        let Some(index) = self.values.iter().position(|(key, _)| *key == flag) else {
            return Err(format!("missing --{name}"));
        };
        Ok(self.values.remove(index).1)
    }

    fn peek(&self, name: &str) -> Option<&OsStr> {
        let flag = OsString::from(format!("--{name}"));
        self.values.iter().find(|(key, _)| *key == flag).map(|(_, value)| value.as_os_str())
    }

    fn optional(&mut self, name: &str) -> Option<OsString> {
        let flag = OsString::from(format!("--{name}"));
        let index = self.values.iter().position(|(key, _)| *key == flag)?;
        Some(self.values.remove(index).1)
    }

    fn repeated(&mut self, name: &str) -> Vec<OsString> {
        let flag = OsString::from(format!("--{name}"));
        let mut found = Vec::new();
        self.values.retain(|(key, value)| {
            if *key == flag {
                found.push(value.clone());
                false
            } else {
                true
            }
        });
        found
    }

    fn finish(self) -> Result<()> {
        if self.values.is_empty() {
            Ok(())
        } else {
            Err(format!(
                "unknown or duplicate option {}",
                self.values[0].0.to_string_lossy()
            ))
        }
    }
}

fn path(value: OsString) -> PathBuf {
    PathBuf::from(value)
}

fn absolute(path: &Path) -> Result<PathBuf> {
    if path.is_absolute() {
        Ok(path.to_path_buf())
    } else {
        env::current_dir()
            .map(|cwd| cwd.join(path))
            .map_err(|error| format!("cannot resolve {}: {error}", path.display()))
    }
}

fn utf8_path(path: &Path) -> Result<&str> {
    path.to_str()
        .ok_or_else(|| format!("path is not valid UTF-8: {}", path.display()))
}

#[cfg(unix)]
fn selected_release_sign(
    host: &Path,
    config: &Path,
    preimage: &Path,
    key: &Path,
    output: &Path,
) -> Result<()> {
    if SOCKET.get().is_some() {
        return Err("selected-release-sign requires direct source Host validation".into());
    }
    if output.exists() {
        return Err(format!("refusing to replace {}", output.display()));
    }
    let mut bytes = Vec::new();
    File::open(preimage)
        .map_err(|e| format!("cannot open selected release preimage: {e}"))?
        .take(1_520_481)
        .read_to_end(&mut bytes)
        .map_err(|e| format!("cannot read selected release preimage: {e}"))?;
    if bytes.is_empty() || bytes.len() > 1_520_480 {
        return Err("selected release preimage exceeds bounded profile".into());
    }
    let signing = crate::fsio::read_secret(key)?;
    let parent = output
        .parent()
        .filter(|part| !part.as_os_str().is_empty())
        .unwrap_or(Path::new("."));
    let temporary = parent.join(format!(
        ".mini-selected-release-check-{}-{}",
        std::process::id(),
        SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .map_err(|e| format!("clock before Unix epoch: {e}"))?
            .as_nanos()
    ));
    fsio::create_private_dir(&temporary)?;
    let result = (|| {
        let canonical_path = temporary.join("canonical.bin");
        process(
            host,
            config,
            &[
                OsStr::new("selected-release-check-preimage"),
                preimage.as_os_str(),
                canonical_path.as_os_str(),
            ],
        )?;
        let mut canonical = Vec::new();
        File::open(&canonical_path)
            .map_err(|e| format!("cannot open Host-checked preimage: {e}"))?
            .take(1_520_481)
            .read_to_end(&mut canonical)
            .map_err(|e| format!("cannot read Host-checked preimage: {e}"))?;
        if canonical != bytes {
            return Err("Host-checked selected release preimage differs from exact input".into());
        }
        create_private(output, &signing.sign(&bytes).to_bytes())
    })();
    let _ = fs::remove_dir_all(&temporary);
    result
}

/// `escrow`: `(@FILE|HEX of the sponsor's 32-byte encryption public key,
/// subject)`. Off by default; when given, the seed is also written to
/// `<public>.escrow`, sealed to the sponsor and bound to the subject
/// (`DREGG/SEED-ESCROW/v1`), which lets the sponsor sign as this key.
/// Where `keygen` puts the NEXT key, or that it makes none.
enum NextKey {
    /// `SECRET.next`, beside the daily key (the shell's hosted default).
    Beside,
    /// `--next-to PATH`: other media.
    To(PathBuf),
    /// `--no-prerotation`: no next key; the identity can never rotate.
    Without,
}

fn keygen(
    secret: &Path,
    public: &Path,
    escrow: Option<(OsString, OsString)>,
    next: NextKey,
    hosted: bool,
) -> Result<()> {
    let public_key = generate_key(secret, public, escrow, next, hosted)?;
    eprintln!("Your blinding key is derived from this seed; it keys the salts that hide each cell’s fields from readers you have not named.");
    println!("{}", hex(&public_key));
    Ok(())
}

/// Create a fresh Ed25519 seed at `secret`, its public key at `public` and,
/// unless `NextKey::Without`, the NEXT key (K-PREROTATE); returns the public
/// key and prints nothing on stdout (`mini fleet-sign` answers in JSON there).
/// No file may already exist.
fn generate_key(
    secret: &Path,
    public: &Path,
    escrow: Option<(OsString, OsString)>,
    next: NextKey,
    hosted: bool,
) -> Result<[u8; 32]> {
    if secret.exists() {
        return Err(format!("refusing to replace {}", secret.display()));
    }
    if public.exists() {
        return Err(format!("refusing to replace {}", public.display()));
    }
    let next_paths = match &next {
        NextKey::Without => None,
        NextKey::Beside => {
            let mut name = secret.as_os_str().to_owned();
            name.push(".next");
            Some(PathBuf::from(name))
        }
        NextKey::To(path) => Some(path.clone()),
    }
    .map(|next_secret| (next_secret, key_rotation::conventional_next_public(secret)));
    if let Some((next_secret, next_public)) = &next_paths {
        for existing in [next_secret, next_public] {
            if existing.exists() {
                return Err(format!("refusing to replace {}", existing.display()));
            }
        }
    }
    let mut seed = fsio::random::<32>()?;
    let signing = SigningKey::from_bytes(&seed);
    let escrowed = match &escrow {
        None => None,
        Some((sponsor, subject)) => {
            let sponsor = sponsor.to_str().ok_or("--escrow-to-sponsor must be UTF-8")?;
            let text = match sponsor.strip_prefix('@') {
                Some(file) => fs::read_to_string(file)
                    .map_err(|error| format!("cannot read sponsor key {file}: {error}"))?,
                None => sponsor.to_owned(),
            };
            // The sponsor's full hybrid public key (`mini enc-public`): X25519 + ML-KEM-768.
            let key = workspace::private::MemberPublic::from_bytes(
                &crate::decode_hex(text.trim())?,
            )?;
            let subject = subject.to_str().ok_or("--escrow-subject must be UTF-8")?;
            Some(workspace::private::escrow_seed(subject, &seed, &key)?)
        }
    };
    create_private(secret, &seed)?;
    seed.fill(0);
    if let Err(error) = create_public(public, &signing.verifying_key().to_bytes()) {
        fs::remove_file(secret).map_err(|cleanup| {
            format!(
                "{error}; also cannot remove newly-created {}: {cleanup}",
                secret.display()
            )
        })?;
        return Err(error);
    }
    if hosted {
        create_private(&workspace::private::hosted_marker_path(secret), b"")?;
    }
    if let Some(wrapped) = escrowed {
        let mut escrow_path = public.as_os_str().to_owned();
        escrow_path.push(".escrow");
        create_private(Path::new(&escrow_path), &wrapped.to_bytes())?;
    }
    eprintln!("{}", workspace::private::KEYGEN_NOTICE);
    match &next_paths {
        None => eprintln!("no next key (--no-prerotation): this identity can never rotate; a stolen key is replaced only by enrolling a new subject"),
        Some((next_secret, next_public)) => {
            let mut next_seed = fsio::random::<32>()?;
            let next_signing = SigningKey::from_bytes(&next_seed);
            create_private(next_secret, &next_seed)?;
            next_seed.fill(0);
            create_public(next_public, &next_signing.verifying_key().to_bytes())?;
            // FIX-IDENTITY: the next key co-signs its succession now, while it is
            // here; an enrollment that commits to it carries this signature.
            let cosign_path = key_rotation::conventional_next_cosign(secret);
            let cosign = key_rotation::cosign(&signing.verifying_key().to_bytes(), &next_signing);
            create_public(&cosign_path, &cosign)?;
            eprintln!("next key: {} (its public half: {})", next_secret.display(), next_public.display());
            eprintln!("for your sponsor's `enroll plan NAME KEYFILE NEXT-PUB COSIGN` (public, safe to send):");
            eprintln!("  next public key: {}", hex(&next_signing.verifying_key().to_bytes()));
            eprintln!("  co-signature:    {}", hex(&cosign));
            eprintln!("{}", key_rotation::PREROTATION_NOTICE);
            if hosted {
                eprintln!("{}", key_rotation::HOSTED_PREROTATION_NOTICE);
            }
        }
    }
    Ok(signing.verifying_key().to_bytes())
}

/// The Host argv of `mini store audit`: `PINNED.json store-audit [--receipts FILE]`.
fn store_audit_argv(config: &Path, receipts: Option<&Path>) -> Vec<OsString> {
    let mut argv = vec![config.as_os_str().to_owned(), OsString::from("store-audit")];
    if let Some(receipts) = receipts {
        argv.push(OsString::from("--receipts"));
        argv.push(receipts.as_os_str().to_owned());
    }
    argv
}

/// `mini store audit --host HOST --config PINNED.json [--receipts FILE]`: runs the Host's
/// `store-audit` arm with the Host's own stdout and stderr, and ends with its exit status
/// (0 clean, 1 a named refusal, 2 usage). Nothing is captured or reworded.
fn store_run(mut args: Args) -> Result<()> {
    const STORE_USAGE: &str = "usage: mini store audit --host HOST --config PINNED.json [--receipts FILE]";
    if args.optional("action").as_deref() != Some(OsStr::new("audit")) {
        return Err(STORE_USAGE.to_owned());
    }
    if SOCKET.get().is_some() {
        return Err("store audit requires direct Host/Main CLI".to_owned());
    }
    let host = path(args.required("host")?);
    let config = path(args.required("config")?);
    let receipts = args.optional("receipts").map(path);
    args.finish()?;
    let status = Command::new(&host)
        .args(store_audit_argv(&config, receipts.as_deref()))
        .status()
        .map_err(|error| format!("cannot run {}: {error}", host.display()))?;
    match status.code() {
        Some(code) => {
            set_exit(u8::try_from(code).unwrap_or(1));
            Ok(())
        }
        None => Err(format!("{} ended by signal: {status}", host.display())),
    }
}

fn process(host: &Path, config: &Path, arguments: &[&OsStr]) -> Result<Output> {
    let pure = arguments.first().and_then(|word| word.to_str()).is_some_and(|verb|
        matches!(verb, "author" | "inspect" | "signatures" | "observe-assemble" | "assemble"));
    if pure {
        return client_consent::codec_process(host, config, arguments);
    }
    if let Some(socket) = SOCKET.get() {
        return socket_process(host, socket, config, arguments);
    }
    if host.as_os_str().is_empty() {
        return Err("no Host image and no socket: pass --remote or --socket".into());
    }
    local_process(host, config, arguments)
}

fn local_process(host: &Path, config: &Path, arguments: &[&OsStr]) -> Result<Output> {
    let mut command = Command::new(host);
    command.arg(config).args(arguments);
    // Audit progress must survive a timeout. Keep ordinary requests and
    // their captured error diagnostics unchanged; socket calls returned above.
    if arguments == [OsStr::new("audit")]
        && std::env::var_os("MINI_AUDIT_TIMING").as_deref() == Some(OsStr::new("1"))
    {
        command.stderr(std::process::Stdio::inherit());
    }
    let output = command
        .output()
        .map_err(|error| format!("cannot run {}: {error}", host.display()))?;
    if !output.status.success() {
        // A decided refusal arrives as exit 3 with the Host's outcome frame on stdout, and is
        // handled as the socket route handles it. Pure codec verbs never reach here (`process`
        // sends them to the codec child); any other failing exit is not a decision, so the
        // status stays uncertain.
        if let Some(decided) = local_outcome_frame(host, config, arguments, &output) {
            return decided;
        }
        return Err(format!(
            "{} exited {}; request status uncertain: {}",
            host.display(),
            output.status,
            String::from_utf8_lossy(&output.stderr).trim()
        ));
    }
    Ok(output)
}

/// One Host outcome frame (marker byte 253 or 255, then the encoded Outcome), from either
/// route: the socket session's reply, or the one-shot Host's stdout when it exits 3 (a decided
/// refusal of a Store-reading verb). The decision is noted as the Host's (a refusal exits 3),
/// a prepare refusal is retained for `why` (`prepare_refusal::retain`), and the returned
/// message names the refusal, or says the effect is undecided. Never "uncertain" for a frame.
fn host_outcome_frame(
    command: &str,
    arguments: &[&OsStr],
    payload: &[u8],
    config: &Path,
    reply: &[u8],
    decoded: Option<Value>,
) -> Result<String> {
    let line = Some(no_record_line(decoded.as_ref()));
    let decision = HostDecision::Frame {
        command: command.to_owned(),
        byte: reply[0],
        encoded: reply[1..].to_vec(),
        decoded,
    };
    let refusal = decision.is_refusal();
    let kind = outcome_type(decision.outcome()).to_owned();
    note_host_decision(decision);
    let destination = match command {
        "prepare" | "submit" | "lookup" | "query" | "query-batch" => arguments.get(2).map(Path::new),
        _ => None,
    };
    if command == "prepare" {
        let destination = Path::new(arguments.get(2).ok_or("prepare has no destination")?);
        prepare_refusal::retain(destination, payload, config, reply)?;
    }
    if command == "query" || command == "query-batch" {
        let destination = Path::new(arguments.get(2).ok_or("query has no destination")?);
        query_refusal::retain(destination, payload, config, reply)?;
    }
    if !refusal {
        return Ok(undecided_frame_message(command, &kind, destination, &reply[1..]));
    }
    Ok(refused_frame_message(command, &reply[1..], line))
}

/// The one-shot Host's decided refusal of `prepare`: exit 3 with its outcome frame on stdout
/// (`Host.Main`, the `prepare` verb). The frame is decoded by the Host's own codec (`inspect
/// outcome`) and handled exactly as the socket route handles it. Anything else is not a frame.
fn local_outcome_frame(host: &Path, config: &Path, arguments: &[&OsStr], output: &Output) -> Option<Result<Output>> {
    let command = arguments.first().and_then(|word| word.to_str())?;
    if output.status.code() != Some(3) || command != "prepare" || arguments.len() != 3 {
        return None;
    }
    let reply = &output.stdout;
    if reply.len() < 2 || reply.len() > transport::HOST_MAX_FRAME + 1 || !is_outcome_frame(reply[0]) {
        return None;
    }
    let payload = match fsio::read_bounded_or_empty(Path::new(arguments[1]), transport::HOST_MAX_FRAME) {
        Ok(payload) => payload,
        Err(error) => return Some(Err(error)),
    };
    let decoded = mini_sdk::local::kind("outcome", &reply[1..])
        .ok()
        .and_then(|request| client_consent::codec_frame(host, config, mini_sdk::host_operations::INSPECT, &request).ok())
        .filter(|inspected| inspected.first() == Some(&mini_sdk::host_operations::INSPECT))
        .and_then(|inspected| serde_json::from_slice::<Value>(&inspected[1..]).ok());
    Some(host_outcome_frame(command, arguments, &payload, config, reply, decoded).and_then(Err))
}

/// A 255 frame whose decoded outcome is not a refusal (or that the Host could not decode): the
/// effect is unknown. For an exact call (`submit`, `lookup`) the retry is named: a lookup of the
/// SAME retained call, never a new operation.
fn undecided_frame_message(command: &str, kind: &str, destination: Option<&Path>, encoded: &[u8]) -> String {
    let retry = match (command, destination.and_then(Path::parent)) {
        ("submit" | "lookup", Some(dir)) => format!("; the exact call is retained: `mini retry --dir {} --mode lookup`", dir.display()),
        _ => String::new(),
    };
    format!("undecided: Host answered {command} with reply byte 255 and outcome {kind}{retry}; encoded frame: {}", hex(encoded))
}

fn refused_frame_message(command: &str, encoded: &[u8], line: Option<String>) -> String {
    match line {
        Some(line) => format!("host refused {command}: {line}; encoded refusal: {}", hex(encoded)),
        None => format!("host refused {command}; encoded refusal: {}", hex(encoded)),
    }
}

#[cfg(unix)]
fn socket_process(
    host: &Path,
    socket: &Path,
    config: &Path,
    arguments: &[&OsStr],
) -> Result<Output> {
    let command = arguments
        .first()
        .and_then(|s| s.to_str())
        .ok_or("missing host command")?;
    let read = |index: usize| -> Result<Vec<u8>> {
        let path = arguments.get(index).ok_or("missing host input path")?;
        let path = Path::new(path);
        fsio::read_bounded_or_empty(path, transport::HOST_MAX_FRAME)
    };
    let pair = |first: Vec<u8>, second: Vec<u8>| -> Result<Vec<u8>> {
        let length: u32 = first.len().try_into().map_err(|_| "host input too large")?;
        let mut bytes = length.to_le_bytes().to_vec();
        bytes.extend(first);
        bytes.extend(second);
        Ok(bytes)
    };
    let kind_payload = |kind: &OsStr, input: Vec<u8>| -> Result<Vec<u8>> {
        let kind = kind.to_str().ok_or("host kind must be UTF-8")?.as_bytes();
        let length: u16 = kind.len().try_into().map_err(|_| "host kind too long")?;
        let mut bytes = length.to_le_bytes().to_vec();
        bytes.extend(kind);
        bytes.extend(input);
        Ok(bytes)
    };
    let (operation, payload, destination) = match command {
        "describe" if arguments.len() == 1 => (0, vec![], None),
        "profile" if arguments.len() == 1 => (6, vec![], None),
        "prepare" if arguments.len() == 3 => (1, read(1)?, Some(arguments[2])),
        "submit" if arguments.len() == 3 => (2, read(1)?, Some(arguments[2])),
        "lookup" if arguments.len() == 3 => (3, read(1)?, Some(arguments[2])),
        "challenge" if arguments.len() == 4 => (4, pair(read(1)?, read(2)?)?, Some(arguments[3])),
        "query" if arguments.len() == 3 => (5, read(1)?, Some(arguments[2])),
        "challenge-batch" if arguments.len() == 3 => (4, read(1)?, Some(arguments[2])),
        "query-batch" if arguments.len() == 3 => (5, read(1)?, Some(arguments[2])),
        "author" if arguments.len() == 4 => {
            (7, kind_payload(arguments[1], read(2)?)?, Some(arguments[3]))
        }
        "inspect" if arguments.len() == 4 => {
            (8, kind_payload(arguments[1], read(2)?)?, Some(arguments[3]))
        }
        "object-audience" | "object-roster-inspect" if arguments.len() == 3 => {
            (8, kind_payload(arguments[0], read(1)?)?, Some(arguments[2]))
        }
        "object-audience-roster" if arguments.len() == 6 => {
            let inputs = pair(read(1)?, pair(read(2)?, pair(read(3)?, read(4)?)?)?)?;
            (8, kind_payload(arguments[0], inputs)?, Some(arguments[5]))
        }
        "signatures" if arguments.len() == 3 => (9, read(1)?, Some(arguments[2])),
        "observe-assemble" if arguments.len() == 4 => {
            (10, pair(read(1)?, read(2)?)?, Some(arguments[3]))
        }
        "assemble" if arguments.len() == 4 => (11, pair(read(1)?, read(2)?)?, Some(arguments[3])),
        "dry-run" if arguments.len() == 4 => {
            (130, pair(read(1)?, read(2)?)?, Some(arguments[3]))
        }
        "law-sat" if arguments.len() == 3 => (150, read(1)?, Some(arguments[2])),
        _ => {
            return Err(format!(
                "{command} is not available through the persistent host session"
            ))
        }
    };
    let reply = session_invoke(host, socket, config, operation, &payload)?;
    if is_outcome_frame(reply[0]) {
        // Ask the same Host session to decode its own frame (op 8, `inspect
        // outcome`). A failed decode leaves the decision undecoded; it is
        // never reconstructed here. The class is the marker's (`is_refusal`).
        let decoded = kind_payload(OsStr::new("outcome"), reply[1..].to_vec())
            .and_then(|request| session_invoke(host, socket, config, mini_sdk::host_operations::INSPECT, &request))
            .ok()
            .filter(|inspected| inspected.first() == Some(&8))
            .and_then(|inspected| serde_json::from_slice::<Value>(&inspected[1..]).ok());
        return Err(host_outcome_frame(command, arguments, &payload, config, &reply, decoded)?);
    }
    if let Some(destination) = destination {
        write_new(Path::new(destination), &reply[1..])?;
    }
    use std::os::unix::process::ExitStatusExt;
    Ok(Output {
        status: std::process::ExitStatus::from_raw(0),
        stdout: reply[1..].to_vec(),
        stderr: Vec::new(),
    })
}

#[cfg(not(unix))]
fn socket_process(
    _host: &Path,
    _socket: &Path,
    _config: &Path,
    _arguments: &[&OsStr],
) -> Result<Output> {
    Err("persistent host sessions require Unix sockets".to_owned())
}

fn host_files(host: &Path, config: &Path, arguments: &[&Path]) -> Result<()> {
    let args: Vec<&OsStr> = arguments.iter().map(|path| path.as_os_str()).collect();
    process(host, config, &args).map(|_| ())
}

fn host_words(host: &Path, config: &Path, arguments: &[&str]) -> Result<Output> {
    let args: Vec<&OsStr> = arguments.iter().map(OsStr::new).collect();
    process(host, config, &args)
}

fn create_dir(path: &Path) -> Result<()> {
    fs::create_dir(path).map_err(|error| format!("cannot create {}: {error}", path.display()))
}

/// The native host may write call.bin without syncing it. A successful
/// external submit must never precede a durable exact call and its pathname.
fn sync_retained_call(directory: &Path, call: &Path) -> Result<()> {
    File::open(call)
        .and_then(|file| mini_sdk::durable::sync_file(&file))
        .map_err(|error| format!("cannot sync exact call {}: {error}", call.display()))?;
    sync_directory_ancestors(directory)
}

fn write_new(path: &Path, bytes: &[u8]) -> Result<()> {
    create_public(path, bytes)
}

/// The Store's checkpoint/log MAC key: 32 bytes of operating-system
/// randomness, mode 0600, beside the pinned configuration. One per Store; it
/// authenticates only that Store's checkpoints and log tags. It is never
/// printed, copied into another artifact, or committed.
fn checkpoint_key(path: &Path) -> Result<()> {
    let mut key = fsio::random::<32>()?;
    let result = create_private(path, &key);
    key.fill(0);
    result
}

fn bootstrap(host: &Path, config: &Path, source: &Path, directory: &Path) -> Result<()> {
    create_dir(directory)?;
    checkpoint_key(&directory.join("checkpoint.key"))?;
    let source_copy = directory.join("genesis-source.json");
    let operator_copy = directory.join("operator-config.json");
    let source_bin = directory.join("genesis-source.bin");
    let genesis_bin = directory.join("genesis.bin");
    let pinned = directory.join("pinned-config.json");
    let profile = directory.join("profile.json");
    copy_new(source, &source_copy)?;
    copy_new(config, &operator_copy)?;
    let output = host_words(host, &operator_copy, &["profile"])?;
    write_new(&profile, &output.stdout)?;
    process(
        host,
        &operator_copy,
        &[
            OsStr::new("author"),
            OsStr::new("genesis"),
            source_copy.as_os_str(),
            source_bin.as_os_str(),
        ],
    )?;
    process(
        host,
        &operator_copy,
        &[
            OsStr::new("genesis"),
            source_bin.as_os_str(),
            genesis_bin.as_os_str(),
            pinned.as_os_str(),
        ],
    )?;
    host_files(host, &pinned, &[Path::new("bootstrap"), &genesis_bin])?;
    let description = process(host, &pinned, &[OsStr::new("describe")])?;
    write_new(&directory.join("description.json"), &description.stdout)?;
    // The pay ledger at genesis: the issuer well before any payment, which `mini pay audit`
    // needs for `-well_now = -well_genesis + credited` (`well_tracks_observed`).
    host_files(
        host,
        &pinned,
        &[Path::new("pay-ledger"), &directory.join("pay-ledger-genesis.json")],
    )?;
    println!("{}", pinned.display());
    Ok(())
}

fn author(host: &Path, config: &Path, kind: &OsStr, input: &Path, output: &Path) -> Result<()> {
    if output.exists() {
        return Err(format!("refusing to replace {}", output.display()));
    }
    process(
        host,
        config,
        &[
            OsStr::new("author"),
            kind,
            input.as_os_str(),
            output.as_os_str(),
        ],
    )?;
    Ok(())
}

pub(crate) fn inspect(host: &Path, config: &Path, kind: &str, input: &Path, output: &Path) -> Result<Value> {
    process(
        host,
        config,
        &[
            OsStr::new("inspect"),
            OsStr::new(kind),
            input.as_os_str(),
            output.as_os_str(),
        ],
    )?;
    let bytes =
        fs::read(output).map_err(|error| format!("cannot read {}: {error}", output.display()))?;
    serde_json::from_slice(&bytes)
        .map_err(|error| format!("invalid host JSON {}: {error}", output.display()))
}

/// Host op 150 (`law-sat`, C-SAT-2): the Host's satisfiability answer for a
/// law, from the request bytes alone.
pub(crate) fn law_sat(host: &Path, config: &Path, input: &Path, output: &Path) -> Result<Value> {
    process(
        host,
        config,
        &[OsStr::new("law-sat"), input.as_os_str(), output.as_os_str()],
    )?;
    let bytes =
        fs::read(output).map_err(|error| format!("cannot read {}: {error}", output.display()))?;
    serde_json::from_slice(&bytes)
        .map_err(|error| format!("invalid law-sat answer {}: {error}", output.display()))
}

fn validate_public_inspection(kind: &str, value: &Value, input: Option<&[u8]>) -> Result<()> {
    match kind {
        "fn-inbox-resource"
            if value.get("type").and_then(Value::as_str)
                == Some("fn-inbox-resource-summary-v1") =>
        {
            Ok(())
        }
        "application-permission-schema"
            if value.get("type").and_then(Value::as_str)
                == Some("minidregg-application-permission-schema-v1") =>
        {
            let canonical = value
                .get("canonical")
                .and_then(Value::as_str)
                .ok_or("schema inspection lacks canonical bytes")?;
            let decoded = mini_sdk::hex::decode(canonical).map_err(|e| e.0)?;
            if Some(decoded.as_slice()) != input {
                return Err("schema inspection canonical bytes differ from exact input".into());
            }
            Ok(())
        }
        _ => Err("Host returned an unexpected public inspection type".into()),
    }
}

fn inspect_public(
    host: &Path,
    config: &Path,
    kind: &str,
    input: &Path,
    output: &Path,
) -> Result<()> {
    if output.exists() {
        return Err(format!("refusing to replace {}", output.display()));
    }
    let schema_input = if kind == "application-permission-schema" {
        let mut bytes = Vec::new();
        File::open(input)
            .map_err(|e| format!("cannot open schema input: {e}"))?
            .take(1_048_577)
            .read_to_end(&mut bytes)
            .map_err(|e| format!("cannot read schema input: {e}"))?;
        if bytes.is_empty() || bytes.len() > 1_048_576 {
            return Err("schema input must be 1..=1048576 bytes".into());
        }
        Some(bytes)
    } else {
        None
    };
    let parent = output
        .parent()
        .filter(|path| !path.as_os_str().is_empty())
        .unwrap_or(Path::new("."));
    let temporary = parent.join(format!(
        ".mini-inspect-{}-{}",
        std::process::id(),
        SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .map_err(|error| format!("clock before Unix epoch: {error}"))?
            .as_nanos()
    ));
    fsio::create_private_dir(&temporary)?;
    let result = (|| {
        let temporary_output = temporary.join("result.json");
        process(
            host,
            config,
            &[
                OsStr::new("inspect"),
                OsStr::new(kind),
                input.as_os_str(),
                temporary_output.as_os_str(),
            ],
        )?;
        let mut bytes = Vec::new();
        let mut file = File::open(&temporary_output)
            .map_err(|error| format!("cannot open host inspection output: {error}"))?;
        if schema_input.is_some() {
            (&mut file)
                .take(1_048_577)
                .read_to_end(&mut bytes)
                .map_err(|error| format!("cannot read schema inspection output: {error}"))?;
            if bytes.len() > 1_048_576 {
                return Err("schema inspection output exceeds 1 MiB".into());
            }
        } else {
            file.read_to_end(&mut bytes)
                .map_err(|error| format!("cannot read host inspection output: {error}"))?;
        }
        let summary: Value = serde_json::from_slice(&bytes)
            .map_err(|error| format!("invalid host inspection JSON: {error}"))?;
        validate_public_inspection(kind, &summary, schema_input.as_deref())?;
        write_new(output, &bytes)?;
        print_json(&summary)
    })();
    let _ = fs::remove_dir_all(&temporary);
    result
}

/// The crate's hex codec for text a person or another tool may type: lowercase on encode; this
/// decoder accepts either case, ASCII digits only, even length, never a panic on non-ASCII input
/// and never `from_str_radix`'s leading `+`. Values the Host produced or this client retained
/// are contract spellings: their sites decode strictly with `mini_sdk::hex::decode`.
pub(crate) use mini_sdk::hex::encode as hex;
pub(crate) fn decode_hex(value: &str) -> Result<Vec<u8>> {
    mini_sdk::hex::decode_any_case(value).map_err(|error| error.0)
}

fn plan_headers(value: &Value) -> Result<Vec<Vec<u8>>> {
    let slots = value
        .get("slots")
        .and_then(Value::as_array)
        .ok_or_else(|| "host plan JSON has no slots array".to_owned())?;
    slots
        .iter()
        .map(|slot| {
            slot.get("header")
                .and_then(Value::as_str)
                .ok_or_else(|| "host plan slot has no header string".to_owned())
                .and_then(|header| mini_sdk::hex::decode(header).map_err(|e| e.0))
        })
        .collect()
}

/// The Host's `signatures` list: each header signed by `signer` under its own scheme
/// (`mini_sdk::signer`), hex, in order. A scheme's signature width is the scheme's, not this file's.
fn sign_headers(signer: &dyn mini_sdk::signer::Signer, headers: &[Vec<u8>]) -> Result<Value> {
    headers
        .iter()
        .map(|header| Ok(Value::String(hex(&signer.sign(header)?))))
        .collect::<Result<Vec<_>>>()
        .map(Value::Array)
}

fn write_json_new(path: &Path, value: &Value) -> Result<()> {
    let mut bytes = serde_json::to_vec_pretty(value)
        .map_err(|error| format!("cannot render {}: {error}", path.display()))?;
    bytes.push(b'\n');
    write_new(path, &bytes)
}

fn print_json(value: &Value) -> Result<()> {
    if QUIET_WORKER.load(Ordering::Relaxed) {
        return Ok(());
    }
    let rendered = serde_json::to_string_pretty(value)
        .map_err(|error| format!("cannot render host JSON: {error}"))?;
    println!("{rendered}");
    Ok(())
}

fn print_confirmed_outcome(value: &Value) -> Result<()> {
    confirmed_outcome(value, true)
}

fn confirmed_outcome(value: &Value, emit: bool) -> Result<()> {
    if emit { print_json(value)?; }
    let charged = charged_line(value);
    if value.get("type").and_then(Value::as_str) != Some("confirmed") || charged.is_some() {
        note_host_decision(HostDecision::Outcome(value.clone()));
    }
    if let Some(line) = charged {
        return Err(format!("{line}; exact outcome evidence was retained"));
    }
    match value.get("type").and_then(Value::as_str) {
        Some("confirmed") => Ok(()),
        Some(kind) => Err(format!(
            "host returned {kind}; exact outcome evidence was retained"
        )),
        None => Err("host outcome JSON has no type; exact evidence was retained".to_owned()),
    }
}

fn encode_signatures(
    host: &Path,
    config: &Path,
    signing: &SigningKey,
    headers: Vec<Vec<u8>>,
    json_path: &Path,
    bin_path: &Path,
) -> Result<()> {
    write_json_new(json_path, &sign_headers(signing, &headers)?)?;
    process(
        host,
        config,
        &[
            OsStr::new("signatures"),
            json_path.as_os_str(),
            bin_path.as_os_str(),
        ],
    )?;
    Ok(())
}

fn write_manifest(directory: &Path, host: &Path, config: &Path, operation: &str) -> Result<()> {
    let config = absolute(config)?;
    let mut manifest = json!({
        "format": "minidregg-resource-client-attempt-v1",
        "operation": operation,
        "host": null,
        "config": utf8_path(&config)?,
        "socket": SOCKET.get().map(|socket| transport::pinned_address(socket)).transpose()?,
        "sshIdentity": ssh_identity()
    });
    if host.as_os_str().is_empty() {
        manifest["hostSha256"] = json!(host_image_sha256(host)?);
    } else {
        let host = absolute(host)?;
        if let Some(sha) = workspace_host_pin(&host) {
            manifest["hostSha256"] = json!(sha);
        }
        manifest["host"] = json!(utf8_path(&host)?);
    }
    if let Some(pins) = client_consent::configured_record()? {
        manifest["localConsent"] = pins;
    }
    write_json_new(&directory.join("attempt.json"), &manifest)
}

/// Select a private SSH transport credential without changing shared ssh config.
fn pin_ssh_identity(path: &Path) -> Result<()> {
    let path = absolute(path)?;
    mini_sdk::private::check_file(&path).map_err(|e| format!("SSH identity: {e}"))?;
    match SSH_IDENTITY.get() {
        Some(existing) if existing != &path => Err("SSH identity differs from the retained transport credential".into()),
        Some(_) => Ok(()),
        None => SSH_IDENTITY.set(path).map_err(|_| "cannot pin SSH identity".into()),
    }
}
fn ssh_identity() -> Option<&'static Path> { SSH_IDENTITY.get().map(PathBuf::as_path) }

/// Pins, for this process, the Host digest a remote workspace or attempt
/// recorded. A second, different pin within one process is refused.
#[cfg(unix)]
fn pin_remote_host(sha: &str) -> Result<()> {
    if sha.len() != 64 || !mini_sdk::hex::is_lower(sha) {
        return Err("Host SHA-256 must be 64 lowercase hex digits".into());
    }
    match EXPECTED_HOST_SHA.get() {
        Some(existing) if existing != sha => Err("pinned Host SHA-256 differs within one process".into()),
        Some(_) => Ok(()),
        None => EXPECTED_HOST_SHA
            .set(sha.to_owned())
            .map_err(|_| "cannot pin the remote Host SHA-256".into()),
    }
}

struct Observed {
    signed: PathBuf,
}

/// The CLI's side of `mini_sdk::flow`: this process's codec child and consent provider
/// (`client_consent`) and its transport (`process`: the pinned socket session, or a one-shot
/// local Host). The order of steps, the signed bytes and the attempt layout are the SDK's.
pub(crate) struct CliHost<'a> {
    pub(crate) host: &'a Path,
    pub(crate) config: &'a Path,
}

impl mini_sdk::flow::Local for CliHost<'_> {
    fn author(&mut self, kind: &str, input: &Path, output: &Path) -> mini_sdk::Result<()> {
        Ok(author(self.host, self.config, OsStr::new(kind), input, output)?)
    }
    fn inspect(&mut self, kind: &str, input: &Path, output: &Path) -> mini_sdk::Result<Value> {
        Ok(inspect(self.host, self.config, kind, input, output)?)
    }
    fn signatures(&mut self, json: &Path, output: &Path) -> mini_sdk::Result<()> {
        Ok(host_files(self.host, self.config, &[Path::new("signatures"), json, output])?)
    }
    fn observe_assemble(&mut self, challenge: &Path, signatures: &Path, output: &Path) -> mini_sdk::Result<()> {
        Ok(host_files(self.host, self.config, &[Path::new("observe-assemble"), challenge, signatures, output])?)
    }
    fn assemble(&mut self, plan: &Path, signatures: &Path, output: &Path) -> mini_sdk::Result<()> {
        Ok(host_files(self.host, self.config, &[Path::new("assemble"), plan, signatures, output])?)
    }
    fn consent_intent(&mut self, intent: &Path, key: &[u8]) -> mini_sdk::Result<Vec<u8>> {
        Ok(client_consent::intent(self.host, self.config, intent, key)?)
    }
    fn consent_observation(&mut self, intent: &Path, signature: &Path, challenge: &Path, key: &[u8]) -> mini_sdk::Result<Vec<Vec<u8>>> {
        Ok(client_consent::observation(self.host, self.config, intent, signature, challenge, key)?)
    }
    fn consent_plan(&mut self, intent: &Path, plan: &Path, key: &[u8]) -> mini_sdk::Result<Vec<Vec<u8>>> {
        Ok(client_consent::plan(self.host, self.config, intent, plan, key)?)
    }
}

impl mini_sdk::flow::Operator for CliHost<'_> {
    /// The transport turns a marker frame into an error it has already classified and noted
    /// (`socket_process`, `HostDecision::is_refusal`), so what comes back here is an answer.
    fn request(&mut self, request: mini_sdk::flow::Request, inputs: &[&Path], output: &Path) -> mini_sdk::Result<mini_sdk::flow::Answered> {
        let mut arguments = vec![Path::new(request.verb())];
        arguments.extend_from_slice(inputs);
        arguments.push(output);
        host_files(self.host, self.config, &arguments)?;
        Ok(mini_sdk::flow::Answered::Answer)
    }
}

/// The member typed the command: that is the release. The consent provider has already limited
/// the headers to what the retained intent permits for this plan.
fn command_release(_: &mini_sdk::flow::Sealing<'_>) -> mini_sdk::Result<()> {
    Ok(())
}

fn authorize_observation(
    host: &Path,
    config: &Path,
    intent: &Path,
    intent_kind: &OsStr,
    signing: &SigningKey,
    directory: &Path,
) -> Result<Observed> {
    note_signer(host, config, intent, intent_kind, signing);
    let source = if intent_kind == OsStr::new("binary") {
        mini_sdk::flow::Source::Binary(intent)
    } else {
        mini_sdk::flow::Source::Authored { kind: intent_kind.to_str().ok_or("intent kind must be UTF-8")?, path: intent }
    };
    let mut cli = CliHost { host, config };
    let signed = mini_sdk::flow::Flow { dir: directory, host: &mut cli, signer: signing }.observe(source)?;
    Ok(Observed { signed })
}

/// Observe, prepare, sign, assemble and (unless `prepare_only`) submit one
/// intent under the exact attempt `directory`. A Host `stale-root` (the state
/// moved between the challenge and its use) re-plans the SAME intent with a
/// fresh observation in the same attempt path (`replan`); the superseded plan
/// is kept under `directory/replanned/`.
fn submit(
    host: &Path,
    config: &Path,
    intent: &Path,
    intent_kind: &OsStr,
    key: &Path,
    directory: &Path,
    prepare_only: bool,
) -> Result<()> {
    create_dir(directory)?;
    replan::replan(
        "submit",
        || submit_once(host, config, intent, intent_kind, key, directory, prepare_only, None, true),
        replan::stale_root,
        |number| replan::retire_attempt(directory, number),
    )
}

/// A guarded attempt preserves one exact admission prefix. It deliberately
/// bypasses ordinary stale-root replanning; recovery needs fresh native proof.
fn submit_with_continuity(
    host: &Path, config: &Path, intent: &Path, intent_kind: &OsStr,
    key: &Path, directory: &Path, prepare_only: bool, descriptor: Option<&Path>,
) -> Result<()> {
    let Some(descriptor) = descriptor else {
        return submit(host, config, intent, intent_kind, key, directory, prepare_only);
    };
    if SOCKET.get().is_none() {
        return Err("provider continuity requires --socket".into());
    }
    create_dir(directory)?;
    #[cfg(unix)] {
        use std::os::unix::fs::PermissionsExt;
        fs::set_permissions(directory, fs::Permissions::from_mode(0o700))
            .map_err(|e| format!("cannot protect continuity attempt: {e}"))?;
    }
    submit_once(host, config, intent, intent_kind, key, directory, prepare_only, Some(descriptor), true)
}

fn submit_once(
    host: &Path,
    config: &Path,
    intent: &Path,
    intent_kind: &OsStr,
    key: &Path,
    directory: &Path,
    prepare_only: bool,
    provider_continuity: Option<&Path>,
    emit_outcome: bool,
) -> Result<()> {
    #[cfg(unix)]
    let continuity = receipt_continuity::begin_attempt(directory)?;
    // Until the seal every file of this attempt is a cache of its seal record: staged and linked
    // without its own fsync (`mini_sdk::phase`). The seal ends the scope; so does any early return.
    let _caches = mini_sdk::phase::CacheScope::enter(directory)?;
    let retained_intent = directory.join(if intent_kind == OsStr::new("binary") {
        "intent-source.bin"
    } else {
        "intent.json"
    });
    copy_new(intent, &retained_intent)?;
    let retained_config = directory.join("config.json");
    copy_new(config, &retained_config)?;
    write_manifest(directory, host, &retained_config, "submit")?;
    let signing = read_secret(key)?;
    let observed = authorize_observation(
        host,
        &retained_config,
        &retained_intent,
        intent_kind,
        &signing,
        directory,
    )?;
    let mut cli = CliHost { host, config: &retained_config };
    let mut flow = mini_sdk::flow::Flow { dir: directory, host: &mut cli, signer: &signing };
    let plan_bin = flow.prepare(&observed.signed)?;
    let plan_json = directory.join("plan.json");
    let (prepared_bin, prepared_json) = if provider_continuity.is_some() {
        // Preserve the existing plan.bin prepare-refusal contract. Only a
        // successful prepare becomes the immutable original guarded plan.
        let (original_bin, original_json) = (directory.join("original-plan.bin"), directory.join("original-plan.json"));
        fs::hard_link(&plan_bin, &original_bin)
            .map_err(|e| format!("cannot retain original continuity plan: {e}"))?;
        fs::remove_file(&plan_bin)
            .map_err(|e| format!("cannot move original continuity plan: {e}"))?;
        (original_bin, original_json)
    } else {
        (plan_bin.clone(), plan_json.clone())
    };
    let presentation = flow.present(&prepared_bin, &prepared_json)?;
    if provider_continuity.is_some() {
        sync_retained_call(directory, &prepared_bin)?;
        sync_retained_call(directory, &prepared_json)?;
    }
    #[cfg(unix)]
    if let Some(descriptor) = provider_continuity {
        if let Err(error) = provider_continuity::guard(
            host, &retained_config, descriptor, directory,
            &prepared_bin, &presentation, &plan_bin, &plan_json,
        ) {
            let retained = provider_continuity::retain_rejection(directory, &retained_intent);
            // This return is the positive control-flow guarantee recorded
            // by the marker: no transaction signing or submit follows it.
            return Err(match retained {
                Ok(()) => error,
                Err(retention) => format!("{error}; cannot retain continuity rejection: {retention}"),
            });
        }
    }
    #[cfg(not(unix))]
    if provider_continuity.is_some() {
        let _ = presentation;
        return Err("provider continuity requires Unix sockets".into());
    }
    flow.seal(&plan_bin, &mut command_release)?;
    if prepare_only {
        return Ok(());
    }
    let (outcome, _answered) = flow.transmit(
        mini_sdk::flow::Request::Submit,
        &directory.join("outcome.bin"),
        &directory.join("outcome.json"),
    )?;
    #[cfg(unix)]
    receipt_continuity::finish_attempt(continuity, &outcome, false)?;
    confirmed_outcome(&outcome, emit_outcome)
}

/// A Host refusal as data: `Ok(Err(line))` when the Host refused the request
/// (`refused: REASON: ...`, from the Host's own decoding of its frame),
/// `Err` for a client failure. Clear the decision slot before the request.
pub(crate) fn host_decided<T>(result: Result<T>) -> Result<std::result::Result<T, String>> {
    match result {
        Ok(value) => Ok(Ok(value)),
        // Only a decoded refusal is the Host's refusal; an undecided 255 frame stays an error
        // (`HostDecision::is_refusal`), so no caller reads it as "refused, try another way".
        Err(error) => match take_host_decision() {
            Some(decision @ HostDecision::Frame { .. }) if decision.is_refusal() => Ok(Err(
                decision.outcome().and_then(refusal_line).unwrap_or_else(|| "refused: unnamed".into()))),
            _ => Err(error),
        },
    }
}

/// `host_decided`, keeping a refused frame's exact bytes at `path` first, so
/// `why` (K-INSPECT-VIEWS) can explain the refusal from the Host's own frame.
pub(crate) fn host_decided_keeping<T>(
    result: Result<T>,
    path: &Path,
) -> Result<std::result::Result<T, String>> {
    if result.is_err() {
        if let Some(decision) = take_host_decision() {
            if let HostDecision::Frame { encoded, .. } = &decision {
                if !path.exists() {
                    create_private(path, encoded)?;
                }
            }
            note_host_decision(decision);
        }
    }
    host_decided(result)
}

/// P-AFFORDANCES: the Host's judgement of one intent, without submitting it.
/// Plans it exactly as `submit` does (observe, op 1), signs the plan, and asks
/// the Host to dry-run that plan (op 130: assemble and submit over a Store
/// writer that never appends). `Ok(None)` is admitted; `Ok(Some(line))` is the
/// Host's own refusal line (`refused: REASON: ...`), from the Host's decoding of
/// its frame; a client failure is `Err`.
pub(crate) fn dry_run(
    host: &Path,
    config: &Path,
    intent: &Path,
    intent_kind: &OsStr,
    key: &Path,
    directory: &Path,
) -> Result<Option<String>> {
    create_dir(directory)?;
    let retained_intent = directory.join(if intent_kind == OsStr::new("binary") {
        "intent-source.bin"
    } else {
        "intent.json"
    });
    copy_new(intent, &retained_intent)?;
    let retained_config = directory.join("config.json");
    copy_new(config, &retained_config)?;
    write_manifest(directory, host, &retained_config, "dry-run")?;
    let signing = read_secret(key)?;
    take_host_decision();
    let observed = match host_decided_keeping(authorize_observation(
        host,
        &retained_config,
        &retained_intent,
        intent_kind,
        &signing,
        directory,
    ), &directory.join("refusal.frame"))? {
        Ok(observed) => observed,
        Err(line) => return Ok(Some(line)),
    };
    let mut cli = CliHost { host, config: &retained_config };
    let mut flow = mini_sdk::flow::Flow { dir: directory, host: &mut cli, signer: &signing };
    let plan_bin = match host_decided_keeping(flow.prepare(&observed.signed).map_err(String::from),
        &directory.join("refusal.frame"))? {
        Ok(plan_bin) => plan_bin,
        Err(line) => return Ok(Some(line)),
    };
    flow.present(&plan_bin, &directory.join("plan.json"))?;
    let signatures_bin = flow.sign(&plan_bin, &mut command_release)?;
    match host_decided_keeping(host_files(
        host,
        &retained_config,
        &[
            Path::new("dry-run"),
            &observed.signed,
            &signatures_bin,
            &directory.join("dry-run-plan.bin"),
        ],
    ), &directory.join("refusal.frame"))? {
        Ok(()) => Ok(None),
        Err(line) => Ok(Some(line)),
    }
}

/// Whether the Host answers its own `stale-root` to the signed observation a
/// refused birth authoring generation retained: the observation is presented
/// to `query` once more, its answer kept as `stale-probe.view` or the refusal
/// recorded. An answered probe means the refusal was not the timer race; a
/// generation is probed at most once.
#[cfg(unix)]
pub(crate) fn observation_stale(host: &Path, config: &Path, generation: &Path) -> bool {
    let probe = generation.join("stale-probe.view");
    let signed = generation.join("factory-observation.bin");
    if probe.exists() || !signed.is_file() {
        return false;
    }
    let earlier = take_host_decision();
    let answered = host_files(host, config, &[Path::new("query"), &signed, &probe]);
    let decision = take_host_decision();
    if answered.is_err() {
        let _ = crate::fsio::replace_public(&probe, format!("{decision:?}\n").as_bytes());
    }
    if let Some(earlier) = earlier {
        note_host_decision(earlier);
    }
    answered.is_err() && replan::is_stale_root(decision.as_ref())
}

fn query_presentation_kind(view: &str, presentation: Option<&str>) -> Result<String> {
    if !matches!(
        view,
        "resource" | "resource-scope" | "policy" | "capability" | "who" | "since" | "at" | "backlinks" | "links"
    ) {
        return Err(
            "--view must be resource, resource-scope, policy, capability, who, since, at, backlinks, or links"
                .to_owned(),
        );
    }
    match presentation {
        None => Ok(format!("view-{view}")),
        Some("fn-inbox-resource") if view == "resource" => Ok("fn-inbox-resource".to_owned()),
        _ => Err("--presentation fn-inbox-resource requires --view resource".to_owned()),
    }
}

/// One signed read. A Host `stale-root` between the challenge and the query
/// observes again (`replan`); a read commits nothing.
fn query_retained(
    host: &Path,
    config: &Path,
    intent: &Path,
    intent_kind: &OsStr,
    key: &Path,
    inspection_kind: &str,
    directory: &Path,
) -> Result<Value> {
    create_dir(directory)?;
    replan::replan(
        "signed read",
        || query_once(host, config, intent, intent_kind, key, inspection_kind, directory),
        replan::stale_root,
        |number| replan::retire_attempt(directory, number),
    )
}

fn query_once(
    host: &Path,
    config: &Path,
    intent: &Path,
    intent_kind: &OsStr,
    key: &Path,
    inspection_kind: &str,
    directory: &Path,
) -> Result<Value> {
    let retained_intent = directory.join(if intent_kind == OsStr::new("binary") {
        "intent-source.bin"
    } else {
        "intent.json"
    });
    copy_new(intent, &retained_intent)?;
    let retained_config = directory.join("config.json");
    copy_new(config, &retained_config)?;
    write_manifest(directory, host, &retained_config, "query")?;
    let signing = read_secret(key)?;
    let observed = authorize_observation(
        host,
        &retained_config,
        &retained_intent,
        intent_kind,
        &signing,
        directory,
    )?;
    let view_bin = directory.join("view.bin");
    let view_json = directory.join("view.json");
    host_files(
        host,
        &retained_config,
        &[Path::new("query"), &observed.signed, &view_bin],
    )?;
    let presented = inspect(
        host,
        &retained_config,
        inspection_kind,
        &view_bin,
        &view_json,
    )?;
    let presented = verify_query_presentation(presented, inspection_kind)?;
    Ok(presented)
}

fn verify_query_presentation(presented: Value, inspection_kind: &str) -> Result<Value> {
    // K-NARROW-HIDE: a resource or at-height view is checked against its own
    // root before it is shown; a view whose opening does not recompute the root
    // is refused, with the signed view retained for inspection.
    let presented = if inspection_kind == "view-resource" || inspection_kind == "view-at" {
        let summary = hiding::verify_view(&presented)?;
        let mut presented = presented;
        if let Some(object) = presented.as_object_mut() {
            object.insert("hiding".to_owned(), summary);
        }
        presented
    } else if inspection_kind == "view-resource-scope" {
        let resource = presented.get("resource").ok_or("resource scope lacks its narrowed resource")?;
        let summary = hiding::verify_view(resource)?;
        let mut presented = presented;
        presented.get_mut("resource").and_then(Value::as_object_mut)
            .ok_or("resource scope payload is not an object")?
            .insert("hiding".to_owned(), summary);
        presented
    } else {
        presented
    };
    if inspection_kind == "fn-inbox-resource"
        && presented.get("type").and_then(Value::as_str) != Some("fn-inbox-resource-summary-v1")
    {
        return Err(
            "host returned an unexpected fn inbox summary type; signed view retained".to_owned(),
        );
    }
    Ok(presented)
}

/// A transport collection retains ordinary individually signed observations.
/// All challenges use one native image; all answers use one native image.
/// Any stale-root replans the whole read-only collection, preserving its targets.
fn query_batch_retained(
    host: &Path, config: &Path, intents: &[(PathBuf, String)], key: &Path,
    directory: &Path,
) -> Result<Vec<(Value, Value, PathBuf)>> {
    if intents.is_empty() || intents.len() > 16 {
        return Err("signed read batch requires 1 through 16 reads".into());
    }
    create_dir(directory)?;
    replan::replan("signed read batch",
        || query_batch_once(host, config, intents, key, directory),
        replan::stale_root, |n| replan::retire_attempt(directory, n))
}

fn batch_author(host: &Path, config: &Path, directory: &Path, stem: &str,
    values: &[Vec<u8>]) -> Result<PathBuf> {
    let source = directory.join(format!("{stem}.json"));
    let encoded = serde_json::to_vec(&values.iter().map(|b| hex(b)).collect::<Vec<_>>())
        .map_err(|e| e.to_string())?;
    write_new(&source, &encoded)?;
    let binary = directory.join(format!("{stem}.bin"));
    author(host, config, OsStr::new("observation-batch"), &source, &binary)?;
    Ok(binary)
}

fn batch_inspect(host: &Path, config: &Path, directory: &Path, stem: &str,
    binary: &Path, count: usize) -> Result<Vec<Vec<u8>>> {
    let value = inspect(host, config, "observation-batch", binary,
        &directory.join(format!("{stem}.json")))?;
    let rows = value.as_array().ok_or("Host batch is not a collection")?;
    if rows.len() != count { return Err("Host batch count differs from signed intents".into()); }
    rows.iter().map(|row| mini_sdk::hex::decode(row.as_str().ok_or("Host batch item is not hex")?).map_err(|e| e.0))
        .collect()
}

fn query_batch_once(
    host: &Path, config: &Path, intents: &[(PathBuf, String)], key: &Path,
    directory: &Path,
) -> Result<Vec<(Value, Value, PathBuf)>> {
    let retained_config = directory.join("config.json");
    copy_new(config, &retained_config)?;
    write_manifest(directory, host, &retained_config, "query")?;
    let signing = read_secret(key)?;
    let mut requests = Vec::new();
    for (n, (intent, _)) in intents.iter().enumerate() {
        let child = directory.join(n.to_string());
        create_dir(&child)?;
        let source = child.join("intent.json");
        copy_new(intent, &source)?;
        let binary = child.join("intent.bin");
        author(host, &retained_config, OsStr::new("intent"), &source, &binary)?;
        let bytes = client_consent::intent(host, &retained_config, &binary, signing.verifying_key().as_bytes())?;
        let signature = signing.sign(&bytes).to_bytes();
        write_new(&child.join("intent-signature.bin"), &signature)?;
        let width: u32 = bytes.len().try_into().map_err(|_| "batch intent too large")?;
        let mut request = width.to_le_bytes().to_vec();
        request.extend(bytes);
        request.extend(signature);
        requests.push(request);
    }
    let request = batch_author(host, &retained_config, directory, "batch-request", &requests)?;
    let challenges = directory.join("batch-challenges.bin");
    host_files(host, &retained_config,
        &[Path::new("challenge-batch"), &request, &challenges])?;
    let challenges = batch_inspect(host, &retained_config, directory,
        "batch-challenges", &challenges, intents.len())?;
    let mut signed_bytes = Vec::new();
    let mut presentations = Vec::new();
    for (n, challenge) in challenges.iter().enumerate() {
        let child = directory.join(n.to_string());
        let binary = child.join("challenge.bin");
        write_new(&binary, challenge)?;
        let presented = inspect(host, &retained_config, "challenge", &binary,
            &child.join("challenge.json"))?;
        // All source-created singleton challenges must have exactly one image.
        if let Some(first) = presentations.first() {
            let first: &Value = first;
            for field in ["domain", "semantics", "worldRoot", "height", "authorityRoot"] {
                if first.get(field) != presented.get(field) || presented.get(field).is_none() {
                    return Err("Host batch challenges have inconsistent coordinates".into());
                }
            }
        }
        encode_signatures(host, &retained_config, &signing,
            client_consent::observation(host, &retained_config, &child.join("intent.bin"),
                &child.join("intent-signature.bin"), &binary, signing.verifying_key().as_bytes())?, &child.join("observation-signatures.json"),
            &child.join("observation-signatures.bin"))?;
        let signed = child.join("signed-observation.bin");
        host_files(host, &retained_config, &[Path::new("observe-assemble"), &binary,
            &child.join("observation-signatures.bin"), &signed])?;
        signed_bytes.push(fs::read(&signed).map_err(|e| e.to_string())?);
        presentations.push(presented);
    }
    let signed = batch_author(host, &retained_config, directory, "batch-signed", &signed_bytes)?;
    // The parent query refusal artifact binds the whole exact collection.
    copy_new(&signed, &directory.join("signed-observation.bin"))?;
    let views = directory.join("view.bin");
    host_files(host, &retained_config, &[Path::new("query-batch"), &signed, &views])?;
    let views = batch_inspect(host, &retained_config, directory, "batch-views", &views, intents.len())?;
    let mut result = Vec::new();
    for (n, ((_, inspection), bytes)) in intents.iter().zip(views).enumerate() {
        let child = directory.join(n.to_string());
        let binary = child.join("view.bin");
        write_new(&binary, &bytes)?;
        let presented = inspect(host, &retained_config, inspection, &binary, &child.join("view.json"))?;
        result.push((verify_query_presentation(presented, inspection)?,
            presentations[n].clone(), child.join("signed-observation.bin")));
    }
    Ok(result)
}

fn query(
    host: &Path,
    config: &Path,
    intent: &Path,
    intent_kind: &OsStr,
    key: &Path,
    inspection_kind: &str,
    directory: &Path,
) -> Result<()> {
    print_json(&query_retained(
        host,
        config,
        intent,
        intent_kind,
        key,
        inspection_kind,
        directory,
    )?)
}

fn manifest_paths(directory: &Path) -> Result<(PathBuf, PathBuf, Option<PathBuf>)> {
    let path = directory.join("attempt.json");
    let bytes = fsio::read_bounded(&path, 1 << 20)?;
    let value: Value = serde_json::from_slice(&bytes)
        .map_err(|error| format!("invalid {}: {error}", path.display()))?;
    if value.get("format").and_then(Value::as_str) != Some("minidregg-resource-client-attempt-v1") {
        return Err(format!("unsupported attempt manifest {}", path.display()));
    }
    if let Some(identity) = value.get("sshIdentity").and_then(Value::as_str) {
        pin_ssh_identity(Path::new(identity))?;
    }
    if let Some(pins) = value.get("localConsent") { client_consent::pin_record(pins)?; }
    let host = match value.get("host") {
        Some(Value::String(host)) => {
            let host = PathBuf::from(host);
            if let Some(sha) = value.get("hostSha256").and_then(Value::as_str) {
                pin_workspace_host(&host, sha)?;
            }
            host
        }
        Some(Value::Null) => {
            let sha = value
                .get("hostSha256")
                .and_then(Value::as_str)
                .ok_or("remote attempt manifest has no Host SHA-256")?;
            pin_remote_host(sha)?;
            PathBuf::new()
        }
        _ => return Err("attempt manifest has no host path".to_owned()),
    };
    let config = value
        .get("config")
        .and_then(Value::as_str)
        .map(PathBuf::from)
        .ok_or_else(|| "attempt manifest has no config path".to_owned())?;
    let socket = value
        .get("socket")
        .and_then(Value::as_str)
        .map(PathBuf::from);
    Ok((host, config, socket))
}

fn next_retry(directory: &Path) -> Result<(PathBuf, PathBuf)> {
    Ok(mini_sdk::store::AttemptDir(directory.to_path_buf()).next_retry()?)
}

fn retry(directory: &Path, mode: &str, direct: bool) -> Result<()> {
    if !matches!(mode, "submit" | "lookup") {
        return Err("--mode must be submit or lookup".to_owned());
    }
    // A retained attempt's caches are checked against its seal record before anything (this
    // process, a one-shot Host, the transport) reads them (`mini_sdk::phase`, invariant 3).
    mini_sdk::phase::repair_dir(directory)?;
    let call = directory.join("call.bin");
    if !call.is_file() {
        return Err(format!("attempt has no retained {}", call.display()));
    }
    sync_retained_call(directory, &call)?;
    #[cfg(unix)]
    if let Some(outcome) = receipt_continuity::carry::retry_lookup(directory, mode, direct)? {
        return print_confirmed_outcome(&outcome);
    }
    let (host, config, socket) = manifest_paths(directory)?;
    if !direct && SOCKET.get().is_none() {
        if let Some(socket) = socket {
            let _ = SOCKET.set(socket);
        }
    }
    #[cfg(unix)]
    let continuity = receipt_continuity::begin_attempt(directory)?;
    let (outcome_bin, outcome_json) = next_retry(directory)?;
    let host = &host;
    host_files(host, &config, &[Path::new(mode), &call, &outcome_bin])?;
    let outcome = inspect(host, &config, "outcome", &outcome_bin, &outcome_json)?;
    #[cfg(unix)]
    receipt_continuity::finish_attempt(continuity, &outcome, true)?;
    print_confirmed_outcome(&outcome)
}

#[cfg(unix)]
fn private_consumer_attempt(
    host: &Path,
    config: &Path,
    directory: &Path,
    operation: &str,
) -> Result<PathBuf> {
    crate::fsio::create_private_dir(directory)?;
    let retained_config = directory.join("config.json");
    copy_new(config, &retained_config)?;
    write_manifest(directory, host, &retained_config, operation)?;
    Ok(retained_config)
}

#[cfg(unix)]
fn continuity_reply(value: &Value) -> Result<bool> {
    if value.get("type").and_then(Value::as_str) != Some("minidregg-provider-continuity-v1") {
        return Err("unexpected provider continuity reply type; complete frame retained".into());
    }
    let canonical = |text: &str| -> bool { mini_sdk::decimal::is_canonical_max(text, 80) };
    let decimal = |object: &Value, name: &str| -> Result<()> {
        if object
            .get(name)
            .and_then(Value::as_str)
            .is_some_and(canonical)
        {
            Ok(())
        } else {
            Err(format!("provider continuity reply lacks canonical {name}"))
        }
    };
    decimal(value, "providerResourceId")?;
    if value.get("providerResourceId").and_then(Value::as_str) == Some("0") {
        return Err("provider continuity reply names no provider resource".into());
    }
    decimal(value, "checkedWorldRoot")?;
    decimal(value, "checkedAcceptedCount")?;
    let anchor = value
        .get("anchor")
        .ok_or("provider continuity reply lacks anchor")?;
    if anchor.get("type").and_then(Value::as_str) != Some("verified-mini-native-prefix-v1") {
        return Err("provider continuity anchor has unexpected type".into());
    }
    for name in ["transactionId", "eventId", "acceptedCount", "worldRoot"] {
        decimal(anchor, name)?;
    }
    let reason = value
        .get("reason")
        .and_then(Value::as_str)
        .ok_or("provider continuity reply lacks reason")?;
    match (
        value.get("status").and_then(Value::as_str),
        value.get("continuous").and_then(Value::as_bool),
    ) {
        (Some("confirmed"), Some(true)) if reason.is_empty() => Ok(true),
        (Some("refused"), Some(false)) if !reason.is_empty() => Ok(false),
        _ => Err("inconsistent provider continuity status and verdict".into()),
    }
}

#[cfg(unix)]
fn continuity(
    host: &Path,
    config: &Path,
    call: &Path,
    outcome: &Path,
    directory: &Path,
) -> Result<()> {
    let socket = SOCKET.get().ok_or("continuity requires --socket")?;
    let call_bytes = fsio::read_bounded(call, transport::HOST_MAX_FRAME)?;
    let outcome_bytes = fsio::read_bounded(outcome, 1024)?;
    if call_bytes.len() + outcome_bytes.len() + 5 > transport::HOST_MAX_FRAME {
        return Err(
            "original reserve call/outcome exceeds provider continuity frame bounds".into(),
        );
    }
    let retained_config = private_consumer_attempt(host, config, directory, "continuity")?;
    create_private(&directory.join("call.bin"), &call_bytes)?;
    create_private(&directory.join("outcome.bin"), &outcome_bytes)?;
    sync_directory_ancestors(directory)?;
    let payload = provider_continuity::request_payload(&call_bytes, &outcome_bytes, None, false)?;
    let frame = session_invoke(host, socket, &retained_config, mini_sdk::host_operations::PROVIDER_CONTINUITY, &payload)?;
    write_new(&directory.join("reply.frame"), &frame)?;
    if is_outcome_frame(frame[0]) {
        return Err("Host refused provider continuity; complete frame retained".into());
    }
    let value: Value = serde_json::from_slice(&frame[1..])
        .map_err(|e| format!("invalid provider continuity JSON; complete frame retained: {e}"))?;
    write_new(&directory.join("continuity.json"), &frame[1..])?;
    let continuous = continuity_reply(&value)?;
    print_json(&value)?;
    if continuous {
        Ok(())
    } else {
        Err("provider continuity refused; typed reply and exact inputs retained".into())
    }
}

/// The Host's public enrollment view (op 112, docs/PAY.md §11.5), decoded by the same Host (op 8
/// `inspect pay-enrolment-view`) and printed as its JSON. This is the roster sync's input
/// (`render-authorized-keys.sh --view required`): it needs only the socket, whose own config
/// pin (`SOCKET.config`, written by `mini serve`) is the default envelope config, and the Host
/// image the socket serves (`--host HOST`, or its `--host-sha256`) pins the v2 envelope (v1 is retired).
#[cfg(unix)]
fn enrollment_view(socket: &Path, config: &Path, host_sha256: &str) -> Result<()> {
    let frame = transport::invoke_pinned(socket, config, host_sha256, mini_sdk::host_operations::PAY_ENROLLMENT_VIEW, &[])?;
    let body = match frame.as_slice() {
        [112, body @ ..] => body,
        [code, rest @ ..] => {
            return Err(format!(
                "the Host refused the enrollment view (frame {code}): {}",
                String::from_utf8_lossy(rest)
            ))
        }
        [] => return Err("the Host returned an empty frame".into()),
    };
    let kind = b"pay-enrolment-view";
    let mut request = (kind.len() as u16).to_le_bytes().to_vec();
    request.extend_from_slice(kind);
    request.extend_from_slice(body);
    let inspected = transport::invoke_pinned(socket, config, host_sha256, mini_sdk::host_operations::INSPECT, &request)?;
    let json = match inspected.as_slice() {
        [8, json @ ..] => json,
        _ => return Err("the Host could not decode its own enrollment view".into()),
    };
    let value: Value =
        serde_json::from_slice(json).map_err(|e| format!("invalid enrollment view JSON: {e}"))?;
    if value.get("view").and_then(Value::as_str) != Some("DREGG/PAY/ENROLMENT-VIEW/v3") {
        return Err("the Host's enrollment view is not DREGG/PAY/ENROLMENT-VIEW/v3".into());
    }
    print_json(&value)
}

fn run(mut args: Args) -> Result<()> {
    #[cfg(unix)]
    // The listener creator of an activated operator route (a resident's or an
    // agent controller's: systemd, uid 0) is pinned explicitly, by flag or by
    // the root-owned unit's MINI_OPERATOR_PEER_UID, which every child `mini`
    // of a controller inherits. Never inferred from the path's owner.
    if let Some(uid) = args.optional("operator-peer-uid").or_else(|| std::env::var_os("MINI_OPERATOR_PEER_UID")) {
        let uid = uid.to_str().and_then(|n| n.parse::<u32>().ok()).ok_or("operator peer UID must be a u32 decimal")?;
        operator_peer::configure(uid)?;
    }
    replan::configure(args.optional("replan-max"), args.optional("replan-window"))?;
    if let Some(identity) = args.optional("ssh-identity") { pin_ssh_identity(&path(identity))?; }
    let mut socket_argument = args.optional("socket");
    #[cfg(unix)]
    if let Some(destination) = args.optional("remote") {
        if socket_argument.is_some() {
            return Err("--remote and --socket name two transports; pass one".into());
        }
        let destination = destination
            .into_string()
            .map_err(|_| "--remote must be UTF-8")?;
        socket_argument = Some(transport::remote_address(&destination)?.into_os_string());
    }
    #[cfg(unix)]
    if let Some(sha) = args.optional("host-sha256") {
        pin_remote_host(sha.to_str().ok_or("--host-sha256 must be UTF-8")?)?;
    }
    if let Some(socket) = &socket_argument {
        let _ = SOCKET.set(path(socket.clone()));
    }
    #[cfg(unix)]
    if socket_argument.as_deref().is_some_and(|s| transport::is_remote(Path::new(s)))
        && !REMOTE_COMMANDS.contains(&args.command.to_string_lossy().as_ref())
    {
        return Err(format!(
            "{} is not a participant command; --remote reaches only the public socket's participant surface ({})",
            args.command.to_string_lossy(),
            REMOTE_COMMANDS.join(", ")
        ));
    }
    match args.command.to_string_lossy().as_ref() {
        #[cfg(unix)]
        "join" if args.peek("memo-version").and_then(OsStr::to_str)==Some("v2") => join_solana_v2::run(args),
        #[cfg(unix)]
        "join" if matches!(args.peek("mode").and_then(OsStr::to_str), Some("solana" | "wait" | "renew")) => join_solana::run(args),
        #[cfg(unix)]
        "join" => participant_enrollment::join(args),
        #[cfg(unix)]
        "socket-proxy" => {
            args.finish()?;
            let socket = SOCKET.get().ok_or("socket-proxy requires --socket")?;
            proxy::serve(socket)
        }
        #[cfg(unix)]
        "workspace" => {
            // One `mini workspace` action publishes 30-40 custody files; their directory fsyncs
            // are coalesced to the barriers (every Host request, and here before exit), each file
            // still complete or absent (`mini_sdk::durable`).
            mini_sdk::durable::defer_directory_syncs();
            let result = workspace::run(args);
            let barrier = transport::durability_barrier();
            result.and(barrier)
        }
        #[cfg(unix)]
        "app-interface" => app_interface::run(args),
        "member" => member::run(args),
        #[cfg(unix)]
        "web" => web::run(args),
        #[cfg(unix)]
        "operation-proof" => append_proof::run(args),
        #[cfg(unix)]
        "enroll" => participant_enrollment::run(args),
        "clock" => clock::run(args),
        "checkpoint" => checkpoint::run(args),
        "export-world" => world_export::run(args),
        #[cfg(unix)]
        "private-compute" => private_compute::run(args),
        #[cfg(unix)]
        "job" => job::run(args),
        "activity" => activity::run(args),
        "bend" => bend::run(args),
        "seat" => seat::run(args),
        #[cfg(unix)]
        "shell" => shell::run(args),
        // mini key carries two verb families: the credential store (keys.rs) and the
        // owner-derived hiding keys (K-NARROW-HIDE, the arm below). Route by --action.
        #[cfg(unix)]
        "key" if !matches!(
            args.peek("action").and_then(OsStr::to_str),
            Some("cell-blinding" | "derive-salt")
        ) => keys::run(args),
        // The credential service moved into the key broker (native/mini-keys);
        // the old verbs refuse by name rather than reading a seal key.
        gone @ ("key-service" | "key-service-config" | "key-namespace") => Err(format!(
            "mini {gone} is gone: the key broker holds credential custody (mini-keys serve; the ssh credential command is mini-keys relay; namespace metadata is mini-keys namespace)"
        )),
        "fleet" => fleet::run(args),
        #[cfg(unix)]
        "apps" => apps::run(args),
        #[cfg(unix)]
        "apps-front" => apps::front::run(args),
        #[cfg(unix)]
        "apps-worker" => apps::worker::run(args),
        #[cfg(unix)]
        "mix" => pq_mailbox::run(args),
        #[cfg(unix)]
        "mix-live" => cohort_tcp::run(args),
        #[cfg(unix)]
        "adopt-next-key" => key_adoption::run(args),
        #[cfg(unix)]
        "rotate-key" => key_rotation::rotate_key(args),
        #[cfg(unix)]
        "key-status" => key_rotation::key_status(args),
        #[cfg(unix)]
        "credit" => credit::run(args),
        "hermes-handoff" => hermes_handoff::run(args),
        #[cfg(unix)]
        "story-law" => story::law_command(args),
        "well" => well::run(args),
        "pay" => pay::run(args),
        #[cfg(unix)]
        "pay-claim" => pay_claim::run(args),
        #[cfg(unix)]
        "enrollment-bootstrap" => enrollment_bootstrap::run(args),
        "enrollment-view" => {
            let config = args.optional("config").map(path);
            let host = args.optional("host").map(path);
            let sha = args.optional("host-sha256").map(|s| s.into_string().map_err(|_| "--host-sha256 must be UTF-8".to_owned())).transpose()?;
            args.finish()?;
            let socket = SOCKET.get().ok_or("enrollment-view requires --socket")?;
            let config = config.unwrap_or_else(|| socket.with_extension("config"));
            let host_sha256 = match (host, sha) {
                (Some(host), None) => host_image_sha256(&host)?,
                (None, Some(sha)) => sha,
                _ => return Err("enrollment-view requires exactly one of --host HOST or --host-sha256 HEX (the v2 envelope pins the Host image)".to_owned()),
            };
            enrollment_view(socket, &config, &host_sha256)
        }
        #[cfg(unix)]
        "selected-exchange" => {
            let phase = args.required("phase")?;
            let phase = phase
                .to_str()
                .ok_or("selected-exchange phase must be UTF-8")?;
            let contract = path(args.required("contract")?);
            let state = path(args.required("state-dir")?);
            args.finish()?;
            selected_exchange::run(phase, &contract, &state)
        }
        "serve" => {
            let host = path(args.required("host")?);
            let config = path(args.required("config")?);
            args.finish()?;
            let socket = SOCKET.get().ok_or("serve requires --socket")?;
            #[cfg(unix)]
            {
                transport::serve(socket, &host, &config)
            }
            #[cfg(not(unix))]
            {
                Err("persistent host sessions require Unix sockets".to_owned())
            }
        }
        #[cfg(unix)]
        "consent-full-ready" => {
            let host = path(args.required("host")?);
            let config = path(args.required("config")?);
            args.finish()?;
            client_consent::full_ready(&host, &config)?;
            println!("{{\"type\":\"mini-consent-full-readiness-v1\",\"ready\":true}}");
            Ok(())
        }
        #[cfg(unix)]
        "consent-resident" => {
            let consent = path(args.required("consent")?);
            let settings = path(args.required("settings")?);
            args.finish()?;
            client_consent::resident(consent, settings)
        }
        #[cfg(unix)]
        "codec-resident" => {
            // HOT-PATH 2a: one storeless codec Host per image+settings binding for every `mini`
            // process of this user, started by the first `local_frame` that finds none listening.
            let host = path(args.required("host")?);
            let settings = path(args.required("settings")?);
            args.finish()?;
            client_consent::codec_resident(host, settings)
        }
        #[cfg(unix)]
        "serve-operator" => {
            let host = path(args.required("host")?);
            let config = path(args.required("config")?);
            let peers = args
                .repeated("peer-uid")
                .into_iter()
                .map(|uid| uid.to_str().and_then(|uid| uid.parse::<u32>().ok()).ok_or("--peer-uid is a decimal uid"))
                .collect::<std::result::Result<Vec<u32>, _>>()?;
            args.finish()?;
            let socket = SOCKET.get().ok_or("serve-operator requires --socket")?;
            transport::serve_operator(socket, &host, &config, &peers)
        }
        #[cfg(unix)]
        "serve-public-proxy" => {
            let upstream = path(args.required("upstream")?);
            let config = path(args.required("config")?);
            let group = args
                .optional("socket-gid")
                .map(|gid| gid.to_str().and_then(|gid| gid.parse::<u32>().ok()).ok_or("--socket-gid is a decimal gid"))
                .transpose()?;
            let controller = args.optional("controller-uid")
                .map(|uid| uid.to_str().and_then(|uid| uid.parse::<u32>().ok()).ok_or("--controller-uid is a decimal UID"))
                .transpose()?;
            args.finish()?;
            let socket = SOCKET.get().ok_or("serve-public-proxy requires --socket")?;
            public_proxy::serve(socket, &upstream, &config, group, controller)
        }
        #[cfg(target_os = "linux")]
        "serve-resident-operator-proxy" => {
            let upstream = path(args.required("upstream")?);
            let config = path(args.required("config")?);
            let uid = args.required("resident-uid")?.to_str().and_then(|n| n.parse::<u32>().ok())
                .ok_or("resident UID must be a decimal u32")?;
            args.finish()?;
            let socket = SOCKET.get().ok_or("serve-resident-operator-proxy requires --socket")?;
            public_proxy::serve_resident_activated(socket, &upstream, &config, uid)
        }
        #[cfg(target_os = "linux")]
        "serve-agent-operator-proxy" => {
            let upstream = path(args.required("upstream")?);
            let config = path(args.required("config")?);
            let uid = args.required("controller-uid")?.to_str().and_then(|n| n.parse::<u32>().ok())
                .ok_or("controller UID must be a decimal u32")?;
            args.finish()?;
            let socket = SOCKET.get().ok_or("serve-agent-operator-proxy requires --socket")?;
            public_proxy::serve_agent_activated(socket, &upstream, &config, uid)
        }
        #[cfg(target_os = "linux")]
        "serve-controller-consent" => {
            let consent = path(args.required("consent")?);
            let config = path(args.required("config")?);
            let anchors = path(args.required("anchors")?);
            let image = consent_proxy::digest(args.required("consent-sha256")?.to_str().ok_or("consent digest must be UTF-8")?)?;
            let settings = consent_proxy::digest(args.required("config-sha256")?.to_str().ok_or("config digest must be UTF-8")?)?;
            let uid = args.required("controller-uid")?.to_str().and_then(|n|n.parse::<u32>().ok()).ok_or("controller UID must be a decimal u32")?;
            // Seconds with no connection before the service ends (socket activation restarts it).
            let idle = match args.optional("idle-seconds") {
                Some(v) => v.to_str().and_then(|n| n.parse::<u64>().ok()).filter(|n| *n > 0)
                    .ok_or("idle seconds must be a positive decimal")?,
                None => mini_sdk::consent::RESIDENT_IDLE_S,
            };
            args.finish()?;
            let socket = SOCKET.get().ok_or("serve-controller-consent requires --socket")?;
            consent_proxy::serve(socket,&consent,&config,image,settings,uid,&anchors,std::time::Duration::from_secs(idle))
        }
        #[cfg(unix)]
        "operator-status" | "drain-operator" => {
            let drain = args.command == OsStr::new("drain-operator");
            let host = path(args.required("host")?);
            let config = path(args.required("config")?);
            let instance = if drain { Some(args.required("instance")?.into_string().map_err(|_| "instance must be UTF-8")?) } else { None };
            let pid = if drain { args.required("pid")?.to_str().ok_or("pid must be UTF-8")?.parse::<u32>().map_err(|_| "invalid process PID")? } else { 0 };
            let timeout = if drain { args.required("timeout-seconds")?.to_str().ok_or("timeout must be UTF-8")?.parse::<u64>().map_err(|_| "invalid timeout")? } else { 0 };
            args.finish()?;
            let socket = SOCKET.get().ok_or("operator control requires --socket")?;
            operator_drain::command(socket, &host, &config, instance.as_deref().map(|instance| (instance, pid, timeout)))
        }
        "provider-continuity" => {
            let host = path(args.required("host")?);
            let config = path(args.required("config")?);
            let attempt = path(args.required("guarded-attempt")?);
            let directory = path(args.required("dir")?);
            args.finish()?;
            #[cfg(unix)]
            {
                provider_continuity::resolve_attempt(&host, &config, &attempt, &directory)
            }
            #[cfg(not(unix))]
            {
                Err("provider continuity requires Unix sockets".into())
            }
        }
        "continuity" => {
            let host = path(args.required("host")?);
            let config = path(args.required("config")?);
            let call = path(args.required("call")?);
            let outcome = path(args.required("outcome")?);
            let directory = path(args.required("dir")?);
            args.finish()?;
            #[cfg(unix)]
            {
                continuity(&host, &config, &call, &outcome, &directory)
            }
            #[cfg(not(unix))]
            {
                Err("provider continuity requires Unix sockets".to_owned())
            }
        }
        "meter" => {
            let host = path(args.required("host")?);
            let config = path(args.required("config")?);
            let metadata = path(args.required("metadata")?);
            let request = path(args.required("request")?);
            let response = path(args.required("response")?);
            let directory = path(args.required("dir")?);
            args.finish()?;
            #[cfg(unix)]
            {
                let socket = SOCKET.get().ok_or("meter requires --socket")?;
                meter::meter(
                    &host, &config, socket, &metadata, &request, &response, &directory,
                )
            }
            #[cfg(not(unix))]
            {
                Err("provider metering requires Unix sockets".to_owned())
            }
        }
        "store" => store_run(args),
        "audit" => {
            if SOCKET.get().is_some() {
                return Err("audit requires direct Host/Main CLI".to_owned());
            }
            let host = path(args.required("host")?);
            let config = path(args.required("config")?);
            args.finish()?;
            let output = process(&host, &config, &[OsStr::new("audit")])?;
            io::stdout()
                .write_all(&output.stdout)
                .map_err(|e| format!("cannot print host output: {e}"))
        }
        "profile" | "describe" => {
            let command = args.command.clone();
            let host = path(args.required("host")?);
            let config = path(args.required("config")?);
            args.finish()?;
            let output = process(&host, &config, &[command.as_os_str()])?;
            io::stdout()
                .write_all(&output.stdout)
                .map_err(|e| format!("cannot print host output: {e}"))
        }
        // The hybrid (X25519 + ML-KEM-768) public key a sponsor's escrow is
        // sealed to, derived from the same seed the signing key file holds.
        "enc-public" => {
            if socket_argument.is_some() {
                return Err("enc-public does not use a host socket".to_owned());
            }
            let secret = path(args.required("secret")?);
            args.finish()?;
            println!("{}", workspace::roomkey::enc_public_hex(&secret)?);
            Ok(())
        }
        // The 32-byte id of that key: what `whoami` shows and a room inviter
        // uses to select an already-published signed record.
        "enc-key-id" => {
            if socket_argument.is_some() {
                return Err("enc-key-id does not use a host socket".to_owned());
            }
            let secret = path(args.required("secret")?);
            args.finish()?;
            println!("{}", workspace::roomkey::enc_key_id_hex(&secret)?);
            Ok(())
        }
        // D3 (b): the sponsor opens a friend's escrowed seed (written by
        // `keygen --escrow-to-sponsor`) into a new key file, which signs as the
        // friend. Only the sponsor's X25519 key opens it, bound to the subject.
        "escrow-recover" => {
            if socket_argument.is_some() {
                return Err("escrow-recover does not use a host socket".to_owned());
            }
            let escrow = path(args.required("escrow")?);
            let sponsor = path(args.required("sponsor-secret")?);
            let subject = args.required("subject")?;
            let secret = path(args.required("secret")?);
            args.finish()?;
            let subject = subject.to_str().ok_or("--subject must be UTF-8")?.to_owned();
            let wrapped = workspace::private::Wrapped::from_bytes(
                &fs::read(&escrow).map_err(|e| format!("cannot read {}: {e}", escrow.display()))?,
            )?;
            let sponsor_secret =
                workspace::private::derive_enc_key(&*crate::fsio::read_seed(&sponsor)?)?;
            let seed = workspace::private::recover_escrowed_seed(&subject, &sponsor_secret, &wrapped)?;
            if secret.exists() {
                return Err(format!("refusing to replace {}", secret.display()));
            }
            create_private(&secret, &seed[..])?;
            println!("{}", hex(&SigningKey::from_bytes(&seed).verifying_key().to_bytes()));
            Ok(())
        }
        "keygen" => {
            // Refuse a socket named for this command; a session (`mini shell`)
            // may already have pinned one for its other verbs.
            if socket_argument.is_some() {
                return Err("keygen does not use a host socket".to_owned());
            }
            let secret = path(args.required("secret")?);
            let public = path(args.required("public")?);
            let escrow = args.optional("escrow-to-sponsor");
            let escrow_subject = args.optional("escrow-subject");
            let next_to = args.optional("next-to").map(path);
            let without = args.optional("no-prerotation").is_some();
            let hosted = args.optional("hosted").is_some();
            args.finish()?;
            let next = match (next_to, without) {
                (Some(_), true) => {
                    return Err("--next-to and --no-prerotation exclude each other".to_owned())
                }
                (Some(path), false) => NextKey::To(path),
                (None, true) => NextKey::Without,
                (None, false) => NextKey::Beside,
            };
            let escrow = match (escrow, escrow_subject) {
                (None, None) => None,
                (Some(sponsor), Some(subject)) => Some((sponsor, subject)),
                _ => {
                    return Err(
                        "--escrow-to-sponsor and --escrow-subject go together".to_owned(),
                    )
                }
            };
            keygen(&secret, &public, escrow, next, hosted)
        }
        "verify-view" => {
            let view = path(args.required("view")?);
            args.finish()?;
            let bytes = fs::read(&view)
                .map_err(|error| format!("cannot read {}: {error}", view.display()))?;
            let value: Value = serde_json::from_slice(&bytes)
                .map_err(|error| format!("{} is not JSON: {error}", view.display()))?;
            print_json(&hiding::verify_view(&value)?)
        }
        "key" => {
            let action = args.required("action")?;
            let seed = crate::fsio::read_seed(&path(args.required("secret")?))?;
            match action.to_str() {
                Some("cell-blinding") => {
                    // With --heights, the cell's CURRENT blinding: the birth blinding
                    // ratcheted once per write at each height (K-HIDE-ROTATE).
                    let cell = args.required("cell")?;
                    let storage = args.optional("storage");
                    let heights = args.optional("heights");
                    args.finish()?;
                    let cell = cell.to_str().ok_or("--cell must be UTF-8")?;
                    let key = hiding::blinding_key(&seed);
                    match heights {
                        None => println!("{}", hiding::cell_blinding(&key, cell)?),
                        Some(heights) => {
                            let storage = storage.ok_or("--heights needs --storage")?;
                            let heights = hiding::parse_heights(
                                heights.to_str().ok_or("--heights must be UTF-8")?,
                            )?;
                            println!(
                                "{}",
                                hiding::ratcheted_blinding(
                                    &key,
                                    storage.to_str().ok_or("--storage must be UTF-8")?,
                                    cell,
                                    &heights,
                                )?
                            );
                        }
                    }
                    Ok(())
                }
                Some("derive-salt") => {
                    let cell = args.required("cell")?;
                    let storage = args.required("storage")?;
                    let entry = args.required("entry")?;
                    let heights = args.optional("heights");
                    args.finish()?;
                    let entry = crate::decode_hex(
                        entry.to_str().ok_or("--entry must be UTF-8 hex")?,
                    )?;
                    // The heights of the cell's writes since birth, in order: the
                    // salts are keyed by the ratcheted blinding (K-HIDE-ROTATE).
                    let heights = match heights {
                        Some(text) => hiding::parse_heights(
                            text.to_str().ok_or("--heights must be UTF-8")?,
                        )?,
                        None => Vec::new(),
                    };
                    let salt = hiding::owner_salt(
                        &seed,
                        storage.to_str().ok_or("--storage must be UTF-8")?,
                        cell.to_str().ok_or("--cell must be UTF-8")?,
                        &heights,
                        &entry,
                    )?;
                    println!("{}", hex(&salt));
                    Ok(())
                }
                _ => Err("key --action is cell-blinding or derive-salt".to_owned()),
            }
        }
        "bootstrap" => {
            if SOCKET.get().is_some() {
                return Err("bootstrap requires direct Host/Main CLI".to_owned());
            }
            let host = path(args.required("host")?);
            let config = path(args.required("config")?);
            let source = path(args.required("source")?);
            let directory = path(args.required("dir")?);
            args.finish()?;
            bootstrap(&host, &config, &source, &directory)
        }
        "author" => {
            let host = path(args.required("host")?);
            let config = path(args.required("config")?);
            let kind = args.required("kind")?;
            let input = path(args.required("input")?);
            let output = path(args.required("output")?);
            args.finish()?;
            author(&host, &config, &kind, &input, &output)
        }
        "inspect" => {
            let host = path(args.required("host")?);
            let config = path(args.required("config")?);
            let kind = args.required("kind")?;
            let input = path(args.required("input")?);
            let output = path(args.required("output")?);
            args.finish()?;
            let kind = kind.to_str().ok_or("public inspect kind must be UTF-8")?;
            if !matches!(kind, "fn-inbox-resource" | "application-permission-schema") {
                return Err("public inspect kind is unavailable".to_owned());
            }
            inspect_public(&host, &config, kind, &input, &output)
        }
        #[cfg(unix)]
        "current-application-intent" | "current-session-intent" | "current-resource-intent" => {
            let route = if args.command == OsStr::new("current-application-intent") {
                current_birth::Route::Application
            } else if args.command == OsStr::new("current-resource-intent") {
                current_birth::Route::Resource
            } else {
                current_birth::Route::Session
            };
            let host = path(args.required("host")?);
            let config = path(args.required("config")?);
            let source = path(args.required("source")?);
            let directory = path(args.required("dir")?);
            let observation = args.optional("signed-observation").map(path);
            args.finish()?;
            let socket = SOCKET
                .get()
                .ok_or("current birth authoring requires --socket")?;
            current_birth::author(
                &host,
                &config,
                socket,
                &source,
                observation.as_deref(),
                &directory,
                route,
            )
        }
        #[cfg(unix)]
        "agent-reserve-plan" => {
            let host = path(args.required("host")?);
            let config = path(args.required("config")?);
            let operator_socket = path(args.required("operator-socket")?);
            let public_socket = path(args.required("public-socket")?);
            let request = path(args.required("request")?);
            let directory = path(args.required("dir")?);
            args.finish()?;
            agent_reserve::plan(
                &host,
                &config,
                &operator_socket,
                &public_socket,
                &request,
                &directory,
            )
        }
        #[cfg(unix)]
        "agent-reserve-seal" => {
            let directory = path(args.required("attempt")?);
            let approval = path(args.required("approval")?);
            args.finish()?;
            agent_reserve::seal(&directory, &approval)
        }
        #[cfg(unix)]
        "agent-reserve-submit" => {
            let directory = path(args.required("attempt")?);
            args.finish()?;
            agent_reserve::submit(&directory)
        }
        #[cfg(unix)]
        "agent-reserve-lookup" => {
            let directory = path(args.required("attempt")?);
            args.finish()?;
            agent_reserve::lookup(&directory)
        }
        #[cfg(unix)]
        "agent-lifetime-reserve-plan" => {
            let host = path(args.required("host")?);
            let config = path(args.required("config")?);
            let operator_socket = path(args.required("operator-socket")?);
            let public_socket = path(args.required("public-socket")?);
            let request = path(args.required("request")?);
            let directory = path(args.required("dir")?);
            args.finish()?;
            agent_reserve::lifetime_plan(
                &host,
                &config,
                &operator_socket,
                &public_socket,
                &request,
                &directory,
            )
        }
        #[cfg(unix)]
        "agent-lifetime-reserve-seal" => {
            let directory = path(args.required("attempt")?);
            let approval = path(args.required("approval")?);
            args.finish()?;
            agent_reserve::lifetime_seal(&directory, &approval)
        }
        #[cfg(unix)]
        "agent-lifetime-reserve-submit" => {
            let directory = path(args.required("attempt")?);
            args.finish()?;
            agent_reserve::lifetime_submit(&directory)
        }
        #[cfg(unix)]
        "agent-lifetime-reserve-lookup" => {
            let directory = path(args.required("attempt")?);
            args.finish()?;
            agent_reserve::lifetime_lookup(&directory)
        }
        #[cfg(unix)]
        "agent-lifetime-paid-plan" => {
            let reserve = path(args.required("reserve-attempt")?);
            let grant = path(args.required("grant-attempt")?);
            let directory = path(args.required("dir")?);
            args.finish()?;
            agent_reserve::lifetime_paid_plan(&reserve, &grant, &directory)
        }
        #[cfg(unix)]
        "agent-lifetime-paid-payer-sign" => {
            let directory = path(args.required("attempt")?);
            let approval = path(args.required("approval")?);
            args.finish()?;
            agent_reserve::lifetime_paid_payer_sign(&directory, &approval)
        }
        #[cfg(unix)]
        "agent-lifetime-paid-seal" => {
            let directory = path(args.required("attempt")?);
            let approval = path(args.required("approval")?);
            args.finish()?;
            agent_reserve::lifetime_paid_seal(&directory, &approval)
        }
        #[cfg(unix)]
        "agent-lifetime-paid-submit" => {
            let directory = path(args.required("attempt")?);
            args.finish()?;
            agent_reserve::lifetime_paid_submit(&directory)
        }
        #[cfg(unix)]
        "agent-lifetime-paid-lookup" => {
            let directory = path(args.required("attempt")?);
            args.finish()?;
            agent_reserve::lifetime_paid_lookup(&directory)
        }
        #[cfg(unix)]
        "agent-lifetime-grant-plan" => {
            let host = path(args.required("host")?);
            let config = path(args.required("config")?);
            let operator_socket = path(args.required("operator-socket")?);
            let request = path(args.required("request")?);
            let directory = path(args.required("dir")?);
            args.finish()?;
            agent_lifetime_grant::grant_plan(&host, &config, &operator_socket, &request, &directory)
        }
        #[cfg(unix)]
        "agent-lifetime-grant-seal" => {
            let directory = path(args.required("attempt")?);
            let approval = path(args.required("approval")?);
            args.finish()?;
            agent_lifetime_grant::grant_seal(&directory, &approval)
        }
        #[cfg(unix)]
        "agent-lifetime-grant-submit" => {
            let directory = path(args.required("attempt")?);
            args.finish()?;
            agent_lifetime_grant::grant_submit(&directory)
        }
        #[cfg(unix)]
        "agent-lifetime-grant-inspect" => {
            let host = path(args.required("host")?);
            let config = path(args.required("config")?);
            let socket = path(args.required("operator-socket")?);
            let ingress = path(args.required("ingress")?);
            let output = path(args.required("output")?);
            args.finish()?;
            agent_lifetime_grant::inspect_accepted(&host, &config, &socket, &ingress, &output)
        }
        #[cfg(unix)]
        "agent-lifetime-grant-lookup" => {
            let directory = path(args.required("attempt")?);
            args.finish()?;
            agent_lifetime_grant::grant_lookup(&directory)
        }
        #[cfg(unix)]
        "session-enrollment-plan" => {
            let host = path(args.required("host")?);
            let config = path(args.required("config")?);
            let socket = path(args.required("operator-socket")?);
            let request = path(args.required("request")?);
            let directory = path(args.required("dir")?);
            args.finish()?;
            session_enrollment::plan(&host, &config, &socket, &request, &directory)
        }
        #[cfg(unix)]
        "session-enrollment-seal" => {
            let directory = path(args.required("attempt")?);
            let approval = path(args.required("approval")?);
            args.finish()?;
            session_enrollment::seal(&directory, &approval)
        }
        #[cfg(unix)]
        "session-enrollment-submit" => {
            let directory = path(args.required("attempt")?);
            args.finish()?;
            session_enrollment::submit(&directory)
        }
        #[cfg(unix)]
        "session-enrollment-lookup" => {
            let directory = path(args.required("attempt")?);
            args.finish()?;
            session_enrollment::lookup(&directory)
        }
        #[cfg(unix)]
        "agent-payer-sign" => {
            let host = path(args.required("host")?);
            let config = path(args.required("config")?);
            let operator_socket = path(args.required("operator-socket")?);
            let reserve_attempt = path(args.required("reserve-attempt")?);
            let plan = path(args.required("plan")?);
            let approval = path(args.required("approval")?);
            let key = path(args.required("key")?);
            let directory = path(args.required("dir")?);
            args.finish()?;
            agent_payer::sign(agent_payer::Inputs {
                host: &host,
                config: &config,
                operator_socket: &operator_socket,
                reserve_attempt: &reserve_attempt,
                paid_plan: &plan,
                approval_path: &approval,
                key_path: &key,
                directory: &directory,
            })
        }
        #[cfg(unix)]
        "share-issue-prepare" => {
            let host = path(args.required("host")?);
            let config = path(args.required("config")?);
            let request = path(args.required("request")?);
            let approval = path(args.required("approval")?);
            let directory = path(args.required("dir")?);
            args.finish()?;
            let socket = SOCKET
                .get()
                .ok_or("share-issue-prepare requires --socket")?;
            share_issue::prepare(&host, &config, socket, &request, &approval, &directory)
        }
        #[cfg(unix)]
        "share-issue-submit" => {
            let directory = path(args.required("attempt")?);
            args.finish()?;
            share_issue::submit(&directory, SOCKET.get().map(PathBuf::as_path))
        }
        #[cfg(unix)]
        "share-issue-lookup" => {
            let directory = path(args.required("attempt")?);
            args.finish()?;
            share_issue::lookup(&directory, SOCKET.get().map(PathBuf::as_path))
        }
        #[cfg(unix)]
        "share-issue-receipt-lookup" => {
            let host = path(args.required("host")?);
            let config = path(args.required("config")?);
            let ingress = path(args.required("ingress")?);
            let transaction_id = args.required("transaction-id")?;
            let event_id = args.required("event-id")?;
            let accepted_count = args.required("accepted-count")?;
            let world_root = args.required("world-root")?;
            let directory = path(args.required("dir")?);
            args.finish()?;
            let socket = SOCKET
                .get()
                .ok_or("share issue receipt lookup requires --socket")?;
            let expected = [transaction_id, event_id, accepted_count, world_root];
            let fields = expected
                .iter()
                .map(|value| {
                    value
                        .to_str()
                        .ok_or_else(|| "share issue receipt field must be UTF-8".to_owned())
                })
                .collect::<Result<Vec<_>>>()?;
            share_issue_receipt::lookup(
                &host,
                &config,
                socket,
                &ingress,
                [fields[0], fields[1], fields[2], fields[3]],
                &directory,
            )
        }
        #[cfg(unix)]
        "grain-share-issue-plan" => {
            let host = path(args.required("host")?);
            let config = path(args.required("config")?);
            let request = path(args.required("request")?);
            let directory = path(args.required("dir")?);
            args.finish()?;
            let socket = SOCKET
                .get()
                .ok_or("grain-share-issue-plan requires --socket")?;
            grain_share_issue::plan(&host, &config, socket, &request, &directory)
        }
        #[cfg(unix)]
        "grain-share-issue-prepare" => {
            let host = path(args.required("host")?);
            let config = path(args.required("config")?);
            let request = path(args.required("request")?);
            let approval = path(args.required("approval")?);
            let directory = path(args.required("dir")?);
            args.finish()?;
            let socket = SOCKET
                .get()
                .ok_or("grain-share-issue-prepare requires --socket")?;
            grain_share_issue::prepare(&host, &config, socket, &request, &approval, &directory)
        }
        #[cfg(unix)]
        "grain-share-issue-submit" => {
            let directory = path(args.required("attempt")?);
            args.finish()?;
            grain_share_issue::submit(&directory, SOCKET.get().map(PathBuf::as_path))
        }
        #[cfg(unix)]
        "grain-share-issue-lookup" => {
            let directory = path(args.required("attempt")?);
            args.finish()?;
            grain_share_issue::lookup(&directory, SOCKET.get().map(PathBuf::as_path))
        }
        #[cfg(unix)]
        "grain-share-issue-receipt-lookup" => {
            let host = path(args.required("host")?);
            let config = path(args.required("config")?);
            let ingress = path(args.required("ingress")?);
            let transaction_id = args.required("transaction-id")?;
            let event_id = args.required("event-id")?;
            let accepted_count = args.required("accepted-count")?;
            let world_root = args.required("world-root")?;
            let directory = path(args.required("dir")?);
            args.finish()?;
            let socket = SOCKET
                .get()
                .ok_or("grain share issue receipt lookup requires --socket")?;
            let expected = [transaction_id, event_id, accepted_count, world_root];
            let fields = expected
                .iter()
                .map(|value| {
                    value
                        .to_str()
                        .ok_or_else(|| "grain share receipt field must be UTF-8".to_owned())
                })
                .collect::<Result<Vec<_>>>()?;
            share_issue_receipt::lookup_grain(
                &host,
                &config,
                socket,
                &ingress,
                [fields[0], fields[1], fields[2], fields[3]],
                &directory,
            )
        }
        #[cfg(unix)]
        "historical-call-receipt-lookup" => {
            let host = path(args.required("host")?);
            let config = path(args.required("config")?);
            let call = path(args.required("call")?);
            let transaction_id = args.required("transaction-id")?;
            let event_id = args.required("event-id")?;
            let accepted_count = args.required("accepted-count")?;
            let world_root = args.required("world-root")?;
            let directory = path(args.required("dir")?);
            args.finish()?;
            let socket = SOCKET
                .get()
                .ok_or("historical call receipt lookup requires --socket")?;
            let expected = [transaction_id, event_id, accepted_count, world_root];
            let fields = expected
                .iter()
                .map(|value| {
                    value
                        .to_str()
                        .ok_or_else(|| "historical call receipt field must be UTF-8".to_owned())
                })
                .collect::<Result<Vec<_>>>()?;
            historical_call_receipt::lookup(
                &host,
                &config,
                socket,
                &call,
                [fields[0], fields[1], fields[2], fields[3]],
                &directory,
            )
        }
        "submit" => {
            let host = path(args.required("host")?);
            let config = path(args.required("config")?);
            let intent = path(args.required("intent")?);
            let intent_kind = args
                .optional("intent-kind")
                .unwrap_or_else(|| OsString::from("intent"));
            let prepare_only = match args.optional("prepare-only").as_deref() {
                None => false,
                Some(value) if value == OsStr::new("false") => false,
                Some(value) if value == OsStr::new("true") => true,
                _ => return Err("--prepare-only must be true or false".to_owned()),
            };
            let provider_continuity = args.optional("provider-continuity").map(path);
            let key = path(args.required("key")?);
            let directory = path(args.required("dir")?);
            args.finish()?;
            submit_with_continuity(
                &host,
                &config,
                &intent,
                &intent_kind,
                &key,
                &directory,
                prepare_only,
                provider_continuity.as_deref(),
            )
        }
        "query" => {
            // A workspace names its serving socket: the signed read goes to that session (ops 4/5);
            // without one, each of challenge and query opens the Store in a cold Host.
            let (host, config, key) = match args.optional("workspace") {
                Some(root) => {
                    let workspace = workspace::load(&path(root))?;
                    (
                        workspace::workspace_host(&workspace)?,
                        workspace::member_path(&workspace, "config")?,
                        workspace::member_path(&workspace, "key")?,
                    )
                }
                None => (
                    path(args.required("host")?),
                    path(args.required("config")?),
                    path(args.required("key")?),
                ),
            };
            let intent = path(args.required("intent")?);
            let intent_kind = args
                .optional("intent-kind")
                .unwrap_or_else(|| OsString::from("intent"));
            let view = args.required("view")?;
            let presentation = args.optional("presentation");
            let directory = path(args.required("dir")?);
            args.finish()?;
            let view = view
                .to_str()
                .ok_or_else(|| "--view must be UTF-8".to_owned())?;
            let presentation = presentation
                .as_deref()
                .map(|value| value.to_str().ok_or("--presentation must be UTF-8"))
                .transpose()?;
            let inspection_kind = query_presentation_kind(view, presentation)?;
            query(
                &host,
                &config,
                &intent,
                &intent_kind,
                &key,
                &inspection_kind,
                &directory,
            )
        }
        #[cfg(unix)]
        "objective-invoke" => {
            let host = path(args.required("host")?);
            let config = path(args.required("config")?);
            let request = path(args.required("request")?);
            let intent_nonce = args.required("intent-nonce")?.into_string()
                .map_err(|_| "--intent-nonce must be UTF-8".to_owned())?;
            let key = path(args.required("key")?);
            let directory = path(args.required("dir")?);
            let prepare_only = match args.optional("prepare-only").as_deref() {
                None => false,
                Some(value) if value == OsStr::new("false") => false,
                Some(value) if value == OsStr::new("true") => true,
                _ => return Err("--prepare-only must be true or false".to_owned()),
            };
            args.finish()?;
            objective_invoke::submit(&host, &config, &request, &intent_nonce, &key, &directory, prepare_only)
        }
        "attempt-state" => {
            let directory = path(args.required("attempt")?);
            let file = args.optional("file").map(|f| f.into_string().map_err(|_| "--file must be UTF-8".to_owned())).transpose()?;
            // `--json` (valueless) is the only rendering; accepted so callers can say what they read.
            let _ = args.optional("json");
            args.finish()?;
            attempt_state::run(&directory, file.as_deref())
        }
        "retry" => {
            let directory = path(args.required("attempt")?);
            let mode = args
                .optional("mode")
                .unwrap_or_else(|| OsString::from("submit"));
            let direct = match args.optional("direct").as_deref() {
                None => false,
                Some(value) if value == OsStr::new("false") => false,
                Some(value) if value == OsStr::new("true") => true,
                _ => return Err("--direct must be true or false".to_owned()),
            };
            if direct && SOCKET.get().is_some() {
                return Err("--direct true cannot be combined with --socket".to_owned());
            }
            args.finish()?;
            let mode = mode
                .to_str()
                .ok_or_else(|| "--mode must be UTF-8".to_owned())?;
            retry(&directory, mode, direct)
        }
        #[cfg(unix)]
        "selected-release-submit" => {
            let host = path(args.required("host")?);
            let config = path(args.required("config")?);
            let ingress = path(args.required("ingress")?);
            let directory = path(args.required("dir")?);
            args.finish()?;
            let socket = SOCKET
                .get()
                .ok_or("selected-release-submit requires --socket")?;
            selected_release::submit(&host, &config, socket, &ingress, &directory)
        }
        #[cfg(unix)]
        "selected-release-sign" => {
            let host = path(args.required("host")?);
            let config = path(args.required("config")?);
            let preimage = path(args.required("preimage")?);
            let key = path(args.required("key")?);
            let output = path(args.required("output")?);
            args.finish()?;
            selected_release_sign(&host, &config, &preimage, &key, &output)
        }
        #[cfg(unix)]
        "selected-source-sign" => {
            let host = path(args.required("host")?);
            let config = path(args.required("config")?);
            let packet = path(args.required("packet")?);
            let capability = args.required("delegate-capability")?;
            let key = path(args.required("key")?);
            let directory = path(args.required("dir")?);
            args.finish()?;
            let capability = capability
                .to_str()
                .ok_or("delegate capability must be UTF-8")?;
            selected_publisher::sign_source(&host, &config, &packet, capability, &key, &directory)
        }
        #[cfg(unix)]
        "selected-source-publish" => {
            let host = path(args.required("host")?);
            let config = path(args.required("config")?);
            let ingress = path(args.required("ingress")?);
            let article = path(args.required("article")?);
            let state = path(args.required("state-dir")?);
            let post_config = path(args.required("post-config")?);
            args.finish()?;
            selected_publisher::publish(&host, &config, &ingress, &article, &state, &post_config)
        }
        #[cfg(unix)]
        "selected-release-lookup" => {
            let directory = path(args.required("attempt")?);
            args.finish()?;
            selected_release::lookup(&directory, SOCKET.get().map(PathBuf::as_path))
        }
        "export-evidence" => {
            let host = path(args.required("host")?);
            let config = path(args.required("config")?);
            let call = path(args.required("call")?);
            let output = path(args.required("output")?);
            args.finish()?;
            if output.exists() {
                return Err(format!("refusing to replace {}", output.display()));
            }
            host_files(
                &host,
                &config,
                &[Path::new("export-evidence"), &call, &output],
            )
        }
        "verify-evidence" => {
            let host = path(args.required("host")?);
            let config = path(args.required("config")?);
            let package = path(args.required("package")?);
            let output = path(args.required("output")?);
            args.finish()?;
            if output.exists() {
                return Err(format!("refusing to replace {}", output.display()));
            }
            host_files(
                &host,
                &config,
                &[Path::new("verify-evidence"), &package, &output],
            )
        }
        other => Err(format!("unknown command {other}\n\n{USAGE}")),
    }
}

fn main() -> ExitCode {
    // Before any thread or child: no child inherits the key-cache passphrase.
    workspace::private::adopt_keycache_passphrase();
    #[cfg(unix)]
    let parsed = match env::args_os().nth(1) {
        Some(command) if command == OsStr::new("fleet-sign") => {
            fleet_sign::run(env::args_os().skip(2).collect())
        }
        _ => Args::parse().and_then(run),
    };
    #[cfg(not(unix))]
    let parsed = Args::parse().and_then(run);
    let ending = main_ending(parsed, EXIT_STATUS.load(Ordering::Relaxed));
    print!("{}", ending.stdout);
    eprint!("{}", ending.stderr);
    ExitCode::from(ending.code)
}

/// How a command ends once it has run: the exit code and what is printed
/// after it returned. `main` prints it; `capture::command` (a command run in
/// this process instead of a child `mini`) returns it, so the two endings are
/// one function.
pub(crate) struct MainEnding {
    pub(crate) code: u8,
    pub(crate) stdout: String,
    pub(crate) stderr: String,
}

pub(crate) fn main_ending(parsed: Result<()>, status: u8) -> MainEnding {
    let ended = |code: u8, stdout: String, stderr: String| MainEnding { code, stdout, stderr };
    if let Some(ending) = take_command_ending() {
        let (code, message) = ending.render();
        return ended(code, String::new(), message);
    }
    match parsed {
        Ok(()) => ended(status, String::new(), String::new()),
        Err(error) if error == USAGE => ended(0, error, String::new()),
        Err(error) => match take_host_decision().as_ref().and_then(host_ending) {
            Some((code, line)) => ended(code, String::new(), format!("{line}\n  client: {error}\n")),
            None => ended(status.max(1), String::new(), format!("mini: {error}\n")),
        },
    }
}

/// Replace the process exit status a verb raised (`set_exit`); the old value.
pub(crate) fn swap_exit_status(value: u8) -> u8 {
    EXIT_STATUS.swap(value, Ordering::Relaxed)
}

#[cfg(test)]
mod tests {

    #[test]
    fn apps_positionals_are_the_grammar_leafs_flags() {
        let flags = |words: &[&str]| Args::parse_from(words.iter().map(OsString::from)).unwrap().values.into_iter()
            .map(|(k, v)| format!("{}={}", k.to_string_lossy(), v.to_string_lossy())).collect::<Vec<_>>();
        assert_eq!(flags(&["apps", "share", "a4501", "bob"]), ["--action=share", "--grain=a4501", "--to=bob"]);
        assert_eq!(flags(&["apps", "search", "slides", "--json"]), ["--action=search", "--term=slides", "--json=yes"]);
        assert_eq!(flags(&["apps", "search", "--term", "slides"]), ["--action=search", "--term=slides"]);
        assert_eq!(flags(&["apps", "renew", "a4501"]), ["--action=renew", "--grain=a4501"]);
        assert_eq!(flags(&["apps", "list"]), ["--action=list"]);
        assert_eq!(flags(&["apps", "revoke-identity", "a4501", "tok"]), ["--action=revoke-identity", "--grain=a4501", "--token=tok"]);
    }
    use super::*;

    #[test]
    fn mini_with_no_command_ends_non_zero_and_help_still_ends_zero() {
        let no_command = Args::parse_from(Vec::<OsString>::new()).err().expect("no command is an error");
        assert_ne!(no_command, USAGE);
        assert!(no_command.starts_with("no command given"));
        assert_ne!(main_ending(Err(no_command), 0).code, 0);
        let help = Args::parse_from([OsString::from("--help")]).err().expect("--help prints usage");
        assert_eq!(main_ending(Err(help), 0).code, 0);
    }

    #[test]
    fn every_command_the_dispatcher_runs_is_named_in_usage() {
        let source = include_str!("main.rs");
        let body = &source[source.find("\nfn run(").expect("fn run")..source.find("\nfn main()").expect("fn main")];
        let mut hidden = Vec::new();
        for line in body.lines() {
            let Some(rest) = line.strip_prefix("        \"") else { continue };
            let Some((names, _)) = rest.split_once(" =>") else { continue };
            let names = names.split_once(" if ").map_or(names, |(names, _)| names);
            for name in names.split(" | ").map(|n| n.trim_matches('"')) {
                if !name.is_empty() && name.bytes().all(|b| b.is_ascii_lowercase() || b == b'-')
                    && !USAGE.contains(&format!("mini {name} ")) && !USAGE.contains(&format!("mini {name}|"))
                    && !USAGE.contains(&format!("mini --verify-host {name} "))
                {
                    hidden.push(name.to_owned());
                }
            }
        }
        assert!(hidden.is_empty(), "commands the dispatcher runs that USAGE never names: {hidden:?}");
    }

    #[cfg(unix)]
    #[test]
    fn object_audience_inspects_are_session_frames_not_codec_frames() {
        let frame = |kind: &str| mini_sdk::local::kind(kind, b"source").unwrap();
        let inspect = mini_sdk::host_operations::INSPECT;
        assert!(session_inspect_kind(inspect, &frame("object-audience")));
        assert!(session_inspect_kind(inspect, &frame("object-audience-roster")));
        // The kinds the storeless codec still answers stay codec frames.
        assert!(!session_inspect_kind(inspect, &frame("object-roster-inspect")));
        assert!(!session_inspect_kind(inspect, &frame("outcome")));
        // No other opcode is redirected, whatever its payload.
        assert!(!session_inspect_kind(mini_sdk::host_operations::AUTHOR, &frame("object-audience")));
        // A truncated kind header is not a session frame.
        assert!(!session_inspect_kind(inspect, &[1]));
        assert!(!session_inspect_kind(inspect, &[]));
    }

    #[test]
    fn store_audit_argv_is_the_host_arm_and_optional_receipts() {
        assert_eq!(
            store_audit_argv(Path::new("/c.json"), None),
            [OsString::from("/c.json"), OsString::from("store-audit")]
        );
        assert_eq!(
            store_audit_argv(Path::new("/c.json"), Some(Path::new("/r.bin"))),
            [
                OsString::from("/c.json"),
                OsString::from("store-audit"),
                OsString::from("--receipts"),
                OsString::from("/r.bin"),
            ]
        );
    }
    use ed25519_dalek::{Verifier, VerifyingKey};
    use std::time::{SystemTime, UNIX_EPOCH};

    fn scratch(name: &str) -> PathBuf {
        let unique = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_nanos();
        let path = env::temp_dir().join(format!("mini-{name}-{}-{unique}", std::process::id()));
        fs::create_dir(&path).unwrap();
        path
    }

    #[cfg(unix)]
    #[test]
    fn host_image_digest_is_cached_per_file_identity() {
        let dir = scratch("host-image-digest");
        let host = dir.join("minidregg-host");
        let sha = |bytes: &[u8]| hex(&sha2::Sha256::digest(bytes));
        fs::write(&host, b"first image").unwrap();
        assert_eq!(host_image_sha256(&host).unwrap(), sha(b"first image"));
        assert_eq!(host_image_sha256(&host).unwrap(), sha(b"first image"));
        // Replaced by rename: a new inode, so the digest is taken again.
        let staged = dir.join("staged");
        fs::write(&staged, b"second image").unwrap();
        fs::rename(&staged, &host).unwrap();
        assert_eq!(host_image_sha256(&host).unwrap(), sha(b"second image"));
        // Rewritten in place at the same length: the status-change time moves.
        std::thread::sleep(std::time::Duration::from_millis(20));
        fs::write(&host, b"third  image").unwrap();
        assert_eq!(host_image_sha256(&host).unwrap(), sha(b"third  image"));
        fs::remove_dir_all(&dir).unwrap();
    }

    /// The plant of the workspace Host pin: a Host file replaced under an unchanged pin is named by
    /// the pin without being read (the serving Host's envelope check refuses it after the next
    /// `serve` start), and `--verify-host` hashes it and refuses the mismatch here.
    #[cfg(unix)]
    #[test]
    fn a_pinned_host_image_is_named_by_its_pin_and_verify_host_refuses_a_replacement() {
        let dir = scratch("host-image-pin");
        let host = dir.join("minidregg-host");
        let sha = |bytes: &[u8]| hex(&sha2::Sha256::digest(bytes));
        fs::write(&host, b"pinned image").unwrap();
        pin_workspace_host(&host, &sha(b"pinned image")).unwrap();
        fs::write(&host, b"replaced image").unwrap();
        assert_eq!(host_image_sha256(&host).unwrap(), sha(b"pinned image"));
        VERIFY_HOST.store(true, Ordering::Relaxed);
        let verified = host_image_sha256(&host);
        VERIFY_HOST.store(false, Ordering::Relaxed);
        let error = verified.unwrap_err();
        assert!(error.contains("differs from the workspace's pinned hostSha256"), "{error}");
        assert!(pin_workspace_host(&host, &sha(b"replaced image")).is_err());
        fs::remove_dir_all(&dir).unwrap();
    }

    #[test]
    fn named_options_preserve_interleaved_fn_argument_order() {
        let mut args = Args {
            command: OsString::from("host-command"),
            values: [
                ("--arg", "first"),
                ("--host", "host"),
                ("--arg", "second"),
                ("--config", "config"),
                ("--command", "consumer-export-reply"),
                ("--arg", "third"),
            ]
            .into_iter()
            .map(|(key, value)| (OsString::from(key), OsString::from(value)))
            .collect(),
        };
        assert_eq!(args.required("host").unwrap(), OsStr::new("host"));
        assert_eq!(args.required("config").unwrap(), OsStr::new("config"));
        assert_eq!(
            args.required("command").unwrap(),
            OsStr::new("consumer-export-reply")
        );
        assert_eq!(
            args.repeated("arg"),
            vec!["first", "second", "third"]
                .into_iter()
                .map(OsString::from)
                .collect::<Vec<_>>()
        );
        args.finish().unwrap();
    }

    #[cfg(unix)]
    #[test]
    fn continuity_reply_needs_typed_matching_verdict_and_anchor_shape() {
        let mut value = json!({"type":"minidregg-provider-continuity-v1",
            "status":"confirmed", "continuous":true, "providerResourceId":"7",
            "checkedWorldRoot":"12", "checkedAcceptedCount":"3", "reason":"",
            "anchor":{"type":"verified-mini-native-prefix-v1", "transactionId":"1",
                "eventId":"2", "acceptedCount":"3", "worldRoot":"4"}});
        assert!(continuity_reply(&value).unwrap());
        value["status"] = json!("refused");
        value["continuous"] = json!(false);
        value["reason"] = json!("provider history changed");
        assert!(!continuity_reply(&value).unwrap());
        value["anchor"]["transactionId"] = json!("01");
        assert!(continuity_reply(&value).is_err());
    }

    #[test]
    fn query_typed_inbox_presentation_is_resource_only() {
        assert_eq!(
            query_presentation_kind("resource", Some("fn-inbox-resource")).unwrap(),
            "fn-inbox-resource"
        );
        assert_eq!(
            query_presentation_kind("policy", None).unwrap(),
            "view-policy"
        );
        assert!(query_presentation_kind("policy", Some("fn-inbox-resource")).is_err());
        assert!(query_presentation_kind("resource", Some("view-resource")).is_err());
    }

    #[test]
    fn public_schema_inspection_requires_exact_canonical_input() {
        let input = b"canonical schema bytes";
        let valid = json!({"type":"minidregg-application-permission-schema-v1",
            "version":"1","root":"7","canonical":hex(input),
            "permissions":[],"roles":[],"denied":[]});
        assert!(
            validate_public_inspection("application-permission-schema", &valid, Some(input))
                .is_ok()
        );
        assert!(validate_public_inspection(
            "application-permission-schema",
            &valid,
            Some(b"changed")
        )
        .is_err());
        let mut wrong = valid.clone();
        wrong["canonical"] = json!("00");
        assert!(
            validate_public_inspection("application-permission-schema", &wrong, Some(input))
                .is_err()
        );
        assert!(validate_public_inspection("fn-inbox-resource", &valid, None).is_err());
    }

    #[test]
    fn inspected_headers_are_signed_as_exact_bytes_in_order() {
        let headers = vec![vec![0, 255, 16], b"mini".to_vec()];

        let signing = SigningKey::from_bytes(&[27; 32]);
        let rendered = sign_headers(&signing, &headers).unwrap();
        let signatures = rendered.as_array().unwrap();
        let verifying = VerifyingKey::from_bytes(&signing.verifying_key().to_bytes()).unwrap();
        for (header, signature) in headers.iter().zip(signatures) {
            let bytes: [u8; 64] = decode_hex(signature.as_str().unwrap())
                .unwrap()
                .try_into()
                .unwrap();
            verifying
                .verify(header, &ed25519_dalek::Signature::from_bytes(&bytes))
                .unwrap();
        }
    }

    #[test]
    fn plan_slots_reject_presentation_without_exact_header_strings() {
        assert!(plan_headers(&json!({"slots": [{"header": "01"}]})).is_ok());
        assert!(plan_headers(&json!({"slots": [{"header": 1}]})).is_err());
        assert!(plan_headers(&json!({"slots": [{"header": "0"}]})).is_err());
        assert!(plan_headers(&json!({"slots": [{"header": "zz"}]})).is_err());
        assert!(print_confirmed_outcome(&json!({"type": "confirmed"})).is_ok());
        assert!(print_confirmed_outcome(&json!({"type": "refused"})).is_err());
    }

    #[test]
    fn refusal_reason_is_rendered_from_the_host_decoding_only() {
        let revoked = json!({"type":"refused","reason":"revoked",
            "phase":hex(b"observation"),"detail":hex(b"the grant is revoked")});
        assert_eq!(
            refusal_line(&revoked).unwrap(),
            "refused: revoked: the grant is revoked (phase observation)"
        );
        let decision = HostDecision::Frame {
            command: "query".into(),
            byte: RESPONSE_NO_RECORD,
            encoded: vec![1],
            decoded: Some(revoked.clone()),
        };
        let (code, line) = host_ending(&decision).unwrap();
        assert_eq!(code, EXIT_REFUSED);
        assert!(line.starts_with("refused: revoked: the grant is revoked (phase observation)\n"), "{line}");
        // The same decoding under the undecided envelope (255) is no refusal.
        let envelope = HostDecision::Frame { command: "query".into(), byte: RESPONSE_HOST_OUTCOME, encoded: vec![1], decoded: Some(revoked) };
        assert_eq!(host_ending(&envelope).unwrap().0, EXIT_UNDECIDED);
        // NO_RECORD with a contention decoding: decided before any append, so a refusal-class line.
        let contended = HostDecision::Frame { command: "submit".into(), byte: RESPONSE_NO_RECORD, encoded: vec![1],
            decoded: Some(json!({"type":"contention"})) };
        let (code, line) = host_ending(&contended).unwrap();
        assert_eq!(code, EXIT_REFUSED);
        assert!(line.starts_with("refused: no record: the Host answered contention before any append"), "{line}");
        // Prose that names a reason is not a reason.
        let nested = json!({"type":"refused","reason":"operation-rejected","phase":hex(b"prepare"),
            "detail":hex(b"invocation preparation: A.Reject.scalar\n  (B.Reject.pageMutation\n    (C.RejectReason.overflow))")});
        assert_eq!(
            refusal_line(&nested).unwrap(),
            "refused: operation-rejected: invocation preparation: A.Reject.scalar (B.Reject.pageMutation (C.RejectReason.overflow)) (phase prepare)"
        );
        let escape = json!({"type":"refused","reason":"malformed","phase":hex(b"x"),"detail":hex(b"a\x1b[2Jb")});
        assert!(refusal_line(&escape).unwrap().starts_with("refused: malformed: hex "));
        let limited = json!({"type":"refused","reason":"rate-limited","phase":hex(b"op 5"),
            "detail":hex(b"rate-limited retry-after-ms 1500")});
        assert_eq!(
            refusal_line(&limited).unwrap(),
            "refused: rate-limited: this subject has used its request rate for now; retry in 2 s (phase op 5)"
        );
        let prose = json!({"type":"refused","phase":hex(b"x"),"detail":hex(b"revoked")});
        assert!(refusal_line(&prose)
            .unwrap()
            .starts_with("refused: unnamed: revoked"));
        let undecoded = HostDecision::Frame {
            command: "query".into(),
            byte: 255,
            encoded: vec![1],
            decoded: None,
        };
        // A 255 frame is not a refusal by its byte: undecoded, or decoded as anything but
        // `refused`, it is undecided (exit 4), and the line says not to repeat the operation.
        let (code, line) = host_ending(&undecoded).unwrap();
        assert_eq!(code, EXIT_UNDECIDED);
        assert!(line.starts_with("undecided: Host answered query with reply byte 255 and outcome undecoded"), "{line}");
        for kind in ["uncertain", "unavailable", "contention", "absent"] {
            let frame = HostDecision::Frame { command: "submit".into(), byte: 255, encoded: vec![1],
                decoded: Some(json!({"type": kind})) };
            assert!(!frame.is_refusal());
            let (code, line) = host_ending(&frame).unwrap();
            assert_eq!(code, EXIT_UNDECIDED, "{kind}");
            assert!(line.contains(&format!("outcome {kind}")) && !line.starts_with("refused"), "{line}");
        }
        let (code, _) = host_ending(&HostDecision::Outcome(json!({"type":"uncertain"}))).unwrap();
        assert_eq!(code, EXIT_UNDECIDED);
        assert_eq!(host_ending(&HostDecision::Outcome(json!({"type":"confirmed"}))), None);
        let charged = json!({"type":"confirmed","confirmation":"installed","disposition":"charged","cause":hex(b"exhausted"),
            "transactionId":"1","eventId":"2","acceptedCount":"3","worldRoot":"4"});
        let (code, line) = host_ending(&HostDecision::Outcome(charged.clone())).unwrap();
        assert_eq!((code, line.as_str()), (EXIT_REFUSED,
            "charged: the Host admitted the call and posted only its price; nothing else was written (cause exhausted)"));
        assert!(print_confirmed_outcome(&charged).unwrap_err().starts_with("charged: "));
    }

    /// `host_decided` reports only a decoded refusal as the Host's refusal; an undecided 255
    /// frame stays an error, so no caller reads it as "refused, so another way is safe".
    #[test]
    fn host_decided_reads_only_a_decoded_refusal_as_a_refusal() {
        note_host_decision(HostDecision::Frame { command: "submit".into(), byte: 255, encoded: vec![1],
            decoded: Some(json!({"type":"unavailable"})) });
        assert_eq!(host_decided::<()>(Err("lost".into())), Err("lost".into()));
        note_host_decision(HostDecision::Frame { command: "submit".into(), byte: 255, encoded: vec![1], decoded: None });
        assert_eq!(host_decided::<()>(Err("lost".into())), Err("lost".into()));
        note_host_decision(HostDecision::Frame { command: "submit".into(), byte: RESPONSE_HOST_OUTCOME, encoded: vec![1],
            decoded: Some(json!({"type":"refused","reason":"revoked","phase":hex(b"x"),"detail":hex(b"gone")})) });
        assert_eq!(host_decided::<()>(Err("lost".into())), Err("lost".into()), "a decoded refusal under 255 is undecided");
        note_host_decision(HostDecision::Frame { command: "submit".into(), byte: RESPONSE_NO_RECORD, encoded: vec![1],
            decoded: Some(json!({"type":"refused","reason":"revoked","phase":hex(b"x"),"detail":hex(b"gone")})) });
        assert_eq!(host_decided::<()>(Err("lost".into())), Ok(Err("refused: revoked: gone (phase x)".into())));
        let message = undecided_frame_message("submit", "uncertain", Some(Path::new("/w/attempts/a/outcome.bin")), &[7]);
        assert!(message.contains("`mini retry --dir /w/attempts/a --mode lookup`"), "{message}");
    }

    #[test]
    fn key_generation_makes_a_next_key_unless_told_not_to_and_never_clobbers_one() {
        let directory = scratch("key-next");
        let secret = directory.join("daily.key");
        let public = directory.join("daily.pub");
        keygen(&secret, &public, None, NextKey::Beside, false).unwrap();
        let next = directory.join("daily.key.next");
        let next_public = directory.join("daily.key.next.pub");
        let next_seed: [u8; 32] = fs::read(&next).unwrap().try_into().unwrap();
        assert_eq!(
            fs::read(&next_public).unwrap(),
            SigningKey::from_bytes(&next_seed).verifying_key().to_bytes()
        );
        assert_ne!(fs::read(&next).unwrap(), fs::read(&secret).unwrap());

        // A next key already present is never replaced, and nothing is written.
        let other = directory.join("other.key");
        let other_public = directory.join("other.pub");
        fs::write(directory.join("other.key.next.pub"), b"existing").unwrap();
        assert!(keygen(&other, &other_public, None, NextKey::Beside, false).is_err());
        assert!(!other.exists() && !other_public.exists());
        assert_eq!(fs::read(directory.join("other.key.next.pub")).unwrap(), b"existing");

        // --next-to puts the next secret elsewhere; its public half stays by convention.
        let away = directory.join("away.next");
        keygen(&directory.join("a.key"), &directory.join("a.pub"), None, NextKey::To(away.clone()), true)
            .unwrap();
        assert!(away.exists() && directory.join("a.key.next.pub").exists());
        assert!(!directory.join("a.key.next").exists());
        // FIX-IDENTITY: the next key co-signed its succession at keygen; the
        // co-signature verifies for (a.key, its next key) and for no other pair.
        let daily: [u8; 32] = fs::read(directory.join("a.pub")).unwrap().try_into().unwrap();
        let next: [u8; 32] = fs::read(directory.join("a.key.next.pub")).unwrap().try_into().unwrap();
        let cosign: [u8; 64] = fs::read(directory.join("a.key.next.cosign")).unwrap().try_into().unwrap();
        key_rotation::verify_cosign(&daily, &next, &cosign).unwrap();
        assert!(key_rotation::verify_cosign(&next, &daily, &cosign).is_err());
        let mut other = daily;
        other[0] ^= 1;
        assert!(key_rotation::verify_cosign(&other, &next, &cosign).is_err());

        // --no-prerotation makes no next key at all.
        keygen(&directory.join("p.key"), &directory.join("p.pub"), None, NextKey::Without, false).unwrap();
        assert!(!directory.join("p.key.next").exists() && !directory.join("p.key.next.pub").exists());
        fs::remove_dir_all(directory).unwrap();
    }

    #[test]
    fn a_key_that_is_not_current_is_named_from_the_host_key_status() {
        // After a rotation the old key's status reports the CURRENT epoch.
        let rotated = json!({"type":"subject-key-status-v1","subject":"7","keyEpoch":"2","keyId":"11",
            "isCurrent":false,"isCommittedNext":false,"currentRevoked":false,"prerotated":false});
        let note = not_current_key_note(&rotated).unwrap();
        assert!(note.contains("rotated away") && note.contains("epoch 2 is current"), "{note}");
        let next = json!({"keyEpoch":"2","isCurrent":false,"isCommittedNext":true});
        let note = not_current_key_note(&next).unwrap();
        assert!(note.contains("committed NEXT key") && note.contains("epoch 2 is current"), "{note}");
        let current = json!({"keyEpoch":"3","isCurrent":true});
        assert_eq!(not_current_key_note(&current), None);
        // A status that does not say is not guessed at.
        assert_eq!(not_current_key_note(&json!({"keyEpoch":"3"})), None);
        assert_eq!(not_current_key_note(&json!({"isCurrent":false})), None);
    }

    #[test]
    fn only_a_bad_signature_refusal_asks_about_the_signing_key() {
        let signer = SignerContext {
            host: PathBuf::from("/nonexistent/host"),
            config: PathBuf::from("/nonexistent/config"),
            subject: "7".into(),
            public: [1; 32],
        };
        let rotated = || Some(json!({"keyEpoch":"2","isCurrent":false,"isCommittedNext":false}));
        let bad = json!({"type":"refused","reason":"bad-signature"});
        // A bad signature by a key the Host reports as no longer current is named.
        let named = explain_bad_signature(&bad, Some(&signer), |context| {
            assert_eq!((context.subject.as_str(), context.public), ("7", [1; 32]));
            rotated()
        });
        assert!(named.contains("rotated away") && named.contains("epoch 2 is current"), "{named}");
        // A current key (a genuinely bad signature) is left as the Host said it.
        let current = explain_bad_signature(&bad, Some(&signer), |_| Some(json!({"keyEpoch":"3","isCurrent":true})));
        assert_eq!(current, "");
        // A status that could not be fetched adds nothing.
        assert_eq!(explain_bad_signature(&bad, Some(&signer), |_| None), "");
        // No recorded signer: nothing to ask.
        assert_eq!(explain_bad_signature(&bad, None, |_| panic!("asked without a signer")), "");
        // Any other reason never asks.
        let stale = json!({"type":"refused","reason":"stale-root"});
        assert_eq!(explain_bad_signature(&stale, Some(&signer), |_| panic!("asked for stale-root")), "");
    }

    #[test]
    fn key_generation_refuses_to_clobber_existing_custody_files() {
        let directory = scratch("key-no-clobber");
        let secret = directory.join("signer.key");
        let public = directory.join("signer.pub");
        fs::write(&secret, b"existing-secret").unwrap();
        fs::write(&public, b"existing-public").unwrap();

        assert!(keygen(&secret, &public, None, NextKey::Beside, false).is_err());
        assert_eq!(fs::read(&secret).unwrap(), b"existing-secret");
        assert_eq!(fs::read(&public).unwrap(), b"existing-public");
        fs::remove_file(&secret).unwrap();
        assert!(keygen(&secret, &public, None, NextKey::Beside, false).is_err());
        assert!(!secret.exists());
        assert_eq!(fs::read(&public).unwrap(), b"existing-public");

        let source = directory.join("source");
        fs::write(&source, b"replacement").unwrap();
        assert!(copy_new(&source, &public).is_err());
        assert_eq!(fs::read(&public).unwrap(), b"existing-public");
        fs::remove_dir_all(directory).unwrap();
    }

    #[cfg(unix)]
    #[test]
    fn read_secret_requires_owner_private_regular_32_byte_file() {
        use std::os::unix::fs::{symlink, PermissionsExt};
        let directory = scratch("read-secret-custody");
        let key = directory.join("mini.key");
        create_private(&key, &[5u8; 32]).unwrap();
        assert_eq!(read_secret(&key).unwrap().to_bytes(), [5u8; 32]);
        for mode in [0o640, 0o604, 0o620, 0o644] {
            fs::set_permissions(&key, fs::Permissions::from_mode(mode)).unwrap();
            assert!(read_secret(&key).unwrap_err().contains("owner-private"), "mode {mode:o}");
        }
        fs::set_permissions(&key, fs::Permissions::from_mode(0o600)).unwrap();
        // A signing seed is never read through a symlink, even to a private target.
        let link = directory.join("link.key");
        symlink(&key, &link).unwrap();
        assert!(read_secret(&link).is_err());
        assert!(read_secret(&directory).unwrap_err().contains("regular file"));
        let long = directory.join("long.key");
        create_private(&long, &[5u8; 33]).unwrap();
        assert!(read_secret(&long).unwrap_err().contains("exactly 32"));
        fs::remove_dir_all(directory).unwrap();
    }

    #[cfg(unix)]
    #[test]
    fn selected_release_sign_requires_exact_host_checked_bytes_and_private_key() {
        use std::os::unix::fs::PermissionsExt;

        let directory = scratch("selected-release-sign");
        let host = directory.join("host.sh");
        let config = directory.join("config.json");
        let preimage = directory.join("preimage.bin");
        let key = directory.join("owner.key");
        let signature = directory.join("owner.sig");
        fs::write(&host, b"#!/bin/sh\ncp \"$3\" \"$4\"\n").unwrap();
        fs::set_permissions(&host, fs::Permissions::from_mode(0o700)).unwrap();
        fs::write(&config, b"{}\n").unwrap();
        fs::write(&preimage, b"exact host-authored preimage").unwrap();
        fs::write(&key, [9u8; 32]).unwrap();
        fs::set_permissions(&key, fs::Permissions::from_mode(0o644)).unwrap();
        assert!(
            selected_release_sign(&host, &config, &preimage, &key, &signature)
                .unwrap_err()
                .contains("owner-private")
        );
        assert!(!signature.exists());
        fs::set_permissions(&key, fs::Permissions::from_mode(0o600)).unwrap();
        fs::write(&host, b"#!/bin/sh\nprintf changed >\"$4\"\n").unwrap();
        assert!(
            selected_release_sign(&host, &config, &preimage, &key, &signature)
                .unwrap_err()
                .contains("differs from exact input")
        );
        assert!(!signature.exists());
        fs::write(&host, b"#!/bin/sh\ncp \"$3\" \"$4\"\n").unwrap();
        selected_release_sign(&host, &config, &preimage, &key, &signature).unwrap();
        let bytes: [u8; 64] = fs::read(&signature).unwrap().try_into().unwrap();
        let public = SigningKey::from_bytes(&[9; 32]).verifying_key();
        public
            .verify_strict(
                b"exact host-authored preimage",
                &ed25519_dalek::Signature::from_bytes(&bytes),
            )
            .unwrap();
        assert_eq!(
            fs::metadata(&signature).unwrap().permissions().mode() & 0o077,
            0
        );
        fs::remove_dir_all(directory).unwrap();
    }

    #[cfg(unix)]
    #[test]
    fn retry_reuses_retained_call_and_never_replaces_prior_evidence() {
        use std::os::unix::fs::PermissionsExt;

        let directory = scratch("exact-retry");
        let host = directory.join("fake-host.sh");
        let config = directory.join("config.json");
        let call = directory.join("call.bin");
        // The one-shot verbs (submit, lookup) echo the call; `inspect` is the storeless codec
        // loop's, as every pure verb is (`client_consent::codec_loop_arm`).
        fs::write(
            &host,
            format!("#!/bin/sh\ncase \"$2\" in\n{}  *) cp \"$3\" \"$4\" ;;\nesac\n",
                client_consent::codec_loop_arm(r#"printf '{"type":"confirmed"}' > "$out""#)),
        )
        .unwrap();
        fs::set_permissions(&host, fs::Permissions::from_mode(0o700)).unwrap();
        fs::write(&config, b"{}").unwrap();
        fs::write(&call, [0, 1, 2, 255, 17]).unwrap();
        let _codec = client_consent::codec_test_lock();
        write_json_new(
            &directory.join("attempt.json"),
            &json!({
                "format": "minidregg-resource-client-attempt-v1",
                "operation": "submit",
                "host": host,
                "config": config
            }),
        )
        .unwrap();

        retry(&directory, "submit", false).unwrap();
        let first = fs::read(directory.join("retry-0001.bin")).unwrap();
        retry(&directory, "lookup", false).unwrap();
        assert_eq!(fs::read(&call).unwrap(), [0, 1, 2, 255, 17]);
        assert_eq!(first, [0, 1, 2, 255, 17]);
        assert_eq!(fs::read(directory.join("retry-0002.bin")).unwrap(), first);
        assert!(directory.join("retry-0001.json").is_file());
        assert!(directory.join("retry-0002.json").is_file());
        fs::remove_dir_all(directory).unwrap();
    }
}

#[cfg(test)]
mod concurrent_request_scratch_tests {
    use super::*;
    #[test]
    fn concurrent_requests_keep_exact_refusal_and_recovery_class() {
        let barrier = std::sync::Arc::new(std::sync::Barrier::new(5));
        let mut workers = Vec::new();
        for member in 0..4 {
            let barrier = barrier.clone();
            workers.push(std::thread::spawn(move || {
                let outcome = json!({"type":"refused", "reason":format!("member-{member}")});
                note_host_decision(HostDecision::Outcome(outcome.clone()));
                note_command_ending(CommandEnding::Undecided(format!("attempt-{member}")));
                note_line_refusal(format!("line-{member}"));
                barrier.wait();
                assert_eq!(take_host_decision(), Some(HostDecision::Outcome(outcome)));
                assert!(matches!(take_command_ending(), Some(CommandEnding::Undecided(id)) if id == format!("attempt-{member}")));
                assert_eq!(take_line_refusal(), Some(format!("line-{member}")));
                assert_eq!(take_host_decision(), None);
            }));
        }
        barrier.wait();
        assert!(take_host_decision().is_none());
        for worker in workers { worker.join().unwrap(); }
    }
}

#[cfg(test)]
mod ascii_hex_regression {
    #[test]
    fn refuses_non_ascii_without_panicking() {
        for value in ["aéa", "é", "💥", "+a", "00éé", "a"] {
            assert!(super::decode_hex(value).is_err(), "{value:?}");
        }
        assert_eq!(super::decode_hex("00AaFF").unwrap(), [0, 170, 255]);
        assert!(super::decode_hex("").unwrap().is_empty());
        // A Host plan header (pay refill reads one) with multi-byte text: the old slicing decoder
        // panicked on the char boundary; signs, prefixes, odd lengths and spaces refuse too.
        for bad in ["a\u{e9}", "-1", "0x", "abc", "zz", " 1"] {
            assert!(super::decode_hex(bad).is_err(), "{bad:?}");
        }
    }
}
