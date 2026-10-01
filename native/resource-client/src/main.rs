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
mod agent_lifetime_grant;
#[cfg(unix)]
mod key_rotation;
#[cfg(unix)]
mod agent_payer;
#[cfg(unix)]
mod agent_reserve;
#[cfg(unix)]
mod current_birth;
#[cfg(unix)]
mod drain;
#[cfg(unix)]
mod fn_frontier;
#[cfg(unix)]
mod fleet;
#[cfg(unix)]
mod fleet_sign;
#[cfg(unix)]
mod fn_namespace;
#[cfg(unix)]
mod grain_share_issue;
#[cfg(unix)]
mod historical_call_receipt;
#[cfg(unix)]
mod meter;
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
mod proxy;
#[cfg(unix)]
mod publisher;
#[cfg(unix)]
mod selected_exchange;
#[cfg(unix)]
mod selected_publisher;
#[cfg(unix)]
mod selected_release;
#[cfg(unix)]
mod session_enrollment;
#[cfg(unix)]
mod share_issue;
#[cfg(unix)]
mod share_issue_receipt;
#[cfg(unix)]
mod chat;
#[cfg(unix)]
mod credit;
mod keys;
#[cfg(unix)]
mod shell;
#[cfg(unix)]
mod transport;
#[cfg(unix)]
mod worker;
#[cfg(unix)]
mod workspace;
#[cfg(unix)]
mod well;

static SOCKET: OnceLock<PathBuf> = OnceLock::new();
#[cfg(unix)]
static EXPECTED_HOST_SHA: OnceLock<String> = OnceLock::new();
static QUIET_WORKER: AtomicBool = AtomicBool::new(false);
/// The exit status a verb chose besides success (1): 3 = the Host refused, 4 = the Host did
/// not decide (M4's shell contract). The highest one set wins.
static EXIT_STATUS: AtomicU8 = AtomicU8::new(0);

fn set_exit(code: u8) {
    EXIT_STATUS.fetch_max(code, Ordering::Relaxed);
}

/// The Host's own verdict on the latest request, retained as data at the point
/// where the Host answered, so a caller (`mini shell`) can tell a Host decision
/// from a client error without reading error prose.
#[derive(Clone, Debug, PartialEq)]
pub(crate) enum HostDecision {
    /// The Host session reply carried a refusal byte; `encoded` is the rest of
    /// the frame (an outcome encoded by the Host's own codec). `decoded` is the
    /// Host's own `inspect outcome` of that frame over the same session, when
    /// it could be asked; the client never decodes the frame itself.
    RefusedFrame {
        command: String,
        byte: u8,
        encoded: Vec<u8>,
        decoded: Option<Value>,
    },
    /// The Host returned a decoded outcome whose type is not `confirmed`.
    Outcome(Value),
}

static HOST_DECISION: Mutex<Option<HostDecision>> = Mutex::new(None);

pub(crate) fn note_host_decision(decision: HostDecision) {
    *HOST_DECISION
        .lock()
        .unwrap_or_else(|poisoned| poisoned.into_inner()) = Some(decision);
}

pub(crate) fn take_host_decision() -> Option<HostDecision> {
    HOST_DECISION
        .lock()
        .unwrap_or_else(|poisoned| poisoned.into_inner())
        .take()
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
    match decode_hex(hex)
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
    Some(format!(
        "refused: {reason}: {} (phase {})",
        outcome_text(outcome.get("detail")),
        outcome_text(outcome.get("phase"))
    ))
}

/// The line `mini` prints when the Host decided a refusal, from the recorded
/// decision only.
fn host_refusal_ending(decision: &HostDecision) -> Option<String> {
    match decision {
        HostDecision::RefusedFrame {
            command,
            byte,
            decoded: Some(outcome),
            ..
        } => refusal_line(outcome)
            .map(|line| format!("{line}\n  Host refused {command}, reply byte {byte}")),
        HostDecision::RefusedFrame { command, byte, .. } => Some(format!(
            "refused: Host refused {command}, reply byte {byte}; the frame was not decoded"
        )),
        HostDecision::Outcome(outcome) => refusal_line(outcome),
    }
}

/// The SHA-256 of the Host image this process selects. A remote client has no
/// Host image: its Host is named by an empty path and known only by the digest
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
    let mut file = File::open(host).map_err(|error| {
        format!(
            "cannot open selected Host image {}: {error}",
            host.display()
        )
    })?;
    if !file
        .metadata()
        .map_err(|error| {
            format!(
                "cannot inspect selected Host image {}: {error}",
                host.display()
            )
        })?
        .is_file()
    {
        return Err("selected Host image is not a regular file".into());
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
            return Ok(hex(&digest.finalize()));
        }
        digest.update(&buffer[..count]);
    }
}

#[cfg(unix)]
fn session_invoke(
    host: &Path,
    socket: &Path,
    config: &Path,
    operation: u8,
    payload: &[u8],
) -> Result<Vec<u8>> {
    let selected_sha = host_image_sha256(host)?;
    if let Some(sha) = EXPECTED_HOST_SHA.get() {
        if sha != &selected_sha {
            return Err("selected Host image differs from durable worker pin".into());
        }
    }
    transport::invoke_pinned(socket, config, &selected_sha, operation, payload)
}

#[cfg(unix)]
fn pin_worker_host_image(state_dir: &Path) -> Result<()> {
    let pin: Value =
        serde_json::from_slice(&fs::read(state_dir.join("pin.json")).map_err(|e| e.to_string())?)
            .map_err(|e| e.to_string())?;
    if matches!(
        pin.get("type").and_then(Value::as_str),
        Some("minidregg-b-consumer-worker-pin-v2" | "minidregg-a-reply-consumer-worker-pin-v2")
    ) {
        let sha = pin
            .get("hostSha256")
            .and_then(Value::as_str)
            .ok_or("v2 worker pin lacks host image digest")?
            .to_owned();
        if let Some(existing) = EXPECTED_HOST_SHA.get() {
            if existing != &sha {
                return Err("worker host image changed within process".into());
            }
        } else {
            EXPECTED_HOST_SHA
                .set(sha)
                .map_err(|_| "cannot pin worker host image")?;
        }
    }
    Ok(())
}

const USAGE: &str = r#"mini — custody and exact-retry client for minidregg-host

usage:
  mini [--remote DEST] COMMAND [options]
  mini keygen --secret KEY --public PUBLIC [--next-to NEXT-KEY | --no-prerotation] [--escrow-to-sponsor @FILE|HEX --escrow-subject SUBJECT]
  mini rotate-key --workspace WORKSPACE --next-key NEXT-KEY [--next-to PATH]
  mini key-status --workspace WORKSPACE [--next-public-key NEXT.pub]
  mini join --key KEY
  mini join --remote DEST --key KEY --sponsor-plan PLAN.json --dir JOIN-ROOT
  mini join --remote DEST --key KEY --welcome WELCOME.json --dir JOIN-ROOT
  mini shell --remote DEST --workspace JOIN-ROOT/workspace --home SESSION-HOME [--line LINE]
  mini socket-proxy --socket PUBLIC-SOCKET
  mini pay address|status --dir WORKSPACE [--account REF]
  mini pay book --dir OPERATOR-WORKSPACE --source {"control","book":[ADDRESS...],"tariff":{...}|null}.json
  mini pay watch-config --dir OBSERVER-WORKSPACE --out CONFIG.json [--min-endpoints N] [--max-pages N] [--page-size N] [--enrol-index I --journal-floor F]
  mini pay observe --dir OBSERVER-WORKSPACE --capability CAP (--from OBSERVATIONS.json|- [--hold true] | --resume ATTEMPT)
  mini pay heartbeat --dir OBSERVER-WORKSPACE --capability CAP --slot SLOT --block-time TIME
  mini pay audit --dir OBSERVER-WORKSPACE [--offline true]
  mini pay refill --mode submit --host HOST --config PINNED-CONFIG.json --socket SOCKET --key OWNER.key --dir NEW-ATTEMPT --subject S --capability C --account A --task T --amount N [--gain G]
  mini pay refill --mode lookup --host HOST --config PINNED-CONFIG.json --socket SOCKET --dir ATTEMPT
  mini enc-public --secret KEY
  mini escrow-recover --escrow PUBLIC.escrow --sponsor-secret KEY --subject SUBJECT --secret NEW-KEY
  mini workspace --action init|import|list|describe|read|tail|submit|recover|create|propose|publish-delegation --dir WORKSPACE [action options]
  mini workspace --action room-key --op found|sync|invite|rotate|kick|list|open|forget --dir WORKSPACE --name ROOM [op options]
  mini enroll --action plan --sponsor-workspace WORKSPACE --factory-ref NAME --name REQUEST-LABEL --new-key KEY [--next-public-key KEY.next.pub | --no-prerotation] --dir ATTEMPT [--operator-socket PRIVATE-SOCKET]
  mini enroll --action plan --sponsor-workspace WORKSPACE --factory-ref NAME --name REQUEST-LABEL --new-public-key PUBLIC [--home-subject N] --dir ATTEMPT
  mini enroll --action offer|welcome --dir ATTEMPT [--birth-context CONTEXT.json]
  mini enroll --action possess --dir ATTEMPT --key KEY --subject N --output SIGNATURE.bin
  mini enroll --action seal --dir ATTEMPT [--possession-signature SIGNATURE.bin]
  mini enroll --action submit|lookup --dir ATTEMPT
  mini key --action set|grant|revoke|ls (--dir WORKSPACE | --pool true) [--provider NAME] [--secret FILE|-] [--runner SUBJECT --per-call TOKENS --per-day CALLS --until HEIGHT] [--providers TABLE] [--credentials ROOT --credentials-key KEY]
  mini shell --socket SOCKET --host HOST --config CONFIG.json --workspace WORKSPACE --home SESSION-HOME [--line LINE]
  mini fleet --action join --sponsor-workspace WORKSPACE --factory-ref NAME --name LABEL --new-key KEY --enroll-dir ATTEMPT --dir NEW-WORKSPACE --fund AMOUNT [--account-name NAME]
  mini fleet --action send|publish --dir WORKSPACE --account NAME --topic TOPIC (--payload TEXT|--payload-hex HEX) [--to ACCOUNT --amount N [--asset ID]]
  mini fleet --action transfer --dir WORKSPACE --account NAME --to ACCOUNT --amount N [--asset ID]
  mini fleet --action receipt --dir WORKSPACE (--transaction ID|--head-of NAME)
  mini fleet --action lookup --dir WORKSPACE --attempt WORKSPACE/attempts/a-NONCE
  mini fleet --action incoming --dir WORKSPACE --account NAME [--topic TOPIC] [--since HEIGHT] [--limit N]
  mini credit --action balance|room|tariff|pay|topup|renew|status|ledger|install|adopt --dir WORKSPACE [--room REF] … (PLACE §2.10; `mini shell` spells them credit / pay ROOM week / tariff / topup / room status|renew|concierge)
  mini fleet --action poll --dir WORKSPACE --account NAME --topic TOPIC [--since CURSOR] [--limit N]
  mini fleet --action feed --dir WORKSPACE --accounts NAME[,NAME...] --topic TOPIC   (one topic, several authors: one feed ordered by admission height)
  mini well --action new --dir WORKSPACE --name NAME --in REALM --law LAW.json
  mini well --action mint|burn --dir WORKSPACE --well NAME|ID --account NAME|ID --amount N [--capability ID] [--attempt NEW-DIR]
  mini well --action ledger --dir WORKSPACE --output LEDGER.json
  mini fleet-sign join|send|transfer|receipt|retry [--profile P] ...   (dregg-client-sign's verbs on Mini; `mini fleet-sign --help`)
  mini selected-exchange --phase prepare|status|publish|receive|receive-transport|cover-plan|cover-advance|ack|verify|verify-transport --contract CONTRACT.json --state-dir PRIVATE-STATE [--approval APPROVAL.json]
  mini profile --host HOST --config CONFIG.json [--socket SOCKET]
  mini describe --host HOST --config CONFIG.json [--socket SOCKET]
  mini bootstrap --host HOST --config OPERATOR.json --source GENESIS.json --dir DEPLOYMENT
  mini audit --host HOST --config PINNED.json
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
  mini agent-lifetime-grant-lookup --attempt PRIVATE-DIR
  mini session-enrollment-plan --host HOST --config CONFIG.json --operator-socket PRIVATE-SOCKET --request SOURCE.json --dir NEW-PRIVATE-DIR
  mini session-enrollment-seal --attempt PRIVATE-DIR --approval OPERATOR-PRIVATE-APPROVAL.json
  mini session-enrollment-submit --attempt PRIVATE-DIR
  mini session-enrollment-lookup --attempt PRIVATE-DIR
  mini agent-payer-sign --host HOST --config CONFIG.json --operator-socket PRIVATE-SOCKET --reserve-attempt ORIGINAL-RESERVE-DIR --plan PAID-PLAN.bin --approval OPERATOR-PRIVATE-APPROVAL.json --key PAYER-SEED.bin --dir NEW-PRIVATE-DIR
  mini inspect --host HOST --config CONFIG.json [--socket SOCKET] --kind fn-inbox-resource|application-permission-schema --input VIEW.bin --output RESULT.json
  mini submit --host HOST --config CONFIG.json --intent INTENT.json [--intent-kind KIND] [--prepare-only true] --key KEY --dir ATTEMPT
  mini query --host HOST --config CONFIG.json --intent INTENT.json [--intent-kind KIND] --key KEY --view resource|policy|capability [--presentation fn-inbox-resource] --dir ATTEMPT
  mini retry --attempt ATTEMPT [--mode submit|lookup] [--socket SOCKET|--direct true]
  mini selected-release-submit --host HOST --config CONFIG.json --socket SOCKET --ingress INGRESS.bin --dir NEW-ATTEMPT
  mini selected-release-sign --host HOST --config SOURCE-CONFIG.json --preimage PREIMAGE.bin --key OWNER.key --output SIGNATURE.bin
  mini selected-source-sign --host HOST --config SOURCE-CONFIG.json --packet PACKET.bin --delegate-capability DECIMAL --key OWNER.key --dir NEW-PRIVATE-DIR
  mini selected-source-publish --host HOST --config SOURCE-CONFIG.json --ingress INGRESS.bin --article ARTICLE.eml --state-dir PRIVATE-DIR --post-config PRIVATE-POST.json
  mini selected-release-lookup --attempt ATTEMPT [--socket SOCKET]
  mini selected-release-retry --attempt ATTEMPT [--socket SOCKET]
  mini fn-namespace-plan --host HOST --config FN-POLL-CONFIG.json --socket OPERATOR-SOCKET --state-dir NEW-PRIVATE-DIR
  mini fn-namespace-register --state-dir PRIVATE-DIR --key GATEWAY.key --approval APPROVAL.json
  mini fn-namespace-lookup --state-dir PRIVATE-DIR
  mini fn-frontier-plan --host HOST --config FN-POLL-CONFIG.json --socket OPERATOR-SOCKET --kind selected|empty --transaction MINI-TX|- --state-dir NEW-PRIVATE-DIR
  mini fn-frontier-advance --state-dir PRIVATE-DIR --key GATEWAY.key --approval APPROVAL.json
  mini fn-frontier-lookup --state-dir PRIVATE-DIR
  mini export-evidence --host HOST --config CONFIG.json --call CALL.bin --output PACKAGE.bin
  mini verify-evidence --host HOST --config INDEPENDENT-PIN.json --package PACKAGE.bin --output RESULT.json
  mini serve --host HOST --config CONFIG.json --socket PRIVATE-DIR/mini.sock
  mini serve-operator --host HOST --config CONFIG.json --socket OPERATOR-PRIVATE-DIR/mini.sock
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
  mini host-command --host HOST --config CONFIG.json --command FN-COMMAND [--arg ARG ...]
  mini consumer-poll --host HOST --config FN-POLL-CONFIG.json --socket SOCKET --dir NEW-ATTEMPT
  mini consumer-ack --host HOST --config FN-POLL-CONFIG.json --socket SOCKET --mini-transaction ID --dir NEW-ATTEMPT
  mini reply-consumer-poll --host HOST --config FN-REPLY-POLL-CONFIG.json --socket SOCKET --dir NEW-ATTEMPT
  mini reply-consumer-ack --host HOST --config FN-REPLY-POLL-CONFIG.json --socket SOCKET --mini-transaction ID --dir NEW-ATTEMPT
  mini origin-outbox-prepare --host HOST --config FN-REPLY-CATALOG-CONFIG.json --socket SOCKET --carrier R.eml --dir NEW-ATTEMPT
  mini origin-outbox-export --host HOST --config FN-REPLY-CATALOG-CONFIG.json --socket SOCKET --mini-transaction ID --dir NEW-ATTEMPT
  mini origin-publish --host HOST --config FN-REPLY-CATALOG-CONFIG.json --socket SOCKET --key KEY --carrier R.eml --state-dir PRIVATE-DIR --post-config PRIVATE-POST.json
  mini continuity --host HOST --config CONFIG.json --socket SOCKET --call RESERVE/call.bin --outcome RESERVE/outcome.bin --dir NEW-ATTEMPT
  mini meter --host HOST --config CONFIG.json --socket SOCKET --metadata META.json --request REQUEST.bin --response RESPONSE.bin --dir NEW-ATTEMPT
  mini consumer-drain-once --host HOST --config FN-POLL-CONFIG.json --socket SOCKET --key KEY --state-dir PRIVATE-DIR [--max-pages 16]
  mini reply-consumer-drain-once --host HOST --config FN-REPLY-CATALOG-CONFIG.json --socket SOCKET --key KEY --state-dir PRIVATE-DIR [--max-pages 16]
  mini consumer-resume-ack --host HOST --config FN-POLL-CONFIG.json --socket SOCKET --key KEY --state-dir PRIVATE-DIR
  mini reply-consumer-resume-ack --host HOST --config FN-REPLY-CATALOG-CONFIG.json --socket SOCKET --key KEY --state-dir PRIVATE-DIR
  mini consumer-host-upgrade --old-host OLD-HOST --old-sha256 SHA256 --new-host NEW-HOST --new-sha256 SHA256 --config FN-POLL-CONFIG.json --socket SOCKET --key KEY --state-dir PRIVATE-DIR --known-outcome CONFIRMED.bin --known-sha256 SHA256
  mini consumer-worker --host HOST --config FN-POLL-CONFIG.json --socket SOCKET --key KEY --state-dir PRIVATE-DIR --worker-config PRIVATE-WAKE.json
  mini reply-consumer-worker --host HOST --config FN-REPLY-CATALOG-CONFIG.json --socket SOCKET --key KEY --state-dir PRIVATE-DIR --worker-config PRIVATE-WAKE.json

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
    "workspace", "enroll", "join", "shell", "submit", "query", "retry", "author", "inspect",
    "describe", "profile",
];

#[derive(Debug)]
struct Args {
    command: OsString,
    values: Vec<(OsString, OsString)>,
}

impl Args {
    fn parse() -> Result<Self> {
        let mut raw = env::args_os().skip(1);
        let mut values = Vec::new();
        let mut command = raw.next().ok_or_else(|| USAGE.to_owned())?;
        if command == OsStr::new("--remote") {
            let destination = raw.next().ok_or("missing value for --remote")?;
            values.push((command, destination));
            command = raw.next().ok_or_else(|| USAGE.to_owned())?;
        }
        if command == OsStr::new("--help") || command == OsStr::new("-h") {
            return Err(USAGE.to_owned());
        }
        let mut raw = raw.peekable();
        // `mini pay ACTION ...` (PAY.md §5 spells the verbs this way) is `mini pay --action ACTION ...`.
        if command == OsStr::new("pay") {
            if let Some(action) = raw.next_if(|next| !next.to_string_lossy().starts_with("--")) {
                values.push((OsString::from("--action"), action));
            }
        }
        while let Some(flag) = raw.next() {
            let rendered = flag.to_string_lossy();
            if !rendered.starts_with("--") || rendered.len() == 2 {
                return Err(format!("unexpected argument {rendered}\n\n{USAGE}"));
            }
            // The one valueless switch: opting out of pre-rotation is a
            // deliberate act and reads as one.
            if rendered == "--no-prerotation" {
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

fn create_private(path: &Path, bytes: &[u8]) -> Result<()> {
    let mut options = OpenOptions::new();
    options.write(true).create_new(true);
    #[cfg(unix)]
    {
        use std::os::unix::fs::OpenOptionsExt;
        options.mode(0o600);
    }
    let mut file = options
        .open(path)
        .map_err(|error| format!("cannot create {}: {error}", path.display()))?;
    file.write_all(bytes)
        .and_then(|()| file.sync_all())
        .map_err(|error| format!("cannot write {}: {error}", path.display()))
}

fn create_public(path: &Path, bytes: &[u8]) -> Result<()> {
    let mut file = OpenOptions::new()
        .write(true)
        .create_new(true)
        .open(path)
        .map_err(|error| format!("cannot create {}: {error}", path.display()))?;
    file.write_all(bytes)
        .and_then(|()| file.sync_all())
        .map_err(|error| format!("cannot write {}: {error}", path.display()))
}

fn read_secret(path: &Path) -> Result<SigningKey> {
    let bytes = fs::read(path)
        .map_err(|error| format!("cannot read signing key {}: {error}", path.display()))?;
    let seed: [u8; 32] = bytes.try_into().map_err(|_| {
        format!(
            "signing key {} must contain exactly 32 raw bytes",
            path.display()
        )
    })?;
    Ok(SigningKey::from_bytes(&seed))
}

#[cfg(unix)]
fn selected_release_sign(
    host: &Path,
    config: &Path,
    preimage: &Path,
    key: &Path,
    output: &Path,
) -> Result<()> {
    use std::os::unix::fs::MetadataExt;
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
    let named =
        fs::symlink_metadata(key).map_err(|e| format!("cannot inspect owner signing key: {e}"))?;
    let mut key_file =
        File::open(key).map_err(|e| format!("cannot open owner signing key: {e}"))?;
    let opened = key_file
        .metadata()
        .map_err(|e| format!("cannot inspect opened owner signing key: {e}"))?;
    unsafe extern "C" {
        fn geteuid() -> u32;
    }
    if !named.file_type().is_file()
        || named.uid() != unsafe { geteuid() }
        || named.mode() & 0o077 != 0
        || (named.dev(), named.ino()) != (opened.dev(), opened.ino())
    {
        return Err("owner signing key must be an owner-private regular file".into());
    }
    let mut seed = [0u8; 32];
    key_file
        .read_exact(&mut seed)
        .map_err(|e| format!("owner signing key must contain 32 bytes: {e}"))?;
    let mut excess = [0u8; 1];
    if key_file
        .read(&mut excess)
        .map_err(|e| format!("cannot finish owner signing key read: {e}"))?
        != 0
    {
        return Err("owner signing key must contain exactly 32 bytes".into());
    }
    let signing = SigningKey::from_bytes(&seed);
    seed.fill(0);
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
    let mut builder = fs::DirBuilder::new();
    use std::os::unix::fs::DirBuilderExt;
    builder.mode(0o700);
    builder
        .create(&temporary)
        .map_err(|e| format!("cannot create private source check directory: {e}"))?;
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
    let mut seed = [0u8; 32];
    File::open("/dev/urandom")
        .and_then(|mut source| source.read_exact(&mut seed))
        .map_err(|error| format!("cannot obtain operating-system randomness: {error}"))?;
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
            let key: [u8; 32] = workspace::private::decode_hex(text.trim())?
                .try_into()
                .map_err(|_| "the sponsor encryption key is exactly 32 bytes".to_owned())?;
            let subject = subject.to_str().ok_or("--escrow-subject must be UTF-8")?;
            Some(workspace::private::escrow_seed(subject, &seed, &x25519_dalek::PublicKey::from(key))?)
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
    if let Some(wrapped) = escrowed {
        let mut escrow_path = public.as_os_str().to_owned();
        escrow_path.push(".escrow");
        create_private(Path::new(&escrow_path), &wrapped.to_bytes())?;
    }
    eprintln!("{}", workspace::private::KEYGEN_NOTICE);
    match &next_paths {
        None => eprintln!("no next key (--no-prerotation): this identity can never rotate; a stolen key is replaced only by enrolling a new subject"),
        Some((next_secret, next_public)) => {
            let mut next_seed = [0u8; 32];
            File::open("/dev/urandom")
                .and_then(|mut source| source.read_exact(&mut next_seed))
                .map_err(|error| format!("cannot obtain operating-system randomness: {error}"))?;
            let next_signing = SigningKey::from_bytes(&next_seed);
            create_private(next_secret, &next_seed)?;
            next_seed.fill(0);
            create_public(next_public, &next_signing.verifying_key().to_bytes())?;
            eprintln!("next key: {} (its public half: {})", next_secret.display(), next_public.display());
            eprintln!("{}", key_rotation::PREROTATION_NOTICE);
            if hosted {
                eprintln!("{}", key_rotation::HOSTED_PREROTATION_NOTICE);
            }
        }
    }
    Ok(signing.verifying_key().to_bytes())
}

fn process(host: &Path, config: &Path, arguments: &[&OsStr]) -> Result<Output> {
    if let Some(socket) = SOCKET.get() {
        return socket_process(host, socket, config, arguments);
    }
    if host.as_os_str().is_empty() {
        return Err("no Host image and no socket: pass --remote or --socket".into());
    }
    let output = Command::new(host)
        .arg(config)
        .args(arguments)
        .output()
        .map_err(|error| format!("cannot run {}: {error}", host.display()))?;
    if !output.status.success() {
        return Err(format!(
            "{} exited {}; request status uncertain: {}",
            host.display(),
            output.status,
            String::from_utf8_lossy(&output.stderr).trim()
        ));
    }
    Ok(output)
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
        let mut file = File::open(path)
            .map_err(|e| format!("cannot read host input {}: {e}", path.display()))?;
        let mut bytes = Vec::new();
        Read::by_ref(&mut file)
            .take((transport::HOST_MAX_FRAME + 1) as u64)
            .read_to_end(&mut bytes)
            .map_err(|e| format!("cannot read host input {}: {e}", path.display()))?;
        if bytes.len() > transport::HOST_MAX_FRAME {
            return Err(format!(
                "host input {} exceeds session frame bound",
                path.display()
            ));
        }
        Ok(bytes)
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
        "challenge" if arguments.len() == 3 => (4, read(1)?, Some(arguments[2])),
        "query" if arguments.len() == 3 => (5, read(1)?, Some(arguments[2])),
        "author" if arguments.len() == 4 => {
            (7, kind_payload(arguments[1], read(2)?)?, Some(arguments[3]))
        }
        "inspect" if arguments.len() == 4 => {
            (8, kind_payload(arguments[1], read(2)?)?, Some(arguments[3]))
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
    if reply[0] == 255 {
        // Ask the same Host session to decode its own frame (op 8, `inspect
        // outcome`). A failed decode leaves the decision undecoded; it is
        // never reconstructed here.
        let decoded = kind_payload(OsStr::new("outcome"), reply[1..].to_vec())
            .and_then(|request| session_invoke(host, socket, config, 8, &request))
            .ok()
            .filter(|inspected| inspected.first() == Some(&8))
            .and_then(|inspected| serde_json::from_slice::<Value>(&inspected[1..]).ok());
        let line = decoded.as_ref().and_then(refusal_line);
        note_host_decision(HostDecision::RefusedFrame {
            command: command.to_owned(),
            byte: 255,
            encoded: reply[1..].to_vec(),
            decoded,
        });
        if command == "prepare" {
            let destination = Path::new(arguments[2]);
            prepare_refusal::retain(destination, &payload, config, &reply)?;
        }
        return Err(match line {
            Some(line) => format!(
                "host refused {command}: {line}; encoded refusal: {}",
                hex(&reply[1..])
            ),
            None => format!(
                "host refused {command}; encoded refusal: {}",
                hex(&reply[1..])
            ),
        });
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
fn sync_directory_ancestors(directory: &Path) -> Result<()> {
    let mut ancestor = Some(absolute(directory)?);
    while let Some(path) = ancestor {
        File::open(&path)
            .and_then(|file| file.sync_all())
            .map_err(|error| {
                format!("cannot sync attempt directory {}: {error}", path.display())
            })?;
        ancestor = path.parent().map(Path::to_path_buf);
    }
    Ok(())
}

fn sync_retained_call(directory: &Path, call: &Path) -> Result<()> {
    File::open(call)
        .and_then(|file| file.sync_all())
        .map_err(|error| format!("cannot sync exact call {}: {error}", call.display()))?;
    sync_directory_ancestors(directory)
}

fn copy_new(source: &Path, destination: &Path) -> Result<()> {
    let mut input =
        File::open(source).map_err(|error| format!("cannot open {}: {error}", source.display()))?;
    let mut output = OpenOptions::new()
        .write(true)
        .create_new(true)
        .open(destination)
        .map_err(|error| format!("cannot create {}: {error}", destination.display()))?;
    io::copy(&mut input, &mut output)
        .and_then(|_| output.sync_all())
        .map_err(|error| {
            format!(
                "cannot copy {} to {}: {error}",
                source.display(),
                destination.display()
            )
        })
}

fn write_new(path: &Path, bytes: &[u8]) -> Result<()> {
    create_public(path, bytes)
}

/// The Store's checkpoint/log MAC key: 32 bytes of operating-system
/// randomness, mode 0600, beside the pinned configuration. One per Store; it
/// authenticates only that Store's checkpoints and log tags. It is never
/// printed, copied into another artifact, or committed.
fn checkpoint_key(path: &Path) -> Result<()> {
    let mut key = [0u8; 32];
    File::open("/dev/urandom")
        .and_then(|mut source| source.read_exact(&mut key))
        .map_err(|error| format!("cannot obtain operating-system randomness: {error}"))?;
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
            let decoded = decode_hex(canonical)?;
            if hex(&decoded) != canonical || Some(decoded.as_slice()) != input {
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
    let mut builder = fs::DirBuilder::new();
    #[cfg(unix)]
    {
        use std::os::unix::fs::DirBuilderExt;
        builder.mode(0o700);
    }
    builder
        .create(&temporary)
        .map_err(|error| format!("cannot create private inspection directory: {error}"))?;
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

fn decode_hex(value: &str) -> Result<Vec<u8>> {
    if !value.len().is_multiple_of(2) {
        return Err("host emitted odd-length header hex".to_owned());
    }
    value
        .as_bytes()
        .chunks(2)
        .map(|pair| {
            std::str::from_utf8(pair)
                .ok()
                .and_then(|text| u8::from_str_radix(text, 16).ok())
                .ok_or_else(|| "host emitted non-hex header".to_owned())
        })
        .collect()
}

fn hex(bytes: &[u8]) -> String {
    const DIGITS: &[u8; 16] = b"0123456789abcdef";
    let mut output = String::with_capacity(bytes.len() * 2);
    for byte in bytes {
        output.push(DIGITS[(byte >> 4) as usize] as char);
        output.push(DIGITS[(byte & 15) as usize] as char);
    }
    output
}

fn challenge_headers(value: &Value) -> Result<Vec<Vec<u8>>> {
    let headers = value
        .get("headers")
        .and_then(Value::as_array)
        .ok_or_else(|| "host challenge JSON has no headers array".to_owned())?;
    headers
        .iter()
        .map(|header| {
            header
                .as_str()
                .ok_or_else(|| "host challenge header is not a string".to_owned())
                .and_then(decode_hex)
        })
        .collect()
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
                .and_then(decode_hex)
        })
        .collect()
}

fn sign_headers(signing: &SigningKey, headers: &[Vec<u8>]) -> Value {
    Value::Array(
        headers
            .iter()
            .map(|header| Value::String(hex(&signing.sign(header).to_bytes())))
            .collect(),
    )
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
    print_json(value)?;
    if value.get("type").and_then(Value::as_str) != Some("confirmed") {
        note_host_decision(HostDecision::Outcome(value.clone()));
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
    write_json_new(json_path, &sign_headers(signing, &headers))?;
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
        "socket": SOCKET.get().map(|socket| transport::pinned_address(socket)).transpose()?
    });
    if host.as_os_str().is_empty() {
        manifest["hostSha256"] = json!(host_image_sha256(host)?);
    } else {
        manifest["host"] = json!(utf8_path(&absolute(host)?)?);
    }
    write_json_new(&directory.join("attempt.json"), &manifest)
}

/// Pins, for this process, the Host digest a remote workspace or attempt
/// recorded. A second, different pin within one process is refused.
#[cfg(unix)]
fn pin_remote_host(sha: &str) -> Result<()> {
    if sha.len() != 64 || !sha.bytes().all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(&b)) {
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

fn authorize_observation(
    host: &Path,
    config: &Path,
    intent: &Path,
    intent_kind: &OsStr,
    signing: &SigningKey,
    directory: &Path,
) -> Result<Observed> {
    let intent_bin = directory.join("intent.bin");
    let challenge_bin = directory.join("challenge.bin");
    let challenge_json = directory.join("challenge.json");
    let signatures_json = directory.join("observation-signatures.json");
    let signatures_bin = directory.join("observation-signatures.bin");
    let signed = directory.join("signed-observation.bin");
    if intent_kind == OsStr::new("binary") {
        copy_new(intent, &intent_bin)?;
    } else {
        author(host, config, intent_kind, intent, &intent_bin)?;
    }
    host_files(
        host,
        config,
        &[Path::new("challenge"), &intent_bin, &challenge_bin],
    )?;
    let presentation = inspect(host, config, "challenge", &challenge_bin, &challenge_json)?;
    encode_signatures(
        host,
        config,
        signing,
        challenge_headers(&presentation)?,
        &signatures_json,
        &signatures_bin,
    )?;
    host_files(
        host,
        config,
        &[
            Path::new("observe-assemble"),
            &challenge_bin,
            &signatures_bin,
            &signed,
        ],
    )?;
    Ok(Observed { signed })
}

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
    let plan_bin = directory.join("plan.bin");
    let plan_json = directory.join("plan.json");
    let signatures_json = directory.join("transaction-signatures.json");
    let signatures_bin = directory.join("transaction-signatures.bin");
    let call = directory.join("call.bin");
    host_files(
        host,
        &retained_config,
        &[Path::new("prepare"), &observed.signed, &plan_bin],
    )?;
    let presentation = inspect(host, &retained_config, "plan", &plan_bin, &plan_json)?;
    encode_signatures(
        host,
        &retained_config,
        &signing,
        plan_headers(&presentation)?,
        &signatures_json,
        &signatures_bin,
    )?;
    host_files(
        host,
        &retained_config,
        &[Path::new("assemble"), &plan_bin, &signatures_bin, &call],
    )?;
    sync_retained_call(directory, &call)?;
    if prepare_only {
        return Ok(());
    }
    let outcome_bin = directory.join("outcome.bin");
    let outcome_json = directory.join("outcome.json");
    host_files(
        host,
        &retained_config,
        &[Path::new("submit"), &call, &outcome_bin],
    )?;
    let outcome = inspect(
        host,
        &retained_config,
        "outcome",
        &outcome_bin,
        &outcome_json,
    )?;
    print_confirmed_outcome(&outcome)
}

/// A Host refusal as data: `Ok(Err(line))` when the Host refused the request
/// (`refused: REASON: ...`, from the Host's own decoding of its frame),
/// `Err` for a client failure. Clear the decision slot before the request.
pub(crate) fn host_decided<T>(result: Result<T>) -> Result<std::result::Result<T, String>> {
    match result {
        Ok(value) => Ok(Ok(value)),
        Err(error) => match take_host_decision() {
            Some(HostDecision::RefusedFrame {
                decoded: Some(outcome),
                ..
            }) => Ok(Err(refusal_line(&outcome)
                .unwrap_or_else(|| format!("stopped: {}", outcome["type"])))),
            Some(HostDecision::RefusedFrame { command, .. }) => Ok(Err(format!(
                "refused: Host refused {command}; the frame was not decoded"
            ))),
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
            if let HostDecision::RefusedFrame { encoded, .. } = &decision {
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
    let plan_bin = directory.join("plan.bin");
    if let Err(line) = host_decided_keeping(host_files(
        host,
        &retained_config,
        &[Path::new("prepare"), &observed.signed, &plan_bin],
    ), &directory.join("refusal.frame"))? {
        return Ok(Some(line));
    }
    let presentation = inspect(
        host,
        &retained_config,
        "plan",
        &plan_bin,
        &directory.join("plan.json"),
    )?;
    let signatures_bin = directory.join("transaction-signatures.bin");
    encode_signatures(
        host,
        &retained_config,
        &signing,
        plan_headers(&presentation)?,
        &directory.join("transaction-signatures.json"),
        &signatures_bin,
    )?;
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

fn query_presentation_kind(view: &str, presentation: Option<&str>) -> Result<String> {
    if !matches!(
        view,
        "resource" | "policy" | "capability" | "who" | "since" | "at"
    ) {
        return Err("--view must be resource, policy, capability, who, since, or at".to_owned());
    }
    match presentation {
        None => Ok(format!("view-{view}")),
        Some("fn-inbox-resource") if view == "resource" => Ok("fn-inbox-resource".to_owned()),
        _ => Err("--presentation fn-inbox-resource requires --view resource".to_owned()),
    }
}

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
    if inspection_kind == "fn-inbox-resource"
        && presented.get("type").and_then(Value::as_str) != Some("fn-inbox-resource-summary-v1")
    {
        return Err(
            "host returned an unexpected fn inbox summary type; signed view retained".to_owned(),
        );
    }
    Ok(presented)
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
    let bytes =
        fs::read(&path).map_err(|error| format!("cannot read {}: {error}", path.display()))?;
    let value: Value = serde_json::from_slice(&bytes)
        .map_err(|error| format!("invalid {}: {error}", path.display()))?;
    if value.get("format").and_then(Value::as_str) != Some("minidregg-resource-client-attempt-v1") {
        return Err(format!("unsupported attempt manifest {}", path.display()));
    }
    let host = match value.get("host") {
        Some(Value::String(host)) => PathBuf::from(host),
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
    for index in 1..=9999 {
        let binary = directory.join(format!("retry-{index:04}.bin"));
        let json = directory.join(format!("retry-{index:04}.json"));
        if !binary.exists() && !json.exists() {
            return Ok((binary, json));
        }
    }
    Err("attempt has exhausted retry evidence names".to_owned())
}

fn retry_with_upgrade(
    directory: &Path,
    mode: &str,
    direct: bool,
    #[cfg(unix)] upgrade: Option<&drain::HostUpgrade>,
) -> Result<()> {
    if !matches!(mode, "submit" | "lookup") {
        return Err("--mode must be submit or lookup".to_owned());
    }
    let call = directory.join("call.bin");
    if !call.is_file() {
        return Err(format!("attempt has no retained {}", call.display()));
    }
    sync_retained_call(directory, &call)?;
    let (original_host, config, socket) = manifest_paths(directory)?;
    if !direct && SOCKET.get().is_none() {
        if let Some(socket) = socket {
            let _ = SOCKET.set(socket);
        }
    }
    let (outcome_bin, outcome_json) = next_retry(directory)?;
    #[cfg(unix)]
    let host = if let Some(upgrade) = upgrade {
        if direct || original_host != upgrade.old_host {
            return Err("upgraded retry must use the original manifest and pinned socket".into());
        }
        let socket = SOCKET
            .get()
            .ok_or("upgraded retry requires pinned socket")?;
        if socket != &upgrade.socket
            || fs::read(&config).map_err(|e| e.to_string())? != upgrade.config_bytes
            || fs::read(&call).map_err(|e| e.to_string())? != upgrade.call_bytes
        {
            return Err("upgraded retry inputs differ from durable migration evidence".into());
        }
        let evidence = fs::read(&upgrade.evidence_path).map_err(|e| e.to_string())?;
        if hex(&sha2::Sha256::digest(&evidence)) != upgrade.evidence_sha
            || hex(&sha2::Sha256::digest(
                fs::read(&upgrade.new_host).map_err(|e| e.to_string())?,
            )) != upgrade.new_host_sha
        {
            return Err("upgraded retry migration evidence changed".into());
        }
        let transport_path = outcome_json.with_extension("transport.json");
        let transport = json!({
            "type":"minidregg-upgraded-retry-transport-v1",
            "originalAttemptHost":utf8_path(&original_host)?,
            "effectiveHost":utf8_path(&upgrade.new_host)?,
            "effectiveHostSha256":upgrade.new_host_sha,
            "upgradeEvidencePath":utf8_path(&upgrade.evidence_path)?,
            "upgradeEvidenceSha256":upgrade.evidence_sha,
            "callSha256":upgrade.call_sha,
            "mode":mode,
            "socket":utf8_path(socket)?
        });
        if transport_path.exists() {
            let existing: Value =
                serde_json::from_slice(&fs::read(&transport_path).map_err(|e| e.to_string())?)
                    .map_err(|e| e.to_string())?;
            if existing != transport {
                return Err("upgraded retry transport record changed".into());
            }
        } else {
            let mut bytes = serde_json::to_vec_pretty(&transport).map_err(|e| e.to_string())?;
            bytes.push(b'\n');
            create_private(&transport_path, &bytes)?;
            sync_directory_ancestors(directory)?;
        }
        &upgrade.new_host
    } else {
        &original_host
    };
    #[cfg(not(unix))]
    let host = &original_host;
    host_files(host, &config, &[Path::new(mode), &call, &outcome_bin])?;
    let outcome = inspect(host, &config, "outcome", &outcome_bin, &outcome_json)?;
    print_confirmed_outcome(&outcome)
}

fn retry(directory: &Path, mode: &str, direct: bool) -> Result<()> {
    retry_with_upgrade(
        directory,
        mode,
        direct,
        #[cfg(unix)]
        None,
    )
}

fn host_command(host: &Path, config: &Path, command: &OsStr, arguments: &[OsString]) -> Result<()> {
    let word = command.to_str().ok_or("host command must be UTF-8")?;
    if !matches!(
        word,
        "portable-verify-fn"
            | "consumer-verify-poll-files"
            | "portable-consumer-decide"
            | "poll-consumer-decide"
            | "consumer-poll-decide"
            | "consumer-export-inbox"
            | "consumer-export-poll"
            | "consumer-ack-poll"
            | "reply-consumer-poll-decide"
            | "reply-consumer-export-result"
            | "reply-consumer-ack-poll"
            | "consumer-export-reply"
            | "consumer-stage-reply-plan"
            | "consumer-stage-reply-sign"
            | "consumer-decide-test"
    ) {
        return Err(format!("unsupported fn consumer command {word}"));
    }
    if SOCKET.get().is_some() {
        return Err("fn consumer file commands require direct Host/Main CLI until a typed session opcode exists".to_owned());
    }
    let mut all = Vec::with_capacity(arguments.len() + 1);
    all.push(command);
    all.extend(arguments.iter().map(OsString::as_os_str));
    let output = process(host, config, &all)?;
    io::stdout()
        .write_all(&output.stdout)
        .map_err(|e| format!("cannot print host output: {e}"))
}

#[cfg(unix)]
#[derive(Clone, Copy)]
struct ConsumerRoute {
    poll_command: &'static str,
    ack_command: &'static str,
    poll_opcode: u8,
    ack_opcode: u8,
    poll_type: &'static str,
    ack_type: &'static str,
    reply: bool,
}

#[cfg(unix)]
const B_CONSUMER: ConsumerRoute = ConsumerRoute {
    poll_command: "consumer-poll",
    ack_command: "consumer-ack",
    poll_opcode: 12,
    ack_opcode: 13,
    poll_type: "fn-consumer-poll-session-v1",
    ack_type: "fn-consumer-ack-session-v1",
    reply: false,
};

#[cfg(unix)]
const A_REPLY_CONSUMER: ConsumerRoute = ConsumerRoute {
    poll_command: "reply-consumer-poll",
    ack_command: "reply-consumer-ack",
    poll_opcode: 14,
    ack_opcode: 15,
    poll_type: "fn-a-reply-poll-session-v1",
    ack_type: "fn-a-reply-ack-session-v1",
    reply: true,
};

#[cfg(unix)]
fn historical_without_intent(value: &Value, route: ConsumerRoute) -> bool {
    if route.reply {
        matches!(
            value.pointer("/decision/decision").and_then(Value::as_str),
            Some("repeated" | "conflict-recorded")
        )
    } else {
        matches!(
            value
                .pointer("/decision/decision/type")
                .and_then(Value::as_str),
            Some(
                "historical-repeat"
                    | "historical-carrier-variation-evidence"
                    | "historical-conflict-evidence"
            )
        )
    }
}

#[cfg(unix)]
fn canonical_poll_decimal<'a>(value: &'a Value, field: &str) -> Result<&'a str> {
    let text = value
        .get(field)
        .and_then(Value::as_str)
        .ok_or_else(|| format!("fn progress lacks {field}"))?;
    if text.is_empty()
        || text.len() > 80
        || !text.bytes().all(|byte| byte.is_ascii_digit())
        || (text.len() > 1 && text.starts_with('0'))
    {
        return Err(format!("fn progress has noncanonical {field}"));
    }
    Ok(text)
}

#[cfg(unix)]
fn validate_skip_decision(value: &Value, route: ConsumerRoute, intent: &[u8]) -> Result<()> {
    let decision = value
        .get("decision")
        .ok_or("fn skip reply lacks decision")?;
    let kind = decision
        .get("type")
        .and_then(Value::as_str)
        .ok_or("fn skip reply lacks decision type")?;
    let own_r = kind == "fn-a-own-r-progress-decision-v1";
    if kind != "fn-empty-page-progress-decision-v1" && !(route.reply && own_r) {
        return Err("fn skip decision type is unsupported for this consumer".into());
    }
    let fields = decision
        .as_object()
        .ok_or("fn skip decision is not an object")?;
    if fields.len() != if own_r { 5 } else { 4 } {
        return Err("fn skip decision fields differ from source schema".into());
    }
    let from = canonical_poll_decimal(decision, "fromPosition")?
        .parse::<u128>()
        .map_err(|_| "fn progress fromPosition exceeds u128")?;
    let to = canonical_poll_decimal(decision, "toPosition")?
        .parse::<u128>()
        .map_err(|_| "fn progress toPosition exceeds u128")?;
    if to > u32::MAX as u128
        || !(1..=16).contains(
            &to.checked_sub(from)
                .ok_or("fn progress position reversed")?,
        )
    {
        return Err("fn progress exceeds source poll scan bound".into());
    }
    if own_r {
        canonical_poll_decimal(decision, "outboxTransactionId")?;
    }
    match decision.get("decision").and_then(Value::as_str) {
        Some("proposed-fresh") if !intent.is_empty() => Ok(()),
        Some("repeated") if intent.is_empty() => Ok(()),
        _ => Err("fn progress decision and intent disagree".into()),
    }
}

#[cfg(unix)]
fn private_consumer_attempt(
    host: &Path,
    config: &Path,
    directory: &Path,
    operation: &str,
) -> Result<PathBuf> {
    use std::os::unix::fs::DirBuilderExt;
    fs::DirBuilder::new()
        .mode(0o700)
        .create(directory)
        .map_err(|e| {
            format!(
                "cannot create private consumer attempt {}: {e}",
                directory.display()
            )
        })?;
    let retained_config = directory.join("config.json");
    copy_new(config, &retained_config)?;
    write_manifest(directory, host, &retained_config, operation)?;
    Ok(retained_config)
}

#[cfg(unix)]
fn consumer_poll(host: &Path, config: &Path, directory: &Path, route: ConsumerRoute) -> Result<()> {
    let socket = SOCKET.get().ok_or("consumer poll requires --socket")?;
    let retained_config = private_consumer_attempt(host, config, directory, route.poll_command)?;
    let frame = session_invoke(host, socket, &retained_config, route.poll_opcode, &[])?;
    write_new(&directory.join("reply.frame"), &frame)?;
    if frame[0] == 255 {
        return Err(format!(
            "host refused {}; complete encoded reply retained in {}",
            route.poll_command,
            directory.join("reply.frame").display()
        ));
    }
    let value: Value = serde_json::from_slice(&frame[1..])
        .map_err(|e| format!("invalid fn consumer host JSON; complete reply retained: {e}"))?;
    write_new(&directory.join("decision.json"), &frame[1..])?;
    if value.get("type").and_then(Value::as_str) != Some(route.poll_type) {
        return Err("unexpected fn consumer host reply type; complete reply retained".to_owned());
    }
    let status = value
        .get("status")
        .and_then(Value::as_str)
        .ok_or("fn consumer reply lacks status; complete reply retained")?;
    let intent_hex = value
        .get("intentHex")
        .and_then(Value::as_str)
        .ok_or("fn consumer reply lacks intentHex; complete reply retained")?;
    let intent = decode_hex(intent_hex)?;
    if hex(&intent) != intent_hex {
        return Err(
            "fn consumer intentHex is not canonical lowercase; complete reply retained".to_owned(),
        );
    }
    match status {
        "accepted-decision" => {
            if intent.is_empty() {
                if !historical_without_intent(&value, route) {
                    return Err("fn consumer accepted without an intent or historical decision; complete reply retained".to_owned());
                }
            } else {
                write_new(&directory.join("intent.bin"), &intent)?;
            }
            print_json(&value)
        }
        "idle"
            if intent.is_empty()
                && value.pointer("/decision/type").and_then(Value::as_str)
                    == Some("fn-empty-page-idle-v1") =>
        {
            print_json(&value)
        }
        "skip-decision" => {
            validate_skip_decision(&value, route, &intent)?;
            if !intent.is_empty() {
                write_new(&directory.join("intent.bin"), &intent)?;
            }
            print_json(&value)
        }
        "refused" if intent.is_empty() => {
            print_json(&value)?;
            Err("fn consumer refused; complete decision retained".to_owned())
        }
        _ => Err("inconsistent fn consumer status and intent; complete reply retained".to_owned()),
    }
}

#[cfg(unix)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum AckResult {
    Exact,
    Covered,
}

#[cfg(unix)]
fn parse_ack_result(value: &Value, route: ConsumerRoute, transaction: &str) -> Result<AckResult> {
    if value.get("type").and_then(Value::as_str) != Some(route.ack_type)
        || value.get("miniTransactionId").and_then(Value::as_str) != Some(transaction)
    {
        return Err("fn ack reply identity mismatch; complete reply retained".into());
    }
    let own_r = value.get("kind").and_then(Value::as_str) == Some("own-r-skip");
    if own_r {
        if !route.reply || value.as_object().is_none_or(|fields| fields.len() != 9) {
            return Err("own-R ACK reply has wrong consumer or fields".into());
        }
        canonical_poll_decimal(value, "outboxTransactionId")?;
        let sequence = canonical_poll_decimal(value, "fnStoreSequence")?
            .parse::<u32>()
            .map_err(|_| "own-R Store sequence exceeds u32")?;
        canonical_poll_decimal(value, "fnStoreTransactionId")?
            .parse::<u32>()
            .map_err(|_| "own-R Store transaction exceeds u32")?;
        let cursor = canonical_poll_decimal(value, "fnCursorPosition")?
            .parse::<u32>()
            .map_err(|_| "own-R ACK cursor exceeds u32")?;
        if sequence.checked_add(1) != Some(cursor) {
            return Err("own-R ACK cursor differs from Store sequence".into());
        }
        let committed = canonical_poll_decimal(value, "fnCommittedAck")?
            .parse::<u32>()
            .map_err(|_| "own-R committed ACK exceeds u32")?;
        if matches!(
            value.get("fnAck").and_then(Value::as_str),
            Some("durable-accepted" | "covered-by-durable-frontier")
        ) && committed < cursor
        {
            return Err("own-R ACK committed frontier precedes retained cursor".into());
        }
    }
    match value.get("fnAck").and_then(Value::as_str) {
        Some("durable-accepted") => Ok(AckResult::Exact),
        Some("covered-by-durable-frontier") => {
            let cursor = value
                .get("fnCursorPosition")
                .and_then(Value::as_str)
                .ok_or("fn coverage lacks retained cursor position")?;
            let committed = value
                .get("fnCommittedAck")
                .and_then(Value::as_str)
                .ok_or("fn coverage lacks committed ACK frontier")?;
            let decimal = |s: &str| -> Result<u128> {
                if s.is_empty()
                    || !s.bytes().all(|b| b.is_ascii_digit())
                    || (s.len() > 1 && s.starts_with('0'))
                {
                    return Err("fn coverage position is not canonical decimal".into());
                }
                s.parse::<u128>()
                    .map_err(|_| "fn coverage position exceeds u128".into())
            };
            if decimal(cursor)? > decimal(committed)? {
                return Err("fn coverage cursor exceeds committed ACK frontier".into());
            }
            let kind = value.get("kind").and_then(Value::as_str);
            if !(matches!(kind, Some("empty-page-skip" | "article-prefix-coverage"))
                || (route.reply && kind == Some("own-r-skip")))
            {
                return Err("fn coverage lacks supported kind".into());
            }
            Ok(AckResult::Covered)
        }
        Some("refused" | "uncertain" | "transport-fault") => {
            Err("fn ack incomplete; complete reply retained for reconciliation".into())
        }
        _ => Err("fn ack reply lacks valid status; complete reply retained".into()),
    }
}

#[cfg(unix)]
fn consumer_ack(
    host: &Path,
    config: &Path,
    transaction: &str,
    directory: &Path,
    route: ConsumerRoute,
) -> Result<()> {
    let socket = SOCKET.get().ok_or("consumer ack requires --socket")?;
    let bytes = transaction.as_bytes();
    if bytes.is_empty()
        || bytes.len() > 80
        || bytes.iter().any(|b| !b.is_ascii_digit())
        || (bytes.len() > 1 && bytes[0] == b'0')
    {
        return Err("--mini-transaction must be canonical decimal (1–80 bytes)".to_owned());
    }
    let retained_config = private_consumer_attempt(host, config, directory, route.ack_command)?;
    write_new(&directory.join("transaction-id.txt"), bytes)?;
    let frame = session_invoke(host, socket, &retained_config, route.ack_opcode, bytes)?;
    write_new(&directory.join("reply.frame"), &frame)?;
    if frame[0] == 255 {
        return Err(format!(
            "host refused {}; complete encoded reply retained in {}",
            route.ack_command,
            directory.join("reply.frame").display()
        ));
    }
    let value: Value = serde_json::from_slice(&frame[1..])
        .map_err(|e| format!("invalid fn ack host JSON; complete reply retained: {e}"))?;
    write_new(&directory.join("ack.json"), &frame[1..])?;
    print_json(&value)?;
    let status = parse_ack_result(&value, route, transaction)?;
    match status {
        AckResult::Exact => Ok(()),
        AckResult::Covered => Err("fn cursor is covered by a durable frontier; exact old ACK event is not proven; complete reply retained".into()),
    }
}

#[cfg(unix)]
fn origin_outbox_intent(value: &Value) -> Result<Option<Vec<u8>>> {
    if value.get("type").and_then(Value::as_str) != Some("fn-a-origin-outbox-session-v1") {
        return Err("unexpected origin outbox reply type; complete frame retained".into());
    }
    if value
        .get("messageId")
        .and_then(Value::as_str)
        .is_none_or(str::is_empty)
        || value.get("miniOrigin").is_none_or(|v| !v.is_object())
    {
        return Err("origin outbox reply lacks message identity or Mini origin".into());
    }
    let source = value
        .get("sourceIdentity")
        .and_then(Value::as_str)
        .ok_or("origin outbox reply lacks source identity")?;
    let source_bytes = decode_hex(source)?;
    if source_bytes.is_empty() || hex(&source_bytes) != source {
        return Err("origin outbox source identity is not canonical lowercase hex".into());
    }
    let intent_hex = value
        .get("intentHex")
        .and_then(Value::as_str)
        .ok_or("origin outbox reply lacks intentHex")?;
    let intent = decode_hex(intent_hex)?;
    if hex(&intent) != intent_hex {
        return Err("origin outbox intentHex is not canonical lowercase".into());
    }
    match (
        value.get("status").and_then(Value::as_str),
        value.get("decision").and_then(Value::as_str),
        intent.is_empty(),
    ) {
        (Some("prepared-decision"), Some("proposed-fresh"), false) => Ok(Some(intent)),
        (Some("prepared-decision"), Some("repeated"), true) => Ok(None),
        (Some("refused"), Some("refused"), true) => {
            Err("origin outbox preparation refused; complete decision retained".into())
        }
        _ => Err("inconsistent origin outbox decision and intent; complete reply retained".into()),
    }
}

#[cfg(unix)]
fn origin_outbox_prepare(
    host: &Path,
    config: &Path,
    carrier: &Path,
    directory: &Path,
) -> Result<()> {
    const MAX_CARRIER: usize = 1_516_384;
    let socket = SOCKET
        .get()
        .ok_or("origin-outbox-prepare requires --socket")?;
    let mut bytes = Vec::new();
    File::open(carrier)
        .map_err(|e| format!("cannot open R carrier {}: {e}", carrier.display()))?
        .take((MAX_CARRIER + 1) as u64)
        .read_to_end(&mut bytes)
        .map_err(|e| format!("cannot read R carrier {}: {e}", carrier.display()))?;
    if bytes.is_empty() || bytes.len() > MAX_CARRIER {
        return Err("R carrier must be 1..1516384 bytes".into());
    }
    let retained_config =
        private_consumer_attempt(host, config, directory, "origin-outbox-prepare")?;
    create_private(&directory.join("carrier.bin"), &bytes)?;
    sync_directory_ancestors(directory)?;
    let frame = session_invoke(host, socket, &retained_config, 16, &bytes)?;
    write_new(&directory.join("reply.frame"), &frame)?;
    if frame[0] == 255 {
        return Err("Host refused origin outbox preparation; complete frame retained".into());
    }
    let value: Value = serde_json::from_slice(&frame[1..])
        .map_err(|e| format!("invalid origin outbox JSON; complete frame retained: {e}"))?;
    write_new(&directory.join("decision.json"), &frame[1..])?;
    let selected = origin_outbox_intent(&value);
    print_json(&value)?;
    match selected {
        Ok(Some(intent)) => {
            write_new(&directory.join("intent.bin"), &intent)?;
            Ok(())
        }
        Ok(None) => Ok(()),
        Err(error) => Err(error),
    }
}

#[cfg(unix)]
fn origin_outbox_export(
    host: &Path,
    config: &Path,
    transaction: &str,
    directory: &Path,
) -> Result<()> {
    let socket = SOCKET
        .get()
        .ok_or("origin-outbox-export requires --socket")?;
    if transaction.is_empty()
        || transaction.len() > 80
        || !transaction.bytes().all(|byte| byte.is_ascii_digit())
        || (transaction.len() > 1 && transaction.starts_with('0'))
    {
        return Err("--mini-transaction must be canonical decimal (1–80 bytes)".into());
    }
    let retained_config =
        private_consumer_attempt(host, config, directory, "origin-outbox-export")?;
    create_private(
        &directory.join("transaction-id.txt"),
        transaction.as_bytes(),
    )?;
    sync_directory_ancestors(directory)?;
    let frame = session_invoke(host, socket, &retained_config, 18, transaction.as_bytes())?;
    write_new(&directory.join("reply.frame"), &frame)?;
    if frame[0] == 255 {
        return Err("Host refused origin outbox export; complete frame retained".into());
    }
    let value: Value = serde_json::from_slice(&frame[1..])
        .map_err(|e| format!("invalid origin outbox export JSON; complete frame retained: {e}"))?;
    write_new(&directory.join("export.json"), &frame[1..])?;
    if value.get("type").and_then(Value::as_str) != Some("fn-a-origin-outbox-export-v1") {
        return Err("unexpected origin outbox export type; complete reply retained".into());
    }
    if value.get("status").and_then(Value::as_str) == Some("refused") {
        print_json(&value)?;
        return Err("origin outbox export refused; complete typed reply retained".into());
    }
    if value.get("status").and_then(Value::as_str) != Some("accepted")
        || value.get("transactionId").and_then(Value::as_str) != Some(transaction)
        || value
            .get("messageId")
            .and_then(Value::as_str)
            .is_none_or(str::is_empty)
    {
        return Err("origin outbox export identity mismatch; complete reply retained".into());
    }
    for name in ["packageIdentity", "originCallIdentity"] {
        let Some(text) = value.get(name).and_then(Value::as_str) else {
            return Err(format!("origin outbox export lacks {name}"));
        };
        if text.is_empty()
            || text.len() > 80
            || !text.bytes().all(|byte| byte.is_ascii_digit())
            || (text.len() > 1 && text.starts_with('0'))
        {
            return Err(format!("origin outbox export has noncanonical {name}"));
        }
    }
    let source_hex = value
        .get("sourceIdentity")
        .and_then(Value::as_str)
        .ok_or("origin outbox export lacks source identity")?;
    let source = decode_hex(source_hex)?;
    if source.is_empty() || hex(&source) != source_hex {
        return Err("origin outbox source identity is not canonical lowercase hex".into());
    }
    for name in ["miniOrigin", "miniOutbox"] {
        if value
            .get(name)
            .and_then(|receipt| receipt.get("type"))
            .and_then(Value::as_str)
            != Some("verified-mini-native-prefix-v1")
        {
            return Err(format!("origin outbox export lacks typed {name} receipt"));
        }
    }
    let carrier_hex = value
        .get("carrierHex")
        .and_then(Value::as_str)
        .ok_or("origin outbox export lacks carrierHex")?;
    if carrier_hex.is_empty() || carrier_hex.len() > 2 * 1_516_384 {
        return Err("origin outbox export carrier exceeds selected profile".into());
    }
    let carrier = decode_hex(carrier_hex)?;
    if carrier.is_empty() || hex(&carrier) != carrier_hex {
        return Err("origin outbox carrier is not canonical lowercase hex".into());
    }
    write_new(&directory.join("carrier.bin"), &carrier)?;
    print_json(&value)
}

#[cfg(unix)]
fn continuity_reply(value: &Value) -> Result<bool> {
    if value.get("type").and_then(Value::as_str) != Some("minidregg-provider-continuity-v1") {
        return Err("unexpected provider continuity reply type; complete frame retained".into());
    }
    let canonical = |text: &str| -> bool {
        !text.is_empty()
            && text.len() <= 80
            && text.bytes().all(|byte| byte.is_ascii_digit())
            && (text.len() == 1 || !text.starts_with('0'))
    };
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
    let mut call_bytes = Vec::new();
    File::open(call)
        .map_err(|e| format!("cannot open original reserve call: {e}"))?
        .take((transport::HOST_MAX_FRAME + 1) as u64)
        .read_to_end(&mut call_bytes)
        .map_err(|e| format!("cannot read original reserve call: {e}"))?;
    let mut outcome_bytes = Vec::new();
    File::open(outcome)
        .map_err(|e| format!("cannot open original reserve outcome: {e}"))?
        .take(1025)
        .read_to_end(&mut outcome_bytes)
        .map_err(|e| format!("cannot read original reserve outcome: {e}"))?;
    if call_bytes.is_empty()
        || outcome_bytes.is_empty()
        || outcome_bytes.len() > 1024
        || call_bytes.len() + outcome_bytes.len() + 5 > transport::HOST_MAX_FRAME
    {
        return Err(
            "original reserve call/outcome exceeds provider continuity frame bounds".into(),
        );
    }
    let retained_config = private_consumer_attempt(host, config, directory, "continuity")?;
    create_private(&directory.join("call.bin"), &call_bytes)?;
    create_private(&directory.join("outcome.bin"), &outcome_bytes)?;
    sync_directory_ancestors(directory)?;
    let mut payload = Vec::with_capacity(4 + call_bytes.len() + outcome_bytes.len());
    payload.extend_from_slice(&(call_bytes.len() as u32).to_le_bytes());
    payload.extend_from_slice(&call_bytes);
    payload.extend_from_slice(&outcome_bytes);
    let frame = session_invoke(host, socket, &retained_config, 17, &payload)?;
    write_new(&directory.join("reply.frame"), &frame)?;
    if frame[0] == 255 {
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

fn run(mut args: Args) -> Result<()> {
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
        "join" => participant_enrollment::join(args),
        #[cfg(unix)]
        "socket-proxy" => {
            args.finish()?;
            let socket = SOCKET.get().ok_or("socket-proxy requires --socket")?;
            proxy::serve(socket)
        }
        #[cfg(unix)]
        "workspace" => workspace::run(args),
        #[cfg(unix)]
        "enroll" => participant_enrollment::run(args),
        "clock" => clock::run(args),
        #[cfg(unix)]
        "shell" => shell::run(args),
        #[cfg(unix)]
        "key" => keys::run(args),
        #[cfg(unix)]
        "rotate-key" => key_rotation::rotate_key(args),
        #[cfg(unix)]
        "key-status" => key_rotation::key_status(args),
        "fleet" => fleet::run(args),
        #[cfg(unix)]
        "credit" => credit::run(args),
        "well" => well::run(args),
        "pay" => pay::run(args),
        #[cfg(unix)]
        "selected-exchange" => {
            let phase = args.required("phase")?;
            let phase = phase
                .to_str()
                .ok_or("selected-exchange phase must be UTF-8")?;
            let contract = path(args.required("contract")?);
            let state = path(args.required("state-dir")?);
            let approval = args.optional("approval").map(path);
            args.finish()?;
            selected_exchange::run(phase, &contract, &state, approval.as_deref())
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
        "serve-operator" => {
            let host = path(args.required("host")?);
            let config = path(args.required("config")?);
            args.finish()?;
            let socket = SOCKET.get().ok_or("serve-operator requires --socket")?;
            transport::serve_operator(socket, &host, &config)
        }
        "host-command" => {
            let host = path(args.required("host")?);
            let config = path(args.required("config")?);
            let command = args.required("command")?;
            let arguments = args.repeated("arg");
            args.finish()?;
            host_command(&host, &config, &command, &arguments)
        }
        "consumer-poll" | "reply-consumer-poll" => {
            let reply = args.command == OsStr::new("reply-consumer-poll");
            let host = path(args.required("host")?);
            let config = path(args.required("config")?);
            let directory = path(args.required("dir")?);
            args.finish()?;
            #[cfg(unix)]
            {
                consumer_poll(
                    &host,
                    &config,
                    &directory,
                    if reply { A_REPLY_CONSUMER } else { B_CONSUMER },
                )
            }
            #[cfg(not(unix))]
            {
                Err("persistent host sessions require Unix sockets".to_owned())
            }
        }
        "consumer-ack" | "reply-consumer-ack" => {
            let reply = args.command == OsStr::new("reply-consumer-ack");
            let host = path(args.required("host")?);
            let config = path(args.required("config")?);
            let transaction = args.required("mini-transaction")?;
            let directory = path(args.required("dir")?);
            args.finish()?;
            let transaction = transaction
                .to_str()
                .ok_or("--mini-transaction must be UTF-8")?;
            #[cfg(unix)]
            {
                consumer_ack(
                    &host,
                    &config,
                    transaction,
                    &directory,
                    if reply { A_REPLY_CONSUMER } else { B_CONSUMER },
                )
            }
            #[cfg(not(unix))]
            {
                Err("persistent host sessions require Unix sockets".to_owned())
            }
        }
        "origin-outbox-prepare" => {
            let host = path(args.required("host")?);
            let config = path(args.required("config")?);
            let carrier = path(args.required("carrier")?);
            let directory = path(args.required("dir")?);
            args.finish()?;
            #[cfg(unix)]
            {
                origin_outbox_prepare(&host, &config, &carrier, &directory)
            }
            #[cfg(not(unix))]
            {
                Err("origin-outbox-prepare requires Unix sockets".to_owned())
            }
        }
        "origin-outbox-export" => {
            let host = path(args.required("host")?);
            let config = path(args.required("config")?);
            let transaction = args.required("mini-transaction")?;
            let directory = path(args.required("dir")?);
            args.finish()?;
            let transaction = transaction
                .to_str()
                .ok_or("--mini-transaction must be UTF-8")?;
            #[cfg(unix)]
            {
                origin_outbox_export(&host, &config, transaction, &directory)
            }
            #[cfg(not(unix))]
            {
                Err("origin-outbox-export requires Unix sockets".to_owned())
            }
        }
        "origin-publish" => {
            let host = path(args.required("host")?);
            let config = path(args.required("config")?);
            let key = path(args.required("key")?);
            let carrier = path(args.required("carrier")?);
            let state_dir = path(args.required("state-dir")?);
            let post_config = path(args.required("post-config")?);
            args.finish()?;
            #[cfg(unix)]
            {
                let socket = SOCKET.get().ok_or("origin-publish requires --socket")?;
                publisher::publish(
                    &host,
                    &config,
                    socket,
                    &key,
                    &carrier,
                    &state_dir,
                    &post_config,
                )
            }
            #[cfg(not(unix))]
            {
                Err("origin-publish requires Unix sockets".to_owned())
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
        "consumer-drain-once" | "reply-consumer-drain-once" => {
            let reply = args.command == OsStr::new("reply-consumer-drain-once");
            let host = path(args.required("host")?);
            let config = path(args.required("config")?);
            let key = path(args.required("key")?);
            let state_dir = path(args.required("state-dir")?);
            let max_pages = args
                .optional("max-pages")
                .unwrap_or_else(|| OsString::from("16"));
            args.finish()?;
            let max_pages = max_pages
                .to_str()
                .ok_or("--max-pages must be UTF-8")?
                .parse::<u32>()
                .map_err(|_| "--max-pages must be an integer from 1 to 16".to_owned())?;
            if !(1..=16).contains(&max_pages) {
                return Err("--max-pages must be an integer from 1 to 16".to_owned());
            }
            #[cfg(unix)]
            {
                let socket = SOCKET
                    .get()
                    .ok_or("consumer-drain-once requires --socket")?;
                if reply {
                    drain::run_reply(&host, &config, socket, &key, &state_dir, max_pages)
                } else {
                    drain::run(&host, &config, socket, &key, &state_dir, max_pages)
                }
            }
            #[cfg(not(unix))]
            {
                Err("consumer-drain-once requires Unix sockets".to_owned())
            }
        }
        "consumer-resume-ack" | "reply-consumer-resume-ack" => {
            let reply = args.command == OsStr::new("reply-consumer-resume-ack");
            let host = path(args.required("host")?);
            let config = path(args.required("config")?);
            let key = path(args.required("key")?);
            let state_dir = path(args.required("state-dir")?);
            args.finish()?;
            #[cfg(unix)]
            {
                let socket = SOCKET
                    .get()
                    .ok_or("consumer-resume-ack requires --socket")?;
                if reply {
                    drain::resume_held_reply_ack(&host, &config, socket, &key, &state_dir)
                } else {
                    drain::resume_held_ack(&host, &config, socket, &key, &state_dir)
                }
            }
            #[cfg(not(unix))]
            {
                Err("consumer-resume-ack requires Unix sockets".to_owned())
            }
        }
        "consumer-host-upgrade" => {
            let old_host = path(args.required("old-host")?);
            let old_sha = args.required("old-sha256")?;
            let new_host = path(args.required("new-host")?);
            let new_sha = args.required("new-sha256")?;
            let config = path(args.required("config")?);
            let key = path(args.required("key")?);
            let state_dir = path(args.required("state-dir")?);
            let known_outcome = path(args.required("known-outcome")?);
            let known_sha = args.required("known-sha256")?;
            args.finish()?;
            #[cfg(unix)]
            {
                let socket = SOCKET
                    .get()
                    .ok_or("consumer-host-upgrade requires --socket")?;
                drain::upgrade_host(drain::UpgradeRequest {
                    old_host: &old_host,
                    new_host: &new_host,
                    config: &config,
                    socket,
                    key: &key,
                    state_dir: &state_dir,
                    known_outcome: &known_outcome,
                    old_sha: old_sha.to_str().ok_or("old SHA must be UTF-8")?,
                    new_sha: new_sha.to_str().ok_or("new SHA must be UTF-8")?,
                    known_sha: known_sha.to_str().ok_or("known SHA must be UTF-8")?,
                })
            }
            #[cfg(not(unix))]
            {
                Err("consumer-host-upgrade requires Unix sockets".to_owned())
            }
        }
        "consumer-worker" | "reply-consumer-worker" => {
            let reply = args.command == OsStr::new("reply-consumer-worker");
            let host = path(args.required("host")?);
            let config = path(args.required("config")?);
            let key = path(args.required("key")?);
            let state_dir = path(args.required("state-dir")?);
            let worker_config = path(args.required("worker-config")?);
            args.finish()?;
            #[cfg(unix)]
            {
                let socket = SOCKET.get().ok_or("consumer-worker requires --socket")?;
                if reply {
                    worker::run_reply(&host, &config, socket, &key, &state_dir, &worker_config)
                } else {
                    worker::run(&host, &config, socket, &key, &state_dir, &worker_config)
                }
            }
            #[cfg(not(unix))]
            {
                Err("consumer-worker requires Unix sockets".to_owned())
            }
        }
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
        // The X25519 public key a private room's inviter wraps the room key to,
        // derived from the same seed the signing key file holds.
        "enc-public" => {
            if socket_argument.is_some() {
                return Err("enc-public does not use a host socket".to_owned());
            }
            let secret = path(args.required("secret")?);
            args.finish()?;
            println!("{}", workspace::roomkey::enc_public_hex(&secret)?);
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
                workspace::private::derive_enc_key(&*workspace::roomkey::seed_of(&sponsor)?);
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
        #[cfg(unix)]
        "fn-namespace-plan" => {
            let host = path(args.required("host")?);
            let config = path(args.required("config")?);
            let directory = path(args.required("state-dir")?);
            args.finish()?;
            let socket = SOCKET.get().ok_or("fn-namespace-plan requires --socket")?;
            fn_namespace::plan(&host, &config, socket, &directory)
        }
        #[cfg(unix)]
        "fn-namespace-register" => {
            let directory = path(args.required("state-dir")?);
            let key = path(args.required("key")?);
            let approval = path(args.required("approval")?);
            args.finish()?;
            if SOCKET.get().is_some() {
                return Err("fn-namespace-register uses its retained operator socket".into());
            }
            fn_namespace::register(&directory, &key, &approval)
        }
        #[cfg(unix)]
        "fn-namespace-lookup" => {
            let directory = path(args.required("state-dir")?);
            args.finish()?;
            if SOCKET.get().is_some() {
                return Err("fn-namespace-lookup uses its retained operator socket".into());
            }
            fn_namespace::lookup_original(&directory)
        }
        #[cfg(unix)]
        "fn-frontier-plan" => {
            let host = path(args.required("host")?);
            let config = path(args.required("config")?);
            let kind = args.required("kind")?;
            let transaction = args.required("transaction")?;
            let directory = path(args.required("state-dir")?);
            args.finish()?;
            let socket = SOCKET.get().ok_or("fn-frontier-plan requires --socket")?;
            fn_frontier::plan(
                &host,
                &config,
                socket,
                kind.to_str().ok_or("fn frontier kind must be UTF-8")?,
                transaction
                    .to_str()
                    .ok_or("fn frontier transaction must be UTF-8")?,
                &directory,
            )
        }
        #[cfg(unix)]
        "fn-frontier-advance" => {
            let directory = path(args.required("state-dir")?);
            let key = path(args.required("key")?);
            let approval = path(args.required("approval")?);
            args.finish()?;
            if SOCKET.get().is_some() {
                return Err("fn-frontier-advance uses its retained operator socket".into());
            }
            fn_frontier::advance(&directory, &key, &approval)
        }
        #[cfg(unix)]
        "fn-frontier-lookup" => {
            let directory = path(args.required("state-dir")?);
            args.finish()?;
            if SOCKET.get().is_some() {
                return Err("fn-frontier-lookup uses its retained operator socket".into());
            }
            fn_frontier::lookup_original(&directory)
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
            let key = path(args.required("key")?);
            let directory = path(args.required("dir")?);
            args.finish()?;
            submit(
                &host,
                &config,
                &intent,
                &intent_kind,
                &key,
                &directory,
                prepare_only,
            )
        }
        "query" => {
            let host = path(args.required("host")?);
            let config = path(args.required("config")?);
            let intent = path(args.required("intent")?);
            let intent_kind = args
                .optional("intent-kind")
                .unwrap_or_else(|| OsString::from("intent"));
            let key = path(args.required("key")?);
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
        #[cfg(unix)]
        "selected-release-retry" => {
            let directory = path(args.required("attempt")?);
            args.finish()?;
            selected_release::retry_submit(&directory, SOCKET.get().map(PathBuf::as_path))
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
    #[cfg(unix)]
    let parsed = match env::args_os().nth(1) {
        Some(command) if command == OsStr::new("fleet-sign") => {
            fleet_sign::run(env::args_os().skip(2).collect())
        }
        _ => Args::parse().and_then(run),
    };
    #[cfg(not(unix))]
    let parsed = Args::parse().and_then(run);
    match parsed {
        Ok(()) => ExitCode::from(EXIT_STATUS.load(Ordering::Relaxed)),
        Err(error) if error == USAGE => {
            print!("{error}");
            ExitCode::SUCCESS
        }
        Err(error) => match take_host_decision().as_ref().and_then(host_refusal_ending) {
            Some(line) => {
                eprintln!("{line}\n  client: {error}");
                ExitCode::from(EXIT_REFUSED)
            }
            None => {
                eprintln!("mini: {error}");
                ExitCode::from(EXIT_STATUS.load(Ordering::Relaxed).max(1))
            }
        },
    }
}

#[cfg(test)]
mod tests {
    use super::*;
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
    fn historical_fn_decisions_need_no_new_mini_intent() {
        assert!(historical_without_intent(
            &json!({"decision": {"decision": {"type": "historical-repeat"}}}),
            B_CONSUMER,
        ));
        assert!(historical_without_intent(
            &json!({"decision": {"decision": {"type": "historical-carrier-variation-evidence"}}}),
            B_CONSUMER,
        ));
        assert!(historical_without_intent(
            &json!({"decision": {"decision": "repeated"}}),
            A_REPLY_CONSUMER,
        ));
        assert!(!historical_without_intent(
            &json!({"decision": {"decision": {"type": "proposed-fresh"}}}),
            B_CONSUMER,
        ));
        assert!(!historical_without_intent(
            &json!({"decision": {"decision": "proposed-fresh"}}),
            A_REPLY_CONSUMER,
        ));
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

    #[cfg(unix)]
    #[test]
    fn origin_outbox_requires_exact_status_intent_pair() {
        let mut value = json!({"type":"fn-a-origin-outbox-session-v1",
            "status":"prepared-decision", "decision":"proposed-fresh",
            "messageId":"<r@example.invalid>", "sourceIdentity":"ab",
            "miniOrigin":{"type":"verified-mini-native-prefix-v1"}, "intentHex":"00"});
        assert_eq!(origin_outbox_intent(&value).unwrap(), Some(vec![0]));
        value["decision"] = json!("repeated");
        assert!(origin_outbox_intent(&value).is_err());
        value["intentHex"] = json!("");
        assert_eq!(origin_outbox_intent(&value).unwrap(), None);
        value["status"] = json!("refused");
        value["decision"] = json!("refused");
        assert!(origin_outbox_intent(&value)
            .unwrap_err()
            .contains("refused"));
        value["sourceIdentity"] = json!("AB");
        assert!(origin_outbox_intent(&value).is_err());
    }

    #[cfg(unix)]
    #[test]
    fn ack_coverage_is_distinct_from_exact_durable_ack() {
        let mut value = json!({"type":"fn-consumer-ack-session-v1",
            "miniTransactionId":"123", "kind":"empty-page-skip",
            "fnAck":"covered-by-durable-frontier",
            "fnCursorPosition":"16", "fnCommittedAck":"23",
            "fnStoreSequence":"", "fnStoreTransactionId":""});
        assert_eq!(
            parse_ack_result(&value, B_CONSUMER, "123").unwrap(),
            AckResult::Covered
        );
        value["fnCursorPosition"] = json!("24");
        assert!(parse_ack_result(&value, B_CONSUMER, "123").is_err());
        value["fnCursorPosition"] = json!("16");
        value["fnAck"] = json!("durable-accepted");
        assert_eq!(
            parse_ack_result(&value, B_CONSUMER, "123").unwrap(),
            AckResult::Exact
        );
        assert!(parse_ack_result(&value, B_CONSUMER, "124").is_err());
    }

    #[cfg(unix)]
    #[test]
    fn a_own_r_progress_is_bounded_and_never_accepted_as_b_skip() {
        let mut value = json!({"type":"fn-a-reply-poll-session-v1",
            "status":"skip-decision", "intentHex":"00",
            "decision":{"type":"fn-a-own-r-progress-decision-v1",
                "decision":"proposed-fresh", "fromPosition":"16",
                "toPosition":"17", "outboxTransactionId":"42"}});
        assert!(validate_skip_decision(&value, A_REPLY_CONSUMER, &[0]).is_ok());
        assert!(validate_skip_decision(&value, B_CONSUMER, &[0]).is_err());
        value["decision"]["toPosition"] = json!("33");
        assert!(validate_skip_decision(&value, A_REPLY_CONSUMER, &[0]).is_err());
        value["decision"]["toPosition"] = json!("17");
        value["decision"]["outboxTransactionId"] = json!("042");
        assert!(validate_skip_decision(&value, A_REPLY_CONSUMER, &[0]).is_err());
        value["decision"]["outboxTransactionId"] = json!("42");
        assert!(validate_skip_decision(&value, A_REPLY_CONSUMER, &[]).is_err());
        value["decision"]["outboxTransactionId"] = json!("0");
        assert!(validate_skip_decision(&value, A_REPLY_CONSUMER, &[0]).is_ok());
        value["decision"]["toPosition"] = json!("4294967296");
        value["decision"]["fromPosition"] = json!("4294967295");
        assert!(validate_skip_decision(&value, A_REPLY_CONSUMER, &[0]).is_err());
        value["decision"]["toPosition"] = json!("17");
        value["decision"]["fromPosition"] = json!("16");
        value["decision"]["decision"] = json!("repeated");
        assert!(validate_skip_decision(&value, A_REPLY_CONSUMER, &[]).is_ok());
        value["decision"]["decision"] = json!("refused");
        assert!(validate_skip_decision(&value, A_REPLY_CONSUMER, &[]).is_err());
    }

    #[cfg(unix)]
    #[test]
    fn a_own_r_ack_requires_selected_transaction_and_durable_cursor() {
        let mut value = json!({"type":"fn-a-reply-ack-session-v1",
            "kind":"own-r-skip", "miniTransactionId":"123", "outboxTransactionId":"42",
            "fnCursorPosition":"17", "fnCommittedAck":"17", "fnStoreSequence":"16",
            "fnStoreTransactionId":"16", "fnAck":"durable-accepted"});
        assert_eq!(
            parse_ack_result(&value, A_REPLY_CONSUMER, "123").unwrap(),
            AckResult::Exact
        );
        value["fnStoreSequence"] = json!("0");
        value["fnStoreTransactionId"] = json!("0");
        value["fnCursorPosition"] = json!("1");
        value["fnCommittedAck"] = json!("1");
        assert_eq!(
            parse_ack_result(&value, A_REPLY_CONSUMER, "123").unwrap(),
            AckResult::Exact
        );
        value["fnCursorPosition"] = json!("17");
        value["fnStoreSequence"] = json!("16");
        value["fnCommittedAck"] = json!("17");
        assert!(parse_ack_result(&value, A_REPLY_CONSUMER, "124").is_err());
        assert!(parse_ack_result(&value, B_CONSUMER, "123").is_err());
        value["fnCommittedAck"] = json!("16");
        assert!(parse_ack_result(&value, A_REPLY_CONSUMER, "123").is_err());
        value["fnCommittedAck"] = json!("18");
        value["fnAck"] = json!("covered-by-durable-frontier");
        assert_eq!(
            parse_ack_result(&value, A_REPLY_CONSUMER, "123").unwrap(),
            AckResult::Covered
        );
        value["outboxTransactionId"] = json!("042");
        assert!(parse_ack_result(&value, A_REPLY_CONSUMER, "123").is_err());
        value["outboxTransactionId"] = json!("42");
        value["fnStoreSequence"] = json!("15");
        assert!(parse_ack_result(&value, A_REPLY_CONSUMER, "123").is_err());
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
        let challenge = json!({"headers": ["00ff10", "6d696e69"]});
        let headers = challenge_headers(&challenge).unwrap();
        assert_eq!(headers, [vec![0, 255, 16], b"mini".to_vec()]);

        let signing = SigningKey::from_bytes(&[27; 32]);
        let rendered = sign_headers(&signing, &headers);
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
        let decision = HostDecision::RefusedFrame {
            command: "query".into(),
            byte: 255,
            encoded: vec![1],
            decoded: Some(revoked),
        };
        assert!(host_refusal_ending(&decision)
            .unwrap()
            .starts_with("refused: revoked: the grant is revoked (phase observation)\n"));
        // Prose that names a reason is not a reason.
        let nested = json!({"type":"refused","reason":"operation-rejected","phase":hex(b"prepare"),
            "detail":hex(b"invocation preparation: A.Reject.scalar\n  (B.Reject.pageMutation\n    (C.RejectReason.overflow))")});
        assert_eq!(
            refusal_line(&nested).unwrap(),
            "refused: operation-rejected: invocation preparation: A.Reject.scalar (B.Reject.pageMutation (C.RejectReason.overflow)) (phase prepare)"
        );
        let escape = json!({"type":"refused","reason":"malformed","phase":hex(b"x"),"detail":hex(b"a\x1b[2Jb")});
        assert!(refusal_line(&escape).unwrap().starts_with("refused: malformed: hex "));
        let prose = json!({"type":"refused","phase":hex(b"x"),"detail":hex(b"revoked")});
        assert!(refusal_line(&prose)
            .unwrap()
            .starts_with("refused: unnamed: revoked"));
        let undecoded = HostDecision::RefusedFrame {
            command: "query".into(),
            byte: 255,
            encoded: vec![1],
            decoded: None,
        };
        assert!(host_refusal_ending(&undecoded)
            .unwrap()
            .starts_with("refused: Host refused query, reply byte 255"));
        assert!(host_refusal_ending(&HostDecision::Outcome(json!({"type":"uncertain"}))).is_none());
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

        // --no-prerotation makes no next key at all.
        keygen(&directory.join("p.key"), &directory.join("p.pub"), None, NextKey::Without, false).unwrap();
        assert!(!directory.join("p.key.next").exists() && !directory.join("p.key.next.pub").exists());
        fs::remove_dir_all(directory).unwrap();
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
        fs::write(
            &host,
            b"#!/bin/sh\nif [ \"$2\" = inspect ]; then printf '{\"type\":\"confirmed\"}' >\"$5\"; else cp \"$3\" \"$4\"; fi\n",
        )
        .unwrap();
        fs::set_permissions(&host, fs::Permissions::from_mode(0o700)).unwrap();
        fs::write(&config, b"{}").unwrap();
        fs::write(&call, [0, 1, 2, 255, 17]).unwrap();
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
