//! One bounded re-observe-and-re-plan loop for every client operation that
//! observes and then acts on the observation.
//!
//! A signed observation binds the world root, authority root and height of
//! the challenge it answers, so any admission between observing and using the
//! observation (a clock tick, a certify, a friend's write) makes the Host
//! refuse with its own `stale-root`. The kernel's rule stays: any commit stales
//! a signed read. The client re-plans: it retires the definitely unadmitted
//! attempt's evidence and observes again.
//!
//! The bound is TIME, not a count (`--replan-window`, default
//! `DEFAULT_WINDOW`). Every refusal this loop retries is the Host's proof that
//! ANOTHER admission landed first (a moved challenge, a moved target), so a
//! retry means the system made progress, not that this writer failed. How many
//! such refusals an honest writer meets is the number of writes that land
//! inside its observe-to-admit window, which grows with the room and with the
//! Host's turn time: five members writing one document on a Host whose turn
//! costs 30 s exhausted a fixed five re-plans (composed scenario, load 45).
//! `--replan-max N` remains an explicit count ceiling (`0` is the old single
//! observation); by default there is none, and the window alone bounds the loop.
//! Between re-plans the writer waits a random fraction of its own last attempt's
//! duration (`pause`), so writers refused by the same landing re-observe at
//! different moments instead of colliding again in lockstep.
//!
//! The default predicate retries the Host's own `stale-root` answer and the
//! local consent provider's `stale observation` refusal: the provider admitted a
//! newer source than the Host's challenge was built over, for this exact intent
//! (`Kernel.NativeClientConsent.classify_stale`). Nothing was signed; the next
//! attempt asks for a challenge on the current source. A challenge for another
//! intent stays a terminal refusal (`remote challenge differs ...`).
//! Workspace text append additionally requires a final decoded admission
//! refusal, the Host's named `stale-target` refusal of the append's own target
//! (`submit_stale_target`), or the controller's exact typed prepare staleTarget
//! refusal, plus a fresh authorized read proving its client-selected preimage
//! changed; it then submits a new call (fresh nonce, identical text) against
//! the new root, recording the class in the retired attempt's
//! `replan-reason.json`.
//! No uncertain or undecoded decision qualifies for either path.
//! A `stale-root` is a refusal: nothing was admitted, so the
//! retired attempt can never install, and the next attempt carries a fresh
//! observation (the plan never carries a stale guard).

use std::fs;
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicU32, AtomicU64, Ordering};
use std::time::{Duration, Instant};

use serde_json::Value;

use crate::{note_host_decision, take_host_decision, HostDecision};

type Result<T> = std::result::Result<T, String>;

/// No count ceiling: the window bounds the loop (`--replan-max` sets one).
pub(crate) const DEFAULT_MAX: u32 = u32::MAX;

/// Wall-clock seconds after which a still-refused operation stops re-planning
/// (`--replan-window`). Ten minutes covers a room of tens of writers on a Host
/// whose turn costs tens of seconds; it is a liveness bound, not a timeout of
/// one attempt (an attempt in flight always finishes and is classified).
pub(crate) const DEFAULT_WINDOW: u64 = 600;

/// The directory inside an attempt that holds its superseded plans.
pub(crate) const REPLANNED: &str = "replanned";

static MAX: AtomicU32 = AtomicU32::new(DEFAULT_MAX);
static WINDOW: AtomicU64 = AtomicU64::new(DEFAULT_WINDOW);
static COUNT: AtomicU32 = AtomicU32::new(0);

/// Tests that set the process-wide bound or read the recorded Host decision
/// serialize on this lock.
#[cfg(test)]
pub(crate) static TEST_LOCK: std::sync::Mutex<()> = std::sync::Mutex::new(());
static CONFIGURED: std::sync::atomic::AtomicBool = std::sync::atomic::AtomicBool::new(false);
static WINDOW_CONFIGURED: std::sync::atomic::AtomicBool = std::sync::atomic::AtomicBool::new(false);

pub(crate) fn set_max(max: u32) {
    MAX.store(max, Ordering::Relaxed);
}

pub(crate) fn max() -> u32 {
    MAX.load(Ordering::Relaxed)
}

pub(crate) fn set_window(seconds: u64) {
    WINDOW.store(seconds, Ordering::Relaxed);
}

pub(crate) fn window() -> Duration {
    Duration::from_secs(WINDOW.load(Ordering::Relaxed))
}

/// Re-plans taken since the last call (the shell reports them per command).
pub(crate) fn take_count() -> u32 {
    COUNT.swap(0, Ordering::Relaxed)
}

/// `--replan-max N` / `--replan-window SECONDS`, or `MINI_REPLAN_MAX` /
/// `MINI_REPLAN_WINDOW` when a flag is absent.
pub(crate) fn configure(max: Option<std::ffi::OsString>, window: Option<std::ffi::OsString>) -> Result<()> {
    if let Some(text) = setting(max, "--replan-max", "MINI_REPLAN_MAX", &CONFIGURED)? {
        let max = text.parse::<u32>().ok().filter(|max| *max <= 100)
            .ok_or("--replan-max must be a whole number 0..100")?;
        set_max(max);
    }
    if let Some(text) = setting(window, "--replan-window", "MINI_REPLAN_WINDOW", &WINDOW_CONFIGURED)? {
        let seconds = text.parse::<u64>().ok().filter(|seconds| *seconds <= 3600)
            .ok_or("--replan-window must be a whole number of seconds 0..3600")?;
        set_window(seconds);
    }
    Ok(())
}

/// A flag's text, else (once per process) the environment's.
fn setting(flag: Option<std::ffi::OsString>, name: &str, variable: &str,
    configured: &std::sync::atomic::AtomicBool) -> Result<Option<String>> {
    let text = match flag {
        Some(value) => value.into_string().map_err(|_| format!("{name} must be UTF-8"))?,
        // The shell runs every line through `run`: the bound it was started
        // with stays; the environment is read once.
        None if configured.load(Ordering::Relaxed) => return Ok(None),
        None => match std::env::var(variable) {
            Ok(value) => value,
            Err(_) => return Ok(None),
        },
    };
    configured.store(true, Ordering::Relaxed);
    Ok(Some(text))
}

/// Whether a Host outcome is the Host's own `stale-root` refusal.
pub(crate) fn outcome_is_stale_root(outcome: &Value) -> bool {
    outcome.get("type").and_then(Value::as_str) == Some("refused")
        && outcome.get("reason").and_then(Value::as_str) == Some("stale-root")
}

/// The Host's decoded outcome of a DECIDED no-effect answer: an operation's own answer, or a
/// `NO_RECORD` (253) frame. A `HOST_OUTCOME` (255) frame is undecided whatever it decodes to, and
/// an undecoded frame decides nothing; neither may re-plan or author anything new.
fn decided(decision: Option<&HostDecision>) -> Option<(&str, &Value)> {
    match decision {
        Some(HostDecision::Outcome(outcome)) => Some(("", outcome)),
        Some(HostDecision::Frame { command, byte, decoded: Some(outcome), .. }) if *byte == crate::RESPONSE_NO_RECORD => {
            Some((command.as_str(), outcome))
        }
        _ => None,
    }
}

/// Whether a recorded Host decision is the Host's own `stale-root` refusal, decided with no
/// record (`decided`).
pub(crate) fn is_stale_root(decision: Option<&HostDecision>) -> bool {
    decided(decision).is_some_and(|(_, outcome)| outcome_is_stale_root(outcome))
}

/// Only a decided, final submit refusal can authorize a new append command.
/// A prepare/query refusal, lost reply or undecided outcome cannot do so.
pub(crate) fn is_final_admission_refusal(decision: Option<&HostDecision>) -> bool {
    let Some((command, outcome)) = decided(decision) else { return false };
    if !(command.is_empty() || command == "submit") {
        return false;
    }
    outcome["type"] == "refused" && outcome["phase"] == "61646d697373696f6e"
}

/// The native controller rejected this exact invocation target before any
/// call was assembled. Match the Host's decoded typed detail exactly.
pub(crate) fn is_prepare_stale_target(decision: Option<&HostDecision>) -> bool {
    let Some((command, value)) = decided(decision) else { return false };
    command == "prepare" && value["type"] == "refused" && value["reason"] == "operation-rejected"
        && value["phase"] == "70726570617265"
        && value["detail"] == crate::hex(b"invocation preparation: Minidregg.Kernel.DeclaredResourceController.Reject.staleTarget")
}

/// The Host's named moved-target refusal of a signed submission: the decoded
/// outcome `refused`, reason `operation-rejected`, phase `stale-target`, detail
/// `target N moved since the plan was signed` (`Kernel/NativeHost.lean`
/// `staleOutcome`, `stalePhase`). Returns N. The Host names the target only to
/// its authenticated signer, and only when the signer observes the whole cell,
/// so the client can prove the move itself with a fresh signed read. The byte
/// that carried it (255, or the positive `NO_RECORD` 253 the Host is growing for
/// proven no-append outcomes) does not matter: only the Host's own decoding
/// classifies.
///
/// Why a NEW call is legitimate here and nowhere else in the append path: the
/// refusal is decided in `prepareFrom`, before `DurableServed.receiveServed`
/// is reached, so nothing was appended, and the re-planned call carries the
/// identical text against the new root. Whether every `staleTarget` refusal at
/// admission is proven no-append is the open Lean question Q2/Q3
/// (docs/review/2026-10-26-native-crates/resource-client.md §8, "Questions for
/// the Lean side"; lane L1 owns the answer). A session frame re-plans only
/// under `NO_RECORD` (253), the Host's proof that nothing was appended; the
/// same decoded refusal under `HOST_OUTCOME` (255) is undecided and is looked
/// up, never re-planned.
pub(crate) fn submit_stale_target(decision: Option<&HostDecision>) -> Option<String> {
    let (command, outcome) = decided(decision)?;
    if !(command.is_empty() || command == "submit") {
        return None;
    }
    if outcome["type"] != "refused" || outcome["reason"] != "operation-rejected"
        || outcome["phase"] != crate::hex(b"stale-target") {
        return None;
    }
    let detail = mini_sdk::hex::decode(outcome["detail"].as_str()?).ok()?;
    let target = std::str::from_utf8(&detail).ok()?
        .strip_prefix("target ")?
        .strip_suffix(" moved since the plan was signed")?;
    (target.len() <= 40 && mini_sdk::decimal::is_digits(target))
        .then(|| target.to_owned())
}

/// Run `attempt` until it succeeds, or until a failure that `race` does not
/// name as the timer race, or until the re-plan window (`window()`) has passed
/// or an explicit `max()` re-plans are spent. Between
/// attempts, `retire(n)` sets the definitely unadmitted attempt `n` aside so
/// the next attempt observes afresh. `race` sees the client error and the
/// Host decision recorded for it; the decision stays recorded for the caller.
pub(crate) fn replan<T>(
    what: &str,
    mut attempt: impl FnMut() -> Result<T>,
    mut race: impl FnMut(&str, Option<&HostDecision>) -> bool,
    mut retire: impl FnMut(u32) -> Result<()>,
) -> Result<T> {
    let max = max();
    let window = window();
    let mut replans = 0u32;
    let started = Instant::now();
    let mut superseded = Duration::ZERO;
    loop {
        // A refusal authorizes recovery only for the attempt that produced it.
        // The previous verdict remains available to callers until a new
        // attempt starts, but cannot classify its local error or lost reply.
        let _ = take_host_decision();
        let _ = crate::client_consent::take_stale_observation();
        let began = Instant::now();
        let error = match attempt() {
            Ok(value) => {
                measure(what, replans, "landed", started, superseded);
                return Ok(value);
            }
            Err(error) => error,
        };
        let decision = take_host_decision();
        let raced = race(&error, decision.as_ref());
        if let Some(decision) = decision {
            note_host_decision(decision);
        }
        if !raced {
            measure(what, replans, "refused", started, superseded);
            return Err(error);
        }
        let last = began.elapsed();
        let bound = if replans >= max {
            Some(format!("--replan-max {max}"))
        } else if started.elapsed() >= window {
            Some(format!("--replan-window {} s", window.as_secs()))
        } else {
            None
        };
        if let Some(bound) = bound {
            measure(what, replans, "exhausted", started, superseded + last);
            return Err(format!(
                "{what}: concurrent source changes exhausted all {} attempts ({replans} re-plans, {bound}, {} s); last answer: {error}",
                replans + 1,
                started.elapsed().as_secs()
            ));
        }
        replans += 1;
        retire(replans)?;
        pause(replans, last, window.saturating_sub(started.elapsed()));
        superseded += began.elapsed();
        COUNT.fetch_add(1, Ordering::Relaxed);
        eprintln!("mini: {what}: the observed source changed before the plan landed; observing again (re-plan {replans}, {} s of {} s)",
            started.elapsed().as_secs(), window.as_secs());
    }
}

/// The shortest scale a pause is drawn over, so a fast local Host still spreads writers.
const PAUSE_FLOOR: Duration = Duration::from_millis(50);
/// The longest scale: past it a writer would idle longer than any one Host turn.
const PAUSE_CEILING: Duration = Duration::from_secs(30);

/// The first re-plan observes at once (a timer write is over by then). Later
/// ones wait a uniformly random time in `[0, scale)`, where `scale` is the
/// writer's own last attempt (its observe-to-answer window, clamped to
/// `PAUSE_FLOOR..PAUSE_CEILING`) doubled per further re-plan up to four times.
/// Writers refused by one landing thereby re-observe spread over about one turn
/// instead of together, so one round no longer has one winner and every other
/// writer a loser again. A pause never outlasts the remaining window.
fn pause(replans: u32, last: Duration, remaining: Duration) {
    if replans < 2 {
        return;
    }
    std::thread::sleep(pause_for(replans, last, remaining, unit()));
}

/// The pause for `replans` (at least 2) given a uniform draw `unit` in `[0, 1)`.
fn pause_for(replans: u32, last: Duration, remaining: Duration, unit: f64) -> Duration {
    let scale = last.clamp(PAUSE_FLOOR, PAUSE_CEILING) * (1u32 << replans.saturating_sub(2).min(2));
    scale.mul_f64(unit.clamp(0.0, 1.0)).min(remaining)
}

/// A uniform draw in `[0, 1)` from operating-system randomness (the clock's
/// nanoseconds only if that is unavailable: a pause is never a secret).
fn unit() -> f64 {
    let bits = mini_sdk::random::bytes::<8>().map(u64::from_be_bytes).unwrap_or_else(|_| {
        std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH)
            .map(|now| u64::from(now.subsec_nanos()) << 32)
            .unwrap_or(0)
    });
    (bits >> 11) as f64 / (1u64 << 53) as f64
}

/// `MINI_REPLAN_LOG=FILE` appends one line per loop: what, re-plans, ending,
/// total ms, ms spent on superseded attempts (the cost of the race).
fn measure(what: &str, replans: u32, ending: &str, started: Instant, superseded: Duration) {
    let Some(path) = std::env::var_os("MINI_REPLAN_LOG") else { return };
    let line = format!(
        "{what}\t{replans}\t{ending}\t{}\t{}\n",
        started.elapsed().as_millis(),
        superseded.as_millis()
    );
    let _ = fs::OpenOptions::new()
        .create(true)
        .append(true)
        .open(path)
        .and_then(|mut file| std::io::Write::write_all(&mut file, line.as_bytes()));
}

/// The default race test: the Host's own `stale-root` answer.
pub(crate) fn stale_root(_error: &str, decision: Option<&HostDecision>) -> bool {
    // Both are read so the local record never outlives this attempt.
    let local = crate::client_consent::take_stale_observation();
    is_stale_root(decision) || local
}

/// Move every entry of `directory` except `keep` (and earlier retirements)
/// into `directory/replanned/NN`, keeping every byte of the superseded
/// attempt as evidence. The attempt path itself is unchanged, so a namespace
/// binding that names it still names the one attempt that may install.
pub(crate) fn retire(directory: &Path, number: u32, keep: &[&str]) -> Result<PathBuf> {
    let parent = directory.join(REPLANNED);
    if !parent.exists() {
        crate::fsio::create_private_dir(&parent)?;
    }
    let target = parent.join(format!("{number:02}"));
    if target.exists() {
        return Err(format!("{} already holds a retired plan", target.display()));
    }
    crate::fsio::create_private_dir(&target)?;
    let mut names = Vec::new();
    for entry in fs::read_dir(directory).map_err(|error| error.to_string())? {
        let name = entry.map_err(|error| error.to_string())?.file_name();
        let text = name.to_string_lossy();
        if text == REPLANNED || keep.contains(&text.as_ref()) {
            continue;
        }
        names.push(name);
    }
    for name in names {
        fs::rename(directory.join(&name), target.join(&name))
            .map_err(|error| format!("cannot retire {}: {error}", directory.join(&name).display()))?;
    }
    Ok(target)
}

/// Whether an attempt directory retains an installed or replayed receipt
/// (`outcome.json` or an exact `retry-*.json`).
fn holds_accepted(directory: &Path) -> Result<bool> {
    for entry in fs::read_dir(directory).map_err(|error| error.to_string())? {
        let name = entry.map_err(|error| error.to_string())?.file_name();
        let name = name.to_string_lossy();
        if name != "outcome.json" && !(name.starts_with("retry-") && name.ends_with(".json")) {
            continue;
        }
        let Ok(bytes) = fs::read(directory.join(name.as_ref())) else { continue };
        let Ok(value) = serde_json::from_slice::<Value>(&bytes) else { continue };
        if value.get("type").and_then(Value::as_str) == Some("confirmed")
            && matches!(value.get("confirmation").and_then(Value::as_str),
                Some("installed" | "recoveredAfterUncertainResponse" | "replayed"))
        {
            return Ok(true);
        }
    }
    Ok(false)
}

/// Retire a `submit`/`query` attempt. A Host `stale-root` is a refusal, so the
/// attempt is definitely unadmitted; an attempt holding an installed or
/// replayed receipt is never retired.
pub(crate) fn retire_attempt(directory: &Path, number: u32) -> Result<()> {
    if directory.exists() && holds_accepted(directory)? {
        return Err(format!(
            "{} holds an accepted outcome; it is never re-planned",
            directory.display()
        ));
    }
    retire(directory, number, &[]).map(|_| ())
}

/// Allocate a new evidence slot for a reused proposal or attempt without
/// overwriting an earlier command's retained refused calls.
pub(crate) fn retire_next(directory: &Path) -> Result<()> {
    let parent = directory.join(REPLANNED);
    let mut next = 1u32;
    if parent.exists() {
        for entry in fs::read_dir(&parent).map_err(|error| error.to_string())? {
            let entry = entry.map_err(|error| error.to_string())?;
            let number = entry.file_name().to_string_lossy().parse::<u32>()
                .map_err(|_| "invalid retained replan evidence slot")?;
            next = next.max(number.checked_add(1).ok_or("replan evidence slot overflow")?);
        }
    }
    retire_attempt(directory, next)
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::json;
    use std::cell::Cell;

    use super::TEST_LOCK as LOCK;

    #[test]
    fn append_recovery_requires_decoded_final_admission_refusal() {
        let value = json!({"type":"refused","reason":"undisclosed","phase":"61646d697373696f6e"});
        assert!(is_final_admission_refusal(Some(&HostDecision::Outcome(value.clone()))));
        for command in ["prepare", "query", "submit"] {
            let frame = HostDecision::Frame { command:command.into(), byte:crate::RESPONSE_NO_RECORD,
                encoded:vec![1], decoded:Some(value.clone()) };
            assert_eq!(is_final_admission_refusal(Some(&frame)), command == "submit");
            // The same decoding under the undecided envelope authorizes nothing.
            let envelope = HostDecision::Frame { command:command.into(), byte:crate::RESPONSE_HOST_OUTCOME,
                encoded:vec![1], decoded:Some(value.clone()) };
            assert!(!is_final_admission_refusal(Some(&envelope)));
        }
        for kind in ["uncertain", "unavailable", "contention", "absent", "confirmed"] {
            let mut other = value.clone(); other["type"] = json!(kind);
            assert!(!is_final_admission_refusal(Some(&HostDecision::Outcome(other))));
        }
        let mut other_phase = value; other_phase["phase"] = json!(hex("observation"));
        assert!(!is_final_admission_refusal(Some(&HostDecision::Outcome(other_phase))));
        assert!(!is_final_admission_refusal(None));
        assert!(!is_final_admission_refusal(Some(&HostDecision::Frame {
            command:"submit".into(), byte:255, encoded:vec![1], decoded:None })));
    }

    #[test]
    fn append_prepare_recovery_matches_exact_native_stale_target_only() {
        let value = json!({"type":"refused","reason":"operation-rejected","phase":hex("prepare"),
            "detail":hex("invocation preparation: Minidregg.Kernel.DeclaredResourceController.Reject.staleTarget")});
        let frame = |command:&str, value:Value| HostDecision::Frame {
            command:command.into(), byte:crate::RESPONSE_NO_RECORD, encoded:vec![1], decoded:Some(value) };
        assert!(is_prepare_stale_target(Some(&frame("prepare", value.clone()))));
        assert!(!is_prepare_stale_target(Some(&HostDecision::Frame { command:"prepare".into(),
            byte:crate::RESPONSE_HOST_OUTCOME, encoded:vec![1], decoded:Some(value.clone()) })));
        assert!(!is_prepare_stale_target(Some(&frame("submit", value.clone()))));
        // An operation's own answer is decided, but it is no prepare refusal frame.
        assert!(!is_prepare_stale_target(Some(&HostDecision::Outcome(value.clone()))));
        for (key, replacement) in [("type", "uncertain"), ("reason", "undisclosed"), ("phase", "61646d697373696f6e"),
            ("detail", "another staleTarget suffix")] {
            let mut other = value.clone(); other[key] = json!(replacement);
            assert!(!is_prepare_stale_target(Some(&frame("prepare", other))));
        }
        assert!(!is_prepare_stale_target(None));
        assert!(!is_prepare_stale_target(Some(&HostDecision::Frame {
            command:"prepare".into(), byte:255, encoded:vec![1], decoded:None })));
    }

    #[test]
    fn nested_recovery_never_overwrites_evidence_or_retires_an_acceptance() {
        let base = std::env::temp_dir().join(format!("nested-replan-{}", std::process::id()));
        let _ = fs::remove_dir_all(&base); crate::fsio::create_private_dir(&base).unwrap();
        fs::write(base.join("call.bin"), b"original").unwrap();
        retire_attempt(&base, 1).unwrap();
        fs::write(base.join("call.bin"), b"fresh observation").unwrap();
        retire_next(&base).unwrap();
        fs::write(base.join("call.bin"), b"fresh append").unwrap();
        retire_next(&base).unwrap();
        for (slot, bytes) in [("01", b"original".as_slice()), ("02", b"fresh observation"), ("03", b"fresh append")] {
            assert_eq!(fs::read(base.join(REPLANNED).join(slot).join("call.bin")).unwrap(), bytes);
        }
        fs::write(base.join("outcome.json"), br#"{"type":"confirmed","confirmation":"installed"}"#).unwrap();
        assert!(retire_next(&base).unwrap_err().contains("never re-planned"));
        assert!(!base.join(REPLANNED).join("04").exists());
        fs::remove_dir_all(&base).unwrap();
    }

    fn hex(text: &str) -> String {
        mini_sdk::hex::encode(text.as_bytes())
    }

    fn refused(reason: &str) -> HostDecision {
        HostDecision::Frame {
            command: "prepare".into(),
            byte: crate::RESPONSE_NO_RECORD,
            encoded: vec![0x44],
            decoded: Some(json!({"type":"refused","reason":reason,
                "phase":hex("observation"),"detail":hex("x")})),
        }
    }

    fn run(max: u32, answers: Vec<Option<HostDecision>>) -> (Result<u32>, u32, u32) {
        set_max(max);
        let _ = take_count();
        let _ = take_host_decision();
        let calls = Cell::new(0u32);
        let retired = Cell::new(0u32);
        let result = replan(
            "test",
            || {
                let index = calls.get() as usize;
                calls.set(calls.get() + 1);
                match answers.get(index).cloned().flatten() {
                    None if index < answers.len() => Err("client: no Host decision".into()),
                    None => Ok(calls.get()),
                    Some(decision) => {
                        note_host_decision(decision);
                        Err("host refused".into())
                    }
                }
            },
            stale_root,
            |number| {
                assert_eq!(number, retired.get() + 1, "retirements are numbered in order");
                retired.set(number);
                Ok(())
            },
        );
        (result, calls.get(), retired.get())
    }

    #[test]
    fn replan_retries_stale_root_and_lands() {
        let _guard = LOCK.lock().unwrap_or_else(|p| p.into_inner());
        let (result, calls, retired) =
            run(5, vec![Some(refused("stale-root")), Some(refused("stale-root"))]);
        assert_eq!(result, Ok(3));
        assert_eq!((calls, retired), (3, 2));
        assert_eq!(take_count(), 2);
        set_max(DEFAULT_MAX);
    }

    #[test]
    fn replan_is_bounded_and_names_attempts_and_last_answer() {
        let _guard = LOCK.lock().unwrap_or_else(|p| p.into_inner());
        let (result, calls, retired) = run(5, vec![Some(refused("stale-root")); 9]);
        let error = result.unwrap_err();
        assert_eq!((calls, retired), (6, 5));
        assert!(error.contains("all 6 attempts (5 re-plans, --replan-max 5,"), "{error}");
        assert!(error.ends_with("last answer: host refused"), "{error}");
        // The last stale-root stays recorded: the friend sees the Host's own line.
        assert!(is_stale_root(take_host_decision().as_ref()));
        set_max(DEFAULT_MAX);
    }

    #[test]
    fn replan_max_zero_is_the_old_behaviour() {
        let _guard = LOCK.lock().unwrap_or_else(|p| p.into_inner());
        let (result, calls, retired) = run(0, vec![Some(refused("stale-root"))]);
        assert!(result.unwrap_err().contains("all 1 attempts (0 re-plans"));
        assert_eq!((calls, retired), (1, 0));
        set_max(DEFAULT_MAX);
    }

    #[test]
    fn replan_never_retries_another_refusal() {
        let _guard = LOCK.lock().unwrap_or_else(|p| p.into_inner());
        for reason in ["law-denied", "undisclosed", "bad-signature", "no-grant", "conflict",
            "operation-rejected", "tail-bound", "over-bound", "rate-limited"]
        {
            let (result, calls, retired) = run(5, vec![Some(refused(reason))]);
            assert_eq!(result, Err("host refused".into()), "{reason}");
            assert_eq!((calls, retired), (1, 0), "{reason}");
            let kept = take_host_decision();
            assert_eq!(kept, Some(refused(reason)), "{reason}: the Host's answer stays recorded");
        }
        set_max(DEFAULT_MAX);
    }

    /// The same decoded `stale-root` re-plans under `NO_RECORD` (253) and never under the
    /// undecided envelope `HOST_OUTCOME` (255).
    #[test]
    fn only_a_no_record_stale_root_re_plans() {
        let _guard = LOCK.lock().unwrap_or_else(|p| p.into_inner());
        let mut envelope = refused("stale-root");
        if let HostDecision::Frame { byte, .. } = &mut envelope {
            *byte = crate::RESPONSE_HOST_OUTCOME;
        }
        assert!(is_stale_root(Some(&refused("stale-root"))));
        assert!(!is_stale_root(Some(&envelope)));
        let (result, calls, retired) = run(5, vec![Some(envelope)]);
        assert!(result.is_err());
        assert_eq!((calls, retired), (1, 0));
        let _ = take_host_decision();
        set_max(DEFAULT_MAX);
    }

    #[test]
    fn replan_never_retries_an_uncertain_or_undecoded_outcome() {
        let _guard = LOCK.lock().unwrap_or_else(|p| p.into_inner());
        let undecided = ["uncertain", "unavailable", "contention", "absent"]
            .map(|kind| Some(HostDecision::Outcome(json!({"type":kind}))));
        for decision in undecided {
            let (result, calls, _) = run(5, vec![decision]);
            assert!(result.is_err());
            assert_eq!(calls, 1);
        }
        // A refusal frame the Host did not decode, and a client error with no
        // Host decision at all (a lost reply), are not the race.
        let undecoded = HostDecision::Frame {
            command: "submit".into(),
            byte: 255,
            encoded: vec![1],
            decoded: None,
        };
        for answers in [vec![Some(undecoded)], vec![None]] {
            let (result, calls, retired) = run(5, answers);
            assert!(result.is_err());
            assert_eq!((calls, retired), (1, 0));
        }
        let _ = take_host_decision();
        set_max(DEFAULT_MAX);
    }

    #[test]
    fn prior_stale_refusal_cannot_classify_the_next_lost_reply() {
        let _guard = LOCK.lock().unwrap_or_else(|p| p.into_inner());
        let (result, calls, retired) = run(5, vec![Some(refused("stale-root")), None]);
        assert_eq!(result, Err("client: no Host decision".into()));
        assert_eq!((calls, retired), (2, 1));
        assert!(take_host_decision().is_none());
        set_max(DEFAULT_MAX);
    }

    #[test]
    fn earlier_command_refusal_does_not_authorize_this_attempt() {
        let _guard = LOCK.lock().unwrap_or_else(|p| p.into_inner());
        note_host_decision(refused("stale-root"));
        let result: Result<()> = replan("local failure", || Err("key unavailable".into()),
            stale_root, |_| panic!("a different command's refusal cannot retire this attempt"));
        assert_eq!(result, Err("key unavailable".into()));
        assert!(take_host_decision().is_none());
    }

    /// With no count ceiling (the default), a writer that keeps meeting
    /// other writers keeps re-planning past the old fixed five, and lands.
    #[test]
    fn default_bound_is_the_window_not_a_count() {
        let _guard = LOCK.lock().unwrap_or_else(|p| p.into_inner());
        set_window(DEFAULT_WINDOW);
        let (result, calls, retired) = run(DEFAULT_MAX, vec![Some(refused("stale-root")); 8]);
        assert_eq!((result, calls, retired), (Ok(9), 9, 8));
        let _ = take_count();
        set_max(DEFAULT_MAX);
    }

    /// The window bounds an endless stream of refusals: the loop stops once
    /// it has passed, names the window, and keeps the Host's last answer.
    #[test]
    fn replan_window_bounds_an_endless_race() {
        let _guard = LOCK.lock().unwrap_or_else(|p| p.into_inner());
        set_window(0);
        let (result, calls, retired) = run(DEFAULT_MAX, vec![Some(refused("stale-root")); 50]);
        let error = result.unwrap_err();
        assert_eq!((calls, retired), (1, 0));
        assert!(error.contains("all 1 attempts (0 re-plans, --replan-window 0 s,"), "{error}");
        assert!(is_stale_root(take_host_decision().as_ref()));
        set_window(DEFAULT_WINDOW);
        set_max(DEFAULT_MAX);
    }

    /// The pause scales with the writer's own attempt time, doubles per
    /// re-plan up to four times, never exceeds the remaining window, and the
    /// first re-plan does not wait.
    #[test]
    fn pause_scales_with_the_attempt_and_is_bounded() {
        let turn = Duration::from_secs(5);
        let lots = Duration::from_secs(3600);
        assert_eq!(pause_for(2, turn, lots, 0.0), Duration::ZERO);
        assert_eq!(pause_for(2, turn, lots, 0.5), Duration::from_millis(2500));
        assert_eq!(pause_for(3, turn, lots, 0.5), Duration::from_secs(5));
        assert_eq!(pause_for(4, turn, lots, 0.5), Duration::from_secs(10));
        assert_eq!(pause_for(9, turn, lots, 0.5), Duration::from_secs(10), "doubling stops at four");
        assert_eq!(pause_for(2, Duration::ZERO, lots, 1.0), PAUSE_FLOOR);
        assert_eq!(pause_for(2, Duration::from_secs(600), lots, 1.0), PAUSE_CEILING);
        assert_eq!(pause_for(4, turn, Duration::from_secs(1), 0.9), Duration::from_secs(1));
        let draws: Vec<f64> = (0..64).map(|_| unit()).collect();
        assert!(draws.iter().all(|u| (0.0..1.0).contains(u)));
        assert!(draws.windows(2).any(|pair| pair[0] != pair[1]), "draws vary");
        let started = Instant::now();
        pause(1, lots, lots);
        assert!(started.elapsed() < Duration::from_millis(20), "the first re-plan observes at once");
    }

    #[test]
    fn successful_replan_does_not_leave_a_superseded_refusal() {
        let _guard = LOCK.lock().unwrap_or_else(|p| p.into_inner());
        let (result, calls, retired) = run(5, vec![Some(refused("stale-root"))]);
        assert_eq!((result, calls, retired), (Ok(2), 2, 1));
        assert!(take_host_decision().is_none());
        set_max(DEFAULT_MAX);
    }

    #[test]
    fn exact_readback_after_uncertain_cas_is_never_retired() {
        let base = std::env::temp_dir().join(format!("recovered-replan-{}", std::process::id()));
        crate::fsio::create_private_dir(&base).unwrap();
        fs::write(base.join("outcome.json"),
            br#"{"type":"confirmed","confirmation":"recoveredAfterUncertainResponse"}"#).unwrap();
        fs::write(base.join("call.bin"), b"exact accepted call").unwrap();
        assert!(retire_attempt(&base, 1).is_err());
        assert_eq!(fs::read(base.join("call.bin")).unwrap(), b"exact accepted call");
        assert!(!base.join(REPLANNED).exists());
        fs::remove_dir_all(base).unwrap();
    }

    #[test]
    fn replan_outcome_refused_stale_root_is_the_race() {
        let outcome = json!({"type":"refused","reason":"stale-root"});
        assert!(is_stale_root(Some(&HostDecision::Outcome(outcome))));
        assert!(!is_stale_root(Some(&HostDecision::Outcome(json!({"type":"uncertain",
            "reason":"stale-root"})))));
    }

    #[test]
    fn replan_retire_keeps_evidence_and_never_retires_an_accepted_attempt() {
        let base = std::env::temp_dir().join(format!("replan-retire-{}", std::process::id()));
        let _ = fs::remove_dir_all(&base);
        crate::fsio::create_private_dir(&base).unwrap();
        let attempt = base.join("a");
        crate::fsio::create_private_dir(&attempt).unwrap();
        fs::write(attempt.join("challenge.bin"), b"one").unwrap();
        fs::write(attempt.join("plan.bin.refusal"), b"stale").unwrap();
        retire_attempt(&attempt, 1).unwrap();
        assert_eq!(fs::read(attempt.join("replanned/01/challenge.bin")).unwrap(), b"one");
        assert!(!attempt.join("challenge.bin").exists());
        fs::write(attempt.join("challenge.bin"), b"two").unwrap();
        retire_attempt(&attempt, 2).unwrap();
        assert_eq!(fs::read(attempt.join("replanned/02/challenge.bin")).unwrap(), b"two");
        assert!(retire_attempt(&attempt, 2).is_err(), "a retirement number is used once");
        fs::write(attempt.join("outcome.json"),
            br#"{"type":"confirmed","confirmation":"installed"}"#).unwrap();
        assert!(retire_attempt(&attempt, 3).unwrap_err().contains("never re-planned"));
        assert!(attempt.join("outcome.json").exists());
        let _ = fs::remove_dir_all(&base);
    }

    #[test]
    fn append_submit_stale_target_names_the_moved_target_only() {
        let value = |phase: &[u8], detail: &[u8]| serde_json::json!({"type":"refused","reason":"operation-rejected",
            "phase":crate::hex(phase),"detail":crate::hex(detail)});
        let good = value(b"stale-target", b"target 42 moved since the plan was signed");
        let frame = |byte| HostDecision::Frame { command: "submit".into(), byte, encoded: vec![], decoded: Some(good.clone()) };
        assert_eq!(submit_stale_target(Some(&frame(253))).as_deref(), Some("42"));
        // The same decoded refusal under 255 is undecided: looked up, never re-planned.
        assert_eq!(submit_stale_target(Some(&frame(255))), None);
        assert_eq!(submit_stale_target(Some(&HostDecision::Outcome(good.clone()))).as_deref(), Some("42"));
        let prepare = HostDecision::Frame { command: "prepare".into(), byte: 255, encoded: vec![], decoded: Some(good.clone()) };
        assert_eq!(submit_stale_target(Some(&prepare)), None);
        for other in [value(b"invoke", b"target 42 moved since the plan was signed"),
            value(b"stale-target", b"target 4x2 moved since the plan was signed"),
            value(b"stale-target", b"target 42 moved"), value(b"stale-target", b"target  moved since the plan was signed")] {
            assert_eq!(submit_stale_target(Some(&HostDecision::Outcome(other))), None);
        }
        let mut uncertain = good.clone(); uncertain["type"] = serde_json::json!("uncertain");
        assert_eq!(submit_stale_target(Some(&HostDecision::Outcome(uncertain))), None);
        assert_eq!(submit_stale_target(Some(&HostDecision::Frame {
            command: "submit".into(), byte: 255, encoded: vec![1], decoded: None })), None);
    }

}
