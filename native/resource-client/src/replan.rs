//! One bounded re-observe-and-re-plan loop for every client operation that
//! observes and then acts on the observation.
//!
//! A signed observation binds the world root, authority root and height of
//! the challenge it answers, so any admission between observing and using the
//! observation (a clock tick, a certify, a friend's write) makes the Host
//! refuse with its own `stale-root`. The kernel's rule stays: any commit stales
//! a signed read. The client re-plans: it retires the definitely unadmitted
//! attempt's evidence and observes again, at most `max()` times.
//!
//! The default predicate retries only the Host's own `stale-root` answer.
//! Workspace text append additionally requires a final decoded admission
//! refusal or the controller's exact typed prepare staleTarget refusal, plus
//! a fresh authorized read proving its client-selected preimage changed.
//! No uncertain or undecoded decision qualifies for either path.
//! A `stale-root` is a refusal: nothing was admitted, so the
//! retired attempt can never install, and the next attempt carries a fresh
//! observation (the plan never carries a stale guard).

use std::fs;
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicU32, Ordering};
use std::time::{Duration, Instant};

use serde_json::Value;

use crate::{note_host_decision, take_host_decision, HostDecision};

type Result<T> = std::result::Result<T, String>;

/// Re-plans one operation may take after its first attempt (`--replan-max`).
pub(crate) const DEFAULT_MAX: u32 = 5;

/// The directory inside an attempt that holds its superseded plans.
pub(crate) const REPLANNED: &str = "replanned";

static MAX: AtomicU32 = AtomicU32::new(DEFAULT_MAX);
static COUNT: AtomicU32 = AtomicU32::new(0);

/// Tests that set the process-wide bound or read the recorded Host decision
/// serialize on this lock.
#[cfg(test)]
pub(crate) static TEST_LOCK: std::sync::Mutex<()> = std::sync::Mutex::new(());
static CONFIGURED: std::sync::atomic::AtomicBool = std::sync::atomic::AtomicBool::new(false);

pub(crate) fn set_max(max: u32) {
    MAX.store(max, Ordering::Relaxed);
}

pub(crate) fn max() -> u32 {
    MAX.load(Ordering::Relaxed)
}

/// Re-plans taken since the last call (the shell reports them per command).
pub(crate) fn take_count() -> u32 {
    COUNT.swap(0, Ordering::Relaxed)
}

/// `--replan-max N`, or `MINI_REPLAN_MAX` when the flag is absent.
pub(crate) fn configure(flag: Option<std::ffi::OsString>) -> Result<()> {
    let text = match flag {
        Some(value) => value
            .into_string()
            .map_err(|_| "--replan-max must be UTF-8".to_owned())?,
        // The shell runs every line through `run`: the bound it was started
        // with stays; the environment is read once.
        None if CONFIGURED.load(Ordering::Relaxed) => return Ok(()),
        None => match std::env::var("MINI_REPLAN_MAX") {
            Ok(value) => value,
            Err(_) => return Ok(()),
        },
    };
    CONFIGURED.store(true, Ordering::Relaxed);
    let max = text
        .parse::<u32>()
        .ok()
        .filter(|max| *max <= 100)
        .ok_or("--replan-max must be a whole number 0..100")?;
    set_max(max);
    Ok(())
}

/// Whether a Host outcome is the Host's own `stale-root` refusal.
pub(crate) fn outcome_is_stale_root(outcome: &Value) -> bool {
    outcome.get("type").and_then(Value::as_str) == Some("refused")
        && outcome.get("reason").and_then(Value::as_str) == Some("stale-root")
}

/// Whether a recorded Host decision is the Host's own `stale-root` refusal,
/// read from the Host's own decoding. An undecoded frame is not one.
pub(crate) fn is_stale_root(decision: Option<&HostDecision>) -> bool {
    match decision {
        Some(HostDecision::RefusedFrame {
            decoded: Some(outcome),
            ..
        }) => outcome_is_stale_root(outcome),
        Some(HostDecision::Outcome(outcome)) => outcome_is_stale_root(outcome),
        _ => false,
    }
}

/// Only a decoded, final submit refusal can authorize a new append command.
/// A prepare/query refusal, lost reply or uncertain outcome cannot do so.
pub(crate) fn is_final_admission_refusal(decision: Option<&HostDecision>) -> bool {
    let outcome = match decision {
        Some(HostDecision::Outcome(value)) => value,
        Some(HostDecision::RefusedFrame { command, decoded: Some(value), .. })
            if command == "submit" => value,
        _ => return false,
    };
    outcome["type"] == "refused" && outcome["phase"] == "61646d697373696f6e"
}

/// The native controller rejected this exact invocation target before any
/// call was assembled. Match the Host's decoded typed detail exactly.
pub(crate) fn is_prepare_stale_target(decision: Option<&HostDecision>) -> bool {
    let Some(HostDecision::RefusedFrame { command, decoded:Some(value), .. }) = decision else { return false };
    command == "prepare" && value["type"] == "refused" && value["reason"] == "operation-rejected"
        && value["phase"] == "70726570617265"
        && value["detail"] == crate::hex(b"invocation preparation: Minidregg.Kernel.DeclaredResourceController.Reject.staleTarget")
}

/// Run `attempt` until it succeeds, or until a failure that `race` does not
/// name as the timer race, or until `max()` re-plans are spent. Between
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
    let mut replans = 0u32;
    let started = Instant::now();
    let mut superseded = Duration::ZERO;
    loop {
        // A refusal authorizes recovery only for the attempt that produced it.
        // The previous verdict remains available to callers until a new
        // attempt starts, but cannot classify its local error or lost reply.
        let _ = take_host_decision();
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
        if replans >= max {
            measure(what, replans, "exhausted", started, superseded + began.elapsed());
            return Err(format!(
                "{what}: concurrent source changes exhausted all {} attempts ({replans} re-plans, --replan-max {max}); last answer: {error}",
                replans + 1
            ));
        }
        replans += 1;
        retire(replans)?;
        pause(replans);
        superseded += began.elapsed();
        COUNT.fetch_add(1, Ordering::Relaxed);
        eprintln!("mini: {what}: the observed source changed before the plan landed; observing again ({replans} of {max})");
    }
}

/// The first re-plan observes at once (a timer write is over by then); later
/// ones wait 100 ms per re-plan plus up to 150 ms of jitter, so writers that
/// keep meeting (a busy room) stop meeting in lockstep.
fn pause(replans: u32) {
    if replans < 2 {
        return;
    }
    let jitter = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map(|now| u64::from(now.subsec_nanos()) % 150)
        .unwrap_or(0);
    std::thread::sleep(Duration::from_millis(100 * u64::from(replans - 1) + jitter));
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
    is_stale_root(decision)
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
    for synced in [directory, &target] {
        fs::File::open(synced)
            .and_then(|handle| handle.sync_all())
            .map_err(|error| error.to_string())?;
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
            let frame = HostDecision::RefusedFrame { command:command.into(), byte:255,
                encoded:vec![1], decoded:Some(value.clone()) };
            assert_eq!(is_final_admission_refusal(Some(&frame)), command == "submit");
        }
        for kind in ["uncertain", "unavailable", "contention", "absent", "confirmed"] {
            let mut other = value.clone(); other["type"] = json!(kind);
            assert!(!is_final_admission_refusal(Some(&HostDecision::Outcome(other))));
        }
        let mut other_phase = value; other_phase["phase"] = json!(hex("observation"));
        assert!(!is_final_admission_refusal(Some(&HostDecision::Outcome(other_phase))));
        assert!(!is_final_admission_refusal(None));
        assert!(!is_final_admission_refusal(Some(&HostDecision::RefusedFrame {
            command:"submit".into(), byte:255, encoded:vec![1], decoded:None })));
    }

    #[test]
    fn append_prepare_recovery_matches_exact_native_stale_target_only() {
        let value = json!({"type":"refused","reason":"operation-rejected","phase":hex("prepare"),
            "detail":hex("invocation preparation: Minidregg.Kernel.DeclaredResourceController.Reject.staleTarget")});
        let frame = |command:&str, value:Value| HostDecision::RefusedFrame {
            command:command.into(), byte:255, encoded:vec![1], decoded:Some(value) };
        assert!(is_prepare_stale_target(Some(&frame("prepare", value.clone()))));
        assert!(!is_prepare_stale_target(Some(&frame("submit", value.clone()))));
        assert!(!is_prepare_stale_target(Some(&HostDecision::Outcome(value.clone()))));
        for (key, replacement) in [("type", "uncertain"), ("reason", "undisclosed"), ("phase", "61646d697373696f6e"),
            ("detail", "another staleTarget suffix")] {
            let mut other = value.clone(); other[key] = json!(replacement);
            assert!(!is_prepare_stale_target(Some(&frame("prepare", other))));
        }
        assert!(!is_prepare_stale_target(None));
        assert!(!is_prepare_stale_target(Some(&HostDecision::RefusedFrame {
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
        text.bytes().map(|b| format!("{b:02x}")).collect()
    }

    fn refused(reason: &str) -> HostDecision {
        HostDecision::RefusedFrame {
            command: "prepare".into(),
            byte: 255,
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
        assert!(error.contains("all 6 attempts (5 re-plans, --replan-max 5)"), "{error}");
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
            "operation-rejected", "tail-bound"]
        {
            let (result, calls, retired) = run(5, vec![Some(refused(reason))]);
            assert_eq!(result, Err("host refused".into()), "{reason}");
            assert_eq!((calls, retired), (1, 0), "{reason}");
            let kept = take_host_decision();
            assert_eq!(kept, Some(refused(reason)), "{reason}: the Host's answer stays recorded");
        }
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
        let undecoded = HostDecision::RefusedFrame {
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
}
