//! The typed close of a reserve whose custody attempt never wrote its call
//! (`reconcile parent unsent`, `reconcile tool unsent`; also tried by startup recovery).
//!
//! A reserve is write-ahead: the controller records the pending attempt and points the hold at
//! it, then runs the custody client, which retains every step in the attempt directory and seals
//! the exact call into `call.bin` before it transmits anything (`mini_sdk::flow::Flow::seal`, then
//! `transmit`, which sends the bytes it reads back from `call.bin`). A client that dies before
//! sealing leaves the pending attempt with no call. On demo-dry (2026-11-09 03:00:23Z) the lobby's
//! controller (task 9872001) wrote attempt 992, a reserve of 3 against its parent grain; the
//! client's first local codec request failed (EPIPE), so the directory holds only `attempt.json`,
//! `config.json` and `intent.json`. Startup recovery then refused, rightly, to read the absence as
//! a receipt, and the retained pending send and hold blocked the nightly checkpoint.
//!
//! **Statement.** `decide(facts, attempt, source, parent)` closes the attempt as never sent and
//! releases its hold exactly when
//! 1. the attempt is a reserve whose hold names it and is neither confirmed nor refused: closing
//!    it releases only an allowance that was never reserved;
//! 2. no process can still send under it: this controller holds no child, its custody gate is
//!    idle, and its unit's cgroup holds no process but the controller (`prove_prior_run_stopped`,
//!    observed now);
//! 3. no call bytes exist: every entry of the attempt directory is a regular file named in
//!    [`BEFORE_SEAL`], so neither `call.bin`, its staging file, the transaction signatures it is
//!    assembled from, nor any retry or outcome is present;
//! 4. the directory is the whole record: the kernel booted before the controller wrote the
//!    attempt's source, so no crash since could have dropped an entry the client had written (the
//!    client publishes files atomically but does not fsync them);
//! 5. the attempt is this controller's transition: its retained `intent.json`, if the client got
//!    that far, is byte-identical to the controller's `source-<id>.json`;
//! 6. nothing landed: the parent grain, read now through a signed read, is exactly the source's
//!    `before` (generation, status, remaining, reserved, and route when named) at the source's
//!    `expectedTargetRoot`. Any commit to the grain moves its generation and root.
//!
//! Otherwise it refuses by the clause's name and nothing changes. A close returns the
//! reconciliation-log entry (the attempt, its entries, the source's `before` and the parent read),
//! which the controller saves before it clears the pending send and the hold. The attempt
//! directory stays as evidence.
use serde_json::{json, Value};

/// The files a submit attempt holds before the client signs the transaction headers, in flow
/// order (`mini_sdk::flow`: retained inputs, observe, prepare, present).
pub(crate) const BEFORE_SEAL: &[&str] = &[
    "intent.json",
    "intent-source.bin",
    "config.json",
    "attempt.json",
    "intent.bin",
    "intent-signature.bin",
    "challenge.bin",
    "challenge.json",
    "observation-signatures.json",
    "observation-signatures.bin",
    "signed-observation.bin",
    "plan.bin",
    "plan.json",
];

/// What the controller observed, as the close reads it.
#[derive(Clone, Debug)]
pub(crate) struct Facts {
    /// Clause 2: `Err` names what could still send (a child, a busy gate, another process in the
    /// controller's cgroup).
    pub(crate) sender_stopped: Result<(), String>,
    /// Clause 4: kernel boot time, seconds since the epoch (`/proc/stat` `btime`).
    pub(crate) boot_epoch: u64,
    /// Clause 4: when the controller wrote `source-<id>.json`, whole seconds since the epoch.
    pub(crate) source_written_epoch: u64,
}

/// The pending attempt and its hold.
#[derive(Clone, Debug)]
pub(crate) struct Attempt {
    pub(crate) operation_id: u64,
    pub(crate) operation: String,
    /// Clause 1: the hold's `reserveAttempt` is this attempt's path.
    pub(crate) hold_names_attempt: bool,
    pub(crate) hold_confirmed: bool,
    pub(crate) hold_refused: bool,
    /// Clause 3: each directory entry, and whether it is a regular file.
    pub(crate) entries: Vec<(String, bool)>,
    /// Clause 5: `None` when the client never copied the intent; else whether its bytes equal the
    /// controller's source.
    pub(crate) intent_matches_source: Option<bool>,
}

pub(crate) fn decide(facts: &Facts, attempt: &Attempt, source: &Value, parent: &Value) -> Result<Value, String> {
    let refuse = |clause: &str, detail: String| Err(format!("refused: unsent-reserve: {clause}: {detail}"));
    if !matches!(attempt.operation.as_str(), "reserve" | "tool reserve")
        || !attempt.hold_names_attempt || attempt.hold_confirmed || attempt.hold_refused
    {
        return refuse("not-a-held-reserve", format!(
            "operation {:?} (hold names it: {}, confirmed: {}, refused: {}); only an unconfirmed reserve's own attempt closes here",
            attempt.operation, attempt.hold_names_attempt, attempt.hold_confirmed, attempt.hold_refused));
    }
    if let Err(why) = &facts.sender_stopped {
        return refuse("sender-not-stopped", why.clone());
    }
    let mut entries: Vec<&str> = Vec::new();
    for (name, regular) in &attempt.entries {
        if !regular || !BEFORE_SEAL.contains(&name.as_str()) {
            return refuse("call-may-exist", format!("the attempt holds {name:?}, which is not a regular pre-seal file"));
        }
        entries.push(name);
    }
    if facts.boot_epoch >= facts.source_written_epoch {
        return refuse("record-incomplete", format!(
            "the kernel booted at {} and the attempt began at {}; a crash since may have dropped an unsynced entry",
            facts.boot_epoch, facts.source_written_epoch));
    }
    if attempt.intent_matches_source == Some(false) {
        return refuse("intent-differs", "the attempt's retained intent is not the controller's source".into());
    }
    let before = source.pointer("/grain/before").ok_or("refused: unsent-reserve: source-unreadable: no grain.before")?;
    let expected_root = source.pointer("/grain/expectedTargetRoot").ok_or("refused: unsent-reserve: source-unreadable: no expectedTargetRoot")?;
    let grain = parent.get("grain").ok_or("refused: unsent-reserve: parent-unread: the signed read has no grain")?;
    let mut fields = vec!["generation", "status", "remaining", "reserved"];
    if before.get("route").is_some() {
        fields.push("route");
    }
    for field in fields {
        if before.get(field).is_none() || grain.get(field) != before.get(field) {
            return refuse("parent-moved", format!(
                "parent {field} is {} now, {} when the attempt was prepared",
                grain.get(field).unwrap_or(&Value::Null), before.get(field).unwrap_or(&Value::Null)));
        }
    }
    if parent.get("targetRoot") != Some(expected_root) {
        return refuse("parent-moved", "the parent's target root is not the attempt's expected root".into());
    }
    Ok(json!({"action":"close-unsent-reserve","stage":"before-signed-call",
        "operationId":attempt.operation_id.to_string(),"operation":attempt.operation,
        "entries":entries,"before":before,"parentNow":{"grain":grain,"targetRoot":parent.get("targetRoot")},
        "bootEpoch":facts.boot_epoch,"sourceWrittenEpoch":facts.source_written_epoch,
        "heldAllowanceReleased":true,"providerRequestRepeated":false,
        "basis":"no call bytes, sender stopped, record complete since boot, parent unchanged at the expected root"}))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn source() -> Value {
        json!({"grain":{"before":{"generation":"3","remaining":"20000","reserved":"0","status":"2"},
            "expectedTargetRoot":"970","operation":{"type":"reserve","amount":"3"}}})
    }
    fn parent() -> Value {
        json!({"grain":{"generation":"3","remaining":"20000","reserved":"0","status":"2"},"targetRoot":"970"})
    }
    fn facts() -> Facts {
        Facts { sender_stopped: Ok(()), boot_epoch: 1_793_337_035, source_written_epoch: 1_794_193_223 }
    }
    fn attempt() -> Attempt {
        Attempt { operation_id: 992, operation: "reserve".into(), hold_names_attempt: true,
            hold_confirmed: false, hold_refused: false,
            entries: ["attempt.json", "config.json", "intent.json"].map(|n| (n.to_owned(), true)).to_vec(),
            intent_matches_source: Some(true) }
    }
    fn refusal(facts: &Facts, attempt: &Attempt, source: &Value, parent: &Value) -> String {
        decide(facts, attempt, source, parent).unwrap_err()
    }

    #[test]
    fn the_demo_dry_attempt_closes_and_its_entry_names_the_evidence() {
        let entry = decide(&facts(), &attempt(), &source(), &parent()).unwrap();
        assert_eq!(entry["action"], "close-unsent-reserve");
        assert_eq!(entry["operationId"], "992");
        assert_eq!(entry["entries"], json!(["attempt.json", "config.json", "intent.json"]));
        assert_eq!(entry["parentNow"]["grain"]["generation"], "3");
        // A client that reached prepare but never signed the transaction is still never-sent.
        let mut prepared = attempt();
        for name in ["intent.bin", "intent-signature.bin", "challenge.bin", "challenge.json",
            "observation-signatures.json", "observation-signatures.bin", "signed-observation.bin", "plan.bin", "plan.json"] {
            prepared.entries.push((name.into(), true));
        }
        assert!(decide(&facts(), &prepared, &source(), &parent()).is_ok());
        // A client that died before copying the intent leaves nothing to compare.
        let bare = Attempt { entries: vec![], intent_matches_source: None, ..attempt() };
        assert!(decide(&facts(), &bare, &source(), &parent()).is_ok());
    }

    #[test]
    fn each_clause_refuses_on_its_own() {
        // 1: not a reserve, a hold naming another attempt, a confirmed or refused reserve.
        let settle = Attempt { operation: "settle".into(), ..attempt() };
        assert!(refusal(&facts(), &settle, &source(), &parent()).contains("not-a-held-reserve"));
        let elsewhere = Attempt { hold_names_attempt: false, ..attempt() };
        assert!(refusal(&facts(), &elsewhere, &source(), &parent()).contains("not-a-held-reserve"));
        let confirmed = Attempt { hold_confirmed: true, ..attempt() };
        assert!(refusal(&facts(), &confirmed, &source(), &parent()).contains("not-a-held-reserve"));
        let refused = Attempt { hold_refused: true, ..attempt() };
        assert!(refusal(&facts(), &refused, &source(), &parent()).contains("not-a-held-reserve"));
        // 2: something could still send.
        let live = Facts { sender_stopped: Err("controller cgroup holds pid 7".into()), ..facts() };
        assert!(refusal(&live, &attempt(), &source(), &parent()).contains("sender-not-stopped"));
        // 3: the call, its staging file, its signatures, an outcome, a retry, a directory.
        for (name, regular) in [("call.bin", true), (".call.bin.durable-1-0-00000000", true),
            ("transaction-signatures.bin", true), ("transaction-signatures.json", true),
            ("outcome.json", true), ("retry-0001.bin", true), ("replanned", false), ("plan.bin", false)] {
            let mut sealed = attempt();
            sealed.entries.push((name.into(), regular));
            assert!(refusal(&facts(), &sealed, &source(), &parent()).contains("call-may-exist"), "{name}");
        }
        // 4: a reboot after the attempt began.
        let rebooted = Facts { boot_epoch: 1_794_193_300, ..facts() };
        assert!(refusal(&rebooted, &attempt(), &source(), &parent()).contains("record-incomplete"));
        let same_second = Facts { boot_epoch: 1_794_193_223, ..facts() };
        assert!(refusal(&same_second, &attempt(), &source(), &parent()).contains("record-incomplete"));
        // 5: the retained intent is another transition.
        let other = Attempt { intent_matches_source: Some(false), ..attempt() };
        assert!(refusal(&facts(), &other, &source(), &parent()).contains("intent-differs"));
        // 6: each field of the parent moved, or its root did.
        for (field, value) in [("generation", "4"), ("status", "3"), ("remaining", "19997"), ("reserved", "3")] {
            let mut moved = parent();
            moved["grain"][field] = json!(value);
            assert!(refusal(&facts(), &attempt(), &source(), &moved).contains("parent-moved"), "{field}");
        }
        let mut rooted = parent();
        rooted["targetRoot"] = json!("971");
        assert!(refusal(&facts(), &attempt(), &source(), &rooted).contains("parent-moved"));
        let mut routed = source();
        routed["grain"]["before"]["route"] = json!("pool");
        assert!(refusal(&facts(), &attempt(), &routed, &parent()).contains("parent-moved"));
    }
}
