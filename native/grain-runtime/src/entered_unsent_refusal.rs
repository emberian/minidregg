//! The pre-admission refusal of a resident prompt that entered native preparation but whose only
//! native act, its parent work reserve, was closed as never sent (`resident refuse-unadmitted ID
//! SHA` on an entered prompt).
//!
//! A resident prompt is entered (`resident-entered-ID.json`, the fence before its first possible
//! native effect), then the controller prepares locally (worker profile, the local provider
//! gateway, launcher proofs: no Mini call, no model request), reserves the parent's work allowance,
//! and only after that reserve succeeds records its admission (`resident-origin-id-ID.json`). An
//! entered prompt with no admission therefore had at most one native effect: that reserve. On
//! demo-dry (2026-11-09 03:00:23Z) prompt 384490e0… entered, its reserve (operation 992) failed
//! before the custody client wrote a call, startup recovery closed it as never sent
//! (`unsent_reserve_close`), and the resident held the prompt pending with no way to close it:
//! `refuse-unadmitted` refused every entered prompt.
//!
//! **Statement.** `decide(facts)` lets the controller record the prompt's pre-admission refusal
//! (no effects, no model request) exactly when
//! 1. the prompt is entered and not admitted: no admitted origin, and the controller's current
//!    prompt origin is not this prompt;
//! 2. nothing is held on the parent and nothing is live: no parent pending send, no parent hold,
//!    no settlement due, no child, no running or pending prompt;
//! 3. the prompt's reserve is identified, by either
//!    a. its binding: `resident-reserve-ID.json`, written by the controller before the reserve's
//!       source (from 2026-11-09), names the reserve's operation id; or
//!    b. time order, for a prompt entered before bindings existed:
//!       - an anchor exists: an operation whose files survive, dated before the entry, with an id
//!         above every id compaction moved to `history.jsonl`, so nothing after the entry was
//!         compacted away;
//!       - every id from the anchor to the next unallocated id is a surviving operation or a
//!         recorded reconciliation decision, so no operation is unaccounted for;
//!       - among the surviving operations dated at or after the entry there is exactly one
//!         reserve transition (of any authority), and it is the prompt's reserve;
//! 4. that reserve is closed as never sent: the reconciliation log holds its
//!    `close-unsent-reserve` entry.
//!
//! Otherwise it refuses by the link's name, and nothing is written. An accepted refusal returns the
//! reconciliation-log entry, which the controller saves before it writes the refusal record.
use std::collections::{BTreeMap, BTreeSet};

use serde_json::{json, Value};

/// One surviving operation, as its files show it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Operation {
    /// Earliest modification time of its files, nanoseconds since the epoch.
    pub(crate) time_ns: i128,
    /// It wrote a transition source, and the source's operation is a reserve.
    pub(crate) reserve: bool,
}

#[derive(Clone, Debug, Default)]
pub(crate) struct Facts {
    pub(crate) entered_ns: i128,
    /// Clause 1.
    pub(crate) admitted: bool,
    /// Clause 2: `Some` names what is held or live.
    pub(crate) held: Option<String>,
    /// Clause 3a.
    pub(crate) bound_reserve: Option<u64>,
    /// Clause 3b: every surviving operation, by id.
    pub(crate) operations: BTreeMap<u64, Operation>,
    /// Clause 3b: the highest id in `history.jsonl`, if any.
    pub(crate) compacted_max: Option<u64>,
    /// Clause 3b: reconciliation decision ids.
    pub(crate) decisions: BTreeSet<u64>,
    /// Clause 3b: the controller's next unallocated operation id.
    pub(crate) next_operation_id: u64,
    /// Clause 4: operation ids the reconciliation log closed as never sent.
    pub(crate) closed_unsent: BTreeSet<u64>,
}

pub(crate) fn decide(id: &str, facts: &Facts) -> Result<Value, String> {
    let refuse = |link: &str, detail: String| Err(format!("refused: entered-unsent: {link}: {detail}"));
    if facts.admitted {
        return refuse("admitted", "the prompt has an admitted origin".into());
    }
    if let Some(what) = &facts.held {
        return refuse("held", what.clone());
    }
    let (reserve, basis) = match facts.bound_reserve {
        Some(reserve) => (reserve, json!({"binding":reserve.to_string()})),
        None => {
            let compacted = facts.compacted_max;
            let anchor = facts.operations.iter().rev()
                .find(|(op, o)| o.time_ns < facts.entered_ns && compacted.is_none_or(|max| **op > max))
                .map(|(op, _)| *op);
            let Some(anchor) = anchor else {
                return refuse("evidence-compacted", format!(
                    "no surviving operation before the entry lies above the compacted ids (history up to {compacted:?})"));
            };
            if let Some(missing) = (anchor + 1..facts.next_operation_id)
                .find(|op| !facts.operations.contains_key(op) && !facts.decisions.contains(op))
            {
                return refuse("evidence-missing", format!("operation {missing} has no surviving files and no recorded decision"));
            }
            let reserves: Vec<u64> = facts.operations.range(anchor + 1..)
                .filter(|(_, o)| o.time_ns >= facts.entered_ns && o.reserve)
                .map(|(op, _)| *op).collect();
            if reserves.len() != 1 {
                return refuse("one-reserve", format!("{} reserves after the entry ({reserves:?})", reserves.len()));
            }
            (reserves[0], json!({"timeOrder":{"anchor":anchor.to_string(),"compactedMax":compacted.map(|v| v.to_string()),
                "enteredNs":facts.entered_ns.to_string()}}))
        }
    };
    if !facts.closed_unsent.contains(&reserve) {
        return refuse("reserve-not-closed", format!("reserve {reserve} has no close-unsent-reserve entry"));
    }
    Ok(json!({"action":"refuse-entered-unsent-prompt","residentPromptId":id,"reserveOperationId":reserve.to_string(),
        "basis":basis,"effects":"none","modelRequests":0,
        "reason":"entered, never admitted; its only native act, the work reserve, was closed as never sent"}))
}

#[cfg(test)]
mod tests {
    use super::*;

    const E: i128 = 1_000;
    fn op(time_ns: i128, reserve: bool) -> Operation { Operation { time_ns, reserve } }
    /// demo-dry: history to 972; 975/983/989 transitions and 974..988 reads before the entry; 990/991
    /// reads and 992 the reserve after it; 993..998 reads; 999 the close decision; next id 1001.
    fn demo() -> Facts {
        let mut operations = BTreeMap::new();
        for id in 973..=989 { operations.insert(id, op(E - 10, matches!(id, 975 | 983 | 989))); }
        for id in [990, 991] { operations.insert(id, op(E + 1, false)); }
        operations.insert(992, op(E + 2, true));
        for id in 993..=998 { operations.insert(id, op(E + 100, false)); }
        Facts { entered_ns: E, operations, compacted_max: Some(972), decisions: [999, 1000].into(),
            next_operation_id: 1001, closed_unsent: [992].into(), ..Facts::default() }
    }

    #[test]
    fn the_demo_dry_prompt_is_refused_before_admission_by_time_order_and_by_binding() {
        let entry = decide("p", &demo()).unwrap();
        assert_eq!(entry["reserveOperationId"], "992");
        assert_eq!(entry["basis"]["timeOrder"]["anchor"], "989");
        let bound = Facts { bound_reserve: Some(992), operations: BTreeMap::new(), compacted_max: Some(5000), ..demo() };
        assert_eq!(decide("p", &bound).unwrap()["basis"]["binding"], "992");
    }

    #[test]
    fn each_link_refuses_on_its_own() {
        let refusal = |facts: &Facts| decide("p", facts).unwrap_err();
        assert!(refusal(&Facts { admitted: true, ..demo() }).contains("admitted"));
        assert!(refusal(&Facts { held: Some("parent hold".into()), ..demo() }).contains("held"));
        // Compaction reached past the entry: no anchor above the compacted ids.
        assert!(refusal(&Facts { compacted_max: Some(995), ..demo() }).contains("evidence-compacted"));
        // An operation after the anchor vanished.
        let mut gap = demo();
        gap.operations.remove(&990);
        assert!(refusal(&gap).contains("evidence-missing"));
        let mut undecided = demo();
        undecided.decisions.remove(&999);
        assert!(refusal(&undecided).contains("evidence-missing"));
        // A second reserve after the entry, or none.
        let mut second = demo();
        second.operations.insert(995, op(E + 100, true));
        assert!(refusal(&second).contains("one-reserve"));
        let mut none = demo();
        none.operations.insert(992, op(E + 2, false));
        assert!(refusal(&none).contains("one-reserve"));
        // The reserve was not closed as never sent.
        assert!(refusal(&Facts { closed_unsent: BTreeSet::new(), ..demo() }).contains("reserve-not-closed"));
        let bound = Facts { bound_reserve: Some(993), ..demo() };
        assert!(refusal(&bound).contains("reserve-not-closed"));
    }
}
