//! The typed close of a prompt witness that outlived its allowance (`reconcile prompt-witness`).
//!
//! A prompt witness is the parent grain's state recorded when a work allowance was reserved for a
//! prompt (`mark_hold` then `reserve`). It is cleared where that allowance is settled
//! (`reconcile_hold_with`), at disconnect, at the end of a Hermes session and in `recover`'s fenced
//! branch. A controller whose allowance ends any other way keeps the witness with nothing that can
//! clear it: on demo-dry (2026-11-07) the lobby's controller (task 9872001) retained only
//! `prompt_witness`, `reconcile parent audited` found no held allowance, `recover` was not an
//! action, and the held work blocked the nightly checkpoint for 40 hours.
//!
//! **Statement.** `decide(facts, witness, parent)` closes the witness exactly when
//! 1. no allowance is held under any authority (parent, tool, provider, dispatch) and no settlement
//!    is due: the witness names no allowance this controller can still settle;
//! 2. nothing can still act on the witnessed reservation: no live worker, no pending send, no
//!    unresolved custody attempt, no running prompt and no Hermes prompt pending;
//! 3. the parent grain, read now, is not the witnessed reservation: it is not reserved (status 3
//!    or 4), or its generation is not the witnessed one.
//!
//! Otherwise it refuses by name and the witness stays. A close returns the reconciliation-log entry
//! (the witness and the parent state it was judged against), which the controller records before it
//! drops the witness.
use serde_json::{json, Value};

/// What the controller holds, as the close reads it.
#[derive(Clone, Debug, Default)]
pub(crate) struct Facts {
    /// Clause 1: any parent, tool, provider or dispatch hold, or a settlement due.
    pub(crate) allowance_held: bool,
    /// Clause 2: a live worker (process or journal child), a pending send of any authority, or an
    /// unresolved provider, dispatch, room, workspace or foreground attempt.
    pub(crate) custody_open: bool,
    /// Clause 2: a prompt runs now, or the Hermes session holds one pending.
    pub(crate) prompt_live: bool,
}

pub(crate) fn decide(facts: &Facts, witness: &Value, parent: &Value) -> Result<Value, String> {
    if facts.allowance_held {
        return Err("an allowance is still held: settle it (`reconcile parent audited` or the authority's own) and that clears the witness".into());
    }
    if facts.custody_open {
        return Err("a worker, pending send or custody attempt is unresolved; reconcile it first".into());
    }
    if facts.prompt_live {
        return Err("a prompt still runs or is pending; the witness is live".into());
    }
    let status = parent.get("status").and_then(Value::as_str);
    let generation = parent.get("generation");
    let witnessed = witness.get("before").and_then(|before| before.get("generation"));
    let reserved = matches!(status, Some("3" | "4"));
    if reserved && generation.is_some() && generation == witnessed {
        return Err("the parent grain is still reserved at the witnessed generation, with no hold recorded; report it, never close it".into());
    }
    Ok(json!({"action":"close-prompt-witness","witness":witness,
        "parentNow":{"status":status,"generation":generation},
        "reason":"no held allowance, no live custody, and the parent is not the witnessed reservation"}))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn witness() -> Value { json!({"task":"9872001","before":{"generation":"7","status":"3"}}) }

    #[test]
    fn an_orphaned_witness_closes_and_its_entry_names_both_states() {
        let entry = decide(&Facts::default(), &witness(), &json!({"status":"2","generation":"8"})).unwrap();
        assert_eq!(entry["action"], "close-prompt-witness");
        assert_eq!(entry["witness"]["before"]["generation"], "7");
        assert_eq!(entry["parentNow"]["generation"], "8");
        // A parent reserved again, for a later generation, is not the witnessed reservation.
        assert!(decide(&Facts::default(), &witness(), &json!({"status":"4","generation":"9"})).is_ok());
    }

    #[test]
    fn each_clause_refuses_on_its_own() {
        let released = json!({"status":"2","generation":"8"});
        let held = Facts { allowance_held: true, ..Facts::default() };
        assert!(decide(&held, &witness(), &released).unwrap_err().contains("allowance is still held"));
        let custody = Facts { custody_open: true, ..Facts::default() };
        assert!(decide(&custody, &witness(), &released).unwrap_err().contains("unresolved"));
        let live = Facts { prompt_live: true, ..Facts::default() };
        assert!(decide(&live, &witness(), &released).unwrap_err().contains("still runs"));
        for status in ["3", "4"] {
            let same = json!({"status":status,"generation":"7"});
            assert!(decide(&Facts::default(), &witness(), &same).unwrap_err().contains("still reserved"));
        }
    }
}
