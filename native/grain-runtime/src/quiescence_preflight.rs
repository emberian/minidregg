//! `quiescence preflight`: would this controller restart retaining its state, judged from durable
//! state alone, before anything is stopped (the nightly checkpoint's first question).
//!
//! `quiescence inspect` takes the resident's lock and fresh stop proofs, so it can answer only once
//! the resident unit is stopped; the checkpoint stops it after the public entrance, the timers and
//! the roster. Its preflight (dregg-infra c7e9c24) asked `inspect` first and, on a box with a
//! running room resident, always read "resident driver is active": demo-dry skipped every nightly
//! from 2026-11-08 on.
//!
//! **Statement.** `verdict(active, retained)` is restartable exactly when nothing is active in this
//! controller (no owned worker, no running prompt, no live custody) and nothing is retained in its
//! journal or in the resident's durable files (`quiescence::retained` over
//! `quiescence::durable_resident_evidence`, the resident files read without the lock, with the same
//! path, ownership and schema checks). It is stricter than `inspect`'s `canRestartRetainingState`,
//! which also admits a restart with retained uncertainty: a checkpoint that would stop the box over
//! retained work skips instead.
//!
//! **The window.** The answer is a snapshot. Between it and the checkpoint's own `quiesce` (after
//! the activators, the entrance and the resident unit stop) the resident may admit a prompt and the
//! controller may start work. That `quiesce`, lock-held and with stop proofs, stays the authority; a
//! preflight only keeps a night with already-retained work from stopping anything.
use serde_json::{json, Value};

pub(crate) const TYPE: &str = "mini-grain-quiescence-preflight-v1";

pub(crate) fn verdict(active: &[&str], retained: &[&str]) -> Value {
    json!({"type":TYPE,"restartable":active.is_empty() && retained.is_empty(),"active":active,"retained":retained})
}

impl crate::Runtime {
    pub(crate) fn quiescence_preflight(&self, resident: Option<&std::path::Path>) -> crate::Result<Value> {
        let evidence = crate::quiescence::durable_resident_evidence(&self.config, resident)?;
        let active = self.quiescence_active();
        let retained = crate::quiescence::retained(&self.journal, evidence);
        Ok(verdict(&active, &retained))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::quiescence::{retained, ResidentEvidence};

    fn stopped(field: usize) -> ResidentEvidence {
        let f = |i| field == i;
        ResidentEvidence::Stopped { prompt_pending: f(0), return_pending: f(1), queued_requests: f(2),
            started_request: f(3), maintenance_pending: f(4) }
    }

    #[test]
    fn restartable_only_with_nothing_active_or_retained_anywhere() {
        let journal = crate::Journal::fresh(json!({}));
        let clean = retained(&journal, stopped(usize::MAX));
        assert_eq!(verdict(&[], &clean)["restartable"], true);
        assert_eq!(verdict(&["prompt_active"], &clean)["restartable"], false);
        for field in 0..5 {
            let held = retained(&journal, stopped(field));
            assert_eq!(held.len(), 1, "{field}");
            assert_eq!(verdict(&[], &held)["restartable"], false);
        }
        let mut pending = crate::Journal::fresh(json!({}));
        pending.hard_reconnect_pending = true;
        assert_eq!(verdict(&[], &retained(&pending, stopped(usize::MAX)))["restartable"], false);
        assert_eq!(verdict(&[], &retained(&journal, ResidentEvidence::NotConfigured))["restartable"], true);
    }
}
