//! No-generation readiness through the same confined ACP lifecycle as a prompt.
//! The accompanying main patch adds a mode to Runtime::hermes, not another launcher.
use crate::*;

#[derive(Clone, Copy, Debug)]
pub(crate) enum Invocation<'a> {
    Prompt(&'a str),
    ResidentPrompt{prompt:&'a str,resident_id:&'a str,digest:&'a str},
    Verify,
}

impl<'a> Invocation<'a> {
    pub(crate) fn prompt(self) -> Option<&'a str> {
        match self { Self::Prompt(text) | Self::ResidentPrompt{prompt:text,..} => Some(text), Self::Verify => None }
    }
    pub(crate) fn resident_identity(self)->Option<(&'a str,&'a str)> {
        match self {Self::ResidentPrompt{resident_id,digest,..}=>Some((resident_id,digest)),_=>None}
    }
    pub(crate) fn is_prompt(self) -> bool { self.prompt().is_some() }
    pub(crate) fn charge<'b>(self, configured: &'b str) -> &'b str {
        if self.is_prompt() { configured } else { "0" }
    }
    pub(crate) fn label(self) -> &'static str {
        if self.is_prompt() { "hermes-acp prompt" } else { "hermes-acp verify-session" }
    }
}

fn require_retained(session: &HermesSession) -> Result<()> {
    if session.pending_prompt || session.retention_issue.is_some() || session.state_fingerprint.is_none() {
        return Err("verify-session requires a retained, reconciled conversation; inspect/recover the pending turn first".into());
    }
    Ok(())
}

impl Runtime {
    pub(crate) fn verify_hermes_session(&mut self, input: &Receiver<Input>) -> Result<Value> {
        // Admin socket alone is insufficient: only the registered controller
        // MainPID may own the native lease and launch/reap the confined worker.
        prove_controller_unit(&self.config.task)?;
        if self.needs_startup_recovery() || self.child.is_some()
            || self.journal.foreground_attempt.is_some()
            || self.journal.application_api_attempt.is_some()
            || self.journal.prompt_witness.is_some()
            || !quiescence::retained(&self.journal, quiescence::ResidentEvidence::NotConfigured).is_empty()
        {
            return Err("verify-session requires a quiescent, fully reconciled task".into());
        }
        let Some(previous) = self.journal.hermes_session.clone() else {
            return Ok(json!({"type":"mini-hermes-session-readiness-v1", "ready":true,
                "retainedSession":false, "loadVerified":false, "workerStarted":false,
                "nativeLeaseChanged":false, "modelRequests":0, "parentCharge":"0"}));
        };
        require_retained(&previous)?;
        let spec = self.config.commands.iter().find(|c| c.name == "hermes-acp")
            .ok_or("verify-session has no configured Hermes command")?;
        if !spec.systemd_scope {
            return Err("verify-session requires the registered scoped worker".into());
        }
        // Scope/counters identify earlier actual provider work. Verification
        // cannot reset them, even though the worker gets a fresh inactive token.
        let replay_before = serde_json::to_value(&self.journal.provider_replays)
            .map_err(|e| e.to_string())?;
        let request_count_before = self.journal.provider_prompt_requests;
        let parent_before = self.query()?;
        let remaining_before = parent_before.pointer("/grain/remaining").and_then(Value::as_str)
            .ok_or("verify-session signed parent balance absent")?.to_owned();
        if parent_before.pointer("/grain/reserved").and_then(Value::as_str) != Some("0") {
            return Err("verify-session signed parent already has a reservation".into());
        }
        let temporary_attach = self.journal.connection == Connection::Detached;
        if temporary_attach { self.attach(true)?; }

        let verification = self.hermes_session(Invocation::Verify, input);
        // The normal disconnect intentionally keeps soft residents attached.
        // Use the existing native mode transition before actual detach. Never
        // overwrite journal bits to pretend a native transition occurred.
        let connection_changed = temporary_attach && self.journal.connection == Connection::Hard;
        let restored = if temporary_attach && !connection_changed {
            if self.journal.connection == Connection::Detached { Ok(()) }
            else { self.attach(false).and_then(|()| self.disconnect()) }
        } else { Ok(()) };
        if let Err(error) = restored {
            return Err(format!("verify-session result={verification:?}; temporary attachment restoration failed: {error}"));
        }
        verification?;
        let parent_after = self.query()?;
        if parent_after.pointer("/grain/reserved").and_then(Value::as_str) != Some("0")
            || parent_after.pointer("/grain/remaining").and_then(Value::as_str) != Some(remaining_before.as_str())
        {
            return Err("verify-session did not finish with unchanged signed parent allowance and zero reservation".into());
        }
        if self.journal.provider_prompt_requests != request_count_before
            || serde_json::to_value(&self.journal.provider_replays).map_err(|e| e.to_string())? != replay_before
        {
            return Err("verify-session changed retained provider request/replay evidence".into());
        }
        let current = self.journal.hermes_session.as_ref().ok_or("verified session disappeared")?;
        require_retained(current)?;
        if current.id != previous.id || !current.load_verified {
            return Err("verify-session did not load the exact retained conversation".into());
        }
        Ok(json!({"type":"mini-hermes-session-readiness-v1", "ready":true,
            "retainedSession":true, "sessionId":current.id, "loadVerified":true,
            "stateFingerprint":current.state_fingerprint, "workerStarted":true,
            "nativeLeaseChanged":true, "temporaryAttachment":temporary_attach,
            "connectionChanged":connection_changed, "connection":self.journal.connection,
            "parentBeforeRoot":parent_before.get("targetRoot"), "parentAfterRoot":parent_after.get("targetRoot"),
            "parentRemaining":remaining_before, "parentReserved":"0",
            "modelRequests":0, "parentCharge":"0"}))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn readiness_cannot_bless_an_interrupted_or_unretained_turn() {
        let mut session = HermesSession { id:"retained-id".into(), workspace:"/workspace".into(),
            load_verified:false, state_fingerprint:Some("closed-db-fingerprint".into()),
            retention_issue:None, pending_prompt:false };
        assert!(require_retained(&session).is_ok());
        session.pending_prompt = true;
        assert!(require_retained(&session).is_err());
        session.pending_prompt = false;
        session.retention_issue = Some("missing database".into());
        assert!(require_retained(&session).is_err());
        session.retention_issue = None;
        session.state_fingerprint = None;
        assert!(require_retained(&session).is_err());
    }
    #[test]
    fn confirmed_provider_settlement_history_is_not_an_active_marker() {
        let mut journal=Journal::fresh(json!({}));
        journal.provider_settlement=Some(serde_json::from_value(json!({
            "providerAttemptId":96,"operationId":111,"operation":"provider settle",
            "attempt":"/private/attempt-111","charge":"2364","sourceSha256":"a".repeat(64),
            "callSha256":"b".repeat(64),"outcomePath":"/private/attempt-111/outcome.json",
            "outcomeSha256":"c".repeat(64),
            "receipt":{"transactionId":"1","eventId":"2","acceptedCount":"50","worldRoot":"3"}
        })).unwrap());
        assert!(quiescence::retained(&journal,quiescence::ResidentEvidence::NotConfigured).is_empty());
        journal.unresolved_external.push("possible provider send".into());
        assert!(!quiescence::retained(&journal,quiescence::ResidentEvidence::NotConfigured).is_empty());
    }

}
