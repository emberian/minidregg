//! Retire a completed, definitively unsent refusal through the same signed
//! origin proof used by the operator command. This never retries a prompt.
use super::*;

fn eligible(attempt: &ProviderAttempt, hold: &HeldCharge) -> bool {
    !attempt.send_started
        && attempt.outcome.is_none()
        && attempt.outcome_path.is_none()
        && attempt.outcome_bytes.is_none()
        && attempt.outcome_sha256.is_none()
        && !hold.reserve_confirmed
        && (hold.reserve_refused || hold.reserve_attempt.is_none())
}

fn retained_reason(config: &Config, hold: &HeldCharge) -> Result<Value> {
    let Some(path) = hold.reserve_attempt.as_ref() else {
        return Ok(json!({"type":"not-submitted","reason":"reservation-not-submitted"}));
    };
    let refusal = match fs::symlink_metadata(path.join("outcome.json")) {
        Ok(_) => serde_json::from_slice::<Value>(&bounded_regular_file(
            &path.join("outcome.json"),
            131_072,
        )?)
        .map_err(|e| e.to_string())?,
        Err(e) if e.kind() == io::ErrorKind::NotFound => {
            inspected_pre_submit_refusal(config, path)?
                .ok_or("definite provider refusal evidence absent")?
        }
        Err(e) => return Err(format!("provider refusal evidence: {e}")),
    };
    if refusal.get("type").and_then(Value::as_str) != Some("refused") {
        return Err("provider retirement requires retained native refusal".into());
    }
    let reason = refusal
        .get("reason")
        .and_then(Value::as_str)
        .ok_or("provider refusal reason absent")?;
    if reason.is_empty()
        || reason.len() > 64
        || !reason.bytes().all(|b| b.is_ascii_lowercase() || b == b'-')
    {
        return Err("provider refusal reason invalid".into());
    }
    Ok(json!({"type":"native-refusal","reason":reason,"attempt":path}))
}

impl Runtime {
    pub(super) fn refused_provider_for_prompt(&self, prompt: u64) -> bool {
        matches!((&self.journal.provider_attempt,&self.journal.provider_hold), (Some(attempt),Some(hold))
            if eligible(attempt,hold) && attempt.prompt_operation_id==prompt
                && self.journal.prompt_witness.as_ref().and_then(|w|w.pointer("/before/generation"))
                    .and_then(Value::as_str)==Some(attempt.parent_generation.as_str()))
    }

    pub(super) fn retire_refused_provider_request(&mut self) -> Result<()> {
        let (Some(attempt), Some(hold)) = (
            self.journal.provider_attempt.as_ref(),
            self.journal.provider_hold.as_ref(),
        ) else {
            return Ok(());
        };
        if !eligible(attempt, hold)
            || self.child.is_some()
            || self.journal.child.is_some()
            || self.prompt_active
            || self.provider_lease.is_some()
            || !self.custody_gate.is_idle()
            || self.current_pgid.load(Ordering::SeqCst) > 0
            || self.journal.pending.is_some()
            || self.journal.tool_pending.is_some()
            || self.journal.provider_pending.is_some()
            || self.journal.dispatch_pending.is_some()
            || self.journal.tool_hold.is_some()
            || self.journal.dispatch_hold.is_some()
            || self.journal.dispatch_attempt.is_some()
            || self.journal.settlement_due.is_some()
            || self.journal.foreground_attempt.is_some()
            || self.journal.application_api_attempt.is_some()
        {
            return Ok(());
        }
        let refusal = retained_reason(&self.config, hold)?;
        // The shared method checks exact request bytes, no possible reserve or
        // send, and freshly signed idle coordinates at the exact held root.
        self.abort_refused_provider_request_with(true, Some(refusal))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    fn fixture() -> (ProviderAttempt, HeldCharge) {
        let attempt:ProviderAttempt=serde_json::from_value(json!({
            "id":1,"promptOperationId":2,"parentGeneration":"1","model":"fixture",
            "requestPath":"/request","requestBytes":3,"requestSha256":"ab".repeat(32),
            "sendStarted":false,"outcomePath":null,"outcomeBytes":null,"outcomeSha256":null,"outcome":null,
            "route":{"provider":"fixture","endpoint":"http://127.0.0.1:1234/v1/chat/completions","credential":"homelab"}
        })).unwrap();
        let hold:HeldCharge=serde_json::from_value(json!({"reserve":"3","charge":"0","beforeGeneration":"1",
            "beforeTargetRoot":"old","reserveAttempt":"/attempt","reserveConfirmed":false,"reserveRefused":true,
            "reserveBoundary":null})).unwrap();
        (attempt, hold)
    }
    #[test]
    fn retirement_never_accepts_confirmed_unknown_or_send_possible_attempt() {
        let (attempt, hold) = fixture();
        assert!(eligible(&attempt, &hold));
        let mut changed = attempt.clone();
        changed.send_started = true;
        assert!(!eligible(&changed, &hold));
        changed = attempt.clone();
        changed.outcome = Some("uncertain".into());
        assert!(!eligible(&changed, &hold));
        changed = attempt.clone();
        changed.outcome_path = Some("/response".into());
        assert!(!eligible(&changed, &hold));
        let mut changed = hold.clone();
        changed.reserve_confirmed = true;
        assert!(!eligible(&attempt, &changed));
        changed = hold.clone();
        changed.reserve_refused = false;
        assert!(!eligible(&attempt, &changed));
        changed.reserve_attempt = None;
        assert!(eligible(&attempt, &changed));
    }
}
