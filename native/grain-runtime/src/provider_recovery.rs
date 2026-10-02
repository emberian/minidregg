//! Resume only the financial tail of a response already delivered to the local
//! client. Exact replay custody is required; an uncertain send or an undelivered
//! response stays held. No request or prompt is repeated.
use super::*;

fn delivered(attempt: &ProviderAttempt, replay: &ProviderReplay) -> bool {
    attempt.send_started
        && attempt.outcome.as_deref()
            == Some(format!("received:{}:{}", replay.status, replay.content_type).as_str())
        && attempt.prompt_operation_id == replay.prompt_operation_id
        && attempt.parent_generation == replay.parent_generation
        && attempt.request_path == replay.request_path
        && attempt.request_bytes == replay.request_bytes
        && attempt.request_sha256 == replay.request_sha256
        && attempt.outcome_path.as_ref() == Some(&replay.response_path)
        && attempt.outcome_bytes == Some(replay.response_bytes)
        && attempt.outcome_sha256.as_ref() == Some(&replay.response_sha256)
        && attempt.response_status == Some(replay.status)
        && attempt.response_content_type.as_ref() == Some(&replay.content_type)
        && attempt.response_headers_path == replay.response_headers_path
        && attempt.response_headers_bytes == replay.response_headers_bytes
        && attempt.response_headers_sha256 == replay.response_headers_sha256
        && attempt.meter_report_path.is_some()
        && attempt.meter_report_path == replay.meter_report_path
        && attempt.meter_report_sha256.is_some()
        && attempt.meter_report_sha256 == replay.meter_report_sha256
        && attempt.metered_charge.is_some()
        && attempt.metered_charge == replay.metered_charge
}

impl Runtime {
    pub(super) fn lookup_provider_settlement(
        &mut self,
        attempt: &ProviderAttempt,
    ) -> Result<ProviderSettlement> {
        let settled = self.verified_provider_settlement(attempt)?;
        let retry_result = next_retry_json(&settled.attempt)?;
        let mut args = vec![
            "retry",
            "--attempt",
            settled
                .attempt
                .to_str()
                .ok_or("provider settlement attempt path UTF-8")?,
            "--mode",
            "lookup",
        ];
        if let Some(socket) = &self.config.host_socket {
            args.extend(["--socket", socket.to_str().ok_or("Host socket path UTF-8")?]);
        }
        self.command_output(&self.config.mini, &args)?;
        let lookup: Value = serde_json::from_slice(&bounded_regular_file(&retry_result, 131_072)?)
            .map_err(|e| format!("provider settlement lookup: {e}"))?;
        if lookup.get("type").and_then(Value::as_str) != Some("confirmed")
            || !matches!(
                lookup.get("confirmation").and_then(Value::as_str),
                Some("installed" | "replayed")
            )
            || ReserveAnchor::from_confirmed(&lookup)? != settled.receipt
        {
            return Err("provider settlement is not confirmed on the current native image".into());
        }
        Ok(settled)
    }

    pub(super) fn require_delivered_provider_response(&self) -> Result<()> {
        let attempt = self
            .journal
            .provider_attempt
            .as_ref()
            .ok_or("no provider response to recover")?;
        if !self
            .journal
            .provider_replays
            .iter()
            .any(|replay| delivered(attempt, replay))
        {
            return Err("provider response lacks exact durable local delivery evidence".into());
        }
        // Revalidate actual retained bytes and the source-owned quote, not only
        // the duplicated metadata. The shared settlement path proves the native
        // hold or exact prior settlement receipt on the current image.
        if self.journal.provider_hold.is_some() {
            self.validated_metered_charge(attempt)?;
        } else {
            self.verified_provider_settlement(attempt)?;
        }
        if let (Some(path), Some(bytes), Some(hash)) = (
            &attempt.response_headers_path,
            attempt.response_headers_bytes,
            &attempt.response_headers_sha256,
        ) {
            let headers = retained_exact(path, bytes, hash, 131_072)?;
            let metadata = provider::response_headers(&headers)?;
            if Some(metadata.0) != attempt.response_status
                || Some(metadata.1) != attempt.response_content_type
            {
                return Err("delivered provider headers differ from response metadata".into());
            }
        } else if attempt.response_headers_path.is_some()
            || attempt.response_headers_bytes.is_some()
            || attempt.response_headers_sha256.is_some()
        {
            return Err("delivered provider headers have incomplete custody".into());
        }
        Ok(())
    }

    pub(super) fn recover_delivered_provider_response(&mut self) -> Result<()> {
        let Some(attempt) = self.journal.provider_attempt.as_ref() else {
            return Ok(());
        };
        if self.startup_recovery_active
            || self.child.is_some()
            || self.journal.child.is_some()
            || self.journal.pending.is_some()
            || self.journal.tool_pending.is_some()
            || self.journal.provider_pending.is_some()
            || self.journal.dispatch_pending.is_some()
            || !self
                .journal
                .provider_replays
                .iter()
                .any(|replay| delivered(attempt, replay))
        {
            return Ok(());
        }
        // Explicit ordinary recovery proves all previous local senders stopped.
        // Existing parent/session/external uncertainty remains unchanged; this
        // only settles the independently known delivered provider response.
        self.reconcile_provider_evidence(true)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn complete_delivery_requires_every_replay_binding() {
        let replay: ProviderReplay =
            serde_json::from_value(json!({"promptOperationId":2,"parentGeneration":"1",
            "requestPath":"/request","requestBytes":3,"requestSha256":"ab".repeat(32),
            "responsePath":"/response","responseBytes":4,"responseSha256":"cd".repeat(32),
            "status":200,"contentType":"application/json","meterReportPath":"/quote",
            "meterReportSha256":"ef".repeat(32),"meteredCharge":"3"}))
            .unwrap();
        let attempt:ProviderAttempt=serde_json::from_value(json!({"id":1,"promptOperationId":2,"parentGeneration":"1","model":"fixture",
            "requestPath":"/request","requestBytes":3,"requestSha256":"ab".repeat(32),
            "sendStarted":true,"outcomePath":"/response","outcomeBytes":4,"outcomeSha256":"cd".repeat(32),
            "outcome":"received:200:application/json","responseStatus":200,"responseContentType":"application/json",
            "meterReportPath":"/quote","meterReportSha256":"ef".repeat(32),"meteredCharge":"3",
            "route":{"provider":"fixture","endpoint":"http://127.0.0.1:1234/v1/chat/completions","credential":"homelab"}})).unwrap();
        assert!(delivered(&attempt, &replay));
        let original = serde_json::to_value(&replay).unwrap();
        for (field, value) in original.as_object().unwrap() {
            let mut changed = original.clone();
            changed[field] = match value {
                Value::Null => json!("introduced"),
                Value::Number(_) => json!(999),
                _ => json!("changed"),
            };
            // Even optional evidence present on only one side cannot match.
            if let Ok(changed) = serde_json::from_value::<ProviderReplay>(changed) {
                assert!(!delivered(&attempt, &changed), "altered {field}");
            }
        }
        for kind in [None, Some("uncertain:lost"), Some("not-sent:refused")] {
            let mut changed = attempt.clone();
            changed.outcome = kind.map(str::to_owned);
            assert!(!delivered(&changed, &replay));
        }
        let mut changed = attempt;
        changed.send_started = false;
        assert!(!delivered(&changed, &replay));
    }
}
