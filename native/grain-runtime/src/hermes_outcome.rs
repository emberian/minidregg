//! A worker's ordinary end-turn response is not proof a managed model ran.
//! Require the current prompt's retained, metered, settled provider response.
use crate::*;

/// Classification only: the controller separately drains journals and reaps.
pub(crate) fn typed_failure(error: &Value) -> Option<Value> {
    let data=error.get("data")?;
    let reason=data.get("reason")?.as_str()?;
    let detail=data.get("detail")?.as_str()?;
    if error.get("code")?.as_i64()? != -32003
        || data.get("type")?.as_str()? != "mini-hermes-turn-failure-v1"
        || reason.is_empty() || reason.len()>96
        || !reason.bytes().all(|c|c.is_ascii_lowercase() || c.is_ascii_digit() || b"_:-".contains(&c))
        || detail.len()>4096
        || !matches!(data.get("retryable"),Some(Value::Bool(_)|Value::Null)) { return None; }
    Some(json!({"miniTurnFailure":error}))
}
pub(crate) fn failure(value: &Value) -> Option<&Value> { value.get("miniTurnFailure") }

fn terminal_blockers(journal: &Journal) -> Vec<&'static str> {
    crate::quiescence::retained(journal,crate::quiescence::ResidentEvidence::NotConfigured)
        .into_iter().filter(|name| !matches!(*name,
            "child"|"parent_hold"|"prompt_witness"|"hermes_pending_prompt"|"hard_reconnect_pending")
            && !(*name=="hermes_retention_issue" && journal.hermes_session.as_ref()
                .and_then(|s|s.retention_issue.as_deref())==Some("first prompt has not yet been retained")))
        .collect()
}
/// A typed failed prompt may first close a proven-unsent provider refusal.
/// All other terminal blockers must already be absent; full validation runs
/// again after physical stop and exact provider retirement.
pub(crate) fn validate_refusal_stop(journal: &Journal) -> Result<()> {
    let blockers:Vec<_>=terminal_blockers(journal).into_iter()
        .filter(|name| !matches!(*name,"provider_hold"|"provider_attempt")).collect();
    if blockers.is_empty() {Ok(())} else {Err(format!("failed prompt retains other work before provider retirement: {blockers:?}"))}
}

pub(crate) fn retain_failure(state: &Path, journal: &Journal, prompt: u64, value: &Value) -> Result<()> {
    let Some(error)=failure(value) else {return Ok(())};
    let record=json!({"type":"mini-hermes-failed-turn-v1","promptOperationId":prompt,
        "sessionId":journal.hermes_session.as_ref().map(|s|&s.id),"error":error,
        "journalSha256":sha256_bytes(&serde_json::to_vec(journal).map_err(|e|e.to_string())?)?,
        "providerResponses":journal.provider_replays,"residentOrigin":journal.resident_prompt_origin,"promptReplayed":false});
    write_new(&state.join(format!("hermes-failed-{prompt:016}.json")),
        &serde_json::to_vec_pretty(&record).map_err(|e|e.to_string())?)
}
pub(crate) fn close_failure(state: &Path, journal: &Journal, prompt: u64) -> Result<()> {
    let record=json!({"type":"mini-hermes-failed-turn-closed-v1","promptOperationId":prompt,
        "journalSha256":sha256_bytes(&serde_json::to_vec(journal).map_err(|e|e.to_string())?)?,
        "session":journal.hermes_session,"promptReplayed":false});
    write_new(&state.join(format!("hermes-failed-{prompt:016}.closed.json")),
        &serde_json::to_vec_pretty(&record).map_err(|e|e.to_string())?)
}

pub(crate) fn validate_completion(value: Value, journal: &Journal, prompt: u64,
    managed_provider: bool) -> Result<Value> {
    let blockers=terminal_blockers(journal);
    if !blockers.is_empty() {
        return Err(format!("Hermes terminal boundary retains unresolved work: {blockers:?}"));
    }
    if failure(&value).is_some() {
        return if typed_failure(&value["miniTurnFailure"]).is_some() {Ok(value)}
            else {Err("malformed typed Hermes failure".into())};
    }
    if value.get("stopReason").and_then(Value::as_str) != Some("end_turn") {
        return Err("Hermes did not report a completed end_turn".into());
    }
    if managed_provider {
        let generation = journal.prompt_witness.as_ref()
            .and_then(|w| w.pointer("/before/generation")).and_then(Value::as_str)
            .ok_or("Hermes prompt generation witness absent")?;
        if journal.provider_pending.is_some() || journal.provider_hold.is_some()
            || journal.provider_attempt.is_some() || !journal.provider_replays.iter().any(|r|
                r.prompt_operation_id == prompt && r.parent_generation == generation
                && r.status == 200 && r.meter_report_path.is_some()
                && r.meter_report_sha256.is_some() && r.metered_charge.is_some()) {
            return Err("Hermes end_turn has no settled metered provider response for this exact prompt".into());
        }
    }
    Ok(value)
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn managed_completion_requires_this_prompt_settled_generation() {
        let (root,rt)=crate::tests::restart_resolution_fixture("hermes-completion");
        let mut j=rt.journal;j.connection=Connection::Soft;j.tool_hold=None;j.workspace_attempt=None;
        j.prompt_witness=Some(json!({"before":{"generation":"7"}}));
        let ok=json!({"stopReason":"end_turn"});
        assert!(validate_completion(ok.clone(),&j,42,true).is_err());
        j.provider_replays.push(ProviderReplay {prompt_operation_id:41,parent_generation:"7".into(),
            request_path:root.join("request"),request_bytes:2,request_sha256:"a".repeat(64),
            response_path:root.join("response"),response_bytes:2,response_sha256:"b".repeat(64),
            status:200,content_type:"text/event-stream".into(),response_headers_path:None,
            response_headers_bytes:None,response_headers_sha256:None,meter_report_path:Some(root.join("meter")),
            meter_report_sha256:Some("c".repeat(64)),metered_charge:Some("1".into())});
        assert!(validate_completion(ok.clone(),&j,42,true).is_err());
        j.provider_replays[0].prompt_operation_id=42;
        j.provider_replays[0].parent_generation="6".into();
        assert!(validate_completion(ok.clone(),&j,42,true).is_err());
        j.provider_replays[0].parent_generation="7".into();
        validate_completion(ok.clone(),&j,42,true).unwrap();
        j.provider_replays[0].status=400;
        assert!(validate_completion(ok.clone(),&j,42,true).is_err());
        j.provider_replays[0].status=200;j.provider_replays[0].metered_charge=None;
        assert!(validate_completion(ok,&j,42,true).is_err());
        fs::remove_dir_all(root).unwrap();
    }
    #[test]
    fn stop_reason_is_never_implicitly_successful() {
        let (root,mut rt)=crate::tests::restart_resolution_fixture("hermes-stop-reason");
        rt.journal.connection=Connection::Soft;rt.journal.tool_hold=None;rt.journal.workspace_attempt=None;
        for value in [json!({}),json!({"stopReason":"refusal"}),json!({"stopReason":"cancelled"}),json!({"stopReason":"max_turn_requests"})] {
            assert!(validate_completion(value,&rt.journal,42,false).is_err());
        }
        validate_completion(json!({"stopReason":"end_turn"}),&rt.journal,42,false).unwrap();
        fs::remove_dir_all(root).unwrap();
    }
    #[test]
    fn typed_failure_keeps_durable_effect_uncertainty_and_never_becomes_success() {
        let (root,mut rt)=crate::tests::restart_resolution_fixture("hermes-typed-failure");
        rt.journal.connection=Connection::Soft;rt.journal.tool_hold=None;rt.journal.workspace_attempt=None;
        let error=json!({"code":-32003,"data":{"type":"mini-hermes-turn-failure-v1",
            "reason":"format_error","retryable":false,"detail":"HTTP400 bounded request"}});
        let value=typed_failure(&error).unwrap();
        validate_completion(value.clone(),&rt.journal,42,true).unwrap();
        retain_failure(&root,&rt.journal,42,&value).unwrap();
        assert!(root.join("hermes-failed-0000000000000042.json").exists());
        rt.journal.unresolved_external.push("possibly sent external request".into());
        assert!(validate_completion(value,&rt.journal,42,true).is_err());
        assert!(typed_failure(&json!({"code":-32003,"data":{"type":"mini-hermes-turn-failure-v1"}})).is_none());
        fs::remove_dir_all(root).unwrap();
    }

}
