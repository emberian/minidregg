//! Room tools in the durable AgentGrain controller. The room's Book payment
//! and the provider purse buy different things; neither confers resource
//! authority. All tools use the controller's pinned ToolTask workspace.
use crate::{resource_tools::{self, RoomTools, RoomToolsConfig}, *};

#[derive(Clone, Serialize, Deserialize, Debug)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub(crate) struct Attempt {
    pub operation_id: u64,
    pub tool: String,
    pub arguments: Value,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub resident_origin: Option<Value>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub expected_reply: Option<(String, u64)>,
    /// None means a payment might have left without its reply. Never pay again.
    pub payment: Option<Value>,
    /// Retained before attach/reserve: the single ToolTask hold belongs to this operation.
    #[serde(default)]
    pub tool_lifecycle_started: bool,
    #[serde(default)]
    pub payment_started: bool,
    pub write_started: bool,
    /// Set only after wait_with_output returned, or proved by the supervisor.
    pub submitter_stopped: bool,
    pub resolution: Option<Value>,
}

pub(crate) fn validate_pins(config: &Config, tool: &ToolTask) -> Result<()> {
    validate_pins_with_workspace(config, tool, None)
}
pub(crate) fn validate_pins_with_workspace(config: &Config, tool: &ToolTask, prospective: Option<&[u8]>) -> Result<()> {
    let Some(room) = &tool.room else { return Ok(()) };
    let workspace = validate_resource_workspace_record(config, tool, prospective)?;
    if room.workspace != workspace || room.mini != config.mini
        || room.host != config.host || room.host_config != config.host_config
        || Some(room.socket.as_path()) != config.host_socket.as_deref()
        || room.home.parent() != Some(config.state_dir.as_path())
        || room.home == workspace
    {
        return Err("room tools must share the delegated workspace/client/Host pins and have a separate home inside controller stateDir".into());
    }
    let meta = fs::symlink_metadata(&room.home).map_err(|e| format!("room home: {e}"))?;
    if !meta.is_dir() || meta.uid() != unsafe { libc::geteuid() } || meta.mode() & 0o077 != 0 {
        return Err("room home must be an owner-private real directory".into());
    }
    for name in std::iter::once(&room.room).chain(room.account.iter()) {
        if name.is_empty() || name.len() > 64 || !name.bytes().all(|b| b.is_ascii_alphanumeric() || b == b'-') {
            return Err("room and account names must be 1..64 ASCII letters, digits or hyphens".into());
        }
    }
    Ok(())
}

/// The patched real ACP adapter reports its final model-visible catalogue.
/// Check after new/load registration and before the first provider request.
pub(crate) fn require_acp_catalogue(response: &Value) -> Result<()> {
    let report = &response["_meta"]["miniToolCatalogue"];
    if report["type"] != "mini-hermes-tool-catalogue-v1" || report["valid"] != true {
        return Err("restricted resident requires verified ACP tool catalogue metadata".into());
    }
    let mut expected: Vec<String> = resource_tools::room_tool_specs().iter()
        .map(|spec| format!("mcp__mini_grain__{}", spec["name"].as_str().unwrap()))
        .chain(std::iter::once("mcp__mini_grain__mini_room_attempts".into())).collect();
    expected.sort();
    let actual: Vec<String> = report["names"].as_array().ok_or("ACP tool names absent")?.iter()
        .map(|name| name.as_str().map(str::to_owned).ok_or("ACP tool name invalid".to_owned()))
        .collect::<Result<_>>()?;
    if actual != expected { return Err("restricted resident ACP tools differ from its exact Mini room catalogue".into()); }
    Ok(())
}

impl Journal {
    pub(crate) fn validate_room(&self, config: &Config) -> Result<()> {
        if self.room_resolutions.len() > 64 { return Err("room resolution retention exceeded".into()); }
        if let Some(attempt) = &self.room_attempt {
            if attempt.operation_id >= self.next_operation_id
                || !resource_tools::ROOM_WRITE_TOOLS.contains(&attempt.tool.as_str())
                || !attempt.arguments.is_object()
                || serde_json::to_vec(&attempt.arguments).map_err(|e| e.to_string())?.len() > 8192
                || (attempt.write_started && attempt.payment.is_none())
                || config.tool_task.as_ref().and_then(|t| t.room.as_ref()).is_none()
            { return Err("malformed retained room attempt".into()); }
        }
        Ok(())
    }
}

impl Runtime {
    fn room_config(&self) -> Result<RoomToolsConfig> {
        let tool = self.config.tool_task.as_ref().ok_or("toolTask absent")?;
        validate_pins(&self.config, tool)?;
        tool.room.clone().ok_or_else(|| "this grain's Hermes is in no room (toolTask.room)".into())
    }

    pub(crate) fn room_attempts(&self, arguments: &Value) -> Result<Value> {
        if arguments != &json!({}) { return Err("mini_room_attempts takes no arguments".into()); }
        self.room_config()?;
        Ok(json!({"pending":self.journal.room_attempt,"resolutions":self.journal.room_resolutions}))
    }

    fn record_room_resolution(&mut self, resolution: Value) -> Result<()> {
        let attempt = self.journal.room_attempt.as_mut().ok_or("room attempt absent")?;
        attempt.resolution = Some(resolution.clone());
        // Persist the exact effect decision before any settlement. A crash or
        // failed settlement retries only the purse lifecycle, never the effect.
        self.save()?;
        if resolution["resolution"] != "uncertain" {
            let attempt = self.journal.room_attempt.as_ref().unwrap();
            let charge = if attempt.payment.is_some() || attempt.write_started {
                self.config.tool_task.as_ref().ok_or("toolTask absent")?.charge.clone()
            } else { "0".to_owned() };
            if attempt.tool_lifecycle_started { self.finish_tool_operation(&charge)?; }
            let attempt = self.journal.room_attempt.take().unwrap();
            self.journal.room_resolutions.push(json!({"operationId":attempt.operation_id.to_string(),
                "tool":attempt.tool,"arguments":attempt.arguments,"residentOrigin":attempt.resident_origin,"expectedReply":attempt.expected_reply,
                "payment":attempt.payment,"toolCharge":charge,"result":resolution}));
            if self.journal.room_resolutions.len() > 64 { self.journal.room_resolutions.remove(0); }
        }
        self.save()
    }

    /// Never replay a payment or a write. Exact document lookup is safe only
    /// after the old submitter has stopped. A stream text match is NOT an
    /// operation identity; payment and stream recovery use the client's
    /// immutable operation record, never tail text or a fresh submission.
    pub(crate) fn recover_room(&mut self) -> Result<()> {
        let Some(attempt) = self.journal.room_attempt.clone() else { return Ok(()) };
        if !attempt.submitter_stopped && !(self.prior_run_stopped && attempt.operation_id < self.process_first_operation_id) {
            return Err("room attempt needs proof that its previous submitter stopped".into());
        }
        if let Some(resolution) = &attempt.resolution {
            if resolution["resolution"] != "uncertain" {
                return self.record_room_resolution(resolution.clone());
            }
        }
        let config = self.room_config()?;
        let tools = RoomTools { config: &config };
        let operation = format!("g{}", attempt.operation_id);
        let resolution = if attempt.tool_lifecycle_started && !attempt.payment_started {
            json!({"resolution":"refused","basis":"payment-not-started","notResent":true})
        } else if attempt.payment.is_none() {
            let payment = tools.lookup_operation(&operation, "payment")?;
            if payment["resolution"] == "performed" {
                self.journal.room_attempt.as_mut().unwrap().payment = Some(payment.clone());
                json!({"resolution":"refused","basis":"paid-but-write-not-started","payment":payment,"notResent":true})
            } else { payment }
        } else if !attempt.write_started {
            json!({"resolution":"refused","basis":"paid-but-write-not-started","notResent":true})
        } else if attempt.tool == "mini_say" {
            tools.lookup_operation(&operation, "write")?
        } else {
            tools.lookup(&operation)?
        };
        let uncertain = resolution["resolution"] == "uncertain";
        self.record_room_resolution(resolution)?;
        if uncertain { Err("room operation remains uncertain; no payment or write was resent".into()) } else { Ok(()) }
    }

    pub(crate) fn room_call(&mut self, name: &str, arguments: &Value) -> Result<Value> {
        self.room_call_with_id(name, arguments, None)
    }

    pub(crate) fn room_call_with_id(&mut self, name: &str, arguments: &Value, allocated: Option<u64>) -> Result<Value> {
        let config = self.room_config()?;
        let tools = RoomTools { config: &config };
        if !resource_tools::ROOM_WRITE_TOOLS.contains(&name) { return tools.read(name, arguments); }
        // Reject malformed calls before spending. The client still judges
        // every actual operation against the current laws and grants.
        resource_tools::validate_room_write(name, arguments)?;
        resident_delivery::admits_room_call(&self.journal, name, arguments, allocated)?;
        if self.journal.room_attempt.is_some() { return Err("room operation is unresolved; inspect mini_room_attempts".into()); }
        if self.journal.workspace_attempt.is_some() || self.journal.workspace_birth.is_some()
            || self.journal.tool_hold.is_some() || self.journal.tool_pending.is_some()
        { return Err("delegated tool operation requires exact recovery".into()); }
        let id = match allocated { Some(id) => id, None => self.next_id()? };
        let op = format!("g{id}");
        self.journal.room_attempt = Some(Attempt { operation_id:id, tool:name.into(), arguments:arguments.clone(),
            resident_origin:resident_delivery::room_origin(&self.journal, self.prompt_active, allocated),
            expected_reply:resident_delivery::expected_reply(&self.journal, allocated)?,
            payment:None, tool_lifecycle_started:true, payment_started:false,
            write_started:false, submitter_stopped:true, resolution:None });
        self.save()?;
        if let Err(error) = self.reserve_tool_operation() {
            let recovery = self.recover_room();
            return Err(format!("room reservation failed before payment: {error}; recovery: {recovery:?}"));
        }
        self.check_not_cancelled()?;
        let attempt = self.journal.room_attempt.as_mut().unwrap();
        attempt.payment_started = true;
        attempt.submitter_stopped = false;
        self.save()?;
        let payment = match tools.pay(&op, name) {
            Ok(value) => value,
            Err(error) => {
                self.journal.room_attempt.as_mut().unwrap().submitter_stopped = true;
                // A CLI failure can follow a sent payment. Use its exact
                // retained operation, never human-readable error matching.
                self.save()?;
                let recovery = self.recover_room();
                return Err(match recovery { Ok(()) => error, Err(uncertain) => format!("{error}; {uncertain}") });
            }
        };
        self.journal.room_attempt.as_mut().unwrap().payment = Some(payment.clone());
        self.journal.room_attempt.as_mut().unwrap().submitter_stopped = true;
        self.save()?;
        self.check_not_cancelled()?;
        self.journal.room_attempt.as_mut().unwrap().submitter_stopped = false;
        self.journal.room_attempt.as_mut().unwrap().write_started = true;
        self.save()?;
        let expected_reply = self.journal.room_attempt.as_ref().unwrap().expected_reply.clone();
        let result = tools.write_with_reply_guard(&op, name, arguments, &mut |_| {}, expected_reply.as_ref().map(|(cell, sequence)| (cell.as_str(), *sequence)));
        self.journal.room_attempt.as_mut().unwrap().submitter_stopped = true;
        self.save()?;
        match result {
            Ok(mut value) => {
                self.record_room_resolution(json!({"resolution":"performed","basis":"client-confirmed","value":value}))?;
                value["turn"] = payment;
                Ok(value)
            }
            Err(error) => {
                let recovery = self.recover_room();
                Err(match recovery { Ok(()) => error, Err(uncertain) => format!("{error}; {uncertain}") })
            }
        }
    }
}

#[cfg(test)]
pub(crate) mod tests {
    use super::*;
    #[test]
    fn room_write_arguments_refuse_before_payment() {
        assert!(resource_tools::validate_room_write("mini_doc_append", &json!({"doc":"x","text":"fine"})).is_ok());
        assert!(resource_tools::validate_room_write("mini_doc_append", &json!({"doc":"../other","text":"fine"})).is_err());
        assert!(resource_tools::validate_room_write("mini_say", &json!({"text":"fine","to":17})).is_err());
        assert!(resource_tools::validate_room_write("mini_doc_link", &json!({"from":"x","to":"y","unexpected":"x"})).is_err());
    }
    pub(crate) fn fixture(tag: &str) -> (PathBuf, Runtime) {
        let (root, mut rt) = crate::tests::restart_resolution_fixture(tag);
        rt.journal.workspace_attempt = None;
        rt.journal.workspace_proposals.clear();
        rt.journal.tool_hold = None;
        rt.config.host_socket = Some(root.join("mini.sock"));
        let home = rt.config.state_dir.join("room-home");
        fs::create_dir(&home).unwrap();
        fs::set_permissions(&home, fs::Permissions::from_mode(0o700)).unwrap();
        let workspace = rt.config.tool_task.as_ref().unwrap().resource_workspace.clone().unwrap();
        let path = workspace.join("workspace.json");
        let mut pin: Value = serde_json::from_slice(&fs::read(&path).unwrap()).unwrap();
        pin["socket"] = json!(rt.config.host_socket);
        fs::write(path, serde_json::to_vec(&pin).unwrap()).unwrap();
        rt.config.tool_task.as_mut().unwrap().room = Some(RoomToolsConfig {
            restrict_tools: false,
            mini:rt.config.mini.clone(), host:rt.config.host.clone(), host_config:rt.config.host_config.clone(),
            socket:rt.config.host_socket.clone().unwrap(), workspace, home, room:"lab".into(),account:None,
        });
        (root, rt)
    }

    fn pending(rt: &mut Runtime, tool: &str, payment: Option<Value>, write_started: bool) {
        rt.journal.room_attempt = Some(Attempt { operation_id:2, tool:tool.into(),
            arguments:json!({"text":"same text twice"}), resident_origin:None, expected_reply:None, payment, write_started, tool_lifecycle_started:false, payment_started:true,
            submitter_stopped:false, resolution:None });
    }

    #[test]
    fn restricted_resident_rejects_hidden_general_tools_before_execution() {
        let (root, mut rt) = fixture("room-restricted");
        rt.config.tool_task.as_mut().unwrap().room.as_mut().unwrap().restrict_tools = true;
        assert!(rt.tool_catalog().unwrap().room_tools);
        assert!(!rt.tool_catalog().unwrap().resource_workspace);
        for name in ["mini_publish", "mini_workspace_submit", "mini_workspace_recover", "mini_grain_status"] {
            assert!(rt.tool_call(name, &json!({})).unwrap_err().contains("only room tools"));
        }
        assert!(!rt.tool_call("mini_room_attempts", &json!({})).unwrap_err().contains("only room tools"));
        fs::remove_dir_all(root).unwrap();
    }

    #[test]
    fn room_custody_cannot_point_to_another_workspace_or_host() {
        let (root, mut rt) = fixture("room-pins");
        assert!(validate_pins(&rt.config, rt.config.tool_task.as_ref().unwrap()).is_ok());
        rt.config.tool_task.as_mut().unwrap().room.as_mut().unwrap().workspace = root.join("other");
        assert!(validate_pins(&rt.config, rt.config.tool_task.as_ref().unwrap()).is_err());
        fs::remove_dir_all(root).unwrap();
    }

    #[test]
    fn crashed_payment_remains_pending_and_is_never_resent() {
        let (root, mut rt) = fixture("room-payment");
        pending(&mut rt, "mini_say", None, false);
        let config = rt.room_config().unwrap();
        let record = RoomTools { config: &config }.operation_record("g2", "payment").unwrap();
        fs::write(record, b"retained operation whose lookup is unavailable").unwrap();
        assert!(rt.recover_room().unwrap_err().contains("proof"));
        rt.prior_run_stopped = true;
        assert!(rt.recover_room().unwrap_err().contains("uncertain"));
        assert_eq!(rt.journal.room_attempt.as_ref().unwrap().resolution.as_ref().unwrap()["basis"], "exact-operation-record");
        assert!(rt.needs_startup_recovery());
        let bytes = fs::read(rt.config.state_dir.join("journal.json")).unwrap();
        let restored: Journal = serde_json::from_slice(&bytes).unwrap();
        assert!(restored.room_attempt.is_some());
        assert!(rt.room_call("mini_say", &json!({"text":"again"})).unwrap_err().contains("unresolved"));
        fs::remove_dir_all(root).unwrap();
    }

    #[test]
    fn crash_before_write_resolves_without_a_second_payment() {
        let (root, mut rt) = fixture("room-paid");
        pending(&mut rt, "mini_say", Some(json!({"paid":true})), false);
        rt.prior_run_stopped = true;
        rt.recover_room().unwrap();
        assert!(rt.journal.room_attempt.is_none());
        assert_eq!(rt.journal.room_resolutions[0]["result"]["basis"], "paid-but-write-not-started");
        fs::remove_dir_all(root).unwrap();
    }

    #[test]
    fn an_identical_stream_message_is_not_exact_recovery() {
        let (root, mut rt) = fixture("room-say");
        pending(&mut rt, "mini_say", Some(json!({"paid":true})), true);
        let config = rt.room_config().unwrap();
        let record = RoomTools { config: &config }.operation_record("g2", "write").unwrap();
        fs::write(record, b"retained operation whose lookup is unavailable").unwrap();
        rt.prior_run_stopped = true;
        assert!(rt.recover_room().is_err());
        assert_eq!(rt.journal.room_attempt.as_ref().unwrap().resolution.as_ref().unwrap()["basis"], "exact-operation-record");
        fs::remove_dir_all(root).unwrap();
    }

    #[test]
    fn document_never_submitted_resolves_only_after_stop_proof() {
        let (root, mut rt) = fixture("room-document");
        pending(&mut rt, "mini_doc_append", Some(json!({"paid":true})), true);
        assert!(rt.recover_room().is_err());
        rt.prior_run_stopped = true;
        rt.recover_room().unwrap();
        assert_eq!(rt.journal.room_resolutions[0]["result"]["basis"], "not-submitted");
        fs::remove_dir_all(root).unwrap();
    }

    fn held_operation(rt: &mut Runtime) {
        rt.journal.room_attempt.as_mut().unwrap().tool_lifecycle_started = true;
        rt.mark_hold(true, "3", "1").unwrap();
        rt.journal.tool_hold.as_mut().unwrap().reserve_confirmed = true;
    }

    #[test]
    fn paid_room_recovery_settles_shared_tool_hold_before_releasing_attempt() {
        let (root, mut rt) = fixture("room-paid-held");
        pending(&mut rt, "mini_say", Some(json!({"paid":true})), false);
        held_operation(&mut rt);
        rt.prior_run_stopped = true;
        rt.recover_room().unwrap();
        assert!(rt.journal.room_attempt.is_none());
        assert!(rt.journal.tool_hold.is_none());
        assert_eq!(fs::read_to_string(root.join("sim/status")).unwrap(), "0");
        assert_eq!(rt.journal.room_resolutions[0]["toolCharge"], "1");
        fs::remove_dir_all(root).unwrap();
    }

    #[test]
    fn room_settlement_failure_retains_exact_result_and_hold_for_retry() {
        let (root, mut rt) = fixture("room-settle-failed");
        pending(&mut rt, "mini_say", Some(json!({"paid":true})), false);
        held_operation(&mut rt);
        rt.prior_run_stopped = true;
        let script = fs::read_to_string(&rt.config.mini).unwrap();
        fs::write(&rt.config.mini, "#!/bin/sh\nexit 42\n").unwrap();
        assert!(rt.recover_room().is_err());
        assert!(rt.journal.tool_hold.is_some());
        assert!(rt.journal.room_resolutions.is_empty());
        let retained = rt.journal.room_attempt.as_ref().unwrap().resolution.clone().unwrap();
        assert_eq!(retained["basis"], "paid-but-write-not-started");
        let journal: Journal = serde_json::from_slice(&fs::read(rt.config.state_dir.join("journal.json")).unwrap()).unwrap();
        assert_eq!(journal.room_attempt.unwrap().resolution, Some(retained.clone()));
        fs::write(&rt.config.mini, script).unwrap();
        rt.recover_room().unwrap();
        assert_eq!(rt.journal.room_resolutions[0]["result"], retained);
        assert!(rt.journal.tool_hold.is_none());
        fs::remove_dir_all(root).unwrap();
    }

    #[test]
    fn crash_after_reserve_before_payment_returns_tool_allowance_without_payment() {
        let (root, mut rt) = fixture("room-before-payment");
        pending(&mut rt, "mini_say", None, false);
        held_operation(&mut rt);
        rt.journal.room_attempt.as_mut().unwrap().payment_started = false;
        rt.prior_run_stopped = true;
        rt.recover_room().unwrap();
        assert!(rt.journal.tool_hold.is_none());
        assert_eq!(rt.journal.room_resolutions[0]["toolCharge"], "0");
        assert_eq!(rt.journal.room_resolutions[0]["result"]["basis"], "payment-not-started");
        fs::remove_dir_all(root).unwrap();
    }

    #[test]
    fn uncertain_room_payment_preserves_tool_hold_and_blocks_new_writes() {
        let (root, mut rt) = fixture("room-uncertain-held");
        pending(&mut rt, "mini_say", None, false);
        held_operation(&mut rt);
        let config = rt.room_config().unwrap();
        let record = RoomTools { config: &config }.operation_record("g2", "payment").unwrap();
        fs::write(record, b"retained unavailable operation").unwrap();
        rt.prior_run_stopped = true;
        assert!(rt.recover_room().is_err());
        assert!(rt.journal.tool_hold.is_some());
        assert!(rt.room_call("mini_say", &json!({"text":"new"})).is_err());
        assert_eq!(fs::read_to_string(root.join("sim/status")).unwrap(), "3");
        fs::remove_dir_all(root).unwrap();
    }

    #[test]
    fn unavailable_tool_purse_refuses_before_any_room_payment() {
        let (root, mut rt) = fixture("room-reserve-first");
        let error = rt.room_call("mini_say", &json!({"text":"must not send"})).unwrap_err();
        assert!(error.contains("reservation failed before payment"));
        let pending = rt.journal.room_attempt.as_ref().unwrap();
        assert!(!pending.payment_started);
        assert!(!pending.write_started);
        assert!(pending.payment.is_none());
        assert!(!rt.config.tool_task.as_ref().unwrap().resource_workspace.as_ref().unwrap().join("room-operations").exists());
        fs::remove_dir_all(root).unwrap();
    }

    #[test]
    fn acp_catalogue_gate_refuses_missing_empty_extra_and_duplicate_tools() {
        let mut names: Vec<String> = resource_tools::room_tool_specs().iter()
            .map(|s| format!("mcp__mini_grain__{}",s["name"].as_str().unwrap()))
            .chain(std::iter::once("mcp__mini_grain__mini_room_attempts".into())).collect();
        names.sort();
        let response = |names: Vec<String>| json!({"_meta":{"miniToolCatalogue":{
            "type":"mini-hermes-tool-catalogue-v1","valid":true,"names":names}}});
        require_acp_catalogue(&response(names.clone())).unwrap();
        assert!(require_acp_catalogue(&json!({})).is_err());
        assert!(require_acp_catalogue(&response(vec![])).is_err());
        let mut extra=names.clone();extra.push("terminal".into());
        assert!(require_acp_catalogue(&response(extra)).is_err());
        let mut duplicate=names.clone();duplicate.push(names[0].clone());
        assert!(require_acp_catalogue(&response(duplicate)).is_err());
        let mut invalid=response(names);invalid["_meta"]["miniToolCatalogue"]["valid"]=json!(false);
        assert!(require_acp_catalogue(&invalid).is_err());
    }

}
