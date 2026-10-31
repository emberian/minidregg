//! Read-only source preflight before a resident marks its request started.
//! Actual prompt admission still repeats these checks. This cannot clear a
//! started/unknown request or authorize a model, payment, or native effect.
use crate::*;

fn config_digest(config:&Config)->Result<String> {
    sha256_bytes(&serde_json::to_vec(config).map_err(|e|e.to_string())?)
}
fn binding_digest(config:&Config,path:&Path)->Result<String> {
    sha256_bytes(&serde_json::to_vec(&json!({"config":config,"configPath":path})).map_err(|e|e.to_string())?)
}
fn response(config:&Config,path:&Path)->Result<Value> {
    Ok(json!({"type":"mini-resident-preflight-ready-v1","task":config.task,
        "configSha256":config_digest(config)?,"bindingSha256":binding_digest(config,path)?}))
}
fn checked_operator(config:&Config,text:&[u8])->Result<Value> {
    let value:Value=serde_json::from_slice(text).map_err(|_|"private operator preflight did not return one JSON response")?;
    if value["format"]!="mini-operator-drain-v1" || value["phase"]!="serving"
        || value["admissionClosed"]!=false || value["drained"]!=false
        || value["processId"].as_u64().is_none_or(|pid|pid==0 || pid>u32::MAX as u64)
        || value["hostProcessId"].as_u64().is_none_or(|pid|pid==0 || pid>u32::MAX as u64)
        || value["instanceId"].as_str().is_none_or(|id|!resident_origin::valid_digest(id))
        || value["requestNonce"].as_str().is_none_or(|id|!resident_origin::valid_digest(id))
        || value["hostSha256"]!=sha256_pinned_file(&config.host)? || value["configSha256"]!=sha256_file(&config.host_config)? {
        return Err("controller requires serving private operator with exact Host/config pins and current process identity".into());
    }
    Ok(value)
}
fn operator_status_command(config:&Config)->Result<Command> {
    // Dispatch custody already names a controller-private, peer-pinned route.
    // Its status-only control listener proves the same upstream operator while
    // ordinary room traffic continues through the participant transport.
    let dispatch=config.dispatch_task.as_ref().filter(|task|task.operator_socket.is_some());
    let socket=dispatch.and_then(|task|task.operator_socket.as_deref()).or(config.host_socket.as_deref())
        .ok_or("resident controller requires private native operator socket")?;
    let mut command=Command::new(&config.mini);
    command.args(["operator-status","--socket"]).arg(socket)
        .arg("--host").arg(&config.host).arg("--config").arg(&config.host_config);
    if let Some(uid)=dispatch.and_then(|task|task.operator_peer_uid) {
        command.arg("--operator-peer-uid").arg(uid.to_string());
    }
    Ok(command)
}
/// The native Mini control command proves the current owner-private transport
/// role and response nonce. An operator path or stale mode file cannot do so.
pub(crate) fn require_private_operator(config:&Config)->Result<Value> {
    let mut waits=OPERATOR_STATUS_BACKOFF.iter();
    loop {
        let mut command=operator_status_command(config)?;
        let result=crate::deadline::output(&mut command,crate::deadline::NATIVE_CALL)
            .map_err(|e|crate::deadline::describe("private operator preflight",e))?;
        if result.status.success() && result.stdout.len()<=65_536 {
            return checked_operator(config,&result.stdout);
        }
        let said=String::from_utf8_lossy(&result.stderr).chars().take(2048).collect::<String>();
        match waits.next() {
            // A status read is read-only: asking again is the same question. A busy box answers late
            // (the operator's frame read deadline, a queue residence deadline), never wrongly.
            Some(wait) if transient_operator_refusal(&said) => std::thread::sleep(*wait),
            _ => return Err(format!("private operator preflight refused: {said}")),
        }
    }
}

/// The pauses before asking the operator's status again after a transient refusal: about 15 s in
/// all, inside the controller's start budget.
const OPERATOR_STATUS_BACKOFF:[std::time::Duration;4]=[std::time::Duration::from_secs(1),std::time::Duration::from_secs(2),
    std::time::Duration::from_secs(4),std::time::Duration::from_secs(8)];

/// A refusal that says the box was too busy to answer in time, not that the operator is wrong.
fn transient_operator_refusal(stderr:&str)->bool {
    ["frame read deadline","queue residence deadline","busy:","contention","unavailable: the Host"].iter().any(|w|stderr.contains(w))
}
const PREPARED:&str="mini-resident-prompt-preparation-v1";
#[derive(Serialize,Deserialize)]
#[serde(rename_all="camelCase",deny_unknown_fields)]
struct Preparation {
    #[serde(rename="type")] kind:String,
    task:String,config_sha256:String,binding_sha256:String,
    resident_prompt_id:String,prompt_sha256:String,
}
fn preparation_path(config:&Config,id:&str)->PathBuf {config.state_dir.join(format!("resident-prepared-{id}.json"))}
fn entered_path(config:&Config,id:&str)->PathBuf {config.state_dir.join(format!("resident-entered-{id}.json"))}
fn preparation(config:&Config,path:&Path,id:&str,sha:&str)->Result<Value> {
    if !resident_origin::valid_digest(id) || !resident_origin::valid_digest(sha) {return Err("invalid source prompt preparation identity".into());}
    Ok(json!({"type":PREPARED,"task":config.task,"configSha256":config_digest(config)?,"bindingSha256":binding_digest(config,path)?,
        "residentPromptId":id,"promptSha256":sha}))
}
fn check_preparation(config:&Config,path:&Path,sha:&str,value:&Value)->Result<String> {
    let prepared:Preparation=serde_json::from_value(value.clone()).map_err(|e|format!("source prompt preparation: {e}"))?;
    let id=prepared.resident_prompt_id;
    if *value!=preparation(config,path,&id,sha)? {return Err("source prompt preparation differs from exact config/text binding".into());}
    Ok(id)
}
pub(crate) fn prepare(config:&Config,path:&Path,sha:&str)->Result<String> {
    if !resident_origin::valid_digest(sha) {return Err("invalid prompt preparation digest".into());}
    let text=control::admin_call(&config.state_dir.join("admin.sock"),&format!("resident prepare {sha}"))?;
    let value:Value=serde_json::from_str(&text).map_err(|_|format!("resident source preparation refused before dispatch: {text}"))?;
    check_preparation(config,path,sha,&value)
}
const REFUSAL:&str="mini-resident-prompt-preadmission-refused-v1";
#[derive(Serialize,Deserialize)]
#[serde(rename_all="camelCase",deny_unknown_fields)]
struct Refusal {
    #[serde(rename="type")] kind:String,
    task:String,config_sha256:String,binding_sha256:String,
    resident_prompt_id:String,prompt_sha256:String,
    preparation_sha256:String,admitted:bool,effects:String,model_requests:u64,reason:String,
}
fn refusal_path(config:&Config,id:&str)->PathBuf {
    config.state_dir.join(format!("resident-preadmission-refused-{id}.json"))
}
fn check_refusal(config:&Config,path:&Path,id:&str,sha:&str,value:Value)->Result<Value> {
    let proof:Refusal=serde_json::from_value(value.clone()).map_err(|e|format!("resident preadmission refusal schema: {e}"))?;
    if !resident_origin::valid_digest(id) || !resident_origin::valid_digest(sha)
        || proof.kind!=REFUSAL || proof.task!=config.task || proof.config_sha256!=config_digest(config)?
        || proof.binding_sha256!=binding_digest(config,path)? || proof.resident_prompt_id!=id || proof.prompt_sha256!=sha
        || !resident_origin::valid_digest(&proof.preparation_sha256) || proof.admitted || proof.effects!="none" || proof.model_requests!=0 || proof.reason.is_empty() || proof.reason.len()>8192 {
        return Err("resident preadmission refusal differs from exact prompt/config binding".into());
    }
    Ok(value)
}
/// Unrecorded means uncertainty, never permission to clear retained work.
pub(crate) fn lookup_refusal(config:&Config,path:&Path,id:&str,sha:&str)->Result<Option<Value>> {
    if !resident_origin::valid_digest(id) || !resident_origin::valid_digest(sha) {return Err("invalid resident refusal lookup identity".into());}
    let text=control::admin_call(&config.state_dir.join("admin.sock"),&format!("resident admission {id} {sha}"))?;
    let value:Value=serde_json::from_str(&text).map_err(|_|format!("resident admission lookup refused: {text}"))?;
    if value==json!({"type":"mini-resident-prompt-admission-unrecorded-v1","residentPromptId":id,"promptSha256":sha}) {return Ok(None);}
    check_refusal(config,path,id,sha,value).map(Some)
}
impl Runtime {
    pub(crate) fn prepare_resident_prompt(&self,sha:&str)->Result<Value> {
        if !resident_origin::valid_digest(sha) {return Err("invalid source prompt preparation digest".into());}
        self.preflight_resident_prompt()?;
        // The caller cannot choose/re-present an old unknown ID. Source fresh
        // issuance is necessary before the driver can mark work started.
        let id=provider_profile::random_token()?;
        let value=preparation(&self.config,&self.config_path,&id,sha)?;
        write_new(&preparation_path(&self.config,&id),&serde_json::to_vec_pretty(&value).map_err(|e|e.to_string())?)?;
        Ok(value)
    }
    pub(crate) fn retained_preparation(&self,id:&str,sha:&str)->Result<(Value,String)> {
        if !resident_origin::valid_digest(id) || !resident_origin::valid_digest(sha) {return Err("invalid resident preparation lookup identity".into());}
        let bytes=bounded_regular_file(&preparation_path(&self.config,id),65_536)
            .map_err(|_|"prompt has no exact source-issued preparation; old unknown work cannot be classified as unadmitted")?;
        let value:Value=serde_json::from_slice(&bytes).map_err(|e|e.to_string())?;
        if check_preparation(&self.config,&self.config_path,sha,&value)?!=id {return Err("retained preparation names another source prompt".into());}
        Ok((value,sha256_bytes(&bytes)?))
    }
    pub(crate) fn enter_resident_prompt(&self,id:&str,sha:&str)->Result<()> {
        let (prepared,hash)=self.retained_preparation(id,sha)?;
        if self.config.state_dir.join(format!("resident-origin-id-{id}.json")).try_exists().map_err(|e|e.to_string())?
            || refusal_path(&self.config,id).try_exists().map_err(|e|e.to_string())? {
            return Err("resident prompt already admitted or refused; exact recovery is required".into());
        }
        // This immutable unique fence commits BEFORE inner Hermes preparation
        // and its first possible native effect. Re-presenting entered IDs fails.
        let value=json!({"type":"mini-resident-prompt-entered-v1","preparation":prepared,"preparationSha256":hash});
        write_new(&entered_path(&self.config,id),&serde_json::to_vec_pretty(&value).map_err(|e|e.to_string())?)?;
        Ok(())
    }
    pub(crate) fn record_resident_preadmission_refusal(&self,id:&str,sha:&str,prompt:&str,reason:&str)->Result<()> {
        // Called only when the source preflight fails, before entering Hermes
        // preparation, first native reserve, provider or worker dispatch.
        resident_origin::validate(id,sha,prompt)?;
        let (_,preparation_sha256)=self.retained_preparation(id,sha)?;
        if entered_path(&self.config,id).try_exists().map_err(|e|e.to_string())? {
            return Err("entered source prompt cannot receive preadmission refusal".into());
        }
        if self.config.state_dir.join(format!("resident-origin-id-{id}.json")).try_exists().map_err(|e|e.to_string())? {
            return Err("admitted prompt cannot receive preadmission refusal".into());
        }
        let proof=Refusal {kind:REFUSAL.into(),task:self.config.task.clone(),config_sha256:config_digest(&self.config)?,
            binding_sha256:binding_digest(&self.config,&self.config_path)?,resident_prompt_id:id.into(),prompt_sha256:sha.into(),
            preparation_sha256,admitted:false,effects:"none".into(),model_requests:0,reason:reason.chars().take(2048).collect()};
        let value=serde_json::to_value(proof).map_err(|e|e.to_string())?;
        let value=check_refusal(&self.config,&self.config_path,id,sha,value)?;
        retain_exact_private(&refusal_path(&self.config,id),&serde_json::to_vec_pretty(&value).map_err(|e|e.to_string())?,65_536)?;
        Ok(())
    }
    pub(crate) fn resident_admission(&self,id:&str,sha:&str)->Result<Value> {
        if !resident_origin::valid_digest(id) || !resident_origin::valid_digest(sha) {return Err("invalid resident admission identity".into());}
        let file=refusal_path(&self.config,id);
        if !file.try_exists().map_err(|e|e.to_string())? {
            return Ok(json!({"type":"mini-resident-prompt-admission-unrecorded-v1","residentPromptId":id,"promptSha256":sha}));
        }
        if self.config.state_dir.join(format!("resident-origin-id-{id}.json")).try_exists().map_err(|e|e.to_string())? {
            return Err("resident refusal conflicts with retained admitted origin".into());
        }
        let (_,hash)=self.retained_preparation(id,sha)?;
        if entered_path(&self.config,id).try_exists().map_err(|e|e.to_string())? {return Err("refusal conflicts with entered prompt; exact native recovery required".into());}
        let value:Value=serde_json::from_slice(&bounded_regular_file(&file,65_536)?).map_err(|e|e.to_string())?;
        if value["preparationSha256"]!=hash {return Err("refusal changed its exact source preparation".into());}
        check_refusal(&self.config,&self.config_path,id,sha,value)
    }
    pub(crate) fn preflight_resident_prompt(&self)->Result<Value> {
        let status=self.quiescence_status()?;
        if !status.active.is_empty() || !status.retained.is_empty() {
            return Err("resident preflight requires recovery of retained or active service work".into());
        }
        let spec=self.config.commands.iter().find(|s|s.name=="hermes-acp").ok_or("no hermes-acp command configured")?;
        if !matches!(spec.program.file_name().and_then(|p|p.to_str()),Some("bwrap"|"sandbox-exec"))
            || !spec.args.iter().any(|arg|arg.ends_with("hermes-acp")) {
            return Err("resident preflight requires the configured confined Hermes command".into());
        }
        if spec.systemd_scope {
            prove_controller_unit(&self.config.task)?;
            Self::prove_launcher_gate(&spec.program)?;
            systemd_manager::verify_launcher(&self.config.task,&spec.program)?;
        }
        require_private_operator(&self.config)?;
        response(&self.config,&self.config_path)
    }
}
#[cfg(test)]
mod transient_tests {
    #[test]
    fn only_a_busy_box_is_asked_again() {
        assert!(super::transient_operator_refusal("error: refused: invalid socket frame: frame read deadline"));
        assert!(super::transient_operator_refusal("busy: queue residence deadline (read resource of roster in lobby)"));
        assert!(!super::transient_operator_refusal("controller requires serving private operator with exact Host/config pins"));
        assert!(!super::transient_operator_refusal("error: no such socket"));
        let total:u64=super::OPERATOR_STATUS_BACKOFF.iter().map(|d|d.as_secs()).sum();
        assert!(total<=30,"the retries fit a controller start");
    }
}
#[cfg(test)]
pub(crate) fn fixture_preparation(config:&Config,path:&Path,sha:&str)->Value {
    preparation(config,path,&provider_profile::random_token().unwrap(),sha).unwrap()
}
#[cfg(test)]
pub(crate) fn fixture_retain_preparation(rt:&Runtime,id:&str,sha:&str) {
    let value=preparation(&rt.config,&rt.config_path,id,sha).unwrap();
    write_new(&preparation_path(&rt.config,id),&serde_json::to_vec_pretty(&value).unwrap()).unwrap();
}
#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn dispatch_preflight_uses_private_status_route_and_exact_activation_peer() {
        let (root,mut rt)=crate::tests::restart_resolution_fixture("dispatch-status-route");
        rt.config.host_socket=Some(root.join("public.sock"));
        let args=|command:Command|command.get_args().map(|v|v.to_string_lossy().into_owned()).collect::<Vec<_>>();
        assert_eq!(args(operator_status_command(&rt.config).unwrap())[2],root.join("public.sock").to_str().unwrap());
        rt.config.dispatch_task=Some(serde_json::from_value(json!({
            "task":"7500","subject":"12","capability":"121","queryCapability":"122",
            "custodyKey":root.join("payer.key"),"parentCapability":"1204","parentObserveCapability":"1205",
            "reserve":"1","charge":"1","socketPath":root.join("dispatch.sock"),"hostUid":1001,
            "operatorSocket":root.join("operator/mini.sock"),"operatorPeerUid":0
        })).unwrap());
        let selected=args(operator_status_command(&rt.config).unwrap());
        assert_eq!(selected[2],root.join("operator/mini.sock").to_str().unwrap());
        assert_eq!(&selected[selected.len()-2..],["--operator-peer-uid","0"]);
        assert!(!selected.iter().any(|a|a==root.join("public.sock").to_str().unwrap()));
        assert_eq!(rt.config.host_socket,Some(root.join("public.sock")),"public transport binding stays unchanged");
        rt.config.dispatch_task.as_mut().unwrap().operator_peer_uid=None;
        assert!(!args(operator_status_command(&rt.config).unwrap()).contains(&"--operator-peer-uid".into()));
        fs::remove_dir_all(root).unwrap();
    }
    #[test]
    fn private_operator_preflight_refuses_public_dead_closed_or_substituted_source() {
        let (root,mut rt)=crate::tests::restart_resolution_fixture("private-operator-preflight");
        rt.config.host=root.join("host-image");rt.config.host_config=root.join("host-config");
        fs::write(&rt.config.host,"exact image").unwrap();fs::write(&rt.config.host_config,"exact config").unwrap();
        let good=json!({"format":"mini-operator-drain-v1","phase":"serving","admissionClosed":false,"drained":false,
            "processId":1,"hostProcessId":2,"instanceId":"a".repeat(64),"requestNonce":"b".repeat(64),
            "hostSha256":sha256_file(&rt.config.host).unwrap(),"configSha256":sha256_file(&rt.config.host_config).unwrap()});
        checked_operator(&rt.config,&serde_json::to_vec(&good).unwrap()).unwrap();
        for (key,value) in [("format",json!("public")),("phase",json!("draining")),("admissionClosed",json!(true)),
            ("hostProcessId",json!(0)),("processId",json!(0)),("instanceId",json!("old")),("requestNonce",json!(null)),
            ("hostSha256",json!("c".repeat(64))),("configSha256",json!("c".repeat(64)))] {
            let mut bad=good.clone();bad[key]=value;assert!(checked_operator(&rt.config,&serde_json::to_vec(&bad).unwrap()).is_err(),"{key}");
        }
        // A public transport has no private status control; source CLI failure
        // is propagated before any kernel call, counter, reserve or model.
        rt.config.host_socket=Some(root.join("mini.sock"));
        rt.config.mini=root.join("mini");fs::write(&rt.config.mini,"#!/bin/sh\nprintf 'operation unavailable on selected socket\\n' >&2\nexit 1\n").unwrap();
        fs::set_permissions(&rt.config.mini,fs::Permissions::from_mode(0o700)).unwrap();
        let before=serde_json::to_value(&rt.journal).unwrap();
        assert!(require_private_operator(&rt.config).unwrap_err().contains("private operator"));
        assert_eq!(serde_json::to_value(&rt.journal).unwrap(),before);
        fs::remove_dir_all(root).unwrap();
    }
    #[test]
    fn source_preadmission_refusal_survives_lost_completion_without_work_or_invented_origin() {
        let (root,mut rt)=crate::tests::restart_resolution_fixture("preadmission-source-refusal");
        rt.journal.workspace_attempt=None;rt.journal.tool_hold=None;rt.journal.connection=Connection::Soft;
        rt.config.commands.clear();
        let before=serde_json::to_value(&rt.journal).unwrap();let disk=fs::read(rt.config.state_dir.join("journal.json")).unwrap();
        let id="a".repeat(64);let text="exact current request";let sha=sha256_bytes(text.as_bytes()).unwrap();
        assert!(rt.resident_admission(&id,&sha).unwrap()["type"]=="mini-resident-prompt-admission-unrecorded-v1");
        fixture_retain_preparation(&rt,&id,&sha);
        let (_sender,input)=mpsc::channel();
        assert!(rt.hermes_session(hermes_session_verify::Invocation::ResidentPrompt{prompt:text,resident_id:&id,digest:&sha},&input)
            .unwrap_err().contains("refused before admission"));
        assert_eq!(serde_json::to_value(&rt.journal).unwrap(),before);
        assert_eq!(fs::read(rt.config.state_dir.join("journal.json")).unwrap(),disk);
        let proof=rt.resident_admission(&id,&sha).unwrap();
        assert_eq!(proof["admitted"],false);assert_eq!(proof["effects"],"none");assert_eq!(proof["modelRequests"],0);
        assert!(rt.journal.resident_prompt_origin.is_none());
        assert!(rt.resident_admission(&id,&"b".repeat(64)).is_err());
        let mut wrong=proof.clone();wrong["bindingSha256"]=json!("b".repeat(64));
        assert!(check_refusal(&rt.config,&rt.config_path,&id,&sha,wrong).is_err());
        // A retained admitted origin categorically defeats preadmission proof.
        let origin=rt.config.state_dir.join(format!("resident-origin-id-{id}.json"));fs::write(&origin,"retained admission").unwrap();
        assert!(rt.resident_admission(&id,&sha).is_err());
        assert!(rt.record_resident_preadmission_refusal(&id,&sha,text,"not admitted").is_err());
        fs::remove_dir_all(root).unwrap();
    }
    #[test]
    fn entered_before_reserve_cut_and_old_unprepared_ids_cannot_mint_zero_effects_proof() {
        let (root,mut rt)=crate::tests::restart_resolution_fixture("resident-entry-fence");
        let text="retained exact request";let sha=sha256_bytes(text.as_bytes()).unwrap();let old="a".repeat(64);let id="b".repeat(64);
        // Existing unknown work from before this protocol has no preparation.
        assert!(rt.record_resident_preadmission_refusal(&old,&sha,text,"retained work").is_err());
        assert!(rt.resident_admission(&old,&sha).unwrap()["type"]=="mini-resident-prompt-admission-unrecorded-v1");
        rt.journal.workspace_attempt=None;rt.journal.tool_hold=None;rt.journal.connection=Connection::Soft;
        assert!(rt.record_resident_preadmission_refusal(&old,&sha,text,"old marker now cleared").is_err());
        fixture_retain_preparation(&rt,&id,&sha);rt.enter_resident_prompt(&id,&sha).unwrap();
        let entered=fs::read(entered_path(&rt.config,&id)).unwrap();
        assert!(rt.journal.resident_prompt_origin.is_none(),"entry fence precedes admitted origin and first reserve");
        assert!(rt.record_resident_preadmission_refusal(&id,&sha,text,"gate changed").unwrap_err().contains("entered"));
        assert!(rt.enter_resident_prompt(&id,&sha).is_err());
        let (_sender,input)=mpsc::channel();
        assert!(rt.hermes_session(hermes_session_verify::Invocation::ResidentPrompt{prompt:text,resident_id:&id,digest:&sha},&input)
            .unwrap_err().contains("previously entered"));
        assert_eq!(fs::read(entered_path(&rt.config,&id)).unwrap(),entered);
        assert!(!refusal_path(&rt.config,&id).exists());
        fs::remove_dir_all(root).unwrap();
    }
    #[test]
    fn source_preparation_issues_fresh_ids_only_after_private_role_and_quiescent_preflight() {
        let (root,mut rt)=crate::tests::restart_resolution_fixture("resident-source-issuance");
        let sha="a".repeat(64);assert!(rt.prepare_resident_prompt(&sha).is_err());
        rt.journal.workspace_attempt=None;rt.journal.tool_hold=None;rt.journal.connection=Connection::Soft;
        rt.config.host=root.join("host-image");rt.config.host_config=root.join("host-config");rt.config.host_socket=Some(root.join("operator.sock"));
        fs::write(&rt.config.host,"exact host").unwrap();fs::write(&rt.config.host_config,"exact config").unwrap();
        rt.config.commands=vec![serde_json::from_value(json!({"name":"hermes-acp","program":"/confined/bwrap",
            "args":["/agent/hermes-acp"],"reserve":"1","charge":"1","systemdScope":false})).unwrap()];
        let status=json!({"format":"mini-operator-drain-v1","phase":"serving","admissionClosed":false,"drained":false,
            "processId":1,"hostProcessId":2,"instanceId":"b".repeat(64),"requestNonce":"c".repeat(64),
            "hostSha256":sha256_file(&rt.config.host).unwrap(),"configSha256":sha256_file(&rt.config.host_config).unwrap()});
        rt.config.mini=root.join("mini");fs::write(&rt.config.mini,format!("#!/bin/sh\ncat <<'STATUS'\n{status}\nSTATUS\n")).unwrap();
        fs::set_permissions(&rt.config.mini,fs::Permissions::from_mode(0o700)).unwrap();
        let first=rt.prepare_resident_prompt(&sha).unwrap();let second=rt.prepare_resident_prompt(&sha).unwrap();
        let a=check_preparation(&rt.config,&rt.config_path,&sha,&first).unwrap();
        let b=check_preparation(&rt.config,&rt.config_path,&sha,&second).unwrap();assert_ne!(a,b);
        rt.retained_preparation(&a,&sha).unwrap();rt.retained_preparation(&b,&sha).unwrap();
        let mut wrong=first;wrong["residentPromptId"]=json!("old-user-chosen-id");assert!(check_preparation(&rt.config,&rt.config_path,&sha,&wrong).is_err());
        assert!(rt.prepare_resident_prompt("old-id sha").is_err());
        assert!(!entered_path(&rt.config,&a).exists());assert!(!entered_path(&rt.config,&b).exists());
        fs::remove_dir_all(root).unwrap();
    }
    #[test]
    fn bad_service_preflight_never_mutates_native_journal_or_request_counts() {
        let (root,mut rt)=crate::tests::restart_resolution_fixture("preflight-no-work");
        assert!(rt.preflight_resident_prompt().unwrap_err().contains("recovery"));
        rt.journal.workspace_attempt=None;rt.journal.tool_hold=None;rt.journal.connection=Connection::Soft;
        rt.config.commands.push(serde_json::from_value(json!({"name":"hermes-acp","program":"/unconfined/program",
            "args":["/agent/hermes-acp"],"reserve":"1","charge":"1"})).unwrap());
        let before=serde_json::to_value(&rt.journal).unwrap();let bytes=fs::read(rt.config.state_dir.join("journal.json")).unwrap();
        assert!(rt.preflight_resident_prompt().unwrap_err().contains("confined"));
        assert_eq!(serde_json::to_value(&rt.journal).unwrap(),before);
        assert_eq!(fs::read(rt.config.state_dir.join("journal.json")).unwrap(),bytes);
        fs::remove_dir_all(root).unwrap();
    }
}
