//! Read-only source preflight before a resident marks its request started.
//! Actual prompt admission still repeats these checks. This cannot clear a
//! started/unknown request or authorize a model, payment, or native effect.
use crate::*;

#[derive(Deserialize)]
#[serde(rename_all="camelCase",deny_unknown_fields)]
struct Ready {
    #[serde(rename="type")]
    kind:String,
    task:String,
    config_sha256:String,
    binding_sha256:String,
}
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
fn checked(config:&Config,path:&Path,text:&str)->Result<()> {
    let ready:Ready=serde_json::from_str(text).map_err(|_|format!("resident preflight refused before prompt dispatch: {text}"))?;
    if ready.kind!="mini-resident-preflight-ready-v1" || ready.task!=config.task
        || ready.config_sha256!=config_digest(config)? || ready.binding_sha256!=binding_digest(config,path)? {
        return Err("resident preflight differs from exact controller configuration".into());
    }
    Ok(())
}
pub(crate) fn require(config:&Config,path:&Path)->Result<()> {
    let text=control::admin_call(&config.state_dir.join("admin.sock"),"resident preflight")?;
    checked(config,path,&text)
}
impl Runtime {
    pub(crate) fn preflight_resident_prompt(&self)->Result<Value> {
        config_migration::ensure_process_current(&self.config.state_dir)?;
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
        response(&self.config,&self.config_path)
    }
}
#[cfg(test)]
pub(crate) fn fixture_response(config:&Config,path:&Path)->Value {response(config,path).unwrap()}
#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn preflight_refusal_and_substitution_do_not_grant_prompt_admission() {
        let (root,rt)=crate::tests::restart_resolution_fixture("preflight-identity");
        let good=fixture_response(&rt.config,&rt.config_path);
        checked(&rt.config,&rt.config_path,&good.to_string()).unwrap();
        for key in ["task","configSha256","bindingSha256","type"] {
            let mut v=good.clone();v[key]=json!("different");
            assert!(checked(&rt.config,&rt.config_path,&v.to_string()).is_err());
        }
        assert!(checked(&rt.config,&rt.config_path,"error: launcher protocol absent").is_err());
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
