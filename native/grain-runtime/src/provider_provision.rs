//! Consume an authenticated member choice into one immutable fresh controller.
//! Normal controller startup and source admission remain the execution path.
use crate::*;

fn digest(bytes: &[u8]) -> String {
    use sha2::Digest;
    sha2::Sha256::digest(bytes)
        .iter()
        .map(|b| format!("{b:02x}"))
        .collect()
}
fn exact(value: &Value, keys: &[&str]) -> Result<()> {
    let obj = value
        .as_object()
        .ok_or("provider provisioning policy must be an object")?;
    if obj.keys().any(|key| !keys.contains(&key.as_str())) {
        return Err("unknown provider provisioning policy field".into());
    }
    Ok(())
}
fn policy(path: &Path, template: &[u8], choice: &credentials::choice::Choice) -> Result<Value> {
    let meta = fs::symlink_metadata(path).map_err(|_| "provisioning policy unavailable")?;
    if !meta.is_file()
        || meta.uid() != 0
        || meta.permissions().mode() & 0o022 != 0
        || meta.len() > 65536
    {
        return Err(
            "provisioning policy must be a root-owned regular file, not group/world writable"
                .into(),
        );
    }
    let value: Value = serde_json::from_slice(&bounded_regular_file(path, 65536)?)
        .map_err(|_| "provisioning policy invalid")?;
    exact(&value, &["type", "templateSha256", "routes"])?;
    if value["type"] != "mini-member-provider-provision-v1"
        || value["templateSha256"] != digest(template)
    {
        return Err("provisioning policy does not pin this template".into());
    }
    let rows = value["routes"]
        .as_array()
        .filter(|r| !r.is_empty() && r.len() <= 32)
        .ok_or("provisioning policy needs 1..32 routes")?;
    let mut allowed = false;
    for row in rows {
        exact(row, &["provider", "models"])?;
        let models = row["models"]
            .as_array()
            .filter(|m| !m.is_empty() && m.len() <= 64)
            .ok_or("provisioning model list invalid")?;
        if models.iter().any(|m| m.as_str().is_none()) {
            return Err("provisioning models must be strings".into());
        }
        if row["provider"] == choice.provider && models.iter().any(|m| m == &choice.model) {
            allowed = true;
        }
    }
    if !allowed {
        return Err("member choice is outside the operator's provisioning routes/models".into());
    }
    Ok(value)
}
fn fresh(view: &Value, task: &str) -> Result<()> {
    let grain = &view["grain"];
    if grain["task"] != task
        || ["generation", "status", "reserved"]
            .iter()
            .any(|field| grain[field].as_str() != Some("0"))
    {
        return Err("provider provisioning requires never-attached source tasks (generation/status/reserved 0); use the existing controller or a new source lifecycle".into());
    }
    Ok(())
}
fn query_only(journal: &Journal) -> Result<()> {
    let mut current = serde_json::to_value(journal).map_err(|e| e.to_string())?;
    let mut initial =
        serde_json::to_value(Journal::fresh(journal.binding.clone())).map_err(|e| e.to_string())?;
    current.as_object_mut().unwrap().remove("nextOperationId");
    initial.as_object_mut().unwrap().remove("nextOperationId");
    if current != initial {
        return Err("provisioning state has execution history; it cannot be rebound".into());
    }
    Ok(())
}

pub(crate) fn run(template: &Path, operator_policy: &Path, output: &Path) -> Result<Value> {
    if !output.is_absolute() {
        return Err("controller output path must be absolute".into());
    }
    let bytes = bounded_regular_file(template, 262144)?;
    let mut config: Config =
        serde_json::from_slice(&bytes).map_err(|e| format!("controller template: {e}"))?;
    let task = config
        .provider_task
        .as_mut()
        .ok_or("template needs providerTask")?;
    let pinned = task
        .on_behalf_of
        .as_ref()
        .ok_or("template needs pinned member onBehalfOf")?;
    let owner = credentials::Owner::new(&pinned.subject, &pinned.public_key)?;
    let table = credentials::ProviderTable::load(&task.providers, 0)?;
    let store = credentials::CredentialStore::open(&task.credentials_root, &task.credentials_key)?;
    let choice = store.selected(&owner, &task.subject, &task.task, &table)?;
    let policy = policy(operator_policy, &bytes, &choice)?;
    task.provider = Some(choice.provider.clone());
    task.model = choice.model.clone();
    validate(&config)?;
    if config.dispatch_task.is_some() {
        return Err(
            "member provider provisioning does not provision an application dispatch task".into(),
        );
    }
    let config_bytes = serde_json::to_vec_pretty(&config).map_err(|e| e.to_string())?;
    let intent = json!({"type":"mini-provider-provision-intent-v1","configSha256":digest(&config_bytes),
        "configPath":output,"choice":choice.to_json(),"choiceSha256":choice.digest(),"policy":policy});
    let intent_path = config.state_dir.join("provider-provision-intent.json");
    let complete_path = config.state_dir.join("provider-provision-complete.json");
    if output.exists() {
        let complete: Value =
            serde_json::from_slice(&bounded_regular_file(&complete_path, 262144)?)
                .map_err(|_| "completed provision evidence invalid")?;
        if complete["intent"] != intent || bounded_regular_file(output, 262144)? != config_bytes {
            return Err(
                "existing controller output differs from exact completed provisioning".into(),
            );
        }
        return Ok(
            json!({"type":"mini-provider-provisioned-v1","controller":output,"existing":true,"choiceSha256":choice.digest()}),
        );
    }
    match fs::DirBuilder::new().mode(0o700).create(&config.state_dir) {
        Ok(()) => write_new(&intent_path, &serde_json::to_vec_pretty(&intent).unwrap())?,
        Err(e) if e.kind() == io::ErrorKind::AlreadyExists => {
            let retained: Value =
                serde_json::from_slice(&bounded_regular_file(&intent_path, 262144)?)
                    .map_err(|_| "provisioning state is not an exact resumable intent")?;
            if retained != intent {
                return Err("state directory belongs to another provisioning or controller".into());
            }
        }
        Err(e) => return Err(format!("fresh controller state: {e}")),
    }
    // This opens the normal exclusive controller lock and binds the exact
    // selected config. Queries keep evidence in its real journal/attempts.
    let mut runtime = Runtime::open(config, output.to_owned())?;
    query_only(&runtime.journal)?;
    let provider = runtime
        .config
        .provider_task
        .as_ref()
        .ok_or("provider task absent")?;
    let profile = runtime.provider_native_profile()?;
    let tariff = select_provider_metering(&profile, &provider.task)?;
    let tariff_pin = provider_route_pin(tariff, provider, "user")?;
    let mut authorities = vec![("parent", runtime.parent())];
    if runtime.config.tool_task.is_some() {
        authorities.push(("tool", runtime.tool()?));
    }
    authorities.push(("provider", runtime.provider()?));
    let mut evidence = Vec::new();
    for (role, authority) in authorities {
        let view = runtime.query_as(&authority)?;
        fresh(&view, &authority.task)?;
        evidence.push(json!({"role":role,"view":view}));
    }
    query_only(&runtime.journal)?;
    let owner_proof = provider_owner::observe(&runtime.config, &owner.subject, &owner.public_key)?;
    let grant_proof = provider_owner::grant_evidence(&runtime.config, &owner_proof)?;
    let complete = json!({"type":"mini-provider-provision-complete-v1","intent":intent,"source":evidence,"tariff":tariff_pin,"ownerAuthority":owner_proof.evidence(),"grantAuthority":grant_proof});
    atomic_json(&complete_path, &complete)?;
    write_new(output, &config_bytes)?;
    if let Some(parent) = output.parent() {
        File::open(parent)
            .and_then(|f| f.sync_all())
            .map_err(|e| format!("controller publication sync: {e}"))?;
    }
    Ok(
        json!({"type":"mini-provider-provisioned-v1","controller":output,"existing":false,
        "choiceSha256":choice.digest(),"provider":choice.provider,"model":choice.model,
        "next":"Start this exact controller with grain-runtime serve; source and credential authority are rechecked on use."}),
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn detached_or_used_tasks_are_not_fresh_even_without_a_new_journal() {
        let initial = json!({"grain":{"task":"88","generation":"0","status":"0","reserved":"0","remaining":"5"}});
        assert!(fresh(&initial, "88").is_ok());
        for (field, value) in [
            ("generation", "1"),
            ("status", "1"),
            ("reserved", "1"),
            ("task", "89"),
        ] {
            let mut changed = initial.clone();
            changed["grain"][field] = json!(value);
            assert!(fresh(&changed, "88").is_err());
        }
        assert!(fresh(&json!({}), "88").is_err());
    }
    #[test]
    fn provisioning_resume_allows_queries_but_no_controller_history() {
        let mut journal = Journal::fresh(json!({"config":"pin"}));
        assert!(query_only(&journal).is_ok());
        journal.next_operation_id += 4;
        assert!(query_only(&journal).is_ok());
        journal.connection = Connection::Soft;
        assert!(query_only(&journal).is_err());
    }
}
