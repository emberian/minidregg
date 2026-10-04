//! Public credential write paths selected by the runtime's own provider parser.
//! This command is a scope description, not native authority or a closed checkpoint.
use crate::*;

/// v2: a controller writes no credential path. The key broker (mini-keys)
/// owns the sealed store and its day counters; the controller names only the
/// broker it asks (`credentialBroker`) and the route its table row selects.
pub(crate) fn describe_config(path: &Path, bytes: &[u8], config: &Config) -> Result<Value> {
    if !minidregg_compatible_upgrade_custody::canonical(path) {
        return Err("controller scope config path must be canonical absolute".into());
    }
    let binding = json!({"config":config,"configPath":path});
    let mut value = json!({"type":"mini-controller-write-scopes-v2", "configPath":path,
        "configSha256":sha256_bytes(bytes)?,
        "bindingSha256":sha256_bytes(&serde_json::to_vec(&binding).map_err(|e|e.to_string())?)?,
        "task":config.task,"credentialBroker":null,"providerTableSha256":null,
        "provider":null,"route":null});
    if let Some(task) = &config.provider_task {
        if !minidregg_compatible_upgrade_custody::canonical(&task.credential_broker) {
            return Err("credentialBroker must be canonical absolute".into());
        }
        let table = credentials::ProviderTable::load(&task.providers, 0)?;
        let row = provider_task_row(task, &table)?;
        value["credentialBroker"] = json!(task.credential_broker);
        value["providerTableSha256"] = json!(table.sha256);
        value["provider"] = json!(row.name);
        value["route"] = json!(row.credential.route());
    }
    Ok(value)
}
pub(crate) fn client(args: &[std::ffi::OsString]) -> Result<()> {
    let value = match args {
        [config] => {
            let path=Path::new(config);
            let (bytes,parsed)=config_migration::scope_config(path)?;
            describe_config(path,&bytes,&parsed)?
        }
        [mode,config,request] if mode=="preflight" =>
            config_migration::scope_preflight(Path::new(config),Path::new(request))?,
        [mode,config,request] if mode=="receipt" =>
            config_migration::scope_receipt(Path::new(config),Path::new(request))?,
        _ => return Err("usage: grain-runtime controller-write-scopes CONFIG | controller-write-scopes preflight CONFIG REQUEST | controller-write-scopes receipt CONFIG REQUEST".into()),
    };
    println!("{value}");
    Ok(())
}
