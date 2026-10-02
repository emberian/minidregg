//! Public credential write paths selected by the runtime's own provider parser.
//! This command is a scope description, not native authority or a closed checkpoint.
use crate::*;

pub(crate) fn describe_config(path: &Path, bytes: &[u8], config: &Config) -> Result<Value> {
    if !minidregg_compatible_upgrade_custody::canonical(path) {
        return Err("controller scope config path must be canonical absolute".into());
    }
    let binding = json!({"config":config,"configPath":path});
    let mut value = json!({"type":"mini-controller-write-scopes-v1", "configPath":path,
        "configSha256":sha256_bytes(bytes)?,
        "bindingSha256":sha256_bytes(&serde_json::to_vec(&binding).map_err(|e|e.to_string())?)?,
        "task":config.task,"credentialsRoot":null,"providerTableSha256":null,
        "provider":null,"route":null,"credentialWriteDirectories":[]});
    if let Some(task) = &config.provider_task {
        if !minidregg_compatible_upgrade_custody::canonical(&task.credentials_root) {
            return Err("credential root must be canonical absolute".into());
        }
        let table = credentials::ProviderTable::load(&task.providers, 0)?;
        let row = provider_task_row(task, &table)?;
        let directories = selected_directories(
            &task.credentials_root,
            row.credential,
            task.on_behalf_of
                .as_ref()
                .map(|o| (o.subject.as_str(), o.public_key.as_str())),
        )?;
        value["credentialsRoot"] = json!(task.credentials_root);
        value["providerTableSha256"] = json!(table.sha256);
        value["provider"] = json!(row.name);
        value["route"] = json!(row.credential.route());
        value["credentialWriteDirectories"] = json!(directories);
    }
    Ok(value)
}
fn selected_directories(
    root: &Path,
    route: credentials::CredentialSource,
    owner: Option<(&str, &str)>,
) -> Result<Vec<PathBuf>> {
    use credentials::{CredentialSource, Namespace, Owner};
    match route {
        CredentialSource::User => {
            let (subject, key) = owner.ok_or("member credential route requires a bound owner")?;
            let owner = Owner::new(subject, key)?;
            Ok(vec![credentials::namespace_path(
                root,
                Namespace::Owner(&owner),
            )?])
        }
        CredentialSource::Pool => Ok(vec![credentials::namespace_path(root, Namespace::Pool)?]),
        CredentialSource::Homelab => Ok(vec![]),
    }
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
#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn only_selected_namespace_is_writable() {
        let root = Path::new("/var/lib/mini/credentials");
        let key = "ab".repeat(32);
        assert_eq!(
            selected_directories(
                root,
                credentials::CredentialSource::User,
                Some(("20", &key))
            )
            .unwrap(),
            vec![root.join("20").join(&key)]
        );
        assert_eq!(
            selected_directories(root, credentials::CredentialSource::Pool, None).unwrap(),
            vec![credentials::namespace_path(root, credentials::Namespace::Pool).unwrap()]
        );
        assert!(
            selected_directories(root, credentials::CredentialSource::Homelab, None)
                .unwrap()
                .is_empty()
        );
        assert!(selected_directories(root, credentials::CredentialSource::User, None).is_err());
        assert!(selected_directories(
            root,
            credentials::CredentialSource::User,
            Some(("../20", &key))
        )
        .is_err());
    }
    #[test]
    fn namespace_derivation_never_reads_secret_or_creates_paths() {
        let root = std::env::temp_dir().join(format!("mini-pure-scope-{}", std::process::id()));
        assert!(!root.exists());
        let key = "01".repeat(32);
        let dirs = selected_directories(
            &root,
            credentials::CredentialSource::User,
            Some(("20", &key)),
        )
        .unwrap();
        assert_eq!(dirs, vec![root.join("20").join(&key)]);
        assert!(!root.exists());
    }
}
