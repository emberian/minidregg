//! Lossless role-relevant ViewInfo projection for Lean canonical authoring.
//! This is app-supplied descriptor input, not an effective permission grant.
use crate::ViewInfo;
use serde_json::{json, Value};
use std::collections::HashSet;

const MAX_DEFINITIONS: usize = 256;
const MAX_SOURCE_BYTES: usize = 1024 * 1024;

fn bounded(info: &ViewInfo, version: u64) -> Result<(), String> {
    if version == 0
        || info.permissions.len() > MAX_DEFINITIONS
        || info.roles.len() > MAX_DEFINITIONS
    {
        return Err("invalid schema version or definition count".into());
    }
    if info.denied_permissions.len() > info.permissions.len()
        || info
            .roles
            .iter()
            .any(|role| role.permissions.len() > info.permissions.len())
    {
        return Err("permission bitset exceeds definition count".into());
    }
    let mut names = HashSet::new();
    for permission in &info.permissions {
        let name = permission.name.as_bytes();
        if name.is_empty()
            || name.len() > 256
            || !name[0].is_ascii_alphabetic()
            || !name.iter().all(u8::is_ascii_alphanumeric)
            || !names.insert(&permission.name)
        {
            return Err("invalid or duplicate permission name".into());
        }
    }
    if info.roles.iter().filter(|role| role.default).count() > 1 {
        return Err("multiple default roles are ambiguous".into());
    }
    Ok(())
}

/// Projects the exact ordered role-relevant fields from a captured Cap'n Proto
/// ViewInfo. `version` is an explicit controller input because Sandstorm's
/// ViewInfo does not contain a schema version. The resulting JSON must be
/// parsed/validated by Lean's authoring route; this Rust value has no authority.
pub fn permission_schema_source(info: &ViewInfo, version: u64) -> Result<Value, String> {
    bounded(info, version)?;
    Ok(json!({
        "type": "minidregg-application-permission-schema-source-v1",
        "version": version.to_string(),
        "permissions": info.permissions.iter().map(|p| json!({
            "name": p.name,
            "obsolete": p.obsolete,
        })).collect::<Vec<_>>(),
        "roles": info.roles.iter().map(|r| json!({
            "permissions": r.permissions,
            "obsolete": r.obsolete,
            "default": r.default,
        })).collect::<Vec<_>>(),
        "denied": info.denied_permissions,
    }))
}

/// A bounded transport notation; canonical bytes/root are authored by Lean.
pub fn permission_schema_source_bytes(info: &ViewInfo, version: u64) -> Result<Vec<u8>, String> {
    let bytes = serde_json::to_vec(&permission_schema_source(info, version)?)
        .map_err(|error| error.to_string())?;
    if bytes.len() > MAX_SOURCE_BYTES {
        return Err("permission schema source exceeds byte bound".into());
    }
    Ok(bytes)
}
