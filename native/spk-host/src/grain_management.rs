//! Explicit member-to-host lifecycle selectors. This file does not grant
//! authority: current Mini policy, delegated capabilities and signatures remain
//! the only admission boundary for BEGIN, claim and completion.
use crate::lifecycle_selector::{decimal, LifecycleSelector};
use serde::{Deserialize, Serialize};
use std::io;

#[derive(Debug, Deserialize, Serialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub(super) struct Delegation {
    protocol: String,
    app_owner: String,
    management_subject: String,
    selector: LifecycleSelector,
    // Retained for snapshot operations; install/start/stop do not consume them.
    snapshot_capability: String,
    snapshot_observe_capability: String,
}

pub(super) fn select(
    bytes: &[u8],
    admitted: &LifecycleSelector,
    owner: &str,
    manager: &str,
) -> io::Result<LifecycleSelector> {
    let delegation: Delegation = serde_json::from_slice(bytes)?;
    delegation.selector.validate()?;
    let s = &delegation.selector;
    let capabilities = [
        &delegation.snapshot_capability,
        &delegation.snapshot_observe_capability,
    ];
    if delegation.protocol != "mini-spk-grain-lifecycle-delegation-v1"
        || delegation.app_owner != owner
        || delegation.management_subject != manager
        || !decimal(&delegation.app_owner)
        || !decimal(&delegation.management_subject)
        || !capabilities.iter().all(|v| decimal(v) && v.as_str() != "0")
        || s.app != admitted.app
        || s.package_manifest != admitted.package_manifest
        || s.snapshot_manifest != admitted.snapshot_manifest
        || s.app_capability == admitted.app_capability
        || s.package_capability == admitted.package_capability
        || s.app_capability == s.package_capability
        || s.app_capability == delegation.snapshot_capability
        || s.package_capability == delegation.snapshot_capability
    {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            "lifecycle delegation differs from application birth or host manager",
        ));
    }
    Ok(delegation.selector)
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::{json, Value};

    fn request() -> Value {
        json!({"protocol":"mini-spk-grain-lifecycle-delegation-v1",
            "appOwner":"12648853121532543039", "managementSubject":"8",
            "selector":{"app":"530101","packageManifest":"530102","snapshotManifest":"530103",
                "appCapability":"976001","appObserveCapability":"976001",
                "packageCapability":"976002","packageObserveCapability":"976002"},
            "snapshotCapability":"976003","snapshotObserveCapability":"976003"})
    }
    fn admitted() -> LifecycleSelector {
        LifecycleSelector {
            app: "530101".into(),
            package_manifest: "530102".into(),
            snapshot_manifest: "530103".into(),
            app_capability: "960000".into(),
            app_observe_capability: "960000".into(),
            package_capability: "960002".into(),
            package_observe_capability: "960002".into(),
        }
    }
    fn check(request: &Value) -> io::Result<LifecycleSelector> {
        select(
            &serde_json::to_vec(request).unwrap(),
            &admitted(),
            "12648853121532543039",
            "8",
        )
    }
    #[test]
    fn member_identity_remains_distinct_from_host_lifecycle_capabilities() {
        let s = check(&request()).unwrap();
        assert_eq!(s.app, "530101");
        assert_eq!(s.app_capability, "976001");
    }
    #[test]
    fn canonical_zero_subjects_are_not_capability_zero() {
        let mut r = request();
        r["appOwner"] = "0".into();
        assert!(select(&serde_json::to_vec(&r).unwrap(), &admitted(), "0", "8").is_ok());
        r["managementSubject"] = "0".into();
        assert!(select(&serde_json::to_vec(&r).unwrap(), &admitted(), "0", "0").is_ok());
        r["snapshotCapability"] = "0".into();
        assert!(select(&serde_json::to_vec(&r).unwrap(), &admitted(), "0", "0").is_err());
    }
    #[test]
    fn wrong_owner_manager_or_resources_refuse() {
        for (section, field, value) in [
            ("", "appOwner", "8"),
            ("", "managementSubject", "7"),
            ("selector", "app", "531101"),
            ("selector", "packageManifest", "530104"),
            ("selector", "snapshotManifest", "530105"),
        ] {
            let mut r = request();
            let parent = if section.is_empty() {
                &mut r
            } else {
                &mut r[section]
            };
            parent[field] = value.into();
            assert!(check(&r).is_err(), "{section}.{field}");
        }
    }
    #[test]
    fn parent_capabilities_and_cross_resource_aliases_refuse() {
        for (field, value) in [
            ("appCapability", "960000"),
            ("packageCapability", "960002"),
            ("packageCapability", "976001"),
            ("appCapability", "976003"),
        ] {
            let mut r = request();
            r["selector"][field] = value.into();
            assert!(check(&r).is_err());
        }
    }
    #[test]
    fn unknown_authority_fields_and_noncanonical_numbers_refuse() {
        let mut r = request();
        r["operatorMayDelegate"] = true.into();
        assert!(check(&r).is_err());
        for value in ["0", "08", "-1", "not-a-cap"] {
            let mut r = request();
            r["snapshotCapability"] = value.into();
            assert!(check(&r).is_err());
        }
    }
}
