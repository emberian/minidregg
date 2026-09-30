//! Per-request application coordinates for Mini lifecycle authoring.
//!
//! The Host pins one lifecycle management identity (`lifecycleManagement`:
//! subject and key) and no application. Every lifecycle authoring call
//! (ops 44/50/52/66/68/70) is framed as `(selector JSON, request)`. The
//! selector confers nothing: Mini's receiver checks the application's current
//! law, which names its package and snapshot manifests and the management
//! subject, and admits the named capabilities against current authority.
//! Custody here only refuses to sign for a different management identity.

use crate::dispatch_author::SignerPin;
use crate::dispatch_native::PrivateOperator;
use serde::{Deserialize, Serialize};
use serde_json::Value;
use std::io;

fn invalid(reason: &'static str) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidData, reason)
}

pub(crate) fn decimal(value: &str) -> bool {
    !value.is_empty()
        && value.len() <= 78
        && (value == "0" || !value.starts_with('0'))
        && value.bytes().all(|byte| byte.is_ascii_digit())
}

/// Exactly the Lean `LifecycleSelector` fields, as canonical decimal strings.
#[derive(Clone, Debug, Deserialize, Serialize, PartialEq, Eq)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub(crate) struct LifecycleSelector {
    pub app: String,
    pub package_manifest: String,
    pub snapshot_manifest: String,
    pub app_capability: String,
    pub app_observe_capability: String,
    pub package_capability: String,
    pub package_observe_capability: String,
}

impl LifecycleSelector {
    pub(crate) fn validate(&self) -> io::Result<()> {
        let fields = [
            &self.app,
            &self.package_manifest,
            &self.snapshot_manifest,
            &self.app_capability,
            &self.app_observe_capability,
            &self.package_capability,
            &self.package_observe_capability,
        ];
        if !fields.iter().all(|value| decimal(value) && *value != "0")
            || self.app == self.package_manifest
            || self.app == self.snapshot_manifest
            || self.package_manifest == self.snapshot_manifest
        {
            return Err(invalid("lifecycle selector coordinates refused"));
        }
        Ok(())
    }

    /// `LE32(len(selector)) || selector || request`, the Host's `splitPair`.
    pub(crate) fn framed(&self, request: &[u8]) -> io::Result<Vec<u8>> {
        self.validate()?;
        let selector = serde_json::to_vec(self)?;
        let width = u32::try_from(selector.len())
            .map_err(|_| invalid("lifecycle selector exceeds frame width"))?;
        if selector.len() > 4096 {
            return Err(invalid("lifecycle selector exceeds Host bound"));
        }
        let mut framed = Vec::with_capacity(4 + selector.len() + request.len());
        framed.extend_from_slice(&width.to_le_bytes());
        framed.extend_from_slice(&selector);
        framed.extend_from_slice(request);
        Ok(framed)
    }
}

fn config_decimal(value: &Value) -> Option<String> {
    value
        .as_str()
        .map(str::to_owned)
        .or_else(|| value.as_u64().map(|number| number.to_string()))
}

/// The Host-pinned lifecycle management identity from the exact pinned Mini
/// config the operator socket serves.
pub(crate) fn pinned_management(operator: &PrivateOperator) -> io::Result<(String, String)> {
    let config: Value = serde_json::from_slice(&operator.pinned_config()?)?;
    for legacy in [
        "completionManagement",
        "residentBeginManagement",
        "residentClaimManagement",
    ] {
        if config.get(legacy).is_some() {
            return Err(invalid(
                "Mini config carries a legacy single-application lifecycle pin",
            ));
        }
    }
    let management = config
        .get("lifecycleManagement")
        .ok_or_else(|| invalid("Mini lifecycle management identity absent"))?;
    let subject = management
        .get("managementSubject")
        .and_then(config_decimal)
        .ok_or_else(|| invalid("Mini lifecycle management subject malformed"))?;
    let key = management
        .get("managementKeyId")
        .and_then(config_decimal)
        .ok_or_else(|| invalid("Mini lifecycle management key malformed"))?;
    Ok((subject, key))
}

/// Shared custody check: the selector is well formed, the custody's
/// management subject and every signer key equal the Host pin, and each seed
/// lives below an ancestor chain the app UID cannot rewrite.
pub(crate) fn validate_custody(
    operator: &PrivateOperator,
    selector: &LifecycleSelector,
    management_subject: &str,
    signers: &[SignerPin],
    app_uid: u32,
) -> io::Result<()> {
    selector.validate()?;
    if !decimal(management_subject) || signers.is_empty() || signers.len() > 64 {
        return Err(invalid("lifecycle management custody refused"));
    }
    let (subject, key_id) = pinned_management(operator)?;
    if subject != management_subject {
        return Err(invalid("lifecycle custody subject differs from Mini pin"));
    }
    for signer in signers {
        if signer.key_id != key_id {
            return Err(invalid("lifecycle signer key differs from Mini pin"));
        }
        crate::sandbox::open_protected_directory(
            signer
                .seed_path
                .parent()
                .ok_or_else(|| invalid("lifecycle signer parent absent"))?,
            app_uid,
            false,
        )?;
    }
    Ok(())
}

#[cfg(test)]
pub(crate) fn test_selector(app: &str, package: &str, snapshot: &str) -> LifecycleSelector {
    LifecycleSelector {
        app: app.into(),
        package_manifest: package.into(),
        snapshot_manifest: snapshot.into(),
        app_capability: "141".into(),
        app_observe_capability: "141".into(),
        package_capability: "143".into(),
        package_observe_capability: "143".into(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn selector_frame_is_host_split_pair() {
        let selector = test_selector("8401", "8402", "8403");
        let framed = selector.framed(b"request").unwrap();
        let width = u32::from_le_bytes(framed[..4].try_into().unwrap()) as usize;
        let parsed: LifecycleSelector = serde_json::from_slice(&framed[4..4 + width]).unwrap();
        assert_eq!(parsed, selector);
        assert_eq!(&framed[4 + width..], b"request");
    }

    #[test]
    fn selector_refuses_noncanonical_or_aliased_coordinates() {
        let mut selector = test_selector("8401", "8402", "8403");
        selector.app = "08401".into();
        assert!(selector.validate().is_err());
        let mut selector = test_selector("8401", "8401", "8403");
        assert!(selector.validate().is_err());
        selector.package_manifest = "8402".into();
        selector.validate().unwrap();
        selector.app_capability = "0".into();
        assert!(selector.validate().is_err());
        let unknown = r#"{"app":"1","packageManifest":"2","snapshotManifest":"3","appCapability":"4","appObserveCapability":"4","packageCapability":"5","packageObserveCapability":"5","extra":"6"}"#;
        assert!(serde_json::from_str::<LifecycleSelector>(unknown).is_err());
    }
}
