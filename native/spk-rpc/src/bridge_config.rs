//! Bounded projection of one already-verified signed bridge-config member.
//!
//! Parsing does not verify the SPK signature or authorize a session. The
//! materializer must supply the exact member from its single verified tree.

use crate::{package_rust_capnp, protocol::decode_view_info, ViewInfo};

const MAX_MEMBER_BYTES: usize = 64 * 1024;
const MAX_API_PATH_BYTES: usize = 4096;

#[derive(Debug, PartialEq, Eq)]
pub struct BridgeConfig {
    pub view_info: ViewInfo,
    /// `None` means the signed package defines no legacy API path.
    pub api_path: Option<String>,
    pub save_identity_caps: bool,
    pub expect_app_hooks: bool,
}

/// Decode one exact, unpacked Cap'n Proto `BridgeConfig` message. Trailing
/// bytes and unsupported Powerbox APIs are refused rather than silently
/// omitted from a Mini interface descriptor.
pub fn decode_bridge_config(member: &[u8]) -> Result<BridgeConfig, String> {
    if member.is_empty() || member.len() > MAX_MEMBER_BYTES {
        return Err("bridge-config member is empty or exceeds 64 KiB".into());
    }
    let mut unread = member;
    let options = capnp::message::ReaderOptions {
        traversal_limit_in_words: Some(MAX_MEMBER_BYTES / 8),
        nesting_limit: 64,
    };
    let message = capnp::serialize::read_message_from_flat_slice(&mut unread, options)
        .map_err(|error| format!("invalid bridge-config frame: {error}"))?;
    if !unread.is_empty() {
        return Err("bridge-config member has trailing bytes".into());
    }
    let config = message
        .get_root::<package_rust_capnp::bridge_config::Reader<'_>>()
        .map_err(|error| format!("invalid bridge-config root: {error}"))?;
    let view_info = decode_view_info(
        config
            .get_view_info()
            .map_err(|error| format!("invalid bridge ViewInfo: {error}"))?,
    )
    .map_err(|error| format!("invalid bridge ViewInfo: {error}"))?;
    let api_path = config
        .get_api_path()
        .map_err(|error| format!("invalid bridge apiPath: {error}"))?
        .to_str()
        .map_err(|error| format!("invalid bridge apiPath UTF-8: {error}"))?;
    if api_path.len() > MAX_API_PATH_BYTES || api_path.contains('\0') {
        return Err("bridge apiPath exceeds bound or contains NUL".into());
    }
    let api_path = if api_path.is_empty() {
        None
    } else if api_path.starts_with('/') && api_path.ends_with('/') {
        Some(api_path.to_owned())
    } else {
        return Err("bridge apiPath must start and end with '/'".into());
    };
    let powerbox_apis = config
        .get_powerbox_apis()
        .map_err(|error| format!("invalid bridge powerboxApis: {error}"))?;
    if !powerbox_apis.is_empty() {
        return Err("powerbox APIs need a separate interface descriptor route".into());
    }
    Ok(BridgeConfig {
        view_info,
        api_path,
        save_identity_caps: config.get_save_identity_caps(),
        expect_app_hooks: config.get_expect_app_hooks(),
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    // Extracted from one verified GitWeb SPK by the host materializer lane.
    // SHA-256 49d196f64ca2ce672a378581a8376ada53b27614bba522bbaec042237f0e70a2.
    const GITWEB: &[u8] = include_bytes!("../tests/fixtures/gitweb-signed-bridge-config.capnp");

    #[test]
    fn signed_gitweb_member_has_ordered_schema_and_legacy_api_path() {
        let config = decode_bridge_config(GITWEB).unwrap();
        assert_eq!(config.view_info.permission_names, ["read", "write"]);
        assert_eq!(config.view_info.roles.len(), 2);
        assert_eq!(config.view_info.roles[0].title.default_text, "guest");
        assert_eq!(config.view_info.roles[0].permissions, [true, false]);
        assert!(!config.view_info.roles[0].default);
        assert_eq!(config.view_info.roles[1].title.default_text, "developer");
        assert_eq!(config.view_info.roles[1].permissions, [true, true]);
        assert!(config.view_info.roles[1].default);
        assert!(config.view_info.denied_permissions.is_empty());
        assert_eq!(config.api_path.as_deref(), Some("/repo.git/"));
        assert!(!config.save_identity_caps);
        assert!(!config.expect_app_hooks);
    }

    #[test]
    fn frame_is_exact_and_bounded() {
        let mut trailing = GITWEB.to_vec();
        trailing.extend_from_slice(&[0; 8]);
        assert!(decode_bridge_config(&trailing).is_err());
        assert!(decode_bridge_config(&vec![0; MAX_MEMBER_BYTES + 1]).is_err());
        assert!(decode_bridge_config(&GITWEB[..GITWEB.len() - 1]).is_err());
    }
}
