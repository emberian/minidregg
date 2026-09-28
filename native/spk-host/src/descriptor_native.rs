//! Source-authored descriptor from one signature-verified SPK parse.
//!
//! Rust supplies exact signed bytes and decoded bridge roles. Mini owns the
//! canonical schema, fixed web/API mapping and package root; the returned
//! bytes are compared to the physical parse before any BEGIN plan uses them.
#![allow(dead_code)] // Joined INSTALL/START resident caller follows native link.

use crate::dispatch_native::{private_dir, write_new, PrivateOperator};
use crate::materialize::{signed_schema_source, InstalledPackage};
use minidregg_spk_rpc::decode_bridge_config;
use serde_json::{json, Value};
use std::fs::DirBuilder;
use std::io;
use std::os::unix::fs::DirBuilderExt;
use std::path::Path;

/// The only pure source-authoring formats the physical SPK descriptor path
/// may request. This does not expose Mini submit, lookup or admission.
pub(crate) enum SourceStep {
    AuthorSchema,
    InspectSchema,
    AuthorPackage,
    InspectPackage,
    AuthorLaunch,
    InspectLaunch,
}

impl SourceStep {
    pub(crate) fn command_kind(&self) -> (&'static str, &'static str) {
        match self {
            Self::AuthorSchema => ("author", "application-permission-schema"),
            Self::InspectSchema => ("inspect", "application-permission-schema"),
            Self::AuthorPackage => ("author", "application-spk-package-identity"),
            Self::InspectPackage => ("inspect", "application-spk-package-identity"),
            Self::AuthorLaunch => ("author", "application-spk-launch-descriptor"),
            Self::InspectLaunch => ("inspect", "application-spk-launch-descriptor"),
        }
    }
}

pub(crate) trait SourceTool {
    fn source_step(&self, step: SourceStep, input: &Path, output: &Path) -> io::Result<Vec<u8>>;
}

impl SourceTool for PrivateOperator {
    fn source_step(&self, step: SourceStep, input: &Path, output: &Path) -> io::Result<Vec<u8>> {
        let (command, kind) = step.command_kind();
        self.tool(command, kind, input, output)
    }
}

fn invalid(reason: &'static str) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidData, reason)
}

fn hex(bytes: &[u8]) -> String {
    let mut out = String::with_capacity(bytes.len() * 2);
    for byte in bytes {
        use std::fmt::Write as _;
        write!(out, "{byte:02x}").expect("writing to String");
    }
    out
}

fn field<'a>(value: &'a Value, name: &str) -> io::Result<&'a str> {
    value
        .get(name)
        .and_then(Value::as_str)
        .ok_or_else(|| invalid("source SPK descriptor field absent"))
}

fn decimal(value: &str) -> bool {
    !value.is_empty()
        && value.len() <= 128
        && (value == "0" || !value.starts_with('0'))
        && value.bytes().all(|byte| byte.is_ascii_digit())
}

pub(crate) struct SourceDescriptor {
    pub canonical: Vec<u8>,
    pub root: String,
    pub image_identity: Vec<u8>,
    pub api_path: Option<String>,
}

/// The package is `InstalledPackage` returned by one verified Bread parse,
/// either the bounded qualifier or protected-image recheck. Its retained
/// bridge member is decoded once here, never looked up from extracted files.
/// A Mini inspector echoes the exact authored bytes; JSON is interpretation
/// only and cannot replace the original canonical descriptor artifact.
pub(crate) fn author_signed_package<T: SourceTool>(
    operator: &T,
    package: &InstalledPackage,
    attempt_dir: &Path,
) -> io::Result<SourceDescriptor> {
    private_dir(
        attempt_dir
            .parent()
            .ok_or_else(|| invalid("descriptor attempt parent absent"))?,
    )?;
    DirBuilder::new().mode(0o700).create(attempt_dir)?;
    let member = package
        .signed_bridge_config
        .as_deref()
        .ok_or_else(|| invalid("signed bridge config absent"))?;
    let bridge = decode_bridge_config(member).map_err(io::Error::other)?;
    if bridge.save_identity_caps
        || bridge.expect_app_hooks
        || bridge
            .api_path
            .as_deref()
            .is_some_and(|path| minidregg_signed_api_path::checked_prefix(path).is_err())
    {
        return Err(invalid("signed bridge outside resident Mini mapping"));
    }
    let schema_source = signed_schema_source(&bridge, package.manifest.app_version);
    let schema_input = write_new(
        attempt_dir,
        "schema-source.json",
        &serde_json::to_vec(&schema_source)?,
    )?;
    let schema = operator.source_step(
        SourceStep::AuthorSchema,
        &schema_input,
        &attempt_dir.join("schema.bin"),
    )?;
    let schema_path = attempt_dir.join("schema.bin");
    let schema_inspection = operator.source_step(
        SourceStep::InspectSchema,
        &schema_path,
        &attempt_dir.join("schema-inspection.json"),
    )?;
    let schema_view: Value = serde_json::from_slice(&schema_inspection)?;
    if field(&schema_view, "type")? != "minidregg-application-permission-schema-v1"
        || field(&schema_view, "canonical")? != hex(&schema)
        || schema_view.get("version") != schema_source.get("version")
        || schema_view.get("permissions") != schema_source.get("permissions")
        || schema_view.get("roles") != schema_source.get("roles")
        || schema_view.get("denied") != schema_source.get("denied")
    {
        return Err(invalid("Mini schema differs from signed bridge roles"));
    }
    let schema_root = field(&schema_view, "root")?;
    if !decimal(schema_root) {
        return Err(invalid("source schema root malformed"));
    }
    let bridge_sha = package
        .signed_bridge_config_sha256
        .ok_or_else(|| invalid("signed bridge hash absent"))?;
    let source = json!({
        "rawSha256":package.raw_sha256,
        "rawLength":package.raw_length.to_string(),
        "signedAppId":package.manifest.app_id.0,
        "signedAppVersion":package.manifest.app_version.to_string(),
        "manifestSha256":hex(&package.signed_manifest_sha256),
        "bridgeConfigSha256":hex(&bridge_sha),
        "bridgeApiPath":bridge.api_path.as_deref().unwrap_or(""),
        "signedSchema":schema_source,
    });
    let input = write_new(
        attempt_dir,
        "descriptor-source.json",
        &serde_json::to_vec(&source)?,
    )?;
    let canonical = operator.source_step(
        SourceStep::AuthorPackage,
        &input,
        &attempt_dir.join("descriptor.bin"),
    )?;
    let descriptor_path = attempt_dir.join("descriptor.bin");
    let inspected = operator.source_step(
        SourceStep::InspectPackage,
        &descriptor_path,
        &attempt_dir.join("descriptor-inspection.json"),
    )?;
    let view: Value = serde_json::from_slice(&inspected)?;
    let mut image_identity = b"DREGG/SPK-IMAGE/v1".to_vec();
    image_identity.extend_from_slice(&package.raw_sha256_bytes);
    if field(&view, "type")?
        != minidregg_signed_api_path::descriptor_inspection_type(bridge.api_path.as_deref())
            .map_err(invalid)?
        || field(&view, "canonical")? != hex(&canonical)
        || field(&view, "imageIdentity")? != hex(&image_identity)
        || field(&view, "rawSha256")? != hex(&package.raw_sha256_bytes)
        || field(&view, "rawLength")? != package.raw_length.to_string()
        || field(&view, "signedAppId")? != hex(package.manifest.app_id.0.as_bytes())
        || field(&view, "signedAppVersion")? != package.manifest.app_version.to_string()
        || field(&view, "manifestSha256")? != hex(&package.signed_manifest_sha256)
        || field(&view, "bridgeConfigSha256")? != hex(&bridge_sha)
        || field(&view, "bridgeApiPath")?
            != hex(bridge.api_path.as_deref().unwrap_or("").as_bytes())
    {
        return Err(invalid("Mini descriptor differs from signed SPK parse"));
    }
    let root = field(&view, "root")?;
    if !decimal(root) {
        return Err(invalid("Mini descriptor root malformed"));
    }
    let interfaces = view
        .get("interfaces")
        .and_then(Value::as_array)
        .ok_or_else(|| invalid("Mini descriptor interfaces absent"))?;
    let expected: &[(&str, &str)] = if bridge.api_path.is_some() {
        &[("1", "web"), ("2", "api")]
    } else {
        &[("1", "web")]
    };
    if interfaces.len() != expected.len() {
        return Err(invalid("Mini interface count differs"));
    }
    for (interface, (id, kind)) in interfaces.iter().zip(expected) {
        if field(interface, "id")? != *id
            || field(interface, "version")? != "1"
            || field(interface, "kind")? != *kind
            || field(interface, "schema")? != hex(&schema)
            || field(interface, "schemaRoot")? != schema_root
        {
            return Err(invalid("Mini interface differs from signed bridge schema"));
        }
    }
    Ok(SourceDescriptor {
        canonical,
        root: root.to_owned(),
        image_identity,
        api_path: bridge.api_path,
    })
}
