//! One operator-owned systemd MainPID holds the verified app and its fd3 RPC.
//! This fresh-start path deliberately has no claim retry or image installation.
//! Install completion, stopped wake and native physical completion remain
//! separate qualified lifecycle operations.
#![allow(dead_code)] // Enabled only after root reviews the exact native cut.

use crate::claim_native::{match_signed_package, submit_once};
use crate::completion_native::{
    assemble_current_completion, preflight_custodian, prepare_running_report,
    submit_completion_once, FixedCompletionSigners,
};
use crate::dispatch_author::FixedAuthoring;
use crate::dispatch_delivery::ResidentHuman;
use crate::dispatch_inspection::{HttpProjection, Route};
use crate::dispatch_native::{private_dir, PrivateOperator};
use crate::hostd::Journal;
use crate::http_entrance::{CustodianPolicy, EntranceKind, PrivateHttpEntrance, ReceivedRequest};
use crate::materialize::verify_installed_spk;
use crate::resident_launch::PreparedResident;
use crate::sandbox::{open_protected_directory, SandboxSpec};
use serde::Deserialize;
use std::fs::OpenOptions;
use std::io::{self, Read};
use std::os::unix::fs::{MetadataExt, OpenOptionsExt, PermissionsExt};
use std::path::{Path, PathBuf};
use std::time::Duration;

const MAX_CONFIG: u64 = 16 * 1024;
const MAX_INGRESS: u64 = 12_102_759;

fn invalid(reason: &'static str) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidData, reason)
}

fn private_file(path: &Path, max: u64) -> io::Result<Vec<u8>> {
    let parent = path
        .parent()
        .ok_or_else(|| invalid("private file parent absent"))?;
    private_dir(parent)?;
    let file = OpenOptions::new()
        .read(true)
        .custom_flags(libc::O_NOFOLLOW)
        .open(path)?;
    let meta = file.metadata()?;
    if !path.is_absolute()
        || !meta.is_file()
        || meta.nlink() != 1
        || meta.uid() != unsafe { libc::geteuid() }
        || meta.permissions().mode() & 0o777 != 0o600
        || meta.len() == 0
        || meta.len() > max
    {
        return Err(invalid("operator private file identity or size refused"));
    }
    let mut bytes = Vec::with_capacity(meta.len() as usize);
    file.take(max + 1).read_to_end(&mut bytes)?;
    if bytes.len() as u64 != meta.len() || bytes.len() as u64 > max {
        return Err(invalid("operator private file changed while reading"));
    }
    Ok(bytes)
}

#[derive(Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct ResidentConfig {
    protocol: String,
    journal_dir: PathBuf,
    image_dir: PathBuf,
    expected_raw_sha256: String,
    persistent_var: PathBuf,
    persistent_var_max_bytes: u64,
    bwrap: PathBuf,
    bwrap_sha256: String,
    app_uid: u32,
    app_gid: u32,
    unit: String,
    mini_host: PathBuf,
    mini_host_sha256: String,
    mini_config: PathBuf,
    mini_config_sha256: String,
    mini_operator_socket: PathBuf,
    begin_ingress: PathBuf,
    claim_ingress: PathBuf,
    claim_attempt_dir: PathBuf,
    completion_attempt_dir: PathBuf,
    completion_sign_attempt_dir: PathBuf,
    completion_submit_attempt_dir: PathBuf,
    completion_custodian_seed: PathBuf,
    completion_management_custody: PathBuf,
    completion_semantics: String,
    dispatch_custody: PathBuf,
    dispatch_attempt_parent: PathBuf,
    display_name: String,
    preferred_handle: String,
}

fn hex64(value: &str) -> bool {
    value.len() == 64
        && value
            .bytes()
            .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
}

impl ResidentConfig {
    fn load(path: &Path) -> io::Result<Self> {
        let bytes = private_file(path, MAX_CONFIG)?;
        let config: Self = serde_json::from_slice(&bytes)?;
        if config.protocol != "mini-spk-resident-start-v1"
            || path.parent() != Some(config.journal_dir.as_path())
            || config.claim_attempt_dir.parent() != Some(config.journal_dir.as_path())
            || config.completion_attempt_dir.parent() != Some(config.journal_dir.as_path())
            || config.completion_sign_attempt_dir.parent() != Some(config.journal_dir.as_path())
            || config.completion_submit_attempt_dir.parent() != Some(config.journal_dir.as_path())
            || config.dispatch_custody.parent() != Some(config.journal_dir.as_path())
            || config.dispatch_attempt_parent != config.journal_dir
            || !hex64(&config.expected_raw_sha256)
            || !hex64(&config.bwrap_sha256)
            || !hex64(&config.mini_host_sha256)
            || !hex64(&config.mini_config_sha256)
            || config.app_uid == 0
            || config.app_gid == 0
            || config.display_name.is_empty()
            || config.display_name.len() > 256
            || config.preferred_handle.is_empty()
            || config.preferred_handle.len() > 256
            || config.persistent_var_max_bytes == 0
            || !config
                .completion_semantics
                .bytes()
                .all(|byte| byte.is_ascii_digit())
            || config.completion_semantics.is_empty()
            || ![
                &config.image_dir,
                &config.persistent_var,
                &config.bwrap,
                &config.mini_host,
                &config.mini_config,
                &config.mini_operator_socket,
                &config.begin_ingress,
                &config.claim_ingress,
                &config.completion_custodian_seed,
                &config.completion_management_custody,
            ]
            .iter()
            .all(|path| path.is_absolute())
        {
            return Err(invalid("resident start config refused"));
        }
        Ok(config)
    }
}

/// This is the systemd ExecStart body for a fresh native START claim. The
/// stopped unit is installed from operator-reviewed pins; HTTP has no path to
/// choose a package, task UID, Mini signer, command, or app generation.
pub fn run(config_path: &Path) -> io::Result<()> {
    let config = ResidentConfig::load(config_path)?;
    let journal = Journal::open(&config.journal_dir)?;
    Journal::preflight_current_unit(&config.unit)?;
    if journal.read()?.is_some() {
        return Err(invalid("resident generation journal is already occupied"));
    }
    let package = verify_installed_spk(&config.image_dir, config.app_uid)?;
    // The operator Host/config/socket and signer live outside the worker mount
    // and below ancestors the app UID cannot rename or rewrite.
    for path in [
        &config.mini_host,
        &config.mini_config,
        &config.mini_operator_socket,
        &config.completion_custodian_seed,
    ] {
        open_protected_directory(
            path.parent()
                .ok_or_else(|| invalid("operator artifact parent absent"))?,
            config.app_uid,
            false,
        )?;
    }
    if package.raw_sha256 != config.expected_raw_sha256 {
        return Err(invalid("resident signed package pin drift"));
    }
    let command = &package.manifest.continue_command;
    let spec = SandboxSpec {
        bwrap: config.bwrap.clone(),
        image_root: package.directory.join("root"),
        persistent_var: config.persistent_var.clone(),
        persistent_var_max_bytes: config.persistent_var_max_bytes,
        argv: command.argv.clone(),
        environ: command.environ.clone(),
    };
    // Preopen physical custody and its exact fd3/4/5 before consuming the
    // one-shot Mini claim. No app child exists yet.
    let prepared =
        PreparedResident::prepare(&spec, config.app_uid, config.app_gid, &config.bwrap_sha256)?;
    let operator = PrivateOperator {
        host: config.mini_host,
        config: config.mini_config,
        socket: config.mini_operator_socket,
        host_sha256: config.mini_host_sha256,
        config_sha256: config.mini_config_sha256,
    };
    preflight_custodian(
        &operator,
        &config.completion_custodian_seed,
        &config.completion_semantics,
    )?;
    let signers: FixedCompletionSigners = serde_json::from_slice(&private_file(
        &config.completion_management_custody,
        MAX_CONFIG,
    )?)?;
    signers.validate(&operator, config.app_uid)?;
    let custody_bytes = private_file(&config.dispatch_custody, MAX_CONFIG)?;
    let custody: FixedAuthoring = serde_json::from_slice(&custody_bytes)?;
    custody.validate()?;
    private_dir(&config.dispatch_attempt_parent)?;
    // Read the fixed transport binding without creating a listener. Binding
    // and accepting must wait for confirmed native START completion.
    let policy = CustodianPolicy::load(&config.journal_dir)?;
    if policy.fixed_app != custody.app
        || policy.fixed_subject != custody.subject
        || policy.fixed_session != custody.session
        || policy.fixed_ticket != custody.ticket_resource
        || !matches!(
            (policy.fixed_session_kind, custody.session_kind.as_str()),
            (EntranceKind::Browser, "web") | (EntranceKind::Api, "api")
        )
    {
        return Err(invalid("HTTP transport differs from fixed Mini custody"));
    }
    let ingress = private_file(&config.claim_ingress, MAX_INGRESS)?;
    let begin_ingress = private_file(&config.begin_ingress, MAX_INGRESS)?;
    let begin_source = write_begin_source(&config.claim_attempt_dir, &begin_ingress)?;
    let echoed_begin = operator.tool(
        "author",
        "application-lifecycle-resident-begin",
        &begin_source,
        &config.journal_dir.join("resident-begin.bin"),
    )?;
    if echoed_begin != begin_ingress {
        return Err(invalid(
            "source resident BEGIN echo differs from pinned ingress",
        ));
    }
    let captured = submit_once(&operator, &ingress, &config.claim_attempt_dir)?;
    let matched = match_signed_package(&operator, &package, &captured, &config.claim_attempt_dir)?;
    if matched.begin.unit != config.unit {
        return Err(invalid(
            "source lifecycle unit differs from installed service",
        ));
    }
    if policy.fixed_session_kind == EntranceKind::Api && matched.bridge.api_path.is_none() {
        return Err(invalid("signed package has no configured API interface"));
    }
    if custody.app != matched.begin.app.to_string() {
        return Err(invalid(
            "fixed participant custody differs from claimed app",
        ));
    }
    journal.arm(matched.begin.clone())?;
    journal.request_launch(&matched.begin)?;
    let mut resident = prepared.start(&journal, &matched.begin)?;
    let view = resident.rpc.get_view_info(Duration::from_secs(300))?;
    if view != matched.bridge.view_info {
        return Err(invalid(
            "running app ViewInfo differs from signed bridge schema",
        ));
    }
    let report = prepare_running_report(
        &operator,
        &journal,
        &begin_ingress,
        &captured.payload,
        &config.completion_custodian_seed,
        &config.completion_semantics,
        &config.completion_attempt_dir,
    )?;
    let completion_ingress = assemble_current_completion(
        &operator,
        &begin_ingress,
        &ingress,
        &report.signed_report,
        &signers,
        config.app_uid,
        &config.completion_sign_attempt_dir,
    )?;
    let _receipt = submit_completion_once(
        &operator,
        &journal,
        &completion_ingress,
        &config.completion_submit_attempt_dir,
    )?;
    // A START completion is the first state that may expose transport. Native
    // admission remains decisive for every later HTTP request as well.
    let entrance = PrivateHttpEntrance::bind(&config.journal_dir)?;
    let api_path = matched.bridge.api_path;
    let mut human = ResidentHuman {
        operator: &operator,
        custody: &custody,
        journal: &journal,
        rpc: &mut resident.rpc,
        display_name: &config.display_name,
        preferred_handle: &config.preferred_handle,
    };
    entrance.serve_resident(|request, kind, policy| {
        deliver_request(
            &mut human,
            request,
            kind,
            policy,
            api_path.as_deref(),
            &config.dispatch_attempt_parent,
        )
    })
}

fn write_begin_source(attempt_dir: &Path, ingress: &[u8]) -> io::Result<PathBuf> {
    private_dir(
        attempt_dir
            .parent()
            .ok_or_else(|| invalid("BEGIN source parent absent"))?,
    )?;
    let path = attempt_dir
        .parent()
        .unwrap()
        .join("resident-begin-source.json");
    let bytes = serde_json::to_vec(&serde_json::json!({"begin": hex_bytes(ingress)}))?;
    let mut file = OpenOptions::new()
        .write(true)
        .create_new(true)
        .mode(0o600)
        .custom_flags(libc::O_NOFOLLOW)
        .open(&path)?;
    use std::io::Write as _;
    file.write_all(&bytes)?;
    file.sync_all()?;
    std::fs::File::open(attempt_dir.parent().unwrap())?.sync_all()?;
    Ok(path)
}

fn hex_bytes(bytes: &[u8]) -> String {
    use std::fmt::Write as _;
    let mut out = String::with_capacity(bytes.len() * 2);
    for byte in bytes {
        write!(out, "{byte:02x}").expect("writing to String");
    }
    out
}

fn deliver_request(
    human: &mut ResidentHuman<'_>,
    request: ReceivedRequest,
    kind: EntranceKind,
    policy: &CustodianPolicy,
    api_path: Option<&str>,
    attempt_parent: &Path,
) -> io::Result<Vec<u8>> {
    let relative = request
        .path_and_query
        .strip_prefix('/')
        .ok_or_else(|| invalid("HTTP target is not root-relative"))?;
    let route = match kind {
        EntranceKind::Browser => Route::Browser,
        EntranceKind::Api => Route::Api {
            signed_path: api_path.ok_or_else(|| invalid("signed SPK lacks API interface"))?,
        },
    };
    let http = HttpProjection {
        method: request.method.as_str(),
        path_and_query: relative,
        ordered_headers: &request.ordinary_headers,
        body: &request.body,
        route,
    };
    human.deliver_once(policy, &http, attempt_parent)
}
