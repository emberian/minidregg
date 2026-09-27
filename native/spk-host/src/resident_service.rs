//! One operator-owned systemd MainPID holds the verified app and its fd3 RPC.
//! START consumes current-image BEGIN/claim plans once, launches the one fd3
//! owner, and opens HTTP only after fresh native physical completion. INSTALL
//! materialization and stopped wake remain separate lifecycle operations.
#![allow(dead_code)] // Enabled only after root reviews the exact native cut.

use crate::agent_api_custody::AgentCustody;
use crate::agent_api_native::ReverseCustodyClient;
use crate::agent_api_server::{AgentApiListener, ResidentAgent};
use crate::claim_native::{match_signed_package, submit_once};
use crate::completion_native::{
    assemble_current_completion, preflight_custodian, prepare_running_report,
    submit_completion_once, FixedCompletionSigners,
};
use crate::descriptor_native::author_signed_package;
use crate::dispatch_author::FixedAuthoring;
use crate::dispatch_delivery::ResidentHuman;
use crate::dispatch_inspection::{HttpProjection, Route};
use crate::dispatch_native::{private_dir, PrivateOperator};
use crate::hostd::Journal;
use crate::http_entrance::{CustodianPolicy, EntranceKind, PrivateHttpEntrance, ReceivedRequest};
use crate::materialize::verify_installed_spk;
use crate::resident_begin_native::{
    assemble_current_claim, submit_once as submit_begin_once, FixedBeginSigners, FixedClaimSigners,
};
use crate::resident_launch::PreparedResident;
use crate::sandbox::{open_protected_directory, SandboxSpec};
use serde::Deserialize;
use std::fs::OpenOptions;
use std::io::{self, Read};
use std::os::unix::fs::{MetadataExt, OpenOptionsExt, PermissionsExt};
use std::path::{Path, PathBuf};
use std::time::Duration;

const MAX_CONFIG: u64 = 16 * 1024;

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
struct FixedEntranceConfig {
    directory: PathBuf,
    dispatch_custody: PathBuf,
    display_name: String,
    preferred_handle: String,
}

#[derive(Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct FixedAgentConfig {
    socket: PathBuf,
    controller_uid: u32,
    custody: PathBuf,
    reverse_socket: PathBuf,
    route_name: String,
    attempt_dir: PathBuf,
    display_name: String,
    preferred_handle: String,
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
    deployment_id: String,
    host_id: String,
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
    begin_management_custody: PathBuf,
    claim_management_custody: PathBuf,
    begin_operation_ledger: PathBuf,
    claim_nonce_ledger: PathBuf,
    descriptor_attempt_dir: PathBuf,
    begin_attempt_dir: PathBuf,
    claim_author_attempt_dir: PathBuf,
    claim_attempt_dir: PathBuf,
    completion_attempt_dir: PathBuf,
    completion_sign_attempt_dir: PathBuf,
    completion_submit_attempt_dir: PathBuf,
    completion_custodian_seed: PathBuf,
    completion_management_custody: PathBuf,
    completion_semantics: String,
    entrances: Vec<FixedEntranceConfig>,
    #[serde(default)]
    agents: Vec<FixedAgentConfig>,
}

fn hex64(value: &str) -> bool {
    value.len() == 64
        && value
            .bytes()
            .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
}

fn agent_socket_parent_overlap(earlier: &[FixedAgentConfig], socket: &Path) -> bool {
    let Some(parent) = socket.parent() else {
        return true;
    };
    earlier.iter().any(|prior| {
        let Some(prior_parent) = prior.socket.parent() else {
            return true;
        };
        parent.starts_with(prior_parent) || prior_parent.starts_with(parent)
    })
}

fn require_source_bound_start_action() -> io::Result<()> {
    // BEGIN-v2/CLAIM-v2 identifies the signed package, but does not select
    // its first-create action versus continue for a retained grain volume.
    // Keep this physical entry closed until a versioned Mini claim binds the
    // exact signed command and volume identity. An operator config or /var
    // contents must not supply that authority.
    Err(invalid("source-bound START action selection unavailable"))
}

impl ResidentConfig {
    fn load(path: &Path) -> io::Result<Self> {
        let bytes = private_file(path, MAX_CONFIG)?;
        let config: Self = serde_json::from_slice(&bytes)?;
        if config.protocol != "mini-spk-resident-start-v3"
            || path.parent() != Some(config.journal_dir.as_path())
            || config.descriptor_attempt_dir.parent() != Some(config.journal_dir.as_path())
            || config.begin_attempt_dir.parent() != Some(config.journal_dir.as_path())
            || config.claim_author_attempt_dir.parent() != Some(config.journal_dir.as_path())
            || config.claim_attempt_dir.parent() != Some(config.journal_dir.as_path())
            || config.begin_operation_ledger.parent() != Some(config.journal_dir.as_path())
            || config.claim_nonce_ledger.parent() != Some(config.journal_dir.as_path())
            || config.begin_operation_ledger == config.claim_nonce_ledger
            || config.completion_attempt_dir.parent() != Some(config.journal_dir.as_path())
            || config.completion_sign_attempt_dir.parent() != Some(config.journal_dir.as_path())
            || config.completion_submit_attempt_dir.parent() != Some(config.journal_dir.as_path())
            || !hex64(&config.expected_raw_sha256)
            || !hex64(&config.bwrap_sha256)
            || !hex64(&config.mini_host_sha256)
            || !hex64(&config.mini_config_sha256)
            || !hex64(&config.deployment_id)
            || !hex64(&config.host_id)
            || config.app_uid == 0
            || config.app_gid == 0
            || config.entrances.is_empty()
            || config.entrances.len() > 8
            || config.agents.len() > 8
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
                &config.begin_management_custody,
                &config.claim_management_custody,
                &config.completion_custodian_seed,
                &config.completion_management_custody,
            ]
            .iter()
            .all(|path| path.is_absolute())
        {
            return Err(invalid("resident start config refused"));
        }
        for (index, entry) in config.entrances.iter().enumerate() {
            if !entry.directory.is_absolute()
                || !entry.dispatch_custody.is_absolute()
                || entry.dispatch_custody.parent() != Some(entry.directory.as_path())
                || entry.directory == config.journal_dir
                || entry.display_name.is_empty()
                || entry.display_name.len() > 256
                || entry.preferred_handle.is_empty()
                || entry.preferred_handle.len() > 256
                || config.entrances[..index]
                    .iter()
                    .any(|prior| prior.directory == entry.directory)
            {
                return Err(invalid("resident entrance config refused"));
            }
        }
        for (index, agent) in config.agents.iter().enumerate() {
            if !agent.socket.is_absolute()
                || agent.controller_uid == 0
                || agent.controller_uid == config.app_uid
                || !agent.custody.is_absolute()
                || !agent.reverse_socket.is_absolute()
                || agent.attempt_dir.parent() != Some(config.journal_dir.as_path())
                || agent.socket.parent().is_some_and(|parent| {
                    parent.starts_with(&config.journal_dir)
                        || parent.starts_with(&agent.attempt_dir)
                })
                || agent.display_name.is_empty()
                || agent.display_name.len() > 256
                || agent.preferred_handle.is_empty()
                || agent.preferred_handle.len() > 256
                || config
                    .entrances
                    .iter()
                    .any(|entry| agent.socket.starts_with(&entry.directory))
                || config.agents[..index].iter().any(|prior| {
                    prior.socket == agent.socket
                        || prior.controller_uid == agent.controller_uid
                        || prior.custody == agent.custody
                        || prior.reverse_socket == agent.reverse_socket
                        || prior.attempt_dir == agent.attempt_dir
                })
                || agent_socket_parent_overlap(&config.agents[..index], &agent.socket)
            {
                return Err(invalid("resident agent config refused"));
            }
        }
        Ok(config)
    }
}

/// This is the systemd ExecStart body for a fresh native START claim. The
/// stopped unit is installed from operator-reviewed pins; HTTP has no path to
/// choose a package, task UID, Mini signer, command, or app generation.
pub fn run(config_path: &Path) -> io::Result<()> {
    let config = ResidentConfig::load(config_path)?;
    require_source_bound_start_action()?;
    let journal = Journal::open(&config.journal_dir)?;
    Journal::preflight_current_unit(&config.unit)?;
    if journal.read()?.is_some() {
        return Err(invalid("resident generation journal is already occupied"));
    }
    // An old one-shot attempt is an uncertainty or recovery record, not a
    // fresh destination. Check every later phase before consuming BEGIN.
    for path in [
        &config.descriptor_attempt_dir,
        &config.begin_attempt_dir,
        &config.claim_author_attempt_dir,
        &config.claim_attempt_dir,
        &config.completion_attempt_dir,
        &config.completion_sign_attempt_dir,
        &config.completion_submit_attempt_dir,
    ] {
        match std::fs::symlink_metadata(path) {
            Ok(_) => return Err(invalid("resident lifecycle attempt already exists")),
            Err(error) if error.kind() == io::ErrorKind::NotFound => {}
            Err(error) => return Err(error),
        }
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
    // Staged v2 code below remains unreachable under the action guard above.
    // The v3 claim must replace this with its signed create/continue selection.
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
    // Read every separately fixed transport/custody pair before consuming the
    // one-shot claim. No HTTP socket is bound until START completion.
    let mut custodies = Vec::with_capacity(config.entrances.len());
    let mut policies = Vec::with_capacity(config.entrances.len());
    for entry in &config.entrances {
        open_protected_directory(&entry.directory, config.app_uid, false)?;
        let custody: FixedAuthoring =
            serde_json::from_slice(&private_file(&entry.dispatch_custody, MAX_CONFIG)?)?;
        custody.validate()?;
        let policy = CustodianPolicy::load(&entry.directory)?;
        if policy.fixed_app != custody.app
            || policy.fixed_subject != custody.subject
            || policy.fixed_session != custody.session
            || policy.fixed_ticket != custody.ticket_resource
            || !matches!(
                (policy.fixed_session_kind, custody.session_kind.as_str()),
                (EntranceKind::Browser, "web") | (EntranceKind::Api, "api")
            )
            || policies.iter().any(|prior: &CustodianPolicy| {
                prior.expected_host == policy.expected_host
                    || (prior.fixed_app == policy.fixed_app
                        && prior.fixed_session == policy.fixed_session
                        && prior.fixed_ticket == policy.fixed_ticket)
            })
        {
            return Err(invalid("HTTP transport differs from fixed Mini custody"));
        }
        policies.push(policy);
        custodies.push(custody);
    }
    let mut agent_preflights = Vec::with_capacity(config.agents.len());
    for agent in &config.agents {
        open_protected_directory(
            agent
                .socket
                .parent()
                .ok_or_else(|| invalid("agent socket parent"))?,
            config.app_uid,
            false,
        )?;
        AgentApiListener::preflight_parent(&agent.socket, agent.controller_uid)?;
        open_protected_directory(
            agent
                .reverse_socket
                .parent()
                .ok_or_else(|| invalid("reverse custody parent"))?,
            config.app_uid,
            false,
        )?;
        let custody: AgentCustody =
            serde_json::from_slice(&private_file(&agent.custody, MAX_CONFIG)?)?;
        custody.validate()?;
        if agent_preflights
            .iter()
            .any(|(prior, _): &(AgentCustody, ReverseCustodyClient)| {
                prior.session == custody.session
                    || prior.ticket_resource == custody.ticket_resource
                    || prior.parent_task == custody.parent_task
                    || prior.purse_task == custody.purse_task
            })
            || custodies.iter().any(|human| {
                human.session == custody.session || human.ticket_resource == custody.ticket_resource
            })
        {
            return Err(invalid("resident agent authority route duplicated"));
        }
        private_dir(&agent.attempt_dir)?;
        let reverse = ReverseCustodyClient::new(
            agent.reverse_socket.clone(),
            agent.controller_uid,
            agent.route_name.clone(),
        )?;
        agent_preflights.push((custody, reverse));
    }
    let descriptor = author_signed_package(&operator, &package, &config.descriptor_attempt_dir)?;
    if (!config.agents.is_empty()
        || policies
            .iter()
            .any(|policy| policy.fixed_session_kind == EntranceKind::Api))
        && descriptor.api_path.is_none()
    {
        return Err(invalid("signed package has no configured API interface"));
    }
    let begin_signers: FixedBeginSigners =
        serde_json::from_slice(&private_file(&config.begin_management_custody, MAX_CONFIG)?)?;
    let claim_signers: FixedClaimSigners =
        serde_json::from_slice(&private_file(&config.claim_management_custody, MAX_CONFIG)?)?;
    let begin = submit_begin_once(
        &operator,
        &begin_signers,
        config.app_uid,
        &descriptor.canonical,
        "start",
        &config.begin_operation_ledger,
        &config.begin_attempt_dir,
    )?;
    let ingress = assemble_current_claim(
        &operator,
        &claim_signers,
        config.app_uid,
        &begin,
        &config.claim_nonce_ledger,
        &config.claim_author_attempt_dir,
    )?;
    let captured = submit_once(&operator, &ingress, &config.claim_attempt_dir)?;
    let matched = match_signed_package(&operator, &package, &captured, &config.claim_attempt_dir)?;
    if matched.descriptor_root != descriptor.root
        || matched.begin.image_identity != hex_bytes(&descriptor.image_identity)
    {
        return Err(invalid(
            "native claim differs from pre-BEGIN signed descriptor",
        ));
    }
    if matched.begin.unit != config.unit {
        return Err(invalid(
            "source lifecycle unit differs from installed service",
        ));
    }
    if policies
        .iter()
        .any(|policy| policy.fixed_session_kind == EntranceKind::Api)
        && matched.bridge.api_path.is_none()
    {
        return Err(invalid("signed package has no configured API interface"));
    }
    if custodies
        .iter()
        .any(|custody| custody.app != matched.begin.app.to_string())
    {
        return Err(invalid(
            "fixed participant custody differs from claimed shared app",
        ));
    }
    for (custody, _) in &agent_preflights {
        if custody.app != matched.begin.app.to_string()
            || custody.app_generation != matched.begin.generation.to_string()
            || matched.bridge.api_path.is_none()
        {
            return Err(invalid("agent custody differs from claimed shared app"));
        }
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
        &begin.ingress,
        &captured.payload,
        &config.completion_custodian_seed,
        &config.completion_semantics,
        &config.completion_attempt_dir,
    )?;
    let completion_ingress = assemble_current_completion(
        &operator,
        &begin.ingress,
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
    let entrances = config
        .entrances
        .iter()
        .map(|entry| PrivateHttpEntrance::bind(&entry.directory))
        .collect::<io::Result<Vec<_>>>()?;
    let api_path = matched.bridge.api_path;
    let mut agent_routes = config
        .agents
        .iter()
        .zip(agent_preflights)
        .map(|(agent, (custody, reverse))| {
            AgentApiListener::bind(&agent.socket, agent.controller_uid)
                .map(|listener| (listener, custody, reverse, agent))
        })
        .collect::<io::Result<Vec<_>>>()?;
    let agent_fds: Vec<_> = agent_routes
        .iter()
        .map(|(listener, _, _, _)| listener.as_raw_fd())
        .collect();
    PrivateHttpEntrance::serve_many_with_aux(&entrances, &agent_fds, |event| {
        if let Ok((index, request, kind, policy)) = event {
            let entry = &config.entrances[index];
            let mut human = ResidentHuman {
                operator: &operator,
                custody: &custodies[index],
                journal: &journal,
                rpc: &mut resident.rpc,
                display_name: &entry.display_name,
                preferred_handle: &entry.preferred_handle,
            };
            return deliver_request(
                &mut human,
                request,
                kind,
                policy,
                api_path.as_deref(),
                &config.journal_dir,
            )
            .map(Some);
        }
        let index = match event {
            Err(index) => index,
            Ok(_) => unreachable!("HTTP branch returned above"),
        };
        let (listener, custody, reverse, agent) = agent_routes
            .get_mut(index)
            .ok_or_else(|| invalid("resident agent poll index drift"))?;
        let mut context = ResidentAgent {
            operator: &operator,
            custody,
            journal: &journal,
            rpc: &mut resident.rpc,
            reverse_reserve: reverse,
            signed_api_path: api_path
                .as_deref()
                .ok_or_else(|| invalid("signed API path absent"))?,
            display_name: &agent.display_name,
            preferred_handle: &agent.preferred_handle,
            attempt_parent: &agent.attempt_dir,
        };
        listener.poll_once(&mut context)?;
        Ok(None)
    })
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
    let http = project_request(&request, kind, api_path)?;
    human.deliver_once(policy, &http, attempt_parent)
}

fn project_request<'a>(
    request: &'a ReceivedRequest,
    kind: EntranceKind,
    api_path: Option<&'a str>,
) -> io::Result<HttpProjection<'a>> {
    // The HTTP parser has already removed exactly one leading slash. Keep
    // that canonical relative form, including the empty API-root path.
    if request.path_and_query.starts_with('/') {
        return Err(invalid("HTTP target is not canonical relative form"));
    }
    let relative = request.path_and_query.as_str();
    let route = match kind {
        EntranceKind::Browser => Route::Browser,
        EntranceKind::Api => Route::Api {
            signed_path: api_path.ok_or_else(|| invalid("signed SPK lacks API interface"))?,
        },
    };
    Ok(HttpProjection {
        method: request.method.as_str(),
        path_and_query: relative,
        ordered_headers: &request.ordinary_headers,
        body: &request.body,
        route,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::dispatch_inspection::app_route_path;
    use crate::http_entrance::read_request;
    use serde_json::json;
    use std::fs::{self, DirBuilder};
    use std::io::Write;
    use std::os::unix::fs::DirBuilderExt;
    use std::os::unix::net::UnixStream;
    use std::time::{SystemTime, UNIX_EPOCH};

    #[test]
    fn distinct_agent_uids_need_disjoint_socket_parent_acl_scopes() {
        let first = FixedAgentConfig {
            socket: PathBuf::from("/run/mini-spk/agent-a/api.sock"),
            controller_uid: 1001,
            custody: PathBuf::from("/var/lib/mini-spk/a-custody.json"),
            reverse_socket: PathBuf::from("/run/mini-spk/reverse-a.sock"),
            route_name: "a".into(),
            attempt_dir: PathBuf::from("/var/lib/mini-spk/a-attempt"),
            display_name: "A".into(),
            preferred_handle: "a".into(),
        };
        assert!(agent_socket_parent_overlap(
            std::slice::from_ref(&first),
            Path::new("/run/mini-spk/agent-a/other.sock")
        ));
        assert!(agent_socket_parent_overlap(
            std::slice::from_ref(&first),
            Path::new("/run/mini-spk/agent-a/nested/api.sock")
        ));
        assert!(!agent_socket_parent_overlap(
            &[first],
            Path::new("/run/mini-spk/agent-b/api.sock")
        ));
    }

    #[test]
    fn resident_config_refuses_two_agent_sockets_under_one_acl_parent() {
        let unique = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_nanos();
        let journal =
            std::env::temp_dir().join(format!("mini-spk-config-{}-{unique}", std::process::id()));
        DirBuilder::new().mode(0o700).create(&journal).unwrap();
        let path = journal.join("resident.json");
        let agent = |name: &str, uid: u32| {
            json!({
                "socket": format!("/run/mini-spk/{name}/api.sock"),
                "controllerUid": uid,
                "custody": format!("/var/lib/mini-spk/{name}-custody.json"),
                "reverseSocket": format!("/run/mini-spk/{name}-reverse.sock"),
                "routeName": name,
                "attemptDir": journal.join(format!("{name}-attempt")),
                "displayName": name,
                "preferredHandle": name
            })
        };
        let mut config = json!({
            "protocol": "mini-spk-resident-start-v3",
            "journalDir": journal.clone(),
            "imageDir": "/var/lib/mini-spk/image",
            "expectedRawSha256": "a".repeat(64),
            "persistentVar": "/var/lib/mini-spk/var",
            "persistentVarMaxBytes": 1048576,
            "deploymentId": "e".repeat(64),
            "hostId": "f".repeat(64),
            "bwrap": "/usr/bin/bwrap",
            "bwrapSha256": "b".repeat(64),
            "appUid": 1000,
            "appGid": 1000,
            "unit": "mini-spk-a8401-g1.service",
            "miniHost": "/opt/mini/host",
            "miniHostSha256": "c".repeat(64),
            "miniConfig": "/etc/mini/host.json",
            "miniConfigSha256": "d".repeat(64),
            "miniOperatorSocket": "/run/mini/operator.sock",
            "beginManagementCustody": "/etc/mini/begin.json",
            "claimManagementCustody": "/etc/mini/claim.json",
            "beginOperationLedger": journal.join("begin-ledger"),
            "claimNonceLedger": journal.join("claim-ledger"),
            "descriptorAttemptDir": journal.join("descriptor-attempt"),
            "beginAttemptDir": journal.join("begin-attempt"),
            "claimAuthorAttemptDir": journal.join("claim-author-attempt"),
            "claimAttemptDir": journal.join("claim-attempt"),
            "completionAttemptDir": journal.join("completion-attempt"),
            "completionSignAttemptDir": journal.join("completion-sign-attempt"),
            "completionSubmitAttemptDir": journal.join("completion-submit-attempt"),
            "completionCustodianSeed": "/etc/mini/completion.seed",
            "completionManagementCustody": "/etc/mini/completion.json",
            "completionSemantics": "1",
            "entrances": [{
                "directory": "/run/mini-spk/human",
                "dispatchCustody": "/run/mini-spk/human/dispatch.json",
                "displayName": "human",
                "preferredHandle": "human"
            }],
            "agents": [agent("agent-a", 1001), agent("agent-b", 1002)]
        });
        let mut file = OpenOptions::new()
            .write(true)
            .create_new(true)
            .mode(0o600)
            .open(&path)
            .unwrap();
        file.write_all(&serde_json::to_vec(&config).unwrap())
            .unwrap();
        file.sync_all().unwrap();
        assert!(ResidentConfig::load(&path).is_ok());
        assert_eq!(
            run(&path).unwrap_err().to_string(),
            "source-bound START action selection unavailable"
        );
        assert_eq!(fs::read_dir(&journal).unwrap().count(), 1);
        config["agents"][1]["socket"] = json!("/run/mini-spk/agent-a/other.sock");
        fs::write(&path, serde_json::to_vec(&config).unwrap()).unwrap();
        assert!(ResidentConfig::load(&path).is_err());
        config["agents"][1]["socket"] = json!("/run/mini-spk/agent-a/nested/api.sock");
        fs::write(&path, serde_json::to_vec(&config).unwrap()).unwrap();
        assert!(ResidentConfig::load(&path).is_err());
        fs::remove_dir_all(&journal).unwrap();
    }

    #[test]
    fn parsed_api_root_and_discovery_keep_one_canonical_prefix() {
        for (target, expected) in [
            ("/", ("repo.git/", "")),
            (
                "/info/refs?service=git-upload-pack",
                ("repo.git/info/refs", "service=git-upload-pack"),
            ),
        ] {
            let (mut writer, mut reader) = UnixStream::pair().unwrap();
            write!(
                writer,
                "GET {target} HTTP/1.1\r\nHost: app.example.test\r\n\r\n"
            )
            .unwrap();
            let request = read_request(&mut reader).unwrap();
            let projected =
                project_request(&request, EntranceKind::Api, Some("/repo.git/")).unwrap();
            assert_eq!(
                app_route_path(&projected).unwrap(),
                (expected.0.to_owned(), expected.1.to_owned())
            );
        }
    }
}
