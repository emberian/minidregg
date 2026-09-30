//! Private copied-volume GitWeb fd3 session-cache qualification.
//! Synthetic session projections are fixture data, not Mini authority.
//! No public listener or mutating Git request is issued.
#[path = "../rpc_adapter.rs"]
mod rpc_adapter;

use minidregg_spk_host::hostd;
use minidregg_spk_host::sandbox::{spawn_sandbox, SandboxSpec};
use minidregg_spk_rpc::{Method, RequestContext, SessionParameters, WebRequest, WebResult};
use rpc_adapter::{RpcDriver, SessionBinding, SessionKind};
use sandstorm_package::{Spk, SpkManifest};
use sha2::{Digest, Sha256};
use std::error::Error;
use std::fs;
use std::os::unix::net::UnixStream;
use std::path::{Path, PathBuf};
use std::process::Child;
use std::time::Duration;

const SPK_SHA: &str = "2bbfe6d3c705dfb0696905ecd9c1d00d6554cc1224e63dc5545152af5f8f2caa";
const APP_ID: &str = "6va4cjamc21j0znf5h5rrgnv0rpyvh1vaxurkrgknefvj0x63ash";
const FIXTURE_RESOURCE: u64 = 991013;
const MAX_SPK: usize = 256 * 1024 * 1024;

struct Args {
    package_dir: PathBuf,
    persistent_var: PathBuf,
    bwrap: PathBuf,
    max_var_bytes: u64,
    commit: String,
    capacity: bool,
}

fn args() -> Result<Args, Box<dyn Error>> {
    let words: Vec<_> = std::env::args().collect();
    if !(words.len() == 6 || (words.len() == 7 && words[6] == "--capacity")) {
        return Err("usage: gitweb-session-smoke PACKAGE_DIR COPIED_VAR_DIR BWRAP MAX_VAR_BYTES EXPECTED_COMMIT [--capacity]".into());
    }
    let commit = words[5].clone();
    if commit.len() != 40
        || !commit.bytes().all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(&b))
    {
        return Err("expected lowercase SHA-1 commit".into());
    }
    Ok(Args {
        package_dir: PathBuf::from(&words[1]),
        persistent_var: PathBuf::from(&words[2]),
        bwrap: PathBuf::from(&words[3]),
        max_var_bytes: words[4].parse()?,
        commit,
        capacity: words.len() == 7,
    })
}

fn signed_manifest(package_dir: &Path) -> Result<SpkManifest, Box<dyn Error>> {
    if package_dir.file_name().and_then(|n| n.to_str())
        != Some(format!("sha256-{SPK_SHA}").as_str())
    {
        return Err("wrong signed image directory".into());
    }
    let stored = package_dir.join("package.spk");
    if fs::metadata(&stored)?.len() as usize > MAX_SPK {
        return Err("SPK too large".into());
    }
    let raw = fs::read(stored)?;
    if format!("{:x}", Sha256::digest(&raw)) != SPK_SHA {
        return Err("SPK hash mismatch".into());
    }
    let manifest = SpkManifest::from_spk(&Spk::parse(&raw)?)?;
    if manifest.app_id.0 != APP_ID || manifest.app_version != 10 {
        return Err("signed app identity/version mismatch".into());
    }
    let installed: serde_json::Value =
        serde_json::from_slice(&fs::read(package_dir.join("manifest.json"))?)?;
    if serde_json::to_value(&manifest)? != installed {
        return Err("installed manifest differs from signed SPK".into());
    }
    Ok(manifest)
}

struct App(Child);
impl Drop for App {
    fn drop(&mut self) {
        let _ = self.0.kill();
        let _ = self.0.wait();
    }
}

fn params(identity: u8, bits: [bool; 2]) -> SessionParameters {
    SessionParameters {
        identity_id: [identity; 32],
        display_name: "GitWeb private session probe".into(),
        preferred_handle: "gitweb-probe".into(),
        permissions: bits.to_vec(),
        tab_id: b"gitweb-session-probe".to_vec(),
        base_path: "https://grain.invalid/i/gitweb-session-probe/".into(),
        user_agent: "Mini-GitWeb-Session-Probe/1".into(),
        acceptable_languages: vec!["en-US".into()],
    }
}

fn binding(kind: SessionKind, bits: [bool; 2], fingerprint: u8) -> SessionBinding {
    let (session_resource, subject, identity) = match kind {
        SessionKind::Web => (6208, 8, 8),
        SessionKind::Api => (6209, 9, 9),
    };
    SessionBinding {
        app: FIXTURE_RESOURCE,
        process_generation: 2,
        session_resource,
        subject,
        projection_fingerprint: [fingerprint; 32],
        kind,
        params: params(identity, bits),
    }
}

fn get(path: &str) -> WebRequest {
    WebRequest {
        method: Method::Get,
        path_and_query: path.into(),
        context: RequestContext::default(),
        body: None,
    }
}

fn checked_html(
    driver: &mut RpcDriver,
    binding: SessionBinding,
    commit: &str,
) -> Result<(), Box<dyn Error>> {
    let reply = driver.dispatch(
        binding,
        get("gitweb.cgi?p=repo.git;a=summary"),
        256 * 1024,
        Duration::from_secs(30),
    )?;
    match reply.result {
        WebResult::Content { status: 200, mime_type, body, .. }
            if mime_type.starts_with("text/html")
                && (body.windows(commit.len()).any(|part| part == commit.as_bytes())
                    || body.windows(b"Mini SPK fixture".len())
                        .any(|part| part == b"Mini SPK fixture")) =>
        {
            println!("html_commit={} bytes={} sha256={:x}", commit, body.len(), Sha256::digest(&body));
            Ok(())
        }
        other => Err(format!("GitWeb summary differs from retained commit: {other:?}").into()),
    }
}

fn run(input: Args, manifest: SpkManifest) -> Result<(), Box<dyn Error>> {
    let child = spawn_sandbox(&SandboxSpec {
        bwrap: input.bwrap,
        image_root: input.package_dir.join("root"),
        persistent_var: input.persistent_var,
        persistent_var_max_bytes: input.max_var_bytes,
        argv: manifest.continue_command.argv.clone(),
        environ: manifest.continue_command.environ.clone(),
        // The app never writes to this harness's stdout/stderr.
        app_output: std::env::temp_dir()
            .join(format!("spk-app-output-{}.log", std::process::id())),
    })?;
    println!("app_output={}", std::env::temp_dir()
        .join(format!("spk-app-output-{}.log", std::process::id())).display());
    println!("app_spawned=continue pid={}", child.process.id());
    let app = App(child.process);
    let rpc: UnixStream = child.rpc;
    let mut driver = RpcDriver::from_connected_stream(FIXTURE_RESOURCE, 2, rpc)?;
    let view = driver.get_view_info(Duration::from_secs(30))?;
    if view.permission_names != ["read", "write"]
        || view.roles.len() != 2
        || view.roles[0].permissions != [true, false]
        || view.roles[1].permissions != [true, true]
    {
        return Err("signed GitWeb role schema differs at runtime".into());
    }
    println!("view={} roles=guest[read],developer[read,write]", view.app_title);

    let owner = binding(SessionKind::Web, [true, true], 1);
    checked_html(&mut driver, owner.clone(), &input.commit)?;
    checked_html(&mut driver, owner, &input.commit)?;
    let reuse = driver.stats()?;
    if reuse.sessions_created != 1 || reuse.cached_sessions != 1 {
        return Err("unchanged Mini projection did not reuse one WebSession".into());
    }
    println!("same_projection_sessions_created={}", reuse.sessions_created);

    checked_html(
        &mut driver,
        binding(SessionKind::Web, [true, false], 2),
        &input.commit,
    )?;
    let attenuated = driver.stats()?;
    if attenuated.sessions_created != 2 || attenuated.cached_sessions != 1 {
        return Err("changed effective permissions kept stale WebSession".into());
    }
    println!("changed_projection_sessions_created={}", attenuated.sessions_created);

    let mut writable_api = binding(SessionKind::Api, [true, true], 1);
    writable_api.subject = 8;
    writable_api.session_resource = 6208;
    writable_api.params = params(8, [true, true]);
    let advertised = driver.dispatch(
        writable_api,
        get("info/refs?service=git-receive-pack"),
        256 * 1024,
        Duration::from_secs(30),
    )?;
    if !matches!(advertised.result, WebResult::Content { status: 200, .. }) {
        return Err(format!("writable subject did not see Git receive-pack: {:?}", advertised.result).into());
    }
    println!("writable_subject_receive_pack_status=200");

    let mut attenuated_api = binding(SessionKind::Api, [true, false], 2);
    attenuated_api.subject = 8;
    attenuated_api.session_resource = 6208;
    attenuated_api.params = params(8, [true, false]);
    let denial = driver.dispatch(
        attenuated_api,
        get("info/refs?service=git-receive-pack"),
        16 * 1024,
        Duration::from_secs(30),
    )?;
    if !matches!(denial.result, WebResult::ClientError { status: 403, .. }) {
        return Err(format!("attenuated subject still sees Git receive-pack: {:?}", denial.result).into());
    }
    let after_api_attenuation = driver.stats()?;
    if after_api_attenuation.sessions_created != 4 || after_api_attenuation.cached_sessions != 2 {
        return Err("changed API permission projection kept stale app-side session".into());
    }
    println!("attenuated_subject_receive_pack_status=403");

    let upload = driver.dispatch(
        binding(SessionKind::Api, [true, false], 3),
        get("info/refs?service=git-upload-pack"),
        256 * 1024,
        Duration::from_secs(30),
    )?;
    match upload.result {
        WebResult::Content { status: 200, mime_type, body, .. }
            if mime_type.starts_with("application/x-git-upload-pack-advertisement")
                && body.windows(input.commit.len()).any(|part| part == input.commit.as_bytes()) =>
        {
            println!("upload_pack_commit={} bytes={} sha256={:x}", input.commit, body.len(), Sha256::digest(&body));
        }
        other => return Err(format!("retained Git repo upload-pack differs: {other:?}").into()),
    }

    if input.capacity {
        let baseline = driver.stats()?.sessions_created;
        for number in 0..33_u8 {
            let mut friend = binding(SessionKind::Web, [true, false], number + 31);
            friend.session_resource = 7000 + u64::from(number);
            friend.subject = 1000 + u64::from(number);
            friend.params = params(number + 31, [true, false]);
            checked_html(&mut driver, friend, &input.commit)?;
        }
        let full = driver.stats()?;
        if full.sessions_created != baseline + 33 || full.cached_sessions != 32 {
            return Err("33 distinct WebSessions did not retain bounded capacity".into());
        }
        let mut evicted = binding(SessionKind::Web, [true, false], 31);
        evicted.session_resource = 7000;
        evicted.subject = 1000;
        evicted.params = params(31, [true, false]);
        checked_html(&mut driver, evicted, &input.commit)?;
        let revisited = driver.stats()?;
        if revisited.sessions_created != baseline + 34 || revisited.cached_sessions != 32 {
            return Err("least-recently-used app session was not recreated".into());
        }
        println!("capacity_sessions_created={} cached={} evicted_oldest_recreated=true", revisited.sessions_created, revisited.cached_sessions);
    }

    // This last read-only request intentionally has an unusably short budget.
    // It can be delivered despite timeout, so no retry or further app call.
    let timed = driver.dispatch(
        binding(SessionKind::Web, [true, false], 2),
        get("gitweb.cgi?p=repo.git;a=summary"),
        256 * 1024,
        Duration::from_nanos(1),
    );
    if timed.is_ok() {
        return Err("one-nanosecond read unexpectedly completed".into());
    }
    if driver.dispatch(
        binding(SessionKind::Web, [true, false], 2),
        get("gitweb.cgi?p=repo.git;a=summary"),
        256 * 1024,
        Duration::from_secs(1),
    ).is_ok() {
        return Err("uncertain RPC driver permitted resubmission".into());
    }
    println!("uncertain_read_refused_resend=true");
    drop(app);
    Ok(())
}

fn main() -> Result<(), Box<dyn Error>> {
    let input = args()?;
    let manifest = signed_manifest(&input.package_dir)?;
    run(input, manifest)
}
