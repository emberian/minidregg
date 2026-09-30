//! Private, bounded physical qualification of one already signed SPK image.
//! This is deliberately separate from `spk-host`: it grants no Mini authority.

use minidregg_spk_host::sandbox::{spawn_sandbox, SandboxSpec};
use minidregg_spk_rpc::{dispatch_web, Method, RequestContext, SessionParameters, SupervisorConnection, WebRequest, WebResult};
use sandstorm_package::{Spk, SpkManifest};
use sha2::{Digest, Sha256};
use std::error::Error;
use std::fs;
use std::os::unix::net::UnixStream;
use std::path::PathBuf;
use std::time::Duration;

const MAX_SPK_BYTES: u64 = 256 * 1024 * 1024;
const MAX_RESPONSE: usize = 64 * 1024;

struct Args {
    mode: String,
    package_dir: PathBuf,
    persistent_var: PathBuf,
    expected_sha: String,
    bwrap: PathBuf,
    max_var_bytes: u64,
    get_path: String,
}

fn args() -> Result<Args, Box<dyn Error>> {
    let values: Vec<String> = std::env::args().collect();
    if values.len() != 8 || !matches!(values[1].as_str(), "create" | "wake") {
        return Err("usage: spk-smoke create|wake PACKAGE_DIR VAR_DIR SPK_SHA256 BWRAP MAX_VAR_BYTES GET_PATH".into());
    }
    let expected_sha = values[4].clone();
    if expected_sha.len() != 64 || !expected_sha.bytes().all(|b| b.is_ascii_hexdigit() && !b.is_ascii_uppercase()) {
        return Err("expected lowercase 64-character SPK SHA-256".into());
    }
    let max_var_bytes = values[6].parse()?;
    Ok(Args {
        mode: values[1].clone(),
        package_dir: PathBuf::from(&values[2]),
        persistent_var: PathBuf::from(&values[3]),
        expected_sha,
        bwrap: PathBuf::from(&values[5]),
        max_var_bytes,
        get_path: values[7].clone(),
    })
}

fn checked_manifest(input: &Args) -> Result<SpkManifest, Box<dyn Error>> {
    let raw_path = input.package_dir.join("package.spk");
    if fs::metadata(&raw_path)?.len() > MAX_SPK_BYTES {
        return Err("stored SPK exceeds bound".into());
    }
    let raw = fs::read(raw_path)?;
    let actual_sha = format!("{:x}", Sha256::digest(&raw));
    if actual_sha != input.expected_sha || input.package_dir.file_name().and_then(|x| x.to_str())
        != Some(format!("sha256-{}", input.expected_sha).as_str()) {
        return Err("stored signed SPK identity mismatch".into());
    }
    let spk = Spk::parse(&raw)?;
    let manifest = SpkManifest::from_spk(&spk)?;
    let recorded: serde_json::Value = serde_json::from_slice(&fs::read(input.package_dir.join("manifest.json"))?)?;
    if serde_json::to_value(&manifest)? != recorded {
        return Err("published manifest differs from signed package".into());
    }
    Ok(manifest)
}

async fn probe(input: Args, manifest: SpkManifest) -> Result<(), Box<dyn Error>> {
    let command = if input.mode == "create" {
        &manifest.actions.first().ok_or("SPK has no create action")?.command
    } else {
        &manifest.continue_command
    };
    let child = spawn_sandbox(&SandboxSpec {
        bwrap: input.bwrap,
        image_root: input.package_dir.join("root"),
        persistent_var: input.persistent_var,
        persistent_var_max_bytes: input.max_var_bytes,
        argv: command.argv.clone(),
        environ: command.environ.clone(),
        // The app never writes to this harness's stdout/stderr.
        app_output: std::env::temp_dir()
            .join(format!("spk-app-output-{}.log", std::process::id())),
    })?;
    println!("app_output={}", std::env::temp_dir()
        .join(format!("spk-app-output-{}.log", std::process::id())).display());
    println!("app_spawned mode={} pid={}", input.mode, child.process.id());
    let mut process = child.process;
    let rpc: UnixStream = child.rpc;
    rpc.set_nonblocking(true)?;
    let rpc = tokio::net::UnixStream::from_std(rpc)?;
    let (supervisor, rpc_system) = SupervisorConnection::from_connected_stream(rpc);
    tokio::task::spawn_local(async move {
        if let Err(error) = rpc_system.await {
            eprintln!("rpc_transport_end={error}");
        }
    });

    let result = async {
        let view = tokio::time::timeout(Duration::from_secs(90), supervisor.get_view_info()).await??;
        println!("view_title={:?} permissions={} roles={}", view.app_title, view.permission_names.len(), view.role_count);
        let params = SessionParameters {
            identity_id: [0x42; 32],
            display_name: "SPK private smoke".into(),
            preferred_handle: "spk-smoke".into(),
            permissions: vec![false; view.permission_names.len()],
            tab_id: b"spk-smoke".to_vec(),
            // Sandstorm's WebSession requires a full origin-bearing base URL.
            // This reserved domain is a protocol value inside a network-isolated
            // smoke, never a host listener or an authority endpoint.
            base_path: "https://grain.invalid/i/spk-smoke/".into(),
            user_agent: "Mini-SPK-Smoke/1".into(),
            acceptable_languages: vec!["en-US".into()],
        };
        let session = tokio::time::timeout(Duration::from_secs(60), supervisor.new_web_session(&params)).await??;
        println!("web_session=ready");
        let get = WebRequest {
            method: Method::Get,
            path_and_query: input.get_path,
            context: RequestContext::default(),
            body: None,
        };
        let response = dispatch_web(&session, &get, MAX_RESPONSE, Duration::from_secs(60)).await?;
        match response.result {
            WebResult::Content { status, mime_type, body, .. } => {
                println!("get_status={status} mime_type={mime_type:?} bytes={} sha256={:x}", body.len(), Sha256::digest(&body));
            }
            other => println!("get_result={other:?}"),
        }
        Ok::<_, Box<dyn Error>>(())
    }.await;
    // Stopping the bwrap MainPID is paired with the unit's control-group kill;
    // children cannot persist past the transient service's completion.
    let _ = process.kill();
    let wait = process.wait()?;
    println!("app_stopped_status={wait}");
    result
}

fn main() -> Result<(), Box<dyn Error>> {
    let input = args()?;
    let manifest = checked_manifest(&input)?;
    let runtime = tokio::runtime::Builder::new_current_thread().enable_all().build()?;
    let local = tokio::task::LocalSet::new();
    local.block_on(&runtime, probe(input, manifest))
}
