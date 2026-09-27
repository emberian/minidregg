//! Private GitWeb package/RPC qualification. No Mini admission or public API.
//! The only HTTP listener is loopback inside this transient unit's private netns;
//! it adapts one local Git CLI to the packaged bridge over the inherited fd 3.

use minidregg_spk_host::sandbox::{spawn_sandbox, SandboxSpec};
use minidregg_spk_rpc::{
    dispatch_web, Method, RequestContext, SessionParameters, SupervisorConnection, WebRequest,
    WebResult,
};
use sandstorm_package::{Spk, SpkManifest};
use sha2::{Digest, Sha256};
use std::error::Error;
use std::fs;
use std::os::unix::fs::DirBuilderExt;
use std::os::unix::net::UnixStream;
use std::path::{Path, PathBuf};
use std::process::{Child, Command};
use std::time::Duration;
use tokio::io::{AsyncReadExt, AsyncWriteExt};
use tokio::net::{TcpListener, TcpStream};

const SPK_SHA: &str = "2bbfe6d3c705dfb0696905ecd9c1d00d6554cc1224e63dc5545152af5f8f2caa";
const MAX_SPK: usize = 256 * 1024 * 1024;
const MAX_HTTP_HEADER: usize = 16 * 1024;
const MAX_HTTP_BODY: usize = 4 * 1024 * 1024;
const MAX_RPC_RESPONSE: usize = 4 * 1024 * 1024;

struct Args {
    mode: String,
    package_dir: PathBuf,
    persistent_var: PathBuf,
    bwrap: PathBuf,
    max_var_bytes: u64,
    expected_commit: Option<String>,
}

fn args() -> Result<Args, Box<dyn Error>> {
    let words: Vec<_> = std::env::args().collect();
    if !matches!(
        (words.get(1).map(String::as_str), words.len()),
        (Some("create"), 6) | (Some("wake"), 7)
    ) {
        return Err(
            "usage: gitweb-smoke create PACKAGE_DIR VAR_DIR BWRAP MAX_VAR_BYTES | wake PACKAGE_DIR VAR_DIR BWRAP MAX_VAR_BYTES EXPECTED_COMMIT".into(),
        );
    }
    let expected_commit = words.get(6).cloned();
    if let Some(commit) = &expected_commit {
        if commit.len() != 40
            || !commit
                .bytes()
                .all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(&b))
        {
            return Err("expected lowercase SHA-1 commit ID".into());
        }
    }
    Ok(Args {
        mode: words[1].clone(),
        package_dir: PathBuf::from(&words[2]),
        persistent_var: PathBuf::from(&words[3]),
        bwrap: PathBuf::from(&words[4]),
        max_var_bytes: words[5].parse()?,
        expected_commit,
    })
}

fn signed_manifest(package_dir: &Path) -> Result<SpkManifest, Box<dyn Error>> {
    if package_dir.file_name().and_then(|n| n.to_str())
        != Some(format!("sha256-{SPK_SHA}").as_str())
    {
        return Err("wrong image directory".into());
    }
    let stored = package_dir.join("package.spk");
    if fs::metadata(&stored)?.len() as usize > MAX_SPK {
        return Err("SPK too large".into());
    }
    let raw = fs::read(stored)?;
    if format!("{:x}", Sha256::digest(&raw)) != SPK_SHA {
        return Err("SPK hash mismatch".into());
    }
    let spk = Spk::parse(&raw)?;
    let manifest = SpkManifest::from_spk(&spk)?;
    if manifest.app_id.0 != "6va4cjamc21j0znf5h5rrgnv0rpyvh1vaxurkrgknefvj0x63ash"
        || manifest.app_version != 10
    {
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

fn session_params(bits: [bool; 2]) -> SessionParameters {
    SessionParameters {
        identity_id: [0x47; 32],
        display_name: "GitWeb private smoke".into(),
        preferred_handle: "gitweb-smoke".into(),
        permissions: bits.to_vec(),
        tab_id: b"gitweb-smoke".to_vec(),
        base_path: "https://grain.invalid/i/gitweb-smoke/".into(),
        user_agent: "Mini-GitWeb-Smoke/1".into(),
        acceptable_languages: vec!["en-US".into()],
    }
}

fn check_view(view: &minidregg_spk_rpc::ViewInfo) -> Result<(), Box<dyn Error>> {
    if view.permission_names != ["read", "write"]
        || view.roles.len() != 2
        || view.roles[0].title.default_text != "guest"
        || view.roles[0].permissions != [true, false]
        || view.roles[1].title.default_text != "developer"
        || view.roles[1].permissions != [true, true]
        || view.denied_permissions.iter().any(|b| *b)
    {
        return Err("GitWeb signed permission/role contract differs at runtime".into());
    }
    println!(
        "view={:?} roles=guest[read],developer[read,write]",
        view.app_title
    );
    Ok(())
}

struct HttpRequest {
    method: Method,
    path: String,
    mime_type: String,
    body: Vec<u8>,
}

fn find_header_end(bytes: &[u8]) -> Option<usize> {
    bytes
        .windows(4)
        .position(|w| w == b"\r\n\r\n")
        .map(|p| p + 4)
}

async fn read_request(stream: &mut TcpStream) -> Result<HttpRequest, Box<dyn Error>> {
    let mut raw = Vec::new();
    let mut chunk = [0u8; 4096];
    let header_end = loop {
        if let Some(end) = find_header_end(&raw) {
            break end;
        }
        if raw.len() >= MAX_HTTP_HEADER {
            return Err("HTTP header exceeds bound".into());
        }
        let n = stream.read(&mut chunk).await?;
        if n == 0 {
            return Err("EOF before HTTP header".into());
        }
        raw.extend_from_slice(&chunk[..n]);
    };
    if header_end > MAX_HTTP_HEADER {
        return Err("HTTP header exceeds bound".into());
    }
    let head = std::str::from_utf8(&raw[..header_end])?;
    let mut lines = head.split("\r\n");
    let line = lines.next().ok_or("empty HTTP request")?;
    let mut parts = line.split(' ');
    let method = match parts.next() {
        Some("GET") => Method::Get,
        Some("POST") => Method::Post,
        _ => return Err("unexpected HTTP method".into()),
    };
    let raw_path = parts.next().ok_or("missing HTTP path")?;
    if parts.next() != Some("HTTP/1.1") || parts.next().is_some() || !raw_path.starts_with('/') {
        return Err("unexpected HTTP request line".into());
    }
    let path = raw_path[1..].to_owned();
    let mut length = None;
    let mut mime_type = String::new();
    for header in lines.take_while(|s| !s.is_empty()) {
        let (name, value) = header.split_once(':').ok_or("malformed HTTP header")?;
        let value = value.trim();
        if name.eq_ignore_ascii_case("Content-Length") {
            if length.is_some() {
                return Err("duplicate Content-Length".into());
            }
            length = Some(value.parse::<usize>()?);
        } else if name.eq_ignore_ascii_case("Content-Type") {
            mime_type = value.to_owned();
        } else if name.eq_ignore_ascii_case("Transfer-Encoding") {
            return Err("chunked or encoded request unsupported".into());
        }
    }
    let length = length.unwrap_or(0);
    if length > MAX_HTTP_BODY || raw.len() - header_end > length {
        return Err("HTTP body outside bound or conflicting length".into());
    }
    while raw.len() - header_end < length {
        let n = stream.read(&mut chunk).await?;
        if n == 0 {
            return Err("EOF in HTTP body".into());
        }
        raw.extend_from_slice(&chunk[..n]);
        if raw.len() - header_end > length {
            return Err("HTTP body exceeds Content-Length".into());
        }
    }
    Ok(HttpRequest {
        method,
        path,
        mime_type,
        body: raw[header_end..].to_vec(),
    })
}

fn expected_route(request: &HttpRequest) -> bool {
    matches!(
        (&request.method, request.path.as_str()),
        (
            Method::Get,
            "info/refs?service=git-receive-pack" | "info/refs?service=git-upload-pack"
        ) | (Method::Post, "git-receive-pack" | "git-upload-pack")
    )
}

async fn handle_http(
    mut stream: TcpStream,
    session: &minidregg_spk_rpc::web_session_capnp::web_session::Client,
    receive_post_seen: &mut bool,
) -> Result<(), Box<dyn Error>> {
    let request =
        tokio::time::timeout(Duration::from_secs(30), read_request(&mut stream)).await??;
    if !expected_route(&request) {
        return Err("Git requested an unexpected route".into());
    }
    if request.method == Method::Post && request.path == "git-receive-pack" {
        if *receive_post_seen {
            return Err("receive-pack POST would be resent".into());
        }
        *receive_post_seen = true; // before RPC send: a timeout leaves its effect uncertain.
    }
    let body = if request.method == Method::Post {
        Some(minidregg_spk_rpc::Body {
            mime_type: request.mime_type,
            encoding: String::new(),
            bytes: request.body,
        })
    } else {
        None
    };
    let reply = dispatch_web(
        session,
        &WebRequest {
            method: request.method,
            path_and_query: request.path.clone(),
            context: RequestContext::default(),
            body,
        },
        MAX_RPC_RESPONSE,
        Duration::from_secs(45),
    )
    .await?;
    let (status, mime, bytes) = match reply.result {
        WebResult::Content {
            status,
            mime_type,
            body,
            ..
        } => (status, mime_type, body),
        WebResult::ClientError { status, html, .. } => {
            (status, "text/html".into(), html.into_bytes())
        }
        other => return Err(format!("unrepresentable Git RPC response: {other:?}").into()),
    };
    if !mime.is_ascii() || mime.contains(['\r', '\n']) {
        return Err("invalid response MIME".into());
    }
    let head = format!("HTTP/1.1 {status} {}\r\nContent-Type: {mime}\r\nContent-Length: {}\r\nConnection: close\r\n\r\n",
        if status == 200 { "OK" } else { "Result" }, bytes.len());
    stream.write_all(head.as_bytes()).await?;
    stream.write_all(&bytes).await?;
    stream.shutdown().await?;
    println!(
        "git_rpc method={:?} path={} status={} bytes={} sha256={:x}",
        request.method,
        request.path,
        status,
        bytes.len(),
        Sha256::digest(&bytes)
    );
    Ok(())
}

fn git_base() -> tokio::process::Command {
    let mut command = tokio::process::Command::new("/usr/bin/git");
    command
        .env_clear()
        .env("PATH", "/usr/bin:/bin")
        .env("LANG", "C")
        .env("GIT_CONFIG_NOSYSTEM", "1")
        .env("GIT_CONFIG_GLOBAL", "/dev/null")
        .env("GIT_TERMINAL_PROMPT", "0")
        .arg("-c")
        .arg("protocol.version=0")
        .arg("-c")
        .arg("http.maxRequests=1")
        .arg("-c")
        .arg("http.postBuffer=4194304");
    command.kill_on_drop(true);
    command
}

async fn git_with_proxy(
    session: &minidregg_spk_rpc::web_session_capnp::web_session::Client,
    arguments: &[String],
    receive_post_seen: &mut bool,
) -> Result<(), Box<dyn Error>> {
    let listener = TcpListener::bind("127.0.0.1:0").await?;
    let port = listener.local_addr()?.port();
    let url = format!("http://127.0.0.1:{port}/");
    let args: Vec<String> = arguments
        .iter()
        .map(|arg| arg.replace("@URL@", &url))
        .collect();
    let mut command = git_base();
    command
        .args(args)
        .stdout(std::process::Stdio::piped())
        .stderr(std::process::Stdio::piped());
    let child = command.spawn()?;
    tokio::time::timeout(Duration::from_secs(120), async {
        let mut output = Box::pin(child.wait_with_output());
        let mut count = 0;
        loop {
            tokio::select! {
                result = &mut output => {
                    let result = result?;
                    println!("git_exit={} stdout={:?} stderr={:?}", result.status,
                        String::from_utf8_lossy(&result.stdout), String::from_utf8_lossy(&result.stderr));
                    if !result.status.success() { return Err("Git smart HTTP command failed".into()); }
                    return Ok(());
                }
                accepted = listener.accept() => {
                    let (stream, _) = accepted?;
                    count += 1;
                    if count > 16 { return Err("too many Git HTTP requests".into()); }
                    handle_http(stream, session, receive_post_seen).await?;
                }
            }
        }
    }).await?
}

fn git_local(arguments: &[&str], cwd: &Path) -> Result<String, Box<dyn Error>> {
    let output = Command::new("/usr/bin/git")
        .args(arguments)
        .current_dir(cwd)
        .env("GIT_CONFIG_NOSYSTEM", "1")
        .env("GIT_CONFIG_GLOBAL", "/dev/null")
        .output()?;
    if !output.status.success() {
        return Err(format!(
            "local Git fixture failed: {:?}",
            String::from_utf8_lossy(&output.stderr)
        )
        .into());
    }
    Ok(String::from_utf8(output.stdout)?.trim().to_owned())
}

async fn web_get(
    session: &minidregg_spk_rpc::web_session_capnp::web_session::Client,
    path: &str,
    expected_commit: &str,
) -> Result<(), Box<dyn Error>> {
    let reply = dispatch_web(
        session,
        &WebRequest {
            method: Method::Get,
            path_and_query: path.into(),
            context: RequestContext::default(),
            body: None,
        },
        256 * 1024,
        Duration::from_secs(45),
    )
    .await?;
    match reply.result {
        WebResult::Content {
            status: 200,
            mime_type,
            body,
            ..
        } => {
            if !mime_type.starts_with("text/html")
                || (!body
                    .windows(expected_commit.len())
                    .any(|part| part == expected_commit.as_bytes())
                    && !body
                        .windows(b"Mini SPK fixture".len())
                        .any(|part| part == b"Mini SPK fixture"))
            {
                return Err("GitWeb HTML did not identify the pushed commit".into());
            }
            println!(
                "browser_path={path:?} status=200 mime={mime_type:?} bytes={} sha256={:x}",
                body.len(),
                Sha256::digest(&body)
            );
            Ok(())
        }
        other => Err(format!("GitWeb browser GET failed: {other:?}").into()),
    }
}

async fn run(input: Args, manifest: SpkManifest) -> Result<(), Box<dyn Error>> {
    let command = if input.mode == "create" {
        &manifest
            .actions
            .first()
            .ok_or("no GitWeb create action")?
            .command
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
    })?;
    println!("app_spawned mode={} pid={}", input.mode, child.process.id());
    let app = App(child.process);
    let rpc: UnixStream = child.rpc;
    rpc.set_nonblocking(true)?;
    let (supervisor, rpc_system) =
        SupervisorConnection::from_connected_stream(tokio::net::UnixStream::from_std(rpc)?);
    tokio::task::spawn_local(async move {
        if let Err(error) = rpc_system.await {
            eprintln!("rpc_transport_end={error}");
        }
    });
    let view = tokio::time::timeout(Duration::from_secs(90), supervisor.get_view_info()).await??;
    check_view(&view)?;
    let developer = tokio::time::timeout(
        Duration::from_secs(60),
        supervisor.new_api_session(&session_params([true, true])),
    )
    .await??;
    let guest = tokio::time::timeout(
        Duration::from_secs(60),
        supervisor.new_api_session(&session_params([true, false])),
    )
    .await??;
    let owner_web = tokio::time::timeout(
        Duration::from_secs(60),
        supervisor.new_web_session(&session_params([true, true])),
    )
    .await??;
    println!("api_sessions=developer,guest web_session=owner");

    let scratch = PathBuf::from(format!("/tmp/mini-gitweb-smoke-{}", std::process::id()));
    fs::DirBuilder::new().mode(0o700).create(&scratch)?;
    let mut receive_post_seen = false;
    let work_result = async {
        let expected = if input.mode == "create" {
            let source = scratch.join("source");
            fs::create_dir(&source)?;
            git_local(&["init", "-q", "-b", "master"], &source)?;
            fs::write(
                source.join("README.md"),
                b"Mini GitWeb private smoke: one signed SPK push.\n",
            )?;
            git_local(&["add", "README.md"], &source)?;
            git_local(
                &[
                    "-c",
                    "user.name=Mini SPK Smoke",
                    "-c",
                    "user.email=spk-smoke@example.invalid",
                    "commit",
                    "-qm",
                    "Mini SPK fixture",
                ],
                &source,
            )?;
            let expected = git_local(&["rev-parse", "HEAD"], &source)?;
            println!("source_commit={expected}");
            git_with_proxy(
                &developer,
                &[
                    "-C".into(),
                    source.display().to_string(),
                    "push".into(),
                    "--porcelain".into(),
                    "@URL@".into(),
                    "HEAD:refs/heads/master".into(),
                ],
                &mut receive_post_seen,
            )
            .await?;
            if !receive_post_seen {
                return Err("push performed no receive-pack POST".into());
            }
            println!("push_post_count=1");
            expected
        } else {
            input
                .expected_commit
                .clone()
                .ok_or("wake requires pinned expected commit")?
        };
        let denial = dispatch_web(
            &guest,
            &WebRequest {
                method: Method::Get,
                path_and_query: "info/refs?service=git-receive-pack".into(),
                context: RequestContext::default(),
                body: None,
            },
            16 * 1024,
            Duration::from_secs(30),
        )
        .await?;
        if !matches!(denial.result, WebResult::ClientError { status: 403, .. }) {
            return Err(format!(
                "guest receive-pack advertisement was not forbidden: {:?}",
                denial.result
            )
            .into());
        }
        println!("guest_receive_pack_status=403");
        let destination = scratch.join("clone");
        git_with_proxy(
            &guest,
            &[
                "clone".into(),
                "--quiet".into(),
                "@URL@".into(),
                destination.display().to_string(),
            ],
            &mut receive_post_seen,
        )
        .await?;
        let readme = fs::read(destination.join("README.md"))?;
        if readme != b"Mini GitWeb private smoke: one signed SPK push.\n" {
            return Err("cloned README mismatch".into());
        }
        let fetched = git_local(&["rev-parse", "HEAD"], &destination)?;
        if fetched != expected {
            return Err("fetched HEAD differs from pushed/retained commit".into());
        }
        println!(
            "guest_fetched_commit={fetched} readme_sha256={:x}",
            Sha256::digest(&readme)
        );
        web_get(&owner_web, "gitweb.cgi?p=repo.git;a=summary", &expected).await?;
        Ok::<(), Box<dyn Error>>(())
    }
    .await;
    if work_result.is_ok() {
        let _ = fs::remove_dir_all(&scratch);
    } else {
        // A receive-pack timeout may have committed. Retain the exact local
        // commit/pack inputs for inspection; never attempt another push here.
        eprintln!("uncertain_or_failed_fixture_scratch={}", scratch.display());
    }
    drop(app); // systemd KillMode=control-group reaps bridge/nginx/fcgiwrap too.
    work_result
}

fn main() -> Result<(), Box<dyn Error>> {
    let input = args()?;
    let manifest = signed_manifest(&input.package_dir)?;
    let runtime = tokio::runtime::Builder::new_current_thread()
        .enable_all()
        .build()?;
    tokio::task::LocalSet::new().block_on(&runtime, run(input, manifest))
}
