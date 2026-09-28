// Explicit component gate. It runs the exact native Unix custodian parser
// and a real Git HTTP backend in private scratch, without a Mini permit.
#[test]
#[ignore = "manual real-Git/Unix-entrance component gate; run with MINI_GITWEB_HUMAN_HELPER and a bounded test deadline"]
fn gitweb_human_seed_lost_reply_then_read_only_lookup() {
    use std::os::unix::fs::OpenOptionsExt;
    use std::process::{Command, Stdio};
    use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
    use std::sync::Arc;

    fn git(args: &[&str]) -> Vec<u8> {
        let output = Command::new("/usr/bin/git").args(args).output().unwrap();
        assert!(output.status.success(), "real Git command failed");
        output.stdout
    }

    fn backend(root: &Path, request: ReceivedRequest) -> io::Result<Vec<u8>> {
        let (path, query) = request
            .path_and_query
            .split_once('?')
            .unwrap_or((&request.path_and_query, ""));
        let content_type = request
            .ordinary_headers
            .iter()
            .find(|(name, _)| name == "content-type")
            .map(|(_, value)| value.as_str())
            .unwrap_or("");
        let mut child = Command::new("/usr/bin/git")
            .arg("http-backend")
            .env_clear()
            .env("PATH", "/usr/bin:/bin")
            .env("GIT_CONFIG_NOSYSTEM", "1")
            .env("GIT_CONFIG_GLOBAL", "/dev/null")
            .env("GIT_HTTP_EXPORT_ALL", "1")
            .env("GIT_PROJECT_ROOT", root)
            .env("PATH_INFO", format!("/{path}"))
            .env("QUERY_STRING", query)
            .env("REQUEST_METHOD", request.method.as_str())
            .env("CONTENT_TYPE", content_type)
            .env("CONTENT_LENGTH", request.body.len().to_string())
            .env("REMOTE_USER", "component-probe")
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::null())
            .spawn()?;
        child.stdin.take().unwrap().write_all(&request.body)?;
        let output = child.wait_with_output()?;
        if !output.status.success() || output.stdout.len() > 512 * 1024 {
            return Err(refuse("real Git HTTP backend failed"));
        }
        let boundary = output
            .stdout
            .windows(4)
            .position(|part| part == b"\r\n\r\n")
            .ok_or_else(|| refuse("real Git CGI header absent"))?
            + 4;
        let header = std::str::from_utf8(&output.stdout[..boundary])
            .map_err(|_| refuse("real Git CGI header invalid"))?;
        let mut status = "200 OK";
        let mut mime = None;
        for line in header.trim_end_matches("\r\n\r\n").split("\r\n") {
            if let Some(value) = line.strip_prefix("Status: ") {
                status = value;
            } else if let Some(value) = line.strip_prefix("Content-Type: ") {
                mime = Some(value);
            }
        }
        let mime = mime.ok_or_else(|| refuse("real Git CGI MIME absent"))?;
        let body = &output.stdout[boundary..];
        let mut response = format!("HTTP/1.1 {status}\r\nContent-Type: {mime}\r\nContent-Length: {}\r\nConnection: close\r\n\r\n", body.len()).into_bytes();
        response.extend_from_slice(body);
        Ok(response)
    }

    let helper = std::env::var("MINI_GITWEB_HUMAN_HELPER")
        .expect("pin source-matched gitweb-human-journey binary path");
    let runtime = std::env::var("XDG_RUNTIME_DIR").unwrap();
    let nonce = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap()
        .as_nanos();
    let root = Path::new(&runtime).join(format!(
        "mini-gitweb-human-probe-{}-{nonce}",
        std::process::id()
    ));
    fs::DirBuilder::new().mode(0o700).create(&root).unwrap();
    let custodian = root.join("custodian");
    initialize_custodian(
        &custodian,
        "friend-probe.localhost",
        "8401",
        "7",
        "8410",
        "8500",
        "api",
    )
    .unwrap();
    let entrance = PrivateHttpEntrance::bind(&custodian).unwrap();
    let bare = root.join("repo.git");
    let bare_text = bare.to_str().unwrap();
    git(&["init", "--bare", "--initial-branch=master", bare_text]);
    git(&["-C", bare_text, "config", "http.receivepack", "true"]);
    let note = root.join("note.txt");
    let mut source = OpenOptions::new()
        .write(true)
        .create_new(true)
        .mode(0o600)
        .open(&note)
        .unwrap();
    source
        .write_all(b"Real native entrance and Git backend probe.\n")
        .unwrap();
    source.sync_all().unwrap();
    let attempt = root.join("seed-attempt");
    let socket = custodian.join("http.sock");
    let api_token = custodian.join("api.token");
    let stop = Arc::new(AtomicBool::new(false));
    let received = Arc::new(AtomicUsize::new(0));
    let stop_server = Arc::clone(&stop);
    let received_server = Arc::clone(&received);
    entrance.listener.set_nonblocking(true).unwrap();
    let root_server = root.clone();
    let server = std::thread::spawn(move || {
        let deadline = Instant::now() + Duration::from_secs(90);
        while !stop_server.load(Ordering::SeqCst) && Instant::now() < deadline {
            match entrance.listener.accept() {
                Ok((peer, _)) => {
                    assert_eq!(peer_uid(&peer), Some(unsafe { libc::geteuid() }));
                    let result = handle_stream_with(
                        peer,
                        &entrance.policy,
                        Some(&custodian),
                        &mut |request, kind, _| {
                            assert_eq!(kind, EntranceKind::Api);
                            let is_receive = request.method == Method::Post
                                && request.path_and_query == "repo.git/git-receive-pack";
                            let response = backend(&root_server, request)?;
                            if is_receive {
                                assert_eq!(received_server.fetch_add(1, Ordering::SeqCst), 0);
                                // Git has accepted the POST. Discard precisely its reply.
                                return Err(refuse("deliberately lost accepted Git reply"));
                            }
                            Ok(response)
                        },
                    );
                    assert!(result.is_ok());
                }
                Err(error) if error.kind() == io::ErrorKind::WouldBlock => {
                    std::thread::sleep(Duration::from_millis(10));
                }
                Err(error) => panic!("native entrance accept failed: {error}"),
            }
        }
        assert!(Instant::now() < deadline, "component entrance timed out");
    });

    let seeded = Command::new(&helper)
        .arg("seed-api")
        .arg(&socket)
        .arg(&api_token)
        .arg("friend-probe.localhost")
        .arg("public/research-note.txt")
        .arg(&note)
        .arg("Probe first commit")
        .arg(&attempt)
        .output()
        .unwrap();
    assert!(
        !seeded.status.success(),
        "deliberately lost reply was accepted"
    );
    assert_eq!(received.load(Ordering::SeqCst), 1);
    assert!(attempt.join("receive-pack-forwarded.marker").exists());
    let committed = String::from_utf8(git(&[
        "--git-dir",
        bare_text,
        "rev-parse",
        "refs/heads/master",
    ]))
    .unwrap();
    assert_eq!(committed.trim().len(), 40);

    let lookup = Command::new(&helper)
        .arg("lookup-api")
        .arg(&socket)
        .arg(&api_token)
        .arg("friend-probe.localhost")
        .arg(&attempt)
        .output()
        .unwrap();
    assert!(
        lookup.status.success(),
        "read-only recovery failed: {}",
        String::from_utf8_lossy(&lookup.stderr)
    );
    let result: serde_json::Value =
        serde_json::from_slice(&fs::read(attempt.join("lookup-0001.json")).unwrap()).unwrap();
    assert_eq!(result["matchesExpected"], true);
    assert_eq!(result["observedRemoteCommit"], committed.trim());
    assert_eq!(
        received.load(Ordering::SeqCst),
        1,
        "lookup resent receive-pack"
    );
    stop.store(true, Ordering::SeqCst);
    server.join().unwrap();
    fs::remove_dir_all(root).unwrap();
}
