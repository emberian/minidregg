use super::*;

// A controlled native-client stub supplies view and submit response files.
// These test the real tool_call, transition, journal, and read paths, not Mini admission.
pub(super) fn fixture(
    fail_release: bool,
    fail_disconnect: bool,
    pre_submit: bool,
) -> (Runtime, PathBuf) {
    let root = PathBuf::from("/tmp").join(format!(
        "gpr-{}-{}",
        std::process::id(),
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos()
    ));
    fs::create_dir(&root).unwrap();
    let state = root.join("state");
    fs::create_dir(&state).unwrap();
    fs::write(state.join("status"), b"0").unwrap();
    if fail_release {
        fs::write(state.join("fail-release"), b"1").unwrap();
    }
    if fail_disconnect {
        fs::write(state.join("fail-disconnect"), b"1").unwrap();
    }
    if pre_submit {
        fs::write(state.join("pre-submit"), b"1").unwrap();
    }
    let mini = root.join("controlled-mini");
    let script = r#"#!/bin/sh
set -eu
state='__STATE__'
command=$1
shift
dir=
intent=
host=
config=
socket=
while [ "$#" -gt 0 ]; do
  case "$1" in
    --dir) dir=$2; shift 2 ;;
    --intent) intent=$2; shift 2 ;;
    --host) host=$2; shift 2 ;;
    --config) config=$2; shift 2 ;;
    --socket) socket=$2; shift 2 ;;
    *) shift ;;
  esac
done
mkdir -p "$dir"
if [ "$command" = query ]; then
  case "$dir" in
    *resource-read-*)
      printf '%s\n' '{"type":"resource","cell":{"root":"701","entries":[]}}' > "$dir/view.json" ;;
    *)
      status=$(cat "$state/status")
      printf '{"cell":{"root":"100","grain":{"task":"7102","generation":"1","status":"%s","remaining":"10","reserved":"3"}}}\n' "$status" > "$dir/view.json"
      printf '%s\n' '{"authorityRoot":"200","signing":[{}],"worldRoot":"300"}' > "$dir/challenge.json" ;;
  esac
  exit 0
fi
[ "$command" = submit ] || exit 40
if [ -f "$state/pre-submit" ] && grep -q '"type": "settle"' "$intent" &&
    grep -q '"target": "7003"' "$intent"; then
  cp "$config" "$dir/config.json"
  printf 'signed observation' > "$dir/signed-observation.bin"
  printf '{"format":"minidregg-resource-client-attempt-v1","operation":"submit","host":"%s","config":"%s/config.json","socket":"%s"}\n' "$host" "$dir" "$socket" > "$dir/attempt.json"
  printf '\377canonical refused outcome' > "$dir/pre-submit-refusal.frame"
  digest() { /usr/bin/openssl dgst -sha256 "$1" | awk '{print $NF}'; }
  printf '{"type":"minidregg-pre-submit-refusal-v1","stage":"prepare","operation":1,"frameSha256":"%s","requestSha256":"%s","hostConfigSha256":"%s","attemptManifestSha256":"%s"}\n' \
    "$(digest "$dir/pre-submit-refusal.frame")" "$(digest "$dir/signed-observation.bin")" \
    "$(digest "$dir/config.json")" "$(digest "$dir/attempt.json")" > "$dir/pre-submit-refusal.json"
  exit 1
fi
printf call > "$dir/call.bin"
printf outcome > "$dir/outcome.bin"
if grep -q '"type": "attach"' "$intent"; then
  printf 1 > "$state/status"
elif grep -q '"type": "reserve"' "$intent"; then
  printf 3 > "$state/status"
elif grep -q '"type": "disconnect"' "$intent"; then
  [ ! -f "$state/fail-disconnect" ] || exit 1
  printf 0 > "$state/status"
elif grep -q '"type": "settle"' "$intent"; then
  if grep -q '"target": "7003"' "$intent"; then
    if grep -q '"expectedTargetRoot": "700"' "$intent"; then
      printf '%s\n' '{"type":"refused","reason":"stale content root"}' > "$dir/outcome.json"
      exit 1
    fi
  elif [ -f "$state/fail-release" ]; then
    exit 1
  fi
  printf 1 > "$state/status"
fi
printf '%s\n' '{"type":"confirmed","confirmation":"installed","worldRoot":"300","transactionId":"11","eventId":"12","acceptedCount":"13"}' > "$dir/outcome.json"
"#
    .replace("__STATE__", state.to_str().unwrap());
    fs::write(&mini, script).unwrap();
    fs::set_permissions(&mini, fs::Permissions::from_mode(0o700)).unwrap();
    let host = root.join("host");
    let host_config = root.join("host-config.json");
    fs::write(&host_config, b"pinned host config").unwrap();
    if pre_submit {
        fs::write(&host, b"#!/bin/sh\n[ \"$2\" = inspect ] && [ \"$3\" = outcome ] || exit 1\nprintf '{\"type\":\"refused\",\"phase\":\"70726570617265\",\"detail\":\"7374616c65546172676574\"}\\n' > \"$5\"\n").unwrap();
        fs::set_permissions(&host, fs::Permissions::from_mode(0o700)).unwrap();
    }
    let config = Config {
        mini,
        host,
        host_config,
        host_socket: pre_submit.then(|| root.join("mini.sock")),
        control_socket: state.join("control.sock"),
        custody_key: root.join("parent.key"),
        state_dir: state,
        cwd: root.clone(),
        task: "7101".into(),
        subject: "7".into(),
        capability: "71".into(),
        query_capability: "74".into(),
        policy_control_capability: Some("72".into()),
        foreground_tool: None,
        dispatch_task: None,
        tool_task: Some(ToolTask {
            room: None,
            task: "7102".into(),
            subject: "8".into(),
            capability: "81".into(),
            query_capability: "82".into(),
            custody_key: root.join("tool.key"),
            parent_capability: "73".into(),
            parent_observe_capability: "75".into(),
            reserve: "3".into(),
            charge: "1".into(),
            allowed_publications: vec![PublicationGrant {
                kind: "object".into(),
                target: "7003".into(),
                capability: "93".into(),
                observe_capability: "94".into(),
            }],
            allowed_reads: vec![resource_tools::AllowedResourceRead {
                name: "publication".into(),
                kind: "object".into(),
                target: "7003".into(),
                observe_capability: "95".into(),
                max_result_bytes: 1024,
                fn_inbox_summary: false,
            }],
            resource_workspace: None,
            allowed_birth_families: vec![],
            allowed_application_families: vec![],
            allowed_session_families: vec![],
            registered_shared_applications: vec![],
            allowed_application_api_routes: vec![],
            allowed_application_lifetime_routes: vec![],
            agent_api_host_sha256: None,
            lifetime_api_host_sha256: None,
            current_birth_host_sha256: None,
        }),
        provider_task: None,
        commands: vec![],
    };
    let mut runtime = Runtime::open(config, root.join("config.json")).unwrap();
    runtime.journal.connection = Connection::Hard;
    runtime.journal.child = Some(ChildRecord {
        operation_id: 1,
        pid: 1,
        program: root.join("hermes-acp"),
        pgid: 1,
        unit: None,
        launch_gate_protocol: None,
    });
    runtime.journal.prompt_witness = Some(json!({"task":"7101","before":{"generation":"1"}}));
    runtime.journal.hermes_session = Some(HermesSession {
        id: "test-session".into(),
        workspace: root.clone(),
        load_verified: true,
        state_fingerprint: None,
        retention_issue: None,
        pending_prompt: true,
    });
    runtime.prompt_active = true;
    runtime.save().unwrap();
    (runtime, root)
}

#[test]
fn workspace_recovery_releases_only_verified_prepare_refusal() {
    let (mut runtime, root) = fixture(false, false, true);
    let mini = fs::read_to_string(&runtime.config.mini)
        .unwrap()
        .replace("\"reserved\":\"3\"", "\"reserved\":\"0\"");
    fs::write(&runtime.config.mini, mini).unwrap();
    let workspace = runtime.config.state_dir.join("resource-workspace");
    for path in [
        workspace.clone(),
        workspace.join("refs"),
        workspace.join("sources"),
        workspace.join("attempts"),
        workspace.join("proposals"),
    ] {
        fs::create_dir(&path).unwrap();
        fs::set_permissions(&path, fs::Permissions::from_mode(0o700)).unwrap();
    }
    let tool = runtime.config.tool_task.as_mut().unwrap();
    tool.resource_workspace = Some(workspace.clone());
    let record = json!({"type":"minidregg-participant-workspace-v1",
        "host":runtime.config.host,"config":runtime.config.host_config,
        "key":tool.custody_key,"subject":tool.subject,"socket":runtime.config.host_socket,
        "birthContext":null,"namespaceRoot":null});
    fs::write(
        workspace.join("workspace.json"),
        serde_json::to_vec(&record).unwrap(),
    )
    .unwrap();
    fs::set_permissions(
        workspace.join("workspace.json"),
        fs::Permissions::from_mode(0o600),
    )
    .unwrap();
    let proposal_dir = workspace.join("proposals").join("1");
    fs::create_dir(&proposal_dir).unwrap();
    let source = b"{\"type\": \"settle\", \"target\": \"7003\"}";
    fs::write(proposal_dir.join("intent.json"), source).unwrap();
    let request = b"{\"type\":\"minidregg-workspace-proposal-v1\"}";
    fs::write(
        runtime
            .config
            .state_dir
            .join("workspace-proposal-0000000000000001.json"),
        request,
    )
    .unwrap();
    let attempt = workspace.join("attempts").join("2");
    let source_path = root.join("workspace-source.json");
    fs::write(&source_path, source).unwrap();
    let status = Command::new(&runtime.config.mini)
        .arg("submit")
        .arg("--host")
        .arg(&runtime.config.host)
        .arg("--config")
        .arg(&runtime.config.host_config)
        .arg("--socket")
        .arg(runtime.config.host_socket.as_ref().unwrap())
        .arg("--intent")
        .arg(&source_path)
        .arg("--dir")
        .arg(&attempt)
        .status()
        .unwrap();
    assert!(!status.success());
    fs::set_permissions(&attempt, fs::Permissions::from_mode(0o700)).unwrap();
    fs::write(attempt.join("intent.json"), source).unwrap();
    let make_pending = |runtime: &mut Runtime| {
        runtime.journal.next_operation_id = 3;
        runtime.journal.workspace_proposals = vec![WorkspaceProposal {
            id: 1,
            request_sha256: sha256_bytes(request).unwrap(),
            intent_sha256: sha256_bytes(source).unwrap(),
            submitted: true,
        }];
        runtime.journal.workspace_attempt = Some(WorkspaceAttempt {
            operation_id: 2,
            proposal_id: 1,
            intent_sha256: sha256_bytes(source).unwrap(),
            attempt: attempt.clone(),
            definite: false,
            no_submit: false,
            authored: None,
        });
        runtime.save().unwrap();
    };
    make_pending(&mut runtime);
    let refusal = runtime.workspace_recover_operation(2, true).unwrap();
    assert_eq!(refusal["outcome"]["type"], "refused");
    assert_eq!(refusal["toolCharge"], "0");
    assert!(runtime.journal.workspace_attempt.is_none());

    make_pending(&mut runtime);
    let marker = attempt.join("pre-submit-refusal.json");
    let exact_marker = fs::read(&marker).unwrap();
    fs::remove_file(&marker).unwrap();
    assert!(runtime.workspace_recover_operation(2, true).is_err());
    assert!(runtime.journal.workspace_attempt.is_some());
    fs::write(&marker, &exact_marker).unwrap();
    fs::write(
        attempt.join("signed-observation.bin"),
        b"changed after prepare",
    )
    .unwrap();
    assert!(runtime.workspace_recover_operation(2, true).is_err());
    assert!(runtime.journal.workspace_attempt.is_some());
    fs::remove_dir_all(root).unwrap();
}

#[test]
fn foreground_status_uses_signed_parent_lease_without_a_hermes_child() {
    let (mut runtime, root) = fixture(false, false, false);
    let original = fs::read_to_string(&runtime.config.mini).unwrap();
    let patched = original
        .replace(
            "status=$(cat \"$state/status\")",
            "status=$(cat \"$state/status\")\n      target=$(jq -r .purpose.target \"$intent\")",
        )
        .replace("\"task\":\"7102\"", "\"task\":\"%s\"")
        .replace(
            "' \"$status\" > \"$dir/view.json\"",
            "' \"$target\" \"$status\" > \"$dir/view.json\"",
        );
    assert_ne!(original, patched);
    fs::write(&runtime.config.mini, patched).unwrap();
    runtime.config.foreground_tool = Some(ForegroundToolProfile {
        reserve: "2".into(),
        charge: "0".into(),
    });
    runtime.journal.connection = Connection::Soft;
    runtime.journal.child = None;
    runtime.journal.hermes_session = None;
    runtime.journal.prompt_witness = None;
    runtime.prompt_active = false;
    runtime.journal.binding = json!({"config":runtime.config,"configPath":runtime.config_path});
    runtime.save().unwrap();
    let server = control::start(&runtime.config.control_socket, Arc::new(|_| {})).unwrap();
    let mut connection = UnixStream::connect(&runtime.config.control_socket).unwrap();
    connection.write_all(b"attach terminal-v1 soft\n").unwrap();
    let attachment_id = match server.events.recv_timeout(Duration::from_secs(2)).unwrap() {
        control::Event::Attached { id, soft: true } => id,
        other => panic!("unexpected foreground attach: {other:?}"),
    };
    let mut attached = String::new();
    io::BufReader::new(&mut connection)
        .read_line(&mut attached)
        .unwrap();
    runtime.output = Some(server.output_handle());
    let (_sender, input) = mpsc::channel();
    let before_rejected = runtime.journal.next_operation_id;
    assert!(runtime.foreground_tool(
        attachment_id,
        br#"{"requestId":"ffffffffffffffffffffffffffffffff","name":"mini_grain_status","arguments":{"unexpected":true}}"#,
        &input,
    ).unwrap_err().contains("takes no arguments"));
    assert_eq!(runtime.journal.next_operation_id, before_rejected);
    assert!(runtime.journal.parent_hold.is_none());
    assert!(runtime.journal.foreground_attempt.is_none());
    assert!(!foreground_tombstone_path(
        &runtime.config.state_dir,
        "ffffffffffffffffffffffffffffffff"
    )
    .exists());
    runtime
        .foreground_tool(
            attachment_id,
            br#"{"requestId":"0123456789abcdef0123456789abcdef","name":"mini_grain_status","arguments":{}}"#,
            &input,
        )
        .unwrap();
    let mut delivered = String::new();
    io::BufReader::new(&mut connection)
        .read_line(&mut delivered)
        .unwrap();
    let event: Value = serde_json::from_str(&delivered).unwrap();
    assert_eq!(event["type"], "tool-complete");
    assert_eq!(event["isError"], false);
    assert_eq!(event["requestId"], "0123456789abcdef0123456789abcdef");
    assert!(runtime.journal.parent_hold.is_none());
    assert!(runtime.journal.child.is_none());
    assert!(runtime.journal.hermes_session.is_none());
    assert_eq!(runtime.journal.foreground_history.len(), 1);
    assert!(!runtime.journal.foreground_history[0].reported);
    assert!(runtime.journal.foreground_attempt.is_none());
    assert_eq!(
        runtime
            .foreground_result("0123456789abcdef0123456789abcdef")
            .unwrap()
            .1,
        event["result"]
    );
    let next_operation = runtime.journal.next_operation_id;
    assert!(runtime.foreground_tool(
        attachment_id,
        br#"{"requestId":"0123456789abcdef0123456789abcdef","name":"mini_grain_status","arguments":{}}"#,
        &input,
    ).unwrap_err().contains("inspect it without resubmitting"));
    assert_eq!(runtime.journal.next_operation_id, next_operation);
    assert!(runtime.foreground_tool(
        attachment_id,
        br#"{"requestId":"0123456789abcdef0123456789abcdef","name":"mini_grain_status","arguments":{"changed":true}}"#,
        &input,
    ).unwrap_err().contains("different bytes"));
    for index in 1..=17 {
        let request = format!(
            "{{\"requestId\":\"{index:032x}\",\"name\":\"mini_grain_status\",\"arguments\":{{}}}}"
        );
        runtime
            .foreground_tool(attachment_id, request.as_bytes(), &input)
            .unwrap();
    }
    assert_eq!(runtime.journal.foreground_history.len(), 18);
    assert!(runtime
        .journal
        .foreground_history
        .iter()
        .all(|record| !record.reported));
    // Simulate a crash after signed settlement and the Definite marker but
    // before moving the final result into the bounded history.
    let last = runtime.journal.foreground_history.pop().unwrap();
    assert_eq!(last.request_id, format!("{:032x}", 17));
    runtime.journal.foreground_attempt = Some(last);
    runtime.save().unwrap();
    drop(connection);
    assert!(matches!(
        server.events.recv_timeout(Duration::from_secs(2)).unwrap(),
        control::Event::Detached { hard: false, .. }
    ));
    let ack_id = format!("{:032x}", 16);
    let mut lost_ack = UnixStream::connect(&runtime.config.control_socket).unwrap();
    lost_ack.write_all(b"attach terminal-v1 inspect\n").unwrap();
    let inspect_attachment = match server.events.recv_timeout(Duration::from_secs(2)).unwrap() {
        control::Event::InspectAttached { id } => id,
        other => panic!("unexpected inspect attach: {other:?}"),
    };
    let mut hello = String::new();
    io::BufReader::new(&mut lost_ack)
        .read_line(&mut hello)
        .unwrap();
    lost_ack
        .write_all(format!("tool ack {ack_id}\n").as_bytes())
        .unwrap();
    assert!(
        matches!(server.events.recv_timeout(Duration::from_secs(2)).unwrap(),
        control::Event::Line { id, text } if id == inspect_attachment && text == format!("tool ack {ack_id}"))
    );
    runtime
        .answer_foreground_ack(inspect_attachment, &ack_id)
        .unwrap();
    drop(lost_ack); // ACK frame may have been queued but was never read.
    assert!(matches!(
        server.events.recv_timeout(Duration::from_secs(2)).unwrap(),
        control::Event::Detached { hard: false, .. }
    ));
    let socket = runtime.config.control_socket.clone();
    let retry = std::thread::spawn(move || control::tool_ack_connect(&socket, &ack_id));
    let inspect_attachment = match server.events.recv_timeout(Duration::from_secs(2)).unwrap() {
        control::Event::InspectAttached { id } => id,
        other => panic!("unexpected retry inspect attach: {other:?}"),
    };
    assert!(
        matches!(server.events.recv_timeout(Duration::from_secs(2)).unwrap(),
        control::Event::Line { id, text } if id == inspect_attachment && text.starts_with("tool ack "))
    );
    runtime
        .answer_foreground_ack(inspect_attachment, &format!("{:032x}", 16))
        .unwrap();
    let ack_frame = retry.join().unwrap().unwrap();
    assert_eq!(ack_frame["type"], "tool-acknowledged");
    assert_eq!(ack_frame["requestId"], format!("{:032x}", 16));
    let saved_config = runtime.config.clone();
    let saved_config_path = runtime.config_path.clone();
    runtime.output = None;
    drop(server);
    drop(runtime);
    let mut reopened = Runtime::open(saved_config, saved_config_path).unwrap();
    assert_eq!(
        reopened
            .foreground_result("0123456789abcdef0123456789abcdef")
            .unwrap()
            .1,
        event["result"]
    );
    assert!(reopened.foreground_result(&format!("{:032x}", 17)).is_ok());
    reopened
        .acknowledge_foreground(&format!("{:032x}", 17))
        .unwrap();
    assert!(reopened.journal.foreground_attempt.is_none());
    assert_eq!(reopened.journal.foreground_history.len(), 18);
    reopened
        .acknowledge_foreground("0123456789abcdef0123456789abcdef")
        .unwrap();
    reopened
        .acknowledge_foreground("0123456789abcdef0123456789abcdef")
        .unwrap();
    assert!(reopened.journal.foreground_history[0].reported);
    let old_operation = reopened.journal.foreground_history[0].operation_id;
    reopened.journal.foreground_history.remove(0);
    reopened.save().unwrap();
    let next_operation = reopened.journal.next_operation_id;
    assert!(reopened.foreground_tool(0,
        br#"{"requestId":"0123456789abcdef0123456789abcdef","name":"mini_grain_status","arguments":{}}"#,
        &input).unwrap_err().contains(&format!("operation {old_operation}")));
    assert_eq!(reopened.journal.next_operation_id, next_operation);
    drop(reopened);
    fs::remove_dir_all(root).unwrap();
}

#[test]
fn paused_parent_next_generation_policy_includes_three_fixed_workers() {
    let (mut runtime, root) = fixture(false, false, false);
    runtime.config.dispatch_task = Some(DispatchTask {
        task: "7103".into(),
        subject: "9".into(),
        capability: "91".into(),
        query_capability: "92".into(),
        custody_key: root.join("dispatch.key"),
        parent_capability: "76".into(),
        parent_observe_capability: "77".into(),
        reserve: "5".into(),
        charge: "2".into(),
        socket_path: runtime.config.state_dir.join("dispatch.sock"),
        host_uid: unsafe { libc::geteuid() } + 1,
        operator_socket: None,
        reserve_signer: None,
    });
    runtime.config.provider_task = Some(ProviderTask {
        context_window_tokens: None,
        homelab: None,
        task: "7104".into(),
        subject: "10".into(),
        capability: "101".into(),
        query_capability: "102".into(),
        custody_key: root.join("provider.key"),
        parent_capability: "78".into(),
        parent_observe_capability: "79".into(),
        reserve: "5".into(),
        max_input_tokens: 8,
        max_output_tokens: 8,
        model: "fixture".into(),
        providers: root.join("providers.json"),
        provider: None,
        on_behalf_of: None,
        credential_broker: root.join("keys-client.json"),
        gateway_bind: "127.0.0.1:0".into(),
        max_request_bytes: 1024,
        max_response_bytes: 1024,
        timeout_seconds: 30,
        max_iterations: None,
        local_fixture_host_network: true,
    });
    let workers = runtime.managed_worker_subjects().unwrap();
    assert_eq!(workers, ["8", "9", "10"]);
    let next_generation = managed_worker_policy_source("7", &workers, "2");
    assert_eq!(
        next_generation,
        json!({"owner":"7",
        "workerSubjects":["8","9","10"],"workerGeneration":"2"})
    );
    assert_ne!(
        next_generation,
        managed_worker_policy_source("7", &workers, "1")
    );
    runtime.config.provider_task.as_mut().unwrap().subject = "9".into();
    assert!(runtime.managed_worker_subjects().is_err());
    runtime.config.provider_task.as_mut().unwrap().subject = "10".into();
    let state = runtime.config.state_dir.clone();
    fs::write(
        state.join("policy-view.json"),
        serde_json::to_vec(&json!({
            "policyId":"7101",
            "domain":"1","semantics":"2","version":"3","address":"4",
            "canonical":"0a0b0c",
            "predicate":managed_worker_policy_source("7", &workers, "1")
        }))
        .unwrap(),
    )
    .unwrap();
    let original = fs::read_to_string(&runtime.config.mini).unwrap();
    let author = r#"if [ "$1" = author ]; then
  shift
  input=
  output=
  while [ "$#" -gt 0 ]; do
    case "$1" in
      --input) input=$2; shift 2 ;;
      --output) output=$2; shift 2 ;;
      *) shift ;;
    esac
  done
  jq -cS . "$input" > "$output"
  exit 0
fi
"#;
    let policy_query = r#"if [ "$command" = query ] && grep -q '"view": "policy"' "$intent"; then
  cp "$state/policy-view.json" "$dir/view.json"
  printf '%s\n' '{"authorityRoot":"200","signing":[{}],"worldRoot":"300"}' > "$dir/challenge.json"
  exit 0
fi
"#;
    let patched = original
        .replacen("command=$1", &format!("{author}command=$1"), 1)
        .replacen(
            "if [ \"$command\" = query ]; then",
            &format!("{policy_query}if [ \"$command\" = query ]; then"),
            1,
        )
        .replace("\"task\":\"7102\"", "\"task\":\"7101\"");
    assert_ne!(original, patched);
    fs::write(&runtime.config.mini, patched).unwrap();
    runtime.renew_worker_policy(true).unwrap();
    let source_path = fs::read_dir(&state)
        .unwrap()
        .map(|entry| entry.unwrap().path())
        .find(|path| {
            path.file_name()
                .unwrap()
                .to_string_lossy()
                .starts_with("policy-source-")
        })
        .unwrap();
    let installed: Value = serde_json::from_slice(&fs::read(source_path).unwrap()).unwrap();
    assert_eq!(installed["workerSubjects"], json!(["8", "9", "10"]));
    assert_eq!(installed["workerGeneration"], "2");
    // The re-pin carries the signed view's canonical source, so the Host
    // preserves its non-predicate metadata (30746612).
    assert_eq!(installed["currentSourceHex"], "0a0b0c");
    drop(runtime);
    fs::remove_dir_all(root).unwrap();
}

fn publication(root: &str) -> Value {
    json!({"publications":[{"kind":"object","target":"7003",
        "expectedTargetRoot":root,"payload":{"type":"scalar","actions":[]}}]})
}

#[test]
fn retained_native_prepare_refusal_releases_tool_hold_without_publication() {
    let (mut runtime, root) = fixture(false, false, true);
    let refused = runtime
        .tool_call("mini_publish", &publication("700"))
        .unwrap_err();
    assert!(refused.contains("tool settle refused by Mini:"));
    assert!(refused.contains("release and disconnect confirmed"));
    assert!(runtime.journal.tool_pending.is_none());
    assert!(runtime.journal.tool_hold.is_none());
    assert!(runtime.journal.publication_receipts.is_empty());
    let attempts: Vec<PathBuf> = fs::read_dir(&runtime.config.state_dir)
        .unwrap()
        .filter_map(|entry| {
            let path = entry.ok()?.path();
            path.join("pre-submit-refusal.frame")
                .is_file()
                .then_some(path)
        })
        .collect();
    assert_eq!(attempts.len(), 1);
    assert!(!attempts[0].join("call.bin").exists());
    let persisted: Value =
        serde_json::from_slice(&fs::read(runtime.config.state_dir.join("journal.json")).unwrap())
            .unwrap();
    assert!(persisted["toolPending"].is_null());
    assert!(persisted["toolHold"].is_null());
    assert!(persisted["publicationReceipts"]
        .as_array()
        .unwrap()
        .is_empty());
    fs::remove_dir_all(root).unwrap();
}

#[test]
fn restart_recognizes_pre_submit_refusal_but_keeps_confirmed_hold() {
    let (mut runtime, root) = fixture(false, false, true);
    let attempt = runtime.config.state_dir.join("attempt-0000000000000099");
    let source = root.join("stale-publication.json");
    fs::write(&source, b"{\"type\": \"settle\", \"target\": \"7003\"}").unwrap();
    let status = Command::new(&runtime.config.mini)
        .args(["submit", "--host"])
        .arg(&runtime.config.host)
        .arg("--config")
        .arg(&runtime.config.host_config)
        .arg("--socket")
        .arg(runtime.config.host_socket.as_ref().unwrap())
        .arg("--intent")
        .arg(&source)
        .arg("--dir")
        .arg(&attempt)
        .status()
        .unwrap();
    assert!(!status.success());
    assert!(!attempt.join("call.bin").exists());
    runtime.journal.tool_pending = Some(Pending {
        operation_id: 99,
        operation: "tool settle".into(),
        attempt: attempt.clone(),
        uncertain: true,
        publication: None,
    });
    runtime.journal.tool_hold = Some(HeldCharge {
        reserve: "2".into(),
        charge: "1".into(),
        before_generation: "1".into(),
        before_target_root: "100".into(),
        reserve_attempt: Some(root.join("confirmed-reserve")),
        reserve_confirmed: true,
        reserve_refused: false,
        reserve_boundary: Some("300".into()),
        reserve_call_sha256: None,
        reserve_source_sha256: None,
        reserve_outcome_path: None,
        reserve_outcome_sha256: None,
        reserve_anchor: None,
    });
    runtime.save().unwrap();
    runtime.retry_pending_slot(AuthoritySlot::Tool).unwrap();
    assert!(runtime.journal.tool_pending.is_none());
    assert!(runtime
        .journal
        .tool_hold
        .as_ref()
        .is_some_and(|hold| hold.reserve_confirmed));
    assert!(runtime
        .journal
        .reconciliation_log
        .iter()
        .any(
            |entry| entry["action"] == "recognize-native-pre-submit-refusal"
                && entry["heldAllowanceReleased"] == false
        ));
    let persisted: Value =
        serde_json::from_slice(&fs::read(runtime.config.state_dir.join("journal.json")).unwrap())
            .unwrap();
    assert!(persisted["toolPending"].is_null());
    assert!(persisted["toolHold"].is_object());
    fs::remove_dir_all(root).unwrap();
}

#[test]
fn definitive_refusal_releases_hold_for_same_prompt_read_and_retry() {
    let (mut runtime, root) = fixture(false, false, false);
    let refused = runtime
        .tool_call("mini_publish", &publication("700"))
        .unwrap_err();
    assert!(refused.contains("stale content root"));
    assert!(refused.contains("release and disconnect confirmed"));
    assert!(runtime.journal.tool_hold.is_none());
    assert!(runtime.journal.tool_pending.is_none());
    let persisted: Value =
        serde_json::from_slice(&fs::read(runtime.config.state_dir.join("journal.json")).unwrap())
            .unwrap();
    assert!(persisted["toolHold"].is_null());
    assert!(persisted["toolPending"].is_null());
    let read = runtime
        .tool_call("mini_read_resource", &json!({"name":"publication"}))
        .unwrap();
    assert_eq!(read["view"]["cell"]["root"], "701");
    runtime
        .tool_call(
            "mini_publish",
            &publication(read["view"]["cell"]["root"].as_str().unwrap()),
        )
        .unwrap();
    assert_eq!(runtime.journal.publication_receipts.len(), 1);
    assert!(runtime.journal.tool_hold.is_none());
    fs::remove_dir_all(root).unwrap();
}

#[test]
fn uncertain_zero_charge_release_retains_hold_and_blocks_same_prompt_tools() {
    let (mut runtime, root) = fixture(true, false, false);
    let refused = runtime
        .tool_call("mini_publish", &publication("700"))
        .unwrap_err();
    assert!(refused.contains("zero-charge tool release unresolved"));
    assert!(refused.contains("reconciliation"));
    assert!(runtime.journal.tool_hold.is_some());
    assert!(runtime
        .journal
        .tool_pending
        .as_ref()
        .is_some_and(|p| p.uncertain));
    let persisted: Value =
        serde_json::from_slice(&fs::read(runtime.config.state_dir.join("journal.json")).unwrap())
            .unwrap();
    assert!(persisted["toolHold"].is_object());
    assert_eq!(persisted["toolPending"]["uncertain"], true);
    let blocked = runtime
        .tool_call("mini_read_resource", &json!({"name":"publication"}))
        .unwrap_err();
    assert!(blocked.contains("owner reconciliation"));
    assert!(runtime
        .tool_call("mini_publish", &publication("701"))
        .is_err());
    fs::remove_dir_all(root).unwrap();
}

#[test]
fn uncertain_disconnect_after_release_retains_exact_attempt_and_blocks_tools() {
    let (mut runtime, root) = fixture(false, true, false);
    let refused = runtime
        .tool_call("mini_publish", &publication("700"))
        .unwrap_err();
    assert!(refused.contains("zero-charge tool release confirmed"));
    assert!(refused.contains("disconnect cleanup did not confirm"));
    assert!(runtime.journal.tool_hold.is_none());
    assert!(runtime
        .journal
        .tool_pending
        .as_ref()
        .is_some_and(|p| p.uncertain && p.operation == "tool disconnect"));
    let persisted: Value =
        serde_json::from_slice(&fs::read(runtime.config.state_dir.join("journal.json")).unwrap())
            .unwrap();
    assert!(persisted["toolHold"].is_null());
    assert_eq!(persisted["toolPending"]["operation"], "tool disconnect");
    assert!(runtime
        .tool_call("mini_read_resource", &json!({"name":"publication"}))
        .unwrap_err()
        .contains("owner reconciliation"));
    fs::remove_dir_all(root).unwrap();
}
