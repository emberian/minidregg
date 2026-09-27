use super::*;

// A controlled native-client stub supplies view and submit response files.
// These test the real tool_call, transition, journal, and read paths, not Mini admission.
pub(super) fn fixture(
    fail_release: bool,
    fail_disconnect: bool,
    pre_submit: bool,
) -> (Runtime, PathBuf) {
    let root = std::env::temp_dir().join(format!(
        "grain-publication-refusal-{}-{}",
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
      printf '%s\n' '{"type":"resource","page":{"root":"701","entries":[]}}' > "$dir/view.json" ;;
    *)
      status=$(cat "$state/status")
      printf '{"page":{"root":"100","grain":{"task":"7102","generation":"1","status":"%s","remaining":"10","reserved":"3"}}}\n' "$status" > "$dir/view.json"
      printf '%s\n' '{"signing":[{"authorityRoot":"200"}],"imageBoundary":"300"}' > "$dir/challenge.json" ;;
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
printf '%s\n' '{"type":"confirmed","confirmation":"installed","imageBoundary":"300","transactionId":"11","eventId":"12","acceptedCount":"13"}' > "$dir/outcome.json"
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
        tool_task: Some(ToolTask {
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
            allowed_birth_families: vec![],
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
    assert_eq!(read["view"]["page"]["root"], "701");
    runtime
        .tool_call(
            "mini_publish",
            &publication(read["view"]["page"]["root"].as_str().unwrap()),
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
