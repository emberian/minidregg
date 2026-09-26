use super::*;

// A controlled native-client stub supplies view and submit response files.
// These test the real tool_call, transition, journal, and read paths, not Mini admission.
fn fixture(fail_release: bool, fail_disconnect: bool) -> (Runtime, PathBuf) {
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
    let mini = root.join("controlled-mini");
    let script = r#"#!/bin/sh
set -eu
state='__STATE__'
command=$1
shift
dir=
intent=
while [ "$#" -gt 0 ]; do
  case "$1" in
    --dir) dir=$2; shift 2 ;;
    --intent) intent=$2; shift 2 ;;
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
    let config = Config {
        mini,
        host: root.join("host"),
        host_config: root.join("host-config.json"),
        host_socket: None,
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
fn definitive_refusal_releases_hold_for_same_prompt_read_and_retry() {
    let (mut runtime, root) = fixture(false, false);
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
    let (mut runtime, root) = fixture(true, false);
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
    let (mut runtime, root) = fixture(false, true);
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
