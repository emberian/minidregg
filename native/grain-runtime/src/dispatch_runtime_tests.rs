use super::*;

#[cfg(target_os = "linux")]
#[test]
fn separate_dispatch_reserve_is_one_shot_and_cannot_abort_after_send() {
    let root = std::env::temp_dir().join(format!(
        "mini-dispatch-runtime-{}-{}",
        std::process::id(),
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos()
    ));
    let state = root.join("state");
    let socket_dir = root.join("socket");
    fs::create_dir_all(&state).unwrap();
    fs::set_permissions(&root, fs::Permissions::from_mode(0o755)).unwrap();
    fs::create_dir(&socket_dir).unwrap();
    fs::set_permissions(&socket_dir, fs::Permissions::from_mode(0o711)).unwrap();
    fs::write(state.join("dispatch-status"), b"0").unwrap();
    let mini = root.join("mock-mini");
    let script = r#"#!/bin/sh
set -eu
state='__STATE__'
command=$1
shift
dir=
intent=
attempt=
while [ "$#" -gt 0 ]; do
  case "$1" in
    --dir) dir=$2; shift 2 ;;
    --intent) intent=$2; shift 2 ;;
    --attempt) attempt=$2; shift 2 ;;
    *) shift ;;
  esac
done
if [ "$command" = retry ]; then
  index=1
  while :; do
    name=$(printf '%s/retry-%04d.json' "$attempt" "$index")
    [ -e "$name" ] || break
    index=$((index + 1))
  done
  cp "$attempt/outcome.json" "$name"
  exit 0
fi
mkdir -p "$dir"
if [ "$command" = query ]; then
  if grep -q '"target": "7103"' "$intent"; then
    [ ! -f "$state/dispatch-delay" ] || sleep 0.2
    task=7103
    status=$(cat "$state/dispatch-status")
    generation=1
    reserved=0
    [ "$status" != 3 ] && [ "$status" != 5 ] || reserved=5
    remaining=10
    [ "$status" != 3 ] && [ "$status" != 5 ] || remaining=5
    [ "$status" != 5 ] || generation=2
  else
    task=7101
    status=3
    generation=1
    reserved=3
    remaining=7
  fi
  printf '{"page":{"root":"100","grain":{"task":"%s","generation":"%s","status":"%s","remaining":"%s","reserved":"%s"}}}\n' "$task" "$generation" "$status" "$remaining" "$reserved" > "$dir/view.json"
  printf '%s\n' '{"signing":[{"authorityRoot":"200"}],"imageBoundary":"300"}' > "$dir/challenge.json"
  exit 0
fi
[ "$command" = submit ] || exit 40
printf call > "$dir/call.bin"
printf outcome > "$dir/outcome.bin"
if grep -q '"type": "attach"' "$intent"; then
  printf 1 > "$state/dispatch-status"
elif grep -q '"type": "reserve"' "$intent"; then
  printf 3 > "$state/dispatch-status"
elif grep -q '"type": "settle"' "$intent"; then
  printf 1 > "$state/dispatch-status"
elif grep -q '"type": "disconnect"' "$intent"; then
  before=$(cat "$state/dispatch-status")
  [ "$before" = 3 ] && printf 5 > "$state/dispatch-status" || printf 0 > "$state/dispatch-status"
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
        host_socket: Some(root.join("mini.sock")),
        control_socket: state.join("control.sock"),
        custody_key: root.join("parent.key"),
        state_dir: state.clone(),
        cwd: root.clone(),
        task: "7101".into(),
        subject: "7".into(),
        capability: "71".into(),
        query_capability: "74".into(),
        policy_control_capability: Some("72".into()),
        tool_task: None,
        dispatch_task: Some(DispatchTask {
            task: "7103".into(),
            subject: "9".into(),
            capability: "91".into(),
            query_capability: "92".into(),
            custody_key: root.join("dispatch.key"),
            parent_capability: "73".into(),
            parent_observe_capability: "75".into(),
            reserve: "5".into(),
            charge: "2".into(),
            socket_path: socket_dir.join("dispatch.sock"),
            host_uid: unsafe { libc::geteuid() } + 1,
        }),
        provider_task: None,
        commands: vec![],
    };
    let mut runtime = Runtime::open(config, root.join("config.json")).unwrap();
    runtime.journal.connection = Connection::Hard;
    runtime.journal.child = Some(ChildRecord {
        operation_id: 1,
        pid: 1,
        program: root.join("hermes"),
        pgid: 1,
        unit: None,
        launch_gate_protocol: None,
    });
    runtime.journal.prompt_witness = Some(json!({"task":"7101"}));
    runtime.prompt_active = true;
    let request = b"canonical Mini HTTP request";
    let reserved = runtime.dispatch_reserve(request, "1234", "50").unwrap();
    assert_eq!(reserved["type"], "dispatch-reserved-v1");
    assert_eq!(reserved["dispatchTask"], "7103");
    let signed_reserve_id = reserved["reserveOperationId"].as_str().unwrap();
    let signed_source: Value = serde_json::from_slice(
        &fs::read(state.join(format!(
            "source-{:016}.json",
            signed_reserve_id.parse::<u64>().unwrap()
        )))
        .unwrap(),
    )
    .unwrap();
    assert_eq!(
        signed_source["grain"]["context"]["operationId"],
        signed_reserve_id
    );
    assert!(
        runtime
            .journal
            .dispatch_hold
            .as_ref()
            .unwrap()
            .reserve_confirmed
    );
    assert!(runtime.dispatch_reserve(request, "1234", "50").is_err());
    let id = reserved["attemptId"]
        .as_str()
        .unwrap()
        .parse::<u64>()
        .unwrap();
    let request_sha = reserved["requestSha256"].as_str().unwrap();
    let permit_sha = "a".repeat(64);
    runtime
        .dispatch_mark_send(id, request_sha, "777", "778", &permit_sha)
        .unwrap();
    assert!(runtime
        .dispatch_mark_send(id, request_sha, "777", "778", &permit_sha)
        .is_err());
    assert!(runtime.dispatch_abort_no_send(id).is_err());
    let response_sha = "b".repeat(64);
    runtime.dispatch_settle_definite(id, &response_sha).unwrap();
    assert!(runtime.journal.dispatch_attempt.is_none());
    assert!(runtime.journal.dispatch_hold.is_none());
    assert_eq!(
        fs::read_to_string(state.join("dispatch-status")).unwrap(),
        "1"
    );

    // Reproduce a crash after the confirmed zero-charge Mini settlement has
    // durably removed the hold, but before the wrapper clears its attempt.
    let second = runtime.dispatch_reserve(request, "1234", "51").unwrap();
    let second_id = second["attemptId"]
        .as_str()
        .unwrap()
        .parse::<u64>()
        .unwrap();
    runtime
        .journal
        .dispatch_attempt
        .as_mut()
        .unwrap()
        .no_send_release_started = true;
    runtime.save().unwrap();
    runtime
        .transition_as(
            &runtime.dispatch().unwrap(),
            json!({"type":"settle","charge":"0"}),
            "dispatch release",
            "definite refusal before app send",
            vec![],
        )
        .unwrap();
    assert!(runtime.journal.dispatch_hold.is_none());
    assert_eq!(
        runtime.journal.dispatch_attempt.as_ref().unwrap().id,
        second_id
    );
    assert!(runtime
        .dispatch_mark_send(
            second_id,
            second["requestSha256"].as_str().unwrap(),
            "777",
            "778",
            &permit_sha
        )
        .is_err());
    runtime.journal.child = None;
    runtime.save().unwrap();
    let settlement = runtime
        .journal
        .dispatch_attempt
        .as_ref()
        .unwrap()
        .settlement
        .as_ref()
        .unwrap()
        .clone();
    let outcome_bytes = settlement.attempt.join("outcome.bin");
    fs::write(&outcome_bytes, b"tampered").unwrap();
    assert!(runtime.recover().is_err());
    assert!(runtime.journal.dispatch_attempt.is_some());
    fs::write(&outcome_bytes, b"outcome").unwrap();
    runtime.recover().unwrap();
    assert!(runtime.journal.dispatch_attempt.is_none());
    runtime.journal.child = Some(ChildRecord {
        operation_id: 2,
        pid: 1,
        program: root.join("hermes"),
        pgid: 1,
        unit: None,
        launch_gate_protocol: None,
    });

    // A crash after confirmed reserve/hold but before copying its operation
    // and postroot into the wrapper, also after starting a definite no-send
    // release, must remain audit-only and settle at zero after restart.
    runtime.dispatch_reserve(request, "1234", "53").unwrap();
    {
        let incomplete = runtime.journal.dispatch_attempt.as_mut().unwrap();
        incomplete.reserve_operation_id = None;
        incomplete.dispatch_generation = None;
        incomplete.dispatch_post_root = None;
        incomplete.no_send_release_started = true;
    }
    runtime.journal.child = None;
    runtime.journal.connection = Connection::Fenced;
    runtime.save().unwrap();
    runtime.recover().unwrap();
    assert!(runtime.journal.dispatch_hold.is_some());
    let mut prehold_crash = runtime.journal.dispatch_attempt.as_ref().unwrap().clone();
    assert!(runtime.reconcile_dispatch_audited(true).is_err());
    runtime.reconcile_dispatch_audited(false).unwrap();
    assert!(runtime.journal.dispatch_attempt.is_none());
    assert!(runtime.journal.dispatch_hold.is_none());

    // The separate pre-submit stage has a durable attempt and unsubmitted
    // hold, but no native reserve operation. Recovery needs signed idle state
    // before removing either marker.
    prehold_crash.no_send_release_started = false;
    prehold_crash.audited_charge = None;
    prehold_crash.settlement = None;
    runtime.journal.dispatch_attempt = Some(prehold_crash);
    runtime
        .mark_hold_as(
            AuthoritySlot::Dispatch,
            &runtime.dispatch().unwrap(),
            "5",
            "2",
        )
        .unwrap();
    runtime.journal.child = None;
    runtime.save().unwrap();
    runtime.recover().unwrap();
    assert!(runtime.journal.dispatch_attempt.is_none());
    assert!(runtime.journal.dispatch_hold.is_none());
    runtime.journal.connection = Connection::Hard;
    runtime.journal.prompt_witness = Some(json!({"task":"7101"}));
    runtime.journal.child = Some(ChildRecord {
        operation_id: 3,
        pid: 1,
        program: root.join("hermes"),
        pgid: 1,
        unit: None,
        launch_gate_protocol: None,
    });

    // A hard EOF arriving while native state is queried must prevent a late
    // mark-send ACK. This held request remains available only for audit.
    let third = runtime.dispatch_reserve(request, "1234", "52").unwrap();
    let third_id = third["attemptId"].as_str().unwrap().parse::<u64>().unwrap();
    let third_sha = third["requestSha256"].as_str().unwrap().to_owned();
    fs::write(state.join("dispatch-delay"), b"1").unwrap();
    let cancelled = runtime.cancelled.clone();
    let canceller = std::thread::spawn(move || {
        std::thread::sleep(std::time::Duration::from_millis(40));
        cancelled.store(true, Ordering::SeqCst);
    });
    assert!(runtime
        .dispatch_mark_send(third_id, &third_sha, "779", "780", &permit_sha)
        .is_err());
    canceller.join().unwrap();
    assert!(
        !runtime
            .journal
            .dispatch_attempt
            .as_ref()
            .unwrap()
            .send_started
    );
    assert!(runtime.journal.dispatch_hold.is_some());
    runtime.journal.child = None;
    runtime.journal.connection = Connection::Fenced;
    runtime.save().unwrap();
    runtime.recover().unwrap();
    assert_eq!(runtime.journal.connection, Connection::Fenced);
    assert_eq!(
        fs::read_to_string(state.join("dispatch-status")).unwrap(),
        "5"
    );
    assert!(runtime.journal.dispatch_hold.is_some());
    runtime.reconcile_dispatch_audited(false).unwrap();
    assert!(runtime.journal.dispatch_hold.is_none());
    assert!(runtime.journal.dispatch_attempt.is_none());
    assert_eq!(
        fs::read_to_string(state.join("dispatch-status")).unwrap(),
        "1"
    );
    assert!(runtime
        .journal
        .unresolved_external
        .iter()
        .any(|note| note.contains("external effects require explicit acknowledgement")));
    drop(runtime);
    fs::remove_dir_all(root).unwrap();
}
