#[cfg(target_os = "linux")]
use super::*;

#[cfg(target_os = "linux")]
#[test]
fn agent_route_participant_is_parent_subject_not_purse_payer() {
    let root = std::env::temp_dir().join(format!(
        "mini-agent-subject-split-{}-{}",
        std::process::id(),
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos()
    ));
    let state = root.join("state");
    fs::create_dir_all(&state).unwrap();
    fs::set_permissions(&root, fs::Permissions::from_mode(0o711)).unwrap();
    fs::set_permissions(&state, fs::Permissions::from_mode(0o700)).unwrap();
    let operator_socket = state.join("operator.sock");
    let _listener = std::os::unix::net::UnixListener::bind(&operator_socket).unwrap();
    fs::set_permissions(&operator_socket, fs::Permissions::from_mode(0o600)).unwrap();
    let host = root.join("host");
    fs::write(&host, b"source-pinned host fixture").unwrap();
    let host_sha = sha256_file(&host).unwrap();
    let host_uid = unsafe { libc::geteuid() } + 1;
    let route = json!({
        "name":"gitweb-app","socketPath":root.join("agent.sock"),
        "hostUid":host_uid,"hostUnit":"mini-spk-a8401-g1.service",
        "appResource":"8401","appGeneration":"1",
        "sessionResource":"8420","sessionGeneration":"1",
        "ticketResource":"8520","participantSubject":"10",
        "parentTask":"7920","parentGeneration":"1",
        "purseResource":"7940","dispatchGeneration":"1",
        "signedApiPath":"/repo.git/",
        "dispatchSelectors":{"issueIndex":"9","packageManifest":"8402",
            "snapshotManifest":"8403","sessionObserve":"101",
            "manifestObserve":"102","enrollmentObserve":"103"}
    });
    let mut value = json!({
        "mini":root.join("mini"),"host":host,
        "hostConfig":root.join("host.json"),"hostSocket":root.join("public.sock"),
        "controlSocket":state.join("control.sock"),"custodyKey":root.join("parent.key"),
        "stateDir":state,"cwd":root.clone(),"task":"7920","subject":"10",
        "capability":"71","queryCapability":"72","policyControlCapability":"73",
        "dispatchTask":{"task":"7940","subject":"12","capability":"81",
            "queryCapability":"82","custodyKey":root.join("purse.key"),
            "parentCapability":"83","parentObserveCapability":"84",
            "reserve":"5","charge":"0","socketPath":root.join("dispatch.sock"),
            "hostUid":host_uid,"operatorSocket":operator_socket,
            "reserveSigner":{"role":"1","index":"0","publicKey":"a".repeat(64),
                "keyId":"1200","keyEpoch":"1"}},
        "toolTask":{"task":"7930","subject":"11","capability":"91",
            "queryCapability":"92","custodyKey":root.join("tool.key"),
            "parentCapability":"93","parentObserveCapability":"94",
            "reserve":"3","charge":"1","allowedPublications":[],
            "allowedApplicationApiRoutes":[route],"agentApiHostSha256":host_sha},
        "commands":[]
    });
    let config: Config = serde_json::from_value(value.clone()).unwrap();
    validate(&config).unwrap();
    // The foreground path must admit the same exact reverse v2 custody
    // handshake while keeping the parent and purse subjects distinct. This
    // checks the no-Hermes-child controller join, before any native submit.
    let mut runtime = Runtime::open(config.clone(), root.join("config.json")).unwrap();
    let forward = json!({"operation_id":"50","method":"POST","path":"git-receive-pack",
        "query":"service=git-receive-pack","headers":[],"body_hex":"abcd"});
    let request_path = state.join("forward-50.json");
    fs::write(&request_path, serde_json::to_vec(&forward).unwrap()).unwrap();
    runtime.journal.connection = Connection::Soft;
    runtime.foreground_operation = Some(40);
    runtime.journal.application_api_attempt = Some(ApplicationApiAttempt {
        operation_id: 50,
        route_name: "gitweb-app".into(),
        request_sha256: sha256_file(&request_path).unwrap(),
        request_path,
        phase: ApplicationApiPhase::DispatchStarted,
        binding_sha256: None,
        host_invocation: None,
        reply_path: None,
        reply_sha256: None,
        reported: false,
    });
    let selected = &config
        .tool_task
        .as_ref()
        .unwrap()
        .allowed_application_api_routes[0];
    let dispatch = config.dispatch_task.as_ref().unwrap();
    let fixed = json!({
        "base":{"issueIndex":selected.dispatch_selectors.issue_index,
            "ticketResource":selected.ticket_resource,
            "packageManifest":selected.dispatch_selectors.package_manifest,
            "snapshotManifest":selected.dispatch_selectors.snapshot_manifest,
            "sessionObserveCapability":selected.dispatch_selectors.session_observe,
            "manifestObserveCapability":selected.dispatch_selectors.manifest_observe,
            "enrollmentObserveCapability":selected.dispatch_selectors.enrollment_observe,
            "http":application_api_tools::routed_reserve_http(&forward, &selected.signed_api_path).unwrap()},
        "parentTask":config.task,"parentCapability":dispatch.parent_capability,
        "parentObserve":dispatch.parent_observe_capability,
        "purseTask":dispatch.task,"purseCapability":dispatch.capability,
        "purseObserve":dispatch.query_capability,"payerSubject":dispatch.subject,
        "reserveAmount":dispatch.reserve,"maximumCharge":dispatch.charge,
        "reserveOperationId":"0"
    });
    runtime
        .verified_reverse_fixed_request("gitweb-app", "50", &fixed)
        .unwrap();
    let mut changed = fixed.clone();
    changed["base"]["http"]["pathHex"] = json!("00");
    assert!(runtime
        .verified_reverse_fixed_request("gitweb-app", "50", &changed)
        .is_err());
    runtime.foreground_operation = None;
    assert!(runtime
        .verified_reverse_fixed_request("gitweb-app", "50", &fixed)
        .is_err());
    value["toolTask"]["allowedApplicationApiRoutes"][0]["participantSubject"] = json!("12");
    let wrong_participant: Config = serde_json::from_value(value).unwrap();
    assert!(validate(&wrong_participant).is_err());
    fs::remove_dir_all(root).unwrap();
}

#[cfg(target_os = "linux")]
#[test]
fn confirmed_v2_reserve_recovers_missing_signed_purse_coordinate_after_crash() {
    let root = std::env::temp_dir().join(format!(
        "mini-v2-reserve-crash-{}-{}",
        std::process::id(),
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos()
    ));
    let state = root.join("state");
    fs::create_dir_all(&state).unwrap();
    fs::set_permissions(&root, fs::Permissions::from_mode(0o711)).unwrap();
    let mini = root.join("mock-mini");
    let script = r#"#!/bin/sh
set -eu
state='__STATE__'
case "$1" in
  agent-reserve-lookup)
    printf looked-up > "$state/lookup-called"
    ;;
  query)
    shift
    dir=
    while [ "$#" -gt 0 ]; do
      case "$1" in
        --dir) dir=$2; shift 2 ;;
        *) shift ;;
      esac
    done
    mkdir -p "$dir"
    printf '%s\n' '{"cell":{"root":"200","grain":{"task":"7103","generation":"2","status":"3","remaining":"5","reserved":"5"}}}' > "$dir/view.json"
    printf '%s\n' '{"authorityRoot":"300","signing":[{}],"worldRoot":"400"}' > "$dir/challenge.json"
    ;;
  *) exit 40 ;;
esac
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
        foreground_tool: None,
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
            socket_path: root.join("dispatch.sock"),
            host_uid: unsafe { libc::geteuid() } + 1,
            operator_socket: None,
            reserve_signer: None,
        }),
        provider_task: None,
        commands: vec![],
    };
    let directory = state.join("agent-reserve-0000000000000007");
    fs::create_dir(&directory).unwrap();
    let source = state.join("dispatch-reserve-source-0000000000000008.json");
    let request_path = state.join("dispatch-0000000000000007.canonical-request");
    fs::write(&source, b"source").unwrap();
    fs::write(&request_path, b"http").unwrap();
    fs::write(directory.join("request.bin"), b"request").unwrap();
    fs::write(directory.join("plan.bin"), b"plan").unwrap();
    fs::write(directory.join("call.bin"), b"call").unwrap();
    fs::write(directory.join("submit-marker.json"), b"{}").unwrap();
    fs::write(directory.join("submit.outcome.bin"), b"outcome").unwrap();
    fs::write(
        directory.join("submit.outcome.json"),
        br#"{"type":"confirmed","confirmation":"installed","transactionId":"11","eventId":"12","acceptedCount":"13","worldRoot":"300"}"#,
    )
    .unwrap();
    fs::write(
        directory.join("receipt.json"),
        br#"{"transactionId":"11","eventId":"12","acceptedCount":"13","worldRoot":"300","reserveIndex":"12"}"#,
    )
    .unwrap();
    fs::write(
        directory.join("plan-inspected.json"),
        br#"{"context":{"reserveOperationId":"8","purseTask":"7103","reserveAmount":"5","requestDigest":"1234","parentGeneration":"1","purseGeneration":"1"}}"#,
    )
    .unwrap();
    let anchor = ReserveAnchor {
        transaction_id: "11".into(),
        event_id: "12".into(),
        accepted_count: "13".into(),
        world_root: "300".into(),
    };
    let mut runtime = Runtime::open(config, root.join("config.json")).unwrap();
    runtime.journal.dispatch_attempt = Some(DispatchAttempt {
        id: 7,
        http_operation_id: "50".into(),
        parent_generation: "1".into(),
        parent_root: "100".into(),
        request_path: request_path.clone(),
        request_bytes: 4,
        request_sha256: sha256_file(&request_path).unwrap(),
        source_request_digest: "1234".into(),
        reserve_operation_id: Some(8),
        reserve_v2_dir: Some(directory.clone()),
        reserve_v2_request_sha256: Some(sha256_file(&directory.join("request.bin")).unwrap()),
        reserve_v2_plan_sha256: Some(sha256_file(&directory.join("plan.bin")).unwrap()),
        reserve_v2_source_sha256: Some(sha256_file(&source).unwrap()),
        lifetime: None,
        dispatch_generation: None,
        dispatch_post_root: None,
        no_send_release_started: false,
        audited_charge: None,
        settlement: None,
        send_started: false,
        committed_dispatch_transaction: None,
        committed_dispatch_event: None,
        committed_permit_sha256: None,
        response_sha256: None,
    });
    runtime.journal.dispatch_hold = Some(HeldCharge {
        reserve: "5".into(),
        charge: "2".into(),
        before_generation: "1".into(),
        before_target_root: "100".into(),
        reserve_attempt: Some(directory.clone()),
        reserve_confirmed: true,
        reserve_refused: false,
        reserve_boundary: Some("300".into()),
        reserve_call_sha256: Some(sha256_file(&directory.join("call.bin")).unwrap()),
        reserve_source_sha256: Some(sha256_file(&source).unwrap()),
        reserve_outcome_path: Some(directory.join("submit.outcome.bin")),
        reserve_outcome_sha256: Some(sha256_file(&directory.join("submit.outcome.bin")).unwrap()),
        reserve_anchor: Some(anchor.clone()),
    });
    runtime.save().unwrap();
    // This is exactly the first post-op2 save: confirmed hold, no copied
    // generation/post-root yet. Recovery must perform lookup, not return.
    runtime.recover_v2_dispatch_reserve().unwrap();
    assert!(state.join("lookup-called").exists());
    let repaired = runtime.journal.dispatch_attempt.as_ref().unwrap();
    assert_eq!(repaired.dispatch_generation.as_deref(), Some("2"));
    assert_eq!(repaired.dispatch_post_root.as_deref(), Some("200"));
    assert_eq!(
        runtime
            .journal
            .dispatch_hold
            .as_ref()
            .unwrap()
            .reserve_anchor,
        Some(anchor)
    );
    fs::remove_dir_all(root).unwrap();
}

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
  printf '{"cell":{"root":"100","grain":{"task":"%s","generation":"%s","status":"%s","remaining":"%s","reserved":"%s"}}}\n' "$task" "$generation" "$status" "$remaining" "$reserved" > "$dir/view.json"
  printf '%s\n' '{"authorityRoot":"200","signing":[{}],"worldRoot":"300"}' > "$dir/challenge.json"
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
printf '%s\n' '{"type":"confirmed","confirmation":"installed","worldRoot":"300","transactionId":"11","eventId":"12","acceptedCount":"13"}' > "$dir/outcome.json"
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
        foreground_tool: None,
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
            operator_socket: None,
            reserve_signer: None,
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
