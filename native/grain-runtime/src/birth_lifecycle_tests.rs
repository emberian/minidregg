use super::*;

// This Mini stub exercises controller crash recovery and the signed-zero
// transition path. Native admission is separately qualified by the Host run.
fn fixture() -> (Runtime, PathBuf) {
    let (runtime, root) = publication_refusal_tests::fixture(false, false, false);
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
  status=$(cat "$state/status")
  reserved=$(cat "$state/reserved")
  printf '{"cell":{"root":"100","grain":{"task":"7102","generation":"1","status":"%s","remaining":"10","reserved":"%s"}}}\n' "$status" "$reserved" > "$dir/view.json"
  printf '%s\n' '{"signing":[{"authorityRoot":"200"}],"worldRoot":"300","height":"10"}' > "$dir/challenge.json"
  exit 0
fi
[ "$command" = submit ] || exit 40
printf call > "$dir/call.bin"
printf outcome > "$dir/outcome.bin"
if grep -q '"type": "settle"' "$intent"; then
  grep -q '"charge": "0"' "$intent" || exit 41
  printf 'zero-settle\n' >> "$state/mutations"
  printf 1 > "$state/status"
  printf 0 > "$state/reserved"
elif grep -q '"type": "disconnect"' "$intent"; then
  printf 'disconnect\n' >> "$state/mutations"
  printf 0 > "$state/status"
else
  exit 42
fi
printf '%s\n' '{"type":"confirmed","confirmation":"installed","worldRoot":"300","transactionId":"11","eventId":"12","acceptedCount":"13"}' > "$dir/outcome.json"
"#
    .replace("__STATE__", runtime.config.state_dir.to_str().unwrap());
    fs::write(&runtime.config.mini, script).unwrap();
    fs::set_permissions(&runtime.config.mini, fs::Permissions::from_mode(0o700)).unwrap();
    fs::write(runtime.config.state_dir.join("reserved"), b"0").unwrap();
    (runtime, root)
}

fn mark_birth(runtime: &mut Runtime) {
    runtime
        .journal
        .birth_next_ordinal
        .insert("content".into(), 1);
    runtime.journal.birth_operation = Some(BirthOperation {
        family: "content".into(),
        ordinal: 0,
        no_native_submit: true,
    });
    runtime.save().unwrap();
}

#[test]
fn crash_after_birth_marker_before_reserve_recovers_without_charge_and_returns_ordinal() {
    let (mut runtime, root) = fixture();
    mark_birth(&mut runtime);
    assert!(runtime.tool_call("mini_grain_status", &json!({})).is_err());
    let persisted: Value =
        serde_json::from_slice(&fs::read(runtime.config.state_dir.join("journal.json")).unwrap())
            .unwrap();
    assert_eq!(persisted["birthOperation"]["ordinal"], 0);
    assert_eq!(persisted["birthNextOrdinal"]["content"], 1);
    assert!(runtime.journal.tool_hold.is_none());
    runtime.finish_no_birth().unwrap();
    assert!(runtime.journal.birth_operation.is_none());
    assert_eq!(runtime.journal.birth_next_ordinal["content"], 0);
    runtime.finish_no_birth().unwrap();
    assert_eq!(runtime.journal.birth_next_ordinal["content"], 0);
    assert!(!runtime.config.state_dir.join("mutations").exists());
    assert!(runtime.journal.born_resources.is_empty());
    fs::remove_dir_all(root).unwrap();
}

#[test]
fn crash_after_reserve_before_birth_call_releases_only_zero() {
    let (mut runtime, root) = fixture();
    fs::write(runtime.config.state_dir.join("status"), b"1").unwrap();
    mark_birth(&mut runtime);
    runtime.mark_hold(true, "3", "2").unwrap();
    runtime
        .journal
        .tool_hold
        .as_mut()
        .unwrap()
        .reserve_confirmed = true;
    runtime.save().unwrap();
    fs::write(runtime.config.state_dir.join("status"), b"3").unwrap();
    fs::write(runtime.config.state_dir.join("reserved"), b"3").unwrap();
    assert!(runtime.reconcile_hold(true, true).is_err());
    assert!(runtime.abort_unsubmitted_hold(true).is_err());
    assert!(runtime.tool_call("mini_grain_status", &json!({})).is_err());
    runtime.finish_no_birth().unwrap();
    assert!(runtime.journal.birth_operation.is_none());
    assert!(runtime.journal.tool_hold.is_none());
    assert!(runtime.journal.tool_pending.is_none());
    assert!(runtime.journal.born_resources.is_empty());
    assert_eq!(
        fs::read_to_string(runtime.config.state_dir.join("mutations")).unwrap(),
        "zero-settle\ndisconnect\n"
    );
    fs::remove_dir_all(root).unwrap();
}

#[test]
fn hard_eof_before_tool_reserve_spawn_leaves_only_zero_charge_marker() {
    let (mut runtime, root) = fixture();
    fs::write(runtime.config.state_dir.join("status"), b"1").unwrap();
    mark_birth(&mut runtime);
    runtime.mark_hold(true, "3", "2").unwrap();
    runtime.cancelled.store(true, Ordering::SeqCst);
    let authority = runtime.tool().unwrap();
    let error = runtime
        .transition_as(
            &authority,
            json!({"type":"reserve","amount":"3"}),
            "tool reserve",
            "birth reserve",
            vec![],
        )
        .unwrap_err();
    assert!(error.contains("before Mini custody spawn"));
    assert!(runtime.journal.tool_pending.is_none());
    let hold = runtime.journal.tool_hold.as_ref().unwrap();
    assert_eq!(hold.charge, "0");
    assert!(hold.reserve_attempt.is_none());
    assert!(runtime.journal.birth_operation.is_some());
    assert!(!runtime.config.state_dir.join("mutations").exists());
    runtime.finish_no_birth().unwrap();
    assert!(runtime.journal.tool_hold.is_none());
    fs::remove_dir_all(root).unwrap();
}
