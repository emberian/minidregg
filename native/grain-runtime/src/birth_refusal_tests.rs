//! Controlled client fixture drives the actual create_resource, signed cleanup,
//! refusal retention and foreground completion. It does not claim Mini admission.
use super::*;
pub(super) const REQUEST: &str = "839a6731941b62b1179b4de9c076f0df";

pub(super) fn fixture(fail_tool_release: bool) -> (Runtime, PathBuf) {
    let (mut rt, root) = crate::publication_refusal_tests::fixture(false, false, true);
    let script = r#"#!/usr/bin/python3
import sys,json,pathlib,hashlib
state=pathlib.Path('__STATE__')
cmd=sys.argv[1]; args=dict(zip(sys.argv[2::2],sys.argv[3::2]))
d=pathlib.Path(args['--dir']);d.mkdir(parents=True,exist_ok=True)
i=json.loads(pathlib.Path(args['--intent']).read_bytes())
p=state/'physical.json'; grains=json.loads(p.read_bytes())
def out(n,v): (d/n).write_text(json.dumps(v))
def digest(n): return hashlib.sha256((d/n).read_bytes()).hexdigest()
with (state/'operations.jsonl').open('a') as log: log.write(json.dumps({'command':cmd,'source':i})+'\n')
if cmd=='query':
 t=i['purpose']['target'];g=grains[t];out('view.json',{'type':'resource','cell':{'root':str(1000+int(t)+int(g['generation'])*10+int(g['status'])),'grain':g}})
 out('challenge.json',{'height':'12','worldRoot':'300','authorityRoot':'200','signing':[{}]});(d/'view.bin').write_bytes(b'controlled view');(d/'challenge.bin').write_bytes(b'controlled challenge');sys.exit(0)
assert cmd=='submit'
if 'grainBirth' in i:
 (d/'config.json').write_bytes(pathlib.Path(args['--config']).read_bytes())
 (d/'signed-observation.bin').write_bytes(b'signed prepare request')
 # a prepare refusal is decided before any append: the Host answers it under NO_RECORD (253), never HOST_OUTCOME (255)
 (d/'pre-submit-refusal.frame').write_bytes(b'\xfdcanonical native prepare refusal')
 out('attempt.json',{'format':'minidregg-resource-client-attempt-v1','operation':'submit','host':args['--host'],'config':str(d/'config.json'),'socket':args['--socket']})
 out('pre-submit-refusal.json',{'type':'minidregg-pre-submit-refusal-v1','stage':'prepare','operation':1,'frameSha256':digest('pre-submit-refusal.frame'),'requestSha256':digest('signed-observation.bin'),'hostConfigSha256':digest('config.json'),'attemptManifestSha256':digest('attempt.json')})
 sys.exit(3)
g=i['grain'];t=g['task'];a=g['operation'];v=grains[t]
if t=='7102' and a['type']=='settle' and (state/'fail-release').exists(): sys.exit(3)
if a['type']=='attach':v['generation']=str(int(v['generation'])+1);v['status']='1'
elif a['type']=='reserve':v['status']='4' if t=='7101' else '3';v['reserved']=a['amount'];v['remaining']=str(int(v['remaining'])-int(a['amount']))
elif a['type']=='settle':v['status']='2' if t=='7101' else '1';v['remaining']=str(int(v['remaining'])+int(v['reserved'])-int(a['charge']));v['reserved']='0'
elif a['type']=='disconnect':v['status']='0';v['generation']=str(int(v['generation'])+1)
else:sys.exit(40)
p.write_text(json.dumps(grains));(d/'call.bin').write_bytes(b'controlled call');(d/'outcome.bin').write_bytes(b'controlled outcome')
out('outcome.json',{'type':'confirmed','confirmation':'installed','worldRoot':'300','transactionId':'11','eventId':'12','acceptedCount':'13'})
"#.replace("__STATE__",rt.config.state_dir.to_str().unwrap());
    fs::write(&rt.config.mini, script).unwrap();
    fs::write(&rt.config.host,b"#!/bin/sh\n[ \"$2\" = inspect ] && [ \"$3\" = outcome ] || exit 1\nprintf '%s' '{\"type\":\"refused\",\"phase\":\"70726570617265\",\"reason\":\"law-denied\"}' > \"$5\"\n").unwrap();
    fs::write(
        rt.config.state_dir.join("physical.json"),
        serde_json::to_vec(&json!({
            "7101":{"task":"7101","generation":"1","status":"2","remaining":"10","reserved":"0"},
            "7102":{"task":"7102","generation":"0","status":"0","remaining":"10","reserved":"0"}
        }))
        .unwrap(),
    )
    .unwrap();
    if fail_tool_release {
        fs::write(rt.config.state_dir.join("fail-release"), b"1").unwrap();
    }
    rt.config.foreground_tool = Some(ForegroundToolProfile {
        reserve: "1".into(),
        charge: "0".into(),
    });
    rt.config.tool_task.as_mut().unwrap().allowed_birth_families=vec![serde_json::from_value(json!({
        "name":"page","genesis":{},"template":{},"predicate":{"type":"all","predicates":[]},
        "factoryTarget":"10","factoryObserveCapability":"54","payerAccount":"11","payerCapability":"41","payerObserveCapability":"42",
        "tariffBase":"1","tariffPerBirth":"1","targetStart":"9000","ownerCapabilityStart":"9100","controlCapabilityStart":"9200",
        "maxBirths":2,"maxResultBytes":1024
    })).unwrap()];
    rt.journal.child = None;
    rt.journal.hermes_session = None;
    rt.child = None;
    rt.prompt_active = false;
    rt.journal.connection = Connection::Soft;
    rt.journal.next_operation_id = 14;
    let bytes = serde_json::to_vec(
        &json!({"requestId":REQUEST,"name":"mini_create_resource","arguments":{"family":"page"}}),
    )
    .unwrap();
    let path = rt
        .config
        .state_dir
        .join("foreground-0000000000000013.request.json");
    write_new(&path, &bytes).unwrap();
    let digest = sha256_bytes(&bytes).unwrap();
    write_new(
        &foreground_tombstone_path(&rt.config.state_dir, REQUEST),
        &serde_json::to_vec(&ForegroundTombstone {
            request_id: REQUEST.into(),
            operation_id: 13,
            request_sha256: digest.clone(),
        })
        .unwrap(),
    )
    .unwrap();
    rt.journal.foreground_attempt = Some(ForegroundAttempt {
        request_id: REQUEST.into(),
        operation_id: 13,
        name: "mini_create_resource".into(),
        request_path: path,
        request_sha256: digest,
        phase: ForegroundPhase::Executing,
        result_path: None,
        result_sha256: None,
        reported: false,
    });
    rt.foreground_operation = Some(13);
    rt.completion_phase.store(PHASE_RUNNING, Ordering::SeqCst);
    rt.reserve_parent_work_lease("1", "0", "foreground tool")
        .unwrap();
    (rt, root)
}

pub(super) fn produce(rt: &mut Runtime) -> String {
    let error = rt
        .create_resource(&json!({"family":"page"}), None)
        .unwrap_err();
    rt.foreground_operation = None;
    error
}

#[test]
fn native_refusal_producer_cleanup_and_foreground_completion_join() {
    let (mut rt, root) = fixture(false);
    let error = produce(&mut rt);
    assert!(error.contains("resource birth refused"), "{error}");
    assert!(rt.journal.birth_operation.is_none() && rt.journal.tool_hold.is_none());
    assert_eq!(rt.journal.birth_next_ordinal["page"], 1);
    assert!(rt.journal.born_resources.is_empty());
    let result = rt.completed_birth_refusal_result().unwrap().unwrap();
    assert_eq!(result["isError"], true);
    let detail: Value = serde_json::from_str(result["text"].as_str().unwrap()).unwrap();
    assert_eq!(detail["reason"], "law-denied");
    assert!(rt.create_resource(&json!({"family":"page"}), None).is_err());
    rt.complete_foreground_result(result.clone(), "0").unwrap();
    assert!(rt.journal.parent_hold.is_none() && rt.journal.settlement_due.is_none());
    assert_eq!(
        rt.journal.foreground_attempt.as_ref().unwrap().phase,
        ForegroundPhase::Definite
    );
    assert!(!rt.journal.foreground_attempt.as_ref().unwrap().reported);
    assert_eq!(rt.foreground_result(REQUEST).unwrap().1, result);
    let before = fs::read(rt.config.state_dir.join("operations.jsonl")).unwrap();
    assert!(rt.complete_foreground_result(result, "0").is_err());
    assert_eq!(
        before,
        fs::read(rt.config.state_dir.join("operations.jsonl")).unwrap()
    );
    rt.acknowledge_foreground(REQUEST).unwrap();
    assert_eq!(rt.journal.foreground_history.len(), 1);
    fs::remove_dir_all(root).unwrap();
}

#[test]
fn native_refusal_cleanup_failure_never_becomes_definite() {
    let (mut rt, root) = fixture(true);
    produce(&mut rt);
    let durable: Journal =
        serde_json::from_slice(&fs::read(rt.config.state_dir.join("journal.json")).unwrap())
            .unwrap();
    assert!(durable.birth_refusal.is_some());
    assert!(durable
        .birth_refusal
        .as_ref()
        .unwrap()
        .terminal_tool
        .is_none());
    assert!(durable.birth_operation.is_some() && durable.tool_pending.is_some());
    assert!(rt.completed_birth_refusal_result().is_err());
    assert!(rt.foreground_result(REQUEST).is_err());
    assert!(rt.journal.parent_hold.is_some());
    fs::remove_dir_all(root).unwrap();
}

#[test]
fn attached_completion_hard_cancel_runs_disconnect_without_settlement_or_rebirth() {
    let (mut rt, root) = fixture(false);
    produce(&mut rt);
    let result = rt.completed_birth_refusal_result().unwrap().unwrap();
    let log_path = rt.config.state_dir.join("operations.jsonl");
    let before = fs::read_to_string(&log_path).unwrap().lines().count();
    rt.hard_connection.store(true, Ordering::SeqCst);
    rt.completion_phase.store(PHASE_CANCELLED, Ordering::SeqCst);
    assert!(rt.complete_attached_foreground_result(result, "0").is_err());
    // Only disconnect changes this physical connection flag. The shared
    // completion's durable error fence alone deliberately does not.
    assert!(!rt.hard_connection.load(Ordering::SeqCst));
    assert!(rt.cancelled.load(Ordering::SeqCst));
    assert!(rt.custody_gate.is_idle());
    assert!(rt.journal.parent_hold.is_some());
    assert!(rt.journal.birth_refusal.is_some());
    assert!(rt
        .journal
        .foreground_attempt
        .as_ref()
        .unwrap()
        .result_path
        .is_some());
    assert_eq!(
        rt.journal.foreground_attempt.as_ref().unwrap().phase,
        ForegroundPhase::Uncertain
    );
    let tail: Vec<Value> = fs::read_to_string(&log_path)
        .unwrap()
        .lines()
        .skip(before)
        .map(|line| serde_json::from_str(line).unwrap())
        .collect();
    assert!(tail.iter().any(|entry| entry["command"] == "submit"
        && entry["source"]["grain"]["operation"]["type"] == "interrupt"));
    assert!(!tail
        .iter()
        .any(|entry| entry["source"].get("grainBirth").is_some()
            || entry["source"]["grain"]["operation"]["type"] == "settle"));
    fs::remove_dir_all(root).unwrap();
}
