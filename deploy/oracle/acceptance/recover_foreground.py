#!/usr/bin/env python3
"""Untrusted acceptance orchestration, never native recovery authority.

Preserves the exact stopped attempt and binds approved binaries before the
fixed installer invokes native recovery. No tool submission or journal edits.
"""
import base64
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import sys

from continue_controller import (durable_json, manifest, read, require,
                                 retained_run_custody, sha, stopped_services, verify_lock)


def decode_export(value, store):
    require(value.get('protocol') == 'mini-spk-controller-evidence-v1' and value.get('store') == store,
            'controller export identity differs')
    files = value.get('files')
    require(isinstance(files, dict) and len(files) <= 4096, 'controller export file count invalid')
    decoded, size = {}, 0
    for name, row in files.items():
        relative = Path(name)
        require(not relative.is_absolute() and '..' not in relative.parts, 'export path escapes state')
        raw = base64.b64decode(row['base64'], validate=True)
        size += len(raw)
        require(size <= 64 * 1024 * 1024 and hashlib.sha256(raw).hexdigest() == row['sha256'],
                'controller export bytes differ')
        decoded[name] = raw
    return decoded


def settle_only(plan):
    goal = plan.get('goal', 'resume-session')
    require(goal in ('resume-session','settle-refusal'), 'unknown recovery plan goal')
    if goal == 'settle-refusal':
        require(type(plan.get('native_operation_id')) is int and plan['native_operation_id'] > 0,
                'native refusal operation malformed')
    return goal == 'settle-refusal'


def evidence_directory(plan):
    suffix = '-refusal-settlement' if settle_only(plan) else ''
    return Path(plan['run'])/'continuations'/('foreground-'+str(plan['operation_id'])+suffix)


def prebirth(export, store, request_id, operation_id, native_refusal=None):
    """Evidence shape only; native command rechecks actual current authority."""
    require(re.fullmatch('[0-9a-f]{32}', request_id) and type(operation_id) is int and operation_id > 0,
            'foreground identity malformed')
    files = decode_export(export, store)
    journal = json.loads(files['journal.json'])
    attempt = journal.get('foregroundAttempt') or {}
    require(journal.get('format') == 'minidregg-grain-runtime-v1'
            and attempt.get('requestId') == request_id and attempt.get('operationId') == operation_id
            and attempt.get('name') == 'mini_create_application_session'
            and attempt.get('phase') == 'uncertain' and attempt.get('reported') is False
            and attempt.get('resultPath') is None and attempt.get('resultSha256') is None,
            'not the exact unresolved foreground session')
    state = Path(journal['binding']['config']['stateDir'])
    request_name = f'foreground-{operation_id:016}.request.json'
    require(attempt.get('requestPath') == str(state / request_name)
            and hashlib.sha256(files[request_name]).hexdigest() == attempt['requestSha256'],
            'retained foreground request changed')
    request = json.loads(files[request_name])
    require(request == {'requestId':request_id,'name':'mini_create_application_session',
                        'arguments':{'application':'oracle-bootstrap-app','family':'oracle-session'}},
            'retained session selectors differ')
    identity = json.loads(files['foreground-request-' + request_id + '.json'])
    require(identity == {key:attempt[key] for key in ('requestId','operationId','requestSha256')},
            'foreground request index differs')
    for name in ('pending','toolPending','dispatchPending','providerPending','toolHold','dispatchHold','providerHold',
                 'birthOperation','birthPending','applicationApiAttempt','dispatchAttempt','child','settlementDue'):
        require(journal.get(name) is None, 'conflicting retained work: ' + name)
    expected_ordinals = {} if native_refusal is None else {'oracle-session':1}
    require(journal.get('bornResources') == [] and journal.get('birthNextOrdinal') == expected_ordinals
            and journal.get('unresolvedExternal') == [], 'a birth or unrelated uncertainty already exists')
    if native_refusal is not None:
        # These are retained evidence joins, not a decision that a birth was
        # refused. The native recovery revalidates the source and cleanup chain.
        require(type(native_refusal) is int and native_refusal > 0, 'refusal operation malformed')
        prefix = f'attempt-{native_refusal:016}/'
        require(not any(prefix+n in files for n in ('call.bin','submit-marker.json','outcome.bin')),
                'refusal attempt has submission evidence')
        proof = json.loads(files[prefix+'pre-submit-refusal.json'])
        require(proof.get('type') == 'minidregg-pre-submit-refusal-v1' and proof.get('stage') == 'prepare'
                and proof.get('operation') == 1
                and proof.get('frameSha256') == hashlib.sha256(files[prefix+'pre-submit-refusal.frame']).hexdigest()
                and proof.get('attemptManifestSha256') == hashlib.sha256(files[prefix+'attempt.json']).hexdigest(),
                'native pre-submit refusal evidence differs')
        verified = [name for name in files if name.startswith(prefix+'prepare-refusal-verify-') and name.endswith('/outcome.json')]
        require(len(verified) == 1, 'expected one native refusal verification')
        refusal = json.loads(files[verified[0]])
        require(refusal.get('type') == 'refused' and refusal.get('reason') == 'law-denied'
                and refusal.get('phase') == '70726570617265', 'native verified prepare refusal differs')
    require(not any(name.startswith(('birth-','foreground-recovery-')) for name in files),
            'native birth or recovery already began')
    hold = journal.get('parentHold') or {}
    require(hold.get('reserveConfirmed') is True and hold.get('reserveRefused') is False
            and hold.get('reserve') == '1' and hold.get('charge') == '0', 'original parent reserve absent')
    reserve = Path(hold['reserveAttempt'])
    require(reserve.parent == state and re.fullmatch('attempt-[0-9]{16}',reserve.name), 'reserve custody path differs')
    outcome = json.loads(files[reserve.name+'/outcome.json'])
    require(outcome.get('type') == 'confirmed' and outcome.get('confirmation') in ('installed','replayed')
            and outcome.get('worldRoot') == hold['reserveBoundary'], 'retained parent reserve receipt differs')
    require(reserve.name+'/call.bin' in files and reserve.name+'/outcome.bin' in files,
            'native reserve exact call/outcome absent')
    return {'request_id':request_id,'operation_id':operation_id,'request_sha256':attempt['requestSha256'],
            'journal_sha256':hashlib.sha256(files['journal.json']).hexdigest(),
            'reserve_call_sha256':hashlib.sha256(files[reserve.name+'/call.bin']).hexdigest(),
            'reserve_receipt':outcome,'parent_hold':hold,'binding':journal['binding']}


def prepare(plan_path, exported_path, status_path, sources_path, output):
    plan = read(plan_path)
    require(plan.get('protocol') == 'mini-oracle-foreground-recovery-plan-v1', 'recovery plan protocol differs')
    run = Path(plan['run'])
    verify_lock(run)
    world = read(run/'world-identity.json')
    require(world['store'] == plan['store'] and not list((run/'world/evidence').glob('start-*.cmd')),
            'retained Store or unstarted application boundary differs')
    terminal = settle_only(plan)
    require(output == evidence_directory(plan) and not output.exists(),
            'recovery evidence already exists or path differs; inspect, never repeat')
    for key in ('predecessor_export','predecessor_status','runtime','public_mini','spk','inventory','benchmark','qualification_manifest'):
        pin = plan[key]; path = Path(pin['path'])
        require(path.is_absolute() and not path.is_symlink() and path.is_file() and sha(path) == pin['sha256'],
                'recovery plan input changed: '+key)
        if key in ('runtime','public_mini'):
            require(path.stat().st_nlink == 1, 'installer binary must have exactly one hardlink: '+key)
    exported, status = read(exported_path), read(status_path)
    require(exported == read(Path(plan['predecessor_export']['path']))
            and status == read(Path(plan['predecessor_status']['path'])), 'fresh stopped evidence differs from reviewed predecessor')
    boundary = prebirth(exported,plan['store'],plan['request_id'],plan['operation_id'],
                        plan['native_operation_id'] if terminal else None)
    require(status.get('store') == plan['store'] and status.get('stopped') is True
            and status['publicListener']['binarySha256'] == plan['old_public_mini_sha256']
            and status['runtimeSha256'] == plan['old_runtime_sha256'], 'installed binary predecessor differs')
    custody, services = retained_run_custody(run), stopped_services(run,plan['store'])
    inputs = manifest(run/'input-sha256.txt')
    for key in ('spk','inventory','benchmark'):
        pin=plan[key];require(inputs.get(pin['path']) == pin['sha256'], 'original v5 input changed: '+key)
    sources = manifest(sources_path)
    qualification = manifest(Path(plan['qualification_manifest']['path']))
    for key in ('runtime','public_mini'):
        pin=plan[key]
        require(qualification.get(pin['path']) == pin['sha256'], 'recovery binary not in independent qualification manifest')
        require(sources.get(pin['path']) == pin['sha256'], 'recovery binary not in execution source manifest')
    workroom=run/'world/store/base/workroom'
    config=workroom/'deployment/pinned-config.json'
    require(sha(config)==plan['host_config_sha256'], 'source Host configuration changed')
    logical=[workroom/'store/forward-link.sqlite3',workroom/'store.head-anchor']
    require({p.name for p in (workroom/'store').iterdir()}=={'forward-link.sqlite3'}
            and all(p.is_file() and not p.is_symlink() for p in logical)
            and sum(p.stat().st_size for p in logical)<=64*1024*1024, 'stopped logical Store shape exceeds snapshot scope')
    original_result = run/'agent-lifetime/session-birth.result.json'
    require(original_result.is_file(), 'original failed client result absent')
    before={str(p):sha(p) for p in logical}
    output.mkdir(mode=0o700); prior=output/'prior';prior.mkdir(mode=0o700)
    for path in [*logical,config,plan_path,exported_path,status_path,sources_path,original_result]:
        target=prior/(hashlib.sha256(str(path).encode()).hexdigest()[:16]+'-'+path.name)
        shutil.copyfile(path,target);target.chmod(0o400)
        require(sha(path)==sha(target),'snapshot changed during copy')
    require(before=={str(p):sha(p) for p in logical},'Store changed during recovery snapshot')
    (output/'phases').mkdir(mode=0o700)
    durable_json(output/'prepared.json',{'protocol':'mini-oracle-foreground-recovery-prepared-v1','plan':plan,
        'plan_sha256':sha(plan_path),'boundary':boundary,'run_custody':custody,'stopped_services':services,
        'source_manifest':sources,'store_before':before,
        'original_result_sha256':sha(original_result),'snapshot_files':{p.name:sha(p) for p in prior.iterdir()},
        'resend':False,'acknowledge_before_settlement':False,'automatic_retry':False})
    return output


def validate_result(plan, recovered, retained, journal, exported):
    require(recovered.get('type') == 'mini-foreground-session-recovery-v1'
            and recovered.get('resultReady') is True
            and recovered.get('requestId') == plan['request_id']
            and str(recovered.get('operationId')) == str(plan['operation_id'])
            and recovered.get('acknowledged') is False, 'native recovery identity or ACK differs')
    terminal = settle_only(plan)
    require(retained.get('type') == 'tool-complete' and retained.get('requestId') == plan['request_id']
            and str(retained.get('operationId')) == str(plan['operation_id']) and retained.get('isError') is terminal
            and retained.get('result', {}).get('isError') is terminal, 'retained result differs from selected recovery goal')
    for name in ('parentHold','toolHold','pending','toolPending','birthOperation','birthPending'):
        require(journal.get(name) is None,'recovered session retains unsettled work: '+name)
    attempt=journal.get('foregroundAttempt') or {}
    require(attempt.get('requestId')==plan['request_id'] and attempt.get('operationId')==plan['operation_id']
            and attempt.get('phase')=='definite' and attempt.get('reported') is False,
            'native foreground is not definite and awaiting ordinary ACK')
    files = decode_export(exported, plan['store'])
    require(json.loads(files['journal.json']) == journal, 'settled export journal differs')
    state = Path(journal['binding']['config']['stateDir'])
    result_name = f"foreground-{plan['operation_id']:016}.result.json"
    raw = files[result_name]
    require(attempt.get('resultPath') == str(state / result_name)
            and hashlib.sha256(raw).hexdigest() == attempt.get('resultSha256') == recovered.get('resultSha256')
            and json.loads(raw) == retained.get('result'), 'native recovery result digest or bytes differ')
    if terminal:
        refusal = json.loads(retained['result']['text'])
        require(refusal.get('type') == 'mini-resource-birth-refused-v1'
                and refusal.get('reason') == 'law-denied' and refusal.get('phase') == 'prepare'
                and refusal.get('born') is False and refusal.get('toolCharge') == '0'
                and str(refusal.get('nativeOperationId')) == str(plan['native_operation_id']),
                'native definite refusal payload differs')
        disposition_name = f"foreground-{plan['operation_id']:016}.birth-refusal.json"
        disposition_raw = files[disposition_name]
        require(hashlib.sha256(disposition_raw).hexdigest() == refusal.get('dispositionSha256'),
                'native refusal disposition digest differs')
        disposition = json.loads(disposition_raw)
        origin = disposition.get('origin') or {}
        require(disposition.get('requestId') == plan['request_id']
                and disposition.get('requestSha256') == attempt.get('requestSha256')
                and origin.get('promptOperationId') == plan['operation_id']
                and origin.get('operationId') == plan['native_operation_id']
                and origin.get('family') == 'oracle-session' and origin.get('ordinal') == 0
                and origin.get('route') == 'session', 'native refusal disposition identity differs')
        require(journal.get('bornResources') == [] and journal.get('birthNextOrdinal') == {'oracle-session':1},
                'terminal refusal must preserve consumed ordinal without a born resource')
        for name in ('dispatchPending','providerPending','dispatchHold','providerHold',
                     'applicationApiAttempt','dispatchAttempt','child','settlementDue'):
            require(journal.get(name) is None, 'terminal refusal retains work: '+name)
        require(journal.get('unresolvedExternal') == [], 'terminal refusal retains external uncertainty')
    else:
        require({str(row.get('target')) for row in journal.get('bornResources',[])} == {'29420','29421'}
                and len(journal['bornResources']) == 2,'native session pair was not retained')


if __name__ == '__main__':
    try:
        if len(sys.argv)==7 and sys.argv[1]=='prepare':
            print(prepare(*map(Path,sys.argv[2:])))
        elif len(sys.argv)==3 and sys.argv[1]=='directory':
            print(evidence_directory(read(Path(sys.argv[2]))))
        elif len(sys.argv)==7 and sys.argv[1]=='result':
            validate_result(*[read(Path(p)) for p in sys.argv[2:]])
        else:raise ValueError('usage: recover_foreground.py prepare PLAN EXPORT STATUS SOURCES OUT | result PLAN RECOVERY RESULT JOURNAL EXPORT')
    except (ValueError,KeyError,OSError) as error:
        raise SystemExit('foreground continuation stopped: '+str(error))
