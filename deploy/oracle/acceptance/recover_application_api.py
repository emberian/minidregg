#!/usr/bin/env python3
"""Untrusted qualification checks around native recovery of one retained API call.

The native controller proves non-dispatch and settles its own foreground/hold.
This harness preserves evidence; it never edits a native journal or Store.
"""
import base64
import hashlib
import json
import errno
import socket
import stat
import re
import tempfile
from pathlib import Path
import shutil
import sys


def read(path):
    return json.loads(Path(path).read_bytes())


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def require(value, message):
    if not value:
        raise ValueError(message)


def exported(export, name):
    entry = export['files'][name]
    raw = base64.b64decode(entry['base64'], validate=True)
    require(hashlib.sha256(raw).hexdigest() == entry['sha256'], 'export digest differs')
    return raw


def recovery_directories(run):
    paths = list((run / 'continuations').glob('application-api-recovery-*'))
    require(all(p.name.rsplit('-', 1)[-1].isdigit() for p in paths), 'unknown API recovery directory')
    paths.sort(key=lambda p: int(p.name.rsplit('-', 1)[-1]))
    require([int(p.name.rsplit('-', 1)[-1]) for p in paths] == list(range(1, len(paths)+1)),
            'API recovery sequence is incomplete')
    return paths


def previous_execution(run):
    paths = recovery_directories(run)
    if not paths:
        return run / 'continuations/activation-successor-1'
    previous = paths[-1]
    boundary = read(previous / 'prepared.json')['boundary']
    if boundary.get('kind') in ('startup-refusal', 'readiness-refusal'):
        export = read(previous / 'observations/controller-export.json')
        journal = json.loads(exported(export, 'journal.json'))
        refused = (readiness_refusal(export, journal, previous / 'prior') if boundary['kind'] == 'readiness-refusal'
                   else startup_refusal(export, journal, previous / 'prior/probe', boundary['request_id']))
        require(refused == boundary['pre_admission'],
                'previous startup refusal evidence differs')
    else:
        check_native(previous, terminal=True)
    require((previous / 'phases/enrollment.completed.json').is_file(),
            'previous API recovery did not reach enrollment')
    return previous


def retained_paths(run, after=None):
    """Find the first preserved version after an execution, before later overwrites."""
    retained = {}
    for directory in recovery_directories(run):
        if after is not None and int(directory.name.rsplit('-', 1)[-1]) <= int(after.name.rsplit('-', 1)[-1]):
            continue
        prepared = read(directory / 'prepared.json')
        for name, entry in {**prepared['preserved'], **prepared['archived']}.items():
            retained.setdefault(name, entry)
    return retained


def startup_refusal(export, journal, probe, request_id):
    """Recognize a native refusal before tool allocation and its timed-out read."""
    require(journal['connection'] == 'fenced' and all(journal.get(key) is None for key in (
        'foregroundAttempt','applicationApiAttempt','parentHold','dispatchAttempt','dispatchPending',
        'dispatchHold','toolPending','toolHold','pending','child','birthPending','birthOperation',
        'providerPending','providerHold','providerAttempt','settlementDue',
        'workspaceAttempt','roomAttempt','workspaceBirth')) and not journal.get('unresolvedExternal'),
        'startup refusal has retained native custody')
    result = read(probe / 'discover-core-query.result.json')
    require(result == {'isError':True,'operationId':None,'requestId':request_id,
        'result':'foreground tool requires an attached, reconciled idle task',
        'type':'tool-complete','v':1}, 'not an exact native pre-admission refusal')
    require(read(probe / 'discover-core-query.request.json') == {
        'requestId':request_id,'name':'mini_oracle_discover','arguments':{
        'application':'oracle-app','availability':'live_direct','limit':1,'query':'core.query'}},
        'pre-admission discovery arguments differ')
    require(not any(x.get('requestId') == request_id for x in journal.get('foregroundHistory', [])),
            'refused request has a retained foreground operation')
    nonce = journal['nextOperationId'] - 1
    directory = 'query-%016d' % nonce
    config = journal['binding']['config']
    intent = json.loads(exported(export, directory + '/intent-source.json'))
    require(intent == {'grants':[{'capability':config['queryCapability'],'kind':'object','target':config['task']}],
        'nonce':str(nonce),'purpose':{'kind':'object','target':config['task'],'type':'query','view':'resource'},
        'subject':config['subject']}, 'last interrupted helper was not the bound read-only query')
    attempt = json.loads(exported(export, directory + '/attempt/attempt.json'))
    require(attempt['operation'] == 'query' and directory + '/attempt/challenge.json' not in export['files'],
            'read-only startup observation boundary differs')
    return {'result':result,'query':directory,'query_intent_sha256':export['files'][directory+'/intent-source.json']['sha256']}


def readiness_refusal(export, journal, root):
    """Exact failed maintenance query, before the harness allocated a tool ID."""
    require(not (root / 'probe').exists(), 'readiness failure already has a tool probe')
    require((root / 'readiness-probe.json').read_bytes() == b'' and
            (root / 'readiness-probe.stderr').read_text() ==
            'grain-runtime admin: error: controller readiness lacks a signed idle task\n',
            'readiness refusal differs')
    require(journal['connection'] == 'soft' and all(journal.get(key) is None for key in (
        'foregroundAttempt','applicationApiAttempt','parentHold','dispatchAttempt','dispatchPending',
        'dispatchHold','toolPending','toolHold','pending','child','birthPending','birthOperation',
        'providerPending','providerHold','providerAttempt','settlementDue',
        'workspaceAttempt','roomAttempt','workspaceBirth')) and not journal.get('unresolvedExternal'),
        'readiness refusal has retained native custody')
    nonce = journal['nextOperationId'] - 1
    directory = 'query-%016d' % nonce
    config = journal['binding']['config']
    intent = json.loads(exported(export, directory + '/intent-source.json'))
    require(intent == {'grants':[{'capability':config['queryCapability'],'kind':'object','target':config['task']}],
        'nonce':str(nonce),'purpose':{'kind':'object','target':config['task'],'type':'query','view':'resource'},
        'subject':config['subject']}, 'readiness helper is not the bound read-only query')
    attempt = json.loads(exported(export, directory + '/attempt/attempt.json'))
    view = json.loads(exported(export, directory + '/attempt/view.json'))
    challenge = json.loads(exported(export, directory + '/attempt/challenge.json'))
    require(attempt['operation'] == 'query' and view['type'] == 'resource' and
            view['cell']['grain']['task'] == config['task'] and
            view['cell']['grain']['status'] == '2' and view['cell']['grain']['reserved'] == '0' and
            challenge['intent'] == intent and challenge.get('height') and challenge.get('worldRoot') and
            bool(exported(export, directory + '/attempt/signed-observation.bin')),
            'readiness signed attached-idle evidence differs')
    return {'query':directory, 'query_intent_sha256':export['files'][directory+'/intent-source.json']['sha256'],
            'view_sha256':export['files'][directory+'/attempt/view.json']['sha256'],
            'signed_observation_sha256':export['files'][directory+'/attempt/signed-observation.bin']['sha256'],
            'no_tool_request':True}


def checked_boundary(run, observations, request_id):
    root = run / 'agent-lifetime'
    readiness = request_id is None
    previous = previous_execution(run)
    require(read(previous / 'exit.json') == {'execution_exit': 1 if readiness else 2, 'cleanup_exit': 0,
                                           'namespace_preserved': True}, 'not stopped after the retained API failure')
    if not readiness:
        require((root / 'probe/discover-core-query.request-id').read_text().strip() == request_id,
                'foreground request ID differs')
    export = read(observations / 'controller-export.json')
    world = read(run / 'world-identity.json')
    require(export['protocol'] == 'mini-spk-controller-evidence-v1' and export['store'] == world['store'],
            'controller export identity differs')
    journal = json.loads(exported(export, 'journal.json'))
    require(journal == read(root / 'controller-final-journal.json'), 'retained controller journal differs')
    foreground = journal['foregroundAttempt']; api = journal['applicationApiAttempt']
    if not readiness and previous.name.startswith('application-api-recovery-'):
        require(request_id != read(previous / 'prepared.json')['boundary']['request_id'],
                'original audited request cannot be submitted again')
    pre_admission = None
    if readiness:
        pre_admission = readiness_refusal(export, journal, root)
        hold = None
    elif foreground is None and api is None:
        pre_admission = startup_refusal(export, journal, root / 'probe', request_id)
        hold = None
    else:
        require(isinstance(foreground, dict) and isinstance(api, dict), 'partial foreground/API custody is not recoverable here')
        require(foreground['requestId'] == request_id and foreground['name'] == 'mini_oracle_discover'
                and foreground['phase'] == 'uncertain' and foreground['resultPath'] is None
                and foreground['resultSha256'] is None and foreground['reported'] is False,
                'foreground is not the original uncertain discovery')
        request = exported(export, Path(foreground['requestPath']).name)
        require(hashlib.sha256(request).hexdigest() == foreground['requestSha256'], 'foreground request changed')
        request_value = json.loads(request)
        require(request_value == {'requestId': request_id, 'name': 'mini_oracle_discover',
                'arguments': {'application': 'oracle-app', 'availability': 'live_direct', 'limit': 1,
                              'query': 'core.query'}}, 'original discovery arguments differ')
        require(api['routeName'] == 'oracle-app' and api['phase'] == 'uncertain' and api['reported'] is False
                and all(api[key] is None for key in ('operationFingerprint', 'lifetimeCommittedReceipt',
                        'lifetimeSettledResponseSha256', 'lifetimeSettlement', 'replyPath', 'replySha256')),
                'API has a possible delivery or settlement marker')
        forward = exported(export, Path(api['requestPath']).name)
        require(hashlib.sha256(forward).hexdigest() == api['requestSha256'], 'forward bytes changed')
        require(json.loads(forward) == {'bindingSha256': api['bindingSha256'], 'bodyHex': '',
            'headers': [{'name': 'accept', 'value': 'application/json'}], 'method': 'GET',
            'operationId': str(api['operationId']), 'path': 'operations', 'protocol': 'mini-spk-agent-api-v3',
            'query': 'offset=0&limit=1&q=core.query&availability=live_direct', 'type': 'dispatch-v3'},
            'retained API request differs')
        require(all(journal[key] is None for key in ('dispatchAttempt', 'dispatchPending', 'dispatchHold',
                    'toolPending', 'toolHold', 'pending', 'child')), 'additional native custody is pending')
        hold = journal['parentHold']
        require(hold['reserveConfirmed'] is True and hold['reserveRefused'] is False
                and hold['reserve'] == '1' and hold['charge'] == '0', 'foreground hold differs')
    status = read(observations / 'controller-status.json')
    require(status['store'] == world['store'] and status['stopped'] is True
            and status['runtimeSha256'] == sha((previous if previous.name.startswith('application-api-recovery-') else run / 'continuations/activation-recovery-1') / 'bin/grain-runtime')
            and status['controllerConfigSha256'] == sha(root / 'controller-active-initial.json'),
            'stopped controller pins differ')
    start = read(previous / 'successor-start.json')
    state = Path(read(run / 'world/evidence/profile-result.json')['stateRoot'])
    app = state / 'apps/9101' / ('g' + start['generation'])
    record = read(app / 'record.json')
    manager = dict(line.split('=', 1) for line in (observations / 'manager.txt').read_text().splitlines() if '=' in line)
    require(record['phase'] == 'running' and record['identity']['unit'] == start['unit']
            and (api is None or record['invocation_id'] == api['hostInvocation'])
            and manager['Id'] == start['unit'] and manager['MainPID'] == '0'
            and manager['ActiveState'] in ('inactive', 'failed') and manager['Job'] in ('', '0'),
            'retained app incarnation is not physically stopped')
    route_name=read(root/'registered-agent-route.json')['registration']['name']
    require(isinstance(route_name,str) and re.fullmatch(r'[A-Za-z0-9_-]{1,48}',route_name), 'registered route name differs')
    native = app / ('agent-'+route_name+'-attempts')
    if api is None:
        require(not native.exists() or not list(native.iterdir()), 'startup refusal has resident API evidence')
    else:
        dispatch = native / ('agent-lifetime-dispatch-op-' + str(api['operationId']))
        require(dispatch.is_dir() and not list(dispatch.iterdir()), 'resident native dispatch evidence exists')
        client = native / ('agent-lifetime-client-op-' + str(api['operationId']))
        require({p.name for p in client.iterdir()} == {'received-v3.json', 'forward-request-v3.json'}
                and read(client / 'forward-request-v3.json') == json.loads(forward)
                and read(client / 'received-v3.json')['forwardSha256'] == sha(client / 'forward-request-v3.json'),
                'resident forward evidence differs')
    require(not any((run / path).exists() for path in ('browser', 'world/evidence/post-a1.stdout',
                                                     'agent-lifetime/probe-restart')),
            'later qualification work already exists')
    return {'kind': 'readiness-refusal' if readiness else ('startup-refusal' if pre_admission else 'unreserved-api'), 'pre_admission': pre_admission,
            'previous_execution': str(previous), 'store': world['store'], 'request_id': request_id, 'foreground': foreground, 'api': api,
            'parent_hold': hold, 'old_generation': start['generation'], 'old_record': record,
            'journal_sha256': export['files']['journal.json']['sha256'],
            'grant_receipt': read(root / 'issued-grant.json')['grantReceipt'],
            'runtime_sha256': status['runtimeSha256'],
            'dispatch_task': journal['binding']['config']['dispatchTask']['task'], 'retransmit': False}


def prepare(run, observations, request_id):
    boundary = checked_boundary(run, observations, request_id)
    output = run / 'continuations' / ('application-api-recovery-' + str(len(recovery_directories(run)) + 1))
    require(not output.exists(), 'API recovery already prepared; inspect retained phases')
    for line in (run / 'input-sha256.txt').read_text().splitlines():
        digest, path = line.split(None, 1)
        require(sha(Path(path)) == digest, 'original input changed')
    output.mkdir(mode=0o700)
    (output / 'phases').mkdir(mode=0o700)
    prior = output / 'prior'; prior.mkdir(mode=0o700)
    shutil.copytree(observations, output / 'observations')
    # Freeze earlier phase evidence before services/initial labels change.
    preserved = {}
    for directory in [run / 'continuations/activation-recovery-1', run / 'continuations/activation-successor-1',
                      *[p for p in recovery_directories(run) if p != output]]:
        for phase in (directory / 'phases').glob('*.completed.json'):
            for name, digest in read(phase)['evidence'].items():
                source = Path(name)
                if source.is_file() and sha(source) == digest and name not in preserved:
                    target = prior / (str(len(preserved)) + '-' + source.name)
                    shutil.copy2(source, target)
                    preserved[name] = {'path': str(target), 'sha256': digest}
    archived = {}
    for path in [*(run / 'agent-lifetime').glob('*initial*'),
                 run / 'agent-lifetime/probe', run / 'agent-lifetime/probe.stderr',
                 run / 'agent-lifetime/probe.stdout', run / 'agent-lifetime/readiness-probe.json',
                 run / 'agent-lifetime/readiness-probe.stderr']:
        if not path.exists():
            continue
        target = prior / path.name
        entries = [path] if path.is_file() else [p for p in path.rglob('*') if p.is_file()]
        archived.update({str(p): {'path': str(target if path.is_file() else target / p.relative_to(path)),
                                 'sha256': sha(p)} for p in entries})
        path.rename(target)
    value = {'schema': 'mini-oracle-application-api-recovery-v1', 'boundary': boundary,
             'preserved': preserved, 'archived': archived, 'automatic_retry': False}
    (output / 'prepared.json').write_text(json.dumps(value, indent=2) + '\n')
    print(output)

def check_native(directory, terminal=False):
    prepared = read(directory / 'prepared.json'); boundary = prepared['boundary']
    result = read(directory / 'native-recovery.json'); proof = result['proof']
    require(result['type'] == 'mini-foreground-api-unreserved-recovery-v1'
            and result['foregroundRemains'] is True and proof['noDispatch'] is True
            and proof['action'] == 'recover-unreserved-foreground-api'
            and proof['requestId'] == boundary['request_id']
            and proof['foregroundOperationId'] == str(boundary['foreground']['operationId'])
            and proof['apiOperationId'] == str(boundary['api']['operationId'])
            and proof['requestSha256'] == boundary['foreground']['requestSha256']
            and proof['forwardRequestSha256'] == boundary['api']['requestSha256']
            and proof['bindingSha256'] == boundary['api']['bindingSha256']
            and proof['signedPurse']['grain']['task'] == boundary['dispatch_task']
            and proof['signedPurse']['grain']['status'] in ('0', '1', '2', '6')
            and proof['signedPurse']['grain']['reserved'] == '0'
            and int(proof['processFirstOperationId']) > max(boundary['foreground']['operationId'], boundary['api']['operationId'])
            and int(proof['decisionId']) >= int(proof['queryStartOperationId']) >= int(proof['processFirstOperationId']),
            'native non-dispatch proof differs')
    journal = read(directory / ('terminal-journal.json' if terminal else 'after-api-journal.json'))
    require(journal['applicationApiAttempt'] is None and proof in journal['reconciliationLog'],
            'native recovery audit absent')
    retained = [x for x in journal['applicationApiHistory'] if x['operationId'] == boundary['api']['operationId']]
    require(len(retained) == 1 and retained[0]['phase'] == 'no-dispatch' and retained[0]['reported'] is True
            and retained[0]['requestSha256'] == boundary['api']['requestSha256'], 'native API history differs')
    if terminal:
        require(all(journal[key] is None for key in ('foregroundAttempt','applicationApiAttempt','parentHold',
            'toolHold','toolPending','dispatchHold','dispatchPending','dispatchAttempt','pending','birthPending',
            'birthOperation','providerPending','providerHold','providerAttempt','settlementDue')),
            'native custody remains pending')
        history = [x for x in journal['foregroundHistory'] if x['requestId'] == boundary['request_id']]
        require(len(history) == 1 and history[0]['phase'] == 'audited' and history[0]['reported'] is True
                and history[0]['resultPath'] is None and history[0]['resultSha256'] is None,
                'foreground did not terminate as audited without a fabricated result')
        require(any(x.get('action') == 'foreground-audited-terminal'
                    and x.get('operationId') == str(boundary['foreground']['operationId'])
                    and x.get('requestSha256') == boundary['foreground']['requestSha256']
                    for x in journal['reconciliationLog']), 'native terminal audit absent')
    return proof


def checked_stopped_broker(observations, endpoint, unit, uid):
    manager=dict(line.split('=',1) for line in (observations/'broker-manager.txt').read_text().splitlines() if '=' in line)
    require(manager['Id']==unit and manager['MainPID']=='0' and manager['ControlGroup']==''
            and manager['ActiveState'] in ('inactive','failed'), 'broker owner unit is not stopped')
    try: before=endpoint.lstat()
    except FileNotFoundError: return {'unit':unit,'socket':str(endpoint),'state':'absent','nativeReclaimRequired':False}
    require(stat.S_ISSOCK(before.st_mode) and before.st_uid==uid and stat.S_IMODE(before.st_mode)==0o600
            and before.st_nlink==1,'retained broker socket custody differs')
    with socket.socket(socket.AF_UNIX,socket.SOCK_STREAM) as probe:
        probe.settimeout(1)
        try: probe.connect(str(endpoint))
        except OSError as error: require(error.errno==errno.ECONNREFUSED,'broker endpoint liveness is uncertain')
        else: raise ValueError('broker endpoint still accepts connections')
    after=endpoint.lstat()
    identity=lambda s:(s.st_dev,s.st_ino,s.st_uid,s.st_mode,s.st_ctime_ns)
    require(identity(before)==identity(after),'broker endpoint changed during inspection')
    return {'unit':unit,'socket':str(endpoint),'state':'stale-refused','nativeReclaimRequired':True,
            'device':before.st_dev,'inode':before.st_ino,'uid':before.st_uid,'mode':stat.S_IMODE(before.st_mode)}


def checked_stopped_resume(run, directory, observations):
    """Resume only an audited original call whose native STOP finished before START."""
    require(directory == recovery_directories(run)[-1], 'resume must name latest API recovery')
    prepared = read(directory/'prepared.json'); b = prepared['boundary']
    require(b.get('kind') == 'unreserved-api', 'resume requires native unreserved API recovery')
    proof = check_native(directory, terminal=True)
    require(read(directory/'exit.json') == {'execution_exit':143,'cleanup_exit':0,'namespace_preserved':True},
            'resume requires recorded operator interruption and successful cleanup')
    require((directory/'phases/retire-incarnation.started.json').is_file()
            and not any((directory/name).exists() for name in
                ('phases/retire-incarnation.completed.json','phases/successor-start.started.json',
                 'successor-start.json','resumption')), 'resume boundary has already advanced')
    for entry in [*prepared['preserved'].values(), *prepared['archived'].values()]:
        require(sha(Path(entry['path'])) == entry['sha256'], 'preserved original evidence changed')
    for line in (directory/'recovery-input-sha256.txt').read_text().splitlines():
        digest,name=line.split(None,1); require(sha(Path(name))==digest,'original recovery source changed')
    status=read(observations/'controller-status.json')
    export=read(observations/'controller-export.json'); journal=json.loads(exported(export,'journal.json'))
    terminal=read(directory/'terminal-journal.json')
    active_config=run/'agent-lifetime/controller-active-initial.json'
    retained_config=Path(prepared['archived'].get(str(active_config),{'path':str(active_config)})['path'])
    require(status['store']==b['store'] and status['stopped'] is True
            and status['runtimeSha256']==sha(directory/'bin/grain-runtime')
            and status['controllerConfigSha256']==sha(retained_config),
            'stopped controller pin differs')
    require(journal['binding']==terminal['binding'] and proof in journal['reconciliationLog']
            and journal['applicationApiHistory']==terminal['applicationApiHistory']
            and journal['foregroundHistory']==terminal['foregroundHistory']
            and journal['connection']=='detached'
            and all(journal.get(k) is None for k in ('foregroundAttempt','applicationApiAttempt','parentHold',
                'dispatchAttempt','dispatchPending','dispatchHold','toolPending','toolHold','pending','child',
                'birthPending','birthOperation','providerPending','providerHold','providerAttempt','settlementDue',
                'workspaceAttempt','roomAttempt','workspaceBirth')) and not journal.get('unresolvedExternal'),
            'stopped controller custody changed after audit')
    state=Path(read(run/'world/evidence/profile-result.json')['stateRoot'])
    app=state/'apps/9101'; old=app/('g'+b['old_generation']); record=read(old/'record.json')
    stop=read(directory/'stop.json')
    manager=dict(line.split('=',1) for line in (observations/'manager.txt').read_text().splitlines() if '=' in line)
    require(stop['protocol']=='mini-spk-grain-stop-v1' and stop['app']=='9101'
            and stop['generation']==b['old_generation'] and stop['unit']==b['old_record']['identity']['unit']
            and record['phase']=='stopped' and record['identity']==b['old_record']['identity']
            and record['invocation_id']==b['old_record']['invocation_id']
            and manager['Id']==stop['unit'] and manager['MainPID']=='0'
            and manager['ActiveState'] in ('inactive','failed') and manager['Job'] in ('','0'),
            'native STOP and physical stopped identity differ')
    require(all(not p.name[1:].isdigit() or int(p.name[1:])<=int(b['old_generation']) for p in app.glob('g*')),
            'successor generation already exists')
    anchors=list((old/'stop-completion').rglob('receipt-anchor.json'))
    require(anchors and all(read(p).get('eventId') and read(p).get('worldRoot') for p in anchors),
            'native STOP receipt anchors absent')
    require(not any((run/name).exists() for name in ('browser','world/evidence/post-a1.stdout','agent-lifetime/probe-restart'))
            and not (run/'agent-lifetime/probe/discover-core-query.request-id').exists(),
            'later qualification already began')
    return {'schema':'mini-oracle-api-stopped-resumption-v1','store':b['store'],
            'request_id':b['request_id'],'old_generation':b['old_generation'],
            'original_prepared_sha256':sha(directory/'prepared.json'),'stop_sha256':sha(directory/'stop.json'),
            'journal_sha256':export['files']['journal.json']['sha256'],'runtime_sha256':status['runtimeSha256'],
            'retransmit':False}


def prepare_stopped_resume(run, directory, observations):
    value=checked_stopped_resume(run,directory,observations)
    evidence={}
    for phase in (directory/'phases').glob('*.completed.json'):
        for name,digest in read(phase)['evidence'].items():
            require(sha(Path(name))==digest,'prior recovery phase evidence changed')
            evidence[name]=digest
    output=directory/'resumption'
    staging=Path(tempfile.mkdtemp(prefix='resumption-prepared.',dir=directory))
    shutil.copytree(observations,staging/'observations')
    preserved={}
    for name,digest in evidence.items():
        relative=Path('prior-evidence')/hashlib.sha256(name.encode()).hexdigest()
        target=staging/relative; target.parent.mkdir(mode=0o700,exist_ok=True)
        shutil.copyfile(name,target)
        require(sha(target)==digest,'copied recovery phase evidence changed')
        preserved[name]={'path':str(output/relative),'sha256':digest}
    value['preserved']=preserved
    shutil.copyfile(directory/'exit.json',staging/'prior-exit.json')
    (staging/'prepared.json').write_text(json.dumps(value,indent=2)+'\n')
    require(not output.exists(),'resumption was concurrently prepared')
    staging.rename(output)
    print(output)


if __name__ == '__main__':
    try:
        if len(sys.argv)==6 and sys.argv[1]=='--check-stopped-broker':
            print(json.dumps(checked_stopped_broker(Path(sys.argv[2]),Path(sys.argv[3]),sys.argv[4],int(sys.argv[5])))); raise SystemExit(0)
        if len(sys.argv) == 5 and sys.argv[1] == '--resume-after-stop':
            prepare_stopped_resume(*map(Path,sys.argv[2:])); raise SystemExit(0)
        if len(sys.argv) == 3 and sys.argv[1] == '--previous':
            print(previous_execution(Path(sys.argv[2])))
            raise SystemExit(0)
        if len(sys.argv) == 3 and sys.argv[1] in ('--check-native', '--check-terminal'):
            check_native(Path(sys.argv[2]), sys.argv[1] == '--check-terminal')
            raise SystemExit(0)
        require(len(sys.argv) == 4, 'usage: recover_application_api.py RUN OBSERVATIONS REQUEST_ID')
        prepare(Path(sys.argv[1]), Path(sys.argv[2]), None if sys.argv[3] == '--readiness' else sys.argv[3])
    except (ValueError, OSError, KeyError) as error:
        raise SystemExit('application API recovery refused: ' + str(error))
