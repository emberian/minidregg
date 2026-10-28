#!/usr/bin/env python3
"""Untrusted stopped-activation recovery checks; never edits a Mini journal.

Only the fixed installer and native supervisor perform runtime replacement,
STOP/START and enrollment. A prepared recovery is never automatically retried.
"""
import base64
import hashlib
import json
from pathlib import Path
import shutil
import stat
import sys


def read(path):
    return json.loads(path.read_bytes())


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def require(condition, message):
    if not condition:
        raise ValueError(message)


def binding_sha(value):
    return hashlib.sha256(json.dumps(value, sort_keys=True, separators=(',', ':'),
                                    ensure_ascii=False).encode()).hexdigest()


def checked_boundary(run, exported, status, manager, enrollment=None, runtime_sha=None, old_phase="running"):
    root = run / 'agent-lifetime'
    world = read(run / 'world-identity.json')
    require(read(run / 'exit.json') == {'execution_exit': 1, 'cleanup_exit': 0,
                                      'namespace_preserved': True}, 'not a cleanly stopped failed run')
    enrollment = enrollment or root / 'enrollment-initial'
    request_path = enrollment / 'request.json'
    request = read(request_path)
    identity = sha(request_path)
    require(request.get('protocol') == 'mini-controller-application-enrollment-v1'
            and request.get('mode') == 'application', 'not an application enrollment')
    require('unknown variant `binding-v3`' in (enrollment / 'stderr').read_text(),
            'not the retained lifetime wire refusal')
    require(exported.get('protocol') == 'mini-spk-controller-evidence-v1'
            and exported.get('store') == world['store'], 'controller export differs')
    files = exported['files']
    def raw(name):
        value = base64.b64decode(files[name]['base64'], validate=True)
        require(hashlib.sha256(value).hexdigest() == files[name]['sha256'], 'export digest differs')
        return value
    journal = json.loads(raw('journal.json'))
    require(journal == read(enrollment / 'before.json')
            == read(root / 'controller-final-journal.json'), 'enrollment journal changed')
    require(journal['connection'] == 'soft', 'controller is not softly detached')
    pending = ('pending', 'toolPending', 'providerPending', 'child', 'settlementDue',
               'parentHold', 'toolHold', 'dispatchPending', 'dispatchHold', 'dispatchAttempt',
               'applicationApiAttempt', 'providerHold', 'providerAttempt', 'providerSettlement',
               'foregroundAttempt', 'birthOperation', 'birthPending')
    require(all(key in journal and journal[key] is None for key in pending), 'controller has pending work')
    archive_request = 'application-enrollments/' + identity + '/request.json'
    require({name for name in files if name.startswith('application-enrollments/')} == {archive_request}
            and raw(archive_request) == request_path.read_bytes(),
            'enrollment has a local commit record or another request')
    require(request['expectedBindingSha256'] == binding_sha(journal['binding']), 'old binding differs')
    require(status.get('stopped') is True and status.get('store') == world['store']
            and status.get('controllerConfigSha256') == request['targetConfigSha256']
            and status.get('runtimeSha256') == (runtime_sha or sha(run / 'bin/grain-runtime')), 'stopped controller pins differ')
    require(not journal['binding']['config']['toolTask'].get('allowedApplicationLifetimeRoutes'),
            'controller already has a lifetime route')
    start = read(run / 'world/evidence/start-a.stdout')
    require(start.get('protocol') == 'mini-spk-grain-start-v1' and start.get('app') == '9101'
            and start.get('generation', '').isdecimal(), 'original START differs')
    state = Path(read(run / 'world/evidence/profile-result.json')['stateRoot'])
    record = read(state / 'apps/9101' / ('g' + start['generation']) / 'record.json')
    require(record['phase'] == old_phase and record.get('dispatch_in_flight') is None
            and record['identity']['unit'] == start['unit']
            and record['identity']['generation'] == int(start['generation']), 'old app lifecycle differs')
    require(manager.get('Id') == start['unit'] and manager.get('LoadState') == 'loaded'
            and manager.get('ActiveState') == 'inactive' and manager.get('SubState') == 'dead'
            and manager.get('MainPID') == '0' and manager.get('InvocationID') == ''
            and manager.get('Job') in ('', '0'), 'old incarnation is not stopped')
    require(not list((state / 'apps/9201').glob('g[0-9]*')), 'second app already started')
    require(not any((run / path).exists() for path in ('browser', 'agent-lifetime/probe',
                'agent-lifetime/controller-active-initial.json', 'world/evidence/post-a1.stdout')),
            'later qualification work already exists')
    issued = read(root / 'issued-grant.json')
    require(issued.get('protocol') == 'mini-oracle-issued-agent-grant-v1'
            and issued['sessionToolResultSha256'] == sha(root / 'session-birth.result.json')
            and (root / 'session-birth.result.json').read_bytes()
                == (root / 'session-birth.retained-result.json').read_bytes()
            and read(root / 'session-birth.result.json').get('isError') is False
            and int(issued['grantReceipt']['acceptedCount']) < int(start['completion']['completionReceipt']['acceptedCount']),
            'admitted session/grant/START evidence differs')
    return {'store': world['store'], 'old_generation': start['generation'], 'old_unit': start['unit'], 'old_record': record,
            'request_sha256': identity, 'journal_sha256': files['journal.json']['sha256'],
            'old_binding_sha256': request['expectedBindingSha256'],
            'grant_receipt': issued['grantReceipt'], 'start_receipt': start['completion']['completionReceipt'],
            'permits_same_generation_relaunch': False, 'permits_enrollment_replay': False}


def latest_start(run):
    paths = [run / 'world/evidence/start-a.stdout',
             *(run / 'continuations').glob('*/successor-start.json')]
    values = [(int(read(p)['generation']), p) for p in paths if p.is_file()]
    require(values and len({n for n, _ in values}) == len(values), 'ambiguous admitted START lineage')
    return max(values)[1]


def checked_read_only_activation(run, observations):
    """The first read of activation failed before any session or route mutation."""
    from recover_application_api import exported
    start_path = latest_start(run)
    previous = start_path.parent
    start = read(start_path); generation = start['generation']
    root = run / 'agent-lifetime'; attempt = root / ('native-activate-' + generation)
    require(read(previous / 'exit.json') == {'execution_exit':1,'cleanup_exit':0,'namespace_preserved':True},
            'activation predecessor did not stop cleanly')
    require(start['protocol']=='mini-spk-grain-start-v1' and start['app']=='9101'
            and start['completion']['completionReceipt']['eventId'], 'admitted START absent')
    require({p.name for p in attempt.iterdir()} == {
        'current-start-before-enrollment.stdout','current-start-before-enrollment.stderr',
        'session-before-enrollment','session-before-enrollment-intent.json',
        'session-before-enrollment.stdout','session-before-enrollment.stderr'},
        'activation progressed beyond its first read')
    query = attempt / 'session-before-enrollment'
    require({p.name for p in query.iterdir()} == {'attempt.json','intent.json','config.json'},
            'read-only query may have signed or received a response')
    a = read(root / 'allocation.json')['agents'][0]
    intent = read(query / 'intent.json')
    require(intent == read(attempt / 'session-before-enrollment-intent.json')
        and intent == {'subject':a['controller']['subject'],'nonce':intent['nonce'],
        'purpose':{'type':'query','kind':'object','target':a['session'],'view':'resource'},
        'grants':[{'kind':'object','target':a['session'],'capability':a['plannedCaps']['sessionOwner']}]},
        'failed activation is not the exact read-only session query')
    call=read(query/'attempt.json')
    require(call['operation']=='query' and call['config']==str(query/'config.json')
        and call['host']==str(run/'bin/minidregg-host')
        and call['socket']==str(run/'world/sock/participant/host.sock'), 'query tool pins differ')
    require((attempt/'session-before-enrollment.stdout').read_bytes()==b''
        and 'resident codec Host failed to start' in (attempt/'session-before-enrollment.stderr').read_text(),
        'not a definite pre-query codec startup refusal')
    require(not any((root/name).exists() for name in ('enrollment-initial','controller-active-initial.json','probe'))
        and not (run/'browser').exists(), 'later enrollment or probe exists')
    status=read(observations/'controller-status.json'); export=read(observations/'controller-export.json')
    world=read(run/'world-identity.json')
    require(export['protocol']=='mini-spk-controller-evidence-v1' and export['store']==world['store'], 'export identity differs')
    journal=json.loads(exported(export,'journal.json'))
    before_candidates=[previous/'terminal-journal.json',
        previous/'resumption/controller-journal.json',
        *(previous/'resumption/retries').glob('*/controller-journal.json'),
        previous/'observations/controller-journal.json']
    require(any(p.is_file() and read(p)==journal for p in before_candidates)
        and journal==read(root/'controller-final-journal.json'), 'controller changed during failed activation')
    require(journal['connection']=='detached' and all(journal.get(k) is None for k in (
        'foregroundAttempt','applicationApiAttempt','parentHold','dispatchAttempt','dispatchPending',
        'dispatchHold','toolPending','toolHold','pending','child','birthPending','birthOperation',
        'providerPending','providerHold','providerAttempt','settlementDue','workspaceAttempt','roomAttempt','workspaceBirth'))
        and not journal.get('unresolvedExternal'), 'controller has retained custody')
    require(status['store']==world['store'] and status['stopped'] is True
        and status['runtimeSha256']==(observations/'runtime.sha256').read_text().strip(), 'stopped runtime pins differ')
    config_candidates=[previous/'resumption/controller-status.json',
        *(previous/'resumption/retries').glob('*/controller-status.json'),previous/'observations/controller-status.json']
    require(any(p.is_file() and p.stat().st_size > 0 and read(p)['controllerConfigSha256']==status['controllerConfigSha256']
        for p in config_candidates), 'stopped controller config changed')
    state=Path(read(run/'world/evidence/profile-result.json')['stateRoot'])
    app=state/'apps/9101'/('g'+generation); record=read(app/'record.json')
    manager=dict(line.split('=',1) for line in (observations/'manager.txt').read_text().splitlines() if '=' in line)
    require(record['phase']=='running' and record.get('dispatch_in_flight') is None
        and record['identity']['unit']==start['unit'] and record['identity']['generation']==int(generation)
        and manager['Id']==start['unit'] and manager['MainPID']=='0'
        and manager['ActiveState'] in ('inactive','failed') and manager['Job'] in ('','0'), 'app is not physically stopped')
    native=app/('agent-'+read(root/'registered-agent-route.json')['registration']['name']+'-attempts')
    require(not native.exists() or not list(native.iterdir()), 'application has API delivery evidence')
    require(not list((state/'apps/9201').glob('g[0-9]*')), 'browser app already started')
    return {'kind':'activation-read-only-refusal','store':world['store'],'old_generation':generation,
        'old_unit':start['unit'],'old_record':record,'previous_execution':str(previous),
        'start_path':str(start_path),'start_sha256':sha(start_path),'journal_sha256':export['files']['journal.json']['sha256'],
        'runtime_sha256':status['runtimeSha256'],'controller_config_sha256':status['controllerConfigSha256'],
        'failed_query':str(query),'failed_query_intent_sha256':sha(query/'intent.json'),
        'permits_same_generation_relaunch':False,'permits_enrollment_replay':False}


def prepare_read_only_activation(run, observations):
    boundary=checked_read_only_activation(run,observations)
    for line in (run/'input-sha256.txt').read_text().splitlines():
        digest,name=line.split(None,1)
        require(sha(Path(name))==digest,'retained input changed')
    output=run/'continuations'/('activation-read-'+boundary['old_generation'])
    require(not output.exists(), 'activation continuation already prepared; inspect retained phase')
    output.mkdir(mode=0o700); (output/'phases').mkdir(mode=0o700)
    shutil.copytree(observations,output/'observations')
    exported=read(observations/'controller-export.json')['files']['journal.json']
    (output/'observations/controller-journal.json').write_bytes(base64.b64decode(exported['base64'],validate=True))
    prior=output/'prior'; prior.mkdir(mode=0o700)
    preserved={}; archived={}
    for path in [Path(boundary['previous_execution'])/'exit.json',run/'agent-lifetime/controller-final-journal.json',
                 run/'agent-lifetime/issued-grant.json',run/'agent-lifetime/registered-agent-route.json']:
        target=prior/(str(len(preserved))+'-'+path.name); shutil.copy2(path,target)
        preserved[str(path)]={'path':str(target),'sha256':sha(target)}
    for path in sorted((run/'agent-lifetime').glob('*initial*')):
        require(path.is_file(),'unexpected initial activation output directory')
        target=prior/path.name; shutil.copy2(path,target)
        archived[str(path)]={'path':str(target),'sha256':sha(target)}
    failed=run/'agent-lifetime'/('native-activate-'+boundary['old_generation'])
    shutil.copytree(failed,prior/failed.name)
    value={'schema':'mini-oracle-activation-read-recovery-v1','boundary':boundary,'automatic_retry':False,
        'preserved':preserved,'archived':archived,
        'failed_attempt_sha256':{str(p.relative_to(failed)):sha(p) for p in failed.rglob('*') if p.is_file()}}
    (output/'prepared.json').write_text(json.dumps(value,indent=2)+'\n')
    print(output)


def prepare_successor(run, observations, predecessor, check_only=False):
    """A completed native STOP and a never-admitted successor; no STOP replay."""
    failure = predecessor / 'socket-failure'
    retained = read(failure / 'boundary.json')
    original = read(predecessor / 'prepared.json')['boundary']
    manager = dict(line.split('=', 1) for line in (observations / 'manager.txt').read_text().splitlines() if '=' in line)
    boundary = checked_boundary(run, read(observations / 'controller-export.json'),
        read(observations / 'controller-status.json'), manager, predecessor / 'prior/enrollment-initial',
        sha(predecessor / 'bin/grain-runtime'), old_phase='stopped')
    require(retained['store'] == original['store'] == boundary['store']
            and retained['old_generation'] == original['old_generation'] == boundary['old_generation']
            and boundary['old_record']['identity'] == original['old_record']['identity']
            and boundary['old_record']['invocation_id'] == original['old_record']['invocation_id']
            and boundary['old_record'] == retained['old_record']
            and boundary['grant_receipt'] == original['grant_receipt'], 'native stopped predecessor differs')
    require(read(predecessor / 'exit.json') == {'execution_exit': 1, 'cleanup_exit': 0,
                                               'namespace_preserved': True}, 'successor cleanup differs')
    require((predecessor / 'supervise.json').read_bytes() == b''
            and 'before START completion' in (predecessor / 'supervise.stderr').read_text()
            and 'agent socket preflight pin refused' in (failure / 'g4-unit.log').read_text(),
            'not the recorded successor preflight failure')
    phases = {path.name for path in (predecessor / 'phases').iterdir()}
    require(phases == {name + '.' + state + '.json' for name in
        ('runtime-upgrade', 'public-listener', 'services') for state in ('started', 'completed')}
        | {'supervise.started.json'}, 'predecessor recovery advanced')
    state = Path(read(run / 'world/evidence/profile-result.json')['stateRoot'])
    generation = retained['successor_generation']
    require(generation.isdecimal() and int(generation) > int(boundary['old_generation']), 'successor generation differs')
    successor = state / 'apps/9101' / ('g' + generation)
    effect_files = ('record.json', 'start-admitted-v3.json', 'start-completed-v3.json', 'begin-attempt',
                    'lifecycle-begin-v3-active.json', 'begin-attempt-retry-v4', 'lifecycle-begin-retry-v4-active.json')
    require(all(not (successor / name).exists() for name in effect_files), 'successor may have begun START')
    require(sha(successor / 'resident.json') == retained['g4_config_sha256'], 'successor configuration changed')
    manager = dict(line.split('=', 1) for line in (observations / 'manager-successor.txt').read_text().splitlines() if '=' in line)
    require(manager.get('Id') == 'mini-spk-s' + boundary['store'] + '-a9101-g' + generation + '.service'
            and manager.get('ActiveState') in ('failed', 'inactive') and manager.get('MainPID') == '0'
            and manager.get('Job') in ('', '0'), 'successor process may be live')
    for path in (failure / 'stop-completion').rglob('*'):
        if path.is_file():
            source = state / 'apps/9101' / ('g' + boundary['old_generation']) / 'stop-completion' / path.relative_to(failure / 'stop-completion')
            require(sha(source) == sha(path), 'native STOP evidence changed')
    receipts = list((failure / 'stop-completion').rglob('receipt-anchor.json'))
    require(bool(receipts) and all(read(path).get('eventId') and read(path).get('worldRoot') for path in receipts),
            'native STOP completion absent')
    for path, digest in read(failure / 'native-store-pins.json').items():
        require(sha(Path(path)) == digest, 'Store changed after successor refusal')
    for line in (run / 'input-sha256.txt').read_text().splitlines():
        digest, path = line.split(None, 1)
        require(sha(Path(path)) == digest, 'original input changed')
    socket = Path(retained['socket']['path']); metadata = socket.lstat()
    require(stat.S_ISSOCK(metadata.st_mode) and (metadata.st_dev, metadata.st_ino, metadata.st_uid)
            == tuple(retained['socket'][key] for key in ('device', 'inode', 'uid')), 'retained socket identity changed')
    require(read(successor / 'resident.json')['agents'][0]['socket'] == str(socket), 'successor socket differs')
    if check_only:
        return boundary
    output = run / 'continuations/activation-successor-1'
    output.mkdir(mode=0o700)
    (output / 'phases').mkdir(mode=0o700)
    shutil.copytree(observations, output / 'observations')
    shutil.copytree(failure, output / 'prior')
    value = {'schema': 'mini-oracle-activation-successor-v1', 'predecessor': str(predecessor),
             'boundary': boundary, 'successor_generation': generation, 'socket': retained['socket'],
             'controller_uid': read(successor / 'resident.json')['agents'][0]['controllerUid'],
             'automatic_retry': False, 'requires_native_socket_reclaim': True,
             'prior_sha256': {str(p.relative_to(output / 'prior')): sha(p)
                              for p in (output / 'prior').rglob('*') if p.is_file()}}
    (output / 'prepared.json').write_text(json.dumps(value, indent=2) + '\n')
    print(output)


def prepare(run, observations):
    exported = read(observations / 'controller-export.json')
    manager = dict(line.split('=', 1) for line in (observations / 'manager.txt').read_text().splitlines() if '=' in line)
    output = run / 'continuations/activation-recovery-1'
    existing = output.exists()
    if (output / 'socket-failure/boundary.json').exists():
        prepare_successor(run, observations, output)
        return
    enrollment = output / 'prior/enrollment-initial' if existing else None
    upgraded = existing and (output / 'phases/runtime-upgrade.completed.json').exists()
    runtime_sha = sha(output / 'bin/grain-runtime') if upgraded else None
    boundary = checked_boundary(run, exported, read(observations / 'controller-status.json'), manager,
                                enrollment, runtime_sha)
    # Check every retained input pin before moving any evidence. The dataset's
    # physical custody is independently rechecked by the native successor START.
    for line in (run / 'input-sha256.txt').read_text().splitlines():
        expected, name = line.split(None, 1)
        require(Path(name).is_file() and sha(Path(name)) == expected, 'retained input changed: ' + name)
    config = read(run / 'world/store/base/workroom/deployment/pinned-config.json')
    store = Path(config['storageRoot'])
    wal = store / 'forward-link.sqlite3-wal'
    require(not wal.exists() or wal.stat().st_size == 0, 'stopped Store has a nonempty WAL')
    if existing:
        prepared = read(output / 'prepared.json')
        require(prepared['boundary'] == boundary, 'prepared boundary changed')
        phases = {p.name for p in (output / 'phases').glob('*')}
        if upgraded:
            require(phases == {'runtime-upgrade.started.json', 'runtime-upgrade.completed.json',
                               'services.started.json'}, 'a lifecycle effect may have started')
            upgrade = read(output / 'runtime-upgrade.json')
            completed = read(output / 'phases/runtime-upgrade.completed.json')
            require(upgrade['store'] == boundary['store']
                    and upgrade['previousRuntimeSha256'] == sha(run / 'bin/grain-runtime')
                    and upgrade['runtimeSha256'] == runtime_sha
                    and completed['started_sha256'] == sha(output / 'phases/runtime-upgrade.started.json')
                    and completed['evidence'] == {str(output / 'runtime-upgrade.json'): sha(output / 'runtime-upgrade.json')},
                    'completed runtime upgrade differs')
            require(not any((output / name).exists() for name in
                            ('supervise.json', 'successor-start.json', 'public-listener.json')),
                    'later recovery work exists')
        else:
            require(not phases and not (output / 'runtime-upgrade.json').exists(), 'an effect may have started')
        require(read(output / 'exit.json') == {'execution_exit': 1, 'cleanup_exit': 0,
                                               'namespace_preserved': True}, 'prepared cleanup differs')
        for entry in [*prepared['snapshots'].values(), *prepared['archived'].values()]:
            require(sha(Path(entry['path'])) == entry['sha256'], 'preserved evidence changed')
        for path in (store / 'forward-link.sqlite3', Path(str(store) + '.head-anchor')):
            require(sha(path) == prepared['snapshots'][str(path)]['sha256'], 'Store changed after preparation')
        attempts = output / 'pre-effect-attempts'
        attempts.mkdir(mode=0o700, exist_ok=True)
        attempt = attempts / str(len(list(attempts.iterdir())) + 1)
        attempt.mkdir(mode=0o700)
        for name in ('exit.json', 'recovery-input-sha256.txt'):
            if (output / name).exists():
                shutil.copy2(output / name, attempt / name)
        shutil.copytree(observations, attempt / 'observations')
        if upgraded:
            (output / 'phases/services.started.json').rename(attempt / 'services.started.json')
        (output / 'phases').mkdir(mode=0o700, exist_ok=True)
        print(output)
        return
    output.parent.mkdir(mode=0o700, exist_ok=True)
    output.mkdir(mode=0o700)
    (output / 'phases').mkdir(mode=0o700)
    prior = output / 'prior'; prior.mkdir(mode=0o700)
    snapshots = {}
    originals = [run / 'exit.json', run / 'agent-lifetime/controller-final-journal.json',
                 run / 'agent-lifetime/issued-grant.json', run / 'world/evidence/start-a.stdout']
    originals += [store / 'forward-link.sqlite3', Path(str(store) + '.head-anchor')]
    for index, path in enumerate(originals):
        target = prior / (str(index) + '-' + path.name)
        shutil.copy2(path, target)
        snapshots[str(path)] = {'path': str(target), 'sha256': sha(target)}
    shutil.copytree(observations, output / 'observations')
    archived = {}
    for path in sorted((run / 'agent-lifetime').glob('*initial*')):
        target = prior / path.name
        entries = [path] if path.is_file() else sorted(p for p in path.rglob('*') if p.is_file())
        archived.update({str(p): {'path': str(target if path.is_file() else target / p.relative_to(path)),
                                 'sha256': sha(p)} for p in entries})
        path.rename(target)
    value = {'schema': 'mini-oracle-activation-recovery-v1', 'boundary': boundary,
             'snapshots': snapshots, 'archived': archived, 'automatic_retry': False}
    (output / 'prepared.json').write_text(json.dumps(value, indent=2) + '\n')
    print(output)


if __name__ == '__main__':
    try:
        if len(sys.argv)==3 and sys.argv[1]=='--latest-start':
            print(latest_start(Path(sys.argv[2]))); raise SystemExit(0)
        if len(sys.argv)==4 and sys.argv[1]=='--read-only':
            prepare_read_only_activation(Path(sys.argv[2]),Path(sys.argv[3])); raise SystemExit(0)
        require(len(sys.argv) == 3, 'usage: recover_activation.py RUN OBSERVATIONS')
        prepare(Path(sys.argv[1]), Path(sys.argv[2]))
    except (ValueError, OSError, KeyError) as error:
        raise SystemExit('activation recovery refused: ' + str(error))
