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


def checked_boundary(run, exported, status, manager, enrollment=None, runtime_sha=None):
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
    require(record['phase'] == 'running' and record.get('dispatch_in_flight') is None
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


def prepare(run, observations):
    exported = read(observations / 'controller-export.json')
    manager = dict(line.split('=', 1) for line in (observations / 'manager.txt').read_text().splitlines() if '=' in line)
    output = run / 'continuations/activation-recovery-1'
    existing = output.exists()
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
        require(len(sys.argv) == 3, 'usage: recover_activation.py RUN OBSERVATIONS')
        prepare(Path(sys.argv[1]), Path(sys.argv[2]))
    except (ValueError, OSError, KeyError) as error:
        raise SystemExit('activation recovery refused: ' + str(error))
