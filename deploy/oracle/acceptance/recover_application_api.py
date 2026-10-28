#!/usr/bin/env python3
"""Untrusted qualification checks around native recovery of one retained API call.

The native controller proves non-dispatch and settles its own foreground/hold.
This harness preserves evidence; it never edits a native journal or Store.
"""
import base64
import hashlib
import json
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


def checked_boundary(run, observations, request_id):
    root = run / 'agent-lifetime'
    previous = run / 'continuations/activation-successor-1'
    require(read(previous / 'exit.json') == {'execution_exit': 2, 'cleanup_exit': 0,
                                           'namespace_preserved': True}, 'not stopped after first API failure')
    require((root / 'probe/discover-core-query.request-id').read_text().strip() == request_id,
            'foreground request ID differs')
    export = read(observations / 'controller-export.json')
    world = read(run / 'world-identity.json')
    require(export['protocol'] == 'mini-spk-controller-evidence-v1' and export['store'] == world['store'],
            'controller export identity differs')
    journal = json.loads(exported(export, 'journal.json'))
    require(journal == read(root / 'controller-final-journal.json'), 'retained controller journal differs')
    foreground = journal['foregroundAttempt']; api = journal['applicationApiAttempt']
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
            and status['runtimeSha256'] == sha(run / 'continuations/activation-recovery-1/bin/grain-runtime')
            and status['controllerConfigSha256'] == sha(root / 'controller-active-initial.json'),
            'stopped controller pins differ')
    start = read(previous / 'successor-start.json')
    state = Path(read(run / 'world/evidence/profile-result.json')['stateRoot'])
    app = state / 'apps/9101' / ('g' + start['generation'])
    record = read(app / 'record.json')
    manager = dict(line.split('=', 1) for line in (observations / 'manager.txt').read_text().splitlines() if '=' in line)
    require(record['phase'] == 'running' and record['identity']['unit'] == start['unit']
            and record['invocation_id'] == api['hostInvocation']
            and manager['Id'] == start['unit'] and manager['MainPID'] == '0'
            and manager['ActiveState'] in ('inactive', 'failed') and manager['Job'] in ('', '0'),
            'retained app incarnation is not physically stopped')
    native = app / 'agent-oracle-agent-v1-attempts'
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
    return {'store': world['store'], 'request_id': request_id, 'foreground': foreground, 'api': api,
            'parent_hold': hold, 'old_generation': start['generation'], 'old_record': record,
            'journal_sha256': export['files']['journal.json']['sha256'],
            'grant_receipt': read(root / 'issued-grant.json')['grantReceipt'],
            'runtime_sha256': status['runtimeSha256'],
            'dispatch_task': journal['binding']['config']['dispatchTask']['task'], 'retransmit': False}


def prepare(run, observations, request_id):
    boundary = checked_boundary(run, observations, request_id)
    output = run / 'continuations/application-api-recovery-1'
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
    for directory in ('activation-recovery-1', 'activation-successor-1'):
        for phase in (run / 'continuations' / directory / 'phases').glob('*.completed.json'):
            for name, digest in read(phase)['evidence'].items():
                source = Path(name)
                if source.is_file() and sha(source) == digest and name not in preserved:
                    target = prior / (str(len(preserved)) + '-' + source.name)
                    shutil.copy2(source, target)
                    preserved[name] = {'path': str(target), 'sha256': digest}
    archived = {}
    for path in [*(run / 'agent-lifetime').glob('*initial*'),
                 run / 'agent-lifetime/probe', run / 'agent-lifetime/probe.stderr',
                 run / 'agent-lifetime/probe.stdout']:
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


if __name__ == '__main__':
    try:
        if len(sys.argv) == 3 and sys.argv[1] in ('--check-native', '--check-terminal'):
            check_native(Path(sys.argv[2]), sys.argv[1] == '--check-terminal')
            raise SystemExit(0)
        require(len(sys.argv) == 4, 'usage: recover_application_api.py RUN OBSERVATIONS REQUEST_ID')
        prepare(Path(sys.argv[1]), Path(sys.argv[2]), sys.argv[3])
    except (ValueError, OSError, KeyError) as error:
        raise SystemExit('application API recovery refused: ' + str(error))
