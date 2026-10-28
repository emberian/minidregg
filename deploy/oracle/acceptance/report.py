#!/usr/bin/env python3
"""Untrusted acceptance assertions, not a Mini semantic or admission engine.

Reads retained native receipts, Linux mount observations and HTTP reply bytes.
A passing report is emitted only when every assertion passes. It does not score
Oracle's specialist panels or assert that returned answers are formally proved.
"""
import hashlib
import json
import math
import re
from pathlib import Path
import sys


def read(path):
    return json.loads(path.read_bytes())


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def mount_rows(directory):
    result = []
    for path in sorted(directory.glob('*.txt')):
        for line in path.read_text().splitlines():
            fields = line.split()
            if len(fields) >= 10 and fields[4] in ('/opt/oracle-data', '/var'):
                result.append({'pid': path.stem, 'device': fields[2],
                               'root': fields[3], 'target': fields[4],
                               'options': fields[5].split(',')})
    return result


def consent_evidence(run, require):
    directory = run / 'agent-lifetime'
    world = read(run / 'world-identity.json')
    created = read(directory / 'controller-create.json')
    staged = read(directory / 'controller-stage-receipt.json')
    base = world['root'] + '/controller'
    expected = {
        'providerSha256': sha(run / 'bin/minidregg-client-consent'),
        'transportSha256': sha(run / 'bin/mini'),
        'configSha256': sha(run / 'world/store/base/workroom/deployment/pinned-config.json'),
        'socket': base + '/home/consent/peer.sock',
        'socketUnit': f"mini-spk-controller-consent-{world['store']}.socket",
        'serviceUnit': f"mini-spk-controller-consent-{world['store']}.service",
        'serviceUid': created['operatorUid'], 'controllerUid': created['controllerUid'],
        'activationPeerUid': 0, 'provider': base + '/bin/minidregg-client-consent',
        'config': base + '/consent/config.json', 'anchors': base + '/consent/anchors',
    }
    require('controller_consent_v2_distinct_identity',
            created.get('protocol') == staged.get('protocol') == 'mini-spk-controller-v2'
            and created.get('store') == staged.get('store') == world['store']
            and type(created['operatorUid']) is int and created['operatorUid'] > 0
            and type(created['controllerUid']) is int and created['controllerUid'] > 0
            and created['operatorUid'] != created['controllerUid']
            and created.get('consentSocket') == expected['socket']
            and created.get('consentPeerUid') == 0)
    if (directory/'consent-memory.json').exists():
        memory=read(directory/'consent-memory.json')
        props=lambda suffix:dict(line.split('=',1) for line in (directory/('consent-memory-'+suffix+'.properties')).read_text().splitlines() if '=' in line)
        before,after=props('before'),props('after')
        require('initial_consent_operator_budget',memory['store']==world['store']
            and memory['nativeOperationSubmitted'] is False
            and before['Id']==after['Id']==expected['serviceUnit']
            and before['MainPID']==after['MainPID']=='0'
            and before['ActiveState'] in ('inactive','failed') and after['ActiveState'] in ('inactive','failed')
            and before['MemorySwapMax']==after['MemorySwapMax']
            and int(after['MemoryMax'])==memory['memoryMiB']*1024*1024)
    session = run / 'continuations/session-refusal-1'
    repair = None
    if session.exists():
        repair = read(session / 'consent-storage.json')
        require('controller_consent_original_stage_preserved', staged.get('consent') == expected)
        require('controller_consent_explicit_storage_upgrade', repair.get('store') == world['store']
                and repair.get('storageUpgrade') == base + '/consent-storage-upgrade.json'
                and all(re.fullmatch('[0-9a-f]{64}', repair.get(key, ''))
                        for key in ('previousStageSha256', 'stageSha256')))
        installed = repair['consent']
    else:
        installed = staged.get('consent', {})
    storage = installed.get('storage', {})
    store_root = Path(read(run / 'world/store/base/workroom/deployment/pinned-config.json')['storageRoot'])
    require('controller_consent_exact_storage_parent',
            storage.get('protocol') == 'mini-spk-consent-storage-v1'
            and storage.get('root') == str(store_root)
            and storage.get('writableParent') == str(store_root.parent)
            and storage.get('replaceableAnchor') == str(store_root) + '.head-anchor')
    for key, path in (('database', store_root / 'forward-link.sqlite3'),
                      ('lock', Path(str(store_root) + '.head-anchor.lock'))):
        pin = storage.get(key, {})
        require('controller_consent_storage_' + key, pin.get('path') == str(path)
                and pin.get('uid') == created['operatorUid'] and pin.get('mode') == 0o600
                and type(pin.get('dev')) is int and type(pin.get('ino')) is int and pin['ino'] > 0)
    directories = storage.get('directories', [])
    require('controller_consent_storage_ancestors',
            [item.get('path') for item in directories] == [str(path) for path in reversed((store_root, *store_root.parents))]
            and all(item.get('uid') in (0, created['operatorUid']) and type(item.get('mode')) is int
                    and item['mode'] & 0o022 == 0 and type(item.get('ino')) is int and item['ino'] > 0
                    for item in directories))
    expected['storage'] = storage
    require('controller_consent_exact_stage_pins', installed == expected)
    require('controller_consent_exact_config_bytes',
            sha(directory / 'controller-stage/host-config.json') == expected['configSha256'])
    starts = {}
    checkpoint_starts = list((run / 'continuations').glob('checkpoint-*/controller-bootstrap-start.json'))
    require('at_most_one_checkpoint_bootstrap', len(checkpoint_starts) <= 1)
    bootstrap = checkpoint_starts[0] if checkpoint_starts else (session / 'controller-bootstrap-start.json' if session.exists() else 'controller-bootstrap-start.json')
    for label, filename in (('bootstrap', bootstrap),
                            ('initial', 'controller-start-initial.json'),
                            ('restart', 'controller-start-restart.json')):
        receipt = read(directory / filename)
        value = receipt.get('consent', {})
        require(f'consent_{label}_exact_pins',
                receipt.get('action') == 'start' and receipt.get('store') == world['store']
                and all(value.get(key) == item for key, item in expected.items())
                and expected['serviceUnit'] in receipt.get('units', [])
                and expected['socketUnit'] in receipt.get('units', []))
        require(f'consent_{label}_observed_readiness_only',
                value.get('readiness') == 'process-and-socket-only'
                and value.get('independentAdmissionObserved') is False
                and type(value.get('mainPid')) is int and value['mainPid'] > 0
                and type(value.get('processStartTicks')) is int and value['processStartTicks'] > 0
                and re.fullmatch('[0-9a-f]{32}', value.get('invocationId', '')) is not None
                and value.get('socketUid') == created['controllerUid'] and value.get('socketMode') == '0600'
                and all(isinstance(value.get(key), list) and len(value[key]) == 2
                        and all(type(n) is int and n >= 0 for n in value[key]) and value[key][1] > 0
                        for key in ('socketIdentity', 'processExecutableIdentity')))
        starts[label] = value
    require('consent_restarts_have_distinct_invocations',
            len({value['invocationId'] for value in starts.values()}) == 3)
    require('consent_restarts_keep_transport_inode',
            all(value['processExecutableIdentity'] == starts['bootstrap']['processExecutableIdentity']
                for value in starts.values()))
    observations = {}
    for stage, start in (('probe', 'initial'), ('probe-after-restart', 'restart')):
        value = read(directory / f'consent-memory-after-{stage}.json')
        properties = value.get('properties', {})
        require(f'consent_{stage}_resources_match_active_invocation',
                value.get('schema') == 'mini-oracle-consent-resources-v1'
                and value.get('unit') == expected['serviceUnit'] and value.get('observation_exit') == 0
                and properties.get('ActiveState') == 'active'
                and properties.get('MainPID') == str(starts[start]['mainPid'])
                and properties.get('InvocationID') == starts[start]['invocationId'])
        def bytes_or_unavailable(key):
            raw = properties.get(key, '')
            return int(raw) if raw.isascii() and raw.isdecimal() and int(raw) < 2**64 - 1 else None
        observations[stage] = {'observation': value,
                               'memory_peak_bytes': bytes_or_unavailable('MemoryPeak'),
                               'memory_limit_bytes': bytes_or_unavailable('MemoryMax')}
    return {'stage': expected, 'storage_repair': repair, 'starts': starts, 'resources': observations,
            'scope': 'Startup receipts show process/socket readiness only. Actual agent operations below '
                     'exercise independent consent. Memory observations cover this run, not arbitrary Store sizes.'}


def controller_continuation(run, require):
    directory = run / 'continuations/controller-create-1'
    created = read(run / 'agent-lifetime/controller-create.json')
    if not directory.exists():
        require('controller_created_without_unrecorded_recovery', not created.get('resumedPendingCreation', False))
        return None
    value = read(directory / 'prepared.json')
    world = read(run / 'world-identity.json')
    require('controller_continuation_exact_boundary',
            value.get('schema') == 'mini-oracle-controller-continuation-v1'
            and value.get('boundary') == 'after-definite-share-before-any-START'
            and value.get('run') == str(run) and value.get('store') == world['store']
            and value.get('repeated_phases') == []
            and value.get('controller_recovery_verb') == 'controller-resume-create'
            and value.get('prior_exit') == {'execution_exit': 1, 'cleanup_exit': 0, 'namespace_preserved': True}
            and created.get('resumedPendingCreation') is True
            and created.get('controllerUid') == value.get('controller_uid'))
    for name, digest in value['prior_files'].items():
        relative = Path(name)
        require('continuation_snapshot_' + name,
                not relative.is_absolute() and '..' not in relative.parts
                and sha(directory / 'prior' / relative) == digest)
    for original, archived in value['archived_original_paths'].items():
        require('continuation_original_location_' + original,
                Path(original).is_relative_to(run) and Path(archived['path']).is_relative_to(directory / 'prior')
                and sha(Path(archived['path'])) == archived['sha256'])
    for original, archived in value['store_snapshot'].items():
        require('continuation_stopped_source_snapshot_' + original,
                Path(archived).is_relative_to(directory / 'prior')
                and sha(Path(archived)) == value['store_before'][original])
    for phase in ('store', 'birth-a', 'install-a', 'birth-b', 'install-b', 'share-a'):
        for suffix in ('cmd', 'stdout', 'stderr', 'exit', 'seconds'):
            name = f'world/evidence/{phase}.{suffix}'
            require(f'continuation_preserves_{phase}_{suffix}', sha(run / name) == value['prior_files'][name])
    for app in ('9101', '9201'):
        status = read(directory / f'status-{app}.json')
        require(f'continuation_{app}_installed_before_first_START',
                status.get('app') == app and status.get('installCompleted') is True and status.get('runs') == [])
    for line in (directory / 'recovery-input-sha256.txt').read_text().splitlines():
        digest, path = line.split(None, 1)
        require('continuation_source_' + path, Path(path).is_absolute() and sha(Path(path)) == digest)
    return {'prepared': value, 'prepared_sha256': sha(directory / 'prepared.json'),
            'recovery_input_manifest_sha256': sha(directory / 'recovery-input-sha256.txt'),
            'prior_exit_path': str(directory / 'prior/exit.json'),
            'continuation_exit_path': str(directory / 'exit.json'),
            'scope': 'Preserved first failure; continued only the pending account creation and later phases. '
                     'No repeated genesis, installation, publication or application share.'}


def controller_enrollments(run, require):
    root = run / 'agent-lifetime'
    session = run / 'continuations/session-refusal-1'
    target = (root / 'native-prepare-bootstrap-dispatch/controller-update/controller.json'
              if session.exists() else root / 'controller-stage/controller.json')
    policy = read(root / 'native-prepare-worker-policy/worker-policy.json')
    config = read(target)
    require('controller_initial_worker_policy_exact',
            policy.get('protocol') == 'mini-oracle-bootstrap-worker-policy-v1'
            and policy.get('controllerConfigSha256') == sha(target)
            and policy.get('workers') == [config[key]['subject'] for key in ('toolTask', 'dispatchTask')]
            and policy.get('workerGeneration') == '1'
            and policy.get('receipt', {}).get('eventId')
            and Path(policy['attempt']).is_relative_to(root / 'native-prepare-worker-policy'))
    before, after = read(Path(policy['before']) / 'view.json'), read(Path(policy['after']) / 'view.json')
    require('controller_owner_policy_extends_initial_version',
            before['policyId'] == after['policyId'] == config['task']
            and before['version'] == '0' and after['version'] == '1'
            and after['previous'] == before['address'])
    outcome = read(Path(policy['attempt']) / 'outcome.json')
    require('controller_owner_policy_matches_retained_native_outcome',
            outcome.get('type') == 'confirmed' and outcome.get('confirmation') in ('installed', 'replayed')
            and {key: outcome.get(key) for key in ('transactionId', 'eventId', 'acceptedCount', 'worldRoot')} == policy['receipt'])
    enrolled = {}
    for label in (['bootstrap-dispatch'] if session.exists() else []) + ['initial', 'restart']:
        directory = root / ('enrollment-' + label)
        request, result = read(directory / 'request.json'), read(directory / 'result.json')
        before, after = read(directory / 'before.json'), read(directory / 'after.json')
        digest = lambda value: hashlib.sha256(json.dumps(value, sort_keys=True, separators=(',', ':'), ensure_ascii=False).encode()).hexdigest()
        target_path = target if label == 'bootstrap-dispatch' else root / ('controller-active-' + label + '.json')
        require('controller_' + label + '_native_binding_enrollment',
                request.get('protocol') == result.get('protocol') == 'mini-controller-application-enrollment-v1'
                and request.get('mode') == ('bootstrap-dispatch' if label == 'bootstrap-dispatch' else 'application')
                and request.get('expectedBindingSha256') == digest(before['binding'])
                and request.get('targetConfigSha256') == sha(target_path)
                and result.get('status') == 'enrolled' and result.get('replayed') is False
                and result.get('requestSha256') == sha(directory / 'request.json')
                and result.get('bindingSha256') == digest(after['binding'])
                and before['binding']['configPath'] == after['binding']['configPath']
                and {k:v for k,v in before.items() if k != 'binding'} ==
                    {k:v for k,v in after.items() if k != 'binding'})
        enrolled[label] = {'request': request, 'result': result,
                           'before_sha256': sha(directory / 'before.json'), 'after_sha256': sha(directory / 'after.json')}
    return {'owner_policy': policy, 'native_enrollments': enrolled}


def foreground_recovery(run, require):
    directory = run / 'continuations/foreground-13'
    if not directory.exists():
        return None
    from recover_foreground import prebirth, validate_result
    value = read(directory / 'prepared.json')
    plan = value['plan']
    require('foreground_recovery_same_operation',
            value.get('protocol') == 'mini-oracle-foreground-recovery-prepared-v1'
            and plan.get('run') == str(run) and plan.get('operation_id') == 13
            and plan.get('store') == read(run / 'world-identity.json')['store']
            and value.get('resend') is False and value.get('automatic_retry') is False
            and value.get('acknowledge_before_settlement') is False)
    for name, digest in value['snapshot_files'].items():
        require('foreground_snapshot_' + name, Path(name).name == name and sha(directory / 'prior' / name) == digest)
    for name, digest in value['source_manifest'].items():
        require('foreground_source_' + name, sha(Path(name)) == digest)
    for name, pin in ((k, v) for k, v in plan.items() if isinstance(v, dict) and 'path' in v):
        require('foreground_plan_pin_' + name, sha(Path(pin['path'])) == pin['sha256'])
    from continue_controller import manifest
    qualification = manifest(Path(plan['qualification_manifest']['path']))
    require('foreground_independent_binary_qualification', all(
        qualification.get(plan[k]['path']) == plan[k]['sha256'] for k in ('runtime','public_mini')))
    boundary = prebirth(read(Path(plan['predecessor_export']['path'])), plan['store'], plan['request_id'], 13)
    require('foreground_original_boundary_preserved', boundary == value['boundary']
            and sha(run / 'agent-lifetime/session-birth.result.json') == value['original_result_sha256'])
    recovery = read(directory / 'recovery-result.json')
    retained = read(directory / 'retained-result.json')
    validate_result(plan, recovery, retained, read(directory / 'settled-journal.json'),
                    read(directory / 'settled-export.json'))
    require('foreground_native_result_and_settlement_join',
            sha(directory / 'retained-result.json') == sha(run / 'agent-lifetime/session-birth.retained-result.json'))
    ack = read(run / 'agent-lifetime/session-birth.ack.json')
    require('foreground_ordinary_ack_after_recovery', ack.get('type') == 'tool-acknowledged'
            and ack.get('requestId') == plan['request_id'] and ack.get('isError') is not True)
    phases = {}
    for name in ('runtime-upgrade','public-listener-upgrade','services','controller-start',
                 'exact-foreground-recovery','session-grant'):
        started = directory / 'phases' / (name + '.started.json')
        completed = read(directory / 'phases' / (name + '.completed.json'))
        require('foreground_phase_' + name, completed.get('phase') == name
                and completed.get('state') == 'completed' and completed.get('started_sha256') == sha(started)
                and completed.get('permits_automatic_retry') is False)
        for artifact, digest in completed['evidence'].items():
            require('foreground_phase_artifact_' + artifact, sha(Path(artifact)) == digest)
        phases[name] = completed
    return {'prepared': value, 'receipt': recovery, 'retained_result': retained, 'phases': phases,
            'original_failed_result_sha256': value['original_result_sha256'],
            'scope': 'Same operation and parent reservation recovered; original failure preserved without resend.'}


def session_continuation(run, require, recovered=None):
    directory = run / 'continuations/session-refusal-1'
    if not directory.exists():
        return None
    value = read(directory / 'prepared.json')
    require('session_continuation_definite_boundary',
            value.get('schema') == 'mini-oracle-session-continuation-v1'
            and value.get('run') == str(run) and value.get('store') == read(run / 'world-identity.json')['store']
            and value.get('boundary', {}).get('boundary') == 'definite-pre-tool-session-refusal'
            and value.get('boundary', {}).get('permits_resend') is False
            and value.get('failed_request_acknowledged') is False and value.get('repeated_phases') == [])
    for name, digest in value['prior_files'].items():
        relative = Path(name)
        require('session_archive_' + name, not relative.is_absolute() and '..' not in relative.parts
                and sha(directory / 'prior' / relative) == digest)
    for original, archived in value['archived_original_paths'].items():
        require('session_original_location_' + original,
                Path(original).is_relative_to(run) and Path(archived['path']).is_relative_to(directory / 'prior')
                and sha(Path(archived['path'])) == archived['sha256'])
    for original, archived in value['store_snapshot'].items():
        require('session_stopped_store_' + original,
                Path(archived).is_relative_to(directory / 'prior') and sha(Path(archived)) == value['store_before'][original])
    for line in (directory / 'recovery-input-sha256.txt').read_text().splitlines():
        digest, path = line.split(None, 1)
        require('session_source_' + path, Path(path).is_absolute() and sha(Path(path)) == digest)
    require('session_retained_profile_and_config_pins',
            sha(directory / 'prior/native-profile.json') == value['native_profile_sha256']
            and sha(directory / 'prior/host-config.json') == value['host_config_sha256']
            and sha(run / 'world/store/base/workroom/deployment/pinned-config.json') == value['host_config_sha256'])
    resumed = None
    if (directory / 'source-resume-1.json').exists():
        resumed = read(directory / 'source-resume-1.json')
        require('session_prepared_only_resume_exact',
                resumed.get('schema') == 'mini-oracle-prepared-session-resume-v1'
                and resumed.get('run') == str(run) and resumed.get('store') == value['store']
                and resumed.get('prepared_sha256') == sha(directory / 'prepared.json')
                and resumed.get('partial_manifest_sha256') == sha(directory / 'recovery-input-sha256.txt')
                and resumed.get('failed_launch_sha256') == sha(Path(resumed['failed_launch_receipt']))
                and resumed.get('existing_backup_reused') is True and resumed.get('repeated_phases') == []
                and resumed.get('runtime_sha256') == sha(directory / 'bin/grain-runtime')
                and resumed.get('execution_manifest') == str(directory / 'source-resume-1-input-sha256.txt'))
        for name, digest in resumed['source_files'].items():
            require('session_resumed_source_' + name, Path(name).is_absolute() and sha(Path(name)) == digest)
        for line in (directory / 'source-resume-1-input-sha256.txt').read_text().splitlines():
            digest, name = line.split(None, 1)
            require('session_execution_source_' + name, Path(name).is_absolute() and sha(Path(name)) == digest)
    prior = read(directory / 'prior/agent-lifetime/session-birth.result.json')
    current = read(run / 'agent-lifetime/session-birth.result.json')
    if recovered is not None:
        require('session_recovery_preserves_original_failed_operation',
                current.get('requestId') == recovered['receipt']['requestId']
                and str(current.get('operationId')) == recovered['receipt']['operationId']
                and current.get('isError') is True)
        current = recovered['retained_result']
    require('session_new_tool_does_not_recast_original_failure',
            prior.get('isError') is True and prior.get('operationId') is None
            and prior.get('requestId') == value['boundary']['request_id']
            and current.get('isError') is False and current.get('operationId') is not None
            and current.get('requestId') != prior['requestId']
            and (recovered is not None or sha(run / 'agent-lifetime/session-birth.result.json') ==
                sha(run / 'agent-lifetime/session-birth.retained-result.json'))
            and (run / 'agent-lifetime/session-birth.ack.json').is_file())
    upgrade = read(directory / 'runtime-upgrade.json')
    require('session_explicit_runtime_upgrade', upgrade.get('store') == value['store']
            and upgrade.get('previousRuntimeSha256') == sha(run / 'bin/grain-runtime')
            and upgrade.get('runtimeSha256') == sha(directory / 'bin/grain-runtime')
            and upgrade['runtimeSha256'] != upgrade['previousRuntimeSha256'])
    return {'prepared': value, 'prepared_sha256': sha(directory / 'prepared.json'),
            'original_failed_tool': prior, 'runtime_upgrade': upgrade, 'prepared_only_resume': resumed,
            'continuation_exit_path': str(directory / 'exit.json'),
            'scope': 'Same retained Store; original null-operation refusal preserved without ACK or resend. '
                     'Explicit source policy and native binding enrollments precede the new session attempt.'}


def checkpoint_continuation(run, require, recovered=None):
    executions = list((run / 'continuations').glob('checkpoint-*/checkpoint.json'))
    if not executions:
        return None
    require('one_checkpoint_execution', len(executions) == 1)
    path = executions[0]
    execution = read(path)
    checkpoint_path = Path(execution['checkpoint'])
    checkpoint = read(checkpoint_path)
    require('checkpoint_exact_boundary',
            execution.get('schema') == 'mini-oracle-checkpoint-execution-v1'
            and execution.get('checkpoint_sha256') == sha(checkpoint_path)
            and checkpoint.get('schema') == 'mini-oracle-phase-checkpoint-v1'
            and checkpoint.get('run') == str(run)
            and checkpoint.get('boundary') == 'after-physical-repairs-before-source'
            and checkpoint.get('completed_phases') == ['consent-storage', 'controller-runtime-upgrade']
            and checkpoint.get('next_phase') == execution.get('next_phase') == 'public-listener'
            and execution.get('repeated_phases') == checkpoint.get('repeated_source_phases') == [])
    for name, digest in checkpoint['receipts'].items():
        require('checkpoint_predecessor_' + name, sha(Path(name)) == digest)
    for name, digest in execution['sources'].items():
        require('checkpoint_source_' + name, sha(Path(name)) == digest)
    for name, archived in execution['archived_original_paths'].items():
        require('checkpoint_archive_' + name, Path(name).is_relative_to(run)
                and Path(archived['path']).is_relative_to(path.parent / 'prior')
                and sha(Path(archived['path'])) == archived['sha256'])
    phases = {}
    for name in ('public-listener', 'services', 'bootstrap-target', 'worker-policy',
                 'bootstrap-enrollment', 'controller-start', 'session-and-grant'):
        start = path.parent / 'phases' / (name + '.started.json')
        if name == 'session-and-grant' and recovered is not None:
            require('checkpoint_uncertain_session_preserved', start.is_file()
                    and not (path.parent / 'phases' / (name + '.completed.json')).exists())
            phases[name] = {'state': 'interrupted', 'recovered_by': recovered['receipt']}
            continue
        completed = read(path.parent / 'phases' / (name + '.completed.json'))
        require('checkpoint_phase_' + name, completed.get('phase') == name and completed.get('state') == 'completed'
                and completed.get('started_sha256') == sha(start) and completed.get('permits_automatic_retry') is False)
        for artifact, digest in completed['evidence'].items():
            require('checkpoint_phase_evidence_' + artifact, sha(Path(artifact)) == digest)
        phases[name] = completed
    listener = read(path.parent / 'public-listener.json')
    require('checkpoint_registered_public_listener',
            {key: value for key, value in listener.items() if key != 'publicListener'} == checkpoint['installer_state']
            and listener['publicListener']['controllerUid'] == listener['controllerUid']
            and listener['publicListener']['socket'] == str(run / 'world/sock/participant/host.sock'))
    # Detailed native owner-policy, enrollment, session, grant and application
    # assertions remain the report's independent obligations below/above.
    return {'checkpoint': checkpoint, 'execution': execution, 'phases': phases,
            'public_listener': listener, 'execution_exit_path': str(path.parent / 'exit.json')}


def activation_recovery(run, require):
    directory = run / 'continuations/activation-recovery-1'
    if not directory.exists():
        return None
    from recover_application_api import retained_paths
    retained = retained_paths(run)
    def original(path):
        entry = retained.get(str(path))
        return Path(entry['path']) if entry else Path(path)
    prepared = read(directory / 'prepared.json')
    boundary = prepared['boundary']
    require('activation_recovery_explicit_stopped_boundary',
            prepared.get('schema') == 'mini-oracle-activation-recovery-v1'
            and prepared.get('automatic_retry') is False
            and boundary.get('permits_same_generation_relaunch') is False
            and boundary.get('permits_enrollment_replay') is False
            and boundary.get('store') == read(run / 'world-identity.json')['store'])
    for name, entry in {**prepared['snapshots'], **prepared['archived']}.items():
        path = Path(entry['path'])
        require('activation_preserved_' + name, path.is_relative_to(directory / 'prior')
                and sha(path) == entry['sha256'])
    prior_request = read(directory / 'prior/enrollment-initial/request.json')
    require('activation_original_request_preserved',
            sha(directory / 'prior/enrollment-initial/request.json') == boundary['request_sha256']
            and prior_request['expectedBindingSha256'] == boundary['old_binding_sha256'])
    old_export = read(directory / 'observations/controller-export.json')
    require('activation_had_no_local_enrollment_commit',
            {name for name in old_export['files'] if name.startswith('application-enrollments/')}
                == {'application-enrollments/' + boundary['request_sha256'] + '/request.json'}
            and old_export['files']['journal.json']['sha256'] == boundary['journal_sha256'])
    upgrade = read(directory / 'runtime-upgrade.json')
    require('activation_exact_native_runtime_upgrade',
            upgrade.get('store') == boundary['store']
            and upgrade.get('previousRuntimeSha256') == sha(run / 'bin/grain-runtime')
            and upgrade.get('runtimeSha256') == sha(directory / 'bin/grain-runtime')
            and upgrade['runtimeSha256'] != upgrade['previousRuntimeSha256'])
    successor = run / 'continuations/activation-successor-1'
    recovered_socket = successor.exists()
    execution = successor if recovered_socket else directory
    old = boundary['old_record']
    if recovered_socket:
        continuation = read(successor / 'prepared.json')
        require('activation_successor_explicit_boundary',
                continuation['schema'] == 'mini-oracle-activation-successor-v1'
                and continuation['automatic_retry'] is False
                and continuation['predecessor'] == str(directory)
                and continuation['boundary']['grant_receipt'] == boundary['grant_receipt'])
        for name, digest in continuation['prior_sha256'].items():
            require('activation_successor_preserved_' + name, sha(successor / 'prior' / name) == digest)
        failed = read(successor / 'prior/boundary.json')
        require('activation_successor_was_never_admitted', all(failed['g4_absent'].values())
                and failed['successor_generation'] == continuation['successor_generation']
                and (directory / 'supervise.json').read_bytes() == b'')
        reclaim = read(successor / 'socket-reclaim.json')
        socket = continuation['socket']
        require('activation_exact_native_socket_reclaim',
                reclaim['protocol'] == 'mini-spk-agent-socket-reclaim-v1'
                and reclaim['removed'] is True and reclaim['nativeOperationSubmitted'] is False
                and reclaim['socket'] == socket['path'] and reclaim['ownerUid'] == socket['uid']
                and reclaim['controllerUid'] == continuation['controller_uid']
                and reclaim['previous'] == {key: (int(socket[key], 8) if key == 'mode' else socket[key])
                                           for key in ('device', 'inode', 'mode', 'uid')})
        stopped = read(successor / 'prior/g2-stopped-record.json')
        start = read(successor / 'successor-start.json')
        require('activation_native_never_begun_successor_reused', start['generation'] == continuation['successor_generation'])
        stop_directory = successor / 'prior/stop-completion'
        supervised = None
    else:
        supervised = read(directory / 'supervise.json')
        stopped = read(directory / 'old-record-after-stop.json')
        require('activation_native_supervision', supervised.get('action') == 'stop-and-continue'
                and supervised['crashed']['unit'] == boundary['old_unit']
                and supervised['stop']['protocol'] == 'mini-spk-grain-stop-v1'
                and supervised['stop']['generation'] == boundary['old_generation'])
        start = supervised['start']
        stop_directory = directory / 'stop-completion'
    require('activation_native_STOP_then_successor_START',
            stopped['phase'] == 'stopped' and stopped['identity'] == old['identity']
            and stopped['invocation_id'] == old['invocation_id']
            and start['startAction']['kind'] == 'continue'
            and int(start['generation']) > int(boundary['old_generation'])
            and start['completion']['completionReceipt']['eventId'])
    stop_receipts = list(stop_directory.rglob('receipt-anchor.json'))
    require('activation_native_STOP_completion_retained', bool(stop_receipts)
            and all(read(path).get('eventId') and read(path).get('worldRoot') for path in stop_receipts))
    issued = read(run / 'agent-lifetime/issued-grant.json')
    require('activation_preserves_admitted_grant', issued['grantReceipt'] == boundary['grant_receipt'])
    enrollment = read(original(run / 'agent-lifetime/enrollment-initial/request.json'))
    require('activation_new_request_for_successor', enrollment != prior_request
            and enrollment['expectedBindingSha256'] == boundary['old_binding_sha256']
            and sha(original(run / 'agent-lifetime/enrollment-initial/request.json')) != boundary['request_sha256'])
    phases = [(directory, phase) for phase in ('runtime-upgrade', 'public-listener')]
    phases += [(execution, phase) for phase in
               (('socket-reclaim', 'services', 'successor-start', 'enrollment') if recovered_socket
                else ('services', 'supervise', 'enrollment'))]
    for phase_directory, phase in phases:
        value = read(phase_directory / 'phases' / (phase + '.completed.json'))
        require('activation_phase_' + phase, value['phase'] == phase and value['state'] == 'completed'
                and value['started_sha256'] == sha(phase_directory / 'phases' / (phase + '.started.json')))
        for name, digest in value['evidence'].items():
            require('activation_phase_evidence_' + name, sha(original(name)) == digest)
    for manifest_directory in ([directory, successor] if recovered_socket else [directory]):
        for line in (manifest_directory / 'recovery-input-sha256.txt').read_text().splitlines():
            digest, name = line.split(None, 1)
            require('activation_source_' + name, sha(Path(name)) == digest)
    transport_repairs = []
    for repair in sorted((run / 'native-agent-socket-reclaims').glob('*')):
        before, result = read(repair / 'before.json'), read(repair / 'result.json')
        require('activation_after_STOP_transport_' + repair.name,
                before['record']['phase'] == 'stopped' and before['stopReceipts']
                and all(receipt.get('eventId') and receipt.get('worldRoot') for receipt in before['stopReceipts'])
                and result['protocol'] == 'mini-spk-agent-socket-reclaim-v1'
                and result['nativeOperationSubmitted'] is False
                and result['socket'] == before['socket'] and result['controllerUid'] == before['controllerUid']
                and result['previous'] == before['previous'] and result['removed'] == (before['previous'] is not None))
        for line in (repair / 'binary-sha256.txt').read_text().splitlines():
            digest, name = line.split(None, 1)
            require('activation_transport_binary_' + repair.name, sha(Path(name)) == digest)
        transport_repairs.append({'after_STOP': before['record']['identity'], 'receipt': result})
    return {'prepared': prepared, 'runtime_upgrade': upgrade, 'supervision': supervised,
            'successor_start': start, 'socket_reclaim': reclaim if recovered_socket else None,
            'after_STOP_transport_repairs': transport_repairs,
            'scope': 'Preserved grant and failed pre-commit enrollment; native STOP/START and fresh route enrollment.',
            'execution_exit_path': str(execution / 'exit.json')}


def application_api_recovery(run, require):
    from recover_application_api import recovery_directories
    return [application_api_recovery_attempt(run, directory, require)
            for directory in recovery_directories(run)]


def operator_upgrade_evidence(directory, store, require):
    operator_upgrades = {}
    extra_phases = []
    if (directory / 'consent-memory.json').exists():
        memory = read(directory / 'consent-memory.json')
        def properties(name):
            return dict(line.split('=', 1) for line in (directory / name).read_text().splitlines() if '=' in line)
        before = properties('consent-memory-before.properties')
        after = properties('consent-memory-after.properties')
        unit = 'mini-spk-controller-consent-' + store + '.service'
        require('operator_consent_memory_revision', memory['store'] == store
                and memory['nativeOperationSubmitted'] is False
                and before['Id'] == after['Id'] == unit
                and before['MainPID'] == after['MainPID'] == '0'
                and before['ActiveState'] in ('inactive','failed') and after['ActiveState'] in ('inactive','failed')
                and int(after['MemoryMax']) == memory['memoryMiB'] * 1024 * 1024
                and before['MemorySwapMax'] == after['MemorySwapMax'])
        operator_upgrades['consent_memory'] = {'receipt':memory, 'before':before, 'after':after}
        extra_phases.append('consent-memory')
    if (directory / 'mini-upgrade.json').exists():
        client = read(directory / 'mini-upgrade.json')
        previous = (directory / 'mini-before.sha256').read_text().split()[0]
        require('operator_exact_controller_mini_revision', client['store'] == store
                and client['miniSha256'] == sha(directory / 'bin/mini')
                and (client.get('previousMiniSha256') == previous or
                     (client.get('alreadyConfigured') is True and previous == client['miniSha256'])))
        operator_upgrades['mini'] = client
        extra_phases.append('mini-upgrade')
    return operator_upgrades, extra_phases


def application_api_recovery_attempt(run, directory, require):
    from recover_application_api import check_native, retained_paths, exported, startup_refusal, readiness_refusal
    retained = retained_paths(run, after=directory)
    later_retained = dict(retained)
    def resumed_original(path):
        return Path(later_retained.get(str(path), {'path':str(path)})['path'])
    resumption = directory / 'resumption'
    resumptions = [resumption,*sorted((resumption/'retries').glob('*'))] if resumption.is_dir() else []
    if resumption.is_dir():
        retained.update(read(resumption/'prepared.json')['preserved'])
    def original(path):
        entry = retained.get(str(path))
        return Path(entry['path']) if entry else Path(path)
    prepared = read(directory / 'prepared.json'); boundary = prepared['boundary']
    startup = boundary.get('kind') in ('startup-refusal','readiness-refusal')
    if startup:
        export = read(directory / 'observations/controller-export.json')
        prior_journal = json.loads(exported(export, 'journal.json'))
        refused = (readiness_refusal(export, prior_journal, directory / 'prior')
                   if boundary['kind'] == 'readiness-refusal' else
                   startup_refusal(export, prior_journal, directory / 'prior/probe', boundary['request_id']))
        require('startup_refusal_exact_no_tool_admission', refused == boundary['pre_admission']
                and not (directory / 'native-recovery.json').exists())
        proof = None
    else:
        proof = check_native(directory, terminal=True)
    require('api_recovery_explicit_original_request',
            prepared['schema'] == 'mini-oracle-application-api-recovery-v1'
            and prepared['automatic_retry'] is False and boundary['retransmit'] is False)
    for entry in [*prepared['preserved'].values(), *prepared['archived'].values()]:
        require('api_recovery_preserved_' + entry['path'], sha(Path(entry['path'])) == entry['sha256'])
    operator_upgrades, extra_phases = operator_upgrade_evidence(directory, boundary['store'], require)
    upgrade = read(directory / 'runtime-upgrade.json')
    require('api_recovery_exact_runtime_upgrade', upgrade['previousRuntimeSha256'] == boundary['runtime_sha256']
            and upgrade['runtimeSha256'] == sha(directory / 'bin/grain-runtime'))
    stop = read(directory / 'stop.json'); stopped = read(directory / 'old-record-after-stop.json')
    start = read(directory / 'successor-start.json')
    require('api_recovery_native_incarnation_retirement', stop['protocol'] == 'mini-spk-grain-stop-v1'
            and stop['generation'] == boundary['old_generation']
            and stopped['phase'] == 'stopped' and stopped['identity'] == boundary['old_record']['identity']
            and stopped['invocation_id'] == boundary['old_record']['invocation_id']
            and start['protocol'] == 'mini-spk-grain-start-v1' and start['startAction']['kind'] == 'continue'
            and int(start['generation']) > int(boundary['old_generation'])
            and start['completion']['completionReceipt']['eventId'])
    stops = list((directory / 'stop-completion').rglob('receipt-anchor.json'))
    require('api_recovery_native_STOP_receipts', bool(stops)
            and all(read(path).get('eventId') and read(path).get('worldRoot') for path in stops))
    journal = prior_journal if startup else read(directory / 'terminal-journal.json')
    binding = hashlib.sha256(json.dumps(journal['binding'],sort_keys=True,separators=(',',':'),ensure_ascii=False).encode()).hexdigest()
    read_recovery=run/'continuations'/('activation-read-'+start['generation'])
    interrupted_enrollment=read_recovery.is_dir()
    if interrupted_enrollment:
        recovered=read(read_recovery/'prepared.json')
        require('api_recovery_preserved_pre_enrollment_refusal',
            recovered['schema']=='mini-oracle-activation-read-recovery-v1'
            and recovered['boundary']['previous_execution']==str(directory)
            and recovered['boundary']['start_sha256']==sha(directory/'successor-start.json')
            and not (directory/'phases/enrollment.completed.json').exists())
    else:
        enrollment = read(original(run / 'agent-lifetime/enrollment-initial/request.json'))
        require('api_recovery_successor_binding_enrolled', enrollment['expectedBindingSha256'] == binding)
    require('api_recovery_original_grant_preserved',
            read(run / 'agent-lifetime/issued-grant.json')['grantReceipt'] == boundary['grant_receipt'])
    require('api_recovery_new_discovery_id_after_preserved_outcome',
            original(run / 'agent-lifetime/probe/discover-core-query.request-id').read_text().strip() != boundary['request_id'])
    if resumption.is_dir():
        resumed=read(resumption/'prepared.json'); next_runtime=read(resumption/'runtime-upgrade.json')
        require('api_resumption_exact_stopped_boundary', resumed['schema']=='mini-oracle-api-stopped-resumption-v1'
                and resumed['retransmit'] is False and resumed['request_id']==boundary['request_id']
                and resumed['original_prepared_sha256']==sha(directory/'prepared.json')
                and resumed['stop_sha256']==sha(directory/'stop.json')
                and read(resumption/'prior-exit.json')=={'execution_exit':143,'cleanup_exit':0,'namespace_preserved':True})
        require('api_resumption_exact_runtime_successor', next_runtime['previousRuntimeSha256']==upgrade['runtimeSha256']
                and next_runtime['runtimeSha256']==sha(resumption/'bin/grain-runtime'))
        for attempt in resumptions:
            preparation=read(attempt/'prepared.json')
            require('api_resumption_boundary_'+str(attempt),preparation['original_prepared_sha256']==sha(directory/'prepared.json')
                    and preparation['stop_sha256']==sha(directory/'stop.json') and preparation['retransmit'] is False)
            if attempt!=resumption:
                prior=read(attempt/'prior-exit.json')
                require('api_resumption_clean_pre_migration_retry_'+str(attempt),prior['execution_exit']!=0
                        and prior['cleanup_exit']==0 and prior['namespace_preserved'] is True
                        and preparation['runtime_sha256']==next_runtime['runtimeSha256'])
                extra_phases.append('resume-services-retry-'+attempt.name)
            for entry in preparation['preserved'].values():
                require('api_resumption_preserved_'+entry['path'],sha(Path(entry['path']))==entry['sha256'])
            for line in (attempt/'source-input-sha256.txt').read_text().splitlines():
                digest,name=line.split(None,1);require('api_resumption_source_'+name,sha(Path(name))==digest)
        repair=run/'agent-lifetime/repair-payer-custody'
        complete=read(repair/'complete.json')
        require('api_resumption_native_payer_route_successor', complete['protocol']=='mini-application-payer-successor-complete-v1'
                and complete['app']=='9101' and complete['grantChanged'] is False and complete['sessionChanged'] is False)
        extra_phases += ['resume-runtime-upgrade','resume-services','payer-route-successor']
    phases = [*extra_phases, 'runtime-upgrade','services']
    if not startup:
        phases += ['controller-start','native-recovery','native-reconciliation']
    phases += ['retire-incarnation','successor-start'] + ([] if interrupted_enrollment else ['enrollment'])
    for phase in phases:
        value = read(directory / 'phases' / (phase+'.completed.json'))
        require('api_recovery_phase_'+phase, value['phase']==phase and value['state']=='completed'
                and value['started_sha256']==sha(directory / 'phases' / (phase+'.started.json')))
        for name,digest in value['evidence'].items():
            candidates=[original(name),resumed_original(name)]
            for attempt in resumptions:
                entry=read(attempt/'prepared.json')['preserved'].get(name)
                if entry and entry['sha256']==digest: candidates.append(Path(entry['path']))
            require('api_recovery_evidence_'+name,any(p.is_file() and sha(p)==digest for p in candidates))
    for line in (directory / 'recovery-input-sha256.txt').read_text().splitlines():
        digest,name=line.split(None,1)
        require('api_recovery_source_'+name,sha(original(name))==digest)
    return {'kind':boundary.get('kind','unreserved-api'),'proof':proof,'original_request_id':boundary['request_id'],
            'operator_upgrades':operator_upgrades,
            'terminal':('native readiness refusal; no tool request allocated' if boundary.get('kind') == 'readiness-refusal' else
                        'native pre-admission refusal; no tool operation allocated' if startup else
                        'audited, already reported; no definitive answer or separate ACK'),
            'retransmitted':False,'successor_start':start,'execution_exit_path':str(directory / 'exit.json')}


def activation_read_recoveries(run, require):
    from recover_application_api import retained_paths, exported
    values=[]
    for directory in sorted((run/'continuations').glob('activation-read-*')):
        prepared=read(directory/'prepared.json'); b=prepared['boundary']
        require('activation_read_exact_boundary',prepared['schema']=='mini-oracle-activation-read-recovery-v1'
            and prepared['automatic_retry'] is False and b['permits_same_generation_relaunch'] is False
            and b['permits_enrollment_replay'] is False)
        for entry in [*prepared['preserved'].values(),*prepared['archived'].values()]:
            require('activation_read_preserved_'+entry['path'],sha(Path(entry['path']))==entry['sha256'])
        failed=directory/'prior'/('native-activate-'+b['old_generation'])
        for name,digest in prepared['failed_attempt_sha256'].items():
            require('activation_read_failed_attempt_'+name,sha(failed/name)==digest)
        query=failed/'session-before-enrollment'
        require('activation_read_unsigned_query_only',set(p.name for p in query.iterdir())=={'intent.json','config.json','attempt.json'}
            and read(query/'attempt.json')['operation']=='query' and read(query/'intent.json')['purpose']['type']=='query'
            and sha(query/'intent.json')==b['failed_query_intent_sha256'])
        journal=json.loads(exported(read(directory/'observations/controller-export.json'),'journal.json'))
        status=read(directory/'observations/controller-status.json')
        require('activation_read_unchanged_stopped_runtime',status['stopped'] is True
            and status['runtimeSha256']==b['runtime_sha256']==sha(directory/'bin/grain-runtime')
            and status['controllerConfigSha256']==b['controller_config_sha256'] and journal['connection']=='detached')
        stop=read(directory/'stop.json'); stopped=read(directory/'old-record-after-stop.json'); start=read(directory/'successor-start.json')
        require('activation_read_native_successor',stop['protocol']=='mini-spk-grain-stop-v1' and stop['generation']==b['old_generation']
            and stopped['phase']=='stopped' and stopped['identity']==b['old_record']['identity']
            and start['startAction']['kind']=='continue' and int(start['generation'])>int(b['old_generation'])
            and start['completion']['completionReceipt']['eventId'])
        retained=retained_paths(run,after=directory)
        for phase in ('services','retire-incarnation','successor-start','enrollment'):
            completed=read(directory/'phases'/(phase+'.completed.json'))
            require('activation_read_phase_'+phase,completed['started_sha256']==sha(directory/'phases'/(phase+'.started.json')))
            for name,digest in completed['evidence'].items():
                path=Path(retained.get(name,{'path':name})['path'])
                require('activation_read_phase_evidence_'+name,sha(path)==digest)
        for line in (directory/'recovery-input-sha256.txt').read_text().splitlines():
            digest,name=line.split(None,1);require('activation_read_source_'+name,sha(Path(name))==digest)
        values.append({'boundary':b,'successor_start':start,'execution_exit_path':str(directory/'exit.json')})
    return values


def pooled_tenant_probe(run, require):
    marker = run / 'pooled-tenant-probe-request.json'
    if not marker.exists():
        return None
    request = read(marker)
    require('pooled_probe_request_exact', request == {
        'protocol':'mini-oracle-pooled-tenant-probe-v1','app':'9101','path':'/query',
        'request':{'request_id':'mini-u3-weather-structured','conversation_id':'mini-owner-pool-collision',
                   'text':'Who wrote Leaves of Grass?'}})
    owner = read(run / 'world/evidence/share-a.stdout')
    config = read(run / 'agent-lifetime/controller-active-initial.json')
    routes = [r for r in config['toolTask']['allowedApplicationLifetimeRoutes'] if r['name'] == 'oracle-app']
    require('pooled_probe_one_agent_route', len(routes) == 1)
    agent = routes[0]
    require('pooled_probe_same_grain_distinct_principals_sessions',
            owner.get('protocol') == 'mini-spk-grain-route-v1' and owner.get('app') == agent.get('appResource') == '9101'
            and owner.get('kind') == 'api' and owner.get('subject') != agent.get('participantSubject')
            and owner.get('session') != agent.get('sessionResource'))
    initial_dir = run / 'agent-lifetime/probe'
    restart_dir = run / 'agent-lifetime/probe-after-restart'
    cases = [c for c in read(initial_dir / 'cases.json') if c['name'] == 'weather-structured']
    require('pooled_probe_exact_agent_request_collision', len(cases) == 1
            and cases[0]['tool'] == 'mini_oracle_call'
            and cases[0]['arguments']['requestId'] == request['request']['request_id']
            and cases[0]['arguments']['operationId'] == 'specialist.meteorology-v2.heat_index_f')
    initial = read(initial_dir / 'weather-structured.http.json')
    restarted = read(restart_dir / 'weather-structured.http.json')
    weather = json.loads(initial['bodyText'])
    require('pooled_probe_agent_weather_survives_owner_collision_and_restart',
            initial['status'] == restarted['status'] == 200 and initial['bodyText'] == restarted['bodyText']
            and weather.get('operation_id') == 'specialist.meteorology-v2.heat_index_f'
            and weather.get('reply', {}).get('status') == 'answered'
            and weather['reply'].get('unit') == 'degF')
    reply_path = run / 'world/evidence/post-a15-body.body'
    owner_reply = read(reply_path)
    headers = (run / 'world/evidence/post-a15-body.headers').read_text().splitlines()
    require('pooled_probe_owner_same_id_query_succeeds', bool(headers) and headers[0].split()[1] == '200'
            and owner_reply.get('reply', {}).get('status') == 'answered'
            and 'Whitman' in owner_reply['reply'].get('response',''))
    return {'request':request,'owner_route':{k:owner[k] for k in ('app','subject','session','issueIndex')},
            'agent_route':{k:agent[k] for k in ('appResource','participantSubject','sessionResource','grantDigest')},
            'owner_reply':owner_reply,'owner_reply_sha256':sha(reply_path),
            'agent_reply':weather,'agent_reply_sha256':sha(initial_dir / 'weather-structured.http.json'),
            'restarted_agent_reply_sha256':sha(restart_dir / 'weather-structured.http.json'),
            'scope':'Two distinct principals and source sessions in the same grain; same-principal isolation is not tested.'}


def main():
    run, inventory_sha = Path(sys.argv[1]), sys.argv[2]
    ev = run / 'world/evidence'
    checks = {}

    def require(name, condition):
        checks[name] = bool(condition)
        if not condition:
            raise AssertionError(name)

    replies = {}
    for label in ('a1', 'a2', 'a3', 'a4', 'a5', 'a6', 'a7', 'a8', 'a9', 'a10', 'a11', 'a12', 'a13', 'a14', 'b1', 'b2', 'b3'):
        path = ev / f'post-{label}-body.body'
        value = read(path)
        replies[label] = {'sha256': sha(path), 'bytes': path.stat().st_size,
                          'status': value.get('reply', {}).get('status'),
                          'path': value.get('reply', {}).get('path'),
                          'refusal': value.get('reply', {}).get('refusal'),
                          'response': value.get('reply', {}).get('response', '')}
    require('whitman', replies['a1']['status'] == 'answered' and 'Whitman' in replies['a1']['response'])
    require('austen', replies['a2']['status'] == 'answered' and 'Austen' in replies['a2']['response'])
    require('followup_1775', replies['a3']['status'] == 'answered'
            and '16 December 1775 (Gregorian calendar)' in replies['a3']['response']
            and 'unavailable' not in replies['a3']['response'].lower())
    require('isa_minus_4_5', replies['a4']['status'] == 'answered' and '-4.5' in replies['a4']['response'])
    require('invalid_altitude_units_refused', replies['a5']['status'] in ('withheld', 'clarification')
            and '-4.5' not in replies['a5']['response'])
    require('two_grains_same_ids_distinct_answers', replies['b1']['status'] == 'answered'
            and 'Austen' in replies['b1']['response']
            and replies['b1']['sha256'] != replies['a1']['sha256'])
    require('first_grain_unchanged_by_second', replies['a1']['sha256'] == replies['a6']['sha256'])
    require('restart_exact_reply', replies['a1']['sha256'] == replies['a7']['sha256'])
    require('restart_exact_followup', replies['a3']['sha256'] == replies['a8']['sha256'])
    require('second_grain_unchanged_by_restart', replies['b1']['sha256'] == replies['b2']['sha256'])
    require('second_grain_exact_replay_after_reconciliation', replies['b1']['sha256'] == replies['b3']['sha256'])
    mars = re.search(r'([0-9]+(?:\.[0-9]+)?)\s+Earth years', replies['a9']['response'])
    require('supplied_mars_periods_preserved', replies['a9']['status'] == 'answered' and mars is not None
            and math.isclose(float(mars.group(1)), 3 * 687 / 365.25, rel_tol=1e-9))
    require('shakespeare_month_precision', replies['a10']['status'] == 'answered'
            and 'April 1564' in replies['a10']['response']
            and 'day unspecified' in replies['a10']['response']
            and not re.search(r'\b[0-9]{1,2} April 1564', replies['a10']['response']))
    require('salinger_real_first_day', replies['a11']['status'] == 'answered'
            and '1 January 1919' in replies['a11']['response']
            and 'day unspecified' not in replies['a11']['response'])
    require('salinger_carter_order_uses_source_dates', replies['a12']['status'] == 'answered'
            and replies['a12']['response'].startswith('[ev:derived] J. D. Salinger.')
            and '1 January 1919 (Gregorian calendar)' in replies['a12']['response']
            and '1 October 1924 (Gregorian calendar)' in replies['a12']['response']
            and 'by 58 years' not in replies['a12']['response'])
    require('shakespeare_newton_order_preserves_month_precision', replies['a13']['status'] == 'answered'
            and replies['a13']['response'].startswith('[ev:derived] William Shakespeare.')
            and 'April 1564 (Julian calendar; day unspecified)' in replies['a13']['response']
            and '25 December 1642 (Julian calendar)' in replies['a13']['response']
            and 'by 104 years' not in replies['a13']['response'])
    require('uncertain_birth_order_terminal_refusal', replies['a14']['status'] == 'withheld'
            and replies['a14']['path'] == 'composed>date_order_unverified'
            and isinstance(replies['a14']['refusal'], dict)
            and replies['a14']['refusal'].get('terminal') is True
            and replies['a14']['refusal'].get('reason') == 'date_order_unverified')
    require('inventory_bytes_pinned', sha(run / 'inventory.json') == inventory_sha)
    publication = read(run / 'publication.json')
    require('published_exact_inventory', publication.get('inventory_sha256') == inventory_sha)
    operator_import = read(run / 'import-profile.json')
    selected_profile = operator_import['selected_profile']
    disk_plan = read(run / 'disk-plan.json')
    require('capacity_plan_keeps_native_guards', disk_plan.get('fits') is True
            and disk_plan.get('reservation') is False
            and disk_plan.get('order') == 'install-both-before-publication'
            and disk_plan['available_bytes'] >= disk_plan['materialize_guard_bytes']
            and disk_plan['projected_available_after_publication'] >= disk_plan['verify_guard_bytes'])
    disk = {name: read(run / f'disk-{name}.json')
            for name in ('before-install', 'after-install', 'after-publication', 'after-stops')}
    require('observed_post_publication_verification_space',
            disk['after-publication']['available_bytes'] >= disk_plan['verify_guard_bytes'])

    op155 = {letter: read(run / f'op155-{letter}/report.json') for letter in ('a', 'b')}
    operator_identities = [read(run / f'op155-operator-{boundary}.json')
                           for boundary in ('before', 'after-a', 'before-b', 'after-b')]
    require('stop_inspection_same_operator_process', all(
        identity == operator_identities[0] for identity in operator_identities))
    require('fresh_stop_resident_controls_at_both_boundaries', all(
        item.get('schema') == 'mini-stop-inspection-probe-v1' and item.get('passed') is True
        and item.get('mode') == 'resident-only' and item.get('served_checks_passed') is True
        and item.get('cold_comparison') == 'not-performed'
        for item in op155.values()))
    if (run/'native-stop-reference.json').exists():
        reference=read(run/'native-stop-reference.json')
        require('same_host_native_STOP_preflight_reference',reference['schema']=='mini-oracle-native-stop-reference-v1'
            and reference['host_sha256']==sha(run/'bin/minidregg-host'))
        for key in ('host_binary','stop_receipt','command_result','control_claim'):
            require('native_STOP_preflight_'+key,sha(Path(reference[key]['path']))==reference[key]['sha256'])
        require('native_STOP_reference_definite_success',read(Path(reference['command_result']['path']))=={'exitCode':0}
            and read(Path(reference['stop_receipt']['path']))['protocol']=='mini-spk-grain-stop-v1')
    copied_benchmark = read(run / 'copied-store-stop-benchmark.json')
    require('separate_copied_store_cold_comparison_same_host',
            copied_benchmark.get('schema') == 'mini-stop-inspection-continuation-v1'
            and copied_benchmark.get('passed') is True
            and copied_benchmark.get('host_sha256') == op155['a']['host_sha256']
            and copied_benchmark.get('config_sha256') != op155['a']['config_sha256']
            and re.fullmatch(r'[0-9a-f]{64}', copied_benchmark.get('cold_sha256', '')) is not None
            and copied_benchmark.get('canonical_wrong_claim_checked') is True
            and copied_benchmark.get('source_and_copied_store_and_anchor') == 'hashes unchanged'
            and copied_benchmark.get('controls') == {
                'trailing-claim': 'source', 'malformed-pair': 'transport-routing',
                'mismatched-committed': 'source', 'public-denied': 'transport-routing'})
    require('stop_inspection_refreshed_for_new_claim',
            op155['a']['plan_sha256'] != op155['b']['plan_sha256']
            and op155['a']['committed_sha256'] != op155['b']['committed_sha256']
            and op155['a']['host_sha256'] == op155['b']['host_sha256']
            and op155['a']['config_sha256'] == op155['b']['config_sha256'])
    require('stop_inspection_rejects_old_canonical_claim',
            op155['b'].get('canonical_wrong_claim_checked') is True
            and op155['b'].get('mismatched_committed_sha256') == op155['a']['committed_sha256'])

    configs, mounts, native_receipts, stop_receipts = {}, {}, {}, {}
    for app in ('9101', '9201'):
        directory = run / 'receiving' / app
        configs[app] = [read(p) for p in sorted(directory.glob('g*/resident.json'))]
        require(f'grain_{app}_native_configs', bool(configs[app]))
        completion = read(directory / 'install-completed-v2.json')
        require(f'grain_{app}_native_install_completed',
                completion.get('protocol') == 'mini-spk-install-completed-v2'
                and completion.get('rawSha256') == configs[app][0]['expectedRawSha256']
                and bool(completion.get('completionReceipt', {}).get('eventId')))
        require(f'grain_{app}_imported_under_selected_profile',
                read(directory / 'import-policy.json') == {'profile': selected_profile})
        maps = list((directory / 'namespaces').glob('*.uid_map'))
        for mapping in maps:
            rows = [tuple(map(int, line.split())) for line in mapping.read_text().splitlines()]
            require(f'grain_{app}_{mapping.stem}_host_root_unmapped', bool(rows)
                    and all(outside != 0 for inside, outside, count in rows))
        require(f'grain_{app}_actual_namespace_observed', bool(maps))
        attachment = read(directory / 'minidregg-data.json')
        require(f'grain_{app}_signed_data_declaration', attachment == {
            'schema': 'minidregg-public-data-v1', 'inventory_sha256': inventory_sha})
        mounts[app] = mount_rows(directory / 'mounts')
        data_mounts = [m for m in mounts[app] if m['target'] == '/opt/oracle-data']
        require(f'grain_{app}_read_only_data_mounted', bool(data_mounts)
                and all('ro' in m['options'] for m in data_mounts))
        require(f'grain_{app}_mount_exact_inventory', all(
            m['root'].endswith(f'/sha256-{inventory_sha}/data') for m in data_mounts))
        native_receipts[app] = [{'file': str(p.relative_to(run)), 'sha256': sha(p)}
                               for p in sorted(directory.glob('g*/start-completed*.json'))]
        require(f'grain_{app}_two_native_start_completions',
                len({Path(row['file']).parts[2] for row in native_receipts[app]}) >= 2)
        stop_receipts[app] = [{'file': str(p.relative_to(run)), 'sha256': sha(p), 'receipt': read(p)}
                              for p in sorted(directory.glob('g*/stop-completion/**/receipt-anchor.json'))]
        require(f'grain_{app}_two_native_stop_completions', len({Path(row['file']).parts[2] for row in stop_receipts[app]}) >= 2
                and all(row['receipt'].get('eventId') and row['receipt'].get('worldRoot')
                        for row in stop_receipts[app]))
    require('restart_keeps_runtime_and_var', len(configs['9101']) >= 2
            and len({c['expectedRawSha256'] for c in configs['9101']}) == 1
            and len({c['persistentVar'] for c in configs['9101']}) == 1)
    require('reconciled_restart_keeps_runtime_and_var', len(configs['9201']) >= 2
            and len({c['expectedRawSha256'] for c in configs['9201']}) == 1
            and len({c['persistentVar'] for c in configs['9201']}) == 1)
    require('both_grains_same_signed_runtime', len({c['expectedRawSha256']
            for cs in configs.values() for c in cs}) == 1)
    require('separate_var_paths', configs['9101'][0]['persistentVar'] != configs['9201'][0]['persistentVar'])
    data = {app: {(m['device'], m['root']) for m in rows if m['target'] == '/opt/oracle-data'}
            for app, rows in mounts.items()}
    require('same_physical_data_mount', len(data['9101']) == 1 and data['9101'] == data['9201'])
    vars_ = {app: {(m['device'], m['root']) for m in rows if m['target'] == '/var'}
             for app, rows in mounts.items()}
    require('separate_physical_var_mounts', bool(vars_['9101']) and bool(vars_['9201'])
            and vars_['9101'].isdisjoint(vars_['9201']))
    reconciliation_dir = run / 'reconcile-b'
    prior = read(reconciliation_dir / 'record-before.json')
    inactive = read(reconciliation_dir / 'record-inactive.json')
    stopped = read(reconciliation_dir / 'record-stopped.json')
    manager = dict(line.split('=', 1) for line in
                   (reconciliation_dir / 'manager-inactive.txt').read_text().splitlines())
    require('manager_stop_keeps_running_journal_exact', prior == inactive and inactive['phase'] == 'running')
    require('reconciliation_exact_inactive_unit', manager.get('Id') == prior['identity']['unit']
            and manager.get('LoadState') == 'loaded' and manager.get('ActiveState') == 'inactive'
            and manager.get('MainPID') == '0' and manager.get('InvocationID') == ''
            and manager.get('ControlGroup') == '' and manager.get('Job') in ('', '0'))
    require('native_stop_reconciles_same_incarnation', stopped['phase'] == 'stopped'
            and stopped['identity'] == prior['identity']
            and stopped['invocation_id'] == prior['invocation_id']
            and stopped['control_group'] == prior['control_group'] and stopped['child_pid'] is None)
    reconciled_status = read(reconciliation_dir / 'after-native-stop.json')
    require('reconciled_generation_source_stopped', any(
        row['generation'] == str(prior['identity']['generation']) and row['state'] == 'stopped'
        for row in reconciled_status['runs']))
    for letter in ('a', 'b'):
        final_status = read(ev / f'status-{letter}.stdout')
        require(f'final_{letter}_source_stopped', all(
            row['state'] in ('stopped', 'never-begun') for row in final_status['runs']))
    refusals = {}
    for label in ('missing-data', 'wrong-data'):
        before, after = read(run / f'{label}-before.json'), read(run / f'{label}-after.json')
        stable = lambda s: [r for r in s['runs'] if r['state'] != 'never-begun']
        require(f'{label}_lifecycle_unchanged', stable(before) == stable(after))
        require(f'{label}_no_running_or_uncertain', all(r['state'] in ('stopped', 'never-begun') for r in after['runs']))
        code = int((run / f'{label}.exit').read_text())
        require(f'{label}_prompt_refusal', code not in (0, 124))
        journal = (run / f'{label}.unit.log').read_text()
        require(f'{label}_signed_dataset_custody_refusal',
                f'signed public-data {inventory_sha} custody refused:' in journal)
        if label == 'wrong-data':
            require('wrong-data_inventory_mismatch_cause',
                    'published inventory differs from signed attachment digest' in journal)
        else:
            require('missing-data_catalog_absent_cause',
                    f'signed public-data {inventory_sha} custody refused: '
                    'No such file or directory (os error 2)' in journal)
        refusals[label] = {'exit': code, 'stderr': (run / f'{label}.stderr').read_text()[-8192:],
                           'unit_journal': journal[-8192:]}
    import_units = {}
    for line in (run / 'import-units.jsonl').read_text().splitlines():
        item = json.loads(line)
        unit, message = item.get('USER_UNIT', ''), item.get('MESSAGE', '')
        if not unit.startswith('mini-spk-ingest-'):
            continue
        record = import_units.setdefault(unit, {'timestamps': [], 'failed': False,
                                               'started': False, 'finished': False})
        record['timestamps'].append(int(item['__MONOTONIC_TIMESTAMP']))
        selected = re.search(r'--import-profile ([a-z0-9-]+)', message)
        if selected:
            record['profile'] = selected.group(1)
        if 'Failed with result' in message:
            record['failed'] = True
        if message.startswith(f'Started {unit} '):
            record['started'] = True
        if message.startswith(f'{unit}: Consumed '):
            record['finished'] = True
    for record in import_units.values():
        stamps = record.pop('timestamps')
        record['observed_elapsed_seconds'] = (max(stamps) - min(stamps)) / 1_000_000
    # Type=exec logs no explicit successful exit at this journal level. A finished
    # nonfailed unit is therefore combined with the exact native install
    # completion and materializer's retained policy checks above.
    require('selected_importer_completed_with_native_install', any(
        record.get('profile') == selected_profile and record['started']
        and record['finished'] and not record['failed']
        for record in import_units.values()))
    # This stage is mandatory for the U3 claim. Receiving HTTP responses above
    # cannot substitute for a controller's agent-origin lifetime grant, native
    # dispatch receipt and distinct-purse settlement.
    consent = consent_evidence(run, require)
    continuation = controller_continuation(run, require)
    recovered_foreground = foreground_recovery(run, require)
    resumed_session = session_continuation(run, require, recovered_foreground)
    checkpoint_result = checkpoint_continuation(run, require, recovered_foreground)
    activation_result = activation_recovery(run, require)
    api_recovery_result = application_api_recovery(run, require)
    activation_read_result = activation_read_recoveries(run, require)
    enrollments = controller_enrollments(run, require)
    agent_stages = {}
    for stage in ('probe', 'probe-after-restart'):
        agent_dir = run / 'agent-lifetime' / stage
        readiness = read(run / 'agent-lifetime' / ('readiness-' + stage + '.json'))
        active = read(run / 'agent-lifetime' / ('controller-active-' + ('initial' if stage == 'probe' else 'restart') + '.json'))
        require('agent_' + stage + '_signed_idle_readiness',
                readiness.get('type') == 'mini-grain-idle-readiness-v1' and readiness.get('ready') is True
                and readiness.get('task') == active['task']
                and readiness.get('signedTask', {}).get('grain', {}).get('task') == active['task']
                and (readiness.get('connection'), readiness['signedTask']['grain']['status']) in
                    (('hard','1'),('soft','2'))
                and readiness['signedTask']['grain']['reserved'] == '0')
        agent_probe = read(agent_dir / 'result.json')
        agent_cases = read(agent_dir / 'cases.json')
        require(f'agent_{stage}_lifetime_probe_completed',
                agent_probe.get('protocol') == 'mini-oracle-lifetime-tool-probe-v1'
                and agent_probe.get('application') == 'oracle-app'
                and agent_probe.get('cases') == len(agent_cases)
                and agent_probe.get('result') == 'all-cases-have-definite-lifetime-delivery-and-settlement')
        require(f'agent_{stage}_discovery_and_invoke_exercised',
                any(case['tool'] == 'mini_oracle_discover' and case['status'] == 200
                    for case in agent_cases)
                and any(case['tool'] == 'mini_oracle_call' and case['status'] == 200
                        for case in agent_cases))
        agent_outcomes = []
        for case in agent_cases:
            name = case['name']
            require(f'agent_{stage}_case_{name}_safe_name', bool(re.fullmatch(r'[A-Za-z0-9_-]{1,64}', name)))
            reply = read(agent_dir / f'{name}.http.json')
            attempt = read(agent_dir / f'{name}.lifetime-attempt.json')
            require(f'agent_{stage}_case_{name}_definite_lifetime_settlement',
                    reply.get('protocol') == 'mini-spk-agent-api-v3'
                    and reply.get('type') == 'http-v3' and reply.get('status') == case['status']
                    and attempt.get('phase') == 'definite' and attempt.get('reported') is True
                    and attempt.get('routeName') == 'oracle-app'
                    and str(attempt.get('operationId')) == reply.get('operationId')
                    and attempt.get('bindingSha256') == reply.get('bindingSha256')
                    and attempt.get('operationFingerprint') == reply.get('operationFingerprint')
                    and attempt.get('lifetimeCommittedReceipt') == reply.get('committedReceipt')
                    and reply.get('committedReceipt') is not None
                    and attempt.get('lifetimeSettledResponseSha256') == reply.get('responseSha256')
                    and re.fullmatch(r'[0-9a-f]{64}', reply.get('responseSha256', '')) is not None
                    and attempt.get('lifetimeSettlement', {}).get('forwardOperationId') == attempt.get('operationId')
                    and attempt.get('lifetimeSettlement', {}).get('settlement', {}).get('operation') == 'dispatch settle')
            require(f'agent_{stage}_case_{name}_retained_tool_result_exact',
                    sha(agent_dir / f'{name}.result.json') == sha(agent_dir / f'{name}.retained-result.json'))
            agent_outcomes.append({'name': name, 'tool': case['tool'], 'status': reply['status'],
                                   'operation_id': reply['operationId'],
                                   'response_sha256': reply['responseSha256'],
                                   'attempt_sha256': sha(agent_dir / f'{name}.lifetime-attempt.json')})
        agent_stages[stage] = {'probe': agent_probe, 'outcomes': agent_outcomes}
    first_agent = run / 'agent-lifetime/probe'
    restarted_agent = run / 'agent-lifetime/probe-after-restart'
    require('agent_restart_uses_same_appliance_requests',
            sha(first_agent / 'cases.json') == sha(restarted_agent / 'cases.json'))
    for case in read(first_agent / 'cases.json'):
        if case['tool'] != 'mini_oracle_call':
            continue
        name = case['name']
        initial = read(first_agent / f'{name}.http.json')
        restarted = read(restarted_agent / f'{name}.http.json')
        require(f'agent_{name}_exact_appliance_reply_after_restart',
                initial['bodyText'] == restarted['bodyText'] and initial['status'] == restarted['status'])
        require(f'agent_{name}_new_native_dispatch_after_restart',
                initial['operationId'] != restarted['operationId']
                and (first_agent / f'{name}.request-id').read_text() !=
                    (restarted_agent / f'{name}.request-id').read_text())
    authority = read(run / 'agent-lifetime/authority/report.json')
    require('actual_lifetime_positive_and_wrong_indices_qualified',
            authority.get('protocol') == 'mini-oracle-agent-authority-probe-v1'
            and authority.get('passed') is True
            and authority.get('positiveReserveReceipt', {}).get('eventId')
            and authority.get('wrong-event22-index', {}).get('passed') is True
            and authority.get('wrong-event27-index', {}).get('passed') is True
            and authority.get('revocationTested') is False
            and authority.get('unsubmittedStalePlanTested') is False
            and authority.get('hostSha256') == op155['a']['host_sha256']
            and authority.get('configSha256') == op155['a']['config_sha256']
            and authority.get('applicationAttemptSha256') == sha(
                first_agent / 'discover-core-query.lifetime-attempt.json'))
    browser = None
    if (run / 'browser').exists():
        from browser_edge import validate as validate_browser
        ready = read(run / 'browser/ready.json')
        browser = read(run / 'browser/result.json')
        passed = read(run / 'browser/passed.json')
        validate_browser(browser, ready)
        require('browser_native_owner_web_journey', passed.get('admission') == 'native owner-web route'
                and passed.get('result_sha256') == sha(run / 'browser/result.json')
                and passed.get('ready_sha256') == sha(run / 'browser/ready.json'))
    pooled = pooled_tenant_probe(run, require)
    report = {'schema': 'mini-oracle-shared-data-acceptance-v1', 'passed': True,
              'scope': 'Private Linux Store; real Mini install/share/enrollment/dispatch, agent lifetime tools, '
                       'source STOP/restart/reconciliation and sandbox. '
                       'No public deployment, specialist panel score, or formal answer-proof claim.',
              'inventory_sha256': inventory_sha,
              'runtime_spk_sha256': configs['9101'][0]['expectedRawSha256'],
              'appliance_receipt_sha256': sha(run / 'receiving/9101/APPLIANCE.json'),
              'checks': checks, 'queries': replies, 'mounts': mounts,
              'operator_import': operator_import,
              'disk_plan': disk_plan, 'disk_observations': disk,
              'import_units': import_units,
              'native_completion_receipts': native_receipts,
              'native_stop_receipts': stop_receipts,
              'stop_inspection': op155, 'operator_identity': operator_identities[0],
              'separate_copied_store_cold_benchmark': {'receipt': copied_benchmark,
                  'sha256': sha(run / 'copied-store-stop-benchmark.json'),
                  'scope': 'Different copied Store/config; same Host. Fresh probes are resident-only.'},
              'agent_lifetime': agent_stages, 'agent_authority_controls': authority,
              'controller_consent': consent, 'browser': browser, 'pooled_tenant_probe': pooled,
              'controller_continuation': continuation,
              'session_continuation': resumed_session, 'checkpoint_continuation': checkpoint_result,
              'activation_recovery': activation_result,
              'application_api_recovery': api_recovery_result,
              'activation_read_recovery': activation_read_result,
              'controller_enrollment': enrollments, 'foreground_recovery': recovered_foreground,
              'stopped_running_reconciliation': {'before': prior, 'inactive_manager': manager,
                                                 'source_stopped': stopped},
              'refusals': refusals}
    (run / 'report.json').write_text(json.dumps(report, indent=2, sort_keys=True) + '\n')
    print(json.dumps({'passed': True, 'checks': len(checks), 'report': str(run / 'report.json')}))


if __name__ == '__main__':
    main()
