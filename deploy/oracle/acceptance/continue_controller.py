#!/usr/bin/env python3
"""Untrusted fixture continuity checks, not Mini admission or recovery authority.

Preserve the definite pre-START account-creation failure before the installer
performs its separately checked pending-account recovery. Never submit a call.
"""
import base64
import fcntl
import hashlib
import re
import json
import os
from pathlib import Path
import shutil
import socket
import stat
import subprocess
import sys
import tarfile
import time


def sha(path):
    value = hashlib.sha256()
    with path.open('rb') as source:
        for block in iter(lambda: source.read(1024 * 1024), b''):
            value.update(block)
    return value.hexdigest()


def read(path):
    return json.loads(path.read_bytes())


def require(condition, message):
    if not condition:
        raise ValueError(message)


def durable_json(path, value):
    """Publish a new evidence record; never replace an earlier outcome."""
    raw = (json.dumps(value, indent=2, sort_keys=True) + '\n').encode()
    temporary = path.with_name('.' + path.name + '.' + str(os.getpid()))
    fd = os.open(temporary, os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_NOFOLLOW, 0o600)
    with os.fdopen(fd, 'wb') as sink:
        sink.write(raw)
        sink.flush()
    # Hard-link publication is atomic and refuses an existing destination. A
    # crashed temporary remains evidence; it never counts as a phase outcome.
    os.link(temporary, path, follow_symlinks=False)
    temporary.unlink()


def locked_exec(run, command):
    """Hold one operator lock across preflight, effects, and shell cleanup."""
    meta = run.lstat()
    require(stat.S_ISDIR(meta.st_mode) and meta.st_uid == os.getuid(), 'run lock directory differs')
    path = run / 'acceptance.lock'
    fd = os.open(path, os.O_RDWR | os.O_CREAT | os.O_NOFOLLOW, 0o600)
    meta = os.fstat(fd)
    require(stat.S_ISREG(meta.st_mode) and meta.st_uid == os.getuid()
            and stat.S_IMODE(meta.st_mode) == 0o600 and meta.st_nlink == 1, 'run lock custody differs')
    try:
        fcntl.flock(fd, fcntl.LOCK_EX | fcntl.LOCK_NB)
    except BlockingIOError as error:
        raise ValueError('another acceptance invocation owns this run') from error
    os.set_inheritable(fd, True)
    os.environ['ORACLE_ACCEPTANCE_LOCK_FD'] = str(fd)
    os.execvp(command[0], command)


def verify_lock(run):
    descriptor = os.environ.get('ORACLE_ACCEPTANCE_LOCK_FD', '')
    require(descriptor.isdecimal(), 'acceptance lock is absent')
    fd = int(descriptor)
    opened, named = os.fstat(fd), (run / 'acceptance.lock').lstat()
    require(stat.S_ISREG(opened.st_mode) and opened.st_uid == os.getuid()
            and stat.S_IMODE(opened.st_mode) == 0o600 and opened.st_nlink == 1
            and (opened.st_dev, opened.st_ino) == (named.st_dev, named.st_ino), 'acceptance lock identity differs')
    try:
        fcntl.flock(fd, fcntl.LOCK_EX | fcntl.LOCK_NB)
    except BlockingIOError as error:
        raise ValueError('acceptance lock belongs to another invocation') from error
    # A separately opened descriptor cannot acquire the held flock, even from
    # this process. Merely inheriting an open file is not proof of exclusion.
    probe = os.open(run / 'acceptance.lock', os.O_RDONLY | os.O_NOFOLLOW)
    try:
        try:
            fcntl.flock(probe, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError:
            return
        raise ValueError('acceptance lock is not held')
    finally:
        os.close(probe)


def phase_record(directory, name, action, evidence=()):
    """Evidence only. Native outcome validators run before completion is called.

    A started record is deliberately irreversible here: neither a timeout nor a
    wrapper exit authorizes retry. Continuation requires a separately checked
    checkpoint, and never derives permission from these markers alone.
    """
    require(re.fullmatch('[a-z][a-z0-9-]{0,79}', name), 'phase name malformed')
    require(action in ('started', 'completed'), 'phase action malformed')
    started = directory / (name + '.started.json')
    completed = directory / (name + '.completed.json')
    if action == 'started':
        require(not started.exists() and not completed.exists(), 'phase already began; inspect retained outcome')
        require(not evidence, 'started phase cannot claim evidence')
        value = {'schema': 'mini-oracle-phase-v1', 'phase': name, 'state': action,
                 'unix_time_ns': time.time_ns(), 'permits_automatic_retry': False}
    else:
        require(started.is_file() and not started.is_symlink(), 'phase has no durable start')
        require(evidence, 'completed phase requires validated evidence')
        files = {}
        for item in evidence:
            path = Path(item)
            require(path.is_absolute() and path.is_file() and not path.is_symlink(), 'phase evidence absent or linked')
            files[str(path)] = sha(path)
        value = {'schema': 'mini-oracle-phase-v1', 'phase': name, 'state': action,
                 'started_sha256': sha(started), 'evidence': files,
                 'unix_time_ns': time.time_ns(), 'permits_automatic_retry': False}
    durable_json(started if action == 'started' else completed, value)


def manifest(path):
    values = {}
    for line in path.read_text().splitlines():
        digest, name = line.split(None, 1)
        item = Path(name)
        require(item.is_absolute() and not item.is_symlink() and item.is_file(), 'manifest path differs')
        require(sha(item) == digest, 'retained bytes changed: ' + name)
        values[name] = digest
    return values


def session_refusal(request_id, result, final_journal, exported, store):
    """Check a definite pre-tool refusal; this never authorizes replay or ACK.

    The caller must separately obtain a fresh fixed-installer export and prove
    stopped services and unchanged installed/native state before continuation.
    """
    require(isinstance(request_id, str) and re.fullmatch('[0-9a-f]{32}', request_id),
            'session request identity malformed')
    require(type(result.get('isError')) is bool and type(result.get('v')) is int
            and result == {'isError': True, 'operationId': None, 'requestId': request_id,
                       'result': 'foreground tool requires an attached, reconciled idle task',
                       'type': 'tool-complete', 'v': 1}, 'not the exact definite pre-tool refusal')
    require(exported.get('protocol') == 'mini-spk-controller-evidence-v1'
            and exported.get('store') == store, 'controller export identity differs')
    expected = {'controller.lock', 'journal.json',
                'query-0000000000000001/attempt/attempt.json',
                'query-0000000000000001/attempt/config.json',
                'query-0000000000000001/attempt/intent.bin',
                'query-0000000000000001/attempt/intent.json',
                'query-0000000000000001/intent-source.json',
                'shared-app-refs/app-birth.bin', 'shared-app-refs/bootstrap-ticket.bin'}
    require(isinstance(exported.get('files'), dict) and set(exported['files']) == expected,
            'controller state contains another operation or sealed request')
    decoded = {}
    for name, entry in exported['files'].items():
        raw = base64.b64decode(entry['base64'], validate=True)
        require(len(raw) <= 1024 * 1024 and hashlib.sha256(raw).hexdigest() == entry['sha256'],
                'controller export bytes differ')
        decoded[name] = raw
    journal = json.loads(decoded['journal.json'])
    require(journal == final_journal and journal.get('format') == 'minidregg-grain-runtime-v1'
            and journal.get('connection') == 'fenced' and journal.get('nextOperationId') == 2,
            'controller journal or attach boundary differs')
    nulls = ('pending', 'toolPending', 'providerPending', 'child', 'settlementDue', 'parentHold',
             'toolHold', 'dispatchPending', 'dispatchHold', 'dispatchAttempt', 'applicationApiAttempt',
             'providerHold', 'providerAttempt', 'providerSettlement', 'foregroundAttempt',
             'birthOperation', 'birthPending', 'workspaceAttempt', 'roomAttempt', 'workspaceBirth',
             'managedLawGeneration', 'hermesSession', 'promptWitness')
    lists = ('applicationApiHistory', 'providerReplays', 'foregroundHistory', 'publicationReceipts',
             'bornResources', 'workspaceProposals', 'roomResolutions', 'workspaceResolutions',
             'reconciliationLog', 'priorHermesSessions', 'unresolvedExternal')
    require(all(name in journal and journal[name] is None for name in nulls)
            and all(journal.get(name) == [] for name in lists)
            and journal.get('birthNextOrdinal') == {} and journal.get('hardReconnectPending') is False
            and journal.get('providerPromptRequests') == 0,
            'controller has pending or completed work beyond the refused attach')
    attempt = json.loads(decoded['query-0000000000000001/attempt/attempt.json'])
    require(attempt.get('format') == 'minidregg-resource-client-attempt-v1'
            and attempt.get('operation') == 'query', 'first operation is not the unsealed parent query')
    return {'boundary': 'definite-pre-tool-session-refusal', 'request_id': request_id,
            'store': store, 'journal_sha256': exported['files']['journal.json']['sha256'],
            'controller_files': {name: entry['sha256'] for name, entry in exported['files'].items()},
            'birth_or_application_attempt': False, 'permits_resend': False,
            'requires': ['fresh fixed-installer export with stopped-service identities',
                         'preserve null-operation client receipt; no native foreground record exists to ACK',
                         'separately admitted owner-policy repair',
                         'qualified native config transition',
                         'new tool-id only after supported attach/reconciliation']}


def validate_run_acl(owner, mode, operator, controller, acl):
    require(type(controller) is int and controller > 0 and controller != operator,
            'installed controller identity malformed')
    expected = ['user::rwx', f'user:{controller}:--x', 'group::---', 'mask::--x', 'other::---']
    require(owner == operator and mode == 0o710 and acl.splitlines() == expected,
            'retained run ACL differs from exact installed-controller traversal')


def retained_run_custody(run):
    meta = run.lstat()
    require(stat.S_ISDIR(meta.st_mode), 'retained run is not a directory')
    world = read(run / 'world-identity.json')
    require(re.fullmatch('[0-9a-f]{16}', world['store']), 'retained Store identity malformed')
    created = read(run / 'agent-lifetime/controller-create.json')
    reservation = Path('/etc/mini-spk-controller-reservations') / (world['store'] + '.json')
    reserved_meta = reservation.lstat()
    require(stat.S_ISREG(reserved_meta.st_mode) and reserved_meta.st_uid == 0
            and stat.S_IMODE(reserved_meta.st_mode) == 0o644 and reserved_meta.st_nlink == 1,
            'controller reservation custody differs')
    reserved = read(reservation)
    require(reserved.get('protocol') == 'mini-spk-controller-namespace-v1'
            and reserved.get('store') == created.get('store') == world['store']
            and reserved.get('operatorUid') == created.get('operatorUid') == os.getuid()
            and reserved.get('controllerUid') == created.get('controllerUid'),
            'installed controller reservation differs')
    result = subprocess.run(['/usr/bin/getfacl', '-cpn', '--', str(run)], capture_output=True,
                            text=True, check=True, timeout=5)
    require(len(result.stdout) <= 4096 and result.stderr == '', 'run ACL observation differs')
    acl = result.stdout.rstrip('\n')
    validate_run_acl(meta.st_uid, stat.S_IMODE(meta.st_mode), os.getuid(), created['controllerUid'], acl)
    return {'path': str(run), 'owner': meta.st_uid, 'mode': stat.S_IMODE(meta.st_mode),
            'controller_uid': created['controllerUid'], 'acl': acl,
            'reservation_sha256': sha(reservation)}


def stopped_services(run, store):
    for name in ('operator.pid', 'participant.pid'):
        require(not (run / 'world/sock' / name).exists(), 'Store service remains present')
    observed = {}
    for name in ('operator/host.sock', 'participant/host.sock'):
        path = run / 'world/sock' / name
        require(not path.is_symlink(), 'retained service socket is linked')
        if path.exists():
            meta = path.lstat()
            require(stat.S_ISSOCK(meta.st_mode) and meta.st_uid == os.getuid()
                    and stat.S_IMODE(meta.st_mode) == 0o600, 'retained socket custody differs')
            with socket.socket(socket.AF_UNIX, socket.SOCK_STREAM) as probe:
                probe.settimeout(1)
                try:
                    probe.connect(str(path))
                except ConnectionRefusedError:
                    observed[str(path)] = {'device': meta.st_dev, 'inode': meta.st_ino,
                                           'state': 'connection-refused-no-bytes'}
                else:
                    raise ValueError('Store socket still has a listener')
    units = [f'mini-spk-controller-{store}.service'] + [
        f'mini-spk-controller-{kind}-{store}.{suffix}'
        for kind in ('proxy', 'consent') for suffix in ('socket', 'service')]
    for unit in units + [f'mini-spk-broker@{store}.service']:
        user = ['--user'] if unit.startswith('mini-spk-broker@') else []
        result = subprocess.run(['systemctl', *user, 'show', unit, '--no-pager',
                                 '-p', 'Id', '-p', 'ActiveState', '-p', 'MainPID'],
                                check=True, capture_output=True, text=True, timeout=15)
        fields = dict(line.split('=', 1) for line in result.stdout.splitlines() if '=' in line)
        require(fields.get('Id') == unit and fields.get('ActiveState') == 'inactive'
                and fields.get('MainPID', '0') == '0', 'service is not stopped: ' + unit)
        observed[unit] = fields
    return observed


def resume_prepared_archive(output, current, source_manifest, check_only):
    """Resume only a durable backup stopped at the source-manifest check."""
    require({p.name for p in output.iterdir()} == {'prepared.json', 'prior', 'bin', 'recovery-input-sha256.txt'},
            'prepared continuation has a newer repair or attempt')
    old = read(output / 'prepared.json')
    for key in ('run', 'store', 'boundary', 'original_inputs', 'original_binaries', 'native_files_before',
                'run_custody', 'stopped_services', 'store_before', 'native_profile_sha256', 'host_config_sha256'):
        require(old.get(key) == current.get(key), 'prepared boundary changed: ' + key)
    for name, digest in old['prior_files'].items():
        relative = Path(name)
        require(not relative.is_absolute() and '..' not in relative.parts
                and not (output / 'prior' / relative).is_symlink()
                and sha(output / 'prior' / relative) == digest, 'durable prepared archive differs')
    actual = {str(p.relative_to(output / 'prior')) for p in (output / 'prior').rglob('*') if p.is_file()}
    require(actual == set(old['prior_files']), 'prepared archive file set differs')
    for original, copy in old['store_snapshot'].items():
        require(Path(copy).is_relative_to(output / 'prior') and sha(Path(copy)) == current['store_before'][original],
                'prepared Store snapshot differs')
    require({p.name for p in (output / 'bin').iterdir()} == {'grain-runtime'}, 'prepared binary set differs')
    runtime = output / 'bin/grain-runtime'
    meta = runtime.lstat()
    require(stat.S_ISREG(meta.st_mode) and meta.st_uid == os.getuid() and meta.st_nlink == 1
            and stat.S_IMODE(meta.st_mode) == 0o500, 'prepared runtime custody differs')
    sources = manifest(source_manifest)
    runtimes = [digest for name, digest in sources.items() if Path(name).name == 'grain-runtime']
    require(runtimes == [sha(runtime)], 'prepared runtime is not the new qualified input')
    partial = output / 'recovery-input-sha256.txt'
    manifest(partial)
    failed_path = Path(old['recovery_source']).parent / 'failed-launch.json'
    failed = read(failed_path)
    require(failed.get('schema') == 'mini-oracle-session-manifest-refusal-v1'
            and failed.get('repairs_begun') is False and failed.get('request_begun') is False
            and failed.get('prepared_sha256') == sha(output / 'prepared.json')
            and failed.get('partial_manifest_sha256') == sha(partial), 'manifest-refusal evidence differs')
    receipt = {'schema': 'mini-oracle-prepared-session-resume-v1', 'run': current['run'], 'store': current['store'],
               'prepared_sha256': sha(output / 'prepared.json'), 'partial_manifest_sha256': sha(partial),
               'failed_launch_receipt': str(failed_path), 'failed_launch_sha256': sha(failed_path),
               'source': current['recovery_source'], 'source_files': sources,
               'source_manifest_sha256': sha(source_manifest), 'runtime_sha256': sha(runtime),
               'existing_backup_reused': True, 'repeated_phases': [],
               'execution_manifest': str(output / 'source-resume-1-input-sha256.txt')}
    if check_only:
        return {**receipt, 'checked': True}
    fd = os.open(output / 'source-resume-1.json', os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o600)
    with os.fdopen(fd, 'wb') as sink:
        sink.write((json.dumps(receipt, indent=2) + '\n').encode()); sink.flush()
    return output


def prepare_session(run, spk, inventory, benchmark, repo, exported_path, resume_manifest=None, check_only=False,
                    observe_only=False):
    """Snapshot the exact failed attach before separately admitted repairs.

    Call only with a fresh fixed-installer export. No native operation, config
    change, result acknowledgment, tool retry, or service start happens here.
    """
    first = run / 'continuations/controller-create-1'
    old = read(first / 'prepared.json')
    require(read(run / 'exit.json') == old['prior_exit'] ==
            {'execution_exit': 1, 'cleanup_exit': 0, 'namespace_preserved': True},
            'original failure receipt differs')
    require(read(first / 'exit.json') == {'execution_exit': 1, 'cleanup_exit': 1, 'namespace_preserved': True},
            'not the preserved failed-attach continuation')
    for name, digest in old['prior_files'].items():
        relative = Path(name)
        require(not relative.is_absolute() and '..' not in relative.parts
                and sha(first / 'prior' / relative) == digest, 'first failure archive differs')
    world = read(run / 'world-identity.json')
    require(re.fullmatch('[0-9a-f]{16}', world['store']) and old['store'] == world['store']
            and old['run'] == str(run), 'retained Store identity differs')
    root = Path('/var/lib/mini-spk-worlds') / world['store']
    require(str(root) == world['root'], 'world path differs')
    agent = run / 'agent-lifetime'
    created = read(agent / 'controller-create.json')
    require(created.get('store') == world['store'] and created.get('resumedPendingCreation') is True
            and created.get('controllerUid') == old['controller_uid'], 'controller identity differs')
    refusal = session_refusal((agent / 'session-birth.request-id').read_text().strip(),
                              read(agent / 'session-birth.result.json'),
                              read(agent / 'controller-final-journal.json'),
                              read(exported_path), world['store'])
    for name in ('session-birth.retained-result.json', 'session-birth.ack.json', 'issued-grant.json',
                 'activation.json', 'probe', 'native-prepare-worker-policy', 'native-prepare-bootstrap-dispatch'):
        require(not (agent / name).exists(), 'work beyond the refused attach exists: ' + name)
    ev = run / 'world/evidence'
    require(not list(ev.glob('start-*.cmd')), 'a START was already attempted')
    for phase in ('store', 'birth-a', 'install-a', 'birth-b', 'install-b', 'share-a'):
        for suffix in ('cmd', 'stdout', 'stderr', 'exit', 'seconds'):
            name = f'world/evidence/{phase}.{suffix}'
            require(sha(run / name) == old['prior_files'][name], 'successful phase changed: ' + name)
    inputs = manifest(run / 'input-sha256.txt')
    binaries = manifest(run / 'binary-sha256.txt')
    for path in (spk, inventory, benchmark):
        require(inputs.get(str(path)) == sha(path), 'original input identity differs')
    profile_result = read(ev / 'profile-result.json')
    state = Path(profile_result['stateRoot'])
    require(state == root / world['store'] / 'host', 'native state root differs')
    profile_path = Path(profile_result['profilePath'])
    require(profile_path == state / 'grain-host.json', 'native profile path differs')
    profile = read(profile_path)
    host_config = run / 'world/store/base/workroom/deployment/pinned-config.json'
    config_sha = sha(host_config)
    require(config_sha == old['prior_files']['world/sock/operator/host.config']
            and profile_result.get('miniConfig') == profile.get('miniConfig') == str(host_config)
            and profile_result.get('miniConfigSha256') == profile.get('miniConfigSha256') == config_sha
            and profile.get('miniHost') == str(run / 'bin/minidregg-host')
            and profile.get('miniHostSha256') == sha(run / 'bin/minidregg-host')
            and profile.get('spkHost') == str(run / 'bin/spk-host')
            and profile.get('spkHostSha256') == sha(run / 'bin/spk-host'), 'native profile/config pins differ')
    actual = {str(p.relative_to(state)): sha(p) for p in (state / 'apps').rglob('*') if p.is_file()}
    require(actual == old['native_files_before'], 'native install/START state changed')
    revision = root / 'spk/public-data' / ('sha256-' + sha(inventory))
    require(not revision.is_symlink() and sha(revision / 'inventory.json') == sha(inventory),
            'published inventory differs')
    custody = retained_run_custody(run)
    services = stopped_services(run, world['store'])
    output = run / 'continuations/session-refusal-1'
    if not observe_only:
        require(output.is_dir() if resume_manifest is not None else not output.exists(),
                'session continuation directory does not match selected boundary')
    workroom = run / 'world/store/base/workroom'
    store_files = list((workroom / 'store').rglob('*'))
    require(all(not p.is_symlink() and p.is_file() for p in store_files)
            and {p.name for p in store_files} == {'forward-link.sqlite3'},
            'stopped logical Store file set differs')
    logical = [*store_files, workroom / 'store.head-anchor']
    require(sum(p.stat().st_size for p in logical) <= 64 * 1024 * 1024, 'Store snapshot exceeds bound')
    before = {str(p): sha(p) for p in logical}
    value = {'schema': 'mini-oracle-session-continuation-v1', 'run': str(run), 'store': world['store'],
             'boundary': refusal, 'prior_continuation': str(first), 'recovery_source': str(repo),
             'original_inputs': inputs, 'original_binaries': binaries, 'native_files_before': actual,
             'run_custody': custody, 'stopped_services': services, 'store_before': before, 'repeated_phases': [],
             'failed_request_acknowledged': False,
             'ack_scope': 'null operation has no retained native foreground record; preserve client receipt only',
             'source_repair_phases': ['worker-policy', 'bootstrap-dispatch-enrollment'],
             'physical_repair_phases': ['consent-storage', 'controller-runtime-upgrade'],
             'fresh_export_sha256': sha(exported_path), 'native_profile_sha256': sha(profile_path),
             'host_config_sha256': config_sha}
    if observe_only:
        return value
    if resume_manifest is not None:
        return resume_prepared_archive(output, value, resume_manifest, check_only)
    if check_only:
        return {**value, 'checked': True}
    output.mkdir(mode=0o700)
    prior = output / 'prior'
    prior.mkdir(mode=0o700)
    names = ['exit.json', 'input-sha256.txt', 'binary-sha256.txt', 'native-state.tar',
             'world-identity.json', 'publication.json', 'cleanup.log', 'broker.log']
    for directory in (agent, first, run / 'world/sock'):
        names += [str(p.relative_to(run)) for p in directory.rglob('*') if p.is_file()]
    require(all(not (run / name).is_symlink() for name in names)
            and sum((run / name).stat().st_size for name in names) <= 64 * 1024 * 1024,
            'continuation archive exceeds bound or contains symlink')
    for name in names:
        target = prior / name
        target.parent.mkdir(parents=True, exist_ok=True, mode=0o700)
        shutil.copyfile(run / name, target)
    shutil.copyfile(exported_path, prior / 'fresh-controller-export.json')
    shutil.copyfile(profile_path, prior / 'native-profile.json')
    shutil.copyfile(host_config, prior / 'host-config.json')
    require(sha(prior / 'native-profile.json') == value['native_profile_sha256']
            and sha(prior / 'host-config.json') == config_sha, 'profile/config snapshot differs')
    for source in logical:
        shutil.copyfile(source, prior / ('logical-' + source.name))
    require(before == {str(p): sha(p) for p in logical}, 'Store changed during snapshot')
    value['store_snapshot'] = {str(p): str(prior / ('logical-' + p.name)) for p in logical}
    require(all(sha(Path(target)) == before[source] for source, target in value['store_snapshot'].items()),
            'Store snapshot differs')
    value['archived_original_paths'] = {str(run / name): {'path': str(prior / name),
                                      'sha256': sha(prior / name)} for name in names}
    value['prior_files'] = {str(p.relative_to(prior)): sha(p) for p in prior.rglob('*') if p.is_file()}
    for path in prior.rglob('*'):
        path.chmod(0o500 if path.is_dir() else 0o400)
    prior.chmod(0o500)
    fd = os.open(output / 'prepared.json', os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_CLOEXEC, 0o600)
    with os.fdopen(fd, 'wb') as sink:
        sink.write((json.dumps(value, indent=2) + '\n').encode())
        sink.flush()
    return output


def repair_checkpoint(run, spk, inventory, benchmark, repo, exported, status_path, failure_path,
                      output, check_only=False):
    """Seal the observed transport boundary; no source operation is replayable.

    Physical completion is joined to the fixed installer's current status. The
    logical Store and controller must still be exactly at the old null-operation
    refusal. Supporting later source boundaries requires their native outcomes,
    not merely another phase name or a successful shell exit.
    """
    verify_lock(run)
    current = prepare_session(run, spk, inventory, benchmark, repo, exported, observe_only=True)
    old = run / 'continuations/session-refusal-1'
    prepared = read(old / 'prepared.json')
    for key in ('run', 'store', 'boundary', 'original_inputs', 'original_binaries', 'native_files_before',
                'run_custody', 'store_before', 'native_profile_sha256', 'host_config_sha256'):
        require(prepared[key] == current[key], 'post-repair boundary changed: ' + key)
    for name, digest in prepared['prior_files'].items():
        require(sha(old / 'prior' / name) == digest, 'prior session archive differs')
    failure = read(failure_path)
    require(failure.get('schema') == 'mini-oracle-physical-repair-service-failure-v1'
            and failure.get('run') == str(run) and failure.get('store') == current['store']
            and failure.get('failed_phase') == 'services'
            and failure.get('physical_repairs_completed') == ['consent-storage', 'controller-runtime-upgrade']
            and failure.get('exit') == read(old / 'exit.json') ==
                {'execution_exit': 1, 'cleanup_exit': 0, 'namespace_preserved': True}
            and all(failure.get(key) is False for key in ('source_policy_started', 'native_enrollment_started',
                                                         'new_session_tool_started', 'start_attempted')),
            'predecessor is not the definite pre-source service failure')
    for name, digest in failure['files'].items():
        require(sha(Path(name)) == digest, 'failed execution evidence changed')
    storage, runtime, status = read(old / 'consent-storage.json'), read(old / 'runtime-upgrade.json'), read(status_path)
    require(status.get('store') == storage.get('store') == runtime.get('store') == current['store']
            and status.get('stopped') is True and status.get('controllerUid') == current['run_custody']['controller_uid']
            and status.get('stageSha256') == runtime.get('stageSha256')
            and status.get('runtimeSha256') == runtime.get('runtimeSha256') == sha(old / 'bin/grain-runtime')
            and runtime.get('previousRuntimeSha256') == sha(run / 'bin/grain-runtime')
            and status.get('controllerConfigSha256') == sha(run / 'agent-lifetime/controller-stage/controller.json')
            # status deliberately exposes raw stage.consent; the repair receipt
            # additionally renders fixed unit/UID/path metadata. The complete
            # root-retained stage SHA is joined above, without projecting it.
            and set(status.get('consent', {})) == {'configSha256', 'providerSha256', 'storage'}
            and status['consent'] == {key: storage.get('consent', {}).get(key)
                                      for key in ('configSha256', 'providerSha256', 'storage')},
            'installed physical repair pins differ')
    require('publicListener' not in status, 'public listener already registered; inspect its exact phase outcome')
    receipts = {str(path): sha(path) for path in (old / 'prepared.json', old / 'consent-storage.json',
        old / 'runtime-upgrade.json', old / 'exit.json', failure_path, status_path, exported)}
    checkpoint = {'schema': 'mini-oracle-phase-checkpoint-v1', 'run': str(run), 'store': current['store'],
        'boundary': 'after-physical-repairs-before-source', 'next_phase': 'public-listener',
        'completed_phases': ['consent-storage', 'controller-runtime-upgrade'], 'receipts': receipts,
        'observed_state': current, 'installer_state': status, 'repeated_source_phases': [],
        'predecessor': str(old), 'original_request_id': current['boundary']['request_id']}
    if check_only:
        return checkpoint
    require(output.parent == run / 'checkpoints', 'checkpoint output must be inside fixed run checkpoints')
    output.parent.mkdir(mode=0o700, exist_ok=True)
    durable_json(output, checkpoint)
    return output


def begin_checkpoint(checkpoint_path, spk, inventory, benchmark, repo, exported, status_path, source_manifest,
                     check_only=False):
    checkpoint = read(checkpoint_path)
    run = Path(checkpoint['run'])
    verify_lock(run)
    require(checkpoint.get('schema') == 'mini-oracle-phase-checkpoint-v1'
            and checkpoint.get('boundary') == 'after-physical-repairs-before-source'
            and checkpoint.get('next_phase') == 'public-listener'
            and checkpoint.get('completed_phases') == ['consent-storage', 'controller-runtime-upgrade']
            and checkpoint.get('repeated_source_phases') == [], 'unsupported checkpoint boundary')
    require(checkpoint_path.parent == run / 'checkpoints' and not checkpoint_path.is_symlink(),
            'checkpoint path differs')
    for name, digest in checkpoint['receipts'].items():
        require(sha(Path(name)) == digest, 'checkpoint predecessor evidence changed')
    current = prepare_session(run, spk, inventory, benchmark, repo, exported, observe_only=True)
    for key in ('run', 'store', 'boundary', 'original_inputs', 'original_binaries', 'native_files_before',
                'run_custody', 'stopped_services', 'store_before', 'native_profile_sha256', 'host_config_sha256'):
        require(current[key] == checkpoint['observed_state'][key], 'checkpoint state changed: ' + key)
    require(read(status_path) == checkpoint['installer_state'], 'checkpoint installer state changed')
    sources = manifest(source_manifest)
    output = run / 'continuations' / ('checkpoint-' + sha(checkpoint_path)[:16])
    require(not output.exists(), 'checkpoint already attempted; inspect its phase records')
    if check_only:
        return {'checked': True, 'checkpoint_sha256': sha(checkpoint_path), 'execution_directory': str(output)}
    output.mkdir(mode=0o700)
    prior = output / 'prior'
    prior.mkdir(mode=0o700)
    names = ['cleanup.log', 'broker.log', 'native-state.tar']
    names += [str(path.relative_to(run)) for directory in (run / 'agent-lifetime', run / 'world/sock')
              for path in directory.rglob('*') if path.is_file()]
    require(all(not (run / name).is_symlink() for name in names)
            and sum((run / name).stat().st_size for name in names) <= 64 * 1024 * 1024,
            'checkpoint archive exceeds bound or contains linked evidence')
    archived = {}
    for name in names:
        target = prior / name
        target.parent.mkdir(mode=0o700, parents=True, exist_ok=True)
        shutil.copyfile(run / name, target)
        target.chmod(0o400)
        archived[str(run / name)] = {'path': str(target), 'sha256': sha(target)}
        require(sha(run / name) == sha(target), 'checkpoint input changed during archive')
    for directory in sorted([prior, *(p for p in prior.rglob('*') if p.is_dir())],
                            key=lambda p: len(p.parts), reverse=True):
        directory.chmod(0o500)
    phases = output / 'phases'
    phases.mkdir(mode=0o700)
    durable_json(output / 'checkpoint.json', {'schema': 'mini-oracle-checkpoint-execution-v1',
        'checkpoint': str(checkpoint_path), 'checkpoint_sha256': sha(checkpoint_path), 'source': str(repo),
        'sources': sources, 'archived_original_paths': archived, 'repeated_phases': [],
        'next_phase': checkpoint['next_phase'], 'original_request_id': checkpoint['original_request_id']})
    return output


def prepare(run, spk, inventory, benchmark, repo, check_only=False):
    ev = run / 'world/evidence'
    workroom = run / 'world/store/base/workroom'
    require(read(run / 'exit.json') == {'execution_exit': 1, 'cleanup_exit': 0,
                                      'namespace_preserved': True}, 'not the definite preserved failure')
    log = run.parent / 'journey-v5.log'
    require("configuration error - unknown item 'CREATE_MAIL_SPOOL'" in log.read_text()
            and 'controller setup refused:' in log.read_text(), 'account creation refusal differs')
    require((run / 'agent-lifetime/controller-create.json').read_bytes() == b'', 'controller create already replied')
    for name in ('controller-stage.json', 'controller-stage-receipt.json', 'session-birth.request-id',
                 'session-birth.result.json', 'issued-grant.json', 'probe'):
        require(not (run / 'agent-lifetime' / name).exists(), 'controller work already began: ' + name)
    for name in ('operator.pid', 'participant.pid'):
        require(not (run / 'world/sock' / name).exists(), 'Store service remains present')
    stale_sockets = {}
    for name in ('operator/host.sock', 'participant/host.sock'):
        path = run / 'world/sock' / name
        require(not path.is_symlink(), 'retained service socket is linked')
        if path.exists():
            metadata = path.lstat()
            require(stat.S_ISSOCK(metadata.st_mode) and stat.S_IMODE(metadata.st_mode) == 0o600
                    and metadata.st_uid == os.getuid(), 'retained socket custody differs')
            with socket.socket(socket.AF_UNIX, socket.SOCK_STREAM) as probe:
                probe.settimeout(1)
                try:
                    probe.connect(str(path))
                except ConnectionRefusedError:
                    stale_sockets[str(path)] = {'device': metadata.st_dev, 'inode': metadata.st_ino,
                                                'observed': 'connection-refused-without-sending-bytes'}
                else:
                    raise ValueError('Store socket still has a listener')
    phases = ('store', 'birth-a', 'install-a', 'birth-b', 'install-b', 'share-a')
    for name in phases:
        require((ev / (name + '.exit')).read_text().strip() == '0', 'prior phase did not complete: ' + name)
    require(not list(ev.glob('start-*.cmd')), 'a START was already attempted')
    inputs = manifest(run / 'input-sha256.txt')
    binaries = manifest(run / 'binary-sha256.txt')
    for path in (spk, inventory, benchmark):
        require(inputs.get(str(path)) == sha(path), 'original input identity differs')
    preserved = manifest(run / 'failure-store-preservation.sha256')
    require(set(preserved) == {str(workroom / 'store/forward-link.sqlite3'),
                              str(workroom / 'store.head-anchor')}, 'stopped Store snapshot differs')
    world = read(run / 'world-identity.json')
    root = Path('/var/lib/mini-spk-worlds') / world['store']
    require(str(root) == world['root'], 'world path differs')
    profile = read(ev / 'profile-result.json')
    state = Path(profile['stateRoot'])
    require(state == root / world['store'] / 'host' and profile['miniConfig'] == str(workroom / 'deployment/pinned-config.json')
            and profile['miniConfigSha256'] == sha(Path(profile['miniConfig'])), 'profile identity differs')
    for app, letter in (('9101', 'a'), ('9201', 'b')):
        installed = read(ev / f'install-{letter}.stdout')
        require(installed.get('protocol') == 'mini-spk-grain-install-v2'
                and installed.get('app') == app and installed.get('store') == world['store']
                and installed.get('rawSha256') == sha(spk)
                and installed.get('completion') == read(state / 'apps' / app / 'install/install-completed-v2.json'),
                'retained native install completion differs')
        require(not list((state / 'apps' / app).glob('g[0-9]*')), 'native START generation exists')
    native_files = {}
    with tarfile.open(run / 'native-state.tar') as archive:
        require(len(archive.getmembers()) <= 2048
                and sum(item.size for item in archive.getmembers()) <= 64 * 1024 * 1024,
                'native archive exceeds this bounded continuation')
        for item in archive.getmembers():
            if item.isdir():
                continue
            relative = Path(item.name)
            require(item.isfile() and not relative.is_absolute() and '..' not in relative.parts
                    and relative.parts[0] == 'apps', 'native archive shape differs')
            digest = hashlib.sha256(archive.extractfile(item).read()).hexdigest()
            require(sha(state / relative) == digest, 'native record changed: ' + item.name)
            native_files[item.name] = digest
    actual = {str(p.relative_to(state)) for p in (state / 'apps').rglob('*') if p.is_file()}
    require(actual == set(native_files), 'native record set changed')
    publication = read(run / 'publication.json')
    revision = root / 'spk/public-data' / ('sha256-' + sha(inventory))
    require(publication.get('inventory_sha256') == sha(inventory)
            and publication.get('directory') == str(revision)
            and not revision.is_symlink() and sha(revision / 'inventory.json') == sha(inventory),
            'published inventory identity differs')
    route = read(ev / 'share-a.stdout')
    require(route.get('protocol') == 'mini-spk-grain-route-v1' and route.get('app') == '9101'
            and route.get('ticket') == '9120' and route.get('kind') == 'api'
            and route.get('signedApiPath') == '/', 'retained receiving share differs')
    reservation_path = Path('/etc/mini-spk-controller-reservations') / (world['store'] + '.json')
    reservation = read(reservation_path)
    output = run / 'continuations/controller-create-1'
    require(not output.exists(), 'controller continuation already attempted')
    if check_only:
        return {'checked': True, 'store': world['store'], 'controller_uid': reservation['controllerUid'],
                'boundary': 'after-definite-share-before-any-START', 'repeated_phases': []}
    output.parent.mkdir(mode=0o700, exist_ok=True)
    output.mkdir(mode=0o700)
    prior = output / 'prior'
    prior.mkdir(mode=0o700)
    names = ['exit.json', 'input-sha256.txt', 'binary-sha256.txt', 'native-state.tar',
             'failure-store-preservation.sha256', 'world-identity.json', 'publication.json',
             'agent-lifetime/controller-create.json', 'world/evidence/journey.log', 'cleanup.log', 'broker.log']
    names += [str(p.relative_to(run)) for p in (run / 'world/sock').rglob('*') if p.is_file()]
    names += [name for name in ('residents.log',) if (run / name).is_file()]
    names += [str(p.relative_to(run)) for name in (*phases, 'services') for p in ev.glob(name + '.*') if p.is_file()]
    for name in names:
        target = prior / name
        target.parent.mkdir(mode=0o700, parents=True, exist_ok=True)
        shutil.copyfile(run / name, target)
    shutil.copyfile(log, prior / 'journey-v5.log')
    files = list((workroom / 'store').rglob('*'))
    require(all(not p.is_symlink() for p in files)
            and sum(p.stat().st_size for p in files if p.is_file()) <= 64 * 1024 * 1024,
            'stopped Store copy exceeds this bounded recovery')
    shutil.copytree(workroom / 'store', prior / 'logical-store')
    shutil.copyfile(workroom / 'store.head-anchor', prior / 'logical-store.head-anchor')
    require(sha(prior / 'logical-store/forward-link.sqlite3') == preserved[str(workroom / 'store/forward-link.sqlite3')]
            and sha(prior / 'logical-store.head-anchor') == preserved[str(workroom / 'store.head-anchor')], 'Store copy differs')
    manifest(run / 'failure-store-preservation.sha256')
    prior_files = {str(p.relative_to(prior)): sha(p) for p in prior.rglob('*') if p.is_file()}
    for p in prior.rglob('*'):
        p.chmod(0o500 if p.is_dir() else 0o400)
    prior.chmod(0o500)
    value = {'schema': 'mini-oracle-controller-continuation-v1', 'boundary': 'after-definite-share-before-any-START',
             'run': str(run), 'recovery_source': str(repo), 'store': world['store'],
             'controller_uid': reservation['controllerUid'], 'reservation_sha256': sha(reservation_path),
             'prior_exit': read(prior / 'exit.json'), 'prior_files': prior_files,
             'archived_original_paths': {str(run / name): {'path': str(prior / name), 'sha256': prior_files[name]}
                                         for name in names},
             'original_inputs': inputs, 'original_binaries': binaries, 'native_files_before': native_files,
             'store_before': preserved, 'repeated_phases': [],
             'stale_service_sockets': stale_sockets,
             'store_snapshot': {str(workroom / 'store/forward-link.sqlite3'): str(prior / 'logical-store/forward-link.sqlite3'),
                                str(workroom / 'store.head-anchor'): str(prior / 'logical-store.head-anchor')},
             'supported_services_to_restart': ['broker', 'operator', 'participant'],
             'controller_recovery_verb': 'controller-resume-create'}
    (output / 'prepared.json').write_text(json.dumps(value, indent=2) + '\n')
    return output


if __name__ == '__main__':
    os.umask(0o077)
    args = sys.argv[1:]
    if args[:1] == ['--locked-exec']:
        require(len(args) >= 4, 'locked execution requires run and command')
        locked_exec(Path(args[1]), args[2:])
    if args[:1] == ['--verify-lock']:
        require(len(args) == 2, 'lock check requires run')
        verify_lock(Path(args[1]))
        sys.exit(0)
    if args[:1] == ['--phase']:
        require(len(args) >= 5, 'phase record requires run, directory, name and action')
        verify_lock(Path(args[1]))
        phase_record(Path(args[2]), args[3], args[4], args[5:])
        sys.exit(0)
    if args[:1] in (['--seal-checkpoint'], ['--begin-checkpoint']):
        target = repair_checkpoint if args[0] == '--seal-checkpoint' else begin_checkpoint
        check = args[1:2] == ['--check-only']
        value = target(*map(Path, args[2:] if check else args[1:]), check_only=check)
        print(json.dumps(value) if check else value)
        sys.exit(0)
    if args[:1] == ['--check-session-custody']:
        require(len(args) == 2, 'session custody requires exactly one run path')
        print(json.dumps(retained_run_custody(Path(args[1]))))
        sys.exit(0)
    session = args[:1] == ['--session-refusal']
    if session:
        args = args[1:]
    check = args[:1] == ['--check-only']
    target = prepare_session if session else prepare
    value = target(*map(Path, args[1:] if check else args), check_only=check)
    print(json.dumps(value) if check else value)
