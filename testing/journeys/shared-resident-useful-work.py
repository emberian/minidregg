#!/usr/bin/env python3
"""Fair multi-author resident completion/recovery on a supplied existing Store.

Consumes platform-inputs.json and exact archived roles; never bootstraps a world,
starts/stops its Store, enrolls members, or seeds runtime journals. Request authors,
the provider witness and the chat room come from explicit inventory names, never
from positions. Source birth, signed delegations, ordinary room/summon/dispatch,
actual MCP/SQLite/SSE work, SIGKILL driver cut, late exact reply, source delivery
replay and a controller restart are retained. Provider is a scripted local fixture,
no paid calls.

The run is a journal of named steps under controllers/TASK/receiving/progress.json.
A finished step is never repeated. A step that started without a recorded outcome
is decided only from durable native evidence (a retained exact attempt, a signed
room read, or the artifact the source command publishes last); otherwise the run
stops and names it. Nothing here clears unknown custody or authors a second effect.
"""
import argparse, concurrent.futures, fcntl, hashlib, json, os, pathlib, pwd, re, signal, socket as net_socket, subprocess, sys, threading, time

PROGRESS = 'mini-resident-receiving-progress-v2'
PHASES = ('preflight', 'birth', 'tool-workspace', 'room', 'capture', 'program', 'registration', 'summon', 'requests',
          'provider', 'config', 'controller', 'cut', 'recover', 'verify', 'replay', 'service-restart', 'continuous', 'retain')
CALIBRATION_ROWS = 8
WAITING = 75  # exit status: a declared external input (capture, root copy, root registration) is not present yet


class Unknown(RuntimeError):
    """A native outcome is not established; only its exact native call may resume."""


class Refused(RuntimeError):
    """A definite refusal or a failed precondition."""


class Waiting(RuntimeError):
    """An external lane/root input is absent; rerun with --resume when it exists."""


def sha(data):
    return hashlib.sha256(data).hexdigest()


def digest(path):
    return sha(pathlib.Path(path).read_bytes())


def load(path):
    return json.loads(pathlib.Path(path).read_text())


def publish(path, data, mode=0o600):
    """Atomic private publication with file and directory fsync."""
    path = pathlib.Path(path)
    temporary = path.with_name('.' + path.name + '.new')
    fd = os.open(temporary, os.O_WRONLY | os.O_CREAT | os.O_TRUNC | os.O_NOFOLLOW, mode)
    try:
        os.fchmod(fd, mode)
        os.write(fd, data)
        os.fsync(fd)
    finally:
        os.close(fd)
    os.replace(temporary, path)
    fd = os.open(path.parent, os.O_RDONLY | os.O_DIRECTORY)
    try:
        os.fsync(fd)
    finally:
        os.close(fd)


def member_names(value):
    """name -> subject from runtime.json allocationNames, a members table, or a flat map."""
    if isinstance(value, dict) and isinstance(value.get('allocationNames'), dict):
        value = value['allocationNames']
    elif isinstance(value, dict) and isinstance(value.get('members'), dict):
        value = {name: row['subject'] if isinstance(row, dict) else row for name, row in value['members'].items()}
    elif isinstance(value, dict) and isinstance(value.get('members'), list):
        value = {row['name']: row['subject'] for row in value['members']}
    if not isinstance(value, dict) or not all(isinstance(k, str) and isinstance(v, str) and re.fullmatch(r'0|[1-9][0-9]*', v) for k, v in value.items()):
        raise Refused('member names must map each inventory name to a canonical decimal subject')
    return value


def select_members(inventory, names, tokens):
    """Resolve explicit names (or subjects) against the supplied inventory; positions are never used."""
    selected = []
    for token in tokens:
        subject = token if token in inventory else names.get(token)
        if subject not in inventory:
            raise Refused('selected member is not in the supplied inventory: ' + token)
        if inventory[subject].get('subject') != subject:
            raise Refused('inventory row differs from its subject key: ' + token)
        selected.append(inventory[subject])
    if len({row['subject'] for row in selected}) != len(selected):
        raise Refused('selected members must be distinct')
    return selected


def public_key_hex(seed):
    from cryptography.hazmat.primitives import serialization
    from cryptography.hazmat.primitives.asymmetric.ed25519 import Ed25519PrivateKey
    if len(seed) != 32:
        raise Refused('member signing seed must be exactly 32 bytes')
    return Ed25519PrivateKey.from_private_bytes(seed).public_key().public_bytes(
        serialization.Encoding.Raw, serialization.PublicFormat.Raw).hex()


def hold_budget(rows, seconds, held_rows, wall, turn_reserve, margin=120, safety=1.5):
    """Decide BEFORE the first prompt whether the held rows fit inside one worker lifetime.

    rows/seconds is the measured native row throughput on this world just now. The
    worker stays alive from its first native read until the gate is released, so the
    held rows plus the turn's own native work must end before the source wall time.
    """
    if rows <= 0 or seconds <= 0:
        raise Refused('no measured native row throughput')
    per_row = seconds / rows
    held = held_rows * per_row * safety
    available = wall - margin - turn_reserve
    return {'measuredRows': rows, 'measuredSeconds': round(seconds, 3), 'secondsPerRow': round(per_row, 3),
            'heldRows': held_rows, 'heldEstimateSeconds': round(held, 1), 'safety': safety, 'workerWallSeconds': wall,
            'turnReserveSeconds': turn_reserve, 'marginSeconds': margin, 'availableSeconds': available, 'fits': held <= available,
            'gateSeconds': max(1, min(1800, wall - margin))}


def service_is_fair(order, requested):
    """order: authors in the order their requests were served; requested: author -> count.

    Every request is served exactly once, and an author's (k+1)th request is served
    only after every other author has had min(k, own count) requests served.
    """
    served = {}
    for author in order:
        if author not in requested:
            return False
        turn = served.get(author, 0) + 1
        if any(served.get(other, 0) < min(turn - 1, count) for other, count in requested.items() if other != author):
            return False
        served[author] = turn
    return served == requested


def proc_identity(pid):
    process = pathlib.Path('/proc') / str(pid)
    stat = (process / 'stat').read_text().rsplit(')', 1)[1].split()
    return {'pid': pid, 'startTicks': stat[19], 'uid': process.stat().st_uid, 'state': stat[0]}


class Journal:
    def __init__(self, path):
        self.path = pathlib.Path(path)
        self.lock = threading.RLock()
        self.data = load(self.path) if self.path.exists() else {'protocol': PROGRESS, 'serial': 0, 'steps': {}, 'values': {}}
        if self.data.get('protocol') != PROGRESS:
            raise Refused('retained progress journal has another protocol')

    def save(self):
        with self.lock:
            publish(self.path, (json.dumps(self.data, indent=2) + '\n').encode())

    def serial(self):
        with self.lock:
            self.data['serial'] += 1
            self.save()
            return self.data['serial']

    def state(self, label):
        return self.data['steps'].get(label, {}).get('state')

    def begin(self, label):
        with self.lock:
            self.data['steps'][label] = {'state': 'started', 'at': time.time()}
            self.save()

    def finish(self, label, value=None, basis='returned'):
        with self.lock:
            self.data['steps'][label] = {'state': 'done', 'at': time.time(), 'value': value, 'basis': basis}
            self.save()

    def drop(self, label):
        """Forget a started step only after durable evidence proved its effect absent."""
        with self.lock:
            self.data['steps'].pop(label, None)
            self.save()

    def step(self, label, action, probe=None, replay=False):
        """Run one effect once. `probe` returns its value from durable evidence, or None.

        replay=True marks read-only or source-idempotent commands which may simply run again.
        """
        row = self.data['steps'].get(label)
        if row and row['state'] == 'done':
            return row.get('value')
        if row and row['state'] == 'started' and not replay:
            value = probe() if probe else None
            if value is None:
                raise Unknown('step ' + label + ' started earlier without a recorded outcome and durable evidence does not decide it; '
                              'inspect it (RUNBOOK recovery), then rerun with --settle ' + label + '=absent or =done')
            self.finish(label, value, 'durable-evidence')
            return value
        if row is None and probe and not replay:
            # A previous program may have completed this effect (for example a shared room that already exists).
            value = probe()
            if value is not None:
                self.finish(label, value, 'pre-existing-durable-evidence')
                return value
        self.begin(label)
        try:
            value = action()
        except Exception as error:
            with self.lock:
                self.data['steps'][label].update(ended=type(error).__name__, detail=str(error)[:2000])
                self.save()
            raise
        self.finish(label, value)
        return value

    def settle(self, label, decision):
        row = self.data['steps'].get(label)
        if not row or row['state'] != 'started':
            raise Refused('only a started step with unknown outcome can be settled: ' + label)
        if decision == 'absent':
            self.data.setdefault('settled', []).append({'step': label, 'decision': 'absent', 'at': time.time(), 'was': row})
            self.drop(label)
        elif decision == 'done':
            self.data.setdefault('settled', []).append({'step': label, 'decision': 'done', 'at': time.time()})
            self.finish(label, None, 'operator-settled')
        else:
            raise Refused('settle decision must be absent or done')


def unfinished_room_rows(journal, tag, count):
    # Started rows remain in the worklist so journaled_room_write fences them.
    return [i for i in range(count) if journal.state(f'{tag}-{i:03d}') != 'done']


def operation_result(output):
    """Read the native recovery envelope even when shell display follows it."""
    decoder = json.JSONDecoder()
    for match in re.finditer(r'\{', output):
        try:
            value, _ = decoder.raw_decode(output[match.start():])
        except ValueError:
            continue
        if isinstance(value, dict) and value.get('type') == 'minidregg-operation-recovery-v1':
            return value
    raise Unknown('native lookup did not return an exact operation recovery envelope')


def journaled_room_write(journal, label, write, operation_record=None, lookup=None, retry=None, binding=None):
    """Continue only the native immutable operation and its original signed call.

    Legacy steps without an operation record stay fenced. A retained unsigned
    record also stays unresolved: the adapter cannot create a second proposal.
    Once a call exists, native retry owns exact submission and receipt continuity.
    """
    if operation_record is None:
        return journal.step(label, write)
    path = pathlib.Path(operation_record)
    pins = journal.data['values'].setdefault('roomWriteBindings', {})
    pin = {'operationRecord': str(path), 'request': binding}
    if label in pins and pins[label] != pin:
        raise Refused('room write binding changed for ' + label)
    if label not in pins:
        if path.exists() or journal.state(label) == 'started':
            raise Unknown('unbound retained room write; keep its original evidence: ' + label)
        pins[label] = pin
        journal.save()

    def recover():
        if not path.exists():
            raise Unknown('room write has no native operation record; original submitter outcome unresolved: ' + label)
        record = load(path)
        workspace = pathlib.Path(binding['workspace']).resolve()
        attempt = pathlib.Path(record.get('attempt', ''))
        if (record.get('type') != 'minidregg-exact-operation-v1' or record.get('kind') != 'workspace'
                or record.get('identity', {}).get('workspace') != str(workspace)
                or not attempt.is_absolute() or attempt.parent != workspace / 'attempts'):
            raise Refused('native operation record belongs to another workspace or attempt')
        # The native record's request is immutable; do not recover a collision
        # at the same pathname merely because its envelope is confirmed.
        targets = record.get('binding', {}).get('request', {}).get('targets', [])
        payload = targets[0].get('payload', {}) if len(targets) == 1 else {}
        try:
            entry = json.loads(payload.get('text', ''))
        except ValueError:
            entry = {}
        if entry != {'type': 'say', 'text': binding['text']} or payload.get('to') != binding['to']:
            raise Refused('native room write request differs from the retained service binding')
        result = lookup(path)
        def checked(value):
            if (value.get('type') != 'minidregg-operation-recovery-v1'
                    or value.get('operationRecord') != str(path) or value.get('attempt') != str(attempt)):
                raise Refused('exact recovery returned another native operation')
            return value.get('status')
        status = checked(result)
        if status == 'uncertain' and (attempt / 'call.bin').is_file():
            retry(attempt)  # native retry: same bytes, same attempt, no fresh challenge
            result = lookup(path)
            status = checked(result)
        if status != 'confirmed':
            raise Unknown('native room write remains ' + str(status) + '; retain exact operation ' + str(path))
        outcome = result.get('outcome', {})
        if outcome.get('type') != 'confirmed' or outcome.get('confirmation') not in ('installed', 'replayed'):
            raise Unknown('room write recovery lacks native confirmation')
        return result

    def action():
        write(path)
        return recover()
    if path.exists() and journal.state(label) is None:
        # The service pin was fsynced before command launch. Recovery after a
        # crash between native completion and Journal.begin remains exact.
        journal.begin(label)
    return journal.step(label, action, probe=recover if journal.state(label) == 'started' else None)


def exact_payment_snapshot(workspace, lookup):
    """Account for every retained native payment, including request-status notices.

    Called after the driver and its client subprocesses ended. The native
    lookup owns confirmation; no bounded controller/feed journal decides costs.
    """
    payments = []
    for path in sorted((pathlib.Path(workspace) / 'room-operations').glob('*-payment.json')):
        record = load(path)
        result = lookup(path)
        status = result.get('status')
        if status in ('not-submitted', 'refused'):
            continue
        if (result.get('type') != 'minidregg-operation-recovery-v1' or status != 'confirmed'
                or result.get('operationRecord') != str(path) or result.get('attempt') != record.get('attempt')):
            raise Unknown('payment exact recovery unresolved: ' + str(path))
        if record.get('kind') == 'no-effect':
            continue
        if record.get('kind') != 'fleet':
            raise Refused('unexpected room payment operation kind')
        attempt = pathlib.Path(record['attempt'])
        plan = load(attempt / 'plan.json')['command']
        transfer = record['binding']['transfer']
        if plan['transfer'] != transfer:
            raise Refused('native payment plan differs from its operation binding')
        outcome = result.get('outcome', {})
        if outcome.get('type') != 'confirmed' or outcome.get('confirmation') not in ('installed', 'replayed'):
            raise Unknown('payment lacks native confirmation')
        payments.append({'operationRecord': str(path), 'operationRecordSha256': digest(path),
            'attempt': str(attempt), 'price': int(transfer['amount']), 'fee': int(plan['fee']),
            'statusNotice': re.fullmatch(r'rs[0-9]+-payment.json', path.name) is not None, 'transaction': outcome.get('transactionId')})
    return {'prices': sum(p['price'] for p in payments), 'fees': sum(p['fee'] for p in payments),
            'payments': len(payments), 'modelPayments': sum(not p['statusNotice'] for p in payments), 'paymentEvidence': payments}


def arguments(argv=None):
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument('--platform-inputs', required=True)
    p.add_argument('--base', required=True, help='root frame, e.g. /var/lib/mini-bigstep-hbox-r1')
    p.add_argument('--member-names', required=True, help='JSON with name->subject (runtime.json allocationNames or WORLD-IDENTITY members)')
    p.add_argument('--authors', required=True, help='comma separated inventory names; the first is the room founder')
    p.add_argument('--request-counts', help='comma separated addressed requests per author (default 1 each)')
    p.add_argument('--provider-witness', required=True, help='inventory name of the provider task owner (not an author)')
    p.add_argument('--room-alias', required=True)
    p.add_argument('--room-mode', required=True, choices=('create', 'existing', 'adopt'), help='create: chat new; existing: chat already present; adopt: founder adopts a supplied workroom')
    p.add_argument('--shared-document-reference', required=True)
    p.add_argument('--capture-reference', required=True)
    p.add_argument('--fixture-acp', required=True)
    p.add_argument('--fixture-provider', required=True)
    p.add_argument('--registration', required=True, help='root registrar receipt (controller-entry.py register output)')
    p.add_argument('--task', type=int, default=8997)
    p.add_argument('--prepoll-rows', type=int, default=129)
    p.add_argument('--held-rows', type=int, default=110)
    p.add_argument('--worker-wall-seconds', type=int, default=1800)
    p.add_argument('--turn-reserve-seconds', type=int, default=420, help='native time reserved for one turn before its gate')
    p.add_argument('--native-timeout-seconds', type=int, default=1800)
    p.add_argument('--capture-timeout-seconds', type=int, default=0, help='0: do not wait, exit 75 when absent')
    p.add_argument('--through', choices=PHASES, default=PHASES[-1])
    p.add_argument('--resume', action='store_true')
    p.add_argument('--settle', action='append', default=[], metavar='STEP=absent|done')
    p.add_argument('--preserve-on-success', action='store_true')
    a = p.parse_args(argv)
    a.authors = [token for token in a.authors.split(',') if token]
    a.request_counts = [int(v) for v in a.request_counts.split(',')] if a.request_counts else [1] * len(a.authors)
    if len(a.authors) < 2 or len(a.request_counts) != len(a.authors) or not all(1 <= n <= 8 for n in a.request_counts):
        p.error('at least two authors, and one request count in 1..8 for each author')
    if not 100 < a.held_rows <= 400 or not 0 <= a.prepoll_rows <= 400 or a.held_rows + a.prepoll_rows + 5 * sum(a.request_counts) + CALIBRATION_ROWS > 480:
        p.error('held rows must exceed the 100-row tail and all rows must stay inside one signed 500-row read')
    if not 300 <= a.worker_wall_seconds <= 1800 or not 60 <= a.turn_reserve_seconds < a.worker_wall_seconds:
        p.error('worker wall time is 300..1800 seconds (the source bound) and the turn reserve must be inside it')
    if not re.fullmatch(r'[A-Za-z0-9-]{1,48}', a.room_alias):
        p.error('room alias malformed')
    return a


def main(argv=None):
    a = arguments(argv)
    os.umask(0o077)
    os.nice(10)
    context_path = pathlib.Path(a.platform_inputs)
    ctx = load(context_path)
    manifest_path = pathlib.Path(ctx['manifest'])
    manifest = load(manifest_path)
    if digest(manifest_path) != ctx['identity']['manifestSha256']:
        raise Refused('supplied manifest pin differs')
    roles = ['mini', 'host', 'store', 'verifier', 'grainRuntime', 'launchGate'] + (['bwrapLauncher'] if 'bwrapLauncher' in manifest.get('sha256', {}) else [])
    for role in roles:
        if digest(manifest[role]) != manifest['sha256'][role]:
            raise Refused('source role bytes differ ' + role)
    mini, host, grain = manifest['mini'], manifest['host'], manifest['grainRuntime']
    launcher = pathlib.Path(manifest.get('bwrapLauncher') or pathlib.Path(manifest['launchGate']).parent / 'bwrap')
    if launcher.name != 'bwrap' or launcher.parent != pathlib.Path(manifest['launchGate']).parent or not os.access(launcher, os.X_OK):
        raise Refused('worker launcher must be the executable named bwrap beside the pinned launch-gate')
    base = pathlib.Path(a.base)
    node = base / 'var/lib/mini/store/node'
    config, socket, member_socket = ctx['config'], ctx['privateSocket'], ctx['publicSocket']
    genesis = load(ctx['genesis'])
    if pathlib.Path(config) != node / 'deployment/pinned-config.json':
        raise Refused('canonical shared Node/config required')
    if digest(config) != ctx['identity']['configSha256']:
        raise Refused('supplied source configuration differs')
    configured = load(config)
    owner, manager = ctx['custody']['owner'], ctx['custody']['management']
    owner_subject, tool_subject = owner['subject'], manager['subject']
    owner_key, tool_key = pathlib.Path(owner['seed']), pathlib.Path(manager['seed'])
    names = member_names(load(a.member_names))
    authors = select_members(ctx['memberInventory'], names, a.authors)
    provider_member = select_members(ctx['memberInventory'], names, [a.provider_witness])[0]
    provider_subject = provider_member['subject']
    author_subjects = [row['subject'] for row in authors]
    requested = dict(zip(author_subjects, a.request_counts))
    total_requests = sum(a.request_counts)
    if len({owner_subject, tool_subject, provider_subject, *author_subjects}) != 3 + len(authors):
        raise Refused('owner, resident, provider witness and every request author must be distinct principals')
    founder = authors[0]
    founder_subject = founder['subject']
    founder_ws, founder_home = pathlib.Path(founder['workspace']), pathlib.Path(founder['home'])
    founder_key = pathlib.Path(load(founder_ws / 'workspace.json')['key'])
    provider_key = pathlib.Path(load(pathlib.Path(provider_member['workspace']) / 'workspace.json')['key'])
    keys = {owner_subject: owner_key, tool_subject: tool_key, provider_subject: provider_key, founder_subject: founder_key}
    controller_root = base / 'var/lib/mini/controllers' / str(a.task)
    root = controller_root / 'receiving'
    state = controller_root / 'state'
    home = state / 'room-home'
    ws = state / 'resource-workspace'
    worker = controller_root / 'worker-work'
    fixture_runtime = controller_root / 'fixture-runtime'
    controller_config, resident_config = controller_root / 'controller.json', controller_root / 'resident.json'
    controller_unit = f'mini-grain-controller@{a.task}.service'
    provider_unit = f'mini-resident-fixture-provider@{a.task}.service'
    room_alias = a.room_alias
    summary_alias = f'resident-summary-{a.task}'
    program_name = f'resident-{a.task}-captured-job.txt'
    # Credential custody is the key broker's (minidregg native/mini-keys): the controller
    # names the deployment's broker client config and never a seal key or a store.
    canonical_table, canonical_broker = base / 'etc/mini/providers.json', base / 'etc/mini/keys-client.json'
    shared_document_ref = pathlib.Path(a.shared_document_reference)
    capture_path = pathlib.Path(a.capture_reference)
    registration_receipt_path = pathlib.Path(a.registration)

    # ---- no-effect structural preflight (before any directory is created) ----
    if not controller_root.is_dir() or controller_root.is_symlink() or controller_root.stat().st_uid != os.getuid() or controller_root.stat().st_mode & 0o077:
        raise Refused('root must pre-provision a private controllers/TASK directory owned by the service operator')
    if root.exists() and not a.resume:
        raise Refused('retained receiving directory exists; continue it with --resume, never start over')
    if not root.exists() and a.resume:
        raise Refused('--resume without a retained receiving directory')
    for path in (owner_key, tool_key, founder_key, provider_key):
        if path.stat().st_size != 32:
            raise Refused('signing seed must be a 32 byte file: ' + str(path))
    for path in (a.fixture_acp, a.fixture_provider, grain, mini, host):
        if not os.access(path, os.X_OK if path != a.fixture_provider else os.R_OK):
            raise Refused('required program is absent: ' + str(path))
    existing_document_ref = load(shared_document_ref)
    capture_alias = existing_document_ref['name']
    if not re.fullmatch(r'[A-Za-z0-9-]{1,64}', capture_alias) or shared_document_ref.resolve() != (founder_ws / 'refs' / (capture_alias + '.json')).resolve():
        raise Refused('supplied shared document reference is not the founder bound alias')
    existing_document_target = existing_document_ref['target']
    owner_enrollment = next(row for row in genesis['enrollments'] if row['key']['subject'] == owner_subject)
    tool_enrollment = next(row for row in genesis['enrollments'] if row['key']['subject'] == tool_subject)
    factory = ctx['authority']['factory']
    if not canonical_broker.is_file() or canonical_broker.stat().st_uid != 0 or canonical_broker.stat().st_mode & 0o022:
        raise Refused('the deployment key broker client config (root-owned) is required')
    if not registration_receipt_path.parent.is_dir():
        raise Refused('registration receipt directory absent')
    public_key_hex(founder_key.read_bytes())

    if not root.exists():
        root.mkdir(mode=0o700)
    # One process owns this receiving journal; its native subprocesses are
    # reaped before this lock is released. Exact retries remain safe after cuts.
    receiving_lock = open(root / 'receiving.lock', 'a')
    fcntl.flock(receiving_lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
    journal = Journal(root / 'progress.json')
    for item in a.settle:
        label, _, decision = item.partition('=')
        journal.settle(label, decision)
    values = journal.data['values']
    checks = load(root / 'checks.json') if (root / 'checks.json').exists() else []

    def save(name, value):
        publish(root / name, (json.dumps(value, indent=2) + '\n').encode())

    def remember(key, value):
        values[key] = value
        journal.save()
        return value

    def check(label, ok, evidence):
        checks[:] = [row for row in checks if row['check'] != label] + [{'check': label, 'passed': bool(ok), 'evidence': evidence}]
        save('checks.json', checks)
        print(('PASS ' if ok else 'FAIL ') + label, flush=True)
        if not ok:
            raise Refused('check failed: ' + label)

    def wait(label, predicate, timeout):
        end = time.monotonic() + timeout
        while time.monotonic() < end:
            try:
                value = predicate()
                if value:
                    return value
            except (OSError, ValueError, KeyError):
                pass
            time.sleep(.2)
        raise Refused('timeout: ' + label)

    timings = []

    def run(label, words, effect=False, timeout=None):
        """One client command with retained argv/stdout/stderr/timing. Nonzero never retries."""
        command = [str(x) for x in words]
        stem = f'{journal.serial():05d}-{label}'
        save(stem + '.command.json', command)
        start = time.monotonic()
        try:
            result = subprocess.run(command, capture_output=True, text=True, stdin=subprocess.DEVNULL, timeout=timeout or a.native_timeout_seconds)
        except subprocess.TimeoutExpired:
            save(stem + '.timing.json', {'seconds': time.monotonic() - start, 'clientDeadline': True})
            raise Unknown(label + ' passed the client deadline; its native outcome is unknown (' + stem + ')')
        seconds = time.monotonic() - start
        (root / (stem + '.stdout')).write_text(result.stdout)
        (root / (stem + '.stderr')).write_text(result.stderr)
        save(stem + '.timing.json', {'seconds': seconds, 'returncode': result.returncode})
        timings.append((label, seconds))
        if result.returncode:
            # Mini's typed endings: 3 is a definite refusal; 4 is undecided; 1 may follow a sent call.
            if effect and result.returncode != 3:
                raise Unknown(f'{label} ended {result.returncode} after a possible native submission ({stem}.stderr)')
            raise Refused(f'{label} refused with status {result.returncode}; retained {stem}.stderr')
        return result.stdout

    def shell_of(member):
        return [mini, 'shell', '--socket', member_socket, '--host', host, '--config', config,
                '--workspace', member['workspace'], '--home', member['home'], '--line']

    def shell(member, label, line, effect=False):
        return run(label, shell_of(member) + [line], effect=effect)

    nonce = [int(time.time_ns() % 8_000_000_000) + 1_000_000_000]

    def next_nonce():
        nonce[0] += 2
        return nonce[0]

    def mini_query(label, subject, target, capability):
        intent = {'subject': subject, 'nonce': str(next_nonce()), 'purpose': {'type': 'query', 'kind': 'object', 'target': str(target), 'view': 'resource'},
                  'grants': [{'kind': 'object', 'target': str(target), 'capability': str(capability)}]}
        stem = f'{journal.serial():05d}-{label}'
        intent_file = root / (stem + '-query-intent.json')
        intent_file.write_text(json.dumps(intent))
        attempt = root / (stem + '-query')
        run(label, [mini, 'query', '--host', host, '--config', config, '--socket', socket, '--intent', intent_file, '--key', keys[subject], '--view', 'resource', '--dir', attempt])
        view, challenge = load(attempt / 'view.json'), load(attempt / 'challenge.json')
        return view.get('cell') or view.get('page'), challenge['authorityRoot']

    def submit(label, build, signer, kind=None):
        """One signed native effect with a retained exact attempt; recovery is exact lookup only."""
        def attempt_of(n):
            return root / (label + '-attempt' + ('' if n == 1 else f'-r{n}'))

        def probe():
            sent = [attempt_of(n) for n in range(1, 9) if (attempt_of(n) / 'call.bin').exists()]
            for attempt in sent:
                try:
                    out = run(label + '-lookup', [mini, 'retry', '--attempt', attempt, '--mode', 'lookup', '--socket', socket])
                except Refused:
                    continue
                value = json.loads(out[out.index('{'):]) if '{' in out else {}
                if value.get('type') == 'confirmed':
                    return value
            if sent:
                raise Unknown('signed call for ' + label + ' was retained but exact lookup did not confirm it; ' + str(sent[-1]))
            return None  # nothing was ever signed: the effect is definitely absent

        def action():
            n = next(n for n in range(1, 9) if not attempt_of(n).exists())
            attempt = attempt_of(n)
            intent_file = root / (attempt.name + '-intent.json')
            intent_file.write_text(json.dumps(build(), indent=2))
            words = [mini, 'submit', '--host', host, '--config', config, '--socket', socket, '--intent', intent_file, '--key', keys[signer], '--dir', attempt]
            if kind:
                words.extend(['--intent-kind', kind])
            run(label, words, effect=True)
            outcome = load(attempt / 'outcome.json')
            if outcome.get('type') != 'confirmed':
                raise Unknown('native effect not confirmed; retained exact attempt ' + str(attempt))
            return outcome

        row = journal.data['steps'].get(label)
        if row and row['state'] == 'started':
            value = probe()
            if value is None:
                journal.drop(label)
            else:
                journal.finish(label, value, 'exact-lookup')
        return journal.step(label, action)

    def room_feed(label, member=None):
        """Signed 500-row room read as JSON entries (an author's own grant, public socket)."""
        member = member or founder
        output = shell(member, label, f'tail --in {room_alias} --json -n 500')
        entries = [json.loads(line) for line in output.splitlines() if line.startswith('{')]
        return [e for e in entries if isinstance(e.get('n'), int) and 'author' in e and 'sequence' in e]

    def say(member, label, line, text, to=None):
        workspace = pathlib.Path(member['workspace']).resolve()
        operation = workspace / 'operations' / f'resident-{a.task}-{label}.json'
        binding = {'workspace': str(workspace), 'room': room_alias, 'text': text, 'to': to}

        def action(path):
            if to is not None:
                # ask has no operation-record option. Its native signed room
                # read chooses Hermes; preserve that decision before recorded say.
                tariff = json.loads(run(label + '-ask-routing', [mini, 'credit', '--action', 'room',
                                       '--dir', workspace, '--room', room_alias]))
                if (tariff.get('type') != 'minidregg-room-tariff-v1' or tariff.get('authority') != 'signed-read'
                        or tariff.get('tariff', {}).get('hermes') != to):
                    raise Refused('current signed room Hermes differs from the addressed request')
            native_line = f'say --in {room_alias} --operation-record {path}'
            if to is not None:
                native_line += ' --to ' + to
            native_line += ' ' + json.dumps(text)
            shell(member, label, native_line, effect=True)

        return journaled_room_write(journal, label, action, operation,
            lambda path: operation_result(run(label + '-exact-lookup', [mini, 'credit', '--action', 'lookup-operation',
                                           '--dir', workspace, '--operation-record', path])),
            lambda attempt: run(label + '-exact-retry', [mini, 'retry', '--attempt', attempt, '--mode', 'submit',
                                                        '--socket', member_socket], effect=True),
            binding)

    def rows(tag, text, count):
        """`count` ordinary rows written concurrently, one writer per author; returns (rows, seconds)."""
        # Only this journal's acknowledged operation decides completion.
        # A visible matching row can belong to another operation, while an
        # absent row may have fallen outside the recent tail.
        todo = unfinished_room_rows(journal, tag, count)
        start = time.monotonic()

        def writer(k):
            for i in todo[k::len(authors)]:
                say(authors[k], f'{tag}-{i:03d}', f'say --in {room_alias} {text} {i:03d}', f'{text} {i:03d}')
            return True
        with concurrent.futures.ThreadPoolExecutor(max_workers=len(authors)) as pool:
            for future in [pool.submit(writer, k) for k in range(len(authors))]:
                future.result()
        seconds = time.monotonic() - start
        print(f'{tag}: {len(todo)} native rows in {seconds:.1f}s', flush=True)
        return len(todo), seconds

    def phase(name):
        if PHASES.index(name) > PHASES.index(a.through):
            save('timings.json', timings)
            print('STOPPED BEFORE ' + name + ' (--through ' + a.through + ')', flush=True)
            raise SystemExit(0)
        print('PHASE ' + name, flush=True)

    # ------------------------------------------------------------ preflight
    phase('preflight')
    operator_status = json.loads(run('native-private-operator-preflight', [mini, 'operator-status', '--socket', socket, '--host', host, '--config', config]))
    if (operator_status.get('format') != 'mini-operator-drain-v1' or operator_status.get('phase') != 'serving' or operator_status.get('admissionClosed') is not False
            or operator_status.get('hostProcessId', 0) <= 0 or operator_status.get('hostSha256') != digest(host) or operator_status.get('configSha256') != digest(config)):
        raise Refused('shared source private operator role/pins not ready')
    for member in authors + [provider_member]:
        me = json.loads(shell(member, 'member-binding', 'whoami'))
        if me.get('subject') != member['subject'] or me.get('socket') != member_socket:
            raise Refused('member workspace is not bound to this Store public socket: ' + member['subject'])
    founder_record = founder_home / 'chat/rooms' / (room_alias + '.json')
    if a.room_mode == 'existing':
        if not founder_record.exists() or load(founder_record).get('founder') != founder_subject:
            raise Refused('existing room alias is not a chat room founded by the first author')
    elif a.room_mode == 'create' and journal.state('room-create') is None and (founder_record.exists() or (founder_ws / 'refs' / (room_alias + '.json')).exists()):
        raise Refused('room alias already names something in the founder workspace; choose another alias or --room-mode existing')
    shell(founder, 'capture-destination-native-read', 'doc show ' + capture_alias)
    save('source-inputs.json', {'platformInputs': str(context_path), 'platformInputsSha256': digest(context_path), 'manifest': str(manifest_path),
                                'manifestSha256': digest(manifest_path), 'journeySha256': digest(__file__), 'roomAlias': room_alias, 'roomMode': a.room_mode,
                                'sharedDocumentReference': str(shared_document_ref), 'requested': requested,
                                'subjects': {'owner': owner_subject, 'tool': tool_subject, 'founder': founder_subject, 'authors': author_subjects, 'provider': provider_subject},
                                'workerWallSeconds': a.worker_wall_seconds, 'heldRows': a.held_rows, 'prepollRows': a.prepoll_rows})
    print('PREFLIGHT OK: no native effect has been submitted', flush=True)

    # ------------------------------------------------------------ birth
    phase('birth')
    # All caller-selected numeric values are explicit allocation, never evidence.
    caps = {k: str(a.task * 100 + i) for k, i in {'parent': 71, 'parentControl': 72, 'toolWitness': 73, 'providerWitness': 75, 'tool': 81, 'toolControl': 82,
                                                 'publication': 91, 'publicationControl': 92, 'publicationTool': 93, 'publicationRead': 94, 'provider': 101, 'providerControl': 102}.items()}
    account = {'target': owner_enrollment['accountId'], 'operationCapability': owner_enrollment['spendCapabilityId'], 'controlCapability': owner_enrollment['controlCapabilityId']}
    save('source-owner-account-hint.json', {'genesisSha256': digest(ctx['genesis']), 'subject': owner_subject, 'account': account})
    template = {'issuer': str(configured['issuer']), 'ownerBudget': str(configured['ownerBudget']), 'lifetime': str(configured['lifetime'])}

    def birth_intent():
        n = next_nonce()
        intent = {'subject': owner_subject, 'nonce': str(n), 'birth': {'genesis': genesis, 'template': template, 'creator': owner_subject, 'nonce': str(n), 'resources': [
            {'kind': 'object', 'storage': 'grain', 'target': str(a.task), 'owner': owner_subject, 'ownerCapability': caps['parent'], 'controlCapability': caps['parentControl'],
             'budget': '1000', 'workerSubjects': [tool_subject, provider_subject], 'workerGeneration': '1'},
            {'kind': 'object', 'storage': 'grain', 'target': str(a.task + 1), 'owner': tool_subject, 'ownerCapability': caps['tool'], 'controlCapability': caps['toolControl'], 'budget': '1000'},
            {'kind': 'object', 'storage': 'declared', 'target': str(a.task + 2), 'owner': owner_subject, 'ownerCapability': caps['publication'],
             'controlCapability': caps['publicationControl'], 'predicate': {'type': 'all', 'predicates': []}},
            {'kind': 'object', 'storage': 'grain', 'target': str(a.task + 3), 'owner': provider_subject, 'ownerCapability': caps['provider'], 'controlCapability': caps['providerControl'], 'budget': '300000'}],
            'sourceCapabilities': [account['operationCapability']], 'funding': [], 'feePayer': owner_subject},
            'grants': [{'kind': 'object', 'target': factory['target'], 'capability': factory['ownerCapability']},
                       {'kind': 'account', 'target': account['target'], 'capability': account['operationCapability']}]}
        if 'grainBirthTariff' in configured:
            intent['birth']['grainBirthTariff'] = {k: str(v) for k, v in configured['grainBirthTariff'].items()}
        return intent

    def delegate(label, target, parent, child, holder, verbs):
        def build():
            cell, authority = mini_query(label + '-pre', owner_subject, target, parent)
            n = next_nonce()
            return {'subject': owner_subject, 'nonce': str(n), 'purpose': {'type': 'prepare', 'draft': {'type': 'delegate-source', 'command': {
                'kind': 'object', 'domain': str(genesis['domain']), 'semantics': genesis['expectedSemantics'], 'subject': owner_subject, 'nonce': str(n + 1),
                'expectedTargetRoot': cell['root'], 'parentId': parent, 'target': str(target),
                'child': {'id': child, 'root': parent, 'parent': parent, 'issuer': str(configured['issuer']), 'holder': {'type': 'subject', 'subject': holder},
                          'targets': [str(target)], 'verbs': verbs, 'maxCost': '50000', 'notBefore': str(configured['genesisHeight']),
                          'notAfter': str(int(configured['genesisHeight']) + int(configured['lifetime']) - 1), 'issuerEpoch': genesis['issuerEpoch'],
                          'policyId': str(target), 'policyEpoch': '0', 'ancestors': [parent], 'channels': []}}}},
                'grants': [{'kind': 'object', 'target': str(target), 'capability': parent}]}
        return submit(label, build, owner_subject)

    born = submit('resident-native-birth', birth_intent, owner_subject, 'birth-intent')
    delegations = [delegate('resident-parent-tool', a.task, caps['parent'], caps['toolWitness'], tool_subject, ['observe', 'mutate']),
                   delegate('resident-parent-provider', a.task, caps['parent'], caps['providerWitness'], provider_subject, ['observe', 'mutate']),
                   delegate('resident-publication-tool', a.task + 2, caps['publication'], caps['publicationTool'], tool_subject, ['observe', 'mutate']),
                   delegate('resident-publication-read', a.task + 2, caps['publication'], caps['publicationRead'], tool_subject, ['observe'])]
    check('resident tasks born and delegated on supplied Store', born['type'] == 'confirmed' and all(d['type'] == 'confirmed' for d in delegations),
          {'birth': born, 'delegations': delegations, 'caps': caps})

    # ------------------------------------------------------------ tool-workspace
    phase('tool-workspace')
    for folder in (state, state / 'resident', home, home / 'inbox', worker, root / 'etc', root / 'keys'):
        folder.mkdir(mode=0o700, exist_ok=True)
    # Reuse the existing source-enrolled management key; init does not rotate it.
    tool_context = {'type': 'minidregg-participant-birth-context-v1', 'genesis': genesis, 'template': template,
                    'sourceCapabilities': [tool_enrollment['spendCapabilityId']], 'funding': [], 'feePayer': tool_subject,
                    'grants': [{'kind': 'object', 'target': str(configured['factoryId']), 'capability': factory['managementCapability']},
                               {'kind': 'account', 'target': tool_enrollment['accountId'], 'capability': tool_enrollment['spendCapabilityId']}]}
    save('tool-birth-context.json', tool_context)
    journal.step('resident-tool-workspace', lambda: run('resident-tool-workspace', [
        mini, 'workspace', '--action', 'init', '--no-prerotation', '--host', host, '--config', config, '--socket', socket, '--key', tool_key,
        '--subject', tool_subject, '--birth-context', root / 'tool-birth-context.json', '--dir', ws], effect=True) and True,
        lambda: True if (ws / 'workspace.json').exists() else None)
    journal.step('resident-tool-factory-ref', lambda: run('resident-tool-factory-ref', [
        mini, 'workspace', '--action', 'import', '--dir', ws, '--name', 'factory', '--kind', 'object', '--target', configured['factoryId'],
        '--observe-capability', factory['managementCapability']]) and True, lambda: True if (ws / 'refs/factory.json').exists() else None)
    journal.step('resident-tool-account-ref', lambda: run('resident-tool-account-ref', [
        mini, 'workspace', '--action', 'import', '--dir', ws, '--name', 'account', '--kind', 'account', '--target', tool_enrollment['accountId'],
        '--observe-capability', tool_enrollment['spendCapabilityId'], '--operation-capability', tool_enrollment['spendCapabilityId'],
        '--control-capability', tool_enrollment['controlCapabilityId']]) and True, lambda: True if (ws / 'refs/account.json').exists() else None)

    # ------------------------------------------------------------ room
    phase('room')
    # Source chat adopt adds the native roster to a founder's existing workroom.
    # It preserves the room people already share and their document authority.
    if a.room_mode == 'create':
        journal.step('room-create', lambda: shell(founder, 'room-create', 'chat new ' + room_alias, effect=True) and True,
                     lambda: True if founder_record.exists() and load(founder_record).get('founder') == founder_subject and load(founder_record).get('stream') else None)
    if a.room_mode == 'adopt':
        journal.step('room-adopt', lambda: shell(founder, 'room-adopt', 'chat adopt ' + room_alias, effect=True) and True,
                     lambda: True if founder_record.exists() and load(founder_record).get('founder') == founder_subject and load(founder_record).get('stream') else None)
    room_cell = load(founder_ws / 'refs' / (room_alias + '.json'))['target']
    shell(founder, 'shared-room-native-read', 'tail --in ' + room_alias + ' --json -n 1')
    for index, member in enumerate(authors[1:], 1):
        subject, member_ws, member_home = member['subject'], pathlib.Path(member['workspace']), pathlib.Path(member['home'])
        member_ref, member_record = member_ws / 'refs' / (room_alias + '.json'), member_home / 'chat/rooms' / (room_alias + '.json')
        if member_ref.exists() and load(member_ref)['target'] != room_cell:
            raise Refused('author already uses this alias for another room: ' + subject)
        joined = lambda record=member_record, ref=member_ref: True if record.exists() and load(record).get('stream') and ref.exists() else None
        if joined() and journal.state(f'room-join-{subject}') is None:
            continue  # already an ordinary member with its own stream
        invitation_path = founder_home / f'chat/invites/{room_alias}-{subject}.json'
        journal.step(f'room-invite-{subject}', lambda s=subject, i=index: shell(founder, 'room-invite', f'chat invite {room_alias} {s} author{i}', effect=True) and True,
                     lambda p=invitation_path: True if p.exists() else None)
        requests_dir = member_home / 'requests'
        requests_dir.mkdir(mode=0o700, exist_ok=True)
        invite_name = f'resident-{a.task}-{room_alias}-invite.json'
        invite_bytes = json.dumps(load(invitation_path)).encode()
        if (requests_dir / invite_name).exists() and (requests_dir / invite_name).read_bytes() != invite_bytes:
            raise Refused('another invitation file with this name exists for ' + subject)
        publish(requests_dir / invite_name, invite_bytes)
        journal.step(f'room-join-{subject}', lambda m=member, n=invite_name: shell(m, 'room-join', f'chat join {room_alias} @{n}', effect=True) and True, joined)

    # ------------------------------------------------------------ capture
    phase('capture')
    room_context = {'protocol': 'mini-resident-room-capture-request-v1', 'worldConfig': config, 'socket': member_socket, 'founderSubject': founder_subject,
                    'founderWorkspace': str(founder_ws), 'founderHome': str(founder_home), 'roomAlias': room_alias, 'roomTarget': room_cell,
                    'documentAlias': capture_alias, 'documentTarget': existing_document_target}
    if not (root / 'room-context.json').exists():
        save('room-context.json', room_context)
    elif load(root / 'room-context.json') != room_context:
        raise Refused('retained room capture request differs from current source coordinates')
    print('CAPTURE ROOM READY ' + str(root / 'room-context.json'), flush=True)
    if not capture_path.exists() and a.capture_timeout_seconds:
        try:
            wait('source app capture/document publication', capture_path.exists, a.capture_timeout_seconds)
        except Refused:
            pass
    if not capture_path.exists():
        raise Waiting('captured-document room context absent: ' + str(capture_path))
    capture = load(capture_path)
    expected = dict(room_context, protocol='mini-captured-document-room-context-v1')
    expected.pop('founderHome')
    if any(capture.get(k) != v for k, v in expected.items()):
        raise Refused('captured document coordinates differ from supplied source room')
    captured_alias, captured_target = capture['documentAlias'], capture['documentTarget']
    if not isinstance(captured_target, str) or not re.fullmatch(r'[1-9][0-9]*', captured_target):
        raise Refused('captured target malformed')
    ref = load(founder_ws / 'refs' / (captured_alias + '.json'))
    if ref['target'] != captured_target:
        raise Refused('captured target differs from native workspace reference')
    shell(founder, 'captured-document-current-read', 'doc show ' + captured_alias)
    save('captured-source-context.json', {'reference': capture, 'referenceSha256': digest(capture_path), 'nativeRef': ref})

    # ------------------------------------------------------------ program
    phase('program')
    journal.step('room-summary', lambda: shell(founder, 'room-summary',
                 f"doc new {summary_alias} 'any [ not (verb == write), subject == {founder_subject}, subject == {tool_subject} ]' --in {room_alias}", effect=True) and True,
                 lambda: True if (founder_ws / 'refs' / (summary_alias + '.json')).exists() else None)
    program_dir = founder_home / 'requests'
    program_dir.mkdir(mode=0o700, exist_ok=True)
    program_text = ('- **Inputs** (read, never write): ' + captured_alias + '\n- **Outputs** (write): ' + summary_alias +
                    '\nRead the signed current input, append a concise verified summary to ' + summary_alias + ', read it back, then reply to the addressed source request.\n')
    if (program_dir / program_name).exists() and (program_dir / program_name).read_text() != program_text:
        raise Refused('another program file with this name exists in the founder requests directory')
    publish(program_dir / program_name, program_text.encode())
    tariff_set = lambda: True if any(line.split() == ['hermes/turn', '1'] for line in shell(founder, 'room-tariff-read', f'tariff {room_alias}').splitlines()) else None
    journal.step('room-tariff', lambda: shell(founder, 'room-tariff', f'tariff {room_alias} set hermes/turn 1', effect=True) and True, tariff_set)

    # ------------------------------------------------------------ registration
    phase('registration')
    registrations = root / 'dispatch-registrations'
    registrations.mkdir(mode=0o700, exist_ok=True)
    dispatch_registration = registrations / (str(a.task) + '.json')
    # The custody check asks the Host whether the resident key is current: it needs the socket.
    registration = json.loads(run('native-resident-registration', [mini, 'hermes-handoff', '--socket', socket, '--action', 'registration', '--dir', ws,
                                                                    '--task', a.task, '--room-cell', room_cell, '--inbox', home / 'inbox']))
    if dispatch_registration.exists() and load(dispatch_registration) != registration:
        raise Refused('retained dispatch registration differs from current source custody')
    publish(dispatch_registration, json.dumps(registration).encode())
    public_registry = json.loads(run('native-public-resident-registry', [mini, 'hermes-handoff', '--socket', socket, '--action', 'registry', '--registrations', registrations]))
    eligible = [row for row in public_registry.get('residents', []) if row.get('roomCell') == room_cell and row.get('task') == str(a.task)]
    if len(eligible) != 1 or eligible[0].get('subject') != tool_subject:
        raise Refused('public registry does not advertise exactly this resident for the room: ' + json.dumps(public_registry.get('diagnostics')))
    (founder_home / 'hermes').mkdir(mode=0o700, exist_ok=True)
    public_registry_path = founder_home / 'hermes/registry.json'
    if public_registry_path.exists():
        if load(public_registry_path) != public_registry:
            raise Refused('retained founder public registry differs; no overwrite')
    else:
        publish(public_registry_path, json.dumps(public_registry).encode())

    # ------------------------------------------------------------ summon
    phase('summon')
    outbox = founder_home / 'outbox' / tool_subject
    bundles = lambda: list(outbox.glob('room-' + room_cell + '/assignment-*/handoff.json'))
    journal.step('room-summon', lambda: shell(founder, 'room-summon', f'summon {room_alias} as runner --program @{program_name} --budget 1000', effect=True) and True,
                 lambda: True if len(bundles()) == 1 else None)
    if len(bundles()) != 1:
        raise Refused('expected one source-bound handoff')
    dispatched = json.loads(run('native-dispatch', [mini, 'hermes-handoff', '--socket', socket, '--action', 'dispatch', '--registration', dispatch_registration, '--bundle', bundles()[0]]))
    inbox = pathlib.Path(dispatched['inbox'])
    checked = json.loads(run('native-delivery-check', [mini, 'hermes-handoff', '--socket', socket, '--action', 'check-delivery', '--dir', ws, '--task', a.task, '--inbox', inbox]))
    activation = json.loads(run('native-current-assignment-activation', [mini, 'hermes-handoff', '--socket', socket, '--action', 'activation', '--registration', dispatch_registration]))
    if (activation.get('type') != 'mini-hermes-assignment-activation-v1' or any(activation.get(k) != checked.get(k) for k in ('task', 'world', 'roomCell', 'assignment', 'account'))
            or activation['inbox'] != str(inbox)):
        raise Refused('native activation/check-delivery binding differs')
    account_name = activation['account']['name']
    save('assignment.json', {'checked': checked, 'activation': activation, 'dispatch': dispatched, 'inbox': str(inbox), 'account': account_name, 'roomCell': room_cell})

    # ------------------------------------------------------------ requests
    phase('requests')
    asks = []
    for index, member in enumerate(authors):
        for k in range(requested[member['subject']]):
            text = f'Request {index + 1}.{k + 1}: read {captured_alias}, write {summary_alias}, verify it, and reply to this source message.'
            say(member, f'request-{member["subject"]}-{k + 1}', f'ask {room_alias} {text}', text, tool_subject)
            asks.append({'author': member['subject'], 'text': text})
    feed = room_feed('requests-signed-read')
    addressed = [e for e in feed if e.get('to') == tool_subject and e.get('author') in requested]
    page_size = 256
    if sorted((e['author'], e['text']) for e in addressed) != sorted((row['author'], row['text']) for row in asks) or any(e['sequence'] > page_size for e in addressed):
        raise Refused('addressed requests are not exactly the asked set inside the first discovery page of each author stream')
    save('addressed-requests.json', addressed)
    if 'prepoll' not in values:
        count, seconds = rows('prepoll-filler', 'Before-poll ordinary message', a.prepoll_rows)
        if count < CALIBRATION_ROWS:
            # A resumed run measured too few rows: measure this world's current native row throughput explicitly.
            count, seconds = rows('calibration', 'Before-poll calibration message', CALIBRATION_ROWS)
        if count < CALIBRATION_ROWS:
            raise Refused('native row throughput is unmeasured; inspect retained timings before the first prompt')
        remember('prepoll', {'rows': count, 'seconds': seconds})

    # ------------------------------------------------------------ provider
    phase('provider')
    provider_source = pathlib.Path(a.fixture_provider)
    provider_sha = digest(provider_source)

    def free_port():
        with net_socket.socket() as probe:
            probe.bind(('127.0.0.1', 0))
            return probe.getsockname()[1]
    provider_port = values.get('providerPort') or remember('providerPort', free_port())
    gateway = values.get('gateway') or remember('gateway', f'127.0.0.1:{free_port()}')
    endpoint = f'http://127.0.0.1:{provider_port}/v1/chat/completions'

    def unit_active(unit, user=True):
        return subprocess.run((['systemctl', '--user'] if user else ['systemctl']) + ['is-active', unit], capture_output=True, text=True).stdout.strip() == 'active'

    def ensure_provider():
        """The endpoint is a separately managed USER dependency on a fixed port, kept on success."""
        if not unit_active(provider_unit):
            (root / 'provider-ready.json').unlink(missing_ok=True)
            run('provider-start', ['systemd-run', '--user', '--collect', '--unit=' + provider_unit, '--property=Type=exec', '--property=Nice=10', '--property=KillMode=control-group',
                                   '--property=StandardOutput=append:' + str(root / 'provider.stdout'), '--property=StandardError=append:' + str(root / 'provider.stderr'),
                                   '/usr/bin/python3', provider_source, '--state', root, '--port', provider_port])
        ready = wait('managed fixture provider', lambda: load(root / 'provider-ready.json'), 180)
        if ready.get('protocol') != 'mini-resident-fixture-provider-ready-v1' or ready.get('sourceSha256') != provider_sha or ready.get('pid', 0) <= 0 or ready.get('endpoint') != endpoint:
            raise Refused('fixture provider readiness differs from the published endpoint')
        return ready
    ensure_provider()
    # The operator's fixture pool key: handed to root, which hands it to the key
    # broker's pool operation (dregg-infra controller-entry provider-custody-copy v2).
    pool_secret = root / 'etc/pool.secret'
    if not pool_secret.exists():
        fd = os.open(pool_secret, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o600)
        os.write(fd, b'completion-cut-local-fixture-key\n')
        os.fsync(fd)
        os.close(fd)
    table = {'type': 'mini-provider-table-v2', 'providers': [{'name': 'resident-fixture-pool', 'endpoint': endpoint, 'kind': 'openai-compatible',
                                                             'models': ['mini-hermes-completion-cut'], 'credential': 'pool', 'caps': {'perCall': '2048', 'perDay': '40'}}]}
    table_bytes = (json.dumps(table, indent=2)).encode()
    if not (root / 'providers-source.json').exists():
        publish(root / 'providers-source.json', table_bytes)
    elif (root / 'providers-source.json').read_bytes() != table_bytes:
        raise Refused('retained provider table differs')
    copy_request = {'protocol': 'mini-resident-provider-custody-copy-v2', 'task': str(a.task),
                    'table': {'source': str(root / 'providers-source.json'), 'sha256': digest(root / 'providers-source.json'), 'target': str(canonical_table)},
                    'poolSecret': {'source': str(pool_secret), 'sha256': digest(pool_secret)}, 'provider': 'resident-fixture-pool'}
    if not (root / 'provider-copy-request.json').exists():
        save('provider-copy-request.json', copy_request)
    elif load(root / 'provider-copy-request.json') != copy_request:
        raise Refused('retained provider custody request differs')
    print('PROVIDER CUSTODY COPY READY ' + str(root / 'provider-copy-request.json'), flush=True)
    ack_path = root / 'provider-copy-ready.json'
    if not ack_path.exists():
        raise Waiting('root canonical provider custody publication absent: ' + str(ack_path))
    ack = load(ack_path)
    if ack.get('protocol') != 'mini-resident-provider-custody-ready-v1' or ack.get('task') != str(a.task) or ack.get('requestSha256') != digest(root / 'provider-copy-request.json'):
        raise Refused('root provider copy acknowledgment differs')
    if digest(canonical_table) != copy_request['table']['sha256']:
        raise Refused('canonical provider table bytes differ')
    if canonical_table.stat().st_uid != 0 or canonical_table.stat().st_mode & 0o022:
        raise Refused('canonical provider table owner/mode refused')
    # The pool key is sealed by the broker (root's pool operation); this account never
    # holds the seal key, so nothing is copied into the canonical store from here.

    # ------------------------------------------------------------ config
    phase('config')
    budget = hold_budget(values['prepoll']['rows'], values['prepoll']['seconds'], a.held_rows, a.worker_wall_seconds, a.turn_reserve_seconds)
    save('hold-budget.json', budget)
    if not budget['fits']:
        raise Refused('measured native throughput cannot fit the held rows inside one worker lifetime; nothing was prompted: ' + json.dumps(budget))
    fixture_runtime.mkdir(mode=0o700, exist_ok=True)
    for name, source in (('hermes-acp', pathlib.Path(a.fixture_acp)), ('grain-runtime', pathlib.Path(grain))):
        target = fixture_runtime / name
        if not target.exists():
            publish(target, source.read_bytes(), 0o700)
        elif digest(target) != digest(source):
            raise Refused('retained fixture runtime entry differs: ' + name)
    fixture_config = {'protocol': 'mini-resident-fixture-acp-config-v1', 'gateSeconds': budget['gateSeconds'], 'gatewayTimeoutSeconds': 660}
    if journal.state('cut-driver') is None:
        publish(worker / 'fixture-config.json', (json.dumps(fixture_config) + '\n').encode())
    runtime = {'mini': mini, 'host': host, 'hostConfig': config, 'hostSocket': socket, 'controlSocket': str(state / 'control.sock'), 'custodyKey': str(owner_key),
               'stateDir': str(state), 'cwd': str(controller_root), 'task': str(a.task), 'subject': owner_subject, 'capability': caps['parent'],
               'queryCapability': caps['parent'], 'policyControlCapability': caps['parentControl'],
               'toolTask': {'task': str(a.task + 1), 'subject': tool_subject, 'capability': caps['tool'], 'queryCapability': caps['tool'], 'custodyKey': str(tool_key),
                            'parentCapability': caps['toolWitness'], 'parentObserveCapability': caps['toolWitness'], 'reserve': '2', 'charge': '1', 'resourceWorkspace': str(ws),
                            'room': {'mini': mini, 'host': host, 'hostConfig': config, 'socket': socket, 'workspace': str(ws), 'home': str(home), 'room': room_alias,
                                     'account': account_name, 'restrictTools': True},
                            'allowedPublications': [{'kind': 'object', 'target': str(a.task + 2), 'capability': caps['publicationTool'], 'observeCapability': caps['publicationTool']}],
                            'allowedReads': [{'name': 'publication', 'kind': 'object', 'target': str(a.task + 2), 'observeCapability': caps['publicationRead'], 'maxResultBytes': 65536}]},
               'providerTask': {'task': str(a.task + 3), 'subject': provider_subject, 'capability': caps['provider'], 'queryCapability': caps['provider'], 'custodyKey': str(provider_key),
                                'parentCapability': caps['providerWitness'], 'parentObserveCapability': caps['providerWitness'], 'reserve': '7000', 'provider': 'resident-fixture-pool',
                                'contextWindowTokens': 262144, 'maxInputTokens': 16384, 'maxOutputTokens': 2048,
                                'onBehalfOf': {'subject': founder_subject, 'publicKey': public_key_hex(founder_key.read_bytes())},
                                'model': 'mini-hermes-completion-cut', 'providers': str(canonical_table), 'credentialBroker': str(canonical_broker),
                                'gatewayBind': gateway, 'maxRequestBytes': 32768, 'maxResponseBytes': 524288, 'maxIterations': 1,
                                'timeoutSeconds': 600, 'localFixtureHostNetwork': True},
               'commands': [{'name': 'hermes-acp', 'program': str(launcher),
                             'args': ['--workspace', str(worker), '--runtime-root', str(fixture_runtime), '--network', 'host', '--', '/agent/hermes-acp'],
                             'systemdScope': True, 'wallTimeSeconds': a.worker_wall_seconds, 'reserve': '3', 'charge': '1'}]}
    resident = {'type': 'mini-hermes-room-resident-v1', 'controller': str(controller_config), 'inbox': str(inbox), 'state': str(state / 'resident'),
                'maxPrompts': total_requests, 'intervalSeconds': 5, 'discoveryPageSize': page_size}
    controller_bytes = json.dumps(runtime, indent=2).encode()
    if not controller_config.exists():
        publish(controller_config, controller_bytes)
    elif controller_config.read_bytes() != controller_bytes:
        raise Refused('controller configuration is already published with other bytes; typed migration required, never an edit')
    if not resident_config.exists():
        publish(resident_config, json.dumps(resident, indent=2).encode())
    elif journal.state('continuous') is None and 'driver-driver-continuous' not in values and load(resident_config) != resident:
        raise Refused('resident configuration is already published with other content')
    save('ready.json', {'config': config, 'socket': socket, 'controller': str(controller_config), 'resident': str(resident_config), 'sharedWorld': str(context_path)})
    print('RESIDENT SOURCE READY ' + str(root / 'ready.json'), flush=True)
    print('AWAIT ROOT REGISTRATION ' + str(registration_receipt_path), flush=True)
    if not registration_receipt_path.is_file():
        raise Waiting('root-installed controller registration receipt absent: ' + str(registration_receipt_path))
    # The registrar reports its canonical registry in a receipt. The native runtime
    # must receive that actual root registration, never the output receipt itself.
    receipt = load(registration_receipt_path)
    launch = receipt.get('launch')
    if not isinstance(launch, dict) or launch.get('protocol') != 'mini-controller-launch-v1':
        raise Refused('typed root launch descriptor required')
    if launch.get('runtime') != grain or launch.get('config') != str(controller_config) or launch.get('unit') != controller_unit or launch.get('workerManager') != 'user':
        raise Refused('typed root launch identity differs')
    environment = launch['environment']
    runtime_registry = launch['runtimeRegistry']
    system = launch['manager'] == 'system'
    manager_command = ['sudo', '-n', 'systemctl'] if system else ['systemctl', '--user']
    manager_query = ['systemctl'] if system else ['systemctl', '--user']
    starter = (['sudo', '-n', 'systemd-run', '--uid=' + str(launch['serviceUid']), '--gid=' + str(pwd.getpwuid(launch['serviceUid']).pw_gid), '--property=Type=exec']
               if system else ['systemd-run', '--user'])
    driver_environment = dict(os.environ, **environment)

    # ------------------------------------------------------------ controller
    phase('controller')

    def controller_active():
        return subprocess.run(manager_query + ['is-active', controller_unit], capture_output=True, text=True).stdout.strip() == 'active'

    def admin_listening():
        # The same bare connect the source uses to tell a live controller from a stale socket.
        with net_socket.socket(net_socket.AF_UNIX) as probe:
            try:
                probe.connect(str(state / 'admin.sock'))
            except OSError:
                return False
        return True

    def ensure_controller(label):
        """A controller start/restart is an ordinary service operation; its journal decides recovery."""
        if not controller_active():
            run(label, [*starter, '--collect', '--unit=' + controller_unit, '--property=Nice=10', '--property=KillMode=control-group',
                        *['--setenv=' + k + '=' + v for k, v in environment.items()],
                        '--property=StandardOutput=append:' + str(root / 'controller.stdout'), '--property=StandardError=append:' + str(root / 'controller.stderr'),
                        grain, 'serve', controller_config])
        wait('controller admin socket', lambda: controller_active() and admin_listening(), 600)
    ensure_controller('start-controller')

    def controller_journal():
        return load(state / 'journal.json')

    def resident_state():
        return load(state / 'resident/resident.json')

    def queue():
        return load(state / 'resident/requests.json')

    def provider_records():
        return load(root / 'provider-received.json') if (root / 'provider-received.json').exists() else []

    def calls():
        return len(provider_records())

    def driver(label):
        """Detached resident driver; its identity is retained so a later invocation can still find it."""
        out = open(root / (label + '.stdout'), 'ab')
        err = open(root / (label + '.stderr'), 'ab')
        proc = subprocess.Popen([grain, 'hermes-room', 'resident', str(resident_config)], stdin=subprocess.DEVNULL, stdout=out, stderr=err,
                                env=driver_environment, start_new_session=True)
        remember('driver-' + label, proc_identity(proc.pid))
        return proc

    def driver_alive(label):
        retained = values.get('driver-' + label)
        if not retained:
            return False
        try:
            current = proc_identity(retained['pid'])
        except (FileNotFoundError, ProcessLookupError):
            return False
        return current['startTicks'] == retained['startTicks'] and current['uid'] == os.getuid() and current['state'] != 'Z'

    def driver_exit(label, proc, timeout):
        """Exit status of a driver this invocation started; a driver from an earlier invocation only reports gone."""
        if proc is not None:
            return proc.wait(timeout=timeout)
        wait('earlier driver ' + label + ' exit', lambda: not driver_alive(label), timeout)
        return None

    def source_grain(label, target, capability, subject=owner_subject):
        cell, _ = mini_query(label, subject, target, capability)
        return cell['grain']

    def native_balances(tag):
        return {'provider': source_grain(tag + '-provider', a.task + 3, caps['provider'], provider_subject),
                'tool': source_grain(tag + '-tool', a.task + 1, caps['tool'], tool_subject),
                'parent': source_grain(tag + '-parent', a.task, caps['parent'])}

    def credit(label, directory, name):
        text = run(label, [mini, 'credit', '--action', 'balance', '--dir', directory, '--account', name])
        if not text.startswith('credit '):
            raise Refused('unexpected native signed balance')
        return int(text.split()[1])

    def no_holds(j):
        return all(j.get(k) is None for k in ('residentCompletion', 'residentDelivery', 'roomAttempt', 'parentHold', 'toolHold', 'providerHold', 'child', 'pending'))

    # ------------------------------------------------------------ cut
    phase('cut')
    if 'before' not in values:
        remember('before', {'till': credit('before-receive-till', founder_ws, room_alias + '-till'), 'book': credit('before-receive-account', ws, account_name)})
    gate_path = worker / 'end-turn-gate.json'
    first = None
    if journal.state('cut-driver') is None:
        if calls() or (state / 'resident/resident.json').exists():
            raise Refused('a resident prompt already exists before the cut; exact recovery required')
        journal.begin('cut-driver')
        first = driver('driver-before-cut')
        journal.finish('cut-driver', values['driver-driver-before-cut'])
    if journal.state('cut-gate') != 'done':
        def gate():
            if gate_path.exists():
                return load(gate_path)
            if (first.poll() is not None) if first is not None else not driver_alive('driver-before-cut'):
                raise Refused('driver ended before the end_turn gate; see driver-before-cut.stderr and RUNBOOK recovery; nothing is replayed')
            return None
        # Adoption, signed reads, reserve, provider exchange and the paid append all precede the gate.
        wait('real ACP end_turn gate', gate, a.worker_wall_seconds + 600)
        selected = queue()['selected']
        before = resident_state()
        save('resident-before-kill.json', before)
        save('selected-before-kill.json', selected)
        pending_authors = {row['entry']['author'] for row in queue()['pending']}
        expected_pending = {s for s, n in requested.items() if n - (1 if s == selected['identity']['author'] else 0) > 0}
        check('one addressed request selected before the provider while every other author stays queued',
              selected['identity']['author'] in requested and selected['entry']['to'] == tool_subject and selected['entry']['text'] in {row['text'] for row in asks}
              and selected['identity']['binding']['assignment'] == checked['assignment'] and selected.get('started') is not None
              and pending_authors == expected_pending and len(queue()['pending']) == total_requests - 1 and before['completed'] == 0 and calls() == 1,
              {'selected': selected, 'pendingAuthors': sorted(pending_authors), 'ready': checked, 'providerCalls': calls()})
        journal.finish('cut-gate', {'selected': selected, 'gate': load(gate_path), 'residentBefore': before})
    cut = journal.data['steps']['cut-gate']['value']
    if 'held' not in values:
        rows('held-filler', 'During-held-reply ordinary message', a.held_rows)
        held_present = len([e for e in room_feed('held-signed-read') if (e.get('text') or '').startswith('During-held-reply ordinary message ')])
        if held_present != a.held_rows:
            raise Refused(f'signed room shows {held_present} held rows, expected {a.held_rows}')
        remember('held', held_present)
    if journal.state('cut-kill') != 'done':
        if driver_alive('driver-before-cut'):
            os.kill(values['driver-driver-before-cut']['pid'], signal.SIGKILL)
            wait('driver death', lambda: not driver_alive('driver-before-cut'), 30)
            ended = 'SIGKILL'
        else:
            ended = 'absent-before-kill'
        if first is not None:
            first.wait(timeout=30)
        check('only the driver was killed after the source advanced beyond tail100',
              ended == 'SIGKILL' and (first is None or first.returncode == -signal.SIGKILL) and controller_active() and admin_listening()
              and not (worker / 'release-end-turn').exists() and calls() == 1,
              {'gate': cut['gate'], 'heldMessages': values['held'], 'driverEnded': ended})
        journal.finish('cut-kill', ended)
    if not (worker / 'release-end-turn').exists():
        publish(worker / 'release-end-turn', b'release genuine source end_turn after driver death\n')
    if journal.state('cut-completion') != 'done':
        def staged():
            j = controller_journal()
            return j.get('residentCompletion') if j.get('child') is None and j.get('parentHold') is None and j.get('providerHold') is None else None
        turn = wait('source completion without driver', staged, a.worker_wall_seconds)
        check('native completion staged without driver counter edit', resident_state() == cut['residentBefore'] and controller_journal().get('residentDelivery') is not None,
              {'source': turn, 'resident': resident_state()})
        journal.finish('cut-completion', True)

    # ------------------------------------------------------------ recover
    phase('recover')
    if journal.state('recover') != 'done':
        second = None
        if not driver_alive('driver-receive') and not (resident_state()['completed'] == total_requests and resident_state()['pending'] is None):
            second = driver('driver-receive')
        status = driver_exit('driver-receive', second, total_requests * (a.worker_wall_seconds + 600))
        check('restart drains the old exact reply and then every other queued author', status in (0, None) and resident_state()['completed'] == total_requests
              and resident_state()['pending'] is None and calls() == total_requests,
              {'resident': resident_state(), 'providerCalls': calls(), 'stderr': (root / 'driver-receive.stderr').read_text()[-4000:]})
        journal.finish('recover', True)

    # ------------------------------------------------------------ verify
    phase('verify')
    records = provider_records()
    outcomes = [load(p) for p in sorted((state / 'resident').glob('request-*-completed.json'))]
    delivery_files = sorted(state.glob('resident-delivered-*.json'))
    deliveries = [load(p) for p in delivery_files]
    order = [d['result']['arguments']['to'] for d in deliveries]
    turns = [load(p) for p in sorted(worker.glob('turn-*.json'))]
    reads = [load(p) for p in sorted(worker.glob('signed-document-read-*.json'))]
    read_hashes = [sha(json.loads(r['content'][0]['text'])['text'].encode()) for r in reads]
    check('every model frame consumed the actual native captured input of its own turn',
          len(records) == total_requests == len(reads) and [r['nativeInputTextSha256'] for r in records] == read_hashes and all(r['reply'] for r in records),
          {'providerInputHashes': [r['nativeInputTextSha256'] for r in records], 'inputStableAcrossTurns': len(set(read_hashes)) == 1, 'sourceReference': capture})
    completed_by = {}
    for row in outcomes:
        completed_by[row['identity']['author']] = completed_by.get(row['identity']['author'], 0) + 1
    check('every addressed source request identity completed exactly once', completed_by == requested and all('modelRequests' not in x for x in outcomes)
          and not list((state / 'resident').glob('request-*-refused.json')) and not list((state / 'resident').glob('request-*-cancelled.json')), outcomes)
    check('native finals were delivered to the exact request authors in fair rotation',
          service_is_fair(order, requested) and order[0] == cut['selected']['identity']['author'] and [t['author'] for t in turns] == order
          and all(d['result']['expectedReply'] and d['result']['payment']['paid'] for d in deliveries) and not list(state.glob('resident-final-refused-*.json')),
          {'serviceOrder': order, 'requested': requested, 'deliveries': deliveries})
    summary_ref = load(founder_ws / 'refs' / (summary_alias + '.json'))
    summary_cell, _ = mini_query('summary-native-atom-classification', founder_subject, summary_ref['target'], summary_ref['observeCapability'])
    summary_atoms = [row for row in summary_cell['entries'] if row.get('type') == 'atom' and row.get('tombstonedAt') is None]
    summary_kinds = {row['kind']['type'] for row in summary_atoms}
    summary_privacy = 'sealed-object' if summary_kinds == {'sealedObject'} else 'public-text' if summary_kinds == {'text'} else 'mixed-or-other'
    check('summary confidentiality classified from signed native atom kinds', bool(summary_atoms) and summary_kinds <= {'text', 'sealedObject'}
          and all(row['kind']['fragment']['ciphertext'] for row in summary_atoms if row['kind']['type'] == 'sealedObject'),
          {'classification': summary_privacy, 'target': summary_ref['target'], 'kinds': sorted(summary_kinds), 'atoms': len(summary_atoms)})
    summary_text = shell(founder, 'summary-founder-readback', 'doc show ' + summary_alias)
    check('founder reads every appended summary back from the shared output document',
          all(' '.join(r['reply'].splitlines()[0].split()) in ' '.join(summary_text.split()) for r in records),
          {'summaryAlias': summary_alias, 'firstLines': [r['reply'].splitlines()[0] for r in records]})
    replies = {r['reply'] for r in records}
    for member in authors:
        seen = [e for e in room_feed('signed-delivered-history', member) if e.get('kind') == 'say' and e.get('author') == tool_subject and e.get('to') == member['subject']]
        check('author ' + member['subject'] + ' reads exactly one signed final per request despite late delivery',
              len(seen) == requested[member['subject']] and all(e.get('text') in replies for e in seen), seen)
    if 'after' not in values:
        snapshot = exact_payment_snapshot(ws, lambda path: operation_result(run('payment-exact-lookup',
            [mini, 'credit', '--action', 'lookup-operation', '--dir', ws, '--operation-record', path])))
        remember('after', dict(snapshot, resident=resident_state(), balances=native_balances('before-replay'),
            book=credit('after-receive-account', ws, account_name), till=credit('after-receive-till', founder_ws, room_alias + '-till')))

    after, before_money = values['after'], values['before']
    check('native Book payments reconcile summaries, finals and typed status notices exactly once',
          after['modelPayments'] == 2 * total_requests and after['prices'] >= 2 * total_requests and after['till'] - before_money['till'] == after['prices']
          and before_money['book'] - after['book'] == after['prices'] + after['fees'], {'before': before_money, 'after': after})

    # ------------------------------------------------------------ replay
    phase('replay')
    if journal.state('replay') != 'done':
        for request_path in sorted((state / 'resident').glob('completion-request-*.json')):
            run('replay-' + request_path.stem, [grain, 'resident-completion', 'receive', state / 'admin.sock', request_path])
        for request_path in sorted((state / 'resident').glob('delivery-request-*.json')):
            run('replay-' + request_path.stem, [grain, 'resident-delivery', 'deliver', state / 'admin.sock', request_path])
        third = driver('driver-repeat')
        status = driver_exit('driver-repeat', third, a.native_timeout_seconds)
        check('exact receiver replay does not call or charge the provider', status == 0 and resident_state() == after['resident'] and calls() == total_requests
              and native_balances('after-replay') == after['balances'] and credit('after-replay-account', ws, account_name) == after['book'],
              {'providerCalls': calls(), 'nativeBalances': after['balances']})
        j = controller_journal()
        check('native finals leave no uncertain holds', len([r for r in j.get('roomResolutions', []) if r.get('tool') == 'mini_say']) == total_requests and no_holds(j), j)
        journal.finish('replay', True)

    # ------------------------------------------------------------ service-restart
    phase('service-restart')
    if journal.state('service-restart') != 'done':
        journal_before = digest(state / 'journal.json')
        run('stop-controller', manager_command + ['stop', controller_unit])
        wait('controller stopped', lambda: not controller_active(), 120)
        run('stop-provider', ['systemctl', '--user', 'stop', provider_unit])
        ready_before = ensure_provider()
        ensure_controller('restart-controller')
        fourth = driver('driver-after-restart')
        status = driver_exit('driver-after-restart', fourth, a.native_timeout_seconds)
        check('controller and provider restart keep the endpoint, add no provider call or charge, and leave no holds',
              status == 0 and resident_state() == after['resident'] and calls() == total_requests and no_holds(controller_journal())
              and native_balances('after-restart') == after['balances'] and credit('after-restart-account', ws, account_name) == after['book']
              and ready_before['endpoint'] == endpoint,
              {'providerCalls': calls(), 'journalSha256Before': journal_before, 'journalSha256After': digest(state / 'journal.json'), 'endpoint': endpoint})
        journal.finish('service-restart', True)

    # ------------------------------------------------------------ continuous
    phase('continuous')
    if journal.state('continuous') != 'done':
        # Continuous provisioning: removing fixture-only maxPrompts must not dispatch
        # unchanged maintenance after the selected requests completed. The config is
        # outside the controller's signed pin and controls only the driver.
        continuous = load(resident_config)
        continuous.pop('maxPrompts', None)
        publish(resident_config, json.dumps(continuous, indent=2).encode())
        discovery = state / 'resident/discovery.json'
        mark = discovery.stat().st_mtime_ns
        fifth = driver('driver-continuous')
        polls = [mark]

        def two_polls():
            if fifth.poll() is not None:
                raise Refused('continuous driver ended; see driver-continuous.stderr')
            current = discovery.stat().st_mtime_ns
            if current != polls[-1]:
                polls.append(current)
            return len(polls) >= 3
        wait('two complete unchanged resident polls', two_polls, a.native_timeout_seconds)
        check('continuous unchanged maintenance makes zero extra provider calls', fifth.poll() is None and calls() == total_requests and resident_state() == after['resident'],
              {'providerCalls': calls(), 'polls': len(polls) - 1, 'maintenance': queue().get('maintenanceRevision')})
        fifth.terminate()
        fifth.wait(timeout=60)
        journal.finish('continuous', True)

    # ------------------------------------------------------------ retain
    phase('retain')
    resident_unit = None
    if a.preserve_on_success:
        resident_unit = receipt['residentUnit']
        if receipt.get('residentConfig') != str(resident_config) or receipt.get('residentState') != str(state / 'resident') or receipt.get('residentInbox') != str(inbox):
            raise Refused('root resident launch coordinates differ')
        resident_entry = base / 'usr/local/lib/mini/controller-entry.py'
        if subprocess.run(manager_query + ['is-active', resident_unit], capture_output=True, text=True).stdout.strip() != 'active':
            run('retain-continuous-resident', [*starter, '--collect', '--unit=' + resident_unit, '--property=Nice=10', '--property=KillMode=control-group',
                                               '--setenv=MINI_ROOT=' + str(base), '--property=StandardOutput=append:' + str(root / 'resident-live.stdout'),
                                               '--property=StandardError=append:' + str(root / 'resident-live.stderr'), resident_entry, 'resident', str(a.task)])
        wait('retained resident unit active', lambda: subprocess.run(manager_query + ['is-active', resident_unit], capture_output=True, text=True).stdout.strip() == 'active', 60)
    else:
        run('stop-controller-final', manager_command + ['stop', controller_unit])
        run('stop-provider-final', ['systemctl', '--user', 'stop', provider_unit])
    save('timings.json', timings)
    save('result.json', {'type': 'mini-resident-multi-author-cut-result-v2', 'passed': all(r['passed'] for r in checks), 'checks': len(checks), 'providerCalls': calls(),
                         'authors': author_subjects, 'requested': requested, 'serviceOrder': order, 'assignment': checked,
                         'cut': 'SIGKILL driver after >100 source rows; native source completion; unchanged driver restart; controller and provider restart',
                         'driverEndedBy': journal.data['steps']['cut-kill']['value'], 'provider': 'scripted local SSE; no paid provider qualification',
                         'summaryConfidentiality': summary_privacy, 'holdBudget': budget})
    save('controller-inventory.json', {'protocol': 'mini-resident-controller-inventory-v1', 'task': str(a.task), 'controller': str(controller_config),
                                       'residentConfig': str(resident_config), 'stateDir': str(state), 'runtimeRegistry': runtime_registry, 'unit': controller_unit,
                                       'manager': launch['manager'], 'workerManager': launch['workerManager'], 'environment': environment,
                                       'sourceManifest': str(manifest_path), 'sourceManifestSha256': digest(manifest_path), 'retainedOnSuccess': a.preserve_on_success,
                                       'providerUnit': provider_unit, 'providerManager': 'user', 'providerServiceUid': os.getuid(), 'providerStateDir': str(root),
                                       'providerEndpoint': endpoint, 'providerSource': str(provider_source), 'providerSourceSha256': provider_sha,
                                       'residentUnit': resident_unit, 'residentManager': launch['manager'], 'residentEntry': str(base / 'usr/local/lib/mini/controller-entry.py')})
    print(root / 'result.json', flush=True)
    if a.preserve_on_success:
        print('RESIDENT LIVE ' + str(root / 'controller-inventory.json'), flush=True)


if __name__ == '__main__':
    try:
        main()
    except Waiting as waiting:
        print('WAITING ' + str(waiting), file=sys.stderr, flush=True)
        sys.exit(WAITING)
    except Unknown as unknown:
        print('UNKNOWN ' + str(unknown), file=sys.stderr, flush=True)
        sys.exit(4)
    except Refused as refused:
        print('REFUSED ' + str(refused), file=sys.stderr, flush=True)
        sys.exit(3)
