#!/usr/bin/env python3
"""Receive synthetic paid-v2 members on a supplied, already running Mini Store.

Provision creates no Store or supervisor. Hook only reconciles retained exact
payment origins against that same source world. Synthetic RPC is explicit and
does not qualify a mainnet payment or provider connection.
"""
import argparse
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import re
import socket
import struct
import subprocess
import sys
import tempfile


def require(ok, message):
    if not ok:
        raise ValueError(message)


def read(path):
    return json.loads(Path(path).read_text())


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def absolute(value, exists=True):
    path = Path(value)
    require(path.is_absolute(), 'absolute path required: ' + str(value))
    return path.resolve(strict=exists)


def save(path, value):
    path = Path(path)
    require(not path.exists(), 'evidence already exists: ' + str(path))
    with tempfile.NamedTemporaryFile(mode='w', dir=path.parent, prefix='.paid-', delete=False) as file:
        json.dump(value, file, indent=2); file.write('\n')
        file.flush(); os.fsync(file.fileno())
    os.replace(file.name, path)
    directory = os.open(path.parent, os.O_RDONLY | os.O_DIRECTORY)
    try:
        os.fsync(directory)
    finally:
        os.close(directory)


def natural(value, name, bound=2**256):
    require(type(value) in (int, str) and re.fullmatch(r'0|[1-9][0-9]*', str(value)), name + ' must be canonical natural')
    number = int(value)
    require(number < bound, name + ' exceeds source bound')
    return number


class Source:
    def __init__(self, request, evidence):
        self.request, self.evidence, self.serial = request, evidence, 0
        self.manifest_path = absolute(request['manifest'])
        self.manifest = read(self.manifest_path)
        self.deployment = request['deployment']
        self.config_path = absolute(self.deployment['config'])
        self.config_bytes = self.config_path.read_bytes()
        config = read(self.config_path)
        self.genesis = read(absolute(self.deployment['genesis'])) if 'genesis' in self.deployment else None
        natural(config['expectedSeed'], 'genesis seed')
        self.identity = dict(manifestSha256=request['manifestSha256'], configSha256=self.deployment['configSha256'],
                             storageRoot=str(absolute(config['storageRoot'])), domain=str(config['domain']),
                             genesisSeed=str(config['expectedSeed']), socket=self.deployment['socket'])
        self.identity['id'] = hashlib.sha256(json.dumps(self.identity, sort_keys=True).encode()).hexdigest()
        require(absolute(config['storageBinary']) == absolute(self.manifest['store']), 'different Store binary')
        require(absolute(config['signatureBinary']) == absolute(self.manifest['verifier']), 'different signature verifier')
        self.pins = {self.manifest_path: request['manifestSha256'], self.config_path: self.deployment['configSha256']}
        for role in ('mini', 'host', 'store', 'verifier', 'payWatcher'):
            self.pins[absolute(self.manifest[role])] = self.manifest['sha256'][role]
        self.check()

    def check(self):
        for path, expected in self.pins.items():
            require(digest(path) == expected, 'paid source pin changed: ' + str(path))

    def run(self, label, argv, env=None):
        self.check(); self.serial += 1
        base = self.evidence / (str(self.serial).zfill(4) + '-' + label)
        argv = [str(value) for value in argv]
        save(base.with_suffix('.command.json'), argv)
        result = subprocess.run(argv, stdin=subprocess.DEVNULL, capture_output=True, env=env,
                                timeout=self.request.get('timeoutSeconds', 600))
        base.with_suffix('.out').write_bytes(result.stdout)
        base.with_suffix('.err').write_bytes(result.stderr)
        base.with_suffix('.rc').write_text(str(result.returncode) + '\n')
        require(result.returncode == 0, label + ': native command refused; see ' + str(base))
        return result.stdout

    def mini(self, label, *args):
        return self.run(label, [self.manifest['mini'], *args])

    def status(self, record, signature, label):
        self.check()
        request = dict(identityKey=record['miniKey'], signature=signature, originalRecipient=record['enrolAddress'])
        payload = json.dumps(request, separators=(',', ':')).encode()
        frame = b'\x02' + struct.pack('<I', len(self.config_bytes)) + self.config_bytes
        frame += bytes.fromhex(self.manifest['sha256']['host']) + bytes([181]) + payload
        def exact(stream, count):
            data = b''
            while len(data) < count:
                piece = stream.recv(count - len(data))
                require(piece, 'paid status transport closed; retained origin must be retried')
                data += piece
            return data
        with socket.socket(socket.AF_UNIX, socket.SOCK_STREAM) as stream:
            stream.settimeout(self.request.get('timeoutSeconds', 600))
            stream.connect(self.deployment['socket'])
            stream.sendall(struct.pack('<I', len(frame)) + frame)
            size = struct.unpack('<I', exact(stream, 4))[0]
            require(0 < size <= 8193, 'paid status exceeds source bound')
            response = exact(stream, size)
        (self.evidence / (label + '.response.bin')).write_bytes(response)
        save(self.evidence / (label + '.request.json'), request)
        require(response[0] == 181, 'source refused exact paid status: ' + repr(response[1:]))
        value = json.loads(response[1:])
        save(self.evidence / (label + '.json'), value)
        require(value['type'] == 'payStatus' and value['identityKey'] == record['miniKey'], 'status identity differs')
        locator = value['paymentLocator']
        require(locator == dict(signature=signature, originalRecipient=record['enrolAddress'],
                                claimId=(b'soltx:' + bytes.fromhex(signature) + bytes.fromhex(record['enrolAddress'])).hex()),
                'source status payment origin differs')
        return value


def consumed(status, record, subject=None):
    payment = status['payment']
    require(payment['state'] == 'consumedV2', 'payment remains retained or refused; do not send it again')
    require(payment['amountAtomic'] == record['amountAtomic'], 'source consumed another payment amount')
    require(payment['weeks'] == record['quote']['split']['weeks'], 'source duration differs')
    require(sum(natural(payment[k], k) for k in ('birthFee', 'membershipCredit', 'creditedRemainder'))
            == natural(payment['mintedCredit'], 'mintedCredit'), 'source credit split does not conserve payment')
    if subject is not None:
        require(status['entry']['subject'] == subject, 'paid source subject differs from member inventory')
    return status['entry']['subject']


def artifacts(root):
    # Custody keys remain private in member homes, not copied into hook evidence.
    return [dict(path=str(path), sha256=digest(path)) for path in sorted(root.rglob('*')) if path.is_file()]


def provision(request, result_path):
    require(request['type'] == 'mini-paid-entry-provision-v1', 'unknown paid provision request')
    require(request.get('rail', 'synthetic-rpc') == 'synthetic-rpc', 'this adapter only receives isolated synthetic RPC')
    root = absolute(request['evidenceDirectory'], False)
    root.mkdir(mode=0o700, parents=False, exist_ok=False)
    source = Source(request, root)
    rows = request['members']
    require(type(rows) is list and 1 <= len(rows) <= request.get('maxMembers', 100), 'declared paid receiving population outside bound')
    names = [row['name'] for row in rows]
    require(len(set(names)) == len(names) and all(re.fullmatch(r'[a-z][a-z0-9-]{0,31}', name) for name in names), 'invalid paid member names')
    for row in rows:
        require(0 < natural(row.get('weeks', 2), 'weeks', 2**32), 'positive weeks required')
        natural(row.get('starterCredit', '1000'), 'starterCredit', 2**128)
        require(not absolute(row['joinDir'], False).exists(), 'fresh paid join directory required')
    genesis_observer = source.genesis.get('payObserver') if source.genesis else None
    require(genesis_observer is not None, 'supplied genesis has no pay observer; requires fresh construction')
    require(genesis_observer['capability'] == request['observer']['capability'] and
            genesis_observer['enrolCapability'] == request['observer']['enrolCapability'], 'observer capabilities differ from genesis')
    observer = absolute(request['observerWorkspace']); operator = absolute(request['operatorWorkspace'])
    observer_pin, operator_pin = read(observer / 'workspace.json'), read(operator / 'workspace.json')
    for pin in (observer_pin, operator_pin):
        require(absolute(pin['config']) == source.config_path and absolute(pin['host']) == absolute(source.manifest['host'])
                and pin['socket'] == source.deployment['socket'], 'paid custody workspace belongs to another Store')
    require(str(observer_pin['subject']) == genesis_observer['subject'] and observer_pin['subject'] != operator_pin['subject'], 'dedicated source observer required')
    enrollments = [row for row in source.genesis['enrollments'] if row['key']['subject'] == str(operator_pin['subject'])]
    require(len(enrollments) == 1, 'operator account has no exact genesis enrollment')
    operator_account = enrollments[0]
    source.mini('operator-account-reference', 'workspace', '--action', 'import', '--dir', operator,
                '--name', 'paid-entry-account', '--kind', 'account', '--target', operator_account['accountId'],
                '--observe-capability', operator_account['spendCapabilityId'], '--operation-capability', operator_account['spendCapabilityId'])
    repo = absolute(request['sourceRepo'])
    fixture = repo / 'native/pay-watcher/fixtures/generate.py'
    tick_script = repo / 'deploy/pay/mini-pay-watcher'
    require(fixture.is_file() and tick_script.is_file(), 'missing pinned source paid recipe')
    source.pins[fixture] = digest(fixture); source.pins[tick_script] = digest(tick_script)
    source.pins[Path(__file__).resolve()] = digest(Path(__file__).resolve())
    save(root / 'source-pins.json', {str(path): sha for path, sha in source.pins.items()})
    sys.dont_write_bytecode = True
    module = importlib.util.spec_from_file_location('paid_fixtures', fixture)
    gen = importlib.util.module_from_spec(module); module.loader.exec_module(gen)
    # Every paid member receives its own future address allocation. Population
    # determines capacity; two-person demonstrations impose no product ceiling.
    book = [gen.ENROL] + [gen.b58(gen.key('shared-world-book-' + source.identity['id'] + '-' + str(i))) for i in range(len(rows))]
    tariff = dict(version='2', asset='0', mint=gen.MINT, tokenProgram=gen.TOKEN_2022, decimals='6',
                  creditPerAtomic='1', maxPerObservation='100000000000', minTickSlots='150',
                  nodeHourRate='5952380', enrolIndex=None, journalFloor='1000000', slashCallerPermille='500')
    save(root / 'book.json', dict(control=request['factoryControl'], book=book, tariff=tariff))
    source.mini('install-book', 'pay', 'book', '--dir', operator, '--source', root / 'book.json')
    assigned = source.mini('assign-enrollment-row', 'pay', 'address', '--dir', operator, '--account', 'paid-entry-account').decode()
    require(assigned.startswith('index 0 → ' + gen.ENROL), 'fresh enrollment row was not assigned exactly once')
    save(root / 'enrollment-tariff.json', dict(control=request['factoryControl'], book=[], tariff=dict(tariff, version='3', enrolIndex='0')))
    source.mini('enable-enrollment', 'pay', 'book', '--dir', operator, '--source', root / 'enrollment-tariff.json')
    pin = root / 'enrol-pin.json'
    save(pin, dict(type='minidregg-enrol-pin-v2', enrolAddress=gen.ENROL, mint=gen.MINT,
                   tokenProgram=gen.TOKEN_2022, decimals='6', login=request.get('login', 'mini@synthetic.invalid')))
    profile = json.loads(source.run('source-profile', [source.manifest['host'], source.config_path, 'profile']))
    birth = root / 'paid-birth-context.json'
    save(birth, dict(type='minidregg-participant-birth-context-v1', genesis=source.genesis, template=profile['template']))
    history, tip = [], 2000
    state = root / 'watcher-state'

    def tick(label):
        endpoints = []
        for side in ('a', 'b'):
            endpoint = gen.Endpoint(); target = root / 'ticks' / label / side
            endpoint.put('getSlot/finalized.json', gen.envelope(tip + 10))
            endpoint.put('getBlockTime/' + str(tip + 10) + '.json', gen.envelope(gen.block_time(tip + 10)))
            for address in book:
                accounts = [gen.token_account_entry(gen.ENROL_TA, owner=gen.ENROL)] if address == gen.ENROL else []
                endpoint.put(f'getTokenAccountsByOwner/{address}.{gen.MINT}.json', gen.envelope({'context': {'slot': tip + 10}, 'value': accounts}))
            newest = [(signature, slot) for signature, slot, body in reversed(history)]
            for until in [None] + [signature for signature, slot in newest]:
                listing = newest if until is None else newest[:[signature for signature, slot in newest].index(until)]
                suffix = '.until.' + gen.b58(until) if until else ''
                chunks = [listing[start:start + 25] for start in range(0, len(listing), 25)] or [[]]
                if len(chunks[-1]) == 25:
                    chunks.append([])
                before = None
                for chunk in chunks:
                    cursor = '.before.' + gen.b58(before) if before else ''
                    endpoint.put('getSignaturesForAddress/' + gen.ENROL_TA + cursor + suffix + '.json',
                                 gen.envelope(gen.listing(*[(signature, slot, None) for signature, slot in chunk])))
                    before = chunk[-1][0] if chunk else None
            for signature, slot, body in history:
                endpoint.tx(signature, body)
            for relative, value in endpoint.files.items():
                gen.dump(str(target / relative), value)
            endpoints.append(str(target))
        env = dict(os.environ, MINI=source.manifest['mini'], PAY_WATCHER=source.manifest['payWatcher'], PAY_STATE=str(state),
                   PAY_OBSERVER_WS=str(observer), PAY_OBSERVER_CAPABILITY=request['observer']['capability'],
                   PAY_ENROL_INDEX='0', PAY_JOURNAL_FLOOR='1000000', PAY_ENROL_CAPABILITY=request['observer']['enrolCapability'],
                   PAY_OPERATOR_SOCKET=source.deployment['operatorSocket'], PAY_RPC_FIXTURES=' '.join(endpoints),
                   PAY_MIN_ENDPOINTS='2', PAY_ENROL_ROUNDS='0')
        env.pop('PAY_RPC_ENDPOINTS', None)
        source.run(label, ['sh', tick_script], env)

    tick('empty-heartbeat')
    members = []
    for row in rows:
        name, directory = row['name'], absolute(row['joinDir'], False)
        source.mini(name + '-quote', 'join', '--memo-version', 'v2', '--solana', '--host', source.manifest['host'],
                    '--config', source.config_path, '--socket', source.deployment['socket'], '--enrol', pin,
                    '--dir', directory, '--name', name, '--weeks', row.get('weeks', 2),
                    '--starter-credit', row.get('starterCredit', '1000'), '--birth-context', birth)
        record = read(directory / 'join.json')
        tip += 300
        signature = gen.sig('shared-world-' + source.identity['id'] + '-' + name)
        body = gen.enrol_tx(signature, tip - 50, int(record['amountAtomic']), memos=[record['memo']])
        save(root / (name + '-synthetic-transfer.json'), dict(rail='synthetic-rpc', signature=signature.hex(), slot=tip - 50, transaction=body))
        history.append((signature, tip - 50, body)); tick(name + '-deposit')
        status = source.status(record, signature.hex(), name + '-consumed')
        subject = consumed(status, record)
        require(status['payment']['authorization'] == 'originalMemo' and status['leaseState'] == 'active', 'fresh paid entry did not consume original memo')
        source.mini(name + '-wait', 'join', '--memo-version', 'v2', '--wait', '--host', source.manifest['host'],
                    '--config', source.config_path, '--socket', source.deployment['socket'], '--dir', directory,
                    '--signature', gen.b58(signature), '--timeout', '0', '--birth-context', birth)
        workspace = directory / 'workspace'
        require(read(workspace / 'workspace.json')['subject'] == subject, 'native paid workspace subject differs')
        source.mini(name + '-credits', 'pay', 'status', '--dir', workspace)
        repeat = source.status(record, signature.hex(), name + '-retry')
        require(repeat['payment'] == status['payment'], 'exact payment retry changed consumption')
        attempts = []
        for attempt in sorted((observer / 'attempts').glob('pay-enrol-*')):
            retained = attempt / 'enrol-status-v2.json'
            if retained.is_file():
                saved = read(retained)
                if saved.get('paymentLocator') == status['paymentLocator']:
                    require(saved['payment'] == status['payment'], 'original observer decision differs from source consumption')
                    require((attempt / 'outcome.bin').is_file() and (attempt / 'signature.bin').is_file(), 'observer lacks original signed receipt')
                    attempts.append(attempt)
        require(len(attempts) == 1, 'payment does not identify one retained observer receipt')
        observer_artifacts = artifacts(attempts[0])
        members.append(dict(name=name, subject=subject, workspace=str(workspace), joinDir=str(directory),
                            miniKeyFile=record['miniKeyFile'], nextPublicFile=record['nextPublicFile'], sshKeyFile=record['sshKeyFile'],
                            signature=signature.hex(), amountAtomic=record['amountAtomic'], statusArtifact=str(root / (name + '-consumed.json')),
                            observerArtifacts=observer_artifacts))
    require(len({member['subject'] for member in members}) == len(members), 'duplicate paid source subjects')
    save(result_path, dict(type='mini-paid-entry-provision-result-v1', status='pass', rail='synthetic-rpc', identity=source.identity,
                          request=request, members=members, artifacts=artifacts(root)))


def hook(request, state_path, result_path):
    state = read(absolute(state_path))
    require(state['type'] == 'mini-paid-entry-provision-result-v1' and state['status'] == 'pass', 'paid construction is incomplete')
    require(request['role'] == 'paid-entry' and request['phase'] == 'run', 'unknown paid hook role/phase')
    root = absolute(request['evidenceDirectory']) / ('paid-' + hashlib.sha256(str(result_path).encode()).hexdigest()[:16])
    root.mkdir(mode=0o700, parents=False, exist_ok=False)
    source = Source(state['request'], root)
    require(request['identity'] == state['identity'] == source.identity, 'paid hook belongs to another supplied Store')
    require(request['manifest'] == state['request']['manifest'] and request['deployment']['config'] == str(source.config_path), 'paid hook source coordinates differ')
    inventory = {member['subject']: member for member in state['members']}
    for artifact in state['artifacts']:
        require(digest(absolute(artifact['path'])) == artifact['sha256'], 'retained paid construction evidence changed')
    credited = []
    for key, subject in request['subjects'].items():
        require(subject in inventory, 'selected subject has no retained paid entry')
        member = inventory[subject]
        for artifact in member['observerArtifacts']:
            require(digest(absolute(artifact['path'])) == artifact['sha256'], 'original signed observer receipt changed')
        require(absolute(request['members'][key]['workspace']) == absolute(member['workspace']), 'selected paid workspace differs')
        record = read(absolute(member['joinDir']) / 'join.json')
        status = source.status(record, member['signature'], key + '-status')
        consumed(status, record, subject)
        before = read(absolute(member['statusArtifact']))
        require(status['payment'] == before['payment'], 'retained payment consumption changed')
        source.mini(key + '-credits', 'pay', 'status', '--dir', member['workspace'])
        credited.append(subject)
    save(result_path, dict(type='mini-joined-member-hook-result-v1', role='paid-entry', phase='run', status='pass',
                          identity=source.identity, rail='synthetic-rpc', creditedSubjects=credited,
                          execution='native receiving with two synthetic finalized RPC fixtures', artifacts=artifacts(root)))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--mode', choices=('provision', 'hook'), default='hook')
    parser.add_argument('--state'); parser.add_argument('--request', required=True); parser.add_argument('--result', required=True)
    args = parser.parse_args()
    request = read(absolute(args.request)); result = absolute(args.result, False)
    require(not result.exists(), 'paid result already exists')
    if args.mode == 'provision':
        provision(request, result)
    else:
        require(args.state, 'paid hook requires retained construction state')
        hook(request, args.state, result)


if __name__ == '__main__':
    main()
