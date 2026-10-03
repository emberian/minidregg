#!/usr/bin/env python3
"""Actual fresh native job refund and original-receipt recovery receiving.

HOST/MINI/STORE/VERIFIER/CONSENT_HOST name immutable matched artifacts; JOURNEY_STEP_DIR must
be fresh. Only this fixture's native Store and local custody records are changed.
The job's symbolic program 0 is never run: native caller-authorized void is a
separate law edge. This is not provider payout or Objective execution evidence.
The missing-confirmation boundary is simulated by moving fixture-owned outcome
records after actual native settlement, not by claiming a real socket fault.
"""
import hashlib
import json
import os
from pathlib import Path
import re
import signal
import subprocess
import sys

HERE = Path(__file__).resolve().parent.parent
ROOT = Path(os.environ['JOURNEY_STEP_DIR']).resolve()
BIN = {name: Path(os.environ[name]).resolve() for name in ('HOST', 'MINI', 'STORE', 'VERIFIER', 'CONSENT_HOST')}
ROWS = []
COUNTER = 0
OWN_ROOT = False
W = ROOT / 'world'
A = W / 'sponsor'


def digest(path):
    with path.open('rb') as f:
        return hashlib.file_digest(f, 'sha256').hexdigest()


def run(*args):
    global COUNTER
    COUNTER += 1
    result = subprocess.run([str(a) for a in args], capture_output=True, text=True, timeout=180)
    (ROOT / f'call-{COUNTER:03d}.log').write_text(result.stdout + '\n--- stderr ---\n' + result.stderr)
    if result.returncode:
        raise RuntimeError(f'call {COUNTER} failed: {result.stderr[-1600:]}')
    return result


def last_json(text):
    for line in reversed(text.splitlines()):
        try:
            return json.loads(line)
        except json.JSONDecodeError:
            pass
    raise RuntimeError('call returned no JSON')


def mini(*args):
    return run(BIN['MINI'], *args)


def job(action):
    return last_json(mini('job', '--action', action, '--dir', A, '--name', 'refund').stdout)


def check(name, condition, detail):
    ROWS.append({'name': name, 'pass': bool(condition), 'detail': detail})
    (ROOT / 'checks.json').write_text(json.dumps(ROWS, indent=2) + '\n')
    print(f'{"PASS" if condition else "FAIL"} {name}: {detail}', flush=True)
    if not condition:
        raise RuntimeError(name)


def balance():
    text = mini('pay', 'status', '--dir', A, '--account', 'purse').stdout
    matched = re.search(r'credit (-?\d+)', text)
    if not matched:
        raise RuntimeError('native signed pay status did not report credit')
    return int(matched[1])


def stop():
    if not OWN_ROOT:
        return
    pidfile = W / 'public/server.pid'
    if pidfile.exists():
        try:
            os.kill(int(pidfile.read_text().strip()), signal.SIGTERM)
        except ProcessLookupError:
            pass


def exact_recovery(label, original, retained, settled_balance):
    ingress = digest(retained / 'ingress.bin')
    attempts = {p.name for p in (A / 'jobs').glob('refund.settle-*')}
    recovered = job('settle')
    receipt = recovered.get('outcome', {})
    keys = ('transactionId', 'eventId', 'acceptedCount', 'worldRoot')
    check(label + ' exact native receipt',
          original.get('type') == receipt.get('type') == 'confirmed'
          and all(original.get(k) is not None and original[k] == receipt.get(k) for k in keys)
          and receipt.get('confirmation') == 'replayed', {'original': original, 'recovered': recovered})
    check(label + ' lookup only, original custody',
          recovered.get('recovered') is True and recovered.get('resubmitted') is False
          and ingress == digest(retained / 'ingress.bin')
          and attempts == {p.name for p in (A / 'jobs').glob('refund.settle-*')}, recovered)
    current_balance = balance()
    fields = job('show')['fields']
    check(label + ' no second refund; closed native job',
          current_balance == settled_balance and fields.get('state') == '6'
          and fields.get('escrow') == fields.get('bond') == '0',
          {'balance': current_balance, 'fields': fields})


def main():
    global OWN_ROOT
    if ROOT.exists() or ROOT.is_symlink():
        raise RuntimeError('refusing existing receiving root')
    os.umask(0o077)
    ROOT.mkdir(mode=0o700)
    OWN_ROOT = True
    for name, binary in BIN.items():
        if not binary.is_file() or not os.access(binary, os.X_OK):
            raise RuntimeError(f'{name} is not an executable immutable artifact')
    (ROOT / 'pins.json').write_text(json.dumps({k: {'path': str(p), 'sha256': digest(p)} for k, p in BIN.items()}, indent=2) + '\n')
    # Select the local native provider independently; persist these exact local
    # pins when bootstrap creates each workspace. No operator/profile fallback.
    os.environ.update(MINI_LOCAL_HOST=str(BIN['HOST']), MINI_CONSENT_HOST=str(BIN['CONSENT_HOST']),
                      MINI_CONSENT_CONFIG=str(W / 'deployment/pinned-config.json'))
    # Short ROOT/socket required; standard bootstrap enforces SUN_LEN.
    run('sh', HERE / 'newparticipant-acceptance.sh', BIN['HOST'], BIN['MINI'], BIN['STORE'], BIN['VERIFIER'], W)
    (ROOT / 'configuration-pin.json').write_text(json.dumps({'path': str(W / 'deployment/pinned-config.json'), 'sha256': digest(W / 'deployment/pinned-config.json'), 'profile': json.loads((W / 'profile.json').read_text())}, indent=2) + '\n')
    mini('workspace', '--action', 'import', '--dir', A, '--name', 'purse', '--kind', 'account',
         '--target', '7', '--observe-capability', '41', '--operation-capability', '41')
    tariff = {'control': '53', 'book': [], 'tariff': {'version': '1', 'asset': '0', 'mint': '85' * 32,
              'tokenProgram': '06' * 32, 'decimals': '6', 'creditPerAtomic': '1', 'maxPerObservation': '2000000000',
              'minTickSlots': '1500', 'nodeHourRate': '5952380', 'enrolIndex': None, 'journalFloor': '1000000',
              'slashCallerPermille': '500'}}
    tariff_path = ROOT / 'tariff.json'
    tariff_path.write_text(json.dumps(tariff))
    mini('pay', 'book', '--dir', A, '--source', tariff_path)
    open_law = ROOT / 'open.json'
    open_law.write_text('{"type":"all","predicates":[]}\n')
    mini('workspace', '--action', 'create', '--dir', A, '--name', 'lab', '--storage', 'declared', '--predicate', open_law)
    posted = last_json(mini('job', '--action', 'post', '--dir', A, '--name', 'refund', '--room', 'lab',
                           '--program', '0', '--input', '0', '--price', '1000', '--deadline', '600', '--account', 'purse').stdout)
    fields = job('show')['fields']
    check('actual native funded order', posted.get('escrow') == '1000' and fields.get('state') == '0'
          and fields.get('escrow') == '1000', {'posted': posted, 'fields': fields})
    request = ROOT / 'void.request.json'
    request.write_text(json.dumps({'type': 'minidregg-workspace-proposal-v1', 'action': 'invoke', 'targets': [
        {'name': 'refund', 'payload': {'type': 'scalar', 'actions': [
            {'type': 'write', 'key': {'type': 'object', 'field': '0'}, 'expected': '0', 'value': '5'}]}}]}))
    mini('workspace', '--action', 'propose', '--dir', A, '--request', request, '--proposal-id', 'void-refund')
    mini('workspace', '--action', 'submit', '--dir', A, '--intent', A / 'proposals/void-refund/intent.json',
         '--attempt', A / 'attempts/void-refund')
    void = json.loads((A / 'attempts/void-refund/outcome.json').read_text())
    check('actual caller-authorized native void', void.get('type') == 'confirmed' and job('show')['fields'].get('state') == '5', void)
    before = balance()
    settled = job('settle')
    after = balance()
    original = settled.get('outcome', {})
    check('native Book refund exactly once', original.get('type') == 'confirmed' and after == before + 1000,
          {'before': before, 'after': after, 'settled': settled})
    attempts = list((A / 'jobs').glob('refund.settle-*'))
    if len(attempts) != 1:
        raise RuntimeError('expected exactly one retained settlement ingress')
    retained = attempts[0]
    custody = ROOT / 'hidden-confirmation'
    custody.mkdir()
    outcomes = list(retained.glob('outcome-*.json'))
    if not outcomes:
        raise RuntimeError('no retained native confirmation to simulate crash boundary')
    for path in outcomes:
        path.rename(custody / path.name)
    exact_recovery('missing confirmation', original, retained, after)
    # Legacy no-origin custody must remain recovery-only even after modern records.
    (retained / 'custody-origin.json').rename(ROOT / 'hidden-custody-origin.json')
    exact_recovery('legacy custody', original, retained, after)
    stop()
    ledger_path = ROOT / 'final-ledger.json'
    run(BIN['HOST'], W / 'deployment/pinned-config.json', 'pay-ledger', ledger_path)
    view_path = ROOT / 'final-job.json'
    run(BIN['HOST'], W / 'deployment/pinned-config.json', 'pay-job', posted['job'], view_path)
    view = json.loads(view_path.read_text())
    check('native final held account empty', view.get('bookHeld') == view.get('held') == '0', view)
    run(BIN['HOST'], W / 'deployment/pinned-config.json', 'audit')
    print('JOB-REFUND-RECOVERY PASS; provider payout and real socket loss remain OPEN')


if __name__ == '__main__':
    try:
        main()
    finally:
        stop()
