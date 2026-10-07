#!/usr/bin/env python3
"""Seats and invitations end to end on a scratch NATIVE world, every turn a signed command.

  objective-seat-native-acceptance.py --bin DIR --root NEW_DIR

A fresh private one-sponsor Store (newparticipant-acceptance.sh) whose genesis
pins this checkout's Objective invocation policy (its maximum envelope, tariff and
source bound are the seat kernel's configuration) and enrolls a second subject
(40, its own key and Book account). Never a live or common world. Two assets are
realm wells the sponsor founds (`mini well`): X (gold) and Y (kelp). Every seat
turn is `mini seat --action submit` (Host op 7 author, op 215 plan, the workspace
key signs the header, op 216 assemble, op 217 submit), every refusal is the
Host's, by name, and the public seat view (op 219) is read after each step,
with the Book's totals of X, Y and the credit asset (which never change).

  E1 publication  world/seats/Broker.obend made a contract artifact
                  (`objective-publication SPEC seat OUT`, the seat
                  kernel's output codec) and published; an instance created
                  on the sponsor's object; the subject 40 cannot invoke its method
                  (notObjectHolder) nor create an instance on it; the instance's
                  method mints the sell and buy invitations (code proposes, the
                  kernel mints under derived ids with the instance's package).
  E2 offers       Alice (the sponsor) offers give 10 X want >= 5 Y; Bob (40)
                  offers give 7 Y want >= 9 X; an offer funded from another
                  subject's account is refused (notAccountOwner); an offer
                  expecting another package is refused (assayFailed); a spent
                  invitation is refused.
  E4 raid         the method relays a raid (Alice gets 4 Y, loses 10 X): refused
                  by her seat's law (offerUnsafe), roots unchanged.
  E3 price moved  the method's swap moves each side's whole give: Alice holds
                  7 Y, Bob 10 X; both exit and are paid; totals never move.
  E5 locked       a second instance whose clause refuses every reallocation: the
                  method's swap is refused (contractClauseRefused), roots
                  unchanged, and Alice's exit still pays her 10 X back.
  E6 zero want    a gift seat (give 10 X, want 0 Y) is swept whole to Bob's seat:
                  admitted.
  E7 exits        a stranger's exit of an on-demand seat is refused
                  (exitNotAuthorized); a deadline seat's exit by a third party
                  before the due height is refused and after it admitted.
  E8 holder       naming a non-activity as a seat's holder, or an activity another
                  subject pays for, is refused (notActivityPayer); Alice's seat
                  held by her awaiting Tally activity (published, created, born by
                  `mini activity`) is CLOSED by that activity's end -- Bob's
                  delivery of the timed-out await -- in the same turn, paying her
                  back its 2 X; the record is retired.
  E9 lost reply   an exit prepared and not submitted: lookup finds nothing;
                  submit installs; resubmit and lookup replay. Reopen: the world's
                  `mini serve` restarts; the replay walk re-admits every seat turn;
                  a lookup returns the original receipt; the view is identical.

ROOT/transcript holds every command's exact output; ROOT/results.json lists every
row with its expectation and verdict; the script exits 1 on any mismatch.
"""
import argparse, json, os, pathlib, secrets, subprocess, sys, time
from activity_world import RESUME_KINDS, covering_body, published_extract_ticks, quote_request, quoted_heap

os.umask(0o077)
HERE = pathlib.Path(__file__).resolve().parent
REPO = HERE.parent.parent
ap = argparse.ArgumentParser()
ap.add_argument('mode', nargs='?', default='all', choices=['all'])  # journey-rows passes `all`, as to every driver
ap.add_argument('--bin', required=True)
ap.add_argument('--root', required=True)
a = ap.parse_args()
root = pathlib.Path(a.root).resolve()
if root.exists():
    raise SystemExit('root must be new')
root.mkdir(mode=0o700)
T = root / 'transcript'
T.mkdir()
binary = pathlib.Path(a.bin).resolve()
host, mini, store, verifier = [binary / n for n in
                               ['minidregg-host', 'mini', 'minidregg-link-sqlite-store',
                                'minidregg-credential-signature-verifier']]
counter = [0]
results = []


def sh(label, *cmd, ok=(0,), env=None):
    counter[0] += 1
    tag = f'{counter[0]:03d}-{label}'
    e = dict(os.environ)
    e.update(env or {})
    r = subprocess.run([str(c) for c in cmd], stdout=subprocess.PIPE, stderr=subprocess.PIPE, env=e)
    (T / f'{tag}.cmd').write_text(' '.join(str(c) for c in cmd) + '\n')
    (T / f'{tag}.out').write_bytes(r.stdout)
    (T / f'{tag}.err').write_bytes(r.stderr)
    (T / f'{tag}.rc').write_text(f'{r.returncode}\n')
    if r.returncode not in ok:
        raise SystemExit(f'FAILED {tag} rc={r.returncode}: {r.stderr.decode(errors="replace")[-1500:]}')
    return r


def last_json(r):
    text = r.stdout.decode(errors='replace').strip()
    if not text:
        return {'error': r.stderr.decode(errors='replace').strip()[-800:]}
    try:
        return json.loads(text.splitlines()[-1])
    except json.JSONDecodeError:
        return {'unparsed': text[-800:]}


def unhex(text):
    try:
        return bytes.fromhex(text).decode(errors='replace')
    except (ValueError, TypeError):
        return str(text)


def nat(n):
    return {'tag': 'natural', 'value': str(n)}


def label(s):
    return {'tag': 'label', 'value': s}


def record(**fields):
    return {'tag': 'record', 'fields': [{'name': k, 'value': v} for k, v in fields.items()]}


def variant(name, payload):
    return {'tag': 'variant', 'label': name, 'payload': payload}


def data_list(items):
    out = variant('nil', record())
    for item in reversed(items):
        out = variant('cons', record(head=item, tail=out))
    return out


# --- the world -----------------------------------------------------------------
MAXIMUM = {'typeFuel': 16384, 'sourceTicks': 200000, 'heap': 200000, 'stack': 200000, 'outputNodes': 20000,
           'outputBytes': 200000, 'extractTicks': 200000, 'inputBytes': 200000, 'scalarBits': 512, 'memoryTouches': 2000000,
           'proofWork': 900000, 'feeDebit': 1000000, 'turnBytes': 4000000, 'witnessBytes': 4000000,
           'storageBytes': 4000000, 'sideEffectCount': 16, 'networkBytes': 0, 'leaseByteBlocks': 0,
           'incidences': 16}
constants = json.loads(sh('constants', host, '/dev/null', 'objective-constants').stdout)
tariff = {'version': '2', 'base': '1', 'typeFuel': '0', 'sourceTicks': '1', 'heap': '0', 'stack': '0',
          'outputNodes': '0', 'outputBytes': '0', 'extractTicks': '0', 'inputBytes': '0'}
policy = {'schema': 'dregg.objective-bend.policy.v1', 'sourceBytes': '4194304',
          'maximum': {k: str(v) for k, v in MAXIMUM.items()}, 'extractTicksPerTurn': str(16 * MAXIMUM['extractTicks']), 'outputs': [constants['genericCodec']],
          'clearAudience': '01ff', 'frontEnd': constants['frontEnd'], 'tariff': tariff}
(root / 'policy.json').write_text(json.dumps(policy, indent=1))
sh('policy', host, '/dev/null', 'author', 'objective-policy', root / 'policy.json', root / 'policy.hex')

sh('keygen-40', mini, 'keygen', '--secret', root / 'subject40.key', '--public', root / 'subject40.pub')
public40 = (root / 'subject40.pub').read_bytes().hex()
BOB = '40'
enrollment = [{'key': {'keyId': '4000', 'keyEpoch': '2', 'algorithm': '1', 'subject': BOB,
                       'publicKey': public40, 'activeFrom': '0', 'activeUntil': '1000000', 'nextKeyDigest': None},
               'accountId': BOB, 'spendCapabilityId': '4002', 'controlCapabilityId': '4003',
               'factoryObserveCapabilityId': '4004', 'initialBalance': '100000',
               'accountPredicate': {'type': 'all', 'predicates': []}}]
(root / 'enrollment-40.json').write_text(json.dumps(enrollment))
W = root / 'w'
sock = W / 'public' / 'mini.sock'
sh('genesis', 'sh', HERE / 'newparticipant-acceptance.sh', host, mini, store, verifier, W, sock,
   env={'OBJECTIVE_INVOCATION_POLICY': (root / 'policy.hex').read_text().strip(),
        'EXTRA_GENESIS_ENROLLMENTS': str(root / 'enrollment-40.json'),
        'NEWPARTICIPANT_SPONSOR_BALANCE': '1000000'})
config = W / 'deployment' / 'pinned-config.json'
alice_ws = W / 'sponsor'
bob_ws = root / 'subject40'
bob_ws.mkdir(mode=0o700)
(bob_ws / 'workspace.json').write_text(json.dumps({
    'type': 'minidregg-participant-workspace-v1', 'host': str(host), 'socket': str(sock), 'config': str(config),
    'key': str(root / 'subject40.key'), 'subject': BOB}))
params = json.loads((W / 'genesis-params.json').read_text())
ALICE = str(params['sponsor']['subject'])
ALICE_ACCOUNT = str(params['sponsor']['accountId'])
ALICE_SPEND = str(params['sponsor']['spendCapabilityId'])
BOB_ACCOUNT = BOB
BOB_SPEND = '4002'
COLLECTOR = str(params['collector'])
permit = root / 'permit-all.json'
permit.write_text('{"type":"all","predicates":[]}\n')

# Two assets: realm wells the sponsor founds and mints from (`mini well`).
sh('create-realm', mini, 'workspace', '--action', 'create', '--dir', alice_ws, '--name', 'bazaar',
   '--storage', 'declared', '--predicate', permit)
for name in ['gold', 'kelp']:
    sh(f'well-new-{name}', mini, 'well', '--action', 'new', '--dir', alice_ws, '--name', name, '--in', 'bazaar',
       '--law', permit)
X = json.loads((alice_ws / 'refs' / 'gold.json').read_text())['target']
Y = json.loads((alice_ws / 'refs' / 'kelp.json').read_text())['target']


def mint(asset_name, account, amount):
    sh(f'mint-{asset_name}-{account}-{amount}', mini, 'well', '--action', 'mint', '--dir', alice_ws,
       '--well', asset_name, '--account', account, '--amount', str(amount))


objects = {}
for name in ['swap', 'locked']:
    sh(f'create-object-{name}', mini, 'workspace', '--action', 'create', '--dir', alice_ws,
       '--name', f'instance-{name}', '--storage', 'content', '--predicate', permit)
    ref = json.loads((alice_ws / 'refs' / f'instance-{name}.json').read_text())
    objects[name] = {'object': ref['target'], 'capability': ref['operationCapability']}
(root / 'objects.json').write_text(json.dumps(objects, indent=1))
CREDIT = None

# --- turns and views -----------------------------------------------------------
attempts = root / 'attempts'
attempts.mkdir()


def view(tag, request):
    r = sh(f'view-{tag}', mini, 'seat', '--action', 'view', '--workspace', alice_ws, '--request', json.dumps(request))
    return last_json(r)


totals = []


def judge(tag, value, expect, detail):
    kind = value.get('type')
    reason = value.get('reason', '')
    text = unhex(value.get('detail', '')) if 'detail' in value else value.get('error', '')
    if expect == 'installed':
        ok = kind == 'confirmed' and value.get('confirmation') == 'installed'
    elif expect == 'replayed':
        ok = kind == 'confirmed' and value.get('confirmation') == 'replayed'
    elif expect == 'prepared':
        ok = kind == 'prepared'
    elif expect == 'absent':
        ok = kind == 'absent'
    elif expect == 'conflict':
        ok = kind == 'refused' and reason == 'conflict'
    else:
        ok = kind == 'refused' or 'refused' in str(value.get('error', ''))
    if ok and detail is not None:
        ok = detail in text
    results.append({'step': tag, 'expect': expect, 'detailExpected': detail, 'type': kind,
                    'reason': reason, 'detail': text[-300:], 'ok': ok})
    print(f'{tag:44} {expect:9} {kind} {reason} {text[-140:]}', flush=True)
    return value


def check(tag, condition, observed):
    results.append({'step': tag, 'expect': 'check', 'ok': bool(condition), 'observed': observed})
    print(f'{tag:44} check     {"ok" if condition else "MISMATCH"} {json.dumps(observed)[:200]}', flush=True)


def turn(tag, workspace, body, expect, detail=None, prepare=False, object_cap=None, account_cap=None,
         confirm_donation=False):
    out = attempts / tag
    command = root / f'{tag}.command.json'
    file = {'turn': body}
    if object_cap is not None:
        file['objectCapability'] = object_cap
    if account_cap is not None:
        file['accountCapability'] = account_cap
    if confirm_donation:
        file['confirmDonation'] = True
    command.write_text(json.dumps(file))
    args = ['seat', '--action', 'submit', '--workspace', workspace, '--command', command, '--out', out]
    if prepare:
        args += ['--prepare-only', 'true']
    value = last_json(sh(tag, mini, *args, ok=(0, 1, 2)))
    return judge(tag, value, expect, detail)


def balances(v):
    return {(b['account'], b['asset']): int(b['balance']) for b in (v.get('balances') or [])}


def registered(v, account):
    return next((b['registered'] for b in (v.get('balances') or []) if b['account'] == str(account)), None)


def cell(v, cell_id):
    return next((c for c in v.get('cells', []) if c.get('cell') == str(cell_id)), {})


def world(tag, seats=(), instances=(), invitations=()):
    v = view(tag, {'instances': list(instances), 'invitations': list(invitations), 'seats': list(seats),
                   'accounts': [ALICE_ACCOUNT, BOB_ACCOUNT, COLLECTOR, X, Y] + list(seats),
                   'assets': [X, Y] + ([CREDIT] if CREDIT else [])})
    b = balances(v)
    totals.append({'after': tag, 'height': v.get('height'),
                   'totals': {t['asset']: t['total'] for t in (v.get('totals') or [])},
                   'minted': {X: -b.get((X, X), 0), Y: -b.get((Y, Y), 0)}})
    return v


def roots(v):
    return {c['cell']: c['root'] for c in v.get('cells', [])}


_EXTRACT = []


def extract_ticks():
    """The extraction budget the Host publishes (`limits.extractTicks` = `config.maxExtractTicks`), asked
    once from the public activity view; it must equal the policy this world authored."""
    if not _EXTRACT:
        _EXTRACT.append(published_extract_ticks(last_json(sh('limits-view', mini, 'activity', '--action', 'view',
                                                             '--workspace', alice_ws, '--request', '{}'))))
        check('extract-quote-is-the-policy-ceiling', _EXTRACT[0] == 16 * MAXIMUM['extractTicks'],
              {'published': _EXTRACT[0], 'policy': 16 * MAXIMUM['extractTicks']})
    return _EXTRACT[0]


def activity_cap(ticks):
    """A declared envelope (Capacity): `ticks` source ticks, the kernel's fixed heap, stack,
    type fuel and Plan budget, priced at 0 (as the activity driver's `cap`), and the published
    extraction budget."""
    c = {k: '0' for k in MAXIMUM}
    for k in ['heap', 'stack', 'typeFuel', 'outputNodes', 'outputBytes']:
        c[k] = str(MAXIMUM[k])
    c['extractTicks'] = str(extract_ticks())
    c['sourceTicks'] = str(ticks)
    return c


def invoke(tag, workspace, inst, inp, expect, detail=None, object_cap=None, account=ALICE_ACCOUNT,
           account_cap=ALICE_SPEND, ticks=2000, prepare=False):
    return turn(tag, workspace, {'kind': 'invoke', 'instance': objects[inst]['object'], 'input': inp,
                                 'envelope': activity_cap(ticks), 'account': account},
                expect, detail, prepare, object_cap=object_cap or objects[inst]['capability'],
                account_cap=account_cap)


def mint_input(role, holder):
    return variant('mint', record(role=label(role), holder=nat(int(holder))))


def move(source, destination, asset, amount):
    return record(source=nat(int(source)), destination=nat(int(destination)), asset=nat(int(asset)),
                  amount=nat(amount))


def offer(tag, workspace, inst, invitation, role, give, want, expect, detail=None, funding=None, account_cap=None,
          package=None, deadline=None, holder=None, donate=False):
    proposal = {'give': [{'asset': a_, 'amount': str(n)} for a_, n in give],
                'want': [{'asset': a_, 'amount': str(n)} for a_, n in want], 'donate': donate}
    if deadline is not None:
        proposal['afterDeadline'] = str(deadline)
    body = {'kind': 'offer', 'invitation': invitation,
            'expect': {'instance': objects[inst]['object'], 'package': package or PIN, 'role': role},
            'funding': funding, 'payee': funding, 'proposal': proposal, 'holder': holder}
    value = turn(tag, workspace, body, expect, detail, account_cap=account_cap, confirm_donation=donate)
    return value.get('seatAccount')


def exit_(tag, workspace, seat, expect, detail=None, prepare=False):
    return turn(tag, workspace, {'kind': 'exit', 'seat': seat}, expect, detail, prepare)


# --- E1: publication, instance, invitations -----------------------------------------
pub = root / 'publication'
pub.mkdir()
spec = {'schema': 'dregg.objective-bend.package-input.v1', 'edition': 'objective-bend-1',
        'modules': [{'name': 'Broker', 'sourcePath': str(REPO / 'world/seats/Broker.obend'), 'imports': []}],
        'entryModule': '0', 'entryDefinition': 'broker'}
(pub / 'spec.json').write_text(json.dumps(spec))
published = last_json(sh('publication', host, config, 'objective-publication', pub / 'spec.json', 'seat', pub / 'out'))
PIN = published['artifactId']
ARTIFACT_HEX = (pub / 'out' / 'artifact.bin').read_bytes().hex()
PACKAGE_HEX = (pub / 'out' / 'package.bin').read_bytes().hex()
v0 = view('credit', {})
mint('gold', ALICE_ACCOUNT, 30)
mint('kelp', BOB_ACCOUNT, 21)
start = world('genesis')
turn('E1-publish', alice_ws, {'kind': 'publish', 'artifact': ARTIFACT_HEX, 'package': PACKAGE_HEX,
     'payer': ALICE_ACCOUNT}, 'installed', account_cap=ALICE_SPEND)
turn('E1-republish-conflicts', bob_ws, {'kind': 'publish', 'artifact': ARTIFACT_HEX, 'package': PACKAGE_HEX,
     'payer': BOB_ACCOUNT}, 'conflict', account_cap=BOB_SPEND)
turn('E1-stranger-create-refused', bob_ws, {'kind': 'create', 'instance': objects['swap']['object'], 'pin': PIN,
     'clause': {'type': 'all', 'predicates': []}}, 'refused', 'notObjectHolder',
     object_cap=objects['swap']['capability'])
turn('E1-create', alice_ws, {'kind': 'create', 'instance': objects['swap']['object'], 'pin': PIN,
     'clause': {'type': 'all', 'predicates': []}}, 'installed', object_cap=objects['swap']['capability'])
turn('E1-create-again-refused', alice_ws, {'kind': 'create', 'instance': objects['swap']['object'], 'pin': PIN,
     'clause': {'type': 'all', 'predicates': []}}, 'refused', 'instanceExists',
     object_cap=objects['swap']['capability'])
invoke('E1-stranger-mint-refused', bob_ws, 'swap', mint_input('sell', BOB), 'refused', 'notObjectHolder',
       account=BOB_ACCOUNT, account_cap=BOB_SPEND)
sell = invoke('E1-mint-sell', alice_ws, 'swap', mint_input('sell', ALICE), 'installed')['mintIds'][0]
buy = invoke('E1-mint-buy', alice_ws, 'swap', mint_input('buy', BOB), 'installed')['mintIds'][0]
v = world('minted', instances=[objects['swap']['object']], invitations=[sell, buy])
inv_sell = next((c.get('invitation') for c in v['cells'] if c.get('kind') == 'invitation'
                 and c['invitation']['id'] == sell), {})
check('E1-invitation-from-code', inv_sell.get('package') == PIN and inv_sell.get('role') == 'sell'
      and inv_sell.get('holder') == ALICE and inv_sell.get('instance') == objects['swap']['object'], inv_sell)

# --- E2: offers ---------------------------------------------------------------------
offer('E2-foreign-funding-refused', bob_ws, 'swap', buy, 'buy', [(X, 1)], [(Y, 1)], 'refused', 'notAccountOwner',
      funding=ALICE_ACCOUNT, account_cap=BOB_SPEND)
offer('E2-wrong-package-refused', alice_ws, 'swap', sell, 'sell', [(X, 10)], [(Y, 5)], 'refused', 'assayFailed',
      funding=ALICE_ACCOUNT, account_cap=ALICE_SPEND, package='12345')
alice_seat = offer('E2-alice-offers', alice_ws, 'swap', sell, 'sell', [(X, 10)], [(Y, 5)], 'installed',
                   funding=ALICE_ACCOUNT, account_cap=ALICE_SPEND)
bob_seat = offer('E2-bob-offers', bob_ws, 'swap', buy, 'buy', [(Y, 7)], [(X, 9)], 'installed',
                 funding=BOB_ACCOUNT, account_cap=BOB_SPEND)
offer('E2-spent-invitation-refused', alice_ws, 'swap', sell, 'sell', [(X, 10)], [(Y, 5)], 'refused',
      'invitationMissing', funding=ALICE_ACCOUNT, account_cap=ALICE_SPEND)
v = world('offered', seats=[alice_seat, bob_seat], instances=[objects['swap']['object']])
b = balances(v)
check('E2-seats-funded', b.get((alice_seat, X)) == 10 and b.get((bob_seat, Y)) == 7,
      {'aliceSeatX': b.get((alice_seat, X)), 'bobSeatY': b.get((bob_seat, Y))})
check('E2-seat-accounts-protected', int(alice_seat) >= 2 ** 256 and int(bob_seat) >= 2 ** 256,
      {'alice': alice_seat, 'bob': bob_seat})

# --- E4: a raid the code proposes is refused by the seat law ---------------------------
before = roots(v)
invoke('E4-raid-refused', alice_ws, 'swap',
       variant('relay', record(moves=data_list([move(alice_seat, bob_seat, X, 10), move(bob_seat, alice_seat, Y, 4)]))),
       'refused', 'offerUnsafe')
v = world('after-raid', seats=[alice_seat, bob_seat], instances=[objects['swap']['object']])
check('E4-roots-unchanged', roots(v) == before, {'changed': [k for k in roots(v) if roots(v)[k] != before.get(k)]})

# --- E3: the price moved; the swap settles -----------------------------------------------
invoke('E3-swap', alice_ws, 'swap', variant('swap', record(sell=nat(int(alice_seat)), buy=nat(int(bob_seat)),
       give=nat(int(X)), take=nat(int(Y)))), 'installed')
v = world('swapped', seats=[alice_seat, bob_seat])
b = balances(v)
check('E3-alice-seat-holds-7Y', b.get((alice_seat, Y)) == 7 and b.get((alice_seat, X)) == 0,
      {'X': b.get((alice_seat, X)), 'Y': b.get((alice_seat, Y))})
check('E3-bob-seat-holds-10X', b.get((bob_seat, X)) == 10 and b.get((bob_seat, Y)) == 0,
      {'X': b.get((bob_seat, X)), 'Y': b.get((bob_seat, Y))})
exit_('E7-stranger-exit-refused', bob_ws, alice_seat, 'refused', 'exitNotAuthorized')
before_pay = balances(world('before-exits'))
exit_('E3-alice-exits', alice_ws, alice_seat, 'installed')
exit_('E3-bob-exits', bob_ws, bob_seat, 'installed')
exit_('E3-exit-twice-refused', alice_ws, alice_seat, 'refused', 'seatMissing')
b = balances(world('settled', seats=[alice_seat, bob_seat], instances=[objects['swap']['object']]))
check('E3-exit-deregisters-seat-accounts',
      registered(world('settled-accounts', seats=[alice_seat, bob_seat]), alice_seat) is False
      and registered(world('settled-accounts-bob', seats=[alice_seat, bob_seat]), bob_seat) is False,
      'seat accounts still registered')
check('E3-exit-retires-seat-cells',
      all(cell(world('settled-cells', seats=[alice_seat, bob_seat]), s).get('kind') == 'retired'
          for s in (alice_seat, bob_seat)), 'seat cells not retired')
check('E3-alice-paid-7Y', b[(ALICE_ACCOUNT, Y)] - before_pay[(ALICE_ACCOUNT, Y)] == 7, b[(ALICE_ACCOUNT, Y)])
check('E3-bob-paid-10X', b[(BOB_ACCOUNT, X)] - before_pay[(BOB_ACCOUNT, X)] == 10, b[(BOB_ACCOUNT, X)])

# --- E5: a locked contract cannot stop exit ------------------------------------------
turn('E5-create-locked', alice_ws, {'kind': 'create', 'instance': objects['locked']['object'], 'pin': PIN,
     'clause': {'type': 'any', 'predicates': []}}, 'installed', object_cap=objects['locked']['capability'])
lsell = invoke('E5-mint-sell', alice_ws, 'locked', mint_input('sell', ALICE), 'installed')['mintIds'][0]
lbuy = invoke('E5-mint-buy', alice_ws, 'locked', mint_input('buy', BOB), 'installed')['mintIds'][0]
la = offer('E5-alice-offers', alice_ws, 'locked', lsell, 'sell', [(X, 10)], [(Y, 5)], 'installed',
           funding=ALICE_ACCOUNT, account_cap=ALICE_SPEND)
lb = offer('E5-bob-offers', bob_ws, 'locked', lbuy, 'buy', [(Y, 7)], [(X, 9)], 'installed',
           funding=BOB_ACCOUNT, account_cap=BOB_SPEND)
v = world('locked-open', seats=[la, lb], instances=[objects['locked']['object']])
before = roots(v)
invoke('E5-swap-refused', alice_ws, 'locked', variant('swap', record(sell=nat(int(la)), buy=nat(int(lb)),
       give=nat(int(X)), take=nat(int(Y)))), 'refused', 'contractClauseRefused')
v = world('locked-after', seats=[la, lb], instances=[objects['locked']['object']])
check('E5-roots-unchanged', roots(v) == before, {'changed': [k for k in roots(v) if roots(v)[k] != before.get(k)]})
before_pay = balances(v)
exit_('E5-alice-exits', alice_ws, la, 'installed')
exit_('E5-bob-exits', bob_ws, lb, 'installed')
b = balances(world('locked-exited', seats=[la, lb]))
check('E5-alice-paid-10X-back', b[(ALICE_ACCOUNT, X)] - before_pay[(ALICE_ACCOUNT, X)] == 10, b[(ALICE_ACCOUNT, X)])

# --- E6: zero want --------------------------------------------------------------------
gsell = invoke('E6-mint-gift', alice_ws, 'swap', mint_input('gift', ALICE), 'installed')['mintIds'][0]
gbuy = invoke('E6-mint-take', alice_ws, 'swap', mint_input('take', BOB), 'installed')['mintIds'][0]
offer('E6-unmarked-zero-want-refused', alice_ws, 'swap', gsell, 'gift', [(X, 10)], [(Y, 0)], 'refused',
      'donationUnmarked', funding=ALICE_ACCOUNT, account_cap=ALICE_SPEND)
offer('E6-unmarked-empty-want-refused', alice_ws, 'swap', gsell, 'gift', [(X, 10)], [], 'refused',
      'donationUnmarked', funding=ALICE_ACCOUNT, account_cap=ALICE_SPEND)
offer('E6-marker-on-a-real-want-refused', alice_ws, 'swap', gsell, 'gift', [(X, 10)], [(Y, 1)], 'refused',
      'donationMarkedWithWant', funding=ALICE_ACCOUNT, account_cap=ALICE_SPEND, donate=True)
gift = offer('E6-gift-offer', alice_ws, 'swap', gsell, 'gift', [(X, 10)], [(Y, 0)], 'installed',
             funding=ALICE_ACCOUNT, account_cap=ALICE_SPEND, donate=True)
take = offer('E6-taker-offer', bob_ws, 'swap', gbuy, 'take', [], [(X, 1)], 'installed',
             funding=BOB_ACCOUNT, account_cap=BOB_SPEND)
invoke('E6-sweep-gift', alice_ws, 'swap', variant('sweep', record(source=nat(int(gift)),
       destination=nat(int(take)), asset=nat(int(X)))), 'installed')
b = balances(world('gift-taken', seats=[gift, take]))
check('E6-gift-taken-whole', b.get((gift, X)) == 0 and b.get((take, X)) == 10,
      {'gift': b.get((gift, X)), 'take': b.get((take, X))})
exit_('E6-taker-exits', bob_ws, take, 'installed')

# --- E7: deadlines --------------------------------------------------------------------
dsell = invoke('E7-mint-deadline', alice_ws, 'swap', mint_input('patient', ALICE), 'installed')['mintIds'][0]
due = int(view('height', {})['height']) + 4
dseat = offer('E7-deadline-offer', alice_ws, 'swap', dsell, 'patient', [(X, 5)], [(Y, 1)], 'installed',
              funding=ALICE_ACCOUNT, account_cap=ALICE_SPEND, deadline=due)
exit_('E7-offerer-before-due-refused', alice_ws, dseat, 'refused', 'exitNotAuthorized')
exit_('E7-third-party-before-due-refused', bob_ws, dseat, 'refused', 'exitNotAuthorized')
pad = 0
while int(view('height', {})['height']) < due and pad < 8:
    pad += 1
    if invoke(f'E7-pass-height-{pad}', alice_ws, 'swap', mint_input('filler', ALICE),
              'installed').get('type') != 'confirmed':
        break
before_pay = balances(world('due', seats=[dseat]))
exit_('E7-third-party-after-due', bob_ws, dseat, 'installed')
b = balances(world('deadline-exited', seats=[dseat]))
check('E7-deadline-paid-offerer', b[(ALICE_ACCOUNT, X)] - before_pay[(ALICE_ACCOUNT, X)] == 5, b[(ALICE_ACCOUNT, X)])

# --- E8: an activity as a seat's holder -------------------------------------------------
# Only the payer of an AWAITING activity may make it a seat's holder; the activity's end
# closes the seat in the same turn (ActivitySeatEnd: one Book batch; the offerer is paid).
# The activity is the Tally of world/activity, published with the activity codec, born
# by Alice (its payer) with Bob as its decider; nobody decides, so the deadline passes
# and Bob's delivery of the timed-out await ENDS it -- natively, by signed commands.
hsell = invoke('E8-mint', alice_ws, 'swap', mint_input('held', ALICE), 'installed')['mintIds'][0]
v = world('before-held', instances=[objects['swap']['object']], invitations=[hsell])
before = roots(v)
offer('E8-holder-not-an-awaiting-activity-refused', alice_ws, 'swap', hsell, 'held', [(X, 2)], [(Y, 1)], 'refused',
      'notActivityPayer', funding=ALICE_ACCOUNT, account_cap=ALICE_SPEND, holder=objects['swap']['object'])
v = world('after-held-refused', instances=[objects['swap']['object']], invitations=[hsell])
check('E8-roots-unchanged', roots(v) == before, {'changed': [k for k in roots(v) if roots(v)[k] != before.get(k)]})


def activity_submit(tag, workspace, body):
    out = attempts / tag
    command = root / f'{tag}.turn.json'
    command.write_text(json.dumps(body))
    return last_json(sh(tag, mini, 'activity', '--action', 'submit', '--workspace', workspace,
                        '--command', command, '--out', out, ok=(0, 1, 2)))


def activity(tag, workspace, body, expect, detail=None):
    """A deliver or exhaust first asks the Host's quote for the heap its checkpoint needs and declares it in
    `extra`, paid by the submitter (activity_world.py)."""
    if body.get('kind') in RESUME_KINDS:
        payer = (BOB_ACCOUNT, BOB_SPEND) if pathlib.Path(workspace) == bob_ws else (ALICE_ACCOUNT, ALICE_SPEND)
        quote = quoted_heap(last_json(sh(f'{tag}-quote', mini, 'activity', '--action', 'view', '--workspace',
                                         workspace, '--request', json.dumps(quote_request(body)))))
        body = covering_body(body, quote, payer)
    return judge(tag, activity_submit(tag, workspace, body), expect, detail)


def activity_view(tag, request):
    return last_json(sh(f'activity-view-{tag}', mini, 'activity', '--action', 'view', '--workspace', alice_ws,
                        '--request', json.dumps(request)))


hpub = root / 'held-publication'
hpub.mkdir()
(hpub / 'spec.json').write_text(json.dumps({
    'schema': 'dregg.objective-bend.package-input.v1', 'edition': 'objective-bend-1',
    'modules': [{'name': 'Tally', 'sourcePath': str(REPO / 'world/activity/Tally.obend'), 'imports': []}],
    'entryModule': '0', 'entryDefinition': 'tally'}))
TALLY_PIN = last_json(sh('held-publication', host, config, 'objective-publication', hpub / 'spec.json', 'activity',
                         hpub / 'out'))['artifactId']
activity('E8-publish-tally', alice_ws, {'kind': 'publish', 'artifact': (hpub / 'out' / 'artifact.bin').read_bytes().hex(),
         'package': (hpub / 'out' / 'package.bin').read_bytes().hex(), 'payer': ALICE_ACCOUNT,
         'payerCapability': ALICE_SPEND}, 'installed')
sh('create-object-held', mini, 'workspace', '--action', 'create', '--dir', alice_ws, '--name', 'held-tally',
   '--storage', 'content', '--predicate', permit)
href = json.loads((alice_ws / 'refs' / 'held-tally.json').read_text())
HELD = {'object': href['target'], 'capability': href['operationCapability']}
activity('E8-create-tally', alice_ws, {'kind': 'create', 'object': HELD['object'], 'objectCapability': HELD['capability'],
         'pin': TALLY_PIN, 'stateType': {'tag': 'field', 'name': 'total', 'member': {'tag': 'natural'}, 'tail': {'tag': 'emptyRow'}},
         'law': {'type': 'all', 'predicates': []}, 'upgrade': {'frozen': {}},
         'payer': ALICE_ACCOUNT, 'payerCapability': ALICE_SPEND}, 'installed')
TICKS = 3000
born = activity('E8-birth-tally', alice_ws, {'kind': 'birth', 'object': HELD['object'],
                'objectCapability': HELD['capability'], 'account': ALICE_ACCOUNT, 'accountCapability': ALICE_SPEND,
                'pin': TALLY_PIN, 'input': record(init=variant('set', nat(0)), decider=nat(int(BOB))),
                'envelope': activity_cap(TICKS), 'resume': activity_cap(TICKS), 'timeout': activity_cap(TICKS),
                'deposit': '20000'}, 'installed')


def held_state(tag):
    hv = activity_view(tag, {'objects': [HELD['object']],
                             'births': [{'object': HELD['object'], 'transaction': born.get('transaction')}]})
    rec_cell = hv['births'][0]['record']
    return rec_cell, next((c for c in hv.get('cells', []) if c.get('cell') == rec_cell), {})


HREC, hrec = held_state('held-born')
check('E8-activity-awaiting', hrec.get('record', {}).get('phase', {}).get('kind') == 'awaiting', hrec.get('kind'))
hawait = hrec['record']['phase']['await']
hbob = invoke('E8-mint-bob', alice_ws, 'swap', mint_input('held', BOB), 'installed')['mintIds'][0]
offer('E8-stranger-holder-refused', bob_ws, 'swap', hbob, 'held', [(Y, 1)], [(X, 1)], 'refused',
      'notActivityPayer', funding=BOB_ACCOUNT, account_cap=BOB_SPEND, holder=HREC)
pre_held = balances(world('before-held-seat'))
held_seat = offer('E8-held-seat', alice_ws, 'swap', hsell, 'held', [(X, 2)], [(Y, 1)], 'installed',
                  funding=ALICE_ACCOUNT, account_cap=ALICE_SPEND, holder=HREC)
v = world('held-seat-open', seats=[held_seat])
b = balances(v)
check('E8-held-seat-funded', b.get((held_seat, X)) == 2
      and b.get((ALICE_ACCOUNT, X)) == pre_held.get((ALICE_ACCOUNT, X)) - 2,
      {'seatX': b.get((held_seat, X)), 'aliceX': [pre_held.get((ALICE_ACCOUNT, X)), b.get((ALICE_ACCOUNT, X))]})
held_cell = cell(v, held_seat)
check('E8-held-seat-names-holder', held_cell.get('seat', {}).get('holder') == HREC, held_cell)
passes = 0
while int(activity_view('height-held', {})['height']) <= int(hawait['deadline']):
    passes += 1
    activity(f'E8-pass-height-{passes}', alice_ws, {'kind': 'topUp', 'record': HREC, 'account': ALICE_ACCOUNT,
             'accountCapability': ALICE_SPEND, 'amount': '1'}, 'installed')
activity('E8-activity-ends', bob_ws, {'kind': 'deliver', 'record': HREC, 'await': hawait['id'],
         'account': '0', 'accountCapability': '0'}, 'installed')
_, hrec_after = held_state('held-ended')
check('E8-activity-retired', hrec_after.get('kind') == 'retired', hrec_after.get('kind'))
v = world('held-seat-closed', seats=[held_seat])
b = balances(v)
held_after = cell(v, held_seat)
check('E8-activity-end-retires-held-seat', held_after.get('kind') == 'retired', held_after)
check('E8-activity-end-deregisters-held-seat', registered(v, held_seat) is False, registered(v, held_seat))
check('E8-held-seat-pays-offerer', b.get((held_seat, X)) == 0
      and b.get((ALICE_ACCOUNT, X)) == pre_held.get((ALICE_ACCOUNT, X)),
      {'seatX': b.get((held_seat, X)), 'aliceX': [pre_held.get((ALICE_ACCOUNT, X)), b.get((ALICE_ACCOUNT, X))]})

# --- E9: lost reply and reopen ---------------------------------------------------------
lsell2 = invoke('E9-mint', alice_ws, 'swap', mint_input('lost', ALICE), 'installed')['mintIds'][0]
lost = offer('E9-offer', alice_ws, 'swap', lsell2, 'lost', [(X, 3)], [(Y, 1)], 'installed',
             funding=ALICE_ACCOUNT, account_cap=ALICE_SPEND)
prepared = exit_('E9-exit-prepared', alice_ws, lost, 'prepared', prepare=True)
ingress = prepared.get('ingress')
judge('E9-lookup-before-submit', last_json(sh('E9-lookup-before', mini, 'seat', '--action', 'lookup',
      '--workspace', alice_ws, '--ingress', ingress, ok=(0, 1, 2))), 'absent', None)
judge('E9-submit', last_json(sh('E9-submit', mini, 'seat', '--action', 'resubmit', '--workspace', alice_ws,
      '--ingress', ingress, ok=(0, 1, 2))), 'installed', None)
judge('E9-resubmit-replays', last_json(sh('E9-resubmit', mini, 'seat', '--action', 'resubmit', '--workspace',
      alice_ws, '--ingress', ingress, ok=(0, 1, 2))), 'replayed', None)
judge('E9-lookup-replays', last_json(sh('E9-lookup', mini, 'seat', '--action', 'lookup', '--workspace', alice_ws,
      '--ingress', ingress, ok=(0, 1, 2))), 'replayed', None)

ALL_SEATS = [alice_seat, bob_seat, la, lb, gift, take, dseat, lost]
ALL_INSTANCES = [objects['swap']['object'], objects['locked']['object']]
final = world('before-reopen', seats=ALL_SEATS, instances=ALL_INSTANCES, invitations=[sell, buy, lsell, lbuy])
pid = int((W / 'public' / 'server.pid').read_text())
try:
    os.kill(pid, 15)
except ProcessLookupError:
    pass
for _ in range(600):
    try:
        os.kill(pid, 0)
        time.sleep(0.1)
    except ProcessLookupError:
        break
if sock.exists():
    sock.unlink()
log = open(W / 'public' / 'serve-reopen.log', 'ab')
p = subprocess.Popen([str(mini), 'serve', '--host', str(host), '--config', str(config), '--socket', str(sock)],
                     stdout=log, stderr=log, stdin=subprocess.DEVNULL, start_new_session=True)
(W / 'public' / 'server.pid').write_text(f'{p.pid}\n')
t0 = time.time()
while not sock.exists():
    if p.poll() is not None:
        raise SystemExit('reopened server exited: see serve-reopen.log')
    if time.time() - t0 > 900:
        raise SystemExit('reopened server socket did not appear')
    time.sleep(0.2)
judge('E9-lookup-after-reopen', last_json(sh('E9-lookup-reopen', mini, 'seat', '--action', 'lookup', '--workspace',
      alice_ws, '--ingress', ingress, ok=(0, 1, 2))), 'replayed', None)
reopened = world('after-reopen', seats=ALL_SEATS, instances=ALL_INSTANCES, invitations=[sell, buy, lsell, lbuy])
keys = ['height', 'cells', 'balances', 'totals']
check('E9-reopen-view-identical', {k: reopened.get(k) for k in keys} == {k: final.get(k) for k in keys},
      {'before': final.get('height'), 'after': reopened.get('height')})

# --- conservation ---------------------------------------------------------------------
xs = {t['totals'].get(X) for t in totals}
ys = {t['totals'].get(Y) for t in totals}
check('X-total-constant', len(xs) == 1, sorted(xs, key=str))
check('Y-total-constant', len(ys) == 1, sorted(ys, key=str))
mx = {t['minted'][X] for t in totals}
my = {t['minted'][Y] for t in totals}
check('X-minted-constant-across-seat-turns', mx == {30}, sorted(mx))
check('Y-minted-constant-across-seat-turns', my == {21}, sorted(my))

(root / 'results.json').write_text(json.dumps({
    'rows': results, 'totals': totals, 'pin': PIN, 'objects': objects, 'assets': {'X': X, 'Y': Y},
    'seats': ALL_SEATS + [held_seat]}, indent=1))
bad = [r for r in results if not r['ok']]
print(f'{len(results) - len(bad)}/{len(results)} rows ok; results in {root / "results.json"}')
sys.exit(1 if bad else 0)
