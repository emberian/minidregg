#!/usr/bin/env python3
"""A bounty whose reward is held by the seat kernel, end to end on a scratch NATIVE world, every turn a signed command.

  objective-bounty-native-acceptance.py --bin DIR --root NEW_DIR [--plant plus-one|double-pay|raid]

A fresh private one-sponsor Store (newparticipant-acceptance.sh) enrolling two more
subjects (Bob 40 the claimant, Carol 41 a rival). Never a live or common world. One asset,
gold, is a realm well the sponsor (Alice, the poster and the board's operator) founds. The contract
is world/bounty/BountyEscrow.obend, published as a seat contract artifact; every scenario is one
instance of it. Every kernel turn is `mini seat --action submit`; every refusal is the Host's, by
name; the public seat view (op 219) is read after steps, with the Book's total of gold (which
never changes). world/bounty/README.md says what is native and what is not.

  A approve   post (the poster's balance falls by exactly the reward), claim, the claimant's seat
              and work seat, `advance` moves the reward from the escrow seat into the claim seat
              (an early exit of it is refused: exitNotAuthorized), the poster's approve seat,
              `advance` pays the claimant whole; every seat closes.
  R reject    the poster's reject seat returns the reward whole to the escrow (the bounty reopens);
              before the deadline the escrow cannot be exited (exitNotAuthorized); at the deadline
              a third party's exit refunds the poster.
  S silence   no decision: the claim seat's own deadline exit, by a third party, pays the claimant.
  C cancel    the poster's cancel seat, `advance` refunds the poster.
  F first     two claimants; the claim seat with the least `opened` is funded, the other gets nothing.
  P plants    the contract with a planted reward+1 move, a planted double payment, and a planted raid
              (the reward moves with no receipt): the Host refuses the invoke by the kernel's own name
              (the raid by the escrow's own offer-safety law: offerUnsafe); roots and balances unchanged.

ROOT/transcript holds every command's exact output; ROOT/results.json lists every row with its
expectation and verdict and ROOT/receipts.json every turn's confirmation; the script exits 1 on any
mismatch. --plant mutates the PUBLISHED contract for every scenario (the mutation is asserted to
have changed the source), so the named rows that depend on the mutated rule go red.
"""
import argparse, json, os, pathlib, secrets, shutil, subprocess, sys, time

os.umask(0o077)
HERE = pathlib.Path(__file__).resolve().parent
REPO = HERE.parent.parent
ap = argparse.ArgumentParser()
ap.add_argument('mode', nargs='?', default='all', choices=['all'])  # journey-rows passes `all`, as to every driver
ap.add_argument('--bin', required=True)
ap.add_argument('--root', required=True)
ap.add_argument('--plant', default='', choices=['', 'plus-one', 'double-pay', 'raid'])
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
receipts = {}


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

BOB, CAROL = '40', '41'
enrollment = []
for name, subject, key_id, caps in [('bob', BOB, '4000', ('4002', '4003', '4004')),
                                    ('carol', CAROL, '4010', ('4012', '4013', '4014'))]:
    sh(f'keygen-{subject}', mini, 'keygen', '--secret', root / f'subject{subject}.key', '--public',
       root / f'subject{subject}.pub')
    enrollment.append({'key': {'keyId': key_id, 'keyEpoch': '2', 'algorithm': '1', 'subject': subject,
                               'publicKey': (root / f'subject{subject}.pub').read_bytes().hex(), 'activeFrom': '0',
                               'activeUntil': '1000000', 'nextKeyDigest': None},
                       'accountId': subject, 'spendCapabilityId': caps[0], 'controlCapabilityId': caps[1],
                       'factoryObserveCapabilityId': caps[2], 'initialBalance': '100000',
                       'accountPredicate': {'type': 'all', 'predicates': []}})
(root / 'enrollment-40.json').write_text(json.dumps(enrollment))
W = root / 'w'
sock = W / 'public' / 'mini.sock'
sh('genesis', 'sh', HERE / 'newparticipant-acceptance.sh', host, mini, store, verifier, W, sock,
   env={'OBJECTIVE_INVOCATION_POLICY': (root / 'policy.hex').read_text().strip(),
        'EXTRA_GENESIS_ENROLLMENTS': str(root / 'enrollment-40.json'),
        'NEWPARTICIPANT_SPONSOR_BALANCE': '1000000000'})
config = W / 'deployment' / 'pinned-config.json'
alice_ws = W / 'sponsor'
participants = {}
for subject in [BOB, CAROL]:
    ws = root / f'subject{subject}'
    ws.mkdir(mode=0o700)
    (ws / 'workspace.json').write_text(json.dumps({
        'type': 'minidregg-participant-workspace-v1', 'host': str(host), 'socket': str(sock), 'config': str(config),
        'key': str(root / f'subject{subject}.key'), 'subject': subject}))
    participants[subject] = ws
bob_ws, carol_ws = participants[BOB], participants[CAROL]
params = json.loads((W / 'genesis-params.json').read_text())
ALICE = str(params['sponsor']['subject'])
ALICE_ACCOUNT = str(params['sponsor']['accountId'])
ALICE_SPEND = str(params['sponsor']['spendCapabilityId'])
BOB_ACCOUNT = BOB
BOB_SPEND = '4002'
CAROL_ACCOUNT = CAROL
CAROL_SPEND = '4012'
COLLECTOR = str(params['collector'])
permit = root / 'permit-all.json'
permit.write_text('{"type":"all","predicates":[]}\n')

# Two assets: realm wells the sponsor founds and mints from (`mini well`).
sh('create-realm', mini, 'workspace', '--action', 'create', '--dir', alice_ws, '--name', 'bazaar',
   '--storage', 'declared', '--predicate', permit)
for name in ['gold', 'receipt']:
    sh(f'well-new-{name}', mini, 'well', '--action', 'new', '--dir', alice_ws, '--name', name, '--in', 'bazaar',
       '--law', permit)
X = json.loads((alice_ws / 'refs' / 'gold.json').read_text())['target']
D = json.loads((alice_ws / 'refs' / 'receipt.json').read_text())['target']


def mint(asset_name, account, amount):
    sh(f'mint-{asset_name}-{account}-{amount}', mini, 'well', '--action', 'mint', '--dir', alice_ws,
       '--well', asset_name, '--account', account, '--amount', str(amount))


objects = {}
SCENARIOS = ['approve', 'reject', 'silence', 'cancel', 'first', 'short', 'plus1', 'double', 'raid']
for name in SCENARIOS:
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
    receipts[tag] = value
    print(f'{tag:44} {expect:9} {kind} {reason} {text[-140:]}', flush=True)
    return value


def check(tag, condition, observed):
    results.append({'step': tag, 'expect': 'check', 'ok': bool(condition), 'observed': observed})
    print(f'{tag:44} check     {"ok" if condition else "MISMATCH"} {json.dumps(observed)[:200]}', flush=True)


def turn(tag, workspace, body, expect, detail=None, prepare=False, object_cap=None, account_cap=None):
    out = attempts / tag
    command = root / f'{tag}.command.json'
    file = {'turn': body}
    if body.get('kind') == 'offer' and body['proposal'].get('donate'):
        file['confirmDonation'] = True
    if object_cap is not None:
        file['objectCapability'] = object_cap
    if account_cap is not None:
        file['accountCapability'] = account_cap
    command.write_text(json.dumps(file))
    args = ['seat', '--action', 'submit', '--workspace', workspace, '--command', command, '--out', out]
    if prepare:
        args += ['--prepare-only', 'true']
    value = last_json(sh(tag, mini, *args, ok=(0, 1, 2)))
    return judge(tag, value, expect, detail)


def balances(v):
    return {(b['account'], b['asset']): int(b['balance']) for b in (v.get('balances') or [])}


def cell(v, cell_id):
    return next((c for c in v.get('cells', []) if c.get('cell') == str(cell_id)), {})


def world(tag, seats=(), instances=(), invitations=()):
    v = view(tag, {'instances': list(instances), 'invitations': list(invitations), 'seats': list(seats),
                   'accounts': [ALICE_ACCOUNT, BOB_ACCOUNT, CAROL_ACCOUNT, COLLECTOR, X, D] + list(seats),
                   'assets': [X, D] + ([CREDIT] if CREDIT else [])})
    b = balances(v)
    totals.append({'after': tag, 'height': v.get('height'),
                   'totals': {t['asset']: t['total'] for t in (v.get('totals') or [])},
                   'minted': {X: -b.get((X, X), 0), D: -b.get((D, D), 0)}})
    return v


def roots(v):
    return {c['cell']: c['root'] for c in v.get('cells', [])}


def activity_cap(ticks):  # (the Order helpers recurse once per height: the envelope is generous)
    """A declared envelope (Capacity): `ticks` source ticks, the kernel's fixed heap, stack,
    type fuel and Plan budget, priced at 0 (as the activity driver's `cap`)."""
    c = {k: '0' for k in MAXIMUM}
    for k in ['heap', 'stack', 'typeFuel', 'outputNodes', 'outputBytes', 'extractTicks']:
        c[k] = str(MAXIMUM[k])
    c['sourceTicks'] = str(ticks)
    return c


def invoke(tag, workspace, inst, inp, expect, detail=None, object_cap=None, account=ALICE_ACCOUNT,
           account_cap=ALICE_SPEND, ticks=12000, prepare=False):
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
          package=None, deadline=None, holder=None):
    proposal = {'give': [{'asset': a_, 'amount': str(n)} for a_, n in give],
                'want': [{'asset': a_, 'amount': str(n)} for a_, n in want]}
    if deadline is not None:
        proposal['afterDeadline'] = str(deadline)
    if not want:
        proposal['donate'] = True  # a seat that wants nothing carries the donation marker (Proposal.donate)
    body = {'kind': 'offer', 'invitation': invitation,
            'expect': {'instance': objects[inst]['object'], 'package': package or PIN, 'role': role},
            'funding': funding, 'payee': funding, 'proposal': proposal, 'holder': holder}
    value = turn(tag, workspace, body, expect, detail, account_cap=account_cap)
    return value.get('seatAccount')


def exit_(tag, workspace, seat, expect, detail=None, prepare=False):
    return turn(tag, workspace, {'kind': 'exit', 'seat': seat}, expect, detail, prepare)


# --- the contract, as published ----------------------------------------------------------------
def contract_source(plant):
    text = (REPO / 'world/bounty/BountyEscrow.obend').read_text()
    mutated = text
    if plant == 'plus-one':
        old = 'amount: held(asset, source.allocation)}'
        assert mutated.count(old) == 1
        mutated = mutated.replace(old, 'amount: held(asset, source.allocation) + 1n}')
    elif plant == 'double-pay':
        old = 'exchange(wholeMove(e, c, headAsset(e.give)), wholeMove(w, e, headAsset(e.want)))'
        assert mutated.count(old) == 1
        mutated = mutated.replace(old, 'exchange(wholeMove(e, c, headAsset(e.give)), wholeMove(e, c, headAsset(e.give)))')
    elif plant == 'raid':
        old = 'exchange(wholeMove(e, c, headAsset(e.give)), wholeMove(w, e, headAsset(e.want)))'
        assert mutated.count(old) == 1
        mutated = mutated.replace(old, 'reallocation(Moves.cons({head: wholeMove(e, c, headAsset(e.give)), tail: Moves.nil()}))')
    if plant:
        assert mutated != text, 'the planted mutation changed nothing'
    return mutated


PUB_COUNT = [0]


def publish_contract(label, plant):
    PUB_COUNT[0] += 1
    pub = root / f'publication-{label}'
    (pub / 'src').mkdir(parents=True)
    shutil.copy(REPO / 'world/workshop/NatOrder.obend', pub / 'src' / 'NatOrder.obend')
    (pub / 'src' / 'BountyEscrow.obend').write_text(contract_source(plant))
    spec = {'schema': 'dregg.objective-bend.package-input.v1', 'edition': 'objective-bend-1',
            'modules': [{'name': 'NatOrder', 'sourcePath': str(pub / 'src' / 'NatOrder.obend'), 'imports': []},
                        {'name': 'BountyEscrow', 'sourcePath': str(pub / 'src' / 'BountyEscrow.obend'),
                         'imports': [{'alias': 'Order', 'path': './NatOrder.obend', 'module': '0'}]}],
            'entryModule': '1', 'entryDefinition': 'bounty'}
    (pub / 'spec.json').write_text(json.dumps(spec))
    published = last_json(sh(f'publication-{label}', host, config, 'objective-publication', pub / 'spec.json', 'seat',
                             pub / 'out'))
    pin = published['artifactId']
    turn(f'{label}-publish', alice_ws, {'kind': 'publish', 'artifact': (pub / 'out' / 'artifact.bin').read_bytes().hex(),
         'package': (pub / 'out' / 'package.bin').read_bytes().hex(), 'payer': ALICE_ACCOUNT}, 'installed',
         account_cap=ALICE_SPEND)
    return pin


def post_input(review):
    return variant('post', record(holder=nat(int(ALICE)), review=nat(review)))


def claim_input(who):
    return variant('claim', record(holder=nat(int(who))))


def advance_input():
    return variant('advance', record())


def pad_input():
    return variant('pad', record(holder=nat(int(ALICE))))


def height():
    return int(view('height', {})['height'])


REWARD = 50


class Board:
    """One bounty: an instance of the published contract on its own object."""

    def __init__(self, name, pin, review):
        self.name, self.pin, self.review, self.advances = name, pin, review, 0
        turn(f'{name}-create', alice_ws, {'kind': 'create', 'instance': objects[name]['object'], 'pin': pin,
             'clause': {'type': 'all', 'predicates': []}}, 'installed', object_cap=objects[name]['capability'])
        ids = invoke(f'{name}-post', alice_ws, name, post_input(review), 'installed').get('mintIds', [])
        check(f'{name}-post-mints-four-invitations', len(ids) >= 4, len(ids))
        self.inv = dict(zip(['escrow', 'approve', 'reject', 'cancel'], ids))
        self.seats = []

    def world(self, tag):
        return world(f'{self.name}-{tag}', seats=self.seats, instances=[objects[self.name]['object']])

    def fund(self, deadline_after):
        before = balances(world(f'{self.name}-before-escrow'))
        self.due_escrow = height() + deadline_after
        self.escrow = offer(f'{self.name}-escrow', alice_ws, self.name, self.inv['escrow'], 'escrow', [(X, REWARD)], [(D, 1)],
                            'installed', funding=ALICE_ACCOUNT, account_cap=ALICE_SPEND, package=self.pin,
                            deadline=self.due_escrow)
        self.seats.append(self.escrow)
        b = balances(self.world('escrowed'))
        check(f'{self.name}-escrow-holds-reward', b.get((self.escrow, X)) == REWARD, b.get((self.escrow, X)))
        check(f'{self.name}-poster-down-by-exactly-the-reward',
              before[(ALICE_ACCOUNT, X)] - b[(ALICE_ACCOUNT, X)] == REWARD,
              [before[(ALICE_ACCOUNT, X)], b[(ALICE_ACCOUNT, X)]])
        return self.escrow

    def claim(self, who, workspace, account, spend, due_after, offer_work=True, refuse_first=False):
        ids = invoke(f'{self.name}-claim-{who}', alice_ws, self.name, claim_input(who), 'installed').get('mintIds', [])
        check(f'{self.name}-claim-mints-claim-and-work-{who}', len(ids) >= 2, len(ids))
        due = height() + due_after
        claim_seat = offer(f'{self.name}-claim-seat-{who}', workspace, self.name, ids[0], 'claim', [], [(X, REWARD)],
                           'installed', funding=account, account_cap=spend, package=self.pin, deadline=due)
        if refuse_first:  # a work seat must give the receipt, which the claimant does not hold yet
            offer(f'{self.name}-work-without-receipt-refused', workspace, self.name, ids[1], 'work', [(D, 1)], [],
                  'refused', None, funding=account, account_cap=spend, package=self.pin)
        mint('receipt', account, 1)  # the issuer's attestation that the work arrived (a realm-well mint)
        work_seat = offer(f'{self.name}-work-seat-{who}', workspace, self.name, ids[1], 'work', [(D, 1)], [], 'installed',
                          funding=account, account_cap=spend, package=self.pin) if offer_work else None
        self.seats += [s for s in (claim_seat, work_seat) if s]
        return claim_seat, work_seat, due

    def advance(self, tag=None, expect='installed', detail=None):
        self.advances += 1
        return invoke(f'{self.name}-advance-{tag or self.advances}', alice_ws, self.name, advance_input(), expect, detail,
                      ticks=150000)

    def decide(self, which):
        seat = offer(f'{self.name}-{which}-seat', alice_ws, self.name, self.inv[which], which, [], [], 'installed',
                     funding=ALICE_ACCOUNT, account_cap=ALICE_SPEND, package=self.pin)
        self.seats.append(seat)
        return seat

    def pad_to(self, target):
        n = 0
        while height() < target and n < 80:
            n += 1
            invoke(f'{self.name}-pad-{n}', alice_ws, self.name, pad_input(), 'installed')


def open_(v, seat):
    # a closed seat leaves the world and its cell is retired (seat-retention): absent == closed
    c = cell(v, seat)
    return c.get('seat', {}).get('open', False) if c else False


# --- scenarios -------------------------------------------------------------------------------------
PIN = publish_contract('main', a.plant)
mint('gold', ALICE_ACCOUNT, 400)
start = world('genesis')

# A: approve pays the claimant whole
A = Board('approve', PIN, review=4)
A.fund(deadline_after=80)
a_claim, a_work, a_due = A.claim(BOB, bob_ws, BOB_ACCOUNT, BOB_SPEND, due_after=16, refuse_first=True)
b = balances(A.world('claimed'))
check('A-claim-moves-nothing', b.get((A.escrow, X)) == REWARD and b.get((a_claim, X)) == 0,
      {'escrow': b.get((A.escrow, X)), 'claim': b.get((a_claim, X))})
A.advance('submit')
b = balances(A.world('submitted'))
check('A-submission-moves-reward-into-claim-seat', b.get((A.escrow, X)) == 0 and b.get((a_claim, X)) == REWARD,
      {'escrow': b.get((A.escrow, X)), 'claim': b.get((a_claim, X))})
check('A-escrow-holds-the-receipt-for-the-reward', b.get((A.escrow, D)) == 1 and b.get((a_work, D), 0) == 0,
      {'escrowReceipt': b.get((A.escrow, D)), 'workReceipt': b.get((a_work, D), 0)})
exit_('A-claimant-early-exit-refused', bob_ws, a_claim, 'refused', 'exitNotAuthorized')
exit_('A-stranger-early-exit-refused', carol_ws, a_claim, 'refused', 'exitNotAuthorized')
A.decide('approve')
pre = balances(A.world('before-approve'))
A.advance('pay')
b = balances(A.world('paid'))
v = A.world('paid-view')
check('A-approve-pays-claimant-whole', b[(BOB_ACCOUNT, X)] - pre[(BOB_ACCOUNT, X)] == REWARD,
      [pre[(BOB_ACCOUNT, X)], b[(BOB_ACCOUNT, X)]])
check('A-claim-seat-closed-and-empty', open_(v, a_claim) is False and b.get((a_claim, X), 0) == 0, open_(v, a_claim))
check('A-escrow-closed-and-empty', open_(v, A.escrow) is False and b.get((A.escrow, X), 0) == 0, open_(v, A.escrow))
check('A-poster-holds-the-receipt', b[(ALICE_ACCOUNT, D)] - pre[(ALICE_ACCOUNT, D)] == 1,
      [pre[(ALICE_ACCOUNT, D)], b[(ALICE_ACCOUNT, D)]])
exit_('A-paid-claim-seat-cannot-pay-twice', carol_ws, a_claim, 'refused', 'seatMissing')

# R: reject reopens; expiry returns the reward to the poster
R = Board('reject', PIN, review=4)
r_start = balances(R.world('start'))
R.fund(deadline_after=40)
r_claim, r_work, r_due = R.claim(BOB, bob_ws, BOB_ACCOUNT, BOB_SPEND, due_after=14)
R.advance('submit')
b = balances(R.world('submitted'))
check('R-submitted', b.get((r_claim, X)) == REWARD, b.get((r_claim, X)))
R.decide('reject')
R.advance('reopen')
b = balances(R.world('reopened'))
v = R.world('reopened-view')
check('R-reject-returns-reward-to-escrow', b.get((R.escrow, X)) == REWARD and b.get((r_claim, X), 0) == 0
      and b.get((R.escrow, D), 0) == 0,
      {'escrow': b.get((R.escrow, X)), 'claim': b.get((r_claim, X), 0), 'escrowReceipt': b.get((R.escrow, D), 0)})
check('R-rejected-claimant-gets-the-receipt-back', b[(BOB_ACCOUNT, D)] - r_start[(BOB_ACCOUNT, D)] == 1,
      [r_start[(BOB_ACCOUNT, D)], b[(BOB_ACCOUNT, D)]])
check('R-claim-seat-closed', open_(v, r_claim) is False, open_(v, r_claim))
check('R-rejected-claimant-keeps-nothing', b[(BOB_ACCOUNT, X)] == r_start[(BOB_ACCOUNT, X)],
      [r_start[(BOB_ACCOUNT, X)], b[(BOB_ACCOUNT, X)]])
exit_('R-escrow-early-exit-refused', carol_ws, R.escrow, 'refused', 'exitNotAuthorized')
exit_('R-poster-cannot-pull-escrow-early', alice_ws, R.escrow, 'refused', 'exitNotAuthorized')
R.pad_to(R.due_escrow)
exit_('R-expiry-refunds-poster', carol_ws, R.escrow, 'installed')
b = balances(R.world('expired'))
check('R-poster-whole-again', b[(ALICE_ACCOUNT, X)] == r_start[(ALICE_ACCOUNT, X)],
      [r_start[(ALICE_ACCOUNT, X)], b[(ALICE_ACCOUNT, X)]])

# S: silence pays the claimant (the claim seat's own deadline exit)
S = Board('silence', PIN, review=3)
S.fund(deadline_after=80)
s_claim, s_work, s_due = S.claim(BOB, bob_ws, BOB_ACCOUNT, BOB_SPEND, due_after=14)
S.advance('submit')
b = balances(S.world('submitted'))
check('S-submitted', b.get((s_claim, X)) == REWARD, b.get((s_claim, X)))
s_pre = balances(S.world('silent'))
invoke('silence-pad-early', alice_ws, 'silence', pad_input(), 'installed')
check('S-undecided-reward-stays-in-claim-seat', balances(S.world('still-silent')).get((s_claim, X)) == REWARD, None)
exit_('S-exit-before-due-refused', carol_ws, s_claim, 'refused', 'exitNotAuthorized')
S.pad_to(s_due)
exit_('S-silence-pays-claimant', carol_ws, s_claim, 'installed')
b = balances(S.world('silence-paid'))
check('S-claimant-paid-whole', b[(BOB_ACCOUNT, X)] - s_pre[(BOB_ACCOUNT, X)] == REWARD,
      [s_pre[(BOB_ACCOUNT, X)], b[(BOB_ACCOUNT, X)]])

# C: cancel refunds the poster
C = Board('cancel', PIN, review=3)
c_pre = balances(C.world('start'))
C.fund(deadline_after=80)
C.decide('cancel')
C.advance('refund')
b = balances(C.world('cancelled'))
v = C.world('cancelled-view')
check('C-cancel-refunds-poster-whole', b[(ALICE_ACCOUNT, X)] == c_pre[(ALICE_ACCOUNT, X)],
      [c_pre[(ALICE_ACCOUNT, X)], b[(ALICE_ACCOUNT, X)]])
check('C-escrow-closed', open_(v, C.escrow) is False, open_(v, C.escrow))

# F: first claimer = least opened
F = Board('first', PIN, review=4)
F.fund(deadline_after=80)
f_ids_bob = invoke('first-claim-40', alice_ws, 'first', claim_input(BOB), 'installed').get('mintIds', [])
f_ids_carol = invoke('first-claim-41', alice_ws, 'first', claim_input(CAROL), 'installed').get('mintIds', [])
check('F-two-claim-invitations', len(f_ids_bob) >= 2 and len(f_ids_carol) >= 2, [len(f_ids_bob), len(f_ids_carol)])
f_due = height() + 20
carol_claim = offer('first-claim-seat-41', carol_ws, 'first', f_ids_carol[0], 'claim', [], [(X, REWARD)], 'installed',
                    funding=CAROL_ACCOUNT, account_cap=CAROL_SPEND, package=PIN, deadline=f_due)
bob_claim = offer('first-claim-seat-40', bob_ws, 'first', f_ids_bob[0], 'claim', [], [(X, REWARD)], 'installed',
                  funding=BOB_ACCOUNT, account_cap=BOB_SPEND, package=PIN, deadline=f_due)
mint('receipt', CAROL_ACCOUNT, 1)
mint('receipt', BOB_ACCOUNT, 1)
carol_work = offer('first-work-seat-41', carol_ws, 'first', f_ids_carol[1], 'work', [(D, 1)], [], 'installed',
                   funding=CAROL_ACCOUNT, account_cap=CAROL_SPEND, package=PIN)
bob_work = offer('first-work-seat-40', bob_ws, 'first', f_ids_bob[1], 'work', [(D, 1)], [], 'installed',
                 funding=BOB_ACCOUNT, account_cap=BOB_SPEND, package=PIN)
F.seats += [carol_claim, bob_claim, carol_work, bob_work]
F.advance('submit')
b = balances(F.world('submitted'))
check('F-least-opened-claim-seat-funded', b.get((carol_claim, X)) == REWARD and b.get((bob_claim, X), 0) == 0,
      {'carol': b.get((carol_claim, X)), 'bob': b.get((bob_claim, X), 0)})
F.decide('approve')
f_pre = balances(F.world('before-approve'))
F.advance('pay')
b = balances(F.world('paid'))
check('F-first-claimer-paid-whole', b[(CAROL_ACCOUNT, X)] - f_pre[(CAROL_ACCOUNT, X)] == REWARD
      and b[(BOB_ACCOUNT, X)] == f_pre[(BOB_ACCOUNT, X)],
      {'carol': b[(CAROL_ACCOUNT, X)] - f_pre[(CAROL_ACCOUNT, X)], 'bob': b[(BOB_ACCOUNT, X)] - f_pre[(BOB_ACCOUNT, X)]})

# T: a claim seat that could exit before the review window has run never receives the reward
SH = Board('short', PIN, review=6)
SH.fund(deadline_after=80)
SH.claim(BOB, bob_ws, BOB_ACCOUNT, BOB_SPEND, due_after=2)
SH.advance('too-early-to-fund-claim-seat')  # a no-op plan is admitted; the check below is the assertion
check('SH-reward-stays-in-escrow', balances(SH.world('short-claim')).get((SH.escrow, X)) == REWARD, None)

# P: planted contracts the kernel refuses
if not a.plant:
    for label, plant, name in [('plus1', 'plus-one', 'plus1'), ('double', 'double-pay', 'double'), ('raid', 'raid', 'raid')]:
        pin = publish_contract(label, plant)
        P = Board(name, pin, review=4)
        P.fund(deadline_after=80)
        P.claim(BOB, bob_ws, BOB_ACCOUNT, BOB_SPEND, due_after=14)
        before = roots(P.world('before-planted'))
        P.advance('planted-pay', 'refused', 'offerUnsafe' if plant == 'raid' else 'unfunded')
        v = P.world('after-planted')
        check(f'P-{label}-roots-unchanged', roots(v) == before,
              {'changed': [k for k in roots(v) if roots(v)[k] != before.get(k)]})
        check(f'P-{label}-escrow-still-whole', balances(v).get((P.escrow, X)) == REWARD, balances(v).get((P.escrow, X)))

# --- conservation ---------------------------------------------------------------------------------
xs = {t['totals'].get(X) for t in totals}
check('X-total-constant', len(xs) == 1, sorted(xs, key=str))
mx = {t['minted'][X] for t in totals}
check('X-minted-constant-across-turns', len(mx) == 1 and mx == {400}, sorted(mx))
ds = {t['totals'].get(D) for t in totals}
check('receipt-total-changes-only-by-issuer-mints', all(isinstance(t, (int, str, type(None))) for t in ds), sorted(ds, key=str))

(root / 'results.json').write_text(json.dumps({
    'rows': results, 'totals': totals, 'plant': a.plant, 'assets': {'gold': X}, 'objects': objects}, indent=1))
(root / 'receipts.json').write_text(json.dumps(receipts, indent=1))
bad = [r for r in results if not r['ok']]
print(f'{len(results) - len(bad)}/{len(results)} rows ok; results in {root / "results.json"}')
for r in bad:
    print('RED', r['step'], r.get('detail') or r.get('observed'))
sys.exit(1 if bad else 0)
