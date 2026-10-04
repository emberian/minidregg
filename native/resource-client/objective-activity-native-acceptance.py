#!/usr/bin/env python3
"""The kernel activity end to end on a scratch NATIVE world, every turn a signed command.

  objective-activity-native-acceptance.py --bin DIR --root NEW_DIR

A fresh private one-sponsor Store (newparticipant-acceptance.sh) whose genesis
pins this checkout's Objective invocation policy (its maximum envelope, tariff and
source bound are the activity kernel's configuration) and enrolls a second subject
(40, its own key and Book account). Never a live or common world. Every activity
turn is `mini activity --action submit` (Host op 7 author, op 210 plan, the
workspace key signs the header, op 211 assemble, op 212 submit), every refusal is
the Host's, by name, and the public view (op 214) is read after each step: the
record, its slot, the object's record and declared state, the purse and the
payers' Book balances, and the Book's total of the credit asset (which never
changes).

  publication   world/activity/Tally.obend captured and lowered by the Host's own
                front end into an activity artifact (`objective-publication SPEC
                activity DIR`) and published; a second package (TallyFromZero,
                importing Tally) is published too, for the pin refusal.
  objects       a cell is an object only with a record (create): subject 40
                cannot create one on the sponsor's resource (notObjectHolder),
                the sponsor cannot name 40's account as payer (notAccountOwner),
                nor pin an unpublished package (pinUnpublished); a birth on a
                resource without a record is refused (notAnObject); the sponsor
                creates each object, pinning Tally; a second creation of the same
                object is a transaction conflict; a birth naming the other
                published package is refused (pinMismatch).
  ownership     subject 40 cannot birth on the sponsor's object, nor write its state
                (notObjectHolder); an underfunded birth is refused.
  tally         born on the sponsor's object: the stranger cannot decide its slot
                (notDecider), an ill-typed reply is refused, the decider replies,
                two deliveries are prepared on one snapshot: the first commits, its
                exact retry replays, the second conflicts, a third naming the spent
                await conflicts, one naming the new await finds nothing decided.
  view          resume with view: the decider replies 7 and a delivery is prepared;
                the owner then writes the object's state (99); the prepared
                delivery is refused (the state moved under it), and a fresh
                delivery resumes the tally with the reply AND the owner's state,
                and the tally's delta lands on it (99 + 7 = 106, never 12).
  two tallies   two activities on one object: the second birth cannot `set`
                the existing state (blindWrite) and joins with `keep`; both
                replies land whatever the order (3 + 4 = 7).
  funding       a tally whose deposit is exactly one fee pair: its second yield
                cannot reserve the pair (awaitsFunding: parked); a top-up; the
                delivery commits.
  timeout       a tally whose deadline passes: the decider is too late
                (pastDeadline), any delivery expires the slot and resumes it with
                `timedOut`; it ends, its record and its slot are RECLAIMED (empty
                tombstones) and its purse returns to the payer; a further delivery
                is refused (recordMissing).
  exhaustion    a tally whose declared resume envelope is too small: a delivery
                is refused `exhausted` (nothing commits); an `exhaust` turn
                commits the attempt and charges the purse the declared price of
                the resume envelope, leaving the activity at its yield; the same
                envelope again is refused before it runs (alreadyExhausted), for
                exhaust and deliver alike; a larger declared envelope exhausts
                again (charged to its submitter only); a sufficient one delivers.
  abandon       a tally nobody decides: abandoning it before deadline + grace is
                refused (notYetAbandonable); after, anyone abandons it: record and
                slot reclaimed, the timeout fee to the collector, the rest of the
                purse to the payer; the late decider finds no slot, a late
                delivery no record, and a retry of the abandonment replays.
  fault         scenario E: a resident (tests/objective-activity/FaultAfterReply.obend)
                that faults after its first reply (its second await asks for a
                patience past the deployment's bound): the delivery COMMITS (never a
                refusal that every later delivery would meet again): the activity
                ends faulted, its record and slot are reclaimed, its purse returns
                to the payer minus the used resume fee, the declared state keeps
                its last write, and later deliveries are refused by name
                (recordMissing).
  growth        twelve resumes of one tally: the stored checkpoint (the Plan
                extraction's state, settled and collected) grows at most 200 B
                per resume after the first (measured: about 0).
  reopen        the world's own `mini serve` restarts on the same Store: replay
                re-admits every activity record; a lookup returns the original
                receipt; the view is byte-identical.

ROOT/transcript holds every command's exact output; ROOT/results.json lists every
row with its expectation and verdict; the script exits 1 on any mismatch.
"""
import argparse, json, os, pathlib, secrets, subprocess, sys, time

os.umask(0o077)
HERE = pathlib.Path(__file__).resolve().parent
REPO = HERE.parent.parent
ap = argparse.ArgumentParser()
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


def nat(n):
    return {'tag': 'natural', 'value': str(n)}


def record(**fields):
    return {'tag': 'record', 'fields': [{'name': k, 'value': v} for k, v in fields.items()]}


def unhex(text):
    try:
        return bytes.fromhex(text).decode(errors='replace')
    except (ValueError, TypeError):
        return str(text)


# --- the world -----------------------------------------------------------------
constants = json.loads(sh('constants', host, '/dev/null', 'objective-constants').stdout)
MAXIMUM = {'typeFuel': 16384, 'sourceTicks': 200000, 'heap': 200000, 'stack': 200000, 'outputNodes': 20000,
           'outputBytes': 200000, 'inputBytes': 200000, 'scalarBits': 512, 'memoryTouches': 2000000,
           'proofWork': 900000, 'feeDebit': 1000000, 'turnBytes': 4000000, 'witnessBytes': 4000000,
           'storageBytes': 4000000, 'sideEffectCount': 16, 'networkBytes': 0, 'leaseByteBlocks': 0,
           'incidences': 16}
tariff = {'version': '1', 'base': '1', 'typeFuel': '0', 'sourceTicks': '1', 'heap': '0', 'stack': '0',
          'outputNodes': '0', 'outputBytes': '0', 'inputBytes': '0'}
policy = {'schema': 'dregg.objective-bend.policy.v1', 'sourceBytes': '4194304',
          'maximum': {k: str(v) for k, v in MAXIMUM.items()}, 'outputs': [constants['genericCodec']],
          'clearAudience': '01ff', 'frontEnd': constants['frontEnd'], 'tariff': tariff}
(root / 'policy.json').write_text(json.dumps(policy, indent=1))
sh('policy', host, '/dev/null', 'author', 'objective-policy', root / 'policy.json', root / 'policy.hex')

sh('keygen-40', mini, 'keygen', '--secret', root / 'subject40.key', '--public', root / 'subject40.pub')
public40 = (root / 'subject40.pub').read_bytes().hex()
SECOND = '40'
enrollment = [{'key': {'keyId': '4000', 'keyEpoch': '2', 'algorithm': '1', 'subject': SECOND,
                       'publicKey': public40, 'activeFrom': '0', 'activeUntil': '1000000', 'nextKeyDigest': None},
               'accountId': SECOND, 'spendCapabilityId': '4002', 'controlCapabilityId': '4003',
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
sponsor = W / 'sponsor'
second = root / 'subject40'
second.mkdir(mode=0o700)
(second / 'workspace.json').write_text(json.dumps({
    'type': 'minidregg-participant-workspace-v1', 'host': str(host), 'socket': str(sock), 'config': str(config),
    'key': str(root / 'subject40.key'), 'subject': SECOND}))
params = json.loads((W / 'genesis-params.json').read_text())
SPONSOR = str(params['sponsor']['subject'])
SPONSOR_ACCOUNT = str(params['sponsor']['accountId'])
SPONSOR_SPEND = str(params['sponsor']['spendCapabilityId'])
COLLECTOR = str(params['collector'])
(root / 'permit-all.json').write_text('{"type":"all","predicates":[]}\n')
objects = {}
for name in ['tally-one', 'tally-two', 'tally-three', 'tally-four', 'tally-five', 'tally-exhaust',
             'tally-abandon', 'tally-fault', 'bare']:
    sh(f'create-{name}', mini, 'workspace', '--action', 'create', '--dir', sponsor, '--name', name,
       '--storage', 'content', '--predicate', root / 'permit-all.json')
    ref = json.loads((sponsor / 'refs' / f'{name}.json').read_text())
    objects[name] = {'object': ref['target'], 'capability': ref['operationCapability']}
(root / 'objects.json').write_text(json.dumps(objects, indent=1))

# --- turns and views -----------------------------------------------------------
attempts = root / 'attempts'
attempts.mkdir()


def view(label, request):
    r = sh(f'view-{label}', mini, 'activity', '--action', 'view', '--workspace', sponsor,
           '--request', json.dumps(request))
    return last_json(r)


totals = []


def watched(label):
    v = view(label, {'accounts': [SPONSOR_ACCOUNT, SECOND, COLLECTOR]})
    totals.append({'after': label, 'height': v.get('height'), 'total': v.get('total')})
    return v


def turn(label, workspace, body, expect, detail=None, prepare=False):
    """One signed command. `expect`: installed | replayed | refused | conflict | prepared."""
    out = attempts / label
    command = root / f'{label}.turn.json'
    command.write_text(json.dumps(body))
    args = ['activity', '--action', 'submit', '--workspace', workspace, '--command', command, '--out', out]
    if prepare:
        args += ['--prepare-only', 'true']
    r = sh(label, mini, *args, ok=(0, 1, 2))
    value = last_json(r)
    return judge(label, value, expect, detail)


def resubmit(label, ingress, expect, detail=None):
    r = sh(label, mini, 'activity', '--action', 'resubmit', '--workspace', sponsor, '--ingress', ingress,
           ok=(0, 1, 2))
    return judge(label, last_json(r), expect, detail)


def judge(label, value, expect, detail):
    kind = value.get('type')
    reason = value.get('reason', '')
    text = unhex(value.get('detail', '')) if 'detail' in value else value.get('error', '')
    if expect == 'installed':
        ok = kind == 'confirmed' and value.get('confirmation') == 'installed'
    elif expect == 'replayed':
        ok = kind == 'confirmed' and value.get('confirmation') == 'replayed'
    elif expect == 'prepared':
        ok = kind == 'prepared'
    elif expect == 'conflict':
        ok = kind == 'refused' and reason == 'conflict'
    else:
        ok = kind == 'refused' or 'refused' in str(value.get('error', ''))
    if ok and detail is not None:
        ok = detail in text
    results.append({'step': label, 'expect': expect, 'detailExpected': detail, 'type': kind,
                    'reason': reason, 'detail': text[-300:], 'ok': ok})
    print(f'{label:44} {expect:9} {kind} {reason} {text[-120:]}', flush=True)
    return value


def check(label, condition, observed):
    results.append({'step': label, 'expect': 'check', 'ok': bool(condition), 'observed': observed})
    print(f'{label:44} check     {"ok" if condition else "MISMATCH"} {json.dumps(observed)[:160]}', flush=True)


def cell_of(v, cell):
    return next((c for c in v.get('cells', []) if c.get('cell') == cell), {})


def balance(v, account):
    return int(next(b['balance'] for b in v['balances'] if b['account'] == account))


# --- publication ---------------------------------------------------------------
def publication(label, modules, entry_module, entry):
    pub = root / label
    pub.mkdir()
    spec = {'schema': 'dregg.objective-bend.package-input.v1', 'edition': 'objective-bend-1',
            'modules': modules, 'entryModule': entry_module, 'entryDefinition': entry}
    (pub / 'spec.json').write_text(json.dumps(spec))
    out = last_json(sh(label, host, config, 'objective-publication', pub / 'spec.json', 'activity', pub / 'out'))
    return out['artifactId'], {'artifact': (pub / 'out' / 'artifact.bin').read_bytes().hex(),
                               'package': (pub / 'out' / 'package.bin').read_bytes().hex()}


TALLY = {'name': 'Tally', 'sourcePath': str(REPO / 'world/activity/Tally.obend'), 'imports': []}
PIN, ARTIFACT = publication('publication', [TALLY], '0', 'tally')
PIN2, ARTIFACT2 = publication('publication-from-zero', [TALLY, {
    'name': 'TallyFromZero', 'sourcePath': str(REPO / 'tests/objective-activity/TallyFromZero.obend'),
    'imports': [{'alias': 'Tally', 'path': './Tally.obend', 'module': '0'}]}], '1', 'fromZero')
PIN3, ARTIFACT3 = publication('publication-fault', [TALLY, {
    'name': 'FaultAfterReply', 'sourcePath': str(REPO / 'tests/objective-activity/FaultAfterReply.obend'),
    'imports': [{'alias': 'Tally', 'path': './Tally.obend', 'module': '0'}]}], '1', 'impatient')
check('three-distinct-pins', len({PIN, PIN2, PIN3}) == 3, {'pins': [PIN, PIN2, PIN3]})
start = watched('genesis')
PUBLISHER = {'payer': SPONSOR_ACCOUNT, 'payerCapability': SPONSOR_SPEND}
turn('publish-foreign-payer-refused', sponsor, dict(ARTIFACT, kind='publish', payer=SECOND, payerCapability='4002'),
     'refused', 'notAccountOwner')
turn('publish-without-package-refused', sponsor, {**PUBLISHER, 'kind': 'publish', 'artifact': ARTIFACT['artifact'],
                                                  'package': ARTIFACT2['package']}, 'refused', 'packageSource')
turn('publish', sponsor, dict(ARTIFACT, kind='publish', **PUBLISHER), 'installed')
v = view('published', {'pins': [PIN]})
check('package-at-coordinate', cell_of(v, v['pins'][0]['packageCell']).get('kind') == 'package' and
      cell_of(v, v['pins'][0]['packageCell']).get('atCoordinate') is True, cell_of(v, v['pins'][0]['packageCell']))
turn('republish-conflicts', second, dict(ARTIFACT, kind='publish', **PUBLISHER), 'conflict')
turn('publish-from-zero', sponsor, dict(ARTIFACT2, kind='publish', **PUBLISHER), 'installed')
turn('publish-fault', sponsor, dict(ARTIFACT3, kind='publish', **PUBLISHER), 'installed')

# --- objects: a cell is an object only with a record --------------------------------
PERMIT_ALL = {'type': 'all', 'predicates': []}


def create(label, workspace, name, expect, detail=None, object_cap=None, payer=SPONSOR_ACCOUNT,
           payer_cap=SPONSOR_SPEND, pin=None):
    o = objects[name]
    return turn(label, workspace, {'kind': 'create', 'object': o['object'],
                                   'objectCapability': object_cap or o['capability'], 'pin': pin or PIN,
                                   'law': PERMIT_ALL, 'upgrade': {'frozen': {}}, 'payer': payer,
                                   'payerCapability': payer_cap}, expect, detail)


create('create-stranger-refused', second, 'tally-one', 'refused', 'notObjectHolder', object_cap='4002',
       payer=SECOND, payer_cap='4002')
create('create-foreign-payer-refused', sponsor, 'tally-one', 'refused', 'notAccountOwner', payer=SECOND,
       payer_cap='4002')
create('create-unpublished-pin-refused', sponsor, 'tally-one', 'refused', 'pinUnpublished', pin='12345')
for name in ['tally-one', 'tally-two', 'tally-three', 'tally-four', 'tally-five', 'tally-exhaust',
             'tally-abandon']:
    create(f'create-{name}', sponsor, name, 'installed')
create('create-tally-fault', sponsor, 'tally-fault', 'installed', pin=PIN3)
ov = view('objects', {'objects': [objects['tally-one']['object'], objects['bare']['object']]})
rec_one = cell_of(ov, ov['objects'][0]['objectCell'])
check('object-record-pins-tally', rec_one.get('kind') == 'object-record' and rec_one.get('pin') == PIN
      and rec_one.get('atCoordinate') is True and rec_one.get('payer') == SPONSOR_ACCOUNT, rec_one)
check('bare-has-no-record', cell_of(ov, ov['objects'][1]['objectCell']).get('kind') == 'absent',
      cell_of(ov, ov['objects'][1]['objectCell']))
create('create-again-conflicts', sponsor, 'tally-one', 'conflict')

def cap(ticks, full=True):
    """A declared envelope (Capacity): `ticks` source ticks; a full one also declares the
    kernel's fixed heap, stack, type fuel and Plan budget (Config.covers), priced at 0."""
    c = {k: '0' for k in MAXIMUM}
    if full:
        for k in ['heap', 'stack', 'typeFuel', 'outputNodes', 'outputBytes']:
            c[k] = str(MAXIMUM[k])
    c['sourceTicks'] = str(ticks)
    return c


TICKS = 3000
PRICE = 1 + TICKS
PAIR = 2 * PRICE


def variant(label, payload):
    return {'tag': 'variant', 'label': label, 'payload': payload}


def birth(label, workspace, name, deposit, expect, detail=None, account=SPONSOR_ACCOUNT, account_cap=SPONSOR_SPEND,
          object_cap=None, decider=SECOND, init=None, ticks=TICKS, resume_ticks=None, pin=None):
    o = objects[name]
    body = {'kind': 'birth', 'object': o['object'], 'objectCapability': object_cap or o['capability'],
            'account': account, 'accountCapability': account_cap, 'pin': pin or PIN,
            'input': record(init=init or variant('set', nat(0)), decider=nat(int(decider))),
            'envelope': cap(ticks), 'resume': cap(resume_ticks or ticks), 'timeout': cap(ticks),
            'deposit': str(deposit)}
    value = turn(label, workspace, body, expect, detail)
    return value.get('transaction')


def state(name, label, transaction):
    o = objects[name]['object']
    v = view(label, {'objects': [o], 'births': [{'object': o, 'transaction': transaction}],
                     'accounts': [SPONSOR_ACCOUNT, SECOND, COLLECTOR]})
    rec_cell = v['births'][0]['record']
    rec = cell_of(v, rec_cell)
    st = cell_of(v, v['objects'][0]['stateCell'])
    v['record'] = rec.get('record', {})
    v['recordKind'] = rec.get('kind')
    v['recordCell'] = rec_cell
    v['state'] = st.get('value')
    v['stateVersion'] = st.get('version')
    v['purse'] = balance(view(label + '-purse', {'accounts': [rec_cell]}), rec_cell)
    totals.append({'after': label, 'height': v.get('height'), 'total': v.get('total')})
    return v


def await_of(v):
    return v['record'].get('phase', {}).get('await', {})


def total_of(v):
    s = v.get('state') or {}
    if s.get('tag') != 'record':
        return None
    total = next((f['value'] for f in s.get('fields', []) if f.get('name') == 'total'), {})
    return int(total.get('value', '-1')) if total.get('tag') == 'natural' else None


# --- ownership -------------------------------------------------------------------
birth('stranger-birth-refused', second, 'tally-one', 20000, 'refused', 'notObjectHolder',
      account=SECOND, account_cap='4002', object_cap='4002')
birth('foreign-account-refused', second, 'tally-one', 20000, 'refused', 'notObjectHolder',
      account=SPONSOR_ACCOUNT, account_cap=SPONSOR_SPEND)
birth('foreign-payer-refused', sponsor, 'tally-one', 20000, 'refused', 'notAccountOwner',
      account=SECOND, account_cap='4002')
birth('underfunded-birth-refused', sponsor, 'tally-one', PAIR - 1, 'refused', 'underfunded')
birth('birth-on-bare-refused', sponsor, 'bare', 20000, 'refused', 'notAnObject')
birth('birth-other-pin-refused', sponsor, 'tally-one', 20000, 'refused', 'pinMismatch', pin=PIN2)

# --- tally one -------------------------------------------------------------------
before = watched('before-birth')
tx1 = birth('birth', sponsor, 'tally-one', 30000, 'installed')
s1 = state('tally-one', 'born', tx1)
REC1 = s1['recordCell']
check('born-awaiting', s1['record'].get('generation') == '0' and s1['record']['phase']['kind'] == 'awaiting'
      and total_of(s1) == 0, {'record': s1['record'].get('phase'), 'state': s1.get('state')})
check('birth-fees-on-book', balance(s1, SPONSOR_ACCOUNT) == balance(before, SPONSOR_ACCOUNT) - PRICE - 30000
      and balance(s1, COLLECTOR) == balance(before, COLLECTOR) + PRICE and s1['purse'] == 30000,
      {'sponsor': [balance(before, SPONSOR_ACCOUNT), balance(s1, SPONSOR_ACCOUNT)],
       'collector': [balance(before, COLLECTOR), balance(s1, COLLECTOR)], 'purse': s1['purse']})
slot1 = await_of(s1)['source']['slot']
turn('stranger-resolve-refused', sponsor, {'kind': 'resolve', 'slot': slot1, 'answer': {'reply': record(amount=nat(5))}},
     'refused', 'notDecider')
turn('ill-typed-reply-refused', second, {'kind': 'resolve', 'slot': slot1,
                                         'answer': {'reply': record(amount={'tag': 'label', 'value': 'five'})}},
     'refused', 'responseType')
turn('resolve', second, {'kind': 'resolve', 'slot': slot1, 'answer': {'reply': record(amount=nat(5))}}, 'installed')
await1 = await_of(s1)['id']
deliver = {'kind': 'deliver', 'record': REC1, 'await': await1, 'account': '0',
           'accountCapability': '0'}
turn('deliver-a-prepared', sponsor, deliver, 'prepared', prepare=True)
turn('deliver-b-prepared', second, deliver, 'prepared', prepare=True)
turn_a = attempts / 'deliver-a-prepared' / 'ingress.bin'
turn_b = attempts / 'deliver-b-prepared' / 'ingress.bin'
resubmit('deliver-a', turn_a, 'installed')
s2 = state('tally-one', 'resumed', tx1)
check('resumed-with-reply', total_of(s2) == 5 and s2['record'].get('generation') == '1'
      and s2['purse'] == 30000 - PRICE, {'state': s2.get('state'), 'generation': s2['record'].get('generation'),
                                          'purse': s2['purse']})
resubmit('deliver-a-retry-replays', turn_a, 'replayed')
resubmit('deliver-b-conflicts', turn_b, 'conflict')
turn('deliver-spent-await-conflicts', second, deliver, 'conflict')
await2 = await_of(s2)['id']
turn('deliver-undecided-refused', sponsor, dict(deliver, **{'await': await2}), 'refused', 'notYetDecided')

# --- resume with view: a write under a moved state is refused; the next resume sees it ---
turn('stranger-write-state-refused', second, {'kind': 'writeState',
                                               'object': objects['tally-one']['object'],
                                               'objectCapability': '4002', 'value': record(total=nat(100))},
     'refused', 'notObjectHolder')
slot2 = await_of(s2)['source']['slot']
turn('resolve-before-write', second, {'kind': 'resolve', 'slot': slot2, 'answer': {'reply': record(amount=nat(7))}},
     'installed')
turn('deliver-prepared-before-write', sponsor, dict(deliver, **{'await': await2}), 'prepared', prepare=True)
turn('owner-write-state', sponsor, {'kind': 'writeState', 'object': objects['tally-one']['object'],
                                    'objectCapability': objects['tally-one']['capability'],
                                    'value': record(total=nat(99))},
     'installed')
w1 = state('tally-one', 'after-owner-write', tx1)
check('owner-write-is-a-version', total_of(w1) == 99 and w1.get('stateVersion') == '3',
      {'state': w1.get('state'), 'version': w1.get('stateVersion')})
resubmit('stale-delivery-refused', attempts / 'deliver-prepared-before-write' / 'ingress.bin', 'refused')
turn('deliver-with-view', sponsor, dict(deliver, **{'await': await2}), 'installed')
s3 = state('tally-one', 'after-view', tx1)
check('reply-lands-on-viewed-state', total_of(s3) == 106 and s3['record'].get('generation') == '2'
      and s3.get('stateVersion') == '4',
      {'state': s3.get('state'), 'version': s3.get('stateVersion'), 'generation': s3['record'].get('generation')})

# --- two tallies on one object: both writes are kept -----------------------------------
tx5a = birth('birth-five-a', sponsor, 'tally-five', 20000, 'installed')
birth('birth-five-blind-set-refused', sponsor, 'tally-five', 20000, 'refused', 'blindWrite',
      init=variant('set', nat(50)))
tx5b = birth('birth-five-b-joins', sponsor, 'tally-five', 20000, 'installed', init=variant('keep', record()))
e1 = state('tally-five', 'five-a-born', tx5a)
e2 = state('tally-five', 'five-b-born', tx5b)
turn('five-resolve-a', second, {'kind': 'resolve', 'slot': await_of(e1)['source']['slot'],
                                'answer': {'reply': record(amount=nat(3))}}, 'installed')
turn('five-resolve-b', second, {'kind': 'resolve', 'slot': await_of(e2)['source']['slot'],
                                'answer': {'reply': record(amount=nat(4))}}, 'installed')
turn('five-deliver-b', sponsor, {'kind': 'deliver', 'record': e2['recordCell'], 'await': await_of(e2)['id'],
                                 'account': '0', 'accountCapability': '0'}, 'installed')
turn('five-deliver-a', sponsor, {'kind': 'deliver', 'record': e1['recordCell'], 'await': await_of(e1)['id'],
                                 'account': '0', 'accountCapability': '0'}, 'installed')
e1b = state('tally-five', 'five-a-resumed', tx5a)
e2b = state('tally-five', 'five-b-resumed', tx5b)
check('two-tallies-keep-both-writes', total_of(e1b) == 7 and e1b['record'].get('generation') == '1'
      and e2b['record'].get('generation') == '1' and e1b.get('stateVersion') == '3',
      {'state': e1b.get('state'), 'version': e1b.get('stateVersion'),
       'generations': [e1b['record'].get('generation'), e2b['record'].get('generation')]})

# --- funding: a purse that cannot reserve the next pair parks the activity ---------------
tx3 = birth('birth-exact-deposit', sponsor, 'tally-three', PAIR, 'installed')
f1 = state('tally-three', 'funding-born', tx3)
REC3 = f1['recordCell']
turn('funding-resolve', second, {'kind': 'resolve', 'slot': await_of(f1)['source']['slot'],
                                 'answer': {'reply': record(amount=nat(2))}}, 'installed')
deliver3 = {'kind': 'deliver', 'record': REC3, 'await': await_of(f1)['id'], 'account': '0',
            'accountCapability': '0'}
turn('deliver-awaits-funding', sponsor, deliver3, 'refused', 'awaitsFunding')
turn('top-up-stranger-account-refused', sponsor, {'kind': 'topUp', 'record': REC3, 'account': SECOND,
                                                  'accountCapability': '4002', 'amount': '10000'},
     'refused', 'notAccountOwner')
turn('top-up', second, {'kind': 'topUp', 'record': REC3, 'account': SECOND, 'accountCapability': '4002',
                        'amount': '10000'}, 'installed')
turn('deliver-funded', sponsor, deliver3, 'installed')
f2 = state('tally-three', 'funded', tx3)
check('funded-resumed', total_of(f2) == 2 and f2['purse'] == PAIR - PRICE + 10000,
      {'state': f2.get('state'), 'purse': f2['purse']})

# --- timeout: the deadline passes ------------------------------------------------------
tx2 = birth('birth-timeout', sponsor, 'tally-two', 20000, 'installed')
t1 = state('tally-two', 'timeout-born', tx2)
REC2 = t1['recordCell']
deadline = int(await_of(t1)['deadline'])
pays = 0
while int(view('height', {})['height']) <= deadline:
    pays += 1
    turn(f'pass-height-{pays}', sponsor, {'kind': 'topUp', 'record': REC3, 'account': SPONSOR_ACCOUNT,
                                          'accountCapability': SPONSOR_SPEND, 'amount': '1'}, 'installed')
turn('late-decider-refused', second, {'kind': 'resolve', 'slot': await_of(t1)['source']['slot'],
                                      'answer': {'reply': record(amount=nat(9))}}, 'refused', 'pastDeadline')
before_timeout = state('tally-two', 'before-timeout', tx2)
turn('deliver-timed-out', second, {'kind': 'deliver', 'record': REC2, 'await': await_of(t1)['id'],
                                   'account': '0', 'accountCapability': '0'}, 'installed')
t2 = state('tally-two', 'timed-out', tx2)
check('timed-out-ends-and-reclaims', t2['recordKind'] == 'reclaimed' and t2['purse'] == 0
      and balance(t2, SPONSOR_ACCOUNT) == balance(before_timeout, SPONSOR_ACCOUNT) + 20000 - PRICE,
      {'recordKind': t2['recordKind'], 'purse': t2['purse'],
       'sponsor': [balance(before_timeout, SPONSOR_ACCOUNT), balance(t2, SPONSOR_ACCOUNT)]})
slot_t = await_of(t1)['source']['slotCell']
sv = view('timed-out-slot', {'cells': [slot_t]})
check('timed-out-slot-reclaimed', cell_of(sv, slot_t).get('kind') == 'reclaimed', cell_of(sv, slot_t))
turn('deliver-after-end-refused', sponsor, {'kind': 'deliver', 'record': REC2, 'await': await_of(t1)['id'],
                                            'account': '0', 'accountCapability': '0'},
     'conflict')
turn('deliver-done-refused', sponsor, {'kind': 'deliver', 'record': REC2, 'await': '1',
                                       'account': '0', 'accountCapability': '0'},
     'refused', 'recordMissing')

# --- exhaustion: an attempt that runs out of its declared envelope is committed and paid -----
SMALL = 5
SMALL_PRICE = 1 + SMALL
tx5 = birth('birth-small-resume', sponsor, 'tally-exhaust', 20000, 'installed', resume_ticks=SMALL)
x1 = state('tally-exhaust', 'exhaust-born', tx5)
REC5 = x1['recordCell']
turn('exhaust-resolve', second, {'kind': 'resolve', 'slot': await_of(x1)['source']['slot'],
                                 'answer': {'reply': record(amount=nat(3))}}, 'installed')
await5 = await_of(x1)['id']
deliver5 = {'kind': 'deliver', 'record': REC5, 'await': await5, 'account': '0',
            'accountCapability': '0'}
exhaust5 = dict(deliver5, kind='exhaust')
turn('deliver-exhausted-refused', sponsor, deliver5, 'refused', 'exhausted')
x_before = state('tally-exhaust', 'exhaust-before', tx5)
turn('exhaust-committed', second, exhaust5, 'installed')
x2 = state('tally-exhaust', 'exhausted-once', tx5)
check('exhaust-charges-declared', x2['purse'] == x_before['purse'] - SMALL_PRICE
      and balance(x2, COLLECTOR) == balance(x_before, COLLECTOR) + SMALL_PRICE
      and balance(x2, SECOND) == balance(x_before, SECOND),
      {'purse': [x_before['purse'], x2['purse']],
       'collector': [balance(x_before, COLLECTOR), balance(x2, COLLECTOR)],
       'submitter': [balance(x_before, SECOND), balance(x2, SECOND)]})
check('exhaust-leaves-yield', x2['record'].get('generation') == x1['record'].get('generation')
      and x2['record'].get('checkpointDigest') == x1['record'].get('checkpointDigest')
      and await_of(x2).get('id') == await5 and x2['record'].get('tried') == str(SMALL),
      {'generation': x2['record'].get('generation'), 'tried': x2['record'].get('tried')})
turn('exhaust-same-envelope-refused', second, exhaust5, 'refused', 'alreadyExhausted')
turn('deliver-same-envelope-refused', sponsor, deliver5, 'refused', 'alreadyExhausted')
x3b = state('tally-exhaust', 'exhaust-before-larger', tx5)
turn('exhaust-larger-envelope', sponsor, dict(exhaust5, extra=cap(2, full=False), account=SPONSOR_ACCOUNT,
                                            accountCapability=SPONSOR_SPEND), 'installed')
x3 = state('tally-exhaust', 'exhausted-twice', tx5)
check('exhaust-again-charges-submitter-only', x3['purse'] == x3b['purse']
      and balance(x3, SPONSOR_ACCOUNT) == balance(x3b, SPONSOR_ACCOUNT) - (1 + 2)
      and x3['record'].get('tried') == str(SMALL + 2),
      {'purse': [x3b['purse'], x3['purse']], 'tried': x3['record'].get('tried'),
       'sponsor': [balance(x3b, SPONSOR_ACCOUNT), balance(x3, SPONSOR_ACCOUNT)]})
turn('deliver-enough-envelope', sponsor, dict(deliver5, extra=cap(TICKS, full=False), account=SPONSOR_ACCOUNT,
                                             accountCapability=SPONSOR_SPEND), 'installed')
x4 = state('tally-exhaust', 'exhaust-delivered', tx5)
check('exhaust-then-delivered', total_of(x4) == 3 and x4['record'].get('tried') == '0'
      and x4['record'].get('generation') == str(int(x1['record'].get('generation')) + 1),
      {'state': x4.get('state'), 'tried': x4['record'].get('tried')})

# --- abandon: nobody ends the await; after deadline + grace anyone reclaims it ------------------
GRACE = 64
tx6 = birth('birth-abandoned', sponsor, 'tally-abandon', 20000, 'installed')
a1 = state('tally-abandon', 'abandon-born', tx6)
REC6 = a1['recordCell']
await6 = await_of(a1)['id']
slot6 = await_of(a1)['source']['slot']
slot6cell = await_of(a1)['source']['slotCell']
abandon6 = {'kind': 'abandon', 'record': REC6, 'await': await6}
turn('abandon-too-early-refused', second, abandon6, 'refused', 'notYetAbandonable')
due6 = int(await_of(a1)['deadline']) + GRACE
while int(view('height-abandon', {})['height']) <= due6:
    pays += 1
    turn(f'pass-height-{pays}', sponsor, {'kind': 'topUp', 'record': REC3, 'account': SPONSOR_ACCOUNT,
                                          'accountCapability': SPONSOR_SPEND, 'amount': '1'}, 'installed')
a_before = state('tally-abandon', 'abandon-before', tx6)
turn('abandon-prepared', second, abandon6, 'prepared', prepare=True)
abandon_ingress = attempts / 'abandon-prepared' / 'ingress.bin'
resubmit('abandon', abandon_ingress, 'installed')
a2 = state('tally-abandon', 'abandoned', tx6)
fee6 = min(a_before['purse'], PRICE)
check('abandon-returns-escrow', a2['recordKind'] == 'reclaimed' and a2['purse'] == 0
      and balance(a2, COLLECTOR) == balance(a_before, COLLECTOR) + fee6
      and balance(a2, SPONSOR_ACCOUNT) == balance(a_before, SPONSOR_ACCOUNT) + a_before['purse'] - fee6,
      {'recordKind': a2['recordKind'], 'purse': [a_before['purse'], a2['purse']],
       'collector': [balance(a_before, COLLECTOR), balance(a2, COLLECTOR)],
       'sponsor': [balance(a_before, SPONSOR_ACCOUNT), balance(a2, SPONSOR_ACCOUNT)]})
sv6 = view('abandoned-slot', {'cells': [slot6cell]})
check('abandon-reclaims-slot', cell_of(sv6, slot6cell).get('kind') == 'reclaimed', cell_of(sv6, slot6cell))
resubmit('abandon-retry-replays', abandon_ingress, 'replayed')
turn('late-decider-finds-no-slot', second, {'kind': 'resolve', 'slot': slot6,
                                            'answer': {'reply': record(amount=nat(1))}}, 'refused', 'slotMissing')
turn('late-delivery-finds-no-record', sponsor, {'kind': 'deliver', 'record': REC6, 'await': await6,
                                                'account': '0', 'accountCapability': '0'},
     'refused', 'recordMissing')

# --- fault (scenario E): a resumed program's own fault commits, never wedges -------------
tx7 = birth('birth-fault', sponsor, 'tally-fault', 20000, 'installed', pin=PIN3)
e1 = state('tally-fault', 'fault-born', tx7)
REC7 = e1['recordCell']
await7 = await_of(e1)['id']
slot7cell = await_of(e1)['source']['slotCell']
turn('fault-resolve', second, {'kind': 'resolve', 'slot': await_of(e1)['source']['slot'],
                               'answer': {'reply': record(amount=nat(2))}}, 'installed')
deliver7 = {'kind': 'deliver', 'record': REC7, 'await': await7, 'account': '0',
            'accountCapability': '0'}
f_before = state('tally-fault', 'fault-before', tx7)
turn('fault-delivery-commits', second, deliver7, 'installed')
e2 = state('tally-fault', 'faulted', tx7)
check('fault-ends-and-returns-escrow', e2['recordKind'] == 'reclaimed' and e2['purse'] == 0
      and balance(e2, SPONSOR_ACCOUNT) == balance(f_before, SPONSOR_ACCOUNT) + f_before['purse'] - PRICE
      and balance(e2, COLLECTOR) == balance(f_before, COLLECTOR) + PRICE
      and total_of(e2) == 0 and e2.get('stateVersion') == '1',
      {'recordKind': e2['recordKind'], 'purse': [f_before['purse'], e2['purse']],
       'sponsor': [balance(f_before, SPONSOR_ACCOUNT), balance(e2, SPONSOR_ACCOUNT)],
       'collector': [balance(f_before, COLLECTOR), balance(e2, COLLECTOR)],
       'state': e2.get('state'), 'version': e2.get('stateVersion')})
sv7 = view('faulted-slot', {'cells': [slot7cell]})
check('fault-reclaims-slot', cell_of(sv7, slot7cell).get('kind') == 'reclaimed', cell_of(sv7, slot7cell))
turn('fault-later-delivery-refused', sponsor, dict(deliver7, **{'await': '1'}), 'refused', 'recordMissing')
turn('fault-retry-other-ingress-conflicts', sponsor, deliver7, 'conflict')

# --- growth: the checkpoint at every yield, over GROWTH turns ----------------------------
GROWTH = 12
tx4 = birth('birth-growth', sponsor, 'tally-four', 25000, 'installed', ticks=1500)
g = state('tally-four', 'growth-0', tx4)
growth = [{'generation': int(g['record']['generation']), 'checkpointBytes': int(g['record']['checkpointBytes'])}]
for i in range(1, GROWTH + 1):
    turn(f'growth-resolve-{i}', second, {'kind': 'resolve', 'slot': await_of(g)['source']['slot'],
                                         'answer': {'reply': record(amount=nat(1))}}, 'installed')
    turn(f'growth-deliver-{i}', sponsor, {'kind': 'deliver', 'record': g['recordCell'], 'await': await_of(g)['id'],
                                         'account': '0', 'accountCapability': '0'}, 'installed')
    g = state('tally-four', f'growth-{i}', tx4)
    growth.append({'generation': int(g['record']['generation']), 'checkpointBytes': int(g['record']['checkpointBytes'])})
check('growth-total', total_of(g) == GROWTH, {'state': g.get('state')})
sizes = [row['checkpointBytes'] for row in growth]
deltas = [b - a for a, b in zip(sizes, sizes[1:])]
# Measured 2026-10-04 (before resume with view): +354 B per resume before collection at
# the yield, +178 after. A yield now stores the Plan extraction's state, settled and
# collected (Kernel/ObjectiveActivity.runSegment, ACTIVITY-NATIVE-2 Q2), and the total
# lives in the declared state: expected about 0 B per resume; the bound is 200 B.
check('growth-per-resume-at-most-200', max(deltas[1:]) <= 200, {'sizes': sizes, 'deltas': deltas})

# --- conservation -------------------------------------------------------------------
check('book-total-constant', len({t['total'] for t in totals}) == 1, totals)

# --- reopen -----------------------------------------------------------------------------
final = state('tally-one', 'before-reopen', tx1)
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
r = sh('lookup-after-reopen', mini, 'activity', '--action', 'lookup', '--workspace', sponsor, '--ingress', turn_a,
       ok=(0, 1, 2))
judge('lookup-after-reopen', last_json(r), 'replayed', None)
reopened = state('tally-one', 'after-reopen', tx1)
check('reopen-view-identical', {k: reopened.get(k) for k in ['height', 'record', 'state', 'total']} ==
      {k: final.get(k) for k in ['height', 'record', 'state', 'total']},
      {'before': final.get('height'), 'after': reopened.get('height')})

checkpoints = [s1, s2, s3]
(root / 'results.json').write_text(json.dumps({
    'rows': results, 'totals': totals, 'pin': PIN, 'objects': objects,
    'records': {'one': REC1, 'two': REC2, 'three': REC3, 'exhaust': REC5, 'abandon': REC6, 'fault': REC7},
    'growthDeltas': deltas,
    'checkpointBytes': [int(s['record'].get('checkpointBytes', 0)) for s in checkpoints],
    'growth': growth,
    'allPass': all(r['ok'] for r in results)}, indent=1) + '\n')
try:
    os.kill(p.pid, 15)
except ProcessLookupError:
    pass
failed = [r['step'] for r in results if not r['ok']]
print(json.dumps({'rows': len(results), 'failed': failed}))
sys.exit(1 if failed else 0)
