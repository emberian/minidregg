#!/usr/bin/env python3
"""Registered invariant domains (GPT-6 row A, A3; Kernel/ObjectiveDomain) end to end on a scratch NATIVE world.

  objective-domain-native-journey.py --bin DIR --root NEW_DIR [--plant NAME[,NAME...]]

The world is native/resource-client/activity_world.py; every object pins world/call/Calls.obend (`deposit`
adds to the object's own total, `forward` deposits on a target AND counts one on its own object). A domain
names member objects and a JOINT law over their states, member i's slots under `member/<i>/`; it is judged at
the END of every turn that writes a member's declared state, on every member's FINAL state.

  D1 joint      a and b (each under a permit-all law, governed by the sponsor) join the domain
                `member/0/state/total = member/1/state/total`, both at 5. a.deposit(1) is refused
                `domainLawDenied` (b is not written, and its state is read). The same deposit on twin t
                (same law, no domain) installs: each object's own law accepts the turn, only the joint
                law refuses it. a.forward(b, 1) moves both by one in one call tree (b by the call, a by its
                own write): installs, 6 = 6. b.forward(a, 2) (b + 1, a + 2) is refused. Each record names the
                domain.
  D2 register   the law must hold on the current states (a 6, u 5: refused `domainLawDenied`); a frozen
                member is refused `memberFrozen`; a member whose upgrade authority does not admit the signer
                is refused `memberDenied`; the same members and law again `domainExists`; a signer whose
                subject the member's authority admits but who holds no capability on it `notObjectHolder`
                (the kernel's consent is judged first, the route's holder check after); no members
                `domainShape`. A refused registration leaves every record without the domain.
  D3 stale      p 5, q 6 join `member/0/state/total <= member/1/state/total`. p.deposit(1) is prepared
                (6 <= 6: admitted). q.withdraw(1) to r installs (5 <= 5). The prepared plan, resubmitted, is
                re-judged on q's NEW state, though it does not write q: refused `domainLawDenied`.

PLANTS (self-test; `--plant` prints `PLANT-RESULT red GROUPS` and exits 1 when exactly the planted rows went red,
`PLANT-RESULT blind ...` and exits 3 when a planted row stayed green):
  domain-blind      a HOST plant: --bin built from a tree patched by scripts/plants/domain-blind.py
                    (`judgeDomains` judges nothing) -> D1 red (a.deposit(1) commits, 6 != 5) and D3 red
                    (the stale plan commits p 6 > q 5)
  member-permit     the members' upgrade authority admits nobody's subject but a stranger's -> D1 red
                    (registration refused `memberDenied`, so the joint law never binds)
ROOT/transcript holds every command's exact output; ROOT/results.json every row. Exit 1 on any red row.
"""
import argparse, pathlib, sys

HERE = pathlib.Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
from activity_world import World, PERMIT_ALL, TICKS, nat, record, eq, any_of, eq_slots, cap  # noqa: E402

PLANTS = {'domain-blind': {'D1-joint', 'D3-stale'}, 'member-permit': {'D1-joint'}}
ap = argparse.ArgumentParser()
ap.add_argument('--bin', required=True)
ap.add_argument('--root', required=True)
ap.add_argument('--plant', default='')
a = ap.parse_args()
plants = {p for p in a.plant.split(',') if p}
if plants - set(PLANTS):
    raise SystemExit(f'unknown plant {sorted(plants - set(PLANTS))}; known: {sorted(PLANTS)}')

NAMES = ['a', 'b', 't', 'z', 'c', 'u', 'p', 'q', 'r']
w = World(a.bin, a.root, HERE.parent.parent)
try:
    w.bring_up(NAMES)
    SPONSOR = w.SPONSOR
    CALLS = {'name': 'Calls', 'sourcePath': str(w.repo / 'world/call/Calls.obend'), 'imports': []}
    w.PIN, ARTIFACT = w.publication('publication', [CALLS], '0', 'deposit')
    w.turn('publish', w.sponsor, dict(ARTIFACT, kind='publish', payer=w.SPONSOR_ACCOUNT,
                                      payerCapability=w.SPONSOR_SPEND), 'installed')
    O = {n: w.objects[n]['object'] for n in NAMES}

    def governed(*subjects):
        return {'governed': {'authority': any_of(*(eq('request/subject', s) for s in subjects)), 'floors': []}}

    MEMBER = governed('999999' if 'member-permit' in plants else SPONSOR)
    policies = {'a': MEMBER, 'b': MEMBER, 't': governed(SPONSOR), 'z': {'frozen': {}},
                'c': governed('999999'), 'u': governed(SPONSOR, w.SECOND), 'p': governed(SPONSOR),
                'q': governed(SPONSOR), 'r': governed(SPONSOR)}
    starts = {'a': 5, 'b': 5, 't': 5, 'z': 5, 'c': 5, 'u': 5, 'p': 5, 'q': 6, 'r': 0}
    for name in NAMES:
        w.create(f'create-{name}', w.sponsor, name, PERMIT_ALL, 'installed', seed=record(total=nat(starts[name])),
                 upgrade=policies[name])

    def total(name, label):
        return w.total_of(w.state(name, label))

    def invoke(label, name, method, args, expect, detail=None, prepare=False):
        body = {'kind': 'invoke', 'object': O[name], 'objectCapability': w.objects[name]['capability'],
                'method': method, 'args': args, 'envelope': cap(TICKS), 'account': w.SPONSOR_ACCOUNT,
                'accountCapability': w.SPONSOR_SPEND}
        return w.turn(label, w.sponsor, body, expect, detail, prepare=prepare)

    def register(label, names, law, expect, detail=None, workspace=None, caps=None):
        body = {'kind': 'registerDomain',
                'members': [{'object': O[n], 'capability': (caps or {}).get(n, w.objects[n]['capability'])}
                            for n in names],
                'law': law, 'payer': w.SPONSOR_ACCOUNT, 'payerCapability': w.SPONSOR_SPEND}
        return w.turn(label, workspace or w.sponsor, body, expect, detail)

    def hop(target, amount):
        return record(target=nat(O[target]), amount=nat(amount))

    EQUAL = eq_slots('member/0/state/total', 'member/1/state/total')

    with w.group('D1-joint'):
        register('d1-register', ['a', 'b'], EQUAL, 'installed')
        ra = (w.state('a', 'd1-a-record').get('objectRecord') or {}).get('domains')
        rb = (w.state('b', 'd1-b-record').get('objectRecord') or {}).get('domains')
        w.check('d1-both-records-name-the-domain', ra is not None and len(ra) == 1 and ra == rb, [ra, rb])
        invoke('d1-a-alone-refused', 'a', 'deposit', nat(1), 'refused', ['domainLawDenied', 'member/1/state/total'])
        w.check('d1-unchanged-5-5', [total('a', 'd1-a1'), total('b', 'd1-b1')] == [5, 5], None)
        invoke('d1-twin-installs', 't', 'deposit', nat(1), 'installed')
        w.check('d1-twin-6', total('t', 'd1-t') == 6, None)
        invoke('d1-both-move', 'a', 'forward', hop('b', 1), 'installed')
        w.check('d1-6-6', [total('a', 'd1-a2'), total('b', 'd1-b2')] == [6, 6], None)
        invoke('d1-uneven-refused', 'b', 'forward', hop('a', 2), 'refused', 'domainLawDenied')
        w.check('d1-still-6-6', [total('a', 'd1-a3'), total('b', 'd1-b3')] == [6, 6], None)

    with w.group('D2-register'):
        register('d2-law-fails-now', ['a', 'u'], EQUAL, 'refused', 'domainLawDenied')
        register('d2-frozen', ['t', 'z'], EQUAL, 'refused', 'memberFrozen')
        register('d2-denied', ['t', 'c'], EQUAL, 'refused', 'memberDenied')
        register('d2-exists', ['a', 'b'], EQUAL, 'refused', 'domainExists')
        register('d2-not-holder', ['u'], PERMIT_ALL, 'refused', 'notObjectHolder', workspace=w.second)
        register('d2-empty', [], EQUAL, 'refused', 'domainShape')
        recs = {n: (w.state(n, f'd2-{n}-record').get('objectRecord') or {}).get('domains') for n in ['t', 'u', 'z', 'c']}
        w.check('d2-refused-joins-nothing', all(r == [] for r in recs.values()), recs)

    with w.group('D3-stale'):
        register('d3-register', ['p', 'q'], {'type': 'leSlots', 'left': 'member/0/state/total',
                                             'right': 'member/1/state/total'}, 'installed')
        invoke('d3-prepared', 'p', 'deposit', nat(1), 'prepared', prepare=True)
        pay = record(to=nat(O['r']), bank=nat(O['q']), amount=nat(1), hook={'tag': 'label', 'value': 'receive'})
        invoke('d3-q-withdraws', 'q', 'withdraw', pay, 'installed')
        w.check('d3-p5-q5-r1', [total('p', 'd3-p0'), total('q', 'd3-q0'), total('r', 'd3-r0')] == [5, 5, 1], None)
        w.resubmit('d3-stale-refused', w.attempts / 'd3-prepared' / 'ingress.bin', 'refused',
                   ['domainLawDenied', 'leSlots'])
        w.check('d3-p-still-5', total('p', 'd3-p1') == 5, None)

finally:
    w.stop()

code = w.finish({'pin': w.__dict__.get('PIN'), 'plants': sorted(plants)})
if plants:
    expected = set().union(*(PLANTS[p] for p in plants))
    red = {g['id'] for g in w.groups if g['status'] != 'PASS'}
    if red == expected:
        print('PLANT-RESULT red ' + ','.join(sorted(red)))
        sys.exit(1)
    print(f'PLANT-RESULT blind expected={sorted(expected)} red={sorted(red)}')
    sys.exit(3)
sys.exit(code)
