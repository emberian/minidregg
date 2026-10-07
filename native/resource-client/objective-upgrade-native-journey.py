#!/usr/bin/env python3
"""The governed upgrade (Kernel/ObjectiveActivityUpgrade) end to end on a scratch NATIVE world.

  objective-upgrade-native-journey.py --bin DIR --root NEW_DIR [--plant NAME[,NAME...]]

One object `t` pins world/activity/Tally.obend (state {total}), governed by the sponsor, at total 10, with three
awaiting Tally activities: a1, a2 and a3. It upgrades to world/activity/TallyV2.obend (state {total, upgrades},
migration `migrate`: {total, upgrades: 1}), whose law caps the total at 100.

  U1 adopt     a stranger's ADOPT is refused `notUpgradeAuthority`; ADOPT of the same pin `samePin`; the
               sponsor's ADOPT installs (a3 chosen for REBIRTH): the record drains toward TallyV2.
  U2 drain     a new birth while draining toward a NON-identity migration is refused. a1's reply of 5 is
               delivered: the write is judged by the old law AND, migrated, by the new one: installs (15). a1's
               reply of 200 would make 215, which the old law admits and the NEW law (total <= 100) refuses:
               the delivery is refused `upgradeConflict`, nothing changes. MIGRATE is refused while old
               activities live (`liveActivities`).
  U3 abort     abortDrained of a2 before the drain deadline is refused `notYetDeadline`; at the deadline anyone
               ends it (resumed `upgraded` for one segment on its own package). a1 ends by a `refused` reply.
  U4 migrate   with no old activity live, MIGRATE (anyone) installs: the state is {total: 15, upgrades: 1}, the
               record pins TallyV2 and is steady again.
  U5 rebirth   a3 (chosen) is frozen: its delivery is refused `awaitingRebirth`; `rebirth` (anyone) restarts it on
               TallyV2 from its stored input; its reply of 3 lands on the migrated state (18).

PLANTS (`--plant` prints `PLANT-RESULT red GROUPS` and exits 1 when exactly the planted rows went red; `blind`, exit 3,
when a planted row stayed green):
  drain-blind   a HOST plant: --bin built from a tree patched by scripts/plants/drain-blind.py (a drained write is not
                judged by the next law) -> U2 red (the 215 delivery commits), and then U3-U5: a state the next
                law refuses got in while draining, so MIGRATE cannot complete (exactly what
                `migrate_cannot_fail` rules out on the honest kernel)
  stranger-authority  t's upgrade authority admits the second subject, not the sponsor -> U1 red (the sponsor's
                ADOPT is refused), and every later group with it (nothing drains)
ROOT/transcript holds every command's exact output; ROOT/results.json every row. Exit 1 on any red row.
"""
import argparse, pathlib, sys

HERE = pathlib.Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import activity_world as AW  # noqa: E402
from activity_world import World, PERMIT_ALL, TICKS, nat, record, eq, le, any_of, cap, variant  # noqa: E402

PLANTS = {'drain-blind': {'U2-drain', 'U3-abort', 'U4-migrate', 'U5-rebirth'},
          'stranger-authority': {'U1-adopt', 'U2-drain', 'U3-abort', 'U4-migrate', 'U5-rebirth'}}
ap = argparse.ArgumentParser()
ap.add_argument('--bin', required=True)
ap.add_argument('--root', required=True)
ap.add_argument('--plant', default='')
a = ap.parse_args()
plants = {p for p in a.plant.split(',') if p}
if plants - set(PLANTS):
    raise SystemExit(f'unknown plant {sorted(plants - set(PLANTS))}; known: {sorted(PLANTS)}')

NAMES = ['t', 'filler']
NAT = {'tag': 'natural'}
V2_STATE = {'tag': 'field', 'name': 'total', 'member': NAT,
            'tail': {'tag': 'field', 'name': 'upgrades', 'member': NAT, 'tail': {'tag': 'emptyRow'}}}
w = World(a.bin, a.root, HERE.parent.parent)
try:
    w.bring_up(NAMES)
    SPONSOR, SECOND = w.SPONSOR, w.SECOND
    TALLY = {'name': 'Tally', 'sourcePath': str(w.repo / 'world/activity/Tally.obend'), 'imports': []}
    TALLY2 = {'name': 'TallyV2', 'sourcePath': str(w.repo / 'world/activity/TallyV2.obend'), 'imports': []}
    w.PIN, ART1 = w.publication('publication-v1', [TALLY], '0', 'tally')
    PIN2, ART2 = w.publication('publication-v2', [TALLY2], '0', 'tally')
    for label, art in (('publish-v1', ART1), ('publish-v2', ART2)):
        w.turn(label, w.sponsor, dict(art, kind='publish', payer=w.SPONSOR_ACCOUNT, payerCapability=w.SPONSOR_SPEND),
               'installed')

    def governed(*subjects):
        return {'governed': {'authority': any_of(*(eq('request/subject', s) for s in subjects)), 'floors': []}}

    authority = governed(SECOND) if 'stranger-authority' in plants else governed(SPONSOR)
    w.create('create-t', w.sponsor, 't', PERMIT_ALL, 'installed', seed=record(total=nat(10)), upgrade=authority)
    w.create('create-filler', w.sponsor, 'filler', PERMIT_ALL, 'installed', seed=record(total=nat(0)))
    KEEP = variant('keep', record())

    def born(label):
        # A deposit that also covers the drained writes' migration runs (each charges the upgrade's envelope).
        tx = w.birth(label, w.sponsor, 't', 30 * AW.PRICE, 'installed', init=KEEP)
        return tx

    tx1, tx2, tx3 = born('birth-a1'), born('birth-a2'), born('birth-a3')
    s1, s2, s3 = (w.state('t', f'a{i}-born', tx) for i, tx in ((1, tx1), (2, tx2), (3, tx3)))

    def deliver_body(v):
        return {'kind': 'deliver', 'record': v['recordCell'], 'await': w.await_of(v)['id'], 'account': '0',
                'accountCapability': '0'}

    def resolve(label, v, answer, expect='installed'):
        return w.turn(label, w.second, {'kind': 'resolve', 'slot': w.await_of(v)['source']['slot'], 'answer': answer},
                      expect)

    def record_of(label):
        v = w.state('t', label)
        return v['objectRecord'], w.total_of(v), v

    def adopt(label, workspace, pin, expect, detail=None):
        body = {'kind': 'adopt', 'object': w.objects['t']['object'], 'objectCapability': w.objects['t']['capability'],
                'pin': pin, 'stateType': V2_STATE, 'migration': 'migrate', 'dropped': [],
                'law': le('state/total', 100), 'upgrade': governed(SPONSOR), 'rebirth': [s3['record'].get('activity')],
                'envelope': cap(TICKS), 'patience': '12', 'account': w.SPONSOR_ACCOUNT,
                'accountCapability': w.SPONSOR_SPEND}
        return w.turn(label, workspace, body, expect, detail)

    with w.group('U1-adopt'):
        # The stranger holds no capability on the object: since row E the capability gate runs BEFORE the turn is
        # decided, so it is refused there (notObjectHolder), before the kernel's upgrade-authority judgment runs.
        adopt('adopt-by-stranger-refused', w.second, PIN2, 'refused', 'notObjectHolder')
        adopt('adopt-same-pin-refused', w.sponsor, w.PIN, 'refused', 'samePin')
        adopt('adopt', w.sponsor, PIN2, 'installed')
        rec, total, _ = record_of('adopted')
        phase = rec.get('phase', {})
        w.check('u1-draining-toward-v2', 'draining' in phase and phase['draining'].get('pin') == PIN2
                and phase['draining'].get('migration') == 'migrate' and rec.get('pin') == w.PIN and total == 10,
                {'phase': phase, 'pin': rec.get('pin'), 'total': total})

    with w.group('U2-drain'):
        w.birth('birth-while-draining-refused', w.sponsor, 't', 7 * AW.PRICE, 'refused', None, init=KEEP)
        resolve('a1-reply-5', s1, {'reply': record(amount=nat(5))})
        w.turn('a1-deliver-5', w.sponsor, deliver_body(s1), 'installed')
        a1 = w.state('t', 'a1-after-5', tx1)
        w.check('u2-drained-write-installed', w.total_of(a1) == 15, w.total_of(a1))
        resolve('a1-reply-200', a1, {'reply': record(amount=nat(200))})
        w.turn('a1-deliver-200-refused', w.sponsor, deliver_body(a1), 'refused', 'upgradeConflict')
        _, total, _ = record_of('after-200')
        w.check('u2-new-law-judged-the-drained-write', total == 15, total)
        w.turn('migrate-while-live-refused', w.second, {'kind': 'migrate', 'object': w.objects['t']['object'],
               'account': w.SECOND, 'accountCapability': w.SECOND_SPEND}, 'refused', 'liveActivities')

    with w.group('U3-abort'):
        abort = {'kind': 'abortDrained', 'record': s2['recordCell'], 'await': w.await_of(s2)['id'],
                 'account': w.SECOND, 'accountCapability': w.SECOND_SPEND}
        rec, _, v = record_of('before-abort')
        deadline = int(rec.get('phase', {}).get('draining', {}).get('deadline', '0'))
        w.turn('abort-before-deadline-refused', w.second, abort, 'refused', 'notYetDeadline')
        i = 0
        while int(w.view(f'height-{i}', {'accounts': []}).get('height', '0')) < deadline and i < 20:
            w.birth(f'filler-{i}', w.sponsor, 'filler', 7 * AW.PRICE, 'installed', init=KEEP)
            i += 1
        w.turn('abort-a2', w.second, abort, 'installed')
        a2 = w.state('t', 'a2-aborted', tx2)
        w.check('u3-a2-ended', a2.get('recordKind') == 'retired', a2.get('recordKind'))
        # a1 is now awaiting its 200 reply's refused delivery? No: the refused delivery left a1 parked on the
        # decided 200 slot. End a1 by abortDrained as well (anyone, past the deadline).
        w.turn('abort-a1', w.second, {'kind': 'abortDrained', 'record': a1['recordCell'],
               'await': w.await_of(a1)['id'], 'account': w.SECOND, 'accountCapability': w.SECOND_SPEND},
               'installed')

    with w.group('U4-migrate'):
        w.turn('migrate', w.second, {'kind': 'migrate', 'object': w.objects['t']['object'],
               'account': w.SECOND, 'accountCapability': w.SECOND_SPEND}, 'installed')
        rec, _, v = record_of('migrated')
        st = v.get('state') or {}
        fields = {f['name']: f['value'].get('value') for f in st.get('fields', [])}
        w.check('u4-migrated-state', fields == {'total': '15', 'upgrades': '1'}, st)
        w.check('u4-record-on-v2-steady', rec.get('pin') == PIN2 and 'steady' in rec.get('phase', {}), rec)

    with w.group('U5-rebirth'):
        w.turn('a3-deliver-frozen-refused', w.sponsor, deliver_body(s3), 'refused', 'awaitingRebirth')
        w.turn('rebirth-a3', w.second, {'kind': 'rebirth', 'record': s3['recordCell'], 'await': w.await_of(s3)['id'],
               'envelope': cap(TICKS)}, 'installed')
        old = w.state('t', 'a3-old', tx3)
        w.check('u5-old-record-ended', old.get('recordKind') == 'retired', old.get('recordKind'))
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
