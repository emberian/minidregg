#!/usr/bin/env python3
"""The object record end to end on a scratch NATIVE world: a cell is an object only with a record, and the
object's law judges every declared-state write (its initial state, a birth's and a delivery's).

  objectrecord-native-journey.py --bin DIR --root NEW_DIR [--plant NAME[,NAME...]]

The world and the turn helpers are native/resource-client/activity_world.py (a fresh private Store, every
turn a signed `mini activity` command, every refusal the Host's, by name). The route's own acceptance
(objective-activity-native-acceptance.py) installs every object under a permit-all law; this journey is
the half that gives the law teeth, on the kernel's object record (Kernel/ObjectRecord, R1-R3):

  OR1 no record     a write to a cell with no record is refused notAnObject (and so is a birth); nothing
                    appears at the object's cells.
  OR2 create        `create` installs the record (pin, law, frozen upgrade, payer); the view reads it back;
                    a second create conflicts; a pin that names no published package is refused. A seed
                    the law refuses (500 > 100) refuses the whole create (objectWrite, nothing installed,
                    not even the record); the same create with a lawful seed (50) installs the record AND
                    the state at version 1 (the seed is judged by the creator's law, not by the package pin).
  OR3 seed + birth  the law is   le state/total 100  AND  (turn = birth OR turn = creation OR monotone
                    state/total).  The seeded object is born onto with `keep` (the state exists, so a birth
                    cannot `set`): its first write is a no-op, the state stays 50 at version 1.
  OR4 birth law     a birth whose first write violates the law is refused objectWrite and commits nothing
                    (no record, no state, no fee); the same birth under a lawful first write installs.
  OR5 resume+view   the tally is resumed with {outcome, view}: the seeded state (50) is IN the view,
                    so a reply of 7 lands as 57, never 7; the delivery's write passes the law. A reply of 60
                    would make 117: the delivery is refused objectWrite and the activity stays parked at the
                    same await, its purse and the state untouched.
  OR6 principal     a delivery's write is judged under the activity's PRINCIPAL (its birth subject), never
                    the deliverer. Law "subject is the sponsor, or a birth": the sponsor's tally is delivered
                    by a stranger and installs. Law "subject is the stranger, or a birth": the sponsor's
                    tally is refused when the stranger delivers it (who satisfies the law) and when the
                    sponsor does.

PLANTS (self-test: the named fault is put in the WORLD, so the turns that must be refused are accepted and the
rows go red). `--plant` runs the whole journey, prints `PLANT-RESULT red GROUPS` and exits 1 when exactly the
planted rows went red (as they must), prints `PLANT-RESULT blind ...` and exits 3 when a planted row stayed
green (the journey cannot see that fault):
  record-present      the record of the no-record cell is created first            -> OR1 red
  permit-all-law      the ledger objects are created under a permit-all law       -> OR2 (the law is not read
                      back), OR3, OR4, OR5 red
  deliverer-passes    the law of the stranger-satisfying object also lets the sponsor and the stranger
                      through, so the delivery is accepted                         -> OR6 red
ROOT/transcript holds every command's exact output; ROOT/results.json every row with its expectation and
verdict; ROOT/groups.tsv one line per journey row (the runner's sub-row format). Exit 1 on any red row.
"""
import argparse, pathlib, sys

HERE = pathlib.Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
from activity_world import World, PERMIT_ALL, nat, record, variant, eq, le, monotone, all_of, any_of  # noqa: E402

# the plant -> the journey rows (groups) that must go red under it
PLANTS = {'record-present': {'OR1-no-record'},
          'permit-all-law': {'OR2-create', 'OR3-write-law', 'OR4-birth-law', 'OR5-resume-view-law'},
          'deliverer-passes': {'OR6-delivery-principal'}}
ap = argparse.ArgumentParser()
ap.add_argument('--bin', required=True)
ap.add_argument('--root', required=True)
ap.add_argument('--plant', default='')
a = ap.parse_args()
plants = {p for p in a.plant.split(',') if p}
if plants - set(PLANTS):
    raise SystemExit(f'unknown plant {sorted(plants - set(PLANTS))}; known: {sorted(PLANTS)}')

w = World(a.bin, a.root, HERE.parent.parent)
try:
    w.bring_up(['bare', 'ledger', 'ledger-b', 'owned-sponsor', 'owned-stranger'])
    SPONSOR, STRANGER = w.SPONSOR, w.SECOND

    # The one package every object here pins: the Tally resident (world/activity/Tally.obend).
    TALLY = {'name': 'Tally', 'sourcePath': str(w.repo / 'world/activity/Tally.obend'), 'imports': []}
    w.PIN, ARTIFACT = w.publication('publication', [TALLY], '0', 'tally')
    w.turn('publish', w.sponsor, dict(ARTIFACT, kind='publish', payer=w.SPONSOR_ACCOUNT,
                                      payerCapability=w.SPONSOR_SPEND), 'installed')
    start = w.watched('genesis')

    # Laws. LEDGER: a total that never passes 100, and only grows after the birth (a birth has no old state,
    # and a monotone atom fails closed on an absent old slot, so the birth is exempt by turn).
    LEDGER = all_of(le('state/total', 100), any_of(eq('request/turn', 1), eq('request/turn', 4),
                                                   monotone('state/total')))
    BY_SPONSOR = any_of(eq('request/subject', SPONSOR), eq('request/turn', 1))
    BY_STRANGER = any_of(eq('request/subject', STRANGER), eq('request/turn', 1))  # no seed: turn 4 never judged
    ledger_law = PERMIT_ALL if 'permit-all-law' in plants else LEDGER
    stranger_law = any_of(eq('request/subject', SPONSOR), eq('request/subject', STRANGER), eq('request/turn', 1)) \
        if 'deliverer-passes' in plants else BY_STRANGER

    def total_state(v, total, version):
        return w.total_of(v) == total and v.get('stateVersion') == str(version)

    deliver_body = lambda rec, await_id: {'kind': 'deliver', 'record': rec, 'await': await_id, 'account': '0',
                                          'accountCapability': '0'}

    # --- OR1: no record, no object --------------------------------------------------------------
    with w.group('OR1-no-record'):
        if 'record-present' in plants:
            w.create('plant-record-on-bare', w.sponsor, 'bare', PERMIT_ALL, 'installed')
        w.birth('birth-without-record-refused', w.sponsor, 'bare', 20000, 'refused', 'notAnObject')
        bare = w.state('bare', 'bare-after')
        w.check('bare-has-no-record-and-no-state', bare['objectRecord'].get('kind') == 'absent'
                and bare['stateKind'] == 'absent', {'object': bare['objectRecord'].get('kind'),
                                                    'state': bare['stateKind']})

    # --- OR2: create installs the record ------------------------------------------------------------
    with w.group('OR2-create'):
        w.create('create-unpublished-pin-refused', w.sponsor, 'ledger', ledger_law, 'refused', 'pinUnpublished',
                 pin='12345')
        w.create('create-seed-500-refused', w.sponsor, 'ledger', ledger_law, 'refused',
                 ['lawDenied', 'le "state/total" 100', 'before := none', 'after := some 500'],
                 seed=record(total=nat(500)))
        nothing = w.state('ledger', 'ledger-after-refused-seed')
        w.check('refused-seed-installed-nothing', nothing['objectRecord'].get('kind') == 'absent'
                and nothing['stateKind'] == 'absent', {'object': nothing['objectRecord'].get('kind'),
                                                       'state': nothing['stateKind']})
        w.create('create-ledger', w.sponsor, 'ledger', ledger_law, 'installed', seed=record(total=nat(50)))
        w.create('create-ledger-again-conflicts', w.sponsor, 'ledger', ledger_law, 'conflict',
                 seed=record(total=nat(50)))
        lv = w.state('ledger', 'ledger-created')
        rec = lv['objectRecord']
        w.check('record-pins-tally-under-its-law', rec.get('kind') == 'object-record' and rec.get('pin') == w.PIN
                and rec.get('payer') == w.SPONSOR_ACCOUNT and 'state/total' in str(rec.get('law')), rec)
        w.check('seed-installed-at-version-1', total_state(lv, 50, 1), {'state': lv.get('state'),
                                                                      'version': lv.get('stateVersion')})

    # --- OR3: a birth joins the seeded state -------------------------------------------------------------------
    with w.group('OR3-write-law'):
        tx = w.birth('ledger-birth', w.sponsor, 'ledger', 20000, 'refused', 'blindWrite')
        tx = w.birth('ledger-birth-keep', w.sponsor, 'ledger', 20000, 'installed', init=variant('keep', record()))
        s0 = w.state('ledger', 'ledger-born', tx)
        REC, SLOT1, AWAIT1 = s0['recordCell'], w.await_of(s0)['source']['slot'], w.await_of(s0)['id']
        w.check('birth-joined-the-seeded-state', total_state(s0, 50, 1), {'state': s0.get('state'),
                                                                         'version': s0.get('stateVersion')})

    # --- OR4: the law judges a birth's first write --------------------------------------------------------
    with w.group('OR4-birth-law'):
        w.create('create-ledger-b', w.sponsor, 'ledger-b', ledger_law, 'installed')
        before = w.watched('before-bad-birth')
        w.birth('birth-set-500-refused', w.sponsor, 'ledger-b', 20000, 'refused',
                ['lawDenied', 'le "state/total" 100', 'before := none', 'after := some 500'],
                init=variant('set', nat(500)))
        after = w.watched('after-bad-birth')
        lb = w.state('ledger-b', 'ledger-b-after-refusal')
        w.check('refused-birth-committed-nothing', lb['stateKind'] == 'absent'
                and w.balance(after, w.SPONSOR_ACCOUNT) == w.balance(before, w.SPONSOR_ACCOUNT),
                {'state': lb['stateKind'], 'sponsor': [w.balance(before, w.SPONSOR_ACCOUNT),
                                                       w.balance(after, w.SPONSOR_ACCOUNT)]})
        txb = w.birth('birth-set-0-installed', w.sponsor, 'ledger-b', 20000, 'installed')
        lb2 = w.state('ledger-b', 'ledger-b-born', txb)
        w.check('lawful-birth-created-the-state', total_state(lb2, 0, 1), {'state': lb2.get('state'),
                                                                          'version': lb2.get('stateVersion')})

    # --- OR5: resume with view; the law judges the delivery's write ------------------------------------------
    with w.group('OR5-resume-view-law'):
        w.turn('resolve-7', w.second, {'kind': 'resolve', 'slot': SLOT1, 'answer': {'reply': record(amount=nat(7))}},
               'installed')
        w.short_heap_plant('deliver-7-one-cell-short-refused', w.sponsor, deliver_body(REC, AWAIT1))
        w.turn('deliver-7', w.sponsor, deliver_body(REC, AWAIT1), 'installed')
        r1 = w.state('ledger', 'after-reply-7', tx)
        w.check('reply-lands-on-the-viewed-state', total_state(r1, 57, 2) and r1['record'].get('generation') == '1',
                {'state': r1.get('state'), 'version': r1.get('stateVersion'),
                 'generation': r1['record'].get('generation')})
        AWAIT2, SLOT2 = w.await_of(r1)['id'], w.await_of(r1)['source']['slot']
        w.turn('resolve-60', w.second, {'kind': 'resolve', 'slot': SLOT2, 'answer': {'reply': record(amount=nat(60))}},
               'installed')
        purse = r1['purse']
        w.turn('deliver-60-refused-by-the-law', w.sponsor, deliver_body(REC, AWAIT2), 'refused',
               ['lawDenied', 'le "state/total" 100', 'before := some 57', 'after := some 117'])
        r2 = w.state('ledger', 'after-refused-delivery', tx)
        w.check('refused-delivery-left-the-activity-parked',
                total_state(r2, 57, 2) and r2['record'].get('generation') == '1' and w.await_of(r2).get('id') == AWAIT2
                and r2['purse'] == purse, {'state': r2.get('state'), 'version': r2.get('stateVersion'),
                                           'generation': r2['record'].get('generation'), 'purse': r2['purse'],
                                           'purseBefore': purse})

    # --- OR6: a delivery is judged as its birth subject ---------------------------------------------------------
    with w.group('OR6-delivery-principal'):
        w.create('create-owned-sponsor', w.sponsor, 'owned-sponsor', BY_SPONSOR, 'installed')
        w.create('create-owned-stranger', w.sponsor, 'owned-stranger', stranger_law, 'installed')
        born = {}
        for name in ['owned-sponsor', 'owned-stranger']:
            t = w.birth(f'birth-{name}', w.sponsor, name, 12000, 'installed')
            v = w.state(name, f'{name}-born', t)
            w.turn(f'resolve-{name}', w.second, {'kind': 'resolve', 'slot': w.await_of(v)['source']['slot'],
                                                 'answer': {'reply': record(amount=nat(5))}}, 'installed')
            born[name] = (t, v)
        t, v = born['owned-sponsor']
        w.turn('stranger-delivers-sponsors-activity', w.second, deliver_body(v['recordCell'], w.await_of(v)['id']),
               'installed')
        done = w.state('owned-sponsor', 'owned-sponsor-delivered', t)
        w.check('delivered-as-the-sponsor', w.total_of(done) == 5 and done['record'].get('generation') == '1',
                {'state': done.get('state'), 'generation': done['record'].get('generation')})
        t, v = born['owned-stranger']
        body = deliver_body(v['recordCell'], w.await_of(v)['id'])
        w.turn('law-satisfying-stranger-is-not-the-principal', w.second, body, 'refused',
               ['lawDenied', 'request/subject'])
        w.turn('sponsor-is-judged-as-itself-too', w.sponsor, body, 'refused',
               ['lawDenied', 'request/subject'])
        held = w.state('owned-stranger', 'owned-stranger-held', t)
        w.check('refused-deliveries-left-it-awaiting', w.await_of(held).get('id') == w.await_of(v)['id']
                and held['record'].get('generation') == '0' and w.total_of(held) == 0,
                {'generation': held['record'].get('generation'), 'state': held.get('state')})

    with w.group('OR7-conservation'):
        end = w.watched('end')
        w.check('book-total-constant', len({t['total'] for t in w.totals}) == 1, w.totals)
    code = w.finish({'plants': sorted(plants), 'pin': w.PIN})
finally:
    w.stop()
if plants:
    red = {g['id'] for g in w.groups if g['status'] != 'PASS'}
    expected = set().union(*(PLANTS[p] for p in plants))
    if expected <= red:
        print(f'PLANT-RESULT red {sorted(red)} (planted {sorted(plants)}; expected at least {sorted(expected)})')
        code = 1
    else:
        print(f'PLANT-RESULT blind: {sorted(expected - red)} stayed green under {sorted(plants)}; red: {sorted(red)}')
        code = 3
sys.exit(code)
