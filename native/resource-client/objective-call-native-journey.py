#!/usr/bin/env python3
"""Synchronous cross-object `call` (OB7, Kernel/ObjectiveCall) end to end on a scratch NATIVE world.

  objective-call-native-journey.py --bin DIR --root NEW_DIR [--plant NAME[,NAME...]]

The world and the turn helpers are native/resource-client/activity_world.py (a fresh private Store, every
turn a signed `mini activity` command, every refusal the Host's, by name). Every object pins one package,
world/call/Calls.obend; an `invoke` turn calls one method of one object, and the call tree runs in that turn.
`report` is the root's result, shown to the signer before it signs (the signing plan's report).

  C1 leaf       counter.deposit(5): installs; the counter's state is 5 at the next version; report 5.
  C2 chain      relayA.relay(via relayB, target counter, 3): A -> B -> C admits; the counter gains 3, each
                relay counts its hop (its own write, applied when its frame returns); report = new total.
  C3 sequence   relayA.twice(counter, 2): two calls to one object in one turn; the second callee is shown
                the first's applied write (report = total + 4) and both land.
  C4 re-entry   relayA.relay(via relayB, target relayA): relayB's call back into relayA is refused `reentry`
                naming the stack; nothing commits (counter, relays, fee unchanged).
  C5 DAO        bank.withdraw pays its payee through the payee's hook BEFORE recording the debit, as a `set`
                computed from the balance it was shown. An honest payee (hook `receive`): installs, bank
                100 -> 70, payee +30. The thief (hook `drain`) withdraws again from inside its hook: refused
                `reentry`; bank stays 70, thief 0. Without the guard (the MUTANT run, see the lane's
                evidence) the same turn commits bank 40, thief 60: 60 paid for 30 debited.
  C6 authority  the vault's law: `request/subject` is the sponsor. The sponsor's direct call installs (the
                root frame carries the signer). relayA.forward(vault): the nested frame carries NO subject
                (no grant): refused `lawDenied` naming the vault, `deposit` and the clause. With a scoped grant
                (v2: {vault, deposit, code = the vault's pin, args exactly 4, 1 use}): installs. With a spent
                grant (0 uses): refused `grantSpent`. The stranger cannot invoke the sponsor's permit-all
                counter (`notObjectHolder`).
  C7 facet      the gated counter's law admits only calls whose `request/caller` is relayA (or its creation seed, turn 4):
                relayB.forward(gated) refused `lawDenied`; relayA.forward(gated) installs.
  C9 grant-args a grant binds the ARGUMENTS (GPT-6 row A): a grant {vault, deposit, cap 10 on the amount}
                used for 20 is refused `grantMismatch vault deposit cap`, nothing commits; the honest use (10)
                installs; relayA.twice(vault, 6) under {cap 10, 2 uses} charges 6 + 6 > 10: the second frame is
                refused `cap` and the WHOLE tree co-fails (the first deposit does not land); an exact grant for
                4 used for 5 is refused `grantMismatch ... args`.
  C10 grant-who a grant binds the CODE and the CALLER: a grant naming another package as the vault's code
                is refused `grantMismatch ... code`; a grant restricted to caller relayB, used by relayA, is
                refused `grantMismatch ... caller`; restricted to relayA it installs.
  C8 shape      a method whose Plan type admits `await` is refused `notCallable` before it runs; an unknown
                method `notCallable`; a call on a cell with no record `notAnObject`; an envelope too small for
                the tree `exhausted`. None of them commits anything.

PLANTS (self-test: the named fault is put in the WORLD, so a turn that must be refused is accepted and its row
goes red). `--plant` runs the whole journey, prints `PLANT-RESULT red GROUPS` and exits 1 when exactly the
planted rows went red, `PLANT-RESULT blind ...` and exits 3 when a planted row stayed green:
  honest-thief       the thief's hook is `receive` (no call back)                -> C5 red
  vault-permit-all   the vault is created under a permit-all law                  -> C6 red
  gate-open          the gated counter admits every caller                        -> C7 red
  args-blind-grant   a HOST plant: --bin built from a tree patched by
                     scripts/plants/args-blind-grant.py (Grant.judge ignores the arguments) -> C9 red
                     (the 20 commits under a grant capped at 10)
ROOT/transcript holds every command's exact output; ROOT/results.json every row; ROOT/groups.tsv one line per
journey row. Exit 1 on any red row.
"""
import argparse, json, pathlib, sys

HERE = pathlib.Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
from activity_world import World, PERMIT_ALL, TICKS, nat, record, variant, eq, any_of, cap, op_id  # noqa: E402

PLANTS = {'honest-thief': {'C5-dao'}, 'vault-permit-all': {'C6-authority'}, 'gate-open': {'C7-facet'},
          'args-blind-grant': {'C9-grant-args'}}
ap = argparse.ArgumentParser()
ap.add_argument('--bin', required=True)
ap.add_argument('--root', required=True)
ap.add_argument('--plant', default='')
a = ap.parse_args()
plants = {p for p in a.plant.split(',') if p}
if plants - set(PLANTS):
    raise SystemExit(f'unknown plant {sorted(plants - set(PLANTS))}; known: {sorted(PLANTS)}')

NAMES = ['counter', 'relayA', 'relayB', 'bank', 'payee', 'thief', 'vault', 'gated', 'bare']
w = World(a.bin, a.root, HERE.parent.parent)
try:
    w.bring_up(NAMES)
    SPONSOR = w.SPONSOR
    CALLS = {'name': 'Calls', 'sourcePath': str(w.repo / 'world/call/Calls.obend'), 'imports': []}
    w.PIN, ARTIFACT = w.publication('publication', [CALLS], '0', 'deposit')
    w.turn('publish', w.sponsor, dict(ARTIFACT, kind='publish', payer=w.SPONSOR_ACCOUNT,
                                      payerCapability=w.SPONSOR_SPEND), 'installed')
    O = {n: w.objects[n]['object'] for n in NAMES}

    VAULT = PERMIT_ALL if 'vault-permit-all' in plants else any_of(eq('request/subject', SPONSOR))
    GATED = PERMIT_ALL if 'gate-open' in plants else any_of(eq('request/caller', O['relayA']),
                                                           eq('request/turn', 4))
    laws = {'vault': VAULT, 'gated': GATED}
    starts = {'counter': 0, 'relayA': 0, 'relayB': 0, 'bank': 100, 'payee': 0, 'thief': 0, 'vault': 0,
              'gated': 0}
    for name in NAMES[:-1]:
        w.create(f'create-{name}', w.sponsor, name, laws.get(name, PERMIT_ALL), 'installed',
                 seed=record(total=nat(starts[name])))

    def total(name, label):
        return w.total_of(w.state(name, label))

    def version(name, label):
        return w.state(name, label).get('stateVersion')

    def invoke(label, name, method, args, expect, detail=None, grants=None, ticks=TICKS, workspace=None):
        body = {'kind': 'invoke', 'object': O[name], 'objectCapability': w.objects[name]['capability'],
                'method': method, 'args': args, 'envelope': cap(ticks), 'account': w.SPONSOR_ACCOUNT,
                'accountCapability': w.SPONSOR_SPEND, 'opId': op_id()}
        if grants is not None:
            body['grants'] = grants
        return w.turn(label, workspace or w.sponsor, body, expect, detail)

    def reported(value):
        r = value.get('report') or {}
        return int(r['value']) if r.get('tag') == 'natural' else None

    def snapshot_of(names, label):
        return {n: total(n, f'{label}-{n}') for n in names}

    def hop(target, amount):
        return record(target=nat(O[target]), amount=nat(amount))

    def grant(name, method, args, uses=1, code=None, caller=None):
        """A v2 grant: the target's code is its pin (every object here pins w.PIN)."""
        g = {'object': O[name], 'method': method, 'code': code or w.PIN, 'args': args, 'uses': str(uses)}
        if caller is not None:
            g['caller'] = O[caller]
        return g

    def capped(limit, path=()):
        return {'cap': {'path': list(path), 'limit': str(limit)}}

    with w.group('C1-leaf'):
        v0 = version('counter', 'c1-before')
        out = invoke('c1-deposit', 'counter', 'deposit', nat(5), 'installed')
        w.check('c1-report-5', reported(out) == 5, out.get('report'))
        w.check('c1-state-5', total('counter', 'c1-after') == 5, None)
        v1 = version('counter', 'c1-version')
        w.check('c1-next-version', v0 is not None and v1 is not None and int(v1) == int(v0) + 1, [v0, v1])

    with w.group('C2-chain'):
        out = invoke('c2-relay', 'relayA', 'relay',
                     record(via=nat(O['relayB']), target=nat(O['counter']), amount=nat(3)), 'installed')
        after = snapshot_of(['counter', 'relayA', 'relayB'], 'c2')
        w.check('c2-counter-8', after['counter'] == 8, after)
        w.check('c2-each-hop-counted', after['relayA'] == 1 and after['relayB'] == 1, after)
        w.check('c2-report-8', reported(out) == 8, out.get('report'))

    with w.group('C3-sequence'):
        out = invoke('c3-twice', 'relayA', 'twice', hop('counter', 2), 'installed')
        w.check('c3-second-sees-first', reported(out) == 12, out.get('report'))
        w.check('c3-both-land', total('counter', 'c3-after') == 12, None)

    with w.group('C4-reentry'):
        before = snapshot_of(['counter', 'relayA', 'relayB'], 'c4-before')
        fee_before = w.watched('c4-fee-before')
        invoke('c4-relay-back', 'relayA', 'relay',
               record(via=nat(O['relayB']), target=nat(O['relayA']), amount=nat(1)), 'refused',
               ['reentry', str(O['relayA'])])
        after = snapshot_of(['counter', 'relayA', 'relayB'], 'c4-after')
        fee_after = w.watched('c4-fee-after')
        w.check('c4-nothing-commits', before == after, {'before': before, 'after': after})
        w.check('c4-no-fee', w.balance(fee_before, w.SPONSOR_ACCOUNT) == w.balance(fee_after, w.SPONSOR_ACCOUNT),
                None)

    with w.group('C5-dao'):
        def pay(to, hook):
            return record(to=nat(O[to]), bank=nat(O['bank']), amount=nat(30),
                          hook={'tag': 'label', 'value': hook})
        invoke('c5-honest', 'bank', 'withdraw', pay('payee', 'receive'), 'installed')
        mid = snapshot_of(['bank', 'payee'], 'c5-mid')
        w.check('c5-honest-paid', mid == {'bank': 70, 'payee': 30}, mid)
        thief_hook = 'receive' if 'honest-thief' in plants else 'drain'
        invoke('c5-thief', 'bank', 'withdraw', pay('thief', thief_hook), 'refused', ['reentry', str(O['bank'])])
        after = snapshot_of(['bank', 'thief'], 'c5-after')
        w.check('c5-bank-kept', after == {'bank': 70, 'thief': 0}, after)

    with w.group('C6-authority'):
        invoke('c6-direct', 'vault', 'deposit', nat(1), 'installed')
        invoke('c6-no-grant', 'relayA', 'forward', hop('vault', 4), 'refused',
               ['lawDenied', str(O['vault']), 'deposit'])
        w.check('c6-no-grant-kept', total('vault', 'c6-a') == 1, None)
        invoke('c6-granted', 'relayA', 'forward', hop('vault', 4), 'installed',
               grants=[grant('vault', 'deposit', {'exact': nat(4)})])
        w.check('c6-granted-landed', total('vault', 'c6-b') == 5, None)
        invoke('c6-spent', 'relayA', 'forward', hop('vault', 4), 'refused', ['grantSpent', str(O['vault'])],
               grants=[grant('vault', 'deposit', {'exact': nat(4)}, uses=0)])
        # A stranger's call on an object it holds no capability on (its law would admit anyone):
        invoke('c6-stranger', 'counter', 'deposit', nat(1), 'refused', 'notObjectHolder', workspace=w.second)
        w.check('c6-vault-final', total('vault', 'c6-c') == 5, None)

    with w.group('C7-facet'):
        invoke('c7-wrong-caller', 'relayB', 'forward', hop('gated', 2), 'refused',
               ['lawDenied', str(O['gated'])])
        invoke('c7-right-caller', 'relayA', 'forward', hop('gated', 2), 'installed')
        w.check('c7-gated-2', total('gated', 'c7') == 2, None)

    with w.group('C9-grant-args'):
        v0 = total('vault', 'c9-before')
        invoke('c9-over-cap', 'relayA', 'forward', hop('vault', 20), 'refused',
               ['grantMismatch', str(O['vault']), 'deposit', 'cap'], grants=[grant('vault', 'deposit', capped(10))])
        w.check('c9-over-cap-kept', total('vault', 'c9-a') == v0, None)
        invoke('c9-within-cap', 'relayA', 'forward', hop('vault', 10), 'installed',
               grants=[grant('vault', 'deposit', capped(10))])
        w.check('c9-within-cap-landed', total('vault', 'c9-b') == v0 + 10, None)
        invoke('c9-cumulative', 'relayA', 'twice', hop('vault', 6), 'refused',
               ['grantMismatch', str(O['vault']), 'cap'], grants=[grant('vault', 'deposit', capped(10), uses=2)])
        w.check('c9-cumulative-co-fails', total('vault', 'c9-c') == v0 + 10, None)
        invoke('c9-exact-mismatch', 'relayA', 'forward', hop('vault', 5), 'refused',
               ['grantMismatch', str(O['vault']), 'args'], grants=[grant('vault', 'deposit', {'exact': nat(4)})])
        w.check('c9-vault-final', total('vault', 'c9-d') == v0 + 10, None)

    with w.group('C10-grant-who'):
        v0 = total('vault', 'c10-before')
        invoke('c10-wrong-code', 'relayA', 'forward', hop('vault', 1), 'refused',
               ['grantMismatch', str(O['vault']), 'code'],
               grants=[grant('vault', 'deposit', {'exact': nat(1)}, code=str(int(w.PIN) ^ 1))])
        invoke('c10-wrong-caller', 'relayA', 'forward', hop('vault', 1), 'refused',
               ['grantMismatch', str(O['vault']), 'caller'],
               grants=[grant('vault', 'deposit', {'exact': nat(1)}, caller='relayB')])
        w.check('c10-nothing-landed', total('vault', 'c10-a') == v0, None)
        invoke('c10-right-caller', 'relayA', 'forward', hop('vault', 1), 'installed',
               grants=[grant('vault', 'deposit', {'exact': nat(1)}, caller='relayA')])
        w.check('c10-landed', total('vault', 'c10-b') == v0 + 1, None)

    with w.group('C8-shape'):
        before = snapshot_of(['counter'], 'c8-before')
        invoke('c8-awaits', 'counter', 'waits', nat(1), 'refused', ['notCallable', 'await'])
        invoke('c8-unknown', 'counter', 'nothing', nat(1), 'refused', 'notCallable')
        invoke('c8-not-object', 'relayA', 'forward', hop('bare', 1), 'refused', ['notAnObject', str(O['bare'])])
        invoke('c8-exhausted', 'relayA', 'relay',
               record(via=nat(O['relayB']), target=nat(O['counter']), amount=nat(1)), 'refused', 'exhausted',
               ticks=20)
        w.check('c8-nothing-commits', snapshot_of(['counter'], 'c8-after') == before, before)
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
