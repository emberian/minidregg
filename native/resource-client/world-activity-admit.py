#!/usr/bin/env python3
"""A world/ app admitted on the ACTIVITY route (Route B), on a scratch native world.

  world-activity-admit.py --bin DIR --root NEW_DIR --method FILE.obend --entry NAME
        --birth-input JSON --deposit N [--state-type JSON] [--seed JSON]

World from activity_world.py (this checkout's Objective policy, its ordinary tariff), then:
publication (`objective-publication SPEC activity DIR`), the publish turn, create (the object pins
the package), birth with the declared envelope and deposit, and the object's declared state and
the activity's record read back from the Host's public view. Every step is a signed `mini activity`
command; every outcome is the Host's, by name, recorded in ROOT/results.json and ROOT/transcript.
Steps beyond the birth (deliveries, refusals) are given as --script FILE.json, a list of turns:
  {"label":..., "body": {...} | "deliver": true, "expect": "installed|refused|...", "detail": "..."}
The last line printed is a JSON summary.
"""
import argparse, json, pathlib, sys
HERE = pathlib.Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import activity_world as aw
from activity_world import World, record, nat, variant

ap = argparse.ArgumentParser()
for f in ['scenario','bin', 'root', 'method', 'entry', 'birth-input', 'deposit', 'state-type', 'seed', 'script', 'ticks']:
    ap.add_argument('--' + f)
a = ap.parse_args()
repo = HERE.parent.parent
w = World(a.bin, a.root, repo)
method = pathlib.Path(a.method).resolve()
ticks = int(a.ticks or aw.TICKS)
DUES_AMOUNT = 200000000
PAID_STATE = {'tag': 'field', 'name': 'paid', 'member': {'tag': 'natural'}, 'tail': {'tag': 'emptyRow'}}


def row_type(**members):
    """A declared state type: the record row of `members` (name -> 'natural'|'boolean'|'label'), fields in the
    canonical (name-sorted) order the Host's type rows use (Compiler/ObjectiveBendElaborate.lean PTy.canonical)."""
    row = {'tag': 'emptyRow'}
    for name in sorted(members, reverse=True):
        row = {'tag': 'field', 'name': name, 'member': {'tag': members[name]}, 'tail': row}
    return row


def label(text):
    return {'tag': 'label', 'value': text}


def boolean(value):
    return {'tag': 'boolean', 'value': value}


def scalar_of(state, name, tag):
    """A scalar field of a record datum ('natural' -> int, 'boolean' -> bool, 'label' -> str; None when absent)."""
    if not state or state.get('tag') != 'record':
        return None
    value = next((f['value'] for f in state.get('fields', []) if f.get('name') == name), {})
    if value.get('tag') != tag:
        return None
    return int(value['value']) if tag == 'natural' else value['value']


def modules_of(method, repo):
    """The package's modules for the publication: each `import PATH as ALIAS` line names a module that comes first
    (the cohorts' own layout: world/workshop/NatOrder.obend is module 0, imported as ./NatOrder.obend), the method last."""
    import re
    mods, imports = [], []
    for path, alias in re.findall(r'^import (\S+) as (\w+)', method.read_text(), re.M):
        src = (method.parent / path)
        src = src if src.exists() else repo / 'world' / 'workshop' / pathlib.Path(path).name
        imports.append({'alias': alias, 'path': path, 'module': str(len(mods))})
        mods.append({'name': src.stem, 'sourcePath': str(src.resolve()), 'imports': []})
    mods.append({'name': method.stem, 'sourcePath': str(method), 'imports': imports})
    return mods


KERNEL_APPS = ('bounty', 'play', 'ballot', 'story', 'commons')
APP_REWARD = 200000000
# The six apps' steps replay more of a package than the tally-sized default envelope (3000 source ticks) runs: a
# delivery of bounty's `claim` was `exhausted` at 3000. A tick is priced at 1 and the package's bytes dominate the
# price, so the envelope is raised well below the policy's per-turn maximum (200000).
APP_TICKS = 100000
ticks = int(a.ticks or (APP_TICKS if a.scenario in KERNEL_APPS else aw.TICKS))


def field_of(state, name):
    """A natural field of a record datum (None when absent)."""
    if not state or state.get('tag') != 'record':
        return None
    value = next((f['value'] for f in state.get('fields', []) if f.get('name') == name), {})
    return int(value['value']) if value.get('tag') == 'natural' else None


def source_of(v):
    return World.await_of(v).get('source', {})


def two_object_route(w, a, method):
    """world/call and world/send: objects that pin one package of methods (the call and send kernels, not a
    birth). Mirrors the call and send groups of objective-call-native-journey.py / objective-send-native-journey.py."""
    from activity_world import op_id
    names = ['counter', 'relayA', 'relayB', 'bare'] if a.scenario == 'call' else ['poster', 'counter', 'bare']
    w.bring_up(names)
    pkg = {'name': method.stem, 'sourcePath': str(method), 'imports': []}
    w.PIN, art = w.publication('publication', [pkg], '0', 'deposit')
    w.turn('publish', w.sponsor, dict(art, kind='publish', payer=w.SPONSOR_ACCOUNT, payerCapability=w.SPONSOR_SPEND),
           'installed')
    O = {n: w.objects[n]['object'] for n in names}
    for n in names[:-1]:
        w.create(f'create-{n}', w.sponsor, n, aw.PERMIT_ALL, 'installed', seed=record(total=nat(0)))
    total = lambda n, label: w.total_of(w.state(n, label))
    rep = lambda value: int((value.get('report') or {}).get('value', -1))

    def invoke(label, name, meth, args, expect, detail=None, postage=False):
        body = {'kind': 'invoke', 'object': O[name], 'objectCapability': w.objects[name]['capability'],
                'method': meth, 'args': args, 'envelope': aw.cap(aw.TICKS), 'account': w.SPONSOR_ACCOUNT,
                'accountCapability': w.SPONSOR_SPEND, 'opId': op_id()}
        if postage:
            body['postage'] = aw.cap(aw.TICKS)
            body['postageLoads'] = 1
        return w.turn(label, w.sponsor, body, expect, detail)

    hop = lambda t, amt: record(target=nat(O[t]), amount=nat(amt))
    if a.scenario == 'call':
        with w.group('call'):
            out = invoke('leaf-deposit-5', 'counter', 'deposit', nat(5), 'installed')
            w.check('leaf-report-and-state-5', rep(out) == 5 and total('counter', 'leaf') == 5,
                    {'report': out.get('report'), 'total': total('counter', 'leaf-b')})
            out = invoke('twice-2', 'relayA', 'twice', hop('counter', 2), 'installed')
            # law: a second call in the same turn is shown the first's applied write (5 + 2 + 2)
            w.check('second-callee-sees-first-write', rep(out) == 9 and total('counter', 'twice') == 9,
                    {'report': out.get('report'), 'total': total('counter', 'twice-b')})
            before = total('counter', 'pre-reentry')
            invoke('reentry-refused', 'relayA', 'relay',
                   record(via=nat(O['relayB']), target=nat(O['relayA']), amount=nat(1)), 'charged',
                   ['reentry', str(O['relayA'])])
            w.check('reentry-commits-nothing', total('counter', 'post-reentry') == before and
                    total('relayA', 'post-reentry-a') == 0, {'counter': before})
    else:
        with w.group('send'):
            out = invoke('post-4', 'poster', 'post', hop('counter', 4), 'installed', postage=True)
            m1 = rep(out)
            w.check('queued-not-delivered', total('counter', 'queued') == 0, {'message': m1})
            w.turn('deliver-4', w.second, {'kind': 'deliverMessage', 'sender': O['poster'], 'target': O['counter'],
                                           'message': str(m1)}, 'installed')
            # law: the message is delivered later, by anyone (the second subject), and lands exactly once
            w.check('delivered-lands-once', total('counter', 'delivered') == 4, {'message': m1})
            w.turn('deliver-again-refused', w.second, {'kind': 'deliverMessage', 'sender': O['poster'],
                   'target': O['counter'], 'message': str(m1)}, 'refused')
            invoke('send-to-bare-refused', 'poster', 'post', hop('bare', 1), 'refused', 'notAnObject', postage=True)
    return w.finish({'pin': w.PIN})


try:
    if a.scenario in ('call', 'send'):
        code = two_object_route(w, a, method)
        sys.exit(code)
    # a further birth on `obj` would write a state that already exists (`blindWrite`): a row that births again
    # (the underfunded teeth, the law teeth) births its own second object
    w.bring_up(['obj', 'lawful', 'forged'] if a.scenario == 'ballot'
               else ['obj', 'lawful'] if a.scenario in ('effect', 'story', 'commons')
               else ['obj', 'poor'] if a.scenario in ('bounty', 'play') else ['obj'])
    if a.scenario == 'effect':
        # world/activity/Effects.obend: commit {total: set 5}, then transfer 1 to the second subject's account
        a.birth_input = json.dumps(record(init=variant('set', nat(5)), to=nat(int(w.SECOND)), amount=nat(1)))
    if a.scenario == 'dues':
        # world/dues/StandingDues.obend: the payer is the sponsor (it funds the purse), the room the second
        # subject's account; one period's amount is more than half the deposit, so the purse pays it once and
        # the kernel refuses the second (`unfunded`): the period stays owed.
        a.birth_input = json.dumps(record(
            terms=record(payer=nat(int(w.SPONSOR_ACCOUNT)), room=nat(int(w.SECOND)), amount=nat(DUES_AMOUNT),
                         period=nat(10), start=nat(0), periods=nat(4), window=nat(3), lease={'tag': 'boolean', 'value': False}),
            deposit=nat(int(a.deposit)), keeper=nat(int(w.SECOND)), fresh={'tag': 'boolean', 'value': True}))
        a.state_type = a.state_type or json.dumps(PAID_STATE)
    if a.scenario in KERNEL_APPS:
        # The six kernel-protocol apps (e6c7ed42). The keeper (the one decider of every await) is the second subject;
        # accounts named in an input are this world's real ones (a transfer's `to` must be an account).
        sponsor_acct, second_acct = int(w.SPONSOR_ACCOUNT), int(w.SECOND)
    if a.scenario == 'bounty':
        # world/bounty/BountyBoard.obend: `Opening` :232 {posted: Posted :27, keeper, fresh}; `Ledger` :237 {moves: Nat}
        # is the declared state; the poster is the sponsor (it funds the purse), claimant and keeper the second subject.
        a.birth_input = json.dumps(record(
            posted=record(poster=nat(sponsor_acct), title=label('translate the README'), reward=nat(APP_REWARD),
                          deadline=nat(100), review=nat(20)),
            keeper=nat(second_acct), fresh=boolean(True)))
        a.state_type = a.state_type or json.dumps(row_type(moves='natural'))
    if a.scenario == 'play':
        # world/play/CommitReveal.obend: `Opening` :240 {a, b, stake, window, now, keeper, fresh}; `Ledger` :249 {moves}.
        # Player A is the sponsor, player B the second subject; the pot (2 * stake) is the deposit's to pay.
        a.birth_input = json.dumps(record(
            a=nat(sponsor_acct), b=nat(second_acct), stake=nat(APP_REWARD // 2), window=nat(5), now=nat(0),
            keeper=nat(second_acct), fresh=boolean(True)))
        a.state_type = a.state_type or json.dumps(row_type(moves='natural'))
    BALLOT_SPEC = lambda: record(first=nat(1), count=nat(3), quorum=nat(2), commitEnd=nat(50), revealEnd=nat(100),
                                 keeper=nat(second_acct), fresh=boolean(True))
    BALLOT_STATE = row_type(yes='natural', no='natural', abstain='natural', vote='natural', salt='natural',
                            commit='natural', passed='boolean', published='boolean')
    if a.scenario == 'ballot':
        # world/ballot/SealedBallot.obend: `Spec` {first, count, quorum, commitEnd, revealEnd, keeper, fresh};
        # `Published` is the declared state (yes, no, abstain, vote, salt, commit: Nat; passed, published: Bool).
        a.birth_input = json.dumps(BALLOT_SPEC())
        a.state_type = a.state_type or json.dumps(BALLOT_STATE)
    STORY_OPENING = lambda: record(title=label('the lighthouse'), window=nat(10), total=nat(1),
                                   electorate=record(first=nat(10), count=nat(3)), now=nat(0),
                                   keeper=nat(second_acct), fresh=boolean(True))
    STORY_STATE = row_type(chapters='natural', author='natural', text='label')
    if a.scenario == 'story':
        # world/story/CoAuthor.obend: `Opening` :304 {title, window, total, electorate: Electorate :44, now, keeper,
        # fresh}; `Shelf` :313 {chapters, author: Nat; text: String} is the declared state.
        a.birth_input = json.dumps(STORY_OPENING())
        a.state_type = a.state_type or json.dumps(STORY_STATE)
    COMMONS_STATE = row_type(phase='label', admissions='natural')
    if a.scenario == 'commons':
        # world/commons/ResidentServiceCommons.obend: `Opening` :766 {keeper, fresh}; `Admitted` :707 {phase: String,
        # admissions: Nat} is the declared state.
        a.birth_input = json.dumps(record(keeper=nat(second_acct), fresh=boolean(True)))
        a.state_type = a.state_type or json.dumps(COMMONS_STATE)
    mods = modules_of(method, repo)
    pin, art = w.publication('publication', mods, str(len(mods) - 1), a.entry)
    w.PIN = pin
    pub = {'payer': w.SPONSOR_ACCOUNT, 'payerCapability': w.SPONSOR_SPEND}

    def halt_if_red():
        """A setup step that is red ends the scenario there, with its red row: the steps after it would only
        fail on what it did not leave behind."""
        if any(not r['ok'] for r in w.results):
            sys.exit(w.finish({'pin': w.PIN}))

    with w.group('publish'):
        w.turn('publish', w.sponsor, dict(art, kind='publish', **pub), 'installed')
    halt_if_red()
    with w.group('create'):
        state_type = json.loads(a.state_type) if a.state_type else None
        seed = json.loads(a.seed) if a.seed else None
        w.create('create', w.sponsor, 'obj', aw.PERMIT_ALL, 'installed', state_type=state_type, seed=seed)
    halt_if_red()
    with w.group('birth'):
        o = w.objects['obj']
        body = {'kind': 'birth', 'object': o['object'], 'objectCapability': o['capability'],
                'account': w.SPONSOR_ACCOUNT, 'accountCapability': w.SPONSOR_SPEND, 'pin': pin,
                'input': json.loads(a.birth_input), 'envelope': aw.cap(ticks), 'resume': aw.cap(ticks),
                'timeout': aw.cap(ticks), 'deposit': str(a.deposit)}
        tx = w.turn('birth', w.sponsor, body, 'installed').get('transaction')
        v = w.state('obj', 'born', tx)
        w.born = v
        print(json.dumps({'record': v.get('record'), 'state': v.get('state'), 'purse': v.get('purse'),
                          'height': v.get('height')})[:1500])
    halt_if_red()
    if a.scenario == 'tally':
        # Tally law (world/activity/Tally.obend): a reply of `amount` is an ADD to the state the activity was
        # resumed with; only the named decider may decide the slot; each delivery advances the generation.
        total = World.total_of
        rec = v['recordCell']
        with w.group('tally'):
            w.check('born-awaiting-total-0', total(v) == 0 and v['record'].get('phase', {}).get('kind') == 'awaiting',
                    {'state': v.get('state'), 'phase': v['record'].get('phase')})
            cur = v
            for rnd, amount in enumerate([5, 7], start=1):
                slot = World.await_of(cur)['source']['slot']
                if rnd == 1:
                    w.turn('stranger-resolve-refused', w.sponsor,
                           {'kind': 'resolve', 'slot': slot, 'answer': {'reply': record(amount=nat(amount))}},
                           'refused', 'notDecider')
                w.turn(f'resolve-{amount}', w.second, {'kind': 'resolve', 'slot': slot,
                       'answer': {'reply': record(amount=nat(amount))}}, 'installed')
                w.turn(f'deliver-{amount}', w.sponsor, {'kind': 'deliver', 'record': rec, 'await': World.await_of(cur)['id'],
                       'account': '0', 'accountCapability': '0'}, 'installed')
                cur = w.state('obj', f'after-{amount}', tx)
                print(json.dumps({'round': rnd, 'total': total(cur), 'generation': cur['record'].get('generation'),
                                  'height': cur.get('height')}))
            w.check('replies-add-never-overwrite', total(cur) == 12 and cur['record'].get('generation') == '2',
                    {'total': total(cur), 'generation': cur['record'].get('generation')})
    if a.scenario == 'effect':
        # The statement's poles natively: an effect Plan is decided AT its yield. Satisfiable: the birth's commit is
        # performed (`settled`, total 5); the delivery's transfer of 1 is performed (the second subject's balance
        # rises by exactly 1, the write lands). Teeth: a transfer far above the purse is refused `unfunded`, one to
        # the collector `reserved`; each moves nothing and writes nothing (balance and state version unchanged).
        rec, bal = v['recordCell'], World.balance
        deliver = lambda label, cur, tx_rec: w.turn(label, w.sponsor, {'kind': 'deliver', 'record': tx_rec,
                                                    'await': World.await_of(cur)['id'], 'account': '0',
                                                    'accountCapability': '0'}, 'installed')
        with w.group('effect-satisfiable'):
            w.check('commit-performed-at-birth', source_of(v) == {'kind': 'performed', 'verdict': 'settled', 'reason': None}
                    and World.total_of(v) == 5, {'source': source_of(v), 'state': v.get('state')})
            second0 = bal(v, w.SECOND)
            # A delivery naming the activity's own purse as the account that pays its added envelope is refused.
            # The receiver refuses it first, `notAccountOwner` (a payer is admitted only for its owner, and no
            # member owns a purse); the kernel's `Delivery.purseApart` (`payerInvalid`) is the proved second line
            # behind it. The sponsor signs with a spend capability it really holds, on its own account.
            w.turn('deliver-from-the-purse-refused', w.sponsor, {'kind': 'deliver', 'record': rec,
                   'await': World.await_of(v)['id'], 'account': rec, 'accountCapability': str(w.SPONSOR_SPEND)},
                   'refused', 'notAccountOwner')
            deliver('deliver-commit', v, rec)
            v1 = w.state('obj', 'after-transfer', tx)
            w.check('transfer-performed-moves-exactly-1',
                    source_of(v1) == {'kind': 'performed', 'verdict': 'settled', 'reason': None}
                    and bal(v1, w.SECOND) == second0 + 1 and World.total_of(v1) == 6,
                    {'source': source_of(v1), 'second': [second0, bal(v1, w.SECOND)], 'state': v1.get('state')})
            deliver('deliver-transfer', v1, rec)
        for name, to, amount, reason in [('unfunded', int(w.SECOND), 10 ** 15, 'unfunded'),
                                         ('reserved', int(w.COLLECTOR), 1, 'reserved')]:
            with w.group(f'effect-teeth-{name}'):
                body = {'kind': 'birth', 'object': o['object'], 'objectCapability': o['capability'],
                        'account': w.SPONSOR_ACCOUNT, 'accountCapability': w.SPONSOR_SPEND, 'pin': pin,
                        'input': record(init=variant('add', nat(0)), to=nat(to), amount=nat(amount)),
                        'envelope': aw.cap(ticks), 'resume': aw.cap(ticks), 'timeout': aw.cap(ticks),
                        'deposit': str(a.deposit)}
                t2 = w.turn(f'birth-{name}', w.sponsor, body, 'installed').get('transaction')
                b = w.state('obj', f'born-{name}', t2)
                deliver(f'deliver-commit-{name}', b, b['recordCell'])
                after = w.state('obj', f'refused-{name}', t2)
                w.check(f'transfer-refused-{reason}-moves-nothing',
                        source_of(after) == {'kind': 'performed', 'verdict': 'refused', 'reason': reason}
                        and bal(after, w.SECOND) == bal(b, w.SECOND) and bal(after, w.COLLECTOR) >= bal(b, w.COLLECTOR)
                        and after.get('stateVersion') == b.get('stateVersion'),
                        {'source': source_of(after), 'second': [bal(b, w.SECOND), bal(after, w.SECOND)],
                         'version': [b.get('stateVersion'), after.get('stateVersion')]})
    if a.scenario == 'effect':
        # DeliverLawRefuses inhabited natively: an object whose law is `total <= 5`; the birth's commit sets 5
        # (admitted), the delivery's transfer writes `total add 1` = 6, which the law refuses: every earlier
        # step of that delivery is admitted and the whole turn is refused `objectWrite`, nothing moves or is written.
        with w.group('effect-law-refuses-delivery'):
            w.create('create-lawful', w.sponsor, 'lawful', aw.le('state/total', 5), 'installed')
            lo = w.objects['lawful']
            body = {'kind': 'birth', 'object': lo['object'], 'objectCapability': lo['capability'],
                    'account': w.SPONSOR_ACCOUNT, 'accountCapability': w.SPONSOR_SPEND, 'pin': pin,
                    'input': record(init=variant('set', nat(5)), to=nat(int(w.SECOND)), amount=nat(1)),
                    'envelope': aw.cap(ticks), 'resume': aw.cap(ticks), 'timeout': aw.cap(ticks),
                    'deposit': str(a.deposit)}
            t3 = w.turn('birth-lawful', w.sponsor, body, 'installed').get('transaction')
            b3 = w.state('lawful', 'born-lawful', t3)
            w.turn('deliver-law-refused', w.sponsor, {'kind': 'deliver', 'record': b3['recordCell'],
                   'await': World.await_of(b3)['id'], 'account': '0', 'accountCapability': '0'}, 'refused', 'objectWrite')
            a3 = w.state('lawful', 'after-law-refusal', t3)
            w.check('law-refused-delivery-writes-and-moves-nothing',
                    World.total_of(a3) == 5 and a3.get('stateVersion') == b3.get('stateVersion')
                    and World.balance(a3, w.SECOND) == World.balance(b3, w.SECOND)
                    and World.await_of(a3).get('id') == World.await_of(b3).get('id'),
                    {'total': World.total_of(a3), 'version': [b3.get('stateVersion'), a3.get('stateVersion')]})
    if a.scenario == 'dues':
        # Dues law (world/dues/StandingDues.obend) natively: period k is paid once, in order, exactly `amount`,
        # FROM THE PURSE to the room, decided by the kernel at the transfer's yield; a payment the purse cannot
        # cover is refused by name (`unfunded`) and the period stays owed; a replayed period pays nothing.
        rec, bal = v['recordCell'], World.balance
        resolve = lambda label, cur, event: w.turn(label, w.second, {'kind': 'resolve', 'slot': source_of(cur)['slot'],
                                                    'answer': {'reply': event}}, 'installed')
        deliver = lambda label, cur: w.turn(label, w.sponsor, {'kind': 'deliver', 'record': rec,
                                            'await': World.await_of(cur)['id'], 'account': '0',
                                            'accountCapability': '0'}, 'installed')
        discharge = lambda period, now: variant('discharge', record(period=nat(period), now=nat(now)))
        with w.group('dues'):
            w.check('born-awaiting-the-keeper-ledger-0', source_of(v).get('kind') == 'reply'
                    and field_of(v.get('state'), 'paid') == 0, {'source': source_of(v), 'state': v.get('state')})
            room0 = bal(v, w.SECOND)
            resolve('discharge-0', v, discharge(0, 0))
            deliver('deliver-discharge-0', v)
            v1 = w.state('obj', 'paid-0', tx)
            w.check('period-0-paid-exactly-amount-from-the-purse',
                    source_of(v1) == {'kind': 'performed', 'verdict': 'settled', 'reason': None}
                    and bal(v1, w.SECOND) == room0 + DUES_AMOUNT and field_of(v1.get('state'), 'paid') == DUES_AMOUNT,
                    {'source': source_of(v1), 'room': [room0, bal(v1, w.SECOND)], 'state': v1.get('state'),
                     'purse': [v.get('purse'), v1.get('purse')]})
            deliver('deliver-settled-0', v1)
            v2 = w.state('obj', 'awaiting-1', tx)
            resolve('replay-0', v2, discharge(0, 5))
            deliver('deliver-replay-0', v2)
            v3 = w.state('obj', 'replay-refused', tx)
            w.check('replayed-period-pays-nothing', source_of(v3).get('kind') == 'reply'
                    and bal(v3, w.SECOND) == room0 + DUES_AMOUNT, {'source': source_of(v3), 'room': bal(v3, w.SECOND)})
            resolve('discharge-1', v3, discharge(1, 10))
            deliver('deliver-discharge-1', v3)
            v4 = w.state('obj', 'unfunded-1', tx)
            w.check('period-1-refused-unfunded-moves-nothing',
                    source_of(v4) == {'kind': 'performed', 'verdict': 'refused', 'reason': 'unfunded'}
                    and bal(v4, w.SECOND) == room0 + DUES_AMOUNT and field_of(v4.get('state'), 'paid') == DUES_AMOUNT,
                    {'source': source_of(v4), 'room': bal(v4, w.SECOND), 'state': v4.get('state'), 'purse': v4.get('purse')})
            deliver('deliver-refused-1', v4)
            v5 = w.state('obj', 'still-owed-1', tx)
            w.check('period-1-still-owed-awaiting', source_of(v5).get('kind') == 'reply', {'source': source_of(v5)})
    if a.scenario in KERNEL_APPS:
        bal = World.balance
        ev = lambda name, **fields: variant(name, record(**fields))
        performed = lambda verdict, reason=None: {'kind': 'performed', 'verdict': verdict, 'reason': reason}

        def birth_of(name, inp, deposit, tag):
            """A further birth on a declared object: its transaction and the view the birth leaves."""
            ob = w.objects[name]
            body = {'kind': 'birth', 'object': ob['object'], 'objectCapability': ob['capability'],
                    'account': w.SPONSOR_ACCOUNT, 'accountCapability': w.SPONSOR_SPEND, 'pin': pin, 'input': inp,
                    'envelope': aw.cap(ticks), 'resume': aw.cap(ticks), 'timeout': aw.cap(ticks), 'deposit': str(deposit)}
            t = w.turn(tag, w.sponsor, body, 'installed').get('transaction')
            return t, w.state(name, f'{tag}-view', t)

        def deliver_only(name, tag, txn, rec_, cur, expect='installed', detail=None):
            w.turn(f'deliver-{tag}', w.sponsor, {'kind': 'deliver', 'record': rec_, 'await': World.await_of(cur)['id'],
                                                 'account': '0', 'accountCapability': '0'}, expect, detail)
            return w.state(name, f'after-{tag}', txn)

        def drive(name, tag, txn, rec_, cur, event, expect='installed', detail=None):
            """The keeper answers the pending await with `event`; anyone delivers it. Returns the view between the
            two (the resolve is the keeper's, the delivery the sponsor's) and the view after the delivery."""
            w.turn(f'resolve-{tag}', w.second, {'kind': 'resolve', 'slot': source_of(cur)['slot'],
                                                'answer': {'reply': event}}, 'installed')
            mid = w.state(name, f'resolved-{tag}', txn)
            return mid, deliver_only(name, tag, txn, rec_, cur, expect, detail)

        def waits_again(view):
            return source_of(view).get('kind') == 'reply'
    if a.scenario == 'bounty':
        # Bounty law natively (world/bounty/BountyBoard.obend header :12-17, `escrowConserved`): the reward leaves the
        # escrow (the purse: the birth deposit) exactly once, whole, to exactly one party. Plans :263-:268 (`transfer`
        # Pay {to, amount, write}), `disburse` :320: approve -> a kernel transfer of the whole reward to the claimant,
        # decided `settled` at the yield; then the next delivery ends the activity ("paid").
        rec = v['recordCell']
        with w.group('bounty'):
            w.check('born-awaiting-the-keeper-ledger-0', source_of(v).get('kind') == 'reply'
                    and field_of(v.get('state'), 'moves') == 0, {'source': source_of(v), 'state': v.get('state')})
            _, v1 = drive('obj', 'claim', tx, rec, v, ev('claim', claimant=nat(second_acct), now=nat(10)))
            _, v2 = drive('obj', 'submit', tx, rec, v1, ev('submit', claimant=nat(second_acct), work=label('doc-hash-1'), now=nat(40)))
            mid, v3 = drive('obj', 'approve', tx, rec, v2, ev('approve', actor=nat(sponsor_acct), now=nat(41)))
            w.check('approved-pays-exactly-the-reward-from-the-purse',
                    source_of(v3) == performed('settled') and bal(v3, w.SECOND) == bal(mid, w.SECOND) + APP_REWARD
                    and field_of(v3.get('state'), 'moves') == 1,
                    {'source': source_of(v3), 'claimant': [bal(mid, w.SECOND), bal(v3, w.SECOND)], 'state': v3.get('state'),
                     'purse': [v.get('purse'), v3.get('purse')]})
            v4 = deliver_only('obj', 'settled', tx, rec, v3)
            w.check('paid-once-and-finished',
                    field_of(v4.get('state'), 'moves') == 1 and bal(v4, w.SECOND) == bal(v3, w.SECOND)
                    and v4['record'].get('phase', {}).get('kind') != 'awaiting',
                    {'phase': v4['record'].get('phase'), 'state': v4.get('state')})
        # Teeth: a purse below the reward cannot pay the poster's refund at the deadline: the transfer is refused
        # `unfunded` at the yield, nothing moves and nothing is written, and the bounty waits for the next event.
        with w.group('bounty-teeth-unfunded'):
            w.create('create-poor', w.sponsor, 'poor', aw.PERMIT_ALL, 'installed', state_type=json.loads(a.state_type))
            tx2, b = birth_of('poor', json.loads(a.birth_input), APP_REWARD // 2, 'birth-underfunded')
            rec2 = b['recordCell']
            mid2, after = drive('poor', 'expire-underfunded', tx2, rec2, b, ev('expire', now=nat(100)))
            w.check('refund-refused-unfunded-moves-nothing',
                    source_of(after) == performed('refused', 'unfunded') and bal(after, w.SECOND) == bal(mid2, w.SECOND)
                    and after.get('stateVersion') == b.get('stateVersion')
                    and field_of(after.get('state'), 'moves') == field_of(b.get('state'), 'moves'),
                    {'source': source_of(after), 'version': [b.get('stateVersion'), after.get('stateVersion')],
                     'state': after.get('state')})
            again = deliver_only('poor', 'refused-underfunded', tx2, rec2, after)
            w.check('refused-disbursement-waits-for-the-next-event', waits_again(again), {'source': source_of(again)})
    if a.scenario == 'play':
        # Pot law natively (world/play/README.md:20 "Every settlement pays out exactly the pot, once"; CommitReveal.obend
        # `serve` :319, `disburse` :339, `payBNow` :357). A (the sponsor) plays paper (move 1, salt 7: seal 3*7+1 = 22,
        # `seal` :118), B (the second subject) scissors (move 2, salt 4: seal 14): B wins, `toA` is 0 so A is not paid
        # and B's one `transfer` is the whole pot (2 * stake), decided `settled` at the yield.
        rec = v['recordCell']
        commit_ = lambda who, seal_, now: ev('commit', who=nat(who), seal=nat(seal_), now=nat(now))  # Commit :83
        reveal_ = lambda who, move, salt, now: ev('reveal', who=nat(who), move=nat(move), salt=nat(salt), now=nat(now))  # Reveal :88
        with w.group('play'):
            w.check('born-awaiting-the-keeper-ledger-0', source_of(v).get('kind') == 'reply'
                    and field_of(v.get('state'), 'moves') == 0, {'source': source_of(v), 'state': v.get('state')})
            _, v1 = drive('obj', 'commit-a', tx, rec, v, commit_(sponsor_acct, 22, 2))
            _, v2 = drive('obj', 'commit-b', tx, rec, v1, commit_(second_acct, 14, 4))
            _, v3 = drive('obj', 'reveal-a', tx, rec, v2, reveal_(sponsor_acct, 1, 7, 6))
            mid, v4 = drive('obj', 'reveal-b', tx, rec, v3, reveal_(second_acct, 2, 4, 8))
            w.check('winner-paid-exactly-the-pot-from-the-purse',
                    source_of(v4) == performed('settled') and bal(v4, w.SECOND) == bal(mid, w.SECOND) + APP_REWARD
                    and field_of(v4.get('state'), 'moves') == 1,
                    {'source': source_of(v4), 'winner': [bal(mid, w.SECOND), bal(v4, w.SECOND)], 'state': v4.get('state'),
                     'purse': [v.get('purse'), v4.get('purse')]})
            v5 = deliver_only('obj', 'settled', tx, rec, v4)
            w.check('pot-paid-once-and-finished',
                    field_of(v5.get('state'), 'moves') == 1 and bal(v5, w.SECOND) == bal(v4, w.SECOND)
                    and v5['record'].get('phase', {}).get('kind') != 'awaiting',
                    {'phase': v5['record'].get('phase'), 'state': v5.get('state')})
        # Teeth: a purse of one stake cannot pay a pot of two. A lapses in its reveal window (timeout at 10 > due 9
        # forfeits A: `toB` is the pot): B's transfer is refused `unfunded`, nothing moves or is written, and the
        # game waits for the next event (the payout is tried again).
        with w.group('play-teeth-unfunded'):
            w.create('create-poor', w.sponsor, 'poor', aw.PERMIT_ALL, 'installed', state_type=json.loads(a.state_type))
            tx2, b = birth_of('poor', json.loads(a.birth_input), APP_REWARD // 2, 'birth-underfunded')
            rec2 = b['recordCell']
            _, c1 = drive('poor', 'commit-a-underfunded', tx2, rec2, b, commit_(sponsor_acct, 22, 2))
            _, c2 = drive('poor', 'commit-b-underfunded', tx2, rec2, c1, commit_(second_acct, 14, 4))
            mid2, after = drive('poor', 'timeout-underfunded', tx2, rec2, c2, ev('timeout', now=nat(10)))
            w.check('payout-refused-unfunded-moves-nothing',
                    source_of(after) == performed('refused', 'unfunded') and bal(after, w.SECOND) == bal(mid2, w.SECOND)
                    and after.get('stateVersion') == c2.get('stateVersion')
                    and field_of(after.get('state'), 'moves') == field_of(c2.get('state'), 'moves'),
                    {'source': source_of(after), 'version': [c2.get('stateVersion'), after.get('stateVersion')],
                     'state': after.get('state')})
            again = deliver_only('poor', 'refused-underfunded', tx2, rec2, after)
            w.check('refused-payout-waits-for-the-next-event', waits_again(again), {'source': source_of(again)})
    if a.scenario == 'ballot':
        # Ballot law natively (world/ballot/README.md:9-10 "TALLY ...: anyone closes the poll, once; the result is
        # derived from the retained openings"; SealedBallot.obend `publish`, `publication`, `eventWrite`). Voters 1 and
        # 2 commit their cSHAKE256("DREGG.PRED.HASHEQ/v2") digests and open inside the reveal window (checked on every
        # reveal by `law commit_binding: new.commit == 0 or hashEq([vote], salt, commit)`); the tally at the close is
        # the one `commit {write}` that publishes yes 2, no 0, abstain 0, passed (quorum 2), decided `settled`.
        RC = [1, 0x8082, 0x800000000000808a, 0x8000000080008000, 0x808b, 0x80000001, 0x8000000080008081,
              0x8000000000008009, 0x8a, 0x88, 0x80008009, 0x8000000a, 0x8000808b, 0x800000000000008b,
              0x8000000000008089, 0x8000000000008003, 0x8000000000008002, 0x8000000000000080, 0x800a,
              0x800000008000000a, 0x8000000080008081, 0x8000000000008080, 0x80000001, 0x8000000080008008]
        ROT = [0, 1, 62, 28, 27, 36, 44, 6, 55, 20, 3, 10, 43, 25, 39, 41, 45, 15, 21, 8, 18, 2, 61, 56, 14]
        PI = [0, 10, 20, 5, 15, 16, 1, 11, 21, 6, 7, 17, 2, 12, 22, 23, 8, 18, 3, 13, 14, 24, 9, 19, 4]
        M64 = (1 << 64) - 1
        rol = lambda x, n: ((x << n) | (x >> (64 - n))) & M64

        def hasheq_commit(cell, vote, salt):
            nm = lambda s: len(s).to_bytes(4, 'big') + s.encode()
            pre = (int(cell).to_bytes(8, 'big') + (1).to_bytes(4, 'big') + nm('state/vote') + nm('state/salt')
                   + nm('state/commit') + (int(vote) + (1 << 255)).to_bytes(32, 'big') + int(salt).to_bytes(32, 'big'))
            msg = bytearray(bytes([1, 136, 1, 0, 1, 160]) + b'DREGG.PRED.HASHEQ/v2' + bytes(110) + pre + b'\x04')
            while len(msg) % 136:
                msg.append(0)
            msg[-1] |= 0x80
            st = [0] * 25
            for off in range(0, len(msg), 136):
                for i in range(17):
                    st[i] ^= int.from_bytes(msg[off + 8 * i:off + 8 * i + 8], 'little')
                for rc in RC:
                    c = [st[x] ^ st[x + 5] ^ st[x + 10] ^ st[x + 15] ^ st[x + 20] for x in range(5)]
                    d = [c[(x - 1) % 5] ^ rol(c[(x + 1) % 5], 1) for x in range(5)]
                    st = [st[i] ^ d[i % 5] for i in range(25)]
                    b = [0] * 25
                    for i in range(25):
                        b[PI[i]] = rol(st[i], ROT[i])
                    st = [b[i] ^ ((~b[5 * (i // 5) + (i + 1) % 5]) & b[5 * (i // 5) + (i + 2) % 5]) for i in range(25)]
                    st[0] ^= rc
            return int.from_bytes(b''.join(st[i].to_bytes(8, 'little') for i in range(4)), 'big')

        rec = v['recordCell']
        obj_cell = int(w.objects['obj']['object'])
        d1, d2 = hasheq_commit(obj_cell, 1, 111), hasheq_commit(obj_cell, 1, 222)
        cast = lambda voter, digest, now: ev('commit', voter=nat(voter), digest=nat(digest), now=nat(now))
        open_ = lambda voter, vote, salt, digest, now: ev('reveal', voter=nat(voter), vote=nat(vote), salt=nat(salt),
                                                          digest=nat(digest), now=nat(now))
        tally = lambda now: ev('tally', now=nat(now))
        with w.group('ballot'):
            w.check('born-awaiting-the-keeper-unpublished',
                    source_of(v).get('kind') == 'reply' and scalar_of(v.get('state'), 'published', 'boolean') is False
                    and field_of(v.get('state'), 'yes') == 0, {'source': source_of(v), 'state': v.get('state')})
            _, v1 = drive('obj', 'commit-1', tx, rec, v, cast(1, d1, 10))
            _, v2 = drive('obj', 'commit-2', tx, rec, v1, cast(2, d2, 11))
            _, v3 = drive('obj', 'reveal-1', tx, rec, v2, open_(1, 1, 111, d1, 60))
            _, v4 = drive('obj', 'reveal-2', tx, rec, v3, open_(2, 1, 222, d2, 61))
            w.check('reveals-checked-by-commit-binding-law',
                    field_of(v3.get('state'), 'commit') == d1 and field_of(v4.get('state'), 'commit') == d2,
                    {'reveal1': field_of(v3.get('state'), 'commit'), 'reveal2': field_of(v4.get('state'), 'commit')})
            _, v5 = drive('obj', 'tally', tx, rec, v4, tally(100))
            st = v5.get('state')
            w.check('tally-commit-publishes-the-derived-result',
                    source_of(v5) == performed('settled') and field_of(st, 'yes') == 2 and field_of(st, 'no') == 0
                    and field_of(st, 'abstain') == 0 and scalar_of(st, 'passed', 'boolean') is True
                    and scalar_of(st, 'published', 'boolean') is True, {'source': source_of(v5), 'state': st})
            v6 = deliver_only('obj', 'settled', tx, rec, v5)
            w.check('published-once-and-finished',
                    v6.get('state') == st and v6.get('stateVersion') == v5.get('stateVersion')
                    and v6['record'].get('phase', {}).get('kind') != 'awaiting',
                    {'phase': v6['record'].get('phase'), 'state': v6.get('state')})
        # Teeth: (1) a forged non-cSHAKE256 digest is refused `objectWrite` on reveal by `commit_binding`, and
        # (2) an object whose law is `yes <= 0` refuses the publication of a result with a yes vote (`objectWrite`).
        with w.group('ballot-teeth-law-refuses-publication'):
            w.create('create-forged', w.sponsor, 'forged', aw.PERMIT_ALL, 'installed', state_type=BALLOT_STATE)
            txf, bf = birth_of('forged', BALLOT_SPEC(), a.deposit, 'birth-forged')
            recf = bf['recordCell']
            _, cf1 = drive('forged', 'commit-forged', txf, recf, bf, cast(1, 222003, 10))
            w.turn('resolve-forged-reveal', w.second, {'kind': 'resolve', 'slot': source_of(cf1)['slot'],
                                                       'answer': {'reply': open_(1, 1, 111, 222003, 60)}}, 'installed')
            w.turn('deliver-forged-reveal-refused', w.sponsor, {'kind': 'deliver', 'record': recf,
                   'await': World.await_of(cf1)['id'], 'account': '0', 'accountCapability': '0'},
                   'refused', 'objectWrite')
            w.create('create-lawful', w.sponsor, 'lawful', aw.le('state/yes', 0), 'installed', state_type=BALLOT_STATE)
            lawful_cell = int(w.objects['lawful']['object'])
            dl1 = hasheq_commit(lawful_cell, 1, 111)
            tx3, b = birth_of('lawful', BALLOT_SPEC(), a.deposit, 'birth-lawful')
            rec3 = b['recordCell']
            _, c1 = drive('lawful', 'commit-1-lawful', tx3, rec3, b, cast(1, dl1, 10))
            _, c2 = drive('lawful', 'reveal-1-lawful', tx3, rec3, c1, open_(1, 1, 111, dl1, 60))
            w.turn('resolve-tally-lawful', w.second, {'kind': 'resolve', 'slot': source_of(c2)['slot'],
                                                       'answer': {'reply': tally(100)}}, 'installed')
            w.turn('deliver-tally-law-refused', w.sponsor, {'kind': 'deliver', 'record': rec3,
                   'await': World.await_of(c2)['id'], 'account': '0', 'accountCapability': '0'}, 'refused', 'objectWrite')
            a3 = w.state('lawful', 'after-law-refusal', tx3)
            w.check('law-refused-publication-writes-nothing',
                    a3.get('state') == c2.get('state') and a3.get('stateVersion') == c2.get('stateVersion')
                    and scalar_of(a3.get('state'), 'published', 'boolean') is False
                    and World.await_of(a3).get('id') == World.await_of(c2)['id'],
                    {'state': a3.get('state'), 'version': [c2.get('stateVersion'), a3.get('stateVersion')]})
    if a.scenario == 'story':
        # Story law natively (world/story/README.md:10 "The proposal with the most votes becomes the next chapter for
        # good"; CoAuthor.obend `publish` :401, `Shelf` :313). One chapter (total 1): authors 1 and 2 propose (ids 1, 2),
        # elector 10 votes for id 2, the seal after the window is the one `commit {write}` that sets the shelf to
        # chapter 1 by author 2 with that text, decided `settled` at the yield. Events: propose/vote/seal (:107).
        rec = v['recordCell']
        propose = lambda author, text, now: ev('propose', author=nat(author), text=label(text), now=nat(now))
        vote = lambda voter, pick, now: ev('vote', voter=nat(voter), pick=nat(pick), now=nat(now))
        seal_ = lambda now: ev('seal', now=nat(now))
        with w.group('story'):
            w.check('born-awaiting-the-keeper-shelf-empty',
                    source_of(v).get('kind') == 'reply' and field_of(v.get('state'), 'chapters') == 0,
                    {'source': source_of(v), 'state': v.get('state')})
            _, v1 = drive('obj', 'propose-1', tx, rec, v, propose(1, 'a light on the rock', 1))
            _, v2 = drive('obj', 'propose-2', tx, rec, v1, propose(2, 'a ship in the fog', 2))
            _, v3 = drive('obj', 'vote-2', tx, rec, v2, vote(10, 2, 3))
            _, v4 = drive('obj', 'seal', tx, rec, v3, seal_(11))
            st = v4.get('state')
            w.check('seal-commits-the-winning-chapter',
                    source_of(v4) == performed('settled') and field_of(st, 'chapters') == 1 and field_of(st, 'author') == 2
                    and scalar_of(st, 'text', 'label') == 'a ship in the fog', {'source': source_of(v4), 'state': st})
            v5 = deliver_only('obj', 'settled', tx, rec, v4)
            w.check('sealed-once-and-complete',
                    v5.get('state') == st and v5.get('stateVersion') == v4.get('stateVersion')
                    and v5['record'].get('phase', {}).get('kind') != 'awaiting',
                    {'phase': v5['record'].get('phase'), 'state': v5.get('state')})
        # Teeth: an object whose law is `chapters <= 0` refuses the seal's chapter write: the seal's delivery is
        # refused `objectWrite` as a whole turn, the shelf stays empty and the activity stays at its yield.
        with w.group('story-teeth-law-refuses-seal'):
            w.create('create-lawful', w.sponsor, 'lawful', aw.le('state/chapters', 0), 'installed', state_type=STORY_STATE)
            tx3, b = birth_of('lawful', STORY_OPENING(), a.deposit, 'birth-lawful')
            rec3 = b['recordCell']
            _, c1 = drive('lawful', 'propose-lawful', tx3, rec3, b, propose(1, 'a light on the rock', 1))
            _, c2 = drive('lawful', 'vote-lawful', tx3, rec3, c1, vote(10, 1, 3))
            w.turn('resolve-seal-lawful', w.second, {'kind': 'resolve', 'slot': source_of(c2)['slot'],
                                                      'answer': {'reply': seal_(11)}}, 'installed')
            w.turn('deliver-seal-law-refused', w.sponsor, {'kind': 'deliver', 'record': rec3,
                   'await': World.await_of(c2)['id'], 'account': '0', 'accountCapability': '0'}, 'refused', 'objectWrite')
            a3 = w.state('lawful', 'after-law-refusal', tx3)
            w.check('law-refused-seal-writes-nothing',
                    a3.get('state') == c2.get('state') and a3.get('stateVersion') == c2.get('stateVersion')
                    and field_of(a3.get('state'), 'chapters') == 0
                    and World.await_of(a3).get('id') == World.await_of(c2).get('id'),
                    {'state': a3.get('state'), 'version': [c2.get('stateVersion'), a3.get('stateVersion')]})
    if a.scenario == 'commons':
        # Commons law natively (ResidentServiceCommons.obend :799-:831 `serve`/`step`/`admit`, comment :662-:672 of the
        # activity layer: an accepted proposal is ONE `commit {write}` that WRITES the admission {phase, admissions+1}
        # through the object's law, decided at the yield). The events are the typed `Event` values of the cohort's own
        # row `CommonsLifecycleCancelPath` (world/commons/preview-cohort.json): reserveRequested then cancelRequested,
        # taken verbatim from its responses (their payloads are the large Request/Offer/Sponsorship records :700).
        rec = v['recordCell']
        rows = json.load(open(repo / 'world' / 'commons' / 'preview-cohort.json'))
        row = next(r for r in rows if r['name'] == 'CommonsLifecycleCancelPath')

        def replies(r):
            out = []
            for resp in r['responses']:
                outcome = next(f['value'] for f in resp['payload']['fields'] if f['name'] == 'outcome')
                if outcome['label'] == 'reply':
                    out.append(outcome['payload'])
            return out
        reserve, cancel = replies(row)
        phase_of = lambda view: scalar_of(view.get('state'), 'phase', 'label')
        with w.group('commons'):
            w.check('cohort-events-are-reserve-then-cancel', reserve['label'] == 'reserveRequested'
                    and cancel['label'] == 'cancelRequested', {'labels': [reserve['label'], cancel['label']]})
            w.check('born-awaiting-the-keeper-vacant-0-admissions',
                    source_of(v).get('kind') == 'reply' and phase_of(v) == 'vacant'
                    and field_of(v.get('state'), 'admissions') == 0, {'source': source_of(v), 'state': v.get('state')})
            _, v1 = drive('obj', 'reserve', tx, rec, v, reserve)
            w.check('reserve-admission-commits-held-once',
                    source_of(v1) == performed('settled') and phase_of(v1) == 'held'
                    and field_of(v1.get('state'), 'admissions') == 1, {'source': source_of(v1), 'state': v1.get('state')})
            v2 = deliver_only('obj', 'settled-reserve', tx, rec, v1)
            _, v3 = drive('obj', 'cancel', tx, rec, v2, cancel)
            w.check('cancel-admission-commits-cancelled-once',
                    source_of(v3) == performed('settled') and phase_of(v3) == 'cancelled'
                    and field_of(v3.get('state'), 'admissions') == 2, {'source': source_of(v3), 'state': v3.get('state')})
            v4 = deliver_only('obj', 'settled-cancel', tx, rec, v3)
            w.check('terminal-phase-ends-the-activity',
                    v4.get('state') == v3.get('state') and v4['record'].get('phase', {}).get('kind') != 'awaiting',
                    {'phase': v4['record'].get('phase'), 'state': v4.get('state')})
        # Teeth: an object whose law is `admissions <= 0` refuses the reservation's admission write: the delivery is
        # refused `objectWrite` as a whole turn, the object stays `vacant` and the activity stays at its yield
        # (cohort row CommonsLifecycleRefusedAdmissionStaysAtYield).
        with w.group('commons-teeth-law-refuses-admission'):
            w.create('create-lawful', w.sponsor, 'lawful', aw.le('state/admissions', 0), 'installed', state_type=COMMONS_STATE)
            tx3, b = birth_of('lawful', record(keeper=nat(second_acct), fresh=boolean(True)), a.deposit, 'birth-lawful')
            rec3 = b['recordCell']
            w.turn('resolve-reserve-lawful', w.second, {'kind': 'resolve', 'slot': source_of(b)['slot'],
                                                         'answer': {'reply': reserve}}, 'installed')
            w.turn('deliver-reserve-law-refused', w.sponsor, {'kind': 'deliver', 'record': rec3,
                   'await': World.await_of(b)['id'], 'account': '0', 'accountCapability': '0'}, 'refused', 'objectWrite')
            a3 = w.state('lawful', 'after-law-refusal', tx3)
            w.check('law-refused-admission-writes-nothing',
                    a3.get('state') == b.get('state') and a3.get('stateVersion') == b.get('stateVersion')
                    and phase_of(a3) == 'vacant' and World.await_of(a3).get('id') == World.await_of(b).get('id'),
                    {'state': a3.get('state'), 'version': [b.get('stateVersion'), a3.get('stateVersion')]})
    code = w.finish({'pin': pin, 'height': (w.totals[-1] if w.totals else {}).get('height')})
finally:
    w.stop()
sys.exit(code)
