#!/usr/bin/env python3
"""Asynchronous `send` between objects with inboxes (OB8: Kernel/Inbox, Kernel/ObjectiveCall `send`,
Kernel/ObjectiveSend) end to end on a scratch NATIVE world.

  objective-send-native-journey.py --bin DIR --root NEW_DIR [--plant NAME[,NAME...]]

The world and the turn helpers are native/resource-client/activity_world.py. Every object pins one package,
world/send/Sends.obend. A method's frame may yield `send {to, method, args}`, answered in the same turn with
`queued {slot}` (the message id, also its reply slot's name); `deliverMessage` (anyone) pops the head of an
inbox and runs it with `request/caller` the sender and no subject.

  S1 send       poster.post(counter, 4): installs; the inbox (poster, counter) holds one message (head 0) whose
                id is the report; its reply slot is open with decider `delivery <id>`; the sponsor paid the
                envelope's price AND the postage (PRICE each); the inbox's purse holds the postage; the counter
                is unchanged (nothing is delivered yet).
  S2 deliver    the SECOND subject (not the sender's signer) delivers it: installs; counter +4; the inbox head
                is 1 and empty; the slot is decided `reply 4`; the purse paid the postage to the collector and the
                submitter paid nothing. Delivering it again is refused (`staleHead`/`empty`).
  S3 full       fan.post3(sink): five turns queue 15; a sixth (18 > 16) is refused `queueFull` naming
                (fan, sink), and nothing commits; one more single post fills 16; the next is refused `queueFull`.
  S4 failed     poster.post(vault, 2): the vault's law needs `request/subject` = the sponsor; a delivered message
                carries no subject. The delivery is NOT refused: it installs, pops the head, decides the slot
                `broken` naming `lawDenied`, commits no write (vault unchanged), and the purse pays the postage.
  S5 forward    poster.pipe(dir, 5): sends `lookup` to dir and, in the same turn, `deposit 5` to the REPLY of that
                lookup (queued on its slot, its postage in the (poster, dir) purse). Delivering the lookup decides
                its slot `ref counter`, empties the slot's queue, and forwards the deposit into inbox
                (poster, counter) with its own slot opened, its postage moved purse to purse; delivering that
                deposits 5 on the counter.
  S6 broken     poster.pipe(dir, 7) with a postage envelope too small to run the lookup: its delivery installs,
                decides the slot `broken` (exhausted), and REFUNDS the queued deposit's postage to the sponsor;
                the purse ends empty, the counter is unchanged. The same with a directory that names no object
                (`none`, no reference): the queued send is refunded.
  S7 shape      a send to a decided slot is refused `notPipelinable`; to a cell with no record `notAnObject`; an
                invocation that sends with no postage envelope is refused `uncovered`. Nothing commits.

PLANTS (self-test: the named fault is put in the WORLD, so a check that must hold fails and its row goes red):
  vault-open      the vault is created permit-all: the S4 delivery succeeds         -> S4 red
  dir-empty       the directory names no object: S5's deposit is refunded           -> S5 red
  roomy-postage   S6's postage covers the lookup: its slot is decided `reply`       -> S6 red
ROOT/transcript holds every command's exact output; ROOT/results.json every row; ROOT/groups.tsv one line per
journey row. Exit 1 on any red row.
"""
import argparse, json, pathlib, sys

HERE = pathlib.Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
from activity_world import World, PERMIT_ALL, TICKS, PRICE, nat, record, eq, any_of, cap  # noqa: E402

PLANTS = {'vault-open': {'S4-failed'}, 'dir-empty': {'S5-forward'}, 'roomy-postage': {'S6-broken'}}
ap = argparse.ArgumentParser()
ap.add_argument('--bin', required=True)
ap.add_argument('--root', required=True)
ap.add_argument('--plant', default='')
a = ap.parse_args()
plants = {p for p in a.plant.split(',') if p}
if plants - set(PLANTS):
    raise SystemExit(f'unknown plant {sorted(plants - set(PLANTS))}; known: {sorted(PLANTS)}')

NAMES = ['poster', 'counter', 'fan', 'sink', 'vault', 'dir', 'nodir', 'bare']
SMALL = 3  # a postage envelope too small to run a lookup
w = World(a.bin, a.root, HERE.parent.parent)
try:
    w.bring_up(NAMES)
    SPONSOR = w.SPONSOR
    SENDS = {'name': 'Sends', 'sourcePath': str(w.repo / 'world/send/Sends.obend'), 'imports': []}
    w.PIN, ARTIFACT = w.publication('publication', [SENDS], '0', 'deposit')
    w.turn('publish', w.sponsor, dict(ARTIFACT, kind='publish', payer=w.SPONSOR_ACCOUNT,
                                      payerCapability=w.SPONSOR_SPEND), 'installed')
    O = {n: w.objects[n]['object'] for n in NAMES}

    VAULT = PERMIT_ALL if 'vault-open' in plants else any_of(eq('request/subject', SPONSOR))
    starts = {n: 0 for n in NAMES[:-1]}
    starts['dir'] = 0 if 'dir-empty' in plants else int(O['counter'])
    for name in NAMES[:-1]:
        w.create(f'create-{name}', w.sponsor, name, VAULT if name == 'vault' else PERMIT_ALL, 'installed')
        w.turn(f'init-{name}', w.sponsor, {'kind': 'writeState', 'object': O[name],
                                           'objectCapability': w.objects[name]['capability'],
                                           'value': record(total=nat(starts[name]))}, 'installed')

    def total(name, label):
        return w.total_of(w.state(name, label))

    def invoke(label, name, method, args, expect, detail=None, postage=TICKS):
        body = {'kind': 'invoke', 'object': O[name], 'objectCapability': w.objects[name]['capability'],
                'method': method, 'args': args, 'envelope': cap(TICKS), 'account': w.SPONSOR_ACCOUNT,
                'accountCapability': w.SPONSOR_SPEND}
        if postage is not None:
            body['postage'] = cap(postage)
        return w.turn(label, w.sponsor, body, expect, detail)

    def deliver(label, sender, target, message, expect, detail=None):
        return w.turn(label, w.second, {'kind': 'deliverMessage', 'sender': O[sender], 'target': O[target],
                                        'message': str(message)}, expect, detail)

    def reported(value):
        r = value.get('report') or {}
        return int(r['value']) if r.get('tag') == 'natural' else None

    def inbox(sender, target, label):
        """The inbox (sender, target) and its purse, with the sponsor's, the second's and the collector's balances."""
        first = w.view(label + '-cell', {'inboxes': [{'sender': O[sender], 'target': O[target]}]})
        cell = first['inboxes'][0]['cell']
        v = w.view(label, {'cells': [cell], 'accounts': [cell, w.SPONSOR_ACCOUNT, w.SECOND, w.COLLECTOR]})
        held = w.cell_of(v, cell).get('inbox') or {'head': '0', 'tail': '0', 'messages': []}
        return {'cell': cell, 'head': int(held['head']), 'ids': [m['id'] for m in held['messages']],
                'messages': held['messages'], 'purse': w.balance(v, cell),
                'sponsor': w.balance(v, w.SPONSOR_ACCOUNT), 'second': w.balance(v, w.SECOND),
                'collector': w.balance(v, w.COLLECTOR)}

    def slot(name, label):
        v = w.view(label, {'slots': [str(name)]})
        return w.cell_of(v, v['slots'][0]['cell']).get('slot') or {}

    def decision(s):
        phase = s.get('phase')
        return phase.get('decision', {}) if isinstance(phase, dict) else {}

    def post(target, amount):
        return record(target=nat(O[target]), amount=nat(amount))

    with w.group('S1-send'):
        before = inbox('poster', 'counter', 's1-before')
        out = invoke('s1-post', 'poster', 'post', post('counter', 4), 'installed')
        m1 = reported(out)
        after = inbox('poster', 'counter', 's1-after')
        s1 = slot(m1, 's1-slot')
        w.check('s1-queued-one', after['ids'] == [str(m1)] and after['head'] == 0, after['ids'])
        w.check('s1-slot-open-delivery', s1.get('phase') == 'open' and s1.get('decider') == {'delivery': str(m1)},
                s1)
        w.check('s1-postage-escrowed', after['purse'] == PRICE and before['sponsor'] - after['sponsor'] == 2 * PRICE,
                {'purse': after['purse'], 'paid': before['sponsor'] - after['sponsor']})
        w.check('s1-not-yet-delivered', total('counter', 's1-counter') == 0, None)

    with w.group('S2-deliver'):
        before = inbox('poster', 'counter', 's2-before')
        out = deliver('s2-deliver', 'poster', 'counter', m1, 'installed')
        after = inbox('poster', 'counter', 's2-after')
        s2 = slot(m1, 's2-slot')
        w.check('s2-counter-4', total('counter', 's2-counter') == 4, None)
        w.check('s2-popped', after['head'] == 1 and after['ids'] == [], after)
        w.check('s2-slot-reply-4', decision(s2) == {'kind': 'reply', 'value': nat(4)}, s2)
        w.check('s2-purse-paid', after['purse'] == 0 and after['collector'] - before['collector'] == PRICE,
                {'purse': after['purse'], 'collector': after['collector'] - before['collector']})
        w.check('s2-submitter-free', after['second'] == before['second'], None)
        deliver('s2-again', 'poster', 'counter', m1, 'refused')

    with w.group('S3-full'):
        for i in range(5):
            invoke(f's3-burst-{i}', 'fan', 'post3', post('sink', 1), 'installed')
        mid = inbox('fan', 'sink', 's3-mid')
        w.check('s3-fifteen', len(mid['ids']) == 15, len(mid['ids']))
        invoke('s3-overflow', 'fan', 'post3', post('sink', 1), 'refused', ['queueFull', str(O['fan']), str(O['sink'])])
        kept = inbox('fan', 'sink', 's3-kept')
        w.check('s3-nothing-commits', kept['ids'] == mid['ids'] and total('fan', 's3-fan') == 15, len(kept['ids']))
        invoke('s3-sixteenth', 'fan', 'post', post('sink', 1), 'installed')
        invoke('s3-full', 'fan', 'post', post('sink', 1), 'refused', 'queueFull')
        w.check('s3-sixteen', len(inbox('fan', 'sink', 's3-end')['ids']) == 16, None)

    with w.group('S4-failed'):
        out = invoke('s4-post', 'poster', 'post', post('vault', 2), 'installed')
        m4 = reported(out)
        before = inbox('poster', 'vault', 's4-before')
        deliver('s4-deliver', 'poster', 'vault', m4, 'installed')
        after = inbox('poster', 'vault', 's4-after')
        d4 = decision(slot(m4, 's4-slot'))
        w.check('s4-slot-broken-law', d4.get('kind') == 'broken' and 'lawDenied' in d4.get('reason', ''), d4)
        w.check('s4-popped', after['head'] == before['head'] + 1 and after['ids'] == [], after['ids'])
        w.check('s4-no-write', total('vault', 's4-vault') == 0, None)
        w.check('s4-paid-from-purse', after['purse'] == 0 and after['collector'] - before['collector'] == PRICE
                and after['sponsor'] == before['sponsor'], after)

    with w.group('S5-forward'):
        c0 = total('counter', 's5-c0')
        out = invoke('s5-pipe', 'poster', 'pipe', record(via=nat(O['dir']), amount=nat(5)), 'installed')
        look = reported(out)
        held = inbox('poster', 'dir', 's5-held')
        sl = slot(look, 's5-slot-open')
        w.check('s5-queued-on-slot', len(sl.get('queued', [])) == 1 and held['purse'] == 2 * PRICE,
                {'queued': len(sl.get('queued', [])), 'purse': held['purse']})
        target_before = inbox('poster', 'counter', 's5-target-before')
        deliver('s5-deliver-lookup', 'poster', 'dir', look, 'installed')
        sl = slot(look, 's5-slot-decided')
        moved = inbox('poster', 'counter', 's5-target-after')
        source = inbox('poster', 'dir', 's5-source-after')
        w.check('s5-reply-ref', decision(sl) == {'kind': 'reply', 'value': {'tag': 'variant', 'label': 'ref',
                                                                           'payload': nat(O['counter'])}}, sl)
        w.check('s5-slot-emptied', sl.get('queued') == [], sl.get('queued'))
        forwarded = [i for i in moved['ids'] if i not in target_before['ids']]
        w.check('s5-forwarded', len(forwarded) == 1 and moved['purse'] - target_before['purse'] == PRICE
                and source['purse'] == 0, {'forwarded': forwarded, 'purse': moved['purse'], 'source': source['purse']})
        fslot = slot(forwarded[0], 's5-fslot') if forwarded else {}
        w.check('s5-forward-slot-open', fslot.get('decider') == {'delivery': forwarded[0] if forwarded else None}
                and fslot.get('phase') == 'open', fslot)
        if forwarded:
            deliver('s5-deliver-forward', 'poster', 'counter', forwarded[0], 'installed')
        w.check('s5-deposited', total('counter', 's5-c1') == c0 + 5, None)

    with w.group('S6-broken'):
        c0 = total('counter', 's6-c0')
        small = TICKS if 'roomy-postage' in plants else SMALL
        out = invoke('s6-pipe', 'poster', 'pipe', record(via=nat(O['dir']), amount=nat(7)), 'installed',
                     postage=small)
        look = reported(out)
        before = inbox('poster', 'dir', 's6-before')
        deliver('s6-deliver', 'poster', 'dir', look, 'installed')
        after = inbox('poster', 'dir', 's6-after')
        d6 = decision(slot(look, 's6-slot'))
        w.check('s6-slot-broken', d6.get('kind') == 'broken', d6)
        w.check('s6-refunded', after['purse'] == 0 and after['sponsor'] - before['sponsor'] == 1 + small
                and after['collector'] - before['collector'] == 1 + small,
                {'refund': after['sponsor'] - before['sponsor'], 'fee': after['collector'] - before['collector']})
        w.check('s6-counter-kept', total('counter', 's6-c1') == c0, None)
        out = invoke('s6-pipe-none', 'poster', 'pipe', record(via=nat(O['nodir']), amount=nat(7)), 'installed')
        look = reported(out)
        before = inbox('poster', 'nodir', 's6n-before')
        deliver('s6-deliver-none', 'poster', 'nodir', look, 'installed')
        after = inbox('poster', 'nodir', 's6n-after')
        dn = decision(slot(look, 's6n-slot'))
        w.check('s6-none-not-a-reference', dn.get('kind') == 'reply' and after['sponsor'] - before['sponsor'] == PRICE
                and after['purse'] == 0, {'decision': dn, 'refund': after['sponsor'] - before['sponsor']})
        w.check('s6-none-counter-kept', total('counter', 's6-c2') == c0, None)

    with w.group('S7-shape'):
        before = inbox('poster', 'counter', 's7-before')
        invoke('s7-decided-slot', 'poster', 'chase', record(target=nat(m1), amount=nat(1)), 'refused',
               ['notPipelinable', str(m1)])
        invoke('s7-not-object', 'poster', 'post', post('bare', 1), 'refused', ['notAnObject', str(O['bare'])])
        invoke('s7-no-postage', 'poster', 'post', post('counter', 1), 'refused', 'uncovered', postage=None)
        after = inbox('poster', 'counter', 's7-after')
        w.check('s7-nothing-commits', after['ids'] == before['ids'] and after['sponsor'] == before['sponsor'],
                {'before': before['ids'], 'after': after['ids']})
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
