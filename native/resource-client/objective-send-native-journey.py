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
  S8 interface  (row F) poster.relay(counter, bounce, 1): `bounce`'s Plan admits `send`, and a delivered message
                has no paying account for onward sends, so the SEND is refused `notDeliverable` naming (counter,
                bounce): no fee, no postage escrowed, no message, no slot. An unknown method is refused
                `notCallable`, arguments that do not type `argumentType`, all at the send. The same relay naming
                `deposit` installs and delivers (+1).
  S9 resolved   (row F) poster.relayVia(dir, bounce, 3): the pipelined send's target is known only when the lookup
                resolves, so `Deliverable` is decided then, at the RESOLVED object: the lookup decides `ref counter`,
                the queued `bounce` is NOT forwarded (inbox (poster, counter) unchanged) and its postage is REFUNDED
                to the sponsor; the (poster, dir) purse ends empty.
  S10 cancel    (row F, CANCEL-IF-QUEUED) poster queues three deposits a, b, c on (poster, counter) and cancels b
                (`cancelOf`, the sending object's frame): b leaves the inbox, a and c keep their order and the
                head stays; the purse returns EXACTLY b's postage to the sponsor (sponsor +PRICE = refund, less the
                cancel's own fee, which the collector gets); b's slot is decided `cancelled`; delivering b is
                refused; a and c are delivered (+1, +3). A cancel of a pipelined lookup refunds the lookup AND the
                send queued on its slot (2 x PRICE), leaving the (poster, dir) purse empty.
  S11 pole      (row F, ack at the yield, effect at the commit) a cancel of m PREPARED while m is queued (acked),
                then m is delivered: the prepared cancel no longer commits (refused `wrongMessage`: the outcome
                its signature consented to, a withdrawal, is not what it would commit now), and a
                fresh cancel commits as a NO-OP: the slot stays `reply`, nothing is refunded (sponsor pays only
                the fee), the purse is unchanged.
  S12 stop      (row F, STOP-WAITING) poster pipes a deposit on a lookup, then `stopOf`s the lookup: the pipelined
                deposit's postage is refunded (PRICE), the slot stays open, unwatched, its queue empty; the lookup
                is STILL delivered (popped, its postage to the collector) and its delivery RETIRES the slot; the
                counter is unchanged. A stop of a slot already decided (S2's) retires it at once.
  S13 who       (row F, authority) another object's cancel or stop of poster's queued message is refused
                `notSender`; a slot that does not exist `notControllable`; a pipelined send onto a stopped slot
                `notPipelinable`; nothing commits.
  S14 continue  (row F, PREPAID CONTINUATION ALLOWANCE) relayer.relayA(counter, bounce, allowance A = 1.5 PRICE):
                the send to a sending method is admitted because its message carries an allowance covering an
                onward send; it escrows PRICE + A. Its delivery replies, queues bounce's onward deposit on
                (counter, counter) at depth 1 with no allowance, its escrow (PRICE) moved purse to purse out of
                the allowance, and refunds EXACTLY the remainder A - PRICE to the sponsor; the onward deposit is
                then delivered.
  S15 exceed    the same with bounce2 (two onward sends, 2 PRICE > A): the delivery decides `broken` naming
                `allowanceExceeded 2PRICE A`, queues nothing onward, commits no write, and refunds the WHOLE
                allowance (the postage paid the attempt). An invocation whose sends carry more allowance than
                the `allowance` its signer declared is refused `allowanceExceeded` at the send; nothing commits.
  S16 fanout    bounce5 (five onward sends, allowance 6 PRICE): broken naming `fanOut 4`, nothing onward,
                the allowance refunded.
  S17 depth     relayer.hop(hopper, 10 PRICE): a self-relaying chain on hopper. Depth 0 and 1 are delivered (each
                queues the next hop, one deeper, out of its allowance); the delivery at depth 2 decides `broken`
                naming `continuationDepth 3` (its onward hop would be at depth 3) and refunds its allowance.
  S18 cancel    relayer queues relayA(counter, bounce, A) and cancels it while queued: the refund is EXACTLY
                PRICE + A (postage and allowance), the slot decided `cancelled`.

PLANTS (self-test: the named fault is put in the WORLD, so a check that must hold fails and its row goes red):
  vault-open      the vault is created permit-all: the S4 delivery succeeds         -> S4 red
  dir-empty       the directory names no object: S5's deposit is refunded           -> S5 red
  roomy-postage   S6's postage covers the lookup: its slot is decided `reply`       -> S6 red
  relay-deposit   S8's sending-method relay names `deposit` (deliverable): admitted -> S8 red
  cancel-late     S10's b is delivered before it is cancelled: nothing to withdraw  -> S10 red
  cancel-early    S11's fresh cancel runs BEFORE m is delivered: it withdraws        -> S11 red
  stop-cancels    S12 yields `cancelOf` where it should `stopOf`: m is withdrawn     -> S12 red
  sender-controls S13's "other object" is poster itself, the sender: admitted        -> S13 red
  bounce-twice    S14 relays bounce2 (two onward sends): over its allowance       -> S14 red
  roomy-allowance S15's allowance covers two sends + deposits: bounce2 fits                        -> S15 red
  fan-four        S16 relays bounce4 (four onward sends): within the fan-out      -> S16 red
  short-chain     S17's chain starts with 3 PRICE: it ends by allowance, at depth 1 -> S17 red
  cancel-bare     S18's message carries no allowance (a deposit): refund PRICE     -> S18 red
Every plant is ASSERTED APPLIED before its row is judged (group P-plant-applied, which must stay PASS): a plant
that did not take hold reads as `blind`, never as red.
The kernel's control checks are planted by building the Host from a planted tree (authority check removed,
cancel refunds nothing, stop does not unwatch, a cancel of a decided slot retires it): S10-S13 red together.
The kernel check itself is planted by building the Host with `ObjectiveCall.Mail.send` not consulting
`deliverable` (the pre-row-F kernel): S8's relay then installs, escrows PRICE, and its delivery decides `broken`
("a delivered message sends") -- S8 red, and S9's bounce is forwarded instead of refunded -- S9 red.
ROOT/transcript holds every command's exact output; ROOT/results.json every row; ROOT/groups.tsv one line per
journey row. Exit 1 on any red row.
"""
import argparse, json, pathlib, sys

HERE = pathlib.Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
from activity_world import World, PERMIT_ALL, TICKS, PRICE, nat, record, eq, any_of, cap  # noqa: E402


def label(text):
    return {'tag': 'label', 'value': text}

PLANTS = {'vault-open': {'S4-failed'}, 'dir-empty': {'S5-forward', 'S9-resolved'}, 'roomy-postage': {'S6-broken'},
          'relay-deposit': {'S8-interface'}, 'cancel-late': {'S10-cancel'}, 'cancel-early': {'S11-pole'},
          'stop-cancels': {'S12-stop'}, 'sender-controls': {'S13-who'}, 'bounce-twice': {'S14-continue'},
          'roomy-allowance': {'S15-exceed'}, 'fan-four': {'S16-fanout'}, 'short-chain': {'S17-depth'},
          'cancel-bare': {'S18-cancel'}}
ap = argparse.ArgumentParser()
ap.add_argument('--bin', required=True)
ap.add_argument('--root', required=True)
ap.add_argument('--plant', default='')
a = ap.parse_args()
plants = {p for p in a.plant.split(',') if p}
if plants - set(PLANTS):
    raise SystemExit(f'unknown plant {sorted(plants - set(PLANTS))}; known: {sorted(PLANTS)}')

NAMES = ['poster', 'counter', 'fan', 'sink', 'vault', 'dir', 'nodir', 'relayer', 'hopper', 'bare']
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
        w.create(f'create-{name}', w.sponsor, name, VAULT if name == 'vault' else PERMIT_ALL, 'installed',
                 seed=record(total=nat(starts[name])))

    def total(name, label):
        return w.total_of(w.state(name, label))

    def invoke(label, name, method, args, expect, detail=None, postage=TICKS, allowance=None):
        body = {'kind': 'invoke', 'object': O[name], 'objectCapability': w.objects[name]['capability'],
                'method': method, 'args': args, 'envelope': cap(TICKS), 'account': w.SPONSOR_ACCOUNT,
                'accountCapability': w.SPONSOR_SPEND}
        if postage is not None:
            body['postage'] = cap(postage)
        if allowance is not None:
            body['allowance'] = str(allowance)
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
                'retired': w.cell_of(v, cell).get('kind') == 'retired',
                'messages': held['messages'], 'purse': w.balance(v, cell),
                'sponsor': w.balance(v, w.SPONSOR_ACCOUNT), 'second': w.balance(v, w.SECOND),
                'collector': w.balance(v, w.COLLECTOR)}

    def slot(name, label):
        v = w.view(label, {'slots': [str(name)]})
        return w.cell_of(v, v['slots'][0]['cell']).get('slot') or {}

    def decision(s):
        phase = s.get('phase')
        return phase.get('decision', {}) if isinstance(phase, dict) else {}

    def queued_message(view, mid):
        found = [x for x in view['messages'] if x['id'] == str(mid)]
        return found[0] if found else {}

    def dep(message):
        """A queued message's storage deposit (its escrow is postage + allowance + deposit)."""
        return int((message or {}).get('deposit', '0'))

    def queued_dep(s, i=0):
        q = s.get('queued') or []
        return dep(q[i]) if len(q) > i else 0

    def post(target, amount):
        return record(target=nat(O[target]), amount=nat(amount))

    with w.group('S1-send'):
        before = inbox('poster', 'counter', 's1-before')
        out = invoke('s1-post', 'poster', 'post', post('counter', 4), 'installed')
        m1 = reported(out)
        after = inbox('poster', 'counter', 's1-after')
        s1 = slot(m1, 's1-slot')
        w.check('s1-queued-one', after['ids'] == [str(m1)] and after['head'] == 0, after['ids'])
        w.check('s1-slot-open-delivery', s1.get('phase') == 'open'
                and s1.get('decider') == {'delivery': str(m1), 'sender': str(O['poster'])}, s1)
        d1 = dep(after['messages'][0]) if after['messages'] else 0
        w.check('s1-postage-escrowed', d1 > 0 and after['purse'] == PRICE + d1
                and before['sponsor'] - after['sponsor'] == 2 * PRICE + d1,
                {'purse': after['purse'], 'deposit': d1, 'paid': before['sponsor'] - after['sponsor']})
        w.check('s1-not-yet-delivered', total('counter', 's1-counter') == 0, None)

    with w.group('S2-deliver'):
        before = inbox('poster', 'counter', 's2-before')
        out = deliver('s2-deliver', 'poster', 'counter', m1, 'installed')
        after = inbox('poster', 'counter', 's2-after')
        s2 = slot(m1, 's2-slot')
        w.check('s2-counter-4', total('counter', 's2-counter') == 4, None)
        w.check('s2-popped', after['ids'] == [] and after['retired'], after)
        w.check('s2-deposit-refunded', after['sponsor'] - before['sponsor'] == d1,
                {'refund': after['sponsor'] - before['sponsor'], 'deposit': d1})
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
        w.check('s4-popped', after['ids'] == [] and after['retired'], after['ids'])
        w.check('s4-no-write', total('vault', 's4-vault') == 0, None)
        d4 = dep(before['messages'][0]) if before['messages'] else 0
        w.check('s4-paid-from-purse', after['purse'] == 0 and after['collector'] - before['collector'] == PRICE
                and after['sponsor'] - before['sponsor'] == d4, after)

    with w.group('S5-forward'):
        c0 = total('counter', 's5-c0')
        out = invoke('s5-pipe', 'poster', 'pipe', record(via=nat(O['dir']), amount=nat(5)), 'installed')
        look = reported(out)
        held = inbox('poster', 'dir', 's5-held')
        sl = slot(look, 's5-slot-open')
        dL, dQ = dep(queued_message(held, look)), queued_dep(sl)
        w.check('s5-queued-on-slot', len(sl.get('queued', [])) == 1 and held['purse'] == 2 * PRICE + dL + dQ,
                {'queued': len(sl.get('queued', [])), 'purse': held['purse'], 'deposits': (dL, dQ)})
        target_before = inbox('poster', 'counter', 's5-target-before')
        deliver('s5-deliver-lookup', 'poster', 'dir', look, 'installed')
        sl = slot(look, 's5-slot-decided')
        moved = inbox('poster', 'counter', 's5-target-after')
        source = inbox('poster', 'dir', 's5-source-after')
        w.check('s5-reply-ref', decision(sl) == {'kind': 'reply', 'value': {'tag': 'variant', 'label': 'ref',
                                                                           'payload': nat(O['counter'])}}, sl)
        w.check('s5-slot-emptied', sl.get('queued') == [], sl.get('queued'))
        forwarded = [i for i in moved['ids'] if i not in target_before['ids']]
        w.check('s5-forwarded', len(forwarded) == 1 and moved['purse'] - target_before['purse'] == PRICE + dQ
                and source['purse'] == 0 and source['retired'],
                {'forwarded': forwarded, 'purse': moved['purse'], 'source': source['purse']})
        fslot = slot(forwarded[0], 's5-fslot') if forwarded else {}
        w.check('s5-forward-slot-open', fslot.get('decider') == {'delivery': forwarded[0] if forwarded else None,
                                                                 'sender': str(O['poster'])}
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
        dL, dQ = dep(queued_message(before, look)), queued_dep(slot(look, 's6-slot-open'))
        deliver('s6-deliver', 'poster', 'dir', look, 'installed')
        after = inbox('poster', 'dir', 's6-after')
        d6 = decision(slot(look, 's6-slot'))
        w.check('s6-slot-broken', d6.get('kind') == 'broken', d6)
        w.check('s6-refunded', after['purse'] == 0 and after['sponsor'] - before['sponsor'] == 1 + small + dL + dQ
                and after['collector'] - before['collector'] == 1 + small,
                {'refund': after['sponsor'] - before['sponsor'], 'fee': after['collector'] - before['collector']})
        w.check('s6-counter-kept', total('counter', 's6-c1') == c0, None)
        out = invoke('s6-pipe-none', 'poster', 'pipe', record(via=nat(O['nodir']), amount=nat(7)), 'installed')
        look = reported(out)
        before = inbox('poster', 'nodir', 's6n-before')
        dL, dQ = dep(queued_message(before, look)), queued_dep(slot(look, 's6n-slot-open'))
        deliver('s6-deliver-none', 'poster', 'nodir', look, 'installed')
        after = inbox('poster', 'nodir', 's6n-after')
        dn = decision(slot(look, 's6n-slot'))
        w.check('s6-none-not-a-reference', dn.get('kind') == 'reply'
                and after['sponsor'] - before['sponsor'] == PRICE + dL + dQ
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

    def relay(target, method, amount):
        return record(target=nat(O[target]), method=label(method), amount=nat(amount))

    with w.group('S8-interface'):
        sending = 'deposit' if 'relay-deposit' in plants else 'bounce'
        before = inbox('poster', 'counter', 's8-before')
        c0 = total('counter', 's8-c0')
        invoke('s8-sending-method', 'poster', 'relay', relay('counter', sending, 1), 'refused',
               ['notDeliverable', str(O['counter']), 'bounce', 'Plan admits send'])
        invoke('s8-unknown-method', 'poster', 'relay', relay('counter', 'nothing', 1), 'refused',
               ['notCallable', 'nothing'])
        invoke('s8-ill-typed-args', 'poster', 'relay', relay('counter', 'post', 1), 'refused', 'argumentType')
        after = inbox('poster', 'counter', 's8-after')
        w.check('s8-nothing-escrowed', after['ids'] == before['ids'] and after['purse'] == before['purse']
                and after['sponsor'] == before['sponsor'] and after['collector'] == before['collector'],
                {'ids': (before['ids'], after['ids']), 'purse': (before['purse'], after['purse']),
                 'sponsor': after['sponsor'] - before['sponsor']})
        out = invoke('s8-deliverable-control', 'poster', 'relay', relay('counter', 'deposit', 1), 'installed')
        m8 = reported(out)
        if m8 is not None:
            deliver('s8-deliver-control', 'poster', 'counter', m8, 'installed')
        w.check('s8-control-delivered', total('counter', 's8-c1') == c0 + 1,
                None)

    with w.group('S9-resolved'):
        c0 = total('counter', 's9-c0')
        target_before = inbox('poster', 'counter', 's9-target-before')
        out = invoke('s9-relay-via', 'poster', 'relayVia', relay('dir', 'bounce', 3), 'installed')
        look = reported(out)
        held = inbox('poster', 'dir', 's9-held')
        sl = slot(look, 's9-slot-open')
        dL, dQ = dep(queued_message(held, look)), queued_dep(sl)
        w.check('s9-queued-on-slot', len(sl.get('queued', [])) == 1 and held['purse'] == 2 * PRICE + dL + dQ,
                {'queued': len(sl.get('queued', [])), 'purse': held['purse'], 'deposits': (dL, dQ)})
        deliver('s9-deliver-lookup', 'poster', 'dir', look, 'installed')
        sl = slot(look, 's9-slot-decided')
        target_after = inbox('poster', 'counter', 's9-target-after')
        source = inbox('poster', 'dir', 's9-source-after')
        w.check('s9-reply-ref', decision(sl) == {'kind': 'reply', 'value': {'tag': 'variant', 'label': 'ref',
                                                                           'payload': nat(O['counter'])}}, sl)
        w.check('s9-not-forwarded', target_after['ids'] == target_before['ids']
                and target_after['purse'] == target_before['purse'], target_after['ids'])
        w.check('s9-refunded', source['purse'] == 0 and source['sponsor'] - held['sponsor'] == PRICE + dL + dQ
                and source['collector'] - held['collector'] == PRICE,
                {'purse': source['purse'], 'refund': source['sponsor'] - held['sponsor'],
                 'fee': source['collector'] - held['collector']})
        w.check('s9-counter-kept', total('counter', 's9-c1') == c0, None)

    applied = {}  # plant -> did it take hold (judged in group P-plant-applied, after the rows)

    def slot_cell(name, label):
        v = w.view(label, {'slots': [str(name)]})
        return w.cell_of(v, v['slots'][0]['cell'])

    def control(label, by, method, slot_id, expect, detail=None):
        return invoke(label, by, method, nat(int(slot_id)), expect, detail)

    def paid(before, after):
        """(refund to the sponsor, fee to the collector) between two inbox views of one turn."""
        fee = after['collector'] - before['collector']
        return after['sponsor'] - before['sponsor'] + fee, fee

    with w.group('S10-cancel'):
        c0 = total('counter', 's10-c0')
        ma = reported(invoke('s10-post-a', 'poster', 'post', post('counter', 1), 'installed'))
        mb = reported(invoke('s10-post-b', 'poster', 'post', post('counter', 2), 'installed'))
        mc = reported(invoke('s10-post-c', 'poster', 'post', post('counter', 3), 'installed'))
        if 'cancel-late' in plants:  # the plant: b is delivered first (a, then b, leave the head)
            deliver('s10-plant-deliver-a', 'poster', 'counter', ma, 'installed')
            deliver('s10-plant-deliver-b', 'poster', 'counter', mb, 'installed')
            applied['cancel-late'] = decision(slot(mb, 's10-plant-b')).get('kind') == 'reply'
        before = inbox('poster', 'counter', 's10-before')
        out = control('s10-cancel-b', 'poster', 'cancelOf', mb, 'installed')
        after = inbox('poster', 'counter', 's10-after')
        refund, fee = paid(before, after)
        db = dep(queued_message(before, mb))
        w.check('s10-acked', reported(out) == mb, reported(out))
        w.check('s10-withdrawn-fifo-kept', after['ids'] == [i for i in before['ids'] if i != str(mb)]
                and str(mb) in before['ids'] and after['head'] == before['head'], (before['ids'], after['ids']))
        w.check('s10-refund-exact', db > 0 and refund == PRICE + db and before['purse'] - after['purse'] == PRICE + db
                and fee == PRICE,
                {'refund': refund, 'fee': fee, 'purse': (before['purse'], after['purse'])})
        sb = slot(mb, 's10-slot-b')
        w.check('s10-slot-cancelled', decision(sb) == {'kind': 'cancelled'} and sb.get('queued') == [], sb)
        deliver('s10-deliver-cancelled-refused', 'poster', 'counter', mb, 'refused')
        if 'cancel-late' not in plants:
            deliver('s10-deliver-a', 'poster', 'counter', ma, 'installed')
        deliver('s10-deliver-c', 'poster', 'counter', mc, 'installed')
        w.check('s10-others-delivered', total('counter', 's10-c1') == c0 + 1 + 3, total('counter', 's10-c1x'))
        look = reported(invoke('s10-pipe', 'poster', 'pipe', record(via=nat(O['dir']), amount=nat(5)), 'installed'))
        held = inbox('poster', 'dir', 's10-pipe-held')
        dL, dQ = dep(queued_message(held, look)), queued_dep(slot(look, 's10-slot-open'))
        control('s10-cancel-lookup', 'poster', 'cancelOf', look, 'installed')
        gone = inbox('poster', 'dir', 's10-pipe-gone')
        refund, fee = paid(held, gone)
        w.check('s10-pipelined-refunded', held['purse'] == 2 * PRICE + dL + dQ and gone['purse'] == 0
                and refund == 2 * PRICE + dL + dQ and gone['ids'] == [] and gone['retired'], {'refund': refund, 'purse': (held['purse'], gone['purse']), 'ids': gone['ids']})
        w.check('s10-lookup-cancelled', decision(slot(look, 's10-slot-look')) == {'kind': 'cancelled'}, None)
        deliver('s10-deliver-lookup-refused', 'poster', 'dir', look, 'refused')

    with w.group('S11-pole'):
        m = reported(invoke('s11-post', 'poster', 'post', post('counter', 6), 'installed'))
        c0 = total('counter', 's11-c0')
        w.turn('s11-cancel-prepared', w.sponsor, {'kind': 'invoke', 'object': O['poster'],
               'objectCapability': w.objects['poster']['capability'], 'method': 'cancelOf', 'args': nat(m),
               'envelope': cap(TICKS), 'account': w.SPONSOR_ACCOUNT, 'accountCapability': w.SPONSOR_SPEND,
               'postage': cap(TICKS)}, 'prepared', prepare=True)
        if 'cancel-early' in plants:
            applied['cancel-early'] = slot(m, 's11-plant-open').get('phase') == 'open'
        else:
            deliver('s11-deliver-first', 'poster', 'counter', m, 'installed')
        w.resubmit('s11-prepared-cancel-stale', w.attempts / 's11-cancel-prepared' / 'ingress.bin', 'refused',
                   'wrongMessage')
        before = inbox('poster', 'counter', 's11-before')
        out = control('s11-cancel-after', 'poster', 'cancelOf', m, 'installed')
        after = inbox('poster', 'counter', 's11-after')
        refund, fee = paid(before, after)
        w.check('s11-acked', reported(out) == m, reported(out))
        w.check('s11-noop-refunds-nothing', refund == 0 and fee == PRICE and after['purse'] == before['purse']
                and after['ids'] == before['ids'], {'refund': refund, 'fee': fee, 'ids': after['ids']})
        w.check('s11-slot-still-reply', decision(slot(m, 's11-slot')) == {'kind': 'reply', 'value': nat(c0 + 6)}
                and total('counter', 's11-c1') == c0 + 6, None)

    with w.group('S12-stop'):
        c0 = total('counter', 's12-c0')
        look = reported(invoke('s12-pipe', 'poster', 'pipe', record(via=nat(O['dir']), amount=nat(5)), 'installed'))
        held = inbox('poster', 'dir', 's12-held')
        dQ = queued_dep(slot(look, 's12-slot-open'))
        how = 'cancelOf' if 'stop-cancels' in plants else 'stopOf'
        out = control('s12-stop', 'poster', how, look, 'installed')
        stopped = inbox('poster', 'dir', 's12-stopped')
        if 'stop-cancels' in plants:
            applied['stop-cancels'] = str(look) not in stopped['ids']
        refund, fee = paid(held, stopped)
        sl = slot(look, 's12-slot-stopped')
        w.check('s12-acked', reported(out) == look, reported(out))
        w.check('s12-pipelined-refunded', refund == PRICE + dQ and held['purse'] - stopped['purse'] == PRICE + dQ
                and stopped['ids'] == held['ids'], {'refund': refund, 'purse': (held['purse'], stopped['purse'])})
        w.check('s12-open-unwatched', sl.get('phase') == 'open' and sl.get('watched') is False
                and sl.get('queued') == [], sl)
        deliver('s12-still-delivered', 'poster', 'dir', look, 'installed')
        done = inbox('poster', 'dir', 's12-done')
        w.check('s12-popped-paid', done['ids'] == [] and done['purse'] == 0
                and done['collector'] - stopped['collector'] == PRICE, done)
        w.check('s12-delivery-retires', slot_cell(look, 's12-cell').get('kind') == 'retired',
                slot_cell(look, 's12-cell-x'))
        w.check('s12-counter-kept', total('counter', 's12-c1') == c0, None)
        control('s12-stop-decided', 'poster', 'stopOf', m1, 'installed')
        w.check('s12-decided-retired', slot_cell(m1, 's12-m1-cell').get('kind') == 'retired',
                slot_cell(m1, 's12-m1-cell-x'))

    with w.group('S13-who'):
        m = reported(invoke('s13-post', 'poster', 'post', post('counter', 1), 'installed'))
        look = reported(invoke('s13-pipe', 'poster', 'pipe', record(via=nat(O['dir']), amount=nat(1)), 'installed'))
        control('s13-stop-look', 'poster', 'stopOf', look, 'installed')
        before = inbox('poster', 'counter', 's13-before')
        other = 'poster' if 'sender-controls' in plants else 'counter'
        if 'sender-controls' in plants:
            applied['sender-controls'] = other == 'poster'
        control('s13-other-cancel', other, 'cancelOf', m, 'refused', ['notSender', str(m), str(O['counter'])])
        control('s13-other-stop', other, 'stopOf', m, 'refused', ['notSender', str(m), str(O['counter'])])
        control('s13-no-such-slot', 'poster', 'cancelOf', 987654321, 'refused', ['notControllable', '987654321'])
        invoke('s13-chase-stopped', 'poster', 'chase', record(target=nat(look), amount=nat(1)), 'refused',
               ['notPipelinable', str(look)])
        after = inbox('poster', 'counter', 's13-after')
        w.check('s13-nothing-commits', after['ids'] == before['ids'] and after['purse'] == before['purse']
                and after['sponsor'] == before['sponsor'], {'ids': (before['ids'], after['ids'])})


    def relay_a(target, method, amount, allowance):
        return record(target=nat(O[target]), method=label(method), amount=nat(amount), allowance=nat(allowance))


    def fresh(before, after):
        return [i for i in after['ids'] if i not in before['ids']]

    with w.group('S14-continue'):
        A = PRICE + PRICE // 2
        how = 'bounce2' if 'bounce-twice' in plants else 'bounce'
        c0 = total('counter', 's14-c0')
        start = inbox('relayer', 'counter', 's14-start')
        cc0 = inbox('counter', 'counter', 's14-cc0')
        m = reported(invoke('s14-relay', 'relayer', 'relayA', relay_a('counter', how, int(O['counter']), A),
                            'installed', allowance=A))
        held = inbox('relayer', 'counter', 's14-held')
        msg = queued_message(held, m)
        if 'bounce-twice' in plants:
            applied['bounce-twice'] = msg.get('method') == 'bounce2'
        dm = dep(msg)
        w.check('s14-escrowed', msg.get('allowance') == str(A) and msg.get('depth') == '0'
                and held['purse'] - start['purse'] == PRICE + A + dm
                and start['sponsor'] - held['sponsor'] == 2 * PRICE + A + dm,
                {'message': msg, 'purse': held['purse'] - start['purse'], 'paid': start['sponsor'] - held['sponsor']})
        deliver('s14-deliver', 'relayer', 'counter', m, 'installed')
        after = inbox('relayer', 'counter', 's14-after')
        cc1 = inbox('counter', 'counter', 's14-cc1')
        d = decision(slot(m, 's14-slot'))
        onward = fresh(cc0, cc1)
        om = queued_message(cc1, onward[0]) if onward else {}
        w.check('s14-replied', d.get('kind') == 'reply', d)
        do = dep(om)
        w.check('s14-onward-queued', len(onward) == 1 and om.get('method') == 'deposit' and om.get('depth') == '1'
                and om.get('allowance') == '0' and cc1['purse'] - cc0['purse'] == PRICE + do,
                {'onward': onward, 'message': om, 'purse': cc1['purse'] - cc0['purse']})
        w.check('s14-remainder-exact', after['sponsor'] - held['sponsor'] == A - PRICE - do + dm
                and after['purse'] == start['purse'] and after['collector'] - held['collector'] == PRICE,
                {'refund': after['sponsor'] - held['sponsor'], 'purse': (start['purse'], after['purse']),
                 'fee': after['collector'] - held['collector']})
        if onward:
            deliver('s14-deliver-onward', 'counter', 'counter', onward[0], 'installed')
        w.check('s14-onward-delivered', total('counter', 's14-c1') == c0 + int(O['counter'])
                and inbox('counter', 'counter', 's14-cc2')['purse'] == cc0['purse'], None)

    with w.group('S15-exceed'):
        A = 2 * (PRICE + PRICE // 4) if 'roomy-allowance' in plants else PRICE + PRICE // 2  # roomy: two onward sends and their deposits
        c0 = total('counter', 's15-c0')
        start = inbox('relayer', 'counter', 's15-start')
        invoke('s15-over-declared', 'relayer', 'relayA', relay_a('counter', 'bounce2', int(O['counter']), A),
               'refused', ['allowanceExceeded', f'{A} {A - 1}'], allowance=A - 1)
        unchanged = inbox('relayer', 'counter', 's15-unchanged')
        w.check('s15-over-declared-nothing', unchanged['ids'] == start['ids'] and unchanged['sponsor'] == start['sponsor'],
                {'ids': unchanged['ids'], 'paid': start['sponsor'] - unchanged['sponsor']})
        cc0 = inbox('counter', 'counter', 's15-cc0')
        m = reported(invoke('s15-relay', 'relayer', 'relayA', relay_a('counter', 'bounce2', int(O['counter']), A),
                            'installed', allowance=A))
        held = inbox('relayer', 'counter', 's15-held')
        dm = dep(queued_message(held, m))
        if 'roomy-allowance' in plants:
            applied['roomy-allowance'] = queued_message(held, m).get('allowance') == str(A)
        deliver('s15-deliver', 'relayer', 'counter', m, 'installed')
        after = inbox('relayer', 'counter', 's15-after')
        cc1 = inbox('counter', 'counter', 's15-cc1')
        d = decision(slot(m, 's15-slot'))
        import re as _re
        over = _re.search(r'allowanceExceeded (\d+) (\d+)', d.get('reason', ''))
        w.check('s15-broken-named', d.get('kind') == 'broken' and over is not None and int(over.group(2)) == A
                and int(over.group(1)) > A and int(over.group(1)) > 2 * PRICE, d)
        w.check('s15-nothing-onward', fresh(cc0, cc1) == [] and cc1['purse'] == cc0['purse'], fresh(cc0, cc1))
        w.check('s15-allowance-refunded', after['sponsor'] - held['sponsor'] == A + dm and after['purse'] == start['purse']
                and after['collector'] - held['collector'] == PRICE,
                {'refund': after['sponsor'] - held['sponsor'], 'fee': after['collector'] - held['collector']})
        w.check('s15-counter-kept', total('counter', 's15-c1') == c0, None)

    with w.group('S16-fanout'):
        A = 6 * PRICE
        how = 'bounce4' if 'fan-four' in plants else 'bounce5'
        start = inbox('relayer', 'counter', 's16-start')
        cc0 = inbox('counter', 'counter', 's16-cc0')
        m = reported(invoke('s16-relay', 'relayer', 'relayA', relay_a('counter', how, int(O['counter']), A),
                            'installed', allowance=A))
        held = inbox('relayer', 'counter', 's16-held')
        dm = dep(queued_message(held, m))
        if 'fan-four' in plants:
            applied['fan-four'] = queued_message(held, m).get('method') == 'bounce4'
        deliver('s16-deliver', 'relayer', 'counter', m, 'installed')
        after = inbox('relayer', 'counter', 's16-after')
        cc1 = inbox('counter', 'counter', 's16-cc1')
        d = decision(slot(m, 's16-slot'))
        w.check('s16-broken-fanout', d.get('kind') == 'broken' and 'fanOut 4' in d.get('reason', ''), d)
        w.check('s16-nothing-onward', fresh(cc0, cc1) == [], fresh(cc0, cc1))
        w.check('s16-allowance-refunded', after['sponsor'] - held['sponsor'] == A + dm and after['purse'] == start['purse'],
                {'refund': after['sponsor'] - held['sponsor']})

    with w.group('S17-depth'):
        A = 3 * PRICE if 'short-chain' in plants else 10 * PRICE
        R = PRICE // 4  # each hop's reserve for its onward message's storage deposit
        h0 = total('hopper', 's17-h0')
        start = inbox('relayer', 'hopper', 's17-start')
        hh0 = inbox('hopper', 'hopper', 's17-hh0')
        m0 = reported(invoke('s17-hop', 'relayer', 'hop', record(target=nat(O['hopper']), price=nat(PRICE),
                                                                   allowance=nat(A), reserve=nat(R)), 'installed',
                             allowance=A - PRICE))
        held = inbox('relayer', 'hopper', 's17-held')
        if 'short-chain' in plants:
            applied['short-chain'] = queued_message(held, m0).get('allowance') == str(A - PRICE - R)
        deliver('s17-deliver-0', 'relayer', 'hopper', m0, 'installed')
        hh1 = inbox('hopper', 'hopper', 's17-hh1')
        n1 = fresh(hh0, hh1)
        m1 = queued_message(hh1, n1[0]) if n1 else {}
        if n1:
            deliver('s17-deliver-1', 'hopper', 'hopper', n1[0], 'installed')
        hh2 = inbox('hopper', 'hopper', 's17-hh2')
        n2 = fresh(hh1, hh2)
        n2 = [i for i in n2 if not n1 or i != n1[0]]
        m2 = queued_message(hh2, n2[0]) if n2 else {}
        w.check('s17-one-hop-deeper', m1.get('depth') == '1' and m2.get('depth') == '2'
                and m2.get('allowance') == str(A - 3 * (PRICE + R)), {'m1': m1, 'm2': m2})
        if n2:
            deliver('s17-deliver-2', 'hopper', 'hopper', n2[0], 'installed')
        hh3 = inbox('hopper', 'hopper', 's17-hh3')
        d2 = decision(slot(n2[0], 's17-slot-2')) if n2 else {}
        w.check('s17-depth-refused', d2.get('kind') == 'broken' and 'continuationDepth 3' in d2.get('reason', ''), d2)
        w.check('s17-depth-refund', bool(n2) and hh3['sponsor'] - hh2['sponsor'] == A - 3 * (PRICE + R) + dep(m2)
                and hh3['ids'] == [] and hh3['purse'] == hh0['purse'],
                {'refund': hh3['sponsor'] - hh2['sponsor'], 'ids': hh3['ids'], 'purse': hh3['purse']})
        w.check('s17-two-delivered', total('hopper', 's17-h1') == h0 + 2, total('hopper', 's17-h1x'))

    with w.group('S18-cancel'):
        bare = 'cancel-bare' in plants
        A = 0 if bare else PRICE + PRICE // 2
        m = reported(invoke('s18-relay', 'relayer', 'relayA',
                            relay_a('counter', 'deposit' if bare else 'bounce', int(O['counter']), A), 'installed',
                            allowance=A))
        before = inbox('relayer', 'counter', 's18-before')
        dm = dep(queued_message(before, m))
        if bare:
            applied['cancel-bare'] = queued_message(before, m).get('allowance') == '0'
        control('s18-cancel', 'relayer', 'cancelOf', m, 'installed')
        after = inbox('relayer', 'counter', 's18-after')
        refund, fee = paid(before, after)
        w.check('s18-refund-postage-and-allowance', refund == 2 * PRICE + PRICE // 2 + dm
                and before['purse'] - after['purse'] == 2 * PRICE + PRICE // 2 + dm and fee == PRICE,
                {'refund': refund, 'fee': fee, 'purse': (before['purse'], after['purse'])})
        w.check('s18-slot-cancelled', decision(slot(m, 's18-slot')) == {'kind': 'cancelled'}
                and after['ids'] == [i for i in before['ids'] if i != str(m)], None)

    if plants:
        with w.group('P-plant-applied'):
            for p in sorted(plants):
                if p in ('cancel-late', 'cancel-early', 'stop-cancels', 'sender-controls', 'bounce-twice',
                         'roomy-allowance', 'fan-four', 'short-chain', 'cancel-bare'):
                    w.check(f'plant-{p}-applied', applied.get(p) is True, applied.get(p))
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
