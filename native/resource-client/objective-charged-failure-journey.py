#!/usr/bin/env python3
"""Signature before decision, and the charged failure (GPT-6 row E), on a scratch NATIVE world.

  objective-charged-failure-journey.py --bin DIR --root NEW_DIR [--pad 3000] [--repeat 5] [--timing-only]

A signed ingress carries the outcome its signer signed; the receiver checks the authority, the capabilities
over that claim, the payer's funds and the signature BEFORE it decides the turn. A paying turn (a birth, an
invocation) that passed all of that and then fails after the validator's work COMMITS a charged failure: the
public price of its declared envelope, payer to collector, and nothing else. A malformed, forged or unfunded
request is refused before anything is decided, and nothing is written or charged.

Rows (ROOT/results.json, ROOT/groups.tsv; timings ROOT/timings.tsv):
  fees           two packages of different sizes: a birth's fee differs by exactly the tariff on the quote
                 difference (the front end is CHARGED, not only refused)
  charged        a birth whose run exhausts its declared ticks: confirmed, the sponsor pays exactly the
                 envelope's price to the collector, no activity record, no declared state
  charged-replay an invocation whose run exhausts: its reply is lost; the exact ingress and a newly planned,
                 freshly signed retry both return the original charged disposition/cause and original receipt;
                 neither retry changes any watched balance
  outcome-moved  a birth planned and signed, then the Book moves (another birth), then submitted: its
                 outcome is not the signed one, so it is a charged failure (the price, nothing else)
  malformed      bytes that are not an ingress: refused `malformedIngress`, no balance moves
  forged         a valid ingress with one signature byte flipped: refused at the signature, no balance moves
  unfunded       a birth whose deposit exceeds the payer's balance: refused `unfunded` before it runs
  cost           op 212 alone (`resubmit`): a forged ingress of a birth of the padded package against a valid
                 ingress of the same birth that runs and is charged. --timing-only runs this row alone (it
                 runs on binaries before this change too, where the forged ingress was decided first)
"""
import argparse, json, os, pathlib, re, sys, time

HERE = pathlib.Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import activity_world as AW  # noqa: E402
from activity_world import World, cap, price, record, variant, nat, op_id  # noqa: E402

ap = argparse.ArgumentParser()
ap.add_argument('--bin', required=True)
ap.add_argument('--root', required=True)
ap.add_argument('--pad', type=int, default=3000)
ap.add_argument('--repeat', type=int, default=5)
ap.add_argument('--timing-only', action='store_true')
a = ap.parse_args()
os.environ['NEWPARTICIPANT_OWNER_BUDGET'] = '4000000'  # the padded package's publication is ~200 KB
w = World(a.bin, a.root, HERE.parent.parent)
timings = []


def balances(label):
    v = w.watched(label)
    return {k: w.balance(v, acct) for k, acct in
            [('sponsor', w.SPONSOR_ACCOUNT), ('collector', w.COLLECTOR), ('second', w.SECOND)]}, v.get('total')


def birth_body(name, pin, deposit, ticks, front, init=None):
    o = w.objects[name]
    env = dict(cap(ticks), replayBytes=str(front[0]), coreBytes=str(front[1]))
    return {'kind': 'birth', 'object': o['object'], 'objectCapability': o['capability'],
            'account': w.SPONSOR_ACCOUNT, 'accountCapability': w.SPONSOR_SPEND, 'pin': pin,
            'input': record(init=init or variant('set', nat(0)), decider=nat(int(w.SECOND))),
            'envelope': env, 'resume': env, 'timeout': env, 'deposit': str(deposit)}


def record_kind(name, transaction):
    o = w.objects[name]['object']
    v = w.view(f'record-{transaction}', {'births': [{'object': o, 'transaction': transaction}], 'objects': [o]})
    rec = w.cell_of(v, v['births'][0]['record'])
    st = w.cell_of(v, v['objects'][0]['stateCell'])
    return rec.get('kind'), st.get('kind')


def flipped(path, label):
    bytes_ = bytearray(pathlib.Path(path).read_bytes())
    bytes_[-1] ^= 0x01  # the last byte of the signed envelope: the signature
    out = w.root / f'{label}.ingress'
    out.write_bytes(bytes(bytes_))
    return out


try:
    w.bring_up(['tally', 'padded', 'quiet', 'mover', 'counter'], sponsor_balance='100000000000')
    tally_src = (w.repo / 'world/activity/Tally.obend').read_text()
    padded = w.root / 'Padded.obend'
    padded.write_text(tally_src.rstrip('\n') + '\n' +
                      ''.join(f'record Pad{i}:\n  pad{i}: Nat\n' for i in range(a.pad)))
    TALLY = {'name': 'Tally', 'sourcePath': str(w.repo / 'world/activity/Tally.obend'), 'imports': []}
    PADDED = {'name': 'Tally', 'sourcePath': str(padded), 'imports': []}
    w.PIN, ARTIFACT = w.publication('publication', [TALLY], '0', 'tally')
    BIG, BIG_ARTIFACT = w.publication('publication-padded', [PADDED], '0', 'tally')
    CALLS = {'name': 'Calls', 'sourcePath': str(w.repo / 'world/call/Calls.obend'), 'imports': []}
    CALL_PIN, CALL_ARTIFACT = w.publication('publication-calls', [CALLS], '0', 'deposit')
    for label, art in [('publish', ARTIFACT), ('publish-padded', BIG_ARTIFACT),
                       ('publish-calls', CALL_ARTIFACT)]:
        w.turn(label, w.sponsor, dict(art, kind='publish', payer=w.SPONSOR_ACCOUNT,
                                      payerCapability=w.SPONSOR_SPEND), 'installed')
    for name, pin in [('tally', w.PIN), ('padded', BIG), ('quiet', w.PIN), ('mover', w.PIN)]:
        w.create(f'create-{name}', w.sponsor, name, AW.PERMIT_ALL, 'installed', pin=pin)
    w.create('create-counter', w.sponsor, 'counter', AW.PERMIT_ALL, 'installed', pin=CALL_PIN,
             seed=record(total=nat(0)))
    quotes = w.view('quotes', {'pins': [str(w.PIN), str(BIG)]})['pins']
    SMALL = (int(quotes[0]['frontEnd']['replayBytes']), int(quotes[0]['frontEnd']['coreBytes']))
    LARGE = (int(quotes[1]['frontEnd']['replayBytes']), int(quotes[1]['frontEnd']['coreBytes']))
    TICKS = AW.TICKS

    def deposit(front):
        return 8 * price(dict(cap(TICKS), replayBytes=str(front[0]), coreBytes=str(front[1])))

    if not a.timing_only:
        with w.group('fees'):
            b0, _ = balances('fees-0')
            w.turn('fee-tally', w.sponsor, birth_body('tally', w.PIN, deposit(SMALL), TICKS, SMALL), 'installed')
            b1, _ = balances('fees-1')
            w.turn('fee-padded', w.sponsor, birth_body('padded', BIG, deposit(LARGE), TICKS, LARGE), 'installed')
            b2, _ = balances('fees-2')
            fee_small = b1['collector'] - b0['collector']
            fee_large = b2['collector'] - b1['collector']
            rates = (int(AW.TARIFF['replayBytes']), int(AW.TARIFF['coreBytes']))
            w.check('fees-differ-by-the-tariff-on-the-quote',
                    fee_large - fee_small == rates[0] * (LARGE[0] - SMALL[0]) + rates[1] * (LARGE[1] - SMALL[1])
                    and fee_small == price(dict(cap(TICKS), replayBytes=str(SMALL[0]), coreBytes=str(SMALL[1]))),
                    {'feeTally': fee_small, 'feePadded': fee_large, 'quotes': [SMALL, LARGE], 'rates': rates})

        with w.group('charged'):
            b0, t0 = balances('charged-0')
            body = birth_body('quiet', w.PIN, deposit(SMALL), 1, SMALL)
            out = w.turn('birth-exhausts-charged', w.sponsor, body, 'charged', 'exhausted')
            b1, t1 = balances('charged-1')
            fee = price(body['envelope'])
            kinds = record_kind('quiet', out.get('transaction'))
            w.check('charged-exactly-the-envelope-price', b0['sponsor'] - b1['sponsor'] == fee
                    and b1['collector'] - b0['collector'] == fee and t0 == t1,
                    {'fee': fee, 'sponsor': [b0['sponsor'], b1['sponsor']], 'collector': [b0['collector'], b1['collector']],
                     'total': [t0, t1]})
            w.check('charged-rolls-back-the-business', kinds == ('absent', 'absent'), {'record/state': kinds})

        with w.group('charged-replay'):
            # The first charged reply is lost. The client first repeats the exact signed ingress, then replans and
            # signs the SAME invocation operation id at the post-failure snapshot. Both are receipt-only replay.
            op = op_id()
            body = {'kind': 'invoke', 'object': w.objects['counter']['object'],
                    'objectCapability': w.objects['counter']['capability'], 'method': 'deposit', 'args': nat(1),
                    'envelope': cap(1), 'account': w.SPONSOR_ACCOUNT,
                    'accountCapability': w.SPONSOR_SPEND, 'opId': op}
            first = w.turn('charged-replay-first', w.sponsor, body, 'charged', 'exhausted')
            b1, _ = balances('charged-replay-after-first')
            exact = w.resubmit('charged-replay-exact', first['ingress'], 'replayed')
            b2, _ = balances('charged-replay-after-exact')
            fresh = w.judge('charged-replay-fresh-signature',
                            w.submit('charged-replay-fresh-signature', w.sponsor, body), 'replayed', None)
            b3, _ = balances('charged-replay-after-fresh')
            answers = (first, exact, fresh)
            w.check('charged-replay-original-disposition-and-cause',
                    all(r.get('disposition') == 'charged' and r.get('cause') == first.get('cause')
                        and r.get('transactionId') == first.get('transactionId')
                        and r.get('eventId') == first.get('eventId') for r in answers)
                    and 'exhausted' in str(first.get('cause')),
                    {'first': {k: first.get(k) for k in ('disposition', 'cause', 'transactionId', 'eventId')},
                     'exact': {k: exact.get(k) for k in ('disposition', 'cause', 'transactionId', 'eventId')},
                     'fresh': {k: fresh.get(k) for k in ('disposition', 'cause', 'transactionId', 'eventId')}})
            w.check('charged-replay-does-not-recharge', b1 == b2 == b3,
                    {'afterFirst': b1, 'afterExact': b2, 'afterFresh': b3})

        with w.group('outcome-moved'):
            body = birth_body('mover', w.PIN, deposit(SMALL), TICKS, SMALL)
            prepared = w.turn('mover-planned', w.sponsor, body, 'prepared', prepare=True)
            w.turn('book-moves', w.sponsor, birth_body('tally', w.PIN, deposit(SMALL), TICKS, SMALL,
                                                       init=variant('keep', record())), 'installed')
            b0, _ = balances('moved-0')
            w.resubmit('mover-submitted-stale', prepared['ingress'], 'installed')
            b1, _ = balances('moved-1')
            fee = price(body['envelope'])
            kinds = record_kind('mover', prepared.get('transaction'))
            w.check('outcome-moved-is-charged', b0['sponsor'] - b1['sponsor'] == fee
                    and b1['collector'] - b0['collector'] == fee and kinds == ('absent', 'absent'),
                    {'fee': fee, 'sponsor': [b0['sponsor'], b1['sponsor']], 'record/state': kinds})

        with w.group('malformed'):
            junk = w.root / 'junk.ingress'
            junk.write_bytes(b'DREGG/OBJECTIVE/ACTIVITY/SIGNED/v2' + bytes(40))
            b0, _ = balances('malformed-0')
            w.resubmit('malformed-refused', junk, 'refused', 'malformedIngress')
            b1, _ = balances('malformed-1')
            w.check('malformed-no-charge', b0 == b1, {'before': b0, 'after': b1})

        with w.group('forged'):
            body = birth_body('quiet', w.PIN, deposit(SMALL), TICKS, SMALL)
            prepared = w.turn('forged-planned', w.sponsor, body, 'prepared', prepare=True)
            b0, _ = balances('forged-0')
            w.resubmit('forged-refused', flipped(prepared['ingress'], 'forged'), 'refused', 'signature')
            b1, _ = balances('forged-1')
            w.check('forged-no-charge', b0 == b1 and record_kind('quiet', prepared.get('transaction'))[0] == 'absent',
                    {'before': b0, 'after': b1})

        with w.group('unfunded'):
            b0, _ = balances('unfunded-0')
            w.turn('unfunded-refused', w.sponsor, birth_body('quiet', w.PIN, 10 ** 15, TICKS, SMALL), 'refused',
                   'unfunded')
            b1, _ = balances('unfunded-1')
            w.check('unfunded-no-charge', b0 == b1, {'before': b0, 'after': b1})

    with w.group('cost'):
        # op 212 alone: the same padded-package birth, forged (refused at the signature) against valid and
        # underfunded (decided: replayed, run, refused for its deposit and, after row E, charged).
        for i in range(a.repeat):
            init = variant('keep', record())
            body = birth_body('padded', BIG, 2 * price(dict(cap(TICKS), replayBytes=str(LARGE[0]),
                                                            coreBytes=str(LARGE[1]))) - 1, TICKS, LARGE, init=init)
            prepared = w.turn(f'cost-plan-{i}', w.sponsor, body, 'prepared', prepare=True)
            forged = flipped(prepared['ingress'], f'cost-forged-{i}')
            t = time.monotonic()
            w.resubmit(f'cost-forged-{i}', forged, 'refused', 'signature')
            timings.append((f'forged-refused-{i}', time.monotonic() - t))
            t = time.monotonic()
            r = w.sh(f'cost-valid-{i}', w.mini, 'activity', '--action', 'resubmit', '--workspace', w.sponsor,
                     '--ingress', prepared['ingress'], ok=(0, 1, 2))
            timings.append((f'decided-{i}', time.monotonic() - t))
        forged_t = sorted(t for k, t in timings if k.startswith('forged-refused-'))
        decided_t = sorted(t for k, t in timings if k.startswith('decided-'))
        median = lambda xs: xs[len(xs) // 2]
        w.check('cost-summary', median(forged_t) < median(decided_t),
                {'medianForgedRefusal_s': round(median(forged_t), 3), 'medianDecided_s': round(median(decided_t), 3),
                 'padDeclarations': a.pad, 'quote': LARGE})
    (w.root / 'timings.tsv').write_text(''.join(f'{k}\t{t:.4f}\n' for k, t in timings))
finally:
    w.stop()
sys.exit(w.finish())
