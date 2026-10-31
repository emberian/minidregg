#!/usr/bin/env python3
"""`bend` through the SHELL: author an Objective Bend, run it in the kernel, read the Host's decision.

  bend-journey.py --bin DIR --root NEW_DIR

A member of a scratch NATIVE world (native/resource-client/activity_world.py: a fresh private Store whose
genesis pins the Objective invocation policy) types, into `mini shell --line`, the three bend verbs over
the activity route (Host ops 7 author / 210 plan / 211 assemble / 212 submit / 213 lookup / 214 view):

  bend-publish   `bend publish tally @Tally.obend --entry tally`: the Host's own front end captures and
                 lowers world/activity/Tally.obend, the publish turn is admitted (exit 0, `admitted:`), and
                 the chain holds the package at the artifact's coordinate with the front end's quote
  bend-run       `bend run tally counter`: the object is created pinning Tally and born under a full
                 envelope; the Host's outcome line names height, world root and receipt; the object's
                 declared state read back through the VIEW (not the shell's line) is Tally's `{total: 0}`;
                 the activity's purse holds the deposit the line states, which is BEND_PURSE_PRICES envelope prices as
                 activity_world prices them (the await's pair, one per answer, the storage slack); the account paid at least that
  bend-full-tally the default purse completes a tally: `bend await` names the slot, the decider's `bend answer` and the
                 `bend deliver` resume it (total 7, a new await), other turns pass the deadline, the timed-out
                 `bend deliver` ends it and the purse returns; the run consumed activity_world's tallyRunCost; every
                 receipt's height is on the clock `bend await` and the deadline use
  bend-show      `bend show counter`: the public view agrees with the view this driver reads
  bend-refusal   `bend publish bad @Bad.obend` with a malformed source: refused (exit 3) by the Host's
                 front end, named, nothing submitted (no attempt directory, the judged height unchanged)

Rows: ROOT/results.json, ROOT/groups.tsv; every command's output under ROOT/transcript.
"""
import argparse, json, os, pathlib, re, sys

HERE = pathlib.Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import activity_world as AW  # noqa: E402
from activity_world import World  # noqa: E402

ap = argparse.ArgumentParser()
ap.add_argument('--bin', required=True)
ap.add_argument('--root', required=True)
a = ap.parse_args()
w = World(a.bin, a.root, HERE.parent.parent)
home = w.root / 'shell-home'


def shell(label, line, ok=(0, 1, 2, 3, 4)):
    """One line typed into the member's shell: (exit code, stdout, stderr)."""
    r = w.sh(label, w.mini, 'shell', '--socket', w.sock, '--host', w.host, '--config', w.config,
             '--workspace', w.sponsor, '--home', home, '--line', line, ok=ok)
    return r.returncode, r.stdout.decode(errors='replace').strip(), r.stderr.decode(errors='replace').strip()


try:
    w.bring_up(['counter', 'lost'], sponsor_balance='100000000000', second_balance='10000')
    # The member's account: the sponsor's own, named once (`bend` finds the workspace's one account reference).
    w.sh('account-reference', w.mini, 'workspace', '--action', 'import', '--dir', w.sponsor, '--name', 'account',
         '--kind', 'account', '--target', w.SPONSOR_ACCOUNT, '--observe-capability', w.SPONSOR_SPEND,
         '--operation-capability', w.SPONSOR_SPEND)
    (home / 'requests').mkdir(parents=True, mode=0o700)
    (home / 'requests' / 'Tally.obend').write_bytes((w.repo / 'world/activity/Tally.obend').read_bytes())
    (home / 'requests' / 'Bad.obend').write_text('edition ObjectiveBend 1\nrecord State:\n  total Nat\ndef bad( -> \n')
    for p in [home / 'requests' / 'Tally.obend', home / 'requests' / 'Bad.obend']:
        p.chmod(0o600)
    FRONT_OK = lambda: AW.FRONT['replayBytes'] == AW.TALLY_QUOTE['replayBytes'] and AW.FRONT['coreBytes'] == AW.TALLY_QUOTE['coreBytes']
    height = lambda label: int(w.view(label, {})['height'])

    with w.group('bend-publish'):
        rc, out, err = shell('publish', 'bend publish tally @Tally.obend --entry tally')
        w.check('publish-admitted', rc == 0 and out.startswith('admitted: bend publish tally'), {'rc': rc, 'out': out, 'err': err[-300:]})
        m = re.search(r'height (\d+), world root (\d+), receipt tx (\d+) event (\d+)', out)
        # the line's height is the height the turn was judged at, the view's clock (the view after it is one more)
        w.check('publish-line-names-height-root-receipt', m is not None and int(m.group(1)) > 0, {'line': out})
        w.check('publish-height-is-the-views-clock', m is not None and int(m.group(1)) + 1 == height('height-after-publish'), {'line': out})
        published_at = int(m.group(1)) if m else 0
        publication = json.loads((w.sponsor / 'bend' / 'tally' / 'out' / 'publication.json').read_text())
        pin = publication['artifactId']
        w.published['tally'] = pin
        v = w.view('package', {'pins': [pin]})
        cell = w.cell_of(v, v['pins'][0]['packageCell'])
        w.check('package-on-chain-with-a-front-end-quote', cell.get('kind') == 'package' and cell.get('atCoordinate') is True
                and v['pins'][0].get('frontEnd') is not None, {'cell': cell, 'pin': v['pins'][0]})
        w.learn_front_end()
        BPRICE = AW.price(AW.cap(AW.BEND_TICKS))  # a bend's birth envelope: BEND_TICKS source ticks and the quote
        economy = AW.demo_economy()
        w.check('economy-matches-the-tallys-quote', FRONT_OK() and economy['tallyBirthPrice'] == BPRICE, {'front': AW.FRONT, 'economy': economy, 'birthPrice': BPRICE})

    with w.group('bend-run'):
        w.objects['counter']  # the content resource bring_up made
        start = w.watched('account-before-run')
        rc, out, err = shell('run', 'bend run tally counter')
        run_out = out
        w.check('run-admitted', rc == 0 and out.startswith('admitted: bend run tally on counter'), {'rc': rc, 'out': out, 'err': err[-300:]})
        m = re.search(r'height (\d+), world root (\d+), receipt tx (\d+) event (\d+); state (\{[^}]*\}); purse (\d+); deposit (\d+); '
                      r'account (\d+) -> (\d+) \(charge (\d+)\)', out)
        w.check('run-line-names-the-decision', m is not None, out)
        if m:
            height_n, root, tx, event, state, purse, deposit, was, now, charge = m.groups()
            w.check('run-is-admitted-after-the-publish', int(height_n) > published_at, {'publish': published_at, 'run': height_n})
            w.check('line-state-is-the-tallys', state == '{total=0}', state)
            w.check('deposit-carries-the-default-answers', int(deposit) == AW.BEND_PURSE_PRICES * BPRICE, {'line': deposit, 'world': AW.BEND_PURSE_PRICES * BPRICE})
            w.check('purse-holds-the-deposit', 0 < int(purse) <= int(deposit), {'purse': purse, 'deposit': deposit})
            w.check('account-paid-at-least-the-deposit', int(charge) >= int(deposit) and int(was) - int(now) == int(charge),
                    {'was': was, 'now': now, 'charge': charge, 'deposit': deposit})
        registry = json.loads((w.sponsor / 'bend' / 'objects' / 'counter.json').read_text())
        s = w.state('counter', 'counter-after-run', registry['transaction'])
        w.check('object-record-pins-tally', s['objectRecord'].get('kind') == 'object-record' and s['objectRecord'].get('pin') == pin,
                s['objectRecord'])
        w.check('declared-state-is-total-0-by-the-view', w.total_of(s) == 0 and s['state'] is not None, s['state'])
        w.check('activity-record-awaits-its-decider', bool(w.await_of(s)), s['record'].get('phase'))
        w.check('purse-by-the-view-equals-the-line', m is not None and s['purse'] == int(m.group(6)), {'view': s['purse']})

    with w.group('bend-fresh-object'):
        # an object the member has not made: refused by name (nothing submitted), then the shell verb that
        # makes a member-owned content cell, then the run admitted
        before = height('height-before-fresh')
        rc, out, err = shell('run-absent', 'bend run tally fresh-name')
        w.check('absent-object-refused-by-name', rc == 3 and err.startswith('refused: no object named fresh-name: make one with `create fresh-name content open`'),
                {'rc': rc, 'err': err[-300:]})
        w.check('absent-object-submitted-nothing', height('height-after-fresh-refusal') == before and 'admitted' not in out, {'out': out})
        rc, out, err = shell('create-fresh', 'create fresh-name content open')
        w.check('create-makes-the-cell', rc == 0, {'rc': rc, 'out': out[-200:], 'err': err[-300:]})
        ref = json.loads((w.sponsor / 'refs' / 'fresh-name.json').read_text())
        w.objects['fresh-name'] = {'object': ref['target'], 'capability': ref['operationCapability']}
        rc, out, err = shell('run-fresh', 'bend run tally fresh-name')
        w.check('run-on-the-made-cell-admitted', rc == 0 and out.startswith('admitted: bend run tally on fresh-name') and 'state {total=0}' in out,
                {'rc': rc, 'out': out[:300], 'err': err[-300:]})

    with w.group('bend-show'):
        rc, out, err = shell('show', 'bend show counter')
        w.check('show-reads-the-object', rc == 0 and 'state {total=0}' in out and f'pin {pin}' in out and 'purse' in out, {'rc': rc, 'out': out, 'err': err[-300:]})

    with w.group('bend-full-tally'):
        # BEND_ANSWERS answers through the default purse, then the deadline: the run COMPLETES (the demo grant's unit)
        reg = json.loads((w.sponsor / 'bend' / 'objects' / 'counter.json').read_text())
        obj, tx = reg['object'], reg['transaction']
        acct = lambda label: w.balance(w.view(label, {'accounts': [w.SPONSOR_ACCOUNT]}), w.SPONSOR_ACCOUNT)
        before_answers = acct('account-before-answers')
        (home / 'requests' / 'seven.json').write_text(json.dumps({'reply': {'tag': 'record', 'fields': [
            {'name': 'amount', 'value': {'tag': 'natural', 'value': '7'}}]}}))
        (home / 'requests' / 'seven.json').chmod(0o600)
        for n in range(AW.BEND_ANSWERS):
            rc, out, err = shell(f'await-{n}', f'bend await {obj} {tx}')
            aw = json.loads(out) if rc == 0 else {}
            w.check(f'await-{n}-names-the-slot-on-the-views-clock', aw.get('phase') == 'awaiting' and aw.get('slot')
                    and int(aw['height']) == height(f'height-at-await-{n}') and int(aw['height']) <= int(aw['deadline']), {'rc': rc, 'out': out[:400], 'err': err[-300:]})
            rc, out, err = shell(f'answer-{n}', f'bend answer {aw.get("slot")} @seven.json')
            m = re.search(r'height (\d+),', out)
            w.check(f'answer-{n}-admitted-at-or-before-the-deadline', rc == 0 and m is not None and int(m.group(1)) <= int(aw.get('deadline', -1)),
                    {'rc': rc, 'out': out[:300], 'err': err[-300:], 'deadline': aw.get('deadline')})
            rc, out, err = shell(f'deliver-{n}', f'bend deliver {obj} {tx}')
            w.check(f'deliver-{n}-resumes-under-the-default-purse', rc == 0 and out.startswith('admitted: bend deliver'), {'rc': rc, 'out': out[:300], 'err': err[-400:]})
            s = w.state('counter', f'counter-after-answer-{n}', tx)
            w.check(f'answer-{n}-added', w.total_of(s) == 7 * (n + 1) and bool(w.await_of(s)), {'state': s['state'], 'phase': s['record'].get('phase')})
        deadline = int(w.await_of(s)['deadline'])
        pad = 0
        while height(f'height-pad-{pad}') <= deadline and pad < 16:
            shell(f'pad-{pad}', f'create pad-{pad} content open')
            pad += 1
        rc, out, err = shell('deliver-timeout', f'bend deliver {obj} {tx}')
        w.check('timed-out-deliver-ends-the-tally', rc == 0 and out.startswith('admitted: bend deliver'), {'rc': rc, 'out': out[:300], 'err': err[-400:]})
        v = w.view('counter-after-end', {'births': [{'object': obj, 'transaction': tx}], 'accounts': [reg['record']]})
        phase = w.cell_of(v, reg['record']).get('record', {}).get('phase') or {}
        purse = next((int(b['balance']) for b in v.get('balances', []) if b.get('account') == reg['record']), 0)
        w.check('ended-record-and-empty-purse', phase.get('kind') != 'awaiting' and purse == 0, {'purse': purse, 'phase': phase})
        # the purse paid one price per answered resume and one for the timed-out end, and returned the rest; the
        # account paid only the answer, deliver and pad turns' own fees on top (a few units each)
        refund = acct('account-after-end') - before_answers
        expect = (AW.BEND_PURSE_PRICES - AW.BEND_ANSWERS - 1) * BPRICE
        w.check('purse-paid-one-price-per-leg-and-returned-the-rest', expect - 64 * (pad + 2 * AW.BEND_ANSWERS + 1) <= refund <= expect,
                {'refund': refund, 'expected': expect, 'pads': pad, 'runCost': AW.demo_economy()['tallyRunCost']})

    with w.group('bend-lost-reply'):
        # the shell's lost-reply switch reaches the activity path: the birth is written, its answer never read
        first_charge = int(re.search(r'charge (\d+)', run_out).group(1)) if run_out else -1
        b0 = w.watched('account-before-lost')
        acct0 = lambda v: w.balance(v, w.SPONSOR_ACCOUNT)
        rc, out, err = shell('run-lost', 'bend run tally lost --lose-reply-once')
        w.check('lost-reply-is-undecided', rc == 4 and err.startswith('undecided:') and 'deliberately not read' in err, {'rc': rc, 'err': err[-400:]})
        w.check('undecided-names-the-two-shell-lines', '`bend lookup tally`' in err and '`bend retry tally`' in err and 'mini activity' not in err, err[-400:])
        w.check('nothing-is-claimed-admitted', 'admitted' not in out, out)
        mid = w.watched('account-after-lost')
        rc, looked, err = shell('lookup', 'bend lookup tally')
        # The Host either committed the unread birth (lookup finds it: decided, and the retry replays the
        # same receipt) or dropped it with the connection (lookup: absent, undecided, nothing submitted; the
        # one exact retry then installs it). Either way: one effect. The branch taken is recorded.
        rc, looked, err = shell('lookup', 'bend lookup tally')
        found = rc == 0
        w.check('lookup-is-decided-or-absent-and-never-submits',
                (found and looked.startswith('admitted: bend lookup tally') and 'state {total=0}' in looked)
                or (rc == 4 and 'Host outcome absent' in err and '`bend retry tally`' in err), {'rc': rc, 'out': looked, 'err': err[-300:]})
        mid2 = w.watched('account-after-lookup')
        w.check('lookup-charged-nothing-more', acct0(mid2) == acct0(mid), {'afterLost': acct0(mid), 'afterLookup': acct0(mid2)})
        rc, retried, err = shell('retry', 'bend retry tally')
        rr = re.search(r'receipt (tx \d+ event \d+)', retried)
        rl = re.search(r'receipt (tx \d+ event \d+)', looked)
        w.check('retry-admitted-once-with-the-same-receipt-if-already-decided',
                rc == 0 and rr is not None and retried.startswith('admitted: bend retry tally')
                and ((found and rl is not None and rr.group(1) == rl.group(1) and '(replayed)' in retried) or (not found and '(installed)' in retried)),
                {'branch': 'committed' if found else 'dropped', 'lookup': looked[:160], 'retry': retried[:200]})
        registry = json.loads((w.sponsor / 'bend' / 'objects' / 'lost.json').read_text())
        s = w.state('lost', 'lost-after-retry', registry['transaction'])
        end = w.watched('account-after-retry')
        w.check('one-record', w.total_of(s) == 0 and s['record'].get('phase', {}).get('await') is not None, s['record'].get('phase'))
        acct = acct0
        w.check('one-charge', acct(b0) - acct(end) == first_charge,
                {'before': acct(b0), 'afterLost': acct(mid), 'afterRetry': acct(end), 'firstRunCharge': first_charge})
        w.check('purse-is-one-deposit', s['purse'] == AW.BEND_PURSE_PRICES * BPRICE, s['purse'])

    with w.group('bend-demo-sized-member'):
        # the seed's shape: an account holding a demo-sized balance (10,000) is told, by name and with the amounts,
        # that the run costs more than it holds, before anything is signed (the account is named with --account;
        # the check reads the balance and signs nothing, so the signer's ownership never comes into it)
        w.sh('poor-account', w.mini, 'workspace', '--action', 'import', '--dir', w.sponsor, '--name', 'poor-account', '--kind', 'account',
             '--target', w.SECOND, '--observe-capability', w.SECOND_SPEND, '--operation-capability', w.SECOND_SPEND)
        held = w.balance(w.view('poor-balance', {'accounts': [w.SECOND]}), w.SECOND)
        before = int(w.view('poor-height', {})['height'])
        rc, out, err = shell('poor-run', 'bend run tally counter --account poor-account')
        m = re.search(r'costs (\d+) .* holds (\d+);', err)
        w.check('demo-sized-run-refused-by-name-with-the-amounts',
                rc == 3 and err.startswith('refused: unfunded: run tally on counter costs') and m is not None and int(m.group(2)) == held
                and int(m.group(1)) == (AW.BEND_PURSE_PRICES + 1) * BPRICE and held < (AW.BEND_PURSE_PRICES + 1) * BPRICE, {'rc': rc, 'err': err[-400:], 'held': held, 'price': BPRICE})
        w.check('nothing-submitted-by-the-unfunded-run', int(w.view('poor-height-after', {})['height']) == before, 'height unchanged')

    with w.group('bend-refusal'):
        before = height('height-before-refusal')
        rc, out, err = shell('publish-malformed', 'bend publish bad @Bad.obend --entry bad')
        w.check('malformed-source-refused-by-the-front-end', rc == 3 and err.startswith('refused: front-end:'), {'rc': rc, 'err': err[-500:]})
        w.check('nothing-was-submitted', not (w.sponsor / 'bend' / 'bad' / 'attempts').exists(), 'no attempts directory for bad')
        after = height('height-after-refusal')
        w.check('judged-height-unchanged', after == before, {'before': before, 'after': after})
        w.check('nothing-admitted-printed', 'admitted' not in out and 'admitted' not in err, {'out': out})
finally:
    w.stop()
sys.exit(w.finish())
