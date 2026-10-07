#!/usr/bin/env python3
"""N quote -> submit births on a scratch NATIVE world; the deposit is a fixed point.

  objective-activity-quote-submit-journey.py --bin DIR --root NEW_DIR [--births 50]

Each birth is quoted ONCE (the Host's own `underfunded D R` refusal of a birth at the bare fee pair) and
submitted ONCE with exactly the quoted deposit R, at a fresh random nonce (so every digest the record carries
differs from the quote's). The record's digests and heights are fixed-width (`encodeRecord_length_mask`), so
the deposit the submission demands is the quote: every submission installs. A refusal `underfunded` is the
defect, named by the row. Rows: ROOT/results.json, ROOT/groups.tsv; the quotes: ROOT/quotes.tsv.
"""
import argparse, json, pathlib, re, sys

HERE = pathlib.Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import activity_world as AW  # noqa: E402
from activity_world import World, record, variant  # noqa: E402

ap = argparse.ArgumentParser()
ap.add_argument('--bin', required=True)
ap.add_argument('--root', required=True)
ap.add_argument('--births', type=int, default=50)
a = ap.parse_args()
w = World(a.bin, a.root, HERE.parent.parent)
QUOTE = re.compile(r'underfunded (\d+) (\d+)')
quotes = []
try:
    w.bring_up(['tally'])
    TALLY = {'name': 'Tally', 'sourcePath': str(w.repo / 'world/activity/Tally.obend'), 'imports': []}
    w.PIN, ARTIFACT = w.publication('publication', [TALLY], '0', 'tally')
    w.turn('publish', w.sponsor, dict(ARTIFACT, kind='publish', payer=w.SPONSOR_ACCOUNT,
                                      payerCapability=w.SPONSOR_SPEND), 'installed')
    w.create('create-tally-object', w.sponsor, 'tally', {'type': 'all', 'predicates': []}, 'installed')
    with w.group('quote-submit'):
        for i in range(a.births):
            # the first birth creates the object's declared state; later ones join it (a `set` of existing state is blindWrite)
            init = None if i == 0 else variant('keep', record())
            # The quote: the plan of a birth at the bare fee pair reports, before anything is submitted or charged,
            # that it would be a charged failure `underfunded D R` (a submitted one would charge its price).
            q = w.birth(f'quote-{i:02d}', w.sponsor, 'tally', AW.PAIR, 'prepared', 'underfunded', init=init,
                        prepare=True)
            row = w.results[-1]
            m = QUOTE.search(row.get('detail', ''))
            need = int(m.group(2)) if m else None
            w.check(f'quote-{i:02d}-parsed', m is not None and int(m.group(1)) == AW.PAIR and need > AW.PAIR,
                    {'quote': m.groups() if m else None})
            if need is None:
                continue
            quotes.append(need)
            w.birth(f'submit-{i:02d}', w.sponsor, 'tally', need, 'installed', init=init)
            if not w.results[-1]['ok'] and 'underfunded' in w.results[-1].get('detail', ''):
                w.results[-1]['defect'] = 'UNDERFUNDED at the quoted deposit'
    (w.root / 'quotes.tsv').write_text(''.join(f'{i}\t{q}\n' for i, q in enumerate(quotes)))
    installed = sum(1 for r in w.results if r['step'].startswith('submit-') and r['ok'])
    underfunded = sum(1 for r in w.results if r['step'].startswith('submit-') and not r['ok']
                      and 'underfunded' in r.get('detail', ''))
    w.check('summary', installed == a.births and underfunded == 0,
            {'births': a.births, 'installed': installed, 'underfunded': underfunded,
             'distinctQuotes': sorted(set(quotes))})
finally:
    w.stop()
sys.exit(w.finish())
