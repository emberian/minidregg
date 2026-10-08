#!/usr/bin/env python3
"""The whole-request work account of an activity turn (GPT-6 row E), on a scratch NATIVE world.

  objective-work-account-journey.py --bin DIR --root NEW_DIR [--pad 3000]

Two packages of the same program: Tally, and Tally padded with `--pad` unused record declarations
(the front end parses, elaborates and lowers every one of them on every turn that replays the package).
The Host publishes, per pin, the front end's quote (op 214 `pins[].frontEnd`: the source bytes the
replay reads, the typed-core bytes it generates). A birth declares them as `replayBytes`/`coreBytes`
in its envelope and both escrowed envelopes (`ObjectiveActivity.frontEndPaid`).

Rows (ROOT/results.json, ROOT/groups.tsv; timings ROOT/timings.tsv):
  quote          the quote is published for both pins, and the padded package's is larger
  front-end      a birth on the padded pin declaring one source byte less than the quote is refused
                 `workUncovered frontEnd needed declared`, BEFORE the replay
  core           ... one typed-core byte less: `workUncovered core`
  escrow         ... a full birth envelope but a short timeout envelope: refused (every delivery replays)
  at-quote       a birth declaring exactly the quote installs (`frontEndPaid_at_quote`)
  cost           wall time of the refusal before the replay (front-end) against a refusal AFTER the
                 replay and the run (underfunded, the same padded package): the work an over-large
                 request costs the validator before it is refused
"""
import argparse, json, os, pathlib, re, sys, time

HERE = pathlib.Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import activity_world as AW  # noqa: E402
from activity_world import World, cap, record, variant, nat  # noqa: E402

ap = argparse.ArgumentParser()
ap.add_argument('--bin', required=True)
ap.add_argument('--root', required=True)
ap.add_argument('--pad', type=int, default=3000)
ap.add_argument('--repeat', type=int, default=5)
a = ap.parse_args()
# The padded package's publication command is ~200 KB; the owner capabilities' maxCost (the command's byte
# length a capability admits) is raised for this world so the publication itself is admitted.
os.environ['NEWPARTICIPANT_OWNER_BUDGET'] = '4000000'
w = World(a.bin, a.root, HERE.parent.parent)
timings = []


def frontend_quote(pin):
    v = w.view(f'quote-{pin}', {'pins': [str(pin)]})
    q = (v.get('pins') or [{}])[0].get('frontEnd')
    return None if q is None else (int(q['replayBytes']), int(q['coreBytes']))


def envelope(ticks, replay, core):
    return dict(cap(ticks), replayBytes=str(replay), coreBytes=str(core))


def birth(label, name, pin, deposit, env, resume, timeout, expect, detail=None, init=None):
    o = w.objects[name]
    body = {'kind': 'birth', 'object': o['object'], 'objectCapability': o['capability'],
            'account': w.SPONSOR_ACCOUNT, 'accountCapability': w.SPONSOR_SPEND, 'pin': pin,
            'input': record(init=init or variant('set', nat(0)), decider=nat(int(w.SECOND))),
            'envelope': env, 'resume': resume, 'timeout': timeout, 'deposit': str(deposit)}
    start = time.monotonic()
    out = w.turn(label, w.sponsor, body, expect, detail)
    return out, time.monotonic() - start


try:
    w.bring_up(['tally', 'padded'])
    tally_src = (w.repo / 'world/activity/Tally.obend').read_text()
    padded = w.root / 'Padded.obend'
    padded.write_text(tally_src.rstrip('\n') + '\n' +
                      ''.join(f'record Pad{i}:\n  pad{i}: Nat\n' for i in range(a.pad)))
    TALLY = {'name': 'Tally', 'sourcePath': str(w.repo / 'world/activity/Tally.obend'), 'imports': []}
    PADDED = {'name': 'Tally', 'sourcePath': str(padded), 'imports': []}
    w.PIN, ARTIFACT = w.publication('publication', [TALLY], '0', 'tally')
    BIG, BIG_ARTIFACT = w.publication('publication-padded', [PADDED], '0', 'tally')
    for label, art in [('publish', ARTIFACT), ('publish-padded', BIG_ARTIFACT)]:
        w.turn(label, w.sponsor, dict(art, kind='publish', payer=w.SPONSOR_ACCOUNT,
                                      payerCapability=w.SPONSOR_SPEND), 'installed')
    w.create('create-tally', w.sponsor, 'tally', {'type': 'all', 'predicates': []}, 'installed')
    w.create('create-padded', w.sponsor, 'padded', {'type': 'all', 'predicates': []}, 'installed', pin=BIG)

    with w.group('quote'):
        small, big = frontend_quote(w.PIN), frontend_quote(BIG)
        w.check('quote-published', small is not None and big is not None, {'tally': small, 'padded': big})
        w.check('quote-padded-larger', small and big and big[0] > small[0] + a.pad * 10 and big[1] >= small[1],
                {'tally': small, 'padded': big})
    SOURCE, CORE = big
    full = envelope(3000, SOURCE, CORE)

    with w.group('front-end'):
        short = envelope(3000, SOURCE - 1, CORE)
        _, t = birth('front-end-short', 'padded', BIG, 4 * AW.PAIR, short, full, full, 'refused',
                     ['workUncovered', 'frontEnd', str(SOURCE), str(SOURCE - 1)])
        timings.append(('refused-before-replay', t))

    with w.group('core'):
        birth('core-short', 'padded', BIG, 4 * AW.PAIR, envelope(3000, SOURCE, CORE - 1), full, full, 'refused',
              ['workUncovered', 'core', str(CORE), str(CORE - 1)])

    with w.group('escrow'):
        birth('timeout-short', 'padded', BIG, 4 * AW.PAIR, full, full, envelope(3000, SOURCE - 1, CORE), 'refused',
              ['workUncovered', 'frontEnd'])

    with w.group('at-quote'):
        out, t = birth('birth-at-quote', 'padded', BIG, 4 * AW.PAIR, full, full, full, 'installed')
        timings.append(('installed-at-quote', t))

    with w.group('cost'):
        # The same padded package, refused AFTER the replay and the run (a deposit below the reserve).
        for i in range(a.repeat):
            _, t1 = birth(f'cost-before-{i}', 'padded', BIG, 4 * AW.PAIR, envelope(3000, SOURCE - 1, CORE), full, full,
                          'refused', 'workUncovered', init=variant('keep', record()))
            # (a deposit short of the reserve is judged after the run: a charged failure, row E range 2)
            _, t2 = birth(f'cost-after-{i}', 'padded', BIG, AW.PAIR - 1, full, full, full, 'charged', 'underfunded',
                          init=variant('keep', record()))
            timings.append((f'refused-before-replay-{i}', t1))
            timings.append((f'refused-after-replay-{i}', t2))
        before = sorted(t for k, t in timings if k.startswith('refused-before-replay-'))
        after = sorted(t for k, t in timings if k.startswith('refused-after-replay-'))
        median = lambda xs: xs[len(xs) // 2]
        w.check('cost-summary', median(before) < median(after),
                {'medianBeforeReplay_s': round(median(before), 3), 'medianAfterReplay_s': round(median(after), 3),
                 'padDeclarations': a.pad, 'sourceBytes': SOURCE, 'coreBytes': CORE})
    (w.root / 'timings.tsv').write_text(''.join(f'{k}\t{t:.4f}\n' for k, t in timings))
finally:
    w.stop()
sys.exit(w.finish())
