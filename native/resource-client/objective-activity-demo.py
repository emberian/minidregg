#!/usr/bin/env python3
"""The kernel activity on a durable scratch world (Kernel/ObjectiveActivity).

  objective-activity-demo.py --exe BIN/objective-activity-world --root NEW_DIR

One fresh world (never a live one). world/activity/Tally.obend is captured by
the pinned frontend, elaborated as a definition by the pinned elaborator, made
an activity artifact, published, and born. Then, each step its own process
against the durable image:

  A. reply:    a stranger cannot decide the slot; the decider replies; two
               deliveries of that await are prepared on the same snapshot; the
               first commits (the tally resumes, publishes 5, awaits again);
               its exact retry replays; the second is a transaction conflict;
               a fresh delivery finds no decided await; an intent claiming the
               spent await without touching the record is refused by the
               executor (alreadyConsumed), while the same forged claim on a
               fresh await id commits (the control).
  B. conflict: the owner writes the object's state after the yield; the next
               reply is delivered as `conflict {stale: 1}`, never as `reply`;
               the tally re-asks with its own total.
  C. forged:   a record cell whose checkpoint bytes were altered is refused at
               delivery (checkpointDigest), though the executor took the write.
  D. timeout:  a second tally; before its deadline an open slot cannot be
               delivered; heights pass; the decider is too late; anyone's
               delivery expires the slot and resumes the tally with
               `timedOut`, which finishes it; the unused resume fee returns.

Every step writes ROOT/transcript/NN-label.{cmd,out,err,rc}; ROOT/results.json
lists each step's verdict against its expectation and the script exits 1 on
any mismatch.
"""
import argparse, json, os, pathlib, subprocess, sys

os.umask(0o077)
HERE = pathlib.Path(__file__).resolve().parent
REPO = HERE.parent.parent
ap = argparse.ArgumentParser()
ap.add_argument('--exe', required=True)
ap.add_argument('--root', required=True)
ap.add_argument('--bun', default='bun')
a = ap.parse_args()
root = pathlib.Path(a.root).resolve()
if root.exists():
    raise SystemExit('root must be new')
T = root / 'transcript'
T.mkdir(parents=True)
W = root / 'world'
results = []
counter = [0]


def run(label, *cmd):
    counter[0] += 1
    tag = f'{counter[0]:02d}-{label}'
    r = subprocess.run([str(c) for c in cmd], stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    (T / f'{tag}.cmd').write_text(' '.join(str(c) for c in cmd) + '\n')
    (T / f'{tag}.out').write_bytes(r.stdout)
    (T / f'{tag}.err').write_bytes(r.stderr)
    (T / f'{tag}.rc').write_text(f'{r.returncode}\n')
    return tag, r


def world(label, verb, expect, *args, check=None):
    tag, r = run(label, a.exe, verb, '--world', W, *args)
    out = r.stdout.decode(errors='replace').strip()
    try:
        value = json.loads(out.splitlines()[-1]) if out else {'error': r.stderr.decode(errors='replace')}
    except json.JSONDecodeError:
        value = {'unparsed': out}
    verdict = value.get('verdict')
    reason = value.get('reason', '')
    ok = verdict == expect[0] and (len(expect) < 2 or expect[1] in reason)
    detail = None
    if ok and check is not None:
        detail = check(value)
        ok = detail is True
    results.append({'step': tag, 'verdict': verdict, 'reason': reason, 'expected': list(expect),
                    'ok': ok, **({} if detail in (None, True) else {'check': detail})})
    print(f'{tag:28} {verdict} {reason[:90]}', flush=True)
    return value


def data(name, value):
    path = root / f'{name}.json'
    path.write_text(json.dumps(value))
    return path


def nat(n):
    return {'tag': 'natural', 'value': str(n)}


def record(**fields):
    return {'tag': 'record', 'fields': [{'name': k, 'value': v} for k, v in fields.items()]}


def field(record_json, name):
    return next(f['value'] for f in record_json['fields'] if f['name'] == name)


# --- the published program ---------------------------------------------------
pub = root / 'publication'
pub.mkdir()
spec = {'schema': 'dregg.objective-bend.package-input.v1', 'edition': 'objective-bend-1',
        'modules': [{'name': 'Tally', 'sourcePath': str(REPO / 'world/activity/Tally.obend'), 'imports': []}],
        'entryModule': '0', 'entryDefinition': 'tally'}
(pub / 'spec.json').write_text(json.dumps(spec))
limits = json.dumps({'heap': '100000', 'stack': '100000', 'ticks': '100000', 'typeFuel': '16384'})
for label, cmd in [
        ('frontend', [a.bun, REPO / 'native/bend-source/objective-frontend.ts', pub / 'spec.json', pub / 'cap']),
        ('elaborate', [a.bun, REPO / 'native/bend-source/objective-elaborate.ts', pub / 'cap/objective.json',
                       pub / 'def', '[]', '[]', limits, 'definition']),
        ('package-input', [a.bun, REPO / 'native/bend-source/objective-source-package.ts',
                           pub / 'cap/objective.json', pub / 'package-input.json'])]:
    tag, r = run(label, *cmd)
    if r.returncode:
        raise SystemExit(f'{label} failed: {r.stderr.decode(errors="replace")[-800:]}')
tag, r = run('artifact', a.exe, 'artifact', '--package-input', pub / 'package-input.json',
             '--core', pub / 'def.typed.json', '--out', pub / 'artifact.bin')
if r.returncode:
    raise SystemExit(f'artifact failed: {r.stderr.decode(errors="replace")[-800:]}')
artifact = json.loads(r.stdout)

OWNER, DECIDER, STRANGER = '1', '2', '3'
world('genesis', 'genesis', ('genesis',), '--accounts', f'{OWNER}:10000000,{DECIDER}:1000,{STRANGER}:100000')
world('publish', 'publish', ('accepted',), '--subject', OWNER, '--artifact', pub / 'artifact.bin')
world('publish-again', 'publish', ('refused-by-kernel', 'packageExists'), '--subject', OWNER,
      '--artifact', pub / 'artifact.bin')

pin = artifact['artifact']
born = world('birth-A', 'birth', ('accepted',), '--subject', OWNER, '--object', 'tally-A', '--pin', pin,
             '--input', data('start-A', record(total=nat(0), decider=nat(DECIDER))), '--nonce', '1',
             '--timeout-ticks', '3000',
             check=lambda v: v['segment']['kind'] == 'yielded' and v['stored']['generation'] == 0
             or 'first segment did not yield at generation 0')
cell = born['record']
slot0 = born['stored']['phase']['await']['source']['slot']
await0 = born['stored']['phase']['await']['id']

# --- A. reply -------------------------------------------------------------------
world('A-deliver-undecided', 'deliver', ('refused-by-kernel', 'notYetDecided'), '--subject', STRANGER, '--record', cell)
world('A-stranger-decides', 'resolve', ('refused-by-kernel', 'notDecider'), '--subject', STRANGER, '--slot', slot0,
      '--reply', data('reply-5', record(amount=nat(5))))
world('A-ill-typed-reply', 'resolve', ('refused-by-kernel', 'responseType'), '--subject', DECIDER, '--slot', slot0,
      '--reply', data('reply-bad', record(amount={'tag': 'label', 'value': 'five'})))
world('A-decider-replies', 'resolve', ('accepted',), '--subject', DECIDER, '--slot', slot0,
      '--reply', root / 'reply-5.json')
world('A-decider-again', 'resolve', ('refused-by-kernel', 'notOpen'), '--subject', DECIDER, '--slot', slot0,
      '--reply', data('reply-6', record(amount=nat(6))))
world('A-prepare-first', 'deliver', ('prepared',), '--subject', STRANGER, '--record', cell,
      '--save-intent', root / 'first.intent',
      check=lambda v: (v['delivered']['label'] == 'reply' and v['path'].endswith('resumed')
                       and v['refund'] == born['stored']['escrow']['timeoutFee'] != born['stored']['escrow']['resumeFee'])
      or f'reply delivery {v.get("delivered")} refund {v.get("refund")}')
world('A-prepare-second', 'deliver', ('prepared',), '--subject', OWNER, '--record', cell, '--extra-ticks', '100',
      '--save-intent', root / 'second.intent')
resumed = world('A-submit-first', 'submit', ('accepted',), '--intent', root / 'first.intent')
world('A-retry-first', 'submit', ('replayed',), '--intent', root / 'first.intent')
world('A-submit-second', 'submit', ('rejected-by-durable-executor', 'transactionConflict'),
      '--intent', root / 'second.intent')
after = world('A-show-record', 'show', (None,), '--cell', cell,
              check=lambda v: (v['record']['generation'] == 1 and v['record']['phase']['kind'] == 'awaiting'
                               and v['record']['phase']['await']['id'] != await0) or 'record did not advance')
world('A-show-state', 'show', (None,), '--cell', born['object'],
      check=lambda v: v.get('value') == nat(5) or f'declared state is {v.get("value")}')
world('A-deliver-again', 'deliver', ('refused-by-kernel', 'notYetDecided'), '--subject', STRANGER, '--record', cell)
world('A-forged-claim-spent', 'claim', ('rejected-by-durable-executor', 'alreadyConsumed'), '--await', await0)
world('A-forged-claim-fresh', 'claim', ('accepted',), '--await', '12345')

# --- B. conflict ----------------------------------------------------------------
slot1 = after['record']['phase']['await']['source']['slot']
world('B-owner-writes-state', 'write-state', ('accepted',), '--subject', OWNER, '--record', cell,
      '--value', data('state-99', nat(99)), '--nonce', '1')
world('B-stranger-writes-state', 'write-state', ('refused-by-kernel', 'notOwner'), '--subject', STRANGER,
      '--record', cell, '--value', root / 'state-99.json', '--nonce', '2')
world('B-decider-replies', 'resolve', ('accepted',), '--subject', DECIDER, '--slot', slot1,
      '--reply', data('reply-7', record(amount=nat(7))))
conflicted = world('B-deliver', 'deliver', ('accepted',), '--subject', STRANGER, '--record', cell,
                   check=lambda v: (v['delivered']['label'] == 'conflict' and v['settled'] == 'reply'
                                    and v['stale'] == 1) or f'delivered {v.get("delivered")}')
world('B-show-state', 'show', (None,), '--cell', born['object'],
      check=lambda v: v.get('value') == nat(5) or f'declared state is {v.get("value")}')
slot2 = conflicted['stored']['phase']['await']['source']['slot']
world('B-decider-replies-again', 'resolve', ('accepted',), '--subject', DECIDER, '--slot', slot2,
      '--reply', data('reply-4', record(amount=nat(4))))
world('B-deliver-current', 'deliver', ('accepted',), '--subject', STRANGER, '--record', cell,
      check=lambda v: (v['delivered']['label'] == 'reply' and v['stale'] == 0) or f'delivered {v.get("delivered")}')
world('B-show-state-9', 'show', (None,), '--cell', born['object'],
      check=lambda v: v.get('value') == nat(9) or f'declared state is {v.get("value")}')

# --- C. forged record -----------------------------------------------------------
born_c = world('C-birth', 'birth', ('accepted',), '--subject', OWNER, '--object', 'tally-C', '--pin', pin,
               '--input', data('start-C', record(total=nat(1), decider=nat(DECIDER))), '--nonce', '3')
slot_c = born_c['stored']['phase']['await']['source']['slot']
world('C-decider-replies', 'resolve', ('accepted',), '--subject', DECIDER, '--slot', slot_c,
      '--reply', root / 'reply-5.json')
world('C-forge-record', 'forge-record', ('accepted',), '--record', born_c['record'])
world('C-deliver-forged', 'deliver', ('refused-by-kernel', 'checkpointDigest'), '--subject', STRANGER,
      '--record', born_c['record'])

# --- D. timeout -----------------------------------------------------------------
born_d = world('D-birth', 'birth', ('accepted',), '--subject', OWNER, '--object', 'tally-D', '--pin', pin,
               '--input', data('start-D', record(total=nat(40), decider=nat(DECIDER))), '--nonce', '4',
               '--timeout-ticks', '5000')
cell_d = born_d['record']
slot_d = born_d['stored']['phase']['await']['source']['slot']
balance_born = world('D-owner-balance-after-birth', 'show', (None,), '--account', OWNER, check=lambda v: True)
world('D-deliver-before-deadline', 'deliver', ('refused-by-kernel', 'notYetDecided'), '--subject', STRANGER,
      '--record', cell_d)
for i in range(5):
    world(f'D-tick-{i}', 'tick', ('accepted',))
world('D-decider-too-late', 'resolve', ('refused-by-kernel', 'pastDeadline'), '--subject', DECIDER, '--slot', slot_d,
      '--reply', root / 'reply-5.json')
timed = world('D-deliver-timeout', 'deliver', ('accepted',), '--subject', STRANGER, '--record', cell_d,
              check=lambda v: (v['delivered']['label'] == 'timedOut' and v['path'].endswith('timedOut')
                               and v['segment']['kind'] == 'finished' and v['segment']['result'] == nat(40)
                               and v['refund'] == born_d['stored']['escrow']['resumeFee']
                               != born_d['stored']['escrow']['timeoutFee'])
              or f'timeout delivered {v.get("delivered")} segment {v.get("segment")}')
world('D-owner-balance-refunded', 'show', (None,), '--account', OWNER,
      check=lambda v: v['balance'] - balance_born['balance'] == born_d['stored']['escrow']['resumeFee']
      or f'refund moved the balance by {v["balance"] - balance_born["balance"]}')
world('D-show-record', 'show', (None,), '--cell', cell_d,
      check=lambda v: (v['record']['phase']['kind'] == 'done' and v['record']['phase']['result'] == nat(40))
      or 'record not done')
world('D-show-slot', 'show', (None,), '--cell', timed['await']['source']['slotCell'],
      check=lambda v: v['slot']['phase']['decision']['kind'] == 'expired' or 'slot not expired')
world('D-deliver-done', 'deliver', ('refused-by-kernel', 'notAwaiting'), '--subject', STRANGER, '--record', cell_d)
world('show-world', 'show', (None,), check=lambda v: True)

summary = {'schema': 'dregg.objective-activity.demo.v1', 'world': str(W), 'pin': pin,
           'steps': len(results), 'failed': [r for r in results if not r['ok']], 'results': results}
(root / 'results.json').write_text(json.dumps(summary, indent=1) + '\n')
print(json.dumps({'steps': len(results), 'failed': len(summary['failed'])}))
sys.exit(1 if summary['failed'] else 0)
