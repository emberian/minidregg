#!/usr/bin/env python3
"""Review the kern baseline-to-train manifest changes without admitting or pinning them.

Run BEFORE pinning: requires the baseline pins and retained scanner outputs
from check-gate-repair.sh manifest-evidence. The committed pure-move TSV is
the durable result; this one-time review helper does not rewrite a live pin.
Emits exact row/hash/module evidence and a candidate ledger for human review.
The regular objective gate remains responsible for validating and pinning it.
"""
import collections
import importlib.util
import json
from pathlib import Path

spec = importlib.util.spec_from_file_location('manifest', 'scripts/objective-manifest.py')
m = importlib.util.module_from_spec(spec)
spec.loader.exec_module(m)
root = Path('build-logs/objective')
pins, errors = m.load_pins('scripts/gates/objective-manifest')
assert not errors, errors
runs = [m.Run(str(root / ('review-' + name + '.out'))) for name in ('theory', 'mathlib')]
fresh = m.fresh_rows(runs)
draft = {}
for line in (root / 'draft-ledger.txt').read_text().splitlines():
    if not line.strip() or line.startswith('#'):
        continue
    row = line.split('\t')
    assert len(row) == 6
    draft[row[0]] = row
counts = collections.Counter()
review, ledger = [], []
for key in sorted(set(pins) | set(fresh)):
    old = pins.get(key)
    new, run = fresh.get(key, (None, None))
    kind = m.classify(old, new)
    if kind == 'same':
        continue
    counts[kind] += 1
    moved = bool(old and new and old.module != new.module)
    pure = bool(moved and old.contract == new.contract)
    record = dict(name=key, classification=kind,
                  oldModule=old.module if old else None, newModule=new.module if new else None,
                  oldStatementHash=old.stmt if old else None, newStatementHash=new.stmt if new else None,
                  pureMove=pure, moved=moved)
    if kind in ('restated', 'removed'):
        record['oldStatement'] = old.text
        record['newStatement'] = new.text if new else None
    if kind in ('added', 'rerendered'):
        review.append(record)
        continue
    row = draft[key]
    assert row[1:4] == [old.contract, new.contract if new else '-', kind], key
    if kind == 'removed':
        if key.startswith('private '):
            name = key[len('private '):].split(' @')[0]
            successors = [r for k, (r, _) in fresh.items()
                          if k == name or k.startswith('private ' + name + ' @')]
            assert len(successors) == 1, (key, len(successors))
            successor = successors[0]
            record['successorModule'] = successor.module
            record['successorStatementHash'] = successor.stmt
            equal = old.stmt == successor.stmt
            reason = (f'successor: {name} -- private declaration relocated from {old.module} '
                      f'to {successor.module}; statement SHA256 '
                      + (f'unchanged {old.stmt}' if equal else f'changed {old.stmt} -> {successor.stmt}; relocated private constant references change the hash, not a pure move'))
        elif key.endswith('Loaded.judge_tail'):
            reason = ('successor: Minidregg.Compiler.DurableReceiverIO.Commit.tail_pinned, '
                      'Minidregg.Compiler.DurableReceiverIO.Judged.tail_pinned -- R2 certificate API; '
                      'tail-law conclusion retained by NativeHostReplay.advance_judged')
        elif key.endswith('.encodableOfLawful'):
            reason = ('obsolete: 775240ec removes lawful-bytes-to-Nat Encodable helper causing exponential '
                      'charged-refusal memory use; explicit byte StreamCodec and callRefusalStream roundtrip replace it')
        else:
            raise AssertionError(key)
    elif kind == 'restated':
        if '.ObjectiveActivityReceiver.callRefusal_encode_roundtrip' in key:
            row[4] = '775240ec+de1a3a33'
            reason = 'charged-refusal byte codec: roundtrip now states the live callRefusalStream codec, replacing Encodable Nat encoding; subsequently moved to Core'
        elif '.World.' in key:
            reason = 'R0 absence guards: Turn gains absent, admit_of requires absentCheck = none, and Reject.cellAbsent shifts generated constructor eliminator indices'
        elif '.ObjectiveActivity.Refusal.' in key:
            reason = 'R0 stateRetired refusal added; generated constructor eliminator index changes'
        elif '.DurableCheckpointCodec.' in key:
            reason = 'pole schema-refs/v6: seed-epoch refusal now also diagnoses schema-refs/v5 versus v6'
        elif any(x in key for x in ('.Inbox.', '.ObjectiveCall.', '.ObjectiveSend.')):
            reason = 'pole generation inboxes: preserve generation across FIFO steps and use snapshot-selected generation cells with exact generation evidence'
        else:
            assert any(x in key for x in ('.DurableReceiverIO.', '.NativeHostReplay.', '.ObjectiveActivityGateRoute.')), key
            reason = 'R2 checked commit API: judge returns indexed evidence, writer/replay consume it, and route/source theorems retain conclusions under Judged evidence'
        reason += f'; individually restated {key}; statement SHA256 {old.stmt} -> {new.stmt}'
    else:
        assert kind == 'redefined', kind
        roots = m.via(run, new, pins)
        record['changedRoots'] = roots
        reason = f'unchanged statement SHA256 {old.stmt}; '
        if moved:
            reason += f'moved declaration {old.module} -> {new.module}; '
        if roots:
            reason += 'changed dependency definitions: ' + ', '.join(roots)
        elif row[4].startswith('UNATTRIBUTED'):
            assert '.JobMoney.' in key or '.PurseRefill.' in key, key
            dependencies = sorted(n for n in run.reach(new.name)
                                  if n.startswith('Minidregg.Kernel.PayAssignmentReceiver.')
                                  or n.startswith('_private.Kernel.PayAssignmentOwner.'))
            assert dependencies, key
            record['ownerDependencies'] = dependencies
            row[4] = 'de1a3a33'
            reason += ('R2 PayAssignmentOwner extraction: OwnerTargets/OwnerGrant and their Decidable instances moved unchanged; '
                       'generated private instance names enter this definition closure: ' + ', '.join(dependencies))
        else:
            if key.endswith('.readBackEntry @Compiler.DurableReceiverIO'):
                reason += 'R2 Core extraction: readBackEntry still has the same statement; its private u64At/blobAt parsing dependencies moved to DurableReceiverCore'
            else:
                assert '.PayAssignmentReceiver.' in key or key.endswith('.accountHolder'), key
                reason += 'R2 PayAssignmentOwner extraction: unchanged OwnerGrant decision now reaches its relocated private match splitter; no authorization predicate change'
        if row[5] != 'TODO':
            reason += '; source attribution: ' + row[5]
    row[5] = reason
    assert 'TODO' not in reason and not row[4].startswith('UNATTRIBUTED'), key
    record['commit'] = row[4]
    record['reason'] = reason
    review.append(record)
    ledger.append('\t'.join(row))
(root / 'review-classification.jsonl').write_text(''.join(json.dumps(r, ensure_ascii=False) + '\n' for r in review))
(root / 'reviewed-ledger-candidate.txt').write_text('\n'.join(ledger) + '\n')
print('classification:', dict(counts))
print('pure moves (same name, statement, closure, axioms):', sum(r['pureMove'] for r in review))
print('moved rows with other changes:', sum(r['moved'] and not r['pureMove'] for r in review))
print('candidate ledger rows:', len(ledger), '(not admitted; review before appending)')
