#!/usr/bin/env python3
"""Restore the old encoder for the OOM plant without removing any theorem.

apply prints a unique backup directory. restore BACKUP restores the exact bytes.
Only Kernel/ObjectiveActivityReceiver.lean is mutated; builds/runs are separate
request_build/request_journey jobs. The final umbrella must run after restore.
"""
import argparse
import pathlib
import subprocess
import tempfile

REPO = pathlib.Path(__file__).resolve().parents[2]
REL = 'Kernel/ObjectiveActivityReceiver.lean'
TARGET = REPO / REL
BASE = '546c1c8894'
MARK = '-- kern-oom old-encoder plant (restore before umbrella)\n'

ap = argparse.ArgumentParser(description=__doc__)
ap.add_argument('action', choices=['apply', 'restore'])
ap.add_argument('backup', nargs='?')
a = ap.parse_args()
current = TARGET.read_text()
if a.action == 'restore':
    if not a.backup or MARK not in current:
        ap.error('restore needs the printed backup directory and a planted receiver')
    saved = pathlib.Path(a.backup) / 'ObjectiveActivityReceiver.lean'
    final = saved.read_text()
    if MARK in final or 'def rejectStream : StreamCodec (Reject)' not in final:
        ap.error('backup is not the final typed byte codec')
    TARGET.write_text(final)
    print(f'restored {saved}')
else:
    if a.backup or MARK in current:
        ap.error('apply takes no backup and requires an unplanted receiver')
    old = subprocess.run(['git', 'show', f'{BASE}:{REL}'], cwd=REPO,
                         check=True, text=True, stdout=subprocess.PIPE).stdout
    # The baseline instance dependency graph, but not its obsolete theorem.
    start = old.index('instance : Encodable UInt8 where')
    stop = old.index('/-- The non-recursive end of a call refusal.', start)
    instances = old[start:stop]
    instances += 'deriving instance Encodable for CallRefusalTerminal\n\n'
    start = old.index('instance : Encodable ObjectiveCall.CallRefusal :=')
    stop = old.index('@[simp] theorem callRefusal_encode_roundtrip', start)
    instances += old[start:stop]
    start = old.index('deriving instance Encodable for ObjectiveSend.MessageRefusal')
    stop = old.index('/-- The typed, canonical cause codec', start)
    instances += old[start:stop]
    start = old.index('def rejectStream :')
    stop = old.index('def rejectCodec :', start)
    encoder = old[start:stop]
    start = current.index('def rejectStream :')
    stop = current.index('def rejectCodec :', start)
    planted = current[:start] + MARK + instances + encoder + current[stop:]
    backup = pathlib.Path(tempfile.mkdtemp(prefix='kern-old-encoder-'))
    (backup / 'ObjectiveActivityReceiver.lean').write_text(current)
    TARGET.write_text(planted)
    print(f'backup={backup}')
