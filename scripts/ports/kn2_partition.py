#!/usr/bin/env python3
"""Partition KN2 port leftovers into at most four non-overlapping lanes.

Input: the census TSV of kn2_rules.py (LEFTOVER rows) and, optionally, a file
of modules that failed to build after the rule pass. Every file goes to
exactly one lane, chosen by the lane that owns its dominant cluster:

  PORT-A  receivers + lookups: tx-id lookups, journal readers, consumed bits
          (G1, G2, G3 in Kernel/*Receiver*, *Lookup*, *Admission*, *Core*,
          Fn*, Pay*, Compiler/GenericSimplex*, Compiler/Carried*Provenance)
  PORT-B  past states: prefix cuts and genesis replays -> Reader.stateAt (G4),
          NativeHistorySelection, *History*, CarriedSegment*, JointSource*,
          FnEvidence, ReceiptContinuity*, NativeObservationController
  PORT-C  the walk/consent family: NativeHostReplay, ConsentAnchor,
          ClientConsentCore, NativeHostSession, NativeProviderHistory,
          NativeReserveContinuity, Kernel/Contracts
  PORT-D  the Host serve path and tools: Host/*, Kernel/NativeHost*.lean
          (other than the above), scripts/*, Verify/*, Assurance/*, docs/*
OB-ENG-owned files (ObjectiveActivity*, ObjectRecord, ObjectiveCall/Send/
Inbox/AnswerSlot, Seat*) are flagged: DEPUTY-OB-ENG reviews those hunks.
"""
import sys, re, collections

C = ['NativeHostReplay', 'ConsentAnchor', 'ClientConsentCore', 'NativeHostSession', 'NativeProviderHistory',
     'NativeReserveContinuity', 'Kernel/Contracts/']
B = ['NativeHistorySelection', 'History.lean', 'HistorySelection', 'CarriedSegment', 'JointSource',
     'FnEvidence', 'ReceiptContinuity', 'NativeObservationController', 'Core.lean', 'CreatedHistory',
     'JointControlBootstrapBundle', 'RetainedSegmentInspection', 'CarriedApplicationProvenance']
D_PREFIX = ('Host/', 'scripts/', 'Verify/', 'Assurance/', 'docs/')
OBENG = re.compile(r'ObjectiveActivity|ObjectRecord|ObjectiveCall|ObjectiveSend|ObjectiveInbox|AnswerSlot|/Seat')

def lane(path):
    if any(c in path for c in C):
        return 'PORT-C'
    if any(b in path for b in B):
        return 'PORT-B'
    if path.startswith(D_PREFIX) or re.match(r'Kernel/NativeHost(Context|Codec)?\.lean$', path):
        return 'PORT-D'
    return 'PORT-A'

def main():
    rows = [line.rstrip('\n').split('\t') for line in open(sys.argv[1])]
    failing = set()
    if len(sys.argv) > 2:
        failing = {l.strip() for l in open(sys.argv[2]) if l.strip()}
    files = collections.defaultdict(list)
    for row in rows:
        if row[0] == 'LEFTOVER':
            files[row[1]].append(row)
    for module in failing:
        path = module.replace('.', '/') + '.lean'
        files.setdefault(path, [])
    lanes = collections.defaultdict(list)
    for path in sorted(files):
        lanes[lane(path)].append(path)
    for name in sorted(lanes):
        print(f'== {name}: {len(lanes[name])} files, {sum(len(files[p]) for p in lanes[name])} leftover sites')
        for path in lanes[name]:
            groups = ','.join(sorted({r[3] for r in files[path]})) or 'build-failure'
            flag = '  [OB-ENG reviews]' if OBENG.search(path) else ''
            fail = '  [does not build after the rule pass]' if path.replace('/', '.')[:-5] in failing else ''
            print(f'  {path}  ({len(files[path])} sites: {groups}){flag}{fail}')

if __name__ == '__main__':
    main()
