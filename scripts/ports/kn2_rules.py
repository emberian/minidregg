#!/usr/bin/env python3
"""KN2-STORE-OPEN stage (3): census-driven port of history reads.

Scans every .lean file outside .lake, splits it into top-level declarations,
and classifies each read of the decoded history inside a COMPUTATIONAL
declaration (def / partial def / instance / abbrev bodies; never theorem,
lemma or example) by shape. Shapes with a meaning-preserving mechanical
rewrite are rewritten (`--apply`); every other site is reported as a leftover
with its census group.

Why a script and not ast-grep: sg has no Lean grammar, and tree-sitter-lean
does not parse this tree's Lean 4 (unicode binders, `match ... with` inside
`do`, `⟨…⟩`, `·`) reliably enough to anchor rewrites; the shapes below are
exact, anchored, and every rewrite is checked by the compiler afterwards.

Rules (applied only in computational declarations):
  R1  <loaded>.image.accepted.length   ->  <loaded>.height
      (`Loaded.height` is that expression by definition today and a field
      after stage 2b; <loaded> is an identifier path, see LOADED below.)
Everything else is a LEFTOVER, grouped:
  G1 tx-lookup      findIdx?/find?/any/filter by transaction id, accepted[i]?, getLast?
  G2 journal        model.journal / lookupRecorded on a served snapshot
  G3 consumed       model.consumed
  G4 prefix         take/drop/prefixImage/prefixAt/atPrefix/loadImage/loadPrefix
  G5 scan           a whole accepted list passed to a fold/scan
  G6 rootLog        rootLog
  G7 history-len    model.history
Usage: kn2_rules.py ROOT [--apply] [--tsv OUT]
"""
import re, sys, os, json

KEYWORDS = re.compile(r'^(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+|partial\s+|unsafe\s+)*'
                      r'(def|theorem|lemma|instance|abbrev|structure|inductive|example|class|opaque|axiom)\b')
COMPUTATIONAL = {'def', 'instance', 'abbrev', 'opaque'}
LOADED = r'(?:[A-Za-z_][\w\']*\.)*(?:durable|loaded|target|physical|current|next|old|opened\.durable|source\.durable|session\.durable)'
R1 = re.compile(r'\b(' + LOADED + r')\.image\.accepted\.length\b')

GROUPS = [
    ('G1', re.compile(r'\.image\.accepted(\.findIdx\?|\.find\?|\.any|\.filter|\[|\.getLast\?|\.findSome\?|\.head\?)')),
    ('G4', re.compile(r'\.image\.accepted\.(take|drop)|prefixImage|prefixAt|atPrefix|loadImage|loadPrefix')),
    ('G2', re.compile(r'model\.journal|lookupRecorded')),
    ('G3', re.compile(r'model\.consumed')),
    ('G6', re.compile(r'\brootLog\b')),
    ('G7', re.compile(r'model\.history')),
    ('G5', re.compile(r'\.image\.accepted\b(?!\.length)')),
]

def declarations(lines):
    kind, start = None, 0
    for i, line in enumerate(lines):
        m = KEYWORDS.match(line)
        if m:
            if kind is not None:
                yield kind, start, i
            kind, start = m.group(1), i
        elif line.startswith('end ') or line.startswith('namespace ') or line.startswith('section') or line.startswith('#'):
            if kind is not None:
                yield kind, start, i
            kind = None
    if kind is not None:
        yield kind, start, len(lines)

SKIP = ('Compiler/DurableReceiverIO.lean', 'Compiler/DurableHistory.lean', 'Compiler/DurableHistoryReader.lean',
        'Compiler/DurableHistoryStore.lean', 'Kernel/DurableView.lean', 'Kernel/DurableCommitProtocol.lean',
        'Kernel/DurableDataIntent.lean', 'Kernel/DurableCheckpoint.lean', 'Kernel/DurableReceiver.lean')

def main():
    root = sys.argv[1]
    apply = '--apply' in sys.argv
    tsv = sys.argv[sys.argv.index('--tsv') + 1] if '--tsv' in sys.argv else None
    rewritten, leftovers = [], []
    for dirpath, dirnames, filenames in os.walk(root):
        dirnames[:] = [d for d in dirnames if d not in ('.lake', '.git', 'native', 'node_modules')]
        for name in filenames:
            if not name.endswith('.lean'):
                continue
            path = os.path.join(dirpath, name)
            rel = os.path.relpath(path, root)
            if rel in SKIP:
                continue
            lines = open(path, encoding='utf-8').read().split('\n')
            changed = False
            for kind, start, end in declarations(lines):
                if kind not in COMPUTATIONAL:
                    continue
                decl = lines[start].strip()[:80]
                for i in range(start, end):
                    line = lines[i]
                    if line.lstrip().startswith('--'):
                        continue
                    new, count = R1.subn(lambda m: m.group(1) + '.height', line)
                    if count:
                        rewritten.append((rel, i + 1, 'R1', decl))
                        if apply:
                            lines[i] = new
                            changed = True
                        line = new
                    for group, pattern in GROUPS:
                        if pattern.search(line):
                            leftovers.append((rel, i + 1, group, decl, line.strip()[:140]))
                            break
            if changed:
                open(path, 'w', encoding='utf-8').write('\n'.join(lines))
    print(f'rewritten by rule: {len(rewritten)} sites in {len(set(r[0] for r in rewritten))} files')
    print(f'leftover: {len(leftovers)} sites in {len(set(l[0] for l in leftovers))} files')
    by = {}
    for l in leftovers:
        by.setdefault(l[2], set()).add(l[0])
    for group in sorted(by):
        print(f'  {group}: {sum(1 for l in leftovers if l[2] == group)} sites, {len(by[group])} files')
    if tsv:
        with open(tsv, 'w') as out:
            for r in rewritten:
                out.write('\t'.join(map(str, ('REWRITTEN',) + r)) + '\n')
            for l in leftovers:
                out.write('\t'.join(map(str, ('LEFTOVER',) + l)) + '\n')

if __name__ == '__main__':
    main()
