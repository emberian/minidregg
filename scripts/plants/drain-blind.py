#!/usr/bin/env python3
"""HOST PLANT for objective-upgrade-native-journey.py --plant drain-blind (Kernel/ObjectiveActivityUpgrade).

  scripts/plants/drain-blind.py TREE

In TREE (a throwaway copy; files are replaced via temp + rename, hardlink-safe), Kernel/ObjectiveActivity.lean's
`judgeDrained` judges nothing: a declared-state write made while the object drains is no longer judged, migrated, by
the next record. The theorems that state what that judgment guarantees are false under this plant (the drained-write
theorem, the upgrade invariant and migrate_cannot_fail), so the plant replaces their proofs with `sorry` and drops
their `#assert_axioms` lines to let the Host link: the planted binary is what the kernel would ship WITHOUT them.
Built into a Host, row U2 must go red (a delivery whose migrated value the next law refuses commits)."""
import os, pathlib, re, sys

tree = pathlib.Path(sys.argv[1])
SORRY = sys.argv[2:]  # theorem names whose proofs the plant must sorry (found by building the planted tree once)


def edit(relative, change):
    path = tree / relative
    s = change(path.read_text())
    tmp = path.with_suffix('.lean.plant-tmp')
    tmp.write_text(s)
    os.replace(tmp, path)


def blind(s):
    old = '''      match judgeMigrated config snapshot record object next written.after.value with
      | .ok _ => .ok ()
      | .error reason => .error reason'''
    assert s.count(old) == 1, old
    return s.replace(old, '''      .ok ()  -- PLANT drain-blind: the drained write is not judged by the next record''')


def sorry_out(s, names):
    for name in names:
        m = re.search(r'^(theorem|private theorem) ' + re.escape(name) + r'\b', s, re.M)
        if not m:
            continue
        start = s.index(':= by', m.start())
        end = re.search(r'\n(?=(theorem |def |/--|/-!|#assert|structure |inductive |private |@\[|end |namespace |section |open |instance |abbrev |noncomputable ))', s[start:])
        stop = start + end.start() if end else len(s)
        s = s[:start] + ':= by\n  sorry -- PLANT drain-blind\n' + s[stop:]
        s = re.sub(r'(^#assert_axioms[^\n]*?) ' + re.escape(name) + r'\b', r'\1', s, flags=re.M)
        s = re.sub(r'^#assert_axioms ' + re.escape(name) + r'\s*$\n', '', s, flags=re.M)
        s = re.sub(r'^#assert_axioms\s*$\n', '', s, flags=re.M)
    return s


edit('Kernel/ObjectiveActivity.lean', blind)
by_file = {}
for spec in SORRY:
    f, n = spec.split(':', 1)
    by_file.setdefault(f, []).append(n)
for f, names in by_file.items():
    edit(f, lambda s, names=names: sorry_out(s, names))
