#!/usr/bin/env python3
"""HOST PLANT for objective-domain-native-journey.py --plant domain-blind (GPT-6 row A, A3).

  scripts/plants/domain-blind.py TREE

In TREE (a throwaway copy; files are replaced via temp + rename, hardlink-safe), Kernel/ObjectiveDomain.lean's
`judgeDomains` judges nothing: every turn ends with no domain refusal and no domain guards. The theorems that
state what the judgment guarantees (`judgeDomains_sound`, `ActivitySeatEnd.finish_domains`) are false under
this plant, so the plant also removes them to let the Host link: the planted binary is what the kernel would
ship WITHOUT those theorems. Built into a Host, row D1 must go red (a.deposit(1) commits although the joint
law a = b refuses it)."""
import os, pathlib, sys

tree = pathlib.Path(sys.argv[1])


def edit(relative, change):
    path = tree / relative
    s = change(path.read_text())
    tmp = path.with_suffix('.lean.plant-tmp')
    tmp.write_text(s)
    os.replace(tmp, path)


def domain(s):
    old = '''    (posts : List Post) : Except Refusal (List ReadGuard) :=
  let written := writtenObjects posts
'''
    assert s.count(old) == 1, old
    s = s.replace(old, '''    (posts : List Post) : Except Refusal (List ReadGuard) :=
  if true then .ok [] else
  let written := writtenObjects posts
''')
    a = s.index('/-- **The domain judgment at turn end, stated.**')
    b = s.index('/-! ## Registration -/')
    s = s[:a] + s[b:]
    old = ' judgeDomains_sound\n'
    assert s.count(old) == 1, old
    return s.replace(old, '\n')


def seat_end(s):
    a = s.index('/-- **What an admitted turn end guarantees about invariant domains.**')
    b = s.index('#assert_axioms joint_admission')
    s = s[:a] + s[b:]
    old = ' finish_domains\n'
    assert s.count(old) == 1, old
    return s.replace(old, '\n')


edit('Kernel/ObjectiveDomain.lean', domain)
edit('Kernel/ActivitySeatEnd.lean', seat_end)
print(f'planted domain-blind in {tree}')
