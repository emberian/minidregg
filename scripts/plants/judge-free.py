#!/usr/bin/env python3
"""HOST PLANT for objective-domain-native-journey.py --plant judge-free (A3 domain pricing, cv 01a115c9-d9b7).

  scripts/plants/judge-free.py TREE [--keep-theorems]

In TREE (a throwaway copy; files are replaced via temp + rename, hardlink-safe), Kernel/ObjectiveDomain.lean's
`judgeDomains` still judges every domain but reports 0 units of work, so `ActivitySeatEnd.finish` never refuses
`domainUncovered`: the judgment is free whatever the turn declared. The theorems that state the judgment counts
its reads (`judgeDomains_units`) and that a finished turn paid for them (`ActivitySeatEnd.finish_domain_covered`)
are false under this plant, so by default the plant removes them to let the Host link: the planted binary is
what the kernel would ship WITHOUT those theorems. Built into a Host, row D6 must go red (the transfer declaring
no domain work commits). With --keep-theorems the theorems stay: the Lean build must go red at
`judgeDomains_units` (the Lean tooth)."""
import os, pathlib, sys

tree = pathlib.Path(sys.argv[1])
keep = '--keep-theorems' in sys.argv[2:]


def edit(relative, change):
    path = tree / relative
    s = change(path.read_text())
    tmp = path.with_suffix('.lean.plant-tmp')
    tmp.write_text(s)
    os.replace(tmp, path)


def domain(s):
    old = '''            guards.length + index.length)'''
    assert s.count(old) == 1, old
    s = s.replace(old, '''            0)''')
    if keep:
        return s
    a = s.index('/-- **The judgment counts every domain it judges at its reads.**')
    b = s.index('/-! ## Registration -/')
    s = s[:a] + s[b:]
    old = ' judgeDomains_units\n'
    assert s.count(old) == 1, old
    return s.replace(old, '\n')


def seat_end(s):
    a = s.index('/-- **A finished turn paid for its domain judgment.**')
    b = s.index('#assert_axioms joint_admission')
    return s[:a] + s[b:]


edit('Kernel/ObjectiveDomain.lean', domain)
if not keep:
    edit('Kernel/ActivitySeatEnd.lean', seat_end)
print(f'planted judge-free{" (theorems kept)" if keep else ""} in {tree}')
