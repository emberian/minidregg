#!/usr/bin/env python3
"""HOST PLANT for objective-domain-native-journey.py --plant joined-drops (GPT-6 row A, A3).

  scripts/plants/joined-drops.py TREE

In TREE (a throwaway copy; files replaced via temp + rename, hardlink-safe), registerDomain writes each
member's record with ONLY the new domain (`joined` replaces `domains` instead of appending): a record write
that drops a domain the member is in. The turn-end rule `keepsDomains` refuses it `domainsDropped`, so on a
Host built from this tree row D5 goes red (the second registration over a bank member is refused).
Combined with keep-blind, the write commits and the member leaves the bank's judgment (D5 red the other way)."""
import os, pathlib, sys

tree = pathlib.Path(sys.argv[1])
path = tree / 'Kernel/ObjectiveDomain.lean'
s = path.read_text()
old = 'def joined (record : ObjectRecord) (id : Digest) : ObjectRecord := { record with domains := record.domains ++ [id] }'
assert s.count(old) == 1, old
s = s.replace(old, 'def joined (record : ObjectRecord) (id : Digest) : ObjectRecord := { record with domains := [id] }')
tmp = path.with_suffix('.lean.plant-tmp')
tmp.write_text(s)
os.replace(tmp, path)
print(f'planted joined-drops in {tree}')
