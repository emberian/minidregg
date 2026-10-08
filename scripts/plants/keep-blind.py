#!/usr/bin/env python3
"""HOST PLANT for objective-domain-native-journey.py --plant joined-drops,keep-blind (GPT-6 row A, A3).

  scripts/plants/keep-blind.py TREE

In TREE (a throwaway copy; files replaced via temp + rename, hardlink-safe), the turn-end rule `keepsDomains`
admits every post: a record write may drop the domains its record names. Its theorem (`records_keep`, and so
`domain_holds_forever`) lives in Kernel/ObjectiveDomainInvariant, outside the Host closure, so the Host links
unchanged. Apply AFTER joined-drops: the dropping registration then commits, and the dropped member's
unbacked mint commits too (row D5 red)."""
import os, pathlib, sys

tree = pathlib.Path(sys.argv[1])
path = tree / 'Kernel/ObjectiveDomain.lean'
s = path.read_text()
old = '''    Except Refusal Unit :=
  match objectOwner .object (payloadOf (snapshot.canonicalBytes post.cell)) with'''
assert s.count(old) == 1, old
s = s.replace(old, '''    Except Refusal Unit :=
  if true then .ok () else
  match objectOwner .object (payloadOf (snapshot.canonicalBytes post.cell)) with''')
tmp = path.with_suffix('.lean.plant-tmp')
tmp.write_text(s)
os.replace(tmp, path)
print(f'planted keep-blind in {tree}')
