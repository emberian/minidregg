#!/usr/bin/env python3
"""gates-union.py scripts/local-gates.sh: resolve conflict hunks on the GATES=(...) line by union,
inserting each THEIRS-only gate after its predecessor in THEIRS' order. Other hunks: refuse (exit 1)."""
import re, sys
p = sys.argv[1]; s = open(p).read()
pat = re.compile(r'<<<<<<< [^\n]*\n(.*?)=======\n(.*?)>>>>>>> [^\n]*\n', re.S)
def res(m):
    a, b = re.fullmatch(r'GATES=\((.*)\)\n', m.group(1)), re.fullmatch(r'GATES=\((.*)\)\n', m.group(2))
    if not (a and b): sys.exit("non-GATES hunk")
    o, t = a.group(1).split(), b.group(1).split()
    for i, g in enumerate(t):
        if g not in o: o.insert(o.index(t[i-1]) + 1 if i and t[i-1] in o else len(o), g)
    return 'GATES=(' + ' '.join(o) + ')\n'
s = pat.sub(res, s); assert '<<<<<<<' not in s; open(p, 'w').write(s)
