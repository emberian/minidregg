#!/usr/bin/env python3
"""union-imports.py FILE: resolve conflict hunks that consist ONLY of `import X  -- comment` lines:
union by module; a module on both sides takes THEIRS' line (the picked commit's edit of its comment);
order: ours' order, then theirs-only modules in theirs' order. Refuses (exit 1) on any hunk with a
non-import line."""
import re, sys
p = sys.argv[1]; s = open(p).read()
pat = re.compile(r'<<<<<<< [^\n]*\n(.*?)(?:\|\|\|\|\|\|\| [^\n]*\n.*?)?=======\n(.*?)>>>>>>> [^\n]*\n', re.S)
def mod(l):
    m = re.match(r'import\s+(\S+)', l); return m.group(1) if m else None
def res(m):
    ours, theirs = m.group(1).splitlines(True), m.group(2).splitlines(True)
    for l in ours + theirs:
        if l.strip() and not mod(l): sys.exit(f"non-import line in hunk: {l!r}")
    tm = {mod(l): l for l in theirs if l.strip()}
    out, seen = [], set()
    for l in ours:
        if not l.strip(): continue
        k = mod(l); out.append(tm.get(k, l)); seen.add(k)
    out += [l for l in theirs if l.strip() and mod(l) not in seen]
    return "".join(out)
n = len(pat.findall(s)); s2 = pat.sub(res, s)
assert '<<<<<<<' not in s2 and '>>>>>>>' not in s2
open(p, 'w').write(s2); print(f"union-imports: {n} hunk(s) resolved in {p}")
