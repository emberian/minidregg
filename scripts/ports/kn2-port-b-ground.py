#!/usr/bin/env python3
"""KN2 PORT-B: re-index lifecycle admissions/cores from `durable : Durable` / `opened : Opened config`
onto `ground : Ground deployment` (Compiler/ServedBasis). Mechanical shapes only; code outside block comments."""
import re, sys
subs = [
 (r'\(durable : (?:DeclaredResourceController\.)?Durable\)', '(ground : Ground deployment)'),
 (r'\{durable : (?:DeclaredResourceController\.)?Durable\}', '{ground : Ground deployment}'),
 (r'\(opened : (?:NativeHost\.)?Opened config\)', '(ground : Ground config.deployment)'),
 (r'\{opened : (?:NativeHost\.)?Opened config\}', '{ground : Ground config.deployment}'),
 (r'\bopened\.durable\.snapshot\.model\.(roots|consumed|journal)', r'ground.view.model.\1'),
 (r'\bdurable\.snapshot\.model\.(roots|consumed|journal)', r'ground.view.model.\1'),
 (r'(?:NativeHost\.)?logicalHeight config opened\.durable', '(config.genesisHeight + ground.height)'),
 (r'\bopened\.durable\b', 'ground'),
 (r'prepared\.authority\.snapshot', 'ground.authority'),
 (r'prepared\.directory\.directory', 'ground.directory'),
 (r'\bdurable\b(?=[ )\]⟩}]|$)', 'ground'),
 (r'\bdurable\.(worldRoot|logStart|height)\b', r'ground.\1'),
 (r'\bopened\b(?=[ )\]⟩}]|$)', 'ground'),
]
def fix(text):
    out=[]; incom=False
    for line in text.split('\n'):
        l=line
        if incom:
            if '-/' in l: incom=False
            out.append(l); continue
        if l.lstrip().startswith('/-'):
            if '-/' not in l: incom=True
            out.append(l); continue
        if l.lstrip().startswith('--'):
            out.append(l); continue
        for a,b in subs: l=re.sub(a,b,l)
        out.append(l)
    return '\n'.join(out)
OPEN='open Minidregg.Compiler.ServedBasis (Ground)'
def addopen(t):
    if 'Ground' not in t or OPEN in t: return t
    t=re.sub(r'^abbrev Durable := DeclaredResourceController\.Durable\n','',t,flags=re.M)
    return t.replace('set_option autoImplicit false\n','set_option autoImplicit false\n\n'+OPEN+'\n',1)
for p in sys.argv[1:]:
    s=open(p).read(); t=addopen(fix(s))
    if t!=s: open(p,'w').write(t); print('rewrote',p)
