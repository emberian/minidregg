#!/usr/bin/env python3
"""pending.py [MERGE-QUEUE.md]: print the requests the merge keeper still owes: every line under
## REQUESTS that is tagged [QUEUED], or that carries NO state tag ([LANDED..]/[GATING..]/[BOUNCED..]/
[HELD..]/LANDED/BOUNCED) but names a branch/range (a `..` range or a 7+ hex sha and a `|`).
Exit 0 with lines printed when something is pending, 1 when nothing is."""
import re, sys
p = sys.argv[1] if len(sys.argv) > 1 else "/Users/ember/dev/redregg/work/MERGE-QUEUE.md"
text = open(p).read()
m = re.search(r"^## REQUESTS\n(.*?)(?=^## )", text, re.S | re.M)
out = [l for l in text.splitlines() if l.startswith("- [QUEUED]")]
for l in (m.group(1) if m else "").splitlines():
    if not l.startswith("- "): continue
    if l.startswith("- [QUEUED]"): continue
    if re.match(r"- \[(LANDED|GATING|BOUNCED|HELD)", l): continue
    if re.search(r"\b(LANDED|BOUNCED|HELD|GATING)\b", l): continue
    if "|" in l and (re.search(r"[0-9a-f]{7,}\.\.[0-9a-f]{7,}", l) or re.search(r"\b[0-9a-f]{8}\b", l)):
        out.append("UNTAGGED " + l)
for l in out: print(l[:300])
sys.exit(0 if out else 1)
