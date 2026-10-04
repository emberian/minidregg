#!/usr/bin/env python3
"""table.py L: the growth table from evidence/grow-{main,mine}: per level, median propose/submit of the
20 writes after the level, store-bench `load:` (DurableReceiverIO.load), kept-root control, lookups."""
import os, re, statistics, sys
L = sys.argv[1]
def rows(tag):
    d = f"{L}/evidence/grow-{tag}"
    out = []
    for f in sorted(os.listdir(d)):
        m = re.fullmatch(r"bench-(\d+)\.txt", f)
        if not m: continue
        n = int(m.group(1)); b = open(f"{d}/{f}").read()
        load = re.search(r"^load: (\d+) ms", b, re.M); roots = re.search(r"kept roots checked (\d+), differing (\d+)", b)
        sysload = re.search(r"^load ([\d.]+)$", b, re.M)
        w = [l.split("\t") for l in open(f"{d}/writes-at-{n}.tsv").read().split("\n") if l] if os.path.exists(f"{d}/writes-at-{n}.tsv") else []
        med = lambda i: f"{statistics.median(float(x[i]) for x in w if x[i] != 'NA'):.2f}" if w else "-"
        lk = open(f"{d}/lookup-{n}.txt").read() if os.path.exists(f"{d}/lookup-{n}.txt") else ""
        lks = re.findall(r"lookup (mid|last) \(g\d+\) ([\d.]+) s", lk)
        agree = all(re.search(r'"acceptedCount":"(\d+)","worldRoot":"(\d+)"\} original \{"acceptedCount":"\1","worldRoot":"\2"', l) for l in lk.split("\n") if l.startswith(("mid:", "last:"))) if lk else None
        out.append((n, load.group(1) if load else "-", f"{roots.group(1)}/{roots.group(2)}" if roots else "-",
                    med(2), med(3), " ".join(f"{a}={t}" for a, t in lks) or "-", {True: "equal", False: "DIFFER", None: "-"}[agree],
                    sysload.group(1) if sysload else "-"))
    return sorted(out)
print("| binaries | records | Store open (load) ms | kept roots checked/differing | propose s (median of 20) | submit s (median of 20) | receipt lookup s | lookup = original | box load1 |")
print("|---|---|---|---|---|---|---|---|---|")
for tag in ("main", "mine"):
    for r in rows(tag):
        print(f"| {tag} | " + " | ".join(str(x) for x in r) + " |")
