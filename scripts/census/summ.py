#!/usr/bin/env python3
# scripts/census/summ.py CENSUS.jsonl: per command p50/p95 wall against the budget
# (CENSUS_BUDGET_MS, default 10: p50 over it is RED), Host ops by total; then per Host op across
# all commands: calls, p50/p95 per call, total ms.
import json, os, sys, statistics as st
B = float(os.environ.get("CENSUS_BUDGET_MS", "10"))
def verdict(ms): return "ok" if ms <= B else f"**RED** +{ms - B:.0f}"
rows = [json.loads(l) for l in open(sys.argv[1])]
def pct(v, p):
    v = sorted(v); return v[min(len(v)-1, int(round(p/100*(len(v)-1))))] if v else 0
by = {}
for r in rows: by.setdefault(r["label"], []).append(r)
print(f"| command | runs | rc | wall p50 | vs {B:.0f} ms | wall p95 | Host op ms p50 (calls) | consent ms | codec ms | elsewhere |")
print("|---|---|---|---|---|---|---|---|---|---|")
ops = {}
for label, rs in by.items():
    walls = [r["wall"] for r in rs]
    opsum = {}; cons=[]; cod=[]; oth=[]
    for r in rs:
        per = {}
        for k, w, ms in r["hops"]:
            if k == "host": per.setdefault(w, []).append(ms); ops.setdefault(w, []).append(ms)
        for w, v in per.items(): opsum.setdefault(w, []).append((sum(v), len(v)))
        c = sum(h[2] for h in r["hops"] if h[0] == "consent"); d = sum(h[2] for h in r["hops"] if h[0] == "codec")
        hsum = sum(h[2] for h in r["hops"] if h[0] == "host")
        cons.append(c); cod.append(d); oth.append(r["wall"] - c - d - hsum)
    opstr = ", ".join(f"{w} {st.median([x[0] for x in v]):.1f} ({round(st.median([x[1] for x in v]))})"
                      for w, v in sorted(opsum.items(), key=lambda kv: -st.median([x[0] for x in kv[1]])))
    rcs = sorted(set(r["rc"] for r in rs))
    print(f"| `{rs[0]['line'] if len(set(r['line'] for r in rs))==1 else label}` | {len(rs)} | {','.join(map(str,rcs))} | {st.median(walls):.0f} | {verdict(st.median(walls))} | {pct(walls,95):.0f} | {opstr or '-'} | {st.median(cons):.0f} | {st.median(cod):.0f} | {st.median(oth):.0f} |")
print()
print("| Host op | calls | p50 ms | p95 ms | total ms | share of all Host op time |")
print("|---|---|---|---|---|---|")
tot = sum(sum(v) for v in ops.values()) or 1
for w, v in sorted(ops.items(), key=lambda kv: -sum(kv[1])):
    print(f"| {w} | {len(v)} | {st.median(v):.1f} | {pct(v,95):.1f} | {sum(v):.0f} | {100*sum(v)/tot:.0f}% |")
