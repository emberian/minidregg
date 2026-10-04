#!/usr/bin/env python3
"""Checkpoint-transparency differential: per activity packet, the lazy turn chain
(resume the machine's own yielded state) against the kernel chain (resume what
Kernel.ObjectiveActivity.runSegment stores: the Plan extraction's state, settled and
collected). scripts/ObjectiveCheckpointTransparency.lean runs both chains; this
driver runs it per packet and judges.

usage: transparency.py PACKET_ROOT LOG [--mutant NAME] [--heap N --stack N --ticks N]
       [--growth NAME:FIRST:LAST ...]

A packet PASSes iff every segment agrees (same outcome, same Plan/result Data, kernel
ticks <= lazy ticks) and the chain consumed every response. --growth NAME:FIRST:LAST
also requires packet NAME's stored checkpoint to have the same byte count at every
segment FIRST..LAST (the growth leg: 0 B per resume). Packets without responses are
not activities and are skipped (listed). With --mutant the verdicts are the planted
fault's: the caller requires at least one FAIL. Exit 0 iff zero FAIL and at least one
PASS.
"""
import argparse, json, os, subprocess, sys

here = os.path.dirname(os.path.abspath(__file__))
repo = os.path.dirname(os.path.dirname(here))
p = argparse.ArgumentParser()
p.add_argument("packets"); p.add_argument("log")
p.add_argument("--mutant", default=None)
p.add_argument("--heap", default="1000000"); p.add_argument("--stack", default="1000000")
p.add_argument("--ticks", default="2000000")
p.add_argument("--growth", action="append", default=[])
a = p.parse_args()
log = open(a.log, "w")
def say(line):
    print(line, flush=True); log.write(line + "\n"); log.flush()
lean = ["lake", "env", "lean", "--run", os.path.join(repo, "scripts/ObjectiveCheckpointTransparency.lean")]
growth = {}
for g in a.growth:
    name, first, last = g.split(":"); growth[name] = (int(first), int(last))
index = json.load(open(os.path.join(a.packets, "index.json")))
passes = fails = 0
seen = set()
say(f"# transparency mutant={a.mutant or 'none'} limits heap={a.heap} stack={a.stack} ticks={a.ticks}")
for item in index:
    name = item["name"]
    responses = json.load(open(item["responses"])) if item.get("responses") else []
    if not responses:
        say(f"SKIP {name} not-an-activity"); continue
    if not item.get("core"):
        fails += 1; say(f"FAIL {name} packet-refused: {item.get('message','')[:200]!r}"); continue
    cmd = lean + [item["core"], a.heap, a.stack, a.ticks, item["responses"]] + ([a.mutant] if a.mutant else [])
    r = subprocess.run(cmd, cwd=repo, capture_output=True, text=True)
    rows = [json.loads(l) for l in r.stdout.splitlines() if l.startswith("{")]
    if not rows or "verdict" not in rows[-1]:
        fails += 1; say(f"FAIL {name} driver: rc={r.returncode} {r.stderr.strip()[:400]!r}"); continue
    final, segments = rows[-1], rows[:-1]
    for row in segments:
        log.write(f"  {name} {json.dumps(row, sort_keys=True)}\n")
    problems = []
    if final["verdict"] != "agree" or r.returncode != 0:
        bad = [s for s in segments if not s["agree"]]
        problems.append(f"disagree at segment {bad[0]['segment'] if bad else '?'}: {json.dumps(bad[0]) if bad else ''}"[:600])
    if final["responsesLeft"] != 0:
        problems.append(f"{final['responsesLeft']} responses undelivered")
    sizes = [s["kernelCheckpointBytes"] for s in segments]
    if name in growth:
        seen.add(name)
        first, last = growth[name]
        window = sizes[first:last + 1]
        if len(window) != last - first + 1 or None in window or len(set(window)) != 1:
            problems.append(f"growth: checkpoint bytes {window} over segments {first}..{last} are not constant")
    summary = (f"{name} segments={final['segments']} ticks lazy={sum(s['lazyTicks'] for s in segments)} "
               f"kernel={sum(s['kernelTicks'] for s in segments)} kernel-checkpoint-bytes={sizes} "
               f"lazy-collected-bytes={[s['lazyCollectedBytes'] for s in segments]}")
    if problems:
        fails += 1; say(f"FAIL {summary} :: {' ; '.join(problems)}")
    else:
        passes += 1; say(f"PASS {summary}")
for name in growth:
    if name not in seen:
        fails += 1; say(f"FAIL {name} growth packet absent")
say(f"# TOTAL pass={passes} fail={fails}")
sys.exit(0 if fails == 0 and passes > 0 else 1)
