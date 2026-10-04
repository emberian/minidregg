#!/usr/bin/env python3
"""Lean-vs-Lean differential: the Core4 machine's specification code
(objective-machine-reference) against the code compiled under the
ObjectiveBendDemandMachineFast @[csimp] lemmas (objective-machine-fast), on every
packet of a packets.ts output root.

usage: differential.py BIN_DIR PACKET_ROOT WORK_ROOT LOG [--only A,B]

Per packet, both binaries run `cases` (MachineRun.lean: runBounded full / tick
cuts / heap-half / stack-3 / two resumes; step iteration; forceWith under two
policies, heap-half, stack-3, tick cut and resume; resume after a yield). A case
PASSes only if the JSON line (outcome, detail, remaining ticks, heap size, stack
length) AND the final State's checkpoint tokens are byte-identical, and the two
binaries emit the same case list. Exit 0 iff zero FAIL and at least one PASS.
"""
import argparse, hashlib, json, os, subprocess, sys, time
p = argparse.ArgumentParser()
p.add_argument("bin"); p.add_argument("packets"); p.add_argument("work"); p.add_argument("log")
p.add_argument("--only", default="")
a = p.parse_args()
os.makedirs(a.work, exist_ok=False)
log = open(a.log, "w")
def say(line):
    print(line, flush=True); log.write(line + "\n"); log.flush()
only = set(filter(None, a.only.split(",")))
index = json.load(open(os.path.join(a.packets, "index.json")))
passes = fails = 0
say(f"# fastmachine differential {time.strftime('%Y-%m-%dT%H:%M:%S%z')} bin={a.bin}")
for item in index:
    name = item["name"]
    if only and name not in only: continue
    if not item.get("core"):
        say(f"SKIP {name} packet-refused"); continue
    runs = {}
    for side in ("reference", "fast"):
        out = os.path.join(a.work, name, side); os.makedirs(out)
        started = time.time()
        r = subprocess.run([os.path.join(a.bin, f"objective-machine-{side}"), "cases", item["core"], out],
                           capture_output=True, text=True)
        if r.returncode != 0:
            runs[side] = None; say(f"FAIL {name} {side}-driver: {r.stderr.strip()[:300]!r}"); continue
        runs[side] = ([json.loads(l) for l in r.stdout.strip().splitlines()], out, time.time() - started)
    if runs["reference"] is None or runs["fast"] is None:
        fails += 1; continue
    ref, refDir, refS = runs["reference"]; fast, fastDir, fastS = runs["fast"]
    say(f"# {name} cases={len(ref)} reference-s={refS:.2f} fast-s={fastS:.2f}")
    if [c["case"] for c in ref] != [c["case"] for c in fast]:
        fails += 1; say(f"FAIL {name} case-lists differ"); continue
    for e, c in zip(ref, fast):
        rb = open(os.path.join(refDir, e["case"] + ".state"), "rb").read()
        fb = open(os.path.join(fastDir, c["case"] + ".state"), "rb").read()
        differ = [k for k in e if e[k] != c.get(k)]
        if rb != fb: differ.append("state-tokens")
        digest = hashlib.sha256(rb).hexdigest()[:16]
        line = (f"{name} {e['case']} outcome={e['outcome']}{(':'+e['detail']) if e['detail'] else ''}"
                f" remaining={e['remaining']} heap={e['heap']} stack={e['stack']} state-sha256={digest}")
        if differ:
            fails += 1; say(f"FAIL {line} differ={differ} fast={json.dumps(c)}")
        else:
            passes += 1; say(f"PASS {line}")
say(f"# TOTAL pass={passes} fail={fails}")
sys.exit(0 if fails == 0 and passes > 0 else 1)
