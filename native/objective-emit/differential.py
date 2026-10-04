#!/usr/bin/env python3
"""Differential harness: the Lean demand machine (`runBounded`, the function the
Core4 soundness theorems are about) against the C backend (runtime.c + the ROM
Compiler/ObjectiveBendEmitC.lean emits), packet by packet, case by case.

usage: differential.py PACKET_ROOT WORK_ROOT LOG [--cflags FLAGS] [--only A,B]
       [--heap N --stack N --ticks N]

PACKET_ROOT is the output of packets.ts (index.json + core/typed packets).
Per packet: one Lean `suite` process (emits program.c, computes every case's
expected outcome/ticks/fingerprint/State bytes), one C build, one C run per
case. A case PASSes only if outcome, detail, tick count, per-tick fingerprint,
heap size, stack length, byte count AND the State bytes are all identical.
Verdicts are the per-case lines in LOG; the exit status is 0 iff zero FAIL.
"""
import argparse, hashlib, json, os, subprocess, sys, time

here = os.path.dirname(os.path.abspath(__file__))
repo = os.path.dirname(os.path.dirname(here))
p = argparse.ArgumentParser()
p.add_argument("packets"); p.add_argument("work"); p.add_argument("log")
p.add_argument("--cflags", default=""); p.add_argument("--only", default="")
p.add_argument("--heap", default="4000000"); p.add_argument("--stack", default="4000000")
p.add_argument("--ticks", default="20000000")
a = p.parse_args()
os.makedirs(a.work, exist_ok=False)
log = open(a.log, "w")
def say(line):
    print(line, flush=True); log.write(line + "\n"); log.flush()
lean = ["lake", "env", "lean", "--run", os.path.join(repo, "Compiler/ObjectiveBendEmitCRun.lean")]
fields = ["outcome", "detail", "ticks", "trace", "heap", "stack", "bytes", "resumes"]
index = json.load(open(os.path.join(a.packets, "index.json")))
only = set(filter(None, a.only.split(",")))
passes = fails = 0
say(f"# differential {time.strftime('%Y-%m-%dT%H:%M:%S%z')} cflags={a.cflags!r} limits heap={a.heap} stack={a.stack} ticks={a.ticks}")
for item in index:
    name = item["name"]
    if only and name not in only: continue
    if not item.get("core"):
        say(f"SKIP {name} packet-refused: {item.get('message','')[:200]!r}"); continue
    work = os.path.join(a.work, name); os.makedirs(work)
    typing = "no-typed-packet"
    if item.get("typed"):
        t = subprocess.run(lean + ["typing", item["typed"]], cwd=repo, capture_output=True, text=True)
        typing = (json.loads(t.stdout.strip().splitlines()[-1])["typing"] if t.returncode == 0 and t.stdout.strip() else "typing-driver-error")
    started = time.time()
    s = subprocess.run(lean + ["suite", item["core"], work, a.heap, a.stack, a.ticks] + ([item["responses"]] if item.get("responses") else []), cwd=repo, capture_output=True, text=True)
    if s.returncode != 0:
        fails += 1; say(f"FAIL {name} lean-suite: {s.stderr.strip()[:400]!r}"); continue
    summary = json.loads(s.stdout.strip().splitlines()[-1])
    say(f"# {name} typing={typing} rom-nodes={summary['nodes']} labels={summary['labels']} full-ticks={summary['fullTicks']} responses={summary.get('responses',0)} yields={summary.get('yields',0)} lean-suite-s={time.time()-started:.1f}")
    prog = os.path.join(work, "prog")
    cc = subprocess.run(["cc", "-O2", "-std=c11", "-Wall", "-Werror"] + a.cflags.split() +
                        ["-o", prog, os.path.join(here, "runtime.c"), os.path.join(work, "program.c")],
                        capture_output=True, text=True)
    if cc.returncode != 0:
        fails += 1; say(f"FAIL {name} cc: {cc.stderr.strip()[:400]!r}"); continue
    for case in json.load(open(os.path.join(work, "cases.json"))):
        cstate = os.path.join(work, case["case"] + ".c.state")
        # FIRST_RESPONSE is passed whenever it is not the default 0; it needs a resume path.
        cmd = [prog, str(case["heap"]), str(case["stack"]), str(case["ticks"]), cstate]
        if case["resume"] or case["first"]:
            cmd += [case["resume"] or "-", str(case["first"])]
        r = subprocess.run(cmd, capture_output=True, text=True)
        if r.returncode != 0:
            fails += 1; say(f"FAIL {name} {case['case']} c-run: {r.stderr.strip()[:300]!r}"); continue
        c = json.loads(r.stdout.strip().splitlines()[-1]); e = case["lean"]
        differ = [f for f in fields if str(e[f]) != str(c[f])]
        lb = open(case["state"], "rb").read(); cb = open(cstate, "rb").read()
        if lb != cb: differ.append("state-bytes")
        digest = hashlib.sha256(lb).hexdigest()[:16]
        line = f"{name} {case['case']} limits=({case['heap']},{case['stack']},{case['ticks']}){' resume' if case['resume'] else ''} first={case['first']} outcome={e['outcome']}{(':'+e['detail']) if e['detail'] else ''} ticks={e['ticks']} resumes={e['resumes']} heap={e['heap']} stack={e['stack']} state-sha256={digest}"
        if differ:
            fails += 1; say(f"FAIL {line} differ={differ} c={json.dumps(c)}")
        else:
            passes += 1; say(f"PASS {line}")
say(f"# TOTAL pass={passes} fail={fails}")
sys.exit(0 if fails == 0 else 1)
