#!/usr/bin/env python3
"""Differential harness: the Lean demand machine (`runBounded`, the function the
Core4 soundness theorems are about) against the C backend (runtime.c + the ROM
Compiler/ObjectiveBendEmitC.lean emits), packet by packet, case by case.

usage: differential.py PACKET_ROOT WORK_ROOT LOG [--cflags FLAGS] [--only A,B]
       [--heap N --stack N --ticks N] [--jobs N] [--serve] [--lean-bin PATH] [--runtime PATH]
       [--precompile-runtime] [--max-fail N]

PACKET_ROOT is the output of packets.ts (index.json + core/typed packets), or of
`ObjectiveBendCDiffGen gen` (the same index, plus per-entry `expectTyping`).
Per packet: one Lean `suite` run (emits program.c, computes every case's
expected outcome/ticks/fingerprint/State bytes), one C build, one C run per
case. A case PASSes only if outcome, detail, tick count, per-tick fingerprint,
heap size, stack length, byte count AND the State bytes are all identical.
Verdicts are the per-case lines in LOG; the exit status is 0 iff zero FAIL.

--jobs N     N packets at a time; the log is still written in index order.
--serve      one long-lived `ObjectiveBendEmitCRun serve` Lean process per job
             instead of one Lean process per command (the same `dispatch`).
--lean-bin P the compiled `objective-cdiff` executable (lake build objective-cdiff) in place of
             `lake env lean --run Compiler/ObjectiveBendEmitCRun.lean`: the same `main`, native speed.
--precompile-runtime  compile the runtime once and link each program against that object (the
             default compiles runtime.c together with every program.c, as the gate always has).
--max-fail N stop starting new packets once N FAIL lines are in (a control run needs one);
             the log then ends `# STOPPED` and the packets not run are listed as not run.
--runtime P  the C runtime source to build against (default runtime.c next to this
             file): how a planted mutant of the runtime is run.
An index entry with `expectTyping` FAILs unless the preview path's checker verdict
starts with it: a generated program that the real checker refuses is a generator
defect, never a pass.
A C or Lean step that exceeds --timeout seconds is a FAIL line, never a hang.
"""
import argparse, concurrent.futures, hashlib, json, os, subprocess, sys, threading, time

here = os.path.dirname(os.path.abspath(__file__))
repo = os.path.dirname(os.path.dirname(here))
p = argparse.ArgumentParser()
p.add_argument("packets"); p.add_argument("work"); p.add_argument("log")
p.add_argument("--cflags", default=""); p.add_argument("--only", default="")
p.add_argument("--heap", default="4000000"); p.add_argument("--stack", default="4000000")
p.add_argument("--ticks", default="20000000")
p.add_argument("--jobs", type=int, default=1); p.add_argument("--serve", action="store_true")
p.add_argument("--lean-bin", default="")
p.add_argument("--runtime", default=os.path.join(here, "runtime.c"))
p.add_argument("--precompile-runtime", action="store_true")
p.add_argument("--max-fail", type=int, default=0)
p.add_argument("--timeout", type=int, default=300)
a = p.parse_args()
os.makedirs(a.work, exist_ok=False)
log = open(a.log, "w")
log_lock = threading.Lock()
def say(line):
    with log_lock:
        print(line, flush=True); log.write(line + "\n"); log.flush()
lean_driver = os.path.join(repo, "Compiler/ObjectiveBendEmitCRun.lean")
lean_once = [os.path.abspath(a.lean_bin)] if a.lean_bin else ["lake", "env", "lean", "--run", lean_driver]
fields = ["outcome", "detail", "ticks", "trace", "heap", "stack", "bytes", "resumes"]
index = json.load(open(os.path.join(a.packets, "index.json")))
only = set(filter(None, a.only.split(",")))
runtime = os.path.abspath(a.runtime)


class LeanWorker:
    """`serve` mode: commands in, `##done RC`-terminated answers out."""
    def __init__(self):
        self.proc = None
    def _start(self):
        self.proc = subprocess.Popen(lean_once + ["serve"], cwd=repo, stdin=subprocess.PIPE,
                                     stdout=subprocess.PIPE, stderr=subprocess.DEVNULL, text=True)
    def run(self, args):
        """-> (returncode, stdout lines, stderr text) like subprocess.run."""
        if self.proc is None or self.proc.poll() is not None:
            self._start()
        timer = threading.Timer(a.timeout, self.proc.kill); timer.start()
        try:
            self.proc.stdin.write(" ".join(args) + "\n"); self.proc.stdin.flush()
            out = []
            while True:
                line = self.proc.stdout.readline()
                if not line:
                    self.proc = None
                    return 99, out, "lean worker died or timed out"
                line = line.rstrip("\n")
                if line.startswith("##done "):
                    return int(line.split()[1]), out, ""
                out.append(line)
        except (BrokenPipeError, ValueError):
            self.proc = None
            return 99, [], "lean worker died"
        finally:
            timer.cancel()
    def close(self):
        if self.proc is not None and self.proc.poll() is None:
            try: self.proc.stdin.close(); self.proc.wait(timeout=10)
            except Exception: self.proc.kill()


def lean_run(worker, args):
    if worker is not None:
        rc, out, err = worker.run(args)
        if rc == 2 and out and out[-1].startswith('{"error"'):
            err = out[-1]
        return rc, out, err
    try:
        r = subprocess.run(lean_once + args, cwd=repo, capture_output=True, text=True, timeout=a.timeout)
    except subprocess.TimeoutExpired:
        return 99, [], "lean timed out"
    return r.returncode, r.stdout.strip().splitlines(), r.stderr


def process(item, worker):
    """-> (lines, passes, fails) for one packet."""
    lines = []; passes = fails = 0
    name = item["name"]
    if not item.get("core"):
        return [f"SKIP {name} packet-refused: {item.get('message','')[:200]!r}"], 0, 0
    work = os.path.join(a.work, name); os.makedirs(work)
    typing = "no-typed-packet"
    if item.get("typed"):
        rc, out, err = lean_run(worker, ["typing", item["typed"]])
        typing = (json.loads(out[-1])["typing"] if rc == 0 and out else "typing-driver-error")
    expect = item.get("expectTyping")
    if expect and not typing.startswith(expect):
        return [f"FAIL {name} generated-packet-not-{expect}: typing={typing[:200]!r}"], 0, 1
    started = time.time()
    rc, out, err = lean_run(worker, ["suite", item["core"], work, a.heap, a.stack, a.ticks] + ([item["responses"]] if item.get("responses") else []))
    if rc != 0:
        return [f"FAIL {name} lean-suite: {err.strip()[:400]!r}"], 0, 1
    summary = json.loads(out[-1])
    # A cohort row may pin the whole run's tick count (O(1) operators: a regression to
    # recursion changes the count, so it is a FAIL, not merely a slower PASS).
    if item.get("expectedTicks") is not None and summary["fullTicks"] != int(item["expectedTicks"]):
        fails += 1; lines.append(f"FAIL {name} ticks-pin: runBounded took {summary['fullTicks']} ticks; the cohort pins {item['expectedTicks']}")
    lines.append(f"# {name} typing={typing} rom-nodes={summary['nodes']} labels={summary['labels']} full-ticks={summary['fullTicks']} responses={summary.get('responses',0)} yields={summary.get('yields',0)} lean-suite-s={time.time()-started:.1f}")
    prog = os.path.join(work, "prog")
    cc = subprocess.run(["cc", "-O2", "-std=c11", "-Wall", "-Werror"] + a.cflags.split() +
                        ["-o", prog, runtime_object or runtime, os.path.join(work, "program.c")],
                        capture_output=True, text=True)
    if cc.returncode != 0:
        return lines + [f"FAIL {name} cc: {cc.stderr.strip()[:400]!r}"], 0, 1
    for case in json.load(open(os.path.join(work, "cases.json"))):
        cstate = os.path.join(work, case["case"] + ".c.state")
        # FIRST_RESPONSE is passed whenever it is not the default 0; it needs a resume path.
        cmd = [prog, str(case["heap"]), str(case["stack"]), str(case["ticks"]), cstate]
        if case["resume"] or case["first"]:
            cmd += [case["resume"] or "-", str(case["first"])]
        try:
            r = subprocess.run(cmd, capture_output=True, text=True, timeout=a.timeout)
        except subprocess.TimeoutExpired:
            fails += 1; lines.append(f"FAIL {name} {case['case']} c-run: timed out after {a.timeout}s"); continue
        if r.returncode != 0:
            fails += 1; lines.append(f"FAIL {name} {case['case']} c-run: {r.stderr.strip()[:300]!r}"); continue
        c = json.loads(r.stdout.strip().splitlines()[-1]); e = case["lean"]
        differ = [f for f in fields if str(e[f]) != str(c[f])]
        lb = open(case["state"], "rb").read(); cb = open(cstate, "rb").read()
        if lb != cb: differ.append("state-bytes")
        digest = hashlib.sha256(lb).hexdigest()[:16]
        line = f"{name} {case['case']} limits=({case['heap']},{case['stack']},{case['ticks']}){' resume' if case['resume'] else ''} first={case['first']} outcome={e['outcome']}{(':'+e['detail']) if e['detail'] else ''} ticks={e['ticks']} resumes={e['resumes']} heap={e['heap']} stack={e['stack']} state-sha256={digest}"
        if differ:
            fails += 1; lines.append(f"FAIL {line} differ={differ} c={json.dumps(c)}")
        else:
            passes += 1; lines.append(f"PASS {line}")
    return lines, passes, fails


runtime_object = None
if a.precompile_runtime:
    runtime_object = os.path.join(a.work, "runtime.o")
    built = subprocess.run(["cc", "-O2", "-std=c11", "-Wall", "-Werror"] + a.cflags.split() + ["-c", "-o", runtime_object, runtime],
                           capture_output=True, text=True)
    if built.returncode != 0:
        print(f"differential: the runtime does not compile: {built.stderr.strip()[:400]}", file=sys.stderr)
        log.write(f"FAIL runtime cc: {built.stderr.strip()[:400]!r}\n# TOTAL pass=0 fail=1\n"); sys.exit(1)
items = [i for i in index if not only or i["name"] in only]
say(f"# differential {time.strftime('%Y-%m-%dT%H:%M:%S%z')} cflags={a.cflags!r} limits heap={a.heap} stack={a.stack} ticks={a.ticks} jobs={a.jobs} serve={a.serve} runtime={runtime}")
passes = fails = 0
done = {}; next_i = 0
local = threading.local()
workers = []
first_fail = [None]; fail_total = [0]; fail_lock = threading.Lock()
def job(i):
    if a.max_fail and fail_total[0] >= a.max_fail:
        return i, ([], 0, 0)
    worker = None
    if a.serve:
        if not hasattr(local, "worker"):
            local.worker = LeanWorker(); workers.append(local.worker)
        worker = local.worker
    try:
        result = process(items[i], worker)
        if result[2]:
            with fail_lock:
                fail_total[0] += result[2]
        return i, result
    except Exception as error:  # a harness fault is a FAIL line, never a lost packet
        return i, ([f"FAIL {items[i]['name']} harness: {type(error).__name__}: {str(error)[:300]}"], 0, 1)
with concurrent.futures.ThreadPoolExecutor(max_workers=max(1, a.jobs)) as pool:
    for future in concurrent.futures.as_completed([pool.submit(job, i) for i in range(len(items))]):
        i, result = future.result()
        done[i] = result
        while next_i in done:   # the log is written in index order, as soon as it is contiguous
            lines, ps, fs = done.pop(next_i)
            for line in lines: say(line)
            if fs and first_fail[0] is None: first_fail[0] = (next_i, items[next_i]["name"])
            passes += ps; fails += fs; next_i += 1
for w in workers: w.close()
if first_fail[0] is not None:
    say(f"# FIRST-FAIL {first_fail[0][1]} (packet {first_fail[0][0] + 1} of {len(items)})")
if a.max_fail and fails >= a.max_fail:
    say(f"# STOPPED after {fails} FAIL (--max-fail {a.max_fail}); packets not run are absent from this log")
say(f"# TOTAL pass={passes} fail={fails}")
sys.exit(0 if fails == 0 else 1)
