#!/usr/bin/env python3
# scripts/census/census.py WORLD MINI REPS OUT.jsonl SPEC... ; SPEC = "MEMBER|LABEL|LINE" (LINE may use {i} {t} {n})
# Each line runs REPS times warm through the forced-command wrapper with a FIXED MINI_TRACE per member
# (the line resident is keyed by MINI_* env); one JSON row per run: wall ms, rc, and every traced hop.
# -v as the first SPEC prints stdout/stderr of the last rep.
import os, sys, json, time, subprocess
W, mini, reps, out = sys.argv[1], sys.argv[2], int(sys.argv[3]), sys.argv[4]
specs = sys.argv[5:]; verbose = False
os.makedirs(os.environ.get("CENSUS_TRACE_DIR", W + "/census"), exist_ok=True)
if specs and specs[0] == "-v": verbose = True; specs = specs[1:]
root = W + "/root/var/lib/mini"; cand = root + "/candidate/current/bin"
wrapper = W + "/root/usr/local/lib/mini/mini-shell-ssh"
def height():
    try: return int(open(root + "/store/node/store.head-anchor", "rb").read()[:0] or 0)
    except Exception: return -1
t = str(int(time.time()))
with open(out, "a") as f:
    for spec in specs:
        member, label, line = spec.split("|", 2)
        home = f"{root}/sessions/{member}"; trace = os.path.join(os.environ.get("CENSUS_TRACE_DIR", W + "/census"), f"trace-{member}.jsonl")
        ws = root + "/store/node/sponsor" if member == "ember" else home + "/workspace"
        args = [wrapper, mini, cand + "/minidregg-host", root + "/store/node/deployment/pinned-config.json",
                root + "/store/node/public/mini.sock", ws, home]
        for i in range(reps):
            n = f"{t}{i}"
            l = line.replace("{i}", str(i)).replace("{t}", t).replace("{n}", n)
            open(trace, "w").close()
            env = dict(os.environ, SSH_ORIGINAL_COMMAND=l, HOME=home, MINI_TRACE=trace)
            t0 = time.perf_counter()
            p = subprocess.run(args, env=env, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
            wall = (time.perf_counter() - t0) * 1000
            hops = []
            for r in open(trace):
                try: j = json.loads(r); hops.append([j["kind"], j["what"], round(j["ms"], 3)])
                except Exception: pass
            row = {"label": label, "member": member, "line": l, "rep": i, "wall": round(wall, 2),
                   "rc": p.returncode, "hops": hops}
            if p.returncode: row["err"] = p.stderr.decode(errors="replace")[-300:]
            f.write(json.dumps(row) + "\n"); f.flush()
            lt = sum(h[2] for h in hops if h[0] == "line")
            print(f"{label:22s} rep{i} wall={wall:7.1f} line={lt:7.1f} rc={p.returncode} " +
                  " ".join(f"{h[1]}:{h[2]:.1f}" for h in hops if h[0] == "host" and h[2] >= 1.0), flush=True)
        if verbose:
            print(p.stdout.decode(errors="replace")[-1500:]); print(p.stderr.decode(errors="replace")[-600:])
