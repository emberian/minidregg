#!/usr/bin/env python3
"""Shrink a program on which the C backend and the Lean machine disagree.

usage: cdiff_minimize.py PACKET_DIR OUT_DIR --bin-dir DIR --runtime RUNTIME_C
                         [--heap N --stack N --ticks N] [--jobs N] [--max-rounds N]

PACKET_DIR holds source.core.json, source.typed.json and responses.json (a packet written
by `objective-cdiff-gen gen`). Each round asks `objective-cdiff-gen shrink` for every
one-step reduction that still passes the real type checker (a node replaced by a literal,
or by one of its own children), smallest first, and runs the differential on them in
batches; the first candidate that fails WITH THE SAME SIGNATURE (the same differing
fields, or the same failure kind) becomes the new program. It stops when no candidate
fails the same way. A reduction that fails differently is a different finding and is not
followed. The result is a type-correct program no single step of which can be removed.
OUT_DIR gets: original/ and minimized/ packets, rounds.log, and the failing lines of the
minimized program (failure.txt).
"""
import argparse, json, os, re, shutil, subprocess, sys, time

HERE = os.path.dirname(os.path.abspath(__file__))
FILES = ["source.core.json", "source.typed.json", "responses.json"]


def signature(line):
    m = re.search(r"differ=(\[[^\]]*\])", line)
    if m:
        return "differ" + m.group(1)
    for kind in ("lean-suite", "c-run", "cc", "harness", "generated-packet"):
        if f" {kind}" in line.split(":")[0] or f" {kind}:" in line:
            return kind
    return "other"


def run_differential(root, work, log, a, extra=()):
    cmd = [sys.executable, os.path.join(HERE, "differential.py"), root, work, log,
           "--jobs", str(a.jobs), "--serve", "--lean-bin", os.path.join(a.bin_dir, "objective-cdiff"),
           "--precompile-runtime", "--runtime", a.runtime, "--heap", a.heap, "--stack", a.stack,
           "--ticks", a.ticks] + list(extra)
    subprocess.run(cmd, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
    try:
        return [l.rstrip("\n") for l in open(log)]
    except FileNotFoundError:
        return []


def fail_lines(lines):
    return [l for l in lines if l.startswith("FAIL ")]


def packet_root(tmp, packet_dir, name="p"):
    root = os.path.join(tmp, "root")
    os.makedirs(root, exist_ok=True)
    dest = os.path.join(root, name)
    shutil.copytree(packet_dir, dest, dirs_exist_ok=True)
    entry = {"name": name, "status": "ok", "core": f"{dest}/source.core.json",
             "typed": f"{dest}/source.typed.json", "responses": f"{dest}/responses.json"}
    json.dump([entry], open(os.path.join(root, "index.json"), "w"))
    return root


def main():
    p = argparse.ArgumentParser()
    p.add_argument("packet"); p.add_argument("out")
    p.add_argument("--bin-dir", required=True); p.add_argument("--runtime", required=True)
    p.add_argument("--heap", default="20000"); p.add_argument("--stack", default="20000")
    p.add_argument("--ticks", default="20000"); p.add_argument("--jobs", type=int, default=4)
    p.add_argument("--max-rounds", type=int, default=300); p.add_argument("--batch", type=int, default=48)
    a = p.parse_args()
    a.bin_dir = os.path.abspath(a.bin_dir); a.runtime = os.path.abspath(a.runtime)
    out = os.path.abspath(a.out); os.makedirs(out, exist_ok=True)
    tmp = os.path.join(out, "tmp"); shutil.rmtree(tmp, ignore_errors=True); os.makedirs(tmp)
    rounds = open(os.path.join(out, "rounds.log"), "w")
    def say(s):
        print(s, flush=True); rounds.write(s + "\n"); rounds.flush()
    shutil.copytree(a.packet, os.path.join(out, "original"), dirs_exist_ok=True)
    current = os.path.join(tmp, "current"); shutil.copytree(a.packet, current)
    lines = run_differential(packet_root(os.path.join(tmp, "r0"), current), os.path.join(tmp, "w0"), os.path.join(tmp, "l0.log"), a)
    fails = fail_lines(lines)
    if not fails:
        say("minimize: the packet does not fail under this runtime/binary/limits; nothing to shrink"); return 2
    target = signature(fails[0])
    say(f"minimize: target signature {target}; first failing line: {fails[0][:240]}")
    shrinker = os.path.join(a.bin_dir, "objective-cdiff-gen")
    for rnd in range(1, a.max_rounds + 1):
        cdir = os.path.join(tmp, f"cand{rnd}")
        r = subprocess.run([shrinker, "shrink", f"{current}/source.typed.json", f"{current}/responses.json", cdir],
                           capture_output=True, text=True)
        if r.returncode != 0:
            say(f"round {rnd}: shrinker refused: {r.stderr.strip()[:200]}"); break
        info = json.loads(r.stdout.strip().splitlines()[-1])
        index = json.load(open(os.path.join(cdir, "index.json")))
        say(f"round {rnd}: size {info['size']}, {len(index)} candidates")
        found = None
        for lo in range(0, len(index), a.batch):
            chunk = index[lo:lo + a.batch]
            sub = os.path.join(tmp, f"sub{rnd}-{lo}"); os.makedirs(sub)
            json.dump(chunk, open(os.path.join(sub, "index.json"), "w"))
            clines = run_differential(sub, os.path.join(tmp, f"wk{rnd}-{lo}"), os.path.join(tmp, f"lg{rnd}-{lo}.log"), a)
            by_name = {}
            for l in fail_lines(clines):
                by_name.setdefault(l.split()[1], []).append(signature(l))
            for entry in chunk:   # smallest first
                if target in by_name.get(entry["name"], []):
                    found = entry; break
            shutil.rmtree(os.path.join(tmp, f"wk{rnd}-{lo}"), ignore_errors=True)
            if found: break
        if not found:
            say(f"round {rnd}: no one-step shrink fails the same way: minimal"); break
        new = os.path.join(tmp, f"current{rnd}")
        shutil.copytree(os.path.dirname(found["core"]), new)
        say(f"round {rnd}: -> {found['name']} (size {found['nodes']})")
        shutil.rmtree(current, ignore_errors=True); current = new
        shutil.rmtree(cdir, ignore_errors=True)
    mini = os.path.join(out, "minimized"); shutil.rmtree(mini, ignore_errors=True); shutil.copytree(current, mini)
    final = run_differential(packet_root(os.path.join(tmp, "rf"), mini), os.path.join(tmp, "wf"), os.path.join(tmp, "lf.log"), a)
    open(os.path.join(out, "failure.txt"), "w").write("\n".join(fail_lines(final)) + "\n")
    shutil.rmtree(tmp, ignore_errors=True)
    say(f"minimize: done; minimized packet at {mini}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
