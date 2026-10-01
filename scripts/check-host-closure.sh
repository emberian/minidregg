#!/usr/bin/env bash
# check-host-closure.sh — what the deployed Host is built from, pinned.
#
# The umbrella (gate 2) elaborates every library module; the minidregg-host
# executable is built from the import closure of Host.Main only. A theorem in a
# module outside that closure is about something the Host never runs. This gate
# computes the closure of Host.Main over tracked library modules, prints how
# many modules of each library it reaches against the library's total, and
# compares the closure with the pinned list scripts/gates/host-closure.pin.
#
# A module ENTERING or LEAVING the Host closure is a red naming it, until the
# pin is rewritten on purpose:
#   scripts/check-host-closure.sh --update "why the Host now reaches/drops these"
# which records the reason, the date and the per-library counts in the pin.
set -euo pipefail
root=$(git -C "$(dirname "$0")" rev-parse --show-toplevel)
cd "$root"
python3 - "$@" <<'PY'
import re, subprocess, sys, datetime
PIN = "scripts/gates/host-closure.pin"
libs = re.findall(r'^\[\[lean_lib\]\]\s*\nname\s*=\s*"([^"]+)"', open("lakefile.toml").read(), re.M)
files = [f for f in subprocess.check_output(["git", "ls-files", "-z", "--", "*.lean"]).decode().split("\0") if f]
mods = {}
for f in files:
    top = f.split("/")[0].removesuffix(".lean")
    if top in libs:
        mods[f[:-5].replace("/", ".")] = f
def imports(m):
    return re.findall(r"^import\s+(\S+)", open(mods[m], encoding="utf-8").read(), re.M)
def closure(roots):
    seen, stack = set(), list(roots)
    while stack:
        m = stack.pop()
        if m.startswith("Minidregg.") and m[len("Minidregg."):] in mods:
            m = m[len("Minidregg."):]
        if m in seen or m not in mods:
            continue
        seen.add(m)
        stack.extend(imports(m))
    return seen
host = closure(["Host.Main"])
exe_roots = re.findall(r'^\[\[lean_exe\]\]\s*\nname\s*=\s*"[^"]+"\s*\nroot\s*=\s*"([^"]+)"',
                       open("lakefile.toml").read(), re.M)
# what the lake-build gate builds: every lean_lib root and every lean_exe root
umbrella = closure(libs + exe_roots)
lib_of = lambda m: m.split(".")[0]
print(f"{'library':10s} {'Host.Main':>10s} {'gate 2':>9s} {'total':>6s}  built-but-not-deployed")
rows = []
for L in libs:
    tot = sum(1 for m in mods if lib_of(m) == L)
    if tot == 0:
        continue
    h = sum(1 for m in host if lib_of(m) == L)
    u = sum(1 for m in umbrella if lib_of(m) == L)
    rows.append(f"{L} {h} {tot}")
    print(f"{L:10s} {h:>10d} {u:>9d} {tot:>6d}  {u - h}")
host_only = sorted(host - umbrella)
print(f"Host.Main reaches {len(host)} of {len(mods)} library modules; gate 2 builds {len(umbrella)}; "
      f"in the Host closure but not built by gate 2: {len(host_only)}")
for m in host_only:
    print(f"  host-only (not built by gate 2): {m}")
if "--update" in sys.argv:
    i = sys.argv.index("--update")
    reason = sys.argv[i + 1].strip() if i + 1 < len(sys.argv) else ""
    if not reason:
        sys.exit("host-closure: --update needs a reason")
    old = open(PIN).read().splitlines() if __import__("os").path.exists(PIN) else []
    log = [l for l in old if l.startswith("# updated ")]
    log.append(f"# updated {datetime.date.today()}: {reason}  [counts: " + ", ".join(rows) + "]")
    with open(PIN, "w") as fh:
        fh.write("# The import closure of Host.Main (the minidregg-host exe root), one module per line.\n"
                 "# Written by scripts/check-host-closure.sh --update REASON; compared by local-gates.\n")
        fh.write("\n".join(log) + "\n")
        fh.write("\n".join(sorted(host)) + "\n")
    print(f"host-closure: pin rewritten ({len(host)} modules)")
    sys.exit(0)
try:
    pinned = {l.strip() for l in open(PIN) if l.strip() and not l.startswith("#")}
except FileNotFoundError:
    sys.exit(f"host-closure: no pin at {PIN}; run with --update REASON")
entered, left = sorted(host - pinned), sorted(pinned - host)
for m in entered:
    print(f"host-closure: ENTERED the Host closure (not in the pin): {m}")
for m in left:
    print(f"host-closure: LEFT the Host closure (in the pin): {m}")
if entered or left:
    print(f"host-closure: FAIL: {len(entered)} entered, {len(left)} left; rewrite the pin with "
          f"scripts/check-host-closure.sh --update REASON once the change is meant")
    sys.exit(1)
print(f"host-closure: OK: the Host closure equals the pin ({len(host)} modules)")
PY
