#!/usr/bin/env bash
# Fail when a tracked library `.lean` module is not reachable by imports from
# `Minidregg`. An unrooted module never elaborates, so nothing in it is checked.
# Library directories are the lean_lib roots in lakefile.toml; scripts/, docs/
# and native/ hold standalone `lake env lean` programs and evidence, not modules.
set -euo pipefail
repo_root=$(git -C "$(dirname "$0")" rev-parse --show-toplevel)
cd "$repo_root"
python3 - <<'PY'
import re, subprocess, sys
libs = re.findall(r'^\[\[lean_lib\]\]\s*\nname\s*=\s*"([^"]+)"',
                  open("lakefile.toml").read(), re.M)
files = subprocess.check_output(["git", "ls-files", "-z", "--", "*.lean"]).decode().split("\0")
mods = {}
for f in files:
    if not f:
        continue
    top = f.split("/")[0].removesuffix(".lean")
    if top in libs:
        mods[f[:-5].replace("/", ".")] = f
def imports(path):
    return [m for m in re.findall(r"^import\s+(\S+)", open(path, encoding="utf-8").read(), re.M)]
seen, stack = set(), ["Minidregg"]
while stack:
    m = stack.pop()
    if m in seen or m not in mods:
        continue
    seen.add(m)
    stack.extend(imports(mods[m]))
if "Minidregg" not in seen:
    sys.exit("build-closure: Minidregg.lean is missing")
unrooted = sorted(set(mods) - seen)
for m in unrooted:
    print(f"build-closure: {mods[m]} is imported by nothing reachable from Minidregg")
print(f"build-closure: {len(seen)} of {len(mods)} library modules rooted")
sys.exit(1 if unrooted else 0)
PY
