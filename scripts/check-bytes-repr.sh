#!/usr/bin/env bash
# check-bytes-repr.sh — runtime bytes are ByteArray: a ratchet on `List UInt8` in executed code.
#
# A `List UInt8` costs ~24 bytes of memory per byte (a cons cell and a boxed scalar) and a pointer
# chase per byte; a `ByteArray` costs one. Runtime data, anything compiled into a deployed
# executable and run, is `ByteArray`. `List UInt8` stays only as the spec-level model: in Theory/,
# and in statements, each executable function tied to it by an `_eq` theorem.
#
# This gate counts `List UInt8` (comments stripped) in the modules the deployed executables are
# built from: the import closure of the Store Host (Host.Main) and the consent providers
# (Host.ClientConsentSession, Host.ClientConsentSpecializedSession), Theory/ excluded. It is red
# when the count RISES past the one number in scripts/gates/bytes-repr.max. Every commit that
# moves a byte path to ByteArray lowers the ceiling:
#   scripts/check-bytes-repr.sh --update "what moved"
# and it also prints the whole tree's count (outside Theory/) and the worst files, for orientation.
set -euo pipefail
root=$(git -C "$(dirname "$0")" rev-parse --show-toplevel)
cd "$root"
python3 - "$@" <<'PY'
import re, subprocess, sys, datetime, os
sys.path.insert(0, "scripts")
from lean_imports import file_imports
MAX = "scripts/gates/bytes-repr.max"
ROOTS = ["Host.Main", "Host.ClientConsentSession", "Host.ClientConsentSpecializedSession"]
libs = re.findall(r'^\[\[lean_lib\]\]\s*\nname\s*=\s*"([^"]+)"', open("lakefile.toml").read(), re.M)
files = [f for f in subprocess.check_output(["git", "ls-files", "-z", "--", "*.lean"]).decode().split("\0") if f]
mods = {}
for f in files:
    if f.split("/")[0].removesuffix(".lean") in libs:
        mods[f[:-5].replace("/", ".")] = f
def closure(roots):
    seen, stack = set(), list(roots)
    while stack:
        m = stack.pop()
        if m.startswith("Minidregg.") and m[len("Minidregg."):] in mods:
            m = m[len("Minidregg."):]
        if m in seen or m not in mods:
            continue
        seen.add(m)
        stack.extend(file_imports(mods[m]))
    return seen
BLOCK = re.compile(r"/-.*?-/", re.S)
LINE = re.compile(r"--[^\n]*")
PAT = re.compile(r"\bList\s+UInt8\b")
def count(path):
    text = open(path, encoding="utf-8").read()
    return len(PAT.findall(LINE.sub("", BLOCK.sub("", text))))
deployed = sorted(m for m in closure(ROOTS) if not m.startswith("Theory."))
per = {m: count(mods[m]) for m in deployed}
total = sum(per.values())
tree = sum(count(f) for f in files if not f.startswith("Theory/"))
bylib = {}
for m, c in per.items():
    bylib[m.split(".")[0]] = bylib.get(m.split(".")[0], 0) + c
print(f"bytes-repr: `List UInt8` in the deployed executables' closure (Theory/ excluded): {total} in "
      f"{sum(1 for c in per.values() if c)} of {len(deployed)} modules ("
      + ", ".join(f"{l} {c}" for l, c in sorted(bylib.items(), key=lambda kv: -kv[1])) + f"); whole tree outside Theory/: {tree}")
for m, c in sorted(per.items(), key=lambda kv: -kv[1])[:12]:
    print(f"  {c:5d}  {mods[m]}")
HEADER = ("# The CEILING on `List UInt8` occurrences in the deployed executables' import closure (Theory/\n"
          "# excluded, comments stripped): scripts/check-bytes-repr.sh is red when the count RISES past it.\n"
          "# Each commit that moves a byte path to ByteArray lowers it with\n"
          "#   scripts/check-bytes-repr.sh --update REASON\n")
def read_max():
    for l in open(MAX):
        l = l.strip()
        if l and not l.startswith("#"):
            return int(l.split()[0])
    sys.exit(f"bytes-repr: no ceiling in {MAX}")
if "--update" in sys.argv:
    i = sys.argv.index("--update")
    reason = sys.argv[i + 1].strip() if i + 1 < len(sys.argv) else ""
    if not reason:
        sys.exit("bytes-repr: --update needs a reason")
    if os.path.exists(MAX) and total > read_max() and "--raise" not in sys.argv:
        sys.exit(f"bytes-repr: {total} is over the ceiling {read_max()}; raising it needs --raise and a reason")
    old = open(MAX).read().splitlines() if os.path.exists(MAX) else []
    log = [l for l in old if l.startswith("# updated ")]
    log.append(f"# updated {datetime.date.today()}: {total} (tree {tree}): {reason}")
    with open(MAX, "w") as fh:
        fh.write(HEADER + "\n".join(log) + "\n" + f"{total}\n")
    print(f"bytes-repr: ceiling set to {total}")
    sys.exit(0)
if not os.path.exists(MAX):
    sys.exit(f"bytes-repr: no ceiling at {MAX}; run with --update REASON")
ceiling = read_max()
if total > ceiling:
    print(f"bytes-repr: FAIL: {total} occurrences of `List UInt8` in executed modules, over the ceiling {ceiling} "
          f"({MAX}). Runtime bytes are ByteArray; a spec model lives in Theory/ with an `_eq` theorem.")
    sys.exit(1)
print(f"bytes-repr: OK: {total}, ceiling {ceiling}"
      + (" (lower it: scripts/check-bytes-repr.sh --update REASON)" if total < ceiling else ""))
PY
