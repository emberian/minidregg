#!/usr/bin/env bash
# check-exports.sh — every Lean `@[export sym]` has a caller, or a reason.
#
# An exported symbol is a C ABI promise. One that no native code links is a
# claim ("Rust calls this") that nothing checks; the census of 2026-10-01 found
# two, both uncalled, and they were deleted. The rule:
#   * every `@[export sym]` in a tracked .lean file must be named by a
#     non-comment line of a tracked file under native/ (.rs .c .h build.rs),
#     or be listed in scripts/gates/exports-allowlist.tsv (`sym<TAB>reason`);
#   * every allowlist row must still name an export (a stale row is red);
#   * `@[extern]` and `implemented_by` are counted and printed, since each is a
#     place the compiled code is not the Lean definition.
set -euo pipefail
root=$(git -C "$(dirname "$0")" rev-parse --show-toplevel)
cd "$root"
python3 - <<'PY'
import re, subprocess, sys
ALLOW = "scripts/gates/exports-allowlist.tsv"
ls = lambda *g: [f for f in subprocess.check_output(["git", "ls-files", "-z", "--", *g]).decode().split("\0") if f]
exports, externs, impl = [], [], []
for f in ls("*.lean"):
    for n, line in enumerate(open(f, encoding="utf-8"), 1):
        code = line.split("--", 1)[0]
        for m in re.finditer(r"@\[\s*export\s+([A-Za-z_][A-Za-z0-9_]*)\s*\]", code):
            exports.append((m.group(1), f"{f}:{n}"))
        if re.search(r"@\[\s*extern\b", code): externs.append(f"{f}:{n}")
        if re.search(r"\bimplemented_by\b", code) and "@[" in code: impl.append(f"{f}:{n}")
native = []
for f in ls("native/*.rs", "native/*.c", "native/*.h"):
    for line in open(f, encoding="utf-8", errors="replace"):
        s = line.strip()
        if s.startswith("//") or s.startswith("*") or s.startswith("/*"):
            continue
        native.append(s)
blob = "\n".join(native)
allow = {}
try:
    for l in open(ALLOW, encoding="utf-8"):
        if l.strip() and not l.startswith("#"):
            sym, _, why = l.rstrip("\n").partition("\t")
            allow[sym.strip()] = why.strip()
except FileNotFoundError:
    pass
bad = 0
print(f"exports: {len(exports)} @[export], {len(externs)} @[extern], {len(impl)} implemented_by")
for sym, where in exports:
    if re.search(r"\b" + re.escape(sym) + r"\b", blob):
        print(f"  {sym:40s} {where:50s} called from native/")
    elif sym in allow and allow[sym]:
        print(f"  {sym:40s} {where:50s} allowlisted: {allow[sym]}")
    else:
        print(f"exports: FAIL: {sym} ({where}) is exported and no native code names it; call it, delete it, or allowlist it with a reason")
        bad += 1
for sym in sorted(set(allow) - {s for s, _ in exports}):
    print(f"exports: FAIL: allowlist row {sym} names no @[export]; delete the row")
    bad += 1
for w in externs: print(f"  @[extern] at {w}")
for w in impl: print(f"  implemented_by at {w}")
if bad:
    sys.exit(1)
print(f"exports: OK ({len(exports)} exports, every one called or allowlisted)")
PY
