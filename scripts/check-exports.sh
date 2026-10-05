#!/usr/bin/env bash
# check-exports.sh — every Lean `@[export sym]` has a caller, or a reason.
#
# An exported symbol is a C ABI promise. One that no native code links is a
# claim ("Rust calls this") that nothing checks; the census of 2026-10-01 found
# two, both uncalled, and they were deleted. The rule:
#   * every `@[export sym]` in a tracked .lean file must be named in the LIVE code of a
#     tracked file under native/ (.rs .c .h build.rs): a name in a comment, or in a
#     `#[cfg(any())]` item that no build compiles, is not a call,
#     or be listed in scripts/gates/exports-allowlist.tsv (`sym<TAB>reason`);
#   * every allowlist row must still name an export, and an export native code now calls
#     must leave the allowlist (a stale row is red either way);
#   * `@[extern]` and `implemented_by` are counted and printed, since each is a
#     place the compiled code is not the Lean definition.
set -euo pipefail
root=$(git -C "$(dirname "$0")" rev-parse --show-toplevel)
cd "$root"
python3 - <<'PY'
import re, subprocess, sys
sys.path.insert(0, "scripts")
from rust_scan import live_code
ALLOW = "scripts/gates/exports-allowlist.tsv"
ls = lambda *g: [f for f in subprocess.check_output(["git", "ls-files", "-z", "--", *g]).decode().split("\0") if f]
exports, externs, impl = [], [], []
for f in ls("*.lean"):
    text = open(f, encoding="utf-8").read()
    # `--` comments out, newlines kept (line numbers survive); an attribute list may sit
    # across lines and hold several attributes: `@[export sym, noinline]`, `@[inline, export sym]`
    code = "\n".join(l.split("--", 1)[0] for l in text.split("\n"))
    line_of = lambda pos: code.count("\n", 0, pos) + 1
    for attrs in re.finditer(r"@\[([^\]]*)\]", code):
        for m in re.finditer(r"(?:^|,)\s*export\s+([A-Za-z_][A-Za-z0-9_]*)\s*(?=,|$)", attrs.group(1)):
            exports.append((m.group(1), f"{f}:{line_of(attrs.start())}"))
        if re.search(r"(?:^|,)\s*extern\b", attrs.group(1)): externs.append(f"{f}:{line_of(attrs.start())}")
        if re.search(r"(?:^|,)\s*implemented_by\b", attrs.group(1)): impl.append(f"{f}:{line_of(attrs.start())}")
# a call is a name in LIVE code: not in a comment (line, trailing or block) and not in a
# `#[cfg(any())]` item no build compiles (scripts/rust_scan.py); string literals count, since the
# calls are dlsym("name") literals
blob = "\n".join(live_code(open(f, encoding="utf-8", errors="replace").read())
                 for f in ls("native/*.rs", "native/*.c", "native/*.h"))
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
        if sym in allow:
            print(f"exports: FAIL: allowlist row {sym} is stale: native code names it now; delete the row")
            bad += 1
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
