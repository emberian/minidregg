#!/usr/bin/env bash
# check-import-boundary.sh — the library tier rule, as the tree obeys it.
#
# Each row names the libraries a library's modules may import. It is the rule
# measured on 2026-10-01 (lane GATES), not an aspiration, and every row is
# checked on every tracked .lean file (direct imports; Theory and Selvage are
# closed under their rows, so their transitive closure is checked too):
#
#   Theory    Mathlib Lean Std Init Theory                     the metatheory never knows the candidate
#   Selvage   Mathlib Theory Selvage             the proof system knows only the metatheory
#   Pred      Mathlib Theory Pred Compiler
#   Kernel    Mathlib Lean Std Init Theory Pred Compiler Kernel
#   Compiler  Mathlib Lean Std Init Theory Pred Kernel Selvage Assurance Compiler
#   Assurance Mathlib Theory Pred Kernel Compiler Selvage Assurance
#   Effects   Mathlib Kernel Compiler Effects
#   Host      Mathlib Lean Theory Pred Kernel Compiler Host  (no Selvage, no Assurance)
#
# Two consequences worth naming: Host and Effects are SINKS (no library imports
# either; only the roots Minidregg and AxiomCensus do), and Pred/Kernel/Compiler/
# Assurance are ONE strongly connected group at library level (Kernel<->Compiler,
# Pred<->Compiler, Compiler<->Assurance all occur; acyclic only per module). So
# "Compiler cannot import Kernel" is NOT a rule of this tree (25 Compiler imports
# of Kernel), and the tier line that does hold is: Theory < Selvage < {the group}
# < {Effects, Host}.
#
# Host also imports Pred for the served law satisfiability query and Mathlib for
# capability-tree deduplication proofs (rooms convergence, 2026-10-02). These do
# not change the sink boundary: no core library imports Host.
# Lean/Std/Init are the language and standard library, not candidate code.
# Candidate-dependent restriction algebra is in Pred/LawComposition.lean.
# A new edge between libraries is a red until this table is changed on purpose.
# Exits 1 listing every offending import line, with the edge it would add.
set -u
cd "$(dirname "$0")/.." || exit 1
python3 - <<'PY'
import re, subprocess, sys
ALLOWED = {
    "Theory":    {"Mathlib", "Lean", "Std", "Init", "Theory"},
    "Selvage":   {"Mathlib", "Theory", "Selvage"},
    "Pred":      {"Mathlib", "Theory", "Pred", "Compiler"},
    "Kernel":    {"Mathlib", "Lean", "Std", "Init", "Theory", "Pred", "Compiler", "Kernel"},
    "Compiler":  {"Mathlib", "Lean", "Std", "Init", "Theory", "Pred", "Kernel", "Selvage", "Assurance", "Compiler"},
    "Assurance": {"Mathlib", "Theory", "Pred", "Kernel", "Compiler", "Selvage", "Assurance"},
    "Effects":   {"Mathlib", "Kernel", "Compiler", "Effects"},
    "Host":      {"Mathlib", "Lean", "Theory", "Pred", "Kernel", "Compiler", "Host"},
}
files = [f for f in subprocess.check_output(["git", "ls-files", "-z", "--", "*.lean"]).decode().split("\0") if f]
bad, counts = [], {}
for f in files:
    lib = f.split("/")[0].removesuffix(".lean")
    if lib not in ALLOWED:
        continue
    for n, line in enumerate(open(f, encoding="utf-8"), 1):
        m = re.match(r"import\s+(\S+)", line)
        if not m:
            continue
        parts = m.group(1).split(".")
        tgt = parts[1] if parts[0] == "Minidregg" and len(parts) > 1 else parts[0]
        counts[(lib, tgt)] = counts.get((lib, tgt), 0) + 1
        if tgt not in ALLOWED[lib]:
            bad.append(f"  {f}:{n}: {line.strip()}   [new edge {lib} -> {tgt}]")
for lib in ALLOWED:
    edges = sorted((t, c) for (l, t), c in counts.items() if l == lib)
    print(f"{lib:9s} -> " + " ".join(f"{t}:{c}" for t, c in edges))
if bad:
    print("FAIL: import-boundary: imports outside the tier table (scripts/check-import-boundary.sh):")
    print("\n".join(bad))
    sys.exit(1)
print("OK: import-boundary: every import of " + " ".join(ALLOWED) + " is inside its row")
PY
