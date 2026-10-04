#!/usr/bin/env bash
# check-import-boundary.sh — the library tier rule, as the tree obeys it.
#
# Each row names the libraries a library's modules may import. It is the rule
# measured on 2026-10-01 (lane GATES), not an aspiration, and every row is
# checked on every tracked .lean file (direct imports; Theory and Selvage are
# closed under their rows, so their transitive closure is checked too):
#
#   Theory    Mathlib Lean Theory                              the metatheory never knows the candidate
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
#
# DELIBERATE RELAXATION (76757030, 2026-10-03): the Theory and Kernel rows were
# widened from {Mathlib, Theory[, Pred, Compiler, Kernel]} to also admit Lean,
# Std and Init. It is a weaker check than the 2026-10-01 table, kept on purpose:
# `import Lean` brings the elaborator and the compiler's own data structures
# into the candidate-independent metatheory, and the closure claim above
# ("Theory is closed under its row") now holds only modulo the toolchain. The
# edge counts printed on every run (Theory -> Lean:N Std:N, Kernel -> Init:N
# Std:N) are where a new such import shows; narrowing these rows again is a
# table edit here, recorded in docs/LEAN-QUALIFICATION.md (import tiers).
#
# NARROWED (2026-10-04): the Theory row loses Std and Init. Their
# only Theory importers were the deleted upstream-Bend kernel and its machine;
# Theory -> Lean remains (the Objective Bend Core4 definitions import Lean).
# A new edge between libraries is a red until this table is changed on purpose.
# Exits 1 listing every offending import line, with the edge it would add.
set -u
cd "$(dirname "$0")/.." || exit 1
python3 - <<'PY'
import re, subprocess, sys
sys.path.insert(0, "scripts")
from lean_imports import header_imports
ALLOWED = {
    "Theory":    {"Mathlib", "Lean", "Theory"},
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
    # the header as Lean reads it: an indented import, several on one line, and the
    # public/meta/private modifiers all count (scripts/lean_imports.py)
    for imported in header_imports(open(f, encoding="utf-8").read()):
        parts = imported.split(".")
        tgt = parts[1] if parts[0] == "Minidregg" and len(parts) > 1 else parts[0]
        counts[(lib, tgt)] = counts.get((lib, tgt), 0) + 1
        if tgt not in ALLOWED[lib]:
            bad.append(f"  {f}: import {imported}   [new edge {lib} -> {tgt}]")
for lib in ALLOWED:
    edges = sorted((t, c) for (l, t), c in counts.items() if l == lib)
    print(f"{lib:9s} -> " + " ".join(f"{t}:{c}" for t, c in edges))
if bad:
    print("FAIL: import-boundary: imports outside the tier table (scripts/check-import-boundary.sh):")
    print("\n".join(bad))
    sys.exit(1)
print("OK: import-boundary: every import of " + " ".join(ALLOWED) + " is inside its row")
PY
