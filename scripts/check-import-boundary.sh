#!/usr/bin/env bash
# check-import-boundary.sh — the library tier rule, as the tree obeys it.
#
# Each row names the libraries a library's modules may import. Every row is checked on every
# tracked .lean file's direct imports. Theory, Selvage and Effects are closed under their rows
# (each row names only libraries whose own rows lie inside it), so for those three the
# transitive closure is checked too.
#
#   Theory    Mathlib Lean Theory                                           the metatheory never knows the candidate
#   Selvage   Mathlib Theory Selvage                                        the proof system knows only the metatheory
#   Effects   Mathlib Lean Theory Effects                                   the derivation engine: a generator over Theory
#   Pred      Mathlib Theory Pred
#   Kernel    Mathlib Lean Std Init Theory Effects Pred Compiler Kernel
#   Compiler  Mathlib Lean Std Init Theory Effects Pred Kernel Selvage Assurance Compiler
#   Assurance Mathlib Theory Pred Kernel Compiler Selvage Assurance
#   Host      Mathlib Lean Std Theory Pred Kernel Compiler Host           (no Selvage, Assurance or Effects)
#
# The tier line: Theory < Selvage < Effects < Pred < {Kernel, Compiler, Assurance} < Host.
# It is one linear order of the library DAG: Selvage, Effects and Pred do not import each other.
# Effects is the GENERATOR whose outputs Kernel and Compiler consume (the derived Hosted*
# descriptors, the EffectSpec engine), so it sits below them and never imports Kernel,
# Compiler or Host. Keystones stated OVER the deployed kernel are consumers of the engine and
# live in Kernel (Kernel/EffectsRevival/, Kernel/MoveEffect.lean). Candidate-independent
# algebra the engine needs lives in Theory (Theory/Signature, Theory/StreamCodec,
# Theory/NatDigits255Fast).
#
# Kernel/Compiler/Assurance are ONE strongly connected group at library level (Kernel<->Compiler
# and Compiler<->Assurance both occur; acyclic only per module), so "Compiler cannot import
# Kernel" is not a rule of this tree. Pred imports only Mathlib and Theory (its hash-equality
# leaf shares Theory's cSHAKE256 sponge), so it sits below the group. Host is the only sink:
# no library imports it (only the roots Minidregg and AxiomCensus do).
#
# Lean/Std/Init are the language and standard library, not candidate code. Theory and Effects
# admit Lean (the Objective Bend Core4 definitions; Lean.Data.Json for the hosted schema), so
# their closure claim holds modulo the toolchain; the edge counts printed below are where a new
# such import shows. Kernel and Compiler admit Std/Init; Host admits Std (Std.Internal.Async.TCP,
# already reached through `import Lean`). `import all Init.X` adds no module to any closure
# (every Lean file imports Init) and is not counted.
#
# The cycle check: from the counted library edges this computes the strongly connected
# components and fails if any component other than the group above has more than one library,
# or if Theory, Selvage, Effects, Pred or Host sits on a cycle. It prints the components in
# dependency order.
#
# A new edge between libraries is a red until this table is changed on purpose.
# Exits 1 listing every offending import line, with the edge it would add.
set -u
cd "$(dirname "$0")/.." || exit 1
python3 - <<'PY'
import subprocess, sys
sys.path.insert(0, "scripts")
from lean_imports import header_imports, header_layout
ALLOWED = {
    "Theory":    {"Mathlib", "Lean", "Theory"},
    "Selvage":   {"Mathlib", "Theory", "Selvage"},
    "Effects":   {"Mathlib", "Lean", "Theory", "Effects"},
    "Pred":      {"Mathlib", "Theory", "Pred"},
    "Kernel":    {"Mathlib", "Lean", "Std", "Init", "Theory", "Effects", "Pred", "Compiler", "Kernel"},
    "Compiler":  {"Mathlib", "Lean", "Std", "Init", "Theory", "Effects", "Pred", "Kernel", "Selvage", "Assurance", "Compiler"},
    "Assurance": {"Mathlib", "Theory", "Pred", "Kernel", "Compiler", "Selvage", "Assurance"},
    "Host":      {"Mathlib", "Lean", "Std", "Theory", "Pred", "Kernel", "Compiler", "Host"},
}
GROUP = {"Kernel", "Compiler", "Assurance"}
ACYCLIC = {"Theory", "Selvage", "Effects", "Pred", "Host"}
files = [f for f in subprocess.check_output(["git", "ls-files", "-z", "--", "*.lean"]).decode().split("\0") if f]
bad, counts = [], {}
for f in files:
    lib = f.split("/")[0].removesuffix(".lean")
    if lib not in ALLOWED:
        continue
    # the header as Lean reads it: an indented import, several on one line, and the
    # public/meta/private modifiers all count (scripts/lean_imports.py)
    text = open(f, encoding="utf-8").read()
    core_all = [m for (s, e, _, m) in header_layout(text)[1] if m.startswith("Init.") and text[s:e].split()[-2:-1] == ["all"]]
    for imported in header_imports(text):
        if imported in core_all:
            continue
        parts = imported.split(".")
        tgt = parts[1] if parts[0] == "Minidregg" and len(parts) > 1 else parts[0]
        counts[(lib, tgt)] = counts.get((lib, tgt), 0) + 1
        if tgt not in ALLOWED[lib]:
            bad.append(f"  {f}: import {imported}   [new edge {lib} -> {tgt}]")
for lib in ALLOWED:
    edges = sorted((t, c) for (l, t), c in counts.items() if l == lib)
    print(f"{lib:9s} -> " + " ".join(f"{t}:{c}" for t, c in edges))

# library graph over the candidate libraries, from the counted edges
libs = list(ALLOWED)
succ = {l: sorted({t for (s, t) in counts if s == l and t in ALLOWED and t != l}) for l in libs}
index, low, stack, on, sccs = {}, {}, [], set(), []
def strong(v):
    index[v] = low[v] = len(index)
    stack.append(v); on.add(v)
    for w in succ[v]:
        if w not in index:
            strong(w); low[v] = min(low[v], low[w])
        elif w in on:
            low[v] = min(low[v], index[w])
    if low[v] == index[v]:
        comp = []
        while True:
            w = stack.pop(); on.discard(w); comp.append(w)
            if w == v:
                break
        sccs.append(sorted(comp, key=libs.index))
for l in libs:
    if l not in index:
        strong(l)
# Tarjan emits a component after every component it reaches: that is dependency order
print("library components, dependencies first: " + " < ".join("{" + ", ".join(c) + "}" if len(c) > 1 else c[0] for c in sccs))
cyc = []
for c in sccs:
    if len(c) > 1 and (set(c) & ACYCLIC or not set(c) <= GROUP):
        cyc.append("  cycle through {" + ", ".join(c) + "}")
if bad:
    print("FAIL: import-boundary: imports outside the tier table (scripts/check-import-boundary.sh):")
    print("\n".join(bad))
if cyc:
    print("FAIL: import-boundary: a library cycle outside the Kernel/Compiler/Assurance group:")
    print("\n".join(cyc))
if bad or cyc:
    sys.exit(1)
print("OK: import-boundary: every import of " + " ".join(ALLOWED) + " is inside its row; no library cycle outside {" + ", ".join(sorted(GROUP, key=libs.index)) + "}")
PY
