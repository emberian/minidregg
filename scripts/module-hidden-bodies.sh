#!/usr/bin/env bash
# scripts/module-hidden-bodies.sh FILE.lean -- which imported definitions FILE reaches without their bodies.
#
# Under the module system an imported definition its home module does not expose arrives as an AXIOM
# (no value): `decide`, `rfl` and `simp [f]` through it get stuck. This walks every definition FILE
# itself declares, through the bodies it can see, and prints each reachable body-less constant that
# is not a real axiom, grouped by home module: the `import all` lines FILE needs
# (scripts/lean-modularize.py RULES / PER_FILE). Runs `lake lean` on a temporary copy of FILE at
# FILE's own path (so private names and the module name are FILE's), then restores FILE.
set -euo pipefail
f=$1; root=$(git rev-parse --show-toplevel); cd "$root"
bak=$(mktemp "${TMPDIR:-/tmp}/hidden-bodies.XXXXXX"); cp -p "$f" "$bak"; trap 'cp -p "$bak" "$f"; rm -f "$bak"' EXIT
cat >> "$f" <<'LEAN'

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let real : NameSet := [``propext, ``Classical.choice, ``Quot.sound, ``sorryAx].foldl (·.insert ·) {}
  let mut seen : NameSet := {}
  let mut stack : Array Name := env.constants.map₂.toList.map (·.1) |>.toArray
  let mut hidden : Std.HashMap Name (Array Name) := {}
  while h : stack.size > 0 do
    let n := stack.back; stack := stack.pop
    if seen.contains n then continue
    seen := seen.insert n
    match env.find? n with
    | some (.axiomInfo ax) =>
      -- a proof (Prop-typed) never needs unfolding; only data definitions do
      let isProof ← liftTermElabM <| Meta.isProp ax.type
      unless real.contains n || isProof || (env.getModuleIdxFor? n).isNone do
        let m := env.header.moduleNames[(env.getModuleIdxFor? n).get!.toNat]!
        hidden := hidden.insert m ((hidden.getD m #[]).push n)
    | some (.defnInfo v) => stack := stack ++ v.value.getUsedConstants
    | some (.opaqueInfo v) => stack := stack ++ v.value.getUsedConstants
    | some (.inductInfo v) => stack := stack ++ v.ctors.toArray
    | _ => pure ()
  for (m, ns) in hidden.toList do
    logInfo m!"HIDDEN import all {m}  -- {ns.toList.take 6}"
LEAN
lake lean "$f" 2>&1 | grep -o 'HIDDEN .*' | sed 's/^HIDDEN //' | sort
