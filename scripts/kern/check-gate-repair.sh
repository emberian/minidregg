#!/usr/bin/env bash
# Run the kern gate-repair checks through the lane journey runner.
set -uo pipefail
cd "$(git -C "$(dirname "$0")" rev-parse --show-toplevel)" || exit
max_rc=0
check() {
  local name=$1 rc
  shift
  if "$@"; then rc=0; else rc=$?; fi
  printf '%s: rc=%s\n' "$name" "$rc"
  if (( rc > max_rc )); then max_rc=$rc; fi
}
case ${1:-static} in
  generate-surfaces)
    check build-surfaces-generate python3 scripts/lean-build-surfaces.py generate
    ;;
  manifest-evidence)
    # Retain the two scans for per-row statement/module/closure review. This
    # does not admit or pin rows; check-objective-proofs.sh still runs in full.
    mkdir -p build-logs/objective || exit
    check manifest-evidence-theory env OBJECTIVE_MANIFEST_OUT=build-logs/objective/review-theory.out \
      lake env lean scripts/ObjectiveManifest.lean
    check manifest-evidence-mathlib env OBJECTIVE_MANIFEST_OUT=build-logs/objective/review-mathlib.out \
      lake env lean scripts/ObjectiveManifestMathlib.lean
    ;;
  audit-contracts)
    check audit-contracts python3 scripts/kern/audit-gate-contracts.py
    ;;
  static)
    check host-closure bash scripts/check-host-closure.sh
    check full-loaded-ratchet bash scripts/ports/check-full-loaded-callers.sh
    check import-boundary bash scripts/check-import-boundary.sh
    check build-surfaces python3 scripts/lean-build-surfaces.py check
    ;;
  *) printf 'usage: %s [generate-surfaces|manifest-evidence|audit-contracts|static]\n' "$0" >&2; exit 64 ;;
esac
exit "$max_rc"
