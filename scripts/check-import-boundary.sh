#!/usr/bin/env bash
# check-import-boundary.sh — mechanical enforcement of the ATLAS §7
# candidate-independence boundary:
#
#   Theory/ (and the Theory.lean root) may import ONLY Mathlib and Theory itself
#           — the metatheory must never know the candidate (no Kernel/Pred/
#           Effects/Compiler/Loom/Assurance imports).
#   Loom/   (and the Loom.lean root) may import ONLY Mathlib, Theory, and Loom.
#
# Exits 1 listing every offending import line; prints OK lines when clean.
set -u
cd "$(dirname "$0")/.." || exit 1

status=0

# check_boundary <label> <allowed-module-prefix-regex> <file...>
check_boundary() {
  local label="$1" allowed="$2"
  shift 2
  if [ "$#" -eq 0 ]; then
    echo "OK: ${label}: no .lean files to check"
    return
  fi
  local offenders
  offenders=$(grep -HnE '^import[[:space:]]' "$@" 2>/dev/null \
    | grep -vE ":[0-9]+:import[[:space:]]+(${allowed})(\.|[[:space:]]|$)")
  if [ -n "${offenders}" ]; then
    echo "FAIL: ${label}: imports outside the allowed set {${allowed}}:"
    echo "${offenders}" | sed 's/^/  /'
    status=1
  else
    echo "OK: ${label}: all imports within {${allowed}}"
  fi
}

# shellcheck disable=SC2046  # controlled filenames, no spaces
check_boundary "Theory" 'Mathlib|Minidregg\.Theory|Theory' \
  Theory.lean $(find Theory -name '*.lean' 2>/dev/null | sort)

check_boundary "Loom" 'Mathlib|Minidregg\.Theory|Minidregg\.Loom|Theory|Loom' \
  Loom.lean $(find Loom -name '*.lean' 2>/dev/null | sort)

exit "${status}"
