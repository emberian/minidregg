#!/usr/bin/env bash
set -euo pipefail

repo_root=$(cd "$(dirname "$0")/.." && pwd)
cd "$repo_root"

# The address-free policy API was removed during the committed-policy cutover.
# Keep a source check so generated/example code cannot quietly revive the
# obsolete arbitrary constructor or projection spelling.
# `git grep`, not `rg`: a missing `rg` exits 127, which `if matches=$(rg ...)` reads as "no matches",
# so on a box without ripgrep the gate printed OK on a tree that held the obsolete spelling
# (measured on the burst boxes, W20-GATE-MUTATION). Exit 0 = a match, 1 = none, anything else = broken.
status=0
matches=$(git grep -nE 'verifyPolicy[[:space:]]*:|\.verifyPolicy\b' -- \
    'Theory/*.lean' 'Compiler/*.lean' 'Kernel/*.lean' 'Assurance/*.lean' 'Selvage/*.lean' 'Pred/*.lean') || status=$?
case $status in
  0)
    printf '%s\n' 'ERROR: obsolete address-free policy verifier reference(s):' >&2
    printf '%s\n' "$matches" >&2
    exit 1 ;;
  1) ;;
  *) printf '%s\n' 'ERROR: the source scan itself failed (git grep)' >&2; exit 2 ;;
esac

printf '%s\n' 'OK: no obsolete address-free policy verifier constructors or projections'
