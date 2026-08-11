#!/usr/bin/env bash
set -euo pipefail

repo_root=$(cd "$(dirname "$0")/.." && pwd)
cd "$repo_root"

# The address-free policy API was removed during the committed-policy cutover.
# Keep a source check so generated/example code cannot quietly revive the
# obsolete arbitrary constructor or projection spelling.
if matches=$(rg -n --glob '*.lean' \
    'verifyPolicy[[:space:]]*:|\.verifyPolicy\b' \
    Theory Compiler Kernel Assurance Loom Pred 2>/dev/null); then
  printf '%s\n' 'ERROR: obsolete address-free policy verifier reference(s):' >&2
  printf '%s\n' "$matches" >&2
  exit 1
fi

printf '%s\n' 'OK: no obsolete address-free policy verifier constructors or projections'
