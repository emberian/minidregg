#!/bin/bash
# Each FAULT-n definition in planted-api-faults.lean must be refused by the elaborator.
set -u
cd "$(git rev-parse --show-toplevel)"
out=$(lake env lean scripts/kn2/planted-api-faults.lean 2>&1)
echo "$out"
fail=0
for line in $(grep -n '^def fault' scripts/kn2/planted-api-faults.lean | cut -d: -f1); do
  next=$((line + 4))
  if ! echo "$out" | grep -qE "planted-api-faults.lean:($line|$((line+1))|$((line+2))|$((line+3))|$next):"; then
    echo "PLANTED FAULT ELABORATED (no error near line $line)"; fail=1
  fi
done
[ $fail = 0 ] && echo "PASS: every planted API fault is refused" || { echo "FAIL"; exit 1; }
