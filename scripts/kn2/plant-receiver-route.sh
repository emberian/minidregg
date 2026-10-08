#!/bin/bash
# T1.5(a) static plant: bypass the current-key check on receiveLoaded's retry
# branch, then require the theorem over receiveLoaded itself to stop compiling.
# The checked-in source is never edited; the mutation and Lean output live in a
# temporary directory which is removed on exit.
# Usage (from the tree root): scripts/kn2/plant-receiver-route.sh
set -eu

plant_root=$(git rev-parse --show-toplevel)
plant_tmp=$(mktemp -d)
trap 'rm -r -- "$plant_tmp"' EXIT
plant_source="$plant_root/Kernel/ObjectiveActivityReceiver.lean"
plant_mutant="$plant_tmp/ObjectiveActivityReceiver.lean"
plant_log="$plant_tmp/lean.log"

cp "$plant_source" "$plant_mutant"
perl -0pi -e 's/return replayAnswer \(← verifyRetry deployment profile ambient native durable ingress\)\n      \(\.retry prior disposition\)/return replayAnswer (.ok ())\n      (.retry prior disposition)/' "$plant_mutant"

# Assert that this run really planted the retry bypass before trusting its verdict.
test "$(grep -Fc 'return replayAnswer (.ok ())' "$plant_mutant")" -eq 2
if grep -Fq 'return replayAnswer (← verifyRetry deployment profile ambient native durable ingress)' "$plant_mutant"; then
  echo "PLANT DID NOT APPLY: retry still calls verifyRetry"
  exit 1
fi

if (cd "$plant_root" && lake env lean "$plant_mutant" >"$plant_log" 2>&1); then
  echo "NOT RED: receiveLoaded_recorded_routes accepted a retry verification bypass"
  exit 1
fi

if grep -Fq 'unsolved goals' "$plant_log" && grep -Fq 'verifyRetry deployment profile ambient native durable ingress' "$plant_log"; then
  echo "RED as intended: receiveLoaded_recorded_routes rejects retry verifyRetry bypass"
  grep -m1 'error: unsolved goals' "$plant_log"
else
  echo "UNEXPECTED RED: mutated source failed outside the routing theorem"
  sed -n '1,80p' "$plant_log"
  exit 1
fi
