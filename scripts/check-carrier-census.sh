#!/usr/bin/env bash
# The other half of ATLAS law 2's gate: which load-bearing carriers have no
# witness?  Fails on a broken instrument (self-test), never on the count --
# 521 unwitnessed carriers is today's honest number, not a regression to gate.
#
# usage: scripts/check-carrier-census.sh [--top N]
set -euo pipefail

top=${2:-40}
cd "$(dirname "$0")/.."

if ! output=$(lake env lean scripts/CarrierCensus.lean 2>&1); then
  echo "$output" >&2
  echo "carrier-census: FAILED (see above)" >&2
  exit 1
fi

echo "$output"

if ! grep -q "^self-test *: PASS" <<<"$output"; then
  echo "carrier-census: self-test did not pass" >&2
  exit 1
fi
