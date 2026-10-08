#!/usr/bin/env bash
# Keep the unchanged transcript gate's temporary state inside this lane.
set -euo pipefail
[[ $# == 1 ]] || { echo 'usage: check-native-fixture-transcripts.sh RUST_TARGET' >&2; exit 2; }
src=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../.." && pwd)
evidence=$(mktemp -d "$src/.lake/kp-transcripts.XXXXXX")
printf 'EVIDENCE %s\n' "$evidence"
export TMPDIR=$evidence CARGO_TARGET_DIR=$1
systemd-run --user --scope -q -p MemoryMax=10G -p MemorySwapMax=0 \
  bash "$src/scripts/check-native-transcripts.sh"
mv -- "$src/build-logs/transcripts-cargo.log" "$evidence/cargo.log"
