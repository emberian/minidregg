#!/usr/bin/env bash
# Requires qualified module oleans; never builds the whole dependency closure.
# A process-restart check, not an fsync or native admission qualification.
set -euo pipefail
if [ "$#" -ne 1 ]; then
  printf 'usage: %s SCRATCH_DIRECTORY\n' "$0" >&2
  exit 2
fi
checkpoint_dir="$1"
mkdir -p "$checkpoint_dir"
for cut in 7 3 12; do
  snapshot="$checkpoint_dir/bend-continuation-$cut.bin"
  lake env lean --run Host/BendContinuationProbe.lean save "$snapshot" "$cut"
  lake env lean --run Host/BendContinuationProbe.lean resume "$snapshot" "$cut"
done
