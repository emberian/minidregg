#!/usr/bin/env bash
# Read-only train runner entrypoint for scoped drift controls and temporary plants.
# Usage: plant-drift-rows.sh m4|hermes RESULTS_ROOT [SOURCE_TREE]
set -euo pipefail
[[ $# == 2 || $# == 3 ]] || { echo "usage: $0 m4|hermes RESULTS_ROOT [SOURCE_TREE]" >&2; exit 64; }
case $1 in m4|hermes) ;; *) echo "unknown drift row: $1" >&2; exit 64 ;; esac
HERE=$(CDPATH='' cd -- "$(dirname -- "$0")" && pwd)
SRC=${3:-$(CDPATH='' cd -- "$HERE/../.." && pwd)}
TRAIN=${DRIFT_TRAIN_SRC:-/srv/lanes/train-prod/src}
TIP=${DRIFT_TIP:-e0a8ba21a39d92b470cc331fd16ea0408f608b1f}
bash "$TRAIN/scripts/pipeline/journey-runner" --once --tip "$TIP" \
  --rows-file "$TRAIN/scripts/pipeline/journey-rows" --results-root "$2" \
  --row "$1" --source-tree "$SRC"
# The runner records row failures in results.tsv; its own exit is not a verdict.
awk -F '\t' -v row="$1" '$1 == row && $2 == "PASS" {ok=1} END {exit !ok}' \
  "$2/$TIP/results.tsv"
