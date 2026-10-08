#!/usr/bin/env bash
# Shared temporary source overlay and row-verdict checks. No live-tree mutation.
drift_setup() { # ROW RESULTS_ROOT
  ROW=$1
  RESULTS=$(realpath -m "$2")
  HERE=$(CDPATH='' cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
  SRC=$(CDPATH='' cd -- "$HERE/../.." && pwd)
  TIP=${DRIFT_TIP:-e0a8ba21a39d92b470cc331fd16ea0408f608b1f}
  [[ ! -e $RESULTS ]] || { echo "plant results already exist: $RESULTS" >&2; exit 64; }
  mkdir -p "$RESULTS"
  TEMP=$(mktemp -d /tmp/drift-source.XXXXXX)
  trap 'rm -rf "$TEMP"' EXIT
}

drift_copy() { # LABEL DRIVER (relative to SRC)
  LABEL=$1
  COPY=$TEMP/$LABEL
  DRIVER=$2
  mkdir -p "$COPY"
  # Retain each driver's relative helpers, without copying custody or build state.
  local path part directory
  for path in "$SRC"/*; do ln -s "$path" "$COPY/$(basename "$path")"; done
  directory=${DRIVER%/*}
  local prefix= source_dir=$SRC copy_dir=$COPY
  IFS=/ read -r -a parts <<<"$directory"
  for part in "${parts[@]}"; do
    source_dir=$source_dir/$part
    copy_dir=$copy_dir/$part
    rm "$copy_dir"
    mkdir "$copy_dir"
    for path in "$source_dir"/*; do ln -s "$path" "$copy_dir/$(basename "$path")"; done
  done
  rm "$COPY/$DRIVER"
  cp "$SRC/$DRIVER" "$COPY/$DRIVER"
}

drift_replace() { # OLD NEW: assert exact mutation, then caller also greps its shape
  python3 - "$COPY/$DRIVER" "$1" "$2" <<'PY'
from pathlib import Path
import sys
p, old, new = sys.argv[1:]
path = Path(p)
source = path.read_text()
assert source.count(old) == 1, ("plant must mutate exactly once", old, source.count(old))
changed = source.replace(old, new)
assert changed != source and old not in changed
path.write_text(changed)
PY
}

drift_red() {
  local rc=0
  bash "$HERE/plant-drift-rows.sh" "$ROW" "$RESULTS/$LABEL" "$COPY" \
    >"$RESULTS/$LABEL.runner.log" 2>&1 || rc=$?
  [[ $rc == 1 ]] || { echo "plant $LABEL expected row failure, got $rc" >&2; exit 1; }
  EVIDENCE=$RESULTS/$LABEL/$TIP/rows/$ROW
  awk -F '\t' -v row="$ROW" '$1 == row && $2 == "FAIL" {red=1} END {exit !red}' \
    "$RESULTS/$LABEL/$TIP/results.tsv"
}
