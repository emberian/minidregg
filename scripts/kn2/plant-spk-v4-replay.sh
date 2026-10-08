#!/bin/bash
# Prepare an asserted temporary source mutation, then use the deputy-approved
# lane build route. No compiler is launched by this script. All theorem and
# assertion text is preserved: the event72 dispatcher drops only its replay
# cache payload, while still admitting and matching the completion record.
set -euo pipefail
usage() {
  echo "usage: $0 prepare|apply|restore /tmp/mini-spk-v4-plant-NAME" >&2
  echo "       $0 run COPY BASE_BIN QUALIFICATION_RUST_BIN MUTANT_HOST NEW_RUN_ROOT SIGNED_SPK" >&2
  exit 2
}
[[ $# -ge 2 ]] || usage
mode=$1 copy=$2
[[ $copy == /tmp/mini-spk-v4-plant-* && $copy != *[!a-zA-Z0-9_./-]* ]] || usage
repo=$(cd "$(dirname "$0")/../.." && pwd)
source=$repo/Kernel/NativeHostReplay.lean
needle='| .ok admitted => return .ok { admitted.toDerived with completionV4 := none }'
case $mode in
  prepare)
    [[ $# == 2 && ! -e $copy ]] || usage
    mkdir -m 700 "$copy"
    cp "$source" "$copy/original.lean"
    python3 - "$source" "$copy/mutant.lean" <<'PY'
from pathlib import Path
import sys
source = Path(sys.argv[1]).read_text()
old = '''  if let some ingress := ApplicationLifecycleRetryCompletionV4Ingress.codec.decode bytes then
    match ← admitCompletionV4At config opened reader retry.claimsV4 ingress with
    | .error detail => return .error detail
    | .ok admitted => return .ok admitted.toDerived'''
new = old.rsplit('return .ok admitted.toDerived', 1)[0] + 'return .ok { admitted.toDerived with completionV4 := none }'
assert source.count(old) == 1, 'event72 dispatcher changed'
mutant = source.replace(old, new)
assert mutant != source
assert mutant.count('with completionV4 := none') == 1
# Retain every declaration/proof/check byte outside the one dispatch line.
assert mutant.replace(new, old) == source
Path(sys.argv[2]).write_text(mutant)
PY
    sha256sum "$copy/original.lean" "$copy/mutant.lean" >"$copy/source-sha256.txt"
    echo 'PREPARED event72 replay completion payload omitted in temp copy' | tee "$copy/plant.log"
    ;;
  apply)
    [[ $# == 2 ]] || usage
    sha256sum -c "$copy/source-sha256.txt"
    cmp "$source" "$copy/original.lean"
    cp "$copy/mutant.lean" "$source"
    grep -F "$needle" "$source" | tee -a "$copy/plant.log"
    echo 'BUILD VIA request_build: minidregg-host minidregg-client-consent' | tee -a "$copy/plant.log"
    ;;
  run)
    [[ $# == 7 ]] || usage
    base=$3 rust=$4 host=$5 run=$6 spk=$7
    sha256sum -c "$copy/source-sha256.txt"
    cmp "$source" "$copy/mutant.lean"
    grep -F "$needle" "$source" | tee -a "$copy/plant.log"
    sha256sum "$source" "$host" | tee -a "$copy/plant.log"
    rc=0
    bash "$repo/scripts/spk-platform/journey.sh" r7 "$base" "$rust" "$host" "$run" "$spk" >"$copy/journey.log" 2>&1 || rc=$?
    [[ $rc != 0 ]] || { echo 'PLANT FAIL: omission remained green' >&2; exit 1; }
    grep -F $'R7-retry-create\tPASS\t' "$run/rows.tsv"
    grep -F $'R7-stop-retry\tFAIL\t' "$run/rows.tsv"
    grep -F 'removal_assertions=0' "$run/result.log"
    echo 'RED R7-stop-retry: event72 replay completion payload omitted' | tee -a "$copy/plant.log"
    ;;
  restore)
    [[ $# == 2 ]] || usage
    sha256sum -c "$copy/source-sha256.txt"
    cmp "$source" "$copy/mutant.lean"
    # Restore the saved authored source, including the lane's new proof and
    # axiom checks. This does not require a writable Git index in worker lanes.
    cp "$copy/original.lean" "$source"
    cmp "$source" "$copy/original.lean"
    if grep -Fq "$needle" "$source"; then echo 'PLANT FAIL: omission still present' >&2; exit 1; fi
    echo 'RESTORED: omission absent; original authored source byte-identical' | tee -a "$copy/plant.log"
    ;;
  *) usage ;;
esac
