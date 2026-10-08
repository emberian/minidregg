#!/usr/bin/env bash
# Re-run: plant-prod-rows.sh SET/bin SET/manifest.json
# Mutations live only in a temporary source copy. The real runner must expose
# withheld input as 98 and a silent successful driver as FAIL.
set -euo pipefail
[ "$#" = 2 ] || { echo "usage: $0 BIN MANIFEST" >&2; exit 2; }
here=$(CDPATH='' cd -- "$(dirname -- "$0")/../.." && pwd)
setdir=$(dirname -- "$(realpath "$2")")
[ "$(realpath "$1")" = "$setdir/bin" ] || { echo "BIN and MANIFEST must name the same set" >&2; exit 2; }
tip=$(jq -er '.sourceCommit | select(test("^[0-9a-f]{40}$"))' "$2")
[ -f "$setdir/READY" ] || { echo "plant needs a READY set: $setdir" >&2; exit 2; }
tmp=$(mktemp -d /tmp/plant-prod-rows.XXXXXX)
trap 'rm -rf "$tmp"' EXIT
mkdir -p "$tmp/source/native/resource-client"
cp "$here/scripts/pipeline/journey-rows" "$tmp/rows"
cp "$here/native/resource-client/selected-exchange-journey.sh" "$tmp/source/native/resource-client/"
cp "$here/native/resource-client/provisioning-acceptance.sh" "$tmp/source/native/resource-client/"
runner=$here/scripts/pipeline/journey-runner

# Mutation 1: establish then explicitly remove a configured input.
export MINI_FN_LAUNCHER=$tmp/source/native/resource-client/selected-exchange-journey.sh
[ -f "$MINI_FN_LAUNCHER" ]
printf '%s\n' 'env -u MINI_FN_LAUNCHER' >"$tmp/withheld-input"
grep -Fx 'env -u MINI_FN_LAUNCHER' "$tmp/withheld-input" >/dev/null
env -u MINI_FN_LAUNCHER bash -c 'test -z "${MINI_FN_LAUNCHER+x}"'  # assert actual withholding
mkdir -p "$tmp/artifacts"
ln -s "$setdir" "$tmp/artifacts/$tip"
env -u MINI_FN_LAUNCHER ARTIFACT_ROOT="$tmp/artifacts" bash "$runner" --once --tip "$tip" \
  --rows-file "$tmp/rows" --source-tree "$tmp/source" --row exchange --results-root "$tmp/missing"
result=$tmp/missing/$tip/rows/exchange/result.tsv
awk -F'\t' '$1=="exchange" && $2=="UNCONFIGURED" && $5=="missing input: MINI_FN_LAUNCHER (value)" {ok=1} END {exit !ok}' "$result"
[ "$(wc -l <"$result")" = 1 ]
printf '%s\n' 'PLANT withheld-input: exchange UNCONFIGURED exit 98: missing input: MINI_FN_LAUNCHER (value)'

# Mutation 2: replace an existing driver by an exit-zero, no-work stub.
driver=$tmp/source/native/resource-client/provisioning-acceptance.sh
[ -s "$driver" ]
printf '#!/bin/sh\nexit 0\n' >"$driver"
grep -Fx 'exit 0' "$driver" >/dev/null
[ "$(wc -l <"$driver")" = 2 ]
[ -f "$driver" ]  # the row cannot honestly call this ABSENT
ARTIFACT_ROOT="$tmp/artifacts" bash "$runner" --once --tip "$tip" --rows-file "$tmp/rows" \
  --source-tree "$tmp/source" --row m3 --results-root "$tmp/silent"
result=$tmp/silent/$tip/rows/m3/result.tsv
awk -F'\t' '$1=="m3" && $2=="FAIL" && $5=="missing expected evidence: timings.tsv" {ok=1} END {exit !ok}' "$result"
[ "$(wc -l <"$result")" = 1 ]
[ ! -s "$tmp/silent/$tip/rows/m3/m3.out" ]
[ ! -s "$tmp/silent/$tip/rows/m3/m3.err" ]
printf '%s\n' 'PLANT silent-driver: m3 FAIL exit 1: missing expected evidence: timings.tsv'

# Mutation 3: a killed scope cannot leave an empty failure detail.
printf '%s\n' '#!/bin/sh' 'exec python3 -c "allocation = bytearray(128 * 1024 * 1024)"' >"$driver"
grep -F 'bytearray(128 * 1024 * 1024)' "$driver" >/dev/null
[ "$(wc -l <"$driver")" = 2 ]
PIPELINE_ROW_MEM_MAX=32M ARTIFACT_ROOT="$tmp/artifacts" bash "$runner" --once --tip "$tip" \
  --rows-file "$tmp/rows" --source-tree "$tmp/source" --row m3 --results-root "$tmp/oom"
result=$tmp/oom/$tip/rows/m3/result.tsv
awk -F'\t' '$1=="m3" && $2=="FAIL" && $5 ~ /^scope OOM-killed \(MemoryMax=32M\); exit [0-9]+; evidence: scope.log$/ {ok=1} END {exit !ok}' "$result"
grep -F 'killed by the OOM killer' "$tmp/oom/$tip/rows/m3/scope.log" >/dev/null
[ "$(wc -l <"$result")" = 1 ]
printf '%s\n' 'PLANT killed-scope: m3 FAIL: scope OOM-killed (MemoryMax=32M); evidence: scope.log'
