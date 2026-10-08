#!/usr/bin/env bash
# Run just exchange from a READY set, against a fresh local fn node.
# --plant substitutes B's signing key for A's on the fresh positive-control
# release. All journey assertions remain; B admission must make the row FAIL.
# Public runner evidence is retained at NEW_RESULTS; private worlds are removed.
set -euo pipefail
[ "$#" = 5 ] || { echo "usage: $0 --green|--plant SET FN_LAUNCHER FN_CORE NEW_RESULTS" >&2; exit 2; }
mode=$1 setdir=$(realpath "$2")
export MINI_FN_LAUNCHER=$(realpath "$3") MINI_FN_CORE=$(realpath "$4")
results=$(realpath -m "$5")
case "$mode" in --green|--plant) ;; *) echo 'expected --green or --plant' >&2; exit 2;; esac
[ ! -e "$results" ] || { echo 'results already exist' >&2; exit 2; }
here=$(CDPATH='' cd -- "$(dirname -- "$0")/../.." && pwd)
[ -f "$setdir/READY" ] || { echo 'expected READY set' >&2; exit 2; }
tip=$(jq -er '.sourceCommit | select(test("^[0-9a-f]{40}$"))' "$setdir/manifest.json")
[ "$(basename "$setdir")" = "$tip" ] || { echo 'set directory does not match sourceCommit' >&2; exit 2; }
fn_image=$(dirname "$MINI_FN_LAUNCHER")
[ "$MINI_FN_CORE" = "$fn_image/fn-host.core" ] && [ "$MINI_FN_LAUNCHER" = "$fn_image/fn-host" ] || {
  echo 'expected frozen production launcher and its core from the same image' >&2; exit 2;
}
(cd "$fn_image" && sha256sum --quiet -c image.sha256)
# The continuous runner sources this lane's driver, but hashes the supplied
# artifact set before executing it. No artifact build or external node is used.
source_tree=$here
tmp=$(mktemp -d /tmp/px.XXXXXX)
trap 'rm -rf "$tmp"' EXIT
if [ "$mode" = --plant ]; then
  source_tree=$tmp/source
  mkdir -p "$source_tree/native/resource-client"
  driver=$source_tree/native/resource-client/selected-exchange-journey.sh
  cp "$here/native/resource-client/selected-exchange-journey.sh" "$driver"
  # Bootstrap stays the exact lane implementation, including its local helpers.
  ln -s "$here/native/resource-client/newparticipant-acceptance.sh" "$source_tree/native/resource-client/newparticipant-acceptance.sh"
  ln -s "$here/native/resource-client/journey.d" "$source_tree/native/resource-client/journey.d"
  ln -s "$here/native/resource-client/genesis.sh" "$source_tree/native/resource-client/genesis.sh"
  ln -s "$here/native/resource-client/genesis-params.example.json" "$source_tree/native/resource-client/genesis-params.example.json"
  python3 - "$driver" <<'PY'
from pathlib import Path
import sys
p = Path(sys.argv[1])
s = p.read_text()
old = 'make_release control 3 "$A/sponsor.key"'
new = '''make_release control 3 "$B/sponsor.key"
[ "$A_PUBLIC" != "$B_PUBLIC" ]
printf '%s\\n' 'PLANT APPLIED: control release signed with Store B key for Store A owner' >&2'''
assert s.count(old) == 1, 'PLANT DID NOT APPLY: expected one control release'
p.write_text(s.replace(old, new, 1))
assert p.read_text().count('make_release control 3 "$B/sponsor.key"') == 1
assert old not in p.read_text()
PY
  bash -n "$driver"
fi
export ARTIFACT_ROOT=$(dirname "$setdir")
export PIPELINE_JOURNEY_JOBS=1
bash "$here/scripts/pipeline/journey-runner" --once --tip "$tip" --row exchange \
  --rows-file "$here/scripts/pipeline/journey-rows" --source-tree "$source_tree" --results-root "$results"
out=$results/$tip/rows/exchange
[ "$(wc -l <"$out/result.tsv")" = 1 ]
if [ "$mode" = --green ]; then
  awk -F'\t' '$1=="exchange" && $2=="PASS" {ok=1} END {exit !ok}' "$out/result.tsv"
  [ "$(cat "$out/exit-code")" = 0 ]
  printf '%s\n' 'GREEN exchange PASS: local fn stopped; exact selected packet admitted and signed readback verified'
else
  grep -Fx 'PLANT APPLIED: control release signed with Store B key for Store A owner' "$out/exchange.err"
  awk -F'\t' '$1=="exchange" && $2=="FAIL" {ok=1} END {exit !ok}' "$out/result.tsv"
  [ "$(cat "$out/exit-code")" = 1 ]
  jq -e '.type=="refused" and .phase=="61646d697373696f6e" and
    .detail=="726571756573742072656675736564"' "$out/positive-control-outcome.json" >/dev/null
  grep -Fx '== positive-control' "$out/exchange.err"
  [ ! -e "$out/public-summary.json" ]
  printf '%s\n' 'RED exchange FAIL: planted Store B owner key refused at recipient admission (positive-control)'
fi
