#!/bin/sh
# deploy/candidate/params.sh's contract, without launching a binary: the shipped example is
# unfilled and refused as-is; fill-genesis fills it to what genesis.sh --check (= run.sh init's
# check) accepts; an explicit bad value (0, string, fraction, negative) is refused by the helper
# AND by the check; a filled file is not re-dated; fill-source fills a bootstrap source.
# Usage: test-params.sh [CANDIDATE_MANIFEST]  -- with a manifest, run.sh init itself is also
# shown refusing the unfilled example and genesisNow=0 before creating state.
set -eu
here=$(CDPATH='' cd -- "$(dirname -- "$0")" && pwd)
P=$here/params.sh G=$here/../../native/resource-client/genesis.sh
EX=$here/../../native/resource-client/genesis-params.example.json
t=$(mktemp -d); trap 'rm -rf "$t"' EXIT
fail() { echo "test-params: FAIL $*" >&2; exit 1; }
refused() { # NAME CMD...: CMD must exit nonzero
  n=$1; shift
  if "$@" >"$t/$n.out" 2>"$t/$n.err"; then fail "$n accepted"; fi
}
refused example-unfilled sh "$G" --check "$EX"
cp "$EX" "$t/p.json"; before=$(date +%s)
sh "$P" fill-genesis "$t/p.json"; after=$(date +%s)
jq -e --argjson b "$before" --argjson a "$after" \
  '.clock.genesisNow >= $b and .clock.genesisNow <= $a and .clock.maxStepSeconds == 300' "$t/p.json" >/dev/null \
  || fail "fill-genesis did not write now/300"
sh "$G" --check "$t/p.json"
jq 'del(.clock.genesisNow, .clock.maxStepSeconds)' "$EX" >"$t/absent.json"
sh "$P" fill-genesis "$t/absent.json"; sh "$G" --check "$t/absent.json"
cp "$t/p.json" "$t/p.keep"
v=$(jq .clock.genesisNow "$t/p.json")
refused redate env GENESIS_NOW=$((v + 1)) sh "$P" fill-genesis "$t/p.json"
cmp "$t/p.json" "$t/p.keep" || fail "refused fill rewrote the file"
GENESIS_NOW=$v sh "$P" fill-genesis "$t/p.json"
cmp "$t/p.json" "$t/p.keep" || fail "pinned re-fill changed the file"
for bad in 0 '"0"' '"1790000000"' -1 1.5 9007199254740992; do
  jq --argjson v "$bad" '.clock.genesisNow = $v | .clock.maxStepSeconds = 300' "$EX" >"$t/bad.json"; cp "$t/bad.json" "$t/bad.keep"
  refused "helper-$bad" sh "$P" fill-genesis "$t/bad.json"
  cmp "$t/bad.json" "$t/bad.keep" || fail "helper rewrote genesisNow=$bad"
  refused "check-$bad" sh "$G" --check "$t/bad.json"
  grep -q clockGenesisNowInvalid "$t/check-$bad.err" || fail "check refused genesisNow=$bad for another reason"
done
jq '.clock.maxStepSeconds = 600' "$EX" >"$t/step.json"
refused step-differs sh "$P" fill-genesis "$t/step.json"
MAX_STEP_SECONDS=600 sh "$P" fill-genesis "$t/step.json"; sh "$G" --check "$t/step.json"
echo '{"clockTickers":[]}' >"$t/src.json"
GENESIS_NOW=1790000000 sh "$P" fill-source "$t/src.json"
jq -e '.clockGenesisNow == "1790000000" and .clockMaxStepSeconds == "300"' "$t/src.json" >/dev/null || fail "fill-source"
echo '{"clockGenesisNow":"0"}' >"$t/src0.json"
refused source-zero sh "$P" fill-source "$t/src0.json"
if [ "$#" -ge 1 ]; then
  for case in unfilled zero; do
    if [ "$case" = zero ]; then jq '.clock.genesisNow = 0 | .clock.maxStepSeconds = 300' "$EX" >"$t/init.json"
    else cp "$EX" "$t/init.json"; fi
    refused "init-$case" sh "$here/run.sh" init --manifest "$1" --params "$t/init.json" --state "$t/state-$case"
    grep -q 'clockGenesisNowInvalid\|clockStepBoundInvalid' "$t/init-$case.err" "$t/init-$case.out" || fail "init-$case refused for another reason"
    [ ! -e "$t/state-$case" ] || fail "init-$case created state"
    echo "test-params: run.sh init refused $case: $(grep -h 'clock' "$t/init-$case.err" "$t/init-$case.out" | head -1)"
  done
fi
echo 'test-params: PASS'
