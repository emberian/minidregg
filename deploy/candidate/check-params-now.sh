#!/bin/sh
# Check the wall-clock placeholder contract without launching any binaries.
set -eu
here=$(CDPATH='' cd -- "$(dirname -- "$0")" && pwd)
. "$here/params.sh"
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
example=$here/../../native/resource-client/genesis-params.example.json
before=$(date +%s)
candidate_params_now "$example" >"$tmp/now.json"
after=$(date +%s)
jq -e --argjson before "$before" --argjson after "$after" '.clock.genesisNow >= $before and .clock.genesisNow <= $after' "$tmp/now.json" >/dev/null
sh "$here/../../native/resource-client/genesis.sh" --check "$tmp/now.json"
jq '.clock.genesisNow = 1790000000' "$example" >"$tmp/explicit.json"
candidate_params_now "$tmp/explicit.json" >"$tmp/kept.json"
cmp "$tmp/explicit.json" "$tmp/kept.json"
for invalid in null '"0"' -1 1.5 9007199254740992; do
  jq --argjson invalid "$invalid" '.clock.genesisNow = $invalid' "$example" >"$tmp/invalid.json"
  if candidate_params_now "$tmp/invalid.json" >"$tmp/refused.json" 2>"$tmp/refused.err"; then exit 1; fi
done
jq 'del(.clock.genesisNow)' "$example" >"$tmp/missing.json"
if candidate_params_now "$tmp/missing.json" >"$tmp/refused.json" 2>"$tmp/refused.err"; then exit 1; fi
echo 'PASS: zero resolved, explicit seconds preserved, invalid and missing values refused'
