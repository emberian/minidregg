#!/usr/bin/env bash
# Run the committed fault plants and the selected real journey rows J0 + M7.
set -euo pipefail
here=$(cd "$(dirname "$0")/../.." && pwd)
c=${1:?candidate directory}
r=${2:?reference candidate directory}
out=${3:?new evidence directory}
[ ! -e "$out" ]
mkdir -p "$out" "$out/sockets"
"$here/scripts/kn2/plant-m7-tamper.sh" "$c" "$out/tamper" >"$out/tamper.log" 2>&1
cat "$out/tamper.log"
"$here/scripts/kn2/plant-m7-no-verification.sh" "$c" "$out/no-verification" >"$out/no-verification.log" 2>&1
cat "$out/no-verification.log"
export JOURNEY_STEPS='J0 M7' JOURNEY_RUNTIME_BASE=$out/sockets M7_REFERENCE=$r/provenance.json
unset MINI_LOCAL_HOST MINI_CONSENT_HOST MINI_CONSENT_CONFIG
"$here/native/resource-client/journey.sh" "$c/manifest.json" "$out/journey"
jq -e '.steps[] | select(.id == "M7") | .status == "PASS"' "$out/journey/journey-result.json" >/dev/null
