#!/usr/bin/env bash
# Remove G's checkpoint call in a temporary driver and pin the kernel refusal.
# Usage: scripts/kn2/plant-growth-certify.sh MANIFEST.json NEW_EVIDENCE_ROOT
set -euo pipefail
if [ "$#" -ne 2 ]; then
  echo "usage: $0 MANIFEST.json NEW_EVIDENCE_ROOT" >&2
  exit 2
fi
plant_root=$(CDPATH='' cd -- "$(dirname -- "$0")/../.." && pwd)
plant_manifest=$1
plant_evidence=$2
case "$plant_evidence" in /*) ;; *) echo "plant: evidence root must be absolute" >&2; exit 2;; esac
test ! -e "$plant_evidence"
mkdir -m 700 "$plant_evidence"
plant_tmp=$(mktemp -d)
trap 'rm -rf -- "$plant_tmp"' EXIT
mkdir -p "$plant_tmp/journey.d/lib"
cp "$plant_root/native/resource-client/journey.sh" "$plant_tmp/journey.sh"
cp "$plant_root/native/resource-client/journey.d/lib/shortdir.sh" "$plant_tmp/journey.d/lib/shortdir.sh"
cp "$plant_root/native/resource-client/newparticipant-acceptance.sh" "$plant_tmp/newparticipant-acceptance.sh"
cp "$plant_root/native/resource-client/genesis.sh" "$plant_tmp/genesis.sh"
cp "$plant_root/native/resource-client/genesis-params.example.json" "$plant_tmp/genesis-params.example.json"
plant_call='  grow_checkpoint "$id" || return 1'
test "$(grep -Fc "$plant_call" "$plant_tmp/journey.sh")" -eq 1
sed -i 's/^  grow_checkpoint "\$id" || return 1$/  : # planted: growth checkpoint removed/' "$plant_tmp/journey.sh"
test "$(grep -Fc '  : # planted: growth checkpoint removed' "$plant_tmp/journey.sh")" -eq 1
if grep -Fq "$plant_call" "$plant_tmp/journey.sh"; then
  echo "PLANT DID NOT APPLY: in-loop checkpoint call remains" >&2
  exit 1
fi
cp "$plant_tmp/journey.sh" "$plant_evidence/mutant-journey.sh"
plant_rc=0
JOURNEY_STEPS="J0 J1 J2 J3 J4 G" JOURNEY_GROWTH_LEVELS="10 100 500 1000" \
  bash "$plant_tmp/journey.sh" "$plant_manifest" "$plant_evidence/run" \
  >"$plant_evidence/journey.out" 2>"$plant_evidence/journey.err" || plant_rc=$?
test "$plant_rc" -ne 0
jq -e '.frontier == "G" and (.steps[] | select(.id == "G") | .status == "FAIL")' \
  "$plant_evidence/run/journey-result.json" >/dev/null
plant_red='refused: tail-bound: head/height <= certified/height + L fails: head 257 certified 0 bound 256; certify (mini checkpoint) to resume'
grep -F "$plant_red" "$plant_evidence/run/steps/G/w/g252.submit.err" >"$plant_evidence/red.txt"
echo "RED as intended: removing in-loop checkpoint makes G fail at g252"
cat "$plant_evidence/red.txt"
