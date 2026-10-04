#!/usr/bin/env bash
# Build the two Lean machine drivers from MachineRun.lean (see its header):
#   OUT_DIR/objective-machine-reference  the specification's own compiled code
#   OUT_DIR/objective-machine-fast       the same calls under the @[csimp] lemmas
# usage: native/objective-emit/fastmachine/build.sh OUT_DIR   (from anywhere)
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
repo=$(cd "$here/../../.." && pwd)
out=$(mkdir -p "$1" && cd "$1" && pwd)
cd "$repo"
lake build Theory.ObjectiveBendDemandData Theory.ObjectiveBendCheckpoint Theory.ObjectiveBendTyping
mkdir -p .lake/fastmachine
fast=.lake/fastmachine/MachineRunFast.lean
sed -e '/@REFERENCE@/d' -e 's/^-- @FAST@ //' "$here/MachineRun.lean" > "$fast"
grep -q '^import Theory.ObjectiveBendDemandData$' "$fast"
grep -q 'forceUnderTest := Minidregg.Theory.ObjectiveBendDemandData.forceWith$' "$fast"
lake env lean -c "$out/reference.c" "$here/MachineRun.lean"
lake env lean -c "$out/fast.c" "$fast"
ir=.lake/build/ir/Theory
leanc=$(dirname "$(command -v lean)")/leanc
[ -x "$leanc" ] || leanc=$(lean --print-prefix)/bin/leanc
common="$ir/ObjectiveBendOpenRecursion.c $ir/ObjectiveBendDemandMachine.c $ir/ObjectiveBendTypes.c $ir/ObjectiveBendTyping.c $ir/ObjectiveBendCheckpoint.c"
"$leanc" -O3 -o "$out/objective-machine-reference" "$out/reference.c" $common
"$leanc" -O3 -o "$out/objective-machine-fast" "$out/fast.c" $common \
  "$ir/ObjectiveBendDemandMachineFast.c" "$ir/ObjectiveBendDemandData.c"
# the reference must not reach the implementation, the fast build must
! grep -q ObjectiveBendDemandMachineFast "$out/reference.c"
grep -q 'ObjectiveBendDemandMachineFast_runBoundedFast(' "$out/fast.c"
grep -q 'ObjectiveBendDemandMachineFast_forceWithFast(' "$out/fast.c"
grep -q 'ObjectiveBendDemandMachineFast_stepFast(' "$out/fast.c"
echo "$out/objective-machine-reference"
echo "$out/objective-machine-fast"
