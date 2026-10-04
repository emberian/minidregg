#!/usr/bin/env bash
# Compile the Lean reference driver — `runBounded` itself — to a native binary
# with Lean's own compiler. No hand-written semantics: the trust added over the
# kernel is the Lean compiler (as for #assert_compiled facts). This is the
# third column of the wall-time row: IR interpreter / Lean-native / hand C.
# usage: build-lean-native.sh OUT_DIR   (run from anywhere, after
#   lake build Compiler.ObjectiveBendEmitC Theory.ObjectiveBendTyping)
set -euo pipefail
repo=$(cd "$(dirname "$0")/../.." && pwd)
out=$1; mkdir -p "$out"; cd "$repo"
lake env lean -c "$out/ObjectiveBendEmitCRun.c" Compiler/ObjectiveBendEmitCRun.lean
ir=.lake/build/ir
leanc=$(dirname "$(command -v lean)")/leanc
[ -x "$leanc" ] || leanc=$(lean --print-prefix)/bin/leanc
"$leanc" -O3 -o "$out/objective-lean-native" "$out/ObjectiveBendEmitCRun.c" \
  $ir/Theory/ObjectiveBendOpenRecursion.c $ir/Theory/ObjectiveBendDemandMachine.c \
  $ir/Theory/ObjectiveBendTypes.c $ir/Theory/ObjectiveBendTyping.c $ir/Compiler/ObjectiveBendEmitC.c
echo "$out/objective-lean-native"
