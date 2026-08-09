#!/usr/bin/env bash
# Compile the two Tower256 controller modules without rebuilding source modules
# whose checked generators intentionally write committed test vectors.
set -euo pipefail

build_dir=.lake/build/lib/lean/Compiler
mkdir -p "$build_dir"

lake env lean \
  -o "$build_dir/Tower256CshakeMerkleController.olean" \
  Compiler/Tower256CshakeMerkleController.lean

lake env lean \
  -o "$build_dir/Tower256LogupControllerPlan.olean" \
  Compiler/Tower256LogupControllerPlan.lean
