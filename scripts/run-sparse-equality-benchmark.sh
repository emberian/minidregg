#!/usr/bin/env bash
set -euo pipefail

project_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
profile_file="$(mktemp "${TMPDIR:-/tmp}/minidregg-sparse-equality.XXXXXX.csv")"
trap 'rm -f "$profile_file"' EXIT

cd "$project_dir"
lake build Compiler.SparseEqualityWorkProfile >/dev/null
lake env lean --run scripts/EmitSparseEqualityWorkProfile.lean >"$profile_file"
cargo run --release --quiet --manifest-path prover/Cargo.toml \
  --bin sparse_equality_bench -- "$profile_file"
