#!/usr/bin/env bash
set -euo pipefail

project_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$project_dir"

cargo run --release --quiet --manifest-path prover/Cargo.toml \
  --bin native_dispatch_bench
