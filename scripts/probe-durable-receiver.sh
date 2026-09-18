#!/usr/bin/env bash
set -euo pipefail

# Narrow joined lifecycle check, not the whole Minidregg build. Every native
# test runs optimized code, so an accidentally debug-only SQL step is visible.
repo=$(cd -- "$(dirname -- "$0")/.." && pwd)
cd "$repo"
export LEAN_NUM_THREADS=2

lake env lean -o .lake/build/lib/lean/Kernel/DurableReceiver.olean Kernel/DurableReceiver.lean
lake env lean -o .lake/build/lib/lean/Compiler/DurableReceiverCodec.olean Compiler/DurableReceiverCodec.lean
lake env lean -o .lake/build/lib/lean/Compiler/DurableReceiverIO.olean Compiler/DurableReceiverIO.lean
cargo test --release --manifest-path native/hyperdocument-link-sqlite-store/Cargo.toml \
  --target-dir native/hyperdocument-link-sqlite-store/target --all-targets
lake env lean --run scripts/durable-receiver.lean \
  "$repo/native/hyperdocument-link-sqlite-store/target/release/minidregg-link-sqlite-store"
