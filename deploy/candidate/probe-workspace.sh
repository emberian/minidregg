#!/usr/bin/env bash
# Measure workspace dependency identity using two cold, different lexical roots.
# Run through request_journey; no changes to the source checkout or pipeline check.
set -euo pipefail
repo=$(git rev-parse --show-toplevel)
evidence=${1:?evidence directory}
mkdir -p "$evidence"
if [ -d "$repo/.m7-evidence/cause" ]; then
  mv "$repo/.m7-evidence/cause" "$evidence/cause"
  rmdir "$repo/.m7-evidence"
fi
work=$evidence/workspace-probe
[ ! -e "$work" ]
mkdir -p "$work/A/src" "$work/B/src"
git archive "${2:-e0a8ba21a39d92b470cc331fd16ea0408f608b1f}" >"$work/source.tar"
unset RUSTC_WRAPPER RUSTC_WORKSPACE_WRAPPER CARGO_ENCODED_RUSTFLAGS
export CARGO_INCREMENTAL=0
cargo_home=$(cd "${CARGO_HOME:-$HOME/.cargo}" && pwd -P)
for side in A B; do
  src=$work/$side/src
  tar -xf "$work/source.tar" -C "$src"
  cat >"$src/Cargo.toml" <<'TOML'
[workspace]
resolver = "2"
members = ["native/grain-runtime", "native/signed-api-path", "native/inference-scheduler", "native/compatible-upgrade-custody", "native/mini-keys"]
TOML
  cp "$src/native/grain-runtime/Cargo.lock" "$src/Cargo.lock"
  rust=$(sed -n 's/^channel *= *"\(.*\)"$/\1/p' "$src/rust-toolchain.toml")
  (cd "$src" && cargo "+$rust" generate-lockfile --offline) >"$work/$side-lock.log" 2>&1
  (cd "$src" && RUSTFLAGS="--remap-path-prefix=$src=/minidregg --remap-path-prefix=$cargo_home=/cargo" \
    cargo "+$rust" build --release --offline --locked -j 4 -p minidregg-grain-runtime --bin grain-runtime \
      --target-dir "$work/$side/target" -vv) >"$work/$side-build.log" 2>&1
  sha256sum "$work/$side/target/release/grain-runtime" | tee -a "$work/sha256sums"
done
cmp "$work/A/target/release/grain-runtime" "$work/B/target/release/grain-runtime"
echo 'workspace-probe: different lexical roots reproduce'
