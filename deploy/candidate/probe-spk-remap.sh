#!/usr/bin/env bash
# Diagnose the residual LLVM anonymous-symbol difference after workspace identity.
set -euo pipefail
work=${1:?completed two-build directory}
new=${2:?new diagnostic directory}
[ ! -e "$new" ]
mkdir -p "$new"
unset RUSTC_WRAPPER RUSTC_WORKSPACE_WRAPPER CARGO_ENCODED_RUSTFLAGS
export CARGO_INCREMENTAL=0
cargo_home=$(cd "${CARGO_HOME:-$HOME/.cargo}" && pwd -P)
for mode in target-remap one-codegen-unit; do
  for side in A B; do
    src=$work/$side/src
    target=$new/$side/target
    flags="--remap-path-prefix=$src=/minidregg --remap-path-prefix=$cargo_home=/cargo --remap-path-prefix=$target=/target"
    if [ "$mode" = one-codegen-unit ]; then flags="$flags -C codegen-units=1"; fi
    rust=$(sed -n 's/^channel *= *"\(.*\)"$/\1/p' "$src/rust-toolchain.toml")
    (cd "$src" && RUSTFLAGS="$flags" cargo "+$rust" build --release --offline --locked -j 4 \
      -p minidregg-spk-host --bin spk-host --target-dir "$target") >"$new/$mode-$side.log" 2>&1
    sha256sum "$target/release/spk-host" | tee -a "$new/$mode.sha256"
  done
  if cmp -s "$new/A/target/release/spk-host" "$new/B/target/release/spk-host"; then
    echo "spk probe: $mode reproduces"; exit 0
  fi
  echo "spk probe: $mode differs"
done
exit 1
