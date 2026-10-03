#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
# Captain supplies one isolated Rust seat. This is a small physical package,
# never a Bread/Mini workspace build and never a Lean source qualification.
[[ -f Cargo.lock ]] || cargo generate-lockfile
find vendor/fhe-dregg -type f -not -path '*/target/*' -not -path '*/.git/*' -print0 | LC_ALL=C sort -z | xargs -0 sha256sum > vendor-source-sha256.txt
sha256sum Cargo.toml Cargo.lock src/lib.rs src/main.rs src/owner.rs src/governed.rs vendor-source-sha256.txt scripts/build-scoped.sh scripts/check-governed.sh > transformer-source-sha256.txt
DREGG_FHE_TRANSFORMER_ID=$(sha256sum transformer-source-sha256.txt | cut -d ' ' -f1)
export DREGG_FHE_TRANSFORMER_ID
cargo build --locked --release --jobs 2
printf '%s\n' "$DREGG_FHE_TRANSFORMER_ID" > transformer-id.txt
sha256sum target/release/fhe-bend target/release/fhe-bend-owner > native-binary-sha256.txt
