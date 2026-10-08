#!/usr/bin/env bash
# Re-emit the historical acceptance fixture from a fresh source-matched world.
set -euo pipefail
[[ $# == 2 ]] || { echo 'usage: regenerate-native-fixture.sh RUST_TARGET LEAN_BIN' >&2; exit 2; }
src=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../.." && pwd)
evidence=$(mktemp -d "$src/.lake/kp-fixture.XXXXXX")
printf 'EVIDENCE %s\n' "$evidence"
mkdir -m 700 -- "$evidence/bin" "$evidence/tmp"
for name in mini minidregg-link-sqlite-store minidregg-credential-signature-verifier; do
  cp -L --reflink=auto -- "$1/release/$name" "$evidence/bin/$name"
done
for name in minidregg-host minidregg-client-consent; do
  cp -L --reflink=auto -- "$2/$name" "$evidence/bin/$name"
done
sha256sum "$evidence/bin"/* >"$evidence/binary-sha256"
export TMPDIR=$evidence/tmp
systemd-run --user --scope -q -p MemoryMax=10G -p MemorySwapMax=0 \
  python3 "$src/native/resource-client/objective-native-acceptance.py" all \
  --bin "$evidence/bin" --root "$evidence/world"
systemd-run --user --scope -q -p MemoryMax=10G -p MemorySwapMax=0 \
  bash "$src/scripts/native-accepted-fixture/generate.sh" "$evidence/world"
sha256sum "$src/Assurance/NativeAcceptedFixtureData.lean"
