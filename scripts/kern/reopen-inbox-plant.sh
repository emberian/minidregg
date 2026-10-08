#!/usr/bin/env bash
# Run only after building the approved generation-1 source plant.
set -euo pipefail
[[ $# == 2 ]] || { echo 'usage: reopen-inbox-plant.sh RUST_TARGET LEAN_BIN' >&2; exit 2; }
src=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../.." && pwd)
evidence=$(mktemp -d "$src/.lake/kp-reopen.XXXXXX")
printf 'EVIDENCE %s\n' "$evidence"
mkdir -m 700 -- "$evidence/bin"
for name in mini minidregg-link-sqlite-store minidregg-credential-signature-verifier; do
  cp -L --reflink=auto -- "$1/release/$name" "$evidence/bin/$name"
done
for name in minidregg-host minidregg-client-consent; do
  cp -L --reflink=auto -- "$2/$name" "$evidence/bin/$name"
done
sha256sum "$evidence/bin"/* >"$evidence/binary-sha256"
if systemd-run --user --scope -q -p MemoryMax=10G -p MemorySwapMax=0 \
    python3 "$src/native/resource-client/objective-send-native-journey.py" \
    --bin "$evidence/bin" --root "$evidence/send" >"$evidence/send.out" 2>"$evidence/send.err"; then
  rc=0
else
  rc=$?
fi
printf 'REOPEN-PLANT journey exit %s\n' "$rc"
cat "$evidence/send.out"
cat "$evidence/send.err" >&2
[[ $rc != 0 && $rc != 137 ]] || { echo 'REOPEN-PLANT blind or oom' >&2; exit 1; }
if rg -q 'physicalPreparation' "$evidence/send.out" "$evidence/send.err"; then
  printf 'REOPEN-PLANT admission refusal detected\n'
else
  echo 'REOPEN-PLANT expected admission refusal missing' >&2
  exit 1
fi
