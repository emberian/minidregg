#!/usr/bin/env bash
set -euo pipefail
source_file=$(cd -- "$(dirname -- "$0")/.." && pwd)/spk-ingest-prepared
scratch=$(mktemp -d /tmp/mini-spk-ingest-custody-XXXXXXXX)
trap 'rm -rf -- "$scratch"' EXIT
# Exercise the exact function used before either materialization or inspection.
eval "$(sed -n '/^safe_root_executable() {/,/^}/p' "$source_file")"
safe_root_executable /usr/bin/sha256sum
cp /usr/bin/sha256sum "$scratch/host"
chmod 755 "$scratch/host"
if safe_root_executable "$scratch/host"; then
  echo 'task-owned host executable was accepted for root execution' >&2; exit 1
fi
ln -s /usr/bin/sha256sum "$scratch/symlink"
if safe_root_executable "$scratch/symlink"; then
  echo 'symlinked host executable was accepted for root execution' >&2; exit 1
fi
echo 'PASS: protected root Host accepted; task-owned and symlinked Host refused'
