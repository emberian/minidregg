#!/usr/bin/env bash
# The same unchanged call row, with source-built old-encoder Host and consent.
set -euo pipefail
if [ "$#" != 3 ]; then
  echo "usage: $0 BASE_BIN_DIR PLANTED_HOST PLANTED_CONSENT" >&2
  exit 2
fi
base=$(realpath "$1")
host=$(realpath "$2")
consent=$(realpath "$3")
repo=$(CDPATH='' cd -- "$(dirname -- "$0")/../.." && pwd)
parent=$(mktemp -d "$(dirname "$repo")/kern-plant-run.XXXXXX")
mkdir "$parent/bin"
ln -s "$host" "$parent/bin/minidregg-host"
ln -s "$consent" "$parent/bin/minidregg-client-consent"
for name in mini minidregg-link-sqlite-store minidregg-credential-signature-verifier; do
  ln -s "$base/$name" "$parent/bin/$name"
done
exec bash "$repo/scripts/kern/journey-rss.sh" "$parent/bin" call "$parent/call"
