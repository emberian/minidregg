#!/usr/bin/env bash
# A source-built Host with unchanged published Rust boundary binaries.
set -euo pipefail
if [ "$#" -lt 3 ]; then
  echo "usage: $0 BASE_BIN_DIR BUILT_HOST BUILT_CONSENT [ROW ...]" >&2
  exit 2
fi
base=$(realpath "$1")
host=$(realpath "$2")
consent=$(realpath "$3")
shift 3
repo=$(CDPATH='' cd -- "$(dirname -- "$0")/../.." && pwd)
lane=$(dirname "$repo")
parent=$(mktemp -d "$lane/kern-fixed.XXXXXX")
mkdir "$parent/bin"
ln -s "$host" "$parent/bin/minidregg-host"
ln -s "$consent" "$parent/bin/minidregg-client-consent"
for name in mini minidregg-link-sqlite-store minidregg-credential-signature-verifier; do
  ln -s "$base/$name" "$parent/bin/$name"
done
# The runtime codec check is also contained: a faulty encoder must not eat the box.
unit=kern-codec-$(basename "$parent")
systemd-run --user --scope --quiet --unit="${unit//./-}" \
  -p MemoryMax=10G -p MemorySwapMax=0 -- timeout 180 \
  bash -c 'cd "$1" && lake env lean --run scripts/kern/RejectCodecChecks.lean' bash "$repo"
if [ "$#" = 0 ]; then set -- call send domain objectrecord; fi
failed=0
for row in "$@"; do
  echo "ROW $row"
  if bash "$repo/scripts/kern/journey-rss.sh" "$parent/bin" "$row" "$parent/$row"; then
    echo "PASS $row"
  else
    rc=$?
    echo "FAIL $row exit=$rc"
    failed=1
  fi
done
echo "evidence=$parent"
exit "$failed"
