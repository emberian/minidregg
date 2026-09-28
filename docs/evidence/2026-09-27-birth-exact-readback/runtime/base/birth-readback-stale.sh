#!/bin/sh
set -eu
helper=/tank/dregg-build/minidregg-9746c47-helpers-evidence/bin/minidregg-link-sqlite-store-9746c47
marker=/tmp/minidregg-birth-exact-r3-20260927/stdio-nonexact/stale-once
genesis=/tmp/minidregg-birth-exact-r3-20260927/base/genesis.bin
if [ "${1-}" = cas ]; then
  "$helper" "$@"
  : > "$marker"
  exit 0
fi
if [ "${1-}" = read-to ] && [ -f "$marker" ]; then
  rm "$marker"
  cp "$genesis" "$3"
  exit 0
fi
exec "$helper" "$@"
