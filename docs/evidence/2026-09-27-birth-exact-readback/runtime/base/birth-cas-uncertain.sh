#!/bin/sh
set -eu
helper=/tank/dregg-build/minidregg-9746c47-helpers-evidence/bin/minidregg-link-sqlite-store-9746c47
if [ "${1-}" = cas ]; then
  shift
  exec "$helper" cas-crash "$@" after-commit
fi
exec "$helper" "$@"
