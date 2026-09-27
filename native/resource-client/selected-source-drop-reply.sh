#!/bin/sh
# Test-only Host transport shim: run one real source submit, retain its native
# outcome, then return truncated bytes to the publisher. All other commands
# delegate unchanged. The selected-source-publisher-acceptance.sh gate pins
# the real Host and this wrapper separately in its private evidence.
set -eu
umask 077

real=${SELECTED_SOURCE_DROP_REAL_HOST:?missing real source Host}
evidence=${SELECTED_SOURCE_DROP_EVIDENCE:?missing private evidence directory}
[ -x "$real" ] || { echo "real source Host is not executable" >&2; exit 2; }
[ -d "$evidence" ] || { echo "private evidence directory is absent" >&2; exit 2; }

if [ "$#" -eq 4 ] && [ "$2" = selected-source-publication-submit ]; then
  [ ! -e "$evidence/drop-native-outcome.bin" ] || {
    echo "refusing a second dropped source submit" >&2; exit 2
  }
  [ ! -e "$4" ] || { echo "source submit output already exists" >&2; exit 2; }
  "$real" "$1" "$2" "$3" "$evidence/drop-native-outcome.bin"
  printf truncated > "$4"
  exit 0
fi
exec "$real" "$@"
