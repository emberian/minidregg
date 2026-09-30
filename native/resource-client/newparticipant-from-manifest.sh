#!/bin/sh
# newparticipant-acceptance.sh driven by a candidate manifest instead of four
# binary paths. MANIFEST is the journey-format manifest written by
# deploy/candidate/build.sh; every binary is checked against its pinned SHA-256
# before the fixture starts.
set -eu
if [ "$#" -ne 2 ]; then
  echo "usage: $0 MANIFEST.json NEW_PRIVATE_DIRECTORY" >&2
  exit 2
fi
command -v jq >/dev/null 2>&1 || { echo 'jq is required' >&2; exit 2; }
here=$(CDPATH='' cd -- "$(dirname -- "$0")" && pwd)
for role in host mini store verifier; do
  path=$(jq -er --arg r "$role" '.[$r] | select(type == "string" and startswith("/"))' "$1") \
    || { echo "manifest .$role must be an absolute path" >&2; exit 2; }
  want=$(jq -er --arg r "$role" '.sha256[$r] | select(type == "string")' "$1") \
    || { echo "manifest pins no sha256 for $role" >&2; exit 2; }
  got=$(sha256sum "$path" | cut -d ' ' -f 1)
  [ "$got" = "$want" ] || { echo "$role $path is $got, manifest pins $want" >&2; exit 1; }
  eval "$role=\$path"
done
# shellcheck disable=SC2154
exec sh "$here/newparticipant-acceptance.sh" "$host" "$mini" "$store" "$verifier" "$2"
