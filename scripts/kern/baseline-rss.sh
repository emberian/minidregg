#!/usr/bin/env bash
set -euo pipefail
if [ "$#" -ne 2 ]; then
  echo "usage: $0 ARTIFACT_TIP ROW" >&2
  exit 2
fi
lane=$(CDPATH='' cd -- "$(dirname -- "$0")/../../.." && pwd)
parent=$(mktemp -d "$lane/kern-artifact.XXXXXX")
bash /srv/pipeline/scripts/fetch-artifacts "$1" "$parent/set" --link
exec bash "$(dirname -- "$0")/journey-rss.sh" "$parent/set/bin" "$2"
