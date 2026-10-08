#!/bin/bash
# Mutate a TEMP COPY of A's request to B's ids; retain A's volume path.
set -euo pipefail
[[ $# == 4 ]] || { echo "usage: $0 INSTALLED_HELPER A_REQUEST B_REGISTRY NEW_EVIDENCE_DIR" >&2; exit 2; }
helper=$1 source=$2 registry=$3 evidence=$4
[[ ! -e $evidence ]] || exit 2
mkdir -m 700 "$evidence"
cp "$source" "$evidence/original.json"
jq --slurpfile b "$registry" '.store=$b[0].store | .deploymentId=$b[0].deploymentId | .appUid=$b[0].appUids[0] | .verb="mount"' "$evidence/original.json" >"$evidence/mutated.json"
other=$(jq -er .store "$registry")
grep -Fq "\"store\": \"$other\"" "$evidence/mutated.json"
[[ $(jq -er .store "$source") != "$other" && $(jq -er .volumePath "$evidence/mutated.json") == "$(jq -er .volumePath "$source")" ]] || { echo 'cross-world mutation assertion failed' >&2; exit 1; }
if sudo -n -- "$helper" "$(jq -c . "$evidence/mutated.json")" >"$evidence/stdout" 2>"$evidence/stderr"; then
  echo 'plant failed: cross-world helper request accepted' >&2; exit 1
fi
grep -Fq 'volume-helper: cross-world-volume-path refused' "$evidence/stderr"
printf 'RED volume-helper: cross-world-volume-path refused\n'
# The root-authoritative enumeration verb must reject A's ids with B's path.
jq --slurpfile b "$registry" '{verb:"volumes-status",store:.store,deploymentId:.deploymentId,volumesRoot:($b[0].grainsRoot+"/volumes")}' "$evidence/original.json" >"$evidence/status-mutated.json"
grep -Fq '"verb": "volumes-status"' "$evidence/status-mutated.json"
[[ $(jq -er .store "$evidence/status-mutated.json") == "$(jq -er .store "$source")" && $(jq -er .volumesRoot "$evidence/status-mutated.json") == "$(jq -er .grainsRoot "$registry")/volumes" ]] || { echo 'volumes-status mutation assertion failed' >&2; exit 1; }
if sudo -n -- "$helper" "$(jq -c . "$evidence/status-mutated.json")" >"$evidence/status.stdout" 2>"$evidence/status.stderr"; then
  echo 'plant failed: cross-world enumeration accepted' >&2; exit 1
fi
grep -Fq 'volume-helper: cross-world-volume-path refused' "$evidence/status.stderr"
printf 'RED volumes-status volume-helper: cross-world-volume-path refused\n'
