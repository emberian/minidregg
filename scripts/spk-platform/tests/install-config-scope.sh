#!/usr/bin/env bash
set -euo pipefail
(( $# == 2 )) || { echo 'usage: install-config-scope.sh BASE_CONFIG CANDIDATE_CONFIG' >&2; exit 2; }
base=$1 candidate=$2
rule=$(cd -- "$(dirname -- "$0")/.." && pwd)/install-config-scope.jq
scratch=$(mktemp -d /tmp/mini-install-config-scope-XXXXXXXX)
trap 'rm -rf -- "$scratch"' EXIT
check() { jq -e --slurpfile base "$base" -f "$rule" "$1" >/dev/null; }
check "$candidate"
jq '.agentLifetimeDispatchFixed={app:8401}' "$candidate" >"$scratch/lifetime.json"
if check "$scratch/lifetime.json"; then
  echo 'non-null lifetime authority accepted' >&2; exit 1
fi
jq '.storageRoot="/tmp/wrong-store"' "$candidate" >"$scratch/storage.json"
if check "$scratch/storage.json"; then
  echo 'storage mutation accepted' >&2; exit 1
fi
jq '.genesis={changed:true}' "$candidate" >"$scratch/genesis.json"
if check "$scratch/genesis.json"; then
  echo 'genesis mutation accepted' >&2; exit 1
fi
jq '.domain="1234"' "$candidate" >"$scratch/domain.json"
if check "$scratch/domain.json"; then
  echo 'domain mutation accepted' >&2; exit 1
fi
echo 'PASS: exact cb55 provider candidate; lifetime, storage, genesis and domain mutations refused'
