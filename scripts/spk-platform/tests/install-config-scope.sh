#!/usr/bin/env bash
set -euo pipefail
(( $# == 4 )) || { echo 'usage: install-config-scope.sh BASE_CONFIG REBOUND_BASE CANDIDATE_REBOUND ORIGINAL_CANDIDATE' >&2; exit 2; }
base=$1 rebound=$2 candidate=$3 original=$4
rule=$(cd -- "$(dirname -- "$0")/.." && pwd)/install-config-scope.jq
base_rule=$(cd -- "$(dirname -- "$0")/.." && pwd)/base-helper-rebind-scope.jq
store=/opt/minidregg-gitweb-r3-20260927/bin/minidregg-link-sqlite-store-9746c47
signature=/opt/minidregg-gitweb-r3-20260927/bin/minidregg-credential-signature-verifier-9746c47
scratch=$(mktemp -d /tmp/mini-install-config-scope-XXXXXXXX)
trap 'rm -rf -- "$scratch"' EXIT
check() { jq -e --slurpfile base "$base" --arg storeHelper "$store" --arg signatureHelper "$signature" -f "$rule" "$1" >/dev/null; }
jq -e --slurpfile base "$base" --arg storeHelper "$store" --arg signatureHelper "$signature" -f "$base_rule" "$rebound" >/dev/null
if check "$original"; then echo 'unprotected original helper path accepted' >&2; exit 1; fi
check "$candidate"
if jq -e --slurpfile base "$base" --arg storeHelper "$store" --arg signatureHelper "$signature" -f "$base_rule" "$original" >/dev/null; then
  echo 'unprotected original base helper path accepted' >&2; exit 1
fi
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
jq '.signatureBinary="/tmp/wrong-helper"' "$candidate" >"$scratch/signature.json"
if check "$scratch/signature.json"; then
  echo 'signature helper path mutation accepted' >&2; exit 1
fi
jq '.storageBinary="/tmp/wrong-helper"' "$rebound" >"$scratch/base-store.json"
if jq -e --slurpfile base "$base" --arg storeHelper "$store" --arg signatureHelper "$signature" -f "$base_rule" "$scratch/base-store.json" >/dev/null; then
  echo 'base helper path mutation accepted' >&2; exit 1
fi
echo 'PASS: exact helper rebound and cb55 services; unrelated mutations refused'
