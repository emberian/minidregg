#!/bin/sh
# Run only against setup-mini.sh's scratch Store after its ordinary child grant.
set -eu

if [ "$#" -ne 1 ]; then
  echo "usage: $0 SETUP-MINI-ROOT" >&2
  exit 64
fi

repo=$(CDPATH='' cd -- "$(dirname -- "$0")/../.." && pwd)
root=$(CDPATH='' cd -- "$1" && pwd)
config="$root/gateway-config.json"
key="$root/ordinary.key"
delegate="$root/delegate-intent.json"
test -f "$config"
test -f "$key"
test -f "$delegate"
ordinary_subject=$(jq -er '.purpose.draft.command.child.holder.subject' "$delegate")
ordinary_capability=$(jq -er '.purpose.draft.command.child.id' "$delegate")
probe_dir=$(mktemp -d "$root/gateway-direct-submit-probe.XXXXXX")
chmod 700 "$probe_dir"

cd "$repo"
FN_GATEWAY_CONFIG="$config" \
FN_GATEWAY_ORDINARY_KEY="$key" \
FN_GATEWAY_ORDINARY_SUBJECT="$ordinary_subject" \
FN_GATEWAY_ORDINARY_CAPABILITY="$ordinary_capability" \
FN_GATEWAY_PROBE_NONCE=830007 \
FN_GATEWAY_PROBE_DIR="$probe_dir" \
FN_GATEWAY_OPENSSL=$(command -v openssl) \
LEAN_NUM_THREADS=2 lake env lean scripts/fn-e1e2/probe_gateway_direct_submit.lean
printf 'probe-artifacts=%s\n' "$probe_dir"
