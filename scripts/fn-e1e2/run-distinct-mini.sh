#!/bin/sh
# Adapt only a private copy of fn's qualified two-Store test harness.
set -eu

if [ "$#" -ne 8 ]; then
  echo "usage: $0 FN_IMAGE_DIR MINI_HOST MINI_CLIENT MINI_REPO MINI_B_DIR MINI_A_DIR FN_SCRATCH LOCAL_OUT" >&2
  exit 2
fi
IMAGE_DIR=$1
MINI_HOST=$2
MINI_CLIENT=$3
MINI_REPO=$4
MINI_B=$5
MINI_A=$6
FN_SCRATCH=$7
LOCAL_OUT=$8
HERE=$(CDPATH='' cd -- "$(dirname -- "$0")" && pwd)
REPO=$(CDPATH='' cd -- "$HERE/../.." && pwd)
FN_HARNESS=${FN_HARNESS:-"$REPO/../fn/tools/runbooks/two_store_join.py"}
FN_FIXTURES=${FN_FIXTURES:-"$REPO/../fn/tests/fixtures/dregg-e1"}
EXPECTED_HARNESS_SHA256=c88160cf459d3959928f6ae913f455ed9ff49971b89619518ab7b49c884c99e6
EXPECTED_MINI_SHA256=${MINI_SHA256:-0cce4fbd02c5b5156fb061e2d96f2e25e12588c35b59d2fd2efe20acb202f286}
COPY_DIR=$LOCAL_OUT.harness

for input in "$FN_HARNESS" "$MINI_HOST" "$MINI_CLIENT" \
  "$MINI_B/gateway-config.json" "$MINI_B/deployment/genesis.bin" \
  "$MINI_B/birth-intent.json" "$MINI_B/custody.key" "$MINI_B/policy.json" \
  "$MINI_A/gateway-config.json" "$MINI_A/deployment/genesis.bin" \
  "$MINI_A/birth-intent.json" "$MINI_A/custody.key" "$MINI_A/policy.json" \
  "$FN_FIXTURES/portable-p2/source-claim.json" "$FN_FIXTURES/source.eml"; do
  if [ ! -f "$input" ]; then echo "missing input: $input" >&2; exit 2; fi
done
if cmp -s "$MINI_B/custody.key" "$MINI_A/custody.key" ||
   cmp -s "$MINI_B/deployment/genesis.bin" "$MINI_A/deployment/genesis.bin"; then
  echo "A and B must have distinct custody keys and genesis bytes" >&2
  exit 2
fi
B_SUBJECT=$(jq -er '.fnGateway.subject' "$MINI_B/gateway-config.json")
A_SUBJECT=$(jq -er '.fnGateway.subject' "$MINI_A/gateway-config.json")
if [ "$A_SUBJECT" = "$B_SUBJECT" ]; then
  echo "A and B must have distinct gateway subjects" >&2
  exit 2
fi
jq -e --argjson subject "$B_SUBJECT" '.subject == $subject' "$MINI_B/policy.json" >/dev/null
jq -e --argjson subject "$A_SUBJECT" '.subject == $subject' "$MINI_A/policy.json" >/dev/null
case "${FN_REVOKE_GATEWAY_BEFORE_B_ACK:-0}:${FN_PUBLIC_B_SESSION:-0}:${FN_PUBLIC_A_SESSION:-0}" in
  0:0:0|1:0:0|0:1:0|0:1:1) ;;
  *) echo "select baseline, revoke, B socket, or B+A socket mode with 0/1 variables" >&2; exit 2 ;;
esac
if [ -e "$COPY_DIR" ] || [ -e "$LOCAL_OUT" ]; then
  echo "refusing to replace private run directory" >&2
  exit 2
fi
actual_harness_sha=$(shasum -a 256 "$FN_HARNESS" | cut -d ' ' -f 1)
if [ "$actual_harness_sha" != "$EXPECTED_HARNESS_SHA256" ]; then
  echo "fn harness source hash changed: $actual_harness_sha" >&2
  exit 2
fi
actual_mini_sha=$(shasum -a 256 "$MINI_HOST" | cut -d ' ' -f 1)
if [ "$actual_mini_sha" != "$EXPECTED_MINI_SHA256" ]; then
  echo "Mini host image hash changed: $actual_mini_sha" >&2
  exit 2
fi

umask 077
mkdir -m 700 "$COPY_DIR"
cp "$FN_HARNESS" "$COPY_DIR/two_store_join.py"
patch -s -d "$COPY_DIR" -p0 <"$HERE/two_store_join_per_side.patch"
cp "$HERE/two_store_join_per_side.patch" "$COPY_DIR/"
patch -s -d "$COPY_DIR" -p0 <"$HERE/two_store_join_creation_context.patch"
cp "$HERE/two_store_join_creation_context.patch" "$COPY_DIR/"
case "${FN_REVOKE_GATEWAY_BEFORE_B_ACK:-0}:${FN_PUBLIC_B_SESSION:-0}:${FN_PUBLIC_A_SESSION:-0}" in
  0:0:0) set -- ;;
  1:0:0)
    patch -s -d "$COPY_DIR" -p0 <"$HERE/two_store_join_revoke_hook.patch"
    cp "$HERE/two_store_join_revoke_hook.patch" "$COPY_DIR/"
    set -- --revoke-gateway-before-b-ack
    ;;
  0:1:0|0:1:1)
    patch -s -d "$COPY_DIR" -p0 <"$HERE/two_store_join_socket_b.patch"
    cp "$HERE/two_store_join_socket_b.patch" "$COPY_DIR/"
    set -- --public-b-session
    if [ "${FN_PUBLIC_A_SESSION:-0}" = 1 ]; then
      patch -s -d "$COPY_DIR" -p0 <"$HERE/two_store_join_socket_a.patch"
      cp "$HERE/two_store_join_socket_a.patch" "$COPY_DIR/"
      set -- --public-b-session --public-a-session
    fi
    ;;
esac
printf '%s  %s\n' "$actual_harness_sha" "$FN_HARNESS" >"$COPY_DIR/source.sha256"
shasum -a 256 "$COPY_DIR/two_store_join.py" >"$COPY_DIR/adapted.sha256"

python3 "$COPY_DIR/two_store_join.py" run \
  --image-dir "$IMAGE_DIR" --mini-bin "$MINI_HOST" \
  --mini-sha256 "$EXPECTED_MINI_SHA256" --mini-repo "$MINI_REPO" \
  --mini-client "$MINI_CLIENT" --scratch "$FN_SCRATCH" \
  --local-out "$LOCAL_OUT" --cut "${FN_CUT:-none}" \
  --r-claim "$FN_FIXTURES/portable-p2/source-claim.json" \
  --r-source "$FN_FIXTURES/source.eml" \
  --origin-pin "$MINI_B/origin-pin.json" \
  --mini-b-pinned-config "$MINI_B/gateway-config.json" \
  --mini-b-genesis "$MINI_B/deployment/genesis.bin" \
  --mini-b-birth-intent "$MINI_B/birth-intent.json" \
  --mini-b-custody-key "$MINI_B/custody.key" --mini-b-policy "$MINI_B/policy.json" \
  --mini-a-pinned-config "$MINI_A/gateway-config.json" \
  --mini-a-genesis "$MINI_A/deployment/genesis.bin" \
  --mini-a-birth-intent "$MINI_A/birth-intent.json" \
  --mini-a-custody-key "$MINI_A/custody.key" --mini-a-policy "$MINI_A/policy.json" \
  "$@"
