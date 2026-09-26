#!/bin/sh
# Adapt a private fn harness copy for an actually accepted Mini AgentGrain R.
set -eu

if [ "$#" -ne 10 ]; then
  echo "usage: $0 FN_IMAGE_DIR MINI_HOST MINI_CLIENT MINI_REPO MINI_B_DIR MINI_A_DIR FN_SCRATCH LOCAL_OUT R_SOURCE ORIGIN_PIN" >&2
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
R_SOURCE=$9
shift 9
ORIGIN_PIN=$1
HERE=$(CDPATH='' cd -- "$(dirname -- "$0")" && pwd)
REPO=$(CDPATH='' cd -- "$HERE/../.." && pwd)
FN_HARNESS=${FN_HARNESS:-"$REPO/../fn/tools/runbooks/two_store_join.py"}
EXPECTED_HARNESS_SHA256=c88160cf459d3959928f6ae913f455ed9ff49971b89619518ab7b49c884c99e6
EXPECTED_MINI_SHA256=${MINI_SHA256:?set MINI_SHA256 to the exact linked native Host hash}
EXPECTED_CLIENT_SHA256=${MINI_CLIENT_SHA256:-d6edadd46960dd055dc1d8e88b05ccbcf2ca0363c424c5a05f8747716c32fc8e}
COPY_DIR=$LOCAL_OUT.harness

for input in "$FN_HARNESS" "$MINI_HOST" "$MINI_CLIENT" "$R_SOURCE" "$ORIGIN_PIN" \
  "$MINI_B/gateway-config.json" "$MINI_B/deployment/genesis.bin" \
  "$MINI_B/birth-intent.json" "$MINI_B/custody.key" "$MINI_B/policy.json" \
  "$MINI_A/gateway-config.json" "$MINI_A/deployment/genesis.bin" \
  "$MINI_A/birth-intent.json" "$MINI_A/custody.key" "$MINI_A/policy.json"; do
  if [ ! -f "$input" ]; then echo "missing input: $input" >&2; exit 2; fi
done
if cmp -s "$MINI_B/custody.key" "$MINI_A/custody.key" ||
   cmp -s "$MINI_B/deployment/genesis.bin" "$MINI_A/deployment/genesis.bin"; then
  echo "A and B must have distinct custody keys and genesis bytes" >&2
  exit 2
fi
if [ "$(jq -er '.fnGateway.subject' "$MINI_B/gateway-config.json")" = \
     "$(jq -er '.fnGateway.subject' "$MINI_A/gateway-config.json")" ]; then
  echo "A and B must have distinct gateway subjects" >&2
  exit 2
fi
if [ "${FN_CUT:-none}" != none ]; then
  echo "dynamic AgentGrain R requires --cut none" >&2
  exit 2
fi
if [ -e "$COPY_DIR" ] || [ -e "$LOCAL_OUT" ]; then
  echo "refusing to replace private run directory" >&2
  exit 2
fi
actual_harness_sha=$(shasum -a 256 "$FN_HARNESS" | cut -d ' ' -f 1)
actual_mini_sha=$(shasum -a 256 "$MINI_HOST" | cut -d ' ' -f 1)
actual_client_sha=$(shasum -a 256 "$MINI_CLIENT" | cut -d ' ' -f 1)
if [ "$actual_harness_sha" != "$EXPECTED_HARNESS_SHA256" ] ||
   [ "$actual_mini_sha" != "$EXPECTED_MINI_SHA256" ] ||
   [ "$actual_client_sha" != "$EXPECTED_CLIENT_SHA256" ]; then
  echo "fn harness, Mini Host or client differs from pinned hash" >&2
  exit 2
fi
R_SOURCE_SHA256=$(shasum -a 256 "$R_SOURCE" | cut -d ' ' -f 1)
R_MESSAGE_ID=$(python3 - "$R_SOURCE" <<'PY'
import pathlib, re, sys
source = pathlib.Path(sys.argv[1]).read_bytes()
headers, sep, _ = source.partition(b"\r\n\r\n")
if not sep or source.count(b"\r\n\r\n") != 1:
    raise SystemExit("R source is not one strict CRLF article")
ids = re.findall(rb"(?:^|\r\n)Message-ID: (<[!-~]+>)", headers)
if len(ids) != 1 or not re.search(rb"(?:^|\r\n)Newsgroups: fn\.test(?:\r\n|$)", headers):
    raise SystemExit("R source has no unique Message-ID in fn.test")
print(ids[0].decode("ascii"))
PY
)

umask 077
mkdir -m 700 "$COPY_DIR"
cp "$FN_HARNESS" "$COPY_DIR/two_store_join.py"
for patch_name in two_store_join_per_side.patch \
                  two_store_join_creation_context.patch \
                  two_store_join_socket_b.patch \
                  two_store_join_socket_a.patch \
                  two_store_join_dynamic_r.patch; do
  patch -s -d "$COPY_DIR" -p0 <"$HERE/$patch_name"
  cp "$HERE/$patch_name" "$COPY_DIR/"
done
printf '%s  %s\n' "$actual_harness_sha" "$FN_HARNESS" >"$COPY_DIR/source.sha256"
shasum -a 256 "$COPY_DIR/two_store_join.py" >"$COPY_DIR/adapted.sha256"

python3 "$COPY_DIR/two_store_join.py" run \
  --image-dir "$IMAGE_DIR" --mini-bin "$MINI_HOST" \
  --mini-sha256 "$EXPECTED_MINI_SHA256" --mini-repo "$MINI_REPO" \
  --mini-client "$MINI_CLIENT" --scratch "$FN_SCRATCH" \
  --local-out "$LOCAL_OUT" --cut none \
  --r-source "$R_SOURCE" --r-message-id "$R_MESSAGE_ID" \
  --r-source-sha256 "$R_SOURCE_SHA256" --origin-pin "$ORIGIN_PIN" \
  --mini-b-pinned-config "$MINI_B/gateway-config.json" \
  --mini-b-genesis "$MINI_B/deployment/genesis.bin" \
  --mini-b-birth-intent "$MINI_B/birth-intent.json" \
  --mini-b-custody-key "$MINI_B/custody.key" --mini-b-policy "$MINI_B/policy.json" \
  --mini-a-pinned-config "$MINI_A/gateway-config.json" \
  --mini-a-genesis "$MINI_A/deployment/genesis.bin" \
  --mini-a-birth-intent "$MINI_A/birth-intent.json" \
  --mini-a-custody-key "$MINI_A/custody.key" --mini-a-policy "$MINI_A/policy.json" \
  --public-b-session --public-a-session
