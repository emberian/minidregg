#!/bin/sh
# Exercise the physical post-CAS readback of a retained signed call on private Stores.
set -eu
umask 077

if [ "$#" -ne 6 ]; then
  echo "usage: $0 HOST MINI STORE SIGNATURE-HELPER BIRTH-FIXTURE NEW_ROOT" >&2
  exit 2
fi
HOST=$1
MINI=$2
STORE=$3
SIGNATURE=$4
FIXTURE=$5
ROOT=$6
for executable in "$HOST" "$MINI" "$STORE" "$SIGNATURE"; do
  test -x "$executable" || { echo "not executable: $executable" >&2; exit 2; }
done
test -s "$FIXTURE/image-birth.bin"
test -s "$FIXTURE/image-content.bin"
test -s "$FIXTURE/image-joint.bin"
test -s "$FIXTURE/content-attempt/call.bin"
test ! -e "$ROOT" || { echo "refusing existing root: $ROOT" >&2; exit 2; }
mkdir "$ROOT"
ROOT=$(CDPATH='' cd -- "$ROOT" && pwd)
FIXTURE=$(CDPATH='' cd -- "$FIXTURE" && pwd)
HOST=$(CDPATH='' cd -- "$(dirname -- "$HOST")" && pwd)/$(basename -- "$HOST")
MINI=$(CDPATH='' cd -- "$(dirname -- "$MINI")" && pwd)/$(basename -- "$MINI")
STORE=$(CDPATH='' cd -- "$(dirname -- "$STORE")" && pwd)/$(basename -- "$STORE")
SIGNATURE=$(CDPATH='' cd -- "$(dirname -- "$SIGNATURE")" && pwd)/$(basename -- "$SIGNATURE")
# The three config substitutions below insert path text inside JSON strings.
# Reject characters that would need JSON escaping rather than changing any
# large numeric source fields through a JSON parser.
if printf '%s' "$ROOT$SIGNATURE" | grep -F -q -e '"' -e '\'; then
  echo 'root or signature helper path needs JSON escaping' >&2
  exit 2
fi
if printf '%s' "$ROOT$SIGNATURE" | LC_ALL=C grep -q '[[:cntrl:]]'; then
  echo 'root or signature helper path has a control character' >&2
  exit 2
fi
SERVER_PID=
cleanup() {
  if [ -n "$SERVER_PID" ]; then
    kill "$SERVER_PID" 2>/dev/null || true
    wait "$SERVER_PID" 2>/dev/null || true
  fi
}
trap cleanup EXIT

for mode in installed lost-cas-reply failed-readback concurrent-suffix; do
  CASE=$ROOT/$mode
  mkdir "$CASE" "$CASE/store" "$CASE/private"
  chmod 700 "$CASE/private"
  "$STORE" cas "$CASE/store" - "$FIXTURE/image-birth.bin" > "$CASE/bootstrap.log"
  cat > "$CASE/storage-wrapper.sh" <<'WRAPPER'
#!/bin/sh
set -eu
if [ "$1" = read-to ] && [ "$MINI_TEST_MODE" = failed-readback ] &&
   [ -e "$MINI_TEST_CASE/cas-finished" ] && [ ! -e "$MINI_TEST_CASE/readback-failed" ]; then
  : > "$MINI_TEST_CASE/readback-failed"
  echo 'injected first post-CAS readback failure' >&2
  exit 71
fi
if [ "$1" = cas ]; then
  "$MINI_TEST_STORE" "$@"
  result=$?
  if [ "$result" -eq 0 ]; then
    : > "$MINI_TEST_CASE/cas-finished"
    if [ "$MINI_TEST_MODE" = concurrent-suffix ]; then
      "$MINI_TEST_STORE" cas "$MINI_TEST_CASE/store" \
        "$MINI_TEST_FIXTURE/image-content.bin" "$MINI_TEST_FIXTURE/image-joint.bin" \
        > "$MINI_TEST_CASE/external-suffix-cas.log"
    fi
    if [ "$MINI_TEST_MODE" = lost-cas-reply ]; then
      echo 'injected lost successful CAS response' >&2
      exit 72
    fi
  fi
  exit "$result"
fi
exec "$MINI_TEST_STORE" "$@"
WRAPPER
  chmod 700 "$CASE/storage-wrapper.sh"
  # Change only the three physical paths. JSON reserialization through jq would
  # round this fixture's unquoted 256-bit expectedSeed.
  MINI_TEST_CONFIG_ROOT="$CASE/store" \
    MINI_TEST_CONFIG_STORE="$CASE/storage-wrapper.sh" \
    MINI_TEST_CONFIG_SIG="$SIGNATURE" \
    perl -0777 -pe '
      s/("storageRoot"\s*:\s*")[^"]*"/${1}$ENV{MINI_TEST_CONFIG_ROOT}"/ or die "missing storageRoot";
      s/("storageBinary"\s*:\s*")[^"]*"/${1}$ENV{MINI_TEST_CONFIG_STORE}"/ or die "missing storageBinary";
      s/("signatureBinary"\s*:\s*")[^"]*"/${1}$ENV{MINI_TEST_CONFIG_SIG}"/ or die "missing signatureBinary";
    ' "$FIXTURE/deployment/pinned-config.json" > "$CASE/config.json"
  mkdir "$CASE/attempt"
  cp "$FIXTURE/content-attempt/call.bin" "$CASE/attempt/call.bin"
  jq -n --arg host "$HOST" --arg config "$CASE/config.json" \
    --arg socket "$CASE/private/mini.sock" \
    '{format:"minidregg-resource-client-attempt-v1",operation:"submit",host:$host,config:$config,socket:$socket}' \
    > "$CASE/attempt/attempt.json"
  export MINI_TEST_STORE=$STORE MINI_TEST_CASE=$CASE MINI_TEST_MODE=$mode
  export MINI_TEST_FIXTURE=$FIXTURE
  "$MINI" serve --host "$HOST" --config "$CASE/config.json" \
    --socket "$CASE/private/mini.sock" > "$CASE/serve.log" 2>&1 &
  SERVER_PID=$!
  ready=0
  for _ in 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18 19 20; do
    if [ -S "$CASE/private/mini.sock" ]; then ready=1; break; fi
    sleep 0.25
  done
  if [ "$ready" -ne 1 ]; then
    echo "session did not open: $mode" >&2
    exit 1
  fi
  "$MINI" describe --host "$HOST" --config "$CASE/config.json" \
    --socket "$CASE/private/mini.sock" > "$CASE/describe.json"
  if "$MINI" retry --attempt "$CASE/attempt" --mode submit \
    --socket "$CASE/private/mini.sock" > "$CASE/submit.log" 2>&1; then
    printf '0\n' > "$CASE/submit.exit"
  else
    printf '1\n' > "$CASE/submit.exit"
  fi
  "$STORE" read-to "$CASE/store" "$CASE/physical-after.bin"
  if [ "$mode" = concurrent-suffix ]; then
    cmp "$FIXTURE/image-joint.bin" "$CASE/physical-after.bin"
  else
    cmp "$FIXTURE/image-content.bin" "$CASE/physical-after.bin"
  fi
  if [ "$mode" = failed-readback ]; then
    test -e "$CASE/readback-failed"
    test "$(cat "$CASE/submit.exit")" = 1
    jq -e '.type == "uncertain" and (.detail | type == "string")' \
      "$CASE/attempt/retry-0001.json" > /dev/null
  else
    test "$(cat "$CASE/submit.exit")" = 0
    jq -e --arg confirmation "$(test "$mode" = lost-cas-reply && echo recoveredAfterUncertainResponse || echo installed)" \
      '.type == "confirmed" and .confirmation == $confirmation and .acceptedCount == "2"' \
      "$CASE/attempt/retry-0001.json" > /dev/null
    test "$(jq -c '{transactionId,eventId,imageBoundary,acceptedCount}' "$CASE/attempt/retry-0001.json")" = \
      "$(jq -c '{transactionId,eventId,imageBoundary,acceptedCount}' "$FIXTURE/content-attempt/retry-0001.json")"
  fi
  "$MINI" retry --attempt "$CASE/attempt" --mode lookup \
    --socket "$CASE/private/mini.sock" > "$CASE/lookup.log" 2>&1
  jq -e '.type == "confirmed" and .confirmation == "replayed" and .acceptedCount == "2"' \
    "$CASE/attempt/retry-0002.json" > /dev/null
  test "$(jq -c '{transactionId,eventId,imageBoundary,acceptedCount}' "$CASE/attempt/retry-0002.json")" = \
    "$(jq -c '{transactionId,eventId,imageBoundary,acceptedCount}' "$FIXTURE/content-attempt/retry-0001.json")"
  cleanup
  SERVER_PID=
  unset MINI_TEST_MODE MINI_TEST_CASE MINI_TEST_STORE MINI_TEST_FIXTURE
done
shasum -a 256 "$HOST" "$MINI" "$STORE" "$SIGNATURE" \
  "$FIXTURE/image-birth.bin" "$FIXTURE/image-content.bin" "$FIXTURE/image-joint.bin" \
  "$FIXTURE/content-attempt/call.bin" "$ROOT"/*/physical-after.bin \
  > "$ROOT/sha256.txt"
printf 'PASS physical exact-readback session gates; evidence %s\n' "$ROOT"
