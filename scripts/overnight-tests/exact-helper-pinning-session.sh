#!/bin/sh
# A running native session must use its private verifier snapshot after the
# configured source pathname changes or disappears. Writes only NEW_ROOT.
set -eu
umask 077

if [ "$#" -ne 6 ]; then
  echo "usage: $0 HOST MINI STORE SIGNATURE-HELPER FIXTURE NEW_ROOT" >&2
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
test ! -e "$ROOT" || { echo "refusing existing root: $ROOT" >&2; exit 2; }
mkdir "$ROOT"
ROOT=$(CDPATH='' cd -- "$ROOT" && pwd)
FIXTURE=$(CDPATH='' cd -- "$FIXTURE" && pwd)
HOST=$(CDPATH='' cd -- "$(dirname -- "$HOST")" && pwd)/$(basename -- "$HOST")
MINI=$(CDPATH='' cd -- "$(dirname -- "$MINI")" && pwd)/$(basename -- "$MINI")
STORE=$(CDPATH='' cd -- "$(dirname -- "$STORE")" && pwd)/$(basename -- "$STORE")
SIGNATURE=$(CDPATH='' cd -- "$(dirname -- "$SIGNATURE")" && pwd)/$(basename -- "$SIGNATURE")
if printf '%s' "$ROOT$STORE" | grep -F -q -e '"' -e '\' ||
   printf '%s' "$ROOT$STORE" | LC_ALL=C grep -q '[[:cntrl:]]'; then
  echo 'test path needs JSON escaping' >&2
  exit 2
fi
mkdir "$ROOT/store" "$ROOT/private" "$ROOT/content" "$ROOT/joint"
chmod 700 "$ROOT/private"
cp "$SIGNATURE" "$ROOT/source-verifier"
chmod 700 "$ROOT/source-verifier"
"$STORE" cas "$ROOT/store" - "$FIXTURE/image-birth.bin" > "$ROOT/bootstrap.log"
MINI_TEST_CONFIG_ROOT="$ROOT/store" \
  MINI_TEST_CONFIG_STORE="$STORE" \
  MINI_TEST_CONFIG_SIG="$ROOT/source-verifier" \
  perl -0777 -pe '
    s/("storageRoot"\s*:\s*")[^"]*"/${1}$ENV{MINI_TEST_CONFIG_ROOT}"/ or die "missing storageRoot";
    s/("storageBinary"\s*:\s*")[^"]*"/${1}$ENV{MINI_TEST_CONFIG_STORE}"/ or die "missing storageBinary";
    s/("signatureBinary"\s*:\s*")[^"]*"/${1}$ENV{MINI_TEST_CONFIG_SIG}"/ or die "missing signatureBinary";
  ' "$FIXTURE/deployment/pinned-config.json" > "$ROOT/config.json"

for name in content joint; do
  cp "$FIXTURE/$name-attempt/call.bin" "$ROOT/$name/call.bin"
  jq -n --arg host "$HOST" --arg config "$ROOT/config.json" \
    --arg socket "$ROOT/private/mini.sock" \
    '{format:"minidregg-resource-client-attempt-v1",operation:"submit",host:$host,config:$config,socket:$socket}' \
    > "$ROOT/$name/attempt.json"
done
SERVER_PID=
cleanup() {
  if [ -n "$SERVER_PID" ]; then
    kill "$SERVER_PID" 2>/dev/null || true
    wait "$SERVER_PID" 2>/dev/null || true
  fi
}
trap cleanup EXIT
"$MINI" serve --host "$HOST" --config "$ROOT/config.json" \
  --socket "$ROOT/private/mini.sock" > "$ROOT/serve.log" 2>&1 &
SERVER_PID=$!
ready=0
for _ in 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18 19 20; do
  if [ -S "$ROOT/private/mini.sock" ]; then ready=1; break; fi
  sleep 0.25
done
test "$ready" -eq 1
"$MINI" describe --host "$HOST" --config "$ROOT/config.json" \
  --socket "$ROOT/private/mini.sock" > "$ROOT/describe.json"

# A fresh session would execute the replacement, but this process must keep
# using the verifier bytes pinned before the replacement.
mv "$ROOT/source-verifier" "$ROOT/source-verifier.original"
printf '#!/bin/sh\nexit 91\n' > "$ROOT/source-verifier"
chmod 700 "$ROOT/source-verifier"
"$MINI" retry --attempt "$ROOT/content" --mode submit \
  --socket "$ROOT/private/mini.sock" > "$ROOT/content-submit.log" 2>&1
jq -e '.type == "confirmed" and .confirmation == "installed" and .acceptedCount == "2"' \
  "$ROOT/content/retry-0001.json" > /dev/null
test "$(jq -c '{transactionId,eventId,imageBoundary,acceptedCount}' "$ROOT/content/retry-0001.json")" = \
  "$(jq -c '{transactionId,eventId,imageBoundary,acceptedCount}' "$FIXTURE/content-attempt/retry-0001.json")"

# Now the configured source path is absent. The same running session still
# verifies a second, independently signed call against its private snapshot.
rm "$ROOT/source-verifier"
"$MINI" retry --attempt "$ROOT/joint" --mode submit \
  --socket "$ROOT/private/mini.sock" > "$ROOT/joint-submit.log" 2>&1
jq -e '.type == "confirmed" and .confirmation == "installed" and .acceptedCount == "3"' \
  "$ROOT/joint/retry-0001.json" > /dev/null
test "$(jq -c '{transactionId,eventId,imageBoundary,acceptedCount}' "$ROOT/joint/retry-0001.json")" = \
  "$(jq -c '{transactionId,eventId,imageBoundary,acceptedCount}' "$FIXTURE/joint-attempt/outcome.json")"
"$STORE" read-to "$ROOT/store" "$ROOT/physical-after.bin"
cmp "$ROOT/physical-after.bin" "$FIXTURE/image-joint.bin"

# A newly started host cannot make the same claim after its configured source
# helper disappears. This check never uses the running session's private copy.
if "$HOST" "$ROOT/config.json" stdio < /dev/null > "$ROOT/fresh.stdout" 2> "$ROOT/fresh.stderr"; then
  echo 'fresh host unexpectedly started with absent verifier source' >&2
  exit 1
fi
test -s "$ROOT/fresh.stderr"
cleanup
SERVER_PID=
shasum -a 256 "$HOST" "$MINI" "$STORE" "$SIGNATURE" \
  "$ROOT/source-verifier.original" "$FIXTURE/image-joint.bin" \
  "$ROOT/physical-after.bin" "$ROOT/content/retry-0001.bin" \
  "$ROOT/joint/retry-0001.bin" > "$ROOT/sha256.txt"
printf 'PASS native session pins verifier across source replacement and removal; evidence %s\n' "$ROOT"
