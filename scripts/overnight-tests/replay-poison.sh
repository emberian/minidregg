#!/bin/sh
# Real Mini host + native SQLite CAS replay regression. Writes only NEW_ROOT.
set -eu
umask 077

if [ "$#" -ne 5 ]; then
  echo "usage: $0 HOST MINI STORE SIGNATURE-HELPER NEW_ROOT" >&2
  exit 2
fi
HOST=$1
MINI=$2
STORE_BINARY=$3
SIGNATURE_BINARY=$4
ROOT=$5
HERE=$(CDPATH='' cd -- "$(dirname -- "$0")" && pwd)
REPO=$(CDPATH='' cd -- "$HERE/../.." && pwd)
CLIENT_DIR=$REPO/native/resource-client

for program in "$HOST" "$MINI" "$STORE_BINARY" "$SIGNATURE_BINARY"; do
  test -x "$program" || { echo "not executable: $program" >&2; exit 2; }
done
test ! -e "$ROOT" || { echo "refusing existing root: $ROOT" >&2; exit 2; }
mkdir "$ROOT"
ROOT=$(CDPATH='' cd -- "$ROOT" && pwd)
FIXTURE=$ROOT/fixture
CONFIG=$FIXTURE/deployment/pinned-config.json
STORE_ROOT=$FIXTURE/store
rustc --edition=2021 "$HERE/replay-poison.rs" -o "$ROOT/replay-poison"

# Capture the exact native images produced at three already checked commits.
# The source acceptance script remains untouched; markers must be unique.
awk -v client_dir="$CLIENT_DIR" -v repo="$REPO" '
  /^HERE=/ { print "HERE=\"" client_dir "\""; next }
  /^REPO=/ { print "REPO=\"" repo "\""; next }
  { print }
  /"\$EVIDENCE\/birth-attempt\/outcome.json" >\/dev\/null$/ {
    print "\"$STORE_BINARY\" read-to \"$EVIDENCE/store\" \"$EVIDENCE/image-birth.bin\""
    birth++
  }
  /^test "\$CALL_HASH_BEFORE" = "\$CALL_HASH_AFTER"$/ {
    print "\"$STORE_BINARY\" read-to \"$EVIDENCE/store\" \"$EVIDENCE/image-content.bin\""
    content++
  }
  /"\$EVIDENCE\/joint-attempt\/outcome.json" >\/dev\/null$/ {
    print "\"$STORE_BINARY\" read-to \"$EVIDENCE/store\" \"$EVIDENCE/image-joint.bin\""
    joint++
  }
  END {
    if (birth != 1 || content != 1 || joint != 1) {
      print "acceptance capture marker changed" > "/dev/stderr"
      exit 1
    }
  }
' "$CLIENT_DIR/acceptance.sh" > "$ROOT/acceptance-instrumented.sh"
chmod 700 "$ROOT/acceptance-instrumented.sh"
export MINI STORE_BINARY SIGNATURE_BINARY
"$ROOT/acceptance-instrumented.sh" "$HOST" "$FIXTURE" > "$ROOT/acceptance.log" 2>&1

for image in image-birth.bin image-content.bin image-joint.bin; do
  test -s "$FIXTURE/$image" || { echo "missing valid image capture: $image" >&2; exit 1; }
done
cmp -s "$FIXTURE/image-birth.bin" "$FIXTURE/image-content.bin" && {
  echo "birth and content images unexpectedly equal" >&2; exit 1;
}
cmp -s "$FIXTURE/image-content.bin" "$FIXTURE/image-joint.bin" && {
  echo "content and joint images unexpectedly equal" >&2; exit 1;
}

# The live stdio host opens height 13, then SQLite atomically publishes the
# accepted height-11 prefix. Its next request must close/fail permanently.
timeout 120 "$ROOT/replay-poison" "$HOST" "$CONFIG" "$STORE_BINARY" "$STORE_ROOT" \
  "$FIXTURE/image-joint.bin" "$FIXTURE/image-birth.bin" > "$ROOT/rollback.log" 2>&1
"$HOST" "$CONFIG" describe > "$ROOT/cold-birth-describe.json"

# Build another valid height-12 branch from the same height-11 parent. Both
# branch images cold-open under the native verifier before the live swap.
jq '.nonce = "40002" |
    .purpose.draft.command.nonce = "40003" |
    .purpose.draft.command.targets[0].payload.actions[0].rootElement = "1002"' \
  "$FIXTURE/content-intent.json" > "$ROOT/fork-intent.json"
"$MINI" submit --host "$HOST" --config "$CONFIG" --intent "$ROOT/fork-intent.json" \
  --key "$FIXTURE/alice.key" --dir "$ROOT/fork-attempt" > "$ROOT/fork-submit.log" 2>&1
jq -e '.type == "confirmed" and .confirmation == "installed" and .acceptedCount == "2"' \
  "$ROOT/fork-attempt/outcome.json" > /dev/null
"$STORE_BINARY" read-to "$STORE_ROOT" "$ROOT/image-fork.bin"
cmp -s "$FIXTURE/image-content.bin" "$ROOT/image-fork.bin" && {
  echo "same-height branch images unexpectedly equal" >&2; exit 1;
}
"$HOST" "$CONFIG" describe > "$ROOT/cold-fork-describe.json"
"$STORE_BINARY" cas "$STORE_ROOT" "$ROOT/image-fork.bin" "$FIXTURE/image-content.bin" \
  > "$ROOT/restore-content-cas.log"
rg -q 'Installed' "$ROOT/restore-content-cas.log"
"$HOST" "$CONFIG" describe > "$ROOT/cold-content-describe.json"
timeout 120 "$ROOT/replay-poison" "$HOST" "$CONFIG" "$STORE_BINARY" "$STORE_ROOT" \
  "$FIXTURE/image-content.bin" "$ROOT/image-fork.bin" > "$ROOT/same-height-fork.log" 2>&1

shasum -a 256 "$HOST" "$MINI" "$STORE_BINARY" "$SIGNATURE_BINARY" \
  "$FIXTURE/image-birth.bin" "$FIXTURE/image-content.bin" \
  "$FIXTURE/image-joint.bin" "$ROOT/image-fork.bin" > "$ROOT/sha256.txt"
printf 'PASS real native rollback and same-height fork poison; evidence %s\n' "$ROOT"
