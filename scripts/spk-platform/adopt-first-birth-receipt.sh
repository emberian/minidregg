#!/bin/sh
# Append the exact accepted r3 birth responses to the original attempt's retry
# namespace. This does not submit, look up, or synthesize an outcome.
set -eu
umask 077

[ "$#" -eq 1 ] || { echo 'usage: adopt-first-birth-receipt.sh ROOT' >&2; exit 2; }
R=$1
[ "$R" = /var/lib/minidregg/spk/fixtures/gitweb-v2-20260927-client-session-r3 ] || {
  echo 'adoption requires the retained r3 root' >&2; exit 2;
}
A="$R/base/workroom/birth-attempt"
D="$R/continuations/first-birth-retry-0002"
P="$D/adoption-0001"
fail() { echo "r3 birth adoption: $*" >&2; exit 2; }
sha() { sha256sum "$1" | cut -d ' ' -f 1; }
private_file() {
  [ -f "$1" ] && [ ! -L "$1" ] && [ -s "$1" ] || fail "source absent or linked: $1"
  [ "$(stat -c '%u' "$1")" = "$(id -u)" ] || fail "foreign source: $1"
  mode=$(stat -c '%a' "$1")
  [ $((0$mode & 022)) -eq 0 ] || fail "writable source: $1"
}
protected_chain() {
  dir=$1
  while :; do
    [ -d "$dir" ] && [ ! -L "$dir" ] || fail "directory absent or linked: $dir"
    owner=$(stat -c '%u' "$dir")
    mode=$(stat -c '%a' "$dir")
    { [ "$owner" = 0 ] || [ "$owner" = "$(id -u)" ]; } || fail "foreign directory: $dir"
    [ $((0$mode & 022)) -eq 0 ] || fail "writable directory ancestor: $dir"
    [ "$dir" = / ] && break
    dir=${dir%/*}; [ -n "$dir" ] || dir=/
  done
}
for dir in "$R" "$A" "$D"; do
  protected_chain "$dir"
done
[ "$(stat -c '%a' "$A")" = 700 ] || fail 'historical lookup requires mode-0700 attempt'
exec 9>"$D/native.lock"
flock -n 9 || fail 'another native action owns the lock'
[ ! -e "$P" ] && [ ! -L "$P" ] || fail 'adoption already attempted; reconcile it'
[ ! -e "$A/outcome.json" ] && [ ! -L "$A/outcome.json" ] &&
  [ ! -e "$A/outcome.bin" ] && [ ! -L "$A/outcome.bin" ] || fail 'original outcome appeared'
for target in retry-0002.bin retry-0002.json retry-0003.bin retry-0003.json; do
  [ ! -e "$A/$target" ] && [ ! -L "$A/$target" ] || fail "retry name already used: $target"
done
private_file "$A/call.bin"
private_file "$A/config.json"
[ -f "$A/retry-0001.json" ] && [ ! -L "$A/retry-0001.json" ] &&
  [ "$(stat -c '%u' "$A/retry-0001.json")" = "$(id -u)" ] ||
  fail 'historical lookup absent, linked, or foreign'
# The historical Mini-produced retry is mode 0664. Keep its bytes/metadata
# unchanged; its exact hash and the protected mode-0700 attempt are the pin.
private_file "$D/transition-intent.json"
private_file "$D/final-verdict.json"
private_file "$D/submit.bin"
private_file "$D/submit.json"
private_file "$D/lookup-after-submit.bin"
private_file "$D/lookup-after-submit.json"
[ "$(sha "$A/call.bin")" = 1ff9d4ad41644a376884d13a6092787a2ca6a2a7d99c30659263f04221d8bdb7 ] || fail 'original call differs'
[ "$(sha "$A/config.json")" = c2c79aa69f66ecc7922f69f620a9dd9ca24cfea25cd94282fcb1a40c2b8296b8 ] || fail 'original config differs'
[ "$(sha "$A/retry-0001.json")" = dfec3d8544c62ae3e669e14eb868872ad622867d7655377e80cb0d7fc86d572d ] || fail 'historical absent lookup differs'
[ "$(sha "$D/transition-intent.json")" = 6662d5f028e21605eeb8130dd92bed9edc18dd52bb53aa72b4ccdea9865f0087 ] || fail 'transition intent differs'
[ "$(sha "$D/final-verdict.json")" = 2832a69d4b071bfd3277a6aae27a505610df33da075eebe5074d3bf51875603a ] || fail 'sealed verdict differs'
[ "$(sha "$D/submit.bin")" = 21672e21e1caa002ad76e906542de4b5c77eabd73e6587180c046eb823d31c88 ] || fail 'submit bytes differ'
[ "$(sha "$D/submit.json")" = 7743232a6bfb077ce28c4c82f6dbb23ca8a7752e06ad57cc679019b776bb20cd ] || fail 'submit projection differs'
[ "$(sha "$D/lookup-after-submit.bin")" = 4beb5fe21c57769135e848dc90f524a49f094dd49dd9cb189544069eb95b94b3 ] || fail 'lookup bytes differ'
[ "$(sha "$D/lookup-after-submit.json")" = 6c181cc081c32fe71c9656255f8a894c8cbe15b7aff4a0c0a04f200f9eea2925 ] || fail 'lookup projection differs'
[ "$(sha "$R/base/workroom/store/forward-link.sqlite3")" = e5515e158fdfb03afdafc3951a3a73c2b779bac37eb8428a146c8244611e30e5 ] || fail 'accepted Store differs'
jq -e '.type == "absent"' "$A/retry-0001.json" >/dev/null || fail 'historical lookup not absent'
jq -e '.type == "confirmed" and .confirmation == "installed" and .acceptedCount == "1"' "$D/submit.json" >/dev/null || fail 'submit not installed'
jq -e '.type == "confirmed" and .confirmation == "replayed" and .acceptedCount == "1"' "$D/lookup-after-submit.json" >/dev/null || fail 'lookup not replayed'
[ "$(jq -Sc '{transactionId,eventId,acceptedCount,worldRoot}' "$D/submit.json")" = \
  "$(jq -Sc '{transactionId,eventId,acceptedCount,worldRoot}' "$D/lookup-after-submit.json")" ] || fail 'four-field receipts differ'
[ "$(stat -c '%d' "$D")" = "$(stat -c '%d' "$A")" ] || fail 'source and attempt are on different filesystems'

# Creation of this private plan is the durable boundary. Any partial links
# thereafter are uncertain evidence and require manual reconciliation.
mkdir -m 700 "$P" || fail 'adoption already claimed'
jq -n --arg action "$D" --arg attempt "$A" \
  --arg submitBinarySha256 21672e21e1caa002ad76e906542de4b5c77eabd73e6587180c046eb823d31c88 \
  --arg submitJsonSha256 7743232a6bfb077ce28c4c82f6dbb23ca8a7752e06ad57cc679019b776bb20cd \
  --arg lookupBinarySha256 4beb5fe21c57769135e848dc90f524a49f094dd49dd9cb189544069eb95b94b3 \
  --arg lookupJsonSha256 6c181cc081c32fe71c9656255f8a894c8cbe15b7aff4a0c0a04f200f9eea2925 '
  {protocol:"mini-spk-r3-first-birth-receipt-adoption-v1",originalAttempt:$attempt,
   protectedAction:$action,operation:"private-copy-then-atomic-noclobber-link",
   mappings:[
     {source:($action+"/submit.bin"),target:($attempt+"/retry-0002.bin"),sha256:$submitBinarySha256},
     {source:($action+"/submit.json"),target:($attempt+"/retry-0002.json"),sha256:$submitJsonSha256},
     {source:($action+"/lookup-after-submit.bin"),target:($attempt+"/retry-0003.bin"),sha256:$lookupBinarySha256},
     {source:($action+"/lookup-after-submit.json"),target:($attempt+"/retry-0003.json"),sha256:$lookupJsonSha256}]}' >"$P/provenance.json"
sync -f "$P/provenance.json"
sync -f "$P"
sync -f "$D"
cp "$D/submit.bin" "$P/stage-retry-0002.bin"
cp "$D/submit.json" "$P/stage-retry-0002.json"
cp "$D/lookup-after-submit.bin" "$P/stage-retry-0003.bin"
cp "$D/lookup-after-submit.json" "$P/stage-retry-0003.json"
for target in retry-0002.bin retry-0002.json retry-0003.bin retry-0003.json; do
  case "$target" in
    retry-0002.bin) source="$D/submit.bin" ;;
    retry-0002.json) source="$D/submit.json" ;;
    retry-0003.bin) source="$D/lookup-after-submit.bin" ;;
    retry-0003.json) source="$D/lookup-after-submit.json" ;;
  esac
  [ "$(sha "$P/stage-$target")" = "$(sha "$source")" ] || fail "private copy differs: $target"
  sync -f "$P/stage-$target"
done
sync -f "$P"
# Each link is atomic and fails if a retry name appeared. The stage copies are
# independent of the protected original response files and remain as evidence.
ln "$P/stage-retry-0002.bin" "$A/retry-0002.bin"
ln "$P/stage-retry-0002.json" "$A/retry-0002.json"
ln "$P/stage-retry-0003.bin" "$A/retry-0003.bin"
ln "$P/stage-retry-0003.json" "$A/retry-0003.json"
for target in retry-0002.bin retry-0002.json retry-0003.bin retry-0003.json; do sync -f "$A/$target"; done
sync -f "$A"
sha256sum "$A/retry-0002.bin" "$A/retry-0002.json" \
  "$A/retry-0003.bin" "$A/retry-0003.json" >"$P/target-sha256.txt"
sync -f "$P/target-sha256.txt"
printf '%s\n' 'four exact original-attempt retry names adopted; outcome.json untouched' >"$P/complete.txt"
sync -f "$P/complete.txt"
sync -f "$P"
printf '%s\n' "$P/complete.txt"
