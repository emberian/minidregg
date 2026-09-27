#!/bin/sh
# One retained r3 workroom continuation after the first signed query succeeded
# and the following jq metadata expression failed to compile. No new birth.
set -eu
umask 077

[ "$#" -eq 1 ] || { echo 'usage: recover-r3-workroom-query.sh ROOT' >&2; exit 2; }
R=$1
[ "$R" = /var/lib/minidregg/spk/fixtures/gitweb-v2-20260927-client-session-r3 ] || exit 2
W=$R/base/workroom
A=$R/continuations/gitweb-journey/base-resume-0001
OLD=$A/workroom-recovery-0001
P=$A/workroom-recovery-0002
D=$R/continuations/first-birth-retry-0002
V=$W/agents/verified
Q=$V/hermes-a-controller
STORE=$W/store/forward-link.sqlite3
HOST=$D/bin/minidregg-host-2649-fin-repair
MINI=/tank/dregg-build/minidregg-007b513-client-evidence/bin/mini-007b513
STORE_BINARY=/tank/dregg-build/minidregg-9746c47-helpers-evidence/bin/minidregg-link-sqlite-store-9746c47
SIGNATURE_BINARY=/tank/dregg-build/minidregg-9746c47-helpers-evidence/bin/minidregg-credential-signature-verifier-9746c47
SOURCE=$OLD/workroom-short-socket.sh
fail() { echo "r3 query recovery: $*" >&2; exit 2; }
sha() { sha256sum "$1" | cut -d ' ' -f 1; }
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
for dir in "$R" "$W" "$A" "$OLD" "$D" "$V" "$Q"; do protected_chain "$dir"; done
exec 9>"$A/lock"
flock -n 9 || fail 'another base continuation owns the lock'
[ -s "$A/workroom.started" ] || fail 'original phase was not started'
[ ! -e "$A/workroom.completed" ] && [ ! -L "$A/workroom.completed" ] || fail 'phase completed'
[ ! -e "$P" ] && [ ! -L "$P" ] || fail 'query recovery already attempted'
[ ! -e "$R/base/app-attempt" ] && [ ! -L "$R/base/app-attempt" ] || fail 'app phase began'
[ "$(sha "$STORE")" = e5515e158fdfb03afdafc3951a3a73c2b779bac37eb8428a146c8244611e30e5 ] || fail 'Store changed'
[ "$(sha "$HOST")" = 2c28356f8c59dc5ec4d17c594ed718bca3f73f336790c8eb30bb395557f28bf7 ] || fail 'Host changed'
[ "$(sha "$MINI")" = a339b384f9a6c15d9c3f64e5df243b230da7e5a50d0b252cafbbcd94ad8e47ee ] || fail 'Mini changed'
[ "$(sha "$SOURCE")" = 8bc251a6525cc8fe6a02619a17bb40410c905aed09bff640e4cff97388d8e26b ] || fail 'prior recovery source changed'
[ "$(sha "$OLD/workroom.stderr")" = 6c383f859ecd16e4361100534bef5da4f2b9ac8f680b4bd168e087ba10bb7c48 ] || fail 'prior jq error changed'
# The literal jq diagnostic names the unbound variable; expansion is unwanted.
# shellcheck disable=SC2016
grep -Fq 'jq: error: $cap is not defined' "$OLD/workroom.stderr" || fail 'prior error is not the known jq failure'
(cd / && sha256sum -c "$A/input-sha256.txt" >/dev/null) || fail 'original input manifest changed'
(cd / && sha256sum -c "$A/generated-sha256.txt" >/dev/null) || fail 'original generated manifest changed'
[ "$(sha "$V/born-views.jsonl")" = e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855 ] || fail 'first query was already aggregated'
[ "$(sha "$V/hermes-a-controller-intent.json")" = 8ec01d62dfdbf36127b321ea2a8e55344caa2be669abe72bb6c0911eaf9ed21c ] || fail 'outer query intent changed'
[ "$(sha "$V/hermes-a-controller.stdout")" = 511bf2e6dbb6e7c35c6d8300dc2f8b108b5c6ee1db8b620bf63a0d1961fe0da7 ] || fail 'query stdout changed'
# Pin the complete private query directory, not just the presented view.
while read -r expected name; do
  [ -f "$Q/$name" ] && [ ! -L "$Q/$name" ] || fail "query member absent or linked: $name"
  [ "$(sha "$Q/$name")" = "$expected" ] || fail "query member changed: $name"
done <<'PINS'
e7be22d4ce43ed2d8bf7d376257ef369bc28cf9ba54040e723a33278aaf61ad9 attempt.json
3fbf3a6c457338ad1b710aed5085b16d9baa68cadd0fc3add4baa744750fc7a0 challenge.bin
b3ffd2f274c3465ddd03216770456406c662b50e7c400983ba92827cd48d8ac0 challenge.json
c2c79aa69f66ecc7922f69f620a9dd9ca24cfea25cd94282fcb1a40c2b8296b8 config.json
bbbe189fbeb151d423a1c940bfb886a1d7ece40417b449f2bd04bd7cb2e7b116 intent.bin
8ec01d62dfdbf36127b321ea2a8e55344caa2be669abe72bb6c0911eaf9ed21c intent.json
0233f4abf4aa599b705827437315e13879ac121bd243dca571d12aa685c86fce observation-signatures.bin
1ee6e7139d43f901838c7fd56bbaa5796221086059cdb7eca9e9a22dc5c64d30 observation-signatures.json
ed3f76988f2b4f73bb8350ae17e1840de80a8b966e0311e020c0bae26ca5e73c signed-observation.bin
29479f9c821ce9e0f96b81b5adb536602ac81f3c1f06bc29ebacb82e2abe5eb8 view.bin
e1d9e99060599c41ebf04ecbbd267f5a4ea8505b21a1ec2fbfc67885f0c1b90a view.json
PINS
[ "$(find "$Q" -mindepth 1 -maxdepth 1 | wc -l | tr -d ' ')" = 11 ] || fail 'unexpected query directory members'
[ "$(find "$V" -mindepth 1 -maxdepth 1 | wc -l | tr -d ' ')" = 4 ] || fail 'unexpected verified entries'
for entry in born-views.jsonl hermes-a-controller hermes-a-controller-intent.json hermes-a-controller.stdout; do
  [ -e "$V/$entry" ] && [ ! -L "$V/$entry" ] || fail "verified entry absent or linked: $entry"
done
old_unit=mini-spk-platform-r3-workroom-recovery-client-session.service
status=$(systemctl --user show "$old_unit" -p ActiveState --value)
main_pid=$(systemctl --user show "$old_unit" -p MainPID --value)
case "$status" in inactive|failed) ;; *) fail "old unit state is $status" ;; esac
[ "$main_pid" = 0 ] || fail "old unit MainPID is $main_pid"
journalctl --user -u "$old_unit" --no-pager --output=cat |
  grep -Fq 'Main process exited, code=exited, status=3/NOTIMPLEMENTED' || fail 'old unit failure not retained'
! fuser -s "$STORE" 2>/dev/null || fail 'Store has a live opener'
mkdir -m 700 "$P" || fail 'query recovery already claimed'
sha256sum "$SOURCE" "$OLD/workroom.stderr" "$V/hermes-a-controller-intent.json" \
  "$V/hermes-a-controller.stdout" "$Q"/* "$V/born-views.jsonl" >"$P/retained-sha256.txt"
sync -f "$P/retained-sha256.txt"
# Archive exact first-query bytes separately before the aggregate file is
# extended. Never move, rewrite, or delete the original query directory.
mkdir -m 700 "$P/retained-query"
cp -p "$Q"/* "$P/retained-query/"
cp -p "$V/hermes-a-controller-intent.json" "$V/hermes-a-controller.stdout" "$P/retained-query/"
cp -p "$V/born-views.jsonl" "$P/retained-query/"
sha256sum "$P/retained-query"/* >"$P/retained-query-sha256.txt"
for file in "$P/retained-query"/*; do sync -f "$file"; done
sync -f "$P/retained-query-sha256.txt"
sync -f "$P/retained-query"
# These are pure source inspection and JSON equality checks; no new signed query.
"$HOST" "$W/deployment/pinned-config.json" inspect view-resource "$Q/view.bin" "$P/reinspected-view.json"
jq -S . "$Q/view.json" >"$P/original-view-sorted.json"
jq -S . "$P/reinspected-view.json" >"$P/reinspected-view-sorted.json"
cmp "$P/original-view-sorted.json" "$P/reinspected-view-sorted.json" || fail 'source view inspection differs'
cmp "$V/hermes-a-controller-intent.json" "$Q/intent.json" || fail 'outer query intent differs'
jq -e --slurpfile allocation "$R/source-stage/agent-allocation.json" '
  .subject == ($allocation[0].agents[] | select(.route == "hermes-a") | .controller.subject) and
  .purpose.target == ($allocation[0].agents[] | select(.route == "hermes-a") | .controller.task) and
  .grants[0].capability == ($allocation[0].agents[] | select(.route == "hermes-a") | .plannedCaps.parentOwner) and
  .nonce == "57920" and .purpose.type == "query" and .purpose.view == "resource"' \
  "$Q/intent.json" >/dev/null || fail 'retained query does not match allocation'
jq -e '.type == "resource" and .page.grain ==
  {task:"7920",generation:"0",status:"0",remaining:"100",reserved:"0"}' \
  "$P/reinspected-view.json" >/dev/null || fail 'retained grain view differs'
# Change only the first-query block: it reuses retained signed evidence. Keep
# all later query, policy, delegation, and birth checks byte-for-byte.
awk '
  $0 == "mkdir -m 700 \"$EVIDENCE/agents/verified\"" {
    print "[ -d \"$EVIDENCE/agents/verified\" ] && [ ! -L \"$EVIDENCE/agents/verified\" ] || exit 2"; mkdirSeen++; next
  }
  /    jq -n --arg s "\$subject" --arg t "\$task" --arg c "\$cap"/ && !seen {print "    if [ \"$label\" = hermes-a-controller ]; then"; print "      [ \"$subject:$task:$cap\" = 10:7920:201 ] || exit 2"; print "    else"; seen=1}
  seen && /      >"\$EVIDENCE\/agents\/verified\/\$label.stdout"/ && !closed {print; print "    fi"; closed=1; next}
  {gsub(/capability:\$cap,root:/,"capability:$capability,root:"); print}
  END {if (mkdirSeen != 1 || !seen || !closed) exit 2}
' "$SOURCE" >"$P/workroom-reuse-first-query.sh" || fail 'exact query substitution refused'
chmod 700 "$P/workroom-reuse-first-query.sh"
/bin/sh -n "$P/workroom-reuse-first-query.sh" || fail 'recovery script syntax refused'
sha256sum "$SOURCE" "$P/workroom-reuse-first-query.sh" >"$P/script-sha256.txt"
sync -f "$P/workroom-reuse-first-query.sh"
sync -f "$P/script-sha256.txt"
sync -f "$P"
[ "$(sha "$STORE")" = e5515e158fdfb03afdafc3951a3a73c2b779bac37eb8428a146c8244611e30e5 ] || fail 'Store changed before continuation'
/bin/sh "$P/workroom-reuse-first-query.sh" "$W" "$HOST" "$MINI" \
  "$STORE_BINARY" "$SIGNATURE_BINARY" "$R/source-stage/agent-allocation.json" \
  "$A/adopted-birth-receipt.json" "$P" >"$P/workroom.stdout" 2>"$P/workroom.stderr"
[ -s "$V/birth-evidence.json" ] || fail 'workroom signed evidence absent'
sha256sum "$V/birth-evidence.json" "$P/workroom-reuse-first-query.sh" >"$P/success-sha256.txt"
sync -f "$P/success-sha256.txt"
jq -n --arg recovery "$P" --arg signedEvidenceSha256 "$(sha "$V/birth-evidence.json")" '
  {protocol:"mini-spk-r3-workroom-recovery-link-v1",recovery:$recovery,
   signedEvidenceSha256:$signedEvidenceSha256}' >"$A/workroom-recovery-link.json"
sync -f "$A/workroom-recovery-link.json"
printf '%s\n' 'complete via workroom-recovery-0002' >"$A/workroom.completed"
sync -f "$A/workroom.completed"
sync -f "$A"
printf '%s\n' "$A/workroom.completed"
