#!/bin/sh
set -eu
umask 077
F=/home/hbox/mini-ticket-tool-fixture-r8
mkdir -m 700 "$F" "$F/root" "$F/bad-root" "$F/stage" "$F/stage/issue"
printf '#!/bin/sh\nset -eu\n[ "$2" = inspect ] && [ "$3" = application-grain-share-issue-plan ] || exit 2\ncp /home/hbox/mini-ticket-tool-fixture-r8/stage/issue/plan-inspected.json "$5"\n' > "$F/host"
chmod 755 "$F/host"
printf '{"domain":8501}\n' > "$F/config.json"
head -c 32 /dev/zero > "$F/key"
chmod 600 "$F/config.json" "$F/key"
S="$F/operator.sock"
perl -MIO::Socket::UNIX -MSocket -e '$s=IO::Socket::UNIX->new(Type=>SOCK_STREAM,Local=>$ARGV[0],Listen=>1) or die; sleep 60' "$S" &
PID=$!
trap 'kill "$PID" 2>/dev/null || :' EXIT
while [ ! -S "$S" ]; do sleep 0.1; done
M=/home/hbox/mini-ticket-tool-mock-r8.sh
H="$F/host"
MS=$(sha256sum "$M" | cut -d ' ' -f1)
HS=$(sha256sum "$H" | cut -d ' ' -f1)
T=/home/hbox/mini-reserve-ticket-tool.sh
chmod 755 "$T"
"$T" prepare "$M" "$H" "$F/config.json" "$S" "$F/key" "$F/root" alice-web 86023001 "$MS" "$HS"
if "$T" send "$F/root" > "$F/first-send.log" 2>&1; then exit 3; fi
if "$T" send "$F/root" > "$F/second-send.log" 2>&1; then exit 4; fi
touch "$F/fail-after-once"
if "$T" lookup "$F/root" > "$F/lost-readback.log" 2>&1; then exit 7; fi
[ -d "$F/root/alice-web-86023001/after-query-0000" ]
[ -f "$F/root/active.json" ]
"$T" lookup "$F/root"
[ "$(wc -l < "$F/sends.log")" -eq 1 ]
[ "$(wc -l < "$F/lookups.log")" -eq 2 ]
[ -d "$F/root/alice-web-86023001/after-query-0001" ]
[ "$(jq -r .nonce "$F/root/alice-web-86023001/after-intent-0000.json")" = 86023003 ]
[ "$(jq -r .nonce "$F/root/alice-web-86023001/after-intent-0001.json")" = 86023004 ]
[ -f "$F/root/alice-web-86023001/after-query-0000.stderr" ]
[ -f "$F/root/alice-web-86023001/after-query-0001.stderr" ]
jq -e '.receipt.acceptedCount == "30"' "$F/root/alice-web-86023001/confirmed.json" >/dev/null
jq -e '.page.grain.status == "3" and .page.grain.reserved == "3"' "$F/root/alice-web-86023001/after-view.json" >/dev/null
printf '{"route":"alice-web"}\n' > "$F/stage/scope.json"
printf '{"scope":"%s"}\n' "$F/stage/scope.json" > "$F/stage/stage.json"
printf 'exact-issue-plan' > "$F/stage/issue/plan.bin"
printf 'exact-issue-ingress' > "$F/stage/issue/ingress.bin"
printf '{"type":"application-grain-share-issue-plan-v1","finalizedGrainBirth":{"tool":{"task":"7902","capability":"81","observeCapability":"81","root":"123","before":{"generation":"1","status":"3","remaining":"22","reserved":"3"}},"parent":{"task":"7901"}}}\n' > "$F/stage/issue/plan-inspected.json"
printf '{"type":"minidregg-grain-share-issue-submit-v1"}\n' > "$F/stage/issue/submit-marker.json"
printf '{"type":"minidregg-grain-share-issue-receipt-anchor-v1","receipt":{"transactionId":"201","eventId":"202","acceptedCount":"31","imageBoundary":"203"}}\n' > "$F/stage/issue/receipt-anchor.json"
chmod 600 "$F/stage"/*.json "$F/stage/issue"/*
cp "$F/stage/issue/plan-inspected.json" "$F/plan-correct.json"
jq ' .finalizedGrainBirth.tool.before.reserved="2" ' "$F/plan-correct.json" > "$F/stage/issue/plan-inspected.json"
if "$T" advance-ticket "$F/root" "$F/stage/issue" > "$F/bad-plan.log" 2>&1; then exit 6; fi
[ -f "$F/root/active.json" ]
[ ! -e "$F/ticket-lookups.log" ]
cp "$F/plan-correct.json" "$F/stage/issue/plan-inspected.json"

"$T" advance-ticket "$F/root" "$F/stage/issue"
[ ! -e "$F/root/active.json" ]
[ -f "$F/root/closed-alice-web-86023001.json" ]
[ "$(wc -l < "$F/ticket-lookups.log")" -eq 1 ]
touch "$F/bad-status"
if "$T" prepare "$M" "$H" "$F/config.json" "$S" "$F/key" "$F/bad-root" bob-web 86023002 "$MS" "$HS" > "$F/bad-status.log" 2>&1; then exit 5; fi
[ ! -e "$F/bad-root/active.json" ]
mkdir -m 700 "$F/writable-binary-root"
chmod 777 "$H"
if "$T" prepare "$M" "$H" "$F/config.json" "$S" "$F/key" \
  "$F/writable-binary-root" bob-web 86023003 "$MS" "$HS" \
  > "$F/writable-binary.log" 2>&1; then exit 8; fi
[ ! -e "$F/writable-binary-root/active.json" ]
chmod 755 "$H"
printf 'first send: '; cat "$F/first-send.log"
printf 'second send: '; cat "$F/second-send.log"
printf 'lost readback: '; cat "$F/lost-readback.log"
printf 'stale before: '; cat "$F/bad-status.log"
printf 'writable binary: '; cat "$F/writable-binary.log"
printf 'one mock native send, exact lookup, event22 receipt/plan join, marker closed; bad before no send\n'
