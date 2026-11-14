#!/usr/bin/env bash
# THIN CONSENT (PLAN-SCOPED-REPLAY): a member signs a turn without replaying
# the Store. Its consent provider (frames 230-232, `Kernel.NativeThinConsent`)
# checks every signing header against the member's own command and checks the
# target views the Host served under the member's observe grant against the
# root the signed command names, and shows the post. Rows:
#   T1  honest: the shown post root is the committed one (the next proposal's
#       expectedTargetRoot, authored from a fresh signed read)
#   FB  a Host whose plan carries the slots of ANOTHER command: refused
#       headerMismatch before anything is signed
#   FA  a Host serving a view of another state: the root recomputed from its
#       opening is not the signed root, refused servedRootMismatch before
#       anything is signed
#   T2  honest again after the faults: shown = committed
#   N1  a member whose observe grant is narrowed to one field: thin consent
#       checks the served view by its salted opening, shows the post at the
#       opened field with no post root (the opening seals the rest), and the
#       turn commits
#   N2  a member with no grant on the target: the Host refuses the signed read,
#       serves no bytes, and nothing is signed
#   S1  a signed call whose target moved, for a signer who observes the target:
#       refused naming the target (phase stale-target)
#   S2  the same for a signer whose observe grant is narrowed: the uniform
#       undisclosed frame
#   D1  honest thin delegation: no view served; the shown parent is the signed
#       one, and the turn commits
#   DF  a Host proposing the slot of a delegation over ANOTHER parent: refused
#       headerMismatch before anything is signed (the plant is asserted first)
#   KR  a whole kind definition read beside a write: checked by its served opening, shown as a
#       read, signed; the Host lying about the kind read's view alone is refused before signing
#   SR  a write the Host's semantics refuses (it creates a field the cell did not declare) is
#       refused when the Host prepares the plan: no plan reaches the consent provider, nothing is
#       shown, nothing is signed, nothing commits. The Host runs the semantics before it proposes
#       anything to sign, so a member is shown a post only for an operation the semantics has
#       admitted at the signed root
#   M   (only with THIN_MUTANT_PROVIDER: a provider built with the served-root
#       comparison removed) the mutant accepts a view of another state, shows a
#       post that differs from the one that commits; the real provider refused
#       the same input in FA
# Inputs as journey.d/jworld-kind.sh, plus THIN_CONSENT_PROVIDER (the
# provider to check against; default: minidregg-client-consent beside HOST).
set -euo pipefail
umask 077
: "${JOURNEY_STEP_DIR:?}" "${MINI:?}" "${HOST:?}" "${CONFIG:?}" "${SOCKET:?}"
: "${SPONSOR_WS:?}" "${SPONSOR_SUBJECT:?}" "${NEWCOMER_WS:?}" "${NEWCOMER_SUBJECT:?}"
HERE=$(CDPATH='' cd -- "$(dirname -- "$0")" && pwd)
D=$JOURNEY_STEP_DIR/jthin-consent
[ ! -e "$D" ] || { echo "refusing to reuse $D" >&2; exit 2; }
mkdir -p -m 700 "$D/alice/requests" "$D/req" "$D/log"
ROWS=$D/rows.tsv
printf 'step\texpect\trc\tresult\n' >"$ROWS"
N=0
SHELL_BIN=${SHELL_BIN:-$MINI}
REAL=${THIN_CONSENT_PROVIDER:-$(dirname "$HOST")/minidregg-client-consent}
PROXY=$HERE/lib/thin-proxy.py
[ -x "$REAL" ] || { echo "no consent provider at $REAL" >&2; exit 2; }
finish() { local rc=$?; printf '%s\n' "$ROWS"; [ "$rc" = 0 ] || echo "JTHIN: stopped at the first failed row; see $D/log" >&2; }
trap finish EXIT
row() { printf '%s\t%s\t%s\t%s\n' "$1" "$2" "$3" "$4" >>"$ROWS"; }
fail() { row "$1" "$2" "$3" FAIL; echo "$1: $5" >&2; exit 1; }

# say WHO LINE [MODE]: one shell line; with MODE, under thin consent through the proxy.
say() {
  local who=$1 line=$2 mode=${3:-}
  N=$((N+1)); OUT=$D/log/$N.out; ERR=$D/log/$N.err
  printf '%s\t%s\n' "${mode:-full}" "$line" >"$D/log/$N.line"
  if [ -n "$mode" ]; then
    # MINI_CONSENT_RESIDENT=0: the client otherwise keeps ONE resident consent provider across shell lines
    # (client_consent.rs), and the proxy reads THIN_PROXY_MODE once at its start; the first line's mode
    # (pass) would then serve every later line and no capture or plant would ever happen.
    if env MINI_THIN_CONSENT=1 MINI_CONSENT_RESIDENT=0 MINI_LOCAL_HOST="$HOST" MINI_CONSENT_HOST="$PROXY" MINI_CONSENT_CONFIG="$CONFIG" \
        THIN_PROXY_REAL="$REAL" THIN_PROXY_MODE="$mode" THIN_PROXY_LOG="$D/proxy.log" \
        THIN_PROXY_OTHER_INTENT="${OTHER_INTENT:-}" THIN_PROXY_SAVE_VIEW="${SAVE_VIEW:-}" \
        "$SHELL_BIN" shell --socket "$SOCKET" --host "$HOST" --config "$CONFIG" \
        --workspace "$SPONSOR_WS" --home "$D/$who" --line "$line" >"$OUT" 2>"$ERR"; then RC=0; else RC=$?; fi
  else
    if "$SHELL_BIN" shell --socket "$SOCKET" --host "$HOST" --config "$CONFIG" \
        --workspace "$SPONSOR_WS" --home "$D/$who" --line "$line" >"$OUT" 2>"$ERR"; then RC=0; else RC=$?; fi
  fi
}
ok() { local step=$1; shift; say "$@"; [ "$RC" = 0 ] || fail "$step" 0 "$RC" x "$(tail -3 "$ERR")"; row "$step" 0 0 PASS; }
check() { local step=$1; shift; if "$@"; then row "$step" true 0 PASS; else fail "$step" true 1 x "check failed: $*"; fi; }
attempt_of() { sed -n 's/^workspace attempt: //p' "$1" | tail -1; }
proposal_root() { jq -r '.purpose.draft.command.targets[0].expectedTargetRoot' "$SPONSOR_WS/proposals/$1/intent.json"; }
shown_root() { jq -r '.[0].postRoot' "$1/thin-display.json"; }
proxy_saw() { grep -q "$1" "$D/proxy.log"; }

cat >"$D/alice/requests/poll.json" <<'JSON'
{"descriptor":{"revision":"1","fields":[
 {"id":"1","name":"question","meaning":"the poll question","codec":"bytes","discipline":"rom"},
 {"id":"2","name":"open","meaning":"whether the poll accepts votes","codec":"nat","discipline":"ram"},
 {"id":"3","name":"votes","meaning":"one immutable vote keyed by member subject","codec":"nat","discipline":"append"}]},
 "defaults":[{"field":"1","key":"0","value":"4c756e63683f"},{"field":"2","key":"0","value":"1"}]}
JSON

ok kind-create alice 'kind create tc-poll @poll.json open'
ok instance-create alice 'create tc-one --from tc-poll open'

# ---- T1: honest thin consent; what it shows is what commits
ok t1-propose-show alice 'instance show tc-one'
ok t1-propose alice 'instance set t1 tc-one open 0 0'
# The view the Host serves for this consent is saved by the proxy: the client reads it for the
# consent alone and keeps no copy (a signed read keeps one journal line, not an attempt tree).
SAVE_VIEW=$D/view-pre-t1.bin say alice 'submit t1' pass
[ "$RC" = 0 ] || fail t1-submit 0 "$RC" x "$(tail -3 "$ERR")"
row t1-submit 0 0 PASS
T1=$(attempt_of "$ERR")
check t1-thin-frames proxy_saw 'frame 232'
check t1-shown test -s "$T1/thin-display.json"
check t1-view-served test -s "$D/view-pre-t1.bin"
ok t1b-propose-show alice 'instance show tc-one'
ok t1b-propose alice 'instance set t1b tc-one open 0 1'
check t1-shown-is-committed test "$(shown_root "$T1")" = "$(proposal_root t1b)"

# ---- FB: the Host's plan carries another command's slots
ok t3b-propose-show alice 'instance show tc-one'
ok t3b-propose alice "instance set t3b tc-one votes $SPONSOR_SUBJECT 1"
say alice 'submit t3b' "capture=$D/planB"
[ "$RC" != 0 ] || fail fb-capture refused 0 x "the capturing proxy let t3b through"
check fb-captured test -s "$D/planB.plan"
ok fb1-propose-show alice 'instance show tc-one'
ok fb1-propose alice 'instance set fb1 tc-one open 0 1'
OTHER_INTENT=$D/planB.intent say alice 'submit fb1' "slots-from=$D/planB.plan"
check fb-planted proxy_saw 'slots-from: spliced'
grep -q 'headerMismatch' "$ERR" || fail fb-refused headerMismatch "$RC" x "$(tail -3 "$ERR")"
FB=$(attempt_of "$ERR")
check fb-nothing-signed test ! -e "$FB/transaction-signatures.json"
row fb-refused headerMismatch "$RC" PASS

# ---- FA: the Host serves a view of another state (the pre-T1 view)
ok fa1-propose-show alice 'instance show tc-one'
ok fa1-propose alice 'instance set fa1 tc-one open 0 1'
say alice 'submit fa1' "view=$D/view-pre-t1.bin"
check fa-planted proxy_saw 'view: replaced'
grep -q 'servedRootMismatch' "$ERR" || fail fa-refused servedRootMismatch "$RC" x "$(tail -3 "$ERR")"
FA=$(attempt_of "$ERR")
check fa-nothing-signed test ! -e "$FA/transaction-signatures.json"
row fa-refused servedRootMismatch "$RC" PASS

# ---- T2: honest again
ok t2-propose-show alice 'instance show tc-one'
ok t2-propose alice 'instance set t2 tc-one open 0 1'
say alice 'submit t2' pass
[ "$RC" = 0 ] || fail t2-submit 0 "$RC" x "$(tail -3 "$ERR")"
row t2-submit 0 0 PASS
T2=$(attempt_of "$ERR")
ok t2c-propose-show alice 'instance show tc-one'
ok t2c-propose alice 'instance set t2c tc-one open 0 0'
check t2-shown-is-committed test "$(shown_root "$T2")" = "$(proposal_root t2c)"

# ---- S1: a signed call whose target moved, signer observes the target
ok s1-propose-show alice 'instance show tc-one'
ok s1-propose alice 'instance set s1 tc-one open 0 1'
S1=$D/s1-attempt
env MINI_THIN_CONSENT=1 MINI_LOCAL_HOST="$HOST" MINI_CONSENT_HOST="$PROXY" MINI_CONSENT_CONFIG="$CONFIG" \
  THIN_PROXY_REAL="$REAL" THIN_PROXY_MODE=pass THIN_PROXY_LOG="$D/proxy.log" \
  "$MINI" workspace --action submit --dir "$SPONSOR_WS" --intent "$SPONSOR_WS/proposals/s1/intent.json" \
  --attempt "$SPONSOR_WS/attempts/s1-sealed" --prepare-only true >"$D/log/s1-prepare.out" 2>"$D/log/s1-prepare.err" \
  || fail s1-sealed 0 1 x "$(tail -3 "$D/log/s1-prepare.err")"
check s1-sealed test -s "$SPONSOR_WS/attempts/s1-sealed/call.bin"
say alice 'submit t2c' pass
[ "$RC" = 0 ] || fail s1-move 0 "$RC" x "$(tail -3 "$ERR")"
row s1-move 0 0 PASS
rc=0; "$MINI" retry --attempt "$SPONSOR_WS/attempts/s1-sealed" --mode submit >"$D/log/s1-retry.out" 2>"$D/log/s1-retry.err" || rc=$?
grep -q 'stale-target' "$D/log/s1-retry.err" || fail s1-named stale-target "$rc" x "$(tail -3 "$D/log/s1-retry.err")"
grep -q "moved since the plan was signed" "$D/log/s1-retry.err" || fail s1-named stale-target "$rc" x "$(tail -3 "$D/log/s1-retry.err")"
row s1-named stale-target "$rc" PASS

# ---- N1 and S2: the newcomer, which may mutate but not observe tc-blind
printf '%s\n' '{"type":"all","predicates":[]}' >"$D/req/permit-all.json"
"$MINI" workspace --action create --dir "$SPONSOR_WS" --name tc-blind --storage declared \
  --predicate "$D/req/permit-all.json" --fields 401-405 >"$D/log/blind-create.out" 2>"$D/log/blind-create.err" \
  || fail blind-create 0 1 x "$(tail -3 "$D/log/blind-create.err")"
jq -n --arg r "$NEWCOMER_SUBJECT" '{type:"minidregg-workspace-proposal-v1",action:"delegate",name:"tc-blind",
  recipient:$r,verbs:["observe","mutate"],fields:["401"],perRequestBytes:"50000"}' >"$D/req/blind-grant.json"
"$MINI" workspace --action propose --dir "$SPONSOR_WS" --request "$D/req/blind-grant.json" --proposal-id tc-blind-grant \
  >"$D/log/blind-grant.out" 2>"$D/log/blind-grant.err" || fail blind-grant 0 1 x "$(tail -3 "$D/log/blind-grant.err")"
"$MINI" workspace --action submit --dir "$SPONSOR_WS" --intent "$SPONSOR_WS/proposals/tc-blind-grant/intent.json" \
  --attempt "$SPONSOR_WS/attempts/tc-blind-grant" >>"$D/log/blind-grant.out" 2>>"$D/log/blind-grant.err" \
  || fail blind-grant 0 1 x "$(tail -3 "$D/log/blind-grant.err")"
"$MINI" workspace --action publish-delegation --dir "$SPONSOR_WS" --proposal-id tc-blind-grant \
  --attempt "$SPONSOR_WS/attempts/tc-blind-grant" >>"$D/log/blind-grant.out" 2>>"$D/log/blind-grant.err" \
  || fail blind-grant 0 1 x "$(tail -3 "$D/log/blind-grant.err")"
"$MINI" workspace --action import --dir "$NEWCOMER_WS" --name tc-blind \
  --from-ref "$SPONSOR_WS/proposals/tc-blind-grant/recipient-reference.json" >"$D/log/blind-import.out" 2>"$D/log/blind-import.err" \
  || fail blind-import 0 1 x "$(tail -3 "$D/log/blind-import.err")"
row blind-setup 0 0 PASS
printf '{"type":"minidregg-workspace-proposal-v1","action":"invoke","targets":[{"name":"tc-blind","payload":{"type":"scalar","actions":[{"type":"create","key":{"type":"object","field":"401"},"value":"1"}]}}]}\n' >"$D/req/blind-write.json"
"$MINI" workspace --action propose --dir "$NEWCOMER_WS" --request "$D/req/blind-write.json" --proposal-id n1 \
  >"$D/log/n1-propose.out" 2>"$D/log/n1-propose.err" || fail n1-propose 0 1 x "$(tail -3 "$D/log/n1-propose.err")"
# N1: its observe grant is narrowed to field 401, so the view the Host serves
# opens field 401 and seals every other entry (the blinding included). Thin
# consent checks it by the opening, shows the post at field 401 with no post
# root, and the turn commits.
: >"$D/proxy-n1.log"
rc=0; env MINI_THIN_CONSENT=1 MINI_LOCAL_HOST="$HOST" MINI_CONSENT_HOST="$PROXY" MINI_CONSENT_CONFIG="$CONFIG" \
  THIN_PROXY_REAL="$REAL" THIN_PROXY_MODE=pass THIN_PROXY_LOG="$D/proxy-n1.log" \
  "$MINI" workspace --action submit --dir "$NEWCOMER_WS" --intent "$NEWCOMER_WS/proposals/n1/intent.json" \
  --attempt "$NEWCOMER_WS/attempts/n1" >"$D/log/n1-submit.out" 2>"$D/log/n1-submit.err" || rc=$?
[ "$rc" = 0 ] || fail n1-narrowed 0 "$rc" x "$(tail -3 "$D/log/n1-submit.err")"
check n1-thin-shown grep -q '^thin consent shows: ' "$D/log/n1-submit.err"
check n1-shown-opened jq -e '.[0].postBytes != null and (.[0] | has("postRoot") | not)' \
  "$NEWCOMER_WS/attempts/n1/thin-display.json"
check n1-signed test -s "$NEWCOMER_WS/attempts/n1/transaction-signatures.json"
row n1-narrowed 0 "$rc" PASS
# N2: a target it holds no grant on at all (tc-one, under its tc-blind
# capability): the Host refuses the signed read, serves no bytes, and nothing
# is signed.
jq --arg t "$(jq -r .target "$SPONSOR_WS/refs/tc-one.json")" '.purpose.draft.command.targets[0].target=$t' \
  "$NEWCOMER_WS/proposals/n1/intent.json" >"$D/req/n2-intent.json"
: >"$D/proxy-n2.log"
rc=0; env MINI_THIN_CONSENT=1 MINI_LOCAL_HOST="$HOST" MINI_CONSENT_HOST="$PROXY" MINI_CONSENT_CONFIG="$CONFIG" \
  THIN_PROXY_REAL="$REAL" THIN_PROXY_MODE=pass THIN_PROXY_LOG="$D/proxy-n2.log" \
  THIN_PROXY_SAVE_VIEW="$D/view-n2.bin" \
  "$MINI" workspace --action submit --dir "$NEWCOMER_WS" --intent "$D/req/n2-intent.json" \
  --attempt "$NEWCOMER_WS/attempts/n2" >"$D/log/n2-submit.out" 2>"$D/log/n2-submit.err" || rc=$?
[ "$rc" != 0 ] || fail n2-refused refused 0 x "a member without a grant signed and submitted"
grep -q '^refused: ' "$D/log/n2-submit.err" || fail n2-refused "host refusal" "$rc" x "$(tail -3 "$D/log/n2-submit.err")"
check n2-no-plan-consent sh -c "! grep -q 'frame 232' '$D/proxy-n2.log'"
check n2-no-bytes-served test ! -e "$D/view-n2.bin"
check n2-nothing-signed test ! -e "$NEWCOMER_WS/attempts/n2/transaction-signatures.json"
row n2-refused "$(grep -m1 '^refused: ' "$D/log/n2-submit.err" | cut -c1-60)" "$rc" PASS
# S2: the newcomer signs its own write over N1's post with full consent (it
# replays), the sponsor moves the cell, the call is refused uniformly.
printf '{"type":"minidregg-workspace-proposal-v1","action":"invoke","targets":[{"name":"tc-blind","payload":{"type":"scalar","actions":[{"type":"write","key":{"type":"object","field":"401"},"expected":"1","value":"2"}]}}]}\n' >"$D/req/s2-write.json"
"$MINI" workspace --action propose --dir "$NEWCOMER_WS" --request "$D/req/s2-write.json" --proposal-id s2 \
  >"$D/log/s2-propose.out" 2>"$D/log/s2-propose.err" || fail s2-propose 0 1 x "$(tail -3 "$D/log/s2-propose.err")"
"$MINI" workspace --action submit --dir "$NEWCOMER_WS" --intent "$NEWCOMER_WS/proposals/s2/intent.json" \
  --attempt "$NEWCOMER_WS/attempts/s2-sealed" --prepare-only true >"$D/log/s2-prepare.out" 2>"$D/log/s2-prepare.err" \
  || fail s2-sealed 0 1 x "$(tail -3 "$D/log/s2-prepare.err")"
printf '{"type":"minidregg-workspace-proposal-v1","action":"invoke","targets":[{"name":"tc-blind","payload":{"type":"scalar","actions":[{"type":"create","key":{"type":"object","field":"402"},"value":"1"}]}}]}\n' >"$D/req/blind-move.json"
"$MINI" workspace --action propose --dir "$SPONSOR_WS" --request "$D/req/blind-move.json" --proposal-id s2-move \
  >"$D/log/s2-move.out" 2>"$D/log/s2-move.err" || fail s2-move 0 1 x "$(tail -3 "$D/log/s2-move.err")"
"$MINI" workspace --action submit --dir "$SPONSOR_WS" --intent "$SPONSOR_WS/proposals/s2-move/intent.json" \
  --attempt "$SPONSOR_WS/attempts/s2-move" >>"$D/log/s2-move.out" 2>>"$D/log/s2-move.err" \
  || fail s2-move 0 1 x "$(tail -3 "$D/log/s2-move.err")"
rc=0; "$MINI" retry --attempt "$NEWCOMER_WS/attempts/s2-sealed" --mode submit >"$D/log/s2-retry.out" 2>"$D/log/s2-retry.err" || rc=$?
grep -q 'undisclosed' "$D/log/s2-retry.err" || fail s2-uniform undisclosed "$rc" x "$(tail -3 "$D/log/s2-retry.err")"
if grep -q 'stale-target' "$D/log/s2-retry.err"; then fail s2-uniform undisclosed "$rc" x "named a target the signer cannot observe"; fi
row s2-uniform undisclosed "$rc" PASS

# ---- D1: honest thin delegation. No view is served; what is shown is the signed
# parent id and child; the child's lineage is the kernel's copy of that parent.
ok d1-propose alice "delegate d1 tc-one $NEWCOMER_SUBJECT observe 50000"
say alice 'submit d1' pass
[ "$RC" = 0 ] || fail d1-submit 0 "$RC" x "$(tail -3 "$ERR")"
row d1-submit 0 0 PASS
D1=$(attempt_of "$ERR")
check d1-thin-frames proxy_saw 'frame 232'
check d1-shown-delegation jq -e '.[0].delegate == true and (.[0].childBytes | length > 0)' "$D1/thin-display.json"
check d1-shown-parent-is-signed test "$(jq -r '.[0].parent' "$D1/thin-display.json")" = "$(jq -r .operationCapability "$SPONSOR_WS/refs/tc-one.json")"

# ---- DF (planted fault): the Host swaps the parent. It proposes, for a
# delegation over tc-one, the signing slot of a delegation over tc-blind (another
# parent capability of the same signer): refused headerMismatch before signing.
ok dfo-propose alice "delegate dfo tc-blind $NEWCOMER_SUBJECT observe 50000"
say alice 'submit dfo' "capture=$D/planD"
[ "$RC" != 0 ] || fail df-capture refused 0 x "the capturing proxy let dfo through"
check df-captured test -s "$D/planD.plan"
ok df-propose alice "delegate df tc-one $NEWCOMER_SUBJECT observe 50000"
OTHER_INTENT=$D/planD.intent say alice 'submit df' "slots-from=$D/planD.plan"
check df-planted proxy_saw "slots-from: spliced the slots of $D/planD.plan"
grep -q 'headerMismatch' "$ERR" || fail df-refused headerMismatch "$RC" x "$(tail -3 "$ERR")"
DF=$(attempt_of "$ERR")
check df-nothing-signed test ! -e "$DF/transaction-signatures.json"
row df-refused headerMismatch "$RC" PASS

# ---- KR: a whole kind definition read (`kindRead`, registered effect code 7) beside a write.
# The read pins the kind's root, so thin consent checks its served opening like a write's; it is
# shown as a read with no effect lines (only a read that pins no root is shown without a view).
# KR1: admitted and signed. KR2: the Host serves another cell's view for the kind read alone and
# the honest view for the write: refused before signing.
P=$D/req/permit-all.json
printf '%s\n' '{"type":"all","predicates":[]}' >"$P"
"$MINI" workspace --action create --dir "$SPONSOR_WS" --name tc-note --storage declared --predicate "$P" --fields 2 \
  >"$D/log/kr-create.out" 2>"$D/log/kr-create.err" || fail kr-create 0 1 x "$(tail -3 "$D/log/kr-create.err")"
row kr-create 0 0 PASS
kr() { # ID ACTION-JSON MODE: a scalar write of tc-note beside a kindRead of tc-poll, submitted under thin consent
  local id=$1 action=$2 mode=$3
  jq -nc --argjson a "$action" '{type:"minidregg-workspace-proposal-v1",action:"invoke",targets:[
    {name:"tc-note",payload:{type:"scalar",actions:[$a]}},{name:"tc-poll",payload:{type:"kindRead"}}]}' >"$D/req/$id.json"
  "$MINI" workspace --action propose --dir "$SPONSOR_WS" --request "$D/req/$id.json" --proposal-id "$id" \
    >"$D/log/$id-propose.out" 2>"$D/log/$id-propose.err" || fail "$id-propose" 0 1 x "$(tail -3 "$D/log/$id-propose.err")"
  : >"$D/proxy-$id.log"
  # MINI_CONSENT_RESIDENT=0: this line's own provider, so this line's proxy mode and log apply (`say`).
  RC=0; env MINI_THIN_CONSENT=1 MINI_CONSENT_RESIDENT=0 MINI_LOCAL_HOST="$HOST" MINI_CONSENT_HOST="$PROXY" MINI_CONSENT_CONFIG="$CONFIG" \
    THIN_PROXY_REAL="$REAL" THIN_PROXY_MODE="$mode" THIN_PROXY_LOG="$D/proxy-$id.log" \
    "$MINI" workspace --action submit --dir "$SPONSOR_WS" --intent "$SPONSOR_WS/proposals/$id/intent.json" \
    --attempt "$SPONSOR_WS/attempts/$id" >"$D/log/$id-submit.out" 2>"$D/log/$id-submit.err" || RC=$?
}
kr tc-kr1 '{"type":"create","key":{"type":"object","field":"2"},"value":"1"}' pass
[ "$RC" = 0 ] || fail kr-admitted 0 "$RC" x "$(tail -3 "$D/log/tc-kr1-submit.err")"
check kr-thin-frames grep -q 'frame 232' "$D/proxy-tc-kr1.log"
check kr-shown-as-read jq -e 'length == 2 and .[0].postBytes != null and .[1].read == true and (.[1] | has("effect") | not)' \
  "$SPONSOR_WS/attempts/tc-kr1/thin-display.json"
check kr-signed test -s "$SPONSOR_WS/attempts/tc-kr1/transaction-signatures.json"
row kr-admitted 0 0 PASS
kr tc-kr2 '{"type":"write","key":{"type":"object","field":"2"},"expected":"1","value":"2"}' "view-last=$D/view-pre-t1.bin"
check kr-lie-planted grep -q 'view-last: replaced' "$D/proxy-tc-kr2.log"
[ "$RC" != 0 ] || fail kr-lie-refused refused 0 x "thin consent signed a kind read over a view of another cell"
check kr-lie-nothing-signed test ! -e "$SPONSOR_WS/attempts/tc-kr2/transaction-signatures.json"
row kr-lie-refused "$(grep -m1 -o 'thin consent refused: [A-Za-z.]* *[A-Za-z]*' "$D/log/tc-kr2-submit.err" | cut -c1-70)" "$RC" PASS

# ---- SR: refused by the Host's semantics at prepare; nothing shown, nothing signed, nothing commits.
# tc-note declared field 2 alone at birth. Creating field 3 is a patch that applies to the served
# store (the address is fresh), so the member patch alone would show a post. The Host's semantics
# refuses it (K-FIELD-CLOSURE) when it prepares the plan, before any plan is proposed for consent.
sr_request() { # ID FIELD: propose a create of FIELD on tc-note
  jq -nc --arg f "$2" '{type:"minidregg-workspace-proposal-v1",action:"invoke",targets:[
    {name:"tc-note",payload:{type:"scalar",actions:[{type:"create",key:{type:"object",field:$f},value:"1"}]}}]}' >"$D/req/$1.json"
  "$MINI" workspace --action propose --dir "$SPONSOR_WS" --request "$D/req/$1.json" --proposal-id "$1" \
    >"$D/log/$1-propose.out" 2>"$D/log/$1-propose.err" || fail "$1-propose" 0 1 x "$(tail -3 "$D/log/$1-propose.err")"
}
sr_request tc-sr 3
: >"$D/proxy-tc-sr.log"
RC=0; env MINI_THIN_CONSENT=1 MINI_CONSENT_RESIDENT=0 MINI_LOCAL_HOST="$HOST" MINI_CONSENT_HOST="$PROXY" MINI_CONSENT_CONFIG="$CONFIG" \
  THIN_PROXY_REAL="$REAL" THIN_PROXY_MODE=pass THIN_PROXY_LOG="$D/proxy-tc-sr.log" \
  "$MINI" workspace --action submit --dir "$SPONSOR_WS" --intent "$SPONSOR_WS/proposals/tc-sr/intent.json" \
  --attempt "$SPONSOR_WS/attempts/tc-sr" >"$D/log/tc-sr-submit.out" 2>"$D/log/tc-sr-submit.err" || RC=$?
[ "$RC" != 0 ] || fail sr-refused undeclared-field 0 x "the Host admitted a write of a field the cell did not declare"
grep -q 'undeclared-field 3 (phase prepare)' "$D/log/tc-sr-submit.err" || fail sr-refused undeclared-field "$RC" x "$(tail -3 "$D/log/tc-sr-submit.err")"
row sr-refused-at-prepare undeclared-field "$RC" PASS
check sr-no-plan-consent sh -c "! grep -q 'frame 232' '$D/proxy-tc-sr.log'"
check sr-nothing-shown test ! -e "$SPONSOR_WS/attempts/tc-sr/thin-display.json"
check sr-nothing-signed test ! -e "$SPONSOR_WS/attempts/tc-sr/transaction-signatures.json"
# Nothing committed: the next proposal, authored from a fresh signed read, names the root tc-sr named.
sr_request tc-sr2 3
check sr-nothing-committed test "$(proposal_root tc-sr)" = "$(proposal_root tc-sr2)"

if [ -n "${THIN_MUTANT_PROVIDER:-}" ]; then
  check m-is-mutant sh -c "[ \"\$(sha256sum < '$THIN_MUTANT_PROVIDER')\" != \"\$(sha256sum < '$REAL')\" ]"
  ok m-propose-show alice 'instance show tc-one'
  ok m-propose alice "instance set m1 tc-one votes $SPONSOR_SUBJECT 1"
  REAL_SAVED=$REAL; REAL=$THIN_MUTANT_PROVIDER
  say alice 'submit m1' "view=$D/view-pre-t1.bin"
  REAL=$REAL_SAVED
  check m-planted proxy_saw 'view: replaced'
  [ "$RC" = 0 ] || fail m-mutant-signed 0 "$RC" x "the mutant refused: $(tail -3 "$ERR")"
  row m-mutant-signed 0 0 PASS
  M=$(attempt_of "$ERR")
  ok m-next-show alice 'instance show tc-one'
  ok m-next alice 'instance set m2 tc-one open 0 1'
  check m-shown-differs-from-committed test "$(shown_root "$M")" != "$(proposal_root m2)"
  printf 'JTHIN-MUTANT: the mutant showed %s, the turn committed %s\n' "$(shown_root "$M")" "$(proposal_root m2)" >&2
fi
printf 'JTHIN: all thin-consent rows passed\n' >&2
