#!/usr/bin/env bash
# journey.d/jfields.sh — K-FIELDS (DATAMODEL B3, PLACE item 10): a scope names
# the fields of a cell it covers and bounds each field's change per write.
# Runs on the journey's fresh Store after J5 (A = sponsor, B = newcomer).
#
# Treasury (MUD J-MUD-5's rows; field 7 = `spent`): A delegates observe+mutate
# with maxDelta {7: 50} to B.
#   t-moves-30        B moves spent 0 -> 30                          -> installed
#   t-moves-60        B moves spent 30 -> 90                         -> refused (maxDeltaExceeded)
#   t-moves-30-again  B moves spent 30 -> 60 (the bound is per write) -> installed
# Ledger (declared, fields 3 and 4; a declared cell is born with field 1):
# A delegates observe+mutate+delegate with fields {3} to B.
#   r-writes-1        B writes field 3                               -> installed
#   r-writes-2        B writes field 4                               -> refused (fieldNotNamed)
#   r-reads           B reads: field 3 present, field 4 absent        -> read
#   a-reads           A reads: both fields present                    -> read
#   roots-agree       B's narrowed view and A's carry the same cell root
#   r-redelegates-12  B delegates fields {3,4} onward                 -> refused (does not narrow)
#   r-redelegates-1   B delegates fields {3} onward                   -> installed
# A submitted write's refusal reaches the submitter as the uniform
# `admission: request refused` (NativeHost.public_refusal_uniform); the named
# reason is read from the operator's log (the service's stderr), and rows with
# a NAME check it there.
# Paper (content; PLACE J12d): A delegates fields {annotations} to B.
#   rv-annotates      B links (an annotation)                         -> installed
#   rv-edits-body     B creates an atom (body)                        -> refused (fieldNotNamed)
#   rv-reads          B reads: links present, A's atom absent         -> read
#   a-reads-paper     A reads: the atom and the link                  -> read
# Exported by the journey: MINI HOST CONFIG SOCKET JOURNEY_WORLD SPONSOR_WS NEWCOMER_WS SPONSOR_SUBJECT
# NEWCOMER_SUBJECT JOURNEY_STEP_DIR. Exit 0 = every row as expected. Last
# stdout line = the rows file.
set -uo pipefail
D=$JOURNEY_STEP_DIR
mkdir -p "$D/req"
rows=$D/field-rows.tsv
: >"$rows"
bad=0
REFUSAL_TAG=44524547472f4e41544956452d484f53542f4f5554434f4d45

run() { local name=$1; shift; "$@" >"$D/$name.out" 2>"$D/$name.err"; echo $? >"$D/$name.rc"; }
host_refused() { [ "$(cat "$D/$1.rc")" != 0 ] && grep -q "encoded refusal: $REFUSAL_TAG" "$D/$1.err"; }
submit_refused() { jq -e '.type == "refused"' "$1" >/dev/null 2>&1; }
OPLOG=$JOURNEY_WORLD/public/serve.log
oplog_lines() { local n; n=$(grep -c "submission refused (operator log)" "$OPLOG" 2>/dev/null); echo "${n:-0}"; }
# The operator-log line a submission added, if any (since line count $1).
oplog_since() { grep "submission refused (operator log)" "$OPLOG" 2>/dev/null | tail -n +$(($1 + 1)) | tail -1 | cut -c1-220; }
refusal_text() {
  grep -o 'encoded refusal: [0-9a-f]*' "$D/$1.err" | tail -1 | cut -d' ' -f3 | xxd -r -p 2>/dev/null \
    | tr -c '[:print:]' ' ' | tr -s ' ' | cut -c1-200
}
installed() { jq -e '.type == "confirmed" and .confirmation == "installed"' "$1" >/dev/null 2>&1; }
must() { [ "$(cat "$D/$1.rc")" = 0 ] || { echo "setup $1 failed: $(tail -1 "$D/$1.err")" >&2; exit 1; }; }
record() { # NAME EXPECT GOT DETAIL [NEEDLE]
  printf '%s\texpect=%s\tgot=%s\t%s\n' "$1" "$2" "$3" "$4" >>"$rows"
  [ "$2" = "$3" ] || bad=$((bad + 1))
  if [ -n "${5:-}" ] && [ "$3" = refused ]; then
    case "$4" in *"$5"*) ;; *) echo "$1 refused, but not by $5: $4" >&2; bad=$((bad + 1));; esac
  fi
}
# invoke WS PROPOSAL REQUEST-FILE: propose + submit; prints the result
invoke() {
  local ws=$1 id=$2 req=$3
  run "$id-propose" "$MINI" workspace --action propose --dir "$ws" --request "$req" --proposal-id "$id"
  if [ "$(cat "$D/$id-propose.rc")" != 0 ]; then echo "propose-error"; return; fi
  local before; before=$(oplog_lines)
  run "$id" "$MINI" workspace --action submit --dir "$ws" --intent "$ws/proposals/$id/intent.json" \
    --attempt "$ws/attempts/$id"
  oplog_since "$before" >"$D/$id.oplog"
  if installed "$ws/attempts/$id/outcome.json"; then echo installed
  elif host_refused "$id" || submit_refused "$ws/attempts/$id/outcome.json"; then echo refused
  else echo client-error; fi
}
row_invoke() { # NAME EXPECT WS REQUEST [NEEDLE]
  local got detail
  got=$(invoke "$3" "$1" "$4")
  if [ "$got" = refused ]; then detail="$(refusal_text "$1") | $(cat "$D/$1.oplog")"
  else detail=$(tail -1 "$D/$1.err" 2>/dev/null | cut -c1-160); fi
  record "$1" "$2" "$got" "$detail" "${5:-}"
}
scalar() { # NAME TYPE FIELD VALUE [EXPECTED]
  if [ -n "${5:-}" ]; then
    jq -nc --arg n "$1" --arg t "$2" --arg f "$3" --arg v "$4" --arg e "$5" '{type:"minidregg-workspace-proposal-v1",
      action:"invoke",targets:[{name:$n,payload:{type:"scalar",actions:[{type:$t,key:{type:"object",field:$f},value:$v,expected:$e}]}}]}'
  else
    jq -nc --arg n "$1" --arg t "$2" --arg f "$3" --arg v "$4" '{type:"minidregg-workspace-proposal-v1",
      action:"invoke",targets:[{name:$n,payload:{type:"scalar",actions:[{type:$t,key:{type:"object",field:$f},value:$v}]}}]}'
  fi
}
content() { # NAME ACTION-JSON
  jq -nc --arg n "$1" --argjson a "$2" '{type:"minidregg-workspace-proposal-v1",action:"invoke",
    targets:[{name:$n,payload:{type:"content",actions:[$a]}}]}'
}
# delegate WS ID NAME RECIPIENT VERBS-JSON EXTRA-JSON: propose+submit+publish; prints the result
delegate() {
  local ws=$1 id=$2
  jq -n --arg n "$3" --arg r "$4" --argjson v "$5" --argjson x "$6" \
    '{type:"minidregg-workspace-proposal-v1",action:"delegate",name:$n,recipient:$r,verbs:$v,maxCost:"50000"} + $x' \
    >"$D/req/$id.json"
  run "$id-propose" "$MINI" workspace --action propose --dir "$ws" --request "$D/req/$id.json" --proposal-id "$id"
  if [ "$(cat "$D/$id-propose.rc")" != 0 ]; then echo "propose-error"; return; fi
  local before; before=$(oplog_lines)
  run "$id" "$MINI" workspace --action submit --dir "$ws" --intent "$ws/proposals/$id/intent.json" \
    --attempt "$ws/attempts/$id"
  oplog_since "$before" >"$D/$id.oplog"
  if installed "$ws/attempts/$id/outcome.json"; then
    run "$id-publish" "$MINI" workspace --action publish-delegation --dir "$ws" --proposal-id "$id" \
      --attempt "$ws/attempts/$id"
    echo installed
  elif host_refused "$id" || submit_refused "$ws/attempts/$id/outcome.json"; then echo refused
  else echo client-error; fi
}
field_value() { jq -r --arg f "$2" '[.cell.entries[]? | select(.key.field == $f) | .value][0] // "absent"' "$1"; }
P=$D/req/permit-all.json
printf '%s\n' '{"type":"all","predicates":[]}' >"$P"

# ---- treasury: maxDelta {7: 50}
run create-treasury "$MINI" workspace --action create --dir "$SPONSOR_WS" --name treasury --storage declared --predicate "$P"
must create-treasury
scalar treasury create 7 0 >"$D/req/t-init.json"
[ "$(invoke "$SPONSOR_WS" t-init "$D/req/t-init.json")" = installed ] || { echo "treasury init failed: $(tail -1 "$D/t-init.err")" >&2; exit 1; }
[ "$(delegate "$SPONSOR_WS" give-treasurer treasury "$NEWCOMER_SUBJECT" '["observe","mutate"]' \
    '{"maxDelta":[{"field":"7","max":"50"}]}')" = installed ] \
  || { echo "treasurer delegation failed: $(tail -1 "$D/give-treasurer.err")" >&2; exit 1; }
jq -e '.purpose.draft.command.child.maxDelta == [{"field":"7","max":"50"}]' \
  "$SPONSOR_WS/proposals/give-treasurer/intent.json" >/dev/null || { echo "treasurer child lacks maxDelta" >&2; exit 1; }
run t-import "$MINI" workspace --action import --dir "$NEWCOMER_WS" --name treasury \
  --from-ref "$SPONSOR_WS/proposals/give-treasurer/recipient-reference.json"; must t-import
scalar treasury write 7 30 0 >"$D/req/t-30.json";  row_invoke t-moves-30 installed "$NEWCOMER_WS" "$D/req/t-30.json"
scalar treasury write 7 90 30 >"$D/req/t-60.json"; row_invoke t-moves-60 refused "$NEWCOMER_WS" "$D/req/t-60.json" maxDeltaExceeded
scalar treasury write 7 60 30 >"$D/req/t-30b.json"; row_invoke t-moves-30-again installed "$NEWCOMER_WS" "$D/req/t-30b.json"

# ---- ledger: fields {3}
run create-ledger "$MINI" workspace --action create --dir "$SPONSOR_WS" --name ledger --storage declared --predicate "$P"
must create-ledger
scalar ledger create 3 10 >"$D/req/l-1.json"; [ "$(invoke "$SPONSOR_WS" l-init-1 "$D/req/l-1.json")" = installed ] || { echo "ledger init 1 failed" >&2; exit 1; }
scalar ledger create 4 20 >"$D/req/l-2.json"; [ "$(invoke "$SPONSOR_WS" l-init-2 "$D/req/l-2.json")" = installed ] || { echo "ledger init 2 failed" >&2; exit 1; }
[ "$(delegate "$SPONSOR_WS" give-reader ledger "$NEWCOMER_SUBJECT" '["observe","mutate","delegate"]' '{"fields":["3"]}')" = installed ] \
  || { echo "ledger delegation failed: $(tail -1 "$D/give-reader.err")" >&2; exit 1; }
run r-import "$MINI" workspace --action import --dir "$NEWCOMER_WS" --name ledger \
  --from-ref "$SPONSOR_WS/proposals/give-reader/recipient-reference.json"; must r-import
scalar ledger write 3 11 10 >"$D/req/r-1.json"; row_invoke r-writes-1 installed "$NEWCOMER_WS" "$D/req/r-1.json"
scalar ledger write 4 21 20 >"$D/req/r-2.json"; row_invoke r-writes-2 refused "$NEWCOMER_WS" "$D/req/r-2.json" fieldNotNamed
run r-reads "$MINI" workspace --action read --dir "$NEWCOMER_WS" --name ledger
v1=$(field_value "$D/r-reads.out" 3); v2=$(field_value "$D/r-reads.out" 4)
[ "$(cat "$D/r-reads.rc")" = 0 ] && [ "$v1" = 11 ] && [ "$v2" = absent ] && got=read || got=wrong
record r-reads read "$got" "field3=$v1 field4=$v2"
run a-reads "$MINI" workspace --action read --dir "$SPONSOR_WS" --name ledger
a1=$(field_value "$D/a-reads.out" 3); a2=$(field_value "$D/a-reads.out" 4)
[ "$(cat "$D/a-reads.rc")" = 0 ] && [ "$a1" = 11 ] && [ "$a2" = 20 ] && got=read || got=wrong
record a-reads read "$got" "field3=$a1 field4=$a2"
r_root=$(jq -r .cell.root "$D/r-reads.out"); a_root=$(jq -r .cell.root "$D/a-reads.out")
[ "$r_root" = "$a_root" ] && got=same || got=different
record roots-agree same "$got" "the narrowed view carries the cell's own root"
# B re-delegates from a workspace of its own that holds a namespace root (the
# journey's newcomer workspace has none, so it cannot reserve a child id).
BW=$D/b-workspace
run b-init "$MINI" workspace --action init --host "$HOST" --config "$CONFIG" --socket "$SOCKET" \
  --enrollment "$JOURNEY_WORLD/attempts/newcomer/enrollment.json" --namespace-root "$D/b-namespace" --dir "$BW"
must b-init
run b-import "$MINI" workspace --action import --dir "$BW" --name ledger \
  --from-ref "$SPONSOR_WS/proposals/give-reader/recipient-reference.json"; must b-import
got=$(delegate "$BW" widen-12 ledger "$SPONSOR_SUBJECT" '["observe"]' '{"fields":["3","4"]}')
record r-redelegates-12 refused "$got" "$( [ "$got" = refused ] && echo "$(refusal_text widen-12)$(cat "$D/widen-12.oplog")" || tail -1 "$D/widen-12.err" | cut -c1-160)" "Reject.shape"
got=$(delegate "$BW" narrow-1 ledger "$SPONSOR_SUBJECT" '["observe"]' '{"fields":["3"]}')
record r-redelegates-1 installed "$got" "$(tail -1 "$D/narrow-1.err" | cut -c1-160)"

# ---- paper (content): fields {annotations}  (PLACE J12d)
run create-paper "$MINI" workspace --action create --dir "$SPONSOR_WS" --name fpaper --storage content --predicate "$P"
must create-paper
content fpaper '{"type":"createAtom","atom":"501","kind":{"type":"text"},"payload":"68656c6c6f"}' >"$D/req/p-atom.json"
[ "$(invoke "$SPONSOR_WS" p-init "$D/req/p-atom.json")" = installed ] || { echo "paper init failed: $(tail -1 "$D/p-init.err")" >&2; exit 1; }
[ "$(delegate "$SPONSOR_WS" give-reviewer fpaper "$NEWCOMER_SUBJECT" '["observe","mutate"]' '{"fields":["annotations"]}')" = installed ] \
  || { echo "reviewer delegation failed: $(tail -1 "$D/give-reviewer.err")" >&2; exit 1; }
run rv-import "$MINI" workspace --action import --dir "$NEWCOMER_WS" --name fpaper \
  --from-ref "$SPONSOR_WS/proposals/give-reviewer/recipient-reference.json"; must rv-import
content fpaper '{"type":"link","link":"601","source":null,"target":{"type":"external","scheme":"6874747073","authority":"6578616d706c65","path":"2f"},"relation":"1"}' >"$D/req/rv-link.json"
row_invoke rv-annotates installed "$NEWCOMER_WS" "$D/req/rv-link.json"
content fpaper '{"type":"createAtom","atom":"502","kind":{"type":"text"},"payload":"6564697473"}' >"$D/req/rv-atom.json"
row_invoke rv-edits-body refused "$NEWCOMER_WS" "$D/req/rv-atom.json" fieldNotNamed
run rv-reads "$MINI" workspace --action read --dir "$NEWCOMER_WS" --name fpaper
types=$(jq -r '[.cell.entries[]?.type] | sort | unique | join(",")' "$D/rv-reads.out" 2>/dev/null)
[ "$(cat "$D/rv-reads.rc")" = 0 ] && [ "$types" = link ] && got=read || got=wrong
record rv-reads read "$got" "entry types: $types"
run a-reads-paper "$MINI" workspace --action read --dir "$SPONSOR_WS" --name fpaper
atypes=$(jq -r '[.cell.entries[]?.type] | sort | unique | join(",")' "$D/a-reads-paper.out" 2>/dev/null)
[ "$(cat "$D/a-reads-paper.rc")" = 0 ] && [ "$atypes" = atom,link ] && got=read || got=wrong
record a-reads-paper read "$got" "entry types: $atypes"

cat "$rows" >&2
n=$(wc -l <"$rows")
[ "$bad" = 0 ] || { echo "$bad field rows differ from expectation (see $rows)" >&2; exit 1; }
echo "$n/$n field rows as expected: maxDelta 30 ok / 60 refused / 30 ok; fields {3} writes 3 not 4, reads 3 only, cannot widen; reviewer annotates, cannot edit" >&2
echo "$rows"
