#!/usr/bin/env bash
# journey.d/j10-index.sh — the index the world keeps (PLACE K-INDEX) and a read
# at a past height (K-HISTORY-READ), on the journey's fresh Store, after K10
# (which made the room `lab`, `note` born in it, and B's observe invite).
#
# Setup: A invites B again with observe+mutate under lab; A writes note's field
# 7 until the log is past the first checkpoint (height 64), and its last write
# is at log height HA; then B writes note's field 8, at HB (HB = HA + 1).
# Rows (heights are absolute: genesis height + log height):
#   who-a            A's `who lab`: A seen at HA, B seen at HB          -> read
#   who-b            B's `who lab` (B's own invite) equals A's            -> read
#   who-third-owner  the third key presents A's lab capability           -> refused
#   who-third-child  the third key presents B's invite                   -> refused
#   since-ha         `since lab HA`: exactly B's write (its transaction) -> read
#   since-before     `since lab HA-1`: A's last write, then B's          -> read
#   at-differ-high   note at HA-1 vs HA (above the checkpoint) differ    -> read
#   at-differ-low    note at a height below the checkpoint vs the next   -> read
#   at-current       note at the current height = the ordinary read      -> read
#   at-above         note at current+5                                   -> refused (reason named)
#   reopen-index     a cold open (checkpoint + suffix) prints the index  -> read
#   audit-index      the genesis re-admission prints the same index      -> read
# Exit 0 = every row as expected. Last stdout line = the rows file.
set -uo pipefail
D=$JOURNEY_STEP_DIR
W=$JOURNEY_WORLD
TW=$W/third-workspace
mkdir -p "$D/req" "$D/q"
rows=$D/index-rows.tsv
: >"$rows"
bad=0

run() { # NAME cmd...
  local name=$1; shift
  "$@" >"$D/$name.out" 2>"$D/$name.err"; echo $? >"$D/$name.rc"
}
ok() { [ "$(cat "$D/$1.rc")" = 0 ] || { echo "setup $1 failed: $(tail -1 "$D/$1.err")" >&2; exit 1; }; }
row() { # NAME EXPECT GOT DETAIL
  printf '%s\texpect=%s\tgot=%s\t%s\n' "$1" "$2" "$3" "$4" >>"$rows"
  [ "$2" = "$3" ] || bad=$((bad + 1))
}
ws() { jq -r ".$2" "$1/workspace.json"; }
scalar() { # NAME ACTION FIELD VALUE [EXPECTED]
  if [ -n "${5:-}" ]; then
    jq -cn --arg n "$1" --arg a "$2" --arg f "$3" --arg v "$4" --arg e "$5" '{type:"minidregg-workspace-proposal-v1",action:"invoke",
      targets:[{name:$n,payload:{type:"scalar",actions:[{type:$a,key:{type:"object",field:$f},value:$v,expected:$e}]}}]}'
  else
    jq -cn --arg n "$1" --arg a "$2" --arg f "$3" --arg v "$4" '{type:"minidregg-workspace-proposal-v1",action:"invoke",
      targets:[{name:$n,payload:{type:"scalar",actions:[{type:$a,key:{type:"object",field:$f},value:$v}]}}]}'
  fi
}
write() { # WS ID REQUEST -> prints the log height (acceptedCount) of the record
  local wsd=$1 id=$2 req=$3
  run "p-$id" "$MINI" workspace --action propose --dir "$wsd" --request "$req" --proposal-id "$id"; ok "p-$id"
  run "s-$id" "$MINI" workspace --action submit --dir "$wsd" --intent "$wsd/proposals/$id/intent.json" \
    --attempt "$wsd/attempts/$id"; ok "s-$id"
  jq -e '.type == "confirmed"' "$wsd/attempts/$id/outcome.json" >/dev/null || { echo "$id not confirmed" >&2; exit 1; }
  jq -r .acceptedCount "$wsd/attempts/$id/outcome.json"
}
q() { # NAME WS VIEW TARGET CAP [HEIGHT] — a signed query, answered by a cold open of the Store
  local name=$1 wsd=$2 view=$3 target=$4 cap=$5 height=${6:-} purpose
  if [ -n "$height" ]; then
    purpose=$(jq -cn --arg v "$view" --arg t "$target" --arg h "$height" '{type:"query",kind:"object",target:$t,view:$v,height:$h}')
  else
    purpose=$(jq -cn --arg v "$view" --arg t "$target" '{type:"query",kind:"object",target:$t,view:$v}')
  fi
  jq -n --arg s "$(ws "$wsd" subject)" --arg n "$(date +%s%N)" --argjson p "$purpose" --arg t "$target" --arg c "$cap" \
    '{subject:$s,nonce:$n,purpose:$p,grants:[{kind:"object",target:$t,capability:$c}]}' >"$D/req/$name.json"
  run "$name" "$MINI" query --host "$(ws "$wsd" host)" --config "$(ws "$wsd" config)" --intent "$D/req/$name.json" \
    --key "$(ws "$wsd" key)" --view "$view" --dir "$D/q/$name"
}
got_of() { # NAME -> read | refused
  if [ "$(cat "$D/$1.rc")" = 0 ]; then echo read
  elif grep -q "refused" "$D/$1.err"; then echo refused
  else echo client-error; fi
}

A=$SPONSOR_SUBJECT
B=$NEWCOMER_SUBJECT
lab=$(jq -r .target "$SPONSOR_WS/refs/lab.json")
note=$(jq -r .target "$SPONSOR_WS/refs/note.json")
labcap=$(jq -r .observeCapability "$SPONSOR_WS/refs/lab.json")
child=$(jq -r .observeCapability "$NEWCOMER_WS/refs/lab.json")

# A second invite: observe and mutate under lab, so B can act in the room.
jq -n --arg r "$B" '{type:"minidregg-workspace-proposal-v1",action:"delegate",name:"lab",
  recipient:$r,verbs:["observe","mutate"],maxCost:"50000",room:true}' >"$D/req/invite-w.json"
run invite-w-propose "$MINI" workspace --action propose --dir "$SPONSOR_WS" --request "$D/req/invite-w.json" \
  --proposal-id invite-bw; ok invite-w-propose
run invite-w-submit "$MINI" workspace --action submit --dir "$SPONSOR_WS" \
  --intent "$SPONSOR_WS/proposals/invite-bw/intent.json" --attempt "$SPONSOR_WS/attempts/invite-bw"; ok invite-w-submit
run invite-w-publish "$MINI" workspace --action publish-delegation --dir "$SPONSOR_WS" --proposal-id invite-bw \
  --attempt "$SPONSOR_WS/attempts/invite-bw"; ok invite-w-publish
run b-import-labw "$MINI" workspace --action import --dir "$NEWCOMER_WS" --name labw \
  --from-ref "$SPONSOR_WS/proposals/invite-bw/recipient-reference.json"; ok b-import-labw
wcap=$(jq -r .observeCapability "$NEWCOMER_WS/refs/labw.json")
run b-import-notew "$MINI" workspace --action import --dir "$NEWCOMER_WS" --name notew --kind object \
  --target "$note" --observe-capability "$wcap" --operation-capability "$wcap"; ok b-import-notew

# A writes note's field 7 until the log is past the checkpoint at 64.
scalar note create 7 1 >"$D/req/a-0.json"
first=$(write "$SPONSOR_WS" a-w0 "$D/req/a-0.json")
value=1; HA=$first; low=$first
while [ "$HA" -lt 70 ]; do
  scalar note write 7 $((value + 1)) "$value" >"$D/req/a-$value.json"
  HA=$(write "$SPONSOR_WS" "a-w$value" "$D/req/a-$value.json")
  value=$((value + 1))
  [ "$value" -lt 120 ] || { echo "the log did not pass height 70" >&2; exit 1; }
done
# B writes note's field 8.
scalar notew create 8 42 >"$D/req/b-0.json"
HB=$(write "$NEWCOMER_WS" b-w0 "$D/req/b-0.json")
btx=$(jq -r .transactionId "$NEWCOMER_WS/attempts/b-w0/outcome.json")
atx=$(jq -r .transactionId "$SPONSOR_WS/attempts/a-w$((value - 1))/outcome.json")
[ "$HB" = $((HA + 1)) ] || { echo "B's write is at log height $HB, not $((HA + 1))" >&2; exit 1; }

# The genesis height: a current read's challenge height minus the log height.
q at-probe "$SPONSOR_WS" resource "$note" "$labcap"; ok at-probe
H=$(jq -r .height "$D/q/at-probe/challenge.json")
G=$((H - HB))
echo "log heights: A last wrote at $HA, B at $HB; genesis height $G; current height $H" >&2

# who
q who-a "$SPONSOR_WS" who "$lab" "$labcap"
seenA=$(jq -r --arg s "$A" '.members[] | select(.subject == $s) | .lastSeen' "$D/who-a.out" 2>/dev/null)
seenB=$(jq -r --arg s "$B" '.members[] | select(.subject == $s) | .lastSeen' "$D/who-a.out" 2>/dev/null)
g=$(got_of who-a); [ "$g" = read ] && { [ "$seenA" = $((G + HA)) ] && [ "$seenB" = $((G + HB)) ] || g="wrong:A=$seenA,B=$seenB"; }
row who-a read "$g" "$(jq -c '.members' "$D/who-a.out" 2>/dev/null) want A@$((G + HA)) B@$((G + HB))"
q who-b "$NEWCOMER_WS" who "$lab" "$child"
g=$(got_of who-b); [ "$g" = read ] && { cmp -s <(jq -S .members "$D/who-a.out") <(jq -S .members "$D/who-b.out") || g=differs; }
row who-b read "$g" "$(jq -c '.members' "$D/who-b.out" 2>/dev/null)"
q who-third-owner "$TW" who "$lab" "$labcap"
row who-third-owner refused "$(got_of who-third-owner)" "$(tail -1 "$D/who-third-owner.err" | cut -c1-160)"
q who-third-child "$TW" who "$lab" "$child"
row who-third-child refused "$(got_of who-third-child)" "$(tail -1 "$D/who-third-child.err" | cut -c1-160)"

# since
q since-ha "$SPONSOR_WS" since "$lab" "$labcap" $((G + HA))
g=$(got_of since-ha)
[ "$g" = read ] && { jq -e --arg tx "$btx" --arg h "$((G + HB))" --arg s "$B" --arg n "$note" \
  '.entries | length == 1 and .[0].transaction == $tx and .[0].height == $h and .[0].subject == $s and .[0].cells == [$n]' \
  "$D/since-ha.out" >/dev/null || g=wrong; }
row since-ha read "$g" "$(jq -c .entries "$D/since-ha.out" 2>/dev/null)"
q since-before "$SPONSOR_WS" since "$lab" "$labcap" $((G + HA - 1))
g=$(got_of since-before)
[ "$g" = read ] && { jq -e --arg a "$atx" --arg b "$btx" '[.entries[].transaction] == [$a, $b]' \
  "$D/since-before.out" >/dev/null || g=wrong; }
row since-before read "$g" "$(jq -c '[.entries[] | {height, subject}]' "$D/since-before.out" 2>/dev/null)"

# at
q at-ha1 "$SPONSOR_WS" at "$note" "$labcap" $((G + HA - 1))
q at-ha "$SPONSOR_WS" at "$note" "$labcap" $((G + HA))
g=read; for n in at-ha1 at-ha; do [ "$(got_of $n)" = read ] || g=$(got_of $n); done
[ "$g" = read ] && { cmp -s "$D/at-ha1.out" "$D/at-ha.out" && g=same; }
row at-differ-high read "$g" "at $((G + HA - 1)) vs $((G + HA)): $(jq -c .resource.cell.root "$D/at-ha1.out") vs $(jq -c .resource.cell.root "$D/at-ha.out")"
q at-low1 "$SPONSOR_WS" at "$note" "$labcap" $((G + low))
q at-low "$SPONSOR_WS" at "$note" "$labcap" $((G + low + 1))
g=read; for n in at-low1 at-low; do [ "$(got_of $n)" = read ] || g=$(got_of $n); done
[ "$g" = read ] && { cmp -s "$D/at-low1.out" "$D/at-low.out" && g=same; }
row at-differ-low read "$g" "at $((G + low)) vs $((G + low + 1)) (checkpoint at 64): $(jq -c .resource.cell.root "$D/at-low1.out") vs $(jq -c .resource.cell.root "$D/at-low.out")"
q at-current "$SPONSOR_WS" at "$note" "$labcap" "$H"
q read-current "$SPONSOR_WS" resource "$note" "$labcap"
g=$(got_of at-current)
[ "$g" = read ] && { cmp -s <(jq -S .resource.cell "$D/at-current.out") <(jq -S .cell "$D/read-current.out") || g=differs; }
row at-current read "$g" "at $H root $(jq -c .resource.cell.root "$D/at-current.out") = read root $(jq -c .cell.root "$D/read-current.out")"
q at-above "$SPONSOR_WS" at "$note" "$labcap" $((H + 5))
g=$(got_of at-above)
[ "$g" = refused ] && { grep -q "above the current height" "$D/at-above.err" || g=refused-without-reason; }
row at-above refused "$g" "$(grep -o 'history read refused[^"]*' "$D/at-above.err" | head -1)"

# A cold open and the audit walk: the same index.
run reopen "$HOST" "$CONFIG" presence-index
run audit "$HOST" "$CONFIG" audit
g=$(got_of reopen)
ri=$(grep '^index ' "$D/reopen.out"); ai=$(grep '^index ' "$D/audit.out")
[ "$g" = read ] && { echo "$ri" | sed 's/^index //' | jq -e --arg n "$note" --arg a "$A" --arg b "$B" --arg ha "$HA" --arg hb "$HB" \
  'any(.lastSeen[]; . == [$n, $a, $ha]) and any(.lastSeen[]; . == [$n, $b, $hb])' >/dev/null || g=wrong; }
row reopen-index read "$g" "$(head -1 "$D/reopen.out")"
g=$(got_of audit)
[ "$g" = read ] && { [ -n "$ai" ] && [ "$ai" = "$ri" ] || g=differs; }
row audit-index read "$g" "$(head -1 "$D/audit.out" | cut -c1-120)"
echo "reopen $ri" >&2
echo "audit  $ai" >&2

cat "$rows" >&2
[ "$bad" = 0 ] || { echo "$bad index rows differ from expectation (see $rows)" >&2; exit 1; }
echo "12/12 index rows as expected: who lists A@$((G + HA)) and B@$((G + HB)), the third key refused twice; since lists only B's write; at differs across a write above and below the checkpoint, equals the read now, refuses above now; cold reopen and audit print the same index" >&2
echo "$rows"
