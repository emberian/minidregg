#!/usr/bin/env bash
# journey.d/jhide.sh — K-NARROW-HIDE: a narrowed read carries a HIDING root;
# K-HIDE-ROTATE: the blinding ratchets at every write, so every sealed leaf moves.
# Runs on the journey's fresh Store after J5 (A = sponsor, B = newcomer).
#
# A births `hledger` (declared; A's client derives its blinding from A's key and
# the cell id), creates fields 3 = 10 and 4 = 20, and delegates observe with
# fields {3} to B.
#   r-view            B reads: field 3 present, field 4 absent; the client
#                     recomputed every opened leaf and the root      -> verified
#   a-view            A reads all fields; only the blinding is sealed -> verified
#   roots-agree       B's root is A's root (a salted root)            -> same
#   r-opens-3         B holds exactly one opening (field 3: salt + entry) -> 1
#   r-sealed-4        field 4 reaches B as a 32-byte leaf only: no salt, no
#                     entry bytes of A's field-4 opening in B's view    -> sealed
#   owner-derives-4   A's client derives field 4's salt from its own key and the
#                     heights of the cell's two writes (the ratchet), and it
#                     equals the salt the Host serves A               -> same
#   owner-derives-3   the same for field 3, against the salt B was served -> same
#   tamper-value      B's view with field 3's displayed value changed  -> refused
#   tamper-entry      B's view with field 3's opened entry changed     -> refused
#   tamper-root       B's view with another root                      -> refused
#   a-writes-4        A writes field 4: 20 -> 21                       -> installed
#   covered-same      B reads again: every opened ENTRY and every displayed
#                     entry byte-identical (the opened salts are re-keyed) -> identical
#   root-moves        ... and the root differs: B learns THAT the cell was
#                     written (still visible under the ratchet)        -> different
#   every-leaf-moves  every sealed leaf differs (fields 1 and 4 and the
#                     blinding alike) and none of B's earlier sealed leaves
#                     appears in its later view: WHICH field was written is
#                     not visible (K-NARROW-HIDE's one-leaf-moves, inverted) -> 3/3
#   return-to-old-value-invisible  A writes 4 := 30 then 4 := 20 (its value at
#                     B's first view); none of B's sealed leaves after equals
#                     any of B's sealed leaves at its first view       -> invisible
#   owner-derives-now A derives field 3's salt after all five writes and it
#                     equals the salt B is served now                 -> same
#   restart-same      after a stop/audit/start, B's view is byte-identical and
#                     verifies (the ratchet replays to the same blinding) -> identical
#   audit             `mini audit` re-admits every signed ingress       -> audited
# Exported by the journey: MINI HOST CONFIG SOCKET JOURNEY_WORLD SPONSOR_WS NEWCOMER_WS SPONSOR_SUBJECT
# NEWCOMER_SUBJECT JOURNEY_STEP_DIR. Exit 0 = every row as expected. Last
# stdout line = the rows file.
set -uo pipefail
D=$JOURNEY_STEP_DIR
W=$JOURNEY_WORLD
mkdir -p "$D/req"
rows=$D/hide-rows.tsv
: >"$rows"
bad=0

run() { local name=$1; shift; "$@" >"$D/$name.out" 2>"$D/$name.err"; echo $? >"$D/$name.rc"; }
must() { [ "$(cat "$D/$1.rc")" = 0 ] || { echo "setup $1 failed: $(tail -1 "$D/$1.err")" >&2; exit 1; }; }
installed() { jq -e '.type == "confirmed" and .confirmation == "installed"' "$1" >/dev/null 2>&1; }
record() { # NAME EXPECT GOT DETAIL
  printf '%s\texpect=%s\tgot=%s\t%s\n' "$1" "$2" "$3" "$4" >>"$rows"
  [ "$2" = "$3" ] || bad=$((bad + 1))
}
invoke() { # WS ID REQUEST -> installed | refused | error
  local ws=$1 id=$2 req=$3
  run "$id-propose" "$MINI" workspace --action propose --dir "$ws" --request "$req" --proposal-id "$id"
  [ "$(cat "$D/$id-propose.rc")" = 0 ] || { echo propose-error; return; }
  run "$id" "$MINI" workspace --action submit --dir "$ws" --intent "$ws/proposals/$id/intent.json" \
    --attempt "$ws/attempts/$id"
  if installed "$ws/attempts/$id/outcome.json"; then echo installed; else echo refused; fi
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
field_value() { jq -r --arg f "$2" '[.cell.entries[]? | select(.key.field == $f) | .value][0] // "absent"' "$1"; }
# The opened item of a displayed field: opened items are in canonical order,
# as the displayed entries are (the blinding is never displayed nor opened).
opened_of() { # VIEW FIELD -> {"salt","entry"}
  jq -c --arg f "$2" '([.cell.entries[] | .key.field] | index($f)) as $i
    | [.opening.items[] | select(.salt)] | .[$i]' "$1"
}
verified() { jq -e '.hiding.verified == true' "$1" >/dev/null 2>&1; }
P=$D/req/permit-all.json
printf '%s\n' '{"type":"all","predicates":[]}' >"$P"
A_KEY=$(jq -r .key "$SPONSOR_WS/workspace.json")
# The admission height of a write: the genesis height plus its record's index
# (a receipt's acceptedCount is that index + 1).  The ratchet runs at it.
G=$(jq -r .genesisHeight "$W/genesis-params.json")
HEIGHTS=""
add_height() { # OUTCOME.json
  local c; c=$(jq -r .acceptedCount "$1")
  HEIGHTS="${HEIGHTS:+$HEIGHTS,}$((G + c - 1))"
}

# ---- setup
run create "$MINI" workspace --action create --dir "$SPONSOR_WS" --name hledger --storage declared --predicate "$P"
must create
T=$(jq -r .target "$SPONSOR_WS/refs/hledger.json")
blinding=$(jq -r '.birth.resources[0].blinding // "none"' "$SPONSOR_WS/sources/create-hledger.json")
[ "$blinding" != none ] || { echo "the birth source carries no blinding" >&2; exit 1; }
[ "$("$MINI" key --action cell-blinding --secret "$A_KEY" --cell "$T")" = "$blinding" ] \
  || { echo "the birth's blinding is not the one A's key derives" >&2; exit 1; }
scalar hledger create 3 10 >"$D/req/c3.json"; [ "$(invoke "$SPONSOR_WS" h-c3 "$D/req/c3.json")" = installed ] || { echo "create 3 failed" >&2; exit 1; }
add_height "$SPONSOR_WS/attempts/h-c3/outcome.json"
scalar hledger create 4 20 >"$D/req/c4.json"; [ "$(invoke "$SPONSOR_WS" h-c4 "$D/req/c4.json")" = installed ] || { echo "create 4 failed" >&2; exit 1; }
add_height "$SPONSOR_WS/attempts/h-c4/outcome.json"
jq -n --arg r "$NEWCOMER_SUBJECT" '{type:"minidregg-workspace-proposal-v1",action:"delegate",name:"hledger",
  recipient:$r,verbs:["observe"],maxCost:"50000",fields:["3"]}' >"$D/req/give.json"
run give-propose "$MINI" workspace --action propose --dir "$SPONSOR_WS" --request "$D/req/give.json" --proposal-id h-give; must give-propose
run give "$MINI" workspace --action submit --dir "$SPONSOR_WS" --intent "$SPONSOR_WS/proposals/h-give/intent.json" \
  --attempt "$SPONSOR_WS/attempts/h-give"
installed "$SPONSOR_WS/attempts/h-give/outcome.json" || { echo "delegation failed: $(tail -1 "$D/give.err")" >&2; exit 1; }
run give-publish "$MINI" workspace --action publish-delegation --dir "$SPONSOR_WS" --proposal-id h-give \
  --attempt "$SPONSOR_WS/attempts/h-give"; must give-publish
run import "$MINI" workspace --action import --dir "$NEWCOMER_WS" --name hledger \
  --from-ref "$SPONSOR_WS/proposals/h-give/recipient-reference.json"; must import

# ---- reads
run r-view "$MINI" workspace --action read --dir "$NEWCOMER_WS" --name hledger
v3=$(field_value "$D/r-view.out" 3); v4=$(field_value "$D/r-view.out" 4)
[ "$(cat "$D/r-view.rc")" = 0 ] && verified "$D/r-view.out" && [ "$v3" = 10 ] && [ "$v4" = absent ] && got=verified || got=wrong
record r-view verified "$got" "field3=$v3 field4=$v4 hiding=$(jq -c .hiding "$D/r-view.out" 2>/dev/null)"
run a-view "$MINI" workspace --action read --dir "$SPONSOR_WS" --name hledger
[ "$(cat "$D/a-view.rc")" = 0 ] && verified "$D/a-view.out" && [ "$(jq .hiding.sealed "$D/a-view.out")" = 1 ] \
  && [ "$(field_value "$D/a-view.out" 4)" = 20 ] && got=verified || got=wrong
record a-view verified "$got" "hiding=$(jq -c .hiding "$D/a-view.out" 2>/dev/null) (the one sealed item is the blinding)"
r_root=$(jq -r .cell.root "$D/r-view.out"); a_root=$(jq -r .cell.root "$D/a-view.out")
[ "$r_root" = "$a_root" ] && got=same || got=different
record roots-agree same "$got" "root ${r_root:0:24}…"
n=$(jq '[.opening.items[] | select(.salt)] | length' "$D/r-view.out")
record r-opens-3 1 "$n" "B's opened items (field 3 only; its entry is checked against the displayed field 3)"
a4=$(opened_of "$D/a-view.out" 4); e4=$(jq -r .entry <<<"$a4"); s4=$(jq -r .salt <<<"$a4")
hits=$(jq --arg e "$e4" --arg s "$s4" '[.. | strings | select(. == $e or . == $s)] | length' "$D/r-view.out")
sealed=$(jq '[.opening.items[] | select(.leaf) | .leaf | length] | map(select(. == 64)) | length' "$D/r-view.out")
[ "$hits" = 0 ] && [ "$sealed" = 3 ] && got=sealed || got=leaked
record r-sealed-4 sealed "$got" "field 4 entry/salt occurrences in B's view: $hits; sealed 32-byte leaves: $sealed (fields 1, 4 and the blinding)"
d4=$("$MINI" key --action derive-salt --secret "$A_KEY" --cell "$T" --storage declared --heights "$HEIGHTS" --entry "$e4" 2>"$D/derive4.err")
[ "$d4" = "$s4" ] && got=same || got=different
record owner-derives-4 same "$got" "A derives field 4's salt from its key and write heights $HEIGHTS: ${d4:0:16}… served ${s4:0:16}…"
r3=$(opened_of "$D/r-view.out" 3)
d3=$("$MINI" key --action derive-salt --secret "$A_KEY" --cell "$T" --storage declared --heights "$HEIGHTS" --entry "$(jq -r .entry <<<"$r3")" 2>"$D/derive3.err")
[ "$d3" = "$(jq -r .salt <<<"$r3")" ] && got=same || got=different
record owner-derives-3 same "$got" "A derives the field-3 salt B was served"

# ---- tampered views refuse client-side
jq '(.cell.entries[] | select(.key.field == "3") | .value) = "99"' "$D/r-view.out" >"$D/t-value.json"
jq '(.opening.items[] | select(.salt) | .entry) |= ("01" + .[2:])' "$D/r-view.out" >"$D/t-entry.json"
jq '.cell.root = "1"' "$D/r-view.out" >"$D/t-root.json"
for t in value entry root; do
  run "tamper-$t" "$MINI" verify-view --view "$D/t-$t.json"
  [ "$(cat "$D/tamper-$t.rc")" != 0 ] && got=refused || got=accepted
  record "tamper-$t" refused "$got" "$(tail -1 "$D/tamper-$t.err" | cut -c1-120)"
done
cmp -s "$D/t-entry.json" "$D/r-view.out" && { echo "tamper-entry did not change the view" >&2; bad=$((bad + 1)); }

# ---- a write B may not read
scalar hledger write 4 21 20 >"$D/req/w4.json"
record a-writes-4 installed "$(invoke "$SPONSOR_WS" h-w4 "$D/req/w4.json")" "A writes field 4: 20 -> 21"
add_height "$SPONSOR_WS/attempts/h-w4/outcome.json"
run r-view2 "$MINI" workspace --action read --dir "$NEWCOMER_WS" --name hledger
verified "$D/r-view2.out" || { echo "B's second view does not verify" >&2; bad=$((bad + 1)); }
o1=$(jq -c '[[.opening.items[] | select(.salt) | .entry], .cell.entries]' "$D/r-view.out")
o2=$(jq -c '[[.opening.items[] | select(.salt) | .entry], .cell.entries]' "$D/r-view2.out")
salts=$(jq -n --slurpfile a "$D/r-view.out" --slurpfile b "$D/r-view2.out" \
  '[$a[0].opening.items[] | select(.salt) | .salt] != [$b[0].opening.items[] | select(.salt) | .salt]')
[ "$o1" = "$o2" ] && got=identical || got=changed
record covered-same identical "$got" "opened entries and displayed entries before/after A's write to field 4 (opened salts re-keyed: $salts)"
r2_root=$(jq -r .cell.root "$D/r-view2.out")
[ "$r2_root" != "$r_root" ] && got=different || got=same
record root-moves different "$got" "still visible: B learns THAT the cell was written"
sealed_moved() { # VIEW-BEFORE VIEW-AFTER -> "<moved>/<sealed> <surviving>": positional moves, and how
  # many of AFTER's sealed leaves equal ANY of BEFORE's (a returned or untouched entry)
  jq -rn --slurpfile a "$1" --slurpfile b "$2" '
    ([$a[0].opening.items[] | select(.leaf) | .leaf]) as $x
    | ([$b[0].opening.items[] | select(.leaf) | .leaf]) as $y
    | "\([range(0; $x | length) as $i | select($x[$i] != $y[$i])] | length)/\($x | length) \([$y[] | select(. as $l | $x | index($l))] | length)"'
}
read -r moved surviving <<<"$(sealed_moved "$D/r-view.out" "$D/r-view2.out")"
[ "$surviving" = 0 ] && got=$moved || got="$moved+$surviving-survive"
record every-leaf-moves 3/3 "$got" "B's sealed leaves that moved / sealed; $surviving of B's earlier sealed leaves reappear (was one-leaf-moves = 1 under the static blinding)"

# ---- a return to an earlier value
scalar hledger write 4 30 21 >"$D/req/w30.json"
[ "$(invoke "$SPONSOR_WS" h-w30 "$D/req/w30.json")" = installed ] || { echo "write 4 := 30 failed" >&2; exit 1; }
add_height "$SPONSOR_WS/attempts/h-w30/outcome.json"
scalar hledger write 4 20 30 >"$D/req/w20.json"
[ "$(invoke "$SPONSOR_WS" h-w20 "$D/req/w20.json")" = installed ] || { echo "write 4 := 20 failed" >&2; exit 1; }
add_height "$SPONSOR_WS/attempts/h-w20/outcome.json"
run a-view4 "$MINI" workspace --action read --dir "$SPONSOR_WS" --name hledger
run r-view4 "$MINI" workspace --action read --dir "$NEWCOMER_WS" --name hledger
read -r moved4 surviving4 <<<"$(sealed_moved "$D/r-view.out" "$D/r-view4.out")"
same4=$(jq -c '[[.opening.items[] | select(.salt) | .entry], .cell.entries]' "$D/r-view4.out")
verified "$D/r-view4.out" && [ "$(field_value "$D/a-view4.out" 4)" = 20 ] && [ "$same4" = "$o1" ] \
  && [ "$surviving4" = 0 ] && got=invisible || got="visible($surviving4)"
record return-to-old-value-invisible invisible "$got" "field 4 back at 20 (A reads $(field_value "$D/a-view4.out" 4)); $moved4 of B's sealed leaves moved; $surviving4 of B's first-view sealed leaves reappear"
r4=$(opened_of "$D/r-view4.out" 3)
d3n=$("$MINI" key --action derive-salt --secret "$A_KEY" --cell "$T" --storage declared --heights "$HEIGHTS" --entry "$(jq -r .entry <<<"$r4")" 2>"$D/derive3n.err")
[ "$d3n" = "$(jq -r .salt <<<"$r4")" ] && got=same || got=different
record owner-derives-now same "$got" "A derives B's current field-3 salt from its key and the five write heights $HEIGHTS"

# ---- restart, audit, replay
pidfile=$W/public/server.pid
pid=$(cat "$pidfile"); kill -TERM "$pid"
for i in $(seq 1 300); do kill -0 "$pid" 2>/dev/null || break; sleep 0.1; done
kill -0 "$pid" 2>/dev/null && { echo "server $pid alive after TERM" >&2; exit 1; }
"$MINI" audit --host "$HOST" --config "$CONFIG" >"$D/audit.out" 2>"$D/audit.err"
setsid nohup "$MINI" serve --host "$HOST" --config "$CONFIG" --socket "$SOCKET" \
  >"$W/public/serve-khide.log" 2>&1 </dev/null &
echo $! >"$pidfile"
for i in $(seq 1 6000); do
  [ -S "$SOCKET" ] && grep -q serving "$W/public/serve-khide.log" 2>/dev/null && break; sleep 0.1
done
run r-view3 "$MINI" workspace --action read --dir "$NEWCOMER_WS" --name hledger
c2=$(jq -c '[.cell, .opening]' "$D/r-view4.out"); c3=$(jq -c '[.cell, .opening]' "$D/r-view3.out")
verified "$D/r-view3.out" && [ "$c2" = "$c3" ] && got=identical || got=changed
record restart-same identical "$got" "B's view across stop/audit/start: the ratchet replays to the same blinding (root $(jq -r .cell.root "$D/r-view4.out" | cut -c1-16)…)"
grep -q "audited" "$D/audit.out" "$D/audit.err" 2>/dev/null && got=audited || got=failed
record audit audited "$got" "$(cat "$D/audit.out" "$D/audit.err" 2>/dev/null | grep -m1 audited | cut -c1-140)"

cat "$rows" >&2
n=$(wc -l <"$rows")
[ "$bad" = 0 ] || { echo "$bad hide rows differ from expectation (see $rows)" >&2; exit 1; }
echo "$n/$n hide rows as expected: field-3 reader verifies its opening against a salted root, field 4 sealed, owner re-derives ratcheted salts, tampering refused, a field-4 write moves the root and every sealed leaf, a return to an old value is invisible, restart and audit replay the ratchet" >&2
echo "$rows"
