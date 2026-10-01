#!/usr/bin/env bash
# journey.d/j12i-links.sh — the link index (K-DOC-INDEX): `doc backlinks` and
# `doc links` are one signed query of the Host's cached fold of the accepted
# log, and a reader sees only backlinks from documents it may read.
#
# Parties: A = sponsor; E = a key enrolled here. A creates two rooms, X and Y,
# and four content documents: `target`, `srcx` and `qdoc` born in X, `srcy`
# born in Y. E holds a room invite (observe) on X only.
# Rows:
#   srcx-links                srcx links to target                         -> installed
#   srcy-links                srcy links to target                         -> installed
#   a-backlinks               A's backlinks of target                      -> srcx, srcy
#   e-backlinks               E's backlinks of target (no grant covers srcy) -> srcx only
#   e-not-srcy                srcy's link is absent from E's view           -> absent
#   oracle-a / oracle-e       the old client fold over every readable page agrees with the view
#   e-after-grant             A delegates srcy (observe) to E; E's backlinks -> srcx, srcy
#   oracle-e2                 the fold agrees again
#   srcx-forward              doc links srcx                                -> 1 link -> target
#   unlink                    A unlinks srcx's link                         -> installed
#   unlink-gone               A's and E's backlinks lose srcx; doc links srcx -> 0
#   oracle-a2                 the fold agrees after the unlink
#   reopen-identical          the view read again (a cold open) is byte-identical; the
#                             checkpoint+suffix index equals audit's genesis replay
#   audit                     Host audit re-admits every accepted record
# Exported by the journey: MINI HOST CONFIG SOCKET SPONSOR_WS JOURNEY_WORLD JOURNEY_STEP_DIR.
# Exit 0 = every row as expected. Last stdout line = the rows file.
set -uo pipefail
D=$JOURNEY_STEP_DIR
W=$JOURNEY_WORLD
mkdir -p "$D/req" "$D/oracle"
rows=$D/link-rows.tsv
: >"$rows"
bad=0
REFUSAL_TAG=44524547472f4e41544956452d484f53542f4f5554434f4d45

run() { local name=$1; shift; "$@" >"$D/$name.out" 2>"$D/$name.err"; echo $? >"$D/$name.rc"; }
host_refused() {
  [ "$(cat "$D/$1.rc")" != 0 ] && grep -q "encoded refusal: $REFUSAL_TAG\|host refused\|host returned refused\|observation refused" "$D/$1.err"
}
row() { # NAME EXPECT GOT DETAIL
  printf '%s\texpect=%s\tgot=%s\t%s\n' "$1" "$2" "$3" "$4" >>"$rows"
  [ "$2" = "$3" ] || bad=$((bad + 1))
}
outcome() {
  if [ "$(cat "$D/$1.rc")" = 0 ]; then echo installed
  elif host_refused "$1"; then echo refused
  else echo client-error; fi
}
ok() { [ "$(cat "$D/$1.rc")" = 0 ] || { echo "setup $1 failed: $(tail -3 "$D/$1.err")" >&2; exit 1; }; }
invoke() { # NAME WS RESOURCE ACTIONS-JSON
  local name=$1 ws=$2 res=$3 actions=$4
  jq -n --arg r "$res" --argjson a "$actions" \
    '{type:"minidregg-workspace-proposal-v1",action:"invoke",targets:[{name:$r,payload:{type:"content",actions:$a}}]}' \
    >"$D/req/$name.json"
  run "$name-propose" "$MINI" workspace --action propose --dir "$ws" --request "$D/req/$name.json" --proposal-id "$name"
  if [ "$(cat "$D/$name-propose.rc")" != 0 ]; then cp "$D/$name-propose.rc" "$D/$name.rc"
    cp "$D/$name-propose.err" "$D/$name.err"; : >"$D/$name.out"; return; fi
  run "$name" "$MINI" workspace --action submit --dir "$ws" \
    --intent "$ws/proposals/$name/intent.json" --attempt "$ws/attempts/$name"
}
publish() { # NAME FROM-WS REQUEST-JSON-FILE
  run "$1-propose" "$MINI" workspace --action propose --dir "$2" --request "$3" --proposal-id "$1"; ok "$1-propose"
  run "$1-submit" "$MINI" workspace --action submit --dir "$2" \
    --intent "$2/proposals/$1/intent.json" --attempt "$2/attempts/$1"; ok "$1-submit"
  run "$1-publish" "$MINI" workspace --action publish-delegation --dir "$2" --proposal-id "$1" \
    --attempt "$2/attempts/$1"; ok "$1-publish"
}
enroll() { # NAME -> workspace at $W/NAME-workspace; prints subject
  local A=$W/attempts/$1
  run "$1-keygen" "$MINI" keygen --secret "$W/$1.key" --public "$W/$1.pub"; ok "$1-keygen"
  run "$1-plan" "$MINI" enroll --action plan --sponsor-workspace "$SPONSOR_WS" --factory-ref factory \
    --name "$1-1" --new-key "$W/$1.key" --dir "$A"; ok "$1-plan"
  run "$1-seal" "$MINI" enroll --action seal --dir "$A"; ok "$1-seal"
  run "$1-enroll" "$MINI" enroll --action submit --dir "$A"; ok "$1-enroll"
  run "$1-init" "$MINI" workspace --action init --host "$HOST" --config "$CONFIG" --socket "$SOCKET" \
    --enrollment "$A/enrollment.json" --dir "$W/$1-workspace"; ok "$1-init"
  jq -r .subject "$D/$1-enroll.out"
}
hexof() { printf '%s' "$1" | xxd -p | tr -d '\n'; }
tgt() { jq -r .target "$1/refs/$2.json"; }
# The view's backlinks as sorted "cell:link" pairs.
view_pairs() { # NAME WS DOC VIEWACTION
  run "$1" "$MINI" workspace --action "$4" --dir "$2" --name "$3"
}
backlink_set() { # WS NAME-OF-VIEW-RUN -> sorted "cell:link" from the view's retained JSON
  local attempt; attempt=$(grep -o 'workspace read attempt: .*\|attempt: [^ ]*' "$D/$2.err" | tail -1 | awk '{print $NF}')
  grep -v '^#' "$D/$2.out" | awk '{print $1":"$3}' | sort | tr '\n' ' ' | sed 's/ $//'
}
# The old fold, kept here as the differential oracle: read every page this
# workspace holds a reference to, and collect each live link whose target is
# DOC (document or range) — as `doc backlinks` computed it before the index.
oracle() { # TAG WS DOCID -> sorted "name:link"
  local tag=$1 ws=$2 doc=$3 name
  : >"$D/oracle/$tag.txt"
  for f in "$ws"/refs/*.json; do
    name=$(basename "$f" .json)
    run "oracle-$tag-$name" "$MINI" workspace --action read --dir "$ws" --name "$name"
    [ "$(cat "$D/oracle-$tag-$name.rc")" = 0 ] || continue
    jq -r --arg d "$doc" --arg n "$name" '.cell.entries[]? | select(.type == "link" and .tombstonedAt == null)
      | select((.target.type == "document" and .target.id == $d) or (.target.type == "range" and .target.document == $d))
      | $n + ":" + .id' "$D/oracle-$tag-$name.out" >>"$D/oracle/$tag.txt" 2>/dev/null
  done
  sort "$D/oracle/$tag.txt" | tr '\n' ' ' | sed 's/ $//'
}

E_SUBJECT=$(enroll erin); EW=$W/erin-workspace
printf '%s\n' '{"type":"all","predicates":[]}' >"$D/req/permit-all.json"
for room in roomx roomy; do
  run "create-$room" "$MINI" workspace --action create --dir "$SPONSOR_WS" --name "$room" --storage declared \
    --predicate "$D/req/permit-all.json"; ok "create-$room"
done
for pair in target:roomx srcx:roomx qdoc:roomx srcy:roomy; do
  doc=${pair%%:*}; room=${pair##*:}
  run "create-$doc" "$MINI" workspace --action create --dir "$SPONSOR_WS" --name "$doc" --storage content \
    --predicate "$D/req/permit-all.json" --in "$room"; ok "create-$doc"
done
target=$(tgt "$SPONSOR_WS" target); srcx=$(tgt "$SPONSOR_WS" srcx); srcy=$(tgt "$SPONSOR_WS" srcy)
qdoc=$(tgt "$SPONSOR_WS" qdoc); roomx=$(tgt "$SPONSOR_WS" roomx)

doc_create() { # NAME ROOTELEMENT ATOM TEXT
  invoke "write-$1" "$SPONSOR_WS" "$1" "$(jq -n --arg e "$2" --arg a "$3" --arg t "$(hexof "$4")" '[
    {type:"createDocument",rootElement:$e,schema:"0"},
    {type:"createAtom",atom:$a,kind:{type:"text"},payload:$t}]')"; ok "write-$1"
}
doc_create target 1 1001 "the target line"
doc_create srcx 2 2001 "x cites the target"
doc_create srcy 3 3001 "y cites the target"
doc_create qdoc 4 4001 "q quotes the target"

link_to() { # NAME DOC LINKID
  invoke "$1" "$SPONSOR_WS" "$2" "$(jq -n --arg l "$3" --arg d "$target" \
    '[{type:"link",link:$l,source:null,target:{type:"document",id:$d},relation:"0"}]')"
}
link_to srcx-links srcx 9101
row srcx-links installed "$(outcome srcx-links)" "$(tail -1 "$D/srcx-links.err" | cut -c1-160)"
link_to srcy-links srcy 9201
row srcy-links installed "$(outcome srcy-links)" "$(tail -1 "$D/srcy-links.err" | cut -c1-160)"

# E: a room invite (observe) on X; references to every document, srcy's under the X grant
# (so the oracle tries it and is refused, exactly as the old fold was).
jq -n --arg r "$E_SUBJECT" '{type:"minidregg-workspace-proposal-v1",action:"delegate",name:"roomx",
  recipient:$r,verbs:["observe"],maxCost:"50000",room:true}' >"$D/req/invite-x.json"
publish invite-x "$SPONSOR_WS" "$D/req/invite-x.json"
run e-import-roomx "$MINI" workspace --action import --dir "$EW" --name roomx \
  --from-ref "$SPONSOR_WS/proposals/invite-x/recipient-reference.json"; ok e-import-roomx
xcap=$(jq -r .observeCapability "$EW/refs/roomx.json")
for pair in target:$target srcx:$srcx qdoc:$qdoc srcy:$srcy; do
  run "e-import-${pair%%:*}" "$MINI" workspace --action import --dir "$EW" --name "${pair%%:*}" --kind object \
    --target "${pair##*:}" --observe-capability "$xcap"; ok "e-import-${pair%%:*}"
done

view_pairs a-backlinks "$SPONSOR_WS" target doc-backlinks; ok a-backlinks
got=$(backlink_set "$SPONSOR_WS" a-backlinks)
row a-backlinks "srcx:9101 srcy:9201" "$got" "$(tail -1 "$D/a-backlinks.out")"
view_pairs e-backlinks "$EW" target doc-backlinks; ok e-backlinks
got=$(backlink_set "$EW" e-backlinks)
row e-backlinks "srcx:9101" "$got" "$(tail -1 "$D/e-backlinks.out")"
row e-not-srcy absent "$(grep -q "$srcy\|^srcy " "$D/e-backlinks.out" && echo present || echo absent)" \
  "srcy's cell id $srcy in E's view"
o=$(oracle a "$SPONSOR_WS" "$target"); v=$(backlink_set "$SPONSOR_WS" a-backlinks)
row oracle-a "$o" "$v" "fold over A's readable pages vs the view"
o=$(oracle e "$EW" "$target"); v=$(backlink_set "$EW" e-backlinks)
row oracle-e "$o" "$v" "fold over E's readable pages vs the view ($(cat "$D/oracle-e-srcy.rc" 2>/dev/null) = E's srcy read rc)"

# Control: A delegates srcy (observe) to E; the same reader now sees srcy's link.
jq -n --arg r "$E_SUBJECT" '{type:"minidregg-workspace-proposal-v1",action:"delegate",name:"srcy",
  recipient:$r,verbs:["observe"],maxCost:"50000"}' >"$D/req/grant-srcy.json"
publish grant-srcy "$SPONSOR_WS" "$D/req/grant-srcy.json"
rm -f "$EW/refs/srcy.json"
run e-import-srcy2 "$MINI" workspace --action import --dir "$EW" --name srcy \
  --from-ref "$SPONSOR_WS/proposals/grant-srcy/recipient-reference.json"; ok e-import-srcy2
view_pairs e-backlinks2 "$EW" target doc-backlinks; ok e-backlinks2
got=$(backlink_set "$EW" e-backlinks2)
row e-after-grant "srcx:9101 srcy:9201" "$got" "after the srcy delegation"
o=$(oracle e2 "$EW" "$target")
row oracle-e2 "$o" "$got" "fold vs view after the delegation"

# (K-DOC-INDEX's quote row is gone with `quote`: a transclusion's forward link
# targets the transclusion, and backlinks of its source document do not yet
# include it -- cv 01a0f612-7abd. The link-kind mark row of J12M is the
# non-plain-relation backlink on this tree.)
view_pairs srcx-forward "$SPONSOR_WS" srcx doc-links; ok srcx-forward
got=$(grep -c '^link ' "$D/srcx-forward.out")
row srcx-forward "1:target" "$got:$(grep '^link ' "$D/srcx-forward.out" | awk '{print $5}')" "$(head -2 "$D/srcx-forward.out" | tail -1)"

# Unlink: srcx's link is tombstoned; it leaves every view.
invoke unlink "$SPONSOR_WS" srcx '[{"type":"unlink","link":"9101"}]'
row unlink installed "$(outcome unlink)" "$(tail -1 "$D/unlink.err" | cut -c1-160)"
view_pairs a-backlinks3 "$SPONSOR_WS" target doc-backlinks; ok a-backlinks3
view_pairs e-backlinks3 "$EW" target doc-backlinks; ok e-backlinks3
view_pairs srcx-forward2 "$SPONSOR_WS" srcx doc-links; ok srcx-forward2
got="$(backlink_set "$SPONSOR_WS" a-backlinks3)|$(backlink_set "$EW" e-backlinks3)|$(grep -c '^link ' "$D/srcx-forward2.out")"
row unlink-gone "srcy:9201|srcy:9201|0" "$got" "A | E | srcx's forward links"
o=$(oracle a2 "$SPONSOR_WS" "$target")
row oracle-a2 "$o" "$(backlink_set "$SPONSOR_WS" a-backlinks3)" "fold vs view after the unlink"

# Every query is answered by a cold open of the Store. Push the log past the
# next checkpoint (cadence 64) with unrelated writes, read the view again and
# compare it; the operator's checkpoint+suffix index must equal audit's
# genesis replay.
n=0
while :; do
  run probe-height "$HOST" "$CONFIG" link-index; ok probe-height
  base=$(head -1 "$D/probe-height.out" | sed -n 's/.*from the checkpoint at \([0-9]*\) .*/\1/p')
  [ "${base:-0}" -gt 0 ] && break
  n=$((n + 1)); [ "$n" -le 40 ] || { echo "no checkpoint after 40 writes" >&2; exit 1; }
  for k in 1 2 3 4 5; do
    invoke "fill-$n-$k" "$SPONSOR_WS" target "$(jq -n --arg a "$((5000 + n * 10 + k))" --arg t "$(hexof "fill $n $k")" \
      '[{type:"createAtom",atom:$a,kind:{type:"text"},payload:$t}]')"; ok "fill-$n-$k"
  done
done
view_pairs a-backlinks4 "$SPONSOR_WS" target doc-backlinks; ok a-backlinks4
same=$(diff <(grep -v '^# backlinks to' "$D/a-backlinks3.out") <(grep -v '^# backlinks to' "$D/a-backlinks4.out") >/dev/null && echo same || echo differ)
run link-index "$HOST" "$CONFIG" link-index; ok link-index
run audit "$HOST" "$CONFIG" audit
li=$(grep '^links ' "$D/link-index.out"); al=$(grep '^links ' "$D/audit.out")
ck=$(head -1 "$D/link-index.out" | sed -n 's/.*from the checkpoint at \([0-9]*\) .*/\1/p')
row reopen-identical "same:equal:resumed" "$same:$([ -n "$li" ] && [ "$li" = "$al" ] && echo equal || echo differs):$([ "${ck:-0}" -gt 0 ] && echo resumed || echo genesis)" \
  "$(head -1 "$D/link-index.out"); view before and after the fill identical but for its height line"
row audit re-admitted "$(grep -q "every signed ingress re-admitted" "$D/audit.out" && echo re-admitted || echo "rc=$(cat "$D/audit.rc")")" \
  "$(head -1 "$D/audit.out")"

cat "$rows" >&2
total=$(wc -l <"$rows")
[ "$bad" = 0 ] || { echo "$bad of $total link rows differ from expectation (see $rows)" >&2; exit 1; }
echo "$total/$total link rows as expected: backlinks from the Host's index, cut to the reader's readable sources, agreeing with the page fold; unlink and quote move the index; cold reopen and audit agree" >&2
echo "$rows"
