#!/usr/bin/env bash
# journey.d/j10-kernel.sh — rooms in the world (K-ROOM 3b), on the journey's
# fresh Store, after J5 (which enrolled the third key and its workspace).
#
# A (the sponsor) creates the room `lab`, then `note` born `--in lab` (raw
# `workspace create --in`; the shell verb is 3c's). A's owner capability on a
# workspace resource is `under` it, so it already reaches `note`. A invites B
# (the newcomer) with a room delegation (`"room": true`: the child is `under lab`).
# Rows:
#   a-reads-note-via-lab    A's `lab` capability reads `note`           -> read
#   b-reads-lab             B's invite covers the room cell itself      -> read
#   b-reads-note            B's invite covers `note` (parent chain)     -> read
#   b-reads-outside         B's invite does not cover a root cell       -> refused
#   third-reads-note-child  the third key presents B's invite           -> refused
#   third-reads-note-owner  the third key presents A's room capability  -> refused
#   b-signature-only        B signs a read of `note` naming no stored capability -> refused
#   create-in-ghost         a birth into a room that does not exist     -> refused
# Exported by the journey: MINI SOCKET SPONSOR_WS NEWCOMER_WS NEWCOMER_SUBJECT
# JOURNEY_WORLD JOURNEY_STEP_DIR. Exit 0 = every row as expected. Last stdout
# line = the rows file.
set -uo pipefail
D=$JOURNEY_STEP_DIR
W=$JOURNEY_WORLD
TW=$W/third-workspace
mkdir -p "$D/req"
rows=$D/room-rows.tsv
: >"$rows"
bad=0
REFUSAL_TAG=44524547472f4e41544956452d484f53542f4f5554434f4d45

run() { # NAME cmd...
  local name=$1; shift
  "$@" >"$D/$name.out" 2>"$D/$name.err"; echo $? >"$D/$name.rc"
}
host_refused() {
  [ "$(cat "$D/$1.rc")" != 0 ] && grep -q "encoded refusal: $REFUSAL_TAG" "$D/$1.err"
}
refusal_text() {
  grep -o 'encoded refusal: [0-9a-f]*' "$D/$1.err" | tail -1 | cut -d' ' -f3 | xxd -r -p 2>/dev/null \
    | tr -c '[:print:]' ' ' | tr -s ' ' | cut -c1-160
}
row() { # NAME EXPECT(read|installed|refused)
  local name=$1 expect=$2 got
  if [ "$(cat "$D/$name.rc")" = 0 ]; then got=$expect; [ "$expect" = refused ] && got=ACCEPTED
  elif host_refused "$name"; then got=refused
  else got="client-error"
  fi
  local detail
  detail=$([ "$got" = refused ] && refusal_text "$name" || tail -1 "$D/$name.err" | cut -c1-160)
  printf '%s\texpect=%s\tgot=%s\t%s\n' "$name" "$expect" "$got" "$detail" >>"$rows"
  [ "$got" = "$expect" ] || bad=$((bad + 1))
}
must() { "$@" || { echo "setup failed: $*" >&2; exit 1; }; }
ok() { # NAME
  [ "$(cat "$D/$1.rc")" = 0 ] || { echo "setup $1 failed: $(tail -1 "$D/$1.err")" >&2; exit 1; }
}

printf '%s\n' '{"type":"all","predicates":[]}' >"$D/req/permit-all.json"

# The room and a note born in it.
run create-lab "$MINI" workspace --action create --dir "$SPONSOR_WS" --name lab --storage declared \
  --predicate "$D/req/permit-all.json"; ok create-lab
run create-note "$MINI" workspace --action create --dir "$SPONSOR_WS" --name note --storage declared \
  --predicate "$D/req/permit-all.json" --in lab; ok create-note
run create-outside "$MINI" workspace --action create --dir "$SPONSOR_WS" --name outside --storage declared \
  --predicate "$D/req/permit-all.json"; ok create-outside
lab=$(jq -r .target "$SPONSOR_WS/refs/lab.json")
note=$(jq -r .target "$SPONSOR_WS/refs/note.json")
outside=$(jq -r .target "$SPONSOR_WS/refs/outside.json")
labcap=$(jq -r .observeCapability "$SPONSOR_WS/refs/lab.json")
jq -e --arg lab "$lab" '.birth.resources[0].room == $lab' "$SPONSOR_WS/sources/create-note.json" >/dev/null \
  || { echo "note's birth source does not name the room" >&2; exit 1; }

# A reads the note with its room capability.
run import-a-note "$MINI" workspace --action import --dir "$SPONSOR_WS" --name note-via-lab --kind object \
  --target "$note" --observe-capability "$labcap"; ok import-a-note
run a-reads-note-via-lab "$MINI" workspace --action read --dir "$SPONSOR_WS" --name note-via-lab
row a-reads-note-via-lab read

# The invite: a room delegation to B.
jq -n --arg r "$NEWCOMER_SUBJECT" '{type:"minidregg-workspace-proposal-v1",action:"delegate",name:"lab",
  recipient:$r,verbs:["observe"],maxCost:"50000",room:true}' >"$D/req/invite.json"
run invite-propose "$MINI" workspace --action propose --dir "$SPONSOR_WS" --request "$D/req/invite.json" \
  --proposal-id invite-b; ok invite-propose
jq -e --arg lab "$lab" '.purpose.draft.command.child.room == $lab and (.purpose.draft.command.child | has("targets") | not)' \
  "$SPONSOR_WS/proposals/invite-b/intent.json" >/dev/null || { echo "invite child is not under lab" >&2; exit 1; }
run invite-submit "$MINI" workspace --action submit --dir "$SPONSOR_WS" \
  --intent "$SPONSOR_WS/proposals/invite-b/intent.json" --attempt "$SPONSOR_WS/attempts/invite-b"; ok invite-submit
run invite-publish "$MINI" workspace --action publish-delegation --dir "$SPONSOR_WS" --proposal-id invite-b \
  --attempt "$SPONSOR_WS/attempts/invite-b"; ok invite-publish
run b-import-lab "$MINI" workspace --action import --dir "$NEWCOMER_WS" --name lab \
  --from-ref "$SPONSOR_WS/proposals/invite-b/recipient-reference.json"; ok b-import-lab
child=$(jq -r .observeCapability "$NEWCOMER_WS/refs/lab.json")
run b-import-note "$MINI" workspace --action import --dir "$NEWCOMER_WS" --name note --kind object \
  --target "$note" --observe-capability "$child"; ok b-import-note
run b-import-outside "$MINI" workspace --action import --dir "$NEWCOMER_WS" --name outside --kind object \
  --target "$outside" --observe-capability "$child"; ok b-import-outside
run b-import-sigonly "$MINI" workspace --action import --dir "$NEWCOMER_WS" --name note-sigonly --kind object \
  --target "$note" --observe-capability 1; ok b-import-sigonly

run b-reads-lab "$MINI" workspace --action read --dir "$NEWCOMER_WS" --name lab
row b-reads-lab read
run b-reads-note "$MINI" workspace --action read --dir "$NEWCOMER_WS" --name note
row b-reads-note read
run b-reads-outside "$MINI" workspace --action read --dir "$NEWCOMER_WS" --name outside
row b-reads-outside refused
run b-signature-only "$MINI" workspace --action read --dir "$NEWCOMER_WS" --name note-sigonly
row b-signature-only refused

# The third key, holding no grant in the room's lineage.
run t-import-child "$MINI" workspace --action import --dir "$TW" --name note-child --kind object \
  --target "$note" --observe-capability "$child"; ok t-import-child
run t-import-owner "$MINI" workspace --action import --dir "$TW" --name note-owner --kind object \
  --target "$note" --observe-capability "$labcap"; ok t-import-owner
run third-reads-note-child "$MINI" workspace --action read --dir "$TW" --name note-child
row third-reads-note-child refused
run third-reads-note-owner "$MINI" workspace --action read --dir "$TW" --name note-owner
row third-reads-note-owner refused

# A birth into a room that does not exist.
run import-ghost "$MINI" workspace --action import --dir "$SPONSOR_WS" --name ghost --kind object \
  --target 999999937 --observe-capability "$labcap"; ok import-ghost
run create-in-ghost "$MINI" workspace --action create --dir "$SPONSOR_WS" --name orphan --storage declared \
  --predicate "$D/req/permit-all.json" --in ghost
row create-in-ghost refused

cat "$rows" >&2
[ "$bad" = 0 ] || { echo "$bad room rows differ from expectation (see $rows)" >&2; exit 1; }
echo "8/8 room rows as expected: A and B read note and lab through under lab; outside, third key (both caps), signature-only and ghost-room birth refused" >&2
echo "$rows"
