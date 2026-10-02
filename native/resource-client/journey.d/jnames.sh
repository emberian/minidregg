#!/usr/bin/env bash
# J-NAMES: two existing enrolled participants share only a room invitation.
# Run on a NEW world whose room template declares field1010 and whose source
# profile includes content/names/unique. Never expands an old room's fields.
# Hook inputs match journey.sh; requires J4's newcomer workspace.
set -euo pipefail
umask 077
: "${JOURNEY_STEP_DIR:?}" "${MINI:?}" "${HOST:?}" "${CONFIG:?}" "${SOCKET:?}" "${SPONSOR_WS:?}" "${NEWCOMER_WS:?}"
D=$JOURNEY_STEP_DIR
mkdir -p "$D/a/requests" "$D/b/requests" "$D/log"
N=0
printf 'step\tresult\n' >"$D/names.tsv"
run() {
  local who=$1 line=$2 ws home
  N=$((N+1)); ws=$SPONSOR_WS; home=$D/a
  if [[ $who == b ]]; then ws=$NEWCOMER_WS; home=$D/b; fi
  printf '%s\n' "$line" >"$D/log/$N.line"
  "$MINI" shell --socket "$SOCKET" --host "$HOST" --config "$CONFIG" \
    --workspace "$ws" --home "$home" --line "$line" >"$D/log/$N.out" 2>"$D/log/$N.err"
}
ok() { run "$@"; printf '%s\tok\n' "$2" >>"$D/names.tsv"; }
refused() {
  local pattern=$3 rc=0
  run "$1" "$2" || rc=$?
  [[ $rc != 0 ]] && grep -Eiq "$pattern" "$D/log/$N.err"
  printf '%s\trefused\n' "$2" >>"$D/names.tsv"
}
expect_target() {
  run "$1" "room resolve $2"
  [[ $(jq -er '.target' "$D/log/$N.out") == "$3" ]]
}
B=$(jq -er '.subject' "$NEWCOMER_WS/workspace.json")
"$MINI" workspace --action index-law --dir "$SPONSOR_WS" >"$D/index-law.json"
printf '%s\n' '{"type":"all","predicates":[]}' >"$D/a/requests/open.json"
ok a 'room new nameslab'
"$MINI" workspace --action doc-new --dir "$SPONSOR_WS" --name namesmap \
  --predicate "$D/index-law.json" --in nameslab >"$D/index-birth.out" 2>"$D/index-birth.err"
ok a 'doc new namesboard --in nameslab'
ok a 'doc new namesoutside'
ok a 'room index names-attach nameslab namesmap'
ok a 'room bind names-bind nameslab board namesboard'
TARGET=$(jq -er '.target' "$SPONSOR_WS/refs/namesboard.json")
ok a "room invite names-invite nameslab $B --verbs observe,mutate"
ok a 'submit names-invite'
ok a 'publish names-invite'
"$MINI" workspace --action import --dir "$NEWCOMER_WS" --name nameslab \
  --from-ref "$SPONSOR_WS/proposals/names-invite/recipient-reference.json" >"$D/import.out" 2>"$D/import.err"
[[ ! -e $NEWCOMER_WS/refs/nameslab.board.json ]]
expect_target a nameslab/board "$TARGET"
expect_target b nameslab/board "$TARGET"
ok b 'doc show nameslab/board'
ok b 'doc show nameslab/index --json'
jq -e '.sharedNames | any(.name=="board")' "$D/log/$N.out" >/dev/null
refused a 'room bind names-duplicate nameslab board namesboard' 'lawDenied|law-denied'
ok a 'room rename names-rename nameslab board current'
expect_target a nameslab/current "$TARGET"
expect_target b nameslab/current "$TARGET"
refused b 'room resolve nameslab/board' 'cannot inspect|no.*reference'
# Rename again, then repeat the FIRST command. Its exact receipt must be
# recovered without changing current names or resolving its old spelling.
ok a 'room rename names-rename-again nameslab current again'
sha256sum "$SPONSOR_WS/attempts/names-rename/call.bin" >"$D/rename-before.sha256"
ok a 'room rename names-rename nameslab board current'
sha256sum --check "$D/rename-before.sha256" >/dev/null
expect_target b nameslab/again "$TARGET"
refused b 'room resolve nameslab/current' 'cannot inspect|no.*reference'
# A shared binding conveys a name, never a new capability to its target.
ok a 'room bind names-outside nameslab outside namesoutside'
refused b 'doc show nameslab/outside' 'grant|scope|capability|authority'
# A maliciously re-lawed index can contain duplicates. A receiving client
# must reject ambiguity independently, rather than choose the first link.
ok a 'law names-open namesmap @open.json'
ok a 'submit names-open'
ok a 'room bind names-ambiguous nameslab again namesoutside'
refused b 'room resolve nameslab/again' 'ambiguous duplicate'
printf 'JNAMES: two-client lookup, rename, exact retry, duplicate-law refusal, target authority and ambiguous-index refusal passed\n' >&2
printf '%s\n' "$D/names.tsv"
