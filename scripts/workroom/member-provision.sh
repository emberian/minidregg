#!/bin/sh
# Fresh two-member fixture. The reviewed single-member provisioner is overlaid
# in a private temporary copy; neither its source nor an active Store changes.
set -eu

if [ "$#" -ne 2 ]; then
  echo "usage: $0 MINIDREGG_HOST NEW_EVIDENCE_DIRECTORY" >&2
  exit 2
fi
HERE=$(CDPATH='' cd -- "$(dirname -- "$0")" && pwd)
BASE=$HERE/provision.sh
EXPECTED=202a6ee4495ed46c474e2a965b258b6f2a4a94412d58f2319c69e9c8c35bd1cb
ACTUAL=$(sha256sum "$BASE" | cut -d' ' -f1)
[ "$ACTUAL" = "$EXPECTED" ] || {
  echo "reviewed provisioner changed; inspect before updating member overlay" >&2
  exit 2
}
case "${WORKROOM_MEMBER_TASK:-7503}" in
  ''|0*|*[!0-9]*|7|8|10|11|12|7003|8001) echo "invalid member task" >&2; exit 2 ;;
esac
WORKROOM_MEMBER_TASK=${WORKROOM_MEMBER_TASK:-7503}
[ "$WORKROOM_MEMBER_TASK" != "${WORKROOM_PARENT_TASK:-7101}" ] &&
  [ "$WORKROOM_MEMBER_TASK" != "${WORKROOM_TOOL_TASK:-7102}" ] || {
    echo "member task collides with parent/tool task" >&2; exit 2;
  }
STAGE=$(mktemp -d)
trap 'rm -rf "$STAGE"' EXIT HUP INT TERM
cat >"$STAGE/preboot" <<'EOF'
"$MINI" keygen --secret "$EVIDENCE/member.key" --public "$EVIDENCE/member.pub" >"$EVIDENCE/member-public.txt"
MEMBER_PUBLIC=$(od -An -tx1 -v "$EVIDENCE/member.pub" | tr -d ' \n')
test "$MEMBER_PUBLIC" != "$CONTROLLER_PUBLIC"
test "$MEMBER_PUBLIC" != "$TOOL_PUBLIC"
jq --arg public "$MEMBER_PUBLIC" '.enrollments += [{
  key:{keyId:"9009",keyEpoch:"2",algorithm:"1",subject:"9",
    publicKey:$public,activeFrom:"0",activeUntil:"1000000",nextKeyDigest:null},
  accountId:"9",spendCapabilityId:"43",controlCapabilityId:"56",
  factoryObserveCapabilityId:"57",initialBalance:"100",
  accountPredicate:{type:"all",predicates:[]}}]' \
  "$EVIDENCE/genesis.json" >"$EVIDENCE/genesis-with-member.json"
mv "$EVIDENCE/genesis-with-member.json" "$EVIDENCE/genesis.json"
EOF
cat >"$STAGE/prebirth" <<'EOF'
jq --arg member_task "$WORKROOM_MEMBER_TASK" \
  '.birth.resources += [{kind:"object",storage:"grain",target:$member_task,
    owner:"9",ownerCapability:"83",controlCapability:"84",budget:"50"}]' \
  "$EVIDENCE/birth-intent.json" >"$EVIDENCE/birth-with-member.json"
mv "$EVIDENCE/birth-with-member.json" "$EVIDENCE/birth-intent.json"
EOF
awk -v preboot="$STAGE/preboot" -v prebirth="$STAGE/prebirth" '
  /^"\$MINI" bootstrap --host / {
    while ((getline inserted < preboot) > 0) print inserted
    close(preboot); boot++
  }
  /cat >"\$EVIDENCE\/birth-intent.json" <<EOF/ { seen_birth=1 }
  seen_birth && /^"\$MINI" submit --host / && !birth_inserted {
    while ((getline inserted < prebirth) > 0) print inserted
    close(prebirth); birth_inserted++
  }
  { print }
  END { if (boot != 1 || birth_inserted != 1) exit 2 }
' "$BASE" >"$STAGE/provision.sh"
chmod 700 "$STAGE/provision.sh"

export WORKROOM_MEMBER_TASK
"$STAGE/provision.sh" "$1" "$2"

# Independently exercise the new subject's enrolled key and born grain.
EVIDENCE=$(CDPATH='' cd -- "$2" && pwd)
MINI=${MINI:?set MINI to the source-matched native client}
jq -n --arg task "$WORKROOM_MEMBER_TASK" \
  '{subject:"9",nonce:"31990",purpose:{type:"query",kind:"object",target:$task,
    view:"resource"},grants:[{kind:"object",target:$task,capability:"83"}]}' \
  >"$EVIDENCE/member-born-intent.json"
"$MINI" query --host "$1" --config "$EVIDENCE/deployment/pinned-config.json" \
  --intent "$EVIDENCE/member-born-intent.json" --key "$EVIDENCE/member.key" \
  --view resource --dir "$EVIDENCE/member-born" >"$EVIDENCE/member-born.stdout"
jq -e --arg task "$WORKROOM_MEMBER_TASK" \
  '.cell.grain == {task:$task,generation:"0",status:"0",remaining:"50",reserved:"0"}' \
  "$EVIDENCE/member-born/view.json" >/dev/null
printf '%s\n' "$EVIDENCE/member-born/view.json"
