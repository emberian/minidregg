#!/bin/sh
# Signed Mini acceptance for two independently enrolled workroom members.
# This tests native kernel admission; it does not launch two grain controllers.
set -eu

if [ "$#" -ne 3 ]; then
  echo "usage: $0 MINIDREGG_HOST MEMBER_PROVISION_DIRECTORY NEW_EVIDENCE_DIRECTORY" >&2
  exit 2
fi
HOST=$1 PROVISION=$2 EVIDENCE=$3
MINI=${MINI:?set MINI to the source-matched native client}
[ -x "$HOST" ] && [ -x "$MINI" ] && [ -d "$PROVISION" ] || exit 2
RESUME=${WORKROOM_RESUME:-fresh}
case "$RESUME" in fresh|stale|split) ;; *) echo "invalid resume mode" >&2; exit 2 ;; esac
command -v jq >/dev/null 2>&1 || exit 2
if [ "$RESUME" = stale ]; then
  [ -d "$EVIDENCE" ] && [ -s "$EVIDENCE/member-stale-attempt/signed-observation.bin" ] &&
    [ ! -e "$EVIDENCE/member-stale-attempt/call.bin" ] || {
      echo "resume requires the retained preflight stale refusal" >&2; exit 2;
    }
elif [ "$RESUME" = split ]; then
  [ -d "$EVIDENCE" ] &&
    jq -e '.type == "confirmed" and .confirmation == "installed" and
      .acceptedCount == "11"' "$EVIDENCE/member-edit-split-attempt/outcome.json" >/dev/null || {
      echo "split resume requires the confirmed member edit" >&2; exit 2;
    }
else
  [ ! -e "$EVIDENCE" ] || { echo "refusing existing evidence directory" >&2; exit 2; }
  mkdir -m 700 "$EVIDENCE"
fi
EVIDENCE=$(CDPATH='' cd -- "$EVIDENCE" && pwd)
PROVISION=$(CDPATH='' cd -- "$PROVISION" && pwd)
CONFIG=$PROVISION/deployment/pinned-config.json
OWNER_KEY=$PROVISION/controller.key
FIRST_KEY=$PROVISION/tool.key
SECOND_KEY=$PROVISION/member.key
for item in "$CONFIG" "$OWNER_KEY" "$FIRST_KEY" "$SECOND_KEY"; do
  [ -f "$item" ] || { echo "missing provision artifact: $item" >&2; exit 2; }
done
SESSION_DIR=$EVIDENCE/session
if [ "$RESUME" = stale ]; then SESSION_DIR=$EVIDENCE/session-resume; fi
if [ "$RESUME" = split ]; then SESSION_DIR=$EVIDENCE/session-split; fi
mkdir -m 700 "$SESSION_DIR"
SOCKET=$SESSION_DIR/host.sock
"$MINI" serve --host "$HOST" --config "$CONFIG" --socket "$SOCKET" \
  >"$SESSION_DIR/mini.stdout" 2>"$SESSION_DIR/mini.stderr" &
SERVICE_PID=$!
cleanup() { kill "$SERVICE_PID" 2>/dev/null || :; wait "$SERVICE_PID" 2>/dev/null || :; }
trap cleanup EXIT HUP INT TERM
tick=0
until [ -S "$SOCKET" ]; do
  kill -0 "$SERVICE_PID" 2>/dev/null || { echo "Mini session failed" >&2; exit 1; }
  tick=$((tick + 1)); [ "$tick" -lt 120 ] || exit 1; sleep 1
done

confirmed() {
  jq -e '.type == "confirmed" and .confirmation == "installed" and
    (.acceptedCount | type == "string" and test("^[1-9][0-9]*$"))' "$1" >/dev/null
}
refused() {
  jq -e '.type == "refused" and (.phase | type == "string" and test("^[0-9a-f]+$")) and
    (.detail | type == "string" and test("^[0-9a-f]+$"))' "$1" >/dev/null
}
reason_hex() { printf '%s' "$1" | od -An -tx1 -v | tr -d ' \n'; }
assert_refusal_reason() {
  label=$1 reason=$2
  encoded=$(reason_hex "$reason")
  if [ -f "$EVIDENCE/$label-attempt/outcome.json" ]; then
    jq -er '.detail' "$EVIDENCE/$label-attempt/outcome.json" | grep -Fq "$encoded"
  else
    grep -Fq "$encoded" "$EVIDENCE/$label.stderr"
  fi || { echo "wrong native refusal for $label: expected $reason" >&2; exit 1; }
}
query() {
  label=$1 subject=$2 target=$3 capability=$4 key=$5 nonce=$6
  jq -n --arg subject "$subject" --arg target "$target" --arg capability "$capability" \
    --arg nonce "$nonce" \
    '{subject:$subject,nonce:$nonce,purpose:{type:"query",kind:"object",target:$target,
      view:"resource"},grants:[{kind:"object",target:$target,capability:$capability}]}' \
    >"$EVIDENCE/$label-intent.json"
  "$MINI" query --host "$HOST" --config "$CONFIG" --socket "$SOCKET" \
    --intent "$EVIDENCE/$label-intent.json" --key "$key" --view resource \
    --dir "$EVIDENCE/$label" >"$EVIDENCE/$label.stdout"
}
deny_query() {
  label=$1 subject=$2 target=$3 capability=$4 key=$5 nonce=$6
  jq -n --arg subject "$subject" --arg target "$target" --arg capability "$capability" \
    --arg nonce "$nonce" \
    '{subject:$subject,nonce:$nonce,purpose:{type:"query",kind:"object",target:$target,
      view:"resource"},grants:[{kind:"object",target:$target,capability:$capability}]}' \
    >"$EVIDENCE/$label-intent.json"
  if "$MINI" query --host "$HOST" --config "$CONFIG" --socket "$SOCKET" \
    --intent "$EVIDENCE/$label-intent.json" --key "$key" --view resource \
    --dir "$EVIDENCE/$label" >"$EVIDENCE/$label.stdout" 2>"$EVIDENCE/$label.stderr"; then
    echo "unauthorized query succeeded: $label" >&2; exit 1
  fi
  [ -s "$EVIDENCE/$label/signed-observation.bin" ] &&
    [ ! -e "$EVIDENCE/$label/view.json" ] &&
    grep -Fq 'host refused query' "$EVIDENCE/$label.stderr" &&
    grep -Fq "$(reason_hex 'observation refused')" "$EVIDENCE/$label.stderr" || {
      echo "denial lacked native observation refusal: $label" >&2; exit 1;
    }
}
submit() {
  label=$1 key=$2
  "$MINI" submit --host "$HOST" --config "$CONFIG" --socket "$SOCKET" \
    --intent "$EVIDENCE/$label-intent.json" --key "$key" \
    --dir "$EVIDENCE/$label-attempt" >"$EVIDENCE/$label.stdout"
  confirmed "$EVIDENCE/$label-attempt/outcome.json"
}
deny_submit() {
  label=$1 key=$2 expected=$3
  if "$MINI" submit --host "$HOST" --config "$CONFIG" --socket "$SOCKET" \
    --intent "$EVIDENCE/$label-intent.json" --key "$key" \
    --dir "$EVIDENCE/$label-attempt" >"$EVIDENCE/$label.stdout" 2>"$EVIDENCE/$label.stderr"; then
    echo "unauthorized mutation succeeded: $label" >&2; exit 1
  fi
  if [ -f "$EVIDENCE/$label-attempt/outcome.json" ]; then
    refused "$EVIDENCE/$label-attempt/outcome.json"
  else
    # A stale observation or revoked grant can be refused during Lean prepare,
    # before the host creates a call or outcome. Preserve that signed boundary.
    [ -s "$EVIDENCE/$label-attempt/signed-observation.bin" ] &&
      [ ! -e "$EVIDENCE/$label-attempt/call.bin" ] &&
      grep -q 'host refused prepare' "$EVIDENCE/$label.stderr" || {
        echo "denial lacked native prepare evidence: $label" >&2; exit 1;
      }
  fi
  assert_refusal_reason "$label" "$expected"
}
delegate() {
  label=$1 child=$2 verb=$3 query_label=$4 nonce=$5
  root=$(jq -er '.cell.root' "$EVIDENCE/$query_label/view.json")
  authority=$(jq -er '.authorityRoot' "$EVIDENCE/$query_label/challenge.json")
  jq -n --arg root "$root" --arg authority "$authority" --arg child "$child" \
    --arg verb "$verb" --arg nonce "$nonce" \
    '{subject:"7",nonce:$nonce,purpose:{type:"prepare",draft:{type:"delegate-source",
      command:{kind:"object",domain:"8501",semantics:env.WORKROOM_SEMANTICS,
        subject:"7",nonce:($nonce + "1"),expectedTargetRoot:$root,parentId:"89",
        target:"8001",
        child:{id:$child,root:"89",parent:"89",issuer:"5",
          holder:{type:"subject",subject:"9"},targets:["8001"],
          verbs:(if $verb == "both" then ["observe","mutate"] else [$verb] end),
          maxCost:"50000",notBefore:"10",notAfter:"1000",
          issuerEpoch:"2",policyId:"8001",policyEpoch:"0",ancestors:["89"],channels:[]}}}},
      grants:[{kind:"object",target:"8001",capability:"89"}]}' \
    >"$EVIDENCE/$label-intent.json"
  submit "$label" "$OWNER_KEY"
}
make_edit() {
  label=$1 subject=$2 capability=$3 observed=$4 payload=$5 nonce=$6
  jq -n --slurpfile view "$EVIDENCE/$observed/view.json" \
    --slurpfile challenge "$EVIDENCE/$observed/challenge.json" \
    --arg subject "$subject" --arg capability "$capability" \
    --arg payload "$payload" --arg nonce "$nonce" \
    '{subject:$subject,nonce:$nonce,purpose:{type:"prepare",draft:{type:"invoke",
      command:{subject:$subject,
        nonce:($nonce + "1"),targets:[{kind:"object",target:"8001",
          capability:$capability,
          observeCapability:(if $subject == "9" then "98" else null end),
          schemaVersion:"1",
          expectedTargetRoot:$view[0].cell.root,
          payload:{type:"content",actions:[{type:"editAtom",atom:"7401",
            before:($view[0].cell.entries[0] |
              {document,kind,payload,createdBy,createdAt,tombstonedAt}),
            kind:{type:"text"},payload:$payload,tombstone:false}]}}]}}},
      grants:[{kind:"object",target:"8001",
        capability:(if $subject == "9" then "98" else $capability end)}]}' \
    >"$EVIDENCE/$label-intent.json"
}
hex_text() { printf '%s' "$1" | od -An -tx1 -v | tr -d ' \n'; }

# Member 8 creates the first note; member 9 reads it while member 8 replaces
# the observed atom. Member 9's old observed edit must refuse before reread.
initial=$(hex_text 'Shared workroom: member eight opened this note.')
second=$(hex_text 'Member eight revised the shared note.')
third=$(hex_text 'Member nine reconciled the newer note.')
fourth=$(hex_text 'Member eight reviewed the joint workroom note.')
if [ "$RESUME" = fresh ]; then
WORKROOM_SEMANTICS=$(jq -er '.semantics' "$PROVISION/operator-profile.json")
export WORKROOM_SEMANTICS
query owner-before 7 8001 89 "$OWNER_KEY" 60001
delegate member-mutate 97 mutate owner-before 60002
query owner-after-mutate 7 8001 89 "$OWNER_KEY" 60004
delegate member-read 98 observe owner-after-mutate 60005
query member-before 9 8001 98 "$SECOND_KEY" 60007
query first-before 8 8001 96 "$FIRST_KEY" 60008
test "$(jq -er '.cell.root' "$EVIDENCE/member-before/view.json")" = \
  "$(jq -er '.cell.root' "$EVIDENCE/first-before/view.json")"
deny_query member-unrelated 9 7003 98 "$SECOND_KEY" 60009
deny_query first-unrelated 8 "${WORKROOM_MEMBER_TASK:-7503}" 96 "$FIRST_KEY" 60010

jq -n --slurpfile view "$EVIDENCE/first-before/view.json" \
  --slurpfile challenge "$EVIDENCE/first-before/challenge.json" \
  --arg payload "$initial" \
  '{subject:"8",nonce:"60100",purpose:{type:"prepare",draft:{type:"invoke",
    command:{subject:"8",
      nonce:"60101",targets:[{kind:"object",target:"8001",capability:"95",
        observeCapability:null,schemaVersion:"1",expectedTargetRoot:$view[0].cell.root,
        payload:{type:"content",actions:[{type:"createAtom",atom:"7401",
          kind:{type:"text"},payload:$payload}]}}]}}},
    grants:[{kind:"object",target:"8001",capability:"95"}]}' \
  >"$EVIDENCE/first-create-intent.json"
submit first-create "$FIRST_KEY"
query member-observed 9 8001 98 "$SECOND_KEY" 60102
query first-observed 8 8001 96 "$FIRST_KEY" 60103
make_edit first-edit 8 95 first-observed "$second" 60104
submit first-edit "$FIRST_KEY"
query after-first-edit 8 8001 96 "$FIRST_KEY" 60106
make_edit member-stale 9 97 member-observed "$third" 60107
deny_submit member-stale "$SECOND_KEY" 'Minidregg.Kernel.DeclaredResourceController.Reject.staleTarget'
fi
if [ "$RESUME" != split ]; then
query after-stale 9 8001 98 "$SECOND_KEY" 60109
test "$(jq -er '.cell.root' "$EVIDENCE/after-stale/view.json")" = \
  "$(jq -er '.cell.root' "$EVIDENCE/after-first-edit/view.json")"
fi
if [ "$RESUME" != split ]; then
make_edit member-edit 9 97 after-stale "$third" 60110
submit member-edit "$SECOND_KEY"
fi
query first-sees-member 8 8001 96 "$FIRST_KEY" 60112
make_edit first-edit-again 8 95 first-sees-member "$fourth" 60113
submit first-edit-again "$FIRST_KEY"
query member-sees-final 9 8001 98 "$SECOND_KEY" 60115
jq -e --arg payload "$fourth" '.cell.entries | length == 1 and
  .[0].type == "atom" and .[0].kind.type == "text" and .[0].payload == $payload' \
  "$EVIDENCE/member-sees-final/view.json" >/dev/null

# Revoke both of member 9's narrowly scoped grants. Current signed owner
# observations supply the target and authority roots for each source command.
revoke() {
  label=$1 child=$2 observed=$3 nonce=$4
  root=$(jq -er '.cell.root' "$EVIDENCE/$observed/view.json")
  authority=$(jq -er '.authorityRoot' "$EVIDENCE/$observed/challenge.json")
  jq -n --arg child "$child" --arg root "$root" --arg authority "$authority" \
    --arg nonce "$nonce" \
    '{subject:"7",nonce:$nonce,purpose:{type:"prepare",draft:{type:"revoke-source",
      command:{kind:"object",subject:"7",nonce:($nonce + "1"),target:"8001",
        victimKind:"object",capability:$child,controlCapability:"90",
        expectedTargetRoot:$root,expectedAuthorityRoot:$authority}}},
      grants:[{kind:"object",target:"8001",capability:"89"}]}' \
    >"$EVIDENCE/$label-intent.json"
  submit "$label" "$OWNER_KEY"
}
query owner-before-revoke 7 8001 89 "$OWNER_KEY" 60116
revoke revoke-member-mutate 97 owner-before-revoke 60117
query owner-mid-revoke 7 8001 89 "$OWNER_KEY" 60119
revoke revoke-member-read 98 owner-mid-revoke 60120
deny_query member-revoked-read 9 8001 98 "$SECOND_KEY" 60122
query owner-after-revoke 7 8001 89 "$OWNER_KEY" 60126
# Use the owner's fresh signed page and authority root, so this next-action
# refusal tests revoked member authority rather than an accidentally stale root.
make_edit member-revoked-edit 9 97 owner-after-revoke "$third" 60123
deny_submit member-revoked-edit "$SECOND_KEY" 'observation refused'
query first-after-revoke 8 8001 96 "$FIRST_KEY" 60125
test "$(jq -er '.cell.root' "$EVIDENCE/first-after-revoke/view.json")" = \
  "$(jq -er '.cell.root' "$EVIDENCE/owner-after-revoke/view.json")"
printf '%s\n' "$EVIDENCE/owner-after-revoke/view.json"
