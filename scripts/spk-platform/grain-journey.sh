#!/bin/sh
# One signed non-Git package (sntfy, root API prefix) installed, started,
# reached over HTTP, stopped and restarted on a fresh Store, then a second
# instance of the same package on the same host. Every lifecycle effect goes
# through `spk-host grain`; application, session, ticket and enrollment are
# ordinary Mini client operations. Nothing per instance is configured by hand:
# the only per-instance inputs are the resource coordinates of the ordinary
# births below.
#
#   grain-journey.sh all RUN_ROOT            fresh Store to second instance
#   grain-journey.sh phase RUN_ROOT NAME     one phase against RUN_ROOT
#   grain-journey.sh stop-services RUN_ROOT  stop the Store services
#
# Runs as root on a grain host (see grain-store.sh). Pins are environment:
#   BIN   directory holding minidregg-host-m6, mini, spk-host, helpers
#   SPK   the signed sntfy package
set -eu
umask 077

usage() { sed -n '2,17p' "$0" >&2; exit 2; }
[ "$#" -ge 2 ] || usage
MODE=$1 RUN=$2
shift 2
HERE=$(CDPATH='' cd -- "$(dirname -- "$0")" && pwd)
BIN=${BIN:-/opt/minidregg-m6-20260930/bin}
SPK=${SPK:-/home/ember/build/mini-product-20260930/m6-grain/inputs/sntfy.spk}
HOST=${GRAIN_HOST:-$BIN/minidregg-host-m6e}
MINI=$BIN/mini
SPK_HOST=$BIN/spk-host
BWRAP=${BWRAP:-/usr/bin/bwrap}
STORE=$RUN/store
WR=$STORE/base/workroom
CONFIG=$WR/deployment/pinned-config.json
PSOCK=$RUN/sock/participant/host.sock
OSOCK=$RUN/sock/operator/host.sock
PROFILE=$RUN/host/grain-host.json
EV=$RUN/evidence
UNIT_PREFIX=${UNIT_PREFIX:-mini-grain-$(basename "$RUN")}
# Resource coordinates: GRAIN_A/GRAIN_B are the two-digit prefixes of the
# app (NN01), session (NN10) and tickets (NN20, NN30).
A=${GRAIN_A:-91} B=${GRAIN_B:-92}

fail() { echo "grain journey: $*" >&2; exit 1; }
now() { date +%s.%N; }
sha() { sha256sum "$1" | cut -d ' ' -f 1; }
mkdir -p -m 700 "$EV"

# step NAME CMD...: run one step, keeping its exact command, stdout, stderr,
# exit status and wall time. The step's verdict is the command's exit.
step() {
  step_name=$1; shift
  printf '%s\n' "$*" >"$EV/$step_name.cmd"
  step_t0=$(now)
  set +e
  ("$@") >"$EV/$step_name.stdout" 2>"$EV/$step_name.stderr"
  step_rc=$?
  set -e
  step_t1=$(now)
  printf '%s\n' "$step_rc" >"$EV/$step_name.exit"
  echo "$step_t1 - $step_t0" | bc >"$EV/$step_name.seconds"
  printf '%-28s exit=%s %6ss\n' "$step_name" "$step_rc" "$(cat "$EV/$step_name.seconds")" |
    tee -a "$EV/journey.log"
  return "$step_rc"
}

confirmed() {
  jq -e '.type == "confirmed" and .confirmation == "installed" and
    (.acceptedCount | type == "string" and test("^[1-9][0-9]*$"))' "$1" >/dev/null
}

service_up() {
  unit=$1 socket=$2 mode=$3
  if [ "$(systemctl show "$unit" --property=ActiveState --value)" = active ]; then
    return 0
  fi
  systemctl reset-failed "$unit" 2>/dev/null || :
  mkdir -p -m 700 "${socket%/*}"
  systemd-run --unit="$unit" --property=Type=exec --property=KillMode=control-group \
    -- "$MINI" "$mode" --host "$HOST" --config "$CONFIG" --socket "$socket" >/dev/null
  tick=0
  until [ -S "$socket" ]; do
    [ "$(systemctl show "$unit" --property=ActiveState --value)" = active ] ||
      fail "$unit is not active"
    tick=$((tick + 1)); [ "$tick" -lt 600 ] || fail "$unit socket timeout"
    sleep 0.5
  done
}

services() {
  service_up "$UNIT_PREFIX-participant.service" "$PSOCK" serve
  service_up "$UNIT_PREFIX-operator.service" "$OSOCK" serve-operator
}

stop_services() {
  for unit in "$UNIT_PREFIX-participant.service" "$UNIT_PREFIX-operator.service"; do
    systemctl stop "$unit" 2>/dev/null || :
    systemctl reset-failed "$unit" 2>/dev/null || :
  done
}

query() (
  name=$1 subject=$2 task=$3 capability=$4 key=$5 nonce=$6 view=${7:-resource}
  jq -n --arg s "$subject" --arg t "$task" --arg c "$capability" --arg n "$nonce" \
    --arg v "$view" \
    '{subject:$s,nonce:$n,purpose:{type:"query",kind:"object",target:$t,view:$v},
      grants:[{kind:"object",target:$t,capability:$c}]}' >"$EV/$name-intent.json"
  rm -rf "$EV/$name"
  "$MINI" query --host "$HOST" --config "$CONFIG" --socket "$PSOCK" \
    --intent "$EV/$name-intent.json" --key "$key" --view "$view" \
    --dir "$EV/$name" >"$EV/$name.stdout"
)

grain_op() (
  name=$1 subject=$2 task=$3 cap=$4 key=$5 nonce=$6 operation=$7
  if [ -s "$EV/$name-attempt/outcome.json" ]; then
    confirmed "$EV/$name-attempt/outcome.json"; exit 0
  fi
  query "$name-before" "$subject" "$task" "$cap" "$key" "$((nonce + 1))"
  jq -n --arg task "$task" --arg subject "$subject" --arg cap "$cap" --arg nonce "$nonce" \
    --argjson operation "$operation" \
    --slurpfile read "$EV/$name-before/view.json" \
    --slurpfile challenge "$EV/$name-before/challenge.json" '
    {grain:{task:$task,subject:$subject,capability:$cap,observeCapability:$cap,
      schemaVersion:"1",expectedAuthorityRoot:$challenge[0].signing[0].authorityRoot,
      expectedTargetRoot:$read[0].page.root,
      context:{operationId:$nonce,payload:"grain journey workroom"},
      before:($read[0].page.grain | {generation,status,remaining,reserved}),
      operation:$operation,publications:[]},
     grants:[{kind:"object",target:$task,capability:$cap}],intentNonce:$nonce}' \
    >"$EV/$name-intent.json"
  "$MINI" submit --host "$HOST" --config "$CONFIG" --socket "$PSOCK" \
    --intent "$EV/$name-intent.json" --intent-kind grain-intent \
    --key "$key" --dir "$EV/$name-attempt" >"$EV/$name.stdout"
  confirmed "$EV/$name-attempt/outcome.json"
)

# The metered birth parent (7901, controller 7) must be reserved in its first
# generation and the tool (7902, subject 8) attached. Idempotent on state.
workroom_ready() {
  query parent-state 8 7901 73 "$WR/tool.key" 30001
  if ! jq -e '.page.grain.status == "3" and .page.grain.reserved == "1"' \
      "$EV/parent-state/view.json" >/dev/null; then
    grain_op parent-attach 7 7901 71 "$WR/controller.key" 30010 '{"type":"attach","soft":false}'
    grain_op parent-reserve 7 7901 71 "$WR/controller.key" 30020 '{"type":"reserve","amount":"1"}'
  fi
  query tool-state 8 7902 81 "$WR/tool.key" 30031
  if jq -e '.page.grain.status == "0"' "$EV/tool-state/view.json" >/dev/null; then
    grain_op tool-attach 8 7902 81 "$WR/tool.key" 30040 '{"type":"attach","soft":false}'
  fi
}

# birth NAME NONCE SPEC_FIELD INNER_FIELD AUTHOR_COMMAND SPEC_JSON
# Reserve metered tool units, then author and submit one current birth.
birth() (
  name=$1 nonce=$2 field=$3 inner=$4 command=$5 spec=$6
  if [ -s "$EV/$name-attempt/outcome.json" ]; then
    confirmed "$EV/$name-attempt/outcome.json"; exit 0
  fi
  [ ! -e "$EV/$name-attempt" ] || { echo "birth $name attempt is uncertain" >&2; exit 1; }
  grain_op "$name-reserve" 8 7902 81 "$WR/tool.key" "$nonce" '{"type":"reserve","amount":"5"}'
  query "$name-tool" 8 7902 81 "$WR/tool.key" "$((nonce + 101))"
  query "$name-parent" 8 7901 73 "$WR/tool.key" "$((nonce + 102))"
  jq -n --arg nonce "$((nonce + 100))" --arg field "$field" --arg inner "$inner" \
    --argjson spec "$spec" \
    --slurpfile genesis "$WR/genesis.json" \
    --slurpfile tool "$EV/$name-tool/view.json" \
    --slurpfile parent "$EV/$name-parent/view.json" \
    --slurpfile challenge "$EV/$name-tool/challenge.json" '
    {subject:"8",nonce:$nonce,
     grants:[{kind:"object",target:"10",capability:"55"},
       {kind:"account",target:"8",capability:"42"},
       {kind:"object",target:"7902",capability:"81"},
       {kind:"object",target:"7901",capability:"73"}]} +
    {($field):{tariff:{base:"2",perBirth:"1"},
      authorityRoot:$challenge[0].signing[0].authorityRoot,
      ($inner):({genesis:$genesis[0],template:{issuer:"5",ownerBudget:"100000",lifetime:"10000"},
        creator:"8",nonce:$nonce,sourceCapabilities:["42"],funding:[],feePayer:"8"} + $spec),
      tool:{task:"7902",capability:"81",observeCapability:"81",targetRoot:$tool[0].page.root,
        before:($tool[0].page.grain | {generation,status,remaining,reserved})},
      parent:{task:"7901",capability:"73",observeCapability:"73",targetRoot:$parent[0].page.root,
        before:($parent[0].page.grain | {generation,status,remaining,reserved})}}}' \
    >"$EV/$name-source.json"
  rm -rf "$EV/$name-author"
  "$MINI" "$command" --host "$HOST" --config "$CONFIG" --socket "$PSOCK" \
    --source "$EV/$name-source.json" --dir "$EV/$name-author" >"$EV/$name-author.stdout"
  "$MINI" submit --host "$HOST" --config "$CONFIG" --socket "$PSOCK" \
    --intent "$EV/$name-author/intent.bin" --intent-kind binary \
    --key "$WR/tool.key" --dir "$EV/$name-attempt" >"$EV/$name-submit.stdout"
  confirmed "$EV/$name-attempt/outcome.json"
)

# Ordinary application birth owned by the host management subject (8).
birth_app() (
  label=$1 nonce=$2 app=$3 cap=$4
  birth "$label-app" "$nonce" applicationGrainBirth applicationBirth \
    current-application-intent "$(jq -nc --arg a "$app" --arg c "$cap" '
      ($a|tonumber) as $n | ($c|tonumber) as $k |
      {application:{app:$a,packageManifest:(($n+1)|tostring),
        snapshotManifest:(($n+2)|tostring),owner:"8",
        appOwnerCapability:$c,appControlCapability:(($k+1)|tostring),
        packageOwnerCapability:(($k+2)|tostring),packageControlCapability:(($k+3)|tostring),
        snapshotOwnerCapability:(($k+4)|tostring),snapshotControlCapability:(($k+5)|tostring)}}')"
)

# Ordinary application session birth for participant subject 8.
birth_session() (
  label=$1 nonce=$2 app=$3 session=$4 kind=$5 cap=$6
  birth "$label-session" "$nonce" applicationSessionGrainBirth applicationSessionBirth \
    current-session-intent "$(jq -nc --arg a "$app" --arg s "$session" --arg k "$kind" \
      --arg c "$cap" '($s|tonumber) as $n | ($c|tonumber) as $m |
      {session:{app:$a,session:$s,descriptor:(($n+1)|tostring),participant:"8",kind:$k,
        sessionOwnerCapability:$c,sessionControlCapability:(($m+1)|tostring),
        descriptorOwnerCapability:(($m+2)|tostring),
        descriptorControlCapability:(($m+3)|tostring)}}')"
)

# Signed-slot approval: every slot must name a workroom key (8008 or 7007).
approve() (
  plan=$1 header=$2 out=$3 base=$4
  : >"$out.signers"
  count=$(jq -er '.slots | length' "$plan")
  index=0
  while [ "$index" -lt "$count" ]; do
    slot=$(jq -cer --argjson i "$index" '.slots[$i]' "$plan")
    case "$(printf '%s' "$slot" | jq -er .signing.keyId)" in
      8008) key=$WR/tool.key; public=$WR/tool.pub ;;
      7007) key=$WR/controller.key; public=$WR/controller.pub ;;
      *) echo "unexpected signer key" >&2; exit 1 ;;
    esac
    hsha=$(printf '%s' "$slot" | jq -er ".$header" | xxd -r -p | sha256sum | cut -d ' ' -f 1)
    printf '%s' "$slot" | jq -c --arg public "$(od -An -tx1 -v "$public" | tr -d ' \n')" \
      --arg h "$hsha" --arg key "$key" \
      '{role,index,keyId:.signing.keyId,keyEpoch:.signing.keyEpoch,
        publicKey:$public,headerSha256:$h,keyPath:$key}' >>"$out.signers"
    index=$((index + 1))
  done
  jq -s --argjson base "$base" '$base + {signers:.}' "$out.signers" >"$out"
  chmod 600 "$out"
)

# delegate_observe LABEL TARGET PARENT_CAP CHILD_CAP HOLDER NONCE: the owner of
# TARGET delegates an observe-only child capability (ordinary signed
# delegation). Event22 does not mint the participant's ticket observation.
delegate_observe() (
  label=$1 target=$2 parent=$3 child=$4 holder=$5 nonce=$6
  D=$EV/$label-delegate-$child
  if [ -s "$D-attempt/outcome.json" ]; then confirmed "$D-attempt/outcome.json"; exit 0; fi
  qcap() (
    name=$1 view=$2 n=$3
    jq -n --arg t "$target" --arg c "$parent" --arg n "$n" --arg v "$view" '
      {subject:"8",nonce:$n,purpose:{type:"query",kind:"object",target:$t,view:$v},
       grants:[{kind:"object",target:$t,capability:$c}]}' >"$D-$name-intent.json"
    rm -rf "$D-$name"
    "$MINI" query --host "$HOST" --config "$CONFIG" --socket "$PSOCK" \
      --intent "$D-$name-intent.json" --key "$WR/tool.key" --view "$view" \
      --dir "$D-$name" >"$D-$name.stdout"
  )
  qcap parent capability "$nonce"
  "$HOST" "$CONFIG" inspect view-object-capability "$D-parent/view.bin" "$D-parent/head.json"
  qcap owner resource "$((nonce + 1))"
  jq -n --slurpfile cap "$D-parent/head.json" --slurpfile current "$D-owner/challenge.json" \
    --slurpfile resource "$D-owner/view.json" --arg holder "$holder" --arg child "$child" \
    --arg target "$target" --arg nonce "$((nonce + 2))" --arg commandNonce "$((nonce + 3))" '
    $cap[0].head as $p | $current[0] as $c |
    {subject:"8",nonce:$nonce,purpose:{type:"prepare",draft:{type:"delegate-source",
      command:{kind:"object",domain:$c.domain,semantics:$c.semantics,subject:"8",nonce:$commandNonce,
        expectedTargetRoot:$resource[0].page.root,parentId:$p.id,target:$target,
        expectedPreRoot:$c.signing[0].authorityRoot,
        child:($p + {id:$child,parent:$p.id,holder:{type:"subject",subject:$holder},
          targets:[$target],verbs:["observe"],ancestors:(($p.ancestors + [$p.id]) | unique)})}}},
     grants:[{kind:"object",target:$target,capability:$p.id}]}' >"$D-intent.json"
  "$MINI" submit --host "$HOST" --config "$CONFIG" --socket "$PSOCK" \
    --intent "$D-intent.json" --key "$WR/tool.key" --dir "$D-attempt" >"$D.stdout"
  confirmed "$D-attempt/outcome.json"
)

# share LABEL APP SESSION TICKET CAP NONCE KIND: session birth, event22 ticket
# and event28 enrollment for participant 8, then `spk-host grain route`.
share() (
  label=$1 app=$2 session=$3 ticket=$4 cap=$5 nonce=$6 kind=$7
  descriptor=$((session + 1)) pkg=$((app + 1))
  appcap=$(jq -er .applicationGrainBirth.applicationBirth.application.appOwnerCapability \
    "$EV/$label-app-author/source.json")
  pkgcap=$(jq -er .applicationGrainBirth.applicationBirth.application.packageOwnerCapability \
    "$EV/$label-app-author/source.json")
  birth_session "$label" "$nonce" "$app" "$session" "$kind" "$cap"
  pkgdir=$RUN/host/apps/$app/install/launch-descriptor/package-v1
  schema=$(jq -er .root "$pkgdir/schema-inspection.json")
  version=$(jq -er .version "$pkgdir/schema-inspection.json")
  query "$label-app-state" 8 "$app" "$appcap" "$WR/tool.key" "$((nonce + 300))"
  pversion=$(jq -er '[.page.entries[] | select(.key.field == "2")][0].value' \
    "$EV/$label-app-state/view.json")
  T=$EV/$label-ticket-$ticket
  mkdir -p -m 700 "$T"
  # The installed manifest's package root is the signed launch descriptor's
  # root (BEGIN v3 prospectiveManifest), not the package identity root.
  launchroot=$(jq -er .root "$RUN/host/apps/$app/install/launch-descriptor/launch-inspection.json")
  if [ ! -s "$T/issue/receipt-anchor.json" ]; then
    grain_op "$label-ticket-$ticket-reserve" 8 7902 81 "$WR/tool.key" "$((nonce + 400))" \
      '{"type":"reserve","amount":"3"}'
    jq -n --arg app "$app" --arg session "$session" --arg descriptor "$descriptor" \
      --arg ticket "$ticket" --arg kind "$kind" --arg appcap "$appcap" \
      --arg scap "$cap" --arg tcap "$((cap + ticket % 100))" --arg nonce "$((nonce + 500))" \
      --arg pversion "$pversion" --arg schema "$schema" --arg version "$version" \
      --arg launchroot "$launchroot" --slurpfile pkg "$pkgdir/descriptor-inspection.json" '
      ([$pkg[0].interfaces[] | select(.kind == $kind)][0]) as $i |
      {spec:{ticket:{resource:$ticket,scope:{app:$app,packageVersion:$pversion,
          packageRoot:$launchroot,interfaceId:$i.id,interfaceVersion:$i.version,
          interfaceRoot:$i.root,schemaRoot:$schema,schemaVersion:$version},
          participant:{session:$session,descriptorResource:$descriptor,kind:$kind,
            subject:"8",origin:{type:"human"},sessionCapability:$scap,
            appObserveCapability:$appcap,ticketObserveCapability:(($tcap|tonumber)+2|tostring)},
          ceiling:{basis:{type:"role",id:"0"},added:[],removed:[],
            roleSchemaRoot:$schema,roleVersion:$version},issueNonce:$nonce},
        issuer:"8",appDelegateCapability:$appcap,ticketOwnerCapability:$tcap,
        ticketControlCapability:(($tcap|tonumber)+1|tostring)},
       payer:"8",funding:[],sourceCapabilities:["42"],
       tool:{task:"7902",capability:"81",observeCapability:"81"},
       parent:{task:"7901",capability:"73",observeCapability:"73"}}' >"$T/request.json"
    rm -rf "$T/preview"
    "$MINI" grain-share-issue-plan --host "$HOST" --config "$CONFIG" --socket "$OSOCK" \
      --request "$T/request.json" --dir "$T/preview" >"$T/preview.stdout"
    jq -e '.type == "application-grain-share-issue-plan-v1"' \
      "$T/preview/plan-inspected.json" >/dev/null
    approve "$T/preview/plan-inspected.json" header "$T/approval.json" "$(jq -c \
      --arg sha "$(sha "$T/preview/request.bin")" '
      {type:"minidregg-grain-share-issue-approval-v1",requestSha256:$sha,
       canonicalSpec:.canonicalSpec,issuer:.spec.issuer,
       participantSubject:.spec.ticket.participant.subject,
       appDelegateCapability:.spec.appDelegateCapability,
       ticketResource:.spec.ticket.resource,payer,funding,sourceCapabilities,tool,parent}' \
      "$T/preview/request-inspected.json")"
    [ -e "$T/issue" ] || "$MINI" grain-share-issue-prepare --host "$HOST" --config "$CONFIG" \
      --socket "$OSOCK" --request "$T/request.json" --approval "$T/approval.json" \
      --dir "$T/issue" >"$T/prepare.stdout"
    [ -e "$T/issue/submit-marker.json" ] ||
      "$MINI" grain-share-issue-submit --socket "$OSOCK" --attempt "$T/issue" \
        >"$T/submit.stdout" || echo "ticket submit uncertain; exact lookup follows" >&2
    "$MINI" grain-share-issue-lookup --socket "$OSOCK" --attempt "$T/issue" >"$T/lookup.stdout"
  fi
  delegate_observe "$label-ticket" "$ticket" "$((cap + ticket % 100))" \
    "$((cap + ticket % 100 + 2))" 8 "$((nonce + 700))"
  jq -n --arg name "owner-$kind" --arg session "$EV/$label-session-author/source.json" \
    --arg receipt "$EV/$label-session-attempt/outcome.json" --arg ticket "$T/issue" \
    --arg seed "$WR/tool.key" \
    --arg public "$(od -An -tx1 -v "$WR/tool.pub" | tr -d ' \n')" '
    {protocol:"mini-spk-grain-route-request-v1",name:$name,expectedHost:"grain.test",
     displayName:"Grain owner",preferredHandle:"owner",sessionSource:$session,
     sessionReceipt:$receipt,ticketIssue:$ticket,
     participantKey:{keyId:"8008",keyEpoch:"2",publicKeyHex:$public,seedPath:$seed}}' \
    >"$EV/$label-route-request.json"
  "$SPK_HOST" grain route "$PROFILE" "$app" "$EV/$label-route-request.json"
)

# enroll LABEL APP SESSION TICKET CAP NONCE: bind participant 8's session to
# the app's current serving generation (event28). A session still active for
# an older generation is first closed by its owner; renewal then re-enrolls.
enroll() (
  label=$1 app=$2 session=$3 ticket=$4 cap=$5 nonce=$6
  pkgcap=$(jq -er .applicationGrainBirth.applicationBirth.application.packageOwnerCapability \
    "$EV/$label-app-author/source.json")
  appcap=$(jq -er .applicationGrainBirth.applicationBirth.application.appOwnerCapability \
    "$EV/$label-app-author/source.json")
  pkgdir=$RUN/host/apps/$app/install/launch-descriptor/package-v1
  schema=$(jq -er .root "$pkgdir/schema-inspection.json")
  version=$(jq -er .version "$pkgdir/schema-inspection.json")
  query "$label-enroll-app-$nonce" 8 "$app" "$appcap" "$WR/tool.key" "$nonce"
  gen=$(jq -er '[.page.entries[] | select(.key.field == "0")][0].value' \
    "$EV/$label-enroll-app-$nonce/view.json")
  N=$EV/$label-enroll-g$gen
  [ ! -s "$N/receipt.json" ] || exit 0
  # Every signed command consumes its nonce: derive them per generation.
  nonce=$((nonce + gen * 10))
  # A definite refusal committed nothing; keep it for audit and plan afresh.
  if [ -s "$N/submit.outcome.json" ] &&
      jq -e '.type == "refused"' "$N/submit.outcome.json" >/dev/null; then
    aside=$N-refused-$(date +%s)
    mv "$N" "$aside"
    for f in "$N"-*.json "$N"-*.stdout; do [ -e "$f" ] && mv "$f" "$aside/" || :; done
  fi
  query "$label-session-$nonce" 8 "$session" "$cap" "$WR/tool.key" "$((nonce + 1))"
  sview=$EV/$label-session-$nonce/view.json
  sgen=$(jq -er '[.page.entries[] | select(.key.field == "2")][0].value' "$sview")
  status=$(jq -er '[.page.entries[] | select(.key.field == "3")][0].value' "$sview")
  if [ "$status" = 5 ]; then
    jq -n --arg s "$session" --arg c "$cap" --arg n "$((nonce + 2))" --arg g "$sgen" \
      --arg g1 "$((sgen + 1))" --slurpfile read "$sview" \
      --slurpfile challenge "$EV/$label-session-$nonce/challenge.json" '
      {subject:"8",nonce:$n,grants:[{kind:"object",target:$s,capability:$c}],
       purpose:{type:"prepare",draft:{type:"invoke",command:{subject:"8",nonce:$n,
         expectedAuthorityRoot:$challenge[0].signing[0].authorityRoot,
         targets:[{kind:"object",target:$s,capability:$c,observeCapability:$c,
           schemaVersion:"1",expectedTargetRoot:$read[0].page.root,
           payload:{type:"scalar",actions:[
             {type:"write",key:{type:"object",resource:$s,field:"2"},expected:$g,value:$g1},
             {type:"write",key:{type:"object",resource:$s,field:"3"},expected:"5",value:"6"}]}}]}}}}' \
      >"$EV/$label-close-g$gen-intent.json"
    "$MINI" submit --host "$HOST" --config "$CONFIG" --socket "$PSOCK" \
      --intent "$EV/$label-close-g$gen-intent.json" --key "$WR/tool.key" \
      --dir "$EV/$label-close-g$gen-attempt" >"$EV/$label-close-g$gen.stdout"
    confirmed "$EV/$label-close-g$gen-attempt/outcome.json"
  fi
  count=$(jq -er .receipt.acceptedCount "$EV/$label-ticket-$ticket/issue/receipt-anchor.json")
  jq -n --arg index "$((count - 1))" --arg ticket "$ticket" --arg pkg "$((app + 1))" \
    --arg dcap "$((cap + 2))" --arg scap "$cap" --arg mcap "$pkgcap" \
    --arg schema "$schema" --arg version "$version" --arg nonce "$((nonce + 3))" '
    {issueIndex:$index,ticketResource:$ticket,packageManifest:$pkg,
     role:{basis:{type:"role",id:"0"},added:[],removed:[],
       roleSchemaRoot:$schema,roleVersion:$version},
     descriptorCapability:$dcap,sessionObserveCapability:$scap,
     descriptorObserveCapability:$dcap,manifestObserveCapability:$mcap,nonce:$nonce}' \
    >"$N-request.json"
  if [ ! -e "$N/seal.json" ]; then
    rm -rf "$N"
    "$MINI" session-enrollment-plan --host "$HOST" --config "$CONFIG" \
      --operator-socket "$OSOCK" --request "$N-request.json" --dir "$N" >"$N-plan.stdout"
    approve "$N/plan-inspected.json" headerHex "$N-approval.json" "$(jq -nc \
      --arg r "$(sha "$N/request.bin")" --arg p "$(sha "$N/plan.bin")" \
      --arg i "$(sha "$N/plan-inspected.json")" '
      {type:"minidregg-session-enrollment-approval-v1",requestSha256:$r,planSha256:$p,
       planInspectionSha256:$i}')"
    "$MINI" session-enrollment-seal --attempt "$N" --approval "$N-approval.json" \
      >"$N-seal.stdout"
  fi
  [ -e "$N/submit-marker.json" ] ||
    "$MINI" session-enrollment-submit --attempt "$N" >"$N-submit.stdout" ||
    echo "enrollment submit uncertain; exact lookup follows" >&2
  "$MINI" session-enrollment-lookup --attempt "$N" >"$N-lookup.stdout"
  [ -s "$N/receipt.json" ]
)

# http_post LABEL APP PATH BODY: one authenticated publish through the route.
http_post() (
  label=$1 app=$2 path=$3 body=$4 kind=api
  dir=$RUN/host/apps/$app/routes/owner-$kind
  curl -sS --max-time 900 --unix-socket "$dir/http.sock" -D "$EV/$label.headers" \
    -H "Host: grain.test" -H "Authorization: Bearer $(cat "$dir/api.token")" \
    -H "Content-Type: text/plain" --data-binary "$body" \
    -o "$EV/$label.body" -w '%{http_code}\n' "http://grain.test$path"
)

# One authenticated request through the resident's route: the resident asks
# Mini to author, sign and admit it (op36/37/34), then delivers it over fd3.
http_get() (
  label=$1 app=$2 path=$3 kind=${4:-api}
  dir=$RUN/host/apps/$app/routes/owner-$kind
  curl -sS --max-time 900 --unix-socket "$dir/http.sock" -D "$EV/$label.headers" \
    -H "Host: grain.test" -H "Authorization: Bearer $(cat "$dir/api.token")" \
    -o "$EV/$label.body" -w '%{http_code}\n' "http://grain.test$path"
)

# floor APP: the M11 floor as the running app sees it. Every process in the
# running generation's unit cgroup is listed with its own /proc status lines
# (the kernel's view of that process: seccomp mode, NNP, capability sets,
# uids); the app is the process that is neither the resident nor bwrap.
floor() (
  app=$1
  gen=$("$SPK_HOST" grain status "$PROFILE" "$app" |
    jq -er '[.runs[] | select(.state == "running")][-1].generation')
  unit=mini-spk-a$app-g$gen.service
  cg=$(systemctl show "$unit" --property=ControlGroup --value)
  [ -n "$cg" ] || { echo "no cgroup for $unit" >&2; exit 1; }
  found=0
  for pid in $(cat "/sys/fs/cgroup$cg/cgroup.procs"); do
    exe=$(readlink "/proc/$pid/exe" 2>/dev/null || echo gone)
    printf 'pid=%s exe=%s ' "$pid" "$exe"
    grep -E '^(Uid|NoNewPrivs|Seccomp|Seccomp_filters|CapInh|CapPrm|CapEff|CapBnd|CapAmb):' \
      "/proc/$pid/status" | tr '\t\n' '  '
    echo
    case "$exe" in
      */spk-host|*/bwrap|gone) ;;
      *) grep -q '^Seccomp:[[:space:]]*2$' "/proc/$pid/status" &&
           grep -q '^NoNewPrivs:[[:space:]]*1$' "/proc/$pid/status" &&
           grep -q '^CapEff:[[:space:]]*0000000000000000$' "/proc/$pid/status" &&
           found=$((found + 1)) ;;
    esac
  done
  [ "$found" -ge 1 ] || { echo "no app process under the floor in $unit" >&2; exit 1; }
  echo "floor-held app-processes=$found unit=$unit"
)

write_profile() {
  [ ! -e "$PROFILE" ] || return 0
  mkdir -p -m 700 "$RUN/host"
  semantics=$(jq -er .semantics "$WR/operator-profile.json")
  jq -n --arg root "$RUN/host" --arg host "$HOST" --arg hostSha "$(sha "$HOST")" \
    --arg config "$CONFIG" --arg configSha "$(sha "$CONFIG")" --arg socket "$OSOCK" \
    --arg public "$(od -An -tx1 -v "$WR/tool.pub" | tr -d ' \n')" \
    --arg seed "$WR/tool.key" --arg completion "$STORE/custody/completion.seed" \
    --arg semantics "$semantics" --arg bwrap "$BWRAP" --arg bwrapSha "$(sha "$BWRAP")" \
    --arg spkHost "$SPK_HOST" --arg spkHostSha "$(sha "$SPK_HOST")" \
    --arg ingest "$BIN/spk-ingest" --arg volume "$BIN/spk-var-volume" '
    {protocol:"mini-spk-grain-host-v1",stateRoot:$root,
     miniHost:$host,miniHostSha256:$hostSha,miniConfig:$config,miniConfigSha256:$configSha,
     miniOperatorSocket:$socket,managementSubject:"8",managementKeyEpoch:"2",
     managementPublicKeyHex:$public,managementSeed:$seed,
     completionCustodianSeed:$completion,completionSemantics:$semantics,
     bwrap:$bwrap,bwrapSha256:$bwrapSha,spkHost:$spkHost,spkHostSha256:$spkHostSha,
     ingestHelper:$ingest,volumeHelper:$volume,
     appUids:[994,993,992,991],volumeMib:512}' >"$PROFILE"
  chmod 600 "$PROFILE"
}


run_phase() {
  case "$1" in
    store)
      [ -e "$STORE" ] || step store "$HERE/grain-store.sh" "$STORE" "$HOST" "$MINI" \
        "$BIN/minidregg-link-sqlite-store" "$BIN/minidregg-credential-signature-verifier" ;;
    services) step services services ;;
    workroom) step workroom workroom_ready ;;
    profile) step profile write_profile ;;
    birth-a) step birth-a birth_app a 51000 ${A}01 3101 ;;
    birth-b) step birth-b birth_app b 61000 ${B}01 3201 ;;
    install-a) step install-a "$SPK_HOST" grain install "$PROFILE" \
      "$EV/a-app-author/source.json" "$EV/a-app-attempt/outcome.json" "$SPK" ;;
    install-b) step install-b "$SPK_HOST" grain install "$PROFILE" \
      "$EV/b-app-author/source.json" "$EV/b-app-attempt/outcome.json" "$SPK" ;;
    status-a) step status-a "$SPK_HOST" grain status "$PROFILE" ${A}01 ;;
    share-a) step share-a share a ${A}01 ${A}10 ${A}20 3111 52000 api ;;
    share-b) step share-b share b ${B}01 ${B}10 ${B}20 3211 62000 api ;;
    share-b2) step share-b2 share b ${B}01 ${B}10 ${B}30 3211 64000 api ;;
    enroll-b3) step enroll-b3 enroll b ${B}01 ${B}10 ${B}30 3211 66000 ;;
    enroll-b4) step enroll-b4 enroll b ${B}01 ${B}10 ${B}30 3211 67000 ;;
    start-b2) step start-b2 "$SPK_HOST" grain start "$PROFILE" ${B}01 ;;
    enroll-b2) step enroll-b2 enroll b ${B}01 ${B}10 ${B}30 3211 65000 ;;
    get-b2) step get-b2 http_get get-b2-body ${B}01 /v1/health ;;
    status-b) step status-b "$SPK_HOST" grain status "$PROFILE" ${B}01 ;;
    status-a2) step status-a2 "$SPK_HOST" grain status "$PROFILE" ${A}01 ;;
    status-b2) step status-b2 "$SPK_HOST" grain status "$PROFILE" ${B}01 ;;
    start-b) step start-b "$SPK_HOST" grain start "$PROFILE" ${B}01 ;;
    stop-b) step stop-b "$SPK_HOST" grain stop "$PROFILE" ${B}01 ;;
    enroll-a) step enroll-a enroll a ${A}01 ${A}10 ${A}20 3111 53000 ;;
    enroll-a2) step enroll-a2 enroll a ${A}01 ${A}10 ${A}20 3111 54000 ;;
    enroll-b) step enroll-b enroll b ${B}01 ${B}10 ${B}20 3211 63000 ;;
    get-a) step get-a http_get get-a-body ${A}01 /v1/health ;;
    post-a) step post-a http_post post-a-body ${A}01 /m6grain "published at generation 2, before STOP" ;;
    poll-a2) step poll-a2 http_get poll-a2-body ${A}01 "/m6grain/json?poll=1&since=all" ;;
    get-a2) step get-a2 http_get get-a2-body ${A}01 /v1/health ;;
    get-b) step get-b http_get get-b-body ${B}01 /v1/health ;;
    start-a) step start-a "$SPK_HOST" grain start "$PROFILE" ${A}01 ;;
    stop-a) step stop-a "$SPK_HOST" grain stop "$PROFILE" ${A}01 ;;
    start-a2) step start-a2 "$SPK_HOST" grain start "$PROFILE" ${A}01 ;;
    stop-a2) step stop-a2 "$SPK_HOST" grain stop "$PROFILE" ${A}01 ;;
    floor-a) step floor-a floor "${A}01" ;;
    floor-a2) step floor-a2 floor "${A}01" ;;
    *) fail "unknown phase $1" ;;
  esac
}

case "$MODE" in
  phase)
    [ "$#" -ge 1 ] || usage
    for phase in "$@"; do run_phase "$phase"; done ;;
  stop-services) stop_services ;;
  jspk0)
    for phase in store services workroom profile birth-a install-a share-a start-a floor-a \
        enroll-a get-a post-a stop-a start-a2 floor-a2 enroll-a2 get-a2 poll-a2 stop-a2; do
      run_phase "$phase"
    done
    step stop-services stop_services ;;
  all)
    for phase in store services workroom profile birth-a install-a share-a start-a \
        enroll-a get-a post-a stop-a start-a2 enroll-a2 get-a2 poll-a2 birth-b install-b \
        share-b start-b enroll-b get-b status-a status-b stop-b stop-a2 status-a2 status-b2; do
      run_phase "$phase"
    done
    step stop-services stop_services ;;
  *) usage ;;
esac
