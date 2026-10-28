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
#   grain-journey.sh phase RUN_ROOT NAME...  phases against RUN_ROOT
#   grain-journey.sh stop-services RUN_ROOT  stop the Store services
#
# Runs as the Store operator (`mini`), never root: every root step is a
# one-shot volume helper call by the unprivileged broker. The Store services are
# child processes of this journey (pid files under RUN/sock). Environment:
#   BIN          directory holding the Host, mini, spk-host and Store helpers
#   GRAIN_HOST   the Host binary (default BIN/minidregg-host)
#   SPK          the signed sntfy package
#   GRAINS_ROOT  the broker's grains root (the grain host state lives below)
set -eu
umask 077

usage() { sed -n '2,17p' "$0" >&2; exit 2; }
[ "$#" -ge 2 ] || usage
MODE=$1 RUN=$2
shift 2
HERE=$(CDPATH='' cd -- "$(dirname -- "$0")" && pwd)
BIN=${BIN:-/opt/minidregg-m6-20260930/bin}
SPK=${SPK:-/srv/lanes/prod-spk/cache/sntfy-bc424d5fd3cf60977cacdac328adfbee4de94f88d57383ad38b3d472c0c24f2d.spk}
HOST=${GRAIN_HOST:-$BIN/minidregg-host}
GRAINS_ROOT=${GRAINS_ROOT:?store-specific grains root required}
# Explicit native CLI/profile pin; never a native environment-selected endpoint.
BROKER_SOCKET=${BROKER_SOCKET:?store-specific broker socket required}
# Every resident `mini` starts (consent, codec) keeps its socket, lock and PID file in the world's
# own anchor directory, never in the operator's shared $HOME: worlds share no state, and
# stop-residents.sh stops a world's residents from these PID files alone. Short on purpose:
# a Unix socket path is bounded.
MINI_CONSENT_ANCHOR_DIR=${MINI_CONSENT_ANCHOR_DIR:-$RUN/a}
mkdir -p -m 700 "$MINI_CONSENT_ANCHOR_DIR"
export MINI_CONSENT_ANCHOR_DIR
MINI=$BIN/mini
SPK_HOST=$BIN/spk-host
STORE=$RUN/store
WR=$STORE/base/workroom
CONFIG=$WR/deployment/pinned-config.json
PSOCK=$RUN/sock/participant/host.sock
OSOCK=$RUN/sock/operator/host.sock
EV=$RUN/evidence
# Store identity belongs to the native host/broker. Retain its exact result;
# never reconstruct a Store key from configuration bytes or scan directories.
PROFILE_RESULT=$EV/profile-result.json
STATE= PROFILE=
state_paths() {
  if [ -f "$PROFILE_RESULT" ]; then
    jq -e --arg config "$CONFIG" --arg grains "$GRAINS_ROOT" \
      --arg configSha "$(sha256sum "$CONFIG" | cut -d ' ' -f 1)" --arg init "$EV/init-store.json" \
      --arg broker "$BROKER_SOCKET" '
      .protocol == "mini-spk-grain-profile-result-v1" and
      .brokerSocket == $broker and
      .miniConfig == $config and .miniConfigSha256 == $configSha and
      .grainsRoot == $grains and .initStoreResult == $init and (.stateRoot | startswith($grains + "/")) and
      .profilePath == (.stateRoot + "/grain-host.json")' "$PROFILE_RESULT" >/dev/null || {
        echo "grain journey: retained profile result differs from this fixture" >&2; exit 1;
      }
    STATE=$(jq -er .stateRoot "$PROFILE_RESULT")
    PROFILE=$(jq -er .profilePath "$PROFILE_RESULT")
    jq -e --arg state "$STATE" --arg broker "$BROKER_SOCKET" '
      .protocol == "mini-spk-grain-init-store-v1" and .stateRoot == $state and
      .brokerSocket == $broker' "$EV/init-store.json" >/dev/null || {
        echo "grain journey: retained profile differs from native Store initialization" >&2; exit 1;
      }
    [ "$(realpath -- "$STATE")" = "$STATE" ] && [ -f "$PROFILE" ] || {
      echo "grain journey: retained profile path is absent or noncanonical" >&2; exit 1;
    }
    jq -e --arg state "$STATE" --arg config "$CONFIG" --arg grains "$GRAINS_ROOT" \
      --arg configSha "$(sha256sum "$CONFIG" | cut -d ' ' -f 1)" \
      --arg broker "$BROKER_SOCKET" '
      .brokerSocket == $broker and .stateRoot == $state and .miniConfig == $config and
      .miniConfigSha256 == $configSha and .grainsRoot == $grains' "$PROFILE" >/dev/null || {
        echo "grain journey: retained profile contradicts its result" >&2; exit 1;
      }
  fi
}
state_paths
# Resource coordinates: GRAIN_A..GRAIN_I are the two-digit prefixes of
# instance a..i's app (NN01), session (NN10) and ticket (NN20). CLASS_X is
# its size class (S, M or L); IMPORT_X (an export directory) with IMPORT_KEY
# installs it from an export. Per instance, SPK_X names its package (default
# SPK) and KIND_X its owner session kind (api: bearer token; web: browser
# cookie); GET_PATH_X, POST_PATH_X/POST_BODY_X/POST_TYPE_X/POST_METHOD_X and
# POLL_PATH_X name the get/post/poll requests (defaults: sntfy's);
# ROLE_BASIS_X the owner's role basis (default role 0).
A=${GRAIN_A:-91} B=${GRAIN_B:-92} C=${GRAIN_C:-93} D=${GRAIN_D:-94} E=${GRAIN_E:-95}
F=${GRAIN_F:-96} G=${GRAIN_G:-97} H=${GRAIN_H:-98} I=${GRAIN_I:-99}

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
  awk -v end="$step_t1" -v start="$step_t0" 'BEGIN { printf "%.9f\n", end - start }' >"$EV/$step_name.seconds"
  printf '%-28s exit=%s %6ss\n' "$step_name" "$step_rc" "$(cat "$EV/$step_name.seconds")" |
    tee -a "$EV/journey.log"
  return "$step_rc"
}

confirmed() {
  jq -e '.type == "confirmed" and .confirmation == "installed" and
    (.acceptedCount | type == "string" and test("^[1-9][0-9]*$"))' "$1" >/dev/null
}

service_up() {
  name=$1 socket=$2 mode=$3
  pidfile=$RUN/sock/$name.pid
  service_binary=$MINI controller_uid=
  if [ "$mode" = serve-public-proxy ] && [ -n "${SPK_PUBLIC_LISTENER_RECEIPT:-}" ]; then
    # Only the fixed installer registration selects a distinct public listener.
    # The ordinary clients and the private operator service keep their pins.
    jq -e --arg socket "$socket" --arg root "$GRAINS_ROOT/controller/public-listener/mini" \
      --argjson operator "$(id -u)" '
      .publicListener.socket == $socket and .publicListener.binary == $root and
      .publicListener.operatorUid == $operator and
      (.publicListener.controllerUid | type == "number" and . > 0 and floor == .) and
      (.publicListener.binarySha256 | test("^[0-9a-f]{64}$"))' "$SPK_PUBLIC_LISTENER_RECEIPT" >/dev/null ||
      fail 'public listener registration differs'
    service_binary=$(jq -er .publicListener.binary "$SPK_PUBLIC_LISTENER_RECEIPT")
    controller_uid=$(jq -er .publicListener.controllerUid "$SPK_PUBLIC_LISTENER_RECEIPT")
    [ -f "$service_binary" ] && [ ! -L "$service_binary" ] &&
      [ "$(stat -c '%u:%h' "$service_binary")" = 0:1 ] &&
      [ "$(sha "$service_binary")" = "$(jq -er .publicListener.binarySha256 "$SPK_PUBLIC_LISTENER_RECEIPT")" ] ||
      fail 'public listener registered binary differs'
  fi
  service_pin=$(printf '%s\n' "$mode" "$service_binary" "$(sha "$service_binary")" "$controller_uid" | sha256sum | cut -d ' ' -f 1)
  if [ -S "$socket" ] && [ -s "$pidfile" ] && kill -0 "$(cat "$pidfile")" 2>/dev/null; then
    # Do not accept the old independent public native session as this proxy.
    [ -s "$pidfile.mode" ] && [ "$(cat "$pidfile.mode")" = "$mode" ] ||
      fail "$name service mode differs; retain this fixture and use a fresh one"
    [ -s "$pidfile.pin" ] && [ "$(cat "$pidfile.pin")" = "$service_pin" ] || fail "$name live service pin differs"
    service_identity check "$pidfile.identity.json" "$(cat "$pidfile")" "$socket" "$service_binary" ||
      fail "$name live process/socket identity differs"
    return 0
  fi
  mkdir -p -m 700 "${socket%/*}"
  rm -f "$socket"
  if [ -f "$pidfile.identity.json" ]; then
    archived_identity=$pidfile.identity.$(sha "$pidfile.identity.json").json
    if [ -e "$archived_identity" ]; then
      cmp "$pidfile.identity.json" "$archived_identity" || fail 'prior service identity archive differs'
      rm "$pidfile.identity.json"
    else
      mv "$pidfile.identity.json" "$archived_identity"
    fi
  fi
  case "$mode" in
    serve-operator)
      set -- "$MINI" serve-operator --host "$HOST" --config "$CONFIG" --socket "$socket" ;;
    serve-public-proxy)
      set -- "$service_binary" serve-public-proxy --socket "$socket" --upstream "$OSOCK" --config "$CONFIG"
      [ -z "$controller_uid" ] || set -- "$@" --controller-uid "$controller_uid" ;;
    *) fail "unsupported fixture service mode $mode" ;;
  esac
  printf '%s\n' "$mode" >"$pidfile.mode"
  printf '%s\n' "$service_pin" >"$pidfile.pin"
  setsid "$@" >"$RUN/sock/$name.log" 2>&1 </dev/null &
  echo "$!" >"$pidfile"
  tick=0
  until [ -S "$socket" ]; do
    kill -0 "$(cat "$pidfile")" 2>/dev/null || fail "$name service exited"
    tick=$((tick + 1)); [ "$tick" -lt 600 ] || fail "$name socket timeout"
    sleep 0.5
  done
  service_identity capture "$pidfile.identity.json" "$(cat "$pidfile")" "$socket" "$service_binary"
}

service_identity() {
  python3 - "$@" <<'PYSERVICE'
import hashlib,json,os,pathlib,signal,stat,sys
action,record,pid,socket,binary=sys.argv[1:]
p=pathlib.Path('/proc')/pid; s=pathlib.Path(socket); record=pathlib.Path(record)
def digest(path): return hashlib.sha256(path.read_bytes()).hexdigest()
if action in ('capture','check','stop'):
    pidfd=None
    if action=='stop':
        try: pidfd=os.pidfd_open(int(pid))
        except ProcessLookupError: raise SystemExit(0)
    fields=(p/'stat').read_text().rsplit(')',1)[1].split()
    sm=s.lstat()
    assert p.stat().st_uid == os.getuid() and stat.S_ISSOCK(sm.st_mode) and sm.st_uid == os.getuid()
    value={'pid':int(pid),'startTicks':fields[19], 'executableSha256':digest(p/'exe'),
           'socket':str(s),'socketDevice':sm.st_dev,'socketInode':sm.st_ino}
    assert value['executableSha256']==digest(pathlib.Path(binary))
    if action=='capture': record.write_text(json.dumps(value,sort_keys=True)+'\n')
    else: assert value==json.loads(record.read_bytes())
    if pidfd is not None:
        signal.pidfd_send_signal(pidfd,signal.SIGTERM)
        os.close(pidfd)
else:
    value=json.loads(record.read_bytes())
    assert value['pid']==int(pid) and value['socket']==str(s)
    if p.exists():
        fields=(p/'stat').read_text().rsplit(')',1)[1].split()
        assert fields[19]!=value['startTicks'] or fields[0]=='Z', 'recorded service remains alive'
    if s.exists():
        sm=s.lstat()
        assert stat.S_ISSOCK(sm.st_mode) and sm.st_uid==os.getuid()
        assert (sm.st_dev,sm.st_ino)==(value['socketDevice'],value['socketInode']), 'socket replacement refused'
        s.unlink()
PYSERVICE
}

services() {
  # One Host owns the Store. The public socket relays only its public envelope
  # subset to that same private owner, with the exact config pin.
  service_up operator "$OSOCK" serve-operator
  service_up participant "$PSOCK" serve-public-proxy
  # workroom_ready performs signed source reads in the following phase;
  # socket existence here is process readiness, not native qualification.
}

stop_services() {
  for name in participant operator; do
    pidfile=$RUN/sock/$name.pid
    [ -s "$pidfile" ] || continue
    if [ -f "$pidfile.identity.json" ]; then
      binary=$MINI
      if [ "$name" = participant ] && [ -n "${SPK_PUBLIC_LISTENER_RECEIPT:-}" ]; then
        binary=$(jq -er .publicListener.binary "$SPK_PUBLIC_LISTENER_RECEIPT")
      fi
      if kill -0 "$(cat "$pidfile")" 2>/dev/null; then
        service_identity stop "$pidfile.identity.json" "$(cat "$pidfile")" "$RUN/sock/$name/host.sock" "$binary" ||
          fail "$name stop identity differs"
      fi
    else
      kill "$(cat "$pidfile")" 2>/dev/null || :
    fi
    if [ -f "$pidfile.identity.json" ]; then
      tick=0
      until service_identity remove-stale "$pidfile.identity.json" "$(cat "$pidfile")" "$RUN/sock/$name/host.sock" "$MINI" 2>/dev/null; do
        tick=$((tick+1)); [ "$tick" -lt 100 ] || fail "$name stop/owned socket cleanup timeout"
        sleep .1
      done
    fi
    rm -f "$pidfile"
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
      schemaVersion:"1",
      expectedTargetRoot:$read[0].cell.root,
      context:{operationId:$nonce,payload:"grain journey workroom"},
      before:($read[0].cell.grain | {generation,status,remaining,reserved}),
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
  if ! jq -e '.cell.grain.status == "3" and .cell.grain.reserved == "1"' \
      "$EV/parent-state/view.json" >/dev/null; then
    grain_op parent-attach 7 7901 71 "$WR/controller.key" 30010 '{"type":"attach","soft":false}'
    grain_op parent-reserve 7 7901 71 "$WR/controller.key" 30020 '{"type":"reserve","amount":"1"}'
  fi
  query tool-state 8 7902 81 "$WR/tool.key" 30031
  if jq -e '.cell.grain.status == "0"' "$EV/tool-state/view.json" >/dev/null; then
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
      ($inner):({genesis:$genesis[0],template:{issuer:"5",ownerBudget:"100000",lifetime:"10000"},
        creator:"8",nonce:$nonce,sourceCapabilities:["42"],funding:[],feePayer:"8"} + $spec),
      tool:{task:"7902",capability:"81",observeCapability:"81",targetRoot:$tool[0].cell.root,
        before:($tool[0].cell.grain | {generation,status,remaining,reserved})},
      parent:{task:"7901",capability:"73",observeCapability:"73",targetRoot:$parent[0].cell.root,
        before:($parent[0].cell.grain | {generation,status,remaining,reserved})}}}' \
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
        expectedTargetRoot:$resource[0].cell.root,parentId:$p.id,target:$target,
        child:($p + {id:$child,parent:$p.id,holder:{type:"subject",subject:$holder},
          targets:[$target],verbs:["observe"],ancestors:(($p.ancestors + [$p.id]) | unique)})}}},
     grants:[{kind:"object",target:$target,capability:$p.id}]}' >"$D-intent.json"
  "$MINI" submit --host "$HOST" --config "$CONFIG" --socket "$PSOCK" \
    --intent "$D-intent.json" --key "$WR/tool.key" --dir "$D-attempt" >"$D.stdout"
  confirmed "$D-attempt/outcome.json"
)

# share LABEL APP SESSION TICKET CAP NONCE KIND [ROUTE]: session birth, event22
# ticket and event28 enrollment for participant 8, then `spk-host grain route`.
# LABEL is the app's letter, or letter+digit for a second browser session on the
# same grain (its own session, ticket, route and tokens; ROUTE names its route).
share() (
  label=$1 app=$2 session=$3 ticket=$4 cap=$5 nonce=$6 kind=$7 route=${8:-owner-$7}
  expected_host=grain.test
  if [ "$label" = b ] && [ -n "${GRAIN_EXPECTED_HOST_B:-}" ]; then
    expected_host=$GRAIN_EXPECTED_HOST_B
    case "$expected_host" in localhost:*) ;; *) fail "browser-B expected host must be localhost with an explicit port" ;; esac
    host_port=${expected_host#localhost:}
    case "$host_port" in ''|0*|*[!0-9]*) fail "browser-B port must be canonical decimal" ;; esac
    [ "$host_port" -ge 1024 ] && [ "$host_port" -le 65535 ] || fail "browser-B port out of range"
  fi
  descriptor=$((session + 1)) pkg=$((app + 1))
  appcap=$(jq -er .applicationGrainBirth.applicationBirth.application.appOwnerCapability \
    "$EV/${label%[0-9]}-app-author/source.json")
  pkgcap=$(jq -er .applicationGrainBirth.applicationBirth.application.packageOwnerCapability \
    "$EV/${label%[0-9]}-app-author/source.json")
  birth_session "$label" "$nonce" "$app" "$session" "$kind" "$cap"
  pkgdir=$STATE/apps/$app/install/launch-descriptor/package-v1
  schema=$(jq -er .root "$pkgdir/schema-inspection.json")
  version=$(jq -er .version "$pkgdir/schema-inspection.json")
  query "$label-app-state" 8 "$app" "$appcap" "$WR/tool.key" "$((nonce + 300))"
  pversion=$(jq -er '[.cell.entries[] | select(.key.field == "2")][0].value' \
    "$EV/$label-app-state/view.json")
  T=$EV/$label-ticket-$ticket
  mkdir -p -m 700 "$T"
  # The installed manifest's package root is the signed launch descriptor's
  # root (BEGIN v3 prospectiveManifest), not the package identity root.
  launchroot=$(jq -er .root "$STATE/apps/$app/install/launch-descriptor/launch-inspection.json")
  if [ ! -s "$T/issue/receipt-anchor.json" ]; then
    grain_op "$label-ticket-$ticket-reserve" 8 7902 81 "$WR/tool.key" "$((nonce + 400))" \
      '{"type":"reserve","amount":"3"}'
    jq -n --argjson basis "$ROLE_BASIS" --arg app "$app" --arg session "$session" --arg descriptor "$descriptor" \
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
          ceiling:{basis:$basis,added:[],removed:[],
            roleSchemaRoot:$schema,roleVersion:$version},issueNonce:$nonce,notAfter:"1000000000"},
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
  case $route in owner-*) display="Grain owner" handle=owner ;; *) display="Second browser" handle=${route%%-*} ;; esac
  jq -n --arg host "$expected_host" --arg name "$route" --arg session "$EV/$label-session-author/source.json" \
    --arg receipt "$EV/$label-session-attempt/outcome.json" --arg ticket "$T/issue" \
    --arg seed "$WR/tool.key" --arg display "$display" --arg handle "$handle" \
    --arg public "$(od -An -tx1 -v "$WR/tool.pub" | tr -d ' \n')" '
    {protocol:"mini-spk-grain-route-request-v1",name:$name,expectedHost:$host,
     displayName:$display,preferredHandle:$handle,sessionSource:$session,
     sessionReceipt:$receipt,ticketIssue:$ticket,
     participantKey:{keyId:"8008",keyEpoch:"2",publicKeyHex:$public,seedPath:$seed}}' \
    >"$EV/$label-route-request.json"
  "$SPK_HOST" grain route "$PROFILE" "$app" "$EV/$label-route-request.json"
)

# register LABEL APP ROUTE: a route bound after START is served only once the
# running resident admits it through its own route control
# (deploy/spk-host/HOT-ROUTE-ENROLLMENT.md); the session generation is the exact
# one LABEL's enrollment admitted.
register() (
  label=$1 app=$2 route=$3
  plan=$(ls -d "$EV/$label"-enroll-g*/plan-inspected.json | tail -1)
  gen=$(jq -er .enrollment.appGeneration "$plan") sgen=$(jq -er .enrollment.sessionGeneration "$plan")
  dir=$STATE/apps/$app/routes/$route
  R=$EV/$label-register-g$gen
  [ ! -s "$R/reply.json" ] || exit 0
  mkdir -p -m 700 "$R"
  jq -n --arg nonce "$(od -An -N32 -tx1 /dev/urandom | tr -d ' \n')" --arg app "$app" --arg gen "$gen" \
    --arg sgen "$sgen" --arg dir "$dir" --arg custody "$dir/dispatch-custody.json" \
    --arg custodySha "$(sha "$dir/dispatch-custody.json")" --arg custodianSha "$(sha "$dir/custodian.json")" \
    --arg handle "${route%%-*}" '
    {protocol:"mini-spk-route-register-v1",registrationNonceHex:$nonce,expectedApp:$app,
     expectedAppGeneration:$gen,expectedSessionGeneration:$sgen,directory:$dir,dispatchCustody:$custody,
     dispatchCustodySha256:$custodySha,custodianSha256:$custodianSha,displayName:"Second browser",
     preferredHandle:$handle}' >"$R/request.json"
  chmod 600 "$R/request.json"
  "$SPK_HOST" grain register-route --socket "$STATE/apps/$app/g$gen/route-control.sock" \
    --request "$R/request.json" >"$R/reply.json.new"
  mv "$R/reply.json.new" "$R/reply.json"
  [ -S "$dir/http.sock" ] || fail "registered route $route has no socket"
)

# enroll LABEL APP SESSION TICKET CAP NONCE: bind participant 8's session to
# the app's current serving generation (event28). A session still active for
# an older generation is first closed by its owner; renewal then re-enrolls.
enroll() (
  label=$1 app=$2 session=$3 ticket=$4 cap=$5 nonce=$6
  pkgcap=$(jq -er .applicationGrainBirth.applicationBirth.application.packageOwnerCapability \
    "$EV/${label%[0-9]}-app-author/source.json")
  appcap=$(jq -er .applicationGrainBirth.applicationBirth.application.appOwnerCapability \
    "$EV/${label%[0-9]}-app-author/source.json")
  pkgdir=$STATE/apps/$app/install/launch-descriptor/package-v1
  schema=$(jq -er .root "$pkgdir/schema-inspection.json")
  version=$(jq -er .version "$pkgdir/schema-inspection.json")
  query "$label-enroll-app-$nonce" 8 "$app" "$appcap" "$WR/tool.key" "$nonce"
  gen=$(jq -er '[.cell.entries[] | select(.key.field == "0")][0].value' \
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
  sgen=$(jq -er '[.cell.entries[] | select(.key.field == "2")][0].value' "$sview")
  status=$(jq -er '[.cell.entries[] | select(.key.field == "3")][0].value' "$sview")
  # Session status is a (kind, status) tag: web 0-3, api 4-7; active is 1 or 5
  # (Kernel/ApplicationGrainSession.tag). Closing writes active -> closed.
  if [ "$status" = 5 ] || [ "$status" = 1 ]; then
    jq -n --arg s "$session" --arg c "$cap" --arg n "$((nonce + 2))" --arg g "$sgen" \
      --arg g1 "$((sgen + 1))" --arg st "$status" --arg st1 "$((status + 1))" --slurpfile read "$sview" \
      --slurpfile challenge "$EV/$label-session-$nonce/challenge.json" '
      {subject:"8",nonce:$n,grants:[{kind:"object",target:$s,capability:$c}],
       purpose:{type:"prepare",draft:{type:"invoke",command:{subject:"8",nonce:$n,
         targets:[{kind:"object",target:$s,capability:$c,observeCapability:$c,
           schemaVersion:"1",expectedTargetRoot:$read[0].cell.root,
           payload:{type:"scalar",actions:[
             {type:"write",key:{type:"object",resource:$s,field:"2"},expected:$g,value:$g1},
             {type:"write",key:{type:"object",resource:$s,field:"3"},expected:$st,value:$st1}]}}]}}}}' \
      >"$EV/$label-close-g$gen-intent.json"
    "$MINI" submit --host "$HOST" --config "$CONFIG" --socket "$PSOCK" \
      --intent "$EV/$label-close-g$gen-intent.json" --key "$WR/tool.key" \
      --dir "$EV/$label-close-g$gen-attempt" >"$EV/$label-close-g$gen.stdout"
    confirmed "$EV/$label-close-g$gen-attempt/outcome.json"
  fi
  count=$(jq -er .receipt.acceptedCount "$EV/$label-ticket-$ticket/issue/receipt-anchor.json")
  jq -n --argjson basis "$ROLE_BASIS" --arg index "$((count - 1))" --arg ticket "$ticket" --arg pkg "$((app + 1))" \
    --arg dcap "$((cap + 2))" --arg scap "$cap" --arg mcap "$pkgcap" \
    --arg schema "$schema" --arg version "$version" --arg nonce "$((nonce + 3))" '
    {issueIndex:$index,ticketResource:$ticket,packageManifest:$pkg,
     role:{basis:$basis,added:[],removed:[],
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

# cred KIND DIR: the transport credential for the owner route of that kind
# (curl header arguments, one per line): the API bearer, or the browser
# session cookie the bootstrap would set (the operator owns the route dir).
cred() {
  expected_host=$(jq -er .expectedHost "$2/custodian.json")
  case "$1" in
    api) printf '%s\n' -H "Authorization: Bearer $(cat "$2/api.token")" ;;
    web) printf '%s\n' -H "Cookie: __Host-mini_spk_session=$(cat "$2/browser.token")" \
      -H "Origin: https://$expected_host" ;;
    *) echo "unknown route kind $1" >&2; return 1 ;;
  esac
}

# http_post LABEL APP KIND PATH BODY [TYPE [METHOD]]: one authenticated write
# through the route.
http_post() (
  label=$1 app=$2 kind=$3 path=$4 body=$5 type=${6:-text/plain} method=${7:-POST}
  dir=$STATE/apps/$app/routes/owner-$kind
  expected_host=$(jq -er .expectedHost "$dir/custodian.json")
  cred "$kind" "$dir" >"$EV/$label.cred"
  set --
  while IFS= read -r arg; do set -- "$@" "$arg"; done <"$EV/$label.cred"
  rm -f "$EV/$label.cred"
  curl -sS --fail-with-body --max-time 900 --unix-socket "$dir/http.sock" -D "$EV/$label.headers" \
    -H "Host: $expected_host" "$@" -X "$method" \
    -H "Content-Type: $type" --data-binary "$body" \
    -o "$EV/$label.body" -w '%{http_code}\n' "http://$expected_host$path"
)

# One authenticated request through the resident's route: the resident asks
# Mini to author, sign and admit it (op36/37/34), then delivers it over fd3.
http_get() (
  label=$1 app=$2 path=$3 kind=${4:-api}
  dir=$STATE/apps/$app/routes/${5:-owner-$kind}
  expected_host=$(jq -er .expectedHost "$dir/custodian.json")
  cred "$kind" "$dir" >"$EV/$label.cred"
  set --
  while IFS= read -r arg; do set -- "$@" "$arg"; done <"$EV/$label.cred"
  rm -f "$EV/$label.cred"
  curl -sS --fail-with-body --max-time 900 --unix-socket "$dir/http.sock" -D "$EV/$label.headers" \
    -H "Host: $expected_host" "$@" \
    -o "$EV/$label.body" -w '%{http_code}\n' "http://$expected_host$path"
)

# floor APP: the M11 floor as the running app sees it. Every process in the
# running generation's unit cgroup is listed with its own /proc status lines
# (the kernel's view of that process: seccomp mode, NNP, capability sets,
# uids); the app is the process that is neither the resident nor bwrap.
floor() (
  app=$1
  unit=$("$SPK_HOST" grain status "$PROFILE" "$app" |
    jq -er '[.runs[] | select(.state == "running")][-1].unit')
  cg=$(systemctl --user show "$unit" --property=ControlGroup --value)
  [ -n "$cg" ] || { echo "no cgroup for $unit" >&2; exit 1; }
  found=0
  # Processes are told apart by their kernel task name (`Name:` in status is
  # world-readable; /proc/PID/exe is not, across UIDs or for a capable task).
  for pid in $(cat "/sys/fs/cgroup$cg/cgroup.procs"); do
    status=/proc/$pid/status
    name=$(sed -n 's/^Name:[[:space:]]*//p' "$status" 2>/dev/null) || continue
    printf 'pid=%s name=%s ' "$pid" "$name"
    grep -E '^(Uid|NoNewPrivs|Seccomp|Seccomp_filters|CapInh|CapPrm|CapEff|CapBnd|CapAmb):' \
      "$status" | tr '\t\n' '  '
    echo
    case "$name" in
      spk-host)
        # Parser and reaper hold no capability set after namespace bootstrap.
        if grep -q '^Uid:[[:space:]]*0[[:space:]]' "$status"; then
          echo "resident runs as root" >&2; exit 1
        fi
        for set in CapInh CapPrm CapEff CapBnd CapAmb; do
          grep -q "^$set:[[:space:]]*0000000000000000$" "$status" ||
            { echo "resident capability set $set is not empty" >&2; exit 1; }
        done
        grep -q '^NoNewPrivs:[[:space:]]*1$' "$status" &&
          grep -q '^Seccomp:[[:space:]]*2$' "$status" ||
          { echo "resident no_new_privs/seccomp floor absent" >&2; exit 1; }
        ;;
      bwrap|mini-grain-bwra) ;; # the kernel truncates task names to 15 bytes
      *) grep -q '^Seccomp:[[:space:]]*2$' "$status" &&
           grep -q '^NoNewPrivs:[[:space:]]*1$' "$status" &&
           grep -q '^CapEff:[[:space:]]*0000000000000000$' "$status" &&
           ! grep -q '^Uid:[[:space:]]*0[[:space:]]' "$status" &&
           found=$((found + 1)) ;;
    esac
  done
  [ "$found" -ge 1 ] || { echo "no app process under the floor in $unit" >&2; exit 1; }
  echo "floor-held app-processes=$found unit=$unit"
)

# edge APP KIND: the public edge in front of the resident's route socket (ruling D9;
# WEB-SPK-PUBLIC section 4.7): a TLS terminator (Caddy, CADDY) on a loopback port with a
# throwaway certificate for grain.test, reverse-proxying to the route's http.sock. Through
# it: the authenticated GET answers 200; the same GET without the credential is refused
# (not 2xx); a WebSocket open (WS_PATH_X, default /m6grain/ws) reaches 101. Caddy is this
# phase's child, stopped by its PID file. Not measured here: the Store's op34 count per GET
# and the edge running under a uid other than the operator's (the peer-gid change, L3).
edge_check() (
  app=$1 kind=$2 ws=$3
  dir=$STATE/apps/$app/routes/owner-$kind
  [ -n "${CADDY:-}" ] && [ -x "$CADDY" ] || { echo "edge phase needs CADDY (a caddy executable)" >&2; exit 1; }
  [ -S "$dir/http.sock" ] || { echo "no route socket $dir/http.sock" >&2; exit 1; }
  e=$RUN/edge-$app
  rm -rf "$e"; mkdir -m 700 "$e" "$e/data" "$e/config"
  openssl req -x509 -newkey ec -pkeyopt ec_paramgen_curve:P-256 -nodes -days 1 -subj /CN=grain.test \
    -addext subjectAltName=DNS:grain.test -keyout "$e/key.pem" -out "$e/cert.pem" 2>"$e/openssl.err" \
    || { echo "openssl could not make the test certificate: $(tail -1 "$e/openssl.err")" >&2; exit 1; }
  port=$((20000 + $(od -An -N2 -tu2 /dev/urandom | tr -d ' ') % 20000))
  cat >"$e/Caddyfile" <<CADDYFILE
{
	admin off
	auto_https off
	storage file_system $e/data
}
https://grain.test:$port {
	bind 127.0.0.1
	tls $e/cert.pem $e/key.pem
	reverse_proxy unix/$dir/http.sock {
		header_up Host grain.test
	}
}
CADDYFILE
  XDG_DATA_HOME=$e/data XDG_CONFIG_HOME=$e/config HOME=$e \
    "$CADDY" run --config "$e/Caddyfile" --adapter caddyfile >"$e/caddy.log" 2>&1 &
  echo $! >"$e/caddy.pid"
  trap 'kill "$(cat "$e/caddy.pid")" 2>/dev/null; wait 2>/dev/null' EXIT
  url=https://grain.test:$port
  tls="--resolve grain.test:$port:127.0.0.1 --cacert $e/cert.pem"
  tries=0
  until curl -s $tls -o /dev/null --max-time 2 "$url/"; do
    tries=$((tries + 1))
    [ "$tries" -lt 50 ] || { echo "edge did not listen on 127.0.0.1:$port: $(tail -1 "$e/caddy.log")" >&2; exit 1; }
    kill -0 "$(cat "$e/caddy.pid")" 2>/dev/null || { echo "caddy exited: $(tail -1 "$e/caddy.log")" >&2; exit 1; }
    sleep 0.2
  done
  cred "$kind" "$dir" >"$e/cred"
  set --
  while IFS= read -r arg; do set -- "$@" "$arg"; done <"$e/cred"
  rm -f "$e/cred"
  authed=$(curl -sS $tls --max-time 900 "$@" -o "$EV/edge-$app-authed.body" -w '%{http_code}' "$url$getp")
  anon=$(curl -sS $tls --max-time 900 -o "$EV/edge-$app-anon.body" -w '%{http_code}' "$url$getp")
  wsc=$(curl -sS $tls --http1.1 --max-time 10 "$@" -H 'Connection: Upgrade' -H 'Upgrade: websocket' \
    -H 'Sec-WebSocket-Version: 13' -H 'Sec-WebSocket-Key: bWluaS1lZGdlLXByb2JlLQ==' \
    -o /dev/null -w '%{http_code}' "$url$ws" 2>/dev/null || :)
  printf 'authed=%s anon=%s websocket=%s port=%s\n' "$authed" "$anon" "$wsc" "$port" >"$EV/edge-$app.result"
  [ "$authed" = 200 ] || { echo "edge: authenticated GET $getp answered $authed, not 200" >&2; exit 1; }
  case $anon in 2??) echo "edge: GET $getp without the credential answered $anon" >&2; exit 1 ;; esac
  [ "$wsc" = 101 ] || { echo "edge: WebSocket open $ws answered ${wsc:-nothing}, not 101" >&2; exit 1; }
  echo "edge-held authed=200 anon=$anon websocket=101 via 127.0.0.1:$port"
)

write_profile() {
  state_paths
  if [ -n "$PROFILE" ]; then
    printf '%s\n' "$PROFILE_RESULT"
    return 0
  fi
  [ ! -e "$EV/init-store.json" ] || fail "Store init already attempted; inspect retained evidence"
  if [ -n "${BROKER_SOCKET:-}" ]; then
    [ "$BROKER_SOCKET" = "$GRAINS_ROOT/runtime-${GRAINS_ROOT##*/}/broker.sock" ] || fail "isolated broker must belong to grains root"
    "$SPK_HOST" grain init-store "$GRAINS_ROOT" "$HOST" "$CONFIG" --broker-socket "$BROKER_SOCKET" >"$EV/init-store.json"
  else
    "$SPK_HOST" grain init-store "$GRAINS_ROOT" "$HOST" "$CONFIG" >"$EV/init-store.json"
  fi
  broker=$(jq -er --arg expected "$BROKER_SOCKET" '
    .brokerSocket | select(. == $expected)' "$EV/init-store.json") || fail "native broker endpoint differs"
  STATE=$(jq -er 'select(.protocol == "mini-spk-grain-init-store-v1") | .stateRoot' "$EV/init-store.json")
  case "$STATE" in "$GRAINS_ROOT"/*) ;; *) fail "native Store root is outside the pinned grains root" ;; esac
  [ -d "$STATE" ] && [ "$(realpath -- "$STATE")" = "$STATE" ] || fail "native Store root is absent or noncanonical"
  PROFILE=$STATE/grain-host.json
  [ ! -e "$PROFILE" ] || fail "profile already exists without this fixture result; preserve it"
  semantics=$(jq -er .semantics "$WR/operator-profile.json")
  # The physical bwrap spk-host's sandbox runs (MINI_BWRAP selects; see resolve-bwrap), pinned into the profile.
  BWRAP=$(sh "$HERE/../../deploy/grain-host/resolve-bwrap") || fail "no usable bwrap for the grain sandbox"
  jq -n --arg root "$STATE" --arg grains "$GRAINS_ROOT" --arg host "$HOST" --arg broker "$broker" \
    --arg hostSha "$(sha "$HOST")" \
    --arg config "$CONFIG" --arg configSha "$(sha "$CONFIG")" --arg socket "$OSOCK" \
    --arg public "$(od -An -tx1 -v "$WR/tool.pub" | tr -d ' \n')" \
    --arg seed "$WR/tool.key" --arg completion "$STORE/custody/completion.seed" \
    --arg semantics "$semantics" --arg bwrap "$BWRAP" --arg bwrapSha "$(sha "$BWRAP")" \
    --arg spkHost "$SPK_HOST" --arg spkHostSha "$(sha "$SPK_HOST")" '
    {protocol:"mini-spk-grain-host-v2",stateRoot:$root,grainsRoot:$grains,
     miniHost:$host,miniHostSha256:$hostSha,miniConfig:$config,miniConfigSha256:$configSha,
     miniOperatorSocket:$socket,managementSubject:"8",managementKeyEpoch:"2",
     managementPublicKeyHex:$public,managementSeed:$seed,
     completionCustodianSeed:$completion,completionSemantics:$semantics,
     bwrap:$bwrap,bwrapSha256:$bwrapSha,spkHost:$spkHost,spkHostSha256:$spkHostSha} +
    {brokerSocket:$broker}' >"$PROFILE"
  chmod 600 "$PROFILE"
  jq -n --arg profile "$PROFILE" --arg state "$STATE" --arg grains "$GRAINS_ROOT" --arg broker "$broker" \
    --arg config "$CONFIG" --arg configSha "$(sha "$CONFIG")" \
    --arg init "$EV/init-store.json" '
    {protocol:"mini-spk-grain-profile-result-v1",profilePath:$profile,stateRoot:$state,
     grainsRoot:$grains,miniConfig:$config,miniConfigSha256:$configSha,
     initStoreResult:$init,brokerSocket:$broker}' >"$PROFILE_RESULT"
  printf '%s\n' "$PROFILE_RESULT"
}


# Phases: store, services, workroom, profile, then VERB-XN for instance X in
# a b c d e and an optional repeat number N (enroll-a2, get-a2, ...). Nonces are
# derived per instance so every signed command's nonce is fresh.
run_phase() {
  case "$1" in
    store)
      [ -e "$STORE" ] || step store "$HERE/grain-store.sh" "$STORE" "$HOST" "$MINI" \
        "$BIN/minidregg-link-sqlite-store" "$BIN/minidregg-credential-signature-verifier"
      state_paths
      return ;;
    services) step services services; return ;;
    workroom) step workroom workroom_ready; return ;;
    profile) step profile write_profile; state_paths; return ;;
  esac
  phase=$1 verb=${1%-*} tail=${1##*-}
  letter=$(printf '%s' "$tail" | cut -c1) n=${tail#?}
  case "$letter" in
    a) P=$A i=1 ;; b) P=$B i=2 ;; c) P=$C i=3 ;; d) P=$D i=4 ;; e) P=$E i=5 ;;
    f) P=$F i=6 ;; g) P=$G i=7 ;; h) P=$H i=8 ;; i) P=$I i=9 ;;
    # j..p: the featured market set (featured-qualify.sh), resource prefixes 61..67.
    j) P=61 i=10 ;; k) P=62 i=11 ;; l) P=63 i=12 ;; m) P=64 i=13 ;; n) P=65 i=14 ;;
    o) P=66 i=15 ;; p) P=67 i=16 ;; *) fail "unknown phase $1" ;;
  esac
  upper=$(printf '%s' "$letter" | tr a-p A-P)
  eval "class=\${CLASS_$upper:-S} import=\${IMPORT_$upper:-} spk=\${SPK_$upper:-\$SPK}"
  eval "kind=\${KIND_$upper:-api} getp=\${GET_PATH_$upper:-/v1/health}"
  eval "postp=\${POST_PATH_$upper:-/m6grain} postt=\${POST_TYPE_$upper:-text/plain}"
  eval "postm=\${POST_METHOD_$upper:-POST} pollp=\${POLL_PATH_$upper:-'/m6grain/json?poll=1&since=all'}"
  eval "postb=\${POST_BODY_$upper:-'published by $letter before STOP'}"
  eval "wsp=\${WS_PATH_$upper:-/m6grain/ws}"
  # The owner's role basis in the share ceiling and the enrollment: role 0
  # (sntfy's only role) unless ROLE_BASIS_X says otherwise, e.g.
  # {"type":"allAccess"} for a package that declares no roles.
  eval "ROLE_BASIS=\${ROLE_BASIS_$upper:-'{\"type\":\"role\",\"id\":\"0\"}'}"
  export ROLE_BASIS
  # NONCE_BASE_X moves an instance's nonces when its coordinates are reused
  # after a refused attempt consumed some (every signed nonce is a nullifier).
  eval "base=\${NONCE_BASE_$upper:-$((40000 + i * 10000))}"
  app=${P}01
  case "$verb" in
    birth) step "$phase" birth_app "$letter" $((base + 1000)) "$app" "3${i}01" ;;
    install)
      if [ ! -f "$spk" ]; then
        fetched=$("$HERE/fetch-test-spk.sh")
        [ "$spk" = "$fetched" ] || fail "requested package absent; fetch supplies only pinned sntfy"
      fi
      if [ -n "$import" ]; then
        step "$phase" "$SPK_HOST" grain install "$PROFILE" "$EV/$letter-app-author/source.json" \
          "$EV/$letter-app-attempt/outcome.json" "$spk" --class "$class" \
          --import "$import" --exporter-key "$IMPORT_KEY"
      else
        step "$phase" "$SPK_HOST" grain install "$PROFILE" "$EV/$letter-app-author/source.json" \
          "$EV/$letter-app-attempt/outcome.json" "$spk" --class "$class"
      fi ;;
    # A trailing 2 (share-b2, enroll-b2, get-b2) is a second browser session on the
    # same grain: session ${P}50, ticket ${P}30, capabilities 3${i}51.. (ticket
    # 3${i}81..), route guest2-KIND, nonces from base + 6000.
    share) if [ "$n" = 2 ]; then
        step "$phase" share "${letter}2" "$app" "${P}50" "${P}30" "3${i}51" $((base + 6000)) "$kind" "guest2-$kind"
      else step "$phase" share "$letter" "$app" "${P}10" "${P}20" "3${i}11" $((base + 2000)) "$kind"; fi ;;
    enroll) if [ "$n" = 2 ]; then
        step "$phase" enroll "${letter}2" "$app" "${P}50" "${P}30" "3${i}51" $((base + 7000))
      else step "$phase" enroll "$letter" "$app" "${P}10" "${P}20" "3${i}11" \
        $((base + 2000 + ${n:-1} * 1000)); fi ;;
    start|stop|status|supervise) step "$phase" "$SPK_HOST" grain "$verb" "$PROFILE" "$app" ;;
    register) [ "$n" = 2 ] || fail "register applies to a second session (register-X2)"
      step "$phase" register "${letter}2" "$app" "guest2-$kind" ;;
    get) if [ "$n" = 2 ]; then step "$phase" http_get "$phase-body" "$app" "$getp" "$kind" "guest2-$kind"
      else step "$phase" http_get "$phase-body" "$app" "$getp" "$kind"; fi ;;
    post) step "$phase" http_post "$phase-body" "$app" "$kind" "$postp" "$postb" "$postt" "$postm" ;;
    poll) step "$phase" http_get "$phase-body" "$app" "$pollp" "$kind" ;;
    floor) step "$phase" floor "$app" ;;
    edge) step "$phase" edge_check "$app" "$kind" "$wsp" ;;
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
