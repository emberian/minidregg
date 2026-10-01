#!/usr/bin/env bash
# The Mini journey: the definition of done for the October 13 shellserver.
#
#   journey.sh MANIFEST.json NEW_RUN_ROOT
#
# One run stands up a fresh private Store, walks every step in order, prints one
# table row per step (PASS / FAIL / UNBUILT, wall seconds, deciding artifact),
# writes NEW_RUN_ROOT/journey-result.json, and names the FRONTIER: the first
# step that did not pass. Exit status is 0 only when the frontier is the end.
# Status is whatever a run prints; nothing else is status.
#
# Steps, in execution order (the bake-off order: growth runs between J6 and J7):
#   J0-J8  the tree-neutral journey, claudesplosion/bakeoff/BAKEOFF.md
#   J12X   host-malformed: malformed requests are refused by name and the service
#          survives (journey.d/j12x.sh, on this Store, between J3 and J4)
#   G      growth at 10/100/500/1000 accepted records; pass = write median
#          <= 5 s and cold reopen <= 60 s at 1000 (list item 1)
#   K4     one resource holds 32 fields and reads them back (list item 2)
#   KC     K-CLOCK: journey.d/jclock.sh (ticks move the one clock; a law reads clock/now)
#   JJ     K-JOINT-INDEX: journey.d/jjoint.sh (a law reads a participant by position)
#   M3-M7  list items 3-7; each runs journey.d/<id>.sh when that file exists
#          and is UNBUILT until then (contract below)
#   J12    PLACE §2.2/§2.4: two friends co-write a document through `mini shell`
#   J12C   PLACE §2.4: a transclusion across rooms (journey.d/j12c.sh)
#   BD     c-bind: plan footprints commute/overlap (journey.d/bind.sh, on this Store)
#   M8     agent fleet (journey.d/m8.sh -> fleet-journey.sh, its own Store)
#   J13    P-LAW: a law refusal names its clause (journey.d/j13.sh -> law-leaf-journey.sh, its own Store)
#   JJOB1  COMPUTE C1: the job law on fresh cells; every lifecycle edge admitted and refused by clause (journey.d/jjob1.sh)
#   J12A   P-AFFORDANCES: `can NAME`, each held verb dry-run (journey.d/j12a.sh -> affordances-journey.sh, its own Store)
#   JPAY1  PAY P1: the pay watcher over fixtures (journey.d/jpay1.sh)
#   JPAY2  PAY P2: the pay cell (journey.d/jpay2.sh, its own Store)
#   M3, M4, M5 run their lanes' stand-alone journeys on their own fresh Stores
#   (journey.d/m3.sh, m4.sh, m5.sh); their detail lines say so.
#   JP2    J-PRIV-2 (PRIVACY.md): a friend enrolled from their own key reaches
#          the Host only through the ssh byte proxy (journey.d/jpriv2.sh)
#
# MANIFEST (JSON; paths absolute):
#   {"host": ..., "mini": ..., "store": ..., "verifier": ...,
#    "shell": ..., "hermes": ..., "spkHost": ..., "candidate": ...,   (optional)
#    "sha256": {"host": "<hex>", ...}}                                (optional pins)
#   A pinned binary whose sha256 differs refuses the run before J0.
#
# STEP HOOKS (journey.d/<id>.sh, id in bind jjoint jclock jsync m3 m4 m5 m6 m7 m8 j12 j12c j13 j12a jpay1 jpay2 jpriv2 j12x jserve jjob1 jjob-money): the file's presence is
# what turns an UNBUILT stub into a real step; the shape of this script does
# not change. A hook is executed (not sourced) with these variables exported:
#   JOURNEY_RUN JOURNEY_WORLD JOURNEY_STEP_DIR   run root, fresh Store root, private dir for the hook
#   MINI HOST STORE VERIFIER CONFIG SOCKET       the pinned binaries and the live service
#   SPONSOR_WS NEWCOMER_WS SPONSOR_SUBJECT NEWCOMER_SUBJECT
#   SHELL_BIN HERMES_BIN SPK_HOST_BIN CANDIDATE  manifest entries ("" when absent)
#   HOOK_TIMEOUT_S (default 3600)
# The live service is running and is ours; a hook must stop every process it
# starts. Exit 0 = PASS; any other exit = FAIL. The LAST stdout line is the
# deciding artifact's absolute path; stderr's last line is the detail.
# Note: by the time M3-M7 run, the resource `shared` is deliberately locked
# (J8). A hook that needs an open resource creates its own through SPONSOR_WS.
#
# Tunables: JOURNEY_ONLY (space-separated step ids; others SKIPPED); JOURNEY_GROWTH_LEVELS (default "10 100 500 1000");
# JOURNEY_GROWTH_FULL=1 keeps measuring after two rising levels already exceed
# the 1000-record thresholds (default stops, see step G);
# JOURNEY_GROWTH_BUDGET_S (default 10800, the bake-off's three-hour rule);
# JOURNEY_STEPS (default: every step) runs only the named steps, in this
# script's order; the frontier is computed over those alone. A step whose
# dependency is not selected is blocked, so a subset must carry its deps.
# Requires: Linux (/proc-free, but GNU date +%N, setsid, timeout), bash, jq, sha256sum.

set -u
umask 077

HERE=$(CDPATH='' cd -- "$(dirname -- "$0")" && pwd)
SELF="$HERE/$(basename -- "$0")"

if [ "$#" -ne 2 ]; then
  echo "usage: $0 MANIFEST.json NEW_RUN_ROOT" >&2
  exit 2
fi
MANIFEST=$1
RUN=$2
for tool in jq sha256sum setsid timeout pgrep xxd; do
  command -v "$tool" >/dev/null 2>&1 || { echo "journey: $tool is required" >&2; exit 2; }
done
[ -f "$MANIFEST" ] || { echo "journey: no manifest at $MANIFEST" >&2; exit 2; }
case "$RUN" in /*) ;; *) echo "journey: run root must be absolute" >&2; exit 2;; esac
[ ! -e "$RUN" ] || { echo "journey: run root already exists: $RUN" >&2; exit 2; }

mf() { jq -r --arg k "$1" '.[$k] // "" | select(type == "string")' "$MANIFEST"; }
HOST=$(mf host); MINI=$(mf mini); STORE=$(mf store); VERIFIER=$(mf verifier)
SHELL_BIN=$(mf shell); HERMES_BIN=$(mf hermes); SPK_HOST_BIN=$(mf spkHost); CANDIDATE=$(mf candidate)
for name in host mini store verifier; do
  path=$(mf "$name")
  case "$path" in /*) ;; *) echo "journey: manifest .$name must be an absolute path" >&2; exit 2;; esac
  [ -x "$path" ] || { echo "journey: manifest .$name is not executable: $path" >&2; exit 2; }
done
for name in host mini store verifier shell hermes spkHost candidate; do
  path=$(mf "$name"); [ -n "$path" ] || continue
  want=$(jq -r --arg k "$name" '.sha256[$k] // ""' "$MANIFEST")
  [ -n "$want" ] || continue
  got=$(sha256sum "$path" | cut -d' ' -f1)
  [ "$got" = "$want" ] || { echo "journey: $name sha256 $got != pinned $want ($path)" >&2; exit 2; }
done

mkdir -m 700 "$RUN"
RUN=$(CDPATH='' cd -- "$RUN" && pwd)
W=$RUN/world                 # the Store root the bootstrap creates
S=$RUN/steps                 # per-step logs and artifacts
mkdir -m 700 "$S"
REQ=$RUN/requests; mkdir -m 700 "$REQ"
TSV=$RUN/journey.tsv; : >"$TSV"
CONFIG=$W/deployment/pinned-config.json
SOCKET=$W/public/mini.sock
SPONSOR_WS=$W/sponsor
NEWCOMER_WS=$W/newcomer-workspace
SPONSOR_SUBJECT=7
NEWCOMER_SUBJECT=""
LAST_COUNT=0                 # Host-reported acceptedCount of the newest accepted record
RUN_START=$(date +%s.%N)
LOAD_START=$(cut -d' ' -f1-3 /proc/loadavg 2>/dev/null)
{
  sha256sum "$SELF" "$HOST" "$MINI" "$STORE" "$VERIFIER"
  for p in "$SHELL_BIN" "$HERMES_BIN" "$SPK_HOST_BIN" "$CANDIDATE"; do [ -n "$p" ] && [ -e "$p" ] && sha256sum "$p"; done
} >"$RUN/inputs.sha256"
cp "$MANIFEST" "$RUN/manifest.json"

# ---------------------------------------------------------------- framework

now() { date +%s.%N; }
elapsed() { awk -v a="$1" -v b="$2" 'BEGIN{printf "%.3f", b-a}'; }
gt() { awk -v a="$1" -v b="$2" 'BEGIN{exit !(a>b)}'; }

STEPS=(J0 J1 J2 J3 J12X J4 JSERVE J5 J6 G J7 J8 K4 KC JJ K10 K11 KIX KF K12C KHQ KW JN2 JN3 JN5 JSYNC BD M3 M4 M5 M6 M7 M8 J12 J12C J13 JJOB1 JJOBM J12A JPAY1 JPAY2 JPAY3 JPAYE1 JPAYE2 JPAYE3 JPAY4 JPAY6 JP2)
if [ -n "${JOURNEY_STEPS:-}" ]; then
  SELECTED=()
  for id in "${STEPS[@]}"; do
    case " $JOURNEY_STEPS " in *" $id "*) SELECTED+=("$id");; esac
  done
  for id in $JOURNEY_STEPS; do
    case " ${STEPS[*]} " in *" $id "*) ;; *) echo "journey: JOURNEY_STEPS names unknown step $id" >&2; exit 2;; esac
  done
  STEPS=("${SELECTED[@]}")
fi
declare -A TITLE STATUS WALL ART DET
TITLE[J0]="clean start: private single-authority service, one sponsor"
TITLE[J1]="enroll an independently generated newcomer key"
TITLE[J2]="sponsor creates a resource under a permissive law"
TITLE[J3]="sponsor delegates observe+mutate (no control) to newcomer"
TITLE[J12X]="malformed requests refused by name; the same Host answers on; a killed Host is restarted"
TITLE[J4]="newcomer signed read, writes field to 1, reads back 1"
TITLE[JSERVE]="a hostile client (trickle, long request, 50 silent, route-mismatch through op 7) stalls no honest read and stops nothing"
TITLE[J5]="a key with no grant: read and write refused"
TITLE[K10]="rooms: born --in R, under R covers R and its chain, outsiders refused at the controller"
TITLE[K11]="per-author streams in a room: K writers append with zero re-plans"
TITLE[KIX]="the index the world keeps: who, since, and a read at a past height"
TITLE[KF]="a scope names fields and bounds each field change per write"
TITLE[K12C]="content actions: annotate at a revision, quote and transclude across cells"
TITLE[KHQ]="commit-reveal at the kernel: a sealed bid opens only to its commitment"
TITLE[KW]="realm wells: mint under the well grant and law, burn by the holder, conservation"
TITLE[JN2]="a friend Nock program becomes a program cell (own Store)"
TITLE[JN3]="the kernel checks a Nock run by re-executing it (own Store)"
TITLE[JN5]="a NockApp kernel door refereed by re-execution (own Store)"
TITLE[JPAY3]="observed payments become Book credit; the observer advances the deployment clock (own Store)"
TITLE[JPAYE1]="the pay watcher enrollment index on fixtures"
TITLE[JPAYE2]="self-enrollment decision with real signatures; enrollment view (own Store)"
TITLE[JPAYE3]="the self-enrollment receiver (own Store)"
TITLE[JPAY4]="the payment rail through the client with the fixture watcher (own Store)"
TITLE[JPAY6]="a Book burn funds an AgentGrain purse in one joint turn (own Store; needs GRAIN, TEST_PROVIDER, LAUNCH_GATE, sudo)"
TITLE[JJOBM]="a job money: escrow, bond and payout as conservation-checked Book turns (own Store)"
TITLE[JSYNC]="the operator's nockFSync at both poles; the lifetime proofWork meter (own Store)"
TITLE[J6]="stop/reopen: receipts recovered, exact retry replays"
TITLE[G]="growth 10/100/500/1000: write<=5s, reopen<=60s at 1000"
TITLE[J7]="law replaced; newcomer's existing grant still works"
TITLE[J8]="deny-all: newcomer refused, sponsor repair refused"
TITLE[K4]="one resource holds 32 fields and reads them back"
TITLE[JJ]="a law reads another participant by position (joint/index/i)"
TITLE[M3]="newcomer provisions itself and creates, no sponsor step"
TITLE[M4]="J1-J8 through the shell over ssh"
TITLE[M5]="Hermes does J4 through the client; killed, restarts, resolves"
TITLE[M6]="a grain: INSTALL -> START -> reachable over http"
TITLE[M7]="candidate built from portable interfaces reproduces hashes"
TITLE[BD]="plans bind address footprints: disjoint plans commute, overlap refused"
TITLE[M8]="agent fleet: fee'd turns, topic events, heads (own Store)"
TITLE[J12]="two friends co-write a document through the shell, with refusals"
TITLE[J12C]="a quote (transclusion) across rooms: four grants, four outcomes"
TITLE[J13]="a law refusal names its failing clause (own Store)"
TITLE[JJOB1]="C1 JOB-LAW: every job edge admitted and refused by clause"
TITLE[J12A]="can NAME: each held verb dry-run, nothing committed (own Store)"
TITLE[JPAY1]="pay watcher: finalized transfers become Observation records"
TITLE[JPAY2]="the pay cell: tariff, deposit book, assignment (own Store)"
TITLE[KC]="K-CLOCK: the one clock; clock/now in every resource law"
TITLE[JP2]="a friend's key never touches the box: enroll, use and delegate over the proxy"

# call NAME cmd args... : run one command under the 600 s per-operation abort
# rule; keeps NAME.{cmd,out,err,rc,wall} in the current step dir; returns rc.
call() {
  local name=$1; shift
  { printf '%q ' "$@"; echo; } >"$SD/$name.cmd"
  local t0 t1 rc
  t0=$(now)
  timeout 600 "$@" >"$SD/$name.out" 2>"$SD/$name.err"
  rc=$?
  t1=$(now)
  echo "$rc" >"$SD/$name.rc"
  elapsed "$t0" "$t1" >"$SD/$name.wall"
  return $rc
}
cwall() { cat "$SD/$1.wall"; }
fail() { DETAIL="$*"; return 1; }

# A refusal counts only when the Host said so: the client exits 3 (a Host
# refusal) AND names the Host's decoded RefusalReason for `host refused
# <stage>` AND the encoded refusal carries the native outcome v2 tag. A client
# crash, a parse error or an undecoded frame is not a refusal.
REFUSAL_TAG=44524547472f4e41544956452d484f53542f4f5554434f4d452f7634   # DREGG/NATIVE-HOST/OUTCOME/v4
refused() {
  local name=$1
  [ "$(cat "$SD/$name.rc")" = 3 ] || return 1
  grep -Eq "^  client: host refused [a-z-]+: refused: [a-z-]+: .*; encoded refusal: $REFUSAL_TAG" "$SD/$name.err"
}
# reason NAME: `<stage> <reason>` of a Host refusal, from the client's line.
reason() {
  grep -Eo "host refused [a-z-]+: refused: [a-z-]+" "$SD/$1.err" | tail -1 | sed -E 's/host refused ([a-z-]+): refused: /\1 /'
}
# decode NAME: the Host's encoded refusal as text, one line.
decode() {
  grep -o 'encoded refusal: [0-9a-f]*' "$SD/$1.err" | tail -1 | cut -d' ' -f3 | xxd -r -p 2>/dev/null \
    | tr -c '[:print:]' ' ' | tr -s ' ' | sed 's/^ *DREGG\/NATIVE-HOST\/OUTCOME\/v4 *//'
}
installed() { jq -e '.type == "confirmed" and .confirmation == "installed"' "$1" >/dev/null 2>&1; }
replayed() { jq -e '.type == "confirmed" and .confirmation == "replayed"' "$1" >/dev/null 2>&1; }
count_of() { jq -r '.acceptedCount' "$1"; }
# Accept a new record: installed and exactly one past the previous count.
accept() {
  local f=$1 c
  installed "$f" || return 1
  c=$(count_of "$f")
  [ "$c" = $((LAST_COUNT + 1)) ] || { DETAIL="acceptedCount $c, expected $((LAST_COUNT + 1)) in $f"; return 1; }
  LAST_COUNT=$c
}
field_value() { jq -r --arg f "$2" '[.cell.entries[]? | select(.key.field == $f) | .value][0] // "absent"' "$1"; }
# The read attempt directory the client names on stderr; its challenge.json
# carries the world root and height the Host answered from.
read_attempt() { sed -n 's/^workspace read attempt: //p' "$SD/$1.err" | tail -1; }
root_of_read() { jq -r '"\(.worldRoot) \(.height)"' "$(read_attempt "$1")/challenge.json"; }
# A receipt's (world root, height).
receipt_root() { jq -r '"\(.worldRoot) \(.acceptedCount)"' "$1"; }
nonce() { od -An -tu8 -N8 /dev/urandom | tr -d ' \n'; }

result_json() {
  local frontier=$1 end
  end=$(now)
  {
    for id in "${STEPS[@]}"; do
      jq -nc --arg id "$id" --arg title "${TITLE[$id]}" --arg status "${STATUS[$id]:-NOT-RUN}" \
        --arg wall "${WALL[$id]:-}" --arg artifact "${ART[$id]:-}" --arg detail "${DET[$id]:-}" \
        '{id:$id,title:$title,status:$status,wallSeconds:$wall,artifact:$artifact,detail:$detail}'
    done
  } | jq -s --arg frontier "$frontier" --arg run "$RUN" --arg script "$SELF" \
      --arg wall "$(elapsed "$RUN_START" "$end")" --rawfile inputs "$RUN/inputs.sha256" \
      --argjson accepted "$LAST_COUNT" --arg load0 "$LOAD_START" --arg load1 "$(cut -d' ' -f1-3 /proc/loadavg 2>/dev/null)" \
      --arg host "$(hostname)" --arg cpus "$(nproc 2>/dev/null)" \
      '{type:"mini-journey-result-v1", runRoot:$run, script:$script,
        inputsSha256:($inputs | split("\n") | map(select(length > 0))),
        acceptedRecords:$accepted, wallSeconds:$wall,
        machine:{host:$host, cpus:$cpus, loadAverageAtStart:$load0, loadAverageNow:$load1},
        frontier:$frontier, reachedEnd:($frontier == "END"), steps:.}' \
    >"$RUN/journey-result.json.tmp" && mv "$RUN/journey-result.json.tmp" "$RUN/journey-result.json"
}

frontier() {
  local id
  for id in "${STEPS[@]}"; do
    [ "${STATUS[$id]:-NOT-RUN}" = PASS ] || { echo "$id"; return; }
  done
  echo END
}

# run_step ID DEP... : a step whose dependency did not pass is FAIL (blocked).
run_step() {
  local id=$1; shift
  local dep t0 t1 rc
  case " ${STEPS[*]} " in *" $id "*) ;; *) return 0;; esac
  SD=$S/$id; mkdir -p -m 700 "$SD"
  DETAIL=""; ARTIFACT=""
  # JOURNEY_ONLY="ID ..." runs only those steps; the rest are SKIPPED (never
  # PASS), so a skipped dependency blocks its dependents and the frontier
  # names the first skipped step: a partial run cannot read as a full one.
  if [ -n "${JOURNEY_ONLY:-}" ] && [[ " $JOURNEY_ONLY " != *" $id "* ]]; then
    STATUS[$id]=SKIPPED; WALL[$id]=0.000; ART[$id]=""; DET[$id]="skipped: not in JOURNEY_ONLY"
    printf '%s\t%s\t%s\t%s\t%s\n' "$id" SKIPPED 0.000 "" "${DET[$id]}" >>"$TSV"
    echo "STEP $id SKIPPED" >&2
    result_json "$(frontier)"
    return
  fi
  for dep in "$@"; do
    if [ "${STATUS[$dep]:-}" != PASS ]; then
      STATUS[$id]=FAIL; WALL[$id]=0.000; ART[$id]=""; DET[$id]="blocked: $dep did not pass"
      printf '%s\t%s\t%s\t%s\t%s\n' "$id" FAIL 0.000 "" "${DET[$id]}" >>"$TSV"
      echo "STEP $id FAIL (blocked by $dep)" >&2
      result_json "$(frontier)"
      return
    fi
  done
  echo "STEP $id: ${TITLE[$id]} ..." >&2
  t0=$(now)
  "step_$id"
  rc=$?
  t1=$(now)
  case $rc in
    0) STATUS[$id]=PASS ;;
    3) STATUS[$id]=UNBUILT ;;
    *) STATUS[$id]=FAIL ;;
  esac
  WALL[$id]=$(elapsed "$t0" "$t1"); ART[$id]=$ARTIFACT; DET[$id]=$DETAIL
  printf '%s\t%s\t%s\t%s\t%s\n' "$id" "${STATUS[$id]}" "${WALL[$id]}" "$ARTIFACT" "$DETAIL" >>"$TSV"
  echo "STEP $id ${STATUS[$id]} ${WALL[$id]}s $DETAIL" >&2
  result_json "$(frontier)"
}

# ---------------------------------------------------------------- the service

server_pid() { cat "$W/public/server.pid" 2>/dev/null; }
ours() {  # the pid is a `mini serve` on OUR socket
  local args
  args=$(ps -o args= -p "$1" 2>/dev/null) || return 1
  case "$args" in *" serve "*"--socket $SOCKET"*) return 0;; *) return 1;; esac
}
stop_server() {
  local pid kids k i
  pid=$(server_pid); [ -n "$pid" ] || return 0
  kill -0 "$pid" 2>/dev/null || return 0
  ours "$pid" || { echo "journey: pid $pid is not our server; not signalling it" >&2; return 1; }
  kids=$(pgrep -P "$pid" | tr '\n' ' ')
  kill -TERM "$pid"
  for i in $(seq 1 300); do kill -0 "$pid" 2>/dev/null || break; sleep 0.1; done
  kill -0 "$pid" 2>/dev/null && { echo "journey: server $pid alive 30 s after TERM" >&2; return 1; }
  for k in $kids; do
    for i in $(seq 1 100); do kill -0 "$k" 2>/dev/null || break; sleep 0.1; done
    kill -0 "$k" 2>/dev/null && { echo "journey: Host child $k outlived its server" >&2; return 1; }
  done
  echo "stopped server $pid children [$kids]" >>"$RUN/services.log"
}
# start_server TAG: start `mini serve` on the same Store and socket.
start_server() {
  local tag=$1 pid
  setsid nohup "$MINI" serve --host "$HOST" --config "$CONFIG" --socket "$SOCKET" \
    >"$W/public/serve-$tag.log" 2>&1 </dev/null &
  pid=$!
  echo "$pid" >"$W/public/server.pid"
  echo "started server $pid ($tag)" >>"$RUN/services.log"
}
# reopen TAG WS NAME: stop, start, and time until the first signed read of
# NAME in workspace WS answers. Sets REOPEN_S; returns nonzero on failure.
reopen() {
  local tag=$1 ws=$2 name=$3 t0 t1 pid n=0
  stop_server || return 1
  t0=$(now)
  start_server "$tag"
  pid=$(server_pid)
  while :; do
    kill -0 "$pid" 2>/dev/null || { DETAIL="server exited on reopen ($W/public/serve-$tag.log)"; return 1; }
    if [ -S "$SOCKET" ] && grep -q serving "$W/public/serve-$tag.log" 2>/dev/null; then
      if "$MINI" workspace --action read --dir "$ws" --name "$name" \
          >"$SD/reopen-$tag.read.out" 2>"$SD/reopen-$tag.read.err"; then break; fi
    fi
    n=$((n + 1))
    t1=$(now)
    gt "$(elapsed "$t0" "$t1")" 600 && { DETAIL="reopen $tag: no signed read within 600 s"; return 1; }
    sleep 0.05
  done
  t1=$(now)
  REOPEN_S=$(elapsed "$t0" "$t1")
  echo "reopen $tag: ${REOPEN_S}s to first signed read ($n polls)" >>"$RUN/services.log"
}
cleanup() { stop_server; }
trap cleanup EXIT
trap 'exit 130' INT TERM

# ---------------------------------------------------------------- requests

printf '%s\n' '{"type":"all","predicates":[]}' >"$REQ/permit-all.json"
printf '%s\n' '{"type":"minidregg-workspace-proposal-v1","action":"install-policy","name":"shared","predicate":{"type":"not","predicate":{"type":"any","predicates":[]}}}' >"$REQ/law-v2.json"
printf '%s\n' '{"type":"minidregg-workspace-proposal-v1","action":"install-policy","name":"shared","predicate":{"type":"any","predicates":[]}}' >"$REQ/deny-all.json"
printf '%s\n' '{"type":"minidregg-workspace-proposal-v1","action":"install-policy","name":"shared","predicate":{"type":"all","predicates":[]}}' >"$REQ/repair.json"
scalar() {  # scalar NAME ACTION FIELD VALUE [EXPECTED]
  if [ -n "${5:-}" ]; then
    printf '{"type":"minidregg-workspace-proposal-v1","action":"invoke","targets":[{"name":"%s","payload":{"type":"scalar","actions":[{"type":"%s","key":{"type":"object","field":"%s"},"value":"%s","expected":"%s"}]}}]}\n' "$1" "$2" "$3" "$4" "$5"
  else
    printf '{"type":"minidregg-workspace-proposal-v1","action":"invoke","targets":[{"name":"%s","payload":{"type":"scalar","actions":[{"type":"%s","key":{"type":"object","field":"%s"},"value":"%s"}]}}]}\n' "$1" "$2" "$3" "$4"
  fi
}
# A crafted intent: the newcomer's well-formed invoke intent re-addressed to
# another subject with fresh nonces. This is an adversary's path, not a
# friend's; the client still signs it with the workspace's own key.
craft() {  # craft SOURCE_INTENT SUBJECT [AUTHORITY_ROOT] > out
  jq --arg s "$2" --arg n1 "$(nonce)" --arg n2 "$(nonce)" --arg root "${3:-}" '
    .subject = $s | .nonce = $n1
    | .purpose.draft.command.subject = $s | .purpose.draft.command.nonce = $n2
    | if $root != "" then .purpose.draft.command.expectedAuthorityRoot = $root else . end' "$1"
}

# ---------------------------------------------------------------- J0-J8

step_J0() {
  ARTIFACT=$W/handoff.json
  call bootstrap sh "$HERE/newparticipant-acceptance.sh" "$HOST" "$MINI" "$STORE" "$VERIFIER" "$W" \
    || fail "bootstrap exit $(cat "$SD/bootstrap.rc"): $(tail -1 "$SD/bootstrap.err")" || return
  jq -e '.type == "minidregg-newparticipant-fixture-v1"' "$W/handoff.json" >/dev/null \
    || fail "no handoff.json" || return
  jq -e '.cell.root // .root' "$W/factory-read.json" >/dev/null \
    || fail "signed factory read did not answer ($W/factory-read.json)" || return
  ours "$(server_pid)" || fail "bootstrap server is not running on our socket" || return
  DETAIL="service up and a signed read answered in $(cwall bootstrap)s"
}

step_J1() {
  local A=$W/attempts/newcomer pub
  ARTIFACT=$A/submit.json
  call plan "$MINI" enroll --action plan --sponsor-workspace "$SPONSOR_WS" --factory-ref factory \
    --name newcomer-1 --new-key "$W/newcomer.key" --dir "$A" || fail "enroll plan refused: $(tail -1 "$SD/plan.err")" || return
  call seal "$MINI" enroll --action seal --dir "$A" || fail "enroll seal failed: $(tail -1 "$SD/seal.err")" || return
  call submit "$MINI" enroll --action submit --dir "$A" || fail "enroll submit failed: $(tail -1 "$SD/submit.err")" || return
  accept "$A/submit.json" || fail "enrollment not installed: ${DETAIL:-$(cat "$A/submit.json")}" || return
  call lookup "$MINI" enroll --action lookup --dir "$A" || fail "enroll lookup failed" || return
  [ "$(jq -r .receipt.transactionId "$SD/lookup.out")" = "$(jq -r .transactionId "$A/submit.json")" ] \
    || fail "lookup returned a different receipt" || return
  NEWCOMER_SUBJECT=$(jq -r .subject "$SD/submit.out")
  pub=$(od -An -tx1 -v "$W/newcomer.pub" | tr -d ' \n')
  # No operator edit on the newcomer's behalf: its key appears in no operator artifact.
  if grep -rlq "$pub" "$W/genesis.json" "$W/operator.json" "$W/deployment" 2>/dev/null; then
    fail "newcomer public key appears in genesis/operator/deployment files"; return
  fi
  DETAIL="subject $NEWCOMER_SUBJECT, record $LAST_COUNT; key absent from genesis/config; lookup = same receipt"
}

step_J2() {
  ARTIFACT=$SPONSOR_WS/attempts/create-shared/outcome.json
  call create "$MINI" workspace --action create --dir "$SPONSOR_WS" --name shared --storage declared \
    --predicate "$REQ/permit-all.json" || fail "create refused: $(tail -1 "$SD/create.err")" || return
  accept "$ARTIFACT" || fail "create not installed: $DETAIL" || return
  jq -e '.controlCapability != null and .observeCapability != null' "$SPONSOR_WS/refs/shared.json" >/dev/null \
    || fail "sponsor holds no control/observe capability for shared" || return
  DETAIL="object $(jq -r .target "$SPONSOR_WS/refs/shared.json") under all[], record $LAST_COUNT"
}

step_J3() {
  local P=$SPONSOR_WS/proposals/grant-newcomer A=$SPONSOR_WS/attempts/grant-newcomer
  ARTIFACT=$A/outcome.json
  jq -n --arg r "$NEWCOMER_SUBJECT" '{type:"minidregg-workspace-proposal-v1",action:"delegate",name:"shared",
    recipient:$r,verbs:["observe","mutate"],maxCost:"50000"}' >"$REQ/delegate.json"
  call propose "$MINI" workspace --action propose --dir "$SPONSOR_WS" --request "$REQ/delegate.json" \
    --proposal-id grant-newcomer || fail "delegate propose failed: $(tail -1 "$SD/propose.err")" || return
  jq -e --arg r "$NEWCOMER_SUBJECT" '.purpose.draft.command.child
      | .verbs == ["observe","mutate"] and .holder.subject == $r' "$P/intent.json" >/dev/null \
    || fail "child capability is not exactly observe+mutate for the newcomer" || return
  call submit "$MINI" workspace --action submit --dir "$SPONSOR_WS" --intent "$P/intent.json" --attempt "$A" \
    || fail "delegate submit refused: $(tail -1 "$SD/submit.err")" || return
  accept "$A/outcome.json" || fail "delegation not installed: $DETAIL" || return
  call publish "$MINI" workspace --action publish-delegation --dir "$SPONSOR_WS" --proposal-id grant-newcomer \
    --attempt "$A" || fail "publish-delegation failed" || return
  jq -e '.type == "minidregg-delegated-reference-v1"' "$P/recipient-reference.json" >/dev/null \
    || fail "no recipient reference" || return
  DETAIL="child $(jq -r .capability "$P/recipient-reference.json") verbs observe,mutate, record $LAST_COUNT"
}

step_J4() {
  local A=$NEWCOMER_WS/attempts/first-action
  ARTIFACT=$A/outcome.json
  call init "$MINI" workspace --action init --host "$HOST" --config "$CONFIG" --socket "$SOCKET" \
    --enrollment "$W/attempts/newcomer/enrollment.json" --dir "$NEWCOMER_WS" || fail "newcomer init failed" || return
  call import "$MINI" workspace --action import --dir "$NEWCOMER_WS" --name shared \
    --from-ref "$SPONSOR_WS/proposals/grant-newcomer/recipient-reference.json" || fail "import failed" || return
  jq -e '.controlCapability == null' "$NEWCOMER_WS/refs/shared.json" >/dev/null \
    || fail "newcomer reference carries a control capability" || return
  call read0 "$MINI" workspace --action read --dir "$NEWCOMER_WS" --name shared \
    || fail "newcomer signed read refused: $(tail -1 "$SD/read0.err")" || return
  [ "$(field_value "$SD/read0.out" 2)" = absent ] || fail "field 2 already present before the write" || return
  scalar shared create 2 1 >"$REQ/first-action.json"
  call propose "$MINI" workspace --action propose --dir "$NEWCOMER_WS" --request "$REQ/first-action.json" \
    --proposal-id first-action || fail "propose failed: $(tail -1 "$SD/propose.err")" || return
  call submit "$MINI" workspace --action submit --dir "$NEWCOMER_WS" \
    --intent "$NEWCOMER_WS/proposals/first-action/intent.json" --attempt "$A" \
    || fail "write refused: $(tail -1 "$SD/submit.err")" || return
  accept "$A/outcome.json" || fail "write not installed: $DETAIL" || return
  call read1 "$MINI" workspace --action read --dir "$NEWCOMER_WS" --name shared || fail "readback refused" || return
  [ "$(field_value "$SD/read1.out" 2)" = 1 ] || fail "readback field 2 = $(field_value "$SD/read1.out" 2), expected 1" || return
  DETAIL="read $(cwall read0)s, write $(awk -v a="$(cwall propose)" -v b="$(cwall submit)" 'BEGIN{printf "%.3f", a+b}')s, readback field 2 = 1, record $LAST_COUNT"
}

step_J5() {
  local A=$W/attempts/third TW=$W/third-workspace UW=$W/stranger-workspace child owner target n=0
  child=$(jq -r .observeCapability "$NEWCOMER_WS/refs/shared.json")
  owner=$(jq -r .observeCapability "$SPONSOR_WS/refs/shared.json")
  target=$(jq -r .target "$SPONSOR_WS/refs/shared.json")
  ARTIFACT=$SD/refusals.tsv; : >"$ARTIFACT"
  # A third, enrolled key holding no grant.
  call keygen "$MINI" keygen --secret "$W/third.key" --public "$W/third.pub" || fail "keygen failed" || return
  call plan "$MINI" enroll --action plan --sponsor-workspace "$SPONSOR_WS" --factory-ref factory \
    --name third-1 --new-key "$W/third.key" --dir "$A" || fail "third enroll plan failed" || return
  call seal "$MINI" enroll --action seal --dir "$A" || fail "third seal failed" || return
  call submit "$MINI" enroll --action submit --dir "$A" || fail "third enroll failed" || return
  accept "$A/submit.json" || fail "third enrollment not installed: $DETAIL" || return
  local third; third=$(jq -r .subject "$SD/submit.out")
  call init "$MINI" workspace --action init --host "$HOST" --config "$CONFIG" --socket "$SOCKET" \
    --enrollment "$A/enrollment.json" --dir "$TW" || fail "third init failed" || return
  call import-child "$MINI" workspace --action import --dir "$TW" --name stolen --kind object \
    --target "$target" --observe-capability "$child" || fail "import failed" || return
  call import-owner "$MINI" workspace --action import --dir "$TW" --name owner --kind object \
    --target "$target" --observe-capability "$owner" || fail "import failed" || return
  # A key that was never enrolled.
  call ukeygen "$MINI" keygen --secret "$W/stranger.key" --public "$W/stranger.pub" || fail "keygen failed" || return
  call uinit "$MINI" workspace --action init --host "$HOST" --config "$CONFIG" --socket "$SOCKET" \
    --key "$W/stranger.key" --subject 4242424242 --dir "$UW" || fail "stranger init failed" || return
  call uimport "$MINI" workspace --action import --dir "$UW" --name stolen --kind object \
    --target "$target" --observe-capability "$child" || fail "import failed" || return
  # The newcomer's own fresh, well-formed write intent (propose has no effect),
  # re-addressed to each stranger.
  scalar shared create 3 1 >"$REQ/j5-template.json"
  call template "$MINI" workspace --action propose --dir "$NEWCOMER_WS" --request "$REQ/j5-template.json" \
    --proposal-id j5-template || fail "newcomer template propose failed" || return
  craft "$NEWCOMER_WS/proposals/j5-template/intent.json" "$third" >"$REQ/j5-third-crafted.json"
  craft "$NEWCOMER_WS/proposals/j5-template/intent.json" 4242424242 >"$REQ/j5-stranger-crafted.json"
  scalar stolen create 3 1 >"$REQ/j5-third-invoke.json"
  local before; call before "$MINI" workspace --action read --dir "$NEWCOMER_WS" --name shared \
    || fail "control read before refusals failed" || return
  before=$(root_of_read before)

  call read-child "$MINI" workspace --action read --dir "$TW" --name stolen
  call read-owner "$MINI" workspace --action read --dir "$TW" --name owner
  call propose-write "$MINI" workspace --action propose --dir "$TW" --request "$REQ/j5-third-invoke.json" --proposal-id third-write
  call submit-crafted "$MINI" workspace --action submit --dir "$TW" --intent "$REQ/j5-third-crafted.json"
  call uread "$MINI" workspace --action read --dir "$UW" --name stolen
  call usubmit "$MINI" workspace --action submit --dir "$UW" --intent "$REQ/j5-stranger-crafted.json"
  local c
  for c in read-child read-owner propose-write submit-crafted uread usubmit; do
    if refused "$c"; then
      printf '%s\trefused\t%s\t%s\n' "$c" "$(reason "$c")" "$(decode "$c")" >>"$ARTIFACT"
    else
      printf '%s\tNOT-REFUSED\trc=%s\n' "$c" "$(cat "$SD/$c.rc")" >>"$ARTIFACT"; n=$((n + 1))
    fi
  done
  [ "$n" = 0 ] || fail "$n of 6 stranger attempts were not refused by the Host (see $ARTIFACT)" || return
  # Control: the grant holder still reads, and nothing the strangers did changed the image.
  call control "$MINI" workspace --action read --dir "$NEWCOMER_WS" --name shared || fail "control read failed" || return
  [ "$(field_value "$SD/control.out" 2)" = 1 ] || fail "control read lost field 2" || return
  [ "$(root_of_read control)" = "$before" ] || fail "world root or height moved during refused attempts" || return
  DETAIL="6/6 refused by the Host (enrolled no-grant read x2, propose, crafted submit; unenrolled read, submit); image unchanged; third = record $LAST_COUNT"
}

step_J6() {
  local A=$NEWCOMER_WS/attempts/first-action E=$W/attempts/newcomer enr_sha b0 b1
  ARTIFACT=$SD/retry.out
  enr_sha=$(sha256sum "$E/enrollment.json" | cut -d' ' -f1)
  reopen J6 "$NEWCOMER_WS" shared || return 1
  cp "$SD/reopen-J6.read.out" "$SD/after-reopen.read.out"
  [ "$(field_value "$SD/after-reopen.read.out" 2)" = 1 ] || fail "J4's value not recovered after reopen" || return
  call lookup "$MINI" enroll --action lookup --dir "$E" || fail "enrollment lookup failed after reopen" || return
  [ "$(jq -r .receipt.transactionId "$SD/lookup.out")" = "$(jq -r .transactionId "$E/submit.json")" ] \
    || fail "J1 receipt not recovered" || return
  [ "$(sha256sum "$E/enrollment.json" | cut -d' ' -f1)" = "$enr_sha" ] || fail "enrollment.json changed" || return
  call b0 "$MINI" workspace --action read --dir "$NEWCOMER_WS" --name shared || fail "read failed" || return
  b0=$(root_of_read b0)
  call retry "$MINI" retry --attempt "$A" --mode submit || fail "exact retry failed: $(tail -1 "$SD/retry.err")" || return
  replayed "$SD/retry.out" || fail "retry was not a replay" || return
  [ "$(jq -r .transactionId "$SD/retry.out")" = "$(jq -r .transactionId "$A/outcome.json")" ] \
    || fail "retry returned a different transaction" || return
  # The replayed receipt is the original: the same (world root, height) the
  # first acceptance sealed, not the current tip's.
  [ "$(receipt_root "$SD/retry.out")" = "$(receipt_root "$A/outcome.json")" ] \
    || fail "retry receipt $(receipt_root "$SD/retry.out") differs from the original $(receipt_root "$A/outcome.json")" || return
  call b1 "$MINI" workspace --action read --dir "$NEWCOMER_WS" --name shared || fail "read failed" || return
  b1=$(root_of_read b1)
  [ "$b0" = "$b1" ] || fail "exact retry moved the world root or height (a second effect): $b0 -> $b1" || return
  DETAIL="reopen to first signed read ${REOPEN_S}s; J1 receipt and field 2 = 1 recovered; retry replayed tx with its original (root, height); read (root, height) unchanged: $b1"
}

# ---------------------------------------------------------------- growth

GROW_N=0
# One growth write: the newcomer overwrites field 101 with the next integer.
grow_write() {
  local id prev
  prev=$(cat "$SD/f101")
  GROW_N=$((GROW_N + 1)); id=g$GROW_N
  scalar shared write 101 "$GROW_N" "$prev" >"$SD/w/$id.json"
  local t0 t1
  t0=$(now)
  call "w/$id.propose" "$MINI" workspace --action propose --dir "$NEWCOMER_WS" --request "$SD/w/$id.json" --proposal-id "$id" \
    || { DETAIL="growth write $id propose failed at record $LAST_COUNT: $(tail -1 "$SD/w/$id.propose.err")"; return 1; }
  call "w/$id.submit" "$MINI" workspace --action submit --dir "$NEWCOMER_WS" \
    --intent "$NEWCOMER_WS/proposals/$id/intent.json" --attempt "$NEWCOMER_WS/attempts/$id" \
    || { DETAIL="growth write $id refused at record $LAST_COUNT: $(tail -1 "$SD/w/$id.submit.err")"; return 1; }
  t1=$(now)
  accept "$NEWCOMER_WS/attempts/$id/outcome.json" || { DETAIL="growth write $id: ${DETAIL:-not installed}"; return 1; }
  echo "$GROW_N" >"$SD/f101"
  LAST_W=$(elapsed "$t0" "$t1")
  printf '%s\t%s\t%s\t%s\t%s\n' "$id" "$LAST_COUNT" "$(cwall "w/$id.propose")" "$(cwall "w/$id.submit")" "$LAST_W" >>"$SD/writes.tsv"
  gt "$LAST_W" 600 && { DETAIL="abort rule: one write took ${LAST_W}s (> 600 s) at record $LAST_COUNT"; return 1; }
  return 0
}
median5() { sort -g | awk '{a[NR]=$1} END{print a[3]}'; }
worst() { sort -g | tail -1; }

step_G() {
  local levels=${JOURNEY_GROWTH_LEVELS:-"10 100 500 1000"} budget=${JOURNEY_GROWTH_BUDGET_S:-10800}
  local L i t0 t1 wm ww rm rw bytes verdict="" over_prev=0 prev_wm="" g0
  g0=$(now)
  ARTIFACT=$SD/levels.tsv
  mkdir -p "$SD/w" "$SD/r"
  printf 'level\twrite_median_s\twrite_worst_s\tread_median_s\tread_worst_s\treopen_s\tstore_bytes\tsampled_records\tloadavg\n' >"$ARTIFACT"
  : >"$SD/writes.tsv"
  # Field 101 is created once; every later growth record is a scalar write to it.
  scalar shared create 101 0 >"$SD/w/create.json"
  call w/create.propose "$MINI" workspace --action propose --dir "$NEWCOMER_WS" --request "$SD/w/create.json" --proposal-id g0 \
    || fail "field 101 propose failed" || return
  call w/create.submit "$MINI" workspace --action submit --dir "$NEWCOMER_WS" \
    --intent "$NEWCOMER_WS/proposals/g0/intent.json" --attempt "$NEWCOMER_WS/attempts/g0" \
    || fail "field 101 create refused: $(tail -1 "$SD/w/create.submit.err")" || return
  accept "$NEWCOMER_WS/attempts/g0/outcome.json" || fail "field 101 create: $DETAIL" || return
  echo 0 >"$SD/f101"
  for L in $levels; do
    while [ "$LAST_COUNT" -lt "$L" ]; do
      gt "$(elapsed "$g0" "$(now)")" "$budget" && {
        fail "${verdict:+$verdict; }growth budget ${budget}s spent before reaching $L records (at $LAST_COUNT)"; return; }
      grow_write || return 1
    done
    : >"$SD/L$L.w"; : >"$SD/L$L.r"
    local first=$((LAST_COUNT + 1))
    for i in 1 2 3 4 5; do grow_write || return 1; echo "$LAST_W" >>"$SD/L$L.w"; done
    for i in 1 2 3 4 5; do
      t0=$(now)
      call "r/L$L-$i" "$MINI" workspace --action read --dir "$NEWCOMER_WS" --name shared \
        || fail "signed read refused at level $L" || return
      t1=$(now); echo "$(elapsed "$t0" "$t1")" >>"$SD/L$L.r"
      [ "$(field_value "$SD/r/L$L-$i.out" 101)" = "$(cat "$SD/f101")" ] || fail "read at level $L returned a stale field 101" || return
    done
    reopen "L$L" "$NEWCOMER_WS" shared || return 1
    wm=$(median5 <"$SD/L$L.w"); ww=$(worst <"$SD/L$L.w")
    rm=$(median5 <"$SD/L$L.r"); rw=$(worst <"$SD/L$L.r")
    bytes=$(du -sb "$W/store" | cut -f1)
    printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s-%s\t%s\n' "$L" "$wm" "$ww" "$rm" "$rw" "$REOPEN_S" "$bytes" "$first" "$LAST_COUNT" \
      "$(cut -d' ' -f1-3 /proc/loadavg 2>/dev/null)" >>"$ARTIFACT"
    echo "  growth level $L: write median ${wm}s worst ${ww}s, read median ${rm}s, reopen ${REOPEN_S}s, store $bytes B" >&2
    verdict="${verdict:+$verdict; }at $L: write ${wm}s, reopen ${REOPEN_S}s"
    if gt "$wm" 5 || gt "$REOPEN_S" 60; then
      # Early stop: two consecutive levels over the 1000-record thresholds with
      # the write cost rising between them. One level over is not enough (a
      # loaded machine can put a small Store over 5 s); a rising second level
      # says the cost comes from history. JOURNEY_GROWTH_FULL=1 measures on.
      if [ "$over_prev" = 1 ] && gt "$wm" "$prev_wm" && [ "${JOURNEY_GROWTH_FULL:-0}" != 1 ]; then
        fail "$verdict — two levels over the 1000-record thresholds (write <= 5 s, reopen <= 60 s), write x$(awk -v a="$prev_wm" -v b="$wm" 'BEGIN{printf "%.1f", b/a}') between them; stopped (JOURNEY_GROWTH_FULL=1 to continue)"; return
      fi
      over_prev=1
    else
      over_prev=0
    fi
    prev_wm=$wm
  done
  case " $levels " in *" 1000 "*) ;; *) fail "$verdict; level 1000 not in JOURNEY_GROWTH_LEVELS, so the exit is unmeasured"; return;; esac
  if gt "$wm" 5 || gt "$REOPEN_S" 60; then fail "$verdict — over thresholds"; return; fi
  DETAIL="$verdict — within thresholds"
}

step_J7() {
  local A=$SPONSOR_WS/attempts/law-v2 NA=$NEWCOMER_WS/attempts/after-law-v2
  ARTIFACT=$NA/outcome.json
  call describe-before "$MINI" workspace --action describe --dir "$SPONSOR_WS" --name shared || fail "describe failed" || return
  call propose "$MINI" workspace --action propose --dir "$SPONSOR_WS" --request "$REQ/law-v2.json" --proposal-id law-v2 \
    || fail "law propose failed: $(tail -1 "$SD/propose.err")" || return
  call submit "$MINI" workspace --action submit --dir "$SPONSOR_WS" --intent "$SPONSOR_WS/proposals/law-v2/intent.json" --attempt "$A" \
    || fail "law install refused: $(tail -1 "$SD/submit.err")" || return
  accept "$A/outcome.json" || fail "law not installed: $DETAIL" || return
  call describe-after "$MINI" workspace --action describe --dir "$SPONSOR_WS" --name shared || fail "describe failed" || return
  [ "$(jq -r .version "$SD/describe-after.out")" = $(( $(jq -r .version "$SD/describe-before.out") + 1 )) ] \
    || fail "policy version did not advance" || return
  jq -e '.predicate.type == "not"' "$SD/describe-after.out" >/dev/null || fail "installed law is not the new one" || return
  call read "$MINI" workspace --action read --dir "$NEWCOMER_WS" --name shared || fail "newcomer read refused after law change" || return
  scalar shared write 2 7 1 >"$REQ/j7-write.json"
  call npropose "$MINI" workspace --action propose --dir "$NEWCOMER_WS" --request "$REQ/j7-write.json" --proposal-id after-law-v2 \
    || fail "newcomer propose refused after law change" || return
  jq -e --arg c "$(jq -r .observeCapability "$NEWCOMER_WS/refs/shared.json")" '.grants[0].capability == $c' \
    "$NEWCOMER_WS/proposals/after-law-v2/intent.json" >/dev/null || fail "newcomer write does not present the J3 grant" || return
  call nsubmit "$MINI" workspace --action submit --dir "$NEWCOMER_WS" --intent "$NEWCOMER_WS/proposals/after-law-v2/intent.json" --attempt "$NA" \
    || fail "newcomer write refused after law change: $(tail -1 "$SD/nsubmit.err")" || return
  accept "$NA/outcome.json" || fail "newcomer write not installed: $DETAIL" || return
  call readback "$MINI" workspace --action read --dir "$NEWCOMER_WS" --name shared || fail "readback refused" || return
  [ "$(field_value "$SD/readback.out" 2)" = 7 ] || fail "readback field 2 = $(field_value "$SD/readback.out" 2)" || return
  DETAIL="law v$(jq -r .version "$SD/describe-after.out") not(any[]) installed (submit $(cwall submit)s); J3 grant wrote 1->7 (submit $(cwall nsubmit)s). The new law is still permit-all"
}

step_J8() {
  local A=$SPONSOR_WS/attempts/lockout NA=$NEWCOMER_WS/attempts/after-law-v2 root n=0 c
  ARTIFACT=$SD/refusals.tsv; : >"$ARTIFACT"
  call propose "$MINI" workspace --action propose --dir "$SPONSOR_WS" --request "$REQ/deny-all.json" --proposal-id lockout \
    || fail "deny-all propose failed" || return
  call submit "$MINI" workspace --action submit --dir "$SPONSOR_WS" --intent "$SPONSOR_WS/proposals/lockout/intent.json" --attempt "$A" \
    || fail "deny-all install refused: $(tail -1 "$SD/submit.err")" || return
  accept "$A/outcome.json" || fail "deny-all not installed: $DETAIL" || return
  call nread "$MINI" workspace --action read --dir "$NEWCOMER_WS" --name shared
  root=$(jq -r '.signing[0].authorityRoot // empty' "$(read_attempt nread)/challenge.json" 2>/dev/null)
  scalar shared write 2 8 7 >"$REQ/j8-write.json"
  call npropose "$MINI" workspace --action propose --dir "$NEWCOMER_WS" --request "$REQ/j8-write.json" --proposal-id after-lock
  craft "$NEWCOMER_WS/proposals/after-law-v2/intent.json" "$NEWCOMER_SUBJECT" "$root" >"$REQ/j8-newcomer-crafted.json"
  call ncrafted "$MINI" workspace --action submit --dir "$NEWCOMER_WS" --intent "$REQ/j8-newcomer-crafted.json"
  call sread "$MINI" workspace --action read --dir "$SPONSOR_WS" --name shared
  call srepair "$MINI" workspace --action propose --dir "$SPONSOR_WS" --request "$REQ/repair.json" --proposal-id repair
  for c in nread npropose ncrafted sread srepair; do
    if refused "$c"; then
      printf '%s\trefused\t%s\t%s\n' "$c" "$(reason "$c")" "$(decode "$c")" >>"$ARTIFACT"
    else
      printf '%s\tNOT-REFUSED\trc=%s\n' "$c" "$(cat "$SD/$c.rc")" >>"$ARTIFACT"; n=$((n + 1))
    fi
  done
  [ "$n" = 0 ] || fail "$n of 5 attempts under deny-all were not refused by the Host (see $ARTIFACT)" || return
  # A historical call still resolves to its original receipt, with no new effect.
  call lookup "$MINI" retry --attempt "$NA" --mode lookup || fail "historical lookup failed under lock" || return
  call resubmit "$MINI" retry --attempt "$NA" --mode submit || fail "historical resubmit failed under lock" || return
  replayed "$SD/resubmit.out" && [ "$(count_of "$SD/resubmit.out")" = "$(count_of "$NA/outcome.json")" ] \
    || fail "historical resubmit was not the original receipt" || return
  DETAIL="deny-all installed (submit $(cwall submit)s); 5/5 refused: newcomer read/propose/crafted(current root), sponsor read, sponsor repair propose; prior call replays"
}

# ---------------------------------------------------------------- K4 typed state

step_K4() {
  local A=$SPONSOR_WS/attempts/create-wide f i got=0 id
  ARTIFACT=$SD/fields.tsv; : >"$ARTIFACT"
  call create "$MINI" workspace --action create --dir "$SPONSOR_WS" --name wide --storage declared \
    --predicate "$REQ/permit-all.json" || fail "create wide refused: $(tail -1 "$SD/create.err")" || return
  accept "$A/outcome.json" || fail "wide not installed: $DETAIL" || return
  for i in $(seq 1 32); do
    f=$((200 + i)); id=wide-$f
    scalar wide create "$f" "$i" >"$REQ/$id.json"
    if ! call "p$f" "$MINI" workspace --action propose --dir "$SPONSOR_WS" --request "$REQ/$id.json" --proposal-id "$id"; then
      fail "field $i of 32 refused at propose: $(tail -1 "$SD/p$f.err" | cut -c1-200)"; return
    fi
    if ! call "s$f" "$MINI" workspace --action submit --dir "$SPONSOR_WS" --intent "$SPONSOR_WS/proposals/$id/intent.json" --attempt "$SPONSOR_WS/attempts/$id"; then
      printf '%s\t%s\trefused\n' "$i" "$f" >>"$ARTIFACT"
      local why; why=$(decode "s$f" | grep -o 'RejectReason\.[a-zA-Z]*' | tail -1)
      ARTIFACT=$SD/s$f.err
      fail "field $i of 32 refused by the Host (${why:-$(tail -1 "$SD/s$f.err" | cut -c1-160)}); the resource holds $((i)) entries incl. field 1"; return
    fi
    accept "$SPONSOR_WS/attempts/$id/outcome.json" || fail "field $i not installed: $DETAIL" || return
    printf '%s\t%s\tinstalled\n' "$i" "$f" >>"$ARTIFACT"
  done
  call read "$MINI" workspace --action read --dir "$SPONSOR_WS" --name wide || fail "wide read refused" || return
  for i in $(seq 1 32); do
    [ "$(field_value "$SD/read.out" $((200 + i)))" = "$i" ] && got=$((got + 1))
  done
  [ "$got" = 32 ] || fail "readback returned $got of 32 fields" || return
  DETAIL="32 fields created and read back under one root"
}

# ---------------------------------------------------------------- M3-M7 hooks

# hook ID EXIT-TEXT [MANIFEST-KEY]
hook() {
  local id=$1 exit_text=$2 need=${3:-} file rc
  file=$HERE/journey.d/$id.sh
  if [ ! -f "$file" ]; then
    DETAIL="UNBUILT: no journey.d/$id.sh. Green when: $exit_text"; return 3
  fi
  if [ -n "$need" ] && [ -z "$(mf "$need")" ]; then
    fail "journey.d/$id.sh exists but the manifest has no .$need"; return
  fi
  export JOURNEY_RUN=$RUN JOURNEY_WORLD=$W JOURNEY_STEP_DIR=$SD MINI HOST STORE VERIFIER CONFIG SOCKET \
    SPONSOR_WS NEWCOMER_WS SPONSOR_SUBJECT NEWCOMER_SUBJECT SHELL_BIN HERMES_BIN SPK_HOST_BIN CANDIDATE
  timeout "${HOOK_TIMEOUT_S:-3600}" "$file" >"$SD/hook.out" 2>"$SD/hook.err"
  rc=$?
  ARTIFACT=$(tail -1 "$SD/hook.out")
  DETAIL=$(tail -1 "$SD/hook.err")
  [ "$rc" = 0 ] || { DETAIL="hook exit $rc: $DETAIL"; return 1; }
  # The live service must still be ours and alive; a hook may not take it down.
  ours "$(server_pid)" || fail "hook left the journey service stopped" || return
}
step_JJ() { hook jjoint "a law on one participant reads joint/index/1/... of a two-target command, and is refused when position 1 is absent or holds a different cell (lane K-JOINT-INDEX)"; }
step_KC() { hook jclock "the one clock ticks forward only, under a capability, and a law over clock/now admits after the tick and refuses before (MUD item 3, K-CLOCK)"; }
step_J12X() { hook j12x "each malformed request (number for a decimal string, missing/extra field, negative index, NaN, truncated, non-UTF-8, 100k nesting, 10 MB, bad frames) is refused by name by the same Host process, which answers on; a Host killed by PID is restarted under the same socket (lane host-malformed)"; }
step_JSERVE() { hook jserve "under each attack (3 bytes then silence; a long Host request; 50 silent connections; the J-PAY-6 route-mismatch intent through op 7) the newcomer signed read is answered (< 2 s where the Host is free), every refusal is named, the same Host answers on, and the malformed table still holds (lane serve-robust)"; }
step_M3() { hook m3 "a key generated outside the sponsor's workspace provisions itself and creates a resource with no sponsor step and no operator edit (list item 3, lane m3-provision)"; }
step_M4() { hook m4 "J1-J8 run from an ssh session through the shell over the client contract (list item 4, lane m4-shell)" shell; }
step_M5() { hook m5 "Hermes performs J4 through the client contract on this Store, is killed mid-attempt, restarts, and the attempt resolves performed/refused/uncertain (list item 5, lane m5-hermes)" hermes; }
step_M6() { hook m6 "a non-Git SPK profile goes INSTALL -> START -> answers curl through the ordinary mechanism (list item 6, lane m6-grain)" spkHost; }
step_J12() { hook j12 "friends provisioned from the shell co-write a doc (append, edit with the read line as guard, link, backlinks, board, revoke); a stale edit, a third key, a reviewer's write, an append-only edit, a backwards task and a revoked read are refused by the Host with their reason (PLACE item 1)" shell; }
step_J12C() { hook j12c "B quotes a range of commons/wall into lab/paper; C (commons only) is refused no-grant reading the quote; A reads the quoted bytes; A's doc follow is refused no-grant (PLACE §2.4)" shell; }
step_K10() { hook j10-kernel "K-ROOM 3b rows: a note born --in lab is read through under lab by its owner and an invitee; an outside cell, a third key with either capability, a signature-only read and a birth into a ghost room are refused (lane k-world)"; }
step_K11() { hook j11-kernel "K-STREAM rows: per-author streams born in a room, six appends planned before submission admitted with zero re-plans, a non-member and a forged author refused, tail identical across a restart (lane k-stream)"; }
step_KIX() { hook j10-index "K-INDEX rows: who lists members with their last visible write, since lists only later writes, at differs across a write above and below the checkpoint and equals the read now, a height above now is refused, a cold reopen prints the same index (lane k-index)"; }
step_KF() { hook jfields "K-FIELDS rows: maxDelta bounds a field move per write, a scope naming fields refuses a write to another and narrows reads to the named fields, re-delegation must narrow, a reviewer annotates but cannot edit the body (lane k-fields)"; }
step_K12C() { hook j12c-kernel "K-CONTENT rows: a reviewer annotates but cannot edit, an annotation goes stale after an edit, quotes and transclusions install with backlinks and render only through the reader own read (lane k-content)"; }
step_KHQ() { hook jhasheq "K-HASHEQ rows: a sealed bid commits a full-width cSHAKE256 digest, the right opening installs, a wrong opening or a reveal before the deadline is refused, the plaintext is on the Store only after the reveal (lane k-hasheq)"; }
step_KW() { hook jwell "K-WELL rows: the referee mints by grant and law, no-grant, law-refused, overburn, credit-asset and rootless mints refused by name in the operator log, conservation and the cold audit ledger equal (lane k-well)"; }
step_JN2() { hook jnock2 "J-NOCK-2b: forge is checked and born at its content address, show/sample read it back, a padded jam is refused (lane k-nock; needs NOCK_TEMPLATES, NOCK_RUN)"; }
step_JN3() { hook jnock3 "J-NOCK-3: a write under ran forge is admitted only with a run claim the kernel re-executes; forged output, low fuel and a direct write refused (lane k-ran; needs NOCK_TEMPLATES, NOCK_RUN)"; }
step_JN5() { hook jnock5 "J-NOCK-5: the hoonc counter kernel is born as a door, pokes are refereed by re-execution, a stale state and a non-write effect refused (lane n11; needs NOCK_DOOR_JAM, NOCK_DOOR_FUEL)"; }
step_JPAY3() { hook jpay3 "J-PAY-3: observed payments credit exactly, a heartbeat advances the clock cell slot, a tip behind the clock and the named refusals, the audit identity (lane p3-pay)"; }
step_JPAYE1() { hook jpay-e1 "J-PAY-E1: the watcher enrollment-index vectors (lane p1b-enroll)"; }
step_JPAYE2() { hook jpay-e2 "J-PAY-E2: the self-enrollment decision with real signatures, the enrollment view, the observer replaced (lane p3b1)"; }
step_JPAYE3() { hook jpay-e3 "J-PAY-E3: the self-enrollment receiver enrols, renews and journals (lane p3b2)"; }
step_JPAY4() { hook jpay4 "J-PAY-4: the payment rail through mini pay with the fixture watcher (lane p4-pay)"; }
step_JPAY6() { hook jpay6 "J-PAY-6: a Book burn funds an AgentGrain purse in one joint turn (lane p6-pay; hbox: needs GRAIN, TEST_PROVIDER, LAUNCH_GATE and passwordless sudo)"; }
step_JJOBM() { hook jjob-money "J-JOB-MONEY: fund, claim and settle move Book credit with the job cell escrow and bond equal to the held account, refusals named in the operator log (lane C3 K-JOB-MONEY; ops 160-163)"; }
step_JSYNC() { hook jsync "nockFSync (default 1,000,000): a 1,000,000-step run admitted, 1,000,010 and 1,000,001 refused overSyncBudget by name, the lifetime proofWork meter refusal named in the operator log (lane hot-path)"; }
step_BD() { hook bind "two plans on disjoint cells are admitted in both orders without re-plan; a second plan on the same cell is refused (lane c-bind)"; }
step_M8() { hook m8 "fleet-journey.sh: fee'd fleet turns, a topic event stream and agent heads on its own fresh Store (list item 8, lane m8-fleet-surface)"; }
step_J13() { hook j13 "law-leaf-journey.sh: a write the law rejects is refused at submit with the failing clause named, on its own fresh Store (lane p-law, J13)" shell; }
step_JJOB1() { hook jjob1 "the job law (COMPUTE §2.3, deploy/shell/templates/job) installs on fresh cells; every edge is admitted with the right subject and time and refused with the wrong one, each refusal naming its clause (lane C1 JOB-LAW; the run slot is a hand-set stand-in on this tree, no K-RAN)"; }
step_J12A() { hook j12a "affordances-journey.sh: can NAME lists the verbs my grants cover, each prepared and dry-run (Host op 130) with the clause on a law refusal; root, height and audit unchanged around every can (lane p-affordances, J12A)" shell; }
step_JPAY1() { hook jpay1 "finalized Solana transfers in fixtures become Observation records; disagreement and failed transactions refused (lane p1-watcher, J-PAY-1)"; }
step_JPAY2() { hook jpay2 "the pay cell on its own fresh Store: tariff, 64-row book, assignments, refusals (uniform), lookup, reopen, audit (lane p2-pay, J-PAY-2)"; }
step_M7() { hook m7 "a candidate built from portable interfaces reproduces the pinned hashes and runs this journey with no private fixture (list item 7, lane m7-candidate)" candidate; }
step_JP2() { hook jpriv2 "a subject enrolled from its own machine creates, writes, reads and delegates through mini --remote; no key of it on the box; a tampered frame is refused (J-PRIV-2, lane local-client)"; }

# ---------------------------------------------------------------- run

run_step J0
run_step J1 J0
run_step J2 J0
run_step J3 J1 J2
run_step J12X J3
run_step J4 J3
run_step JSERVE J4
run_step J5 J4
run_step J6 J4
run_step G J4
run_step J7 J4
run_step J8 J7
run_step K4 J2
run_step KC J2
run_step JJ J2
run_step K10 J5
run_step K11 J5
run_step KIX K10
run_step KF J5
run_step K12C J5
run_step KHQ J4
run_step KW J5
run_step JN2 J0
run_step JN3 J0
run_step JN5 J0
run_step JSYNC J0
run_step M3 J0
run_step M4 J0
run_step M5 J0
run_step M6 J0
run_step M7 J0
run_step M8 J0
run_step BD J2
run_step J12 J0
run_step J12C J0
run_step J13 J0
run_step JJOB1 J4
run_step JJOBM J0
run_step J12A J0
run_step JPAY1 J0
run_step JPAY2 J0
run_step JPAY3 J0
run_step JPAYE1 J0
run_step JPAYE2 J0
run_step JPAYE3 J0
run_step JPAY4 J0
run_step JPAY6 J0
run_step JP2 J0

stop_server || echo "journey: could not stop the service cleanly" >&2
trap - EXIT
F=$(frontier)
result_json "$F"

printf '\n%-3s  %-7s  %9s  %s\n' step status wall_s "what / detail / deciding artifact"
jq -r '.steps[] | [.id, .status, .wallSeconds, .title, .detail, .artifact] | join("\u001f")' "$RUN/journey-result.json" \
| while IFS=$'\x1f' read -r id st wall title det art; do
    printf '%-3s  %-7s  %9s  %s\n' "$id" "$st" "$wall" "$title"
    [ -n "$det" ] && printf '%26s%s\n' "" "$det"
    [ -n "$art" ] && printf '%26s-> %s\n' "" "$art"
  done
printf '\nFRONTIER: %s   (accepted records: %s; load average start/end: %s / %s on %s CPUs; result: %s)\n' \
  "$F" "$LAST_COUNT" "$LOAD_START" "$(cut -d' ' -f1-3 /proc/loadavg 2>/dev/null)" "$(nproc 2>/dev/null)" "$RUN/journey-result.json"
[ "$F" = END ]
