#!/bin/sh
# spk-survey.sh: run real Sandstorm market packages through the grain host,
# one Store, one app after another, each through the ordinary lifecycle:
# birth, install (size class), share (owner session of its kind), START
# under the floor, floor probe, enrollment, GET, one write, STOP, continue
# (START again), floor, enrollment, and the write read back.
#
#   spk-survey.sh RUN_ROOT APPS_TSV [LETTER...]
#
# APPS_TSV, one app per line, tab-separated (empty field = "-"):
#   letter prefix name spk class kind get_path post_method post_path post_type
#   post_body poll_path poll_expect
# A step that fails is recorded and the app's dependent steps are skipped;
# the next app still runs. Every verdict comes from an artifact: the step's
# exit (grain-journey keeps stdout/stderr/exit/seconds per step), the HTTP
# status curl wrote, the floor probe's /proc lines, the cgroup's own counters.
# Results: RUN_ROOT/survey.tsv (app step verdict seconds detail) and
# RUN_ROOT/metrics/<name>.json. Runs as the Store operator; the broker serves.
# Environment: BIN SPK GRAINS_ROOT (as grain-journey.sh); SURVEY_PASS=1 runs
# through the first GET and leaves the grain serving, SURVEY_PASS=2 resumes
# from the write; unset runs both.
set -eu
umask 077
SURVEY_PASS=${SURVEY_PASS:-all}
ALL_ACCESS='{"type":"allAccess"}'
[ "$#" -ge 2 ] || { sed -n '2,20p' "$0" >&2; exit 2; }
RUN=$1 APPS=$2
shift 2
HERE=$(CDPATH='' cd -- "$(dirname -- "$0")" && pwd)
J=$HERE/grain-journey.sh
EV=$RUN/evidence
OUT=$RUN/survey.tsv
mkdir -p -m 700 "$RUN" "$RUN/metrics"
[ "$(id -u)" != 0 ] || { echo "spk-survey: run as the Store operator" >&2; exit 2; }

record() { printf '%s\t%s\t%s\t%s\t%s\n' "$1" "$2" "$3" "$4" "$5" | tee -a "$OUT"; }
# phase NAME STEP: one grain-journey phase; PASS iff its step exited 0.
phase() {
  name=$1 st=$2
  set +e
  "$J" phase "$RUN" "$st" >/dev/null 2>"$RUN/metrics/$name-$st.err"
  rc=$?
  set -e
  secs=$(cat "$EV/$st.seconds" 2>/dev/null || echo -)
  if [ "$rc" = 0 ]; then
    record "$name" "$st" PASS "$secs" "$(tail -n 1 "$EV/$st.stdout" 2>/dev/null | cut -c1-200)"
  else
    record "$name" "$st" FAIL "$secs" "$(tail -n 2 "$EV/$st.stderr" "$RUN/metrics/$name-$st.err" 2>/dev/null | grep -v '^==' | grep . | tail -n 1 | cut -c1-300)"
  fi
  return "$rc"
}
profile() {
  for p in "$GRAINS_ROOT"/*/host/grain-host.json; do
    [ -r "$p" ] || continue
    [ "$(jq -r .miniConfig "$p")" = "$RUN/store/base/workroom/deployment/pinned-config.json" ] &&
      { echo "$p"; return 0; }
  done
  return 1
}
# metrics NAME APP TAG: the running generation's cgroup counters.
metrics() {
  name=$1 app=$2 tag=$3
  unit=$("$BIN/spk-host" grain status "$(profile)" "$app" |
    jq -er '[.runs[] | select(.state == "running")][-1].unit') || return 0
  cg=/sys/fs/cgroup$(systemctl show "$unit" --property=ControlGroup --value)
  slice=$(systemctl show "$unit" --property=Slice --value)
  jq -n --arg unit "$unit" --arg slice "$slice" --arg tag "$tag" \
    --arg peak "$(cat "$cg/memory.peak" 2>/dev/null || echo -)" \
    --arg current "$(cat "$cg/memory.current" 2>/dev/null || echo -)" \
    --arg pidsPeak "$(cat "$cg/pids.peak" 2>/dev/null || echo -)" \
    --arg procs "$(wc -l <"$cg/cgroup.procs" 2>/dev/null || echo -)" \
    --arg threads "$(wc -l <"$cg/cgroup.threads" 2>/dev/null || echo -)" \
    --arg memMax "$(cat "/sys/fs/cgroup/$(systemctl show "$slice" --property=ControlGroup --value)/memory.max" 2>/dev/null || echo -)" \
    --arg names "$(for p in $(cat "$cg/cgroup.procs"); do sed -n 's/^Name:[[:space:]]*//p' /proc/$p/status 2>/dev/null; done | sort | uniq -c | tr -s ' ' | paste -sd, -)" \
    '{tag:$tag,unit:$unit,slice:$slice,memoryPeak:$peak,memoryCurrent:$current,
      pidsPeak:$pidsPeak,procs:$procs,threads:$threads,sliceMemoryMax:$memMax,processNames:$names}' \
    >"$RUN/metrics/$name-$tag.json"
  record "$name" "metrics-$tag" PASS - "$(jq -c '{memoryPeak,pidsPeak,procs,processNames}' "$RUN/metrics/$name-$tag.json")"
}
# settle NAME APP STEP: `grain start` gave up waiting (its 900 s bound) while
# the resident may still be completing. No other write may race it on this
# Store (a completion that loses its CAS is refused `contention` and the
# START wedges claimed), so wait, bounded, until the run is serving or its
# unit is gone.
settle() {
  name=$1 app=$2 st=$3 t0=$(date +%s)
  while :; do
    run=$("$BIN/spk-host" grain status "$(profile)" "$app" | jq -c '.runs[-1]') || run=null
    state=$(printf '%s' "$run" | jq -r '.state // "none"')
    active=$(printf '%s' "$run" | jq -r '.unitActiveState // "none"')
    if [ "$state" = running ]; then
      record "$name" "$st-settled" PASS "$(( $(date +%s) - t0 ))" "START completed after the operator wait: $run"
      return 0
    fi
    case "$active" in active|activating) ;; *)
      record "$name" "$st-settled" FAIL "$(( $(date +%s) - t0 ))" "$run"; return 1 ;;
    esac
    [ "$(( $(date +%s) - t0 ))" -lt 1800 ] || { record "$name" "$st-settled" FAIL 1800 "$run"; return 1; }
    sleep 15
  done
}
http_verdict() {
  name=$1 st=$2
  code=$(tail -n 1 "$EV/$st.stdout" 2>/dev/null || echo -)
  bytes=$(wc -c <"$EV/$st-body.body" 2>/dev/null || echo 0)
  record "$name" "$st-http" "$code" - "bytes=$bytes $(head -c 160 "$EV/$st-body.body" 2>/dev/null | tr '\n\t\r' '   ')"
}

# The Store once.
[ -e "$RUN/store" ] || phase store store || exit 1
"$J" phase "$RUN" services workroom profile >/dev/null

tab=$(printf '\t')
while IFS="$tab" read -r letter prefix name spk class kind getp postm postp postt postb pollp pollx; do
  case "$letter" in ''|'#'*) continue ;; esac
  if [ "$#" -gt 0 ]; then
    case " $* " in *" $letter "*) ;; *) continue ;; esac
  fi
  U=$(printf '%s' "$letter" | tr a-i A-I)
  export "GRAIN_$U=$prefix" "SPK_$U=$spk" "CLASS_$U=$class" "KIND_$U=$kind" "GET_PATH_$U=$getp"
  [ "$postp" = - ] || export "POST_PATH_$U=$postp" "POST_METHOD_$U=$postm" "POST_TYPE_$U=$postt" "POST_BODY_$U=$postb"
  [ "$pollp" = - ] || export "POLL_PATH_$U=$pollp"
  # The grain owner holds every permission (Sandstorm's owner semantics);
  # role 0 is an app's first declared role, which can be view-only (Davros)
  # or absent (Roundcube, Gogs declare no roles).
  export "ROLE_BASIS_$U=${SURVEY_ROLE_BASIS:-$ALL_ACCESS}"
  app=${prefix}01
  if [ "$SURVEY_PASS" != 2 ]; then
  record "$name" package INFO - "$(sha256sum "$spk" | cut -c1-32) $(stat -c %s "$spk")B class=$class kind=$kind app=$app"
  phase "$name" "birth-$letter" || continue
  phase "$name" "install-$letter" || continue
  phase "$name" "share-$letter" || continue
  phase "$name" "start-$letter" || settle "$name" "$app" "start-$letter" ||
    { metrics "$name" "$app" start-failed; continue; }
  phase "$name" "floor-$letter" || :
  phase "$name" "enroll-$letter" || { metrics "$name" "$app" g1; phase "$name" "stop-$letter" || :; continue; }
  phase "$name" "get-$letter" || :
  http_verdict "$name" "get-$letter"
  metrics "$name" "$app" g1-get
  # Pass 1 leaves the grain serving so its write can be worked out.
  [ "$SURVEY_PASS" != 1 ] || continue
  fi
  if [ "$postp" != - ]; then
    phase "$name" "post-$letter" || :
    http_verdict "$name" "post-$letter"
  fi
  metrics "$name" "$app" g1
  phase "$name" "stop-$letter" || continue
  phase "$name" "start-${letter}2" || settle "$name" "$app" "start-${letter}2" || continue
  phase "$name" "floor-${letter}2" || :
  phase "$name" "enroll-${letter}2" || { phase "$name" "stop-${letter}2" || :; continue; }
  if [ "$pollp" != - ]; then
    phase "$name" "poll-${letter}2" || :
    http_verdict "$name" "poll-${letter}2"
    if [ "$pollx" != - ] && grep -qF -- "$pollx" "$EV/poll-${letter}2-body.body" 2>/dev/null; then
      record "$name" survived PASS - "after STOP + continue the write reads back: $pollx"
    else
      record "$name" survived FAIL - "expected text not in the poll body: $pollx"
    fi
  else
    phase "$name" "get-${letter}2" || :
    http_verdict "$name" "get-${letter}2"
  fi
  metrics "$name" "$app" g2
  # SURVEY_FINAL_STOP=0 leaves the continued generation serving (the
  # operator stops it later); each Mini STOP costs minutes of Host replay.
  [ "${SURVEY_FINAL_STOP:-1}" = 0 ] || phase "$name" "stop-${letter}2" || :
done <"$APPS"
echo "$OUT"
