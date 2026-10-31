#!/bin/bash
# apps-e2e.sh WORLD.env OUT_DIR APP-ID [APP-ID...]: the first real `mini apps install`, end to end,
# on a standing world (world-up.sh), as the member turn docs/APP-MARKET-2026-10-27.md §3 describes:
#   - the manager (the workroom's subject 8, tool.key) and a member (the workroom's subject 9,
#     member.key) each get a workspace over their own key and birth context;
#   - the manager imports the world's metered tool and parent references and delegates observe and
#     the grain operation on both to the member (`delegate`, `submit`, `publish`), leaving the
#     recipient references in the member's HOME/inbox exactly as mini-reenroll's apps_member_grants
#     does on the box;
#   - apps.json (mini-apps-config-v1) and the worker's apps-world.json are written; the worker runs
#     (its PID in OUT/worker.pid) with --dev-member member (no mini-s-* accounts on a lane box);
#   - the member runs `mini apps install` for each APP-ID over the recorded index with the packages
#     pre-seeded in a quarantine (MINI_MARKET_CACHE), retrying on `fetching`/`undecided` until
#     decided, then `apps list`, `apps status`, `apps open`;
#   - the origin check: one authenticated GET through the grain's route socket with the route's
#     browser cookie and the grain's Host, as the edge would send it.
# Every step is one real verb; nothing is faked. Stop the worker by its PID file only.
#
# Knobs (environment), so a sibling row (joracle.sh) runs the same path with another package:
#   APPS_E2E_INDEX     the catalogue to install from (default: the recorded fixture; joracle: fixture + the pin)
#   APPS_E2E_CLASS     the member's class choice (default S; the oracle needs L)
#   APPS_E2E_ATTEMPTS  install retries, 15 s apart (default 20; the operator-appliance import budget needs 130)
#   APPS_E2E_GET_PATH  the authenticated GET's path (default /; the oracle bridge serves /health)
#   APPS_E2E_POST      "PATH|CONTENT-TYPE|BODY-FILE": one authenticated POST after the GET, body kept in OUT/<grain>.post.body
#   APPS_E2E_STOP=1    `mini apps stop` the grain at the end and check it is decided stopped
#   APPS_E2E_BOOTSTRAP=1  the world's metered tasks are the ones `mini apps bootstrap` births and activates
#                      for the manager (a fresh world's first install), not the workroom's pre-activated 7901/7902
#   APPS_E2E_RESTART=1 on Hacker Slides: write through the route, restart (stop, start: generation +2), write
#                      again with NO enroll step, `mini apps renew` says current, then an operator-direct restart
#                      (spk-host grain stop/start, which skips the worker's enroll) is refused by name until renew
set -uo pipefail
umask 077
[[ $# -ge 3 ]] || { echo "usage: $0 WORLD.env OUT_DIR APP-ID [APP-ID...]" >&2; exit 2; }
env_file=$1 out=$2; shift 2
# shellcheck disable=SC1090
. "$env_file"
here=$(cd "$(dirname "$0")" && pwd)
repo=$(cd "$here/../.." && pwd)
FIXTURE=${APPS_E2E_INDEX:-$repo/native/resource-client/tests/fixtures/sandstorm-index-2026-10-27.json}
CLASS=${APPS_E2E_CLASS:-S} ATTEMPTS=${APPS_E2E_ATTEMPTS:-20} GET_PATH=${APPS_E2E_GET_PATH:-/}
[[ ! -e $out ]] || { echo "fresh OUT_DIR required" >&2; exit 2; }
mkdir -m 700 "$out"
# The consent and codec residents this run's `mini` calls start keep their anchors and PID files in
# OUT/a, and stop_residents ends them at exit: their settings live under OUT, which world-down never
# touches, so nothing would otherwise stop them.
export MINI_CONSENT_ANCHOR_DIR="$out/a"; mkdir -m 700 "$MINI_CONSENT_ANCHOR_DIR"
stop_worker() { [ -f "$out/worker.pid" ] && kill "$(cat "$out/worker.pid")" 2>/dev/null; rm -f "$out/worker.pid"; }
stop_residents() { bash "$here/stop-residents.sh" "$out" >&2; rm -f "$out"/ws-*/attempts/*/config.json; }
cleanup() { stop_worker; stop_residents; }
trap cleanup EXIT
rows=0 fails=0
row() { rows=$((rows + 1)); if [ "$2" = 1 ]; then printf 'PASS\t%s\t%s\n' "$1" "$3"; else fails=$((fails + 1)); printf 'FAIL\t%s\t%s\n' "$1" "$3"; fi; }
verdict() { local v="J-APPS-E2E PASS $rows/$rows"; [ "$fails" = 0 ] || v="J-APPS-E2E FAIL $fails/$rows"; echo "$v"; echo "$v" >&2; [ "$fails" = 0 ]; }
# The client under test is the lane's current `mini` (E2E_MINI), not the world's pinned copy: the
# world's Host, broker and spk-host stay as world-up left them; the member verbs and the worker are
# what this script exercises.
MINI=${E2E_MINI:-$BIN/mini}
WR=$RUN/store/base/workroom
GENESIS=$WR/genesis.json
[[ -f $GENESIS && -f $WR/tool.key && -f $WR/member.key ]] || { echo "the world's workroom lacks genesis.json, tool.key or member.key" >&2; exit 1; }
# `--socket` is a client option after the command (never before it).
mini() { "$MINI" "$@" --socket "$PSOCK"; }   # the Host socket last: `mini apps ACTION` wants the action right after the verb

# ---- two workspaces over the workroom's own keys ----------------------------------------------
context() { # SUBJECT FACTORY-CAP ACCOUNT-CAP -> file
  local s=$1 fcap=$2 acap=$3 f=$out/context-$1.json
  jq -n --slurpfile g "$GENESIS" --arg s "$s" --arg f "$fcap" --arg a "$acap" '
    {type:"minidregg-participant-birth-context-v1",genesis:$g[0],template:{issuer:"5",ownerBudget:"100000",lifetime:"10000"},
     feePayer:$s,sourceCapabilities:[$a],funding:[],
     grants:[{kind:"object",target:"10",capability:$f},{kind:"account",target:$s,capability:$a}]}' >"$f"
  echo "$f"
}
init_ws() { # NAME SUBJECT KEY CONTEXT  (the workroom's records commit to no next key: --no-prerotation)
  local ws=$out/ws-$1 home=$out/home-$1
  mkdir -m 700 -p "$home/inbox" "$out/ns-$1"
  mini workspace --action init --dir "$ws" --host "$HOST" --config "$CONFIG" --key "$3" --subject "$2" \
    --birth-context "$4" --namespace-root "$out/ns-$1" --no-prerotation >"$out/init-$1.out" 2>"$out/init-$1.err"
  [[ -f $ws/workspace.json ]]
}
# With APPS_E2E_BOOTSTRAP the manager pays the bootstrap birth from a funded account of its own, provisioned
# by the sponsor the way the member's is below, so the manager workspace is initialised after that.
manager_row() { row "manager workspace (subject 8) over the workroom's tool key" "$([ -f "$out/ws-manager/workspace.json" ] && echo 1 || echo 0)" "$(tail -1 "$out/init-manager.err" 2>/dev/null | cut -c1-120)"; }
if [ "${APPS_E2E_BOOTSTRAP:-0}" != 1 ]; then init_ws manager 8 "$WR/tool.key" "$(context 8 55 42)"; manager_row; fi
init_ws controller 7 "$WR/controller.key" "$(context 7 54 41)"; row "controller workspace (subject 7, the parent task's owner) over the workroom's controller key" "$([ -f "$out/ws-controller/workspace.json" ] && echo 1 || echo 0)" "$(tail -1 "$out/init-controller.err" 2>/dev/null | cut -c1-120)"
# The member is funded the way the door funds one (dregg-infra mini-reenroll): the sponsor (the
# factory's controller, 7) provisions a funded account for the holder through the factory and
# hands it the birth context; the member's own account pays for its app births.
# The grant bound and the funding the door gives (deploy/market/INSTALL.md): the metered birth charges
# more than 1000 under the delegated tool task, so a 1000 bound is refused no-grant at the birth.
MEMBER_FUNDING=${MEMBER_FUNDING:-20000}
gsrc=$RUN/store/base/workroom/deployment/genesis-source.json
mini workspace --action import --dir "$out/ws-controller" --name factory --kind object --target "$(jq -er .factoryId "$gsrc")" \
  --observe-capability 54 --control-capability "$(jq -er .factoryControllerCapability "$gsrc")" >"$out/import-factory.out" 2>&1
printf '%s\n' '{"type":"all","predicates":[]}' >"$out/permit-all.json"
mini workspace --action provision --dir "$out/ws-controller" --name member9 --holder 9 --funding "$MEMBER_FUNDING" \
  --account-predicate "$out/permit-all.json" --factory-ref factory >"$out/provision.out" 2>"$out/provision.err"
MEMBER_CONTEXT=$out/ws-controller/provisions/member9/birth-context.json
row "the sponsor provisions the member a funded account ($MEMBER_FUNDING), as the door does" "$([ -s "$MEMBER_CONTEXT" ] && echo 1 || echo 0)" "$(jq -r '.account.target // empty' "$out/provision.out" 2>/dev/null) $(tail -1 "$out/provision.err" | cut -c1-140)"
if [ "${APPS_E2E_BOOTSTRAP:-0}" = 1 ]; then
  mini workspace --action provision --dir "$out/ws-controller" --name manager8 --holder 8 --funding "${MANAGER_FUNDING:-100000}" \
    --account-predicate "$out/permit-all.json" --factory-ref factory >"$out/provision-manager.out" 2>"$out/provision-manager.err"
  init_ws manager 8 "$WR/tool.key" "$out/ws-controller/provisions/manager8/birth-context.json"; manager_row
fi
init_ws member 9 "$WR/member.key" "$MEMBER_CONTEXT"; row "member workspace (subject 9) over the workroom's member key, from the provisioned birth context" "$([ -f "$out/ws-member/workspace.json" ] && echo 1 || echo 0)" "$(tail -1 "$out/init-member.err" 2>/dev/null | cut -c1-120)"
WSM=$out/ws-manager WSC=$out/ws-controller WS9=$out/ws-member HOME9=$out/home-member

# ---- the factory admits the member's grain-backed birth, as the demo's genesis does -------------
# The workroom admits births only from its controller (7) and grain-backed ones from its worker
# (8); the candidate genesis pins factoryPredicate `all []`, so on the demo every member's births
# pass the factory (the app birth is grain-backed, the request cell an ordinary declared birth).
# The controller installs the next version with that clause replaced by the demo's own base
# `all []`, the ticker/observer/pay-claim wrapper kept. A signed policy read, then install-source
# under the read's exact root.
widen_factory() {
  local d=$out/factory-law key n1 n2 n3 gs=$RUN/store/base/workroom/deployment/genesis-source.json fsub fcap
  mkdir -m 700 -p "$d"; key=$(jq -r .key "$WSC/workspace.json")
  # The factory's controller and its control capability, from the world's own genesis (54 is only the
  # controller's observe grant; the workroom's control capability is 53).
  fsub=$(jq -er '.factoryControllerSubject' "$gs") && fcap=$(jq -er '.factoryControllerCapability' "$gs") || { echo "no factory controller in $gs" >"$d/intent.err"; return 1; }
  [ "$fsub" = 7 ] || { echo "factoryControllerUnexpected: $fsub is not the controller workspace's subject 7" >"$d/intent.err"; return 1; }
  n1=$(od -An -N4 -tu4 /dev/urandom | tr -d ' '); n2=$(od -An -N4 -tu4 /dev/urandom | tr -d ' '); n3=$(od -An -N4 -tu4 /dev/urandom | tr -d ' ')
  jq -n --arg n "$n1" '{subject:"7",nonce:$n,purpose:{type:"query",kind:"object",target:"10",view:"policy"},grants:[{kind:"object",target:"10",capability:"54"}]}' >"$d/query-intent.json"
  mini query --host "$HOST" --config "$CONFIG" --intent "$d/query-intent.json" --key "$key" --view policy --dir "$d/query" >"$d/query.out" 2>"$d/query.err" || return 1
  jq -n --slurpfile p "$d/query/view.json" --slurpfile c "$d/query/challenge.json" --arg n "$n2" --arg dn "$n3" --arg fcap "$fcap" '
    def eq($s;$v): {slot:$s,type:"eq",value:$v};
    def pinned: {predicates:[eq("request/subject";"7"),{predicates:[eq("request/subject";"8"),{predicates:[eq("request/verb";"1"),eq("birth/mode/grain-backed";"1")],type:"any"}],type:"all"}],type:"any"};
    def grainonly: {predicates:[eq("request/subject";"7"),{predicates:[eq("request/verb";"1"),eq("birth/mode/grain-backed";"1")],type:"any"}],type:"any"};
    def demo: {predicates:[],type:"all"};
    def count($x): [.. | select(. == $x)] | length;
    $p[0] as $p | $c[0] as $c |
    ($p.predicate | count(pinned) + count(grainonly)) as $old |
    if $old == 0 and ($p.predicate | [.. | objects | select(.slot? == "request/subject" and .value? == "8")] | length) == 0 then {already:true}
    elif $old != 1 then error("factoryLawUnrecognized: the workroom birth clause is not present exactly once")
    else {subject:"7",nonce:$n,purpose:{type:"prepare",draft:{type:"install-source",subject:"7",control:$fcap,
      declaration:{expectedPreRoot:$c.authorityRoot,expected:{version:$p.version,address:$p.address},nonce:$dn,
        source:{policyId:$p.policyId,version:(($p.version|tonumber)+1|tostring),domain:$p.domain,semantics:$p.semantics,
          previous:$p.address,predicate:($p.predicate | walk(if . == pinned or . == grainonly then demo else . end))}}}},
      grants:[{kind:"object",target:"10",capability:"54"}]} end' >"$d/intent.json" 2>"$d/intent.err" || return 1
  jq -e '.already == true' "$d/intent.json" >/dev/null && { echo already; return 0; }
  mini submit --host "$HOST" --config "$CONFIG" --intent "$d/intent.json" --key "$key" --dir "$d/submit" >"$d/submit.out" 2>"$d/submit.err" || return 1
  echo "version $(jq -r .purpose.draft.declaration.source.version "$d/intent.json")"
}
fl=$(widen_factory) && ok=1 || ok=0
row "the controller sets the scratch factory's birth clause to the demo genesis base (all [])" $ok "${fl:-$(tail -1 "$out/factory-law/"*.err 2>/dev/null | cut -c1-160)}"

# ---- a fresh world's metered tasks: `mini apps bootstrap` (APPS_E2E_BOOTSTRAP=1) --------------------
if [ "${APPS_E2E_BOOTSTRAP:-0}" = 1 ]; then
  mini apps bootstrap --dir "$WSM" --budget "${BOOTSTRAP_BUDGET:-5000}" >"$out/bootstrap.out" 2>"$out/bootstrap.err"
  act=1
  for step in tool-attach parent-attach parent-reserve; do
    jq -e '.type == "confirmed"' "$WSM/attempts/apps-activate-$step/outcome.json" >/dev/null 2>&1 || act=0
  done
  row "apps bootstrap births the tool and parent tasks and activates them (tool attach, parent attach, parent reserve 1: all admitted)" \
    "$([ -f "$WSM/refs/tool.json" ] && [ -f "$WSM/refs/parent.json" ] && [ "$act" = 1 ] && echo 1 || echo 0)" \
    "tool $(jq -r .toolTask "$out/bootstrap.out" 2>/dev/null) parent $(jq -r .parentTask "$out/bootstrap.out" 2>/dev/null) $(tail -1 "$out/bootstrap.err" | cut -c1-120)"
fi

# ---- the metered tasks' owners delegate observe+mutate to the member -------------------------------
# The workroom's tool (7902) is owned by subject 8 (capability 81), its parent (7901) by the
# controller 7 (capability 71; 8 holds only the management capability 73, which cannot delegate).
# On the box both are the sponsor's, born by mini apps bootstrap; here each owner delegates its own.
if [ "${APPS_E2E_BOOTSTRAP:-0}" != 1 ]; then
  mini workspace --action import --dir "$WSM" --name tool --kind object --target 7902 --observe-capability 81 --operation-capability 81 >"$out/import-tool.out" 2>&1
  mini workspace --action import --dir "$WSC" --name parent --kind object --target 7901 --observe-capability 71 --operation-capability 71 >"$out/import-parent.out" 2>&1
  row "the task owners hold their references (tool: 8, parent: 7)" "$([ -f "$WSM/refs/tool.json" ] && [ -f "$WSC/refs/parent.json" ] && echo 1 || echo 0)" "$(tail -1 "$out/import-parent.out" | cut -c1-100)"
fi
delegate() { # WORKSPACE REF
  local ws=$1 ref=$2 id=apps-$2-member
  printf '{"type":"minidregg-workspace-proposal-v1","action":"delegate","name":"%s","recipient":"9","verbs":["observe","mutate"],"maxCost":"%s"}\n' "$ref" "${APPS_MAX:-50000}" >"$out/delegate-$ref.json"
  mini workspace --action propose --dir "$ws" --request "$out/delegate-$ref.json" --proposal-id "$id" >"$out/propose-$ref.out" 2>&1 || return 1
  mini workspace --action submit --dir "$ws" --intent "$ws/proposals/$id/intent.json" --attempt "$ws/attempts/$id" >"$out/submit-$ref.out" 2>&1 || return 1
  mini workspace --action publish-delegation --dir "$ws" --proposal-id "$id" --attempt "$ws/attempts/$id" >"$out/publish-$ref.out" 2>&1 || return 1
  cp "$ws/proposals/$id/recipient-reference.json" "$HOME9/inbox/$ref.json"
}
ok=1; delegate "$WSM" tool || ok=0
if [ "${APPS_E2E_BOOTSTRAP:-0}" = 1 ]; then delegate "$WSM" parent || ok=0; else delegate "$WSC" parent || ok=0; fi
row "each owner delegates observe+mutate on its task to the member; references land in HOME/inbox" "$ok" "$(for r in tool parent; do tail -1 "$out/propose-$r.out" 2>/dev/null | cut -c1-80; done | tr '\n' ' ')"

# ---- the world's apps config and the worker --------------------------------------------------------
mkdir -m 700 -p "$out/quarantine" "$out/wanted" "$out/verdicts" "$out/meta" "$out/state"
chmod 755 "$out/verdicts" "$out/meta"
for f in "${MINI_MARKET_CACHE:-/nonexistent}"/*.spk; do [ -f "$f" ] && cp "$f" "$out/quarantine/"; done
printf '{"protocol":"mini-apps-config-v1","managementSubject":"8","toolRef":"tool","parentRef":"parent","tariff":{"base":"2","perBirth":"1"}}\n' >"$out/apps.json"
# The workroom's own tasks by default; with APPS_E2E_BOOTSTRAP the manager owns both bootstrapped
# tasks, so its owner capabilities are the worker's.
TOOL_TASK=7902 TOOL_CAP=81 PARENT_TASK=7901 PARENT_CAP=73
if [ "${APPS_E2E_BOOTSTRAP:-0}" = 1 ]; then
  TOOL_TASK=$(jq -er .target "$WSM/refs/tool.json") TOOL_CAP=$(jq -er .operationCapability "$WSM/refs/tool.json")
  PARENT_TASK=$(jq -er .target "$WSM/refs/parent.json") PARENT_CAP=$(jq -er .operationCapability "$WSM/refs/parent.json")
fi
jq -n --arg profile "$PROFILE" --arg mini "$MINI" --arg psock "$PSOCK" --arg genesis "$GENESIS" --arg q "$out/quarantine" --arg w "$out/wanted" --arg v "$out/verdicts" --arg nonce "$out/nonce" \
  --arg tt "$TOOL_TASK" --arg tc "$TOOL_CAP" --arg pt "$PARENT_TASK" --arg pc "$PARENT_CAP" '
  {protocol:"mini-apps-world-v1",profile:$profile,mini:$mini,publicSocket:$psock,managementKeyId:"8008",
   toolTask:$tt,toolCapability:$tc,parentTask:$pt,parentCapability:$pc,genesis:$genesis,
   quarantine:$q,wanted:$w,verdicts:$v,domain:"demo.test",nonceFile:$nonce,roleBasis:{type:"allAccess"}}' >"$out/apps-world.json"
nohup "$MINI" apps-worker --state "$out/state" --world "$out/apps-world.json" --member-socket "$out/worker.sock" --edge-socket "$out/edge.sock" --dev-member member >"$out/worker.log" 2>&1 &
echo $! >"$out/worker.pid"
for _ in $(seq 1 50); do [ -S "$out/worker.sock" ] && break; sleep 0.1; done
row "the worker serves its member socket" "$([ -S "$out/worker.sock" ] && echo 1 || echo 0)" "pid $(cat "$out/worker.pid")"

# ---- restart then write (APPS_E2E_RESTART=1, Hacker Slides) ---------------------------------------
# The worker enrols the owner's route after every START (apps_worker.rs World::enroll), so a member
# restarts and writes with no enroll or renew step. A route that nobody re-enrolled is refused by name.
slides_put() { # MARKER -> http code (the response body stays in OUT/put.body)
  printf '# %s\n\n---\n\n## Mini market write\n' "$1" >"$out/put.md"
  curl -sS --max-time 900 --unix-socket "$rdir/http.sock" -X PUT -H "Host: $grain.demo.test" -H "Origin: https://$grain.demo.test" \
    -H "Cookie: __Host-mini_spk_session=$(cat "$rdir/browser.token")" -H 'Content-Type: text/markdown' --data-binary @"$out/put.md" \
    -o "$out/put.body" -w '%{http_code}' "http://$grain.demo.test/slides.md" 2>>"$out/put.err" || echo 000
}
slides_www() { # the anonymous read-back through the publishing socket
  curl -sS --max-time 120 --unix-socket "${rdir%/routes/*}/www.sock" -H 'Host: grain.test' http://grain.test/slides.md 2>>"$out/put.err"
}
serving_generation() { # the highest generation the worker holds a receipted enrollment for
  local d g best=0
  for d in "$out/state/work/$grain/enroll-member"/enroll-member-g[0-9]*; do
    [ -s "$d/receipt.json" ] || continue; g=${d##*-g}; [ "$g" -gt "$best" ] && best=$g
  done
  echo "$best"
}
restart_rows() {
  local g0 g1 code www stale outcome appid
  g0=$(serving_generation)
  code=$(slides_put "slides write before the restart"); www=$(slides_www)
  row "Hacker Slides: a write through the member's route before any restart is admitted and read back" \
    "$([ "$code" = 200 ] && grep -Fq 'slides write before the restart' <<<"$www" && echo 1 || echo 0)" "PUT /slides.md $code; generation $g0"
  mini apps stop --dir "$WS9" --grain "$grain" --json >"$out/restart-stop.json" 2>&1
  mini apps start --dir "$WS9" --grain "$grain" --json >"$out/restart-start.json" 2>&1
  g1=$(serving_generation)
  # no enroll step here: START enrolled the route against the new generation itself
  code=$(slides_put "slides write after the restart"); www=$(slides_www)
  row "restart then write, no manual enroll: generation $g0 -> $g1, the write through the route is admitted and read back" \
    "$([ "$g1" = $((g0 + 2)) ] && [ "$code" = 200 ] && grep -Fq 'slides write after the restart' <<<"$www" && echo 1 || echo 0)" \
    "PUT /slides.md $code; stop $(jq -r .state "$out/restart-stop.json" 2>/dev/null) start $(jq -r .state "$out/restart-start.json" 2>/dev/null)"
  outcome=$(mini apps renew --dir "$WS9" --grain "$grain" --json 2>&1); printf '%s\n' "$outcome" >"$out/renew-current.json"
  row "apps renew --grain after the restart reports current (nothing stale, nothing submitted)" \
    "$(grep -q '"state": "current"' <<<"$outcome" && echo 1 || echo 0)" "$(grep -oE '"(state|detail)": "[^"]*"' <<<"$outcome" | tr '\n' ' ' | cut -c1-200)"
  # The stale case, the cheapest honest way: the operator restarts the app directly (spk-host grain
  # stop and start, the very commands the worker runs) so nothing re-enrols the member's session.
  appid=$(jq -er .app "$out/state/grains/$grain.json" 2>/dev/null || jq -er '.. | .app? // empty' "$out/state/grains/$grain.json" | head -1)
  "$BIN/spk-host" grain stop "$PROFILE" "$appid" >"$out/direct-stop.out" 2>&1
  "$BIN/spk-host" grain start "$PROFILE" "$appid" >"$out/direct-start.out" 2>&1
  code=$(slides_put "slides write on a stale enrollment"); stale=$(head -c 400 "$out/put.body" | tr '\n' ' ')
  row "a write whose session enrollment names the old generation is refused by name (renew it with mini apps renew)" \
    "$([ "$code" != 200 ] && grep -q "session enrollment names app generation $g1 but the app now serves generation $((g1 + 2))" <<<"$stale" && grep -q 'mini apps renew' <<<"$stale" && echo 1 || echo 0)" "PUT /slides.md $code: $(cut -c1-220 <<<"$stale")"
  outcome=$(mini apps renew --dir "$WS9" --grain "$grain" --json 2>&1); printf '%s\n' "$outcome" >"$out/renew-renewed.json"
  code=$(slides_put "slides write after renew"); www=$(slides_www)
  row "apps renew re-enrols the stale route (renewed), then the write is admitted and read back" \
    "$(grep -q '"state": "renewed"' <<<"$outcome" && [ "$code" = 200 ] && grep -Fq 'slides write after renew' <<<"$www" && echo 1 || echo 0)" \
    "$(grep -oE '"state": "[a-z]*"' <<<"$outcome" | head -1) PUT /slides.md $code"
}

# ---- the install, as the member -------------------------------------------------------------------
export MINI_MARKET_INDEX=$FIXTURE MINI_MARKET_META=$out/meta MINI_APPS_VERDICTS=$out/verdicts MINI_APPS_WORKER_SOCKET=$out/worker.sock MINI_APPS_CONFIG=$out/apps.json
install_app() { # APP-ID
  local app=$1 attempt=1 outcome rid before
  before=$(ls "$WS9/apps/requests/" 2>/dev/null | sort)
  outcome=$(mini apps install --dir "$WS9" --home "$HOME9" --app "$app" --class "$CLASS" --json 2>"$out/install-$app.err")
  rid=$(grep -oE 'request [0-9a-f]{32}' <<<"$outcome" | head -1 | cut -d' ' -f2)
  # Only a request file this install created: an earlier app's request must never be taken for this one's.
  [ -n "$rid" ] || rid=$(comm -13 <(printf '%s\n' "$before") <(ls "$WS9/apps/requests/" 2>/dev/null | sort) | grep -E '^[0-9a-f]{32}\.json$' | tail -1 | cut -d. -f1)
  # The worker answers a long install `pending` at once and runs it on its own thread: a read meanwhile is not held.
  if grep -q '"state": "pending"' <<<"$outcome"; then
    local t0 t1 during; t0=$(date +%s%N); during=$(mini apps list --dir "$WS9" --json 2>&1); t1=$(date +%s%N)
    row "while install $app is pending, apps list answers within 5 s" "$(grep -q '"state": "listed"' <<<"$during" && [ $(( (t1 - t0) / 1000000 )) -lt 5000 ] && echo 1 || echo 0)" "$(( (t1 - t0) / 1000000 )) ms"
  fi
  # A first attempt refused before the worker (no request id) is decided; only an undecided request is retried.
  while [ -n "$rid" ] && [ $attempt -le "$ATTEMPTS" ] && ! grep -q '"decided": true' <<<"$outcome"; do
    attempt=$((attempt + 1)); sleep 15
    outcome=$(mini apps install --dir "$WS9" --home "$HOME9" --app "$app" --retry "$rid" --json 2>>"$out/install-$app.err")
  done
  printf '%s\n' "$outcome" >"$out/install-$app.json"
  grep -q '"state": "running"' <<<"$outcome"
}
# The member's own account pays: its balance before the first install and after each one is the
# measured cost of an install (the budget figure INSTALL.md §4 states).
balance() { mini credit --action balance --dir "$WS9" 2>/dev/null | sed -nE 's/^credit ([0-9]+) .*/\1/p' | head -1; }   # "credit N  (asset 0, account A, signed read at height H)"
bal_start=$(balance)
bal_before=$(balance); echo "member balance before installs: ${bal_before:-unreadable}" >>"$out/balances.log"
for app in "$@"; do
  name=$(jq -r --arg a "$app" '.apps[] | select(.appId == $a or .packageId == $a) | .name' "$FIXTURE" | head -1)
  install_app "$app"; installed=$?
  bal_after=$(balance); echo "after $app: ${bal_after:-unreadable}" >>"$out/balances.log"
  if [ "$installed" = 0 ] && [ -n "$bal_before" ] && [ -n "$bal_after" ]; then
    row "the install of $name debited the member's own account" "$([ "$bal_after" -lt "$bal_before" ] && echo 1 || echo 0)" "before=$bal_before after=$bal_after debit=$((bal_before - bal_after))"
  fi
  bal_before=$bal_after
  # The Host's side of the install, whatever the worker did after it: the tool reservation and the
  # application birth admitted (the request record keeps the birth receipt), not law-denied.
  adm=""; for rec in "$out"/state/requests/*.json; do case $rec in *.outcome.json) continue ;; esac
    adm=$(jq -r --arg a "$app" 'select(.appId == $a or .packageId == $a) | .documents.birthReceipt.effect // empty' "$rec" 2>/dev/null | head -1); [ -n "$adm" ] && break; done
  # The funding is the measured install spend (about 10,360 on Hacker Slides: the request cell, six delegation
  # proposals and the three-resource application birth at tariff base 2, perBirth 1, perInitialPayloadByte 1)
  # plus a margin; a spend above the funding is refused by name, never absorbed.
  if [ -n "$bal_start" ] && [ -n "$bal_after" ]; then
    spend=$((bal_start - bal_after))
    row "the member's install spend is within its funding ($MEMBER_FUNDING)" "$([ "$spend" -le "$MEMBER_FUNDING" ] && echo 1 || echo 0)" \
      "$([ "$spend" -le "$MEMBER_FUNDING" ] || echo "spendOverFunding: ")spend $spend of $MEMBER_FUNDING"
  fi
  row "the first install of $name is admitted by the Host at the tool reservation and the application birth (not law-denied)" \
    "$([ "$adm" = admitted ] && ! grep -q 'law-denied' "$out/install-$app.err" "$out/install-$app.json" 2>/dev/null && echo 1 || echo 0)" \
    "birth ${adm:-none}; $(grep -ohE 'law-denied|installRefused|no-grant|resourceBatch|birthStale' "$out/install-$app.err" "$out/install-$app.json" 2>/dev/null | sort -u | tr '\n' ' ')"
  if [ "$installed" = 0 ]; then
    grain=$(grep -oE '"grain": "a[0-9]+"' "$out/install-$app.json" | head -1 | grep -oE 'a[0-9]+')
    row "install $name as the member: running, grain $grain" 1 "$(jq -r '.receipt.origin' "$out/install-$app.json" 2>/dev/null)"
    # the origin check: one authenticated GET through the route socket with the route's cookie and the grain's Host
    rdir=$(jq -r --arg m member '.routes[$m].directory' "$out/state/grains/$grain.json")
    code=$(curl -sS --max-time 900 --unix-socket "$rdir/http.sock" -H "Host: $grain.demo.test" -H "Origin: https://$grain.demo.test" \
      -H "Cookie: __Host-mini_spk_session=$(cat "$rdir/browser.token")" -o "$out/$grain.body" -w '%{http_code}' "http://$grain.demo.test$GET_PATH" 2>"$out/$grain.curl.err" || echo 000)
    anon=$(curl -sS --max-time 120 --unix-socket "$rdir/http.sock" -H "Host: $grain.demo.test" -o /dev/null -w '%{http_code}' "http://$grain.demo.test$GET_PATH" 2>/dev/null || echo 000)
    row "origin check $grain: authenticated GET $GET_PATH 200 through the route, anonymous refused" "$([ "$code" = 200 ] && [ "$anon" != 200 ] && echo 1 || echo 0)" "authed=$code anon=$anon $(head -c 60 "$out/$grain.body" | tr '\n' ' ')"
    if [ "${APPS_E2E_RESTART:-0}" = 1 ] && [ "$app" = "${APPS_E2E_RESTART_APP:-}" ]; then restart_rows; fi
    if [ -n "${APPS_E2E_POST:-}" ]; then
      IFS='|' read -r ppath ptype pbody <<<"$APPS_E2E_POST"
      pcode=$(curl -sS --max-time 900 --unix-socket "$rdir/http.sock" -H "Host: $grain.demo.test" -H "Origin: https://$grain.demo.test" \
        -H "Cookie: __Host-mini_spk_session=$(cat "$rdir/browser.token")" -H "Content-Type: $ptype" -H "Accept: application/json" --data-binary "@$pbody" \
        -o "$out/$grain.post.body" -w '%{http_code}' "http://$grain.demo.test$ppath" 2>"$out/$grain.post.err" || echo 000)
      row "POST $ppath through the route answers 200" "$([ "$pcode" = 200 ] && echo 1 || echo 0)" "code=$pcode $(head -c 100 "$out/$grain.post.body" | tr '\n' ' ')"
    fi
    open=$(mini apps open --dir "$WS9" --grain "$grain" --json 2>&1); row "apps open $grain hands the member the one-time bootstrap token" "$(grep -q bootstrapToken <<<"$open" && echo 1 || echo 0)" "$(grep -oE '"origin": "[^"]*"' <<<"$open")"
  else
    row "install $name as the member" 0 "$(tail -1 "$out/install-$app.err" | cut -c1-160) $(grep -oE '"(refused|state|detail)": "[^"]*"' "$out/install-$app.json" | tr '\n' ' ' | cut -c1-200)"
  fi
done
listed=$(mini apps list --dir "$WS9" --json 2>&1); row "apps list shows the member's grains" "$(grep -q '"grains"' <<<"$listed" && echo 1 || echo 0)" "$(grep -oE '"grain": "a[0-9]+"' <<<"$listed" | tr '\n' ' ')"
if [ "${APPS_E2E_STOP:-0}" = 1 ]; then
  for g in $(grep -oE '"grain": "a[0-9]+"' <<<"$listed" | grep -oE 'a[0-9]+' | sort -u); do
    stopped=$(mini apps stop --dir "$WS9" --grain "$g" --json 2>&1); printf '%s\n' "$stopped" >"$out/stop-$g.json"
    row "apps stop $g is decided stopped (a source-authorized STOP through the custodian)" "$(grep -q '"decided": true' <<<"$stopped" && grep -q '"state": "stopped"' <<<"$stopped" && echo 1 || echo 0)" "$(grep -oE '"(state|refused|detail)": "[^"]*"' <<<"$stopped" | tr '\n' ' ' | cut -c1-160)"
  done
fi
cp "$out/state/grains/"*.json "$out/" 2>/dev/null
verdict