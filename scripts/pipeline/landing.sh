#!/usr/bin/env bash
# scripts/pipeline/landing.sh TIP [--lane NAME] [--wait-s N]   -- land one candidate BY THE RULE on this box.
# scripts/pipeline/landing.sh --check TIP                        -- only judge TIP's finished standing run.
#
# PROTOCOL 6 (landed = on GitHub main AND a full static gate red=0 at that sha AND the standing journey run at
# that sha has every required row PASS / UNCONFIGURED-declared) and 7 (tools run from the TIP'S TREE).
# The push to GitHub main is the root's, from the results.tsv this prints; this script never pushes.
#
#   1. mk-lane from the warm base, by the BASE TREE's own mk-lane ($PIPELINE_WARM_BASE/src/scripts/
#      pipeline/mk-lane.sh; never a copy), then fetch TIP from the shared repo and check it out.
#      HAND-OFF: when TIP's tree has a landing.sh that differs from this one, the rest runs as TIP's own
#      (exec, --in-lane); a TIP without one predates this script and the log says this copy continued.
#   2. gate: TIP's own scripts/pipeline/run-gate-burst.sh (umbrella in the gate slot under swarm-build, then
#      merge-gate-checks.sh), started when /proc/loadavg's 1-min load is <= PIPELINE_GATE_MAX_LOAD (20).
#      Required: umbrella PASS and `TOTAL red=0`.
#   3. publish: TIP's own scripts/pipeline/publish-artifacts TIP next LANE/src (the gated tree: nothing
#      compiles), which smokes the set and writes READY + the `next` label.
#   4. standing run: kick pipeline-journeys.service (install-journey-units; it runs the SET'S OWN TREE's
#      journey-runner) and wait for $JOURNEY_ROOT/TIP/DONE (or REFUSED) up to --wait-s (14400).
#   5. verdict: the non-PASS lines and the row count, then every id of required-rows (read from the MAIN
#      BASE's tree: the policy in force, not the candidate's) must be PASS, or UNCONFIGURED with a detail
#      matching a declaration in $PIPELINE_ROOT/absent-inputs.tsv (ROW<TAB>DETAIL-REGEX<TAB>REASON) for
#      that row. Exit 0 only then. Exit codes: 10 gate red, 11 publish failed, 12 run refused or timed
#      out, 13 required rows not met, 2 usage/environment.
set -euo pipefail
PIPELINE_PROG=landing
here=$(CDPATH='' cd -- "$(dirname -- "$0")" && pwd)
[ -n "${PIPELINE_ROOT:-}" ] && [ -f "$PIPELINE_ROOT/box.env" ] || { echo "landing: set PIPELINE_ROOT to a box layout with box.env (docs/PIPELINE-HBOX.md)" >&2; exit 2; }
. "$here/lib.sh"
self_sha() { sha256sum "$1" | cut -c1-16; }
lane="" wait_s=14400 in_lane="" check_only=0 tip=""
while [ $# -gt 0 ]; do
  case "$1" in
    --lane) lane=$2; shift 2 ;; --wait-s) wait_s=$2; shift 2 ;; --in-lane) in_lane=$2; shift 2 ;;
    --check) check_only=1; shift ;; -*) pipeline_die "unknown option $1" ;; *) tip=$1; shift ;;
  esac
done
[ -n "$tip" ] || pipeline_die "usage: landing.sh TIP [--lane NAME] [--wait-s N] | --check TIP"
SHARED=${PIPELINE_SHARED_GIT:-}
tip=$(pipeline_full_sha "$tip" "${SHARED:-$PIPELINE_WARM_BASE/src}")
W=$PIPELINE_WARM_BASE
base_tip=$(sed -n 's/^tip=//p' "$W/FROZEN")
pipeline_log "landing.sh $here/landing.sh sha256:$(self_sha "$here/landing.sh"); tip $tip; base $base_tip; PIPELINE_ROOT=$PIPELINE_ROOT"

# --- the verdict (step 5), also alone with --check ------------------------------------------------
judge() {
  local J=$JOURNEY_ROOT/$tip req decl
  req=$W/src/scripts/pipeline/required-rows; [ -f "$req" ] || req=$here/required-rows
  decl=$PIPELINE_ROOT/absent-inputs.tsv; [ -f "$decl" ] || decl=/dev/null
  # BASELINE: main's own most recent standing run on THIS box ($ARTIFACT_ROOT/main -> its journeys DONE)
  local base_t base_res=/dev/null
  base_t=$(readlink "$ARTIFACT_ROOT/main" 2>/dev/null || true)
  if [ -n "$base_t" ] && [ -f "$JOURNEY_ROOT/$base_t/DONE" ]; then base_res=$JOURNEY_ROOT/$base_t/results.tsv; fi
  [ -f "$J/DONE" ] || { pipeline_log "no finished standing run at $J"; return 12; }
  # Which tree the standing run executed, and whether that runner is TIP's own: a greppable line, never an
  # absence. The dispatch record is the service's (install-journey-units); the reference sha is TIP's blob
  # in the shared repo, independent of the set.
  local D=$JOURNEY_ROOT/.trees/$tip.dispatch ran want git_dir
  if [ -f "$D" ]; then
    ran=$(sed -n 's/^runner_sha256=//p' "$D")
    echo "RUN-TREE tip=$tip tree=$(sed -n 's/^tree=//p' "$D") runner=$(sed -n 's/^runner=//p' "$D") runner_sha256=$ran source_tar_sha256=$(sed -n 's/^source_tar_sha256=//p' "$D") dispatched=$(sed -n 's/^dispatched=//p' "$D")"
    git_dir=${PIPELINE_SHARED_GIT:-$W/src/.git}
    want=$(git --git-dir="$git_dir" show "$tip:scripts/pipeline/journey-runner" 2>/dev/null | sha256sum | cut -d' ' -f1)
    if [ -n "$ran" ] && [ "$ran" = "$want" ] && cmp -s "$(sed -n 's/^runner=//p' "$D")" <(git --git-dir="$git_dir" show "$tip:scripts/pipeline/journey-runner"); then
      echo "SELF-CHECK PASS: the standing run executed $tip's own journey-runner (sha256 $ran = git $tip:scripts/pipeline/journey-runner)"
    else
      echo "SELF-CHECK FAIL: executed runner sha256 ${ran:-?} != $tip's journey-runner ${want:-?}"; return 12
    fi
  else
    echo "SELF-CHECK FAIL: no dispatch record $D (the run was not started by pipeline-journeys.service)"; return 12
  fi
  if [ -s "$PIPELINE_ROOT/logs/PLANT-STALE-RUNNER-EXECUTED" ]; then
    echo "STALE-COPY EXECUTED: $(tail -1 "$PIPELINE_ROOT/logs/PLANT-STALE-RUNNER-EXECUTED")"
  fi
  echo "== standing run $J ($(sed -n 2p "$J/table.txt" 2>/dev/null))"
  echo "== awk -F'\\t' '\$2!=\"PASS\"' $J/results.tsv"
  awk -F'\t' '$2!="PASS"' "$J/results.tsv" | cut -c1-240
  echo "== rows: $(wc -l <"$J/results.tsv") lines; $(awk -F'\t' '{c[$2]++} END {for (k in c) printf "%s=%d ", k, c[k]}' "$J/results.tsv")"
  echo "== required rows: $req (sha256:$(self_sha "$req")); declarations: $decl"
  echo "== baseline: main ${base_t:-none} on $(hostname): $base_res"
  [ "$base_res" != /dev/null ] || echo "NO BASELINE: no finished standing run of main on this box; every required non-PASS counts as new"
  python3 - "$req" "$J/results.tsv" "$decl" "$base_res" <<'PY'
import re, sys
req_f, res_f, decl_f, base_f = sys.argv[1:]
req, pending, known = [], [], {}
for l in open(req_f):
    l = l.strip()
    if not l or l.startswith('#'): continue
    if l.startswith('pending '): pending.append(l[8:]); continue
    if l.startswith('known-red '):
        p = l.split(None, 3); known[p[1]] = (p[2], p[3] if len(p) > 3 else ''); continue
    req.append(l)
rows = [l.rstrip('\n').split('\t') for l in open(res_f) if l.strip()]
base = {}
for l in open(base_f):
    if l.strip():
        p = l.rstrip('\n').split('\t'); base[p[0]] = p[1]
cand = {r[0]: r[1] for r in rows}
# (b) NEW REDS: every line PASS at main's baseline that is not PASS (or is gone) in the candidate's run
new = [(k, cand.get(k, 'MISSING')) for k, st in base.items() if st == 'PASS' and cand.get(k) != 'PASS']
print(f"new reds vs baseline: {len(new)}")
for k, st in new: print(f"NEW RED   {k} {st} (PASS at main's baseline)")
decl = []
for l in open(decl_f):
    if not l.strip() or l.startswith('#'): continue
    p = l.rstrip('\n').split('\t')
    if len(p) >= 3: decl.append((p[0], re.compile(p[1]), p[2]))
def declared(r):
    for row, rx, why in decl:
        if row == r[0] and len(r) > 4 and rx.search(r[4]): return why
    return None
bad = 0
unmet = []
seen = set()   # a sub-row is covered by its own id AND its parent's: judge and print it once
for rid in req:
    mine = [r for r in rows if r[0] == rid or r[0].startswith(rid + '/')]
    if not mine:
        print(f"MISSING   {rid}: no line in results.tsv"); bad += 1; continue
    subs = [r for r in mine if r[0] != rid]
    for r in mine:
        if r[0] in seen: continue
        seen.add(r[0])
        st = r[1]
        if st == 'PASS': continue
        why = declared(r) if st == 'UNCONFIGURED' else None
        # a parent UNCONFIGURED only because of its sub-rows: accepted when every sub-row is accepted
        if st == 'UNCONFIGURED' and r[0] == rid and subs and why is None:
            if all(s[1] == 'PASS' or (s[1] == 'UNCONFIGURED' and declared(s)) for s in subs):
                print(f"ok        {r[0]} UNCONFIGURED via declared sub-rows"); continue
        if why:
            print(f"declared  {r[0]} UNCONFIGURED: {why}"); continue
        unmet.append((r[0], st, (r[4] if len(r) > 4 else '')[:200]))
for p in pending:
    pid = p.split()[0]
    green_gate = len(p.split()) > 1 and p.split()[1] == 'when-green-at-main'
    mine_base = {k: st for k, st in base.items() if k == pid or k.startswith(pid + '/')}
    if green_gate and not (mine_base and all(st == 'PASS' for st in mine_base.values())):
        # required only once main's baseline has it PASS; (b) above still judges it line by line
        mine = [r for r in rows if r[0] == pid or r[0].startswith(pid + '/')]
        now = ', '.join(f"{r[0]} {r[1]}" for r in mine) or 'no line'
        was = ', '.join(f"{k} {st}" for k, st in mine_base.items()) or 'no line'
        print(f"pending   {pid} (when green at main; main's baseline: {was}; candidate: {now})")
        for r in mine:
            if r[1] != 'PASS': print(f"  not yet  {r[0]} {r[1]}: {(r[4] if len(r) > 4 else '')[:200]}")
        continue
    if any(r[0] == pid or r[0].startswith(pid + '/') for r in rows):
        # a pending row that now exists is required (required-rows header)
        for r in [r for r in rows if r[0] == pid or r[0].startswith(pid + '/')]:
            if r[1] == 'PASS': continue
            why = declared(r) if r[1] == 'UNCONFIGURED' else None
            if why: print(f"declared  {r[0]} UNCONFIGURED: {why}"); continue
            print(f"NOT MET   {r[0]} {r[1]} (pending row now exists, so required): {(r[4] if len(r) > 4 else '')[:200]}"); bad += 1
        print(f"required  {pid} (was pending; the row exists now)")
    else:
        print(f"pending   {p}")
# (c) a required line unmet in the candidate that was ALSO non-PASS at main's baseline is pre-existing: it
# blocks nothing only when required-rows lists it as `known-red ROW CV-ID note` (the fix has an owner).
pre, blocking = [], []
for rid, st, det in unmet:
    top = rid.split('/')[0]
    was = base.get(rid)
    if was is not None and was != 'PASS' and (rid in known or top in known):
        cv = known.get(rid, known.get(top))[0]
        pre.append(f"{rid} (cv {cv})"); print(f"PRE-RED   {rid} {st} (non-PASS at main's baseline too: {was}; cv {cv}): {det}")
    else:
        why = "" if was is None or was == 'PASS' else f" (non-PASS at main's baseline too: {was}, but no known-red cv task in required-rows: open one)"
        blocking.append(rid); print(f"NOT MET   {rid} {st}{why}: {det}")
bad += len(blocking)
print(f"required unmet: {[u[0] for u in unmet]} (of which pre-existing at main: {pre})")
ok = not new and not bad
print(f"REQUIRED: {len(req)} ids; new reds vs baseline: {len(new)}; blocking: {bad}" + (" -> LANDABLE by the baseline-relative rule" if ok else " -> NOT landable"))
sys.exit(0 if ok else 1)
PY
}
if [ "$check_only" = 1 ]; then judge; exit $?; fi

# --- 1. lane from the warm base, by the base tree's own mk-lane ------------------------------------
if [ -z "$in_lane" ]; then
  lane=${lane:-land-${tip:0:8}}
  mk=$W/src/scripts/pipeline/mk-lane.sh
  pipeline_log "mk-lane $lane by $mk sha256:$(self_sha "$mk") (the base tree's own, at $base_tip)"
  bash "$mk" "$lane"
  L=$PIPELINE_LANES/$lane
  cd "$L/src"
  if ! git cat-file -e "$tip^{commit}" 2>/dev/null; then
    [ -n "$SHARED" ] || pipeline_die "$tip is not in the base and PIPELINE_SHARED_GIT is unset"
    git fetch -q "$SHARED" "+refs/heads/*:refs/remotes/shared/*"
  fi
  git checkout -q -B main "$tip"
  if [ -f scripts/pipeline/landing.sh ] && ! cmp -s scripts/pipeline/landing.sh "$here/landing.sh"; then
    pipeline_log "HAND-OFF: $tip has its own landing.sh (sha256:$(self_sha scripts/pipeline/landing.sh)); it runs the rest"
    exec bash "$L/src/scripts/pipeline/landing.sh" "$tip" --in-lane "$L" --wait-s "$wait_s"
  fi
  [ -f scripts/pipeline/landing.sh ] || pipeline_log "$tip predates landing.sh: this copy (sha256:$(self_sha "$here/landing.sh")) continues; every tool below is $tip's own"
else
  L=$in_lane; cd "$L/src"; [ "$(git rev-parse HEAD)" = "$tip" ] || pipeline_die "$L/src HEAD is not $tip"
fi
T=$L/src/scripts/pipeline
for f in run-gate-burst.sh merge-gate-checks.sh publish-artifacts; do
  [ -f "$T/$f" ] || pipeline_die "$tip's tree has no scripts/pipeline/$f"
  pipeline_log "tool $T/$f sha256:$(self_sha "$T/$f") ($tip's tree)"
done

# --- 2. gate ----------------------------------------------------------------------------------------
tag=land-${tip:0:8}
# The shared Lake cache's guard, from the tip's own tree (lib.sh pipeline_cache_audit): poisoned or
# written-through entries are purged before the gate's builds can fetch them; an audit that cannot run
# refuses the landing.
pipeline_cache_audit "$L/src" || pipeline_die "lake-cache-audit could not run on ${LAKE_CACHE_DIR:-?}: the gate does not build on an unguarded cache"
pipeline_log "cache-audit done (${LAKE_CACHE_DIR:-cache off})"
while :; do
  load=$(cut -d' ' -f1 /proc/loadavg)
  awk -v l="$load" -v m="${PIPELINE_GATE_MAX_LOAD:-20}" 'BEGIN {exit !(l <= m)}' && break
  pipeline_log "load $load > ${PIPELINE_GATE_MAX_LOAD:-20}: gate waits"; sleep 120
done
pipeline_log "gate $tag: $T/run-gate-burst.sh $L $base_tip $tag"
bash "$T/run-gate-burst.sh" "$L" "$base_tip" "$tag" || true
S=$L/logs/gate-$tag.summary
[ -f "$L/logs/gate-$tag.done" ] || pipeline_die "gate did not finish: $(cat "$L/logs/gate-$tag.aborted" 2>/dev/null)"
cat "$S"
grep -q "^umbrella PASS" "$S" && grep -q "^TOTAL red=0 HEAD=$tip" "$S" \
  || { pipeline_log "GATE RED at $tip ($S)"; exit 10; }
pipeline_log "gate red=0 at $tip"

# --- 3. publish (the gated tree: nothing compiles) -----------------------------------------------
pipeline_log "publish: $T/publish-artifacts $tip next $L/src"
bash "$T/publish-artifacts" "$tip" next "$L/src" || { pipeline_log "publish FAILED for $tip"; exit 11; }
[ -f "$ARTIFACT_ROOT/$tip/READY" ] || { pipeline_log "publish returned but $ARTIFACT_ROOT/$tip is not READY"; exit 11; }

# --- 4. the standing run (the service runs the set's own tree) -------------------------------------
J=$JOURNEY_ROOT/$tip
systemctl --user start --no-block pipeline-journeys.service 2>/dev/null \
  || pipeline_log "could not kick pipeline-journeys.service (not installed? scripts/pipeline/install-journey-units); waiting for its timer"
t0=$(date +%s)
until [ -f "$J/DONE" ] || [ -f "$J/REFUSED" ]; do
  [ $(( $(date +%s) - t0 )) -lt "$wait_s" ] || { pipeline_log "no standing run of $tip within $wait_s s"; exit 12; }
  sleep 30
done
[ -f "$J/DONE" ] || { pipeline_log "standing run REFUSED: $(cat "$J/REFUSED")"; exit 12; }

# --- 5. verdict --------------------------------------------------------------------------------------
judge | tee "$L/logs/landing-$tip.txt"; rc=${PIPESTATUS[0]}
[ "$rc" = 0 ] || { pipeline_log "required rows NOT met at $tip"; exit 13; }
pipeline_log "LANDABLE $tip: gate red=0, set READY ($ARTIFACT_ROOT/$tip), standing run meets the required rows ($J/results.tsv). The root pushes main from that file."
