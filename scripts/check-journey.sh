#!/usr/bin/env bash
# check-journey.sh — gate 5: the Mini journey, from this tree, on a fresh Store.
#
# Builds what the journey runs FROM THIS CHECKOUT (lake build minidregg-host;
# cargo build --release of mini, the Store helper, the verifier, grain-runtime,
# spk-host and pay-watcher into $CARGO_TARGET_DIR, default <repo>/target-gates),
# writes a manifest with sha256 pins, and runs native/resource-client/journey.sh
# under a SHORT private root (mktemp under $XDG_RUNTIME_DIR, else /run/user/UID,
# else /tmp), because grain sockets must fit sun_path (108 bytes).
#
# Verdict, read from journey-result.json (never from the exit code alone):
#   FAIL                          red, named
#   SKIPPED                       red (a partial run is not a gate run)
#   UNBUILT                       red unless the step is pinned in
#                                 scripts/gates/journey-unbuilt.tsv with a reason
#   UNMEASURED (G)                allowed only when LOCAL_GATES_GROWTH_LEVELS was
#                                 set without 1000; printed in the summary
#   UNCONFIGURED                  an input from outside the tree was not supplied;
#                                 printed in the summary by name, not red
#   NOT-RUN / missing result      red
# Inputs from outside the tree (all optional):
#   LOCAL_GATES_NOCK_TEMPLATES LOCAL_GATES_NOCK_RUN     JN2, JN3
#   LOCAL_GATES_NOCK_DOOR_JAM  LOCAL_GATES_NOCK_DOOR_FUEL  JN5
#   LOCAL_GATES_CANDIDATE (a deploy/candidate/build.sh output dir)   M7
#   LOCAL_GATES_GROWTH_LEVELS (default "10 100 500 1000": G at its real level)
#   LOCAL_GATES_JOURNEY_ONLY (passed as JOURNEY_ONLY; the skipped steps are red)
#   LOCAL_GATES_JOURNEY_BUDGET_S (default 14400; wall budget of the whole journey, 0 = none)
# Prints the journey's step table and frontier; the last line is the verdict.
set -uo pipefail
root=$(git -C "$(dirname "$0")" rev-parse --show-toplevel)
cd "$root" || exit 2
export PATH=$HOME/.elan/bin:$HOME/.cargo/bin:$PATH
export CARGO_TARGET_DIR=${CARGO_TARGET_DIR:-$root/target-gates}
rust=$(sed -n 's/^channel *= *"\(.*\)"$/\1/p' rust-toolchain.toml)
die() { echo "journey-gate: FAIL: $*"; exit 1; }
# A build that fails prints the end of its own log, so the cause is in the gate
# output and not only in a file the runner discards.
build_die() { local log=$1; shift; echo "journey-gate: tail of $log:"; tail -n 40 "$log" | sed 's/^/  | /'; die "$@"; }

lake build minidregg-host >"$root/build-logs/gate5-host.log" 2>&1 || build_die "$root/build-logs/gate5-host.log" "lake build minidregg-host (build-logs/gate5-host.log)"
for c in resource-client hyperdocument-link-sqlite-store credential-signature-verifier grain-runtime spk-host pay-watcher; do
  (cd "native/$c" && cargo "+$rust" build --release --locked -j "${LOCAL_GATES_CARGO_JOBS:-6}") \
    >"$root/build-logs/gate5-cargo-$c.log" 2>&1 || build_die "$root/build-logs/gate5-cargo-$c.log" "cargo build --release native/$c (build-logs/gate5-cargo-$c.log)"
done
bin=$CARGO_TARGET_DIR/release
base=${XDG_RUNTIME_DIR:-/run/user/$(id -u)}
[ -d "$base" ] && [ -w "$base" ] || base=/tmp
short=$(mktemp -d "$base/lg.XXXXXX") || die "mktemp under $base"
run=$short/r
man=$short/manifest.json
host=$root/.lake/build/bin/minidregg-host
jq -n --arg host "$host" --arg mini "$bin/mini" --arg store "$bin/minidregg-link-sqlite-store" \
  --arg verifier "$bin/minidregg-credential-signature-verifier" --arg hermes "$bin/grain-runtime" \
  --arg spk "$bin/spk-host" --arg cand "${LOCAL_GATES_CANDIDATE:-}" \
  '{host:$host, mini:$mini, shell:$mini, store:$store, verifier:$verifier, hermes:$hermes, spkHost:$spk}
   + (if $cand == "" then {} else {candidate:$cand} end)' >"$man.tmp"
pins=$(jq -r '[.host,.mini,.store,.verifier,.hermes,.spkHost][]' "$man.tmp" | xargs sha256sum | awk '{print $1}' | paste -sd' ')
jq --arg p "$pins" '. + {sha256: ($p | split(" ") as $h | {host:$h[0], mini:$h[1], store:$h[2], verifier:$h[3], hermes:$h[4], spkHost:$h[5]})}' \
  "$man.tmp" >"$man" && rm -f "$man.tmp"
echo "journey-gate: run root $run (manifest $man)"
jq -r '.sha256 | to_entries[] | "  \(.key) \(.value)"' "$man"

levels=${LOCAL_GATES_GROWTH_LEVELS:-10 100 500 1000}
# The whole journey is bounded: past this wall budget every step not yet started is
# recorded FAIL naming the budget and the slowest steps, and every call and hook is
# capped at what is left (journey.sh, JOURNEY_BUDGET_S). 4 h leaves the 350 min CI job
# its lake build and the other gates; a run that reaches it is red with a reason, never
# cut by the job limit with no verdict. LOCAL_GATES_JOURNEY_BUDGET_S=0 removes it.
env_args=(JOURNEY_GROWTH_LEVELS="$levels" PAY_WATCHER_BIN="$bin/pay-watcher"
  JOURNEY_BUDGET_S="${LOCAL_GATES_JOURNEY_BUDGET_S:-14400}")
[ -n "${LOCAL_GATES_JOURNEY_ONLY:-}" ] && env_args+=(JOURNEY_ONLY="$LOCAL_GATES_JOURNEY_ONLY")
for v in NOCK_TEMPLATES NOCK_RUN NOCK_DOOR_JAM NOCK_DOOR_FUEL; do
  src=LOCAL_GATES_$v
  [ -n "${!src:-}" ] && env_args+=("$v=${!src}")
done
env -u JOURNEY_ONLY -u NOCK_TEMPLATES -u NOCK_RUN -u NOCK_DOOR_JAM -u NOCK_DOOR_FUEL \
  "${env_args[@]}" bash native/resource-client/journey.sh "$man" "$run"
jrc=$?
res=$run/journey-result.json
[ -s "$res" ] || die "journey exit $jrc and no journey-result.json (setup refused; see above)"
cp "$res" "$root/build-logs/gate5-journey-result.json"

python3 - "$res" "$levels" <<'PY'
import json, re, sys
res, levels = json.load(open(sys.argv[1])), sys.argv[2].split()
pinned = {}
for l in open("scripts/gates/journey-unbuilt.tsv", encoding="utf-8"):
    if l.strip() and not l.startswith("#"):
        sid, _, why = l.rstrip("\n").partition("\t")
        pinned[sid.strip()] = why.strip()
red, notes = [], []
for st in res["steps"]:
    i, s, d = st["id"], st["status"], st["detail"]
    if s == "PASS":
        if i in pinned:
            notes.append(f"{i} passes but is pinned UNBUILT; delete its row from scripts/gates/journey-unbuilt.tsv")
            red.append(f"{i} PASS but pinned UNBUILT (stale pin)")
        continue
    if s == "UNBUILT" and pinned.get(i):
        notes.append(f"{i} UNBUILT (pinned: {pinned[i]})"); continue
    if s == "UNMEASURED" and i == "G" and "1000" not in levels:
        notes.append(f"G UNMEASURED (LOCAL_GATES_GROWTH_LEVELS={' '.join(levels)}): {d}"); continue
    if s == "UNCONFIGURED":
        notes.append(f"{i} UNCONFIGURED: {d}"); continue
    red.append(f"{i} {s}: {d}")
for n in notes:
    print(f"journey-gate: note: {n}")
red.sort(key=lambda r: (" SKIPPED" in r, r))
for r in red:
    print(f"journey-gate: RED: {r}")
unconf = [st["id"] for st in res["steps"] if st["status"] == "UNCONFIGURED"]
summary = f"frontier {res['frontier']}, {sum(st['status']=='PASS' for st in res['steps'])}/{len(res['steps'])} PASS"
if unconf: summary += f", unconfigured {' '.join(unconf)}"
if red:
    print(f"journey-gate: FAIL: {len(red)} step(s) red ({summary})"); sys.exit(1)
print(f"journey-gate: PASS ({summary})")
PY
