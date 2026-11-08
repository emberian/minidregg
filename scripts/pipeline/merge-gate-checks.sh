#!/usr/bin/env bash
# merge-gate-checks.sh SRC FROM TO TAG  -- MERGE-KEEPER post-merge checks (run AFTER the umbrella
# `lake build $(bash scripts/pipeline/umbrella-targets)` is green in SRC at TO).
# Every check runs even after a red. Logs: <basedir>/logs/gate-TAG-<check>.log; summary
# <basedir>/logs/gate-TAG.summary (one line per check: name PASS|RED rc secs). Exit = number red.
# Rust: only the rows of scripts/check-rust-tests.sh whose crate FROM..TO touches (rust-rows.py).
set -u
SRC=$1 FROM=$2 TO=$3 TAG=$4
B=$(cd "$SRC/.." && pwd); H=$(cd "$(dirname "$0")" && pwd)
L=$B/logs; mkdir -p "$L"
S=$L/gate-$TAG.summary; : > "$S"
export PATH=$HOME/.elan/bin:$HOME/.cargo/bin:$HOME/.bun/bin:$PATH
export CARGO_TARGET_DIR=${CARGO_TARGET_DIR:-$B/rust-target}
export LOCAL_GATES_CARGO_JOBS=${LOCAL_GATES_CARGO_JOBS:-4}
# Lean the checks build (new targets, exe roots, the axiom census) goes through LAKE_WRAP.
# Default: the gate slot under swarm-build (slot-mk.sh; a lane slot where the box has no gate slot), so an
# unset LAKE_WRAP never means an uncapped, unslotted Lean build (it did: `nice -n 10`).
if [ -z "$LAKE_WRAP" ]; then
  if command -v swarm-build >/dev/null 2>&1; then LAKE_WRAP="$H/slot-mk.sh swarm-build"; else LAKE_WRAP="nice -n 10"; fi
fi
export SWARM_BUILD_TAG=${SWARM_BUILD_TAG:-gate-$TAG}
# Every check is bounded: PIPELINE_CHECK_TIMEOUT_S (2 h) -> TIMEOUT counts as red, its process tree killed
# (timeout signals the whole process group), so a hung check never parks the gate.
TMO=${PIPELINE_CHECK_TIMEOUT_S:-7200}
cd "$SRC"
[ "$(git rev-parse HEAD)" = "$(git rev-parse "$TO")" ] || { echo "HEAD != $TO" | tee -a "$S"; exit 99; }
# ONE writer of .lake at a time, readers beside it (lane/pipeline-parallel, 2026-10-14).
# The checks fall into two jobs that run CONCURRENTLY when the box has slack:
#   builders  every check that runs `lake build` (new-targets, exe-roots, axiom-census, objective-proofs), SERIALLY
#             in one job: two lake builds in one workspace both write .trace/.ilean in place, so they never overlap.
#   readers   scripts and `lake env lean` programs over modules the umbrella already built, and the touched Rust
#             rows (own CARGO_TARGET_DIR).
# The censuses that elaborate the whole research umbrella (TokenCensus, the hypothesis ledger, scripts-elab) are
# NIGHTLY on dregg-build, not per landing (docs/COORDINATION-2026-10-27.md §2, §6).
# Slack = 1-min loadavg <= PIPELINE_GATE_PARALLEL_MAX_LOAD (default 24) when the gate starts; otherwise the two
# jobs run one after another (readers, builders). Every non-build job runs under swarm-build (one shared
# swarm.slice memory cap bounds their sum). Every check still runs after a red; red = the summary lines whose
# status is neither PASS nor KNOWN-RED, counted at the end (each job is a subshell, so no shared counter).
MAXL=${PIPELINE_GATE_PARALLEL_MAX_LOAD:-24}
load1=$(cut -d' ' -f1 /proc/loadavg)
if [ -n "${PIPELINE_GATE_SERIAL:-}" ] || awk -v l="$load1" -v m="$MAXL" 'BEGIN{exit !(l>m)}'; then PAR=0; else PAR=1; fi
SB=""; command -v swarm-build >/dev/null 2>&1 && SB=swarm-build
echo "merge-gate: mode $([ $PAR = 1 ] && echo parallel || echo serial) (load1 $load1, max $MAXL)" > "$L/gate-$TAG.mode"
run() { local n=$1; shift; local s=$(date +%s); timeout -k 30 "$TMO" "$@" > "$L/gate-$TAG-$n.log" 2>&1; local rc=$?
  local st=PASS
  if [ $rc = 124 ] || [ $rc = 137 ]; then st="TIMEOUT(${TMO}s)"; echo "merge-gate: $n killed after ${TMO}s" >> "$L/gate-$TAG-$n.log"
  elif [ $rc != 0 ]; then st=RED; fi
  echo "$n $st rc=$rc $(( $(date +%s) - s ))s :: $(tail -n 1 "$L/gate-$TAG-$n.log" | cut -c1-200)" | tee -a "$S"; }
# Self-tests run only when the instrument could have changed (scripts/pipeline/instruments.tsv): selftests NAME
# prints 1 when FROM..TO touched one of NAME's files or the gate itself, else 0, recording
# "NAME: instrument unchanged since <sha>: self-tests skipped" in the mode file and the summary.
selftests() {
  local n=$1 paths last
  paths=$(awk -F'\t' -v n="$n" '$1==n{print $2}' "$H/instruments.tsv")
  [ -n "$paths" ] || { echo 1; return; }
  # shellcheck disable=SC2086
  if [ -n "$(git diff --name-only "$FROM" "$TO" -- $paths scripts/pipeline/merge-gate-checks.sh scripts/pipeline/instruments.tsv)" ]; then
    echo 1
  else
    last=$(git log -1 --format=%h "$TO" -- $paths)
    echo "$n: instrument unchanged since $last: self-tests skipped" | tee -a "$L/gate-$TAG.mode" >> "$S"
    echo 0
  fi
}
# lean targets the range DECLARES (new [[lean_lib]]/[[lean_exe]] names in lakefile.toml) are built too:
# the umbrella does not reach a new exe root, CI's lake-build gate does
tnames() { git show "$1:lakefile.toml" | sed -n '/^\[\[lean_\(lib\|exe\)\]\]/{n;s/^name *= *"\(.*\)"$/\1/p}' | sort; }
newt=$(comm -13 <(tnames "$FROM") <(tnames "$TO") | grep -v '^ResearchWip$' | tr '\n' ' ')
# EVERY lean_exe root, every batch (cv 01a1147a-f80e): the umbrella reaches none of the exe-only
# modules, so Compiler.ObjectiveBendCDiffGen sat red on main unseen and a range that broke
# Kernel/ConsentAnchor (outside Minidregg, inside minidregg-client-consent) would have landed.
exes=$(git show "$TO:lakefile.toml" | sed -n '/^\[\[lean_exe\]\]/{n;s/^name *= *"\(.*\)"$/\1/p}' | tr '\n' ' ')

builders() {
  # HOT-PATH 2d: every lean loads .lake/native/libmini_kernels_lean.so; build it first, loudly.
  run mini-kernels bash scripts/build-mini-kernels.sh
  if [ -n "$newt" ]; then run new-targets env LEAN_NUM_THREADS=${THREADS:-6} $LAKE_WRAP lake build $newt; fi
  run exe-roots env LEAN_NUM_THREADS=${THREADS:-6} $LAKE_WRAP lake build $exes
  # HP-6 SIM (HP-DESIGN section 4): seeded Host-path vs follower simulation with crash-restart, and its
  # plant (the follower skipping a failed guard) red at its recorded seed and step. Needs the world-sim
  # exe (exe-roots, just above, builds it). The nightly knob is in the script header.
  run world-sim       bash scripts/gates/check-world-sim .lake/build/bin/world-sim
  # native/private-backend codec agreement: the two Lean fixture exes (exe-roots built them) emit the canonical
  # frames and Plan; the Rust crate must decode and re-encode them, and refuse a flipped byte.
  run private-backend-wire bash scripts/gates/check-private-backend-wire .lake/build/bin
  # Generic Simplex (Kernel/GenericSimplex* + Verify/*): the harness, log-reopen, load and four-source-fixture
  # programs exe-roots builds, run, each with its plant red (fixed timer, split tip, flipped journal bit,
  # corrupt checkpoint segment). Seconds; header names them.
  run generic-simplex bash scripts/gates/check-generic-simplex .lake/build/bin
  # A `sorry` or a declared axiom in a deployed module is only a WARNING to the umbrella build above
  # (measured: `theorem t : 1 = 2 := sorry` in Compiler/DeclaredEffectCellRegistry builds green); the
  # tree-wide axiom census is what turns it red. Deployed is built by the umbrella, so this elaborates
  # Deployed + the census module only.
  run axiom-census    $LAKE_WRAP lake build AxiomCensus
  run objective-proofs $LAKE_WRAP bash scripts/check-objective-proofs.sh proofs
}

readers() {
  run host-closure    bash scripts/check-host-closure.sh
  # The umbrella builds every Lean root the candidate ships, and the recorded runs (Fixtures).
  run umbrella-targets bash scripts/pipeline/umbrella-targets --check
  # KN2 ratchet: callers of the full verified materialization may only shrink (a text ratchet, not a call-graph proof)
  run full-loaded-ratchet bash scripts/ports/check-full-loaded-callers.sh
  # Each planted fault against the pinned history API is refused by the guard it plants
  # (a per-fault expected error, not "any error": API drift does not pass it).
  run api-faults     $SB bash scripts/kn2/check-planted-api-faults.sh
  # A native helper that cannot start, or answers bytes that are not a tagged reply, is refused by name
  # with no panic (2026-10-07: a failed exec flushed the caller's buffered stdout into the reply pipe and
  # its bytes, read as a length, aborted the Host). Executed, no fixture; seconds.
  run coprocess-faults $SB lake env lean --run scripts/kn2/coprocess-faults.lean
  # Only the finish/checkInert routes hand out the object kernel facet (Config.kernelTransport): an
  # environment census (scripts/KernelTransportCensus.lean) after self-test plants; a new caller or a
  # stale row is red. Needs Kernel.NativeHost + Kernel.NativeHostReplay built (the umbrella does); ~30 s.
  local kst=""; [ "$(selftests kernel-transport)" = 0 ] && kst=--no-self-test
  run kernel-transport $SB bash scripts/check-kernel-transport.sh $kst
  run import-boundary bash scripts/check-import-boundary.sh
  run bytes-repr      bash scripts/check-bytes-repr.sh
  run platform-field-readers python3 -I scripts/check-platform-field-readers.py
  run proof-hygiene   bash scripts/check-proof-hygiene.sh
  run build-surfaces  python3 scripts/lean-build-surfaces.py check
  # The pure-script pins local-gates runs and this list lacked (W20-GATE-MUTATION, 2026-10-05): each is
  # seconds, none builds Lean. Mutants that each of them kills and this gate did not see: a new unrooted
  # module (build-closure), an @[export] nothing calls (exports), an is_absolute() in a shell-line parser
  # (shell-paths), a request byte routed without a Host receiver (host-operations), a stale SheetLaw embed
  # (gen-sheetlaw), a stale status page (website).
  run build-closure   bash -c 'bash scripts/check-build-closure.sh && python3 scripts/test_build_gate_boundaries.py && python3 scripts/test_lean_build_surfaces.py'
  run exports         bash scripts/check-exports.sh
  run unit-tests      $SB bash scripts/check-unit-tests.sh
  run policy-portal   bash scripts/check-canonical-policy-portal.sh
  run shell-paths     bash scripts/check-shell-paths.sh
  run host-operations bash -c 'python3 scripts/host-operations.py check && python3 scripts/test-host-operations.py'
  run gen-sheetlaw    python3 scripts/gen-sheetlaw.py --check
  # The story law files and Kernel/StoryLaw.lean (generated region) are the client's own generator output: build `mini` and
  # require that `mini story-law` still produces exactly the embedded text (a stale embed is how a theorem
  # about `law taleTable` stops being about the law `story seal` installs; the rfl in the build only holds
  # the Lean side, this holds the Rust side).
  run gen-storylaw    $SB bash -c 'cargo build --quiet --manifest-path native/resource-client/Cargo.toml --bin mini && python3 scripts/gen-storylaw.py --check --mini "$CARGO_TARGET_DIR/debug/mini"'
  run website         python3 website/gen-status.py --check
  # A generated fixture's authority (a hand-written file no generator writes) never changes in the same
  # commit as the implementation, and only with an Authority-Change trailer; every generated fixture has
  # a row in scripts/pipeline/fixture-authorities.txt (cv 01a1147b-103d).
  run fixture-authority bash scripts/pipeline/check-fixture-authority.sh "$FROM..$TO"
  run intent-vector-authority python3 scripts/pipeline/check-intent-vector-authority.py
  # The receiving pipeline's one live verifier: one Ran.mk, no Ran instance, no hand-built Verifier (plants: ran-instance, second-mint, handbuilt)
  run receiver-verifier bash scripts/check-receiver-verifier.sh
  # Ran.mk is mentioned, by term and theorems included, only by receiverVerifier (plants: unfolded oracleAnswered, live Answered); scan root AxiomCensusResearch, whose import closure (1307 modules) contains Host.Main's (781; difference empty, measured with scripts/lean_imports.py); on first run check both plants fail by name before trusting green; needs AxiomCensusResearch built
  run ran-mint $SB bash scripts/check-ran-mint.sh
  python3 "$H/rust-rows.py" "$SRC" "$FROM" "$TO" "$B/tmp-rust-rows-$TAG.sh" > "$L/gate-$TAG-rust-rows.txt" 2>&1 || echo "rust-rows RED (selector failed)" | tee -a "$S"
  cat "$L/gate-$TAG-rust-rows.txt"
  run rust-rows       $SB bash "$B/tmp-rust-rows-$TAG.sh"
  # non-Lean, non-Rust tests the change touches: deploy tooling, changed python test files
  if git diff --name-only "$FROM..$TO" | grep -q '^deploy/'; then
    run deploy-scripts bash -c 'python3 deploy/pay/test-render-enrol.py && python3 deploy/candidate/test-package.py && bash deploy/candidate/test-lane-build.sh && sh deploy/candidate/test-params.sh'
    run spk-shell bash scripts/check-spk-shell-tests.sh
  fi
  for f in $(git diff --name-only --diff-filter=AM "$FROM..$TO" | grep -E '(^|/)test_[^/]*\.py$'); do
    run "py-$(basename "$f" .py)" bash -c "cd $(dirname "$f") && python3 $(basename "$f")"
  done
}

g0=$(date +%s)
if [ "$PAR" = 1 ]; then
  builders & BP=$!
  readers & rp=$!
  wait $BP; wait $rp
else
  readers; builders
fi
echo "merge-gate: checks wall $(( $(date +%s) - g0 ))s" >> "$L/gate-$TAG.mode"
d=$(git status --porcelain --untracked-files=no | wc -l)
[ "$d" = 0 ] && echo "tracked-clean PASS" | tee -a "$S" || { echo "tracked-clean RED ($d tracked files changed)" | tee -a "$S"; git status --porcelain --untracked-files=no | head -20 >> "$S"; }
red=$(awk '$1!="TOTAL" && NF>=2 && $2!="PASS" && $2 !~ /^KNOWN-RED/ && $2 ~ /^(RED|TIMEOUT)/' "$S" | wc -l)
echo "TOTAL red=$red HEAD=$(git rev-parse HEAD) $(date -Is)" | tee -a "$S"
exit $red
