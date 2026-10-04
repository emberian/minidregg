#!/usr/bin/env bash
# merge-gate-checks.sh SRC FROM TO TAG  -- MERGE-KEEPER post-merge checks (run AFTER the umbrella
# `lake build Minidregg +Host.Main:leanArts ObjectiveProofs` is green in SRC at TO).
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
cd "$SRC"
[ "$(git rev-parse HEAD)" = "$(git rev-parse "$TO")" ] || { echo "HEAD != $TO" | tee -a "$S"; exit 99; }
red=0
run() { local n=$1; shift; local s=$(date +%s); ( "$@" ) > "$L/gate-$TAG-$n.log" 2>&1; local rc=$?
  local st=PASS; [ $rc = 0 ] || { st=RED; red=$((red+1)); }
  echo "$n $st rc=$rc $(( $(date +%s) - s ))s :: $(tail -n 1 "$L/gate-$TAG-$n.log" | cut -c1-200)" | tee -a "$S"; }
# lean targets the range DECLARES (new [[lean_lib]]/[[lean_exe]] names in lakefile.toml) are built too:
# the umbrella does not reach a new exe root, CI's lake-build gate does
tnames() { git show "$1:lakefile.toml" | sed -n '/^\[\[lean_\(lib\|exe\)\]\]/{n;s/^name *= *"\(.*\)"$/\1/p}' | sort; }
newt=$(comm -13 <(tnames "$FROM") <(tnames "$TO") | grep -v '^ResearchWip$' | tr '\n' ' ')
if [ -n "$newt" ]; then run new-targets env LEAN_NUM_THREADS=${THREADS:-6} ${LAKE_WRAP:-nice -n 10} lake build $newt; fi
run host-closure    bash scripts/check-host-closure.sh
run import-boundary bash scripts/check-import-boundary.sh
run proof-hygiene   bash scripts/check-proof-hygiene.sh
run build-surfaces  python3 scripts/lean-build-surfaces.py check
run objective-proofs bash scripts/check-objective-proofs.sh proofs
python3 "$H/rust-rows.py" "$SRC" "$FROM" "$TO" "$B/tmp-rust-rows-$TAG.sh" > "$L/gate-$TAG-rust-rows.txt" 2>&1 || { echo "rust-rows RED (selector failed)" | tee -a "$S"; red=$((red+1)); }
cat "$L/gate-$TAG-rust-rows.txt"
run rust-rows       ${LAKE_WRAP:-} bash "$B/tmp-rust-rows-$TAG.sh"
# non-Lean, non-Rust tests the change touches: deploy tooling, changed python test files
if git diff --name-only "$FROM..$TO" | grep -q '^deploy/'; then
  run deploy-scripts bash -c 'python3 deploy/pay/test-render-enrol.py && python3 deploy/candidate/test-package.py && bash deploy/candidate/test-lane-build.sh'
fi
for f in $(git diff --name-only --diff-filter=AM "$FROM..$TO" | grep -E '(^|/)test_[^/]*\.py$'); do
  run "py-$(basename "$f" .py)" bash -c "cd $(dirname "$f") && python3 $(basename "$f")"
done
d=$(git status --porcelain --untracked-files=no | wc -l)
[ "$d" = 0 ] && echo "tracked-clean PASS" | tee -a "$S" || { echo "tracked-clean RED ($d tracked files changed)" | tee -a "$S"; git status --porcelain --untracked-files=no | head -20 >> "$S"; red=$((red+1)); }
echo "TOTAL red=$red HEAD=$(git rev-parse HEAD) $(date -Is)" | tee -a "$S"
exit $red
