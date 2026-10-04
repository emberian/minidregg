#!/usr/bin/env bash
# check-unit-tests.sh -- the python unittest modules that no other gate ran (W43-ORPHAN-GATES).
#
# scripts/gates/unit-tests.tsv names each module and the number of tests it ran when it was added
# (the floor). A module is red when unittest exits non-zero OR it ran fewer tests than its floor:
# a module whose tests were deleted, renamed or skipped, or a file that no longer defines any,
# exits 0 with `Ran 0 tests` and would read green on the exit code alone. A path in the list that
# no longer exists is red. A new `test_*.py` unittest module under the listed directories that is
# in no row is red too: it enters by being listed, so a new test cannot be an orphan.
set -uo pipefail
root=$(git -C "$(dirname "$0")" rev-parse --show-toplevel)
cd "$root" || exit 2
list=scripts/gates/unit-tests.tsv
logs=$root/build-logs/unit-tests; mkdir -p "$logs"
red=0 n=0
while IFS=$'\t' read -r path floor task; do
  [ -n "$path" ] && [[ $path != \#* ]] || continue
  case $path in
    @elsewhere) continue ;;   # @elsewhere<TAB>path<TAB>the gate that already runs it
    @known-red)               # @known-red<TAB>path<TAB>cv task: must STILL fail; the day it passes the row is red
      kr=$floor; n=$((n + 1)); log=$logs/$(echo "$kr" | tr / _).log
      (cd "$(dirname "$kr")" && python3 -m unittest "$(basename "$kr" .py)") >"$log" 2>&1 \
        && { echo "unit-tests: RED: $kr: known-red module now PASSES; move it to a floor row (cv task $task)"; red=$((red + 1)); } \
        || echo "unit-tests: known-red: $kr still fails, as recorded (cv task $task)"
      continue ;;
  esac
  n=$((n + 1)); log=$logs/$(echo "$path" | tr / _).log
  case $floor in ''|*[!0-9]*|0) echo "unit-tests: RED: $path: floor '$floor' is not a positive integer"; red=$((red + 1)); continue ;; esac
  [ -f "$path" ] || { echo "unit-tests: RED: $path: listed but absent"; red=$((red + 1)); continue; }
  mod=$(basename "$path" .py)
  (cd "$(dirname "$path")" && python3 -m unittest "$mod") >"$log" 2>&1; rc=$?
  ran=$(grep -Eo '^Ran [0-9]+ test' "$log" | awk '{print $2}' | tail -1)
  if [ "$rc" != 0 ]; then
    echo "unit-tests: RED: $path: exit $rc: $(grep -E '^(FAIL|ERROR):' "$log" | head -2 | tr '\n' ';') ($log)"; red=$((red + 1))
  elif [ "${ran:-0}" -lt "$floor" ]; then
    echo "unit-tests: RED: $path: ran ${ran:-0} tests, floor $floor ($log)"; red=$((red + 1))
  fi
done <"$list"
# a test module in the listed directories that no row names
for dir in $(grep -v '^#' "$list" | awk -F'\t' '{print ($1 ~ /^@/) ? $2 : $1}' | xargs -n1 dirname | sort -u); do
  for f in "$dir"/test_*.py; do
    [ -f "$f" ] || continue
    awk -F'\t' -v f="$f" '$1 == f || ($1 ~ /^@/ && $2 == f) {found = 1} END {exit !found}' "$list" || { echo "unit-tests: RED: $f is a test module in no row of $list"; red=$((red + 1)); }
  done
done
[ "$n" -gt 0 ] || { echo "unit-tests: RED: no row"; exit 1; }
if [ "$red" != 0 ]; then echo "unit-tests: FAIL: $red red of $n modules"; exit 1; fi
echo "unit-tests: PASS ($n modules)"
