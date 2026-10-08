#!/usr/bin/env bash
# Run the standing train row unchanged, or inject a lost-Host-load fault in
# a temporary journey copy. No production source or artifact is mutated.
# Usage: plant-jserve-runner.sh [train runner arguments...]
#        plant-jserve-{long,queue,keys}.sh [TIP [RESULTS_ROOT]]
set -euo pipefail
train=/srv/lanes/train-prod/src/scripts/pipeline
if [[ ${1:-} != --plant ]]; then
  exec bash "$train/journey-runner" "$@"
fi
fault=$2; shift 2
case "$fault" in
  long) check='(b) a long Host request while an honest client reads' ;;
  queue) check='(b2) requests beyond the Host queue bound (32)' ;;
  keys) check='(b3) maximum admitted distinct keys and the oversized 1M-key object' ;;
  *) echo "unknown jserve plant: $fault" >&2; exit 64 ;;
esac
tip=${1:-e0a8ba21a39d92b470cc331fd16ea0408f608b1f}
root=$(CDPATH='' cd -- "$(dirname -- "$0")/../.." && pwd)
results=${2:-$(mktemp -d /tmp/plant-jserve-$fault-results.XXXXXX)}
copy=$(mktemp -d /tmp/plant-jserve-$fault-source.XXXXXX)
trap 'rm -rf "$copy"' EXIT
mkdir -p "$copy/native/resource-client"
for input in journey.sh newparticipant-acceptance.sh journey-stranger.py genesis.sh genesis-params.example.json; do
  cp "$root/native/resource-client/$input" "$copy/native/resource-client/"
done
cp -a "$root/native/resource-client/journey.d" "$copy/native/resource-client/"
hook=$copy/native/resource-client/journey.d/jserve.sh
python3 - "$hook" "$fault" <<'PY'
import sys
path, fault = sys.argv[1:]
s = open(path).read()
start = s.index({'long': 'def long_request():', 'queue': 'def queue_bound():', 'keys': 'def many_keys():'}[fault])
end = s.index('\nguarded(', start)
section = s[start:end]
old = 'raw(keys_body, delivered=delivered)' if fault == 'keys' else 'raw(long_body, delivered=delivered)'
# Reintroduce precisely the stale attack: it is rejected before Host queuing,
# so no honest-read/queue assertion is allowed to claim hostile Host load.
new = ('raw(oversized_keys_body, delivered=delivered)' if fault == 'keys' else
       'raw(AUTHOR_PREFIX + b\'{"pad":[\' + b"0," * 4_000_000 + b\'0]}\', delivered=delivered)')
assert section.count(old) == 1, (fault, section.count(old))
section = section.replace(old, new)
s = s[:start] + '# PLANTED-JSERVE-' + fault + ': oversized payload loses Host load\n' + section + s[end:]
open(path, 'w').write(s)
PY
grep -Fq "# PLANTED-JSERVE-$fault: oversized payload loses Host load" "$hook"
case "$fault" in
  keys) grep -Fq 'raw(oversized_keys_body, delivered=delivered)' "$hook" ;;
  *) grep -Fq 'b"0," * 4_000_000' "$hook" ;;
esac
bash "$train/journey-runner" --once --tip "$tip" --rows-file "$train/journey-rows" \
  --row jserve --source-tree "$copy" --results-root "$results"
# The train runner returns 0 even when a row is red. Require the exact row
# and subcheck verdict, not its exit status or a different failed step.
verdict=$results/$tip/rows/jserve/steps/JSERVE/jserve/serve-rows.tsv
python3 - "$verdict" "$check" <<'PY'
import csv, sys
path, name = sys.argv[1:]
with open(path) as f:
    matches = [r for r in csv.DictReader(f, delimiter='\t') if r['row'] == name]
assert len(matches) == 1 and matches[0]['status'] == 'FAIL', matches
assert 'author request body exceeds its bound' in matches[0]['got'], matches
print('FAIL ' + name + ': ' + matches[0]['got'])
PY
awk -F '\t' '$1=="jserve" && $2=="FAIL" {found=1} END {exit !found}' "$results/$tip/rows/jserve/result.tsv"
printf 'PLANT-JSERVE-%s RED: %s\n' "$fault" "$check"
