#!/bin/bash
# Generic public-store lifecycle qualification. No app-specific requests or writes.
set -euo pipefail
umask 077
here=$(cd "$(dirname "$0")" && pwd)
world_up_lock=${WORLD_UP_LOCK:-/home/hbox/lanes/world-up.lock}
repo=$(cd "$here/../.." && pwd)
data=$here/store-sweep-data.py
usage() {
  cat <<'HELP'
store-sweep.sh --candidate DIR --out DIR [--staging DIR] [--index FILE]
               [--batch-size 1..7] [--max-worlds N] [--retry-stage STAGE] [--dry-run]
Run as the world operator on hbox (MINI_OPERATOR_UID/NAME as for world-up.sh).
Candidate DIR is an immutable build named by its full git SHA, containing bin/.
Default index: fetched from the public Sandstorm index through mini-market-fetch.
--index uses a recorded index instead; --dry-run fetches only the index, prints the
unjudged plan, and starts no worlds. --max-worlds 0 (default) means the whole store.
Evidence, verdicts.tsv and qualification.json are retained under OUT/<candidate>/.
Resume with the same OUT: completed PASS and FAIL records are skipped only for the
same candidate and package. Interrupted apps have no verdict and are tried fresh.
--retry-stage explicitly archives FAIL records at that stage before replanning.
Staging defaults to /tank/lanes/cx-store-sweep/staging and is removed after teardown.
A cleanup failure stops the sweep and retains staging for inspection.
Each entire world holds flock -o $WORLD_UP_LOCK (default /home/hbox/lanes/world-up.lock) through teardown.
PASS means the lifecycle plus authenticated GET / answered HTTP 2xx or 3xx;
redirects are recorded, not followed. No app-specific functionality is certified.
HELP
}
candidate='' out='' index='' staging=/tank/lanes/cx-store-sweep/staging size=7 maximum=0 dry=0 retry=''
while (($#)); do
  case $1 in
    --candidate) candidate=$2; shift 2;; --out) out=$2; shift 2;;
    --staging) staging=$2; shift 2;; --index) index=$2; shift 2;;
    --batch-size) size=$2; shift 2;; --max-worlds) maximum=$2; shift 2;;
    --retry-stage) retry=$2; shift 2;;
    --dry-run) dry=1; shift;; --help|-h) usage; exit 0;;
    *) echo "unknown option: $1" >&2; exit 2;;
  esac
done
[[ -d $candidate/bin && -n $out && $size =~ ^[1-7]$ && $maximum =~ ^[0-9]+$ ]] || { usage >&2; exit 2; }
candidate=$(cd "$candidate" && pwd)
sha=${candidate##*/}
[[ $sha =~ ^[0-9a-f]{40}$ ]] || { echo 'candidate directory must be named by its full git SHA' >&2; exit 2; }
jq -e --arg sha "$sha" '.source.commit == $sha' "$candidate/provenance.json" >/dev/null || {
  echo 'candidate provenance does not match its directory' >&2; exit 2;
}
mkdir -p "$out/$sha"
out=$(cd "$out/$sha" && pwd)
# Local output lock prevents concurrent writers, independently of the shared world lock.
# flock -o closes its fd in children, including Mini's long-lived residents.
if [[ $dry == 0 && ${STORE_SWEEP_OUTPUT_LOCKED:-} != "$out" ]]; then
  exec flock -o "$out/sweep.lock" env STORE_SWEEP_OUTPUT_LOCKED="$out" "$0" \
    --candidate "$candidate" --out "${out%/*}" --staging "$staging" --batch-size "$size" \
    --max-worlds "$maximum" ${index:+--index "$index"} ${retry:+--retry-stage "$retry"}
fi
if [[ -z $index ]]; then
  if [[ $dry == 1 ]]; then
    index=$out/dry-index.json
    curl --fail --silent --show-error --proto '=https' --max-time 120 --max-filesize 4194304 \
      https://app-index.sandstorm.io/apps/index.json -o "$index.new"
    mv "$index.new" "$index"
  else
    bash "$repo/deploy/market/mini-market-fetch" --state "$out/market" --mini "$candidate/bin/mini" refresh
    index=$out/market/index.json
  fi
fi
if [[ $dry == 0 ]]; then
  "$candidate/bin/mini" apps index-check --in "$index" --out "$out/index.json"
  index=$out/index.json
  [[ -z $retry ]] || python3 "$data" retry-stage "$out" "$sha" "$retry" "$index"
  python3 "$data" publish "$out" "$sha"
fi
plan=$out/plan.jsonl
[[ $dry == 0 ]] || plan=$out/dry-plan.jsonl
python3 "$data" plan "$index" "$out" "$sha" "$size" "$maximum" "$retry" >"$plan.new"
mv "$plan.new" "$plan"
jq -r 'to_entries[] | [.value.letter,.value.name,.value.packageId,"birth → install → share → start → enroll → GET /"] | @tsv' "$plan"
echo "$(wc -l <"$plan") worlds; candidate $sha; profile chosen from package bytes and native segment limits"
[[ $dry == 0 ]] || exit 0
[[ $staging == /tank/lanes/* && $staging != *[!a-zA-Z0-9_./-]* ]] || { echo 'staging must be a simple absolute directory under /tank/lanes' >&2; exit 2; }
mkdir -p "$staging"
if compgen -G "$staging/b.*" >/dev/null; then
  flock -o "$world_up_lock" "$here/store-sweep-world.sh" "$candidate" "$out" "$staging" - --recover-all
fi
# Save the scripts and binary pins used, independently of subsequent lane edits.
mkdir -p "$out/driver"
cp "$0" "$data" "$here/store-sweep-profile.sh" "$here/world-import-profile.sh" "$here/store-sweep-world.sh" "$here/grain-journey.sh" "$here/world-up.sh" "$here/broker-world-up.sh" "$here/world-down.sh" "$here/stop-residents.sh" "$out/driver/"
sha256sum "$candidate/bin/mini" "$candidate/bin/spk-host" "$candidate/bin/minidregg-host" >"$out/binary-sha256.txt"
while IFS= read -r batch; do
  batchfile=$(mktemp "$out/batch.XXXXXX.json")
  printf '%s\n' "$batch" >"$batchfile"
  # The lock covers preparation, world-up, every app, world-down and resident cleanup.
  flock -o "$world_up_lock" "$here/store-sweep-world.sh" "$candidate" "$out" "$staging" "$batchfile"
done <"$plan"
jq '.counts' "$out/qualification.json"
