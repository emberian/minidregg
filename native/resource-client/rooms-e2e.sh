#!/usr/bin/env bash
# rooms-e2e.sh -- private rooms, end to end on a REAL Host: found, invite, sync, seal, kick,
# a hosted invitee, a signing-key rotation of the founder, the chat feed's privacy stamp, a restart
# and a cold audit. DEVNET QUALITY; PRIVACY NOT AUDITED.
#
#   MINI_HOST_BIN=/abs/minidregg-host MINI_BIN=/abs/mini \
#   MINI_STORE_BIN=/abs/minidregg-link-sqlite-store MINI_VERIFIER_BIN=/abs/minidregg-credential-signature-verifier \
#     native/resource-client/rooms-e2e.sh [RUN_ROOT]
#
# MINI_HOST_BIN is the only input without a default: a built Host image (`lake build minidregg-host`
# or the cut lane's approved image). The others default to <repo>/target-gates/release/ (what
# scripts/check-journey.sh builds). RUN_ROOT defaults to a fresh directory under the runtime dir
# (grain and Host sockets must fit sun_path, so it is kept SHORT). The run is on a scratch Store of
# its own: it never touches a live world.
#
# It runs the journey steps J0..J5 (the fresh Store, the sponsor, the first friends: JPRIV1's
# dependency chain) and JPRIV1 (journey.d/jpriv1.sh), then compares the hook's row table with
# journey.d/jpriv1.expected.tsv. Exit 0 only if J0..J5 and JPRIV1 PASS, no row is FAIL and every
# expected row is present and ok. The expected transcript was authored from the script, not from a
# run: the first real run may need script corrections (the file says so).
#
#   rooms-e2e.sh --self-check     no Host needed: every expected row is a literal of the script, and
#                                 the script is syntactically valid. This is all that can run today.
set -uo pipefail
HERE=$(CDPATH='' cd -- "$(dirname -- "$0")" && pwd)
ROOT=$(CDPATH='' cd -- "$HERE/../.." && pwd)
EXPECTED=$HERE/journey.d/jpriv1.expected.tsv
HOOK=$HERE/journey.d/jpriv1.sh
die() { echo "rooms-e2e: $*" >&2; exit 2; }

self_check() {
  bash -n "$HOOK" || die "journey.d/jpriv1.sh does not parse"
  bash -n "$HERE/journey.sh" || die "journey.sh does not parse"
  python3 - "$EXPECTED" "$HOOK" <<'PY' || exit 2
import sys
expected, hook = sys.argv[1], sys.argv[2]
src = open(hook, encoding="utf-8").read()
rows = [l.rstrip("\n").split("\t", 2) for l in open(expected, encoding="utf-8") if l.strip() and not l.startswith("#")]
bad = [r for r in rows if len(r) != 3 or r[2] not in src]
for r in bad:
    print("rooms-e2e: expected row is not a literal of jpriv1.sh:", r, file=sys.stderr)
print(f"rooms-e2e: self-check: {len(rows)} expected rows, {len(bad)} not literal in the script")
sys.exit(1 if bad else 0)
PY
}

if [ "${1:-}" = --self-check ]; then self_check; exit $?; fi

: "${MINI_HOST_BIN:?set MINI_HOST_BIN to an absolute path of a built minidregg-host image. There is no warm Host build yet (the cut lane is still gating); this script is authored, not run. Restart condition: a Host image exists and this env var names it.}"
for tool in jq sha256sum python3 setsid timeout pgrep xxd bc; do
  command -v "$tool" >/dev/null 2>&1 || die "$tool is required"
done
bin=${MINI_RELEASE_DIR:-$ROOT/target-gates/release}
MINI_BIN=${MINI_BIN:-$bin/mini}
MINI_STORE_BIN=${MINI_STORE_BIN:-$bin/minidregg-link-sqlite-store}
MINI_VERIFIER_BIN=${MINI_VERIFIER_BIN:-$bin/minidregg-credential-signature-verifier}
for v in MINI_HOST_BIN MINI_BIN MINI_STORE_BIN MINI_VERIFIER_BIN; do
  p=${!v}
  case "$p" in /*) ;; *) die "$v must be an absolute path (got: $p)";; esac
  [ -x "$p" ] || die "$v is not an executable file: $p"
done
self_check || exit 2

base=${XDG_RUNTIME_DIR:-/run/user/$(id -u)}
[ -d "$base" ] && [ -w "$base" ] || base=/tmp
short=$(mktemp -d "$base/re.XXXXXX") || die "mktemp under $base"
run=${1:-$short/r}
case "$run" in /*) ;; *) die "RUN_ROOT must be absolute";; esac
man=$short/manifest.json
jq -n --arg host "$MINI_HOST_BIN" --arg mini "$MINI_BIN" --arg store "$MINI_STORE_BIN" --arg verifier "$MINI_VERIFIER_BIN" \
  '{host:$host, mini:$mini, shell:$mini, store:$store, verifier:$verifier}' >"$man.tmp"
pins=$(jq -r '[.host,.mini,.store,.verifier][]' "$man.tmp" | xargs sha256sum | awk '{print $1}' | paste -sd' ')
jq --arg p "$pins" '. + {sha256: ($p | split(" ") as $h | {host:$h[0], mini:$h[1], store:$h[2], verifier:$h[3]})}' "$man.tmp" >"$man" && rm -f "$man.tmp"
echo "rooms-e2e: manifest $man; run root $run"
jq -r '.sha256 | to_entries[] | "  \(.key) \(.value)"' "$man"

JOURNEY_ONLY="J0 J1 J2 J3 J4 J5 JPRIV1" JOURNEY_GROWTH_LEVELS="10" \
  bash "$HERE/journey.sh" "$man" "$run"
echo "rooms-e2e: journey.sh exit $? (non-zero is expected: the other steps are SKIPPED by design; the verdict is below)"

res=$run/journey-result.json
[ -s "$res" ] || die "no journey-result.json under $run: the setup refused (see above)"
tsv=$(find "$run" -name jpriv1.tsv -print -quit)
python3 - "$res" "${tsv:-}" "$EXPECTED" <<'PY'
import csv, json, sys
result, tsv, expected = sys.argv[1], sys.argv[2], sys.argv[3]
steps = {s["id"]: s for s in json.load(open(result))["steps"]}
bad = []
for need in ["J0", "J1", "J2", "J3", "J4", "J5", "JPRIV1"]:
    st = steps.get(need, {}).get("status", "MISSING")
    print(f"rooms-e2e: {need:7} {st}")
    if st != "PASS":
        bad.append(f"{need} is {st}: {steps.get(need, {}).get('detail', '')}")
rows = []
if tsv:
    with open(tsv, encoding="utf-8") as f:
        rows = list(csv.DictReader(f, delimiter="\t"))
else:
    bad.append("no jpriv1.tsv: the hook did not run")
red = [r for r in rows if r.get("verdict") != "ok"]
for r in red[:10]:
    bad.append(f"row {r['n']} {r['step']} {r['who']}: {r['line'][:100]} -> {r['note'][:160]}")
want = [l.rstrip("\n").split("\t", 2) for l in open(expected, encoding="utf-8") if l.strip() and not l.startswith("#")]
missing = [w for w in want if not any(r["step"] == w[0] and r["who"].lower() == w[1].lower() and w[2] in r["line"] and r["verdict"] == "ok" for r in rows)]
for w in missing:
    bad.append(f"expected row absent or red: {w[0]} {w[1]}: {w[2][:100]}")
print(f"rooms-e2e: {len(rows)} rows, {len(red)} red, {len(want) - len(missing)}/{len(want)} expected rows present and ok")
if bad:
    print("rooms-e2e: FAIL"); [print("  " + b) for b in bad]; sys.exit(1)
print("rooms-e2e: PASS")
PY
