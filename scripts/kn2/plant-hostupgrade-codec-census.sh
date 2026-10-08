#!/usr/bin/env bash
# Mutate temp copies only. Both directions of the named build check must be live.
set -euo pipefail
ROOT=$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)
OUT=${1:?usage: plant-hostupgrade-codec-census.sh OUT}
mkdir -p "$OUT"
OUT=$(cd "$OUT" && pwd)
SCRATCH=$(mktemp -d)
trap 'rm -rf "$SCRATCH"' EXIT
cd "$ROOT"

expect_red() {
  local name=$1 source_root=$2 expected=$3
  if lake env bash -c 'export LEAN_PATH="$1:$LEAN_PATH"; exec lean --root="$1" "$1/Compiler/PersistedCodecTagCensus.lean"' _ "$source_root" >"$OUT/$name.log" 2>&1; then
    printf 'FAIL census plant %s unexpectedly green\n' "$name"
    exit 1
  fi
  if ! rg -F 'persisted codec tag set equality failed:' "$OUT/$name.log" >/dev/null; then
    cat "$OUT/$name.log"
    printf 'FAIL census plant %s failed without equality verdict\n' "$name"
    exit 1
  fi
  if ! rg -F "$expected" "$OUT/$name.log" >/dev/null; then
    cat "$OUT/$name.log"
    printf 'FAIL census plant %s missing pinned identity\n' "$name"
    exit 1
  fi
  printf 'RED as intended: census %s (%s)\n' "$name" "$expected"
}

python3 - "$ROOT" "$SCRATCH" <<'PY'
import pathlib, sys
root, scratch = map(pathlib.Path, sys.argv[1:])
census = (root / "Compiler/PersistedCodecTagCensus.lean").read_text()
registry = (root / "Compiler/PersistedCodecTags.lean").read_text()
marker = "\n#assert_persisted_codec_tags\nend Minidregg.Compiler.PersistedCodecTagCensus"
assert census.count(marker) == 1
probe = '\ndef encodeCensusPlant (payload : List UInt8) : List UInt8 := "DREGG/CENSUS/PLANT/v99".toUTF8.toList ++ payload\n'
assert "DREGG/CENSUS/PLANT/v99" not in census and "DREGG/CENSUS/PLANT/v99" not in registry
mutated = census.replace(marker, probe + marker)
assert mutated != census and mutated.replace(probe, "", 1) == census
target = scratch / "new-literal/Compiler"
target.mkdir(parents=True)
(target / "PersistedCodecTagCensus.lean").write_text(mutated)
print("MUTATION ASSERTED new-literal: one reachable encoder tag added", flush=True)

removed = '@[persisted_codec_tag] abbrev objective_activity_recorded_failure_v1 : String := "DREGG/OBJECTIVE/ACTIVITY/RECORDED-FAILURE/v1"\n'
assert registry.count(removed) == 1
mutated = registry.replace(removed, "", 1)
assert mutated != registry and removed.strip() not in mutated
target = scratch / "missing-entry/Compiler"
target.mkdir(parents=True)
(target / "PersistedCodecTags.lean").write_text(mutated)
(target / "PersistedCodecTagCensus.lean").write_text(census)
print("MUTATION ASSERTED missing-entry: recorded-failure registry entry deleted", flush=True)

ghost = '@[persisted_codec_tag] abbrev censusUnreachable : String := "DREGG/CENSUS/REGISTRY-ONLY/v99"\n\n'
assert registry.count("make_persisted_codec_manifest") == 1
assert "censusUnreachable" not in registry
mutated = registry.replace("make_persisted_codec_manifest", ghost + "make_persisted_codec_manifest")
assert mutated != registry and mutated.replace(ghost, "", 1) == registry
target = scratch / "unreachable-entry/Compiler"
target.mkdir(parents=True)
(target / "PersistedCodecTags.lean").write_text(mutated)
(target / "PersistedCodecTagCensus.lean").write_text(census)
print("MUTATION ASSERTED unreachable-entry: one registry-only tag added", flush=True)
PY

# Lean chooses a module root by its top-level directory. Populate that directory
# with read-only symlinks to unchanged artifacts, then unlink the mutated module
# outputs before compiling so no write can follow a symlink into the real tree.
for name in new-literal missing-entry unreachable-entry; do
  cp -as "$ROOT/.lake/build/lib/lean/Compiler/." "$SCRATCH/$name/Compiler/"
done
for name in missing-entry unreachable-entry; do
  for artifact in "$SCRATCH/$name/Compiler/PersistedCodecTags."*; do
    if [[ -L "$artifact" ]]; then rm "$artifact"; fi
  done
done
expect_red new-literal "$SCRATCH/new-literal" 'DREGG/CENSUS/PLANT/v99'
for name in missing-entry unreachable-entry; do
  lake env lean --root="$SCRATCH/$name" "$SCRATCH/$name/Compiler/PersistedCodecTags.lean" \
    -o "$SCRATCH/$name/Compiler/PersistedCodecTags.olean" >"$OUT/$name-registry.log" 2>&1
done
expect_red missing-entry "$SCRATCH/missing-entry" 'DREGG/OBJECTIVE/ACTIVITY/RECORDED-FAILURE/v1'
expect_red unreachable-entry "$SCRATCH/unreachable-entry" 'registry-only [Minidregg.Compiler.PersistedCodecTags.censusUnreachable]'
printf 'PASS asserted census plants: new literal, deleted entry, reverse coverage\n'
