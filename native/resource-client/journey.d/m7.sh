#!/usr/bin/env bash
# M7 hook for native/resource-client/journey.sh: the journey's binaries are a
# candidate built by deploy/candidate/build.sh, that candidate reproduces an
# independent build, and its operator procedure runs a Store on its own.
#
# Passes only when all of these hold:
#  1. The candidate directory matches its SHA256SUMS, and the four binaries this
#     journey is running are byte-for-byte the candidate's (provenance.json).
#  2. Nothing the journey runs or configures lives under /tmp, and the live
#     pinned config names the candidate's Store helper and verifier.
#  3. REPRODUCTION: a reference candidate built independently in a different
#     directory (M7_REFERENCE, or .m7Reference in the journey manifest: path to
#     its provenance/manifest JSON with .binaries.*.sha256 and
#     logs/source-files.sha256 beside it) has the same complete output SHA-256 set, and every
#     compiled input (Lean Host closure, lake/lean pins, all Rust crates'
#     manifests, sources and build scripts, rust-toolchain.toml) is identical.
#  4. The candidate's own run.sh initializes a second fresh Store from the
#     candidate's genesis-params.example.json, serves it, answers the sponsor's
#     signed factory read, and stops it.
# Last stdout line: the result JSON. Last stderr line: the detail.
set -euo pipefail
D=$JOURNEY_STEP_DIR
. "$(CDPATH='' cd -- "$(dirname -- "$0")" && pwd)/lib/shortdir.sh"
fail() { echo "M7: $*" >&2; exit 1; }
[ -n "${CANDIDATE:-}" ] && [ -f "$CANDIDATE" ] || fail "no candidate provenance in the manifest (build with deploy/candidate/build.sh)"
jq -e '.type == "minidregg-candidate-provenance-v1"' "$CANDIDATE" >/dev/null || fail "candidate is not minidregg-candidate-provenance-v1"
C=$(CDPATH='' cd -- "$(dirname -- "$CANDIDATE")" && pwd -P)

# 1. integrity and identity
(cd "$C" && sha256sum --check SHA256SUMS) >"$D/sha256sums-check.txt" 2>&1 || fail "candidate files differ from SHA256SUMS"
declare -A running=([host]=$HOST [mini]=$MINI [store]=$STORE [verifier]=$VERIFIER)
for role in host mini store verifier; do
  want=$(jq -r --arg r "$role" '.binaries[$r].sha256' "$CANDIDATE")
  path="$C/$(jq -r --arg r "$role" '.binaries[$r].path' "$CANDIDATE")"
  [ "$(realpath "${running[$role]}")" = "$(realpath "$path")" ] || fail "journey $role ${running[$role]} is not the candidate's $path"
  [ "$(sha256sum "$path" | cut -d' ' -f1)" = "$want" ] || fail "candidate $role differs from provenance"
done

# 2. no private fixture
for p in "$HOST" "$MINI" "$STORE" "$VERIFIER" "$CONFIG" "$SOCKET" "$C"; do
  case "$(realpath -m "$p")" in /tmp/*|/var/tmp/*) fail "journey input under a temporary directory: $p" ;; esac
done
[ "$(jq -r .storageBinary "$CONFIG")" = "$STORE" ] || fail "live config names a different Store helper"
[ "$(jq -r .signatureBinary "$CONFIG")" = "$VERIFIER" ] || fail "live config names a different verifier"
case "$(jq -r .storageRoot "$CONFIG")" in /tmp/*|/var/tmp/*) fail "live Store root is under /tmp" ;; esac

# 3. reproduction against an independent build
ref=${M7_REFERENCE:-$(jq -r '.m7Reference // ""' "$JOURNEY_RUN/manifest.json")}
[ -n "$ref" ] && [ -f "$ref" ] || fail "no reference build (set M7_REFERENCE or .m7Reference to another build's provenance JSON)"
R=$(CDPATH='' cd -- "$(dirname -- "$ref")" && pwd -P)
[ "$R" != "$C" ] || fail "reference is the candidate itself"
compiled='^[0-9a-f]{64}  \./(.*\.lean|Cargo\.(toml|lock)|\.cargo/.*|lakefile\.toml|lake-manifest\.json|lean-toolchain|rust-toolchain\.toml|native/.*|protocol/.*|scripts/build-native-host\.sh|deploy/candidate/(build|lane-build|lib)\.sh)$'
grep -E "$compiled" "$C/logs/source-files.sha256" >"$D/compiled-inputs.candidate"
grep -E "$compiled" "$R/logs/source-files.sha256" >"$D/compiled-inputs.reference"
[ -s "$D/compiled-inputs.candidate" ] || fail "no compiled inputs listed for the candidate"
cmp -s "$D/compiled-inputs.candidate" "$D/compiled-inputs.reference" \
  || fail "reference was built from different compiled inputs ($(diff "$D/compiled-inputs.candidate" "$D/compiled-inputs.reference" | grep -c '^[<>]') lines differ)"
# Compare every shipping path (including consent, services and friend bundles).
for entry in "$C/manifest.json" "$R/manifest.json"; do
  jq -e '.type == "minidregg-candidate-manifest-v2" and (.outputs | length > 0)' "$entry" >/dev/null \
    || fail "candidate/reference lacks complete v2 output identity"
done
jq -S '.outputs | map_values(.sha256)' "$C/manifest.json" >"$D/candidate-sha256.json"
jq -S '.outputs | map_values(.sha256)' "$R/manifest.json" >"$D/reference-sha256.json"
cmp -s "$D/candidate-sha256.json" "$D/reference-sha256.json" || fail "candidate outputs do not reproduce"
(cd "$R" && sha256sum --check SHA256SUMS) >"$D/reference-sha256sums-check.txt" 2>&1 \
  || fail "reference files differ from SHA256SUMS"
# Check both manifests through the shipped runtime verifier; a reference's claimed
# hashes alone are not evidence of the bytes built there.
for dir in "$C" "$R"; do
  ( . "$dir/lib.sh"; candidate_resolve "$dir/manifest.json"; candidate_verify_outputs "$dir/manifest.json" ) \
    || fail "candidate/reference runtime identity verification failed"
done
"$C/check-tamper.sh" "$C" "$D/tamper" >"$D/tamper.txt" 2>&1 \
  || fail "tamper check failed: $(tail -1 "$D/tamper.txt")"

# 4. the operator procedure, on its own Store, in a short directory (its
# socket must fit sun_path), kept as $D/rt (journey.d/lib/shortdir.sh).
journey_shortdir m7
S=$JOURNEY_D
cleanup() {
  if [ -f "$S/state.json" ]; then
    if ! "$C/run.sh" stop --state "$S" >"$D/operator-cleanup.txt" 2>&1; then
      echo "M7: operator cleanup failed; see $D/operator-cleanup.txt" >&2
    fi
  fi
  journey_shortdir_return
}
trap cleanup EXIT
"$C/run.sh" init --manifest "$C/manifest.json" --params "$C/genesis-params.example.json" --state "$S" >"$D/operator-init.txt" 2>&1 || fail "run.sh init failed: $(tail -1 "$D/operator-init.txt")"
"$C/run.sh" start --state "$S" >"$D/operator-start.txt" 2>&1 || fail "run.sh start failed: $(tail -1 "$D/operator-start.txt")"
"$C/run.sh" sponsor --state "$S" >"$D/operator-sponsor.txt" 2>&1 || fail "run.sh sponsor failed: $(tail -1 "$D/operator-sponsor.txt")"
jq -e '.type == "resource"' "$S/logs/sponsor-factory-read.json" >/dev/null || fail "sponsor's signed factory read did not answer"
"$C/run.sh" stop --state "$S" >"$D/operator-stop.txt" 2>&1 || fail "run.sh stop failed"
trap journey_shortdir_return EXIT

jq -n --arg commit "$(jq -r .source.commit "$CANDIDATE")" --arg refCommit "$(jq -r .source.commit "$ref")" \
  --arg candidate "$C" --arg reference "$R" --slurpfile p "$CANDIDATE" \
  '{type: "minidregg-m7-result-v1", candidateCommit: $commit, referenceCommit: $refCommit,
    candidate: $candidate, reference: $reference, binaries: ($p[0].binaries | map_values(.sha256)),
    checks: ["sha256sums", "journey-runs-candidate-binaries", "no-tmp-inputs",
             "reproduces-all-outputs", "tamper-init-and-serve-refuse", "run.sh-init-start-sponsor-stop"]}' >"$D/m7-result.json"
echo "M7: candidate $(jq -r .source.commit "$CANDIDATE" | cut -c1-12) reproduces $(jq -r .source.commit "$ref" | cut -c1-12) built in another directory (all output SHA-256, identical compiled inputs, tamper refused); run.sh served its own Store" >&2
echo "$D/m7-result.json"
