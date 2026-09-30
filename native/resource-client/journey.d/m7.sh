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
#     logs/source-files.sha256 beside it) has the same four SHA-256s, and every
#     compiled input (Lean Host closure, lake/lean pins, the three Rust crates'
#     manifests, sources and build scripts, rust-toolchain.toml) is identical.
#  4. The candidate's own run.sh initializes a second fresh Store from the
#     candidate's genesis-params.example.json, serves it, answers the sponsor's
#     signed factory read, and stops it.
# Last stdout line: the result JSON. Last stderr line: the detail.
set -euo pipefail
D=$JOURNEY_STEP_DIR
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
compiled='^[0-9a-f]{64}  \./((Compiler|Host|Kernel|Pred|Selvage|Theory)/.*\.lean|lakefile\.toml|lake-manifest\.json|lean-toolchain|rust-toolchain\.toml|native/(resource-client|hyperdocument-link-sqlite-store|credential-signature-verifier)/(Cargo\.(toml|lock)|build\.rs|src/.*))$'
grep -E "$compiled" "$C/logs/source-files.sha256" >"$D/compiled-inputs.candidate"
grep -E "$compiled" "$R/logs/source-files.sha256" >"$D/compiled-inputs.reference"
[ -s "$D/compiled-inputs.candidate" ] || fail "no compiled inputs listed for the candidate"
cmp -s "$D/compiled-inputs.candidate" "$D/compiled-inputs.reference" \
  || fail "reference was built from different compiled inputs ($(diff "$D/compiled-inputs.candidate" "$D/compiled-inputs.reference" | grep -c '^[<>]') lines differ)"
for role in host mini store verifier; do
  a=$(jq -r --arg r "$role" '.binaries[$r].sha256' "$CANDIDATE")
  b=$(jq -er --arg r "$role" '.binaries[$r].sha256' "$ref") || fail "reference lacks .binaries.$role.sha256"
  [ "$a" = "$b" ] || fail "$role does not reproduce: candidate $a, reference $b"
done

# 4. the operator procedure, on its own Store. The socket path must stay under
# 108 bytes, so the Store sits directly under the run root, not the step dir.
S=$JOURNEY_RUN/m7-store
cleanup() { "$C/run.sh" stop --state "$S" >"$D/operator-stop.txt" 2>&1 || true; }
trap cleanup EXIT
"$C/run.sh" init --manifest "$C/manifest.json" --params "$C/genesis-params.example.json" --state "$S" >"$D/operator-init.txt" 2>&1 || fail "run.sh init failed: $(tail -1 "$D/operator-init.txt")"
"$C/run.sh" start --state "$S" >"$D/operator-start.txt" 2>&1 || fail "run.sh start failed: $(tail -1 "$D/operator-start.txt")"
"$C/run.sh" sponsor --state "$S" >"$D/operator-sponsor.txt" 2>&1 || fail "run.sh sponsor failed: $(tail -1 "$D/operator-sponsor.txt")"
jq -e '.type == "resource"' "$S/logs/sponsor-factory-read.json" >/dev/null || fail "sponsor's signed factory read did not answer"
"$C/run.sh" stop --state "$S" >"$D/operator-stop.txt" 2>&1 || fail "run.sh stop failed"
trap - EXIT

jq -n --arg commit "$(jq -r .source.commit "$CANDIDATE")" --arg refCommit "$(jq -r .source.commit "$ref")" \
  --arg candidate "$C" --arg reference "$R" --slurpfile p "$CANDIDATE" \
  '{type: "minidregg-m7-result-v1", candidateCommit: $commit, referenceCommit: $refCommit,
    candidate: $candidate, reference: $reference, binaries: ($p[0].binaries | map_values(.sha256)),
    checks: ["sha256sums", "journey-runs-candidate-binaries", "no-tmp-inputs",
             "reproduces-independent-build", "run.sh-init-start-sponsor-stop"]}' >"$D/m7-result.json"
echo "M7: candidate $(jq -r .source.commit "$CANDIDATE" | cut -c1-12) reproduces $(jq -r .source.commit "$ref" | cut -c1-12) built in another directory (4/4 SHA-256, identical compiled inputs); run.sh served its own Store" >&2
echo "$D/m7-result.json"
