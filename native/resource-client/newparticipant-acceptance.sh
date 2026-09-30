#!/bin/sh
# Fresh, private one-sponsor Mini image for independent participant enrollment.
# Run on the same Linux host as the candidate. The four binaries come from a
# candidate manifest written by deploy/candidate/build.sh and are hash-checked
# before use; no prior Store, resource allocation, participant identity, or
# genesis image is copied. Genesis coordinates are the candidate's
# genesis-params.example.json.
set -eu
umask 077

if [ "$#" -ne 2 ]; then
  echo "usage: $0 CANDIDATE/manifest.json NEW_PRIVATE_DIRECTORY" >&2
  exit 2
fi
MANIFEST=$1 ROOT=$2
command -v jq >/dev/null 2>&1 || { echo 'jq is required' >&2; exit 2; }
command -v sha256sum >/dev/null 2>&1 || { echo 'sha256sum is required' >&2; exit 2; }
case "$ROOT" in /*) ;; *) echo 'fixture path must be absolute' >&2; exit 2;; esac
[ -f "$MANIFEST" ] || { echo "manifest not found: $MANIFEST" >&2; exit 2; }
CANDIDATE=$(CDPATH='' cd -- "$(dirname -- "$MANIFEST")" && pwd)
RUN=$CANDIDATE/run.sh
[ -x "$RUN" ] || { echo "candidate has no run.sh: $CANDIDATE" >&2; exit 2; }
(cd "$CANDIDATE" && sha256sum --check --quiet SHA256SUMS) \
  || { echo 'candidate files do not match SHA256SUMS' >&2; exit 1; }

"$RUN" init --manifest "$CANDIDATE/manifest.json" \
  --params "$CANDIDATE/genesis-params.example.json" --state "$ROOT" >/dev/null
"$RUN" start --state "$ROOT" >/dev/null
"$RUN" sponsor --state "$ROOT" >/dev/null
jq -e --slurpfile p "$ROOT/genesis-params.json" '
  .type == "minidregg-participant-reference-v1"
  and .target == ($p[0].factoryId | tostring)
  and .observeCapability == ($p[0].sponsor.factoryObserveCapabilityId | tostring)
  and .controlCapability == ($p[0].factoryControllerCapability | tostring)' \
  "$ROOT/sponsor/refs/factory.json" >/dev/null

MINI=$CANDIDATE/$(jq -r '.binaries.mini.path' "$CANDIDATE/manifest.json")
"$MINI" keygen --secret "$ROOT/keys/newcomer.key" --public "$ROOT/keys/newcomer.pub" \
  >"$ROOT/keys/newcomer.pub.hex"
NEWCOMER_PUBLIC=$(od -An -tx1 -v "$ROOT/keys/newcomer.pub" | tr -d ' \n')
SPONSOR_PUBLIC=$(od -An -tx1 -v "$ROOT/keys/sponsor.pub" | tr -d ' \n')
[ "$SPONSOR_PUBLIC" != "$NEWCOMER_PUBLIC" ] || { echo 'keys unexpectedly equal' >&2; exit 1; }
mkdir -m 700 "$ROOT/attempts"

CONFIG=$ROOT/deployment/pinned-config.json
sha256sum "$CANDIDATE/manifest.json" "$CONFIG" "$ROOT/genesis.json" \
  "$ROOT/sponsor/refs/factory.json" >"$ROOT/source-binaries-and-fixture.sha256"
jq -n --arg root "$ROOT" --arg manifest "$CANDIDATE/manifest.json" --arg mini "$MINI" \
  --arg config "$CONFIG" --arg socket "$ROOT/public/mini.sock" --arg public "$NEWCOMER_PUBLIC" \
  '{type: "minidregg-newparticipant-fixture-v2", root: $root, manifest: $manifest, mini: $mini,
    config: $config, publicSocket: $socket, sponsorWorkspace: ($root + "/sponsor"),
    factoryRef: "factory", newKey: ($root + "/keys/newcomer.key"), newPublicKey: $public,
    namespaceRoot: ($root + "/namespace"), enrollmentAttempt: ($root + "/attempts/newcomer"),
    stop: ($manifest | sub("manifest.json$"; "run.sh stop --state ") + $root),
    status: "fresh-genesis-and-sponsor-workspace; no newcomer admitted"}' >"$ROOT/handoff.json"
printf '%s\n' "$ROOT/handoff.json"
