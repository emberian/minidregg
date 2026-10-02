#!/usr/bin/env bash
# Prepare a signed, exact-preimage paid-claim law update. No policy evaluation here.
# This is the retained signed-policy query route used by workspace law-show.
# Existing current rules still decide whether the operator may install the update.
set -euo pipefail
umask 077
usage() {
  cat <<'HELP'
Prepare (default, no policy write):
  jpay-claim-law.sh --mini /path/mini --workspace /operator/workspace --name factory --dir /new/private/run
Author only after the signed read:
  jpay-claim-law.sh --mini /path/mini --workspace /operator/workspace --name factory --dir /new/private/run --dry
Apply exactly the retained prepared call (no new read, nonce or signatures):
  jpay-claim-law.sh --mini /path/mini --dir /retained/run --apply
Recover an uncertain apply without creating another intent:
  jpay-claim-law.sh --mini /path/mini --dir /retained/run --lookup

Requires bash, jq, sha256sum, and a local operator workspace with a Host path
and Unix socket. The helper never reads a signing key: its path goes to mini.
Only the recognized ticker + observer factory wrapper is eligible. An unknown
wrapper, pre-existing claim slots, or stale exact policy/root fails closed.
Keep the entire retained directory. Review intent.json and query/view.json
before --apply. A later policy/root change is a source refusal, never a rebase.
HELP
}
die() { printf '%s\n' "$*" >&2; exit 64; }
MINI= WS= NAME= RUN= MODE=prepare
while (($#)); do
  case "$1" in
    --help|-h) usage; exit 0;;
    --mini|--workspace|--name|--dir)
      (($# >= 2)) || die "missing value: $1"
      case "$1" in --mini) MINI=$2;; --workspace) WS=$2;; --name) NAME=$2;; --dir) RUN=$2;; esac
      shift 2;;
    --apply|--lookup|--dry)
      [[ $MODE == prepare ]] || die "choose one mode"
      MODE=${1#--}; shift;;
    *) die "unknown argument: $1";;
  esac
done
[[ $MINI == /* && -x $MINI && $RUN == /* ]] || die "absolute --mini executable and --dir required"
command -v jq >/dev/null || die "jq required"
command -v sha256sum >/dev/null || die "sha256sum required"
HERE=$(CDPATH='' cd -- "$(dirname -- "$0")" && pwd)
if [[ $MODE == apply || $MODE == lookup ]]; then
  [[ -z $WS && -z $NAME ]] || die "retained apply/lookup accepts no workspace or name"
  [[ -f $RUN/prepared.json && -f $RUN/prepared.sha256 ]] || die "directory has no completed prepared call"
  jq -e '.type == "minidregg-paid-claim-law-prepared-v1"' "$RUN/prepared.json" >/dev/null
  (cd -- "$RUN"; sha256sum --status --check prepared.sha256) || die "retained prepared files changed"
  if [[ $MODE == apply ]]; then RETRY_MODE=submit; else RETRY_MODE=lookup; fi
  exec "$MINI" retry --attempt "$RUN/submit" --mode "$RETRY_MODE"
fi
[[ $WS == /* && -f $WS/workspace.json ]] || die "absolute --workspace required"
[[ $NAME =~ ^[A-Za-z0-9_-]+(/[A-Za-z0-9_-]+)*$ ]] || die "invalid reference name"
[[ ! -e $RUN && ! -L $RUN ]] || die "run directory must be fresh"
REF=$WS/refs/${NAME//\//.}.json
[[ -f $REF ]] || die "reference not found"
# Key is a path only. No stat/open/copy of key material is performed here.
jq -e '
 .type == "minidregg-participant-workspace-v1" and
 ([.host,.config,.key,.socket] | all(.[]; type=="string" and startswith("/") and (test("[\u0000-\u001f]")|not))) and
 (.subject | type=="string" and test("^(0|[1-9][0-9]*)$"))
' "$WS/workspace.json" >/dev/null || die "requires local workspace with absolute Host/config/key/socket paths"
jq -e --arg name "$NAME" '
 .type == "minidregg-participant-reference-v1" and .name==$name and
 (.kind=="object" or .kind=="account" or .kind=="program") and
 ([.target,.observeCapability,.controlCapability] | all(.[]; type=="string" and test("^(0|[1-9][0-9]*)$")))
' "$REF" >/dev/null || die "reference lacks exact target/observe/control"
mkdir -m 700 -- "$RUN"
cp -- "$WS/workspace.json" "$RUN/workspace.json"
cp -- "$REF" "$RUN/reference.json"
HOST=$(jq -r .host "$RUN/workspace.json")
CONFIG=$(jq -r .config "$RUN/workspace.json")
KEY=$(jq -r .key "$RUN/workspace.json")
SOCKET=$(jq -r .socket "$RUN/workspace.json")
cp -- "$CONFIG" "$RUN/config.json"
nonce() {
  local a b
  a=$(od -An -N4 -tu4 /dev/urandom); b=$(od -An -N4 -tu4 /dev/urandom)
  printf '%s' "$(( (a << 31) | (b & 2147483647) ))"
}
jq -n --slurpfile w "$RUN/workspace.json" --slurpfile r "$RUN/reference.json" --arg nonce "$(nonce)" '
 $w[0] as $w | $r[0] as $r |
 {subject:$w.subject,nonce:$nonce,purpose:{type:"query",kind:$r.kind,target:$r.target,view:"policy"},
  grants:[{kind:$r.kind,target:$r.target,capability:$r.observeCapability}]}
' >"$RUN/query-intent.json"
"$MINI" query --host "$HOST" --config "$RUN/config.json" --socket "$SOCKET" \
  --intent "$RUN/query-intent.json" --key "$KEY" --view policy --dir "$RUN/query" >"$RUN/query-output.json"
[[ -s $RUN/query/signed-observation.bin ]] || die "query did not retain a signed observation"
jq -n -f "$HERE/jpay-claim-law.jq" --slurpfile policy "$RUN/query/view.json" \
  --slurpfile challenge "$RUN/query/challenge.json" --slurpfile reference "$RUN/reference.json" \
  --slurpfile workspace "$RUN/workspace.json" --arg nonce "$(nonce)" \
  --arg declarationNonce "$(nonce)" >"$RUN/intent.json"
if [[ $MODE == dry ]]; then
  printf 'Retained signed policy and exact-preimage intent: %s\n' "$RUN"
  exit 0
fi
"$MINI" submit --host "$HOST" --config "$RUN/config.json" --socket "$SOCKET" \
  --intent "$RUN/intent.json" --key "$KEY" --dir "$RUN/submit" --prepare-only true >"$RUN/prepare-output.json"
[[ -s $RUN/submit/call.bin ]] || die "prepare did not retain a signed call"
cmp -s "$RUN/intent.json" "$RUN/submit/intent.json" || die "submit changed retained intent"
(cd -- "$RUN"; sha256sum intent.json config.json query/view.json query/challenge.json \
  query/signed-observation.bin submit/intent.json submit/config.json submit/attempt.json submit/call.bin >prepared.sha256)
jq -n --slurpfile intent "$RUN/intent.json" '
 {type:"minidregg-paid-claim-law-prepared-v1",
  expected:$intent[0].purpose.draft.declaration.expected,
  expectedPreRoot:$intent[0].purpose.draft.declaration.expectedPreRoot,
  policyId:$intent[0].purpose.draft.declaration.source.policyId,
  nextVersion:$intent[0].purpose.draft.declaration.source.version}
' >"$RUN/prepared.json"
printf 'Prepared only; exact signed call retained: %s\n' "$RUN"
