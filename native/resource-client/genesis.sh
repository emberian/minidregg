#!/bin/sh
# The one Mini genesis template. From a genesis params file
# (minidregg-candidate-genesis-params-v1, see deploy/candidate/INTERFACES.md;
# genesis-params.example.json beside this script holds the qualified values)
# and the sponsor's public key, write into DIR:
#   operator.json               Host operator config (storageRoot DIR/store)
#   profile.json                the Host's semantics/metering profile
#   genesis.json                genesis source (coordinates as decimal strings)
#   sponsor-birth-context.json  the sponsor's birth context
# It never bootstraps; the caller does. Callers: newparticipant-acceptance.sh
# (the journey's J0 and newparticipant-from-manifest.sh) and
# deploy/candidate/run.sh init.
#
# EXTRA_GENESIS_ENROLLMENTS, if set, is an absolute path to a JSON array of at
# most 8 further genesis enrollments (a hosted operator's agent-grain subjects;
# the only AgentGrain birth route is the historical birth intent, admitted only
# against the genesis image). None may reuse the sponsor's subject or account.
#
# GENESIS_PAY_OBSERVER, if set, is an absolute path to a JSON object
# {"subject","capability","controlCapability","enrolCapability"} (canonical
# decimal strings) naming the PAY observer (deploy/pay/README.md): genesis then
# installs the pay law and the observer's, the pay controller's and the
# self-enrollment capabilities. Its subject must be one of the genesis
# enrollments (the sponsor or an EXTRA_GENESIS_ENROLLMENTS entry).
set -eu
umask 077
check_params() {
  # Every coordinate is a JSON integer the operator chose. jq holds numbers as
  # doubles, so refuse anything at or above 2^53 rather than round it.
  jq -e '
    def int: type == "number" and . >= 0 and . == floor and . < 9007199254740992;
    .type == "minidregg-candidate-genesis-params-v1"
    and ([.domain, .federation, .factoryId, .resourceBookId, .authorityCellId, .issuer,
          .ownerBudget, .lifetime, .tariffBase, .tariffPerBirth, .tariffPerGrant,
          .tariffPerInitialPayloadByte, .collector, .asset, .genesisHeight, .issuerEpoch,
          .factoryControllerCapability] | all(int))
    and (.sponsor | [.subject, .keyId, .keyEpoch, .activeFrom, .activeUntil, .accountId,
          .spendCapabilityId, .controlCapabilityId, .factoryObserveCapabilityId,
          .initialBalance] | all(int))
    and (.meterAllowance | type == "object" and length == 10 and (map_values(int) | all))
  ' "$1" >/dev/null || { echo "genesis: params file fails the minidregg-candidate-genesis-params-v1 schema" >&2; exit 2; }
}
if [ "$#" -eq 2 ] && [ "$1" = --check ]; then
  check_params "$2"
  exit 0
fi
if [ "$#" -ne 6 ]; then
  echo "usage: $0 PARAMS.json SPONSOR_PUBLIC_HEX HOST STORE VERIFIER DIR" >&2
  echo "       $0 --check PARAMS.json" >&2
  exit 2
fi
params=$1 public=$2 host=$3 store=$4 verifier=$5 dir=$6
for path in "$params" "$host" "$store" "$verifier" "$dir"; do
  case "$path" in /*) ;; *) echo "genesis: path must be absolute: $path" >&2; exit 2;; esac
done
[ -d "$dir" ] || { echo "genesis: not a directory: $dir" >&2; exit 2; }
case "$public" in *[!0-9a-f]*|"") echo 'genesis: sponsor public key must be lowercase hex' >&2; exit 2;; esac
[ "${#public}" -eq 64 ] || { echo 'genesis: sponsor public key must be 32 bytes' >&2; exit 2; }
for target in operator.json profile.json genesis.json sponsor-birth-context.json; do
  [ ! -e "$dir/$target" ] && [ ! -L "$dir/$target" ] || { echo "genesis: refusing existing $dir/$target" >&2; exit 2; }
done

check_params "$params"

jq -n --slurpfile p "$params" --arg store "$store" --arg root "$dir/store" --arg verifier "$verifier" '
  $p[0] as $p |
  {domain: $p.domain, federation: $p.federation, factoryId: $p.factoryId,
   resourceBookId: $p.resourceBookId, authorityCellId: $p.authorityCellId,
   issuer: $p.issuer, ownerBudget: $p.ownerBudget, lifetime: $p.lifetime,
   tariffBase: $p.tariffBase, tariffPerBirth: $p.tariffPerBirth, tariffPerGrant: $p.tariffPerGrant,
   tariffPerInitialPayloadByte: $p.tariffPerInitialPayloadByte, collector: $p.collector,
   asset: $p.asset, genesisHeight: $p.genesisHeight, expectedSeed: 0,
   storageBinary: $store, storageRoot: $root, signatureBinary: $verifier}' >"$dir/operator.json"

"$host" "$dir/operator.json" profile >"$dir/profile.json"
semantics=$(jq -er '.semantics | select(type == "string" and test("^(0|[1-9][0-9]*)$"))' \
  "$dir/profile.json") || { echo 'genesis: Host profile has no semantics digest' >&2; exit 1; }

jq -n --slurpfile p "$params" --arg semantics "$semantics" --arg public "$public" '
  $p[0] as $p | def s: tostring;
  {domain: ($p.domain|s), factoryId: ($p.factoryId|s), resourceBookId: ($p.resourceBookId|s),
   authorityCellId: ($p.authorityCellId|s), federation: ($p.federation|s),
   tariffBase: ($p.tariffBase|s), tariffPerBirth: ($p.tariffPerBirth|s),
   tariffPerGrant: ($p.tariffPerGrant|s),
   tariffPerInitialPayloadByte: ($p.tariffPerInitialPayloadByte|s),
   collector: ($p.collector|s), asset: ($p.asset|s), expectedSemantics: $semantics,
   issuerEpoch: ($p.issuerEpoch|s), genesisHeight: ($p.genesisHeight|s),
   factoryPredicate: {type: "all", predicates: []},
   enrollments: [{key: {keyId: ($p.sponsor.keyId|s), keyEpoch: ($p.sponsor.keyEpoch|s),
                        algorithm: "1", subject: ($p.sponsor.subject|s), publicKey: $public,
                        activeFrom: ($p.sponsor.activeFrom|s),
                        activeUntil: ($p.sponsor.activeUntil|s)},
                  accountId: ($p.sponsor.accountId|s),
                  spendCapabilityId: ($p.sponsor.spendCapabilityId|s),
                  controlCapabilityId: ($p.sponsor.controlCapabilityId|s),
                  factoryObserveCapabilityId: ($p.sponsor.factoryObserveCapabilityId|s),
                  initialBalance: ($p.sponsor.initialBalance|s),
                  accountPredicate: {type: "all", predicates: []}}],
   factoryControllerSubject: ($p.sponsor.subject|s),
   factoryControllerCapability: ($p.factoryControllerCapability|s),
   meterAllowance: ($p.meterAllowance | map_values(s))}' >"$dir/genesis.json"

if [ -n "${EXTRA_GENESIS_ENROLLMENTS:-}" ]; then
  case "$EXTRA_GENESIS_ENROLLMENTS" in /*) ;; *) echo 'genesis: EXTRA_GENESIS_ENROLLMENTS must be absolute' >&2; exit 2;; esac
  jq -e --slurpfile p "$params" '
    ($p[0].sponsor.subject|tostring) as $subject | ($p[0].sponsor.accountId|tostring) as $account |
    type == "array" and length > 0 and length <= 8 and
    all(.[]; .key.subject != $subject and .accountId != $account)' \
    "$EXTRA_GENESIS_ENROLLMENTS" >/dev/null ||
    { echo 'genesis: extra genesis enrollments are invalid' >&2; exit 2; }
  jq --slurpfile extra "$EXTRA_GENESIS_ENROLLMENTS" '.enrollments += $extra[0]' \
    "$dir/genesis.json" >"$dir/genesis-extended.json"
  mv "$dir/genesis-extended.json" "$dir/genesis.json"
fi

if [ -n "${GENESIS_PAY_OBSERVER:-}" ]; then
  case "$GENESIS_PAY_OBSERVER" in /*) ;; *) echo 'genesis: GENESIS_PAY_OBSERVER must be absolute' >&2; exit 2;; esac
  jq -e --slurpfile g "$dir/genesis.json" '
    def dec: type == "string" and test("^(0|[1-9][0-9]*)$");
    type == "object" and (keys == ["capability", "controlCapability", "enrolCapability", "subject"])
    and ([.subject, .capability, .controlCapability, .enrolCapability] | all(dec))
    and (.subject as $s | $g[0].enrollments | any(.key.subject == $s))' \
    "$GENESIS_PAY_OBSERVER" >/dev/null ||
    { echo 'genesis: the pay observer is invalid or not enrolled' >&2; exit 2; }
  jq --slurpfile o "$GENESIS_PAY_OBSERVER" '.payObserver = $o[0]' \
    "$dir/genesis.json" >"$dir/genesis-observed.json"
  mv "$dir/genesis-observed.json" "$dir/genesis.json"
fi

jq -n --slurpfile p "$params" --slurpfile g "$dir/genesis.json" '
  $p[0] as $p | def s: tostring;
  {type: "minidregg-participant-birth-context-v1", genesis: $g[0],
   template: {issuer: ($p.issuer|s), ownerBudget: ($p.ownerBudget|s), lifetime: ($p.lifetime|s)},
   sourceCapabilities: [($p.sponsor.spendCapabilityId|s)], funding: [],
   feePayer: ($p.sponsor.accountId|s),
   grants: [{kind: "object", target: ($p.factoryId|s),
             capability: ($p.sponsor.factoryObserveCapabilityId|s)},
            {kind: "account", target: ($p.sponsor.accountId|s),
             capability: ($p.sponsor.spendCapabilityId|s)}]}' >"$dir/sponsor-birth-context.json"
