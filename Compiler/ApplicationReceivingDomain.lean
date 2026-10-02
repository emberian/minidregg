/- Pure application receiving identities shared by actual source codecs and
CanonicalRuntimeProfile. Keep this leaf free of receivers/NativeHost imports.
A frame preserves representation; receivingContract also commits the authority,
freshness, replay, renewal and physical-custody distinctions behind those bytes.
-/
import Init

namespace Minidregg.Compiler.ApplicationReceivingDomain

def streamContinuityChallengeFrame : List UInt8 :=
  "DREGG/APPLICATION/STREAM-CONTINUITY-CHALLENGE/v1".toUTF8.toList

def streamContinuityRequestFrame : List UInt8 :=
  "DREGG/APPLICATION/STREAM-CONTINUITY-REQUEST/v1".toUTF8.toList

def streamContinuityAttestationFrame : List UInt8 :=
  "DREGG/APPLICATION/STREAM-CONTINUITY-ATTESTATION/v1".toUTF8.toList

def routeAdmissionChallengeFrame : List UInt8 :=
  "DREGG/APPLICATION/ROUTE-ADMISSION-CHALLENGE/v1".toUTF8.toList

def routeAdmissionRequestFrame : List UInt8 :=
  "DREGG/APPLICATION/ROUTE-ADMISSION-REQUEST/v1".toUTF8.toList

def routeAdmissionAttestationFrame : List UInt8 :=
  "DREGG/APPLICATION/ROUTE-ADMISSION-ATTESTATION/v1".toUTF8.toList

def routeBoundDispatchFrame : List UInt8 :=
  "DREGG/APPLICATION/ROUTE-BOUND-DISPATCH/v1".toUTF8.toList

def noRecordRefusalFrame : List UInt8 :=
  "DREGG/APPLICATION/DISPATCH-NO-RECORD-REFUSAL/v1".toUTF8.toList

def dispatchCommittedPermitFrame : List UInt8 :=
  "DREGG/APPLICATION/DISPATCH-COMMITTED-PERMIT/v1".toUTF8.toList

def agentDispatchCommittedPermitFrame : List UInt8 :=
  "DREGG/APPLICATION/AGENT-DISPATCH-COMMITTED-PERMIT/v2".toUTF8.toList

def streamContinuityProbeProtocol : List UInt8 :=
  "dregg.authority.continuity.v1".toUTF8.toList

def routeAdmissionProbeProtocol : List UInt8 :=
  "dregg.authority.route-admission.v1".toUTF8.toList

/-- Local compatible-upgrade evidence is not a cryptographic authority or
permission to reuse a stopped generation. Runtime consumers still enforce its
root ownership, exact image/config pins and signed source reenrollment. -/
def receivingContract : List UInt8 :=
  ("DREGG.APPLICATION-RECEIVING/v2:" ++
   "physical-permit-fresh-cas-winner-and-installed;" ++
   "confirmed-recovered-historical-receipt-never-redelivers;" ++
   "exact-historical-call-lookup-before-current-admission;" ++
   "marker-clear-only-verified-whole-history-call-absence-and-fresh-physical-tip;" ++
   "unknown-conflicting-call-retains-uncertainty;" ++
   "route-binding-compared-to-same-current-signed-admission-before-cas;" ++
   "post-cas-current-tip-and-physical-custody-guard;" ++
   "renew-same-human-web-binding-domain-semantics-generations-subject-ticket-fingerprint;" ++
   "signed-stream32-and-attempt32-nonces-minimum-height-root-current-tip;" ++
   "renewal-read-only-no-app-rpc-no-cas-no-billing;" ++
   "admission-anchored-bounded-physical-lease-reject-late-stale-replayed-renewal;" ++
   "new-human-web-api-route-distinct-registration32-challenge;" ++
   "regrant-new-immutable-binding-never-revives-old-lease;" ++
   "initial-route-single-durable-seal-before-memory-publication;" ++
   "interrupted-seal-refuses-same-generation-restart;" ++
   "compatible-upgrade-root-evidence-not-source-authority;" ++
   "immutable-selected-profile-exact-image-config-identity-pins;" ++
   "per-store-runtime-pending-fences-launch-ready-after-unit-reload;" ++
   "checked-new-generation-start-then-signed-session-reenrollment-and-route-admission;" ++
   "member-owner-admin-distinct-from-explicit-lifecycle-manager;" ++
   "owner-signed-policy-install-and-current-revocable-object-delegation-required;" ++
   "lifecycle-manager-no-program-admin-or-share-issuer-transfer;" ++
   "managed-app-package-exact-same-owner-manager-source-linkage;" ++
   "dispatch-owner-issuer-preserved-manager-derived-from-authenticated-app-law").toUTF8.toList

end Minidregg.Compiler.ApplicationReceivingDomain
