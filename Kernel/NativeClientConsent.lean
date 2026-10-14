/-
Local consent for a client which independently holds a verified source prefix.
The remote endpoint proposes bytes; it never chooses what custody signs. Every
header is reconstructed by the SAME observation/planning implementation used by
the native Host, under the caller's pinned configuration and retained intent.

This is the full-peer producer. It is not a permission to copy protected source
state to a client, and not a new admission bypass. The thin producer
(`Kernel.NativeThinConsent`) does not re-derive the plan: it checks what is
signed against the member's own command and the served target views, and
proves that what it shows is what commits. Signature validity remains the native verifier's
existing assumption. Keeping a verified prefix warm is a caller responsibility;
this module does not replay history for each signature. The prefix is a
`ConsentAnchor.Basis`: the full re-admission from genesis, or native admission
of every record after the client's own retained anchor.
-/
import Kernel.NativeHost
import Kernel.ConsentAnchor

namespace Minidregg.Kernel.NativeClientConsent

open Minidregg.Compiler
open Minidregg.Compiler.NativeHostCodec
open Minidregg.Compiler.NativeObservationCodec
open Minidregg.Kernel.NativeHost

set_option autoImplicit false

/-- Only this module constructs consent. `wanted` and `intentSignature` are
locally retained inputs, not values parsed from the proposed challenge. -/
structure ObservationConsent (config : Config) {target : Durable}
    (basis : ConsentAnchor.Basis config target) (wanted : Intent)
    (intentSignature candidate : List UInt8) where
  private mk ::
  challenge : Challenge
  derived : NativeObservationController.challenge
    (observationContext config basis.opened) config.profile config.federation
    config.genesisHeight wanted intentSignature = .ok challenge
  exactBytes : challengeCodec.encode challenge = candidate

/-- Why a proposed observation challenge received no consent. Every refusal
releases nothing; the reason only tells custody what to do next. -/
inductive ObservationRefusal where
  /-- The local observation planner refused the retained intent on the admitted source. -/
  | localPreparation
  /-- The proposal answers this exact retained intent and intent signature,
  under the same domain, semantics and federation, at another source height than
  the one custody admitted: the source moved between the Host's challenge and
  this check. Custody observes again on the new source and consents afresh. -/
  | staleObservation (remoteHeight localHeight : Nat)
  /-- Anything else: the proposal is not this custody's intent on its source. -/
  | differs
  deriving DecidableEq, Repr

/-- The prefix every stale-observation refusal carries on the consent wire; the
Rust client re-observes on it and on nothing else from this check. -/
def staleObservationTag : String := "stale observation:"

def ObservationRefusal.message : ObservationRefusal → String
  | .localPreparation => "local observation preparation refused"
  | .staleObservation remote here =>
      s!"{staleObservationTag} the remote challenge answers this intent at source height {remote}; " ++
        s!"the locally admitted source is at height {here}"
  | .differs => "remote challenge differs from locally prepared intent"

/-- The reason for a candidate that is not the local derivation's bytes. Stale
only when the decoded proposal carries the retained intent and signature, the
local domain, semantics and federation, and a different height; a proposal at
the SAME height that differs anywhere is the operator proposing other bytes. -/
def classifyMismatch (here : Challenge) (wanted : Intent)
    (intentSignature candidate : List UInt8) : ObservationRefusal :=
  match challengeCodec.decode candidate with
  | some remote =>
      if remote.intent = wanted ∧ remote.intentSignature = intentSignature ∧
          remote.domain = here.domain ∧ remote.semantics = here.semantics ∧
          remote.federation = here.federation ∧ remote.height ≠ here.height then
        .staleObservation remote.height here.height
      else .differs
  | none => .differs

/-- The entire challenge is compared: intent, ordered headers, signature,
profile, world/authority coordinates and clock. A remotely rendered JSON view
is neither read nor trusted. No header escapes on mismatch. A mismatch is only
classified (`classifyMismatch`); acceptance is exactly byte equality. -/
def checkObservation (config : Config) {target : Durable}
    (basis : ConsentAnchor.Basis config target) (wanted : Intent)
    (intentSignature candidate : List UInt8) :
    Except ObservationRefusal (ObservationConsent config basis wanted intentSignature candidate) :=
  match derived : NativeObservationController.challenge
      (observationContext config basis.opened) config.profile config.federation
      config.genesisHeight wanted intentSignature with
  | .error _ => .error .localPreparation
  | .ok challenge =>
      if exactBytes : challengeCodec.encode challenge = candidate then
        .ok ⟨challenge, derived, exactBytes⟩
      else .error (classifyMismatch challenge wanted intentSignature candidate)

/-- A stale label is given only to a proposal that decodes to THIS retained
intent and intent signature at another height. An intent changed anywhere
between custody's preparation and the Host's challenge is never stale. -/
theorem classify_stale {here : Challenge} {wanted : Intent}
    {intentSignature candidate : List UInt8} {remoteHeight localHeight : Nat}
    (stale : classifyMismatch here wanted intentSignature candidate =
      .staleObservation remoteHeight localHeight) :
    ∃ remote, challengeCodec.decode candidate = some remote ∧ remote.intent = wanted ∧
      remote.intentSignature = intentSignature ∧ remote.height = remoteHeight ∧
      localHeight = here.height ∧ remoteHeight ≠ localHeight := by
  unfold classifyMismatch at stale
  split at stale
  next remote decoded =>
    split at stale
    next same =>
      injection stale with remoteExact localExact
      subst remoteExact
      subst localExact
      exact ⟨remote, decoded, same.1, same.2.1, rfl, rfl, same.2.2.2.2.2⟩
    next => cases stale
  next => cases stale

theorem stale_observation_is_this_intent {config : Config} {target : Durable}
    {basis : ConsentAnchor.Basis config target} {wanted : Intent}
    {intentSignature candidate : List UInt8} {remoteHeight localHeight : Nat}
    (refused : checkObservation config basis wanted intentSignature candidate =
      .error (.staleObservation remoteHeight localHeight)) :
    ∃ remote, challengeCodec.decode candidate = some remote ∧ remote.intent = wanted ∧
      remote.intentSignature = intentSignature ∧ remote.height = remoteHeight ∧
      remoteHeight ≠ localHeight := by
  unfold checkObservation at refused
  split at refused
  next => cases refused
  next =>
    split at refused
    next => cases refused
    next =>
      obtain ⟨remote, decoded, intentExact, signatureExact, heightExact, _, apart⟩ :=
        classify_stale (Except.error.inj refused)
      exact ⟨remote, decoded, intentExact, signatureExact, heightExact, apart⟩

/-- A proposal whose decoded intent is not the retained one is refused as
`differs` (when it is not the local bytes at all), never as stale. -/
theorem changed_intent_not_stale {config : Config} {target : Durable}
    {basis : ConsentAnchor.Basis config target} {wanted : Intent}
    {intentSignature candidate : List UInt8} {remote : Challenge}
    (decoded : challengeCodec.decode candidate = some remote)
    (changed : remote.intent ≠ wanted) (remoteHeight localHeight : Nat) :
    checkObservation config basis wanted intentSignature candidate ≠
      .error (.staleObservation remoteHeight localHeight) := by
  intro refused
  obtain ⟨other, decodedOther, intentExact, _⟩ := stale_observation_is_this_intent refused
  rw [decoded] at decodedOther
  cases decodedOther
  exact changed intentExact

def ObservationConsent.headers {config : Config} {target : Durable}
    {basis : ConsentAnchor.Basis config target} {wanted : Intent}
    {intentSignature candidate : List UInt8}
    (consent : ObservationConsent config basis wanted intentSignature candidate) :
    List (List UInt8) := consent.challenge.headers

/-- The original draft remains an index of the capability. Birth finalization
is performed by the real planner, not a client rule permitting arbitrary changes
under a 'birth' tag. Every ordered role, index and header is compared as bytes. -/
structure PlanConsent (config : Config) {target : Durable}
    (basis : ConsentAnchor.Basis config target) (draft : Draft)
    (candidate : List UInt8) where
  private mk ::
  plan : SigningPlan
  derived : prepareLoaded config basis.opened draft = .ok plan
  exactBytes : signingPlanCodec.encode plan = candidate

def checkPlan (config : Config) {target : Durable}
    (basis : ConsentAnchor.Basis config target) (draft : Draft)
    (candidate : List UInt8) : Except String (PlanConsent config basis draft candidate) :=
  match derived : prepareLoaded config basis.opened draft with
  | .error _ => .error "local transaction preparation refused"
  | .ok plan =>
      if exactBytes : signingPlanCodec.encode plan = candidate then
        .ok ⟨plan, derived, exactBytes⟩
      else .error "remote signing plan differs from locally prepared intent"

def PlanConsent.headers {config : Config} {target : Durable}
    {basis : ConsentAnchor.Basis config target} {draft : Draft}
    {candidate : List UInt8}
    (consent : PlanConsent config basis draft candidate) : List (List UInt8) :=
  consent.plan.slots.map SigningSlot.header

/-- Connect preparation to the locally retained observation intent. Query-only
intents have no transaction consent path. This checks consent, not admission:
the ordinary native receiver must still authenticate and authorize submission. -/
def checkIntentPlan (config : Config) {target : Durable}
    (basis : ConsentAnchor.Basis config target) (wanted : Intent)
    (candidate : List UInt8) : Except String (List (List UInt8)) :=
  match wanted.purpose with
  | .query _ => .error "query intent cannot authorize transaction signing"
  | .prepare draft => (checkPlan config basis draft candidate).map PlanConsent.headers

/-- An accepting observation has an actual native derivation from the LOCAL
intent and prefix, and its complete canonical bytes equal the proposal. This
states the exact consent boundary; it does not claim cryptographic security. -/
theorem observation_origin {config : Config} {target : Durable}
    {basis : ConsentAnchor.Basis config target} {wanted : Intent}
    {intentSignature candidate : List UInt8}
    (consent : ObservationConsent config basis wanted intentSignature candidate) :
    ∃ challenge, NativeObservationController.challenge
      (observationContext config basis.opened) config.profile config.federation
      config.genesisHeight wanted intentSignature = .ok challenge ∧
      challengeCodec.encode challenge = candidate ∧
      consent.headers = challenge.headers :=
  ⟨consent.challenge, consent.derived, consent.exactBytes, rfl⟩

/-- In particular this covers all planner branches, not just invocation or a
fixed fixture. It inherits the planner's meaning, including its unresolved
semantic/proof boundaries, rather than asserting that meaning is correct. -/
theorem plan_origin {config : Config} {target : Durable}
    {basis : ConsentAnchor.Basis config target} {draft : Draft}
    {candidate : List UInt8}
    (consent : PlanConsent config basis draft candidate) :
    ∃ plan, prepareLoaded config basis.opened draft = .ok plan ∧
      signingPlanCodec.encode plan = candidate ∧
      consent.headers = plan.slots.map SigningSlot.header :=
  ⟨consent.plan, consent.derived, consent.exactBytes, rfl⟩

/-- No modified frame can receive consent against the same local prefix/draft,
even when its separate server-authored presentation claims identical metadata. -/
theorem changed_plan_refused {config : Config} {target : Durable}
    (basis : ConsentAnchor.Basis config target) (draft : Draft)
    (plan : SigningPlan) (candidate : List UInt8)
    (derived : prepareLoaded config basis.opened draft = .ok plan)
    (different : signingPlanCodec.encode plan ≠ candidate) :
    checkPlan config basis draft candidate =
      .error "remote signing plan differs from locally prepared intent" := by
  unfold checkPlan
  split
  next error actual => simp [derived] at actual
  next expected actual =>
    have same : plan = expected := Except.ok.inj (derived.symm.trans actual)
    subst expected
    simp only [dif_neg different]

#assert_axioms classify_stale
#assert_axioms stale_observation_is_this_intent
#assert_axioms changed_intent_not_stale

end Minidregg.Kernel.NativeClientConsent
