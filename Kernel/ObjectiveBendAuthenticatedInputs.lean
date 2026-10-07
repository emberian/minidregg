/- Independent signed source/input queries, authenticated through the actual
NativeObservationController on ONE current image, delivered to the Objective gate
as its `ReadOracle`. Proposal (quotation) and final admission use this SAME
oracle; neither requires a fabricated final application command. The gate itself
re-checks every read against the signed claim (`ObjectiveBendNativeAdmission.
Authenticated.sound`) and computes the CAS guards; this module only authenticates.

Import order: NativeObservationController sits ABOVE DeclaredResourceController
(NativeObservationCodec → NativeHostCodec → DeclaredResourceController, and the
capability controllers), so this module cannot be imported by the gate; it is
installed by the hosts that call `DeclaredResourceController.admit`. -/
import Kernel.NativeObservationController
import Kernel.ObjectiveBendNativeAdmission
namespace Minidregg.Kernel.ObjectiveBendAuthenticatedInputs
open Minidregg.Compiler Minidregg.Theory Minidregg.Theory.TypedAuthorization
open Minidregg.Kernel.DurableDataIntent
open Minidregg.Compiler.NativeObservationCodec
set_option autoImplicit false
abbrev Deployment := CanonicalCellRegistry.Deployment
abbrev Durable := ResourceObservationAdmission.Durable
abbrev Environment := ObjectiveBendNativeAdmission.Environment
variable {F : Type} [Field F] [DecidableEq F]
variable {deployment : Deployment} {ground : DeclaredResourceController.Ground deployment}

inductive Failure where
  | malformed | selection | capacity
  | authorization
  deriving Repr

/-- Exactly one resourceScope query by this subject and nonce for this ref. -/
def matchesRef (environment : Environment deployment ground)
    (ref : ObjectiveInvocationClaim.InputRef) (signed : Signed) : Bool :=
  decide (signed.challenge.intent.subject = environment.subject ∧
    signed.challenge.intent.nonce = environment.nonce ∧
    signed.challenge.intent.purpose = .query ⟨ref.kind,ref.resource,.resourceScope⟩ ∧
    signed.challenge.intent.grants = [⟨ref.kind,ref.resource,ref.capability⟩])

/-- The admitted read of one authorized single-grant query. -/
def readOf (environment : Environment deployment ground)
    (profile : CanonicalRuntimeProfile.Profile F)
    (ref : ObjectiveInvocationClaim.InputRef) (signed : Signed)
    (authorized : NativeObservationController.AuthorizedIntent environment.context profile
      environment.federation environment.genesisHeight signed.challenge.intent) :
    Option (ObjectiveBendNativeAdmission.Read environment profile) := do
  if shape : matchesRef environment ref signed = true then
    have components := (of_decide_eq_true shape : signed.challenge.intent.subject = environment.subject ∧
      signed.challenge.intent.nonce = environment.nonce ∧
      signed.challenge.intent.purpose = .query ⟨ref.kind,ref.resource,.resourceScope⟩ ∧
      signed.challenge.intent.grants = [⟨ref.kind,ref.resource,ref.capability⟩])
    let index : Fin signed.challenge.intent.grants.length := ⟨0,by simp [components.2.2.2]⟩
    let admitted := authorized.grants index
    let funded : Option (RunComputeBudgetDomain.Prepared deployment ground.view signed.challenge.intent.subject) :=
      components.1.symm ▸ environment.compute
    some (ObjectiveBendNativeInput.admitRead environment.subject admitted.preparation admitted.checked
      (by change signed.challenge.intent.subject = environment.subject; exact components.1) funded)
  else none

/-- Pure request-shape checks precede crypto; every state-dependent check is the
existing signature-first observation receiver. -/
def authorizeQuery {m : Type → Type} [Monad m] (native : CredentialSignatureIO.Oracle m)
    (environment : Environment deployment ground) (profile : CanonicalRuntimeProfile.Profile F)
    (ref : ObjectiveInvocationClaim.InputRef) (bytes : List UInt8) :
    m (Except Failure (ObjectiveBendNativeAdmission.Read environment profile)) := do
  match signedCodec.decode bytes with
  | none => return .error .malformed
  | some signed =>
    if matchesRef environment ref signed != true then return .error .selection
    match ← NativeObservationController.authorize native environment.context profile
        environment.federation environment.genesisHeight signed with
    | .error _ => return .error .authorization
    | .ok authorized =>
      match readOf environment profile ref signed authorized with
      | none => return .error .selection
      | some read => return .ok read

private def authorizeList {m : Type → Type} [Monad m] (native : CredentialSignatureIO.Oracle m)
    (environment : Environment deployment ground) (profile : CanonicalRuntimeProfile.Profile F) :
    List ObjectiveInvocationClaim.InputRef → List (List UInt8) →
      m (Except Failure (List (ObjectiveBendNativeAdmission.Read environment profile)))
  | [],[] => pure (.ok [])
  | ref::refs,bytes::envelopes => do
      match ← authorizeQuery native environment profile ref bytes with
      | .error reason => return .error reason
      | .ok read =>
        match ← authorizeList native environment profile refs envelopes with
        | .error reason => return .error reason
        | .ok rest => return .ok (read :: rest)
  | _,_ => pure (.error .malformed)

/-- Authenticate the claim's source envelope and every input envelope, bounded
by the signed capacity before any signature work. -/
def authorize {m : Type → Type} [Monad m] (native : CredentialSignatureIO.Oracle m)
    (environment : Environment deployment ground) (profile : CanonicalRuntimeProfile.Profile F)
    (claim : ObjectiveInvocationClaim.Claim) :
    m (Except Failure (ObjectiveBendNativeAdmission.Authenticated environment profile claim)) := do
  if claim.sourceEnvelope.length + claim.inputEnvelopes.flatten.length > claim.capacity.turnBytes ||
      claim.inputRefs.length + 1 > claim.capacity.incidences then return .error .capacity
  match ← authorizeQuery native environment profile claim.source claim.sourceEnvelope with
  | .error reason => return .error reason
  | .ok source =>
    match ← authorizeList native environment profile claim.inputRefs claim.inputEnvelopes with
    | .error reason => return .error reason
    | .ok inputs =>
      match ObjectiveBendNativeAdmission.authenticate claim source inputs with
      | none => return .error .selection
      | some authenticated => return .ok authenticated

def Failure.reject : Failure → DeclaredResourceController.Reject
  | .malformed => .malformedCommand
  | .capacity => .bendExecution
  | .selection | .authorization => .observationRejected

/-- The production oracle. Every host entry that admits Objective commands
(`NativeHost.submitLoadedVia .invoke`, `NativeHostReplay.derive`) installs it. -/
def oracle {m : Type → Type} [Monad m] : ObjectiveBendNativeAdmission.ReadOracle m :=
  ⟨fun native environment profile claim => do
    match ← authorize native environment profile claim with
    | .error reason => return .error reason.reject
    | .ok authenticated => return .ok authenticated⟩

end Minidregg.Kernel.ObjectiveBendAuthenticatedInputs
