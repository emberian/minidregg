/- Independent signed input queries. Proposal and final admission use this SAME
factory; neither requires a fabricated final application command. Native effect
permission and publication remain separate. -/
import Kernel.NativeObservationController
import Kernel.ObjectiveBendNativeInput
import Compiler.ObjectiveInvocationClaim
namespace Minidregg.Kernel.ObjectiveBendAuthenticatedInputs
open Minidregg.Compiler Minidregg.Theory Minidregg.Theory.TypedAuthorization
open Minidregg.Kernel.DurableDataIntent
open Minidregg.Compiler.NativeObservationCodec
set_option autoImplicit false
abbrev Deployment := CanonicalCellRegistry.Deployment
abbrev Durable := ResourceObservationAdmission.Durable
variable {F : Type} [Field F] [DecidableEq F]
variable {deployment : Deployment} {durable : Durable}

structure Environment (deployment : Deployment) (durable : Durable) where
  context : ResourceObservationAdmission.Context deployment durable
  federation : FederationId
  genesisHeight : Nat
  subject : SubjectId
  nonce : Nat
  compute : Option (RunComputeBudgetDomain.Prepared deployment durable.snapshot subject)

inductive Failure where
  | malformed | selection | capacity
  | authorization (reason : NativeObservationController.Refusal)
  deriving Repr

def matches (environment : Environment deployment durable)
    (ref : ObjectiveInvocationClaim.InputRef) (signed : Signed) : Bool :=
  decide (signed.challenge.intent.subject = environment.subject ∧
    signed.challenge.intent.nonce = environment.nonce ∧
    signed.challenge.intent.purpose = .query ⟨ref.kind,ref.resource,.resourceScope⟩ ∧
    signed.challenge.intent.grants = [⟨ref.kind,ref.resource,ref.capability⟩])

structure Query (environment : Environment deployment durable)
    (profile : CanonicalRuntimeProfile.Profile F)
    (ref : ObjectiveInvocationClaim.InputRef) (bytes : List UInt8) where
  private mk ::
  signed : Signed
  decoded : signedCodec.decode bytes = some signed
  shapeExact : matches environment ref signed = true
  authorized : NativeObservationController.AuthorizedIntent environment.context profile
    environment.federation environment.genesisHeight signed.challenge.intent
  read : ObjectiveBendNativeInput.AdmittedRead environment.context profile environment.subject
  selectorExact : read.kind = ref.kind ∧ read.request.target.value = ref.resource ∧ read.capability = ref.capability
  valueExact : read.value.root = ref.root
  guards : List ReadGuard
  guardsRoots : ∀ guard ∈ guards, guard.expectedRoot = durable.snapshot.model.roots guard.cellId
  inputGuard : (⟨⟨ref.resource⟩,durable.snapshot.model.roots ⟨ref.resource⟩⟩ : ReadGuard) ∈ guards

def fromAuthorized (environment : Environment deployment durable)
    (profile : CanonicalRuntimeProfile.Profile F)
    (ref : ObjectiveInvocationClaim.InputRef) (bytes : List UInt8) (signed : Signed)
    (decoded : signedCodec.decode bytes = some signed)
    (authorized : NativeObservationController.AuthorizedIntent environment.context profile
      environment.federation environment.genesisHeight signed.challenge.intent) :
    Option (Query environment profile ref bytes) := do
  if shape : matches environment ref signed = true then
    have components := (of_decide_eq_true shape : signed.challenge.intent.subject = environment.subject ∧
      signed.challenge.intent.nonce = environment.nonce ∧
      signed.challenge.intent.purpose = .query ⟨ref.kind,ref.resource,.resourceScope⟩ ∧
      signed.challenge.intent.grants = [⟨ref.kind,ref.resource,ref.capability⟩])
    let index : Fin signed.challenge.intent.grants.length := ⟨0,by simp [components.2.2.2]⟩
    let admitted := authorized.grants index
    let funded : Option (RunComputeBudgetDomain.Prepared deployment durable.snapshot signed.challenge.intent.subject) :=
      components.1.symm ▸ environment.compute
    let read := ObjectiveBendNativeInput.admitRead environment.subject admitted.preparation admitted.checked
      (by change signed.challenge.intent.subject = environment.subject; exact components.1) funded
    if selector : read.kind = ref.kind ∧ read.request.target.value = ref.resource ∧ read.capability = ref.capability then
      if root : read.value.root = ref.root then
        let laws ← ResourceObservationAdmission.lawReadGuards admitted.preparation
        let inputGuard : ReadGuard := ⟨⟨ref.resource⟩,durable.snapshot.model.roots ⟨ref.resource⟩⟩
        let guards := inputGuard :: admitted.preparation.clock.readGuard ::
          (laws.map fun (cell,root) => (⟨⟨cell⟩,root⟩ : ReadGuard))
        if roots : ∀ guard ∈ guards, guard.expectedRoot = durable.snapshot.model.roots guard.cellId then
          some ⟨signed,decoded,shape,authorized,read,selector,root,guards,roots,by simp [guards]⟩
        else none
      else none
    else none
  else none

def authorizeQuery (native : CredentialSignatureIO.NativeConfig)
    (environment : Environment deployment durable) (profile : CanonicalRuntimeProfile.Profile F)
    (ref : ObjectiveInvocationClaim.InputRef) (bytes : List UInt8) :
    IO (Except Failure (Query environment profile ref bytes)) := do
  match decoded : signedCodec.decode bytes with
  | none => return .error .malformed
  | some signed =>
    -- Pure request-shape checks precede crypto. All state-dependent checks are
    -- still performed by the existing signature-first observation receiver.
    if matches environment ref signed != true then return .error .selection
    match ← NativeObservationController.authorize native environment.context profile
        environment.federation environment.genesisHeight signed with
    | .error reason => return .error (.authorization reason)
    | .ok authorized =>
      match fromAuthorized environment profile ref bytes signed decoded authorized with
      | none => return .error .selection
      | some query => return .ok query

inductive Queries (environment : Environment deployment durable) (profile : CanonicalRuntimeProfile.Profile F) :
    List ObjectiveInvocationClaim.InputRef → List (List UInt8) → Type
  | nil : Queries environment profile [] []
  | cons {ref bytes refs envelopes} (query : Query environment profile ref bytes)
      (rest : Queries environment profile refs envelopes) :
      Queries environment profile (ref::refs) (bytes::envelopes)

structure Verified (environment : Environment deployment durable) (profile : CanonicalRuntimeProfile.Profile F)
    (claim : ObjectiveInvocationClaim.Claim) where
  private mk ::
  queries : Queries environment profile claim.inputRefs claim.inputEnvelopes

private def authorizeList (native : CredentialSignatureIO.NativeConfig)
    (environment : Environment deployment durable) (profile : CanonicalRuntimeProfile.Profile F) :
    (refs : List ObjectiveInvocationClaim.InputRef) → (envelopes : List (List UInt8)) →
      IO (Except Failure (Queries environment profile refs envelopes))
  | [],[] => pure (.ok .nil)
  | ref::refs,bytes::envelopes => do
      match ← authorizeQuery native environment profile ref bytes with
      | .error reason => return .error reason
      | .ok query =>
        match ← authorizeList native environment profile refs envelopes with
        | .error reason => return .error reason
        | .ok rest => return .ok (.cons query rest)
  | _,_ => pure (.error .malformed)

def authorize (native : CredentialSignatureIO.NativeConfig)
    (environment : Environment deployment durable) (profile : CanonicalRuntimeProfile.Profile F)
    (claim : ObjectiveInvocationClaim.Claim) : IO (Except Failure (Verified environment profile claim)) := do
  if claim.inputEnvelopes.flatten.length > claim.capacity.turnBytes ||
      claim.inputRefs.length > claim.capacity.incidences then return .error .capacity
  match ← authorizeList native environment profile claim.inputRefs claim.inputEnvelopes with
  | .error reason => return .error reason
  | .ok queries => return .ok ⟨queries⟩

def Queries.reads {environment : Environment deployment durable} {profile : CanonicalRuntimeProfile.Profile F}
    {refs envelopes} : Queries environment profile refs envelopes →
    List (ObjectiveBendNativeInput.AdmittedRead environment.context profile environment.subject)
  | .nil => []
  | .cons query rest => query.read :: rest.reads

def Queries.guards {environment : Environment deployment durable} {profile : CanonicalRuntimeProfile.Profile F}
    {refs envelopes} : Queries environment profile refs envelopes → List ReadGuard
  | .nil => []
  | .cons query rest => query.guards ++ rest.guards

def Verified.reads {environment : Environment deployment durable} {profile : CanonicalRuntimeProfile.Profile F}
    {claim} (verified : Verified environment profile claim) := verified.queries.reads

def Verified.guards {environment : Environment deployment durable} {profile : CanonicalRuntimeProfile.Profile F}
    {claim} (verified : Verified environment profile claim) := verified.queries.guards

theorem Queries.guards_roots {environment : Environment deployment durable} {profile : CanonicalRuntimeProfile.Profile F}
    {refs envelopes} (queries : Queries environment profile refs envelopes) :
    ∀ guard ∈ queries.guards, guard.expectedRoot = durable.snapshot.model.roots guard.cellId := by
  induction queries with
  | nil => simp [Queries.guards]
  | cons query rest ih =>
    intro guard member
    rcases List.mem_append.mp member with member | member
    · exact query.guardsRoots guard member
    · exact ih guard member

theorem Verified.guards_roots {environment : Environment deployment durable} {profile : CanonicalRuntimeProfile.Profile F}
    {claim} (verified : Verified environment profile claim) :
    ∀ guard ∈ verified.guards, guard.expectedRoot = durable.snapshot.model.roots guard.cellId :=
  verified.queries.guards_roots
#assert_axioms Queries.guards_roots
#assert_axioms Verified.guards_roots
end Minidregg.Kernel.ObjectiveBendAuthenticatedInputs
