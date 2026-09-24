/- The sole signed resource invocation receiver. A one-target transaction is
an ordinary finite transaction, not a separate admission or persistence path.
Every target and the shared replay marker form one actual MultiCellHyperedge
PreparedTuple; all signatures and current policies precede its single CAS. -/
import Kernel.ResourceTransaction
import Kernel.ResourceObservationAdmission
import Compiler.ResourceAuthorityProjection

namespace Minidregg.Kernel.DeclaredResourceController
open Minidregg.Compiler
open Minidregg.Compiler.CanonicalPolicyAdmission
open Minidregg.Compiler.CredentialAuthorityDomain
open Minidregg.Compiler.CredentialAuthorityDomainReceiver
open Minidregg.Compiler.CredentialAuthorityPolicyRegistry
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Kernel.MultiCellHyperedge
open Minidregg.Kernel.DurableDataIntent
open Minidregg.Theory
open Minidregg.Theory.CellRegistry
open Minidregg.Theory.CellState
open Minidregg.Theory.IndexedProgram
open Minidregg.Theory.TypedAuthorization
set_option autoImplicit false
set_option maxHeartbeats 800000

abbrev Source (command : Command) := { actual : Command // actual = command }
variable {F : Type} [Field F] {deployment : Deployment}
  {profile : CanonicalRuntimeProfile.Profile F} {ambient : Ambient}
  {durable : Durable} {command : Command}

def layout (prepared : PreparedInvocation deployment profile ambient durable command) :
    CellLayout (Incidence command) where
  schema | some i => command.targets[i].schema | none => CredentialAuthorityState.schema.{0,0}
  fieldDecidableEq incidence := by cases incidence <;> dsimp <;> infer_instance
  resourceDecidableEq incidence := by cases incidence <;> dsimp <;> infer_instance
  materializer | some i => command.targets[i].materializer | none => CredentialAuthorityStateCodec.materializer
  projectAuthority := fun _ _ => prepared.authority.snapshot.authState
  cellId | some i => ⟨command.targets[i].target⟩ | none => deployment.authorityAnchor.catalogueCellId

local instance fieldEq (prepared : PreparedInvocation deployment profile ambient durable command)
    (incidence : Incidence command) : DecidableEq ((layout prepared).schema incidence).Field :=
  (layout prepared).fieldDecidableEq incidence
local instance resourceEq (prepared : PreparedInvocation deployment profile ambient durable command)
    (incidence : Incidence command) : DecidableEq ((layout prepared).schema incidence).Resource :=
  (layout prepared).resourceDecidableEq incidence

def rawLeg (prepared : PreparedInvocation deployment profile ambient durable command)
    (source : Source command) : (incidence : Incidence command) → CandidateLegData (layout prepared) incidence
  | some i =>
      { pre := (prepared.targets i).pre
        patch := targetPatch command.targets[i] (prepared.targets i).pre (prepared.targets i).post
        request := ⟨command.targets[i].kind, requestFor prepared.authority.snapshot profile.semantics
          ambient command command.targets[i] (prepared.targets i).pre.root⟩
        Postcondition := fun logical =>
          (targetPatch command.targets[i] (prepared.targets i).pre (prepared.targets i).post).ResultAt
            (prepared.targets i).pre.logical logical }
  | none =>
      { pre := prepared.authority.snapshot.cell
        patch := markerPatch prepared.authority.snapshot profile.semantics source.val
        request := ⟨source.val.first.kind, request prepared.authority.snapshot profile.semantics
          ambient source.val prepared.authority.snapshot.cell.root⟩
        Postcondition := fun logical =>
          (markerPatch prepared.authority.snapshot profile.semantics source.val).ResultAt
            prepared.authority.snapshot.logical logical }

def bindFamily (prepared : PreparedInvocation deployment profile ambient durable command)
    (source : Source command) (_portals : Incidence command → Portal) :
    (incidence : Incidence command) → SemanticLegBinding.{0,0,0,0,0,0} (rawLeg prepared source incidence)
  | some i =>
      { Nullifier := Nat
        family := by
          change SemanticEffectFamily command.targets[i].schema command.targets[i].materializer Nat
          exact targetFamily deployment prepared.authority.snapshot profile.semantics ambient command
            command.targets[i] (prepared.targets i).pre
        declaration := ()
        outcome := (prepared.targets i).post
        preExact := rfl
        requestExact := rfl
        effectsExact := by simp only [rawLeg, targetFamily, requestFor, id_eq]
        patchExact := rfl
        postconditionExact := fun _ => Iff.rfl }
  | none =>
      { Nullifier := Nat
        family := markerFamily prepared.authority.snapshot profile.semantics ambient
        declaration := source.val
        outcome := ()
        preExact := rfl, requestExact := rfl, effectsExact := rfl, patchExact := rfl
        postconditionExact := fun _ => Iff.rfl }

def plan (prepared : PreparedInvocation deployment profile ambient durable command) :
    PreparationPlan.{0,0,0,0,0,0} (layout prepared) (Source command) where
  leg := rawLeg prepared
  jointDigest := fun source => effectsDigest prepared.authority.snapshot.domain profile.semantics source.val
  legEffectsDigest := fun source _ => effectsDigest prepared.authority.snapshot.domain profile.semantics source.val
  bindFamily := bindFamily prepared

def validated (prepared : PreparedInvocation deployment profile ambient durable command) :
    (incidence : Incidence command) → ValidatedPatch ((layout prepared).materializer incidence)
      (rawLeg prepared ⟨command, rfl⟩ incidence).pre
      (rawLeg prepared ⟨command, rfl⟩ incidence).patch
  | some i => (prepared.targets i).candidate.validated
  | none => prepared.marker.prepared.validated

theorem postconditions (prepared : PreparedInvocation deployment profile ambient durable command) :
    ∀ incidence, (rawLeg prepared ⟨command, rfl⟩ incidence).Postcondition
      (validated prepared incidence).apply.logical := by
  intro incidence
  cases incidence with
  | some i => exact (prepared.targets i).candidate.postcondition
  | none => exact prepared.marker.prepared.validated.resultAt

def prepareTuple (prepared : PreparedInvocation deployment profile ambient durable command) :
    Option (PreparedTuple (plan prepared)) :=
  if distinct : Function.Injective (layout prepared).cellId then
    some
      { source := ⟨command, rfl⟩
        primary := none
        validated := validated prepared
        postconditions := postconditions prepared
        cellIdsDistinct := distinct
        requestRoots := by intro incidence; cases incidence <;> rfl
        requestEffects := by intro incidence; cases incidence <;> rfl }
  else none

abbrev bytesSlots := ResourceAuthorityProjection.bytesSlots

/-- Exact scalar/content projection from the committed old and candidate final
states. Local names remain convenient; joint names expose every declared
participant without granting a view of unrelated cells. -/
def targetProjection (target : Target) (before after : LogicalState target.schema) : List (String × Int) := by
  cases target with
  | mk kind id capability version root payload observe =>
    cases payload with
    | scalar _ => exact
        match DeclaredEffectPageMaterializer.pageAt before, DeclaredEffectPageMaterializer.pageAt after with
        | some old, some post => DeclaredResourceProjection.project id old post
        | _, _ => []
    | content content => exact
        match HyperdocumentContentPageMaterializer.pageAt before, HyperdocumentContentPageMaterializer.pageAt after with
        | some old, some post => ContentResource.project old post content
        | _, _ => []

def incidenceTarget (command : Command) : Incidence command → Target
  | some i => command.targets[i]
  | none => command.first

def observeVerb : (kind : ResourceKind) → Verb kind
  | .object => .observeObject
  | .account => .observeAccount
  | .program => .observeProgram

/-- This signature is specific to the exact proposed joint command, one
participant's real loaded pre-state and the current authority snapshot. -/
def readRequest (prepared : PreparedInvocation deployment profile ambient durable command)
    (i : TargetIndex command) : Request command.targets[i].kind :=
  { requestFor prepared.authority.snapshot profile.semantics ambient command command.targets[i]
      (prepared.targets i).before.payload.root with
    verb := observeVerb command.targets[i].kind
    effectsDigest := (Sp800185Cshake256.hash "DREGG.RESOURCE.TRANSACTION.OBSERVE/v3".toUTF8.toList
      ((StreamCodec.product bytesStream StreamCodec.nat).encode
        (commandBytes prepared.authority.snapshot.domain profile.semantics command,
          command.targets[i].target))).digest }

def firstIndex (prepared : PreparedInvocation deployment profile ambient durable command) : TargetIndex command :=
  ⟨0, List.length_pos_iff.mpr prepared.nonempty⟩

/- These slots depend on the admitted tuple and incidence, but not on which
old/new logical state the policy examines. Derive them here once per step;
the caller cannot inject an independent request or command projection. -/
def projectCommonSlots (prepared : PreparedInvocation deployment profile ambient durable command)
    (primary : Incidence command) (source : Source command) : List (String × Int) :=
  let selected := incidenceTarget command primary
  let preRoot := match primary with
    | some i => (prepared.targets i).pre.root
    | none => prepared.authority.snapshot.cell.root
  CanonicalRuntimeProfile.requestSlots
      (requestFor prepared.authority.snapshot profile.semantics ambient command selected preRoot) ++
    bytesSlots "command/bytes" 0 (commandCodec.encode source.val)

def projectWithCommon (prepared : PreparedInvocation deployment profile ambient durable command)
    (primary : Incidence command) (common : List (String × Int))
    (logical : (incidence : Incidence command) → LogicalState ((layout prepared).schema incidence)) :
    Minidregg.Pred.State :=
  let localIndex := primary.getD (firstIndex prepared)
  let localSlots :=
    bytesSlots "resource/bytes" 0 (command.targets[localIndex].materializer.codec.encode (logical (some localIndex))) ++
    targetProjection command.targets[localIndex] (prepared.targets localIndex).pre.logical (logical (some localIndex))
  let joint := (List.finRange command.targets.length).flatMap fun i =>
    (bytesSlots "resource/bytes" 0 (command.targets[i].materializer.codec.encode (logical (some i))) ++
      targetProjection command.targets[i] (prepared.targets i).pre.logical (logical (some i))).map fun slot =>
        (s!"joint/target/{command.targets[i].target}/{slot.1}", slot.2)
  ⟨common ++ localSlots ++ joint⟩

def project (prepared : PreparedInvocation deployment profile ambient durable command)
    (primary : Incidence command) (source : Source command)
    (logical : (incidence : Incidence command) → LogicalState ((layout prepared).schema incidence)) :
    Minidregg.Pred.State :=
  projectWithCommon prepared primary (projectCommonSlots prepared primary source) logical

theorem projectWithCommon_exact (prepared : PreparedInvocation deployment profile ambient durable command)
    (primary : Incidence command) (source : Source command)
    (logical : (incidence : Incidence command) → LogicalState ((layout prepared).schema incidence)) :
    projectWithCommon prepared primary (projectCommonSlots prepared primary source) logical =
      project prepared primary source logical := rfl

/- The tuple's generic `pre` selector constructs a complete raw leg, including
the hash of the entire signed command's request. These projections select the
same prepared cells without rebuilding that unused request for every policy
read. The exact-context constructor below checks both equalities. -/
def policyPreCell (prepared : PreparedInvocation deployment profile ambient durable command) :
    (incidence : Incidence command) →
      CellState.Materialized ((layout prepared).materializer incidence)
  | some i => (prepared.targets i).pre
  | none => prepared.authority.snapshot.cell

theorem policyPreCell_exact (prepared : PreparedInvocation deployment profile ambient durable command)
    (tuple : PreparedTuple (plan prepared)) (incidence : Incidence command) :
    policyPreCell prepared incidence = tuple.pre incidence := by
  have sourceExact : tuple.source = ⟨command, rfl⟩ := Subtype.ext tuple.source.property
  unfold PreparedTuple.pre
  rw [sourceExact]
  cases incidence <;> rfl

def policyPostState (prepared : PreparedInvocation deployment profile ambient durable command) :
    (incidence : Incidence command) → LogicalState ((layout prepared).schema incidence) :=
  fun incidence => ((validated prepared incidence).apply).logical

theorem policyPostState_exact (prepared : PreparedInvocation deployment profile ambient durable command)
    (tuple : PreparedTuple (plan prepared)) (incidence : Incidence command) :
    policyPostState prepared incidence = tuple.logicalPost incidence := by
  apply congrArg Materialized.logical
  apply Materialized.ext
  simp only [PreparedTuple.post, ValidatedPatch.apply]
  have sourceExact : tuple.source = ⟨command, rfl⟩ := Subtype.ext tuple.source.property
  rw [sourceExact]
  rfl

def step (prepared : PreparedInvocation deployment profile ambient durable command)
    (tuple : PreparedTuple (plan prepared)) (incidence : Incidence command) : PolicyStepContext :=
  let common := projectCommonSlots prepared incidence tuple.source
  PolicyStepContext.ofPreparedTupleExact
    (fun _ logical => projectWithCommon prepared incidence common logical) profile.semantics
    { tuple with primary := incidence }
    (policyPreCell prepared) (policyPostState prepared)
    (policyPreCell_exact prepared tuple) (policyPostState_exact prepared tuple)

theorem step_prepared_exact
    (prepared : PreparedInvocation deployment profile ambient durable command)
    (tuple : PreparedTuple (plan prepared)) (incidence : Incidence command) :
    step prepared tuple incidence =
      PolicyStepContext.ofPreparedTuple (project prepared incidence) profile.semantics
        { tuple with primary := incidence } := by
  unfold step
  rw [PolicyStepContext.ofPreparedTupleExact_eq]
  rfl

def policyConfig [DecidableEq F]
    (prepared : PreparedInvocation deployment profile ambient durable command)
    (tuple : PreparedTuple (plan prepared)) (incidence : Incidence command) : CanonicalPolicyConfig F :=
  CredentialAuthorityPolicyRegistry.config profile.compilerProfile prepared.authority.snapshot
    (sourceStore prepared.authority.snapshot.domain prepared.directory.directory)
    (sourceCapabilityPortal prepared.authority.snapshot
      (operationMarker prepared.authority.snapshot.domain profile.semantics command))
    (step prepared tuple incidence)

def portals [DecidableEq F]
    (prepared : PreparedInvocation deployment profile ambient durable command)
    (tuple : PreparedTuple (plan prepared)) : Incidence command → Portal :=
  fun incidence => (policyConfig prepared tuple incidence).portal

theorem source_request_epoch_current
    (prepared : PreparedInvocation deployment profile ambient durable command)
    (tuple : PreparedTuple (plan prepared)) (incidence : Incidence command) :
    (tuple.request incidence).2.policyEpoch =
      prepared.authority.snapshot.authState.policyEpoch (tuple.request incidence).2.policyId := by
  cases incidence <;> rfl

theorem source_request_revision_current
    (prepared : PreparedInvocation deployment profile ambient durable command)
    (tuple : PreparedTuple (plan prepared)) (incidence : Incidence command) :
    (tuple.request incidence).2.policyRevision =
      prepared.authority.snapshot.authState.policyRevision (tuple.request incidence).2.policyId := by
  cases incidence <;> rfl

def authorizeLeg [DecidableEq F]
    (prepared : PreparedInvocation deployment profile ambient durable command)
    (tuple : PreparedTuple (plan prepared)) (incidence : Incidence command)
    (signature : CredentialSignatureAdmission.CheckedSignature prepared.authority.snapshot) :
    Except Reject (Authorized (portals prepared tuple incidence)
      prepared.authority.snapshot.authState (tuple.request incidence).2) := do
  let wanted := (tuple.request incidence).2
  let context := step prepared tuple incidence
  let config := CredentialAuthorityPolicyRegistry.config profile.compilerProfile
    prepared.authority.snapshot
    (sourceStore prepared.authority.snapshot.domain prepared.directory.directory)
    (sourceCapabilityPortal prepared.authority.snapshot
      (operationMarker prepared.authority.snapshot.domain profile.semantics command))
    context
  let capability := (incidenceTarget command incidence).capability
  let evidence ← requireSome .capabilityRejected (sourceCapabilityOnlyEvidence profile.compilerProfile prepared.authority.snapshot
    (sourceStore prepared.authority.snapshot.domain prepared.directory.directory)
    (operationMarker prepared.authority.snapshot.domain profile.semantics command)
    context wanted capability signature)
  let committed ← requireSome .policyUnavailable (config.registry.resolve wanted.policyId wanted.policyRevision)
  let witness := canonicalWitness profile.compilerProfile.compiler committed
    context.oldState context.newState
  if inputsInRange profile.compilerProfile.compiler committed.record.predicate witness.oldState witness.newState != true then
    throw .policyInputRange
  if !decide (castInjOn F (intsOf committed.record.predicate witness.oldState witness.newState)) then
    throw .policyCastAlias
  requireSome .policyRejected (CanonicalPolicyAdmission.admit config prepared.authority.snapshot.authState wanted evidence witness
    (.policy wanted.policyId wanted.policyRevision)
    (source_request_epoch_current prepared tuple incidence)
    (source_request_revision_current prepared tuple incidence))

structure SignedCommand where
  commandBytes : List UInt8
  targetEnvelopes : List (List UInt8)
  observeEnvelopes : List (List UInt8)
  authorityEnvelope : List UInt8
  deriving DecidableEq, Repr

def SignedCommand.envelope (signed : SignedCommand) (command : Command) : Incidence command → List UInt8
  | some i => signed.targetEnvelopes[i.val]?.getD []
  | none => signed.authorityEnvelope

def readContext (prepared : PreparedInvocation deployment profile ambient durable command) :
    ResourceObservationAdmission.Context deployment durable :=
  ⟨prepared.directory, prepared.authority⟩

def readCapability (i : TargetIndex command) : CapabilityId :=
  command.targets[i].observeCapability.getD ⟨0⟩

def readPreparation [DecidableEq F] (prepared : PreparedInvocation deployment profile ambient durable command)
    (i : TargetIndex command) :=
  ResourceObservationAdmission.prepare (readContext prepared) profile (readRequest prepared i)
    (operationMarker prepared.authority.snapshot.domain profile.semantics command)
    (readCapability i) (commandCodec.encode command)

/-- A foreign-policy view requires an actual current read capability, a
native signature bound to this exact joint request, and the resource's current
observe policy. A mutation grant or the outer preparation flow is insufficient. -/
structure ReadLeg [DecidableEq F]
    (prepared : PreparedInvocation deployment profile ambient durable command)
    (i : TargetIndex command) (envelope : List UInt8) where
  capabilityPresent : command.targets[i].observeCapability.isSome = true
  selected : ResourceObservationAdmission.Prepared (readContext prepared) profile (readRequest prepared i)
    (operationMarker prepared.authority.snapshot.domain profile.semantics command)
    (readCapability i) (commandCodec.encode command)
  preparedExact : readPreparation prepared i = .ok selected
  checked : ResourceObservationAdmission.Checked selected envelope

def verifyRead [DecidableEq F] (native : CredentialSignatureIO.NativeConfig)
    (prepared : PreparedInvocation deployment profile ambient durable command)
    (i : TargetIndex command) (envelope : List UInt8) :
    IO (Except Reject (ReadLeg prepared i envelope)) := do
  if present : command.targets[i].observeCapability.isSome = true then
    match selected : readPreparation prepared i with
    | .error _ => return .error .observationRejected
    | .ok ready =>
        match ← ResourceObservationAdmission.check native ready envelope with
        | .error _ => return .error .observationRejected
        | .ok checked => return .ok ⟨present, ready, selected, checked⟩
  else return .error .observationRequired

attribute [irreducible] portals

structure CheckedLeg [DecidableEq F]
    (prepared : PreparedInvocation deployment profile ambient durable command)
    (tuple : PreparedTuple (plan prepared)) (incidence : Incidence command) (envelope : List UInt8) where
  receipt : CredentialSignatureAdmission.CheckedSignature prepared.authority.snapshot
  envelopeExact : receipt.envelopeBytes = envelope
  authorization : Authorized (portals prepared tuple incidence)
    prepared.authority.snapshot.authState (tuple.request incidence).2
  authorized : authorizeLeg prepared tuple incidence receipt = .ok authorization

def verifyAndAuthorizeLeg [DecidableEq F] (native : CredentialSignatureIO.NativeConfig)
    (prepared : PreparedInvocation deployment profile ambient durable command)
    (tuple : PreparedTuple (plan prepared)) (incidence : Incidence command) (envelope : List UInt8) :
    IO (Except Reject (CheckedLeg prepared tuple incidence envelope)) := do
  match ← CredentialSignatureAdmission.verifyNative native prepared.authority.snapshot
      (operationMarker prepared.authority.snapshot.domain profile.semantics command)
      (tuple.request incidence).2 envelope with
  | .error reason => return .error (.signature reason)
  | .ok signature =>
      if exactWire : signature.envelopeBytes = envelope then
        match admitted : authorizeLeg prepared tuple incidence signature with
        | .error reason => return .error reason
        | .ok authorization => return .ok ⟨signature, exactWire, authorization, admitted⟩
      else return .error (.signature .sourceBinding)

theorem tuple_source_exact
    (prepared : PreparedInvocation deployment profile ambient durable command)
    (tuple : PreparedTuple (plan prepared)) : tuple.source = ⟨command, rfl⟩ :=
  Subtype.ext tuple.source.property

theorem tuple_post_exact
    (prepared : PreparedInvocation deployment profile ambient durable command)
    (tuple : PreparedTuple (plan prepared)) (incidence : Incidence command) :
    tuple.post incidence = (validated prepared incidence).apply := by
  apply Materialized.ext
  simp only [PreparedTuple.post, ValidatedPatch.apply]
  rw [tuple_source_exact prepared tuple]
  rfl

def admissionEvidence [DecidableEq F]
    (prepared : PreparedInvocation deployment profile ambient durable command)
    (tuple : PreparedTuple (plan prepared))
    (authorizations : ∀ incidence, Authorized (portals prepared tuple incidence)
      prepared.authority.snapshot.authState (tuple.request incidence).2) :
    tuple.AdmissionEvidence (portals prepared tuple) where
  modes incidence := by
    cases incidence with
    | some i => exact (prepared.targets i).candidate.modeEvidence
    | none =>
        change MarkerMode prepared.authority.snapshot profile.semantics tuple.source.val
        rw [tuple.source.property]
        exact prepared.marker
  authorizations := authorizations
  disclosure := fun _ => .sealed
  disclosureAllowed incidence := by cases incidence <;> rfl

/-- A dependent traversal of native verification. Every index must return a
checked receipt before any accepted transaction value is constructed. -/
def collectIO {n : Nat} {E : Type} {P : Fin n → Type}
    (run : (i : Fin n) → IO (Except E (P i))) : IO (Except E ((i : Fin n) → P i)) := do
  let rec loop : (count : Nat) → (bound : count ≤ n) →
      IO (Except E ((i : Fin count) → P ⟨i.val, Nat.lt_of_lt_of_le i.isLt bound⟩))
    | 0, _ => pure (.ok (fun i => nomatch i))
    | count + 1, bound => do
      match ← loop count (Nat.le_trans (Nat.le_succ count) bound) with
      | .error reason => pure (.error reason)
      | .ok previous =>
          let index : Fin n := ⟨count, Nat.lt_of_lt_of_le (Nat.lt_succ_self count) bound⟩
          match ← run index with
          | .error reason => pure (.error reason)
          | .ok current =>
              pure (.ok (fun i => if below : i.val < count then previous ⟨i.val, below⟩
                else by have equal : i.val = count := by omega
                        simpa only [equal] using current))
  loop n (Nat.le_refl n)

structure AcceptedInvocation [DecidableEq F]
    (prepared : PreparedInvocation deployment profile ambient durable command) (signed : SignedCommand) where
  private mk ::
  ingressExact : commandCodec.encode command = signed.commandBytes
  envelopeCount : signed.targetEnvelopes.length = command.targets.length
  observeCount : signed.observeEnvelopes.length =
    (if command.requiresObservation then command.targets.length else 0)
  observations : command.requiresObservation = true → (i : TargetIndex command) →
    ReadLeg prepared i (signed.observeEnvelopes[i.val]?.getD [])
  tuple : PreparedTuple (plan prepared)
  checked : (incidence : Incidence command) → CheckedLeg prepared tuple incidence (signed.envelope command incidence)

def AcceptedInvocation.evidence [DecidableEq F]
    {prepared : PreparedInvocation deployment profile ambient durable command} {signed : SignedCommand}
    (accepted : AcceptedInvocation prepared signed) :
    accepted.tuple.AdmissionEvidence (portals prepared accepted.tuple) :=
  admissionEvidence prepared accepted.tuple fun incidence => (accepted.checked incidence).authorization

theorem AcceptedInvocation.native_ingress_exact [DecidableEq F]
    {prepared : PreparedInvocation deployment profile ambient durable command} {signed : SignedCommand}
    (accepted : AcceptedInvocation prepared signed) (incidence : Incidence command) :
    (accepted.checked incidence).receipt.envelopeBytes = signed.envelope command incidence :=
  (accepted.checked incidence).envelopeExact

def verifyReads [DecidableEq F] (native : CredentialSignatureIO.NativeConfig)
    (prepared : PreparedInvocation deployment profile ambient durable command) (signed : SignedCommand) :
    IO (Except Reject (command.requiresObservation = true → (i : TargetIndex command) →
      ReadLeg prepared i (signed.observeEnvelopes[i.val]?.getD []))) := do
  if needed : command.requiresObservation = true then
    match ← collectIO (fun i : TargetIndex command =>
        verifyRead native prepared i (signed.observeEnvelopes[i.val]?.getD [])) with
    | .error reason => return .error reason
    | .ok checked => return .ok (fun _ => checked)
  else return .ok (fun contradiction => False.elim (needed contradiction))

def admit [DecidableEq F] (native : CredentialSignatureIO.NativeConfig)
    (prepared : PreparedInvocation deployment profile ambient durable command) (signed : SignedCommand) :
    IO (Except Reject (AcceptedInvocation prepared signed)) := do
  if ingress : commandCodec.encode command = signed.commandBytes then
    if count : signed.targetEnvelopes.length = command.targets.length then
      if readCount : signed.observeEnvelopes.length =
          (if command.requiresObservation then command.targets.length else 0) then
        match ← verifyReads native prepared signed with
        | .error reason => return .error reason
        | .ok observations =>
          match prepareTuple prepared with
          | none => return .error .conflictingIncidences
          | some tuple =>
              match ← collectIO (fun i : TargetIndex command =>
                  verifyAndAuthorizeLeg native prepared tuple (some i) (signed.envelope command (some i))) with
              | .error reason => return .error reason
              | .ok targets =>
                  match ← verifyAndAuthorizeLeg native prepared tuple none signed.authorityEnvelope with
                  | .error reason => return .error reason
                  | .ok authority => return .ok ⟨ingress, count, readCount, observations, tuple,
                      fun incidence => match incidence with | some i => targets i | none => authority⟩
      else return .error .wrongEnvelopeCount
    else return .error .wrongEnvelopeCount
  else return .error .malformedCommand

def AcceptedInvocation.apex [DecidableEq F]
    {prepared : PreparedInvocation deployment profile ambient durable command} {signed : SignedCommand}
    (_accepted : AcceptedInvocation prepared signed) : Digest :=
  effectsDigest prepared.authority.snapshot.domain profile.semantics command

def AcceptedInvocation.declaration [DecidableEq F]
    {prepared : PreparedInvocation deployment profile ambient durable command} {signed : SignedCommand}
    (accepted : AcceptedInvocation prepared signed) :=
  accepted.tuple.toDeclaration (portals prepared accepted.tuple) accepted.apex

def AcceptedInvocation.legs [DecidableEq F]
    {prepared : PreparedInvocation deployment profile ambient durable command} {signed : SignedCommand}
    (accepted : AcceptedInvocation prepared signed) : accepted.declaration.AcceptedLegs :=
  accepted.tuple.accept (portals prepared accepted.tuple) accepted.apex accepted.evidence

theorem AcceptedInvocation.post_exact [DecidableEq F]
    {prepared : PreparedInvocation deployment profile ambient durable command} {signed : SignedCommand}
    (accepted : AcceptedInvocation prepared signed) (incidence : Incidence command) :
    accepted.declaration.post accepted.legs incidence = (validated prepared incidence).apply :=
  (accepted.tuple.accepted_posts_exact (portals prepared accepted.tuple)
    accepted.apex accepted.evidence incidence).trans (tuple_post_exact prepared accepted.tuple incidence)

theorem AcceptedInvocation.authority_post_exact [DecidableEq F]
    {prepared : PreparedInvocation deployment profile ambient durable command} {signed : SignedCommand}
    (accepted : AcceptedInvocation prepared signed) :
    accepted.declaration.post accepted.legs none = prepared.physical.post.cell := by
  rw [accepted.post_exact none]
  apply Materialized.ext
  exact prepared.physical.projection_exact.symm

theorem AcceptedInvocation.policy_view_exact [DecidableEq F]
    {prepared : PreparedInvocation deployment profile ambient durable command} {signed : SignedCommand}
    (accepted : AcceptedInvocation prepared signed) (primary : Incidence command) :
    project prepared primary accepted.tuple.source
        (fun incidence => (accepted.declaration.post accepted.legs incidence).logical) =
      project prepared primary accepted.tuple.source accepted.tuple.logicalPost := by
  congr 1
  funext incidence
  exact congrArg Materialized.logical
    (accepted.tuple.accepted_posts_exact (portals prepared accepted.tuple)
      accepted.apex accepted.evidence incidence)

/-! One physical plan and one exact replay identity. -/
def targetWrite (prepared : PreparedInvocation deployment profile ambient durable command)
    (i : TargetIndex command) : DataWrite :=
  ResourceBirthController.Concrete.packedWrite command.targets[i].target (prepared.targets i).before
    (packTarget command.targets[i] (prepared.targets i).candidate.post)

def writes (prepared : PreparedInvocation deployment profile ambient durable command) : List DataWrite :=
  (List.finRange command.targets.length).map (targetWrite prepared) ++ prepared.physical.writes ++
    prepared.physical.placement.auxiliaryCreates.map ResourceBirthController.birthWrite

def sourceGuards (prepared : PreparedInvocation deployment profile ambient durable command) : List ReadGuard :=
  (List.finRange command.targets.length).map fun i =>
    ⟨⟨(prepared.targets i).source.readGuard.1⟩, (prepared.targets i).source.readGuard.2⟩

def readGuards (prepared : PreparedInvocation deployment profile ambient durable command) : List ReadGuard :=
  sourceGuards prepared ++ readonlyGuards prepared.authority.readGuards (writes prepared)

def PhysicalShape (prepared : PreparedInvocation deployment profile ambient durable command) : Prop :=
  ((writes prepared).map DataWrite.cellId).Nodup ∧
    (∀ write ∈ writes prepared, write.expectedPre = durable.snapshot.model.roots write.cellId) ∧
    (∀ write ∈ writes prepared, ResourceBirthController.Concrete.PhysicalPostLaw deployment write) ∧
    (∀ guard ∈ sourceGuards prepared, guard.cellId ∉ (writes prepared).map DataWrite.cellId) ∧
    (∀ guard ∈ readGuards prepared, guard.expectedRoot = durable.snapshot.model.roots guard.cellId)

/- Construct the full target writes once for the five physical-shape clauses.
The ordinary proposition below remains the receiver's authority condition;
this Boolean is only an implementation of its decision procedure. -/
def physicalShapeCheck (prepared : PreparedInvocation deployment profile ambient durable command) : Bool :=
  let ws := writes prepared
  let ids := ws.map DataWrite.cellId
  let source := sourceGuards prepared
  let guards := source ++ readonlyGuards prepared.authority.readGuards ws
  decide ids.Nodup &&
  decide (∀ write ∈ ws, write.expectedPre = durable.snapshot.model.roots write.cellId) &&
  decide (∀ write ∈ ws, ResourceBirthController.Concrete.PhysicalPostLaw deployment write) &&
  decide (∀ guard ∈ source, guard.cellId ∉ ids) &&
  decide (∀ guard ∈ guards, guard.expectedRoot = durable.snapshot.model.roots guard.cellId)

theorem physicalShapeCheck_iff
    (prepared : PreparedInvocation deployment profile ambient durable command) :
    physicalShapeCheck prepared = true ↔ PhysicalShape prepared := by
  simp [physicalShapeCheck, PhysicalShape, readGuards, Bool.and_eq_true]
  tauto

instance physicalShapeDecidable (prepared : PreparedInvocation deployment profile ambient durable command) :
    Decidable (PhysicalShape prepared) :=
  decidable_of_iff (physicalShapeCheck prepared = true)
    (physicalShapeCheck_iff prepared)

theorem writes_roots_bound (prepared : PreparedInvocation deployment profile ambient durable command) :
    ∀ write ∈ writes prepared, ResourceBirthCodec.rootBytes write.canonicalPostBytes = write.exactPost := by
  intro write member
  rcases List.mem_append.mp member with ordinary | allocation
  · rcases List.mem_append.mp ordinary with target | authority
    · obtain ⟨i, _, rfl⟩ := List.mem_map.mp target
      rfl
    · exact CredentialAuthorityDomainReceiver.planWrites_roots_bound
        deployment.authorityAnchor durable.snapshot prepared.authority.snapshot.catalogue
        prepared.marker.prepared.postPages prepared.physical.placement write authority
  · obtain ⟨creation, _, rfl⟩ := List.mem_map.mp allocation
    exact ResourceBirthController.birthWrite_root_bound creation

theorem readGuards_readonly (prepared : PreparedInvocation deployment profile ambient durable command)
    (shape : PhysicalShape prepared) :
    ∀ guard ∈ readGuards prepared, guard.cellId ∉ (writes prepared).map DataWrite.cellId := by
  intro guard member
  rcases List.mem_append.mp member with source | authority
  · exact shape.2.2.2.1 guard source
  · exact of_decide_eq_true (List.mem_filter.mp authority).2

def signedIngressFrame : List UInt8 := "DREGG/RESOURCE/SIGNED-INGRESS".toUTF8.toList ++ [3]
abbrev SignedIngress := Digest × Digest × SignedCommand

def signedIngressStream : StreamCodec SignedIngress :=
  StreamCodec.xmap
    (StreamCodec.product digestStream (StreamCodec.product digestStream
      (StreamCodec.product bytesStream (StreamCodec.product (StreamCodec.list bytesStream)
        (StreamCodec.product (StreamCodec.list bytesStream) bytesStream)))))
    (fun (domain, semantics, signed) =>
      (domain, semantics, signed.commandBytes, signed.targetEnvelopes, signed.observeEnvelopes, signed.authorityEnvelope))
    (fun (domain, semantics, command, targets, observe, authority) =>
      (domain, semantics, ⟨command, targets, observe, authority⟩))
    (by rintro ⟨domain, semantics, signed⟩; cases signed; rfl)

def signedIngressRawCodec : LawfulCodec SignedIngress where
  encode ingress := signedIngressFrame ++ signedIngressStream.encode ingress
  decode bytes := if bytes.take signedIngressFrame.length = signedIngressFrame then
    signedIngressStream.toLawful.decode (bytes.drop signedIngressFrame.length) else none
  decode_encode := by
    intro ingress
    have exact := signedIngressStream.toLawful.decode_encode ingress
    change signedIngressStream.toLawful.decode (signedIngressStream.encode ingress) = some ingress at exact
    simp [exact]

def signedIngressCodec : LawfulCodec SignedIngress := ResourceBirthCodec.strictCodec signedIngressRawCodec

def signedBytes (domain semantics : Digest) (signed : SignedCommand) : List UInt8 :=
  signedIngressCodec.encode (domain, semantics, signed)
abbrev decodeSignedBytes := signedIngressCodec.decode

theorem decodeSignedBytes_encode (domain semantics : Digest) (signed : SignedCommand) :
    decodeSignedBytes (signedBytes domain semantics signed) = some (domain, semantics, signed) :=
  signedIngressCodec.decode_encode _
theorem decodeSignedBytes_canonical {bytes : List UInt8} {ingress : SignedIngress}
    (decoded : decodeSignedBytes bytes = some ingress) : signedBytes ingress.1 ingress.2.1 ingress.2.2 = bytes :=
  ResourceBirthCodec.strictCodec_canonical signedIngressRawCodec decoded

abbrev invocationNullifier := CredentialAuthorityReplay.nullifier

def invocationEvent (domain semantics : Digest) (command : Command) (signed : SignedCommand) : StableEvent where
  codecVersion := 3
  domain := domain
  eventId := effectsDigest domain semantics command
  canonicalBytes := signedBytes domain semantics signed

def transactionId (domain semantics : Digest) (command : Command) : Digest :=
  ⟨operationMarker domain semantics command⟩

def sourceChargeFrom (prepared : PreparedInvocation deployment profile ambient durable command)
    (signed : SignedCommand) (ws : List DataWrite) (guards : List ReadGuard) :
    ResourceCost.Charge
  | .incidences => command.targets.length + 1
  | .turnBytes => (signedBytes prepared.authority.snapshot.domain profile.semantics signed).length
  | .memoryTouches => ws.length + guards.length
  | .storageBytes => (ws.map fun write => write.canonicalPostBytes.length).sum
  | .feeDebit | .witnessBytes | .proofWork | .networkBytes | .sideEffectCount | .leaseByteBlocks => 0

def sourceCharge (prepared : PreparedInvocation deployment profile ambient durable command)
    (signed : SignedCommand) : ResourceCost.Charge :=
  sourceChargeFrom prepared signed (writes prepared) (readGuards prepared)

def AcceptedInvocation.dataIntent [DecidableEq F]
    {prepared : PreparedInvocation deployment profile ambient durable command} {signed : SignedCommand}
    (_accepted : AcceptedInvocation prepared signed) (shape : PhysicalShape prepared) :
    DataIntent ResourceBirthCodec.rootBytes :=
  let ws := writes prepared
  let guards := sourceGuards prepared ++ readonlyGuards prepared.authority.readGuards ws
  { transactionId := transactionId prepared.authority.snapshot.domain profile.semantics command
    writes := ws
    readGuards := guards
    nullifiers := [invocationNullifier prepared.authority.snapshot.domain
      (operationMarker prepared.authority.snapshot.domain profile.semantics command)]
    exactCharge := sourceChargeFrom prepared signed ws guards
    event := invocationEvent prepared.authority.snapshot.domain profile.semantics command signed
    postRootsBound := writes_roots_bound prepared
    guardsReadOnly := readGuards_readonly prepared shape }

theorem AcceptedInvocation.dataIntent_exact_charge [DecidableEq F]
    {prepared : PreparedInvocation deployment profile ambient durable command} {signed : SignedCommand}
    (accepted : AcceptedInvocation prepared signed) (shape : PhysicalShape prepared) :
    (accepted.dataIntent shape).exactCharge = sourceCharge prepared signed := by
  rfl

/-- Sharing the runtime write and guard values leaves the complete original
receiver intent, including every write, charge, event and proof field, exact. -/
theorem AcceptedInvocation.dataIntent_original_exact [DecidableEq F]
    {prepared : PreparedInvocation deployment profile ambient durable command} {signed : SignedCommand}
    (accepted : AcceptedInvocation prepared signed) (shape : PhysicalShape prepared) :
    accepted.dataIntent shape =
      { transactionId := transactionId prepared.authority.snapshot.domain profile.semantics command
        writes := writes prepared
        readGuards := readGuards prepared
        nullifiers := [invocationNullifier prepared.authority.snapshot.domain
          (operationMarker prepared.authority.snapshot.domain profile.semantics command)]
        exactCharge := sourceCharge prepared signed
        event := invocationEvent prepared.authority.snapshot.domain profile.semantics command signed
        postRootsBound := writes_roots_bound prepared
        guardsReadOnly := readGuards_readonly prepared shape } := by
  rfl

def recordedInvocation (domain semantics : Digest) (command : Command) (signed : SignedCommand)
    (durable : Durable) : Except Unit (Option (DurableCommitProtocol.Intent Digest Digest StableNullifier ReplayEnvelope)) :=
  match DurableCommitProtocol.Snapshot.lookupRecorded (transactionId domain semantics command)
      durable.snapshot.model.journal with
  | none => .ok none
  | some recorded =>
      if recorded.transactionId = transactionId domain semantics command ∧
          recorded.event.event = invocationEvent domain semantics command signed ∧
          recorded.nullifiers = [invocationNullifier domain (operationMarker domain semantics command)] then
        .ok (some recorded)
      else .error ()

inductive ReceiveResult where
  | replayed (recorded : DurableCommitProtocol.Intent Digest Digest StableNullifier ReplayEnvelope)
  | rejected (reason : Reject)
  | transactionConflict
  | unavailable (detail : String)
  | settlement (result : DurableReceiverIO.Result ResourceBirthCodec.rootBytes)

def receiveLoaded {F : Type} [Field F] [DecidableEq F]
    (deployment : Deployment) (profile : CanonicalRuntimeProfile.Profile F)
    (ambient : Ambient) (native : CredentialSignatureIO.NativeConfig)
    (transport : DurableReceiverIO.Transport) (durable : Durable) (signed : SignedCommand) : IO ReceiveResult := do
  match commandCodec.decode signed.commandBytes with
  | none => return .rejected .malformedCommand
  | some command =>
      match recordedInvocation deployment.domain profile.semantics command signed durable with
      | .error _ => return .transactionConflict
      | .ok (some recorded) => return .replayed recorded
      | .ok none =>
          match prepare deployment profile ambient durable command with
          | .error reason => return .rejected reason
          | .ok prepared =>
              if shape : PhysicalShape prepared then
                match ← admit native prepared signed with
                | .error reason => return .rejected reason
                | .ok accepted => return .settlement (← DurableReceiverIO.receiveLoaded transport ResourceBirthCodec.rootBytes
                    durable (accepted.dataIntent shape))
              else return .rejected .physicalPreparation

def receive {F : Type} [Field F] [DecidableEq F]
    (deployment : Deployment) (profile : CanonicalRuntimeProfile.Profile F)
    (ambient : Ambient) (native : CredentialSignatureIO.NativeConfig)
    (transport : DurableReceiverIO.Transport) (signed : SignedCommand) (_attempts : Nat := 3) : IO ReceiveResult := do
  match ← DurableReceiverIO.load transport ResourceBirthCodec.rootBytes with
  | .error detail => return .unavailable detail
  | .ok durable => receiveLoaded deployment profile ambient native transport durable signed

end Minidregg.Kernel.DeclaredResourceController
