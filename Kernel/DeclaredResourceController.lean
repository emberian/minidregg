/- The sole signed resource invocation receiver. A one-target transaction is
an ordinary finite transaction, not a separate admission or persistence path.
Every target and the authority read incidence form one actual MultiCellHyperedge
PreparedTuple; all signatures and current policies precede its single CAS.  The
shared replay marker is the intent's durable nullifier. -/
import Kernel.ResourceTransaction
import Kernel.ResourceObservationAdmission
import Compiler.ResourceAuthorityProjection
import Kernel.JointSlots

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
open Minidregg.Theory.Store
open Minidregg.Theory.TypedAuthorization
set_option autoImplicit false
set_option maxHeartbeats 800000

abbrev Source (command : Command) := { actual : Command // actual = command }
variable {F : Type} [Field F] {deployment : Deployment}
  {profile : CanonicalRuntimeProfile.Profile F} {ambient : Ambient}
  {durable : Durable} {command : Command}

def layout (prepared : PreparedInvocation deployment profile ambient durable command) :
    CellLayout (Incidence command) where
  storeLayout | some i => command.targets[i].layout | none => CredentialAuthorityState.layout
  materializer | some i => command.targets[i].materializer | none => CredentialAuthorityCell.materializer
  projectAuthority := fun _ _ => prepared.authority.snapshot.authState
  cellId | some i => ⟨command.targets[i].target⟩ | none => CredentialAuthorityDomainReceiver.cellIdOf deployment

def rawLeg (prepared : PreparedInvocation deployment profile ambient durable command)
    (source : Source command) : (incidence : Incidence command) → CandidateLegData (layout prepared) incidence
  | some i =>
      { pre := (prepared.targets i).pre
        patch := targetPatch prepared.authority.snapshot profile.semantics ambient command command.targets[i]
          (prepared.targets i).pre
        request := ⟨command.targets[i].kind, requestFor prepared.authority.snapshot profile.semantics
          ambient command command.targets[i] (prepared.targets i).pre.root⟩
        Postcondition := fun logical =>
          (targetPatch prepared.authority.snapshot profile.semantics ambient command command.targets[i]
            (prepared.targets i).pre).ResultAt
            (prepared.targets i).pre.logical logical }
  | none =>
      { pre := prepared.authority.snapshot.cell
        patch := authorityReadPatch
        request := ⟨source.val.first.kind, request prepared.authority.snapshot profile.semantics
          ambient source.val prepared.authority.snapshot.cell.root⟩
        Postcondition := fun logical =>
          authorityReadPatch.ResultAt prepared.authority.snapshot.logical logical }

def bindFamily (prepared : PreparedInvocation deployment profile ambient durable command)
    (source : Source command) (_portals : Incidence command → Portal) :
    (incidence : Incidence command) → SemanticLegBinding.{0,0,0,0,0} (rawLeg prepared source incidence)
  | some i =>
      { Nullifier := Nat
        family := by
          change SemanticEffectFamily command.targets[i].layout command.targets[i].materializer Nat
          exact targetFamily deployment prepared.authority.snapshot profile.semantics ambient command
            command.targets[i] (prepared.targets i).pre
        declaration := ()
        outcome := (prepared.targets i).post
        preExact := rfl
        requestExact := rfl
        effectsExact := by simp only [rawLeg, targetFamily, requestFor_eq_reference,
          requestForReference, id_eq]
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
    PreparationPlan.{0,0,0,0,0} (layout prepared) (Source command) where
  leg := rawLeg prepared
  jointDigest := fun source => effectsDigest prepared.authority.snapshot.domain profile.semantics source.val
  legEffectsDigest := fun source _ => effectsDigest prepared.authority.snapshot.domain profile.semantics source.val
  bindFamily := bindFamily prepared

theorem validated (prepared : PreparedInvocation deployment profile ambient durable command) :
    (incidence : Incidence command) → ValidatedPatch ((layout prepared).materializer incidence)
      (rawLeg prepared ⟨command, rfl⟩ incidence).pre
      (rawLeg prepared ⟨command, rfl⟩ incidence).request.2.preStateRoot
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
        requestEffects := by intro incidence; cases incidence <;> rfl }
  else none

abbrev bytesSlots := ResourceAuthorityProjection.bytesSlots

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

/-- The controller's run slots (the reserved `run/` namespace): the checked
program's `ranSlot` (read by `Pred.ran`), the evaluator it ran on (`evaluatorSlot`,
which a law may pin), the oracle's step count and the ABI fuel. Absent unless the
command's claim was re-executed and accepted. -/
def runSlots : Option CheckedRun → List (String × Int)
  | none => []
  | some checked =>
      [(Minidregg.Pred.ranSlot checked.claim.programId.value, 1),
       (Minidregg.Pred.evaluatorSlot checked.evaluator.value, 1),
       ("run/steps", Int.ofNat checked.verdict.steps),
       ("run/fuel", Int.ofNat checked.fuel)]

/- These slots depend on the admitted tuple and incidence, but not on which
old/new logical state the policy examines. Derive them here once per step;
the caller cannot inject an independent request or command projection. -/
def projectCommonSlots (prepared : PreparedInvocation deployment profile ambient durable command)
    (primary : Incidence command) (source : Source command) : List (String × Int) :=
  let selected := incidenceTarget command primary
  let preRoot := match primary with
    | some i => (prepared.targets i).pre.root
    | none => prepared.authority.snapshot.cell.root
  Kernel.ClockCell.slots prepared.clock.clock ++
  CanonicalRuntimeProfile.requestSlots
      (requestFor prepared.authority.snapshot profile.semantics ambient command selected preRoot) ++
    bytesSlots "command/bytes" 0 (commandCodec.encode source.val) ++
    runSlots prepared.run

/-- Participant `i`'s own slots: exactly what a law on `i` reads locally. -/
def participantSlots (prepared : PreparedInvocation deployment profile ambient durable command)
    (logical : (incidence : Incidence command) → Store ((layout prepared).storeLayout incidence))
    (i : TargetIndex command) : List (String × Int) :=
  bytesSlots "resource/bytes" 0 (command.targets[i].materializer.codec.encode (logical (some i))) ++
    targetProjection command.targets[i] (prepared.targets i).pre.logical (logical (some i))

/-- Local names for the primary participant, then every participant under
`joint/target/{id}/…` and again under `joint/index/{i}/…` (`jointSlots`). -/
def projectWithCommon (prepared : PreparedInvocation deployment profile ambient durable command)
    (primary : Incidence command) (common : List (String × Int))
    (logical : (incidence : Incidence command) → Store ((layout prepared).storeLayout incidence)) :
    Minidregg.Pred.State :=
  let localIndex := primary.getD (firstIndex prepared)
  ⟨common ++ participantSlots prepared logical localIndex ++
    jointSlots command.targets (participantSlots prepared logical)⟩

def project (prepared : PreparedInvocation deployment profile ambient durable command)
    (primary : Incidence command) (source : Source command)
    (logical : (incidence : Incidence command) → Store ((layout prepared).storeLayout incidence)) :
    Minidregg.Pred.State :=
  projectWithCommon prepared primary (projectCommonSlots prepared primary source) logical

theorem projectWithCommon_exact (prepared : PreparedInvocation deployment profile ambient durable command)
    (primary : Incidence command) (source : Source command)
    (logical : (incidence : Incidence command) → Store ((layout prepared).storeLayout incidence)) :
    projectWithCommon prepared primary (projectCommonSlots prepared primary source) logical =
      project prepared primary source logical := rfl

section JointIndex
open JointSlots

/-- A stream append's slots (`request/topic…`, `stream/sequence`, `request/to`,
`request/ref/…`) are not joint keys. -/
theorem streamSlots_unjoint (request : StreamCell.Append) (before : Store StreamCell.layout) :
    Unjoint (streamSlots request before) := by
  unfold streamSlots
  refine unjoint_append _ _ (unjoint_append _ _ (unjoint_append _ _ ?_
    (bytesSlots_unjoint "request/topic" 'r' (by decide) (by decide) _ _)) ?_) ?_
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl <;> dsimp only <;> decide
  · intro p hp
    cases h : request.recipient with
    | none => simp [h] at hp
    | some subject =>
        simp only [h, List.mem_cons, List.not_mem_nil, or_false] at hp
        subst hp; dsimp only; decide
  · intro p hp
    cases h : request.ref with
    | none => simp [h] at hp
    | some pair =>
        obtain ⟨cell, sequence⟩ := pair
        simp only [h, List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl <;> dsimp only <;> decide

theorem targetProjection_unjoint (target : Target) (before after : Store target.layout) :
    Unjoint (targetProjection target before after) := by
  cases target with
  | mk kind id capability version root payload observe =>
    cases payload with
    | scalar _ => exact scalarSlots_unjoint _ _
    | content content => exact contentProject_unjoint _ _ _
    | append request => exact streamSlots_unjoint _ _

/-- A checked run's slots (`run/program/{id}`, `run/evaluator/{id}`, `run/steps`,
`run/fuel`) are not joint keys. -/
theorem runSlots_unjoint (run : Option CheckedRun) : Unjoint (runSlots run) := by
  intro p hp
  cases run with
  | none => simp [runSlots] at hp
  | some checked =>
      simp only [runSlots, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl
      · simp [Minidregg.Pred.ranSlot, String.toList_append]
      · simp [Minidregg.Pred.evaluatorSlot, String.toList_append]
      · dsimp only; decide
      · dsimp only; decide

theorem participantSlots_unjoint (prepared : PreparedInvocation deployment profile ambient durable command)
    (logical : (incidence : Incidence command) → Store ((layout prepared).storeLayout incidence))
    (i : TargetIndex command) : Unjoint (participantSlots prepared logical i) :=
  unjoint_append _ _ (bytesSlots_unjoint "resource/bytes" 'r' (by decide) (by decide) _ _)
    (targetProjection_unjoint _ _ _)

/-- The clock's common slots (`clock/now`, `clock/day`, `clock/slot`) are not joint keys. -/
theorem clockSlots_unjoint (clock : Kernel.ClockCell.Clock) : Unjoint (Kernel.ClockCell.slots clock) := by
  intro p hp
  simp only [Kernel.ClockCell.slots, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl <;> dsimp only <;> decide

theorem projectCommonSlots_unjoint (prepared : PreparedInvocation deployment profile ambient durable command)
    (primary : Incidence command) (source : Source command) :
    Unjoint (projectCommonSlots prepared primary source) :=
  unjoint_append _ _
    (unjoint_append _ _
      (unjoint_append _ _ (clockSlots_unjoint _) (requestSlots_unjoint _))
      (bytesSlots_unjoint "command/bytes" 'c' (by decide) (by decide) _ _))
    (runSlots_unjoint _)

/-- Every joint key is read from the joint block: nothing local or common can shadow it. -/
theorem project_joint_get (prepared : PreparedInvocation deployment profile ambient durable command)
    (primary : Incidence command) (source : Source command)
    (logical : (incidence : Incidence command) → Store ((layout prepared).storeLayout incidence))
    (k : String) (hk : k.toList.head? = some 'j') :
    (project prepared primary source logical).get k =
      Minidregg.Pred.State.get ⟨jointSlots command.targets (participantSlots prepared logical)⟩ k := by
  unfold project projectWithCommon
  rw [get_append, get_unjoint _ (unjoint_append _ _ (projectCommonSlots_unjoint prepared primary source)
    (participantSlots_unjoint prepared logical _)) k hk, Option.none_or]

/-- Position `i` of the command reads participant `i`'s own slots. -/
theorem joint_index_exact (prepared : PreparedInvocation deployment profile ambient durable command)
    (primary : Incidence command) (source : Source command)
    (logical : (incidence : Incidence command) → Store ((layout prepared).storeLayout incidence))
    (i : TargetIndex command) (slot : String) :
    (project prepared primary source logical).get (jointIndexKey i.val slot) =
      Minidregg.Pred.State.get ⟨participantSlots prepared logical i⟩ slot := by
  rw [project_joint_get _ _ _ _ _ (jointIndexKey_head _ _), jointSlots_index]

/-- The id key names the same participant, since a prepared command's target ids are distinct. -/
theorem joint_target_exact (prepared : PreparedInvocation deployment profile ambient durable command)
    (primary : Incidence command) (source : Source command)
    (logical : (incidence : Incidence command) → Store ((layout prepared).storeLayout incidence))
    (i : TargetIndex command) (slot : String) :
    (project prepared primary source logical).get (jointTargetKey command.targets[i].target slot) =
      Minidregg.Pred.State.get ⟨participantSlots prepared logical i⟩ slot := by
  rw [project_joint_get _ _ _ _ _ (jointTargetKey_head _ _), jointSlots_target _ _ prepared.distinct]

/-- The two keyings agree: `joint/index/{i}/s` and `joint/target/{id of target i}/s`
read the same value (or are both absent) for every slot name `s`. -/
theorem joint_index_of_target (prepared : PreparedInvocation deployment profile ambient durable command)
    (primary : Incidence command) (source : Source command)
    (logical : (incidence : Incidence command) → Store ((layout prepared).storeLayout incidence))
    (i : Nat) (t : Target) (h : command.targets[i]? = some t) (slot : String) :
    (project prepared primary source logical).get (jointIndexKey i slot) =
      (project prepared primary source logical).get (jointTargetKey t.target slot) := by
  obtain ⟨lt, rfl⟩ := List.getElem?_eq_some_iff.mp h
  exact (joint_index_exact prepared primary source logical ⟨i, lt⟩ slot).trans
    (joint_target_exact prepared primary source logical ⟨i, lt⟩ slot).symm

/-- A position the command does not have names nothing: every Pred atom is
false on it (fail-closed), so a law asserting a fact about that position
refuses the command. (A `not` around such an atom is true.) -/
theorem joint_index_absent (prepared : PreparedInvocation deployment profile ambient durable command)
    (primary : Incidence command) (source : Source command)
    (logical : (incidence : Incidence command) → Store ((layout prepared).storeLayout incidence))
    (n : Nat) (h : command.targets.length ≤ n) (slot : String) :
    (project prepared primary source logical).get (jointIndexKey n slot) = none := by
  rw [project_joint_get _ _ _ _ _ (jointIndexKey_head _ _), jointSlots_index_absent _ _ n h]

/-- info: 'Minidregg.Kernel.DeclaredResourceController.targetProjection_unjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms targetProjection_unjoint
/-- info: 'Minidregg.Kernel.DeclaredResourceController.participantSlots_unjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms participantSlots_unjoint
/-- info: 'Minidregg.Kernel.DeclaredResourceController.clockSlots_unjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms clockSlots_unjoint
/-- info: 'Minidregg.Kernel.DeclaredResourceController.projectCommonSlots_unjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms projectCommonSlots_unjoint
/-- info: 'Minidregg.Kernel.DeclaredResourceController.project_joint_get' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms project_joint_get
/-- info: 'Minidregg.Kernel.DeclaredResourceController.joint_index_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms joint_index_exact
/-- info: 'Minidregg.Kernel.DeclaredResourceController.joint_target_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms joint_target_exact
/-- info: 'Minidregg.Kernel.DeclaredResourceController.joint_index_of_target' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms joint_index_of_target
/-- info: 'Minidregg.Kernel.DeclaredResourceController.joint_index_absent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms joint_index_absent

end JointIndex
/-- **`now_slot_exact`.**  Every law judging a resource invocation reads
`clock/now` as exactly the `now` of the clock cell held by the snapshot the
record is prepared from (and guarded against, `domainGuards`). -/
theorem now_slot_exact (prepared : PreparedInvocation deployment profile ambient durable command)
    (primary : Incidence command) (source : Source command)
    (logical : (incidence : Incidence command) → Store ((layout prepared).storeLayout incidence)) :
    (project prepared primary source logical).get "clock/now" =
        some (Int.ofNat prepared.clock.clock.now) ∧
      Kernel.ClockCell.clockOf prepared.clock.cell.logical = some prepared.clock.clock := by
  refine ⟨?_, prepared.clock.clockExact⟩
  simp [project, projectWithCommon, projectCommonSlots, Kernel.ClockCell.slots,
    Minidregg.Pred.State.get]

/-- info: 'Minidregg.Kernel.DeclaredResourceController.now_slot_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms now_slot_exact

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
    (incidence : Incidence command) → Store ((layout prepared).storeLayout incidence) :=
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
  let config := policyConfig prepared tuple incidence
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

/-- The failing clause of this leg's committed law, read on exactly the witness
`authorizeLeg` hands to `CanonicalPolicyAdmission.admit`: the same resolved law,
the same projected old and new states. It decides nothing; the Host uses it to
name the clause when it refuses to plan a write its law rejects. -/
def lawLeaf [DecidableEq F]
    (prepared : PreparedInvocation deployment profile ambient durable command)
    (tuple : PreparedTuple (plan prepared)) (incidence : Incidence command) : Option LawLeaf := do
  let wanted := (tuple.request incidence).2
  let context := step prepared tuple incidence
  let committed ← (policyConfig prepared tuple incidence).registry.resolve wanted.policyId wanted.policyRevision
  let witness := canonicalWitness (F := F) profile.compilerProfile.compiler committed
    context.oldState context.newState
  LawLeaf.of committed.record.predicate witness.oldState witness.newState

/-- A named clause is a leaf of the leg's resolved committed law, at its path,
and it is false on the witness states `authorizeLeg` evaluates that law on. -/
theorem lawLeaf_fails [DecidableEq F]
    (prepared : PreparedInvocation deployment profile ambient durable command)
    (tuple : PreparedTuple (plan prepared)) (incidence : Incidence command) (leaf : LawLeaf)
    (named : lawLeaf prepared tuple incidence = some leaf) :
    ∃ committed, (policyConfig prepared tuple incidence).registry.resolve
        (tuple.request incidence).2.policyId (tuple.request incidence).2.policyRevision = some committed ∧
      committed.record.predicate.subterm leaf.path = some leaf.clause ∧
      Minidregg.Pred.eval leaf.clause
        (canonicalWitness (F := F) profile.compilerProfile.compiler committed
          (step prepared tuple incidence).oldState (step prepared tuple incidence).newState).oldState
        (canonicalWitness (F := F) profile.compilerProfile.compiler committed
          (step prepared tuple incidence).oldState (step prepared tuple incidence).newState).newState = false := by
  unfold lawLeaf at named
  cases resolved : (policyConfig prepared tuple incidence).registry.resolve
      (tuple.request incidence).2.policyId (tuple.request incidence).2.policyRevision with
  | none => simp [resolved] at named
  | some committed =>
      simp only [resolved, Option.bind_eq_bind, Option.bind_some] at named
      obtain ⟨at_, _, fails⟩ := LawLeaf.of_fails _ _ _ leaf named
      exact ⟨committed, rfl, at_, fails⟩

/-- **One evaluation, two call sites.** The Host's prepare-time refusal
(`lawLeaf`, run before it plans a write) and the submission verdict (the
compiled check `config.verifies` inside `CanonicalPolicyAdmission.admit`, which
`authorizeLeg` reaches) read the same resolved committed law on the same
canonical witness. Under the binding facts a resolved leg carries (exactly the
premises of `canonical_verifies_iff_eval`), prepare names no clause exactly
when submission's compiled check accepts. -/
theorem lawLeaf_none_iff_verifies [DecidableEq F]
    (prepared : PreparedInvocation deployment profile ambient durable command)
    (tuple : PreparedTuple (plan prepared)) (incidence : Incidence command)
    {committed : CommittedPolicy}
    (resolved : (policyConfig prepared tuple incidence).registry.resolve
      (tuple.request incidence).2.policyId (tuple.request incidence).2.policyRevision = some committed)
    (policyIdExact : committed.record.policyId = (tuple.request incidence).2.policyId)
    (versionExact : committed.record.version = (tuple.request incidence).2.policyRevision)
    (domainExact : committed.record.domain = (tuple.request incidence).2.domain)
    (semanticsExact : committed.record.semantics = (tuple.request incidence).2.semantics)
    (recordDigestExact :
      (policyConfig prepared tuple incidence).recordDigest committed.record = committed.address)
    (stepExact : (policyConfig prepared tuple incidence).stepBinding.matches
      (tuple.request incidence).2 (step prepared tuple incidence).oldState
      (step prepared tuple incidence).newState = true)
    (profileCompatible : (policyConfig prepared tuple incidence).compilerProfile.compatible
      (policyConfig prepared tuple incidence).stepBinding = true)
    (profileSemanticsExact :
      (tuple.request incidence).2.semantics = profile.compilerProfile.semantics)
    (supportedExact : supported profile.compilerProfile.compiler committed.record.predicate = true)
    (rangesExact : inputsInRange profile.compilerProfile.compiler committed.record.predicate
      (step prepared tuple incidence).oldState (step prepared tuple incidence).newState = true)
    (castExact : castInjOn F (intsOf committed.record.predicate
      (step prepared tuple incidence).oldState (step prepared tuple incidence).newState)) :
    lawLeaf prepared tuple incidence = none ↔
      (policyConfig prepared tuple incidence).verifies (tuple.request incidence).2
        (canonicalWitness profile.compilerProfile.compiler committed
          (step prepared tuple incidence).oldState (step prepared tuple incidence).newState) = true := by
  have verdict := canonical_verifies_iff_eval (config := policyConfig prepared tuple incidence)
    resolved policyIdExact versionExact domainExact semanticsExact recordDigestExact stepExact
    profileCompatible profileSemanticsExact supportedExact rangesExact castExact
  refine Iff.trans ?_ verdict.symm
  unfold lawLeaf
  simp only [resolved, Option.bind_eq_bind, Option.bind_some]
  exact LawLeaf.of_none_iff _ _ _

/-- The same fact from the refusing side: on a resolved, bound leg the Host
refuses to plan the write (names a clause) exactly when the submission's
compiled policy check rejects the same witness, so `admit` returns `none` and
`authorizeLeg` answers `policyRejected`. -/
theorem lawLeaf_refuses_iff_verifies_rejects [DecidableEq F]
    (prepared : PreparedInvocation deployment profile ambient durable command)
    (tuple : PreparedTuple (plan prepared)) (incidence : Incidence command)
    {committed : CommittedPolicy}
    (resolved : (policyConfig prepared tuple incidence).registry.resolve
      (tuple.request incidence).2.policyId (tuple.request incidence).2.policyRevision = some committed)
    (policyIdExact : committed.record.policyId = (tuple.request incidence).2.policyId)
    (versionExact : committed.record.version = (tuple.request incidence).2.policyRevision)
    (domainExact : committed.record.domain = (tuple.request incidence).2.domain)
    (semanticsExact : committed.record.semantics = (tuple.request incidence).2.semantics)
    (recordDigestExact :
      (policyConfig prepared tuple incidence).recordDigest committed.record = committed.address)
    (stepExact : (policyConfig prepared tuple incidence).stepBinding.matches
      (tuple.request incidence).2 (step prepared tuple incidence).oldState
      (step prepared tuple incidence).newState = true)
    (profileCompatible : (policyConfig prepared tuple incidence).compilerProfile.compatible
      (policyConfig prepared tuple incidence).stepBinding = true)
    (profileSemanticsExact :
      (tuple.request incidence).2.semantics = profile.compilerProfile.semantics)
    (supportedExact : supported profile.compilerProfile.compiler committed.record.predicate = true)
    (rangesExact : inputsInRange profile.compilerProfile.compiler committed.record.predicate
      (step prepared tuple incidence).oldState (step prepared tuple incidence).newState = true)
    (castExact : castInjOn F (intsOf committed.record.predicate
      (step prepared tuple incidence).oldState (step prepared tuple incidence).newState)) :
    (lawLeaf prepared tuple incidence).isSome = true ↔
      (policyConfig prepared tuple incidence).verifies (tuple.request incidence).2
        (canonicalWitness profile.compilerProfile.compiler committed
          (step prepared tuple incidence).oldState (step prepared tuple incidence).newState) = false := by
  have same := lawLeaf_none_iff_verifies prepared tuple incidence resolved policyIdExact
    versionExact domainExact semanticsExact recordDigestExact stepExact profileCompatible
    profileSemanticsExact supportedExact rangesExact castExact
  cases named : lawLeaf prepared tuple incidence <;>
    cases verdict : (policyConfig prepared tuple incidence).verifies (tuple.request incidence).2
      (canonicalWitness profile.compilerProfile.compiler committed
        (step prepared tuple incidence).oldState (step prepared tuple incidence).newState) <;>
    simp_all

/-- The out-of-range order clause of this leg's committed law, read on exactly the
witness `authorizeLeg` range-checks before it refuses with `policyInputRange`. It
decides nothing; the Host uses it to name the clause and its two values. -/
def rangeLeaf [DecidableEq F]
    (prepared : PreparedInvocation deployment profile ambient durable command)
    (tuple : PreparedTuple (plan prepared)) (incidence : Incidence command) : Option LawLeaf := do
  let wanted := (tuple.request incidence).2
  let context := step prepared tuple incidence
  let committed ← (policyConfig prepared tuple incidence).registry.resolve wanted.policyId wanted.policyRevision
  let witness := canonicalWitness (F := F) profile.compilerProfile.compiler committed
    context.oldState context.newState
  LawLeaf.ofRange profile.compilerProfile.compiler committed.record.predicate
    witness.oldState witness.newState

/-- The leg names an out-of-range clause exactly when `authorizeLeg`'s range check
on its resolved law fails: the named refusal and `policyInputRange` agree. -/
theorem rangeLeaf_none_iff_inputsInRange [DecidableEq F]
    (prepared : PreparedInvocation deployment profile ambient durable command)
    (tuple : PreparedTuple (plan prepared)) (incidence : Incidence command)
    {committed : CommittedPolicy}
    (resolved : (policyConfig prepared tuple incidence).registry.resolve
      (tuple.request incidence).2.policyId (tuple.request incidence).2.policyRevision = some committed) :
    rangeLeaf prepared tuple incidence = none ↔
      inputsInRange profile.compilerProfile.compiler committed.record.predicate
        (step prepared tuple incidence).oldState (step prepared tuple incidence).newState = true := by
  unfold rangeLeaf
  simp only [resolved, Option.bind_eq_bind, Option.bind_some, canonicalWitness]
  exact LawLeaf.ofRange_none_iff _ _ _ _

/-- Two integers of this leg's step with one field image, read on exactly the
integers `authorizeLeg`'s cast check covers before it refuses with
`policyCastAlias`. -/
def castAliasLeg [DecidableEq F]
    (prepared : PreparedInvocation deployment profile ambient durable command)
    (tuple : PreparedTuple (plan prepared)) (incidence : Incidence command) : Option (Int × Int) := do
  let wanted := (tuple.request incidence).2
  let context := step prepared tuple incidence
  let committed ← (policyConfig prepared tuple incidence).registry.resolve wanted.policyId wanted.policyRevision
  let witness := canonicalWitness (F := F) profile.compilerProfile.compiler committed
    context.oldState context.newState
  castAlias F (intsOf committed.record.predicate witness.oldState witness.newState)

/-- The leg names a pair exactly when `authorizeLeg`'s cast check on its resolved law fails. -/
theorem castAliasLeg_none_iff_castInjOn [DecidableEq F]
    (prepared : PreparedInvocation deployment profile ambient durable command)
    (tuple : PreparedTuple (plan prepared)) (incidence : Incidence command)
    {committed : CommittedPolicy}
    (resolved : (policyConfig prepared tuple incidence).registry.resolve
      (tuple.request incidence).2.policyId (tuple.request incidence).2.policyRevision = some committed) :
    castAliasLeg prepared tuple incidence = none ↔
      castInjOn F (intsOf committed.record.predicate
        (step prepared tuple incidence).oldState (step prepared tuple incidence).newState) := by
  unfold castAliasLeg
  simp only [resolved, Option.bind_eq_bind, Option.bind_some, canonicalWitness]
  exact castAlias_none_iff F _

/-- The first leg whose step carries two integers with one field image. -/
def firstCastAlias [DecidableEq F]
    (prepared : PreparedInvocation deployment profile ambient durable command)
    (tuple : PreparedTuple (plan prepared)) : Option (Int × Int) :=
  ((List.finRange command.targets.length).map some ++ [none]).findSome?
    (castAliasLeg prepared tuple)

/-- The first leg (targets in order, then the authority leg) whose law holds an
out-of-range order clause. -/
def firstRangeLeaf [DecidableEq F]
    (prepared : PreparedInvocation deployment profile ambient durable command)
    (tuple : PreparedTuple (plan prepared)) : Option LawLeaf :=
  ((List.finRange command.targets.length).map some ++ [none]).findSome?
    (rangeLeaf prepared tuple)

/-- The first leg (targets in order, then the authority leg) whose law names a
failing clause. -/
def firstLawLeaf [DecidableEq F]
    (prepared : PreparedInvocation deployment profile ambient durable command)
    (tuple : PreparedTuple (plan prepared)) : Option LawLeaf :=
  ((List.finRange command.targets.length).map some ++ [none]).findSome?
    (lawLeaf prepared tuple)

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

/-! ## Fields (K-FIELDS): a write's footprint against the authorizing scope

A scalar target's fields are its declared state keys' coordinates and its
values are integers; a content target's fields are `body`/`annotations` and it
moves no number.  The footprint is computed from the loaded pre-state and the
computed post-state of the leg, never from the request or the command. -/

def targetField (target : Target) : Address target.layout → CellField := by
  cases target with
  | mk kind id capability version root payload observe =>
    cases payload with
    | scalar _ => exact fun address => ResourceObservationAdmission.declaredField address.2
    | content _ => exact fun address => ResourceObservationAdmission.contentField address.1
    | append _ => exact fun _ => .body

def targetAmount (target : Target) :
    (address : Address target.layout) → target.layout.Value address.1 → Int := by
  cases target with
  | mk kind id capability version root payload observe =>
    cases payload with
    | scalar _ => exact fun _ value => value
    | content _ => exact fun _ _ => 0
    | append _ => exact fun _ _ => 0

/-- A target's footprint, scanning only the patch's write footprint. -/
def targetFootprint (target : Target) (patch : Patch target.layout)
    (pre post : Store target.layout) : Footprint :=
  ResourceObservationAdmission.footprintOf
    (ResourceObservationAdmission.changedWithin (Patch.writeFootprint patch) pre post)
    (targetField target) (targetAmount target) pre post

/-- The footprint of one incidence: a target's write, or nothing for the
authority read. -/
def legFootprint (prepared : PreparedInvocation deployment profile ambient durable command) :
    Incidence command → Option Footprint
  | some i => some (targetFootprint command.targets[i]
      (targetPatch prepared.authority.snapshot profile.semantics ambient command command.targets[i]
        (prepared.targets i).pre)
      (prepared.targets i).pre.logical (prepared.targets i).post)
  | none => none

/-- **The leg's footprint is exactly what the write changed**: scanning the
patch's write footprint finds every changed address of the target cell
(`Patch.run_frame`), so it equals the whole-cell footprint. -/
theorem legFootprint_exact (prepared : PreparedInvocation deployment profile ambient durable command)
    (i : TargetIndex command) :
    legFootprint prepared (some i) = some (ResourceObservationAdmission.footprint
      (targetField command.targets[i]) (targetAmount command.targets[i])
      (prepared.targets i).pre.logical (prepared.targets i).post) := by
  simp only [legFootprint, targetFootprint, ResourceObservationAdmission.footprint]
  rw [ResourceObservationAdmission.changedWithin_eq_changed]
  intro address outside
  rw [← (prepared.targets i).postExact]
  exact (Patch.run_frame _ _ address outside).symm

/-- The authorizing capability's scope against a leg's footprint. Refusals
name the failed coordinate: a field the scope does not name, or a named field
moved past one of its bounds. -/
def fieldsCheck {kind : ResourceKind} (capability : Option (Capability kind × Digest)) :
    Option Footprint → Except Reject Unit
  | none => .ok ()
  | some footprint =>
    match capability with
    | none => .error .capabilityRejected
    | some (cap, _) =>
      if ∀ field ∈ footprint.touched, CellField.NamedBy cap.scope.fields field then
        if cap.scope.FieldsCover footprint then .ok () else .error .maxDeltaExceeded
      else .error .fieldNotNamed

theorem fieldsCheck_ok {kind : ResourceKind} {capability : Option (Capability kind × Digest)}
    {footprint : Footprint} (ok : fieldsCheck capability (some footprint) = .ok ()) :
    ∃ cap digest, capability = some (cap, digest) ∧ cap.scope.FieldsCover footprint := by
  unfold fieldsCheck at ok
  rcases capability with _ | ⟨cap, digest⟩
  · cases ok
  · refine ⟨cap, digest, rfl, ?_⟩
    simp only at ok
    split at ok
    · split at ok
      · assumption
      · cases ok
    · cases ok

/-- Pole: a footprint touching a field the scope does not name refuses by name. -/
theorem fieldsCheck_unnamed {kind : ResourceKind} (cap : Capability kind) (digest : Digest)
    (footprint : Footprint) (field : CellField) (touched : field ∈ footprint.touched)
    (unnamed : ¬ CellField.NamedBy cap.scope.fields field) :
    fieldsCheck (some (cap, digest)) (some footprint) = .error .fieldNotNamed := by
  unfold fieldsCheck
  simp only
  rw [if_neg (fun all => unnamed (all field touched))]

structure CheckedLeg [DecidableEq F]
    (prepared : PreparedInvocation deployment profile ambient durable command)
    (tuple : PreparedTuple (plan prepared)) (incidence : Incidence command) (envelope : List UInt8) where
  receipt : CredentialSignatureAdmission.CheckedSignature prepared.authority.snapshot
  envelopeExact : receipt.envelopeBytes = envelope
  authorization : Authorized (portals prepared tuple incidence)
    prepared.authority.snapshot.authState (tuple.request incidence).2
  authorized : authorizeLeg prepared tuple incidence receipt = .ok authorization
  /-- The authorizing capability names every field the leg changed and bounds
  each change (K-FIELDS). -/
  fields : fieldsCheck authorization.evidence.capabilityValue (legFootprint prepared incidence) = .ok ()

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
        | .ok authorization =>
            match covered : fieldsCheck authorization.evidence.capabilityValue
                (legFootprint prepared incidence) with
            | .error reason => return .error reason
            | .ok () => return .ok ⟨signature, exactWire, authorization, admitted, covered⟩
      else return .error (.signature .sourceBinding)

/-- **An accepted write leg's capability covers its fields.** The capability
that authorized target `i` names every field the leg changed, and each change
is within every bound its scope sets. -/
theorem CheckedLeg.fields_covered [DecidableEq F]
    {prepared : PreparedInvocation deployment profile ambient durable command}
    {tuple : PreparedTuple (plan prepared)} {i : TargetIndex command} {envelope : List UInt8}
    (leg : CheckedLeg prepared tuple (some i) envelope) :
    ∃ cap digest, leg.authorization.evidence.capabilityValue = some (cap, digest) ∧
      cap.scope.FieldsCover (ResourceObservationAdmission.footprint
        (targetField command.targets[i]) (targetAmount command.targets[i])
        (prepared.targets i).pre.logical (prepared.targets i).post) := by
  have fields := leg.fields
  rw [legFootprint_exact] at fields
  exact fieldsCheck_ok fields

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
    accepted.declaration.post accepted.legs none = prepared.authorityPost :=
  accepted.post_exact none

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

/-- The physical writes are the targets' alone: the authority incidence is a
read, so the authority cell enters as a read guard (`readGuards`). -/
def writes (prepared : PreparedInvocation deployment profile ambient durable command) : List DataWrite :=
  (List.finRange command.targets.length).map (targetWrite prepared)

def sourceGuards (prepared : PreparedInvocation deployment profile ambient durable command) : List ReadGuard :=
  (List.finRange command.targets.length).map fun i =>
    ⟨⟨(prepared.targets i).source.readGuard.1⟩, (prepared.targets i).source.readGuard.2⟩

/-- The domain reads of every invocation: the authority cell and the clock. -/
def domainGuards (prepared : PreparedInvocation deployment profile ambient durable command) : List ReadGuard :=
  prepared.authority.readGuards ++ [prepared.clock.readGuard]

def readGuards (prepared : PreparedInvocation deployment profile ambient durable command) : List ReadGuard :=
  sourceGuards prepared ++ (domainGuards prepared).filter fun guard =>
    guard.cellId ∉ (writes prepared).map DataWrite.cellId

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
  let guards := source ++ (domainGuards prepared).filter fun guard => guard.cellId ∉ ids
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
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp member
  rfl

theorem readGuards_readonly (prepared : PreparedInvocation deployment profile ambient durable command)
    (shape : PhysicalShape prepared) :
    ∀ guard ∈ readGuards prepared, guard.cellId ∉ (writes prepared).map DataWrite.cellId := by
  intro guard member
  rcases List.mem_append.mp member with source | authority
  · exact shape.2.2.2.1 guard source
  · simpa using (List.mem_filter.mp authority).2

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
  | .proofWork => (prepared.run.map fun checked => checked.verdict.steps).getD 0
  | .feeDebit | .witnessBytes | .networkBytes | .sideEffectCount | .leaseByteBlocks => 0

def sourceCharge (prepared : PreparedInvocation deployment profile ambient durable command)
    (signed : SignedCommand) : ResourceCost.Charge :=
  sourceChargeFrom prepared signed (writes prepared) (readGuards prepared)

def AcceptedInvocation.dataIntent [DecidableEq F]
    {prepared : PreparedInvocation deployment profile ambient durable command} {signed : SignedCommand}
    (_accepted : AcceptedInvocation prepared signed) (shape : PhysicalShape prepared) :
    DataIntent ResourceBirthCodec.rootBytes :=
  let ws := writes prepared
  let guards := sourceGuards prepared ++ (domainGuards prepared).filter fun guard =>
    guard.cellId ∉ ws.map DataWrite.cellId
  { transactionId := transactionId prepared.authority.snapshot.domain profile.semantics command
    writes := ws
    readGuards := guards
    nullifiers := [invocationNullifier prepared.authority.snapshot.domain
      (operationMarker prepared.authority.snapshot.domain profile.semantics command)]
    exactCharge := sourceChargeFrom prepared signed ws guards
    event := invocationEvent prepared.authority.snapshot.domain profile.semantics command signed
    subject := some command.subject
    postRootsBound := writes_roots_bound prepared
    guardsReadOnly := readGuards_readonly prepared shape }

/-- **Charging rule: a record is charged the bytes it writes.**  The storage
charge of an accepted invocation is exactly the canonical bytes of the cells
its record writes, and those writes are the targets' alone (one per target):
the authority cell is read (a guard), neither stored nor charged. -/
theorem AcceptedInvocation.storage_charge_is_written_bytes [DecidableEq F]
    {prepared : PreparedInvocation deployment profile ambient durable command} {signed : SignedCommand}
    (accepted : AcceptedInvocation prepared signed) (shape : PhysicalShape prepared) :
    (accepted.dataIntent shape).exactCharge .storageBytes =
        ((accepted.dataIntent shape).writes.map fun write => write.canonicalPostBytes.length).sum ∧
      (accepted.dataIntent shape).writes =
        (List.finRange command.targets.length).map (targetWrite prepared) :=
  ⟨rfl, rfl⟩

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
        subject := some command.subject
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

/-- The continuation receives the very object admitted for this signed call
and old durable prefix. It can retain that object through physical readback;
no second independent historical admission is substituted for it. -/
def withAcceptedLoaded {F : Type} [Field F] [DecidableEq F] {R : Type}
    (deployment : Deployment) (profile : CanonicalRuntimeProfile.Profile F)
    (ambient : Ambient) (native : CredentialSignatureIO.NativeConfig)
    (durable : Durable) (signed : SignedCommand)
    (acceptedResult : {command : Command} →
      (prepared : PreparedInvocation deployment profile ambient durable command) →
      (shape : PhysicalShape prepared) →
      AcceptedInvocation prepared signed → IO R)
    (ordinaryResult : ReceiveResult → IO R) : IO R := do
  match commandCodec.decode signed.commandBytes with
  | none => ordinaryResult (.rejected .malformedCommand)
  | some command =>
      match recordedInvocation deployment.domain profile.semantics command signed durable with
      | .error _ => ordinaryResult .transactionConflict
      | .ok (some recorded) => ordinaryResult (.replayed recorded)
      | .ok none =>
          match prepare deployment profile ambient durable command with
          | .error reason => ordinaryResult (.rejected reason)
          | .ok prepared =>
              if shape : PhysicalShape prepared then
                match ← admit native prepared signed with
                | .error reason => ordinaryResult (.rejected reason)
                | .ok accepted => acceptedResult prepared shape accepted
              else ordinaryResult (.rejected .physicalPreparation)

def receiveLoaded {F : Type} [Field F] [DecidableEq F]
    (deployment : Deployment) (profile : CanonicalRuntimeProfile.Profile F)
    (ambient : Ambient) (native : CredentialSignatureIO.NativeConfig)
    (transport : DurableReceiverIO.Transport) (durable : Durable) (signed : SignedCommand) : IO ReceiveResult :=
  withAcceptedLoaded deployment profile ambient native durable signed
    (fun _ shape accepted => do
      return .settlement (← DurableReceiverIO.receiveLoaded transport ResourceBirthCodec.rootBytes
        durable (accepted.dataIntent shape))) pure

def receive {F : Type} [Field F] [DecidableEq F]
    (deployment : Deployment) (profile : CanonicalRuntimeProfile.Profile F)
    (ambient : Ambient) (native : CredentialSignatureIO.NativeConfig)
    (transport : DurableReceiverIO.Transport) (signed : SignedCommand) (_attempts : Nat := 3) : IO ReceiveResult := do
  match ← DurableReceiverIO.load transport ResourceBirthCodec.rootBytes with
  | .error detail => return .unavailable detail
  | .ok durable => receiveLoaded deployment profile ambient native transport durable signed

/-- info: 'Minidregg.Kernel.DeclaredResourceController.lawLeaf_fails' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms lawLeaf_fails
/-- info: 'Minidregg.Kernel.DeclaredResourceController.lawLeaf_none_iff_verifies' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms lawLeaf_none_iff_verifies
/-- info: 'Minidregg.Kernel.DeclaredResourceController.lawLeaf_refuses_iff_verifies_rejects' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms lawLeaf_refuses_iff_verifies_rejects
#assert_axioms rangeLeaf_none_iff_inputsInRange
#assert_axioms castAliasLeg_none_iff_castInjOn

end Minidregg.Kernel.DeclaredResourceController
/-- info: 'Minidregg.Kernel.DeclaredResourceController.fieldsCheck_ok' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.DeclaredResourceController.fieldsCheck_ok
/-- info: 'Minidregg.Kernel.DeclaredResourceController.legFootprint_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.DeclaredResourceController.legFootprint_exact
/-- info: 'Minidregg.Kernel.DeclaredResourceController.fieldsCheck_unnamed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.DeclaredResourceController.fieldsCheck_unnamed
/-- info: 'Minidregg.Kernel.DeclaredResourceController.CheckedLeg.fields_covered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.DeclaredResourceController.CheckedLeg.fields_covered
