/-
Exact portable custody over an existing source history. This module neither
executes a second world nor authorizes installation, reconfiguration or private
share export. The current native receiver remains the authority for those acts.
An acknowledged prefix is independently held by its participant. Archive repair
returns an exact candidate; it does not confer overwrite rights.
-/
import Theory.AssertAxioms
import Kernel.ReceiptContinuity

namespace Minidregg.Kernel.PortableContinuationManifest
open Minidregg.Theory.TypedAuthorization
set_option autoImplicit false
abbrev Bytes := List UInt8

/-- Complete source identity; supplied by a trusted native source configuration,
never learned solely from the archive being restored. -/
abbrev Identity := Minidregg.Kernel.ReceiptContinuity.Identity

structure Prefix where
  identity : Identity
  seed : Bytes
  /-- Canonical encodings of the actual accepted IntentRecords, in order. -/
  records : List Bytes
  deriving DecidableEq, Repr

def Prefix.Extends (new old : Prefix) : Prop :=
  new.identity = old.identity ∧ new.seed = old.seed ∧
  old.records.length ≤ new.records.length ∧
  new.records.take old.records.length = old.records

instance (new old : Prefix) : Decidable (new.Extends old) := by
  unfold Prefix.Extends; infer_instance

theorem Prefix.extends_refl (prefix : Prefix) : prefix.Extends prefix := by
  simp [Prefix.Extends]

theorem Prefix.extends_trans {new middle old : Prefix}
    (later : new.Extends middle) (earlier : middle.Extends old) : new.Extends old := by
  rcases later with ⟨identity, seed, length, records⟩
  rcases earlier with ⟨oldIdentity, oldSeed, oldLength, oldRecords⟩
  refine ⟨identity.trans oldIdentity, seed.trans oldSeed, oldLength.trans length, ?_⟩
  rw [← oldRecords, ← records, List.take_take, Nat.min_eq_left oldLength]

/-- Physical selector is a canonical, source-selected coordinate, not an arbitrary
request path. Include immutable snapshot/invocation/generation identity in the
coordinate; a mutable pathname alone is not an obligation identity. Its bytes
may name a volume, provider hold, control frame, outbox,
private generation descriptor or immutable correlation anchor. -/
structure Artifact where
  coordinate : Bytes
  exactInventory : Bytes
  deriving DecidableEq, Repr

structure Manifest where
  prefix : Prefix
  /-- Entire canonical DurableReceiver.Image, not a projection of app counters.
Contains all cells/modules/currentrefs/notes/nullifiers/charges and accepted events. -/
  image : Bytes
  /-- Public endpoint computed from the complete source image by the native codec. -/
  point : Minidregg.Kernel.ReceiptContinuity.Point
  generation : Nat
  /-- Exact predecessor custody frame pin; physical publication checks its bytes.
This is custody linkage, never a source-authorized transfer fence. -/
  predecessor : Bytes
  /-- Native pause, SPK, resident/provider, consensus replay and private custody
inventories are opaque and exact. Their owners retain admission semantics. -/
  artifacts : List Artifact
  deriving DecidableEq, Repr

/-- Independent participant-held pin. Changing a source signing key or copying a
MAC key from the archive cannot rewrite this acknowledged prefix. -/
structure ParticipantPin where
  participant : SubjectId
  publicKey : Bytes
  identity : Identity
  acknowledged : Minidregg.Kernel.ReceiptContinuity.Point
  deriving DecidableEq, Repr

/-- Public commitment only. Neither acknowledgement nor its continuity suffix
contains hidden source records, payload bytes or private custody inventory. -/
structure Acknowledgement where
  participant : SubjectId
  publicKey : Bytes
  identity : Identity
  point : Minidregg.Kernel.ReceiptContinuity.Point
  deriving DecidableEq, Repr

def acknowledgementQuery (pin : ParticipantPin) (ack : Acknowledgement) :
    Minidregg.Kernel.ReceiptContinuity.Query :=
  ⟨pin.identity, some pin.acknowledged, ack.point⟩

/-- Continuity, not signatures/current authority. The native IO seam verifies
this exact public frame with the independently pinned key before returning an
opaque checked ACK. Paging a suffix cannot acknowledge an unreached endpoint. -/
def acknowledge (pin : ParticipantPin) (ack : Acknowledgement)
    (extension : Minidregg.Kernel.ReceiptContinuity.Extension) : Option ParticipantPin :=
  if ack.participant = pin.participant ∧ ack.publicKey = pin.publicKey ∧
      ack.identity = pin.identity ∧ extension.endPoint = ack.point ∧
      Minidregg.Kernel.ReceiptContinuity.Valid (acknowledgementQuery pin ack) extension then
    some { pin with acknowledged := ack.point }
  else none

theorem acknowledge_exact {pin next : ParticipantPin} {ack : Acknowledgement}
    {extension : Minidregg.Kernel.ReceiptContinuity.Extension}
    (accepted : acknowledge pin ack extension = some next) :
    ack.participant = pin.participant ∧ ack.publicKey = pin.publicKey ∧
    ack.identity = pin.identity ∧ extension.endPoint = ack.point ∧
    Minidregg.Kernel.ReceiptContinuity.Valid (acknowledgementQuery pin ack) extension ∧
    next.acknowledged = ack.point ∧ next.participant = pin.participant ∧
    next.publicKey = pin.publicKey ∧ next.identity = pin.identity := by
  unfold acknowledge at accepted
  split at accepted
  · rename_i checked
    cases accepted
    exact ⟨checked.1, checked.2.1, checked.2.2.1, checked.2.2.2.1,
      checked.2.2.2.2, rfl, rfl, rfl, rfl⟩
  · cases accepted

theorem acknowledge_nonregression {pin next : ParticipantPin} {ack : Acknowledgement}
    {extension : Minidregg.Kernel.ReceiptContinuity.Extension}
    (accepted : acknowledge pin ack extension = some next) :
    pin.acknowledged.height ≤ next.acknowledged.height := by
  have exact := acknowledge_exact accepted
  rw [exact.2.2.2.2.2.1]
  exact exact.2.2.2.2.1.2.2.1

/-- The old acknowledged endpoint's authenticated system opening and exact
chain extension remain load-bearing. This is commitment-prefix continuity;
source record equality additionally uses hash separation, not a disclosure. -/
theorem acknowledge_prefix_preserved {pin next : ParticipantPin} {ack : Acknowledgement}
    {extension : Minidregg.Kernel.ReceiptContinuity.Extension}
    (accepted : acknowledge pin ack extension = some next) :
    extension.startPoint = pin.acknowledged ∧
    Minidregg.Kernel.ReceiptContinuity.chainAfterDigests extension.startChain
      extension.suffix = extension.endChain ∧
    Minidregg.Kernel.ReceiptContinuity.opens extension.startPoint extension.startChain
      extension.fromSiblings = true ∧
    Minidregg.Kernel.ReceiptContinuity.opens extension.endPoint extension.endChain
      extension.toSiblings = true := by
  have valid := (acknowledge_exact accepted).2.2.2.2.1
  exact Minidregg.Kernel.ReceiptContinuity.accepted_binds_chain _ _
    ((Minidregg.Kernel.ReceiptContinuity.verify_ok_iff _ _).mpr valid)

theorem acknowledge_wrong_key_refuses (pin : ParticipantPin) (ack : Acknowledgement)
    (extension : Minidregg.Kernel.ReceiptContinuity.Extension)
    (wrong : ack.publicKey ≠ pin.publicKey) : acknowledge pin ack extension = none := by
  simp [acknowledge, wrong]

theorem acknowledge_same_height_fork_refuses (pin : ParticipantPin) (ack : Acknowledgement)
    (extension : Minidregg.Kernel.ReceiptContinuity.Extension)
    (height : pin.acknowledged.height = ack.point.height)
    (conflict : pin.acknowledged.worldRoot ≠ ack.point.worldRoot) :
    acknowledge pin ack extension = none := by
  unfold acknowledge
  apply if_neg
  intro checked
  have refused := Minidregg.Kernel.ReceiptContinuity.same_height_conflict_refused
    (acknowledgementQuery pin ack) extension height conflict
  have valid := (Minidregg.Kernel.ReceiptContinuity.verify_ok_iff _ _).mpr checked.2.2.2.2
  rw [refused] at valid
  cases valid

/-- Requirements come from the source-owned outstanding-obligation closure.
A proposed archive cannot choose an empty list to erase old liabilities. -/
def Preserves (required : List Artifact) (manifest : Manifest) : Prop :=
  ∀ artifact ∈ required, artifact ∈ manifest.artifacts

instance (required : List Artifact) (manifest : Manifest) : Decidable (Preserves required manifest) := by
  unfold Preserves; infer_instance

/-- Restore acceptance retains the participant prefix and every outstanding
source-selected obligation. It still does not authorize running the snapshot. -/
def acceptRepair (pin : ParticipantPin) (required : List Artifact)
    (manifest : Manifest) (extension : Minidregg.Kernel.ReceiptContinuity.Extension) : Option Manifest :=
  let ack : Acknowledgement := ⟨pin.participant, pin.publicKey, manifest.prefix.identity, manifest.point⟩
  if (acknowledge pin ack extension).isSome ∧ Preserves required manifest then
    some manifest else none

theorem repair_exact {pin : ParticipantPin} {required : List Artifact}
    {offered accepted : Manifest} {extension : Minidregg.Kernel.ReceiptContinuity.Extension}
    (checked : acceptRepair pin required offered extension = some accepted) :
    accepted = offered ∧ Preserves required accepted := by
  unfold acceptRepair at checked
  split at checked
  · rename_i valid
    cases checked
    exact ⟨rfl, valid.2⟩
  · cases checked

theorem repair_missing_obligation_refuses (pin : ParticipantPin) (required : List Artifact)
    (manifest : Manifest) (extension : Minidregg.Kernel.ReceiptContinuity.Extension)
    (artifact : Artifact) (owed : artifact ∈ required) (missing : artifact ∉ manifest.artifacts) :
    acceptRepair pin required manifest extension = none := by
  unfold acceptRepair
  apply if_neg
  intro checked
  exact missing (checked.2 artifact owed)

/-- The readback seam consumes a canonically checked frame from immutable archive
custody. Equal base means already current. Exactly one linked next generation
means a typed recovery candidate; no automatic installation/acknowledgement. -/
inductive Reconciliation where
  | current
  | recoveryRequired (candidate : Manifest)
  | refused
  deriving DecidableEq, Repr

def reconcile (base : Manifest) (baseFrame : Bytes) (archive : Manifest) : Reconciliation :=
  if archive = base then .current
  else if archive.generation = base.generation + 1 ∧ archive.predecessor = baseFrame ∧
      archive.prefix.Extends base.prefix then .recoveryRequired archive
  else .refused

theorem recovery_one_successor {base archive candidate : Manifest} {baseFrame : Bytes}
    (checked : reconcile base baseFrame archive = .recoveryRequired candidate) :
    candidate = archive ∧ candidate.generation = base.generation + 1 ∧
    candidate.predecessor = baseFrame ∧ candidate.prefix.Extends base.prefix := by
  unfold reconcile at checked
  split at checked
  · cases checked
  · split at checked
    · rename_i linked
      cases checked
      exact ⟨rfl, linked.1, linked.2.1, linked.2.2⟩
    · cases checked

theorem reconcile_generation_gap_refuses (base archive : Manifest) (baseFrame : Bytes)
    (different : archive ≠ base) (gap : archive.generation ≠ base.generation + 1) :
    reconcile base baseFrame archive = .refused := by
  simp [reconcile, different, gap]

/-- The current source receiver, private qualified-generation adapter and physical
worker fence must each discharge their OWN predicate before successor activation.
This is an obligation join, not an independent governance/token constructor. -/
structure SuccessorCore where
  retained : Manifest
  targetConfiguration : Bytes
  nextGeneration : Nat
  privateDescriptor : Bytes
  deriving DecidableEq, Repr

structure SuccessorRequest where
  retained : Manifest
  targetConfiguration : Bytes
  nextGeneration : Nat
  sourceDecision : Bytes
  privateDescriptor : Bytes

def SuccessorRequest.core (request : SuccessorRequest) : SuccessorCore :=
  ⟨request.retained, request.targetConfiguration, request.nextGeneration, request.privateDescriptor⟩

structure ReadySuccessor (request : SuccessorRequest)
    (CurrentSourceAuthorized PrivateQualified OldWorkerFenced : SuccessorRequest → Prop)
    (required : List Artifact) : Prop where
  sourceAuthorized : CurrentSourceAuthorized request
  privateQualified : PrivateQualified request
  oldWorkerFenced : OldWorkerFenced request
  freshGeneration : request.nextGeneration = request.retained.generation + 1
  obligationsPreserved : Preserves required request.retained

/-- Uncertain external effects retain their exact request/reply/provider/outbox
custody. Neither repair nor an acknowledged prefix resolves that uncertainty. -/
theorem repair_retains_obligation {pin : ParticipantPin} {required : List Artifact}
    {offered accepted : Manifest} {extension : Minidregg.Kernel.ReceiptContinuity.Extension}
    (checked : acceptRepair pin required offered extension = some accepted)
    {artifact : Artifact} (owed : artifact ∈ required) : artifact ∈ accepted.artifacts :=
  (repair_exact checked).2 artifact owed

#assert_axioms acknowledge_wrong_key_refuses
#assert_axioms acknowledge_same_height_fork_refuses
#assert_axioms repair_missing_obligation_refuses
#assert_axioms reconcile_generation_gap_refuses
#assert_axioms Prefix.extends_trans
#assert_axioms acknowledge_nonregression
#assert_axioms acknowledge_prefix_preserved
#assert_axioms repair_exact
#assert_axioms recovery_one_successor
#assert_axioms repair_retains_obligation
end Minidregg.Kernel.PortableContinuationManifest
