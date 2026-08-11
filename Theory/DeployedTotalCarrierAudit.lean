/-
# Theory.DeployedTotalCarrierAudit -- all deleted deployed carriers stay dead

`MaterializerCardinality` proves the original total-function carrier impossible
for declared effects, and `Kernel.EventLogMaterializerLimit` proves the same
for the event log.  The authority and Hyperdocument cases were described but
not separately pinned.  This module closes those two regression teeth.

Both proofs embed every Boolean stream into one infinite typed address plane:
authority revocation membership and Hyperdocument mark records respectively.
Any lawful total-state codec would therefore inject `Nat -> Bool` into byte
strings, which is impossible.  These negative theorems concern only the
deleted total carrier.  The canonical finite `DFinsupp` state remains inhabited
and is exercised by the deployed witnesses.
-/
import Theory.DeployedMaterializerWitness
import Theory.MaterializerCardinality

namespace Minidregg.Theory.DeployedTotalCarrierAudit

open Minidregg.Theory
open Minidregg.Theory.CellState
open Minidregg.Theory.CredentialAuthorityState
open Minidregg.Theory.Hyperdocument
open Minidregg.Theory.IndexedProgram
open Minidregg.Theory.MaterializerCardinality
open Minidregg.Theory.TypedAuthorization

set_option autoImplicit false

/-! ## Credential authority total-state impossibility -/

def emptyCapability (kind : ResourceKind) : Capability kind where
  id := ⟨0⟩
  root := ⟨0⟩
  parent := none
  issuer := ⟨0⟩
  holder := .bearer
  scope := ⟨∅, ∅, 0⟩
  notBefore := 0
  notAfter := 0
  issuerEpoch := 0
  policyId := ⟨0⟩
  policyEpoch := 0
  ancestors := ∅
  channels := ∅

/-- The old total authority state can retain an arbitrary Boolean stream in
the capability-revocation plane.  All unrelated typed fields receive an
arbitrary inhabitant solely to reconstruct the deleted carrier. -/
noncomputable def totalAuthorityStateOf (marked : Nat -> Bool) :
    TotalLogicalState CredentialAuthorityState.schema.{0, 0} where
  fields
    | .capability kind _ => ⟨emptyCapability kind, []⟩
    | .issuerEpoch _ => show Epoch from 0
    | .policyEpoch _ => show Epoch from 0
    | .policyAddress _ _ => show Digest from ⟨0⟩
    | .subjectKeyEpoch _ => show Epoch from 0
    | .revoked (.capability ⟨identifier⟩) => marked identifier
    | .revoked (.channel _) => false
    | .nullifier _ => false
  resources := fun resource => nomatch resource

theorem totalAuthorityStateOf_injective :
    Function.Injective totalAuthorityStateOf := by
  intro left right same
  funext index
  have fields := congrArg TotalLogicalState.fields same
  have point := congrFun fields (.revoked (.capability ⟨index⟩))
  exact point

/-- Restoring a total field at the authority boundary reintroduces the exact
cardinality obstruction fixed by the sparse migration. -/
theorem totalAuthorityMaterializer_isEmpty :
    IsEmpty
      (TotalMaterializer CredentialAuthorityState.schema.{0, 0} Digest) :=
  totalMaterializer_isEmpty_of_natBool_embedding totalAuthorityStateOf
    totalAuthorityStateOf_injective

/-! ## Hyperdocument total-state impossibility -/

def baseDigest : Digest := ⟨0⟩
def baseIdentifier {domain : IdDomain} : Identifier .v1 domain := ⟨baseDigest⟩
def basePrincipal : PrincipalRef := ⟨⟨0⟩, .object, ⟨0⟩⟩
def basePoint : StablePoint :=
  ⟨baseIdentifier, none, .before, .invalidate⟩
def baseRange : StableRange := ⟨basePoint, basePoint⟩

def baseDocumentRecord : DocumentRecord :=
  ⟨baseIdentifier, baseDigest, basePrincipal, baseIdentifier⟩
def baseAtomRecord : AtomRecord :=
  ⟨baseIdentifier, .text, [], basePrincipal, baseIdentifier, none⟩
def baseRunRecord : RunRecord :=
  ⟨baseIdentifier, [], basePrincipal, baseIdentifier, none⟩
def baseElementRecord : ElementRecord :=
  ⟨baseIdentifier, none, .container [], basePrincipal, baseIdentifier, none⟩
def baseFieldRecord : FieldRecord where
  valueType := .flag
  value := false
  merge := .exclusive
  writtenBy := basePrincipal
  writtenAt := baseIdentifier
def baseFieldKey : FieldKey := ⟨.document baseIdentifier, baseDigest⟩
def baseConflictRecord : ConflictRecord :=
  ⟨baseFieldKey, none, [], .exclusive, baseIdentifier⟩
def baseOpening : OpeningDescriptor :=
  ⟨.value, baseDigest, baseDigest, [], baseDigest⟩
def baseSource : StoredSourceIdentity :=
  ⟨baseDigest, baseDigest, baseDigest, baseDigest⟩
def baseReference : StoredTransclusionRef :=
  ⟨baseDigest, baseSource, baseOpening, .snapshot, ∅, ∅⟩
def baseLinkRecord : LinkRecord :=
  ⟨baseIdentifier, none, .document baseIdentifier, baseDigest,
    basePrincipal, baseIdentifier, none⟩
def baseTransclusionRecord : TransclusionRecord :=
  ⟨baseIdentifier, baseReference, basePrincipal, baseIdentifier, baseDigest,
    none⟩
def baseAnnotationRecord : AnnotationRecord :=
  ⟨baseIdentifier, none, baseIdentifier, basePrincipal, baseIdentifier,
    baseDigest, none⟩

/-- Two visibly distinct mark values, with every non-discriminating field held
fixed. -/
def markValue (marked : Bool) : MarkRecord :=
  ⟨baseIdentifier, baseRange, ⟨if marked then 1 else 0⟩, [],
    basePrincipal, baseIdentifier, baseDigest, none⟩

theorem markValue_injective : Function.Injective markValue := by
  intro left right same
  have kind := congrArg MarkRecord.kind same
  cases left <;> cases right <;> simp [markValue] at kind ⊢

/-- The old total Hyperdocument state can retain a Boolean stream in the
infinite mark-id plane. -/
def totalHyperdocumentStateOf (marked : Nat -> Bool) :
    TotalLogicalState Hyperdocument.cellSchema.{0, 0} where
  fields
    | ⟨.documents, _⟩ => baseDocumentRecord
    | ⟨.atoms, _⟩ => baseAtomRecord
    | ⟨.runs, _⟩ => baseRunRecord
    | ⟨.elements, _⟩ => baseElementRecord
    | ⟨.fields, _⟩ => baseFieldRecord
    | ⟨.conflicts, _⟩ => baseConflictRecord
    | ⟨.links, _⟩ => baseLinkRecord
    | ⟨.transclusions, _⟩ => baseTransclusionRecord
    | ⟨.marks, ⟨⟨identifier⟩⟩⟩ => markValue (marked identifier)
    | ⟨.annotations, _⟩ => baseAnnotationRecord
  resources := fun resource => nomatch resource

theorem totalHyperdocumentStateOf_injective :
    Function.Injective totalHyperdocumentStateOf := by
  intro left right same
  funext index
  have fields := congrArg TotalLogicalState.fields same
  have point := congrFun fields
    (⟨.marks, ⟨⟨index⟩⟩⟩ : Hyperdocument.Address)
  exact markValue_injective point

/-- Restoring a total field at the Hyperdocument boundary is impossible for
the same cardinality reason; finite sparse storage is load-bearing. -/
theorem totalHyperdocumentMaterializer_isEmpty :
    IsEmpty (TotalMaterializer Hyperdocument.cellSchema.{0, 0} Digest) :=
  totalMaterializer_isEmpty_of_natBool_embedding totalHyperdocumentStateOf
    totalHyperdocumentStateOf_injective

/-! ## Axiom audit -/

/-- info: 'Minidregg.Theory.DeployedTotalCarrierAudit.totalAuthorityStateOf_injective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms totalAuthorityStateOf_injective
/-- info: 'Minidregg.Theory.DeployedTotalCarrierAudit.totalAuthorityMaterializer_isEmpty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms totalAuthorityMaterializer_isEmpty
/-- info: 'Minidregg.Theory.DeployedTotalCarrierAudit.totalHyperdocumentStateOf_injective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms totalHyperdocumentStateOf_injective
/-- info: 'Minidregg.Theory.DeployedTotalCarrierAudit.totalHyperdocumentMaterializer_isEmpty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms totalHyperdocumentMaterializer_isEmpty

end Minidregg.Theory.DeployedTotalCarrierAudit
