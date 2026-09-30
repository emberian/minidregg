/-
# Theory.DeployedTotalCarrierAudit -- all deleted deployed carriers stay dead

`MaterializerCardinality` proves the original total-function carrier impossible
for declared effects, and `Kernel.EventLogMaterializerLimit` proves the same
for the event log.  The authority and Hyperdocument cases were described but
not separately pinned.  This module closes those two regression teeth.

Both proofs embed every Boolean stream into one infinite typed namespace:
authority revocation membership and Hyperdocument mark records respectively.
Any lawful total-state codec would therefore inject `Nat -> Bool` into byte
strings, which is impossible.  These negative theorems concern only the
deleted total carrier, `MaterializerCardinality.TotalStore`.  The canonical
`Store L` remains inhabited (`DeployedMaterializerWitness`).
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
open Minidregg.Theory.Store

set_option autoImplicit false

/-! ## Credential authority total-state impossibility -/

def emptyCapability (kind : ResourceKind) : Capability kind where
  id := ⟨0⟩
  root := ⟨0⟩
  parent := none
  issuer := ⟨0⟩
  holder := .bearer
  scope := ⟨.explicit ∅, ∅, 0⟩
  notBefore := 0
  notAfter := 0
  issuerEpoch := 0
  policyId := ⟨0⟩
  policyEpoch := 0
  ancestors := ∅
  channels := ∅

/-- The old total authority state can retain an arbitrary Boolean stream in
the issuer-epoch plane (epoch `1` marks, `0` does not).  The revocation,
nullifier and registration planes are presence-only (`Unit`) and carry no bit;
every other typed field receives an arbitrary inhabitant solely to reconstruct
the deleted carrier. -/
def totalAuthorityStateOf (marked : Nat -> Bool) :
    TotalStore CredentialAuthorityState.layout
  | ⟨.capability kind, _⟩ => show StoredCapability kind from ⟨emptyCapability kind, []⟩
  | ⟨.issuerEpoch, ⟨identifier⟩⟩ => show Epoch from (marked identifier).toNat
  | ⟨.policyEpoch, _⟩ => show Epoch from 0
  | ⟨.policyRevision, _⟩ => show PolicyRevision from 0
  | ⟨.policyAddress, _⟩ => show Digest from ⟨0⟩
  | ⟨.subjectKeyEpoch, _⟩ => show Epoch from 0
  | ⟨.subjectKey, (subject, epoch)⟩ =>
      show CredentialSigningKey.KeyRecord from
        { keyId := 0, keyEpoch := epoch, algorithm := 0, subject := subject.value,
          publicKey := [], activeFrom := 0, activeUntil := 0, revoked := false }
  | ⟨.revoked, _⟩ => show Unit from ()
  | ⟨.nullifier, _⟩ => show Unit from ()
  | ⟨.registered, _⟩ => show Unit from ()

theorem totalAuthorityStateOf_injective :
    Function.Injective totalAuthorityStateOf := by
  intro left right same
  funext index
  have marked : (left index).toNat = (right index).toNat := congrFun same
    (⟨.issuerEpoch, ⟨index⟩⟩ : Address CredentialAuthorityState.layout)
  revert marked
  cases left index <;> cases right index <;> decide

/-- Restoring a total field at the authority boundary reintroduces the exact
cardinality obstruction fixed by the sparse migration. -/
theorem totalAuthorityMaterializer_isEmpty :
    IsEmpty
      (TotalMaterializer CredentialAuthorityState.layout Digest) :=
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
    TotalStore Hyperdocument.layout
  | ⟨.documents, _⟩ => show DocumentRecord from baseDocumentRecord
  | ⟨.atoms, _⟩ => show AtomRecord from baseAtomRecord
  | ⟨.runs, _⟩ => show RunRecord from baseRunRecord
  | ⟨.elements, _⟩ => show ElementRecord from baseElementRecord
  | ⟨.fields, _⟩ => show FieldRecord from baseFieldRecord
  | ⟨.conflicts, _⟩ => show ConflictRecord from baseConflictRecord
  | ⟨.links, _⟩ => show LinkRecord from baseLinkRecord
  | ⟨.transclusions, _⟩ => show TransclusionRecord from baseTransclusionRecord
  | ⟨.marks, ⟨⟨identifier⟩⟩⟩ => show MarkRecord from markValue (marked identifier)
  | ⟨.annotations, _⟩ => show AnnotationRecord from baseAnnotationRecord

theorem totalHyperdocumentStateOf_injective :
    Function.Injective totalHyperdocumentStateOf := by
  intro left right same
  funext index
  exact markValue_injective (congrFun same
    (⟨.marks, ⟨⟨index⟩⟩⟩ : Hyperdocument.Address))

/-- Restoring a total field at the Hyperdocument boundary is impossible for
the same cardinality reason; finite sparse storage is load-bearing. -/
theorem totalHyperdocumentMaterializer_isEmpty :
    IsEmpty (TotalMaterializer Hyperdocument.layout Digest) :=
  totalMaterializer_isEmpty_of_natBool_embedding totalHyperdocumentStateOf
    totalHyperdocumentStateOf_injective

/-! ## Axiom audit -/

/-- info: 'Minidregg.Theory.DeployedTotalCarrierAudit.totalAuthorityStateOf_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms totalAuthorityStateOf_injective
/-- info: 'Minidregg.Theory.DeployedTotalCarrierAudit.totalAuthorityMaterializer_isEmpty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms totalAuthorityMaterializer_isEmpty
/-- info: 'Minidregg.Theory.DeployedTotalCarrierAudit.totalHyperdocumentStateOf_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms totalHyperdocumentStateOf_injective
/-- info: 'Minidregg.Theory.DeployedTotalCarrierAudit.totalHyperdocumentMaterializer_isEmpty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms totalHyperdocumentMaterializer_isEmpty

end Minidregg.Theory.DeployedTotalCarrierAudit
