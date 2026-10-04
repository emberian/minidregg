/-
Frozen Store2 boundary for the audited 3b1f628a deployment. The generic codec
below only describes source bytes; it authorizes nothing. The closed role
converters pin old descriptors and are used only after retained-source audit.
Transform2 begins each retained hiding key's target ratchet at the carry height;
it does not assert that historical Store2 writes already followed that ratchet.
-/
import Compiler.CanonicalCellRegistry
import Kernel.PayCellUpgrade

namespace Minidregg.Compiler.LegacyStoreCarry

open Minidregg.Theory
open Minidregg.Theory.Store
open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.CredentialAuthorityState
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Compiler.StoreCodec
open Minidregg.Compiler.CanonicalCellRegistry (Kind)

set_option autoImplicit false

/-- Exact source frame. Never uses the target storeVersion. -/
def frameV2 {L : Layout.{0, 0, 0}} (wire : StoreCodec.Wire L) : List UInt8 :=
  [68, 82, 69, 71, 71, 47, 83, 84, 79, 82, 69, 2] ++ layoutDigest wire

def encodeV2 {L : Layout.{0, 0, 0}} (wire : StoreCodec.Wire L) (store : Store L) : List UInt8 :=
  frameV2 wire ++ (payloadStream wire).encode store

/-- Fully consumed canonical source bytes, including the frozen outer frame. -/
def decodeV2 {L : Layout.{0, 0, 0}} (wire : StoreCodec.Wire L) (bytes : List UInt8) : Option (Store L) := do
  if bytes.take (frameV2 wire).length != frameV2 wire then none else do
    let store ← decodePayload wire (bytes.drop (frameV2 wire).length)
    if encodeV2 wire store = bytes then some store else none

private def ns (tag : List UInt8) (discipline : UInt8) (key value : String) : NamespaceDescriptor :=
  (tag, discipline, key.toUTF8.toList, value.toUTF8.toList)

private def desc (name : String) (spaces : List NamespaceDescriptor)
    (blinding : Option (List UInt8) := none) : LayoutDescriptor :=
  (name.toUTF8.toList, spaces, blinding)

/-- Literal descriptors reviewed against source commit 3b1f628a. A later target
codec declaration cannot quietly change what this converter accepts. -/
def declaredDescriptor : LayoutDescriptor :=
  desc "minidregg/declared-effect/v1"
    [ns [] 1 "state-key/tagged-v3" "int/zigzag-base255"] (some [3])

def eventDescriptor : LayoutDescriptor :=
  desc "minidregg/hyperdocument-events/v1"
    [ns [] 2 "version-event-id/digest" "version-event-record/v1"]

def payDescriptor : LayoutDescriptor :=
  desc "DREGG/PAY/CELL/v4"
    [ns [0] 1 "unit" "DREGG/PAY/TARIFF/v3",
     ns [1] 2 "book-index/nat" "address32/bytes",
     ns [2] 2 "book-index/nat" "account-id/nat",
     ns [4] 1 "mini-key32/bytes" "DREGG/PAY/ENROLMENT/v1",
     ns [5] 2 "ssh-ed25519-blob/bytes" "mini-key32/bytes",
     ns [6] 2 "soltx-nullifier/bytes" "DREGG/PAY/UNATTRIBUTED/v1"]

def streamDescriptor : LayoutDescriptor :=
  desc "minidregg/stream-head/v2" [ns [] 1 "unit" "stream-head/v2"]
def streamEntryDescriptor : LayoutDescriptor :=
  desc "minidregg/stream-entry/v1" [ns [] 2 "unit" "stream-entry/v1"]
def clockDescriptor : LayoutDescriptor :=
  desc "DREGG/CLOCK/v1" [ns [0] 1 "unit" "DREGG/CLOCK/NOW-SLOT/v1"]
def systemDescriptor : LayoutDescriptor :=
  desc "DREGG/SYSTEM/v1" [ns [0] 1 "unit" "DREGG/SYSTEM/CERTIFIED-HEIGHT-DIGEST-TAIL-BOUND/v1"]

private def decodePinned {L : Layout.{0, 0, 0}} (wire : StoreCodec.Wire L)
    (expected : LayoutDescriptor) (bytes : List UInt8) : Except String (Store L) := do
  if layoutDescriptor wire != expected then
    throw "carry target wire differs from the frozen source layout"
  let some store := decodeV2 wire bytes | throw "carry refuses noncanonical or non-Store2 source"
  pure store

/-- Source v2 signing-key record: no pre-rotation commitment existed. -/
abbrev LegacyKey := Nat × Nat × Nat × Nat × List UInt8 × Nat × Nat

-- Supply the product instances explicitly: asking typeclass search for the
-- entire transparent alias can select this very instance recursively.
instance : DecidableEq LegacyKey :=
  @instDecidableEqProd Nat _ inferInstance
    (@instDecidableEqProd Nat _ inferInstance
      (@instDecidableEqProd Nat _ inferInstance
        (@instDecidableEqProd Nat _ inferInstance
          (@instDecidableEqProd (List UInt8) _ inferInstance
            (@instDecidableEqProd Nat Nat inferInstance inferInstance)))))

def legacyKeyStream : StreamCodec LegacyKey :=
  StreamCodec.product StreamCodec.nat
    (StreamCodec.product StreamCodec.nat
      (StreamCodec.product StreamCodec.nat
        (StreamCodec.product StreamCodec.nat
          (StreamCodec.product bytesStream
            (StreamCodec.product StreamCodec.nat StreamCodec.nat)))))

def liftKey : LegacyKey → CredentialSigningKey.KeyRecord
  | (keyId, keyEpoch, algorithm, subject, publicKey, activeFrom, activeUntil) =>
      { keyId, keyEpoch, algorithm, subject, publicKey, activeFrom, activeUntil,
        nextKeyDigest := none }

@[simp] theorem liftKey_no_future_commitment (key : LegacyKey) :
    (liftKey key).nextKeyDigest = none := by
  rcases key with ⟨_, _, _, _, _, _, _⟩
  rfl

def LegacyValue : AuthorityPlane → Type
  | .subjectKey => LegacyKey
  | plane => plane.Value

instance legacyValueDecEq : (plane : AuthorityPlane) → DecidableEq (LegacyValue plane) := by
  intro plane
  cases plane <;> simp only [LegacyValue] <;> infer_instance

abbrev authorityLayout : Layout.{0, 0, 0} where
  Namespace := AuthorityPlane
  Key := AuthorityPlane.Key
  Value := LegacyValue
  discipline := AuthorityPlane.discipline

def legacyValueStream : (plane : AuthorityPlane) → StreamCodec (LegacyValue plane)
  | .subjectKey => legacyKeyStream
  | .capability kind => CredentialAuthorityCell.valueStream (.capability kind)
  | .issuerEpoch => CredentialAuthorityCell.valueStream .issuerEpoch
  | .policyEpoch => CredentialAuthorityCell.valueStream .policyEpoch
  | .policyRevision => CredentialAuthorityCell.valueStream .policyRevision
  | .policyAddress => CredentialAuthorityCell.valueStream .policyAddress
  | .subjectKeyEpoch => CredentialAuthorityCell.valueStream .subjectKeyEpoch
  | .revoked => CredentialAuthorityCell.valueStream .revoked
  | .registered => CredentialAuthorityCell.valueStream .registered
  | .parent => CredentialAuthorityCell.valueStream .parent

def authorityWire : StoreCodec.Wire authorityLayout where
  name := "minidregg/credential-authority/v5"
  namespaces := CredentialAuthorityCell.planes
  namespaces_complete := CredentialAuthorityCell.wire.namespaces_complete
  namespaceStream := CredentialAuthorityCell.planeStream
  keyStream := CredentialAuthorityCell.keyStream
  valueStream := legacyValueStream
  keyCodecId := CredentialAuthorityCell.keyCodecId
  valueCodecId plane := match plane with
    | .subjectKey => "signing-key-record/v2"
    | other => CredentialAuthorityCell.valueCodecId other

def authorityDescriptor : LayoutDescriptor :=
  desc "minidregg/credential-authority/v5"
    [ns [0] 1 "capability-id/nat" "stored-capability/v3",
     ns [1] 1 "capability-id/nat" "stored-capability/v3",
     ns [2] 1 "capability-id/nat" "stored-capability/v3",
     ns [3] 1 "issuer-id/nat" "nat/base255",
     ns [4] 1 "policy-id/nat" "nat/base255",
     ns [11] 1 "policy-id/nat" "nat/base255",
     ns [5] 1 "policy-id/nat x nat" "digest/nat",
     ns [6] 1 "subject-id/nat" "nat/base255",
     ns [10] 1 "subject-id/nat x nat" "signing-key-record/v2",
     ns [7] 2 "revocation-key/tagged-v2" "unit/presence",
     ns [12] 2 "revocation-key/tagged-v2" "unit/presence",
     ns [13] 2 "cell-id/nat" "cell-id/nat"]

def liftAuthorityValue : (plane : AuthorityPlane) → LegacyValue plane → plane.Value
  | .subjectKey, value => liftKey value
  | .capability _, value => value
  | .issuerEpoch, value => value
  | .policyEpoch, value => value
  | .policyRevision, value => value
  | .policyAddress, value => value
  | .subjectKeyEpoch, value => value
  | .revoked, value => value
  | .registered, value => value
  | .parent, value => value

def liftAuthority (store : Store authorityLayout) : Store CredentialAuthorityState.layout :=
  store.mapRange (fun address value => value.map (liftAuthorityValue address.1))
    (fun _ => rfl)

/-- Every present source entry is lifted at the identical typed address;
absence is preserved, including retired historical policy-address entries. -/
@[simp] theorem liftAuthority_apply (store : Store authorityLayout)
    (address : Address authorityLayout) :
    liftAuthority store address = (store address).map (liftAuthorityValue address.1) := rfl

theorem liftAuthority_absent (store : Store authorityLayout)
    (address : Address authorityLayout) (absent : store address = none) :
    liftAuthority store address = none := by
  simp [liftAuthority_apply, absent]

/-- Actual grant records, including scopes, parent lineage, epochs and
revocation references, are retained verbatim as typed values. -/
@[simp] theorem liftAuthority_capability (store : Store authorityLayout)
    (kind : ResourceKind) (identifier : CapabilityId) :
    liftAuthority store ⟨.capability kind, identifier⟩ =
      store ⟨.capability kind, identifier⟩ := by
  rw [liftAuthority_apply]
  cases store ⟨AuthorityPlane.capability kind, identifier⟩ <;> rfl

private def oldObjectCapability (cap : StoredCapability .object) : Bool :=
  !(decide (.placeObject ∈ cap.head.scope.verbs)) && cap.ancestry.all fun link =>
    !(decide (.placeObject ∈ link.parent.scope.verbs)) && match link.origin with
      | .strict => true
      | .delegated request => request.verb != .placeObject

/-- No source grant is created or attenuated. Keys retain every old field and
explicitly lack an invented future-key commitment. New object verb tag10 is
not in the source language, including inside retained lineage requests. -/
def decodeAuthority (bytes : List UInt8) : Except String (Store CredentialAuthorityState.layout) := do
  let old ← decodePinned authorityWire authorityDescriptor bytes
  for entry in entries authorityWire old do
    match entry with
    | ⟨⟨AuthorityPlane.capability ResourceKind.object, _⟩, cap⟩ =>
        if !oldObjectCapability cap then throw "carry source grant uses a post-source verb"
    | _ => pure ()
  pure (liftAuthority old)

/-- The carry itself is the first target ratchet step, at the actual global
height assigned to the carry record. All ordinary declared fields are exact. -/
def liftDeclared (height : Nat) (store : Store EffectDeclaration.effectLayout) :
    Store EffectDeclaration.effectLayout :=
  Patch.run store (DeclaredEffectCell.blinding.patch store height)

theorem liftDeclared_other (height : Nat) (store : Store EffectDeclaration.effectLayout)
    (address : Address EffectDeclaration.effectLayout)
    (other : address ≠ DeclaredEffectCell.blinding.address) :
    liftDeclared height store address = store address :=
  DeclaredEffectCell.blinding.run_patch_frame store store height address other

private def decodeDeclared (height : Nat) (bytes : List UInt8) :
    Except String (Store EffectDeclaration.effectLayout) := do
  pure (liftDeclared height (← decodePinned DeclaredEffectCell.wire declaredDescriptor bytes))

/-- The source paid payload uses the literal Store2/v4 layout. Decode it
with the frozen typed source wire, then use the shared field-preserving v5
lift. New claims, chain evidence, usage and activation remain absent: carry
cannot turn unknown historical execution into an unused compute allowance. -/
def decodePay (bytes : List UInt8) : Except String Kernel.PayCell.PayStore := do
  let old ← decodePinned Kernel.PayCellLegacyV4.wire payDescriptor bytes
  pure (Kernel.PayCellUpgrade.lift old)

/-- Closed non-content/non-policy role dispatch. This returns logical target
state; the caller still checks the actual role/deployment and full loaded image.
Content and policy have separate semantic converters. Newly introduced world
roles refuse. The Book and Nock wires did not change at this boundary. -/
def convertPayload (kind : Kind) (height : Nat) (bytes : List UInt8) :
    Except String (Store (CanonicalCellRegistry.layout kind)) :=
  match kind with
  | .eventHistory => decodePinned HyperdocumentCell.eventWire eventDescriptor bytes
  | .authority => decodeAuthority bytes
  | .declaredObject => decodeDeclared height bytes
  | .accountMetadata => decodeDeclared height bytes
  | .declaredProgram => decodeDeclared height bytes
  | .pay => decodePay bytes
  | .stream => decodePinned StreamCell.headWire streamDescriptor bytes
  | .streamEntry => decodePinned StreamCell.entryWire streamEntryDescriptor bytes
  | .clock => decodePinned Kernel.ClockCell.wire clockDescriptor bytes
  | .system => decodePinned Kernel.SystemCell.wire systemDescriptor bytes
  | .resourceBook =>
      match CanonicalResourcePageMaterializer.materializer.codec.decode bytes with
      | some store => .ok store
      | none => .error "carry source Book is not canonical"
  | .nockProgram =>
      match NockProgramCodec.materializer.codec.decode bytes with
      | some store => .ok store
      | none => .error "carry source Nock program is not canonical"
  | .content | .policySource | .worldKind | .worldInstance | .objectiveActivity =>
      .error "carry role requires a separate closed semantic converter"

end Minidregg.Compiler.LegacyStoreCarry
