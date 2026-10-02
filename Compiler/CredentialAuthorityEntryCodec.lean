/-
# Compiler.CredentialAuthorityEntryCodec -- exact executable authority payloads

The payload types are the actual `TypedAuthorization.Capability` and
`CredentialAuthorityState.StoredCapability`; no transport-side authority
model participates. Finite sets are encoded in sorted natural-label order,
not through a noncomputable choice of enumeration. Naturals use the shared
compact prefix codec. Whole-page canonical decoding is enforced by the page
materializer, including rejection of aliases accepted by primitive codecs.
-/
import Compiler.TypedAuthorizationRequestCodec
import Compiler.CredentialSigningKeyCodec
import Theory.CredentialAuthorityState
import Mathlib.Data.Finset.Sort

namespace Minidregg.Compiler.CredentialAuthorityEntryCodec

open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Compiler.TypedAuthorizationRequestCodec
open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.CredentialAuthorityState
open Minidregg.Theory.CredentialAuthorityFamily

set_option autoImplicit false

/-- Sorting is a computable canonical enumeration of the finite set. -/
def natSetStream : StreamCodec (Finset Nat) :=
  StreamCodec.xmap (StreamCodec.list StreamCodec.nat)
    (fun values => values.sort (· ≤ ·)) List.toFinset
    (by intro values; exact Finset.sort_toFinset _ _)

/-- Transport a sorted finite set along a concrete, total retraction.
Invalid natural labels may decode provisionally; exact whole-page re-encoding
rejects them before they become materialized authority. -/
def labeledSetStream {alpha : Type} [DecidableEq alpha]
    (label : alpha → Nat) (ofLabel : Nat → alpha)
    (roundtrip : ∀ value, ofLabel (label value) = value) :
    StreamCodec (Finset alpha) :=
  StreamCodec.xmap natSetStream (Finset.image label) (Finset.image ofLabel)
    (by
      intro values
      rw [Finset.image_image]
      simpa only [Function.comp_def, roundtrip] using
        (Finset.image_id : Finset.image _root_.id values = values))

def capabilityIdStream : StreamCodec CapabilityId :=
  StreamCodec.xmap StreamCodec.nat CapabilityId.value CapabilityId.mk
    (by intro value; cases value; rfl)

def issuerIdStream : StreamCodec IssuerId :=
  StreamCodec.xmap StreamCodec.nat IssuerId.value IssuerId.mk
    (by intro value; cases value; rfl)

def channelIdStream : StreamCodec ChannelId :=
  StreamCodec.xmap StreamCodec.nat ChannelId.value ChannelId.mk
    (by intro value; cases value; rfl)

def capabilitySetStream : StreamCodec (Finset CapabilityId) :=
  labeledSetStream CapabilityId.value CapabilityId.mk
    (by intro value; cases value; rfl)

def channelSetStream : StreamCodec (Finset ChannelId) :=
  labeledSetStream ChannelId.value ChannelId.mk
    (by intro value; cases value; rfl)

def resourceSetStream (kind : ResourceKind) :
    StreamCodec (Finset (ResourceId kind)) :=
  labeledSetStream ResourceId.value ResourceId.mk
    (by intro value; cases value; rfl)

def verbTag : {kind : ResourceKind} → Verb kind → Nat
  | _, .observeObject => 1
  | _, .mutateObject => 2
  | _, .delegateObject => 3
  | _, .observeAccount => 1
  | _, .transfer => 2
  | _, .delegateAccount => 3
  | _, .observeProgram => 1
  | _, .installProgram => 2
  | _, .delegateProgram => 3
  | _, .installPolicy => 4
  | _, .revokeCapability => 5
  | _, .appendObject => 7
  | _, .mintAsset => 8
  | _, .burnAsset => 9
  | _, .observePayment => 6
  | _, .tickClock => 11
  | _, .placeObject => 10

def verbOfTag : (kind : ResourceKind) → Nat → Verb kind
  | .object, 1 => .observeObject
  | .object, 2 => .mutateObject
  | .object, 7 => .appendObject
  | .object, 10 => .placeObject
  | .object, _ => .delegateObject
  | .account, 1 => .observeAccount
  | .account, 2 => .transfer
  | .account, 8 => .mintAsset
  | .account, 9 => .burnAsset
  | .account, _ => .delegateAccount
  | .program, 1 => .observeProgram
  | .program, 2 => .installProgram
  | .program, 4 => .installPolicy
  | .program, 5 => .revokeCapability
  | .program, 6 => .observePayment
  | .program, 11 => .tickClock
  | .program, _ => .delegateProgram

theorem verbOfTag_tag {kind : ResourceKind} (verb : Verb kind) :
    verbOfTag kind (verbTag verb) = verb := by
  cases verb <;> rfl

def verbSetStream (kind : ResourceKind) : StreamCodec (Finset (Verb kind)) :=
  labeledSetStream verbTag (verbOfTag kind) verbOfTag_tag

def holderStream : StreamCodec Holder where
  encode
    | .bearer => [0]
    | .subject subject => 1 :: subjectIdStream.encode subject
  decodePrefix
    | 0 :: suffix => some (.bearer, suffix)
    | 1 :: bytes => do
        let (subject, suffix) ← subjectIdStream.decodePrefix bytes
        some (.subject subject, suffix)
    | _ => none
  decodePrefix_encode := by
    intro holder suffix
    cases holder with
    | bearer => rfl
    | subject subject => simp [subjectIdStream.decodePrefix_encode]

/-- Scope targets carry a tag byte: `0` an explicit sorted target set, `1`
the room cell of an `under` scope. Any other leading byte refuses. -/
def targetSetStream (kind : ResourceKind) : StreamCodec (TargetSet kind) where
  encode
    | .explicit targets => 0 :: (resourceSetStream kind).encode targets
    | .under room => 1 :: StreamCodec.nat.encode room
  decodePrefix
    | 0 :: bytes => do
        let (targets, suffix) ← (resourceSetStream kind).decodePrefix bytes
        some (.explicit targets, suffix)
    | 1 :: bytes => do
        let (room, suffix) ← StreamCodec.nat.decodePrefix bytes
        some (.under room, suffix)
    | _ => none
  decodePrefix_encode := by
    intro targets suffix
    cases targets with
    | explicit targets => simp [(resourceSetStream kind).decodePrefix_encode]
    | under room => simp [StreamCodec.nat.decodePrefix_encode]

/-- A field's natural label: `slot n ↦ 4n`, `balance a ↦ 4a+1`, and the
three content/program fields at `2`, `6`, `10`.  Any other label decodes
provisionally to `slot 0` and is refused by the whole-page re-encoding. -/
def fieldLabel : CellField → Nat
  | .slot n => 4 * n
  | .balance asset => 4 * asset + 1
  | .code => 2
  | .body => 6
  | .annotations => 10

def fieldOfLabel (label : Nat) : CellField :=
  if label % 4 = 0 then .slot (label / 4)
  else if label % 4 = 1 then .balance (label / 4)
  else if label = 2 then .code
  else if label = 6 then .body
  else if label = 10 then .annotations
  else .slot 0

theorem fieldOfLabel_label (field : CellField) : fieldOfLabel (fieldLabel field) = field := by
  cases field <;> simp [fieldLabel, fieldOfLabel] <;> omega

def fieldSetStream : StreamCodec (Finset CellField) :=
  labeledSetStream fieldLabel fieldOfLabel fieldOfLabel_label

/-- The JSON name of a field: `"7"` (slot 7), `"balance:3"`, `"code"`,
`"body"`, `"annotations"`. -/
def cellFieldName : CellField → String
  | .slot n => toString n
  | .balance asset => s!"balance:{asset}"
  | .code => "code"
  | .body => "body"
  | .annotations => "annotations"

def cellFieldOfName (name : String) : Option CellField :=
  match name with
  | "code" => some .code
  | "body" => some .body
  | "annotations" => some .annotations
  | _ =>
    if name.startsWith "balance:" then (name.drop 8).toNat?.map CellField.balance
    else name.toNat?.map CellField.slot

/-- A per-field bound is labelled by the Cantor pairing of its field label and
its bound. -/
def boundLabel (bound : CellField × Nat) : Nat := Nat.pair (fieldLabel bound.1) bound.2

def boundOfLabel (label : Nat) : CellField × Nat :=
  (fieldOfLabel label.unpair.1, label.unpair.2)

theorem boundOfLabel_label (bound : CellField × Nat) : boundOfLabel (boundLabel bound) = bound := by
  simp [boundLabel, boundOfLabel, Nat.unpair_pair, fieldOfLabel_label]

def boundSetStream : StreamCodec (Finset (CellField × Nat)) :=
  labeledSetStream boundLabel boundOfLabel boundOfLabel_label

/-- Scope frame (`stored-capability/v3`): target set, verbs, budget, then the
named fields (absent = every field) and the per-field bounds. -/
abbrev ScopeTuple (kind : ResourceKind) :=
  TargetSet kind × Finset (Verb kind) × Nat × Option (Finset CellField) × Finset (CellField × Nat)

def scopeTupleStream (kind : ResourceKind) : StreamCodec (ScopeTuple kind) :=
  StreamCodec.product (targetSetStream kind)
    (StreamCodec.product (verbSetStream kind)
      (StreamCodec.product StreamCodec.nat
        (StreamCodec.product (StreamCodec.option fieldSetStream) boundSetStream)))

def scopeTuple {kind : ResourceKind} (scope : Scope kind) : ScopeTuple kind :=
  (scope.targets, scope.verbs, scope.maxCost, scope.fields, scope.maxDelta)

def scopeOfTuple {kind : ResourceKind} (tuple : ScopeTuple kind) : Scope kind :=
  ⟨tuple.1, tuple.2.1, tuple.2.2.1, tuple.2.2.2.1, tuple.2.2.2.2⟩

def scopeStream (kind : ResourceKind) : StreamCodec (Scope kind) :=
  StreamCodec.xmap (scopeTupleStream kind) scopeTuple scopeOfTuple
    (by intro scope; rfl)

abbrev CapabilityTuple (kind : ResourceKind) :=
  CapabilityId × CapabilityId × Option CapabilityId × IssuerId × Holder ×
    Scope kind × Nat × Nat × Nat × PolicyId × Nat × Finset CapabilityId ×
    Finset ChannelId

def capabilityTupleStream (kind : ResourceKind) :
    StreamCodec (CapabilityTuple kind) :=
  StreamCodec.product capabilityIdStream
    (StreamCodec.product capabilityIdStream
      (StreamCodec.product (StreamCodec.option capabilityIdStream)
        (StreamCodec.product issuerIdStream
          (StreamCodec.product holderStream
            (StreamCodec.product (scopeStream kind)
              (StreamCodec.product StreamCodec.nat
                (StreamCodec.product StreamCodec.nat
                  (StreamCodec.product StreamCodec.nat
                    (StreamCodec.product policyIdStream
                      (StreamCodec.product StreamCodec.nat
                        (StreamCodec.product capabilitySetStream
                          channelSetStream)))))))))))

def capabilityTuple {kind : ResourceKind} (cap : Capability kind) :
    CapabilityTuple kind :=
  ⟨cap.id, cap.root, cap.parent, cap.issuer, cap.holder, cap.scope,
    cap.notBefore, cap.notAfter, cap.issuerEpoch, cap.policyId,
    cap.policyEpoch, cap.ancestors, cap.channels⟩

def capabilityOfTuple {kind : ResourceKind} (tuple : CapabilityTuple kind) :
    Capability kind where
  id := tuple.1
  root := tuple.2.1
  parent := tuple.2.2.1
  issuer := tuple.2.2.2.1
  holder := tuple.2.2.2.2.1
  scope := tuple.2.2.2.2.2.1
  notBefore := tuple.2.2.2.2.2.2.1
  notAfter := tuple.2.2.2.2.2.2.2.1
  issuerEpoch := tuple.2.2.2.2.2.2.2.2.1
  policyId := tuple.2.2.2.2.2.2.2.2.2.1
  policyEpoch := tuple.2.2.2.2.2.2.2.2.2.2.1
  ancestors := tuple.2.2.2.2.2.2.2.2.2.2.2.1
  channels := tuple.2.2.2.2.2.2.2.2.2.2.2.2

theorem capabilityOfTuple_tuple {kind : ResourceKind} (cap : Capability kind) :
    capabilityOfTuple (capabilityTuple cap) = cap := rfl

def capabilityStream (kind : ResourceKind) : StreamCodec (Capability kind) :=
  StreamCodec.xmap (capabilityTupleStream kind) capabilityTuple capabilityOfTuple
    capabilityOfTuple_tuple

/-- Exact origin data. A delegated request is historical source data, not
an authorization certificate; the effect family owns its creation proof. -/
def lineageOriginStream (kind : ResourceKind) : StreamCodec (LineageOrigin kind) where
  encode
    | .strict => [0]
    | .delegated request => 1 :: (requestStreamFor kind).encode request
  decodePrefix
    | 0 :: suffix => some (.strict, suffix)
    | 1 :: bytes => do
        let (request, suffix) ← (requestStreamFor kind).decodePrefix bytes
        some (.delegated request, suffix)
    | _ => none
  decodePrefix_encode := by
    intro origin suffix
    cases origin with
    | strict => rfl
    | delegated request => simp [(requestStreamFor kind).decodePrefix_encode]

def parentLinkStream (kind : ResourceKind) : StreamCodec (ParentLink kind) :=
  StreamCodec.xmap
    (StreamCodec.product (capabilityStream kind) (lineageOriginStream kind))
    (fun link => (link.parent, link.origin))
    (fun pair => ⟨pair.1, pair.2⟩)
    (by intro link; rfl)

def storedCapabilityStream (kind : ResourceKind) :
    StreamCodec (StoredCapability kind) :=
  StreamCodec.xmap
    (StreamCodec.product (capabilityStream kind)
      (StreamCodec.list (parentLinkStream kind)))
    (fun stored => (stored.head, stored.ancestry))
    (fun tuple => ⟨tuple.1, tuple.2⟩)
    (by intro stored; rfl)

/-- An explicit scope survives transport exactly. -/
theorem scope_explicit_roundtrip (kind : ResourceKind)
    (targets : Finset (ResourceId kind)) (verbs : Finset (Verb kind)) (maxCost : Nat)
    (fields : Option (Finset CellField)) (bounds : Finset (CellField × Nat))
    (suffix : List UInt8) :
    (scopeStream kind).decodePrefix
        ((scopeStream kind).encode ⟨.explicit targets, verbs, maxCost, fields, bounds⟩ ++ suffix) =
      some (⟨.explicit targets, verbs, maxCost, fields, bounds⟩, suffix) :=
  (scopeStream kind).decodePrefix_encode _ suffix

/-- An `under` scope survives transport exactly. -/
theorem scope_under_roundtrip (kind : ResourceKind)
    (room : Nat) (verbs : Finset (Verb kind)) (maxCost : Nat) (fields : Option (Finset CellField)) (bounds : Finset (CellField × Nat))
    (suffix : List UInt8) :
    (scopeStream kind).decodePrefix
        ((scopeStream kind).encode ⟨.under room, verbs, maxCost, fields, bounds⟩ ++ suffix) =
      some (⟨.under room, verbs, maxCost, fields, bounds⟩, suffix) :=
  (scopeStream kind).decodePrefix_encode _ suffix

/-- The tag byte is the first byte of every scope frame. -/
theorem scope_frame_tag (kind : ResourceKind) (scope : Scope kind) :
    ((scopeStream kind).encode scope).head? =
      some (match scope.targets with | .explicit _ => 0 | .under _ => 1) := by
  rcases scope with ⟨targets, verbs, maxCost, fields, bounds⟩
  cases targets <;> rfl

/-- An explicit scope and an `under` scope never share bytes. -/
theorem scope_explicit_ne_under (kind : ResourceKind)
    (targets : Finset (ResourceId kind)) (room : Nat)
    (verbs verbs' : Finset (Verb kind)) (maxCost maxCost' : Nat)
    (fields fields' : Option (Finset CellField)) (bounds bounds' : Finset (CellField × Nat)) :
    (scopeStream kind).encode ⟨.explicit targets, verbs, maxCost, fields, bounds⟩ ≠
      (scopeStream kind).encode ⟨.under room, verbs', maxCost', fields', bounds'⟩ := by
  intro same
  have heads := congrArg List.head? same
  rw [scope_frame_tag, scope_frame_tag] at heads
  simp at heads

/-- A scope frame whose tag byte is neither `0` nor `1` refuses. -/
theorem scope_other_tag_refused (kind : ResourceKind) (tag : UInt8)
    (zero : tag ≠ 0) (one : tag ≠ 1) (rest : List UInt8) :
    (scopeStream kind).decodePrefix (tag :: rest) = none := by
  simp only [scopeStream, StreamCodec.xmap, scopeTupleStream, StreamCodec.product,
    targetSetStream]
  split <;> simp_all

/-- Two scopes that differ only in their named fields encode differently: a
`fields` restriction cannot be dropped in transport. -/
theorem scope_fields_bound {kind : ResourceKind} {left right : Scope kind}
    (same : (scopeStream kind).encode left = (scopeStream kind).encode right) :
    left.fields = right.fields ∧ left.maxDelta = right.maxDelta := by
  have decoded := congrArg (fun bytes => (scopeStream kind).decodePrefix (bytes ++ [])) same
  simp only [(scopeStream kind).decodePrefix_encode, Option.some.injEq, Prod.mk.injEq] at decoded
  rw [decoded.1]; exact ⟨rfl, rfl⟩

/-- Origin tags never conflate a strict step with an explicit delegated step. -/
theorem lineage_origin_tags_separate (kind : ResourceKind) (request : Request kind) :
    (lineageOriginStream kind).encode .strict ≠
      (lineageOriginStream kind).encode (.delegated request) := by
  simp [lineageOriginStream]

/-- Retaining the resource-kind coordinate rejects a request transplanted
from a different kind, even inside an otherwise valid lineage record. -/
theorem lineage_origin_wrong_request_kind {actual expected : ResourceKind}
    (request : Request actual) (suffix : List UInt8) (different : actual ≠ expected) :
    (lineageOriginStream expected).decodePrefix
      (1 :: (someRequestStream.encode ⟨actual, request⟩ ++ suffix)) = none := by
  simp [lineageOriginStream, requestStreamFor_wrong_kind request suffix different]

/-- Every field of the capability, including lineage, survives transport. -/
theorem storedCapability_roundtrip (kind : ResourceKind)
    (stored : StoredCapability kind) (suffix : List UInt8) :
    (storedCapabilityStream kind).decodePrefix
        ((storedCapabilityStream kind).encode stored ++ suffix) =
      some (stored, suffix) :=
  (storedCapabilityStream kind).decodePrefix_encode stored suffix

/-- Changing a holder or any lineage detail changes the bytes: this is a
universal separation theorem, not a golden vector. -/
theorem storedCapability_encode_injective (kind : ResourceKind) :
    Function.Injective (storedCapabilityStream kind).encode := by
  intro left right equal
  have decoded := congrArg (storedCapabilityStream kind).toLawful.decode equal
  change (storedCapabilityStream kind).toLawful.decode
      ((storedCapabilityStream kind).toLawful.encode left) =
    (storedCapabilityStream kind).toLawful.decode
      ((storedCapabilityStream kind).toLawful.encode right) at decoded
  rw [(storedCapabilityStream kind).toLawful.decode_encode,
    (storedCapabilityStream kind).toLawful.decode_encode] at decoded
  exact Option.some.inj decoded

/-- A diagnostic representation uses the same computable exact encoding;
it does not invoke the noncomputable/unsafe `Finset` printer. -/
instance (kind : ResourceKind) : Repr (StoredCapability kind) where
  reprPrec stored precedence :=
    reprPrec ((storedCapabilityStream kind).encode stored) precedence

/-- info: 'Minidregg.Compiler.CredentialAuthorityEntryCodec.fieldOfLabel_label' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms fieldOfLabel_label
/-- info: 'Minidregg.Compiler.CredentialAuthorityEntryCodec.boundOfLabel_label' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms boundOfLabel_label
/-- info: 'Minidregg.Compiler.CredentialAuthorityEntryCodec.scope_fields_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms scope_fields_bound
/-- info: 'Minidregg.Compiler.CredentialAuthorityEntryCodec.scope_explicit_roundtrip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms scope_explicit_roundtrip
/-- info: 'Minidregg.Compiler.CredentialAuthorityEntryCodec.scope_under_roundtrip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms scope_under_roundtrip
/-- info: 'Minidregg.Compiler.CredentialAuthorityEntryCodec.scope_explicit_ne_under' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms scope_explicit_ne_under
/-- info: 'Minidregg.Compiler.CredentialAuthorityEntryCodec.scope_other_tag_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms scope_other_tag_refused
/-- info: 'Minidregg.Compiler.CredentialAuthorityEntryCodec.storedCapability_roundtrip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms storedCapability_roundtrip
/-- info: 'Minidregg.Compiler.CredentialAuthorityEntryCodec.storedCapability_encode_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms storedCapability_encode_injective

end Minidregg.Compiler.CredentialAuthorityEntryCodec
