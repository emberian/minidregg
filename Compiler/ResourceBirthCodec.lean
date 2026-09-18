/-
# Compiler.ResourceBirthCodec -- exact birth and lifecycle bytes

Birth transport encodes the existing complete descriptor, including dependent
typed initial cells and full capabilities. It has no host-selected effects
projection. Strict whole-message re-encoding rejects aliases and trailing data.

The physical lifecycle envelope represents the existing Directory's slot and
permanent allocation bit. Fresh absence is the empty byte string, matching the
durable receiver's unknown-cell default. A retired identity has an explicit
tombstone. Live cells retain the existing PackedCell dependent schema envelope.
This module defines no alternative create/delete transition or directory.

Physical roots and native payload roots have different purposes and encodings.
The former use one cSHAKE domain for durable CAS; the latter remain the exact
selected schema materializer's roots. No equality between those functions is
postulated.
-/
import Theory.ResourceBirth
import Compiler.CredentialAuthorityEntryCodec
import Compiler.Sp800185Cshake256

namespace Minidregg.Compiler.ResourceBirthCodec

open Minidregg.Theory
open Minidregg.Theory.IndexedProgram
open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.CredentialAuthorityState
open Minidregg.Theory.CellRegistry
open Minidregg.Theory.ResourceBirth
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Compiler.TypedAuthorizationRequestCodec
open Minidregg.Compiler.CredentialAuthorityEntryCodec

set_option autoImplicit false

/-! ## Exact canonical transport -/

def strictCodec {α : Type} (codec : LawfulCodec α) : LawfulCodec α where
  encode := codec.encode
  decode bytes := do
    let value ← codec.decode bytes
    if codec.encode value = bytes then some value else none
  decode_encode := by intro value; simp [codec.decode_encode]

theorem strictCodec_canonical {α : Type} (codec : LawfulCodec α)
    {bytes : List UInt8} {value : α}
    (accepted : (strictCodec codec).decode bytes = some value) :
    codec.encode value = bytes := by
  simp only [strictCodec, Option.bind_eq_bind, Option.bind_eq_some_iff] at accepted
  obtain ⟨decoded, _, accepted⟩ := accepted
  split_ifs at accepted with exactBytes
  · cases Option.some.inj accepted
    exact exactBytes

theorem lawful_encode_injective {α : Type} (codec : LawfulCodec α) :
    Function.Injective codec.encode := by
  intro left right same
  have decoded := congrArg codec.decode same
  rw [codec.decode_encode, codec.decode_encode] at decoded
  exact Option.some.inj decoded

def packedCellStream (registry : TypeRegistry Digest) :
    StreamCodec (PackedCell registry) where
  encode cell := bytesStream.encode (PackedCell.bytes registry cell)
  decodePrefix bytes := do
    let (payload, suffix) ← bytesStream.decodePrefix bytes
    let cell ← PackedCell.decode registry payload
    some (cell, suffix)
  decodePrefix_encode := by
    intro cell suffix
    simp [bytesStream.decodePrefix_encode, PackedCell.decode_bytes]

def resourceKindStream : StreamCodec ResourceKind where
  encode
    | .object => [0]
    | .account => [1]
    | .program => [2]
  decodePrefix
    | 0 :: suffix => some (.object, suffix)
    | 1 :: suffix => some (.account, suffix)
    | 2 :: suffix => some (.program, suffix)
    | _ => none
  decodePrefix_encode := by intro kind suffix; cases kind <;> rfl

def createRequestStream (registry : TypeRegistry Digest) :
    StreamCodec (CreateRequest (CellId := Nat) registry) :=
  StreamCodec.xmap
    (StreamCodec.product StreamCodec.nat
      (StreamCodec.product digestStream (packedCellStream registry)))
    (fun request => (request.cellId, request.expectedPreRoot, request.cell))
    (fun tuple => ⟨tuple.1, tuple.2.1, tuple.2.2⟩)
    (by intro request; rfl)

def birthItemStream (registry : TypeRegistry Digest) :
    StreamCodec (BirthItem registry) :=
  StreamCodec.xmap
    (StreamCodec.product (createRequestStream registry)
      (StreamCodec.product resourceKindStream subjectIdStream))
    (fun item => (item.create, item.resourceKind, item.owner))
    (fun tuple => ⟨tuple.1, tuple.2.1, tuple.2.2⟩)
    (by intro item; rfl)

def authorityGrantStream : StreamCodec AuthorityGrant where
  encode
    | ⟨.object, stored⟩ => 0 :: (storedCapabilityStream .object).encode stored
    | ⟨.account, stored⟩ => 1 :: (storedCapabilityStream .account).encode stored
    | ⟨.program, stored⟩ => 2 :: (storedCapabilityStream .program).encode stored
  decodePrefix
    | 0 :: bytes => do
        let (stored, suffix) ← (storedCapabilityStream .object).decodePrefix bytes
        some (⟨.object, stored⟩, suffix)
    | 1 :: bytes => do
        let (stored, suffix) ← (storedCapabilityStream .account).decodePrefix bytes
        some (⟨.account, stored⟩, suffix)
    | 2 :: bytes => do
        let (stored, suffix) ← (storedCapabilityStream .program).decodePrefix bytes
        some (⟨.program, stored⟩, suffix)
    | _ => none
  decodePrefix_encode := by
    rintro ⟨kind, stored⟩ suffix
    cases kind <;> simp [(storedCapabilityStream _).decodePrefix_encode]

def fourNatStream : StreamCodec (Nat × Nat × Nat × Nat) :=
  StreamCodec.product StreamCodec.nat
    (StreamCodec.product StreamCodec.nat
      (StreamCodec.product StreamCodec.nat StreamCodec.nat))

def fundingStream : StreamCodec InitialFunding :=
  StreamCodec.xmap fourNatStream
    (fun funding => (funding.source, funding.destination, funding.asset, funding.amount))
    (fun tuple => ⟨tuple.1, tuple.2.1, tuple.2.2.1, tuple.2.2.2⟩)
    (by intro funding; rfl)

def feeStream : StreamCodec CreationFee :=
  StreamCodec.xmap fourNatStream
    (fun fee => (fee.payer, fee.collector, fee.asset, fee.amount))
    (fun tuple => ⟨tuple.1, tuple.2.1, tuple.2.2.1, tuple.2.2.2⟩)
    (by intro fee; rfl)

def initialPolicyStream : StreamCodec InitialPolicy :=
  StreamCodec.xmap
    (StreamCodec.product policyIdStream (StreamCodec.product digestStream bytesStream))
    (fun policy => (policy.policyId, policy.address, policy.canonicalBytes))
    (fun tuple => ⟨tuple.1, tuple.2.1, tuple.2.2⟩)
    (by intro policy; rfl)

abbrev DescriptorTuple (registry : TypeRegistry Digest) :=
  ResourceId .object × SubjectId × Digest × Nat × List (BirthItem registry) ×
    List (CreateRequest (CellId := Nat) registry) ×
    List AuthorityGrant × List InitialPolicy × Nat × List InitialFunding × CreationFee

def descriptorTupleStream (registry : TypeRegistry Digest) :
    StreamCodec (DescriptorTuple registry) :=
  StreamCodec.product (resourceIdStream .object)
    (StreamCodec.product subjectIdStream
      (StreamCodec.product digestStream
        (StreamCodec.product StreamCodec.nat
          (StreamCodec.product (StreamCodec.list (birthItemStream registry))
            (StreamCodec.product (StreamCodec.list (createRequestStream registry))
              (StreamCodec.product (StreamCodec.list authorityGrantStream)
                (StreamCodec.product (StreamCodec.list initialPolicyStream)
                  (StreamCodec.product StreamCodec.nat
                    (StreamCodec.product (StreamCodec.list fundingStream) feeStream)))))))))

def descriptorTuple {registry : TypeRegistry Digest}
    (descriptor : Descriptor registry) : DescriptorTuple registry :=
  ⟨descriptor.factory, descriptor.creator, descriptor.transactionId,
    descriptor.nonce, descriptor.births, descriptor.auxiliaryCreates, descriptor.grants,
    descriptor.initialPolicies, descriptor.authorityNullifier, descriptor.funding, descriptor.fee⟩

def descriptorOfTuple {registry : TypeRegistry Digest}
    (tuple : DescriptorTuple registry) : Descriptor registry where
  factory := tuple.1
  creator := tuple.2.1
  transactionId := tuple.2.2.1
  nonce := tuple.2.2.2.1
  births := tuple.2.2.2.2.1
  auxiliaryCreates := tuple.2.2.2.2.2.1
  grants := tuple.2.2.2.2.2.2.1
  initialPolicies := tuple.2.2.2.2.2.2.2.1
  authorityNullifier := tuple.2.2.2.2.2.2.2.2.1
  funding := tuple.2.2.2.2.2.2.2.2.2.1
  fee := tuple.2.2.2.2.2.2.2.2.2.2

def descriptorStream (registry : TypeRegistry Digest) :
    StreamCodec (Descriptor registry) :=
  StreamCodec.xmap (descriptorTupleStream registry)
    descriptorTuple descriptorOfTuple (by intro descriptor; rfl)

def descriptorFrame : List UInt8 := [68,82,69,71,71,47,66,73,82,84,72,3]

def framedDescriptorCodec (registry : TypeRegistry Digest) :
    LawfulCodec (Descriptor registry) where
  encode descriptor := descriptorFrame ++ (descriptorStream registry).encode descriptor
  decode
    | 68 :: 82 :: 69 :: 71 :: 71 :: 47 :: 66 :: 73 :: 82 :: 84 :: 72 :: 3 :: payload =>
        (descriptorStream registry).toLawful.decode payload
    | _ => none
  decode_encode := by
    intro descriptor
    simpa [descriptorFrame] using (descriptorStream registry).toLawful.decode_encode descriptor

def descriptorCodec (registry : TypeRegistry Digest) :
    LawfulCodec (Descriptor registry) := strictCodec (framedDescriptorCodec registry)

theorem descriptor_decode_encode (registry : TypeRegistry Digest)
    (descriptor : Descriptor registry) :
    (descriptorCodec registry).decode ((descriptorCodec registry).encode descriptor) =
      some descriptor :=
  (descriptorCodec registry).decode_encode descriptor

theorem descriptor_decode_canonical (registry : TypeRegistry Digest)
    {bytes : List UInt8} {descriptor : Descriptor registry}
    (accepted : (descriptorCodec registry).decode bytes = some descriptor) :
    (descriptorCodec registry).encode descriptor = bytes :=
  strictCodec_canonical (framedDescriptorCodec registry) accepted

/-- Full descriptors are separated by exact canonical bytes. Hash binding is
not inferred from this theorem, and no finite hash is assumed injective. -/
theorem descriptor_encode_injective (registry : TypeRegistry Digest) :
    Function.Injective (descriptorCodec registry).encode :=
  lawful_encode_injective (descriptorCodec registry)

/-- Version-one payloads cannot be read as births with omitted installed
source. The version boundary is checked before any payload interpretation. -/
theorem descriptor_legacy_version_refused (registry : TypeRegistry Digest)
    (payload : List UInt8) :
    (descriptorCodec registry).decode
      ([68,82,69,71,71,47,66,73,82,84,72,1] ++ payload) = none := rfl

/-- Version two carried the old capability ancestry representation and no
separate current policy revision. It is not reinterpreted under this ABI. -/
theorem descriptor_pre_revision_version_refused (registry : TypeRegistry Digest)
    (payload : List UInt8) :
    (descriptorCodec registry).decode
      ([68,82,69,71,71,47,66,73,82,84,72,2] ++ payload) = none := rfl

/-- Full source bytes, addresses and target policy identities are retained by
the command encoding. No content-hash injectivity is used here. -/
theorem descriptor_initial_sources_bound (registry : TypeRegistry Digest)
    (left right : Descriptor registry)
    (same : (descriptorCodec registry).encode left =
      (descriptorCodec registry).encode right) :
    left.initialPolicies = right.initialPolicies :=
  congrArg Descriptor.initialPolicies (descriptor_encode_injective registry same)

def commitmentBytes (bytes : List UInt8) : Digest :=
  (Sp800185Cshake256.hash "DREGG.RESOURCE.BIRTH.COMMIT/v1".toUTF8.toList bytes).digest

/-- Fixed once by the receiving deployment. The schema catalog is not a wire
argument; its match is retained by every FactoryAuthorization. -/
def sourceEncoding (registry : TypeRegistry Digest)
    (resourceKindOf : registry.Kind -> ResourceKind) : SourceEncoding registry where
  codec := descriptorCodec registry
  hashBytes := commitmentBytes
  resourceKindOf := resourceKindOf

/-! ## Representation of the existing lifecycle directory -/

/-- A serialized observation, not a second directory or transition system.
`view` below is its only relationship to the logical lifecycle authority. -/
inductive LifecycleImage (registry : TypeRegistry Digest) where
  | fresh
  | retired
  | live (cell : PackedCell registry)

namespace LifecycleImage

variable (registry : TypeRegistry Digest)

def bytes : LifecycleImage registry -> List UInt8
  | .fresh => []
  | .retired => [68,82,2,0]
  | .live cell => [68,82,2,1] ++ PackedCell.bytes registry cell

def rawDecode : List UInt8 -> Option (LifecycleImage registry)
  | [] => some .fresh
  | [68,82,2,0] => some .retired
  | 68 :: 82 :: 2 :: 1 :: payload =>
      (PackedCell.decode registry payload).map LifecycleImage.live
  | _ => none

theorem rawDecode_bytes (image : LifecycleImage registry) :
    rawDecode registry (bytes registry image) = some image := by
  cases image with
  | fresh => rfl
  | retired => rfl
  | live cell => simp [bytes, rawDecode, PackedCell.decode_bytes]

def rawCodec : LawfulCodec (LifecycleImage registry) where
  encode := bytes registry
  decode := rawDecode registry
  decode_encode := rawDecode_bytes registry

def codec : LawfulCodec (LifecycleImage registry) := strictCodec (rawCodec registry)

theorem decode_encode (image : LifecycleImage registry) :
    (codec registry).decode ((codec registry).encode image) = some image :=
  (codec registry).decode_encode image

theorem decode_canonical {encoded : List UInt8} {image : LifecycleImage registry}
    (accepted : (codec registry).decode encoded = some image) :
    bytes registry image = encoded :=
  strictCodec_canonical (rawCodec registry) accepted

def view (directory : Directory Nat registry) (cellId : Nat) : LifecycleImage registry :=
  match directory.slots cellId with
  | .absent => if cellId ∈ directory.used then .retired else .fresh
  | .present cell => .live cell

def slot : LifecycleImage registry -> CellSlot registry
  | .fresh | .retired => .absent
  | .live cell => .present cell

def everUsed : LifecycleImage registry -> Bool
  | .fresh => false
  | .retired | .live _ => true

theorem view_slot (directory : Directory Nat registry) (cellId : Nat) :
    slot registry (view registry directory cellId) = directory.slots cellId := by
  unfold view
  cases current : directory.slots cellId with
  | absent => split_ifs <;> rfl
  | present cell => rfl

theorem view_used (directory : Directory Nat registry) (cellId : Nat) :
    everUsed registry (view registry directory cellId) = true ↔ cellId ∈ directory.used := by
  unfold view
  cases current : directory.slots cellId with
  | absent => by_cases used : cellId ∈ directory.used <;> simp [used, everUsed]
  | present cell => simp [everUsed, directory.present_used current]

theorem view_fresh_iff (directory : Directory Nat registry) (cellId : Nat) :
    view registry directory cellId = .fresh ↔
      directory.slots cellId = .absent ∧ cellId ∉ directory.used := by
  unfold view
  cases current : directory.slots cellId with
  | absent => by_cases used : cellId ∈ directory.used <;> simp [used]
  | present cell => simp

theorem view_live_iff (directory : Directory Nat registry) (cellId : Nat)
    (cell : PackedCell registry) :
    view registry directory cellId = .live cell ↔
      directory.slots cellId = .present cell := by
  unfold view
  cases current : directory.slots cellId with
  | absent => split_ifs <;> simp
  | present existing => simp

theorem view_insert (directory : Directory Nat registry) (cellId : Nat)
    (cell : PackedCell registry) :
    view registry (Directory.insert registry directory cellId cell) cellId = .live cell := by
  simp [view, Directory.insert]

theorem view_retire (directory : Directory Nat registry) (cellId : Nat)
    (used : cellId ∈ directory.used) :
    view registry (Directory.retire registry directory cellId) cellId = .retired := by
  simp [view, Directory.retire, used]

theorem accepted_fresh_before (before after : Directory Nat registry)
    (requests : List (CreateRequest (CellId := Nat) registry))
    (success : ResourceBirth.allocate registry before requests = .ok after)
    (request : CreateRequest (CellId := Nat) registry) (member : request ∈ requests) :
    view registry before request.cellId = .fresh := by
  apply (view_fresh_iff registry before request.cellId).mpr
  have fresh := ResourceBirth.allocate_success_fresh registry before after requests
    success request member
  refine ⟨?_, fresh⟩
  cases current : before.slots request.cellId with
  | absent => rfl
  | present cell => exact False.elim (fresh (before.present_used current))

theorem accepted_live_after (before after : Directory Nat registry)
    (requests : List (CreateRequest (CellId := Nat) registry))
    (success : ResourceBirth.allocate registry before requests = .ok after)
    (request : CreateRequest (CellId := Nat) registry) (member : request ∈ requests) :
    view registry after request.cellId = .live request.cell :=
  (view_live_iff registry after request.cellId request.cell).mpr
    (ResourceBirth.allocate_success_created registry before after requests success request member)

/-- Retired and never-used absence differ in bytes even if a digest collides. -/
theorem retired_bytes_ne_fresh :
    bytes registry .retired ≠ bytes registry .fresh := by simp [bytes]

end LifecycleImage

def rootCustomization : List UInt8 := "DREGG.CELL.LIFECYCLE/v1".toUTF8.toList

def rootBytes (bytes : List UInt8) : Digest :=
  (Sp800185Cshake256.hash rootCustomization bytes).digest

def physicalRoot {registry : TypeRegistry Digest} (image : LifecycleImage registry) : Digest :=
  rootBytes (LifecycleImage.bytes registry image)

theorem physicalRoot_exact {registry : TypeRegistry Digest} (image : LifecycleImage registry) :
    physicalRoot image = rootBytes ((LifecycleImage.codec registry).encode image) := rfl

theorem decoded_physicalRoot_exact {registry : TypeRegistry Digest}
    {bytes : List UInt8} {image : LifecycleImage registry}
    (accepted : (LifecycleImage.codec registry).decode bytes = some image) :
    physicalRoot image = rootBytes bytes := by
  unfold physicalRoot
  rw [LifecycleImage.decode_canonical registry accepted]

/-- The inner semantic root retains the exact native schema materializer.
It is deliberately not identified with the physical lifecycle root. -/
theorem native_payload_root_exact {registry : TypeRegistry Digest}
    (cell : PackedCell registry) :
    cell.payloadRoot =
      (registry.materializer cell.kind).rootBytes cell.payloadBytes := rfl

/-! ## Typed view of the actual lifecycle slot

This schema makes allocation visible in the same candidate tuple as authority
and resource changes. It represents the existing physical observation exactly:
an absent sparse field is fresh, a present `none` is retired, and a present
`some cell` is live. There is no fourth logical state and no new lifecycle
transition. In particular, these bytes already contain the outer envelope and
must not be packed into a second lifecycle envelope by the physical receiver.
-/

namespace LifecycleSlot

open CellState

variable (registry : TypeRegistry Digest)

def schema : CellState.Schema.{0, 0, 0, 0} where
  Field := Unit
  FieldType := fun _ => Option (PackedCell registry)
  Resource := Empty
  ResourceType := Empty.elim
  Authority := fun resource => nomatch resource
  Evidence := fun resource => nomatch resource

instance fieldDecidableEq : DecidableEq (schema registry).Field :=
  inferInstanceAs (DecidableEq Unit)

instance resourceDecidableEq : DecidableEq (schema registry).Resource :=
  fun resource => resource.elim

def state : LifecycleImage registry -> LogicalState (schema registry)
  | .fresh => { fields := 0, resources := fun resource => nomatch resource }
  | .retired =>
      { fields := (0 : FieldStore (schema registry)).write () none
        resources := fun resource => nomatch resource }
  | .live cell =>
      { fields := (0 : FieldStore (schema registry)).write () (some cell)
        resources := fun resource => nomatch resource }

def image (logical : LogicalState (schema registry)) : LifecycleImage registry :=
  match logical.fields () with
  | none => .fresh
  | some none => .retired
  | some (some cell) => .live cell

@[simp] theorem image_state (observation : LifecycleImage registry) :
    image registry (state registry observation) = observation := by
  cases observation <;> simp [image, state]

theorem state_image (logical : LogicalState (schema registry)) :
    state registry (image registry logical) = logical := by
  cases logical with
  | mk fields resources =>
      have resourcesExact : resources = fun resource => nomatch resource := by
        funext resource
        exact Empty.elim resource
      cases present : fields () with
      | none =>
          have fieldsExact : fields = (0 : FieldStore (schema registry)) := by
            apply DFinsupp.ext
            intro field
            cases field
            simpa using present
          rw [fieldsExact, resourcesExact]
          rfl
      | some value =>
          have fieldsExact : fields =
              (0 : FieldStore (schema registry)).write () value := by
            apply DFinsupp.ext
            intro field
            cases field
            simp [present]
          rw [fieldsExact, resourcesExact]
          cases value <;> simp [image, state]

def codec : LawfulCodec (LogicalState (schema registry)) where
  encode logical := LifecycleImage.bytes registry (image registry logical)
  decode bytes := ((LifecycleImage.codec registry).decode bytes).map (state registry)
  decode_encode := by
    intro logical
    have decoded := LifecycleImage.decode_encode registry (image registry logical)
    simpa [LifecycleImage.codec, strictCodec, LifecycleImage.rawCodec,
      state_image registry logical] using congrArg (Option.map (state registry)) decoded

theorem decode_canonical {bytes : List UInt8}
    {logical : LogicalState (schema registry)}
    (decoded : (codec registry).decode bytes = some logical) :
    (codec registry).encode logical = bytes := by
  obtain ⟨observation, observed, same⟩ := Option.map_eq_some_iff.mp decoded
  cases same
  simpa [codec] using LifecycleImage.decode_canonical registry observed

def materializer : Materializer (schema registry) Digest where
  codec := codec registry
  rootBytes := ResourceBirthCodec.rootBytes

def cell (observation : LifecycleImage registry) : Materialized (materializer registry) :=
  materialize (materializer registry) (state registry observation)

theorem bytes_exact (observation : LifecycleImage registry) :
    (cell registry observation).bytes = LifecycleImage.bytes registry observation := by
  simp [cell, materialize, Materialized.bytes, materializer, codec]

theorem root_exact (observation : LifecycleImage registry) :
    (cell registry observation).root = physicalRoot observation := by
  change ResourceBirthCodec.rootBytes (cell registry observation).bytes = _
  rw [bytes_exact]
  rfl

theorem fresh_bytes : (cell registry .fresh).bytes = [] := bytes_exact registry .fresh

theorem live_bytes (payload : PackedCell registry) :
    (cell registry (.live payload)).bytes =
      [68,82,2,1] ++ PackedCell.bytes registry payload := bytes_exact registry (.live payload)

theorem observed_bytes (directory : Directory Nat registry) (identifier : Nat) :
    (cell registry (LifecycleImage.view registry directory identifier)).bytes =
      LifecycleImage.bytes registry (LifecycleImage.view registry directory identifier) :=
  bytes_exact registry _

end LifecycleSlot

/-! ## Reconstruct the existing Directory from finite current physical cells -/

namespace DirectoryImage

variable (registry : TypeRegistry Digest)

abbrev Rows := List (Nat × LifecycleImage registry)

private theorem lookup_member {rows : Rows registry} {id : Nat}
    {image : LifecycleImage registry} (found : rows.lookup id = some image) :
    (id, image) ∈ rows := by
  obtain ⟨left, right, same, _⟩ := List.lookup_eq_some_iff.mp found
  rw [same]
  simp

private theorem lookup_of_member {rows : Rows registry}
    (unique : (rows.map Prod.fst).Nodup) {id : Nat} {image : LifecycleImage registry}
    (member : (id, image) ∈ rows) : rows.lookup id = some image := by
  induction rows with
  | nil => simp at member
  | cons head rest induction =>
      rcases head with ⟨key, value⟩
      have pieces := List.nodup_cons.mp unique
      rcases List.mem_cons.mp member with same | inRest
      · cases same
        simp
      · have different : id ≠ key := by
          intro same
          apply pieces.1
          exact List.mem_map.mpr ⟨(id, image), inRest, same⟩
        have differentBool : (id == key) = false := by simp [different]
        simpa only [List.lookup_cons, differentBool] using induction pieces.2 inRest

def used (rows : Rows registry) : Finset Nat :=
  ((rows.filter fun row => LifecycleImage.everUsed registry row.2).map Prod.fst).toFinset

/-- This is the existing Directory constructor over decoded observations. No
allocation, retirement or resource operation is interpreted here. -/
def ofRows (rows : Rows registry) : Directory Nat registry where
  slots id := LifecycleImage.slot registry ((rows.lookup id).getD .fresh)
  used := used registry rows
  present_used := by
    intro id cell present
    cases found : rows.lookup id with
    | none => simp [found, LifecycleImage.slot] at present
    | some image =>
        cases image with
        | fresh => simp [found, LifecycleImage.slot] at present
        | retired => simp [found, LifecycleImage.slot] at present
        | live payload =>
            have member := lookup_member registry found
            simp only [used, List.mem_toFinset, List.mem_map]
            refine ⟨(id, .live payload), ?_, rfl⟩
            exact List.mem_filter.mpr ⟨member, rfl⟩

theorem ofRows_view (rows : Rows registry)
    (unique : (rows.map Prod.fst).Nodup) (id : Nat) :
    LifecycleImage.view registry (ofRows registry rows) id =
      (rows.lookup id).getD .fresh := by
  cases found : rows.lookup id with
  | none =>
      have unused : id ∉ used registry rows := by
        intro member
        obtain ⟨⟨key, image⟩, inFiltered, same⟩ := List.mem_map.mp
          (List.mem_toFinset.mp member)
        have inRows := (List.mem_filter.mp inFiltered).1
        have lookup := lookup_of_member registry unique inRows
        simp only at same
        subst key
        rw [found] at lookup
        contradiction
      simp [LifecycleImage.view, ofRows, found, LifecycleImage.slot, unused]
  | some image =>
      have member := lookup_member registry found
      have used_exact : id ∈ used registry rows ↔ LifecycleImage.everUsed registry image = true := by
        constructor
        · intro present
          obtain ⟨⟨key, other⟩, inFiltered, same⟩ := List.mem_map.mp
            (List.mem_toFinset.mp present)
          have inRows := (List.mem_filter.mp inFiltered).1
          have isUsed := (List.mem_filter.mp inFiltered).2
          have lookup := lookup_of_member registry unique inRows
          simp only at same
          subst key
          rw [found] at lookup
          cases Option.some.inj lookup
          exact isUsed
        · intro isUsed
          simp only [used, List.mem_toFinset, List.mem_map]
          exact ⟨(id, image), List.mem_filter.mpr ⟨member, isUsed⟩, rfl⟩
      cases image with
      | fresh =>
          have unused : id ∉ used registry rows := by simpa [LifecycleImage.everUsed] using used_exact
          simp [LifecycleImage.view, ofRows, found, LifecycleImage.slot, unused]
      | retired =>
          have wasUsed : id ∈ used registry rows := used_exact.mpr rfl
          simp [LifecycleImage.view, ofRows, found, LifecycleImage.slot, wasUsed]
      | live cell => simp [LifecycleImage.view, ofRows, found, LifecycleImage.slot]

def decodeRows : List (Nat × List UInt8) -> Option (Rows registry)
  | [] => some []
  | (identifier, bytes) :: rest => do
      let image ← (LifecycleImage.codec registry).decode bytes
      let tail ← decodeRows rest
      some ((identifier, image) :: tail)

theorem decodeRows_keys {input : List (Nat × List UInt8)} {rows : Rows registry}
    (decoded : decodeRows registry input = some rows) :
    rows.map Prod.fst = input.map Prod.fst := by
  induction input generalizing rows with
  | nil => simp [decodeRows] at decoded; subst rows; rfl
  | cons head rest induction =>
      rcases head with ⟨id, bytes⟩
      simp only [decodeRows, Option.bind_eq_bind, Option.bind_eq_some_iff] at decoded
      obtain ⟨image, _, tail, tailDecoded, same⟩ := decoded
      cases Option.some.inj same
      simp [induction tailDecoded]

theorem decodeRows_lookup {input : List (Nat × List UInt8)} {rows : Rows registry}
    (decoded : decodeRows registry input = some rows) (id : Nat) :
    LifecycleImage.bytes registry ((rows.lookup id).getD .fresh) =
      (input.lookup id).getD [] := by
  induction input generalizing rows with
  | nil => simp [decodeRows] at decoded; subst rows; rfl
  | cons head rest induction =>
      rcases head with ⟨key, bytes⟩
      simp only [decodeRows, Option.bind_eq_bind, Option.bind_eq_some_iff] at decoded
      obtain ⟨image, imageDecoded, tail, tailDecoded, same⟩ := decoded
      cases Option.some.inj same
      by_cases equal : id = key
      · subst id
        simpa using LifecycleImage.decode_canonical registry imageDecoded
      · have differentBool : (id == key) = false := by simp [equal]
        simpa only [List.lookup_cons, differentBool] using induction tailDecoded

/-- Complete finite current cells yield a typed directory only after every
envelope decodes and all identities are distinct. Explicit fresh rows stay
fresh; tombstones enter the permanent used set. -/
def decode (input : List (Nat × List UInt8)) : Option (Directory Nat registry) := do
  let rows ← decodeRows registry input
  if (rows.map Prod.fst).Nodup then some (ofRows registry rows) else none

theorem decode_exact {input : List (Nat × List UInt8)} {directory : Directory Nat registry}
    (decoded : decode registry input = some directory) (id : Nat) :
    LifecycleImage.bytes registry (LifecycleImage.view registry directory id) =
      (input.lookup id).getD [] := by
  simp only [decode, Option.bind_eq_bind, Option.bind_eq_some_iff] at decoded
  obtain ⟨rows, rowsDecoded, decoded⟩ := decoded
  split_ifs at decoded with unique
  · cases Option.some.inj decoded
    rw [ofRows_view registry rows unique id]
    exact decodeRows_lookup registry rowsDecoded id

end DirectoryImage

/-! ## Axiom accounting for the source and receiving laws -/

/-- info: 'Minidregg.Compiler.ResourceBirthCodec.descriptor_decode_encode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Compiler.ResourceBirthCodec.descriptor_decode_encode

/-- info: 'Minidregg.Compiler.ResourceBirthCodec.descriptor_decode_canonical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Compiler.ResourceBirthCodec.descriptor_decode_canonical

/-- info: 'Minidregg.Compiler.ResourceBirthCodec.descriptor_encode_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Compiler.ResourceBirthCodec.descriptor_encode_injective

/-- info: 'Minidregg.Compiler.ResourceBirthCodec.LifecycleImage.decode_encode' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Compiler.ResourceBirthCodec.LifecycleImage.decode_encode

/-- info: 'Minidregg.Compiler.ResourceBirthCodec.LifecycleImage.decode_canonical' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Compiler.ResourceBirthCodec.LifecycleImage.decode_canonical

/-- info: 'Minidregg.Compiler.ResourceBirthCodec.DirectoryImage.decode_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Compiler.ResourceBirthCodec.DirectoryImage.decode_exact

/-- info: 'Minidregg.Compiler.ResourceBirthCodec.LifecycleSlot.state_image' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Compiler.ResourceBirthCodec.LifecycleSlot.state_image

/-- info: 'Minidregg.Compiler.ResourceBirthCodec.LifecycleSlot.decode_canonical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Compiler.ResourceBirthCodec.LifecycleSlot.decode_canonical

/-- info: 'Minidregg.Compiler.ResourceBirthCodec.LifecycleSlot.bytes_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Compiler.ResourceBirthCodec.LifecycleSlot.bytes_exact

end Minidregg.Compiler.ResourceBirthCodec
