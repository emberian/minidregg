/-
# Theory.CellSlot -- stable heterogeneous cell identity and lifecycle

`CellState` describes the state *inside* one already-existing cell.  This
module supplies the missing outer boundary: a stable registry of heterogeneous
cell schemas, an absent/present slot for each identifier, and exact logical
create/delete transitions.

The registry does not use `Dynamic`, `unsafeCast`, or an untyped payload.  A
decoded kind tag selects the exact `CellState.Schema`; only then can its lawful
logical-state codec decode the payload.  The stored `PackedCell` therefore
contains a genuinely materialized value of that selected schema.

Deleting a cell does not make its identifier fresh again.  `Directory.used` is
monotone, while `Directory.slots` may move from present back to absent.  This
separation rejects both duplicate creation and delete-then-recreate attacks.

Roots are projections of canonical slot bytes.  No collision-resistance claim
is built in: `RootBindingPremise` is the explicit optional deployment premise.
Likewise the transitions below are logical transitions only;
`PersistenceRefinement` states the separate obligation of a durable handler.
-/
import Theory.CausalVersionDag
import Theory.CellState
import Theory.DeclaredTurn
import Theory.Hyperdocument

namespace Minidregg.Theory.CellRegistry

open CellState
open CausalVersionDag
open IndexedProgram

set_option autoImplicit false

universe uRoot uCell uPhysical uError

/-! ## Stable schema registry and dependent envelope -/

/-- A deployment registry for heterogeneous cell kinds.

Every kind has a stable one-byte wire tag, a public schema identity/version,
an exact `CellState.Schema`, and the materializer for that schema.  The reverse
tag law prevents aliases.  The registry supplies codecs; this module never
manufactures one from countability or choice. -/
structure TypeRegistry (Root : Type uRoot) where
  Kind : Type
  tag : Kind -> UInt8
  kindAtTag : UInt8 -> Option Kind
  kindAtTag_tag : forall kind, kindAtTag (tag kind) = some kind
  schemaRef : Kind -> SchemaRef
  schemaRef_injective : Function.Injective schemaRef
  schema : Kind -> CellState.Schema.{0, 0, 0, 0}
  materializer : (kind : Kind) -> CellState.Materializer (schema kind) Root
  rootBytes : List UInt8 -> Root

/-! ### The currently deployed Theory-side schema family -/

/-- Stable constructors for the three heterogeneous Theory-side cell schemas
which have crossed the sparse-materializer boundary.  Adding a constructor is
a wire-format and migration decision, not a runtime registration side effect. -/
inductive DeployedKind where
  | declaredEffect
  | credentialAuthority
  | hyperdocument
  deriving DecidableEq, Repr

def DeployedKind.tag : DeployedKind -> UInt8
  | .declaredEffect => 1
  | .credentialAuthority => 2
  | .hyperdocument => 3

def deployedKindAtTag : UInt8 -> Option DeployedKind
  | 1 => some .declaredEffect
  | 2 => some .credentialAuthority
  | 3 => some .hyperdocument
  | _ => none

@[simp] theorem deployedKindAtTag_tag (kind : DeployedKind) :
    deployedKindAtTag kind.tag = some kind := by
  cases kind <;> rfl

/-- The dependent schema selected by each stable deployed kind. -/
def deployedSchema : DeployedKind -> CellState.Schema.{0, 0, 0, 0}
  | .declaredEffect => DeclaredTurn.effectSchema
  | .credentialAuthority => CredentialAuthorityState.schema
  | .hyperdocument => Hyperdocument.cellSchema

/-- Deployment must provide concrete materializers and stable schema refs for
all deployed kinds.  In particular, this contract does not import or reuse the
non-cryptographic `codecOfCountable` carrier-inhabitation witness. -/
structure DeployedRegistryConfig (Root : Type uRoot) where
  schemaRef : DeployedKind -> SchemaRef
  schemaRef_injective : Function.Injective schemaRef
  materializer : (kind : DeployedKind) ->
    CellState.Materializer (deployedSchema kind) Root
  rootBytes : List UInt8 -> Root

/-- Realize the deployed heterogeneous family as the generic stable registry. -/
def deployedRegistry {Root : Type uRoot}
    (config : DeployedRegistryConfig Root) : TypeRegistry Root where
  Kind := DeployedKind
  tag := DeployedKind.tag
  kindAtTag := deployedKindAtTag
  kindAtTag_tag := deployedKindAtTag_tag
  schemaRef := config.schemaRef
  schemaRef_injective := config.schemaRef_injective
  schema := deployedSchema
  materializer := config.materializer
  rootBytes := config.rootBytes

/-- A type-safe heterogeneous cell.  Its tag chooses its schema before the
materialized payload can even be typed. -/
structure PackedCell {Root : Type uRoot} (registry : TypeRegistry Root) where
  kind : registry.Kind
  payload : CellState.Materialized (registry.materializer kind)

namespace PackedCell

variable {Root : Type uRoot} (registry : TypeRegistry Root)

/-- The stable envelope binds the Dregg marker, envelope version, registry tag,
and exact canonical bytes of the selected materialized payload. -/
def bytes (cell : PackedCell registry) : List UInt8 :=
  [68, 82, 1, registry.tag cell.kind] ++
    (registry.materializer cell.kind).codec.encode cell.payload.logical

/-- Decode without a runtime cast: matching `kindAtTag` refines the payload
type to the exact schema selected by that kind. -/
def decode : List UInt8 -> Option (PackedCell registry)
  | 68 :: 82 :: 1 :: tag :: payloadBytes =>
      match registry.kindAtTag tag with
      | none => none
      | some kind =>
          ((registry.materializer kind).codec.decode payloadBytes).map
            (fun logical =>
              { kind := kind
                payload := CellState.materialize (registry.materializer kind) logical })
  | _ => none

@[simp] theorem decode_bytes (cell : PackedCell registry) :
    decode registry (bytes registry cell) = some cell := by
  rcases cell with ⟨kind, payload⟩
  change (match registry.kindAtTag (registry.tag kind) with
    | none => none
    | some decodedKind =>
        ((registry.materializer decodedKind).codec.decode
          ((registry.materializer kind).codec.encode payload.logical)).map
          (fun logical =>
            PackedCell.mk decodedKind
              (CellState.materialize
                (registry.materializer decodedKind) logical))) =
      some (PackedCell.mk kind payload)
  rw [registry.kindAtTag_tag]
  change ((registry.materializer kind).codec.decode
      ((registry.materializer kind).codec.encode payload.logical)).map
        (fun logical => PackedCell.mk kind
          (CellState.materialize (registry.materializer kind) logical)) =
    some (PackedCell.mk kind payload)
  rw [(registry.materializer kind).codec.decode_encode]
  simp only [Option.map_some, Option.some.injEq]
  apply congrArg (PackedCell.mk kind)
  exact CellState.Materialized.ext rfl

/-- The envelope itself has a lawful codec.  Its decoder is dependent rather
than cast-based. -/
def codec : LawfulCodec (PackedCell registry) where
  encode := bytes registry
  decode := decode registry
  decode_encode := decode_bytes registry

/-- Native payload bytes remain observable separately from the stable outer
envelope. -/
def payloadBytes (cell : PackedCell registry) : List UInt8 :=
  cell.payload.bytes

/-- The native schema materializer's root.  The directory root below instead
binds the stable outer kind/version envelope as well. -/
def payloadRoot (cell : PackedCell registry) : Root :=
  cell.payload.root

@[simp] theorem bytes_exact (cell : PackedCell registry) :
    (codec registry).encode cell =
      [68, 82, 1, registry.tag cell.kind] ++ cell.payload.bytes :=
  rfl

end PackedCell

/-! ## Absent/present slots and canonical roots -/

/-- A registry slot has exactly two logical states.  Retirement is not a third
payload state; identifier non-reuse lives in `Directory.used`. -/
inductive CellSlot {Root : Type uRoot} (registry : TypeRegistry Root) where
  | absent
  | present (cell : PackedCell registry)

namespace CellSlot

variable {Root : Type uRoot} (registry : TypeRegistry Root)

/-- Canonical bytes distinguish absence from presence before the packed-cell
envelope. -/
def bytes : CellSlot registry -> List UInt8
  | .absent => [68, 82, 1, 0]
  | .present cell => [68, 82, 1, 1] ++ (PackedCell.codec registry).encode cell

def decode : List UInt8 -> Option (CellSlot registry)
  | [68, 82, 1, 0] => some .absent
  | 68 :: 82 :: 1 :: 1 :: packedBytes =>
      ((PackedCell.codec registry).decode packedBytes).map CellSlot.present
  | _ => none

@[simp] theorem decode_bytes (slot : CellSlot registry) :
    decode registry (bytes registry slot) = some slot := by
  cases slot with
  | absent => rfl
  | present cell =>
      simp [bytes, decode, PackedCell.codec]

def codec : LawfulCodec (CellSlot registry) where
  encode := bytes registry
  decode := decode registry
  decode_encode := decode_bytes registry

/-- The one logical slot root, computed from exact canonical slot bytes. -/
def root (slot : CellSlot registry) : Root :=
  registry.rootBytes ((codec registry).encode slot)

@[simp] theorem root_encoding_coherent (slot : CellSlot registry) :
    root registry slot = registry.rootBytes ((codec registry).encode slot) :=
  rfl

end CellSlot

/-- Digest collision resistance or ideal binding is an explicit deployment
premise.  None of the lifecycle admission rules below assumes it: freshness is
checked from the actual slot and monotone allocation set. -/
structure RootBindingPremise {Root : Type uRoot}
    (registry : TypeRegistry Root) : Prop where
  reflectsSlotEquality : forall {left right : CellSlot registry},
    CellSlot.root registry left = CellSlot.root registry right -> left = right

/-! ## Monotone identifier directory -/

/-- `used` records every identifier ever allocated.  Present cells must be in
that set; absent used identifiers are retired and cannot be resurrected. -/
structure Directory (CellId : Type uCell) [DecidableEq CellId]
    {Root : Type uRoot} (registry : TypeRegistry Root) where
  slots : CellId -> CellSlot registry
  used : Finset CellId
  present_used : forall {cellId cell},
    slots cellId = .present cell -> cellId ∈ used

namespace Directory

variable {Root : Type uRoot} {CellId : Type uCell} [DecidableEq CellId]
variable (registry : TypeRegistry Root)

/-- A genuinely fresh empty directory. -/
def empty : Directory CellId registry where
  slots := fun _ => .absent
  used := ∅
  present_used := by simp

@[simp] theorem empty_slot (cellId : CellId) :
    (empty registry : Directory CellId registry).slots cellId = .absent :=
  rfl

@[simp] theorem empty_unused (cellId : CellId) :
    cellId ∉ (empty registry : Directory CellId registry).used := by
  simp [empty]

/-- Exact logical insertion.  Admission below is the only public operation
which should call it; this constructor exposes its post-state for proofs. -/
def insert (before : Directory CellId registry) (cellId : CellId)
    (cell : PackedCell registry) : Directory CellId registry where
  slots := Function.update before.slots cellId (.present cell)
  used := before.used ∪ {cellId}
  present_used := by
    intro other presentCell presentAt
    by_cases same : other = cellId
    · subst other
      simp
    · have oldPresent : before.slots other = .present presentCell := by
        simpa [Function.update, same] using presentAt
      exact Finset.mem_union_left {cellId} (before.present_used oldPresent)

/-- Exact logical deletion.  The slot becomes absent, while `used` is retained
unchanged. -/
def retire (before : Directory CellId registry) (cellId : CellId) :
    Directory CellId registry where
  slots := Function.update before.slots cellId .absent
  used := before.used
  present_used := by
    intro other presentCell presentAt
    by_cases same : other = cellId
    · subst other
      simp [Function.update] at presentAt
    · apply before.present_used
      simpa [Function.update, same] using presentAt

@[simp] theorem insert_slot (before : Directory CellId registry)
    (cellId : CellId) (cell : PackedCell registry) :
    (Directory.insert registry before cellId cell).slots cellId =
      CellSlot.present cell := by
  simp [Directory.insert]

theorem insert_slot_other (before : Directory CellId registry)
    {cellId other : CellId} (different : other ≠ cellId)
    (cell : PackedCell registry) :
    (Directory.insert registry before cellId cell).slots other = before.slots other := by
  simp [Directory.insert, Function.update, different]

@[simp] theorem insert_used (before : Directory CellId registry)
    (cellId : CellId) (cell : PackedCell registry) :
    cellId ∈ (Directory.insert registry before cellId cell).used := by
  simp [Directory.insert]

@[simp] theorem retire_slot (before : Directory CellId registry)
    (cellId : CellId) :
    (Directory.retire registry before cellId).slots cellId = CellSlot.absent := by
  simp [Directory.retire]

@[simp] theorem retire_used (before : Directory CellId registry)
    (cellId : CellId) :
    (Directory.retire registry before cellId).used = before.used :=
  rfl

theorem retire_slot_other (before : Directory CellId registry)
    {cellId other : CellId} (different : other ≠ cellId) :
    (Directory.retire registry before cellId).slots other = before.slots other := by
  simp [Directory.retire, Function.update, different]

end Directory

/-! ## Executable lifecycle admission -/

structure CreateRequest {Root : Type uRoot} {CellId : Type uCell}
    (registry : TypeRegistry Root) where
  cellId : CellId
  expectedPreRoot : Root
  cell : PackedCell registry

structure DeleteRequest {Root : Type uRoot} {CellId : Type uCell}
    (registry : TypeRegistry Root) where
  cellId : CellId
  expectedPreRoot : Root
  expectedSchema : SchemaRef

inductive RejectReason where
  | duplicateCreate
  | retiredIdentifier
  | stalePreRoot
  | missingCell
  | schemaMismatch
  deriving DecidableEq, Repr

variable {Root : Type uRoot} {CellId : Type uCell} [DecidableEq CellId]
variable (registry : TypeRegistry Root) [DecidableEq Root]

/-- Create checks actual absence, permanent freshness, and the exact absent-slot
pre-root.  Root equality alone is never used as evidence of absence. -/
def create (before : Directory CellId registry)
    (request : CreateRequest (CellId := CellId) registry) :
    Except RejectReason (Directory CellId registry) :=
  match before.slots request.cellId with
  | .present _ => .error .duplicateCreate
  | .absent =>
      if request.cellId ∈ before.used then
        .error .retiredIdentifier
      else if request.expectedPreRoot = CellSlot.root registry .absent then
        .ok (Directory.insert registry before request.cellId request.cell)
      else
        .error .stalePreRoot

/-- Delete binds both the stable schema identity and exact current slot root.
Successful deletion retires rather than frees the identifier. -/
def delete (before : Directory CellId registry)
    (request : DeleteRequest (CellId := CellId) registry) :
    Except RejectReason (Directory CellId registry) :=
  match before.slots request.cellId with
  | .absent => .error .missingCell
  | .present cell =>
      if registry.schemaRef cell.kind ≠ request.expectedSchema then
        .error .schemaMismatch
      else if request.expectedPreRoot = CellSlot.root registry (.present cell) then
        .ok (Directory.retire registry before request.cellId)
      else
        .error .stalePreRoot

/-! ## Positive laws and regression teeth -/

theorem create_of_fresh
    (before : Directory CellId registry)
    (request : CreateRequest (CellId := CellId) registry)
    (absent : before.slots request.cellId = .absent)
    (fresh : request.cellId ∉ before.used)
    (rootExact : request.expectedPreRoot = CellSlot.root registry .absent) :
    create registry before request =
      .ok (Directory.insert registry before request.cellId request.cell) := by
  simp [create, absent, fresh, rootExact]

theorem delete_of_exact
    (before : Directory CellId registry)
    (request : DeleteRequest (CellId := CellId) registry)
    (cell : PackedCell registry)
    (present : before.slots request.cellId = .present cell)
    (schemaExact : registry.schemaRef cell.kind = request.expectedSchema)
    (rootExact : request.expectedPreRoot =
      CellSlot.root registry (.present cell)) :
    delete registry before request =
      .ok (Directory.retire registry before request.cellId) := by
  simp [delete, present, schemaExact, rootExact]

/-- A second create never overwrites an existing heterogeneous payload. -/
theorem duplicate_create_rejected
    (before : Directory CellId registry)
    (request : CreateRequest (CellId := CellId) registry)
    (existing : PackedCell registry)
    (present : before.slots request.cellId = .present existing) :
    create registry before request = .error .duplicateCreate := by
  simp [create, present]

/-- A fresh absent slot with the wrong expected root fails closed. -/
theorem stale_create_rejected
    (before : Directory CellId registry)
    (request : CreateRequest (CellId := CellId) registry)
    (absent : before.slots request.cellId = .absent)
    (fresh : request.cellId ∉ before.used)
    (stale : request.expectedPreRoot ≠ CellSlot.root registry .absent) :
    create registry before request = .error .stalePreRoot := by
  have staleExact : request.expectedPreRoot ≠
      registry.rootBytes ((CellSlot.codec registry).encode CellSlot.absent) := by
    simpa [CellSlot.root] using stale
  simp [create, absent, fresh, staleExact]

/-- A delete with the correct schema but stale current root fails closed. -/
theorem stale_delete_rejected
    (before : Directory CellId registry)
    (request : DeleteRequest (CellId := CellId) registry)
    (cell : PackedCell registry)
    (present : before.slots request.cellId = .present cell)
    (schemaExact : registry.schemaRef cell.kind = request.expectedSchema)
    (stale : request.expectedPreRoot ≠
      CellSlot.root registry (.present cell)) :
    delete registry before request = .error .stalePreRoot := by
  have staleExact : request.expectedPreRoot ≠
      registry.rootBytes
        ((CellSlot.codec registry).encode (CellSlot.present cell)) := by
    simpa [CellSlot.root] using stale
  simp [delete, present, schemaExact, staleExact]

omit [DecidableEq Root] in
/-- Deletion cannot erase the permanent allocation bit. -/
theorem retired_identifier_remains_used
    (before : Directory CellId registry) (cellId : CellId)
    (used : cellId ∈ before.used) :
    cellId ∈ (Directory.retire registry before cellId).used := by
  simpa using used

/-- The central resurrection tooth: create, then retire, then attempt to create
under the same identifier.  Even though the slot is absent again, admission
returns `retiredIdentifier`. -/
theorem recreate_after_retire_rejected
    (before : Directory CellId registry)
    (first second : CreateRequest (CellId := CellId) registry)
    (sameId : second.cellId = first.cellId) :
    create registry
      (Directory.retire registry
        (Directory.insert registry before first.cellId first.cell) first.cellId)
      second = .error .retiredIdentifier := by
  let after := Directory.retire registry
    (Directory.insert registry before first.cellId first.cell) first.cellId
  change create registry after second = .error .retiredIdentifier
  have absent : after.slots second.cellId = CellSlot.absent := by
    rw [sameId]
    simp [after]
  have used : second.cellId ∈ after.used := by
    rw [sameId]
    simp [after, Directory.insert, Directory.retire]
  simp [create, absent, used]

omit [DecidableEq Root] in
/-- Exact insertion binds the post-root to the exact canonical bytes of the
new heterogeneous payload and its stable kind tag. -/
theorem inserted_root_exact
    (before : Directory CellId registry)
    (request : CreateRequest (CellId := CellId) registry) :
    CellSlot.root registry
        ((Directory.insert registry before request.cellId request.cell).slots
          request.cellId) =
      registry.rootBytes
        ((CellSlot.codec registry).encode (.present request.cell)) := by
  simp [CellSlot.root]

/-! ## Explicit physical refinement boundary -/

/-- A durable implementation must separately exhibit how physical installation
represents the exact logical directory post-state.  The logical semantics does
not claim that a root write fsyncs bytes, survives crashes, or installs an
index. -/
structure PersistenceRefinement
    (PhysicalState : Type uPhysical) (InstallError : Type uError)
    (registry : TypeRegistry Root) [DecidableEq CellId] where
  Represents : PhysicalState -> Directory CellId registry -> Prop
  install : PhysicalState -> Directory CellId registry ->
    Except InstallError PhysicalState
  install_refines : forall {physical before after physicalAfter},
    Represents physical before ->
    install physical after = .ok physicalAfter ->
    Represents physicalAfter after

/-! ## Axiom audit -/

/-- info: 'Minidregg.Theory.CellRegistry.PackedCell.decode_bytes' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms PackedCell.decode_bytes
/-- info: 'Minidregg.Theory.CellRegistry.CellSlot.decode_bytes' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms CellSlot.decode_bytes
/-- info: 'Minidregg.Theory.CellRegistry.duplicate_create_rejected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms duplicate_create_rejected
/-- info: 'Minidregg.Theory.CellRegistry.stale_create_rejected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms stale_create_rejected
/-- info: 'Minidregg.Theory.CellRegistry.stale_delete_rejected' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms stale_delete_rejected
/-- info: 'Minidregg.Theory.CellRegistry.recreate_after_retire_rejected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms recreate_after_retire_rejected

end Minidregg.Theory.CellRegistry
