/-
# `Kernel/ReadEffects.lean` — the two root-pinning reads, each ONE declaration

* `readEffect` (code 3, JSON `read`): an observe-only read of a content cell. A `transclude` of
  another target of the same command names this cell as its source; this read is where the
  admission checks the transcluder's grant and the source's own policy at this height, and its
  loaded state is what the opening is checked against.
* `kindReadEffect` (code 7, JSON `kindRead`): the whole authenticated world-kind definition,
  observe-only. A partial grant never receives it.

Neither has an operand: the operation type is `Unit` and its codec writes no byte, so the
payload is the tag octet alone. Neither commutes: the header refuses a moved root
(`staleTarget`), so the signer commits to the root it read, and thin consent displays these
from a checked served opening (`Kernel/NativeThinConsent.lean`), never view-less. Both emit the
empty patch and are authorized under the kind's observe verb.
-/
module

public import Kernel.ResourceEffect
public import Kernel.ContentEffect
public import Kernel.WorldPrototypeConstruction
public import Kernel.ResourceObservationAdmission

-- Bodies this file reduces or derives through, not exposed by their modules (module system).
import all Init.Data.Repr
import all Init.Data.ToString.Basic
import all Init.Data.ToString.Extra
import all Init.Data.Array.Basic
import all Init.Data.ByteArray.Basic
import all Init.Data.String.Decode
import all Init.Data.String.Defs
import all Init.Control.Except
import all Init.Data.List.Basic
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.String.Bootstrap
import all Init.Data.Format.Basic

@[expose] public section

namespace Minidregg.Kernel.DeclaredResourceController
open Minidregg.Compiler
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Effects
open Minidregg.Theory
open Minidregg.Theory.CellRegistry
open Minidregg.Theory.CellState
open Minidregg.Theory.Store
open Minidregg.Theory.TypedAuthorization
set_option autoImplicit false

/-- The JSON face of an operation without operand: the object holds `type` and nothing else. -/
def unitOfJson (path : String) (json : Lean.Json) : Except String Unit := do
  let _ ← EffectJson.exactObject path ["type"] json
  pure ()

/-! ## The content read -/

inductive ReadRefusal where
  /-- The target's capability is not its observe capability: a read's only authorization is
  its observation. -/
  | observationRequired
  deriving DecidableEq, Repr

def ReadRefusal.name : ReadRefusal → String
  | .observationRequired => "observationRequired"

def readSem (ctx : EffectCtx) (_ : Unit) (_ : Store Hyperdocument.layout) :
    Except ReadRefusal (Patch Hyperdocument.layout) :=
  if ctx.observe != some ctx.capability then .error .observationRequired else .ok []

theorem readSem_ok {ctx : EffectCtx} {op : Unit} {store : Store Hyperdocument.layout}
    {ps : Patch Hyperdocument.layout} (ok : readSem ctx op store = .ok ps) :
    ps = [] ∧ ctx.observe = some ctx.capability := by
  unfold readSem at ok
  split at ok
  · cases ok
  · rename_i same
    exact ⟨(Except.ok.inj ok).symm, by simpa only [bne_iff_ne, ne_eq, Decidable.not_not] using same⟩

/-- **The content read's declaration.** An object's content cell at the content schema version;
the root is pinned (it does not commute); no rotate, an empty frame; the law's view is the
content projection of the loaded cell under the empty command. -/
def readSpec : Revival.EffectSpec EffectCtx (Revival.storeSubstrate Hyperdocument.layout)
    Unit ReadRefusal where
  opStream := StoreCodec.unitStream
  refusalName := ReadRefusal.name
  accepts := fun kind => kind == .object
  version := ContentResource.commandVersion
  sem := readSem
  rotate := fun _ _ => []
  rotated := fun _ => false
  field := ResourceObservationAdmission.contentFieldAt
  amount := fun _ _ => 0
  frame := fun _ => ∅
  verb := fun kind _ => observeVerb kind
  view := fun _ _ before after => ContentResource.project before after ⟨[]⟩

/-- **The content read, as the registry binds it** (code 3, JSON `read`). -/
def readEffect : Effect where
  name := "read"
  L := Hyperdocument.layout
  wire := HyperdocumentCell.contentWire
  O := Unit
  R := ReadRefusal
  decO := inferInstance
  spec := readSpec
  pack := fun _ cell => ⟨.content, cell⟩
  unpack := fun _ packed =>
    match packed with
    | ⟨.content, value⟩ => some value
    | _ => none
  toJson := fun _ => []
  ofJson := unitOfJson
  display := fun _ => ["authenticated read; no resource write"]
  member := some fun _ _ _ => some []
  memberReadsStore := false
  member_exact := by
    intro f stated ctx op store ps patch answered sem
    cases stated
    cases answered
    exact (readSem_ok (show readSem ctx op store = .ok ps from sem)).1
  member_tail := fun _ _ _ _ _ _ _ => rfl
  member_blind := by
    intro _ f stated ctx op left right
    cases stated
    rfl
  viewDemand := fun want _ _ before after => ContentResource.projectDemand want before after ⟨[]⟩
  viewDemand_eq := fun want _ _ before after => ContentResource.projectDemand_eq want before after ⟨[]⟩
  unpack_pack := fun _ _ => rfl
  pack_unpack := by
    intro kind packed cell selected
    split at selected
    · cases selected; rfl
    · cases selected
  observes_silent := by
    intro ctx op store ps _ emitted
    unfold Revival.EffectSpec.emitted at emitted
    cases sem : readSem ctx op store with
    | error reason =>
        rw [show readSpec.sem ctx op store = readSem ctx op store from rfl, sem] at emitted
        cases emitted
    | ok descriptor =>
        rw [show readSpec.sem ctx op store = readSem ctx op store from rfl, sem] at emitted
        have empty := (readSem_ok sem).1
        subst empty
        exact (Except.ok.inj emitted).symm
  complete := by
    intro ctx op store ps ok
    have empty : ps = [] := (readSem_ok (show readSem ctx op store = .ok ps from ok)).1
    subst empty
    exact ⟨fun loc member => absurd member (Finset.notMem_empty loc), rfl⟩
  view_unjoint := fun _ _ before after => JointSlots.contentProject_unjoint before after ⟨[]⟩

theorem read_observeOnly (op : Unit) : readEffect.observeOnly op = true := rfl

/-- **The content read's member patch is complete**: wherever the semantics admits the read, the
member is shown exactly its patch (the empty one). The read pins its root at every operation. -/
theorem read_member_complete (ctx : EffectCtx) (op : Unit) (store : Store Hyperdocument.layout)
    (ps : Patch Hyperdocument.layout) (admitted : readEffect.spec.sem ctx op store = .ok ps) :
    readEffect.spec.commutes op = false ∧ readEffect.memberPatch ctx.signed op store = .ok ps := by
  have empty := (readSem_ok (show readSem ctx op store = .ok ps from admitted)).1
  subst empty
  exact ⟨rfl, rfl⟩

/-! ## The whole kind definition read -/

inductive KindReadRefusal where
  /-- The target's capability is not its observe capability. -/
  | observationRequired
  /-- The authority cell does not hold the observe capability. -/
  | observationRejected
  /-- The observe capability is a partial grant: the whole definition is not named by it, and
  a partial grant never receives canonical hidden defaults. -/
  | fieldNotNamed
  deriving DecidableEq, Repr

def KindReadRefusal.name : KindReadRefusal → String
  | .observationRequired => "observationRequired"
  | .observationRejected => "observationRejected"
  | .fieldNotNamed => "fieldNotNamed"

def kindReadSem (ctx : EffectCtx) (_ : Unit) (_ : Store WorldKindCell.definitionLayout) :
    Except KindReadRefusal (Patch WorldKindCell.definitionLayout) :=
  if ctx.observe != some ctx.capability then .error .observationRequired
  else
    match CredentialAuthorityState.readCapability ctx.snapshot.cell .object ctx.capability with
    | none => .error .observationRejected
    | some stored =>
        if stored.head.scope.fields.isSome then .error .fieldNotNamed else .ok []

/-- An admitted kind read emits nothing, names its observe capability, and that capability is
held whole (no field scope). -/
theorem kindReadSem_ok {ctx : EffectCtx} {op : Unit} {store : Store WorldKindCell.definitionLayout}
    {ps : Patch WorldKindCell.definitionLayout} (ok : kindReadSem ctx op store = .ok ps) :
    ps = [] ∧ ctx.observe = some ctx.capability ∧
      ∃ stored, CredentialAuthorityState.readCapability ctx.snapshot.cell .object ctx.capability =
          some stored ∧ stored.head.scope.fields = none := by
  unfold kindReadSem at ok
  split at ok
  · cases ok
  · rename_i same
    split at ok
    · cases ok
    · rename_i stored found
      split at ok
      · cases ok
      · rename_i whole
        exact ⟨(Except.ok.inj ok).symm,
          by simpa only [bne_iff_ne, ne_eq, Decidable.not_not] using same, stored, found,
          by simpa using whole⟩

/-- **The kind read's declaration.** An object's world-kind cell at schema version 1; the root
is pinned; no rotate, an empty frame; the law's view is the whole-definition projection of the
loaded cell. -/
def kindReadSpec : Revival.EffectSpec EffectCtx (Revival.storeSubstrate WorldKindCell.definitionLayout)
    Unit KindReadRefusal where
  opStream := StoreCodec.unitStream
  refusalName := KindReadRefusal.name
  accepts := fun kind => kind == .object
  version := 1
  sem := kindReadSem
  rotate := fun _ _ => []
  rotated := fun _ => false
  field := fun _ => .body
  amount := fun _ _ => 0
  frame := fun _ => ∅
  verb := fun kind _ => observeVerb kind
  view := fun _ _ before _ => WorldPrototypeConstruction.observeProject before

/-- **The whole kind definition read, as the registry binds it** (code 7, JSON `kindRead`). -/
def kindReadEffect : Effect where
  name := "kindRead"
  L := WorldKindCell.definitionLayout
  wire := WorldKindCell.definitionWire
  O := Unit
  R := KindReadRefusal
  decO := inferInstance
  spec := kindReadSpec
  pack := fun _ cell => ⟨.worldKind, cell⟩
  unpack := fun _ packed =>
    match packed with
    | ⟨.worldKind, value⟩ => some value
    | _ => none
  toJson := fun _ => []
  ofJson := unitOfJson
  display := fun _ => ["authenticated whole kind definition read; no resource write"]
  member := some fun _ _ _ => some []
  memberReadsStore := false
  member_exact := by
    intro f stated ctx op store ps patch answered sem
    cases stated
    cases answered
    exact (kindReadSem_ok (show kindReadSem ctx op store = .ok ps from sem)).1
  member_tail := fun _ _ _ _ _ _ _ => rfl
  member_blind := by
    intro _ f stated ctx op left right
    cases stated
    rfl
  unpack_pack := fun _ _ => rfl
  pack_unpack := by
    intro kind packed cell selected
    split at selected
    · cases selected; rfl
    · cases selected
  observes_silent := by
    intro ctx op store ps _ emitted
    unfold Revival.EffectSpec.emitted at emitted
    cases sem : kindReadSem ctx op store with
    | error reason =>
        rw [show kindReadSpec.sem ctx op store = kindReadSem ctx op store from rfl, sem] at emitted
        cases emitted
    | ok descriptor =>
        rw [show kindReadSpec.sem ctx op store = kindReadSem ctx op store from rfl, sem] at emitted
        have empty := (kindReadSem_ok sem).1
        subst empty
        exact (Except.ok.inj emitted).symm
  complete := by
    intro ctx op store ps ok
    have empty : ps = [] := (kindReadSem_ok (show kindReadSem ctx op store = .ok ps from ok)).1
    subst empty
    exact ⟨fun loc member => absurd member (Finset.notMem_empty loc), rfl⟩
  view_unjoint := fun _ _ before _ => WorldPrototypeConstruction.observeProject_unjoint before

theorem kindRead_observeOnly (op : Unit) : kindReadEffect.observeOnly op = true := rfl

/-- **The kind read's member patch is complete**: wherever the semantics admits the read, the
member is shown exactly its patch (the empty one). The read pins its root at every operation. -/
theorem kindRead_member_complete (ctx : EffectCtx) (op : Unit)
    (store : Store WorldKindCell.definitionLayout) (ps : Patch WorldKindCell.definitionLayout)
    (admitted : kindReadEffect.spec.sem ctx op store = .ok ps) :
    kindReadEffect.spec.commutes op = false ∧
      kindReadEffect.memberPatch ctx.signed op store = .ok ps := by
  have empty := (kindReadSem_ok (show kindReadSem ctx op store = .ok ps from admitted)).1
  subst empty
  exact ⟨rfl, rfl⟩

end Minidregg.Kernel.DeclaredResourceController
