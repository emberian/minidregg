/-
# `Kernel/ScalarEffect.lean` — declared scalar actions as a registered effect

`scalarEffect` (code 0, JSON `scalar`): the guarded field actions of a declared cell (an object's
fields, a program's code), with the cell's blinding ratchet as the kernel's rotate.

* Its semantics is the root-free core of the scalar receiver, `DeclaredResourceScalar.prepareStore`
  (the role's cell law, the scoped admission of every action, every guard in sequence, field
  closure, the cell law at the post), after two refusals of its own: an account role
  (`accountRequiresBook`: an account's balances are the Book's) and an empty action list
  (`emptyActions`). It is given no schema version and no expected root: the header owns both.
* Its guards are reads (`guardFields`): the header refuses a capability the authority cell does
  not hold and one whose scope does not name every guarded field, before the schema version and
  the root, at every loaded store.
* Its member patch is the actions' own patch (`actionsPatch`), computed from the signed
  operation alone (`memberReadsStore := false`): a member whose view seals fields can still be
  shown the post of a write to the fields it names.
* Its faces: the request grammar's actions (`ResourceGrammarJson.action`), the inbox's action
  objects (`scalarToJson`), one line per action (`scalarDisplay`).
-/
module

public import Kernel.ResourceEffect
public import Kernel.ContentEffect
public import Kernel.ResourceGrammarJson
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
open Minidregg.Theory.DeclaredActionLowering (Action)
set_option autoImplicit false

/-! ## The guards' reads -/

/-- The state keys an action's guards read: `Action.ops` is one guarded set per key, and its
guard is the key's exact expected value (`guardedSet_enabled_iff`). -/
def guardKeys : Action → List EffectDeclaration.StateKey
  | .create key _ | .write key _ _ => [key]
  | .move source destination resource _ _ _ =>
      [.accountBalance source resource, .accountBalance destination resource]

/-- The fields the actions' guards read, as a capability's scope names them. -/
def scalarGuardFields (actions : List Action) : List CellField :=
  actions.flatMap fun action => (guardKeys action).map ResourceObservationAdmission.declaredField

/-! ## The semantics -/

/-- **The scalar semantics**: an account role and an empty action list are refused by name, then
the root-free core of the receiver. -/
def scalarSem (ctx : EffectCtx) (actions : List Action)
    (store : Store EffectDeclaration.effectLayout) :
    Except DeclaredResourceScalar.Reject (Patch EffectDeclaration.effectLayout) :=
  if ctx.kind = .account then .error .accountRequiresBook
  else if actions = [] then .error .emptyActions
  else DeclaredResourceScalar.prepareStore ctx.kind ctx.target actions store

/-- What an answered semantics says: an ordinary role, some action, and the core's answer. -/
theorem scalarSem_ok {ctx : EffectCtx} {actions : List Action}
    {store : Store EffectDeclaration.effectLayout} {ps : Patch EffectDeclaration.effectLayout}
    (ok : scalarSem ctx actions store = .ok ps) :
    ctx.kind ≠ .account ∧ actions ≠ [] ∧
      DeclaredResourceScalar.prepareStore ctx.kind ctx.target actions store = .ok ps := by
  unfold scalarSem at ok
  by_cases account : ctx.kind = .account
  · rw [if_pos account] at ok; cases ok
  rw [if_neg account] at ok
  by_cases empty : actions = []
  · rw [if_pos empty] at ok; cases ok
  rw [if_neg empty] at ok
  exact ⟨account, empty, ok⟩

/-- The converse: an ordinary role and some action leave the core. -/
theorem scalarSem_core {ctx : EffectCtx} {actions : List Action}
    (ordinary : ctx.kind ≠ .account) (some : actions ≠ [])
    (store : Store EffectDeclaration.effectLayout) :
    scalarSem ctx actions store =
      DeclaredResourceScalar.prepareStore ctx.kind ctx.target actions store := by
  unfold scalarSem
  rw [if_neg ordinary, if_neg some]

/-- A scalar refusal's name: its constructor with its argument (`guardRejected 0`,
`undeclaredField 3`), without the namespace. -/
def scalarRefusalName (reason : DeclaredResourceScalar.Reject) : String :=
  ((reprStr reason).splitOn ".").getLastD ""

/-- The fields the actions write: their patch's write footprint, classified. -/
def scalarFrame (actions : List Action) : Finset CellField :=
  (Patch.writeFootprint (DeclaredResourceScalar.actionsPatch actions)).image fun address =>
    ResourceObservationAdmission.declaredField address.2

/-- **The scalar actions' declaration.** Any role is selected (an account is refused by the
semantics, by name); schema version 1; the root is pinned; the rotate is the cell's blinding
ratchet at the admission height. -/
def scalarSpec : Revival.EffectSpec EffectCtx
    (Revival.storeSubstrate EffectDeclaration.effectLayout) (List Action)
    DeclaredResourceScalar.Reject where
  opStream := StreamCodec.list DeclaredResourceScalar.actionStream
  refusalName := scalarRefusalName
  accepts := fun _ => true
  version := 1
  sem := scalarSem
  rotate := fun ctx s => DeclaredEffectCell.blinding.patch s ctx.ambient.height
  rotated := fun (address : Address EffectDeclaration.effectLayout) =>
    match address.2 with
    | .blinding => true
    | _ => false
  field := fun (address : Address EffectDeclaration.effectLayout) =>
    ResourceObservationAdmission.declaredField address.2
  amount := fun _ value => value.getD 0
  frame := scalarFrame
  verb := fun kind _ => DeclaredResourceScalar.ordinaryVerb kind
  view := fun site _ before after => DeclaredResourceProjection.project site.target before after

/-- The ratchet's address is the rotated one. -/
theorem scalar_rotated_blinding :
    scalarSpec.rotated DeclaredEffectCell.blinding.address = true := rfl

/-- An address the declaration does not mark rotated is not the ratchet's. -/
theorem scalar_unrotated_ne {address : Address EffectDeclaration.effectLayout}
    (unrotated : scalarSpec.rotated address = false) :
    address ≠ DeclaredEffectCell.blinding.address := by
  intro same
  subst same
  rw [scalar_rotated_blinding] at unrotated
  cases unrotated

open Minidregg.Effects.Revival in
/-- **The scalar declaration is complete**: every admitted action list writes only the fields of
its own patch, and its descriptor (with the ratchet) replays at every height. -/
theorem scalarSpec_complete : scalarSpec.Complete := by
  intro ctx actions s ps emitted
  change scalarSem ctx actions s = .ok ps at emitted
  obtain ⟨_, _, core⟩ := scalarSem_ok emitted
  have same := (DeclaredResourceScalar.prepareStore_ok core).1
  subst same
  refine ⟨?_, ?_⟩
  · intro loc member unrotated
    obtain ⟨op, inside, written⟩ := store_footprint_mem _ loc member
    rcases List.mem_append.mp inside with inside | inside
    · exact Finset.mem_image.mpr
        ⟨loc, (Patch.mem_writeFootprint_iff _ _).2 ⟨op, inside, written⟩, rfl⟩
    · change op ∈ DeclaredEffectCell.blinding.patch s ctx.ambient.height at inside
      unfold StoreCodec.Blinding.patch at inside
      split at inside
      · rw [List.mem_singleton] at inside
        subst inside
        exact absurd (Option.some.inj written).symm (scalar_unrotated_ne unrotated)
      · simp at inside
  · change ((storeSubstrate EffectDeclaration.effectLayout).run s
        (DeclaredResourceScalar.actionsPatch actions ++
          DeclaredEffectCell.blinding.patch s ctx.ambient.height)).isSome = true
    rw [store_run_validFrom (L := EffectDeclaration.effectLayout) _ _
      (DeclaredResourceScalar.prepareStore_ratchet_valid core ctx.ambient.height)]
    rfl

/-- A scalar write is never authorized as an observation. -/
theorem scalarSpec_writes (kind : ResourceKind) (actions : List Action) :
    observes (scalarSpec.verb kind actions) = false := by
  cases kind <;> rfl

/-! ## The faces -/

/-- A state key as an inbox shows it. -/
def scalarKeyJson : EffectDeclaration.StateKey → Lean.Json
  | .objectField resource field => .mkObj
      [("type", .str "object"), ("resource", EffectJson.decimal resource.value),
       ("field", EffectJson.decimal field.value)]
  | .accountBalance account resource => .mkObj
      [("type", .str "account"), ("resource", EffectJson.decimal account.value),
       ("field", EffectJson.decimal resource.value)]
  | .blinding => .mkObj [("type", .str "blinding")]
  | .programCode program => .mkObj
      [("type", .str "program"), ("resource", EffectJson.decimal program.value)]
  | .fieldDeclared object field => .mkObj
      [("type", .str "declared"), ("resource", EffectJson.decimal object.value),
       ("declares", EffectJson.decimal field.value)]
  | .fieldsOpen object => .mkObj
      [("type", .str "open"), ("resource", EffectJson.decimal object.value)]
  | .fieldsFrom object => .mkObj
      [("type", .str "from"), ("resource", EffectJson.decimal object.value)]

/-- One action as an inbox shows it. -/
def scalarActionJson : Action → Lean.Json
  | .create key value => .mkObj
      [("type", .str "create"), ("key", scalarKeyJson key),
       ("value", EffectJson.signedDecimal value)]
  | .write key before after => .mkObj
      [("type", .str "write"), ("key", scalarKeyJson key),
       ("expected", (before.map EffectJson.signedDecimal).getD .null),
       ("replacement", EffectJson.signedDecimal after)]
  | .move source destination resource expectedSource expectedDestination amount => .mkObj
      [("type", .str "move"), ("source", EffectJson.decimal source.value),
       ("destination", EffectJson.decimal destination.value),
       ("resource", EffectJson.decimal resource.value),
       ("expectedSource", (expectedSource.map EffectJson.signedDecimal).getD .null),
       ("expectedDestination", (expectedDestination.map EffectJson.signedDecimal).getD .null),
       ("amount", EffectJson.signedDecimal amount)]

/-- What an inbox shows of signed scalar actions: each action, whole. -/
def scalarToJson (actions : List Action) : List (String × Lean.Json) :=
  [("actions", .arr (actions.toArray.map scalarActionJson))]

/-- The JSON face: `{"type": "scalar", "actions": […]}`, the request grammar's actions. -/
def scalarOfJson (path : String) (json : Lean.Json) : Except String (List Action) := do
  let obj ← EffectJson.exactObject path ["type", "actions"] json
  EffectJson.list (path ++ ".actions") ResourceGrammarJson.action
    (← EffectJson.field path "actions" obj)

/-- One action in words, as a member is shown it before signing and as `mini inspect` prints it. -/
def scalarActionText : Action → String
  | .create (.objectField _ f) v => s!"create field {f.value} = {v}"
  | .create key v => s!"create {repr key} = {v}"
  | .write (.objectField _ f) e v =>
      s!"write field {f.value} := {v} (expected {e.map toString |>.getD "absent"})"
  | .write key _ v => s!"write {repr key} := {v}"
  | .move src dst _ _ _ amount => s!"move {amount} from {src.value} to {dst.value}"

def scalarDisplay (actions : List Action) : List String := actions.map scalarActionText

/-- One action as a field write of the command's `i`-th target, when it is one. -/
def actionWrite (i target : Nat) : Action → Option Eval.FieldWrite
  | .write (.objectField object field) _ value =>
      if object.value = target then some ⟨i, field.value, value⟩ else none
  | .create (.objectField object field) value =>
      if object.value = target then some ⟨i, field.value, value⟩ else none
  | _ => none

/-! ## The declaration, as the registry binds it -/

/-- **Scalar actions, as the registry binds them** (code 0, JSON `scalar`). -/
def scalarEffect : Effect where
  name := "scalar"
  L := EffectDeclaration.effectLayout
  wire := DeclaredEffectCell.wire
  O := List Action
  R := DeclaredResourceScalar.Reject
  decO := inferInstance
  spec := scalarSpec
  pack := DeclaredResourceScalar.packDeclared
  unpack := unpackDeclared
  toJson := scalarToJson
  ofJson := scalarOfJson
  display := scalarDisplay
  guardFields := fun actions => some (scalarGuardFields actions)
  viewDemand := fun want leads site _ before after =>
    DeclaredResourceProjection.projectDemand want leads site.target before after
  viewDemand_eq := fun want leads sound site _ before after =>
    DeclaredResourceProjection.projectDemand_eq want leads sound site.target before after
  member := some fun _ actions _ => some (DeclaredResourceScalar.actionsPatch actions)
  memberReadsStore := false
  member_exact := by
    intro f stated ctx actions s ps patch answered sem
    cases stated
    cases answered
    exact (DeclaredResourceScalar.prepareStore_ok (scalarSem_ok sem).2.2).1
  member_tail := by
    intro f _ ctx s store address unrotated
    exact DeclaredEffectCell.blinding.run_patch_frame store s ctx.ambient.height address
      (scalar_unrotated_ne unrotated)
  member_blind := by
    intro _ f stated ctx actions left right
    cases stated
    rfl
  runWrites := some fun _ _ index target _ actions => actions.mapM (actionWrite index target)
  authors := fun actions => !actions.isEmpty
  unpack_pack := unpackDeclared_pack
  pack_unpack := packDeclared_unpack
  observes_silent := by
    intro ctx actions s ps observed _
    rw [scalarSpec_writes] at observed
    cases observed
  complete := scalarSpec_complete
  view_unjoint := fun site _ before after =>
    JointSlots.scalarSlots_unjoint (DeclaredResourceProjection.values site.target before)
      (DeclaredResourceProjection.values site.target after)

/-- **The member patch is complete.** Whenever the semantics admits the actions, the member
patch answers the very patch it emits, at every store and under every context: it is never
vacuously safe by answering nothing. -/
theorem scalar_member_complete (ctx : EffectCtx) (actions : List Action)
    (s : Store EffectDeclaration.effectLayout) (ps : Patch EffectDeclaration.effectLayout)
    (admitted : scalarSpec.sem ctx actions s = .ok ps) :
    scalarEffect.memberPatch ctx.signed actions s = .ok ps := by
  have same := (DeclaredResourceScalar.prepareStore_ok (scalarSem_ok admitted).2.2).1
  subst same
  rfl

open Minidregg.Effects.Revival in
/-- What the controller runs where the semantics answers and the descriptor is valid: its replay. -/
theorem Effect.run_ok (e : Effect) {code : Nat} {ctx : EffectCtx} {op : e.O} {s : Store e.L}
    {ps : Patch e.L} (sem : e.spec.sem ctx op s = .ok ps)
    (valid : Patch.ValidFrom s (ps ++ e.rotate ctx s)) :
    e.run code ctx op s = .ok (Patch.run s (ps ++ e.rotate ctx s)) := by
  have replayed := store_run_validFrom (L := e.L) _ _ valid
  unfold Effect.run
  rw [sem]
  dsimp only
  split
  · rename_i ran
    cases replayed.symm.trans ran
  · rename_i post ran
    cases replayed.symm.trans ran
    rfl

/-- What the controller runs where the semantics refuses: the refusal under its declared name. -/
theorem Effect.run_refused (e : Effect) {code : Nat} {ctx : EffectCtx} {op : e.O} {s : Store e.L}
    {r : e.R} (sem : e.spec.sem ctx op s = .error r) :
    e.run code ctx op s = .error (.refused code (e.spec.refusalName r) (e.spec.refusalDetail r)) := by
  unfold Effect.run
  rw [sem]

set_option backward.isDefEq.respectTransparency false in
/-- What the controller runs for scalar actions: a refusal under the declaration's name, or the
answered patch replayed with the blinding ratchet at the admission height. -/
theorem scalar_run (code : Nat) (ctx : EffectCtx) (actions : List Action)
    (store : Store EffectDeclaration.effectLayout) :
    scalarEffect.run code ctx actions store =
      match scalarSem ctx actions store with
      | .error reason => .error (.refused code (scalarRefusalName reason) .empty)
      | .ok patch => .ok (Patch.run store
          (patch ++ DeclaredEffectCell.blinding.patch store ctx.ambient.height)) := by
  cases sem : scalarSem ctx actions store with
  | error reason =>
    exact scalarEffect.run_refused (show scalarEffect.spec.sem ctx actions store = .error reason from sem)
  | ok patch =>
    exact scalarEffect.run_ok (show scalarEffect.spec.sem ctx actions store = .ok patch from sem)
      (DeclaredResourceScalar.prepareStore_ratchet_valid (scalarSem_ok sem).2.2 ctx.ambient.height)

/-- A scalar write pins its root and is never observe-only. -/
theorem scalar_pinned (actions : List Action) : scalarSpec.commutes actions = false := rfl

theorem scalar_not_observeOnly (actions : List Action) :
    scalarEffect.observeOnly actions = false := rfl

/-- The header's scope gate for scalar actions, in the guards' own terms: the capability is
held and its scope names the field of every key a guard reads. -/
theorem scalar_scopeRefusal (code : Nat) (ctx : EffectCtx) (actions : List Action) :
    scalarEffect.scopeRefusal code ctx actions =
      match CredentialAuthorityState.readCapability ctx.snapshot.cell ctx.kind ctx.capability with
      | none => some (.capabilityRejected code)
      | some stored =>
          if actions.all fun action => (guardKeys action).all fun key =>
              decide (CellField.NamedBy stored.head.scope.fields
                (ResourceObservationAdmission.declaredField key))
          then none else some (.fieldNotNamed code) := by
  unfold Effect.scopeRefusal
  rw [show scalarEffect.guardFields actions = some (scalarGuardFields actions) from rfl]
  dsimp only
  cases CredentialAuthorityState.readCapability ctx.snapshot.cell ctx.kind ctx.capability with
  | none => rfl
  | some stored =>
    dsimp only
    have same : ((scalarGuardFields actions).all fun field =>
          decide (CellField.NamedBy stored.head.scope.fields field)) =
        actions.all fun action => (guardKeys action).all fun key =>
          decide (CellField.NamedBy stored.head.scope.fields
            (ResourceObservationAdmission.declaredField key)) := by
      unfold scalarGuardFields
      rw [List.all_flatMap]
      congr 1
      funext action
      rw [List.all_map]
      rfl
    rw [same]

#assert_axioms scalarSpec_complete scalarSpec_writes scalar_member_complete scalar_scopeRefusal
#assert_axioms scalar_run

end Minidregg.Kernel.DeclaredResourceController
