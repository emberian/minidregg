/-
# `Kernel/WorldKindEffects.lean` — a world kind's definition revision and a world instance's actions, each ONE declaration

`kindDefinitionEffect` (code 5, JSON `kindDefinition`): replace a world-kind cell's definition by
its next revision. The operation is the whole next `WorldKindCell.Definition`; the wire bytes are
the tag octet 5 and `WorldKindCell.definitionStream`'s bytes, as the hand arm wrote them. The
semantics is `WorldKindCell.prepareDefinition` at the loaded store: one guarded write of the
definition address naming the definition it replaces, or the one refusal `notNextRevision` (no
stored definition, another kind, a revision that is not the next one, or a definition that does
not instantiate).

`worldEffect` (code 4, JSON `world`): a list of guarded field actions on a world instance. The
wire bytes are the tag octet 4 and the action list's bytes, as the hand arm wrote them. The
semantics is `WorldKindCell.preparePatch` at the loaded store, admitted when the patch applies
and the post decodes under the same descriptor; one refusal, `worldKind`. Three things about it
are not the default and are stated on the declaration: its semantic footprint (the inner
fields, `Effect.footprint`), what a run may claim of it (`Effect.runWrites`: its method's bound
outputs) and that an empty action list authors nothing (`Effect.authors`).

Each pins its root. The revision's patch reads the loaded store and nothing of the receiver (no authority
snapshot, no height), so the declaration states it as its member patch (`Effect.member`): thin
consent displays a revision from a served view that seals nothing.
-/
module

public import Kernel.ResourceEffect
public import Kernel.ContentEffect
public import Kernel.ResourceGrammarJson
public import Kernel.WorldKindProjection
public import Kernel.WorldKindMethods

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

/-! ## The kind definition revision -/

inductive KindDefinitionRefusal where
  /-- The cell holds no definition, or the signed one is not its next revision: another kind,
  a revision that is not the stored one plus one, or a definition that does not instantiate. -/
  | notNextRevision
  deriving DecidableEq, Repr

def KindDefinitionRefusal.name : KindDefinitionRefusal → String
  | .notNextRevision => "notNextRevision"

def kindDefinitionSem (_ : EffectCtx) (definition : WorldKindCell.Definition)
    (store : Store WorldKindCell.definitionLayout) :
    Except KindDefinitionRefusal (Patch WorldKindCell.definitionLayout) :=
  match WorldKindCell.prepareDefinition store definition with
  | some patch => .ok patch
  | none => .error .notNextRevision

/-- What a prepared revision is: one write of the definition address, guarded at the stored
definition. -/
theorem prepareDefinition_some {store : Store WorldKindCell.definitionLayout}
    {next : WorldKindCell.Definition} {patch : Patch WorldKindCell.definitionLayout}
    (prepared : WorldKindCell.prepareDefinition store next = some patch) :
    ∃ old, store WorldKindCell.definitionAddress = some old ∧ patch = [.write () () old next] := by
  unfold WorldKindCell.prepareDefinition at prepared
  cases stored : store WorldKindCell.definitionAddress with
  | none => simp [stored] at prepared
  | some old =>
    simp only [stored, Option.bind_eq_bind, Option.bind_some] at prepared
    split at prepared
    · exact ⟨old, rfl, (Option.some.inj prepared).symm⟩
    · cases prepared

/-- A prepared revision applies to the store it was prepared from. -/
theorem prepareDefinition_valid {store : Store WorldKindCell.definitionLayout}
    {next : WorldKindCell.Definition} {patch : Patch WorldKindCell.definitionLayout}
    (prepared : WorldKindCell.prepareDefinition store next = some patch) :
    Patch.ValidFrom store patch := by
  obtain ⟨old, stored, rfl⟩ := prepareDefinition_some prepared
  exact ⟨⟨rfl, stored⟩, trivial⟩

theorem kindDefinitionSem_ok {ctx : EffectCtx} {definition : WorldKindCell.Definition}
    {store : Store WorldKindCell.definitionLayout} {ps : Patch WorldKindCell.definitionLayout}
    (ok : kindDefinitionSem ctx definition store = .ok ps) :
    WorldKindCell.prepareDefinition store definition = some ps := by
  unfold kindDefinitionSem at ok
  split at ok
  · rename_i patch prepared
    rw [prepared, Except.ok.inj ok]
  · cases ok

/-- **The kind definition revision's declaration.** An object's world-kind cell at schema
version 1; the root is pinned; no rotate; every write is the body's; the authorization is the
kind's ordinary write; the law's view is the definition projection of the two states. -/
def kindDefinitionSpec : Revival.EffectSpec EffectCtx
    (Revival.storeSubstrate WorldKindCell.definitionLayout)
    WorldKindCell.Definition KindDefinitionRefusal where
  opStream := WorldKindCell.definitionStream
  refusalName := KindDefinitionRefusal.name
  accepts := fun kind => kind == .object
  version := 1
  sem := kindDefinitionSem
  rotate := fun _ _ => []
  rotated := fun _ => false
  field := fun _ => .body
  amount := fun _ _ => 0
  frame := fun _ => {.body}
  verb := fun kind _ => DeclaredResourceScalar.ordinaryVerb kind
  view := fun _ _ before after => WorldKindProjection.definitionProject before after

theorem ordinaryVerb_writes (kind : ResourceKind) :
    observes (DeclaredResourceScalar.ordinaryVerb kind) = false := by
  cases kind <;> rfl

/-- The JSON face: `{"type": "kindDefinition", "definition": …}`, the definition in the world
grammar (`ResourceGrammarJson.worldDefinition`). -/
def kindDefinitionOfJson (path : String) (json : Lean.Json) :
    Except String WorldKindCell.Definition := do
  let obj ← EffectJson.exactObject path ["type", "definition"] json
  ResourceGrammarJson.worldDefinition (path ++ ".definition")
    (← EffectJson.field path "definition" obj)

/-- What an inbox shows of a signed revision: its kind, its revision, and the definition's
canonical bytes. -/
def kindDefinitionToJson (definition : WorldKindCell.Definition) : List (String × Lean.Json) :=
  [("kind", EffectJson.decimal definition.descriptor.kind),
   ("revision", EffectJson.decimal definition.descriptor.revision),
   ("exactDefinitionHex",
     .str (ContentJson.encodeHex (WorldKindCell.definitionStream.encode definition)))]

/-- **The kind definition revision, as the registry binds it** (code 5, JSON `kindDefinition`). -/
def kindDefinitionEffect : Effect where
  name := "kindDefinition"
  L := WorldKindCell.definitionLayout
  wire := WorldKindCell.definitionWire
  O := WorldKindCell.Definition
  R := KindDefinitionRefusal
  decO := inferInstance
  spec := kindDefinitionSpec
  pack := fun _ cell => ⟨.worldKind, cell⟩
  unpack := fun _ packed =>
    match packed with
    | ⟨.worldKind, value⟩ => some value
    | _ => none
  toJson := kindDefinitionToJson
  ofJson := kindDefinitionOfJson
  display := fun definition =>
    [s!"kind {definition.descriptor.kind}: layout revision {definition.descriptor.revision}, {definition.descriptor.fields.length} semantic fields"]
  member := some fun _ definition store => WorldKindCell.prepareDefinition store definition
  member_exact := by
    intro f stated ctx definition store ps patch answered sem
    cases stated
    have prepared := kindDefinitionSem_ok (show kindDefinitionSem ctx definition store = .ok ps from sem)
    exact Option.some.inj (prepared.symm.trans answered)
  member_tail := fun _ _ _ _ _ _ _ => rfl
  unpack_pack := fun _ _ => rfl
  pack_unpack := by
    intro kind packed cell selected
    split at selected
    · cases selected; rfl
    · cases selected
  observes_silent := by
    intro ctx definition store ps observed _
    exact absurd ((ordinaryVerb_writes ctx.kind).symm.trans observed) Bool.false_ne_true
  complete := by
    intro ctx definition store ps ok
    have prepared := kindDefinitionSem_ok (show kindDefinitionSem ctx definition store = .ok ps from ok)
    refine ⟨fun loc _ _ => Finset.mem_singleton_self _, ?_⟩
    change ((Revival.storeSubstrate WorldKindCell.definitionLayout).run store (ps ++ [])).isSome
    rw [List.append_nil, Revival.store_run_validFrom ps store (prepareDefinition_valid prepared)]
    rfl
  view_unjoint := fun _ _ before after => WorldKindProjection.definitionProject_unjoint before after

/-- The semantics at a store where a revision is prepared. -/
theorem kindDefinitionSem_some {definition : WorldKindCell.Definition}
    {store : Store WorldKindCell.definitionLayout} {patch : Patch WorldKindCell.definitionLayout}
    (prepared : WorldKindCell.prepareDefinition store definition = some patch) (ctx : EffectCtx) :
    kindDefinitionEffect.spec.sem ctx definition store = .ok patch := by
  show kindDefinitionSem ctx definition store = _
  simp only [kindDefinitionSem, prepared]
  rfl

/-- The semantics at a store where none is prepared. -/
theorem kindDefinitionSem_none {definition : WorldKindCell.Definition}
    {store : Store WorldKindCell.definitionLayout}
    (prepared : WorldKindCell.prepareDefinition store definition = none) (ctx : EffectCtx) :
    kindDefinitionEffect.spec.sem ctx definition store = .error .notNextRevision := by
  show kindDefinitionSem ctx definition store = _
  simp only [kindDefinitionSem, prepared]
  rfl

/-- A patch that applies replays to its run: the revision has no rotate. -/
theorem kindDefinition_replay (ctx : EffectCtx) (store : Store WorldKindCell.definitionLayout)
    (ps : List (Revival.storeSubstrate kindDefinitionEffect.L).Prim)
    (valid : Patch.ValidFrom store ps) :
    (Revival.storeSubstrate kindDefinitionEffect.L).run store
      (ps ++ kindDefinitionEffect.spec.rotate ctx store) = some (Patch.run store ps) := by
  have ran := Revival.store_run_validFrom ps store valid
  have nil : ps ++ kindDefinitionEffect.spec.rotate ctx store = ps := List.append_nil ps
  rw [nil]
  exact ran

/-- What the controller runs for a revision: the prepared write replayed, or the one refusal.
A prepared revision always replays (`prepareDefinition_valid`), so the guard cannot fail. -/
theorem kindDefinition_run (code : Nat) (ctx : EffectCtx) (definition : WorldKindCell.Definition)
    (store : Store WorldKindCell.definitionLayout) :
    kindDefinitionEffect.run code ctx definition store =
      match WorldKindCell.prepareDefinition store definition with
      | some patch => .ok (Patch.run store patch)
      | none => .error (.refused code "notNextRevision" .empty) := by
  unfold Effect.run
  cases prepared : WorldKindCell.prepareDefinition store definition with
  | none =>
    rw [kindDefinitionSem_none prepared]
    rfl
  | some patch =>
    rw [kindDefinitionSem_some prepared]
    dsimp only
    rw [kindDefinition_replay ctx store patch (prepareDefinition_valid prepared)]
    rfl

/-- **The revision's member patch is complete**: wherever the semantics admits a revision, the
member is shown exactly its patch. A revision pins its root at every operation. -/
theorem kindDefinition_member_complete (ctx : EffectCtx) (definition : WorldKindCell.Definition)
    (store : Store WorldKindCell.definitionLayout) (ps : Patch WorldKindCell.definitionLayout)
    (admitted : kindDefinitionEffect.spec.sem ctx definition store = .ok ps) :
    kindDefinitionEffect.spec.commutes definition = false ∧
      kindDefinitionEffect.memberPatch ctx.signed definition store = .ok ps := by
  have prepared := kindDefinitionSem_ok
    (show kindDefinitionSem ctx definition store = .ok ps from admitted)
  exact ⟨rfl, kindDefinitionEffect.memberPatch_of rfl rfl prepared⟩

/-- **The converse**: wherever the member is shown a patch, the semantics admits the revision
with it. The semantics reads nothing the member does not: a shown revision is refused by the
receiver only at its header (the role, the schema version, a moved root). -/
theorem kindDefinition_member_admitted (ctx : EffectCtx) (definition : WorldKindCell.Definition)
    (store : Store WorldKindCell.definitionLayout) (patch : Patch WorldKindCell.definitionLayout)
    (shown : kindDefinitionEffect.memberPatch ctx.signed definition store = .ok patch) :
    kindDefinitionEffect.spec.sem ctx definition store = .ok patch := by
  obtain ⟨_, f, stated, answered⟩ := kindDefinitionEffect.memberPatch_ok shown
  have same : some f = some (fun (_ : MemberCtx) (next : WorldKindCell.Definition)
      (served : Store WorldKindCell.definitionLayout) =>
        WorldKindCell.prepareDefinition served next) := stated.symm
  cases same
  exact kindDefinitionSem_some answered ctx

/-! ## A world instance's actions -/

inductive WorldRefusal where
  /-- The actions do not lower over the instance's descriptor, a guard does not hold at the
  loaded store, or the post is no instance of the same descriptor. -/
  | worldKind
  deriving DecidableEq, Repr

def WorldRefusal.name : WorldRefusal → String
  | .worldKind => "worldKind"

/-- The actions' guarded patch at the loaded store (`WorldKindCell.preparePatch`: one write of
the payload entry naming the bytes it replaces), admitted when it applies and its post decodes
under the same descriptor. -/
def worldSem (_ : EffectCtx) (actions : List WorldKindInstance.Action)
    (store : Store WorldKindCell.instanceLayout) :
    Except WorldRefusal (Patch WorldKindCell.instanceLayout) :=
  match WorldKindCell.preparePatch store actions with
  | none => .error .worldKind
  | some patch =>
    if Patch.ValidFrom store patch then
      if (WorldKindProjection.footprint store (Patch.run store patch)).isNone then .error .worldKind
      else .ok patch
    else .error .worldKind

theorem worldSem_ok {ctx : EffectCtx} {actions : List WorldKindInstance.Action}
    {store : Store WorldKindCell.instanceLayout} {ps : Patch WorldKindCell.instanceLayout}
    (ok : worldSem ctx actions store = .ok ps) :
    WorldKindCell.preparePatch store actions = some ps ∧ Patch.ValidFrom store ps ∧
      (WorldKindProjection.footprint store (Patch.run store ps)).isSome = true := by
  unfold worldSem at ok
  split at ok
  · cases ok
  · rename_i patch prepared
    split at ok
    · rename_i valid
      split at ok
      · cases ok
      · rename_i decoded
        have decodes : (WorldKindProjection.footprint store (Patch.run store patch)).isSome = true := by
          cases found : WorldKindProjection.footprint store (Patch.run store patch) with
          | none => rw [found] at decoded; exact absurd rfl decoded
          | some _ => rfl
        cases ok
        exact ⟨prepared, valid, decodes⟩
    · cases ok

/-- **The world actions' declaration.** An object's world-instance cell at schema version 1; the
root is pinned; no rotate; every write is the body's (the scope's fields are the inner ones:
`worldEffect.footprint`); the authorization is the kind's ordinary write. -/
def worldSpec : Revival.EffectSpec EffectCtx
    (Revival.storeSubstrate WorldKindCell.instanceLayout)
    (List WorldKindInstance.Action) WorldRefusal where
  opStream := StreamCodec.list WorldKindInstance.actionStream
  refusalName := WorldRefusal.name
  accepts := fun kind => kind == .object
  version := 1
  sem := worldSem
  rotate := fun _ _ => []
  rotated := fun _ => false
  field := fun _ => .body
  amount := fun _ _ => 0
  frame := fun _ => {.body}
  verb := fun kind _ => DeclaredResourceScalar.ordinaryVerb kind
  view := fun site _ before after => WorldKindProjection.project site.subject before after

/-- The JSON face: `{"type": "world", "descriptor": …, "actions": […]}`; the descriptor is what
the actions are read against and is not part of the operation. -/
def worldOfJson (path : String) (json : Lean.Json) :
    Except String (List WorldKindInstance.Action) := do
  let obj ← EffectJson.exactObject path ["type", "descriptor", "actions"] json
  let descriptor ← ResourceGrammarJson.worldDescriptor (path ++ ".descriptor")
    (← EffectJson.field path "descriptor" obj)
  EffectJson.list (path ++ ".actions") (ResourceGrammarJson.worldAction descriptor)
    (← EffectJson.field path "actions" obj)

/-- What an inbox shows of signed world actions: how many, and their canonical bytes. -/
def worldToJson (actions : List WorldKindInstance.Action) : List (String × Lean.Json) :=
  [("actionCount", EffectJson.decimal actions.length),
   ("exactActionsHex", .str (ContentJson.encodeHex
     ((StreamCodec.list WorldKindInstance.actionStream).encode actions)))]

/-- **A world instance's actions, as the registry binds them** (code 4, JSON `world`). -/
def worldEffect : Effect where
  name := "world"
  L := WorldKindCell.instanceLayout
  wire := WorldKindCell.instanceWire
  O := List WorldKindInstance.Action
  R := WorldRefusal
  decO := inferInstance
  spec := worldSpec
  pack := fun _ cell => ⟨.worldInstance, cell⟩
  unpack := fun _ packed =>
    match packed with
    | ⟨.worldInstance, value⟩ => some value
    | _ => none
  toJson := worldToJson
  ofJson := worldOfJson
  display := fun actions => [s!"world instance: {actions.length} guarded field actions"]
  member := some fun _ actions store => WorldKindCell.preparePatch store actions
  member_exact := by
    intro f stated ctx actions store ps patch answered sem
    cases stated
    have prepared := (worldSem_ok (show worldSem ctx actions store = .ok ps from sem)).1
    exact Option.some.inj (prepared.symm.trans answered)
  member_tail := fun _ _ _ _ _ _ _ => rfl
  footprint := some fun pre post =>
    (WorldKindProjection.footprint pre post).getD ⟨{.body}, fun _ => 0⟩
  runWrites := some fun pre program index actions => WorldKindMethods.writes pre program index actions
  authors := fun actions => !actions.isEmpty
  unpack_pack := fun _ _ => rfl
  pack_unpack := by
    intro kind packed cell selected
    split at selected
    · cases selected; rfl
    · cases selected
  observes_silent := by
    intro ctx actions store ps observed _
    exact absurd ((ordinaryVerb_writes ctx.kind).symm.trans observed) Bool.false_ne_true
  complete := by
    intro ctx actions store ps ok
    have valid := (worldSem_ok (show worldSem ctx actions store = .ok ps from ok)).2.1
    refine ⟨fun loc _ _ => Finset.mem_singleton_self _, ?_⟩
    have ran := Revival.store_run_validFrom ps store valid
    have nil : ps ++ worldSpec.rotate ctx store = ps := List.append_nil ps
    rw [nil, ran]
    rfl
  view_unjoint := fun site _ before after => WorldKindProjection.project_unjoint site.subject before after

/-- **The world actions' member patch is complete**: wherever the semantics admits the actions,
the member is shown exactly their patch. World actions pin their root at every operation. The
converse does not hold and is not claimed: the semantics also refuses a patch that does not
apply or whose post does not decode, which thin consent checks itself (`Patch.ValidFrom`) or
which commits nothing. -/
theorem world_member_complete (ctx : EffectCtx) (actions : List WorldKindInstance.Action)
    (store : Store WorldKindCell.instanceLayout) (ps : Patch WorldKindCell.instanceLayout)
    (admitted : worldEffect.spec.sem ctx actions store = .ok ps) :
    worldEffect.spec.commutes actions = false ∧
      worldEffect.memberPatch ctx.signed actions store = .ok ps :=
  ⟨rfl, worldEffect.memberPatch_of rfl rfl
    (worldSem_ok (show worldSem ctx actions store = .ok ps from admitted)).1⟩

end Minidregg.Kernel.DeclaredResourceController
