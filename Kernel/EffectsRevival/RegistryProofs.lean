/-
# `Kernel/EffectsRevival/RegistryProofs.lean` — the registry keystone's poles, PROVED

Proofs of the statements in `Kernel/EffectsRevival/Statements.lean` §7b about the open payload
constructor and the registry the deployed target dispatch reads:

* `registryPremise : RegistryPremise`: every bound handler is lawful. It is proved for ANY
  declaration (`effect_handler_lawful`): soundness from the declaration's `unpack_pack` and
  `pack_unpack` fields, completeness from its `complete` field. A declaration that is not lawful
  is not an `Effect`, so it cannot be bound.
* `liveLegacyCensus : LiveLegacyCensus` and `liveLegacyCensusTeeth`: the hand decoder yields no
  payload at a bound code, a bound tag is read by its declaration alone, and an octet neither
  binds is refused by the payload decoder.
* `registry_noTwin`, `registry_unregistered`: the `noTwin` and `unregistered` clauses of
  `RegistryKeystone` (a hand-armed code is unbound; a code neither bound nor hand-armed refuses
  by name), and `registryTeeth_named`: the three clauses of `RegistryTeeth` that are about names.

* `registryKeystone : RegistryKeystone`: the deployed target dispatch dispatches every bound code
  through the registry. Its heart is `liveTargetDispatch_registered`: at a bound code and EVERY
  byte string, the deployed functions (`payloadStream`'s decode, `selectTarget`, `computeTarget`,
  the `targetPatch` validation, `packTarget`) are the engine's `dispatch`. It is proved for any
  declaration (`effect_dispatch_fire`), so binding another code adds no proof here.
* `registryAccepted : RegistryAccepted`: both poles of the cited read through the deployed
  dispatch, at an authority cell that holds an observe capability scoped to one field
  (`citedSnapshot`).
* `registryTeeth : RegistryTeeth`, with the ghost clause: a declaration that never compares its
  footprint is not what the deployed dispatch runs.
-/
module

public import Kernel.EffectsRevival.Statements
public import Effects.Revival.EngineProofs
public import Kernel.EffectsRevival.ContentProofs
public import Theory.AssertAxioms

-- Bodies this file reduces or derives through, not exposed by their modules (module system).
import all Init.Control.Except
import all Init.Data.List.Basic

@[expose] public section

namespace Minidregg.Effects.Revival

open Minidregg.Compiler
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Theory
open Minidregg.Theory.CellState
open Minidregg.Theory.Store
open Minidregg.Theory.TypedAuthorization
open Minidregg.Kernel

set_option autoImplicit false

/-- **Every declaration's handler is sound**, at every code. -/
theorem effect_handler_sound (e : DeclaredResourceController.Effect) (code : Nat) :
    (e.handler code).Sound := by
  refine ⟨?_, ?_, storeSubstrate_framed e.L⟩
  · intro ctx s
    show (e.unpack ctx.kind (e.pack ctx.kind (CellState.materialize e.materializer s))).map
      (·.logical) = some s
    rw [e.unpack_pack]
    rfl
  · intro ctx cell s selected
    show e.pack ctx.kind (CellState.materialize e.materializer s) = cell
    have selected' : (e.unpack ctx.kind cell).map (·.logical) = some s := selected
    cases found : e.unpack ctx.kind cell with
    | none => rw [found] at selected'; cases selected'
    | some pre =>
      rw [found] at selected'
      have same : pre.logical = s := Option.some.inj selected'
      subst same
      rw [materialize_logical]
      exact e.pack_unpack _ _ _ found

/-- **Every declaration's handler is lawful.** -/
theorem effect_handler_lawful (e : DeclaredResourceController.Effect) (code : Nat) :
    (e.handler code).Lawful :=
  ⟨effect_handler_sound e code, fun ctx op s ps ok => e.complete ctx.toEffectCtx op s ps ok⟩

/-- Reindexing a handler's context keeps it lawful. -/
theorem comap_lawful {C C' Cell : Type} (f : C' → C) (h : Handler C Cell) (lawful : h.Lawful) :
    (h.comap f).Lawful :=
  ⟨⟨fun ctx s => lawful.1.1 (f ctx) s, fun ctx cell s => lawful.1.2.1 (f ctx) cell s, lawful.1.2.2⟩,
    fun ctx op s ps ok => lawful.2 (f ctx) op s ps ok⟩

/-- A lookup through a list mapped on its values, the code kept. -/
theorem lookup_map_snd {α β : Type _} (g : Nat → α → β) (l : List (Nat × α)) (code : Nat) :
    (l.map fun entry => (entry.1, g entry.1 entry.2)).lookup code = (l.lookup code).map (g code) := by
  induction l with
  | nil => rfl
  | cons entry rest ih =>
    obtain ⟨k, a⟩ := entry
    cases same : code == k with
    | false => simp [List.lookup, same, ih]
    | true =>
      have equal := eq_of_beq same
      subst equal
      simp [List.lookup]

/-- A found entry is a member. -/
theorem lookup_mem {α : Type _} (l : List (Nat × α)) (code : Nat) (a : α)
    (found : l.lookup code = some a) : (code, a) ∈ l := by
  induction l with
  | nil => cases found
  | cons entry rest ih =>
    obtain ⟨k, b⟩ := entry
    cases same : code == k with
    | false =>
      simp [List.lookup, same] at found
      exact List.mem_cons_of_mem _ (ih found)
    | true =>
      have equal := eq_of_beq same
      subst equal
      simp [List.lookup] at found
      subst found
      exact List.mem_cons_self

/-- **What the host registry binds**: at every code, the handler of the declaration the
registry of effects binds there, and nothing else. -/
theorem hostRegistry_lookup_eq (code : Nat) :
    hostRegistry.lookup code = (DeclaredResourceController.liveEffects.lookup code).map
      fun e => (e.handler code).comap dispatchCtxOf := by
  have shape : hostRegistry = DeclaredResourceController.liveEffects.map
      fun entry => (entry.1, (entry.2.handler entry.1).comap dispatchCtxOf) := rfl
  rw [shape]
  exact lookup_map_snd
    (fun code (e : DeclaredResourceController.Effect) => (e.handler code).comap dispatchCtxOf) _ code

theorem hostRegistry_bound {code : Nat} {h : Handler HostCtx HostCell}
    (found : hostRegistry.lookup code = some h) :
    ∃ e, DeclaredResourceController.liveEffects.lookup code = some e ∧
      h = (e.handler code).comap dispatchCtxOf := by
  rw [hostRegistry_lookup_eq] at found
  cases bound : DeclaredResourceController.liveEffects.lookup code with
  | none => rw [bound] at found; cases found
  | some e => rw [bound] at found; exact ⟨e, rfl, (Option.some.inj found).symm⟩

/-- Every bound code is one octet (the payload tag). -/
theorem liveEffects_small {code : Nat} {e : DeclaredResourceController.Effect}
    (bound : DeclaredResourceController.liveEffects.lookup code = some e) : code < 256 := by
  have every : (DeclaredResourceController.liveEffects.all fun entry => decide (entry.1 < 256)) = true :=
    rfl
  exact of_decide_eq_true (List.all_eq_true.mp every _ (lookup_mem _ _ _ bound))

theorem registryPremise : RegistryPremise := by
  intro code h found
  obtain ⟨e, _, rfl⟩ := hostRegistry_bound found
  exact comap_lawful _ _ (effect_handler_lawful _ _)

/-- `noTwin`: no hand-armed code is bound. -/
theorem registry_noTwin : ∀ code ∈ liveLegacy, hostRegistry.lookup code = none := by
  intro code member
  simp only [liveLegacy, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-- `unregistered`: a code neither bound nor hand-armed is refused by name. -/
theorem registry_unregistered : ∀ code, hostRegistry.lookup code = none → code ∉ liveLegacy →
    ∀ bytes ctx cell, liveTargetDispatch code bytes ctx cell = .error (.unregistered code) := by
  intro code missing outside bytes ctx cell
  have unbound : DeclaredResourceController.registeredCode code = false := by
    rw [hostRegistry_lookup_eq] at missing
    unfold DeclaredResourceController.registeredCode
    cases bound : DeclaredResourceController.liveEffects.lookup code with
    | none => rfl
    | some e => rw [bound] at missing; cases missing
  unfold liveTargetDispatch
  rw [if_pos ⟨unbound, outside⟩]

/-- The clauses of `RegistryTeeth` about names: code 9 cannot also be a hand arm, and the codes
beside it and past the octet are refused by name. -/
theorem registryTeeth_named :
    ¬ Dispatches hostRegistry (9 :: liveLegacy) liveTargetDispatch ∧
    (∀ bytes ctx cell, liveTargetDispatch 10 bytes ctx cell = .error (.unregistered 10)) ∧
    (∀ bytes ctx cell, liveTargetDispatch 300 bytes ctx cell = .error (.unregistered 300)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro dispatches
    have twin := dispatches.noTwin 9 (List.mem_cons_self ..)
    have bound : hostRegistry.lookup 9 =
        some ((DeclaredResourceController.citedEffect.handler 9).comap dispatchCtxOf) := rfl
    rw [bound] at twin
    cases twin
  · exact registry_unregistered 10 rfl (by decide)
  · exact registry_unregistered 300 rfl (by decide)

theorem liveLegacyCensus : LiveLegacyCensus := by
  refine ⟨?_, ?_⟩
  · intro bytes payload rest decoded
    unfold DeclaredResourceController.legacyPayloadDecode at decoded
    split at decoded <;> first
      | (cases decoded; done)
      | (cases decoded; rfl)
      | (simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at decoded
         obtain ⟨⟨_, _⟩, _, same⟩ := decoded
         simp only [Option.some.injEq, Prod.mk.injEq] at same
         obtain ⟨same, _⟩ := same
         subst same
         rfl)
  · intro tag bytes bound
    show (if DeclaredResourceController.registeredOctet tag = true then _ else _) = _
    rw [if_pos bound]

theorem liveLegacyCensusTeeth : LiveLegacyCensusTeeth := by
  intro tag bytes unbound outside
  show (if DeclaredResourceController.registeredOctet tag = true then _
    else DeclaredResourceController.legacyPayloadDecode (tag :: bytes)) = none
  rw [if_neg (by rw [unbound]; exact Bool.false_ne_true)]
  have ne : ∀ k : UInt8, k.toNat ∈ liveLegacy → tag ≠ k :=
    fun k member same => outside (same ▸ member)
  have h0 := ne 0 (by decide)
  have h1 := ne 1 (by decide)
  have h2 := ne 2 (by decide)
  have h3 := ne 3 (by decide)
  have h4 := ne 4 (by decide)
  have h5 := ne 5 (by decide)
  have h6 := ne 6 (by decide)
  have h7 := ne 7 (by decide)
  have h8 := ne 8 (by decide)
  simp [DeclaredResourceController.legacyPayloadDecode, h0, h1, h2, h3, h4, h5, h6, h7, h8]

/-! ## The registry keystone: the deployed dispatch IS the engine's, at every bound code.

Everything below `effect_dispatch_fire` is about an arbitrary declaration `e`; the registry
enters only through `hostRegistry_bound`.

A handler's operation and state types are projections of a definition (`(e.handler code).O` is
`e.O` only after `Effect.handler` unfolds), so the rewrites below are checked at the default
transparency. -/

set_option backward.isDefEq.respectTransparency false

/-- A handler's firing, with its gate unfolded. -/
theorem Handler.fire_eq {Ctx Cell : Type} (h : Handler Ctx Cell) (code : Nat) (ctx : Ctx) (op : h.O)
    (cell : Cell) :
    h.fire code ctx op cell =
      match h.header ctx cell with
      | .error r => .error r
      | .ok () =>
        if h.spec.commutes op || h.fresh ctx cell then
          match h.select ctx cell with
          | none => .error (.wrongRole code)
          | some s => (h.spec.exec code ctx op s).map (h.pack ctx)
        else .error (.staleTarget code) := by
  unfold Handler.fire Handler.admits
  cases h.header ctx cell with
  | error r => rfl
  | ok u =>
    cases u
    by_cases gate : (h.spec.commutes op || h.fresh ctx cell) = true
    · simp only [if_pos gate]
      rfl
    · simp only [if_neg gate]

theorem EffectSpec.exec_comap {C C' : Type} {S : Substrate} {O R : Type} (f : C' → C)
    (E : EffectSpec C S O R) (code : Nat) (c : C') (op : O) (s : S.State) :
    (E.comap f).exec code c op s = E.exec code (f c) op s := rfl

theorem EffectSpec.commutes_comap {C C' : Type} {S : Substrate} {O R : Type} (f : C' → C)
    (E : EffectSpec C S O R) (op : O) : (E.comap f).commutes op = E.commutes op := rfl

theorem Handler.comap_fire {C C' Cell : Type} (f : C' → C) (h : Handler C Cell) (code : Nat)
    (c : C') (op : h.O) (cell : Cell) :
    (h.comap f).fire code c op cell = h.fire code (f c) op cell := by
  -- Two matches over a stuck scrutinee are compared argument by argument, so each scrutinee is
  -- rewritten to the same term and split before the sides are compared.
  unfold Handler.fire
  rw [show (h.comap f).admits code c op cell = h.admits code (f c) op cell from rfl]
  cases h.admits code (f c) op cell with
  | error r => rfl
  | ok u =>
    cases u
    dsimp only
    rw [show (h.comap f).select c cell = h.select (f c) cell from rfl]
    cases h.select (f c) cell with
    | none => rfl
    | some s => rfl

/-- One handler read from an operation's bytes: what `dispatch` runs at a bound code. -/
def Handler.read {Ctx Cell : Type} (h : Handler Ctx Cell) (code : Nat) (bytes : List UInt8)
    (ctx : Ctx) (cell : Cell) : Except DispatchRefusal Cell :=
  match h.spec.opStream.toLawful.decode bytes with
  | none => .error (.malformed code)
  | some op => h.fire code ctx op cell

theorem dispatch_found {Ctx Cell : Type} {R : Registry Ctx Cell} {code : Nat} {h : Handler Ctx Cell}
    (found : R.lookup code = some h) (bytes : List UInt8) (ctx : Ctx) (cell : Cell) :
    dispatch R code bytes ctx cell = h.read code bytes ctx cell := by
  simp only [dispatch, Handler.read, found]
  first
    | done
    | (cases h.spec.opStream.toLawful.decode bytes <;> rfl)

/-- A refused execution is the declaration's own named refusal or one of the executor's two. -/
theorem EffectSpec.exec_error {Ctx : Type} {S : Substrate} {O R : Type} {E : EffectSpec Ctx S O R}
    {code : Nat} {ctx : Ctx} {op : O} {s : S.State} {r : DispatchRefusal}
    (refused : E.exec code ctx op s = .error r) :
    (∃ x, r = .refused code (E.refusalName x) (E.refusalDetail x)) ∨ r = .guardFailed code ∨
      r = .outOfFrame code := by
  unfold EffectSpec.exec at refused
  split at refused
  · rename_i x _
    exact Or.inl ⟨x, (Except.error.inj refused).symm⟩
  · split at refused
    · split at refused
      · exact Or.inr (Or.inl (Except.error.inj refused).symm)
      · cases refused
    · exact Or.inr (Or.inr (Except.error.inj refused).symm)

theorem EffectSpec.exec_refused {Ctx : Type} {S : Substrate} {O R : Type} {E : EffectSpec Ctx S O R}
    {code : Nat} {ctx : Ctx} {op : O} {s : S.State} {x : R} (refused : E.sem ctx op s = .error x) :
    E.exec code ctx op s = .error (.refused code (E.refusalName x) (E.refusalDetail x)) := by
  unfold EffectSpec.exec
  rw [refused]

/-- A complete declaration that emits nothing and has no rotate returns the state it met. -/
theorem EffectSpec.exec_silent {Ctx : Type} {S : Substrate} {O R : Type} {E : EffectSpec Ctx S O R}
    (complete : E.Complete) {code : Nat} {ctx : Ctx} {op : O} {s : S.State}
    (silent : E.sem ctx op s = .ok []) (still : E.rotate ctx s = []) :
    E.exec code ctx op s = .ok s := by
  obtain ⟨post, executed⟩ := exec_ok_of_complete (code := code) complete silent
  obtain ⟨ps, emitted, _, ran⟩ := EffectSpec.exec_ok executed
  rw [silent] at emitted
  cases emitted
  rw [still] at ran
  have same : s = post := Option.some.inj ran
  rw [executed, same]

/-- **The executor against the deployed arm's tail.** The deployed arm maps the executor's
refusal into the controller's vocabulary and back (`Reject.ofDispatch`, `ofReject`), then
validates the target's patch (the emitted descriptor) at the loaded store before packing. Both
are the identity on the executor's results: its refusals are carried whole, and an admitted
descriptor replays, so the validation never refuses. -/
theorem effect_run_agrees (e : DeclaredResourceController.Effect) (code : Nat)
    (ectx : DeclaredResourceController.EffectCtx) (op : e.O) (s : Store e.L) (kind : ResourceKind) :
    (match (e.spec.exec code ectx op s).mapError DeclaredResourceController.Reject.ofDispatch with
      | .error r => .error (ofReject code r)
      | .ok post =>
        if Patch.ValidFrom s (e.patch ectx op s) then
          .ok (e.pack kind (CellState.materialize e.materializer post))
        else .error (.guardFailed code) : Except DispatchRefusal HostCell) =
      (e.spec.exec code ectx op s).map fun s => e.pack kind (CellState.materialize e.materializer s) := by
  cases ran : e.spec.exec code ectx op s with
  | error r =>
    have named : ofReject code (DeclaredResourceController.Reject.ofDispatch r) = r := by
      rcases EffectSpec.exec_error ran with ⟨x, rfl⟩ | rfl | rfl <;> rfl
    show (Except.error (ofReject code (DeclaredResourceController.Reject.ofDispatch r)) :
      Except DispatchRefusal HostCell) = Except.error r
    rw [named]
  | ok post =>
    obtain ⟨ps, emitted, _, replayed⟩ := EffectSpec.exec_ok ran
    have patched : e.patch ectx op s = ps ++ e.spec.rotate ectx s := by
      unfold DeclaredResourceController.Effect.patch EffectSpec.emitted
      rw [emitted]
      rfl
    have valid : Patch.ValidFrom s (e.patch ectx op s) := by
      rw [patched]
      exact ((store_run_iff _ _ _).mp replayed).1
    show (if Patch.ValidFrom s (e.patch ectx op s) then
        (Except.ok (e.pack kind (CellState.materialize e.materializer post)) :
          Except DispatchRefusal HostCell)
      else .error (.guardFailed code)) = Except.ok _
    exact if_pos valid

/-- A declaration's handler fired on a selected cell: the header (role, version), the expected
root unless the operation commutes, then the executor, packed. -/
theorem effect_fire_some (e : DeclaredResourceController.Effect) (code : Nat)
    (d : DeclaredResourceController.DispatchCtx) (op : e.O) (cell : HostCell) (pre : e.Cell)
    (selected : e.select d.deployment d.target d.kind cell = some pre) :
    (e.handler code).fire code d op cell =
      if e.spec.accepts d.kind = false then .error (.wrongRole code)
      else if d.version ≠ e.spec.version then .error (.unsupportedVersion code)
      else if e.spec.commutes op = false ∧ d.root ≠ pre.root then .error (.staleTarget code)
      else (e.spec.exec code d.toEffectCtx op pre.logical).map fun s =>
        e.pack d.kind (CellState.materialize e.materializer s) := by
  have unpacked : e.unpack d.kind cell = some pre := by
    unfold DeclaredResourceController.Effect.select at selected
    split at selected
    · exact selected
    · cases selected
  rw [Handler.fire_eq]
  simp only [DeclaredResourceController.Effect.handler, selected, unpacked, Option.map_some,
    EffectSpec.exec_comap, EffectSpec.commutes_comap]
  cases commuting : e.spec.commutes op <;> by_cases current : d.root = pre.root <;>
    by_cases refusedRole : e.spec.accepts d.kind = false <;>
    by_cases versioned : d.version = e.spec.version <;>
    simp [refusedRole, versioned, current] <;> rfl

/-- The same, with the header and freshness discharged. -/
theorem effect_fire_admitted (e : DeclaredResourceController.Effect) (code : Nat)
    (d : DeclaredResourceController.DispatchCtx) (op : e.O) (cell : HostCell) (pre : e.Cell)
    (selected : e.select d.deployment d.target d.kind cell = some pre)
    (accepted : e.spec.accepts d.kind = true) (versioned : d.version = e.spec.version)
    (current : e.spec.commutes op = true ∨ d.root = pre.root) :
    (e.handler code).fire code d op cell =
      (e.spec.exec code d.toEffectCtx op pre.logical).map fun s =>
        e.pack d.kind (CellState.materialize e.materializer s) := by
  have role : ¬ (e.spec.accepts d.kind = false) := by rw [accepted]; decide
  have version : ¬ (d.version ≠ e.spec.version) := fun moved => moved versioned
  have fresh : ¬ (e.spec.commutes op = false ∧ d.root ≠ pre.root) := fun both =>
    current.elim (fun commuting => by rw [commuting] at both; exact absurd both.1 (by decide))
      (fun same => both.2 same)
  rw [effect_fire_some e code d op cell pre selected, if_neg role, if_neg version, if_neg fresh]

/-- The deployed computation of a registered target and its patch validation, against the
handler's header and executor: the same four-way decision. -/
theorem effect_compute_agrees (e : DeclaredResourceController.Effect) (code : Nat)
    (d : DeclaredResourceController.DispatchCtx) (op : e.O) (pre : e.Cell) :
    (match (e.compute code d.toEffectCtx d.version d.root op pre).mapError
          DeclaredResourceController.Reject.ofDispatch with
      | .error r => .error (ofReject code r)
      | .ok post =>
        if Patch.ValidFrom pre.logical (e.patch d.toEffectCtx op pre.logical) then
          .ok (e.pack d.kind (CellState.materialize e.materializer post))
        else .error (.guardFailed code) : Except DispatchRefusal HostCell) =
      if e.spec.accepts d.kind = false then .error (.wrongRole code)
      else if d.version ≠ e.spec.version then .error (.unsupportedVersion code)
      else if e.spec.commutes op = false ∧ d.root ≠ pre.root then .error (.staleTarget code)
      else (e.spec.exec code d.toEffectCtx op pre.logical).map fun s =>
        e.pack d.kind (CellState.materialize e.materializer s) := by
  unfold DeclaredResourceController.Effect.compute
  rw [DeclaredResourceController.Effect.run_eq_exec]
  by_cases refusedRole : e.spec.accepts d.kind = false
  · rw [if_pos refusedRole, if_pos refusedRole] <;> rfl
  · rw [if_neg refusedRole, if_neg refusedRole]
    by_cases moved : d.version ≠ e.spec.version
    · rw [if_pos moved, if_pos moved] <;> rfl
    · rw [if_neg moved, if_neg moved]
      by_cases stale : e.spec.commutes op = false ∧ d.root ≠ pre.root
      · rw [if_pos stale, if_pos stale] <;> rfl
      · rw [if_neg stale, if_neg stale]
        exact effect_run_agrees e code d.toEffectCtx op pre.logical d.kind

/-- **The deployed arms of a registered payload ARE its handler fired.** Selection
(`Effect.select`), the derived computation mapped into and out of the controller's refusals, the
patch validation and the packing, at every operation, context and cell. -/
theorem effect_dispatch_fire (e : DeclaredResourceController.Effect) (code : Nat)
    (d : DeclaredResourceController.DispatchCtx) (op : e.O) (cell : HostCell) :
    (match e.select d.deployment d.target d.kind cell with
      | none => .error (.wrongRole code)
      | some pre =>
        match (e.compute code d.toEffectCtx d.version d.root op pre).mapError
            DeclaredResourceController.Reject.ofDispatch with
        | .error r => .error (ofReject code r)
        | .ok post =>
          if Patch.ValidFrom pre.logical (e.patch d.toEffectCtx op pre.logical) then
            .ok (e.pack d.kind (CellState.materialize e.materializer post))
          else .error (.guardFailed code) : Except DispatchRefusal HostCell) =
      (e.handler code).fire code d op cell := by
  cases selected : e.select d.deployment d.target d.kind cell with
  | none =>
    rw [Handler.fire_eq]
    simp only [DeclaredResourceController.Effect.handler, selected] <;> rfl
  | some pre =>
    rw [effect_fire_some e code d op cell pre selected]
    exact effect_compute_agrees e code d op pre

/-- The deployed payload decoder at a bound tag, read to the end: the declaration's own
decoder, the operation wrapped in the open constructor. -/
theorem payload_decode_bound (tag : UInt8)
    (bound : DeclaredResourceController.registeredOctet tag = true) (bytes : List UInt8) :
    DeclaredResourceController.payloadStream.toLawful.decode (tag :: bytes) =
      ((DeclaredResourceController.effectAt tag.toNat).spec.opStream.toLawful.decode bytes).map
        (DeclaredResourceController.Payload.registered tag) := by
  have census := liveLegacyCensus.2 tag bytes bound
  simp only [StreamCodec.toLawful, census]
  cases (DeclaredResourceController.effectAt tag.toNat).spec.opStream.decodePrefix bytes with
  | none => rfl
  | some decoded =>
    obtain ⟨op, rest⟩ := decoded
    by_cases empty : rest = []
    · subst empty
      rfl
    · simp [empty]

/-- **Today's dispatch at a bound code**: decode by the declaration, then its handler fired. -/
theorem hostTargetDispatch_bound (code : Nat) (small : code < 256)
    (bound : DeclaredResourceController.registeredCode code = true)
    (bytes : List UInt8) (ctx : HostCtx) (cell : HostCell) :
    hostTargetDispatch code bytes ctx cell =
      (((DeclaredResourceController.effectAt code).handler code).comap dispatchCtxOf).read
        code bytes ctx cell := by
  obtain ⟨tag, rfl⟩ : ∃ tag : UInt8, tag.toNat = code :=
    ⟨UInt8.ofNat code, uint8_toNat_ofNat_small small⟩
  unfold hostTargetDispatch Handler.read
  rw [if_neg (Nat.not_le.mpr small), UInt8.ofNat_toNat, payload_decode_bound tag bound,
    show (((DeclaredResourceController.effectAt tag.toNat).handler tag.toNat).comap
        dispatchCtxOf).spec.opStream.toLawful.decode bytes =
      (DeclaredResourceController.effectAt tag.toNat).spec.opStream.toLawful.decode bytes from rfl]
  cases (DeclaredResourceController.effectAt tag.toNat).spec.opStream.toLawful.decode bytes with
  | none => rfl
  | some op =>
    simp only [Option.map_some]
    rw [Handler.comap_fire,
      show DeclaredResourceController.selectTarget ctx.deployment
          (hostTarget ctx (.registered tag op)) cell =
        (DeclaredResourceController.effectAt tag.toNat).select (dispatchCtxOf ctx).deployment
          (dispatchCtxOf ctx).target (dispatchCtxOf ctx).kind cell from rfl]
    cases selected : (DeclaredResourceController.effectAt tag.toNat).select
        (dispatchCtxOf ctx).deployment (dispatchCtxOf ctx).target (dispatchCtxOf ctx).kind cell with
    | none =>
      have fired := effect_dispatch_fire (DeclaredResourceController.effectAt tag.toNat) tag.toNat
        (dispatchCtxOf ctx) op cell
      rw [selected] at fired
      exact fired
    | some pre =>
      -- Each side's match is its own definition's; the deployed scrutinee is rewritten to the
      -- declaration's computation and split, so both reduce before they are compared.
      have agrees := effect_compute_agrees (DeclaredResourceController.effectAt tag.toNat) tag.toNat
        (dispatchCtxOf ctx) op pre
      rw [effect_fire_some _ tag.toNat (dispatchCtxOf ctx) op cell pre selected]
      dsimp only
      rw [show DeclaredResourceController.computeTarget ctx.snapshot ctx.semantics ctx.ambient
            ctx.command (hostTarget ctx (.registered tag op)) pre =
          ((DeclaredResourceController.effectAt tag.toNat).compute tag.toNat
            (dispatchCtxOf ctx).toEffectCtx (dispatchCtxOf ctx).version (dispatchCtxOf ctx).root op
            pre).mapError DeclaredResourceController.Reject.ofDispatch from rfl]
      cases computed : ((DeclaredResourceController.effectAt tag.toNat).compute tag.toNat
          (dispatchCtxOf ctx).toEffectCtx (dispatchCtxOf ctx).version (dispatchCtxOf ctx).root op
          pre).mapError DeclaredResourceController.Reject.ofDispatch with
      | error r =>
        rw [computed] at agrees
        exact agrees
      | ok post =>
        rw [computed] at agrees
        exact agrees

/-- **At a bound code the deployed dispatch is the engine's dispatch**, on every byte string. -/
theorem liveTargetDispatch_registered {code : Nat} {h : Handler HostCtx HostCell}
    (found : hostRegistry.lookup code = some h) (bytes : List UInt8) (ctx : HostCtx)
    (cell : HostCell) :
    liveTargetDispatch code bytes ctx cell = dispatch hostRegistry code bytes ctx cell := by
  obtain ⟨e, bound, rfl⟩ := hostRegistry_bound found
  have small := liveEffects_small bound
  have registered : DeclaredResourceController.registeredCode code = true := by
    unfold DeclaredResourceController.registeredCode
    rw [bound]
    rfl
  have declared : DeclaredResourceController.effectAt code = e := by
    unfold DeclaredResourceController.effectAt
    rw [bound]
    rfl
  subst declared
  have notBoth : ¬ (DeclaredResourceController.registeredCode code = false ∧ code ∉ liveLegacy) :=
    fun both => by rw [registered] at both; exact absurd both.1 (by decide)
  unfold liveTargetDispatch
  rw [if_neg notBoth, hostTargetDispatch_bound code small registered bytes ctx cell,
    dispatch_found found]

theorem registry_sound : ∀ code h, hostRegistry.lookup code = some h → h.Sound :=
  fun code h found => (registryPremise code h found).1

/-- **THE REGISTRY KEYSTONE, PROVED.** -/
theorem registryKeystone : RegistryKeystone := by
  have engine := engineKeystone HostCtx HostCell hostRegistry registry_sound
  refine ⟨registry_noTwin, ?_, registry_unregistered, ?_⟩
  · intro code h found op ctx cell
    rw [liveTargetDispatch_registered found]
    exact engine.agreement code h found op ctx cell
  · intro code h found bytes ctx cell cell' admitted
    rw [liveTargetDispatch_registered found] at admitted
    exact engine.frame code h found bytes ctx cell cell' admitted

/-! ## The poles of the cited read, through the deployed dispatch.

The authority cell holds one capability, `⟨0⟩`: an observe grant whose scope names one field,
slot 5. The read cell is an empty declared object. A read citing slot 5 as absent is admitted
and returns the cell it met; a read citing it as `1` is refused `citedStale`, naming that key. -/

/-- An observe capability scoped to one field. -/
def citedCapability : CredentialAuthorityState.StoredCapability .object :=
  ⟨{ id := ⟨0⟩, root := ⟨0⟩, parent := none, issuer := ⟨0⟩, holder := .bearer,
     scope := { targets := .explicit {⟨0⟩}, verbs := {.observeObject}, perRequestBytes := 0,
                fields := some {.slot 5} },
     notBefore := 0, notAfter := 0, issuerEpoch := 0, policyId := ⟨0⟩, policyEpoch := 0,
     ancestors := ∅, channels := ∅ }, []⟩

/-- The authority store that holds it. -/
def citedAuthority : Store CredentialAuthorityState.layout :=
  Store.set 0 ⟨.capability .object, ⟨0⟩⟩ (some citedCapability)

def citedSnapshot : DeclaredResourceController.AuthoritySnapshot :=
  CredentialAuthorityDomain.Snapshot.ofCell ⟨0⟩ 0 (fun _ => false)
    (materialize CredentialAuthorityCell.materializer citedAuthority)

/-- The cited field. -/
def citedKey : EffectDeclaration.StateKey := .objectField ⟨0⟩ ⟨5⟩

/-- The read cell's store: nothing held. -/
abbrev citedStore : Store EffectDeclaration.effectLayout := 0

def citedCell : HostCell := ⟨.declaredObject, materialize DeclaredEffectCell.materializer citedStore⟩

/-- The host context: an object target 0 whose capability is its observe capability. -/
def citedCtx : HostCtx :=
  hostCtxOf { sampleCtx with snapshot := citedSnapshot } sampleDeployment 1 ⟨0⟩ (some ⟨0⟩) none none

theorem citedCapability_held :
    CredentialAuthorityState.readCapability citedSnapshot.cell .object ⟨0⟩ = some citedCapability := by
  show citedAuthority ⟨.capability .object, ⟨0⟩⟩ = some citedCapability
  exact Store.set_eq _ _ _

theorem citedScope_sample (v : Option Int) :
    DeclaredResourceController.citedScope citedSnapshot .object ⟨0⟩ [(citedKey, v)] = none := by
  have named : CellField.NamedBy citedCapability.head.scope.fields
      (ResourceObservationAdmission.declaredField citedKey) := by decide
  unfold DeclaredResourceController.citedScope
  rw [citedCapability_held]
  exact if_pos (by simp [named])

theorem citedRead_sample (v : Option Int) :
    DeclaredResourceController.citedRead citedSnapshot .object 0 ⟨0⟩ (some ⟨0⟩) false
        [(citedKey, v)] citedStore =
      if DeclaredResourceController.citedMoved citedStore [(citedKey, v)] = [] then .ok citedStore
      else .error (.citedStale (DeclaredResourceController.citedMoved citedStore [(citedKey, v)])) := by
  have observed : ¬ (some (⟨0⟩ : CapabilityId) ≠ some ⟨0⟩) := fun differs => differs rfl
  have own : ¬ (([(citedKey, v)].all fun read =>
      DeclaredActionLowering.writableKeyCheck (⟨0⟩ : ResourceId .object) read.1) = false) := by
    show ¬ ((DeclaredActionLowering.writableKeyCheck (⟨0⟩ : ResourceId .object) citedKey && true) = false)
    decide
  unfold DeclaredResourceController.citedRead
  rw [if_neg Bool.false_ne_true, if_neg observed, if_neg own, citedScope_sample] <;> rfl

theorem citedMoved_absent :
    DeclaredResourceController.citedMoved citedStore [(citedKey, none)] = [] := by
  first | decide | rfl

theorem citedMoved_one :
    DeclaredResourceController.citedMoved citedStore [(citedKey, some 1)] = [citedKey] := by
  first | decide | rfl

theorem citedCell_law : CanonicalCellRegistry.CellLaw sampleDeployment 0 citedCell := by
  refine ⟨by decide, ?_⟩
  refine (show CanonicalCellRegistry.DeclaredCellLaw .object 0 citedStore from ⟨?_, ?_⟩)
  · intro address member
    exact absurd rfl (Minidregg.Theory.SparseMap.mem_support_iff.mp member)
  · intro address member
    exact absurd rfl (Minidregg.Theory.SparseMap.mem_support_iff.mp member)

theorem citedCell_selected (e : DeclaredResourceController.Effect) {pre : e.Cell}
    (declared : e.unpack .object citedCell = some pre) :
    e.select sampleDeployment 0 .object citedCell = some pre := by
  unfold DeclaredResourceController.Effect.select
  rw [if_pos citedCell_law]
  exact declared

/-- The deployed dispatch of a cited read at the sample cell: the declaration's executor at the
empty store, packed. -/
theorem cited_dispatch (reads : List DeclaredResourceController.FieldRead) :
    liveTargetDispatch 9 ((StreamCodec.list DeclaredResourceController.fieldReadStream).encode reads)
        citedCtx citedCell =
      (DeclaredResourceController.citedSpec.exec 9 (dispatchCtxOf citedCtx).toEffectCtx reads
        citedStore).map fun s =>
          DeclaredResourceScalar.packDeclared .object
            (materialize DeclaredEffectCell.materializer s) :=
  (registryKeystone.agreement 9
      ((DeclaredResourceController.citedEffect.handler 9).comap dispatchCtxOf) rfl reads citedCtx
      citedCell).trans
    (effect_fire_admitted DeclaredResourceController.citedEffect 9 (dispatchCtxOf citedCtx) reads
      citedCell (materialize DeclaredEffectCell.materializer citedStore)
      (citedCell_selected _ rfl) rfl rfl (Or.inl rfl))

theorem cited_admitted :
    liveTargetDispatch 9
        ((StreamCodec.list DeclaredResourceController.fieldReadStream).encode [(citedKey, none)])
        citedCtx citedCell = .ok citedCell := by
  have read : DeclaredResourceController.citedRead citedSnapshot .object 0 ⟨0⟩ (some ⟨0⟩) false
      [(citedKey, none)] citedStore = .ok citedStore := by
    rw [citedRead_sample]
    exact if_pos citedMoved_absent
  have silent : DeclaredResourceController.citedSpec.sem (dispatchCtxOf citedCtx).toEffectCtx
      [(citedKey, none)] citedStore = .ok [] := by
    show (DeclaredResourceController.citedRead citedSnapshot .object 0 ⟨0⟩ (some ⟨0⟩) false
      [(citedKey, none)] citedStore).map (fun _ => []) = .ok []
    rw [read]
    rfl
  have executed : DeclaredResourceController.citedSpec.exec 9 (dispatchCtxOf citedCtx).toEffectCtx
      [(citedKey, none)] citedStore = .ok citedStore :=
    EffectSpec.exec_silent DeclaredResourceController.citedEffect.complete silent rfl
  rw [cited_dispatch, executed]
  rfl

theorem cited_stale :
    liveTargetDispatch 9
        ((StreamCodec.list DeclaredResourceController.fieldReadStream).encode [(citedKey, some 1)])
        citedCtx citedCell =
      .error (.refused 9 "citedStale" (DeclaredResourceController.movedStream.encode [citedKey])) := by
  have read : DeclaredResourceController.citedRead citedSnapshot .object 0 ⟨0⟩ (some ⟨0⟩) false
      [(citedKey, some 1)] citedStore = .error (.citedStale [citedKey]) := by
    rw [citedRead_sample, citedMoved_one]
    exact if_neg (List.cons_ne_nil _ _)
  have refused : DeclaredResourceController.citedSpec.sem (dispatchCtxOf citedCtx).toEffectCtx
      [(citedKey, some 1)] citedStore = .error (.citedStale [citedKey]) := by
    show (DeclaredResourceController.citedRead citedSnapshot .object 0 ⟨0⟩ (some ⟨0⟩) false
      [(citedKey, some 1)] citedStore).map (fun _ => []) = .error (.citedStale [citedKey])
    rw [read]
    rfl
  have executed : DeclaredResourceController.citedSpec.exec 9 (dispatchCtxOf citedCtx).toEffectCtx
      [(citedKey, some 1)] citedStore =
        .error (.refused 9 "citedStale" (DeclaredResourceController.movedStream.encode [citedKey])) :=
    EffectSpec.exec_refused refused
  rw [cited_dispatch, executed]
  rfl

theorem registryAccepted : RegistryAccepted :=
  ⟨⟨[(citedKey, none)], citedCtx, citedCell, List.cons_ne_nil _ _, cited_admitted⟩,
    ⟨[(citedKey, some 1)], citedCtx, citedCell, _, citedKey, cited_stale,
      DeclaredResourceController.movedStream.toLawful.decode_encode [citedKey]⟩⟩

/-- **The ghost clause**: the ghost admits the stale read the deployed dispatch refuses. -/
theorem registryTeeth_ghost :
    ¬ Dispatches [(9, (citedGhost.handler 9).comap dispatchCtxOf)] liveLegacy liveTargetDispatch := by
  intro dispatches
  have agreed := dispatches.agreement 9 ((citedGhost.handler 9).comap dispatchCtxOf) rfl
    [(citedKey, some 1)] citedCtx citedCell
  have fired := effect_fire_admitted citedGhost 9 (dispatchCtxOf citedCtx) [(citedKey, some 1)]
    citedCell (materialize DeclaredEffectCell.materializer citedStore) (citedCell_selected _ rfl)
    rfl rfl (Or.inl rfl)
  have executed : citedGhost.spec.exec 9 (dispatchCtxOf citedCtx).toEffectCtx [(citedKey, some 1)]
      citedStore = .ok citedStore :=
    EffectSpec.exec_silent citedGhost.complete rfl rfl
  have admitted : ((citedGhost.handler 9).comap dispatchCtxOf).fire 9 citedCtx [(citedKey, some 1)]
      citedCell = .ok citedCell := by
    refine Eq.trans fired ?_
    show (citedGhost.spec.exec 9 (dispatchCtxOf citedCtx).toEffectCtx [(citedKey, some 1)]
      citedStore).map _ = _
    rw [executed]
    rfl
  have clash : (Except.error (.refused 9 "citedStale"
      (DeclaredResourceController.movedStream.encode [citedKey])) : Except DispatchRefusal HostCell) =
        .ok citedCell :=
    cited_stale.symm.trans (agreed.trans admitted)
  cases clash

theorem registryTeeth : RegistryTeeth :=
  ⟨registryTeeth_ghost, registryTeeth_named.1, registryTeeth_named.2.1, registryTeeth_named.2.2⟩

#assert_axioms registryPremise
#assert_axioms registry_noTwin
#assert_axioms registry_unregistered
#assert_axioms registryTeeth_named
#assert_axioms liveLegacyCensus
#assert_axioms liveLegacyCensusTeeth
#assert_axioms registryKeystone
#assert_axioms registryAccepted
#assert_axioms registryTeeth

end Minidregg.Effects.Revival
