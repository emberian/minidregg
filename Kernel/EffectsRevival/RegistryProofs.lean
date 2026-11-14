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

OWED (stated, not proved here): `RegistryKeystone`'s `agreement` and `frame` clauses,
`RegistryAccepted`, and the ghost clause of `RegistryTeeth`.
-/
module

public import Kernel.EffectsRevival.Statements
public import Effects.Revival.EngineProofs
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

/-- What the host registry binds: the cited read at code 9, and nothing else. -/
theorem hostRegistry_lookup {code : Nat} {h : Handler HostCtx HostCell}
    (found : hostRegistry.lookup code = some h) :
    code = 9 ∧ h = (DeclaredResourceController.citedEffect.handler 9).comap dispatchCtxOf := by
  have shape : hostRegistry =
      [(9, (DeclaredResourceController.citedEffect.handler 9).comap dispatchCtxOf)] := rfl
  rw [shape] at found
  simp only [List.lookup] at found
  split at found
  · rename_i same
    exact ⟨eq_of_beq same, (Option.some.inj found).symm⟩
  · cases found

theorem registryPremise : RegistryPremise := by
  intro code h found
  obtain ⟨_, rfl⟩ := hostRegistry_lookup found
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
    by_cases nine : code = 9
    · subst nine
      have bound : hostRegistry.lookup 9 =
          some ((DeclaredResourceController.citedEffect.handler 9).comap dispatchCtxOf) := rfl
      rw [bound] at missing
      cases missing
    · simp [DeclaredResourceController.registeredCode, DeclaredResourceController.liveEffects,
        List.lookup, beq_eq_false_iff_ne.mpr nine]
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

#assert_axioms registryPremise
#assert_axioms registry_noTwin
#assert_axioms registry_unregistered
#assert_axioms registryTeeth_named
#assert_axioms liveLegacyCensus
#assert_axioms liveLegacyCensusTeeth

end Minidregg.Effects.Revival
