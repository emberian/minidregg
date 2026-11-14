/-
# `Kernel/EffectsRevival/HostTeethProofs.lean` — `HostTeeth`, PROVED

`Kernel/EffectsRevival/Statements.lean` §7 (audited): the host dispatch does not dispatch through a
registry whose content handler drops the rotation, nor through one that keeps code 1 as a
hand arm.

The twin half is `noTwin` at code 1.  The ghost half compares the host dispatch with the
ghost handler's firing at the blinded cell of `ContentProofs` (a link admitted): the
dispatch's post blinding is one ratchet step of the pre blinding
(`StoreCodec.Blinding.run_leg_blinding`), the ghost's is the pre blinding unchanged.  That the
step MOVES the blinding is a fact about cSHAKE256 on concrete bytes (`ratchet_moves`), checked by
compiled evaluation (`native_decide`, pinned by `#assert_compiled`); every other proof here is
kernel-checked.
-/
module

public import Kernel.EffectsRevival.ContentProofs
public import Kernel.EffectsRevival.RegistryProofs
public import Theory.AssertAxioms
-- `ratchet_moves` is evaluated by compiled code (native_decide): its definitions must be available at
-- compile time, and `#assert_compiled` re-runs it.
public meta import Compiler.HyperdocumentCell
meta import Theory.AssertCompiled

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
import all Init.Data.List.Scan.Basic

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

/-- The canonical bytes of the zero blinding. -/
def zeroBlindingKey : List UInt8 :=
  (HyperdocumentCell.contentWire.valueStream .blinding).encode (⟨0⟩ : Digest)

/-- **The one hash fact**: a ratchet step at height 0 moves the zero blinding. -/
theorem ratchet_moves :
    (HyperdocumentCell.contentBlinding.step 0 zeroBlindingKey != zeroBlindingKey) = true := by
  -- A fact about concrete data (one cSHAKE256 step over a 32-byte key): checked by compiled
  -- evaluation, on the Rust kernel behind `@[extern]` (ember, 2026-11-06: concrete data by the
  -- compiler, general theorems by the kernel). `decide +kernel` ran cSHAKE in the kernel: 37 s and
  -- 8.3 GB for this module.
  native_decide

set_option backward.isDefEq.respectTransparency false in
theorem blindedStore_key :
    StoreCodec.blindingKey HyperdocumentCell.contentWire blindedStore = some zeroBlindingKey := by
  rw [HyperdocumentCell.contentBlinding.blindingKey_eq]
  simp [blindedStore, StoreCodec.Blinding.address, HyperdocumentCell.contentBlinding, zeroBlindingKey]

set_option backward.isDefEq.respectTransparency false in
/-- The link's allocation leaves the blinding where it was. -/
theorem sampleLinkOps_key :
    StoreCodec.blindingKey HyperdocumentCell.contentWire (Patch.run blindedStore sampleLinkOps) =
      some zeroBlindingKey := by
  rw [HyperdocumentCell.contentBlinding.blindingKey_eq]
  have kept : Patch.run blindedStore sampleLinkOps ⟨.blinding, ()⟩ = blindedStore ⟨.blinding, ()⟩ := by
    simp only [sampleLinkOps, Patch.run_cons, Patch.run_nil, Op.apply]
    exact Store.set_ne _ _ _ _ (by simp)
  change (Patch.run blindedStore sampleLinkOps ⟨.blinding, ()⟩).map _ = _
  rw [kept]
  simp [blindedStore, zeroBlindingKey]
  rfl

/-- The ghost declaration's executor at the blinded store: the link's allocation alone. -/
theorem footprint_append_left {S : Substrate} (qs : List S.Prim) :
    ∀ (ps : List S.Prim) (loc : S.Loc), loc ∈ S.footprint ps → loc ∈ S.footprint (ps ++ qs)
  | [], _, member => by simp [Substrate.footprint] at member
  | p :: ps, loc, member => by
      rw [List.cons_append, Substrate.footprint_cons]
      rw [Substrate.footprint_cons, Finset.mem_union] at member
      rcases member with member | member
      · exact Finset.mem_union_left _ member
      · exact Finset.mem_union_right _ (footprint_append_left qs ps loc member)

theorem ghost_exec_blinded :
    EffectSpec.exec contentGhost 1 sampleCtx sampleLinkCommand blindedStore =
      .ok (Patch.run blindedStore sampleLinkOps) := by
  have emitted : contentGhost.sem sampleCtx sampleLinkCommand blindedStore = .ok sampleLinkOps :=
    sampleLink_emits_blinded_eq
  obtain ⟨inFrame, runs⟩ := contentComplete sampleCtx sampleLinkCommand blindedStore sampleLinkOps
    sampleLink_emits_blinded_eq
  obtain ⟨s', ran⟩ := Option.isSome_iff_exists.mp runs
  have whole := ((store_run_iff (L := Hyperdocument.layout) _ _ _).1 ran).1
  have valid : Patch.ValidFrom blindedStore sampleLinkOps :=
    ((Patch.validFrom_append _ _ _).1 whole).1
  have replays := (store_run_iff (L := Hyperdocument.layout) sampleLinkOps blindedStore _).2 ⟨valid, rfl⟩
  unfold EffectSpec.exec
  rw [emitted]
  dsimp only
  split
  · split
    · rename_i missing
      simp only [contentGhost] at missing
      erw [List.append_nil, replays] at missing
      cases missing
    · rename_i s'' replayed
      simp only [contentGhost] at replayed
      erw [List.append_nil, replays] at replayed
      cases replayed
      rfl
  · rename_i outside
    exact absurd (fun loc member unrotated =>
      inFrame loc (footprint_append_left _ _ loc (by exact member)) unrotated)
      outside

set_option backward.isDefEq.respectTransparency false in
/-- **A handler without its rotate fires as the handler does up to the executor**: where the
handler admits and selects, its unrotated twin runs its own executor on the same store and packs
the same way. -/
theorem Handler.unrotated_fire {Ctx Cell : Type} (h : Handler Ctx Cell) {code : Nat} {ctx : Ctx}
    {op : h.O} {cell cell' : Cell} (fired : h.fire code ctx op cell = .ok cell') :
    ∃ s, h.select ctx cell = some s ∧
      h.unrotated.fire code ctx op cell =
        (h.unrotated.spec.exec code ctx op s).map (h.pack ctx) := by
  rw [Handler.fire_eq] at fired
  have ghost := Handler.fire_eq h.unrotated code ctx op cell
  have sameHeader : h.unrotated.header = h.header := rfl
  have sameFresh : h.unrotated.fresh = h.fresh := rfl
  have sameSelect : h.unrotated.select = h.select := rfl
  have samePack : h.unrotated.pack = h.pack := rfl
  have sameCommutes : h.unrotated.spec.commutes op = h.spec.commutes op := rfl
  rw [sameHeader, sameFresh, sameSelect, samePack, sameCommutes] at ghost
  cases header : h.header ctx cell with
  | error r => rw [header] at fired; cases fired
  | ok u =>
    cases u
    rw [header] at fired ghost
    dsimp only at fired ghost
    by_cases gate : (h.spec.commutes op || h.fresh ctx cell) = true
    · rw [if_pos gate] at fired ghost
      cases selected : h.select ctx cell with
      | none => rw [selected] at fired; cases fired
      | some s =>
        rw [selected] at ghost
        exact ⟨s, rfl, ghost⟩
    · rw [if_neg gate] at fired
      cases fired

/-- A packed content cell's blinding key. -/
def contentKey : Except DispatchRefusal HostCell → Option (List UInt8)
  | .ok ⟨.content, cell⟩ => StoreCodec.blindingKey HyperdocumentCell.contentWire cell.logical
  | _ => none

set_option backward.isDefEq.respectTransparency false in
theorem hostGhost_disagrees :
    ¬ Dispatches [(1, contentHostHandler.unrotated)] liveLegacy liveTargetDispatch := by
  intro dispatches
  obtain ⟨post, executed, dispatched⟩ := hostDispatch_blinded
  have agree := dispatches.agreement 1 contentHostHandler.unrotated (by simp [List.lookup])
    sampleLinkCommand sampleHostCtx ⟨.content, cellOf blindedStore⟩
  have real := registryKeystone.agreement 1 contentHostHandler rfl
    sampleLinkCommand sampleHostCtx ⟨.content, cellOf blindedStore⟩
  change liveTargetDispatch 1 (ContentResource.commandStream.encode sampleLinkCommand) sampleHostCtx _ = _
    at real
  rw [liveTargetDispatch_content, dispatched] at real
  obtain ⟨s, selected, ghost⟩ := Handler.unrotated_fire contentHostHandler real.symm
  have store : s = blindedStore :=
    Option.some.inj (selected.symm.trans
      (rfl : contentHostHandler.select sampleHostCtx
        (⟨.content, cellOf blindedStore⟩ : HostCell) = some blindedStore))
  subst store
  have fired : contentHostHandler.unrotated.fire 1 sampleHostCtx sampleLinkCommand
      (⟨.content, cellOf blindedStore⟩ : HostCell) =
        .ok ⟨.content, CellState.materialize HyperdocumentCell.contentMaterializer
          (Patch.run blindedStore sampleLinkOps)⟩ := by
    rw [ghost]
    show (EffectSpec.exec contentGhost 1 sampleCtx sampleLinkCommand blindedStore).map _ = _
    rw [ghost_exec_blinded]
    rfl
  change liveTargetDispatch 1 (ContentResource.commandStream.encode sampleLinkCommand) sampleHostCtx _ = _
    at agree
  rw [liveTargetDispatch_content, dispatched, fired] at agree
  have keys := congrArg contentKey agree
  -- the dispatch's post: the descriptor, then the rotation
  have postRun : post = Patch.run blindedStore
      (sampleLinkOps ++ HyperdocumentCell.contentBlinding.patch blindedStore 0) := by
    unfold EffectSpec.exec at executed
    rw [sampleLink_emits_blinded_eq] at executed
    dsimp only at executed
    obtain ⟨inFrame, -⟩ := contentComplete sampleCtx sampleLinkCommand blindedStore sampleLinkOps
      sampleLink_emits_blinded_eq
    rw [if_pos inFrame] at executed
    split at executed
    · cases executed
    · rename_i s' ran
      cases executed
      exact ((store_run_iff (L := Hyperdocument.layout) _ _ _).1 ran).2.symm
  have dispatchKey : StoreCodec.blindingKey HyperdocumentCell.contentWire post =
      some (HyperdocumentCell.contentBlinding.step 0 zeroBlindingKey) := by
    rw [postRun]
    exact HyperdocumentCell.contentBlinding.run_leg_blinding blindedStore sampleLinkOps 0 blindedStore_key
  have moved := ratchet_moves
  change StoreCodec.blindingKey HyperdocumentCell.contentWire post =
    StoreCodec.blindingKey HyperdocumentCell.contentWire (Patch.run blindedStore sampleLinkOps) at keys
  rw [sampleLinkOps_key, dispatchKey] at keys
  simp only [Option.some.injEq] at keys
  rw [keys] at moved
  simp at moved

theorem hostTwin_refuted :
    ¬ Dispatches hostRegistry (1 :: liveLegacy) liveTargetDispatch := fun dispatches => by
  have unbound := dispatches.noTwin 1 (by simp)
  rw [hostKeystone.2.1] at unbound
  cases unbound

theorem hostTeeth : HostTeeth := ⟨hostGhost_disagrees, hostTwin_refuted⟩

#assert_axioms blindedStore_key
#assert_axioms sampleLinkOps_key
#assert_axioms ghost_exec_blinded
#assert_axioms hostTwin_refuted
#assert_compiled ratchet_moves
#assert_compiled hostTeeth

end Minidregg.Effects.Revival
