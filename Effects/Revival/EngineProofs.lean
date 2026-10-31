/-
# `Effects/Revival/EngineProofs.lean` — the engine's keystones, PROVED

Proofs of the statements in `Effects/Revival/Engine.lean` (audited, pass 19 of
lane/audit-platform; nothing here changes a statement): the engine keystone, the
completeness keystone, and every satisfiable / teeth / premise witness of the two-entry pole,
plus the materialize lemma the live content handler's soundness needs.
-/
module

public import Effects.Revival.Engine
public import Theory.CellState
public import Theory.AssertAxioms

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

open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Theory
open Minidregg.Theory.CellState
open Minidregg.Theory.Store
open Minidregg.Theory.TypedAuthorization

set_option autoImplicit false

/-! ## Proofs, step 1: the materialize lemma. -/

/-- A materialized cell is its logical store, re-materialized: two packages
with the same logical store are equal (`Materialized.ext`). -/
theorem materialize_logical {L : Layout.{0, 0, 0}} {Root : Type} (M : Materializer L Root)
    (v : Materialized M) : CellState.materialize M v.logical = v :=
  CellState.Materialized.ext rfl

/-! ## Step 3a: substrate lemmas. -/

/-- The store substrate is framed: a guarded op changes only its own write address. -/
theorem storeSubstrate_framed (L : Layout.{0, 0, 0}) : (storeSubstrate L).Framed := by
  intro op s s' stepped loc outside
  simp only [storeSubstrate] at stepped outside ⊢
  split at stepped
  · cases stepped
    cases op with
    | read space key observed => rfl
    | write space key before after =>
        exact Store.set_ne _ _ _ _ (fun h => outside (by subst h; exact Finset.mem_singleton_self _))
    | allocate space key value =>
        exact Store.set_ne _ _ _ _ (fun h => outside (by subst h; exact Finset.mem_singleton_self _))
    | free space key before =>
        exact Store.set_ne _ _ _ _ (fun h => outside (by subst h; exact Finset.mem_singleton_self _))
  · cases stepped

theorem Substrate.footprint_cons (S : Substrate) (p : S.Prim) (ps : List S.Prim) :
    S.footprint (p :: ps) = S.writes p ∪ S.footprint ps := rfl

/-- A framed substrate's replay leaves every location outside the descriptor's footprint
unchanged. -/
theorem Substrate.run_frame (S : Substrate) (framed : S.Framed) :
    ∀ (ps : List S.Prim) (s s' : S.State), S.run s ps = some s' →
      ∀ loc, loc ∉ S.footprint ps → S.read s' loc = S.read s loc := by
  intro ps
  induction ps with
  | nil =>
      intro s s' ran loc _
      simp only [Substrate.run] at ran
      cases ran; rfl
  | cons p ps ih =>
      intro s s' ran loc outside
      rw [Substrate.footprint_cons, Finset.mem_union, not_or] at outside
      simp only [Substrate.run] at ran
      split at ran
      · cases ran
      · rename_i mid stepped
        rw [ih mid s' ran loc outside.2]
        exact framed p s mid stepped loc outside.1

/-! ## Step 3b: the engine keystone. -/

theorem decode_encode_op {α : Type} (c : StreamCodec α) (a : α) :
    c.toLawful.decode (c.encode a) = some a := c.toLawful.decode_encode a

theorem engineKeystone (Ctx Cell : Type) : EngineKeystone Ctx Cell := by
  intro R sound
  refine ⟨by simp, ?_, ?_, ?_⟩
  · intro code e found op ctx cell
    simp only [dispatch, found, decode_encode_op]
  · intro code missing _ bytes ctx cell
    simp only [dispatch, missing]
  · intro code e found bytes ctx cell cell' admitted
    simp only [dispatch, found] at admitted
    cases decoded : e.spec.opStream.toLawful.decode bytes with
    | none => rw [decoded] at admitted; cases admitted
    | some op =>
      rw [decoded] at admitted
      simp only [Handler.fire] at admitted
      split at admitted
      · cases admitted
      · split at admitted
        · cases admitted
        · rename_i s selected
          simp only [EffectSpec.exec] at admitted
          split at admitted
          · cases admitted
          · rename_i ps _
            split at admitted
            · rename_i inFrame
              split at admitted
              · cases admitted
              · rename_i s' ran
                cases admitted
                refine ⟨op, s, s', rfl, selected, (sound code e found).1 s', ?_⟩
                intro loc unrotated outsideFrame
                apply Substrate.run_frame e.S (sound code e found).2.2 _ s s' ran loc
                intro member
                exact outsideFrame (inFrame loc member unrotated)
            · cases admitted

/-! ## Step 3c: the completeness keystone. -/

theorem completenessKeystone (Ctx Cell : Type) : CompletenessKeystone Ctx Cell := by
  intro L code e found op ctx s r headerOk refused
  have lawful := L.lawful code e found
  simp only [dispatch, found, decode_encode_op, Handler.fire, headerOk,
    lawful.1.1 s, EffectSpec.exec] at refused
  split at refused
  · rename_i x _
    simp only [Except.map, Except.error.injEq] at refused
    exact ⟨x, refused.symm⟩
  · rename_i ps semOk
    obtain ⟨inFrame, replays⟩ := lawful.2 ctx op s ps semOk
    rw [if_pos inFrame] at refused
    cases ran : e.S.run s (ps ++ e.spec.rotate ctx s) with
    | none => rw [ran] at replays; cases replays
    | some s' => rw [ran] at refused; cases refused

/-! ## Step 2: the toy pole's witnesses. -/

theorem toyEntry_sound {O R : Type} (spec : EffectSpec Unit ToySubstrate O R) :
    (toyEntry spec).Sound :=
  ⟨fun _ => rfl, fun _ _ selected => (Option.some.inj selected).symm, storeSubstrate_framed toyLayout⟩

theorem enginePremise : EnginePremise := by
  intro code e found
  rcases code with _ | _ | code
  · simp [toyPole] at found; subst found; exact toyEntry_sound _
  · simp [toyPole, List.lookup] at found; subst found; exact toyEntry_sound _
  · simp [toyPole, List.lookup] at found

/-- The simp set that evaluates a toy dispatch. -/
theorem toyDispatchA5 :
    dispatch toyPole 0 (StreamCodec.nat.encode 5) () toyEmpty =
      .ok (Store.set toyEmpty ⟨false, ()⟩ (some (5 : Nat))) := by
  simp [dispatch, ToySubstrate, toyPole, decode_encode_op, Handler.fire, Handler.admits, toyEntry,
    EffectSpec.exec, entryASpec, toyWrite, toyEmpty, EffectSpec.InFrame, Substrate.footprint,
    Substrate.run, storeSubstrate, Op.Enabled, Op.apply, Store.Fresh, toyField,
    Op.writeAddress?, Op.address, Except.map]

theorem toyDispatchBfalse :
    dispatch toyPole 1 (StreamCodec.bool.encode false) () toyEmpty = .error (.outOfFrame 1) := by
  simp [dispatch, ToySubstrate, toyPole, List.lookup, decode_encode_op, Handler.fire, Handler.admits, toyEntry,
    EffectSpec.exec, entryBSpec, toyWrite, toyEmpty, EffectSpec.InFrame, Substrate.footprint,
    storeSubstrate, toyField, Op.writeAddress?, Op.address, Except.map]

theorem freshnessGate : FreshnessGate := by
  have decoded : entryASpec.opStream.toLawful.decode (StreamCodec.nat.encode 5) = some 5 :=
    entryASpec.opStream.toLawful.decode_encode 5
  refine ⟨?_, ?_⟩
  · simp [dispatch, List.lookup, decoded, Handler.fire, Handler.admits, staleToyEntry, toyEntry]
  · rw [toyDispatchA5]
    simp [dispatch, ToySubstrate, List.lookup, decode_encode_op, Handler.fire, Handler.admits, staleToyEntry,
      toyEntry, EffectSpec.exec, entryASpec, toyWrite, toyEmpty, EffectSpec.InFrame,
      Substrate.footprint, Substrate.run, storeSubstrate, Op.Enabled, Op.apply, Store.Fresh,
      toyField, Op.writeAddress?, Op.address, Except.map]

theorem engineSatisfiable : EngineSatisfiable :=
  ⟨engineKeystone Unit ToyStore toyPole enginePremise, toyDispatchA5, toyDispatchBfalse⟩

theorem engineTeeth : EngineTeeth := by
  have honest := engineSatisfiable.1
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h
    have agree : dispatch toyGhostPole 0 (StreamCodec.nat.encode 5) () toyEmpty =
        dispatch toyPole 0 (StreamCodec.nat.encode 5) () toyEmpty :=
      (h.agreement 0 (toyEntry entryASpec) rfl (5 : Nat) () toyEmpty).trans
        (honest.agreement 0 (toyEntry entryASpec) rfl (5 : Nat) () toyEmpty).symm
    rw [toyDispatchA5] at agree
    simp [dispatch, ToySubstrate, toyGhostPole, decode_encode_op, Handler.fire, Handler.admits, toyEntry,
      EffectSpec.exec, entryASpec, ghostASpec, toyWrite, toyEmpty, EffectSpec.InFrame,
      Substrate.footprint, Substrate.run, storeSubstrate, Op.Enabled, Op.apply, Store.Fresh,
      toyField, Op.writeAddress?, Op.address, Except.map] at agree
    have at0 := congrArg (fun c : ToyStore => c ⟨false, ()⟩) agree
    simp at at0
  · intro h
    have refused := h.unregistered 7 (by simp [toyPole, List.lookup]) (by simp)
      (StreamCodec.nat.encode 5) () toyEmpty
    have missing : toyPole.lookup 7 = none := by simp [toyPole, List.lookup]
    simp only [toyFailOpen, missing, toyDispatchA5] at refused
    cases refused
  · intro h
    have agree : dispatchUnframed toyPole 1 (StreamCodec.bool.encode false) () toyEmpty =
        dispatch toyPole 1 (StreamCodec.bool.encode false) () toyEmpty :=
      (h.agreement 1 (toyEntry entryBSpec) rfl false () toyEmpty).trans
        (honest.agreement 1 (toyEntry entryBSpec) rfl false () toyEmpty).symm
    rw [toyDispatchBfalse] at agree
    simp [dispatchUnframed, ToySubstrate, toyPole, List.lookup, decode_encode_op, toyEntry, Handler.admits,
      entryBSpec, toyWrite, toyEmpty, Substrate.run, storeSubstrate, Op.Enabled, Op.apply,
      Store.Fresh] at agree
  · intro h
    have twin := h.noTwin 1 (by simp)
    simp [toyPole, List.lookup] at twin

/-! ## Step 2: the completeness witnesses. -/

/-- A one-primitive descriptor (with an empty rotation) is in frame when its primitive's
writes are. -/
theorem toy_single_inFrame {O R : Type} (spec : EffectSpec Unit ToySubstrate O R) (op : O)
    (p : Store.Op toyLayout)
    (writes : ∀ loc ∈ (storeSubstrate toyLayout).writes p, spec.rotated loc = false →
      spec.field loc ∈ spec.frame op) :
    spec.InFrame op (([p] : List (storeSubstrate toyLayout).Prim) ++ []) := by
  intro loc member
  simp only [List.append_nil, Substrate.footprint, List.foldr, Finset.union_empty] at member
  exact writes loc member

/-- A one-primitive descriptor (with an empty rotation) replays when its guard holds. -/
theorem toy_single_run (p : Store.Op toyLayout) (s : ToyStore) (enabled : p.Enabled s) :
    ((storeSubstrate toyLayout).run s (([p] : List (storeSubstrate toyLayout).Prim) ++ [])).isSome
      = true := by
  have stepped : (storeSubstrate toyLayout).step p s = some (p.apply s) := by
    simp only [storeSubstrate]
    exact if_pos enabled
  have ran : (storeSubstrate toyLayout).run s (([p] : List (storeSubstrate toyLayout).Prim) ++ [])
      = some (p.apply s) := by
    show (storeSubstrate toyLayout).run s [p] = _
    simp only [Substrate.run, stepped]
    rfl
  rw [ran]; rfl

theorem entryA_lawful : (toyEntry entryASpec).Lawful := by
  refine ⟨toyEntry_sound _, ?_⟩
  intro ctx n s ps emitted
  change ToyStore at s
  simp only [toyEntry, entryASpec] at emitted
  split at emitted
  · cases emitted
  · cases emitted
    cases present : s ⟨false, ()⟩ with
    | none =>
        have shape : toyWrite false n s = [.allocate false () n] := by simp [toyWrite, present]
        refine ⟨?_, ?_⟩
        · rw [shape]
          refine toy_single_inFrame entryASpec n _ ?_
          intro loc member _
          simp [storeSubstrate, Op.writeAddress?, Op.address] at member
          obtain rfl := Finset.mem_singleton.mp member
          show toyField ⟨false, ()⟩ ∈ ({.slot 0} : Finset CellField)
          simp [toyField]
        · rw [shape]
          exact toy_single_run _ s (by simp [Op.Enabled, Store.Fresh, present])
    | some v =>
        have shape : toyWrite false n s = [.write false () v n] := by simp [toyWrite, present]
        refine ⟨?_, ?_⟩
        · rw [shape]
          refine toy_single_inFrame entryASpec n _ ?_
          intro loc member _
          simp [storeSubstrate, Op.writeAddress?, Op.address] at member
          obtain rfl := Finset.mem_singleton.mp member
          show toyField ⟨false, ()⟩ ∈ ({.slot 0} : Finset CellField)
          simp [toyField]
        · rw [shape]
          exact toy_single_run _ s (by simp [Op.Enabled, present])

theorem completenessSatisfiable : CompletenessSatisfiable := by
  refine ⟨entryA_lawful, ?_⟩
  simp [dispatch, ToySubstrate, List.lookup, decode_encode_op, Handler.fire, Handler.admits, toyEntry, EffectSpec.exec,
    entryASpec, toyRefusalName, Except.map]

set_option backward.isDefEq.respectTransparency false in
theorem completenessTeeth : CompletenessTeeth := by
  intro h
  have frame := (h.2 () false toyEmpty [.allocate false () 1]
    (by simp [toyEntry, entryBSpec, toyWrite, toyEmpty])).1
  have written := frame ⟨false, ()⟩ (by decide) rfl
  exact absurd written (by decide)

theorem completenessPremise : CompletenessPremise :=
  ⟨⟨[(0, toyEntry entryASpec)], by simp, by simp,
    fun code e found => by
      rcases code with _ | code
      · simp [List.lookup] at found; subst found; exact entryA_lawful
      · simp [List.lookup] at found⟩, rfl⟩

/-! ## Step 4: the legacy census, one source, and registry extension. -/

/-- The ghost pole reads code 0 differently from the pole (`5` lands as `6`). -/
theorem toyGhostDispatch5 :
    dispatch toyGhostPole 0 (StreamCodec.nat.encode 5) () toyEmpty ≠
      .ok (Store.set toyEmpty ⟨false, ()⟩ (some (5 : Nat))) := by
  intro agree
  simp [dispatch, ToySubstrate, toyGhostPole, decode_encode_op, Handler.fire, Handler.admits, toyEntry,
    EffectSpec.exec, entryASpec, ghostASpec, toyWrite, toyEmpty, EffectSpec.InFrame,
    Substrate.footprint, Substrate.run, storeSubstrate, Op.Enabled, Op.apply, Store.Fresh,
    toyField, Op.writeAddress?, Op.address, Except.map] at agree
  have at0 := congrArg (fun c : ToyStore => c ⟨false, ()⟩) agree
  simp at at0

theorem legacyCensusSatisfiable : LegacyCensusSatisfiable := by
  intro p
  cases p
  simp [toyLegacyTag, toyPole]

theorem legacyCensusTeeth : LegacyCensusTeeth := fun census => census () (by simp [toyPole])

theorem oneSourceSatisfiable : OneSourceSatisfiable := by
  refine ⟨fun code _ _ _ => .error (.unregistered code), ?_⟩
  funext code bytes ctx cell
  unfold composeDispatch
  cases found : toyPole.lookup code with
  | none => simp [dispatch, ToySubstrate, found]
  | some e => rfl

theorem oneSourceTeeth : OneSourceTeeth := by
  rintro ⟨legacy, same⟩
  have at0 := congrFun (congrFun (congrFun (congrFun same 0) (StreamCodec.nat.encode 5)) ()) toyEmpty
  simp only [composeDispatch, show toyPole.lookup 0 = some (toyEntry entryASpec) from rfl,
    toyDispatchA5] at at0
  exact toyGhostDispatch5 at0

theorem extensionPreserves (Ctx Cell : Type) : ExtensionPreserves Ctx Cell := by
  intro R R' ext code present bytes ctx cell
  cases found : R.lookup code with
  | none => exact absurd found present
  | some e => simp only [dispatch, ext code e found, found]

theorem extensionSatisfiable : ExtensionSatisfiable := by
  refine ⟨?_, by simp⟩
  intro code e found
  rcases code with _ | code
  · simp [List.lookup] at found; subst found; rfl
  · simp [List.lookup] at found

theorem extensionTeeth : ExtensionTeeth := by
  refine ⟨fun ext => ?_, fun safe => ?_⟩
  · have same := extensionPreserves Unit ToyStore toyPole toyGhostPole ext 0
      (by simp [toyPole]) (StreamCodec.nat.encode 5) () toyEmpty
    rw [toyDispatchA5] at same
    exact toyGhostDispatch5 same
  · have retired := safe.2 1 (by simp)
    simp [toyPole, List.lookup] at retired

/-! ## Step 5: prefix consumption. -/

theorem uint8_toNat_ofNat_small {n : Nat} (small : n < 256) : (UInt8.ofNat n).toNat = n := by
  simp only [UInt8.toNat_ofNat']
  exact Nat.mod_eq_of_lt small

theorem readPrefix_consumes {Ctx Cell : Type} (R : Registry Ctx Cell) :
    ConsumesPrefix R (readPrefix R) where
  consume code e found small op suffix := by
    simp [readPrefix, uint8_toNat_ofNat_small small, found, StreamCodec.decodePrefix_encode]
  refuse tag rest missing := by
    simp [readPrefix, missing]
  canonical bytes code opBytes suffix read := by
    rcases bytes with _ | ⟨tag, rest⟩
    · cases read
    · simp only [readPrefix] at read
      cases found : R.lookup tag.toNat with
      | none => simp [found] at read
      | some e =>
        simp only [found] at read
        cases decoded : e.spec.opStream.decodePrefix rest with
        | none => simp [decoded] at read
        | some pair =>
          obtain ⟨op, after⟩ := pair
          simp only [decoded, Option.map_some, Option.some.injEq, Prod.mk.injEq] at read
          obtain ⟨rfl, rfl, rfl⟩ := read
          refine ⟨e, found, UInt8.toNat_lt tag, ⟨op, rfl⟩, ?_⟩
          rw [StreamCodec.encode_decodePrefix _ _ _ _ decoded, UInt8.ofNat_toNat]

theorem prefixKeystone (Ctx Cell : Type) : PrefixKeystone Ctx Cell := by
  refine ⟨readPrefix_consumes, ?_⟩
  intro R R' ext code present small rest
  cases found : R.lookup code with
  | none => exact absurd found present
  | some e =>
    simp only [readPrefix, uint8_toNat_ofNat_small small, found, ext code e found]

theorem prefixSatisfiable : PrefixSatisfiable :=
  ⟨readPrefix_consumes toyPole,
    (readPrefix_consumes toyPole).consume 0 (toyEntry entryASpec) rfl (by decide) (5 : Nat) [7]⟩

theorem prefixTeeth : PrefixTeeth := by
  refine ⟨fun consumes => ?_, fun consumes => ?_, ?_⟩
  · have read := consumes.consume 0 (toyEntry entryASpec) rfl (by decide) (5 : Nat) [7]
    simp [readWhole, toyPole, toyEntry, entryASpec, StreamCodec.toLawful,
      StreamCodec.decodePrefix_encode] at read
  · have read := consumes.refuse 2 (StreamCodec.nat.encode 5) (by simp [toyPole])
    simp [readFailOpen, readPrefix, toyPole, toyEntry, entryASpec, List.lookup] at read
    rw [show StreamCodec.nat.encode 5 = StreamCodec.nat.encode 5 ++ [] from
      (List.append_nil _).symm, StreamCodec.decodePrefix_encode] at read
    cases read
  · simp [readPrefix, toyRebindPole, toyPole, toyEntry, entryASpec, entryBSpec, StreamCodec.nat,
      StreamCodec.bool, StreamCodec.decodeNatPrefix, List.lookup]

/-! ## Axiom pins. -/

#assert_axioms prefixKeystone
#assert_axioms prefixSatisfiable
#assert_axioms prefixTeeth
#assert_axioms legacyCensusSatisfiable
#assert_axioms legacyCensusTeeth
#assert_axioms oneSourceSatisfiable
#assert_axioms oneSourceTeeth
#assert_axioms extensionPreserves
#assert_axioms extensionSatisfiable
#assert_axioms extensionTeeth

#assert_axioms engineKeystone
#assert_axioms completenessKeystone
#assert_axioms engineSatisfiable
#assert_axioms engineTeeth
#assert_axioms enginePremise
#assert_axioms completenessSatisfiable
#assert_axioms completenessTeeth
#assert_axioms completenessPremise
#assert_axioms materialize_logical
#assert_axioms freshnessGate

end Minidregg.Effects.Revival
