/-
# Theory.CellStateAux -- a materializer's persistent auxiliary structure (statement)

Statement-first for the cell-representation change (`docs/PRIVATE-CELLS-STATE.md`, the
KeptCell ruling, option (b)). A materializer gains an `AuxCache`: a persistent structure
kept beside the logical store, updated per write, from which the root is read without
re-encoding the store. Flat kinds keep `AuxCache.flat` (`Aux := PUnit`, the root read from
the cached bytes as today); the private kinds keep the masked private index (a
`Theory.AuthTrie.Cache`, `Kernel/PrivateCellReceiver.lean`), so a patch costs one trie walk
per operation and the root one outer hash.

What this module fixes before `Theory/CellState.lean` changes:
* `AuxCache`: `Holds a s` relates a structure to the store it represents (a relation, not a
  function of the store: a kept trie is not structurally the bulk build's); `build` gives a
  structure for any store; `set` follows `Store.set`; `root?` reads a root from a structure,
  `none` meaning "hash the bytes". The two laws: `root?_sound` (a read root is the
  materializer's root of the represented store) and `root?_agree` (two structures of one store
  read the same, so a quotient may carry the structure).
* `Carried M C s := Trunc {a // C.Holds a s}`: what `Materialized` will carry. It is a
  subsingleton (`Carried.subsingleton`), so `Materialized.ext` (equal logical stores, equal
  cells) survives the new field unchanged.
* `Carried.run`: a patch moves the carried structure by `set` once per writing operation and
  never by `build` (`Carried.run_holds`); `Carried.root?` reads it.
* `RootFromCarried`: the target `Materialized.rootCache` law: the carried read, when present, is
  the root; otherwise the fallback (a `Thunk`, forced only then). Proved (`rootFromCarried`).
* `RootAvailable`: on admitted stores the read is always present; teeth `flat_not_available`,
  `stale_root_refuted`, `constant_root_refuted`.

Acceptance is a logical patch: the receiver's custody update (the blinding value, which carries
the cell's context and fresh mask) is one operation of the patch it applies, so the carried
structure never advances context on its own and `rootExact` keeps the root a function of the
store. The private instance is a total index plus the decoded context and mask; the gate
(`FitStore`) and custody stay outside it.

Per-write cost is instance-specific and stated with the private instance (the heap-program
interpreter's count, as `Theory.PrivateCellTrie.EraseCost`); a self-reported count is not a
cost statement.
-/
module

public import Theory.Store
import Theory.AssertAxioms

@[expose] public section

namespace Minidregg.Theory.CellStateAux

open Minidregg.Theory
open Minidregg.Theory.Store

set_option autoImplicit false

universe u v w y

variable {L : Layout.{u, v, w}} {Root : Type y}

/-- A persistent structure kept beside a logical store, over a root specification `spec`
(the materializer's `rootOf`; factored over the function so that `Materializer` itself can
carry one). Total: a structure exists for every store and follows every `Store.set`;
admission and custody stay outside it, and fast-path guarantees are stated over admitted
stores (`RootAvailable`). -/
structure AuxCache (spec : Store L → Root) where
  Aux : Type
  Holds : Aux → Store L → Prop
  build : (s : Store L) → {a : Aux // Holds a s}
  set : Aux → (address : Address L) → Option (L.Value address.1) → Aux
  set_holds : ∀ {a s} (address : Address L) (value : Option (L.Value address.1)),
    Holds a s → Holds (set a address value) (s.set address value)
  root? : Aux → Option Root
  root?_sound : ∀ {a s r}, Holds a s → root? a = some r → r = spec s
  root?_agree : ∀ {a b s}, Holds a s → Holds b s → root? a = root? b

/-- The flat structure: nothing kept, the root always read from the bytes. -/
def AuxCache.flat (spec : Store L → Root) : AuxCache spec where
  Aux := PUnit
  Holds := fun _ _ => True
  build := fun _ => ⟨PUnit.unit, trivial⟩
  set := fun a _ _ => a
  set_holds := fun _ _ _ => trivial
  root? := fun _ => none
  root?_sound := fun _ h => nomatch h
  root?_agree := fun _ _ => rfl

variable {spec : Store L → Root}

/-- What a cell carries: some structure representing its store, up to the choice of one. -/
abbrev Carried (C : AuxCache spec) (s : Store L) : Type := Trunc {a : C.Aux // C.Holds a s}

instance Carried.subsingleton (C : AuxCache spec) (s : Store L) : Subsingleton (Carried C s) :=
  inferInstance

/-- One operation on the carried structure: `set` at a writing operation, nothing at a read. -/
def opAux (C : AuxCache spec) (a : C.Aux) : Op L → C.Aux
  | .read _ _ _ => a
  | .write space key _ after => C.set a ⟨space, key⟩ (some after)
  | .allocate space key value => C.set a ⟨space, key⟩ (some value)
  | .free space key _ => C.set a ⟨space, key⟩ none

theorem opAux_holds (C : AuxCache spec) {a : C.Aux} {s : Store L} (op : Op L) (h : C.Holds a s) :
    C.Holds (opAux C a op) (op.apply s) := by
  cases op <;> first | exact h | exact C.set_holds _ _ h

/-- A patch on the structure: one `opAux` per operation, in order. -/
def patchAux (C : AuxCache spec) : C.Aux → Patch L → C.Aux
  | a, [] => a
  | a, op :: rest => patchAux C (opAux C a op) rest

theorem patchAux_holds (C : AuxCache spec) :
    ∀ {a : C.Aux} {s : Store L} (patch : Patch L), C.Holds a s →
      C.Holds (patchAux C a patch) (Patch.run s patch)
  | _, _, [], h => h
  | _, _, op :: rest, h => patchAux_holds C rest (opAux_holds C op h)

/-- **The carried structure follows a patch**: by `set` per writing operation, never `build`. -/
def Carried.run (C : AuxCache spec) {s : Store L} (patch : Patch L) (carried : Carried C s) :
    Carried C (Patch.run s patch) :=
  Trunc.map (fun a => ⟨patchAux C a.1 patch, patchAux_holds C patch a.2⟩) carried

/-- The carried root read, well defined on the quotient by `root?_agree`. -/
def Carried.root? (C : AuxCache spec) {s : Store L} (carried : Carried C s) : Option Root :=
  Trunc.lift (fun a => C.root? a.1) (fun a b => C.root?_agree a.2 b.2) carried

/-- The root a cell's cache will hold: the carried read when present, else the fallback,
forced only then (a `Thunk`, so a cell whose structure reads its root never encodes). -/
def Carried.rootOr (C : AuxCache spec) {s : Store L} (carried : Carried C s)
    (fallback : Thunk Root) : Root :=
  match Carried.root? C carried with
  | some r => r
  | none => fallback.get

/-- **Statement** (`Materialized.rootExact` under the new field): reading the root from the
carried structure, falling back to the specification, is the specification's root. -/
def RootFromCarried (C : AuxCache spec) : Prop :=
  ∀ (s : Store L) (carried : Carried C s), Carried.rootOr C carried (Thunk.mk fun _ => spec s) = spec s

theorem rootOr_eq (C : AuxCache spec) {s : Store L} (carried : Carried C s) (fallback : Thunk Root)
    (exact : fallback.get = spec s) : Carried.rootOr C carried fallback = spec s := by
  induction carried using Trunc.ind with
  | _ a =>
    show (match C.root? a.1 with | some r => r | none => fallback.get) = spec s
    cases h : C.root? a.1 with
    | none => exact exact
    | some r => exact C.root?_sound a.2 h

theorem rootFromCarried (C : AuxCache spec) : RootFromCarried C := by
  intro s carried
  induction carried using Trunc.ind with
  | _ a =>
    unfold Carried.rootOr Carried.root?
    simp only [Trunc.lift_mk]
    cases h : C.root? a.1 with
    | none => rfl
    | some r => exact C.root?_sound a.2 h

/-- Teeth: a structure whose read ignores the store cannot satisfy `root?_sound` once two
stores have different roots; `AuxCache` admits no constant-root cache. -/
theorem constant_root_refuted (r : Root) (s t : Store L) (differ : spec s ≠ spec t)
    (C : AuxCache spec) (constant : ∀ a, C.root? a = some r) : False :=
  differ ((C.root?_sound (C.build s).2 (constant _)).symm.trans
    (C.root?_sound (C.build t).2 (constant _)))

/-- The flat structure is the satisfiable pole: today's behaviour, every root from the
fallback. -/
theorem flat_rootOr (s : Store L) (carried : Carried (AuxCache.flat spec) s) (fallback : Thunk Root) :
    Carried.rootOr (AuxCache.flat spec) carried fallback = fallback.get := by
  induction carried using Trunc.ind with
  | _ a => rfl

/-- **Statement** (the fast path): on every admitted store, every structure representing it
reads its root, so `rootOr` never forces the fallback. The private instance owes this at the
gate's admitted stores (`Kernel.PrivateCellView.FitStore`); the flat structure owes it at no
store. -/
def RootAvailable (C : AuxCache spec) (Admitted : Store L → Prop) : Prop :=
  ∀ {a s}, Admitted s → C.Holds a s → (C.root? a).isSome

/-- Teeth: the always-fallback structure is not available at any admitted store. -/
theorem flat_not_available (s : Store L) (Admitted : Store L → Prop) (admitted : Admitted s) :
    ¬ RootAvailable (AuxCache.flat spec) Admitted :=
  fun available => by simpa [AuxCache.flat] using available (a := PUnit.unit) admitted trivial

/-- Teeth: a structure that does not follow writes (a stale `set`) is refuted by `set_holds`
together with `root?_sound` once a write changes the root: every structure representing the
written store that still reads the old root contradicts soundness. -/
theorem stale_root_refuted (C : AuxCache spec) {a : C.Aux} {s : Store L} (address : Address L)
    (value : Option (L.Value address.1)) (h : C.Holds a s) (r : Root) (old : C.root? a = some r)
    (stale : C.root? (C.set a address value) = C.root? a) (moved : spec (s.set address value) ≠ spec s) :
    False :=
  moved ((C.root?_sound (C.set_holds address value h) (stale.trans old)).symm.trans (C.root?_sound h old))

#assert_axioms rootOr_eq
#assert_axioms rootFromCarried
#assert_axioms constant_root_refuted
#assert_axioms flat_not_available
#assert_axioms stale_root_refuted

end Minidregg.Theory.CellStateAux
