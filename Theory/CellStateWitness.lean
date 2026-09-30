/-
# Theory.CellStateWitness -- the cell-state layer has subjects

`Theory/CellState.lean` defines `Materializer`, `Materialized` and
`ValidatedPatch` over `Theory.Store`, with private constructors -- the only way
to know the types are inhabited is to run `materialize` and `validate` on built
data.  `ValidatedPatch` is the sole premise standing between a patch and a
canonical post-state, so every theorem downstream of it inherits its
inhabitation.

This module builds two closed layouts with concrete lawful codecs, cells, and
patches, obtains `ValidatedPatch`es from `validate`, and exhibits the negative
side: a stale pre-root and a stale guard are each rejected with the exact
reason, by computation.

Layout A has one address carrying `Bool`; layout B has two addresses carrying
`Unit`.  They are witnesses that the layer's obligations are satisfiable, not a
claim that any deployed layout is.
-/
import Theory.CellState
import Theory.TypedAuthorization

namespace Minidregg.Theory.CellStateWitness

open Minidregg.Theory
open Minidregg.Theory.CellState
open Minidregg.Theory.IndexedProgram
open Minidregg.Theory.Store
open Minidregg.Theory.TypedAuthorization (Digest)

set_option autoImplicit false

/-! ## Layout A: one address carrying `Bool` -/

abbrev layout : Layout.{0, 0, 0} where
  Namespace := Unit
  Key := fun _ => Unit
  Value := fun _ => Bool
  discipline := fun _ => .ram

/-- The sole address. -/
def sole : Address layout := ⟨(), ()⟩

/-- A store with a present value at the sole address. -/
def stateOf (value : Bool) : Store layout := (0 : Store layout).set sole (some value)

/-- Any of the three possible stores: absent, present false, present true. -/
def stateOfOption : Option Bool → Store layout
  | none => 0
  | some value => stateOf value

def fieldOption (state : Store layout) : Option Bool := state sole

theorem state_ext (state : Store layout) :
    state = stateOfOption (fieldOption state) := by
  apply DFinsupp.ext
  rintro ⟨⟨⟩, ⟨⟩⟩
  change state sole = stateOfOption (fieldOption state) sole
  cases present : state sole with
  | none => simp [stateOfOption, fieldOption, present]
  | some value => simp [stateOfOption, stateOf, fieldOption, present]

/-- A lawful codec: one byte carrying the one address.  `decode_encode` is a
theorem about built functions, not a carried assumption. -/
def stateCodec : LawfulCodec (Store layout) where
  encode := fun state =>
    match fieldOption state with
    | none => [2]
    | some false => [0]
    | some true => [1]
  decode := fun bytes =>
    match bytes with
    | [0] => some (stateOf false)
    | [1] => some (stateOf true)
    | [2] => some (stateOfOption none)
    | _ => none
  decode_encode := fun state => by
    rw [state_ext state]
    cases present : fieldOption state with
    | none => simp [fieldOption, stateOfOption]
    | some value => cases value <;> simp [fieldOption, stateOfOption, stateOf]

/-- The root is the one encoded byte, so a value change moves the root. -/
def materializer : Materializer layout Digest where
  codec := stateCodec
  rootBytes := fun bytes => ⟨(bytes.headD 0).toNat⟩

/-- **The cell exists**, holding `false`. -/
def cell : Materialized materializer := materialize materializer (stateOf false)

theorem cell_root : cell.root = ⟨0⟩ := by decide

/-- A second cell, holding `true`. -/
def cellTrue : Materialized materializer := materialize materializer (stateOf true)

theorem cellTrue_root : cellTrue.root = ⟨1⟩ := by decide

/-! ## Patches that validate -/

/-- Overwrite `false` with `true`, quoting the exact prior value. -/
def honestPatch : Patch layout := [@Op.write layout () () false true]

/-- **Validation accepts, by computation.**  A `ValidatedPatch` is obtained
from the validator, whose constructor is the only route. -/
theorem honestPatch_accepted :
    ∃ validated : ValidatedPatch materializer cell ⟨0⟩ honestPatch,
      validate materializer cell ⟨0⟩ honestPatch = .accepted validated :=
  validate_accepts _ _ _ _ (by decide) (by decide)

/-- **`ValidatedPatch` is inhabited.** -/
theorem validatedPatch_nonempty :
    Nonempty (ValidatedPatch materializer cell ⟨0⟩ honestPatch) :=
  ⟨honestPatch_accepted.choose⟩

/-- Its patch writes the value back to `false`. -/
def honestPatchTrue : Patch layout := [@Op.write layout () () true false]

theorem honestPatchTrue_accepted :
    ∃ validated : ValidatedPatch materializer cellTrue ⟨1⟩ honestPatchTrue,
      validate materializer cellTrue ⟨1⟩ honestPatchTrue = .accepted validated :=
  validate_accepts _ _ _ _ (by decide) (by decide)

/-! ## Sparse deletion is a real transition -/

/-- Deletion frees the address, quoting the exact prior value; it is not an
application-level tombstone. -/
def erasePatch : Patch layout := [@Op.free layout () () true]

theorem erasePatch_accepted :
    ∃ validated : ValidatedPatch materializer cellTrue ⟨1⟩ erasePatch,
      validate materializer cellTrue ⟨1⟩ erasePatch = .accepted validated :=
  validate_accepts _ _ _ _ (by decide) (by decide)

/-- Every validator-minted instance of the erase patch produces structural
absence at the touched address. -/
theorem erasePatch_post_absent
    (validated : ValidatedPatch materializer cellTrue ⟨1⟩ erasePatch) :
    validated.apply.logical sole = none := by
  rw [ValidatedPatch.apply_logical]
  decide

/-! ## Teeth: the validator is not a rubber stamp -/

/-- A stale pre-root is rejected with the exact reason, by computation. -/
theorem stalePreRoot_rejected :
    validate materializer cell ⟨1⟩ honestPatch = .rejected .stalePreRoot :=
  validate_stalePreRoot _ _ _ _ (by decide)

/-- A patch whose guard quotes a value the cell does not hold is rejected at
exactly that operation, even with the right pre-root. -/
def staleGuardPatch : Patch layout := [@Op.write layout () () true false]

theorem staleGuardPatch_rejected :
    validate materializer cell ⟨0⟩ staleGuardPatch = .rejected (.disabledOperation 0) := by
  rfl

/-- Allocation over a present value is rejected: freshness is a guard. -/
def allocateOverPresentPatch : Patch layout := [@Op.allocate layout () () true]

theorem allocateOverPresent_rejected :
    validate materializer cell ⟨0⟩ allocateOverPresentPatch =
      .rejected (.disabledOperation 0) := by
  rfl

/-! ## Layout B: two addresses carrying `Unit`

The joint-turn witnesses need cells whose LAYOUTS differ, not just whose
values do.  This one inverts the shape of A: two keys carrying `Unit`, where A
had one key carrying `Bool`.  Its codec is concrete, a presence bitmask. -/

abbrev layoutB : Layout.{0, 0, 0} where
  Namespace := Unit
  Key := fun _ => Bool
  Value := fun _ => Unit
  discipline := fun _ => .ram

def addressB (key : Bool) : Address layoutB := ⟨(), key⟩

/-- The presence bits of a layout-B store. -/
def bitsB (state : Store layoutB) : Bool × Bool :=
  ((state (addressB false)).isSome, (state (addressB true)).isSome)

def presentIf (present : Bool) : Option Unit := if present then some () else none

def stateB (bits : Bool × Bool) : Store layoutB :=
  ((0 : Store layoutB).set (addressB false) (presentIf bits.1)).set
    (addressB true) (presentIf bits.2)

theorem stateB_ext (state : Store layoutB) : state = stateB (bitsB state) := by
  apply DFinsupp.ext
  rintro ⟨⟨⟩, key⟩
  cases key
  · change state (addressB false) = stateB (bitsB state) (addressB false)
    rw [stateB, Store.set_ne _ _ _ _ (by decide), Store.set_eq]
    cases present : state (addressB false) <;> simp [bitsB, presentIf, present]
  · change state (addressB true) = stateB (bitsB state) (addressB true)
    rw [stateB, Store.set_eq]
    cases present : state (addressB true) <;> simp [bitsB, presentIf, present]

def encodeBits : Bool × Bool → UInt8
  | (false, false) => 0
  | (true, false) => 1
  | (false, true) => 2
  | (true, true) => 3

def decodeBits : UInt8 → Option (Bool × Bool)
  | 0 => some (false, false)
  | 1 => some (true, false)
  | 2 => some (false, true)
  | 3 => some (true, true)
  | _ => none

theorem decodeBits_encodeBits (bits : Bool × Bool) :
    decodeBits (encodeBits bits) = some bits := by
  rcases bits with ⟨_ | _, _ | _⟩ <;> rfl

theorem bitsB_stateB (bits : Bool × Bool) : bitsB (stateB bits) = bits := by
  rcases bits with ⟨_ | _, _ | _⟩ <;> decide

def stateCodecB : LawfulCodec (Store layoutB) where
  encode := fun state => [encodeBits (bitsB state)]
  decode := fun bytes =>
    match bytes with
    | [byte] => (decodeBits byte).map stateB
    | _ => none
  decode_encode := fun state => by
    simp only [decodeBits_encodeBits, Option.map_some]
    exact congrArg some (stateB_ext state).symm

def materializerB : Materializer layoutB Digest where
  codec := stateCodecB
  rootBytes := fun bytes => ⟨(bytes.headD 0).toNat⟩

/-- Both addresses absent. -/
def logicalB : Store layoutB := 0

def cellB : Materialized materializerB := materialize materializerB logicalB

theorem cellB_root : cellB.root = ⟨0⟩ := by decide

/-- A patch touching only the second key, so its footprint is a proper subset
of the layout's addresses. -/
def honestPatchB : Patch layoutB := [@Op.allocate layoutB () true ()]

theorem honestPatchB_accepted :
    ∃ validated : ValidatedPatch materializerB cellB ⟨0⟩ honestPatchB,
      validate materializerB cellB ⟨0⟩ honestPatchB = .accepted validated :=
  validate_accepts _ _ _ _ (by decide) (by decide)

/-- The two layouts differ observably: one key carrying `Bool` against two keys
carrying `Unit`.  A joint turn over both is heterogeneous rather than one
layout used twice. -/
theorem layouts_differ :
    layout.Key () = Unit ∧ layoutB.Key () = Bool ∧
      layout.Value () = Bool ∧ layoutB.Value () = Unit :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- info: 'Minidregg.Theory.CellStateWitness.state_ext' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms state_ext
/-- info: 'Minidregg.Theory.CellStateWitness.cell_root' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms cell_root
/-- info: 'Minidregg.Theory.CellStateWitness.cellTrue_root' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms cellTrue_root
/-- info: 'Minidregg.Theory.CellStateWitness.honestPatch_accepted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms honestPatch_accepted
/-- info: 'Minidregg.Theory.CellStateWitness.validatedPatch_nonempty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms validatedPatch_nonempty
/-- info: 'Minidregg.Theory.CellStateWitness.honestPatchTrue_accepted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms honestPatchTrue_accepted
/-- info: 'Minidregg.Theory.CellStateWitness.erasePatch_accepted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms erasePatch_accepted
/-- info: 'Minidregg.Theory.CellStateWitness.erasePatch_post_absent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms erasePatch_post_absent
/-- info: 'Minidregg.Theory.CellStateWitness.stalePreRoot_rejected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms stalePreRoot_rejected
/-- info: 'Minidregg.Theory.CellStateWitness.staleGuardPatch_rejected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms staleGuardPatch_rejected
/-- info: 'Minidregg.Theory.CellStateWitness.allocateOverPresent_rejected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms allocateOverPresent_rejected
/-- info: 'Minidregg.Theory.CellStateWitness.stateB_ext' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms stateB_ext
/-- info: 'Minidregg.Theory.CellStateWitness.cellB_root' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms cellB_root
/-- info: 'Minidregg.Theory.CellStateWitness.honestPatchB_accepted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms honestPatchB_accepted
/-- info: 'Minidregg.Theory.CellStateWitness.layouts_differ' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms layouts_differ

end Minidregg.Theory.CellStateWitness
