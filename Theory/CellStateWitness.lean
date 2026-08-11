/-
# Theory.CellStateWitness -- the cell-state layer has subjects

`Theory/CellState.lean` defines `Schema`, `Materializer`, `Materialized`,
`Patch`, and `ValidatedPatch`, and never exhibits one.  Its keys have private
constructors -- `Materialized.mk` and `ValidatedPatch.mk` -- which is the right
design and also means the only way to know the types are inhabited is to run
`materialize` and `validate` on built data.  Nothing in the tree did.

That matters more here than almost anywhere else: `ValidatedPatch` is the sole
premise standing between a raw patch and a canonical post-state, so every
theorem downstream of it -- `CanonicalTransition`, `AcceptedCellEffect`, the
hyperedge carriers -- inherits its inhabitation.

This module builds a closed schema, its lawful codec, a materializer, a cell,
and a patch, then obtains a `ValidatedPatch` from `validate` by computation.
It also exhibits the negative side: patches that lie about the pre-root or
misdeclare a footprint are rejected, with the exact reason, by `decide`.

The schema is deliberately minimal (one trivial field, no resources).  It is a
witness that the layer's obligations are satisfiable, not a claim that any
deployed schema is.
-/
import Theory.CellState
import Theory.IndexedProgram
import Theory.MaterializerCardinality
import Theory.TypedAuthorization

namespace Minidregg.Theory.CellStateWitness

open Minidregg.Theory
open Minidregg.Theory.CellState
open Minidregg.Theory.IndexedProgram
open Minidregg.Theory.TypedAuthorization (Digest)

set_option autoImplicit false

/-! ## A closed schema -/

/-- One trivial field and no resources: the smallest schema that still has a
field footprint to get wrong. -/
def schema : Schema.{0, 0, 0, 0} where
  Field := Unit
  FieldType := fun _ => Bool
  Resource := Empty
  ResourceType := fun resource => resource.elim
  Authority := fun resource => resource.elim
  Evidence := fun resource => resource.elim

instance : DecidableEq schema.Field := inferInstanceAs (DecidableEq Unit)
instance : DecidableEq schema.Resource := fun resource => resource.elim

/-- Build a present value at the sole field. -/
def stateOf (value : Bool) : LogicalState schema where
  fields := (0 : FieldStore schema).write () value
  resources := fun resource => resource.elim

/-- Build any of the three possible sparse states: absent, present false, or
present true. -/
def stateOfOption : Option Bool → LogicalState schema
  | none => { fields := 0, resources := fun resource => resource.elim }
  | some value => stateOf value

def fieldOption (state : LogicalState schema) : Option Bool := state.fields ()

/-- The total semantic view uses false as its explicit absent default. -/
def fieldValue (state : LogicalState schema) : Bool :=
  (fieldOption state).getD false

theorem state_ext (state : LogicalState schema) :
    state = stateOfOption (fieldOption state) := by
  cases state with
  | mk fields resources =>
      have hr : resources = fun resource => resource.elim :=
        funext fun resource => resource.elim
      cases present : fields () with
      | none =>
          have hf : fields = (0 : FieldStore schema) := by
            apply DFinsupp.ext
            intro field
            cases field
            simpa using present
          rw [hf, hr]
          rfl
      | some value =>
          have hf : fields = (0 : FieldStore schema).write () value := by
            apply DFinsupp.ext
            intro field
            cases field
            simpa [present]
          rw [hf, hr]
          rfl

/-- A lawful codec: one byte carrying the one field.  `decode_encode` is a
theorem about built functions, not a carried assumption. -/
def stateCodec : LawfulCodec (LogicalState schema) where
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
    | some value =>
        cases value <;> simp [fieldOption, stateOfOption, stateOf]

/-- The root is the one encoded byte, so a field change moves the root. -/
def materializer : Materializer schema Digest where
  codec := stateCodec
  rootBytes := fun bytes => ⟨(bytes.headD 0).toNat⟩

/-- **The cell exists**, holding `false`. -/
def cell : Materialized materializer := materialize materializer (stateOf false)

theorem cell_root : cell.root = ⟨0⟩ := rfl

/-! ## A patch that validates -/

/-- Declare the one field, write it, and quote the exact pre-root. -/
def honestPatch : Patch schema Digest where
  expectedPreRoot := ⟨0⟩
  fieldFootprint := {()}
  resourceFootprint := ∅
  fieldWrites := [{ field := (), value := some true }]
  resourceWrites := []

/-- **Validation accepts, by computation.**  The outcome is the accepted
constructor, so a `ValidatedPatch` is obtained rather than assumed -- its
constructor is private, so running the validator is the only route. -/
theorem honestPatch_accepted :
    ∃ validated : ValidatedPatch materializer cell honestPatch,
      validate materializer cell honestPatch =
        ValidationOutcome.accepted validated := by
  unfold validate
  rw [dif_pos (show honestPatch.expectedPreRoot = cell.root from rfl)]
  rw [dif_pos (show honestPatch.fieldFootprint = honestPatch.namedFields by decide)]
  rw [dif_pos
    (show honestPatch.resourceFootprint = honestPatch.namedResources by decide)]
  exact ⟨_, rfl⟩

/-- **`ValidatedPatch` is inhabited.**  This is the premise every canonical
post-state in the tree stands on. -/
theorem validatedPatch_nonempty :
    Nonempty (ValidatedPatch materializer cell honestPatch) :=
  ⟨honestPatch_accepted.choose⟩

/-- A second cell, holding `true`, so a joint turn can carry two distinct
canonical pre-states under one apex. -/
def cellTrue : Materialized materializer := materialize materializer (stateOf true)

theorem cellTrue_root : cellTrue.root = ⟨1⟩ := by decide

/-- Its patch writes the field back to `false`. -/
def honestPatchTrue : Patch schema Digest where
  expectedPreRoot := ⟨1⟩
  fieldFootprint := {()}
  resourceFootprint := ∅
  fieldWrites := [{ field := (), value := some false }]
  resourceWrites := []

theorem honestPatchTrue_accepted :
    ∃ validated : ValidatedPatch materializer cellTrue honestPatchTrue,
      validate materializer cellTrue honestPatchTrue =
        ValidationOutcome.accepted validated := by
  unfold validate
  rw [dif_pos (show honestPatchTrue.expectedPreRoot = cellTrue.root by decide)]
  rw [dif_pos
    (show honestPatchTrue.fieldFootprint = honestPatchTrue.namedFields by decide)]
  rw [dif_pos
    (show honestPatchTrue.resourceFootprint = honestPatchTrue.namedResources by decide)]
  exact ⟨_, rfl⟩

/-! ## Sparse deletion is a real transition -/

/-- Deletion names the address in the authoritative footprint and assigns
`none`; it is not an application-level tombstone. -/
def erasePatch : Patch schema Digest where
  expectedPreRoot := ⟨1⟩
  fieldFootprint := {()}
  resourceFootprint := ∅
  fieldWrites := [{ field := (), value := none }]
  resourceWrites := []

theorem erasePatch_accepted :
    ∃ validated : ValidatedPatch materializer cellTrue erasePatch,
      validate materializer cellTrue erasePatch =
        ValidationOutcome.accepted validated := by
  unfold validate
  rw [dif_pos (show erasePatch.expectedPreRoot = cellTrue.root by decide)]
  rw [dif_pos (show erasePatch.fieldFootprint = erasePatch.namedFields by decide)]
  rw [dif_pos
    (show erasePatch.resourceFootprint = erasePatch.namedResources by decide)]
  exact ⟨_, rfl⟩

/-- Every validator-minted instance of the erase patch produces structural
absence at the touched address. -/
theorem erasePatch_post_absent
    (validated : ValidatedPatch materializer cellTrue erasePatch) :
    validated.apply.logical.fields () = none := by
  simp [ValidatedPatch.apply, erasePatch, applyFieldWrites, FieldStore.assign]
  rfl

/-! ## A genuinely different schema

The joint-turn witnesses need cells whose SCHEMAS differ, not just whose values
do.  This one inverts the shape of the first: two field keys carrying a trivial
value type, where the first had one key carrying `Bool`. -/

/-- Two field keys, each carrying `Unit`, and no resources. -/
def schemaB : Schema.{0, 0, 0, 0} where
  Field := Bool
  FieldType := fun _ => Unit
  Resource := Empty
  ResourceType := fun resource => resource.elim
  Authority := fun resource => resource.elim
  Evidence := fun resource => resource.elim

instance : DecidableEq schemaB.Field := inferInstanceAs (DecidableEq Bool)
instance : DecidableEq schemaB.Resource := fun resource => resource.elim

/-- The chosen state has both field addresses absent.  Even with `Unit` values,
the sparse state space also distinguishes presence from absence; this is one
canonical base state, not a uniqueness claim. -/
def logicalB : LogicalState schemaB where
  fields := 0
  resources := fun resource => resource.elim

instance : Countable schemaB.Field := inferInstanceAs (Countable Bool)
instance : ∀ field : schemaB.Field, Countable (schemaB.FieldType field) :=
  fun _ => inferInstanceAs (Countable Unit)

instance : Countable (LogicalState schemaB) :=
  MaterializerCardinality.sparse_schema_state_countable
    (S := schemaB) ⟨fun resource => resource.elim⟩

instance : Nonempty (LogicalState schemaB) := ⟨logicalB⟩

noncomputable def stateCodecB : LawfulCodec (LogicalState schemaB) :=
  Classical.choice MaterializerCardinality.nonempty_lawfulCodec_of_countable

noncomputable def materializerB : Materializer schemaB Digest where
  codec := stateCodecB
  rootBytes := fun _ => ⟨0⟩

noncomputable def cellB : Materialized materializerB :=
  materialize materializerB logicalB

theorem cellB_root : cellB.root = ⟨0⟩ := rfl

/-- A patch touching only the second field key, so its footprint is a proper
subset of the schema's fields. -/
def honestPatchB : Patch schemaB Digest where
  expectedPreRoot := ⟨0⟩
  fieldFootprint := {true}
  resourceFootprint := ∅
  fieldWrites := [{ field := true, value := some () }]
  resourceWrites := []

theorem honestPatchB_accepted :
    ∃ validated : ValidatedPatch materializerB cellB honestPatchB,
      validate materializerB cellB honestPatchB =
        ValidationOutcome.accepted validated := by
  unfold validate
  rw [dif_pos (show honestPatchB.expectedPreRoot = cellB.root from rfl)]
  rw [dif_pos (show honestPatchB.fieldFootprint = honestPatchB.namedFields by decide)]
  rw [dif_pos
    (show honestPatchB.resourceFootprint = honestPatchB.namedResources by decide)]
  exact ⟨_, rfl⟩

/-- The two schemas differ observably: one field key carrying `Bool` against two
field keys carrying `Unit`.  A joint turn over both is heterogeneous rather than
one schema used twice. -/
theorem schemas_differ :
    schema.Field = Unit ∧ schemaB.Field = Bool ∧
      schema.FieldType () = Bool ∧ schemaB.FieldType true = Unit :=
  ⟨rfl, rfl, rfl, rfl⟩

/-! ## Teeth: the validator is not a rubber stamp -/

/-- A stale pre-root is rejected with the exact reason, by computation. -/
def stalePatch : Patch schema Digest :=
  { honestPatch with expectedPreRoot := ⟨1⟩ }

theorem stalePatch_rejected :
    validate materializer cell stalePatch =
      ValidationOutcome.rejected RejectReason.stalePreRoot := rfl

/-- A patch that declares a field footprint it does not write is rejected. -/
def overDeclaredPatch : Patch schema Digest :=
  { honestPatch with fieldWrites := [] }

theorem overDeclaredPatch_rejected :
    validate materializer cell overDeclaredPatch =
      ValidationOutcome.rejected RejectReason.fieldFootprintMismatch := by
  unfold validate
  rw [dif_pos (show overDeclaredPatch.expectedPreRoot = cell.root from rfl)]
  rw [dif_neg
    (show ¬overDeclaredPatch.fieldFootprint = overDeclaredPatch.namedFields by decide)]

/-- And a patch that writes a field it did not declare is rejected the same
way -- the footprint equation is exact in both directions, not an upper
bound. -/
def underDeclaredPatch : Patch schema Digest :=
  { honestPatch with fieldFootprint := ∅ }

theorem underDeclaredPatch_rejected :
    validate materializer cell underDeclaredPatch =
      ValidationOutcome.rejected RejectReason.fieldFootprintMismatch := by
  unfold validate
  rw [dif_pos (show underDeclaredPatch.expectedPreRoot = cell.root from rfl)]
  rw [dif_neg
    (show ¬underDeclaredPatch.fieldFootprint = underDeclaredPatch.namedFields by decide)]

/-- info: 'Minidregg.Theory.CellStateWitness.state_ext' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms state_ext
/-- info: 'Minidregg.Theory.CellStateWitness.cellTrue_root' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms cellTrue_root
/-- info: 'Minidregg.Theory.CellStateWitness.cellB_root' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms cellB_root
/-- info: 'Minidregg.Theory.CellStateWitness.honestPatchB_accepted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms honestPatchB_accepted
/-- info: 'Minidregg.Theory.CellStateWitness.schemas_differ' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms schemas_differ
/-- info: 'Minidregg.Theory.CellStateWitness.honestPatchTrue_accepted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms honestPatchTrue_accepted
/-- info: 'Minidregg.Theory.CellStateWitness.erasePatch_accepted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms erasePatch_accepted
/-- info: 'Minidregg.Theory.CellStateWitness.erasePatch_post_absent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms erasePatch_post_absent
/-- info: 'Minidregg.Theory.CellStateWitness.cell_root' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms cell_root
/-- info: 'Minidregg.Theory.CellStateWitness.honestPatch_accepted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms honestPatch_accepted
/-- info: 'Minidregg.Theory.CellStateWitness.validatedPatch_nonempty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms validatedPatch_nonempty
/-- info: 'Minidregg.Theory.CellStateWitness.stalePatch_rejected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms stalePatch_rejected
/-- info: 'Minidregg.Theory.CellStateWitness.overDeclaredPatch_rejected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms overDeclaredPatch_rejected
/-- info: 'Minidregg.Theory.CellStateWitness.underDeclaredPatch_rejected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms underDeclaredPatch_rejected

end Minidregg.Theory.CellStateWitness
