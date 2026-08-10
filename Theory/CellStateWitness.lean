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

/-- A logical state is determined by its one field, since the resource family
is empty. -/
def stateOf (value : Bool) : LogicalState schema where
  fields := fun _ => value
  resources := fun resource => resource.elim

/-- The one field, read at `Bool` rather than at the schema's projection. -/
def fieldValue (state : LogicalState schema) : Bool := state.fields ()

theorem state_ext (state : LogicalState schema) :
    state = stateOf (fieldValue state) := by
  cases state with
  | mk fields resources =>
      have hf : fields = fun _ => fields () := funext fun _ => rfl
      have hr : resources = fun resource => resource.elim :=
        funext fun resource => resource.elim
      rw [hf, hr]
      rfl

/-- A lawful codec: one byte carrying the one field.  `decode_encode` is a
theorem about built functions, not a carried assumption. -/
def stateCodec : LawfulCodec (LogicalState schema) where
  encode := fun state => [if fieldValue state then 1 else 0]
  decode := fun bytes => some (stateOf (decide (bytes = [1])))
  decode_encode := fun state => by
    rw [state_ext state]
    cases hvalue : fieldValue state <;> simp [stateOf, fieldValue, hvalue]

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
  fieldWrites := [{ field := (), value := true }]
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
  fieldWrites := [{ field := (), value := false }]
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

#print axioms state_ext
#print axioms cellTrue_root
#print axioms honestPatchTrue_accepted
#print axioms cell_root
#print axioms honestPatch_accepted
#print axioms validatedPatch_nonempty
#print axioms stalePatch_rejected
#print axioms overDeclaredPatch_rejected
#print axioms underDeclaredPatch_rejected

end Minidregg.Theory.CellStateWitness
