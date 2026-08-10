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
def schema : Schema where
  Field := Unit
  FieldType := fun _ => Unit
  Resource := Empty
  ResourceType := fun resource => resource.elim
  Authority := fun resource => resource.elim
  Evidence := fun resource => resource.elim

instance : DecidableEq schema.Field := inferInstanceAs (DecidableEq Unit)
instance : DecidableEq schema.Resource := fun resource => resource.elim

/-- The only logical state this schema has. -/
def logical : LogicalState schema where
  fields := fun _ => ()
  resources := fun resource => resource.elim

theorem logical_unique (state : LogicalState schema) : state = logical := by
  cases state with
  | mk fields resources =>
      have hf : fields = logical.fields := funext fun _ => rfl
      have hr : resources = logical.resources := funext fun resource => resource.elim
      rw [hf, hr]

/-- A lawful codec: the state space is a singleton, so the empty encoding
round-trips.  `decode_encode` is a theorem about built functions, not a
carried assumption. -/
def stateCodec : LawfulCodec (LogicalState schema) where
  encode := fun _ => []
  decode := fun _ => some logical
  decode_encode := fun state => by rw [logical_unique state]

/-- Roots are the byte length, which is honest for a singleton state space and
makes the pre-root check below compute. -/
def materializer : Materializer schema Digest where
  codec := stateCodec
  rootBytes := fun bytes => ⟨bytes.length⟩

/-- **The cell exists.** -/
def cell : Materialized materializer := materialize materializer logical

theorem cell_root : cell.root = ⟨0⟩ := rfl

/-! ## A patch that validates -/

/-- Declare the one field, write it, and quote the exact pre-root. -/
def honestPatch : Patch schema Digest where
  expectedPreRoot := ⟨0⟩
  fieldFootprint := {()}
  resourceFootprint := ∅
  fieldWrites := [{ field := (), value := () }]
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

#print axioms logical_unique
#print axioms cell_root
#print axioms honestPatch_accepted
#print axioms validatedPatch_nonempty
#print axioms stalePatch_rejected
#print axioms overDeclaredPatch_rejected
#print axioms underDeclaredPatch_rejected

end Minidregg.Theory.CellStateWitness
