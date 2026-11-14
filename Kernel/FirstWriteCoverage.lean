/-
# Kernel.FirstWriteCoverage -- who judges a cell's first write

A write whose expected pre-root is the fresh root creates its cell. Two judges cover every such
write, split at `ProtectedCell.authorityBase`:

* below it, the factory step names the cell and its exact post (`ResourceBirthController.Concrete.Named`,
  the naming check `checkNamed`): `bornIn` is the fresh pre-root below the authority space;
* at or above it, `AuthoritySpaceGate.gate` admits only a live cell of the authority kind (a head
  or an entry), and the Receiver's `lawFault` admits that kind only from a family in
  `authorityWriters` (`AuthoritySpaceGate.space_write_by_authority_writer`).

`first_write_covered` is the join. An authority entry's first write is not named by the factory
step and is not asked to be (`authority_space_never_unnamed`); a first write below the authority
space that the step does not name is still refused (`unnamed_below_refused`).
-/
module

public import Kernel.AuthoritySpaceGate
public import Kernel.ResourceBirthController

@[expose] public section

namespace Minidregg.Kernel.FirstWriteCoverage

open Minidregg.Kernel.DurableDataIntent
open Minidregg.Compiler
open Minidregg.Compiler.CanonicalPolicyAdmission (PolicyStepContext)
open Minidregg.Compiler.CredentialAuthorityLayout (encodeCell)
open Minidregg.Kernel.ResourceBirthController.Concrete
open Minidregg.Theory.TypedAuthorization (Digest)

set_option autoImplicit false

/-- `bornIn`, spelled out: the fresh pre-root, below the authority space. -/
theorem bornIn_iff (write : DataWrite) :
    bornIn write = true ↔
      write.expectedPre = freshRoot ∧ write.cellId.value < ProtectedCell.authorityBase := by
  simp [bornIn]

/-- **Every first write is judged.** In an intent the authority-space gate admits and whose
births the factory step names, a write that creates its cell is either below the authority space
and named by the step with its exact post, or in the authority space and the canonical live
image of a cell of the authority kind. -/
theorem first_write_covered {rootBytes : List UInt8 → Digest} {intent : DataIntent rootBytes}
    (admitted : AuthoritySpaceGate.gate intent = .ok ()) {step : PolicyStepContext}
    (named : Named step intent.writes) {write : DataWrite} (member : write ∈ intent.writes)
    (first : write.expectedPre = freshRoot) :
    (write.cellId.value < ProtectedCell.authorityBase ∧ ReceivingLaw.namesBirth step write = true) ∨
      (ProtectedCell.authorityBase ≤ write.cellId.value ∧
        ∃ cell, write.canonicalPostBytes = encodeCell cell) := by
  by_cases below : write.cellId.value < ProtectedCell.authorityBase
  · exact Or.inl ⟨below, named write member ((bornIn_iff write).mpr ⟨first, below⟩)⟩
  · exact Or.inr ⟨Nat.le_of_not_lt below,
      AuthoritySpaceGate.admitted_space_write_is_authority admitted member (Nat.le_of_not_lt below)⟩

/-- **An authority entry's first write is admitted without being named**: the naming check never
refuses a patch for a write in the authority space, whatever the step says. -/
theorem authority_space_never_unnamed (step : PolicyStepContext) (writes : List DataWrite)
    (inSpace : ∀ write ∈ writes, ProtectedCell.authorityBase ≤ write.cellId.value) :
    unnamedBirth step writes = none := by
  rw [unnamedBirth_none_iff]
  intro write member born
  exact absurd ((bornIn_iff write).mp born).2 (Nat.not_lt.mpr (inSpace write member))

/-- **A first write below the authority space that the step does not name is still refused**,
naming a cell (the controller's `neutralBirthUnjudged`). -/
theorem unnamed_below_refused {step : PolicyStepContext} {writes : List DataWrite}
    {write : DataWrite} (member : write ∈ writes) (first : write.expectedPre = freshRoot)
    (below : write.cellId.value < ProtectedCell.authorityBase)
    (unnamed : ReceivingLaw.namesBirth step write = false) :
    ∃ cell, checkNamed step writes = .error cell := by
  cases found : unnamedBirth step writes with
  | some cell =>
      refine ⟨cell, ?_⟩
      unfold checkNamed
      split
      · rename_i other same
        rw [found] at same
        cases same
        rfl
      · rename_i same
        rw [found] at same
        cases same
  | none =>
      have names := (unnamedBirth_none_iff step writes).mp found write member
        ((bornIn_iff write).mpr ⟨first, below⟩)
      rw [unnamed] at names
      cases names

#assert_axioms bornIn_iff
#assert_axioms first_write_covered
#assert_axioms authority_space_never_unnamed
#assert_axioms unnamed_below_refused

end Minidregg.Kernel.FirstWriteCoverage
