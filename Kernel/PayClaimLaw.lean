/-
Default local factory clause for source-authorized paid-claim actions.

Only the claim receiver projects the operation and authorized slots, after its
Checked signature, current-owner, exact unconsumed-origin and quote decision.
The subject remains the stable owner. This clause is placed inside the existing
observer/ticker confinement; composed inherited restrictions remain mandatory
outside it. It supplies no capability, receipt, signature or authority witness.
-/
import Pred.Core
import Theory.AssertAxioms

namespace Minidregg.Kernel.PayClaimLaw

open Minidregg.Pred

set_option autoImplicit false

def operationSlot : String := "authority/operation/pay-claim"
def authorizedSlot : String := "pay/claim/authorized"

def clause : Pred := .all [.eq operationSlot 1, .eq authorizedSlot 1]

/-- A claim operation never falls through to a permissive ordinary base.
When the source operation slot is absent, the old base is exactly preserved. -/
def extend (base : Pred) : Pred :=
  .any [clause, .all [.not (.eq operationSlot 1), base]]

theorem default_allows_claim (base : Pred) (old new : State)
    (operation : new.get operationSlot = some 1)
    (authorized : new.get authorizedSlot = some 1) :
    eval (extend base) old new = true := by
  simp [extend, clause, eval, evalWith, operation, authorized]

theorem claim_requires_authorized (base : Pred) (old new : State)
    (operation : new.get operationSlot = some 1)
    (unauthorized : new.get authorizedSlot ≠ some 1) :
    eval (extend base) old new = false := by
  simp [extend, clause, eval, evalWith, operation, unauthorized]

theorem ordinary_preserved (base : Pred) (old new : State)
    (ordinary : new.get operationSlot = none) :
    eval (extend base) old new = eval base old new := by
  simp [extend, clause, eval, evalWith, ordinary]

/-- Extending the local default cannot erase an inherited restriction that
the composed source keeps outside this local branch. -/
theorem inherited_restriction_required (inherited base : Pred) (old new : State)
    (accepted : eval (.all [inherited, extend base]) old new = true) :
    eval inherited old new = true := by
  have both : eval inherited old new = true ∧ eval (extend base) old new = true := by
    simpa [eval, evalWith] using accepted
  exact both.1

theorem checked_claim_over_denied_ordinary_base :
    eval (extend (.any [])) ⟨[]⟩
      ⟨[(operationSlot, 1), (authorizedSlot, 1)]⟩ = true := by decide

theorem unproven_claim_cannot_use_permissive_base :
    eval (extend (.all [])) ⟨[]⟩ ⟨[(operationSlot, 1)]⟩ = false := by decide

theorem claim_cannot_escape_inherited_denial :
    eval (.all [.any [], extend (.all [])]) ⟨[]⟩
      ⟨[(operationSlot, 1), (authorizedSlot, 1)]⟩ = false := by decide

#assert_axioms default_allows_claim
#assert_axioms claim_requires_authorized
#assert_axioms ordinary_preserved
#assert_axioms inherited_restriction_required
#assert_axioms checked_claim_over_denied_ordinary_base
#assert_axioms unproven_claim_cannot_use_permissive_base
#assert_axioms claim_cannot_escape_inherited_denial

end Minidregg.Kernel.PayClaimLaw
