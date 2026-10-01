/-
# Kernel.ProviderRouteProofs -- a refilled purse pays a user-route call its fee

P6's refill burns Book credit 1:1 into a purse; the provider purse's route
law then charges a user-route call only its per-operation fee. Joined: the
friend's credit leaves the Book exactly once (the burn), and leaves the purse
only as the fee (or nothing, for a call that never left).
-/
import Kernel.PurseRefill
import Kernel.ProviderRoute

namespace Minidregg.Kernel.ProviderRouteProofs

open Minidregg.Kernel
open Minidregg.Kernel.PayTariff
open Minidregg.Kernel.ProviderRoute
open Minidregg.Theory.CanonicalResourceKernel
open Minidregg.Theory.CredentialAuthorityState
open Minidregg.Theory.TypedAuthorization
open Minidregg.Kernel.ProviderMetering (Schedule)

set_option autoImplicit false

/-- **Refill, then one user-route call: conservation.** The refill's Book leg
burns `amount` from the payer and its purse leg adds the same `amount`; a
user-route reserve then settle on that purse consumes exactly the fee or
nothing. The friend's provider bill is not in Mini's ledger at all. -/
theorem refill_then_user_route_conserves
    {tariff : Option Tariff} {stored : Option (StoredCapability .account)}
    {subject : SubjectId} {book : Book} {purse : Option AgentGrain.State}
    {account amount gain : Nat} {plan : PurseRefill.Plan}
    (refilled : PurseRefill.decideRefill tariff stored subject book purse account amount gain =
      .ok plan)
    {schedule : Schedule} {r0 r1 r2 : ProviderRoute.State}
    {old0 st0 old1 st1 : Minidregg.Pred.State}
    (funded : r0.grain = plan.after)
    (reads0 : Reads st0 r0 r1) (reserve : Minidregg.Pred.eval (transition schedule) old0 st0 = true)
    (free0 : IsFree r0.grain.status) (user : r1.route = 1)
    (reads1 : Reads st1 r1 r2) (settle : Minidregg.Pred.eval (transition schedule) old1 st1 = true)
    (free2 : IsFree r2.grain.status) :
    (plan.batch.apply book).totalAsset plan.asset = book.totalAsset plan.asset ∧
      (plan.batch.apply book).balance account plan.asset =
        book.balance account plan.asset - Int.ofNat amount ∧
      ∃ fee : Int, (fee = 0 ∨ fee = (schedule.user : Int)) ∧
        r2.budget = PurseRefill.budget plan.before + Int.ofNat amount - fee := by
  obtain ⟨total, _, payer, _, funds, _, _, _⟩ := PurseRefill.refill_conserves refilled
  obtain ⟨held1, _, kept⟩ := user_route_holds_per_op reads0 reserve free0 user
  have fee := user_route_charges_per_op_only reads1 settle held1 user free2
  refine ⟨total, payer, charged r1 r2, fee, ?_⟩
  have start : r0.budget = PurseRefill.budget plan.before + Int.ofNat amount := by
    rw [← funds]; simp [State.budget, PurseRefill.budget, funded]
  unfold charged at kept ⊢
  omega

#assert_axioms refill_then_user_route_conserves

end Minidregg.Kernel.ProviderRouteProofs
