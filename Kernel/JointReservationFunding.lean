import Kernel.JointReceiverAdmission
import Theory.AssertAxioms
namespace Minidregg.Kernel.JointReservationFunding
open Minidregg.Theory
open Minidregg.Theory.ResourceCost
open Minidregg.Compiler
open Minidregg.Kernel.DurableDataIntent
open Minidregg.Kernel.JointReservation
open Minidregg.Kernel.JointReceiverAdmission
set_option autoImplicit false

/-- An admitted source operation pays its actual charge first. All selected
holds and independent maintenance remain funded in the resulting snapshot.
The theorem is pointwise for every lane, not one closed happy-path case. -/
theorem held_funded_after_actual_debit {rootBytes : List UInt8 → TypedAuthorization.Digest}
    (before : DataSnapshot rootBytes) (intent : DataIntent rootBytes) (held maintenance : Charge)
    (funded : Charge.fundedCheck (held + maintenance + intent.exactCharge) before.model.available = true) :
    held + maintenance ≤ (DataSnapshot.install before intent).model.available := by
  have budget := (Charge.fundedCheck_eq_true_iff _ _).mp funded
  intro lane
  change held lane + maintenance lane ≤ before.model.available lane - intent.exactCharge lane
  exact Nat.le_sub_of_add_le (budget lane)

/-- The reservation constructor checks the post-fee obligation, hence an exact
fit before paying the reservation method cannot strand completion maintenance. -/
theorem reservation_post_funded {F : Type} [Field F] [DecidableEq F]
    {deployment : DeclaredResourceController.Deployment}
    {profile : CanonicalRuntimeProfile.Profile F}
    {ambient : DeclaredResourceController.Ambient}
    {durable : DeclaredResourceController.Durable}
    (r : Reserved deployment profile ambient durable) :
    heldCharge r.reservation.domain r.after.reservations + r.after.maintenanceReserve ≤
      (DataSnapshot.install durable.snapshot r.intent).model.available :=
  held_funded_after_actual_debit durable.snapshot r.intent _ _ r.funded

/-- Charging the explicit reserve operation preserves every lane charged by
its independently accepted current source control method. -/
theorem reserve_preserves_control_charge {rootBytes : List UInt8 → TypedAuthorization.Digest}
    (bytes : List UInt8) (control effect : DataIntent rootBytes) (guards : List ReadGuard) :
    control.exactCharge ≤ reserveCharge bytes control effect guards := by
  intro lane
  exact Nat.le_add_right _ _

#assert_axioms held_funded_after_actual_debit
#assert_axioms reservation_post_funded
#assert_axioms reserve_preserves_control_charge
end Minidregg.Kernel.JointReservationFunding
