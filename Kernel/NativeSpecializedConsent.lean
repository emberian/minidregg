/- Same-source consent for operator-proposed specialized native plans.
A caller retains its request locally and admits a warm source prefix independently.
This module uses the actual loaded native planners and their canonical whole-plan
codecs. It has no operator Bool, sparse state defaults, or planner semantic twin.
-/
import Kernel.NativeClientConsent
import Kernel.NativeHostPayClaims

namespace Minidregg.Kernel.NativeSpecializedConsent
open Minidregg.Compiler Minidregg.Kernel
open Minidregg.Compiler.Tower256ConcreteBackend
set_option autoImplicit false

/-- A byte-level gate is useful only after the same native planner produced the
expected whole plan from the retained request and independently verified source. -/
structure ExactPlan (expected candidate : List UInt8) : Type where
  private mk ::
  exact : expected = candidate

def checkExact (expected candidate : List UInt8) : Except String (ExactPlan expected candidate) :=
  if h : expected = candidate then .ok ⟨h⟩
  else .error "operator plan differs from complete local native preparation"

theorem changed_plan_refused (expected candidate : List UInt8) (changed : expected ≠ candidate) :
    checkExact expected candidate = .error "operator plan differs from complete local native preparation" := by
  simp [checkExact, changed]

def supported (operation : UInt8) : Bool :=
  [86, 92, 96, 103, 108, 113, 117, 123, 126, 140, 160, 170, 183, 210].contains operation

private def splitPair (payload : List UInt8) : IO (List UInt8 × List UInt8) := do
  unless payload.length ≥ 4 do throw (IO.userError "truncated specialized request pair")
  let length := (payload.take 4).foldr (fun b rest => b.toNat + 256 * rest) 0
  unless length ≤ payload.length - 4 do throw (IO.userError "specialized request pair exceeds payload")
  pure ((payload.drop 4).take length, payload.drop (4 + length))

private def admitted {α ε : Type} (result : Except ε α) : IO α :=
  match result with
  | .ok value => pure value
  | .error _ => throw (IO.userError "local authenticated specialized preparation refused")

/-- The exact production functions and production encoders used by Host.Main.
No source mutation or signature creation occurs here. -/
def expectedPlanBytes (config : NativeHost.Config) {target : NativeHost.Durable}
    (basis : ConsentAnchor.Basis config target) (operation : UInt8)
    (request : List UInt8) : IO (List UInt8) := do
  let opened := basis.opened
  match operation with
  | 86 =>
      let (observation, command) ← splitPair request
      let plan ← admitted (← NativeHost.enrollmentPlanAuthorizedLoaded config opened observation command)
      pure (ParticipantKeyEnrollment.signingPlanCodec.encode plan)
  | 92 =>
      let (observation, command) ← splitPair request
      let plan ← admitted (← NativeHost.provisionPlanAuthorizedLoaded config opened observation command)
      pure (ParticipantFactoryProvisioning.signingPlanCodec.encode plan)
  | 96 =>
      let (observation, draft) ← splitPair request
      let plan ← admitted (← NativeHost.fleetPlanAuthorizedLoaded config opened observation draft)
      pure (FleetTurn.signingPlanCodec.encode plan)
  | 103 =>
      pure (PayCellDomain.signingPlanCodec.encode (← IO.ofExcept (NativeHost.payPlanLoaded config opened request)))
  | 108 =>
      pure (PayCellDomain.signingPlanCodec.encode (← IO.ofExcept (NativeHost.payObservationPlanLoaded config opened request)))
  | 113 =>
      pure (PayCellDomain.signingPlanCodec.encode (← IO.ofExcept (NativeHost.payRefillPlanLoaded config opened request)))
  | 117 =>
      pure (PayCellDomain.signingPlanCodec.encode (← IO.ofExcept (← NativeHost.payEnrolPlanCurrentLoaded config opened request)))
  | 123 =>
      pure (RealmWellCodec.signingPlanCodec.encode (← IO.ofExcept (NativeHost.wellPlanLoaded config opened request)))
  | 126 =>
      pure (ClockTickReceiver.signingPlanCodec.encode (← IO.ofExcept (NativeHost.clockPlanLoaded config opened request)))
  | 140 =>
      pure (SubjectKeyRotation.signingPlanCodec.encode (← IO.ofExcept (NativeHost.rotationPlanLoaded config opened request)))
  | 160 =>
      pure (PayCellDomain.signingPlanCodec.encode (← IO.ofExcept (NativeHost.jobMoneyPlanLoaded config opened request)))
  | 170 =>
      pure (CertifyReceiver.signingPlanCodec.encode (← IO.ofExcept (NativeHost.certifyPlanLoaded config opened request)))
  | 183 =>
      pure (NativeHost.claimSigningPlanCodec.encode (← IO.ofExcept (NativeHost.payClaimPlanLoaded config opened request)))
  | 210 =>
      pure (ObjectiveActivityReceiver.signingPlanCodec.encode
        (← IO.ofExcept (NativeHost.activityPlanLoaded config opened request)))
  | _ => throw (IO.userError "specialized consent operation is unsupported")

end Minidregg.Kernel.NativeSpecializedConsent
