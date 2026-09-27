/-
Physical hosting profile for the first resident signed-SPK adapter. This is
not the generic BEGIN-v2 admission law: historical v2 ingress with other
opaque identities keeps its original replay meaning, but cannot be launched
by this host adapter.
-/
import Kernel.ApplicationLifecycleBeginV2Ingress
import Kernel.ApplicationLifecycleBeginV3Ingress
import Kernel.ApplicationLifecycleClaimProjection

namespace Minidregg.Kernel.ApplicationLifecycleResidentProfile

open Minidregg.Kernel

set_option autoImplicit false

def processIdentity (app : Nat) (generation : Int) : List UInt8 :=
  s!"mini-spk-a{app}-g{generation}.service".toUTF8.toList

def beginMatches (ingress : ApplicationLifecycleBeginV2Ingress.Ingress) : Bool :=
  ingress.base.source.imageIdentity == ingress.descriptor.imageIdentity &&
  ingress.base.source.processIdentity ==
    processIdentity ingress.base.source.app ingress.base.source.processGeneration

/-- A v3 STOP advances the app operation generation, but fences the unit from
the already-running START generation. The replay's admitted-running witness
binds that prior unit and exact incarnation. Historical v2 matching is
unchanged. -/
def beginMatchesV3 (ingress : ApplicationLifecycleBeginV3Ingress.Ingress) : Bool :=
  let source := ingress.base.source
  source.imageIdentity == ingress.descriptor.package.imageIdentity &&
    source.processIdentity == processIdentity source.app
      (if source.kind == .stop then source.before.generation
       else source.processGeneration)

def claimMatches (claim : ApplicationLifecycleClaimProjection.CommittedV2) : Bool :=
  claim.core.source.begin.source.imageIdentity == claim.descriptor.imageIdentity &&
  claim.core.source.begin.source.processIdentity ==
    processIdentity claim.core.source.begin.source.app
      claim.core.source.begin.source.processGeneration

theorem beginMatches_image {ingress : ApplicationLifecycleBeginV2Ingress.Ingress}
    (matching : beginMatches ingress = true) :
    ingress.base.source.imageIdentity = ingress.descriptor.imageIdentity := by
  simp only [beginMatches, Bool.and_eq_true, beq_iff_eq] at matching
  exact matching.1

theorem claimMatches_image {claim : ApplicationLifecycleClaimProjection.CommittedV2}
    (matching : claimMatches claim = true) :
    claim.core.source.begin.source.imageIdentity = claim.descriptor.imageIdentity := by
  simp only [claimMatches, Bool.and_eq_true, beq_iff_eq] at matching
  exact matching.1

theorem beginMatches_wrong_image (ingress : ApplicationLifecycleBeginV2Ingress.Ingress)
    (different : ingress.base.source.imageIdentity ≠ ingress.descriptor.imageIdentity) :
    beginMatches ingress = false := by
  simp [beginMatches, different]

theorem claimMatches_wrong_unit (claim : ApplicationLifecycleClaimProjection.CommittedV2)
    (different : claim.core.source.begin.source.processIdentity ≠
      processIdentity claim.core.source.begin.source.app
        claim.core.source.begin.source.processGeneration) :
    claimMatches claim = false := by
  simp [claimMatches, different]

end Minidregg.Kernel.ApplicationLifecycleResidentProfile
