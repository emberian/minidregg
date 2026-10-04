/-
Physical hosting profile for the first resident signed-SPK adapter. This is
not the generic BEGIN-v2 admission law: historical v2 ingress with other
opaque identities keeps its original replay meaning, but cannot be launched
by this host adapter.

The resident unit name carries the Store: two Stores on one physical host
(a scratch copy beside a live world, or two tenants) may both hold app 7101 at
generation 2 and must not name the same unit. The Store is the deployment's
genesis seed identity (`Config.expectedSeed`), fixed for the deployment's life
and unchanged by profile upgrades; `storeTag` is its low 64 bits in 16
lowercase hex digits, the same key the physical host uses for volume, slice
and journal paths (it reads it from the pinned Host's `profile` output, never
recomputes it).
-/
import Kernel.ApplicationLifecycleBeginV2Ingress
import Kernel.ApplicationLifecycleBeginV3Ingress
import Kernel.ApplicationLifecycleClaimProjection

namespace Minidregg.Kernel.ApplicationLifecycleResidentProfile

open Minidregg.Kernel
open Minidregg.Theory.TypedAuthorization (Digest)

set_option autoImplicit false

/-- Sixteen lowercase hex digits of the low 64 bits of a Store's genesis seed
identity. -/
def storeTag (store : Digest) : String :=
  let digits := Nat.toDigits 16 (store.value % 2 ^ 64)
  String.ofList (List.replicate (16 - digits.length) '0' ++ digits)

/-- The resident unit: `mini-spk-s<storeTag>-a<app>-g<generation>.service`. -/
def unitName (store : Digest) (app : Nat) (generation : Int) : String :=
  "mini-spk-s" ++ storeTag store ++ "-a" ++ toString app ++ "-g" ++ toString generation ++
    ".service"

def processIdentity (store : Digest) (app : Nat) (generation : Int) : List UInt8 :=
  (unitName store app generation).toUTF8.toList

/-- The tag is always exactly sixteen digits, so the name's fields are
delimited by position as well as by their separators. -/
theorem storeTag_length (store : Digest) : (storeTag store).length = 16 := by
  have below : store.value % 2 ^ 64 < 16 ^ 16 := by
    have := Nat.mod_lt store.value (show 0 < 2 ^ 64 by positivity)
    calc store.value % 2 ^ 64 < 2 ^ 64 := this
      _ = 16 ^ 16 := by norm_num
  have bounded := Nat.toDigits_length 16 (store.value % 2 ^ 64) 16 (by decide) below
  simp only [storeTag, String.length_ofList, List.length_append, List.length_replicate]
  omega

/-- Two Stores whose tags differ name different units for the same app and
generation: a scratch copy of a world never claims the live world's unit. -/
theorem unitName_separates_stores (store other : Digest) (app : Nat) (generation : Int)
    (tags : storeTag store ≠ storeTag other) :
    unitName store app generation ≠ unitName other app generation := by
  intro same
  apply tags
  apply String.ext
  have lists := congrArg String.toList same
  simp only [unitName, String.toList_append, List.append_assoc] at lists
  exact List.append_cancel_right (List.append_cancel_left lists)

def beginMatches (store : Digest) (ingress : ApplicationLifecycleBeginV2Ingress.Ingress) : Bool :=
  ingress.base.source.imageIdentity == ingress.descriptor.imageIdentity &&
  ingress.base.source.processIdentity ==
    processIdentity store ingress.base.source.app ingress.base.source.processGeneration

/-- A v3 STOP advances the app operation generation, but fences the unit from
the already-running START generation. The replay's admitted-running witness
binds that prior unit and exact incarnation. Historical v2 matching is
unchanged. -/
def beginMatchesV3 (store : Digest) (ingress : ApplicationLifecycleBeginV3Ingress.Ingress) : Bool :=
  let source := ingress.base.source
  source.imageIdentity == ingress.descriptor.package.imageIdentity &&
    source.processIdentity == processIdentity store source.app
      (if source.kind == .stop then source.before.generation
       else source.processGeneration)

def claimMatches (store : Digest) (claim : ApplicationLifecycleClaimProjection.CommittedV2) : Bool :=
  claim.core.source.begin.source.imageIdentity == claim.descriptor.imageIdentity &&
  claim.core.source.begin.source.processIdentity ==
    processIdentity store claim.core.source.begin.source.app
      claim.core.source.begin.source.processGeneration

theorem beginMatches_image {store : Digest} {ingress : ApplicationLifecycleBeginV2Ingress.Ingress}
    (matching : beginMatches store ingress = true) :
    ingress.base.source.imageIdentity = ingress.descriptor.imageIdentity := by
  simp only [beginMatches, Bool.and_eq_true, beq_iff_eq] at matching
  exact matching.1

theorem claimMatches_image {store : Digest} {claim : ApplicationLifecycleClaimProjection.CommittedV2}
    (matching : claimMatches store claim = true) :
    claim.core.source.begin.source.imageIdentity = claim.descriptor.imageIdentity := by
  simp only [claimMatches, Bool.and_eq_true, beq_iff_eq] at matching
  exact matching.1

theorem beginMatches_wrong_image (store : Digest) (ingress : ApplicationLifecycleBeginV2Ingress.Ingress)
    (different : ingress.base.source.imageIdentity ≠ ingress.descriptor.imageIdentity) :
    beginMatches store ingress = false := by
  simp [beginMatches, different]

/-- A claim whose unit is not THIS Store's name for its app and generation is
outside the profile: in particular a claim another Store authored for the same
app and generation, whose unit carries the other Store's tag. -/
theorem claimMatches_wrong_unit (store : Digest) (claim : ApplicationLifecycleClaimProjection.CommittedV2)
    (different : claim.core.source.begin.source.processIdentity ≠
      processIdentity store claim.core.source.begin.source.app
        claim.core.source.begin.source.processGeneration) :
    claimMatches store claim = false := by
  simp [claimMatches, different]


/-- info: 'Minidregg.Kernel.ApplicationLifecycleResidentProfile.storeTag_length' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms storeTag_length
/-- info: 'Minidregg.Kernel.ApplicationLifecycleResidentProfile.unitName_separates_stores' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms unitName_separates_stores

end Minidregg.Kernel.ApplicationLifecycleResidentProfile
