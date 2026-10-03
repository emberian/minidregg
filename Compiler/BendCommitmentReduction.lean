import Compiler.BendProofProjection

/- Binding for the ACTUAL salted cSHAKE framing is a reduction to an exhibited
collision, never an uninhabited globally injective compressing commitment.
No probability, random-oracle, Fiat–Shamir or hiding bound is inferred here. -/
namespace Minidregg.Compiler.BendCommitmentReduction
open Minidregg.Theory Tower256ConcreteBackend BendProofProjection
set_option autoImplicit false

def preimageCodec : StreamCodec (Context × List UInt8 × List UInt8) :=
  StreamCodec.product contextStream (StreamCodec.product bytesStream bytesStream)

def preimage (context : Context) (coins payload : List UInt8) : List UInt8 :=
  preimageCodec.encode (context, coins, payload)

/-- This carries the actual two different hash inputs, not an impossible
assumption that a fixed-width root injects every message. -/
structure Collision (domain : String) where
  left : List UInt8
  right : List UInt8
  distinct : left ≠ right
  equalDigest : (Sp800185Cshake256.hash domain.toUTF8.toList left).digest =
    (Sp800185Cshake256.hash domain.toUTF8.toList right).digest

theorem preimage_injective : Function.Injective preimageCodec.encode := by
  intro left right same
  have decodeLeft := preimageCodec.decodePrefix_encode left []
  have decodeRight := preimageCodec.decodePrefix_encode right []
  simp only [List.append_nil] at decodeLeft decodeRight
  rw [same, decodeRight] at decodeLeft
  exact (congrArg Prod.fst (Option.some.inj decodeLeft)).symm

/-- A successful equivocation with different payloads constructively supplies
a collision of the exact domain-separated hash used by the projection. This
remains a meaningful statement for finite compressing digests. -/
def collisionOfDifferentPayload (domain : String) (leftContext rightContext : Context)
    (leftCoins rightCoins leftPayload rightPayload : List UInt8)
    (different : leftPayload ≠ rightPayload)
    (same : commit domain leftContext leftCoins leftPayload =
      commit domain rightContext rightCoins rightPayload) : Collision domain where
  left := preimage leftContext leftCoins leftPayload
  right := preimage rightContext rightCoins rightPayload
  distinct := by
    intro equalBytes
    have equalValues := preimage_injective equalBytes
    exact different (congrArg (fun value : Context × List UInt8 × List UInt8 => value.2.2) equalValues)
  equalDigest := same

/-- Two actual projection openings that agree publicly but claim different
canonical input bytes exhibit an input-commitment collision. Native authority
and proof-system acceptance must still supply those exact opening relations. -/
def inputCollision (policy : Policy) (artifact : BendWorldProgramCodec.Artifact)
    (leftResult rightResult : BendInvocation.Result)
    (leftInput rightInput : List UInt8) (leftCoins rightCoins : Coins)
    (different : leftInput ≠ rightInput)
    (samePublic : project policy artifact leftResult leftInput leftCoins =
      project policy artifact rightResult rightInput rightCoins) :
    Collision "DREGG.BEND.INPUT-COMMIT/v1" := by
  apply collisionOfDifferentPayload _ (expectedContext policy artifact leftResult)
    (expectedContext policy artifact rightResult) leftCoins.input rightCoins.input
    leftInput rightInput different
  simpa only [project] using congrArg Public.inputCommitment samePublic

#assert_axioms preimage_injective
#assert_axioms collisionOfDifferentPayload
#assert_axioms inputCollision
end Minidregg.Compiler.BendCommitmentReduction
