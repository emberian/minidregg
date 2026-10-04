import Compiler.Tower256ConcreteBackend
import Theory.AssertAxioms

/- Objective-only commitment context, independent of historical BendTT and
its invocation/source profiles. Generic framing and circuit machinery consume
this codec; actual current admission must derive every field independently.
No default public projection of a complete result is introduced here. -/
namespace Minidregg.Compiler.ObjectiveProofContext
open Minidregg.Theory Minidregg.Theory.TypedAuthorization
open Tower256ConcreteBackend
set_option autoImplicit false

/-- Source/core/ROM/entry/plan identities selected by the actual Objective
admission producer. This codec grants no authority and supplies no execution
proof. In particular an arbitrary digest is not a source-to-ROM certificate. -/
structure Definition where
  semantic : Digest
  artifact : Digest
  program : Digest
  method : Digest
  plan : Digest
  deriving DecidableEq, Repr

def definitionStream : StreamCodec Definition :=
  StreamCodec.xmap (StreamCodec.product digestStream
    (StreamCodec.product digestStream (StreamCodec.product digestStream
    (StreamCodec.product digestStream digestStream))))
    (fun value => (value.semantic, value.artifact, value.program, value.method, value.plan))
    (fun value => ⟨value.1, value.2.1, value.2.2.1, value.2.2.2.1, value.2.2.2.2⟩)
    (by intro value; cases value; rfl)

inductive Policy where
  | privateEffects
  | publicEffects
  deriving DecidableEq, Repr

def Policy.name : Policy → String
  | .privateEffects => "public-semantic/private-input-result-v1"
  | .publicEffects => "public-semantic/public-effects-private-returns-v1"

def Policy.id (policy : Policy) : Digest :=
  (Sp800185Cshake256.hash "DREGG.OBJECTIVE-BEND.DISCLOSURE-PROFILE/v1".toUTF8.toList
    policy.name.toUTF8.toList).digest

def policyStream : StreamCodec Policy :=
  StreamCodec.xmap StreamCodec.bool
    (fun p => match p with | .privateEffects => false | .publicEffects => true)
    (fun b => if b then .publicEffects else .privateEffects)
    (by intro p; cases p <;> rfl)

/-- Public context fixed independently by admitted invocation and disclosure
law. Generation, epoch and audience identify a release context; they never
replace the current recipient's separate release authorization. -/
structure Context where
  policy : Policy
  definition : Definition
  invocation : Digest
  profile : Digest
  generation : Nat
  keyEpoch : Digest
  audience : Digest
  tariff : Digest
  capacity : List Nat
  deriving DecidableEq, Repr

def contextStream : StreamCodec Context :=
  StreamCodec.xmap (StreamCodec.product policyStream
    (StreamCodec.product definitionStream
    (StreamCodec.product digestStream (StreamCodec.product digestStream
    (StreamCodec.product StreamCodec.nat (StreamCodec.product digestStream
    (StreamCodec.product digestStream (StreamCodec.product digestStream
      (StreamCodec.list StreamCodec.nat)))))))))
    (fun c => (c.policy, c.definition, c.invocation, c.profile, c.generation,
      c.keyEpoch, c.audience, c.tariff, c.capacity))
    (fun c => ⟨c.1, c.2.1, c.2.2.1, c.2.2.2.1, c.2.2.2.2.1,
      c.2.2.2.2.2.1, c.2.2.2.2.2.2.1, c.2.2.2.2.2.2.2.1,
      c.2.2.2.2.2.2.2.2⟩)
    (by intro c; cases c; rfl)

/-- The actual randomized hash candidate; no hiding/binding bound is implied. -/
def commit (domain : String) (context : Context) (coins payload : List UInt8) : Digest :=
  (Sp800185Cshake256.hash domain.toUTF8.toList
    ((StreamCodec.product contextStream
      (StreamCodec.product bytesStream bytesStream)).encode (context, coins, payload))).digest

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


#assert_axioms preimage_injective
end Minidregg.Compiler.ObjectiveProofContext
