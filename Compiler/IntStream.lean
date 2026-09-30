/-
# Compiler.IntStream -- the one integer byte codec

Every store-coded integer (declared-effect values, Book balances, account
views) is written as the base-255 natural of its zigzag image
`EffectDeclaration.encodeInt`: nonnegatives to evens, negatives to odds.  That
map is already the one the effect digest words and the declared-action codes
use, so the byte codec and the declaration words agree on what an integer is.

Before this module there were two integer codecs that encoded differently: the
declared-effect page wrote the zigzag natural, and the Book page wrote a
`Sum Nat Nat` (a tag byte, then the magnitude).  The `Sum` codec is deleted;
cells written with it refuse to decode under the store frame, because their
layout digest names a different value codec id (`intCodecId`).
-/
import Compiler.Tower256ConcreteBackend
import Theory.EffectDeclaration

namespace Minidregg.Compiler.IntStream

open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Theory.EffectDeclaration

set_option autoImplicit false

def intStream : StreamCodec Int :=
  StreamCodec.xmap StreamCodec.nat encodeInt decodeInt decodeInt_encodeInt

/-- The declared codec id a store layout descriptor commits to. -/
def intCodecId : String := "int/zigzag-base255"

/-- The byte image is exactly the natural codec at the zigzag word. -/
theorem intStream_encode (value : Int) :
    intStream.encode value = StreamCodec.nat.encode (encodeInt value) :=
  rfl

theorem intStream_injective : Function.Injective intStream.encode := by
  intro left right same
  have decoded := intStream.decodePrefix_encode left []
  rw [same, intStream.decodePrefix_encode right []] at decoded
  exact (Prod.mk.inj (Option.some.inj decoded)).1.symm

/-- The sign is carried by the word's parity, not a tag: `-1` and `1` have the
adjacent words `1` and `2`, and their bytes differ. -/
theorem negOne_word : encodeInt (-1) = 1 := rfl

theorem one_word : encodeInt 1 = 2 := rfl

theorem sign_distinguished : intStream.encode (-1) ≠ intStream.encode 1 := by
  intro same
  have := intStream_injective same
  omega

end Minidregg.Compiler.IntStream
