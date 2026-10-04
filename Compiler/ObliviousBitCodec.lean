/- Language-independent physical bit codec and exact front-consumption laws.
Extracted from the earlier controller work so Objective and other backends
share the implementation without importing a retired language or heap. -/
import Init.Data.BitVec.Lemmas
import Theory.AssertAxioms

namespace Minidregg.Compiler.ObliviousBitCodec
set_option autoImplicit false

def bits (width value : Nat) : List Bool := (List.range width).map value.testBit
abbrev Read (α : Type) := StateT (List Bool) Option α

def takeBits (count : Nat) : Read (List Bool) := fun input =>
  if count > input.length then none else some (input.take count,input.drop count)

def nat (width : Nat) : Read Nat := do
  let data ← takeBits width
  pure (BitVec.ofBoolListLE data).toNat

theorem bits_length (width value : Nat) : (bits width value).length = width := by simp [bits]

theorem bits_read_modulo (width value : Nat) :
    (BitVec.ofBoolListLE (bits width value)).toNat = value % 2^width := by
  apply Nat.eq_of_testBit_eq
  intro bit
  change (BitVec.ofBoolListLE (bits width value)).getLsbD bit = _
  rw [BitVec.getLsbD_ofBoolListLE, List.getD_eq_getElem?_getD, Nat.testBit_mod_two_pow]
  by_cases inside : bit < width
  · simp [bits, List.getElem?_range inside, inside]
  · have beyond : (List.range width)[bit]? = none :=
      List.getElem?_eq_none (by simp; omega)
    simp [bits,beyond,inside]

theorem bits_read_exact {width value : Nat} (fits : value < 2^width) :
    (BitVec.ofBoolListLE (bits width value)).toNat = value := by
  rw [bits_read_modulo,Nat.mod_eq_of_lt fits]

theorem read_bind {α β : Type} (read : Read α) (next : α → Read β) (input : List Bool) :
    (read >>= next) input = match read input with
      | none => none
      | some (value,rest) => next value rest := by
  cases result : read input with
  | none => simp [Bind.bind,StateT.bind,Option.bind,result]
  | some pair => cases pair; simp [Bind.bind,StateT.bind,Option.bind,result]

theorem read_map {α β : Type} (f : α → β) (read : Read α) (input : List Bool) :
    (f <$> read) input = match read input with
      | none => none
      | some (value,rest) => some (f value,rest) := by
  cases result : read input with
  | none => simp [Functor.map,StateT.map,Option.map,result]
  | some pair => cases pair; simp [Functor.map,StateT.map,Option.map,result]

theorem read_pure {α : Type} (value : α) (input : List Bool) :
    (pure value : Read α) input = some (value,input) := rfl
theorem read_get (input : List Bool) : (get : Read (List Bool)) input = some (input,input) := rfl
theorem read_set (value input : List Bool) : (set value : Read PUnit) input = some ((),value) := rfl

theorem takeBits_append (front rest : List Bool) :
    takeBits front.length (front ++ rest) = some (front,rest) := by
  have room : ¬ front.length + rest.length < front.length := by omega
  simp [takeBits,room]

theorem nat_append (width value : Nat) (rest : List Bool) (fits : value < 2^width) :
    nat width (bits width value ++ rest) = some (value,rest) := by
  have take : takeBits width (bits width value ++ rest) = some (bits width value,rest) := by
    simpa only [bits_length] using takeBits_append (bits width value) rest
  unfold nat
  rw [read_bind,take]
  change some ((BitVec.ofBoolListLE (bits width value)).toNat,rest) = _
  rw [bits_read_exact fits]

#assert_axioms bits_length
#assert_axioms bits_read_modulo
#assert_axioms bits_read_exact
#assert_axioms takeBits_append
#assert_axioms nat_append
end Minidregg.Compiler.ObliviousBitCodec

