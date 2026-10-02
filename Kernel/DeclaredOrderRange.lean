/-
# `R` on a declared resource's projected step

`NativeHostProfile.order_agrees_with_eval_on_R` asks every integer the law's
step carries to lie in `R = [-2^123, 2^123)`. A declared resource's projection
carries more than its field values: each field's `delta` and every pair's
`a + b - oldA - oldB` (`DeclaredResourceProjection.scalarSlots`). A pair delta
is a sum of four field values, so field values in `[-2^121, 2^121)` put every
projected slot in `R` (`scalarSlots_inR`). That is the band a friend's field
values are decided in: every signed and unsigned 64-bit value, with 57 bits to
spare.

A value outside it is still fail-closed. Outside the order width it is refused
as `law-input-range` naming the clause; two projected integers with the same
image in `ZMod (2^127 - 1)` (only possible beyond `2^126`, e.g. a pair delta of
`2^127 ≡ 1`) are refused as `law-input-range` naming the two integers.
-/
import Kernel.DeclaredResourceProjection
import Compiler.NativeHostProfile

namespace Minidregg.Kernel.DeclaredOrderRange

open Minidregg.Compiler
open Minidregg.Kernel.DeclaredResourceProjection

set_option autoImplicit false

/-- The bound on a declared field value. -/
def fieldBound : Int := 2 ^ 121

/-- `[-2^121, 2^121)`: the field values whose every projected slot lies in `R`. -/
abbrev InFieldR (x : Int) : Prop := InBand fieldBound x

theorem get_some_mem {xs : Values} {k : Nat} {v : Int} (h : DeclaredResourceProjection.get xs k = some v) :
    ∃ p ∈ xs, p.2 = v := by
  unfold DeclaredResourceProjection.get at h
  cases hf : xs.find? (fun p => p.1 == k) with
  | none => simp [hf] at h
  | some pr =>
      simp only [hf, Option.map_some, Option.some.injEq] at h
      exact ⟨pr, List.mem_of_find?_eq_some hf, h⟩

private theorem bounds (x : Int) (h : InFieldR x) : -(2 : Int) ^ 121 ≤ x ∧ x < 2 ^ 121 := h

/-- Field values in `[-2^121, 2^121)` put every projected slot (fields, deltas, pair
deltas) in `R`. -/
theorem scalarSlots_inR (before after : Values)
    (hb : ∀ p ∈ before, InFieldR p.2) (ha : ∀ p ∈ after, InFieldR p.2) :
    ∀ s ∈ scalarSlots before after, NativeHostProfile.InR s.2 := by
  have P : (2 : Int) ^ 123 = 4 * 2 ^ 121 := by norm_num
  intro s hs
  simp only [scalarSlots, List.mem_append, List.mem_map, List.mem_filterMap,
    List.mem_flatMap] at hs
  show -(2 : Int) ^ 123 ≤ s.2 ∧ s.2 < 2 ^ 123
  rw [P]
  generalize hQ : (2 : Int) ^ 121 = Q
  have hQpos : 0 < Q := by rw [← hQ]; positivity
  rcases hs with ((⟨p, hp, rfl⟩ | ⟨p, hp, rfl⟩) | ⟨p, hp, hsome⟩) | ⟨a, hamem, b, hbmem, hsome⟩
  · obtain ⟨l, u⟩ := bounds _ (hb p hp); rw [hQ] at l u; dsimp only; constructor <;> omega
  · obtain ⟨l, u⟩ := bounds _ (ha p hp); rw [hQ] at l u; dsimp only; constructor <;> omega
  · cases hg : DeclaredResourceProjection.get before p.1 with
    | none => simp [hg] at hsome
    | some old =>
        simp only [hg, Option.map_some, Option.some.injEq] at hsome
        subst hsome
        obtain ⟨q, hq, rfl⟩ := get_some_mem hg
        obtain ⟨l1, u1⟩ := bounds _ (ha p hp)
        obtain ⟨l2, u2⟩ := bounds _ (hb q hq)
        rw [hQ] at l1 u1 l2 u2
        dsimp only; constructor <;> omega
  · cases hgA : DeclaredResourceProjection.get before a.1 with
    | none => simp [hgA] at hsome
    | some oldA =>
      cases hgB : DeclaredResourceProjection.get before b.1 with
      | none => simp [hgA, hgB] at hsome
      | some oldB =>
          simp only [hgA, hgB, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
            Option.some.injEq] at hsome
          subst hsome
          obtain ⟨qa, hqa, rfl⟩ := get_some_mem hgA
          obtain ⟨qb, hqb, rfl⟩ := get_some_mem hgB
          obtain ⟨l1, u1⟩ := bounds _ (ha a hamem)
          obtain ⟨l2, u2⟩ := bounds _ (ha b hbmem)
          obtain ⟨l3, u3⟩ := bounds _ (hb qa hqa)
          obtain ⟨l4, u4⟩ := bounds _ (hb qb hqb)
          rw [hQ] at l1 u1 l2 u2 l3 u3 l4 u4
          dsimp only; constructor <;> omega

/-- Every unsigned 64-bit field value is in the field band. -/
theorem uint64_inFieldR (x : Int) (h0 : 0 ≤ x) (h1 : x < 2 ^ 64) : InFieldR x := by
  refine ⟨?_, ?_⟩ <;> norm_num [fieldBound] at * <;> omega

/-- `0` is in the field range. -/
theorem zero_inFieldR : InFieldR 0 := by decide

/-- The field range is half-open: its bound is outside it. -/
theorem fieldBound_not_inFieldR : ¬ InFieldR fieldBound := by decide

#assert_axioms scalarSlots_inR
#assert_axioms zero_inFieldR
#assert_axioms fieldBound_not_inFieldR

end Minidregg.Kernel.DeclaredOrderRange
