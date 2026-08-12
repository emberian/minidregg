/-
# Loom.SpongeIndiffPrefixConflict — exact construction consistency event

The corrected construction interpreter can reject only when a primitive edge
and the lazy RO have already assigned different rate values to the same rooted
message prefix.  This module exposes that event proof-relevantly for the
single-prefix kernel and proves an exact iff with interpreter rejection.

This is the atom the adaptive multi-prefix coupling must union and price.  It
is not called a hash collision: it is a consistency failure between two lazy
sample schedules on the same message/edge incidence.  Fresh RO or primitive
entries cannot trigger it, and an agreeing pair replays successfully.
-/
import Loom.SpongeIndiffPrefixWalk

namespace Minidregg.Loom

section PrefixConflict

variable {Rate Cap : Type} [AddCommGroup Rate] [DecidableEq Rate]

/-- One exact already-sampled disagreement at the next rooted prefix. -/
def PrefixConflict (ro : Oracle (List Rate) Rate)
    (primitive : Oracle (Rate × Cap) (Rate × Cap))
    (state : Rate × Cap) (seen : List Rate) (block : Rate) : Prop :=
  ∃ edgeValue roValue,
    primitive.lookup (state.1 + block, state.2) = some edgeValue ∧
      ro.lookup (seen ++ [block]) = some roValue ∧
      edgeValue.1 ≠ roValue

/-- For one remaining block with exact coin counts, construction rejection is
equivalent to the exact already-sampled prefix conflict. -/
theorem programPrefixes_singleton_none_iff_conflict
    (ro : Oracle (List Rate) Rate)
    (primitive : Oracle (Rate × Cap) (Rate × Cap))
    (state : Rate × Cap) (seen : List Rate)
    (block rateCoin : Rate) (capacityCoin : Cap) :
    programPrefixes ro primitive state seen [block] [rateCoin]
        [capacityCoin] = none ↔
      PrefixConflict ro primitive state seen block := by
  unfold PrefixConflict
  simp only [programPrefixes]
  cases hedge : primitive.lookup (state.1 + block, state.2) with
  | none =>
      rw [hedge]
      simp only
      constructor
      · intro hnone
        simp [programPrefixes] at hnone
      · rintro ⟨edgeValue, roValue, hedge', -⟩
        rw [hedge] at hedge'
        contradiction
  | some edgeValue =>
      rw [hedge]
      simp only
      cases hro : ro.lookup (seen ++ [block]) with
      | none =>
          rw [Oracle.respond_fresh_fst hro]
          simp only [if_pos rfl, programPrefixes, reduceCtorEq]
          rintro ⟨value, roValue, -, hro', -⟩
          rw [hro] at hro'
          contradiction
      | some roValue =>
          rw [Oracle.respond_hit hro]
          by_cases hagree : edgeValue.1 = roValue
          · rw [if_pos hagree]
            simp only [programPrefixes, reduceCtorEq, false_iff]
            rintro ⟨value, value', hedge', hro', hne⟩
            have hvalue : value = edgeValue := by
              exact Option.some.inj (hedge'.symm.trans hedge)
            have hvalue' : value' = roValue := by
              exact Option.some.inj (hro'.symm.trans hro)
            subst value
            subst value'
            exact hne hagree
          · rw [if_neg hagree]
            constructor
            · intro _
              exact ⟨edgeValue, roValue, hedge, hro, hagree⟩
            · intro _
              rfl

/-- A fresh RO prefix cannot be a consistency conflict, regardless of the
primitive table. -/
theorem no_prefixConflict_of_ro_fresh
    (ro : Oracle (List Rate) Rate)
    (primitive : Oracle (Rate × Cap) (Rate × Cap))
    (state : Rate × Cap) (seen : List Rate) (block : Rate)
    (hfresh : ro.lookup (seen ++ [block]) = none) :
    ¬ PrefixConflict ro primitive state seen block := by
  rintro ⟨edgeValue, roValue, hedge, hro, hne⟩
  rw [hfresh] at hro
  contradiction

/-- A fresh primitive edge cannot be a consistency conflict, regardless of
the RO table. -/
theorem no_prefixConflict_of_primitive_fresh
    (ro : Oracle (List Rate) Rate)
    (primitive : Oracle (Rate × Cap) (Rate × Cap))
    (state : Rate × Cap) (seen : List Rate) (block : Rate)
    (hfresh : primitive.lookup (state.1 + block, state.2) = none) :
    ¬ PrefixConflict ro primitive state seen block := by
  rintro ⟨edgeValue, roValue, hedge, hro, hne⟩
  rw [hfresh] at hedge
  contradiction

end PrefixConflict

/-- info: 'Minidregg.Loom.programPrefixes_singleton_none_iff_conflict' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms programPrefixes_singleton_none_iff_conflict
/-- info: 'Minidregg.Loom.no_prefixConflict_of_ro_fresh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms no_prefixConflict_of_ro_fresh

end Minidregg.Loom
