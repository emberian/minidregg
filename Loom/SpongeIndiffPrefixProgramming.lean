/-
# Loom.SpongeIndiffPrefixProgramming — construction-driven prefix programming

A construction query on `m = [m₀, …, mₙ]` exposes more than the final sponge
value.  The distinguisher may later ask any prefix as a construction query, so
the primitive edge after every prefix must squeeze to that prefix's RO answer.
Programming only the final edge is insufficient.

This module gives the operational semantics needed by an honest hybrid.  It
walks the message from the IV, lazily samples one RO answer for each nonempty
prefix, and programs the corresponding fresh primitive edge to
`(RO(prefix), freshCapacity)`.  A pre-existing edge must already have that
rate or the execution fails closed.  Successful execution therefore consumes
exactly one rate coin and one capacity coin per message block.

The runner is deterministic from its explicit coins and tables.  It does not
yet assign a probability distribution to variable-length coin streams or
prove the final random-permutation switch.
-/
import Loom.SpongeIndiffLazyHybrid

namespace Minidregg.Loom

section PrefixProgramming

variable {Rate Cap : Type} [AddCommGroup Rate] [DecidableEq Rate]

/-- State returned after programming all nonempty prefixes. -/
structure PrefixProgramState (Rate Cap : Type) where
  state : Rate × Cap
  ro : Oracle (List Rate) Rate
  primitive : Oracle (Rate × Cap) (Rate × Cap)

/-- Program every nonempty extension of `prefix` in `message`.  `state` is the
primitive state reached by `prefix`; `rateCoins` and `capacityCoins` must have
exactly the remaining message length. -/
noncomputable def programPrefixes
    (ro : Oracle (List Rate) Rate)
    (primitive : Oracle (Rate × Cap) (Rate × Cap))
    (state : Rate × Cap) (seen : List Rate) :
    List Rate → List Rate → List Cap → Option (PrefixProgramState Rate Cap)
  | [], [], [] => some ⟨state, ro, primitive⟩
  | [], _, _ => none
  | _ :: _, [], _ => none
  | _ :: _, _, [] => none
  | x :: xs, rateCoin :: rateCoins, capacityCoin :: capacityCoins =>
      let nextPrefix := seen ++ [x]
      let roReply := ro.respond nextPrefix rateCoin
      let key : Rate × Cap := (state.1 + x, state.2)
      match hlookup : primitive.lookup key with
      | some value =>
          if value.1 = roReply.1 then
            programPrefixes roReply.2 primitive value nextPrefix xs
              rateCoins capacityCoins
          else none
      | none =>
          let value : Rate × Cap := (roReply.1, capacityCoin)
          let primitiveReply := primitive.respond key value
          programPrefixes roReply.2 primitiveReply.2 primitiveReply.1
            nextPrefix xs rateCoins capacityCoins

/-- Public construction entry point, rooted at `iv` and the empty prefix. -/
noncomputable def programConstruction
    (iv : Rate × Cap) (ro : Oracle (List Rate) Rate)
    (primitive : Oracle (Rate × Cap) (Rate × Cap))
    (message rateCoins : List Rate) (capacityCoins : List Cap) :
    Option (PrefixProgramState Rate Cap) :=
  if message.isEmpty then none
  else programPrefixes ro primitive iv [] message rateCoins capacityCoins

/-- Successful prefix programming consumes exactly one rate coin and one
capacity coin per remaining message block. -/
theorem programPrefixes_some_lengths
    (ro : Oracle (List Rate) Rate)
    (primitive : Oracle (Rate × Cap) (Rate × Cap))
    (state : Rate × Cap) (seen : List Rate) :
    ∀ {message rateCoins : List Rate} {capacityCoins : List Cap} {result},
      programPrefixes ro primitive state seen message rateCoins capacityCoins =
        some result →
      message.length = rateCoins.length ∧
        message.length = capacityCoins.length := by
  intro message
  induction message generalizing ro primitive state seen with
  | nil =>
      intro rateCoins capacityCoins result h
      cases rateCoins <;> cases capacityCoins <;> simp [programPrefixes] at h ⊢
  | cons x xs ih =>
      intro rateCoins capacityCoins result h
      cases rateCoins with
      | nil => simp [programPrefixes] at h
      | cons rateCoin rateCoins =>
          cases capacityCoins with
          | nil => simp [programPrefixes] at h
          | cons capacityCoin capacityCoins =>
              simp only [programPrefixes] at h
              let nextPrefix := seen ++ [x]
              let roReply := ro.respond nextPrefix rateCoin
              let key : Rate × Cap := (state.1 + x, state.2)
              cases hlookup : primitive.lookup key with
              | some value =>
                  by_cases heq : value.1 = roReply.1
                  · have htail : programPrefixes roReply.2 primitive value
                        nextPrefix xs rateCoins capacityCoins = some result := by
                      simpa [nextPrefix, roReply, key, hlookup, heq] using h
                    obtain ⟨hrate, hcap⟩ :=
                      ih (ro := roReply.2) (primitive := primitive)
                        (state := value) (seen := nextPrefix) htail
                    exact ⟨by simp [hrate], by simp [hcap]⟩
                  · simp [nextPrefix, roReply, key, hlookup, heq] at h
              | none =>
                  let value : Rate × Cap := (roReply.1, capacityCoin)
                  let primitiveReply := primitive.respond key value
                  have htail : programPrefixes roReply.2 primitiveReply.2
                      primitiveReply.1 nextPrefix xs rateCoins capacityCoins =
                        some result := by
                    simpa [nextPrefix, roReply, key, hlookup, value,
                      primitiveReply] using h
                  obtain ⟨hrate, hcap⟩ :=
                    ih (ro := roReply.2) (primitive := primitiveReply.2)
                      (state := primitiveReply.1) (seen := nextPrefix) htail
                  exact ⟨by simp [hrate], by simp [hcap]⟩

/-- Successful public construction has exact message/rate/capacity lengths. -/
theorem programConstruction_some_lengths
    (iv : Rate × Cap) (ro : Oracle (List Rate) Rate)
    (primitive : Oracle (Rate × Cap) (Rate × Cap))
    (message rateCoins : List Rate) (capacityCoins : List Cap) {result}
    (h : programConstruction iv ro primitive message rateCoins capacityCoins =
      some result) :
    message.length = rateCoins.length ∧ message.length = capacityCoins.length := by
  unfold programConstruction at h
  split at h
  · contradiction
  · exact programPrefixes_some_lengths ro primitive iv [] h

/-- One fresh block is programmed exactly to the singleton prefix's RO answer
and the supplied capacity coin. -/
theorem programConstruction_singleton_fresh
    (iv : Rate × Cap) (ro : Oracle (List Rate) Rate)
    (primitive : Oracle (Rate × Cap) (Rate × Cap))
    (x rateCoin : Rate) (capacityCoin : Cap)
    (hfresh : primitive.lookup (iv.1 + x, iv.2) = none) :
    programConstruction iv ro primitive [x] [rateCoin] [capacityCoin] =
      some ⟨((ro.respond [x] rateCoin).1, capacityCoin),
        (ro.respond [x] rateCoin).2,
        (primitive.respond (iv.1 + x, iv.2)
          ((ro.respond [x] rateCoin).1, capacityCoin)).2⟩ := by
  unfold programConstruction
  simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte,
    programPrefixes]
  rw [hfresh]
  simp only
  rw [Oracle.respond_fresh_fst hfresh]
  rfl

/-- A pre-existing final edge with the wrong rate is rejected even when its
capacity is otherwise usable.  The consistency test is load-bearing. -/
theorem programConstruction_singleton_wrong_rate
    (iv : Rate × Cap) (ro : Oracle (List Rate) Rate)
    (primitive : Oracle (Rate × Cap) (Rate × Cap))
    (x rateCoin : Rate) (capacityCoin : Cap) (existing : Rate × Cap)
    (hlookup : primitive.lookup (iv.1 + x, iv.2) = some existing)
    (hne : existing.1 ≠ (ro.respond [x] rateCoin).1) :
    programConstruction iv ro primitive [x] [rateCoin] [capacityCoin] = none := by
  unfold programConstruction
  simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte,
    programPrefixes]
  rw [hlookup]
  simp [hne]

end PrefixProgramming

/-! ## Two-block prefixes are both materialized -/

namespace SpongePrefixProgrammingExample

def iv : ZMod 2 × Fin 5 := (0, 0)

noncomputable def result : PrefixProgramState (ZMod 2) (Fin 5) :=
  ⟨(0, 2),
    ((Oracle.empty.respond ([1] : List (ZMod 2)) 1).2.respond [1, 1] 0).2,
    ((Oracle.empty.respond (1, 0) (1, 1)).2.respond (0, 1) (0, 2)).2⟩

/-- Exact two-block construction: first prefix squeezes to `H([1]) = 1`,
second prefix squeezes to `H([1,1]) = 0`. -/
theorem two_prefixes_programmed :
    programConstruction iv Oracle.empty Oracle.empty [1, 1] [1, 0] [1, 2] =
      some result := by
  simp [programConstruction, programPrefixes, iv, result,
    Oracle.respond_fresh_fst, Oracle.lookup_respond_ne]

theorem first_prefix_lookup : result.ro.lookup [1] = some 1 := by
  unfold result
  rw [Oracle.lookup_respond_ne _ (by decide)]
  rw [Oracle.lookup_respond_self,
    Oracle.respond_fresh_fst (Oracle.lookup_empty [1])]

theorem second_prefix_lookup : result.ro.lookup [1, 1] = some 0 := by
  unfold result
  rw [Oracle.lookup_respond_self]
  rw [Oracle.respond_fresh_fst]
  rw [Oracle.lookup_respond_ne _ (by decide), Oracle.lookup_empty]

theorem first_prefix_walk :
    walkFrom result.primitive iv [1] = some (1, 1) := by
  unfold result iv
  simp [walkFrom, Oracle.lookup_respond_ne]

theorem full_prefix_walk :
    walkFrom result.primitive iv [1, 1] = some (0, 2) := by
  unfold result iv
  simp [walkFrom, Oracle.lookup_respond_ne]

end SpongePrefixProgrammingExample

/-- info: 'Minidregg.Loom.programPrefixes_some_lengths' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms programPrefixes_some_lengths
/-- info: 'Minidregg.Loom.SpongePrefixProgrammingExample.two_prefixes_programmed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SpongePrefixProgrammingExample.two_prefixes_programmed
/-- info: 'Minidregg.Loom.SpongePrefixProgrammingExample.full_prefix_walk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SpongePrefixProgrammingExample.full_prefix_walk

end Minidregg.Loom
