/-
# Loom.SpongeIndiffOracleReordering — extensional lazy-sampling commutation

Construction-first prefix programming samples RO entries earlier than the
landed ideal simulator, which waits until a prefix is publicly revealed.  The
two handlers need not have definitionally equal logs: distinct responses are
appended in different orders.  What the games observe is lookup behavior.

This module proves the exact extensional algebra needed for the coupling.
Lookup-equivalent handlers return the same answer to the same response step
and remain lookup-equivalent.  In particular, responses to distinct queries
commute extensionally, and each response is unchanged by moving the other
distinct response before it.

No probability assertion appears here.  The later game equivalence must lift
this deterministic coin-reordering law to a bijection of the fixed uniform
work sample space.
-/
import Loom.SpongeIndiffWorkStream

namespace Minidregg.Loom

namespace Oracle

section Reordering

variable {Q C : Type}

/-- Two finite lazy handlers denote the same partial response function.  Their
log order and proof fields may differ. -/
def LookupEquivalent (left right : Oracle Q C) : Prop :=
  ∀ query, left.lookup query = right.lookup query

theorem LookupEquivalent.refl (oracle : Oracle Q C) :
    LookupEquivalent oracle oracle := fun _ => rfl

theorem LookupEquivalent.symm {left right : Oracle Q C}
    (h : LookupEquivalent left right) : LookupEquivalent right left :=
  fun query => (h query).symm

theorem LookupEquivalent.trans {left middle right : Oracle Q C}
    (hlm : LookupEquivalent left middle)
    (hmr : LookupEquivalent middle right) : LookupEquivalent left right :=
  fun query => (hlm query).trans (hmr query)

/-- A response answer is determined only by the current lookup result. -/
theorem respond_fst_eq_of_lookup_eq (left right : Oracle Q C) (query : Q)
    (coin : C) (hlookup : left.lookup query = right.lookup query) :
    (left.respond query coin).1 = (right.respond query coin).1 := by
  cases hleft : left.lookup query with
  | some value =>
      have hright : right.lookup query = some value := hlookup ▸ hleft
      rw [respond_hit hleft, respond_hit hright]
  | none =>
      have hright : right.lookup query = none := hlookup ▸ hleft
      rw [respond_fresh_fst hleft, respond_fresh_fst hright]

/-- A response changes the queried lookup to its returned value and frames all
other queries. -/
theorem lookup_respond (oracle : Oracle Q C) (query other : Q) (coin : C) :
    (oracle.respond query coin).2.lookup other =
      if other = query then some (oracle.respond query coin).1
      else oracle.lookup other := by
  by_cases heq : other = query
  · subst other
    rw [if_pos rfl, lookup_respond_self]
  · rw [if_neg heq, lookup_respond_ne oracle heq]

/-- Responding with the same query and coin preserves lookup equivalence. -/
theorem LookupEquivalent.respond {left right : Oracle Q C}
    (h : LookupEquivalent left right) (query : Q) (coin : C) :
    LookupEquivalent (left.respond query coin).2
      (right.respond query coin).2 := by
  intro other
  rw [lookup_respond, lookup_respond]
  split
  · congr 2
    exact respond_fst_eq_of_lookup_eq left right query coin (h query)
  · exact h other

/-- Moving a distinct response earlier does not change this query's returned
answer. -/
theorem respond_distinct_fst (oracle : Oracle Q C) {first second : Q}
    (hne : second ≠ first) (firstCoin secondCoin : C) :
    (((oracle.respond first firstCoin).2.respond second secondCoin).1) =
      (oracle.respond second secondCoin).1 := by
  apply respond_fst_eq_of_lookup_eq
  exact lookup_respond_ne oracle hne firstCoin

/-- Two responses at distinct queries commute as partial functions, even
though their append-ordered log records are generally not equal. -/
theorem respond_distinct_commute (oracle : Oracle Q C) {first second : Q}
    (hne : first ≠ second) (firstCoin secondCoin : C) :
    LookupEquivalent
      ((oracle.respond first firstCoin).2.respond second secondCoin).2
      ((oracle.respond second secondCoin).2.respond first firstCoin).2 := by
  intro other
  rw [lookup_respond, lookup_respond]
  by_cases hsecond : other = second
  · subst other
    rw [if_pos rfl, if_neg hne]
    rw [lookup_respond]
    rw [if_pos rfl]
    congr 2
    exact respond_distinct_fst oracle (Ne.symm hne) firstCoin secondCoin
  · rw [if_neg hsecond]
    by_cases hfirst : other = first
    · subst other
      rw [if_pos rfl]
      rw [lookup_respond, if_neg hne]
      congr 2
      exact respond_distinct_fst oracle hne secondCoin firstCoin |>.symm
    · rw [if_neg hfirst]
      rw [lookup_respond, if_neg hfirst, lookup_respond, if_neg hsecond]

end Reordering

end Oracle

/-! ## Order differs, semantics agree -/

namespace SpongeOracleReorderingExample

def leftFirst : Oracle Nat Bool :=
  ((Oracle.empty.respond 7 true).2.respond 9 false).2

def rightFirst : Oracle Nat Bool :=
  ((Oracle.empty.respond 9 false).2.respond 7 true).2

theorem logs_differ : leftFirst.log ≠ rightFirst.log := by decide

theorem lookups_agree : Oracle.LookupEquivalent leftFirst rightFirst := by
  exact Oracle.respond_distinct_commute Oracle.empty (by decide) true false

theorem exact_values :
    leftFirst.lookup 7 = some true ∧ leftFirst.lookup 9 = some false := by
  constructor
  · rw [Oracle.lookup_respond_ne _ (by decide), Oracle.lookup_respond_self,
      Oracle.respond_fresh_fst (Oracle.lookup_empty 7)]
  · rw [Oracle.lookup_respond_self]
    rw [Oracle.respond_fresh_fst]
    rw [Oracle.lookup_respond_ne _ (by decide), Oracle.lookup_empty]

end SpongeOracleReorderingExample

/-- info: 'Minidregg.Loom.Oracle.respond_distinct_commute' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Oracle.respond_distinct_commute
/-- info: 'Minidregg.Loom.SpongeOracleReorderingExample.lookups_agree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SpongeOracleReorderingExample.lookups_agree

end Minidregg.Loom
