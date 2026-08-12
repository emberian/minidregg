/-
# Loom.SpongeIndiffWorkStream — fixed uniform coins indexed by primitive work

Construction messages have variable block length, so assigning one coin pair
per public query is not the sample space used by the sponge computation.  This
module feeds the prefix-programmed hybrid from a fixed `Fin work` vector of
`(rate, capacity)` pairs.  Each primitive evaluation consumes exactly one
pair: a construction consumes one pair per block, while a public forward or
inverse query consumes one pair.

The vector is a genuine finite uniform sample space.  If an adaptive execution
requests more than `work` pairs it fails with `exhausted`; no randomness is
conjured beyond the supplied vector.  This is the operational basis for the
work-indexed game.  A later coupling must still reorder deferred coins when
comparing construction-first programming with the landed ideal simulator.
-/
import Loom.SpongeIndiffPrefixHybrid

namespace Minidregg.Loom

section WorkStream

variable {Rate Cap : Type} [AddCommGroup Rate] [DecidableEq Rate]

/-- Repackage an exact primitive-work segment into the coin shape expected by
the public query.  The caller separately checks the segment length. -/
def SpQuery.prefixCoins : SpQuery Rate Cap → List (Rate × Cap) →
    Option (PrefixHybridCoins Rate Cap)
  | .constr _ _, used =>
      some (.construction (used.map Prod.fst) (used.map Prod.snd))
  | .fwd _, [coin] => some (.primitive coin)
  | .inv _, [coin] => some (.primitive coin)
  | _, _ => none

omit [AddCommGroup Rate] [DecidableEq Rate] in
/-- Exact-length work segments always have the right public coin shape. -/
theorem SpQuery.prefixCoins_some_of_length (query : SpQuery Rate Cap)
    (used : List (Rate × Cap))
    (hlength : used.length = query.primitiveCalls) :
    ∃ coins, query.prefixCoins used = some coins := by
  cases query with
  | constr x xs => exact ⟨.construction (used.map Prod.fst) (used.map Prod.snd), rfl⟩
  | fwd s =>
      cases used with
      | nil => simp [SpQuery.primitiveCalls] at hlength
      | cons coin rest =>
          cases rest with
          | nil => exact ⟨.primitive coin, rfl⟩
          | cons coin' rest => simp [SpQuery.primitiveCalls] at hlength
  | inv t =>
      cases used with
      | nil => simp [SpQuery.primitiveCalls] at hlength
      | cons coin rest =>
          cases rest with
          | nil => exact ⟨.primitive coin, rfl⟩
          | cons coin' rest => simp [SpQuery.primitiveCalls] at hlength

/-- Prefix-programmed hybrid state plus the unconsumed work vector suffix. -/
structure WorkHybridState (Rate Cap : Type) where
  core : PrefixHybridState Rate Cap
  remaining : List (Rate × Cap)

def WorkHybridState.initial {work : Nat}
    (coins : Fin work → Rate × Cap) : WorkHybridState Rate Cap :=
  ⟨PrefixHybridState.empty, List.ofFn coins⟩

inductive WorkHybridError where
  | exhausted
  | malformedSegment
  | hybrid (error : PrefixHybridError)

/-- Consume the next exact work segment and execute one adaptive public step. -/
noncomputable def workHybridStep {q : Nat}
    (D : Distinguisher Rate Cap q) (iv : Rate × Cap)
    (st : WorkHybridState Rate Cap) (j : Fin q) :
    Except WorkHybridError (WorkHybridState Rate Cap) :=
  let query := D.move st.core.ans
  let need := query.primitiveCalls
  let used := st.remaining.take need
  if used.length = need then
    match query.prefixCoins used with
    | some roundCoins =>
        match prefixHybridStep D iv (fun _ => roundCoins) st.core j with
        | .ok next => .ok ⟨next, st.remaining.drop need⟩
        | .error error => .error (.hybrid error)
    | none => .error .malformedSegment
  else .error .exhausted

/-- Every successful work-stream step charges exactly the selected query's
primitive cost in the underlying hybrid state. -/
theorem workHybridStep_work_exact {q : Nat}
    (D : Distinguisher Rate Cap q) (iv : Rate × Cap)
    (st next : WorkHybridState Rate Cap) (j : Fin q)
    (h : workHybridStep D iv st j = .ok next) :
    next.core.work = st.core.work + (D.move st.core.ans).primitiveCalls := by
  unfold workHybridStep at h
  dsimp only at h
  split at h
  · split at h
    · split at h
      · injection h with hnext
        subst next
        exact prefixHybridStep_work_exact D iv _ st.core _ j ‹_›
      · contradiction
    · contradiction
  · contradiction

/-- A successful step drops exactly the selected query's primitive cost from
the front of the remaining work stream. -/
theorem workHybridStep_remaining_exact {q : Nat}
    (D : Distinguisher Rate Cap q) (iv : Rate × Cap)
    (st next : WorkHybridState Rate Cap) (j : Fin q)
    (h : workHybridStep D iv st j = .ok next) :
    next.remaining = st.remaining.drop (D.move st.core.ans).primitiveCalls := by
  unfold workHybridStep at h
  dsimp only at h
  split at h
  · split at h
    · split at h
      · injection h with hnext
        subst next
        rfl
      · contradiction
    · contradiction
  · contradiction

/-- Execute all public rounds against one fixed primitive-work vector. -/
noncomputable def workHybridRun {q work : Nat}
    (D : Distinguisher Rate Cap q) (iv : Rate × Cap)
    (coins : Fin work → Rate × Cap) :
    Except WorkHybridError (WorkHybridState Rate Cap) :=
  (List.finRange q).foldl
    (fun state j => state.bind fun st => workHybridStep D iv st j)
    (.ok (WorkHybridState.initial coins))

end WorkStream

section WorkProbability

variable (Rate Cap : Type) [AddCommGroup Rate]
  [Fintype Rate] [Fintype Cap] [DecidableEq Rate] [DecidableEq Cap]

/-- Acceptance probability of the corrected prefix-programmed random-function
hybrid on a fixed `work`-pair uniform sample space.  Exhaustion or a semantic
mismatch rejects. -/
noncomputable def workHybridProb {q work : Nat}
    (D : Distinguisher Rate Cap q) (iv : Rate × Cap) : Real :=
  uniformProb (Fin work → Rate × Cap) fun coins =>
    match workHybridRun D iv coins with
    | .ok state => D.out state.core.ans = true
    | .error _ => False

/-- Work-indexed hybrid-to-ideal agreement is deliberately a named theorem
target rather than an asserted field.  Its proof must couple construction-time
prefix capacities with the ideal simulator's later reveal-time samples. -/
def PrefixHybridIdealAgreement (iv : Rate × Cap) : Prop :=
  ∀ (q work : Nat) (D : Distinguisher Rate Cap q),
    PrimitiveWorkBound D work →
      workHybridProb Rate Cap (work := work) D iv = idealProb D iv

end WorkProbability

/-! ## The fixed stream actually drives a construction-first replay -/

namespace SpongeWorkStreamExample

open SpongePrefixHybridExample

def stream : Fin 3 → ZMod 2 × Nat
  | 0 => (1, 1)
  | 1 => (0, 2)
  | 2 => (0, 3)

noncomputable def initial : WorkHybridState (ZMod 2) Nat :=
  ⟨PrefixHybridState.empty, [(1, 1), (0, 2), (0, 3)]⟩

noncomputable def afterConstruction : WorkHybridState (ZMod 2) Nat :=
  ⟨firstState, [(0, 3)]⟩

noncomputable def afterReplay : WorkHybridState (ZMod 2) Nat :=
  ⟨finalState, []⟩

theorem first_step_exact :
    workHybridStep constructionThenForward iv initial 0 =
      .ok afterConstruction := by
  unfold workHybridStep
  simp only [initial, constructionThenForward, PrefixHybridState.empty,
    List.isEmpty_nil, ↓reduceIte, SpQuery.primitiveCalls, List.take,
    List.length_cons, List.length_nil, Nat.reduceAdd, List.map,
    SpQuery.prefixCoins, List.drop]
  change (match prefixHybridStep constructionThenForward iv
      (fun _ => .construction [1, 0] [1, 2]) PrefixHybridState.empty 0 with
    | Except.ok next => Except.ok ⟨next, [(0, 3)]⟩
    | Except.error error => Except.error (.hybrid error)) =
      Except.ok afterConstruction
  rw [show prefixHybridStep constructionThenForward iv
      (fun _ => .construction [1, 0] [1, 2]) PrefixHybridState.empty 0 =
        .ok firstState by
    simpa [coins] using SpongePrefixHybridExample.first_step_exact]
  rfl

theorem second_step_exact :
    workHybridStep constructionThenForward iv afterConstruction 1 =
      .ok afterReplay := by
  unfold workHybridStep
  simp only [afterConstruction, constructionThenForward, firstState,
    List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte, SpQuery.primitiveCalls,
    List.take, List.length_cons, List.length_nil, SpQuery.prefixCoins,
    List.drop]
  change (match prefixHybridStep constructionThenForward iv
      (fun _ => .primitive (0, 3)) firstState 1 with
    | Except.ok next => Except.ok ⟨next, []⟩
    | Except.error error => Except.error (.hybrid error)) =
      Except.ok afterReplay
  rw [show prefixHybridStep constructionThenForward iv
      (fun _ => .primitive (0, 3)) firstState 1 = .ok finalState by
    simpa [coins] using SpongePrefixHybridExample.second_step_exact]
  rfl

theorem stream_as_list : List.ofFn stream = [(1, 1), (0, 2), (0, 3)] := by
  decide

/-- A fixed three-pair sample drives the two-block construction and subsequent
public replay, consuming the work vector exactly. -/
theorem fixed_work_stream_replays :
    workHybridRun constructionThenForward iv stream = .ok afterReplay := by
  unfold workHybridRun WorkHybridState.initial
  rw [stream_as_list]
  rw [show List.finRange 2 = [0, 1] by decide]
  simp only [List.foldl_cons, List.foldl_nil, Except.bind]
  change (match workHybridStep constructionThenForward iv initial 0 with
    | Except.error error => Except.error error
    | Except.ok state => workHybridStep constructionThenForward iv state 1) =
      Except.ok afterReplay
  rw [first_step_exact]
  exact second_step_exact

end SpongeWorkStreamExample

/-- info: 'Minidregg.Loom.workHybridStep_work_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms workHybridStep_work_exact
/-- info: 'Minidregg.Loom.SpongeWorkStreamExample.fixed_work_stream_replays' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SpongeWorkStreamExample.fixed_work_stream_replays

end Minidregg.Loom
