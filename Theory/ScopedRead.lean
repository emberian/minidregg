/-
# Theory.ScopedRead — evaluation over a served read set that never defaults

A thin consent client does not hold the world.  The Host serves it the plan's
read set `R` (keys with their values, `none` = known absent), and the client
re-runs the plan on that partial view.  This is sound only if the evaluator can
never treat an omitted key as anything: an omitted read must stop the run by
name.  A reader function `K → Except E V` cannot promise that, because a caller
can catch the error and default it.  So a plan here is a free program over
reads (`Prog`), with no catch construct.  Its only interaction with state is
`read`, and the scoped runner turns an unlisted key into `Outcome.outside k`.

## Theorems

* `frame` — a scoped run that finished is the full run on every state the view
  agrees with.  A Host that serves the right values for every key the run reads
  cannot make the client see a result other than the real one; a Host that lies
  about a read value is a disagreeing view, and the signed binding catches it at
  admission (`Theory.PlanBinding.admit`), not here.
* `runOn_restrict_reads` — completeness: the keys the full run reads suffice, so
  an honest Host can always serve a view the client finishes on.
* `outside_unlisted` and `outside_is_read` — an outside refusal names a key the
  view does not list, and (when the view agrees) a key the real run reads.
* `defaulting_breaks_frame` — the refuted pole: the same runner, with an
  unlisted key read as absent, finishes with a value the full run never yields.
  This is why `runOn` must not default.
* `restrict_agrees` — the honest view's premise is inhabited: a view built from
  the state agrees with it.

The premises of `frame` and `runOn_restrict_reads` are inhabited by
`restrict_agrees` and `Example.honest_finishes`.
-/
import Theory.AxiomPin

namespace Minidregg.Theory.ScopedRead

set_option autoImplicit false

/-- A plan over reads: return, or read key `k` and continue with its value
(`none` = absent).  There is no catch: nothing a program does can observe that a
read was refused. -/
inductive Prog (K V α : Type) where
  | pure (a : α)
  | read (k : K) (next : Option V → Prog K V α)

namespace Prog

variable {K V α β : Type}

def bind : Prog K V α → (α → Prog K V β) → Prog K V β
  | .pure a, f => f a
  | .read k next, f => .read k fun v => bind (next v) f

instance : Monad (Prog K V) where
  pure := .pure
  bind := bind

/-- Read one key. -/
def get (k : K) : Prog K V (Option V) := .read k .pure

/-- The run on a whole state. -/
def runFull (s : K → Option V) : Prog K V α → α
  | .pure a => a
  | .read k next => runFull s (next (s k))

/-- The keys the run on a whole state reads, in order. -/
def reads (s : K → Option V) : Prog K V α → List K
  | .pure _ => []
  | .read k next => k :: reads s (next (s k))

end Prog

/-- A served view: listed keys with their values (`none` = known absent). -/
structure View (K V : Type) where
  entries : List (K × Option V)

/-- The result of a scoped run: finished, or stopped at an unlisted key. -/
inductive Outcome (K α : Type) where
  | ok (a : α)
  | outside (k : K)
  deriving DecidableEq, Repr

namespace View

variable {K V : Type} [DecidableEq K]

/-- `some v` when the view lists `k` (first entry wins); `none` when it does not. -/
def lookup (w : View K V) (k : K) : Option (Option V) :=
  (w.entries.find? fun e => decide (e.1 = k)).map (·.2)

/-- Every entry of the view is the state's value. -/
def Agrees (w : View K V) (s : K → Option V) : Prop :=
  ∀ e ∈ w.entries, s e.1 = e.2

theorem lookup_agrees {w : View K V} {s : K → Option V} (agree : w.Agrees s) {k : K}
    {v : Option V} (found : w.lookup k = some v) : v = s k := by
  unfold lookup at found
  cases hfind : w.entries.find? (fun e => decide (e.1 = k)) with
  | none => rw [hfind] at found; cases found
  | some e =>
      rw [hfind] at found
      have hv : e.2 = v := Option.some.inj found
      have mem := List.mem_of_find?_eq_some hfind
      have key : e.1 = k := by simpa using List.find?_some hfind
      rw [← hv, ← agree e mem, key]

theorem lookup_eq_none_iff (w : View K V) (k : K) :
    w.lookup k = none ↔ ∀ e ∈ w.entries, e.1 ≠ k := by
  unfold lookup
  rw [Option.map_eq_none_iff, List.find?_eq_none]
  simp

end View

/-- The view an honest Host serves: the state's value at each named key. -/
def restrict {K V : Type} (s : K → Option V) (ks : List K) : View K V :=
  ⟨ks.map fun k => (k, s k)⟩

section Run

variable {K V α : Type} [DecidableEq K]

/-- The scoped run.  An unlisted key stops it with `outside k`; it is never read
as absent. -/
def Prog.runOn (w : View K V) : Prog K V α → Outcome K α
  | .pure a => .ok a
  | .read k next =>
      match w.lookup k with
      | none => .outside k
      | some v => Prog.runOn w (next v)

/-- The defaulting runner, kept only to refute it (`defaulting_breaks_frame`). -/
def Prog.runOnDefaulting (w : View K V) : Prog K V α → α
  | .pure a => a
  | .read k next => Prog.runOnDefaulting w (next ((w.lookup k).getD none))

omit [DecidableEq K] in
theorem restrict_agrees (s : K → Option V) (ks : List K) : (restrict s ks).Agrees s := by
  intro e mem
  simp only [restrict, List.mem_map] at mem
  obtain ⟨k, _, rfl⟩ := mem
  rfl

theorem lookup_restrict_mem (s : K → Option V) {ks : List K} {k : K} (mem : k ∈ ks) :
    (restrict s ks).lookup k = some (s k) := by
  cases found : (restrict s ks).lookup k with
  | some v => rw [View.lookup_agrees (restrict_agrees s ks) found]
  | none =>
      have absent := (View.lookup_eq_none_iff _ k).1 found
      exact absurd rfl (absent (k, s k) (by simp only [restrict, List.mem_map]; exact ⟨k, mem, rfl⟩))

/-- **Frame.**  A scoped run that finished is the full run on every state the
view agrees with. -/
theorem frame (w : View K V) (s : K → Option V) (agree : w.Agrees s) :
    ∀ (p : Prog K V α) (a : α), p.runOn w = .ok a → p.runFull s = a
  | .pure b, a, h => by
      simp only [Prog.runOn, Outcome.ok.injEq] at h
      exact h
  | .read k next, a, h => by
      simp only [Prog.runOn] at h
      cases found : w.lookup k with
      | none => rw [found] at h; cases h
      | some v =>
          rw [found] at h
          have hv := View.lookup_agrees agree found
          subst hv
          exact frame w s agree (next (s k)) a h

/-- **Completeness.**  A view listing every key the full run reads finishes,
with the full run's result. -/
theorem runOn_restrict (s : K → Option V) (ks : List K) :
    ∀ (p : Prog K V α), (∀ k ∈ p.reads s, k ∈ ks) → p.runOn (restrict s ks) = .ok (p.runFull s)
  | .pure _, _ => rfl
  | .read k next, cover => by
      have here : k ∈ ks := cover k (by simp [Prog.reads])
      have rest : ∀ k' ∈ (next (s k)).reads s, k' ∈ ks :=
        fun k' mem => cover k' (by simp [Prog.reads, mem])
      simp only [Prog.runOn, lookup_restrict_mem s here, Prog.runFull]
      exact runOn_restrict s ks (next (s k)) rest

theorem runOn_restrict_reads (s : K → Option V) (p : Prog K V α) :
    p.runOn (restrict s (p.reads s)) = .ok (p.runFull s) :=
  runOn_restrict s (p.reads s) p fun _ mem => mem

/-- **Refusal names an unlisted key.** -/
theorem outside_unlisted (w : View K V) :
    ∀ (p : Prog K V α) (k : K), p.runOn w = .outside k → w.lookup k = none
  | .pure _, _, h => by simp [Prog.runOn] at h
  | .read k' next, k, h => by
      simp only [Prog.runOn] at h
      cases found : w.lookup k' with
      | none =>
          rw [found] at h
          simp only [Outcome.outside.injEq] at h
          subst h
          exact found
      | some v =>
          rw [found] at h
          exact outside_unlisted w (next v) k h

/-- **…and, on an agreeing view, a key the real run reads.**  The client's
refusal points at a read the Host omitted, never at an invented one. -/
theorem outside_is_read (w : View K V) (s : K → Option V) (agree : w.Agrees s) :
    ∀ (p : Prog K V α) (k : K), p.runOn w = .outside k → k ∈ p.reads s
  | .pure _, _, h => by simp [Prog.runOn] at h
  | .read k' next, k, h => by
      simp only [Prog.runOn] at h
      cases found : w.lookup k' with
      | none =>
          rw [found] at h
          simp only [Outcome.outside.injEq] at h
          subst h
          simp [Prog.reads]
      | some v =>
          rw [found] at h
          have hv := View.lookup_agrees agree found
          subst hv
          have := outside_is_read w s agree (next (s k')) k h
          simp [Prog.reads, this]

end Run

/-! ## Poles on a two-key toy -/

namespace Example

/-- Read key 0; if present, read key 1 and add. -/
def plan : Prog Nat Nat Nat := do
  match ← Prog.get 0 with
  | none => pure 0
  | some x =>
      match ← Prog.get 1 with
      | none => pure x
      | some y => pure (x + y)

def state : Nat → Option Nat
  | 0 => some 2
  | 1 => some 3
  | _ => none

/-- The honest view finishes with the full result (premise of `frame` inhabited
by `restrict_agrees`). -/
theorem honest_finishes :
    plan.runOn (restrict state (plan.reads state)) = .ok 5 ∧ plan.runFull state = 5 := by
  decide

/-- A Host that omits key 1 stops the client at key 1. -/
theorem omitted_refused : plan.runOn (restrict state [0]) = .outside 1 := by decide

/-- **The defaulting runner is wrong.**  Reading the omitted key 1 as absent
finishes with 2, a value the real run (5) never yields, on a view that agrees
with the state. -/
theorem defaulting_breaks_frame :
    (restrict state [0]).Agrees state ∧
      plan.runOnDefaulting (restrict state [0]) = 2 ∧ plan.runFull state = 5 :=
  ⟨restrict_agrees state [0], by decide, by decide⟩

end Example

#assert_axioms View.lookup_agrees restrict_agrees lookup_restrict_mem frame runOn_restrict
  runOn_restrict_reads outside_unlisted outside_is_read Example.honest_finishes
  Example.omitted_refused Example.defaulting_breaks_frame

end Minidregg.Theory.ScopedRead
