/-
# FleetLaws: the S5, S6, S7 and S8 laws of docs/fleet-interfaces, as statements a receiver can meet

A standalone program in the docs/evidence sense (not a `lean_lib` module): Lean core only, no
Mathlib, no project imports, so it checks with `lean docs/fleet-interfaces/FleetLaws.lean` on the
pinned toolchain. Paths are any type with decidable equality and a `parent` function, so a
receiver can restate these over its own cell ids.

What is stated (each with its teeth below):

* `land_stale_names_every_moved` (S5.2): a staleness refusal names exactly the read-set entries
  some change moved, every one of them, not the first.
* `landed_iff_nothing_moved` (S5.1): a land is admitted iff no change hits its read set.
* `land_commutes` (S5.3): two lands whose writes miss each other's read sets are both admitted
  in either order.
* `stale_persists` (S7.4): once stale, more changes never make a land or a verdict current again.
* `green_needs_red_control` (S6.1): a unit reads green only when its known-red control read red.
* `compensate_within_target` and `compensate_refusal_names_every_outside` (S8.2): a keeper's
  compensation touches only paths the target land wrote, and a refusal names every outside path.
* `inverse_inverse`, `apply_inverse_restores` (S8.5): undoing an undo is the original diff, and
  applying a well-formed diff then its inverse restores every path.

What is NOT stated: signatures, roles, time, git's merge, or how a read set is traced. These
model the decision once the inputs exist; fleetif.py is the same decision over JSON.
-/
set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace FleetLaws

/-! ## Read sets and changes -/

inductive How where
  | read    -- the path was opened
  | absent  -- the path was looked up and missing
  | list    -- the directory was listed
  deriving DecidableEq, Repr

structure Entry (P : Type) where
  path : P
  how : How
  deriving DecidableEq, Repr

inductive Change (P : Type) where
  | modify (p : P)
  | add (p : P)
  | delete (p : P)
  deriving DecidableEq, Repr

variable {P : Type} [DecidableEq P] (parent : P → P)

/-- Does a change move what an entry read? fleetif.py `hits`. -/
def hits (e : Entry P) : Change P → Bool
  | .modify q => e.how == .read && q == e.path
  | .delete q => (e.how == .read && q == e.path) || (e.how == .list && parent q == e.path)
  | .add q => (e.how == .absent && q == e.path) || (e.how == .list && parent q == e.path)

/-- Every entry some change moves, in read-set order. -/
def moved (rs : List (Entry P)) (cs : List (Change P)) : List (Entry P) :=
  rs.filter fun e => cs.any (hits parent e)

inductive Outcome (P : Type) where
  | landed
  | stale (moved : List (Entry P))
  deriving DecidableEq, Repr

/-- S5: the one staleness refusal. -/
def land (rs : List (Entry P)) (cs : List (Change P)) : Outcome P :=
  match moved parent rs cs with
  | [] => .landed
  | m => .stale m

theorem land_stale_names_every_moved (rs : List (Entry P)) (cs : List (Change P))
    (m : List (Entry P)) (h : land parent rs cs = .stale m) :
    ∀ e ∈ rs, e ∈ m ↔ ∃ c ∈ cs, hits parent e c = true := by
  intro e he
  have hm : moved parent rs cs = m := by
    unfold land at h
    split at h <;> simp_all
  subst hm
  simp [moved, List.mem_filter, List.any_eq_true, he]

theorem landed_iff_nothing_moved (rs : List (Entry P)) (cs : List (Change P)) :
    land parent rs cs = .landed ↔ ∀ e ∈ rs, ∀ c ∈ cs, hits parent e c = false := by
  unfold land
  constructor
  · intro h e he c hc
    split at h
    · rename_i hnil
      have : e ∉ moved parent rs cs := by simp [hnil]
      simp only [moved, List.mem_filter, List.any_eq_true, not_and, not_exists] at this
      have := this he c hc
      simpa using this
    · cases h
  · intro h
    have : moved parent rs cs = [] := by
      simp only [moved, List.filter_eq_nil_iff, List.any_eq_true, not_exists, not_and]
      intro e he c hc
      simp [h e he c hc]
    simp [this]

theorem land_commutes (rsA rsB : List (Entry P)) (base wA wB : List (Change P))
    (hA : land parent rsA base = .landed) (hB : land parent rsB base = .landed)
    (missA : ∀ e ∈ rsA, ∀ c ∈ wB, hits parent e c = false)
    (missB : ∀ e ∈ rsB, ∀ c ∈ wA, hits parent e c = false) :
    land parent rsA (base ++ wB) = .landed ∧ land parent rsB (base ++ wA) = .landed := by
  rw [landed_iff_nothing_moved] at hA hB ⊢
  rw [landed_iff_nothing_moved]
  constructor
  · intro e he c hc
    rcases List.mem_append.mp hc with h | h
    · exact hA e he c h
    · exact missA e he c h
  · intro e he c hc
    rcases List.mem_append.mp hc with h | h
    · exact hB e he c h
    · exact missB e he c h

theorem stale_persists (rs : List (Entry P)) (cs more : List (Change P))
    (h : land parent rs cs ≠ .landed) : land parent rs (cs ++ more) ≠ .landed := by
  intro h2
  apply h
  rw [landed_iff_nothing_moved] at h2 ⊢
  intro e he c hc
  exact h2 e he c (List.mem_append_left _ hc)

/-! ## Known-red control (S6.1, nanodregg gates/runs.py:11-18) -/

inductive Reading where
  | green | red | incomplete | unread
  deriving DecidableEq, Repr

/-- A run's result is read only when its known-red control read red. -/
def reads (control result : Reading) : Reading :=
  if control = .red then result else .unread

theorem green_needs_red_control (control result : Reading) (h : reads control result = .green) :
    control = .red ∧ result = .green := by
  unfold reads at h
  split at h
  · exact ⟨by assumption, h⟩
  · cases h

/-! ## Compensation (S8) -/

/-- One path's before and after content. -/
structure Edit (P V : Type) where
  path : P
  before : V
  after : V
  deriving DecidableEq, Repr

variable {V : Type} [DecidableEq V]

def writes (d : List (Edit P V)) : List P := d.map (·.path)

inductive Comp (P V : Type) where
  | ok (diff : List (Edit P V))
  | refused (outside : List P)
  deriving DecidableEq, Repr

/-- The keeper's compensation of a target land over `scope`: refused, naming every path of the
scope the target never wrote; otherwise the inverse of the target's edits on the scope. -/
def compensate (target : List (Edit P V)) (scope : List P) : Comp P V :=
  match scope.filter (fun p => !(writes target).contains p) with
  | [] => .ok ((target.filter (fun e => scope.contains e.path)).map
      fun e => { path := e.path, before := e.after, after := e.before })
  | out => .refused out

theorem compensate_within_target (target : List (Edit P V)) (scope : List P)
    (diff : List (Edit P V)) (h : compensate target scope = .ok diff) :
    ∀ p ∈ writes diff, p ∈ writes target := by
  unfold compensate at h
  split at h
  · cases h
    intro p hp
    simp only [writes, List.mem_map, List.mem_filter] at hp ⊢
    obtain ⟨w, ⟨x, ⟨hx, _⟩, hxw⟩, hwp⟩ := hp
    exact ⟨x, hx, by rw [← hwp, ← hxw]⟩
  · cases h

theorem compensate_refusal_names_every_outside (target : List (Edit P V)) (scope : List P)
    (out : List P) (h : compensate target scope = .refused out) :
    ∀ p ∈ scope, p ∈ out ↔ p ∉ writes target := by
  unfold compensate at h
  split at h
  · cases h
  · rename_i hfil _
    cases h
    intro p hp
    simp [List.mem_filter, hp]

def inverse (d : List (Edit P V)) : List (Edit P V) :=
  d.map fun e => { path := e.path, before := e.after, after := e.before }

theorem inverse_inverse (d : List (Edit P V)) : inverse (inverse d) = d := by
  simp [inverse, List.map_map, Function.comp_def]

/-- Apply a diff to a state: a path the diff edits holds that edit's `after` (a diff names each
path once, as `git diff` does; the first edit for a path is the one read). -/
def apply (s : P → V) (d : List (Edit P V)) (q : P) : V :=
  match d.find? (fun e => e.path == q) with
  | some e => e.after
  | none => s q

/-- A diff is well formed on a state when each edit's `before` is what the state holds there. -/
def WellFormed (s : P → V) (d : List (Edit P V)) : Prop :=
  ∀ e ∈ d, s e.path = e.before

theorem apply_inverse_restores (s : P → V) (d : List (Edit P V)) (hw : WellFormed s d) :
    ∀ q, apply (apply s d) (inverse d) q = s q := by
  intro q
  unfold apply inverse
  rw [List.find?_map]
  have hp : ((fun e : Edit P V => e.path == q) ∘ fun e : Edit P V =>
      ({ path := e.path, before := e.after, after := e.before } : Edit P V)) =
      fun e => e.path == q := rfl
  rw [hp]
  cases h : d.find? (fun e => e.path == q) with
  | none => simp
  | some e =>
    have he : e ∈ d := List.mem_of_find?_eq_some h
    have hq : e.path = q := by simpa using List.find?_some h
    simp [← hq, hw e he]

/-! ## Teeth: each law refuses something, and each premise is inhabited -/

def up (n : Nat) : Nat := n / 10  -- path 52 lives in directory 5

example : land up [⟨52, .read⟩, ⟨53, .absent⟩, ⟨5, .list⟩] [.modify 52, .add 53]
    = .stale [⟨52, .read⟩, ⟨53, .absent⟩, ⟨5, .list⟩] := by decide
example : land up [⟨52, .read⟩] [.modify 61, .add 70] = .landed := by decide
example : land up [⟨5, .list⟩] [.add 512] = .landed := by decide  -- a grandchild is not listed
example : reads .green .green = .unread := by decide
example : compensate (V := Nat) [⟨1, 0, 1⟩, ⟨2, 0, 2⟩] [2, 3, 4] = .refused [3, 4] := by decide
example : compensate (V := Nat) [⟨1, 0, 1⟩, ⟨2, 0, 2⟩] [2] = .ok [⟨2, 2, 0⟩] := by decide

/-! ## Axiom footprints: a regression gate (no `sorryAx`, no project axiom) -/

/-- info: 'FleetLaws.land_stale_names_every_moved' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms land_stale_names_every_moved

/-- info: 'FleetLaws.landed_iff_nothing_moved' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms landed_iff_nothing_moved

/-- info: 'FleetLaws.land_commutes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms land_commutes

/-- info: 'FleetLaws.stale_persists' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms stale_persists

/-- info: 'FleetLaws.compensate_within_target' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms compensate_within_target

/-- info: 'FleetLaws.compensate_refusal_names_every_outside' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms compensate_refusal_names_every_outside

/-- info: 'FleetLaws.inverse_inverse' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms inverse_inverse

/-- info: 'FleetLaws.apply_inverse_restores' depends on axioms: [propext] -/
#guard_msgs in #print axioms apply_inverse_restores

/-- info: 'FleetLaws.green_needs_red_control' does not depend on any axioms -/
#guard_msgs in #print axioms green_needs_red_control

end FleetLaws
