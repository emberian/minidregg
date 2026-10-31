/-
# Assurance.StoryHistory -- no skip, no rewind, over the controller's own checked legs

`Assurance.StoryLaw.sealed_story_scene_monotone` is proved over `Kernel.LawHistory.Accepted`, a
model of a cell's write history judged by `LawView.admits`; no theorem identifies that model's
`LawView.view` with the state the Host's controller hands the policy (`DeclaredResourceController.step`).
The per-step `kernel_story_step` IS about the controller (a `CheckedLeg`). This file lifts the per-step
statement to histories, over the controller's states.

* `Realized t S n`: `n` is the full projected `newState` of the controller's step (`fullStep`; the
  step its law is judged on is it cut to the law's reads, with the same verdict) for some
  `CheckedLeg` that is a write on a cell whose authenticated closure includes the sealed story law
  (`StoryInstalled`). `realized_step` gets `Step t S n` from `kernel_story_step_full`.
* `Chained`: consecutive legs link, scene and turn: the `after` slot of one leg equals the `before`
  slot of the next. This is the durable CAS (each pre is the previous post), a premise on the states.
* `Coherent n`: for the scene and turn fields, `delta = after - before`. No longer a premise of the
  main theorem: `coherent_of_step` derives it from `Step` and `realized_scalar`.

**R1 is discharged.** `Realized` now also requires the primary target's payload to be scalar (a
story cell is one). `realized_scalar` proves that the controller's `newState` answers every
`resource/field/N/{before,after,delta}` key from `scalarSlots` of the cell's before and after
stores (`local_field_exact`: the common, byte and joint blocks hold no such key; `participant_field`:
a scalar target's projection is `scalarSlots`), and `coherent_of_step` turns that plus `Step` into
`Coherent`.

**Named residuals (premises, not proved here).** (R2a) The Host discharging `StoryInstalled`: nothing
in the Host runs `checkInstalled`/`checkActiveComponent`, and it cannot call `StoryLaw.checkInstalled`
(the Host may not import Assurance); see the census doc, Door 11. (R2b) `Chained` for the receiver's
actual sequence of accepted writes (the CAS chain). (R3) A concrete `CheckedLeg` on the tale,
inhabiting `Realized` (the satisfiable pole below inhabits every premise except that one, through
`Step`). The main theorem is proved given these.
-/
import Assurance.StoryLaw

namespace Minidregg.Assurance.StoryHistory

open Minidregg.Pred (Pred State eval)
open Minidregg.Kernel.DeclaredResourceProjection (fieldName Values scalarSlots)
open Minidregg.Kernel.DeclaredResourceController
open Minidregg.Kernel.MultiCellHyperedge
open Minidregg.Compiler
open Minidregg.Assurance.StoryLaw
open Minidregg.Kernel.StoryLaw
set_option autoImplicit false
set_option linter.unusedSimpArgs false


/-! ## §0. The controller's scalar projection of a story cell (discharges R1)

`scalar_before/after/delta`: `scalarSlots b a` answers a `resource/field/N/{before,after,delta}` key
by `b`, `a` and their difference. `local_field_exact` and `participant_field`: the controller's
`newState` answers such a key from the primary participant's own `scalarSlots` when that target's
payload is scalar (common slots, the byte block and the joint block hold no `resource/field` key;
the tenth character of every other key is not `f`). -/

section Scalar
open Minidregg.Kernel.LawView
open Minidregg.Kernel.DeclaredResourceProjection (scalarSlots pairName Values)
open Minidregg.Kernel.DeclaredResourceController.JointSlots
open Minidregg.Theory.TypedAuthorization Minidregg.Theory.Store Minidregg.Kernel
abbrev gt := Minidregg.Kernel.DeclaredResourceProjection.get
variable {F : Type} [Field F] [DecidableEq F] {deployment : Deployment}
  {profile : CanonicalRuntimeProfile.Profile F} {ambient : Ambient}
  {ground : Ground deployment} {command : Command}

theorem gt_cons (p : Nat × Int) (rest : Values) (k : Nat) :
    gt (p :: rest) k = if p.1 = k then some p.2 else gt rest k := by
  unfold gt Minidregg.Kernel.DeclaredResourceProjection.get
  by_cases h : p.1 = k <;> simp [h]

theorem gt_nil (k : Nat) : gt [] k = none := rfl

theorem before_ne_after (a b : Nat) : fieldName a "before" ≠ fieldName b "after" :=
  ne_of_lastc (by rw [lastc_before, lastc_after]; decide)
theorem before_ne_delta (a b : Nat) : fieldName a "before" ≠ fieldName b "delta" :=
  ne_of_lastc (by rw [lastc_before, lastc_delta]; decide)
theorem after_ne_delta (a b : Nat) : fieldName a "after" ≠ fieldName b "delta" :=
  ne_of_lastc (by rw [lastc_after, lastc_delta]; decide)

theorem find_map_key (xs : Values) (v : String) (f : Nat) :
    ((xs.map fun p => (fieldName p.1 v, p.2)).find? (fun q => q.1 == fieldName f v)).map (·.2) = gt xs f := by
  induction xs with
  | nil => rfl
  | cons p rest ih =>
      rw [gt_cons]
      by_cases h : p.1 = f
      · subst h; simp
      · have hne : ¬ (fieldName p.1 v = fieldName f v) := fun e => h (fieldName_inj.mp e)
        rw [List.map_cons, List.find?_cons]
        have e : ((fieldName p.1 v, p.2).1 == fieldName f v) = false := by simpa using hne
        rw [e]; simp only [Bool.false_eq_true, if_false]
        rw [if_neg h]; exact ih

theorem map_none_of (xs : Values) (v w : String) (f : Nat) (hne : ∀ a b : Nat, fieldName a v ≠ fieldName b w) :
    (xs.map fun p => (fieldName p.1 v, p.2)).find? (fun q => q.1 == fieldName f w) = none := by
  apply find_none
  intro q hq
  simp only [List.mem_map] at hq
  obtain ⟨p, -, rfl⟩ := hq
  exact hne _ _

theorem pairs_none (pre post : Values) (f : Nat) :
    (post.flatMap (fun a => post.filterMap fun b => do
        let oldA ← gt pre a.1
        let oldB ← gt pre b.1
        return (pairName a.1 b.1, a.2 + b.2 - oldA - oldB))).find? (fun q => q.1 == fieldName f "delta") = none := by
  apply find_none
  intro q hq
  obtain ⟨a, b, e⟩ := mem_pairs hq
  rw [e]; exact pairName_ne_fieldName _ _ _ _

def gD (pre : Values) (p : Nat × Int) : Option (String × Int) :=
  (gt pre p.1).map fun old => (fieldName p.1 "delta", p.2 - old)

theorem gD_none (pre : Values) (p : Nat × Int) (h : gt pre p.1 = none) : gD pre p = none := by
  simp [gD, h]
theorem gD_some (pre : Values) (p : Nat × Int) (old : Int) (h : gt pre p.1 = some old) :
    gD pre p = some (fieldName p.1 "delta", p.2 - old) := by
  simp [gD, h]

theorem delta_none (pre : Values) (f : Nat) (h : gt pre f = none) : ∀ post : Values,
    ((post.filterMap (gD pre)).find? (fun q => q.1 == fieldName f "delta")) = none := by
  intro post
  induction post with
  | nil => rfl
  | cons p rest ih =>
      by_cases hp : p.1 = f
      · have hg : gt pre p.1 = none := by rw [hp]; exact h
        rw [List.filterMap_cons_none (gD_none pre p hg)]; exact ih
      · have hne : ¬ (fieldName p.1 "delta" = fieldName f "delta") := fun e => hp (fieldName_inj.mp e)
        cases hg : gt pre p.1 with
        | none => rw [List.filterMap_cons_none (gD_none pre p hg)]; exact ih
        | some old =>
            rw [List.filterMap_cons_some (gD_some pre p old hg), List.find?_cons]
            have e : ((fieldName p.1 "delta", p.2 - old).1 == fieldName f "delta") = false := by simpa using hne
            rw [e]; exact ih

theorem delta_find (pre : Values) (f : Nat) : ∀ post : Values,
    (((post.filterMap (gD pre)).find? (fun q => q.1 == fieldName f "delta"))).map (·.2) =
      (gt post f).bind fun y => (gt pre f).map fun x => y - x := by
  intro post
  induction post with
  | nil => rfl
  | cons p rest ih =>
      rw [gt_cons]
      by_cases hp : p.1 = f
      · rw [if_pos hp]
        cases hg : gt pre f with
        | none =>
            have hg' : gt pre p.1 = none := by rw [hp]; exact hg
            rw [List.filterMap_cons_none (gD_none pre p hg'), delta_none pre f hg rest]; rfl
        | some old =>
            have hg' : gt pre p.1 = some old := by rw [hp]; exact hg
            rw [List.filterMap_cons_some (gD_some pre p old hg'), List.find?_cons]
            have e : ((fieldName p.1 "delta", p.2 - old).1 == fieldName f "delta") = true := by simp [hp]
            rw [e]; simp
      · rw [if_neg hp]
        have hne : ¬ (fieldName p.1 "delta" = fieldName f "delta") := fun e => hp (fieldName_inj.mp e)
        cases hg : gt pre p.1 with
        | none => rw [List.filterMap_cons_none (gD_none pre p hg)]; exact ih
        | some old =>
            rw [List.filterMap_cons_some (gD_some pre p old hg), List.find?_cons]
            have e : ((fieldName p.1 "delta", p.2 - old).1 == fieldName f "delta") = false := by simpa using hne
            rw [e]; exact ih

theorem scalar_delta (b a : Values) (f : Nat) :
    State.get ⟨scalarSlots b a⟩ (fieldName f "delta") = (gt a f).bind fun y => (gt b f).map fun x => y - x := by
  rw [state_get, scalarSlots_split]
  have n1 := map_none_of b "before" "delta" f before_ne_delta
  have n2 := map_none_of a "after" "delta" f after_ne_delta
  have n3 := pairs_none b a f
  rw [List.find?_append, List.find?_append, List.find?_append, n1, n2, n3]
  simp only [Option.none_or, Option.or_none]
  exact delta_find b f a

theorem deltas_none (pre post : Values) (f : Nat) (v : String) (hne : ∀ m : Nat, fieldName m "delta" ≠ fieldName f v) :
    (post.filterMap (fun p => (gt pre p.1).map fun old => (fieldName p.1 "delta", p.2 - old))).find?
      (fun q => q.1 == fieldName f v) = none := by
  apply find_none
  intro q hq
  obtain ⟨m, e⟩ := mem_deltas hq
  rw [e]; exact hne m

theorem pairs_none' (pre post : Values) (f : Nat) (v : String) :
    (post.flatMap (fun a => post.filterMap fun b => do
        let oldA ← gt pre a.1
        let oldB ← gt pre b.1
        return (pairName a.1 b.1, a.2 + b.2 - oldA - oldB))).find? (fun q => q.1 == fieldName f v) = none := by
  apply find_none
  intro q hq
  obtain ⟨a, b, e⟩ := mem_pairs hq
  rw [e]; exact pairName_ne_fieldName _ _ _ _

theorem scalar_before (b a : Values) (f : Nat) :
    State.get ⟨scalarSlots b a⟩ (fieldName f "before") = gt b f := by
  rw [state_get, scalarSlots_split]
  have n2 := map_none_of a "after" "before" f (fun x y => (before_ne_after y x).symm)
  have n3 := deltas_none b a f "before" (fun m => (before_ne_delta f m).symm)
  have n4 := pairs_none' b a f "before"
  rw [List.find?_append, List.find?_append, List.find?_append, n2, n3, n4]
  rw [← find_map_key b "before" f]
  simp only [Option.none_or, Option.or_none]

theorem scalar_after (b a : Values) (f : Nat) :
    State.get ⟨scalarSlots b a⟩ (fieldName f "after") = gt a f := by
  rw [state_get, scalarSlots_split]
  have n1 := map_none_of b "before" "after" f before_ne_after
  have n3 := deltas_none b a f "after" (fun m => (after_ne_delta f m).symm)
  have n4 := pairs_none' b a f "after"
  rw [List.find?_append, List.find?_append, List.find?_append, n1, n3, n4]
  rw [← find_map_key a "after" f]
  simp only [Option.none_or, Option.or_none]



/-- A key whose tenth character is not `f`: never a `resource/field/..` name. -/
def Foreign (k : String) : Prop := k.toList[9]? ≠ some 'f'

theorem idx9_append (s t : String) (h : 9 < s.toList.length) : (s ++ t).toList[9]? = s.toList[9]? := by
  rw [String.toList_append, List.getElem?_append_left h]

theorem field_not_foreign (f : Nat) (v : String) : ¬ Foreign (fieldName f v) := by
  unfold Foreign; intro h; apply h
  rw [show fieldName f v = "resource/field/" ++ (toString f ++ "/" ++ v) by
    rw [fieldName_def]; simp only [String.append_assoc]]
  rw [idx9_append _ _ (by decide)]; decide

def AllForeign (xs : List (String × Int)) : Prop := ∀ p ∈ xs, Foreign p.1

theorem allForeign_append {xs ys : List (String × Int)} (hx : AllForeign xs) (hy : AllForeign ys) :
    AllForeign (xs ++ ys) := by
  intro p hp; rcases List.mem_append.mp hp with h | h
  · exact hx p h
  · exact hy p h

theorem get_none_of_foreign (xs : List (String × Int)) (h : AllForeign xs) (f : Nat) (v : String) :
    State.get ⟨xs⟩ (fieldName f v) = none :=
  get_none _ _ fun p hp e => field_not_foreign f v (e ▸ h p hp)

theorem bytes_foreign (stem : String) (h : 9 < stem.toList.length) (hs : stem.toList[9]? ≠ some 'f') :
    ∀ (o : Nat) (bs : List UInt8), AllForeign (ResourceAuthorityProjection.bytesSlots stem o bs)
  | _, [] => by intro p hp; simp [ResourceAuthorityProjection.bytesSlots] at hp
  | o, b :: rest => by
      intro p hp
      simp only [ResourceAuthorityProjection.bytesSlots, List.mem_cons] at hp
      rcases hp with rfl | hp
      · show Foreign (stem ++ "/" ++ toString o)
        unfold Foreign; simp only [String.append_assoc]; rw [idx9_append _ _ h]; exact hs
      · exact bytes_foreign stem h hs (o + 1) rest p hp


theorem request_foreign {kind : ResourceKind} (request : Minidregg.Theory.TypedAuthorization.Request kind) :
    AllForeign (CanonicalRuntimeProfile.requestSlots request) := by
  intro p hp
  simp only [CanonicalRuntimeProfile.requestSlots, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    dsimp only <;> unfold Foreign <;> decide

theorem common_foreign (prepared : PreparedInvocation deployment profile ambient ground command)
    (primary : Incidence command) (source : Source command) :
    AllForeign (projectCommonSlots prepared primary source) := by
  unfold projectCommonSlots
  refine allForeign_append (allForeign_append (allForeign_append (allForeign_append
    (allForeign_append (allForeign_append ?_ ?_) ?_) (request_foreign _)) ?_) ?_) ?_
  · intro p hp; simp only [objectiveSlots, List.mem_singleton] at hp; subst p
    show Foreign "objective/artifact"; unfold Foreign; decide
  · intro p hp; simp only [List.mem_singleton] at hp; subst p; show Foreign "target/storageKind"; unfold Foreign; decide
  · intro p hp
    simp only [Minidregg.Kernel.ClockCell.slots, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl <;> dsimp only <;> unfold Foreign <;> decide
  · exact bytes_foreign "command/bytes" (by decide) (by decide) _ _
  · intro p hp
    cases run : prepared.run with
    | none => simp [runSlots, run] at hp
    | some checked =>
      simp only [runSlots, run, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl
      · unfold Foreign Minidregg.Pred.ranSlot
        rw [idx9_append _ _ (by decide)]; decide
      · unfold Foreign Minidregg.Pred.evaluatorSlot
        rw [idx9_append _ _ (by decide)]; decide
      · dsimp only; unfold Foreign; decide
      · dsimp only; unfold Foreign; decide
  · intro p hp
    cases computed : prepared.compute with
    | none => simp [computeSlots, computed] at hp
    | some budget =>
      simp only [computeSlots, computed, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl <;> dsimp only <;> unfold Foreign <;> decide

theorem joint_foreign (targets : List Target) (slots : Fin targets.length → List (String × Int)) :
    AllForeign (Minidregg.Kernel.DeclaredResourceController.jointSlots targets slots) := by
  intro p hp
  simp only [Minidregg.Kernel.DeclaredResourceController.jointSlots, List.mem_append, List.mem_flatMap, List.mem_map] at hp
  rcases hp with ⟨i, -, q, -, rfl⟩ | ⟨i, -, q, -, rfl⟩
  · unfold Foreign jointTargetKey; simp only [String.append_assoc]
    rw [idx9_append _ _ (by decide)]; decide
  · unfold Foreign jointIndexKey; simp only [String.append_assoc]
    rw [idx9_append _ _ (by decide)]; decide

/-- A `resource/field` name is read from the primary participant's own slots only. -/
theorem local_field_exact (prepared : PreparedInvocation deployment profile ambient ground command)
    (primary : Incidence command) (source : Source command)
    (logical : (incidence : Incidence command) → Store ((layout prepared).storeLayout incidence))
    (f : Nat) (v : String) :
    (project prepared primary source logical).get (fieldName f v) =
      State.get ⟨participantSlots prepared logical (primary.getD (firstIndex prepared))⟩ (fieldName f v) := by
  unfold project projectWithCommon
  rw [JointSlots.get_append, JointSlots.get_append,
    get_none_of_foreign _ (common_foreign prepared primary source) f v, Option.none_or,
    get_none_of_foreign _ (joint_foreign _ _) f v, Option.or_none]

theorem target_scalar (subject : SubjectId) (target : Target) (h : ∃ s, target.payload = .scalar s) (before after : Store target.layout) :
    ∃ b a : Values, targetProjection subject target before after = scalarSlots b a := by
  obtain ⟨k, i, c, v, r, p, o, ae, ar⟩ := target
  obtain ⟨s, h⟩ := h
  simp only at h
  subst h
  exact ⟨_, _, rfl⟩

theorem participant_field (prepared : PreparedInvocation deployment profile ambient ground command)
    (logical : (incidence : Incidence command) → Store ((layout prepared).storeLayout incidence))
    (i : TargetIndex command)
    (h : ∃ s, command.targets[i].payload = .scalar s) :
    ∃ b a : Values, ∀ f v, State.get ⟨participantSlots prepared logical i⟩ (fieldName f v) =
      State.get ⟨scalarSlots b a⟩ (fieldName f v) := by
  obtain ⟨b, a, e⟩ := target_scalar command.subject command.targets[i] h
    (prepared.targets i).pre.logical (logical (some i))
  refine ⟨b, a, fun f v => ?_⟩
  have money : moneyPolicySlots prepared i = [] := by
    obtain ⟨s, h⟩ := h
    unfold moneyPolicySlots; rw [h]; cases prepared.money <;> rfl
  unfold participantSlots
  rw [e, money, List.append_nil, JointSlots.get_append,
    get_none_of_foreign _ (bytes_foreign "resource/bytes" (by decide) (by decide) _ _) f v, Option.none_or]


end Scalar

/-! ## §1. The premises, on the controller's states -/

/-- `n` is the full projected new state of the controller's step (`fullStep`; the step the law
is judged on is it cut to the law's reads, with the same verdict) for a checked write leg on a cell carrying the
sealed story law of `t` for player `S`. -/
def Realized (t : Table) (S : Int) (n : State) : Prop :=
  ∃ (F : Type) (_ : Field F) (_ : DecidableEq F) (deployment : Deployment)
    (profile : CanonicalRuntimeProfile.Profile F) (ambient : Ambient)
    (ground : Ground deployment) (command : Command)
    (prepared : PreparedInvocation deployment profile ambient ground command)
    (tuple : PreparedTuple (plan prepared)) (incidence : Incidence command) (envelope : List UInt8),
    Nonempty (CheckedLeg prepared tuple incidence envelope) ∧
    StoryInstalled t S tuple incidence ∧
    (∃ s, command.targets[incidence.getD (firstIndex prepared)].payload = .scalar s) ∧
    (fullStep prepared tuple incidence).newState = n ∧
    n.get "request/verb" = some 2

theorem realized_step {t : Table} {S : Int} {n : State} (h : Realized t S n) : Step t S n := by
  obtain ⟨F, _, _, deployment, profile, ambient, ground, command, prepared, tuple, incidence,
    envelope, ⟨leg⟩, installed, -, rfl, w⟩ := h
  exact kernel_story_step_full t S leg installed w

/-- **R1.** A realized leg's `resource/field` keys are read from `scalarSlots` of the cell's
before and after field stores. -/
theorem realized_scalar {t : Table} {S : Int} {n : State} (h : Realized t S n) :
    ∃ b a : Values, ∀ f v, n.get (fieldName f v) = State.get ⟨scalarSlots b a⟩ (fieldName f v) := by
  obtain ⟨F, _, _, deployment, profile, ambient, ground, command, prepared, tuple, incidence,
    envelope, -, -, sc, rfl, -⟩ := h
  obtain ⟨b, a, e⟩ := participant_field prepared (policyPostState prepared)
    (incidence.getD (firstIndex prepared)) sc
  refine ⟨b, a, fun f v => ?_⟩
  rw [← e f v]
  have post : tuple.logicalPost = policyPostState prepared :=
    funext fun i => (policyPostState_exact prepared tuple i).symm
  change (project prepared incidence tuple.source tuple.logicalPost).get _ = _
  rw [post]
  exact local_field_exact prepared incidence tuple.source (policyPostState prepared) f v

/-- The scene (field 0) and turn (field 1) slots of a leg's state are an arithmetic row. -/
def Coherent (n : State) : Prop :=
  ∀ f : Nat, f ≤ 1 → ∃ b a : Int, n.get (fieldName f "before") = some b ∧
    n.get (fieldName f "after") = some a ∧ n.get (fieldName f "delta") = some (a - b)

theorem coherent_of_step {t : Table} {S : Int} {n : State} (st : Step t S n)
    (sc : ∃ b a : Values, ∀ f v, n.get (fieldName f v) = State.get ⟨scalarSlots b a⟩ (fieldName f v)) :
    Coherent n := by
  obtain ⟨b, a, e⟩ := sc
  have gb : ∀ f, n.get (fieldName f "before") = gt b f := fun f => by rw [e, scalar_before]
  have ga : ∀ f, n.get (fieldName f "after") = gt a f := fun f => by rw [e, scalar_after]
  have gd : ∀ f, n.get (fieldName f "delta") = (gt a f).bind fun y => (gt b f).map fun x => y - x :=
    fun f => by rw [e, scalar_delta]
  have both : ∀ f (d : Int), n.get (fieldName f "delta") = some d →
      ∃ x y : Int, gt b f = some x ∧ gt a f = some y ∧ d = y - x := by
    intro f d h
    rw [gd] at h
    cases hy : gt a f with
    | none => simp [hy] at h
    | some y =>
        cases hx : gt b f with
        | none => simp [hy, hx] at h
        | some x => simp [hy, hx] at h; exact ⟨x, y, rfl, rfl, h.symm⟩
  intro f hf
  have hf' : f = 0 ∨ f = 1 := by omega
  rcases hf' with rfl | rfl
  · rcases st.scene with h | ⟨e', he', h1, h2⟩
    · obtain ⟨x, y, hx, hy, -⟩ := both 0 0 h
      exact ⟨x, y, by rw [gb, hx], by rw [ga, hy], by rw [gd, hy, hx]; rfl⟩
    · have h1' := h1; have h2' := h2
      rw [gb] at h1'; rw [ga] at h2'
      exact ⟨e'.src, e'.dst, h1, h2, by rw [gd, h1', h2']; rfl⟩
  · obtain ⟨x, y, hx, hy, -⟩ := both 1 1 st.turn
    exact ⟨x, y, by rw [gb, hx], by rw [ga, hy], by rw [gd, hy, hx]; rfl⟩

/-- The next leg starts where the previous one ended. -/
def Links (n m : State) : Prop :=
  n.get (fieldName 0 "after") = m.get (fieldName 0 "before") ∧
  n.get (fieldName 1 "after") = m.get (fieldName 1 "before")

def Chained : List State → Prop
  | n :: m :: rest => Links n m ∧ Chained (m :: rest)
  | _ => True

/-! ## §2. The theorem -/

/-- **`story_history_monotone`.** For a chain of the controller's checked story legs that starts at
scene `a`, turn `k`: every leg is the player's, moves the scene along a table edge or not at all
(no skip), and raises the turn by exactly one, so the last leg ends at turn `k + length` (no
rewind). Generic over the leg predicate `R` that yields `Step` (`Realized` is the instance). -/
theorem story_history_monotone_of (t : Table) (S : Int) (R : State → Prop)
    (hR : ∀ n, R n → Step t S n) :
    ∀ (ns : List State) (a k : Int),
      (∀ n ∈ ns, R n) → (∀ n ∈ ns, Coherent n) → Chained ns →
      (∀ n, ns.head? = some n → n.get (fieldName 0 "before") = some a ∧
        n.get (fieldName 1 "before") = some k) →
      (∀ n ∈ ns, n.get "request/subject" = some S ∧ ∃ x y m : Int,
          n.get (fieldName 0 "before") = some x ∧ n.get (fieldName 0 "after") = some y ∧
          n.get (fieldName 1 "before") = some m ∧ n.get (fieldName 1 "after") = some (m + 1) ∧
          (y = x ∨ ∃ e ∈ t.edges, e.src = x ∧ e.dst = y)) ∧
      (∀ n, ns.getLast? = some n → n.get (fieldName 1 "after") = some (k + ns.length)) := by
  intro ns
  induction ns with
  | nil => intro a k _ _ _ _; exact ⟨fun n hn => by simp at hn, fun n hn => by simp at hn⟩
  | cons n rest ih =>
      intro a k hR' hCoh hCh hStart
      have hn := hR _ (hR' n (by simp))
      obtain ⟨b0, a0, hb0, ha0, hd0⟩ := hCoh n (by simp) 0 (by omega)
      obtain ⟨b1, a1, hb1, ha1, hd1⟩ := hCoh n (by simp) 1 (by omega)
      obtain ⟨hb0', hb1'⟩ := hStart n (by simp)
      have e0 : b0 = a := by rw [hb0] at hb0'; exact Option.some.inj hb0'
      have e1 : b1 = k := by rw [hb1] at hb1'; exact Option.some.inj hb1'
      have d1 : a1 = b1 + 1 := by
        have := hn.turn; rw [hd1] at this; have := Option.some.inj this; omega
      have scene : a0 = b0 ∨ ∃ e ∈ t.edges, n.get (fieldName 0 "before") = some e.src ∧
          n.get (fieldName 0 "after") = some e.dst := by
        rcases hn.scene with h | h
        · left; rw [hd0] at h; have := Option.some.inj h; omega
        · right; exact h
      have headFacts : n.get "request/subject" = some S ∧ ∃ x y m : Int,
          n.get (fieldName 0 "before") = some x ∧ n.get (fieldName 0 "after") = some y ∧
          n.get (fieldName 1 "before") = some m ∧ n.get (fieldName 1 "after") = some (m + 1) ∧
          (y = x ∨ ∃ e ∈ t.edges, e.src = x ∧ e.dst = y) := by
        refine ⟨hn.subject, b0, a0, b1, hb0, ha0, hb1, by rw [ha1, d1], ?_⟩
        rcases scene with h | ⟨e, he, h1, h2⟩
        · left; exact h
        · right
          refine ⟨e, he, ?_, ?_⟩
          · rw [hb0] at h1; exact (Option.some.inj h1).symm
          · rw [ha0] at h2; exact (Option.some.inj h2).symm
      cases rest with
      | nil =>
          refine ⟨?_, ?_⟩
          · intro m hm; simp at hm; subst hm; exact headFacts
          · intro m hm; simp at hm; subst hm; rw [ha1, d1, e1]; simp
      | cons m rest' =>
          obtain ⟨⟨l0, l1⟩, hCh'⟩ := hCh
          have hm0 : m.get (fieldName 0 "before") = some a0 := by rw [← l0, ha0]
          have hm1 : m.get (fieldName 1 "before") = some (k + 1) := by rw [← l1, ha1, d1, e1]
          obtain ⟨hall, hlast⟩ := ih a0 (k + 1)
            (fun x hx => hR' x (by simp [hx])) (fun x hx => hCoh x (by simp [hx])) hCh'
            (fun x hx => by simp at hx; subst hx; exact ⟨hm0, hm1⟩)
          refine ⟨?_, ?_⟩
          · intro x hx
            rcases List.mem_cons.mp hx with rfl | hx
            · exact headFacts
            · exact hall x hx
          · intro x hx
            have := hlast x (by simpa [List.getLast?_cons_cons] using hx)
            rw [this]; simp only [List.length_cons]; congr 1; push_cast; ring

theorem story_history_monotone (t : Table) (S : Int) (ns : List State) (a k : Int)
    (real : ∀ n ∈ ns, Realized t S n) (chain : Chained ns)
    (start : ∀ n, ns.head? = some n → n.get (fieldName 0 "before") = some a ∧
      n.get (fieldName 1 "before") = some k) :
    (∀ n ∈ ns, n.get "request/subject" = some S ∧ ∃ x y m : Int,
        n.get (fieldName 0 "before") = some x ∧ n.get (fieldName 0 "after") = some y ∧
        n.get (fieldName 1 "before") = some m ∧ n.get (fieldName 1 "after") = some (m + 1) ∧
        (y = x ∨ ∃ e ∈ t.edges, e.src = x ∧ e.dst = y)) ∧
    (∀ n, ns.getLast? = some n → n.get (fieldName 1 "after") = some (k + ns.length)) :=
  story_history_monotone_of t S (Realized t S) (fun _ h => realized_step h) ns a k real
    (fun n hn => coherent_of_step (realized_step (real n hn)) (realized_scalar (real n hn))) chain start

/-! ## §3. Poles on the tale (player 7)

Satisfiable: a four-leg play-through of `taleTable` meets every premise of
`story_history_monotone_of` with `R := Step` (the part of `Realized` this file can inhabit; (R3)
above is the controller side) and its conclusion says the last leg ends at turn 4.
Teeth: a skipped scene and a repeated turn are not `Step`s (so not `Realized`); a chain whose next
leg does not start where the last ended is not `Chained`; and dropping `Chained` is load-bearing:
two legs that are each lawful, coherent and correctly started, whose last turn is not `k + length`. -/

/-- A leg of player 7's cell: scene `x` to `y`, turn `m` to `m + b`; the slots the law reads. -/
def leg (x y m b : Int) : State :=
  ⟨[("request/subject", 7), ("request/verb", 2),
    (fieldName 0 "before", x), (fieldName 0 "after", y), (fieldName 0 "delta", y - x),
    (fieldName 1 "before", m), (fieldName 1 "after", m + b), (fieldName 1 "delta", b)]⟩

section LegGet
variable (x y m b : Int)

private theorem ne_sym {α : Type} {a c : α} (h : a ≠ c) : c ≠ a := fun e => h e.symm

theorem leg_subject : (leg x y m b).get "request/subject" = some 7 := by
  simp [leg, State.get]
theorem leg_verb : (leg x y m b).get "request/verb" = some 2 := by
  have h : "request/verb" ≠ "request/subject" := by decide
  simp [leg, State.get, h]
theorem leg_b0 : (leg x y m b).get (fieldName 0 "before") = some x := by
  have h1 : fieldName 0 "before" ≠ "request/subject" := by decide
  have h2 : fieldName 0 "before" ≠ "request/verb" := by decide
  simp [leg, State.get, ne_sym h1, ne_sym h2]
theorem leg_a0 : (leg x y m b).get (fieldName 0 "after") = some y := by
  have h1 : fieldName 0 "after" ≠ "request/subject" := by decide
  have h2 : fieldName 0 "after" ≠ "request/verb" := by decide
  have h3 : fieldName 0 "after" ≠ fieldName 0 "before" := by decide
  simp [leg, State.get, ne_sym h1, ne_sym h2, ne_sym h3]
theorem leg_d0 : (leg x y m b).get (fieldName 0 "delta") = some (y - x) := by
  have h1 : fieldName 0 "delta" ≠ "request/subject" := by decide
  have h2 : fieldName 0 "delta" ≠ "request/verb" := by decide
  have h3 : fieldName 0 "delta" ≠ fieldName 0 "before" := by decide
  have h4 : fieldName 0 "delta" ≠ fieldName 0 "after" := by decide
  simp [leg, State.get, ne_sym h1, ne_sym h2, ne_sym h3, ne_sym h4]
theorem leg_b1 : (leg x y m b).get (fieldName 1 "before") = some m := by
  have h1 : fieldName 1 "before" ≠ "request/subject" := by decide
  have h2 : fieldName 1 "before" ≠ "request/verb" := by decide
  have h3 : fieldName 1 "before" ≠ fieldName 0 "before" := by decide
  have h4 : fieldName 1 "before" ≠ fieldName 0 "after" := by decide
  have h5 : fieldName 1 "before" ≠ fieldName 0 "delta" := by decide
  simp [leg, State.get, ne_sym h1, ne_sym h2, ne_sym h3, ne_sym h4, ne_sym h5]
theorem leg_a1 : (leg x y m b).get (fieldName 1 "after") = some (m + b) := by
  have h1 : fieldName 1 "after" ≠ "request/subject" := by decide
  have h2 : fieldName 1 "after" ≠ "request/verb" := by decide
  have h3 : fieldName 1 "after" ≠ fieldName 0 "before" := by decide
  have h4 : fieldName 1 "after" ≠ fieldName 0 "after" := by decide
  have h5 : fieldName 1 "after" ≠ fieldName 0 "delta" := by decide
  have h6 : fieldName 1 "after" ≠ fieldName 1 "before" := by decide
  simp [leg, State.get, ne_sym h1, ne_sym h2, ne_sym h3, ne_sym h4, ne_sym h5, ne_sym h6]
theorem leg_d1 : (leg x y m b).get (fieldName 1 "delta") = some b := by
  have h1 : fieldName 1 "delta" ≠ "request/subject" := by decide
  have h2 : fieldName 1 "delta" ≠ "request/verb" := by decide
  have h3 : fieldName 1 "delta" ≠ fieldName 0 "before" := by decide
  have h4 : fieldName 1 "delta" ≠ fieldName 0 "after" := by decide
  have h5 : fieldName 1 "delta" ≠ fieldName 0 "delta" := by decide
  have h6 : fieldName 1 "delta" ≠ fieldName 1 "before" := by decide
  have h7 : fieldName 1 "delta" ≠ fieldName 1 "after" := by decide
  simp [leg, State.get, ne_sym h1, ne_sym h2, ne_sym h3, ne_sym h4, ne_sym h5, ne_sym h6, ne_sym h7]
end LegGet

theorem coherent_leg (x y m : Int) : Coherent (leg x y m 1) := by
  intro f hf
  have : f = 0 ∨ f = 1 := by omega
  rcases this with rfl | rfl
  · exact ⟨x, y, leg_b0 .., leg_a0 .., leg_d0 ..⟩
  · exact ⟨m, m + 1, leg_b1 .., leg_a1 .., by simpa using leg_d1 x y m 1⟩

theorem step_leg_of_edge (x y m : Int) (e : Edge) (he : e ∈ taleTable.edges) (h1 : e.src = x)
    (h2 : e.dst = y) : Step taleTable 7 (leg x y m 1) :=
  ⟨leg_subject .., leg_d1 .., Or.inr ⟨e, he, by rw [leg_b0, h1], by rw [leg_a0, h2]⟩⟩

theorem step_leg_stay (x m : Int) : Step taleTable 7 (leg x x m 1) :=
  ⟨leg_subject .., leg_d1 .., Or.inl (by rw [leg_d0]; simp)⟩

/-- hallway to anteroom, take the key (the scene stays), anteroom to landing, landing to lamp room. -/
def play : List State := [leg 0 1 0 1, leg 1 1 1 1, leg 1 3 2 1, leg 3 4 3 1]

theorem play_chained : Chained play := by
  simp [play, Chained, Links, leg_b0, leg_a0, leg_b1, leg_a1, leg_d0, leg_d1, leg_subject, leg_verb]

theorem play_steps : ∀ n ∈ play, Step taleTable 7 n := by
  intro n hn
  simp only [play, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl
  · exact step_leg_of_edge 0 1 0 ⟨0, 1, none⟩ (by decide) rfl rfl
  · exact step_leg_stay 1 1
  · exact step_leg_of_edge 1 3 2 ⟨1, 3, some 0⟩ (by decide) rfl rfl
  · exact step_leg_of_edge 3 4 3 ⟨3, 4, none⟩ (by decide) rfl rfl

theorem play_coherent : ∀ n ∈ play, Coherent n := by
  intro n hn
  simp only [play, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl <;> exact coherent_leg _ _ _

/-- **Satisfiable.** Every premise of the history theorem holds of a real play-through, and its
conclusion is the expected one: the last leg ends at turn 4. -/
theorem history_satisfiable :
    play ≠ [] ∧ (∀ n ∈ play, Step taleTable 7 n) ∧ (∀ n ∈ play, Coherent n) ∧ Chained play ∧
    (∀ n, play.head? = some n → n.get (fieldName 0 "before") = some 0 ∧
      n.get (fieldName 1 "before") = some 0) ∧
    (∀ n, play.getLast? = some n → n.get (fieldName 1 "after") = some (0 + play.length)) := by
  refine ⟨by simp [play], play_steps, play_coherent, play_chained, ?_, ?_⟩
  · intro n hn; simp [play] at hn; subst hn; simp [leg_b0, leg_a0, leg_b1, leg_a1, leg_d0, leg_d1, leg_subject, leg_verb]
  · intro n hn; simp [play] at hn; subst hn; simp [leg_b0, leg_a0, leg_b1, leg_a1, leg_d0, leg_d1, leg_subject, leg_verb, play]

/-- **Teeth (skip).** Scene 0 straight to scene 3 is no `Step`, hence no `Realized`. -/
theorem skip_not_step : ¬ Step taleTable 7 (leg 0 3 0 1) := by
  rintro ⟨-, -, h⟩
  rcases h with h | ⟨e, he, h1, h2⟩
  · simp [leg_b0, leg_a0, leg_b1, leg_a1, leg_d0, leg_d1, leg_subject, leg_verb] at h
  · simp only [taleTable, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl <;> simp [leg_b0, leg_a0, leg_b1, leg_a1, leg_d0, leg_d1, leg_subject, leg_verb] at h1 h2

/-- **Teeth (repeat).** A leg that leaves the turn where it was is no `Step`. -/
theorem repeat_not_step : ¬ Step taleTable 7 (leg 0 1 0 0) := by
  rintro ⟨-, h, -⟩
  simp [leg_b0, leg_a0, leg_b1, leg_a1, leg_d0, leg_d1, leg_subject, leg_verb] at h

/-- **Teeth (rewind).** A next leg that starts at an earlier turn is not linked. -/
theorem rewind_not_chained : ¬ Chained [leg 0 1 1 1, leg 1 2 0 1] := by
  simp [Chained, Links, leg_b0, leg_a0, leg_b1, leg_a1, leg_d0, leg_d1, leg_subject, leg_verb]

/-- **Teeth (the chain is load-bearing).** Two lawful, coherent, correctly started legs that do not
link: the history conclusion fails, so `Chained` cannot be dropped. -/
theorem unchained_breaks_conclusion :
    (∀ n ∈ [leg 0 1 0 1, leg 1 2 0 1], Step taleTable 7 n) ∧
    (∀ n ∈ [leg 0 1 0 1, leg 1 2 0 1], Coherent n) ∧
    ¬ Chained [leg 0 1 0 1, leg 1 2 0 1] ∧
    (∀ n, ([leg 0 1 0 1, leg 1 2 0 1] : List State).getLast? = some n →
      n.get (fieldName 1 "after") ≠ some (0 + ([leg 0 1 0 1, leg 1 2 0 1] : List State).length)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro n hn
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with rfl | rfl
    · exact step_leg_of_edge 0 1 0 ⟨0, 1, none⟩ (by decide) rfl rfl
    · exact step_leg_of_edge 1 2 0 ⟨1, 2, none⟩ (by decide) rfl rfl
  · intro n hn
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with rfl | rfl <;> exact coherent_leg _ _ _
  · simp [Chained, Links, leg_b0, leg_a0, leg_b1, leg_a1, leg_d0, leg_d1, leg_subject, leg_verb]
  · intro n hn; simp at hn; subst hn; simp [leg_b0, leg_a0, leg_b1, leg_a1, leg_d0, leg_d1, leg_subject, leg_verb]


/-- info: 'Minidregg.Assurance.StoryHistory.realized_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms realized_step
/-- info: 'Minidregg.Assurance.StoryHistory.story_history_monotone_of' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms story_history_monotone_of
/-- info: 'Minidregg.Assurance.StoryHistory.story_history_monotone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms story_history_monotone
/-- info: 'Minidregg.Assurance.StoryHistory.history_satisfiable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms history_satisfiable
/-- info: 'Minidregg.Assurance.StoryHistory.skip_not_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms skip_not_step
/-- info: 'Minidregg.Assurance.StoryHistory.repeat_not_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms repeat_not_step
/-- info: 'Minidregg.Assurance.StoryHistory.rewind_not_chained' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms rewind_not_chained
/-- info: 'Minidregg.Assurance.StoryHistory.unchained_breaks_conclusion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms unchained_breaks_conclusion

end Minidregg.Assurance.StoryHistory
