/-
The kernel-side vocabulary a declared-resource law is read through: what an atom of `Pred`
means as a proposition (§1), and the slot list the kernel hands a policy for one step over the
declared field store, with the lookup lemmas that resolve every name a law reads to the store
value (§2). Extracted from the MUD sheet law (`Assurance/SheetLaw.lean` §3 and §6) so that a
Kernel law (`Kernel/Job.lean`) reads it without importing Assurance; the sheet and item laws
read it from here too.
-/
import Pred.Core
import Kernel.DeclaredResourceProjection

namespace Minidregg.Kernel.LawView

open Minidregg.Pred (Pred State eval)
open Minidregg.Kernel.DeclaredResourceProjection (Values fieldName pairName scalarSlots)
set_option autoImplicit false

/-! ## §1. Reading atoms as propositions -/

section Atoms
variable {o n : State}

theorem ev_eq {s : String} {v : Int} : eval (.eq s v) o n = true ↔ n.get s = some v := by
  simp [eval, Minidregg.Pred.evalWith]

theorem ev_le {s : String} {v : Int} :
    eval (.le s v) o n = true ↔ ∃ x, n.get s = some x ∧ x ≤ v := by
  simp only [eval, Minidregg.Pred.evalWith]; cases n.get s <;> simp

theorem ev_memberOf {s : String} {xs : List Int} :
    eval (.memberOf s xs) o n = true ↔ ∃ x, n.get s = some x ∧ x ∈ xs := by
  simp only [eval, Minidregg.Pred.evalWith]; cases n.get s <;> simp

theorem ev_monotone {s : String} :
    eval (.monotone s) o n = true ↔ ∃ a b, o.get s = some a ∧ n.get s = some b ∧ a ≤ b := by
  simp only [eval, Minidregg.Pred.evalWith]; cases o.get s <;> cases n.get s <;> simp

theorem ev_eqSlots {a b : String} :
    eval (.eqSlots a b) o n = true ↔ ∃ x, n.get a = some x ∧ n.get b = some x := by
  simp only [eval, Minidregg.Pred.evalWith]; cases n.get a <;> cases n.get b <;> simp [eq_comm]

theorem ev_leSlots {a b : String} :
    eval (.leSlots a b) o n = true ↔ ∃ x y, n.get a = some x ∧ n.get b = some y ∧ x ≤ y := by
  simp only [eval, Minidregg.Pred.evalWith]; cases n.get a <;> cases n.get b <;> simp [eq_comm]

theorem ev_leSlotsOff {a b : String} {k : Int} :
    eval (.leSlotsOff a b k) o n = true ↔
      ∃ x y, n.get a = some x ∧ n.get b = some y ∧ x ≤ y + k := by
  simp only [eval, Minidregg.Pred.evalWith]; cases n.get a <;> cases n.get b <;> simp

theorem ev_not {q : Pred} : eval (.not q) o n = true ↔ ¬ eval q o n = true := by
  simp [Minidregg.Pred.eval_not]

theorem ev_all {ps : List Pred} : eval (Pred.all ps) o n = true ↔ ∀ q ∈ ps, eval q o n = true := by
  simp [Minidregg.Pred.eval_all]

theorem ev_any {ps : List Pred} : eval (Pred.any ps) o n = true ↔ ∃ q ∈ ps, eval q o n = true := by
  simp [Minidregg.Pred.eval_any]

end Atoms

/-! ## §2. The kernel's view of one step over the declared field store

`view t pre post` is the slot list `DeclaredResourceController.projectWithCommon` hands the policy for
the primary target, restricted to what this law reads: the two request slots it names
(`CanonicalRuntimeProfile.requestSlots` spells them `request/verb`, `request/subject`), then the
target's own `scalarSlots pre post` (the kernel function, not a copy), then the slots that have not
landed: `clock/now` (K-CLOCK) and `joint/index/{i}/resource/field/{n}/{view}` (K-JOINT-INDEX), each
optional. The policy's old state is `view t pre pre` and its new state `view t pre post`
(`PolicyStepContext.ofPreparedTuple`: `project logicalPre`, `project logicalPost`, both against the
pre-state). The lookup lemmas below prove that the names the law reads resolve to the store values,
whatever the store holds. -/

/-- The request slots the law reads. -/
def request (verb subject : Int) : List (String × Int) :=
  [("request/verb", verb), ("request/subject", subject)]

/-- K-CLOCK's slot, when it is present. -/
def clockSlots : Option Int → List (String × Int)
  | none => []
  | some t => [("clock/now", t)]

/-- K-JOINT-INDEX's slot name, as `render.py` spells it. -/
def jointName (i n : Nat) (v : String) : String := s!"joint/index/{i}/resource/field/{n}/{v}"

def jointSlots (j : List (Nat × Nat × String × Int)) : List (String × Int) :=
  j.map fun q => (jointName q.1 q.2.1 q.2.2.1, q.2.2.2)

/-- One mutate or observe on the cell: who, which verb, the clock and joint slots the step exposes
(empty on this branch), and the post-state of the declared fields. -/
structure Turn where
  verb : Int
  subject : Int
  now : Option Int
  joint : List (Nat × Nat × String × Int)
  post : Values

def view (t : Turn) (pre post : Values) : State :=
  ⟨request t.verb t.subject ++ scalarSlots pre post ++ clockSlots t.now ++ jointSlots t.joint⟩

/-- The law's verdict on a turn from `pre`. -/
def admits (law : Pred) (pre : Values) (t : Turn) : Bool :=
  eval law (view t pre pre) (view t pre t.post)

section Names

def lastc (s : String) : Option Char := s.toList.getLast?
def headc (s : String) : Option Char := s.toList.head?

theorem lastc_append (s t : String) (h : t.toList ≠ []) : lastc (s ++ t) = lastc t := by
  unfold lastc
  rw [String.toList_append, List.getLast?_append]
  cases hl : t.toList.getLast? with
  | none => exact absurd (List.getLast?_eq_none_iff.mp hl) h
  | some c => rfl

theorem headc_append (s t : String) (h : s.toList ≠ []) : headc (s ++ t) = headc s := by
  unfold headc
  rw [String.toList_append]
  cases hs : s.toList with
  | nil => exact absurd hs h
  | cons c cs => rfl

theorem ne_of_lastc {s t : String} (h : lastc s ≠ lastc t) : s ≠ t := fun e => h (congrArg lastc e)
theorem ne_of_headc {s t : String} (h : headc s ≠ headc t) : s ≠ t := fun e => h (congrArg headc e)

theorem fieldName_def (N : Nat) (v : String) :
    fieldName N v = "resource/field/" ++ toString N ++ "/" ++ v := rfl

theorem pairName_def (a b : Nat) :
    pairName a b = "resource/pair/" ++ toString a ++ "/" ++ toString b ++ "/delta" := rfl

theorem jointName_def (i n : Nat) (v : String) :
    jointName i n v = "joint/index/" ++ toString i ++ "/resource/field/" ++ toString n ++ "/" ++ v :=
  rfl

theorem lastc_fieldName (N : Nat) (v : String) (h : v.toList ≠ []) :
    lastc (fieldName N v) = lastc v := by
  rw [fieldName_def]; exact lastc_append _ _ h

theorem lastc_after (N : Nat) : lastc (fieldName N "after") = some 'r' := by
  rw [lastc_fieldName _ _ (by decide)]; decide
theorem lastc_before (N : Nat) : lastc (fieldName N "before") = some 'e' := by
  rw [lastc_fieldName _ _ (by decide)]; decide
theorem lastc_delta (N : Nat) : lastc (fieldName N "delta") = some 'a' := by
  rw [lastc_fieldName _ _ (by decide)]; decide
theorem lastc_pairName (a b : Nat) : lastc (pairName a b) = some 'a' := by
  rw [pairName_def, lastc_append _ _ (by decide)]; decide

theorem headc_fieldName (N : Nat) (v : String) : headc (fieldName N v) = some 'r' := by
  rw [fieldName_def]; simp only [String.append_assoc]
  rw [headc_append _ _ (by decide)]; decide
theorem headc_jointName (i n : Nat) (v : String) : headc (jointName i n v) = some 'j' := by
  rw [jointName_def]; simp only [String.append_assoc]
  rw [headc_append _ _ (by decide)]; decide

/-- The kernel's field names are injective in the field number. -/
theorem fieldName_inj {a b : Nat} {v : String} : fieldName a v = fieldName b v ↔ a = b := by
  constructor
  · intro h
    rw [fieldName_def, fieldName_def, String.append_left_inj, String.append_left_inj,
      String.append_right_inj, Nat.toString_eq_repr, Nat.toString_eq_repr] at h
    exact Nat.repr_injective h
  · rintro rfl; rfl

/-- A pair-delta name is never a field name. -/
theorem pairName_ne_fieldName (a b N : Nat) (v : String) : pairName a b ≠ fieldName N v := by
  intro h
  have ep : pairName a b = "resource/" ++ ("pair/" ++ toString a ++ "/" ++ toString b ++ "/delta") := by
    rw [pairName_def, show "resource/pair/" = "resource/" ++ "pair/" by decide]
    simp only [String.append_assoc]
  have ef : fieldName N v = "resource/" ++ ("field/" ++ toString N ++ "/" ++ v) := by
    rw [fieldName_def, show "resource/field/" = "resource/" ++ "field/" by decide]
    simp only [String.append_assoc]
  rw [ep, ef, String.append_right_inj] at h
  have hc := congrArg headc h
  simp only [String.append_assoc] at hc
  rw [headc_append _ _ (by decide), headc_append _ _ (by decide)] at hc
  exact absurd hc (by decide)

end Names

section Lookup
open Minidregg.Kernel.DeclaredResourceProjection (get)

theorem state_get (l : List (String × Int)) (k : String) :
    (State.mk l).get k = (l.find? (fun q => q.1 == k)).map (·.2) := rfl

theorem find_none {l : List (String × Int)} {k : String} (h : ∀ q ∈ l, q.1 ≠ k) :
    l.find? (fun q => q.1 == k) = none := by
  rw [List.find?_eq_none]; intro q hq; simpa using h q hq

/-- `scalarSlots`, split into its four runs (definitionally). -/
theorem scalarSlots_split (pre post : Values) :
    scalarSlots pre post =
      pre.map (fun p => (fieldName p.1 "before", p.2)) ++
      post.map (fun p => (fieldName p.1 "after", p.2)) ++
      post.filterMap (fun p => (get pre p.1).map fun old => (fieldName p.1 "delta", p.2 - old)) ++
      post.flatMap (fun a => post.filterMap fun b => do
        let oldA ← get pre a.1
        let oldB ← get pre b.1
        return (pairName a.1 b.1, a.2 + b.2 - oldA - oldB)) := rfl

theorem mem_pairs {pre post : Values} {q : String × Int}
    (h : q ∈ post.flatMap (fun a => post.filterMap fun b => do
        let oldA ← get pre a.1
        let oldB ← get pre b.1
        return (pairName a.1 b.1, a.2 + b.2 - oldA - oldB))) :
    ∃ a b, q.1 = pairName a b := by
  simp only [List.mem_flatMap, List.mem_filterMap] at h
  obtain ⟨a, -, b, -, hb⟩ := h
  cases ha : get pre a.1 <;> cases hb' : get pre b.1 <;> simp [ha, hb'] at hb
  exact ⟨a.1, b.1, by rw [← hb]⟩

theorem mem_deltas {pre post : Values} {q : String × Int}
    (h : q ∈ post.filterMap (fun p => (get pre p.1).map fun old => (fieldName p.1 "delta", p.2 - old))) :
    ∃ m, q.1 = fieldName m "delta" := by
  simp only [List.mem_filterMap, Option.map_eq_some_iff] at h
  obtain ⟨p, -, old, -, rfl⟩ := h
  exact ⟨p.1, rfl⟩

theorem mem_joint {j : List (Nat × Nat × String × Int)} {q : String × Int} (h : q ∈ jointSlots j) :
    ∃ i n v, q.1 = jointName i n v := by
  simp only [jointSlots, List.mem_map] at h
  obtain ⟨r, -, rfl⟩ := h
  exact ⟨_, _, _, rfl⟩

theorem mem_clock {c : Option Int} {q : String × Int} (h : q ∈ clockSlots c) : q.1 = "clock/now" := by
  cases c <;> simp [clockSlots] at h
  rw [h]

theorem mem_request {v s : Int} {q : String × Int} (h : q ∈ request v s) :
    q.1 = "request/verb" ∨ q.1 = "request/subject" := by
  simp [request] at h
  rcases h with rfl | rfl <;> simp

/-- A field name is never one of the request, clock, pair or joint names. -/
theorem request_ne_field {v s : Int} {q : String × Int} (h : q ∈ request v s) (N : Nat) (w : String)
    (hw : lastc w = some 'r' ∨ lastc w = some 'e' ∨ lastc w = some 'a') (hne : w.toList ≠ []) :
    q.1 ≠ fieldName N w := by
  apply ne_of_lastc
  rw [lastc_fieldName _ _ hne]
  rcases mem_request h with e | e <;> rw [e] <;> rcases hw with hw | hw | hw <;> rw [hw] <;> decide

theorem clock_ne_field {c : Option Int} {q : String × Int} (h : q ∈ clockSlots c) (N : Nat) (w : String)
    (hw : lastc w = some 'r' ∨ lastc w = some 'e' ∨ lastc w = some 'a') (hne : w.toList ≠ []) :
    q.1 ≠ fieldName N w := by
  apply ne_of_lastc
  rw [lastc_fieldName _ _ hne, mem_clock h]
  rcases hw with hw | hw | hw <;> rw [hw] <;> decide

theorem joint_ne_field {j : List (Nat × Nat × String × Int)} {q : String × Int} (h : q ∈ jointSlots j)
    (N : Nat) (w : String) : q.1 ≠ fieldName N w := by
  obtain ⟨i, n, v, e⟩ := mem_joint h
  apply ne_of_headc
  rw [e, headc_jointName, headc_fieldName]
  decide

/-- **The new-view `after` slot is the post-state's field.** -/
theorem get_after (t : Turn) (pre post : Values) (N : Nat) :
    (view t pre post).get (fieldName N "after") = get post N := by
  have hw : lastc "after" = some 'r' ∨ lastc "after" = some 'e' ∨ lastc "after" = some 'a' :=
    .inl (by decide)
  have hreq := find_none (l := request t.verb t.subject) (k := fieldName N "after") (fun q hq => request_ne_field hq N _ hw (by decide))
  have hbef := find_none (l := pre.map (fun p => (fieldName p.1 "before", p.2))) (k := fieldName N "after")
    (fun q hq => by
      simp only [List.mem_map] at hq
      obtain ⟨p, -, rfl⟩ := hq
      exact ne_of_lastc (by rw [lastc_before, lastc_after]; decide))
  have haft : (post.map (fun p => (fieldName p.1 "after", p.2))).find? (fun q => q.1 == fieldName N "after") =
      (post.find? (fun q => q.1 == N)).map (fun p => (fieldName p.1 "after", p.2)) := by
    have hp : ((fun q : String × Int => q.1 == fieldName N "after") ∘
        fun p : Nat × Int => (fieldName p.1 "after", p.2)) = (fun q => q.1 == N) := by
      funext p; simp [fieldName_inj]
    rw [List.find?_map, hp]
  have hdel := find_none (k := fieldName N "after")
    (l := post.filterMap (fun p => (get pre p.1).map fun old => (fieldName p.1 "delta", p.2 - old)))
    (fun q hq => by
      obtain ⟨m, e⟩ := mem_deltas hq
      rw [e]; exact ne_of_lastc (by rw [lastc_delta, lastc_after]; decide))
  have hpair := find_none (k := fieldName N "after")
    (l := post.flatMap (fun a => post.filterMap fun b => do
        let oldA ← get pre a.1
        let oldB ← get pre b.1
        return (pairName a.1 b.1, a.2 + b.2 - oldA - oldB)))
    (fun q hq => by
      obtain ⟨a, b, e⟩ := mem_pairs hq
      rw [e]; exact pairName_ne_fieldName a b N _)
  have hclock := find_none (k := fieldName N "after") (l := clockSlots t.now)
    (fun q hq => clock_ne_field hq N _ hw (by decide))
  have hjoint := find_none (k := fieldName N "after") (l := jointSlots t.joint)
    (fun q hq => joint_ne_field hq N _)
  simp only [view, state_get, scalarSlots_split, List.find?_append, hreq, hbef, haft, hdel, hpair,
    hclock, hjoint, Option.none_or, Option.or_none, Option.map_map]
  rfl

/-- **The `before` slot is the pre-state's field** (in either view). -/
theorem get_before (t : Turn) (pre post : Values) (N : Nat) :
    (view t pre post).get (fieldName N "before") = get pre N := by
  have hw : lastc "before" = some 'r' ∨ lastc "before" = some 'e' ∨ lastc "before" = some 'a' :=
    .inr (.inl (by decide))
  have hreq := find_none (l := request t.verb t.subject) (k := fieldName N "before") (fun q hq => request_ne_field hq N _ hw (by decide))
  have hbef : (pre.map (fun p => (fieldName p.1 "before", p.2))).find? (fun q => q.1 == fieldName N "before") =
      (pre.find? (fun q => q.1 == N)).map (fun p => (fieldName p.1 "before", p.2)) := by
    have hp : ((fun q : String × Int => q.1 == fieldName N "before") ∘
        fun p : Nat × Int => (fieldName p.1 "before", p.2)) = (fun q => q.1 == N) := by
      funext p; simp [fieldName_inj]
    rw [List.find?_map, hp]
  have haft := find_none (l := post.map (fun p => (fieldName p.1 "after", p.2))) (k := fieldName N "before")
    (fun q hq => by
      simp only [List.mem_map] at hq
      obtain ⟨p, -, rfl⟩ := hq
      exact ne_of_lastc (by rw [lastc_before, lastc_after]; decide))
  have hdel := find_none (k := fieldName N "before")
    (l := post.filterMap (fun p => (get pre p.1).map fun old => (fieldName p.1 "delta", p.2 - old)))
    (fun q hq => by
      obtain ⟨m, e⟩ := mem_deltas hq
      rw [e]; exact ne_of_lastc (by rw [lastc_delta, lastc_before]; decide))
  have hpair := find_none (k := fieldName N "before")
    (l := post.flatMap (fun a => post.filterMap fun b => do
        let oldA ← get pre a.1
        let oldB ← get pre b.1
        return (pairName a.1 b.1, a.2 + b.2 - oldA - oldB)))
    (fun q hq => by
      obtain ⟨a, b, e⟩ := mem_pairs hq
      rw [e]; exact pairName_ne_fieldName a b N _)
  have hclock := find_none (k := fieldName N "before") (l := clockSlots t.now)
    (fun q hq => clock_ne_field hq N _ hw (by decide))
  have hjoint := find_none (k := fieldName N "before") (l := jointSlots t.joint)
    (fun q hq => joint_ne_field hq N _)
  simp only [view, state_get, scalarSlots_split, List.find?_append, hreq, hbef, haft, hdel, hpair,
    hclock, hjoint, Option.none_or, Option.or_none, Option.map_map]
  rfl

/-- **The `delta` slot is post − pre** when the pre-state has the field. -/
theorem get_delta (t : Turn) (pre post : Values) (N : Nat) (o : Int) (hpre : get pre N = some o) :
    (view t pre post).get (fieldName N "delta") = (get post N).map (· - o) := by
  have hw : lastc "delta" = some 'r' ∨ lastc "delta" = some 'e' ∨ lastc "delta" = some 'a' :=
    .inr (.inr (by decide))
  have hreq := find_none (l := request t.verb t.subject) (k := fieldName N "delta") (fun q hq => request_ne_field hq N _ hw (by decide))
  have hbef := find_none (l := pre.map (fun p => (fieldName p.1 "before", p.2))) (k := fieldName N "delta")
    (fun q hq => by
      simp only [List.mem_map] at hq
      obtain ⟨p, -, rfl⟩ := hq
      exact ne_of_lastc (by rw [lastc_before, lastc_delta]; decide))
  have haft := find_none (l := post.map (fun p => (fieldName p.1 "after", p.2))) (k := fieldName N "delta")
    (fun q hq => by
      simp only [List.mem_map] at hq
      obtain ⟨p, -, rfl⟩ := hq
      exact ne_of_lastc (by rw [lastc_delta, lastc_after]; decide))
  have hdel : (post.filterMap (fun p => (get pre p.1).map fun old => (fieldName p.1 "delta", p.2 - old))).find?
      (fun q => q.1 == fieldName N "delta") =
      (post.find? (fun q => q.1 == N)).map (fun p => (fieldName p.1 "delta", p.2 - o)) := by
    rw [List.find?_filterMap]
    have hp : (fun a : Nat × Int => ((get pre a.1).map fun old => (fieldName a.1 "delta", a.2 - old)).any
        (fun q => q.1 == fieldName N "delta")) = (fun q => q.1 == N) := by
      funext a
      by_cases ha : a.1 = N
      · simp [ha, hpre]
      · cases get pre a.1 <;> simp [fieldName_inj, ha]
    rw [hp]
    cases hf : post.find? (fun q => q.1 == N) with
    | none => rfl
    | some a =>
      have : a.1 = N := by simpa using List.find?_some hf
      simp [this, hpre]
  have hpair := find_none (k := fieldName N "delta")
    (l := post.flatMap (fun a => post.filterMap fun b => do
        let oldA ← get pre a.1
        let oldB ← get pre b.1
        return (pairName a.1 b.1, a.2 + b.2 - oldA - oldB)))
    (fun q hq => by
      obtain ⟨a, b, e⟩ := mem_pairs hq
      rw [e]; exact pairName_ne_fieldName a b N _)
  have hclock := find_none (k := fieldName N "delta") (l := clockSlots t.now)
    (fun q hq => clock_ne_field hq N _ hw (by decide))
  have hjoint := find_none (k := fieldName N "delta") (l := jointSlots t.joint)
    (fun q hq => joint_ne_field hq N _)
  simp only [view, state_get, scalarSlots_split, List.find?_append, hreq, hbef, haft, hdel, hpair,
    hclock, hjoint, Option.none_or, Option.or_none, Option.map_map]
  simp only [Minidregg.Kernel.DeclaredResourceProjection.get, Option.map_map]
  rfl

theorem get_verb (t : Turn) (pre post : Values) : (view t pre post).get "request/verb" = some t.verb := by
  simp [view, state_get, request]

theorem get_subject (t : Turn) (pre post : Values) :
    (view t pre post).get "request/subject" = some t.subject := by
  simp [view, state_get, request]

theorem get_clock (t : Turn) (pre post : Values) : (view t pre post).get "clock/now" = t.now := by
  have hreq : (request t.verb t.subject).find? (fun q => q.1 == "clock/now") = none := by
    simp [request]
  have hscalar := find_none (k := "clock/now") (l := scalarSlots pre post) (fun q hq => by
    rw [scalarSlots_split] at hq
    simp only [List.mem_append] at hq
    rcases hq with ((hq | hq) | hq) | hq
    · simp only [List.mem_map] at hq
      obtain ⟨p, -, rfl⟩ := hq
      exact ne_of_lastc (by rw [lastc_before]; decide)
    · simp only [List.mem_map] at hq
      obtain ⟨p, -, rfl⟩ := hq
      exact ne_of_lastc (by rw [lastc_after]; decide)
    · obtain ⟨m, e⟩ := mem_deltas hq
      rw [e]; exact ne_of_lastc (by rw [lastc_delta]; decide)
    · obtain ⟨a, b, e⟩ := mem_pairs hq
      rw [e]; exact ne_of_lastc (by rw [lastc_pairName]; decide))
  have hjoint := find_none (k := "clock/now") (l := jointSlots t.joint) (fun q hq => by
    obtain ⟨i, n, v, e⟩ := mem_joint hq
    rw [e]; exact ne_of_headc (by rw [headc_jointName]; decide))
  cases hc : t.now with
  | none => simp [view, state_get, List.find?_append, hreq, hscalar, hjoint, hc, clockSlots]
  | some x => simp [view, state_get, List.find?_append, hreq, hscalar, hc, clockSlots]

end Lookup

/-! ## Axiom pins -/

/-- info: 'Minidregg.Kernel.LawView.fieldName_inj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms fieldName_inj
/-- info: 'Minidregg.Kernel.LawView.pairName_ne_fieldName' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms pairName_ne_fieldName
/-- info: 'Minidregg.Kernel.LawView.get_after' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms get_after
/-- info: 'Minidregg.Kernel.LawView.get_before' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms get_before
/-- info: 'Minidregg.Kernel.LawView.get_delta' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms get_delta
/-- info: 'Minidregg.Kernel.LawView.get_verb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms get_verb
/-- info: 'Minidregg.Kernel.LawView.get_subject' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms get_subject
/-- info: 'Minidregg.Kernel.LawView.get_clock' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms get_clock

end Minidregg.Kernel.LawView
