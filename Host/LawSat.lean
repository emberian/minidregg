/-
# Law satisfiability, served (C-SAT-2, Host op 150 `law-sat`)

C-SAT-1 (`Pred.Satisfiable`, `Pred.SatisfiableTotal`) decides whether a law admits any step:
`Pred.difference?` translates a law in the arithmetic fragment to difference-constraint
systems, and `DiffProblem.decide` answers a witness `eval` accepted or a certificate
`checkAll` accepted. This module is what a friend's shell asks about a law it holds the bytes
of; it reads no Store (see `Host.LawSatWire.lawSat_reads_no_store`).

A query is a law and an extra clause the asker adds, judged together as
`Pred.all [law, extra]`:

* `law check` asks with `extra = open`: does the law admit any step at all?
* `law` install also asks with `extra = verb == write`: can any write pass?
* `can --any` asks *from here*: `extra` pins the asker's own request slots and the
  cell's current field values, and the query is `realize`d first.

## Realizing the before-state (`realize`)

A step the kernel judges is not an arbitrary pair of states. For a declared scalar resource
the old state is the projection of the pre-store against itself (`DeclaredResourceController.step`:
`before = after = pre`, every delta `0`), and the request, clock, command and run slots are
the same in both. So `old[field N after] = new[field N before]`, `old[field N delta] = 0`
exactly when `new[field N before]` is present, and `old[s] = new[s]` for the common slots
(`scalarView`). `realize` replaces the only atoms that read `old` (`monotone`, `writeOnce`) by
atoms over `new` with the same truth value on every step of that shape
(`realize_eval`), so a witness of the realized query is a new state from which the old state
is determined, and the law admits that pair (`lawSat_witness_admits_from_here`).
A law that reads the old value of a slot the view does not model (a content or stream slot,
`resource/bytes`, a joint slot) is answered `unrealizable`, naming the slot.

What is proved here is relative to the view: `Shaped scalarView o n` is the hypothesis. That
the kernel's projection is shaped this way is read from `DeclaredResourceProjection` and
checked by the journey (`jlawsat.sh` submits each witness as a write and the kernel admits
it); it is not a theorem of this module.
-/
import Pred.SatisfiableTotal
import Compiler.RefusalReason
import Theory.AssertAxioms
import Lean.Data.Json

namespace Minidregg.Host.LawSat

open Minidregg.Pred
open Minidregg.Pred.Sat

set_option autoImplicit false

/-! ## §1. Where an old value comes from -/

/-- Where the old state's value of a slot is read from, on a step of a known shape:
`slot t` is `new[t]`; `zeroIf ts` is `0` when every `new[t]` is present, and absent
otherwise. -/
inductive OldSrc where
  | slot (t : Slot)
  | zeroIf (ts : List Slot)
deriving Repr, DecidableEq

def OldSrc.resolve (n : State) : OldSrc → Option Int
  | .slot t => n.get t
  | .zeroIf ts => if ts.all (fun t => (n.get t).isSome) then some 0 else none

/-- A view: for each slot the shape models, where its old value comes from. -/
abbrev View := Slot → Option OldSrc

/-- `o` is the old state the view determines from `n`, on every slot the view models. -/
def Shaped (view : View) (o n : State) : Prop :=
  ∀ s src, view s = some src → o.get s = src.resolve n

/-- The declared scalar resource's step shape (`DeclaredResourceProjection.scalarSlots` on
`pre, pre` for the old state and `pre, post` for the new one; the common slots are shared). -/
def scalarView : View := fun s =>
  match s.splitOn "/" with
  | ["resource", "field", k, "after"] => some (.slot s!"resource/field/{k}/before")
  | ["resource", "field", _, "before"] => some (.slot s)
  | ["resource", "field", k, "delta"] => some (.zeroIf [s!"resource/field/{k}/before"])
  | ["resource", "pair", a, b, "delta"] =>
      some (.zeroIf [s!"resource/field/{a}/before", s!"resource/field/{b}/before"])
  | "request" :: _ => some (.slot s)
  | "target" :: _ => some (.slot s)
  | "clock" :: _ => some (.slot s)
  | "command" :: _ => some (.slot s)
  | "run" :: _ => some (.slot s)
  | _ => none

/-! ## §2. Realizing a law over the new state alone -/

/-- `new[t]` is present (`leSlots t t` fails closed exactly on an absent slot). -/
def present (t : Slot) : Pred := .leSlots t t

def realizeMono (s : Slot) : OldSrc → Pred
  | .slot t => .leSlots t s
  | .zeroIf ts => Pred.all (ts.map present ++ [present s, .not (.le s (-1))])

def realizeOnce (s : Slot) : OldSrc → Pred
  | .slot t => Pred.any [.not (present t), .eq t 0, .eqSlots s t]
  | .zeroIf _ => Pred.all []

mutual
/-- Replace every atom that reads `old` by its reading through the view; `none` when the law
reads the old value of a slot the view does not model. -/
def realize (view : View) : Pred → Option Pred
  | .monotone s => (view s).map (realizeMono s)
  | .writeOnce s => (view s).map (realizeOnce s)
  | .not q => (realize view q).map .not
  | .allL ps => (realizeList view ps).map .allL
  | .anyL ps => (realizeList view ps).map .anyL
  | .eq s v => some (.eq s v)
  | .le s v => some (.le s v)
  | .memberOf s xs => some (.memberOf s xs)
  | .eqSlots a b => some (.eqSlots a b)
  | .leSlots a b => some (.leSlots a b)
  | .leSlotsOff a b k => some (.leSlotsOff a b k)
  | .witnessed vk => some (.witnessed vk)
  | .hashEq v b c => some (.hashEq v b c)
  | .ran p => some (.ran p)
def realizeList (view : View) : PredList → Option PredList
  | .nil => some .nil
  | .cons q rest =>
      match realize view q, realizeList view rest with
      | some q', some r => some (.cons q' r)
      | _, _ => none
end

mutual
/-- The first old-reading slot the view does not model (for the refusal's text). -/
def unmodelled (view : View) : Pred → Option Slot
  | .monotone s => if (view s).isSome then none else some s
  | .writeOnce s => if (view s).isSome then none else some s
  | .not q => unmodelled view q
  | .allL ps => unmodelledList view ps
  | .anyL ps => unmodelledList view ps
  | _ => none
def unmodelledList (view : View) : PredList → Option Slot
  | .nil => none
  | .cons q rest => (unmodelled view q).or (unmodelledList view rest)
end

theorem eval_present (t : Slot) (o n : State) :
    evalWith failClosed (present t) o n = (n.get t).isSome := by
  cases h : n.get t <;> simp [present, evalWith, h]

theorem eval_all (l : List Pred) (o n : State) :
    evalWith failClosed (Pred.all l) o n = l.all (fun q => evalWith failClosed q o n) :=
  evalWithAll_ofList failClosed l o n

theorem eval_any (l : List Pred) (o n : State) :
    evalWith failClosed (Pred.any l) o n = l.any (fun q => evalWith failClosed q o n) :=
  evalWithAny_ofList failClosed l o n

theorem realizeMono_eval (s : Slot) (src : OldSrc) (o o' n : State)
    (ho : o.get s = src.resolve n) :
    evalWith failClosed (realizeMono s src) o' n = evalWith failClosed (.monotone s) o n := by
  cases src with
  | slot t =>
      simp only [realizeMono, evalWith, ho, OldSrc.resolve]
  | zeroIf ts =>
      rw [realizeMono, eval_all, List.all_append, List.all_map]
      simp only [Function.comp_def, eval_present, List.all_cons, List.all_nil, Bool.and_true]
      have hm : evalWith failClosed (.monotone s) o n =
          (match o.get s, n.get s with
            | some a, some b => decide (a ≤ b)
            | _, _ => false) := rfl
      rw [hm, ho]
      simp only [OldSrc.resolve]
      by_cases hall : (ts.all fun t => (n.get t).isSome) = true
      · rw [if_pos hall, hall]
        cases h : n.get s with
        | none => simp
        | some x =>
            simp only [Option.isSome_some, Bool.true_and]
            have hl : evalWith failClosed (Pred.le s (-1)).not o' n = !(decide (x ≤ -1)) := by
              simp [evalWith, h]
            rw [hl]
            by_cases hx : 0 ≤ x
            · have : ¬ x ≤ -1 := by omega
              simp [hx, this]
            · have : x ≤ -1 := by omega
              simp [hx, this]
      · rw [if_neg hall]
        simp only [Bool.not_eq_true] at hall
        simp [hall]

theorem realizeOnce_eval (s : Slot) (src : OldSrc) (o o' n : State)
    (ho : o.get s = src.resolve n) :
    evalWith failClosed (realizeOnce s src) o' n = evalWith failClosed (.writeOnce s) o n := by
  have hw : evalWith failClosed (.writeOnce s) o n =
      (match o.get s with
        | none => true
        | some v => v == 0 || decide (n.get s = some v)) := rfl
  rw [hw, ho]
  cases src with
  | slot t =>
      rw [realizeOnce, eval_any]
      simp only [List.any_cons, List.any_nil, Bool.or_false, OldSrc.resolve]
      have hn : evalWith failClosed (.not (present t)) o' n = !((n.get t).isSome) := by
        show (!(evalWith failClosed (present t) o' n)) = _
        rw [eval_present]
      have he : evalWith failClosed (.eq t 0) o' n = decide (n.get t = some 0) := rfl
      have hs : evalWith failClosed (.eqSlots s t) o' n =
          (match n.get s, n.get t with
            | some x, some y => decide (x = y)
            | _, _ => false) := rfl
      rw [hn, he, hs]
      cases ht : n.get t with
      | none => simp
      | some v =>
          cases hs' : n.get s with
          | none =>
              by_cases hv : v = 0
              · subst hv; simp
              · simp [hv]
          | some x =>
              by_cases hv : v = 0
              · subst hv; simp
              · by_cases hx : x = v
                · subst hx; simp
                · simp [hv, hx]
  | zeroIf ts =>
      rw [realizeOnce, eval_all]
      simp only [List.all_nil, OldSrc.resolve]
      cases hall : (ts.all fun t => (n.get t).isSome) <;> simp

mutual
/-- **`realize_eval`** — on a step whose old state is the one the view determines, the
realized law has the original law's verdict, whatever old state it is handed: it reads
only `new`. -/
theorem realize_eval (view : View) (o o' n : State) (ho : Shaped view o n) :
    ∀ (p q : Pred), realize view p = some q →
      evalWith failClosed q o' n = evalWith failClosed p o n
  | .monotone s, q, h => by
      simp only [realize, Option.map_eq_some_iff] at h
      obtain ⟨src, hs, rfl⟩ := h
      exact realizeMono_eval s src o o' n (ho s src hs)
  | .writeOnce s, q, h => by
      simp only [realize, Option.map_eq_some_iff] at h
      obtain ⟨src, hs, rfl⟩ := h
      exact realizeOnce_eval s src o o' n (ho s src hs)
  | .not p, q, h => by
      simp only [realize, Option.map_eq_some_iff] at h
      obtain ⟨p', hp, rfl⟩ := h
      simp only [evalWith, realize_eval view o o' n ho p p' hp]
  | .allL ps, q, h => by
      simp only [realize, Option.map_eq_some_iff] at h
      obtain ⟨qs, hqs, rfl⟩ := h
      simp only [evalWith, (realizeList_eval view o o' n ho ps qs hqs).1]
  | .anyL ps, q, h => by
      simp only [realize, Option.map_eq_some_iff] at h
      obtain ⟨qs, hqs, rfl⟩ := h
      simp only [evalWith, (realizeList_eval view o o' n ho ps qs hqs).2]
  | .eq _ _, q, h => by simp only [realize, Option.some.injEq] at h; subst h; rfl
  | .le _ _, q, h => by simp only [realize, Option.some.injEq] at h; subst h; rfl
  | .memberOf _ _, q, h => by simp only [realize, Option.some.injEq] at h; subst h; rfl
  | .eqSlots _ _, q, h => by simp only [realize, Option.some.injEq] at h; subst h; rfl
  | .leSlots _ _, q, h => by simp only [realize, Option.some.injEq] at h; subst h; rfl
  | .leSlotsOff _ _ _, q, h => by simp only [realize, Option.some.injEq] at h; subst h; rfl
  | .witnessed _, q, h => by simp only [realize, Option.some.injEq] at h; subst h; rfl
  | .hashEq _ _ _, q, h => by simp only [realize, Option.some.injEq] at h; subst h; rfl
  | .ran _, q, h => by simp only [realize, Option.some.injEq] at h; subst h; rfl
theorem realizeList_eval (view : View) (o o' n : State) (ho : Shaped view o n) :
    ∀ (ps qs : PredList), realizeList view ps = some qs →
      evalWithAll failClosed qs o' n = evalWithAll failClosed ps o n ∧
      evalWithAny failClosed qs o' n = evalWithAny failClosed ps o n
  | .nil, qs, h => by
      simp only [realizeList, Option.some.injEq] at h
      subst h; exact ⟨rfl, rfl⟩
  | .cons p rest, qs, h => by
      simp only [realizeList] at h
      split at h
      · rename_i p' r hp hr
        simp only [Option.some.injEq] at h
        subst h
        have e1 := realize_eval view o o' n ho p p' hp
        have e2 := realizeList_eval view o o' n ho rest r hr
        refine ⟨?_, ?_⟩ <;> simp only [evalWithAll, evalWithAny, e1, e2.1, e2.2]
      · cases h
end

/-! ## §3. Outside the fragment, named -/

mutual
/-- The path to the first leaf outside the arithmetic fragment (`witnessed`, `hashEq`,
`ran`), in `Pred.subterm`'s path convention. -/
def outsidePath : Pred → Option (List Nat)
  | .witnessed _ => some []
  | .hashEq _ _ _ => some []
  | .ran _ => some []
  | .not q => (outsidePath q).map (0 :: ·)
  | .allL ps => outsideList 0 ps
  | .anyL ps => outsideList 0 ps
  | _ => none
def outsideList (i : Nat) : PredList → Option (List Nat)
  | .nil => none
  | .cons q rest =>
      match outsidePath q with
      | some path => some (i :: path)
      | none => outsideList (i + 1) rest
end

mutual
/-- A law with a leaf outside the fragment has no translation, at either polarity. -/
theorem outside_dnf_none (cap : Nat) :
    ∀ (p : Pred), (outsidePath p).isSome = true → ∀ b, dnf cap b p = none
  | .witnessed _, _, b => by simp [dnf]
  | .hashEq _ _ _, _, b => by simp [dnf]
  | .ran _, _, b => by simp [dnf]
  | .not q, h, b => by
      simp only [outsidePath, Option.isSome_map] at h
      simp only [dnf]
      exact outside_dnf_none cap q h (!b)
  | .allL ps, h, b => by
      simp only [outsidePath] at h
      have := outsideList_dnf_none cap ps 0 h b
      cases b <;> simp [dnf, this.1, this.2]
  | .anyL ps, h, b => by
      simp only [outsidePath] at h
      have := outsideList_dnf_none cap ps 0 h b
      cases b <;> simp [dnf, this.1, this.2]
  | .eq _ _, h, _ => by simp [outsidePath] at h
  | .le _ _, h, _ => by simp [outsidePath] at h
  | .memberOf _ _, h, _ => by simp [outsidePath] at h
  | .writeOnce _, h, _ => by simp [outsidePath] at h
  | .monotone _, h, _ => by simp [outsidePath] at h
  | .eqSlots _ _, h, _ => by simp [outsidePath] at h
  | .leSlots _ _, h, _ => by simp [outsidePath] at h
  | .leSlotsOff _ _ _, h, _ => by simp [outsidePath] at h
theorem outsideList_dnf_none (cap : Nat) :
    ∀ (ps : PredList) (i : Nat), (outsideList i ps).isSome = true → ∀ b,
      dnfAnd cap b ps = none ∧ dnfOr cap b ps = none
  | .nil, _, h, _ => by simp [outsideList] at h
  | .cons q rest, i, h, b => by
      simp only [outsideList] at h
      cases hq : outsidePath q with
      | some path =>
          have hn := outside_dnf_none cap q (by simp [hq]) b
          simp [dnfAnd, dnfOr, hn]
      | none =>
          simp only [hq] at h
          have hr := outsideList_dnf_none cap rest (i + 1) h b
          constructor
          · simp only [dnfAnd, hr.1]; split <;> simp_all
          · simp only [dnfOr, hr.2]; split <;> simp_all
end

/-- **`outside_has_no_translation`** — the `outside` answer is not a label: a law with such a
leaf has no `difference?` at all. -/
theorem outside_has_no_translation (p : Pred) (h : (outsidePath p).isSome = true) :
    p.difference? = none := by
  simp [Pred.difference?, outside_dnf_none dnfCap p h true]

/-! ## §4. The query and its answer -/

/-- A law, an extra clause the asker adds, and whether to judge it from the declared scalar
step shape (`realize scalarView`). -/
structure Query where
  law : Pred
  extra : Pred
  fromHere : Bool
deriving Repr, DecidableEq

/-- The two judged together. Paths below start `0` (the law) or `1` (the extra clause). -/
def Query.pred (q : Query) : Pred := Pred.all [q.law, q.extra]

/-- The predicate handed to `difference?`. -/
def Query.target (q : Query) : Option Pred :=
  if q.fromHere then realize scalarView q.pred else some q.pred

inductive Answer where
  /-- A leaf outside the fragment, at this path of `Query.pred`. -/
  | outside (path : List Nat)
  /-- The law reads the old value of a slot the step shape does not model. -/
  | unrealizable (slot : Slot)
  /-- `difference?` translated the target to `d`; `v` is `d.decide`. -/
  | decided (d : DiffProblem) (v : Verdict)
  /-- In the fragment, but the translation passed `dnfCap` systems. -/
  | pastCap
deriving Repr, DecidableEq

/-- **`answer`** — the one function op 150 serves. -/
def answer (q : Query) : Answer :=
  match outsidePath q.pred with
  | some path => .outside path
  | none =>
      match q.target with
      | none => .unrealizable ((unmodelled scalarView q.pred).getD "")
      | some t =>
          match t.difference? with
          | some d => .decided d d.decide
          | none => .pastCap

/-! ## §5. The answer is `Sat.decide`'s -/

/-- **`lawSat_is_decide`** — on a query in the fragment the Host's answer is `decide` on the
translation of exactly the predicate it was asked about. -/
theorem lawSat_is_decide (q : Query) (t : Pred) (d : DiffProblem)
    (hin : outsidePath q.pred = none) (ht : q.target = some t) (hd : t.difference? = some d) :
    answer q = .decided d d.decide := by
  simp [answer, hin, ht, hd]

/-- Every `decided` answer is `decide` on the target's translation; the Host has no other
way to produce one. -/
theorem lawSat_decided_is_decide (q : Query) (d : DiffProblem) (v : Verdict)
    (h : answer q = .decided d v) :
    ∃ t, q.target = some t ∧ t.difference? = some d ∧ v = d.decide := by
  unfold answer at h
  split at h
  · cases h
  · split at h
    · cases h
    · rename_i t ht
      split at h
      · rename_i d' hd
        simp only [Answer.decided.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨t, ht, hd, rfl⟩
      · cases h

/-- **`lawSat_never_unknown`** — a decided answer is a witness or a certificate. -/
theorem lawSat_never_unknown (q : Query) (d : DiffProblem) (v : Verdict)
    (h : answer q = .decided d v) : v ≠ .unknown := by
  obtain ⟨t, _, hd, rfl⟩ := lawSat_decided_is_decide q d v h
  exact decide_never_unknown hd

/-- **`lawSat_outside_is_untranslatable`** — `outside` is answered only for a query
`difference?` cannot translate. -/
theorem lawSat_outside_is_untranslatable (q : Query) (path : List Nat)
    (h : answer q = .outside path) : q.pred.difference? = none := by
  unfold answer at h
  split at h
  · rename_i p hp
    exact outside_has_no_translation _ (by simp [hp])
  · split at h
    · cases h
    · split at h <;> cases h

theorem eval_pred (q : Query) (o n : State) :
    eval q.pred o n = (eval q.law o n && eval q.extra o n) := by
  show evalWith failClosed (Pred.all [q.law, q.extra]) o n = _
  rw [eval_all]
  simp [eval]

/-- **`lawSat_witness_admits`** — a witness to a plain query is a step the law admits (and
the extra clause too). -/
theorem lawSat_witness_admits (q : Query) (d : DiffProblem) (o n : State)
    (hr : q.fromHere = false) (h : answer q = .decided d (.witness o n)) :
    eval q.law o n = true ∧ eval q.extra o n = true := by
  obtain ⟨t, ht, hd, hv⟩ := lawSat_decided_is_decide q d _ h
  simp only [Query.target, hr, Bool.false_eq_true, if_false, Option.some.injEq] at ht
  subst ht
  have := witness_sound hd hv.symm
  rw [eval_pred] at this
  simpa using this

/-- **`lawSat_witness_admits_from_here`** — a witness to a realized query is a new state;
on the old state the declared scalar step shape determines from it, the law admits the
step. -/
theorem lawSat_witness_admits_from_here (q : Query) (d : DiffProblem) (o' n : State)
    (hr : q.fromHere = true) (h : answer q = .decided d (.witness o' n)) :
    ∀ o, Shaped scalarView o n → eval q.law o n = true ∧ eval q.extra o n = true := by
  intro o ho
  obtain ⟨t, ht, hd, hv⟩ := lawSat_decided_is_decide q d _ h
  simp only [Query.target, hr, if_true] at ht
  have hw := witness_sound hd hv.symm
  have he := realize_eval scalarView o o' n ho q.pred t ht
  simp only [eval] at hw
  rw [he] at hw
  have hp : eval q.pred o n = true := hw
  rw [eval_pred] at hp
  simpa using hp

/-- **`lawSat_unsat_admits_nothing`** — a certificate to a plain query: no step at all passes
both the law and the extra clause. -/
theorem lawSat_unsat_admits_nothing (q : Query) (d : DiffProblem) (c : Certificate)
    (hr : q.fromHere = false) (h : answer q = .decided d (.unsat c)) :
    ∀ o n, (eval q.law o n && eval q.extra o n) = false := by
  intro o n
  obtain ⟨t, ht, hd, hv⟩ := lawSat_decided_is_decide q d _ h
  simp only [Query.target, hr, Bool.false_eq_true, if_false, Option.some.injEq] at ht
  subst ht
  rw [← eval_pred]
  exact certificate_unsat hd hv.symm o n

/-- **`lawSat_unsat_from_here`** — a certificate to a realized query: no step of the declared
scalar shape passes both. -/
theorem lawSat_unsat_from_here (q : Query) (d : DiffProblem) (c : Certificate)
    (hr : q.fromHere = true) (h : answer q = .decided d (.unsat c)) :
    ∀ o n, Shaped scalarView o n → (eval q.law o n && eval q.extra o n) = false := by
  intro o n ho
  obtain ⟨t, ht, hd, hv⟩ := lawSat_decided_is_decide q d _ h
  simp only [Query.target, hr, if_true] at ht
  have hu := certificate_unsat hd hv.symm o n
  have he := realize_eval scalarView o o n ho q.pred t ht
  simp only [eval] at hu
  rw [he] at hu
  rw [← eval_pred]
  exact hu

#assert_axioms realize_eval
#assert_axioms outside_has_no_translation
#assert_axioms lawSat_is_decide
#assert_axioms lawSat_decided_is_decide
#assert_axioms lawSat_never_unknown
#assert_axioms lawSat_outside_is_untranslatable
#assert_axioms lawSat_witness_admits
#assert_axioms lawSat_witness_admits_from_here
#assert_axioms lawSat_unsat_admits_nothing
#assert_axioms lawSat_unsat_from_here

/-! ## §6. Poles -/

namespace Sample

set_option maxRecDepth 20000

def falsifier : Pred :=
  Pred.all [.le "resource/field/1/after" 0, .monotone "resource/field/1/after",
    .eq "resource/field/1/after" 1]

def admitting : Pred :=
  Pred.all [.le "resource/field/1/after" 0, .monotone "resource/field/1/after"]

/-- The EVAL falsifier: unsatisfiable, and the certificate is the two-constraint cycle
`field 1 ≤ 0`, `field 1 ≥ 1`. -/
theorem falsifier_answer :
    (match answer ⟨falsifier, Pred.all [], false⟩ with
      | .decided _ (.unsat c) => some c
      | _ => none) =
      some [.cycle [⟨.new "resource/field/1/after", .zero, 0⟩,
        ⟨.zero, .new "resource/field/1/after", -1⟩]] := by
  decide

/-- `sealed` admits nothing, and its certificate is empty: no system at all. -/
theorem sealed_answer :
    (match answer ⟨Pred.any [], Pred.all [], false⟩ with
      | .decided d (.unsat c) => some (d.systems.length, c)
      | _ => none) = some (0, []) := by
  decide

/-- A `ran` leaf is outside the fragment, named by its path in the law. -/
theorem ran_outside :
    answer ⟨Pred.all [.le "resource/field/1/after" 5, .ran 7], Pred.all [], false⟩ =
      .outside [0, 1] := by
  decide

/-- A one-slot view in the declared shape (`old[field 1 after] = new[field 1 before]`),
spelled with string equality alone so the kernel evaluates it (`scalarView`'s `splitOn`
does not reduce in the kernel; `realize_eval` is what covers it). -/
def fieldOneView : View := fun s =>
  if s = "resource/field/1/after" then some (.slot "resource/field/1/before") else none

def fromHere (law : Pred) (before : Int) : Option Verdict :=
  (realize fieldOneView (Pred.all [law, .eq "request/verb" 2,
      .eq "resource/field/1/before" before, present "resource/field/1/after"])).bind
    fun t => t.difference?.map (·.decide)

/-- From a cell holding field 1 = 0, the falsifier-without-`eq` admits a write: field 1
stays 0 (`monotone` realized as `before ≤ after`). -/
theorem admitting_from_zero :
    (match fromHere admitting 0 with
      | some (.witness _ n) => n.get "resource/field/1/after"
      | _ => none) = some 0 := by
  decide

/-- From a cell holding field 1 = 3, no write: `monotone` forces `after ≥ 3`, `le` forces
`after ≤ 0`. The law is satisfiable in general, unsatisfiable from here. -/
theorem admitting_stuck_from_three :
    (match fromHere admitting 3 with
      | some (.unsat _) => true
      | _ => false) = true := by
  decide

#assert_axioms falsifier_answer
#assert_axioms sealed_answer
#assert_axioms ran_outside
#assert_axioms admitting_from_zero
#assert_axioms admitting_stuck_from_three

end Sample

end Minidregg.Host.LawSat
