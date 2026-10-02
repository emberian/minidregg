/-
# Assurance.ItemLaw — no dupe for a unique item, as a theorem of the item law and the kernel

`deploy/shell/templates/mud/item/law.item.json` (branch `mud-templates`, commit `1ee44ed`), composed
`all [law.management, clause 1, …, clause 7]`, written out literally in §2. Field numbers are
`item/fields.json`: id 0, kind 1, owner 2, where 3, worn 4, charges 5.

The law's whole anti-dupe content is two clauses: 1 (only the holder — `eqSlots request/subject
resource/field/2/before` — or the referee writes) and 4 (a referee that is not the holder leaves
`owner`, `where`, `worn` unchanged). There is no `writeOnce`: a give is the holder's plain write of
`owner`, and what refuses the *second* of two concurrent gives is not the law but the durable CAS
(`DurableDataIntent.stale_read_guard_rejected`: a turn prepared against a root that has moved is
refused `staleReadGuard` before any law is read). `concurrent_gives_both_law_admitted` shows the law
alone admits both gives from the same pre-state; `second_give_refused_after_first` shows it refuses
the second once the first has landed. So `no_dupe_unique` is stated over an accepted log, where each
step starts from the previous post (the CAS's guarantee).

Clauses 6 (drop-here) and 7 (take-here) read `joint/index/1/…` (K-JOINT-INDEX, not on this branch):
without it, drop and take are refused (`drop_needs_joint`); the theorems below hold with or without
those slots.
-/
import Assurance.SheetLaw

namespace Minidregg.Assurance.ItemLaw

open Minidregg.Pred (Pred State eval)
open Minidregg.Kernel.DeclaredResourceProjection (Values fieldName get)
open Minidregg.Kernel.LawHistory (Accepted stepsOf final)
open Minidregg.Kernel.LawView (ev_eq ev_le ev_memberOf ev_eqSlots ev_not ev_all ev_any Turn view admits get_before get_after get_verb get_subject find_none state_get scalarSlots_split mem_deltas mem_pairs mem_joint request_ne_field clock_ne_field joint_ne_field ne_of_lastc lastc_before lastc_after lastc_delta pairName_ne_fieldName fieldName_inj get_delta)
set_option autoImplicit false

/-! ## §1. Constants -/

/-- The `{UPPER}` placeholders of `law.management ; law.item`. -/
structure Params where
  REF : Int
  W_FOUNDER : Int
  ID : Int
  KIND : Int

/-! ## §2. The law, literally (`law.management.json`, then `item/law.item.json` clauses 1–7) -/

section Law
set_option linter.unusedVariables false

def management (p : Params) : Pred :=
  Pred.any [
    .eq "request/verb" 1,
    .eq "request/verb" 2,
    Pred.all [
      .memberOf "request/verb" [3, 4, 5],
      .eq "request/subject" p.W_FOUNDER]]

/-- clause 1 -/
def itemClause1 (p : Params) : Pred :=
  Pred.any [
    .not (.eq "request/verb" 2),
    .eqSlots "request/subject" "resource/field/2/before",
    .eq "request/subject" p.REF]

/-- clause 2 -/
def itemClause2 (p : Params) : Pred :=
  Pred.any [
    .not (.eq "request/verb" 2),
    Pred.all [
      .eq "resource/field/0/after" p.ID,
      .eq "resource/field/1/after" p.KIND]]

/-- clause 3 -/
def itemClause3 (p : Params) : Pred :=
  Pred.any [
    .not (.eq "request/verb" 2),
    .le "resource/field/5/delta" 0]

/-- clause 4 -/
def itemClause4 (p : Params) : Pred :=
  Pred.any [
    .not (.eq "request/verb" 2),
    .not (.eq "request/subject" p.REF),
    .eqSlots "request/subject" "resource/field/2/before",
    Pred.all [
      .eq "resource/field/2/delta" 0,
      .eq "resource/field/3/delta" 0,
      .eq "resource/field/4/delta" 0]]

/-- clause 5 -/
def itemClause5 (p : Params) : Pred :=
  Pred.any [
    .not (.eq "request/verb" 2),
    .eq "resource/field/2/after" p.REF,
    .eq "resource/field/3/after" 0]

/-- clause 6 -/
def itemClause6 (p : Params) : Pred :=
  Pred.any [
    .not (.eq "request/verb" 2),
    .not (.eq "resource/field/2/after" p.REF),
    .eq "resource/field/2/delta" 0,
    Pred.all [
      .eqSlots "joint/index/1/resource/field/0/after" "request/subject",
      .eqSlots "resource/field/3/after" "joint/index/1/resource/field/1/after"]]

/-- clause 7 -/
def itemClause7 (p : Params) : Pred :=
  Pred.any [
    .not (.eq "request/verb" 2),
    .not (.eq "resource/field/2/before" p.REF),
    .eq "resource/field/2/delta" 0,
    .eq "resource/field/3/before" 0,
    Pred.all [
      .eqSlots "joint/index/1/resource/field/0/after" "resource/field/2/after",
      .eqSlots "joint/index/1/resource/field/1/after" "resource/field/3/before"]]

end Law

/-- The installed item law: management is clause 0, then clauses 1–7 in file order. -/
def itemClauses (p : Params) : List Pred :=
  [management p, itemClause1 p, itemClause2 p, itemClause3 p, itemClause4 p, itemClause5 p,
   itemClause6 p, itemClause7 p]

def itemLaw (p : Params) : Pred := Pred.all (itemClauses p)

theorem item_clause {p : Params} {o n : State} (h : eval (itemLaw p) o n = true) {q : Pred}
    (hq : q ∈ itemClauses p) : eval q o n = true :=
  ev_all.mp h q hq

/-! ## §3. Law-level: who may write, and what the referee may not touch -/

/-- **Clauses 1 and 4.** An admitted mutate is either by the holder (the subject equals `owner`
before), or by the referee, in which case `owner`, `where` and `worn` each have a zero delta. -/
theorem holder_or_referee (p : Params) (o n : State) (x : Int)
    (admitted : eval (itemLaw p) o n = true) (verb : n.get "request/verb" = some 2)
    (subject : n.get "request/subject" = some x) :
    n.get "resource/field/2/before" = some x ∨
      (x = p.REF ∧ n.get "resource/field/2/delta" = some 0 ∧
        n.get "resource/field/3/delta" = some 0 ∧ n.get "resource/field/4/delta" = some 0) := by
  have c1 := item_clause admitted (q := itemClause1 p) (by simp [itemClauses])
  have c4 := item_clause admitted (q := itemClause4 p) (by simp [itemClauses])
  simp only [itemClause1, itemClause4, ev_any, ev_all, ev_not, ev_eq, ev_eqSlots, List.mem_cons,
    List.not_mem_nil, or_false, exists_eq_or_imp, exists_eq_left, verb, subject,
    not_true_eq_false, false_or, forall_eq_or_imp, forall_eq, Option.some.injEq] at c1 c4
  rcases c1 with ⟨y, rfl, hy⟩ | hr
  · exact .inl hy
  · rcases c4 with c4 | ⟨y, rfl, hy⟩ | ⟨h2, h3, h4⟩
    · exact absurd hr c4
    · exact .inl hy
    · exact .inr ⟨hr, h2, h3, h4⟩

/-- **A former holder is a stranger.** Once `owner` is `B`, a subject `A ≠ B` that is not the
referee has no admitted mutate. -/
theorem former_holder_refused (p : Params) (o n : State) (a b : Int)
    (verb : n.get "request/verb" = some 2) (subject : n.get "request/subject" = some a)
    (owner : n.get "resource/field/2/before" = some b) (moved : a ≠ b) (notReferee : a ≠ p.REF) :
    eval (itemLaw p) o n = false := by
  apply Bool.eq_false_iff.mpr
  intro admitted
  rcases holder_or_referee p o n a admitted verb subject with h | ⟨h, -⟩
  · rw [owner] at h; exact moved (Option.some.inj h).symm
  · exact notReferee h

/-! ## §4. Over the declared field store -/

/-- The `delta` slot is absent when the pre-state lacks the field. -/
theorem get_delta_absent (t : Turn) (pre post : Values) (N : Nat) (hpre : get pre N = none) :
    (view t pre post).get (fieldName N "delta") = none := by
  have hw : Minidregg.Kernel.LawView.lastc "delta" = some 'r' ∨ Minidregg.Kernel.LawView.lastc "delta" = some 'e' ∨
      Minidregg.Kernel.LawView.lastc "delta" = some 'a' := .inr (.inr (by decide))
  have hreq := find_none (l := Minidregg.Kernel.LawView.request t.verb t.subject) (k := fieldName N "delta")
    (fun q hq => request_ne_field hq N _ hw (by decide))
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
  have hdel := find_none (k := fieldName N "delta")
    (l := post.filterMap (fun p => (get pre p.1).map fun old => (fieldName p.1 "delta", p.2 - old)))
    (fun q hq => by
      simp only [List.mem_filterMap, Option.map_eq_some_iff] at hq
      obtain ⟨p, -, old, hold, rfl⟩ := hq
      intro e
      have : p.1 = N := fieldName_inj.mp e
      rw [this, hpre] at hold
      cases hold)
  have hpair := find_none (k := fieldName N "delta")
    (l := post.flatMap (fun a => post.filterMap fun b => do
        let oldA ← get pre a.1
        let oldB ← get pre b.1
        return (Minidregg.Kernel.DeclaredResourceProjection.pairName a.1 b.1, a.2 + b.2 - oldA - oldB)))
    (fun q hq => by
      obtain ⟨a, b, e⟩ := mem_pairs hq
      rw [e]; exact pairName_ne_fieldName a b N _)
  have hclock := find_none (k := fieldName N "delta") (l := Minidregg.Kernel.LawView.clockSlots t.now)
    (fun q hq => clock_ne_field hq N _ hw (by decide))
  have hjoint := find_none (k := fieldName N "delta") (l := Minidregg.Kernel.LawView.jointSlots t.joint)
    (fun q hq => joint_ne_field hq N _)
  simp only [view, state_get, scalarSlots_split, List.find?_append, hreq, hbef, haft, hdel, hpair,
    hclock, hjoint, Option.or_none]
  rfl

/-- **One step.** An admitted mutate is by the holder, or it is the referee's and `owner` is present
and unchanged. -/
theorem no_dupe_step (p : Params) (pre : Values) (t : Turn)
    (admitted : admits (itemLaw p) pre t = true) (verb : t.verb = 2) :
    get pre 2 = some t.subject ∨
      (t.subject = p.REF ∧ ∃ o, get pre 2 = some o ∧ get t.post 2 = some o) := by
  rcases holder_or_referee p _ _ t.subject admitted (by rw [get_verb, verb]) (get_subject _ _ _) with
    h | ⟨hr, h2, -, -⟩
  · rw [show "resource/field/2/before" = fieldName 2 "before" from rfl, get_before] at h
    exact .inl h
  · rw [show "resource/field/2/delta" = fieldName 2 "delta" from rfl] at h2
    cases hpre : get pre 2 with
    | none => rw [get_delta_absent _ _ _ _ hpre] at h2; cases h2
    | some o =>
      rw [get_delta _ _ _ _ o hpre] at h2
      cases hpost : get t.post 2 with
      | none => rw [hpost] at h2; cases h2
      | some a =>
        rw [hpost] at h2
        have : a = o := by simp at h2; omega
        exact .inr ⟨hr, o, rfl, by rw [this]⟩

/-! ## §5. `no_dupe_unique` over an accepted history -/

/-- **Nobody takes an item from its holder.** Along an accepted log from a state where `o` holds
the item, if `o` itself never writes, `o` still holds it at the end — whoever else writes, however
many times (by induction over the log). -/
theorem holder_keeps_unless_holder_writes (p : Params) :
    ∀ (v : Values) (ts : List Turn) (o : Int), Accepted (itemLaw p) v ts → get v 2 = some o →
      (∀ s ∈ stepsOf v ts, s.2.subject ≠ o) → get (final v ts) 2 = some o
  | v, [], _, _, h, _ => h
  | v, t :: ts, o, acc, h, others => by
    obtain ⟨verb, adm⟩ := acc.head
    have notHolder : t.subject ≠ o := others (v, t) (by simp [stepsOf])
    rcases no_dupe_step p v t adm verb with e | ⟨-, o', e, post⟩
    · rw [h] at e; exact absurd (Option.some.inj e).symm notHolder
    · rw [h] at e; cases e
      exact holder_keeps_unless_holder_writes p t.post ts o acc.tail post
        (fun s hs => others s (by simp [stepsOf, hs]))

/-- **`no_dupe_unique`** (MUD.md §2.2 / §5 item 6). Along any accepted history of a unique item:
(1) every step is by the holder at that height, or by the referee leaving `owner` present and
unchanged; (2) so every change of `owner` was written by the owner it took the item from; and
(3) a holder who never writes keeps the item, whoever else writes. Two subjects never both hold it:
the owner at each height is the one `owner` value, and only that subject can move it on. -/
theorem no_dupe_unique (p : Params) (v : Values) (ts : List Turn)
    (acc : Accepted (itemLaw p) v ts) :
    (∀ s ∈ stepsOf v ts, get s.1 2 = some s.2.subject ∨
      (s.2.subject = p.REF ∧ ∃ o, get s.1 2 = some o ∧ get s.2.post 2 = some o)) ∧
    (∀ s ∈ stepsOf v ts, get s.2.post 2 ≠ get s.1 2 → get s.1 2 = some s.2.subject) ∧
    (∀ o, get v 2 = some o → (∀ s ∈ stepsOf v ts, s.2.subject ≠ o) →
      get (final v ts) 2 = some o) := by
  refine ⟨fun s hs => ?_, fun s hs moved => ?_, fun o h others =>
    holder_keeps_unless_holder_writes p v ts o acc h others⟩
  · obtain ⟨verb, adm⟩ := acc s hs
    exact no_dupe_step p s.1 s.2 adm verb
  · obtain ⟨verb, adm⟩ := acc s hs
    rcases no_dupe_step p s.1 s.2 adm verb with h | ⟨-, o, e, post⟩
    · exact h
    · rw [e, post] at moved; exact absurd rfl moved

/-! ## §6. The kernel form -/

section Kernel
open Minidregg.Compiler
open Minidregg.Compiler.CanonicalPolicyAdmission
open Minidregg.Kernel.MultiCellHyperedge
open Minidregg.Kernel.DeclaredResourceController
open Minidregg.Theory.TypedAuthorization

variable {F : Type} [Field F] [DecidableEq F] {deployment : Deployment}
  {profile : CanonicalRuntimeProfile.Profile F} {ambient : Ambient}
  {durable : Durable} {command : Command}

/-- The leg's installed law is the item law at `p`. -/
def ItemInstalled (p : Params)
    {prepared : PreparedInvocation deployment profile ambient durable command}
    (tuple : PreparedTuple (plan prepared)) (incidence : Incidence command) : Prop :=
  ∀ committed, (policyConfig prepared tuple incidence).registry.resolve
      (tuple.request incidence).2.policyId (tuple.request incidence).2.policyRevision = some committed →
    committed.record.predicate = itemLaw p

/-- **Kernel form of clauses 1 and 4.** On every leg the controller admitted under the item law, a
mutate was by the holder, or by the referee with zero `owner`/`where`/`worn` deltas. -/
theorem kernel_holder_or_referee (p : Params)
    {prepared : PreparedInvocation deployment profile ambient durable command}
    {tuple : PreparedTuple (plan prepared)} {incidence : Incidence command} {envelope : List UInt8}
    (leg : CheckedLeg prepared tuple incidence envelope) (installed : ItemInstalled p tuple incidence)
    (x : Int) (verb : (step prepared tuple incidence).newState.get "request/verb" = some 2)
    (subject : (step prepared tuple incidence).newState.get "request/subject" = some x) :
    (step prepared tuple incidence).newState.get "resource/field/2/before" = some x ∨
      (x = p.REF ∧ (step prepared tuple incidence).newState.get "resource/field/2/delta" = some 0 ∧
        (step prepared tuple incidence).newState.get "resource/field/3/delta" = some 0 ∧
        (step prepared tuple incidence).newState.get "resource/field/4/delta" = some 0) := by
  obtain ⟨committed, resolved, holds⟩ := Minidregg.Kernel.LawHistory.checked_leg_policy_eval leg
  rw [installed committed resolved] at holds
  exact holder_or_referee p _ _ x holds verb subject

end Kernel

/-! ## §7. Poles, by `decide` -/

section Poles

/-- The referee is 3, the founder 1; item 42 is a sword (kind 3, `item/fields.json` itemKinds). -/
def realm : Params := { REF := 3, W_FOUNDER := 1, ID := 42, KIND := 3 }

/-- Item 42 held by `o`, lying `where`, worn `w`, with `c` charges. -/
def item (o where' w c : Int) : Values := [(0, 42), (1, 3), (2, o), (3, where'), (4, w), (5, c)]

def heldBy7 : Values := item 7 0 0 5
def giveTo8 : Turn := ⟨2, 7, none, [], item 8 0 0 5⟩
def giveTo9 : Turn := ⟨2, 7, none, [], item 9 0 0 5⟩
def eightGivesTo9 : Turn := ⟨2, 8, none, [], item 9 0 0 5⟩
def strangerTakes : Turn := ⟨2, 9, none, [], item 9 0 0 5⟩
def refereeMoves : Turn := ⟨2, 3, none, [], item 9 0 0 5⟩
def refereeSpends : Turn := ⟨2, 3, none, [], item 7 0 0 4⟩
def refereeRefills : Turn := ⟨2, 3, none, [], item 7 0 0 6⟩
def holderWears : Turn := ⟨2, 7, none, [], item 7 0 1 5⟩
/-- 7 drops the item in room 101: owner := the referee (the floor), where := 101. Joint index 1 is
7's sheet (id 7, at 101) under K-JOINT-INDEX. -/
def dropWithJoint : Turn := ⟨2, 7, none, [(1, 0, "after", 7), (1, 1, "after", 101)], item 3 101 0 5⟩
def dropWaveC : Turn := ⟨2, 7, none, [], item 3 101 0 5⟩

/-- Satisfiable: the holder's give is admitted. Refutable: a stranger's `owner := me` is refused,
and so is the referee's move of an item a player holds. -/
theorem give_poles :
    admits (itemLaw realm) heldBy7 giveTo8 = true ∧
      admits (itemLaw realm) heldBy7 strangerTakes = false ∧
      admits (itemLaw realm) heldBy7 refereeMoves = false := by
  decide

/-- The referee may spend charges (clause 4 leaves them to it), never refill them (clause 3); the
holder may wear the item. -/
theorem charges_and_wear_poles :
    admits (itemLaw realm) heldBy7 refereeSpends = true ∧
      admits (itemLaw realm) heldBy7 refereeRefills = false ∧
      admits (itemLaw realm) heldBy7 holderWears = true := by
  decide

/-- **The law alone does not refuse a concurrent double give.** Two gives by the holder, prepared
against the same pre-state, are each admitted by the law; only the durable CAS refuses the second
(`staleReadGuard`). -/
theorem concurrent_gives_both_law_admitted :
    admits (itemLaw realm) heldBy7 giveTo8 = true ∧ admits (itemLaw realm) heldBy7 giveTo9 = true := by
  decide

/-- ...and once the first give has landed, the law refuses the second: 7 is no longer the holder. -/
theorem second_give_refused_after_first :
    admits (itemLaw realm) (item 8 0 0 5) giveTo9 = false := by
  decide

/-- Drop needs K-JOINT-INDEX: admitted with 7's sheet at joint index 1, refused on this branch. -/
theorem drop_needs_joint :
    admits (itemLaw realm) heldBy7 dropWithJoint = true ∧
      admits (itemLaw realm) heldBy7 dropWaveC = false := by
  decide

/-- A chain of gives 7 → 8 → 9 is an accepted history; 7 → 8 then 7 → 9 is not. -/
theorem give_chain_poles :
    Accepted (itemLaw realm) heldBy7 [giveTo8, eightGivesTo9] ∧
      get (final heldBy7 [giveTo8, eightGivesTo9]) 2 = some 9 ∧
      ¬ Accepted (itemLaw realm) heldBy7 [giveTo8, giveTo9] := by
  decide

end Poles

/-! ## Axiom pins -/

/-- info: 'Minidregg.Assurance.ItemLaw.holder_or_referee' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms holder_or_referee
/-- info: 'Minidregg.Assurance.ItemLaw.former_holder_refused' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms former_holder_refused
/-- info: 'Minidregg.Assurance.ItemLaw.get_delta_absent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms get_delta_absent
/-- info: 'Minidregg.Assurance.ItemLaw.no_dupe_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms no_dupe_step
/-- info: 'Minidregg.Assurance.ItemLaw.holder_keeps_unless_holder_writes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms holder_keeps_unless_holder_writes
/-- info: 'Minidregg.Assurance.ItemLaw.no_dupe_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms no_dupe_unique
/-- info: 'Minidregg.Assurance.ItemLaw.kernel_holder_or_referee' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms kernel_holder_or_referee
/-- info: 'Minidregg.Assurance.ItemLaw.give_poles' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms give_poles
/-- info: 'Minidregg.Assurance.ItemLaw.charges_and_wear_poles' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms charges_and_wear_poles
/-- info: 'Minidregg.Assurance.ItemLaw.concurrent_gives_both_law_admitted' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms concurrent_gives_both_law_admitted
/-- info: 'Minidregg.Assurance.ItemLaw.second_give_refused_after_first' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms second_give_refused_after_first
/-- info: 'Minidregg.Assurance.ItemLaw.drop_needs_joint' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms drop_needs_joint
/-- info: 'Minidregg.Assurance.ItemLaw.give_chain_poles' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms give_chain_poles

end Minidregg.Assurance.ItemLaw
