/-
# Theory.StoreNormalize -- the normal form of a guarded patch is its diff

A receiver's guarded patch is the local view of a transition: every guard is
checked at the store its prefix produced (`Patch.ValidFrom`).  This module gives
that patch a normal form, `Patch.normalize`, that keeps every guard that can
fail and collapses everything that cannot, so that under validity its write
footprint is exactly the set of addresses whose value differs.

The rewrites, all at one address and all exact (`Op.fuse_enabled_iff`):

* a read whose observed value is the value an earlier modifying operation at the
  same address left is dropped (it is implied by that operation's guard);
* `write a x y` then `write a y z` is `write a x z`; `write a x y` then
  `free a y` is `free a x`; `free a x` then `allocate a v` is `write a x v`;
* `allocate a v` then `write a v z` is `allocate a z`, and `allocate a v` then
  `free a v` is the absence guard `read a none` -- both only in a RAM
  namespace, where the second operation's discipline check is implied;
* a write-back `write a x x` in a RAM namespace is the read guard
  `read a (some x)` (`Op.tidy`).  The guard survives; only the write goes.

Operations at distinct addresses commute (`Op.apply_comm`), so an operation is
fused with the next operation *at its address*, past any operations at other
addresses (`Patch.pull`).  A read is never fused with what follows it, and a
read of an address no earlier operation wrote is never dropped.

A guard whose value disagrees with what the patch itself produced is never
fused, so a stale guard stays refused: `normalize_validFrom_iff` holds in both
directions.  Because two rewrites replace a write by a read, `run` agrees only
on valid patches (`normalize_run`); on an invalid patch the two runs may differ,
and neither is accepted.
-/
import Theory.Store

namespace Minidregg.Theory.Store

set_option autoImplicit false
set_option linter.dupNamespace false

universe u v w

namespace Op

variable {L : Layout.{u, v, w}}

/-! ## One operation -/

theorem update_update (s : Store L) (a : Address L) (x y : Option (L.Value a.1)) :
    (DFinsupp.update s a x).update a y = DFinsupp.update s a y := by
  apply DFinsupp.ext; intro b
  simp only [DFinsupp.coe_update, Function.update_idem]

theorem update_of_eq (s : Store L) (a : Address L) (x : Option (L.Value a.1))
    (h : s a = x) : DFinsupp.update s a x = s := by
  rw [← h, DFinsupp.update_self]

/-- A write-back of its own guard value in a RAM namespace is that read guard. -/
def tidy : Op L → Op L
  | .write space key before after =>
      if before = after ∧ L.discipline space = .ram then .read space key (some before)
      else .write space key before after
  | op => op

/-- Fuse `first` then `second`, when they touch one address and the second's
guard is exactly the value the first left.  `none` otherwise -- in particular
whenever the second guard is stale, so no rewrite can launder it. -/
def fuse : Op L → Op L → Option (Op L)
  | .write s₁ k₁ x y, .read s₂ k₂ observed =>
      if h : s₂ = s₁ then
        match h with
        | rfl => if k₂ = k₁ ∧ observed = some y then some (.write s₂ k₁ x y) else none
      else none
  | .write s₁ k₁ x y, .write s₂ k₂ y' z =>
      if h : s₂ = s₁ then
        match h with
        | rfl => if k₂ = k₁ ∧ y' = y then some (.write s₂ k₁ x z) else none
      else none
  | .write s₁ k₁ x y, .free s₂ k₂ y' =>
      if h : s₂ = s₁ then
        match h with
        | rfl => if k₂ = k₁ ∧ y' = y then some (.free s₂ k₁ x) else none
      else none
  | .allocate s₁ k₁ v, .read s₂ k₂ observed =>
      if h : s₂ = s₁ then
        match h with
        | rfl => if k₂ = k₁ ∧ observed = some v then some (.allocate s₂ k₁ v) else none
      else none
  | .allocate s₁ k₁ v, .write s₂ k₂ v' z =>
      if h : s₂ = s₁ then
        match h with
        | rfl =>
            if k₂ = k₁ ∧ v' = v ∧ L.discipline s₂ = .ram then some (.allocate s₂ k₁ z)
            else none
      else none
  | .allocate s₁ k₁ v, .free s₂ k₂ v' =>
      if h : s₂ = s₁ then
        match h with
        | rfl =>
            if k₂ = k₁ ∧ v' = v ∧ L.discipline s₂ = .ram then some (.read s₂ k₁ none)
            else none
      else none
  | .free s₁ k₁ x, .read s₂ k₂ observed =>
      if h : s₂ = s₁ then
        match h with
        | rfl => if k₂ = k₁ ∧ observed = none then some (.free s₂ k₁ x) else none
      else none
  | .free s₁ k₁ x, .allocate s₂ k₂ v =>
      if h : s₂ = s₁ then
        match h with
        | rfl => if k₂ = k₁ then some (.write s₂ k₁ x v) else none
      else none
  | _, _ => none

theorem enabled_congr {s t : Store L} (op : Op L) (same : s op.address = t op.address) :
    op.Enabled s ↔ op.Enabled t := by
  cases op <;> simp_all [Enabled, address, Store.Fresh]

theorem apply_address_ne (s : Store L) (op : Op L) (b : Address L) (ne : b ≠ op.address) :
    op.apply s b = s b :=
  op.apply_frame s b (fun h => ne (writeAddress?_eq_some h).symm)

/-- Operations at distinct addresses commute. -/
theorem apply_comm (s : Store L) (x r : Op L) (ne : x.address ≠ r.address) :
    x.apply (r.apply s) = r.apply (x.apply s) := by
  cases x <;> cases r <;>
    simp only [apply, Store.set] <;>
    first
    | rfl
    | (apply DFinsupp.ext; intro b
       simp only [DFinsupp.coe_update]
       exact congrFun (Function.update_comm (Ne.symm ne) _ _ _) b)

theorem tidy_enabled_iff (s : Store L) (op : Op L) : op.tidy.Enabled s ↔ op.Enabled s := by
  cases op with
  | write space key before after =>
      simp only [tidy]
      split
      · rename_i h; simp [Enabled, h.2]
      · rfl
  | _ => rfl

theorem tidy_apply (s : Store L) (op : Op L) (enabled : op.Enabled s) :
    op.tidy.apply s = op.apply s := by
  cases op with
  | write space key before after =>
      simp only [tidy]
      split
      · rename_i h
        rcases h with ⟨rfl, -⟩
        have := enabled.2
        simp only [apply, Store.set]
        rw [← this, DFinsupp.update_self]
      · rfl
  | _ => rfl

theorem tidy_writeAddress? (op : Op L) (b : Address L) (h : op.tidy.writeAddress? = some b) :
    op.writeAddress? = some b := by
  cases op with
  | write space key before after =>
      simp only [tidy] at h
      split at h
      · simp [writeAddress?] at h
      · exact h
  | _ => exact h

theorem tidy_tidy (op : Op L) : op.tidy.tidy = op.tidy := by
  cases op with
  | write space key before after =>
      by_cases h : before = after ∧ L.discipline space = .ram <;> simp [tidy, h]
  | _ => rfl

/-- The exact specification of one fusion: same address, same guard, same effect
under that guard, and no new write. -/
theorem fuse_spec {p q m : Op L} (fused : p.fuse q = some m) :
    m.address = p.address ∧ q.address = p.address ∧
      (∀ s : Store L, m.Enabled s ↔ p.Enabled s ∧ q.Enabled (p.apply s)) ∧
      (∀ s : Store L, p.Enabled s → q.Enabled (p.apply s) → m.apply s = q.apply (p.apply s)) ∧
      (∀ b, m.writeAddress? = some b → p.writeAddress? = some b) := by
  cases p <;> cases q <;> simp only [fuse, reduceCtorEq] at fused <;>
    (split at fused <;> [skip; simp at fused]) <;>
    (rename_i hs; subst hs; simp only at fused) <;>
    (split at fused <;> [skip; simp at fused]) <;>
    (rename_i hc; simp only [Option.some.injEq] at fused; subst fused) <;>
    (obtain ⟨rfl, hc⟩ := hc) <;>
    (try obtain ⟨rfl, hc⟩ := hc) <;>
    refine ⟨rfl, rfl, ?_, ?_, ?_⟩ <;>
    (try intro s) <;>
    simp_all [Enabled, apply, Store.Fresh, writeAddress?, address, Store.set]
  all_goals
    intros
    first
    | (rw [update_update]; exact (update_of_eq _ _ _ ‹_›).symm)
    | simp only [update_update]

/-- Completeness of `fuse`: a modifying operation fuses with the next operation
at its address whenever that operation's guard holds at the value it left. -/
theorem fuse_complete {p r : Op L} {s t : Store L}
    (writes : p.writeAddress? = some p.address) (enabled : p.Enabled s)
    (sameAddress : r.address = p.address) (next : r.Enabled t)
    (atAddress : t p.address = p.apply s p.address) :
    p.fuse r ≠ none := by
  cases p <;> cases r <;> simp only [writeAddress?, address, reduceCtorEq,
    Sigma.mk.inj_iff] at writes sameAddress <;>
    (obtain ⟨rfl, hk⟩ := sameAddress; cases eq_of_heq hk) <;>
    dsimp only [Op.address, apply] at atAddress <;>
    simp only [Store.set_eq] at atAddress <;>
    simp_all [fuse, Enabled, Store.Fresh]

theorem apply_of_writeAddress?_none (s : Store L) (op : Op L)
    (reads : op.writeAddress? = none) : op.apply s = s := by
  cases op <;> simp_all [writeAddress?, apply]

/-- A tidied modifying operation, enabled, changes its address. -/
theorem apply_changes {p : Op L} {s : Store L} (tidied : p.tidy = p)
    (writes : p.writeAddress? = some p.address) (enabled : p.Enabled s) :
    p.apply s p.address ≠ s p.address := by
  cases p with
  | read => simp [writeAddress?] at writes
  | write space key before after =>
      by_cases h : before = after ∧ L.discipline space = .ram
      · simp [tidy, h] at tidied
      · have ram := enabled.1
        have ne : before ≠ after := fun e => h ⟨e, ram⟩
        simp only [apply, address, Store.set_eq, enabled.2]
        exact fun e => ne (Option.some.inj e).symm
  | allocate space key value =>
      have fresh : s ⟨space, key⟩ = none := enabled.2
      simp only [apply, address, Store.set_eq, fresh]
      simp
  | free space key before =>
      simp only [apply, address, Store.set_eq, enabled.2]
      simp

end Op

/-! ## Patches -/

namespace Patch

variable {L : Layout.{u, v, w}}

/-- Fuse `p` with the next operation in `q` at `p`'s address, if that fusion
exists.  Operations at other addresses are passed over in place; the first
operation at `p`'s address that does not fuse stops the search. -/
def pull (p : Op L) : Patch L → Option (Op L × Patch L)
  | [] => none
  | r :: rest =>
      if r.address = p.address then (p.fuse r).map fun m => (m, rest)
      else (pull p rest).map fun mr => (mr.1, r :: mr.2)

/-- Push `p` onto an already-normal `q`, fusing for as long as fusion applies.
The fuel `q.length` always suffices (`pull_length`); it keeps the recursion
structural so concrete normal forms reduce by `rfl` and `decide`. -/
def pushAux : Nat → Op L → Patch L → Patch L
  | 0, p, q => p.tidy :: q
  | n + 1, p, q =>
      match pull p.tidy q with
      | some mr => pushAux n mr.1 mr.2
      | none => p.tidy :: q

def push (p : Op L) (q : Patch L) : Patch L :=
  pushAux q.length p q

/-- **The normal form of a patch.**  Under validity it is the diff: its write
footprint is exactly the addresses whose value changes
(`normalize_writeFootprint_exact`). -/
def normalize : Patch L → Patch L
  | [] => []
  | op :: rest => push op (normalize rest)

/-- Normality: every operation is tidy and does not fuse with the next operation
at its address. -/
def Normal : Patch L → Prop
  | [] => True
  | p :: q => p.tidy = p ∧ pull p q = none ∧ Normal q

theorem mem_writeFootprint_cons (op : Op L) (rest : Patch L) (b : Address L) :
    b ∈ writeFootprint (op :: rest) ↔ op.writeAddress? = some b ∨ b ∈ writeFootprint rest := by
  simp [writeFootprint]

theorem pull_length {p : Op L} {q : Patch L} {mr : Op L × Patch L}
    (pulled : pull p q = some mr) : mr.2.length + 1 = q.length := by
  induction q generalizing mr with
  | nil => simp [pull] at pulled
  | cons r rest ih =>
      simp only [pull] at pulled
      split at pulled
      · simp only [Option.map_eq_some_iff] at pulled
        obtain ⟨m, -, rfl⟩ := pulled
        rfl
      · simp only [Option.map_eq_some_iff] at pulled
        obtain ⟨mr', h, rfl⟩ := pulled
        simp [← ih h]

/-- Two operations at distinct addresses commute, for validity and for `run`. -/
theorem swap (x r : Op L) (l : Patch L) (ne : x.address ≠ r.address) (s : Store L) :
    (ValidFrom s (x :: r :: l) ↔ ValidFrom s (r :: x :: l)) ∧
      run s (x :: r :: l) = run s (r :: x :: l) := by
  have hr : r.Enabled (x.apply s) ↔ r.Enabled s :=
    r.enabled_congr (x.apply_address_ne s r.address (Ne.symm ne))
  have hx : x.Enabled (r.apply s) ↔ x.Enabled s :=
    x.enabled_congr (r.apply_address_ne s x.address ne)
  have comm := x.apply_comm s r ne
  refine ⟨?_, ?_⟩
  · simp only [ValidFrom, hr, hx, comm]
    tauto
  · simp only [run_cons, comm]

theorem pull_spec {p : Op L} {q : Patch L} {mr : Op L × Patch L}
    (pulled : pull p q = some mr) :
    mr.1.address = p.address ∧
      (∀ s, ValidFrom s (mr.1 :: mr.2) ↔ ValidFrom s (p :: q)) ∧
      (∀ s, ValidFrom s (p :: q) → run s (mr.1 :: mr.2) = run s (p :: q)) ∧
      (∀ b, b ∈ writeFootprint (mr.1 :: mr.2) → b ∈ writeFootprint (p :: q)) := by
  induction q generalizing mr with
  | nil => simp [pull] at pulled
  | cons r rest ih =>
      simp only [pull] at pulled
      split at pulled
      · simp only [Option.map_eq_some_iff] at pulled
        obtain ⟨m, fused, rfl⟩ := pulled
        obtain ⟨hm, -, hen, happ, hwa⟩ := Op.fuse_spec fused
        refine ⟨hm, fun s => ?_, fun s valid => ?_, fun b member => ?_⟩
        · simp only [ValidFrom]
          constructor
          · rintro ⟨em, rest⟩
            obtain ⟨ep, er⟩ := (hen s).1 em
            exact ⟨ep, er, happ s ep er ▸ rest⟩
          · rintro ⟨ep, er, rest⟩
            exact ⟨(hen s).2 ⟨ep, er⟩, (happ s ep er).symm ▸ rest⟩
        · simp only [run_cons, happ s valid.1 valid.2.1]
        · simp only [mem_writeFootprint_cons] at member ⊢
          rcases member with h | h
          · exact Or.inl (hwa b h)
          · exact Or.inr (Or.inr h)
      · rename_i different
        simp only [Option.map_eq_some_iff] at pulled
        obtain ⟨mr', h, rfl⟩ := pulled
        obtain ⟨hm, hval, hrun, hwf⟩ := ih h
        have ne₁ : mr'.1.address ≠ r.address := fun e => different (e.symm.trans hm)
        have ne₂ : p.address ≠ r.address := fun e => different e.symm
        refine ⟨hm, fun s => ?_, fun s valid => ?_, fun b member => ?_⟩
        · rw [(swap _ _ _ ne₁ s).1, (swap _ _ _ ne₂ s).1]
          simp only [ValidFrom] at hval ⊢
          rw [hval]
        · have valid' := (swap _ _ _ ne₂ s).1.1 valid
          calc run s (mr'.1 :: r :: mr'.2) = run s (r :: mr'.1 :: mr'.2) := (swap _ _ _ ne₁ s).2
            _ = run (r.apply s) (mr'.1 :: mr'.2) := rfl
            _ = run (r.apply s) (p :: rest) := hrun _ valid'.2
            _ = run s (r :: p :: rest) := rfl
            _ = run s (p :: r :: rest) := ((swap _ _ _ ne₂ s).2).symm
        · simp only [mem_writeFootprint_cons] at member ⊢
          have := fun h => (mem_writeFootprint_cons _ _ b).1 (hwf b ((mem_writeFootprint_cons _ _ b).2 h))
          tauto

theorem tidy_cons_spec (p : Op L) (q : Patch L) :
    (∀ s, ValidFrom s (p.tidy :: q) ↔ ValidFrom s (p :: q)) ∧
      (∀ s, ValidFrom s (p :: q) → run s (p.tidy :: q) = run s (p :: q)) ∧
      (∀ b, b ∈ writeFootprint (p.tidy :: q) → b ∈ writeFootprint (p :: q)) := by
  refine ⟨fun s => ?_, fun s valid => ?_, fun b member => ?_⟩
  · simp only [ValidFrom, Op.tidy_enabled_iff]
    constructor
    · rintro ⟨e, rest⟩; exact ⟨e, p.tidy_apply s e ▸ rest⟩
    · rintro ⟨e, rest⟩; exact ⟨e, (p.tidy_apply s e).symm ▸ rest⟩
  · simp only [run_cons, p.tidy_apply s valid.1]
  · simp only [mem_writeFootprint_cons] at member ⊢
    rcases member with h | h
    · exact Or.inl (p.tidy_writeAddress? b h)
    · exact Or.inr h

theorem pushAux_spec (n : Nat) (p : Op L) (q : Patch L) :
    (∀ s, ValidFrom s (pushAux n p q) ↔ ValidFrom s (p :: q)) ∧
      (∀ s, ValidFrom s (p :: q) → run s (pushAux n p q) = run s (p :: q)) ∧
      (∀ b, b ∈ writeFootprint (pushAux n p q) → b ∈ writeFootprint (p :: q)) := by
  induction n generalizing p q with
  | zero => exact tidy_cons_spec p q
  | succ n ih =>
      obtain ⟨tv, tr, tw⟩ := tidy_cons_spec p q
      simp only [pushAux]
      split
      · rename_i mr pulled
        obtain ⟨-, pv, pr, pw⟩ := pull_spec pulled
        obtain ⟨iv, ir, iw⟩ := ih mr.1 mr.2
        refine ⟨fun s => (iv s).trans ((pv s).trans (tv s)), fun s valid => ?_,
          fun b member => tw b (pw b (iw b member))⟩
        have v1 := (tv s).2 valid
        have v2 := (pv s).2 v1
        rw [ir s v2, pr s v1, tr s valid]
      · exact tidy_cons_spec p q

theorem push_spec (p : Op L) (q : Patch L) :
    (∀ s, ValidFrom s (push p q) ↔ ValidFrom s (p :: q)) ∧
      (∀ s, ValidFrom s (p :: q) → run s (push p q) = run s (p :: q)) ∧
      (∀ b, b ∈ writeFootprint (push p q) → b ∈ writeFootprint (p :: q)) :=
  pushAux_spec _ p q

/-- **Validity is exactly preserved, in both directions.**  The forward half is
`normalize_valid`; the backward half is the refutable pole: a normal form never
launders a stale guard. -/
theorem normalize_validFrom_iff (s : Store L) (p : Patch L) :
    ValidFrom s (normalize p) ↔ ValidFrom s p := by
  induction p generalizing s with
  | nil => rfl
  | cons op rest ih =>
      simp only [normalize]
      rw [(push_spec op _).1 s]
      simp only [ValidFrom]
      constructor
      · rintro ⟨e, v⟩; exact ⟨e, (ih _).1 v⟩
      · rintro ⟨e, v⟩; exact ⟨e, (ih _).2 v⟩

theorem normalize_valid {s : Store L} {p : Patch L} (valid : ValidFrom s p) :
    ValidFrom s (normalize p) :=
  (normalize_validFrom_iff s p).2 valid

/-- **No laundering.**  A patch refused at `s` stays refused after normalization. -/
theorem normalize_refuses {s : Store L} {p : Patch L} (refused : ¬ ValidFrom s p) :
    ¬ ValidFrom s (normalize p) :=
  fun valid => refused ((normalize_validFrom_iff s p).1 valid)

/-- On a valid patch, the normal form computes the same store.  (Validity is
needed: a write-back becomes a read guard, which does not write.) -/
theorem normalize_run {s : Store L} {p : Patch L} (valid : ValidFrom s p) :
    run s (normalize p) = run s p := by
  induction p generalizing s with
  | nil => rfl
  | cons op rest ih =>
      simp only [normalize]
      have v : ValidFrom s (op :: normalize rest) :=
        ⟨valid.1, normalize_valid valid.2⟩
      rw [(push_spec op _).2.1 s v, run_cons, run_cons, ih valid.2]

/-- Normalization never adds a written address. -/
theorem normalize_writeFootprint_subset (p : Patch L) :
    writeFootprint (normalize p) ⊆ writeFootprint p := by
  induction p with
  | nil => exact fun _ h => h
  | cons op rest ih =>
      intro b member
      have := (push_spec op _).2.2 b member
      rw [mem_writeFootprint_cons] at this ⊢
      exact this.imp_right (fun h => ih h)

/-! ### Normality and idempotence -/

theorem pull_none_of_removed {p o : Op L} {rest : Patch L} {mr : Op L × Patch L}
    (pulled : pull p rest = some mr) (different : o.address ≠ p.address)
    (none_ : pull o rest = none) : pull o mr.2 = none := by
  induction rest generalizing mr with
  | nil => simp [pull] at pulled
  | cons r tl ih =>
      simp only [pull] at pulled
      split at pulled
      · rename_i atP
        simp only [Option.map_eq_some_iff] at pulled
        obtain ⟨m, -, rfl⟩ := pulled
        have : r.address ≠ o.address := fun e => different (e.symm.trans atP)
        simpa [pull, this] using none_
      · simp only [Option.map_eq_some_iff] at pulled
        obtain ⟨mr', h, rfl⟩ := pulled
        simp only [pull] at none_ ⊢
        split at none_
        · rename_i atO; simpa [atO] using none_
        · rename_i notO
          simp only [notO, if_false, Option.map_eq_none_iff] at none_ ⊢
          exact ih h none_

theorem pull_normal {p : Op L} {q : Patch L} {mr : Op L × Patch L}
    (pulled : pull p q = some mr) (normal : Normal q) : Normal mr.2 := by
  induction q generalizing mr with
  | nil => simp [pull] at pulled
  | cons r rest ih =>
      obtain ⟨tidied, rNone, restNormal⟩ := normal
      simp only [pull] at pulled
      split at pulled
      · simp only [Option.map_eq_some_iff] at pulled
        obtain ⟨m, -, rfl⟩ := pulled
        exact restNormal
      · rename_i different
        simp only [Option.map_eq_some_iff] at pulled
        obtain ⟨mr', h, rfl⟩ := pulled
        exact ⟨tidied, pull_none_of_removed h different rNone, ih h restNormal⟩

theorem pushAux_normal (n : Nat) (p : Op L) (q : Patch L) (fuel : q.length ≤ n)
    (normal : Normal q) : Normal (pushAux n p q) := by
  induction n generalizing p q with
  | zero =>
      have : q = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.1 fuel)
      subst this
      exact ⟨p.tidy_tidy, rfl, trivial⟩
  | succ n ih =>
      simp only [pushAux]
      split
      · rename_i mr pulled
        have := pull_length pulled
        exact ih _ _ (by omega) (pull_normal pulled normal)
      · rename_i pulled
        exact ⟨p.tidy_tidy, pulled, normal⟩

theorem push_normal (p : Op L) {q : Patch L} (normal : Normal q) : Normal (push p q) :=
  pushAux_normal _ p q le_rfl normal

theorem normalize_normal (p : Patch L) : Normal (normalize p) := by
  induction p with
  | nil => trivial
  | cons op rest ih => exact push_normal op ih

theorem push_of_normal {p : Op L} {q : Patch L} (tidied : p.tidy = p)
    (none_ : pull p q = none) : push p q = p :: q := by
  unfold push
  cases q.length with
  | zero => simp [pushAux, tidied]
  | succ n => simp [pushAux, tidied, none_]

theorem normalize_of_normal {p : Patch L} (normal : Normal p) : normalize p = p := by
  induction p with
  | nil => rfl
  | cons op rest ih =>
      obtain ⟨tidied, none_, restNormal⟩ := normal
      simp only [normalize, ih restNormal]
      exact push_of_normal tidied none_

/-- **Idempotence.** -/
theorem normalize_idem (p : Patch L) : normalize (normalize p) = normalize p :=
  normalize_of_normal (normalize_normal p)

/-! ### Exactness: the normal form of a valid patch is its diff -/

/-- After a tidied, enabled modifying operation, a normal tail that is valid
from the resulting store never touches that address again. -/
theorem pull_none_untouched {o : Op L} {s : Store L}
    (writes : o.writeAddress? = some o.address) (enabled : o.Enabled s) :
    ∀ (q : Patch L) (t : Store L), pull o q = none → ValidFrom t q →
      t o.address = o.apply s o.address → ∀ r ∈ q, r.address ≠ o.address := by
  intro q
  induction q with
  | nil => intro _ _ _ _ r h; simp at h
  | cons r rest ih =>
      intro t none_ valid atAddress r' member
      simp only [pull] at none_
      split at none_
      · rename_i same
        simp only [Option.map_eq_none_iff] at none_
        exact absurd none_ (Op.fuse_complete writes enabled same valid.1 atAddress)
      · rename_i different
        simp only [Option.map_eq_none_iff] at none_
        rcases List.mem_cons.1 member with rfl | inRest
        · exact different
        · exact ih (r.apply t) none_ valid.2
            ((r.apply_address_ne t o.address (Ne.symm different)).trans atAddress) r' inRest

theorem normal_writeFootprint_exact {N : Patch L} (normal : Normal N) {s : Store L}
    (valid : ValidFrom s N) (a : Address L) :
    a ∈ writeFootprint N ↔ run s N a ≠ s a := by
  induction N generalizing s with
  | nil => simp [writeFootprint]
  | cons o q ih =>
      obtain ⟨tidied, none_, qNormal⟩ := normal
      obtain ⟨enabled, qValid⟩ := valid
      rw [mem_writeFootprint_cons, run_cons]
      cases hw : o.writeAddress? with
      | none =>
          rw [o.apply_of_writeAddress?_none s hw] at qValid ⊢
          simpa using ih qNormal qValid
      | some b =>
          have hb : o.address = b := Op.writeAddress?_eq_some hw
          subst hb
          by_cases ha : a = o.address
          · subst ha
            have untouched := pull_none_untouched hw enabled q (o.apply s) none_ qValid rfl
            have outside : o.address ∉ writeFootprint q := by
              intro member
              obtain ⟨r, mem, wr⟩ := (mem_writeFootprint_iff q _).1 member
              exact untouched r mem (Op.writeAddress?_eq_some wr)
            rw [run_frame _ q _ outside]
            simpa using Op.apply_changes tidied hw enabled
          · have same : o.apply s a = s a := o.apply_address_ne s a ha
            have : ¬ (some o.address = some a) := fun e => ha (Option.some.inj e).symm
            simp only [this, false_or]
            rw [ih qNormal qValid, same]

/-- **The normal form of a valid patch is its diff**: its write footprint is
exactly the set of addresses whose value the patch changes. -/
theorem normalize_writeFootprint_exact {s : Store L} {p : Patch L}
    (valid : ValidFrom s p) (a : Address L) :
    a ∈ writeFootprint (normalize p) ↔ run s p a ≠ s a := by
  rw [← normalize_run valid]
  exact normal_writeFootprint_exact (normalize_normal p) (normalize_valid valid) a

theorem normalize_writeFootprint_eq_diff {s : Store L} {p : Patch L}
    (valid : ValidFrom s p) :
    (↑(writeFootprint (normalize p)) : Set (Address L)) = {a | run s p a ≠ s a} :=
  Set.ext fun a => normalize_writeFootprint_exact valid a

end Patch

/-! ## Poles, over `Theory.Store.Example` -/

namespace Example

/-- The falsifier of fusion: two writes in a chain are one write. -/
theorem normalize_fuses_write_chain :
    Patch.normalize [write .heap 7 0 1, write .heap 7 1 2] = [write .heap 7 0 2] := rfl

/-- A write and its undo normalize to the read guard `heap[7] = 0`, with an empty
write footprint -- and that guard is still refused where `heap[7] ≠ 0`.  The
original patch's footprint is `{heap[7]}`, so footprint *preservation* is false. -/
theorem normalize_undo_is_read_guard :
    Patch.normalize [write .heap 7 0 1, write .heap 7 1 0] = [read .heap 7 (some 0)] ∧
      Patch.writeFootprint (Patch.normalize [write .heap 7 0 1, write .heap 7 1 0]) = ∅ ∧
      Patch.writeFootprint [write .heap 7 0 1, write .heap 7 1 0] = {at_ .heap 7} ∧
      ¬ Patch.ValidFrom (empty.set (at_ .heap 7) (some (5 : Nat)))
        (Patch.normalize [write .heap 7 0 1, write .heap 7 1 0]) := by
  refine ⟨rfl, ?_, ?_, ?_⟩ <;> decide

/-- A stale middle guard. -/
def stalePatch : Patch layout :=
  [allocate .heap 7 0, write .heap 7 0 1, write .heap 7 5 2, write .heap 7 2 3]

/-- **The refutable pole.**  The stale middle guard `heap[7] = 5` is refused in
the patch and in its normal form, which keeps the stale write; the endpoint-only
collapse `allocate heap[7] = 3` would have been accepted, so the pole has teeth. -/
theorem stale_middle_guard_stays_refused :
    Patch.normalize stalePatch = [allocate .heap 7 1, write .heap 7 5 3] ∧
      ¬ Patch.ValidFrom empty stalePatch ∧
      ¬ Patch.ValidFrom empty (Patch.normalize stalePatch) ∧
      Patch.ValidFrom empty [allocate .heap 7 3] := by
  refine ⟨rfl, ?_, ?_, ?_⟩ <;> decide

/-- Fusion passes over other addresses: the undo at `heap[7]` collapses across
the write at `heap[8]`, and the footprint is exactly `{heap[8]}`. -/
theorem normalize_interleaved :
    Patch.normalize [write .heap 7 0 1, write .heap 8 0 5, write .heap 7 1 0] =
      [read .heap 7 (some 0), write .heap 8 0 5] ∧
      Patch.writeFootprint
        (Patch.normalize [write .heap 7 0 1, write .heap 8 0 5, write .heap 7 1 0]) =
        {at_ .heap 8} := by
  refine ⟨rfl, ?_⟩; decide

/-- A read of an address no earlier operation wrote is never dropped, even when
a later write at the same address re-checks the same value. -/
theorem normalize_keeps_unwritten_read :
    Patch.normalize [read .heap 9 (some 4), read .heap 7 (some 0), write .heap 7 0 1] =
      [read .heap 9 (some 4), read .heap 7 (some 0), write .heap 7 0 1] := rfl

/-- Allocate-then-free in RAM is the absence guard; in the append-only log the
free is never enabled and the pair is kept, still refused. -/
theorem normalize_allocate_free :
    Patch.normalize [allocate .heap 7 1, Op.free .heap 7 1] = [read .heap 7 none] ∧
      Patch.normalize [allocate .log 0 1, Op.free .log 0 1] =
        [allocate .log 0 1, Op.free .log 0 1] ∧
      ¬ Patch.ValidFrom empty [allocate .log 0 1, Op.free .log 0 1] := by
  refine ⟨rfl, rfl, ?_⟩; decide

end Example

/-- info: 'Minidregg.Theory.Store.Patch.normalize_validFrom_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Patch.normalize_validFrom_iff
/-- info: 'Minidregg.Theory.Store.Patch.normalize_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Patch.normalize_run
/-- info: 'Minidregg.Theory.Store.Patch.normalize_writeFootprint_subset' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Patch.normalize_writeFootprint_subset
/-- info: 'Minidregg.Theory.Store.Patch.normalize_writeFootprint_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Patch.normalize_writeFootprint_exact
/-- info: 'Minidregg.Theory.Store.Patch.normalize_writeFootprint_eq_diff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Patch.normalize_writeFootprint_eq_diff
/-- info: 'Minidregg.Theory.Store.Patch.normalize_idem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Patch.normalize_idem
/-- info: 'Minidregg.Theory.Store.Patch.normalize_refuses' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Patch.normalize_refuses
/-- info: 'Minidregg.Theory.Store.Example.normalize_fuses_write_chain' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms Example.normalize_fuses_write_chain
/-- info: 'Minidregg.Theory.Store.Example.normalize_undo_is_read_guard' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Example.normalize_undo_is_read_guard
/-- info: 'Minidregg.Theory.Store.Example.stale_middle_guard_stays_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Example.stale_middle_guard_stays_refused
/-- info: 'Minidregg.Theory.Store.Example.normalize_interleaved' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Example.normalize_interleaved
/-- info: 'Minidregg.Theory.Store.Example.normalize_keeps_unwritten_read' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms Example.normalize_keeps_unwritten_read
/-- info: 'Minidregg.Theory.Store.Example.normalize_allocate_free' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Example.normalize_allocate_free

end Minidregg.Theory.Store
