/-
# Compiler.TwistMultisetInvariant -- Nebula Lemma 2 over the sparse typed carriers

`TwistContinuity` (Compiler/SparseAuthenticatedStateLogupBridge.lean) is the
row-only sequential-consistency relation a Twist-style memory argument must
prove.  Until now the tree held only its honest direction
(`TwistContinuity.of_busRelation`); the adversarial direction -- forcing a
*committed* row list into continuity -- was the named residual.

This module lands the missing combinatorial keystone: **Nebula's Lemma 2**
(Arun--Setty, *Nebula: Efficient read-write memory and switchboard circuits for
folding schemes*, following Spice, eprint 2018/907 Lemma C.1), transplanted to
our carriers and proved in BOTH directions:

    TwistContinuity pre rows post
      <->  frame outside the audited domain
        /\ EXISTS read stamps + final stamps with
             IS + WS = RS + FS   (multisets of (address, value, stamp) tuples)

with the stamp discipline `stamp i <= base + i` -- Spice's `t < ts` check with
the global counter realized by list position, which is exactly what the
deployed `BusRelation` clocks are.

Deltas from Nebula's model, stated rather than assumed:

* **Typed disciplines** (ROM/RAM/appendOnly) are orthogonal: `DisciplineRowValid`
  is row-local and enters as a hypothesis, never as part of the multiset
  argument.
* **`free` (absent from Nebula) costs the invariant NOTHING.**  Our cells are
  `Option`-valued (absence is a value), so a `free` is a write whose after-value
  is `none` and an `allocate` is a write consuming `none`; the soundness
  induction below has no `free` case split anywhere.  The Nebula-flagged hazard
  (a freed cell's stale tuple re-entering RS) is refused by the same stamp
  discipline that refuses every stale read; see the
  `stale_read_after_free_refused` tooth.
* Timestamps are **not** read from the `clock` column: `TwistContinuity` is
  clock-blind, so the write stamps are positional (`base + i + 1`) and the read
  stamps are a prover-supplied function priced by the discipline hypothesis.

This is finite combinatorics: no field, no probability, no commitment.  The
Reed--Solomon fingerprint that checks the multiset equation lives in
`Selvage/MultisetFingerprint.lean`, and the join (with the named remaining
cryptographic obligations) in `Assurance/TwistMemoryFingerprintJoin.lean`,
which also roots this module (Compiler.lean carries a sibling lane's
uncommitted work, so the umbrella import lands there).
-/

import Compiler.SparseAuthenticatedStateLogupBridge

namespace Minidregg.Compiler.TwistMultisetInvariant

open Minidregg.Kernel.SparseAuthenticatedState
open Minidregg.Compiler.SparseAuthenticatedStateLogupBridge

set_option autoImplicit false

universe u v w

/-! ## Offline-checking tuples -/

/-- One offline-memory-checking tuple: a typed address, the `Option`-valued
cell content it carries, and a stamp.  This is Spice's `(a, v, t)` with `v`
widened to `Option` so that allocation and free are ordinary writes. -/
structure MemTuple (L : Layout.{u, v, w}) where
  address : Address L
  value : Option (L.Value address.1)
  stamp : Nat

variable {L : Layout.{u, v, w}}

/-- The audit multiset of a store over a finite address domain: one tuple per
audited address, carrying the store's exact content there.  Instantiated at
the pre-state it is Nebula's `IS`; at the post-state it is `FS`. -/
def auditTuples (store : Store L) (stampOf : Address L → Nat)
    (dom : Finset (Address L)) : Multiset (MemTuple L) :=
  dom.val.map fun a => ⟨a, store.lookup a, stampOf a⟩

/-- Nebula's `WS`: the tuple produced by each row, stamped by list position
(`base + i + 1` for the `i`-th row) -- the verifier's counter, not prover data. -/
def writeTuples : Nat → List (BusRow L) → Multiset (MemTuple L)
  | _, [] => 0
  | base, row :: rest =>
      (⟨busAddress row, row.after, base + 1⟩ : MemTuple L) ::ₘ
        writeTuples (base + 1) rest

/-- Nebula's `RS`: the tuple consumed by each row, with a prover-supplied
stamp function (Spice's claimed last-write timestamps). -/
def readTuples : (Nat → Nat) → List (BusRow L) → Multiset (MemTuple L)
  | _, [] => 0
  | stamp, row :: rest =>
      (⟨busAddress row, row.before, stamp 0⟩ : MemTuple L) ::ₘ
        readTuples (fun i => stamp (i + 1)) rest

@[simp] theorem writeTuples_nil (base : Nat) :
    writeTuples (L := L) base [] = 0 := rfl

@[simp] theorem writeTuples_cons (base : Nat) (row : BusRow L)
    (rest : List (BusRow L)) :
    writeTuples base (row :: rest) =
      (⟨busAddress row, row.after, base + 1⟩ : MemTuple L) ::ₘ
        writeTuples (base + 1) rest := rfl

@[simp] theorem readTuples_nil (stamp : Nat → Nat) :
    readTuples (L := L) stamp [] = 0 := rfl

@[simp] theorem readTuples_cons (stamp : Nat → Nat) (row : BusRow L)
    (rest : List (BusRow L)) :
    readTuples stamp (row :: rest) =
      (⟨busAddress row, row.before, stamp 0⟩ : MemTuple L) ::ₘ
        readTuples (fun i => stamp (i + 1)) rest := rfl

/-- **The grand equation** `IS + WS = RS + FS` -- Nebula Lemma 2's multiset
invariant, verbatim, over the typed sparse carriers. -/
def MemoryGrandEquation (base : Nat) (pre post : Store L)
    (istamp fstamp : Address L → Nat) (dom : Finset (Address L))
    (stamp : Nat → Nat) (rows : List (BusRow L)) : Prop :=
  auditTuples pre istamp dom + writeTuples base rows =
    readTuples stamp rows + auditTuples post fstamp dom

/-! ## Elementary structure of the three sides -/

@[simp] theorem card_auditTuples (store : Store L)
    (stampOf : Address L → Nat) (dom : Finset (Address L)) :
    Multiset.card (auditTuples store stampOf dom) = dom.card := by
  unfold auditTuples
  rw [Multiset.card_map]
  rfl

@[simp] theorem card_writeTuples (base : Nat) (rows : List (BusRow L)) :
    Multiset.card (writeTuples base rows) = rows.length := by
  induction rows generalizing base with
  | nil => rfl
  | cons row rest ih => simp [writeTuples_cons, ih]

@[simp] theorem card_readTuples (stamp : Nat → Nat) (rows : List (BusRow L)) :
    Multiset.card (readTuples stamp rows) = rows.length := by
  induction rows generalizing stamp with
  | nil => rfl
  | cons row rest ih => simp [readTuples_cons, ih]

/-- Every produced (write-side) stamp exceeds the base: the verifier's counter
only moves forward.  This is the pigeonhole that forces the head read to match
the audit, never a later write -- the heart of the soundness direction. -/
theorem stamp_lt_of_mem_writeTuples {base : Nat} {rows : List (BusRow L)}
    {t : MemTuple L} (h : t ∈ writeTuples base rows) : base + 1 ≤ t.stamp := by
  induction rows generalizing base with
  | nil => simp [writeTuples] at h
  | cons row rest ih =>
      rw [writeTuples_cons, Multiset.mem_cons] at h
      rcases h with h | h
      · subst h; exact Nat.le_refl _
      · exact Nat.le_of_succ_le (ih h)

/-- Peel the audited tuple of one member address off the audit multiset. -/
theorem auditTuples_cons_erase {store : Store L} {stampOf : Address L → Nat}
    {dom : Finset (Address L)} [DecidableEq L.Namespace]
    [(space : L.Namespace) → DecidableEq (L.Key space)]
    {a : Address L} (ha : a ∈ dom) :
    auditTuples store stampOf dom =
      (⟨a, store.lookup a, stampOf a⟩ : MemTuple L) ::ₘ
        (dom.erase a).val.map fun b => ⟨b, store.lookup b, stampOf b⟩ := by
  unfold auditTuples
  conv_lhs => rw [← Multiset.cons_erase (show a ∈ dom.val from ha)]
  rw [Multiset.map_cons, Finset.erase_val]

/-- One-step audit update: after one row's transition the audit multiset is
the produced write tuple consed onto the untouched remainder of the pre-state
audit.  Shared by both directions of Lemma 2. -/
theorem auditTuples_step {pre middle : Store L} {row : BusRow L}
    {istamp : Address L → Nat} {dom : Finset (Address L)} {n : Nat}
    [DecidableEq L.Namespace]
    [(space : L.Namespace) → DecidableEq (L.Key space)]
    (ha : busAddress row ∈ dom)
    (hafter : middle.lookup (busAddress row) = row.after)
    (hframe : ∀ b : Address L, b ≠ busAddress row →
      middle.lookup b = pre.lookup b) :
    auditTuples middle (Function.update istamp (busAddress row) n) dom =
      (⟨busAddress row, row.after, n⟩ : MemTuple L) ::ₘ
        (dom.erase (busAddress row)).val.map
          fun b => ⟨b, pre.lookup b, istamp b⟩ := by
  rw [auditTuples_cons_erase ha]
  congr 1
  · rw [hafter]
    simp
  · refine Multiset.map_congr rfl fun b hb => ?_
    have hne : b ≠ busAddress row :=
      (Finset.mem_erase.mp (Finset.mem_val.mp hb)).1
    rw [hframe b hne, Function.update_of_ne hne]

/-- Audit equality pins the store on the audited domain. -/
theorem lookup_eq_of_auditTuples_eq {pre post : Store L}
    {istamp fstamp : Address L → Nat} {dom : Finset (Address L)}
    (h : auditTuples pre istamp dom = auditTuples post fstamp dom)
    {a : Address L} (ha : a ∈ dom) : post.lookup a = pre.lookup a := by
  have hmem : (⟨a, pre.lookup a, istamp a⟩ : MemTuple L) ∈
      auditTuples post fstamp dom := by
    rw [← h]
    exact Multiset.mem_map_of_mem _ (show a ∈ dom.val from ha)
  obtain ⟨b, _, heq⟩ := Multiset.mem_map.mp hmem
  simp only [MemTuple.mk.injEq] at heq
  obtain ⟨rfl, hv, -⟩ := heq
  exact eq_of_heq hv

/-! ## Lemma 2, soundness direction (the adversarial keystone)

Spice C.1's argument as one list induction: the head row's read stamp is
`<= base` while every write stamp is `>= base + 1`, so the head read tuple can
only match the audit tuple at its own address -- pinning `row.before` to the
actual store content.  Cancel the matched pair, absorb the head's write tuple
into the audit of the updated store, recurse. -/

/-- **Adversarial direction.** A row list whose grand equation holds under the
stamp discipline, whose rows have the discipline shapes, and whose addresses
are covered by an audit domain outside of which the claimed post-state stands
still, is sequentially consistent: `TwistContinuity` holds.  No hypothesis
mentions how `rows` was produced -- this is the statement a committed bus is
forced into. -/
theorem twistContinuity_of_grandEquation
    [DecidableEq L.Namespace]
    [(space : L.Namespace) → DecidableEq (L.Key space)]
    {base : Nat} {pre post : Store L} {istamp fstamp : Address L → Nat}
    {dom : Finset (Address L)} {stamp : Nat → Nat} {rows : List (BusRow L)}
    (disc : ∀ row ∈ rows, DisciplineRowValid row)
    (addr : ∀ row ∈ rows, busAddress row ∈ dom)
    (outside : ∀ a : Address L, a ∉ dom → post.lookup a = pre.lookup a)
    (stampDisc : ∀ i < rows.length, stamp i ≤ base + i)
    (eq : MemoryGrandEquation base pre post istamp fstamp dom stamp rows) :
    TwistContinuity pre rows post := by
  induction rows generalizing base pre istamp stamp with
  | nil =>
      unfold MemoryGrandEquation at eq
      rw [writeTuples_nil, readTuples_nil, add_zero, zero_add] at eq
      have hstore : pre = post := by
        apply Store.ext
        intro space key
        by_cases hmem : (⟨space, key⟩ : Address L) ∈ dom
        · exact (lookup_eq_of_auditTuples_eq eq hmem).symm
        · exact (outside ⟨space, key⟩ hmem).symm
      cases hstore
      exact TwistContinuity.nil _
  | cons row rest ih =>
      unfold MemoryGrandEquation at eq
      have ha : busAddress row ∈ dom := addr row List.mem_cons_self
      have hstamp0 : stamp 0 ≤ base := by
        simpa using stampDisc 0 (by simp)
      -- the head read tuple is in the left side of the equation, and its
      -- stamp forbids the write side
      have hin : (⟨busAddress row, row.before, stamp 0⟩ : MemTuple L) ∈
          auditTuples pre istamp dom := by
        have hr : (⟨busAddress row, row.before, stamp 0⟩ : MemTuple L) ∈
            auditTuples pre istamp dom + writeTuples base (row :: rest) := by
          rw [eq, readTuples_cons]
          exact Multiset.mem_add.mpr (Or.inl (Multiset.mem_cons_self _ _))
        rcases Multiset.mem_add.mp hr with hin | hin
        · exact hin
        · exact absurd
            (show base + 1 ≤ stamp 0 from stamp_lt_of_mem_writeTuples hin)
            (by omega)
      -- so it matches the audit tuple at its own address
      obtain ⟨b, _, heq⟩ := Multiset.mem_map.mp hin
      simp only [MemTuple.mk.injEq] at heq
      obtain ⟨hb, hv, hs⟩ := heq
      subst hb
      have hbefore : pre.lookup (busAddress row) = row.before := eq_of_heq hv
      -- the one-cell transition, with its frame
      have htrans : CellTransition pre
          (pre.set row.space row.key row.after) row :=
        ⟨hbefore, Store.set_eq pre row.space row.key row.after,
          fun space key hne =>
            Store.set_ne pre row.space row.key row.after space key hne⟩
      -- rearrange the equation into the tail's grand equation
      have hstep : auditTuples (pre.set row.space row.key row.after)
          (Function.update istamp (busAddress row) (base + 1)) dom =
          (⟨busAddress row, row.after, base + 1⟩ : MemTuple L) ::ₘ
            (dom.erase (busAddress row)).val.map
              fun b => ⟨b, pre.lookup b, istamp b⟩ :=
        auditTuples_step ha
          (Store.set_eq pre row.space row.key row.after)
          (fun b hne => Store.set_ne pre row.space row.key row.after b.1 b.2
            hne)
      rw [auditTuples_cons_erase (store := pre)
            (stampOf := istamp) ha, writeTuples_cons, readTuples_cons] at eq
      rw [Multiset.cons_add, Multiset.add_cons, Multiset.cons_add] at eq
      rw [show (⟨busAddress row, pre.lookup (busAddress row),
            istamp (busAddress row)⟩ : MemTuple L) =
          ⟨busAddress row, row.before, stamp 0⟩ by rw [hbefore, hs]] at eq
      have eq' := (Multiset.cons_inj_right _).mp eq
      -- recurse on the tail at the updated store
      refine TwistContinuity.cons (disc row List.mem_cons_self) htrans
        (ih (base := base + 1)
          (pre := pre.set row.space row.key row.after)
          (istamp := Function.update istamp (busAddress row) (base + 1))
          (stamp := fun i => stamp (i + 1))
          (fun r hr => disc r (List.mem_cons_of_mem _ hr))
          (fun r hr => addr r (List.mem_cons_of_mem _ hr))
          (fun a hnot => ?_)
          (fun i hi => by
            have hd := stampDisc (i + 1)
              (by simpa using Nat.succ_lt_succ hi)
            show stamp (i + 1) ≤ base + 1 + i
            omega)
          ?_)
      · rw [outside a hnot]
        refine (Store.set_ne pre row.space row.key row.after a.1 a.2 ?_).symm
        intro h
        exact hnot (show a ∈ dom from by
          rw [show a = busAddress row from h]; exact ha)
      · unfold MemoryGrandEquation
        rw [hstep, Multiset.cons_add]
        exact eq'

/-! ## Lemma 2, completeness direction (the honest prover's stamps) -/

/-- **Honest direction.**  A sequentially consistent row list admits read
stamps (the actual last-write positions) and final stamps making the grand
equation hold.  Together with `TwistContinuity.of_busRelation` this says every
accepted semantic execution passes the offline check -- Lemma 2's "if reads
are consistent then such an FS exists". -/
theorem grandEquation_of_twistContinuity
    [DecidableEq L.Namespace]
    [(space : L.Namespace) → DecidableEq (L.Key space)]
    {pre post : Store L} {rows : List (BusRow L)}
    (tc : TwistContinuity pre rows post) :
    ∀ {base : Nat} {istamp : Address L → Nat} {dom : Finset (Address L)},
      (∀ row ∈ rows, busAddress row ∈ dom) →
      (∀ a ∈ dom, istamp a ≤ base) →
      ∃ stamp fstamp, (∀ i < rows.length, stamp i ≤ base + i) ∧
        MemoryGrandEquation base pre post istamp fstamp dom stamp rows := by
  induction tc with
  | nil store =>
      intro base istamp dom _ _
      refine ⟨fun _ => 0, istamp, fun i _ => Nat.zero_le _, ?_⟩
      unfold MemoryGrandEquation
      rw [writeTuples_nil, readTuples_nil, add_zero, zero_add]
  | @cons pre middle post row rest _hdisc htrans tail ih =>
      intro base istamp dom addr istampLe
      have ha : busAddress row ∈ dom := addr row List.mem_cons_self
      obtain ⟨stamp', fstamp, hdisc', heq'⟩ :=
        ih (base := base + 1)
          (istamp := Function.update istamp (busAddress row) (base + 1))
          (fun r hr => addr r (List.mem_cons_of_mem _ hr))
          (fun a hmem => by
            by_cases hab : a = busAddress row
            · subst hab; simp
            · rw [Function.update_of_ne hab]
              exact Nat.le_succ_of_le (istampLe a hmem))
      refine ⟨fun i => match i with
          | 0 => istamp (busAddress row)
          | i + 1 => stamp' i,
        fstamp, ?_, ?_⟩
      · intro i hi
        match i with
        | 0 => simpa using istampLe _ ha
        | i + 1 =>
            simpa [Nat.add_assoc, Nat.add_comm 1 i] using
              hdisc' i (by simpa using Nat.lt_of_succ_lt_succ hi)
      · have hstep : auditTuples middle
            (Function.update istamp (busAddress row) (base + 1)) dom =
            (⟨busAddress row, row.after, base + 1⟩ : MemTuple L) ::ₘ
              (dom.erase (busAddress row)).val.map
                fun b => ⟨b, pre.lookup b, istamp b⟩ :=
          auditTuples_step ha htrans.after_exact
            (fun b hne => htrans.frame b.1 b.2 hne)
        have hbe : pre.lookup (busAddress row) = row.before :=
          htrans.before_exact
        unfold MemoryGrandEquation at heq' ⊢
        rw [hstep, Multiset.cons_add] at heq'
        rw [auditTuples_cons_erase (store := pre) (stampOf := istamp) ha,
          writeTuples_cons, readTuples_cons]
        rw [Multiset.cons_add, Multiset.add_cons, Multiset.cons_add]
        rw [show (⟨busAddress row, pre.lookup (busAddress row),
              istamp (busAddress row)⟩ : MemTuple L) =
            ⟨busAddress row, row.before,
              istamp (busAddress row)⟩ by rw [hbe]]
        exact congrArg _ heq'

/-- The whole-trace frame of `TwistContinuity`: untouched addresses stand
still.  (The per-step frame, folded.) -/
theorem _root_.Minidregg.Compiler.SparseAuthenticatedStateLogupBridge.TwistContinuity.lookup_frame
    {pre post : Store L}
    {rows : List (BusRow L)} (tc : TwistContinuity pre rows post)
    {a : Address L} (huntouched : ∀ row ∈ rows, busAddress row ≠ a) :
    post.lookup a = pre.lookup a := by
  induction tc with
  | nil => rfl
  | @cons pre middle post row rest _ htrans _ ih =>
      rw [ih fun r hr => huntouched r (List.mem_cons_of_mem _ hr)]
      obtain ⟨space, key⟩ := a
      exact htrans.frame space key
        (Ne.symm (huntouched row List.mem_cons_self))

/-! ## The biconditional (Nebula Lemma 2, both directions, packaged) -/

/-- **Lemma 2.**  Under row-local discipline shapes and an audit domain
covering the accessed addresses, sequential consistency IS the multiset
invariant: `TwistContinuity` holds iff the claimed post-state stands still
outside the domain and some read/final stamps satisfy the stamp discipline
and the grand equation.  `DisciplineRowValid` stays a hypothesis because it is
checked row-locally by the shape constraints, never by the multiset argument. -/
theorem twistContinuity_iff_grandEquation
    [DecidableEq L.Namespace]
    [(space : L.Namespace) → DecidableEq (L.Key space)]
    {pre post : Store L} {dom : Finset (Address L)} {rows : List (BusRow L)}
    (disc : ∀ row ∈ rows, DisciplineRowValid row)
    (addr : ∀ row ∈ rows, busAddress row ∈ dom) :
    TwistContinuity pre rows post ↔
      ((∀ a : Address L, a ∉ dom → post.lookup a = pre.lookup a) ∧
        ∃ stamp fstamp, (∀ i < rows.length, stamp i ≤ i) ∧
          MemoryGrandEquation 0 pre post (fun _ => 0) fstamp dom stamp rows) := by
  constructor
  · intro tc
    constructor
    · intro a hnot
      exact tc.lookup_frame fun row hrow hba => hnot (hba ▸ addr row hrow)
    · obtain ⟨stamp, fstamp, hdisc, heq⟩ :=
        grandEquation_of_twistContinuity tc (base := 0)
          (istamp := fun _ => 0) addr (fun _ _ => Nat.le_refl 0)
      exact ⟨stamp, fstamp, fun i hi => by simpa using hdisc i hi, heq⟩
  · rintro ⟨outside, stamp, fstamp, hdisc, heq⟩
    exact twistContinuity_of_grandEquation disc addr outside
      (fun i hi => by simpa using hdisc i hi) heq

/-- Contrapositive packaging of the soundness direction, in the shape the
fingerprint layer consumes: a non-continuous trace has NO stamps satisfying
the invariant -- for every prover-supplied read/final stamp choice the two
tuple multisets genuinely differ. -/
theorem grandEquation_refuted_of_not_twistContinuity
    [DecidableEq L.Namespace]
    [(space : L.Namespace) → DecidableEq (L.Key space)]
    {pre post : Store L} {dom : Finset (Address L)} {rows : List (BusRow L)}
    (disc : ∀ row ∈ rows, DisciplineRowValid row)
    (addr : ∀ row ∈ rows, busAddress row ∈ dom)
    (outside : ∀ a : Address L, a ∉ dom → post.lookup a = pre.lookup a)
    (htc : ¬ TwistContinuity pre rows post)
    {base : Nat} {istamp fstamp : Address L → Nat} {stamp : Nat → Nat}
    (stampDisc : ∀ i < rows.length, stamp i ≤ base + i) :
    auditTuples pre istamp dom + writeTuples base rows ≠
      readTuples stamp rows + auditTuples post fstamp dom :=
  fun heq => htc
    (twistContinuity_of_grandEquation disc addr outside stampDisc heq)

/-! ## The bridge consumer: accepted executions pass the offline check -/

/-- Every exact bus claim of an accepted sparse execution admits stamps
satisfying the grand equation over any covering audit domain: the honest half
of the offline memory check, derived (never re-proved) from the bridge's
`TwistContinuity.of_busRelation`. -/
theorem _root_.Minidregg.Compiler.SparseAuthenticatedStateLogupBridge.ExactBusClaim.grandEquation
    {L : Layout.{u, v, w}} {Root : Type}
    [DecidableEq L.Namespace]
    [(space : L.Namespace) → DecidableEq (L.Key space)]
    {materializer : Materializer L Root}
    {pre : Materialized materializer} {operations : List (Op L)}
    {accepted : AcceptedExecution materializer pre operations}
    (bus : ExactBusClaim accepted) {dom : Finset (Address L)}
    (addr : ∀ row ∈ bus.rows, busAddress row ∈ dom) :
    ∃ stamp fstamp, (∀ i < bus.rows.length, stamp i ≤ i) ∧
      MemoryGrandEquation 0 pre.logical accepted.post.logical
        (fun _ => 0) fstamp dom stamp bus.rows := by
  obtain ⟨stamp, fstamp, hdisc, heq⟩ :=
    grandEquation_of_twistContinuity
      (TwistContinuity.of_busRelation bus.rows_semantic) (base := 0)
      (istamp := fun _ => 0) addr (fun _ _ => Nat.le_refl 0)
  exact ⟨stamp, fstamp, fun i hi => by simpa using hdisc i hi, heq⟩

/-! ## Teeth (over the kernel's own example layout)

Three poles, all constructive:
1. the value-swap cycle -- STAMPLESS accounting is satisfied, the stamped
   invariant refuses (stamps are load-bearing, Nebula's timestamp discipline
   is not decoration);
2. a stale read after `free` -- the Nebula-model gap exhibited CLOSED;
3. an honest RAM trace including a `free` -- accepted with explicit stamps
   (premise inhabitation: the equation is satisfiable, not vacuously refused).
-/

namespace Teeth

open Minidregg.Kernel.SparseAuthenticatedState.Example

/-- Strip stamps: the accounting a stampless checker sees. -/
def stripStamps (m : Multiset (MemTuple layout)) : Multiset (MemTuple layout) :=
  m.map fun t => ⟨t.address, t.value, 0⟩

/-- The one heap namespace, at the layout's typed carrier. -/
def heapSpace : layout.Namespace := Namespace.heap

def heapKey : layout.Key heapSpace := (7 : Nat)

def heapVal (n : Nat) : layout.Value heapSpace := n

/-- One RAM cell holding `some 0`. -/
def cyclePre : Store layout :=
  (0 : Store layout).set heapSpace heapKey (some (heapVal 0))

/-- The value-swap cycle: write `1 -> 2` then `2 -> 1` at a cell that actually
holds `0`.  No read ever returned the last write, yet every VALUE that is
consumed is also produced. -/
def cycleRows : List (BusRow layout) :=
  [⟨0, .write, heapSpace, heapKey, some (heapVal 1), some (heapVal 2)⟩,
   ⟨1, .write, heapSpace, heapKey, some (heapVal 2), some (heapVal 1)⟩]

def heapCell : Address layout := ⟨heapSpace, heapKey⟩

def cycleDom : Finset (Address layout) := {heapCell}

theorem cycleRows_disc : ∀ row ∈ cycleRows, DisciplineRowValid row := by
  intro row hrow
  simp only [cycleRows, List.mem_cons, List.not_mem_nil, or_false] at hrow
  rcases hrow with rfl | rfl
  · exact .ramWrite 0 heapSpace heapKey (heapVal 1) (heapVal 2) rfl
  · exact .ramWrite 1 heapSpace heapKey (heapVal 2) (heapVal 1) rfl

theorem cycleRows_addr : ∀ row ∈ cycleRows, busAddress row ∈ cycleDom := by
  intro row hrow
  simp only [cycleRows, List.mem_cons, List.not_mem_nil, or_false] at hrow
  rcases hrow with rfl | rfl <;> exact Finset.mem_singleton_self _

/-- **Tooth 1a: the stampless checker is FOOLED.**  With every stamp erased,
`IS + WS = RS + FS` holds for the swap cycle at `post = pre` -- value-only
multiset accounting cannot see that the cycle reads values written in its own
future. -/
theorem stampless_accounting_fooled :
    stripStamps (auditTuples cyclePre (fun _ => 0) cycleDom +
        writeTuples 0 cycleRows) =
      stripStamps (readTuples (fun _ => 0) cycleRows +
        auditTuples cyclePre (fun _ => 0) cycleDom) := by
  simp only [cycleRows, cycleDom, auditTuples, stripStamps, busAddress,
    heapCell, writeTuples_cons, writeTuples_nil, readTuples_cons,
    readTuples_nil, Finset.singleton_val, Multiset.map_singleton,
    Multiset.singleton_add, Multiset.cons_add, Multiset.add_cons,
    Multiset.map_cons, Multiset.cons_zero]
  -- LHS: w₁(some 2) :: audit(some 0) :: w₂(some 1);
  -- RHS: r₁(some 1) :: r₂(some 2) :: audit(some 0) -- same multiset, reordered
  conv_rhs => rw [Multiset.cons_swap]
  exact congrArg _ (Multiset.cons_swap _ _ _)

/-- The cycle is not sequentially consistent: its first row claims to consume
`some 1` from a cell holding `some 0`. -/
theorem cycle_not_continuous :
    ¬ TwistContinuity cyclePre cycleRows cyclePre := by
  intro h
  simp only [cycleRows] at h
  cases h with
  | cons _ htrans _ =>
      have hbefore := htrans.before_exact
      have hcell : cyclePre heapSpace heapKey = some (heapVal 0) :=
        Store.set_eq (0 : Store layout) heapSpace heapKey (some (heapVal 0))
      rw [hcell] at hbefore
      exact absurd hbefore (by decide)

/-- **Tooth 1b: stamps are load-bearing.**  The SAME cycle is refused by the
stamped invariant for EVERY prover stamp choice -- Nebula's timestamp
discipline is exactly what separates this from tooth 1a. -/
theorem cycle_refused_with_stamps
    {istamp fstamp : Address layout → Nat} {stamp : Nat → Nat}
    (stampDisc : ∀ i < cycleRows.length, stamp i ≤ i) :
    auditTuples cyclePre istamp cycleDom + writeTuples 0 cycleRows ≠
      readTuples stamp cycleRows + auditTuples cyclePre fstamp cycleDom :=
  grandEquation_refuted_of_not_twistContinuity
    cycleRows_disc cycleRows_addr (fun _ _ => rfl) cycle_not_continuous
    (base := 0) (fun i hi => by simpa using stampDisc i hi)

/-- Allocate, free, then read the freed value: the stale tuple a Nebula-style
argument must not let re-enter `RS`. -/
def staleRows : List (BusRow layout) :=
  [⟨0, .allocate, heapSpace, heapKey, none, some (heapVal 42)⟩,
   ⟨1, .free, heapSpace, heapKey, some (heapVal 42), none⟩,
   ⟨2, .read, heapSpace, heapKey, some (heapVal 42), some (heapVal 42)⟩]

theorem staleRows_disc : ∀ row ∈ staleRows, DisciplineRowValid row := by
  intro row hrow
  simp only [staleRows, List.mem_cons, List.not_mem_nil, or_false] at hrow
  rcases hrow with rfl | rfl | rfl
  · exact .ramAllocate 0 heapSpace heapKey (heapVal 42) rfl
  · exact .ramFree 1 heapSpace heapKey (heapVal 42) rfl
  · exact .read 2 heapSpace heapKey (some (heapVal 42))

theorem staleRows_addr : ∀ row ∈ staleRows, busAddress row ∈ cycleDom := by
  intro row hrow
  simp only [staleRows, List.mem_cons, List.not_mem_nil, or_false] at hrow
  rcases hrow with rfl | rfl | rfl <;> exact Finset.mem_singleton_self _

theorem stale_not_continuous :
    ¬ TwistContinuity (0 : Store layout) staleRows (0 : Store layout) := by
  intro h
  simp only [staleRows] at h
  cases h with
  | cons _ _ tail₁ =>
      cases tail₁ with
      | cons _ htrans₂ tail₂ =>
          cases tail₂ with
          | cons _ htrans₃ _ =>
              have h₂ := htrans₂.after_exact
              have h₃ := htrans₃.before_exact
              rw [h₂] at h₃
              simp at h₃

/-- **Tooth 2: the `free` gap, exhibited closed.**  The stale read of a freed
cell is refused for EVERY stamp choice: under `Option`-valued cells the free
consumed the tuple `(a, some 42, _)` itself, so the multiset equation has no
copy left for the read to consume. -/
theorem stale_read_after_free_refused
    {istamp fstamp : Address layout → Nat} {stamp : Nat → Nat}
    (stampDisc : ∀ i < staleRows.length, stamp i ≤ i) :
    auditTuples (0 : Store layout) istamp cycleDom +
        writeTuples 0 staleRows ≠
      readTuples stamp staleRows +
        auditTuples (0 : Store layout) fstamp cycleDom :=
  grandEquation_refuted_of_not_twistContinuity
    staleRows_disc staleRows_addr (fun _ _ => rfl) stale_not_continuous
    (base := 0) (fun i hi => by simpa using stampDisc i hi)

/-- An honest RAM lifetime: allocate, overwrite, read back, free. -/
def honestOps : List (Op layout) :=
  [Op.allocate heapSpace heapKey (heapVal 42),
   Op.write heapSpace heapKey (heapVal 42) (heapVal 43),
   Op.read heapSpace heapKey (some (heapVal 43)),
   Op.free heapSpace heapKey (heapVal 43)]

theorem honestOps_valid :
    Trace.ValidFrom (0 : Store layout) honestOps :=
  ⟨⟨by decide, rfl⟩,
   ⟨rfl, Store.set_eq _ _ _ _⟩,
   Store.set_eq _ _ _ _,
   ⟨rfl, Store.set_eq _ _ _ _⟩,
   trivial⟩

theorem honestRows_addr :
    ∀ row ∈ Trace.busRows (0 : Store layout) honestOps,
      busAddress row ∈ cycleDom := by
  intro row hrow
  simp only [honestOps, Trace.busRows, Trace.busRowsFrom, Op.busRow,
    List.mem_cons, List.not_mem_nil, or_false] at hrow
  rcases hrow with rfl | rfl | rfl | rfl <;> exact Finset.mem_singleton_self _

/-- **Tooth 3: premise inhabitation.**  The honest lifetime -- including its
`free` -- passes the offline check with explicit stamps; the invariant is
satisfiable, so the refusals above are refusals, not vacuity. -/
theorem honest_trace_accepted :
    ∃ stamp fstamp,
      (∀ i < (Trace.busRows (0 : Store layout) honestOps).length,
        stamp i ≤ i) ∧
      MemoryGrandEquation 0 (0 : Store layout)
        (Trace.run (0 : Store layout) honestOps) (fun _ => 0) fstamp cycleDom
        stamp (Trace.busRows (0 : Store layout) honestOps) := by
  have tc : TwistContinuity (0 : Store layout)
      (Trace.busRows (0 : Store layout) honestOps)
      (Trace.run (0 : Store layout) honestOps) :=
    TwistContinuity.of_busRelation
      (Trace.busRelation_of_valid 0 (0 : Store layout) honestOps
        honestOps_valid)
  obtain ⟨stamp, fstamp, hdisc, heq⟩ :=
    grandEquation_of_twistContinuity tc (base := 0) (istamp := fun _ => 0)
      honestRows_addr (fun _ _ => Nat.le_refl 0)
  exact ⟨stamp, fstamp, fun i hi => by simpa using hdisc i hi, heq⟩

end Teeth

/-! ## Axiom pins -/

/-- info: 'Minidregg.Compiler.TwistMultisetInvariant.twistContinuity_of_grandEquation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms twistContinuity_of_grandEquation
/-- info: 'Minidregg.Compiler.TwistMultisetInvariant.grandEquation_of_twistContinuity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms grandEquation_of_twistContinuity
/-- info: 'Minidregg.Compiler.TwistMultisetInvariant.twistContinuity_iff_grandEquation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms twistContinuity_iff_grandEquation
/-- info: 'Minidregg.Compiler.SparseAuthenticatedStateLogupBridge.ExactBusClaim.grandEquation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Compiler.SparseAuthenticatedStateLogupBridge.ExactBusClaim.grandEquation
/-- info: 'Minidregg.Compiler.TwistMultisetInvariant.Teeth.stampless_accounting_fooled' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Teeth.stampless_accounting_fooled
/-- info: 'Minidregg.Compiler.TwistMultisetInvariant.Teeth.cycle_refused_with_stamps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Teeth.cycle_refused_with_stamps
/-- info: 'Minidregg.Compiler.TwistMultisetInvariant.Teeth.stale_read_after_free_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Teeth.stale_read_after_free_refused
/-- info: 'Minidregg.Compiler.TwistMultisetInvariant.Teeth.honest_trace_accepted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Teeth.honest_trace_accepted

end Minidregg.Compiler.TwistMultisetInvariant
