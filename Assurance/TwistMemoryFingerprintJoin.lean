/-
# Assurance.TwistMemoryFingerprintJoin -- the offline memory check, priced

The cross-boundary join (this directory is the tree's one lawful home for it):
the kernel-side multiset invariant of `Compiler/TwistMultisetInvariant.lean`
meets the Reed--Solomon fingerprint of `Selvage/MultisetFingerprint.lean`.
Together they are Nebula's Lemma 2 + Corollary 1 over our carriers:

* **Adversarial pole** (`nonContinuous_fingerprint_accept_le`): a committed bus
  that is NOT sequentially consistent passes the fingerprinted offline check on
  at most a `(|dom| + |rows|) * (k+1) / |F|` fraction of challenge pairs --
  for every prover-supplied read/final stamp choice.  This is the residual the
  bridge names ("the semantic statement a Twist-style argument must prove"),
  discharged down to the named cryptographic floor below.
* **Honest pole** (`exactBusClaim_fingerprint_accepted`): every accepted sparse
  execution's exact bus admits stamps whose fingerprints agree at EVERY
  challenge pair -- completeness end to end, consuming the bridge's
  `ExactBusClaim` across the module boundary.

## Residual [TWIST-FP-BIND] -- what this join does NOT discharge, by name

The two theorems condition on committed data and honest scheduling.  Turning
them into a deployed memory argument requires exactly:

1. **Binding**: the tuple multisets the products range over must be the
   committed row/stamp columns -- the `CommitmentBindingCR` premise carried by
   `AcceptedLogupRun` (Compiler/AuthenticatedColumnLogupBridge.lean).
2. **Schedule**: `γ = (γ₁, γ₂)` drawn only after those commitments -- the
   roots-before-challenge discipline of the same accepted-run object
   (`TerminalAttestation`); `fingerprint_forged_after_challenge` is the tooth
   showing the reversed order loses everything.
3. **Range checks realizing `Set.InjOn vec`**: the encoding is injective on
   range-checked committed tuples, never globally (a `Nat`-stamped tuple space
   cannot inject into bounded-degree polynomials -- the hypothesis is honest).
4. **Row-shape checks realizing `DisciplineRowValid`** (ROM read-only,
   append-only fresh allocation, RAM write/alloc/free), row-local constraints.
5. **The audit frame**: `dom` covering the accessed addresses with the claimed
   post-state framed outside it, realized against the exact
   `bus.preRoot`/`bus.postRoot` state roots.
6. **Positional write stamps**: `writeTuples` stamps by list position (the
   verifier's counter).  The circuit must DERIVE each write stamp from the row
   index; a write stamp read from a prover-committed column reopens exactly
   the stale-read hole the stamp discipline closes.

None of these is absorbed here; each names the constraint family or accepted
object that must supply it.
-/

import Compiler.TwistMultisetInvariant
import Selvage.MultisetFingerprint

namespace Minidregg.Assurance.TwistMemoryFingerprintJoin

open Minidregg.Kernel.SparseAuthenticatedState
open Minidregg.Compiler.SparseAuthenticatedStateLogupBridge
open Minidregg.Compiler.TwistMultisetInvariant
open Minidregg.Selvage

set_option autoImplicit false

universe u v w

variable {L : Layout.{u, v, w}}
    [DecidableEq L.Namespace]
    [(space : L.Namespace) → DecidableEq (L.Key space)]
    {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- **The Twist memory-soundness join (adversarial pole).**  A row list that
is not sequentially consistent -- with row shapes, covered addresses, the
outside frame, and the stamp discipline all granted -- passes the
Reed--Solomon fingerprint check on at most a
`(|dom| + |rows|)·(k+1)/|F|` fraction of challenge pairs, for ANY
prover-supplied read/final stamps.  Quantifier order is the content: rows and
stamps are fixed before the uniform draw. -/
theorem nonContinuous_fingerprint_accept_le
    {pre post : Store L} {dom : Finset (Address L)} {rows : List (BusRow L)}
    (vec : MemTuple L → Polynomial F) {k : ℕ}
    (hdeg : ∀ t, (vec t).natDegree ≤ k)
    {istamp fstamp : Address L → Nat} {stamp : Nat → Nat}
    (hinj : Set.InjOn vec {t |
      t ∈ auditTuples pre istamp dom + writeTuples 0 rows ∨
      t ∈ readTuples stamp rows + auditTuples post fstamp dom})
    (disc : ∀ row ∈ rows, DisciplineRowValid row)
    (addr : ∀ row ∈ rows, busAddress row ∈ dom)
    (outside : ∀ a : Address L, a ∉ dom → post.lookup a = pre.lookup a)
    (stampDisc : ∀ i < rows.length, stamp i ≤ i)
    (htc : ¬ TwistContinuity pre rows post) :
    uniformProb (F × F) (fun γ =>
      fingerprintProd vec γ
        (auditTuples pre istamp dom + writeTuples 0 rows) =
      fingerprintProd vec γ
        (readTuples stamp rows + auditTuples post fstamp dom)) ≤
      (((dom.card + rows.length) * (k + 1) : ℕ) : ℝ) / Fintype.card F := by
  have h := fingerprint_multiset_sound_of_injOn vec hdeg hinj
    (grandEquation_refuted_of_not_twistContinuity disc addr outside htc
      (base := 0) (istamp := istamp) (fstamp := fstamp)
      (fun i hi => by simpa using stampDisc i hi))
  have hc : max
      (Multiset.card (auditTuples pre istamp dom + writeTuples 0 rows))
      (Multiset.card (readTuples stamp rows + auditTuples post fstamp dom)) =
      dom.card + rows.length := by
    simp [Nat.add_comm rows.length dom.card]
  rwa [hc] at h

omit [Fintype F] [DecidableEq F] in
/-- **The honest pole.**  Every accepted execution's exact bus admits stamps
whose fingerprints agree at EVERY challenge pair: the bridge's
`ExactBusClaim` (consumed across the Compiler/Assurance boundary) composed
with Lemma 2's completeness and the fingerprint's completeness. -/
theorem exactBusClaim_fingerprint_accepted
    {Root : Type} {materializer : Materializer L Root}
    {pre : Materialized materializer} {operations : List (Op L)}
    {accepted : AcceptedExecution materializer pre operations}
    (bus : ExactBusClaim accepted) {dom : Finset (Address L)}
    (addr : ∀ row ∈ bus.rows, busAddress row ∈ dom)
    (vec : MemTuple L → Polynomial F) :
    ∃ stamp fstamp, (∀ i < bus.rows.length, stamp i ≤ i) ∧
      ∀ γ : F × F,
        fingerprintProd vec γ
          (auditTuples pre.logical (fun _ => 0) dom +
            writeTuples 0 bus.rows) =
        fingerprintProd vec γ
          (readTuples stamp bus.rows +
            auditTuples accepted.post.logical fstamp dom) := by
  obtain ⟨stamp, fstamp, hdisc, heq⟩ := ExactBusClaim.grandEquation bus addr
  exact ⟨stamp, fstamp, hdisc,
    fun γ => fingerprint_multiset_complete vec γ heq⟩

/-! ## Premise inhabitation: the adversarial join fires on a concrete instance

Every hypothesis of `nonContinuous_fingerprint_accept_le` is jointly
inhabited on a real instance -- one stale read against an empty store -- so
the composed theorem is a constraint, never a vacuously conditioned one.
In particular `Set.InjOn` is exhibited on the run's members with a bounded
Nebula-style `(value, stamp)` encoding over F₅, which global injectivity
could never supply. -/

namespace Teeth

open Minidregg.Kernel.SparseAuthenticatedState.Example
open Minidregg.Compiler.TwistMultisetInvariant.Teeth
open Minidregg.Selvage.MultisetFingerprintExample

/-- One stale read against the empty store: the row claims to observe
`some 1` where nothing was ever written. -/
def badRows : List (BusRow layout) :=
  [⟨0, .read, heapSpace, heapKey, some (heapVal 1), some (heapVal 1)⟩]

theorem badRows_disc : ∀ row ∈ badRows, DisciplineRowValid row := by
  intro row hrow
  simp only [badRows, List.mem_cons, List.not_mem_nil, or_false] at hrow
  subst hrow
  exact .read 0 heapSpace heapKey (some (heapVal 1))

theorem badRows_addr : ∀ row ∈ badRows, busAddress row ∈ cycleDom := by
  intro row hrow
  simp only [badRows, List.mem_cons, List.not_mem_nil, or_false] at hrow
  subst hrow
  exact Finset.mem_singleton_self _

theorem badRows_not_continuous :
    ¬ TwistContinuity (0 : Store layout) badRows (0 : Store layout) := by
  intro h
  simp only [badRows] at h
  cases h with
  | cons _ htrans _ =>
      have hbefore := htrans.before_exact
      simp at hbefore

/-- Bounded Option-value encoding: absence is `0`, `some v` is `v + 1`. -/
def valueEnc : Option Nat → ZMod 5
  | none => 0
  | some v => (v : ZMod 5) + 1

/-- The Nebula-style tuple encoding `(value, stamp) ↦ value + stamp·X`,
factored through the injective `pairVec`. -/
noncomputable def tupleVec (t : MemTuple layout) : Polynomial (ZMod 5) :=
  pairVec (valueEnc (t.value : Option Nat), (t.stamp : ZMod 5))

theorem tupleVec_natDegree_le : ∀ t, (tupleVec t).natDegree ≤ 1 :=
  fun _ => pairVec_natDegree_le _

theorem tupleVec_injOn :
    Set.InjOn tupleVec {t |
      t ∈ auditTuples (0 : Store layout) (fun _ => 0) cycleDom +
        writeTuples 0 badRows ∨
      t ∈ readTuples (fun _ => 0) badRows +
        auditTuples (0 : Store layout) (fun _ => 0) cycleDom} := by
  intro t ht u hu heq
  have hg : (valueEnc (t.value : Option Nat), ((t.stamp : ZMod 5))) =
      (valueEnc (u.value : Option Nat), ((u.stamp : ZMod 5))) :=
    pairVec_injective heq
  simp only [badRows, cycleDom, auditTuples, Set.mem_setOf_eq,
    writeTuples_cons, writeTuples_nil, readTuples_cons, readTuples_nil,
    Finset.singleton_val, Multiset.map_singleton, Multiset.singleton_add,
    Multiset.cons_zero, Multiset.mem_cons, Multiset.mem_singleton] at ht hu
  rcases ht with (rfl | rfl) | (rfl | rfl) <;>
    rcases hu with (rfl | rfl) | (rfl | rfl) <;>
      first
        | rfl
        | (exfalso; revert hg; decide)

/-- **The join fires.**  All premises inhabited at once: the stale read is
accepted on at most `(|dom| + |rows|)·(k+1)/|F| = 4/5` of challenge pairs. -/
theorem bad_read_priced :
    uniformProb (ZMod 5 × ZMod 5) (fun γ =>
      fingerprintProd tupleVec γ
        (auditTuples (0 : Store layout) (fun _ => 0) cycleDom +
          writeTuples 0 badRows) =
      fingerprintProd tupleVec γ
        (readTuples (fun _ => 0) badRows +
          auditTuples (0 : Store layout) (fun _ => 0) cycleDom)) ≤
      (((cycleDom.card + badRows.length) * (1 + 1) : ℕ) : ℝ) /
        Fintype.card (ZMod 5) :=
  nonContinuous_fingerprint_accept_le tupleVec (k := 1)
    tupleVec_natDegree_le tupleVec_injOn badRows_disc badRows_addr
    (fun _ _ => rfl) (fun _ _ => Nat.zero_le _) badRows_not_continuous

/-- The concrete bound constrains: `4/5 < 1`. -/
theorem bad_read_bound_nontrivial :
    (((cycleDom.card + badRows.length) * (1 + 1) : ℕ) : ℝ) /
        Fintype.card (ZMod 5) < 1 := by
  norm_num [cycleDom, badRows]

end Teeth

/-! ## Axiom pins -/

/-- info: 'Minidregg.Assurance.TwistMemoryFingerprintJoin.nonContinuous_fingerprint_accept_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms nonContinuous_fingerprint_accept_le
/-- info: 'Minidregg.Assurance.TwistMemoryFingerprintJoin.exactBusClaim_fingerprint_accepted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms exactBusClaim_fingerprint_accepted
/-- info: 'Minidregg.Assurance.TwistMemoryFingerprintJoin.Teeth.bad_read_priced' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Teeth.bad_read_priced
/-- info: 'Minidregg.Assurance.TwistMemoryFingerprintJoin.Teeth.bad_read_bound_nontrivial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Teeth.bad_read_bound_nontrivial

end Minidregg.Assurance.TwistMemoryFingerprintJoin
