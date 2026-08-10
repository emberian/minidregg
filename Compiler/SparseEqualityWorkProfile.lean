/-
# Compiler.SparseEqualityWorkProfile — Lean-owned dense/sparse work schedule

This module fixes the mathematical quantity and the empirical schedule used to
choose between two opaque native execution plans for an equality-weighted sparse
table:

* `dense`: materialize every `chiEval` weight on the `2^m` Boolean cube, scatter
  the active values into a dense table, then take a dot product;
* `sparse`: evaluate `chiEval` only at the active addresses and accumulate those
  products directly.

`mle_sparseTable` proves that both plans target the same Lean expression.  It
does not relate either Rust implementation to Lean.  The benchmark profile is
also Lean data and is emitted verbatim for the native timing harness; Rust does
not select the tested dimensions, densities, or repetition counts.
-/
import Loom.MultilinearExtension

namespace Minidregg.Compiler.SparseEqualityWorkProfile

open Minidregg.Loom

set_option autoImplicit false

/-! ## One semantic quantity, two execution plans -/

section Semantics

variable {F : Type*} [CommRing F] {m q : Nat}

/-- A dense Boolean-cube table assembled from an address-native row list.
Repeated addresses are added in the carrier, matching scatter-add execution. -/
def sparseTable (address : Fin q -> Fin m -> Bool) (value : Fin q -> F) :
    (Fin m -> Bool) -> F :=
  fun corner => ∑ row, if address row = corner then value row else 0

/-- The exact common quantity behind the benchmark: dense MLE evaluation of a
scatter-added table equals direct equality-weight accumulation over its active
rows.  Address uniqueness is not required. -/
theorem mle_sparseTable (address : Fin q -> Fin m -> Bool) (value : Fin q -> F)
    (point : Fin m -> F) :
    mle (sparseTable address value) point =
      ∑ row, value row * chiEval (address row) point := by
  classical
  rw [mle]
  simp only [sparseTable, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro row _
  rw [Fintype.sum_eq_single (address row)]
  · simp
  · intro corner hne
    simp [hne.symm]

end Semantics

/-! ## Lean-owned empirical work profile -/

/-- One density point.  `iterations` controls repeated wall-clock samples in
the opaque benchmark harness; it is not a soundness or protocol parameter. -/
structure BenchmarkCase where
  logDomain : Nat
  activeRows : Nat
  iterations : Nat
deriving DecidableEq, Repr

def BenchmarkCase.domainPoints (test : BenchmarkCase) : Nat :=
  2 ^ test.logDomain

/-- Two multiplications per newly materialized equality weight, then one per
dense dot-product slot. -/
def BenchmarkCase.denseMulCount (test : BenchmarkCase) : Nat :=
  3 * test.domainPoints - 2

/-- One factor per address bit plus the final multiplication by the row value. -/
def BenchmarkCase.sparseMulCount (test : BenchmarkCase) : Nat :=
  (test.logDomain + 1) * test.activeRows

/-- The dense plan simultaneously holds the equality vector and scattered table.
Inputs common to both plans and allocator metadata are deliberately excluded. -/
def BenchmarkCase.denseExtraBytes (test : BenchmarkCase) : Nat :=
  2 * test.domainPoints * 32

def BenchmarkCase.WellFormed (test : BenchmarkCase) : Prop :=
  0 < test.logDomain ∧
  0 < test.activeRows ∧
  test.activeRows <= test.domainPoints ∧
  0 < test.iterations

/-- A 12-bit address space spans both sides of the arithmetic crossover while
remaining practical for the current scalar, recursive `Tower256` multiplication:
the sparse plan performs `activeRows * 13` multiplications, while the dense plan
performs `3 * 2^12 - 2` across recurrence and dot product.

The active counts deliberately bracket the whole-functional multiplication
crossover `(3 * 2^12 - 2) / 13`, between 256 and 1024 rows; timings, not this
operation-count heuristic, decide the actual crossover on each host. -/
def profile : List BenchmarkCase :=
  [ { logDomain := 12, activeRows := 64, iterations := 3 },
    { logDomain := 12, activeRows := 256, iterations := 3 },
    { logDomain := 12, activeRows := 512, iterations := 3 },
    { logDomain := 12, activeRows := 768, iterations := 3 },
    { logDomain := 12, activeRows := 1024, iterations := 2 },
    { logDomain := 12, activeRows := 4096, iterations := 1 } ]

theorem profile_wellFormed : ∀ test ∈ profile, test.WellFormed := by
  simp [profile, BenchmarkCase.WellFormed, BenchmarkCase.domainPoints]

def schema : String := "minidregg/sparse-equality-work-profile/v1"

private def BenchmarkCase.csvRow (test : BenchmarkCase) : String :=
  String.intercalate ","
    [schema, toString test.logDomain, toString test.domainPoints,
      toString test.activeRows, toString test.iterations,
      toString test.denseMulCount, toString test.sparseMulCount,
      toString test.denseExtraBytes]

/-- Canonical text consumed by the native timing harness. -/
def profileCsv : String :=
  String.intercalate "\n"
    (("schema,log_domain,domain_points,active_rows,iterations,dense_mul_count," ++
      "sparse_mul_count,dense_extra_bytes") :: profile.map BenchmarkCase.csvRow) ++
  "\n"

end Minidregg.Compiler.SparseEqualityWorkProfile

/-- info: 'Minidregg.Compiler.SparseEqualityWorkProfile.mle_sparseTable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Compiler.SparseEqualityWorkProfile.mle_sparseTable
/-- info: 'Minidregg.Compiler.SparseEqualityWorkProfile.profile_wellFormed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Compiler.SparseEqualityWorkProfile.profile_wellFormed
