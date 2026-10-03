/-
Bounded working-set input lowering for the ACTUAL registered Mini evaluator.
The address schedule of fetch/scatter is explicit and data-independent at this
reference level. This is NOT a claim that Lean's branching/Nock oracle is a
constant-time MPC circuit. Secret-PC/noun-heap arithmetization remains a separate
refinement. No native semantic branch, absence or metered outcome is replaced.
-/
import Compiler.Evaluator
import Theory.AssertAxioms

namespace Minidregg.Compiler.ObliviousEvaluator

open Minidregg.Theory
open Minidregg.Theory.Eval
open Minidregg.Kernel.NockProgramCell
open Minidregg.Compiler.NockProgramCodec
set_option autoImplicit false

structure Key where
  target : Nat
  field : String
  deriving DecidableEq, Repr

structure Entry where
  key : Key
  /-- A cached absence differs from a cache miss. Never default to zero. -/
  value : Option Int
  deriving DecidableEq, Repr

/-- Fixed-list fold: unlike an early-return lookup, the memory access schedule
contains every row. Each conditional is a mux obligation for circuit lowering. -/
def scan (key : Key) (rows : List Entry) : Option Int :=
  rows.foldr (fun row tail => if row.key = key then row.value else tail) none

/-- The ordinary first-match specification, used only for refinement. -/
def lookup (key : Key) : List Entry → Option Int
  | [] => none
  | row :: tail => if row.key = key then row.value else lookup key tail

theorem scan_eq_lookup (key : Key) (rows : List Entry) : scan key rows = lookup key rows := by
  induction rows with
  | nil => rfl
  | cons row tail ih =>
    change (if row.key = key then row.value else scan key tail) =
      (if row.key = key then row.value else lookup key tail)
    rw [ih]

/-- Fixed scatter visits all rows, including misses and dummy writes. Callers
with aliasing rows get the same update in every alias, never an arbitrary one. -/
def scatter (key : Key) (value : Option Int) (rows : List Entry) : List Entry :=
  rows.map fun row => if row.key = key then { row with value := value } else row

@[simp] theorem scatter_length (key : Key) (value : Option Int) (rows : List Entry) :
    (scatter key value rows).length = rows.length := by simp [scatter]

theorem scatter_preserves_other (written observed : Key) (value : Option Int)
    (rows : List Entry) (different : written ≠ observed) :
    scan observed (scatter written value rows) = scan observed rows := by
  induction rows with
  | nil => rfl
  | cons row tail ih =>
    by_cases hit : row.key = written
    · simp [scatter, scan, hit, different] at ih ⊢
      exact ih
    · simp only [scatter, List.map_cons, hit, ↓reduceIte]
      change (if row.key = observed then row.value else scan observed (scatter written value tail)) =
        (if row.key = observed then row.value else scan observed tail)
      rw [ih]

/-- Writing an unallocated slot is not silently accepted. Birth/allocation is
another bounded operation that must provide a complete native successor. -/
def scatterChecked (key : Key) (value : Option Int) (rows : List Entry) :
    Option (List Entry) :=
  if rows.any (fun row => decide (row.key = key)) then some (scatter key value rows)
  else none

def gather (read : Nat → String → Option Int) (keys : List Key) : List Entry :=
  keys.map fun key => ⟨key, read key.target key.field⟩

@[simp] theorem gather_length (read : Nat → String → Option Int) (keys : List Key) :
    (gather read keys).length = keys.length := by simp [gather]

theorem scan_gather {read : Nat → String → Option Int} {key : Key} {keys : List Key}
    (present : key ∈ keys) :
    scan key (gather read keys) = read key.target key.field := by
  rw [scan_eq_lookup]
  induction keys with
  | nil => cases present
  | cons head tail ih =>
    by_cases same : head = key
    · subst head
      simp [gather, lookup]
    · have inside : key ∈ tail := by
        rcases List.mem_cons.mp present with equal | inside
        · exact False.elim (same equal.symm)
        · exact inside
      simpa [gather, lookup, same] using ih inside

structure Capacity where
  rows : Nat
  targetBits : Nat
  keyBytes : Nat
  valueBits : Nat
  deriving DecidableEq, Repr

def entryFits (capacity : Capacity) (entry : Entry) : Bool :=
  decide (entry.key.target < 2 ^ capacity.targetBits) &&
  decide (entry.key.field.toUTF8.size ≤ capacity.keyBytes) &&
  match entry.value with
  | none => true
  | some value => decide (value.natAbs < 2 ^ capacity.valueBits)

/-- Overflow is capacity failure, not semantic crash or a missing field. The
whole requested set must fit; `take capacity` would silently lose dependencies. -/
def gatherBounded (capacity : Capacity) (read : Nat → String → Option Int)
    (keys : List Key) : Option (List Entry) :=
  let rows := gather read keys
  if keys.length ≤ capacity.rows ∧ rows.all (entryFits capacity) = true then
    some rows
  else none

theorem gatherBounded_exact {capacity : Capacity} {read : Nat → String → Option Int}
    {keys : List Key} {rows : List Entry}
    (accepted : gatherBounded capacity read keys = some rows) :
    rows = gather read keys := by
  dsimp only [gatherBounded] at accepted
  split at accepted
  · cases accepted; rfl
  · cases accepted

theorem gatherBounded_complete (capacity : Capacity) (read : Nat → String → Option Int)
    (keys : List Key) (count : keys.length ≤ capacity.rows)
    (width : (gather read keys).all (entryFits capacity) = true) :
    gatherBounded capacity read keys = some (gather read keys) := by
  simp [gatherBounded, count, width]

def slotKey (slot : SampleSlot) : Key := ⟨slot.target, slot.slot⟩

def Covers (keys : List Key) (abi : Abi) : Prop :=
  ∀ slot ∈ abi.sample, slotKey slot ∈ keys

/-- This check is internal/private in a private backend. Publishing a miss
would disclose a footprint. All sample dependencies are checked, not hinted. -/
def coversCheck (keys : List Key) (abi : Abi) : Bool :=
  abi.sample.all fun slot => decide (slotKey slot ∈ keys)

@[simp] theorem coversCheck_iff (keys : List Key) (abi : Abi) :
    coversCheck keys abi = true ↔ Covers keys abi := by
  simp [coversCheck, Covers]

/-- Exact native sample, including context mode, target order, keys, slot
encoding, maximums, and absence refusal. This lemma covers live and pinned ABI. -/
theorem gathered_sample_exact (M : Machine) (read : Nat → String → Option Int)
    (keys : List Key) (abi : Abi) (ctx : Context) (targets : List Nat)
    (covered : Covers keys abi) :
    M.sampleOf abi ctx targets (fun target field => scan ⟨target, field⟩ (gather read keys)) =
      M.sampleOf abi ctx targets read := by
  unfold Machine.sampleOf sampleRecord
  have same := readSlots_congr (read := fun target field => scan ⟨target, field⟩ (gather read keys))
    (read' := read) abi.sample (fun slot member => scan_gather (covered slot member))
  rw [same]

/-- Keep all three actual oracle outcomes and their exact fees. -/
inductive Result (Output : Type)
  | overflow
  | sampleRefused
  | evaluated (result : Ran Output)
  deriving DecidableEq, Repr

def nativeRun (M : Machine) (fuel : Nat) (params : M.Params) (code : M.Code)
    (libs : List M.Code) (abi : Abi) (ctx : Context) (targets : List Nat)
    (read : Nat → String → Option Int) : Result M.Output :=
  match M.sampleOf abi ctx targets read with
  | none => .sampleRefused
  | some sample => .evaluated (M.oracle fuel (M.entry params code libs sample))

/-- The native oracle is still the reference computation. The implemented
lowering here is its finite working-set input boundary, not full private Nock. -/
def runGathered (M : Machine) (capacity : Capacity) (keys : List Key)
    (fuel : Nat) (params : M.Params) (code : M.Code) (libs : List M.Code)
    (abi : Abi) (ctx : Context) (targets : List Nat)
    (read : Nat → String → Option Int) : Result M.Output :=
  if coversCheck keys abi then
    match gatherBounded capacity read keys with
    | none => .overflow
    | some rows => nativeRun M fuel params code libs abi ctx targets
        (fun target field => scan ⟨target, field⟩ rows)
  else .overflow

theorem runGathered_native_exact (M : Machine) (capacity : Capacity) (keys : List Key)
    (fuel : Nat) (params : M.Params) (code : M.Code) (libs : List M.Code)
    (abi : Abi) (ctx : Context) (targets : List Nat) (read : Nat → String → Option Int)
    (covered : Covers keys abi) (count : keys.length ≤ capacity.rows)
    (width : (gather read keys).all (entryFits capacity) = true) :
    runGathered M capacity keys fuel params code libs abi ctx targets read =
      nativeRun M fuel params code libs abi ctx targets read := by
  have check := (coversCheck_iff keys abi).2 covered
  simp only [runGathered, check, ↓reduceIte,
    gatherBounded_complete capacity read keys count width, nativeRun]
  rw [gathered_sample_exact M read keys abi ctx targets covered]

/-- A finite authenticated snapshot projection must account for EVERY ABI
sample slot, including absent fields. Authentication belongs to the native
source/working-set producer; this type records exact semantic projection. -/
structure WorldProjection (capacity : Capacity) (abi : Abi)
    (read : Nat → String → Option Int) where
  rows : List Entry
  count : rows.length = capacity.rows
  width : rows.all (entryFits capacity) = true
  exact : ∀ slot ∈ abi.sample,
    scan (slotKey slot) rows = read slot.target slot.slot

theorem nativeRun_congr (M : Machine) (fuel : Nat) (params : M.Params)
    (code : M.Code) (libs : List M.Code) (abi : Abi) (ctx : Context)
    (targets : List Nat) (read read' : Nat → String → Option Int)
    (same : ∀ slot ∈ abi.sample, read slot.target slot.slot = read' slot.target slot.slot) :
    nativeRun M fuel params code libs abi ctx targets read =
      nativeRun M fuel params code libs abi ctx targets read' := by
  unfold nativeRun Machine.sampleOf sampleRecord
  rw [readSlots_congr abi.sample same]

/-- Fetch from a finite world through the full scan itself, rather than an
arbitrary address-dependent lookup callback. The retained oracle remains the
native semantic reference, not an MPC implementation. -/
def runWorld (M : Machine) (workingCapacity : Capacity) (keys : List Key)
    (fuel : Nat) (params : M.Params) (code : M.Code) (libs : List M.Code)
    (abi : Abi) (ctx : Context) (targets : List Nat) (world : List Entry) : Result M.Output :=
  runGathered M workingCapacity keys fuel params code libs abi ctx targets
    (fun target field => scan ⟨target, field⟩ world)

theorem runWorld_native_exact (M : Machine) (worldCapacity workingCapacity : Capacity)
    (keys : List Key) (fuel : Nat) (params : M.Params) (code : M.Code)
    (libs : List M.Code) (abi : Abi) (ctx : Context) (targets : List Nat)
    (read : Nat → String → Option Int) (world : WorldProjection worldCapacity abi read)
    (covered : Covers keys abi) (count : keys.length ≤ workingCapacity.rows)
    (width : (gather (fun target field => scan ⟨target, field⟩ world.rows) keys).all
      (entryFits workingCapacity) = true) :
    runWorld M workingCapacity keys fuel params code libs abi ctx targets world.rows =
      nativeRun M fuel params code libs abi ctx targets read := by
  unfold runWorld
  rw [runGathered_native_exact M workingCapacity keys fuel params code libs abi ctx targets
    _ covered count width]
  exact nativeRun_congr M fuel params code libs abi ctx targets _ read world.exact

/-- Actual registered Nock, not a separate toy object evaluator. -/
abbrev nockRun := runGathered Machine.nock

/-- Public abstract memory schedule: every gather lane scans all public rows;
scatter scans every row again. Dummy keys still use the same addresses. Actual
circuit mux/bit encoding and malicious MPC remain explicit refinement work. -/
def phaseSchedule (worldRows workingRows : Nat) : List Nat :=
  (List.replicate workingRows (List.range worldRows)).flatten ++ List.range worldRows

theorem phaseSchedule_same (worldRows workingRows : Nat) (leftKeys rightKeys : List Key)
    (_leftBound : leftKeys.length = workingRows) (_rightBound : rightKeys.length = workingRows) :
    phaseSchedule worldRows leftKeys.length = phaseSchedule worldRows rightKeys.length := by
  rw [_leftBound, _rightBound]

#assert_axioms scan_eq_lookup
#assert_axioms scan_gather
#assert_axioms scatter_preserves_other
#assert_axioms gatherBounded_exact
#assert_axioms runGathered_native_exact
#assert_axioms phaseSchedule_same
#assert_axioms runWorld_native_exact

end Minidregg.Compiler.ObliviousEvaluator
