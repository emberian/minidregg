/-
# Theory.ResourceCost -- proof-native resource and cost effects

Resource metering is part of the Lean semantics, not an interpretation supplied
by a native executor.  This module gives every prepared canonical turn a
declaration-time upper bound and a transition-indexed exact charge.  Charges
form a pointwise additive algebra, so sequential and flat joint work aggregate
without a call forest.

The carrier is `Nat` on purpose: semantic charges cannot be negative and do
not overflow.  A separate checked fixed-width boundary makes machine-word
overflow explicit.  Network and side-effect lanes account for committed
*intent*; performing physical I/O remains a handler operation outside this
pure logical transition.
-/
import Theory.CanonicalTransition

namespace Minidregg.Theory.ResourceCost

open Minidregg.Theory
open Minidregg.Theory.CellState
open Minidregg.Theory.CanonicalTransition

set_option autoImplicit false

universe u v w x y z

/-! ## The additive resource algebra -/

/-- Independently budgeted semantic resource lanes.  `incidences` counts the
flat requests participating in one joint turn; it deliberately does not encode
parent/child call-forest structure.  Lease usage is byte-block time, hence is
additive across storage and duration. -/
inductive Lane
  | incidences
  | turnBytes
  | memoryTouches
  | witnessBytes
  | proofWork
  | storageBytes
  | networkBytes
  | sideEffectCount
  | feeDebit
  | leaseByteBlocks
  deriving DecidableEq, Fintype, Repr

/-- Closed executable quantification over resource lanes.  Keeping this
enumeration beside the inductive prevents a host-side metric registry. -/
def Lane.allCheck (predicate : Lane -> Bool) : Bool :=
  predicate .incidences && (
  predicate .turnBytes && (
  predicate .memoryTouches && (
  predicate .witnessBytes && (
  predicate .proofWork && (
  predicate .storageBytes && (
  predicate .networkBytes && (
  predicate .sideEffectCount && (
  predicate .feeDebit &&
  predicate .leaseByteBlocks))))))))

@[simp] theorem Lane.allCheck_eq_true_iff (predicate : Lane -> Bool) :
    Lane.allCheck predicate = true <-> forall lane, predicate lane = true := by
  constructor
  · intro accepted lane
    cases lane <;> simp_all [Lane.allCheck]
  · intro accepted
    simp [Lane.allCheck, accepted]

/-- A proof-native resource vector.  Addition and order are the pointwise
instances for functions into `Nat`. -/
abbrev Charge := Lane -> Nat

namespace Charge

/-- Pointwise order, exposed as a theorem so budget obligations never depend
on an opaque comparison routine. -/
theorem le_iff (left right : Charge) :
    left <= right <-> forall lane, left lane <= right lane :=
  Iff.rfl

@[simp] theorem zero_apply (lane : Lane) : (0 : Charge) lane = 0 :=
  rfl

@[simp] theorem add_apply (left right : Charge) (lane : Lane) :
    (left + right) lane = left lane + right lane :=
  rfl

/-- Exact charges are intrinsically nonnegative, including at an eventual
signed accounting boundary. -/
theorem toInt_nonnegative (charge : Charge) (lane : Lane) :
    (0 : Int) <= Int.ofNat (charge lane) := by
  simp

/-- Additive aggregation for any finite sequence of semantic effects. -/
def aggregate (charges : List Charge) : Charge :=
  charges.foldr (fun charge total => charge + total) 0

@[simp] theorem aggregate_nil : aggregate [] = 0 :=
  rfl

@[simp] theorem aggregate_cons (charge : Charge) (charges : List Charge) :
    aggregate (charge :: charges) = charge + aggregate charges :=
  rfl

theorem aggregate_append (left right : List Charge) :
    aggregate (left ++ right) = aggregate left + aggregate right := by
  induction left with
  | nil => simp
  | cons charge charges induction =>
      simp [induction, add_assoc]

/-- Executable finite check for pointwise funding. -/
def fundedCheck (exact available : Charge) : Bool :=
  Lane.allCheck fun lane => decide (exact lane <= available lane)

@[simp] theorem fundedCheck_eq_true_iff (exact available : Charge) :
    fundedCheck exact available = true <-> exact <= available := by
  simp [fundedCheck, Charge.le_iff]

end Charge

/-! ## Static quotes and compositional exact charges -/

/-- A static upper bound paired with the exact semantic charge.  The exact
charge is data derived by Lean; a runtime cannot substitute a cheaper receipt. -/
structure Quote where
  upper : Charge
  exact : Charge
  exact_le_upper : exact <= upper

namespace Quote

def zero : Quote where
  upper := 0
  exact := 0
  exact_le_upper := by intro lane; exact Nat.le_refl 0

/-- Sequential/parallel composition uses the same pointwise sum. -/
def compose (left right : Quote) : Quote where
  upper := left.upper + right.upper
  exact := left.exact + right.exact
  exact_le_upper := by
    intro lane
    exact Nat.add_le_add (left.exact_le_upper lane)
      (right.exact_le_upper lane)

@[simp] theorem compose_upper (left right : Quote) :
    (compose left right).upper = left.upper + right.upper :=
  rfl

@[simp] theorem compose_exact (left right : Quote) :
    (compose left right).exact = left.exact + right.exact :=
  rfl

def aggregate : List Quote -> Quote
  | [] => zero
  | quote :: quotes => compose quote (aggregate quotes)

@[simp] theorem aggregate_upper (quotes : List Quote) :
    (aggregate quotes).upper = Charge.aggregate (quotes.map Quote.upper) := by
  induction quotes with
  | nil => rfl
  | cons quote quotes induction =>
      simp [aggregate, Charge.aggregate, induction]

@[simp] theorem aggregate_exact (quotes : List Quote) :
    (aggregate quotes).exact = Charge.aggregate (quotes.map Quote.exact) := by
  induction quotes with
  | nil => rfl
  | cons quote quotes induction =>
      simp [aggregate, Charge.aggregate, induction]

/-- A strict excess in any lane refutes a claimed static bound. -/
theorem not_bounded_of_lane_exceeds (quote : Quote) (lane : Lane)
    (exceeds : quote.upper lane < quote.exact lane) : False :=
  Nat.not_lt_of_ge (quote.exact_le_upper lane) exceeds

end Quote

/-! ## Explicit machine-word overflow boundary -/

/-- Per-lane serialization widths.  Semantic arithmetic stays unbounded; this
layout is used only where a fixed-width artifact is emitted. -/
structure WordLayout where
  bits : Lane -> Nat

def WordLayout.capacity (layout : WordLayout) (lane : Lane) : Nat :=
  2 ^ layout.bits lane

def WordLayout.Fits (layout : WordLayout) (charge : Charge) : Prop :=
  forall lane, charge lane < layout.capacity lane

def WordLayout.fitsCheck (layout : WordLayout) (charge : Charge) : Bool :=
  Lane.allCheck fun lane => decide (charge lane < layout.capacity lane)

@[simp] theorem WordLayout.fitsCheck_eq_true_iff
    (layout : WordLayout) (charge : Charge) :
    layout.fitsCheck charge = true <-> layout.Fits charge := by
  simp [WordLayout.fitsCheck, WordLayout.Fits]

/-- Checked fixed-width encoding.  `none` is semantic evidence of overflow,
not wrapping arithmetic. -/
def WordLayout.encode? (layout : WordLayout) (charge : Charge) :
    Option ((lane : Lane) -> Fin (layout.capacity lane)) :=
  if checked : layout.fitsCheck charge = true then
    some (fun lane =>
      ⟨charge lane, (layout.fitsCheck_eq_true_iff charge).mp checked lane⟩)
  else
    none

@[simp] theorem WordLayout.encode?_eq_none_iff
    (layout : WordLayout) (charge : Charge) :
    layout.encode? charge = none <-> ¬ layout.Fits charge := by
  simp [WordLayout.encode?]

theorem WordLayout.not_fits_iff_exists_overflow
    (layout : WordLayout) (charge : Charge) :
    (¬ layout.Fits charge) <->
      exists lane, layout.capacity lane <= charge lane := by
  simp [WordLayout.Fits]

/-- Load-bearing overflow tooth: one overflowing coordinate makes the entire
fixed-width charge encoding fail. -/
theorem WordLayout.encode?_none_of_overflow
    (layout : WordLayout) (charge : Charge) (lane : Lane)
    (overflow : layout.capacity lane <= charge lane) :
    layout.encode? charge = none := by
  rw [WordLayout.encode?_eq_none_iff,
    WordLayout.not_fits_iff_exists_overflow]
  exact ⟨lane, overflow⟩

/-! ## Canonical prepared-turn metering -/

/-- A Lean-owned metering semantics for canonical prepared turns.  Both the
static bound and exact charge are functions of the exact indexed turn.  Memory
touches are pinned to the canonical typed field/resource footprints. -/
structure PreparedCostSemantics
    {S : CellState.Schema.{u, v, w, x}} {Root : Type y}
    [DecidableEq S.Field] [DecidableEq S.Resource]
    (M : CellState.Materializer S Root) (pre : CellState.Materialized M)
    (Nullifier : Type z) where
  upper : PreparedTurn M pre Nullifier -> Charge
  exact : PreparedTurn M pre Nullifier -> Charge
  exact_le_upper : forall turn, exact turn <= upper turn
  memoryTouches_exact : forall turn,
    exact turn .memoryTouches =
      turn.delta.fieldFootprint.card + turn.delta.resourceFootprint.card

def PreparedCostSemantics.quote
    {S : CellState.Schema.{u, v, w, x}} {Root : Type y}
    [DecidableEq S.Field] [DecidableEq S.Resource]
    {M : CellState.Materializer S Root} {pre : CellState.Materialized M}
    {Nullifier : Type z}
    (semantics : PreparedCostSemantics M pre Nullifier)
    (turn : PreparedTurn M pre Nullifier) : Quote where
  upper := semantics.upper turn
  exact := semantics.exact turn
  exact_le_upper := semantics.exact_le_upper turn

/-- A bounded quote indexed by one exact canonical prepared turn.  This is the
integration seam for semantic objects (such as flat hyperedges) whose exact
charge is naturally derived only after their own acceptance proof exists. -/
structure BoundedPreparedTurn
    {S : CellState.Schema.{u, v, w, x}} {Root : Type y}
    [DecidableEq S.Field] [DecidableEq S.Resource]
    {M : CellState.Materializer S Root} {pre : CellState.Materialized M}
    {Nullifier : Type z}
    (turn : PreparedTurn M pre Nullifier) where
  quote : Quote
  memoryTouches_exact :
    quote.exact .memoryTouches =
      turn.delta.fieldFootprint.card + turn.delta.resourceFootprint.card

def PreparedCostSemantics.bounded
    {S : CellState.Schema.{u, v, w, x}} {Root : Type y}
    [DecidableEq S.Field] [DecidableEq S.Resource]
    {M : CellState.Materializer S Root} {pre : CellState.Materialized M}
    {Nullifier : Type z}
    (semantics : PreparedCostSemantics M pre Nullifier)
    (turn : PreparedTurn M pre Nullifier) : BoundedPreparedTurn turn where
  quote := semantics.quote turn
  memoryTouches_exact := semantics.memoryTouches_exact turn

/-! ## Exact debit receipts and atomic refusal -/

/-- Funding evidence for the exact Lean-derived charge.  Remaining budget is a
projection, not a caller field. -/
structure ChargeReceipt (available : Charge) (quote : Quote) : Prop where
  funded : quote.exact <= available

def ChargeReceipt.remaining {available : Charge} {quote : Quote}
    (_receipt : ChargeReceipt available quote) : Charge :=
  fun lane => available lane - quote.exact lane

/-- Every admitted lane has the exact charged delta: no undercharge and no
overcharge are hidden in the receipt. -/
theorem ChargeReceipt.exact_delta {available : Charge} {quote : Quote}
    (receipt : ChargeReceipt available quote) :
    quote.exact + receipt.remaining = available := by
  funext lane
  change quote.exact lane + (available lane - quote.exact lane) = available lane
  rw [Nat.add_comm]
  exact Nat.sub_add_cancel (receipt.funded lane)

/-- Metering refines the total canonical decision.  A prepared post becomes
visible only in the funded constructor; blocked, semantic rejection, and
over-budget refusal all preserve the exact pre-cell and budget. -/
inductive SettledDecision
    {S : CellState.Schema.{u, v, w, x}} {Root : Type y}
    [DecidableEq S.Field] [DecidableEq S.Resource]
    (M : CellState.Materializer S Root)
    (Blocked Reject Nullifier : Type z)
    (pre : CellState.Materialized M)
    (semantics : PreparedCostSemantics M pre Nullifier)
    (available : Charge) : Type _
  | blocked (reason : Blocked)
  | rejected (reason : Reject)
  | overBudget (turn : PreparedTurn M pre Nullifier)
      (insufficient : ¬ (semantics.exact turn <= available))
  | admitted (turn : PreparedTurn M pre Nullifier)
      (receipt : ChargeReceipt available (semantics.quote turn))

def SettledDecision.ofDecision
    {S : CellState.Schema.{u, v, w, x}} {Root : Type y}
    [DecidableEq S.Field] [DecidableEq S.Resource]
    {M : CellState.Materializer S Root}
    {Blocked Reject Nullifier : Type z} {pre : CellState.Materialized M}
    (semantics : PreparedCostSemantics M pre Nullifier) (available : Charge) :
    Decision M Blocked Reject Nullifier pre ->
      SettledDecision M Blocked Reject Nullifier pre semantics available
  | .blocked reason => .blocked reason
  | .rejected reason => .rejected reason
  | .prepared turn =>
      if checked : Charge.fundedCheck (semantics.exact turn) available = true then
        .admitted turn
          ⟨(Charge.fundedCheck_eq_true_iff
            (semantics.exact turn) available).mp checked⟩
      else
        .overBudget turn (by
          intro funded
          exact checked ((Charge.fundedCheck_eq_true_iff
            (semantics.exact turn) available).mpr funded))

def SettledDecision.logicalPost
    {S : CellState.Schema.{u, v, w, x}} {Root : Type y}
    [DecidableEq S.Field] [DecidableEq S.Resource]
    {M : CellState.Materializer S Root}
    {Blocked Reject Nullifier : Type z} {pre : CellState.Materialized M}
    {semantics : PreparedCostSemantics M pre Nullifier} {available : Charge} :
    SettledDecision M Blocked Reject Nullifier pre semantics available ->
      CellState.Materialized M
  | .blocked _ => pre
  | .rejected _ => pre
  | .overBudget _ _ => pre
  | .admitted turn _ => turn.post

def SettledDecision.remaining
    {S : CellState.Schema.{u, v, w, x}} {Root : Type y}
    [DecidableEq S.Field] [DecidableEq S.Resource]
    {M : CellState.Materializer S Root}
    {Blocked Reject Nullifier : Type z} {pre : CellState.Materialized M}
    {semantics : PreparedCostSemantics M pre Nullifier} {available : Charge} :
    SettledDecision M Blocked Reject Nullifier pre semantics available -> Charge
  | .blocked _ => available
  | .rejected _ => available
  | .overBudget _ _ => available
  | .admitted _ receipt => receipt.remaining

@[simp] theorem SettledDecision.blocked_atomic
    {S : CellState.Schema.{u, v, w, x}} {Root : Type y}
    [DecidableEq S.Field] [DecidableEq S.Resource]
    {M : CellState.Materializer S Root}
    {Blocked Reject Nullifier : Type z} {pre : CellState.Materialized M}
    {semantics : PreparedCostSemantics M pre Nullifier} {available : Charge}
    (reason : Blocked) :
    (SettledDecision.blocked (M := M) (Reject := Reject)
      (Nullifier := Nullifier) (pre := pre) (semantics := semantics)
      (available := available) reason).logicalPost = pre /\
    (SettledDecision.blocked (M := M) (Reject := Reject)
      (Nullifier := Nullifier) (pre := pre) (semantics := semantics)
      (available := available) reason).remaining = available :=
  ⟨rfl, rfl⟩

@[simp] theorem SettledDecision.rejected_atomic
    {S : CellState.Schema.{u, v, w, x}} {Root : Type y}
    [DecidableEq S.Field] [DecidableEq S.Resource]
    {M : CellState.Materializer S Root}
    {Blocked Reject Nullifier : Type z} {pre : CellState.Materialized M}
    {semantics : PreparedCostSemantics M pre Nullifier} {available : Charge}
    (reason : Reject) :
    (SettledDecision.rejected (M := M) (Blocked := Blocked)
      (Nullifier := Nullifier) (pre := pre) (semantics := semantics)
      (available := available) reason).logicalPost = pre /\
    (SettledDecision.rejected (M := M) (Blocked := Blocked)
      (Nullifier := Nullifier) (pre := pre) (semantics := semantics)
      (available := available) reason).remaining = available :=
  ⟨rfl, rfl⟩

@[simp] theorem SettledDecision.overBudget_atomic
    {S : CellState.Schema.{u, v, w, x}} {Root : Type y}
    [DecidableEq S.Field] [DecidableEq S.Resource]
    {M : CellState.Materializer S Root}
    {Blocked Reject Nullifier : Type z} {pre : CellState.Materialized M}
    {semantics : PreparedCostSemantics M pre Nullifier} {available : Charge}
    (turn : PreparedTurn M pre Nullifier)
    (insufficient : ¬ (semantics.exact turn <= available)) :
    (SettledDecision.overBudget (Blocked := Blocked) (Reject := Reject)
      (semantics := semantics) (available := available) turn insufficient).logicalPost =
        pre /\
    (SettledDecision.overBudget (Blocked := Blocked) (Reject := Reject)
      (semantics := semantics) (available := available) turn insufficient).remaining =
        available :=
  ⟨rfl, rfl⟩

/-- An admitted decision exposes exactly the canonical post and exact debit. -/
theorem SettledDecision.admitted_exact
    {S : CellState.Schema.{u, v, w, x}} {Root : Type y}
    [DecidableEq S.Field] [DecidableEq S.Resource]
    {M : CellState.Materializer S Root}
    {Blocked Reject Nullifier : Type z} {pre : CellState.Materialized M}
    {semantics : PreparedCostSemantics M pre Nullifier} {available : Charge}
    (turn : PreparedTurn M pre Nullifier)
    (receipt : ChargeReceipt available (semantics.quote turn)) :
    (SettledDecision.admitted (Blocked := Blocked) (Reject := Reject)
      turn receipt).logicalPost = turn.post /\
    semantics.exact turn +
      (SettledDecision.admitted (Blocked := Blocked) (Reject := Reject)
        turn receipt).remaining = available := by
  constructor
  · rfl
  · exact receipt.exact_delta

end Minidregg.Theory.ResourceCost

#print axioms Minidregg.Theory.ResourceCost.Quote.compose
#print axioms Minidregg.Theory.ResourceCost.WordLayout.encode?_none_of_overflow
#print axioms Minidregg.Theory.ResourceCost.SettledDecision.admitted_exact
