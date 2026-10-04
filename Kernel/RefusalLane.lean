/- Per-subject refusal lane for signed invocations.

A command whose signature authenticates but which preparation or admission then
refuses commits nothing, yet it cost the Host real work: decoding, physical
reads, law evaluation and Nock or Bend re-execution. Without a charge any
enrolled key can keep the single serial Host busy with refused commands.

Each such refusal debits its signer's lane by the wall time it cost (never less
than a base fee); while a subject's lane is empty, that subject's next commands
are refused right after authentication, before any preparation. Lanes refill at
a fixed rate. Other subjects' lanes are untouched (`charge_other`), and enough
refusals at one instant close the charged lane (`charges_close_lane`).

This is Host-process state, a bound on refusal work, not money: it is not part
of the durable image and starts full when the Host starts.
-/
import Std.Data.HashMap
import Theory.AssertAxioms

namespace Minidregg.Kernel.RefusalLane

set_option autoImplicit false

structure Policy where
  /-- Refusal work a subject may cost before its lane closes. -/
  capacityMs : Nat
  /-- Refusal work restored per elapsed second. -/
  refillPerSecondMs : Nat
  /-- The least an authenticated refusal is charged (authentication itself). -/
  baseFeeMs : Nat
  deriving Repr

/-- 30 s of refused work per subject, restored at 100 ms per second: alone, a
subject can keep the Host refusing it at most a tenth of the time. -/
def deployed : Policy := ⟨30_000, 100, 50⟩

/-- Balance in microseconds, so that a refill of `elapsedMs * refillPerSecondMs`
is exact for every elapsed millisecond. -/
structure Lane where
  balanceUs : Nat
  stampMs : Nat
  deriving DecidableEq, Repr

def Lane.full (policy : Policy) (now : Nat) : Lane := ⟨policy.capacityMs * 1000, now⟩

def Lane.refill (policy : Policy) (lane : Lane) (now : Nat) : Lane :=
  ⟨min (policy.capacityMs * 1000) (lane.balanceUs + (now - lane.stampMs) * policy.refillPerSecondMs),
    max lane.stampMs now⟩

def Lane.isOpen (lane : Lane) : Bool := decide (0 < lane.balanceUs)

def fee (policy : Policy) (costMs : Nat) : Nat := max policy.baseFeeMs costMs

def Lane.debit (policy : Policy) (lane : Lane) (costMs : Nat) : Lane :=
  { lane with balanceUs := lane.balanceUs - fee policy costMs * 1000 }

abbrev Lanes := Std.HashMap Nat Lane

def current (policy : Policy) (lanes : Lanes) (subject now : Nat) : Lane :=
  (lanes.getD subject (Lane.full policy now)).refill policy now

def admits (policy : Policy) (lanes : Lanes) (subject now : Nat) : Bool :=
  (current policy lanes subject now).isOpen

def charge (policy : Policy) (lanes : Lanes) (subject now costMs : Nat) : Lanes :=
  lanes.insert subject ((current policy lanes subject now).debit policy costMs)

/-- Charging one subject changes no other subject's lane. -/
theorem charge_other (policy : Policy) (lanes : Lanes) (subject other now costMs : Nat)
    (distinct : subject ≠ other) :
    (charge policy lanes subject now costMs)[other]? = lanes[other]? := by
  simp [charge, Std.HashMap.getElem?_insert, distinct]

theorem admits_other (policy : Policy) (lanes : Lanes) (subject other now costMs later : Nat)
    (distinct : subject ≠ other) :
    admits policy (charge policy lanes subject now costMs) other later =
      admits policy lanes other later := by
  simp only [admits, current, Std.HashMap.getD_eq_getD_getElem?,
    charge_other policy lanes subject other now costMs distinct]

theorem current_le_capacity (policy : Policy) (lanes : Lanes) (subject now : Nat) :
    (current policy lanes subject now).balanceUs ≤ policy.capacityMs * 1000 := by
  simp only [current, Lane.refill]
  exact Nat.min_le_left _ _

/-- A charge at `now`, read back at the same `now`, is exactly the fee. -/
theorem current_charge_same (policy : Policy) (lanes : Lanes) (subject now costMs : Nat) :
    (current policy (charge policy lanes subject now costMs) subject now).balanceUs =
      (current policy lanes subject now).balanceUs - fee policy costMs * 1000 := by
  have capped := current_le_capacity policy lanes subject now
  simp only [current, charge, Std.HashMap.getD_insert_self, Lane.debit, Lane.refill] at capped ⊢
  have elapsed : now - max (lanes.getD subject (Lane.full policy now)).stampMs now = 0 :=
    Nat.sub_eq_zero_of_le (Nat.le_max_right _ _)
  rw [elapsed, Nat.zero_mul, Nat.add_zero]
  exact Nat.min_eq_right (Nat.le_trans (Nat.sub_le _ _) capped)

theorem current_charges_same (policy : Policy) (subject now : Nat) (costs : List Nat)
    (lanes : Lanes) :
    (current policy (costs.foldl (fun held cost => charge policy held subject now cost) lanes)
        subject now).balanceUs =
      (current policy lanes subject now).balanceUs - (costs.map (fee policy)).sum * 1000 := by
  induction costs generalizing lanes with
  | nil => simp
  | cons cost rest ih =>
      simp only [List.foldl_cons, List.map_cons, List.sum_cons]
      rw [ih, current_charge_same, Nat.sub_sub, Nat.add_mul]

/-- Refusals whose fees reach the capacity, charged at one instant, close the
charged subject's lane. -/
theorem charges_close_lane (policy : Policy) (subject now : Nat) (costs : List Nat)
    (lanes : Lanes) (enough : policy.capacityMs ≤ (costs.map (fee policy)).sum) :
    admits policy (costs.foldl (fun held cost => charge policy held subject now cost) lanes)
      subject now = false := by
  have capped := current_le_capacity policy lanes subject now
  have spent : (current policy lanes subject now).balanceUs ≤ (costs.map (fee policy)).sum * 1000 :=
    Nat.le_trans capped (Nat.mul_le_mul_right 1000 enough)
  simp [admits, Lane.isOpen, current_charges_same, Nat.sub_eq_zero_of_le spent]

/-- Thirty-one refusals of one second each close a fresh deployed lane, and
leave every other subject's lane open. -/
theorem deployed_thirty_one_seconds_close (lanes : Lanes) (subject other now : Nat)
    (distinct : subject ≠ other) (fresh : lanes[other]? = none) :
    admits deployed ((List.replicate 31 1000).foldl
        (fun held cost => charge deployed held subject now cost) lanes) subject now = false ∧
    admits deployed ((List.replicate 31 1000).foldl
        (fun held cost => charge deployed held subject now cost) lanes) other now = true := by
  refine ⟨charges_close_lane deployed subject now _ lanes (by decide), ?_⟩
  have untouched : ∀ (costs : List Nat) (held : Lanes),
      admits deployed (costs.foldl (fun held cost => charge deployed held subject now cost) held)
        other now = admits deployed held other now := by
    intro costs
    induction costs with
    | nil => intro held; rfl
    | cons cost rest ih =>
        intro held
        simp only [List.foldl_cons]
        rw [ih, admits_other deployed held subject other now cost now distinct]
  rw [untouched]
  simp [admits, current, Std.HashMap.getD_eq_getD_getElem?, fresh,
    Lane.full, Lane.refill, Lane.isOpen, deployed]

#assert_axioms charge_other
#assert_axioms admits_other
#assert_axioms current_charge_same
#assert_axioms current_charges_same
#assert_axioms charges_close_lane
#assert_axioms deployed_thirty_one_seconds_close

/-- The Host's lanes. -/
initialize lanes : IO.Ref Lanes ← IO.mkRef {}

/-- May `subject` be prepared now? Read at the instant `now`. -/
def isOpenAt (subject now : Nat) : IO Bool :=
  return admits deployed (← lanes.get) subject now

/-- Charge `subject` for a refusal whose work began at `startedMs`. -/
def chargeSince (subject startedMs : Nat) : IO Unit := do
  let now ← IO.monoMsNow
  lanes.modify fun held => charge deployed held subject now (now - startedMs)

end Minidregg.Kernel.RefusalLane
