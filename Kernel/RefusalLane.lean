/- Per-subject refusal lane for signed invocations.

A command whose signature authenticates but which preparation or admission then
refuses commits nothing, yet it cost the Host real work: decoding, physical
reads, law evaluation and Nock or Bend re-execution. Without a charge any
enrolled key can keep the single serial Host busy with refused commands.

Each such refusal debits its signer's lane by the wall time it cost (never less
than a base fee), into debt if it must; while a subject's lane is not positive,
that subject's next commands are refused right after authentication, before any
preparation, and the refill repays the debt before the lane reopens
(`Lane.refill_closed`, `deployed_empty_lane_owes_a_fee`). Lanes refill at
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
is exact for every elapsed millisecond. An `Int`: a refusal that costs more than
the balance leaves a DEBT, and the lane stays closed until refill repays it. (A
`Nat` balance saturated at zero, so a closed lane reopened one millisecond later
and the refill rate bounded nothing after the first closing.) -/
structure Lane where
  balanceUs : Int
  stampMs : Nat
  deriving DecidableEq, Repr

def Lane.full (policy : Policy) (now : Nat) : Lane :=
  ⟨((policy.capacityMs * 1000 : Nat) : Int), now⟩

def Lane.refill (policy : Policy) (lane : Lane) (now : Nat) : Lane :=
  ⟨min ((policy.capacityMs * 1000 : Nat) : Int)
      (lane.balanceUs + (((now - lane.stampMs) * policy.refillPerSecondMs : Nat) : Int)),
    max lane.stampMs now⟩

def Lane.isOpen (lane : Lane) : Bool := decide (0 < lane.balanceUs)

def fee (policy : Policy) (costMs : Nat) : Nat := max policy.baseFeeMs costMs

def Lane.debit (policy : Policy) (lane : Lane) (costMs : Nat) : Lane :=
  { lane with balanceUs := lane.balanceUs - ((fee policy costMs * 1000 : Nat) : Int) }

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
    (current policy lanes subject now).balanceUs ≤ ((policy.capacityMs * 1000 : Nat) : Int) := by
  simp only [current, Lane.refill]
  exact Int.min_le_left _ _

/-- A charge at `now`, read back at the same `now`, is exactly the fee: the
balance goes down by it, below zero if it must. -/
theorem current_charge_same (policy : Policy) (lanes : Lanes) (subject now costMs : Nat) :
    (current policy (charge policy lanes subject now costMs) subject now).balanceUs =
      (current policy lanes subject now).balanceUs - ((fee policy costMs * 1000 : Nat) : Int) := by
  have capped := current_le_capacity policy lanes subject now
  simp only [current, charge, Std.HashMap.getD_insert_self, Lane.debit, Lane.refill] at capped ⊢
  have elapsed : now - max (lanes.getD subject (Lane.full policy now)).stampMs now = 0 :=
    Nat.sub_eq_zero_of_le (Nat.le_max_right _ _)
  rw [elapsed, Int.min_eq_right (by omega)]
  omega

theorem current_charges_same (policy : Policy) (subject now : Nat) (costs : List Nat)
    (lanes : Lanes) :
    (current policy (costs.foldl (fun held cost => charge policy held subject now cost) lanes)
        subject now).balanceUs =
      (current policy lanes subject now).balanceUs -
        (((costs.map (fee policy)).sum * 1000 : Nat) : Int) := by
  induction costs generalizing lanes with
  | nil => simp
  | cons cost rest ih =>
      simp only [List.foldl_cons, List.map_cons, List.sum_cons]
      rw [ih, current_charge_same]
      omega

/-- Refusals whose fees reach the capacity, charged at one instant, close the
charged subject's lane. -/
theorem charges_close_lane (policy : Policy) (subject now : Nat) (costs : List Nat)
    (lanes : Lanes) (enough : policy.capacityMs ≤ (costs.map (fee policy)).sum) :
    admits policy (costs.foldl (fun held cost => charge policy held subject now cost) lanes)
      subject now = false := by
  have capped := current_le_capacity policy lanes subject now
  have spent : policy.capacityMs * 1000 ≤ (costs.map (fee policy)).sum * 1000 :=
    Nat.mul_le_mul_right 1000 enough
  simp only [admits, Lane.isOpen, current_charges_same, decide_eq_false_iff_not, Int.not_lt]
  omega

/-- **The debt holds.** A lane whose balance plus the refill since its stamp is
not positive is closed: the refill repays a debt before it reopens anything. -/
theorem Lane.refill_closed (policy : Policy) (lane : Lane) (later : Nat)
    (owed : lane.balanceUs + (((later - lane.stampMs) * policy.refillPerSecondMs : Nat) : Int) ≤ 0) :
    (lane.refill policy later).isOpen = false := by
  simp only [Lane.refill, Lane.isOpen, decide_eq_false_iff_not, Int.not_lt]
  exact Int.le_trans (Int.min_le_right _ _) owed

/-- Reading a lane back after a charge: the charged lane, refilled. -/
theorem current_charge (policy : Policy) (lanes : Lanes) (subject now costMs later : Nat) :
    current policy (charge policy lanes subject now costMs) subject later =
      ((current policy lanes subject now).debit policy costMs).refill policy later := by
  simp only [current, charge, Std.HashMap.getD_insert_self]

/-- **A lane in debt refuses until it is repaid.** A refusal charged at `now`
whose fee exceeds the lane's balance leaves a debt; at every later instant at
which the refill since `now` has not yet covered that debt, the subject is
refused (`admits = false`), however many milliseconds have passed. -/
theorem debt_refuses_until_repaid (policy : Policy) (lanes : Lanes) (subject now costMs later : Nat)
    (owed : (current policy lanes subject now).balanceUs - ((fee policy costMs * 1000 : Nat) : Int)
        + (((later - now) * policy.refillPerSecondMs : Nat) : Int) ≤ 0) :
    admits policy (charge policy lanes subject now costMs) subject later = false := by
  unfold admits
  rw [current_charge]
  apply Lane.refill_closed
  have stamp : now ≤ ((current policy lanes subject now).debit policy costMs).stampMs := by
    simp only [current, Lane.debit, Lane.refill]
    exact Nat.le_max_right _ _
  have less : (((later - ((current policy lanes subject now).debit policy costMs).stampMs) *
      policy.refillPerSecondMs : Nat) : Int) ≤ (((later - now) * policy.refillPerSecondMs : Nat) : Int) :=
    Int.ofNat_le.mpr (Nat.mul_le_mul_right _ (Nat.sub_le_sub_left stamp later))
  simp only [Lane.debit] at less ⊢
  exact Int.le_trans (Int.add_le_add_left less _) owed

/-- The deployed policy, a fresh subject and a flood: 600 base-fee refusals at
one instant empty the lane exactly; one more leaves it 50 ms in debt, and the
subject stays refused for the next 500 ms of refill (here: at 499 ms). -/
theorem deployed_flood_debt_holds (subject now : Nat) :
    admits deployed (charge deployed ((List.replicate 600 50).foldl
        (fun held cost => charge deployed held subject now cost) {}) subject now 50)
      subject (now + 499) = false := by
  apply debt_refuses_until_repaid
  rw [current_charges_same]
  have fresh : (current deployed ({} : Lanes) subject now).balanceUs = 30_000_000 := by
    simp [current, Lane.full, Lane.refill, deployed]
  rw [fresh, List.map_replicate, List.sum_replicate_nat, Nat.add_sub_cancel_left]
  decide

/-- At the deployed rate a 50 ms refusal charged to an empty lane keeps it closed
for 500 ms: closed at 499 ms, open at 501 ms. Under the old saturating `Nat`
balance the same lane was open again at 1 ms. -/
theorem deployed_empty_lane_owes_a_fee :
    ((Lane.debit deployed ⟨0, 0⟩ 50).refill deployed 499).isOpen = false ∧
      ((Lane.debit deployed ⟨0, 0⟩ 50).refill deployed 501).isOpen = true := by
  decide

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
#assert_axioms Lane.refill_closed
#assert_axioms current_charge
#assert_axioms debt_refuses_until_repaid
#assert_axioms deployed_flood_debt_holds
#assert_axioms deployed_empty_lane_owes_a_fee
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
