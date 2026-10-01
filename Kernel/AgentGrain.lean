/- Source-authored execution resource for hosted agent tasks.
A grain may own many such task resources. Its stable task identity is the
ordinary object id, never a transport connection or a process id. The four
fields are execution generation, status, remaining allowance and unresolved
reservation, in integer permission micro-units. These are scoped spend
allowances, not Book balances or $DREGG. Birth does not prove funding; a
broker must accept only explicitly allocated task resources, never an
arbitrary caller-authored initial allowance. The one funded increase is the
`refill` edge: `Kernel.PurseRefill` burns Book credit 1:1 into `remaining`
in the same turn, so one micro-unit is one credit. No field is a policy revision or grant
revocation generation. A stopped status proves admission fencing, not that
an external process or provider actually stopped. -/
import Kernel.DeclaredFields
import Kernel.ResourceTransaction
import Pred.Core

namespace Minidregg.Kernel.AgentGrain
open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.EffectDeclaration
open Minidregg.Theory.DeclaredActionLowering
open Minidregg.Theory.Store (Store Address)
open Minidregg.Pred
set_option autoImplicit false

structure State where
  generation : Int
  status : Int
  remaining : Int
  reserved : Int
  deriving DecidableEq, Repr

def State.values (s : State) : List Int :=
  [s.generation, s.status, s.remaining, s.reserved]

abbrev key (task : Nat) (field : Nat) : StateKey := DeclaredFields.key task field

/-- The four coordinates in the store's canonical order (fields 1, 2, 3, 0;
see `DeclaredFields`). -/
def State.coordinates (s : State) : DeclaredResourceProjection.Values :=
  [(1,s.status),(2,s.remaining),(3,s.reserved),(0,s.generation)]

theorem State.coordinates_four (s : State) :
    s.coordinates = DeclaredFields.four s.generation s.status s.remaining s.reserved := rfl

/-- The task resource as a declared-effect store: exactly its four fields. -/
def State.store (s : State) (task : Nat) : Store effectLayout :=
  DeclaredFields.store task s.coordinates

def initialStore (task budget : Nat) : Store effectLayout :=
  DeclaredFields.birthStore task (⟨0, 0, Int.ofNat budget, 0⟩ : State).coordinates

def readState (task : Nat) (store : Store effectLayout) : Option State := do
  let read := fun n => DeclaredFields.read task n store
  return ⟨← read 0, ← read 1, ← read 2, ← read 3⟩

theorem readState_store (task : Nat) (s : State) : readState task (s.store task) = some s := by
  obtain ⟨r0, r1, r2, r3⟩ := DeclaredFields.read_four task s.generation s.status s.remaining s.reserved
  simp [readState, State.store, State.coordinates_four, r0, r1, r2, r3]

/-- Every operation compares all four old coordinates, including unchanged
ones. The generic declared receiver checks these writes against the durable
store and binds the exact actions into authorization and replay identity. -/
def actions (task : Nat) (before after : State) : List Action :=
  (List.range 4).zipWith (fun n pair =>
    .write (key task n) (some pair.1) pair.2) (before.values.zip after.values)

/-- Projection vocabulary required in the generic resource receiver. Both
sides are read from the task's canonical store, never supplied as decision bits
by a host. Deltas preserve arithmetic over the exact integer state. -/
def slots (before after : State) : List (String × Int) :=
  DeclaredResourceProjection.scalarSlots before.coordinates after.coordinates

def project := DeclaredResourceProjection.project

/-- The policy view of a task resource is exactly its four coordinates. -/
theorem store_projection_exact (task : Nat) (before after : State) :
    DeclaredResourceProjection.project task (before.store task) (after.store task) =
      slots before after := by
  simp only [State.store, slots, State.coordinates_four]
  exact DeclaredFields.project_four task _ _ _ _ _ _ _ _

private def nonnegative (slot : String) : Pred := .not (.le slot (-1))
private def unchangedBudget : Pred := .all [
  .eq "resource/field/2/delta" 0, .eq "resource/field/3/delta" 0]
private def edge (old new gen : Int) (extra : List Pred := []) : Pred :=
  .all ([.eq "resource/field/1/before" old, .eq "resource/field/1/after" new,
    .eq "resource/field/0/delta" gen] ++ extra)

/-- 0 paused, 1 running hard, 2 running soft, 3 reserved hard,
4 reserved soft, 5 paused with unresolved reservation, 6 cancelled,
7 cancelled with unresolved reservation. One paid attempt per task can be
in flight; independent parallel tasks use independent resources/budgets. -/
def transitionPolicy : Pred := .all [
  .le "resource/pair/2/3/delta" 0,
  .memberOf "resource/field/0/delta" [0,1],
  .memberOf "resource/field/1/before" [0,1,2,3,4,5,6,7],
  .memberOf "resource/field/1/after" [0,1,2,3,4,5,6,7],
  nonnegative "resource/field/0/before", nonnegative "resource/field/0/after",
  nonnegative "resource/field/2/before", nonnegative "resource/field/2/after",
  nonnegative "resource/field/3/before", nonnegative "resource/field/3/after",
  .any (
    -- Fresh attachment, same task. Outstanding attempts must reconcile first.
    [edge 0 1 1 [unchangedBudget, .eq "resource/field/3/after" 0],
     edge 0 2 1 [unchangedBudget, .eq "resource/field/3/after" 0],
     edge 1 2 0 [unchangedBudget], edge 2 1 0 [unchangedBudget],
     -- Controller start/input is an authorized no-op, not a paid reservation.
     edge 1 1 0 [unchangedBudget, .eq "resource/field/3/after" 0],
     -- A delegated tool publication may carry the parent execution as a
     -- joint exact-state witness while its prompt is reserved. The generic
     -- receiver checks the old root, current grant and signed read leg.
     edge 3 3 0 [unchangedBudget],
     -- Soft disconnect changes neither authority nor allowance.
     edge 2 2 0 [unchangedBudget], edge 4 4 0 [unchangedBudget]] ++
    -- Reserve before dispatch; zero-cost operations still have a pending state.
    ([ (1,3), (2,4) ].map fun p => edge p.1 p.2 0
      [.eq "resource/field/3/before" 0, .eq "resource/pair/2/3/delta" 0,
       .le "resource/field/2/delta" 0]) ++
    -- Settlement releases at most the held allowance; unknown effects stay held.
    ([ (3,1), (4,2), (5,0), (7,6) ].map fun p => edge p.1 p.2 0
      [.eq "resource/field/3/after" 0, .le "resource/pair/2/3/delta" 0,
       nonnegative "resource/field/2/delta"]) ++
    -- Controller interruption fences either attachment mode without cancelling
    -- the task. A reserved attempt remains held until audited settlement.
    ([ (1,0), (2,0), (3,5), (4,5), (0,6), (1,6), (2,6), (3,7), (4,7), (5,7) ].map
      fun p => edge p.1 p.2 1 [unchangedBudget]))]

/-- The slot only the purse-refill receiver (`Kernel.PurseRefillReceiver`)
projects, after it has decided the joint turn: the payer's owner grant, the
Book burn admitted at the loaded Book, and the joint credit delta balanced.
No other receiver projects a slot of this name (READ: the generic declared
receiver projects `request/*`, `target/policyId`, `command/bytes/*`,
`resource/*` and `joint/target/*`). -/
def refillSlot : String := "authority/operation/purse-refill"

/-- The `refill` edge (PAY §2.7). Only the remaining allowance grows, by a
positive amount; generation, status and the (zero) reservation are unchanged;
the task is paused or attached without an outstanding reservation (0, 1, 2).
It is a separate branch of `policy`, not of `transitionPolicy`: every
transition the generic receiver can reach is still budget-nonincreasing
(`accepted_budget_nonincrease`), and the only budget increase is this edge,
which requires `refillSlot`. -/
def refillPolicy : Pred := .all [
  .eq refillSlot 1,
  .memberOf "resource/field/1/before" [0,1,2],
  .eq "resource/field/1/delta" 0,
  .eq "resource/field/0/delta" 0,
  .eq "resource/field/3/before" 0,
  .eq "resource/field/3/delta" 0,
  .not (.le "resource/field/2/delta" 0),
  nonnegative "resource/field/0/before", nonnegative "resource/field/2/before"]

/-- Management is deliberately lockable. The caller may supply an explicit
management rule; it governs policy installation and capability revocation, never mutation.
Ordinary observation/delegation still require the native capability checker.
The refill branch carries no subject or verb test: whoever burns their own
credit may fund the purse; the burn is authorized on the payer's account. -/
def policy (management : Pred := .any []) : Pred := .any [
  .all [.eq "request/verb" 2, transitionPolicy],
  refillPolicy,
  .memberOf "request/verb" [1,3],
  .all [.memberOf "request/verb" [4,5], management]]

/-- Use this predicate to restrict an execution worker. The native grant
carrier currently narrows targets, verbs, time and budget but has no arbitrary
Pred caveat field: the deployed path must conjoin this predicate in the resource
law for that worker's subject. A future caveated grant carrier may reuse it.
A worker must not receive the controller's unrestricted authority: expected-value writes
alone cannot stop a stale worker that can read a newer page. Reconciliation
of late external outcomes uses the controller's separately governed right. -/
def executionCaveat (generation : Int) : Pred :=
  .all [.eq "request/verb" 2, .eq "resource/field/0/after" generation,
    .eq "resource/field/0/delta" 0, .any [edge 1 3 0, edge 2 4 0, edge 3 1 0, edge 4 2 0]]

/-- A delegated tool subject can carry the reserved parent as an exact-state
witness in a joint publication. It cannot reserve, settle, attach or trip the
parent. The fixed generation refuses a stale witness after a hard disconnect,
including when a later controller attaches the same task again. -/
def witnessCaveat (generation : Int) : Pred :=
  .all [.eq "request/verb" 2,
    .eq "resource/field/0/before" generation,
    .eq "resource/field/0/after" generation,
    .memberOf "resource/field/1/before" [3,4],
    .eq "resource/field/0/delta" 0,
    .eq "resource/field/1/delta" 0,
    .eq "resource/field/2/delta" 0,
    .eq "resource/field/3/delta" 0]

/-- Construction is not authorization: only the generic receiver, current
committed policy, current grants and signature evidence admit these actions. -/
def reserve (s : State) (amount : Int) : State :=
  { s with status := s.status + 2, remaining := s.remaining - amount, reserved := amount }

def settle (s : State) (charge : Int) : State :=
  { s with
    status := (if s.status = 5 then 0 else if s.status = 7 then 6 else s.status - 2)
    remaining := s.remaining + s.reserved - charge
    reserved := 0 }

def trip (s : State) : State :=
  { s with generation := s.generation + 1, status := if s.status = 3 then 5 else 0 }

/-- Abnormal interruption of either attachment mode. An unresolved reservation
remains held; settlement can return the task to paused status for reattachment. -/
def interrupt (s : State) : State :=
  { s with generation := s.generation + 1, status := if s.status = 3 ∨ s.status = 4 then 5 else 0 }

/-- Authoring vocabulary; receiver admission still comes exclusively from
ordinary declared writes plus the installed source predicate. No request can
select an alternative transition evaluator. -/
inductive Operation where
  | input
  | attach (soft : Bool)
  | mode (soft : Bool)
  | reserve (amount : Int)
  | settle (charge : Int)
  | disconnect
  | interrupt
  | cancel
  /-- Admitted only by the purse-refill receiver, in one joint turn with the
  Book burn of the same amount (`Kernel.PurseRefill`). -/
  | refill (amount : Int)
  deriving DecidableEq, Repr

def Operation.after (operation : Operation) (s : State) : State :=
  match operation with
  | .input => s
  | .attach soft => { s with generation := s.generation + 1, status := (if soft then 2 else 1) }
  | .mode soft => { s with status := (if soft then 2 else 1) }
  | .reserve amount => AgentGrain.reserve s amount
  | .settle charge => AgentGrain.settle s charge
  | .disconnect => if s.status = 2 ∨ s.status = 4 then s else trip s
  | .interrupt => AgentGrain.interrupt s
  | .cancel => { s with
      generation := s.generation + 1
      status := (if s.status = 3 ∨ s.status = 4 ∨ s.status = 5 then 7 else 6) }
  | .refill amount => { s with remaining := s.remaining + amount }

theorem input_witness_exact (s : State) : Operation.input.after s = s := rfl

theorem input_witness_generation (s : State) :
    (Operation.input.after s).generation = s.generation := rfl

/-- Exact canonical host operation bytes include a unique operation id as
well as the prompt/request. The source-derived nonce binds those bytes into
the existing native request/signature/nullifier path, under the deployed
cSHAKE collision-resistance assumption. Equal context bytes are a replay,
not authorization to dispatch again. This binds bytes, not how Hermes built
them or the truth of externally reported usage. -/
def contextNonce (context : List UInt8) : Nat :=
  (Minidregg.Compiler.Sp800185Cshake256.hash
    "DREGG.AGENT-GRAIN.CONTEXT/v1".toUTF8.toList context).digest.value

def Operation.actions (operation : Operation) (task : Nat) (s : State) : List Action :=
  AgentGrain.actions task s (operation.after s)

/-- Author one ordinary resource incidence. This convenience function carries
no admission decision: the same generic transaction receiver checks the exact
old root, current installed law, grant and signed command. -/
def Operation.target (operation : Operation) (task : Nat) (capability : CapabilityId)
    (expectedRoot : Digest) (before : State) (observeCapability : Option CapabilityId := none) :
    DeclaredResourceController.Target :=
  { kind := .object, target := task, capability := capability,
    observeCapability := observeCapability, schemaVersion := 1,
    expectedTargetRoot := expectedRoot, payload := .scalar (operation.actions task before) }

/-- Publish a task transition together with ordinary authored resource edits.
The caller supplies each other incidence; the kernel requires distinct target
identities and admits all against one old authority snapshot, or commits none.
There is no agent-specific transaction mode or storage path. -/
def Operation.command (operation : Operation) (subject : SubjectId)
    (nonce task : Nat) (capability : CapabilityId) (expectedRoot : Digest) (before : State)
    (publications : List DeclaredResourceController.Target := [])
    (observeCapability : Option CapabilityId := none) :
    DeclaredResourceController.Command :=
  { subject := subject, nonce := nonce,
    targets := operation.target task capability expectedRoot before observeCapability :: publications }

theorem operation_target_actions_exact (operation : Operation) (task : Nat)
    (capability : CapabilityId) (expectedRoot : Digest) (before : State)
    (observeCapability : Option CapabilityId) :
    (operation.target task capability expectedRoot before observeCapability).payload =
      .scalar (AgentGrain.actions task before (operation.after before)) := rfl

theorem operation_command_retains_publications (operation : Operation) (subject : SubjectId)
    (nonce task : Nat) (capability : CapabilityId)
    (expectedRoot : Digest) (before : State) (publications : List DeclaredResourceController.Target)
    (observeCapability : Option CapabilityId) :
    (operation.command subject nonce task capability expectedRoot before publications
      observeCapability).targets.tail =
      publications := rfl

def accepts (before after : State) : Bool :=
  eval transitionPolicy ⟨[]⟩ ⟨slots before after⟩

/-- Every admitted operation preserves or consumes the task's total
remaining-plus-reserved allowance. No operation mints budget, including
soft disconnect, cancellation and late-result reconciliation. -/
theorem accepted_budget_nonincrease (before after : State)
    (accepted : accepts before after = true) :
    after.remaining + after.reserved ≤ before.remaining + before.reserved := by
  unfold accepts transitionPolicy at accepted
  rw [eval_all] at accepted
  have bound := (List.all_eq_true.mp accepted) (.le "resource/pair/2/3/delta" 0) (by simp)
  simp [eval, evalWith, Minidregg.Pred.State.get, slots, State.coordinates,
    DeclaredResourceProjection.scalarSlots, DeclaredResourceProjection.get,
    DeclaredResourceProjection.fieldName, DeclaredResourceProjection.pairName,
    Nat.repr_eq_ofList_toDigits, Nat.toDigits, Nat.toDigitsCore, Nat.digitChar, toString] at bound

  omega

/-- The canonical generation can stay put or advance once; a stale epoch is
never restored by a resume, settlement or mode change. -/
theorem accepted_generation_monotone (before after : State)
    (accepted : accepts before after = true) : before.generation ≤ after.generation := by
  unfold accepts transitionPolicy at accepted
  rw [eval_all] at accepted
  have bound := (List.all_eq_true.mp accepted) (.memberOf "resource/field/0/delta" [0,1]) (by simp)
  simp [eval, evalWith, Minidregg.Pred.State.get, slots, State.coordinates,
    DeclaredResourceProjection.scalarSlots, DeclaredResourceProjection.get,
    DeclaredResourceProjection.fieldName, DeclaredResourceProjection.pairName,
    Nat.repr_eq_ofList_toDigits, Nat.toDigits, Nat.toDigitsCore, Nat.digitChar, toString] at bound

  omega

/-- A generation-scoped worker cannot refresh a stale token by reading a
new page: the same native policy projection binds both ends of its operation. -/
theorem worker_generation_exact (before after : State) (generation : Int)
    (accepted : eval (executionCaveat generation) ⟨[]⟩
      ⟨("request/verb",2) :: slots before after⟩ = true) :
    before.generation = generation ∧ after.generation = generation := by
  unfold executionCaveat at accepted
  rw [eval_all] at accepted
  have post := (List.all_eq_true.mp accepted) (.eq "resource/field/0/after" generation) (by simp)
  have delta := (List.all_eq_true.mp accepted) (.eq "resource/field/0/delta" 0) (by simp)
  simp [eval, evalWith, Minidregg.Pred.State.get, slots, State.coordinates,
    DeclaredResourceProjection.scalarSlots, DeclaredResourceProjection.get,
    DeclaredResourceProjection.fieldName, DeclaredResourceProjection.pairName,
    Nat.repr_eq_ofList_toDigits, Nat.toDigits, Nat.toDigitsCore, Nat.digitChar, toString] at post delta
  omega

theorem reserve_total (s : State) (amount : Int) :
    (reserve s amount).remaining + (reserve s amount).reserved = s.remaining := by
  simp [reserve]

theorem trip_generation (s : State) : (trip s).generation = s.generation + 1 := rfl

theorem trip_preserves_unresolved (s : State) :
    (trip s).remaining = s.remaining ∧ (trip s).reserved = s.reserved := ⟨rfl, rfl⟩

theorem interrupt_generation (s : State) :
    (interrupt s).generation = s.generation + 1 := rfl

theorem interrupt_preserves_unresolved (s : State) :
    (interrupt s).remaining = s.remaining ∧ (interrupt s).reserved = s.reserved := ⟨rfl, rfl⟩

theorem interrupt_invalidates_generation (s : State) :
    (interrupt s).generation ≠ s.generation := by simp [interrupt]

theorem interrupted_worker_refused (before after : State) :
    eval (executionCaveat before.generation) ⟨[]⟩
      ⟨("request/verb",2) :: slots (interrupt before) after⟩ ≠ true := by
  intro admitted
  exact interrupt_invalidates_generation before
    (worker_generation_exact (interrupt before) after before.generation admitted).1

theorem hard_trip_invalidates_generation (s : State) :
    (trip s).generation ≠ s.generation := by simp [trip]

theorem tripped_worker_refused (before after : State) :
    eval (executionCaveat before.generation) ⟨[]⟩
      ⟨("request/verb",2) :: slots (trip before) after⟩ ≠ true := by
  intro admitted
  exact hard_trip_invalidates_generation before
    (worker_generation_exact (trip before) after before.generation admitted).1

theorem witness_generation_before_exact (before after : State) (generation : Int)
    (accepted : eval (witnessCaveat generation) ⟨[]⟩
      ⟨("request/verb",2) :: slots before after⟩ = true) :
    before.generation = generation := by
  unfold witnessCaveat at accepted
  rw [eval_all] at accepted
  have bound := (List.all_eq_true.mp accepted)
    (.eq "resource/field/0/before" generation) (by simp)
  simp [eval, evalWith, Minidregg.Pred.State.get, slots, State.coordinates,
    DeclaredResourceProjection.scalarSlots, DeclaredResourceProjection.get,
    DeclaredResourceProjection.fieldName, DeclaredResourceProjection.pairName,
    Nat.repr_eq_ofList_toDigits, Nat.toDigits, Nat.toDigitsCore, Nat.digitChar, toString]
    at bound
  exact bound

theorem interrupted_parent_witness_refused (before after : State) :
    eval (witnessCaveat before.generation) ⟨[]⟩
      ⟨("request/verb",2) :: slots (interrupt before) after⟩ ≠ true := by
  intro admitted
  exact interrupt_invalidates_generation before
    (witness_generation_before_exact (interrupt before) after before.generation admitted)

theorem soft_reserved_interrupt_general (g r h : Int)
    (hg : 0 ≤ g) (hr : 0 ≤ r) (hh : 0 ≤ h) :
    accepts ⟨g,4,r,h⟩ (interrupt ⟨g,4,r,h⟩) = true := by
  simp [accepts, transitionPolicy, interrupt, edge, unchangedBudget, nonnegative,
    slots, State.coordinates, DeclaredResourceProjection.scalarSlots,
    DeclaredResourceProjection.get, DeclaredResourceProjection.fieldName,
    DeclaredResourceProjection.pairName, eval, evalWith, Pred.all, Pred.any,
    PredList.ofList, evalWithAll, evalWithAny, Minidregg.Pred.State.get,
    Nat.repr_eq_ofList_toDigits, Nat.toDigits, Nat.toDigitsCore, Nat.digitChar, toString]
  omega


theorem interrupt_general (s : State)
    (hg : 0 ≤ s.generation) (hr : 0 ≤ s.remaining) (hh : 0 ≤ s.reserved)
    (hs : s.status = 1 ∨ s.status = 2 ∨ s.status = 3 ∨ s.status = 4) :
    accepts s (interrupt s) = true := by
  rcases s with ⟨g, status, r, h⟩
  dsimp at hg hr hh hs
  rcases hs with hs | hs | hs | hs <;> subst status <;>
    simp [accepts, transitionPolicy, interrupt, edge, unchangedBudget, nonnegative,
      slots, State.coordinates, DeclaredResourceProjection.scalarSlots,
      DeclaredResourceProjection.get, DeclaredResourceProjection.fieldName,
      DeclaredResourceProjection.pairName, eval, evalWith, Pred.all, Pred.any,
      PredList.ofList, evalWithAll, evalWithAny, Minidregg.Pred.State.get,
      Nat.repr_eq_ofList_toDigits, Nat.toDigits, Nat.toDigitsCore, Nat.digitChar, toString] <;>
    omega

theorem interrupted_reserved_settlement_general (g r h charge : Int)
    (hg : 0 ≤ g) (hr : 0 ≤ r) (hh : 0 ≤ h)
    (hc0 : 0 ≤ charge) (hch : charge ≤ h) :
    accepts (interrupt ⟨g,4,r,h⟩)
      (settle (interrupt ⟨g,4,r,h⟩) charge) = true := by
  simp [accepts, transitionPolicy, interrupt, settle, edge, unchangedBudget, nonnegative,
    slots, State.coordinates, DeclaredResourceProjection.scalarSlots,
    DeclaredResourceProjection.get, DeclaredResourceProjection.fieldName,
    DeclaredResourceProjection.pairName, eval, evalWith, Pred.all, Pred.any,
    PredList.ofList, evalWithAll, evalWithAny, Minidregg.Pred.State.get,
    Nat.repr_eq_ofList_toDigits, Nat.toDigits, Nat.toDigitsCore, Nat.digitChar, toString]
  omega

theorem hard_reserved_settlement_general (g r h charge : Int)
    (hg : 0 ≤ g) (hr : 0 ≤ r) (hh : 0 ≤ h)
    (hc0 : 0 ≤ charge) (hch : charge ≤ h) :
    accepts (interrupt ⟨g,3,r,h⟩)
      (settle (interrupt ⟨g,3,r,h⟩) charge) = true := by
  simpa [interrupt] using
    interrupted_reserved_settlement_general g r h charge hg hr hh hc0 hch

/-! ## The refill edge (PAY §2.7, lane P6) -/

/-- The refill branch as the purse-refill receiver evaluates it: the slot it
alone projects, then the task's exact four-coordinate projection. -/
def refillAccepts (before after : State) : Bool :=
  eval refillPolicy ⟨[]⟩ ⟨(refillSlot, 1) :: slots before after⟩

theorem refill_after (s : State) (amount : Int) :
    (Operation.refill amount).after s = { s with remaining := s.remaining + amount } := rfl

set_option maxHeartbeats 1600000 in
/-- What an accepted refill edge is: generation, status and the zero
reservation unchanged, the remaining allowance strictly larger, and no
reservation outstanding (status 0, 1 or 2). -/
theorem refill_accepted_exact (before after : State)
    (accepted : refillAccepts before after = true) :
    after.generation = before.generation ∧ after.status = before.status ∧
      before.reserved = 0 ∧ after.reserved = 0 ∧ before.remaining < after.remaining ∧
      (before.status = 0 ∨ before.status = 1 ∨ before.status = 2) := by
  unfold refillAccepts refillPolicy at accepted
  rw [eval_all] at accepted
  simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at accepted
  obtain ⟨_, sb, sd, gd, rb, rd, up, _, _⟩ := accepted
  simp [eval, evalWith, Minidregg.Pred.State.get, slots, State.coordinates, refillSlot,
    DeclaredResourceProjection.scalarSlots, DeclaredResourceProjection.get,
    DeclaredResourceProjection.fieldName, DeclaredResourceProjection.pairName,
    Nat.repr_eq_ofList_toDigits, Nat.toDigits, Nat.toDigitsCore, Nat.digitChar, toString] at sb
  simp [eval, evalWith, Minidregg.Pred.State.get, slots, State.coordinates, refillSlot,
    DeclaredResourceProjection.scalarSlots, DeclaredResourceProjection.get,
    DeclaredResourceProjection.fieldName, DeclaredResourceProjection.pairName,
    Nat.repr_eq_ofList_toDigits, Nat.toDigits, Nat.toDigitsCore, Nat.digitChar, toString] at sd
  simp [eval, evalWith, Minidregg.Pred.State.get, slots, State.coordinates, refillSlot,
    DeclaredResourceProjection.scalarSlots, DeclaredResourceProjection.get,
    DeclaredResourceProjection.fieldName, DeclaredResourceProjection.pairName,
    Nat.repr_eq_ofList_toDigits, Nat.toDigits, Nat.toDigitsCore, Nat.digitChar, toString] at gd
  simp [eval, evalWith, Minidregg.Pred.State.get, slots, State.coordinates, refillSlot,
    DeclaredResourceProjection.scalarSlots, DeclaredResourceProjection.get,
    DeclaredResourceProjection.fieldName, DeclaredResourceProjection.pairName,
    Nat.repr_eq_ofList_toDigits, Nat.toDigits, Nat.toDigitsCore, Nat.digitChar, toString] at rb
  simp [eval, evalWith, Minidregg.Pred.State.get, slots, State.coordinates, refillSlot,
    DeclaredResourceProjection.scalarSlots, DeclaredResourceProjection.get,
    DeclaredResourceProjection.fieldName, DeclaredResourceProjection.pairName,
    Nat.repr_eq_ofList_toDigits, Nat.toDigits, Nat.toDigitsCore, Nat.digitChar, toString] at rd
  rw [eval_not, Bool.not_eq_true'] at up
  simp [eval, evalWith, Minidregg.Pred.State.get, slots, State.coordinates, refillSlot,
    DeclaredResourceProjection.scalarSlots, DeclaredResourceProjection.get,
    DeclaredResourceProjection.fieldName, DeclaredResourceProjection.pairName,
    Nat.repr_eq_ofList_toDigits, Nat.toDigits, Nat.toDigitsCore, Nat.digitChar, toString] at up
  omega

/-- Satisfiable pole, general: every positive refill of a task holding no
reservation, paused or attached, is accepted by the edge. -/
theorem refill_edge_accepted (s : State) (amount : Int)
    (hg : 0 ≤ s.generation) (hr : 0 ≤ s.remaining) (hres : s.reserved = 0)
    (hs : s.status = 0 ∨ s.status = 1 ∨ s.status = 2) (positive : 0 < amount) :
    refillAccepts s ((Operation.refill amount).after s) = true := by
  rcases s with ⟨g, status, r, h⟩
  dsimp at hg hr hres hs
  subst hres
  rcases hs with hs | hs | hs <;> subst status <;>
    simp [refillAccepts, refillPolicy, refill_after, nonnegative, refillSlot,
      slots, State.coordinates, DeclaredResourceProjection.scalarSlots,
      DeclaredResourceProjection.get, DeclaredResourceProjection.fieldName,
      DeclaredResourceProjection.pairName, eval, evalWith, Pred.all,
      PredList.ofList, evalWithAll, Minidregg.Pred.State.get,
      Nat.repr_eq_ofList_toDigits, Nat.toDigits, Nat.toDigitsCore, Nat.digitChar, toString] <;>
    omega

/-- **Without the refill slot, no mutation the policy admits increases the
task's allowance.** A verb-2 request admitted by `policy` whose projection does
not carry `refillSlot = 1` satisfies `transitionPolicy`, whose first conjunct
is `resource/pair/2/3/delta ≤ 0`. -/
theorem policy_mutation_nonincrease_without_refill (management : Pred)
    (old st : Minidregg.Pred.State)
    (accepted : eval (policy management) old st = true)
    (mutation : st.get "request/verb" = some 2)
    (noRefill : st.get refillSlot ≠ some 1) :
    ∃ d, st.get "resource/pair/2/3/delta" = some d ∧ d ≤ 0 := by
  unfold policy at accepted
  rw [eval_any] at accepted
  obtain ⟨branch, member, holds⟩ := List.any_eq_true.mp accepted
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · rw [eval_all] at holds
    have t := (List.all_eq_true.mp holds) transitionPolicy (by simp)
    unfold transitionPolicy at t
    rw [eval_all] at t
    have b := (List.all_eq_true.mp t) (.le "resource/pair/2/3/delta" 0) (by simp)
    simp only [eval, evalWith] at b
    cases h : st.get "resource/pair/2/3/delta" with
    | none => simp [h] at b
    | some d => exact ⟨d, rfl, by simpa [h] using b⟩
  · unfold refillPolicy at holds
    rw [eval_all] at holds
    have r := (List.all_eq_true.mp holds) (.eq refillSlot 1) (by simp)
    simp only [eval, evalWith, decide_eq_true_eq] at r
    exact absurd r noRefill
  · simp [eval, evalWith, mutation] at holds
  · rw [eval_all] at holds
    have v := (List.all_eq_true.mp holds) (.memberOf "request/verb" [4,5]) (by simp)
    simp [eval, evalWith, mutation] at v

end Minidregg.Kernel.AgentGrain
