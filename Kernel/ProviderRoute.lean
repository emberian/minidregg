/-
# Kernel.ProviderRoute -- the provider purse charges by the route recorded at reserve

A hosted Hermes call has one payer, chosen by the controller from the
operator's provider table and the friend's credential grant (HERMES-KEYS):

* `user`  -- the friend's own key: the friend pays the provider directly, and
  the purse is charged only the per-operation fee for the turn;
* `pool`  -- the operator's key: the purse pays the metered tariff;
* `homelab` -- a keyless upstream the operator runs: per-operation fee plus
  its own metered rates.

A *provider purse* is an AgentGrain task with a fifth declared field,
`route` (field 4): 0 while no call is in flight, otherwise the code of the
route the in-flight call took. Its installed law (`policy`) conjoins the
ordinary grain policy with `transition schedule`, whose constants are the
per-operation fees of the Host's pinned per-route tariff at birth.

`transition` makes the route a FACT the kernel holds, not a settlement claim:

* a reserve (free status → held status) must record a real route (1, 2 or 3)
  and hold at least that route's fee; a user-route hold is exactly the fee;
* while a call is held the route cannot change;
* a settle (held → free) clears the route and must charge by the recorded
  route's schedule: a user-route call is charged its fee or nothing (the
  release of a call that never left), a metered call nothing or at least its
  fee, never more than the hold.

What the kernel cannot see is which bearer the controller attached to the
HTTP request. The controller resolves the route and the bearer together, from
one table row, before it reserves (`grain-runtime provider_route`); the route
it records at reserve is the one the settle is charged by
(`settle_route_matches_reserve`), so a pool-key call cannot be settled as a
user call (`route_cannot_downgrade_at_settle`).
-/
import Kernel.ProviderMetering
import Theory.AssertAxioms

namespace Minidregg.Kernel.ProviderRoute

open Minidregg.Compiler
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.EffectDeclaration
open Minidregg.Theory.DeclaredActionLowering
open Minidregg.Theory.Store (Store Address)
open Minidregg.Pred
open Minidregg.Kernel.ProviderMetering (Route Schedule)

set_option autoImplicit false

/-- The provider purse's route field. -/
def routeField : Nat := 4

/-- A provider purse: the four AgentGrain coordinates and the route of the
call in flight (0: none). -/
structure State where
  grain : AgentGrain.State
  route : Int
  deriving DecidableEq, Repr

def State.values (s : State) : List Int :=
  s.grain.values ++ [s.route]

/-- The five coordinates in the store's canonical order: field `n` encodes as
`nat n = [n, 255]` for `0 < n < 255` and `nat 0 = [255]`, so 1, 2, 3, 4, 0. -/
def State.coordinates (s : State) : DeclaredResourceProjection.Values :=
  [(1, s.grain.status), (2, s.grain.remaining), (3, s.grain.reserved), (4, s.route),
    (0, s.grain.generation)]

def State.store (s : State) (task : Nat) : Store effectLayout :=
  DeclaredFields.store task s.coordinates

/-- The provider purse declares the four grain fields and its route field. -/
def recordFields : FieldClosure.FieldSet := .closed [0, 1, 2, 3, 4]

/-- A provider purse at birth: the AgentGrain birth state and no call, with
exactly its five mutable coordinates declared. -/
def initialStore (task budget : Nat) : Store effectLayout :=
  FieldClosure.declare task recordFields
    ((⟨⟨0, 0, Int.ofNat budget, 0⟩, 0⟩ : State).store task)

/-- Birth is closed under the same five-field rule the receiver enforces. -/
theorem fixture_initial_closed : FieldClosure.Closed 8784 (initialStore 8784 300000) := by
  decide

/-- The route can be written, while an unrelated sixth field remains forbidden. -/
theorem fixture_initial_field_boundary :
    FieldClosure.declaredIn 8784 (initialStore 8784 300000) 4 = true ∧
    FieldClosure.declaredIn 8784 (initialStore 8784 300000) 5 = false := by
  decide

def readState (task : Nat) (store : Store effectLayout) : Option State := do
  let grain ← AgentGrain.readState task store
  return ⟨grain, ← DeclaredFields.read task routeField store⟩

/-- The total allowance: what a settle can consume. -/
def State.budget (s : State) : Int := s.grain.remaining + s.grain.reserved

/-- What one transition consumed from the purse. -/
def charged (before after : State) : Int := before.budget - after.budget

/-! ## Store facts for the five-field record

`DeclaredFields` proves these for four fields; its helpers are private, so the
two short lemmas are restated here. -/

private theorem key_addressKey (object field : Nat) :
    StoreCodec.addressKey DeclaredEffectCell.wire (DeclaredFields.key object field).address =
      ((0 :: StreamCodec.nat.encode object).map UInt8.toNat) ++
        (digestStream.encode ⟨field⟩).map UInt8.toNat := by
  simp [StoreCodec.addressKey, StoreCodec.addressStream, FiniteDependentMapCodec.entryStream,
    DeclaredEffectCell.wire, DeclaredFields.key, StateKey.address,
    DeclaredEffectCell.stateKeyStream, StoreCodec.unitStream, List.map_append]

private theorem field_lt (object i j : Nat)
    (ordered : (digestStream.encode ⟨i⟩).map UInt8.toNat <
      (digestStream.encode ⟨j⟩).map UInt8.toNat) :
    StoreCodec.addressKey DeclaredEffectCell.wire (DeclaredFields.key object i).address <
      StoreCodec.addressKey DeclaredEffectCell.wire (DeclaredFields.key object j).address := by
  rw [key_addressKey, key_addressKey]
  exact List.append_left_lt ordered

theorem coordinates_ordered (object : Nat) (s : State) :
    (DeclaredFields.entries object s.coordinates).Pairwise
      (StoreCodec.AddressLT DeclaredEffectCell.wire) := by
  simp only [DeclaredFields.entries, State.coordinates, List.map_cons, List.map_nil]
  refine List.Pairwise.cons ?_ (List.Pairwise.cons ?_ (List.Pairwise.cons ?_
    (List.Pairwise.cons ?_ (List.Pairwise.cons ?_ List.Pairwise.nil))))
  all_goals
    intro other member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    try (rcases member with rfl | rfl | rfl | rfl <;> (apply field_lt; decide))

/-- The receiver's projection of two provider-purse stores is exactly the
scalar slots of their five canonical coordinates. -/
theorem store_projection_exact (task : Nat) (before after : State) :
    DeclaredResourceProjection.project task (before.store task) (after.store task) =
      DeclaredResourceProjection.scalarSlots before.coordinates after.coordinates := by
  unfold DeclaredResourceProjection.project DeclaredResourceProjection.values State.store
    DeclaredFields.store
  rw [StoreCodec.entries_fromEntries_of_pairwise _ _ (coordinates_ordered task before),
    StoreCodec.entries_fromEntries_of_pairwise _ _ (coordinates_ordered task after)]
  simp [DeclaredFields.entries, State.coordinates, DeclaredFields.key, StateKey.address]

/-- Each field of a provider purse reads back exactly, so the AgentGrain
reader sees the same four coordinates and the route reads back. -/
theorem readState_store (task : Nat) (s : State) :
    readState task (s.store task) = some s := by
  have distinct : ((DeclaredFields.entries task s.coordinates).map Sigma.fst).Nodup := by
    refine List.pairwise_map.mpr ((coordinates_ordered task s).imp ?_)
    intro left right less same
    unfold StoreCodec.AddressLT at less
    rw [same] at less
    exact List.lt_irrefl _ less
  have r0 : DeclaredFields.read task 0 (DeclaredFields.store task s.coordinates) =
      some s.grain.generation := StoreCodec.fromEntries_apply_of_mem _ distinct
    (entry := ⟨(DeclaredFields.key task 0).address, s.grain.generation⟩)
    (by simp [DeclaredFields.entries, State.coordinates])
  have r1 : DeclaredFields.read task 1 (DeclaredFields.store task s.coordinates) =
      some s.grain.status := StoreCodec.fromEntries_apply_of_mem _ distinct
    (entry := ⟨(DeclaredFields.key task 1).address, s.grain.status⟩)
    (by simp [DeclaredFields.entries, State.coordinates])
  have r2 : DeclaredFields.read task 2 (DeclaredFields.store task s.coordinates) =
      some s.grain.remaining := StoreCodec.fromEntries_apply_of_mem _ distinct
    (entry := ⟨(DeclaredFields.key task 2).address, s.grain.remaining⟩)
    (by simp [DeclaredFields.entries, State.coordinates])
  have r3 : DeclaredFields.read task 3 (DeclaredFields.store task s.coordinates) =
      some s.grain.reserved := StoreCodec.fromEntries_apply_of_mem _ distinct
    (entry := ⟨(DeclaredFields.key task 3).address, s.grain.reserved⟩)
    (by simp [DeclaredFields.entries, State.coordinates])
  have r4 : DeclaredFields.read task 4 (DeclaredFields.store task s.coordinates) =
      some s.route := StoreCodec.fromEntries_apply_of_mem _ distinct
    (entry := ⟨(DeclaredFields.key task 4).address, s.route⟩)
    (by simp [DeclaredFields.entries, State.coordinates])
  simp [readState, AgentGrain.readState, State.store, routeField, r0, r1, r2, r3, r4]

/-! ## The route law -/

def heldStatuses : List Int := [3, 4, 5, 7]
def freeStatuses : List Int := [0, 1, 2, 6]

/-- A reserve records a real route and holds at least its fee; a user-route
hold is exactly the fee, so a Host whose pinned fee differs from the purse's
law is refused at reserve, before anything is sent. -/
def reserveRule (schedule : Schedule) : Pred := .any [
  .all [.eq "resource/field/4/after" 1,
    .eq "resource/field/3/after" ((schedule.user : Int))],
  .all [.eq "resource/field/4/after" 2,
    .not (.le "resource/field/3/after" ((schedule.pool : Int) - 1))],
  .all [.eq "resource/field/4/after" 3,
    .not (.le "resource/field/3/after" ((schedule.homelab : Int) - 1))]]

/-- A settle charges by the route recorded at reserve. The charge is
`-(resource/pair/2/3/delta)`. Zero is the release of a call that never left
the controller (the not-sent outcome); otherwise a user-route call is charged
exactly its fee and a metered call at least its fee. -/
def settleRule (schedule : Schedule) : Pred := .any [
  .all [.eq "resource/field/4/before" 1,
    .memberOf "resource/pair/2/3/delta" [0, -((schedule.user : Int))]],
  .all [.eq "resource/field/4/before" 2,
    .any [.eq "resource/pair/2/3/delta" 0,
      .le "resource/pair/2/3/delta" (-((schedule.pool : Int)))]],
  .all [.eq "resource/field/4/before" 3,
    .any [.eq "resource/pair/2/3/delta" 0,
      .le "resource/pair/2/3/delta" (-((schedule.homelab : Int)))]]]

/-- The route law of a provider purse, over the generic receiver's
projection. It restates the budget facts of `AgentGrain.transitionPolicy` it
relies on (a continued hold moves no allowance; a settle empties the hold and
returns the uncharged rest), so its theorems need nothing else. -/
def transition (schedule : Schedule) : Pred := .all [
  .memberOf "resource/field/4/after" [0, 1, 2, 3],
  .any [
    -- The call stays in flight: the route is fixed and no allowance moves.
    .all [.memberOf "resource/field/1/before" heldStatuses,
      .memberOf "resource/field/1/after" heldStatuses,
      .eq "resource/field/4/delta" 0,
      .eq "resource/field/2/delta" 0, .eq "resource/field/3/delta" 0],
    -- No call: no route, nothing held (attach, mode, cancel, refill).
    .all [.memberOf "resource/field/1/before" freeStatuses,
      .memberOf "resource/field/1/after" freeStatuses,
      .eq "resource/field/4/before" 0, .eq "resource/field/4/after" 0,
      .eq "resource/field/3/delta" 0],
    -- Reserve: the allowance moves into the hold, under a recorded route.
    .all [.memberOf "resource/field/1/before" freeStatuses,
      .memberOf "resource/field/1/after" heldStatuses,
      .eq "resource/field/4/before" 0,
      .eq "resource/pair/2/3/delta" 0,
      reserveRule schedule],
    -- Settle: the hold empties, the route clears, the charge is the route's.
    .all [.memberOf "resource/field/1/before" heldStatuses,
      .memberOf "resource/field/1/after" freeStatuses,
      .eq "resource/field/4/after" 0,
      .eq "resource/field/3/after" 0,
      .not (.le "resource/field/2/delta" (-1)),
      settleRule schedule]]]

/-- The installed law of a provider purse: the grain policy `base` (owner,
workers, refill, management) and, for every request that can write, the
route law. Observation (1), delegation (3) and management (4, 5) write no
resource field. -/
def policy (schedule : Schedule) (base : Pred) : Pred := .all [
  base,
  .any [.memberOf "request/verb" [1, 3, 4, 5], transition schedule]]

/-- Every mutation the installed law admits satisfies the route law. -/
theorem installed_route_law (schedule : Schedule) (base : Pred) (old st : Minidregg.Pred.State)
    (accepted : eval (policy schedule base) old st = true)
    (mutation : st.get "request/verb" = some 2) :
    eval (transition schedule) old st = true := by
  unfold policy at accepted
  rw [eval_all] at accepted
  have guard := (List.all_eq_true.mp accepted)
    (.any [.memberOf "request/verb" [1, 3, 4, 5], transition schedule]) (by simp)
  rw [eval_any] at guard
  obtain ⟨branch, member, holds⟩ := List.any_eq_true.mp guard
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at member
  rcases member with rfl | rfl
  · simp [Minidregg.Pred.eval, Minidregg.Pred.evalWith, mutation] at holds
  · exact holds

/-- The slot values the route law reads, as the generic receiver projects
them from a provider purse moving from `before` to `after`. -/
structure Reads (st : Minidregg.Pred.State) (before after : State) : Prop where
  statusBefore : st.get "resource/field/1/before" = some before.grain.status
  statusAfter : st.get "resource/field/1/after" = some after.grain.status
  remainingDelta : st.get "resource/field/2/delta" =
    some (after.grain.remaining - before.grain.remaining)
  reservedAfter : st.get "resource/field/3/after" = some after.grain.reserved
  reservedDelta : st.get "resource/field/3/delta" =
    some (after.grain.reserved - before.grain.reserved)
  routeBefore : st.get "resource/field/4/before" = some before.route
  routeAfter : st.get "resource/field/4/after" = some after.route
  routeDelta : st.get "resource/field/4/delta" = some (after.route - before.route)
  budgetDelta : st.get "resource/pair/2/3/delta" =
    some (after.grain.remaining + after.grain.reserved -
      before.grain.remaining - before.grain.reserved)

set_option maxHeartbeats 2000000 in
/-- The receiver's projection of two provider purses carries exactly those
values. -/
theorem reads_projection (task : Nat) (before after : State) :
    Reads ⟨DeclaredResourceProjection.project task (before.store task) (after.store task)⟩
      before after := by
  rw [store_projection_exact]
  constructor <;>
  simp [State.coordinates, DeclaredResourceProjection.scalarSlots,
    DeclaredResourceProjection.get, DeclaredResourceProjection.fieldName,
    DeclaredResourceProjection.pairName, Minidregg.Pred.State.get,
    Nat.repr_eq_ofList_toDigits, Nat.toDigits, Nat.toDigitsCore, Nat.digitChar, toString]

/-- A grain status that holds a reservation. -/
def IsHeld (status : Int) : Prop := status = 3 ∨ status = 4 ∨ status = 5 ∨ status = 7
/-- A grain status that holds no reservation. -/
def IsFree (status : Int) : Prop := status = 0 ∨ status = 1 ∨ status = 2 ∨ status = 6

/-! The two status classes are disjoint and each has both poles: the route law's case split
reads a real distinction, not a constant. -/
theorem isHeld_three : IsHeld 3 := Or.inl rfl
theorem not_isHeld_zero : ¬ IsHeld 0 := by simp only [IsHeld]; omega
theorem isFree_zero : IsFree 0 := Or.inl rfl
theorem not_isFree_three : ¬ IsFree 3 := by simp only [IsFree]; omega
theorem not_isHeld_and_isFree (status : Int) : ¬ (IsHeld status ∧ IsFree status) := by
  unfold IsHeld IsFree; omega

/-- The route law, read as arithmetic over the projected values. -/
theorem transition_law {schedule : Schedule} {old st : Minidregg.Pred.State}
    {before after : State} (reads : Reads st before after)
    (accepted : eval (transition schedule) old st = true) :
    (after.route = 0 ∨ after.route = 1 ∨ after.route = 2 ∨ after.route = 3) ∧
    ((IsHeld before.grain.status ∧ IsHeld after.grain.status ∧ after.route = before.route ∧
        after.grain.remaining = before.grain.remaining ∧
        after.grain.reserved = before.grain.reserved) ∨
      (IsFree before.grain.status ∧ IsFree after.grain.status ∧
        before.route = 0 ∧ after.route = 0 ∧ after.grain.reserved = before.grain.reserved) ∨
      (IsFree before.grain.status ∧ IsHeld after.grain.status ∧ before.route = 0 ∧
        charged before after = 0 ∧
        ((after.route = 1 ∧ after.grain.reserved = (schedule.user : Int)) ∨
         (after.route = 2 ∧ (schedule.pool : Int) ≤ after.grain.reserved) ∨
         (after.route = 3 ∧ (schedule.homelab : Int) ≤ after.grain.reserved))) ∨
      (IsHeld before.grain.status ∧ IsFree after.grain.status ∧ after.route = 0 ∧
        after.grain.reserved = 0 ∧ before.grain.remaining ≤ after.grain.remaining ∧
        ((before.route = 1 ∧ (charged before after = 0 ∨
            charged before after = (schedule.user : Int))) ∨
         (before.route = 2 ∧ (charged before after = 0 ∨
            (schedule.pool : Int) ≤ charged before after)) ∨
         (before.route = 3 ∧ (charged before after = 0 ∨
            (schedule.homelab : Int) ≤ charged before after))))) := by
  obtain ⟨sb, sa, rd, ra, resd, rb, rta, rtd, bd⟩ := reads
  simp [transition, reserveRule, settleRule, heldStatuses, freeStatuses, Minidregg.Pred.eval,
    Minidregg.Pred.evalWith, Pred.all, Pred.any, PredList.ofList, Minidregg.Pred.evalWithAll,
    Minidregg.Pred.evalWithAny, sb, sa, rd, ra, resd, rb, rta, rtd, bd] at accepted
  unfold IsHeld IsFree charged State.budget
  obtain ⟨hr, h | h | h | h⟩ := accepted
  · exact ⟨hr, Or.inl (by omega)⟩
  · exact ⟨hr, Or.inr (Or.inl (by omega))⟩
  · exact ⟨hr, Or.inr (Or.inr (Or.inl (by omega)))⟩
  · exact ⟨hr, Or.inr (Or.inr (Or.inr (by omega)))⟩

/-! ## Theorems -/

/-- **A call with no route opens no hold.** An admitted transition from a
purse with no call in flight that leaves the route at 0 leaves the purse
free and its hold unchanged: there is no reserve under `none`. -/
theorem none_route_reserves_nothing {schedule : Schedule} {old st : Minidregg.Pred.State}
    {before after : State} (reads : Reads st before after)
    (accepted : eval (transition schedule) old st = true)
    (free : IsFree before.grain.status) (none : after.route = 0) :
    IsFree after.grain.status ∧ after.grain.reserved = before.grain.reserved := by
  obtain ⟨hr, h | h | h | h⟩ := transition_law reads accepted <;>
    (try simp only [IsFree, IsHeld] at *) <;> omega

/-- **A user-route call is charged its per-operation fee and nothing else.**
Its hold is exactly the fee, and its settle charges the fee or (a call that
never left) nothing; no token count enters. -/
theorem user_route_charges_per_op_only {schedule : Schedule} {old st : Minidregg.Pred.State}
    {before after : State} (reads : Reads st before after)
    (accepted : eval (transition schedule) old st = true)
    (held : IsHeld before.grain.status) (user : before.route = 1)
    (settled : IsFree after.grain.status) :
    charged before after = 0 ∨ charged before after = (schedule.user : Int) := by
  obtain ⟨hr, h | h | h | h⟩ := transition_law reads accepted <;>
    (try simp only [IsFree, IsHeld] at *) <;> omega

theorem user_route_holds_per_op {schedule : Schedule} {old st : Minidregg.Pred.State}
    {before after : State} (reads : Reads st before after)
    (accepted : eval (transition schedule) old st = true)
    (free : IsFree before.grain.status) (user : after.route = 1) :
    IsHeld after.grain.status ∧ after.grain.reserved = (schedule.user : Int) ∧
      charged before after = 0 := by
  obtain ⟨hr, h | h | h | h⟩ := transition_law reads accepted <;>
    (try simp only [IsFree, IsHeld] at *) <;> omega

/-- **A pool-route call pays the metered tariff.** The kernel bounds what it
can see: nothing (a call that never left), or at least the pool fee and at
most the hold. The metered part is the Host's quote of the retained response
(`ProviderMetering.Quote.pool_is_metered`). -/
theorem pool_route_charges_metered {schedule : Schedule} {old st : Minidregg.Pred.State}
    {before after : State} (reads : Reads st before after)
    (accepted : eval (transition schedule) old st = true)
    (held : IsHeld before.grain.status) (pool : before.route = 2)
    (settled : IsFree after.grain.status) :
    charged before after = 0 ∨
      ((schedule.pool : Int) ≤ charged before after ∧
        charged before after ≤ before.grain.reserved) := by
  obtain ⟨hr, h | h | h | h⟩ := transition_law reads accepted <;>
    (try simp only [IsFree, IsHeld, charged, State.budget] at *) <;> omega

theorem homelab_route_charges_metered {schedule : Schedule} {old st : Minidregg.Pred.State}
    {before after : State} (reads : Reads st before after)
    (accepted : eval (transition schedule) old st = true)
    (held : IsHeld before.grain.status) (homelab : before.route = 3)
    (settled : IsFree after.grain.status) :
    charged before after = 0 ∨
      ((schedule.homelab : Int) ≤ charged before after ∧
        charged before after ≤ before.grain.reserved) := by
  obtain ⟨hr, h | h | h | h⟩ := transition_law reads accepted <;>
    (try simp only [IsFree, IsHeld, charged, State.budget] at *) <;> omega

/-- **The settle never charges more than the hold**, on every route. -/
theorem charge_le_reserve {schedule : Schedule} {old st : Minidregg.Pred.State}
    {before after : State} (reads : Reads st before after)
    (accepted : eval (transition schedule) old st = true)
    (held : IsHeld before.grain.status) (settled : IsFree after.grain.status) :
    0 ≤ charged before after ∧ charged before after ≤ before.grain.reserved := by
  obtain ⟨hr, h | h | h | h⟩ := transition_law reads accepted <;>
    (try simp only [IsFree, IsHeld, charged, State.budget] at *) <;> omega

/-- **A call reserved as pool cannot settle as user.** While it is held its
route stays pool; the transition that ends the hold clears the route and is
charged by the pool rule. -/
theorem route_cannot_downgrade_at_settle {schedule : Schedule} {old st : Minidregg.Pred.State}
    {before after : State} (reads : Reads st before after)
    (accepted : eval (transition schedule) old st = true)
    (held : IsHeld before.grain.status) (pool : before.route = 2) :
    (IsHeld after.grain.status ∧ after.route = 2) ∨
      (IsFree after.grain.status ∧ after.route = 0 ∧
        (charged before after = 0 ∨ (schedule.pool : Int) ≤ charged before after)) := by
  obtain ⟨hr, h | h | h | h⟩ := transition_law reads accepted <;>
    (try simp only [IsFree, IsHeld] at *) <;> omega

/-- The concrete downgrade: a pool hold settled for the user fee, when the
user fee is positive and below the pool fee, is refused. -/
theorem pool_hold_refuses_the_user_fee {schedule : Schedule} {old st : Minidregg.Pred.State}
    {before after : State} (reads : Reads st before after)
    (held : IsHeld before.grain.status) (pool : before.route = 2)
    (settled : IsFree after.grain.status)
    (cheaper : 0 < schedule.user ∧ schedule.user < schedule.pool)
    (asUser : charged before after = (schedule.user : Int)) :
    eval (transition schedule) old st = false := by
  cases h : eval (transition schedule) old st with
  | false => rfl
  | true =>
      rcases route_cannot_downgrade_at_settle reads h held pool with d | d <;>
        (try simp only [IsFree, IsHeld] at *) <;> omega

/-- An admitted run of transitions in which every state reached is held. -/
inductive HeldRun (schedule : Schedule) : State → State → Prop where
  | refl (s : State) : HeldRun schedule s s
  | step {x y z : State} (st : Minidregg.Pred.State) (old : Minidregg.Pred.State)
      (reads : Reads st x y) (accepted : eval (transition schedule) old st = true)
      (held : IsHeld y.grain.status) (rest : HeldRun schedule y z) : HeldRun schedule x z

theorem HeldRun.route {schedule : Schedule} {x z : State} (run : HeldRun schedule x z)
    (held : IsHeld x.grain.status) : IsHeld z.grain.status ∧ z.route = x.route := by
  induction run with
  | refl => exact ⟨held, rfl⟩
  | step st old reads accepted heldY _ ih =>
      obtain ⟨hz, rz⟩ := ih heldY
      refine ⟨hz, ?_⟩
      obtain ⟨hr, h | h | h | h⟩ := transition_law reads accepted <;>
        (try simp only [IsFree, IsHeld] at *) <;> omega

/-- The charge rule of one route. -/
def SettledBy (schedule : Schedule) (route : Route) (charge : Int) : Prop :=
  match route with
  | .user => charge = 0 ∨ charge = (schedule.user : Int)
  | .pool => charge = 0 ∨ (schedule.pool : Int) ≤ charge
  | .homelab => charge = 0 ∨ (schedule.homelab : Int) ≤ charge

/-- A reserve records a real route. -/
theorem reserve_records_route {schedule : Schedule} {old st : Minidregg.Pred.State}
    {before after : State} (reads : Reads st before after)
    (accepted : eval (transition schedule) old st = true)
    (free : IsFree before.grain.status) (held : IsHeld after.grain.status) :
    after.route = 1 ∨ after.route = 2 ∨ after.route = 3 := by
  obtain ⟨hr, h | h | h | h⟩ := transition_law reads accepted <;>
    (try simp only [IsFree, IsHeld] at *) <;> omega

/-- A settle clears the route. -/
theorem settle_clears_route {schedule : Schedule} {old st : Minidregg.Pred.State}
    {before after : State} (reads : Reads st before after)
    (accepted : eval (transition schedule) old st = true)
    (held : IsHeld before.grain.status) (free : IsFree after.grain.status) :
    after.route = 0 := by
  obtain ⟨hr, h | h | h | h⟩ := transition_law reads accepted <;>
    (try simp only [IsFree, IsHeld] at *) <;> omega

/-- **The settle is charged by the route recorded at reserve.** Whatever
admitted transitions keep the call held in between (interruption, restart
fencing, a witness), the route the reserve recorded is the route the settle
is charged by. -/
theorem settle_route_matches_reserve {schedule : Schedule}
    {r0 r1 r2 r3 : State} {old0 st0 old2 st2 : Minidregg.Pred.State}
    (reads0 : Reads st0 r0 r1) (reserve : eval (transition schedule) old0 st0 = true)
    (free0 : IsFree r0.grain.status) (held1 : IsHeld r1.grain.status)
    (run : HeldRun schedule r1 r2)
    (reads2 : Reads st2 r2 r3) (settle : eval (transition schedule) old2 st2 = true)
    (free3 : IsFree r3.grain.status) :
    ∃ route : Route, r1.route = route.code ∧ r2.route = route.code ∧
      SettledBy schedule route (charged r2 r3) ∧ r3.route = 0 := by
  have code := reserve_records_route reads0 reserve free0 held1
  obtain ⟨held2, same⟩ := run.route held1
  have cleared := settle_clears_route reads2 settle held2 free3
  rcases code with c | c | c
  · exact ⟨.user, c, same.trans c,
      user_route_charges_per_op_only reads2 settle held2 (same.trans c) free3, cleared⟩
  · refine ⟨.pool, c, same.trans c, ?_, cleared⟩
    rcases pool_route_charges_metered reads2 settle held2 (same.trans c) free3 with z | ⟨low, _⟩
    · exact Or.inl z
    · exact Or.inr low
  · refine ⟨.homelab, c, same.trans c, ?_, cleared⟩
    rcases homelab_route_charges_metered reads2 settle held2 (same.trans c) free3 with
      z | ⟨low, _⟩
    · exact Or.inl z
    · exact Or.inr low

/-! ## Authoring: the five writes of one provider-purse transition -/

/-- The transition a grain operation makes on a provider purse: a reserve
records the route code `route`, a settle clears it, everything else keeps it. -/
def after (operation : AgentGrain.Operation) (route : Int) (s : State) : State :=
  match operation with
  | .reserve _ => ⟨operation.after s.grain, route⟩
  | .settle _ => ⟨operation.after s.grain, 0⟩
  | _ => ⟨operation.after s.grain, s.route⟩

/-- Every operation compares all five old coordinates, including unchanged
ones, against the durable store. A settle authored from a `before` that names
another route than the store holds fails that comparison. -/
def actions (task : Nat) (before after : State) : List Action :=
  (List.range 5).zipWith (fun n pair =>
    .write (DeclaredFields.key task n) (some pair.1) pair.2) (before.values.zip after.values)

def target (operation : AgentGrain.Operation) (route : Int) (task : Nat)
    (capability : CapabilityId) (expectedRoot : Digest) (before : State)
    (observeCapability : Option CapabilityId := none) : DeclaredResourceController.Target :=
  { kind := .object, target := task, capability := capability,
    observeCapability := observeCapability, schemaVersion := 1,
    expectedTargetRoot := expectedRoot,
    payload := .scalar (actions task before (after operation route before)) }

/-! ## Poles: the law is satisfiable and refutes -/

def fixtureSchedule : Schedule := ⟨5, 7, 3⟩

private def run (before after : State) : Bool :=
  eval (transition fixtureSchedule) ⟨[]⟩
    ⟨DeclaredResourceProjection.scalarSlots before.coordinates after.coordinates⟩

/-- A user-route reserve of exactly the fee, then its settle for the fee. -/
theorem fixture_user_call_accepted :
    run ⟨⟨1, 1, 100, 0⟩, 0⟩ ⟨⟨1, 3, 95, 5⟩, 1⟩ = true ∧
      run ⟨⟨1, 3, 95, 5⟩, 1⟩ ⟨⟨1, 1, 95, 0⟩, 0⟩ = true := by decide

/-- A user-route hold larger than the fee is refused; a user settle charging
more than the fee (here the whole of a pool-sized hold) cannot even be held. -/
theorem fixture_user_overhold_refused :
    run ⟨⟨1, 1, 100, 0⟩, 0⟩ ⟨⟨1, 3, 70, 30⟩, 1⟩ = false := by decide

/-- A user settle that charges one credit less than the fee is refused. -/
theorem fixture_user_partial_refused :
    run ⟨⟨1, 3, 95, 5⟩, 1⟩ ⟨⟨1, 1, 96, 0⟩, 0⟩ = false := by decide

/-- A pool call: hold 30, settle 7 (fee) + 93 metered is refused (over the
hold), 7 + 13 accepted, 6 (below the fee) refused, 0 (never sent) accepted. -/
theorem fixture_pool_settles :
    run ⟨⟨1, 3, 70, 30⟩, 2⟩ ⟨⟨1, 1, 80, 0⟩, 0⟩ = true ∧
      run ⟨⟨1, 3, 70, 30⟩, 2⟩ ⟨⟨1, 1, 94, 0⟩, 0⟩ = false ∧
      run ⟨⟨1, 3, 70, 30⟩, 2⟩ ⟨⟨1, 1, 100, 0⟩, 0⟩ = true ∧
      run ⟨⟨1, 3, 70, 30⟩, 2⟩ ⟨⟨1, 1, 60, 0⟩, 0⟩ = false := by decide

/-- No route, no reserve. -/
theorem fixture_none_reserve_refused :
    run ⟨⟨1, 1, 100, 0⟩, 0⟩ ⟨⟨1, 3, 70, 30⟩, 0⟩ = false := by decide

/-- A pool hold cannot be relabelled user while held, nor settled for the
user fee (5 < 7). -/
theorem fixture_pool_relabel_refused :
    run ⟨⟨1, 3, 70, 30⟩, 2⟩ ⟨⟨1, 3, 70, 30⟩, 1⟩ = false ∧
      run ⟨⟨1, 3, 70, 30⟩, 2⟩ ⟨⟨1, 1, 95, 0⟩, 0⟩ = false := by decide

/-- Interruption keeps the route; the interrupted hold settles by it. -/
theorem fixture_interrupted_pool :
    run ⟨⟨1, 3, 70, 30⟩, 2⟩ ⟨⟨2, 5, 70, 30⟩, 2⟩ = true ∧
      run ⟨⟨2, 5, 70, 30⟩, 2⟩ ⟨⟨2, 0, 80, 0⟩, 0⟩ = true := by decide

#assert_axioms fixture_initial_closed
#assert_axioms fixture_initial_field_boundary
#assert_axioms coordinates_ordered
#assert_axioms store_projection_exact
#assert_axioms readState_store
#assert_axioms installed_route_law
#assert_axioms reads_projection
#assert_axioms transition_law
#assert_axioms isHeld_three
#assert_axioms not_isHeld_zero
#assert_axioms isFree_zero
#assert_axioms not_isFree_three
#assert_axioms not_isHeld_and_isFree
#assert_axioms none_route_reserves_nothing
#assert_axioms user_route_charges_per_op_only
#assert_axioms user_route_holds_per_op
#assert_axioms pool_route_charges_metered
#assert_axioms homelab_route_charges_metered
#assert_axioms charge_le_reserve
#assert_axioms route_cannot_downgrade_at_settle
#assert_axioms pool_hold_refuses_the_user_fee
#assert_axioms HeldRun.route
#assert_axioms reserve_records_route
#assert_axioms settle_clears_route
#assert_axioms settle_route_matches_reserve
#assert_axioms fixture_user_call_accepted
#assert_axioms fixture_user_overhold_refused
#assert_axioms fixture_user_partial_refused
#assert_axioms fixture_pool_settles
#assert_axioms fixture_none_reserve_refused
#assert_axioms fixture_pool_relabel_refused
#assert_axioms fixture_interrupted_pool

end Minidregg.Kernel.ProviderRoute
