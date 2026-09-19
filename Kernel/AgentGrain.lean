/- Source-authored execution resource for hosted agent tasks.
A grain may own many such task resources. Its stable task identity is the
ordinary object id, never a transport connection or a process id. The four
fields are execution generation, status, remaining allowance and unresolved
reservation, in integer permission micro-units. These are scoped spend
allowances, not Book balances or $DREGG. Birth does not prove funding; a
broker must accept only explicitly allocated task resources, never an
arbitrary caller-authored initial allowance. No field is a policy revision or grant
revocation generation. A stopped status proves admission fencing, not that
an external process or provider actually stopped. -/
import Kernel.DeclaredResourceProjection
import Kernel.ResourceTransaction
import Pred.Core

namespace Minidregg.Kernel.AgentGrain
open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.EffectDeclaration
open Minidregg.Theory.DeclaredActionLowering
open Minidregg.Compiler.DeclaredEffectPageMaterializer
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

def key (task : Nat) (field : Nat) : StateKey := .objectField ⟨task⟩ ⟨field⟩

def State.page (s : State) (domain : Digest) (task : Nat) : Page :=
  ⟨domain, task % shardCount,
    some ⟨key task 0, s.generation⟩, some ⟨key task 1, s.status⟩,
    some ⟨key task 2, s.remaining⟩, some ⟨key task 3, s.reserved⟩⟩

def initialPage (domain : Digest) (task budget : Nat) : Page :=
  (⟨0,0,Int.ofNat budget,0⟩ : State).page domain task

def readState (task : Nat) (page : Page) : Option State := do
  let read := fun n => (page.entries.find? (fun e => e.key == key task n)).map (·.value)
  return ⟨← read 0, ← read 1, ← read 2, ← read 3⟩

/-- Every operation compares all four old coordinates, including unchanged
ones. The generic declared receiver checks these writes against the durable
page and binds the exact actions into authorization and replay identity. -/
def actions (task : Nat) (before after : State) : List Action :=
  (List.range 4).zipWith (fun n pair =>
    .write (key task n) (some pair.1) pair.2) (before.values.zip after.values)

/-- Projection vocabulary required in the generic resource receiver. Both
sides are decoded from canonical pages, never supplied as decision bits by a
host. Deltas preserve arithmetic over the exact integer state. -/
def State.coordinates (s : State) : DeclaredResourceProjection.Values :=
  [(0,s.generation),(1,s.status),(2,s.remaining),(3,s.reserved)]

def slots (before after : State) : List (String × Int) :=
  DeclaredResourceProjection.scalarSlots before.coordinates after.coordinates

def project := DeclaredResourceProjection.project

theorem page_projection_exact (domain : Digest) (task : Nat) (before after : State) :
    DeclaredResourceProjection.project task (before.page domain task) (after.page domain task) =
      slots before after := by
  simp [DeclaredResourceProjection.project, DeclaredResourceProjection.values,
    Page.entries, State.page, key, slots, State.coordinates]

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
    -- Break/cancel fences old execution even when remote effects are unresolved.
    ([ (1,0), (3,5), (0,6), (1,6), (2,6), (3,7), (4,7), (5,7) ].map
      fun p => edge p.1 p.2 1 [unchangedBudget]))]

/-- Management is deliberately lockable. The caller may supply an explicit
management rule; it governs policy installation and capability revocation, never mutation.
Ordinary observation/delegation still require the native capability checker. -/
def policy (management : Pred := .any []) : Pred := .any [
  .all [.eq "request/verb" 2, transitionPolicy],
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
  | cancel
  deriving DecidableEq, Repr

def Operation.after (operation : Operation) (s : State) : State :=
  match operation with
  | .input => s
  | .attach soft => { s with generation := s.generation + 1, status := (if soft then 2 else 1) }
  | .mode soft => { s with status := (if soft then 2 else 1) }
  | .reserve amount => AgentGrain.reserve s amount
  | .settle charge => AgentGrain.settle s charge
  | .disconnect => if s.status = 2 ∨ s.status = 4 then s else trip s
  | .cancel => { s with
      generation := s.generation + 1
      status := (if s.status = 3 ∨ s.status = 4 ∨ s.status = 5 then 7 else 6) }

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
def Operation.command (operation : Operation) (subject : SubjectId) (authorityRoot : Digest)
    (nonce task : Nat) (capability : CapabilityId) (expectedRoot : Digest) (before : State)
    (publications : List DeclaredResourceController.Target := [])
    (observeCapability : Option CapabilityId := none) :
    DeclaredResourceController.Command :=
  { subject := subject, expectedAuthorityRoot := authorityRoot, nonce := nonce,
    targets := operation.target task capability expectedRoot before observeCapability :: publications }

theorem operation_target_actions_exact (operation : Operation) (task : Nat)
    (capability : CapabilityId) (expectedRoot : Digest) (before : State)
    (observeCapability : Option CapabilityId) :
    (operation.target task capability expectedRoot before observeCapability).payload =
      .scalar (AgentGrain.actions task before (operation.after before)) := rfl

theorem operation_command_retains_publications (operation : Operation) (subject : SubjectId)
    (authorityRoot : Digest) (nonce task : Nat) (capability : CapabilityId)
    (expectedRoot : Digest) (before : State) (publications : List DeclaredResourceController.Target)
    (observeCapability : Option CapabilityId) :
    (operation.command subject authorityRoot nonce task capability expectedRoot before publications
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

theorem hard_trip_invalidates_generation (s : State) :
    (trip s).generation ≠ s.generation := by simp [trip]

theorem tripped_worker_refused (before after : State) :
    eval (executionCaveat before.generation) ⟨[]⟩
      ⟨("request/verb",2) :: slots (trip before) after⟩ ≠ true := by
  intro admitted
  exact hard_trip_invalidates_generation before
    (worker_generation_exact (trip before) after before.generation admitted).1

end Minidregg.Kernel.AgentGrain
