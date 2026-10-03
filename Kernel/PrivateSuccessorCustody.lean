/-
Persistent identities and one-use resource transitions for a private successor.
This is an executable journal model, not MPC, disk durability or a sharing proof.
The exact native IntentRecord is retained. Holder/private-output qualification
and physical monotonic persistence are explicit obligations at the receiving seam.
-/
import Kernel.DurableReceiver
import Theory.AssertAxioms

namespace Minidregg.Kernel.PrivateSuccessorCustody

open Minidregg.Theory.TypedAuthorization
open Minidregg.Kernel.DurableReceiver
set_option autoImplicit false

structure GenerationKey where
  invocation : Digest
  commandBytes : List UInt8
  attempt : Nat
  generation : Nat
  configuration : Digest
  deriving DecidableEq, Repr

/-- Internal/private data; serializing this is not permission to publish holders. -/
structure Descriptor where
  key : GenerationKey
  exactSuccessor : IntentRecord
  holderIds : List Nat
  threshold : Nat
  recoveryBytes : List UInt8

/-- A qualification obligation, not an implementation of sharing or recovery.
`privateRecovery` must be discharged for the actual sharing representation.
A numerical quorum alone cannot construct this token. -/
structure Qualified (descriptor : Descriptor) (corrupt : Nat → Bool)
    (privateRecovery : Descriptor → Prop) : Prop where
  holdersDistinct : descriptor.holderIds.Nodup
  thresholdPositive : 0 < descriptor.threshold
  enoughHonest : descriptor.threshold ≤
    (descriptor.holderIds.filter fun holder => !corrupt holder).length
  recoverable : privateRecovery descriptor

inductive CorrelationPurpose
  | triple | agreementCoin | holderOutputPad | audienceReleasePad
  deriving DecidableEq, Repr

/-- Pool identity is stable across attempts, configurations and purposes. Changing
any of those labels may NEVER make an already allocated physical row fresh. -/
structure CorrelationId where
  /-- Stable identifier of the physical correlation pool, across reconfiguration. -/
  pool : Digest
  row : Nat
  deriving DecidableEq, Repr

inductive Consumption
  | reserved | consumed
  deriving DecidableEq, Repr

structure Allocation where
  correlation : CorrelationId
  generation : GenerationKey
  purpose : CorrelationPurpose
  state : Consumption
  deriving DecidableEq, Repr

structure Journal where
  /-- Monotonic allocation tombstones. No transition removes one. -/
  spent : List CorrelationId
  allocations : List Allocation
  deriving DecidableEq, Repr

def Journal.empty : Journal := ⟨[], []⟩

/-- Persist the returned journal BEFORE exposing the allocated secret row.
Returning `none` includes retry of the same allocation: recover its stored
protocol transcript instead of handing out another one-use secret. -/
def reserve (journal : Journal) (id : CorrelationId) (generation : GenerationKey)
    (purpose : CorrelationPurpose) :
    Option Journal :=
  if id ∈ journal.spent then none
  else some ⟨id :: journal.spent,
    ⟨id, generation, purpose, .reserved⟩ :: journal.allocations⟩

/-- Consumption or uncertain crash burns the allocation. Reserved already
forbids reuse; this marks status without weakening the monotonic frontier. -/
def burn (journal : Journal) (id : CorrelationId) : Journal :=
  { journal with allocations := journal.allocations.map fun allocation =>
      if allocation.correlation = id then { allocation with state := .consumed }
      else allocation }

@[simp] theorem burn_spent (journal : Journal) (id : CorrelationId) :
    (burn journal id).spent = journal.spent := rfl

theorem reserve_spent {journal next : Journal} {id : CorrelationId}
    {generation : GenerationKey} {purpose : CorrelationPurpose}
    (accepted : reserve journal id generation purpose = some next) :
    next.spent = id :: journal.spent := by
  unfold reserve at accepted
  split at accepted
  · cases accepted
  · cases accepted
    rfl

theorem reserve_never_reassigns {journal next : Journal} {id : CorrelationId}
    {generation : GenerationKey} {purpose : CorrelationPurpose}
    (accepted : reserve journal id generation purpose = some next)
    (otherGeneration : GenerationKey) (otherPurpose : CorrelationPurpose) :
    reserve next id otherGeneration otherPurpose = none := by
  simp [reserve, reserve_spent accepted]

theorem burn_never_reassigns {journal next : Journal} {id : CorrelationId}
    {generation : GenerationKey} {purpose : CorrelationPurpose}
    (accepted : reserve journal id generation purpose = some next)
    (otherGeneration : GenerationKey) (otherPurpose : CorrelationPurpose) :
    reserve (burn next id) id otherGeneration otherPurpose = none := by
  simp [reserve, reserve_spent accepted]

theorem reserve_preserves_spent {journal next : Journal} {id old : CorrelationId}
    {generation : GenerationKey} {purpose : CorrelationPurpose}
    (accepted : reserve journal id generation purpose = some next)
    (wasSpent : old ∈ journal.spent) : old ∈ next.spent := by
  rw [reserve_spent accepted]
  exact List.mem_cons_of_mem _ wasSpent

inductive Phase
  | retained | prepared | committed | applied | aborted
  deriving DecidableEq, Repr

inductive Event
  | prepare | commit | apply | abort
  deriving DecidableEq, Repr

/-- No timeout event exists. In particular, prepared cannot expire locally. -/
def advance : Phase → Event → Option Phase
  | .retained, .prepare => some .prepared
  | .retained, .abort => some .aborted
  | .prepared, .commit => some .committed
  | .prepared, .abort => some .aborted
  | .committed, .apply => some .applied
  | .applied, .apply => some .applied
  | _, _ => none

/-- Calling `advance` is not authorization. The joint receiver must supply the
matching authoritative decision for commit/abort and reservation for prepare. -/
structure Record where
  descriptor : Descriptor
  phase : Phase

def transition (record : Record) (event : Event) : Option Record :=
  (advance record.phase event).map fun phase => { record with phase := phase }

theorem transition_exact_generation {record next : Record} {event : Event}
    (accepted : transition record event = some next) :
    next.descriptor = record.descriptor := by
  unfold transition at accepted
  cases step : advance record.phase event with
  | none => simp [step] at accepted
  | some phase =>
    simp only [step, Option.map_some, Option.some.injEq] at accepted
    cases accepted
    rfl

theorem transition_exact_successor {record next : Record} {event : Event}
    (accepted : transition record event = some next) :
    next.descriptor.exactSuccessor = record.descriptor.exactSuccessor := by
  rw [transition_exact_generation accepted]

@[simp] theorem committed_cannot_abort : advance .committed .abort = none := rfl
@[simp] theorem applied_cannot_abort : advance .applied .abort = none := rfl
@[simp] theorem aborted_cannot_commit : advance .aborted .commit = none := rfl
@[simp] theorem applied_replay : advance .applied .apply = some .applied := rfl

/-- A re-sharing transition is not mixed-share recovery: the caller must prove
same exact native successor and the new representation's recovery qualification.
No equation here licenses combining shares from parent and child generations. -/
structure Descendant (parent child : Descriptor)
    (privateRecovery : Descriptor → Prop) : Prop where
  invocationExact : child.key.invocation = parent.key.invocation
  commandExact : child.key.commandBytes = parent.key.commandBytes
  semanticSuccessorExact : child.exactSuccessor = parent.exactSuccessor
  freshGeneration : child.key ≠ parent.key
  childRecoverable : privateRecovery child

/-- Physical persistence must preserve this monotonic order across recovery.
Integrity/authentication of a stale snapshot is insufficient. -/
def Extends (new old : Journal) : Prop :=
  ∀ id, id ∈ old.spent → id ∈ new.spent

theorem reserve_extends {journal next : Journal} {id : CorrelationId}
    {generation : GenerationKey} {purpose : CorrelationPurpose}
    (accepted : reserve journal id generation purpose = some next) :
    Extends next journal := fun _ h => reserve_preserves_spent accepted h

theorem burn_extends (journal : Journal) (id : CorrelationId) :
    Extends (burn journal id) journal := fun _ h => h

#assert_axioms reserve_never_reassigns
#assert_axioms burn_never_reassigns
#assert_axioms transition_exact_generation
#assert_axioms transition_exact_successor
#assert_axioms reserve_extends

end Minidregg.Kernel.PrivateSuccessorCustody
