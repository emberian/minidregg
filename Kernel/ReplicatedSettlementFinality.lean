/-
# Kernel.ReplicatedSettlementFinality -- quorum safety above framed WALs

`FramedWalRefinement` gives one byte-framed device an exact linearization point.
It does not say which replica may linearize, how replicas agree on a log, or
when a client may call a transaction final.  This module adds a deliberately
small replicated-settlement model:

* candidates carry an epoch and an exact log prefix ending in one durable
  intent;
* a quorum certificate consists of actual votes recorded in a vote book;
* every replica's votes must be log-prefix compatible, including across epoch
  changes;
* intersecting quorums therefore cannot finalize different transactions at
  the same log slot;
* a failover-ready replica must decode the exact finalized framed-WAL log, so
  recovery and idempotent replay are inherited from `DurableCommitProtocol`.

Safety and liveness are separate.  Safety needs quorum intersection and the
prefix discipline.  Progress is proved only from an online quorum, eventual
network delivery, and replica responsiveness.  These are explicit premises,
not consequences of the safety model.

**Trust ceiling.**  This is not a consensus implementation, a network model,
or a proof about Raft/Paxos, clocks, failure detectors, disks, or partitions.
A deployment must refine real voting, epoch handoff, transport, and storage
transitions to the carriers below.  No availability or termination is inferred
without the stated premises.
-/
import Kernel.FramedWalRefinement
import Kernel.DurableDataIntent

namespace Minidregg.Kernel.ReplicatedSettlementFinality

open Minidregg.Theory
open Minidregg.Kernel.DurableCommitProtocol
open Minidregg.Kernel.FramedWalRefinement

set_option autoImplicit false

universe u v w x n c

variable {TxId : Type u} {CellId : Type v} {Nullifier : Type w}
  {Event : Type x}

abbrev WalIntent := Intent TxId CellId Nullifier Event

/-! ## Exact epoch/log candidates -/

/-- One proposal extends an exact prefix by exactly one durable intent.  The
slot is derived from the prefix length, never supplied as independent data. -/
structure Candidate
    (TxId : Type u) (CellId : Type v) (Nullifier : Type w) (Event : Type x) where
  epoch : Nat
  priorLog : List (Intent TxId CellId Nullifier Event)
  intent : Intent TxId CellId Nullifier Event

namespace Candidate

variable (candidate : Candidate TxId CellId Nullifier Event)

def slot : Nat := candidate.priorLog.length

def log : List (WalIntent (TxId := TxId) (CellId := CellId)
    (Nullifier := Nullifier) (Event := Event)) :=
  candidate.priorLog ++ [candidate.intent]

@[simp] theorem log_length : candidate.log.length = candidate.slot + 1 := by
  simp [log, slot]

@[simp] theorem log_getLast? : candidate.log.getLast? = some candidate.intent := by
  simp [log]

/-- Exact payload-bearing `DataIntent` values enter replication only through
their lossless durable erasure.  Canonical post bytes and read guards remain in
the `ReplayEnvelope`, so replication does not collapse data identity to roots. -/
def ofData
    {rootBytes : List UInt8 -> TypedAuthorization.Digest}
    (epoch : Nat)
    (prior : List (Intent
      Minidregg.Kernel.DurableDataIntent.TransactionId
      Minidregg.Kernel.DurableDataIntent.CellId
      Minidregg.Kernel.DurableDataIntent.StableNullifier
      Minidregg.Kernel.DurableDataIntent.ReplayEnvelope))
    (intent : Minidregg.Kernel.DurableDataIntent.DataIntent rootBytes) :
    Candidate
      Minidregg.Kernel.DurableDataIntent.TransactionId
      Minidregg.Kernel.DurableDataIntent.CellId
      Minidregg.Kernel.DurableDataIntent.StableNullifier
      Minidregg.Kernel.DurableDataIntent.ReplayEnvelope where
  epoch := epoch
  priorLog := prior
  intent := intent.erase

@[simp] theorem ofData_intent
    {rootBytes : List UInt8 -> TypedAuthorization.Digest}
    (epoch : Nat)
    (prior : List (Intent
      Minidregg.Kernel.DurableDataIntent.TransactionId
      Minidregg.Kernel.DurableDataIntent.CellId
      Minidregg.Kernel.DurableDataIntent.StableNullifier
      Minidregg.Kernel.DurableDataIntent.ReplayEnvelope))
    (intent : Minidregg.Kernel.DurableDataIntent.DataIntent rootBytes) :
    (ofData epoch prior intent).intent = intent.erase := rfl

end Candidate

/-! ## Quorums, votes, and safety -/

/-- A quorum system exposes only the safety fact needed here: any two admitted
quorums share a node.  It does not prescribe majority arithmetic or membership
reconfiguration. -/
structure QuorumSystem (Node : Type n) [DecidableEq Node] where
  isQuorum : Finset Node -> Prop
  intersects : forall left right,
    isQuorum left -> isQuorum right ->
      exists node, node ∈ left ∧ node ∈ right

variable {Node : Type n} [DecidableEq Node]

abbrev VoteBook := Node ->
  List (Candidate TxId CellId Nullifier Event)

/-- Honest replica discipline across all epochs and slots.  Any two candidates
recorded by one replica must describe comparable exact logs.  This is the
lock/epoch-handoff obligation a concrete consensus implementation must prove. -/
structure PrefixDiscipline
    (book : VoteBook (Node := Node) (TxId := TxId) (CellId := CellId)
      (Nullifier := Nullifier) (Event := Event)) : Prop where
  compatible : forall node left right,
    left ∈ book node -> right ∈ book node ->
      left.log.IsPrefix right.log ∨ right.log.IsPrefix left.log

/-- A finality certificate contains the actual voter set and evidence that
every voter recorded this exact epoch/log candidate. -/
structure Finalized
    (quorums : QuorumSystem Node)
    (book : VoteBook (Node := Node) (TxId := TxId) (CellId := CellId)
      (Nullifier := Nullifier) (Event := Event))
    (candidate : Candidate TxId CellId Nullifier Event) : Type (max u v w x n) where
  voters : Finset Node
  quorum : quorums.isQuorum voters
  voted : forall node, node ∈ voters -> candidate ∈ book node

/-- Intersecting quorum certificates inherit one common replica's prefix
discipline.  Finalized logs can be equal or extend one another; they cannot
fork. -/
theorem finalized_logs_comparable
    {quorums : QuorumSystem Node}
    {book : VoteBook (Node := Node) (TxId := TxId) (CellId := CellId)
      (Nullifier := Nullifier) (Event := Event)}
    (discipline : PrefixDiscipline book)
    {left right : Candidate TxId CellId Nullifier Event}
    (leftFinal : Finalized quorums book left)
    (rightFinal : Finalized quorums book right) :
    left.log.IsPrefix right.log ∨ right.log.IsPrefix left.log := by
  rcases quorums.intersects leftFinal.voters rightFinal.voters
    leftFinal.quorum rightFinal.quorum with ⟨node, inLeft, inRight⟩
  exact discipline.compatible node left right
    (leftFinal.voted node inLeft) (rightFinal.voted node inRight)

/-- Prefix compatibility becomes exact transaction equality at an equal log
slot.  This is the central replicated safety result: no two finalized
certificates can assign different durable intents to one slot, even if they
were proposed in different epochs. -/
theorem finalized_transaction_unique_at_slot
    {quorums : QuorumSystem Node}
    {book : VoteBook (Node := Node) (TxId := TxId) (CellId := CellId)
      (Nullifier := Nullifier) (Event := Event)}
    (discipline : PrefixDiscipline book)
    {left right : Candidate TxId CellId Nullifier Event}
    (leftFinal : Finalized quorums book left)
    (rightFinal : Finalized quorums book right)
    (sameSlot : left.slot = right.slot) :
    left.intent = right.intent := by
  rcases finalized_logs_comparable discipline leftFinal rightFinal with ordering | ordering
  · have sameLength : left.log.length = right.log.length := by
      rw [left.log_length, right.log_length, sameSlot]
    have logsEqual := ordering.eq_of_length sameLength
    have lastEqual := congrArg List.getLast? logsEqual
    simpa using lastEqual
  · have sameLength : right.log.length = left.log.length := by
      rw [right.log_length, left.log_length, sameSlot]
    have logsEqual := ordering.eq_of_length sameLength
    have lastEqual := congrArg List.getLast? logsEqual
    simpa using lastEqual.symm

/-- The fork event excluded by quorum intersection plus prefix discipline. -/
def ConflictsAtSlot
    (left right : Candidate TxId CellId Nullifier Event) : Prop :=
  left.slot = right.slot ∧ left.intent ≠ right.intent

theorem no_conflicting_finalized_transactions
    {quorums : QuorumSystem Node}
    {book : VoteBook (Node := Node) (TxId := TxId) (CellId := CellId)
      (Nullifier := Nullifier) (Event := Event)}
    (discipline : PrefixDiscipline book)
    {left right : Candidate TxId CellId Nullifier Event}
    (leftFinal : Finalized quorums book left)
    (rightFinal : Finalized quorums book right) :
    ¬ ConflictsAtSlot left right := by
  rintro ⟨sameSlot, differs⟩
  exact differs (finalized_transaction_unique_at_slot discipline
    leftFinal rightFinal sameSlot)

/-- Explicit epoch handoff witness.  A higher epoch may be entered only by
extending the earlier finalized log.  The safety theorem above does not assume
that such handoffs eventually occur. -/
structure EpochAdvance
    (earlier later : Candidate TxId CellId Nullifier Event) : Prop where
  laterEpoch : earlier.epoch < later.epoch
  extendsPrior : earlier.log.IsPrefix later.priorLog

theorem epochAdvance_extends_log
    {earlier later : Candidate TxId CellId Nullifier Event}
    (advance : EpochAdvance earlier later) :
    earlier.log.IsPrefix later.log :=
  advance.extendsPrior.trans (by simp [Candidate.log])

/-! ## Durable replicas, failover, and replay -/

variable [DecidableEq TxId] [DecidableEq CellId] [DecidableEq Nullifier]
  [DecidableEq Event]

/-- A replica is failover-ready for a finalized candidate only when its framed
WAL decodes to that exact log under the same checkpoint.  A torn successor may
exist, since `FramedWalRefinement` proves it is outside recovered meaning. -/
structure DurableReplica
    (codec : FrameCodec (WalIntent (TxId := TxId) (CellId := CellId)
      (Nullifier := Nullifier) (Event := Event)))
    (checkpoint : Snapshot TxId CellId Nullifier Event)
    (candidate : Candidate TxId CellId Nullifier Event) : Type (max u v w x) where
  device : DeviceState TxId CellId Nullifier Event
  checkpoint_exact : device.checkpoint = checkpoint
  decoded_exact : DeviceState.decodeAll codec device.durableFrames =
    some candidate.log

namespace DurableReplica

variable {codec : FrameCodec (WalIntent (TxId := TxId) (CellId := CellId)
  (Nullifier := Nullifier) (Event := Event))}
  {checkpoint : Snapshot TxId CellId Nullifier Event}
  {candidate : Candidate TxId CellId Nullifier Event}

/-- Failover reconstruction is the exact fold of the finalized log. -/
theorem recovered_exact (replica : DurableReplica codec checkpoint candidate) :
    DeviceState.recovered codec replica.device =
      candidate.log.foldl Snapshot.install checkpoint := by
  simp only [DeviceState.recovered, replica.decoded_exact]
  rw [replica.checkpoint_exact]

/-- Any two failover-ready replicas for one certificate recover the identical
semantic snapshot, even when their caches or torn tails differ. -/
theorem failover_same_recovery
    (primary backup : DurableReplica codec checkpoint candidate) :
    DeviceState.recovered codec primary.device =
      DeviceState.recovered codec backup.device := by
  rw [primary.recovered_exact, backup.recovered_exact]

/-- The finalized transaction is already journaled after failover.  A client
retry is an idempotent replay, not a second root/nullifier/debit/history
installation. -/
theorem retry_after_failover_replays
    (replica : DurableReplica codec checkpoint candidate) :
    execute .complete (DeviceState.recovered codec replica.device)
      candidate.intent = .replayed candidate.intent := by
  rw [replica.recovered_exact]
  change execute .complete
      ((candidate.priorLog ++ [candidate.intent]).foldl Snapshot.install checkpoint)
      candidate.intent = .replayed candidate.intent
  rw [List.foldl_append]
  exact execute_retry_after_install .complete
    (candidate.priorLog.foldl Snapshot.install checkpoint) candidate.intent

end DurableReplica

/-! ## Liveness is conditional, not smuggled into safety -/

/-- An abstract network trace records delivery by a finite round and requires
delivery to remain true thereafter.  It says nothing about real transport. -/
structure NetworkSchedule
    (Node : Type n)
    (CandidateType : Type c) where
  deliveredBy : Nat -> Node -> CandidateType -> Prop
  monotone : forall {round later node candidate},
    round ≤ later -> deliveredBy round node candidate ->
      deliveredBy later node candidate

def EventuallyDelivered
    (schedule : NetworkSchedule Node
      (Candidate TxId CellId Nullifier Event))
    (node : Node) (candidate : Candidate TxId CellId Nullifier Event) : Prop :=
  exists round, schedule.deliveredBy round node candidate

/-- Availability is an explicit online quorum, not a theorem of quorum
intersection. -/
structure AvailableQuorum
    (quorums : QuorumSystem Node)
    (online : Node -> Prop) : Type n where
  voters : Finset Node
  quorum : quorums.isQuorum voters
  online_voters : forall node, node ∈ voters -> online node

/-- Fair delivery for one candidate and one chosen online quorum. -/
structure FairDelivery
    (schedule : NetworkSchedule Node
      (Candidate TxId CellId Nullifier Event))
    {quorums : QuorumSystem Node} {online : Node -> Prop}
    (available : AvailableQuorum quorums online)
    (candidate : Candidate TxId CellId Nullifier Event) : Prop where
  eventually : forall node, node ∈ available.voters ->
    EventuallyDelivered schedule node candidate

/-- Responsive replicas eventually record every delivered candidate while
online.  A real consensus implementation must prove this only for candidates
allowed by its lock, epoch, and validation rules. -/
def Responsive
    (schedule : NetworkSchedule Node
      (Candidate TxId CellId Nullifier Event))
    (online : Node -> Prop)
    (book : VoteBook (Node := Node) (TxId := TxId) (CellId := CellId)
      (Nullifier := Nullifier) (Event := Event)) : Prop :=
  forall node candidate,
    online node -> EventuallyDelivered schedule node candidate ->
      candidate ∈ book node

/-- Conditional progress theorem.  It constructs a finality certificate only
after availability, eventual delivery, and responsiveness are supplied. -/
def finalized_of_available_fair_responsive
    {quorums : QuorumSystem Node}
    {online : Node -> Prop}
    {book : VoteBook (Node := Node) (TxId := TxId) (CellId := CellId)
      (Nullifier := Nullifier) (Event := Event)}
    {schedule : NetworkSchedule Node
      (Candidate TxId CellId Nullifier Event)}
    (available : AvailableQuorum quorums online)
    (candidate : Candidate TxId CellId Nullifier Event)
    (fair : FairDelivery schedule available candidate)
    (responsive : Responsive schedule online book) :
    Finalized quorums book candidate where
  voters := available.voters
  quorum := available.quorum
  voted := fun node member => responsive node candidate
    (available.online_voters node member) (fair.eventually node member)

/-- If no quorum is available, no theorem in this layer manufactures a
certificate. -/
theorem no_finality_without_any_quorum
    (quorums : QuorumSystem Node)
    (book : VoteBook (Node := Node) (TxId := TxId) (CellId := CellId)
      (Nullifier := Nullifier) (Event := Event))
    (candidate : Candidate TxId CellId Nullifier Event)
    (none : forall voters, ¬ quorums.isQuorum voters) :
    ¬ Nonempty (Finalized quorums book candidate) := by
  rintro ⟨finalized⟩
  exact none finalized.voters finalized.quorum

/-! ## Closed non-vacuous witnesses -/

namespace ClosedInstance

open Minidregg.Kernel.DurableWalHandler.ClosedInstance

namespace FramedWitness

def codec := Minidregg.Kernel.FramedWalRefinement.ClosedInstance.codec
def afterSync := Minidregg.Kernel.FramedWalRefinement.ClosedInstance.afterSync
theorem intent_roundTrips : codec.RoundTrips intent :=
  Minidregg.Kernel.FramedWalRefinement.ClosedInstance.intent_roundTrips

end FramedWitness
abbrev ReplicaNode := Fin 3

/-- Two fixed voting nodes form the closed witness quorum.  The construction
is intentionally simple; generic safety above uses only intersection. -/
def core : Finset ReplicaNode := {0, 1}

def quorums : QuorumSystem ReplicaNode where
  isQuorum voters := core ⊆ voters
  intersects := by
    intro left right leftQuorum rightQuorum
    refine ⟨0, leftQuorum ?_, rightQuorum ?_⟩ <;> simp [core]

def candidate : Candidate Nat Nat Nat Nat where
  epoch := 4
  priorLog := []
  intent := intent

def book : VoteBook (Node := ReplicaNode) (TxId := Nat) (CellId := Nat)
    (Nullifier := Nat) (Event := Nat) :=
  fun _ => [candidate]

def discipline : PrefixDiscipline book where
  compatible := by
    intro node left right leftVote rightVote
    simp only [book, List.mem_singleton] at leftVote rightVote
    subst left
    subst right
    exact Or.inl List.prefix_rfl

def certificate : Finalized quorums book candidate where
  voters := core
  quorum := fun _ member => member
  voted := by simp [book]

/-- A second certificate at the same slot cannot carry another intent. -/
theorem closed_no_conflicting_finalization
    {other : Candidate Nat Nat Nat Nat}
    (otherFinal : Finalized quorums book other) :
    ¬ ConflictsAtSlot candidate other :=
  no_conflicting_finalized_transactions discipline certificate otherFinal

def primary : DurableReplica FramedWitness.codec device.checkpoint candidate where
  device := FramedWitness.afterSync
  checkpoint_exact := rfl
  decoded_exact := by
    change DeviceState.decodeAll FramedWitness.codec
      [FramedWitness.codec.encodeFrame intent] =
      some [intent]
    simp only [DeviceState.decodeAll]
    rw [FramedWitness.intent_roundTrips]
    rfl

/-- The backup has the same finalized frames and a torn successor.  Recovery
must ignore that tail rather than lose the finalized transaction. -/
def backupDevice : DeviceState Nat Nat Nat Nat where
  checkpoint := FramedWitness.afterSync.checkpoint
  durableFrames := FramedWitness.afterSync.durableFrames
  tornTail := some ((FramedWitness.codec.encodeFrame intent).take 2)
  cache := none

def backup : DurableReplica FramedWitness.codec device.checkpoint candidate where
  device := backupDevice
  checkpoint_exact := rfl
  decoded_exact := primary.decoded_exact

theorem failover_recovers_same_finalized_snapshot :
    DeviceState.recovered FramedWitness.codec primary.device =
      DeviceState.recovered FramedWitness.codec backup.device :=
  DurableReplica.failover_same_recovery primary backup

theorem retry_on_backup_is_idempotent :
    execute .complete
      (DeviceState.recovered FramedWitness.codec backup.device) intent =
      .replayed intent :=
  DurableReplica.retry_after_failover_replays backup

/-- The payload-bearing path really enters the same candidate carrier without
discarding its exact erased replay envelope. -/
def dataCandidate := Candidate.ofData 7 []
  Minidregg.Kernel.DurableDataIntent.Witness.intent

theorem dataCandidate_retains_exact_envelope :
    dataCandidate.intent =
      Minidregg.Kernel.DurableDataIntent.Witness.intent.erase := rfl

def online : ReplicaNode -> Prop := fun _ => True

def schedule : NetworkSchedule ReplicaNode (Candidate Nat Nat Nat Nat) where
  deliveredBy := fun _ _ proposed => proposed = candidate
  monotone := by
    intro round later node proposed le delivered
    exact delivered

def available : AvailableQuorum quorums online where
  voters := core
  quorum := fun _ member => member
  online_voters := by simp [online]

def fair : FairDelivery schedule available candidate where
  eventually := by
    intro node member
    exact ⟨0, rfl⟩

theorem responsive : Responsive schedule online book := by
  intro node proposed onlineNode delivered
  rcases delivered with ⟨round, delivered⟩
  simp only [schedule] at delivered
  subst proposed
  simp [book]

/-- Closed progress is inhabited only after all three liveness premises are
provided. -/
def conditionallyFinalized : Finalized quorums book candidate :=
  finalized_of_available_fair_responsive available candidate fair responsive

end ClosedInstance

/-! ## Pinned axiom audit -/

/-- info: 'Minidregg.Kernel.ReplicatedSettlementFinality.finalized_transaction_unique_at_slot' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms finalized_transaction_unique_at_slot
/-- info: 'Minidregg.Kernel.ReplicatedSettlementFinality.no_conflicting_finalized_transactions' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms no_conflicting_finalized_transactions
/-- info: 'Minidregg.Kernel.ReplicatedSettlementFinality.DurableReplica.failover_same_recovery' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms DurableReplica.failover_same_recovery
/-- info: 'Minidregg.Kernel.ReplicatedSettlementFinality.DurableReplica.retry_after_failover_replays' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DurableReplica.retry_after_failover_replays
/-- info: 'Minidregg.Kernel.ReplicatedSettlementFinality.finalized_of_available_fair_responsive' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms finalized_of_available_fair_responsive
/-- info: 'Minidregg.Kernel.ReplicatedSettlementFinality.ClosedInstance.closed_no_conflicting_finalization' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ClosedInstance.closed_no_conflicting_finalization
/-- info: 'Minidregg.Kernel.ReplicatedSettlementFinality.ClosedInstance.retry_on_backup_is_idempotent' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ClosedInstance.retry_on_backup_is_idempotent

end Minidregg.Kernel.ReplicatedSettlementFinality
