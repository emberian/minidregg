/-
# Kernel.FinalityLiveness -- liveness as ONE named carrier (`PostGSTProgress`)

The constitution's sentence (breadstuffs paper2 §5 floor 8, §8): *liveness is
exactly as strong as its carrier -- `PostGSTProgress`; a partitioned network
stalls finality; it cannot forge it.*  `ReplicatedSettlementFinality` carries
the safety of quorum finality and proves progress only from three separate
premises (`AvailableQuorum`, `FairDelivery`, `Responsive`); `FinalityGate` is
the decider.  This module makes the three premises ONE typed obligation with a
realizer slot (ATLAS §6 law 1) and turns the sentence into two theorems.
`docs/DISTRIBUTED-DESIGN.md` §3.2.

* **`PostGSTProgress quorums book candidate`** is the liveness floor: a
  `Type`-valued structure bundling a network schedule, an online predicate, an
  available quorum on it, fair delivery of this candidate to that quorum, and
  replica responsiveness -- exactly the replicated layer's premises, no more.
  It is a realizer slot: inhabiting it is the deployment's work (a GST/round
  model, a transport), never an axiom.
* **`progress`** is the replicated layer's `finalized_of_available_fair_responsive`
  applied to the carrier (reused, not re-proved); **`checked_of_progress`**:
  under the carrier the DECIDER accepts (`FinalityGate.check_complete`).
* **The two poles, kept separate.**  `cannot_forge`: with no quorum anywhere,
  every presented certificate is refused -- NO liveness premise appears
  (`check_false_of_no_quorum`; safety needs none).  `no_progress_without_quorum`:
  with no quorum anywhere, the carrier has NO realizer (`IsEmpty`) -- the
  network stalls.
* **Closed instance, computed.**  `realizer` inhabits the carrier on
  `ReplicatedSettlementFinality.ClosedInstance` (its schedule / online /
  available / fair / responsive, reused); `progress realizer` is the honest
  certificate and its voters check `true` by `decide`.  Three broken siblings:
  `deadQuorums` (no set is a quorum) -- the carrier is empty AND every cert is
  refused, both instantiated; `partitioned` (only node 2 online, the core on the
  far side) -- no `AvailableQuorum`, so no realizer with that online predicate;
  `neverSchedule` (nothing is ever delivered) -- `FairDelivery` fails for the
  honest quorum while `Responsive` still holds, so the refusal is the fair
  leg's alone, and no realizer uses that schedule.

**Residuals.**
`[LIVENESS-gst]` no GST/round model and no `World.rand` measure bridge -- the
carrier is realized by a schedule, not derived from partial synchrony
(breadstuffs' irreducible residual, `Distributed/Consensus.lean:636-645`).
`[LIVENESS-authenticated]` the authenticated layer's `OnlineQuorumExists` /
`EventualNetworkDelivery` / `ResponsiveReplicas` `Prop` fields
(`Kernel/AuthenticatedSettlementFinality.lean` ~595-600) are the shape law 1
forbids and should be REPLACED by this carrier; not done here.
`dead_undecidable` and `revocation_needs_consensus` are ported in
`Theory/RevocationConsensus.lean`.
-/
import Kernel.ReplicatedSettlementFinality
import Kernel.FinalityGate

namespace Minidregg.Kernel.FinalityLiveness

open Minidregg.Kernel.DurableCommitProtocol
open Minidregg.Kernel.ReplicatedSettlementFinality
open Minidregg.Kernel.FinalityGate

set_option autoImplicit false

universe u v w x n

variable {TxId : Type u} {CellId : Type v} {Nullifier : Type w} {Event : Type x}
variable {Node : Type n} [DecidableEq Node]

/-! ## §1. The carrier. -/

/-- The liveness floor, as one typed obligation.  A realizer supplies a network
schedule, the online predicate, an available quorum on it, fair delivery of
this candidate to that quorum, and replica responsiveness.  Nothing here is
derived from safety; nothing here is assumed -- it is the slot a deployment
fills. -/
structure PostGSTProgress
    (quorums : QuorumSystem Node)
    (book : VoteBook (Node := Node) (TxId := TxId) (CellId := CellId)
      (Nullifier := Nullifier) (Event := Event))
    (candidate : Candidate TxId CellId Nullifier Event) where
  schedule : NetworkSchedule Node (Candidate TxId CellId Nullifier Event)
  online : Node -> Prop
  available : AvailableQuorum quorums online
  fair : FairDelivery schedule available candidate
  responsive : Responsive schedule online book

section Generic

variable (quorums : QuorumSystem Node)
  (book : VoteBook (Node := Node) (TxId := TxId) (CellId := CellId)
    (Nullifier := Nullifier) (Event := Event))
  (candidate : Candidate TxId CellId Nullifier Event)

/-! ## §2. Progress under the carrier -- the existing construction, reused. -/

/-- The replicated layer's conditional progress, fed by the carrier. -/
def progress (p : PostGSTProgress quorums book candidate) :
    Finalized quorums book candidate :=
  finalized_of_available_fair_responsive p.available candidate p.fair p.responsive

theorem progress_voters (p : PostGSTProgress quorums book candidate) :
    (progress quorums book candidate p).voters = p.available.voters := rfl

/-- Under the carrier, the DECIDER accepts the constructed certificate. -/
theorem checked_of_progress [DecidablePred quorums.isQuorum]
    [DecidableEq (Candidate TxId CellId Nullifier Event)]
    (p : PostGSTProgress quorums book candidate) :
    check quorums book candidate ⟨(progress quorums book candidate p).voters⟩ = true :=
  check_complete quorums book (progress quorums book candidate p)

/-! ## §3. The constitution's sentence as two theorems, kept apart. -/

/-- *It cannot forge it.*  With no quorum anywhere, every presented certificate
is refused.  No liveness premise appears: safety needs none. -/
theorem cannot_forge [DecidablePred quorums.isQuorum]
    [DecidableEq (Candidate TxId CellId Nullifier Event)]
    (none : ∀ voters, ¬ quorums.isQuorum voters) :
    ∀ cert : Cert Node, check quorums book candidate cert = false :=
  fun cert => check_false_of_no_quorum quorums book cert none

/-- *It stalls.*  With no quorum anywhere, the carrier has no realizer: no
schedule, online set, or responsiveness manufactures an available quorum. -/
theorem no_progress_without_quorum (none : ∀ voters, ¬ quorums.isQuorum voters) :
    IsEmpty (PostGSTProgress quorums book candidate) :=
  ⟨fun p => none p.available.voters p.available.quorum⟩

end Generic

/-! ## §4. The closed instance: the carrier inhabited, and refuted at three
broken siblings. -/

namespace ClosedInstance

open Minidregg.Kernel.ReplicatedSettlementFinality.ClosedInstance
open Minidregg.Kernel.FinalityGate.ClosedInstance

/-- *Premise-inhabitation*: the replicated layer's closed schedule, online
predicate, available quorum, fair delivery, and responsiveness, as ONE
realizer. -/
def realizer : PostGSTProgress quorums book candidate where
  schedule := schedule
  online := online
  available := available
  fair := fair
  responsive := responsive

theorem realizer_voters : (progress quorums book candidate realizer).voters = core := rfl

/-- The certificate progress constructs is accepted by the decider -- derived
through `check_complete`, and COMPUTED. -/
theorem realizer_checked :
    check quorums book candidate ⟨(progress quorums book candidate realizer).voters⟩ = true :=
  checked_of_progress quorums book candidate realizer

example : check quorums book candidate ⟨(progress quorums book candidate realizer).voters⟩ = true := by
  decide

/-! ### Broken sibling 1: no set is a quorum.  Both poles instantiate. -/

/-- The quorum system in which nothing is a quorum; intersection is vacuous. -/
def deadQuorums : QuorumSystem ReplicaNode where
  isQuorum := fun _ => False
  intersects := fun _ _ absurd _ => absurd.elim

instance deadQuorumsDecidable : DecidablePred deadQuorums.isQuorum :=
  fun _ => isFalse id

theorem deadQuorums_none : ∀ voters, ¬ deadQuorums.isQuorum voters := fun _ absurd => absurd

/-- The carrier over `deadQuorums` has no realizer: finality stalls. -/
theorem dead_stalls : IsEmpty (PostGSTProgress deadQuorums book candidate) :=
  no_progress_without_quorum deadQuorums book candidate deadQuorums_none

/-- Every presented certificate over `deadQuorums` is refused: finality is not
forged.  The honest wire included -- decided. -/
theorem dead_cannot_forge : ∀ cert : Cert ReplicaNode, check deadQuorums book candidate cert = false :=
  cannot_forge deadQuorums book candidate deadQuorums_none

example : check deadQuorums book candidate honest = false := by decide
example : check deadQuorums book candidate full = false := by decide

/-! ### Broken sibling 2: a partition.  The quorum system is intact; only node
`2` is online and the core `{0, 1}` is on the far side. -/

def partitioned : ReplicaNode -> Prop := fun node => node = 2

/-- No available quorum exists on the partitioned side. -/
theorem partition_no_available : IsEmpty (AvailableQuorum quorums partitioned) :=
  ⟨fun a =>
    have inCore : (0 : ReplicaNode) ∈ core := by decide
    have zeroOnline : (0 : ReplicaNode) = 2 := a.online_voters 0 (a.quorum inCore)
    absurd zeroOnline (by decide)⟩

/-- Hence no realizer of the carrier has the partitioned online predicate. -/
theorem partition_stalls :
    ¬ ∃ p : PostGSTProgress quorums book candidate, p.online = partitioned := by
  rintro ⟨p, same⟩
  exact partition_no_available.false (same ▸ p.available)

/-! ### Broken sibling 3: a schedule that never delivers.  Availability and
responsiveness still hold; fair delivery is the leg that fails. -/

def neverSchedule : NetworkSchedule ReplicaNode (Candidate Nat Nat Nat Nat) where
  deliveredBy := fun _ _ _ => False
  monotone := fun _ absurd => absurd

theorem never_responsive : Responsive neverSchedule online book :=
  fun _ _ _ delivered => delivered.elim (fun _ absurd => absurd.elim)

theorem never_not_fair : ¬ FairDelivery neverSchedule available candidate := by
  intro fair
  rcases fair.eventually 0 (by decide) with ⟨_, delivered⟩
  exact delivered

/-- No realizer of the carrier uses the never-delivering schedule. -/
theorem never_stalls :
    ¬ ∃ p : PostGSTProgress quorums book candidate, p.schedule = neverSchedule := by
  rintro ⟨p, same⟩
  have inCore : (0 : ReplicaNode) ∈ core := by decide
  rcases p.fair.eventually 0 (p.available.quorum inCore) with ⟨round, delivered⟩
  rw [same] at delivered
  exact delivered

end ClosedInstance

/-! ## §5. Axiom pins. -/

/-- info: 'Minidregg.Kernel.FinalityLiveness.checked_of_progress' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms checked_of_progress

/-- info: 'Minidregg.Kernel.FinalityLiveness.cannot_forge' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms cannot_forge

/-- info: 'Minidregg.Kernel.FinalityLiveness.no_progress_without_quorum' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms no_progress_without_quorum

/--
info: 'Minidregg.Kernel.FinalityLiveness.ClosedInstance.realizer_checked' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms ClosedInstance.realizer_checked

/-- info: 'Minidregg.Kernel.FinalityLiveness.ClosedInstance.dead_stalls' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms ClosedInstance.dead_stalls

/--
info: 'Minidregg.Kernel.FinalityLiveness.ClosedInstance.dead_cannot_forge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms ClosedInstance.dead_cannot_forge

/-- info: 'Minidregg.Kernel.FinalityLiveness.ClosedInstance.partition_stalls' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms ClosedInstance.partition_stalls

/-- info: 'Minidregg.Kernel.FinalityLiveness.ClosedInstance.never_not_fair' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms ClosedInstance.never_not_fair

/-- info: 'Minidregg.Kernel.FinalityLiveness.ClosedInstance.never_stalls' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms ClosedInstance.never_stalls

end Minidregg.Kernel.FinalityLiveness
