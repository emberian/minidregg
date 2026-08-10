/-
# Assurance.HyperdocumentDurableInstallation -- the durable half, no longer assumed

`HyperdocumentAgentOperation.DurablePlan` derives one costed handler `Intent`
from an already accepted joint publication, and then states its physical
atomicity as `physical_step_no_partial`, which takes an
`ImplementationRefinement` as a hypothesis.  Until something inhabited that
structure, the theorem said only "if a correct handler exists, it is atomic".

`Kernel.DurableWalHandler.walRefinement` inhabits it.  This module discharges
the hypothesis at the Hyperdocument slice, so the statements below have no
handler premise left:

* a device step on the operation's intent lands on the whole old snapshot or
  the whole installed one;
* the commit marker moves cold-start recovery by exactly that one install;
* a crash before the marker leaves recovery where it was, and the installation
  did not happen; and
* a lost response after the marker replays idempotently rather than charging
  the operation twice.

**Caveat added after `Theory.MaterializerCardinality` (same night).**  Every
theorem below is generic over the joint `Commit`, and that carrier IS inhabited
-- `Kernel.MultiCellHyperedgeWitness` exhibits one at finite witness schemas, so
none of these statements is vacuous.  But at the ACTUAL Hyperdocument
instantiation the commit is currently vacuous: `HyperdocumentPublication`'s cell
family demands a `Hyperdocument.Materializer Digest` and a
`CredentialAuthorityState.Cell`, and both materializers are proved EMPTY.  So
this module says "any joint commit installs durably like this", which is true
and useful, and it does NOT yet say anything about a Hyperdocument publication
in particular.  The file name promises more than the theorems deliver until
`LogicalState` becomes finitely supported.

The scope of "no longer assumed" is exact and narrow.  The handler is
`Kernel.DurableWalHandler`'s device MODEL -- a staged slot, an append-only
committed region, and a compacting checkpoint.  It has no `fsync`, no torn
record, no byte codec, no page cache, no replication, no clock, and no
liveness.  A real store must still exhibit its own state as a `WalState` and
its own transitions as `WalStep`s.  What changed is that the Hyperdocument
operation's durable statements are now about a constructed handler instead of
a quantified one.
-/
import Assurance.HyperdocumentAgentOperation
import Kernel.DurableWalHandler

namespace Minidregg.Assurance.HyperdocumentDurableInstallation

open Minidregg.Assurance.HyperdocumentAgentOperation
open Minidregg.Kernel.DurableCommitProtocol
open Minidregg.Kernel.DurableWalHandler
open Minidregg.Theory
open Minidregg.Theory.TypedAuthorization (Digest)

set_option autoImplicit false

noncomputable section

variable
    {Incidence : Type*} [Fintype Incidence] [DecidableEq Incidence]
    {cells : Minidregg.Kernel.MultiCellHyperedge.CellFamily Incidence}
    {declaration : Minidregg.Kernel.MultiCellHyperedge.Declaration cells}
    {Coordinate Balance : Type*} [AddCommMonoid Balance]
    {law : Minidregg.Kernel.MultiCellHyperedge.ResourceLaw declaration
      Coordinate Balance}
    {accepted : declaration.AcceptedLegs}
    {boundary : Minidregg.Kernel.MultiCellHyperedge.HandlerBoundary declaration}
    {commit : Minidregg.Kernel.MultiCellHyperedge.Commit law accepted boundary}
    [DecidableEq (Minidregg.Kernel.MultiCellHyperedge.JointNullifier accepted)]

/-- The model snapshot type this slice settles into. -/
abbrev OperationSnapshot (accepted : declaration.AcceptedLegs) :=
  Snapshot Digest Digest
    (Minidregg.Kernel.MultiCellHyperedge.JointNullifier accepted)
    Minidregg.Kernel.MultiCellHyperedge.JointCommitInput

/-- The constructed log device this slice installs on. -/
abbrev OperationDevice (accepted : declaration.AcceptedLegs) :=
  WalState Digest Digest
    (Minidregg.Kernel.MultiCellHyperedge.JointNullifier accepted)
    Minidregg.Kernel.MultiCellHyperedge.JointCommitInput

/-! ## Atomicity, with the handler premise discharged -/

/-- **No partial commit, unconditionally at this slice.**  The
`ImplementationRefinement` argument of `DurablePlan.physical_step_no_partial`
is supplied by `walRefinement`, so nothing about a hypothetical correct
handler is assumed. -/
theorem no_partial_commit_on_wal (plan : DurablePlan commit)
    {deviceBefore deviceAfter : OperationDevice accepted}
    {model : OperationSnapshot accepted}
    (represented : Represents deviceBefore model)
    (stepped : WalStep deviceBefore plan.intent deviceAfter) :
    ∃ modelAfter,
      Represents deviceAfter modelAfter ∧
        (modelAfter = model ∨
          modelAfter = Snapshot.install model plan.intent) :=
  DurablePlan.physical_step_no_partial plan walRefinement represented stepped

/-! ## The commit marker, and the two ways a response can be lost -/

/-- **Installation.**  When the marker reaches the device, cold-start recovery
moves by exactly the one atomic install of the operation's intent -- every
root write, nullifier, charge lane, history event, and journal record, or none
of them. -/
theorem marker_installs (plan : DurablePlan commit)
    (device : OperationDevice accepted) :
    WalState.recovered
        { checkpoint := device.checkpoint
          committed := device.committed ++ [plan.intent]
          staged := none } =
      Snapshot.install device.recovered plan.intent :=
  WalState.recovered_append device plan.intent none

/-- **Crash before the marker.**  Recovery is unchanged, and it is not the
installed snapshot: the operation genuinely did not happen, rather than
half-happening. -/
theorem crash_before_marker (plan : DurablePlan commit)
    (device : OperationDevice accepted) :
    WalState.recovered
        { device with
          staged := (none : Option (Intent Digest Digest
            (Minidregg.Kernel.MultiCellHyperedge.JointNullifier accepted)
            Minidregg.Kernel.MultiCellHyperedge.JointCommitInput)) } =
        device.recovered ∧
      WalState.recovered
        { device with
          staged := (none : Option (Intent Digest Digest
            (Minidregg.Kernel.MultiCellHyperedge.JointNullifier accepted)
            Minidregg.Kernel.MultiCellHyperedge.JointCommitInput)) } ≠
        Snapshot.install device.recovered plan.intent :=
  crash_before_marker_loses_record device plan.intent

/-- **Lost response after the marker.**  Re-submitting the same operation
against the recovered snapshot replays rather than installing again, under
every schedule -- the agent may retry a request whose reply it never saw
without charging the document twice. -/
theorem retry_after_marker (plan : DurablePlan commit)
    (device : OperationDevice accepted) (schedule : Schedule) :
    execute schedule
        (WalState.recovered
          { checkpoint := device.checkpoint
            committed := device.committed ++ [plan.intent]
            staged := none })
        plan.intent =
      .replayed plan.intent := by
  rw [marker_installs]
  exact plan.retry_after_install schedule device.recovered

/-! ## The two-step installation exists

Atomicity theorems are cheap for a handler that never installs anything.  This
is the positive direction: whenever the model would accept the operation's
intent, the stage-then-commit sequence is a constructed `WalStep`, and its
effect is the exact install. -/

/-- The constructed commit step for one accepted Hyperdocument operation. -/
def install (plan : DurablePlan commit) (device : OperationDevice accepted)
    (unrecorded : Snapshot.lookupRecorded plan.intent.transactionId
      device.recovered.journal = none)
    (preflighted : plan.intent.preflight device.recovered = .ok ()) :
    WalStep { device with staged := some plan.intent } plan.intent
      { checkpoint := device.checkpoint
        committed := device.committed ++ [plan.intent]
        staged := none } :=
  stageThenCommit device plan.intent unrecorded preflighted

/-- Its cell coverage is the operation's own: one root write per incidence of
the joint publication, so the durable record installs the whole hyperedge and
not a subset of it. -/
theorem install_covers_every_incidence (plan : DurablePlan commit) :
    plan.intent.rootWrites.length = Fintype.card Incidence :=
  plan.intent_root_count

/-- info: 'Minidregg.Assurance.HyperdocumentDurableInstallation.no_partial_commit_on_wal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms no_partial_commit_on_wal
/-- info: 'Minidregg.Assurance.HyperdocumentDurableInstallation.marker_installs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms marker_installs
/-- info: 'Minidregg.Assurance.HyperdocumentDurableInstallation.crash_before_marker' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms crash_before_marker
/-- info: 'Minidregg.Assurance.HyperdocumentDurableInstallation.retry_after_marker' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms retry_after_marker
/-- info: 'Minidregg.Assurance.HyperdocumentDurableInstallation.install_covers_every_incidence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms install_covers_every_incidence

end

end Minidregg.Assurance.HyperdocumentDurableInstallation
