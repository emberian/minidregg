/- The deployed World view of objective and seat receiver execution.

The structural simulation applies to arbitrary derivable intents. The receiver
bridge below is stronger: its privately admitted objects supply the activity
turn/finalization or checked seat inertness used by the OB invariant proofs.
-/
import Kernel.HostRefinesWorld
import Kernel.DeployedHistory
import Kernel.ObjectiveDomainInvariant
import Kernel.ObjectiveAdmissible

namespace Minidregg.Kernel.ObjectiveRefinesWorld

open Minidregg.Theory Minidregg.Compiler
open Minidregg.Theory.TypedAuthorization (Digest)
open Minidregg.Kernel.World
open Minidregg.Kernel.TurnOfIntent
open Minidregg.Kernel.DeployedBridge
open Minidregg.Kernel.HostRefinesWorld
open Minidregg.Kernel.DurableDataIntent
open Minidregg.Kernel.DurableCommitProtocol (Schedule)
open Minidregg.Kernel.ObjectiveUpgradeInvariant (payloads Payloads)

set_option autoImplicit false

/-- The activity payload view of the World's logical cells. -/
def payloadsOf (w : World deployedR TransactionId Digest) : Payloads :=
  fun c => (w.cells c.value).bind fun cell =>
    (cell.storeAt .objectiveActivity).bind ObjectiveActivityCell.payloadAt

/-- Exact representation transports every activity payload, including absence. -/
theorem payloads_of_represents {snap : DataSnapshot ResourceBirthCodec.rootBytes} {h : Nat}
    {w : World deployedR TransactionId Digest} (rep : SnapRepresents bridge snap h w) :
    payloads snap.canonicalBytes = payloadsOf w := by
  funext c
  exact decodeCell_payload (rep.cells c.value)

/-- Structural simulation, honestly generic in the intent and history. -/
theorem intent_refines_step (H : History deployedR TransactionId StableEvent Digest)
    {p : DurableReceiverIO.Loaded ResourceBirthCodec.rootBytes}
    {w : World deployedR TransactionId Digest} (rep : DeployedRepresents p w)
    (intent : DataIntent ResourceBirthCodec.rootBytes) {t : DTurn deployedR Digest}
    (derived : Turn.ofLoaded bridge H p intent = .ok t) (schedule : Schedule) :
    let o := execute schedule p.snapshot intent
    (Installs o = true → ∃ w', World.step H w t = some w' ∧
      SnapRepresents bridge (o.storeAfter p.snapshot) (p.height + 1) w' ∧
      payloads (o.storeAfter p.snapshot).canonicalBytes = payloadsOf w') ∧
    (Installs o = false → SnapRepresents bridge (o.storeAfter p.snapshot) p.height w) := by
  dsimp only
  rcases execute_cases schedule p.snapshot intent with ⟨hi, fresh, ready, after⟩ | ⟨hi, after⟩
  · obtain ⟨w', step, post⟩ := ofIntent_run bridge H rep
      ((ofLoaded_eq bridge H rep intent).symm.trans derived) fresh ready
    rw [after]
    exact ⟨fun _ => ⟨w', step, post, payloads_of_represents post⟩, by simp [hi]⟩
  · rw [after]
    exact ⟨by simp [hi], fun _ => rep⟩

/-- The structural simulation instantiated at the deployed history and the
activity receiver's exact intent, for every crash schedule. -/
theorem objective_refines_step {config : NativeHost.Config} {opened : NativeHost.Opened config}
    {w : World deployedR TransactionId Digest} (rep : DeployedRepresents opened.durable w)
    {ingress : ObjectiveActivityReceiver.DecodedIngress}
    (verdict : ObjectiveActivityReceiver.Verdict config.deployment config.profile
      ⟨config.federation, NativeHost.logicalHeight config opened.durable,
        config.tariff.asset, config.tariff.collector⟩ opened.durable ingress)
    {t : DTurn deployedR Digest}
    (derived : Turn.ofLoaded bridge DeployedHistory.history opened.durable verdict.intent = .ok t)
    (schedule : Schedule) :
    let o := execute schedule opened.durable.snapshot verdict.intent
    (Installs o = true → ∃ w', World.step DeployedHistory.history w t = some w' ∧
      SnapRepresents bridge (o.storeAfter opened.durable.snapshot) (opened.durable.height + 1) w' ∧
      payloads (o.storeAfter opened.durable.snapshot).canonicalBytes = payloadsOf w') ∧
    (Installs o = false → SnapRepresents bridge (o.storeAfter opened.durable.snapshot)
      opened.durable.height w) :=
  intent_refines_step DeployedHistory.history rep verdict.intent derived schedule

/-- The same exact-intent simulation for the seat receiver's admitted object. -/
theorem seat_refines_step {config : NativeHost.Config} {opened : NativeHost.Opened config}
    {w : World deployedR TransactionId Digest} (rep : DeployedRepresents opened.durable w)
    {ingress : SeatReceiver.DecodedIngress}
    (verdict : SeatReceiver.Accepted config.deployment config.profile
      ⟨config.federation, NativeHost.logicalHeight config opened.durable,
        config.tariff.asset, config.tariff.collector⟩ opened.durable ingress)
    {t : DTurn deployedR Digest}
    (derived : Turn.ofLoaded bridge DeployedHistory.history opened.durable (SeatReceiver.intent verdict) = .ok t)
    (schedule : Schedule) :
    let o := execute schedule opened.durable.snapshot (SeatReceiver.intent verdict)
    (Installs o = true → ∃ w', World.step DeployedHistory.history w t = some w' ∧
      SnapRepresents bridge (o.storeAfter opened.durable.snapshot) (opened.durable.height + 1) w' ∧
      payloads (o.storeAfter opened.durable.snapshot).canonicalBytes = payloadsOf w') ∧
    (Installs o = false → SnapRepresents bridge (o.storeAfter opened.durable.snapshot)
      opened.durable.height w) :=
  intent_refines_step DeployedHistory.history rep (SeatReceiver.intent verdict) derived schedule

#assert_axioms payloads_of_represents intent_refines_step objective_refines_step seat_refines_step

/-- The actual activity receiving object at this native opening. -/
abbrev ActivityVerdict (config : NativeHost.Config) (opened : NativeHost.Opened config)
    (ingress : ObjectiveActivityReceiver.DecodedIngress) :=
  ObjectiveActivityReceiver.Verdict config.deployment config.profile
    ⟨config.federation, NativeHost.logicalHeight config opened.durable,
      config.tariff.asset, config.tariff.collector⟩ opened.durable ingress

/-- The OB configuration the receiver actually used. -/
def activityConfig {config : NativeHost.Config} {opened : NativeHost.Opened config}
    {ingress : ObjectiveActivityReceiver.DecodedIngress} :
    ActivityVerdict config opened ingress → ObjectiveActivity.Config
  | .accepted accepted => accepted.prepared.config
  | .failed failed => failed.gated.config

/-- An admitted activity verdict supplies the checked finalization required by
OB induction, including the charged-failure arm. -/
theorem objective_receiver_step {config : NativeHost.Config} {opened : NativeHost.Opened config}
    {ingress : ObjectiveActivityReceiver.DecodedIngress}
    (verdict : ActivityVerdict config opened ingress) (schedule : Schedule) :
    ObjectiveCheckpointInvariant.Step (activityConfig verdict) opened.durable.snapshot
      ((execute schedule opened.durable.snapshot verdict.intent).storeAfter opened.durable.snapshot) := by
  cases verdict with
  | accepted accepted =>
    exact .turn accepted.prepared.decided
      (ObjectiveActivityReceiver.admissionSeal accepted.prepared ingress)
      accepted.prepared.final.1 accepted.prepared.final.2 accepted.prepared.finalExact schedule
  | failed failed =>
    exact .turn (.failed failed.request failed.failure)
      { ObjectiveActivityReceiver.sealAt (profile := config.profile) failed.gated.authority
          ingress.command ingress with
        event := ObjectiveActivityReceiver.failedEvent
          (ObjectiveActivityReceiver.event config.deployment.domain config.profile.semantics ingress) failed.cause }
      failed.final.1 failed.final.2 failed.finalExact schedule

/-- Seat admission supplies checked inertness, so it preserves any OB configuration. -/
theorem seat_receiver_step {config : NativeHost.Config} {opened : NativeHost.Opened config}
    {ingress : SeatReceiver.DecodedIngress}
    (verdict : SeatReceiver.Accepted config.deployment config.profile
      ⟨config.federation, NativeHost.logicalHeight config opened.durable,
        config.tariff.asset, config.tariff.collector⟩ opened.durable ingress)
    (ob : ObjectiveActivity.Config) (schedule : Schedule) :
    ObjectiveCheckpointInvariant.Step ob opened.durable.snapshot
      ((execute schedule opened.durable.snapshot (SeatReceiver.intent verdict)).storeAfter
        opened.durable.snapshot) :=
  .inert (SeatReceiver.intent verdict) verdict.prepared.decided.posts rfl
    verdict.prepared.decided.inert schedule

/-- Exactly the two native receivers whose OB invariants are transported below.
Activity admission fixes the configuration; seat admission is inert for every
OB configuration. Neither constructor accepts an arbitrary intent. -/
inductive ReceiverIntent (config : NativeHost.Config) (opened : NativeHost.Opened config) :
    ObjectiveActivity.Config → DataIntent ResourceBirthCodec.rootBytes → Prop
  | activity {ingress : ObjectiveActivityReceiver.DecodedIngress}
      (verdict : ActivityVerdict config opened ingress) :
      ReceiverIntent config opened (activityConfig verdict) verdict.intent
  | seat {ingress : SeatReceiver.DecodedIngress}
      (verdict : SeatReceiver.Accepted config.deployment config.profile
        ⟨config.federation, NativeHost.logicalHeight config opened.durable,
          config.tariff.asset, config.tariff.collector⟩ opened.durable ingress)
      (ob : ObjectiveActivity.Config) :
      ReceiverIntent config opened ob (SeatReceiver.intent verdict)

theorem ReceiverIntent.step {config : NativeHost.Config} {opened : NativeHost.Opened config}
    {ob : ObjectiveActivity.Config} {intent : DataIntent ResourceBirthCodec.rootBytes}
    (receiver : ReceiverIntent config opened ob intent) (schedule : Schedule) :
    ObjectiveCheckpointInvariant.Step ob opened.durable.snapshot
      ((execute schedule opened.durable.snapshot intent).storeAfter opened.durable.snapshot) := by
  cases receiver with
  | activity verdict => exact objective_receiver_step verdict schedule
  | seat verdict ob => exact seat_receiver_step verdict ob schedule

/-- Checkpoint typing expressed entirely through activity payloads. -/
def CheckpointsTyped (ob : ObjectiveActivity.Config) (P : Payloads) : Prop :=
  ∀ cell record, ObjectiveUpgradeInvariant.recordView (P cell) = some record →
    cell = ObjectiveActivity.recordCell ob.domain record.object record.activity →
    ObjectiveCheckpointInvariant.CheckpointTyped ob
      ((P (ObjectiveActivity.packageCell ob.domain record.pin)).bind fun p =>
        if p.role = .package then some p.body else none) record

theorem checkpointsTyped_payloads {ob : ObjectiveActivity.Config}
    {snap : DataSnapshot ResourceBirthCodec.rootBytes} :
    CheckpointsTyped ob (payloads snap.canonicalBytes) ↔
      ObjectiveCheckpointInvariant.RecordCellsTyped ob snap := by
  have read (cell : DurableDataIntent.CellId) :
      ObjectiveUpgradeInvariant.recordView (payloads snap.canonicalBytes cell) =
        ObjectiveActivity.readRecord snap cell := by
    unfold ObjectiveUpgradeInvariant.recordView payloads ObjectiveActivity.readRecord ObjectiveActivity.bodyOf
    cases ObjectiveActivity.payloadOf (snap.canonicalBytes cell) with
    | none => rfl
    | some p => by_cases h : p.role = .record <;> simp [h]
  unfold CheckpointsTyped ObjectiveCheckpointInvariant.RecordCellsTyped
  simp only [read]
  rfl

/-- The reached World and the receiver's next snapshot have the same OB view;
the receiver also extends the original OB reachability proof by one real step. -/
theorem receiver_reached_view {config : NativeHost.Config} {opened : NativeHost.Opened config}
    {ob : ObjectiveActivity.Config} {intent : DataIntent ResourceBirthCodec.rootBytes}
    (receiver : ReceiverIntent config opened ob intent)
    {w w' : World deployedR TransactionId Digest} (rep : DeployedRepresents opened.durable w)
    {t : DTurn deployedR Digest}
    (derived : Turn.ofLoaded bridge DeployedHistory.history opened.durable intent = .ok t)
    (schedule : Schedule)
    (installs : Installs (execute schedule opened.durable.snapshot intent) = true)
    (stepped : World.step DeployedHistory.history w t = some w')
    {genesis : DataSnapshot ResourceBirthCodec.rootBytes}
    (reachable : ObjectiveCheckpointInvariant.Reachable ob genesis opened.durable.snapshot) :
    let after := (execute schedule opened.durable.snapshot intent).storeAfter opened.durable.snapshot
    ObjectiveCheckpointInvariant.Reachable ob genesis after ∧
      payloads after.canonicalBytes = payloadsOf w' := by
  obtain ⟨next, step, _, view⟩ := (intent_refines_step DeployedHistory.history rep intent derived schedule).1 installs
  have same : next = w' := Option.some.inj (step.symm.trans stepped)
  subst next
  exact ⟨.step reachable (receiver.step schedule), view⟩

#assert_axioms objective_receiver_step seat_receiver_step ReceiverIntent.step
#assert_axioms checkpointsTyped_payloads receiver_reached_view

/-- Every checkpoint in a World reached by an admitted activity or seat turn
is typed. The receiving object supplies the new OB step in the induction. -/
theorem stored_checkpoints_typed {config : NativeHost.Config} {opened : NativeHost.Opened config}
    {ob : ObjectiveActivity.Config} {intent : DataIntent ResourceBirthCodec.rootBytes}
    (receiver : ReceiverIntent config opened ob intent)
    {w w' : World deployedR TransactionId Digest} (rep : DeployedRepresents opened.durable w)
    {t : DTurn deployedR Digest}
    (derived : Turn.ofLoaded bridge DeployedHistory.history opened.durable intent = .ok t)
    (schedule : Schedule)
    (installs : Installs (execute schedule opened.durable.snapshot intent) = true)
    (stepped : World.step DeployedHistory.history w t = some w')
    {genesis : DataSnapshot ResourceBirthCodec.rootBytes}
    (reachable : ObjectiveCheckpointInvariant.Reachable ob genesis opened.durable.snapshot)
    (genesisTyped : ObjectiveCheckpointInvariant.RecordCellsTyped ob genesis) :
    CheckpointsTyped ob (payloadsOf w') := by
  obtain ⟨reached, view⟩ := receiver_reached_view receiver rep derived schedule installs stepped reachable
  rw [← view]
  exact checkpointsTyped_payloads.mpr
    (ObjectiveCheckpointInvariant.stored_checkpoints_typed genesisTyped reached)

/-- Registered domain laws hold on the reached World's payloads, after the
receiver's actual finalization or checked inert seat step. -/
theorem domain_holds_forever {config : NativeHost.Config} {opened : NativeHost.Opened config}
    {ob : ObjectiveActivity.Config} {intent : DataIntent ResourceBirthCodec.rootBytes}
    (receiver : ReceiverIntent config opened ob intent)
    {w w' : World deployedR TransactionId Digest} (rep : DeployedRepresents opened.durable w)
    {t : DTurn deployedR Digest}
    (derived : Turn.ofLoaded bridge DeployedHistory.history opened.durable intent = .ok t)
    (schedule : Schedule)
    (installs : Installs (execute schedule opened.durable.snapshot intent) = true)
    (stepped : World.step DeployedHistory.history w t = some w')
    {genesis : DataSnapshot ResourceBirthCodec.rootBytes}
    (reachable : ObjectiveCheckpointInvariant.Reachable ob genesis opened.durable.snapshot)
    (start : ObjectiveDomainInvariant.DomainsHold ob (payloads genesis.canonicalBytes)) :
    ObjectiveDomainInvariant.DomainsHold ob (payloadsOf w') := by
  obtain ⟨reached, view⟩ := receiver_reached_view receiver rep derived schedule installs stepped reachable
  rw [← view]
  exact ObjectiveDomainInvariant.reachable_domainsHold start reached

/-- The reached World's live, rebirth and pending counters have an exact
census over its own activity payloads. -/
theorem live_counts {config : NativeHost.Config} {opened : NativeHost.Opened config}
    {ob : ObjectiveActivity.Config} {intent : DataIntent ResourceBirthCodec.rootBytes}
    (receiver : ReceiverIntent config opened ob intent)
    {w w' : World deployedR TransactionId Digest} (rep : DeployedRepresents opened.durable w)
    {t : DTurn deployedR Digest}
    (derived : Turn.ofLoaded bridge DeployedHistory.history opened.durable intent = .ok t)
    (schedule : Schedule)
    (installs : Installs (execute schedule opened.durable.snapshot intent) = true)
    (stepped : World.step DeployedHistory.history w t = some w')
    {genesis : DataSnapshot ResourceBirthCodec.rootBytes}
    (reachable : ObjectiveCheckpointInvariant.Reachable ob genesis opened.durable.snapshot)
    (book : ObjectiveUpgradeInvariant.BookUnprotected ob)
    (clean : ObjectiveUpgradeInvariant.GenesisClean ob genesis) :
    ObjectiveUpgradeInvariant.LiveCounts ob (payloadsOf w') := by
  obtain ⟨reached, view⟩ := receiver_reached_view receiver rep derived schedule installs stepped reachable
  rw [← view]
  exact (ObjectiveUpgradeInvariant.reachable_upgradable book clean reached).1

/-- Migration of the reached World's state cannot fail its migration or next
record's write judgment. This is the payload-only obligation used by
`migrate_cannot_fail`; admission's fee/Book check is a separate premise there. -/
theorem migrate_cannot_fail {config : NativeHost.Config} {opened : NativeHost.Opened config}
    {ob : ObjectiveActivity.Config} {intent : DataIntent ResourceBirthCodec.rootBytes}
    (receiver : ReceiverIntent config opened ob intent)
    {w w' : World deployedR TransactionId Digest} (rep : DeployedRepresents opened.durable w)
    {t : DTurn deployedR Digest}
    (derived : Turn.ofLoaded bridge DeployedHistory.history opened.durable intent = .ok t)
    (schedule : Schedule)
    (installs : Installs (execute schedule opened.durable.snapshot intent) = true)
    (stepped : World.step DeployedHistory.history w t = some w')
    {genesis : DataSnapshot ResourceBirthCodec.rootBytes}
    (reachable : ObjectiveCheckpointInvariant.Reachable ob genesis opened.durable.snapshot)
    (book : ObjectiveUpgradeInvariant.BookUnprotected ob)
    (clean : ObjectiveUpgradeInvariant.GenesisClean ob genesis) :
    ObjectiveUpgradeInvariant.MigratableStates ob (payloadsOf w') := by
  obtain ⟨reached, view⟩ := receiver_reached_view receiver rep derived schedule installs stepped reachable
  rw [← view]
  exact (ObjectiveUpgradeInvariant.reachable_upgradable book clean reached).2

#assert_axioms stored_checkpoints_typed domain_holds_forever live_counts migrate_cannot_fail

/-- Replace just the final post's bytes and bound post-root. Its cell id and
expected pre-root are preserved, as are every earlier post and all other
intent fields. The explicit decomposition makes the affected post reviewable. -/
def tamperLast (intent : DataIntent ResourceBirthCodec.rootBytes)
    (earlier : List DataWrite) (last : DataWrite) (shape : intent.writes = earlier ++ [last])
    (bytes : List UInt8) : DataIntent ResourceBirthCodec.rootBytes where
  transactionId := intent.transactionId
  writes := earlier ++ [{ last with canonicalPostBytes := bytes, exactPost := ResourceBirthCodec.rootBytes bytes }]
  readGuards := intent.readGuards
  nullifiers := intent.nullifiers
  exactCharge := intent.exactCharge
  event := intent.event
  subject := intent.subject
  postRootsBound := by
    intro write member
    rcases List.mem_append.mp member with member | member
    · exact intent.postRootsBound write (by rw [shape]; exact List.mem_append_left _ member)
    · simp only [List.mem_singleton] at member; subst write; rfl
  guardsReadOnly := by
    intro guard member
    simpa [shape] using intent.guardsReadOnly guard member

/-- The tamper preserves the final write's exact CAS precondition. -/
theorem tamperLast_same_pre (intent : DataIntent ResourceBirthCodec.rootBytes)
    (earlier : List DataWrite) (last : DataWrite) (shape : intent.writes = earlier ++ [last])
    (bytes : List UInt8) :
    ((tamperLast intent earlier last shape bytes).writes.map fun w => (w.cellId, w.expectedPre)) =
      intent.writes.map (fun w => (w.cellId, w.expectedPre)) := by
  simp [tamperLast, shape]

theorem lookup_final_post (earlier : List DataWrite) (last : DataWrite)
    (unique : last.cellId ∉ earlier.map DataWrite.cellId) :
    DataSnapshot.lookupPostBytes last.cellId (earlier ++ [last]) = some last.canonicalPostBytes := by
  induction earlier with
  | nil => simp [DataSnapshot.lookupPostBytes]
  | cons first rest ih =>
    simp only [List.map_cons, List.mem_cons, not_or] at unique
    simp [DataSnapshot.lookupPostBytes, Ne.symm unique.1, ih unique.2]

/-- Post-admission substitution has a different payload view from the World
produced by the receiver's admitted turn, even with the same id and pre-root. -/
theorem tamper_breaks_payload_view {config : NativeHost.Config} {opened : NativeHost.Opened config}
    {ingress : ObjectiveActivityReceiver.DecodedIngress}
    (verdict : ActivityVerdict config opened ingress)
    {w w' : World deployedR TransactionId Digest} (rep : DeployedRepresents opened.durable w)
    {t : DTurn deployedR Digest}
    (derived : Turn.ofLoaded bridge DeployedHistory.history opened.durable verdict.intent = .ok t)
    (schedule : Schedule)
    (installs : Installs (execute schedule opened.durable.snapshot verdict.intent) = true)
    (stepped : World.step DeployedHistory.history w t = some w')
    (earlier : List DataWrite) (last : DataWrite) (shape : verdict.intent.writes = earlier ++ [last])
    (bytes : List UInt8)
    (changed : ObjectiveActivity.payloadOf last.canonicalPostBytes ≠ ObjectiveActivity.payloadOf bytes) :
    payloadsOf w' ≠ payloads (DataSnapshot.install opened.durable.snapshot
      (tamperLast verdict.intent earlier last shape bytes)).canonicalBytes := by
  have nodup : (verdict.intent.writes.map DataWrite.cellId).Nodup := by
    cases verdict with
    | accepted accepted => exact accepted.physical.1
    | failed failed => exact failed.physical.1
  have unique : last.cellId ∉ earlier.map DataWrite.cellId := by
    rw [shape, List.map_append, List.map_singleton] at nodup
    intro member
    exact (List.nodup_append.mp nodup).2.2 last.cellId member last.cellId (by simp) rfl
  obtain ⟨next, step, _, view⟩ := (objective_refines_step rep verdict derived schedule).1 installs
  have same : next = w' := Option.some.inj (step.symm.trans stepped)
  subst next
  rcases execute_cases schedule opened.durable.snapshot verdict.intent with
    ⟨_, _, _, after⟩ | ⟨no, _⟩
  · rw [after] at view
    intro eq
    have atLast := congrFun (view.trans eq) last.cellId
    have lookup := lookup_final_post earlier last unique
    have tampered := lookup_final_post earlier
      { last with canonicalPostBytes := bytes, exactPost := ResourceBirthCodec.rootBytes bytes } unique
    simp only [payloads, DataSnapshot.install_canonicalBytes, shape, lookup, Option.getD_some,
      tamperLast] at atLast
    rw [tampered] at atLast
    exact changed atLast
  · rw [installs] at no; cases no

/-- A concrete byte substitution at the same role and key changes the payload;
this supplies the tamper theorem's semantic difference without hash assumptions. -/
theorem changed_body_changes_payload :
    ObjectiveActivity.payloadOf (ObjectiveActivity.image .package [] [0]) ≠
      ObjectiveActivity.payloadOf (ObjectiveActivity.image .package [] [1]) := by
  rw [ObjectiveCheckpointInvariant.payloadOf_image, ObjectiveCheckpointInvariant.payloadOf_image]
  decide

#assert_axioms tamperLast_same_pre lookup_final_post tamper_breaks_payload_view changed_body_changes_payload

/-! World reachability: induction nodes are Worlds, never snapshots. -/

/-- The IO certificate's exact intent supplies the semantic step and the
post-view of the very World the certified Turn reaches. -/
theorem admissible_post_view {ob : ObjectiveActivity.Config}
    {w w' : ObjectiveAdmissible.W} {t : ObjectiveAdmissible.T}
    (cert : ObjectiveAdmissible.Admissible ob w t)
    (stepped : World.step DeployedHistory.history w t = some w') :
    let after := (execute .complete cert.loaded.snapshot cert.commit.intent).storeAfter cert.loaded.snapshot
    ObjectiveCheckpointInvariant.Step ob cert.loaded.snapshot after ∧
      payloads cert.loaded.snapshot.canonicalBytes = payloadsOf w ∧
      payloads after.canonicalBytes = payloadsOf w' := by
  obtain ⟨next, step, _, view⟩ := (intent_refines_step DeployedHistory.history
    cert.represents cert.commit.intent cert.commit.derived .complete).1 cert.commit.installs
  have same : next = w' := Option.some.inj (step.symm.trans stepped)
  subst next
  exact ⟨cert.commit.source.step .complete, payloads_of_represents cert.represents, view⟩

theorem world_step_checkpoints {ob : ObjectiveActivity.Config} {w w' : ObjectiveAdmissible.W}
    (step : ObjectiveAdmissible.WStep ob w w') (prior : CheckpointsTyped ob (payloadsOf w)) :
    CheckpointsTyped ob (payloadsOf w') := by
  cases step with
  | mk cert stepped =>
    obtain ⟨semantic, before, after⟩ := admissible_post_view cert stepped
    rw [← after]
    exact checkpointsTyped_payloads.mpr (semantic.preserves
      (checkpointsTyped_payloads.mp (before.symm ▸ prior)))

theorem world_step_domains {ob : ObjectiveActivity.Config} {w w' : ObjectiveAdmissible.W}
    (step : ObjectiveAdmissible.WStep ob w w')
    (prior : ObjectiveDomainInvariant.DomainsHold ob (payloadsOf w)) :
    ObjectiveDomainInvariant.DomainsHold ob (payloadsOf w') := by
  cases step with
  | mk cert stepped =>
    obtain ⟨semantic, before, after⟩ := admissible_post_view cert stepped
    rw [← after]
    exact ObjectiveDomainInvariant.Step.domainsHold semantic (before.symm ▸ prior)

theorem world_step_upgradable {ob : ObjectiveActivity.Config} {w w' : ObjectiveAdmissible.W}
    (book : ObjectiveUpgradeInvariant.BookUnprotected ob)
    (step : ObjectiveAdmissible.WStep ob w w')
    (prior : ObjectiveUpgradeInvariant.Upgradable ob (payloadsOf w)) :
    ObjectiveUpgradeInvariant.Upgradable ob (payloadsOf w') := by
  cases step with
  | mk cert stepped =>
    obtain ⟨semantic, before, after⟩ := admissible_post_view cert stepped
    rw [← after]
    exact ObjectiveUpgradeInvariant.Step.upgradable book semantic (before.symm ▸ prior)

/-- Every record in a World reached by any finite sequence of certified
World.step transitions has a typed checkpoint. -/
theorem reachable_stored_checkpoints_typed {ob : ObjectiveActivity.Config}
    {genesis w : ObjectiveAdmissible.W}
    (start : CheckpointsTyped ob (payloadsOf genesis))
    (reached : ObjectiveAdmissible.Reachable ob genesis w) :
    CheckpointsTyped ob (payloadsOf w) := by
  induction reached with
  | genesis => exact start
  | step _ step ih => exact world_step_checkpoints step ih

/-- Domain laws hold after every finite certified World execution. -/
theorem reachable_domain_holds_forever {ob : ObjectiveActivity.Config}
    {genesis w : ObjectiveAdmissible.W}
    (start : ObjectiveDomainInvariant.DomainsHold ob (payloadsOf genesis))
    (reached : ObjectiveAdmissible.Reachable ob genesis w) :
    ObjectiveDomainInvariant.DomainsHold ob (payloadsOf w) := by
  induction reached with
  | genesis => exact start
  | step _ step ih => exact world_step_domains step ih

theorem reachable_upgradable {ob : ObjectiveActivity.Config} {genesis w : ObjectiveAdmissible.W}
    (book : ObjectiveUpgradeInvariant.BookUnprotected ob)
    (start : ObjectiveUpgradeInvariant.Upgradable ob (payloadsOf genesis))
    (reached : ObjectiveAdmissible.Reachable ob genesis w) :
    ObjectiveUpgradeInvariant.Upgradable ob (payloadsOf w) := by
  induction reached with
  | genesis => exact start
  | step _ step ih => exact world_step_upgradable book step ih

/-- Live/rebirth/pending counts describe exactly the reached World's records. -/
theorem reachable_live_counts {ob : ObjectiveActivity.Config} {genesis w : ObjectiveAdmissible.W}
    (book : ObjectiveUpgradeInvariant.BookUnprotected ob)
    (start : ObjectiveUpgradeInvariant.Upgradable ob (payloadsOf genesis))
    (reached : ObjectiveAdmissible.Reachable ob genesis w) :
    ObjectiveUpgradeInvariant.LiveCounts ob (payloadsOf w) :=
  (reachable_upgradable book start reached).1

/-- Migration and the successor's state law hold on the reached World view;
Book payment remains the separate admission premise of the existing theorem. -/
theorem reachable_migrate_cannot_fail {ob : ObjectiveActivity.Config} {genesis w : ObjectiveAdmissible.W}
    (book : ObjectiveUpgradeInvariant.BookUnprotected ob)
    (start : ObjectiveUpgradeInvariant.Upgradable ob (payloadsOf genesis))
    (reached : ObjectiveAdmissible.Reachable ob genesis w) :
    ObjectiveUpgradeInvariant.MigratableStates ob (payloadsOf w) :=
  (reachable_upgradable book start reached).2

/-- The seat receiver supplies the inertness premise for this certified
World step: every activity payload in the reached World is unchanged. -/
theorem world_inert_agree {ob : ObjectiveActivity.Config}
    {w w' : ObjectiveAdmissible.W} {t : ObjectiveAdmissible.T}
    (cert : ObjectiveAdmissible.Admissible ob w t)
    {F : Type} [Field F] [DecidableEq F]
    {deployment : CanonicalCellRegistry.Deployment} {profile : CanonicalRuntimeProfile.Profile F}
    {ambient : ObjectiveKernelConfig.Ambient} {ingress : SeatReceiver.DecodedIngress}
    (accepted : SeatReceiver.Accepted deployment profile ambient cert.loaded ingress)
    (intent : cert.commit.intent = SeatReceiver.intent accepted)
    (stepped : World.step DeployedHistory.history w t = some w') :
    payloadsOf w' = payloadsOf w := by
  obtain ⟨_, before, after⟩ := admissible_post_view cert stepped
  rw [← after, ← before]
  rcases execute_no_partial_data_commit .complete cert.loaded.snapshot cert.commit.intent with unchanged | installed
  · rw [unchanged]
  · rw [installed, intent, ObjectiveUpgradeInvariant.install_payloads _ rfl,
      ObjectiveUpgradeInvariant.inert_agree accepted.prepared.decided.inert]

/-- The ordinary gate's frame law on a certified World step. Unlike the OB
induction headlines, this is deliberately a structural noninterference lemma. -/
theorem world_foreign_preserves {ob : ObjectiveActivity.Config}
    {w w' : ObjectiveAdmissible.W} {t : ObjectiveAdmissible.T}
    (cert : ObjectiveAdmissible.Admissible ob w t)
    (ordinary : ObjectiveActivityGate.ordinaryGate cert.commit.intent = .ok ())
    (stepped : World.step DeployedHistory.history w t = some w')
    (cell : DurableDataIntent.CellId) (isProtected : ObjectiveActivityGate.Protected cell) :
    payloadsOf w' cell = payloadsOf w cell := by
  obtain ⟨_, before, after⟩ := admissible_post_view cert stepped
  rw [← after, ← before]
  unfold payloads
  rw [ObjectiveActivityGate.ordinary_execute_protected .complete cert.loaded.snapshot ordinary isProtected]

#assert_axioms world_inert_agree world_foreign_preserves

#assert_axioms admissible_post_view world_step_checkpoints world_step_domains world_step_upgradable
#assert_axioms reachable_stored_checkpoints_typed reachable_domain_holds_forever
#assert_axioms reachable_upgradable reachable_live_counts reachable_migrate_cannot_fail

end Minidregg.Kernel.ObjectiveRefinesWorld
