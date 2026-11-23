/- A height-one instance of the deployed host submission theorem. -/
import Kernel.HostRefinesWorldCore
import Kernel.ObjectiveTurnTotality

namespace Minidregg.Kernel.HostRefinesWorld.SubmitWitness

open Minidregg.Compiler
open DurableReceiverIO DurableDataIntent DurableCheckpoint
open DurableCommitProtocol
open ObjectiveTurnTotality (freshRetirementIntent)
open TurnOfIntent World

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

private def seed : DurableReceiver.Seed := ⟨[], [], fun _ => 10⟩

private def initial : Loaded ResourceBirthCodec.rootBytes :=
  (loadSeed ResourceBirthCodec.rootBytes ⟨0⟩ seed).toOption.get (by decide +kernel)

private def initialWorld : DWorld :=
  ⟨0, TurnLog.genesisSystem seed.available⟩

private theorem initial_held : initial.track.world? = some initialWorld := rfl

private theorem preflight_writing {root : List UInt8 → Theory.TypedAuthorization.Digest}
    (before : DataSnapshot root) (intent : DataIntent root)
    (guards : intent.readGuardsMatchCheck before = true)
    (writes : intent.writes ≠ []) (erased : intent.erase.rootWrites ≠ [])
    (distinct : (intent.erase.rootWrites.map RootWrite.cellId).Nodup)
    (nodup : intent.erase.nullifiers.Nodup)
    (matched : intent.erase.rootsMatchCheck before.model = true)
    (fresh : intent.erase.nullifiersFreshCheck before.model = true)
    (budget : intent.erase.exactCharge.fundedCheck before.model.available = true) :
    intent.preflight before = .ok () := by
  simp only [DataIntent.preflight, guards, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
    writes, false_and, Intent.preflight, erased, distinct, nodup, decide_true, matched, fresh, budget]

private theorem prepared :
    DurableDataIntent.execute .complete initial.snapshot freshRetirementIntent =
      .accepted (DataSnapshot.install initial.snapshot freshRetirementIntent) := by
  apply DurableDataIntent.execute_complete_ready
  · rfl
  · have matched : freshRetirementIntent.erase.rootsMatchCheck initial.snapshot.model = true := by
      apply (Intent.rootsMatchCheck_eq_true_iff ..).2
      intro write member
      change write ∈ [_] at member
      rcases List.mem_singleton.mp member with rfl
      rfl
    have guards : freshRetirementIntent.readGuardsMatchCheck initial.snapshot = true := rfl
    have writes : freshRetirementIntent.writes ≠ [] := List.cons_ne_nil _ _
    have erased : freshRetirementIntent.erase.rootWrites ≠ [] := List.cons_ne_nil _ _
    have distinct : (freshRetirementIntent.erase.rootWrites.map RootWrite.cellId).Nodup :=
      List.nodup_singleton _
    have nodup : freshRetirementIntent.erase.nullifiers.Nodup := List.nodup_nil
    have fresh : freshRetirementIntent.erase.nullifiersFreshCheck initial.snapshot.model = true := rfl
    have budget : freshRetirementIntent.erase.exactCharge.fundedCheck initial.snapshot.model.available = true := by
      apply (Minidregg.Theory.ResourceCost.Charge.fundedCheck_eq_true_iff ..).2
      intro lane
      change freshRetirementIntent.exactCharge lane ≤ 10
      cases lane <;> decide +kernel
    exact preflight_writing _ _ guards writes erased distinct nodup matched fresh budget

private def ready : Ready _ initial.image initial.baseHeight initial.base initial.snapshot
    freshRetirementIntent :=
  ⟨_, prepared, resume_append _ _ _ _ _ _ _ initial.withinLog initial.resumed prepared⟩

private theorem advance_installs {root : List UInt8 → Theory.TypedAuthorization.Digest}
    {before next : DataSnapshot root} {height height' : Nat} {intent : DataIntent root}
    (executed : DurableDataIntent.execute .complete before intent = .accepted next)
    (up : height' = height + 1) (track : WorldTrack before height)
    {w after : DWorld} {t : DTurn DeployedBridge.deployedR Theory.TypedAuthorization.Digest}
    (held : track.world? = some w)
    (derived : Turn.ofIntent DeployedBridge.bridge DeployedHistory.history w intent = .ok t)
    (charge : t.charge = intent.exactCharge)
    (admit : World.admit DeployedHistory.history w t = .ok after) :
    (track.advance executed up).world? = some after := by
  cases track with
  | lost _ => cases held
  | held current rep =>
    cases held
    have funded := (congrArg (fun cost => DeployedCharge.mismatch cost intent.exactCharge) charge).trans
      (DeployedCharge.mismatch_self intent.exactCharge)
    have gates := (Minidregg.Kernel.World.admitPinned_by_eq DeployedHistory.history (fails := snapPinFails before w) w t
      (fun p _ => snapPinFails_eq rep p)).trans admit
    unfold WorldTrack.advance
    split <;> rename_i d
    · cases d.symm.trans derived
    · cases d.symm.trans derived
      split <;> rename_i c
      · cases c.symm.trans funded
      · split <;> rename_i g
        · cases g.symm.trans gates
        · cases g.symm.trans gates
          rfl

private theorem extend_installs {root : List UInt8 → Theory.TypedAuthorization.Digest}
    (loaded : Loaded root) {intent : DataIntent root}
    (r : Ready root loaded.image loaded.baseHeight loaded.base loaded.snapshot intent)
    {w after : DWorld} {t : DTurn DeployedBridge.deployedR Theory.TypedAuthorization.Digest}
    (held : loaded.track.world? = some w)
    (derived : Turn.ofIntent DeployedBridge.bridge DeployedHistory.history w intent = .ok t)
    (charge : t.charge = intent.exactCharge)
    (admit : World.admit DeployedHistory.history w t = .ok after) :
    (loaded.extend r).track.world? = some after :=
  advance_installs (loaded.extend_snapshot r ▸ r.executed)
    (by simp [Loaded.extend, DurableReceiver.Image.append]) loaded.track held derived charge admit

/-- The height-one record's canonical MAC input. The authenticated index starts empty. -/
private def firstCarried : DurableHistory.Carried :=
  let record := DurableReceiver.IntentRecord.ofIntent freshRetirementIntent
  let bytes := DurableCheckpointCodec.recordFrame.encode record
  let extended := initial.extend ready
  let leaf := DurableHistory.leafDigest 1 bytes extended.chain extended.worldRoot
  let rows := DurableIndex.IndexRows.changes 1 record.transactionId record.nullifiers ++
    DurableIndex.IndexRows.cellChanges 1 (record.writes.map DataWrite.cellId) ++
    DurableIndex.IndexRows.seqChanges 1 ((Theory.JournalSequences.distinct (JournalIndex.sequences record)).map (·, 0))
  ⟨extended.worldRoot, extended.chain, DurableHistory.frontierDigest 1 (DurableHistory.Frontier.push [] leaf),
    DurableIndex.rootOf (DurableIndex.modelApply [] rows)⟩

/-- Full executor acceptance and a derived World step inhabit the exact append premise.
The stored height-one trailer verifies to the installed physical root. -/
theorem host_submit_authenticated_witness (key : DurableCheckpointCodec.MacKey) :
    ∃ append : Appended ResourceBirthCodec.rootBytes initial freshRetirementIntent,
      DurableHistory.verifyTagged key 1 append.entry.tag firstCarried.chain firstCarried.frontier
        firstCarried.indexRoot = .ok append.next.worldRoot := by
  have derivedOk : (Turn.ofIntent DeployedBridge.bridge DeployedHistory.history initialWorld
      freshRetirementIntent).isOk = true := by decide +kernel
  cases derived : Turn.ofIntent DeployedBridge.bridge DeployedHistory.history initialWorld
      freshRetirementIntent with
  | error e => rw [derived] at derivedOk; cases derivedOk
  | ok t =>
    obtain ⟨after, step, _, _⟩ := ofIntent_step DeployedBridge.bridge DeployedHistory.history derived
      (show initialWorld.head = some (0, ⟨0⟩) from rfl)
      (show initialWorld.journal freshRetirementIntent.transactionId = none from rfl)
      (by decide +kernel)
      (by intro n hn; simp [freshRetirementIntent, ObjectiveActivityWire.intentOf,
        ObjectiveTurnTotality.sealing] at hn)
      (by intro lane ne; cases lane <;> decide +kernel)
      (by decide +kernel)
      (fun _ ne => absurd rfl ne)
      (by
        intro wr hw
        change wr ∈ [_] at hw
        rcases List.mem_singleton.mp hw with rfl
        rw [DeployedHistory.history_cellDigest, DeployedBridge.bridge_pin]
        rfl)
      (by intro g hg; simp [freshRetirementIntent, ObjectiveActivityWire.intentOf,
        ObjectiveActivityWire.readOnly, ObjectiveTurnTotality.sealing] at hg)
    have charge : t.charge = freshRetirementIntent.exactCharge := by
      have chargeCheck : (Turn.ofIntent DeployedBridge.bridge DeployedHistory.history initialWorld
          freshRetirementIntent).toOption.map (fun turn =>
          DeployedCharge.mismatch turn.charge freshRetirementIntent.exactCharge) = some none := by
        decide +kernel
      rw [derived] at chargeCheck
      exact DeployedCharge.mismatch_none (Option.some.inj chargeCheck)
    have admits := (step_eq_some DeployedHistory.history).1 step
    let extended := initial.extend ready
    have installed : extended.track.world? = some after :=
      extend_installs initial ready initial_held derived charge admits
    let entry : Entry := ⟨(DurableCheckpointCodec.recordFrame.encode
      (DurableReceiver.IntentRecord.ofIntent freshRetirementIntent)).toByteArray, DurableHistory.trailer key 1 firstCarried⟩
    refine ⟨⟨{ extended with headTag := some entry.tag },
      rfl, entry, DurableHistory.toByteArray_toList _, rfl,
      ⟨initialWorld, t, after, initial_held, installed, derived, charge, admits⟩⟩, ?_⟩
    exact DurableHistory.verifyTagged_trailer key 1 firstCarried

private def witnessKey : DurableCheckpointCodec.MacKey := ⟨List.replicate 32 0x31, by simp⟩

theorem host_submit_is_step_inhabited :
    Nonempty (Appended ResourceBirthCodec.rootBytes initial freshRetirementIntent) := by
  obtain ⟨append, _⟩ := host_submit_authenticated_witness witnessKey
  exact ⟨append⟩

/-- Altering one receipt's digest gives a concrete failed root correspondence. -/
theorem host_submit_forged_root_inhabited :
    ∃ append : Appended ResourceBirthCodec.rootBytes initial freshRetirementIntent,
      (⟨append.next.worldRoot.value + 1⟩ : Theory.TypedAuthorization.Digest) ≠
        WorldRoot.deployedRoot (entriesOf append.next.image append.next.snapshot append.next.chain) := by
  obtain ⟨append⟩ := host_submit_is_step_inhabited
  exact ⟨append, host_submit_forged_root append fun eq =>
    Nat.succ_ne_self _ (congrArg Theory.TypedAuthorization.Digest.value eq)⟩

/-- info: 'Minidregg.Kernel.HostRefinesWorld.SubmitWitness.host_submit_authenticated_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms host_submit_authenticated_witness

/-- info: 'Minidregg.Kernel.HostRefinesWorld.SubmitWitness.host_submit_forged_root_inhabited' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms host_submit_forged_root_inhabited

/-- info: 'Minidregg.Kernel.HostRefinesWorld.SubmitWitness.host_submit_is_step_inhabited' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms host_submit_is_step_inhabited

end Minidregg.Kernel.HostRefinesWorld.SubmitWitness
