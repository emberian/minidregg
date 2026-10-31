/-
# Kernel.SnapRepresents -- what it means for a deployed snapshot to represent a World

Below `Compiler.DurableReceiverCore`, so a `Loaded` can carry its World and the
proof that its snapshot represents it (FD-1 4a).  `SnapRepresents`, the
executor's shapes, `ofIntent_run` (a represented snapshot's admitted intent is a
`World.step` of its derived turn) moved here unchanged from
`Kernel.HostRefinesWorldCore` (same namespace, same statements); `replay_model`/`resume_model`
live in `Kernel.DurableEngine`.
-/
module

public import Kernel.TurnOfIntent
public import Kernel.DurableCheckpoint
public import Kernel.DurableEngine
public import Theory.AssertAxioms

-- Bodies this file reduces or derives through, not exposed by their modules (module system).
import all Init.Data.Repr
import all Init.Data.ToString.Basic
import all Init.Data.ToString.Extra
import all Init.Data.Array.Basic
import all Init.Data.ByteArray.Basic
import all Init.Data.String.Decode
import all Init.Data.String.Defs
import all Init.Control.Except
import all Init.Data.List.Basic
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.String.Bootstrap
import all Init.Data.Format.Basic
import all Init.Data.List.Scan.Basic

@[expose] public section

namespace Minidregg.Kernel.HostRefinesWorld

open Minidregg.Theory.Store
open Minidregg.Kernel.World
open Minidregg.Kernel.TurnOfIntent
open Minidregg.Theory.ResourceCost (Lane Charge)
open Minidregg.Kernel.DurableCommitProtocol (Snapshot Schedule CrashPoint)
open Minidregg.Kernel.DurableDataIntent
  (DataIntent DataSnapshot StableEvent StableNullifier TransactionId Outcome execute)

set_option autoImplicit false

section Represent

variable {R : Registry} {D : Type} [DecidableEq D] [Minidregg.Theory.StoreKey D]
variable {rootBytes : List UInt8 → Theory.TypedAuthorization.Digest}

/-- The held cells a deployed snapshot decodes to. -/
def cellsOf (B : Bridge R D) (snap : DataSnapshot rootBytes) (c : CellId) : Option (Cell R) :=
  (B.codec.decode (snap.canonicalBytes ⟨c⟩)).getD none

/-- **What it means for a deployed snapshot at a height to represent a world.** -/
structure SnapRepresents (B : Bridge R D) (snap : DataSnapshot rootBytes) (height : Nat)
    (w : World R TransactionId D) : Prop where
  /-- Every cell's canonical bytes decode to exactly the world's cell. -/
  cells : ∀ c : CellId, B.codec.decode (snap.canonicalBytes ⟨c⟩) = some (w.cells c)
  /-- The spent set is the consumed set, under the injective key. -/
  spent : ∀ d, (w.spent d).isSome = true ↔ ∃ n, B.key n = d ∧ snap.model.consumed n = true
  /-- The journal holds exactly the journaled transaction ids. -/
  journal : ∀ x, (w.journal x).isSome = (Snapshot.lookupRecorded x snap.model.journal).isSome
  /-- The clock: the head height is the deployed height. -/
  head : ∃ r, w.head = some (height, r)
  /-- Every meter lane, storage included, is recorded and is the deployed allowance:
  the Host debits the derived turn's charge (G-CHARGE, the append path refuses any
  other) and credits its credit. Recorded, not read through `getD 0`, so the World's
  guarded allowance write is valid on a credited lane at an exhausted meter. -/
  meter : ∀ l, w.allowanceOf l = some (snap.model.available l)
  /-- A cell is retired exactly when its deployed bytes are the retirement. -/
  retired : ∀ c, (w.retired c).isSome = B.codec.retires (snap.canonicalBytes ⟨c⟩)
  /-- No parent rows: the present Host keeps parentage in the authority
  cell's plane 13, inside a cell's bytes (G-PARENT, T7). -/
  parent : ∀ c, w.parent c = none

/-- The meter reading of a represented World is the deployed allowance. -/
theorem SnapRepresents.meter_eq {B : Bridge R D} {snap : DataSnapshot rootBytes} {height : Nat}
    {w : World R TransactionId D} (rep : SnapRepresents B snap height w) (l : Lane) :
    w.meter l = snap.model.available l := by
  show (w.allowanceOf l).getD 0 = _
  rw [rep.meter l]
  rfl

theorem cellsOf_eq {B : Bridge R D} {snap : DataSnapshot rootBytes} {height : Nat}
    {w : World R TransactionId D} (rep : SnapRepresents B snap height w) (c : CellId) :
    w.cells c = cellsOf B snap c := by
  simp [cellsOf, rep.cells c]

/-! ### The executor's outcomes -/

/-- Whether an outcome installed the intent. -/
def Installs : Outcome rootBytes → Bool
  | .accepted _ => true
  | .crashed .afterAtomicInstall _ => true
  | _ => false

/-- **The executor's two shapes**: it installed (the id was fresh and the
preflight passed), or it left the snapshot as it was. -/
theorem execute_cases (schedule : Schedule) (before : DataSnapshot rootBytes)
    (intent : DataIntent rootBytes) :
    (Installs (execute schedule before intent) = true ∧
        Snapshot.lookupRecorded intent.transactionId before.model.journal = none ∧
        intent.preflight before = .ok () ∧
        (execute schedule before intent).storeAfter before = DataSnapshot.install before intent) ∨
      (Installs (execute schedule before intent) = false ∧
        (execute schedule before intent).storeAfter before = before) := by
  unfold execute
  split
  · split <;> exact .inr ⟨rfl, rfl⟩
  · rename_i hl
    split
    · exact .inr ⟨rfl, rfl⟩
    · rename_i hp
      cases schedule with
      | complete => exact .inl ⟨rfl, hl, hp, rfl⟩
      | crash pt =>
          cases pt
          · exact .inr ⟨rfl, rfl⟩
          · exact .inl ⟨rfl, hl, hp, rfl⟩

set_option backward.isDefEq.respectTransparency false in
/-- What a passing preflight establishes about the nullifiers and the meter. -/
theorem preflight_facts {before : DataSnapshot rootBytes} {intent : DataIntent rootBytes}
    (ok : intent.preflight before = .ok ()) :
    intent.nullifiers.Nodup ∧ (∀ n ∈ intent.nullifiers, before.model.consumed n = false) ∧
      intent.exactCharge ≤ before.model.available := by
  have lower : intent.erase.preflight before.model = .ok () := by
    unfold DataIntent.preflight at ok
    split at ok
    · cases ok
    split at ok
    · cases ok
    split at ok
    · cases ok
    · assumption
  have fresh := DurableCommitProtocol.Intent.preflight_ok_fresh _ _ lower
  unfold DurableCommitProtocol.Intent.preflight at lower
  split_ifs at lower with h1 h2 h3 h4 h5 h6
  refine ⟨?_, ?_, ?_⟩
  · simpa using h3
  · intro n m
    exact (DurableCommitProtocol.Intent.nullifiersFreshCheck_eq_true_iff _ _).mp fresh n
      (by simpa using m)
  · exact (Theory.ResourceCost.Charge.fundedCheck_eq_true_iff _ _).mp (by simpa using h6)

/-- What a passing preflight establishes about the asserted pre-roots: every
write's `expectedPre` and every read guard's `expectedRoot` is the snapshot's
root of its cell. -/
theorem preflight_roots {before : DataSnapshot rootBytes} {intent : DataIntent rootBytes}
    (ok : intent.preflight before = .ok ()) :
    (∀ wr ∈ intent.writes, before.model.roots wr.cellId = wr.expectedPre) ∧
      ∀ g ∈ intent.readGuards, before.model.roots g.cellId = g.expectedRoot := by
  have hg : intent.readGuardsMatchCheck before = true := by
    unfold DataIntent.preflight at ok
    cases h : intent.readGuardsMatchCheck before
    · simp [h] at ok
    · rfl
  have lower : intent.erase.preflight before.model = .ok () := by
    unfold DataIntent.preflight at ok
    split at ok
    · cases ok
    split at ok
    · cases ok
    split at ok
    · cases ok
    · assumption
  refine ⟨fun wr m => ?_, (DataIntent.readGuardsMatchCheck_eq_true_iff _ _).mp hg⟩
  unfold DurableCommitProtocol.Intent.preflight at lower
  split_ifs at lower with h1 h2 h3 h4 h5 h6
  have roots : ∀ a ∈ intent.writes, before.model.roots a.cellId = a.expectedPre := by
    simpa using h4
  exact roots wr m

/-- **The intent's pins hold at a represented world** whose snapshot passes
preflight: under pin coherence, each asserted root read as a pin is the
world's digest of that cell's slot. -/
theorem pins_of_preflight (B : Bridge R D) (H : History R TransactionId StableEvent D)
    {snap : DataSnapshot rootBytes} {height : Nat} {w : World R TransactionId D}
    (rep : SnapRepresents B snap height w) (coherent : PinCoherent B H rootBytes)
    {intent : DataIntent rootBytes} {t : DTurn R D}
    (derived : Turn.ofIntent B H w intent = .ok t) (ready : intent.preflight snap = .ok ()) :
    (∀ wr ∈ intent.writes, H.cellDigest (w.cells wr.cellId.value) = B.pin wr.expectedPre) ∧
      ∀ g ∈ intent.readGuards, H.cellDigest (w.cells g.cellId.value) = B.pin g.expectedRoot := by
  have d := ofCells_ok derived
  obtain ⟨wroots, groots⟩ := preflight_roots ready
  have at_cell : ∀ c : DurableDataIntent.CellId, (w.retired c.value).isSome = false →
      H.cellDigest (w.cells c.value) = B.pin (snap.model.roots c) := by
    intro c unretired
    have live : B.codec.retires (snap.canonicalBytes c) = false :=
      (rep.retired c.value).symm.trans unretired
    rw [coherent _ _ (rep.cells c.value) live, snap.coherent]
  refine ⟨fun wr hw => ?_, fun g hg => ?_⟩
  · rw [at_cell wr.cellId (written_unretired d hw), wroots wr hw]
  · rw [at_cell g.cellId (d.guards_unretired _ (guard_mem_guardIds hg)), groots g hg]

/-! ### `ofIntent_run` -/

theorem lookupPostBytes_some {c : DurableDataIntent.CellId} :
    ∀ {ws : List DurableDataIntent.DataWrite} {b : List UInt8},
      DataSnapshot.lookupPostBytes c ws = some b →
        ∃ w0 ∈ ws, w0.cellId = c ∧ w0.canonicalPostBytes = b
  | [], _, h => by cases h
  | w0 :: rest, b, h => by
      unfold DataSnapshot.lookupPostBytes at h
      split at h
      · rename_i e
        exact ⟨w0, by simp, e, Option.some.inj h⟩
      · obtain ⟨w1, m, e, eb⟩ := lookupPostBytes_some h
        exact ⟨w1, by simp [m], e, eb⟩

omit [DecidableEq D] in
theorem decodes_of_derived {B : Bridge R D} {H : History R TransactionId StableEvent D}
    {cells : CellId → Option (Cell R)} {retired : CellId → Bool} {intent : DataIntent rootBytes}
    {t : DTurn R D}
    (d : Derived B H cells retired intent t) {w0 : DurableDataIntent.DataWrite} (hw : w0 ∈ intent.writes) :
    ∃ v, B.codec.decode w0.canonicalPostBytes = some v := by
  obtain ⟨δ, hδ, -, -⟩ := delta_of_write d hw
  have spec := deltaOf_spec hδ
  cases δ with
  | absent => exact ⟨_, spec.2.1⟩
  | burn => exact ⟨_, spec.2.1⟩
  | create => exact ⟨_, spec.2⟩
  | change => exact ⟨_, spec.2⟩
  | retire => exact ⟨_, spec.2.1⟩

theorem lookupPostBytes_none_unwritten {c : CellId} :
    ∀ {ws : List DurableDataIntent.DataWrite}, DataSnapshot.lookupPostBytes ⟨c⟩ ws = none →
      c ∉ writeIds ws
  | [], _ => by simp [writeIds]
  | w0 :: rest, h => by
      unfold DataSnapshot.lookupPostBytes at h
      split at h
      · cases h
      · rename_i ne
        intro m
        simp only [writeIds, List.map_cons, List.mem_cons] at m
        rcases m with e | m
        · exact ne (by rw [e])
        · exact lookupPostBytes_none_unwritten h m

/-- `ofIntent_run` with the pins given: from a represented snapshot, an intent
the executor would install, and its derived turn charged the intent's charge
and whose pins hold at the world, `World.step` accepts the turn and its world
represents `DataSnapshot.install` one height up. -/
theorem ofIntent_run_pinned (B : Bridge R D) (H : History R TransactionId StableEvent D)
    {snap : DataSnapshot rootBytes} {height : Nat} {w : World R TransactionId D}
    (rep : SnapRepresents B snap height w)
    {intent : DataIntent rootBytes} {t : DTurn R D}
    (derived : Turn.ofIntent B H w intent = .ok t)
    (charged : t.charge = intent.exactCharge)
    (fresh : Snapshot.lookupRecorded intent.transactionId snap.model.journal = none)
    (ready : intent.preflight snap = .ok ())
    (pinsHold : ∀ p ∈ t.pins, w.retired p.1 = none ∧ H.cellDigest (w.cells p.1) = p.2) :
    ∃ w', World.step H w t = some w' ∧
      SnapRepresents B (DataSnapshot.install snap intent) (height + 1) w' := by
  obtain ⟨r, hh⟩ := rep.head
  obtain ⟨nodup, unconsumed, funded⟩ := preflight_facts ready
  have jfresh : w.journal intent.transactionId = none := by
    have := rep.journal intent.transactionId
    rw [fresh] at this
    simpa using this
  have unspent : ∀ n ∈ intent.nullifiers, w.spent (B.key n) = none := by
    intro n m
    cases hs : w.spent (B.key n) with
    | none => rfl
    | some u =>
        obtain ⟨n', hk, hc⟩ := (rep.spent (B.key n)).mp (by simp [hs])
        have e := B.key_injective hk
        subst e
        rw [unconsumed _ m] at hc
        cases hc
  have fundedL : ∀ l, l ≠ .storageBytes → intent.exactCharge l ≤ w.meter l := by
    intro l _
    rw [rep.meter_eq l]
    exact funded l
  have fundedS : intent.exactCharge .storageBytes ≤ w.meter .storageBytes := by
    rw [rep.meter_eq]
    exact funded _
  obtain ⟨w', hs, hcells, hsys⟩ := ofCells_step B H (fun _ => rfl) (fun _ => rfl) derived hh jfresh
    nodup unspent fundedL fundedS (fun l _ => ⟨_, rep.meter l⟩) pinsHold
  have derived' : ofCells B H (fun c => w.cells c) (fun c => (w.retired c).isSome) intent = .ok t := derived
  obtain ⟨htx, hret, hrows, hnull, -, -⟩ := ofCells_fields derived
  have d := ofCells_ok derived
  refine ⟨w', hs, ⟨fun c => ?_, fun dd => ?_, fun x => ?_, ⟨H.chain r (H.turnDigest t), ?_⟩, fun l => ?_,
    fun c => ?_, fun c => ?_⟩⟩
  · -- cells
    rw [DataSnapshot.install_canonicalBytes, hcells c]
    cases hl : DataSnapshot.lookupPostBytes ⟨c⟩ intent.writes with
    | none =>
        simp only [Option.getD_none]
        unfold postCell
        rw [hl]
        exact rep.cells c
    | some b =>
        simp only [Option.getD_some]
        obtain ⟨w0, hw, -, rfl⟩ := lookupPostBytes_some hl
        obtain ⟨v, hv⟩ := decodes_of_derived d hw
        unfold postCell
        rw [hl]
        show B.codec.decode w0.canonicalPostBytes =
          some ((B.codec.decode w0.canonicalPostBytes).getD (w.cells c))
        rw [hv]
        rfl
  · -- spent
    show (w'.system ⟨SysSpace.spent, dd⟩).isSome = true ↔ _
    rw [hsys, sysPost_spent, hnull]
    have inst : ∀ n, (DataSnapshot.install snap intent).model.consumed n =
        (if n ∈ intent.nullifiers then true else snap.model.consumed n) := fun _ => rfl
    simp only [inst]
    by_cases hm : dd ∈ intent.nullifiers.map B.key
    · rw [if_pos hm]
      obtain ⟨n, hn, rfl⟩ := List.mem_map.mp hm
      exact ⟨fun _ => ⟨n, rfl, by simp [hn]⟩, fun _ => rfl⟩
    · rw [if_neg hm]
      rw [show (w.system ⟨SysSpace.spent, dd⟩).isSome = (w.spent dd).isSome from rfl, rep.spent dd]
      constructor
      · rintro ⟨n, hk, hc⟩
        exact ⟨n, hk, by simp [hc]⟩
      · rintro ⟨n, hk, hc⟩
        refine ⟨n, hk, ?_⟩
        by_cases hn : n ∈ intent.nullifiers
        · exact absurd (List.mem_map.mpr ⟨n, hn, hk⟩) hm
        · simpa [hn] using hc
  · -- journal
    show (w'.system ⟨SysSpace.journal, x⟩).isSome = _
    rw [hsys, sysPost_journal, htx]
    have inst : Snapshot.lookupRecorded x (DataSnapshot.install snap intent).model.journal =
        if intent.transactionId = x then some intent.erase
        else Snapshot.lookupRecorded x snap.model.journal := rfl
    rw [inst]
    by_cases e : x = intent.transactionId
    · rw [if_pos e, if_pos e.symm]
      rfl
    · rw [if_neg e, if_neg (Ne.symm e)]
      exact rep.journal x
  · -- head
    show w'.system ⟨SysSpace.head, ()⟩ = _
    rw [hsys, sysPost_head]
  · -- meter
    have credited : t.credit = intent.credit := ofIntent_credit derived
    show w'.system ⟨SysSpace.allowance, l⟩ =
      some (snap.model.available l - intent.exactCharge l + intent.credit l)
    rw [hsys, sysPost_allowance, ← charged, ← credited, ← rep.meter_eq l]
    split
    · rfl
    · rename_i z
      simp only [not_or, not_not] at z
      rw [z.1, z.2, Nat.sub_zero, Nat.add_zero, rep.meter_eq l]
      exact rep.meter l
  · -- retired
    show (w'.system ⟨SysSpace.retired, c⟩).isSome =
      B.codec.retires ((DataSnapshot.install snap intent).canonicalBytes ⟨c⟩)
    rw [hsys, sysPost_retired, DataSnapshot.install_canonicalBytes]
    cases hl : DataSnapshot.lookupPostBytes ⟨c⟩ intent.writes with
    | none =>
        have nr : c ∉ t.retires := fun m => lookupPostBytes_none_unwritten hl (retires_written derived' m)
        simp only [nr, if_false, Option.getD_none]
        exact rep.retired c
    | some b =>
        obtain ⟨w0, hw, e, rfl⟩ := lookupPostBytes_some hl
        have same : w0.cellId.value = c := by rw [e]
        have iff := retires_iff derived' w0 hw
        rw [same] at iff
        simp only [Option.getD_some]
        by_cases r : B.codec.retires w0.canonicalPostBytes = true
        · rw [if_pos (iff.mpr r), r]; rfl
        · rw [if_neg (fun m => r (iff.mp m))]
          have unretired := written_unretired (ofCells_ok derived') hw
          rw [same] at unretired
          have unretired' : (w.system ⟨SysSpace.retired, c⟩).isSome = false := unretired
          rw [unretired']
          cases hb : B.codec.retires w0.canonicalPostBytes
          · rfl
          · exact absurd hb r
  · -- parent
    show w'.system ⟨SysSpace.parent, c⟩ = none
    rw [hsys, run_sysPatch_core H _ _ _ _ _ _ (fun e => SysSpace.noConfusion e)
      (fun e => SysSpace.noConfusion e)]
    unfold sysCore
    rw [hrows]
    simp only [List.map_nil, List.append_nil, Patch.run_append, run_createReads, Patch.run_cons, Patch.run_nil,
      op_apply_write, op_apply_allocate]
    rw [Store.set_ne _ _ _ _ (sys_space_ne (fun e => SysSpace.noConfusion e)),
      run_retireAllocs_ne _ _ _ (fun e => SysSpace.noConfusion e),
      Store.set_ne _ _ _ _ (sys_space_ne (fun e => SysSpace.noConfusion e))]
    exact rep.parent c

/-- **`ofIntent_run`.**  `World.step H w (ofIntent w i)` is the deployed
post-state: from a represented snapshot, an intent the executor would install
(fresh id, passing preflight) and its derived turn whose charge is the intent's
(`charged`: the Host debits what the World debits), `World.step` accepts the
turn and its world represents `DataSnapshot.install` one height up.  The
turn's pins are the intent's asserted roots; `coherent` (proved for the
deployed bridge and history, `DeployedHistory.deployed_pinCoherent`) is what
makes the preflight's root equalities the World's pin equalities. -/
theorem ofIntent_run (B : Bridge R D) (H : History R TransactionId StableEvent D)
    {snap : DataSnapshot rootBytes} {height : Nat} {w : World R TransactionId D}
    (rep : SnapRepresents B snap height w) (coherent : PinCoherent B H rootBytes)
    {intent : DataIntent rootBytes} {t : DTurn R D}
    (derived : Turn.ofIntent B H w intent = .ok t)
    (charged : t.charge = intent.exactCharge)
    (fresh : Snapshot.lookupRecorded intent.transactionId snap.model.journal = none)
    (ready : intent.preflight snap = .ok ()) :
    ∃ w', World.step H w t = some w' ∧
      SnapRepresents B (DataSnapshot.install snap intent) (height + 1) w' := by
  obtain ⟨pinned, guarded⟩ := pins_of_preflight B H rep coherent derived ready
  exact ofIntent_run_pinned B H rep derived charged fresh ready
    (pinsHold_of_intent derived pinned guarded)

/-- **An accepted execution from a represented snapshot is an admitted turn**:
the executor's `.accepted next` and the derived turn give `World.admit = .ok w'`
with `next` representing `w'` one height up (`ofIntent_run`, read at `admit`). -/
theorem admit_of_accepted (B : Bridge R D) (H : History R TransactionId StableEvent D)
    {snap next : DataSnapshot rootBytes} {height : Nat} {w : World R TransactionId D}
    (rep : SnapRepresents B snap height w) (coherent : PinCoherent B H rootBytes)
    {intent : DataIntent rootBytes} {t : DTurn R D}
    (derived : Turn.ofIntent B H w intent = .ok t)
    (charged : t.charge = intent.exactCharge)
    (executed : execute .complete snap intent = .accepted next) :
    ∃ w', World.admit H w t = .ok w' ∧ SnapRepresents B next (height + 1) w' := by
  rcases execute_cases .complete snap intent with ⟨-, fresh, ready, after⟩ | ⟨installs, -⟩
  · obtain ⟨w', hs, hrep⟩ := ofIntent_run B H rep coherent derived charged fresh ready
    have hn : next = DataSnapshot.install snap intent := by
      rw [executed] at after; exact after
    refine ⟨w', ?_, hn ▸ hrep⟩
    unfold World.step at hs
    cases ha : World.admit H w t with
    | error r => rw [ha] at hs; cases hs
    | ok v => rw [ha] at hs; cases hs; rfl
  · rw [executed] at installs; simp [Installs] at installs

/-- **An admitted turn's world is represented**: from a represented snapshot,
an accepted execution and its derived turn charged the intent's charge, the
world `World.admit` returned represents the executed snapshot one height up.
No coherence premise: the World's own pin check, which admitted the turn, is
what the representation needs of the pins. -/
theorem represents_of_admitted (B : Bridge R D) (H : History R TransactionId StableEvent D)
    {snap next : DataSnapshot rootBytes} {height : Nat} {w w' : World R TransactionId D}
    (rep : SnapRepresents B snap height w) {intent : DataIntent rootBytes} {t : DTurn R D}
    (derived : Turn.ofIntent B H w intent = .ok t)
    (charged : t.charge = intent.exactCharge)
    (executed : execute .complete snap intent = .accepted next)
    (admitted : World.admit H w t = .ok w') :
    SnapRepresents B next (height + 1) w' := by
  obtain ⟨height', logRoot, -, hk⟩ := admit_ok_turnCheck H admitted
  have pinsHold := ((turnCheck_eq_none_iff H).1 hk).1
  rcases execute_cases .complete snap intent with ⟨-, fresh, ready, after⟩ | ⟨installs, -⟩
  · obtain ⟨w'', hs, hrep⟩ := ofIntent_run_pinned B H rep derived charged fresh ready pinsHold
    have hn : next = DataSnapshot.install snap intent := by
      rw [executed] at after; exact after
    rw [(step_eq_some H).1 hs] at admitted
    cases admitted
    exact hn ▸ hrep
  · rw [executed] at installs; simp [Installs] at installs

/-- **The receiver preflight's guard checks are a corollary of admission.**
At a represented world, under pin coherence and an injective pin reading
(deployed: the identity), if the World admits an intent's derived turn then
every read guard matches the snapshot (`readGuardsMatchCheck`) and every
write's `expectedPre` is the snapshot's root of its cell: the World's pin check
decided everything the receiver's staleness checks decide. -/
theorem preflight_of_admit (B : Bridge R D) (H : History R TransactionId StableEvent D)
    {snap : DataSnapshot rootBytes} {height : Nat} {w : World R TransactionId D}
    (rep : SnapRepresents B snap height w) (coherent : PinCoherent B H rootBytes)
    (pinInj : Function.Injective B.pin)
    {intent : DataIntent rootBytes} {t : DTurn R D}
    (derived : Turn.ofIntent B H w intent = .ok t)
    {w' : World R TransactionId D} (admitted : World.admit H w t = .ok w') :
    intent.readGuardsMatchCheck snap = true ∧
      ∀ wr ∈ intent.writes, snap.model.roots wr.cellId = wr.expectedPre := by
  have d := ofCells_ok derived
  have hpins : t.pins = pinsOf B intent := by rw [d.eq]; rfl
  obtain ⟨height', logRoot, -, hk⟩ := admit_ok_turnCheck H admitted
  have held := ((turnCheck_eq_none_iff H).1 hk).1
  have root_of_pin : ∀ (c : DurableDataIntent.CellId) (asserted : Theory.TypedAuthorization.Digest),
      (c.value, B.pin asserted) ∈ t.pins → snap.model.roots c = asserted := by
    intro c asserted m
    obtain ⟨unretired, same⟩ := held _ m
    have live : B.codec.retires (snap.canonicalBytes c) = false :=
      (rep.retired c.value).symm.trans (by simp [unretired])
    rw [coherent _ _ (rep.cells c.value) live, snap.coherent] at same
    exact pinInj same
  refine ⟨(DataIntent.readGuardsMatchCheck_eq_true_iff _ _).mpr fun g hg => ?_, fun wr hw => ?_⟩
  · exact root_of_pin g.cellId g.expectedRoot
      (by rw [hpins]; exact List.mem_append_right _ (List.mem_map_of_mem hg))
  · exact root_of_pin wr.cellId wr.expectedPre
      (by rw [hpins]; exact List.mem_append_left _ (List.mem_map_of_mem hw))

end Represent

#assert_axioms cellsOf_eq
#assert_axioms execute_cases
#assert_axioms preflight_facts
#assert_axioms lookupPostBytes_some
#assert_axioms decodes_of_derived
#assert_axioms ofIntent_run
#assert_axioms ofIntent_run_pinned
#assert_axioms represents_of_admitted
#assert_axioms admit_of_accepted
#assert_axioms preflight_roots
#assert_axioms pins_of_preflight
#assert_axioms preflight_of_admit

end Minidregg.Kernel.HostRefinesWorld
