/-
# Kernel.HostRefinesWorld -- the present Host is an implementation refinement of `World.step`

SURPASS §2(b), stage 0, lane T3.  No Host byte changes.  The deployed
transition is `DurableDataIntent.execute` (reached through
`DurableCheckpoint.prepare`) followed by the append that `Loaded.extend` makes;
its state is `DurableReceiverIO.Loaded`.  This module says what it means for a
`Loaded` to represent a `World` and proves that every deployed step -- accepted,
refused, replayed, crashed before or after the atomic install -- represents
either the old world or the world `World.step` produces on the turn
`Turn.ofIntent` derives from the admitted intent.

* `Represents B p w` (`SnapRepresents` on `p.snapshot` at `p.height`): every
  cell's canonical bytes decode to the world's cell; the spent set is the
  consumed set under the injective key; the journal holds exactly the
  journaled ids; the head height is the log length; every meter lane but
  storage is the deployed allowance; the storage lane is at least the deployed
  one; no cell is retired; the system cell holds no parent rows.  Each of the
  last three is a named gap, not a weakening (see the T3 report, §3).
* `ofIntent_run`: from a represented snapshot, an intent the executor accepts
  and its derived turn, `World.step` accepts the turn and its world represents
  `DataSnapshot.install` one height up.
* `deployed_refines_step`: an `ImplementationRefinement` instance for
  `HostStep` (execute under any schedule, then append).  `extendStep`,
  `refusedStep` and `failedAppendStep` show the real code paths are `HostStep`s.
* `host_trace_represents_fold`: whatever refusals and crashes the deployed Host
  went through, its state represents the fold of a sublist of what it was
  given.
* The refuting poles: `appendOnly_rewrite_has_no_turn` and
  `rom_image_has_no_turn` (no turn at all produces such a cell), the deployed
  instance `policy_source_birth_has_no_turn` (install's and every
  initial-policy birth's source cell), and the toy run where `ofIntent` refuses
  the rewrite while deriving and stepping the satisfiable write.
-/
import Kernel.TurnOfIntent
import Kernel.TurnRecord
import Compiler.DurableReceiverIO
import Compiler.CanonicalCellRegistry
import Kernel.NativeHostReplay
import Theory.AssertAxioms

namespace Minidregg.Kernel.HostRefinesWorld

open Minidregg.Theory.Store
open Minidregg.Kernel.World
open Minidregg.Kernel.TurnOfIntent
open Minidregg.Kernel.TurnRecord (ImplementationRefinement Trace trace_represents_fold)
open Minidregg.Theory.ResourceCost (Lane Charge)
open Minidregg.Kernel.DurableCommitProtocol (Snapshot Schedule CrashPoint)
open Minidregg.Kernel.DurableDataIntent
  (DataIntent DataSnapshot StableEvent StableNullifier TransactionId Outcome execute)
open Minidregg.Compiler.DurableReceiverIO (Loaded)
open Minidregg.Kernel.DurableCheckpoint (Ready)

set_option autoImplicit false

/-! ## 1. Any step, cell by cell -/

section CellCases

variable {R : Registry} {TxId Ev D' : Type} [DecidableEq TxId] [DecidableEq D']

theorem storeAt_zero {k k' : R.Kind} {pre : Store (R.layout k')}
    (h : (⟨k, 0⟩ : Cell R).storeAt k' = some pre) : pre = 0 := by
  unfold Cell.storeAt at h
  split at h
  · rename_i e
    subst e
    exact (Option.some.inj h).symm
  · cases h

/-- **What one accepted step does to one cell**: nothing; retires it; runs a
valid leg from the store it held (or from the empty store of a cell the turn
created); or creates it empty. -/
theorem step_cell_cases (H : History R TxId Ev D') {w w' : World R TxId D'}
    {t : Turn R TxId Ev D'} (h : World.step H w t = some w') (c : CellId) :
    w'.cells c = w.cells c ∨ w'.cells c = none ∨
      (∃ leg ∈ t.legs, leg.cell = c ∧ ∃ pre,
        ((w.cells c).bind (·.storeAt leg.kind) = some pre ∨ (w.cells c = none ∧ pre = 0)) ∧
        Patch.ValidFrom pre leg.patch ∧ w'.cells c = some ⟨leg.kind, Patch.run pre leg.patch⟩) ∨
      (∃ k, w.cells c = none ∧ w'.cells c = some ⟨k, 0⟩) := by
  obtain ⟨shaped, height, logRoot, -, -, -, hc, -⟩ := admit_ok H ((step_eq_some H).1 h)
  obtain ⟨c1, c2, h1, h2, h3⟩ := applyCells_ok hc
  by_cases hr : c ∈ t.retires
  · exact .inr (.inl (applyRetires_mem h3 shaped.2.2.2 c hr).2)
  have e3 : w'.cells c = c2 c := applyRetires_frame h3 c hr
  by_cases hcr : c ∈ t.creates.map Prod.fst
  · obtain ⟨⟨xc, k0, room⟩, mx, ex⟩ := List.mem_map.mp hcr
    simp only at ex
    subst ex
    obtain ⟨hnone, hc1⟩ := applyCreates_mem h1 shaped.2.2.1 xc k0 room mx
    by_cases hl : xc ∈ t.legs.map Leg.cell
    · obtain ⟨leg, ml, el⟩ := List.mem_map.mp hl
      obtain ⟨pre, hb, hvp, hpost⟩ := applyLegs_mem h2 shaped.2.1 leg ml
      rw [el, hc1] at hb
      simp only [Option.bind_some] at hb
      refine .inr (.inr (.inl ⟨leg, ml, el, pre, .inr ⟨hnone, storeAt_zero hb⟩, hvp, ?_⟩))
      rw [e3, ← el]
      exact hpost
    · exact .inr (.inr (.inr ⟨k0, hnone, by rw [e3, applyLegs_frame h2 xc hl, hc1]⟩))
  · have e1 : c1 c = w.cells c := applyCreates_frame h1 c hcr
    by_cases hl : c ∈ t.legs.map Leg.cell
    · obtain ⟨leg, ml, el⟩ := List.mem_map.mp hl
      obtain ⟨pre, hb, hvp, hpost⟩ := applyLegs_mem h2 shaped.2.1 leg ml
      rw [el, e1] at hb
      refine .inr (.inr (.inl ⟨leg, ml, el, pre, .inl hb, hvp, ?_⟩))
      rw [e3, ← el]
      exact hpost
    · exact .inl (by rw [e3, applyLegs_frame h2 c hl, e1])

/-- **The refuting pole: an append-only rewrite has no turn.**  If a cell
holds `x` at an append-only address, no accepted turn leaves it holding, at the
same kind, a store that disagrees there.  The derived `ofIntent` refuses such
an intent with `Refusal.notAPatch`; this says no other turn could do better. -/
theorem appendOnly_rewrite_has_no_turn (H : History R TxId Ev D') {w w' : World R TxId D'}
    {t : Turn R TxId Ev D'} (h : World.step H w t = some w') {c : CellId}
    {k : R.Kind} {s : Store (R.layout k)} (held : w.cells c = some ⟨k, s⟩)
    (a : Address (R.layout k)) {x : (R.layout k).Value a.1} (row : s a = some x)
    (ao : (R.layout k).discipline a.1 = .appendOnly)
    (s' : Store (R.layout k)) (rewrite : s' a ≠ some x) :
    w'.cells c ≠ some ⟨k, s'⟩ := by
  intro e
  rcases step_cell_cases H h c with h1 | h1 | ⟨leg, -, el, pre, hpre, hv, hpost⟩ | ⟨k0, hn, -⟩
  · rw [h1, held] at e
    have := (Cell.mk.inj (Option.some.inj e)).2
    exact rewrite (eq_of_heq this ▸ row)
  · rw [h1] at e; cases e
  · subst el
    rcases hpre with hb | ⟨hn, -⟩
    · rw [held] at hb
      simp only [Option.bind_some] at hb
      obtain ⟨ek, hs⟩ := Cell.mk.inj (Cell.eq_of_storeAt hb)
      subst ek
      have := eq_of_heq hs
      subst this
      rw [hpost] at e
      have e2 := eq_of_heq (Cell.mk.inj (Option.some.inj e)).2
      have kept := Patch.appendOnly_present_preserved _ leg.patch a x hv ao row
      rw [e2] at kept
      exact rewrite kept
    · rw [held] at hn; cases hn
  · rw [held] at hn; cases hn

/-- **The refuting pole for births: a ROM image has no turn.**  A cell absent
before a turn never ends holding a store with a present ROM address: a
created cell starts empty and no valid patch writes ROM.  The world model has
no create-with-image. -/
theorem rom_image_has_no_turn (H : History R TxId Ev D') {w w' : World R TxId D'}
    {t : Turn R TxId Ev D'} (h : World.step H w t = some w') {c : CellId}
    (absent : w.cells c = none) {k : R.Kind} (s' : Store (R.layout k))
    (a : Address (R.layout k)) (rom : (R.layout k).discipline a.1 = .rom)
    (present : s' a ≠ none) : w'.cells c ≠ some ⟨k, s'⟩ := by
  intro e
  rcases step_cell_cases H h c with h1 | h1 | ⟨leg, -, el, pre, hpre, hv, hpost⟩ | ⟨k0, -, hk⟩
  · rw [h1, absent] at e; cases e
  · rw [h1] at e; cases e
  · subst el
    rcases hpre with hb | ⟨-, rfl⟩
    · rw [absent] at hb; cases hb
    · rw [hpost] at e
      obtain ⟨ek, hs⟩ := Cell.mk.inj (Option.some.inj e)
      subst ek
      have := eq_of_heq hs
      have kept := Patch.rom_preserved 0 leg.patch a hv rom
      rw [this] at kept
      exact present kept
  · rw [hk] at e
    obtain ⟨ek, hs⟩ := Cell.mk.inj (Option.some.inj e)
    subst ek
    have := eq_of_heq hs
    exact present (by rw [← this]; rfl)

end CellCases

/-! ## 2. The deployed instance of the ROM pole: policy source births -/

/-- The deployed registry as a world registry. -/
def deployedR : Registry where
  Kind := Minidregg.Compiler.CanonicalCellRegistry.Kind
  layout := Minidregg.Compiler.CanonicalCellRegistry.layout

/-- **Install's policy-source cell has no turn.**  Every accepted install, and
every birth whose descriptor carries initial policies, writes a fresh
`policySource` cell holding its record (`PolicyInstallReceiver.successorCreate`,
`ResourceBirthController.PreparedBirth.initial_source_write`).  That layout is
ROM (`PolicySourceCell.layout`), so no turn of the world model creates it. -/
theorem policy_source_birth_has_no_turn {TxId Ev D' : Type} [DecidableEq TxId] [DecidableEq D']
    (H : History deployedR TxId Ev D') {w w' : World deployedR TxId D'}
    {t : Turn deployedR TxId Ev D'} (h : World.step H w t = some w') {c : CellId}
    (absent : w.cells c = none) (record : Minidregg.Compiler.CanonicalPolicyAdmission.PolicyRecord) :
    w'.cells c ≠ some ⟨Minidregg.Compiler.CanonicalCellRegistry.Kind.policySource,
      Minidregg.Compiler.PolicySourceCell.stateOfOption (some record)⟩ :=
  rom_image_has_no_turn H h absent _ Minidregg.Compiler.PolicySourceCell.recordAddress rfl
    (by
      show (Store.set 0 Minidregg.Compiler.PolicySourceCell.recordAddress (some record))
        Minidregg.Compiler.PolicySourceCell.recordAddress ≠ none
      rw [Store.set_eq]
      exact Option.some_ne_none _)

/-! ## 3. Representation -/

section Represent

variable {R : Registry} {D : Type} [DecidableEq D]
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
  /-- Every meter lane but storage is the deployed allowance. -/
  meter : ∀ l, l ≠ .storageBytes → w.meter l = snap.model.available l
  /-- Storage: the model charges the patch, the present Host the image (G-CHARGE). -/
  storage : snap.model.available .storageBytes ≤ w.meter .storageBytes
  /-- No cell is retired: the present Host never retires (G-RETIRE). -/
  retired : ∀ c, w.retired c = none
  /-- No parent rows: the present Host keeps parentage in the authority
  cell's plane 13, inside a cell's bytes (G-PARENT, T7). -/
  parent : ∀ c, w.parent c = none

/-- **`Represents : Loaded → World → Prop`.** -/
def Represents (B : Bridge R D) (p : Loaded rootBytes) (w : World R TransactionId D) : Prop :=
  SnapRepresents B p.snapshot p.height w

/-- The derived turn against a loaded image's decoded cells. -/
def Turn.ofLoaded (B : Bridge R D) (H : History R TransactionId StableEvent D)
    (p : Loaded rootBytes) (intent : DataIntent rootBytes) : Except Refusal (DTurn R D) :=
  ofCells B H (cellsOf B p.snapshot) intent

theorem cellsOf_eq {B : Bridge R D} {snap : DataSnapshot rootBytes} {height : Nat}
    {w : World R TransactionId D} (rep : SnapRepresents B snap height w) (c : CellId) :
    w.cells c = cellsOf B snap c := by
  simp [cellsOf, rep.cells c]

/-- Under representation, the loaded derivation is the world's. -/
theorem ofLoaded_eq (B : Bridge R D) (H : History R TransactionId StableEvent D)
    {p : Loaded rootBytes} {w : World R TransactionId D} (rep : Represents B p w)
    (intent : DataIntent rootBytes) :
    Turn.ofLoaded B H p intent = Turn.ofIntent B H w intent := by
  unfold Turn.ofLoaded Turn.ofIntent
  congr 1
  funext c
  exact (cellsOf_eq rep c).symm

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
    {cells : CellId → Option (Cell R)} {intent : DataIntent rootBytes} {t : DTurn R D}
    (d : Derived B H cells intent t) {w0 : DurableDataIntent.DataWrite} (hw : w0 ∈ intent.writes) :
    ∃ v, B.codec.decode w0.canonicalPostBytes = some v := by
  obtain ⟨δ, hδ, -, -⟩ := delta_of_write d hw
  have spec := deltaOf_spec hδ
  cases δ with
  | absent => exact ⟨_, spec.2⟩
  | create => exact ⟨_, spec.2⟩
  | change => exact ⟨_, spec.2⟩

/-- **`ofIntent_run`.**  `World.step H w (ofIntent w i)` is the deployed
post-state: from a represented snapshot, an intent the executor would install
(fresh id, passing preflight) and its derived turn, `World.step` accepts the
turn and its world represents `DataSnapshot.install` one height up. -/
theorem ofIntent_run (B : Bridge R D) (H : History R TransactionId StableEvent D)
    {snap : DataSnapshot rootBytes} {height : Nat} {w : World R TransactionId D}
    (rep : SnapRepresents B snap height w) {intent : DataIntent rootBytes} {t : DTurn R D}
    (derived : Turn.ofIntent B H w intent = .ok t)
    (fresh : Snapshot.lookupRecorded intent.transactionId snap.model.journal = none)
    (ready : intent.preflight snap = .ok ()) :
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
    intro l e
    rw [rep.meter l e]
    exact funded l
  have fundedS : intent.exactCharge .storageBytes ≤ w.meter .storageBytes :=
    le_trans (funded _) rep.storage
  obtain ⟨w', hs, hcells, hsys⟩ := ofIntent_step B H derived hh jfresh nodup unspent fundedL fundedS
    rep.retired
  obtain ⟨htx, hret, hrows, hnull, hchg, hchgS⟩ := ofCells_fields derived
  have d := ofCells_ok derived
  refine ⟨w', hs, ⟨fun c => ?_, fun dd => ?_, fun x => ?_, ⟨H.chain r (H.turnDigest t), ?_⟩, fun l e => ?_, ?_,
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
    rw [meter_system, hsys, sysPost_allowance]
    show _ = snap.model.available l - intent.exactCharge l
    rw [← hchg l e, ← rep.meter l e]
    split
    · rfl
    · rename_i z
      simp only [not_not] at z
      rw [z, Nat.sub_zero]
      rfl
  · -- storage
    rw [meter_system, hsys, sysPost_allowance]
    show snap.model.available .storageBytes - intent.exactCharge .storageBytes ≤ _
    have hm := rep.storage
    split
    · show _ ≤ w.meter .storageBytes - t.charge .storageBytes
      omega
    · show _ ≤ w.meter .storageBytes
      omega
  · -- retired
    show w'.system ⟨SysSpace.retired, c⟩ = none
    rw [hsys, sysPost_retired, hret]
    exact rep.retired c
  · -- parent
    show w'.system ⟨SysSpace.parent, c⟩ = none
    rw [hsys, run_sysPatch_core H _ _ _ _ _ _ (fun e => SysSpace.noConfusion e)
      (fun e => SysSpace.noConfusion e)]
    rw [sysCore_unroomed H hrows hret, Patch.run_append, run_createReads]
    simp only [Patch.run_cons, Patch.run_nil, Op.apply]
    rw [Store.set_ne _ _ _ _ (sys_space_ne (fun e => SysSpace.noConfusion e)),
      Store.set_ne _ _ _ _ (sys_space_ne (fun e => SysSpace.noConfusion e))]
    exact rep.parent c

/-! ### The deployed step and the refinement -/

/-- **The deployed step, indexed by the turn it is.**  The admitted intent,
its derived turn, the schedule the executor ran under (complete, or a crash
before or after the atomic install), the snapshot that results, and the
height: one more exactly when the executor installed. -/
structure HostStep (B : Bridge R D) (H : History R TransactionId StableEvent D)
    (p : Loaded rootBytes) (t : DTurn R D) (p' : Loaded rootBytes) : Type where
  intent : DataIntent rootBytes
  derived : Turn.ofLoaded B H p intent = .ok t
  schedule : Schedule
  snapshot : p'.snapshot = (execute schedule p.snapshot intent).storeAfter p.snapshot
  height : p'.height =
    if Installs (execute schedule p.snapshot intent) then p.height + 1 else p.height

/-- **`deployed_refines_step`.**  Today's executor (execute, then append) is an
`ImplementationRefinement` of `World.step` under `Represents`. -/
theorem deployed_refines_step (B : Bridge R D) (H : History R TransactionId StableEvent D) :
    ImplementationRefinement H (Loaded rootBytes) (HostStep B H) (Represents B) := by
  refine ⟨fun {pb pa wb t} rep st => ?_⟩
  rcases execute_cases st.schedule pb.snapshot st.intent with
    ⟨hi, fresh, ready, after⟩ | ⟨hi, after⟩
  · right
    have derived : Turn.ofIntent B H wb st.intent = .ok t :=
      (ofLoaded_eq B H rep st.intent).symm.trans st.derived
    obtain ⟨w', hs, hrep⟩ := ofIntent_run B H rep derived fresh ready
    refine ⟨w', hs, ?_⟩
    unfold Represents
    rw [st.snapshot, after, st.height, hi]
    simpa using hrep
  · left
    unfold Represents
    rw [st.snapshot, after, st.height, hi]
    simpa using rep

/-- **`host_trace_represents_fold`.**  Whatever refusals and crashes the
deployed Host went through, its state represents the fold, from the world it
started at, of a sublist of the turns it was given. -/
theorem host_trace_represents_fold (B : Bridge R D) (H : History R TransactionId StableEvent D)
    {p0 p : Loaded rootBytes} {g : World R TransactionId D} {log : List (DTurn R D)}
    (start : Represents B p0 g) (trace : Trace (HostStep B H) p0 log p) :
    ∃ sub W, sub.Sublist log ∧ fold H g sub = some W ∧ Represents B p W :=
  trace_represents_fold H (deployed_refines_step B H) start trace

/-! ### The real code paths are `HostStep`s -/

/-- `prepare`'s success branch: `Loaded.extend ready` (the append that
`receiveLoaded` confirms by read-back) is a `HostStep`. -/
def extendStep (B : Bridge R D) (H : History R TransactionId StableEvent D) (p : Loaded rootBytes)
    {intent : DataIntent rootBytes}
    (ready : Ready rootBytes p.image p.baseHeight p.base p.snapshot intent)
    {t : DTurn R D} (derived : Turn.ofLoaded B H p intent = .ok t) :
    HostStep B H p t (p.extend ready) where
  intent := intent
  derived := derived
  schedule := .complete
  snapshot := by rw [ready.executed]; rfl
  height := by
    rw [ready.executed]
    simp [Installs, Loaded.height, Loaded.extend, DurableReceiver.Image.append]

/-- A refusal or replay (the executor installs nothing) keeps the image. -/
def refusedStep (B : Bridge R D) (H : History R TransactionId StableEvent D) (p : Loaded rootBytes)
    {intent : DataIntent rootBytes}
    (refused : Installs (execute .complete p.snapshot intent) = false)
    {t : DTurn R D} (derived : Turn.ofLoaded B H p intent = .ok t) : HostStep B H p t p where
  intent := intent
  derived := derived
  schedule := .complete
  snapshot := by
    rcases execute_cases .complete p.snapshot intent with ⟨hi, -⟩ | ⟨-, after⟩
    · rw [hi] at refused; cases refused
    · exact after.symm
  height := by rw [refused]; rfl

/-- A failed or contended append (the CAS did not take; `receiveLoaded`
returns `contention`/`unavailable` and the caller reloads) is the
crash-before-install schedule. -/
def failedAppendStep (B : Bridge R D) (H : History R TransactionId StableEvent D)
    (p : Loaded rootBytes) {intent : DataIntent rootBytes}
    {t : DTurn R D} (derived : Turn.ofLoaded B H p intent = .ok t) : HostStep B H p t p where
  intent := intent
  derived := derived
  schedule := .crash .beforeAtomicInstall
  snapshot := by
    rcases execute_cases (.crash .beforeAtomicInstall) p.snapshot intent with
      ⟨hi, -⟩ | ⟨-, after⟩
    · exact absurd hi (by unfold execute; split <;> (try split) <;> simp [Installs])
    · exact after.symm
  height := by
    rcases execute_cases (.crash .beforeAtomicInstall) p.snapshot intent with
      ⟨hi, -⟩ | ⟨hi, -⟩
    · exact absurd hi (by unfold execute; split <;> (try split) <;> simp [Installs])
    · rw [hi]; rfl

end Represent

/-! ## 4. All 33 constructors: the admitted object is the intent -/

section Admission

variable {R : Registry} {D : Type} [DecidableEq D]

/-- **`Turn.ofIntent` on the admitted object.**  `NativeAdmission config opened`
is indexed by the `DataIntent` it admits: each of its 33 constructors carries
the private receiving object (`AcceptedBirth`, `AcceptedInvocation`, …) whose
intent is that index.  So the turn of an admission is the turn of its index,
and one derivation covers all 33 -- there is no per-constructor `ofIntent`. -/
def Turn.ofAdmission (B : Bridge R D) (H : History R TransactionId StableEvent D)
    (w : World R TransactionId D) {config : NativeHost.Config} {opened : NativeHost.Opened config}
    {intent : DataIntent Minidregg.Compiler.ResourceBirthCodec.rootBytes}
    (_admitted : NativeHostReplay.NativeAdmission config opened intent) :
    Except Refusal (DTurn R D) :=
  Turn.ofIntent B H w intent

/-- The admission form of `ofIntent_run`: an admitted intent the executor
installs, from a represented snapshot, steps the world to a representation of
the installed snapshot. -/
theorem ofAdmission_run (B : Bridge R D) (H : History R TransactionId StableEvent D)
    {config : NativeHost.Config} {opened : NativeHost.Opened config}
    {intent : DataIntent Minidregg.Compiler.ResourceBirthCodec.rootBytes}
    (admitted : NativeHostReplay.NativeAdmission config opened intent)
    {snap : DataSnapshot Minidregg.Compiler.ResourceBirthCodec.rootBytes} {height : Nat}
    {w : World R TransactionId D} (rep : SnapRepresents B snap height w) {t : DTurn R D}
    (derived : Turn.ofAdmission B H w admitted = .ok t)
    (installs : Installs (execute .complete snap intent) = true) :
    ∃ w', World.step H w t = some w' ∧
      SnapRepresents B (DataSnapshot.install snap intent) (height + 1) w' := by
  rcases execute_cases .complete snap intent with ⟨-, fresh, ready, -⟩ | ⟨hi, -⟩
  · exact ofIntent_run B H rep derived fresh ready
  · rw [installs] at hi; cases hi

end Admission

/-! ## 5. Poles on a toy registry, in the real pipeline -/

namespace Example

inductive Space
  | log
  | heap
  deriving DecidableEq, Repr

/-- One append-only and one RAM address. -/
def toyLayout : Layout.{0, 0, 0} where
  Namespace := Space
  Key := fun _ => Unit
  Value := fun _ => Nat
  discipline := fun
    | .log => .appendOnly
    | .heap => .ram

def toyR : Registry where
  Kind := Unit
  layout := fun _ => toyLayout

def logA : Address toyLayout := ⟨.log, ()⟩
def heapA : Address toyLayout := ⟨.heap, ()⟩

theorem toy_addrs_nodup : ([logA, heapA] : List (Address toyLayout)).Nodup := by decide

def toyStore (l h : Nat) : Store toyLayout :=
  ((0 : Store toyLayout).set logA (some l)).set heapA (some h)

def toyCell (l h : Nat) : Cell toyR := ⟨(), toyStore l h⟩

/-- Bytes `[]` are the absent slot, `[l, h]` a cell, anything else undecodable. -/
def toyDecode : List UInt8 → Option (Option (Cell toyR))
  | [] => some none
  | [l, h] => some (some (toyCell l.toNat h.toNat))
  | _ => none

def toyCodec : Codec toyR where
  decode := toyDecode
  support _ s := ([logA, heapA] : List (Address toyLayout)).filter fun a => decide (s a ≠ none)
  mem_support _ s a := by
    constructor
    · intro m
      exact of_decide_eq_true (List.mem_filter.mp m).2
    · intro h
      refine List.mem_filter.mpr ⟨?_, decide_eq_true h⟩
      rcases a with ⟨_ | _, ⟨⟩⟩
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ List.mem_cons_self
  support_nodup _ _ := List.Nodup.filter _ toy_addrs_nodup

def toyB : Bridge toyR Nat := ⟨toyCodec, nullifierCode, nullifierCode_injective⟩

def toyH : History toyR TransactionId StableEvent Nat where
  turnDigest := fun _ => 0
  chain := fun _ _ => 0
  logRoot0 := 0
  legBytes := fun _ => 0

/-- Cell 0 holds `log = 1, heap = 5`. -/
def w0 : World toyR TransactionId Nat :=
  ⟨(0 : Cells toyR).update 0 (some (toyCell 1 5)), genesisSystem toyH⟩

def toyRoot (_ : List UInt8) : Theory.TypedAuthorization.Digest := ⟨0⟩

/-- The deployed-shaped intent writing cell 0's whole image. -/
def writeIntent (l h : UInt8) : DataIntent toyRoot where
  transactionId := ⟨7⟩
  writes := [⟨⟨0⟩, ⟨0⟩, ⟨0⟩, [l, h]⟩]
  readGuards := []
  nullifiers := []
  exactCharge := 0
  event := ⟨0, ⟨0⟩, ⟨0⟩, []⟩
  subject := none
  postRootsBound := by intro w m; simp at m; subst m; rfl
  guardsReadOnly := by intro g m; simp at m

/-- **Refuting pole, derived.**  Rewriting the append-only `log` row `1 → 2`
is refused by `ofIntent` as `notAPatch` -- though the durable layer would
install it (it checks roots, not discipline). -/
theorem toy_rewrite_refused :
    refusalOf (Turn.ofIntent toyB toyH w0 (writeIntent 2 5)) = some (.notAPatch 0) := by
  decide +kernel

/-- **Refuting pole, for every turn.**  No turn at all takes cell 0 to the
rewritten image. -/
theorem toy_rewrite_has_no_turn (t : DTurn toyR Nat) (w' : World toyR TransactionId Nat)
    (h : World.step toyH w0 t = some w') : w'.cells 0 ≠ some (toyCell 2 5) :=
  appendOnly_rewrite_has_no_turn toyH h (k := ()) (s := toyStore 1 5) (by rfl) logA
    (x := (1 : Nat)) (by rfl) rfl (toyStore 2 5) (by decide)

/-- The value cell 0 holds at an address. -/
def valAt (w : World toyR TransactionId Nat) (a : Address toyLayout) : Option Nat :=
  (w.cells 0).bind fun cell => (cell.store : Store toyLayout) a

/-- **Satisfiable pole, derived.**  Writing `heap 5 → 6` derives a turn that
`World.step` accepts, leaving exactly the decoded post image. -/
theorem toy_write_steps :
    ((Turn.ofIntent toyB toyH w0 (writeIntent 1 6)).toOption.bind (World.step toyH w0)).map
        (fun w => (valAt w logA, valAt w heapA)) =
      some (some 1, some 6) := by
  decide +kernel

/-- The derived write leg is the one-op diff: a read guard on the unchanged
`log` row, then `write heap 5 6`. -/
theorem toy_write_leg :
    ((Turn.ofIntent toyB toyH w0 (writeIntent 1 6)).toOption.map fun t =>
        t.legs.map fun leg => leg.patch.length) = some [2] := by
  decide +kernel

/-- The deployed snapshot of a seed holding cell 0's bytes. -/
def toySnap : DataSnapshot toyRoot :=
  DurableReceiver.Seed.snapshot toyRoot ⟨[], [(⟨0⟩, [1, 5])], 0⟩

theorem genesis_sys_none (a : Address (sysLayout TransactionId Nat)) (ne : a.1 ≠ SysSpace.head) :
    genesisSystem toyH a = none := by
  unfold genesisSystem
  rw [Store.set_ne _ _ _ _ (fun e => ne (by rw [e]))]
  rfl

/-- **`Represents` is satisfiable**: the seed snapshot represents `w0`. -/
theorem toy_represents : SnapRepresents toyB toySnap 0 w0 := by
  refine ⟨fun c => ?_, fun d => ?_, fun x => ?_, ⟨0, rfl⟩, fun l _ => ?_, ?_, fun c => ?_,
    fun c => ?_⟩
  · by_cases e : c = 0
    · subst e; rfl
    · have : (⟨0⟩ : Theory.TypedAuthorization.Digest) ≠ ⟨c⟩ := fun h => e (by cases h; rfl)
      show toyDecode ((DurableReceiver.Seed.lookup [(⟨0⟩, [1, 5])] ⟨c⟩).getD []) = _
      simp only [DurableReceiver.Seed.lookup, this, if_false, Option.getD_none]
      show some none = some (((0 : Cells toyR).update 0 (some (toyCell 1 5))) c)
      rw [cells_update_ne _ _ e]
      rfl
  · show (genesisSystem toyH ⟨SysSpace.spent, d⟩).isSome = true ↔ _
    rw [genesis_sys_none _ (fun e => SysSpace.noConfusion e)]
    simp [toySnap, DurableReceiver.Seed.snapshot]
  · show (genesisSystem toyH ⟨SysSpace.journal, x⟩).isSome = _
    rw [genesis_sys_none _ (fun e => SysSpace.noConfusion e)]
    rfl
  · rw [meter_system]
    show Option.getD (α := Nat) (genesisSystem toyH ⟨SysSpace.allowance, l⟩) 0 = _
    rw [genesis_sys_none _ (fun e => SysSpace.noConfusion e)]
    rfl
  · exact Nat.zero_le _
  · exact genesis_sys_none _ (fun e => SysSpace.noConfusion e)
  · exact genesis_sys_none _ (fun e => SysSpace.noConfusion e)

/-- **The refinement is not vacuous**: on the represented seed, the deployed
executor installs the heap write, its derived turn steps, and the stepped
world represents the installed snapshot one height up. -/
theorem toy_refined :
    ∃ t w', Turn.ofIntent toyB toyH w0 (writeIntent 1 6) = .ok t ∧
      World.step toyH w0 t = some w' ∧
      SnapRepresents toyB (DataSnapshot.install toySnap (writeIntent 1 6)) 1 w' := by
  have installs : Installs (execute .complete toySnap (writeIntent 1 6)) = true := by
    decide +kernel
  rcases execute_cases .complete toySnap (writeIntent 1 6) with ⟨-, fresh, ready, -⟩ | ⟨hi, -⟩
  · cases h : Turn.ofIntent toyB toyH w0 (writeIntent 1 6) with
    | error e =>
        have ok : refusalOf (Turn.ofIntent toyB toyH w0 (writeIntent 1 6)) = none := by
          decide +kernel
        rw [h] at ok
        cases ok
    | ok t =>
        obtain ⟨w', hs, hr⟩ := ofIntent_run toyB toyH toy_represents h fresh ready
        exact ⟨t, w', rfl, hs, hr⟩
  · rw [installs] at hi; cases hi

end Example

/-! ## Axiom pins -/

#assert_axioms storeAt_zero
#assert_axioms step_cell_cases
#assert_axioms appendOnly_rewrite_has_no_turn
#assert_axioms rom_image_has_no_turn
#assert_axioms policy_source_birth_has_no_turn
#assert_axioms cellsOf_eq
#assert_axioms ofLoaded_eq
#assert_axioms execute_cases
#assert_axioms preflight_facts
#assert_axioms lookupPostBytes_some
#assert_axioms decodes_of_derived
#assert_axioms ofIntent_run
#assert_axioms deployed_refines_step
#assert_axioms host_trace_represents_fold
#assert_axioms ofAdmission_run
#assert_axioms Example.toy_rewrite_refused
#assert_axioms Example.toy_rewrite_has_no_turn
#assert_axioms Example.toy_write_steps
#assert_axioms Example.toy_write_leg
#assert_axioms Example.toy_represents
#assert_axioms Example.toy_refined


/-! `#print axioms`, pinned: the standard three. -/
/-- info: 'Minidregg.Kernel.HostRefinesWorld.ofIntent_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ofIntent_run
/-- info: 'Minidregg.Kernel.HostRefinesWorld.deployed_refines_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms deployed_refines_step
/-- info: 'Minidregg.Kernel.HostRefinesWorld.host_trace_represents_fold' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms host_trace_represents_fold
/-- info: 'Minidregg.Kernel.HostRefinesWorld.ofAdmission_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ofAdmission_run
/-- info: 'Minidregg.Kernel.HostRefinesWorld.appendOnly_rewrite_has_no_turn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms appendOnly_rewrite_has_no_turn
/-- info: 'Minidregg.Kernel.HostRefinesWorld.rom_image_has_no_turn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms rom_image_has_no_turn
/-- info: 'Minidregg.Kernel.HostRefinesWorld.policy_source_birth_has_no_turn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms policy_source_birth_has_no_turn
/-- info: 'Minidregg.Kernel.HostRefinesWorld.Example.toy_rewrite_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Example.toy_rewrite_refused
/-- info: 'Minidregg.Kernel.HostRefinesWorld.Example.toy_refined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Example.toy_refined

end Minidregg.Kernel.HostRefinesWorld
