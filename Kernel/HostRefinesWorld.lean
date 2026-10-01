/-
# Kernel.HostRefinesWorld -- the present Host is an implementation refinement of `World.step`

SURPASS §2(b), stage 0, lanes T3 and T3b.  No Host byte changes.  The deployed
transition is `DurableDataIntent.execute` (reached through
`DurableCheckpoint.prepare`) followed by the append that `Loaded.extend` makes
and the checkpoint rebase `afterCheckpoint` may make; its state is
`DurableReceiverIO.Loaded`.  This module says what it means for a `Loaded` to
represent a `World` and proves that every deployed step -- accepted, refused,
replayed, crashed before or after the atomic install, rebased on a stored
checkpoint -- represents either the old world or the world `World.step`
produces on the turn `Turn.ofIntent` derives from the admitted intent.

* `Represents B p w` (`SnapRepresents` on `p.snapshot` at `p.height`).  Over the
  deployed bridge (`DeployedRepresents`, `Kernel.DeployedBridge.bridge`) its
  cells field says every deployed cell's bytes ARE the canonical lifecycle
  encoding of the world's cell (`deployedRepresents_cells`).
* `ofIntent_run`, `deployed_refines_step` (an `ImplementationRefinement` over
  every schedule), `host_trace_represents_fold`: unchanged statements; since
  T3b they cover install and every birth with initial policies, because a
  create carries its ROM image (`World.applyCreates`) and a birth's leg is never
  `notAPatch` (`TurnOfIntent.Delta.create_patchOk`).
* `confirmed_represents`: the confirmed append path, checkpoint rebase
  included -- `afterCheckpoint (p.extend ready) stored` represents the stepped
  world (`represents_rebaseD`, under `BaseHonest`).
* ROM births: `policy_source_birth_is_turn` (the deployed source birth is an
  accepted turn holding the record), `ofIntent_policySource_birth` (the derived
  turn of an intent writing a source cell creates it with the record),
  `birth_rom_image` (a born cell's ROM is exactly its create's image), and the
  poles `policy_source_rewrite_has_no_turn` (the record in an EXISTING source
  cell is never rewritten) and `appendOnly_rewrite_has_no_turn`.
* The three rows T3 inferred are traced: `shareIssue_…`,
  `grainShareIssue_…`, `lifetimeGrantIssue_birth_has_one_initial_policy`.

## THE LIST

Empty.  `TurnCensus.every_admission_is_turn` decides it for all 33 shapes and
`TurnCensus.theList_empty`; `TurnCensus.theListWithoutRomBirth_eq` is the pole
(without ROM birth the list is exactly the six source-creating receivers).

## `Represents`, field by field, and what T4 must prove of each

* `cells` -- exact, over the real codec (`decodeCell`, one wire per kind).
  Nothing left model-side.
* `spent` -- exact (the consumed set, under the injective `digestKey`).
* `journal` -- presence of the id only (G-JOURNAL, not narrowed: the model
  journals `(height, H.turnDigest t)` of the DERIVED turn, which does not
  determine the recorded intent -- its storage lane is replaced and its writes
  are diffs against the pre-state -- so no function of the deployed record is
  the model digest).  T4/T5 must prove, once the log holds turns:
  `∀ x, w.journal x = (p.turns.findIdx? (·.txId = x)).map fun i => (i, H.turnDigest p.turns[i]!)`.
* `head` -- the height is the log length.  G-CLOCK narrowed:
  `represents_logicalHeight` (`logicalHeight config p = config.genesisHeight + h`).
  T4 must prove the window translation for every receiver that pins a height:
  `ofAdmission_window : derived = .ok t → (t.notBefore ≤ h ∧ ∀ u ∈ t.validUntil, h ≤ u) ↔
    receiverHeightCheck admitted (config.genesisHeight + h)`.
* `meter` -- exact on 9 lanes.  `storage` -- `≤` (G-CHARGE).  T5 must prove
  `intent.exactCharge .storageBytes = storageOf H t.creates t.legs` for every
  admitted intent and its derived `t` (the legs' bytes plus the born images'),
  after which the field is an equality.
* `retired` -- none (G-RETIRE: the Host never retires; `decodeCell_retired`
  refuses a retired image).
* `parent` -- none (G-PARENT, T7): T7 must prove
  `∀ c, w.parent c = (CredentialAuthorityState.parentOf (authorityStore p)) c`, then delete plane 13.
* capability / key epoch / window -- not in `DataIntent` (G-AUTH): T4 must
  prove `ofAdmission_auth : derived = .ok t → t.capability = some (capDigest admitted) ∧
    t.keyEpoch = subjectKeyEpoch admitted`.
* rebase (G-REBASE) -- closed: `represents_rebaseD`, `confirmed_represents`.
  Its premise `BaseHonest p` holds at genesis, is kept by `extend` and
  established by `rebaseD`.  T4 must prove it for the cold open:
  `load_baseHonest : DurableReceiverIO.load transport rootBytes = .ok p → BaseHonest p`
  (a stored checkpoint's consumed list is its prefix's nullifiers; today that
  rests on the checkpoint MAC, i.e. custody).

## The statement left for T4

```lean
theorem host_submit_is_step
    (H : History deployedR TransactionId StableEvent Digest)
      -- stage F: WorldRoot.cshakeHistory encode logRoot0 legBytes imageBytes
    {config : NativeHost.Config} {opened : NativeHost.Opened config}
    {intent : DataIntent ResourceBirthCodec.rootBytes}
    (admitted : NativeHostReplay.NativeAdmission config opened intent)
    {w : World deployedR TransactionId Digest}
    (represents : DeployedRepresents opened.durable w) (honest : BaseHonest opened.durable)
    {t : DTurn deployedR Digest} (derived : Turn.ofAdmission bridge H w admitted = .ok t)
    {ready : Ready ResourceBirthCodec.rootBytes opened.durable.image opened.durable.baseHeight
      opened.durable.base opened.durable.snapshot intent}
    (prepared : DurableCheckpoint.prepare opened.durable.image opened.durable.baseHeight
      opened.durable.base opened.durable.snapshot opened.durable.withinLog opened.durable.resumed
      intent = .inl ready)
    (stored : Bool) {receipt : NativeHostCodec.Receipt}
    (sealed : NativeHost.historicalReceipt config
      (DurableReceiverIO.afterCheckpoint (opened.durable.extend ready) stored)
      intent.transactionId intent.event.eventId = some receipt) :
    ∃ w', World.admit H w t = .ok w' ∧
      DeployedRepresents (DurableReceiverIO.afterCheckpoint (opened.durable.extend ready) stored) w' ∧
      receipt.acceptedCount = (w.head.map Prod.fst).getD 0 + 1 ∧
      receipt.worldRoot = WorldRoot.rootOf S w'
```

Its state half is `confirmed_represents` (proved here, for any bridge).  What
T4 adds is the receipt (`acceptedCount` from `represents.head`; `worldRoot`
needs `Loaded.worldRoot = WorldRoot.rootOf S w'`, the root-cache agreement),
and then the cutover itself: `Loaded` becomes a `World`, `Represents` becomes
equality, `prepare`+`extend` becomes `World.admit` + append.

Its two poles, which T4 must keep:

* satisfiable -- `Example.toy_refined` (the derived turn steps and the
  installed snapshot represents it) lifted through `confirmed_represents`; a
  deployed source birth (`policy_source_birth_is_turn`).
* refuting -- an admitted intent whose derived turn is refused is a deployed
  step that installs nothing:
  `Turn.ofAdmission bridge H w admitted = .error r → ∀ ready, prepare … ≠ .inl ready`
  is what the cutover must make TRUE (today the durable layer would install an
  append-only rewrite, `Example.toy_rewrite_refused` shows `ofIntent` refusing
  it); and `policy_source_rewrite_has_no_turn` (no turn rewrites a ROM record).
-/
import Kernel.TurnOfIntent
import Kernel.DeployedBridge
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
open Minidregg.Kernel.DeployedBridge (deployedR sourceCell)

set_option autoImplicit false

/-! ## 1. Any step, cell by cell -/

section CellCases

variable {R : Registry} {TxId Ev D' : Type} [DecidableEq TxId] [DecidableEq D']

/-- **What one accepted step does to one cell**: nothing; retires it; runs a
valid leg from the store it held (or from the ROM image a create of the turn
gave it); or creates it, born as the create carries it (T3b). -/
theorem step_cell_cases (H : History R TxId Ev D') {w w' : World R TxId D'}
    {t : Turn R TxId Ev D'} (h : World.step H w t = some w') (c : CellId) :
    w'.cells c = w.cells c ∨ w'.cells c = none ∨
      (∃ leg ∈ t.legs, leg.cell = c ∧ ∃ pre,
        ((w.cells c).bind (·.storeAt leg.kind) = some pre ∨
          (w.cells c = none ∧ RomOnly pre ∧
            ∃ room, (c, (⟨leg.kind, pre⟩ : Cell R), room) ∈ t.creates)) ∧
        Patch.ValidFrom pre leg.patch ∧ w'.cells c = some ⟨leg.kind, Patch.run pre leg.patch⟩) ∨
      (∃ b room, (c, b, room) ∈ t.creates ∧ w.cells c = none ∧ w'.cells c = some b) := by
  obtain ⟨shaped, height, logRoot, -, -, -, hc, -⟩ := admit_ok H ((step_eq_some H).1 h)
  obtain ⟨c1, c2, h1, h2, h3⟩ := applyCells_ok hc
  by_cases hr : c ∈ t.retires
  · exact .inr (.inl (applyRetires_mem h3 shaped.2.2.2 c hr).2)
  have e3 : w'.cells c = c2 c := applyRetires_frame h3 c hr
  by_cases hcr : c ∈ t.creates.map Prod.fst
  · obtain ⟨⟨xc, b0, room⟩, mx, ex⟩ := List.mem_map.mp hcr
    simp only at ex
    subst ex
    obtain ⟨hnone, hc1⟩ := applyCreates_mem h1 shaped.2.2.1 xc b0 room mx
    have hrom := applyCreates_romOnly h1 xc b0 room mx
    by_cases hl : xc ∈ t.legs.map Leg.cell
    · obtain ⟨leg, ml, el⟩ := List.mem_map.mp hl
      obtain ⟨pre, hb, hvp, hpost⟩ := applyLegs_mem h2 shaped.2.1 leg ml
      rw [el, hc1] at hb
      simp only [Option.bind_some] at hb
      have eb := Cell.eq_of_storeAt hb
      subst eb
      refine .inr (.inr (.inl ⟨leg, ml, el, pre, .inr ⟨hnone, hrom, room, mx⟩, hvp, ?_⟩))
      rw [e3, ← el]
      exact hpost
    · exact .inr (.inr (.inr ⟨b0, room, mx, hnone, by rw [e3, applyLegs_frame h2 xc hl, hc1]⟩))
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
  rcases step_cell_cases H h c with h1 | h1 | ⟨leg, -, el, pre, hpre, hv, hpost⟩ | ⟨b, room, -, hn, -⟩
  · rw [h1, held] at e
    have := (Cell.mk.inj (Option.some.inj e)).2
    exact rewrite (eq_of_heq this ▸ row)
  · rw [h1] at e; cases e
  · subst el
    rcases hpre with hb | ⟨hn, -, -⟩
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

/-- **A born cell's ROM is the image its create carried (T3b).**  If a cell
absent before an accepted turn is present after it, the turn has a create of
that cell whose image is exactly the post store's ROM part: ROM enters a cell
only at birth, through the create that carries it. -/
theorem birth_rom_image (H : History R TxId Ev D') {w w' : World R TxId D'}
    {t : Turn R TxId Ev D'} (h : World.step H w t = some w') {c : CellId}
    (absent : w.cells c = none) {k : R.Kind} {s' : Store (R.layout k)}
    (post : w'.cells c = some ⟨k, s'⟩) :
    ∃ room, (c, (⟨k, romPart s'⟩ : Cell R), room) ∈ t.creates := by
  rcases step_cell_cases H h c with h1 | h1 | ⟨leg, -, el, pre, hpre, hv, hpost⟩ |
      ⟨b, room, mem, -, hb⟩
  · rw [h1, absent] at post; cases post
  · rw [h1] at post; cases post
  · subst el
    rcases hpre with hb | ⟨-, rom, room, mem⟩
    · rw [absent] at hb; cases hb
    · rw [hpost] at post
      obtain ⟨ek, hs⟩ := Cell.mk.inj (Option.some.inj post)
      subst ek
      have hs' := eq_of_heq hs
      subst hs'
      refine ⟨room, ?_⟩
      have e : romPart (Patch.run pre leg.patch) = pre := by
        apply DFinsupp.ext
        intro a
        rw [romPart_apply]
        split
        · rename_i hr
          exact Patch.rom_preserved pre leg.patch a hv hr
        · rename_i hr
          cases hp : pre a with
          | none => rfl
          | some v => exact absurd (rom a (by rw [hp]; exact Option.some_ne_none v)) hr
      rw [e]
      exact mem
  · rw [hb] at post
    have e := Option.some.inj post
    subst e
    refine ⟨room, ?_⟩
    rw [romPart_of_romOnly (step_create_romOnly H h c _ room mem)]
    exact mem

/-- **No birth, no cell**: an absent cell that no create of the turn names is
still absent after it.  (T3's `rom_image_has_no_turn` is this with the create
premise made explicit: since T3b a create may carry a ROM image.) -/
theorem birth_needs_create (H : History R TxId Ev D') {w w' : World R TxId D'}
    {t : Turn R TxId Ev D'} (h : World.step H w t = some w') {c : CellId}
    (absent : w.cells c = none) (noCreate : ∀ b room, (c, b, room) ∉ t.creates) :
    w'.cells c = none := by
  cases hpost : w'.cells c with
  | none => rfl
  | some cell =>
      obtain ⟨room, mem⟩ := birth_rom_image H h absent (k := cell.kind) (s' := cell.store) hpost
      exact absurd mem (noCreate _ room)

end CellCases

/-! ## 2. Policy-source births are turns (T3b) -/

/-- The birth turn of a policy-source cell: one create carrying the record's
ROM image, charged the image's bytes, and nothing else. -/
def sourceBirth {D' : Type} (H : History deployedR TransactionId StableEvent D')
    (x : TransactionId) (c : CellId)
    (record : Minidregg.Compiler.CanonicalPolicyAdmission.PolicyRecord) (ev : StableEvent) :
    DTurn deployedR D' :=
  { txId := x, creates := [(c, sourceCell record, none)], legs := [], retires := [], event := ev,
    charge := fun l => if l = .storageBytes then H.imageBytes (sourceCell record) else 0 }

/-- **`policy_source_birth_is_turn`.**  Every accepted install, and every
birth whose descriptor carries initial policies, writes a fresh `policySource`
cell holding its record (`PolicyInstallReceiver.successorCreate`,
`ResourceBirthController.PreparedBirth.initial_source_write`).  That layout is
ROM; since T3b a create carries its ROM image, so at any world with a head, a
fresh transaction id, an absent unretired cell and the image's bytes funded,
the birth is an accepted turn and the cell holds exactly the record. -/
theorem policy_source_birth_is_turn {D' : Type} [DecidableEq D']
    (H : History deployedR TransactionId StableEvent D') {w : World deployedR TransactionId D'}
    {height : Nat} {logRoot : D'} (hh : w.head = some (height, logRoot))
    {x : TransactionId} (fresh : w.journal x = none) {c : CellId} (absent : w.cells c = none)
    (unretired : w.retired c = none)
    (record : Minidregg.Compiler.CanonicalPolicyAdmission.PolicyRecord) (ev : StableEvent)
    (funded : H.imageBytes (sourceCell record) ≤ w.meter .storageBytes) :
    ∃ w', World.step H w (sourceBirth H x c record ev) = some w' ∧
      w'.cells c = some (sourceCell record) := by
  have shaped : Shaped (sourceBirth H x c record ev) := by
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [sourceBirth]
  have funded' : (sourceBirth H x c record ev).charge ≤ w.meter := by
    intro l
    by_cases e : l = .storageBytes
    · subst e
      simpa [sourceBirth] using funded
    · simp [sourceBirth, e]
  have hk : turnCheck H w (sourceBirth H x c record ev) height = none := by
    rw [turnCheck_eq_none_iff]
    refine ⟨by simp [sourceBirth], ⟨by simp [sourceBirth], by simp [sourceBirth]⟩,
      by simp [sourceBirth], by simp [sourceBirth, patchBytes], funded'⟩
  have hv : Patch.ValidFrom w.system
      (sysPatch H (sourceBirth H x c record ev) height logRoot w.meter) := by
    refine sysPatch_valid_unroomed H (by simp [sourceBirth]) rfl
      (by
        intro y hy
        simp only [sourceBirth, List.mem_singleton] at hy
        subst hy
        exact unretired)
      fresh hh ⟨by simp [sourceBirth], by simp [sourceBirth]⟩ ?_
    intro l hl
    have pos : 0 < w.meter l := lt_of_lt_of_le (Nat.pos_of_ne_zero hl) (funded' l)
    rw [meter_system] at pos ⊢
    revert pos
    cases w.system ⟨SysSpace.allowance, l⟩ with
    | none => intro pos; exact absurd pos (lt_irrefl 0)
    | some a => intro _; rfl
  have hcells : applyCells w.cells (sourceBirth H x c record ev) =
      .ok (w.cells.update c (some (sourceCell record))) := by
    have rom : RomOnly (sourceCell record).store :=
      Minidregg.Kernel.DeployedBridge.policySource_romOnly _
    simp [applyCells, applyCreates, sourceBirth, absent, roomPresent, rom, applyLegs,
      applyRetires]
  refine ⟨_, (step_eq_some H).2 (admit_of H shaped hh fresh hk hv hcells), ?_⟩
  exact cells_update_self _ _ _

/-- **The pole: the same record written into an EXISTING source cell has no
turn.**  A policy-source cell holding `r` is, after any accepted turn, retired
or still holding `r`: the record is ROM (`World.step_rom_preserved`). -/
theorem policy_source_rewrite_has_no_turn {TxId Ev D' : Type} [DecidableEq TxId] [DecidableEq D']
    (H : History deployedR TxId Ev D') {w w' : World deployedR TxId D'}
    {t : Turn deployedR TxId Ev D'} (h : World.step H w t = some w') {c : CellId}
    {r : Minidregg.Compiler.CanonicalPolicyAdmission.PolicyRecord}
    (held : w.cells c = some (sourceCell r))
    (r' : Minidregg.Compiler.CanonicalPolicyAdmission.PolicyRecord) (other : r' ≠ r) :
    w'.cells c ≠ some (sourceCell r') := by
  intro e
  rcases step_rom_preserved H h held with ⟨gone, -⟩ | ⟨s', post, same⟩
  · rw [gone] at e; cases e
  · rw [post] at e
    have hs := eq_of_heq (Cell.mk.inj (Option.some.inj e)).2
    have kept : Minidregg.Compiler.PolicySourceCell.recordAt
          (Minidregg.Compiler.PolicySourceCell.stateOfOption (some r')) =
        Minidregg.Compiler.PolicySourceCell.recordAt
          (Minidregg.Compiler.PolicySourceCell.stateOfOption (some r)) := by
      have k := same Minidregg.Compiler.PolicySourceCell.recordAddress rfl
      rw [hs] at k
      exact k
    simp only [Minidregg.Compiler.PolicySourceCell.recordAt_stateOfOption] at kept
    exact other (Option.some.inj kept)

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

/-! ### `Represents` survives the checkpoint rebase (G-REBASE, T3b)

A confirmed append ends in `afterCheckpoint (p.extend ready) stored`, which
re-materializes the head as a fresh checkpoint base (`Loaded.rebaseD`) when a
checkpoint was stored.  The rebased snapshot is `State.snapshot` of
`State.ofSnapshot`: every enumerable identifier with its current bytes, the
whole log's journal, the whole log's nullifiers, the remaining allowance.  It
agrees with the replayed snapshot on everything `Represents` reads -- given
that the base the loaded state was resumed from consumed exactly its prefix's
nullifiers (`BaseHonest`).  That premise holds at the genesis base, is kept by
`extend` and established by `rebaseD`; a cold open from a stored checkpoint
supplies it by custody (the checkpoint MAC), which is T4's to state. -/

/-- What a replay does to the journal and the consumed set. -/
theorem replay_model :
    ∀ (records : List DurableReceiver.IntentRecord) (before after : DataSnapshot rootBytes),
      DurableReceiver.replay rootBytes before records = some after →
        after.model.journal =
            (records.map fun r => (r.transactionId, DurableCheckpoint.IntentRecord.erase r)).reverse ++
              before.model.journal ∧
          ∀ n, after.model.consumed n =
            (decide (n ∈ records.flatMap DurableReceiver.IntentRecord.nullifiers) ||
              before.model.consumed n)
  | [], before, after, h => by
      simp only [DurableReceiver.replay, Option.some.injEq] at h
      subst h
      exact ⟨by simp, fun n => by simp⟩
  | r :: rs, before, after, h => by
      unfold DurableReceiver.replay at h
      cases hb : r.bind? rootBytes with
      | none => rw [hb] at h; cases h
      | some intent =>
          rw [hb] at h
          change (match DurableDataIntent.execute .complete before intent with
            | .accepted next => DurableReceiver.replay rootBytes next rs
            | _ => none) = some after at h
          split at h
          · rename_i next he
            have hn : next = DataSnapshot.install before intent := by
              rcases execute_cases .complete before intent with ⟨-, -, -, a⟩ | ⟨i, -⟩
              · rw [he] at a; exact a
              · rw [he] at i; cases i
            obtain ⟨hj, hc⟩ := replay_model rs next after h
            have he' := DurableCheckpoint.IntentRecord.erase_bind hb
            subst hn
            refine ⟨?_, fun n => ?_⟩
            · rw [hj]
              show _ ++ ((intent.erase.transactionId, intent.erase) :: before.model.journal) = _
              rw [he']
              simp [DurableCheckpoint.IntentRecord.erase]
            · rw [hc n]
              show (decide _ || (if n ∈ intent.erase.nullifiers then true else
                before.model.consumed n)) = _
              rw [he']
              by_cases hm : n ∈ r.nullifiers <;>
                simp [hm, DurableCheckpoint.IntentRecord.erase, List.flatMap_cons]
          · cases h

/-- What a resume is: the whole log's journal, and the base's consumed set plus
the replayed suffix's nullifiers. -/
theorem resume_model {image : DurableReceiver.Image} {bh : Nat} {st : DurableCheckpoint.State}
    {snap : DataSnapshot rootBytes} (h : DurableCheckpoint.resume rootBytes image bh st = some snap) :
    snap.model.journal =
        (image.accepted.map fun r => (r.transactionId, DurableCheckpoint.IntentRecord.erase r)).reverse ∧
      ∀ n, snap.model.consumed n =
        (decide (n ∈ (image.accepted.drop bh).flatMap DurableReceiver.IntentRecord.nullifiers) ||
          decide (n ∈ st.consumed)) := by
  unfold DurableCheckpoint.resume at h
  split at h
  · obtain ⟨hj, hc⟩ := replay_model _ _ _ h
    refine ⟨?_, fun n => hc n⟩
    rw [hj]
    show _ ++ ((image.accepted.take bh).map fun r =>
      (r.transactionId, DurableCheckpoint.IntentRecord.erase r)).reverse = _
    rw [← List.reverse_append, ← List.map_append, List.take_append_drop]
  · cases h

/-- The base a loaded state was resumed from consumed exactly its prefix's
nullifiers. -/
def BaseHonest (p : Loaded rootBytes) : Prop :=
  ∀ n, n ∈ p.base.consumed ↔
    n ∈ (p.image.accepted.take p.baseHeight).flatMap DurableReceiver.IntentRecord.nullifiers

/-- An honest loaded state has consumed exactly its log's nullifiers. -/
theorem consumed_of_honest {p : Loaded rootBytes} (honest : BaseHonest p) (n : StableNullifier) :
    p.snapshot.model.consumed n =
      decide (n ∈ p.image.accepted.flatMap DurableReceiver.IntentRecord.nullifiers) := by
  rw [(resume_model p.resumed).2 n]
  conv => rhs; rw [← List.take_append_drop p.baseHeight p.image.accepted]
  rw [List.flatMap_append]
  by_cases h1 : n ∈ (p.image.accepted.drop p.baseHeight).flatMap
      DurableReceiver.IntentRecord.nullifiers
  · simp only [h1, decide_true, Bool.true_or, List.mem_append, or_true]
  · simp only [h1, decide_false, Bool.false_or, List.mem_append, or_false]
    exact decide_eq_decide.mpr (honest n)

theorem lookup_map_self (l : List DurableDataIntent.CellId) (f : DurableDataIntent.CellId → List UInt8)
    (c : DurableDataIntent.CellId) :
    DurableReceiver.Seed.lookup (l.map fun x => (x, f x)) c = if c ∈ l then some (f c) else none := by
  induction l with
  | nil => rfl
  | cons x rest ih =>
      simp only [List.map_cons, DurableReceiver.Seed.lookup, List.mem_cons]
      by_cases e : x = c
      · subst e; simp
      · rw [if_neg e, ih]
        by_cases m : c ∈ rest
        · simp [m]
        · simp [m, Ne.symm e]

/-- **The rebased snapshot agrees with the loaded one** on bytes, journal,
consumed set and allowance, at the same height. -/
theorem rebase_agrees {p p' : Loaded rootBytes} (honest : BaseHonest p) (h : p.rebase = some p') :
    (∀ c, p'.snapshot.canonicalBytes c = p.snapshot.canonicalBytes c) ∧
      p'.snapshot.model.journal = p.snapshot.model.journal ∧
      (∀ n, p'.snapshot.model.consumed n = p.snapshot.model.consumed n) ∧
      p'.snapshot.model.available = p.snapshot.model.available ∧ p'.height = p.height ∧
      BaseHonest p' := by
  have fields : p'.image = p.image ∧ p'.baseHeight = p.image.accepted.length ∧
      p'.base = DurableCheckpoint.State.ofSnapshot p.image p.snapshot := by
    unfold Loaded.rebase at h
    dsimp only at h
    split at h
    · cases h
    · split at h
      · cases h
      · cases h
        exact ⟨rfl, rfl, rfl⟩
  obtain ⟨himg, hbh, hbase⟩ := fields
  have resumed := p'.resumed
  rw [himg, hbh, hbase] at resumed
  unfold DurableCheckpoint.resume at resumed
  rw [if_pos (DurableCheckpoint.ofSnapshot_admissible _ _), List.drop_length,
    List.take_length] at resumed
  simp only [DurableReceiver.replay, Option.some.injEq] at resumed
  have hp' : p'.height = p.height := by
    show p'.image.accepted.length = p.image.accepted.length
    rw [himg]
  refine ⟨fun c => ?_, ?_, fun n => ?_, ?_, hp', ?_⟩
  · rw [← resumed]
    show (DurableReceiver.Seed.lookup (p.image.cellIds.map fun c => (c, p.snapshot.canonicalBytes c))
      c).getD p.image.seed.absentBytes = _
    rw [lookup_map_self]
    by_cases m : c ∈ p.image.cellIds
    · simp [m]
    · simp only [m, if_false, Option.getD_none]
      exact (DurableCheckpoint.resume_outside_support rootBytes _ _ _ _ p.resumed c m).symm
  · rw [← resumed, (resume_model p.resumed).1]
    rfl
  · rw [← resumed, consumed_of_honest honest]
    rfl
  · rw [← resumed]
    rfl
  · intro n
    rw [himg, hbh, hbase, List.take_length]
    rfl

/-- **`represents_rebaseD`.**  An honest loaded state that represents a world
still represents it after the checkpoint rebase. -/
theorem represents_rebaseD (B : Bridge R D) {p : Loaded rootBytes} {w : World R TransactionId D}
    (honest : BaseHonest p) (rep : Represents B p w) : Represents B p.rebaseD w := by
  unfold Loaded.rebaseD
  cases hr : p.rebase with
  | none => exact rep
  | some p' =>
      obtain ⟨hbytes, hj, hc, ha, hh, -⟩ := rebase_agrees honest hr
      show SnapRepresents B p'.snapshot p'.height w
      refine ⟨fun c => ?_, fun d => ?_, fun x => ?_, ?_, fun l e => ?_, ?_, rep.retired, rep.parent⟩
      · rw [hbytes]; exact rep.cells c
      · simp only [hc]; exact rep.spent d
      · rw [hj]; exact rep.journal x
      · rw [hh]; exact rep.head
      · rw [ha]; exact rep.meter l e
      · rw [ha]; exact rep.storage

/-- Honesty survives the rebase. -/
theorem baseHonest_rebaseD {p : Loaded rootBytes} (honest : BaseHonest p) :
    BaseHonest p.rebaseD := by
  unfold Loaded.rebaseD
  cases hr : p.rebase with
  | none => exact honest
  | some p' => exact (rebase_agrees honest hr).2.2.2.2.2

/-- Honesty survives an append: the base and its height are unchanged, and the
prefix they name is unchanged. -/
theorem baseHonest_extend {p : Loaded rootBytes} (honest : BaseHonest p) {intent : DataIntent rootBytes}
    (ready : Ready rootBytes p.image p.baseHeight p.base p.snapshot intent) :
    BaseHonest (p.extend ready) := by
  intro n
  show n ∈ p.base.consumed ↔ n ∈ ((p.image.accepted ++ [DurableReceiver.IntentRecord.ofIntent intent]).take
    p.baseHeight).flatMap DurableReceiver.IntentRecord.nullifiers
  rw [List.take_append_of_le_length p.withinLog]
  exact honest n

/-- **The pole: a rebase that drops a cell breaks representation.**  The
materialized checkpoint must carry every enumerable identifier; a state whose
cell list omits a present cell re-materializes it as the absent slot. -/
theorem rebase_dropping_cell_breaks (B : Bridge R D) {height : Nat}
    {w : World R TransactionId D} (st : DurableCheckpoint.State) (prefixRecords : List DurableReceiver.IntentRecord)
    {c : CellId} (dropped : (⟨c⟩ : DurableDataIntent.CellId) ∉ st.cells.map Prod.fst)
    (absentReads : B.codec.decode st.absentBytes = some none) (present : w.cells c ≠ none) :
    ¬ SnapRepresents B (DurableCheckpoint.State.snapshot rootBytes st prefixRecords) height w := by
  intro rep
  have e := rep.cells c
  have bytes : (DurableCheckpoint.State.snapshot rootBytes st prefixRecords).canonicalBytes ⟨c⟩ =
      st.absentBytes := by
    show (DurableReceiver.Seed.lookup st.cells ⟨c⟩).getD st.absentBytes = _
    rw [DurableReceiver.Seed.lookup_missing _ _ dropped]
    rfl
  rw [bytes, absentReads] at e
  exact present (Option.some.inj e).symm

/-- **The confirmed append path, rebase included.**  From an honest loaded
state representing `w`, the deployed successor `afterCheckpoint (p.extend
ready) stored` -- what `receiveLoadedDetailedWithFresh` returns on a confirmed
read-back -- represents the world `World.step` produces on the derived turn,
and stays honest. -/
theorem confirmed_represents (B : Bridge R D) (H : History R TransactionId StableEvent D)
    {p : Loaded rootBytes} {w : World R TransactionId D} (rep : Represents B p w)
    (honest : BaseHonest p) {intent : DataIntent rootBytes}
    (ready : Ready rootBytes p.image p.baseHeight p.base p.snapshot intent)
    {t : DTurn R D} (derived : Turn.ofLoaded B H p intent = .ok t) (stored : Bool) :
    ∃ w', World.step H w t = some w' ∧
      Represents B (Minidregg.Compiler.DurableReceiverIO.afterCheckpoint (p.extend ready) stored) w' ∧
      BaseHonest (Minidregg.Compiler.DurableReceiverIO.afterCheckpoint (p.extend ready) stored) := by
  have derived' : Turn.ofIntent B H w intent = .ok t := (ofLoaded_eq B H rep intent).symm.trans derived
  rcases execute_cases .complete p.snapshot intent with ⟨-, fresh, prepared, after⟩ | ⟨hi, -⟩
  · obtain ⟨w', hs, hrep0⟩ := ofIntent_run B H rep derived' fresh prepared
    have hnext : ready.next = DataSnapshot.install p.snapshot intent := by
      rw [ready.executed] at after
      exact after
    have hrep : Represents B (p.extend ready) w' := by
      unfold Represents
      have hh : (p.extend ready).height = p.height + 1 := by
        simp [Loaded.height, Loaded.extend, DurableReceiver.Image.append]
      have hsnap : (p.extend ready).snapshot = ready.next := rfl
      rw [hh, hsnap, hnext]
      exact hrep0
    refine ⟨w', hs, ?_, ?_⟩
    · unfold Minidregg.Compiler.DurableReceiverIO.afterCheckpoint
      split
      · exact represents_rebaseD B (baseHonest_extend honest ready) hrep
      · exact hrep
    · unfold Minidregg.Compiler.DurableReceiverIO.afterCheckpoint
      split
      · exact baseHonest_rebaseD (baseHonest_extend honest ready)
      · exact baseHonest_extend honest ready
  · rw [ready.executed] at hi
    simp [Installs] at hi

/-- **The clock offset (G-CLOCK, narrowed).**  Under `Represents`, the
deployed logical height every receiver pins (`NativeHost.logicalHeight`) is the
genesis height plus the world's head height: the offset is one constant. -/
theorem represents_logicalHeight (B : Bridge R D)
    {p : Loaded Minidregg.Compiler.ResourceBirthCodec.rootBytes} {w : World R TransactionId D}
    (rep : Represents B p w) (config : NativeHost.Config) :
    ∃ h r, w.head = some (h, r) ∧ NativeHost.logicalHeight config p = config.genesisHeight + h := by
  obtain ⟨r, hr⟩ := rep.head
  exact ⟨p.height, r, hr, rfl⟩

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

/-! ## 5. The deployed bridge, the ROM births, and the traced rows (T3b) -/

section Deployed

open Minidregg.Kernel.DeployedBridge (bridge encodeCell)

/-- **`Represents` over the real codecs.** -/
abbrev DeployedRepresents (p : Loaded Minidregg.Compiler.ResourceBirthCodec.rootBytes)
    (w : World deployedR TransactionId Theory.TypedAuthorization.Digest) : Prop :=
  Represents bridge p w

/-- Its cells field, instantiated: every deployed cell's bytes are the
canonical lifecycle encoding of the world's cell. -/
theorem deployedRepresents_cells {p : Loaded Minidregg.Compiler.ResourceBirthCodec.rootBytes}
    {w : World deployedR TransactionId Theory.TypedAuthorization.Digest}
    (rep : DeployedRepresents p w) (c : CellId) :
    p.snapshot.canonicalBytes ⟨c⟩ = encodeCell (w.cells c) :=
  (Minidregg.Kernel.DeployedBridge.deployed_cells_iff (fun c => p.snapshot.canonicalBytes ⟨c⟩)
    (fun c => w.cells c)).mp rep.cells c

/-- **The derived turn of a deployed source birth carries the record**: if an
intent writes an absent cell with the canonical bytes of a policy-source cell
(as install's `successorCreate` and every initial-policy birth do), the turn
`ofIntent` derives over the deployed bridge creates that cell born with the
record.  Together with `Delta.create_patchOk` (a birth is never `notAPatch`)
this is why install and the births are on no list. -/
theorem ofIntent_policySource_birth {D' : Type} [DecidableEq D']
    {B : Bridge deployedR D'} (hcodec : B.codec = bridge.codec)
    {H : History deployedR TransactionId StableEvent D'} {w : World deployedR TransactionId D'}
    {intent : DataIntent Minidregg.Compiler.ResourceBirthCodec.rootBytes} {t : DTurn deployedR D'}
    (h : Turn.ofIntent B H w intent = .ok t) {wr : DurableDataIntent.DataWrite}
    (hw : wr ∈ intent.writes) (absent : w.cells wr.cellId.value = none)
    {record : Minidregg.Compiler.CanonicalPolicyAdmission.PolicyRecord}
    (post : wr.canonicalPostBytes = encodeCell (some (sourceCell record))) :
    (wr.cellId.value, sourceCell record, none) ∈ t.creates := by
  have d := ofCells_ok h
  obtain ⟨δ, hδ, -, md⟩ := delta_of_write d hw
  have spec := deltaOf_spec hδ
  have dec : B.codec.decode wr.canonicalPostBytes = some (some (sourceCell record)) := by
    rw [hcodec, post]
    exact Minidregg.Kernel.DeployedBridge.bridge_decode_total_on_registry _
  rw [d.eq]
  cases δ with
  | absent => rw [spec.2] at dec; cases dec
  | change k s s' => exact absurd (spec.1.symm.trans absent) (Option.some_ne_none _)
  | create k s' =>
      rw [spec.2] at dec
      have e := Option.some.inj (Option.some.inj dec)
      have hk : k = .policySource := (Cell.mk.inj e).1
      subst hk
      have hs := eq_of_heq (Cell.mk.inj e).2
      subst hs
      have rom : romPart (L := deployedR.layout .policySource)
            (Minidregg.Compiler.PolicySourceCell.stateOfOption (some record)) =
          Minidregg.Compiler.PolicySourceCell.stateOfOption (some record) :=
        romPart_of_romOnly (Minidregg.Kernel.DeployedBridge.policySource_romOnly _)
      exact mem_createsOf.mpr ⟨_, _, _, md,
        Prod.ext rfl (Prod.ext (congrArg (Cell.mk (R := deployedR) .policySource) rom.symm) rfl)⟩

/-! ### The three inferred rows, traced (T3 §2: 13, 14, 16)

Each of `applicationShareIssue`, `applicationGrainShareIssue`,
`applicationAgentLifetimeGrantIssue` admits a nested birth whose descriptor is
pinned to the source's `expectedDescriptor` (`sourceDescriptor`), and that
descriptor carries exactly one initial policy: the ticket / grant policy
record.  So every accepted intent of the three creates one policy-source cell
(through `PreparedBirth.initial_source_write`) -- a ROM birth, a turn since
T3b. -/

theorem shareIssue_birth_has_one_initial_policy {F : Type} [Field F] [DecidableEq F]
    {profile : Minidregg.Compiler.CanonicalRuntimeProfile.Profile F} {config : NativeHost.Config}
    {pins : Minidregg.Theory.ResourceBirth.FactoryPins}
    {durable : ResourceBirthController.Concrete.Durable}
    {height : Minidregg.Theory.TypedAuthorization.Height}
    {ingress : ApplicationShareIssueSource.Ingress}
    (accepted : ApplicationShareIssueAdmission.Accepted profile config pins durable height ingress) :
    accepted.birth.descriptor.initialPolicies.length = 1 := by
  rw [accepted.sourceDescriptor]
  rfl

theorem grainShareIssue_birth_has_one_initial_policy {F : Type} [Field F] [DecidableEq F]
    {profile : Minidregg.Compiler.CanonicalRuntimeProfile.Profile F} {config : NativeHost.Config}
    {pins : Minidregg.Theory.ResourceBirth.FactoryPins}
    {durable : ResourceBirthController.Concrete.Durable}
    {ambient : DeclaredResourceController.Ambient}
    {ingress : ApplicationShareIssueGrainSource.Ingress}
    (accepted : ApplicationShareIssueGrainAdmission.Accepted profile config pins durable ambient
      ingress) :
    accepted.decoded.source.birth.initialPolicies.length = 1 := by
  rw [accepted.sourceDescriptor]
  rfl

theorem lifetimeGrantIssue_birth_has_one_initial_policy {F : Type} [Field F] [DecidableEq F]
    {profile : Minidregg.Compiler.CanonicalRuntimeProfile.Profile F} {config : NativeHost.Config}
    {pins : Minidregg.Theory.ResourceBirth.FactoryPins}
    {durable : ResourceBirthController.Concrete.Durable}
    {height : Minidregg.Theory.TypedAuthorization.Height}
    {ingress : ApplicationAgentLifetimeGrantSource.Ingress}
    (accepted : ApplicationAgentLifetimeGrantAdmission.Accepted profile config pins durable height
      ingress) :
    accepted.birth.descriptor.initialPolicies.length = 1 := by
  rw [accepted.sourceDescriptor]
  rfl

end Deployed

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
  imageBytes := fun _ => 0

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

/-- **Rebase, satisfiable**: the checkpoint state that keeps cell 0's bytes
re-materializes a snapshot that still represents `w0`. -/
theorem toy_rebase_keeping_cell_represents :
    SnapRepresents toyB (DurableCheckpoint.State.snapshot toyRoot ⟨[], [(⟨0⟩, [1, 5])], [], 0⟩ [])
      0 w0 := by
  rw [show (⟨[], [(⟨0⟩, [1, 5])], [], 0⟩ : DurableCheckpoint.State) =
    DurableCheckpoint.State.ofSeed ⟨[], [(⟨0⟩, [1, 5])], 0⟩ from rfl,
    DurableCheckpoint.ofSeed_snapshot]
  exact toy_represents

/-- **Rebase, refuted**: the checkpoint state that drops cell 0 does not. -/
theorem toy_rebase_dropping_cell_breaks :
    ¬ SnapRepresents toyB (DurableCheckpoint.State.snapshot toyRoot ⟨[], [], [], 0⟩ []) 0 w0 :=
  rebase_dropping_cell_breaks toyB _ [] (c := 0) (by simp) rfl
    (by rw [show w0.cells 0 = some (toyCell 1 5) from cells_update_self _ _ _]; simp)

end Example

/-! ## Axiom pins -/

#assert_axioms step_cell_cases
#assert_axioms appendOnly_rewrite_has_no_turn
#assert_axioms birth_rom_image
#assert_axioms birth_needs_create
#assert_axioms policy_source_birth_is_turn
#assert_axioms policy_source_rewrite_has_no_turn
#assert_axioms replay_model
#assert_axioms resume_model
#assert_axioms consumed_of_honest
#assert_axioms lookup_map_self
#assert_axioms rebase_agrees
#assert_axioms represents_rebaseD
#assert_axioms baseHonest_rebaseD
#assert_axioms baseHonest_extend
#assert_axioms rebase_dropping_cell_breaks
#assert_axioms confirmed_represents
#assert_axioms represents_logicalHeight
#assert_axioms deployedRepresents_cells
#assert_axioms ofIntent_policySource_birth
#assert_axioms shareIssue_birth_has_one_initial_policy
#assert_axioms grainShareIssue_birth_has_one_initial_policy
#assert_axioms lifetimeGrantIssue_birth_has_one_initial_policy
#assert_axioms Example.toy_rebase_keeping_cell_represents
#assert_axioms Example.toy_rebase_dropping_cell_breaks
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
/-- info: 'Minidregg.Kernel.HostRefinesWorld.birth_rom_image' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms birth_rom_image
/-- info: 'Minidregg.Kernel.HostRefinesWorld.policy_source_birth_is_turn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms policy_source_birth_is_turn
/-- info: 'Minidregg.Kernel.HostRefinesWorld.policy_source_rewrite_has_no_turn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms policy_source_rewrite_has_no_turn
/-- info: 'Minidregg.Kernel.HostRefinesWorld.represents_rebaseD' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms represents_rebaseD
/-- info: 'Minidregg.Kernel.HostRefinesWorld.confirmed_represents' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms confirmed_represents
/-- info: 'Minidregg.Kernel.HostRefinesWorld.Example.toy_rebase_dropping_cell_breaks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Example.toy_rebase_dropping_cell_breaks
/-- info: 'Minidregg.Kernel.HostRefinesWorld.Example.toy_rewrite_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Example.toy_rewrite_refused
/-- info: 'Minidregg.Kernel.HostRefinesWorld.Example.toy_refined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Example.toy_refined

end Minidregg.Kernel.HostRefinesWorld
