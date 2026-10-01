/-
# Kernel.World -- the world, the turn record, and history as a fold

DATAMODEL §3.3/§3.9, step B2.  The kernel's durable state is one value:

* `World` is a finite map of cells `Π₀ c : CellId, Option (Cell R)` together
  with a distinguished **system cell**, itself a `Theory.Store` over a fixed
  layout with four namespaces: `journal : TxId ↦ (height, H(turn))`
  (append-only), `head : () ↦ (height, logRoot)` (RAM),
  `retired : CellId ↦ ()` (append-only), and `parent : CellId ↦ CellId`
  (append-only; the room a cell was born in, K-ROOM), `spent : D ↦ ()` (append-only;
  the consumed nullifiers, T1) and `allowance : Lane ↦ Nat` (RAM; the remaining
  meter, T1).  The indexes and the history chain are therefore state, written
  by the same guarded `Patch` primitive as every cell.
* `Turn` is deterministic data: a transaction id, the cells it creates, one
  guarded patch per written cell (`Leg`), the cells it retires, and an event;
  and (T1) the nullifiers it spends, its exact charge, its signing subject and
  key epoch, the capability it exercised, and its height window.
  It carries no post bytes, no post roots and no signatures; the post is
  `Patch.run pre patch`.
* `World.admit` is the one fail-closed transition (`step` is its `Option`
  shadow), `fold` is `List.foldlM step`, and a `Checkpoint` is a world at a
  height with its root.

The system half of every accepted turn is the `sysPatch`: a `read retired c none`
guard per create, one `allocate journal txId (height, H turn)`, one
`allocate retired c ()` per retire, the `head` write that advances the height
and chains the log root, and one `allocate parent c room` per create born in a
room; then (T1) one `allocate spent n ()` per nullifier and one
`write allowance lane a (a - charge lane)` per charged lane.  A create's room must be a present cell when the create runs
(`Reject.missingParent`); the row is written once and never rewritten, so
`under R` coverage over `World.parentage` only grows (`step_narrows_stable`).  Journal freshness, retired-identifier refusal and
monotone height are the store's own allocation/write guards, not a second
checker.

## One home per fact (T1, SURPASS §2(b))

* **Spent nullifiers** live in `spent`; the deployed durable consumed set is the
  twin T4 deletes.  **The clock** is the head's height (`fold_head`); a turn's
  clock pin is its `notBefore`/`validUntil` window (`step_window`); the K-CLOCK
  wall-time cell is an ordinary cell, pinned by a read leg.  **The meter** is
  `allowance`, debited by the charge (`charge_le_allowance`), whose storage lane
  is the patch bytes (`charge_is_patch_bytes`).
* **Who is whose parent** lives in the system cell's `parent` rows, written by
  `step` on every create (`step_parent_recorded`, `step_parent_exists`).  The
  authority cell's `parent` plane (tag 13, `CredentialAuthorityCell`) is the
  twin: birth writes the same fact there through one receiver's leg.  T7
  deletes the plane and re-points `Admissible.scope`, delegate's `parentage`,
  `realmWell` and `wellLedgerLoaded` at `World.parentage`.
* **A Book is a cell** (the pay book, the purse, a well): a registry kind whose
  postings are legs; conservation is a property of the leg
  (`TurnCensus.step_conserves`), not a namespace here.  **The tariff** is a cell
  too, or a pinned genesis value; operator pins (`fnGateway`,
  `completionCustodianKey`, the dispatch pins) are Host configuration, not
  world state — and replay must not read them (census (i).11).
* **Indexes are not state.**  The presence index, the link store and the walk
  accumulators are folds over the log; their theorem shape is
  `index_from_replay : index (fold g log) = indexOf log`, which
  `NativeHostReplay.Verified.index_from_replay` already has for the presence
  index.  No namespace here holds them.

The world root is a parameter here (`Checkpoint.check` takes the root
function): its stage-F definition is C1's, its SMT definition D1/E1's.  The
native store and the host's open/submit path are C2's.
-/
import Theory.Store
import Theory.TypedAuthorization
import Theory.ResourceCost
import Theory.AssertAxioms

namespace Minidregg.Kernel.World

open Minidregg.Theory.Store
open Minidregg.Theory.ResourceCost (Lane Charge)

set_option autoImplicit false
/- `World.World` is the world type of the `World` module. -/
set_option linter.dupNamespace false

/-- Cell identifiers are the `Nat`s `create` names (DATAMODEL §3.2). -/
abbrev CellId := Nat

/-! ## Cells and the registry -/

/-- A registry of cell kinds, each with its store layout. -/
structure Registry where
  Kind : Type
  layout : Kind → Layout.{0, 0, 0}
  [kindDecEq : DecidableEq Kind]

attribute [instance] Registry.kindDecEq

/-- A cell is a kind and a store over that kind's layout. -/
structure Cell (R : Registry) where
  kind : R.Kind
  store : Store (R.layout kind)

namespace Cell

variable {R : Registry}

/-- The store of a cell read at an expected kind; `none` on a kind mismatch.
This is the only place a store is transported along a kind equality. -/
def storeAt (cell : Cell R) (k : R.Kind) : Option (Store (R.layout k)) :=
  if h : cell.kind = k then some (h ▸ cell.store) else none

@[simp] theorem storeAt_self (k : R.Kind) (s : Store (R.layout k)) :
    (Cell.mk k s).storeAt k = some s := by
  simp [storeAt]

theorem eq_of_storeAt {cell : Cell R} {k : R.Kind} {s : Store (R.layout k)}
    (h : cell.storeAt k = some s) : cell = ⟨k, s⟩ := by
  rcases cell with ⟨k', s'⟩
  unfold storeAt at h
  split at h
  · rename_i hk
    subst hk
    simp only [Option.some.injEq] at h
    subst h
    rfl
  · exact absurd h (by simp)

end Cell

/-! ## The system cell's layout -/

/-- The namespaces of the system cell. -/
inductive SysSpace
  | journal
  | head
  | retired
  | parent
  | spent
  | allowance
  deriving DecidableEq, Repr

section System

variable (TxId D : Type)

/-- System keys: transaction ids, the unit head key, cell ids, nullifiers
(digests), meter lanes. -/
@[reducible] def SysKey : SysSpace → Type
  | .journal => TxId
  | .head => Unit
  | .retired => CellId
  | .parent => CellId
  | .spent => D
  | .allowance => Lane

/-- System values: `(height, turn digest)`, `(height, log root)`, presence. -/
@[reducible] def SysValue : SysSpace → Type
  | .journal => Nat × D
  | .head => Nat × D
  | .retired => Unit
  | .parent => CellId
  | .spent => Unit
  | .allowance => Nat

/-- The journal, the retired set, the parent rows and the spent set only grow;
the head and the meter are overwritten. -/
def sysDiscipline : SysSpace → Discipline
  | .journal => .appendOnly
  | .head => .ram
  | .retired => .appendOnly
  | .parent => .appendOnly
  | .spent => .appendOnly
  | .allowance => .ram

variable [DecidableEq TxId] [DecidableEq D]

instance sysKeyDecEq : (s : SysSpace) → DecidableEq (SysKey TxId D s)
  | .journal => inferInstanceAs (DecidableEq TxId)
  | .head => inferInstanceAs (DecidableEq Unit)
  | .retired => inferInstanceAs (DecidableEq Nat)
  | .parent => inferInstanceAs (DecidableEq Nat)
  | .spent => inferInstanceAs (DecidableEq D)
  | .allowance => inferInstanceAs (DecidableEq Lane)

instance sysValueDecEq : (s : SysSpace) → DecidableEq (SysValue D s)
  | .journal => inferInstanceAs (DecidableEq (Nat × D))
  | .head => inferInstanceAs (DecidableEq (Nat × D))
  | .retired => inferInstanceAs (DecidableEq Unit)
  | .parent => inferInstanceAs (DecidableEq Nat)
  | .spent => inferInstanceAs (DecidableEq Unit)
  | .allowance => inferInstanceAs (DecidableEq Nat)

/-- The system cell's layout. -/
def sysLayout : Layout.{0, 0, 0} where
  Namespace := SysSpace
  Key := SysKey TxId D
  Value := SysValue D
  discipline := sysDiscipline
  keyDecEq := sysKeyDecEq TxId D
  valueDecEq := sysValueDecEq D

end System

/-! ## The world -/

/-- The cell map. -/
abbrev Cells (R : Registry) := Π₀ _ : CellId, Option (Cell R)

/-- The world: the cell map and the system cell. -/
structure World (R : Registry) (TxId D : Type) [DecidableEq TxId] [DecidableEq D] where
  cells : Cells R
  system : Store (sysLayout TxId D)

namespace World

variable {R : Registry} {TxId D : Type} [DecidableEq TxId] [DecidableEq D]

/-- The journal entry of a transaction id. -/
def journal (w : World R TxId D) (x : TxId) : Option (Nat × D) :=
  w.system ⟨SysSpace.journal, x⟩

/-- The head: current height and log root. -/
def head (w : World R TxId D) : Option (Nat × D) :=
  w.system ⟨SysSpace.head, ()⟩

/-- The retired mark of a cell id. -/
def retired (w : World R TxId D) (c : CellId) : Option Unit :=
  w.system ⟨SysSpace.retired, c⟩

/-- The room a cell was born in. -/
def parent (w : World R TxId D) (c : CellId) : Option CellId :=
  w.system ⟨SysSpace.parent, c⟩

/-- The spent mark of a nullifier (T1: the durable consumed set's home). -/
def spent (w : World R TxId D) (n : D) : Option Unit :=
  w.system ⟨SysSpace.spent, n⟩

/-- The recorded allowance of a meter lane. -/
def allowanceOf (w : World R TxId D) (lane : Lane) : Option Nat :=
  w.system ⟨SysSpace.allowance, lane⟩

/-- The remaining meter: the recorded allowance per lane, zero where none is
recorded (an unrecorded lane funds nothing). -/
def meter (w : World R TxId D) : Charge :=
  fun lane => (w.allowanceOf lane).getD 0

/-- The cell a system address contributes to the parent rows' support. -/
def parentKeyAt : Address (sysLayout TxId D) → Finset CellId
  | ⟨.parent, c⟩ => {c}
  | _ => ∅

theorem mem_parentKeys (s : Store (sysLayout TxId D)) (c : CellId) :
    c ∈ s.support.biUnion parentKeyAt ↔ (s ⟨SysSpace.parent, c⟩).isSome = true := by
  constructor
  · intro member
    obtain ⟨⟨space, key⟩, supported, contributes⟩ := Finset.mem_biUnion.mp member
    cases space <;> simp [parentKeyAt] at contributes
    have same : c = key := Finset.mem_singleton.mp contributes
    subst same
    exact Option.isSome_iff_ne_none.mpr (DFinsupp.mem_support_iff.mp supported)
  · intro present
    exact Finset.mem_biUnion.mpr ⟨⟨SysSpace.parent, c⟩,
      DFinsupp.mem_support_iff.mpr (Option.isSome_iff_ne_none.mp present),
      Finset.mem_singleton_self c⟩

/-- The system cell's parent projection, the parentage `under R` coverage is
decided at: the `parent` rows with their finite support. -/
def parentage (w : World R TxId D) : Theory.TypedAuthorization.Parentage where
  parentOf c := w.parent c
  support := w.system.support.biUnion parentKeyAt
  supported c recorded :=
    (mem_parentKeys w.system c).mpr (Option.isSome_iff_ne_none.mpr recorded)

/-- Present cells are never retired (the `Directory` invariant, over the
system cell's `retired` namespace). -/
def WF (w : World R TxId D) : Prop :=
  ∀ c, w.cells c ≠ none → w.retired c = none

end World

/-! ## The turn record -/

/-- One written cell: its id, the kind the patch is typed at, and the patch. -/
structure Leg (R : Registry) where
  cell : CellId
  kind : R.Kind
  patch : Patch (R.layout kind)

/-- The turn record: deterministic data, no post bytes or roots.  Creates run
first (each at an absent, never-retired id, with the empty store, and in the
room it names — a cell present when the create runs — if any), then the
legs (each a guarded patch at the store its cell holds), then the retires
(each of a present cell whose store is empty).

The T1 fields (each defaulted, so a turn that spends, charges and signs
nothing is written as before):

* `nullifiers` — the markers the turn consumes, allocated in the system cell's
  `spent` namespace; a spent marker is refused (`Reject.nullifierSpent`) and,
  underneath, by the allocation guard.  The durable consumed set's home.
* `charge` — the exact resource charge, per meter lane.  Its storage lane is
  the turn's patch bytes (`H.legBytes` summed over the legs: D2's "a record is
  charged the bytes it writes", `charge_is_patch_bytes`); the whole charge is
  debited from the `allowance` namespace and refused above it.
* `subject`, `keyEpoch`, `capability` — who signed, at which key epoch, under
  which capability.  They are turn data, bound by the turn digest into the
  journal and the log chain; `admit` decides none of them (the authority
  decision stays in the receiver until T3 derives the turn from it).
* `notBefore`, `validUntil` — the clock pin: the height window the turn may be
  journaled in (`valid_until` is a block height, 09-29).  The wall clock is
  the K-CLOCK cell, pinned like any other read: by a read leg.

The footprint (the addresses read, with the values they must hold) is not a
field: it is the read ops of the legs (`Turn.footprint`), so it cannot
disagree with what `admit` checks. -/
structure Turn (R : Registry) (TxId Ev D : Type) where
  txId : TxId
  creates : List (CellId × R.Kind × Option CellId)
  legs : List (Leg R)
  retires : List CellId
  event : Ev
  nullifiers : List D := []
  charge : Charge := 0
  subject : Option Theory.TypedAuthorization.SubjectId := none
  keyEpoch : Nat := 0
  capability : Option D := none
  notBefore : Nat := 0
  validUntil : Option Nat := none

/-- The `(cell, room)` rows a turn's creates record. -/
def Turn.parentRows {R : Registry} {TxId Ev D : Type} (t : Turn R TxId Ev D) :
    List (CellId × CellId) :=
  t.creates.filterMap fun c => c.2.2.map fun room => (c.1, room)

/-- Whether an op is a read (a guard that changes nothing). -/
def Op.isRead {L : Layout.{0, 0, 0}} : Op L → Bool
  | .read _ _ _ => true
  | _ => false

/-- A leg's guards: its leading reads.  The turn's footprint is the guards of
its legs — each the address it reads and the value that address must hold
(K-FIELDS' address-level footprint).  It is read off the legs, never carried
beside them. -/
def Leg.guards {R : Registry} (leg : Leg R) : Patch (R.layout leg.kind) :=
  leg.patch.takeWhile Op.isRead

/-- The cells the turn's footprint pins. -/
def Turn.footprint {R : Registry} {TxId Ev D : Type} (t : Turn R TxId Ev D) : List CellId :=
  (t.legs.filter fun leg => !leg.guards.isEmpty).map Leg.cell

/-- The hash surface history needs: a turn digest and the log chain.  Stage F
instantiates both with cSHAKE over the turn's canonical bytes (C1). -/
structure History (R : Registry) (TxId Ev D : Type) where
  turnDigest : Turn R TxId Ev D → D
  chain : D → D → D
  logRoot0 : D
  /-- The bytes a leg writes, the storage charge's unit (D2).  Stage F counts
  the canonical encoding of the leg's write, allocate and free ops; it has no
  default, so no history charges nothing by omission. -/
  legBytes : Leg R → Nat

/-- Refusal reasons.  Every refusal leaves the world unchanged (`admit` returns
no world on any error branch). -/
inductive Reject
  | emptyTurn
  | duplicateLegCell
  | duplicateCreate
  | duplicateRetire
  | noHead
  | replayedTransaction
  | retiredIdentifier
  | cellPresent (cell : CellId)
  | missingCell (cell : CellId)
  | kindMismatch (cell : CellId)
  | guardFailed (cell : CellId) (index : Nat)
  | retireNonEmpty (cell : CellId)
  | missingParent (cell : CellId) (room : CellId)
  | duplicateNullifier
  | outsideWindow
  | nullifierSpent
  | chargeMismatch
  | overAllowance
  deriving DecidableEq, Repr

/-- The reason an `Except` refused, if it did. -/
def rejectOf {α : Type} : Except Reject α → Option Reject
  | .error r => some r
  | .ok _ => none

section Step

variable {R : Registry} {TxId Ev D : Type} [DecidableEq TxId] [DecidableEq D]
variable (H : History R TxId Ev D)

/-- The B2/K-ROOM system half of a turn: retired guards, the journal row, the
retires, the head, the parent rows. -/
def sysCore (t : Turn R TxId Ev D) (height : Nat) (logRoot : D) :
    Patch (sysLayout TxId D) :=
  t.creates.map (fun c => Op.read (L := sysLayout TxId D) SysSpace.retired c.1 none) ++
    [Op.allocate (L := sysLayout TxId D) SysSpace.journal t.txId (height, H.turnDigest t)] ++
    t.retires.map (fun c => Op.allocate (L := sysLayout TxId D) SysSpace.retired c ()) ++
    [Op.write (L := sysLayout TxId D) SysSpace.head () (height, logRoot)
      (height + 1, H.chain logRoot (H.turnDigest t))] ++
    t.parentRows.map (fun row => Op.allocate (L := sysLayout TxId D) SysSpace.parent row.1 row.2)

/-- The meter lanes, each once. -/
def meterLanes : List Lane :=
  [.incidences, .turnBytes, .memoryTouches, .witnessBytes, .proofWork, .storageBytes,
    .networkBytes, .sideEffectCount, .feeDebit, .leaseByteBlocks]

/-- The lanes a charge debits: those it charges a nonzero amount. -/
def chargedLanes (charge : Charge) : List Lane :=
  meterLanes.filter fun lane => charge lane ≠ 0

/-- One spent mark per nullifier. -/
def spentAllocs (ns : List D) : Patch (sysLayout TxId D) :=
  ns.map fun n => Op.allocate (L := sysLayout TxId D) SysSpace.spent n ()

/-- The meter debit: each listed lane goes from `avail` to `avail - charge`. -/
def debits (lanes : List Lane) (charge avail : Charge) : Patch (sysLayout TxId D) :=
  lanes.map fun lane =>
    Op.write (L := sysLayout TxId D) SysSpace.allowance lane (avail lane) (avail lane - charge lane)

/-- The system half of a turn, as one guarded patch on the system cell: the
core, then the spent marks, then the meter debit from `avail` (the world's
`meter`). -/
def sysPatch (t : Turn R TxId Ev D) (height : Nat) (logRoot : D) (avail : Charge) :
    Patch (sysLayout TxId D) :=
  sysCore H t height logRoot ++ spentAllocs t.nullifiers ++
    debits (chargedLanes t.charge) t.charge avail

/-- The patch bytes of a turn: the bytes its legs write. -/
def patchBytes (t : Turn R TxId Ev D) : Nat :=
  (t.legs.map H.legBytes).sum

/-- The T1 checks, each a named refusal of something the store guards would
also refuse (or, for the charge rule and the window, something no store guard
sees): distinct nullifiers, the height window, unspent nullifiers, the charge
rule (storage lane = patch bytes), the charge within the meter. -/
def turnCheck (w : World R TxId D) (t : Turn R TxId Ev D) (height : Nat) : Option Reject :=
  if ¬ t.nullifiers.Nodup then some .duplicateNullifier
  else if ¬ (t.notBefore ≤ height ∧ (t.validUntil.all fun u => decide (height ≤ u)) = true) then
    some .outsideWindow
  else if ∃ n ∈ t.nullifiers, (w.spent n).isSome then some .nullifierSpent
  else if t.charge .storageBytes ≠ patchBytes H t then some .chargeMismatch
  else if Charge.fundedCheck t.charge w.meter = false then some .overAllowance
  else none

/-- A create's room, if it names one, is a present cell. -/
def roomPresent (cells : Cells R) : Option CellId → Bool
  | none => true
  | some room => (cells room).isSome

/-- Create the listed cells, each at an absent id, with the empty store, each
in a room that is present when it is created (an earlier create of the same
turn counts). -/
def applyCreates : Cells R → List (CellId × R.Kind × Option CellId) → Except Reject (Cells R)
  | cells, [] => .ok cells
  | cells, (c, k, p) :: rest =>
      match cells c, roomPresent cells p with
      | some _, _ => .error (.cellPresent c)
      | none, false => .error (.missingParent c (p.getD 0))
      | none, true => applyCreates (cells.update c (some ⟨k, 0⟩)) rest

/-- Apply one leg: the cell is present at the leg's kind and the patch is
valid from the store it holds. -/
def applyLeg (cells : Cells R) (leg : Leg R) : Except Reject (Cells R) :=
  match cells leg.cell with
  | none => .error (.missingCell leg.cell)
  | some cell =>
      match cell.storeAt leg.kind with
      | none => .error (.kindMismatch leg.cell)
      | some pre =>
          match Patch.firstDisabled? pre leg.patch with
          | some index => .error (.guardFailed leg.cell index)
          | none => .ok (cells.update leg.cell (some ⟨leg.kind, Patch.run pre leg.patch⟩))

/-- Apply the legs in order. -/
def applyLegs : Cells R → List (Leg R) → Except Reject (Cells R)
  | cells, [] => .ok cells
  | cells, leg :: rest =>
      match applyLeg cells leg with
      | .error r => .error r
      | .ok next => applyLegs next rest

/-- Retire the listed cells, each present with an empty store.  Emptying a
cell is a guarded patch in a leg of the same or an earlier turn, so a retire
never discards a value no guard has seen. -/
def applyRetires : Cells R → List CellId → Except Reject (Cells R)
  | cells, [] => .ok cells
  | cells, c :: rest =>
      match cells c with
      | none => .error (.missingCell c)
      | some cell =>
          if cell.store = 0 then applyRetires (cells.update c none) rest
          else .error (.retireNonEmpty c)

/-- The cell half of a turn: creates, then legs, then retires. -/
def applyCells (cells : Cells R) (t : Turn R TxId Ev D) : Except Reject (Cells R) :=
  match applyCreates cells t.creates with
  | .error r => .error r
  | .ok c1 =>
      match applyLegs c1 t.legs with
      | .error r => .error r
      | .ok c2 => applyRetires c2 t.retires

/-- A turn is well-shaped: it does something, and names each cell at most once
per role. -/
def Shaped (t : Turn R TxId Ev D) : Prop :=
  ¬ (t.legs.isEmpty ∧ t.creates.isEmpty ∧ t.retires.isEmpty) ∧
    (t.legs.map Leg.cell).Nodup ∧ (t.creates.map Prod.fst).Nodup ∧ t.retires.Nodup

/-- **The one transition.**  Fail-closed: every error branch returns no world. -/
def World.admit (w : World R TxId D) (t : Turn R TxId Ev D) : Except Reject (World R TxId D) :=
  if t.legs.isEmpty ∧ t.creates.isEmpty ∧ t.retires.isEmpty then .error .emptyTurn
  else if ¬ (t.legs.map Leg.cell).Nodup then .error .duplicateLegCell
  else if ¬ (t.creates.map Prod.fst).Nodup then .error .duplicateCreate
  else if ¬ t.retires.Nodup then .error .duplicateRetire
  else
    match w.head with
    | none => .error .noHead
    | some (height, logRoot) =>
        if (w.journal t.txId).isSome then .error .replayedTransaction
        else match turnCheck H w t height with
        | some r => .error r
        | none =>
          if ¬ Patch.ValidFrom w.system (sysPatch H t height logRoot w.meter) then
            .error .retiredIdentifier
          else
            match applyCells w.cells t with
            | .error r => .error r
            | .ok cells => .ok ⟨cells, Patch.run w.system (sysPatch H t height logRoot w.meter)⟩

/-- `step` is `admit` with the reason forgotten. -/
def World.step (w : World R TxId D) (t : Turn R TxId Ev D) : Option (World R TxId D) :=
  (World.admit H w t).toOption

/-- The state after a log. -/
def fold (g : World R TxId D) (log : List (Turn R TxId Ev D)) : Option (World R TxId D) :=
  log.foldlM (World.step H) g

/-- The log chain of a list of turns from a starting log root. -/
def logChain (r : D) (log : List (Turn R TxId Ev D)) : D :=
  log.foldl (fun acc t => H.chain acc (H.turnDigest t)) r

/-- A genesis world: height zero at the initial log root, empty journal. -/
def Genesis (g : World R TxId D) : Prop :=
  g.head = some (0, H.logRoot0) ∧ ∀ x, g.journal x = none

/-- The genesis system cell: only the head is present. -/
def genesisSystem : Store (sysLayout TxId D) :=
  Store.set 0 ⟨SysSpace.head, ()⟩ (some ((0 : Nat), H.logRoot0))

/-- The genesis world over given initial cells. -/
def genesis (cells : Cells R) : World R TxId D :=
  ⟨cells, genesisSystem H⟩

end Step


/-! ## The fold: monoid-action laws and replay exactness (DATAMODEL §4.3) -/

section Fold

variable {R : Registry} {TxId Ev D : Type} [DecidableEq TxId] [DecidableEq D]
variable (H : History R TxId Ev D)

@[simp] theorem fold_nil (g : World R TxId D) : fold H g [] = some g := rfl

theorem fold_cons (g : World R TxId D) (t : Turn R TxId Ev D) (log : List (Turn R TxId Ev D)) :
    fold H g (t :: log) = (World.step H g t).bind (fun w => fold H w log) := rfl

/-- **History is a fold.**  Folding a concatenated log is folding the prefix,
then the suffix from where the prefix left the world. -/
theorem fold_append (g : World R TxId D) (l₁ l₂ : List (Turn R TxId Ev D)) :
    fold H g (l₁ ++ l₂) = (fold H g l₁).bind (fun w => fold H w l₂) := by
  induction l₁ generalizing g with
  | nil => rfl
  | cons t l ih =>
      rw [List.cons_append, fold_cons, fold_cons]
      cases World.step H g t with
      | none => rfl
      | some w => exact ih w

theorem fold_snoc (g : World R TxId D) (l : List (Turn R TxId Ev D)) (t : Turn R TxId Ev D) :
    fold H g (l ++ [t]) = (fold H g l).bind (fun w => World.step H w t) := by
  rw [fold_append]
  cases fold H g l with
  | none => rfl
  | some w =>
      show (World.step H w t).bind (fun w' => fold H w' []) = World.step H w t
      cases World.step H w t <;> rfl

/-- The relational reading of history: a world is reached by a log when each
turn in order is admitted at the world its prefix reached. -/
inductive Reaches (g : World R TxId D) : List (Turn R TxId Ev D) → World R TxId D → Prop
  | nil : Reaches g [] g
  | snoc {log : List (Turn R TxId Ev D)} {t : Turn R TxId Ev D} {w w' : World R TxId D} :
      Reaches g log w → World.step H w t = some w' → Reaches g (log ++ [t]) w'

/-- **Replay exactness (§4.3).**  The executable fold returns a world exactly
when that world is reached by admitting the log turn by turn; the state after
a log is therefore unique and is the fold. -/
theorem fold_eq_some_iff (g : World R TxId D) (log : List (Turn R TxId Ev D))
    (W : World R TxId D) : fold H g log = some W ↔ Reaches H g log W := by
  constructor
  · intro h
    induction log using List.reverseRecOn generalizing W with
    | nil =>
        simp only [fold_nil, Option.some.injEq] at h
        subst h
        exact .nil
    | append_singleton l t ih =>
        rw [fold_snoc] at h
        cases hl : fold H g l with
        | none => rw [hl] at h; cases h
        | some w =>
            rw [hl] at h
            exact .snoc (ih w hl) h
  · intro h
    induction h with
    | nil => rfl
    | snoc _ hstep ih => rw [fold_snoc, ih]; exact hstep

end Fold

/-! ## Decomposing an accepted turn -/

section Decompose

variable {R : Registry} {TxId Ev D : Type} [DecidableEq TxId] [DecidableEq D]
variable (H : History R TxId Ev D)

theorem cells_update_self (cells : Cells R) (c : CellId) (v : Option (Cell R)) :
    cells.update c v c = v := by
  simp

theorem cells_update_ne (cells : Cells R) {c x : CellId} (v : Option (Cell R))
    (h : x ≠ c) : cells.update c v x = cells x := by
  simp [DFinsupp.coe_update, Function.update_of_ne h]

theorem step_eq_some {w w' : World R TxId D} {t : Turn R TxId Ev D} :
    World.step H w t = some w' ↔ World.admit H w t = .ok w' := by
  unfold World.step
  cases World.admit H w t <;> simp [Except.toOption]

/-- An accepted turn: well-shaped, the head present, the transaction id
absent from the journal, the system patch valid, the cell half accepted, and
the post system cell exactly `run` of the system patch. -/
theorem admit_ok {w w' : World R TxId D} {t : Turn R TxId Ev D}
    (h : World.admit H w t = .ok w') :
    Shaped t ∧ ∃ height logRoot, w.head = some (height, logRoot) ∧
      w.journal t.txId = none ∧
      Patch.ValidFrom w.system (sysPatch H t height logRoot w.meter) ∧
      applyCells w.cells t = .ok w'.cells ∧
      w'.system = Patch.run w.system (sysPatch H t height logRoot w.meter) := by
  unfold World.admit at h
  by_cases hE : t.legs.isEmpty ∧ t.creates.isEmpty ∧ t.retires.isEmpty
  · rw [if_pos hE] at h; cases h
  rw [if_neg hE] at h
  by_cases hL : (t.legs.map Leg.cell).Nodup
  swap
  · rw [if_pos hL] at h; cases h
  rw [if_neg (not_not.mpr hL)] at h
  by_cases hC : (t.creates.map Prod.fst).Nodup
  swap
  · rw [if_pos hC] at h; cases h
  rw [if_neg (not_not.mpr hC)] at h
  by_cases hR : t.retires.Nodup
  swap
  · rw [if_pos hR] at h; cases h
  rw [if_neg (not_not.mpr hR)] at h
  refine ⟨⟨hE, hL, hC, hR⟩, ?_⟩
  cases hh : w.head with
  | none => simp [hh] at h
  | some p =>
      obtain ⟨height, logRoot⟩ := p
      simp only [hh] at h
      by_cases hJ : (w.journal t.txId).isSome
      · rw [if_pos hJ] at h; cases h
      rw [if_neg hJ] at h
      cases hk : turnCheck H w t height with
      | some r => rw [hk] at h; cases h
      | none =>
      rw [hk] at h
      by_cases hV : Patch.ValidFrom w.system (sysPatch H t height logRoot w.meter)
      swap
      · rw [if_pos hV] at h; cases h
      rw [if_neg (not_not.mpr hV)] at h
      cases hc : applyCells w.cells t with
      | error r => rw [hc] at h; cases h
      | ok cells =>
          rw [hc] at h
          cases h
          exact ⟨height, logRoot, rfl, by simpa using hJ, hV, rfl, rfl⟩

/-- The T1 half of an accepted turn: its checks passed at the height it was
journaled at. -/
theorem admit_ok_turnCheck {w w' : World R TxId D} {t : Turn R TxId Ev D}
    (h : World.admit H w t = .ok w') :
    ∃ height logRoot, w.head = some (height, logRoot) ∧ turnCheck H w t height = none := by
  unfold World.admit at h
  by_cases hE : t.legs.isEmpty ∧ t.creates.isEmpty ∧ t.retires.isEmpty
  · rw [if_pos hE] at h; cases h
  rw [if_neg hE] at h
  by_cases hL : (t.legs.map Leg.cell).Nodup
  swap
  · rw [if_pos hL] at h; cases h
  rw [if_neg (not_not.mpr hL)] at h
  by_cases hC : (t.creates.map Prod.fst).Nodup
  swap
  · rw [if_pos hC] at h; cases h
  rw [if_neg (not_not.mpr hC)] at h
  by_cases hR : t.retires.Nodup
  swap
  · rw [if_pos hR] at h; cases h
  rw [if_neg (not_not.mpr hR)] at h
  cases hh : w.head with
  | none => simp [hh] at h
  | some p =>
      obtain ⟨height, logRoot⟩ := p
      simp only [hh] at h
      by_cases hJ : (w.journal t.txId).isSome
      · rw [if_pos hJ] at h; cases h
      rw [if_neg hJ] at h
      cases hk : turnCheck H w t height with
      | some r => rw [hk] at h; cases h
      | none => exact ⟨height, logRoot, rfl, hk⟩

/-- The converse of `admit_ok`: every premise it names is also sufficient. -/
theorem admit_of {w : World R TxId D} {t : Turn R TxId Ev D} {height : Nat} {logRoot : D}
    {cells : Cells R} (shaped : Shaped t) (hh : w.head = some (height, logRoot))
    (hj : w.journal t.txId = none)
    (hk : turnCheck H w t height = none)
    (hv : Patch.ValidFrom w.system (sysPatch H t height logRoot w.meter))
    (hc : applyCells w.cells t = .ok cells) :
    World.admit H w t = .ok ⟨cells, Patch.run w.system (sysPatch H t height logRoot w.meter)⟩ := by
  obtain ⟨hE, hL, hC, hR⟩ := shaped
  unfold World.admit
  rw [if_neg hE, if_neg (not_not.mpr hL), if_neg (not_not.mpr hC), if_neg (not_not.mpr hR)]
  simp only [hh]
  rw [if_neg (by simp [hj]), hk]
  simp only
  rw [if_neg (not_not.mpr hv)]
  simp only [hc]

omit [DecidableEq TxId] in
theorem applyCells_ok {cells cells' : Cells R} {t : Turn R TxId Ev D}
    (h : applyCells cells t = .ok cells') :
    ∃ c1 c2, applyCreates cells t.creates = .ok c1 ∧ applyLegs c1 t.legs = .ok c2 ∧
      applyRetires c2 t.retires = .ok cells' := by
  unfold applyCells at h
  cases h1 : applyCreates cells t.creates with
  | error r => simp only [h1] at h; cases h
  | ok c1 =>
      simp only [h1] at h
      cases h2 : applyLegs c1 t.legs with
      | error r => simp only [h2] at h; cases h
      | ok c2 => simp only [h2] at h; exact ⟨c1, c2, rfl, h2, h⟩

/-! ### Creates -/

theorem applyCreates_frame : ∀ {cells cells' : Cells R} {cs : List (CellId × R.Kind × Option CellId)},
    applyCreates cells cs = .ok cells' → ∀ x, x ∉ cs.map Prod.fst → cells' x = cells x
  | cells, cells', [], h, x, _ => by cases h; rfl
  | cells, cells', (c, k, p) :: rest, h, x, hx => by
      unfold applyCreates at h
      split at h
      · cases h
      · cases h
      · have hxc : x ≠ c := fun e => hx (by simp [e])
        have hxr : x ∉ rest.map Prod.fst := fun m => hx (List.mem_cons_of_mem _ m)
        rw [applyCreates_frame h x hxr, cells_update_ne _ _ hxc]

theorem applyCreates_mem : ∀ {cells cells' : Cells R} {cs : List (CellId × R.Kind × Option CellId)},
    applyCreates cells cs = .ok cells' → (cs.map Prod.fst).Nodup →
      ∀ c k p, (c, k, p) ∈ cs → cells c = none ∧ cells' c = some ⟨k, 0⟩
  | _, _, [], _, _, _, _, _, m => absurd m (by simp)
  | cells, cells', (c0, k0, p0) :: rest, h, nd, c, k, p, m => by
      unfold applyCreates at h
      split at h
      · cases h
      · cases h
      · rename_i hc0 _
        simp only [List.map_cons, List.nodup_cons] at nd
        rcases List.mem_cons.mp m with e | m'
        · simp only [Prod.mk.injEq] at e
          obtain ⟨rfl, rfl, rfl⟩ := e
          refine ⟨hc0, ?_⟩
          rw [applyCreates_frame h c nd.1, cells_update_self]
        · have hne : c ≠ c0 := fun e => nd.1 (e ▸ List.mem_map_of_mem (f := Prod.fst) m')
          obtain ⟨hnone, hpost⟩ := applyCreates_mem h nd.2 c k p m'
          rw [cells_update_ne _ _ hne] at hnone
          exact ⟨hnone, hpost⟩

/-- A create's room was present when the create ran: present before the turn,
or created by an earlier create of the same turn. -/
theorem applyCreates_room : ∀ {cells cells' : Cells R} {cs : List (CellId × R.Kind × Option CellId)},
    applyCreates cells cs = .ok cells' →
      ∀ c k room, (c, k, some room) ∈ cs → cells room ≠ none ∨ room ∈ cs.map Prod.fst
  | _, _, [], _, _, _, _, m => absurd m (by simp)
  | cells, cells', (c0, k0, p0) :: rest, h, c, k, room, m => by
      unfold applyCreates at h
      split at h
      · cases h
      · cases h
      · rename_i _ hp0
        rcases List.mem_cons.mp m with e | m'
        · simp only [Prod.mk.injEq] at e
          obtain ⟨rfl, rfl, rfl⟩ := e
          simp only [roomPresent, Option.isSome_iff_ne_none] at hp0
          exact .inl hp0
        · rcases applyCreates_room h c k room m' with present | later
          · by_cases e : room = c0
            · exact .inr (by simp [e])
            · rw [cells_update_ne _ _ e] at present
              exact .inl present
          · exact .inr (List.mem_cons_of_mem _ later)

/-- Refusal pole: a create whose room is absent (and not created earlier in the
same turn) is refused, naming the cell and the room. -/
theorem applyCreates_missing_room (cells : Cells R) (c : CellId) (k : R.Kind) (room : CellId)
    (rest : List (CellId × R.Kind × Option CellId))
    (fresh : cells c = none) (absent : cells room = none) :
    applyCreates cells ((c, k, some room) :: rest) = .error (.missingParent c room) := by
  simp [applyCreates, fresh, roomPresent, absent]

theorem applyCreates_present : ∀ {cells cells' : Cells R} {cs : List (CellId × R.Kind × Option CellId)},
    applyCreates cells cs = .ok cells' → ∀ x, cells' x ≠ none →
      cells x ≠ none ∨ x ∈ cs.map Prod.fst
  | _, _, [], h, x, hx => by cases h; exact .inl hx
  | cells, cells', (c, k, p) :: rest, h, x, hx => by
      unfold applyCreates at h
      split at h
      · cases h
      · cases h
      · rcases applyCreates_present h x hx with p | m
        · by_cases e : x = c
          · exact .inr (by simp [e])
          · rw [cells_update_ne _ _ e] at p; exact .inl p
        · exact .inr (List.mem_cons_of_mem _ m)

/-! ### Legs -/

theorem applyLeg_ok {cells cells' : Cells R} {leg : Leg R}
    (h : applyLeg cells leg = .ok cells') :
    ∃ cell pre, cells leg.cell = some cell ∧ cell.storeAt leg.kind = some pre ∧
      Patch.ValidFrom pre leg.patch ∧
      cells' = cells.update leg.cell (some ⟨leg.kind, Patch.run pre leg.patch⟩) := by
  unfold applyLeg at h
  split at h
  · cases h
  · rename_i cell hcell
    split at h
    · cases h
    · rename_i pre hpre
      split at h
      · cases h
      · rename_i hfd
        cases h
        exact ⟨cell, pre, hcell, hpre, (Patch.firstDisabled?_eq_none_iff pre leg.patch).1 hfd, rfl⟩

theorem applyLegs_frame : ∀ {cells cells' : Cells R} {legs : List (Leg R)},
    applyLegs cells legs = .ok cells' → ∀ x, x ∉ legs.map Leg.cell → cells' x = cells x
  | _, _, [], h, x, _ => by cases h; rfl
  | cells, cells', leg :: rest, h, x, hx => by
      unfold applyLegs at h
      split at h
      · cases h
      · rename_i next hnext
        obtain ⟨_, _, _, _, _, rfl⟩ := applyLeg_ok hnext
        have hxc : x ≠ leg.cell := fun e => hx (by simp [e])
        have hxr : x ∉ rest.map Leg.cell := fun m => hx (List.mem_cons_of_mem _ m)
        rw [applyLegs_frame h x hxr, cells_update_ne _ _ hxc]

/-- **Per-leg exactness.**  Each leg's cell ends holding `run pre patch`, where
`pre` is the store the cell held when the turn's legs began and the patch is
valid from it. -/
theorem applyLegs_mem : ∀ {cells cells' : Cells R} {legs : List (Leg R)},
    applyLegs cells legs = .ok cells' → (legs.map Leg.cell).Nodup →
      ∀ leg, leg ∈ legs → ∃ pre, (cells leg.cell).bind (·.storeAt leg.kind) = some pre ∧
        Patch.ValidFrom pre leg.patch ∧
        cells' leg.cell = some ⟨leg.kind, Patch.run pre leg.patch⟩
  | _, _, [], _, _, _, m => absurd m (by simp)
  | cells, cells', l0 :: rest, h, nd, leg, m => by
      unfold applyLegs at h
      split at h
      · cases h
      · rename_i next hnext
        simp only [List.map_cons, List.nodup_cons] at nd
        obtain ⟨cell, pre, hcell, hpre, hvalid, rfl⟩ := applyLeg_ok hnext
        rcases List.mem_cons.mp m with rfl | m'
        · refine ⟨pre, by simp [hcell, hpre], hvalid, ?_⟩
          rw [applyLegs_frame h leg.cell nd.1, cells_update_self]
        · have hne : leg.cell ≠ l0.cell :=
            fun e => nd.1 (e ▸ List.mem_map_of_mem (f := Leg.cell) m')
          obtain ⟨pre', hpre', hv', hpost⟩ := applyLegs_mem h nd.2 leg m'
          rw [cells_update_ne _ _ hne] at hpre'
          exact ⟨pre', hpre', hv', hpost⟩

theorem applyLegs_present : ∀ {cells cells' : Cells R} {legs : List (Leg R)},
    applyLegs cells legs = .ok cells' → ∀ x, cells' x ≠ none → cells x ≠ none
  | _, _, [], h, x, hx => by cases h; exact hx
  | cells, cells', leg :: rest, h, x, hx => by
      unfold applyLegs at h
      split at h
      · cases h
      · rename_i next hnext
        obtain ⟨cell, _, hcell, _, _, rfl⟩ := applyLeg_ok hnext
        have p := applyLegs_present h x hx
        by_cases e : x = leg.cell
        · rw [e, hcell]; simp
        · rwa [cells_update_ne _ _ e] at p

/-! ### Retires -/

theorem applyRetires_frame : ∀ {cells cells' : Cells R} {rs : List CellId},
    applyRetires cells rs = .ok cells' → ∀ x, x ∉ rs → cells' x = cells x
  | _, _, [], h, x, _ => by cases h; rfl
  | cells, cells', c :: rest, h, x, hx => by
      unfold applyRetires at h
      split at h
      · cases h
      · split at h
        · have hxc : x ≠ c := fun e => hx (by simp [e])
          rw [applyRetires_frame h x (fun m => hx (List.mem_cons_of_mem _ m)),
            cells_update_ne _ _ hxc]
        · cases h

theorem applyRetires_mem : ∀ {cells cells' : Cells R} {rs : List CellId},
    applyRetires cells rs = .ok cells' → rs.Nodup →
      ∀ c, c ∈ rs → (∃ cell, cells c = some cell ∧ cell.store = 0) ∧ cells' c = none
  | _, _, [], _, _, _, m => absurd m (by simp)
  | cells, cells', c0 :: rest, h, nd, c, m => by
      unfold applyRetires at h
      split at h
      · cases h
      · rename_i cell hcell
        split at h
        · rename_i hempty
          rw [List.nodup_cons] at nd
          rcases List.mem_cons.mp m with rfl | m'
          · exact ⟨⟨cell, hcell, hempty⟩, by rw [applyRetires_frame h c nd.1, cells_update_self]⟩
          · have hne : c ≠ c0 := fun e => nd.1 (e ▸ m')
            obtain ⟨⟨cell', hc', he'⟩, hpost⟩ := applyRetires_mem h nd.2 c m'
            rw [cells_update_ne _ _ hne] at hc'
            exact ⟨⟨cell', hc', he'⟩, hpost⟩
        · cases h

theorem applyRetires_present : ∀ {cells cells' : Cells R} {rs : List CellId},
    applyRetires cells rs = .ok cells' → ∀ x, cells' x ≠ none → cells x ≠ none
  | _, _, [], h, x, hx => by cases h; exact hx
  | cells, cells', c :: rest, h, x, hx => by
      unfold applyRetires at h
      split at h
      · cases h
      · rename_i cell hcell
        split at h
        · have p := applyRetires_present h x hx
          by_cases e : x = c
          · subst e; rw [cells_update_self] at p; exact absurd rfl p
          · rwa [cells_update_ne _ _ e] at p
        · cases h

/-! ### The system patch -/

theorem op_apply_write {L : Layout.{0, 0, 0}} (s : Store L) (sp : L.Namespace) (k : L.Key sp)
    (b a : L.Value sp) : Op.apply s (.write sp k b a) = s.set ⟨sp, k⟩ (some a) := rfl

theorem op_apply_allocate {L : Layout.{0, 0, 0}} (s : Store L) (sp : L.Namespace) (k : L.Key sp)
    (v : L.Value sp) : Op.apply s (.allocate sp k v) = s.set ⟨sp, k⟩ (some v) := rfl

theorem sys_space_ne {a b : SysSpace} {k : SysKey TxId D a} {k' : SysKey TxId D b} (h : a ≠ b) :
    (⟨a, k⟩ : Address (sysLayout TxId D)) ≠ ⟨b, k'⟩ :=
  fun e => h (congrArg Sigma.fst e)

theorem sys_key_ne {a : SysSpace} {k k' : SysKey TxId D a} (h : k ≠ k') :
    (⟨a, k⟩ : Address (sysLayout TxId D)) ≠ ⟨a, k'⟩ :=
  fun e => h (eq_of_heq (Sigma.mk.inj e).2)

theorem run_createReads (s : Store (sysLayout TxId D)) (cs : List (CellId × R.Kind × Option CellId)) :
    Patch.run s (cs.map (fun c => Op.read (L := sysLayout TxId D) SysSpace.retired c.1 none)) = s := by
  induction cs with
  | nil => rfl
  | cons c rest ih => exact ih

theorem validFrom_createReads (s : Store (sysLayout TxId D)) (cs : List (CellId × R.Kind × Option CellId)) :
    Patch.ValidFrom s (cs.map (fun c => Op.read (L := sysLayout TxId D) SysSpace.retired c.1 none)) ↔
      ∀ c ∈ cs, s ⟨SysSpace.retired, c.1⟩ = none := by
  induction cs with
  | nil => simp [Patch.ValidFrom]
  | cons c rest ih =>
      simp only [List.map_cons, Patch.ValidFrom, List.mem_cons, forall_eq_or_imp]
      exact and_congr Iff.rfl ih

theorem run_retireAllocs_ne (s : Store (sysLayout TxId D)) (rs : List CellId)
    (a : Address (sysLayout TxId D)) (ha : a.1 ≠ SysSpace.retired) :
    Patch.run s (rs.map (fun c => Op.allocate (L := sysLayout TxId D) SysSpace.retired c ())) a =
      s a := by
  induction rs generalizing s with
  | nil => rfl
  | cons c rest ih =>
      show Patch.run (s.set ⟨SysSpace.retired, c⟩ (some ())) _ a = s a
      rw [ih]
      exact Store.set_ne _ _ _ _ (fun e => ha (congrArg Sigma.fst e))

theorem run_retireAllocs_at (s : Store (sysLayout TxId D)) (rs : List CellId) (c : CellId) :
    Patch.run s (rs.map (fun c => Op.allocate (L := sysLayout TxId D) SysSpace.retired c ()))
        ⟨SysSpace.retired, c⟩ =
      if c ∈ rs then some () else s ⟨SysSpace.retired, c⟩ := by
  induction rs generalizing s with
  | nil => simp only [List.not_mem_nil, if_false]; rfl
  | cons c0 rest ih =>
      show Patch.run (s.set ⟨SysSpace.retired, c0⟩ (some ())) _ _ = _
      rw [ih]
      by_cases hr : c ∈ rest
      · simp [hr]
      · by_cases e : c = c0
        · subst e
          simp only [hr, if_false, List.mem_cons, true_or, if_true]
          exact Store.set_eq _ _ _
        · simp only [hr, if_false, List.mem_cons, e, false_or]
          exact Store.set_ne _ _ _ _ (sys_key_ne e)

theorem run_parentAllocs_ne (s : Store (sysLayout TxId D)) (rows : List (CellId × CellId))
    (a : Address (sysLayout TxId D)) (ha : a.1 ≠ SysSpace.parent) :
    Patch.run s (rows.map (fun row => Op.allocate (L := sysLayout TxId D) SysSpace.parent row.1 row.2)) a =
      s a := by
  induction rows generalizing s with
  | nil => rfl
  | cons row rest ih =>
      show Patch.run (s.set ⟨SysSpace.parent, row.1⟩ (some row.2)) _ a = s a
      rw [ih]
      exact Store.set_ne _ _ _ _ (fun e => ha (congrArg Sigma.fst e))

theorem run_parentAllocs_other (s : Store (sysLayout TxId D)) (rows : List (CellId × CellId))
    (c : CellId) (hc : c ∉ rows.map Prod.fst) :
    Patch.run s (rows.map (fun row => Op.allocate (L := sysLayout TxId D) SysSpace.parent row.1 row.2))
        ⟨SysSpace.parent, c⟩ = s ⟨SysSpace.parent, c⟩ := by
  induction rows generalizing s with
  | nil => rfl
  | cons row rest ih =>
      show Patch.run (s.set ⟨SysSpace.parent, row.1⟩ (some row.2)) _ _ = _
      simp only [List.map_cons, List.mem_cons, not_or] at hc
      rw [ih _ hc.2]
      exact Store.set_ne _ _ _ _ (sys_key_ne (Ne.symm (Ne.symm hc.1)))

theorem run_parentAllocs_mem (s : Store (sysLayout TxId D)) (rows : List (CellId × CellId))
    (nodup : (rows.map Prod.fst).Nodup) (c room : CellId) (m : (c, room) ∈ rows) :
    Patch.run s (rows.map (fun row => Op.allocate (L := sysLayout TxId D) SysSpace.parent row.1 row.2))
        ⟨SysSpace.parent, c⟩ = some room := by
  induction rows generalizing s with
  | nil => exact absurd m (by simp)
  | cons row rest ih =>
      show Patch.run (s.set ⟨SysSpace.parent, row.1⟩ (some row.2)) _ _ = _
      simp only [List.map_cons, List.nodup_cons] at nodup
      rcases List.mem_cons.mp m with e | m'
      · subst e
        rw [run_parentAllocs_other _ _ _ nodup.1]
        exact Store.set_eq _ _ _
      · exact ih _ nodup.2 m'

theorem parentRows_nodup (t : Turn R TxId Ev D) (nodup : (t.creates.map Prod.fst).Nodup) :
    (t.parentRows.map Prod.fst).Nodup := by
  unfold Turn.parentRows
  generalize t.creates = cs at nodup ⊢
  induction cs with
  | nil => simp
  | cons c rest ih =>
      obtain ⟨c0, k0, p0⟩ := c
      simp only [List.map_cons, List.nodup_cons] at nodup
      cases p0 with
      | none => simpa using ih nodup.2
      | some room =>
          simp only [List.filterMap_cons, Option.map_some, List.map_cons, List.nodup_cons]
          refine ⟨fun member => nodup.1 ?_, ih nodup.2⟩
          obtain ⟨row, rowMember, rfl⟩ := List.mem_map.mp member
          obtain ⟨c, cMember, hc⟩ := List.mem_filterMap.mp rowMember
          obtain ⟨r, _, rfl⟩ := Option.map_eq_some_iff.mp hc
          exact List.mem_map_of_mem cMember

theorem mem_parentRows {t : Turn R TxId Ev D} {c : CellId} {k : R.Kind} {room : CellId}
    (m : (c, k, some room) ∈ t.creates) : (c, room) ∈ t.parentRows :=
  List.mem_filterMap.mpr ⟨(c, k, some room), m, rfl⟩

/-! ### The T1 tail: spent marks and the meter debit -/

theorem run_spentAllocs_ne (s : Store (sysLayout TxId D)) (ns : List D)
    (a : Address (sysLayout TxId D)) (ha : a.1 ≠ SysSpace.spent) :
    Patch.run s (spentAllocs ns) a = s a := by
  induction ns generalizing s with
  | nil => rfl
  | cons n rest ih =>
      show Patch.run (s.set ⟨SysSpace.spent, n⟩ (some ())) (spentAllocs rest) a = s a
      rw [ih]
      exact Store.set_ne _ _ _ _ (fun e => ha (congrArg Sigma.fst e))

theorem run_spentAllocs_at (s : Store (sysLayout TxId D)) (ns : List D) (n : D) :
    Patch.run s (spentAllocs ns) ⟨SysSpace.spent, n⟩ =
      if n ∈ ns then some () else s ⟨SysSpace.spent, n⟩ := by
  induction ns generalizing s with
  | nil => simp only [List.not_mem_nil, if_false]; rfl
  | cons n0 rest ih =>
      show Patch.run (s.set ⟨SysSpace.spent, n0⟩ (some ())) (spentAllocs rest) _ = _
      rw [ih]
      by_cases hr : n ∈ rest
      · simp [hr]
      · by_cases e : n = n0
        · subst e
          simp only [hr, if_false, List.mem_cons, true_or, if_true]
          exact Store.set_eq _ _ _
        · simp only [hr, if_false, List.mem_cons, e, false_or]
          exact Store.set_ne _ _ _ _ (sys_key_ne e)

/-- The spent marks are valid exactly when the nullifiers are distinct and
none is already spent. -/
theorem validFrom_spentAllocs (s : Store (sysLayout TxId D)) (ns : List D) :
    Patch.ValidFrom s (spentAllocs ns) ↔ ns.Nodup ∧ ∀ n ∈ ns, s ⟨SysSpace.spent, n⟩ = none := by
  induction ns generalizing s with
  | nil => exact ⟨fun _ => ⟨List.nodup_nil, by simp⟩, fun _ => trivial⟩
  | cons n rest ih =>
      show (Op.Enabled s (Op.allocate (L := sysLayout TxId D) SysSpace.spent n ()) ∧
        Patch.ValidFrom (s.set ⟨SysSpace.spent, n⟩ (some ())) (spentAllocs rest)) ↔ _
      rw [ih]
      simp only [Op.Enabled, Store.Fresh, List.nodup_cons, List.mem_cons, forall_eq_or_imp]
      constructor
      · rintro ⟨⟨_, fresh⟩, nd, rest_fresh⟩
        refine ⟨⟨fun m => ?_, nd⟩, fresh, fun x mx => ?_⟩
        · have := rest_fresh n m
          rw [Store.set_eq] at this
          cases this
        · have := rest_fresh x mx
          by_cases e : x = n
          · subst e; rw [Store.set_eq] at this; cases this
          · rwa [Store.set_ne _ _ _ _ (sys_key_ne e)] at this
      · rintro ⟨⟨notin, nd⟩, fresh, rest_fresh⟩
        refine ⟨⟨fun e => Discipline.noConfusion e, fresh⟩, nd, fun x mx => ?_⟩
        have e : x ≠ n := fun e => notin (e ▸ mx)
        rw [Store.set_ne _ _ _ _ (sys_key_ne e)]
        exact rest_fresh x mx

theorem run_debits_ne (s : Store (sysLayout TxId D)) (lanes : List Lane) (charge avail : Charge)
    (a : Address (sysLayout TxId D)) (ha : a.1 ≠ SysSpace.allowance) :
    Patch.run s (debits lanes charge avail) a = s a := by
  induction lanes generalizing s with
  | nil => rfl
  | cons l rest ih =>
      show Patch.run (s.set ⟨SysSpace.allowance, l⟩ (some (avail l - charge l)))
        (debits rest charge avail) a = s a
      rw [ih]
      exact Store.set_ne _ _ _ _ (fun e => ha (congrArg Sigma.fst e))

theorem run_debits_at (s : Store (sysLayout TxId D)) (lanes : List Lane) (charge avail : Charge)
    (l : Lane) :
    Patch.run s (debits lanes charge avail) ⟨SysSpace.allowance, l⟩ =
      if l ∈ lanes then some (avail l - charge l) else s ⟨SysSpace.allowance, l⟩ := by
  induction lanes generalizing s with
  | nil => simp only [List.not_mem_nil, if_false]; rfl
  | cons l0 rest ih =>
      show Patch.run (s.set ⟨SysSpace.allowance, l0⟩ (some (avail l0 - charge l0)))
        (debits rest charge avail) _ = _
      rw [ih]
      by_cases hr : l ∈ rest
      · simp [hr]
      · by_cases e : l = l0
        · subst e
          simp only [hr, if_false, List.mem_cons, true_or, if_true]
          exact Store.set_eq _ _ _
        · simp only [hr, if_false, List.mem_cons, e, false_or]
          exact Store.set_ne _ _ _ _ (sys_key_ne e)

/-- The meter debit over distinct lanes is valid exactly when each lane holds
the quoted allowance. -/
theorem validFrom_debits (s : Store (sysLayout TxId D)) (lanes : List Lane) (charge avail : Charge)
    (nodup : lanes.Nodup) :
    Patch.ValidFrom s (debits lanes charge avail) ↔
      ∀ l ∈ lanes, s ⟨SysSpace.allowance, l⟩ = some (avail l) := by
  induction lanes generalizing s with
  | nil => exact ⟨fun _ _ m => absurd m (by simp), fun _ => trivial⟩
  | cons l rest ih =>
      simp only [List.nodup_cons] at nodup
      show (Op.Enabled s (Op.write (L := sysLayout TxId D) SysSpace.allowance l (avail l)
          (avail l - charge l)) ∧
        Patch.ValidFrom (s.set ⟨SysSpace.allowance, l⟩ (some (avail l - charge l)))
          (debits rest charge avail)) ↔ _
      rw [ih _ nodup.2]
      simp only [Op.Enabled, List.mem_cons, forall_eq_or_imp]
      have frame : ∀ x ∈ rest, (s.set ⟨SysSpace.allowance, l⟩ (some (avail l - charge l)))
          ⟨SysSpace.allowance, x⟩ = s ⟨SysSpace.allowance, x⟩ := fun x mx =>
        Store.set_ne _ _ _ _ (sys_key_ne (fun e => nodup.1 (e ▸ mx)))
      constructor
      · rintro ⟨⟨_, here⟩, rest_ok⟩
        exact ⟨here, fun x mx => (frame x mx) ▸ rest_ok x mx⟩
      · rintro ⟨here, rest_ok⟩
        exact ⟨⟨rfl, here⟩, fun x mx => (frame x mx).symm ▸ rest_ok x mx⟩

theorem meterLanes_nodup : (meterLanes : List Lane).Nodup := by decide

theorem mem_meterLanes (l : Lane) : l ∈ meterLanes := by cases l <;> decide

theorem mem_chargedLanes {charge : Charge} {l : Lane} : l ∈ chargedLanes charge ↔ charge l ≠ 0 := by
  simp [chargedLanes, mem_meterLanes]

theorem chargedLanes_nodup (charge : Charge) : (chargedLanes charge).Nodup :=
  meterLanes_nodup.filter _

/-- Off the T1 namespaces, the system patch is its core. -/
theorem run_sysPatch_core (s : Store (sysLayout TxId D)) (t : Turn R TxId Ev D)
    (height : Nat) (logRoot : D) (avail : Charge) (a : Address (sysLayout TxId D))
    (hs : a.1 ≠ SysSpace.spent) (ha : a.1 ≠ SysSpace.allowance) :
    Patch.run s (sysPatch H t height logRoot avail) a = Patch.run s (sysCore H t height logRoot) a := by
  simp only [sysPatch, Patch.run_append]
  rw [run_debits_ne _ _ _ _ _ ha, run_spentAllocs_ne _ _ _ hs]

/-- The system patch's validity, block by block. -/
theorem validFrom_sysPatch (s : Store (sysLayout TxId D)) (t : Turn R TxId Ev D)
    (height : Nat) (logRoot : D) (avail : Charge) :
    Patch.ValidFrom s (sysPatch H t height logRoot avail) ↔
      Patch.ValidFrom s (sysCore H t height logRoot) ∧
        Patch.ValidFrom (Patch.run s (sysCore H t height logRoot)) (spentAllocs t.nullifiers) ∧
        Patch.ValidFrom (Patch.run (Patch.run s (sysCore H t height logRoot))
          (spentAllocs t.nullifiers)) (debits (chargedLanes t.charge) t.charge avail) := by
  simp only [sysPatch, Patch.validFrom_append, Patch.run_append, and_assoc]

/-- The core never touches the spent marks. -/
theorem run_sysCore_spent (s : Store (sysLayout TxId D)) (t : Turn R TxId Ev D)
    (height : Nat) (logRoot : D) (n : D) :
    Patch.run s (sysCore H t height logRoot) ⟨SysSpace.spent, n⟩ = s ⟨SysSpace.spent, n⟩ := by
  simp only [sysCore, Patch.run_append, run_createReads, Patch.run_cons, Patch.run_nil]
  rw [run_parentAllocs_ne _ _ _ (fun e => SysSpace.noConfusion e)]
  rw [op_apply_write, Store.set_ne _ _ _ _ (sys_space_ne (by decide)), op_apply_allocate]
  rw [run_retireAllocs_ne _ _ _ (fun e => SysSpace.noConfusion e)]
  exact Store.set_ne _ _ _ _ (sys_space_ne (by decide))

/-- The core never touches the meter. -/
theorem run_sysCore_allowance (s : Store (sysLayout TxId D)) (t : Turn R TxId Ev D)
    (height : Nat) (logRoot : D) (l : Lane) :
    Patch.run s (sysCore H t height logRoot) ⟨SysSpace.allowance, l⟩ =
      s ⟨SysSpace.allowance, l⟩ := by
  simp only [sysCore, Patch.run_append, run_createReads, Patch.run_cons, Patch.run_nil]
  rw [run_parentAllocs_ne _ _ _ (fun e => SysSpace.noConfusion e)]
  rw [op_apply_write, Store.set_ne _ _ _ _ (sys_space_ne (by decide)), op_apply_allocate]
  rw [run_retireAllocs_ne _ _ _ (fun e => SysSpace.noConfusion e)]
  exact Store.set_ne _ _ _ _ (sys_space_ne (by decide))

/-- **The spent marks after a turn**: the old ones plus the turn's. -/
theorem sysPost_spent (s : Store (sysLayout TxId D)) (t : Turn R TxId Ev D)
    (height : Nat) (logRoot : D) (avail : Charge) (n : D) :
    Patch.run s (sysPatch H t height logRoot avail) ⟨SysSpace.spent, n⟩ =
      if n ∈ t.nullifiers then some () else s ⟨SysSpace.spent, n⟩ := by
  simp only [sysPatch, Patch.run_append]
  rw [run_debits_ne _ _ _ _ _ (fun e => SysSpace.noConfusion e), run_spentAllocs_at,
    run_sysCore_spent]

/-- **The meter after a turn**: each charged lane is debited from `avail`. -/
theorem sysPost_allowance (s : Store (sysLayout TxId D)) (t : Turn R TxId Ev D)
    (height : Nat) (logRoot : D) (avail : Charge) (l : Lane) :
    Patch.run s (sysPatch H t height logRoot avail) ⟨SysSpace.allowance, l⟩ =
      if t.charge l ≠ 0 then some (avail l - t.charge l) else s ⟨SysSpace.allowance, l⟩ := by
  simp only [sysPatch, Patch.run_append]
  rw [run_debits_at]
  by_cases hl : t.charge l ≠ 0
  · rw [if_pos (mem_chargedLanes.mpr hl), if_pos hl]
  · rw [if_neg (fun m => hl (mem_chargedLanes.mp m)), if_neg hl,
      run_spentAllocs_ne _ _ _ (fun e => SysSpace.noConfusion e), run_sysCore_allowance]

theorem sysPost_parent (s : Store (sysLayout TxId D)) (t : Turn R TxId Ev D)
    (height : Nat) (logRoot : D) (avail : Charge) (nodup : (t.creates.map Prod.fst).Nodup)
    {c : CellId} {k : R.Kind} {room : CellId} (m : (c, k, some room) ∈ t.creates) :
    Patch.run s (sysPatch H t height logRoot avail) ⟨SysSpace.parent, c⟩ = some room := by
  rw [run_sysPatch_core H _ _ _ _ _ _ (fun e => SysSpace.noConfusion e)
    (fun e => SysSpace.noConfusion e)]
  simp only [sysCore, Patch.run_append]
  exact run_parentAllocs_mem _ _ (parentRows_nodup t nodup) c room (mem_parentRows m)

theorem sysPost_journal (s : Store (sysLayout TxId D)) (t : Turn R TxId Ev D)
    (height : Nat) (logRoot : D) (avail : Charge) (x : TxId) :
    Patch.run s (sysPatch H t height logRoot avail) ⟨SysSpace.journal, x⟩ =
      if x = t.txId then some (height, H.turnDigest t) else s ⟨SysSpace.journal, x⟩ := by
  rw [run_sysPatch_core H _ _ _ _ _ _ (fun e => SysSpace.noConfusion e)
    (fun e => SysSpace.noConfusion e)]
  simp only [sysCore, Patch.run_append, run_createReads, Patch.run_cons, Patch.run_nil]
  rw [run_parentAllocs_ne _ _ _ (fun e => SysSpace.noConfusion e)]
  rw [op_apply_write, Store.set_ne _ _ _ _ (sys_space_ne (by decide)), op_apply_allocate]
  rw [run_retireAllocs_ne _ _ _ (fun e => SysSpace.noConfusion e)]
  by_cases e : x = t.txId
  · subst e; rw [if_pos rfl]; exact Store.set_eq _ _ _
  · rw [if_neg e]; exact Store.set_ne _ _ _ _ (sys_key_ne e)

theorem sysPost_head (s : Store (sysLayout TxId D)) (t : Turn R TxId Ev D)
    (height : Nat) (logRoot : D) (avail : Charge) :
    Patch.run s (sysPatch H t height logRoot avail) ⟨SysSpace.head, ()⟩ =
      some (height + 1, H.chain logRoot (H.turnDigest t)) := by
  rw [run_sysPatch_core H _ _ _ _ _ _ (fun e => SysSpace.noConfusion e)
    (fun e => SysSpace.noConfusion e)]
  simp only [sysCore, Patch.run_append, run_createReads, Patch.run_cons, Patch.run_nil]
  rw [run_parentAllocs_ne _ _ _ (fun e => SysSpace.noConfusion e)]
  exact Store.set_eq _ _ _

theorem sysPost_retired (s : Store (sysLayout TxId D)) (t : Turn R TxId Ev D)
    (height : Nat) (logRoot : D) (avail : Charge) (c : CellId) :
    Patch.run s (sysPatch H t height logRoot avail) ⟨SysSpace.retired, c⟩ =
      if c ∈ t.retires then some () else s ⟨SysSpace.retired, c⟩ := by
  rw [run_sysPatch_core H _ _ _ _ _ _ (fun e => SysSpace.noConfusion e)
    (fun e => SysSpace.noConfusion e)]
  simp only [sysCore, Patch.run_append, run_createReads, Patch.run_cons, Patch.run_nil]
  rw [run_parentAllocs_ne _ _ _ (fun e => SysSpace.noConfusion e)]
  rw [op_apply_write, Store.set_ne _ _ _ _ (sys_space_ne (by decide)), op_apply_allocate]
  rw [run_retireAllocs_at]
  by_cases hr : c ∈ t.retires
  · simp [hr]
  · simp only [hr, if_false]
    exact Store.set_ne _ _ _ _ (sys_space_ne (by decide))

theorem sysPatch_valid_creates {s : Store (sysLayout TxId D)} {t : Turn R TxId Ev D}
    {height : Nat} {logRoot : D} {avail : Charge}
    (hv : Patch.ValidFrom s (sysPatch H t height logRoot avail)) :
    ∀ c ∈ t.creates, s ⟨SysSpace.retired, c.1⟩ = none := by
  replace hv := ((validFrom_sysPatch H s t height logRoot avail).1 hv).1
  unfold sysCore at hv
  simp only [List.append_assoc] at hv
  rw [Patch.validFrom_append] at hv
  exact (validFrom_createReads s t.creates).1 hv.1

/-- The system patch of a turn with no creates or retires is valid exactly
when the id is fresh and the head is where the patch quotes it. -/
theorem sysPatch_valid_plain {s : Store (sysLayout TxId D)} {t : Turn R TxId Ev D}
    {height : Nat} {logRoot : D} {avail : Charge} (hc : t.creates = []) (hr : t.retires = [])
    (hj : s ⟨SysSpace.journal, t.txId⟩ = none)
    (hh : s ⟨SysSpace.head, ()⟩ = some (height, logRoot))
    (hn : t.nullifiers.Nodup ∧ ∀ n ∈ t.nullifiers, s ⟨SysSpace.spent, n⟩ = none)
    (hm : ∀ l, t.charge l ≠ 0 → s ⟨SysSpace.allowance, l⟩ = some (avail l)) :
    Patch.ValidFrom s (sysPatch H t height logRoot avail) := by
  rw [validFrom_sysPatch]
  refine ⟨?_, ?_, ?_⟩
  · simp only [sysCore, Turn.parentRows, hc, hr, List.map_nil, List.nil_append,
      List.filterMap_nil, List.append_nil]
    refine ⟨⟨fun e => Discipline.noConfusion e, hj⟩, ⟨rfl, ?_⟩, trivial⟩
    show (s.set ⟨SysSpace.journal, t.txId⟩ (some (height, H.turnDigest t))) ⟨SysSpace.head, ()⟩ = _
    rw [Store.set_ne _ _ _ _ (sys_space_ne (fun e => SysSpace.noConfusion e)), hh]
    rfl
  · rw [validFrom_spentAllocs]
    exact ⟨hn.1, fun n m => (run_sysCore_spent H s t height logRoot n).trans (hn.2 n m)⟩
  · rw [validFrom_debits _ _ _ _ (chargedLanes_nodup _)]
    intro l m
    rw [run_spentAllocs_ne _ _ _ (fun e => SysSpace.noConfusion e), run_sysCore_allowance]
    exact hm l (mem_chargedLanes.mp m)

end Decompose

/-! ## `step`: frame, per-leg exactness, creates, retires, invariant (§4.2, §4.7) -/

section StepLaws

variable {R : Registry} {TxId Ev D : Type} [DecidableEq TxId] [DecidableEq D]
variable (H : History R TxId Ev D)

/-- **Frame through `step` (§4.2).**  A cell a turn neither creates, writes,
nor retires is unchanged. -/
theorem step_frame {w w' : World R TxId D} {t : Turn R TxId Ev D}
    (h : World.step H w t = some w') (x : CellId)
    (hc : x ∉ t.creates.map Prod.fst) (hl : x ∉ t.legs.map Leg.cell) (hr : x ∉ t.retires) :
    w'.cells x = w.cells x := by
  obtain ⟨_, _, _, _, _, _, hcells, _⟩ := admit_ok H ((step_eq_some H).1 h)
  obtain ⟨c1, c2, h1, h2, h3⟩ := applyCells_ok hcells
  rw [applyRetires_frame h3 x hr, applyLegs_frame h2 x hl, applyCreates_frame h1 x hc]

/-- **Per-leg exactness through `step`.**  A leg on an existing cell (not
created or retired by the same turn) was valid from the store the cell held in
the pre-world, and the cell ends holding `run pre patch`.  There is no
caller-supplied post. -/
theorem step_leg {w w' : World R TxId D} {t : Turn R TxId Ev D}
    (h : World.step H w t = some w') (leg : Leg R) (m : leg ∈ t.legs)
    (hc : leg.cell ∉ t.creates.map Prod.fst) (hr : leg.cell ∉ t.retires) :
    ∃ pre, (w.cells leg.cell).bind (·.storeAt leg.kind) = some pre ∧
      Patch.ValidFrom pre leg.patch ∧
      w'.cells leg.cell = some ⟨leg.kind, Patch.run pre leg.patch⟩ := by
  obtain ⟨⟨_, hnd, _, _⟩, _, _, _, _, _, hcells, _⟩ := admit_ok H ((step_eq_some H).1 h)
  obtain ⟨c1, c2, h1, h2, h3⟩ := applyCells_ok hcells
  obtain ⟨pre, hpre, hv, hpost⟩ := applyLegs_mem h2 hnd leg m
  rw [applyCreates_frame h1 _ hc] at hpre
  exact ⟨pre, hpre, hv, by rw [applyRetires_frame h3 _ hr, hpost]⟩

/-- A create is at an absent, never-retired id. -/
theorem step_create {w w' : World R TxId D} {t : Turn R TxId Ev D}
    (h : World.step H w t = some w') (c : CellId) (k : R.Kind) (p : Option CellId)
    (m : (c, k, p) ∈ t.creates)
    (hl : c ∉ t.legs.map Leg.cell) (hr : c ∉ t.retires) :
    w.cells c = none ∧ w.retired c = none ∧ w'.cells c = some ⟨k, 0⟩ := by
  obtain ⟨⟨_, _, hnd, _⟩, _, _, _, _, hv, hcells, _⟩ := admit_ok H ((step_eq_some H).1 h)
  obtain ⟨c1, c2, h1, h2, h3⟩ := applyCells_ok hcells
  obtain ⟨hnone, hpost⟩ := applyCreates_mem h1 hnd c k p m
  refine ⟨hnone, sysPatch_valid_creates H hv (c, k, p) m, ?_⟩
  rw [applyRetires_frame h3 c hr, applyLegs_frame h2 c hl, hpost]

/-- A retire removes the cell and marks its id retired. -/
theorem step_retire {w w' : World R TxId D} {t : Turn R TxId Ev D}
    (h : World.step H w t = some w') (c : CellId) (m : c ∈ t.retires) :
    w'.cells c = none ∧ w'.retired c = some () := by
  obtain ⟨⟨_, _, _, hnd⟩, height, logRoot, _, _, _, hcells, hsys⟩ :=
    admit_ok H ((step_eq_some H).1 h)
  obtain ⟨c1, c2, h1, h2, h3⟩ := applyCells_ok hcells
  refine ⟨(applyRetires_mem h3 hnd c m).2, ?_⟩
  show w'.system _ = _
  rw [hsys, sysPost_retired, if_pos m]

/-- **The invariant is carried.**  `step` preserves "present cells are never
retired": a present post cell was present before or created at a
read-guarded never-retired id, and retired ids are exactly the old ones plus
this turn's retires, which are absent after it. -/
theorem step_wf {w w' : World R TxId D} {t : Turn R TxId Ev D}
    (hwf : w.WF) (h : World.step H w t = some w') : w'.WF := by
  obtain ⟨⟨_, _, _, hnd⟩, height, logRoot, _, _, hv, hcells, hsys⟩ :=
    admit_ok H ((step_eq_some H).1 h)
  obtain ⟨c1, c2, h1, h2, h3⟩ := applyCells_ok hcells
  intro c hc
  have hret : w'.retired c = if c ∈ t.retires then some () else w.retired c := by
    show w'.system _ = _
    rw [hsys, sysPost_retired]; rfl
  by_cases m : c ∈ t.retires
  · exact absurd (applyRetires_mem h3 hnd c m).2 hc
  rw [hret, if_neg m]
  have p2 := applyRetires_present h3 c hc
  have p1 := applyLegs_present h2 c p2
  rcases applyCreates_present h1 c p1 with p0 | mc
  · exact hwf c p0
  · obtain ⟨⟨c', k, p⟩, mem, rfl⟩ := List.mem_map.mp mc
    exact sysPatch_valid_creates H hv (c', k, p) mem

/-- **`birth_parent_recorded` (world).**  A create born in a room records the
room in the system cell's `parent` rows, in the same accepted turn. -/
theorem step_parent_recorded {w w' : World R TxId D} {t : Turn R TxId Ev D}
    (h : World.step H w t = some w') {c : CellId} {k : R.Kind} {room : CellId}
    (m : (c, k, some room) ∈ t.creates) : w'.parent c = some room := by
  obtain ⟨⟨_, _, hnd, _⟩, height, logRoot, _, _, _, _, hsys⟩ := admit_ok H ((step_eq_some H).1 h)
  show w'.system _ = _
  rw [hsys]
  exact sysPost_parent H _ t height logRoot _ hnd m

/-- **`birth_parent_must_exist` (world).**  A create's room was a present cell
when the create ran: present before the turn, or created earlier in it. -/
theorem step_parent_exists {w w' : World R TxId D} {t : Turn R TxId Ev D}
    (h : World.step H w t = some w') {c : CellId} {k : R.Kind} {room : CellId}
    (m : (c, k, some room) ∈ t.creates) :
    w.cells room ≠ none ∨ room ∈ t.creates.map Prod.fst := by
  obtain ⟨_, _, _, _, _, _, hcells, _⟩ := admit_ok H ((step_eq_some H).1 h)
  obtain ⟨c1, c2, h1, _, _⟩ := applyCells_ok hcells
  exact applyCreates_room h1 c k room m

/-- Parent rows are never rewritten or removed by an accepted turn. -/
theorem step_parent_stable {w w' : World R TxId D} {t : Turn R TxId Ev D}
    (h : World.step H w t = some w') {c room : CellId} (recorded : w.parent c = some room) :
    w'.parent c = some room := by
  obtain ⟨_, height, logRoot, _, _, hv, _, hsys⟩ := admit_ok H ((step_eq_some H).1 h)
  show w'.system _ = _
  rw [hsys]
  exact Patch.appendOnly_present_preserved _ _ ⟨SysSpace.parent, c⟩ room hv rfl
    (show w.system ⟨SysSpace.parent, c⟩ = some room from recorded)

/-- **`narrows_stable` over the world.**  A delegation's narrowing checked at
one world's parentage stays a narrowing at every world an accepted turn
reaches from it. -/
theorem step_narrows_stable {w w' : World R TxId D} {t : Turn R TxId Ev D}
    (h : World.step H w t = some w') {kind : Theory.TypedAuthorization.ResourceKind}
    {child parent : Theory.TypedAuthorization.Scope kind}
    (narrows : child.Narrows parent w.parentage) : child.Narrows parent w'.parentage :=
  ⟨Theory.TypedAuthorization.TargetSet.narrows_mono (fun _ _ recorded => step_parent_stable H h recorded)
    narrows.targets, narrows.verbs, narrows.maxCost, narrows.fields, narrows.maxDelta⟩

/-- Accepted turns carry the invariant along the whole log. -/
theorem fold_wf {g W : World R TxId D} {log : List (Turn R TxId Ev D)}
    (hg : g.WF) (h : fold H g log = some W) : W.WF := by
  induction log using List.reverseRecOn generalizing W with
  | nil => simp only [fold_nil, Option.some.injEq] at h; subst h; exact hg
  | append_singleton l t ih =>
      rw [fold_snoc] at h
      cases hl : fold H g l with
      | none => rw [hl] at h; cases h
      | some w => rw [hl] at h; exact step_wf H (ih hl) h

/-- `genesis` is a genesis world: height zero at the initial log root and an
empty journal, so `journal_exact` and `fold_head` apply from it. -/
theorem genesis_is_Genesis (cells : Cells R) : Genesis H (genesis H cells : World R TxId D) := by
  refine ⟨Store.set_eq _ _ _, fun x => ?_⟩
  show (genesisSystem H : Store (sysLayout TxId D)) ⟨SysSpace.journal, x⟩ = none
  unfold genesisSystem
  rw [Store.set_ne _ _ _ _ (sys_space_ne (fun e => SysSpace.noConfusion e))]
  rfl

/-- A genesis world has no retired ids, so it satisfies the invariant. -/
theorem genesis_wf (cells : Cells R) : (genesis H cells : World R TxId D).WF := by
  intro c _
  show (genesisSystem H : Store (sysLayout TxId D)) ⟨SysSpace.retired, c⟩ = none
  unfold genesisSystem
  rw [Store.set_ne _ _ _ _ (sys_space_ne (fun e => SysSpace.noConfusion e))]
  rfl

end StepLaws

/-! ## Height, log chain, and journal exactness (§4.9, §4.13) -/

section Journal

variable {R : Registry} {TxId Ev D : Type} [DecidableEq TxId] [DecidableEq D]
variable (H : History R TxId Ev D)

theorem step_head {w w' : World R TxId D} {t : Turn R TxId Ev D}
    (h : World.step H w t = some w') :
    ∃ height logRoot, w.head = some (height, logRoot) ∧
      w'.head = some (height + 1, H.chain logRoot (H.turnDigest t)) := by
  obtain ⟨_, height, logRoot, hh, _, _, _, hsys⟩ := admit_ok H ((step_eq_some H).1 h)
  exact ⟨height, logRoot, hh, by show w'.system _ = _; rw [hsys, sysPost_head]⟩

/-- **Monotone height, chained log root (§4.13).**  After a log, the head is
the starting height plus the log's length, at the log chain of the turns. -/
theorem fold_head {g W : World R TxId D} {log : List (Turn R TxId Ev D)}
    {h0 : Nat} {r0 : D} (hg : g.head = some (h0, r0)) (h : fold H g log = some W) :
    W.head = some (h0 + log.length, logChain H r0 log) := by
  induction log using List.reverseRecOn generalizing W with
  | nil => simp only [fold_nil, Option.some.injEq] at h; subst h; simpa [logChain] using hg
  | append_singleton l t ih =>
      rw [fold_snoc] at h
      cases hl : fold H g l with
      | none => rw [hl] at h; cases h
      | some w =>
          rw [hl] at h
          obtain ⟨height, logRoot, hh, hh'⟩ := step_head H h
          rw [ih hl, Option.some.injEq, Prod.mk.injEq] at hh
          obtain ⟨rfl, rfl⟩ := hh
          rw [hh']
          simp [logChain, List.foldl_append, Nat.add_assoc]

theorem step_journal {w w' : World R TxId D} {t : Turn R TxId Ev D}
    (h : World.step H w t = some w') :
    ∃ height logRoot, w.head = some (height, logRoot) ∧ w.journal t.txId = none ∧
      ∀ x, w'.journal x =
        if x = t.txId then some (height, H.turnDigest t) else w.journal x := by
  obtain ⟨_, height, logRoot, hh, hj, _, _, hsys⟩ := admit_ok H ((step_eq_some H).1 h)
  refine ⟨height, logRoot, hh, hj, fun x => ?_⟩
  show w'.system _ = _
  rw [hsys, sysPost_journal]; rfl

private theorem getElem?_snoc {α : Type} (l : List α) (t : α) (i : Nat) :
    (l ++ [t])[i]? = if i < l.length then l[i]? else if i = l.length then some t else none := by
  by_cases h1 : i < l.length
  · rw [if_pos h1, List.getElem?_append_left h1]
  · rw [if_neg h1, List.getElem?_append_right (by omega)]
    by_cases h2 : i = l.length
    · subst h2; simp
    · rw [if_neg h2]
      have : 1 ≤ i - l.length := by omega
      simp only [List.getElem?_eq_none_iff, List.length_singleton]
      omega

/-- **Journal exactness (§4.9).**  From a genesis world, the journal entry of
a transaction id is `(h, H turn)` exactly when the log's turn at height `h`
carries that id.  In particular the journal is the index of the log, and a
transaction id occurs at most once in an accepted log. -/
theorem journal_exact {g W : World R TxId D} {log : List (Turn R TxId Ev D)}
    (hg : Genesis H g) (hf : fold H g log = some W) (x : TxId) (i : Nat) (d : D) :
    W.journal x = some (i, d) ↔
      ∃ t, log[i]? = some t ∧ t.txId = x ∧ d = H.turnDigest t := by
  induction log using List.reverseRecOn generalizing W with
  | nil =>
      simp only [fold_nil, Option.some.injEq] at hf
      subst hf
      simp [hg.2 x]
  | append_singleton l t ih =>
      rw [fold_snoc] at hf
      cases hl : fold H g l with
      | none => rw [hl] at hf; cases hf
      | some w =>
          rw [hl] at hf
          obtain ⟨height, logRoot, hh, hj, hpost⟩ := step_journal H hf
          have hheight : height = l.length := by
            have := fold_head H hg.1 hl
            rw [hh, Option.some.injEq, Prod.mk.injEq] at this
            omega
          subst hheight
          rw [hpost x, getElem?_snoc]
          by_cases hx : x = t.txId
          · subst hx
            rw [if_pos rfl]
            constructor
            · intro e
              simp only [Option.some.injEq, Prod.mk.injEq] at e
              obtain ⟨rfl, rfl⟩ := e
              exact ⟨t, by simp, rfl, rfl⟩
            · rintro ⟨t', ht', hid, rfl⟩
              by_cases hi : i < l.length
              · rw [if_pos hi] at ht'
                have := (ih hl).2 ⟨t', ht', hid, rfl⟩
                rw [hj] at this
                cases this
              · rw [if_neg hi] at ht'
                by_cases hi' : i = l.length
                · rw [if_pos hi'] at ht'
                  cases ht'
                  subst hi'
                  rfl
                · rw [if_neg hi'] at ht'; cases ht'
          · rw [if_neg hx, ih hl]
            constructor
            · rintro ⟨t', ht', hid, rfl⟩
              have hi : i < l.length := (List.getElem?_eq_some_iff.mp ht').1
              exact ⟨t', by rw [if_pos hi]; exact ht', hid, rfl⟩
            · rintro ⟨t', ht', hid, rfl⟩
              by_cases hi : i < l.length
              · rw [if_pos hi] at ht'; exact ⟨t', ht', hid, rfl⟩
              · rw [if_neg hi] at ht'
                by_cases hi' : i = l.length
                · rw [if_pos hi'] at ht'
                  cases ht'
                  exact absurd hid.symm hx
                · rw [if_neg hi'] at ht'; cases ht'

/-- The DATAMODEL §4.9 form: the journal's height for an id is the log
position carrying it. -/
theorem journal_height_iff {g W : World R TxId D} {log : List (Turn R TxId Ev D)}
    (hg : Genesis H g) (hf : fold H g log = some W) (x : TxId) (i : Nat) :
    (W.journal x).map Prod.fst = some i ↔ (log[i]?).map Turn.txId = some x := by
  constructor
  · intro e
    obtain ⟨⟨i', d⟩, hj, rfl⟩ := Option.map_eq_some_iff.mp e
    obtain ⟨t, ht, hid, _⟩ := (journal_exact H hg hf x i' d).1 hj
    simp [ht, hid]
  · intro e
    obtain ⟨t, ht, hid⟩ := Option.map_eq_some_iff.mp e
    rw [(journal_exact H hg hf x i (H.turnDigest t)).2 ⟨t, ht, hid, rfl⟩]
    rfl

/-- Replay detection: an accepted log never carries one transaction id at two
heights. -/
theorem fold_txId_unique {g W : World R TxId D} {log : List (Turn R TxId Ev D)}
    (hg : Genesis H g) (hf : fold H g log = some W) {i j : Nat} {ti tj : Turn R TxId Ev D}
    (hi : log[i]? = some ti) (hj : log[j]? = some tj) (same : ti.txId = tj.txId) : i = j := by
  have ei := (journal_exact H hg hf ti.txId i (H.turnDigest ti)).2 ⟨ti, hi, rfl, rfl⟩
  have ej := (journal_exact H hg hf ti.txId j (H.turnDigest tj)).2 ⟨tj, hj, same.symm, rfl⟩
  rw [ei, Option.some.injEq, Prod.mk.injEq] at ej
  exact ej.1

/-! ### Retry, restated as journal exactness -/

/-- What a resubmission of a turn meets: a fresh id, the recorded turn at a
height (same digest), or a different turn under the same id. -/
inductive Resubmission
  | fresh
  | replay (height : Nat)
  | conflict (height : Nat)
  deriving DecidableEq, Repr

/-- Classify a resubmission by the journal alone. -/
def classify (w : World R TxId D) (t : Turn R TxId Ev D) : Resubmission :=
  match w.journal t.txId with
  | none => .fresh
  | some (height, digest) => if digest = H.turnDigest t then .replay height else .conflict height

/-- **Retry never commits twice.**  Resubmitting an accepted turn at the
world it produced is refused as a replay. -/
theorem admit_retry_refused {w w' : World R TxId D} {t : Turn R TxId Ev D}
    (h : World.step H w t = some w') :
    World.admit H w' t = .error .replayedTransaction := by
  obtain ⟨⟨hE, hL, hC, hR⟩, height, logRoot, _, _, _, _, hsys⟩ :=
    admit_ok H ((step_eq_some H).1 h)
  have hj : (w'.journal t.txId).isSome := by
    show (w'.system _).isSome
    rw [hsys, sysPost_journal, if_pos rfl]; rfl
  have hh : w'.head = some (height + 1, H.chain logRoot (H.turnDigest t)) := by
    show w'.system _ = _
    rw [hsys, sysPost_head]
  unfold World.admit
  rw [if_neg hE, if_neg (not_not.mpr hL), if_neg (not_not.mpr hC), if_neg (not_not.mpr hR)]
  simp only [hh]
  rw [if_pos hj]

/-- **Retry exactness (§4.9, `execute_retry_after_install` restated).**  After
an accepted log, resubmitting the turn at height `i` is classified as a replay
of height `i`. -/
theorem classify_replay {g W : World R TxId D} {log : List (Turn R TxId Ev D)}
    (hg : Genesis H g) (hf : fold H g log = some W) {i : Nat} {t : Turn R TxId Ev D}
    (ht : log[i]? = some t) : classify H W t = .replay i := by
  unfold classify
  rw [(journal_exact H hg hf t.txId i (H.turnDigest t)).2 ⟨t, ht, rfl, rfl⟩]
  simp

/-- A different turn under a recorded id is a conflict, whenever the digest
separates the two turns (the digest's binding is the premise, refuted in
`Example.digest_collision_hides_conflict`). -/
theorem classify_conflict {g W : World R TxId D} {log : List (Turn R TxId Ev D)}
    (hg : Genesis H g) (hf : fold H g log = some W) {i : Nat} {t t' : Turn R TxId Ev D}
    (ht : log[i]? = some t) (same : t'.txId = t.txId)
    (separates : H.turnDigest t ≠ H.turnDigest t') : classify H W t' = .conflict i := by
  unfold classify
  rw [same, (journal_exact H hg hf t.txId i (H.turnDigest t)).2 ⟨t, ht, rfl, rfl⟩]
  simp [separates]

/-- An id the log never carried is fresh. -/
theorem classify_fresh {g W : World R TxId D} {log : List (Turn R TxId Ev D)}
    (hg : Genesis H g) (hf : fold H g log = some W) {t : Turn R TxId Ev D}
    (absent : ∀ t' ∈ log, t'.txId ≠ t.txId) : classify H W t = .fresh := by
  unfold classify
  cases hj : W.journal t.txId with
  | none => rfl
  | some p =>
      obtain ⟨i, d⟩ := p
      obtain ⟨t', ht', hid, _⟩ := (journal_exact H hg hf t.txId i d).1 hj
      exact absurd hid (absent t' (List.mem_of_getElem? ht'))

end Journal

/-! ## T1: spent markers, the meter, the clock pin, the footprint -/

section TurnLaws

variable {R : Registry} {TxId Ev D : Type} [DecidableEq TxId] [DecidableEq D]
variable (H : History R TxId Ev D)

/-- `turnCheck` passes exactly when every T1 condition holds. -/
theorem turnCheck_eq_none_iff {w : World R TxId D} {t : Turn R TxId Ev D} {height : Nat} :
    turnCheck H w t height = none ↔
      t.nullifiers.Nodup ∧
      (t.notBefore ≤ height ∧ (t.validUntil.all fun u => decide (height ≤ u)) = true) ∧
      (∀ n ∈ t.nullifiers, w.spent n = none) ∧
      t.charge .storageBytes = patchBytes H t ∧
      t.charge ≤ w.meter := by
  unfold turnCheck
  constructor
  · intro h
    split_ifs at h with h1 h2 h3 h4 h5 <;> try cases h
    refine ⟨h1, h2, fun n m => ?_, by simpa using h4, by simpa using h5⟩
    by_contra hne
    exact h3 ⟨n, m, Option.isSome_iff_ne_none.mpr hne⟩
  · rintro ⟨h1, h2, h3, h4, h5⟩
    have h3' : ¬ ∃ n ∈ t.nullifiers, (w.spent n).isSome := fun ⟨n, m, hs⟩ => by
      simp [h3 n m] at hs
    have h5' : Charge.fundedCheck t.charge w.meter = true :=
      (Charge.fundedCheck_eq_true_iff _ _).2 h5
    simp only [h1, h2, h3', h4, h5', not_true_eq_false, not_false_eq_true, and_self, if_false,
      ne_eq, reduceCtorEq]

/-- The meter, read off the system cell. -/
theorem meter_system {w : World R TxId D} (l : Lane) :
    w.meter l = Option.getD (α := Nat) (w.system ⟨SysSpace.allowance, l⟩) 0 := rfl

/-- **Spent markers only grow.**  A nullifier spent before a turn is spent
after it (the `spent` namespace is append-only). -/
theorem spent_monotone {w w' : World R TxId D} {t : Turn R TxId Ev D}
    (h : World.step H w t = some w') {n : D} (spent : w.spent n = some ()) :
    w'.spent n = some () := by
  obtain ⟨_, height, logRoot, _, _, hv, _, hsys⟩ := admit_ok H ((step_eq_some H).1 h)
  show w'.system _ = _
  rw [hsys]
  exact Patch.appendOnly_present_preserved _ _ ⟨SysSpace.spent, n⟩ () hv rfl
    (show w.system ⟨SysSpace.spent, n⟩ = some () from spent)

/-- Along a whole log. -/
theorem fold_spent_monotone {g W : World R TxId D} {log : List (Turn R TxId Ev D)}
    (h : fold H g log = some W) {n : D} (spent : g.spent n = some ()) : W.spent n = some () := by
  induction log using List.reverseRecOn generalizing W with
  | nil => simp only [fold_nil, Option.some.injEq] at h; subst h; exact spent
  | append_singleton l t ih =>
      rw [fold_snoc] at h
      cases hl : fold H g l with
      | none => rw [hl] at h; cases h
      | some w => rw [hl] at h; exact spent_monotone H h (ih hl)

/-- An accepted turn spends every nullifier it carries. -/
theorem step_spends {w w' : World R TxId D} {t : Turn R TxId Ev D}
    (h : World.step H w t = some w') {n : D} (m : n ∈ t.nullifiers) : w'.spent n = some () := by
  obtain ⟨_, height, logRoot, _, _, _, _, hsys⟩ := admit_ok H ((step_eq_some H).1 h)
  show w'.system _ = _
  rw [hsys, sysPost_spent, if_pos m]

/-- **A spent nullifier is refused** (D2's `spent_marker_refused`, over `World`). -/
theorem spent_refused {w : World R TxId D} {t : Turn R TxId Ev D} {n : D}
    (m : n ∈ t.nullifiers) (spent : w.spent n = some ()) : World.step H w t = none := by
  cases hs : World.step H w t with
  | none => rfl
  | some w' =>
      obtain ⟨height, logRoot, _, hk⟩ := admit_ok_turnCheck H ((step_eq_some H).1 hs)
      have := ((turnCheck_eq_none_iff H).1 hk).2.2.1 n m
      rw [spent] at this
      cases this

/-- **The charge stays within the allowance**, and the meter is debited by
exactly the charge. -/
theorem charge_le_allowance {w w' : World R TxId D} {t : Turn R TxId Ev D}
    (h : World.step H w t = some w') :
    t.charge ≤ w.meter ∧ ∀ l, w'.meter l = w.meter l - t.charge l := by
  have ha := (step_eq_some H).1 h
  obtain ⟨height, logRoot, hh, hk⟩ := admit_ok_turnCheck H ha
  obtain ⟨_, height', logRoot', hh', _, _, _, hsys⟩ := admit_ok H ha
  rw [hh] at hh'
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hh')
  refine ⟨((turnCheck_eq_none_iff H).1 hk).2.2.2.2, fun l => ?_⟩
  rw [meter_system, meter_system (w := w), hsys, sysPost_allowance]
  by_cases hl : t.charge l ≠ 0
  · rw [if_pos hl]; rfl
  · rw [if_neg hl]
    simp only [not_not] at hl
    rw [hl, Nat.sub_zero]

/-- **The storage charge is the patch bytes** (D2's
`storage_charge_is_written_bytes`, as SURPASS §2(b).6's `charge_is_patch_bytes`). -/
theorem charge_is_patch_bytes {w w' : World R TxId D} {t : Turn R TxId Ev D}
    (h : World.step H w t = some w') : t.charge .storageBytes = patchBytes H t := by
  obtain ⟨height, logRoot, _, hk⟩ := admit_ok_turnCheck H ((step_eq_some H).1 h)
  exact ((turnCheck_eq_none_iff H).1 hk).2.2.2.1

/-- **The clock pin.**  An accepted turn was journaled at a height inside its
window. -/
theorem step_window {w w' : World R TxId D} {t : Turn R TxId Ev D}
    (h : World.step H w t = some w') :
    ∃ height logRoot, w.head = some (height, logRoot) ∧ t.notBefore ≤ height ∧
      ∀ u ∈ t.validUntil, height ≤ u := by
  obtain ⟨height, logRoot, hh, hk⟩ := admit_ok_turnCheck H ((step_eq_some H).1 h)
  obtain ⟨lo, hi⟩ := ((turnCheck_eq_none_iff H).1 hk).2.1
  refine ⟨height, logRoot, hh, lo, fun u m => ?_⟩
  rw [Option.mem_def] at m
  rw [m] at hi
  simpa using hi

/-- Reads leave the store unchanged, so a valid run of reads has each read
enabled at the starting store. -/
theorem validFrom_reads {L : Layout.{0, 0, 0}} {s : Store L} :
    ∀ {p : Patch L}, (∀ op ∈ p, Op.isRead op = true) → Patch.ValidFrom s p →
      ∀ op ∈ p, op.Enabled s
  | [], _, _, op, m => absurd m (by simp)
  | op0 :: rest, reads, valid, op, m => by
      have same : op0.apply s = s := by
        have r := reads op0 (by simp)
        cases op0 <;> first | rfl | cases r
      rcases List.mem_cons.mp m with e | m'
      · subst e; exact valid.1
      · have v := valid.2
        rw [same] at v
        exact validFrom_reads (fun o mo => reads o (List.mem_cons_of_mem _ mo)) v op m'

/-- **The footprint is pinned.**  A turn one of whose guards no longer holds
at the pre-world — the value at a read address moved — is refused.  (A leg on
a cell the turn neither creates nor retires; a created cell has no prior
value to pin.) -/
theorem footprint_pinned {w : World R TxId D} {t : Turn R TxId Ev D} (leg : Leg R)
    (m : leg ∈ t.legs) (hc : leg.cell ∉ t.creates.map Prod.fst) (hr : leg.cell ∉ t.retires)
    {pre : Store (R.layout leg.kind)}
    (hpre : (w.cells leg.cell).bind (·.storeAt leg.kind) = some pre)
    {op : Op (R.layout leg.kind)} (pinned : op ∈ leg.guards) (moved : ¬ op.Enabled pre) :
    World.step H w t = none := by
  cases hs : World.step H w t with
  | none => rfl
  | some w' =>
      obtain ⟨pre', hpre', hv, _⟩ := step_leg H hs leg m hc hr
      rw [hpre] at hpre'
      cases hpre'
      have split := List.takeWhile_append_dropWhile (p := Op.isRead) (l := leg.patch)
      rw [← split, Patch.validFrom_append] at hv
      exact absurd (validFrom_reads (fun o mo => List.all_eq_true.mp List.all_takeWhile o mo) hv.1 op pinned) moved

/-- A turn that writes, creates and retires nothing is refused whether or not
it spends: a spend must be pinned by at least one guard leg (the deployed
`unguardedEventOnly` rule, which `emptyTurn` already is). -/
theorem spend_needs_guard (w : World R TxId D) (t : Turn R TxId Ev D)
    (hl : t.legs = []) (hc : t.creates = []) (hr : t.retires = []) :
    rejectOf (World.admit H w t) = some .emptyTurn := by
  unfold World.admit
  simp [hl, hc, hr, rejectOf]

end TurnLaws

/-! ## Checkpoints (§4.4) -/

section Checkpoints

variable {R : Registry} {TxId Ev D : Type} [DecidableEq TxId] [DecidableEq D]
variable (H : History R TxId Ev D)

/-- A world at a height with its root.  The root function is the caller's
(C1: stage-F sorted hash; D1/E1: SMT). -/
structure Checkpoint (R : Registry) (TxId D Root : Type) [DecidableEq TxId] [DecidableEq D] where
  height : Nat
  world : World R TxId D
  root : Root

namespace Checkpoint

variable {Root : Type} [DecidableEq Root]

/-- The only thing a checkpoint certifies by itself: its world hashes to its
root. -/
def check (rootOf : World R TxId D → Root) (c : Checkpoint R TxId D Root) : Bool :=
  decide (rootOf c.world = c.root)

/-- Recovery: a checkpoint that checks, then the suffix folded from it. -/
def resume (rootOf : World R TxId D → Root) (c : Checkpoint R TxId D Root)
    (suffix : List (Turn R TxId Ev D)) : Option (World R TxId D) :=
  if c.check rootOf then fold H c.world suffix else none

end Checkpoint

/-- **Checkpoint soundness (§4.4).**  The world after the first `h` turns,
folded over the rest of the log, is the world after the whole log. -/
theorem checkpoint_suffix (g W_h : World R TxId D) (log : List (Turn R TxId Ev D)) (h : Nat)
    (prefixed : fold H g (log.take h) = some W_h) :
    fold H W_h (log.drop h) = fold H g log := by
  conv_rhs => rw [← List.take_append_drop h log]
  rw [fold_append, prefixed]
  rfl

/-- Recovery from a stored checkpoint equals the fold from genesis, when the
stored root is the honest world's root (the receipt chain's claim) and the
root binds at that pair (the collision-resistance carrier, stated at the one
pair compared; refuted in `Example.nonbinding_root_accepts_tamper`). -/
theorem resume_sound {Root : Type} [DecidableEq Root] (rootOf : World R TxId D → Root)
    (g W_h : World R TxId D) (log : List (Turn R TxId Ev D)) (c : Checkpoint R TxId D Root)
    (prefixed : fold H g (log.take c.height) = some W_h)
    (honestRoot : c.root = rootOf W_h)
    (binds : rootOf c.world = rootOf W_h → c.world = W_h)
    (checks : c.check rootOf = true) :
    c.resume H rootOf (log.drop c.height) = fold H g log := by
  unfold Checkpoint.resume
  rw [if_pos checks]
  have hw : c.world = W_h := binds (by
    have := of_decide_eq_true checks
    rw [this, honestRoot])
  rw [hw]
  exact checkpoint_suffix H g W_h log c.height prefixed

end Checkpoints

/-! ## Poles: built instances that pass and built instances that fail -/

namespace Example

/-- One namespace, `Nat` keys and values, RAM. -/
def toyLayout : Layout.{0, 0, 0} where
  Namespace := Unit
  Key := fun _ => Nat
  Value := fun _ => Nat
  discipline := fun _ => .ram

/-- Two kinds over the toy layout, so a kind mismatch is constructible. -/
def toyR : Registry where
  Kind := Bool
  layout := fun _ => toyLayout

abbrev ToyWorld := World toyR Nat Nat
abbrev ToyTurn := Turn toyR Nat Unit Nat

/-- A toy digest: deliberately NOT binding (it sees only the id and the leg
count), so the collision poles below are constructible. -/
def toyH : History toyR Nat Unit Nat where
  turnDigest := fun t => t.txId * 7 + t.legs.length
  chain := fun r d => r * 31 + d + 1
  logRoot0 := 1
  -- The B2 toy charges no storage; `Kernel.TurnCensus` exercises the meter.
  legBytes := fun _ => 0

def g : ToyWorld := genesis toyH 0

def alloc (key value : Nat) : Op toyLayout := .allocate () key value
def wr (key before after : Nat) : Op toyLayout := .write () key before after
def rd (key : Nat) (observed : Option Nat) : Op toyLayout := .read () key observed
def free (key before : Nat) : Op toyLayout := .free () key before

def leg (c : CellId) (p : Patch toyLayout) : Leg toyR := ⟨c, false, p⟩

def turn (x : Nat) (creates : List (CellId × Bool)) (legs : List (Leg toyR))
    (retires : List CellId := []) : ToyTurn :=
  { txId := x, creates := creates.map (fun c => (c.1, c.2, none)), legs := legs,
    retires := retires, event := () }

/-- A turn whose creates each name a room. -/
def turnIn (x : Nat) (creates : List (CellId × Bool × Option CellId)) (legs : List (Leg toyR)) :
    ToyTurn :=
  { txId := x, creates := creates, legs := legs, retires := [], event := () }

/-- Create cells 0 and 1, each holding key 0. -/
def t0 : ToyTurn := turn 1 [(0, false), (1, false)] [leg 0 [alloc 0 5], leg 1 [alloc 0 9]]
/-- Write cell 0 guarded at 5, read-guard cell 1 at 9. -/
def t1 : ToyTurn := turn 2 [] [leg 0 [wr 0 5 6], leg 1 [rd 0 (some 9)]]

/-- The value at key 0 of a cell. -/
def val (w : ToyWorld) (c : CellId) : Option Nat :=
  (w.cells c).bind fun cell => (cell.storeAt false).bind fun s => s ⟨(), (0 : Nat)⟩

def log2 : List ToyTurn := [t0, t1]

/-! ### §4.3 replay exactness -/

theorem log2_folds : ((fold toyH g log2).map fun w => (val w 0, val w 1)) =
    some (some 6, some 9) := by decide +kernel

theorem log2_reaches : ∃ W, Reaches toyH g log2 W := by
  cases e : fold toyH g log2 with
  | none => exact absurd (congrArg Option.isSome e) (by decide +kernel)
  | some W => exact ⟨W, (fold_eq_some_iff toyH g log2 W).1 e⟩

/-- Refuting pole: a log whose second turn's guard is stale does not fold. -/
theorem stale_guard_log_refused :
    (fold toyH g [t0, turn 2 [] [leg 0 [wr 0 4 6]]]).isNone = true := by decide +kernel

/-- Refuting pole: a log repeating a transaction id does not fold. -/
theorem duplicate_txId_log_refused :
    (fold toyH g [t0, turn 1 [] [leg 0 [wr 0 5 6]]]).isNone = true := by decide +kernel

/-! ### §4.9 journal exactness and retry -/

theorem log2_journal :
    ((fold toyH g log2).map fun w => (w.journal 1, w.journal 2, w.journal 3, w.head)) =
      some (some (0, 9), some (1, 16), none,
        some (2, logChain toyH 1 log2)) := by decide +kernel

/-- The retry of `t1` after the log is a replay of height 1; its accepted
retry is refused. -/
theorem log2_retry :
    ((fold toyH g log2).map fun w => (classify toyH w t1, rejectOf (World.admit toyH w t1))) =
      some (.replay 1, some .replayedTransaction) := by decide +kernel

/-- A different turn under id 2, separated by the digest, is a conflict. -/
theorem log2_conflict :
    ((fold toyH g log2).map fun w => classify toyH w (turn 2 [] [leg 0 [wr 0 6 7]])) =
      some (.conflict 1) := by decide +kernel

/-- Refuting pole for the digest premise: the toy digest does not bind, and a
different turn under id 2 with the same leg count is misread as a replay. -/
theorem digest_collision_hides_conflict :
    ((fold toyH g log2).map fun w =>
      classify toyH w (turn 2 [] [leg 0 [wr 0 5 7], leg 1 [rd 0 (some 9)]])) =
      some (.replay 1) := by decide +kernel

/-! ### §4.7 fail-closed admission: one built refusal per reason -/

def w1 : ToyWorld := (fold toyH g [t0]).getD g

theorem reject_emptyTurn : rejectOf (World.admit toyH w1 (turn 5 [] [])) = some .emptyTurn := by
  decide +kernel
theorem reject_duplicateLegCell :
    rejectOf (World.admit toyH w1 (turn 5 [] [leg 0 [], leg 0 []])) = some .duplicateLegCell := by
  decide +kernel
theorem reject_duplicateCreate :
    rejectOf (World.admit toyH w1 (turn 5 [(4, false), (4, true)] [])) = some .duplicateCreate := by
  decide +kernel
theorem reject_duplicateRetire :
    rejectOf (World.admit toyH w1 (turn 5 [] [] [0, 0])) = some .duplicateRetire := by
  decide +kernel
theorem reject_noHead :
    rejectOf (World.admit toyH (⟨0, 0⟩ : ToyWorld) t0) = some .noHead := by
  decide +kernel
theorem reject_replayedTransaction :
    rejectOf (World.admit toyH w1 (turn 1 [] [leg 0 [wr 0 5 6]])) = some .replayedTransaction := by
  decide +kernel
theorem reject_cellPresent :
    rejectOf (World.admit toyH w1 (turn 5 [(0, false)] [])) = some (.cellPresent 0) := by
  decide +kernel
theorem reject_missingCell :
    rejectOf (World.admit toyH w1 (turn 5 [] [leg 7 [rd 0 none]])) = some (.missingCell 7) := by
  decide +kernel
theorem reject_kindMismatch :
    rejectOf (World.admit toyH w1 (turn 5 [] [⟨0, true, [rd 0 (some 5)]⟩])) =
      some (.kindMismatch 0) := by
  decide +kernel
theorem reject_guardFailed :
    rejectOf (World.admit toyH w1 (turn 5 [] [leg 0 [rd 0 (some 5), wr 0 4 6]])) =
      some (.guardFailed 0 1) := by
  decide +kernel
theorem reject_retireNonEmpty :
    rejectOf (World.admit toyH w1 (turn 5 [] [] [0])) = some (.retireNonEmpty 0) := by
  decide +kernel

/-- Retire after emptying by a guarded free: accepted, and the id is retired. -/
def tRetire : ToyTurn := turn 5 [] [leg 0 [free 0 5]] [0]

theorem retire_accepted :
    ((World.step toyH w1 tRetire).map fun w => (val w 0, w.retired 0, val w 1)) =
      some (none, some (), some 9) := by
  decide +kernel

/-- A retired id cannot be created again. -/
theorem reject_retiredIdentifier :
    ((World.step toyH w1 tRetire).map fun w =>
      rejectOf (World.admit toyH w (turn 6 [(0, false)] []))) =
      some (some .retiredIdentifier) := by
  decide +kernel

/-! ### Rooms (K-ROOM): a create names a present room; the row is recorded -/

/-- Cell 5 is created in room 0 and cell 6 in room 5, in one turn: an earlier
create of the same turn is a present room. -/
def tRoom : ToyTurn := turnIn 6 [(5, false, some 0), (6, false, some 5)] []

theorem room_create_accepted :
    ((World.step toyH w1 tRoom).map fun w => (w.parent 5, w.parent 6, w.parent 0)) =
      some (some 0, some 5, none) := by
  decide +kernel

/-- `under 0` covers room 0 itself, cell 5 and cell 6 (by the chain 6 → 5 → 0)
at the world's own parentage; `under 5` does not cover room 0. -/
theorem room_chain_covers :
    ((World.step toyH w1 tRoom).map fun w =>
      (decide ((Theory.TypedAuthorization.TargetSet.under 0 : Theory.TypedAuthorization.TargetSet .object).Covers
          w.parentage ⟨6⟩),
        decide ((Theory.TypedAuthorization.TargetSet.under 0 : Theory.TypedAuthorization.TargetSet .object).Covers
          w.parentage ⟨0⟩),
        decide ((Theory.TypedAuthorization.TargetSet.under 5 : Theory.TypedAuthorization.TargetSet .object).Covers
          w.parentage ⟨0⟩))) =
      some (true, true, false) := by
  decide +kernel

/-- Refusal pole: a create in an absent room is refused, naming cell and room. -/
theorem reject_missingParent :
    rejectOf (World.admit toyH w1 (turnIn 6 [(5, false, some 99)] [])) =
      some (.missingParent 5 99) := by
  decide +kernel

/-- Refusal pole: order matters — a create cannot name a room created later in
the same turn. -/
theorem reject_room_created_later :
    rejectOf (World.admit toyH w1 (turnIn 6 [(6, false, some 5), (5, false, some 0)] [])) =
      some (.missingParent 6 5) := by
  decide +kernel

/-! ### §4.8 no TOCTOU: the guard is checked at the world `step` applies to -/

/-- `t1` is accepted at `w1` ... -/
theorem t1_accepted_at_w1 : (World.step toyH w1 t1).isSome = true := by decide +kernel

/-- ... and refused where only its read-guarded address (cell 1, key 0) moved. -/
theorem t1_refused_after_read_moves :
    ((World.step toyH w1 (turn 9 [] [leg 1 [wr 0 9 10]])).map fun w =>
      rejectOf (World.admit toyH w t1)) = some (some (.guardFailed 1 0)) := by
  decide +kernel

/-! ### §4.2 frame: the written cell moves, the untouched one does not -/

theorem frame_poles :
    ((World.step toyH w1 (turn 9 [] [leg 1 [wr 0 9 10]])).map fun w => (val w 0, val w 1)) =
      some (val w1 0, some 10) ∧ val w1 1 = some 9 := by
  decide +kernel

/-! ### §4.4 checkpoints -/

/-- A root that sees every cell's key-0 value at ids 0..3 and the head:
binding on the toy worlds compared here. -/
def toyRoot (w : ToyWorld) : List (Option Nat) × Option (Nat × Nat) :=
  ((List.range 4).map (val w), w.head)

/-- A root that sees only the head: not binding. -/
def headRoot (w : ToyWorld) : Option (Nat × Nat) := w.head

/-- The honest checkpoint at height 1. -/
def honest : Checkpoint toyR Nat Nat (List (Option Nat) × Option (Nat × Nat)) :=
  ⟨1, w1, toyRoot w1⟩

/-- The tampered world: cell 1's value replaced, head unchanged. -/
def tamperedWorld : ToyWorld :=
  { w1 with cells := w1.cells.update 1 (some ⟨false, (0 : Store toyLayout).set ⟨(), (0 : Nat)⟩ (some (99 : Nat))⟩) }

theorem w1_prefix : fold toyH g (log2.take 1) = some w1 := by
  have e : (fold toyH g [t0]).isSome = true := by decide +kernel
  exact (Option.eq_some_of_isSome e).trans rfl

/-- Satisfiable pole: the honest checkpoint checks and resumes to the fold. -/
theorem honest_resumes :
    honest.check toyRoot = true ∧
      honest.resume toyH toyRoot (log2.drop honest.height) = fold toyH g log2 :=
  ⟨by decide +kernel,
    resume_sound toyH toyRoot g w1 log2 honest w1_prefix rfl (fun _ => rfl) (by decide +kernel)⟩

/-- Refuting pole: a tampered world under the honest root fails `check`. -/
theorem tampered_check_fails :
    (⟨1, tamperedWorld, toyRoot w1⟩ : Checkpoint toyR Nat Nat _).check toyRoot = false := by
  decide +kernel

/-- Refuting pole for the binding premise: under a root that sees only the
head, the tampered checkpoint checks, and its resume disagrees with the fold
from genesis. -/
theorem nonbinding_root_accepts_tamper :
    (⟨1, tamperedWorld, headRoot w1⟩ : Checkpoint toyR Nat Nat _).check headRoot = true ∧
      ((Checkpoint.resume toyH headRoot ⟨1, tamperedWorld, headRoot w1⟩ (log2.drop 1)).map
          fun w => val w 1) ≠
        (fold toyH g log2).map fun w => val w 1 := by
  decide +kernel

end Example

/-! ## Axiom pins -/

/-- info: 'Minidregg.Kernel.World.Cell.eq_of_storeAt' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms Cell.eq_of_storeAt
/-- info: 'Minidregg.Kernel.World.fold_cons' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms fold_cons
/-- info: 'Minidregg.Kernel.World.fold_append' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms fold_append
/-- info: 'Minidregg.Kernel.World.fold_snoc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms fold_snoc
/-- info: 'Minidregg.Kernel.World.fold_eq_some_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms fold_eq_some_iff
/-- info: 'Minidregg.Kernel.World.cells_update_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms cells_update_self
/-- info: 'Minidregg.Kernel.World.cells_update_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms cells_update_ne
/-- info: 'Minidregg.Kernel.World.step_eq_some' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms step_eq_some
/-- info: 'Minidregg.Kernel.World.admit_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms admit_ok
/-- info: 'Minidregg.Kernel.World.admit_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms admit_of
/-- info: 'Minidregg.Kernel.World.applyCells_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms applyCells_ok
/-- info: 'Minidregg.Kernel.World.applyCreates_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms applyCreates_frame
/-- info: 'Minidregg.Kernel.World.applyCreates_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms applyCreates_mem
/-- info: 'Minidregg.Kernel.World.applyCreates_present' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms applyCreates_present
/-- info: 'Minidregg.Kernel.World.applyLeg_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms applyLeg_ok
/-- info: 'Minidregg.Kernel.World.applyLegs_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms applyLegs_frame
/-- info: 'Minidregg.Kernel.World.applyLegs_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms applyLegs_mem
/-- info: 'Minidregg.Kernel.World.applyLegs_present' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms applyLegs_present
/-- info: 'Minidregg.Kernel.World.applyRetires_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms applyRetires_frame
/-- info: 'Minidregg.Kernel.World.applyRetires_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms applyRetires_mem
/-- info: 'Minidregg.Kernel.World.applyRetires_present' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms applyRetires_present
/-- info: 'Minidregg.Kernel.World.op_apply_write' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms op_apply_write
/-- info: 'Minidregg.Kernel.World.op_apply_allocate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms op_apply_allocate
/-- info: 'Minidregg.Kernel.World.sys_space_ne' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms sys_space_ne
/-- info: 'Minidregg.Kernel.World.sys_key_ne' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms sys_key_ne
/-- info: 'Minidregg.Kernel.World.run_createReads' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms run_createReads
/-- info: 'Minidregg.Kernel.World.validFrom_createReads' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms validFrom_createReads
/-- info: 'Minidregg.Kernel.World.run_retireAllocs_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms run_retireAllocs_ne
/-- info: 'Minidregg.Kernel.World.run_retireAllocs_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms run_retireAllocs_at
/-- info: 'Minidregg.Kernel.World.sysPost_journal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms sysPost_journal
/-- info: 'Minidregg.Kernel.World.sysPost_head' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms sysPost_head
/-- info: 'Minidregg.Kernel.World.sysPost_retired' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms sysPost_retired
/-- info: 'Minidregg.Kernel.World.sysPatch_valid_creates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms sysPatch_valid_creates
/-- info: 'Minidregg.Kernel.World.sysPatch_valid_plain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms sysPatch_valid_plain
/-- info: 'Minidregg.Kernel.World.step_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms step_frame
/-- info: 'Minidregg.Kernel.World.step_leg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms step_leg
/-- info: 'Minidregg.Kernel.World.step_create' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms step_create
/-- info: 'Minidregg.Kernel.World.step_retire' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms step_retire
/-- info: 'Minidregg.Kernel.World.step_wf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms step_wf
/-- info: 'Minidregg.Kernel.World.fold_wf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms fold_wf
/-- info: 'Minidregg.Kernel.World.genesis_is_Genesis' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms genesis_is_Genesis
/-- info: 'Minidregg.Kernel.World.genesis_wf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms genesis_wf
/-- info: 'Minidregg.Kernel.World.step_head' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms step_head
/-- info: 'Minidregg.Kernel.World.fold_head' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms fold_head
/-- info: 'Minidregg.Kernel.World.step_journal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms step_journal
/-- info: 'Minidregg.Kernel.World.journal_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms journal_exact
/-- info: 'Minidregg.Kernel.World.journal_height_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms journal_height_iff
/-- info: 'Minidregg.Kernel.World.fold_txId_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms fold_txId_unique
/-- info: 'Minidregg.Kernel.World.admit_retry_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms admit_retry_refused
/-- info: 'Minidregg.Kernel.World.classify_replay' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms classify_replay
/-- info: 'Minidregg.Kernel.World.classify_conflict' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms classify_conflict
/-- info: 'Minidregg.Kernel.World.classify_fresh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms classify_fresh
/-- info: 'Minidregg.Kernel.World.checkpoint_suffix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms checkpoint_suffix
/-- info: 'Minidregg.Kernel.World.resume_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms resume_sound
/-- info: 'Minidregg.Kernel.World.Example.log2_folds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Example.log2_folds
/-- info: 'Minidregg.Kernel.World.Example.log2_reaches' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Example.log2_reaches
/-- info: 'Minidregg.Kernel.World.Example.stale_guard_log_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Example.stale_guard_log_refused
/-- info: 'Minidregg.Kernel.World.Example.duplicate_txId_log_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Example.duplicate_txId_log_refused
/-- info: 'Minidregg.Kernel.World.Example.log2_journal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Example.log2_journal
/-- info: 'Minidregg.Kernel.World.Example.log2_retry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Example.log2_retry
/-- info: 'Minidregg.Kernel.World.Example.log2_conflict' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Example.log2_conflict
/-- info: 'Minidregg.Kernel.World.Example.digest_collision_hides_conflict' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Example.digest_collision_hides_conflict
/-- info: 'Minidregg.Kernel.World.Example.reject_emptyTurn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Example.reject_emptyTurn
/-- info: 'Minidregg.Kernel.World.Example.reject_duplicateLegCell' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Example.reject_duplicateLegCell
/-- info: 'Minidregg.Kernel.World.Example.reject_duplicateCreate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Example.reject_duplicateCreate
/-- info: 'Minidregg.Kernel.World.Example.reject_duplicateRetire' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Example.reject_duplicateRetire
/-- info: 'Minidregg.Kernel.World.Example.reject_noHead' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Example.reject_noHead
/-- info: 'Minidregg.Kernel.World.Example.reject_replayedTransaction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Example.reject_replayedTransaction
/-- info: 'Minidregg.Kernel.World.Example.reject_cellPresent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Example.reject_cellPresent
/-- info: 'Minidregg.Kernel.World.Example.reject_missingCell' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Example.reject_missingCell
/-- info: 'Minidregg.Kernel.World.Example.reject_kindMismatch' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Example.reject_kindMismatch
/-- info: 'Minidregg.Kernel.World.Example.reject_guardFailed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Example.reject_guardFailed
/-- info: 'Minidregg.Kernel.World.Example.reject_retireNonEmpty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Example.reject_retireNonEmpty
/-- info: 'Minidregg.Kernel.World.Example.retire_accepted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Example.retire_accepted
/-- info: 'Minidregg.Kernel.World.Example.reject_retiredIdentifier' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Example.reject_retiredIdentifier
/-- info: 'Minidregg.Kernel.World.Example.t1_accepted_at_w1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Example.t1_accepted_at_w1
/-- info: 'Minidregg.Kernel.World.Example.t1_refused_after_read_moves' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Example.t1_refused_after_read_moves
/-- info: 'Minidregg.Kernel.World.Example.frame_poles' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Example.frame_poles
/-- info: 'Minidregg.Kernel.World.Example.w1_prefix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Example.w1_prefix
/-- info: 'Minidregg.Kernel.World.Example.honest_resumes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Example.honest_resumes
/-- info: 'Minidregg.Kernel.World.Example.tampered_check_fails' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Example.tampered_check_fails
/-- info: 'Minidregg.Kernel.World.Example.nonbinding_root_accepts_tamper' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Example.nonbinding_root_accepts_tamper

/-- info: 'Minidregg.Kernel.World.applyCreates_room' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.World.applyCreates_room
/-- info: 'Minidregg.Kernel.World.applyCreates_missing_room' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.World.applyCreates_missing_room
/-- info: 'Minidregg.Kernel.World.sysPost_parent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.World.sysPost_parent
/-- info: 'Minidregg.Kernel.World.step_parent_recorded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.World.step_parent_recorded
/-- info: 'Minidregg.Kernel.World.step_parent_exists' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.World.step_parent_exists
/-- info: 'Minidregg.Kernel.World.step_parent_stable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.World.step_parent_stable
/-- info: 'Minidregg.Kernel.World.step_narrows_stable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.World.step_narrows_stable
/-- info: 'Minidregg.Kernel.World.Example.room_create_accepted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.World.Example.room_create_accepted
/-- info: 'Minidregg.Kernel.World.Example.room_chain_covers' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.World.Example.room_chain_covers
/-- info: 'Minidregg.Kernel.World.Example.reject_missingParent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.World.Example.reject_missingParent
/-- info: 'Minidregg.Kernel.World.Example.reject_room_created_later' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.World.Example.reject_room_created_later

/-! ### T1 pins -/

#assert_axioms admit_ok_turnCheck
#assert_axioms turnCheck_eq_none_iff
#assert_axioms meter_system
#assert_axioms spent_monotone
#assert_axioms fold_spent_monotone
#assert_axioms step_spends
#assert_axioms spent_refused
#assert_axioms charge_le_allowance
#assert_axioms charge_is_patch_bytes
#assert_axioms step_window
#assert_axioms validFrom_reads
#assert_axioms footprint_pinned
#assert_axioms spend_needs_guard
#assert_axioms run_spentAllocs_ne
#assert_axioms run_spentAllocs_at
#assert_axioms validFrom_spentAllocs
#assert_axioms run_debits_ne
#assert_axioms run_debits_at
#assert_axioms validFrom_debits
#assert_axioms meterLanes_nodup
#assert_axioms mem_meterLanes
#assert_axioms mem_chargedLanes
#assert_axioms chargedLanes_nodup
#assert_axioms run_sysPatch_core
#assert_axioms validFrom_sysPatch
#assert_axioms run_sysCore_spent
#assert_axioms run_sysCore_allowance
#assert_axioms sysPost_spent
#assert_axioms sysPost_allowance

end Minidregg.Kernel.World
