/-
# Kernel.TurnLog -- a log of Turns, folded by `World.admit` (FD-1, R4a)

The deployed genesis World of a `Seed`, the Turn log's framing, and the
follower: decode each entry against its own world (`DeployedTurnCompact.decodeTurnAt`:
digest guards, no old values), admit it (`World.admit` at `DeployedHistory.history`),
stop by height on the first entry that does not decode or does not take.
`followFrom_sound`: what a follower reaches is `World.fold` of the turns it
returns; `followFrom_writeLog`: a follower of the writer's log reaches the
writer's world with exactly the writer's turns.  No persisted byte changes yet:
the Host still appends `IntentRecord`s; `Host/TurnLogFollower` derives this log.

The root a follower reports (`turnLogRoot`) is the deployed root's shape: the
system slot `systemLeaf height logRoot` with the World's own head (the chain
over turn digests), and each listed cell's `rootBytes` of the bytes the World
holds for it (`bytesOf`: the canonical encoding, or the retired image).
-/
module

public import Kernel.DeployedTurnCompact
public import Compiler.DurableCheckpointCodec
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

namespace Minidregg.Kernel.TurnLog

open Minidregg.Theory.Store
open Minidregg.Theory.TypedAuthorization (Digest)
open Minidregg.Theory.ResourceCost (Lane Charge)
open Minidregg.Kernel.World
open Minidregg.Kernel.DeployedBridge
open Minidregg.Kernel.DeployedHistory
open Minidregg.Kernel.DeployedTurnCodec
open Minidregg.Kernel.DeployedTurnCompact
open Minidregg.Kernel.TurnOfIntent
open Minidregg.Compiler
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Kernel.DurableDataIntent (TransactionId StableEvent)

set_option autoImplicit false

/-- The deployed World. -/
abbrev DWorld := World deployedR TransactionId Digest

/-! ## Genesis -/

/-- Why a seed has no genesis World. -/
inductive GenesisRefusal
  /-- The bytes an unlisted cell holds do not read as the absent slot. -/
  | absentNotAbsent
  /-- A seed cell's bytes do not decode at any registry kind. -/
  | undecodable (cell : CellId)
  /-- A seed lists one cell id twice. -/
  | duplicateCell (cell : CellId)
  deriving DecidableEq, Repr

/-- The genesis system cell with the seed's allowance: the head `(0, logRoot0)`
and one `allowance` row per meter lane. -/
def genesisSystem (available : Charge) : Store (sysLayout TransactionId Digest) :=
  meterLanes.foldl (fun s lane => Store.set s ⟨SysSpace.allowance, lane⟩ (some (available lane)))
    (World.genesisSystem history)

/-- Mark retired seed cells. -/
def retireRows (s : Store (sysLayout TransactionId Digest)) (ids : List CellId) :
    Store (sysLayout TransactionId Digest) :=
  ids.foldl (fun s c => Store.set s ⟨SysSpace.retired, c⟩ (some ())) s

/-- **The deployed genesis World of a seed**: every seed cell decoded at its
registry kind (a retired image is an absent cell with a `retired` row), the
seed's allowance in the meter, the head at height 0. -/
def genesisOfSeed (seed : DurableReceiver.Seed) : Except GenesisRefusal DWorld := do
  match decodeCell seed.absentBytes with
  | some none => if retiresCell seed.absentBytes then throw .absentNotAbsent
  | _ => throw .absentNotAbsent
  let ids := seed.cells.map fun c => c.1.value
  unless ids.Nodup do
    throw (.duplicateCell ((ids.find? fun c => ids.count c > 1).getD 0))
  let mut cells : Cells deployedR := 0
  let mut retired : List CellId := []
  for entry in seed.cells do
    let id := entry.1
    let bytes := entry.2
    match decodeCell bytes with
    | none => throw (.undecodable id.value)
    | some slot =>
      cells := cells.set id.value slot
      if retiresCell bytes then retired := id.value :: retired
  return ⟨cells, retireRows (genesisSystem seed.available) retired.reverse⟩

/-! ## The follower -/

/-- Why a follower stopped, and at which height (0-based entry index). -/
inductive FollowStop
  | undecodable (height : Nat)
  /-- The entry at `height`, or its turn, is past a static bound (`decodeEntry`). -/
  | overBound (height : Nat) (name : Bounds.Name) (value limit : Nat)
  | refused (height : Nat) (reason : Reject)
  deriving DecidableEq, Repr

/-- Fold a list of persisted entries from `w`, numbering from `height`: each
entry is decoded AGAINST the current world (`decodeEntry`: refused by name past a
static bound, then `decodeTurnAt`, whose digest guards are checked against the
cells the world holds) and admitted. -/
def followFrom (w : DWorld) (height : Nat) :
    List (List UInt8) → Except FollowStop (DWorld × List (DTurn deployedR Digest))
  | [] => .ok (w, [])
  | entry :: rest =>
    match decodeEntry w entry with
    | .error .undecodable => .error (.undecodable height)
    | .error (.overBound name value limit) => .error (.overBound height name value limit)
    | .ok t =>
      match World.admit history w t with
      | .error reason => .error (.refused height reason)
      | .ok w' => (followFrom w' (height + 1) rest).map fun r => (r.1, t :: r.2)

/-- **Every world a follower reaches is the fold of the turns it returns.** -/
theorem followFrom_sound : ∀ (w W : DWorld) (height : Nat) (entries : List (List UInt8))
    (turns : List (DTurn deployedR Digest)),
    followFrom w height entries = .ok (W, turns) →
      turns.length = entries.length ∧ World.fold history w turns = some W
  | w, W, _, [], turns, h => by
      simp only [followFrom, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨rfl, rfl⟩
  | w, W, height, entry :: rest, turns, h => by
      simp only [followFrom] at h
      cases hd : decodeEntry w entry with
      | error e => cases e <;> simp [hd] at h
      | ok t =>
        cases ha : World.admit history w t with
        | error r => simp [hd, ha] at h
        | ok w' =>
          simp only [hd, ha] at h
          cases hr : followFrom w' (height + 1) rest with
          | error e => simp [hr, Except.map] at h
          | ok r =>
            simp only [hr, Except.map, Except.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            obtain ⟨hl, hf⟩ := followFrom_sound w' r.1 (height + 1) rest r.2 hr
            have hs : World.step history w t = some w' := by
              simp [World.step, ha, Except.toOption]
            exact ⟨by simp [hl], by simp [World.fold_cons, hs, hf]⟩

/-- The writer's log: each turn persisted against the world it is admitted at. A
turn whose entry is past a static bound is not written (`entryWithinBounds`). -/
def writeLog : DWorld → List (DTurn deployedR Digest) → Option (List (List UInt8))
  | _, [] => some []
  | w, t :: ts =>
    if entryWithinBounds w t then
      (World.step history w t).bind fun w' => (writeLog w' ts).map (encodeTurnAt w t :: ·)
    else none

/-- **A follower of the writer's log reaches the writer's world**: the persisted
digest-guard entries decode, against the follower's own world, to exactly the
admitted turns. -/
theorem followFrom_writeLog : ∀ (w : DWorld) (height : Nat) (ts : List (DTurn deployedR Digest))
    (entries : List (List UInt8)), writeLog w ts = some entries →
      ∃ W, World.fold history w ts = some W ∧ followFrom w height entries = .ok (W, ts)
  | w, _, [], entries, h => by
      simp only [writeLog, Option.some.injEq] at h
      subst h
      exact ⟨w, rfl, rfl⟩
  | w, height, t :: ts, entries, h => by
      simp only [writeLog] at h
      by_cases hb : entryWithinBounds w t = true
      swap
      · simp [hb] at h
      rw [if_pos hb] at h
      cases hs : World.step history w t with
      | none => simp [hs] at h
      | some w' =>
        cases hr : writeLog w' ts with
        | none => simp [hs, hr] at h
        | some es =>
          simp only [hs, hr, Option.bind_some, Option.map_some, Option.some.injEq] at h
          subst h
          obtain ⟨W, hf, hfol⟩ := followFrom_writeLog w' (height + 1) ts es hr
          have ha : World.admit history w t = .ok w' := by
            unfold World.step at hs
            cases h2 : World.admit history w t with
            | error r => simp [h2, Except.toOption] at hs
            | ok v => simp [h2, Except.toOption] at hs; rw [hs]
          refine ⟨W, by simp [World.fold_cons, hs, hf], ?_⟩
          simp only [followFrom, decodeEntry_encodeTurnAt w t hb, ha, hfol]
          rfl

/-- A log entry's frame: its length, then its bytes. -/
def frameEntries (entries : List (List UInt8)) : List UInt8 :=
  (StreamCodec.list bytesStream).encode entries

/-- Unframe a whole log. -/
def unframeEntries (bytes : List UInt8) : Option (List (List UInt8)) :=
  full (StreamCodec.list bytesStream) bytes

theorem unframe_frame (entries : List (List UInt8)) :
    unframeEntries (frameEntries entries) = some entries := full_encode _ _

/-! ## The root a follower reports -/

/-- The bytes the World holds for a cell id: its canonical encoding, or the
retired image. -/
def bytesOf (w : DWorld) (c : CellId) : List UInt8 :=
  if (w.retired c).isSome then
    ResourceBirthCodec.LifecycleImage.bytes CanonicalCellRegistry.registry .retired
  else encodeCell (w.cells c)

/-- The root over the system slot (the World's head) and the listed cells. -/
def turnLogRoot (w : DWorld) (ids : List CellId) : Digest :=
  let (height, logRoot) := w.head.getD (0, history.logRoot0)
  WorldRoot.deployedRoot
    ((WorldRoot.Key.system, DurableCheckpointCodec.systemLeaf height logRoot) ::
      ids.map fun c => (WorldRoot.Key.cell c, ResourceBirthCodec.rootBytes (bytesOf w c)))

/-- The cell ids a log names: the seed's, then each create's, without repeats. -/
def idsOf (seed : DurableReceiver.Seed) (turns : List (DTurn deployedR Digest)) : List CellId :=
  ((seed.cells.map fun c => c.1.value) ++ turns.flatMap fun t => t.creates.map Prod.fst).eraseDups

#assert_axioms decodeTurn_encodeTurn
#assert_axioms followFrom_sound
#assert_axioms followFrom_writeLog
#assert_axioms unframe_frame

end Minidregg.Kernel.TurnLog
