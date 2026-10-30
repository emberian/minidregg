/- CONSENT-OWN executed plant: no operator-sealed checkpoint is a client base.

A Store key holder (the operator) can seal any state it likes. Most of it is
caught: every later write names its cell's pre-root (`expectedPre`), so a forged
cell that a record later writes does not replay; a checkpoint state may only hold
cells the image seeds or writes, with the seed's absent default
(`State.Admissible`), and the anchor's world root covers those cells. What
neither sees is `State.available`, the metering budget: a checkpoint sealed with
a raised budget passes the open, the replay, the head-root check and the anchor
root, and every state resumed from it carries the operator's budget, so a later
record the honest budget refuses (`insufficientBudget`) would be admitted. This
plant re-seals checkpoint 32 under the Store's own key with every lane's budget
raised by 777, then reads the same heights both ways in one pass (honest
incidences budget after h records = 1000 - h):

  OPERATOR (before CONSENT-OWN): `Loaded.prefixAt` (the opening's old cut at 36)
  and the Store Reader's `stateAt 34` resume from the sealed 32: budget + 777,
  with the cut's world root EQUAL to the honest one (the anchor passes).
  OWN (after): `Loaded.prefixOwn` (the opening's cut), `Reader.ownOnly []` at 34
  and `Reader.ownOnly [own base at 36]` at 38 and at 34: the honest budget, base 0
  or the own base 36.

PASS requires the forgery to APPEAR on every operator path (the plant is live)
and to be ABSENT on every own path.

Usage: lake env lean --run scripts/consent/own-base-plant.lean STORE-HELPER -/
import Compiler.DurableStoreAudit
import Compiler.DurableServed
import Compiler.Sp800185Cshake256

open Minidregg.Theory.TypedAuthorization
open Minidregg.Kernel
open Minidregg.Kernel.DurableDataIntent
open Minidregg.Kernel.DurableReceiver
open Minidregg.Compiler
open Minidregg.Compiler.DurableReceiverIO
open Minidregg.Compiler.DurableHistoryReader

namespace ConsentOwnPlant

def rootBytes (bytes : List UInt8) : Digest :=
  (Sp800185Cshake256.hash "DREGG.DURABLE.RECEIVER.PROBE/v1".toUTF8.toList bytes).digest

def seed : Seed := { absentBytes := [], cells := [(⟨1⟩, [1]), (⟨3⟩, [0])], available := fun _ => 1000 }

def nullifier (number : Nat) : StableNullifier := ⟨1, ⟨700⟩, ⟨number⟩, [UInt8.ofNat number]⟩

/-- Record `number` moves cell 3 from `[number - 1]` to `[number]`. -/
def step (number : Nat) : DataIntent rootBytes where
  transactionId := ⟨1000 + number⟩
  writes := [⟨⟨3⟩, rootBytes [UInt8.ofNat (number - 1)], rootBytes [UInt8.ofNat number], [UInt8.ofNat number]⟩]
  readGuards := []
  nullifiers := [nullifier number]
  exactCharge := fun _ => 1
  event := ⟨1, ⟨800⟩, ⟨number⟩, [UInt8.ofNat number]⟩
  subject := none
  postRootsBound := by simp
  guardsReadOnly := by simp

def require (label : String) (condition : Bool) : IO Unit :=
  unless condition do throw (IO.userError s!"FAIL consent-own plant: {label}")

def cell (id : Nat) (snapshot : DataSnapshot rootBytes) : List UInt8 := snapshot.canonicalBytes ⟨id⟩

/-- The incidences budget a state carries (`State.available`, which the world root does not cover). -/
def budget (snapshot : DataSnapshot rootBytes) : Nat :=
  snapshot.model.available Minidregg.Theory.ResourceCost.Lane.incidences

/-- The own base of a genesis-based cut (`ConsentAnchor.ownOfGenesis`, here over
the probe's root function). -/
def ownOf (cut : Loaded rootBytes) (zero : cut.baseHeight = 0)
    (seeded : cut.base = DurableCheckpoint.State.ofSeed cut.image.seed) : OwnBase rootBytes :=
  ⟨cut.image.seed, cut.logStart, cut.image.accepted.length, cut.chain,
    Thunk.mk fun _ => DurableCheckpoint.State.ofSnapshot cut.image cut.snapshot,
    ⟨cut.image.accepted, rfl, cut.chainExact.symm, cut.snapshot, by
      have folded := cut.resumed
      rw [zero, seeded, DurableCheckpoint.resume_genesis] at folded
      simpa only [Image.ofAccepted_accepted] using folded,
      by show DurableCheckpoint.State.ofSnapshot cut.image cut.snapshot = _
         rw [Image.ofAccepted_accepted]⟩⟩

def run (binary : System.FilePath) (directory : System.FilePath) : IO Unit := do
  IO.FS.writeBinFile (directory / "key") ((List.range 32).map (fun i => UInt8.ofNat (i * 7 + 3))).toByteArray
  let config : NativeConfig :=
    { binary := binary, root := directory / "store", key := directory / "key", checkpointEvery := 16 }
  let transport := { config.transport (fun _ => ⟨7⟩) ⟨999⟩ with systemCell := none }
  match ← bootstrap transport rootBytes seed with
  | .error message => throw (IO.userError message)
  | .ok () => pure ()
  for number in List.range' 1 41 do
    match ← receive transport rootBytes (step number) 3 with
    | .confirmed _ _ => pure ()
    | _ => throw (IO.userError s!"FAIL commit {number}")
  let key ← match ← transport.key with
    | .ok key => pure key
    | .error detail => throw (IO.userError detail)
  -- The operator re-seals checkpoint 32 over its state with every budget lane raised by 777.
  let some stored := (← transport.checkpointAt 32).toOption.join
    | throw (IO.userError "FAIL no checkpoint at 32")
  let body ← match DurableCheckpointCodec.openSealed key rootBytes stored.bytes with
    | .ok body => pure body
    | .error _ => throw (IO.userError "FAIL the honest checkpoint does not open")
  require "the honest checkpoint is at 32" (body.height == 32)
  let forged := { body.state with available := fun lane => body.state.available lane + 777 }
  match ← transport.putCheckpoint 32 (DurableCheckpointCodec.checkpointFrame.encode
      (DurableCheckpointCodec.sealCheckpoint key rootBytes 32 body.chain body.frontier body.indexRoot forged
        body.system)) with
  | .ok () => pure ()
  | .error detail => throw (IO.userError s!"FAIL put: {detail}")
  let ⟨target, chains, chainsExact⟩ ← match ← loadChained transport rootBytes with
    | .ok opened => pure opened
    | .error detail => throw (IO.userError s!"FAIL the forged Store does not open: {detail}")
  require "the forged Store opens on base 32 at head 41" (target.baseHeight == 32 && target.height == 41)
  -- OPERATOR path: the opening's old cut at the anchor 36, and the Store Reader.
  let ⟨old, _, _⟩ ← match target.prefixAt 36 chains chainsExact with
    | .ok cut => pure cut
    | .error detail => throw (IO.userError s!"FAIL old cut: {detail}")
  match target.prefixOwn 36 chains chainsExact with
  | .error detail => throw (IO.userError s!"FAIL own cut: {detail}")
  | .ok ⟨own, imaged, _, zero, seeded, _⟩ =>
      IO.println s!"OPERATOR cut at 36: base {old.baseHeight}, budget = {budget old.snapshot}, cell 3 = {cell 3 old.snapshot}"
      IO.println s!"OWN      cut at 36: base {own.baseHeight}, budget = {budget own.snapshot}, cell 3 = {cell 3 own.snapshot}"
      require "the plant is live: the operator cut carries the forged budget" (budget old.snapshot == 964 + 777)
      require "the anchor comparison cannot see it: equal world roots at 36" (old.worldRoot == own.worldRoot)
      require "the own cut carries the honest budget" (budget own.snapshot == 964 && cell 3 own.snapshot == [36])
      let past (loaded : Loaded rootBytes) (height : Nat) : Nat :=
        ((loaded.atPrefixFrom none height).map budget).getD 0
      IO.println s!"at 34: operator cut {past old 34}, own cut {past own 34}"
      require "operator past read at 34 shows the forgery" (past old 34 == 966 + 777)
      require "own past read at 34 does not" (past own 34 == 966)
      let ⟨store, reader⟩ ← match ← DurableHistoryStore.readerOf transport rootBytes target with
        | .ok sealed => pure sealed
        | .error detail => throw (IO.userError s!"FAIL reader: {detail}")
      let readAt (reader : Reader rootBytes store) (height : Nat) : IO (Nat × Nat) := do
        match ← reader.stateAt height with
        | .ok state => pure (state.baseHeight, budget state.snapshot)
        | .error refusal => throw (IO.userError s!"FAIL stateAt {height}: {refusal.message}")
      let ownBase := ownOf own zero (by rw [seeded, imaged, Image.ofAccepted_seed])
      let operator ← readAt reader 34
      let ownGenesis ← readAt (reader.ownOnly transport []) 34
      let ownAt38 ← readAt (reader.ownOnly transport [ownBase]) 38
      let ownAt34 ← readAt (reader.ownOnly transport [ownBase]) 34
      IO.println s!"Reader.stateAt 34: operator base {operator.1} budget = {operator.2}; own (none) base {ownGenesis.1} budget = {ownGenesis.2}"
      IO.println s!"Reader.ownOnly [own@36]: at 38 base {ownAt38.1} budget = {ownAt38.2}; at 34 base {ownAt34.1} budget = {ownAt34.2}"
      require "operator Reader at 34 resumes from the sealed 32 and shows the forgery" (operator == (32, 966 + 777))
      require "own Reader at 34 folds from the seed" (ownGenesis == (0, 966))
      require "own Reader at 38 resumes from the own base at 36" (ownAt38 == (36, 962))
      require "own Reader at 34 (below the own base) folds from the seed" (ownAt34 == (0, 966))
      IO.println "PASS consent-own plant: the sealed forgery shows on every operator path and on no own path"

end ConsentOwnPlant

def main (arguments : List String) : IO Unit := do
  match arguments with
  | [binary] => IO.FS.withTempDir fun directory => ConsentOwnPlant.run binary directory
  | _ => throw (IO.userError "usage: own-base-plant STORE-HELPER")
