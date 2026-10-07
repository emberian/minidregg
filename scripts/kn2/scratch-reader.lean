/- KN2-STORE-OPEN executed check of `DurableHistoryStore.scratchReader`: a portable
image (the accepted fixture's seed and journal prefix, decoded from bytes, with no
Store of its own) is written into an EMPTY Store under the deployment's pinned
config and read back as a history Reader of that real Store.

 - control: the Reader's head is at the image's height; every record verifies at its
   height and is byte for byte the image's record; `stateAt` reaches the head;
 - plant 1: the deployment's log start is not the one asked for -> refused by name;
 - plant 2: writing into a Store that is not empty -> refused by name (bootstrap);
 - plant 3: an image with one record's post bytes altered (its root no longer binds)
   -> refused by name, naming that record's height (its carried root check is bypassed
   for this plant, so the write path's own refusal is what is exercised);
 - plants 4, 5: the carried commitment (the native Host's reported world root after
   objective-first, at height 4) altered in its root or its height -> refused by name.

Usage: lake env lean --run scripts/kn2/scratch-reader.lean STORE-HELPER -/
import Assurance.NativeAcceptedFixtureData
import Kernel.NativeHostContext
import Compiler.DurableHistoryStore
import Compiler.NativeHostCodec
import Kernel.ObjectiveBendNativeAdmission

open Minidregg.Theory.TypedAuthorization
open Minidregg.Kernel
open Minidregg.Kernel.DurableReceiver
open Minidregg.Kernel.DurableDataIntent
open Minidregg.Compiler
open Minidregg.Compiler.DurableCheckpointCodec
open Minidregg.Assurance.NativeAcceptedFixtureData

namespace ScratchReader

def hexBytes (text : String) : List UInt8 :=
  go text.toList []
where
  nibble (c : Char) : Nat := if c.isDigit then c.toNat - '0'.toNat else c.toNat - 'a'.toNat + 10
  go : List Char → List UInt8 → List UInt8
    | a :: b :: rest, acc => go rest (UInt8.ofNat (nibble a * 16 + nibble b) :: acc)
    | _, acc => acc.reverse

def config (storage : DurableReceiverIO.NativeConfig) : NativeHost.Config where
  deployment := ⟨⟨pinDomain⟩, pinFactoryId, pinResourceBookId, pinAuthorityCellId⟩
  federation := ⟨pinFederation⟩
  template := ⟨⟨pinIssuer⟩, pinOwnerBudget, pinLifetime, CanonicalRuntimeProfile.defaultBirthSlack⟩
  tariff := ⟨pinTariffBase, pinTariffPerBirth, pinTariffPerGrant, pinTariffPerInitialPayloadByte,
    pinCollector, pinAsset⟩
  genesisHeight := pinGenesisHeight
  expectedSeed := ⟨pinExpectedSeed⟩
  storage := storage
  signature := ⟨""⟩
  invocationBindings := (ObjectiveBendNativeAdmission.decodePolicy (hexBytes pinObjectivePolicyHex)).map
    fun policy => [(.objectiveMethod, ObjectiveBendNativeAdmission.encodePolicy policy)]

def require (label : String) (condition : Bool) : IO Unit :=
  unless condition do throw (IO.userError s!"FAIL scratch reader: {label}")

def expectRefused (label : String) (needle : String)
    (result : Except String ((store : DurableHistory.StoreIdentity) ×
      DurableHistoryReader.Reader ResourceBirthCodec.rootBytes store)) : IO Unit :=
  match result with
  | .ok _ => throw (IO.userError s!"FAIL scratch reader: {label} was accepted")
  | .error detail => do
      IO.println s!"refused as expected ({label}): {detail}"
      require s!"{label} is refused by name ({needle})" ((detail.splitOn needle).length > 1)

/-- The first write of the first record whose post bytes can be altered. -/
def alter (record : IntentRecord) : IntentRecord :=
  match record.writes with
  | write :: rest =>
      let changed : DataWrite := { write with canonicalPostBytes := 7 :: write.canonicalPostBytes }
      { record with writes := changed :: rest }
  | [] => record

def run (binary : System.FilePath) (directory : System.FilePath) : IO Unit := do
  let base := config { binary := binary, root := directory / "unused", key := directory / "unused-key", checkpointEvery := 2 }
  let a ← base.scratch (directory / "a")
  let b ← base.scratch (directory / "b")
  let c ← base.scratch (directory / "c")
  let rootBytes := ResourceBirthCodec.rootBytes
  let some seed := seedFrame.decode (hexBytes seedHex)
    | throw (IO.userError "FAIL the fixture seed no longer decodes")
  let some records := recordHexes.mapM fun record => recordFrame.decode (hexBytes record)
    | throw (IO.userError "FAIL the fixture records no longer decode")
  let some first := recordFrame.decode (hexBytes firstRecordHex)
    | throw (IO.userError "FAIL the fixture's first record no longer decodes")
  -- The image through objective-first: its carried commitment is the root the native Host reported.
  let records := records ++ [first]
  let image : Image := ⟨seed, records⟩
  let cfg := a
  let logStart := cfg.logStart seed
  let rootOf := NativeHostCodec.worldRoot cfg.deployment.domain cfg.profile.semantics
  let carried : DurableHistoryStore.Commitment := ⟨records.length, ⟨firstWorldRoot⟩, rootOf⟩
  -- control
  match ← DurableHistoryStore.scratchReader cfg.physicalTransport rootBytes image logStart carried with
  | .error detail => throw (IO.userError s!"FAIL scratch reader of the fixture image: {detail}")
  | .ok ⟨_, reader⟩ =>
      require s!"the head is at the image's height ({reader.head.height})" (reader.head.height == records.length)
      for (record, index) in records.zipIdx do
        match ← reader.atHeight (index + 1) with
        | .error refusal => throw (IO.userError s!"FAIL record {index + 1}: {refusal.message}")
        | .ok verified =>
            require s!"record {index + 1} is the image's"
              (recordFrame.encode verified.record == recordFrame.encode record)
      match ← reader.stateAt records.length with
      | .error refusal => throw (IO.userError s!"FAIL stateAt the head: {refusal.message}")
      | .ok _ => pure ()
      IO.println s!"control: a Reader at height {reader.head.height}, every record verified and exact, stateAt the head"
  -- plant 1: another log start
  expectRefused "another log start" "log start"
    (← DurableHistoryStore.scratchReader b.physicalTransport rootBytes image ⟨logStart.value + 1⟩ carried)
  -- plant 2: the Store is not empty (store a holds the image)
  expectRefused "a non-empty Store" "scratch Store"
    (← DurableHistoryStore.scratchReader cfg.physicalTransport rootBytes image logStart carried)
  -- plant 3: an altered record
  let altered : Image := ⟨seed, records.map alter⟩
  require "the plant alters the first record" (records.head?.map (·.writes.length) != some 0)
  expectRefused "an altered record" "record 1 does not bind"
    (← DurableHistoryStore.scratchReader c.physicalTransport rootBytes altered logStart
      { carried with rootOf := fun _ => carried.worldRoot })
  -- plants 4 and 5: the carried commitment disagrees (root, height); nothing is written.
  let d ← base.scratch (directory / "d")
  expectRefused "another carried root" "is not the carried commitment"
    (← DurableHistoryStore.scratchReader d.physicalTransport rootBytes image logStart
      { carried with worldRoot := ⟨firstWorldRoot + 1⟩ })
  expectRefused "another carried height" "is not the carried height"
    (← DurableHistoryStore.scratchReader d.physicalTransport rootBytes image logStart
      { carried with height := records.length - 1 })
  IO.println "PASS scratch reader: a portable image is a real Store's Reader; another log start, a non-empty Store, an altered record, another carried root and another carried height are each refused by name"

end ScratchReader

def main (arguments : List String) : IO Unit := do
  match arguments with
  | [binary] => IO.FS.withTempDir (ScratchReader.run binary)
  | _ => throw (IO.userError "usage: lean --run scripts/kn2/scratch-reader.lean STORE-HELPER")
