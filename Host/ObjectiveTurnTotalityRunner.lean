/- Executable OB turn-totality pole. Replay retained native commands at
their exact durable prefixes, and check expressibility before advancing.
This runner never writes the Store. A refusal is counted, not a replay abort. -/
import Host.ClientConsentCore
import Kernel.HostRefinesWorld
import Kernel.DeployedBridge
import Kernel.DeployedHistory

namespace Minidregg.Host.ObjectiveTurnTotalityRunner

open Minidregg.Theory.TypedAuthorization
open Minidregg.Compiler
open Minidregg.Kernel
open Minidregg.Compiler.ResourceBirthCodec
open Minidregg.Kernel.World
open Minidregg.Kernel.DurableDataIntent
open Minidregg.Kernel.NativeHost

set_option autoImplicit false

abbrev DeployedH := History DeployedBridge.deployedR TransactionId StableEvent Digest

inductive Plant
  | none
  | dropAbsent
  | absentRefuses

structure Counts where
  ok : Nat := 0
  refused : Nat := 0
  seedlessCreates : Nat := 0
  statelessMembers : Nat := 0
  nonemptyAbsent : Nat := 0
  deriving Repr

def Counts.total (counts : Counts) : Nat := counts.ok + counts.refused

def Counts.add (a b : Counts) : Counts :=
  ⟨a.ok + b.ok, a.refused + b.refused,
    a.seedlessCreates + b.seedlessCreates, a.statelessMembers + b.statelessMembers,
    a.nonemptyAbsent + b.nonemptyAbsent⟩

/-- The measured expression itself. H is supplied by the caller; no history
or accounting is substituted in the core. -/
def checkIntent (H : DeployedH) (plant : Plant) (row : String) (index : Nat)
    (opened : Compiler.DurableReceiverIO.Loaded rootBytes) (intent : DataIntent rootBytes) :
    IO Counts := do
  let ordinary := HostRefinesWorld.Turn.ofLoaded DeployedBridge.bridge H opened intent
  match ordinary with
  | .error (.retiredCell offending) =>
    -- Diagnosis only: show the exact loaded tombstone and each element that
    -- can trigger retiredCell, without changing admission or derivation.
    for write in intent.writes do
      let bytes := opened.snapshot.canonicalBytes write.cellId
      if DeployedBridge.retiresCell bytes then
        IO.eprintln s!"OFFENDER {row} {index} write cell {write.cellId.value} first {write.cellId.value == offending} retired true retirement-kind untyped-lifecycle bytes {reprStr (bytes.map UInt8.toNat)} post-bytes {reprStr (write.canonicalPostBytes.map UInt8.toNat)}"
    for guard in intent.readGuards do
      let bytes := opened.snapshot.canonicalBytes guard.cellId
      if (TurnOfIntent.guardIds intent.writes intent.readGuards).contains guard.cellId.value &&
          DeployedBridge.retiresCell bytes then
        IO.eprintln s!"OFFENDER {row} {index} guard cell {guard.cellId.value} first {guard.cellId.value == offending} retired true retirement-kind untyped-lifecycle bytes {reprStr (bytes.map UInt8.toNat)} root-matches {guard.expectedRoot == opened.snapshot.model.roots guard.cellId}"
  | _ => pure ()
  let nonemptyAbsent := match ordinary with
    | .ok turn => if turn.absent.isEmpty then 0 else 1
    | .error _ => 0
  let measured : Except TurnOfIntent.Refusal (TurnOfIntent.DTurn DeployedBridge.deployedR Digest) :=
    match ordinary, plant with
    | .ok turn, .dropAbsent => .ok { turn with absent := [] }
    | .ok _, .absentRefuses =>
      TurnOfIntent.ofCells DeployedBridge.bridge H
        (HostRefinesWorld.cellsOf DeployedBridge.bridge opened.snapshot) (fun _ => true) intent
    | _, _ => ordinary
  match measured with
  | .ok turn =>
    -- Compute the required pins directly from the intent and loaded cells;
    -- do not call absentOf, so a lost mapping cannot make the pole blind.
    let guarded := TurnOfIntent.guardIds intent.writes intent.readGuards
    let missing := guarded.filter fun cell =>
      (HostRefinesWorld.cellsOf DeployedBridge.bridge opened.snapshot cell).isNone &&
        !turn.absent.contains cell
    if missing.isEmpty then
      IO.println s!"{row} {index} ok"
      (← IO.getStdout).flush
      return { ok := 1, nonemptyAbsent := nonemptyAbsent }
    else
      IO.println s!"{row} {index} refusal pin-missing {(reprStr missing).replace "\n" " "}"
      (← IO.getStdout).flush
      return { refused := 1, nonemptyAbsent := nonemptyAbsent }
  | .error reason =>
    IO.println s!"{row} {index} refusal {(reprStr reason).replace "\n" " "}"
    (← IO.getStdout).flush
    return { refused := 1, nonemptyAbsent := nonemptyAbsent }

/-- Coverage of the expected absence plants, decoded from the admitted
command and the actual prefix rather than inferred from totality's result. -/
def coverage (config : ObjectiveActivity.Config) (durable : Durable)
    (command : ObjectiveActivityReceiver.Command) : Counts :=
  match command.turn with
  | .create _ _ _ _ _ _ none _ _ => { seedlessCreates := 1 }
  | .registerDomain members _ _ _ _ =>
    { statelessMembers := (members.filter fun member =>
        match ObjectiveActivity.readState config durable.snapshot ⟨member.1⟩ with
        | .ok none => true
        | _ => false).length }
  | _ => {}

/-- Chronological Host replay. Non-OB records still pass native admission,
full record comparison, durable advance and successor validation. The pole
runs before advance, including for charged failures and seat commits. -/
def replay (H : DeployedH) (plant : Plant) (row : String) (config : Config)
    {current : Durable} (verified : NativeHostReplay.Verified config current)
    (counts : Counts) : List DurableReceiver.IntentRecord → IO Counts
  | [] => return counts
  | record :: rest => do
    let index := verified.opened.durable.image.accepted.length
    IO.eprintln s!"PHASE {row} {index} derive"
    let derived ← IO.ofExcept (← NativeHostReplay.deriveVerified verified
      (NativeHostReplay.historicalSourceEvent record.event).canonicalBytes)
    IO.eprintln s!"PHASE {row} {index} derived event-v{derived.intent.event.codecVersion} event-bytes {derived.intent.event.canonicalBytes.length} nullifier-byte-lengths {repr (derived.intent.nullifiers.map fun n => n.canonicalBytes.length)}"
    unless NativeHostReplay.recordMatches record derived.intent do
      throw (IO.userError s!"{row} {index} replay record mismatch")
    let measured ← match derived.kernel with
      | some (.activity ingress verdict _) => do
        IO.eprintln s!"PHASE {row} {index} totality"
        let measured ← checkIntent H plant row index verified.opened.durable verdict.intent
        let activityConfig := match verdict with
          | .accepted accepted => accepted.prepared.config
          | .failed failed => failed.gated.config
        pure (measured.add (coverage activityConfig verified.opened.durable ingress.command))
      | some (.seat _ accepted _) =>
        checkIntent H plant row index verified.opened.durable (SeatReceiver.intent accepted)
      | none => pure ({} : Counts)
    IO.eprintln s!"PHASE {row} {index} advance"
    let next ← IO.ofExcept (NativeHostReplay.advance verified.opened derived)
    let later ← match ← NativeHostReplay.extendVerified config verified.reader verified next with
      | .error failure =>
        throw (IO.userError s!"{row} replay {failure.index}: {failure.detail}")
      | .ok later => pure later
    replay H plant row config later (counts.add measured) rest

def runStore (H : DeployedH) (plant : Plant) (row path : String) : IO Counts := do
  IO.eprintln s!"PHASE {row} settings"
  let settings ← Minidregg.Host.ClientConsentCore.loadSettings path
  Minidregg.Host.ClientConsentCore.withPinnedSignature settings.config fun config => do
    IO.eprintln s!"PHASE {row} durable-load"
    let target ← IO.ofExcept (← DurableReceiverIO.load config.transport rootBytes)
    IO.eprintln s!"PHASE {row} reader {target.image.accepted.length}"
    let ⟨_, reader⟩ ← Minidregg.Host.ClientConsentCore.storeReader config target
    let initial ← IO.ofExcept (DurableReceiverIO.loadSeed rootBytes
      (config.logStart target.image.seed) target.image.seed)
    IO.eprintln s!"PHASE {row} genesis-verify"
    let verified ← match ← NativeHostReplay.verifyLoaded config reader initial with
      | .error failure =>
        throw (IO.userError s!"{row} genesis {failure.index}: {failure.detail}")
      | .ok verified => pure verified
    IO.eprintln s!"PHASE {row} replay"
    replay H plant row config verified {} target.image.accepted

def rows : List String := ["activity", "objectrecord", "call", "send", "seats", "domain", "upgrade"]

/-- Manifest is a list of {row, config} objects. Multiple retained worlds per
row are supported. Missing rows, empty logs, unknown rows and duplicate
configuration paths refuse; no empty run can report success. -/
def run (H : DeployedH) (plant : Plant) (manifest : System.FilePath)
    (selectedRows : List String := rows) : IO UInt32 := do
  unless !selectedRows.isEmpty && selectedRows.all rows.contains do
    throw (IO.userError "unknown or empty row scope")
  if selectedRows.length != rows.length then
    IO.eprintln s!"SCOPE {repr selectedRows}"
  match plant with
  | .none => pure ()
  | .dropAbsent => IO.eprintln "PLANT drop-absent"
  | .absentRefuses => IO.eprintln "PLANT absent-refuses (all cells marked retired)"
  let json ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile manifest))
  let stores ← IO.ofExcept json.getArr?
  let mut seen : List String := []
  let mut totals : List (String × Counts) := selectedRows.map fun row => (row, {})
  let mut healthy := true
  for entry in stores do
    let row ← IO.ofExcept (entry.getObjValAs? String "row")
    let path ← IO.ofExcept (entry.getObjValAs? String "config")
    unless selectedRows.contains row do throw (IO.userError s!"row outside scope {row}")
    if seen.contains path then throw (IO.userError s!"duplicate config path {path}")
    seen := path :: seen
    try
      let counts ← runStore H plant row path
      totals := totals.map fun pair =>
        if pair.1 == row then (row, pair.2.add counts) else pair
    catch error =>
      IO.eprintln s!"{row} replay-error {error}"
      healthy := false
  let mut total : Counts := {}
  for (row, counts) in totals do
    IO.println s!"ROW {row} {counts.total} ok {counts.ok} refused {counts.refused}"
    IO.eprintln s!"COVERAGE {row} seedless-create {counts.seedlessCreates} stateless-domain-member {counts.statelessMembers} nonempty-absent {counts.nonemptyAbsent}"
    if counts.total == 0 then
      IO.eprintln s!"{row} empty-row"
      healthy := false
    total := total.add counts
  IO.println s!"TOTAL {total.total} ok {total.ok} refused {total.refused}"
  return if healthy && total.refused == 0 then 0 else 1

end Minidregg.Host.ObjectiveTurnTotalityRunner

def main (arguments : List String) : IO UInt32 := do
  let invocation := match arguments with
    | [manifest] => some (Minidregg.Host.ObjectiveTurnTotalityRunner.Plant.none,
      manifest, Minidregg.Host.ObjectiveTurnTotalityRunner.rows)
    | ["--row", row, manifest] =>
      some (Minidregg.Host.ObjectiveTurnTotalityRunner.Plant.none, manifest, [row])
    | ["--plant-drop-absent", manifest] =>
      some (Minidregg.Host.ObjectiveTurnTotalityRunner.Plant.dropAbsent,
        manifest, Minidregg.Host.ObjectiveTurnTotalityRunner.rows)
    | ["--plant-drop-absent", "--row", row, manifest] =>
      some (Minidregg.Host.ObjectiveTurnTotalityRunner.Plant.dropAbsent, manifest, [row])
    | ["--plant-absent-refuses", manifest] =>
      some (Minidregg.Host.ObjectiveTurnTotalityRunner.Plant.absentRefuses,
        manifest, Minidregg.Host.ObjectiveTurnTotalityRunner.rows)
    | ["--plant-absent-refuses", "--row", row, manifest] =>
      some (Minidregg.Host.ObjectiveTurnTotalityRunner.Plant.absentRefuses, manifest, [row])
    | _ => none
  match invocation with
  | some (plant, manifest, selectedRows) =>
    try
      return ← Minidregg.Host.ObjectiveTurnTotalityRunner.run
        Minidregg.Kernel.DeployedHistory.history plant manifest selectedRows
    catch error =>
      IO.eprintln s!"objective-turn-totality: {error}"
      return (1 : UInt32)
  | none =>
    IO.eprintln "objective-turn-totality: usage: objective-turn-totality [--plant-drop-absent|--plant-absent-refuses] [--row ROW] MANIFEST.json"
    return 2
