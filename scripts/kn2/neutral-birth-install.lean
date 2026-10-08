/- KN2-NEUTRAL-BIRTHS executed probe, cluster (4): a policy installation births its
successor policy-source cell, and commits only when the install step the OLD source's law
admitted names it (`birth/<id>` ↦ the successor's exact post root).

A source-built genesis (subject 7 holds the factory's control capability 43, with a real
Ed25519 key from the fixture signer) is booted into a native Store.  Subject 7 installs a
successor of the factory's policy: the declaration is authored from the current head
(version+1, previous = the head's address), planned by `NativeHost.prepareLoaded`, signed,
assembled, and submitted through the real Host path `NativeHost.submitLoaded` on the light
opening (`submitInstallLight`: basis, admission on `Ground.ofBasis`, the served commit).

 control  the installation commits (`confirmed`), and the installed head is the successor;
 refusal  printed by name when a plant (plant-neutral-birth-install.sh) drops the newborn
          slot from the install step: `neutralBirthUnjudged <successor cell>`.

Usage: lake env lean --run scripts/kn2/neutral-birth-install.lean VERIFIER SIGN-PROBE STORE-BINARY -/
import Kernel.NativeHostGenesis
import Kernel.NativeHost
import Kernel.NativeHostLight

open Minidregg.Theory
open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.ResourceBirth
open Minidregg.Compiler
open Minidregg.Kernel

namespace NeutralBirthInstallProbe

def require (label : String) (yes : Bool) : IO Unit :=
  unless yes do throw (IO.userError s!"FAIL neutral birth install: {label}")

def sign (binary : System.FilePath) (seed : Nat) (frame : List UInt8) :
    IO (List UInt8 × List UInt8) :=
  IO.FS.withTempDir fun directory => do
    let framePath := directory / "frame.bin"
    let keyPath := directory / "public.bin"
    let sigPath := directory / "signature.bin"
    IO.FS.writeBinFile framePath frame.toByteArray
    let output ← IO.Process.output
      { cmd := binary.toString
        args := #[toString seed, framePath.toString, keyPath.toString, sigPath.toString] }
    require s!"fixture signer: {output.stderr}" (output.exitCode == 0)
    pure ((← IO.FS.readBinFile keyPath).toList, (← IO.FS.readBinFile sigPath).toList)

def tariff : CreationTariff := ⟨0, 0, 0, 0, 99, 0⟩

def hostTemplate : NativeHost.Config where
  deployment := ⟨⟨8500⟩, 10, 11, 12⟩
  federation := ⟨9⟩
  template := ⟨⟨5⟩, 100000, 10000, 64⟩
  tariff := tariff
  genesisHeight := 10
  expectedSeed := ⟨0⟩
  storage := { binary := "unused", root := "unused", key := "unused", checkpointEvery := 16 }
  signature := ⟨"unused"⟩

def profile := hostTemplate.profile

def genesis (creatorKey : List UInt8) : NativeHostGenesis.Config where
  deployment := hostTemplate.deployment
  federation := hostTemplate.federation
  tariff := tariff
  expectedSemantics := profile.semantics
  issuerEpoch := 2
  genesisHeight := 10
  factoryPredicate := .all []
  enrollments :=
    [⟨⟨7007, 2, 1, 7, creatorKey, 0, 100, none⟩, 7,
      ⟨41⟩, ⟨44⟩, ⟨46⟩, 100, .all []⟩]
  factoryController := ⟨⟨7⟩, ⟨43⟩⟩
  meterAllowance := fun _ => 10000000
  clockTickers := []
  tailBound := 1000
  clockGenesisNow := 0
  clockMaxStepSeconds := 300

def describe : NativeHostCodec.Outcome → String
  | .confirmed _ _ => "committed"
  | .charged _ receipt causeBytes =>
      let cause := match ObjectiveActivityReceiver.rejectCodec.decode causeBytes with
        | some typed => reprStr typed
        | none => s!"invalid canonical cause {repr causeBytes}"
      s!"charged failure at height {receipt.acceptedCount}: {cause}"
  | .refused _ phase detail _ =>
      s!"refused {String.fromUTF8! ⟨phase.toArray⟩}: {String.fromUTF8! ⟨detail.toArray⟩}"
  | .contention => "contention"
  | .unavailable detail => s!"unavailable {String.fromUTF8! ⟨detail.toArray⟩}"
  | .uncertain detail => s!"uncertain {String.fromUTF8! ⟨detail.toArray⟩}"
  | .absent => "absent"

def run (verifier signer storeBinary : System.FilePath) : IO Unit := do
  let (creatorPublic, _) ← sign signer 7 []
  let cfg := genesis creatorPublic
  let built ← match NativeHostGenesis.build profile cfg with
    | .error reason => throw (IO.userError s!"genesis build: {repr reason}")
    | .ok value => pure value
  IO.FS.withTempDir fun directory => do
    IO.FS.writeBinFile (directory / "key") ((List.range 32).map (fun i => UInt8.ofNat (i * 7 + 3))).toByteArray
    let storage : DurableReceiverIO.NativeConfig :=
      { binary := storeBinary, root := directory / "store", key := directory / "key", checkpointEvery := 16 }
    let host : NativeHost.Config :=
      { hostTemplate with
        expectedSeed := NativeHost.seedIdentity built.seed
        storage := storage
        signature := ⟨verifier⟩ }
    match ← DurableReceiverIO.bootstrap host.transport ResourceBirthCodec.rootBytes built.seed with
    | .error reason => throw (IO.userError s!"native bootstrap: {reason}")
    | .ok () => pure ()
    let opened ← match ← NativeHost.openExisting host with
      | .error reason => throw (IO.userError s!"native host open: {reason}")
      | .ok value => pure value
    let factory : PolicyId := ⟨host.deployment.factoryId⟩
    let some head := opened.authority.snapshot.currentHead factory
      | throw (IO.userError "factory has no policy head")
    let some old := CanonicalCellRegistry.loadPolicySource host.deployment.domain
        opened.directory.directory head.address
      | throw (IO.userError "factory policy source unavailable")
    let source := { old.record with
      version := head.version + 1
      previous := some head.address
      predicate := .any [.all []] }
    let declaration : PolicyInstallController.Declaration :=
      ⟨opened.authority.snapshot.cell.root, some head, 1, source⟩
    let bytes := PolicyInstallController.encodeDeclaration declaration
    let successor := CanonicalCellRegistry.policySourceCreate host.deployment.domain source
    IO.println s!"successor policy-source cell {successor.cellId}"
    let plan ← match NativeHost.prepareLoaded host opened (.install ⟨7⟩ ⟨43⟩ bytes) with
      | .error reason => throw (IO.userError s!"install plan: {reason}")
      | .ok value => pure value
    let signatures ← plan.slots.mapM fun slot => do
      let (_, signature) ← sign signer 7 slot.header
      pure signature
    let call ← match NativeHost.assemble plan signatures with
      | .error reason => throw (IO.userError s!"assemble: {reason}")
      | .ok value => pure value
    let light ← match ← NativeHostLight.start host with
      | .ok light => pure light
      | .error detail => throw (IO.userError s!"light open: {detail}")
    let outcome ← NativeHost.submitLoaded host opened light call
    let verdict := describe outcome
    IO.println s!"install submission: {verdict}"
    require s!"install commits (got {verdict})" (verdict == "committed")
    let reopened ← match ← NativeHost.openExisting host with
      | .error reason => throw (IO.userError s!"reopen: {reason}")
      | .ok value => pure value
    require "installed head is the successor"
      ((reopened.authority.snapshot.currentHead factory).map (·.version) == some source.version)
    require "successor source cell is live"
      ((CanonicalCellRegistry.loadPolicySource host.deployment.domain reopened.directory.directory
        (PolicyRecordCodec.digest source)).isSome)
    IO.println "PASS neutral birth install (control)"

end NeutralBirthInstallProbe

def main (args : List String) : IO Unit := do
  match args with
  | [verifier, signer, store] => NeutralBirthInstallProbe.run verifier signer store
  | _ => throw (IO.userError "usage: neutral-birth-install VERIFIER SIGN-PROBE STORE-BINARY")
