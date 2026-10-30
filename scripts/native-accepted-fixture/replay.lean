/-
# scripts/native-accepted-fixture/replay.lean -- one op-2 admission, re-run in Lean

Re-runs the admission the native Host ran for one retained call
(`NativeHost.submitInvokeLight`: `DeclaredResourceController.prepare` on a verified
`ServedBasis.Ground`, `PhysicalShape`, `DeclaredResourceController.admit` with the production
read oracle). The node prepares on the light ground of the request's declared keys; this
re-run prepares the SAME controller on the full ground of the Store prefix
(`Ground.full`, the prefix's own loaded directory and authority), and
`ResourceTransaction.prepare_light_full` is the agreement: the two grounds prepare alike on a
declared marker. A prefix whose directory or authority does not load is refused by name.
over a Store prefix, under the deployment's pinned settings. Signatures are checked by the
linked native kernel (`CredentialSignatureIO.Oracle.io_native`); `generate.sh` loads
`verify-shim.c` in front of it, which records every check, and writes the checks the pinned
verifier binary answers `verified` as the transcript `Fixtures.NativeAcceptedFixture` replays
without a process. VERIFIER names that binary (the config's legacy artifact path).

usage: lake env lean --run replay.lean DIR SETTINGS VERIFIER HEIGHT [doc]
  `doc` prints the projection of a member's document write
  (`Fixtures.NativeDocWriteFixtureProjection`) instead of the Objective acceptance's.
  DIR holds seed.bin, rec-1.bin .. rec-HEIGHT.bin (the Store's own frames), call.bin
  (the retained op-2 call) and, for an accepted call, host-record.bin (the record the
  Host appended after it).
prints `ACCEPTED record=<same|DIFFERENT> root=<world root after>` or `REFUSED <reason>`,
then the call's semantic projection (`PROJECTION key = value` lines,
`Fixtures.NativeAcceptedFixtureProjection`, the definition the fixture checks
against the hand-written authority), exit 0; any other outcome exits non-zero. The interpreter recurses deeply: run it
under `ulimit -s unlimited`.
-/
import Theory.Sp800185Cshake256Native
import Host.ClientConsentCore
import Kernel.ObjectiveBendAuthenticatedInputs
import Fixtures.NativeAcceptedFixtureProjection
import Fixtures.NativeDocWriteFixtureProjection
open Minidregg Minidregg.Compiler Minidregg.Kernel
open Minidregg.Compiler.DurableCheckpointCodec Minidregg.Kernel.DurableReceiver
open Minidregg.Kernel.DeclaredResourceController
open Minidregg.Fixtures.NativeAcceptedFixtureProjection (projectAccepted projectRefused reasonName receiptSubjects recordLegs)
open Minidregg.Fixtures.NativeDocWriteFixtureProjection (projectDocWrite)

def printProjection (lines : List (String × String)) : IO Unit :=
  for (key, value) in lines do IO.println s!"PROJECTION {key} = {value}"

def readBytes (p : System.FilePath) : IO (List UInt8) := do
  return (← IO.FS.readBinFile p).toList

def main (args : List String) : IO UInt32 := do
  let (dir, settingsPath, verifier, heightText, doc) ← match args with
    | [dir, settingsPath, verifier, heightText] => pure (dir, settingsPath, verifier, heightText, false)
    | [dir, settingsPath, verifier, heightText, "doc"] => pure (dir, settingsPath, verifier, heightText, true)
    | _ => IO.eprintln "usage: replay.lean DIR SETTINGS VERIFIER HEIGHT [doc]"; return 2
  let some height := heightText.toNat? | IO.eprintln "HEIGHT must be a number"; return 2
  let dir := System.FilePath.mk dir
  let settings ← Minidregg.Host.ClientConsentCore.loadSettings settingsPath
  let config := NativeHost.Config.ofInputs { settings.config.toInputs with signature := { binary := verifier } }
  let some seed := seedFrame.decode (← readBytes (dir / "seed.bin")) | IO.eprintln "seed.bin: noncanonical"; return 3
  let mut records := []
  for i in [1:height + 1] do
    let some record := recordFrame.decode (← readBytes (dir / s!"rec-{i}.bin"))
      | IO.eprintln s!"rec-{i}.bin: noncanonical"; return 3
    records := records ++ [record]
  let image : Image := Image.ofAccepted seed records
  unless NativeHost.seedIdentity seed == config.expectedSeed do
    IO.eprintln "the seed is not the deployment's genesis"; return 3
  let durable ← match DurableReceiverIO.loadImage ResourceBirthCodec.rootBytes (config.logStart seed) image with
    | .ok durable => pure durable
    | .error detail => IO.eprintln s!"image: {detail}"; return 4
  let call ← readBytes (dir / "call.bin")
  let some (.invoke signed) := NativeHostCodec.callCodec.decode call
    | IO.eprintln "call.bin is not an op-2 call"; return 5
  let some command := commandCodec.decode signed.commandBytes | IO.eprintln "noncanonical command"; return 5
  let ambient : Ambient := ⟨config.federation, NativeHost.logicalHeight config durable⟩
  let some directory := CredentialAuthorityDomainReceiver.loadDirectory durable
    | IO.eprintln "image: the directory does not load"; return 4
  let some authority := CredentialAuthorityDomainReceiver.loadDeployment config.deployment durable.snapshot
    | IO.eprintln "image: the deployment authority does not load"; return 4
  let ground : Minidregg.Compiler.ServedBasis.Ground config.deployment := .full durable directory authority
  match prepare config.deployment config.profile ambient ground command with
  | .error reason =>
      IO.println s!"REFUSED {repr reason}"
      printProjection (projectRefused (reasonName s!"{repr reason}")); return 0
  | .ok prepared =>
    if shape : PhysicalShape prepared then
      match ← admit config.signature prepared signed ObjectiveBendAuthenticatedInputs.oracle with
      | .error reason =>
          IO.println s!"REFUSED {repr reason}"
          printProjection (projectRefused (reasonName s!"{repr reason}")); return 0
      | .ok accepted =>
        let intent := accepted.dataIntent shape
        let record := recordFrame.encode (IntentRecord.ofIntent intent)
        let host ← readBytes (dir / "host-record.bin")
        let root := NativeHostCodec.worldRoot config.deployment.domain config.profile.semantics (image.append intent)
        IO.println s!"ACCEPTED record={if record == host then "same" else "DIFFERENT"} root={root.value}"
        if doc then
          printProjection (projectDocWrite config.deployment command (IntentRecord.ofIntent intent)
            (receiptSubjects accepted) (signedBytes ground.authority.domain config.profile.semantics signed) (recordLegs ground.view (IntentRecord.ofIntent intent)))
        else
          printProjection (projectAccepted config.deployment command (IntentRecord.ofIntent intent)
            (receiptSubjects accepted) (signedBytes ground.authority.domain config.profile.semantics signed) (recordLegs ground.view (IntentRecord.ofIntent intent)))
        return 0
    else
      IO.println "REFUSED physicalPreparation"
      printProjection (projectRefused "physicalPreparation"); return 0
