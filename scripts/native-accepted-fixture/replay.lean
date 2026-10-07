/-
# scripts/native-accepted-fixture/replay.lean -- one op-2 admission, re-run in Lean

Re-runs the admission the native Host ran for one retained call
(`NativeHost.submitLoadedVia`, `.invoke`: `prepareFrom` over the image's directory,
`PhysicalShape`, `DeclaredResourceController.admit` with the production read oracle)
over a Store prefix, under the deployment's pinned settings, with the NATIVE verifier
named on the command line. `generate.sh` points that at `verify-logger.py`, which
records every triple the admission asks about: that record is the transcript
`Assurance.NativeAcceptedFixture` replays without a process.

usage: lake env lean --run replay.lean DIR SETTINGS VERIFIER HEIGHT
  DIR holds seed.bin, rec-1.bin .. rec-HEIGHT.bin (the Store's own frames), call.bin
  (the retained op-2 call) and, for an accepted call, host-record.bin (the record the
  Host appended after it).
prints `ACCEPTED record=<same|DIFFERENT> root=<world root after>` or `REFUSED <reason>`,
then the call's semantic projection (`PROJECTION key = value` lines,
`Assurance.NativeAcceptedFixtureProjection`, the definition the fixture checks
against the hand-written authority), exit 0; any other outcome exits non-zero. The interpreter recurses deeply: run it
under `ulimit -s unlimited`.
-/
import Host.ClientConsentCore
import Kernel.ObjectiveBendAuthenticatedInputs
import Assurance.NativeAcceptedFixtureProjection
open Minidregg Minidregg.Compiler Minidregg.Kernel
open Minidregg.Compiler.DurableCheckpointCodec Minidregg.Kernel.DurableReceiver
open Minidregg.Kernel.DeclaredResourceController
open Minidregg.Assurance.NativeAcceptedFixtureProjection (projectAccepted projectRefused reasonName receiptSubjects)

def printProjection (lines : List (String × String)) : IO Unit :=
  for (key, value) in lines do IO.println s!"PROJECTION {key} = {value}"

def readBytes (p : System.FilePath) : IO (List UInt8) := do
  return (← IO.FS.readBinFile p).toList

def main (args : List String) : IO UInt32 := do
  let [dir, settingsPath, verifier, heightText] := args
    | IO.eprintln "usage: replay.lean DIR SETTINGS VERIFIER HEIGHT"; return 2
  let some height := heightText.toNat? | IO.eprintln "HEIGHT must be a number"; return 2
  let dir := System.FilePath.mk dir
  let settings ← Minidregg.Host.ClientConsentCore.loadSettings settingsPath
  let config := { settings.config with signature := { binary := verifier } }
  let some seed := seedFrame.decode (← readBytes (dir / "seed.bin")) | IO.eprintln "seed.bin: noncanonical"; return 3
  let mut records := []
  for i in [1:height + 1] do
    let some record := recordFrame.decode (← readBytes (dir / s!"rec-{i}.bin"))
      | IO.eprintln s!"rec-{i}.bin: noncanonical"; return 3
    records := records ++ [record]
  let image : Image := ⟨seed, records⟩
  unless NativeHost.seedIdentity seed == config.expectedSeed do
    IO.eprintln "the seed is not the deployment's genesis"; return 3
  let durable ← match DurableReceiverIO.loadImage ResourceBirthCodec.rootBytes (config.logStart seed) image with
    | .ok durable => pure durable
    | .error detail => IO.eprintln s!"image: {detail}"; return 4
  let some (.invoke signed) := NativeHostCodec.callCodec.decode (← readBytes (dir / "call.bin"))
    | IO.eprintln "call.bin is not an op-2 call"; return 5
  let some command := commandCodec.decode signed.commandBytes | IO.eprintln "noncanonical command"; return 5
  let ambient : Ambient := ⟨config.federation, NativeHost.logicalHeight config durable⟩
  match prepareFrom config.deployment config.profile ambient durable
      (CredentialAuthorityDomainReceiver.loadDirectory durable) command with
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
        printProjection (projectAccepted config.deployment command (IntentRecord.ofIntent intent)
          (receiptSubjects accepted))
        return 0
    else
      IO.println "REFUSED physicalPreparation"
      printProjection (projectRefused "physicalPreparation"); return 0
