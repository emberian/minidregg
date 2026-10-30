/-
# A member's document write, named in Lean

The scratch world of `native/resource-client/doc-write-native-acceptance.py`, run with a native
Host and clients built from one candidate, admitted two ordinary `doc append`s to a member's
document (`paper`, made by `doc new paper draft`) through the Host's public socket: the calls
`mini shell` makes, the surface of the tour's step 3.  This module runs THE SECOND of them again,
inside Lean: the op-2 path of `NativeHost.submitLoadedVia` (`prepare` over the image's own
directory, `PhysicalShape`, then `DeclaredResourceController.admit`), over the Store prefix it
was admitted at, under the deployment's pinned config.  The same two things stand in for the
process boundary and nothing else does (see `Fixtures.NativeAcceptedFixture`): the verifier
(`.recorded transcript`, re-submitted to the built verifier by `scripts/check-native-transcripts.sh`)
and the Store (its seed and records, decoded and replayed by `DurableReceiverIO.loadImage`).

What it proves (compiled evaluation, `#assert_compiled`):
* `write_accepted`: the admission accepts, and the record of the accepted intent is byte for byte
  the record the native Host appended, and the world root after it is the root the Host reported;
* `write_receipts_recorded`: every receipt of the accepted object records the recorded run as its
  source, never the process;
* `write_projection`: the re-run's SEMANTIC PROJECTION (who signed, which cells it writes, what it
  guards and spends, what the document holds afterwards, what it is charged) is the hand-written
  authority `Fixtures.NativeDocWriteFixtureAuthority`, read from what the member asked for;
* `tampered_refused` (refuting pole): the same admission over the same prefix, with one byte of the
  target leg's signature flipped, refuses at the leg's signature (`legSignature`) -- the recorded transcript answers for the
  original signature only.

Regenerate the data (a wire or semantics change turns this module red, by design):
`scripts/native-doc-write-fixture/generate.sh WORLD` after
`native/resource-client/doc-write-native-acceptance.py` ran on a fresh world with one candidate's binaries.
-/
import Fixtures.NativeDocWriteFixtureData
import Fixtures.NativeDocWriteFixtureProjection
import Fixtures.NativeDocWriteFixtureAuthority
import Kernel.NativeHostContext
import Kernel.ObjectiveBendAuthenticatedInputs
import Compiler.NativeHostCodec
import Theory.Sp800185Cshake256Native
import Theory.AssertCompiled

namespace Minidregg.Fixtures.NativeDocWriteFixture
open Minidregg.Theory Minidregg.Theory.TypedAuthorization
open Minidregg.Compiler Minidregg.Compiler.DurableCheckpointCodec
open Minidregg.Kernel Minidregg.Kernel.DurableReceiver Minidregg.Kernel.DurableDataIntent
open Minidregg.Kernel.DeclaredResourceController
open Minidregg.Fixtures.NativeDocWriteFixtureData
set_option autoImplicit false

/-- Lowercase hex to bytes (accumulating: the records are kilobytes). -/
def hexBytes (text : String) : List UInt8 :=
  go text.toList []
where
  nibble (c : Char) : Nat := if c.isDigit then c.toNat - '0'.toNat else c.toNat - 'a'.toNat + 10
  go : List Char → List UInt8 → List UInt8
    | a :: b :: rest, acc => go rest (UInt8.ofNat (nibble a * 16 + nibble b) :: acc)
    | _, acc => acc.reverse

/-- The verifier's recorded answers during the admission below. -/
@[irreducible] def transcript : CredentialSignatureIO.Transcript :=
  ⟨verifiedTriples.map fun (key, frame, signature) => (hexBytes key, hexBytes frame, hexBytes signature)⟩

/-- The deployment's pinned config (`w/deployment/pinned-config.json`, read the way `Host.Main`'s
`Settings.config` reads it; this world pins no Objective policy). Its verifier binary is never run:
the admission below is handed `.recorded transcript`. -/
def config : NativeHost.Config := NativeHost.Config.ofInputs {
  deployment := ⟨⟨pinDomain⟩, pinFactoryId, pinResourceBookId, pinAuthorityCellId⟩
  federation := ⟨pinFederation⟩
  template := ⟨⟨pinIssuer⟩, pinOwnerBudget, pinLifetime, CanonicalRuntimeProfile.defaultBirthSlack⟩
  tariff := ⟨pinTariffBase, pinTariffPerBirth, pinTariffPerGrant, pinTariffPerInitialPayloadByte,
    pinCollector, pinAsset⟩
  genesisHeight := pinGenesisHeight
  expectedSeed := ⟨pinExpectedSeed⟩
  storage := { binary := "", root := "", key := "" }
  signature := ⟨""⟩
  invocationBindings := none
  grainBirthTariff := pinGrainBirthTariff.map fun (base, perBirth) => ⟨base, perBirth⟩
  completionCustodianKey := pinCompletionCustodianKeyHex.map hexBytes }

/-- The Store prefix the write was admitted at. -/
def image : Option Image := do
  let seed ← seedFrame.decode (hexBytes seedHex)
  let records ← recordHexes.mapM fun record => recordFrame.decode (hexBytes record)
  pure (Image.ofAccepted seed records)

/-- The signed command of an op-2 call. -/
def invoked (call : String) : Option SignedCommand :=
  match NativeHostCodec.callCodec.decode (hexBytes call) with
  | some (.invoke signed) => some signed
  | _ => none

/-- The Host's ambient at an image: its federation and logical height. -/
def ambientOf (durable : Durable) : Ambient := ⟨config.federation, NativeHost.logicalHeight config durable⟩

/-- `DeclaredResourceController.admit` as the Host calls it for op 2, at `Id` instead of `IO`, its
signature checks answered by the recorded run instead of the process. -/
def admitRun {command : Command} {durable : Durable} {ground : Ground config.deployment}
    (prepared : PreparedInvocation config.deployment config.profile (ambientOf durable) ground command)
    (signed : SignedCommand) : Except Reject (AcceptedInvocation prepared signed) :=
  Id.run (admit (.recorded transcript) prepared signed ObjectiveBendAuthenticatedInputs.oracle)

/-- The full shape's ground of an image: its own decoded directory and authority. -/
def groundAt (durable : Durable) : Option (Ground config.deployment) := do
  let directory ← CredentialAuthorityDomainReceiver.loadDirectory durable
  let authority ← CredentialAuthorityDomainReceiver.loadDeployment config.deployment durable.snapshot
  pure (.full durable directory authority)

def loadAt (image : Image) : Option Durable :=
  (DurableReceiverIO.loadImage ResourceBirthCodec.rootBytes (config.logStart image.seed) image).toOption

/-- An accepted op-2 call, with the Host's evidence of the same acceptance. -/
structure Accepted (signed : SignedCommand) where
  durable : Durable
  ground : Ground config.deployment
  command : Command
  prepared : PreparedInvocation config.deployment config.profile (ambientOf durable) ground command
  shape : PhysicalShape prepared
  accepted : AcceptedInvocation prepared signed
  /-- The accepted intent's journal record is the Host's appended record. -/
  journalExact : recordFrame.encode (IntentRecord.ofIntent (accepted.dataIntent shape)) = hexBytes hostRecordHex
  /-- The world root after it is the root the Host reported. -/
  rootExact : (NativeHostCodec.worldRoot config.deployment.domain config.profile.semantics
    (durable.image.append (accepted.dataIntent shape))).value = hostWorldRoot

/-- The admission of `signed` over `durable`, run to its end. -/
def acceptAt (durable : Durable) (signed : SignedCommand) : Option (Accepted signed) := do
  let command ← commandCodec.decode signed.commandBytes
  let ground ← groundAt durable
  let .ok prepared := prepare config.deployment config.profile (ambientOf durable) ground command | none
  if shape : PhysicalShape prepared then
    let .ok accepted := admitRun prepared signed | none
    if journal : recordFrame.encode (IntentRecord.ofIntent (accepted.dataIntent shape)) = hexBytes hostRecordHex then
      if root : (NativeHostCodec.worldRoot config.deployment.domain config.profile.semantics
          (durable.image.append (accepted.dataIntent shape))).value = hostWorldRoot then
        some ⟨durable, ground, command, prepared, shape, accepted, journal, root⟩
      else none
    else none
  else none

def signedWrite : Option SignedCommand := invoked callHex

@[irreducible] def writeRun : Option (Σ signed : SignedCommand, Accepted signed) := do
  let image ← image
  let durable ← loadAt image
  let signed ← signedWrite
  let accepted ← acceptAt durable signed
  pure ⟨signed, accepted⟩

/-- **The member's document write, re-run in Lean, accepts**, and its record and world root are the
native Host's. -/
theorem write_accepted : writeRun.isSome = true := by native_decide

/-- The sources that answered an accepted invocation's signature checks: one per incidence (the
authority leg, then each target's authorizing signature). -/
def sourcesOf {signed : SignedCommand} (accepted : Accepted signed) : List CredentialSignatureIO.Source :=
  (accepted.accepted.receipt none).source ::
    (List.finRange accepted.command.targets.length).map fun i =>
      (accepted.accepted.receipt (some i)).source

def recordedOnly (sources : List CredentialSignatureIO.Source) : Bool :=
  sources.all (· == .transcript transcript) && decide (sources.length ≥ 2)

/-- **Every receipt of the accepted object records the recorded run as its source** -- never the
process: the accepted object says which oracle answered it. -/
theorem write_receipts_recorded :
    writeRun.map (fun run => recordedOnly (sourcesOf run.2)) = some true := by
  native_decide

open Minidregg.Fixtures.NativeAcceptedFixtureProjection (parseAuthority)
open Minidregg.Fixtures.NativeDocWriteFixtureProjection (projectDocWrite)
open Minidregg.Fixtures.NativeAcceptedFixtureProjection (receiptSubjects)

/-- The authority: hand-written, read from what the member asked for; no generator writes it. -/
def authority : List NativeAcceptedFixtureProjection.Line :=
  parseAuthority NativeDocWriteFixtureAuthority.text

/-- The re-run's projection of the accepted write, its record passed through `alter` first
(the run-dependent lanes relative to the call's length). -/
def projectionRunWith (alter : IntentRecord → IntentRecord) :
    Option (List NativeAcceptedFixtureProjection.Line) := do
  let ⟨_, run⟩ ← writeRun
  pure (projectDocWrite config.deployment run.command
    (alter (IntentRecord.ofIntent (run.accepted.dataIntent run.shape))) (receiptSubjects run.accepted)
    (hexBytes callHex).length
    (NativeAcceptedFixtureProjection.recordLegs run.ground.view
      (IntentRecord.ofIntent (run.accepted.dataIntent run.shape))))

/-- The re-run's projection of the accepted write. -/
def projectionRun : Option (List NativeAcceptedFixtureProjection.Line) := projectionRunWith id

/-- **The re-run means what the member asked for.**  The projection of the accepted write's record
(signer, signature checks, written cells, guards, nullifiers, the document's payload bytes, every
charge lane) is exactly the hand-written authority.  A regeneration that changes what the write
records turns this red until the authority is changed in its own reviewed commit. -/
theorem write_projection : projectionRun = some authority := by native_decide

/-- `record` with one charge lane a byte over its measured value. -/
def bumped (lane : Theory.ResourceCost.Lane) (record : IntentRecord) : IntentRecord :=
  { record with exactCharge := fun other =>
      if other = lane then record.exactCharge other + 1 else record.exactCharge other }

/-- **Teeth of the relational byte lines.** The authority states the turn and storage lanes as
their relations to the call (`call + k`), not as numbers; a record whose turn bytes, or whose
storage, is one byte off that relation is refused. -/
theorem turn_off_by_one_refused :
    projectionRunWith (bumped .turnBytes) ≠ some authority := by native_decide

theorem storage_off_by_one_refused :
    projectionRunWith (bumped .storageBytes) ≠ some authority := by native_decide

/-- `signed` with the last byte of its first target leg's signed envelope flipped. -/
def tamper (signed : SignedCommand) : SignedCommand :=
  { signed with targetEnvelopes := match signed.targetEnvelopes with
      | envelope :: rest => (envelope.dropLast ++ (envelope.getLast?.map (· ^^^ 1)).toList) :: rest
      | [] => [] }

/-- The admission of the tampered write over the same prefix: `true` when it refuses at a leg's
signature (`Reject.legSignature`), the check the flipped byte belongs to. -/
def tamperedRefuses : Option Bool := do
  let ⟨signed, run⟩ ← writeRun
  match admitRun run.prepared (tamper signed) with
  | .error (.legSignature ..) => some true
  | _ => some false

/-- **Refuting pole.** The same admission over the same prefix refuses the write with one byte of
its signature flipped: the recorded transcript answers for the original signature only. -/
theorem tampered_refused : tamperedRefuses = some true := by native_decide

/-! Each pin re-runs every oracle its theorem rests on, which exhausts the default heartbeat budget
of one command. -/
set_option maxHeartbeats 4000000 in
#assert_compiled write_accepted
set_option maxHeartbeats 4000000 in
#assert_compiled write_receipts_recorded
set_option maxHeartbeats 4000000 in
#assert_compiled write_projection
set_option maxHeartbeats 4000000 in
#assert_compiled tampered_refused
set_option maxHeartbeats 4000000 in
#assert_compiled turn_off_by_one_refused
set_option maxHeartbeats 4000000 in
#assert_compiled storage_off_by_one_refused

end Minidregg.Fixtures.NativeDocWriteFixture
