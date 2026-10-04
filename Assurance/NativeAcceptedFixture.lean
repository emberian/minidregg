/-
# The first native Objective acceptance, named in Lean

The scratch world of `native/resource-client/objective-native-acceptance.py all`,
run with a native Host and clients built from this tree, accepted its first
Objective invocation (`objective-first`) and journaled it. This module runs THAT
admission again, inside Lean: the op-2 path of `NativeHost.submitLoadedVia`
(`prepareFrom` over the image's own directory, `PhysicalShape`, then
`DeclaredResourceController.admit` with the production read oracle
`ObjectiveBendAuthenticatedInputs.oracle`), over the Store prefix it was admitted
at, under the deployment's pinned config. Two things stand in for the process
boundary and nothing else does:

* the verifier: the oracle `.recorded transcript` (`CredentialSignatureIO.Oracle`),
  the triples the pinned Ed25519 verifier answered `verified` on during that
  admission. It exists only at `Id`; the Host's receivers run at `IO`, where the only
  oracle is the process (`Oracle.io_process`). Every receipt records the source that
  answered it (`first_receipts_recorded`). `scripts/check-native-transcripts.sh`
  re-submits every triple to the verifier built from this tree;
* the Store: its seed and log records, decoded with the current codecs and
  replayed through the canonical executor (`DurableReceiverIO.loadImage`).

What it proves (compiled evaluation, `#assert_compiled`; the evaluated definitions
are `@[irreducible]`, so neither the elaborator nor a proof ever unfolds the admission
or the deployed hash -- only the compiled evaluator runs them):
* `first_accepted`: the admission accepts, and the record of the accepted intent is
  byte for byte the record the native Host appended (`Accepted.journalExact`), and
  the world root after it is the root the Host reported (`Accepted.rootExact`);
* `refused_admission`: the same admission refuses the dishonest call `r01`
  (a validly signed command naming the package as its source) with
  `objectiveSource`, the Host's own refusal, on the image right after `first`.

The `NativeBinding` poles (`Assurance.PrivateEvaluatorCustodyJoin`):
* `first_binding` (satisfying): the descriptor `ofAccepted` builds over the accepted
  object binds to it;
* `refused_call_unbound` (refuting): the descriptor a caller would supply for the
  refused call -- its transaction and command bytes over the accepted successor --
  does not.

Regenerate the data (a wire or semantics change turns this module red, by design):
`scripts/native-accepted-fixture/generate.sh WORLD` after the acceptance driver ran
on a fresh world with this tree's binaries.
-/
import Assurance.PrivateEvaluatorCustodyJoin
import Assurance.NativeAcceptedFixtureData
import Kernel.NativeHostContext
import Kernel.ObjectiveBendAuthenticatedInputs
import Compiler.NativeHostCodec
import Theory.AssertCompiled

namespace Minidregg.Assurance.NativeAcceptedFixture
open Minidregg.Theory Minidregg.Theory.TypedAuthorization
open Minidregg.Compiler Minidregg.Compiler.DurableCheckpointCodec
open Minidregg.Kernel Minidregg.Kernel.DurableReceiver Minidregg.Kernel.DurableDataIntent
open Minidregg.Kernel.DeclaredResourceController
open Minidregg.Kernel.PrivateSuccessorCustody
open Minidregg.Assurance.PrivateEvaluatorCustodyJoin
open Minidregg.Assurance.NativeAcceptedFixtureData
set_option autoImplicit false

/-- Lowercase hex to bytes (accumulating: the records are ~100 KB). -/
def hexBytes (text : String) : List UInt8 :=
  go text.toList []
where
  nibble (c : Char) : Nat := if c.isDigit then c.toNat - '0'.toNat else c.toNat - 'a'.toNat + 10
  go : List Char → List UInt8 → List UInt8
    | a :: b :: rest, acc => go rest (UInt8.ofNat (nibble a * 16 + nibble b) :: acc)
    | _, acc => acc.reverse

/-- The verifier's recorded answers during the two admissions below. -/
@[irreducible] def transcript : CredentialSignatureIO.Transcript :=
  ⟨verifiedTriples.map fun (key, frame, signature) => (hexBytes key, hexBytes frame, hexBytes signature)⟩

/-- The deployment's pinned config (`w/deployment/pinned-config.json`, read the way
`Host.Main`'s `Settings.config` reads it). Its verifier binary is never run: the
admission below is handed `.recorded transcript`, not this config. -/
def config : NativeHost.Config where
  deployment := ⟨⟨pinDomain⟩, pinFactoryId, pinResourceBookId, pinAuthorityCellId⟩
  federation := ⟨pinFederation⟩
  template := ⟨⟨pinIssuer⟩, pinOwnerBudget, pinLifetime, CanonicalRuntimeProfile.defaultBirthSlack⟩
  tariff := ⟨pinTariffBase, pinTariffPerBirth, pinTariffPerGrant, pinTariffPerInitialPayloadByte,
    pinCollector, pinAsset⟩
  genesisHeight := pinGenesisHeight
  expectedSeed := ⟨pinExpectedSeed⟩
  storage := { binary := "", root := "", key := "" }
  signature := ⟨""⟩
  invocationBindings := (ObjectiveBendNativeAdmission.decodePolicy (hexBytes pinObjectivePolicyHex)).map
    fun policy => [(.objectiveMethod, ObjectiveBendNativeAdmission.encodePolicy policy)]

/-- The Store prefix the first invocation was admitted at. -/
def image : Option Image := do
  let seed ← seedFrame.decode (hexBytes seedHex)
  let records ← recordHexes.mapM fun record => recordFrame.decode (hexBytes record)
  pure ⟨seed, records⟩

/-- The signed command of an op-2 call. -/
def invoked (call : String) : Option SignedCommand :=
  match NativeHostCodec.callCodec.decode (hexBytes call) with
  | some (.invoke signed) => some signed
  | _ => none

/-- The Host's ambient at an image: its federation and logical height. -/
def ambientOf (durable : Durable) : Ambient := ⟨config.federation, NativeHost.logicalHeight config durable⟩

/-- `DeclaredResourceController.admit` as the Host calls it for op 2, with the
production read oracle -- the same definition, at `Id` instead of `IO`, its signature
checks answered by the recorded run (`Oracle.recorded`) instead of the process. -/
def admitRun {command : Command} {durable : Durable}
    (prepared : PreparedInvocation config.deployment config.profile (ambientOf durable) durable command)
    (signed : SignedCommand) : Except Reject (AcceptedInvocation prepared signed) :=
  Id.run (admit (.recorded transcript) prepared signed ObjectiveBendAuthenticatedInputs.oracle)

/-- An accepted op-2 call, with the Host's evidence of the same acceptance. -/
structure Accepted (signed : SignedCommand) (hostRecord : List UInt8) (hostRoot : Nat) where
  durable : Durable
  command : Command
  prepared : PreparedInvocation config.deployment config.profile (ambientOf durable) durable command
  shape : PhysicalShape prepared
  accepted : AcceptedInvocation prepared signed
  /-- The accepted intent's journal record is the Host's appended record. -/
  journalExact : recordFrame.encode (IntentRecord.ofIntent (accepted.dataIntent shape)) = hostRecord
  /-- The world root after it is the root the Host reported. -/
  rootExact : (NativeHostCodec.worldRoot config.deployment.domain config.profile.semantics
    (durable.image.append (accepted.dataIntent shape))).value = hostRoot

/-- The admission of `signed` over `durable`, run to its end. -/
def acceptAt (durable : Durable) (signed : SignedCommand) (hostRecord : List UInt8) (hostRoot : Nat) :
    Option (Accepted signed hostRecord hostRoot) := do
  let command ← commandCodec.decode signed.commandBytes
  let .ok prepared := prepareFrom config.deployment config.profile (ambientOf durable) durable
    (CredentialAuthorityDomainReceiver.loadDirectory durable) command | none
  if shape : PhysicalShape prepared then
    let .ok accepted := admitRun prepared signed | none
    if journal : recordFrame.encode (IntentRecord.ofIntent (accepted.dataIntent shape)) = hostRecord then
      if root : (NativeHostCodec.worldRoot config.deployment.domain config.profile.semantics
          (durable.image.append (accepted.dataIntent shape))).value = hostRoot then
        some ⟨durable, command, prepared, shape, accepted, journal, root⟩
      else none
    else none
  else none

def loadAt (image : Image) : Option Durable :=
  (DurableReceiverIO.loadImage ResourceBirthCodec.rootBytes (config.logStart image.seed) image).toOption

def firstSigned : Option SignedCommand := invoked firstCallHex

@[irreducible] def firstRun : Option (Σ signed : SignedCommand,
    Accepted signed (hexBytes firstRecordHex) firstWorldRoot) := do
  let image ← image
  let durable ← loadAt image
  let signed ← firstSigned
  let accepted ← acceptAt durable signed (hexBytes firstRecordHex) firstWorldRoot
  pure ⟨signed, accepted⟩

/-- **The first native Objective acceptance, re-run in Lean, accepts**, and its
record and world root are the native Host's. -/
theorem first_accepted : firstRun.isSome = true := by native_decide

@[irreducible] def first := firstRun.get first_accepted

/-- `first` is the run's value. Every compiled evaluation below goes through
`firstRun` (an `Option`) and never through `first`: were the run to stop accepting
(a wire or semantics change), `first_accepted` refuses by name and nothing else
evaluates `Option.get` of `none` (which the compiled evaluator turns into a crash). -/
theorem firstRun_eq : firstRun = some first := by
  unfold first; exact (Option.some_get first_accepted).symm

/-- The accepted object and its shape witness: a named point of `AcceptedInvocation`. -/
def firstAccepted := first.2.accepted
def firstShape := first.2.shape

/-- The sources that answered an accepted invocation's signature checks: one per
incidence (the authority leg, then each target leg). -/
def sourcesOf {signed : SignedCommand} {record : List UInt8} {root : Nat}
    (accepted : Accepted signed record root) : List CredentialSignatureIO.Source :=
  (accepted.accepted.checked none).receipt.source ::
    (List.finRange accepted.command.targets.length).map fun i =>
      (accepted.accepted.checked (some i)).receipt.source

def recordedOnly (sources : List CredentialSignatureIO.Source) : Bool :=
  sources.all (· == .transcript transcript) && decide (sources.length ≥ 2)

theorem first_receipts_recorded_run :
    firstRun.map (fun run => recordedOnly (sourcesOf run.2)) = some true := by
  native_decide

/-- **Every receipt of the accepted object records the recorded run as its source**
-- never the process: the accepted object says which oracle answered it. -/
theorem first_receipts_recorded : recordedOnly (sourcesOf first.2) = true := by
  have run := first_receipts_recorded_run
  rw [firstRun_eq, Option.map_some] at run
  exact Option.some.inj run

/-- The custody descriptor `ofAccepted` builds over it (no holders: the binding does
not depend on the holder configuration). -/
def firstDescriptor : Descriptor := ofAccepted firstAccepted firstShape 0 0 ⟨0⟩ [] 0 []

/-- **`NativeBinding`, satisfying pole**: a descriptor bound to an actual accepted
native invocation. -/
theorem first_binding : NativeBinding firstAccepted firstShape firstDescriptor :=
  ofAccepted_bound firstAccepted firstShape 0 0 ⟨0⟩ [] 0 []

/-! ## The refused call -/

def refusedSigned : Option SignedCommand := invoked refusedCallHex

/-- The admission's verdict on `r01` on the image right after `first` (the Host
refused it there). `some reason` = refused with `reason`. -/
def refusedRun : Option Reject := do
  let signed ← refusedSigned
  let ⟨_, accepted⟩ ← firstRun
  let durable ← loadAt (accepted.durable.image.append (accepted.accepted.dataIntent accepted.shape))
  let command ← commandCodec.decode signed.commandBytes
  let .ok prepared := prepareFrom config.deployment config.profile (ambientOf durable) durable
    (CredentialAuthorityDomainReceiver.loadDirectory durable) command | none
  if PhysicalShape prepared then
    match admitRun prepared signed with
    | .error reason => some reason
    | .ok _ => none
  else none

def isObjectiveSource : Option Reject → Bool
  | some .objectiveSource => true
  | _ => false

/-- **The same admission refuses `r01` with the Host's reason.** -/
theorem refused_admission : isObjectiveSource refusedRun = true := by native_decide

theorem refused_decodes : refusedSigned.isSome = true := by native_decide

@[irreducible] def refused := refusedSigned.get refused_decodes

theorem refusedSigned_eq : refusedSigned = some refused := by
  unfold refused; exact (Option.some_get refused_decodes).symm

theorem refused_command_differs_run :
    (do let run ← firstRun; let call ← refusedSigned
        pure (decide (call.commandBytes ≠ run.1.commandBytes))) = some true := by
  native_decide

theorem refused_command_differs : refused.commandBytes ≠ first.1.commandBytes := by
  have run := refused_command_differs_run
  rw [firstRun_eq, refusedSigned_eq] at run
  exact of_decide_eq_true (Option.some.inj run)

/-- `descriptor` keyed to another call: its transaction and its command bytes. -/
def rekeyed (descriptor : Descriptor) (invocation : TransactionId) (commandBytes : List UInt8) :
    Descriptor :=
  { descriptor with key := { descriptor.key with invocation := invocation, commandBytes := commandBytes } }

theorem rekeyed_commandBytes (descriptor : Descriptor) (invocation : TransactionId)
    (commandBytes : List UInt8) : (rekeyed descriptor invocation commandBytes).key.commandBytes = commandBytes :=
  rfl

/-- The refused call's transaction. -/
def refusedInvocation : TransactionId :=
  transactionId config.deployment.domain config.profile.semantics
    ((commandCodec.decode refused.commandBytes).getD first.2.command)

/-- The descriptor a caller would supply for the refused call: its transaction and
command bytes, grafted onto the accepted successor. -/
def refusedDescriptor : Descriptor := rekeyed firstDescriptor refusedInvocation refused.commandBytes

/-- **`NativeBinding`, refuting pole**: the refused call's descriptor does not bind
to the accepted invocation. -/
theorem refused_call_unbound : ¬ NativeBinding firstAccepted firstShape refusedDescriptor :=
  fun binding => refused_command_differs
    ((rekeyed_commandBytes firstDescriptor refusedInvocation refused.commandBytes).symm.trans
      binding.commandExact)

/-! Each pin re-runs every oracle its theorem rests on (the first admission alone is
~40 s of evaluation), which exhausts the default heartbeat budget of one command. -/
set_option maxHeartbeats 4000000 in
#assert_compiled first_accepted
set_option maxHeartbeats 4000000 in
#assert_compiled first_binding
set_option maxHeartbeats 4000000 in
#assert_compiled first_receipts_recorded
#assert_axioms rekeyed_commandBytes
set_option maxHeartbeats 4000000 in
#assert_compiled refused_admission
set_option maxHeartbeats 4000000 in
#assert_compiled refused_command_differs
set_option maxHeartbeats 4000000 in
#assert_compiled refused_call_unbound

end Minidregg.Assurance.NativeAcceptedFixture
