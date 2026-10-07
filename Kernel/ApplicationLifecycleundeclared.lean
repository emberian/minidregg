/- KN2 PORT-B executed probe: the lifecycle modules refuse a key the light basis did not
declare, BY NAME, on a REAL deployment Store (never read as absent / unconsumed).

The Store is the deployment's pinned genesis (`Assurance.NativeAcceptedFixtureData`: the
accepted-fixture seed under its pinned config), bootstrapped and opened as `Light.start`
opens a served Store, so every `Basis` below is a validated served state with a verified
footprint. Then, at the SAME height and head:
 1. a BEGIN whose transaction id the basis declares replays as "not recorded" (`none`);
    with an empty footprint the same BEGIN replays as the named refusal
    "lifecycle begin transaction identity undeclared";
 2. `DeclaredResourceController.prepare` of that BEGIN's command: with the BEGIN's
    `keys` declared it does not refuse `undeclaredMarker`; with an empty footprint it
    refuses exactly `undeclaredMarker`;
 3. the v3 launch markers (`BeginV3Admission.markersCurrentOf`): with their two
    nullifiers declared a first create finds them unconsumed (true); with an empty
    footprint `markersDeclaredOf` and `markersCurrentOf` are false.
Usage: lake env lean --run scripts/kn2/port-b-undeclared.lean STORE-HELPER -/
import Assurance.NativeAcceptedFixtureData
import Kernel.NativeHostLight
import Kernel.ApplicationLifecycleBeginReceiver
import Kernel.ApplicationLifecycleBeginV3Admission
import Kernel.ObjectiveBendNativeAdmission

open Minidregg.Theory.TypedAuthorization
open Minidregg.Kernel
open Minidregg.Kernel.NativeHost
open Minidregg.Compiler
open Minidregg.Compiler.DurableCheckpointCodec
open Minidregg.Assurance.NativeAcceptedFixtureData

namespace UndeclaredProbe

def hexBytes (text : String) : List UInt8 :=
  go text.toList []
where
  nibble (c : Char) : Nat := if c.isDigit then c.toNat - '0'.toNat else c.toNat - 'a'.toNat + 10
  go : List Char → List UInt8 → List UInt8
    | a :: b :: rest, acc => go rest (UInt8.ofNat (nibble a * 16 + nibble b) :: acc)
    | _, acc => acc.reverse

/-- The deployment's pinned config, its Store paths supplied by the caller. -/
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

def source : ApplicationLifecycleBegin.Source where
  kind := .start
  app := 20
  packageManifest := 21
  snapshotManifest := 22
  operationId := 5
  subject := ⟨1⟩
  managementSubject := ⟨1⟩
  capability := ⟨1⟩
  packageObserveCapability := ⟨2⟩
  before := ⟨0, 0, 0, 0⟩
  appRoot := ⟨1⟩
  packageRoot := ⟨2⟩
  packageDigest := ⟨3⟩
  imageIdentity := []
  processGeneration := 0
  processIdentity := []

def ingress (cfg : NativeHost.Config) : ApplicationLifecycleBeginIngress.Ingress where
  domain := cfg.deployment.domain
  semantics := cfg.profile.semantics
  source := source
  signed := ⟨[], [], [], []⟩
  packageObservationEnvelope := []

def binding : ApplicationLifecycleLaunchBinding.Binding where
  app := 20
  volume := ⟨1⟩
  packageRoot := ⟨2⟩
  choice := .create 0
  priorCreate := none
  commandDigest := ⟨3⟩

def require (label : String) (condition : Bool) : IO Unit :=
  unless condition do throw (IO.userError s!"FAIL undeclared probe: {label}")

def run (binary : System.FilePath) (directory : System.FilePath) : IO Unit := do
  IO.FS.writeBinFile (directory / "key") ((List.range 32).map (fun i => UInt8.ofNat (i * 7 + 3))).toByteArray
  let cfg := config { binary := binary, root := directory / "store", key := directory / "key", checkpointEvery := 16 }
  let some seed := seedFrame.decode (hexBytes seedHex)
    | throw (IO.userError "FAIL the fixture seed no longer decodes")
  match ← DurableReceiverIO.bootstrap cfg.transport ResourceBirthCodec.rootBytes seed with
  | .error detail => throw (IO.userError s!"FAIL bootstrap: {detail}")
  | .ok () => pure ()
  let light ← match ← NativeHostLight.start cfg with
    | .ok light => pure light
    | .error detail => throw (IO.userError s!"FAIL light open of the pinned genesis: {detail}")
  let ing := ingress cfg
  let declared ← match ← light.basis (ApplicationLifecycleBeginReceiver.keys ing) with
    | .ok basis => pure basis
    | .error detail => throw (IO.userError s!"FAIL declared basis: {detail}")
  let empty ← match ← light.basis ⟨[], []⟩ with
    | .ok basis => pure basis
    | .error detail => throw (IO.userError s!"FAIL empty basis: {detail}")
  -- 1. the transaction id.
  let gDeclared := ServedBasis.Ground.ofBasis declared
  let gEmpty := ServedBasis.Ground.ofBasis empty
  require "a declared, unrecorded BEGIN replays as not recorded"
    (match ApplicationLifecycleBeginReceiver.replay gDeclared ing with | none => true | _ => false)
  match ApplicationLifecycleBeginReceiver.replay gEmpty ing with
  | some (.error detail) =>
      IO.println s!"refused as expected (undeclared transaction): {detail}"
      require "the refusal names the undeclared transaction" ((detail.splitOn "undeclared").length > 1)
  | _ => throw (IO.userError "FAIL an undeclared transaction was not refused by name")
  -- 2. the operation marker, through the declared-resource controller.
  let command := ApplicationLifecycleBegin.command cfg.deployment.domain cfg.profile.semantics ing.source
  let ambient : DeclaredResourceController.Ambient := ⟨cfg.federation, cfg.genesisHeight + gDeclared.height⟩
  match DeclaredResourceController.prepare cfg.deployment cfg.profile ambient gEmpty command with
  | .error .undeclaredMarker => IO.println "refused as expected (undeclared marker): undeclaredMarker"
  | .error other => throw (IO.userError s!"FAIL empty footprint refused otherwise: {repr other}")
  | .ok _ => throw (IO.userError "FAIL an undeclared marker prepared")
  match DeclaredResourceController.prepare cfg.deployment cfg.profile ambient gDeclared command with
  | .error .undeclaredMarker => throw (IO.userError "FAIL a declared marker was refused as undeclared")
  | _ => IO.println "declared marker: not refused as undeclared"
  -- 3. the launch markers (a nullifier read from the spent map).
  let domain := cfg.deployment.domain
  let markers := ApplicationLifecycleBeginV3Admission.markerNullifiersOf domain (some binding)
  let withMarkers ← match ← light.basis ⟨[], markers⟩ with
    | .ok basis => pure basis
    | .error detail => throw (IO.userError s!"FAIL marker basis: {detail}")
  let gMarkers := ServedBasis.Ground.ofBasis withMarkers
  require "declared launch markers of a first create are unconsumed: current"
    (ApplicationLifecycleBeginV3Admission.markersCurrentOf gMarkers domain (some binding))
  require "undeclared launch markers are not declared"
    (!ApplicationLifecycleBeginV3Admission.markersDeclaredOf gEmpty domain (some binding))
  require "undeclared launch markers refuse (never read as unconsumed)"
    (!ApplicationLifecycleBeginV3Admission.markersCurrentOf gEmpty domain (some binding))
  IO.println "refused as expected (undeclared launch markers): markersDeclaredOf and markersCurrentOf are false"
  IO.println "PASS port-b undeclared: one undeclared transaction id and undeclared nullifiers, each refused by name"

end UndeclaredProbe

def main (arguments : List String) : IO Unit := do
  match arguments with
  | [binary] => IO.FS.withTempDir (UndeclaredProbe.run binary)
  | _ => throw (IO.userError "usage: lean --run scripts/kn2/port-b-undeclared.lean STORE-HELPER")
