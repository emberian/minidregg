/- KN2-STORE-OPEN executed probe for the invoke route (opcode 2 on the light basis):
an invocation key the request's basis did not declare is refused BY NAME on a REAL
deployment Store, and the declared request prepares.

The Store is the accepted fixture's (`Assurance.NativeAcceptedFixtureData`): the pinned
genesis seed, bootstrapped under the pinned config, then the fixture's journal prefix
(`recordHexes`, each record bound by `IntentRecord.bind?` and committed by
`DurableReceiverIO.receive`), so the Store is at the height where the native Host
accepted `objective-first`. It is opened as the Host opens a served Store
(`NativeHostLight.start`), and every basis below is `Light.basis` of that opening.
The command is `objective-first`'s, decoded from the Host's call bytes.

 1. undeclared marker: a basis declaring the transaction id but not the operation
    marker's replay nullifier -> `DeclaredResourceController.prepare` refuses exactly
    `undeclaredMarker`;
 2. undeclared transaction: a basis declaring the marker but not the transaction id ->
    `withAcceptedOn` refuses exactly `undeclaredTransaction` (before the journal is read
    and before the signature is checked);
 3. control: the basis of `invocationKeys` (what `NativeHost.submitInvokeLight` reads)
    prepares (`.ok`, with its `PhysicalShape`); `recordedInvocation` on the declared basis answers "not recorded"; `withAcceptedOn`
    on it does not refuse `undeclaredTransaction`: with VERIFIER it is accepted; without,
    the missing verifier answers `unavailable` naming zero reply bytes (no panic).

Usage: lake env lean --run scripts/kn2/invoke-undeclared.lean STORE-HELPER [VERIFIER] -/
import Assurance.NativeAcceptedFixtureData
import Kernel.NativeHostLight
import Compiler.NativeHostCodec
import Kernel.ObjectiveBendAuthenticatedInputs

open Minidregg.Theory.TypedAuthorization
open Minidregg.Kernel
open Minidregg.Kernel.DurableReceiver
open Minidregg.Kernel.NativeHost
open Minidregg.Compiler
open Minidregg.Compiler.DurableCheckpointCodec
open Minidregg.Assurance.NativeAcceptedFixtureData

namespace InvokeUndeclared

def hexBytes (text : String) : List UInt8 :=
  go text.toList []
where
  nibble (c : Char) : Nat := if c.isDigit then c.toNat - '0'.toNat else c.toNat - 'a'.toNat + 10
  go : List Char → List UInt8 → List UInt8
    | a :: b :: rest, acc => go rest (UInt8.ofNat (nibble a * 16 + nibble b) :: acc)
    | _, acc => acc.reverse

/-- The deployment's pinned config, its Store and verifier paths supplied by the caller. -/
def config (storage : DurableReceiverIO.NativeConfig) (verifier : System.FilePath) : NativeHost.Config where
  deployment := ⟨⟨pinDomain⟩, pinFactoryId, pinResourceBookId, pinAuthorityCellId⟩
  federation := ⟨pinFederation⟩
  template := ⟨⟨pinIssuer⟩, pinOwnerBudget, pinLifetime, CanonicalRuntimeProfile.defaultBirthSlack⟩
  tariff := ⟨pinTariffBase, pinTariffPerBirth, pinTariffPerGrant, pinTariffPerInitialPayloadByte,
    pinCollector, pinAsset⟩
  genesisHeight := pinGenesisHeight
  expectedSeed := ⟨pinExpectedSeed⟩
  storage := storage
  signature := ⟨verifier⟩
  invocationBindings := (ObjectiveBendNativeAdmission.decodePolicy (hexBytes pinObjectivePolicyHex)).map
    fun policy => [(.objectiveMethod, ObjectiveBendNativeAdmission.encodePolicy policy)]

def require (label : String) (condition : Bool) : IO Unit :=
  unless condition do throw (IO.userError s!"FAIL invoke undeclared probe: {label}")

def verdict : DeclaredResourceController.ReceiveResult → String
  | .replayed _ => "replayed"
  | .rejected .undeclaredTransaction => "rejected undeclaredTransaction"
  | .rejected reason => s!"rejected {repr reason}"
  | .transactionConflict => "transactionConflict"
  | .unavailable detail => s!"unavailable {detail}"

def run (binary : System.FilePath) (verifier : Option System.FilePath) (directory : System.FilePath) :
    IO Unit := do
  IO.FS.writeBinFile (directory / "key") ((List.range 32).map (fun i => UInt8.ofNat (i * 7 + 3))).toByteArray
  let cfg := config { binary := binary, root := directory / "store", key := directory / "key", checkpointEvery := 16 }
    (verifier.getD "/nonexistent/verifier")
  let rootBytes := ResourceBirthCodec.rootBytes
  let some seed := seedFrame.decode (hexBytes seedHex)
    | throw (IO.userError "FAIL the fixture seed no longer decodes")
  match ← DurableReceiverIO.bootstrap cfg.transport rootBytes seed with
  | .error detail => throw (IO.userError s!"FAIL bootstrap: {detail}")
  | .ok () => pure ()
  -- The journal prefix `objective-first` was admitted at.
  for (hex, index) in recordHexes.zipIdx do
    let some record := recordFrame.decode (hexBytes hex)
      | throw (IO.userError s!"FAIL fixture record {index} no longer decodes")
    let some intent := record.bind? rootBytes
      | throw (IO.userError s!"FAIL fixture record {index} does not bind")
    match ← DurableReceiverIO.receive cfg.transport rootBytes intent 3 with
    | .confirmed _ _ => pure ()
    | .rejected reason => throw (IO.userError s!"FAIL commit of record {index}: rejected {repr reason}")
    | .unavailable detail => throw (IO.userError s!"FAIL commit of record {index}: unavailable {detail}")
    | .uncertain detail => throw (IO.userError s!"FAIL commit of record {index}: uncertain {detail}")
    | .contention => throw (IO.userError s!"FAIL commit of record {index}: contention")
  IO.println s!"store at height {recordHexes.length} (the fixture's prefix)"
  let light ← match ← NativeHostLight.start cfg with
    | .ok light => pure light
    | .error detail => throw (IO.userError s!"FAIL light open: {detail}")
  let some signed := match NativeHostCodec.callCodec.decode (hexBytes firstCallHex) with
      | some (.invoke signed) => some signed
      | _ => none
    | throw (IO.userError "FAIL objective-first no longer decodes as an invoke call")
  let some command := DeclaredResourceController.commandCodec.decode signed.commandBytes
    | throw (IO.userError "FAIL objective-first's command no longer decodes")
  let domain := cfg.deployment.domain
  let semantics := cfg.profile.semantics
  let keys := DeclaredResourceController.invocationKeys domain semantics command
  let basisOf (keys : DurableView.Keys) (label : String) := do
    match ← light.basis keys with
    | .ok basis => pure basis
    | .error detail => throw (IO.userError s!"FAIL {label} basis: {detail}")
  let declared ← basisOf keys "declared"
  let noMarker ← basisOf ⟨keys.transactions, []⟩ "marker-less"
  let noTransaction ← basisOf ⟨[], keys.nullifiers⟩ "transaction-less"
  let gDeclared : ServedBasis.Ground cfg.deployment := .ofBasis declared
  let gNoMarker : ServedBasis.Ground cfg.deployment := .ofBasis noMarker
  let gNoTransaction : ServedBasis.Ground cfg.deployment := .ofBasis noTransaction
  let ambient : DeclaredResourceController.Ambient := ⟨cfg.federation, cfg.genesisHeight + gDeclared.height⟩
  -- 1. the operation marker.
  match DeclaredResourceController.prepare cfg.deployment cfg.profile ambient gNoMarker command with
  | .error .undeclaredMarker => IO.println "refused as expected (undeclared marker): undeclaredMarker"
  | .error other => throw (IO.userError s!"FAIL a marker-less basis refused otherwise: {repr other}")
  | .ok _ => throw (IO.userError "FAIL an undeclared marker prepared")
  -- 2. the transaction id.
  let result ← DeclaredResourceController.withAcceptedOn cfg.deployment cfg.profile ambient cfg.signature
    gNoTransaction signed (fun _ _ _ => pure "accepted") (fun result => pure (verdict result))
    ObjectiveBendAuthenticatedInputs.oracle
  require s!"an undeclared transaction id refuses undeclaredTransaction (got {result})"
    (result == "rejected undeclaredTransaction")
  IO.println s!"refused as expected (undeclared transaction): {result}"
  -- 3. controls.
  match DeclaredResourceController.prepare cfg.deployment cfg.profile ambient gDeclared command with
  | .error reason => throw (IO.userError s!"FAIL the declared basis refused: {repr reason}")
  | .ok prepared =>
      require "the declared preparation has its physical shape"
        (decide (DeclaredResourceController.PhysicalShape prepared))
      IO.println "control (light, declared keys): prepares, with its physical shape"
  match DeclaredResourceController.recordedInvocation domain semantics command signed gDeclared with
  | .ok none => IO.println "control (declared transaction id): not recorded"
  | _ => throw (IO.userError "FAIL the declared transaction id did not answer `not recorded`")
  let declaredResult ← DeclaredResourceController.withAcceptedOn cfg.deployment cfg.profile ambient
    cfg.signature gDeclared signed (fun _ _ _ => pure "accepted") (fun result => pure (verdict result))
    ObjectiveBendAuthenticatedInputs.oracle
  require s!"a declared transaction id is not refused as undeclared (got {declaredResult})"
    (declaredResult != "rejected undeclaredTransaction")
  match verifier with
  | some _ =>
    require s!"with the pinned verifier the declared request is accepted (got {declaredResult})"
      (declaredResult == "accepted")
  | none =>
    -- No verifier: the signature check reaches a helper that cannot start, which answers
    -- `unavailable` naming zero reply bytes (it panicked the probe before 2026-10-07:
    -- scripts/kn2/coprocess-faults.lean).
    let absent := NativeCoprocess.Failure.render (.closed 0)
    require s!"with no verifier the declared request is unavailable as `{absent}` (got {declaredResult})"
      ((declaredResult.splitOn absent).length > 1)
  IO.println s!"control (withAcceptedOn, declared keys, verifier {verifier.isSome}): {declaredResult}"
  IO.println "PASS invoke undeclared: an undeclared marker and an undeclared transaction id, each refused by name; the declared request prepares and is accepted on the light ground"

end InvokeUndeclared

def main (arguments : List String) : IO Unit := do
  match arguments with
  | [binary] => IO.FS.withTempDir (InvokeUndeclared.run binary none)
  | [binary, verifier] => IO.FS.withTempDir (InvokeUndeclared.run binary (some verifier))
  | _ => throw (IO.userError "usage: lean --run scripts/kn2/invoke-undeclared.lean STORE-HELPER [VERIFIER]")
