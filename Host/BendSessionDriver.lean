/- Current native session glue for BFV public source execution.
Uses actual NativeHost opened images, native command signing plans, admitted
source/key reads, ordinary opaque storage and independent current release.
Source authored WIP: shared next-cohort replay/Host dispatch and custody signer
route must qualify before an executable governed run is claimed. -/
import Host.BendReceiving
import Host.BendOwnerManifestJson
import Host.BendReturnReleaseAuthoring
import Kernel.BendKeyRegistration

namespace Minidregg.Host.BendSessionDriver
open Lean
open Minidregg.Compiler
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Theory
open Minidregg.Theory.Hyperdocument
open Minidregg.Theory.TypedAuthorization
open Minidregg.Kernel
open Minidregg.Kernel.DeclaredResourceController
set_option autoImplicit false

/-- Operator selected native context, never derived from physical request IDs.
Roots and current laws are rechecked by actual native read/store/release gates.
Compilation admission and physical executable SHA are external deployment pins. -/
structure Session where
  subject : SubjectId
  nonce : Nat
  sourceResource : Nat
  sourceCapability : CapabilityId
  sourceRoot : Digest
  sourceAtom : AtomId
  keyResource : Nat
  keyCapability : CapabilityId
  keyRoot : Digest
  keyAtom : AtomId
  resultResource : Nat
  resultCapability : CapabilityId
  resultRoot : Digest
  releaseCapability : CapabilityId
  audience : Digest
  generation : Nat
  purpose : String
  returnName : String
  predecessor : Digest
  capacity : List Nat
  compilerSHA256 : String
  physicalBinary : String
  physicalBinarySHA256 : String
  physicalTransformerSHA256 : String

/-- Custody receives canonical source-selected plans. Signatures are subsequently
rechecked by the actual native current-authority receivers. No Boolean signer
result is used. The client route must reuse its inspected plan signing operation. -/
structure Signer where
  nativePlan : NativeHostCodec.SigningPlan → IO (Except String (List (List UInt8)))
  returnPlan : BendReturnReleaseAuthoring.Plan → IO (Except String (List UInt8))

structure Prepared where
  private mk ::
  source : BendWorldProgramCodec.Artifact
  registered : BendKeyRecord.Registered
  definition : BendInvocation.ProgramIdentity
  invocation : Digest
  authority : Digest
  sourceRoot : Digest
  keyRoot : Digest
  resultRoot : Digest
  sourceTrace : WorldMethodTrace.Trace

def readCommand (s : Session) : Command :=
  { subject := s.subject, nonce := s.nonce
    targets := [
      { kind := .object, target := s.sourceResource, capability := s.sourceCapability
        schemaVersion := ContentResource.commandVersion
        expectedTargetRoot := s.sourceRoot, payload := .read },
      { kind := .object, target := s.keyResource, capability := s.keyCapability
        schemaVersion := ContentResource.commandVersion
        expectedTargetRoot := s.keyRoot, payload := .read },
      { kind := .object, target := s.resultResource, capability := s.resultCapability
        schemaVersion := ContentResource.commandVersion
        expectedTargetRoot := s.resultRoot, payload := .read }]
    run := none }

def invocationId (config : NativeHost.Config) (s : Session)
    (a : BendWorldProgramCodec.Artifact) : Digest :=
  (Sp800185Cshake256.hash "DREGG.BEND.AUTHORED-INVOCATION/v1".toUTF8.toList
    ((StreamCodec.product digestStream
      (StreamCodec.product TypedAuthorizationRequestCodec.subjectIdStream
      (StreamCodec.product StreamCodec.nat
      (StreamCodec.product digestStream
      (StreamCodec.product digestStream
      (StreamCodec.product StreamCodec.nat digestStream)))))).encode
      (config.deployment.domain, s.subject, s.nonce, BendWorldProgramCodec.artifactId a,
        BendInvocation.methodId a, s.generation, s.predecessor))).digest

def definition (a : BendWorldProgramCodec.Artifact) : BendInvocation.ProgramIdentity :=
  ⟨BendWorldProgramCodec.semanticId a, BendWorldProgramCodec.artifactId a,
    BendWorldProgramCodec.executionProgramId a, BendInvocation.methodId a, a.plan⟩

def foreignSHA (kind value : String) : Digest :=
  (Sp800185Cshake256.hash kind.toUTF8.toList value.toUTF8.toList).digest

/-- Current nonce/domain/method invocation identity precedes physical execution.
The eventual storage transaction includes output bytes and cannot define it. -/
def contextJson (s : Session) (p : Prepared) : Json :=
  Json.mkObj [
    ("semantic_id", .str (toString p.definition.semantic.value)),
    ("program_id", .str (toString p.definition.program.value)),
    ("method_id", .str (toString p.definition.method.value)),
    ("invocation", .str (toString p.invocation.value)),
    ("predecessor", .str (toString s.predecessor.value)),
    ("authority_snapshot", .str (toString p.authority.value)),
    ("tariff_id", .str (toString p.source.profile.charge.value)),
    ("canonical_charge", .arr (s.capacity.map (fun n => toJson n)).toArray)]

def signCommand (config : NativeHost.Config) (opened : NativeHost.Opened config)
    (signer : Signer) (command : Command) : IO (Except String SignedCommand) := do
  let .ok plan := NativeHost.prepareLoaded config opened
      (.invoke (commandCodec.encode command))
    | return .error "current native signing preparation refused"
  let .ok signatures ← signer.nativePlan plan
    | return .error "current native signing custody refused"
  match NativeHost.assemble plan signatures with
  | .ok (.invoke signed) => return .ok signed
  | _ => return .error "current native invocation assembly refused"

/-- Same admitted source/key/result observation; no raw caller-supplied store
or root is promoted to provenance. The observed data stays local to the driver. -/
def prepareContext (config : NativeHost.Config) (s : Session) (signer : Signer)
    (sourceBytes : List UInt8) (keyBytes : List UInt8) : IO (Except String Prepared) := do
  unless s.capacity.length == 10 && BendOwnerManifestJson.sha256Shape s.compilerSHA256 &&
      BendOwnerManifestJson.sha256Shape s.physicalBinarySHA256 &&
      BendOwnerManifestJson.sha256Shape s.physicalTransformerSHA256 &&
      BendWorldSource.nameValid s.returnName && !s.purpose.isEmpty do
    return .error "malformed native Bend session"
  let .ok opened ← NativeHost.openExisting config
    | return .error "current native image unavailable"
  let .ok signed ← signCommand config opened signer (readCommand s)
    | return .error "current source/key observation signing refused"
  return ← withAcceptedLoadedFrom config.deployment config.profile
    ⟨config.federation, NativeHost.logicalHeight config opened.durable⟩
    config.signature opened.durable (some opened.directory) signed
    (fun {command} prepared _shape accepted => do
      if enough : 2 < command.targets.length then
        let sourceIndex : Fin command.targets.length := ⟨0, by omega⟩
        let keyIndex : Fin command.targets.length := ⟨1, by omega⟩
        let resultIndex : Fin command.targets.length := ⟨2, enough⟩
        let some loaded := BendSourcePublication.lookupAccepted prepared accepted sourceIndex s.sourceAtom
          | return .error "current source atom lookup refused"
        let some registered := BendKeyRegistration.lookupAccepted prepared accepted keyIndex s.keyAtom
          | return .error "current key atom lookup refused"
        unless BendWorldProgramCodec.encode loaded.artifact == sourceBytes &&
            BendKeyRecord.encode registered == keyBytes &&
            registered.subject == s.subject &&
            registered.artifact == BendWorldProgramCodec.artifactId loaded.artifact &&
            registered.method == BendInvocation.methodId loaded.artifact &&
            registered.material.transformerSHA256 == s.physicalTransformerSHA256 do
          return .error "source/key/session exact material binding differs"
        return .ok {
          source := loaded.artifact, registered := registered
          definition := definition loaded.artifact
          invocation := invocationId config s loaded.artifact
          authority := prepared.authority.snapshot.cell.root
          sourceRoot := command.targets[sourceIndex].expectedTargetRoot
          keyRoot := command.targets[keyIndex].expectedTargetRoot
          resultRoot := command.targets[resultIndex].expectedTargetRoot
          sourceTrace := loaded.trace }
      else return .error "native source/key/result read layout refused")
    (fun _ => pure (.error "current source/key observation admission refused"))

def registerKey (config : NativeHost.Config) (s : Session) (signer : Signer)
    (source : BendWorldProgramCodec.Artifact) (material : BendKeyRecord.PublicMaterial) :
    IO (Except String (BendKeyRecord.Registered × NativeHostCodec.Receipt)) := do
  let registered : BendKeyRecord.Registered :=
    ⟨s.subject, BendWorldProgramCodec.artifactId source, BendInvocation.methodId source, material⟩
  let publication : BendKeyRegistration.Publication :=
    ⟨s.subject, s.nonce, s.sourceResource, s.sourceCapability, s.sourceRoot, s.sourceAtom,
      s.keyResource, s.keyCapability, s.keyRoot, registered⟩
  let .ok opened ← NativeHost.openExisting config
    | return .error "key registration native image unavailable"
  let command := BendKeyRegistration.command publication
  let .ok signed ← signCommand config opened signer command
    | return .error "key registration current signing refused"
  let received ← BendKeyRegistration.receiveLoaded config.deployment config.profile
    ⟨config.federation, NativeHost.logicalHeight config opened.durable⟩
    config.signature config.transport opened.durable publication signed
  match ← BendReceiving.sealStorage config command signed received with
  | .stored receipt => return .ok (registered, receipt)
  | .refused detail | .uncertain detail => return .error detail
  | .released _ _ => return .error "unexpected release during key registration"

def exactOpaqueResult (s : Session) (p : Prepared)
    (inputIds : List Digest) (completionBytes : List UInt8) : BendInvocation.Result :=
  { definition := p.definition
    execution := {
      invocation := p.invocation, predecessor := s.predecessor, authority := p.authority
      inputs := inputIds, tariff := p.source.profile.charge, capacity := s.capacity
      parameters := foreignSHA "DREGG.BEND.BFV.PARAMETERS-SHA256/v1"
        p.registered.material.parametersSHA256
      transformer := foreignSHA "DREGG.BEND.BFV.TRANSFORMER-SHA256/v1"
        p.registered.material.transformerSHA256 }
    effects := []
    result := {
      name := s.returnName, valueSchema := BendOpaqueResultReceiver.opaqueValueSchema
      encoding := foreignSHA "DREGG.BEND.BFV.COMPLETION-ENCODING/v1" p.registered.material.profile
      recipient := s.subject
      keyEpoch := BendKeyRecord.keyId p.registered
      audience := s.audience, generation := s.generation, bytes := completionBytes } }

/-- Reopen/recheck source/key/result at commit, then store only exact retained
completion bytes. Receiver authenticates native signatures/laws/ordinary charge.
The result is opaque; no accepted computation/effect/range/noise certificate. -/
private def commitOpaque (config : NativeHost.Config) (s : Session) (signer : Signer)
    (sourceBytes keyBytes : List UInt8) (previous : Prepared)
    (inputIds : List Digest) (completionBytes : List UInt8) :
    IO (Except String (BendInvocation.Result × NativeHostCodec.Receipt)) := do
  let .ok current ← prepareContext config s signer sourceBytes keyBytes
    | return .error "current source/key/result commit recheck refused"
  unless current.definition == previous.definition && current.invocation == previous.invocation &&
      current.authority == previous.authority && current.sourceRoot == previous.sourceRoot &&
      current.keyRoot == previous.keyRoot && current.resultRoot == previous.resultRoot &&
      BendKeyRecord.encode current.registered == BendKeyRecord.encode previous.registered &&
      BendWorldProgramCodec.encode current.source == BendWorldProgramCodec.encode previous.source do
    return .error "prepared native source/key/result context changed"
  let candidate := exactOpaqueResult s current inputIds completionBytes
  let publication : BendOpaqueResultReceiver.Publication :=
    ⟨s.subject, s.nonce + 1, s.sourceResource, s.sourceCapability, current.sourceRoot,
      s.sourceAtom, s.resultResource, s.resultCapability, current.resultRoot, candidate⟩
  let .ok opened ← NativeHost.openExisting config
    | return .error "opaque result native image unavailable"
  let .ok signed ← signCommand config opened signer (BendOpaqueResultReceiver.command publication)
    | return .error "opaque result current signing refused"
  match ← BendReceiving.storeOpaque config publication signed with
  | .stored receipt => return .ok (candidate, receipt)
  | .refused detail | .uncertain detail => return .error detail
  | .released _ _ => return .error "unexpected release during result custody"

/-- This token denotes the exact physical public replay check and native
context binding only. It cannot establish encrypted input range/noise/bitness. -/
structure CheckedPhysical where
  private mk ::
  bytes : List UInt8
  inputs : List Digest
  contextBytes : List UInt8
  keyId : Digest

def fileSHA256 (path : String) : IO (Except String String) := do
  let output ← IO.Process.output { cmd := "sha256sum", args := #[path] }
  if output.exitCode != 0 || !output.stderr.isEmpty then
    return .error "physical SHA256 helper refused"
  let value := String.ofList (output.stdout.toList.take 64)
  if BendOwnerManifestJson.sha256Shape value then return .ok value
  else return .error "physical SHA256 helper malformed output"

/-- The trusted local driver owns the supplied fresh snapshot directory.
The filesystem/process/config/executable selection remain native deployment
assumptions; this is not an attestation against a hostile host OS. -/
def checkPhysical (s : Session) (p : Prepared) (snapshot : String)
    (compilerBytes requestBytes completionBytes : List UInt8) :
    IO (Except String CheckedPhysical) := do
  let .ok binarySHA ← fileSHA256 s.physicalBinary
    | return .error "physical checker executable unavailable"
  unless binarySHA == s.physicalBinarySHA256 do
    return .error "physical checker differs from deployment pin"
  let root : System.FilePath := snapshot
  if ← root.pathExists then return .error "physical snapshot directory already exists"
  IO.FS.createDirAll root
  let compilerPath := root / "compiler.json"
  let requestPath := root / "request.json"
  let completionPath := root / "completion.json"
  IO.FS.writeBinFile compilerPath ⟨compilerBytes.toArray⟩
  IO.FS.writeBinFile requestPath ⟨requestBytes.toArray⟩
  IO.FS.writeBinFile completionPath ⟨completionBytes.toArray⟩
  let .ok compilerSHA ← fileSHA256 compilerPath.toString
    | return .error "compiler snapshot SHA unavailable"
  unless compilerSHA == s.compilerSHA256 do
    return .error "compiler snapshot differs from externally admitted source pin"
  let parsed : Except String Json := do
    let request ← Minidregg.Host.Json.parse (String.fromUTF8! ⟨requestBytes.toArray⟩)
    let context ← request.getObjVal? "context"
    unless context.compress == (contextJson s p).compress do
      throw "physical request native context differs"
    let material := p.registered.material
    unless (← (← request.getObjVal? "profile").getStr?) == material.profile &&
      (← (← request.getObjVal? "parameters_sha256").getStr?) == material.parametersSHA256 &&
      (← (← request.getObjVal? "transformer_sha256").getStr?) == material.transformerSHA256 &&
      (← (← request.getObjVal? "key_epoch").getStr?) == material.epochSHA256 &&
      (← Minidregg.Host.Json.decodeHex "public_key" (← request.getObjVal? "public_key")) ==
        material.publicKey do
      throw "physical request differs from registered native public material"
    match material.relinearizationKey with
    | none =>
        if (request.getObjVal? "relinearization_key").isOk then
          throw "unexpected physical relinearization key"
    | some key =>
        unless (← Minidregg.Host.Json.decodeHex "relinearization_key"
            (← request.getObjVal? "relinearization_key")) == key do
          throw "physical request relinearization key differs"
    pure request
  let .ok request := parsed | return .error "physical request registration/context binding refused"
  let output ← IO.Process.output {
    cmd := s.physicalBinary
    args := #["check", compilerPath.toString, requestPath.toString,
      completionPath.toString, s.compilerSHA256] }
  if output.exitCode != 0 || !output.stderr.isEmpty then
    return .error "independent physical ciphertext replay refused"
  unless (← IO.FS.readBinFile requestPath).toList == requestBytes &&
      (← IO.FS.readBinFile completionPath).toList == completionBytes &&
      (← IO.FS.readBinFile compilerPath).toList == compilerBytes do
    return .error "physical replay snapshot bytes changed"
  let ids : Except String (List Digest) := do
    let inputs ← (← request.getObjVal? "inputs").getArr?
    inputs.toList.mapM fun input => do
      let bytes ← Minidregg.Host.Json.decodeHex "input" input
      pure (Sp800185Cshake256.hash "DREGG.BEND.CIPHERTEXT-INPUT/v1".toUTF8.toList bytes).digest
  match ids with
  | .error detail => return .error detail
  | .ok inputIds => return .ok ⟨completionBytes, inputIds,
      (contextJson s p).compress.toUTF8.toList, BendKeyRecord.keyId p.registered⟩

def commitChecked (config : NativeHost.Config) (s : Session) (signer : Signer)
    (sourceBytes keyBytes : List UInt8) (previous : Prepared)
    (checked : CheckedPhysical) :
    IO (Except String (BendInvocation.Result × NativeHostCodec.Receipt)) :=
  if checked.contextBytes == (contextJson s previous).compress.toUTF8.toList &&
      checked.keyId == BendKeyRecord.keyId previous.registered then
    commitOpaque config s signer sourceBytes keyBytes previous checked.inputs checked.bytes
  else pure (.error "physical check belongs to a different native context/key")

/-- Durable result release returns the exact retained bytes or no bytes.
Storage receipt/root from a prior image is not a future release authorization. -/
def releaseExact (config : NativeHost.Config) (s : Session) (signer : Signer)
    (currentResultRoot : Digest) (candidate : BendInvocation.Result) :
    IO (Except String (NativeHostCodec.Receipt × List UInt8)) := do
  let spec : BendReturnRelease.Spec := {
    domain := config.deployment.domain, semantics := config.profile.semantics
    subject := s.subject, nonce := s.nonce + 2
    source := ⟨s.resultResource, currentResultRoot, BendInvocation.resultId candidate⟩
    destination := ⟨s.subject, candidate.result.keyEpoch, s.audience, s.generation, s.purpose⟩
    capability := s.releaseCapability }
  let .ok opened ← NativeHost.openExisting config
    | return .error "current release native image unavailable"
  let .ok plan := BendReturnReleaseAuthoring.prepareLoaded config opened spec
    | return .error "current release source/destination/law refused"
  let .ok signature ← signer.returnPlan plan
    | return .error "current release signature custody refused"
  let .ok ingress := BendReturnReleaseAuthoring.assemble plan signature
    | return .error "current release canonical signature assembly refused"
  match ← BendReceiving.release config ingress with
  | .released receipt bytes =>
      if bytes == candidate.result.bytes then return .ok (receipt, bytes)
      else return .error "durably released bytes differ from retained completion"
  | .refused detail | .uncertain detail => return .error detail
  | .stored _ => return .error "unexpected storage response during release"

/-- Source-owned custody inspection re-prepares the COMPLETE canonical plan
on the current image. Structural plan decoding is never permission to sign. -/
def signingInspection (config : NativeHost.Config) (kind : String)
    (bytes : List UInt8) : IO (Except String Json) := do
  let .ok opened ← NativeHost.openExisting config
    | return .error "Bend signing current image unavailable"
  if kind == "native" then
    let some supplied := NativeHostCodec.signingPlanCodec.decode bytes
      | return .error "noncanonical native Bend signing plan"
    unless (match supplied.finalizedDraft with | .invoke _ => true | _ => false) do
      return .error "Bend custody signs current invocation plans only"
    let .ok current := NativeHost.prepareLoaded config opened supplied.finalizedDraft
      | return .error "current native Bend signing plan refused"
    unless NativeHostCodec.signingPlanCodec.encode current == bytes do
      return .error "native Bend signing plan differs from current preparation"
    return .ok (Json.mkObj [
      ("type", .str "bend-current-native-plan-v1"),
      ("canonical", .str (Minidregg.Host.Json.encodeHex bytes)),
      ("slots", .arr (current.slots.map (fun slot =>
        Json.mkObj [("header", .str (Minidregg.Host.Json.encodeHex slot.header))])).toArray)])
  else if kind == "return" then
    let some supplied := BendReturnReleaseAuthoring.planCodec.decode bytes
      | return .error "noncanonical Bend return signing plan"
    let .ok current := BendReturnReleaseAuthoring.prepareLoaded config opened supplied.spec
      | return .error "current native Bend return signing preparation refused"
    unless BendReturnReleaseAuthoring.planCodec.encode current == bytes do
      return .error "Bend return signing plan differs from current preparation"
    return .ok (Json.mkObj [
      ("type", .str "bend-current-return-plan-v1"),
      ("canonical", .str (Minidregg.Host.Json.encodeHex bytes)),
      ("header", .str (Minidregg.Host.Json.encodeHex current.canonicalHeader))])
  else return .error "unknown Bend current plan kind"

/-- Existing native client holds Ed25519 custody. BFV sk is never supplied.
Both binaries and the operator's exact native config path are deployment pins. -/
structure Custody where
  client : String
  clientSHA256 : String
  nativeHost : String
  nativeHostSHA256 : String
  nativeConfigPath : String
  authoritySeedPath : String
  privateRoot : String

def clientSigner (custody : Custody) : IO (Except String Signer) := do
  let .ok clientPin ← fileSHA256 custody.client
    | return .error "Bend custody client unavailable"
  let .ok hostPin ← fileSHA256 custody.nativeHost
    | return .error "Bend custody Host unavailable"
  unless clientPin == custody.clientSHA256 && hostPin == custody.nativeHostSHA256 do
    return .error "Bend custody binary deployment pin differs"
  let fresh ← IO.Process.output {
    cmd := "mktemp", args := #["-d", "-p", custody.privateRoot, "bend-sign.XXXXXXXXXX"] }
  if fresh.exitCode != 0 || !fresh.stderr.isEmpty then
    return .error "Bend custody private snapshot allocation refused"
  let freshRoot := fresh.stdout.trimAscii.toString
  unless freshRoot.startsWith (custody.privateRoot ++ "/bend-sign.") do
    return .error "Bend custody snapshot path differs"
  let counter ← IO.mkRef (0 : Nat)
  let operate := fun (kind : String) (bytes : List UInt8) => do
    let sequence ← counter.modifyGet (fun n => (n, n + 1))
    let directory : System.FilePath := freshRoot
    let planPath := directory / s!"plan-{sequence}.bin"
    let runPath := directory / s!"sign-{sequence}"
    if ← planPath.pathExists then
      return (.error "Bend custody plan snapshot already exists" : Except String (List UInt8))
    IO.FS.writeBinFile planPath ⟨bytes.toArray⟩
    let output ← IO.Process.output { cmd := custody.client
      args := #["bend-session-sign", kind, "--host", custody.nativeHost,
        "--config", custody.nativeConfigPath, "--plan", planPath.toString,
        "--key", custody.authoritySeedPath, "--dir", runPath.toString] }
    if output.exitCode != 0 || !output.stderr.isEmpty then
      return .error "Bend current plan signing custody refused"
    unless (← IO.FS.readBinFile planPath).toList == bytes do
      return .error "Bend custody plan snapshot changed"
    let filename := if kind == "native" then "signatures.bin" else "signature.bin"
    return .ok (← IO.FS.readBinFile (runPath / filename)).toList
  return .ok {
    nativePlan := fun plan => do
      let .ok bytes ← operate "native" (NativeHostCodec.signingPlanCodec.encode plan)
        | return .error "Bend native detached signature custody refused"
      let codec := ResourceBirthCodec.strictCodec (StreamCodec.list bytesStream).toLawful
      match codec.decode bytes with
      | some signatures => return .ok signatures
      | none => return .error "Bend native detached signatures noncanonical"
    returnPlan := fun plan =>
      operate "return" (BendReturnReleaseAuthoring.planCodec.encode plan) }

theorem opaque_no_effects (s : Session) (p : Prepared) (ids : List Digest)
    (bytes : List UInt8) : (exactOpaqueResult s p ids bytes).effects = [] := rfl
theorem opaque_bytes_exact (s : Session) (p : Prepared) (ids : List Digest)
    (bytes : List UInt8) : (exactOpaqueResult s p ids bytes).result.bytes = bytes := rfl
#assert_axioms opaque_no_effects
#assert_axioms opaque_bytes_exact
end Minidregg.Host.BendSessionDriver
