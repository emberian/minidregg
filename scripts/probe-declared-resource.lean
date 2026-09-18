/-
Native ordinary invocation through the concrete declared-resource receiver.
The starting resource/authority/policy are explicit bootstrap fixtures; this
probe does not call that bootstrap a resource-birth admission. The joined birth
and delegation probe composes these same receiving APIs after their closures.
No private signature receipt, capability verdict or proposed post is supplied.
-/
import Kernel.DeclaredResourceController

open Minidregg.Theory
open Minidregg.Theory.CellState
open Minidregg.Theory.CellRegistry
open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.CredentialAuthorityState
open Minidregg.Theory.CredentialSigningKey
open Minidregg.Compiler
open Minidregg.Compiler.CanonicalPolicyAdmission
open Minidregg.Kernel

namespace DeclaredResourceProbe

def require (label : String) (condition : Bool) : IO Unit :=
  unless condition do throw (IO.userError s!"FAIL declared resource: {label}")

def requireSome {α : Type} (label : String) : Option α → IO α
  | some value => pure value
  | none => throw (IO.userError s!"FAIL declared resource: {label}")

def requireOk {ε α : Type} [Repr ε] (label : String) : Except ε α → IO α
  | .ok value => pure value
  | .error reason => throw (IO.userError s!"FAIL declared resource: {label}: {repr reason}")

def sign (signer : System.FilePath) (seed : Nat) (frame : List UInt8) :
    IO (List UInt8 × List UInt8) :=
  IO.FS.withTempDir fun directory => do
    let framePath := directory / "frame.bin"
    let keyPath := directory / "key.bin"
    let signaturePath := directory / "signature.bin"
    IO.FS.writeBinFile framePath frame.toByteArray
    let output ← IO.Process.output
      { cmd := signer.toString
        args := #[toString seed, framePath.toString, keyPath.toString, signaturePath.toString] }
    require "public-test-key signing executable"
      (output.exitCode == 0 && output.stdout == "" &&
        output.stderr == s!"PUBLIC TEST KEY: seed = [{seed}; 32]; anyone can reproduce this signing key.\n")
    pure ((← IO.FS.readBinFile keyPath).toList, (← IO.FS.readBinFile signaturePath).toList)

instance : Fact (Nat.Prime 65537) := ⟨by norm_num⟩

def profile : CanonicalRuntimeProfile.Profile (ZMod 65537) :=
  .source ⟨⟨5⟩, 100000, 10000⟩ ⟨65537⟩ 65537 inferInstance 15
    (PredOrder.noWrap_zmod (by decide))

def deployment : CanonicalCellRegistry.Deployment := ⟨⟨8400⟩, 10, 11, 12⟩
def ambient : DeclaredResourceController.Ambient := ⟨⟨9⟩, 10⟩
def targetId : Nat := 600
def capId : CapabilityId := ⟨42⟩

def key (subject : Nat) (publicKey : List UInt8) : KeyRecord where
  keyId := 7000 + subject
  keyEpoch := 2
  algorithm := CredentialSignatureAdmission.ed25519Algorithm
  subject := subject
  publicKey := publicKey
  activeFrom := 0
  activeUntil := 100
  revoked := false

def policy : PolicyRecord where
  policyId := ⟨targetId⟩
  version := 0
  domain := deployment.domain
  semantics := profile.semantics
  previous := none
  predicate := .eq "request/verb" 2

def owner : Capability .object where
  id := capId
  root := capId
  parent := none
  issuer := ⟨5⟩
  holder := .subject ⟨7⟩
  scope := ⟨{⟨targetId⟩}, {.mutateObject, .delegateObject}, 100000⟩
  notBefore := 0
  notAfter := 10000
  issuerEpoch := 2
  policyId := ⟨targetId⟩
  policyEpoch := 0
  ancestors := ∅
  channels := ∅

def targetPage : DeclaredEffectPageMaterializer.Page :=
  ⟨deployment.domain, targetId % DeclaredEffectPageMaterializer.shardCount,
    some ⟨.objectField ⟨targetId⟩ ⟨1⟩, 0⟩, none, none, none⟩

def targetCell : PackedCell CanonicalCellRegistry.registry :=
  ⟨.declaredObject, materialize DeclaredEffectPageMaterializer.materializer
    (DeclaredEffectPageMaterializer.stateOfOption (some targetPage))⟩

def seed (alice bob : KeyRecord) : IO DurableReceiver.Seed := do
  let entries : List CredentialAuthorityPageMaterializer.Entry :=
    [.subjectKey alice, .subjectKey bob, .issuerEpoch ⟨5⟩ 2,
      .policy ⟨targetId⟩ 0 0 (PolicyRecordCodec.digest policy),
      .capability .object ⟨owner, []⟩]
  let pages ← requireSome "source-routed authority fixture"
    (CredentialAuthorityDomain.runEdits deployment.domain []
      (entries.map fun entry => ⟨none, entry⟩))
  let empty : CredentialAuthorityDomain.Catalogue := ⟨deployment.domain, 0, []⟩
  let catalogue := CredentialAuthorityDomainReceiver.placedCatalogue empty
    (CredentialAuthorityDomainReceiver.placePages empty pages 2000)
  let sourceId := PolicySourceCell.physicalId deployment.domain (PolicyRecordCodec.digest policy)
  let source := CanonicalCellRegistry.policySourceCell policy
  pure
    { absentBytes := []
      cells :=
        [(deployment.authorityAnchor.catalogueCellId, CredentialAuthorityDomainReceiver.catalogueBytes catalogue),
         (⟨targetId⟩, ResourceBirthCodec.LifecycleImage.bytes _ (.live targetCell)),
         (⟨sourceId⟩, ResourceBirthCodec.LifecycleImage.bytes _ (.live source))] ++
          (catalogue.pages.zip pages).map fun (reference, page) =>
            (reference.cellId, CredentialAuthorityDomainReceiver.shardBytes page)
      available := fun _ => 10000000 }

def command (snapshot : CredentialAuthorityDomain.Snapshot) : DeclaredResourceController.Command :=
  { kind := .object
    target := targetId
    subject := ⟨7⟩
    capability := capId
    expectedAuthorityRoot := snapshot.cell.root
    schemaVersion := 1
    expectedTargetRoot := targetCell.payload.root
    nonce := 991
    actions := [.write (.objectField ⟨targetId⟩ ⟨1⟩) (some 0) 1] }

def signed (signer : System.FilePath) (snapshot : CredentialAuthorityDomain.Snapshot)
    (command : DeclaredResourceController.Command) (seed : Nat := 7) : IO DeclaredResourceController.SignedCommand := do
  let marker := DeclaredResourceController.operationMarker snapshot.domain profile.semantics command
  let makeEnvelope := fun root => do
    let wanted := DeclaredResourceController.request snapshot profile.semantics ambient command root
    let header ← requireOk "source-owned exact request signing header"
      (CredentialSignatureAdmission.signingHeader snapshot marker ⟨command.kind, wanted⟩)
    let (_, signature) ← sign signer seed (CredentialSignedEnvelopeController.headerCodec.encode header)
    pure (CredentialSignedEnvelopeController.envelopeCodec.encode ⟨header, signature⟩)
  pure
    { commandBytes := DeclaredResourceController.commandCodec.encode command
      targetEnvelope := ← makeEnvelope command.expectedTargetRoot
      authorityEnvelope := ← makeEnvelope snapshot.cell.root }

def rejected : DeclaredResourceController.ReceiveResult → Bool
  | .rejected _ | .transactionConflict => true
  | _ => false

def run (verifier signer nativeStore : System.FilePath) : IO Unit :=
  IO.FS.withTempDir fun directory => do
    let native : CredentialSignatureIO.NativeConfig := ⟨verifier⟩
    let transport := (DurableReceiverIO.NativeConfig.mk nativeStore (directory / "store")).transport
    let (aliceKey, _) ← sign signer 7 []
    let (bobKey, _) ← sign signer 8 []
    let initial ← seed (key 7 aliceKey) (key 8 bobKey)
    requireOk "physical bootstrap fixture" (← DurableReceiverIO.bootstrap transport ResourceBirthCodec.rootBytes initial)
    let durable ← requireOk "physical reopen" (← DurableReceiverIO.load transport ResourceBirthCodec.rootBytes)
    let authority ← requireSome "complete anchored authority load"
      (CredentialAuthorityDomainReceiver.loadDeployment deployment durable.snapshot)
    let cmd := command authority.snapshot
    let wire := DeclaredResourceController.commandCodec.encode cmd
    require "compact full-width root command" (wire.length < 2048)
    require "exact compact codec roundtrip" (decide (DeclaredResourceController.commandCodec.decode wire = some cmd))
    require "trailing bytes refuse" ((DeclaredResourceController.commandCodec.decode (wire ++ [0])).isNone)
    let input ← signed signer authority.snapshot cmd
    let before ← requireOk "read original physical bytes" (← transport.read)
    let call := DeclaredResourceController.receive deployment profile ambient native transport
    let altered := { cmd with actions := [.write (.objectField ⟨targetId⟩ ⟨1⟩) (some 0) 2] }
    require "same logical nonce retains marker after action tamper"
      (DeclaredResourceController.operationMarker deployment.domain profile.semantics cmd ==
        DeclaredResourceController.operationMarker deployment.domain profile.semantics altered)
    require "altered exact request refuses copied envelopes"
      (rejected (← call { input with commandBytes := DeclaredResourceController.commandCodec.encode altered }))
    let bob := { cmd with subject := ⟨8⟩ }
    require "unrelated valid enrolled signer cannot use Alice capability"
      (rejected (← call (← signed signer authority.snapshot bob 8)))
    let stale := { cmd with expectedTargetRoot := ⟨cmd.expectedTargetRoot.value + 1⟩ }
    require "stale target root refuses"
      (rejected (← call { input with commandBytes := DeclaredResourceController.commandCodec.encode stale }))
    let overbroad := { cmd with actions := [.write (.objectField ⟨targetId + 1⟩ ⟨1⟩) (some 0) 1] }
    require "out-of-target edit refuses"
      (rejected (← call { input with commandBytes := DeclaredResourceController.commandCodec.encode overbroad }))
    let policyAttempt := { cmd with actions := [.write (.programCode ⟨targetId⟩) none 1] }
    require "ordinary object editing cannot replace program or law"
      (rejected (← call { input with commandBytes := DeclaredResourceController.commandCodec.encode policyAttempt }))
    require "refusals preserve exact physical image" (decide ((← requireOk "read after refusals" (← transport.read)) = before))
    match ← call input with
    | .settlement (.confirmed _ _) => pure ()
    | _ => throw (IO.userError "FAIL declared resource: owner invocation did not confirm physical publication")
    let reopened ← requireOk "reopen committed exact image" (← DurableReceiverIO.load transport ResourceBirthCodec.rootBytes)
    let finalDirectory ← requireSome "reopened complete directory"
      (CredentialAuthorityDomainReceiver.loadDirectory reopened)
    let target ← requireSome "actual persisted target"
      (DeclaredResourceController.observeTarget deployment finalDirectory.directory cmd)
    let page ← requireSome "actual persisted target page"
      (DeclaredEffectPageMaterializer.pageAt target.pre.logical)
    require "reopened target has exact action result"
      (decide (page.lookup (.objectField ⟨targetId⟩ ⟨1⟩) = some 1))
    let afterAuthority ← requireSome "reopened complete authority"
      (CredentialAuthorityDomainReceiver.loadDeployment deployment reopened.snapshot)
    require "same publication persists the one authority marker"
      (isNullified afterAuthority.snapshot.cell
        (DeclaredResourceController.operationMarker deployment.domain profile.semantics cmd))
    match ← call input with
    | .replayed _ => pure ()
    | _ => throw (IO.userError "FAIL declared resource: exact retry did not replay before stale-root admission")
    match ← call { input with commandBytes := DeclaredResourceController.commandCodec.encode altered } with
    | .transactionConflict => pure ()
    | _ => throw (IO.userError "FAIL declared resource: same nonce changed ingress was not a replay conflict")
    IO.println "PASS declared resource: real native signatures + stored capability + selected physical policy source + exact page/authority tuple + durable publication/reopen/replay; tamper, unrelated signer, stale root, overbroad edit and object-to-program edit refuse. Bootstrap fixture only; no birth/delegation admission claimed."

end DeclaredResourceProbe

def main (arguments : List String) : IO Unit :=
  match arguments with
  | [verifier, signer, store] => DeclaredResourceProbe.run verifier signer store
  | _ => throw (IO.userError "usage: lean --run scripts/probe-declared-resource.lean VERIFIER TEST-SIGNER SQLITE-STORE")
