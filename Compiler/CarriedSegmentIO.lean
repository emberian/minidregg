/- Operator-local carry receiving boundary. The retained old executable audits
old ingress under its original profile. This process loads the same exact cut,
constructs the target through the shared durable executor, validates the actual
target native state, and verifies an independently pinned operator's edge.

No old Host starts a public socket here. Staging is distinct from active service
publication, which requires the infra writer-quiescence/atomic-switch protocol.
-/
import Kernel.CarriedSegment
import Kernel.NativeHostContext
import Compiler.RetainedArtifactIO
import Compiler.CredentialSignatureIO
import Compiler.ReceiptContinuityIO
import Compiler.DurableHistoryStore
import Kernel.NativeHistorySelection
import Lean

namespace Minidregg.Compiler.CarriedSegmentIO

open Lean
open Minidregg.Theory.TypedAuthorization
open Minidregg.Kernel
open Minidregg.Kernel.CarriedSegment
open Minidregg.Kernel.DurableReceiver
open Minidregg.Kernel.DurableDataIntent
open Minidregg.Compiler

set_option autoImplicit false

structure SourceCapsule where
  host : System.FilePath
  configuration : System.FilePath
  profile : System.FilePath
  signatureVerifier : System.FilePath
  storage : DurableReceiverIO.NativeConfig
  identity : CarriedSegment.Identity
  pins : CapsulePins

/-- Constructed only after the actual old executable has re-admitted its
retained journal, and that exact head/image has been loaded through its pinned
helper and old genesis/profile-rooted MAC chain. -/
structure AuditedSource where
  private mk ::
  capsule : SourceCapsule
  durable : DurableReceiverIO.Loaded ResourceBirthCodec.rootBytes
  auditTranscript : String

private def hexDigit (n : Nat) : Char :=
  Char.ofNat (if n < 10 then '0'.toNat + n else 'a'.toNat + n - 10)
private def hex (bytes : List UInt8) : String :=
  String.ofList (bytes.flatMap fun byte => [hexDigit (byte.toNat / 16), hexDigit (byte.toNat % 16)])
private def liftResult {α : Type} (result : Except String α) : IO α := IO.ofExcept result

def checkCapsule (capsule : SourceCapsule) : IO Unit := do
  if !capsule.pins.wellFormed then throw (IO.userError "malformed retained source capsule")
  for (path, pin) in [(capsule.host, capsule.pins.host),
      (capsule.storage.binary, capsule.pins.storageHelper),
      (capsule.signatureVerifier, capsule.pins.signatureVerifier),
      (capsule.configuration, capsule.pins.configuration),
      (capsule.profile, capsule.pins.profile)] do
    liftResult (← RetainedArtifactIO.checkedFile path (hex pin))
  let profile ← liftResult (Json.parse (← IO.FS.readFile capsule.profile))
  for (name, expected) in [("domain", capsule.identity.domain.value),
      ("semantics", capsule.identity.semantics.value),
      ("expectedSeed", capsule.identity.genesis.value)] do
    let text ← liftResult ((profile.getObjVal? name).bind Json.getStr?)
    if text != toString expected then throw (IO.userError "source capsule profile identity differs")

/-- Retain the original configuration byte-for-byte. Historical execution gets
only a private, derived physical-path overlay. Lean Json retains arbitrary-width
numbers; no float/string round trip is used. Every semantic field is the exact
parsed original value. Both helper binaries are separately artifact-pinned and
the resulting old profile must still equal the retained original profile. -/
def withExecutionConfig {α : Type} (capsule : SourceCapsule)
    (body : System.FilePath → IO α) : IO α := do
  let original ← liftResult (Json.parse (← IO.FS.readFile capsule.configuration))
  let _ ← liftResult original.getObj?
  for key in ["storageBinary", "storageRoot", "signatureBinary"] do
    let _ ← liftResult ((original.getObjVal? key).bind Json.getStr?)
  let substitutions := [("storageBinary", capsule.storage.binary.toString),
    ("storageRoot", capsule.storage.root.toString),
    ("checkpointKey", capsule.storage.key.toString),
    ("signatureBinary", capsule.signatureVerifier.toString)]
  let execution := substitutions.foldl
    (fun json entry => json.setObjVal! entry.1 (.str entry.2)) original
  IO.FS.withTempDir fun directory => do
    let path := directory / "execution-config.json"
    IO.FS.writeFile path execution.compress
    body path

private def sourceTransport (capsule : SourceCapsule) : DurableReceiverIO.Transport :=
  let storage := { capsule.storage with
    anchorIdentity := s!"domain:{capsule.identity.domain.value};semantics:{capsule.identity.semantics.value};seed:{capsule.identity.genesis.value}" }
  storage.transport
    (NativeHostCodec.logRoot0 capsule.identity.domain capsule.identity.semantics)
    ⟨SystemCell.physicalId capsule.identity.domain⟩

def auditSource (capsule : SourceCapsule) : IO (Except String AuditedSource) := do
  try
    checkCapsule capsule
    let profile ← withExecutionConfig capsule fun execution =>
      IO.Process.output { cmd := capsule.host.toString, args := #[execution.toString, "profile"] }
    if profile.exitCode != 0 || profile.stderr != "" then return .error "retained source profile invocation failed"
    if profile.stdout != (← IO.FS.readFile capsule.profile) then return .error "retained executable profile changed"
    let audit ← withExecutionConfig capsule fun execution =>
      IO.Process.output { cmd := capsule.host.toString, args := #[execution.toString, "audit"] }
    if audit.exitCode != 0 then return .error s!"retained source audit refused: {audit.stderr}"
    let durable ← liftResult (← DurableReceiverIO.load (sourceTransport capsule) ResourceBirthCodec.rootBytes)
    let expected := s!"audited {durable.height} accepted records: every signed ingress re-admitted at its original prefix"
    if (audit.stdout.splitOn "\n").head! != expected then
      return .error "source head differs from actual audited cut"
    if seedIdentity durable.image.seed != capsule.identity.genesis then return .error "source genesis differs"
    checkCapsule capsule
    return .ok ⟨capsule, durable, audit.stdout⟩
  catch error => return .error s!"source capsule refused: {error}"

/-- Internal receiving result. The public wire receiver must use the closed
neutral converter; no wire entry accepts a changes list. -/
structure Prepared (config : NativeHost.Config) where
  private mk ::
  source : AuditedSource
  body : Body
  changes : List (CellId × List UInt8)
  target : NativeHost.Opened config

def prepareDerived (config : NativeHost.Config) (source : AuditedSource)
    (trustedOperator : List UInt8) (body : Body)
    (derivedChanges : List (CellId × List UInt8)) : Except String (Prepared config) := do
  if body.sourceCapsule != source.capsule.pins then throw "source capsule differs from signed carry body"
  let identity : CarriedSegment.Identity :=
    ⟨config.deployment.domain, config.profile.semantics, config.expectedSeed⟩
  if identity != body.target then throw "target actual profile differs from carry body"
  let durable ← buildTarget source.capsule.identity trustedOperator source.durable body derivedChanges
  let opened ← NativeHost.validateLoaded config durable
  pure ⟨source, body, derivedChanges, opened⟩

structure Authorized (config : NativeHost.Config) where
  private mk ::
  prepared : Prepared config
  edge : EdgeSeal

def authorizePrepared (config : NativeHost.Config) (prepared : Prepared config)
    (trustedOperator : List UInt8) (signature : List UInt8) : IO (Except String (Authorized config)) := do
  let old := Minidregg.Compiler.ReceiptContinuityIO.current prepared.source.durable
  let next := Minidregg.Compiler.ReceiptContinuityIO.current prepared.target.durable
  let edge : EdgeSeal := ⟨prepared.body, pointOf prepared.target.durable,
    old.siblings, next.siblings, signature⟩
  if let .error detail := checkPublic prepared.source.capsule.identity trustedOperator edge then
    return .error detail
  -- The closed neutral receiver checks the target capsule before this call;
  -- no helper pathname is taken from the public edge.
  match ← CredentialSignatureIO.verify config.signature trustedOperator edge.signingBytes signature with
  | .error detail => return .error s!"operator signature unavailable: {repr detail}"
  | .ok false => return .error "operator did not authorize this exact carry edge"
  | .ok true => return .ok ⟨prepared, edge⟩

/-- Restartable provenance token for the exact retained source and authorized
carry prefix. The current suffix is not claimed admitted by this token: its
source-owned suffix verifier must establish that separate obligation. -/
structure PreservedPrefix (config : NativeHost.Config) (current : NativeHost.Durable) where
  private mk ::
  source : AuditedSource
  edge : EdgeSeal
  start : NativeHost.Opened config
  prefixExact : current.prefixImage start.durable.height = start.durable.image

/-- Only an actually audited and signature-authorized carry can mint this
binding. Registry reload reconstructs Authorized from its exact accepted event;
callers cannot supply an asserted provenance Boolean or an unrelated old image. -/
def bindPreservedPrefix (config : NativeHost.Config) (authorized : Authorized config)
    (current : NativeHost.Durable) : Except String (PreservedPrefix config current) := do
  let start := authorized.prepared.target
  if current.logStart != start.durable.logStart then throw "carried prefix target log identity differs"
  if current.height < start.durable.height then throw "carried prefix is beyond current history"
  if exact : current.prefixImage start.durable.height = start.durable.image then
    return ⟨authorized.prepared.source, authorized.edge, start, exact⟩
  else throw "carried prefix differs from the exact authorized history"

/-- Rebind an existing authenticated source to a later actual image. This
cannot change the origin, authorized edge or validated carry start. -/
def PreservedPrefix.rebind {config : NativeHost.Config} {current : NativeHost.Durable}
    (prior : PreservedPrefix config current) (next : NativeHost.Durable)
    (exact : next.prefixImage prior.start.durable.height = prior.start.durable.image) :
    PreservedPrefix config next := ⟨prior.source, prior.edge, prior.start, exact⟩

@[simp] theorem PreservedPrefix.rebind_source {config : NativeHost.Config}
    {current : NativeHost.Durable} (prior : PreservedPrefix config current)
    (next : NativeHost.Durable) (exact) :
    (prior.rebind next exact).source = prior.source := rfl

@[simp] theorem PreservedPrefix.rebind_edge {config : NativeHost.Config}
    {current : NativeHost.Durable} (prior : PreservedPrefix config current)
    (next : NativeHost.Durable) (exact) :
    (prior.rebind next exact).edge = prior.edge := rfl

@[simp] theorem PreservedPrefix.rebind_start {config : NativeHost.Config}
    {current : NativeHost.Durable} (prior : PreservedPrefix config current)
    (next : NativeHost.Durable) (exact) :
    (prior.rebind next exact).start = prior.start := rfl

def PreservedPrefix.rebindChecked {config : NativeHost.Config} {current : NativeHost.Durable}
    (prior : PreservedPrefix config current) (next : NativeHost.Durable) :
    Except String (PreservedPrefix config next) := do
  if next.logStart != prior.start.durable.logStart then throw "carried prefix target log identity differs"
  if next.height < prior.start.durable.height then throw "carried prefix is beyond target history"
  if exact : next.prefixImage prior.start.durable.height = prior.start.durable.image then
    return prior.rebind next exact
  else throw "carried prefix differs from retained authorization"

/-- Stage/resume only the exact authorized full image. An interrupted partial
stage can continue; a differing seed, prefix or extra record refuses. The normal
Store helper fsyncs its independent anchor before each acknowledgement. This
function never switches a live service or initializes a replacement genesis. -/
def stageAuthorized (config : NativeHost.Config) (authorized : Authorized config) :
    IO (Except String (NativeHost.Opened config)) := do
  try
    let planned := authorized.prepared.target.durable
    let transport := config.transport
    let _ ← transport.initializeSeed (DurableCheckpointCodec.seedFrame.encode planned.image.seed)
    let mut current ← liftResult (← DurableReceiverIO.load transport ResourceBirthCodec.rootBytes)
    if DurableReceiverCodec.seedStream.encode current.image.seed !=
        DurableReceiverCodec.seedStream.encode planned.image.seed then
      return .error "staged carry seed differs; refusing replacement"
    if current.height > planned.height then return .error "staged carry is beyond authorized head"
    -- The staged Store's records are read through its authenticated `Reader`,
    -- window by window, against the planned (in-memory, authorized) image.
    let ⟨_, reader⟩ ← liftResult (← DurableHistoryStore.readerOf transport
      ResourceBirthCodec.rootBytes current)
    let compared ← NativeHistorySelection.foldRange reader 1 current.height planned.image.accepted
      fun remaining window =>
        if window.length ≤ remaining.length &&
            window.map DurableReceiverCodec.intentStream.encode ==
              (remaining.take window.length).map DurableReceiverCodec.intentStream.encode then
          .ok (remaining.drop window.length)
        else .error "staged carry prefix differs from exact authorized history"
    if let .error detail := compared then return .error detail
    -- Reproducing an already audited prefix is privileged staging, never a
    -- public admission bypass. Live target admission retains its system tail law.
    let staging := { transport with systemCell := none }
    for record in planned.image.accepted.drop current.height do
      let some intent := record.bind? ResourceBirthCodec.rootBytes
        | return .error "authorized carry record lost exact root binding"
      match ← DurableReceiverIO.receiveLoadedDetailed staging ResourceBirthCodec.rootBytes current intent with
      | .exact _ appended => current := appended.next
      | .ordinary _ => return .error "carry stage interrupted or refused; recover exact stage before publication"
    if pointOf current != authorized.edge.targetStart then return .error "staged carry head differs from authorized edge"
    let opened ← liftResult (NativeHost.validateLoaded config current)
    return .ok opened
  catch error => return .error s!"carry stage refused: {error}"

end Minidregg.Compiler.CarriedSegmentIO
