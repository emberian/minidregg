/- Governed source storage and lookup through the actual resource receiver.
This stores source artifacts, not a claim that their programs executed or that
their compiler is correct. The returned receipt is the ordinary native durable
receipt; no source authority or computation receipt is manufactured here. -/
import Compiler.BendWorldProgramCodec
import Compiler.BendCoreAdmission
import Kernel.WorldMethodTrace

namespace Minidregg.Kernel.BendSourcePublication
open Minidregg.Compiler
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Theory
open Minidregg.Theory.CellRegistry
open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.Hyperdocument
open Minidregg.Kernel.DeclaredResourceController
open Minidregg.Kernel.DurableDataIntent
set_option autoImplicit false

def schema : Digest :=
  (Sp800185Cshake256.hash "DREGG.BEND.SOURCE-SCHEMA/v1".toUTF8.toList []).digest

structure Publication where
  subject : SubjectId
  nonce : Nat
  resource : Nat
  capability : CapabilityId
  expectedRoot : Digest
  artifact : BendWorldProgramCodec.Artifact

def atom (publication : Publication) : AtomId :=
  ⟨BendWorldProgramCodec.artifactId publication.artifact⟩

def target (publication : Publication) : Target :=
  { kind := .object
    target := publication.resource
    capability := publication.capability
    schemaVersion := ContentResource.commandVersion
    expectedTargetRoot := publication.expectedRoot
    payload := .content ⟨[.createAtom (atom publication) (.inlineObject schema)
      (BendWorldProgramCodec.encode publication.artifact)]⟩ }

def command (publication : Publication) : Command :=
  { subject := publication.subject
    nonce := publication.nonce
    targets := [target publication]
    run := none }

/-- Exact core checker/entry gate precedes ordinary governed source storage.
It is not a source-to-core or core-to-backend correspondence theorem. -/
def checkedArtifact (artifact : BendWorldProgramCodec.Artifact) : Bool :=
  match BendCoreAdmission.admit artifact.book with
  | .error _ => false
  | .ok core => (BendCoreAdmission.entry core artifact.entry).isOk

/-- Complete signed command equality, then ordinary current capability, law,
exact-preimage, charge and durable admission. No alternate authorization path. -/
def receiveLoaded {F : Type} [Field F] [DecidableEq F]
    (deployment : Deployment) (profile : CanonicalRuntimeProfile.Profile F)
    (ambient : Ambient) (native : CredentialSignatureIO.NativeConfig)
    (transport : DurableReceiverIO.Transport) (durable : Durable)
    (publication : Publication) (signed : SignedCommand) : IO ReceiveResult :=
  if BendWorldProgramCodec.wellFormed publication.artifact && checkedArtifact publication.artifact &&
      decide (signed.commandBytes = commandCodec.encode (command publication)) then
    DeclaredResourceController.receiveLoaded deployment profile ambient native transport durable signed
  else pure (.rejected .malformedCommand)

/-- A content-hash address remains an exact artifact address even if a writer
later edits/tombstones that atom: altered or retired content refuses lookup. -/
def lookup (store : ContentResource.ContentStore) (id : AtomId) :
    Option BendWorldProgramCodec.Artifact := do
  let record ← Hyperdocument.lookup store .atoms id
  if record.tombstonedAt.isSome then none else do
    let .inlineObject selectedSchema := record.kind | none
    if selectedSchema != schema then none else do
      let artifact ← BendWorldProgramCodec.decode record.payload
      if BendWorldProgramCodec.wellFormed artifact && checkedArtifact artifact &&
          decide (BendWorldProgramCodec.artifactId artifact = id.digest) then
        some artifact
      else none

structure Loaded where
  artifact : BendWorldProgramCodec.Artifact
  resource : Nat
  root : Digest
  atom : AtomId
  /-- Keep the actual admitted observation/dependencies, not a caller's root list. -/
  trace : WorldMethodTrace.Trace

/-- Source lookup after actual native observation admission. A pure lookup of
arbitrary bytes is never substituted for current observe authority. -/
def lookupAccepted {F : Type} [Field F] [DecidableEq F]
    {deployment : Deployment} {profile : CanonicalRuntimeProfile.Profile F}
    {ambient : Ambient} {durable : Durable} {invocation : Command}
    (prepared : PreparedInvocation deployment profile ambient durable invocation)
    {signed : SignedCommand} (accepted : AcceptedInvocation prepared signed)
    (index : Fin invocation.targets.length) (id : AtomId) : Option Loaded := do
  let target := invocation.targets[index]
  if target.payload != .read then none else do
    let store ← target.contentStore? (prepared.targets index).pre
    let artifact ← lookup store id
    pure ⟨artifact, target.target, target.expectedTargetRoot, id,
      WorldMethodTrace.ofAccepted prepared accepted⟩

theorem publication_no_execution_claim (publication : Publication) :
    (command publication).run = none := rfl

theorem publication_exact_source (publication : Publication) :
    (command publication).targets[0]?.map Target.payload =
      some (.content ⟨[.createAtom (atom publication) (.inlineObject schema)
        (BendWorldProgramCodec.encode publication.artifact)]⟩) := rfl

end Minidregg.Kernel.BendSourcePublication
