/- Actual governed storage of an opaque backend completion candidate.
The source observation and result write share the existing native admission,
current laws and durable CAS. This receipt proves storage, not computation,
plaintext validity, cryptographic soundness, or permission to decrypt. -/
import Kernel.BendSourcePublication
import Compiler.BendInvocation

namespace Minidregg.Kernel.BendOpaqueResultReceiver
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
  (Sp800185Cshake256.hash "DREGG.BEND.OPAQUE-RESULT-SCHEMA/v1".toUTF8.toList []).digest
def opaqueValueSchema : Digest :=
  (Sp800185Cshake256.hash "DREGG.BEND.OPAQUE-COMPLETION/v1".toUTF8.toList []).digest

structure Publication where
  subject : SubjectId
  nonce : Nat
  sourceResource : Nat
  sourceCapability : CapabilityId
  sourceRoot : Digest
  sourceAtom : AtomId
  resultResource : Nat
  resultCapability : CapabilityId
  resultRoot : Digest
  candidate : BendInvocation.Result

def atom (publication : Publication) : AtomId :=
  ⟨BendInvocation.resultId publication.candidate⟩

def command (publication : Publication) : Command :=
  { subject := publication.subject
    nonce := publication.nonce
    targets := [
      { kind := .object, target := publication.sourceResource
        capability := publication.sourceCapability
        schemaVersion := ContentResource.commandVersion
        expectedTargetRoot := publication.sourceRoot, payload := .read },
      { kind := .object, target := publication.resultResource
        capability := publication.resultCapability
        schemaVersion := ContentResource.commandVersion
        expectedTargetRoot := publication.resultRoot
        payload := .content ⟨[.createAtom (atom publication) (.inlineObject schema)
          (BendInvocation.encode publication.candidate)]⟩ }]
    run := none }

/-- Initial BFV input admission carries an honest-owner assumption. Explicitly
restrict this receiver to opaque candidate custody and no derived method effects.
The stored capacity vector is provenance; ordinary storage charges stay exact. -/
def candidateWellFormed (publication : Publication) : Bool :=
  decide (publication.candidate.effects = [] ∧
    publication.candidate.result.valueSchema = opaqueValueSchema ∧
    publication.candidate.result.recipient = publication.subject) &&
  BendWorldSource.nameValid publication.candidate.result.name

def candidateFitsArtifact (publication : Publication)
    (artifact : BendWorldProgramCodec.Artifact) : Bool :=
  BendInvocation.matchesArtifact publication.candidate artifact &&
  match artifact.profile.bounds[8]? with
  | none => false
  | some outputBound => decide (publication.candidate.result.bytes.length ≤ outputBound)

def sourceFromPrepared {F : Type} [Field F] [DecidableEq F]
    {deployment : Deployment} {profile : CanonicalRuntimeProfile.Profile F}
    {ambient : Ambient} {durable : Durable} {invocation : Command}
    (prepared : PreparedInvocation deployment profile ambient durable invocation)
    (publication : Publication) : Option BendWorldProgramCodec.Artifact :=
  if positive : 0 < invocation.targets.length then do
    let index : Fin invocation.targets.length := ⟨0, positive⟩
    let first := invocation.targets[index]
    if first.kind != .object || first.target != publication.sourceResource ||
        first.expectedTargetRoot != publication.sourceRoot || first.payload != .read then none else do
      let store ← first.contentStore? (prepared.targets index).pre
      BendSourcePublication.lookup store publication.sourceAtom
  else none

/-- Uses the real admitted preimage for source lookup, then passes the *original*
accepted intent to durability. It neither substitutes a charge nor a receipt.
The exact candidate bytes are in the signed native command and stored atom. -/
def receiveLoaded {F : Type} [Field F] [DecidableEq F]
    (deployment : Deployment) (profile : CanonicalRuntimeProfile.Profile F)
    (ambient : Ambient) (native : CredentialSignatureIO.NativeConfig)
    (transport : DurableReceiverIO.Transport) (durable : Durable)
    (publication : Publication) (signed : SignedCommand) : IO ReceiveResult :=
  if candidateWellFormed publication &&
      decide (signed.commandBytes = commandCodec.encode (command publication)) then
    withAcceptedLoaded deployment profile ambient native durable signed
      (fun prepared shape accepted => do
        match sourceFromPrepared prepared publication with
        | none => return .rejected .malformedCommand
        | some artifact =>
            if candidateFitsArtifact publication artifact then
              return .settlement (← DurableReceiverIO.receiveLoaded transport
                ResourceBirthCodec.rootBytes durable (accepted.dataIntent shape))
            else return .rejected .malformedCommand)
      pure
  else pure (.rejected .malformedCommand)

def lookup (store : ContentResource.ContentStore) (id : AtomId) :
    Option BendInvocation.Result := do
  let record ← Hyperdocument.lookup store .atoms id
  if record.tombstonedAt.isSome then none else do
    let .inlineObject selectedSchema := record.kind | none
    if selectedSchema != schema then none else do
      let result ← BendInvocation.decode record.payload
      if decide (BendInvocation.resultId result = id.digest ∧ result.effects = [] ∧
          result.result.valueSchema = opaqueValueSchema) then some result else none

theorem no_computation_receipt (publication : Publication) :
    (command publication).run = none := rfl

end Minidregg.Kernel.BendOpaqueResultReceiver
