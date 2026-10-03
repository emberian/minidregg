/- Ordinary current-authority custody of exact BFV public key material.
The source read and key write share the original native accepted DataIntent.
No key possession, ciphertext membership/range/noise or crypto proof is minted. -/
import Kernel.BendSourcePublication
import Compiler.BendKeyRecord

namespace Minidregg.Kernel.BendKeyRegistration
open Minidregg.Compiler
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Theory
open Minidregg.Theory.CellRegistry
open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.Hyperdocument
open Minidregg.Kernel.DeclaredResourceController
set_option autoImplicit false

def schema : Digest :=
  (Sp800185Cshake256.hash "DREGG.BEND.REGISTERED-KEY-SCHEMA/v1".toUTF8.toList []).digest

structure Publication where
  subject : SubjectId
  nonce : Nat
  sourceResource : Nat
  sourceCapability : CapabilityId
  sourceRoot : Digest
  sourceAtom : AtomId
  keyResource : Nat
  keyCapability : CapabilityId
  keyRoot : Digest
  registered : BendKeyRecord.Registered

def atom (p : Publication) : AtomId := ⟨BendKeyRecord.keyId p.registered⟩
def command (p : Publication) : Command :=
  { subject := p.subject, nonce := p.nonce
    targets := [
      { kind := .object, target := p.sourceResource, capability := p.sourceCapability
        schemaVersion := ContentResource.commandVersion
        expectedTargetRoot := p.sourceRoot, payload := .read },
      { kind := .object, target := p.keyResource, capability := p.keyCapability
        schemaVersion := ContentResource.commandVersion
        expectedTargetRoot := p.keyRoot
        payload := .content ⟨[.createAtom (atom p) (.inlineObject schema)
          (BendKeyRecord.encode p.registered)]⟩ }]
    run := none }

def fitsSource (p : Publication) (a : BendWorldProgramCodec.Artifact) : Bool :=
  decide (p.registered.subject = p.subject ∧
    p.registered.artifact = BendWorldProgramCodec.artifactId a ∧
    p.registered.method = BendInvocation.methodId a)

def sourceFromPrepared {F : Type} [Field F] [DecidableEq F]
    {deployment : Deployment} {profile : CanonicalRuntimeProfile.Profile F}
    {ambient : Ambient} {durable : Durable} {invocation : Command}
    (prepared : PreparedInvocation deployment profile ambient durable invocation)
    (p : Publication) : Option BendWorldProgramCodec.Artifact :=
  if positive : 0 < invocation.targets.length then do
    let index : Fin invocation.targets.length := ⟨0, positive⟩
    let first := invocation.targets[index]
    if first.kind != .object || first.target != p.sourceResource ||
        first.expectedTargetRoot != p.sourceRoot || first.payload != .read then none else do
      let store ← first.contentStore? (prepared.targets index).pre
      BendSourcePublication.lookup store p.sourceAtom
  else none

def receiveLoaded {F : Type} [Field F] [DecidableEq F]
    (deployment : Deployment) (profile : CanonicalRuntimeProfile.Profile F)
    (ambient : Ambient) (native : CredentialSignatureIO.NativeConfig)
    (transport : DurableReceiverIO.Transport) (durable : Durable)
    (p : Publication) (signed : SignedCommand) : IO ReceiveResult :=
  if decide (signed.commandBytes = commandCodec.encode (command p)) then
    withAcceptedLoaded deployment profile ambient native durable signed
      (fun prepared shape accepted => do
        match sourceFromPrepared prepared p with
        | none => return .rejected .malformedCommand
        | some source =>
            if fitsSource p source then
              return .settlement (← DurableReceiverIO.receiveLoaded transport
                ResourceBirthCodec.rootBytes durable (accepted.dataIntent shape))
            else return .rejected .malformedCommand)
      pure
  else pure (.rejected .malformedCommand)

def lookup (store : ContentResource.ContentStore) (id : AtomId) :
    Option BendKeyRecord.Registered := do
  let record ← Hyperdocument.lookup store .atoms id
  if record.tombstonedAt.isSome then none else do
    let .inlineObject selected := record.kind | none
    if selected != schema then none else do
      let key ← BendKeyRecord.decode record.payload
      if decide (BendKeyRecord.keyId key = id.digest) then some key else none

/-- Called with a real native observation token; no raw store is exported. -/
def lookupAccepted {F : Type} [Field F] [DecidableEq F]
    {deployment : Deployment} {profile : CanonicalRuntimeProfile.Profile F}
    {ambient : Ambient} {durable : Durable} {invocation : Command}
    (prepared : PreparedInvocation deployment profile ambient durable invocation)
    {signed : SignedCommand} (_accepted : AcceptedInvocation prepared signed)
    (index : Fin invocation.targets.length) (id : AtomId) : Option BendKeyRecord.Registered := do
  let target := invocation.targets[index]
  if target.payload != .read then none else do
    let store ← target.contentStore? (prepared.targets index).pre
    lookup store id

theorem no_computation_receipt (p : Publication) : (command p).run = none := rfl
theorem same_signed_source (p : Publication) :
    (command p).targets[0]?.map Target.expectedTargetRoot = some p.sourceRoot := rfl

#assert_axioms no_computation_receipt
#assert_axioms same_signed_source
end Minidregg.Kernel.BendKeyRegistration
