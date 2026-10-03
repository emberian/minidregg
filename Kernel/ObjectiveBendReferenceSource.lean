/- Referenced prototype source uses the EXISTING governed content role. Every
lookup below consumes a current admitted narrowed read, exact resource/root,
live atom/schema and canonical content identity. It cannot reinterpret a pin
through mutable latest source or a caller-supplied unobserved package. -/
import Compiler.ObjectiveBendReference
import Kernel.BendInvocationInput
import Compiler.BendCoreAdmission
import Kernel.WorldMethodTrace

namespace Minidregg.Kernel.ObjectiveBendReferenceSource
open Minidregg.Compiler
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Theory
open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.Hyperdocument
open Minidregg.Kernel.DeclaredResourceController
open ObjectiveBendReference
set_option autoImplicit false

/-- Pure canonical lookup is NEVER a read authorization token. Open partial
requirements remain authorable; complete behavior admission happens at linking. -/
def lookupPartial (store : ContentResource.ContentStore) (content : Digest) :
    Option ObjectiveBendPrototype.Partial := do
  let record ← Hyperdocument.lookup store .atoms (⟨content⟩ : AtomId)
  if record.tombstonedAt.isSome then none else do
    let .inlineObject schema := record.kind | none
    if schema != partialSchema then none else do
      let prototype ← ObjectiveBendPrototype.decode record.payload
      if partialDigest prototype != content then none else do
        if (ObjectiveBendPrototype.reflect prototype).isOk then some prototype else none

def lookupCore (store : ContentResource.ContentStore) (content : Digest) : Option Core := do
  let record ← Hyperdocument.lookup store .atoms (⟨content⟩ : AtomId)
  if record.tombstonedAt.isSome then none else do
    let .inlineObject schema := record.kind | none
    if schema != coreSchema then none else do
      let core ← decodeCore record.payload
      if coreIdentity core != content then none else do
        if (BendCoreAdmission.admit core.book).isOk then some core else none

variable {F : Type} [Field F] [DecidableEq F]
  {deployment : ResourceObservationAdmission.Deployment}
  {durable : ResourceObservationAdmission.Durable}
  {context : ResourceObservationAdmission.Context deployment durable}
  {profile : CanonicalRuntimeProfile.Profile F} {subject : SubjectId}

structure Source (reference : Reference) where
  current : BendInvocationInput.Admitted context profile subject
  resourceExact : current.value.resource = reference.resource
  rootExact : current.value.root = reference.root
  store : ContentResource.ContentStore
  decoded : HyperdocumentCell.contentMaterializer.codec.decode current.value.resourceBytes = some store

/-- Narrowed content bytes, not the internal whole method trace preimage, are
what this source decoder receives. A capability excluding body leaves no atoms
and therefore cannot load a source program/prototype. -/
def loadSource (reference : Reference)
    (current : BendInvocationInput.Admitted context profile subject) : Option (Source (context := context) (profile := profile) (subject := subject) reference) := do
  if resource : current.value.resource = reference.resource then
    if root : current.value.root = reference.root then
      if current.value.physicalKind != CanonicalCellRegistry.Kind.content.tag.toNat then none else do
        match decoded : HyperdocumentCell.contentMaterializer.codec.decode current.value.resourceBytes with
        | none => none
        | some store => some ⟨current, resource, root, store, decoded⟩
    else none
  else none

structure PartialAt (reference : Reference) where
  source : Source (context := context) (profile := profile) (subject := subject) reference
  prototype : ObjectiveBendPrototype.Partial
  exact : lookupPartial source.store reference.content = some prototype

structure CoreAt (reference : Reference) where
  source : Source (context := context) (profile := profile) (subject := subject) reference
  core : Core
  exact : lookupCore source.store reference.content = some core

def loadPartial (reference : Reference)
    (current : BendInvocationInput.Admitted context profile subject) : Option (PartialAt (context := context) (profile := profile) (subject := subject) reference) := do
  let source ← loadSource reference current
  match exact : lookupPartial source.store reference.content with
  | none => none
  | some prototype => some ⟨source, prototype, exact⟩

def loadCore (reference : Reference)
    (current : BendInvocationInput.Admitted context profile subject) : Option (CoreAt (context := context) (profile := profile) (subject := subject) reference) := do
  let source ← loadSource reference current
  match exact : lookupCore source.store reference.content with
  | none => none
  | some core => some ⟨source, core, exact⟩

structure Publication where
  subject : SubjectId
  nonce : Nat
  resource : Nat
  capability : CapabilityId
  expectedRoot : Digest
  prototype : ObjectiveBendPrototype.Partial

def command (publication : Publication) : Command :=
  ⟨publication.subject, publication.nonce,
    [⟨.object, publication.resource, publication.capability, ContentResource.commandVersion,
      publication.expectedRoot,
      .content ⟨[.createAtom ⟨partialDigest publication.prototype⟩
        (.inlineObject partialSchema) (ObjectiveBendPrototype.encode publication.prototype)]⟩,
      none, none, none⟩], none⟩

/-- This is ordinary actual native receiving. Neither closure compilation nor
a successful publish grants installation/birth authority or claims execution. -/
def receiveLoaded (selectedDeployment : Deployment)
    (selectedProfile : CanonicalRuntimeProfile.Profile F) (ambient : Ambient)
    (native : CredentialSignatureIO.NativeConfig) (transport : DurableReceiverIO.Transport)
    (selectedDurable : Durable) (publication : Publication) (signed : SignedCommand) : IO ReceiveResult :=
  if (ObjectiveBendPrototype.reflect publication.prototype).isOk &&
      decide (signed.commandBytes = commandCodec.encode (command publication)) then
    DeclaredResourceController.receiveLoaded selectedDeployment selectedProfile ambient native transport
      selectedDurable signed
  else pure (.rejected .malformedCommand)

/-- Core source publication requires actual core admission, while ordinary
current content authority still judges the exact proposed storage effect. This
stores source only; numeric/backend/cost/disclosure profile is separately bound
when invoking it. -/
structure CorePublication where
  subject : SubjectId
  nonce : Nat
  resource : Nat
  capability : CapabilityId
  expectedRoot : Digest
  core : Core

def coreCommand (publication : CorePublication) : Command :=
  ⟨publication.subject, publication.nonce,
    [⟨.object, publication.resource, publication.capability, ContentResource.commandVersion,
      publication.expectedRoot,
      .content ⟨[.createAtom ⟨coreIdentity publication.core⟩
        (.inlineObject coreSchema) (encodeCore publication.core)]⟩,
      none, none, none⟩], none⟩

def receiveCoreLoaded (selectedDeployment : Deployment)
    (selectedProfile : CanonicalRuntimeProfile.Profile F) (ambient : Ambient)
    (native : CredentialSignatureIO.NativeConfig) (transport : DurableReceiverIO.Transport)
    (selectedDurable : Durable) (publication : CorePublication) (signed : SignedCommand) : IO ReceiveResult :=
  if (BendCoreAdmission.admit publication.core.book).isOk &&
      decide (signed.commandBytes = commandCodec.encode (coreCommand publication)) then
    DeclaredResourceController.receiveLoaded selectedDeployment selectedProfile ambient native transport
      selectedDurable signed
  else pure (.rejected .malformedCommand)

theorem loaded_actual_root {reference : Reference} (source : Source
    (context := context) (profile := profile) (subject := subject) reference) :
    source.current.value.root = reference.root := source.rootExact

theorem publication_exact_partial (publication : Publication) :
    (command publication).targets[0]?.map Target.payload = some (.content ⟨[.createAtom
      ⟨partialDigest publication.prototype⟩ (.inlineObject partialSchema)
      (ObjectiveBendPrototype.encode publication.prototype)]⟩) := rfl

#assert_axioms loaded_actual_root
#assert_axioms publication_exact_partial
end Minidregg.Kernel.ObjectiveBendReferenceSource
