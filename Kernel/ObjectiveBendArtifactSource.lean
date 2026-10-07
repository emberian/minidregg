/- Canonical immutable Objective source loading: the artifact record, decoded and
named by its identity. Loading does not parse or type the artifact's typed core:
a receiver re-runs the front end on the artifact's package and requires the core
to be that replay's rendering (`ObjectiveBendPublication.Replayed`), then types the
replayed term. Consumers retain the actual current read and its CAS dependency. -/
import Compiler.ObjectiveBendSourceArtifact
import Kernel.ContentResource
import Kernel.ResourceObservationAdmission
import Theory.AssertAxioms
namespace Minidregg.Kernel.ObjectiveBendArtifactSource
open Minidregg.Compiler
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Theory
open Minidregg.Theory.Hyperdocument
open Minidregg.Theory.TypedAuthorization
set_option autoImplicit false

structure Loaded (store : ContentResource.ContentStore) (id : AtomId) (maxBytes : Nat) where
  private mk ::
  record : AtomRecord
  recordExact : Hyperdocument.lookup store .atoms id = some record
  live : record.tombstonedAt.isNone = true
  schemaExact : record.kind = .inlineObject ObjectiveBendSourceArtifact.schema
  artifact : ObjectiveBendSourceArtifact.Artifact
  decoded : ObjectiveBendSourceArtifact.decode record.payload = some artifact
  identityExact : ObjectiveBendSourceArtifact.identity artifact = id.digest

def lookup (store : ContentResource.ContentStore) (id : AtomId) (maxBytes : Nat) :
    Option (Loaded store id maxBytes) := do
  match recordExact : Hyperdocument.lookup store .atoms id with
  | none => none
  | some record =>
    if record.payload.length > maxBytes then none else
    if live : record.tombstonedAt.isNone = true then
      if schemaExact : record.kind = .inlineObject ObjectiveBendSourceArtifact.schema then
        match decoded : ObjectiveBendSourceArtifact.decode record.payload with
        | none => none
        | some artifact =>
          if identityExact : ObjectiveBendSourceArtifact.identity artifact = id.digest then
            some ⟨record,recordExact,live,schemaExact,artifact,decoded,identityExact⟩
          else none
      else none
    else none

theorem loaded_canonical {store : ContentResource.ContentStore} {id : AtomId} {maxBytes : Nat}
    (loaded : Loaded store id maxBytes) :
    ObjectiveBendSourceArtifact.encode loaded.artifact = loaded.record.payload :=
  ObjectiveBendSourceArtifact.decoded_canonical loaded.decoded

/-- Retaining a native read is deliberately separate from pure content loading.
The receiver can construct this only with the actual signed current observation
check, plus equality to that read's complete ContentStore. -/
structure Current {F : Type} [Field F] [DecidableEq F]
    {deployment : ResourceObservationAdmission.Deployment}
    (context : ResourceObservationAdmission.Context deployment)
    (profile : CanonicalRuntimeProfile.Profile F)
    {kind : ResourceKind} (wanted : Request kind) (marker : Nat)
    (capability : CapabilityId) (contextBytes : List UInt8)
    (prepared : ResourceObservationAdmission.Prepared context profile wanted marker capability contextBytes)
    (envelope : List UInt8) (store : ContentResource.ContentStore) (id : AtomId) (maxBytes : Nat) where
  private mk ::
  read : ResourceObservationAdmission.Checked prepared envelope
  fullScope : ResourceObservationAdmission.readerFields context kind capability = none
  payload : CellState.Materialized (CanonicalCellRegistry.materializer .content)
  contentExact : prepared.observed.before = ⟨.content,payload⟩
  storeExact : payload.logical = store
  source : Loaded store id maxBytes

/-- Callers cannot replace current read evidence with a manifest or root label. -/
def bindCurrent {F : Type} [Field F] [DecidableEq F]
    {deployment : ResourceObservationAdmission.Deployment}
    {context : ResourceObservationAdmission.Context deployment}
    {profile : CanonicalRuntimeProfile.Profile F}
    {kind : ResourceKind} {wanted : Request kind} {marker : Nat}
    {capability : CapabilityId} {contextBytes : List UInt8}
    {prepared : ResourceObservationAdmission.Prepared context profile wanted marker capability contextBytes}
    {envelope : List UInt8} {store : ContentResource.ContentStore} {id : AtomId} {maxBytes : Nat}
    (read : ResourceObservationAdmission.Checked prepared envelope)
    (fullScope : ResourceObservationAdmission.readerFields context kind capability = none)
    (payload : CellState.Materialized (CanonicalCellRegistry.materializer .content))
    (contentExact : prepared.observed.before = ⟨.content,payload⟩)
    (storeExact : payload.logical = store) (source : Loaded store id maxBytes) :
    Current context profile wanted marker capability contextBytes prepared envelope store id maxBytes :=
  ⟨read,fullScope,payload,contentExact,storeExact,source⟩

#assert_axioms loaded_canonical
end Minidregg.Kernel.ObjectiveBendArtifactSource
