/-
Composite factory and Book semantic families for a grain-backed birth. The
bare birth families remain unchanged. This module supplies no authorization:
its evidence is indexed to the composite factory request and the exact old
Book, and must be constructed by the joint receiving admission.
-/
import Kernel.GrainResourceBirthPolicyController
import Kernel.CanonicalResourceEffect

namespace Minidregg.Kernel.GrainResourceBirthFamilies

open Minidregg.Compiler
open Minidregg.Theory
open Minidregg.Theory.CellState
open Minidregg.Theory.IndexedProgram
open Minidregg.Theory.ResourceBirth
open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.CanonicalResourceKernel
open Minidregg.Kernel.ResourceBirthPolicyController

set_option autoImplicit false

abbrev Source := GrainResourceBirthController.Source
abbrev Tariff := GrainResourceBirthController.Tariff

/-- The current factory law must authorize the composite request, whose
domain-separated arguments contain the birth and both grain incidences. The
shared metadata checker still supplies all bare factory invariants. -/
structure FactoryAuthorization (tariff : Tariff) (source : Source)
    (pins : FactoryPins) (encoding : SourceEncoding CanonicalCellRegistry.registry)
    (portal : Portal) (oldAuthority : AuthState)
    (factoryPreRoot : Digest) (height : Height) where
  checked : Checked pins encoding oldAuthority source.birth
  authorized : Authorized portal oldAuthority
    (source.factoryRequest tariff pins encoding oldAuthority factoryPreRoot height)

def factoryFamily (tariff : Tariff) (source : Source)
    (pins : FactoryPins) (encoding : SourceEncoding CanonicalCellRegistry.registry)
    (oldAuthority : AuthState) (pre : FactoryCell) (height : Height) :
    SemanticEffectFamily EffectDeclaration.effectLayout DeclaredEffectCell.materializer Unit where
  Declaration := Unit
  declarationCodec := DeclaredActionLowering.unitCodec
  pre := pre
  request := fun _ => ⟨.object,
    source.factoryRequest tariff pins encoding oldAuthority pre.root height⟩
  Outcome := fun _ => Unit
  outcomeCodec := fun _ => DeclaredActionLowering.unitCodec
  ModeEvidence := fun _ _ => Unit
  Postcondition := fun _ _ logical => logical = pre.logical
  effectDigest := fun _ => encoding.hashBytes
    ("DREGG/GRAIN-RESOURCE-BIRTH/EFFECTS/v1".toUTF8.toList ++
      source.canonicalBytes tariff)
  patch := fun _ _ => ResourceBirthPolicyController.factoryPatch pre
  nullifier := fun _ _ => none
  Release := fun _ _ => Empty
  DeclassificationAuthority := fun _ _ => Empty
  ReleaseAuthorization := fun _ _ _ => Empty
  DisclosureAllowed := fun _ _ _ => True

/-- A conserved Book batch still uses its existing request and exact
admission. The factory witness is now for the composite request; a bare
factory token cannot inhabit this evidence. -/
structure BirthBatchEvidence {M : CellState.Materializer CanonicalResourceKernel.layout Digest}
    (tariff : Tariff) (source : Source)
    (pins : FactoryPins) (encoding : SourceEncoding CanonicalCellRegistry.registry)
    (factoryPortal sourcePortal : Portal) (oldAuthority : AuthState)
    (factoryPreRoot : Digest) (height : Height)
    (pre : CellState.Materialized M)
    (contexts : Nat → CanonicalResourceEffect.RequestContext) where
  factory : FactoryAuthorization tariff source pins encoding factoryPortal oldAuthority
    factoryPreRoot height
  admission : source.birth.resourceBatch.Admission (CanonicalResourceKernel.logicalBook pre.logical)
  sources : ∀ position : Fin source.birth.resourceBatch.operations.length,
    Authorized sourcePortal oldAuthority
      (CanonicalResourceEffect.batchSourceRequest encoding pre contexts source.birth position)

def birthFamily {M : CellState.Materializer CanonicalResourceKernel.layout Digest}
    (tariff : Tariff) (source : Source)
    (pins : FactoryPins) (encoding : SourceEncoding CanonicalCellRegistry.registry)
    (factoryPortal sourcePortal : Portal) (oldAuthority : AuthState)
    (factoryPreRoot : Digest) (height : Height)
    (pre : CellState.Materialized M)
    (contexts : Nat → CanonicalResourceEffect.RequestContext) :
    SemanticEffectFamily CanonicalResourceKernel.layout M Unit where
  Declaration := Unit
  declarationCodec := DeclaredActionLowering.unitCodec
  pre := pre
  request := fun _ => ⟨.account,
    CanonicalResourceEffect.birthRequest encoding pre contexts source.birth⟩
  Outcome := fun _ => Unit
  outcomeCodec := fun _ => DeclaredActionLowering.unitCodec
  ModeEvidence := fun _ _ => BirthBatchEvidence tariff source pins encoding
    factoryPortal sourcePortal oldAuthority factoryPreRoot height pre contexts
  Postcondition := fun _ _ post =>
    (source.birth.resourceBatch.patch pre).ResultAt pre.logical post ∧
      CanonicalResourceKernel.logicalBook post =
        source.birth.resourceBatch.apply (CanonicalResourceKernel.logicalBook pre.logical)
  effectDigest := fun _ => encoding.effectsDigest source.birth
  patch := fun _ _ => source.birth.resourceBatch.patch pre
  nullifier := fun _ _ => none
  Release := fun _ _ => PEmpty
  DeclassificationAuthority := fun _ _ => PEmpty
  ReleaseAuthorization := fun _ _ release => release.elim
  DisclosureAllowed := fun _ _ disclosure => disclosure = .sealed

/-- One authority incidence installs birth grants, birth nullifier and the
derived grain-operation marker. Its request is independently authorized at
the actual authority pre-root, over the same full composite source. -/
def authorityFamily (tariff : Tariff) (source : Source)
    (pins : FactoryPins) (encoding : SourceEncoding CanonicalCellRegistry.registry)
    (snapshot : CredentialAuthorityDomain.Snapshot)
    (semantics : Digest) (height : Height) :
    SemanticEffectFamily CredentialAuthorityState.layout CredentialAuthorityCell.materializer Nat where
  Declaration := Unit
  declarationCodec := DeclaredActionLowering.unitCodec
  pre := snapshot.cell
  request := fun _ => ⟨.object,
    source.factoryRequest tariff pins encoding snapshot.authState snapshot.cell.root height⟩
  Outcome := fun _ => Unit
  outcomeCodec := fun _ => DeclaredActionLowering.unitCodec
  ModeEvidence := fun _ _ => Unit
  Postcondition := fun _ _ logical =>
    (source.authorityPatch snapshot).ResultAt snapshot.cell.logical logical
  effectDigest := fun _ => encoding.hashBytes
    ("DREGG/GRAIN-RESOURCE-BIRTH/EFFECTS/v1".toUTF8.toList ++
      source.canonicalBytes tariff)
  patch := fun _ _ => source.authorityPatch snapshot
  nullifier := fun _ _ => some
    (DeclaredResourceController.operationMarker snapshot.domain semantics
      (source.grainCommand tariff))
  Release := fun _ _ => Empty
  DeclassificationAuthority := fun _ _ => Empty
  ReleaseAuthorization := fun _ _ _ => Empty
  DisclosureAllowed := fun _ _ disclosure => disclosure = .sealed

end Minidregg.Kernel.GrainResourceBirthFamilies
