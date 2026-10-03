/- Transport fixture construction for the actual native reserve-birth receiver.
   These functions issue no capability or success token; native source admission
   and physical CAS/readback must qualify their outputs. -/
import Kernel.NativeHostReserveBirth

namespace Minidregg.Verify.ResourceReserveBirthFixture

open Minidregg.Compiler
open Minidregg.Theory
open Minidregg.Theory.ResourceBirth
open Minidregg.Theory.TypedAuthorization
open Minidregg.Kernel
open Minidregg.Kernel.ResourceBirthPolicyController.Concrete

set_option autoImplicit false

structure Born where
  item : BirthItem CanonicalCellRegistry.registry
  ownerCapability : CapabilityId
  controlCapability : CapabilityId

def declared (target : Nat) (owner : SubjectId) (ownerCapability controlCapability : CapabilityId) : Born :=
  ⟨⟨⟨target, CellRegistry.CellSlot.root CanonicalCellRegistry.registry .absent,
      NativeHostGenesis.declaredPacked target false .open⟩,
    .object, owner, none, none⟩, ownerCapability, controlCapability⟩

/-- Initial content remains empty as required by CanonicalCellRegistry.UserInitial.
The pinned control atom must be initialized by a second admitted content operation. -/
def content (target : Nat) (owner : SubjectId) (ownerCapability controlCapability : CapabilityId) : Born :=
  ⟨⟨⟨target, CellRegistry.CellSlot.root CanonicalCellRegistry.registry .absent,
      ⟨.content, CellState.materialize HyperdocumentCell.contentMaterializer ContentResource.initialStore⟩⟩,
    .object, owner, none, none⟩, ownerCapability, controlCapability⟩

def ordinaryDescriptor (config : NativeHost.Config) (source : NativeHostGenesis.Config)
    (opened : NativeHost.Opened config) (creator : SubjectId) (nonce payer : Nat)
    (born : List Born) : Descriptor CanonicalCellRegistry.registry :=
  let height := NativeHost.logicalHeight config opened.durable
  let root := fun (kind : ResourceKind) (id : CapabilityId) (owner : SubjectId)
      (target : Nat) (verbs : Finset (Verb kind)) =>
    { NativeHostGenesis.rootCapability config.profile source kind id owner target verbs with
      issuerEpoch := opened.authority.snapshot.authState.issuerEpoch config.profile.template.issuer
      notBefore := height
      notAfter := height + config.profile.template.lifetime }
  let grants : List AuthorityGrant := born.flatMap fun entry =>
    [⟨entry.item.resourceKind, ⟨root entry.item.resourceKind entry.ownerCapability entry.item.owner
        entry.item.create.cellId (ownerVerbs entry.item.resourceKind), []⟩⟩,
     ⟨.program, ⟨root .program entry.controlCapability entry.item.owner entry.item.create.cellId
        {.installPolicy, .revokeCapability}, []⟩⟩]
  let policies := born.map fun entry =>
    let record := NativeHostGenesis.policy config.profile source entry.item.create.cellId (.all [])
    (⟨record.policyId, PolicyRecordCodec.digest record, PolicyRecordCodec.encode record⟩ : InitialPolicy)
  let identity := ResourceBirthController.Concrete.sourceIdentity config.profile.compilerProfile
    config.deployment creator nonce
  let unpriced : Descriptor CanonicalCellRegistry.registry := {
    factory := ⟨config.deployment.factoryId⟩
    creator := creator
    transactionId := identity
    nonce := nonce
    births := born.map (·.item)
    auxiliaryCreates := []
    grants := grants
    initialPolicies := policies
    authorityNullifier := identity.value
    funding := []
    fee := ⟨payer, config.tariff.collector, config.tariff.asset, 0⟩ }
  { unpriced with fee := { unpriced.fee with amount := unpriced.quotedFee config.tariff } }

/-- Two independent owner incidences expose omitted/reordered consent refuters.
The creator pays; each owner's source signature must verify with its own actual key. -/
def twoOwnerPlan (config : NativeHost.Config) (source : NativeHostGenesis.Config)
    (opened : NativeHost.Opened config) (creator otherOwner : SubjectId)
    (nonce payer : Nat) (debitCapability : CapabilityId) :
    Except String NativeHostReserveBirth.SigningPlan := do
  let ordinary := ordinaryDescriptor config source opened creator nonce payer
    [declared 100 otherOwner ⟨1001⟩ ⟨1101⟩, declared 101 creator ⟨1002⟩ ⟨1102⟩]
  let descriptor ← NativeHostReserveBirth.withReserveGrants config.profile.template
    opened.authority.snapshot.authState (NativeHost.logicalHeight config opened.durable)
    config.tariff ordinary [⟨1201⟩, ⟨1202⟩]
  NativeHostReserveBirth.prepareLoaded config opened
    (CanonicalCellRegistry.sourceEncoding.codec.encode descriptor) [debitCapability]

/-- Actual native invocation shape for a framed control initializer. The
receiving bootstrap gate must independently compare payload with the source's
canonical empty Control and bind its pinned owner/cell/atom/schema. -/
def initializationCommand (owner : SubjectId) (nonce cell : Nat)
    (ownerCapability : CapabilityId) (preRoot : Digest)
    (atom : Hyperdocument.AtomId) (schema : Digest) (payload : List UInt8) :
    ResourceTransaction.Command where
  subject := owner
  nonce := nonce
  targets := [⟨.object, cell, ownerCapability, ContentResource.commandVersion, preRoot,
    .content ⟨[.createAtom atom (.inlineObject schema) payload]⟩, none, none, none⟩]
  run := none

end Minidregg.Verify.ResourceReserveBirthFixture
