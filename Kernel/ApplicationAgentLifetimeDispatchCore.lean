/-
Current-image event26 candidate. The caller still needs verifier-minted
historical event22/event27/reserve evidence before submitting this intent.
No HTTP delivery permit or native receiver is exported here.
-/
import Kernel.ApplicationAgentLifetimeDispatchCurrent
import Kernel.ApplicationAgentLifetimeDispatchPayer

namespace Minidregg.Kernel.ApplicationAgentLifetimeDispatchCore

open Minidregg.Compiler
open Minidregg.Compiler.ResourceBirthCodec
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Theory
open Minidregg.Theory.CellRegistry
open Minidregg.Theory.ResourceCost
open Minidregg.Theory.TypedAuthorization
open Minidregg.Kernel.NativeHost
open Minidregg.Kernel.DurableDataIntent
open Minidregg.Kernel.ApplicationAgentLifetimeDispatchIngress
open Minidregg.Kernel.ApplicationAgentLifetimeDispatchReserveCore

set_option autoImplicit false

private def observedGuard (resource : Nat)
    (cell : PackedCell CanonicalCellRegistry.registry) : ReadGuard :=
  ⟨⟨resource⟩, ResourceBirthCodec.physicalRoot (.live cell)⟩

private def purseGuard {config : Config} {opened : Opened config}
    {context : ApplicationAgentLifetimeDispatchReserveContext.Context}
    (payer : ApplicationAgentLifetimeDispatchPayer.Checked config opened context) : ReadGuard :=
  observedGuard context.base.purseTask payer.cell

structure Checked (config : Config) (opened : Opened config)
    (ingress : Ingress) (spec : ApplicationShareIssueSource.Spec)
    (descriptor : ResourceBirth.Descriptor CanonicalCellRegistry.registry)
    (grant : ApplicationAgentLifetimeGrant.Grant)
    (ticketIssueIndex : Nat) (ticketIssueReceipt : NativeHostCodec.Receipt)
    (issuedIngressBytes : List UInt8) (certifiedGrantIssueIndex : Nat)
    (certifiedGrantRoot : Digest)
    (reserved : ApplicationAgentLifetimeDispatchReserveCore.ReservedEvidence config) where
  private mk ::
  contextExact : reserved.context = ingress.reserveContext
  current : ApplicationAgentLifetimeDispatchCurrent.Checked config.deployment
    config.profile ⟨config.federation, logicalHeight config opened.durable⟩
    opened.durable ingress spec descriptor grant ticketIssueIndex ticketIssueReceipt
    issuedIngressBytes certifiedGrantIssueIndex certifiedGrantRoot
  payer : ApplicationAgentLifetimeDispatchPayer.Checked config opened ingress.reserveContext
  holdExact : payer.state = AgentGrain.reserve reserved.beforeState
    ingress.reserveContext.base.reserveAmount
  purseDistinctParent : ingress.reserveContext.base.purseTask ≠
    ingress.reserveContext.base.parentTask
  purseDistinctSession : ingress.reserveContext.base.purseTask ≠
    ingress.dispatch.dispatch.dispatch.session.resource
  purseDistinctGrant : ingress.reserveContext.base.purseTask ≠ ingress.reserveContext.grantResource
  purseReadonly : (purseGuard payer).cellId ∉
    (DeclaredResourceController.writes current.prepared).map DataWrite.cellId

def checkCurrent (config : Config) (opened : Opened config)
    (ingress : Ingress) (spec : ApplicationShareIssueSource.Spec)
    (descriptor : ResourceBirth.Descriptor CanonicalCellRegistry.registry)
    (grant : ApplicationAgentLifetimeGrant.Grant)
    (ticketIssueIndex : Nat) (ticketIssueReceipt : NativeHostCodec.Receipt)
    (issuedIngressBytes : List UInt8) (certifiedGrantIssueIndex : Nat)
    (certifiedGrantRoot : Digest)
    (reserved : ApplicationAgentLifetimeDispatchReserveCore.ReservedEvidence config) :
    IO (Except String (Checked config opened ingress spec descriptor grant
      ticketIssueIndex ticketIssueReceipt issuedIngressBytes certifiedGrantIssueIndex certifiedGrantRoot reserved)) := do
  if contextExact : reserved.context = ingress.reserveContext then
    match ← ApplicationAgentLifetimeDispatchCurrent.checkCurrent config.deployment
        config.profile ⟨config.federation, logicalHeight config opened.durable⟩
        config.signature opened.durable ingress spec descriptor grant
        ticketIssueIndex ticketIssueReceipt issuedIngressBytes certifiedGrantIssueIndex certifiedGrantRoot with
    | .error detail => return .error detail
    | .ok current =>
      match ← ApplicationAgentLifetimeDispatchPayer.checkCurrent config opened
          ingress.reserveContext ingress.payerCapability
          ingress.payerObserve ingress.payerSigned with
      | .error detail => return .error detail
      | .ok payer =>
        if holdExact : payer.state = AgentGrain.reserve reserved.beforeState
            ingress.reserveContext.base.reserveAmount then
          if purseDistinctParent : ingress.reserveContext.base.purseTask ≠
              ingress.reserveContext.base.parentTask then
            if purseDistinctSession : ingress.reserveContext.base.purseTask ≠
                ingress.dispatch.dispatch.dispatch.session.resource then
              if purseDistinctGrant : ingress.reserveContext.base.purseTask ≠
                  ingress.reserveContext.grantResource then
                if purseReadonly : (purseGuard payer).cellId ∉
                    (DeclaredResourceController.writes current.prepared).map
                      DataWrite.cellId then
                  return .ok ⟨contextExact, current, payer, holdExact,
                    purseDistinctParent, purseDistinctSession, purseDistinctGrant,
                    purseReadonly⟩
                else return .error "lifetime dispatch purse overlaps app writes"
              else return .error "lifetime dispatch purse overlaps grant"
            else return .error "lifetime dispatch purse overlaps session"
          else return .error "lifetime dispatch purse overlaps parent"
        else return .error "lifetime dispatch payer hold differs from admitted reserve"
  else return .error "lifetime dispatch reserve context differs from admitted original"

def readGuards {config : Config} {opened : Opened config}
    {ingress : Ingress} {spec : ApplicationShareIssueSource.Spec}
    {descriptor : ResourceBirth.Descriptor CanonicalCellRegistry.registry}
    {grant : ApplicationAgentLifetimeGrant.Grant}
    {ticketIssueIndex : Nat} {ticketIssueReceipt : NativeHostCodec.Receipt}
    {issuedIngressBytes : List UInt8} {certifiedGrantIssueIndex : Nat}
    {certifiedGrantRoot : Digest}
    {reserved : ApplicationAgentLifetimeDispatchReserveCore.ReservedEvidence config}
    (checked : Checked config opened ingress spec descriptor grant ticketIssueIndex
      ticketIssueReceipt issuedIngressBytes certifiedGrantIssueIndex certifiedGrantRoot reserved) : List ReadGuard :=
  [observedGuard ingress.dispatch.dispatch.dispatch.app.resource
      checked.current.appRead.selected.observed.before,
    observedGuard ingress.dispatch.dispatch.dispatch.app.packageManifest
      checked.current.manifestRead.selected.observed.before,
    observedGuard ingress.dispatch.dispatch.enrollmentResource
      checked.current.enrollmentRead.selected.observed.before,
    observedGuard spec.ticket.resource checked.current.ticketRead.selected.observed.before,
    observedGuard ingress.reserveContext.grantResource checked.current.grantRead.selected.observed.before,
    purseGuard checked.payer]

theorem readGuards_current {config : Config} {opened : Opened config}
    {ingress : Ingress} {spec : ApplicationShareIssueSource.Spec}
    {descriptor : ResourceBirth.Descriptor CanonicalCellRegistry.registry}
    {grant : ApplicationAgentLifetimeGrant.Grant}
    {ticketIssueIndex : Nat} {ticketIssueReceipt : NativeHostCodec.Receipt}
    {issuedIngressBytes : List UInt8} {certifiedGrantIssueIndex : Nat}
    {certifiedGrantRoot : Digest}
    {reserved : ApplicationAgentLifetimeDispatchReserveCore.ReservedEvidence config}
    (checked : Checked config opened ingress spec descriptor grant ticketIssueIndex
      ticketIssueReceipt issuedIngressBytes certifiedGrantIssueIndex certifiedGrantRoot reserved)
    (guard : ReadGuard) (member : guard ∈ readGuards checked) :
    guard.expectedRoot = opened.durable.snapshot.model.roots guard.cellId := by
  simp [readGuards, observedGuard, purseGuard] at member
  rcases member with app | manifest | enrollment | ticket | grant | purse
  · subst guard; exact checked.current.appRead.current
  · subst guard; exact checked.current.manifestRead.current
  · subst guard; exact checked.current.enrollmentRead.current
  · subst guard; exact checked.current.ticketRead.current
  · subst guard; exact checked.current.grantRead.current
  · subst guard; exact checked.payer.physicalCurrent

theorem readGuards_readonly {config : Config} {opened : Opened config}
    {ingress : Ingress} {spec : ApplicationShareIssueSource.Spec}
    {descriptor : ResourceBirth.Descriptor CanonicalCellRegistry.registry}
    {grant : ApplicationAgentLifetimeGrant.Grant}
    {ticketIssueIndex : Nat} {ticketIssueReceipt : NativeHostCodec.Receipt}
    {issuedIngressBytes : List UInt8} {certifiedGrantIssueIndex : Nat}
    {certifiedGrantRoot : Digest}
    {reserved : ApplicationAgentLifetimeDispatchReserveCore.ReservedEvidence config}
    (checked : Checked config opened ingress spec descriptor grant ticketIssueIndex
      ticketIssueReceipt issuedIngressBytes certifiedGrantIssueIndex certifiedGrantRoot reserved)
    (guard : ReadGuard) (member : guard ∈ readGuards checked) :
    guard.cellId ∉ (DeclaredResourceController.writes checked.current.prepared).map
      DataWrite.cellId := by
  simp [readGuards, observedGuard, purseGuard] at member
  rcases member with app | manifest | enrollment | ticket | grant | purse
  · subst guard; exact checked.current.appRead.readonly
  · subst guard; exact checked.current.manifestRead.readonly
  · subst guard; exact checked.current.enrollmentRead.readonly
  · subst guard; exact checked.current.ticketRead.readonly
  · subst guard; exact checked.current.grantRead.readonly
  · subst guard; exact checked.purseReadonly

def charge {config : Config} {opened : Opened config}
    {ingress : Ingress} {spec : ApplicationShareIssueSource.Spec}
    {descriptor : ResourceBirth.Descriptor CanonicalCellRegistry.registry}
    {grant : ApplicationAgentLifetimeGrant.Grant}
    {ticketIssueIndex : Nat} {ticketIssueReceipt : NativeHostCodec.Receipt}
    {issuedIngressBytes : List UInt8} {certifiedGrantIssueIndex : Nat}
    {certifiedGrantRoot : Digest}
    {reserved : ApplicationAgentLifetimeDispatchReserveCore.ReservedEvidence config}
    (checked : Checked config opened ingress spec descriptor grant ticketIssueIndex
      ticketIssueReceipt issuedIngressBytes certifiedGrantIssueIndex certifiedGrantRoot reserved) : Charge :=
  let ordinary := checked.current.invocation.dataIntent checked.current.shape
  fun dimension => match dimension with
    | .incidences => ordinary.exactCharge .incidences + 6
    | .turnBytes => ingress.canonicalBytes.length
    | .witnessBytes => ingress.canonicalBytes.length
    | .proofWork => ordinary.exactCharge .proofWork + 6
    | .memoryTouches => ordinary.exactCharge .memoryTouches + 6
    | .storageBytes => ordinary.exactCharge .storageBytes +
        ingress.canonicalBytes.length +
        (ApplicationDispatchAdmissionIngress.nullifier ingress.dispatch).canonicalBytes.length +
        (ApplicationAgentLifetimeDispatchReserveCore.claimNullifier reserved).canonicalBytes.length
    | other => ordinary.exactCharge other

/-- The one CAS includes the unchanged app/session DRC writes, six current
physical read guards, the same one-use operation key as event21, and the
original purse reserve claim. The complete version26 carrier is retained. -/
def candidateIntent {config : Config} {opened : Opened config}
    {ingress : Ingress} {spec : ApplicationShareIssueSource.Spec}
    {descriptor : ResourceBirth.Descriptor CanonicalCellRegistry.registry}
    {grant : ApplicationAgentLifetimeGrant.Grant}
    {ticketIssueIndex : Nat} {ticketIssueReceipt : NativeHostCodec.Receipt}
    {issuedIngressBytes : List UInt8} {certifiedGrantIssueIndex : Nat}
    {certifiedGrantRoot : Digest}
    {reserved : ApplicationAgentLifetimeDispatchReserveCore.ReservedEvidence config}
    (checked : Checked config opened ingress spec descriptor grant ticketIssueIndex
      ticketIssueReceipt issuedIngressBytes certifiedGrantIssueIndex certifiedGrantRoot reserved) :
    DataIntent ResourceBirthCodec.rootBytes := by
  let ordinary := checked.current.invocation.dataIntent checked.current.shape
  have guarded : ∀ guard ∈ ordinary.readGuards ++ readGuards checked,
      guard.cellId ∉ ordinary.writes.map DataWrite.cellId := by
    intro guard member
    rcases List.mem_append.mp member with old | extra
    · exact ordinary.guardsReadOnly guard old
    · exact readGuards_readonly checked guard extra
  exact
    { transactionId := ordinary.transactionId
      writes := ordinary.writes
      readGuards := ordinary.readGuards ++ readGuards checked
      nullifiers := ordinary.nullifiers ++
        [ApplicationDispatchAdmissionIngress.nullifier ingress.dispatch,
          ApplicationAgentLifetimeDispatchReserveCore.claimNullifier reserved]
      exactCharge := charge checked
      event := ApplicationAgentLifetimeDispatchIngress.event ingress
      subject := ordinary.subject
      postRootsBound := ordinary.postRootsBound
      guardsReadOnly := guarded }

theorem candidate_event_version {config : Config} {opened : Opened config}
    {ingress : Ingress} {spec : ApplicationShareIssueSource.Spec}
    {descriptor : ResourceBirth.Descriptor CanonicalCellRegistry.registry}
    {grant : ApplicationAgentLifetimeGrant.Grant}
    {ticketIssueIndex : Nat} {ticketIssueReceipt : NativeHostCodec.Receipt}
    {issuedIngressBytes : List UInt8} {certifiedGrantIssueIndex : Nat}
    {certifiedGrantRoot : Digest}
    {reserved : ApplicationAgentLifetimeDispatchReserveCore.ReservedEvidence config}
    (checked : Checked config opened ingress spec descriptor grant ticketIssueIndex
      ticketIssueReceipt issuedIngressBytes certifiedGrantIssueIndex certifiedGrantRoot reserved) :
    (candidateIntent checked).event.codecVersion = 26 := rfl

end Minidregg.Kernel.ApplicationAgentLifetimeDispatchCore
