/-
Cycle-safe current-image admission and event21 candidate intent. Its inputs
remain components until Replay proves both historical issue and reserve are
members of this exact admitted prefix. Neither this module nor its candidate
can deliver an HTTP request or recover a historical permit.
-/
import Kernel.ApplicationDispatchAgentIngress
import Kernel.ApplicationDispatchHistoricalCore

namespace Minidregg.Kernel.ApplicationDispatchAgentCore

open Minidregg.Compiler
open Minidregg.Compiler.ResourceBirthCodec
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Theory
open Minidregg.Theory.CellRegistry
open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.ResourceCost
open Minidregg.Kernel.NativeHost
open Minidregg.Kernel.DurableDataIntent
open Minidregg.Kernel.ApplicationDispatchAgentIngress
open Minidregg.Kernel.ApplicationDispatchAgentReserveContext
open Minidregg.Kernel.ApplicationDispatchAgentReserveCore

set_option autoImplicit false

private def purseGuard {config : Config} {opened : Opened config}
    {context : Context}
    (payer : ApplicationDispatchAgentPayer.Checked config opened context) : ReadGuard :=
  ⟨⟨context.purseTask⟩, ResourceBirthCodec.physicalRoot (.live payer.cell)⟩

structure Checked (config : Config) (opened : Opened config)
    (ingress : ApplicationDispatchAgentIngress.Ingress)
    (issued : ApplicationDispatchHistoricalCore.IssuedEvidence config)
    (reserved : ReservedEvidence config) where
  private mk ::
  contextExact : reserved.context = ingress.reserveContext
  scopeExact : matchesIngress ingress.reserveContext ingress.dispatch
    issued.spec.ticket.resource = true
  base : ApplicationDispatchHistoricalCore.CheckedCandidate config
    opened.durable ingress.dispatch issued
  payer : ApplicationDispatchAgentPayer.Checked config opened ingress.reserveContext
  holdExact : payer.state = AgentGrain.reserve reserved.beforeState
    ingress.reserveContext.reserveAmount
  purseDistinctParent : ingress.reserveContext.purseTask ≠
    ingress.reserveContext.parentTask
  purseDistinctSession : ingress.reserveContext.purseTask ≠
    ingress.dispatch.dispatch.dispatch.session.resource
  purseReadonly : (purseGuard payer).cellId ∉
    (ApplicationDispatchPending.candidateIntent base.checked).writes.map DataWrite.cellId

theorem Checked.purseGuard_current {config : Config} {opened : Opened config}
    {ingress : ApplicationDispatchAgentIngress.Ingress}
    {issued : ApplicationDispatchHistoricalCore.IssuedEvidence config}
    {reserved : ReservedEvidence config}
    (checked : Checked config opened ingress issued reserved) :
    (purseGuard checked.payer).expectedRoot =
      opened.durable.snapshot.model.roots (purseGuard checked.payer).cellId :=
  checked.payer.physicalCurrent

def checkCurrent (config : Config) (opened : Opened config)
    (ingress : ApplicationDispatchAgentIngress.Ingress)
    (issued : ApplicationDispatchHistoricalCore.IssuedEvidence config)
    (reserved : ReservedEvidence config) :
    IO (Except String (Checked config opened ingress issued reserved)) := do
  if contextExact : reserved.context = ingress.reserveContext then
    if scopeExact : matchesIngress ingress.reserveContext ingress.dispatch
        issued.spec.ticket.resource = true then
      match ← ApplicationDispatchHistoricalCore.checkCurrent config opened.durable
          ingress.dispatch issued with
      | .error detail => return .error detail
      | .ok base =>
        match ← ApplicationDispatchAgentPayer.checkCurrent config opened
            ingress.reserveContext ingress.payerCapability ingress.payerObserve
            ingress.payerSigned with
        | .error detail => return .error detail
        | .ok payer =>
          if holdExact : payer.state = AgentGrain.reserve reserved.beforeState
              ingress.reserveContext.reserveAmount then
            if purseDistinctParent : ingress.reserveContext.purseTask ≠
                ingress.reserveContext.parentTask then
              if purseDistinctSession : ingress.reserveContext.purseTask ≠
                  ingress.dispatch.dispatch.dispatch.session.resource then
                if purseReadonly : (purseGuard payer).cellId ∉
                    (ApplicationDispatchPending.candidateIntent base.checked).writes.map
                      DataWrite.cellId then
                  return .ok ⟨contextExact, scopeExact, base, payer,
                    holdExact, purseDistinctParent, purseDistinctSession, purseReadonly⟩
                else return .error "dispatch purse overlaps app writes"
              else return .error "dispatch purse overlaps session"
            else return .error "dispatch purse overlaps parent"
          else return .error "dispatch payer hold differs from admitted reserve"
    else return .error "dispatch reserve context differs from app or issued ticket"
  else return .error "dispatch reserve context differs from admitted original"

def charge {config : Config} {opened : Opened config}
    {ingress : ApplicationDispatchAgentIngress.Ingress}
    {issued : ApplicationDispatchHistoricalCore.IssuedEvidence config}
    {reserved : ReservedEvidence config}
    (checked : Checked config opened ingress issued reserved) : Charge :=
  let base := (ApplicationDispatchPending.candidateIntent checked.base.checked).exactCharge
  fun dimension => match dimension with
    | .incidences => base .incidences + 1
    | .turnBytes => ingress.canonicalBytes.length
    | .witnessBytes => ingress.canonicalBytes.length
    | .proofWork => base .proofWork + 1
    | .memoryTouches => base .memoryTouches + 1
    | .storageBytes => base .storageBytes + ingress.canonicalBytes.length +
        (claimNullifier reserved).canonicalBytes.length
    | other => base other

/-- The app mutation is unchanged, but the event is version21, the physical
purse read guard joins its CAS, and the original reserve receipt is claimed
once. Replay must still certify `reserved` as a prior admitted step. -/
def candidateIntent {config : Config} {opened : Opened config}
    {ingress : ApplicationDispatchAgentIngress.Ingress}
    {issued : ApplicationDispatchHistoricalCore.IssuedEvidence config}
    {reserved : ReservedEvidence config}
    (checked : Checked config opened ingress issued reserved) :
    DataIntent rootBytes := by
  let base := ApplicationDispatchPending.candidateIntent checked.base.checked
  have guarded : ∀ guard ∈ base.readGuards ++ [purseGuard checked.payer],
      guard.cellId ∉ base.writes.map DataWrite.cellId := by
    intro guard member
    rcases List.mem_append.mp member with old | purse
    · exact base.guardsReadOnly guard old
    · simp only [List.mem_singleton] at purse
      subst guard
      exact checked.purseReadonly
  exact
    { transactionId := base.transactionId
      writes := base.writes
      readGuards := base.readGuards ++ [purseGuard checked.payer]
      nullifiers := base.nullifiers ++ [claimNullifier reserved]
      exactCharge := charge checked
      event := ApplicationDispatchAgentIngress.event ingress
      subject := base.subject
      postRootsBound := base.postRootsBound
      guardsReadOnly := guarded }

theorem candidate_event_version {config : Config} {opened : Opened config}
    {ingress : ApplicationDispatchAgentIngress.Ingress}
    {issued : ApplicationDispatchHistoricalCore.IssuedEvidence config}
    {reserved : ReservedEvidence config}
    (checked : Checked config opened ingress issued reserved) :
    (candidateIntent checked).event.codecVersion = 21 := rfl

/-- A human dispatch event11 can never be mistaken for the paid agent event,
even when the app command and HTTP operation identifier are identical. -/
theorem candidate_event_ne_human {config : Config} {opened : Opened config}
    {ingress : ApplicationDispatchAgentIngress.Ingress}
    {issued : ApplicationDispatchHistoricalCore.IssuedEvidence config}
    {reserved : ReservedEvidence config}
    (checked : Checked config opened ingress issued reserved) :
    (candidateIntent checked).event ≠
      ApplicationDispatchAdmissionIngress.event ingress.dispatch := by
  intro equal
  have versions := congrArg StableEvent.codecVersion equal
  norm_num [candidate_event_version, ApplicationDispatchAdmissionIngress.event] at versions

end Minidregg.Kernel.ApplicationDispatchAgentCore
