/-
Cycle-safe current-image admission and event21 candidate intent. Its inputs
remain components until Replay proves both historical issue and reserve are
members of this exact admitted prefix. Neither this module nor its candidate
can deliver an HTTP request or recover a historical permit.
-/
module

public import Kernel.ApplicationDispatchAgentIngress
public import Kernel.ApplicationDispatchHistoricalCore
public import Kernel.NativeHostServed

-- Bodies this file reduces or derives through, not exposed by their modules (module system).
import all Init.Data.Repr
import all Init.Data.ToString.Basic
import all Init.Data.ToString.Extra
import all Init.Data.Array.Basic
import all Init.Data.ByteArray.Basic
import all Init.Data.String.Decode
import all Init.Data.String.Defs
import all Init.Control.Except
import all Init.Data.List.Basic
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.String.Bootstrap
import all Init.Data.Format.Basic
import all Init.Data.List.Scan.Basic
import all Init.System.ST
import all Init.System.IO

@[expose] public section

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

private def purseGuard {config : Config} {ground : ServedBasis.Ground config.deployment}
    {context : Context}
    (payer : ApplicationDispatchAgentPayer.Checked config ground context) : ReadGuard :=
  ⟨⟨context.purseTask⟩, ResourceBirthCodec.physicalRoot (.live payer.cell)⟩

structure Checked (config : Config) (ground : ServedBasis.Ground config.deployment)
    (ingress : ApplicationDispatchAgentIngress.Ingress)
    (issued : ApplicationDispatchHistoricalCore.IssuedEvidence config)
    (reserved : ReservedEvidence config) where
  private mk ::
  contextExact : reserved.context = ingress.reserveContext
  scopeExact : matchesIngress ingress.reserveContext ingress.dispatch
    issued.spec.ticket.resource = true
  base : ApplicationDispatchHistoricalCore.CheckedCandidate config
    ground ingress.dispatch issued
  payer : ApplicationDispatchAgentPayer.Checked config ground ingress.reserveContext
  holdExact : payer.state = AgentGrain.reserve reserved.beforeState
    ingress.reserveContext.reserveAmount
  purseDistinctParent : ingress.reserveContext.purseTask ≠
    ingress.reserveContext.parentTask
  purseDistinctSession : ingress.reserveContext.purseTask ≠
    ingress.dispatch.dispatch.dispatch.session.resource
  purseReadonly : (purseGuard payer).cellId ∉
    (ApplicationDispatchPending.candidateIntent base.checked).writes.map DataWrite.cellId

theorem Checked.purseGuard_current {config : Config} {ground : ServedBasis.Ground config.deployment}
    {ingress : ApplicationDispatchAgentIngress.Ingress}
    {issued : ApplicationDispatchHistoricalCore.IssuedEvidence config}
    {reserved : ReservedEvidence config}
    (checked : Checked config ground ingress issued reserved) :
    (purseGuard checked.payer).expectedRoot =
      ground.view.model.roots (purseGuard checked.payer).cellId :=
  checked.payer.physicalCurrent

/-- The reserve context bound by the original reserve is the ingress's, it is
scoped to the issued ticket, and the payer purse read at `ground` holds exactly
that reserve over the reserve's before-state. -/
theorem Checked.reserve_held_at_opened {config : Config} {ground : ServedBasis.Ground config.deployment}
    {ingress : ApplicationDispatchAgentIngress.Ingress}
    {issued : ApplicationDispatchHistoricalCore.IssuedEvidence config}
    {reserved : ReservedEvidence config}
    (checked : Checked config ground ingress issued reserved) :
    reserved.context = ingress.reserveContext ∧
      matchesIngress ingress.reserveContext ingress.dispatch
        issued.spec.ticket.resource = true ∧
      checked.payer.state = AgentGrain.reserve reserved.beforeState
        ingress.reserveContext.reserveAmount ∧
      ResourceBirthCodec.physicalRoot (.live checked.payer.cell) =
        ground.view.model.roots ⟨ingress.reserveContext.purseTask⟩ :=
  ⟨checked.contextExact, checked.scopeExact, checked.holdExact, checked.payer.physicalCurrent⟩

def checkCurrent (config : Config) (ground : ServedBasis.Ground config.deployment)
    (ingress : ApplicationDispatchAgentIngress.Ingress)
    (issued : ApplicationDispatchHistoricalCore.IssuedEvidence config)
    (reserved : ReservedEvidence config) :
    IO (Except String (Checked config ground ingress issued reserved)) := do
  if contextExact : reserved.context = ingress.reserveContext then
    if scopeExact : matchesIngress ingress.reserveContext ingress.dispatch
        issued.spec.ticket.resource = true then
      match ← ApplicationDispatchHistoricalCore.checkCurrent config ground
          ingress.dispatch issued with
      | .error detail => return .error detail
      | .ok base =>
        match ← ApplicationDispatchAgentPayer.checkCurrent config ground
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

/-- The paid-agent tariff over the already-derived human candidate intent. `base` is a parameter,
never a `let` under the lane binder: the compiler eta-expands a charge-returning definition, and a
`let` in its body would re-derive the whole human candidate intent on every lane query
(see `ApplicationDispatchPending.chargeOf`). -/
def chargeOf {config : Config} {ground : ServedBasis.Ground config.deployment}
    {ingress : ApplicationDispatchAgentIngress.Ingress}
    (base : DataIntent rootBytes) : Charge :=
  fun dimension => match dimension with
    | .incidences => base.exactCharge .incidences + 1
    | .turnBytes => ingress.canonicalBytes.length
    | .witnessBytes => ingress.canonicalBytes.length
    | .proofWork => base.exactCharge .proofWork + 1
    | .memoryTouches => base.exactCharge .memoryTouches + 1
    | .storageBytes => DeployedCharge.storageCharge ground.view
        base.writes
        (ApplicationDispatchAgentIngress.event ingress)
    | other => base.exactCharge other

def charge {config : Config} {ground : ServedBasis.Ground config.deployment}
    {ingress : ApplicationDispatchAgentIngress.Ingress}
    {issued : ApplicationDispatchHistoricalCore.IssuedEvidence config}
    {reserved : ReservedEvidence config}
    (checked : Checked config ground ingress issued reserved) : Charge :=
  chargeOf (config := config) (ground := ground) (ingress := ingress)
    (ApplicationDispatchPending.candidateIntent checked.base.checked)

/-- The app mutation is unchanged, but the event is version21, the physical
purse read guard joins its CAS, and the original reserve receipt is claimed
once. Replay must still certify `reserved` as a prior admitted step. -/
def candidateIntent {config : Config} {ground : ServedBasis.Ground config.deployment}
    {ingress : ApplicationDispatchAgentIngress.Ingress}
    {issued : ApplicationDispatchHistoricalCore.IssuedEvidence config}
    {reserved : ReservedEvidence config}
    (checked : Checked config ground ingress issued reserved) :
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
      exactCharge := (Charge.materialize
        (chargeOf (config := config) (ground := ground) (ingress := ingress) base)).toCharge
      event := ApplicationDispatchAgentIngress.event ingress
      subject := base.subject
      postRootsBound := base.postRootsBound
      guardsReadOnly := guarded }

/-- The held charge is the specified charge. -/
theorem candidateIntent_exactCharge {config : Config} {ground : ServedBasis.Ground config.deployment}
    {ingress : ApplicationDispatchAgentIngress.Ingress}
    {issued : ApplicationDispatchHistoricalCore.IssuedEvidence config}
    {reserved : ReservedEvidence config}
    (checked : Checked config ground ingress issued reserved) :
    (candidateIntent checked).exactCharge = charge checked :=
  Charge.materialize_eq _

theorem candidate_event_version {config : Config} {ground : ServedBasis.Ground config.deployment}
    {ingress : ApplicationDispatchAgentIngress.Ingress}
    {issued : ApplicationDispatchHistoricalCore.IssuedEvidence config}
    {reserved : ReservedEvidence config}
    (checked : Checked config ground ingress issued reserved) :
    (candidateIntent checked).event.codecVersion = 21 := rfl

/-- A human dispatch event11 can never be mistaken for the paid agent event,
even when the app command and HTTP operation identifier are identical. -/
theorem candidate_event_ne_human {config : Config} {ground : ServedBasis.Ground config.deployment}
    {ingress : ApplicationDispatchAgentIngress.Ingress}
    {issued : ApplicationDispatchHistoricalCore.IssuedEvidence config}
    {reserved : ReservedEvidence config}
    (checked : Checked config ground ingress issued reserved) :
    (candidateIntent checked).event ≠
      ApplicationDispatchAdmissionIngress.event ingress.dispatch := by
  intro equal
  have versions := congrArg StableEvent.codecVersion equal
  norm_num [candidate_event_version, ApplicationDispatchAdmissionIngress.event] at versions

end Minidregg.Kernel.ApplicationDispatchAgentCore
