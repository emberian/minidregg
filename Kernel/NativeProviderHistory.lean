/-
Provider reservation continuity through one exact, admitted hard fence.
Only the retained signed disconnect call and its verifier-recomputed receipt
may be excepted. No final-value equality or same-shaped replacement supplies
this evidence. All other suffix entries retain NativeReserveContinuity's
conservative ordinary-other rule, including authority-family exclusions.
-/
import Kernel.NativeReserveContinuity
import Kernel.ProviderRoute

namespace Minidregg.Kernel.NativeProviderHistory

open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.DeclaredActionLowering
open Minidregg.Kernel.DurableDataIntent
open Minidregg.Compiler
open Minidregg.Kernel.NativeHost
open Minidregg.Kernel.NativeReserveContinuity

set_option autoImplicit false

/-- Exact evidence for one already admitted provider write. -/
structure ExactWrite {config : Config} (session : NativeHostSession.Walked config)
    (receipt : NativeHostCodec.Receipt) (call : List UInt8) (provider : CellId) where
  positive : 0 < receipt.acceptedCount
  receiptExact : session.verified.receipts[receipt.acceptedCount - 1]? = some receipt
  ingress : List UInt8
  parsed : reserveIngress? config call = some ingress
  callExact : (session.target.image.accepted[receipt.acceptedCount - 1]?).map
    (fun record => record.event.canonicalBytes) = some ingress
  written : (session.target.image.accepted[receipt.acceptedCount - 1]?).any
    (fun record => decide (writesCell record provider)) = true

def exactWrite {config : Config} (session : NativeHostSession.Walked config)
    (receipt : NativeHostCodec.Receipt) (call : List UInt8) (provider : CellId) :
    Except String (ExactWrite session receipt call provider) := do
  if positive : 0 < receipt.acceptedCount then
    if receiptExact : session.verified.receipts[receipt.acceptedCount - 1]? = some receipt then
      match parsed : reserveIngress? config call with
      | none => .error "history call is not a canonical signed invocation"
      | some ingress =>
          if callExact : (session.target.image.accepted[receipt.acceptedCount - 1]?).map
              (fun record => record.event.canonicalBytes) = some ingress then
            if written : (session.target.image.accepted[receipt.acceptedCount - 1]?).any
                (fun record => decide (writesCell record provider)) = true then
              return ⟨positive, receiptExact, ingress, parsed, callExact, written⟩
            else .error "confirmed history call did not write the provider"
          else .error "history call differs from admitted ingress"
    else .error "history receipt differs from admitted prefix"
  else .error "history receipt has zero accepted count"

def command? (call : List UInt8) : Option DeclaredResourceController.Command := do
  let .invoke signed ← NativeHostCodec.callCodec.decode call | none
  DeclaredResourceController.commandCodec.decode signed.commandBytes

/-- Read the old coordinates from the five compare-and-write actions, then
compare the WHOLE payload with the source-owned disconnect authoring below. -/
def before? (payload : DeclaredResourceController.Payload) : Option ProviderRoute.State :=
  match payload with
  | .scalar [.write _ (some generation) _, .write _ (some status) _,
      .write _ (some remaining) _, .write _ (some reserved) _, .write _ (some route) _] =>
      some ⟨⟨generation, status, remaining, reserved⟩, route⟩
  | _ => none

/-- Additional incidences may witness a parent's exact old coordinates. They
must be canonical no-op grain inputs; no arbitrary publication rides along. -/
def exactWitness (target : DeclaredResourceController.Target) : Bool :=
  match target.payload with
  | .scalar [.write _ (some generation) _, .write _ (some status) _,
      .write _ (some remaining) _, .write _ (some reserved) _] =>
      decide (target.kind = .object) && decide (target.schemaVersion = 1) &&
      decide (target.payload = .scalar
        (AgentGrain.Operation.input.actions target.target ⟨generation, status, remaining, reserved⟩))
  | _ => false

/-- One canonical hard reserve, plus optional exact parent witnesses. Its
authored post must be the fence's complete five-coordinate old state. Exact
accepted ingress and the intervening no-write suffix establish that this is
the same reservation, not merely a matching current balance. -/
def exactHardReserve (provider : CellId) (reserve : DeclaredResourceController.Command)
    (held : ProviderRoute.State) : Bool :=
  match reserve.targets.filter (fun target => target.target == provider.value) with
  | [target] =>
      match before? target.payload with
      | some before =>
          decide (reserve.run = none) && decide (target.kind = .object) &&
          decide (target.schemaVersion = 1) &&
          decide (before.grain.status = 1) && decide (before.grain.reserved = 0) &&
          decide (before.route = 0) && decide (0 < held.grain.reserved) &&
          decide (1 ≤ held.route ∧ held.route ≤ 3) &&
          decide (held = ProviderRoute.after (.reserve held.grain.reserved) held.route before) &&
          decide (target.payload = .scalar (ProviderRoute.actions provider.value before held)) &&
          (reserve.targets.filter (fun other => other.target != provider.value)).all exactWitness
      | none => false
  | _ => false

def exactHardFence (provider : CellId) (reserveCall fenceCall : List UInt8) : Bool :=
  match command? reserveCall, command? fenceCall with
  | some reserve, some fence =>
      match fence.targets with
      | [target] =>
          match before? target.payload with
          | some before =>
              decide (reserve.subject = fence.subject) &&
              exactHardReserve provider reserve before &&
              decide (fence.run = none) &&
              decide (target.kind = .object) &&
              decide (target.target = provider.value) &&
              decide (target.schemaVersion = 1) &&
              decide (before.grain.status = 3) &&
              decide (0 < before.grain.reserved) &&
              decide (target.payload = .scalar (ProviderRoute.actions provider.value before
                (ProviderRoute.after .disconnect before.route before)))
          | none => false
      | _ => false
  | _, _ => false

/-- The permitted source transition keeps the held funds and route intact. -/
theorem hardFence_preserves_hold (before : ProviderRoute.State)
    (held : before.grain.status = 3) :
    (ProviderRoute.after .disconnect before.route before).grain.remaining = before.grain.remaining ∧
    (ProviderRoute.after .disconnect before.route before).grain.reserved = before.grain.reserved ∧
    (ProviderRoute.after .disconnect before.route before).route = before.route := by
  simp [ProviderRoute.after, AgentGrain.Operation.after, AgentGrain.trip, held]

/-- The index is the absolute accepted count (one-based), not a caller's
operation id. The sole exception must also have the exact admitted ingress. -/
def safeAt {config : Config} (session : NativeHostSession.Walked config)
    (provider : CellId) (fenceCount : Nat) (fenceIngress : List UInt8)
    (entry : DurableReceiver.IntentRecord × Nat) : Bool :=
  if entry.2 = fenceCount then entry.1.event.canonicalBytes == fenceIngress
  else ordinaryOther session provider entry.1

theorem safeAt_other_no_write {config : Config}
    (session : NativeHostSession.Walked config) (provider : CellId)
    (fenceCount count : Nat) (fenceIngress : List UInt8)
    (record : DurableReceiver.IntentRecord) (other : count ≠ fenceCount)
    (safe : safeAt session provider fenceCount fenceIngress (record, count) = true) :
    ¬ writesCell record provider := by
  apply ordinaryOther_no_provider_write session provider record
  simpa [safeAt, other] using safe

def suffixEntries {config : Config} (session : NativeHostSession.Walked config)
    (reserveCount : Nat) : List (DurableReceiver.IntentRecord × Nat) :=
  let records := session.target.image.accepted.drop reserveCount
  records.zip ((List.range records.length).map (fun offset => reserveCount + offset + 1))

structure Continuity {config : Config} (session : NativeHostSession.Walked config)
    (anchor fence : NativeHostCodec.Receipt) (reserveCall fenceCall : List UInt8)
    (provider : CellId) where
  reserveExact : ExactWrite session anchor reserveCall provider
  fenceExact : ExactWrite session fence fenceCall provider
  later : anchor.acceptedCount < fence.acceptedCount
  hardFence : exactHardFence provider reserveCall fenceCall = true
  suffixSafe : (suffixEntries session anchor.acceptedCount).all
    (safeAt session provider fence.acceptedCount fenceExact.ingress) = true

theorem Continuity.no_other_provider_write {config : Config}
    {session : NativeHostSession.Walked config} {anchor fence : NativeHostCodec.Receipt}
    {reserveCall fenceCall : List UInt8} {provider : CellId}
    (checked : Continuity session anchor fence reserveCall fenceCall provider)
    (record : DurableReceiver.IntentRecord) (count : Nat)
    (member : (record, count) ∈ suffixEntries session anchor.acceptedCount)
    (other : count ≠ fence.acceptedCount) : ¬ writesCell record provider :=
  safeAt_other_no_write session provider fence.acceptedCount count
    checked.fenceExact.ingress record other ((List.all_eq_true.mp checked.suffixSafe) _ member)

def check {config : Config} (session : NativeHostSession.Walked config)
    (anchor fence : NativeHostCodec.Receipt) (reserveCall fenceCall : List UInt8)
    (provider : CellId) :
    Except String (Continuity session anchor fence reserveCall fenceCall provider) := do
  let reserveExact ← exactWrite session anchor reserveCall provider
  let fenceExact ← exactWrite session fence fenceCall provider
  if later : anchor.acceptedCount < fence.acceptedCount then
    if hardFence : exactHardFence provider reserveCall fenceCall = true then
      if suffixSafe : (suffixEntries session anchor.acceptedCount).all
          (safeAt session provider fence.acceptedCount fenceExact.ingress) = true then
        return ⟨reserveExact, fenceExact, later, hardFence, suffixSafe⟩
      else .error "provider rewrite or authority-changing ingress outside exact fence"
    else .error "allowed fence is not the same provider subject's canonical held disconnect"
  else .error "allowed fence does not follow reserve"

end Minidregg.Kernel.NativeProviderHistory
