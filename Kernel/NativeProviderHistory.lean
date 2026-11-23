/-
Provider reservation continuity through one exact, admitted hard fence.
Only the retained signed disconnect call and its verifier-recomputed receipt
may be excepted. No final-value equality or same-shaped replacement supplies
this evidence. All other suffix entries retain NativeReserveContinuity's
conservative ordinary-other rule, including authority-family exclusions.
-/
module

public import Kernel.NativeReserveContinuity
public import Kernel.ProviderRoute

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

@[expose] public section

namespace Minidregg.Kernel.NativeProviderHistory

open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.DeclaredActionLowering
open Minidregg.Kernel.DurableDataIntent
open Minidregg.Compiler
open Minidregg.Kernel.NativeHost
open Minidregg.Kernel.NativeReserveContinuity

set_option autoImplicit false

/-- A retained API17 observation's historical position and world root. The
root binds the deployed world's seed/log/cells under its existing digest
binding premise; a counter alone is deliberately insufficient. -/
structure PriorChecked where
  acceptedCount : Nat
  worldRoot : Digest
  deriving DecidableEq, Repr

def priorBounds (reserveCount currentCount : Nat) (point : PriorChecked) : Bool :=
  decide (0 < reserveCount ∧ reserveCount ≤ point.acceptedCount ∧
    point.acceptedCount ≤ currentCount)

def priorReceiptMatches (point : PriorChecked) (receipt : NativeHostCodec.Receipt) : Bool :=
  decide (receipt.acceptedCount = point.acceptedCount ∧ receipt.worldRoot = point.worldRoot)

/-- This receipt comes from the semantic walk at precisely the old observation
index. Its world root is recomputed there; it is not a client receipt decoder. -/
structure PriorInPrefix {config : Config} (session : NativeHostSession.Walked config)
    (reserveCount : Nat) (point : PriorChecked) where
  bounds : priorBounds reserveCount session.target.image.accepted.length point = true
  receipt : NativeHostCodec.Receipt
  receiptAt : session.verified.receiptAt (point.acceptedCount - 1) = some receipt
  exactPoint : priorReceiptMatches point receipt = true

theorem PriorInPrefix.exact_root {config : Config}
    {session : NativeHostSession.Walked config} {reserveCount : Nat} {point : PriorChecked}
    (checked : PriorInPrefix session reserveCount point) :
    checked.receipt.acceptedCount = point.acceptedCount ∧
    checked.receipt.worldRoot = point.worldRoot := by
  simpa only [priorReceiptMatches, decide_eq_true_eq] using checked.exactPoint

def checkPrior {config : Config} (session : NativeHostSession.Walked config)
    (reserveCount : Nat) (point : PriorChecked) :
    Except String (PriorInPrefix session reserveCount point) := do
  if bounds : priorBounds reserveCount session.target.height point = true then
    match receiptAt : session.verified.receiptAt (point.acceptedCount - 1) with
    | none => .error "prior checked prefix receipt is absent from verified history"
    | some receipt =>
        if exactPoint : priorReceiptMatches point receipt = true then
          return ⟨bounds, receipt, receiptAt, exactPoint⟩
        else .error "prior checked root differs from verified historical prefix"
  else .error "prior checked count is outside reserve and current prefix bounds"

/-- Exact evidence for one already admitted provider write. -/
structure ExactWrite {config : Config} (session : NativeHostSession.Walked config)
    (receipt : NativeHostCodec.Receipt) (call : List UInt8) (provider : CellId) where
  positive : 0 < receipt.acceptedCount
  receiptExact : session.verified.receiptAt (receipt.acceptedCount - 1) = some receipt
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
    if receiptExact : session.verified.receiptAt (receipt.acceptedCount - 1) = some receipt then
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

/-- The last two occurrences suffice when a continuity request exempts at most one fence. -/
structure LastTwo where
  last : Nat := 0
  previous : Nat := 0
  deriving Inhabited

def LastTwo.after (p : LastTwo) (anchor fence : Nat) : Bool :=
  decide (anchor < (if p.last = fence then p.previous else p.last))

def LastTwo.push (p : LastTwo) (height : Nat) : LastTwo := ⟨height, p.last⟩

theorem LastTwo.after_push (p : LastTwo) (height anchor fence : Nat)
    (ordered : p.previous ≤ p.last) (fresh : p.last < height) :
    (p.push height).after anchor fence =
      ((decide (anchor < height ∧ height ≠ fence)) || p.after anchor fence) := by
  simp only [LastTwo.after, LastTwo.push]
  by_cases h : height = fence <;> by_cases l : p.last = fence <;> simp_all <;> omega

/-- info: 'Minidregg.Kernel.NativeProviderHistory.LastTwo.after_push' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms LastTwo.after_push

/-- An isolated fence is safe; a preceding conflicting write stays visible. -/
theorem fence_alone_and_rewrite :
    (⟨9, 4⟩ : LastTwo).after 4 9 = false ∧ (⟨9, 5⟩ : LastTwo).after 4 9 = true := by decide

/-- One historical position, sufficient for exact anchor, fence and old-root selection.
Only signed invocation frames can equal an authored reserve or fence. -/
structure Position where
  receipt : NativeHostCodec.Receipt
  invocation : Option (List UInt8)
  written : List Nat

structure Index where
  positions : Array Position := #[]
  blocked : LastTwo := {}
  writes : List (Nat × LastTwo) := []
  targets : List (Nat × LastTwo) := []

private def mark (height : Nat) (table : List (Nat × LastTwo)) (cell : Nat) :=
  let prior := (table.lookup cell).getD {}
  (cell, prior.push height) :: table.filter (fun row => row.1 != cell)

def Index.append (index : Index) (record : DurableReceiver.IntentRecord) (receipt : NativeHostCodec.Receipt) :
    Index :=
  let bytes := record.event.canonicalBytes
  let written := (record.writes.map (·.cellId.value)).eraseDups
  let invocation := if (DeclaredResourceController.decodeSignedBytes bytes).isSome then some bytes else none
  let height := receipt.acceptedCount
  let common := { index with
    positions := index.positions.push ⟨receipt, invocation, written⟩
    writes := written.foldl (mark height) index.writes }
  match ordinaryTargets bytes with
  | none => { common with blocked := index.blocked.push height }
  | some targets => { common with targets := targets.eraseDups.foldl (mark height) index.targets }

private def Index.exact (index : Index) (config : Config) (receipt : NativeHostCodec.Receipt)
    (call : List UInt8) (cell : Nat) (fenced : Bool) : Except String Unit := do
  if receipt.acceptedCount = 0 then
    throw (if fenced then "history receipt has zero accepted count" else "reserve receipt has zero accepted count")
  let position := index.positions[receipt.acceptedCount - 1]?
  unless position.map (·.receipt) == some receipt do
    throw (if fenced then "history receipt differs from admitted prefix" else "confirmed reserve receipt differs from admitted prefix")
  let some ingress := reserveIngress? config call
    | throw (if fenced then "history call is not a canonical signed invocation" else "reserve call is not a canonical signed invocation")
  unless (position.bind (·.invocation)) == some ingress do
    throw (if fenced then "history call differs from admitted ingress" else "confirmed reserve call differs from admitted history")
  unless position.any (fun p => p.written.contains cell) do
    throw (if fenced then "confirmed history call did not write the provider" else "confirmed call did not write the provider resource")

def Index.check (index : Index) (config : Config) (authority : List CellId)
    (anchor : NativeHostCodec.Receipt) (call : List UInt8) (provider : CellId)
    (fence : Option (List UInt8 × NativeHostCodec.Receipt)) (prior : Option PriorChecked) : Except String Unit := do
  index.exact config anchor call provider.value fence.isSome
  let exception ← match fence with
    | none => pure 0
    | some (fenceCall, receipt) => do
        index.exact config receipt fenceCall provider.value true
        unless anchor.acceptedCount < receipt.acceptedCount do throw "allowed fence does not follow reserve"
        unless exactHardFence provider call fenceCall do
          throw "allowed fence is not the same provider subject's canonical held disconnect"
        pure receipt.acceptedCount
  let later := fun (p : LastTwo) => p.after anchor.acceptedCount exception
  if later index.blocked || (index.writes.lookup provider.value).any later ||
      authority.any (fun id => (index.targets.lookup id.value).any later) then
    throw (if fence.isSome then "provider rewrite or authority-changing ingress outside exact fence"
      else "provider rewrite or authority-changing ingress after reserve")
  if let some point := prior then
    unless priorBounds anchor.acceptedCount index.positions.size point do
      throw "prior checked count is outside reserve and current prefix bounds"
    let some p := index.positions[point.acceptedCount - 1]?
      | throw "prior checked prefix receipt is absent from verified history"
    unless priorReceiptMatches point p.receipt do throw "prior checked root differs from verified historical prefix"

open Minidregg.Theory Minidregg.Compiler.NativeHostCodec Minidregg.Compiler.Tower256ConcreteBackend

private def lastStream : StreamCodec LastTwo :=
  StreamCodec.xmap (StreamCodec.product StreamCodec.nat StreamCodec.nat)
    (fun p => (p.last, p.previous)) (fun (a,b) => ⟨a,b⟩) (by intro p; cases p; rfl)

private def positionStream : StreamCodec Position :=
  StreamCodec.xmap (StreamCodec.product receiptStream (StreamCodec.product
    (StreamCodec.option bytesStream) (StreamCodec.list StreamCodec.nat)))
    (fun p => (p.receipt, p.invocation, p.written)) (fun (r,i,w) => ⟨r,i,w⟩) (by intro p; cases p; rfl)

def indexStream : StreamCodec Index :=
  let table := StreamCodec.list (StreamCodec.product StreamCodec.nat lastStream)
  StreamCodec.xmap (StreamCodec.product (StreamCodec.list positionStream)
    (StreamCodec.product lastStream (StreamCodec.product table table)))
    (fun i => (i.positions.toList, i.blocked, i.writes, i.targets))
    (fun (ps,b,w,t) => ⟨ps.toArray,b,w,t⟩) (by intro i; cases i; simp)

end Minidregg.Kernel.NativeProviderHistory
