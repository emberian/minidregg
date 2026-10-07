/-
Fresh paid agent dispatch. An event21 permit exists only after same-tip native
admission, a freshly won durable CAS, exact complete post-image readback and
validation. Already-present and reply-lost readback preserves the original
receipt, but cannot mint another physical delivery permit.
-/
import Compiler.ApplicationReceivingDomain
import Kernel.ApplicationDispatchAgentProjection

namespace Minidregg.Kernel.ApplicationDispatchAgentReceiver

open Minidregg.Compiler
open Minidregg.Compiler.ResourceBirthCodec
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.IndexedProgram
open Minidregg.Kernel.NativeHost

set_option autoImplicit false

/-- Exact committed evidence retains its receipt independently of delivery. -/
structure Committed (config : Config) where
  private mk ::
  target : Durable
  old : NativeHostReplay.Verified config target
  ingress : ApplicationDispatchAgentIngress.Ingress
  admitted : NativeHostReplay.AgentDispatchAt config old.opened ingress
  projection : ApplicationDispatchAgentProjection.Paid
  readback : NativeHostReplay.ExactReadback config old
  derivedExact : readback.derived.intent = admitted.intent
  confirmation : DurableReceiverIO.Confirmation
  store : DurableHistory.StoreIdentity
  reader : DurableHistoryReader.Reader ResourceBirthCodec.rootBytes store
  freshCasWinner : Bool

def Committed.verified {config : Config} (permit : Committed config) :
    NativeHostReplay.Verified config
      (NativeHostReplay.exactCandidate permit.old
        permit.readback.derived permit.readback.ready) :=
  NativeHostReplay.extendExact permit.reader permit.old permit.readback

def Committed.receipt {config : Config} (permit : Committed config) : NativeHostCodec.Receipt :=
  let candidate := NativeHostReplay.exactCandidate permit.old
    permit.readback.derived permit.readback.ready
  ⟨permit.readback.derived.intent.transactionId,
    permit.readback.derived.intent.event.eventId,
    permit.old.opened.durable.height + 1,
    candidate.worldRoot⟩

theorem Committed.receipt_in_verified {config : Config} (committed : Committed config) :
    committed.verified.receipts = committed.old.receipts ++ [committed.receipt] :=
  NativeHostReplay.extendExact_receipts committed.reader committed.old committed.readback

theorem Committed.postRecord_exact {config : Config} (permit : Committed config) :
    permit.readback.appended.entry.record =
      DurableCheckpointCodec.recordFrame.encode
        (DurableReceiver.IntentRecord.ofIntent permit.readback.derived.intent) :=
  NativeHostReplay.extendExact_physicalRecord permit.old permit.readback

/-- Exact readback alone is not delivery authority. Both witnesses must come
from this attempt's fresh installed physical CAS branch. -/
structure Permit (config : Config) extends Committed config where
  private mk ::
  fresh : toCommitted.freshCasWinner = true
  installed : toCommitted.confirmation = .installed

def Permit.verified {config : Config} (permit : Permit config) :
    NativeHostReplay.Verified config
      (NativeHostReplay.exactCandidate permit.old
        permit.readback.derived permit.readback.ready) := permit.toCommitted.verified

def Permit.receipt {config : Config} (permit : Permit config) : NativeHostCodec.Receipt :=
  permit.toCommitted.receipt

theorem Permit.receipt_in_verified {config : Config} (permit : Permit config) :
    permit.verified.receipts = permit.old.receipts ++ [permit.receipt] :=
  permit.toCommitted.receipt_in_verified

theorem Permit.postRecord_exact {config : Config} (permit : Permit config) :
    permit.readback.appended.entry.record =
      DurableCheckpointCodec.recordFrame.encode
        (DurableReceiver.IntentRecord.ofIntent permit.readback.derived.intent) :=
  permit.toCommitted.postRecord_exact

theorem Permit.won_fresh_installed {config : Config} (permit : Permit config) :
    permit.freshCasWinner = true ∧ permit.confirmation = .installed :=
  ⟨permit.fresh, permit.installed⟩

private def permitCodec : LawfulCodec
    (ApplicationDispatchAgentProjection.Paid × NativeHostCodec.Receipt) :=
  NativeHostCodec.framed
    ApplicationReceivingDomain.agentDispatchCommittedPermitFrame
    (StreamCodec.product ApplicationDispatchAgentProjection.paidStream
      NativeHostCodec.receiptStream)

/-- Strict frame inspection is read-only; it does not prove a CAS. Host may
inspect only the exact bytes received from its private op46 process. -/
def inspectCommittedBytes (bytes : List UInt8) :
    Option (ApplicationDispatchAgentProjection.Paid × NativeHostCodec.Receipt) :=
  permitCodec.decode bytes

private def Permit.canonicalBytes {config : Config} (permit : Permit config) : List UInt8 :=
  permitCodec.encode (permit.projection, permit.receipt)

/-- A point-in-time native response handoff, not a lease across the later
physical fd3 hop. Host must also check the live parent/purse process fences. -/
def Permit.withFreshTip {config : Config} {α : Type} (permit : Permit config)
    (handoff : List UInt8 → IO α) : IO (Except String α) := do
  unless permit.freshCasWinner && permit.confirmation == .installed do
    return .error "agent dispatch attempt did not freshly win physical CAS"
  let .ok current ← DurableReceiverIO.tipIs config.transport
      permit.readback.appended.next.height permit.readback.appended.entry
    | return .error "agent dispatch physical tip unavailable before handoff"
  if current then
    return .ok (← handoff permit.canonicalBytes)
  else return .error "agent dispatch physical tip changed before handoff"

inductive Result (config : Config) where
  | permitted (permit : Permit config)
  | committed (committed : Committed config)
  | rejected (detail : String)
  | contention
  | unavailable (detail : String)
  | uncertain (detail : String)

/-- An exact committed nonwinner remains receipt evidence; it can never be
promoted to another physical dispatch merely because readback agrees. -/
def Committed.result {config : Config} (committed : Committed config) : Result config :=
  if fresh : committed.freshCasWinner = true then
    if installed : committed.confirmation = .installed then
      .permitted ⟨committed, fresh, installed⟩
    else .committed committed
  else .committed committed

theorem nonwinner_receipt_only {config : Config} (committed : Committed config)
    (notFresh : committed.freshCasWinner = false) :
    committed.result = .committed committed := by
  simp [Committed.result, notFresh]

theorem recovered_receipt_only {config : Config} (committed : Committed config)
    (recovered : committed.confirmation = .recoveredAfterUncertainResponse) :
    committed.result = .committed committed := by
  simp [Committed.result, recovered]

theorem fresh_installed_permitted {config : Config} (committed : Committed config)
    (fresh : committed.freshCasWinner = true)
    (installed : committed.confirmation = .installed) :
    ∃ permit : Permit config,
      committed.result = .permitted permit ∧ permit.toCommitted = committed := by
  refine ⟨⟨committed, fresh, installed⟩, ?_, rfl⟩
  simp [Committed.result, fresh, installed]

#assert_axioms Committed.receipt_in_verified
#assert_axioms nonwinner_receipt_only
#assert_axioms recovered_receipt_only
#assert_axioms fresh_installed_permitted
#assert_axioms Permit.won_fresh_installed

def receiveVerified (config : Config) {target : Durable}
    (old : NativeHostReplay.Verified config target)
    (bytes : List UInt8) : IO (Result config) := do
  let some ingress := ApplicationDispatchAgentIngress.codec.decode bytes
    | return .rejected "noncanonical paid agent dispatch ingress"
  let .agent _ _ := ingress.dispatch.dispatch.dispatch.session.origin
    | return .rejected "paid agent dispatch requires agent-origin session"
  let .ok admitted ← NativeHostReplay.admitAgentDispatchVerified old ingress
    | return .rejected "agent dispatch native admission or prior reserve refused"
  let some projection := ApplicationDispatchAgentProjection.ofAgentDispatchAt admitted
    | return .rejected "agent dispatch physical projection refused"
  let derived := admitted.toDerived
  if old.opened.durable.image.accepted.findIdx?
      (fun record => record.transactionId == derived.intent.transactionId) != none then
    return .rejected "agent dispatch transaction identity already used"
  let (freshCasWinner, result) ← DurableReceiverIO.receiveLoadedDetailedWithFresh config.transport
    ResourceBirthCodec.rootBytes old.opened.durable derived.intent
  match result with
  | .exact kind appended =>
      match NativeHostReplay.ExactReadback.ofAppended old derived appended with
      | .error detail => return .uncertain s!"agent dispatch post-image validation: {detail}"
      | .ok ⟨proof, proofDerived⟩ =>
            let ⟨_, reader⟩ ← match ← DurableHistoryStore.readerOf config.transport ResourceBirthCodec.rootBytes appended.next with
              | .error detail => return .uncertain s!"post-append history reader: {detail}"
              | .ok reader => pure reader
            let committed : Committed config := ⟨target, old, ingress, admitted, projection,
              proof, ((congrArg NativeHostReplay.Derived.intent proofDerived).trans admitted.toDerived_intent),
              kind, _, reader, freshCasWinner⟩
            return committed.result
  | .ordinary ordinary =>
      match ordinary with
      | .confirmed _ _ =>
          return .uncertain "agent dispatch confirmation lacks exact fresh post-CAS readback"
      | .rejected _ => return .rejected "durable agent dispatch refused"
      | .contention => return .contention
      | .unavailable detail => return .unavailable detail
      | .uncertain detail => return .uncertain detail

end Minidregg.Kernel.ApplicationDispatchAgentReceiver
