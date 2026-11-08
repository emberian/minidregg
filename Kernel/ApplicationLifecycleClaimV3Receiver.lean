/-
Exact-CAS reservation for a launch-bound lifecycle claim. V1 claims can
remain in historical replay but never produce this SPK launch handoff.

The light route (`receiveServed`, KN2 2b): the claim admits on the light opening's ground at
its head, its original BEGIN selected and re-admitted at that BEGIN's own prefix through the
opening's Reader (`ApplicationLifecycleClaimV3Core.prepare`), committed by
`DurableServed.receiveServed`; launch power goes only to this attempt's own install.
-/
module

public import Kernel.ApplicationLifecycleClaimV3Projection
public import Kernel.NativeHostReplay
public import Kernel.NativeHostLight

@[expose] public section

namespace Minidregg.Kernel.ApplicationLifecycleClaimV3Receiver

open Minidregg.Compiler
open Minidregg.Compiler.ResourceBirthCodec
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Kernel.NativeHost

set_option autoImplicit false

/-- A claim reserved on the light route: its conditional (the original BEGIN re-admitted at
its own prefix under the opening's head, the current claim admitted on the light ground),
its transaction verified unrecorded there, and the appended record exactly its intent's. -/
structure Reservation (config : Config) (opening : DurableServed.Opening ResourceBirthCodec.rootBytes) where
  private mk ::
  ingress : ApplicationLifecycleClaimV3Ingress.Ingress
  grounded : ServedBasis.Grounded config.deployment opening.head
  conditional : ApplicationLifecycleClaimV3Core.Conditional config opening.head grounded.ground ingress
  fresh : grounded.ground.recorded conditional.intent.transactionId = some none
  kind : DurableReceiverIO.Confirmation
  next : DurableServed.Opening ResourceBirthCodec.rootBytes
  height : next.head.height = opening.head.height + 1
  entry : DurableReceiverIO.Entry
  entryExact : entry.record.toList =
    DurableCheckpointCodec.recordFrame.encode (DurableReceiver.IntentRecord.ofIntent conditional.intent)
  /-- This attempt's own append installed the entry (`Received.appended`'s `fresh`). -/
  freshCasWinner : Bool

/-- **What a light reservation proves**: the appended record is the conditional's intent's,
written as the opening's next record; the original BEGIN record it reserves is the one the
re-admitted original BEGIN wrote; its transaction id was verified unrecorded on its ground. -/
theorem Reservation.exact {config : Config} {opening : DurableServed.Opening ResourceBirthCodec.rootBytes}
    (reservation : Reservation config opening) :
    reservation.entry.record.toList = DurableCheckpointCodec.recordFrame.encode
        (DurableReceiver.IntentRecord.ofIntent reservation.conditional.intent) ∧
      reservation.next.head.height = opening.head.height + 1 ∧
      reservation.conditional.original.record =
        DurableReceiver.IntentRecord.ofIntent reservation.conditional.originalAccepted.intent ∧
      reservation.grounded.ground.recorded reservation.conditional.intent.transactionId = some none :=
  ⟨reservation.entryExact, reservation.height, reservation.conditional.original_record_exact,
    reservation.fresh⟩

def Reservation.receipt {config : Config} {opening : DurableServed.Opening ResourceBirthCodec.rootBytes}
    (reservation : Reservation config opening) : NativeHostCodec.Receipt :=
  ⟨reservation.conditional.intent.transactionId, reservation.conditional.intent.event.eventId,
    reservation.next.head.height, reservation.next.served.worldRoot⟩

def Reservation.projection {config : Config} {opening : DurableServed.Opening ResourceBirthCodec.rootBytes}
    (reservation : Reservation config opening) : ApplicationLifecycleClaimV3Projection.Committed :=
  let source := reservation.ingress.base.source
  let served := reservation.next.served
  { core :=
      { source := source
        originalTransaction := reservation.conditional.original.record.transactionId
        originalEvent := reservation.conditional.original.record.event.eventId
        originalNullifier :=
          (ApplicationLifecycleBegin.stableNullifier config.deployment.domain
            config.profile.semantics source.begin.source).nullifierId
        claimReceipt := reservation.receipt
        claimNullifier :=
          (ApplicationLifecycleClaim.stableNullifier config.deployment.domain
            config.profile.semantics source).nullifierId
        appPhysicalRoot := served.roots ⟨source.begin.source.app⟩
        packagePhysicalRoot := served.roots ⟨source.begin.source.packageManifest⟩
        authorityPhysicalRoot := served.roots ⟨config.deployment.authorityCellId⟩
        postWorldRoot := reservation.receipt.worldRoot }
    originalClaim := reservation.ingress }

/-- The SPK launch handoff, only to this attempt's own install and only while the Store's tip
is still exactly its entry. -/
def Reservation.withFreshTip {config : Config} {opening : DurableServed.Opening ResourceBirthCodec.rootBytes}
    {α : Type} (reservation : Reservation config opening) (transport : DurableReceiverIO.Transport)
    (handoff : List UInt8 → IO α) : IO (Except String α) := do
  unless reservation.kind == .installed && reservation.freshCasWinner do
    return .error "launch-bound claim was not freshly installed"
  let .ok current ← DurableReceiverIO.tipIs transport reservation.next.head.height reservation.entry
    | return .error "launch-bound claim physical tip unavailable before handoff"
  if current then
    return .ok (← handoff reservation.projection.canonicalBytes)
  else return .error "launch-bound claim physical tip changed before handoff"

inductive Result (config : Config) (opening : DurableServed.Opening ResourceBirthCodec.rootBytes) where
  | reserved (reservation : Reservation config opening)
  | rejected (detail : String)
  | contention
  | unavailable (detail : String)
  | uncertain (detail : String)

/-- **The light claim**: its keys (`ApplicationLifecycleClaimV3Core.keys`) read into a ground of
`light` at the opening's head, the conditional prepared through the opening's Reader, committed
by `receiveServed`, the readback handed to `adopt`. -/
def receiveServed (config : Config) (transport : DurableReceiverIO.Transport)
    (light : NativeHostLight.Light config) (bytes : List UInt8)
    (adopt : NativeHostLight.Adopt := fun _ _ => pure ()) :
    IO (Result config light.opening) := do
  let some ingress := ApplicationLifecycleClaimV3Ingress.codec.decode bytes
    | return .rejected "noncanonical launch-bound lifecycle claim ingress"
  let grounded ← match ← light.groundedVia transport (ApplicationLifecycleClaimV3Core.keys ingress) with
    | .error detail => return .unavailable detail
    | .ok grounded => pure grounded
  let reader := light.opening.reader transport ResourceBirthCodec.rootBytes
  let conditional ← match ← ApplicationLifecycleClaimV3Core.prepare config reader grounded ingress with
    | .error detail => return .rejected s!"launch-bound BEGIN absent or current claim authority refused: {detail}"
    | .ok conditional => pure conditional
  match fresh : grounded.ground.recorded conditional.intent.transactionId with
  | none => return .rejected "launch-bound claim transaction identity undeclared"
  | some (some _) => return .rejected "launch-bound claim transaction identity already used"
  | some none =>
      match ← DurableServed.receiveServed transport ResourceBirthCodec.rootBytes light.opening
          conditional.intent with
      | .appended kind next height entry entryExact freshCasWinner =>
          adopt next none
          return .reserved ⟨ingress, grounded, conditional, fresh, kind, next, height, entry, entryExact,
            freshCasWinner⟩
      | .replayed _ => return .rejected "launch-bound claim transaction identity already used"
      | .rejected _ => return .rejected "durable launch-bound claim refused"
      | .contention => return .contention
      | .unavailable detail => return .unavailable detail
      | .uncertain detail => return .uncertain detail

end Minidregg.Kernel.ApplicationLifecycleClaimV3Receiver
