/-
Fresh launch-bound physical lifecycle completion. The original v3 claim is bound
to the same native-admitted chronological Replay context, the host custodian
report and current law are checked, and the exact event-25 intent is submitted
once through one CAS with complete physical post-image readback.

The light route (`receiveServed`, KN2 2b) serves every completion but a STOP's: the original
claim is selected and re-admitted at its own prefix through the light opening's Reader
(`ApplicationLifecycleCompletionV2Admission.prepareConditional`), the current part admits on
the opening's ground at its head, the commit is `DurableServed.receiveServed`. A STOP's
completion still checks the running incarnation from the walk (`receiveVerified`).
-/
module

public import Kernel.NativeHostReplay
public import Kernel.NativeHostLight

@[expose] public section

namespace Minidregg.Kernel.ApplicationLifecycleCompletionV2Receiver

open Minidregg.Compiler
open Minidregg.Compiler.ResourceBirthCodec
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Kernel.NativeHost

set_option autoImplicit false

structure Confirmed (config : Config) where
  private mk ::
  target : Durable
  old : NativeHostReplay.Verified config target
  ingress : ApplicationLifecycleCompletionV2Ingress.Ingress
  admitted : NativeHostReplay.CompletionAtV2 config old.opened ingress
  readback : NativeHostReplay.ExactReadback config old
  derivedExact : readback.derived.intent = admitted.intent
  confirmation : DurableReceiverIO.Confirmation
  store : DurableHistory.StoreIdentity
  reader : DurableHistoryReader.Reader ResourceBirthCodec.rootBytes store

def Confirmed.verified {config : Config} (confirmed : Confirmed config) :
    NativeHostReplay.Verified config
      (NativeHostReplay.exactCandidate confirmed.old
        confirmed.readback.derived confirmed.readback.ready confirmed.readback.tag) :=
  NativeHostReplay.extendExact confirmed.reader confirmed.old confirmed.readback

def Confirmed.receipt {config : Config} (confirmed : Confirmed config) :
    NativeHostCodec.Receipt :=
  let old := confirmed.old
  let candidate := NativeHostReplay.exactCandidate old
    confirmed.readback.derived confirmed.readback.ready confirmed.readback.tag
  ⟨confirmed.readback.derived.intent.transactionId,
    confirmed.readback.derived.intent.event.eventId,
    old.opened.durable.height + 1,
    candidate.worldRoot⟩

theorem Confirmed.event_exact {config : Config} (confirmed : Confirmed config) :
    confirmed.readback.derived.intent.event =
      ApplicationLifecycleCompletionV2Ingress.event confirmed.ingress := by
  rw [confirmed.derivedExact]
  exact ApplicationLifecycleCompletionV2Core.intent_event confirmed.admitted.conditional

theorem Confirmed.postRecord_exact {config : Config} (confirmed : Confirmed config) :
    confirmed.readback.appended.entry.record.toList =
      DurableCheckpointCodec.recordFrame.encode
        (DurableReceiver.IntentRecord.ofIntent confirmed.readback.derived.intent) :=
  NativeHostReplay.extendExact_physicalRecord confirmed.old confirmed.readback

/-- The confirmed successor is admitted under `config`: the read-back intent
carries this ingress's event, and `validateLoaded config` accepts the one
candidate extending the verified tip by that read-back intent. -/
theorem Confirmed.successor_validated {config : Config} (confirmed : Confirmed config) :
    confirmed.readback.derived.intent.event =
        ApplicationLifecycleCompletionV2Ingress.event confirmed.ingress ∧
      NativeHost.validateLoaded config
          (NativeHostReplay.exactCandidate confirmed.old
            confirmed.readback.derived confirmed.readback.ready confirmed.readback.tag) =
        .ok confirmed.readback.after :=
  ⟨confirmed.event_exact, confirmed.readback.validated⟩

inductive Result (config : Config) where
  | confirmed (confirmed : Confirmed config)
  | rejected (detail : String)
  | contention
  | unavailable (detail : String)
  | uncertain (detail : String)

def receiveVerified (config : Config) {target : Durable}
    (old : NativeHostReplay.Verified config target)
    (bytes : List UInt8) : IO (Result config) := do
  let some ingress := ApplicationLifecycleCompletionV2Ingress.codec.decode bytes
    | return .rejected "noncanonical checked lifecycle completion ingress"
  let admitted ← match ← NativeHostReplay.admitCompletionV2Verified old ingress with
    | .error detail => return .rejected detail
    | .ok admitted => pure admitted
  let derived := admitted.toDerived
  if old.opened.durable.firstIndex derived.intent.transactionId != none then
    return .rejected "checked lifecycle completion transaction identity already used"
  let result ← DurableReceiverIO.receiveLoadedDetailed config.transport
    ResourceBirthCodec.rootBytes old.opened.durable derived.intent
  match result with
  | .exact kind appended =>
      match NativeHostReplay.ExactReadback.ofAppended old derived appended with
      | .error detail => return .uncertain s!"checked lifecycle completion post-image: {detail}"
      | .ok ⟨proof, proofDerived⟩ =>
            match ← DurableHistoryStore.readerOf config.transport ResourceBirthCodec.rootBytes appended.next with
            | .error detail => return .uncertain s!"post-append history reader: {detail}"
            | .ok ⟨_, reader⟩ =>
              return .confirmed ⟨target, old, ingress, admitted, proof,
                ((congrArg NativeHostReplay.Derived.intent proofDerived).trans admitted.toDerived_intent), kind, _, reader⟩
  | .ordinary ordinary =>
      match ordinary with
      | .confirmed _ _ =>
          return .uncertain "checked lifecycle completion lacks exact post-CAS readback"
      | .rejected _ => return .rejected "durable checked lifecycle completion refused"
      | .contention => return .contention
      | .unavailable detail => return .unavailable detail
      | .uncertain detail => return .uncertain detail

/-! ## The light route -/

/-- A completion confirmed on the light route: its candidate (original claim re-admitted at its
own prefix under the opening's head, current law, custodian report and markers on the light
ground), not a STOP's, its transaction verified unrecorded, the appended record its intent's. -/
structure LightConfirmed (config : Config) (opening : DurableServed.Opening ResourceBirthCodec.rootBytes) where
  private mk ::
  ingress : ApplicationLifecycleCompletionV2Ingress.Ingress
  grounded : ServedBasis.Grounded config.deployment opening.head
  conditional : ApplicationLifecycleCompletionV2Admission.Candidate config opening.head grounded.ground ingress
  notStop : ingress.source.originalBegin.base.source.kind ≠ .stop
  fresh : grounded.ground.recorded (ApplicationLifecycleCompletionV2Core.intent conditional).transactionId =
    some none
  kind : DurableReceiverIO.Confirmation
  next : DurableServed.Opening ResourceBirthCodec.rootBytes
  height : next.head.height = opening.head.height + 1
  entry : DurableReceiverIO.Entry
  entryExact : entry.record.toList = DurableCheckpointCodec.recordFrame.encode
    (DurableReceiver.IntentRecord.ofIntent (ApplicationLifecycleCompletionV2Core.intent conditional))

/-- **What a light completion proves**: the appended record is the candidate's intent's, at the
opening's next height; it carries this ingress's event; its transaction id was verified
unrecorded on its ground. -/
theorem LightConfirmed.exact {config : Config} {opening : DurableServed.Opening ResourceBirthCodec.rootBytes}
    (confirmed : LightConfirmed config opening) :
    confirmed.entry.record.toList = DurableCheckpointCodec.recordFrame.encode
        (DurableReceiver.IntentRecord.ofIntent (ApplicationLifecycleCompletionV2Core.intent confirmed.conditional)) ∧
      confirmed.next.head.height = opening.head.height + 1 ∧
      (ApplicationLifecycleCompletionV2Core.intent confirmed.conditional).event =
        ApplicationLifecycleCompletionV2Ingress.event confirmed.ingress ∧
      confirmed.grounded.ground.recorded
        (ApplicationLifecycleCompletionV2Core.intent confirmed.conditional).transactionId = some none :=
  ⟨confirmed.entryExact, confirmed.height,
    ApplicationLifecycleCompletionV2Core.intent_event confirmed.conditional, confirmed.fresh⟩

inductive LightResult (config : Config) (opening : DurableServed.Opening ResourceBirthCodec.rootBytes) where
  | confirmed (confirmed : LightConfirmed config opening)
  /-- A STOP's completion: its running incarnation is checked from the walk (`receiveVerified`). -/
  | stop
  | rejected (detail : String)
  | contention
  | unavailable (detail : String)
  | uncertain (detail : String)

def receiveServed (config : Config) (transport : DurableReceiverIO.Transport)
    (light : NativeHostLight.Light config) (bytes : List UInt8)
    (adopt : NativeHostLight.Adopt light.opening := fun _ _ _ => pure ()) :
    IO (LightResult config light.opening) := do
  let some ingress := ApplicationLifecycleCompletionV2Ingress.codec.decode bytes
    | return .rejected "noncanonical checked lifecycle completion ingress"
  if notStop : ingress.source.originalBegin.base.source.kind = .stop then return .stop
  else
  let grounded ← match ← light.groundedVia transport
      (ApplicationLifecycleCompletionV2Admission.keys config ingress) with
    | .error detail => return .unavailable detail
    | .ok grounded => pure grounded
  let reader := light.opening.reader transport ResourceBirthCodec.rootBytes
  let conditional ← match ← ApplicationLifecycleCompletionV2Admission.prepareConditional config reader
      grounded ingress with
    | .error detail => return .rejected detail
    | .ok conditional => pure conditional
  let intent := ApplicationLifecycleCompletionV2Core.intent conditional
  match fresh : grounded.ground.recorded intent.transactionId with
  | none => return .rejected "checked lifecycle completion transaction identity undeclared"
  | some (some _) => return .rejected "checked lifecycle completion transaction identity already used"
  | some none =>
      match ← DurableServed.receiveServed transport ResourceBirthCodec.rootBytes light.opening intent with
      | .appended kind next height entry entryExact _ moved =>
          adopt next _ moved
          return .confirmed ⟨ingress, grounded, conditional, notStop, fresh, kind, next, height, entry,
            entryExact⟩
      | .replayed _ => return .rejected "checked lifecycle completion transaction identity already used"
      | .rejected _ => return .rejected "durable checked lifecycle completion refused"
      | .contention => return .contention
      | .unavailable detail => return .unavailable detail
      | .uncertain detail => return .uncertain detail

end Minidregg.Kernel.ApplicationLifecycleCompletionV2Receiver
