/-
Exact-CAS receiving for launch-bound lifecycle BEGIN. Event23 records a durable
pending operation, not physical execution. Continue admission is gated by the
Verified original completed-create certificate in NativeHostReplay.

The light route (`receiveServed`, KN2 2b): the BEGIN admits on the light opening's basis for
its declared keys, a continue reads its completed create from the Store's history at the
opening's head (re-admitted at its own prefix, `NativeHostReplay.selectCreated`), and the
commit is `DurableServed.receiveServed`. No full image, no walk. STOP still selects its
running incarnation from the walk (`receiveVerified`).
-/
module

public import Kernel.NativeHostReplay
public import Kernel.NativeHostLight

@[expose] public section

namespace Minidregg.Kernel.ApplicationLifecycleBeginV3Receiver

open Minidregg.Compiler
open Minidregg.Compiler.ResourceBirthCodec
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Kernel.NativeHost

set_option autoImplicit false

structure Confirmed (config : Config) where
  private mk ::
  target : Durable
  old : NativeHostReplay.Verified config target
  ingress : ApplicationLifecycleBeginV3Ingress.Ingress
  readback : NativeHostReplay.ExactReadback config old
  eventExact : readback.derived.intent.event =
    ApplicationLifecycleBeginV3Ingress.event ingress
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
  let candidate := NativeHostReplay.exactCandidate confirmed.old
    confirmed.readback.derived confirmed.readback.ready confirmed.readback.tag
  ⟨confirmed.readback.derived.intent.transactionId,
    confirmed.readback.derived.intent.event.eventId,
    confirmed.old.opened.durable.height + 1,
    candidate.worldRoot⟩

theorem Confirmed.postRecord_exact {config : Config} (confirmed : Confirmed config) :
    confirmed.readback.appended.entry.record =
      DurableCheckpointCodec.recordFrame.encode
        (DurableReceiver.IntentRecord.ofIntent confirmed.readback.derived.intent) :=
  NativeHostReplay.extendExact_physicalRecord confirmed.old confirmed.readback

/-- The confirmed successor is admitted under `config`: the read-back intent
carries this ingress's event, and `validateLoaded config` accepts the one
candidate extending the verified tip by that read-back intent. -/
theorem Confirmed.successor_validated {config : Config} (confirmed : Confirmed config) :
    confirmed.readback.derived.intent.event =
        ApplicationLifecycleBeginV3Ingress.event confirmed.ingress ∧
      NativeHost.validateLoaded config
          (NativeHostReplay.exactCandidate confirmed.old
            confirmed.readback.derived confirmed.readback.ready confirmed.readback.tag) =
        .ok confirmed.readback.after :=
  ⟨confirmed.eventExact, confirmed.readback.validated⟩

inductive Result (config : Config) where
  | confirmed (confirmed : Confirmed config)
  | rejected (detail : String)
  | contention
  | unavailable (detail : String)
  | uncertain (detail : String)

def receiveVerified (config : Config) {target : Durable}
    (old : NativeHostReplay.Verified config target)
    (bytes : List UInt8) : IO (Result config) := do
  let some ingress := ApplicationLifecycleBeginV3Ingress.codec.decode bytes
    | return .rejected "noncanonical launch-bound lifecycle BEGIN"
  let .ok derived ← NativeHostReplay.admitBeginV3Verified old ingress
    | return .rejected "current launch-bound lifecycle BEGIN refused"
  if eventExact : derived.intent.event = ApplicationLifecycleBeginV3Ingress.event ingress then
    if old.opened.durable.firstIndex derived.intent.transactionId != none then
      return .rejected "launch-bound BEGIN transaction identity already used"
    let result ← DurableReceiverIO.receiveLoadedDetailed config.transport
      ResourceBirthCodec.rootBytes old.opened.durable derived.intent
    match result with
    | .exact kind appended =>
        match NativeHostReplay.ExactReadback.ofAppended old derived appended with
        | .error detail => return .uncertain s!"v3 lifecycle BEGIN post-image: {detail}"
        | .ok ⟨proof, proofDerived⟩ =>
              match ← DurableHistoryStore.readerOf config.transport ResourceBirthCodec.rootBytes appended.next with
              | .error detail => return .uncertain s!"post-append history reader: {detail}"
              | .ok ⟨_, reader⟩ =>
                return .confirmed ⟨target, old, ingress, proof, (by rw [proofDerived]; exact eventExact), kind, _, reader⟩
    | .ordinary ordinary =>
        match ordinary with
        | .confirmed _ _ =>
            return .uncertain "v3 lifecycle BEGIN lacks exact post-CAS readback"
        | .rejected _ => return .rejected "durable v3 lifecycle BEGIN refused"
        | .contention => return .contention
        | .unavailable detail => return .unavailable detail
        | .uncertain detail => return .uncertain detail
  else return .rejected "source-admitted v3 BEGIN event differs from ingress"

/-! ## The light route -/

/-- The chronology a light BEGIN's signed choice needs, read at the opening's head. A STOP
is not here: it selects its running incarnation from the walk (`receiveVerified`). -/
inductive LightHistory (config : Config) {store : DurableHistory.StoreIdentity}
    (head : DurableHistory.Head store) (ingress : ApplicationLifecycleBeginV3Ingress.Ingress) : Type where
  | install (selected : ingress.start = none) (notStop : ingress.base.source.kind ≠ .stop)
  | create (binding : ApplicationLifecycleLaunchBinding.Binding) (index : Nat)
      (selected : ingress.start = some binding) (choice : binding.choice = .create index)
  | continue (binding : ApplicationLifecycleLaunchBinding.Binding)
      (selected : ingress.start = some binding) (choice : binding.choice = .continue)
      (created : NativeHostReplay.CreatedSelected config head binding)

/-- A BEGIN confirmed on the light route: admitted on the light ground of the opening it
was received on, its chronology read at that opening's head, and the record appended
being exactly its intent's. -/
structure LightConfirmed (config : Config) (opening : DurableServed.Opening ResourceBirthCodec.rootBytes) where
  private mk ::
  ingress : ApplicationLifecycleBeginV3Ingress.Ingress
  basis : ServedBasis.Basis config.deployment opening.store
  accepted : ApplicationLifecycleBeginV3Admission.Accepted config.deployment config.profile
    ⟨config.federation, config.genesisHeight + basis.height⟩ (.ofBasis basis) ingress
  history : LightHistory config opening.head ingress
  fresh : (ServedBasis.Ground.ofBasis basis).recorded accepted.intent.transactionId = some none
  eventExact : accepted.intent.event = ApplicationLifecycleBeginV3Ingress.event ingress
  kind : DurableReceiverIO.Confirmation
  next : DurableServed.Opening ResourceBirthCodec.rootBytes
  height : next.head.height = opening.head.height + 1
  entry : DurableReceiverIO.Entry
  entryExact : entry.record =
    DurableCheckpointCodec.recordFrame.encode (DurableReceiver.IntentRecord.ofIntent accepted.intent)

/-- **What a light confirmation proves**: the appended record is the admitted intent's,
written as the opening's next record; the intent carries this ingress's event; its
transaction id was verified unrecorded on the basis it was admitted on; and a continue's
completed create is the one its binding names, re-admitted at that create's own prefix. -/
theorem LightConfirmed.exact {config : Config} {opening : DurableServed.Opening ResourceBirthCodec.rootBytes}
    (confirmed : LightConfirmed config opening) :
    confirmed.entry.record = DurableCheckpointCodec.recordFrame.encode
        (DurableReceiver.IntentRecord.ofIntent confirmed.accepted.intent) ∧
      confirmed.next.head.height = opening.head.height + 1 ∧
      confirmed.accepted.intent.event = ApplicationLifecycleBeginV3Ingress.event confirmed.ingress ∧
      (ServedBasis.Ground.ofBasis confirmed.basis).recorded confirmed.accepted.intent.transactionId =
        some none :=
  ⟨confirmed.entryExact, confirmed.height, confirmed.eventExact, confirmed.fresh⟩

inductive LightResult (config : Config) (opening : DurableServed.Opening ResourceBirthCodec.rootBytes) where
  | confirmed (confirmed : LightConfirmed config opening)
  /-- A STOP: its running incarnation is selected from the walk (`receiveVerified`). -/
  | stop
  | rejected (detail : String)
  | contention
  | unavailable (detail : String)
  | uncertain (detail : String)

private def lightHistory (config : Config) (transport : DurableReceiverIO.Transport)
    (opening : DurableServed.Opening ResourceBirthCodec.rootBytes)
    (ingress : ApplicationLifecycleBeginV3Ingress.Ingress) :
    IO (Except String (Option (LightHistory config opening.head ingress))) := do
  match selected : ingress.start with
  | none =>
      if kind : ingress.base.source.kind = .stop then return .ok none
      else return .ok (some (.install selected kind))
  | some binding =>
      match choice : binding.choice with
      | .create index => return .ok (some (.create binding index selected choice))
      | .continue =>
          let reader := opening.reader transport ResourceBirthCodec.rootBytes
          match ← NativeHostReplay.selectCreated config reader opening.head.height binding with
          | .error detail => return .error detail
          | .ok created => return .ok (some (.continue binding selected choice created))

/-- **The light BEGIN** (install, START, upgrade, continue): its keys (transaction id,
operation marker, launch markers) read into a basis of `light`, its chronology read at the
opening's head, admitted on that basis's ground, committed by `receiveServed` and the
readback handed to `adopt`. -/
def receiveServed (config : Config) (transport : DurableReceiverIO.Transport)
    (light : NativeHostLight.Light config) (bytes : List UInt8)
    (adopt : NativeHostLight.Adopt := fun _ _ => pure ()) :
    IO (LightResult config light.opening) := do
  let some ingress := ApplicationLifecycleBeginV3Ingress.codec.decode bytes
    | return .rejected "noncanonical launch-bound lifecycle BEGIN"
  let history ← match ← lightHistory config transport light.opening ingress with
    | .error detail => return .rejected s!"current launch-bound lifecycle BEGIN refused: {detail}"
    | .ok none => return .stop
    | .ok (some history) => pure history
  let basis ← match ← light.basisVia transport (ApplicationLifecycleBeginV3Admission.keys ingress) with
    | .error detail => return .unavailable detail
    | .ok basis => pure basis
  let ambient : DeclaredResourceController.Ambient := ⟨config.federation, config.genesisHeight + basis.height⟩
  let accepted ← match ← ApplicationLifecycleBeginV3Admission.admitNative config.deployment
      config.profile ambient config.signature (.ofBasis basis) ingress with
    | .error detail => return .rejected s!"current launch-bound lifecycle BEGIN refused: {detail}"
    | .ok accepted => pure accepted
  if eventExact : accepted.intent.event = ApplicationLifecycleBeginV3Ingress.event ingress then
    match fresh : (ServedBasis.Ground.ofBasis basis).recorded accepted.intent.transactionId with
    | none => return .rejected "launch-bound BEGIN transaction identity undeclared"
    | some (some _) => return .rejected "launch-bound BEGIN transaction identity already used"
    | some none =>
        match ← DurableServed.receiveServed transport ResourceBirthCodec.rootBytes light.opening
            accepted.intent with
        | .appended kind next height entry entryExact _ =>
            adopt next none
            return .confirmed ⟨ingress, basis, accepted, history, fresh, eventExact, kind, next, height,
              entry, entryExact⟩
        | .replayed _ => return .rejected "launch-bound BEGIN transaction identity already used"
        | .rejected _ => return .rejected "durable v3 lifecycle BEGIN refused"
        | .contention => return .contention
        | .unavailable detail => return .unavailable detail
        | .uncertain detail => return .uncertain detail
  else return .rejected "source-admitted v3 BEGIN event differs from ingress"

end Minidregg.Kernel.ApplicationLifecycleBeginV3Receiver
