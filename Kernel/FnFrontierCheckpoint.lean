/- A projection of native replay at an authenticated Store head. A genesis verification
mints the initial cut. Typed native receives advance it before their compare-and-swap. The reader binds the body to its own
deployment, gateway pin and physical head before decoding the audit. -/
module

public import Kernel.NativeProviderHistory
public import Kernel.NativeHost

@[expose] public section

namespace Minidregg.Kernel.FnFrontierCheckpoint

open Minidregg.Theory Minidregg.Theory.TypedAuthorization
open Minidregg.Compiler Minidregg.Compiler.NativeHostCodec
open Minidregg.Compiler.Tower256ConcreteBackend
open FnConsumerFrontierCore FnConsumerFrontierReplay NativeHost

set_option autoImplicit false

private def modeStream : StreamCodec Mode :=
  StreamCodec.xmap (StreamCodec.option StreamCodec.bool)
    (fun | .virgin => none | .legacyAnchor => some false | .orderedV2 => some true)
    (fun | none => .virgin | some false => .legacyAnchor | some true => .orderedV2)
    (by intro m; cases m <;> rfl)
    (by intro w; cases w with | none => rfl | some b => cases b <;> rfl)

private def cursorStream : StreamCodec Cursor :=
  StreamCodec.xmap (StreamCodec.product StreamCodec.nat
    (StreamCodec.product (StreamCodec.option receiptStream) modeStream))
    (fun c => (c.position, c.receipt, c.mode)) (fun (n, r, m) => ⟨n, r, m⟩)
    (by intro c; cases c; rfl)

private def legacyStream : StreamCodec FnConsumerNamespaceAdmissionAt.Legacy :=
  StreamCodec.xmap (StreamCodec.product DurableReceiverCodec.intentStream receiptStream)
    (fun l => (l.record, l.receipt)) (fun (r, receipt) => ⟨r, receipt⟩)
    (by intro l; cases l; rfl)

private def originalStream : StreamCodec FnConsumerNamespaceHistory.Original :=
  StreamCodec.xmap ((StreamCodec.product FnConsumerNamespaceRegistration.ingressStream
    receiptStream).refine (fun (ingress, receipt) =>
      FnConsumerNamespaceRegistration.transactionId ingress.spec = receipt.transactionId ∧
      (FnConsumerNamespaceRegistration.event ingress).eventId = receipt.eventId))
    (fun o => ⟨(o.ingress, o.receipt), o.transactionExact, o.eventExact⟩)
    (fun w => ⟨w.val.1, w.val.2, w.property.1, w.property.2⟩)
    (by intro o; cases o; rfl) (by intro w; rfl)

def auditStream : StreamCodec Audit :=
  StreamCodec.xmap (StreamCodec.product (StreamCodec.list (StreamCodec.product keyStream cursorStream))
    (StreamCodec.product (StreamCodec.list keyStream)
      (StreamCodec.product (StreamCodec.list (StreamCodec.product keyStream legacyStream))
        (StreamCodec.product (StreamCodec.list originalStream) StreamCodec.bool))))
    (fun a => (a.ordered, a.ambiguous, a.legacyRecords, a.registrations, a.fault))
    (fun (ordered, ambiguous, legacy, registrations, fault) =>
      ⟨ordered, ambiguous, legacy, registrations, fault⟩)
    (by intro a; cases a; rfl)

/-- Includes the retained event13 originals for a selected frontier plan. This
keeps projection and receipt on the same head across a concurrent append. -/
structure Snapshot where
  audit : Audit
  special : List (DurableReceiver.IntentRecord × Receipt)
  provider : NativeProviderHistory.Index := {}

private def snapshotStream : StreamCodec Snapshot :=
  let records := StreamCodec.list (StreamCodec.product DurableReceiverCodec.intentStream receiptStream)
  StreamCodec.xmap (StreamCodec.product auditStream (StreamCodec.product records NativeProviderHistory.indexStream))
    (fun s => (s.audit, s.special, s.provider)) (fun (a, r, p) => ⟨a, r, p⟩) (by intro s; cases s; rfl)

private def specialVersion (record : DurableReceiver.IntentRecord) :=
  [13, 17, 19, 20].contains record.event.codecVersion

def ofVerified {config : Config} {target : Durable} (v : NativeHostReplay.Verified config target) :
    Snapshot :=
  let entries := target.image.accepted.zip v.receipts
  ⟨v.frontier, (entries.filter (fun entry => specialVersion entry.1)).reverse,
    entries.foldl (fun index (record, receipt) => index.append record receipt) {}⟩

private def Snapshot.append (config : Config) (s : Snapshot)
    (record : DurableReceiver.IntentRecord) (receipt : Receipt) : Except String Snapshot := do
  let audit ← NativeHostReplay.foldFrontier config s.audit [(record, receipt)]
  let special := if specialVersion record then (record, receipt) :: s.special else s.special
  return ⟨audit, special, s.provider.append record receipt⟩

private def binding (config : Config) (height : Nat) (chain root : Digest) : ByteArray :=
  let gate := config.fnGateway.map fun p => bytesStream.encode p.application ++
    (StreamCodec.list StreamCodec.nat).encode [p.subject.value, p.target, p.capability.value, p.policyAddress.value]
  (bytesStream.encode config.anchorIdentity.toUTF8.toList ++
    (StreamCodec.option bytesStream).encode gate ++
    (StreamCodec.option GenericSimplexCodec.contextStream).encode config.jointConsensus ++
    (StreamCodec.list StreamCodec.nat).encode
      [DurableCheckpointCodec.foldSemantics.value, height, chain.value, root.value]).toByteArray

private def tag (key : DurableCheckpointCodec.MacKey) (context body : ByteArray) : ByteArray :=
  let digest := Sp800185Cshake256.Native.cshake256Kernel "DREGG/FN/FRONTIER-BODY/v1".toUTF8 body
  Sp800185Cshake256.kmac256Kernel key.bytes.toByteArray "DREGG/FN/ADMITTED-FRONTIER/v1".toUTF8
    (context ++ digest)

/-- The packed checkpoint authenticates the same message as the original disk format. -/
private theorem tag_eq (key : DurableCheckpointCodec.MacKey) (context body : ByteArray) :
    (tag key context body).toList =
      Sp800185Cshake256.kmac256Bytes key.bytes "DREGG/FN/ADMITTED-FRONTIER/v1".toUTF8.toList
        (context.toList ++ (Sp800185Cshake256.hash "DREGG/FN/FRONTIER-BODY/v1".toUTF8.toList
          body.toList).bytes) := by
  simp only [tag, ByteArray.toList_eq_data_toList, Sp800185Cshake256.kmac256Kernel,
    Sp800185Cshake256.Native.cshake256Kernel, Sp800185Cshake256.Native.bytesOfList_toList,
    List.toList_data_toByteArray, ByteArray.data_append, Array.toList_append,
    Sp800185Cshake256.kmac256Fast_eq, Sp800185Cshake256.Fast.cshake256Fast_eq, Sp800185Cshake256.hash]

#assert_axioms tag_eq

private def sealBody (key : DurableCheckpointCodec.MacKey) (context : ByteArray)
    (snapshot : Snapshot) : ByteArray :=
  let body := snapshotStream.encodeBytes snapshot
  (StreamCodec.product bytesStream bytesStream).encodeBytes ((tag key context body).toList, body.toList)

private def openBody (key : DurableCheckpointCodec.MacKey) (context bytes : ByteArray) :
    Option Snapshot := do
  let (mac, body) ← (StreamCodec.product bytesStream bytesStream).decodeBytes bytes
  let packed := body.toByteArray
  if (tag key context packed).toList = mac then snapshotStream.decodeBytes packed else none

private theorem decode_written {α : Type} (codec : StreamCodec α) (value : α) :
    codec.decodeBytes (codec.encodeBytes value) = some value := by
  rw [StreamCodec.decodeBytes_eq, ByteArray.toList_eq_data_toList, StreamCodec.encodeBytes_data]
  exact codec.toLawful.decode_encode value

private theorem open_seal (key : DurableCheckpointCodec.MacKey) (context : ByteArray)
    (snapshot : Snapshot) : openBody key context (sealBody key context snapshot) = some snapshot := by
  let body := snapshotStream.encodeBytes snapshot
  have packed : body.toList.toByteArray = body := DurableIndex.byteArray_eq_of_toList (by
    rw [List.toList_data_toByteArray, ByteArray.toList_eq_data_toList])
  unfold openBody sealBody
  rw [decode_written]
  change (if (tag key context body.toList.toByteArray).toList = (tag key context body).toList then
    snapshotStream.decodeBytes body.toList.toByteArray else none) = _
  rw [packed, if_pos rfl]
  exact decode_written _ _

/-- Mint only from replay, using the MAC key of that replay's physical Store. -/
def sealVerified {config : Config} {target : Durable} (v : NativeHostReplay.Verified config target) :
    ByteArray :=
  sealBody v.store.key (binding config target.height target.chain target.worldRoot) (ofVerified v)

def restore (config : Config) (key : DurableCheckpointCodec.MacKey)
    (height : Nat) (chain root : Digest) (bytes : ByteArray) : Option Snapshot :=
  openBody key (binding config height chain root) bytes

theorem restore_verified {config : Config} {target : Durable} (v : NativeHostReplay.Verified config target) :
    restore config v.store.key target.height target.chain target.worldRoot (sealVerified v) = some (ofVerified v) :=
  open_seal _ _ _

/-- Every admitted tail sees exactly the frontier the original walk supplied,
including its ambiguity set, retained legacy evidence and global fault. -/
theorem restored_tail_eq {config : Config} {target : Durable} (v : NativeHostReplay.Verified config target)
    (tail : List (DurableReceiver.IntentRecord × Receipt)) :
    (restore config v.store.key target.height target.chain target.worldRoot (sealVerified v)).map
      (fun s => NativeHostReplay.foldFrontier config s.audit tail) =
      some (NativeHostReplay.foldFrontier config v.frontier tail) := by
  rw [restore_verified]; rfl

/-- info: 'Minidregg.Kernel.FnFrontierCheckpoint.restored_tail_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms restored_tail_eq

/-- The state written by the native append callback, including its error case,
agrees with replay from genesis split at the migrated cut. -/
theorem append_replays (config : Config) (initial : Audit) (prior : List (DurableReceiver.IntentRecord × Receipt))
    (s : Snapshot) (record : DurableReceiver.IntentRecord) (receipt : Receipt)
    (verified : NativeHostReplay.foldFrontier config initial prior = .ok s.audit) :
    (s.append config record receipt).map (·.audit) =
      NativeHostReplay.foldFrontier config initial (prior ++ [(record, receipt)]) := by
  rw [NativeHostReplay.checkpoint_tail_frontier_eq config initial s.audit prior _ verified]
  unfold Snapshot.append
  cases NativeHostReplay.foldFrontier config s.audit [(record, receipt)] <;> rfl

/-- info: 'Minidregg.Kernel.FnFrontierCheckpoint.append_replays' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms append_replays

/-- A registered gateway's subsequent legacy write leaves the registration and cursor
bytes unchanged but poisons resolution. The refusal survives serialization. -/
theorem restored_ambiguous_cursor_refused (key : DurableCheckpointCodec.MacKey) (context : ByteArray)
    (audit : Audit) (record : DurableReceiver.IntentRecord) (transition : Transition)
    (clean : transition.key ∉ audit.ambiguous)
    (registered : audit.registrations.any (fun prior => prior.ingress.spec.key == transition.key) = true) :
    (openBody key context (sealBody key context ⟨audit.adoptLegacy record transition, [], {}⟩)).map
      (fun s => s.audit.cursor transition.key) = some (.error "fn consumer frontier is ambiguous") := by
  rw [open_seal]
  exact congrArg some (registered_legacy_poisons_resolution audit record transition clean registered).2.2

/-- info: 'Minidregg.Kernel.FnFrontierCheckpoint.restored_ambiguous_cursor_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms restored_ambiguous_cursor_refused

/-- The poison theorem applies to the first legacy write after any fresh registration. -/
theorem poison_premises (original : FnConsumerNamespaceHistory.Original) :
    let audit : Audit := { registrations := [original] }
    original.ingress.spec.key ∉ audit.ambiguous ∧
      audit.registrations.any (fun prior => prior.ingress.spec.key == original.ingress.spec.key) = true := by
  simp [List.any_cons]

private def path (config : Config) (height : Nat) (chain root : Digest) :=
  config.storage.root / s!"admitted-frontier-{height}-{chain.value}-{root.value}.bin"

/-- Publish the cut atomically. Competing heads have distinct destinations. -/
private def writeCut (config : Config) (height : Nat) (chain root : Digest) (bytes : ByteArray) : IO Unit := do
  let nonce := (← IO.getRandomBytes 16).toList.map (fun b => toString b.toNat)
  let tmp := config.storage.root / (".fn-frontier-" ++ String.intercalate "-" nonce)
  let handle ← IO.FS.Handle.mk tmp .writeNew
  try
    IO.setAccessRights tmp { user := { read := true, write := true } }
    handle.write bytes
    handle.flush
    IO.FS.rename tmp (path config height chain root)
  finally
    if ← tmp.pathExists then IO.FS.removeFile tmp

/-- The snapshot was authenticated at this exact opening. -/
structure At (config : Config) {store : DurableHistory.StoreIdentity} (head : DurableHistory.Head store) where
  private mk ::
  snapshot : Snapshot

def loadAt (config : Config) {store : DurableHistory.StoreIdentity}
    (head : DurableHistory.Head store) : IO (Option (At config head)) := do
  let file := path config head.height head.chain head.root
  unless ← file.pathExists do return none
  try
    return (restore config store.key head.height head.chain head.root (← IO.FS.readBinFile file)).map At.mk
  catch e =>
    if !(← file.pathExists) then return none else throw e

def atVerified {config : Config} {target : Durable} (v : NativeHostReplay.Verified config target)
    {store : DurableHistory.StoreIdentity} (head : DurableHistory.Head store) : Except String (At config head) :=
  if target.height == head.height && target.chain == head.chain && target.worldRoot == head.root &&
      v.store.key.id == store.key.id then .ok ⟨ofVerified v⟩
  else .error "admitted checkpoint head moved during verification"

inductive Poll where
  | registration (ingress : FnConsumerNamespaceRegistration.Ingress)
  | selected (ingress : FnSelectedPollCoverage.Ingress)
  | empty (ingress : FnEmptyPollProgressV2.Ingress)

private def Poll.tx : Poll → Digest
  | .registration i => FnConsumerNamespaceRegistration.transactionId i.spec
  | .selected i => FnSelectedPollCoverage.transactionId i.spec
  | .empty i => FnEmptyPollProgressV2.transactionId i.spec

private def Poll.proposal : Poll → FnConsumerFrontierGateway.Proposal
  | .registration i => FnConsumerNamespaceAdmissionAt.proposal i
  | .selected i => FnConsumerFrontierProposal.selected i
  | .empty i => FnConsumerFrontierProposal.empty i

private def Poll.replays (snapshot : Snapshot) (record : DurableReceiver.IntentRecord) (receipt : Receipt) :
    Poll → Bool
  | .registration i =>
      match snapshot.audit.registrationFor i.spec.key receipt with
      | .ok original => original.ingress == i && record.event == FnConsumerNamespaceRegistration.event i
      | .error _ => false
  | .selected i => record.event == FnSelectedPollCoverage.event i &&
      record.nullifiers.contains (FnSelectedPollCoverage.frontierNullifier i.spec)
  | .empty i => record.event == FnEmptyPollProgressV2.event i &&
      record.nullifiers.contains (FnEmptyPollProgressV2.frontierNullifier i.spec)

private def Snapshot.releaseFor (snapshot : Snapshot) (config : Config) (id : Digest) :
    Option FnSelectedPollReleaseShape.Original := do
  let (record, receipt) ← snapshot.special.find? (fun entry => entry.1.transactionId == id)
  let ingress ← FnSelectiveReleaseIngress.ingressCodec.decode record.event.canonicalBytes
  unless record.event.codecVersion == 13 && receipt.transactionId == id &&
      receipt.eventId == record.event.eventId && FnSelectiveReleaseIngress.transactionId ingress == id &&
      FnSelectiveReleaseIngress.event ingress == record.event &&
      record.nullifiers == [FnSelectiveReleaseReceiver.ordinaryNullifier config ingress,
        FnSelectiveReleaseIngress.releaseNullifier ingress.packet.release] do none
  return ⟨ingress, receipt⟩

private def Poll.prepare (config : Config) (ground : ServedBasis.Ground config.deployment)
    (snapshot : Snapshot) (poll : Poll) : IO (Except String
      (DurableDataIntent.DataIntent ResourceBirthCodec.rootBytes)) := do
  let audit := snapshot.audit
  match poll with
  | .registration i =>
      unless audit.registrationAbsent i.spec.consumerNamespace do return .error "fn consumer namespace admission refused"
      let .ok legacy := audit.legacyFor i.spec | return .error "fn consumer namespace admission refused"
      let .ok accepted ← FnConsumerNamespaceAdmissionAt.prepareConditionalGround config ground legacy i
        | return .error "fn consumer namespace admission refused"
      return .ok (accepted.intent config ground legacy i)
  | .selected i =>
      let .ok cursor := audit.cursor i.spec.evidence.key | return .error "selected fn poll admission refused"
      let some release := snapshot.releaseFor config i.spec.evidence.releaseKey
        | return .error "selected fn poll admission refused"
      let .ok original := audit.registrationFor i.spec.evidence.key i.spec.registrationReceipt
        | return .error "selected fn poll admission refused"
      let .ok accepted ← FnSelectedPollAdmissionAt.admitAtGround config ground cursor release original i
        | return .error "selected fn poll admission refused"
      return .ok (accepted.intent config ground cursor release original i)
  | .empty i =>
      let .ok cursor := audit.cursor i.spec.evidence.key | return .error "empty fn poll admission refused"
      let .ok original := audit.registrationFor i.spec.evidence.key i.spec.registrationReceipt
        | return .error "empty fn poll admission refused"
      let .ok accepted ← FnEmptyPollAdmissionAtV2.admitAtGround config ground cursor original i
        | return .error "empty fn poll admission refused"
      return .ok (accepted.intent config ground cursor original i)

/-- This wrapper is private to the typed native receive paths below. Publish a candidate
before the physical CAS. Only the matching authenticated Store head can open it, including
after a lost reply or process restart. A competing candidate has a distinct filename. -/
private def receivingTransport (config : Config) (transport : DurableReceiverIO.Transport)
    (previous : Nat) (chain root : Digest) : DurableReceiverIO.Transport :=
  { transport with append := fun height entry nodes => do
      let file := path config previous chain root
      if height != previous + 1 || !(← file.pathExists) then return ← transport.append height entry nodes
      let candidate : IO Bool := do
        let key ← IO.ofExcept (← transport.key)
        let some snapshot := restore config key previous chain root (← IO.FS.readBinFile file)
          | return false
        let some record := DurableHistory.decodeRecordBytes entry.record | return false
        let some carried := DurableHistory.trailerCarried entry.tag | return false
        unless DurableCheckpointCodec.chainStep chain record == carried.chain &&
            DurableHistory.trailer key height carried == entry.tag do return false
        let receipt : Receipt := ⟨record.transactionId, record.event.eventId, height, carried.root⟩
        let advanced ← IO.ofExcept (snapshot.append config record receipt)
        writeCut config height carried.chain carried.root
          (sealBody key (binding config height carried.chain carried.root) advanced)
        return true
      let issued ← try candidate catch e =>
        IO.eprintln s!"native admission checkpoint: {e}"
        pure false
      let result ← transport.append height entry nodes
      if issued && result == .installed then
        try IO.FS.removeFile file catch _ => pure ()
      return result }

/-- Each entry to the checkpoint writer runs the same native admission and source gates
as the ordinary receiver. Its transport is fixed here, never accepted from a requester. -/
def submitOrdinary (config : Config) (light : NativeHostLight.Light config) (call : SignedCall)
    (confirm : Confirm) (adopt : NativeHostLight.Adopt light.opening) :=
  let head := light.opening.head
  NativeHost.submitDisclosedSession config light call confirm adopt
    (receivingTransport config config.transport head.height head.chain head.root)

private def fromOpened (config : Config) (opened : Opened config) (transport : DurableReceiverIO.Transport) :=
  receivingTransport config transport opened.durable.height opened.durable.chain opened.durable.worldRoot

def submitClock (config : Config) (confirm : Confirm) (opened : Opened config) (bytes : List UInt8) :=
  NativeHost.clockSubmitLoaded config confirm opened bytes (fromOpened config opened config.transport)

def submitCertify (config : Config) (confirm : Confirm) (opened : Opened config) (bytes : List UInt8) :=
  NativeHost.certifySubmitLoaded config confirm opened bytes (fromOpened config opened config.transport)

def submitActivity (config : Config) (confirm : Confirm) (opened : Opened config)
    (held : ObjectiveActivity.LoadMemo) (bytes : List UInt8) :=
  NativeHost.activitySubmitLoaded config confirm opened held bytes (fromOpened config opened config.kernelTransport)

def submitSeat (config : Config) (confirm : Confirm) (opened : Opened config) (bytes : List UInt8) :=
  NativeHost.seatSubmitLoaded config confirm opened bytes (fromOpened config opened config.kernelTransport)

def submitRelease (config : Config) (opened : Opened config) (bytes : List UInt8) :=
  FnSelectiveReleaseReceiver.receiveLoaded config opened bytes (fromOpened config opened config.transport)

/-- A historical retry selects its exact migrated original. A fresh command must check
the current gateway signature, authority and event-specific predecessor before CAS.
Only its byte-exact readback may extend the certified frontier. -/
def receive (config : Config) (light : NativeHostLight.Light config) (cut : At config light.opening.head)
    (poll : Poll) (phase : String) (adopt : NativeHostLight.Adopt light.opening) : IO Outcome := do
  let head := light.opening.head
  let tx := poll.tx
  let snapshot := cut.snapshot
  let conflict := Outcome.refused .conflict "replay".toUTF8.toList "transaction identity conflict".toUTF8.toList
  match ← DurableHistoryStore.indexAnswer config.transport head (DurableIndex.transactionKey tx) with
  | .error e => return .unavailable e.toUTF8.toList
  | .ok ⟨some value, _⟩ =>
      let some (record, receipt) := snapshot.special.find? (fun entry => entry.1.transactionId == tx)
        | return conflict
      if DurableIndex.heightOf value == some receipt.acceptedCount && receipt.transactionId == tx &&
          receipt.eventId == record.event.eventId && poll.replays snapshot record receipt then
        return .confirmed .replayed receipt
      return conflict
  | .ok ⟨none, _⟩ =>
      let marker := FnConsumerFrontierGateway.marker poll.proposal
      let basis ← match ← light.basis ⟨[], [CredentialAuthorityReplay.nullifier config.deployment.domain marker]⟩ with
        | .ok b => pure b
        | .error e => return .unavailable e.toUTF8.toList
      let intent ← match ← poll.prepare config (ServedBasis.Ground.ofBasis basis) snapshot with
        | .ok i => pure i
        | .error e => return .refused .operationRejected phase.toUTF8.toList e.toUTF8.toList
      match ← DurableServed.receiveServed
          (receivingTransport config config.transport head.height head.chain head.root) ResourceBirthCodec.rootBytes light.opening intent with
      | .appended kind next _ _ _ _ moved =>
          adopt next _ moved
          let record := DurableReceiver.IntentRecord.ofIntent intent
          let receipt : Receipt := ⟨record.transactionId, record.event.eventId, next.head.height, next.head.root⟩
          if let .error detail := light.adoptStep next _ moved then
            return .uncertain detail.toUTF8.toList
          return .confirmed kind receipt
      | .replayed _ => return .uncertain "fn consumer receipt differs from checked head".toUTF8.toList
      | .rejected _ => return .refused .operationRejected phase.toUTF8.toList (phase ++ " durable refusal").toUTF8.toList
      | .contention => return .contention
      | .unavailable e => return .unavailable e.toUTF8.toList
      | .uncertain e => return .uncertain e.toUTF8.toList

/-- Migrating an old store verifies its complete native admissions, then binds the cut
to the exact head the caller opened. A concurrent move cannot mix the two views. -/
def migrateAt (config : Config) {store : DurableHistory.StoreIdentity} (head : DurableHistory.Head store) :
    IO (At config head) := do
  let opened ← IO.ofExcept (← NativeHost.openExisting config)
  let ⟨_, reader⟩ ← IO.ofExcept
    (← DurableHistoryStore.readerOf config.transport ResourceBirthCodec.rootBytes opened.durable)
  let v ← IO.ofExcept ((← NativeHostReplay.verifyLoaded config reader opened.durable).mapError (·.detail))
  let cut ← IO.ofExcept (atVerified v head)
  writeCut config head.height head.chain head.root (sealVerified v)
  return cut

def migrate (config : Config) : IO Nat := do
  let light ← IO.ofExcept (← NativeHostLight.start config)
  discard <| migrateAt config light.opening.head
  return light.opening.head.height

end Minidregg.Kernel.FnFrontierCheckpoint
