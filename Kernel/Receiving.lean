/-
# Kernel.Receiving -- the deployed receiving pipeline, one copy

`Theory.Receiving` defines the pipeline and proves its laws over an abstract
journal.  This module instantiates that journal with the deployed durable layer
(`DurableDataIntent.DataSnapshot` for the journal and the executor's install,
`DurableReceiverIO.Loaded` for the state, `receiveLoadedDetailed` for the
append) and the native Ed25519 verifier, and turns a receiving `Family` -- what
is specific to one operation -- into a `Theory.Receiving.Receiver`.

A family supplies: the ingress codec, the command, the signature claims, the
gate (`prepare`), the per-cell patch (`writes`, with its root binding), the
cells it observed, its post law, its journal identity (`txId`, `event`,
`nullifiers`), the signing subject and its witness bytes.  This module
supplies, once: the read guards (`readGuards`, written cells removed), the
physical shape check, the exact charge on every lane, the `DataIntent` with
both construction obligations discharged, the receipt, `receiveLoaded`,
`admitNative` (the audit walk's re-admission, the same function the live path
runs), and `lookupLoaded`.

Theorems: `lookup_install` (the store law the abstract replay theorem needs,
over the real `Snapshot.install`), `execute_accepted_install`,
`replay_after_execute` (the record the executor installs for an admission is
the record replay confirms), `shape_sound` (the shape check means what it
says about the loaded snapshot).
-/
import Compiler.DurableReceiverIO
import Compiler.CredentialSignatureIO
import Compiler.ResourceBirthCodec
import Theory.Receiving

namespace Minidregg.Kernel.Receiving

open Minidregg.Compiler
open Minidregg.Kernel.DurableDataIntent
open Minidregg.Theory.ResourceCost (Charge Lane)
open Minidregg.Theory.TypedAuthorization (Digest SubjectId)
open Minidregg.Theory.Receiving (SigQuery Journal Recorded Refusal Receiver)

set_option autoImplicit false

abbrev rootBytes : List UInt8 → Digest := ResourceBirthCodec.rootBytes
abbrev Durable := DurableReceiverIO.Loaded rootBytes

/-! ## The journal -/

/-- The durable payload of one admission, carrying the two obligations every
`DataIntent` carries; `Family.payload` discharges them once for every family. -/
structure Payload where
  writes : List DataWrite
  readGuards : List ReadGuard
  exactCharge : Charge
  subject : Option SubjectId
  postRootsBound : ∀ write, write ∈ writes → rootBytes write.canonicalPostBytes = write.exactPost
  guardsReadOnly : ∀ guard, guard ∈ readGuards → guard.cellId ∉ writes.map DataWrite.cellId

def intentOf (txId : Digest) (event : StableEvent) (nullifiers : List StableNullifier)
    (payload : Payload) : DataIntent rootBytes where
  transactionId := txId
  writes := payload.writes
  readGuards := payload.readGuards
  nullifiers := nullifiers
  exactCharge := payload.exactCharge
  event := event
  subject := payload.subject
  postRootsBound := payload.postRootsBound
  guardsReadOnly := payload.guardsReadOnly

/-- The journal record of a transaction id: its id, event and nullifiers. -/
def lookup (snapshot : DataSnapshot rootBytes) (txId : Digest) :
    Option (Recorded Digest StableEvent StableNullifier) :=
  (DurableCommitProtocol.Snapshot.lookupRecorded txId snapshot.model.journal).map
    fun recorded => ⟨recorded.transactionId, recorded.event.event, recorded.nullifiers⟩

/-- The store law, over the executor's own install. -/
theorem lookup_install (snapshot : DataSnapshot rootBytes) (txId : Digest)
    (event : StableEvent) (nullifiers : List StableNullifier) (payload : Payload) :
    lookup (DataSnapshot.install snapshot (intentOf txId event nullifiers payload)) txId =
      some ⟨txId, event, nullifiers⟩ := by
  simp [lookup, DataSnapshot.install, intentOf, DataIntent.erase,
    DurableCommitProtocol.Snapshot.install, DurableCommitProtocol.Snapshot.lookupRecorded]

@[reducible] def journal : Journal where
  State := Durable
  Snap := DataSnapshot rootBytes
  snap := fun durable => durable.snapshot
  TxId := Digest
  Event := StableEvent
  Nullifier := StableNullifier
  Payload := Payload
  Intent := DataIntent rootBytes
  txIdDecEq := inferInstance
  eventDecEq := inferInstance
  nullifierDecEq := inferInstance
  lookup := lookup
  intentOf := intentOf
  install := DataSnapshot.install
  lookup_install := lookup_install

/-- The executor's accepted snapshot is its install. -/
theorem execute_accepted_install {before next : DataSnapshot rootBytes}
    {intent : DataIntent rootBytes}
    (accepted : DurableDataIntent.execute .complete before intent = .accepted next) :
    next = DataSnapshot.install before intent := by
  unfold DurableDataIntent.execute at accepted
  split at accepted
  · split at accepted <;> cases accepted
  · split at accepted
    · cases accepted
    · cases accepted; rfl

/-! ## A receiving family -/

/-- What is specific to one receiving operation. -/
structure Family where
  Env : Type
  Ingress : Type
  Command : Type
  Reject : Type
  rejectRepr : Repr Reject
  Prepared : Env → Durable → Command → Type
  decode : List UInt8 → Option Ingress
  /-- The exact signed bytes: the turn bytes and the event payload. -/
  bytes : Ingress → List UInt8
  command : Ingress → Command
  /-- The signature claims, from the decoded ingress and a key lookup. -/
  claims : Env → Durable → Ingress → Except Reject (List SigQuery)
  /-- The gate: authority, freshness, validation of the per-cell patch. -/
  prepare : (env : Env) → (durable : Durable) → (command : Command) →
    Except Reject (Prepared env durable command)
  /-- The per-cell patch: one canonical post image per written cell. -/
  writes : {env : Env} → {durable : Durable} → {command : Command} →
    Prepared env durable command → List DataWrite
  writes_bound : ∀ {env : Env} {durable : Durable} {command : Command}
    (prepared : Prepared env durable command) (write : DataWrite),
    write ∈ writes prepared → rootBytes write.canonicalPostBytes = write.exactPost
  /-- The cells the gate observed; `readGuards` removes the written ones. -/
  observed : {env : Env} → {durable : Durable} → {command : Command} →
    Prepared env durable command → List ReadGuard
  /-- Family checks on the post images beyond the standard shape. -/
  postLaw : {env : Env} → {durable : Durable} → {command : Command} →
    Prepared env durable command → Bool
  txId : Env → Ingress → Digest
  event : Env → Ingress → StableEvent
  nullifiers : Env → Ingress → List StableNullifier
  subject : Ingress → Option SubjectId
  /-- Witness bytes the turn carries beyond its command. -/
  witnessBytes : Ingress → Nat

namespace Family

variable (F : Family)

instance : Repr F.Reject := F.rejectRepr

variable {F} {env : F.Env} {durable : Durable} {command : F.Command}

/-- The read guards: observed cells the patch does not write. -/
def readGuards (prepared : F.Prepared env durable command) : List ReadGuard :=
  Receiver.guardsOff DataWrite.cellId ReadGuard.cellId (F.writes prepared) (F.observed prepared)

/-- The physical shape every receiver checks before it emits an intent:
distinct written cells, each write's expected pre-root and each guard's root
current in the loaded snapshot, and the family's post law. -/
def shape (prepared : F.Prepared env durable command) : Bool :=
  decide ((F.writes prepared).map DataWrite.cellId).Nodup &&
    (F.writes prepared).all (fun write =>
      decide (write.expectedPre = durable.snapshot.model.roots write.cellId)) &&
    (readGuards prepared).all (fun guard =>
      decide (guard.expectedRoot = durable.snapshot.model.roots guard.cellId)) &&
    F.postLaw prepared

/-- **The shape check means what it says.** -/
theorem shape_sound {prepared : F.Prepared env durable command} (shaped : shape prepared = true) :
    ((F.writes prepared).map DataWrite.cellId).Nodup ∧
      (∀ write ∈ F.writes prepared, write.expectedPre = durable.snapshot.model.roots write.cellId) ∧
      (∀ guard ∈ readGuards prepared,
        guard.expectedRoot = durable.snapshot.model.roots guard.cellId) ∧
      F.postLaw prepared = true := by
  simpa [shape, List.all_eq_true, and_assoc] using shaped

variable (F)

/-- The exact charge, one definition for every family. -/
def charge (env : F.Env) (durable : Durable) (ingress : F.Ingress)
    (prepared : F.Prepared env durable (F.command ingress)) : Charge
  | .incidences => 1
  | .turnBytes => (F.bytes ingress).length
  | .memoryTouches => (F.writes prepared).length + (readGuards prepared).length
  | .storageBytes => ((F.writes prepared).map fun write => write.canonicalPostBytes.length).sum
  | .witnessBytes => F.witnessBytes ingress
  | .proofWork =>
      match F.claims env durable ingress with
      | .ok claims => claims.length
      | .error _ => 0
  | .feeDebit | .networkBytes | .sideEffectCount | .leaseByteBlocks => 0

def payload {env : F.Env} {durable : Durable} (ingress : F.Ingress)
    (prepared : F.Prepared env durable (F.command ingress)) : Payload where
  writes := F.writes prepared
  readGuards := readGuards prepared
  exactCharge := F.charge env durable ingress prepared
  subject := F.subject ingress
  postRootsBound := F.writes_bound prepared
  guardsReadOnly := fun _ member => Receiver.guardsOff_readonly member

/-- The family as a `Theory.Receiving.Receiver` over the deployed journal. -/
def receiver : Receiver journal where
  Env := F.Env
  Ingress := F.Ingress
  Command := F.Command
  Reject := F.Reject
  Prepared := F.Prepared
  decode := F.decode
  command := F.command
  claims := F.claims
  prepare := F.prepare
  shape := fun prepared => shape prepared
  txId := F.txId
  event := F.event
  nullifiers := F.nullifiers
  payload := fun ingress prepared => F.payload ingress prepared

/-- `F.receiver.Reject` is `F.Reject` by definition, but instance search does not unfold
`receiver`: a refusal of the receiver prints with the family's own `Repr`. -/
instance receiverRejectRepr : Repr F.receiver.Reject := F.rejectRepr

/-! ## Native verification and the durable append -/

/-- The append's exact evidence: only `receiveLoadedDetailed`'s read-back-equal
branch constructs `DurableReceiverIO.Appended`. -/
structure Appended (durable : Durable) (intent : DataIntent rootBytes) where
  kind : DurableReceiverIO.Confirmation
  appended : DurableReceiverIO.Appended rootBytes durable intent

/-- Every other settlement of one append attempt. -/
inductive Settled where
  | journaled (kind : DurableReceiverIO.Confirmation)
  | rejected (reason : DurableDataIntent.RejectReason)
  | contention
  | unavailable (detail : String)
  | uncertain (detail : String)

def appendNative (transport : DurableReceiverIO.Transport) (durable : Durable)
    (intent : DataIntent rootBytes) :
    IO (Receiver.Commit (Appended durable intent) Settled) := do
  match ← DurableReceiverIO.receiveLoadedDetailed transport rootBytes durable intent with
  | .exact kind appended => pure (.exact ⟨kind, appended⟩)
  | .ordinary (.confirmed kind _) => pure (.other (.journaled kind))
  | .ordinary (.rejected reason) => pure (.other (.rejected reason))
  | .ordinary .contention => pure (.other .contention)
  | .ordinary (.unavailable detail) => pure (.other (.unavailable detail))
  | .ordinary (.uncertain detail) => pure (.other (.uncertain detail))

def verifyNative (native : CredentialSignatureIO.NativeConfig) (claim : SigQuery) :
    IO (Except String Bool) := do
  match ← CredentialSignatureIO.verify native claim.publicKey claim.message claim.signature with
  | .error reason => pure (.error s!"{repr reason}")
  | .ok verdict => pure (.ok verdict)

abbrev Outcome (env : F.Env) (durable : Durable) :=
  F.receiver.Outcome env durable Appended Settled

/-- **The receiver**, every family: `Theory.Receiving.Receiver.receive` in `IO`. -/
def receiveLoaded (native : CredentialSignatureIO.NativeConfig)
    (transport : DurableReceiverIO.Transport) (env : F.Env) (durable : Durable)
    (bytes : List UInt8) : IO (F.Outcome env durable) :=
  F.receiver.receive (verifyNative native) (appendNative transport) env durable bytes

/-- The audit walk's re-admission: the live admission path, exactly. -/
def admitNative (native : CredentialSignatureIO.NativeConfig) (env : F.Env)
    (durable : Durable) (ingress : F.Ingress) :
    IO (Except (Refusal F.Reject) (F.receiver.Admitted env durable ingress)) :=
  F.receiver.admitVia (verifyNative native) env durable ingress

structure Receipt where
  transactionId : Digest
  eventId : Digest
  deriving DecidableEq, Repr

def receipt (env : F.Env) (ingress : F.Ingress) : Receipt :=
  ⟨F.txId env ingress, (F.event env ingress).eventId⟩

/-- Receipt-only lookup: the journal, never fresh work. -/
def lookupLoaded (env : F.Env) (durable : Durable) (ingress : F.Ingress) :
    Option (Except Unit Receipt) :=
  (F.receiver.replay env durable ingress).map fun selected =>
    selected.map fun _ => F.receipt env ingress

/-- **Replay after the executor commits.**  When the executor accepts an
admission's intent on the loaded snapshot, any later loaded state at that
snapshot looks the same ingress up as confirmed with the same receipt. -/
theorem replay_after_execute {env : F.Env} {durable : Durable} {ingress : F.Ingress}
    (accepted : F.receiver.Accepted env durable ingress) {next : DataSnapshot rootBytes}
    (executed : DurableDataIntent.execute .complete durable.snapshot
      (F.receiver.intent accepted) = .accepted next)
    (later : Durable) (atNext : later.snapshot = next) :
    F.lookupLoaded env later ingress = some (.ok (F.receipt env ingress)) := by
  have replayed := F.receiver.replay_after_install accepted later durable.snapshot
    (by rw [show journal.snap later = later.snapshot from rfl, atNext,
      execute_accepted_install executed])
  simp [lookupLoaded, replayed, Except.map]

end Family

#assert_axioms lookup_install
#assert_axioms execute_accepted_install
#assert_axioms Family.shape_sound
#assert_axioms Family.replay_after_execute

end Minidregg.Kernel.Receiving
