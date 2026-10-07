/-
# Kernel.Receiving -- the deployed receiving pipeline, one copy

`Theory.Receiving` defines the pipeline and proves its laws over an abstract
journal.  This module instantiates that journal with the deployed durable layer
(`DurableDataIntent.DataSnapshot` for the journal and the executor's install,
`DurableReceiverIO.Loaded` for the state, `receiveLoadedDetailed` for the
append) and the native Ed25519 verifier, and turns a receiving `Family` -- what
is specific to one operation -- into a `Theory.Receiving.Receiver`.

A family supplies: its identity (`id`, the registry's `FamilyId`), the ingress
codec, the command, the signature claims, the gate (`prepare`, handed the
Receiver's verdict on those claims as `CredentialSignatureAdmission.Received`:
the oracle and its vouchers), the per-cell
patch (`writes`, with its root binding), the law step it projects for each write
(`lawStep`), the cells it observed, its physical post law, its journal identity
(`txId`, `event`, `nullifiers`), the signing subject and its witness bytes.
This module supplies, once: the read guards (`readGuards`, written cells
removed, the laws' source cells added), the physical shape check, THE LAW
JUDGEMENT of every written cell (`lawFault`, `Kernel.ReceivingLaw`: a family
projects, the Receiver judges), the exact charge on every lane, the
`DataIntent` with both construction obligations discharged, the receipt,
`receiveLoaded`, `admitNative` (the audit walk's re-admission, the same
function the live path runs), and `lookupLoaded`.

The laws are read through a `ReceivingLaw.Laws` value; the deployed entry
points (`receiveLoaded`, `admitNative`) take the deployment's compiler profile
and install `Laws.physical` themselves (`receiveLoaded_laws`,
`admitNative_laws`), so a host cannot hand a family another law source.

Theorems: `lookup_install` (the store law the abstract replay theorem needs,
over the real `Snapshot.install`), `execute_accepted_install`,
`replay_after_execute` (the record the executor installs for an admission is
the record replay confirms), `shape_sound` (the shape check means what it
says about the loaded snapshot), `shape_lawful` (an admitted patch's every
written cell is lawful), `receive_committed_lawful` and
`kernelOnly_writers_sound` (the same, for a committed outcome).
-/
import Compiler.DurableReceiverIO
import Compiler.CredentialSignatureIO
import Compiler.CredentialSignatureAdmission
import Compiler.ResourceBirthCodec
import Theory.Receiving
import Kernel.ReceivingLaw

namespace Minidregg.Kernel.Receiving

open Minidregg.Compiler
open Minidregg.Kernel.DurableDataIntent
open Minidregg.Theory.ResourceCost (Charge Lane)
open Minidregg.Theory.TypedAuthorization (Digest SubjectId)
open Minidregg.Theory.Receiving (SigQuery Journal Recorded Refusal Receiver Vouchers)
open Minidregg.Compiler.CredentialSignatureAdmission (Received receiverVerify)
open Minidregg.Kernel.ReceivingLaw (Laws LawFault Lawful)
open Minidregg.Compiler.CanonicalCellRegistry (FamilyId Kind LawClass)
open Minidregg.Compiler.CanonicalPolicyAdmission (PolicyStepContext PolicyCompilerProfile)

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
  /-- The family's registry identity: the writer a `kernelOnly` row names. -/
  id : FamilyId
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
  /-- The gate: authority, freshness, validation of the per-cell patch.  It is
  handed the Receiver's verdict on `claims` (`Received`: the oracle and the
  vouchers of the claims it accepted) and may read a signature only from it
  (`Received.find?`, `Received.signed?`, `CheckedSignature.ofReceiverClaim`). -/
  prepare : Received → (env : Env) → (durable : Durable) → (command : Command) →
    Except Reject (Prepared env durable command)
  /-- The per-cell patch: one canonical post image per written cell. -/
  writes : {env : Env} → {durable : Durable} → {command : Command} →
    Prepared env durable command → List DataWrite
  writes_bound : ∀ {env : Env} {durable : Durable} {command : Command}
    (prepared : Prepared env durable command) (write : DataWrite),
    write ∈ writes prepared → rootBytes write.canonicalPostBytes = write.exactPost
  /-- The law step of one write: the old and new predicate states of the real
  pre and post stores, for the written cell's committed law.  `none` for a write
  to a kernel-only cell.  The family projects; the Receiver judges. -/
  lawStep : {env : Env} → {durable : Durable} → {command : Command} →
    (prepared : Prepared env durable command) → (write : DataWrite) →
    write ∈ writes prepared → Option PolicyStepContext
  /-- The cells the gate observed; `readGuards` removes the written ones. -/
  observed : {env : Env} → {durable : Durable} → {command : Command} →
    Prepared env durable command → List ReadGuard
  /-- Physical well-formedness of the post images (`CellLaw` and the like).
  Never a committed law: those are the Receiver's (`lawFault`). -/
  physicalPostLaw : {env : Env} → {durable : Durable} → {command : Command} →
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

variable {F} (laws : Laws Durable) {env : F.Env} {durable : Durable} {command : F.Command}

/-- **The law judgement**, every family: the first fault the written cells' laws
raise against the patch (`ReceivingLaw.lawFault` on the family's own writes and
steps, under its own identity), on the loaded state it prepared against. -/
def lawFault (prepared : F.Prepared env durable command) : Option LawFault :=
  ReceivingLaw.lawFault laws F.id durable (F.writes prepared) (F.lawStep prepared)

def lawful (prepared : F.Prepared env durable command) : Bool := (lawFault laws prepared).isNone

/-- The read guards: observed cells the patch does not write, and the source
cells of every law-bearing write's committed law (`ReceivingLaw.lawGuards`). -/
def readGuards (prepared : F.Prepared env durable command) : List ReadGuard :=
  Receiver.guardsOff DataWrite.cellId ReadGuard.cellId (F.writes prepared)
    (F.observed prepared ++ ReceivingLaw.lawGuards laws durable (F.writes prepared) (F.lawStep prepared))

/-- The physical shape every receiver checks before it emits an intent:
distinct written cells, each write's expected pre-root and each guard's root
current in the loaded snapshot, and the family's physical post law. -/
def shape (prepared : F.Prepared env durable command) : Bool :=
  decide ((F.writes prepared).map DataWrite.cellId).Nodup &&
    (F.writes prepared).all (fun write =>
      decide (write.expectedPre = durable.snapshot.model.roots write.cellId)) &&
    (readGuards laws prepared).all (fun guard =>
      decide (guard.expectedRoot = durable.snapshot.model.roots guard.cellId)) &&
    F.physicalPostLaw prepared

/-- **The shape check means what it says.** -/
theorem shape_sound {prepared : F.Prepared env durable command} (shaped : shape laws prepared = true) :
    ((F.writes prepared).map DataWrite.cellId).Nodup ∧
      (∀ write ∈ F.writes prepared, write.expectedPre = durable.snapshot.model.roots write.cellId) ∧
      (∀ guard ∈ readGuards laws prepared,
        guard.expectedRoot = durable.snapshot.model.roots guard.cellId) ∧
      F.physicalPostLaw prepared = true := by
  simpa [shape, List.all_eq_true, and_assoc] using shaped

/-- **Every written cell of an admitted patch is lawful.**  When the shape check
and the law judgement pass, every write is either to a `lawBearing` cell, not a
birth, whose committed law resolved on the family's step with both compiler
verdicts true and `Pred.eval` accepting the step; or to a `kernelOnly writers`
cell, with no step, by a family its row names. -/
theorem shape_lawful {prepared : F.Prepared env durable command}
    (shaped : shape laws prepared = true) (judged : lawful laws prepared = true) :
    F.physicalPostLaw prepared = true ∧
      ∀ write (member : write ∈ F.writes prepared),
        Lawful laws F.id durable write (F.lawStep prepared write member) := by
  refine ⟨(shape_sound laws shaped).2.2.2, ?_⟩
  have none_ : lawFault laws prepared = none := by
    simpa [lawful, Option.isNone_iff_eq_none] using judged
  exact (ReceivingLaw.lawFault_none_iff laws F.id durable _ _).1 none_

variable (F)

/-- The exact charge, one definition for every family. -/
def charge (laws : Laws Durable) (env : F.Env) (durable : Durable) (ingress : F.Ingress)
    (prepared : F.Prepared env durable (F.command ingress)) : Charge
  | .incidences => 1
  | .turnBytes => (F.bytes ingress).length
  | .memoryTouches => (F.writes prepared).length + (readGuards laws prepared).length
  | .storageBytes => ((F.writes prepared).map fun write => write.canonicalPostBytes.length).sum
  | .witnessBytes => F.witnessBytes ingress
  | .proofWork =>
      match F.claims env durable ingress with
      | .ok claims => claims.length
      | .error _ => 0
  | .feeDebit | .networkBytes | .sideEffectCount | .leaseByteBlocks => 0

def payload (laws : Laws Durable) {env : F.Env} {durable : Durable} (ingress : F.Ingress)
    (prepared : F.Prepared env durable (F.command ingress)) : Payload where
  writes := F.writes prepared
  readGuards := readGuards laws prepared
  exactCharge := F.charge laws env durable ingress prepared
  subject := F.subject ingress
  postRootsBound := F.writes_bound prepared
  guardsReadOnly := fun _ member => Receiver.guardsOff_readonly member

/-- The family as a `Theory.Receiving.Receiver` over the deployed journal,
judged by `laws`, its claims verified by `oracle` (`receiverVerify`). -/
def receiver (laws : Laws Durable) {m : Type → Type} (oracle : CredentialSignatureIO.Oracle m) :
    Receiver journal (receiverVerify oracle) where
  Env := F.Env
  Ingress := F.Ingress
  Command := F.Command
  Reject := F.Reject
  Prepared := F.Prepared
  decode := F.decode
  command := F.command
  claims := F.claims
  prepare := fun vouchers => F.prepare ⟨oracle, vouchers⟩
  shape := fun prepared => shape laws prepared
  Fault := LawFault
  lawFault := fun prepared => lawFault laws prepared
  txId := F.txId
  event := F.event
  nullifiers := F.nullifiers
  payload := fun ingress prepared => F.payload laws ingress prepared

/-- `F.receiver.Reject` is `F.Reject` by definition, but instance search does not unfold
`receiver`: a refusal of the receiver prints with the family's own `Repr`. -/
instance receiverRejectRepr (laws : Laws Durable) {m : Type → Type}
    (oracle : CredentialSignatureIO.Oracle m) : Repr (F.receiver laws oracle).Reject := F.rejectRepr

instance receiverFaultRepr (laws : Laws Durable) {m : Type → Type}
    (oracle : CredentialSignatureIO.Oracle m) : Repr (F.receiver laws oracle).Fault :=
  inferInstanceAs (Repr LawFault)

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

/-- The live receiver of a family: its claims verified by the pinned native process. -/
abbrev liveReceiver (laws : Laws Durable) (native : CredentialSignatureIO.NativeConfig) :=
  F.receiver laws (CredentialSignatureIO.Oracle.live native)

abbrev Outcome (laws : Laws Durable) (native : CredentialSignatureIO.NativeConfig) (env : F.Env)
    (durable : Durable) :=
  (F.liveReceiver laws native).Outcome env durable Appended Settled

/-- **The receiver**, every family: `Theory.Receiving.Receiver.receive` in `IO`,
judged by the deployment's laws (`Laws.physical` of its compiler profile). -/
def receiveLoaded {Fld : Type} [Field Fld] [DecidableEq Fld]
    (profile : PolicyCompilerProfile Fld) (deployment : CanonicalCellRegistry.Deployment)
    (native : CredentialSignatureIO.NativeConfig)
    (transport : DurableReceiverIO.Transport) (env : F.Env) (durable : Durable)
    (bytes : List UInt8) : IO (F.Outcome (Laws.physical profile deployment) native env durable) :=
  (F.liveReceiver (Laws.physical profile deployment) native).receive
    (appendNative transport) env durable bytes

/-- **The live receiver judges by the deployed laws**: the host chooses the
profile and deployment, never the law source. -/
theorem receiveLoaded_laws {Fld : Type} [Field Fld] [DecidableEq Fld]
    (profile : PolicyCompilerProfile Fld) (deployment : CanonicalCellRegistry.Deployment)
    (native : CredentialSignatureIO.NativeConfig) (transport : DurableReceiverIO.Transport)
    (env : F.Env) (durable : Durable) (bytes : List UInt8) :
    F.receiveLoaded profile deployment native transport env durable bytes =
      (F.receiver (Laws.physical profile deployment) (.live native)).receive
        (appendNative transport) env durable bytes := rfl

/-- The audit walk's re-admission: the live admission path, exactly. -/
def admitNative {Fld : Type} [Field Fld] [DecidableEq Fld]
    (profile : PolicyCompilerProfile Fld) (deployment : CanonicalCellRegistry.Deployment)
    (native : CredentialSignatureIO.NativeConfig) (env : F.Env)
    (durable : Durable) (ingress : F.Ingress) :
    IO (Except (Refusal F.Reject LawFault)
      ((F.liveReceiver (Laws.physical profile deployment) native).Admitted env durable ingress)) :=
  (F.liveReceiver (Laws.physical profile deployment) native).admitVia env durable ingress

theorem admitNative_laws {Fld : Type} [Field Fld] [DecidableEq Fld]
    (profile : PolicyCompilerProfile Fld) (deployment : CanonicalCellRegistry.Deployment)
    (native : CredentialSignatureIO.NativeConfig) (env : F.Env) (durable : Durable)
    (ingress : F.Ingress) :
    F.admitNative profile deployment native env durable ingress =
      (F.receiver (Laws.physical profile deployment) (.live native)).admitVia env durable
        ingress := rfl

structure Receipt where
  transactionId : Digest
  eventId : Digest
  deriving DecidableEq, Repr

def receipt (env : F.Env) (ingress : F.Ingress) : Receipt :=
  ⟨F.txId env ingress, (F.event env ingress).eventId⟩

/-- The receiver replay is read through: replay consults no verifier (the
empty transcript; `replay_oracle_irrelevant`). -/
abbrev replayReceiver (laws : Laws Durable) :=
  F.receiver laws (CredentialSignatureIO.Oracle.recorded ⟨[]⟩)

/-- Replay is the same under every oracle: it reads only the journal and the
family's transaction identity. -/
theorem replay_oracle_irrelevant (laws : Laws Durable) {m : Type → Type}
    (oracle : CredentialSignatureIO.Oracle m) (env : F.Env) (durable : Durable) (ingress : F.Ingress) :
    (F.receiver laws oracle).replay env durable ingress =
      (F.replayReceiver laws).replay env durable ingress := rfl

/-- Receipt-only lookup: the journal, never fresh work. -/
def lookupLoaded (laws : Laws Durable) (env : F.Env) (durable : Durable) (ingress : F.Ingress) :
    Option (Except Unit Receipt) :=
  ((F.replayReceiver laws).replay env durable ingress).map fun selected =>
    selected.map fun _ => F.receipt env ingress

/-- **Replay after the executor commits.**  When the executor accepts an
admission's intent on the loaded snapshot, any later loaded state at that
snapshot looks the same ingress up as confirmed with the same receipt. -/
theorem replay_after_execute {laws : Laws Durable} {m : Type → Type}
    {oracle : CredentialSignatureIO.Oracle m} {env : F.Env} {durable : Durable}
    {ingress : F.Ingress}
    (accepted : (F.receiver laws oracle).Accepted env durable ingress) {next : DataSnapshot rootBytes}
    (executed : DurableDataIntent.execute .complete durable.snapshot
      ((F.receiver laws oracle).intent accepted) = .accepted next)
    (later : Durable) (atNext : later.snapshot = next) :
    F.lookupLoaded laws env later ingress = some (.ok (F.receipt env ingress)) := by
  have replayed := (F.receiver laws oracle).replay_after_install accepted later durable.snapshot
    (by rw [show journal.snap later = later.snapshot from rfl, atNext,
      execute_accepted_install executed])
  rw [F.replay_oracle_irrelevant laws oracle] at replayed
  simp [lookupLoaded, replayed, Except.map]

/-! ## A committed write was judged -/

/-- **A committed outcome's every written cell is lawful.**  Exactly
`receive_committed`'s premises, at `Id` (any oracle that runs there: a recorded
transcript): the admission a committed outcome carries wrote only cells whose
laws admit it -- a `lawBearing` cell (not a birth) under its own committed law
resolved on the loaded state, with both compiler verdicts and `Pred.eval` true on
the family's step; or a `kernelOnly` cell its row lets this family write.  Every
family on `Family`, any `prepare`. -/
theorem receive_committed_lawful {laws : Laws Durable}
    {oracle : CredentialSignatureIO.Oracle Id}
    {Exact : Durable → DataIntent rootBytes → Type} {Other : Type}
    {append : (state : Durable) → (intent : DataIntent rootBytes) →
      Id (Receiver.Commit (Exact state intent) Other)}
    {env : F.Env} {durable : Durable} {bytes : List UInt8} {ingress : F.Ingress}
    {admission : (F.receiver laws oracle).Admitted env durable ingress}
    {witness : Exact durable ((F.receiver laws oracle).intent admission.accepted)}
    (committed : (F.receiver laws oracle).receive append env durable bytes =
      pure (.committed ingress admission witness)) :
    ∀ write (member : write ∈ F.writes admission.accepted.prepared),
      Lawful laws F.id durable write (F.lawStep admission.accepted.prepared write member) := by
  obtain ⟨shaped, faultless⟩ := (F.receiver laws oracle).receive_committed_lawFault committed
  exact (shape_lawful laws shaped (by simpa [lawful, Option.isNone_iff_eq_none] using faultless)).2

/-- **A committed outcome passed the physical shape**: its written cells are
distinct, each write's pre-root and each guard's root were current, and the
family's physical post law held. -/
theorem receive_committed_shape {laws : Laws Durable}
    {oracle : CredentialSignatureIO.Oracle Id}
    {Exact : Durable → DataIntent rootBytes → Type} {Other : Type}
    {append : (state : Durable) → (intent : DataIntent rootBytes) →
      Id (Receiver.Commit (Exact state intent) Other)}
    {env : F.Env} {durable : Durable} {bytes : List UInt8} {ingress : F.Ingress}
    {admission : (F.receiver laws oracle).Admitted env durable ingress}
    {witness : Exact durable ((F.receiver laws oracle).intent admission.accepted)}
    (committed : (F.receiver laws oracle).receive append env durable bytes =
      pure (.committed ingress admission witness)) :
    ((F.writes admission.accepted.prepared).map DataWrite.cellId).Nodup ∧
      (∀ write ∈ F.writes admission.accepted.prepared,
        write.expectedPre = durable.snapshot.model.roots write.cellId) ∧
      F.physicalPostLaw admission.accepted.prepared = true := by
  obtain ⟨shaped, -⟩ := (F.receiver laws oracle).receive_committed_lawFault committed
  obtain ⟨nodup, current, -, physical⟩ := shape_sound laws shaped
  exact ⟨nodup, current, physical⟩

/-- **Only the named families write a kernel-only cell**: in a committed
outcome of family `F`, every written cell of a `kernelOnly writers` kind has
`F.id ∈ writers`.  The registry review cites this. -/
theorem kernelOnly_writers_sound {laws : Laws Durable}
    {oracle : CredentialSignatureIO.Oracle Id}
    {Exact : Durable → DataIntent rootBytes → Type} {Other : Type}
    {append : (state : Durable) → (intent : DataIntent rootBytes) →
      Id (Receiver.Commit (Exact state intent) Other)}
    {env : F.Env} {durable : Durable} {bytes : List UInt8} {ingress : F.Ingress}
    {admission : (F.receiver laws oracle).Admitted env durable ingress}
    {witness : Exact durable ((F.receiver laws oracle).intent admission.accepted)}
    (committed : (F.receiver laws oracle).receive append env durable bytes =
      pure (.committed ingress admission witness)) :
    ∀ write ∈ F.writes admission.accepted.prepared, ∀ (kind : Kind) (writers : List FamilyId),
      laws.kindOf durable write = some kind → kind.lawClass = .kernelOnly writers →
        F.id ∈ writers := by
  intro write member kind writers kindEq row
  obtain ⟨-, faultless⟩ := (F.receiver laws oracle).receive_committed_lawFault committed
  exact ReceivingLaw.kernelOnly_writers laws F.id durable faultless member kindEq row

/-- **`prepare` is handed only the Receiver's vouchers.**  Every admission of a
family (any oracle, any monad) was prepared by `F.prepare` given exactly the
admission's vouchers under the receiver's own oracle, and every claim the family
named is among them.  A family reads a signature only through that `Received`
value (`Vouchers` has a private constructor, and `admitVia` is its only
producer), so a gate holds a signature verdict only when the oracle gave it. -/
theorem admitted_prepared_received {laws : Laws Durable} {m : Type → Type}
    {oracle : CredentialSignatureIO.Oracle m} {env : F.Env} {durable : Durable}
    {ingress : F.Ingress} (admission : (F.receiver laws oracle).Admitted env durable ingress) :
    F.prepare ⟨oracle, admission.vouchers⟩ env durable (F.command ingress) =
        .ok admission.accepted.prepared ∧
      ∃ claims, F.claims env durable ingress = .ok claims ∧
        ∀ claim ∈ claims, claim ∈ admission.vouchers.verified :=
  admission.prepared

end Family

#assert_axioms lookup_install
#assert_axioms execute_accepted_install
#assert_axioms Family.shape_sound
#assert_axioms Family.shape_lawful
#assert_axioms Family.replay_after_execute
#assert_axioms Family.receiveLoaded_laws
#assert_axioms Family.admitNative_laws
#assert_axioms Family.receive_committed_lawful
#assert_axioms Family.kernelOnly_writers_sound
#assert_axioms Family.receive_committed_shape
#assert_axioms Family.admitted_prepared_received
#assert_axioms Family.replay_oracle_irrelevant

end Minidregg.Kernel.Receiving
