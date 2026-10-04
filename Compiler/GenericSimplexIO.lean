import Compiler.GenericSimplexCodec
import Theory.AssertAxioms
namespace Minidregg.Compiler.GenericSimplexIO
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Compiler.GenericSimplexCodec
open Minidregg.Kernel.GenericSimplex
set_option autoImplicit false
/-- Persisted inputs include source-validation grants, so replay never rechecks
them against a different present snapshot. This log is private trusted storage.
A source check can be appended only by the native controller, not peer ingress. -/
structure Journal where
  context : Context
  self : Nat
  initialTime : Nat
  events : List Event := []
  commitWitnesses : List CommitWitness := []
  deriving DecidableEq, BEq, Repr
def journalStream : StreamCodec Journal :=
  StreamCodec.xmap
    (StreamCodec.product contextStream (StreamCodec.product StreamCodec.nat
      (StreamCodec.product StreamCodec.nat
        (StreamCodec.product (StreamCodec.list eventStream) (StreamCodec.list commitWitnessStream)))))
    (fun j => (j.context,j.self,j.initialTime,j.events,j.commitWitnesses))
    (fun (c,s,t,e,w) => ⟨c,s,t,e,w⟩) (by intro j; cases j; rfl)
def replayEvents (c : Config) : State → List Event → Option State
  | s, [] => some s
  | s, e :: es => do
      let input ← decodeInput e
      let next := step c s input
      if next.failed then none else replayEvents c next es
def restore (expected : Context) (bytes : Bytes) : Option (Journal × State) := do
  let j ← journalStream.toLawful.decode bytes
  if journalStream.encode j != bytes || j.context != expected ||
      !expected.wellFormed || j.self ≥ expected.config.parties then none else
  let s ← replayEvents expected.config (start expected.config j.self j.initialTime) j.events
  if s.failed then none else some (j,s)
theorem replay_append (config : Config) (state : State) (events more : List Event) :
    replayEvents config state (events ++ more) =
      (replayEvents config state events).bind (fun next => replayEvents config next more) := by
  induction events generalizing state with
  | nil => rfl
  | cons event events ih =>
    simp only [List.cons_append,replayEvents]
    cases decoded : decodeInput event with
    | none => simp [decoded]
    | some input =>
      dsimp only [Bind.bind, Option.bind]
      split <;> simp_all <;> rfl

#assert_axioms replay_append

/-! ## Append-only physical journal

The durable image is `logMagic`, one length-prefixed canonical base `Journal`
frame, then length-prefixed `Delta` frames. Each acknowledged input is exactly
one appended delta. Nothing is rewritten: a legacy whole-image `agreement.bin`
is not this shape and does not decode (`convert-journal` re-encodes it
explicitly and checks the replayed state is identical). -/

/-- ASCII "MINI-SIMPLEX-LOG" and format version 1. -/
def logMagic : Bytes := [77,73,78,73,45,83,73,77,80,76,69,88,45,76,79,71,1]

/-- One acknowledged append: the exact inputs replayed through `step`, and the
transferable COMMIT witnesses verified in the same transaction. -/
structure Delta where
  events : List Event := []
  witnesses : List CommitWitness := []
  deriving DecidableEq, BEq, Repr

def deltaStream : StreamCodec Delta :=
  StreamCodec.xmap
    (StreamCodec.product (StreamCodec.list eventStream) (StreamCodec.list commitWitnessStream))
    (fun d => (d.events,d.witnesses)) (fun (e,w) => ⟨e,w⟩) (by intro d; cases d; rfl)

def deltaFrame (d : Delta) : Bytes := bytesStream.encode (deltaStream.encode d)

def encodeDeltas : List Delta → Bytes
  | [] => []
  | d :: ds => deltaFrame d ++ encodeDeltas ds

/-- `recent` is newest-first so an append is O(1) in memory. -/
structure Log where
  base : Journal
  recent : List Delta := []
  deriving DecidableEq, BEq, Repr

def Log.deltas (l : Log) : List Delta := l.recent.reverse

def Log.encode (l : Log) : Bytes :=
  logMagic ++ bytesStream.encode (journalStream.encode l.base) ++ encodeDeltas l.deltas

def Log.push (l : Log) (d : Delta) : Log := {l with recent := d :: l.recent}

/-- The journal whose whole replay defines the state of this log. -/
def Log.merged (l : Log) : Journal :=
  { l.base with
    events := l.base.events ++ l.deltas.flatMap Delta.events
    commitWitnesses := l.base.commitWitnesses ++ l.deltas.flatMap Delta.witnesses }

def decodeDeltas : Nat → Bytes → Option (List Delta)
  | 0, bytes => if bytes.isEmpty then some [] else none
  | fuel + 1, bytes =>
    if bytes.isEmpty then some [] else do
      let (payload,rest) ← bytesStream.decodePrefix bytes
      let d ← deltaStream.toLawful.decode payload
      let ds ← decodeDeltas fuel rest
      some (d :: ds)

def decodeLog (bytes : Bytes) : Option Log := do
  if bytes.take logMagic.length != logMagic then none
  let (payload,rest) ← bytesStream.decodePrefix (bytes.drop logMagic.length)
  let base ← journalStream.toLawful.decode payload
  let deltas ← decodeDeltas rest.length rest
  some ⟨base,deltas.reverse⟩

/-- Replay of a decoded log: the same guards and whole replay as `restore`,
over the merged journal. -/
def replayLog (expected : Context) (l : Log) : Option State :=
  let j := l.merged
  if (j.context != expected || !expected.wellFormed || decide (j.self ≥ expected.config.parties)) = true
  then none
  else do
    let s ← replayEvents expected.config (start expected.config j.self j.initialTime) j.events
    if s.failed then none else pure s

/-- Whole canonical replay of the physical log bytes. -/
def restoreLog (expected : Context) (bytes : Bytes) : Option (Log × State) := do
  let l ← decodeLog bytes
  if l.encode != bytes then none
  let s ← replayLog expected l
  some (l,s)

theorem bytesStream_encode_ne_nil (payload : Bytes) : bytesStream.encode payload ≠ [] := by
  simp [bytesStream, StreamCodec.nat, StreamCodec.encodeNat]

theorem encodeDeltas_append (ds : List Delta) (d : Delta) :
    encodeDeltas (ds ++ [d]) = encodeDeltas ds ++ deltaFrame d := by
  induction ds with
  | nil => simp [encodeDeltas]
  | cons x xs ih => simp [encodeDeltas, ih, List.append_assoc]

theorem length_le_encodeDeltas (ds : List Delta) : ds.length ≤ (encodeDeltas ds).length := by
  induction ds with
  | nil => simp [encodeDeltas]
  | cons d ds ih =>
    have nonempty : 0 < (deltaFrame d).length :=
      List.length_pos_of_ne_nil (bytesStream_encode_ne_nil _)
    simp only [encodeDeltas, List.length_append, List.length_cons]
    omega

theorem decodeDeltas_encode (ds : List Delta) :
    ∀ fuel, (encodeDeltas ds).length ≤ fuel → decodeDeltas fuel (encodeDeltas ds) = some ds := by
  induction ds with
  | nil => intro fuel _; cases fuel <;> simp [encodeDeltas, decodeDeltas]
  | cons d ds ih =>
    intro fuel bound
    have frame : (deltaFrame d) ≠ [] := bytesStream_encode_ne_nil _
    have frameLength : 0 < (deltaFrame d).length := List.length_pos_of_ne_nil frame
    have total : (encodeDeltas (d :: ds)).length = (deltaFrame d).length + (encodeDeltas ds).length := by
      simp [encodeDeltas]
    cases fuel with
    | zero => omega
    | succ fuel =>
      have rest := ih fuel (by omega)
      have payload := bytesStream.decodePrefix_encode (deltaStream.encode d) (encodeDeltas ds)
      have inner := deltaStream.toLawful.decode_encode d
      change deltaStream.toLawful.decode (deltaStream.encode d) = some d at inner
      have nonempty : (encodeDeltas (d :: ds)).isEmpty = false := by
        simp [encodeDeltas, deltaFrame, bytesStream_encode_ne_nil]
      simp only [decodeDeltas, nonempty, Bool.false_eq_true, ↓reduceIte]
      simp only [encodeDeltas, deltaFrame] at payload ⊢
      simp [payload, inner, rest]

theorem decodeLog_encode (l : Log) : decodeLog l.encode = some l := by
  have base := bytesStream.decodePrefix_encode (journalStream.encode l.base)
    (encodeDeltas l.recent.reverse)
  have inner : journalStream.toLawful.decode (journalStream.encode l.base) = some l.base :=
    journalStream.toLawful.decode_encode l.base
  have deltas : decodeDeltas (encodeDeltas l.recent.reverse).length
      (encodeDeltas l.recent.reverse) = some l.recent.reverse :=
    decodeDeltas_encode _ _ (Nat.le_refl _)
  unfold decodeLog Log.encode Log.deltas
  simp [List.append_assoc, List.take_left', List.drop_left', base, inner, deltas]

theorem Log.merged_push (l : Log) (d : Delta) :
    (l.push d).merged =
      { l.merged with
        events := l.merged.events ++ d.events
        commitWitnesses := l.merged.commitWitnesses ++ d.witnesses } := by
  simp [Log.merged, Log.push, Log.deltas, List.append_assoc]

theorem Log.encode_push (l : Log) (d : Delta) :
    (l.push d).encode = l.encode ++ deltaFrame d := by
  simp [Log.encode, Log.push, Log.deltas, encodeDeltas_append, List.append_assoc]

theorem restoreLog_encode (context : Context) (l : Log) :
    restoreLog context l.encode = (replayLog context l).map (fun s => (l,s)) := by
  unfold restoreLog
  rw [decodeLog_encode]
  cases h : replayLog context l <;> simp [h]

theorem replayLog_of_restoreLog {context : Context} {l : Log} {state : State}
    (h : restoreLog context l.encode = some (l,state)) : replayLog context l = some state := by
  rw [restoreLog_encode] at h
  cases r : replayLog context l with
  | none => simp [r] at h
  | some s => simp [r] at h; simp [h]

/-- The fast append is exactly the original whole-log replay of the extended
image: replay of the old log, then only the appended inputs. -/
theorem replayLog_push (context : Context) (l : Log) (state next : State) (d : Delta)
    (old : replayLog context l = some state)
    (continued : replayEvents context.config state d.events = some next)
    (notFailed : next.failed = false) :
    replayLog context (l.push d) = some next := by
  unfold replayLog at old ⊢
  rw [Log.merged_push]
  dsimp only
  by_cases guard : (l.merged.context != context || !context.wellFormed ||
      decide (l.merged.self ≥ context.config.parties)) = true
  · simp [guard] at old
  · simp only [guard, Bool.false_eq_true, ↓reduceIte] at old ⊢
    cases replayed : replayEvents context.config
        (start context.config l.merged.self l.merged.initialTime) l.merged.events with
    | none => simp [replayed] at old
    | some s =>
      rw [replayed] at old
      simp at old
      obtain ⟨_, rfl⟩ := old
      rw [replay_append, replayed]
      simp [continued, notFailed]

theorem restoreLog_push (context : Context) (l : Log) (state next : State) (d : Delta)
    (old : restoreLog context l.encode = some (l,state))
    (continued : replayEvents context.config state d.events = some next)
    (notFailed : next.failed = false) :
    restoreLog context (l.push d).encode = some (l.push d,next) := by
  rw [restoreLog_encode, replayLog_push context l state next d
    (replayLog_of_restoreLog old) continued notFailed]
  rfl

/-- In-process authoritative image of this replica's journal. `length` is the
exact physical byte length the single writer compares before appending. -/
structure Restored (context : Context) where
  log : Log
  state : State
  length : Nat
  witnesses : List CommitWitness
  exact : restoreLog context log.encode = some (log,state)
  sized : log.encode.length = length
  witnessed : witnesses = log.merged.commitWitnesses

def Restored.self {context : Context} (r : Restored context) : Nat := r.log.base.self

def openRestored (context : Context) (bytes : Bytes) : Option (Restored context) :=
  match h : restoreLog context bytes with
  | none => none
  | some (l,s) =>
    if same : l.encode = bytes then
      some ⟨l,s,bytes.length,l.merged.commitWitnesses,same ▸ h,by rw [same],rfl⟩
    else none

/-- Execute only the appended inputs; the result carries the whole-replay
equation for the extended physical image. Returns the exact frame to append. -/
def appendRestored {context : Context} (old : Restored context)
    (events : List Event) (witnesses : List CommitWitness) : Option (Restored context × Bytes) :=
  match continued : replayEvents context.config old.state events with
  | none => none
  | some next =>
    if notFailed : next.failed = false then
      let d : Delta := ⟨events,witnesses⟩
      some (⟨old.log.push d,next,old.length + (deltaFrame d).length,
        old.witnesses ++ witnesses,
        restoreLog_push context old.log old.state next d old.exact continued notFailed,
        by rw [Log.encode_push, List.length_append, old.sized],
        by rw [Log.merged_push, old.witnessed]⟩,deltaFrame d)
    else none

theorem appendRestored_exact {context : Context} (next : Restored context) :
    restoreLog context next.log.encode = some (next.log,next.state) := next.exact

#assert_axioms decodeLog_encode
#assert_axioms restoreLog_push
#assert_axioms appendRestored_exact

/-- A reader's classification of a physical image: the longest prefix of
complete frames, and whether the remainder is an unacknowledged torn frame.
A complete but undecodable frame is corruption and is never truncated. -/
def scanLog (bytes : Bytes) : Option Nat := Id.run do
  if bytes.take logMagic.length != logMagic then return none
  let afterMagic := bytes.drop logMagic.length
  let some (_,afterBase) := bytesStream.decodePrefix afterMagic | return none
  let mut rest := afterBase
  let mut valid := bytes.length - rest.length
  for _ in List.range (rest.length + 1) do
    if rest.isEmpty then return some valid
    match bytesStream.decodePrefix rest with
    | some (payload,next) =>
      if (deltaStream.toLawful.decode payload).isNone then return none
      rest := next
      valid := bytes.length - rest.length
    | none =>
      -- Torn: the length digits never terminate, or fewer bytes than declared.
      match StreamCodec.nat.decodePrefix rest with
      | none => return (if rest.contains 255 then none else some valid)
      | some (count,payload) => return (if payload.length < count then some valid else none)
  return none

structure Crypto where
  /-- Concrete ML-DSA-65 implementation, context MiniJointAgreementV1. -/
  verify : Bytes → Bytes → Bytes → IO Bool
  sign : Bytes → IO Bytes
def verifyAttestations (crypto : Crypto) (expected : Context) (bytes : Bytes)
    (signers : List Attestation) : IO Bool := do
  if !expected.wellFormed || signers.length < expected.config.quorum ||
      (signers.map Attestation.signer).eraseDups.length != signers.length then
    return false
  for a in signers do
    if a.signer ≥ expected.config.parties || a.signature.length != 3309 then return false
    let some pk := expected.publicKeys[a.signer]? | return false
    if !(← crypto.verify pk bytes a.signature) then return false
  return true
def verifyCertificate (crypto : Crypto) (expected : Context) (cert : Certificate) : IO Bool := do
  if cert.context != expected || cert.view == 0 || cert.block.isEmpty then return false
  verifyAttestations crypto expected (commitmentBytes expected cert.view cert.block) cert.signers

/-- A checked network commitment, never deserialized directly. Its constructor
is private to this module, whose sole public producer pins the expected Context
and verifies a quorum of real signatures. This is an IO verification boundary,
not a proof of ML-DSA unforgeability or the whole distributed algorithm. -/
structure VerifiedCommit (expected : Context) where
  private mk ::
  private certificate : Certificate
  private pinned : certificate.context = expected
  private quorum : expected.config.quorum ≤ certificate.signers.length
  private distinct : (certificate.signers.map Attestation.signer).Nodup
  private members : ∀ a ∈ certificate.signers, a.signer < expected.config.parties
def VerifiedCommit.context {expected : Context} (_v : VerifiedCommit expected) : Context := expected
def VerifiedCommit.view {expected : Context} (v : VerifiedCommit expected) : Nat := v.certificate.view
def VerifiedCommit.block {expected : Context} (v : VerifiedCommit expected) : Block := v.certificate.block
def VerifiedCommit.bytes {expected : Context} (v : VerifiedCommit expected) : Bytes := certificateStream.encode v.certificate
def VerifiedCommit.signerIds {expected : Context} (v : VerifiedCommit expected) : List Nat :=
  v.certificate.signers.map Attestation.signer
theorem VerifiedCommit.signers_distinct {expected : Context} (v : VerifiedCommit expected) :
    v.signerIds.Nodup := v.distinct
theorem VerifiedCommit.quorum_size {expected : Context} (v : VerifiedCommit expected) :
    expected.config.quorum ≤ v.signerIds.length := by
  simpa [VerifiedCommit.signerIds] using v.quorum
theorem VerifiedCommit.signers_members {expected : Context} (v : VerifiedCommit expected)
    (id : Nat) (member : id ∈ v.signerIds) : id < expected.config.parties := by
  obtain ⟨a,inside,same⟩ := List.mem_map.mp member
  rw [← same]
  exact v.members a inside
def verifyCommitted (crypto : Crypto) (expected : Context)
    (certificate : Certificate) : IO (Option (VerifiedCommit expected)) := do
  if pinned : certificate.context = expected then
    if quorum : expected.config.quorum ≤ certificate.signers.length then
      if distinct : (certificate.signers.map Attestation.signer).Nodup then
        if members : ∀ a ∈ certificate.signers, a.signer < expected.config.parties then
          if ← verifyCertificate crypto expected certificate then
            return some (VerifiedCommit.mk certificate pinned quorum distinct members)
          else return none
        else return none
      else return none
    else return none
  else return none
def verifyCommittedBytes (crypto : Crypto) (expected : Context)
    (bytes : Bytes) : IO (Option (VerifiedCommit expected)) := do
  let some certificate := certificateStream.toLawful.decode bytes | return none
  if certificateStream.encode certificate != bytes then return none
  verifyCommitted crypto expected certificate

def verifyCommitWitness (crypto : Crypto) (expected : Context)
    (witness : CommitWitness) : IO Bool := do
  if !expected.wellFormed || witness.view == 0 || witness.block.isEmpty ||
      witness.attestation.signer ≥ expected.config.parties ||
      witness.attestation.signature.length != 3309 then return false
  let some pk := expected.publicKeys[witness.attestation.signer]? | return false
  crypto.verify pk (commitmentBytes expected witness.view witness.block)
    witness.attestation.signature

inductive Result where
  | invalid | conflict | uncertain
  | durable (state : State)
  deriving Repr

inductive PersistResult where
  | conflict | uncertain | durable
  deriving DecidableEq, BEq, Repr

/-- The replica's journal as seen by its single writer process. `current` is
the authoritative in-memory image; `append` is the helper's length-checked,
fsynced append. A read-only storage has no writer and refuses appends. -/
structure Storage where
  current : IO (Option (Sigma Restored))
  install : Option (Sigma Restored) → IO Unit
  append : Nat → Bytes → IO PersistResult
  deriving Inhabited

def current (storage : Storage) (context : Context) : IO (Option (Restored context)) := do
  let some prior ← storage.current | return none
  if same : prior.1 = context then return some (same ▸ prior.2) else return none

def Storage.readOnly (snapshot : Sigma Restored) : Storage where
  current := return some snapshot
  install _ := throw (IO.userError "read-only agreement journal")
  append _ _ := return .conflict

/-- A new image is installed only after the exact frame was durably appended at
the expected length. Conflict or uncertainty drops the image: the owner must
reopen from disk; nothing proceeds on a guessed state. -/
def commitRestored {context : Context} (storage : Storage) (prior next : Restored context)
    (frame : Bytes) : IO Result := do
  match ← storage.append prior.length frame with
  | .conflict => storage.install none; return .conflict
  | .uncertain => storage.install none; return .uncertain
  | .durable =>
    storage.install (some ⟨context,next⟩)
    return .durable next.state

/-- A peer retransmission can be acknowledged without another protocol input
only when its exact message is already represented by canonical durable replay.
This is transport duplicate suppression, not an idempotence claim about step:
deliveryAt would also update logical time and run the pump. Explicit tick/poll
service remains responsible for clocks and enabled continuation work. -/
def receivedBefore {context : Context} (prior : Restored context) (message : Message) : Prop :=
  ∃ old ∈ (viewAt prior.state message.view).received, old = message

instance {context : Context} (prior : Restored context) (message : Message) :
    Decidable (receivedBefore prior message) := inferInstanceAs
      (Decidable (∃ old ∈ (viewAt prior.state message.view).received, old = message))

def witnessBefore {context : Context} (prior : Restored context) (witness : CommitWitness) : Prop :=
  (∃ old ∈ prior.witnesses, old.view = witness.view ∧
    old.block = witness.block ∧ old.attestation.signer = witness.attestation.signer) ∧
      receivedBefore prior witness.message

instance {context : Context} (prior : Restored context) (witness : CommitWitness) :
    Decidable (witnessBefore prior witness) := inferInstanceAs
      (Decidable ((∃ old ∈ prior.witnesses, old.view = witness.view ∧
    old.block = witness.block ∧ old.attestation.signer = witness.attestation.signer) ∧
      receivedBefore prior witness.message))

/-- Randomized valid signatures may differ for the same exact signed statement.
Retaining an existing verified signature for that same member/view/full block is
sufficient; the incoming signature is independently verified before this test. -/
theorem retained_witness_has_message {context : Context} (prior : Restored context)
    (witness : CommitWitness) (retained : witnessBefore prior witness) :
    (∃ old ∈ prior.witnesses, old.view = witness.view ∧
      old.block = witness.block ∧ old.attestation.signer = witness.attestation.signer) ∧
      witness.message ∈ (viewAt prior.state witness.view).received := by
  obtain ⟨stored,previous,messageInside,messageSame⟩ := retained
  subst previous
  exact ⟨stored,messageInside⟩

#assert_axioms retained_witness_has_message

/-- Authenticated ordinary peer delivery. A duplicate leaves the durable image
unchanged and writes nothing. COMMIT uses the witness path. -/
def receiveAuthenticated (storage : Storage) (context : Context)
    (time : Nat) (message : Message) : IO Result := do
  let some prior ← current storage context | return .invalid
  if receivedBefore prior message then return .durable prior.state
  let some (next,frame) := appendRestored prior [encodeInput (.deliveryAt time message)] []
    | return .invalid
  commitRestored storage prior next frame

/-- Append one exact input using the proved continuation of the prior replay. -/
def persist (storage : Storage) (context : Context) (input : Input) : IO Result := do
  let some prior ← current storage context | return .invalid
  let some (next,frame) := appendRestored prior [encodeInput input] [] | return .invalid
  commitRestored storage prior next frame

/-- Candidate dissemination persists only unvalidated offers. Every complete
source record remains subject to the native historical checker before checked.
Keeping every nonempty record allows restart/catchup to rediscover the work. -/
def retainCandidateOffers (storage : Storage) (context : Context) (block : Block) : IO Result := do
  let some prior ← current storage context | return .invalid
  let fresh := (applicationHistory block).filter (fun payload => !prior.state.offers.contains payload)
  if fresh.isEmpty then return .durable prior.state
  let some (next,frame) := appendRestored prior
      (fresh.map (fun payload => encodeInput (.offer payload))) [] | return .invalid
  commitRestored storage prior next frame

/-- Verification, protocol delivery and retained transferable evidence share one
journal append. A crash cannot preserve the counted COMMIT while dropping the
witness needed to recover its decision. Only this producer accepts peer proofs. -/
def receiveCommitWitness (storage : Storage) (crypto : Crypto) (context : Context)
    (time : Nat) (witness : CommitWitness) : IO Result := do
  if !(← verifyCommitWitness crypto context witness) then return .invalid
  let some prior ← current storage context | return .invalid
  if witnessBefore prior witness then return .durable prior.state
  let added := if prior.witnesses.any (fun w =>
      w.view == witness.view && w.block == witness.block &&
      w.attestation.signer == witness.attestation.signer) then [] else [witness]
  let some (next,frame) := appendRestored prior [encodeInput (.deliveryAt time witness.message)] added
    | return .invalid
  commitRestored storage prior next frame

/-- Sign only a durable actual COMMIT send, with its retained audit cause.
Requiring local doCommit here would destroy liveness: prepare totality does not
imply a quorum of local doCommit outputs. -/
def exportCommitment (storage : Storage) (crypto : Crypto) (context : Context)
    (view : Nat) (block : Block) : IO (Option Attestation) := do
  let some prior ← current storage context | return none
  if !exportable prior.state view block then return none
  let signature ← crypto.sign (commitmentBytes context view block)
  if signature.length != 3309 then return none
  return some ⟨prior.self,signature⟩
/-- Any replica may reconstruct a certificate from received COMMIT evidence,
including a replica which never locally doCommitted. Its own durable COMMIT send
can contribute without a loopback packet. The result is reverified, not cast. -/
def recoverCommitment (storage : Storage) (crypto : Crypto) (context : Context)
    (view : Nat) (block : Block) : IO (Option (VerifiedCommit context)) := do
  let some prior ← current storage context | return none
  let mut signers := (prior.witnesses.filter (fun w =>
    w.view == view && w.block == block)).map CommitWitness.attestation
  if !(signers.any (fun a => a.signer == prior.self)) then
    if let some own ← exportCommitment storage crypto context view block then
      signers := signers ++ [own]
  verifyCommitted crypto context ⟨context,view,block,signers⟩
/-- Import a transferable quorum using one durable append. Signatures are
checked before any contained COMMIT is counted; all proofs survive restart.
This does not produce Input.checked or source application authority. -/
def receiveCommitment (storage : Storage) (crypto : Crypto) (context : Context)
    (time : Nat) (certificateBytes : Bytes) : IO Result := do
  let some verified ← verifyCommittedBytes crypto context certificateBytes | return .invalid
  let certificate := verified.certificate
  let some prior ← current storage context | return .invalid
  let incoming := certificate.signers.map (fun a =>
    CommitWitness.mk certificate.view certificate.block a)
  if ∀ witness ∈ incoming, witnessBefore prior witness then
    return .durable prior.state
  let added := incoming.foldl (fun ws w =>
    if (prior.witnesses ++ ws).any (fun old => old.view == w.view && old.block == w.block &&
        old.attestation.signer == w.attestation.signer) then ws else ws ++ [w]) []
  let some (next,frame) := appendRestored prior
      (incoming.map (fun w => encodeInput (.deliveryAt time w.message))) added
    | return .invalid
  commitRestored storage prior next frame
end Minidregg.Compiler.GenericSimplexIO
