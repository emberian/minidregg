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
/-- A memoized restoration is indexed by the complete configured context and
carries the exact pure replay equation. This is not a source authority token. -/
structure Restored (context : Context) where
  bytes : Bytes
  journal : Journal
  state : State
  exact : restore context bytes = some (journal,state)

abbrev RestoreCache := IO.Ref (Option (Sigma Restored))

def coldRestore (context : Context) (bytes : Bytes) : Option (Restored context) :=
  match h : restore context bytes with
  | none => none
  | some (journal,state) => some ⟨bytes,journal,state,h⟩

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

/-- The guard and replay facts extracted from the actual canonical decoder. -/
theorem restore_facts (context : Context) (bytes : Bytes) (journal : Journal) (state : State)
    (h : restore context bytes = some (journal,state)) :
    (journal.context != context || !context.wellFormed ||
      decide (journal.self ≥ context.config.parties)) = false ∧
    replayEvents context.config (start context.config journal.self journal.initialTime)
      journal.events = some state ∧ state.failed = false := by
  unfold restore at h
  cases decoded : journalStream.toLawful.decode bytes with
  | none => simp [decoded] at h
  | some parsed =>
    simp only [decoded] at h
    dsimp only [Bind.bind, Option.bind] at h
    split at h
    · contradiction
    · rename_i guardFalse
      cases replayed : replayEvents context.config
          (start context.config parsed.self parsed.initialTime) parsed.events with
      | none => simp [replayed] at h
      | some next =>
        simp only [replayed] at h
        split at h
        · contradiction
        · rename_i notFailed
          cases h
          simp_all

theorem restore_encoded (context : Context) (journal : Journal) (state : State)
    (guard : (journal.context != context || !context.wellFormed ||
      decide (journal.self ≥ context.config.parties)) = false)
    (replayed : replayEvents context.config
      (start context.config journal.self journal.initialTime) journal.events = some state)
    (notFailed : state.failed = false) :
    restore context (journalStream.encode journal) = some (journal,state) := by
  have decoded := journalStream.toLawful.decode_encode journal
  change journalStream.toLawful.decode (journalStream.encode journal) = some journal at decoded
  simp_all [restore]

/-- Arbitrary retained evidence may be added, but only the exact supplied events
advance state. No history is skipped or replaced, and failed continuations stay
refused. This theorem connects the fast append to the original full replay. -/
theorem append_restores (context : Context) (old : Restored context)
    (events : List Event) (witnesses : List CommitWitness) (nextState : State)
    (continued : replayEvents context.config old.state events = some nextState)
    (notFailed : nextState.failed = false) :
    let nextJournal := {old.journal with
      events := old.journal.events ++ events, commitWitnesses := witnesses}
    restore context (journalStream.encode nextJournal) = some (nextJournal,nextState) := by
  have facts := restore_facts context old.bytes old.journal old.state old.exact
  apply restore_encoded
  · exact facts.1
  · rw [replay_append,facts.2.1]
    exact continued
  · exact notFailed

#assert_axioms restore_facts
#assert_axioms restore_encoded
#assert_axioms append_restores
/-- Execute only the appended events. The proof identifies the result with
whole-journal replay of the exact new canonical image; no checkpoint is trusted. -/
def appendRestored {context : Context} (old : Restored context)
    (events : List Event) (witnesses : List CommitWitness) : Option (Restored context) :=
  match continued : replayEvents context.config old.state events with
  | none => none
  | some nextState =>
    if notFailed : nextState.failed = false then
      let nextJournal := {old.journal with
        events := old.journal.events ++ events,commitWitnesses := witnesses}
      some ⟨journalStream.encode nextJournal,nextJournal,nextState,
        append_restores context old events witnesses nextState continued notFailed⟩
    else none

theorem appendRestored_exact {context : Context} (next : Restored context) :
    restore context next.bytes = some (next.journal,next.state) := next.exact
#assert_axioms appendRestored_exact

/-- Outbox is the exact full replayed message sequence. Physical sender may resend
any item; the recipient deduplicates by sender/view/kind/value. No "sent" bit can
erase an obligation before durable recipient acknowledgement. -/
def allOutbox (s : State) : List Bytes := s.outbox.map messageStream.encode
inductive PersistResult where
  | conflict | uncertain | durable
  deriving DecidableEq, BEq, Repr
structure Storage where
  read : IO Bytes
  compareAppend : Bytes → Bytes → IO PersistResult
  restoreCache : Option RestoreCache := none

/-- Memo hits compare the entire durable image, never a digest or present source
height. The cache stores only results of the original canonical replay. -/
def restoreCached (storage : Storage) (context : Context) (bytes : Bytes) :
    IO (Option (Restored context)) := do
  if let some cache := storage.restoreCache then
    if let some prior ← cache.get then
      if same : prior.1 = context then
        let snapshot : Restored context := same ▸ prior.2
        if identical : snapshot.bytes = bytes then
          return some ⟨bytes,snapshot.journal,snapshot.state,identical ▸ snapshot.exact⟩
    let restored := coldRestore context bytes
    cache.set (restored.map fun snapshot => ⟨context,snapshot⟩)
    return restored
  return coldRestore context bytes

def restoredPair (storage : Storage) (context : Context) (bytes : Bytes) :
    IO (Option (Journal × State)) := do
  return (← restoreCached storage context bytes).map (fun s => (s.journal,s.state))

def invalidateRestore (storage : Storage) : IO Unit := do
  if let some cache := storage.restoreCache then cache.set none

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
/-- A new replay capability is remembered only after the unchanged exact image
CAS and exact durable readback. Conflict or uncertain completion clears the hint. -/
def commitRestored {context : Context} (storage : Storage) (expected : Bytes)
    (next : Restored context) : IO Result := do
  match ← storage.compareAppend expected next.bytes with
  | .conflict => invalidateRestore storage; return .conflict
  | .uncertain => invalidateRestore storage; return .uncertain
  | .durable =>
    if (← storage.read) != next.bytes then
      invalidateRestore storage
      return .uncertain
    if let some cache := storage.restoreCache then cache.set (some ⟨context,next⟩)
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
  (∃ old ∈ prior.journal.commitWitnesses, old.view = witness.view ∧
    old.block = witness.block ∧ old.attestation.signer = witness.attestation.signer) ∧
      receivedBefore prior witness.message

instance {context : Context} (prior : Restored context) (witness : CommitWitness) :
    Decidable (witnessBefore prior witness) := inferInstanceAs
      (Decidable ((∃ old ∈ prior.journal.commitWitnesses, old.view = witness.view ∧
    old.block = witness.block ∧ old.attestation.signer = witness.attestation.signer) ∧
      receivedBefore prior witness.message))

/-- Readback still detects an external writer or uncertain current image. A
successful duplicate acknowledgement neither writes bytes nor manufactures a
new source receipt, protocol action, clock advance or transferable witness. -/
def acknowledgeRetained {context : Context} (storage : Storage)
    (prior : Restored context) : IO Result := do
  if (← storage.read) != prior.bytes then
    invalidateRestore storage
    return .conflict
  return .durable prior.state

/-- Randomized valid signatures may differ for the same exact signed statement.
Retaining an existing verified signature for that same member/view/full block is
sufficient; the incoming signature is independently verified before this test. -/
theorem retained_witness_has_message {context : Context} (prior : Restored context)
    (witness : CommitWitness) (retained : witnessBefore prior witness) :
    (∃ old ∈ prior.journal.commitWitnesses, old.view = witness.view ∧
      old.block = witness.block ∧ old.attestation.signer = witness.attestation.signer) ∧
      witness.message ∈ (viewAt prior.state witness.view).received := by
  obtain ⟨stored,previous,messageInside,messageSame⟩ := retained
  subst previous
  exact ⟨stored,messageInside⟩

#assert_axioms retained_witness_has_message

/-- Authenticated ordinary peer delivery. Novel input retains the original
physical append path. Duplicates leave replay state unchanged; they are not
allowed to replace clock/continuation service. COMMIT uses the witness path. -/
def receiveAuthenticated (storage : Storage) (context : Context) (expected : Bytes)
    (time : Nat) (message : Message) : IO Result := do
  let some prior ← restoreCached storage context expected | return .invalid
  if receivedBefore prior message then return ← acknowledgeRetained storage prior
  let some next := appendRestored prior [encodeInput (.deliveryAt time message)]
      prior.journal.commitWitnesses | return .invalid
  commitRestored storage expected next

/-- Append one exact input using the proved continuation of the prior replay. -/
def persist (storage : Storage) (context : Context) (expected : Bytes)
    (input : Input) : IO Result := do
  let some prior ← restoreCached storage context expected | return .invalid
  let some next := appendRestored prior [encodeInput input] prior.journal.commitWitnesses
    | return .invalid
  commitRestored storage expected next
/-- Candidate dissemination persists only unvalidated offers. Every complete
source record remains subject to the native historical checker before checked.
Keeping every nonempty record allows restart/catchup to rediscover the work. -/
def retainCandidateOffers (storage : Storage) (context : Context) (expected : Bytes)
    (block : Block) : IO Result := do
  let some prior ← restoreCached storage context expected | return .invalid
  let fresh := (applicationHistory block).filter (fun payload => !prior.state.offers.contains payload)
  if fresh.isEmpty then return ← acknowledgeRetained storage prior
  let some next := appendRestored prior (fresh.map (fun payload => encodeInput (.offer payload)))
      prior.journal.commitWitnesses | return .invalid
  commitRestored storage expected next

/-- Verification, protocol delivery and retained transferable evidence share one
journal CAS. A crash cannot preserve the counted COMMIT while dropping the
witness needed to recover its decision. Only this producer accepts peer proofs. -/
def receiveCommitWitness (storage : Storage) (crypto : Crypto) (context : Context)
    (expected : Bytes) (time : Nat) (witness : CommitWitness) : IO Result := do
  if !(← verifyCommitWitness crypto context witness) then return .invalid
  let some prior ← restoreCached storage context expected | return .invalid
  if witnessBefore prior witness then return ← acknowledgeRetained storage prior
  let j := prior.journal
  let witnesses := if j.commitWitnesses.any (fun w =>
      w.view == witness.view && w.block == witness.block &&
      w.attestation.signer == witness.attestation.signer) then j.commitWitnesses
    else j.commitWitnesses ++ [witness]
  let some next := appendRestored prior [encodeInput (.deliveryAt time witness.message)] witnesses
    | return .invalid
  commitRestored storage expected next

/-- Sign only a durable actual COMMIT send, with its retained audit cause.
Requiring local doCommit here would destroy liveness: prepare totality does not
imply a quorum of local doCommit outputs. -/
def exportCommitment (storage : Storage) (crypto : Crypto) (context : Context)
    (view : Nat) (block : Block) : IO (Option Attestation) := do
  let bytes ← storage.read
  let some (j,s) ← restoredPair storage context bytes | return none
  if !exportable s view block then return none
  let signature ← crypto.sign (commitmentBytes context view block)
  if signature.length != 3309 then return none
  return some ⟨j.self,signature⟩
/-- Any replica may reconstruct a certificate from received COMMIT evidence,
including a replica which never locally doCommitted. Its own durable COMMIT send
can contribute without a loopback packet. The result is reverified, not cast. -/
def recoverCommitment (storage : Storage) (crypto : Crypto) (context : Context)
    (view : Nat) (block : Block) : IO (Option (VerifiedCommit context)) := do
  let some (journal,_) ← restoredPair storage context (← storage.read) | return none
  let mut signers := (journal.commitWitnesses.filter (fun w =>
    w.view == view && w.block == block)).map CommitWitness.attestation
  if !(signers.any (fun a => a.signer == journal.self)) then
    if let some own ← exportCommitment storage crypto context view block then
      signers := signers ++ [own]
  verifyCommitted crypto context ⟨context,view,block,signers⟩
/-- Import a transferable quorum using one durable transaction. Signatures are
checked before any contained COMMIT is counted; all proofs survive restart.
This does not produce Input.checked or source application authority. -/
def receiveCommitment (storage : Storage) (crypto : Crypto) (context : Context)
    (expected : Bytes) (time : Nat) (certificateBytes : Bytes) : IO Result := do
  let some verified ← verifyCommittedBytes crypto context certificateBytes | return .invalid
  let certificate := verified.certificate
  let some prior ← restoreCached storage context expected | return .invalid
  let journal := prior.journal
  let incoming := certificate.signers.map (fun a =>
    CommitWitness.mk certificate.view certificate.block a)
  if ∀ witness ∈ incoming, witnessBefore prior witness then
    return ← acknowledgeRetained storage prior
  let witnesses := incoming.foldl (fun ws w =>
    if ws.any (fun old => old.view == w.view && old.block == w.block &&
        old.attestation.signer == w.attestation.signer) then ws else ws ++ [w])
    journal.commitWitnesses
  let some next := appendRestored prior
      (incoming.map (fun w => encodeInput (.deliveryAt time w.message))) witnesses
    | return .invalid
  commitRestored storage expected next
end Minidregg.Compiler.GenericSimplexIO
