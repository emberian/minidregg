import Compiler.GenericSimplexCodec
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
/-- One atomic append/readback boundary before any newly enabled network output.
CAS must include source reservation state when input.checked grants reservation
authority; a separate ordinary-file journal cannot supply that atomicity. -/
def persist (storage : Storage) (context : Context) (expected : Bytes)
    (input : Input) : IO Result := do
  let some (j,_) := restore context expected | return .invalid
  let nextJournal := { j with events := j.events ++ [encodeInput input] }
  let bytes := journalStream.encode nextJournal
  let some (_,s) := restore context bytes | return .invalid
  let outcome ← storage.compareAppend expected bytes
  match outcome with
  | .conflict => return .conflict
  | .uncertain => return .uncertain
  | .durable =>
      if (← storage.read) != bytes then return .uncertain
      return .durable s
/-- Verification, protocol delivery and retained transferable evidence share one
journal CAS. A crash cannot preserve the counted COMMIT while dropping the
witness needed to recover its decision. Only this producer accepts peer proofs. -/
def receiveCommitWitness (storage : Storage) (crypto : Crypto) (context : Context)
    (expected : Bytes) (time : Nat) (witness : CommitWitness) : IO Result := do
  if !(← verifyCommitWitness crypto context witness) then return .invalid
  let some (j,_) := restore context expected | return .invalid
  let witnesses := if j.commitWitnesses.any (fun w =>
      w.view == witness.view && w.block == witness.block &&
      w.attestation.signer == witness.attestation.signer) then j.commitWitnesses
    else j.commitWitnesses ++ [witness]
  let nextJournal := { j with
    events := j.events ++ [encodeInput (.deliveryAt time witness.message)]
    commitWitnesses := witnesses }
  let bytes := journalStream.encode nextJournal
  let some (_,state) := restore context bytes | return .invalid
  match ← storage.compareAppend expected bytes with
  | .conflict => return .conflict
  | .uncertain => return .uncertain
  | .durable =>
    if (← storage.read) != bytes then return .uncertain
    return .durable state

/-- Sign only a durable actual COMMIT send, with its retained audit cause.
Requiring local doCommit here would destroy liveness: prepare totality does not
imply a quorum of local doCommit outputs. -/
def exportCommitment (storage : Storage) (crypto : Crypto) (context : Context)
    (view : Nat) (block : Block) : IO (Option Attestation) := do
  let bytes ← storage.read
  let some (j,s) := restore context bytes | return none
  if !exportable s view block then return none
  let signature ← crypto.sign (commitmentBytes context view block)
  if signature.length != 3309 then return none
  return some ⟨j.self,signature⟩
/-- Any replica may reconstruct a certificate from received COMMIT evidence,
including a replica which never locally doCommitted. Its own durable COMMIT send
can contribute without a loopback packet. The result is reverified, not cast. -/
def recoverCommitment (storage : Storage) (crypto : Crypto) (context : Context)
    (view : Nat) (block : Block) : IO (Option (VerifiedCommit context)) := do
  let some (journal,_) := restore context (← storage.read) | return none
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
  let some (journal,_) := restore context expected | return .invalid
  let incoming := certificate.signers.map (fun a =>
    CommitWitness.mk certificate.view certificate.block a)
  let witnesses := incoming.foldl (fun ws w =>
    if ws.any (fun old => old.view == w.view && old.block == w.block &&
        old.attestation.signer == w.attestation.signer) then ws else ws ++ [w])
    journal.commitWitnesses
  let next := { journal with
    events := journal.events ++ incoming.map (fun w => encodeInput (.deliveryAt time w.message))
    commitWitnesses := witnesses }
  let bytes := journalStream.encode next
  let some (_,state) := restore context bytes | return .invalid
  match ← storage.compareAppend expected bytes with
  | .conflict => return .conflict
  | .uncertain => return .uncertain
  | .durable =>
    if (← storage.read) != bytes then return .uncertain
    return .durable state
end Minidregg.Compiler.GenericSimplexIO
