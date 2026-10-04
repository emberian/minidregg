/-
# Kernel.Receivers.SubjectKeyRotation -- a pre-rotated subject rotates its signing key

The host face of `Theory.KeyPreRotation`, as a `Kernel.Receiving.Family`.  A
rotation command names the subject and its complete successor key record; the
ingress carries that command and one signature, by the NEW key, over the
rotation's possession frame.  No sponsor, capability or current-key signature
participates: the authority is the commitment the current record already holds.

The family declares:

* one signature claim (`claim`): the new key, the possession frame, the
  presented signature -- computed from the decoded ingress and the deployment
  alone, so `Kernel.Receiving` verifies it before `prepare` runs;
* the gate (`prepare`): `KeyPreRotation.gate` at the loaded authority cell,
  instantiated with `nextKeyDigest` (cSHAKE256 under `DREGG.SIGNING-KEY.NEXT/v1`)
  and the oracle of the claim (`assumed`; `admitted_gate` re-derives it under
  the verifier's actual verdict), a fresh public key, an Ed25519 key shape, an
  unspent marker, and the validated patch;
* the patch (`writes`): `KeyPreRotation.patch`, the subject's key rows only,
  as the authority cell's one write.  The authority cell is `kernelOnly` in
  the registry with this family among its writers, so the Receiver's law
  judgement admits the write with no law step (`lawStep` is `none`) and adds
  no guard: the intent is byte-identical to the pre-judgement one;
* the journal identity: the operation marker is the transaction id and the
  durable nullifier, so an exact rotation is admitted once; a second rotation
  needs the next commitment, so a replayed ingress fails the gate as well.

Everything else -- refusals, the accepted object, read guards, shape, charge,
intent, replay, receipt, `receiveLoaded` -- is `Kernel.Receiving`'s one copy.
The `DataIntent` an admission produces is byte-for-byte the one the deleted
bespoke receiver produced (same writes, guards, nullifier, event, subject and
charge on every lane; `proofWork` is the one claim), so the journal and its
replay are unchanged.
-/
import Compiler.SigningKeyCommitment
import Kernel.ParticipantKeyEnrollment
import Kernel.Receiving
import Kernel.ReceivingLaw
import Theory.KeyPreRotation

namespace Minidregg.Kernel.SubjectKeyRotation

open Minidregg.Compiler
open Minidregg.Compiler.CredentialAuthorityDomainReceiver
open Minidregg.Compiler.CredentialAuthorityEntryCodec
open Minidregg.Compiler.ResourceBirthCodec
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Kernel
open Minidregg.Kernel.DurableDataIntent
open Minidregg.Theory
open Minidregg.Theory.CellState
open Minidregg.Theory.CellRegistry
open Minidregg.Theory.CredentialAuthorityState
open Minidregg.Theory.CredentialSigningKey
open Minidregg.Theory.IndexedProgram
open Minidregg.Theory.Store (Store Patch Op Address)
open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.Receiving (SigQuery need)

set_option autoImplicit false

abbrev Deployment := CanonicalCellRegistry.Deployment
abbrev Durable := Receiving.Durable
abbrev AuthorityMaterializer := CredentialAuthorityCell.materializer
abbrev Registry := CanonicalCellRegistry.registry

/-! ## The next-key digest

One definition, `ParticipantKeyEnrollment.nextKeyDigest`: enrollment commits
to it and checks the next key's possession against it; a rotation opens it. -/

export Minidregg.Kernel.ParticipantKeyEnrollment (nextKeyDigest nextKeyDigestTag)

/-! ## Command, ingress, frames -/

structure Command where
  subject : SubjectId
  nonce : Nat
  key : KeyRecord
  deriving DecidableEq, Repr

def commandStream : StreamCodec Command :=
  StreamCodec.xmap
    (StreamCodec.product TypedAuthorizationRequestCodec.subjectIdStream
      (StreamCodec.product StreamCodec.nat CredentialSigningKeyCodec.keyRecordStream))
    (fun command => (command.subject, command.nonce, command.key))
    (fun (subject, nonce, key) => ⟨subject, nonce, key⟩)
    (by intro command; cases command; rfl)

def commandFrame : List UInt8 := "DREGG/SUBJECT-KEY/ROTATE/v1".toUTF8.toList

def commandCodec : LawfulCodec Command :=
  ParticipantKeyEnrollment.framed commandFrame commandStream

def Command.rotation (command : Command) : KeyPreRotation.Rotation :=
  ⟨command.subject, command.key⟩

structure Ingress where
  commandBytes : List UInt8
  possessionSignature : List UInt8
  deriving DecidableEq, Repr

def ingressStream : StreamCodec Ingress :=
  StreamCodec.xmap (StreamCodec.product bytesStream bytesStream)
    (fun ingress => (ingress.commandBytes, ingress.possessionSignature))
    (fun (command, possession) => ⟨command, possession⟩)
    (by intro ingress; cases ingress; rfl)

def ingressCodec : LawfulCodec Ingress :=
  ParticipantKeyEnrollment.framed "DREGG/SUBJECT-KEY/ROTATE/SIGNED/v1".toUTF8.toList ingressStream

structure DecodedIngress where
  private mk ::
  ingress : Ingress
  command : Command
  canonical : commandCodec.encode command = ingress.commandBytes

def decodeIngress (bytes : List UInt8) : Option DecodedIngress := do
  let ingress ← ingressCodec.decode bytes
  match commandExact : commandCodec.decode ingress.commandBytes with
  | none => none
  | some command =>
      some ⟨ingress, command,
        ResourceBirthCodec.strictCodec_canonical
          (ParticipantKeyEnrollment.framedRaw commandFrame commandStream) commandExact⟩

def DecodedIngress.bytes (ingress : DecodedIngress) : List UInt8 :=
  ingressCodec.encode ingress.ingress

/-- The operation marker: the durable nullifier and the transaction id. -/
def marker (domain semantics : Digest) (command : Command) : Nat :=
  (Sp800185Cshake256.hash "DREGG.SUBJECT-KEY.ROTATE.IDENTITY/v1".toUTF8.toList
    ((StreamCodec.product digestStream (StreamCodec.product digestStream
      (StreamCodec.product TypedAuthorizationRequestCodec.subjectIdStream
        (StreamCodec.product StreamCodec.nat StreamCodec.nat)))).encode
      (domain, semantics, command.subject, command.key.keyEpoch, command.nonce))).digest.value

/-- The exact bytes the NEW key signs. -/
def possessionFrame (domain semantics : Digest) (command : Command) : List UInt8 :=
  "DREGG/SUBJECT-KEY/ROTATE/POSSESSION/v1".toUTF8.toList ++
    (StreamCodec.product digestStream (StreamCodec.product digestStream bytesStream)).encode
      (domain, semantics, commandCodec.encode command)

/-- The signature oracle of one presented possession signature: it vouches for
the new key exactly when the native verifier accepted it under that key, and
for no other key. -/
def presented (command : Command) (verified : Bool) : List UInt8 → Bool :=
  fun publicKey => decide (publicKey = command.key.publicKey) && verified

/-- The oracle a plan assumes: the possession signature, once made, verifies. -/
def assumed (command : Command) : List UInt8 → Bool := presented command true

/-! ## The signature claim -/

/-- The deployment a rotation is admitted under. -/
structure Env where
  deployment : Deployment
  semantics : Digest

/-- The one claim: the new key signed the possession frame of this command. -/
def claim (env : Env) (ingress : DecodedIngress) : SigQuery :=
  ⟨ingress.command.key.publicKey,
    possessionFrame env.deployment.domain env.semantics ingress.command,
    ingress.ingress.possessionSignature⟩

/-! ## The gate -/

inductive Reject where
  | authorityUnavailable
  | gate (reason : KeyPreRotation.Reject)
  | publicKeyExists | malformedKey | replayedMarker | validation
  deriving Repr

structure Prepared (env : Env) (durable : Durable) (command : Command) where
  private mk ::
  authority : Loaded env.deployment durable.snapshot
  current : KeyRecord
  gated : KeyPreRotation.gate nextKeyDigest authority.snapshot.logical command.rotation
    (assumed command) = .ok current
  publicKeyFresh : ParticipantKeyEnrollment.allKeys authority.snapshot.logical
    (fun key => key.publicKey != command.key.publicKey) = true
  keyShape : command.key.algorithm = CredentialSignatureAdmission.ed25519Algorithm ∧
    command.key.publicKey.length = 32 ∧
    command.key.activeFrom ≤ authority.snapshot.revision + 1 ∧
    authority.snapshot.revision + 1 ≤ command.key.activeUntil
  unspent : authority.snapshot.spent (marker authority.snapshot.domain env.semantics command) = false
  validated : CellState.ValidatedPatch AuthorityMaterializer authority.snapshot.cell
    authority.snapshot.cell.root
    (KeyPreRotation.patch authority.snapshot.logical current command.rotation)

/-- The gate.  It runs only after `claim` verified (`Kernel.Receiving`), and,
signature-free, behind the host's rotation plan (`NativeHost.rotationPlanLoaded`). -/
def prepare (env : Env) (durable : Durable) (command : Command) :
    Except Reject (Prepared env durable command) := do
  let authority ← need .authorityUnavailable (loadDeployment env.deployment durable.snapshot)
  let snapshot := authority.snapshot
  match gated : KeyPreRotation.gate nextKeyDigest snapshot.logical command.rotation
      (assumed command) with
  | .error reason => throw (.gate reason)
  | .ok current =>
    if publicKeyFresh : ParticipantKeyEnrollment.allKeys snapshot.logical
        (fun key => key.publicKey != command.key.publicKey) then
      if keyShape : command.key.algorithm = CredentialSignatureAdmission.ed25519Algorithm ∧
          command.key.publicKey.length = 32 ∧
          command.key.activeFrom ≤ snapshot.revision + 1 ∧
          snapshot.revision + 1 ≤ command.key.activeUntil then
        if unspent : snapshot.spent (marker snapshot.domain env.semantics command) = false then
          match validate AuthorityMaterializer snapshot.cell snapshot.cell.root
              (KeyPreRotation.patch snapshot.logical current command.rotation) with
          | .rejected _ => throw .validation
          | .accepted validated =>
              pure ⟨authority, current, gated, publicKeyFresh, keyShape, unspent, validated⟩
        else throw .replayedMarker
      else throw .malformedKey
    else throw .publicKeyExists

variable {env : Env} {durable : Durable} {command : Command}

/-- The authority cell after rotation: the validated patch applied. -/
def Prepared.authorityPost (prepared : Prepared env durable command) :
    CredentialAuthorityDomain.Cell :=
  prepared.validated.apply

/-- A prepared rotation opens the commitment: the new key's digest is the
current record's `nextKeyDigest`. -/
theorem Prepared.precommitted (prepared : Prepared env durable command) :
    prepared.current.nextKeyDigest = some (nextKeyDigest command.key.publicKey) :=
  (KeyPreRotation.rotation_requires_precommitted_key prepared.gated).2

/-! ## The patch and the journal identity -/

def writes (prepared : Prepared env durable command) : List DataWrite :=
  prepared.authority.writes prepared.authorityPost

theorem writes_roots_bound (prepared : Prepared env durable command)
    (write : DataWrite) (member : write ∈ writes prepared) :
    rootBytes write.canonicalPostBytes = write.exactPost := by
  simp only [writes, Loaded.writes, List.mem_singleton] at member
  subst write
  exact prepared.authority.write_root_bound _

def physicalPostLaw (prepared : Prepared env durable command) : Bool :=
  (writes prepared).all fun write =>
    decide (ResourceBirthController.Concrete.PhysicalPostLaw env.deployment write)

def transactionId (domain semantics : Digest) (ingress : DecodedIngress) : Digest :=
  ⟨marker domain semantics ingress.command⟩

def event (domain semantics : Digest) (ingress : DecodedIngress) : StableEvent where
  codecVersion := 1
  domain := domain
  eventId := (Sp800185Cshake256.hash "DREGG.SUBJECT-KEY.ROTATE.EFFECT/v1".toUTF8.toList
    ((StreamCodec.product digestStream (StreamCodec.product digestStream bytesStream)).encode
      (domain, semantics, ingress.bytes))).digest
  canonicalBytes := ingress.bytes

def nullifier (domain semantics : Digest) (ingress : DecodedIngress) : StableNullifier :=
  CredentialAuthorityReplay.nullifier domain (marker domain semantics ingress.command)

/-! ## The family -/

def family : Receiving.Family where
  id := .subjectKeyRotation
  Env := Env
  Ingress := DecodedIngress
  Command := Command
  Reject := Reject
  rejectRepr := inferInstance
  Prepared := Prepared
  decode := decodeIngress
  bytes := DecodedIngress.bytes
  command := DecodedIngress.command
  claims := fun env _ ingress => .ok [claim env ingress]
  prepare := prepare
  writes := writes
  writes_bound := writes_roots_bound
  -- The one write is the authority cell, kernel-only: no committed law to project for.
  lawStep := fun _ _ _ => none
  observed := fun prepared => prepared.authority.readGuards
  physicalPostLaw := physicalPostLaw
  txId := fun env ingress => transactionId env.deployment.domain env.semantics ingress
  event := fun env ingress => event env.deployment.domain env.semantics ingress
  nullifiers := fun env ingress => [nullifier env.deployment.domain env.semantics ingress]
  -- The rotation is signed by the subject's NEXT key, on the subject's behalf.
  subject := fun ingress => some ingress.command.subject
  witnessBytes := fun ingress => ingress.ingress.possessionSignature.length

abbrev receiver (laws : ReceivingLaw.Laws Durable) := family.receiver laws

/-- **The law judgement leaves the rotation's intent as it was.**  The one write
is to the kernel-only authority cell with no step, so whatever laws the Receiver
judges by, the record's read guards are exactly the authority guards off the
written cell -- the pre-judgement payload, byte for byte (writes, nullifier,
event, subject and every charge lane are untouched by the judgement). -/
theorem readGuards_unjudged (laws : ReceivingLaw.Laws Durable)
    {env : Env} {durable : Durable} {command : Command} (prepared : Prepared env durable command) :
    Receiving.Family.readGuards (F := family) laws prepared =
      Minidregg.Theory.Receiving.Receiver.guardsOff DataWrite.cellId ReadGuard.cellId
        (writes prepared) prepared.authority.readGuards := by
  have none_ : ReceivingLaw.lawGuards laws durable (family.writes prepared)
      (family.lawStep prepared) = [] := by
    show ReceivingLaw.lawGuards laws durable (writes prepared) (fun _ _ => none) = []
    rw [ReceivingLaw.lawGuards_uniform]
    simp [ReceivingLaw.writeGuards]
  simp only [Receiving.Family.readGuards, none_, List.append_nil]
  rfl

/-! ## What an admission means here -/

variable {ingress : DecodedIngress} {laws : ReceivingLaw.Laws Durable}

/-- **An admitted rotation's possession signature was vouched for**: the
verdict oracle of the admission accepts the new key's signature over this
command's possession frame. -/
theorem admitted_possession (admission : (receiver laws).Admitted env durable ingress) :
    admission.ok (claim env ingress) = true := by
  obtain ⟨claims, resolved, vouched, -, -, -⟩ :=
    ((receiver laws).admit_ok_iff admission.accepted).1 admission.admitted
  cases resolved
  exact vouched _ (List.mem_singleton_self _)

/-- **The gate under the verifier's verdict.**  An admitted rotation passes
`KeyPreRotation.gate` with the oracle that vouches for the new key exactly when
the verifier accepted its possession signature (`presented`). -/
theorem admitted_gate (admission : (receiver laws).Admitted env durable ingress) :
    let prepared : Prepared env durable ingress.command := admission.accepted.prepared
    KeyPreRotation.gate nextKeyDigest prepared.authority.snapshot.logical
        ingress.command.rotation (presented ingress.command (admission.ok (claim env ingress))) =
      .ok prepared.current := by
  intro prepared
  rw [admitted_possession admission]
  exact prepared.gated

/-- **Signature first, here**: a rotation whose possession signature the
verifier refuses is refused `unauthenticated` before the gate runs. -/
theorem refused_possession_unauthenticated (v : SigQuery → Bool)
    (refused : v (claim env ingress) = false) :
    (receiver laws).admitVia (Minidregg.Theory.Receiving.Receiver.pureVerifier v) env durable ingress =
      (pure (.error (.unauthenticated (claim env ingress))) : Id _) := by
  obtain ⟨selected, member, admitted⟩ :=
    (receiver laws).admitVia_unauthenticated v (claims := [claim env ingress]) rfl
      (List.mem_singleton_self _) refused
  rw [List.mem_singleton.mp member] at admitted
  exact admitted

/-! ## Plan and status (no secret, no signature) -/

/-- What the new key signs, authored by the host after the rotation prepares. -/
structure SigningPlan where
  domain : Digest
  semantics : Digest
  commandBytes : List UInt8
  possessionHeader : List UInt8
  deriving DecidableEq, Repr

def signingPlanStream : StreamCodec SigningPlan :=
  StreamCodec.xmap (StreamCodec.product digestStream
    (StreamCodec.product digestStream (StreamCodec.product bytesStream bytesStream)))
    (fun plan => (plan.domain, plan.semantics, plan.commandBytes, plan.possessionHeader))
    (fun (domain, semantics, command, possession) => ⟨domain, semantics, command, possession⟩)
    (by intro plan; cases plan; rfl)

def signingPlanCodec : LawfulCodec SigningPlan :=
  ParticipantKeyEnrollment.framed "DREGG/SUBJECT-KEY/ROTATE/PLAN/v1".toUTF8.toList signingPlanStream

/-- A subject's key status as seen by someone holding one public key: the
current epoch and key line, whether a next key is committed, and whether the
presented key is the current key or the committed next key.  It discloses no
key the asker does not already hold. -/
structure Status where
  epoch : Nat
  keyId : Nat
  prerotated : Bool
  isCurrent : Bool
  isCommittedNext : Bool
  currentRevoked : Bool
  deriving DecidableEq, Repr

def status (logical : Store CredentialAuthorityState.layout) (subject : SubjectId)
    (publicKey : List UInt8) : Option Status := do
  let current ← currentSigningKey logical subject
  pure ⟨current.keyEpoch, current.keyId, current.nextKeyDigest.isSome,
    decide (current.publicKey = publicKey),
    decide (current.nextKeyDigest = some (nextKeyDigest publicKey)),
    (logical ⟨.revoked, signingKeyRevocation current⟩).isSome⟩

#assert_axioms Prepared.precommitted
#assert_axioms readGuards_unjudged
#assert_axioms writes_roots_bound
#assert_axioms admitted_possession
#assert_axioms admitted_gate
#assert_axioms refused_possession_unauthenticated

end Minidregg.Kernel.SubjectKeyRotation
