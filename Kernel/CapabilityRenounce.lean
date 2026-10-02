/-
# Kernel.CapabilityRenounce — a holder revokes a capability it holds

The host face of `Theory.Renounce`. A renounce command names the signer, the
capability's kind and id, and a nonce. The ingress carries that command and one
signed envelope: the signer's CURRENT key (`CredentialSignatureAdmission.select`:
the subject's current key epoch, the key record at that epoch, registered and
not revoked) over a request whose subject is the command's signer and whose
arguments digest binds the whole command. No management grant, capability or
policy participates.

Order of admission. The signature is checked BEFORE the gate: the request is
built from the command alone (it names no stored capability field), so an
unauthenticated caller learns nothing about which capabilities exist or whom
they name. Only after the signer is authenticated does `Renounce.gateAt` decide:
`notHolder` (no capability at that id is held by the signer -- absent, another
subject's, or a bearer grant), `unregistered`, `alreadyRevoked`.

The write is the existing revocation record (`RevokeDeclaration` for
`.capability id`): one presence entry on the append-only `revoked` plane.
Descendants die by the existing lineage rule. The operation marker is a durable
nullifier, so an exact retry replays its receipt; a second renounce under a new
nonce reaches the gate and is refused `alreadyRevoked`.
-/
import Kernel.CapabilityRevocationController
import Theory.Renounce

namespace Minidregg.Kernel.CapabilityRenounce

open Minidregg.Compiler
open Minidregg.Compiler.CredentialAuthorityDomainReceiver
open Minidregg.Compiler.CredentialAuthorityEntryCodec
open Minidregg.Compiler.ResourceBirthCodec
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Kernel.DurableDataIntent
open Minidregg.Theory
open Minidregg.Theory.CellRegistry
open Minidregg.Theory.CellState
open Minidregg.Theory.CredentialAuthorityState
open Minidregg.Theory.CredentialAuthorityEffects
open Minidregg.Theory.IndexedProgram
open Minidregg.Theory.TypedAuthorization

set_option autoImplicit false

abbrev Deployment := CanonicalCellRegistry.Deployment
abbrev Durable := DurableReceiverIO.Loaded ResourceBirthCodec.rootBytes
abbrev Snapshot := CredentialAuthorityDomain.Snapshot
abbrev AuthorityMaterializer := CredentialAuthorityCell.materializer
abbrev Ambient := CapabilityRevocationController.Ambient

/-! ## Command and ingress -/

structure Command where
  subject : SubjectId
  nonce : Nat
  kind : ResourceKind
  capability : CapabilityId
  deriving DecidableEq, Repr

def commandStream : StreamCodec Command :=
  StreamCodec.xmap
    (StreamCodec.product TypedAuthorizationRequestCodec.subjectIdStream
      (StreamCodec.product StreamCodec.nat
        (StreamCodec.product ResourceBirthCodec.resourceKindStream capabilityIdStream)))
    (fun command => (command.subject, command.nonce, command.kind, command.capability))
    (fun (subject, nonce, kind, capability) => ⟨subject, nonce, kind, capability⟩)
    (by intro command; cases command; rfl)

def commandFrame : List UInt8 := "DREGG/CAPABILITY/RENOUNCE".toUTF8.toList ++ [1]

def rawCommandCodec : LawfulCodec Command where
  encode command := commandFrame ++ commandStream.encode command
  decode bytes := if bytes.take commandFrame.length = commandFrame then
    commandStream.toLawful.decode (bytes.drop commandFrame.length) else none
  decode_encode := by
    intro command
    have decoded := commandStream.toLawful.decode_encode command
    change commandStream.toLawful.decode (commandStream.encode command) = some command at decoded
    simp [decoded]

def commandCodec : LawfulCodec Command := ResourceBirthCodec.strictCodec rawCommandCodec

theorem command_decode_canonical {bytes : List UInt8} {command : Command}
    (decoded : commandCodec.decode bytes = some command) : commandCodec.encode command = bytes :=
  ResourceBirthCodec.strictCodec_canonical rawCommandCodec decoded

/-- One operation per (signer, nonce): a substituted capability under the same
nonce is a transaction-identity conflict, never a second admission. -/
def operationMarker (domain semantics : Digest) (command : Command) : Nat :=
  (Sp800185Cshake256.hash "DREGG.CAPABILITY.RENOUNCE.IDENTITY/v1".toUTF8.toList
    ((StreamCodec.product digestStream
      (StreamCodec.product digestStream
        (StreamCodec.product TypedAuthorizationRequestCodec.subjectIdStream StreamCodec.nat))).encode
      (domain, semantics, command.subject, command.nonce))).digest.value

/-- The revocation record a renounce writes: the existing one. -/
def declaration (domain semantics : Digest) (preRoot : Digest) (command : Command) :
    RevokeDeclaration :=
  ⟨.capability command.capability, preRoot, operationMarker domain semantics command⟩

def commandBytes (domain semantics : Digest) (command : Command) : List UInt8 :=
  (StreamCodec.product digestStream (StreamCodec.product digestStream bytesStream)).encode
    (domain, semantics, commandCodec.encode command)

def argsDigest (domain semantics : Digest) (command : Command) : Digest :=
  (Sp800185Cshake256.hash "DREGG.CAPABILITY.RENOUNCE.ARGS/v1".toUTF8.toList
    (commandBytes domain semantics command)).digest

def effectsDigest (domain semantics : Digest) (preRoot : Digest) (command : Command) : Digest :=
  (Sp800185Cshake256.hash "DREGG.CAPABILITY.RENOUNCE.EFFECT/v1".toUTF8.toList
    (commandBytes domain semantics command ++
      CapabilityRevocationController.declarationCodec.encode
        (declaration domain semantics preRoot command))).digest

/-- The request the signer signs. It is built from the command and the
authority snapshot alone -- no stored capability field -- so the signature is
checked before anything about the named capability is read. The target slot
carries the renounced capability's id; a renounce consults no policy, so the
policy coordinates are zero; the arguments digest binds the whole command. -/
def request (snapshot : Snapshot) (semantics : Digest) (ambient : Ambient)
    (command : Command) : Request .program where
  domain := snapshot.domain
  semantics := semantics
  federation := ambient.federation
  subject := command.subject
  subjectKeyEpoch := snapshot.authState.subjectKeyEpoch command.subject
  target := ⟨command.capability.value⟩
  verb := .revokeCapability
  argsDigest := argsDigest snapshot.domain semantics command
  effectsDigest := effectsDigest snapshot.domain semantics snapshot.cell.root command
  nonce := operationMarker snapshot.domain semantics command
  height := ambient.height
  preStateRoot := snapshot.cell.root
  policyId := ⟨0⟩
  policyEpoch := 0
  policyRevision := 0
  cost := (commandCodec.encode command).length

structure Ingress where
  commandBytes : List UInt8
  envelopeBytes : List UInt8

def ingressStream : StreamCodec Ingress :=
  StreamCodec.xmap (StreamCodec.product bytesStream bytesStream)
    (fun ingress => (ingress.commandBytes, ingress.envelopeBytes))
    (fun (command, envelope) => ⟨command, envelope⟩)
    (by intro ingress; cases ingress; rfl)

def ingressFrame : List UInt8 := "DREGG/CAPABILITY/RENOUNCE/SIGNED-INGRESS".toUTF8.toList ++ [1]

def rawIngressCodec : LawfulCodec Ingress where
  encode ingress := ingressFrame ++ ingressStream.encode ingress
  decode bytes := if bytes.take ingressFrame.length = ingressFrame then
    ingressStream.toLawful.decode (bytes.drop ingressFrame.length) else none
  decode_encode := by
    intro ingress
    have decoded := ingressStream.toLawful.decode_encode ingress
    change ingressStream.toLawful.decode (ingressStream.encode ingress) = some ingress at decoded
    simp [decoded]

def ingressCodec : LawfulCodec Ingress := strictCodec rawIngressCodec

structure DecodedIngress where
  private mk ::
  ingress : Ingress
  command : Command
  commandExact : commandCodec.encode command = ingress.commandBytes

def decodeIngress (bytes : List UInt8) : Option DecodedIngress := do
  let ingress ← ingressCodec.decode bytes
  match commandExact : commandCodec.decode ingress.commandBytes with
  | none => none
  | some command => some ⟨ingress, command, command_decode_canonical commandExact⟩

def DecodedIngress.bytes (ingress : DecodedIngress) : List UInt8 := ingressCodec.encode ingress.ingress

/-! ## Preparation (no read of the named capability) -/

inductive Reject where
  | malformedCommand | authorityUnavailable | replayedMarker
  | signature (reason : CredentialSignatureAdmission.Reject)
  | signatureBinding
  | validation | physicalPreparation
  deriving Repr

def requireSome {A : Type} (reason : Reject) : Option A → Except Reject A
  | none => .error reason
  | some value => .ok value

structure Prepared (deployment : Deployment) (semantics : Digest) (ambient : Ambient)
    (durable : Durable) (command : Command) where
  private mk ::
  authority : Loaded deployment durable.snapshot
  unspent : authority.snapshot.spent
    (operationMarker authority.snapshot.domain semantics command) = false

def prepare (deployment : Deployment) (semantics : Digest) (ambient : Ambient)
    (durable : Durable) (command : Command) :
    Except Reject (Prepared deployment semantics ambient durable command) := do
  let authority ← requireSome .authorityUnavailable (loadDeployment deployment durable.snapshot)
  if unspent : authority.snapshot.spent (operationMarker authority.snapshot.domain semantics command) = false then
    .ok ⟨authority, unspent⟩
  else .error .replayedMarker

variable {deployment : Deployment} {semantics : Digest} {ambient : Ambient}
  {durable : Durable} {command : Command}

def Prepared.request (prepared : Prepared deployment semantics ambient durable command) :
    Request .program :=
  CapabilityRenounce.request prepared.authority.snapshot semantics ambient command

def Prepared.marker (prepared : Prepared deployment semantics ambient durable command) : Nat :=
  operationMarker prepared.authority.snapshot.domain semantics command

def Prepared.declaration (prepared : Prepared deployment semantics ambient durable command) :
    RevokeDeclaration :=
  CapabilityRenounce.declaration prepared.authority.snapshot.domain semantics
    prepared.authority.snapshot.cell.root command

/-! ## Admission: the signer, then the gate -/

structure Accepted (prepared : Prepared deployment semantics ambient durable command)
    (envelope : List UInt8) where
  private mk ::
  receipt : CredentialSignatureAdmission.CheckedSignature prepared.authority.snapshot
  envelopeExact : receipt.envelopeBytes = envelope
  bound : CredentialSignatureAdmission.verifySignature prepared.authority.snapshot prepared.marker
    prepared.request receipt = true
  victim : Capability command.kind
  gated : Renounce.gateAt prepared.authority.snapshot.cell command.kind command.capability
    command.subject = .ok victim
  validated : ValidatedPatch AuthorityMaterializer prepared.authority.snapshot.cell
    prepared.authority.snapshot.cell.root (prepared.declaration.patch prepared.authority.snapshot.logical)

/-- A gate refusal carries the checked signature that preceded it. It is said
only to the authenticated signer, and it is about the signer's own holding:
`notHolder` (the signer holds no capability at that id), `unregistered`,
`alreadyRevoked`. -/
structure HolderRefusal (prepared : Prepared deployment semantics ambient durable command)
    (envelope : List UInt8) where
  private mk ::
  receipt : CredentialSignatureAdmission.CheckedSignature prepared.authority.snapshot
  envelopeExact : receipt.envelopeBytes = envelope
  bound : CredentialSignatureAdmission.verifySignature prepared.authority.snapshot prepared.marker
    prepared.request receipt = true
  reason : Renounce.Reject
  gated : Renounce.gateAt prepared.authority.snapshot.cell command.kind command.capability
    command.subject = .error reason

inductive Admission (prepared : Prepared deployment semantics ambient durable command)
    (envelope : List UInt8) where
  | accepted (accepted : Accepted prepared envelope)
  /-- After the signature verified: the gate refused, to the signer. -/
  | refusedToHolder (refusal : HolderRefusal prepared envelope)
  /-- Before or outside authentication: never disclosed. -/
  | rejected (reason : Reject)

def admitNative (native : CredentialSignatureIO.NativeConfig)
    (prepared : Prepared deployment semantics ambient durable command) (envelope : List UInt8) :
    IO (Admission prepared envelope) := do
  match ← CredentialSignatureAdmission.verifyNative native prepared.authority.snapshot
      prepared.marker prepared.request envelope with
  | .error reason => return .rejected (.signature reason)
  | .ok receipt =>
    if same : receipt.envelopeBytes = envelope then
      if bound : CredentialSignatureAdmission.verifySignature prepared.authority.snapshot prepared.marker
          prepared.request receipt = true then
        match gated : Renounce.gateAt prepared.authority.snapshot.cell command.kind command.capability
            command.subject with
        | .error reason => return .refusedToHolder ⟨receipt, same, bound, reason, gated⟩
        | .ok victim =>
          match validate AuthorityMaterializer prepared.authority.snapshot.cell
              prepared.authority.snapshot.cell.root
              (prepared.declaration.patch prepared.authority.snapshot.logical) with
          | .rejected _ => return .rejected .validation
          | .accepted validated => return .accepted ⟨receipt, same, bound, victim, gated, validated⟩
      else return .rejected .signatureBinding
    else return .rejected .signatureBinding

/-- The authority cell after the renounce: the validated revocation patch
applied. It is the one authority write. -/
def Accepted.authorityPost {prepared : Prepared deployment semantics ambient durable command}
    {envelope : List UInt8} (accepted : Accepted prepared envelope) : CredentialAuthorityDomain.Cell :=
  accepted.validated.apply

/-! ## Durable intent -/

def transactionId (domain semantics : Digest) (ingress : DecodedIngress) : Digest :=
  ⟨operationMarker domain semantics ingress.command⟩

def event (domain semantics : Digest) (ingress : DecodedIngress) : StableEvent where
  codecVersion := 1
  domain := domain
  eventId := (Sp800185Cshake256.hash "DREGG.CAPABILITY.RENOUNCE.EVENT/v1".toUTF8.toList
    ((StreamCodec.product digestStream (StreamCodec.product digestStream bytesStream)).encode
      (domain, semantics, ingress.bytes))).digest
  canonicalBytes := ingress.bytes

def nullifier (domain semantics : Digest) (ingress : DecodedIngress) : StableNullifier :=
  CredentialAuthorityReplay.nullifier domain (operationMarker domain semantics ingress.command)

variable {envelope : List UInt8}

def writes {prepared : Prepared deployment semantics ambient durable command}
    (accepted : Accepted prepared envelope) : List DataWrite :=
  prepared.authority.writes accepted.authorityPost

def readGuards {prepared : Prepared deployment semantics ambient durable command}
    (accepted : Accepted prepared envelope) : List ReadGuard :=
  prepared.authority.readGuards.filter fun guard =>
    guard.cellId ∉ (writes accepted).map DataWrite.cellId

def PhysicalShape {prepared : Prepared deployment semantics ambient durable command}
    (accepted : Accepted prepared envelope) : Prop :=
  ((writes accepted).map DataWrite.cellId).Nodup ∧
    (∀ write ∈ writes accepted, write.expectedPre = durable.snapshot.model.roots write.cellId) ∧
    (∀ write ∈ writes accepted, ResourceBirthController.Concrete.PhysicalPostLaw deployment write) ∧
    (∀ guard ∈ readGuards accepted, guard.expectedRoot = durable.snapshot.model.roots guard.cellId)

instance physicalShapeDecidable {prepared : Prepared deployment semantics ambient durable command}
    (accepted : Accepted prepared envelope) : Decidable (PhysicalShape accepted) := by
  unfold PhysicalShape
  infer_instance

theorem writes_roots_bound {prepared : Prepared deployment semantics ambient durable command}
    (accepted : Accepted prepared envelope) (write : DataWrite) (member : write ∈ writes accepted) :
    rootBytes write.canonicalPostBytes = write.exactPost := by
  simp only [writes, Loaded.writes, List.mem_singleton] at member
  subst write
  exact prepared.authority.write_root_bound _

theorem readGuards_readonly {prepared : Prepared deployment semantics ambient durable command}
    (accepted : Accepted prepared envelope) (guard : ReadGuard) (member : guard ∈ readGuards accepted) :
    guard.cellId ∉ (writes accepted).map DataWrite.cellId := by
  simpa using (List.mem_filter.mp member).2

structure AcceptedRenounce (deployment : Deployment) (semantics : Digest) (ambient : Ambient)
    (durable : Durable) (ingress : DecodedIngress) where
  private mk ::
  prepared : Prepared deployment semantics ambient durable ingress.command
  accepted : Accepted prepared ingress.ingress.envelopeBytes
  physical : PhysicalShape accepted

inductive DecodedAdmission (deployment : Deployment) (semantics : Digest) (ambient : Ambient)
    (durable : Durable) (ingress : DecodedIngress) where
  | accepted (accepted : AcceptedRenounce deployment semantics ambient durable ingress)
  | refusedToHolder {prepared : Prepared deployment semantics ambient durable ingress.command}
      (refusal : HolderRefusal prepared ingress.ingress.envelopeBytes)
  | rejected (reason : Reject)

def admitDecodedNative (deployment : Deployment) (semantics : Digest) (ambient : Ambient)
    (durable : Durable) (native : CredentialSignatureIO.NativeConfig) (ingress : DecodedIngress) :
    IO (DecodedAdmission deployment semantics ambient durable ingress) := do
  match prepare deployment semantics ambient durable ingress.command with
  | .error reason => return .rejected reason
  | .ok prepared =>
    match ← admitNative native prepared ingress.ingress.envelopeBytes with
    | .rejected reason => return .rejected reason
    | .refusedToHolder refusal => return .refusedToHolder refusal
    | .accepted accepted =>
      if physical : PhysicalShape accepted then return .accepted ⟨prepared, accepted, physical⟩
      else return .rejected .physicalPreparation

variable {ingress : DecodedIngress}

def charge (accepted : AcceptedRenounce deployment semantics ambient durable ingress) :
    ResourceCost.Charge
  | .incidences => 1
  | .turnBytes => ingress.bytes.length
  | .memoryTouches => (writes accepted.accepted).length + (readGuards accepted.accepted).length
  | .storageBytes => ((writes accepted.accepted).map fun write => write.canonicalPostBytes.length).sum
  | .witnessBytes => ingress.ingress.envelopeBytes.length
  | .proofWork => 1
  | .feeDebit | .networkBytes | .sideEffectCount | .leaseByteBlocks => 0

def intent (accepted : AcceptedRenounce deployment semantics ambient durable ingress) :
    DataIntent rootBytes where
  transactionId := transactionId deployment.domain semantics ingress
  writes := writes accepted.accepted
  readGuards := readGuards accepted.accepted
  nullifiers := [nullifier deployment.domain semantics ingress]
  exactCharge := charge accepted
  event := event deployment.domain semantics ingress
  subject := some ingress.command.subject
  postRootsBound := writes_roots_bound accepted.accepted
  guardsReadOnly := readGuards_readonly accepted.accepted

structure Receipt where
  transactionId : Digest
  eventId : Digest
  deriving DecidableEq, Repr

def receipt (domain semantics : Digest) (ingress : DecodedIngress) : Receipt :=
  ⟨transactionId domain semantics ingress, (event domain semantics ingress).eventId⟩

def replay (domain semantics : Digest) (durable : Durable) (ingress : DecodedIngress) :
    Option (Except Unit Receipt) :=
  match DurableCommitProtocol.Snapshot.lookupRecorded (transactionId domain semantics ingress)
      durable.snapshot.model.journal with
  | none => none
  | some recorded =>
    if recorded.transactionId = transactionId domain semantics ingress ∧
        recorded.event.event = event domain semantics ingress ∧
        recorded.nullifiers = [nullifier domain semantics ingress] then
      some (.ok (receipt domain semantics ingress))
    else some (.error ())

/-- An exact retry returns the original receipt and nothing else. -/
theorem replay_only_original (domain semantics : Digest) (durable : Durable) (ingress : DecodedIngress)
    (result : Receipt) (accepted : replay domain semantics durable ingress = some (.ok result)) :
    result = receipt domain semantics ingress ∧
      ∃ recorded,
        DurableCommitProtocol.Snapshot.lookupRecorded (transactionId domain semantics ingress)
          durable.snapshot.model.journal = some recorded ∧
        recorded.event.event = event domain semantics ingress ∧
        recorded.nullifiers = [nullifier domain semantics ingress] := by
  unfold replay at accepted
  split at accepted
  · cases accepted
  · rename_i recorded found
    split at accepted
    · rename_i exactRecord
      have same : receipt domain semantics ingress = result := by simpa using accepted
      exact ⟨same.symm, recorded, found, exactRecord.2⟩
    · cases accepted

inductive Result where
  | confirmed (kind : DurableReceiverIO.Confirmation) (receipt : Receipt)
  | rejected (reason : Reject)
  /-- The gate's refusal, after the signer's signature verified. -/
  | refusedToHolder (reason : Renounce.Reject)
  | transactionConflict
  | durableRejected (reason : DurableDataIntent.RejectReason)
  | contention
  | unavailable (detail : String)
  | uncertain (detail : String)

def receiveLoaded (deployment : Deployment) (semantics : Digest) (ambient : Ambient)
    (native : CredentialSignatureIO.NativeConfig) (transport : DurableReceiverIO.Transport)
    (durable : Durable) (bytes : List UInt8) : IO Result := do
  let some ingress := decodeIngress bytes
    | return .rejected .malformedCommand
  match replay deployment.domain semantics durable ingress with
  | some (.ok prior) => return .confirmed .replayed prior
  | some (.error _) => return .transactionConflict
  | none =>
    match ← admitDecodedNative deployment semantics ambient durable native ingress with
    | .rejected reason => return .rejected reason
    | .refusedToHolder refusal => return .refusedToHolder refusal.reason
    | .accepted accepted =>
      match ← DurableReceiverIO.receiveLoaded transport rootBytes durable (intent accepted) with
      | .confirmed kind _ => return .confirmed kind (receipt deployment.domain semantics ingress)
      | .rejected reason => return .durableRejected reason
      | .contention => return .contention
      | .unavailable detail => return .unavailable detail
      | .uncertain detail => return .uncertain detail

/-- A refusal disclosed to the holder was produced after a checked signature
over exactly this renounce's request, whose subject is the command's signer. -/
theorem HolderRefusal.signer_authenticated
    {prepared : Prepared deployment semantics ambient durable command} {envelope : List UInt8}
    (refusal : HolderRefusal prepared envelope) :
    refusal.receipt.request = ⟨.program, prepared.request⟩ ∧
      prepared.request.subject = command.subject ∧ refusal.receipt.envelopeBytes = envelope :=
  ⟨(CredentialSignatureAdmission.verified_request_exact _ _ _ _ refusal.bound).1, rfl,
    refusal.envelopeExact⟩

/-- info: 'Minidregg.Kernel.CapabilityRenounce.HolderRefusal.signer_authenticated' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms HolderRefusal.signer_authenticated

/-- info: 'Minidregg.Kernel.CapabilityRenounce.replay_only_original' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms replay_only_original

end Minidregg.Kernel.CapabilityRenounce
