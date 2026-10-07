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
import Compiler.ServedBasis
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
abbrev Ground := ServedBasis.Ground
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
  /-- The request did not declare the operation marker's replay nullifier, so its
  ground has no answer for it (`ServedBasis.Ground.markerSpent`): refused first,
  never read as unspent. -/
  | undeclaredMarker
  /-- The request did not declare the renounce's transaction id, so its ground has
  no journal answer for it (`ServedBasis.Ground.replayOf`). -/
  | undeclaredTransaction
  | signature (reason : CredentialSignatureAdmission.Reject)
  | signatureBinding
  | validation | physicalPreparation
  deriving Repr

def requireSome {A : Type} (reason : Reject) : Option A → Except Reject A
  | none => .error reason
  | some value => .ok value

/-- A prepared renounce over the authority snapshot and the operation marker's
spent answer it read: the answer is "declared, unspent". -/
structure PreparedOn (deployment : Deployment) (semantics : Digest) (ambient : Ambient)
    (authority : Snapshot) (markerSpent : Option Bool) (command : Command) : Type where
  private mk ::
  answered : markerSpent = some false

/-- The preparation over what it reads: the operation marker's spent answer
(`none`: not declared by the request, refused first). Nothing of the named
capability is read before the signature verifies. -/
def prepareOn (deployment : Deployment) (semantics : Digest) (ambient : Ambient)
    (authority : Snapshot) (markerSpent : Option Bool) (command : Command) :
    Except Reject (PreparedOn deployment semantics ambient authority markerSpent command) :=
  match markerSpent with
  | none => .error .undeclaredMarker
  | some true => .error .replayedMarker
  | some false => .ok ⟨rfl⟩

/-- A prepared renounce over a ground (`ServedBasis.Ground`). -/
abbrev Prepared (deployment : Deployment) (semantics : Digest) (ambient : Ambient)
    (ground : Ground deployment) (command : Command) :=
  PreparedOn deployment semantics ambient ground.authority
    (ground.markerSpent (operationMarker ground.authority.domain semantics command)) command

def prepare (deployment : Deployment) (semantics : Digest) (ambient : Ambient)
    (ground : Ground deployment) (command : Command) :
    Except Reject (Prepared deployment semantics ambient ground command) :=
  prepareOn deployment semantics ambient ground.authority
    (ground.markerSpent (operationMarker ground.authority.domain semantics command)) command

/-- **A prepared renounce's marker is unspent** in the ground's authority (on the
light route: the spent map's verified answer for the declared nullifier). -/
theorem Prepared.unspent {deployment : Deployment} {semantics : Digest} {ambient : Ambient}
    {ground : Ground deployment} {command : Command}
    (prepared : Prepared deployment semantics ambient ground command) :
    ground.authority.spent (operationMarker ground.authority.domain semantics command) = false :=
  (ServedBasis.Ground.markerSpent_some ground prepared.answered).symm

/-- The preparation's outcome is a function of the marker's answer alone. -/
theorem prepareOn_map (deployment : Deployment) (semantics : Digest) (ambient : Ambient)
    (authority : Snapshot) (markerSpent : Option Bool) (command : Command) :
    (prepareOn deployment semantics ambient authority markerSpent command).map (fun _ => ()) =
      (match markerSpent with
        | none => .error .undeclaredMarker
        | some true => .error .replayedMarker
        | some false => .ok ()) := by
  cases markerSpent with
  | none => rfl
  | some spent => cases spent <;> rfl

/-- **Agreement**: two grounds with the same answer for the marker prepare alike
(the renounce reads nothing else before its signature verifies). -/
theorem prepare_agrees (deployment : Deployment) (semantics : Digest) (ambient : Ambient)
    (light full : Ground deployment) (command : Command)
    (markers : light.markerSpent (operationMarker light.authority.domain semantics command) =
      full.markerSpent (operationMarker full.authority.domain semantics command)) :
    (prepare deployment semantics ambient light command).map (fun _ => ()) =
      (prepare deployment semantics ambient full command).map (fun _ => ()) := by
  unfold prepare
  rw [prepareOn_map, prepareOn_map, markers]

/-- **An undeclared marker is refused by name**: the preparation's outcome is exactly the
refusal `undeclaredMarker`, whatever the state (the prepared value is a proof-only record,
so its outcome is all there is). -/
theorem prepare_undeclared (deployment : Deployment) (semantics : Digest) (ambient : Ambient)
    {store : DurableHistory.StoreIdentity} (basis : ServedBasis.Basis deployment store) (command : Command)
    (undeclared : CredentialAuthorityReplay.nullifier deployment.domain
        (operationMarker (ServedBasis.Ground.ofBasis basis).authority.domain semantics command) ∉
          basis.keys.nullifiers) :
    (prepare deployment semantics ambient (ServedBasis.Ground.ofBasis basis) command).map (fun _ => ()) =
      .error .undeclaredMarker := by
  unfold prepare
  rw [prepareOn_map, ServedBasis.Ground.markerSpent_undeclared basis _ undeclared]

#assert_axioms Prepared.unspent
#assert_axioms prepare_agrees
#assert_axioms prepare_undeclared

variable {deployment : Deployment} {semantics : Digest} {ambient : Ambient}
  {ground : Ground deployment} {command : Command}

def Prepared.request (prepared : Prepared deployment semantics ambient ground command) :
    Request .program :=
  CapabilityRenounce.request ground.authority semantics ambient command

def Prepared.marker (prepared : Prepared deployment semantics ambient ground command) : Nat :=
  operationMarker ground.authority.domain semantics command

def Prepared.declaration (prepared : Prepared deployment semantics ambient ground command) :
    RevokeDeclaration :=
  CapabilityRenounce.declaration ground.authority.domain semantics
    ground.authority.cell.root command

/-! ## Admission: the signer, then the gate -/

structure Accepted (prepared : Prepared deployment semantics ambient ground command)
    (envelope : List UInt8) where
  private mk ::
  receipt : CredentialSignatureAdmission.CheckedSignature ground.authority
  envelopeExact : receipt.envelopeBytes = envelope
  bound : CredentialSignatureAdmission.verifySignature ground.authority prepared.marker
    prepared.request receipt = true
  victim : Capability command.kind
  gated : Renounce.gateAt ground.authority.cell command.kind command.capability
    command.subject = .ok victim
  validated : ValidatedPatch AuthorityMaterializer ground.authority.cell
    ground.authority.cell.root (prepared.declaration.patch ground.authority.logical)

/-- A gate refusal carries the checked signature that preceded it. It is said
only to the authenticated signer, and it is about the signer's own holding:
`notHolder` (the signer holds no capability at that id), `unregistered`,
`alreadyRevoked`. -/
structure HolderRefusal (prepared : Prepared deployment semantics ambient ground command)
    (envelope : List UInt8) where
  private mk ::
  receipt : CredentialSignatureAdmission.CheckedSignature ground.authority
  envelopeExact : receipt.envelopeBytes = envelope
  bound : CredentialSignatureAdmission.verifySignature ground.authority prepared.marker
    prepared.request receipt = true
  reason : Renounce.Reject
  gated : Renounce.gateAt ground.authority.cell command.kind command.capability
    command.subject = .error reason

inductive Admission (prepared : Prepared deployment semantics ambient ground command)
    (envelope : List UInt8) where
  | accepted (accepted : Accepted prepared envelope)
  /-- After the signature verified: the gate refused, to the signer. -/
  | refusedToHolder (refusal : HolderRefusal prepared envelope)
  /-- Before or outside authentication: never disclosed. -/
  | rejected (reason : Reject)

def admitNative (native : CredentialSignatureIO.NativeConfig)
    (prepared : Prepared deployment semantics ambient ground command) (envelope : List UInt8) :
    IO (Admission prepared envelope) := do
  match ← CredentialSignatureAdmission.verifyNative native ground.authority
      prepared.marker prepared.request envelope with
  | .error reason => return .rejected (.signature reason)
  | .ok receipt =>
    if same : receipt.envelopeBytes = envelope then
      if bound : CredentialSignatureAdmission.verifySignature ground.authority prepared.marker
          prepared.request receipt = true then
        match gated : Renounce.gateAt ground.authority.cell command.kind command.capability
            command.subject with
        | .error reason => return .refusedToHolder ⟨receipt, same, bound, reason, gated⟩
        | .ok victim =>
          match validate AuthorityMaterializer ground.authority.cell
              ground.authority.cell.root
              (prepared.declaration.patch ground.authority.logical) with
          | .rejected _ => return .rejected .validation
          | .accepted validated => return .accepted ⟨receipt, same, bound, victim, gated, validated⟩
      else return .rejected .signatureBinding
    else return .rejected .signatureBinding

/-- The authority cell after the renounce: the validated revocation patch
applied. It is the one authority write. -/
def Accepted.authorityPost {prepared : Prepared deployment semantics ambient ground command}
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

def writes {prepared : Prepared deployment semantics ambient ground command}
    (accepted : Accepted prepared envelope) : List DataWrite :=
  ground.authorityWrites accepted.authorityPost

def readGuards {prepared : Prepared deployment semantics ambient ground command}
    (accepted : Accepted prepared envelope) : List ReadGuard :=
  ground.authorityReadGuards.filter fun guard =>
    guard.cellId ∉ (writes accepted).map DataWrite.cellId

def PhysicalShape {prepared : Prepared deployment semantics ambient ground command}
    (accepted : Accepted prepared envelope) : Prop :=
  ((writes accepted).map DataWrite.cellId).Nodup ∧
    (∀ write ∈ writes accepted, write.expectedPre = ground.view.model.roots write.cellId) ∧
    (∀ write ∈ writes accepted, ResourceBirthController.Concrete.PhysicalPostLaw deployment write) ∧
    (∀ guard ∈ readGuards accepted, guard.expectedRoot = ground.view.model.roots guard.cellId)

instance physicalShapeDecidable {prepared : Prepared deployment semantics ambient ground command}
    (accepted : Accepted prepared envelope) : Decidable (PhysicalShape accepted) := by
  unfold PhysicalShape
  infer_instance

theorem writes_roots_bound {prepared : Prepared deployment semantics ambient ground command}
    (accepted : Accepted prepared envelope) (write : DataWrite) (member : write ∈ writes accepted) :
    rootBytes write.canonicalPostBytes = write.exactPost := by
  simp only [writes, ServedBasis.Ground.authorityWrites, List.mem_singleton] at member
  subst write
  exact ground.authorityWrite_root_bound _

theorem readGuards_readonly {prepared : Prepared deployment semantics ambient ground command}
    (accepted : Accepted prepared envelope) (guard : ReadGuard) (member : guard ∈ readGuards accepted) :
    guard.cellId ∉ (writes accepted).map DataWrite.cellId := by
  simpa using (List.mem_filter.mp member).2

structure AcceptedRenounce (deployment : Deployment) (semantics : Digest) (ambient : Ambient)
    (ground : Ground deployment) (ingress : DecodedIngress) where
  private mk ::
  prepared : Prepared deployment semantics ambient ground ingress.command
  accepted : Accepted prepared ingress.ingress.envelopeBytes
  physical : PhysicalShape accepted

inductive DecodedAdmission (deployment : Deployment) (semantics : Digest) (ambient : Ambient)
    (ground : Ground deployment) (ingress : DecodedIngress) where
  | accepted (accepted : AcceptedRenounce deployment semantics ambient ground ingress)
  | refusedToHolder {prepared : Prepared deployment semantics ambient ground ingress.command}
      (refusal : HolderRefusal prepared ingress.ingress.envelopeBytes)
  | rejected (reason : Reject)

def admitDecodedNative (deployment : Deployment) (semantics : Digest) (ambient : Ambient)
    (ground : Ground deployment) (native : CredentialSignatureIO.NativeConfig) (ingress : DecodedIngress) :
    IO (DecodedAdmission deployment semantics ambient ground ingress) := do
  match prepare deployment semantics ambient ground ingress.command with
  | .error reason => return .rejected reason
  | .ok prepared =>
    match ← admitNative native prepared ingress.ingress.envelopeBytes with
    | .rejected reason => return .rejected reason
    | .refusedToHolder refusal => return .refusedToHolder refusal
    | .accepted accepted =>
      if physical : PhysicalShape accepted then return .accepted ⟨prepared, accepted, physical⟩
      else return .rejected .physicalPreparation

variable {ingress : DecodedIngress}

def charge (accepted : AcceptedRenounce deployment semantics ambient ground ingress) :
    ResourceCost.Charge
  | .incidences => 1
  | .turnBytes => ingress.bytes.length
  | .memoryTouches => (writes accepted.accepted).length + (readGuards accepted.accepted).length
  | .storageBytes => ((writes accepted.accepted).map fun write => write.canonicalPostBytes.length).sum
  | .witnessBytes => ingress.ingress.envelopeBytes.length
  | .proofWork => 1
  | .feeDebit | .networkBytes | .sideEffectCount | .leaseByteBlocks => 0

def intent (accepted : AcceptedRenounce deployment semantics ambient ground ingress) :
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

/-- The keys a renounce consults beyond the state: its transaction id (the replay
lookup) and its marker's replay nullifier (the spent check). -/
def keys (domain semantics : Digest) (ingress : DecodedIngress) : DurableView.Keys :=
  ⟨[transactionId domain semantics ingress], [nullifier domain semantics ingress]⟩

/-- The recorded intent under this renounce's transaction id is exactly its own. -/
def exactRecord (domain semantics : Digest) (ingress : DecodedIngress)
    (recorded : DurableCommitProtocol.Intent Digest Digest StableNullifier ReplayEnvelope) : Bool :=
  decide (recorded.transactionId = transactionId domain semantics ingress ∧
    recorded.event.event = event domain semantics ingress ∧
    recorded.nullifiers = [nullifier domain semantics ingress])

/-- The replay verdict on a ground, read only through its answer for the
transaction id (`ServedBasis.Ground.replayOf`): an undeclared id is `undeclared`. -/
def replay (domain semantics : Digest) (ground : Ground deployment) (ingress : DecodedIngress) :
    ServedBasis.Ground.Replay Receipt :=
  ground.replayOf (transactionId domain semantics ingress) (exactRecord domain semantics ingress)
    (receipt domain semantics ingress)

/-- An exact retry returns the original receipt and nothing else. -/
theorem replay_only_original (domain semantics : Digest) (ground : Ground deployment) (ingress : DecodedIngress)
    (result : Receipt) (accepted : replay domain semantics ground ingress = .original result) :
    result = receipt domain semantics ingress ∧
      ∃ recorded,
        DurableCommitProtocol.Snapshot.lookupRecorded (transactionId domain semantics ingress)
          ground.view.model.journal = some recorded ∧
        recorded.event.event = event domain semantics ingress ∧
        recorded.nullifiers = [nullifier domain semantics ingress] := by
  obtain ⟨same, recorded, found, isExact⟩ := ServedBasis.Ground.replayOf_original ground _ _ _ result accepted
  simp only [exactRecord, decide_eq_true_eq] at isExact
  exact ⟨same, recorded, found, isExact.2⟩

/-- **An undeclared transaction id is refused by name**: never "not recorded". -/
theorem replay_undeclared (domain semantics : Digest) {store : DurableHistory.StoreIdentity}
    (basis : ServedBasis.Basis deployment store) (ingress : DecodedIngress)
    (undeclared : transactionId domain semantics ingress ∉ basis.keys.transactions) :
    replay domain semantics (ServedBasis.Ground.ofBasis basis) ingress = .undeclared :=
  ServedBasis.Ground.replayOf_undeclared basis _ _ _ undeclared

#assert_axioms replay_undeclared

/-- A refusal disclosed to the holder was produced after a checked signature
over exactly this renounce's request, whose subject is the command's signer. -/
theorem HolderRefusal.signer_authenticated
    {prepared : Prepared deployment semantics ambient ground command} {envelope : List UInt8}
    (refusal : HolderRefusal prepared envelope) :
    refusal.receipt.request = ⟨.program, prepared.request⟩ ∧
      prepared.request.subject = command.subject ∧ refusal.receipt.envelopeBytes = envelope :=
  ⟨(CredentialSignatureAdmission.verified_request_exact _ _ _ _ refusal.bound).1, rfl,
    refusal.envelopeExact⟩

/-- info: 'Minidregg.Kernel.CapabilityRenounce.HolderRefusal.signer_authenticated' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms HolderRefusal.signer_authenticated

#assert_axioms replay_only_original

end Minidregg.Kernel.CapabilityRenounce
