/-
# Compiler.CredentialSignatureAdmission — native signatures from one authority snapshot

The complete authority snapshot selects the current committed key. Lean
derives the singleton key projection, authority root, authority clock,
canonical seventeen-field request and shared operation nullifier. The existing
SignedEnvelope controller checks canonical framing, key identity/epoch,
revocation, activation and replay before the native verifier sees bytes.

`CheckedSignature` has a private constructor and no wire decoder. Its only
producer calls the configured Ed25519 verifier and the existing controller's
finish step. Pure policy/capability admission can compare this receipt to the
exact request; a caller cannot submit an arbitrary positive verification bit.

Verification does not persist the controller's standalone nextStateBytes.
The enclosing source-owned authority effect consumes the expected nullifier
ONCE with the whole hyperedge, under the same old authority snapshot guards.
All its incidences may bind that one marker. Native implementation/transport
and cryptographic custody assumptions remain explicit; the receipt is not a
Lean proof of Ed25519 or physical commit.
-/
import Compiler.CredentialSignatureIO
import Compiler.CredentialAuthorityDomain
import Compiler.TypedAuthorizationRequestCodec
import Compiler.ResourceBirthCodec
import Compiler.PlanFootprintCodec
import Theory.Receiving

namespace Minidregg.Compiler.CredentialSignatureAdmission

open Minidregg.Theory
open Minidregg.Theory.IndexedProgram
open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.AuthorizationDeclaration
open Minidregg.Theory.CredentialSigningKey
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Compiler.CredentialAuthorityDomain

open Minidregg.Kernel

set_option autoImplicit false

/-- Source-pinned algorithm code for this receiving adapter. -/
def ed25519Algorithm : Nat := 1

def signatureDomain : List UInt8 := "DREGG/AUTH/SIGNED-REQUEST".toUTF8.toList ++ [2]
abbrev requestFrame := TypedAuthorizationRequestCodec.requestFrame

/-- Canonical ingress uses the existing signed-envelope parser and encoding.
The legacy stream remains useful inside a source-owned ordered bundle, whose
whole-message decoder must likewise enforce exact re-encoding. Parsing a
canonical envelope alone does not authenticate it or mint a receipt. -/
def canonicalEnvelopeCodec : LawfulCodec CredentialSignedEnvelopeController.SignedEnvelope :=
  ResourceBirthCodec.strictCodec CredentialSignedEnvelopeController.envelopeCodec

theorem canonicalEnvelopeCodec_accepted_bytes
    {bytes : List UInt8} {envelope : CredentialSignedEnvelopeController.SignedEnvelope}
    (accepted : canonicalEnvelopeCodec.decode bytes = some envelope) :
    canonicalEnvelopeCodec.encode envelope = bytes :=
  ResourceBirthCodec.strictCodec_canonical CredentialSignedEnvelopeController.envelopeCodec accepted

/-- Signing uses the sole complete kind-indexed codec. No second projection of
request fields exists in the native signature adapter. -/
abbrev requestBytes := TypedAuthorizationRequestCodec.signedRequestBytes

theorem requestWords_injective : Function.Injective TypedAuthorizationRequestCodec.requestWords :=
  TypedAuthorizationRequestCodec.requestWords_injective

/-- The native adapter signs precisely the sole source-owned plan projection
of the request, for every kind and every request; source revision is never
defaulted. -/
theorem requestBytes_exact_projection (request : SomeRequest) :
    requestBytes request = requestFrame ++
      (StreamCodec.list StreamCodec.nat).encode
        (TypedAuthorizationRequestCodec.requestWords
          (encodeRequest (TypedAuthorizationRequestCodec.planOf request))) := rfl

theorem requestBytes_separates_policyRevision {kind : ResourceKind}
    (request : Request kind) (revision : Nat) (different : request.policyRevision ≠ revision) :
    requestBytes ⟨kind, request⟩ ≠ requestBytes ⟨kind, { request with policyRevision := revision }⟩ := by
  intro same
  have samePlan := (TypedAuthorizationRequestCodec.signedRequestBytes_eq_iff _ _).1 same
  have sameWire := congrArg encodeRequest samePlan
  exact different (congrArg RequestWire.policyRevision sameWire)

inductive Reject where
  | wrongDomain
  | missingCurrentKey
  | subjectKeyEpoch
  /-- The selected key version is not in the cell's `registered` plane. -/
  | unregisteredKey
  /-- The selected key version is in the cell's `revoked` plane. -/
  | revokedKey
  | unsupportedAlgorithm
  | publicKeyLength
  | envelope (reason : CredentialSignedEnvelopeController.Failure CredentialSignatureIO.Error)
  | sourceBinding
  /-- The signed footprint does not decode as authority reads. -/
  | malformedFootprint
  /-- A value this plan read in the authority cell has changed since it was
  signed; `address` is the canonical bytes of the first such address. -/
  | footprintStale (address : List UInt8)
  /-- The admission height is past the plan's signed `validUntil`. -/
  | expired (height validUntil : Nat)
  /-- The Receiver issued no voucher for the claim the envelope admission
  selected (`CheckedSignature.ofReceiverClaim`): that signature was not verified. -/
  | unvouched
  deriving DecidableEq, Repr

/-- Selection is a read of the canonical authority schema, never a host key
map. Missing epoch or record refuses, including an absent "epoch zero". -/
structure Selected (snapshot : Snapshot) (request : SomeRequest) where
  key : KeyRecord
  selected : CredentialAuthorityState.currentSigningKey snapshot.logical
    request.2.subject = some key
  epochCurrent : request.2.subjectKeyEpoch = snapshot.authState.subjectKeyEpoch request.2.subject
  epochExact : key.keyEpoch = request.2.subjectKeyEpoch
  /-- The signer check: the selected key version is registered and not
  revoked, read by `CredentialAuthorityState.keyStanding` -- the same function
  the settlement model's `CurrentSigner.standing` states. -/
  standing : CredentialAuthorityState.keyStanding snapshot.cell
    (CredentialAuthorityState.signingKeyRevocation key) = .live
  domainExact : request.2.domain = snapshot.domain
  algorithmExact : key.algorithm = ed25519Algorithm
  keyLength : key.publicKey.length = 32

def select (snapshot : Snapshot) (request : SomeRequest) : Except Reject (Selected snapshot request) :=
  if domainExact : request.2.domain = snapshot.domain then
    match selected : CredentialAuthorityState.currentSigningKey snapshot.logical request.2.subject with
    | none => .error .missingCurrentKey
    | some key =>
        if epochCurrent : request.2.subjectKeyEpoch =
            snapshot.authState.subjectKeyEpoch request.2.subject then
          if epochExact : key.keyEpoch = request.2.subjectKeyEpoch then
            match standing : CredentialAuthorityState.keyStanding snapshot.cell
                (CredentialAuthorityState.signingKeyRevocation key) with
            | .unregistered => .error .unregisteredKey
            | .revoked => .error .revokedKey
            | .live =>
              if algorithmExact : key.algorithm = ed25519Algorithm then
                if keyLength : key.publicKey.length = 32 then
                  .ok ⟨key, selected, epochCurrent, epochExact, standing, domainExact,
                    algorithmExact, keyLength⟩
                else .error .publicKeyLength
              else .error .unsupportedAlgorithm
          else .error .subjectKeyEpoch
        else .error .subjectKeyEpoch
  else .error .wrongDomain

/-! ## The plan's authority footprint

A signature binds the values its admission reads in the authority cell, not the
cell's root (`Theory.PlanBinding`).  Signature admission reads exactly the
subject's current key epoch, the key record at that epoch, and that key
version's standing (`CredentialAuthorityState.keyStanding`: its `registered`
and `revoked` presence entries) (`select`); those four addresses, at the values
they held when the plan was signed, are the footprint.  Another agent's
admission consumes its own nullifier in the durable set (never the cell), and
enrolls, registers or rotates only its own key, so it moves none of these
addresses and leaves this plan admissible.  Policy epoch and revision are request fields, and the capability
check runs at admission against the current cell (check equals use). -/

open Minidregg.Theory.PlanBinding in
def footprintAddresses (subject : SubjectId) (epoch : Epoch) :
    List (Store.Address CredentialAuthorityState.layout) :=
  [⟨.subjectKeyEpoch, subject⟩, ⟨.subjectKey, (subject, epoch)⟩,
    ⟨.registered, .signingKey subject epoch⟩, ⟨.revoked, .signingKey subject epoch⟩]

open Minidregg.Theory.PlanBinding in
def footprint (snapshot : Snapshot) (request : SomeRequest) :
    Footprint CredentialAuthorityState.layout :=
  Footprint.observe snapshot.logical
    (footprintAddresses request.2.subject request.2.subjectKeyEpoch)

def footprintBytes (snapshot : Snapshot) (request : SomeRequest) : List UInt8 :=
  PlanFootprintCodec.encode CredentialAuthorityCell.wire (footprint snapshot request)

/-- How long a signed plan stays admissible, in admitted turns after the height
it was authored at.  A deployment pin; replay is the nullifier's job, not this. -/
def planValidityWindow : Nat := 256

/-- The activation epoch is the authority clock (`Snapshot.revision`): the
durable height the snapshot was loaded at
(`CredentialAuthorityDomainReceiver.Loaded.revisionExact`). It never runs
backwards and every accepted record advances it
(`CredentialAuthorityDomainReceiver.clockOf_install`); it is not a subject
epoch.  It is checked at admission against the current snapshot and is not
signed. -/
def keyRegistry (snapshot : Snapshot) (key : KeyRecord) : CredentialSignedEnvelopeController.KeyRegistryProjection where
  codecVersion := CredentialSignedEnvelopeController.registryCodecVersion
  authorityRoot := snapshot.cell.root
  registryEpoch := snapshot.revision
  keys := [key]

def controllerState (snapshot : Snapshot) (key : KeyRecord) (nullifier : Nat)
    (request : SomeRequest) : CredentialSignedEnvelopeController.ControllerState where
  codecVersion := CredentialSignedEnvelopeController.stateCodecVersion
  authorityRoot := snapshot.cell.root
  registryCommitment := CredentialSignedEnvelopeController.registryDigest
    (CredentialSignedEnvelopeController.registryCodec.encode (keyRegistry snapshot key))
  registryEpoch := snapshot.revision
  footprint := footprintBytes snapshot request
  height := request.2.height
  consumedNullifiers :=
    if snapshot.spent nullifier then [nullifier] else []

/-- The signed header.  It names the plan's authority footprint and the height
it is valid until; it names no authority root, registry commitment or
authority clock, so an unrelated admission does not invalidate it. -/
def header (snapshot : Snapshot) (key : KeyRecord) (nullifier : Nat)
    (request : SomeRequest) (validUntil : Nat) : CredentialSignedEnvelopeController.SignedHeader where
  codecVersion := CredentialSignedEnvelopeController.envelopeCodecVersion
  footprint := footprintBytes snapshot request
  validUntil := validUntil
  keyId := key.keyId
  keyEpoch := key.keyEpoch
  algorithm := ed25519Algorithm
  domain := signatureDomain
  message := requestBytes request
  nullifier := nullifier

/-- Client preparation exposes only the exact source-derived bytes to sign;
it does not construct a checked signature or choose an independent key.  The
plan is valid for `planValidityWindow` turns after the authoring height. -/
def signingHeader (snapshot : Snapshot) (nullifier : Nat) (request : SomeRequest) :
    Except Reject CredentialSignedEnvelopeController.SignedHeader := do
  let selected ← select snapshot request
  .ok (header snapshot selected.key nullifier request (request.2.height + planValidityWindow))

open Minidregg.Theory.PlanBinding in
/-- Name the staleness before the controller's byte comparison: decode the
signed footprint and check it against the current authority cell.  A plan whose
reads all still hold passes; one whose read moved is refused naming it. -/
def checkFootprint (snapshot : Snapshot) (envelopeBytes : List UInt8) : Except Reject Unit :=
  match CredentialSignedEnvelopeController.envelopeCodec.decode envelopeBytes with
  | none => .ok ()
  | some envelope =>
      match PlanFootprintCodec.decode CredentialAuthorityCell.wire envelope.header.footprint with
      | none => .error .malformedFootprint
      | some signed =>
          match Footprint.admit snapshot.logical signed with
          | .ok () => .ok ()
          | .error (.footprintStale address) =>
              .error (.footprintStale (PlanFootprintCodec.addressBytes CredentialAuthorityCell.wire address))

structure Prepared (snapshot : Snapshot) (nullifier : Nat) (request : SomeRequest) where
  source : Selected snapshot request
  controller : CredentialSignedEnvelopeController.Prepared
  keyExact : controller.key = source.key
  headerExact : controller.envelope.header =
    header snapshot source.key nullifier request controller.envelope.header.validUntil

/-- The parser and all envelope admission decisions remain in the existing
controller. The additional equality pins its result to this source snapshot
and the enclosing operation's exact shared nullifier. -/
def prepare (snapshot : Snapshot) (nullifier : Nat) (request : SomeRequest)
    (envelopeBytes : List UInt8) : Except Reject (Prepared snapshot nullifier request) := do
  let source ← select snapshot request
  checkFootprint snapshot envelopeBytes
  match CredentialSignedEnvelopeController.prepare (NativeError := CredentialSignatureIO.Error) request.2.subject.value
      signatureDomain (requestBytes request)
      (CredentialSignedEnvelopeController.stateCodec.encode (controllerState snapshot source.key nullifier request))
      (CredentialSignedEnvelopeController.registryCodec.encode (keyRegistry snapshot source.key)) envelopeBytes with
  | .error .expired => .error (.expired request.2.height (match
      CredentialSignedEnvelopeController.envelopeCodec.decode envelopeBytes with
      | some envelope => envelope.header.validUntil
      | none => 0))
  | .error reason => .error (.envelope reason)
  | .ok controller =>
      if keyExact : controller.key = source.key then
        if headerExact : controller.envelope.header =
            header snapshot source.key nullifier request controller.envelope.header.validUntil then
          .ok ⟨source, controller, keyExact, headerExact⟩
        else .error .sourceBinding
      else .error .sourceBinding

/-- The constructor is module-private. There is no positive-result decoder,
test receipt constructor, arbitrary verifier callback or pure mint function. The
verdict is the configured verifier's, and the receipt keeps that config
(`verifier`): the pinned native process, or -- only in a Lean fixture that evaluates
a real admission -- a recorded run of that process
(`CredentialSignatureIO.Transcript`), which `scripts/check-native-transcripts.sh`
re-submits to it.  **Layer 2**: the verdict is the oracle's, a runtime fact; `private
mk` stops names but not `by constructor`, so the guarantee that only `verifyNative`
and `ofReceiverClaim` mint a receipt is `TokenCensus` (no foreign mint, a planted
forgery detected). -/
structure CheckedSignature (snapshot : Snapshot) where
  private mk ::
  /-- The oracle that answered the signature check: the pinned process, or (only
  in a pure evaluation) a recorded run of it (`CredentialSignatureIO.Oracle`). -/
  source : CredentialSignatureIO.Source
  request : SomeRequest
  nullifier : Nat
  envelopeBytes : List UInt8
  prepared : Prepared snapshot nullifier request
  preparedFrom : prepare snapshot nullifier request envelopeBytes = .ok prepared
  admission : CredentialSignedEnvelopeController.Admission
  admitted : CredentialSignedEnvelopeController.finish prepared.controller (Except.ok true : Except CredentialSignatureIO.Error Bool) =
    .ok admission

def verifyNative {m : Type → Type} [Monad m] (config : CredentialSignatureIO.Oracle m) (snapshot : Snapshot) (nullifier : Nat)
    {kind : ResourceKind} (request : Request kind) (envelopeBytes : List UInt8) :
    m (Except Reject (CheckedSignature snapshot)) := do
  match preparation : prepare snapshot nullifier ⟨kind, request⟩ envelopeBytes with
  | .error reason => return .error reason
  | .ok prepared =>
      match ← config.check prepared.controller.key.publicKey prepared.controller.frame
          prepared.controller.envelope.signature with
      | .error error => return .error (.envelope (.nativeVerify error))
      | .ok false => return .error (.envelope .invalidSignature)
      | .ok true =>
          match admitted : CredentialSignedEnvelopeController.finish prepared.controller
              (Except.ok true : Except CredentialSignatureIO.Error Bool) with
          | .error reason => return .error (.envelope reason)
          | .ok admission =>
              return .ok ⟨config.source, ⟨kind, request⟩, nullifier, envelopeBytes,
                prepared, preparation, admission, admitted⟩

/-! ## The Receiver's verdict as a receipt

A `Kernel.Receiving` family's signature claims are verified by the Receiver
BEFORE its `prepare` runs (`Theory.Receiving.Receiver.admitVia`); `prepare`
receives the accepted claims as `Theory.Receiving.Vouchers` of the Receiver's
verifier.  `receiverVerify` is that verifier over a `CredentialSignatureIO.Oracle`
-- the same closed family of oracles `verifyNative` takes, so at `IO` the
verdict is the pinned process's (`Oracle.io_process`).  `ReceiverSignature` and
`CheckedSignature.ofReceiverClaim` turn a voucher into a value a gate can hold;
neither can be built without one. -/

open Minidregg.Theory.Receiving (SigQuery Vouchers)

/-- **The Receiver's verifier over one oracle**: the oracle's verdict on the
claim's exact key, message and signature, its error printed. -/
def receiverVerify : {m : Type → Type} → CredentialSignatureIO.Oracle m → SigQuery →
    m (Except String Bool)
  | _, .live config, claim => do
      let answer ← match claim.scheme with
        | .ed25519 => CredentialSignatureIO.verify config claim.publicKey claim.message claim.signature
        | .sshsig nameSpace =>
          CredentialSignatureIO.verifySshsig config claim.publicKey nameSpace claim.message claim.signature
      match answer with
      | .error reason => pure (.error s!"{repr reason}")
      | .ok verdict => pure (.ok verdict)
  | _, .recorded transcript, claim =>
      (match claim.scheme with
        | .sshsig _ => .error "a recorded transcript holds Ed25519 verdicts only"
        | .ed25519 =>
          match CredentialSignatureIO.recordedVerdict transcript claim.publicKey claim.message
              claim.signature with
          | .error reason => .error s!"{repr reason}"
          | .ok verdict => .ok verdict : Except String Bool)

/-- **What a family's `prepare` receives from the Receiver**: the oracle that
answered and the vouchers of the claims it accepted, typed by that oracle's
verifier. -/
structure Received where
  {m : Type → Type}
  oracle : CredentialSignatureIO.Oracle m
  vouchers : Vouchers (receiverVerify oracle)

/-- A signature the Receiver's verifier accepted before `prepare` ran: the
exact claim, and the oracle that answered (`Source.receiver`).  The constructor
is private; the only producers read a voucher (`Received.find?`,
`Received.signed?`).  **Layer 2**, protected by `TokenCensus`.  It is a `Type`-level value a `Prepared` record can hold,
where the `Received` bundle (indexed by the oracle's monad) cannot be. -/
structure ReceiverSignature where
  private mk ::
  source : CredentialSignatureIO.Source
  claim : SigQuery

namespace Received

/-- The Receiver's signature for exactly `claim`, if it vouched for it. -/
def find? (received : Received) (claim : SigQuery) : Option ReceiverSignature :=
  if received.vouchers.vouches claim then some ⟨.receiver received.oracle.source, claim⟩ else none

/-- The Receiver's Ed25519 signature by `publicKey` over `message`, if it vouched for one. -/
def signed? (received : Received) (publicKey message : List UInt8) : Option ReceiverSignature :=
  (received.vouchers.signed? .ed25519 publicKey message).map fun claim =>
    ⟨.receiver received.oracle.source, claim⟩

theorem find?_some {received : Received} {claim : SigQuery} {signature : ReceiverSignature}
    (found : received.find? claim = some signature) :
    claim ∈ received.vouchers.verified ∧ signature.claim = claim ∧
      signature.source = .receiver received.oracle.source := by
  unfold find? at found
  split at found
  · rename_i vouched
    cases found
    exact ⟨(Vouchers.vouches_iff _ _).1 vouched, rfl, rfl⟩
  · cases found

theorem signed?_some {received : Received} {publicKey message : List UInt8}
    {signature : ReceiverSignature} (found : received.signed? publicKey message = some signature) :
    signature.claim ∈ received.vouchers.verified ∧ signature.claim.scheme = .ed25519 ∧
      signature.claim.publicKey = publicKey ∧
      signature.claim.message = message ∧ signature.source = .receiver received.oracle.source := by
  unfold signed? at found
  cases vouched : received.vouchers.signed? .ed25519 publicKey message with
  | none => rw [vouched] at found; cases found
  | some claim =>
      rw [vouched] at found
      cases found
      obtain ⟨member, scheme, key, frame⟩ := Vouchers.signed?_some vouched
      exact ⟨member, scheme, key, frame, rfl⟩

end Received

/-- The claim the envelope admission's native check is about: the selected key,
the controller's frame (the encoded signed header) and the envelope's signature
-- exactly what `verifyNative` hands the oracle. -/
def controllerClaim (controller : CredentialSignedEnvelopeController.Prepared) : SigQuery :=
  ⟨.ed25519, controller.key.publicKey, controller.frame, controller.envelope.signature⟩

/-- **The claim the Receiver verifies for a signed envelope by `subject`**,
before any preparation: the subject's current key (a key lookup), the envelope's
own header frame and its signature.  It reads no plan and re-executes nothing.
`ofReceiverClaim` later looks up `controllerClaim` of the envelope admission,
which selects the same current key and decodes the same envelope; if the two
ever differ, the lookup misses and the receipt is refused (`unvouched`). -/
def envelopeClaim (snapshot : Snapshot) (subject : SubjectId) (envelopeBytes : List UInt8) :
    Except Reject SigQuery :=
  match CredentialAuthorityState.currentSigningKey snapshot.logical subject with
  | none => .error .missingCurrentKey
  | some key =>
      match CredentialSignedEnvelopeController.envelopeCodec.decode envelopeBytes with
      | none => .error (.envelope .malformedEnvelope)
      | some envelope => .ok ⟨.ed25519, key.publicKey, envelope.frame, envelope.signature⟩

/-- **A checked signature from the Receiver's verdict.**  The envelope admission
runs exactly as in `verifyNative` (`prepare`: key selection, footprint, the
controller's framing, staleness and replay checks, the source binding); the
native call is replaced by the Receiver's voucher for exactly the claim that call
would make (`controllerClaim`).  No voucher, no receipt: `unvouched`. -/
def CheckedSignature.ofReceiverClaim (received : Received) (snapshot : Snapshot) (nullifier : Nat)
    {kind : ResourceKind} (request : Request kind) (envelopeBytes : List UInt8) :
    Except Reject (CheckedSignature snapshot) :=
  match preparation : prepare snapshot nullifier ⟨kind, request⟩ envelopeBytes with
  | .error reason => .error reason
  | .ok prepared =>
      match received.find? (controllerClaim prepared.controller) with
      | none => .error .unvouched
      | some signature =>
          match admitted : CredentialSignedEnvelopeController.finish prepared.controller
              (Except.ok true : Except CredentialSignatureIO.Error Bool) with
          | .error reason => .error (.envelope reason)
          | .ok admission =>
              .ok ⟨signature.source, ⟨kind, request⟩, nullifier, envelopeBytes, prepared,
                preparation, admission, admitted⟩

/-- **A receipt from the Receiver is a vouched one**: the claim its envelope
admission checked is among the Receiver's vouchers, and the receipt records that
the Receiver's oracle answered it. -/
theorem CheckedSignature.ofReceiverClaim_vouched {received : Received} {snapshot : Snapshot}
    {nullifier : Nat} {kind : ResourceKind} {request : Request kind} {envelopeBytes : List UInt8}
    {receipt : CheckedSignature snapshot}
    (checked : CheckedSignature.ofReceiverClaim received snapshot nullifier request envelopeBytes =
      .ok receipt) :
    controllerClaim receipt.prepared.controller ∈ received.vouchers.verified ∧
      receipt.source = .receiver received.oracle.source ∧
      receipt.request = ⟨kind, request⟩ ∧ receipt.nullifier = nullifier ∧
      receipt.envelopeBytes = envelopeBytes := by
  unfold CheckedSignature.ofReceiverClaim at checked
  split at checked
  · cases checked
  · rename_i prepared _
    split at checked
    · cases checked
    · rename_i signature found
      split at checked
      · cases checked
      · cases checked
        obtain ⟨member, -, source⟩ := Received.find?_some found
        exact ⟨member, source, rfl, rfl, rfl⟩

/-- **No voucher, no receipt**: if the Receiver did not vouch for the claim the
envelope admission selected, `ofReceiverClaim` refuses. -/
theorem CheckedSignature.ofReceiverClaim_unvouched {received : Received} {snapshot : Snapshot}
    {nullifier : Nat} {kind : ResourceKind} {request : Request kind} {envelopeBytes : List UInt8}
    {prepared : Prepared snapshot nullifier ⟨kind, request⟩}
    (preparation : prepare snapshot nullifier ⟨kind, request⟩ envelopeBytes = .ok prepared)
    (missing : controllerClaim prepared.controller ∉ received.vouchers.verified) :
    CheckedSignature.ofReceiverClaim received snapshot nullifier request envelopeBytes =
      .error .unvouched := by
  have none_ : received.find? (controllerClaim prepared.controller) = none := by
    unfold Received.find?
    rw [if_neg (by rw [Vouchers.vouches_iff]; exact missing)]
  unfold CheckedSignature.ofReceiverClaim
  split
  · rename_i reason failed
    rw [preparation] at failed; cases failed
  · rename_i prepared' found
    rw [preparation] at found
    cases found
    rw [none_]

/-- The pure portal can use a native receipt only for its exact complete
request and the same operation marker. Snapshot selection is a type index. -/
def verifySignature (snapshot : Snapshot) (expectedNullifier : Nat)
    {kind : ResourceKind} (request : Request kind) (receipt : CheckedSignature snapshot) : Bool :=
  decide (encodeRequest receipt.request = encodeRequest ⟨kind, request⟩ ∧
    receipt.nullifier = expectedNullifier)

theorem verified_request_exact (snapshot : Snapshot) (expectedNullifier : Nat)
    {kind : ResourceKind} (request : Request kind) (receipt : CheckedSignature snapshot)
    (verified : verifySignature snapshot expectedNullifier request receipt = true) :
    receipt.request = ⟨kind, request⟩ ∧ receipt.nullifier = expectedNullifier := by
  have binding : encodeRequest receipt.request = encodeRequest ⟨kind, request⟩ ∧
      receipt.nullifier = expectedNullifier := of_decide_eq_true verified
  constructor
  · have decoded := congrArg decodeRequest binding.1
    rw [decodeRequest_encodeRequest, decodeRequest_encodeRequest] at decoded
    exact Option.some.inj decoded
  · exact binding.2

theorem checked_key_from_same_snapshot (snapshot : Snapshot) (receipt : CheckedSignature snapshot) :
    CredentialAuthorityState.currentSigningKey snapshot.logical receipt.request.2.subject =
      some receipt.prepared.controller.key := by
  rw [receipt.prepared.keyExact]
  exact receipt.prepared.source.selected

theorem checked_frame_exact (snapshot : Snapshot) (receipt : CheckedSignature snapshot) :
    receipt.prepared.controller.frame = CredentialSignedEnvelopeController.headerCodec.encode
      (header snapshot receipt.prepared.source.key receipt.nullifier receipt.request
        receipt.prepared.controller.envelope.header.validUntil) := by
  rw [receipt.prepared.controller.frameExact]
  exact congrArg CredentialSignedEnvelopeController.headerCodec.encode receipt.prepared.headerExact

/-- Explicit IO-to-verifier refinement obligation for ACTUAL execution,
including the pinned executable and exact process/filesystem byte transport.
`Returned` denotes that physical execution relation; a structurally available
receipt alone is not its proof. No relation or instance is asserted here.
The existing controller separately requires cryptographic refinement and
EUF-CMA/key-custody assumptions. -/
structure NativeIORefinement
    (config : CredentialSignatureIO.NativeConfig)
    (Returned : CredentialSignatureIO.NativeConfig → List UInt8 → List UInt8 → List UInt8 →
      Except CredentialSignatureIO.Error Bool → Prop)
    (verify : CredentialSignedEnvelopeController.OpaqueVerifier CredentialSignatureIO.Error) : Prop where
  exactResult : ∀ publicKey frame signature result,
    Returned config publicKey frame signature result → verify publicKey frame signature = result

theorem issued_of_checked
    {config : CredentialSignatureIO.NativeConfig}
    {Returned : CredentialSignatureIO.NativeConfig → List UInt8 → List UInt8 → List UInt8 →
      Except CredentialSignatureIO.Error Bool → Prop}
    {verify : CredentialSignedEnvelopeController.OpaqueVerifier CredentialSignatureIO.Error}
    {Authenticates : List UInt8 → List UInt8 → List UInt8 → Prop}
    {SignerIssued : Nat → Nat → List UInt8 → List UInt8 → Prop}
    (ioRefinement : NativeIORefinement config Returned verify)
    (completion : CredentialSignedEnvelopeController.SignatureCompletion
      verify Authenticates SignerIssued)
    (snapshot : Snapshot) (receipt : CheckedSignature snapshot)
    (observed : Returned config receipt.prepared.controller.key.publicKey
      receipt.prepared.controller.frame receipt.prepared.controller.envelope.signature (.ok true)) :
    SignerIssued receipt.prepared.controller.key.keyId receipt.prepared.controller.key.keyEpoch
      receipt.prepared.controller.frame receipt.prepared.controller.envelope.signature :=
  completion.issued_of_verified receipt.prepared.controller
    (ioRefinement.exactResult _ _ _ _ observed)

/-- **Signer check, refuting pole.**  Whatever the envelope, a request whose
current key version the cell has not registered is refused by selection, before
any envelope decode or native verification. -/
theorem select_unregistered_refused (snapshot : Snapshot) (request : SomeRequest)
    (key : KeyRecord)
    (domainExact : request.2.domain = snapshot.domain)
    (current : CredentialAuthorityState.currentSigningKey snapshot.logical request.2.subject = some key)
    (epochCurrent : request.2.subjectKeyEpoch = snapshot.authState.subjectKeyEpoch request.2.subject)
    (epochExact : key.keyEpoch = request.2.subjectKeyEpoch)
    (unregistered : CredentialAuthorityState.keyStanding snapshot.cell
      (CredentialAuthorityState.signingKeyRevocation key) = .unregistered) :
    select snapshot request = .error .unregisteredKey := by
  unfold select
  rw [dif_pos domainExact]
  split
  · rename_i none; rw [current] at none; cases none
  · rename_i selectedKey selected
    rw [current] at selected
    cases selected
    rw [dif_pos epochCurrent, dif_pos epochExact]
    split <;> simp_all

/-- **Signer check, refuting pole.**  A revoked current key version is refused. -/
theorem select_revoked_refused (snapshot : Snapshot) (request : SomeRequest)
    (key : KeyRecord)
    (domainExact : request.2.domain = snapshot.domain)
    (current : CredentialAuthorityState.currentSigningKey snapshot.logical request.2.subject = some key)
    (epochCurrent : request.2.subjectKeyEpoch = snapshot.authState.subjectKeyEpoch request.2.subject)
    (epochExact : key.keyEpoch = request.2.subjectKeyEpoch)
    (revoked : CredentialAuthorityState.isRevoked snapshot.cell
      (CredentialAuthorityState.signingKeyRevocation key) = true) :
    select snapshot request = .error .revokedKey := by
  have standing := CredentialAuthorityState.keyStanding_revoked snapshot.cell _ revoked
  unfold select
  rw [dif_pos domainExact]
  split
  · rename_i none; rw [current] at none; cases none
  · rename_i selectedKey selected
    rw [current] at selected
    cases selected
    rw [dif_pos epochCurrent, dif_pos epochExact]
    split <;> simp_all

/-- **Signer check, sound pole.**  Every checked signature's key version is
registered and live in the exact snapshot cell. -/
theorem checked_signer_live (snapshot : Snapshot) (receipt : CheckedSignature snapshot) :
    CredentialAuthorityState.isRegistered snapshot.cell
        (CredentialAuthorityState.signingKeyRevocation receipt.prepared.controller.key) = true ∧
      CredentialAuthorityState.isRevoked snapshot.cell
        (CredentialAuthorityState.signingKeyRevocation receipt.prepared.controller.key) = false := by
  rw [receipt.prepared.keyExact]
  exact (CredentialAuthorityState.keyStanding_live_iff _ _).mp receipt.prepared.source.standing

#assert_axioms Received.find?_some
#assert_axioms Received.signed?_some
#assert_axioms CheckedSignature.ofReceiverClaim_vouched
#assert_axioms CheckedSignature.ofReceiverClaim_unvouched

/-- info: 'Minidregg.Compiler.CredentialSignatureAdmission.select_unregistered_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms select_unregistered_refused
/-- info: 'Minidregg.Compiler.CredentialSignatureAdmission.select_revoked_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms select_revoked_refused
/-- info: 'Minidregg.Compiler.CredentialSignatureAdmission.checked_signer_live' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms checked_signer_live
/-- info: 'Minidregg.Compiler.CredentialSignatureAdmission.requestBytes_exact_projection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms requestBytes_exact_projection
/-- info: 'Minidregg.Compiler.CredentialSignatureAdmission.requestBytes_separates_policyRevision' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms requestBytes_separates_policyRevision

end Minidregg.Compiler.CredentialSignatureAdmission
