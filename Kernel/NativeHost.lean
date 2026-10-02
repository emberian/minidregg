/-
A native host for the actual canonical Mini receivers. Operator configuration
is fixed for the process. Opening never initializes; administration explicitly
bootstraps a checked, pinned genesis. Public calls carry signed operations only.

Logical height and admission share one Loaded image, and the receiver's CAS is
against that exact image. Contention requires preparation/signing against the
new state. Exact historical replay is looked up before fresh authorization.
-/
import Kernel.NativeHostContext
import Kernel.NativeHostGrainBirth
import Kernel.GrainResourceBirthReceiver
import Kernel.NativeObservationController
import Kernel.NativeHostReplay
import Kernel.FnConsumerProgressHistory
import Kernel.PreparedInvocationDiagnostics

namespace Minidregg.Kernel.NativeHost

open Minidregg.Theory
open Minidregg.Theory.CellRegistry
open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.ResourceBirth
open Minidregg.Compiler
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Compiler.NativeHostCodec

set_option autoImplicit false

attribute [local irreducible] Config.profile CanonicalRuntimeProfile.Profile.compilerProfile

/-- Ordinary open only reads and validates; it never installs a missing seed.
It trusts the host's own MAC'd checkpoint and log (DATAMODEL §6 Q1): the latest
checkpoint is materialized and only the records after it are replayed through
the shared executor (`DurableCheckpoint.resume`, sound by `resume_sound`). No
signed ingress is re-admitted here; `audit` does that. -/
def openExisting (config : Config) : IO (Except String (Opened config)) := do
  match ← DurableReceiverIO.load config.transport ResourceBirthCodec.rootBytes with
  | .error detail => return .error detail
  | .ok durable => return validateLoaded config durable

/-- Operator audit: the genesis re-admission of every retained signed ingress
by its real native receiver at its original prefix height, compared with the
stored history record for record (formerly the request path's `verifyLoaded`).
Returns the number of accepted records audited and the presence and link
indexes of the re-admitted history (`NativeHostReplay.Verified.index_from_replay`
and `Verified.linkIndex_from_replay`: they are the stored log's indexes). -/
def audit (config : Config) :
    IO (Except String (Nat × PresenceIndex.Index × LinkIndex.Index)) := do
  match ← DurableReceiverIO.load config.transport ResourceBirthCodec.rootBytes with
  | .error detail => return .error detail
  | .ok durable =>
      match ← NativeHostReplay.verifyLoaded config durable with
      | .error failure =>
          return .error s!"audit refused history at entry {failure.index}: {failure.detail}"
      | .ok verified => return .ok (verified.receipts.length, verified.opened.durable.index,
          verified.opened.durable.links)

/-- Operator read of the whole presence index after an ordinary (checkpoint +
suffix) open. Local administration only: the operator holds the Store. -/
def presenceIndex (config : Config) : IO (Except String (Nat × Nat × PresenceIndex.Index)) := do
  match ← openExisting config with
  | .error detail => return .error detail
  | .ok opened =>
      return .ok (opened.durable.baseHeight, opened.durable.height, opened.durable.index)

/-- Operator read of the whole link index after an ordinary (checkpoint +
suffix) open. Local administration only: the operator holds the Store. -/
def linkIndex (config : Config) : IO (Except String (Nat × Nat × LinkIndex.Index)) := do
  match ← openExisting config with
  | .error detail => return .error detail
  | .ok opened =>
      return .ok (opened.durable.baseHeight, opened.durable.height, opened.durable.links)

/-- Explicit local administration, separate from the signed network protocol.
The exact operator-pinned source genesis must have no accepted transactions. -/
def bootstrap (config : Config) (canonicalImage : List UInt8) : IO (Except String Unit) := do
  match DurableReceiverIO.loadBytes ResourceBirthCodec.rootBytes config.logStart canonicalImage with
  | .error detail => return .error detail
  | .ok durable =>
      if !durable.image.accepted.isEmpty then return .error "bootstrap image contains accepted history"
      match validateLoaded config durable with
      | .error detail => return .error detail
      | .ok _ =>
          return ← DurableReceiverIO.bootstrap config.transport
            ResourceBirthCodec.rootBytes durable.image.seed

private def refused (reason : RefusalReason) (phase detail : String) : Outcome :=
  .refused reason phase.toUTF8.toList detail.toUTF8.toList

/-- A refusal at the durable boundary.  The tail bound is named (`tailBound`,
with the head, the certified height and `L`): it is a fact about the public
chain head, not about the request.  Every other durable reason is the
receiver's `operationRejected`. -/
def durableRefusal : DurableDataIntent.RejectReason → Outcome
  | .tailBound head certified bound =>
      refused .tailBound "tail" s!"head {head} certified {certified} bound {bound}"
  | reason => refused .operationRejected "durable" s!"{repr reason}"

/-- The tail bound's refusal names `tailBound` and the three heights. -/
theorem durableRefusal_tailBound (head certified bound : Nat) :
    durableRefusal (.tailBound head certified bound) =
      refused .tailBound "tail" s!"head {head} certified {certified} bound {bound}" := rfl

private def birthRejection : ResourceBirthReceiver.Reject → String
  | .malformedIngress => "malformed ingress"
  | .transactionConflict => "transaction identity conflict"
  | .admission reason => s!"admission: {repr reason}"
  | .durable (.tailBound head certified bound) => s!"head {head} certified {certified} bound {bound}"
  | .durable reason => s!"durable: {repr reason}"

private def birthReason : ResourceBirthReceiver.Reject → RefusalReason
  | .malformedIngress => .malformed
  | .transactionConflict => .conflict
  | .admission _ => .operationRejected
  | .durable (.tailBound ..) => .tailBound
  | .durable _ => .operationRejected

private def slot (snapshot : CredentialAuthorityDomain.Snapshot) (marker role index : Nat)
    (wanted : PackedEffectRequest) : Except String SigningSlot := do
  let header ← (CredentialSignatureAdmission.signingHeader snapshot marker wanted).mapError
    (fun reason => s!"signing key selection: {repr reason}")
  pure ⟨role, index, CredentialSignedEnvelopeController.headerCodec.encode header⟩

def prepareLoaded (config : Config) (opened : Opened config) (draft : Draft) :
    Except String SigningPlan := do
  let height := logicalHeight config opened.durable
  let profile := config.profile
  let (finalized, slots) ← match draft with
    | .birth bytes capabilities => do
        if (GrainResourceBirthHostCodec.sourceCodec.decode bytes).isSome then
          let (finalized, slots) ← NativeHostGrainBirth.prepareLoaded config opened bytes capabilities
          pure (.birth finalized capabilities, slots)
        else do
          let descriptor ← need "noncanonical birth draft"
            (CanonicalCellRegistry.sourceEncoding.codec.decode bytes)
          let prepared ← (ResourceBirthController.Concrete.prepareDraft profile.compilerProfile
            profile.disabledEvaluators config.deployment opened.pins opened.durable descriptor height).mapError
              (fun reason => s!"birth preparation: {repr reason}")
          check (capabilities.length == prepared.descriptor.resourceBatch.operations.length)
            "birth source capability count mismatch"
          let forBranch := fun (role index : Nat)
              (branch : ResourceBirthPolicyController.Concrete.Branch prepared.descriptor) =>
            slot prepared.prepared.authority.snapshot prepared.descriptor.authorityNullifier role index
              (ResourceBirthPolicyController.Concrete.branchRequest (profile := profile)
                prepared.prepared height branch)
          let factory ← forBranch 0 0 .factory
          let authority ← forBranch 1 0 .authority
          let allocations ← (List.finRange prepared.descriptor.createRequests.length).mapM
            (fun index => forBranch 2 index.val (.allocation index))
          let sources ← (List.finRange prepared.descriptor.resourceBatch.operations.length).mapM
            (fun index => forBranch 3 index.val (.source index))
          pure (.birth (CanonicalCellRegistry.sourceEncoding.codec.encode prepared.descriptor) capabilities,
            factory :: authority :: allocations ++ sources)
    | .invoke bytes => do
        let command ← need "noncanonical invocation command" (DeclaredResourceController.commandCodec.decode bytes)
        let prepared ← (DeclaredResourceController.prepareFrom config.deployment profile
          ⟨config.federation, height⟩ opened.durable (some opened.directory) command).mapError
            (fun reason => s!"invocation preparation: {repr reason}")
        let tuple ← need "invocation incidence collision" (DeclaredResourceController.prepareTuple prepared)
        let marker := DeclaredResourceController.operationMarker config.deployment.domain profile.semantics command
        let targets ← (List.finRange command.targets.length).mapM fun index =>
          slot prepared.authority.snapshot marker 4 index.val (tuple.request (some index))
        let observations ← if command.requiresObservation then
          (List.finRange command.targets.length).mapM fun index =>
            slot prepared.authority.snapshot marker 8 index.val
              ⟨command.targets[index].kind, DeclaredResourceController.readRequest prepared index⟩
          else pure []
        let authority ← slot prepared.authority.snapshot marker 1 0 (tuple.request none)
        pure (.invoke bytes, targets ++ observations ++ [authority])
    | .install subject control bytes => do
        let declaration ← need "noncanonical install declaration" (PolicyInstallController.decodeDeclaration bytes)
        let context : PolicyInstallController.RequestContext :=
          { federation := config.federation, subject := subject
            subjectKeyEpoch := opened.authority.snapshot.authState.subjectKeyEpoch subject
            height := height
            policyEpoch := opened.authority.snapshot.authState.policyEpoch declaration.source.policyId
            policyRevision := opened.authority.snapshot.authState.policyRevision declaration.source.policyId }
        let prepared ← (PolicyInstallController.prepare profile opened.authority.snapshot context bytes).mapError
          (fun reason => s!"install preparation: {repr reason}")
        let request := PolicyInstallController.request profile opened.authority.snapshot context prepared.declaration
        let marker := (PolicyInstallController.requestDigest profile opened.authority.snapshot context prepared.declaration).value
        let signature ← slot opened.authority.snapshot marker 5 0 ⟨.program, request⟩
        pure (.install subject control bytes, [signature])
    | .delegate bytes => do
        let packed ← need "noncanonical delegation command" (CapabilityDelegationController.commandCodec.decode bytes)
        let ambient : CapabilityDelegationController.Ambient := ⟨config.federation, height⟩
        let prepared ← (CapabilityDelegationController.prepare config.deployment profile ambient
          opened.durable packed.2).mapError (fun reason => s!"delegation preparation: {repr reason}")
        let wanted := CapabilityDelegationController.request prepared.authority.snapshot profile.semantics ambient packed.2
        let marker := CapabilityDelegationController.operationMarker config.deployment.domain profile.semantics packed.2
        let signature ← slot prepared.authority.snapshot marker 6 0 ⟨packed.1, wanted⟩
        pure (.delegate bytes, [signature])
    | .revoke bytes => do
        let packed ← need "noncanonical revocation command" (CapabilityRevocationController.commandCodec.decode bytes)
        let ambient : CapabilityRevocationController.Ambient := ⟨config.federation, height⟩
        let prepared ← (CapabilityRevocationController.prepare config.deployment profile ambient
          opened.durable packed.2).mapError (fun reason => s!"revocation preparation: {repr reason}")
        let wanted := CapabilityRevocationController.request prepared.authority.snapshot profile.semantics ambient packed.2
        let marker := CapabilityRevocationController.operationMarker config.deployment.domain profile.semantics packed.2
        let signature ← slot prepared.authority.snapshot marker 7 0 ⟨.program, wanted⟩
        pure (.revoke bytes, [signature])
    | .renounce bytes => do
        -- The plan reads nothing about the named capability: the signer's key
        -- record (public) is the only state it consults. The gate runs at
        -- submission, after the signature verifies.
        let command ← need "noncanonical renounce command" (CapabilityRenounce.commandCodec.decode bytes)
        let ambient : CapabilityRenounce.Ambient := ⟨config.federation, height⟩
        let prepared ← (CapabilityRenounce.prepare config.deployment profile.semantics ambient
          opened.durable command).mapError (fun reason => s!"renounce preparation: {repr reason}")
        let signature ← slot prepared.authority.snapshot prepared.marker 9 0 ⟨.program, prepared.request⟩
        pure (.renounce bytes, [signature])
  pure ⟨config.deployment.domain, profile.semantics, opened.durable.worldRoot,
    height, finalized, slots⟩

/-- Internal operator computation only. It must not be exposed to an untrusted
client before the source-owned observe/preparation gate authorizes its reads. -/
def prepareInternal (config : Config) (bytes : List UInt8) : IO (Except String SigningPlan) := do
  match draftCodec.decode bytes with
  | none => return .error "noncanonical host draft"
  | some draft =>
      match ← openExisting config with
      | .error detail => return .error detail
      | .ok opened => return prepareLoaded config opened draft

/-- Source-authored enrollment plan on one verified image. The sponsor slot is
the ordinary current-authority SignedHeader; the second slot is the exact raw
proof-of-possession frame for the proposed new key. -/
def enrollmentPlanLoaded (config : Config) (opened : Opened config)
    (commandBytes : List UInt8) : Except String ParticipantKeyEnrollment.SigningPlan := do
  let command ← need "noncanonical participant enrollment command"
    (ParticipantKeyEnrollment.commandCodec.decode commandBytes)
  let ambient : ParticipantKeyEnrollment.Ambient :=
    ⟨config.federation, logicalHeight config opened.durable⟩
  let prepared ← (ParticipantKeyEnrollment.prepare config.deployment config.profile ambient
    opened.durable command).mapError (fun reason => s!"enrollment preparation: {repr reason}")
  let selected ← (CredentialSignatureAdmission.signingHeader prepared.authority.snapshot
    (ParticipantKeyEnrollment.marker config.deployment.domain config.profile.semantics command)
    ⟨.program, ParticipantKeyEnrollment.request config.deployment prepared.authority.snapshot
      config.profile.semantics ambient command⟩).mapError
        (fun reason => s!"enrollment sponsor key: {repr reason}")
  pure ⟨config.deployment.domain, config.profile.semantics, commandBytes,
    CredentialSignedEnvelopeController.headerCodec.encode selected,
    ParticipantKeyEnrollment.possessionFrame config.deployment.domain
      config.profile.semantics command⟩

/-- The sponsor's signed factory observation authorizes the plan. Byte-level
mismatches between the command and the observation are `malformed`; the
observation's own refusal is passed through unchanged; a refused plan on an
authorized observation is `operationRejected` with the controller's reason. -/
def enrollmentPlanAuthorizedLoaded (config : Config) (opened : Opened config)
    (signedObservationBytes commandBytes : List UInt8) :
    IO (Except Refusal ParticipantKeyEnrollment.SigningPlan) := do
  let some command := ParticipantKeyEnrollment.commandCodec.decode commandBytes
    | return .error (.of .malformed)
  let some signed := NativeObservationCodec.signedCodec.decode signedObservationBytes
    | return .error (.of .malformed)
  if signed.challenge.intent.subject != command.sponsor then
    return .error (.of .malformed)
  match signed.challenge.intent.purpose with
  | .query query =>
      if query.kind != .object || query.target != config.deployment.factoryId ||
          query.view != .resource then
        return .error (.of .malformed)
  | .prepare _ => return .error (.of .malformed)
  match ← NativeObservationController.authorize config.signature
      ⟨opened.directory, opened.authority⟩ config.profile config.federation
      config.genesisHeight signed with
  | .error refusal => return .error refusal
  | .ok _ => return ((enrollmentPlanLoaded config opened commandBytes).mapError
      fun detail => ⟨.operationRejected, detail, none⟩)

/-- One-shot form. An unopenable Store is an error, never a refusal. -/
def enrollmentPlan (config : Config) (signedObservationBytes commandBytes : List UInt8) :
    IO (Except Refusal ParticipantKeyEnrollment.SigningPlan) := do
  let opened ← IO.ofExcept (← openExisting config)
  enrollmentPlanAuthorizedLoaded config opened signedObservationBytes commandBytes

/-- Assembly transports the detached signatures: the sponsor's, the new key's
and, for a record that commits to a next key, that next key's public half and
its co-signature (both empty otherwise). Native submission rechecks all of
them, the current factory law, exact old state and fresh subject. -/
def enrollmentAssemble (plan : ParticipantKeyEnrollment.SigningPlan)
    (sponsorSignature possessionSignature nextPublicKey nextSignature : List UInt8) :
    Except String (List UInt8) := do
  check (decide (sponsorSignature.length = 64)) "sponsor signature must be 64 bytes"
  check (decide (possessionSignature.length = 64)) "possession signature must be 64 bytes"
  let header ← need "noncanonical enrollment sponsor header"
    (CredentialSignedEnvelopeController.headerCodec.decode plan.sponsorHeader)
  let command ← need "noncanonical enrollment plan command"
    (ParticipantKeyEnrollment.commandCodec.decode plan.commandBytes)
  check (decide (plan.possessionHeader = ParticipantKeyEnrollment.possessionFrame
    plan.domain plan.semantics command)) "enrollment possession frame differs"
  match command.key.nextKeyDigest with
  | none =>
      check (decide (nextPublicKey = [] ∧ nextSignature = []))
        "the record commits to no next key: no next key or co-signature may be presented"
  | some _ =>
      check (decide (nextPublicKey.length = 32))
        "the record commits to a next key: its 32-byte public key is required"
      check (decide (nextSignature.length = 64))
        "the record commits to a next key: that key's 64-byte co-signature is required"
  let envelope := CredentialSignedEnvelopeController.envelopeCodec.encode
    ⟨header, sponsorSignature⟩
  pure (ParticipantKeyEnrollment.ingressCodec.encode
    ⟨plan.commandBytes, envelope, possessionSignature, nextPublicKey, nextSignature⟩)

/-! ## Subject key rotation (pre-rotation)

Public: a rotation needs no capability and no current-key signature, only the
commitment the subject's current record holds and possession of the committed
key.  So plan, assembly, submit, lookup and status are open to the friend who
holds only the next key. -/

/-- Host-authored rotation plan: the exact possession frame the new key signs.
It prepares the rotation first, assuming that signature, so a rotation the gate
refuses (a key whose digest is not the commitment, a subject without one) is
refused here by name. -/
def rotationPlanLoaded (config : Config) (opened : Opened config)
    (commandBytes : List UInt8) : Except String SubjectKeyRotation.SigningPlan := do
  let command ← need "noncanonical subject key rotation command"
    (SubjectKeyRotation.commandCodec.decode commandBytes)
  let _ ← (SubjectKeyRotation.prepare config.deployment config.profile.semantics
    opened.durable command).mapError (fun reason => s!"rotation preparation: {repr reason}")
  pure ⟨config.deployment.domain, config.profile.semantics, commandBytes,
    SubjectKeyRotation.possessionFrame config.deployment.domain config.profile.semantics command⟩

/-- Assembly transports the new key's detached possession signature. -/
def rotationAssemble (plan : SubjectKeyRotation.SigningPlan)
    (possessionSignature : List UInt8) : Except String (List UInt8) := do
  check (decide (possessionSignature.length = 64)) "possession signature must be 64 bytes"
  let command ← need "noncanonical rotation plan command"
    (SubjectKeyRotation.commandCodec.decode plan.commandBytes)
  check (decide (plan.possessionHeader = SubjectKeyRotation.possessionFrame
    plan.domain plan.semantics command)) "rotation possession frame differs"
  pure (SubjectKeyRotation.ingressCodec.encode ⟨plan.commandBytes, possessionSignature⟩)

/-- The current key status of `subject` as seen by the holder of `publicKey`. -/
def keyStatusLoaded (config : Config) (opened : Opened config) (subject : SubjectId)
    (publicKey : List UInt8) : Except String SubjectKeyRotation.Status := do
  let authority ← need "authority cell unavailable"
    (CredentialAuthorityDomainReceiver.loadDeployment config.deployment opened.durable.snapshot)
  need "subject has no current signing key"
    (SubjectKeyRotation.status authority.snapshot.logical subject publicKey)

/-- Source-authored factory-observation provisioning plan on one verified
image. The single slot is the sponsor's ordinary current-authority header for
the factory-management request; the capability fields are source-derived. -/
def provisionPlanLoaded (config : Config) (opened : Opened config)
    (commandBytes : List UInt8) : Except String ParticipantFactoryProvisioning.SigningPlan := do
  let command ← need "noncanonical participant provisioning command"
    (ParticipantFactoryProvisioning.commandCodec.decode commandBytes)
  let ambient : ParticipantFactoryProvisioning.Ambient :=
    ⟨config.federation, logicalHeight config opened.durable⟩
  let prepared ← (ParticipantFactoryProvisioning.prepare config.deployment config.profile ambient
    opened.durable command).mapError (fun reason => s!"provisioning preparation: {repr reason}")
  let selected ← (CredentialSignatureAdmission.signingHeader prepared.authority.snapshot
    (ParticipantFactoryProvisioning.marker config.deployment.domain config.profile.semantics command)
    ⟨.program, ParticipantFactoryProvisioning.request config.deployment config.profile.template
      prepared.authority.snapshot config.profile.semantics ambient command⟩).mapError
        (fun reason => s!"provisioning sponsor key: {repr reason}")
  pure ⟨config.deployment.domain, config.profile.semantics, commandBytes,
    CredentialSignedEnvelopeController.headerCodec.encode selected⟩

/-- As for key enrollment, detailed preparation is disclosed only after a
sponsor-signed factory resource observation on this same opened image. -/
def provisionPlanAuthorizedLoaded (config : Config) (opened : Opened config)
    (signedObservationBytes commandBytes : List UInt8) :
    IO (Except Refusal ParticipantFactoryProvisioning.SigningPlan) := do
  let some command := ParticipantFactoryProvisioning.commandCodec.decode commandBytes
    | return .error (.of .malformed)
  let some signed := NativeObservationCodec.signedCodec.decode signedObservationBytes
    | return .error (.of .malformed)
  if signed.challenge.intent.subject != command.sponsor then
    return .error (.of .malformed)
  match signed.challenge.intent.purpose with
  | .query query =>
      if query.kind != .object || query.target != config.deployment.factoryId ||
          query.view != .resource then
        return .error (.of .malformed)
  | .prepare _ => return .error (.of .malformed)
  match ← NativeObservationController.authorize config.signature
      ⟨opened.directory, opened.authority⟩ config.profile config.federation
      config.genesisHeight signed with
  | .error refusal => return .error refusal
  | .ok _ => return ((provisionPlanLoaded config opened commandBytes).mapError
      fun detail => { reason := .operationRejected, detail := detail })

/-- Assembly transports one detached sponsor signature; native submission
rechecks it, the current factory law, the exact old state and the holder. -/
def provisionAssemble (plan : ParticipantFactoryProvisioning.SigningPlan)
    (sponsorSignature : List UInt8) : Except String (List UInt8) := do
  check (decide (sponsorSignature.length = 64)) "sponsor signature must be 64 bytes"
  let header ← need "noncanonical provisioning sponsor header"
    (CredentialSignedEnvelopeController.headerCodec.decode plan.sponsorHeader)
  let _ ← need "noncanonical provisioning plan command"
    (ParticipantFactoryProvisioning.commandCodec.decode plan.commandBytes)
  let envelope := CredentialSignedEnvelopeController.envelopeCodec.encode
    ⟨header, sponsorSignature⟩
  pure (ParticipantFactoryProvisioning.ingressCodec.encode ⟨plan.commandBytes, envelope⟩)

def observationContext (config : Config) (opened : Opened config) :
    NativeObservationController.Context config.deployment opened.durable :=
  ⟨opened.directory, opened.authority⟩

/-- The answer to an observation request, given the subject's selected key and the native
verdict on its intent signature. Only an authenticated request reaches the challenge, which
reads the intent's targets; from there only commitments and explicitly public
request/key/policy coordinates escape, and a refusal names only a `preAuthentication`
reason. -/
def challengeAnswer (config : Config) (opened : Opened config)
    (intent : NativeObservationCodec.Intent) (intentSignature : List UInt8)
    (key : Except Refusal (List UInt8)) (verdict : Except CredentialSignatureIO.Error Bool) :
    Except Refusal NativeObservationCodec.Challenge :=
  match NativeObservationController.authenticated key verdict with
  | .error refusal => .error refusal
  | .ok () =>
      (NativeObservationController.challenge (observationContext config opened)
        config.profile config.federation config.genesisHeight intent intentSignature).mapError
          NativeObservationController.preAuthentication

/-- Op 4. The request is the intent's bytes and the subject's signature over them. The
Host decodes the intent, selects the subject's current key, and verifies the signature;
nothing about the intent's targets is read until that succeeds (FIX-DISCLOSE). -/
def challengeLoaded (config : Config) (opened : Opened config)
    (intentBytes intentSignature : List UInt8) :
    IO (Except Refusal NativeObservationCodec.Challenge) := do
  let some intent := NativeObservationCodec.intentCodec.decode intentBytes
    | return .error (.of .malformed)
  let key := NativeObservationController.intentKey (observationContext config opened) intent.subject
  let verdict ← NativeObservationController.intentVerdict config.signature key intent intentSignature
  return challengeAnswer config opened intent intentSignature key verdict

/-- **One path before authentication.** Op 4 is: decode, select the subject's key, ask the
native verifier about the intent signature (`intentVerdict`, which is handed the key, the
intent's bytes and the signature, and nothing of the Store's directory), then answer. -/
theorem challengeLoaded_authenticates_first (config : Config) (opened : Opened config)
    (intentBytes intentSignature : List UInt8) :
    challengeLoaded config opened intentBytes intentSignature =
      (match NativeObservationCodec.intentCodec.decode intentBytes with
      | none => pure (.error (.of .malformed))
      | some intent => do
          let verdict ← NativeObservationController.intentVerdict config.signature
            (NativeObservationController.intentKey (observationContext config opened) intent.subject)
            intent intentSignature
          pure (challengeAnswer config opened intent intentSignature
            (NativeObservationController.intentKey (observationContext config opened) intent.subject)
            verdict)) := by
  unfold challengeLoaded
  cases NativeObservationCodec.intentCodec.decode intentBytes <;> rfl

/-- **`unenrolled_response_independent_of_target`.** A request whose intent signature does
not verify under the subject's current key -- a key that was never enrolled naming an
enrolled subject, or any wrong key -- gets the same answer whatever its intent names:
present or absent targets, any capability numbers, any purpose. With
`challengeLoaded_authenticates_first`, the answer is computed on the one path that reads
only the subject's key. -/
theorem unenrolled_response_independent_of_target (config : Config) (opened : Opened config)
    (left right : NativeObservationCodec.Intent) (leftSignature rightSignature : List UInt8)
    (subject : left.subject = right.subject)
    (leftVerdict rightVerdict : Except CredentialSignatureIO.Error Bool)
    (leftFails : leftVerdict ≠ .ok true) (rightFails : rightVerdict ≠ .ok true) :
    challengeAnswer config opened left leftSignature
        (NativeObservationController.intentKey (observationContext config opened) left.subject)
        leftVerdict =
      challengeAnswer config opened right rightSignature
        (NativeObservationController.intentKey (observationContext config opened) right.subject)
        rightVerdict := by
  have same : NativeObservationController.authenticated
        (NativeObservationController.intentKey (observationContext config opened) left.subject)
        leftVerdict =
      NativeObservationController.authenticated
        (NativeObservationController.intentKey (observationContext config opened) right.subject)
        rightVerdict := by
    rw [subject]
    exact NativeObservationController.authenticated_unverified _ _ _ leftFails rightFails
  unfold challengeAnswer
  cases refused : NativeObservationController.authenticated
      (NativeObservationController.intentKey (observationContext config opened) right.subject)
      rightVerdict with
  | ok value =>
      exact absurd refused fun admitted =>
        rightFails ((NativeObservationController.authenticated_ok_iff _ _).mp admitted).2
  | error refusal => rw [same, refused]

/-- The accepting pole: an authenticated request reaches the challenge exactly as before. -/
theorem authenticated_reaches_challenge (config : Config) (opened : Opened config)
    (intent : NativeObservationCodec.Intent) (intentSignature publicKey : List UInt8) :
    challengeAnswer config opened intent intentSignature (.ok publicKey) (.ok true) =
      (NativeObservationController.challenge (observationContext config opened)
        config.profile config.federation config.genesisHeight intent intentSignature).mapError
          NativeObservationController.preAuthentication := rfl

/-- An answer's refusal is an unauthenticated one (`unknownKey`, `badSignature`), a
`preAuthentication` reason, or `malformed` for bytes that do not decode. -/
theorem challengeAnswer_public (config : Config) (opened : Opened config)
    (intent : NativeObservationCodec.Intent) (intentSignature : List UInt8)
    (verdict : Except CredentialSignatureIO.Error Bool) (refusal : Refusal)
    (refused : challengeAnswer config opened intent intentSignature
      (NativeObservationController.intentKey (observationContext config opened) intent.subject)
      verdict = .error refusal) :
    refusal = .of .unknownKey ∨ refusal = .of .badSignature ∨
      ∃ inner, refusal = NativeObservationController.preAuthentication inner := by
  unfold challengeAnswer at refused
  cases gate : NativeObservationController.authenticated
      (NativeObservationController.intentKey (observationContext config opened) intent.subject)
      verdict with
  | error reason =>
      rw [gate] at refused
      cases refused
      rcases NativeObservationController.authenticated_refusal _ _ _ _ gate with known | bad
      · exact Or.inl known
      · exact Or.inr (Or.inl bad)
  | ok value =>
      rw [gate] at refused
      cases decided : NativeObservationController.challenge (observationContext config opened)
          config.profile config.federation config.genesisHeight intent intentSignature with
      | error inner =>
          rw [decided] at refused
          cases refused
          exact Or.inr (Or.inr ⟨inner, rfl⟩)
      | ok value =>
          rw [decided] at refused
          cases refused

/-- One-shot form. An unopenable Store is an error, never a refusal. -/
def challenge (config : Config) (intentBytes intentSignature : List UInt8) :
    IO (Except Refusal NativeObservationCodec.Challenge) := do
  let opened ← IO.ofExcept (← openExisting config)
  challengeLoaded config opened intentBytes intentSignature

/-- The steps a command's run claim names, when they exceed the operator's
synchronous budget `config.nockFSync`; `none` when the command claims no run or
claims at most the budget (`overSyncBudget_admits`, `overSyncBudget_refuses`). -/
def overSyncBudget (config : Config) (command : DeclaredResourceController.Command) : Option Nat :=
  match command.run with
  | some claim => if config.nockFSync < claim.steps then some claim.steps else none
  | none => none

theorem overSyncBudget_admits (config : Config) (command : DeclaredResourceController.Command)
    (claim : Run.RunClaim) (run : command.run = some claim)
    (within : claim.steps ≤ config.nockFSync) : overSyncBudget config command = none := by
  simp [overSyncBudget, run, Nat.not_lt.mpr within]

theorem overSyncBudget_refuses (config : Config) (command : DeclaredResourceController.Command)
    (claim : Run.RunClaim) (run : command.run = some claim)
    (exceeds : config.nockFSync < claim.steps) : overSyncBudget config command = some claim.steps := by
  simp [overSyncBudget, run, exceeds]

theorem overSyncBudget_unclaimed (config : Config) (command : DeclaredResourceController.Command)
    (run : command.run = none) : overSyncBudget config command = none := by
  simp [overSyncBudget, run]

def overSyncBudgetDetail (config : Config) (steps : Nat) : String :=
  s!"overSyncBudget: run claim of {steps} Lean steps exceeds the operator's synchronous budget nockFSync {config.nockFSync}"

/-- The operator-log detail of an invocation's `insufficientBudget`. The
durable meter is the genesis `meterAllowance` less every admitted charge
(`DurableCommitProtocol.Snapshot.install`); nothing replenishes it, and a run
claim debits its steps from `proofWork` one for one
(`DeclaredResourceController.sourceChargeFrom`). The per-turn bound is
`nockFSync` (`overSyncBudget`); this is the deployment's lifetime meter. -/
def meterShortfallDetail (proofWorkLeft claimed : Nat) : String :=
  if claimed ≤ proofWorkLeft then
    s!"insufficientBudget: a lifetime resource meter (genesis meterAllowance) is exhausted; proofWork still holds {proofWorkLeft} against this run claim of {claimed} steps"
  else
    s!"insufficientBudget: the lifetime proofWork meter holds {proofWorkLeft} (genesis meterAllowance.proofWork less every admitted charge; never replenished) against this run claim of {claimed} steps"

/-- The sync gate on a preparation draft: only an invocation carries a run claim. -/
def draftOverSyncBudget (config : Config) : Draft → Option Nat
  | .invoke bytes => (DeclaredResourceController.commandCodec.decode bytes).bind (overSyncBudget config)
  | _ => none

/-- The clause of a target's committed law that an invocation draft would fail,
evaluated on the same projected step and resolved law that
`DeclaredResourceController.authorizeLeg` admits at submission
(`DeclaredResourceController.lawLeaf_fails`). Only the read-authorized
preparation path consults it, so the requester learns the clause of a law over
state it may already read. -/
def invokeLawLeaf (config : Config) (opened : Opened config) : Draft → Option LawLeaf
  | .invoke bytes => do
      let command ← DeclaredResourceController.commandCodec.decode bytes
      let prepared ← (DeclaredResourceController.prepareFrom config.deployment config.profile
        ⟨config.federation, logicalHeight config opened.durable⟩ opened.durable (some opened.directory)
        command).toOption
      let tuple ← DeclaredResourceController.prepareTuple prepared
      DeclaredResourceController.firstLawLeaf prepared tuple
  | _ => none

/-- The out-of-range order clause of a target's committed law that an invocation
draft would hit, on the same projected step and resolved law that
`DeclaredResourceController.authorizeLeg` range-checks at submission
(`DeclaredResourceController.rangeLeaf_none_iff_inputsInRange`). -/
def invokeRangeLeaf (config : Config) (opened : Opened config) : Draft → Option LawLeaf
  | .invoke bytes => do
      let command ← DeclaredResourceController.commandCodec.decode bytes
      let prepared ← (DeclaredResourceController.prepare config.deployment config.profile
        ⟨config.federation, logicalHeight config opened.durable⟩ opened.durable command).toOption
      let tuple ← DeclaredResourceController.prepareTuple prepared
      DeclaredResourceController.firstRangeLeaf prepared tuple
  | _ => none

/-- Two integers of an invocation draft's step with one field image, on the same
step and resolved law `DeclaredResourceController.authorizeLeg` cast-checks
(`DeclaredResourceController.castAliasLeg_none_iff_castInjOn`). -/
def invokeCastAlias (config : Config) (opened : Opened config) : Draft → Option (Int × Int)
  | .invoke bytes => do
      let command ← DeclaredResourceController.commandCodec.decode bytes
      let prepared ← (DeclaredResourceController.prepare config.deployment config.profile
        ⟨config.federation, logicalHeight config opened.durable⟩ opened.durable command).toOption
      let tuple ← DeclaredResourceController.prepareTuple prepared
      DeclaredResourceController.firstCastAlias prepared tuple
  | _ => none

/-- Op 4's payload: the session's pair framing (a four-byte little-endian length, the
intent's bytes, then the signature). Anything else is `malformed`. -/
def challengeRequestParts (payload : List UInt8) : Option (List UInt8 × List UInt8) :=
  if payload.length < 4 then none
  else
    let width := payload[0]!.toNat + 256 * payload[1]!.toNat +
      65536 * payload[2]!.toNat + 16777216 * payload[3]!.toNat
    if width ≤ payload.length - 4 then some ((payload.drop 4).take width, payload.drop (4 + width))
    else none

/-- Op 4 on an opened image: split the request, then `challengeLoaded`. -/
def challengeRequestLoaded (config : Config) (opened : Opened config) (payload : List UInt8) :
    IO (Except Refusal NativeObservationCodec.Challenge) :=
  match challengeRequestParts payload with
  | none => pure (.error (.of .malformed))
  | some (intentBytes, intentSignature) => challengeLoaded config opened intentBytes intentSignature

/-- Op 4, one-shot. -/
def challengeRequest (config : Config) (payload : List UInt8) :
    IO (Except Refusal NativeObservationCodec.Challenge) := do
  let opened ← IO.ofExcept (← openExisting config)
  challengeRequestLoaded config opened payload

/-- The fields the requester's observation grant on `target` names (K-FIELDS): the first
grant of the signed intent naming that target. A target the intent names no grant for is
told no field (`some ∅`). -/
def grantFields (config : Config) (opened : Opened config) (grants : List NativeObservationCodec.GrantRef)
    (target : Nat) : Option (Finset CellField) :=
  match grants.find? (fun grant => grant.target == target) with
  | some grant => ResourceObservationAdmission.readerFields (observationContext config opened)
      grant.kind grant.capability
  | none => some ∅

/-- Diagnose one already prepared invocation, with each leg's grant controlling
which values may be disclosed. Submission still performs its own fresh preparation. -/
def invokeRefusal (config : Config) (opened : Opened config)
    (grants : List NativeObservationCodec.GrantRef) : Draft → Option Refusal
  | .invoke bytes => do
      let command ← DeclaredResourceController.commandCodec.decode bytes
      let prepared ← (DeclaredResourceController.prepareFrom config.deployment config.profile
        ⟨config.federation, logicalHeight config opened.durable⟩ opened.durable
        (some opened.directory) command).toOption
      let tuple ← DeclaredResourceController.prepareTuple prepared
      let legs := DeclaredResourceController.preparePolicyLegs prepared tuple
      let fieldsOf := fun incidence => match incidence with
        | some i => grantFields config opened grants command.targets[i].target
        | none => some ∅
      (legs.firstRangeWith (fun i leaf => Refusal.lawInputRangeFor (fieldsOf i) leaf)).orElse fun _ =>
        (legs.firstCastWith (fun i x y => Refusal.castAliasFor (fieldsOf i) x y)).orElse fun _ =>
          legs.firstLawWith (fun i committed oldState newState =>
            Refusal.lawDeniedFor (fieldsOf i) committed.record.predicate oldState newState)
  | _ => none

/-- The only public preparation path. A source-owned proof of every actual
read permission is required before the internal planner may disclose a result
or a detailed state-dependent error, on the very same opened image. -/
def prepareAuthorizedLoaded (config : Config) (opened : Opened config)
    (bytes : List UInt8) : IO (Except Refusal SigningPlan) := do
  let some signed := NativeObservationCodec.signedCodec.decode bytes
    | return .error (.of .malformed)
  match ← NativeObservationController.authorize config.signature (observationContext config opened)
      config.profile config.federation config.genesisHeight signed with
  | .error refusal => return .error refusal
  | .ok _ =>
      match signed.challenge.intent.purpose with
      | .prepare draft =>
          if let some steps := draftOverSyncBudget config draft then
            return .error ⟨.operationRejected, overSyncBudgetDetail config steps, none⟩
          match invokeRefusal config opened signed.challenge.intent.grants draft with
          | some refusal => return .error refusal
          | none => return ((prepareLoaded config opened draft).mapError
              fun detail => ⟨.operationRejected, detail, none⟩)
      | .query _ => return .error (.of .malformed)

/-- One-shot form. An unopenable Store is an error, never a refusal. -/
def prepare (config : Config) (bytes : List UInt8) : IO (Except Refusal SigningPlan) := do
  let opened ← IO.ofExcept (← openExisting config)
  prepareAuthorizedLoaded config opened bytes

/-- The controller projects the authorized logical resource/account cut. Raw
snapshots, whole Books, and unrelated authority pages never escape this API. -/
def queryLoaded (config : Config) (opened : Opened config)
    (bytes : List UInt8) : IO (Except Refusal (List UInt8)) := do
  let some signed := NativeObservationCodec.signedCodec.decode bytes
    | return .error (.of .malformed)
  match ← NativeObservationController.authorize config.signature (observationContext config opened)
      config.profile config.federation config.genesisHeight signed with
  | .error refusal => return .error refusal
  | .ok token =>
      match token.queryResult with
      | .ok view => return .ok view
      | .error reason => return .error (.of reason)

/-- One-shot form. An unopenable Store is an error, never a refusal. -/
def query (config : Config) (bytes : List UInt8) : IO (Except Refusal (List UInt8)) := do
  let opened ← IO.ofExcept (← openExisting config)
  queryLoaded config opened bytes

/-- Custody signs each exact canonical header outside the host. Assembly only
places signatures into the source-owned ingress; submission checks them anew. -/
def assemble (plan : SigningPlan) (signatures : List (List UInt8)) : Except String SignedCall := do
  check (signatures.length == plan.slots.length) "signature count mismatch"
  let envelopes ← (plan.slots.zip signatures).mapM fun (selected, signature) => do
    check (signature.length == 64) "Ed25519 signature must be 64 bytes"
    let header ← need "noncanonical signing header"
      (CredentialSignedEnvelopeController.headerCodec.decode selected.header)
    pure (CredentialSignedEnvelopeController.envelopeCodec.encode ⟨header, signature⟩)
  match plan.finalizedDraft with
  | .invoke bytes => do
      let command ← need "noncanonical finalized invocation" (DeclaredResourceController.commandCodec.decode bytes)
      let targetCount := command.targets.length
      let observeCount := if command.requiresObservation then targetCount else 0
      check (!command.targets.isEmpty && envelopes.length == targetCount + observeCount + 1)
        "invocation signing slots mismatch"
      let authority ← need "missing invocation authority envelope" envelopes[targetCount + observeCount]?
      pure (.invoke ⟨bytes, envelopes.take targetCount,
        envelopes.drop targetCount |>.take observeCount, authority⟩)
  | .install subject control bytes =>
      match envelopes with
      | [envelope] => pure (.install (PolicyInstallReceiver.ingressCodec.encode ⟨subject, control, bytes, envelope⟩))
      | _ => .error "install signing slots mismatch"
  | .birth bytes capabilities => do
      if let some finalized := GrainResourceBirthHostCodec.finalizedCodec.decode bytes then
        let source ← need "noncanonical finalized grain birth source"
          (GrainResourceBirthHostCodec.sourceCodec.decode finalized.sourceBytes)
        let command ← need "noncanonical finalized grain command"
          (DeclaredResourceController.commandCodec.decode finalized.commandBytes)
        let allocationCount := source.birth.createRequests.length
        let sourceCount := source.birth.resourceBatch.operations.length
        let targetCount := command.targets.length
        let bornCount := 2 + allocationCount + sourceCount
        check (capabilities.length == sourceCount && targetCount == 2 &&
          envelopes.length == bornCount + targetCount + targetCount)
          "grain-backed birth signing slots mismatch"
        let factory ← need "missing composite factory envelope" envelopes[0]?
        let authority ← need "missing composite authority envelope" envelopes[1]?
        let allocations := (envelopes.drop 2 |>.take allocationCount).map fun envelope =>
          ({ capability := none, envelope := envelope } :
            ResourceBirthPolicyController.Concrete.BranchCredential)
        let sources := (capabilities.zip
            (envelopes.drop (2 + allocationCount) |>.take sourceCount)).map
          fun (capability, envelope) =>
            ({ capability := some capability, envelope := envelope } :
              ResourceBirthPolicyController.Concrete.BranchCredential)
        let birthBytes := ResourceBirthPolicyController.Concrete.ingressCodec.encode
          ⟨(ResourceBirthCodec.descriptorCodec CanonicalCellRegistry.registry).encode source.birth,
            ⟨⟨none, factory⟩, ⟨none, authority⟩, allocations, sources⟩⟩
        let grainSigned : DeclaredResourceController.SignedCommand :=
          ⟨finalized.commandBytes,
            envelopes.drop bornCount |>.take targetCount,
            envelopes.drop (bornCount + targetCount) |>.take targetCount,
            authority⟩
        let grainBytes := DeclaredResourceController.signedBytes plan.domain plan.semantics grainSigned
        return .birth (GrainResourceBirthPolicyController.ingressCodec.encode
          ⟨finalized.sourceBytes, birthBytes, grainBytes⟩)
      let descriptor ← need "noncanonical finalized birth" (CanonicalCellRegistry.sourceEncoding.codec.decode bytes)
      let allocationCount := descriptor.createRequests.length
      let sourceCount := descriptor.resourceBatch.operations.length
      check (capabilities.length == sourceCount && envelopes.length == 2 + allocationCount + sourceCount)
        "birth signing slots mismatch"
      let factory ← need "missing factory envelope" envelopes[0]?
      let authority ← need "missing authority envelope" envelopes[1]?
      let allocations := (envelopes.drop 2 |>.take allocationCount).map fun envelope =>
        ({ capability := none, envelope := envelope } : ResourceBirthPolicyController.Concrete.BranchCredential)
      let sources := (capabilities.zip (envelopes.drop (2 + allocationCount))).map fun (capability, envelope) =>
        ({ capability := some capability, envelope := envelope } : ResourceBirthPolicyController.Concrete.BranchCredential)
      pure (.birth (ResourceBirthPolicyController.Concrete.ingressCodec.encode
        ⟨bytes, ⟨⟨none, factory⟩, ⟨none, authority⟩, allocations, sources⟩⟩))
  | .delegate bytes =>
      match envelopes with
      | [envelope] => pure (.delegate (CapabilityDelegationReceiver.ingressCodec.encode ⟨bytes, envelope⟩))
      | _ => .error "delegation signing slots mismatch"
  | .revoke bytes =>
      match envelopes with
      | [envelope] => pure (.revoke (CapabilityRevocationReceiver.ingressCodec.encode ⟨bytes, envelope⟩))
      | _ => .error "revocation signing slots mismatch"
  | .renounce bytes =>
      match envelopes with
      | [envelope] => pure (.renounce (CapabilityRenounce.ingressCodec.encode ⟨bytes, envelope⟩))
      | _ => .error "renounce signing slots mismatch"

/-- The world root after accepted record `index`: at the head it is the served
image's cached root (one read); an earlier prefix is evaluated from its image
(the specification root; a lookup of old history pays for it). -/
def receiptRoot (config : Config) (durable : Durable) (index : Nat) : Digest :=
  if index + 1 = durable.image.accepted.length then durable.worldRoot
  else worldRoot config ⟨durable.image.seed, durable.image.accepted.take (index + 1)⟩

/-- Seal the ORIGINAL accepted prefix, even when a later transaction was
published before physical confirmation/readback completed. -/
def historicalReceipt (config : Config) (durable : Durable) (transactionId eventId : Digest) :
    Option NativeHostCodec.Receipt := do
  let index ← durable.image.accepted.findIdx? (fun record => record.transactionId == transactionId)
  let record ← durable.image.accepted[index]?
  if record.event.eventId != eventId then none else
    some ⟨transactionId, eventId, index + 1, receiptRoot config durable index⟩

/-- **Receipt binding (DATAMODEL §3.4).**  A sealed receipt names its
transaction's accepted prefix, and carries exactly that prefix's world root and
height. -/
theorem historicalReceipt_bound (config : Config) (durable : Durable)
    (transactionId eventId : Digest) (receipt : NativeHostCodec.Receipt)
    (sealed : historicalReceipt config durable transactionId eventId = some receipt) :
    ∃ index, durable.image.accepted.findIdx?
        (fun record => record.transactionId == transactionId) = some index ∧
      receipt.worldRoot = receiptRoot config durable index ∧
      receipt.acceptedCount =
        NativeHostCodec.height ⟨durable.image.seed, durable.image.accepted.take (index + 1)⟩ := by
  unfold historicalReceipt at sealed
  rcases hidx : durable.image.accepted.findIdx?
      (fun record => record.transactionId == transactionId) with _ | index
  · simp [hidx] at sealed
  · have hlt : index < durable.image.accepted.length := by
      rcases List.findIdx?_eq_some_iff_getElem.mp hidx with ⟨h, _⟩
      exact h
    rcases hrec : durable.image.accepted[index]? with _ | record
    · simp at hrec; omega
    · simp only [hidx, hrec, Option.bind_eq_bind, Option.bind_some] at sealed
      split at sealed
      · cases sealed
      · cases sealed
        refine ⟨index, hidx, rfl, ?_⟩
        simp [NativeHostCodec.height, List.length_take]
        omega

/-- When the old chronological prefix has no matching transaction ID, the
historical selector points at the newly appended record and reproduces its
original-prefix receipt. This is a list fact, not a hash collision premise. -/
theorem historicalReceipt_exactCandidate_fresh (config : Config)
    {oldTarget : Durable} (old : NativeHostReplay.Verified config oldTarget)
    (derived : NativeHostReplay.Derived config old.opened)
    (ready : DurableCheckpoint.Ready ResourceBirthCodec.rootBytes
      old.opened.durable.image old.opened.durable.baseHeight old.opened.durable.base
      old.opened.durable.snapshot derived.intent)
    (fresh : old.opened.durable.image.accepted.findIdx?
      (fun record => record.transactionId == derived.intent.transactionId) = none) :
    historicalReceipt config (NativeHostReplay.exactCandidate old derived ready)
      derived.intent.transactionId derived.intent.event.eventId =
      some ⟨derived.intent.transactionId, derived.intent.event.eventId,
        old.opened.durable.image.accepted.length + 1,
        (NativeHostReplay.exactCandidate old derived ready).worldRoot⟩ := by
  simp [historicalReceipt, receiptRoot, NativeHostReplay.exactCandidate,
    DurableReceiverIO.Loaded.extend, DurableReceiver.Image.append, List.findIdx?_append, fresh,
    DurableReceiver.IntentRecord.ofIntent]

private def confirmed (config : Config) (kind : DurableReceiverIO.Confirmation)
    (transactionId eventId : Digest) : IO Outcome := do
  match ← openExisting config with
  | .error detail => return .uncertain s!"receipt readback: {detail}".toUTF8.toList
  | .ok opened =>
      match historicalReceipt config opened.durable transactionId eventId with
      | none => return .uncertain "original receipt prefix unavailable".toUTF8.toList
      | some receipt => return .confirmed kind receipt

def enrollmentSubmitLoaded (config : Config) (opened : Opened config)
    (bytes : List UInt8) : IO Outcome := do
  match ← ParticipantKeyEnrollmentReceiver.receiveLoaded config.deployment config.profile
      ⟨config.federation, logicalHeight config opened.durable⟩ config.signature
      config.transport opened.durable bytes with
  | .confirmed kind receipt => confirmed config kind receipt.transactionId receipt.eventId
  | .rejected reason => return refused .operationRejected "enroll-key" s!"{repr reason}"
  | .transactionConflict => return refused .conflict "replay" "transaction identity conflict"
  | .durableRejected reason => return durableRefusal reason
  | .contention => return .contention
  | .unavailable detail => return .unavailable detail.toUTF8.toList
  | .uncertain detail => return .uncertain detail.toUTF8.toList

def enrollmentSubmit (config : Config) (bytes : List UInt8) : IO Outcome := do
  match ← openExisting config with
  | .error detail => return .unavailable detail.toUTF8.toList
  | .ok opened => enrollmentSubmitLoaded config opened bytes

/-- Receipt-only historical lookup. Absence never submits fresh work. -/
def enrollmentLookupLoaded (config : Config) (opened : Opened config)
    (bytes : List UInt8) : Outcome :=
  match ParticipantKeyEnrollment.decodeIngress bytes with
  | none => refused .malformed "enroll-key" "noncanonical signed ingress"
  | some ingress =>
    match ParticipantKeyEnrollmentReceiver.replay config.deployment.domain
        config.profile.semantics opened.durable ingress with
    | some (.ok receipt) =>
        match historicalReceipt config opened.durable receipt.transactionId receipt.eventId with
        | some original => .confirmed .replayed original
        | none => .uncertain "original receipt prefix unavailable".toUTF8.toList
    | some (.error _) => refused .conflict "replay" "transaction identity conflict"
    | none => .absent

def enrollmentLookup (config : Config) (bytes : List UInt8) : IO Outcome := do
  match ← openExisting config with
  | .error detail => return .unavailable detail.toUTF8.toList
  | .ok opened => return enrollmentLookupLoaded config opened bytes

def rotationSubmitLoaded (config : Config) (opened : Opened config)
    (bytes : List UInt8) : IO Outcome := do
  match ← SubjectKeyRotation.receiveLoaded config.deployment config.profile.semantics
      config.signature config.transport opened.durable bytes with
  | .confirmed kind receipt => confirmed config kind receipt.transactionId receipt.eventId
  | .rejected reason => return refused .operationRejected "rotate-key" s!"{repr reason}"
  | .transactionConflict => return refused .conflict "replay" "transaction identity conflict"
  | .durableRejected reason => return refused .operationRejected "durable" s!"{repr reason}"
  | .contention => return .contention
  | .unavailable detail => return .unavailable detail.toUTF8.toList
  | .uncertain detail => return .uncertain detail.toUTF8.toList

/-- Receipt-only historical lookup of one rotation ingress. -/
def rotationLookupLoaded (config : Config) (opened : Opened config)
    (bytes : List UInt8) : Outcome :=
  match SubjectKeyRotation.decodeIngress bytes with
  | none => refused .malformed "rotate-key" "noncanonical signed ingress"
  | some ingress =>
    match SubjectKeyRotation.replay config.deployment.domain
        config.profile.semantics opened.durable ingress with
    | some (.ok receipt) =>
        match historicalReceipt config opened.durable receipt.transactionId receipt.eventId with
        | some original => .confirmed .replayed original
        | none => .uncertain "original receipt prefix unavailable".toUTF8.toList
    | some (.error _) => refused .conflict "replay" "transaction identity conflict"
    | none => .absent

def provisionSubmitLoaded (config : Config) (opened : Opened config)
    (bytes : List UInt8) : IO Outcome := do
  match ← ParticipantFactoryProvisioningReceiver.receiveLoaded config.deployment config.profile
      ⟨config.federation, logicalHeight config opened.durable⟩ config.signature
      config.transport opened.durable bytes with
  | .confirmed kind receipt => confirmed config kind receipt.transactionId receipt.eventId
  | .rejected reason => return refused .operationRejected "provision-factory-observe" s!"{repr reason}"
  | .transactionConflict => return refused .conflict "replay" "transaction identity conflict"
  | .durableRejected reason => return durableRefusal reason
  | .contention => return .contention
  | .unavailable detail => return .unavailable detail.toUTF8.toList
  | .uncertain detail => return .uncertain detail.toUTF8.toList

/-! ## Fleet turns: plan, assembly, submit, lookup, topic reads, heads -/

/-- The finalized command fills exactly two draft fields: the pinned base
tariff and, when the draft's publication position is zero, the stream's next
position on this image. Every other field is the draft's. -/
def fleetFinalize (config : Config) (opened : Opened config) (draft : FleetTurn.Command) :
    FleetTurn.Command :=
  let publication := draft.publication.map fun publication =>
    if publication.sequence = 0 then
      let head := FleetTurn.streamHead config.deployment opened.directory.directory
        (FleetTurn.streamDigest config.deployment.domain draft.payer publication.topic)
      { publication with sequence := head.nextSeq }
    else publication
  { draft with fee := config.tariff.base, publication := publication }

def fleetPlanLoaded (config : Config) (opened : Opened config) (command : FleetTurn.Command) :
    Except String FleetTurn.SigningPlan := do
  let ambient : FleetTurn.Ambient := ⟨config.federation, logicalHeight config opened.durable⟩
  let prepared ← (FleetTurn.prepare config.deployment config.profile config.tariff ambient
    opened.durable command).mapError (fun reason => s!"fleet turn preparation: {repr reason}")
  let selected ← (CredentialSignatureAdmission.signingHeader prepared.authority.snapshot
    (FleetTurn.marker config.deployment.domain config.profile.semantics command)
    ⟨.account, FleetTurn.request prepared.authority.snapshot config.profile.semantics ambient
      command⟩).mapError (fun reason => s!"fleet turn signer key: {repr reason}")
  pure ⟨config.deployment.domain, config.profile.semantics, FleetTurn.commandCodec.encode command,
    CredentialSignedEnvelopeController.headerCodec.encode selected⟩

/-- Planning reads the paying account's balance and topic head, so it is
released only behind a current signed observation of that account by the
turn's own signer. -/
def fleetObservedAccount (config : Config) (opened : Opened config)
    (signedObservationBytes : List UInt8) : IO (Except Refusal (SubjectId × Nat)) := do
  let some signed := NativeObservationCodec.signedCodec.decode signedObservationBytes
    | return .error (.of .malformed)
  match signed.challenge.intent.purpose with
  | .query query =>
      if query.kind != .account || query.view != .resource then
        return .error (.of .malformed)
      match ← NativeObservationController.authorize config.signature
          ⟨opened.directory, opened.authority⟩ config.profile config.federation
          config.genesisHeight signed with
      | .error refusal => return .error refusal
      | .ok _ => return .ok (signed.challenge.intent.subject, query.target)
  | .prepare _ => return .error (.of .malformed)

def fleetPlanAuthorizedLoaded (config : Config) (opened : Opened config)
    (signedObservationBytes draftBytes : List UInt8) :
    IO (Except Refusal FleetTurn.SigningPlan) := do
  let some draft := FleetTurn.commandCodec.decode draftBytes
    | return .error { reason := .malformed, detail := "noncanonical fleet turn draft" }
  match ← fleetObservedAccount config opened signedObservationBytes with
  | .error refusal => return .error refusal
  | .ok (subject, account) =>
      if subject != draft.subject || account != draft.payer then
        return .error (.of .malformed)
      return ((fleetPlanLoaded config opened (fleetFinalize config opened draft)).mapError
        fun detail => { reason := .operationRejected, detail := detail })

def fleetAssemble (plan : FleetTurn.SigningPlan) (signature : List UInt8) :
    Except String (List UInt8) := do
  check (decide (signature.length = 64)) "fleet signature must be 64 bytes"
  let header ← need "noncanonical fleet turn header"
    (CredentialSignedEnvelopeController.headerCodec.decode plan.header)
  let _ ← need "noncanonical fleet turn plan command"
    (FleetTurn.commandCodec.decode plan.commandBytes)
  let envelope := CredentialSignedEnvelopeController.envelopeCodec.encode ⟨header, signature⟩
  pure (FleetTurn.ingressCodec.encode ⟨plan.commandBytes, envelope⟩)

/-- `confirm` seals the original receipt from the image the caller already
tracks (a session refreshes by the appended delta); it never substitutes a
different admission. -/
def fleetSubmitLoaded (config : Config) (opened : Opened config)
    (bytes : List UInt8)
    (confirm : DurableReceiverIO.Confirmation → Digest → Digest → IO Outcome) :
    IO Outcome := do
  match ← FleetTurnReceiver.receiveLoaded config.deployment config.profile config.tariff
      ⟨config.federation, logicalHeight config opened.durable⟩ config.signature
      config.transport opened.durable bytes with
  | .confirmed kind receipt => confirm kind receipt.transactionId receipt.eventId
  -- The signed header names an authority root older than the loaded one: the
  -- plan was made against an earlier image and nothing moved. That is the
  -- typed contention outcome (re-plan against the new state), decided from the
  -- header's root before any signature is examined.
  | .rejected (.signature (.envelope .staleAuthority)) => return .contention
  | .rejected reason => return refused .operationRejected "fleet-turn" s!"{repr reason}"
  | .transactionConflict => return refused .conflict "replay" "transaction identity conflict"
  | .durableRejected reason => return durableRefusal reason
  | .contention => return .contention
  | .unavailable detail => return .unavailable detail.toUTF8.toList
  | .uncertain detail => return .uncertain detail.toUTF8.toList

/-- Receipt-only historical lookup. Absence never submits fresh work. -/
def provisionLookupLoaded (config : Config) (opened : Opened config)
    (bytes : List UInt8) : Outcome :=
  match ParticipantFactoryProvisioning.decodeIngress bytes with
  | none => refused .malformed "provision-factory-observe" "noncanonical signed ingress"
  | some ingress =>
    match ParticipantFactoryProvisioningReceiver.replay config.deployment.domain
        config.profile.semantics opened.durable ingress with
    | some (.ok receipt) =>
        match historicalReceipt config opened.durable receipt.transactionId receipt.eventId with
        | some original => .confirmed .replayed original
        | none => .uncertain "original receipt prefix unavailable".toUTF8.toList
    | some (.error _) => refused .conflict "replay" "transaction identity conflict"
    | none => .absent

/-- Receipt-only historical lookup of one retained ingress. Absence never
submits fresh work. -/
def fleetLookupLoaded (config : Config) (opened : Opened config)
    (bytes : List UInt8) : Outcome :=
  match FleetTurn.decodeIngress bytes with
  | none => refused .malformed "fleet-turn" "noncanonical signed ingress"
  | some ingress =>
    match FleetTurnReceiver.replay config.deployment.domain
        config.profile.semantics opened.durable ingress with
    | some (.ok receipt) =>
        match historicalReceipt config opened.durable receipt.transactionId receipt.eventId with
        | some original => .confirmed .replayed original
        | none => .uncertain "original receipt prefix unavailable".toUTF8.toList
    | some (.error _) => refused .conflict "replay" "transaction identity conflict"
    | none => .absent

/-- Exact receipt of one accepted transaction, by transaction id alone. It
names the original accepted prefix; a later tip does not replace it. -/
def receiptByTransactionLoaded (config : Config) (opened : Opened config)
    (transactionId : Digest) : Option Receipt := do
  let record ← opened.durable.image.accepted.find? (fun record => record.transactionId == transactionId)
  historicalReceipt config opened.durable transactionId record.event.eventId

/-- One topic event as a reader sees it. `height` is the admission height,
unique per accepted record on one Host: K authors' streams of one topic merge
into one ordered feed by `(height, sequence)`. A poll carries no receipt: a
historical receipt seals its prefix's world root, which costs a world-root
evaluation of that prefix, so a reader that wants one asks op 102 for that
transaction. -/
structure FleetPolledEvent where
  sequence : Nat
  eventKey : Digest
  parent : Option Digest
  transactionId : Digest
  height : Nat
  author : SubjectId
  payloadDigest : Digest
  /-- The exact payload from the accepted signed ingress, present only when
  its digest equals the one the entry committed. -/
  payload : Option (List UInt8)

structure FleetPollView where
  subject : SubjectId
  payer : Nat
  topic : List UInt8
  stream : Digest
  cursor : Nat
  head : Nat
  tail : Option Digest
  events : List FleetPolledEvent

def fleetJournalTurn {config : Config} (opened : Opened config) (transactionId : Digest) :
    Option FleetTurn.DecodedIngress := do
  let record ← opened.durable.image.accepted.find? (fun record => record.transactionId == transactionId)
  FleetTurn.decodeIngress record.event.canonicalBytes

def fleetPolledEvent (config : Config) (opened : Opened config)
    (item : Nat × StreamCell.Entry) : FleetPolledEvent :=
  let (sequence, entry) := item
  let record := entry.record
  let payload := (fleetJournalTurn opened record.transaction).bind fun ingress =>
    ingress.command.publication.bind fun publication =>
      if StreamCell.payloadDigest publication.payload = record.entry.payloadDigest
      then some publication.payload else none
  ⟨sequence, StreamCell.entryKey entry, entry.parent, record.transaction, record.height,
    record.author, record.entry.payloadDigest, payload⟩

def fleetPollMax : Nat := 64

/-- Events of `(observed account, topic)` strictly after `cursor`, behind a
current signed observation of that account. Reading an account's topics is
the account's own observe grant; a topic label confers nothing. -/
def fleetPollAuthorizedLoaded (config : Config) (opened : Opened config)
    (signedObservationBytes topic : List UInt8) (cursor limit : Nat) :
    IO (Except Refusal FleetPollView) := do
  if topic.isEmpty || topic.length > FleetTurn.maxTopicBytes then
    return .error { reason := .malformed, detail := "fleet topic must be 1..64 bytes" }
  match ← fleetObservedAccount config opened signedObservationBytes with
  | .error refusal => return .error refusal
  | .ok (subject, payer) =>
      let stream := FleetTurn.streamDigest config.deployment.domain payer topic
      let directory := opened.directory.directory
      let entries := FleetTurn.eventsSince config.deployment directory stream cursor
        (min limit fleetPollMax)
      let head := FleetTurn.streamHead config.deployment directory stream
      return .ok ⟨subject, payer, topic, stream, cursor, head.count, head.tail,
        entries.map (fleetPolledEvent config opened)⟩

structure FleetHeadView where
  subject : SubjectId
  payer : Nat
  /-- Accepted fleet turns paid by this account, in journal order. -/
  turns : Nat
  head : Option (Digest × Receipt)

/-- The newest accepted fleet turn paid by the observed account. This is a
scan of the accepted journal, decoding each retained ingress exactly. -/
def fleetHeadAuthorizedLoaded (config : Config) (opened : Opened config)
    (signedObservationBytes : List UInt8) : IO (Except Refusal FleetHeadView) := do
  match ← fleetObservedAccount config opened signedObservationBytes with
  | .error refusal => return .error refusal
  | .ok (subject, payer) =>
      let paid := opened.durable.image.accepted.filter fun record =>
        match FleetTurn.decodeIngress record.event.canonicalBytes with
        | some ingress => ingress.command.payer == payer
        | none => false
      let head := paid.getLast?.bind fun record =>
        (historicalReceipt config opened.durable record.transactionId record.event.eventId).map
          fun receipt => (record.transactionId, receipt)
      return .ok ⟨subject, payer, paid.length, head⟩
/-! ## The incoming ledger of an account (op 180)

A fleet turn's topic belongs to the PAYING account (`FleetTurn`, module doc),
so a payee cannot read who paid it from any topic of its own. Its ledger is a
read of the accepted journal: every fleet turn whose transfer names the
observed account as its destination, at the height that record took, released
behind a current signed observation of that account (the same gate as poll and
head). A room's concierge renews member windows from this view (PLACE §2.10:
the room account's `renew` ledger). It is a read; nothing is admitted here. -/

/-- One accepted fleet turn that paid the observed account. `topic` and
`payload` are the turn's own signed publication (empty when it published
nothing). -/
structure FleetIncomingEntry where
  height : Nat
  transactionId : Digest
  subject : SubjectId
  payer : Nat
  asset : Nat
  amount : Nat
  topic : List UInt8
  payload : List UInt8

/-- An empty `topic` matches every paying turn; otherwise only turns that
published on exactly that topic. -/
def fleetTopicMatches (topic : List UInt8) : Option FleetTurn.Publication → Bool
  | some publication => topic.isEmpty || publication.topic == topic
  | none => topic.isEmpty

/-- The ledger entry an accepted record contributes at `height`, if it is a
fleet turn paying `account` on `topic`. -/
def fleetIncomingEntry? (account : Nat) (topic : List UInt8) (height : Nat)
    (record : DurableReceiver.IntentRecord) : Option FleetIncomingEntry :=
  match FleetTurn.decodeIngress record.event.canonicalBytes with
  | none => none
  | some ingress =>
      match ingress.command.transfer with
      | none => none
      | some transfer =>
          if transfer.destination = account ∧
              fleetTopicMatches topic ingress.command.publication = true then
            some ⟨height, record.transactionId, ingress.command.subject, ingress.command.payer,
              transfer.asset, transfer.amount,
              (ingress.command.publication.map (·.topic)).getD [],
              (ingress.command.publication.map (·.payload)).getD []⟩
          else none

/-- Entries strictly above `after`, the record at list position `i` taking
height `start + i` (the journal's own height assignment: `sinceFrom`). -/
def fleetIncomingFrom (account : Nat) (topic : List UInt8) (after : Nat) :
    Nat → List DurableReceiver.IntentRecord → List FleetIncomingEntry
  | _, [] => []
  | height, record :: rest =>
      (if after < height then (fleetIncomingEntry? account topic height record).toList else []) ++
        fleetIncomingFrom account topic after (height + 1) rest

/-- **An entry is a payment to the account.** Every entry the record yields
decodes as a fleet turn whose transfer names `account` as destination, and
the entry repeats that turn's signer, payer, asset and amount exactly. -/
theorem fleetIncomingEntry?_sound {account : Nat} {topic : List UInt8} {height : Nat}
    {record : DurableReceiver.IntentRecord} {entry : FleetIncomingEntry}
    (found : fleetIncomingEntry? account topic height record = some entry) :
    ∃ ingress transfer, FleetTurn.decodeIngress record.event.canonicalBytes = some ingress ∧
      ingress.command.transfer = some transfer ∧ transfer.destination = account ∧
      entry.height = height ∧ entry.transactionId = record.transactionId ∧
      entry.subject = ingress.command.subject ∧ entry.payer = ingress.command.payer ∧
      entry.asset = transfer.asset ∧ entry.amount = transfer.amount := by
  unfold fleetIncomingEntry? at found
  split at found
  · cases found
  · rename_i ingress decoded
    split at found
    · cases found
    · rename_i transfer paid
      split at found
      · rename_i matched
        cases found
        exact ⟨ingress, transfer, decoded, paid, matched.1, rfl, rfl, rfl, rfl, rfl, rfl⟩
      · cases found

/-- **A payment to another account is never listed** (the refuting pole):
a record whose decoded transfer names a different destination yields nothing. -/
theorem fleetIncomingEntry?_other_destination {account : Nat} {topic : List UInt8}
    {height : Nat} {record : DurableReceiver.IntentRecord} {ingress : FleetTurn.DecodedIngress}
    {transfer : FleetTurn.Transfer}
    (decoded : FleetTurn.decodeIngress record.event.canonicalBytes = some ingress)
    (paid : ingress.command.transfer = some transfer) (other : transfer.destination ≠ account) :
    fleetIncomingEntry? account topic height record = none := by
  unfold fleetIncomingEntry?
  rw [decoded]
  simp only [paid]
  rw [if_neg (fun both => other both.1)]

/-- **The ledger is exact about what it names**: every entry is above
`after`, at the height of a record in the log, and is that record's own
payment to the account. -/
theorem fleetIncomingFrom_sound {account : Nat} {topic : List UInt8} {after : Nat} :
    ∀ {start : Nat} {log : List DurableReceiver.IntentRecord} {entry : FleetIncomingEntry},
      entry ∈ fleetIncomingFrom account topic after start log →
        after < entry.height ∧ ∃ index record, log[index]? = some record ∧
          entry.height = start + index ∧
          fleetIncomingEntry? account topic entry.height record = some entry
  | _, [], _, member => by simp [fleetIncomingFrom] at member
  | start, record :: rest, entry, member => by
      simp only [fleetIncomingFrom, List.mem_append] at member
      rcases member with here | later
      · split at here
        next above =>
          rcases found : fleetIncomingEntry? account topic start record with _ | yielded
          · rw [found] at here; simp at here
          · rw [found] at here
            simp only [Option.toList, List.mem_singleton] at here
            subst here
            obtain ⟨_, _, _, _, _, atHeight, _⟩ := fleetIncomingEntry?_sound found
            refine ⟨atHeight ▸ above, 0, record, rfl, by rw [atHeight]; simp, ?_⟩
            rw [atHeight]; exact found
        next => simp at here
      · obtain ⟨above, index, record', found, height, yields⟩ := fleetIncomingFrom_sound later
        exact ⟨above, index + 1, record', by simpa using found, by rw [height]; omega, yields⟩

/-- **The ledger misses no payment**: a record of the log above `after` that
yields an entry at its height is listed. -/
theorem fleetIncomingFrom_complete {account : Nat} {topic : List UInt8} {after : Nat} :
    ∀ {start : Nat} {log : List DurableReceiver.IntentRecord} {index : Nat}
      {record : DurableReceiver.IntentRecord} {entry : FleetIncomingEntry},
      log[index]? = some record → after < start + index →
      fleetIncomingEntry? account topic (start + index) record = some entry →
      entry ∈ fleetIncomingFrom account topic after start log
  | _, [], _, _, _, found, _, _ => by simp at found
  | start, head :: rest, 0, record, entry, found, above, yields => by
      simp only [List.getElem?_cons_zero, Option.some.injEq] at found
      subst found
      simp only [Nat.add_zero] at above yields
      simp [fleetIncomingFrom, above, yields]
  | start, head :: rest, index + 1, record, entry, found, above, yields => by
      simp only [List.getElem?_cons_succ] at found
      have lifted : after < start + 1 + index := by omega
      have shifted : fleetIncomingEntry? account topic (start + 1 + index) record = some entry := by
        rw [show start + 1 + index = start + (index + 1) by omega]; exact yields
      have next := fleetIncomingFrom_complete found lifted shifted
      simp only [fleetIncomingFrom, List.mem_append]
      exact Or.inr next

structure FleetIncomingView where
  subject : SubjectId
  account : Nat
  topic : List UInt8
  cursor : Nat
  /-- The current logical height (`logicalHeight`): the next record takes `tip + 1`. -/
  tip : Nat
  entries : List FleetIncomingEntry

/-- Payments to the observed account above `cursor`, at most `limit`
(bounded by `fleetPollMax`), behind a current signed observation of that
account by its reader. -/
def fleetIncomingAuthorizedLoaded (config : Config) (opened : Opened config)
    (signedObservationBytes topic : List UInt8) (cursor limit : Nat) :
    IO (Except Refusal FleetIncomingView) := do
  if topic.length > FleetTurn.maxTopicBytes then
    return .error { reason := .malformed, detail := "fleet topic must be 0..64 bytes" }
  match ← fleetObservedAccount config opened signedObservationBytes with
  | .error refusal => return .error refusal
  | .ok (subject, account) =>
      let entries := fleetIncomingFrom account topic cursor (config.genesisHeight + 1)
        opened.durable.image.accepted
      return .ok ⟨subject, account, topic, cursor, logicalHeight config opened.durable,
        entries.take (min limit fleetPollMax)⟩

#assert_axioms fleetIncomingEntry?_sound
#assert_axioms fleetIncomingEntry?_other_destination
#assert_axioms fleetIncomingFrom_sound
#assert_axioms fleetIncomingFrom_complete

/-! ## The pay cell (lane P2): session operations 103–107

One plan/assembly/submission/lookup quartet serves both pay command families;
the command frame (`DREGG/PAY/BOOK/v1` or `DREGG/PAY/ASSIGN/v1`) selects the
receiver. -/

/-- The signing plan for a pay command on one opened image.  It discloses no
pay decision; a signer key that the authority cell does not hold is refused. -/
def payPlanLoaded (config : Config) (opened : Opened config) (commandBytes : List UInt8) :
    Except String PayCellDomain.SigningPlan := do
  let height := logicalHeight config opened.durable
  let header ← match PayBookReceiver.commandCodec.decode commandBytes with
    | some command =>
        PayBookReceiver.signingHeader config.deployment config.profile
          ⟨config.federation, height⟩ opened.durable command
    | none =>
        match PayAssignmentReceiver.commandCodec.decode commandBytes with
        | some command =>
            PayAssignmentReceiver.signingHeader config.deployment config.profile
              ⟨config.federation, height⟩ opened.durable command
        | none => .error "noncanonical pay command"
  pure ⟨config.deployment.domain, config.profile.semantics, commandBytes,
    CredentialSignedEnvelopeController.headerCodec.encode header⟩

/-- Assembly transports one detached signature; submission rechecks it, the
current law, the exact pay and authority roots and the whole decision. -/
def payAssemble (plan : PayCellDomain.SigningPlan) (signature : List UInt8) :
    Except String (List UInt8) := do
  check (decide (signature.length = 64)) "pay signature must be 64 bytes"
  let header ← need "noncanonical pay header"
    (CredentialSignedEnvelopeController.headerCodec.decode plan.header)
  let envelope := CredentialSignedEnvelopeController.envelopeCodec.encode ⟨header, signature⟩
  if (PayBookReceiver.commandCodec.decode plan.commandBytes).isSome then
    pure (PayBookReceiver.ingressCodec.encode ⟨plan.commandBytes, envelope⟩)
  else if (PayAssignmentReceiver.commandCodec.decode plan.commandBytes).isSome then
    pure (PayAssignmentReceiver.ingressCodec.encode ⟨plan.commandBytes, envelope⟩)
  else .error "noncanonical pay plan command"

def paySubmitLoaded (config : Config) (opened : Opened config) (bytes : List UInt8) :
    IO Outcome := do
  let ambient := logicalHeight config opened.durable
  if (PayBookReceiver.decodeIngress bytes).isSome then
    match ← PayBookReceiver.receiveLoaded config.deployment config.profile
        ⟨config.federation, ambient⟩ config.signature config.transport opened.durable bytes with
    | .confirmed kind receipt => confirmed config kind receipt.transactionId receipt.eventId
    | .rejected reason => return refused .operationRejected "pay-book" s!"{repr reason}"
    | .transactionConflict => return refused .conflict "replay" "transaction identity conflict"
    | .durableRejected reason => return durableRefusal reason
    | .contention => return .contention
    | .unavailable detail => return .unavailable detail.toUTF8.toList
    | .uncertain detail => return .uncertain detail.toUTF8.toList
  else
    match ← PayAssignmentReceiver.receiveLoaded config.deployment config.profile
        ⟨config.federation, ambient⟩ config.signature config.transport opened.durable bytes with
    | .confirmed kind receipt => confirmed config kind receipt.transactionId receipt.eventId
    | .rejected reason => return refused .operationRejected "pay-assign" s!"{repr reason}"
    | .transactionConflict => return refused .conflict "replay" "transaction identity conflict"
    | .durableRejected reason => return durableRefusal reason
    | .contention => return .contention
    | .unavailable detail => return .unavailable detail.toUTF8.toList
    | .uncertain detail => return .uncertain detail.toUTF8.toList

/-- Receipt-only historical lookup of either pay family.  Absence never
submits fresh work. -/
def payLookupLoaded (config : Config) (opened : Opened config) (bytes : List UInt8) : Outcome :=
  let found : Option (Except Unit (Digest × Digest)) :=
    match PayBookReceiver.decodeIngress bytes with
    | some ingress =>
        (PayBookReceiver.replay config.deployment.domain config.profile.semantics opened.durable
          ingress).map (fun result => result.map fun receipt => (receipt.transactionId, receipt.eventId))
    | none =>
        match PayAssignmentReceiver.decodeIngress bytes with
        | some ingress =>
            (PayAssignmentReceiver.replay config.deployment.domain config.profile.semantics
              opened.durable ingress).map
              (fun result => result.map fun receipt => (receipt.transactionId, receipt.eventId))
        | none => some (.error ())
  match PayBookReceiver.decodeIngress bytes, PayAssignmentReceiver.decodeIngress bytes, found with
  | none, none, _ => refused .malformed "pay" "noncanonical signed ingress"
  | _, _, some (.ok (transactionId, eventId)) =>
      match historicalReceipt config opened.durable transactionId eventId with
      | some original => .confirmed .replayed original
      | none => .uncertain "original receipt prefix unavailable".toUTF8.toList
  | _, _, some (.error _) => refused .conflict "replay" "transaction identity conflict"
  | _, _, none => .absent

/-- The public view of the pay cell (no assignment map). -/
def payViewLoaded (config : Config) (opened : Opened config) : Except String PayCellDomain.View := do
  let pay ← need "pay cell unavailable" (PayCellDomain.load config.deployment opened.durable.snapshot)
  let factoryRoot ← match opened.directory.directory.slots config.deployment.factoryId with
    | .present before => pure before.payload.root
    | .absent => .error "factory unavailable"
  pure ⟨pay.cell.root, opened.authority.snapshot.cell.root, factoryRoot,
    PayCell.tariffOf pay.cell.logical,
    PayCell.nextFree pay.cell.logical, PayCellDomain.bookRows pay.cell.logical⟩

/-! ## Realm wells (lane K-WELL): session operations 123–125

123 = signing plan for a `DREGG/WELL/COMMAND/v1` command (`DREGG/WELL/PLAN/v1`),
124 = detached assembly `pair(plan, sig64)` → `DREGG/WELL/SIGNED/v1` ingress,
125 = submit (an exact resubmission of an accepted ingress returns its original
receipt as `replayed`). The well ledger is the operator-local CLI `well-ledger`. -/

def wellAmbient (config : Config) (opened : Opened config) : RealmWellReceiver.Ambient :=
  ⟨config.federation, logicalHeight config opened.durable, config.tariff.asset⟩

/-- The header the subject signs over this opened image. It discloses no
decision; a signer key the authority cell does not hold is refused. -/
def wellPlanLoaded (config : Config) (opened : Opened config) (commandBytes : List UInt8) :
    Except String RealmWellCodec.SigningPlan := do
  let command ← need "noncanonical realm well command"
    (RealmWellCodec.commandCodec.decode commandBytes)
  let header ← RealmWellReceiver.signingHeader config.deployment config.profile
    (wellAmbient config opened) opened.durable command
  pure ⟨config.deployment.domain, config.profile.semantics, commandBytes,
    CredentialSignedEnvelopeController.headerCodec.encode header⟩

def wellAssemble (plan : RealmWellCodec.SigningPlan) (signature : List UInt8) :
    Except String (List UInt8) := do
  check (decide (signature.length = 64)) "realm well signature must be 64 bytes"
  let header ← need "noncanonical realm well header"
    (CredentialSignedEnvelopeController.headerCodec.decode plan.header)
  check (RealmWellCodec.commandCodec.decode plan.commandBytes).isSome
    "noncanonical realm well plan command"
  let envelope := CredentialSignedEnvelopeController.envelopeCodec.encode ⟨header, signature⟩
  pure (RealmWellCodec.ingressCodec.encode ⟨plan.commandBytes, envelope⟩)

def wellSubmitLoaded (config : Config) (opened : Opened config) (bytes : List UInt8) :
    IO Outcome := do
  match ← RealmWellReceiver.receiveLoaded config.deployment config.profile
      (wellAmbient config opened) config.signature config.transport opened.durable bytes with
  | .confirmed kind receipt => confirmed config kind receipt.transactionId receipt.eventId
  | .rejected reason => return refused .operationRejected "realm-well" s!"{repr reason}"
  | .transactionConflict => return refused .conflict "replay" "transaction identity conflict"
  | .durableRejected reason => return refused .operationRejected "durable" s!"{repr reason}"
  | .contention => return .contention
  | .unavailable detail => return .unavailable detail.toUTF8.toList
  | .uncertain detail => return .uncertain detail.toUTF8.toList

/-- One realm well: its asset (= the well account), its realm (the well's
parent row), the well's balance, every other registered account's nonzero
balance in the asset, their sum and the asset's total (which conservation
keeps at zero). -/
structure WellLedgerRow where
  asset : Nat
  realm : Nat
  well : Int
  holders : List (Nat × Int)
  holdersSum : Int
  total : Int

/-- The operator's local ledger read: every realm well, and the credit asset's
own well balance. -/
structure WellLedger where
  bookRoot : Digest
  creditAsset : Nat
  creditWell : Int
  creditTotal : Int
  wells : List WellLedgerRow

def wellLedgerLoaded (config : Config) (opened : Opened config) : Except String WellLedger := do
  let authority ← need "authority unavailable"
    (CredentialAuthorityDomainReceiver.loadDeployment config.deployment opened.durable.snapshot)
  let book ← need "book unavailable"
    (ResourceBirthController.Concrete.observeCell config.deployment opened.directory.directory
      config.deployment.resourceBookId .resourceBook)
  let logical := CanonicalResourceKernel.logicalBook book.payload.logical
  let parent := authority.snapshot.authState.parent
  let accounts := logical.accounts.sort (· ≤ ·)
  let wells := accounts.filterMap fun asset => (parent asset).map fun realm =>
    let holders := (accounts.filter (· ≠ asset)).filterMap fun holder =>
      let balance := logical.balance holder asset
      if balance = 0 then none else some (holder, balance)
    let holdersSum := (holders.map Prod.snd).sum
    ({ asset, realm, well := logical.balance asset asset, holders, holdersSum,
       total := logical.balance asset asset + holdersSum } : WellLedgerRow)
  let credit := config.tariff.asset
  pure ⟨book.payload.root, credit, logical.balance credit credit, logical.totalAsset credit, wells⟩

def wellLedger (config : Config) : IO (Except String WellLedger) := do
  match ← openExisting config with
  | .error detail => return .error detail
  | .ok opened => return wellLedgerLoaded config opened

/-! ## The clock (K-CLOCK): session operations 126-129

126 = tick signing plan, 127 = detached assembly, 128 = submit, 129 = public
clock view.  The command is authored by `author clock-tick`; the signer is a
genesis clock ticker presenting its `C_tick` on the clock cell, under the
clock cell's law (`NativeHostGenesis.clock_subject_confined`). -/

def clockPlanLoaded (config : Config) (opened : Opened config) (commandBytes : List UInt8) :
    Except String ClockTickReceiver.SigningPlan := do
  let height := logicalHeight config opened.durable
  let some command := ClockTickReceiver.commandCodec.decode commandBytes
    | .error "noncanonical clock tick command"
  let header ← ClockTickReceiver.signingHeader config.deployment config.profile
    ⟨config.federation, height⟩ opened.durable command
  pure ⟨config.deployment.domain, config.profile.semantics, commandBytes,
    CredentialSignedEnvelopeController.headerCodec.encode header⟩

def clockAssemble (plan : ClockTickReceiver.SigningPlan) (signature : List UInt8) :
    Except String (List UInt8) := do
  check (decide (signature.length = 64)) "clock tick signature must be 64 bytes"
  let header ← need "noncanonical clock tick header"
    (CredentialSignedEnvelopeController.headerCodec.decode plan.header)
  let envelope := CredentialSignedEnvelopeController.envelopeCodec.encode ⟨header, signature⟩
  if (ClockTickReceiver.commandCodec.decode plan.commandBytes).isSome then
    pure (ClockTickReceiver.ingressCodec.encode ⟨plan.commandBytes, envelope⟩)
  else .error "noncanonical clock plan command"

def clockSubmitLoaded (config : Config) (opened : Opened config) (bytes : List UInt8) :
    IO Outcome := do
  let ambient := logicalHeight config opened.durable
  match ← ClockTickReceiver.receiveLoaded config.deployment config.profile
      ⟨config.federation, ambient⟩ config.signature config.transport opened.durable bytes with
  | .confirmed kind receipt => confirmed config kind receipt.transactionId receipt.eventId
  | .rejected reason => return refused .operationRejected "clock-tick" s!"{repr reason}"
  | .transactionConflict => return refused .conflict "replay" "transaction identity conflict"
  | .durableRejected reason => return durableRefusal reason
  | .contention => return .contention
  | .unavailable detail => return .unavailable detail.toUTF8.toList
  | .uncertain detail => return .uncertain detail.toUTF8.toList

/-- The public view of the clock: its value and the two roots a tick pins. -/
def clockViewLoaded (config : Config) (opened : Opened config) : Except String ClockCellDomain.View := do
  let clock ← need "clock cell unavailable" (ClockCellDomain.load config.deployment opened.durable.snapshot)
  pure ⟨clock.cell.root, opened.authority.snapshot.cell.root, clock.clock⟩

/-- Session operation 112 (PAY P3b): the public enrollment view — the hour of
the deployment clock and every self-enrolled Mini key with its subject, ssh
blob, lease and book index.  No key is needed; nothing private is in it. -/
def payEnrolmentViewLoaded (config : Config) (opened : Opened config) :
    Except String PayCellDomain.EnrolmentView := do
  let pay ← need "pay cell unavailable" (PayCellDomain.load config.deployment opened.durable.snapshot)
  let clock ← need "clock cell unavailable" (ClockCellDomain.load config.deployment opened.durable.snapshot)
  pure (PayCellDomain.enrolmentView clock.clock.now pay.cell.logical)

/-! ## Payment observation (lane P3): session operations 108–111

The observer's report (`DREGG/PAY/OBSERVATION/v2`) has its own
plan/assembly/submission/lookup quartet; its signed ingress is
`DREGG/PAY/OBSERVATION/SIGNED/v2`. -/

/-- The signing plan for a report on one opened image.  It discloses no
decision (`PayObservationReceiver.signingHeader`); a signer key the authority
cell does not hold is refused. -/
def payObservationPlanLoaded (config : Config) (opened : Opened config) (commandBytes : List UInt8) :
    Except String PayCellDomain.SigningPlan := do
  let command ← need "noncanonical pay observation command"
    (PayObservation.commandCodec.decode commandBytes)
  let header ← PayObservationReceiver.signingHeader config.deployment config.profile
    ⟨config.federation, logicalHeight config opened.durable⟩ opened.durable command
  pure ⟨config.deployment.domain, config.profile.semantics, commandBytes,
    CredentialSignedEnvelopeController.headerCodec.encode header⟩

def payObservationAssemble (plan : PayCellDomain.SigningPlan) (signature : List UInt8) :
    Except String (List UInt8) := do
  check (decide (signature.length = 64)) "pay observation signature must be 64 bytes"
  let header ← need "noncanonical pay observation header"
    (CredentialSignedEnvelopeController.headerCodec.decode plan.header)
  check (PayObservation.commandCodec.decode plan.commandBytes).isSome
    "noncanonical pay observation plan command"
  let envelope := CredentialSignedEnvelopeController.envelopeCodec.encode ⟨header, signature⟩
  pure (PayObservation.ingressCodec.encode ⟨plan.commandBytes, envelope⟩)

def payObservationSubmitLoaded (config : Config) (opened : Opened config) (bytes : List UInt8) :
    IO Outcome := do
  match ← PayObservationReceiver.receiveLoaded config.deployment config.profile
      ⟨config.federation, logicalHeight config opened.durable⟩ config.signature config.transport
      opened.durable bytes with
  | .confirmed kind receipt => confirmed config kind receipt.transactionId receipt.eventId
  | .rejected reason => return refused .operationRejected "pay-observation" s!"{repr reason}"
  | .transactionConflict => return refused .conflict "replay" "transaction identity conflict"
  | .durableRejected reason => return refused .operationRejected "durable" s!"{repr reason}"
  | .contention => return .contention
  | .unavailable detail => return .unavailable detail.toUTF8.toList
  | .uncertain detail => return .uncertain detail.toUTF8.toList

/-- Receipt-only historical lookup of a report.  Absence never submits. -/
def payObservationLookupLoaded (config : Config) (opened : Opened config) (bytes : List UInt8) :
    Outcome :=
  match PayObservationReceiver.decodeIngress bytes with
  | none => refused .malformed "pay-observation" "noncanonical signed ingress"
  | some ingress =>
      match PayObservationReceiver.replay config.deployment.domain config.profile.semantics
          opened.durable ingress with
      | none => .absent
      | some (.error _) => refused .conflict "replay" "transaction identity conflict"
      | some (.ok receipt) =>
          match historicalReceipt config opened.durable receipt.transactionId receipt.eventId with
          | some original => .confirmed .replayed original
          | none => .uncertain "original receipt prefix unavailable".toUTF8.toList

/-! ## Self-enrollment (lane P3b-2): session operations 117–120

The observer's submission of one enrollment-index transfer
(`DREGG/PAY/SELF-ENROL/v1`) has its own plan/assembly/submission/lookup
quartet; its signed ingress is `DREGG/PAY/SELF-ENROL/SIGNED/v1`.  (113–116 are
P6's.)  The plan runs the native verifier on the memo, because the decision
the observer signs depends on both possession bits. -/

def payEnrolAmbient (config : Config) (opened : Opened config) : PayEnrolReceiver.Ambient :=
  ⟨config.federation, logicalHeight config opened.durable, config.tariff⟩

def payEnrolPlanLoaded (config : Config) (opened : Opened config) (commandBytes : List UInt8) :
    IO (Except String PayCellDomain.SigningPlan) := do
  let some command := PayEnrolReceiver.commandCodec.decode commandBytes
    | return .error "noncanonical pay enrolment command"
  match ← PayEnrolReceiver.signingHeader config.deployment config.profile
      (payEnrolAmbient config opened) opened.durable config.signature command with
  | .error detail => return .error detail
  | .ok header =>
      return .ok ⟨config.deployment.domain, config.profile.semantics, commandBytes,
        CredentialSignedEnvelopeController.headerCodec.encode header⟩

def payEnrolAssemble (plan : PayCellDomain.SigningPlan) (signature : List UInt8) :
    Except String (List UInt8) := do
  check (decide (signature.length = 64)) "pay enrolment signature must be 64 bytes"
  let header ← need "noncanonical pay enrolment header"
    (CredentialSignedEnvelopeController.headerCodec.decode plan.header)
  check (PayEnrolReceiver.commandCodec.decode plan.commandBytes).isSome
    "noncanonical pay enrolment plan command"
  let envelope := CredentialSignedEnvelopeController.envelopeCodec.encode ⟨header, signature⟩
  pure (PayEnrolReceiver.ingressCodec.encode ⟨plan.commandBytes, envelope⟩)

def payEnrolSubmitLoaded (config : Config) (opened : Opened config) (bytes : List UInt8) :
    IO Outcome := do
  match ← PayEnrolReceiver.receiveLoaded config.deployment config.profile
      (payEnrolAmbient config opened) config.signature config.transport opened.durable bytes with
  | .confirmed kind receipt => confirmed config kind receipt.transactionId receipt.eventId
  | .rejected reason => return refused .operationRejected "pay-enrol" s!"{repr reason}"
  | .transactionConflict => return refused .conflict "replay" "transaction identity conflict"
  | .durableRejected reason => return refused .operationRejected "durable" s!"{repr reason}"
  | .contention => return .contention
  | .unavailable detail => return .unavailable detail.toUTF8.toList
  | .uncertain detail => return .uncertain detail.toUTF8.toList

/-- Receipt-only historical lookup of an enrolment submission.  Absence never
submits. -/
def payEnrolLookupLoaded (config : Config) (opened : Opened config) (bytes : List UInt8) :
    Outcome :=
  match PayEnrolReceiver.decodeIngress bytes with
  | none => refused .malformed "pay-enrol" "noncanonical signed ingress"
  | some ingress =>
      match PayEnrolReceiver.replay config.deployment.domain config.profile.semantics
          opened.durable ingress with
      | none => .absent
      | some (.error _) => refused .conflict "replay" "transaction identity conflict"
      | some (.ok receipt) =>
          match historicalReceipt config opened.durable receipt.transactionId receipt.eventId with
          | some original => .confirmed .replayed original
          | none => .uncertain "original receipt prefix unavailable".toUTF8.toList

/-- One assigned deposit index and the Book balance of its payer in the
tariff's asset. -/
structure PayLedgerRow where
  index : Nat
  account : Nat
  balance : Int

/-- The operator's local ledger read (not a socket operation: it names the
assignment map, which the public view withholds): the pay root, tariff and
the deployment clock (the clock cell's), the issuer well of the tariff asset, and each assigned payer's balance. -/
structure PayLedger where
  payRoot : Digest
  tariff : Option PayTariff.Tariff
  clock : Option ClockCell.Clock
  asset : Nat
  well : Int
  /-- The asset's Book total, well included (conserved by every admitted batch). -/
  total : Int
  rows : List PayLedgerRow

def payLedgerLoaded (config : Config) (opened : Opened config) : Except String PayLedger := do
  let pay ← need "pay cell unavailable" (PayCellDomain.load config.deployment opened.durable.snapshot)
  let book ← need "book unavailable"
    (ResourceBirthController.Concrete.observeCell config.deployment opened.directory.directory
      config.deployment.resourceBookId .resourceBook)
  let logical := CanonicalResourceKernel.logicalBook book.payload.logical
  let store := pay.cell.logical
  let clock := (ClockCellDomain.load config.deployment opened.durable.snapshot).map (·.clock)
  let asset := ((PayCell.tariffOf store).map PayTariff.Tariff.asset).getD 0
  let rows := (List.range (PayCell.nextFree store)).filterMap fun index =>
    (PayCell.assignmentAt store index).map fun account => ⟨index, account, logical.balance account asset⟩
  pure ⟨pay.cell.root, PayCell.tariffOf store, clock, asset,
    logical.balance asset asset, logical.totalAsset asset, rows⟩

def payLedger (config : Config) : IO (Except String PayLedger) := do
  match ← openExisting config with
  | .error detail => return .error detail
  | .ok opened => return payLedgerLoaded config opened

/-! ## Purse refill (lane P6): session operations 113–116

The account owner's refill (`DREGG/PAY/REFILL/v1`) has its own
plan/assembly/submission/lookup quartet; its signed ingress is
`DREGG/PAY/REFILL/SIGNED/v1`.  The plan is P2's shared `SigningPlan`. -/

def payRefillPlanLoaded (config : Config) (opened : Opened config) (commandBytes : List UInt8) :
    Except String PayCellDomain.SigningPlan := do
  let command ← need "noncanonical pay refill command"
    (PurseRefillReceiver.commandCodec.decode commandBytes)
  let header ← PurseRefillReceiver.signingHeader config.deployment config.profile
    ⟨config.federation, logicalHeight config opened.durable⟩ opened.durable command
  pure ⟨config.deployment.domain, config.profile.semantics, commandBytes,
    CredentialSignedEnvelopeController.headerCodec.encode header⟩

def payRefillAssemble (plan : PayCellDomain.SigningPlan) (signature : List UInt8) :
    Except String (List UInt8) := do
  check (decide (signature.length = 64)) "pay refill signature must be 64 bytes"
  let header ← need "noncanonical pay refill header"
    (CredentialSignedEnvelopeController.headerCodec.decode plan.header)
  check (PurseRefillReceiver.commandCodec.decode plan.commandBytes).isSome
    "noncanonical pay refill plan command"
  let envelope := CredentialSignedEnvelopeController.envelopeCodec.encode ⟨header, signature⟩
  pure (PurseRefillReceiver.ingressCodec.encode ⟨plan.commandBytes, envelope⟩)

def payRefillSubmitLoaded (config : Config) (opened : Opened config) (bytes : List UInt8) :
    IO Outcome := do
  match ← PurseRefillReceiver.receiveLoaded config.deployment config.profile
      ⟨config.federation, logicalHeight config opened.durable⟩ config.signature config.transport
      opened.durable bytes with
  | .confirmed kind receipt => confirmed config kind receipt.transactionId receipt.eventId
  | .rejected reason => return refused .operationRejected "pay-refill" s!"{repr reason}"
  | .transactionConflict => return refused .conflict "replay" "transaction identity conflict"
  | .durableRejected reason => return refused .operationRejected "durable" s!"{repr reason}"
  | .contention => return .contention
  | .unavailable detail => return .unavailable detail.toUTF8.toList
  | .uncertain detail => return .uncertain detail.toUTF8.toList

/-- Receipt-only historical lookup of a refill.  Absence never submits. -/
def payRefillLookupLoaded (config : Config) (opened : Opened config) (bytes : List UInt8) :
    Outcome :=
  match PurseRefillReceiver.decodeIngress bytes with
  | none => refused .malformed "pay-refill" "noncanonical signed ingress"
  | some ingress =>
      match PurseRefillReceiver.replay config.deployment.domain config.profile.semantics
          opened.durable ingress with
      | none => .absent
      | some (.error _) => refused .conflict "replay" "transaction identity conflict"
      | some (.ok receipt) =>
          match historicalReceipt config opened.durable receipt.transactionId receipt.eventId with
          | some original => .confirmed .replayed original
          | none => .uncertain "original receipt prefix unavailable".toUTF8.toList

/-! ## Job money (lane C3 K-JOB-MONEY): session operations 131–134

Fund, claim and settle (`DREGG/JOB/MONEY/v1`) share one
plan/assembly/submission/lookup quartet; the signed ingress is
`DREGG/JOB/MONEY/SIGNED/v1`.  The plan is P2's shared `SigningPlan`. -/

def jobMoneyPlanLoaded (config : Config) (opened : Opened config) (commandBytes : List UInt8) :
    Except String PayCellDomain.SigningPlan := do
  let command ← need "noncanonical job money command"
    (JobMoneyReceiver.commandCodec.decode commandBytes)
  let header ← JobMoneyReceiver.signingHeader config.deployment config.profile
    ⟨config.federation, logicalHeight config opened.durable⟩ opened.durable command
  pure ⟨config.deployment.domain, config.profile.semantics, commandBytes,
    CredentialSignedEnvelopeController.headerCodec.encode header⟩

def jobMoneyAssemble (plan : PayCellDomain.SigningPlan) (signature : List UInt8) :
    Except String (List UInt8) := do
  check (decide (signature.length = 64)) "job money signature must be 64 bytes"
  let header ← need "noncanonical job money header"
    (CredentialSignedEnvelopeController.headerCodec.decode plan.header)
  check (JobMoneyReceiver.commandCodec.decode plan.commandBytes).isSome
    "noncanonical job money plan command"
  let envelope := CredentialSignedEnvelopeController.envelopeCodec.encode ⟨header, signature⟩
  pure (JobMoneyReceiver.ingressCodec.encode ⟨plan.commandBytes, envelope⟩)

def jobMoneySubmitLoaded (config : Config) (opened : Opened config) (bytes : List UInt8) :
    IO Outcome := do
  match ← JobMoneyReceiver.receiveLoaded config.deployment config.profile
      ⟨config.federation, logicalHeight config opened.durable⟩ config.signature config.transport
      opened.durable bytes with
  | .confirmed kind receipt => confirmed config kind receipt.transactionId receipt.eventId
  | .rejected reason => return refused .operationRejected "job-money" s!"{repr reason}"
  | .transactionConflict => return refused .conflict "replay" "transaction identity conflict"
  | .durableRejected reason => return refused .operationRejected "durable" s!"{repr reason}"
  | .contention => return .contention
  | .unavailable detail => return .unavailable detail.toUTF8.toList
  | .uncertain detail => return .uncertain detail.toUTF8.toList

/-- Receipt-only historical lookup of a job-money turn.  Absence never submits. -/
def jobMoneyLookupLoaded (config : Config) (opened : Opened config) (bytes : List UInt8) :
    Outcome :=
  match JobMoneyReceiver.decodeIngress bytes with
  | none => refused .malformed "job-money" "noncanonical signed ingress"
  | some ingress =>
      match JobMoneyReceiver.replay config.deployment.domain config.profile.semantics
          opened.durable ingress with
      | none => .absent
      | some (.error _) => refused .conflict "replay" "transaction identity conflict"
      | some (.ok receipt) =>
          match historicalReceipt config opened.durable receipt.transactionId receipt.eventId with
          | some original => .confirmed .replayed original
          | none => .uncertain "original receipt prefix unavailable".toUTF8.toList

/-- The operator's local read of one job (not a socket operation): its root,
its eight money fields, and what the Book's held account for it (the account
with the job's id) holds in the credit asset. -/
structure PayJob where
  job : Nat
  root : Digest
  state : JobMoney.Job
  bookHeld : Int

def payJobLoaded (config : Config) (opened : Opened config) (job : Nat) :
    Except String PayJob := do
  let .present packed := opened.directory.directory.slots job
    | .error s!"job {job} absent"
  let cell ← need s!"job {job} is not a declared object"
    (CanonicalCellRegistry.selectDeclared config.deployment job .object packed)
  let state ← need s!"job {job} has no money fields" (JobMoney.readJob job cell.logical)
  let pay ← need "pay cell unavailable" (PayCellDomain.load config.deployment opened.durable.snapshot)
  let book ← need "book unavailable"
    (ResourceBirthController.Concrete.observeCell config.deployment opened.directory.directory
      config.deployment.resourceBookId .resourceBook)
  let asset := ((PayCell.tariffOf pay.cell.logical).map PayTariff.Tariff.asset).getD 0
  let logical := CanonicalResourceKernel.logicalBook book.payload.logical
  pure ⟨job, cell.root, state, logical.balance (JobMoney.heldAccount job) asset⟩

def payJob (config : Config) (job : Nat) : IO (Except String PayJob) := do
  match ← openExisting config with
  | .error detail => return .error detail
  | .ok opened => return payJobLoaded config opened job

/-- The operator's local explanation of one job-money command (not a socket
operation: a public submission stays blind, MR's rule). It runs the receiver's
own preparation (`JobMoneyReceiver.prepare`: the money decision, the claimer's
membership, the pinned job law at the clock) on the Store as it is now, and
names the refusal it reaches. It signs nothing and commits nothing. -/
def jobMoneyExplain (config : Config) (commandBytes : List UInt8) : IO (Except String String) := do
  match ← openExisting config with
  | .error detail => return .error detail
  | .ok opened =>
      match JobMoneyReceiver.commandCodec.decode commandBytes with
      | none => return .error "noncanonical job money command"
      | some command =>
          match JobMoneyReceiver.prepare config.deployment config.profile
              ⟨config.federation, logicalHeight config opened.durable⟩ opened.durable command with
          | .ok _ => return .ok "prepared: the receiver would admit this command up to its signature"
          | .error reason => return .ok s!"refused {(repr reason).pretty}"

/-- The operator's local read of one AgentGrain purse (not a socket
operation): its root and its four coordinates. -/
structure PayPurse where
  task : Nat
  root : Digest
  state : AgentGrain.State

def payPurseLoaded (config : Config) (opened : Opened config) (task : Nat) :
    Except String PayPurse := do
  let .present packed := opened.directory.directory.slots task
    | .error s!"purse {task} absent"
  let purse ← need s!"purse {task} is not a declared object"
    (CanonicalCellRegistry.selectDeclared config.deployment task .object packed)
  let state ← need s!"purse {task} is not an AgentGrain task"
    (AgentGrain.readState task purse.logical)
  pure ⟨task, purse.root, state⟩

def payPurse (config : Config) (task : Nat) : IO (Except String PayPurse) := do
  match ← openExisting config with
  | .error detail => return .error detail
  | .ok opened => return payPurseLoaded config opened task

/-! ## Certify (the checkpoint path)

170 = certify signing plan, 171 = detached assembly, 172 = submit, 173 = public
system view.  The command is authored by `author certify` from the view's head
and chain; the signer is any subject the factory law admits in capability mode
for `authority/operation/certify` (today the operator's ticker). -/

def certifyPlanLoaded (config : Config) (opened : Opened config) (commandBytes : List UInt8) :
    Except String CertifyReceiver.SigningPlan := do
  let height := logicalHeight config opened.durable
  let some command := CertifyReceiver.commandCodec.decode commandBytes
    | .error "noncanonical certify command"
  let header ← CertifyReceiver.signingHeader config.deployment config.profile
    ⟨config.federation, height⟩ opened.durable command
  pure ⟨config.deployment.domain, config.profile.semantics, commandBytes,
    CredentialSignedEnvelopeController.headerCodec.encode header⟩

def certifyAssemble (plan : CertifyReceiver.SigningPlan) (signature : List UInt8) :
    Except String (List UInt8) := do
  check (decide (signature.length = 64)) "certify signature must be 64 bytes"
  let header ← need "noncanonical certify header"
    (CredentialSignedEnvelopeController.headerCodec.decode plan.header)
  let envelope := CredentialSignedEnvelopeController.envelopeCodec.encode ⟨header, signature⟩
  if (CertifyReceiver.commandCodec.decode plan.commandBytes).isSome then
    pure (CertifyReceiver.ingressCodec.encode ⟨plan.commandBytes, envelope⟩)
  else .error "noncanonical certify plan command"

def certifySubmitLoaded (config : Config) (opened : Opened config) (bytes : List UInt8) :
    IO Outcome := do
  let ambient := logicalHeight config opened.durable
  match ← CertifyReceiver.receiveLoaded config.deployment config.profile
      ⟨config.federation, ambient⟩ config.signature config.transport opened.durable bytes with
  | .confirmed kind receipt => confirmed config kind receipt.transactionId receipt.eventId
  | .rejected reason => return refused .operationRejected "certify" s!"{repr reason}"
  | .transactionConflict => return refused .conflict "replay" "transaction identity conflict"
  | .durableRejected reason => return durableRefusal reason
  | .contention => return .contention
  | .unavailable detail => return .unavailable detail.toUTF8.toList
  | .uncertain detail => return .uncertain detail.toUTF8.toList

/-- The public view of the system cell: its value, the roots a certify pins,
and the head a certify would name now with that head's chain value.  The head
and its chain are public (every receipt carries a height and a root). -/
def certifyViewLoaded (config : Config) (opened : Opened config) :
    Except String SystemCellDomain.View := do
  let system ← need "system cell unavailable"
    (SystemCellDomain.load config.deployment opened.durable.snapshot)
  let factoryRoot ← match opened.directory.directory.slots config.deployment.factoryId with
    | .present before => pure before.payload.root
    | .absent => .error "factory unavailable"
  pure ⟨system.cell.root, opened.authority.snapshot.cell.root, factoryRoot, system.system,
    opened.durable.height, opened.durable.chain⟩
/-- Who may read a submission's refusal. Every refusal is uniform
(`publicSubmissionOutcome`) except a renounce's gate refusal, which exists only
after the signer's signature verified (`CapabilityRenounce.HolderRefusal`) and
concerns only the signer's own holding. -/
inductive Disclosure where
  | uniform
  | toSigner
  deriving DecidableEq, Repr

def submitRenounceVia (transport : DurableReceiverIO.Transport) (config : Config)
    (opened : Opened config) (bytes : List UInt8)
    (confirm : DurableReceiverIO.Confirmation → Digest → Digest → IO Outcome) :
    IO (Outcome × Disclosure) := do
  let height := logicalHeight config opened.durable
  match ← CapabilityRenounce.receiveLoaded config.deployment config.profile.semantics
      ⟨config.federation, height⟩ config.signature transport opened.durable bytes with
  | .confirmed kind receipt => return (← confirm kind receipt.transactionId receipt.eventId, .uniform)
  | .refusedToHolder reason =>
      return (refused .operationRejected "renounce" s!"{repr reason}", .toSigner)
  | .rejected reason => return (refused .operationRejected "renounce" s!"{repr reason}", .uniform)
  | .transactionConflict =>
      return (refused .conflict "replay" "transaction identity conflict", .uniform)
  | .durableRejected reason =>
      return (refused .operationRejected "durable" s!"{repr reason}", .uniform)
  | .contention => return (.contention, .uniform)
  | .unavailable detail => return (.unavailable detail.toUTF8.toList, .uniform)
  | .uncertain detail => return (.uncertain detail.toUTF8.toList, .uniform)

/-- The served renounce: `submitRenounceVia` over the Store's own writer. -/
def submitRenounceWith (config : Config) (opened : Opened config) (bytes : List UInt8)
    (confirm : DurableReceiverIO.Confirmation → Digest → Digest → IO Outcome) :
    IO (Outcome × Disclosure) :=
  submitRenounceVia config.transport config opened bytes confirm

/-- The submission path, over the Store writer it is handed. The served path
passes `config.transport` (`submitLoadedWith`); the dry run (`Host.DryRun`,
op 130) passes a writer that never appends, so both run this one program. -/
def submitLoadedVia (transport : DurableReceiverIO.Transport) (config : Config)
    (opened : Opened config) (call : SignedCall)
    (confirm : DurableReceiverIO.Confirmation → Digest → Digest → IO Outcome) : IO Outcome := do
  let height := logicalHeight config opened.durable
  match call with
  | .renounce bytes => return (← submitRenounceVia transport config opened bytes confirm).1
  | .revoke bytes =>
      match ← CapabilityRevocationReceiver.receiveLoaded config.deployment config.profile
          ⟨config.federation, height⟩ config.signature transport opened.durable bytes with
      | .confirmed kind receipt => confirm kind receipt.transactionId receipt.eventId
      | .rejected reason => return refused .operationRejected "revoke" s!"{repr reason}"
      | .transactionConflict => return refused .conflict "replay" "transaction identity conflict"
      | .durableRejected reason => return durableRefusal reason
      | .contention => return .contention
      | .unavailable detail => return .unavailable detail.toUTF8.toList
      | .uncertain detail => return .uncertain detail.toUTF8.toList
  | .delegate bytes =>
      match ← CapabilityDelegationReceiver.receiveLoaded config.deployment config.profile
          ⟨config.federation, height⟩ config.signature transport opened.durable bytes with
      | .confirmed kind receipt => confirm kind receipt.transactionId receipt.eventId
      | .rejected reason => return refused .operationRejected "delegate" s!"{repr reason}"
      | .transactionConflict => return refused .conflict "replay" "transaction identity conflict"
      | .durableRejected reason => return durableRefusal reason
      | .contention => return .contention
      | .unavailable detail => return .unavailable detail.toUTF8.toList
      | .uncertain detail => return .uncertain detail.toUTF8.toList
  | .birth bytes =>
      if (GrainResourceBirthPolicyController.decodeIngress bytes).isSome then
        let tariff := config.grainBirthTariffValue.toOption
        let ambient : DeclaredResourceController.Ambient := ⟨config.federation, height⟩
        match ← GrainResourceBirthReceiver.receiveLoaded config.profile config.deployment
            opened.pins tariff ambient config.signature transport
            opened.durable bytes with
        | .historical receipt => return ← confirm .replayed receipt.transactionId receipt.eventId
        | .confirmed kind receipt => return ← confirm kind receipt.transactionId receipt.eventId
        | .rejected _ => return refused .operationRejected "grain-birth" "request refused"
        | .contention => return .contention
        | .unavailable detail => return .unavailable detail.toUTF8.toList
        | .uncertain detail => return .uncertain detail.toUTF8.toList
      match ← ResourceBirthReceiver.receiveLoaded config.profile config.deployment opened.pins
          config.signature transport opened.durable height bytes with
      | .confirmed kind receipt => confirm kind receipt.transactionId receipt.eventId
      | .rejected reason => return refused (birthReason reason) "birth" (birthRejection reason)
      | .contention => return .contention
      | .unavailable detail => return .unavailable detail.toUTF8.toList
      | .uncertain detail => return .uncertain detail.toUTF8.toList
  | .install bytes =>
      match ← PolicyInstallReceiver.receiveLoaded config.profile config.deployment config.signature
          transport opened.durable config.federation height bytes with
      | .confirmed kind receipt => confirm kind receipt.transactionId receipt.eventId
      | .rejected reason => return refused .operationRejected "install" s!"{repr reason}"
      | .durableRejected reason => return durableRefusal reason
      | .contention => return .contention
      | .unavailable detail => return .unavailable detail.toUTF8.toList
      | .uncertain detail => return .uncertain detail.toUTF8.toList
  | .invoke signed =>
      match DeclaredResourceController.commandCodec.decode signed.commandBytes with
      | none => return refused .malformed "invoke" "noncanonical command"
      | some command =>
          -- The operator's synchronous budget, before the referee re-executes the claim.
          if let some steps := overSyncBudget config command then
            return refused .operationRejected "overSyncBudget" (overSyncBudgetDetail config steps)
          match ← DeclaredResourceController.withAcceptedLoadedFrom config.deployment config.profile
              ⟨config.federation, height⟩ config.signature opened.durable (some opened.directory) signed
              (fun _ shape accepted => do
                let intent := accepted.dataIntent shape
                if (FnConsumerProgress.recognizedLegacyIntentAnyGateway?
                    config.deployment.domain config.profile.semantics intent).isSome then
                  return .rejected .physicalPreparation
                return .settlement (← DurableReceiverIO.receiveLoaded
                  transport ResourceBirthCodec.rootBytes opened.durable intent))
              pure with
          | .replayed record => confirm .replayed record.transactionId record.event.event.eventId
          | .rejected reason => return refused .operationRejected "invoke" s!"{repr reason}"
          | .transactionConflict => return refused .conflict "replay" "transaction identity conflict"
          | .unavailable detail => return .unavailable detail.toUTF8.toList
          | .settlement result =>
              match result with
              | .confirmed kind _ =>
                  confirm kind
                    (DeclaredResourceController.transactionId config.deployment.domain config.profile.semantics command)
                    (DeclaredResourceController.invocationEvent config.deployment.domain config.profile.semantics command signed).eventId
              | .rejected (.durable .insufficientBudget) =>
                  return refused .operationRejected "durable"
                    (meterShortfallDetail (opened.durable.snapshot.model.available .proofWork)
                      ((command.run.map fun claim => claim.steps).getD 0))
              | .rejected reason => return durableRefusal reason
              | .contention => return .contention
              | .unavailable detail => return .unavailable detail.toUTF8.toList
              | .uncertain detail => return .uncertain detail.toUTF8.toList

def submitLoadedWith (config : Config) (opened : Opened config) (call : SignedCall)
    (confirm : DurableReceiverIO.Confirmation → Digest → Digest → IO Outcome) : IO Outcome :=
  submitLoadedVia config.transport config opened call confirm

def submitLoaded (config : Config) (opened : Opened config) (call : SignedCall) : IO Outcome :=
  submitLoadedWith config opened call (confirmed config)

/-- The outcome frame for a refused signed observation, preparation or
enrollment plan: it carries the reason of the branch that decided. -/
def refusalOutcome (phase : String) (refusal : Refusal) : Outcome :=
  .refused refusal.reason phase.toUTF8.toList refusal.detail.toUTF8.toList refusal.leaf

/-- Twin of `public_refusal_uniform`: on the signed requester's own channel the
decoded frame names exactly the reason (and, for a law refusal, the failing
clause) the admission path produced (for the
capability branch, `ResourceObservationAdmission.authorizeChecked_capability_reason`). -/
theorem signedRefusal_carries_reason (phase : String) (refusal : Refusal) :
    outcomeCodec.decode (outcomeCodec.encode (refusalOutcome phase refusal)) =
      some (.refused refusal.reason phase.toUTF8.toList refusal.detail.toUTF8.toList refusal.leaf) :=
  outcome_roundtrip _

/-- A fresh mutation need not confer read authority (blind writes and credits
remain possible). Its preflight/native/semantic refusal therefore exposes no
state-dependent reason. This is output non-disclosure, not a timing theorem. -/
def publicSubmissionOutcome : Outcome → Outcome
  | .refused .tailBound phase detail leaf => .refused .tailBound phase detail leaf
  | .refused .. => refused .undisclosed "admission" "request refused"
  | result => result

/-- The submitter receives the uniform refusal; the operator's own log (this
process's stderr) keeps the named reason. -/
def logOperatorRefusal (result : Outcome) : IO Unit := do
  if let .refused reason phase detail _ := result then
    IO.eprintln s!"host: submission refused (operator log): {repr reason}: {String.fromUTF8! ⟨phase.toArray⟩}: {String.fromUTF8! ⟨detail.toArray⟩}"

/-- Every blind-submission refusal is the same frame, whatever branch refused
and whatever reason it named, so a submitter without read authority learns
nothing from it. Its twin for the signed observation channel is
`signedRefusal_carries_reason`. -/
theorem public_refusal_uniform (reason : RefusalReason) (phase detail : List UInt8)
    (leaf : Option LawLeaf) (notTail : reason ≠ .tailBound) :
    publicSubmissionOutcome (.refused reason phase detail leaf) =
      refused .undisclosed "admission" "request refused" := by
  cases reason <;> first | rfl | exact absurd rfl notTail

/-- The submitter's view of a submission: uniform, except a renounce's gate
refusal to its authenticated signer. -/
def disclose : Outcome × Disclosure → Outcome
  | (result, .toSigner) => result
  | (result, .uniform) => publicSubmissionOutcome result

theorem disclose_uniform (result : Outcome) :
    disclose (result, .uniform) = publicSubmissionOutcome result := rfl

/-- The one signed-submission path: a renounce is disclosed by its own rule,
every other call uniformly. -/
def submitDisclosedWith (config : Config) (opened : Opened config) (call : SignedCall)
    (confirm : DurableReceiverIO.Confirmation → Digest → Digest → IO Outcome) :
    IO (Outcome × Disclosure) := do
  match call with
  | .renounce bytes => submitRenounceWith config opened bytes confirm
  | _ => return (← submitLoadedWith config opened call confirm, .uniform)

def submit (config : Config) (bytes : List UInt8) : IO Outcome := do
  let result ← match callCodec.decode bytes with
    | none => pure (refused .malformed "wire" "noncanonical or unsupported native host call", .uniform)
    | some call =>
        match ← openExisting config with
        | .error detail => pure (.unavailable detail.toUTF8.toList, .uniform)
        | .ok opened => submitDisclosedWith config opened call (confirmed config)
  logOperatorRefusal result.1
  return disclose result

/-- Lookup is read-only exact-ingress replay. It cannot submit an absent call. -/
def lookupLoaded (config : Config) (opened : Opened config) (call : SignedCall) : Outcome :=
  let finish := fun transaction event =>
    match historicalReceipt config opened.durable transaction event with
    | none => .uncertain "historical receipt prefix unavailable".toUTF8.toList
    | some receipt => .confirmed .replayed receipt
  match call with
  | .renounce bytes =>
      match CapabilityRenounce.decodeIngress bytes with
      | none => refused .malformed "renounce" "noncanonical ingress"
      | some ingress =>
          match CapabilityRenounce.replay config.deployment.domain config.profile.semantics
              opened.durable ingress with
          | none => .absent
          | some (.error _) => refused .conflict "replay" "transaction identity conflict"
          | some (.ok receipt) => finish receipt.transactionId receipt.eventId
  | .revoke bytes =>
      match CapabilityRevocationReceiver.decodeIngress bytes with
      | none => refused .malformed "revoke" "noncanonical ingress"
      | some ingress =>
          match CapabilityRevocationReceiver.replay config.deployment.domain config.profile.semantics opened.durable ingress with
          | none => .absent
          | some (.error _) => refused .conflict "replay" "transaction identity conflict"
          | some (.ok receipt) => finish receipt.transactionId receipt.eventId
  | .delegate bytes =>
      match CapabilityDelegationReceiver.decodeIngress bytes with
      | none => refused .malformed "delegate" "noncanonical ingress"
      | some ingress =>
          match CapabilityDelegationReceiver.replay config.deployment.domain config.profile.semantics opened.durable ingress with
          | none => .absent
          | some (.error _) => refused .conflict "replay" "transaction identity conflict"
          | some (.ok receipt) => finish receipt.transactionId receipt.eventId
  | .birth bytes =>
      match GrainResourceBirthPolicyController.decodeIngress bytes with
      | some ingress =>
          match GrainResourceBirthReceiver.replay opened.durable ingress with
          | none => .absent
          | some (.error _) => refused .conflict "replay" "transaction identity conflict"
          | some (.ok receipt) => finish receipt.transactionId receipt.eventId
      | none =>
          if bytes.take 7 = GrainResourceBirthPolicyController.ingressFrame.take 7 then
            refused .malformed "grain-birth" "noncanonical ingress"
          else
            match ResourceBirthPolicyController.Concrete.decodeIngress bytes with
            | none => refused .malformed "birth" "noncanonical ingress"
            | some ingress =>
                match ResourceBirthReceiver.replay config.deployment.domain opened.durable ingress with
                | none => .absent
                | some (.error _) => refused .conflict "replay" "transaction identity conflict"
                | some (.ok receipt) => finish receipt.transactionId receipt.eventId
  | .install bytes =>
      match PolicyInstallReceiver.decodeIngress bytes with
      | none => refused .malformed "install" "noncanonical ingress"
      | some ingress =>
          match PolicyInstallReceiver.replay config.deployment.domain opened.durable ingress with
          | none => .absent
          | some (.error _) => refused .conflict "replay" "transaction identity conflict"
          | some (.ok receipt) => finish receipt.transactionId receipt.eventId
  | .invoke signed =>
      match DeclaredResourceController.commandCodec.decode signed.commandBytes with
      | none => refused .malformed "invoke" "noncanonical command"
      | some command =>
          match DeclaredResourceController.recordedInvocation config.deployment.domain config.profile.semantics
              command signed opened.durable with
          | .error _ => refused .conflict "replay" "transaction identity conflict"
          | .ok none => .absent
          | .ok (some record) => finish record.transactionId record.event.event.eventId

/-- Composite birth lookup is the same exact event-and-two-nullifier replay
used by the receiving path. A historical receipt is selected from the
original accepted prefix; current tariff and policy do not reauthorize it. -/
theorem lookupLoaded_composite_exact (config : Config) (opened : Opened config)
    (bytes : List UInt8) (ingress : GrainResourceBirthPolicyController.DecodedIngress)
    (receipt : GrainResourceBirthReceiver.Receipt) (historical : NativeHostCodec.Receipt)
    (decoded : GrainResourceBirthPolicyController.decodeIngress bytes = some ingress)
    (replayed : GrainResourceBirthReceiver.replay opened.durable ingress = some (.ok receipt))
    (selected : historicalReceipt config opened.durable receipt.transactionId receipt.eventId =
      some historical) :
    lookupLoaded config opened (.birth bytes) = .confirmed .replayed historical := by
  simp [lookupLoaded, decoded, replayed, selected]

theorem lookupLoaded_composite_absent (config : Config) (opened : Opened config)
    (bytes : List UInt8) (ingress : GrainResourceBirthPolicyController.DecodedIngress)
    (decoded : GrainResourceBirthPolicyController.decodeIngress bytes = some ingress)
    (absent : GrainResourceBirthReceiver.replay opened.durable ingress = none) :
    lookupLoaded config opened (.birth bytes) = .absent := by
  simp [lookupLoaded, decoded, absent]

theorem lookupLoaded_composite_conflict (config : Config) (opened : Opened config)
    (bytes : List UInt8) (ingress : GrainResourceBirthPolicyController.DecodedIngress)
    (reason : GrainResourceBirthReceiver.Reject)
    (decoded : GrainResourceBirthPolicyController.decodeIngress bytes = some ingress)
    (conflict : GrainResourceBirthReceiver.replay opened.durable ingress = some (.error reason)) :
    lookupLoaded config opened (.birth bytes) =
      refused .conflict "replay" "transaction identity conflict" := by
  simp [lookupLoaded, decoded, conflict]

/-- Once the composite `DREGG/G` family prefix is present, malformed composite
bytes cannot be reinterpreted by the legacy `DREGG/R` birth decoder. -/
theorem lookupLoaded_malformed_composite (config : Config) (opened : Opened config)
    (bytes : List UInt8)
    (prefixExact : bytes.take 7 = GrainResourceBirthPolicyController.ingressFrame.take 7)
    (malformed : GrainResourceBirthPolicyController.decodeIngress bytes = none) :
    lookupLoaded config opened (.birth bytes) =
      refused .malformed "grain-birth" "noncanonical ingress" := by
  simp [lookupLoaded, malformed, prefixExact]

/-- info: 'Minidregg.Kernel.NativeHost.lookupLoaded_composite_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms lookupLoaded_composite_exact
/-- info: 'Minidregg.Kernel.NativeHost.lookupLoaded_composite_absent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms lookupLoaded_composite_absent
/-- info: 'Minidregg.Kernel.NativeHost.lookupLoaded_composite_conflict' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms lookupLoaded_composite_conflict
/-- info: 'Minidregg.Kernel.NativeHost.lookupLoaded_malformed_composite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms lookupLoaded_malformed_composite

def lookup (config : Config) (bytes : List UInt8) : IO Outcome := do
  match callCodec.decode bytes with
  | none => return refused .malformed "wire" "noncanonical native host call"
  | some call =>
      match ← openExisting config with
      | .error detail => return .unavailable detail.toUTF8.toList
      | .ok opened => return lookupLoaded config opened call

end Minidregg.Kernel.NativeHost

/-- info: 'Minidregg.Kernel.NativeHost.historicalReceipt_exactCandidate_fresh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.NativeHost.historicalReceipt_exactCandidate_fresh
/-- info: 'Minidregg.Kernel.NativeHost.historicalReceipt_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.NativeHost.historicalReceipt_bound
