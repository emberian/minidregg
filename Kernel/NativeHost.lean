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

/-- Ordinary open only reads and validates. It never installs a missing seed. -/
def openExisting (config : Config) : IO (Except String (Opened config)) := do
  match ← DurableReceiverIO.load config.storage.transport ResourceBirthCodec.rootBytes with
  | .error detail => return .error detail
  | .ok durable =>
      match ← NativeHostReplay.verifyLoaded config durable with
      | .error failure => return .error s!"semantic history refused at entry {failure.index}: {failure.detail}"
      | .ok verified => return .ok verified.opened

/-- Explicit local administration, separate from the signed network protocol.
The exact operator-pinned source genesis must have no accepted transactions. -/
def bootstrap (config : Config) (canonicalImage : List UInt8) : IO (Except String Unit) := do
  match DurableReceiverIO.loadBytes ResourceBirthCodec.rootBytes canonicalImage with
  | .error detail => return .error detail
  | .ok durable =>
      if !durable.image.accepted.isEmpty then return .error "bootstrap image contains accepted history"
      match validateLoaded config durable with
      | .error detail => return .error detail
      | .ok _ =>
          return ← DurableReceiverIO.bootstrap config.storage.transport
            ResourceBirthCodec.rootBytes durable.image.seed

private def refused (phase detail : String) : Outcome :=
  .refused phase.toUTF8.toList detail.toUTF8.toList

private def birthRejection : ResourceBirthReceiver.Reject → String
  | .malformedIngress => "malformed ingress"
  | .transactionConflict => "transaction identity conflict"
  | .admission reason => s!"admission: {repr reason}"
  | .durable reason => s!"durable: {repr reason}"

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
            config.deployment opened.pins opened.durable descriptor).mapError
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
        let prepared ← (DeclaredResourceController.prepare config.deployment profile
          ⟨config.federation, height⟩ opened.durable command).mapError
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
  -- Loaded.canonical and imageBoundaryCanonical_loaded preserve the exact
  -- commitment while avoiding another whole-history serialization per plan.
  pure ⟨config.deployment.domain, profile.semantics, imageBoundaryCanonical config opened.durable.bytes,
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

def enrollmentPlanAuthorizedLoaded (config : Config) (opened : Opened config)
    (signedObservationBytes commandBytes : List UInt8) :
    IO (Except String ParticipantKeyEnrollment.SigningPlan) := do
  let some command := ParticipantKeyEnrollment.commandCodec.decode commandBytes
    | return .error "enrollment observation refused"
  let some signed := NativeObservationCodec.signedCodec.decode signedObservationBytes
    | return .error "enrollment observation refused"
  if signed.challenge.intent.subject != command.sponsor then
    return .error "enrollment observation refused"
  match signed.challenge.intent.purpose with
  | .query query =>
      if query.kind != .object || query.target != config.deployment.factoryId ||
          query.view != .resource then
        return .error "enrollment observation refused"
  | .prepare _ => return .error "enrollment observation refused"
  match ← NativeObservationController.authorize config.signature
      ⟨opened.directory, opened.authority⟩ config.profile config.federation
      config.genesisHeight signed with
  | .error _ => return .error "enrollment observation refused"
  | .ok _ => return enrollmentPlanLoaded config opened commandBytes

def enrollmentPlan (config : Config) (signedObservationBytes commandBytes : List UInt8) :
    IO (Except String ParticipantKeyEnrollment.SigningPlan) := do
  match ← openExisting config with
  | .error _ => return .error "enrollment observation refused"
  | .ok opened =>
      enrollmentPlanAuthorizedLoaded config opened signedObservationBytes commandBytes

/-- Assembly transports two detached signatures. Native submission rechecks
both, the current factory law, exact old state and fresh subject. -/
def enrollmentAssemble (plan : ParticipantKeyEnrollment.SigningPlan)
    (sponsorSignature possessionSignature : List UInt8) : Except String (List UInt8) := do
  check (decide (sponsorSignature.length = 64)) "sponsor signature must be 64 bytes"
  check (decide (possessionSignature.length = 64)) "possession signature must be 64 bytes"
  let header ← need "noncanonical enrollment sponsor header"
    (CredentialSignedEnvelopeController.headerCodec.decode plan.sponsorHeader)
  let command ← need "noncanonical enrollment plan command"
    (ParticipantKeyEnrollment.commandCodec.decode plan.commandBytes)
  check (decide (plan.possessionHeader = ParticipantKeyEnrollment.possessionFrame
    plan.domain plan.semantics command)) "enrollment possession frame differs"
  let envelope := CredentialSignedEnvelopeController.envelopeCodec.encode
    ⟨header, sponsorSignature⟩
  pure (ParticipantKeyEnrollment.ingressCodec.encode
    ⟨plan.commandBytes, envelope, possessionSignature⟩)

def observationContext (config : Config) (opened : Opened config) :
    NativeObservationController.Context config.deployment opened.durable :=
  ⟨opened.directory, opened.authority⟩

/-- Only commitments and explicitly public request/key/policy coordinates
escape this pre-authorization step; the controller derives every header. -/
def challengeLoaded (config : Config) (opened : Opened config) (bytes : List UInt8) :
    Except String NativeObservationCodec.Challenge := do
  let some intent := NativeObservationCodec.intentCodec.decode bytes
    | throw "observation refused"
  (NativeObservationController.challenge (observationContext config opened)
    config.profile config.federation config.genesisHeight intent).mapError
      (fun _ => "observation refused")

def challenge (config : Config) (bytes : List UInt8) :
    IO (Except String NativeObservationCodec.Challenge) := do
  match ← openExisting config with
  | .error _ => return .error "observation refused"
  | .ok opened => return challengeLoaded config opened bytes

/-- The only public preparation path. A source-owned proof of every actual
read permission is required before the internal planner may disclose a result
or a detailed state-dependent error, on the very same opened image. -/
def prepareAuthorizedLoaded (config : Config) (opened : Opened config)
    (bytes : List UInt8) : IO (Except String SigningPlan) := do
  let some signed := NativeObservationCodec.signedCodec.decode bytes
    | return .error "observation refused"
  match ← NativeObservationController.authorize config.signature (observationContext config opened)
      config.profile config.federation config.genesisHeight signed with
  | .error _ => return .error "observation refused"
  | .ok _ =>
      match signed.challenge.intent.purpose with
      | .prepare draft => return prepareLoaded config opened draft
      | .query _ => return .error "signed observation purpose is not preparation"

def prepare (config : Config) (bytes : List UInt8) : IO (Except String SigningPlan) := do
  match ← openExisting config with
  | .error _ => return .error "observation refused"
  | .ok opened => prepareAuthorizedLoaded config opened bytes

/-- The controller projects the authorized logical resource/account cut. Raw
snapshots, whole Books, and unrelated authority pages never escape this API. -/
def queryLoaded (config : Config) (opened : Opened config)
    (bytes : List UInt8) : IO (Except String (List UInt8)) := do
  let some signed := NativeObservationCodec.signedCodec.decode bytes
    | return .error "observation refused"
  match ← NativeObservationController.authorize config.signature (observationContext config opened)
      config.profile config.federation config.genesisHeight signed with
  | .error _ => return .error "observation refused"
  | .ok token => return need "signed observation purpose is not a query" token.queryResult

def query (config : Config) (bytes : List UInt8) : IO (Except String (List UInt8)) := do
  match ← openExisting config with
  | .error _ => return .error "observation refused"
  | .ok opened => queryLoaded config opened bytes

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

/-- Seal the ORIGINAL accepted prefix, even when a later transaction was
published before physical confirmation/readback completed. -/
def historicalReceipt (config : Config) (durable : Durable) (transactionId eventId : Digest) :
    Option NativeHostCodec.Receipt := do
  let index ← durable.image.accepted.findIdx? (fun record => record.transactionId == transactionId)
  let record ← durable.image.accepted[index]?
  if record.event.eventId != eventId then none else
    let acceptedPrefix : DurableReceiver.Image := ⟨durable.image.seed, durable.image.accepted.take (index + 1)⟩
    some ⟨transactionId, eventId, index + 1, imageBoundary config acceptedPrefix⟩

/-- When the old chronological prefix has no matching transaction ID, the
historical selector points at the newly appended record and reproduces its
original-prefix receipt. This is a list fact, not a hash collision premise. -/
theorem historicalReceipt_exactCandidate_fresh (config : Config)
    {oldTarget : Durable} (old : NativeHostReplay.Verified config oldTarget)
    (derived : NativeHostReplay.Derived config old.opened)
    (ready : DurableReceiver.Ready ResourceBirthCodec.rootBytes
      old.opened.durable.image old.opened.durable.snapshot derived.intent)
    (fresh : old.opened.durable.image.accepted.findIdx?
      (fun record => record.transactionId == derived.intent.transactionId) = none) :
    historicalReceipt config (NativeHostReplay.exactCandidate old derived ready)
      derived.intent.transactionId derived.intent.event.eventId =
      some ⟨derived.intent.transactionId, derived.intent.event.eventId,
        old.opened.durable.image.accepted.length + 1,
        imageBoundary config (NativeHostReplay.exactCandidate old derived ready).image⟩ := by
  simp [historicalReceipt, NativeHostReplay.exactCandidate,
    DurableReceiver.Image.append, List.findIdx?_append, fresh,
    DurableReceiver.IntentRecord.ofIntent, List.take_append,
    List.take_of_length_le (Nat.le_succ _)]

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
      config.storage.transport opened.durable bytes with
  | .confirmed kind receipt => confirmed config kind receipt.transactionId receipt.eventId
  | .rejected reason => return refused "enroll-key" s!"{repr reason}"
  | .transactionConflict => return refused "replay" "transaction identity conflict"
  | .durableRejected reason => return refused "durable" s!"{repr reason}"
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
  | none => refused "enroll-key" "noncanonical signed ingress"
  | some ingress =>
    match ParticipantKeyEnrollmentReceiver.replay config.deployment.domain
        config.profile.semantics opened.durable ingress with
    | some (.ok receipt) =>
        match historicalReceipt config opened.durable receipt.transactionId receipt.eventId with
        | some original => .confirmed .replayed original
        | none => .uncertain "original receipt prefix unavailable".toUTF8.toList
    | some (.error _) => refused "replay" "transaction identity conflict"
    | none => .absent

def enrollmentLookup (config : Config) (bytes : List UInt8) : IO Outcome := do
  match ← openExisting config with
  | .error detail => return .unavailable detail.toUTF8.toList
  | .ok opened => return enrollmentLookupLoaded config opened bytes

def submitLoadedWith (config : Config) (opened : Opened config) (call : SignedCall)
    (confirm : DurableReceiverIO.Confirmation → Digest → Digest → IO Outcome) : IO Outcome := do
  let height := logicalHeight config opened.durable
  match call with
  | .revoke bytes =>
      match ← CapabilityRevocationReceiver.receiveLoaded config.deployment config.profile
          ⟨config.federation, height⟩ config.signature config.storage.transport opened.durable bytes with
      | .confirmed kind receipt => confirm kind receipt.transactionId receipt.eventId
      | .rejected reason => return refused "revoke" s!"{repr reason}"
      | .transactionConflict => return refused "replay" "transaction identity conflict"
      | .durableRejected reason => return refused "durable" s!"{repr reason}"
      | .contention => return .contention
      | .unavailable detail => return .unavailable detail.toUTF8.toList
      | .uncertain detail => return .uncertain detail.toUTF8.toList
  | .delegate bytes =>
      match ← CapabilityDelegationReceiver.receiveLoaded config.deployment config.profile
          ⟨config.federation, height⟩ config.signature config.storage.transport opened.durable bytes with
      | .confirmed kind receipt => confirm kind receipt.transactionId receipt.eventId
      | .rejected reason => return refused "delegate" s!"{repr reason}"
      | .transactionConflict => return refused "replay" "transaction identity conflict"
      | .durableRejected reason => return refused "durable" s!"{repr reason}"
      | .contention => return .contention
      | .unavailable detail => return .unavailable detail.toUTF8.toList
      | .uncertain detail => return .uncertain detail.toUTF8.toList
  | .birth bytes =>
      if (GrainResourceBirthPolicyController.decodeIngress bytes).isSome then
        let tariff := config.grainBirthTariffValue.toOption
        let ambient : DeclaredResourceController.Ambient := ⟨config.federation, height⟩
        match ← GrainResourceBirthReceiver.receiveLoaded config.profile config.deployment
            opened.pins tariff ambient config.signature config.storage.transport
            opened.durable bytes with
        | .historical receipt => return ← confirm .replayed receipt.transactionId receipt.eventId
        | .confirmed kind receipt => return ← confirm kind receipt.transactionId receipt.eventId
        | .rejected _ => return refused "grain-birth" "request refused"
        | .contention => return .contention
        | .unavailable detail => return .unavailable detail.toUTF8.toList
        | .uncertain detail => return .uncertain detail.toUTF8.toList
      match ← ResourceBirthReceiver.receiveLoaded config.profile config.deployment opened.pins
          config.signature config.storage.transport opened.durable height bytes with
      | .confirmed kind receipt => confirm kind receipt.transactionId receipt.eventId
      | .rejected reason => return refused "birth" (birthRejection reason)
      | .contention => return .contention
      | .unavailable detail => return .unavailable detail.toUTF8.toList
      | .uncertain detail => return .uncertain detail.toUTF8.toList
  | .install bytes =>
      match ← PolicyInstallReceiver.receiveLoaded config.profile config.deployment config.signature
          config.storage.transport opened.durable config.federation height bytes with
      | .confirmed kind receipt => confirm kind receipt.transactionId receipt.eventId
      | .rejected reason => return refused "install" s!"{repr reason}"
      | .durableRejected reason => return refused "durable" s!"{repr reason}"
      | .contention => return .contention
      | .unavailable detail => return .unavailable detail.toUTF8.toList
      | .uncertain detail => return .uncertain detail.toUTF8.toList
  | .invoke signed =>
      match DeclaredResourceController.commandCodec.decode signed.commandBytes with
      | none => return refused "invoke" "noncanonical command"
      | some command =>
          match ← DeclaredResourceController.withAcceptedLoaded config.deployment config.profile
              ⟨config.federation, height⟩ config.signature opened.durable signed
              (fun _ shape accepted => do
                let intent := accepted.dataIntent shape
                if (FnConsumerProgress.recognizedLegacyIntentAnyGateway?
                    config.deployment.domain config.profile.semantics intent).isSome then
                  return .rejected .physicalPreparation
                return .settlement (← DurableReceiverIO.receiveLoaded
                  config.storage.transport ResourceBirthCodec.rootBytes opened.durable intent))
              pure with
          | .replayed record => confirm .replayed record.transactionId record.event.event.eventId
          | .rejected reason => return refused "invoke" s!"{repr reason}"
          | .transactionConflict => return refused "replay" "transaction identity conflict"
          | .unavailable detail => return .unavailable detail.toUTF8.toList
          | .settlement result =>
              match result with
              | .confirmed kind _ =>
                  confirm kind
                    (DeclaredResourceController.transactionId config.deployment.domain config.profile.semantics command)
                    (DeclaredResourceController.invocationEvent config.deployment.domain config.profile.semantics command signed).eventId
              | .rejected reason => return refused "durable" s!"{repr reason}"
              | .contention => return .contention
              | .unavailable detail => return .unavailable detail.toUTF8.toList
              | .uncertain detail => return .uncertain detail.toUTF8.toList

def submitLoaded (config : Config) (opened : Opened config) (call : SignedCall) : IO Outcome :=
  submitLoadedWith config opened call (confirmed config)

/-- Complete one already admitted native operation from the exact CAS readback.
The only durable shortcut is complete-byte equality to the receiver's prepared
successor; an ordinary confirmation retains the existing reopen path. -/
private def submitDerivedVerifiedWith (config : Config) {oldTarget : Durable}
    (old : NativeHostReplay.Verified config oldTarget)
    (derived : NativeHostReplay.Derived config old.opened)
    (durableRejected : DurableDataIntent.RejectReason → Outcome)
    (confirm : DurableReceiverIO.Confirmation → Digest → Digest → IO Outcome)
    (confirmExact : (kind : DurableReceiverIO.Confirmation) →
      {target : Durable} → NativeHostReplay.Verified config target →
      NativeHostCodec.Receipt → IO Outcome) : IO Outcome := do
  let intent := derived.intent
  let result ← DurableReceiverIO.receiveLoadedDetailed config.storage.transport
    ResourceBirthCodec.rootBytes old.opened.durable intent
  match result with
  | .exact kind ready preparedEq readback readbackExact =>
      let candidate := NativeHostReplay.exactCandidate old derived ready
      match validated : validateLoaded config candidate with
      | .error detail =>
          return .uncertain s!"receipt readback: {detail}".toUTF8.toList
      | .ok after =>
          if afterExact : after.durable.bytes.toByteArray == candidate.bytes.toByteArray then
            let proof : NativeHostReplay.ExactReadback config old :=
              { derived := derived
                ready := ready
                prepared := preparedEq
                physicalBytes := readback
                exactBytes := readbackExact
                after := after
                validated := validated
                afterExact := (DurableReceiverIO.byteArray_beq_exact _ _).mp afterExact }
            let verified := NativeHostReplay.extendExact old proof
            let receipt : NativeHostCodec.Receipt :=
              ⟨intent.transactionId, intent.event.eventId,
                old.opened.durable.image.accepted.length + 1,
                imageBoundary config candidate.image⟩
            match historicalReceipt config candidate intent.transactionId intent.event.eventId with
            | none => return .uncertain "original receipt prefix unavailable".toUTF8.toList
            | some selected =>
                if _selectedExact : selected = receipt then
                  confirmExact kind verified selected
                else return .uncertain "original receipt prefix mismatch".toUTF8.toList
          else return .uncertain "receipt readback: validated successor bytes changed".toUTF8.toList
  | .ordinary result =>
      match result with
      | .confirmed kind _ => confirm kind intent.transactionId intent.event.eventId
      | .rejected reason => return durableRejected reason
      | .contention => return .contention
      | .unavailable detail => return .unavailable detail.toUTF8.toList
      | .uncertain detail => return .uncertain detail.toUTF8.toList

/-- A persistent session retains a typed fresh admission and complete CAS
readback for ordinary invocation and birth. Concurrent or nonexact outcomes
keep the historical confirmation/current-tip refresh behavior. -/
def submitVerifiedLoadedWith (config : Config) {oldTarget : Durable}
    (old : NativeHostReplay.Verified config oldTarget) (call : SignedCall)
    (confirm : DurableReceiverIO.Confirmation → Digest → Digest → IO Outcome)
    (confirmExact : (kind : DurableReceiverIO.Confirmation) →
      {target : Durable} → NativeHostReplay.Verified config target →
      NativeHostCodec.Receipt → IO Outcome) : IO Outcome := do
  match call with
  | .invoke signed =>
      let height := logicalHeight config old.opened.durable
      DeclaredResourceController.withAcceptedLoaded config.deployment config.profile
        ⟨config.federation, height⟩ config.signature old.opened.durable signed
        (fun prepared shape accepted => do
          let intent := accepted.dataIntent shape
          if (FnConsumerProgress.recognizedLegacyIntentAnyGateway?
              config.deployment.domain config.profile.semantics intent).isSome then
            return refused "invoke" "v1 fn consumer progress is historical only"
          let derived : NativeHostReplay.Derived config old.opened :=
            NativeHostReplay.Derived.ofInvoke prepared signed shape accepted
          submitDerivedVerifiedWith config old derived
            (fun reason => refused "durable" s!"{repr reason}") confirm confirmExact)
        (fun result =>
          match result with
          | .replayed record => confirm .replayed record.transactionId record.event.event.eventId
          | .rejected reason => pure <| refused "invoke" s!"{repr reason}"
          | .transactionConflict => pure <| refused "replay" "transaction identity conflict"
          | .unavailable detail => pure (.unavailable detail.toUTF8.toList)
          | .settlement _ => pure (.unavailable "unexpected invocation settlement".toUTF8.toList))
  | .birth bytes =>
      if (GrainResourceBirthPolicyController.decodeIngress bytes).isSome then
        submitLoadedWith config old.opened call confirm
      else
        match ResourceBirthPolicyController.Concrete.decodeIngress bytes with
        | none => return refused "birth" (birthRejection .malformedIngress)
        | some ingress =>
            match ResourceBirthReceiver.replay config.deployment.domain old.opened.durable ingress with
            | some (.ok receipt) => confirm .replayed receipt.transactionId receipt.eventId
            | some (.error reason) => return refused "birth" (birthRejection reason)
            | none =>
                let height := logicalHeight config old.opened.durable
                match ← ResourceBirthPolicyController.Concrete.admitDecodedNative
                    config.profile config.deployment old.opened.pins config.signature
                    old.opened.durable height ingress with
                | .error reason => return refused "birth" (birthRejection (.admission reason))
                | .ok accepted =>
                    submitDerivedVerifiedWith config old
                      (NativeHostReplay.Derived.ofBirth accepted)
                      (fun reason => refused "birth" (birthRejection (.durable reason)))
                      confirm confirmExact
  | _ => submitLoadedWith config old.opened call confirm

/-- A fresh mutation need not confer read authority (blind writes and credits
remain possible). Its preflight/native/semantic refusal therefore exposes no
state-dependent reason. This is output non-disclosure, not a timing theorem. -/
def publicSubmissionOutcome : Outcome → Outcome
  | .refused _ _ => refused "admission" "request refused"
  | result => result

theorem public_refusal_uniform (phase detail : List UInt8) :
    publicSubmissionOutcome (.refused phase detail) =
      refused "admission" "request refused" := rfl

def submit (config : Config) (bytes : List UInt8) : IO Outcome := do
  let result ← match callCodec.decode bytes with
    | none => pure (refused "wire" "noncanonical or unsupported native host call")
    | some call =>
        match ← openExisting config with
        | .error detail => pure (.unavailable detail.toUTF8.toList)
        | .ok opened => submitLoaded config opened call
  return publicSubmissionOutcome result

/-- Lookup is read-only exact-ingress replay. It cannot submit an absent call. -/
def lookupLoaded (config : Config) (opened : Opened config) (call : SignedCall) : Outcome :=
  let finish := fun transaction event =>
    match historicalReceipt config opened.durable transaction event with
    | none => .uncertain "historical receipt prefix unavailable".toUTF8.toList
    | some receipt => .confirmed .replayed receipt
  match call with
  | .revoke bytes =>
      match CapabilityRevocationReceiver.decodeIngress bytes with
      | none => refused "revoke" "noncanonical ingress"
      | some ingress =>
          match CapabilityRevocationReceiver.replay config.deployment.domain config.profile.semantics opened.durable ingress with
          | none => .absent
          | some (.error _) => refused "replay" "transaction identity conflict"
          | some (.ok receipt) => finish receipt.transactionId receipt.eventId
  | .delegate bytes =>
      match CapabilityDelegationReceiver.decodeIngress bytes with
      | none => refused "delegate" "noncanonical ingress"
      | some ingress =>
          match CapabilityDelegationReceiver.replay config.deployment.domain config.profile.semantics opened.durable ingress with
          | none => .absent
          | some (.error _) => refused "replay" "transaction identity conflict"
          | some (.ok receipt) => finish receipt.transactionId receipt.eventId
  | .birth bytes =>
      match GrainResourceBirthPolicyController.decodeIngress bytes with
      | some ingress =>
          match GrainResourceBirthReceiver.replay opened.durable ingress with
          | none => .absent
          | some (.error _) => refused "replay" "transaction identity conflict"
          | some (.ok receipt) => finish receipt.transactionId receipt.eventId
      | none =>
          if bytes.take 7 = GrainResourceBirthPolicyController.ingressFrame.take 7 then
            refused "grain-birth" "noncanonical ingress"
          else
            match ResourceBirthPolicyController.Concrete.decodeIngress bytes with
            | none => refused "birth" "noncanonical ingress"
            | some ingress =>
                match ResourceBirthReceiver.replay config.deployment.domain opened.durable ingress with
                | none => .absent
                | some (.error _) => refused "replay" "transaction identity conflict"
                | some (.ok receipt) => finish receipt.transactionId receipt.eventId
  | .install bytes =>
      match PolicyInstallReceiver.decodeIngress bytes with
      | none => refused "install" "noncanonical ingress"
      | some ingress =>
          match PolicyInstallReceiver.replay config.deployment.domain opened.durable ingress with
          | none => .absent
          | some (.error _) => refused "replay" "transaction identity conflict"
          | some (.ok receipt) => finish receipt.transactionId receipt.eventId
  | .invoke signed =>
      match DeclaredResourceController.commandCodec.decode signed.commandBytes with
      | none => refused "invoke" "noncanonical command"
      | some command =>
          match DeclaredResourceController.recordedInvocation config.deployment.domain config.profile.semantics
              command signed opened.durable with
          | .error _ => refused "replay" "transaction identity conflict"
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
      refused "replay" "transaction identity conflict" := by
  simp [lookupLoaded, decoded, conflict]

/-- Once the composite `DREGG/G` family prefix is present, malformed composite
bytes cannot be reinterpreted by the legacy `DREGG/R` birth decoder. -/
theorem lookupLoaded_malformed_composite (config : Config) (opened : Opened config)
    (bytes : List UInt8)
    (prefixExact : bytes.take 7 = GrainResourceBirthPolicyController.ingressFrame.take 7)
    (malformed : GrainResourceBirthPolicyController.decodeIngress bytes = none) :
    lookupLoaded config opened (.birth bytes) =
      refused "grain-birth" "noncanonical ingress" := by
  simp [lookupLoaded, malformed, prefixExact]

#print axioms lookupLoaded_composite_exact
#print axioms lookupLoaded_composite_absent
#print axioms lookupLoaded_composite_conflict
#print axioms lookupLoaded_malformed_composite

def lookup (config : Config) (bytes : List UInt8) : IO Outcome := do
  match callCodec.decode bytes with
  | none => return refused "wire" "noncanonical native host call"
  | some call =>
      match ← openExisting config with
      | .error detail => return .unavailable detail.toUTF8.toList
      | .ok opened => return lookupLoaded config opened call

end Minidregg.Kernel.NativeHost

#print axioms Minidregg.Kernel.NativeHost.historicalReceipt_exactCandidate_fresh
