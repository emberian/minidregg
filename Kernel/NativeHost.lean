/-
A native host for the actual canonical Mini receivers. Operator configuration
is fixed for the process. Opening never initializes; administration explicitly
bootstraps a checked, pinned genesis. Public calls carry signed operations only.

Logical height and admission share one Loaded image, and the receiver's CAS is
against that exact image. Contention requires preparation/signing against the
new state. Exact historical replay is looked up before fresh authorization.
-/
import Kernel.NativeHostContext
import Kernel.NativeObservationController
import Kernel.NativeHostReplay

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
  pure ⟨config.deployment.domain, profile.semantics, imageBoundary config opened.durable.image,
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

def observationContext (config : Config) (opened : Opened config) :
    NativeObservationController.Context config.deployment opened.durable :=
  ⟨opened.directory, opened.authority⟩

/-- Only commitments and explicitly public request/key/policy coordinates
escape this pre-authorization step; the controller derives every header. -/
def challenge (config : Config) (bytes : List UInt8) :
    IO (Except String NativeObservationCodec.Challenge) := do
  let some intent := NativeObservationCodec.intentCodec.decode bytes
    | return .error "observation refused"
  match ← openExisting config with
  | .error _ => return .error "observation refused"
  | .ok opened =>
      return (NativeObservationController.challenge (observationContext config opened)
        config.profile config.federation config.genesisHeight intent).mapError
          (fun _ => "observation refused")

/-- The only public preparation path. A source-owned proof of every actual
read permission is required before the internal planner may disclose a result
or a detailed state-dependent error, on the very same opened image. -/
def prepare (config : Config) (bytes : List UInt8) : IO (Except String SigningPlan) := do
  let some signed := NativeObservationCodec.signedCodec.decode bytes
    | return .error "observation refused"
  match ← openExisting config with
  | .error _ => return .error "observation refused"
  | .ok opened =>
      match ← NativeObservationController.authorize config.signature (observationContext config opened)
          config.profile config.federation config.genesisHeight signed with
      | .error _ => return .error "observation refused"
      | .ok _ =>
          match signed.challenge.intent.purpose with
          | .prepare draft => return prepareLoaded config opened draft
          | .query _ => return .error "signed observation purpose is not preparation"

/-- The controller projects the authorized logical resource/account cut. Raw
snapshots, whole Books, and unrelated authority pages never escape this API. -/
def query (config : Config) (bytes : List UInt8) : IO (Except String (List UInt8)) := do
  let some signed := NativeObservationCodec.signedCodec.decode bytes
    | return .error "observation refused"
  match ← openExisting config with
  | .error _ => return .error "observation refused"
  | .ok opened =>
      match ← NativeObservationController.authorize config.signature (observationContext config opened)
          config.profile config.federation config.genesisHeight signed with
      | .error _ => return .error "observation refused"
      | .ok token => return need "signed observation purpose is not a query" token.queryResult

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

private def confirmed (config : Config) (kind : DurableReceiverIO.Confirmation)
    (transactionId eventId : Digest) : IO Outcome := do
  match ← openExisting config with
  | .error detail => return .uncertain s!"receipt readback: {detail}".toUTF8.toList
  | .ok opened =>
      match historicalReceipt config opened.durable transactionId eventId with
      | none => return .uncertain "original receipt prefix unavailable".toUTF8.toList
      | some receipt => return .confirmed kind receipt

def submitLoaded (config : Config) (opened : Opened config) (call : SignedCall) : IO Outcome := do
  let height := logicalHeight config opened.durable
  match call with
  | .revoke bytes =>
      match ← CapabilityRevocationReceiver.receiveLoaded config.deployment config.profile
          ⟨config.federation, height⟩ config.signature config.storage.transport opened.durable bytes with
      | .confirmed kind receipt => confirmed config kind receipt.transactionId receipt.eventId
      | .rejected reason => return refused "revoke" s!"{repr reason}"
      | .transactionConflict => return refused "replay" "transaction identity conflict"
      | .durableRejected reason => return refused "durable" s!"{repr reason}"
      | .contention => return .contention
      | .unavailable detail => return .unavailable detail.toUTF8.toList
      | .uncertain detail => return .uncertain detail.toUTF8.toList
  | .delegate bytes =>
      match ← CapabilityDelegationReceiver.receiveLoaded config.deployment config.profile
          ⟨config.federation, height⟩ config.signature config.storage.transport opened.durable bytes with
      | .confirmed kind receipt => confirmed config kind receipt.transactionId receipt.eventId
      | .rejected reason => return refused "delegate" s!"{repr reason}"
      | .transactionConflict => return refused "replay" "transaction identity conflict"
      | .durableRejected reason => return refused "durable" s!"{repr reason}"
      | .contention => return .contention
      | .unavailable detail => return .unavailable detail.toUTF8.toList
      | .uncertain detail => return .uncertain detail.toUTF8.toList
  | .birth bytes =>
      match ← ResourceBirthReceiver.receiveLoaded config.profile config.deployment opened.pins
          config.signature config.storage.transport opened.durable height bytes with
      | .confirmed kind receipt => confirmed config kind receipt.transactionId receipt.eventId
      | .rejected reason => return refused "birth" (birthRejection reason)
      | .contention => return .contention
      | .unavailable detail => return .unavailable detail.toUTF8.toList
      | .uncertain detail => return .uncertain detail.toUTF8.toList
  | .install bytes =>
      match ← PolicyInstallReceiver.receiveLoaded config.profile config.deployment config.signature
          config.storage.transport opened.durable config.federation height bytes with
      | .confirmed kind receipt => confirmed config kind receipt.transactionId receipt.eventId
      | .rejected reason => return refused "install" s!"{repr reason}"
      | .durableRejected reason => return refused "durable" s!"{repr reason}"
      | .contention => return .contention
      | .unavailable detail => return .unavailable detail.toUTF8.toList
      | .uncertain detail => return .uncertain detail.toUTF8.toList
  | .invoke signed =>
      match DeclaredResourceController.commandCodec.decode signed.commandBytes with
      | none => return refused "invoke" "noncanonical command"
      | some command =>
          match ← DeclaredResourceController.receiveLoaded config.deployment config.profile
              ⟨config.federation, height⟩ config.signature config.storage.transport opened.durable signed with
          | .replayed record => confirmed config .replayed record.transactionId record.event.event.eventId
          | .rejected reason => return refused "invoke" s!"{repr reason}"
          | .transactionConflict => return refused "replay" "transaction identity conflict"
          | .unavailable detail => return .unavailable detail.toUTF8.toList
          | .settlement result =>
              match result with
              | .confirmed kind _ =>
                  confirmed config kind
                    (DeclaredResourceController.transactionId config.deployment.domain config.profile.semantics command)
                    (DeclaredResourceController.invocationEvent config.deployment.domain config.profile.semantics command signed).eventId
              | .rejected reason => return refused "durable" s!"{repr reason}"
              | .contention => return .contention
              | .unavailable detail => return .unavailable detail.toUTF8.toList
              | .uncertain detail => return .uncertain detail.toUTF8.toList

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

def lookup (config : Config) (bytes : List UInt8) : IO Outcome := do
  match callCodec.decode bytes with
  | none => return refused "wire" "noncanonical native host call"
  | some call =>
      match ← openExisting config with
      | .error detail => return .unavailable detail.toUTF8.toList
      | .ok opened => return lookupLoaded config opened call

end Minidregg.Kernel.NativeHost
