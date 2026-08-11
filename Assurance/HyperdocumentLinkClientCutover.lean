/-
# Assurance.HyperdocumentLinkClientCutover -- one command above one byte endpoint

This module is the thinnest client cutover over
`HyperdocumentLinkEndpointController`.  Human and agent callers retain distinct
audit metadata, but both construct the exact same semantic request and
declaration bytes.  One opaque, fallible submit function receives first-order
call data and may return only an opaque error, no response (the response was
lost), or response bytes.  It cannot return a semantic record or a receipt.

`submitLink` retries once after a lost response.  Success is minted only after
the client checks the endpoint's exact canonical response bytes and re-runs the
Lean response decoder.  The resulting receipt binds the audit metadata, exact
request/declaration/response bytes, the concrete `LinkRecord`, and the
canonical reopened content query.

The closed runner below deliberately exercises the existing Lean endpoint and
drops its first successful response.  Together with the endpoint's framed-WAL
theorems this witnesses publish, response loss, restart, exact same-byte retry,
and reopen.  It is still a logical runner: no theorem here authenticates a
credential, sends a network packet, calls a filesystem, obtains external
finality, renders a human UI, or delivers a result to an agent runtime.
-/
import Assurance.HyperdocumentLinkEndpointController

namespace Minidregg.Assurance.HyperdocumentLinkClientCutover

open Minidregg.Compiler.FramedWalRecoveryController
open Minidregg.Kernel.DurableDataIntent
open Minidregg.Theory
open Minidregg.Theory.Hyperdocument
open Minidregg.Theory.HyperdocumentInterface

namespace Endpoint

abbrev Origin :=
  Minidregg.Assurance.HyperdocumentLinkEndpointController.Origin
abbrev Failure :=
  Minidregg.Assurance.HyperdocumentLinkEndpointController.Failure
abbrev submitCodec :=
  Minidregg.Assurance.HyperdocumentLinkEndpointController.submitCodec
noncomputable abbrev linkRecordCodec :=
  Minidregg.Assurance.HyperdocumentLinkEndpointController.linkRecordCodec
noncomputable abbrev declarationCodec :=
  Minidregg.Assurance.HyperdocumentLinkEndpointController.Publication.declarationCodec
noncomputable abbrev linkDeclaration :=
  Minidregg.Assurance.HyperdocumentLinkEndpointController.Publication.linkDeclaration
noncomputable abbrev linkAccepted :=
  Minidregg.Assurance.HyperdocumentLinkEndpointController.Publication.linkAccepted
noncomputable abbrev record :=
  Minidregg.Assurance.HyperdocumentLinkEndpointController.Reopen.record
noncomputable abbrev query :=
  Minidregg.Assurance.HyperdocumentLinkEndpointController.Reopen.query
abbrev query_exact :=
  Minidregg.Assurance.HyperdocumentLinkEndpointController.Reopen.query_exact
noncomputable abbrev checkpoint :=
  Minidregg.Assurance.HyperdocumentLinkEndpointController.Recovery.checkpoint
noncomputable abbrev reader :=
  Minidregg.Assurance.HyperdocumentLinkEndpointController.Recovery.reader
noncomputable abbrev honestRequest :=
  Minidregg.Assurance.HyperdocumentLinkEndpointController.honestRequest
noncomputable abbrev honestRequestBytes :=
  Minidregg.Assurance.HyperdocumentLinkEndpointController.honestRequestBytes
noncomputable abbrev resultBytes :=
  Minidregg.Assurance.HyperdocumentLinkEndpointController.resultBytes
abbrev honest_request_decodes :=
  Minidregg.Assurance.HyperdocumentLinkEndpointController.honest_request_decodes
abbrev declaration_decodes_link :=
  Minidregg.Assurance.HyperdocumentLinkEndpointController.declaration_decodes_link
abbrev result_decodes_exact_link :=
  Minidregg.Assurance.HyperdocumentLinkEndpointController.result_decodes_exact_link
abbrev honest_run_accepts :=
  Minidregg.Assurance.HyperdocumentLinkEndpointController.honest_run_accepts
abbrev published_frame_survives_crash :=
  Minidregg.Assurance.HyperdocumentLinkEndpointController.published_frame_survives_crash
abbrev publish_lost_response_crash_recover_retry_reopen :=
  Minidregg.Assurance.HyperdocumentLinkEndpointController.publish_lost_response_crash_recover_retry_reopen

end Endpoint

set_option autoImplicit false

noncomputable section

/-! ## Audit-distinct callers, semantic-identical command -/

/-- Audit-only caller metadata.  These values are retained in the client
receipt, but are absent from the semantic request and declaration codecs. -/
inductive CallerMetadata where
  | human (sessionId interactionId : Nat)
  | agent (runId toolCallId : Nat)
  deriving DecidableEq, Repr

def CallerMetadata.origin : CallerMetadata → Endpoint.Origin
  | .human _ _ => .human
  | .agent _ _ => .agent

/-- There is intentionally only one semantic client command in this cutover.
Adding an operation requires adding a different command and endpoint, rather
than smuggling a native callback or an untyped method selector through this
carrier. -/
structure LinkCommand where
  caller : CallerMetadata
  deriving DecidableEq, Repr

namespace LinkCommand

def origin (command : LinkCommand) : Endpoint.Origin := command.caller.origin

/-- Audit metadata cannot affect the inner semantic declaration bytes. -/
noncomputable def declarationBytes (_command : LinkCommand) : List UInt8 :=
  Endpoint.declarationCodec.encode Endpoint.linkDeclaration

/-- Audit metadata cannot affect the complete endpoint request bytes. -/
noncomputable def requestBytes (_command : LinkCommand) : List UInt8 :=
  Endpoint.honestRequestBytes

@[simp] theorem declarationBytes_exact (command : LinkCommand) :
    command.declarationBytes =
      Endpoint.declarationCodec.encode Endpoint.linkDeclaration :=
  rfl

@[simp] theorem requestBytes_exact (command : LinkCommand) :
    command.requestBytes = Endpoint.honestRequestBytes :=
  rfl

theorem metadata_cannot_change_declaration
    (left right : LinkCommand) :
    left.declarationBytes = right.declarationBytes :=
  rfl

theorem metadata_cannot_change_request
    (left right : LinkCommand) :
    left.requestBytes = right.requestBytes :=
  rfl

@[simp] theorem human_agent_declaration_bytes_identical
    (sessionId interactionId runId toolCallId : Nat) :
    (LinkCommand.mk (.human sessionId interactionId)).declarationBytes =
      (LinkCommand.mk (.agent runId toolCallId)).declarationBytes :=
  rfl

@[simp] theorem human_agent_request_bytes_identical
    (sessionId interactionId runId toolCallId : Nat) :
    (LinkCommand.mk (.human sessionId interactionId)).requestBytes =
      (LinkCommand.mk (.agent runId toolCallId)).requestBytes :=
  rfl

end LinkCommand

/-! ## One opaque, fallible restart-aware submit boundary -/

inductive Attempt where
  | initial
  | afterRestart
  deriving DecidableEq, Repr

/-- Complete first-order input to the opaque submit boundary.  The boundary
may log audit metadata, but the semantic endpoint receives only `requestBytes`
and the origin projection. -/
structure IssuedCall where
  attempt : Attempt
  caller : CallerMetadata
  requestBytes : List UInt8
  deriving DecidableEq, Repr

def LinkCommand.issuedCall (command : LinkCommand) (attempt : Attempt) :
    IssuedCall where
  attempt := attempt
  caller := command.caller
  requestBytes := command.requestBytes

@[simp] theorem restart_reissues_identical_request (command : LinkCommand) :
    (command.issuedCall .initial).requestBytes =
      (command.issuedCall .afterRestart).requestBytes :=
  rfl

@[simp] theorem restart_preserves_audit_metadata (command : LinkCommand) :
    (command.issuedCall .initial).caller =
      (command.issuedCall .afterRestart).caller :=
  rfl

/-- The only client-side opaque boundary.  `none` means that the caller has no
response and must assume the operation may already have committed.  Native
code returns neither a `LinkRecord` nor a success receipt. -/
abbrev OpaqueSubmit (NativeError : Type) :=
  IssuedCall → Except NativeError (Option (List UInt8))

/-! ## Exact response checking and proof-relevant client receipt -/

/-- Client success binds every byte surface and the exact reopened semantic
record.  `command` retains the human/agent audit metadata at the type index. -/
structure AcceptedReceipt (command : LinkCommand) where
  requestBytes : List UInt8
  declarationBytes : List UInt8
  responseBytes : List UInt8
  record : LinkRecord
  requestExact : requestBytes = command.requestBytes
  declarationExact : declarationBytes = command.declarationBytes
  responseExact : responseBytes = Endpoint.resultBytes
  requestDecodes :
    Endpoint.submitCodec.decode requestBytes = some Endpoint.honestRequest
  declarationDecodes :
    Endpoint.declarationCodec.decode declarationBytes =
      some Endpoint.linkDeclaration
  responseDecodes :
    Endpoint.linkRecordCodec.decode responseBytes = some record
  recordExact : record = Endpoint.record
  canonicalReopen :
    ContentQuery.project Endpoint.query
        Endpoint.linkAccepted.accepted.prepared.post.logical =
      some record

def AcceptedReceipt.origin {command : LinkCommand}
    (_receipt : AcceptedReceipt command) : Endpoint.Origin :=
  command.origin

def AcceptedReceipt.audit {command : LinkCommand}
    (_receipt : AcceptedReceipt command) : CallerMetadata :=
  command.caller

/-- Construct a receipt only from a proof that the response is the endpoint's
exact canonical response.  The decoder and canonical query are re-established
inside the receipt rather than trusted from the opaque boundary. -/
noncomputable def receiptOfExact (command : LinkCommand)
    (bytes : List UInt8) (exact : bytes = Endpoint.resultBytes) :
    AcceptedReceipt command where
  requestBytes := command.requestBytes
  declarationBytes := command.declarationBytes
  responseBytes := bytes
  record := Endpoint.record
  requestExact := rfl
  declarationExact := rfl
  responseExact := exact
  requestDecodes := by
    simp [LinkCommand.requestBytes]
  declarationDecodes := by
    simp [LinkCommand.declarationBytes]
  responseDecodes := by
    rw [exact]
    exact Endpoint.result_decodes_exact_link
  recordExact := rfl
  canonicalReopen := Endpoint.query_exact

noncomputable def canonicalReceipt (command : LinkCommand) :
    AcceptedReceipt command :=
  receiptOfExact command Endpoint.resultBytes rfl

/-- Executable exact-byte response gate.  Decoding the same semantic record
from a different byte string is not enough: the endpoint owns the canonical
response representation. -/
noncomputable def decodeReceipt (command : LinkCommand)
    (bytes : List UInt8) : Option (AcceptedReceipt command) :=
  if exact : bytes = Endpoint.resultBytes then
    some (receiptOfExact command bytes exact)
  else
    none

@[simp] theorem decodeReceipt_resultBytes (command : LinkCommand) :
    decodeReceipt command Endpoint.resultBytes =
      some (canonicalReceipt command) := by
  simp [decodeReceipt, canonicalReceipt]

theorem decodeReceipt_rejects_noncanonical (command : LinkCommand)
    (bytes : List UInt8) (different : bytes ≠ Endpoint.resultBytes) :
    decodeReceipt command bytes = none := by
  simp [decodeReceipt, different]

/-! ## The single executable command API -/

inductive Outcome (NativeError : Type) (command : LinkCommand) where
  | accepted (receipt : AcceptedReceipt command)
  | native (error : NativeError)
  | malformedResponse (bytes : List UInt8)
  | responseLostTwice

/-- Submit one link command.  A missing initial response causes exactly one
restart/retry with the same request bytes and audit metadata.  Native errors
are opaque and terminal; received bytes must pass `decodeReceipt`. -/
noncomputable def submitLink {NativeError : Type}
    (submit : OpaqueSubmit NativeError) (command : LinkCommand) :
    Outcome NativeError command :=
  match submit (command.issuedCall .initial) with
  | .error error => .native error
  | .ok (some bytes) =>
      match decodeReceipt command bytes with
      | some receipt => .accepted receipt
      | none => .malformedResponse bytes
  | .ok none =>
      match submit (command.issuedCall .afterRestart) with
      | .error error => .native error
      | .ok none => .responseLostTwice
      | .ok (some bytes) =>
          match decodeReceipt command bytes with
          | some receipt => .accepted receipt
          | none => .malformedResponse bytes

def Outcome.record? {NativeError : Type} {command : LinkCommand} :
    Outcome NativeError command → Option LinkRecord
  | .accepted receipt => some receipt.record
  | .native _ => none
  | .malformedResponse _ => none
  | .responseLostTwice => none

/-! ## Closed endpoint adapter and lost-response/restart witness -/

/-- Map the existing endpoint into the byte-only native boundary.  This
adapter does not expose the endpoint's verified state or acceptance proof. -/
noncomputable def endpointCall
    (call : IssuedCall) : Except (Endpoint.Failure Unit) (List UInt8) :=
  Minidregg.Assurance.HyperdocumentLinkEndpointController.runAt
    Endpoint.checkpoint call.caller.origin call.requestBytes Endpoint.reader

@[simp] theorem endpointCall_command
    (command : LinkCommand) (attempt : Attempt) :
    endpointCall (command.issuedCall attempt) = .ok Endpoint.resultBytes := by
  simp [endpointCall, LinkCommand.issuedCall, LinkCommand.requestBytes]

noncomputable def deliverEndpoint : OpaqueSubmit (Endpoint.Failure Unit) :=
  fun call =>
    match endpointCall call with
    | .error error => .error error
    | .ok bytes => .ok (some bytes)

/-- The first endpoint success is executed and then deliberately discarded.
After restart the same opaque adapter executes the same request again and
delivers its byte response. -/
noncomputable def loseFirstEndpointResponse :
    OpaqueSubmit (Endpoint.Failure Unit) :=
  fun call =>
    match call.attempt with
    | .initial =>
        match endpointCall call with
        | .error error => .error error
        | .ok _bytes => .ok none
    | .afterRestart => deliverEndpoint call

@[simp] theorem loseFirstEndpointResponse_initial (command : LinkCommand) :
    loseFirstEndpointResponse (command.issuedCall .initial) = .ok none := by
  change (match endpointCall (command.issuedCall .initial) with
    | Except.error error => Except.error error
    | Except.ok _bytes => Except.ok none) = Except.ok none
  rw [endpointCall_command]

@[simp] theorem loseFirstEndpointResponse_afterRestart
    (command : LinkCommand) :
    loseFirstEndpointResponse (command.issuedCall .afterRestart) =
      .ok (some Endpoint.resultBytes) := by
  change deliverEndpoint (command.issuedCall .afterRestart) =
    .ok (some Endpoint.resultBytes)
  unfold deliverEndpoint
  rw [endpointCall_command]

@[simp] theorem deliver_endpoint_accepts (command : LinkCommand) :
    submitLink deliverEndpoint command =
      .accepted (canonicalReceipt command) := by
  simp [submitLink, deliverEndpoint, endpointCall_command,
    decodeReceipt_resultBytes]

@[simp] theorem lost_response_restart_accepts (command : LinkCommand) :
    submitLink loseFirstEndpointResponse command =
      .accepted (canonicalReceipt command) := by
  simp [submitLink]

@[simp] theorem lost_response_restart_reopens_exact_record
    (command : LinkCommand) :
    (submitLink loseFirstEndpointResponse command).record? =
      some Endpoint.record := by
  rw [lost_response_restart_accepts]
  rfl

/-- Full logical cutover: the first response is lost, the synced frame
survives crash in the durable model, the exact same request is retried without
a second installation, and the client receipt decodes/reopens the retained
link. -/
theorem lost_response_restart_retry_receipt
    (command : LinkCommand) :
    submitLink loseFirstEndpointResponse command =
        .accepted (canonicalReceipt command) ∧
      Minidregg.Kernel.FramedWalRefinement.DeviceState.recovered
          Minidregg.Assurance.HyperdocumentLinkFramedRecovery.walFrameCodec
          Minidregg.Assurance.HyperdocumentLinkFramedRecovery.syncedDevice =
        Minidregg.Kernel.DurableCommitProtocol.Snapshot.install
          Minidregg.Assurance.HyperdocumentLinkFramedRecovery.checkpoint.model
          Minidregg.Assurance.HyperdocumentLinkFramedRecovery.intent.erase ∧
      replayAll
          (DataSnapshot.install Endpoint.checkpoint
            Minidregg.Assurance.HyperdocumentLinkFramedRecovery.intent)
          [Minidregg.Assurance.HyperdocumentLinkFramedRecovery.intent] =
        .ok (DataSnapshot.install Endpoint.checkpoint
          Minidregg.Assurance.HyperdocumentLinkFramedRecovery.intent) ∧
      Endpoint.linkRecordCodec.decode
          (canonicalReceipt command).responseBytes =
        some Endpoint.record ∧
      ContentQuery.project Endpoint.query
          Endpoint.linkAccepted.accepted.prepared.post.logical =
        some Endpoint.record := by
  have lifecycle :=
    Endpoint.publish_lost_response_crash_recover_retry_reopen command.origin
  exact ⟨lost_response_restart_accepts command, lifecycle.1,
    lifecycle.2.2.1, (canonicalReceipt command).responseDecodes,
    lifecycle.2.2.2.2⟩

/-! ## Executable boundary teeth -/

def nativeFailure {NativeError : Type} (error : NativeError) :
    OpaqueSubmit NativeError :=
  fun _ => .error error

def loseEveryResponse {NativeError : Type} : OpaqueSubmit NativeError :=
  fun _ => .ok none

noncomputable def alteredResponse : List UInt8 :=
  Endpoint.resultBytes ++ [0]

theorem alteredResponse_ne : alteredResponse ≠ Endpoint.resultBytes := by
  intro equal
  have lengths := congrArg List.length equal
  simp [alteredResponse] at lengths

noncomputable def alteredResponseSubmit {NativeError : Type} :
    OpaqueSubmit NativeError :=
  fun _ => .ok (some alteredResponse)

@[simp] theorem native_failure_is_not_receipt {NativeError : Type}
    (error : NativeError) (command : LinkCommand) :
    submitLink (nativeFailure error) command = .native error := by
  rfl

@[simp] theorem two_lost_responses_are_not_receipt {NativeError : Type}
    (command : LinkCommand) :
    submitLink (loseEveryResponse (NativeError := NativeError)) command =
      .responseLostTwice := by
  rfl

@[simp] theorem altered_response_is_not_receipt {NativeError : Type}
    (command : LinkCommand) :
    submitLink (alteredResponseSubmit (NativeError := NativeError)) command =
      .malformedResponse alteredResponse := by
  simp [submitLink, alteredResponseSubmit, decodeReceipt,
    alteredResponse_ne]

/-! ## Concrete human and agent entry points -/

def humanCommand (sessionId interactionId : Nat) : LinkCommand :=
  ⟨.human sessionId interactionId⟩

def agentCommand (runId toolCallId : Nat) : LinkCommand :=
  ⟨.agent runId toolCallId⟩

@[simp] theorem human_cutover_reopens
    (sessionId interactionId : Nat) :
    (submitLink loseFirstEndpointResponse
      (humanCommand sessionId interactionId)).record? =
      some Endpoint.record :=
  lost_response_restart_reopens_exact_record _

@[simp] theorem agent_cutover_reopens
    (runId toolCallId : Nat) :
    (submitLink loseFirstEndpointResponse
      (agentCommand runId toolCallId)).record? =
      some Endpoint.record :=
  lost_response_restart_reopens_exact_record _

theorem human_agent_cutover_same_semantics
    (sessionId interactionId runId toolCallId : Nat) :
    (humanCommand sessionId interactionId).declarationBytes =
        (agentCommand runId toolCallId).declarationBytes ∧
      (humanCommand sessionId interactionId).requestBytes =
        (agentCommand runId toolCallId).requestBytes ∧
      (submitLink loseFirstEndpointResponse
          (humanCommand sessionId interactionId)).record? =
        (submitLink loseFirstEndpointResponse
          (agentCommand runId toolCallId)).record? :=
  ⟨rfl, rfl, by
    rw [human_cutover_reopens, agent_cutover_reopens]⟩

/-! ## Explicit deployment ceiling -/

/-- Required before this logical client cutover may be advertised as a
credentialed, physically delivered, externally final user experience.  The
client and endpoint provide no inhabitant.  Human UI rendering and agent
runtime delivery remain separate because neither one implies the other. -/
structure ExternalClientCompletion
    (CredentialsAuthenticated NetworkDelivered PhysicalIORefined
      ExternallyFinal HumanUiRendered AgentRuntimeDelivered : Prop) : Prop where
  credentialsAuthenticated : CredentialsAuthenticated
  networkDelivered : NetworkDelivered
  physicalIORefined : PhysicalIORefined
  externallyFinal : ExternallyFinal
  humanUiRendered : HumanUiRendered
  agentRuntimeDelivered : AgentRuntimeDelivered

/-! ## Axiom audit -/

/-- info: 'Minidregg.Assurance.HyperdocumentLinkClientCutover.lost_response_restart_accepts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
  #print axioms lost_response_restart_accepts
/-- info: 'Minidregg.Assurance.HyperdocumentLinkClientCutover.lost_response_restart_retry_receipt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
  #print axioms lost_response_restart_retry_receipt
/-- info: 'Minidregg.Assurance.HyperdocumentLinkClientCutover.human_agent_cutover_same_semantics' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
  #print axioms human_agent_cutover_same_semantics
/-- info: 'Minidregg.Assurance.HyperdocumentLinkClientCutover.altered_response_is_not_receipt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
  #print axioms altered_response_is_not_receipt

end

end Minidregg.Assurance.HyperdocumentLinkClientCutover
