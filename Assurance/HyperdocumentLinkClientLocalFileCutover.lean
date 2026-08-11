/-
# Assurance.HyperdocumentLinkClientLocalFileCutover -- file read to client receipt

This narrow join composes the independently committed client and local-file
boundaries.  A restarted file reader remains opaque and fallible.  If its one
observable result is the exact Lean-authored recovery fixture, the ordinary
client command may lose its first endpoint response, retry the identical
request after restart, and mint the same exact `AcceptedReceipt`.

The join proves only a read-result refinement.  The companion Rust lifecycle
test exercises real filesystem calls, but no theorem here identifies those
calls with the file model, `fsync`, stable media, network delivery, credential
authentication, external finality, UI rendering, or agent-runtime delivery.
-/
import Assurance.HyperdocumentLinkClientCutover
import Assurance.HyperdocumentLinkLocalFileStore

namespace Minidregg.Assurance.HyperdocumentLinkClientCutover.LocalFile

open Minidregg.Assurance.HyperdocumentLinkLocalFileStore
open Minidregg.Compiler.FramedWalRecoveryController
open Minidregg.Kernel.DurableDataIntent

set_option autoImplicit false

noncomputable section

/-! ## One observed restarted file boundary -/

/-- The native reader is still an opaque, fallible function.  Its exact result
is an observation supplied at the deployment seam, not a claim about why the
host filesystem produced those bytes. -/
structure RestartedBoundary (Error : Type) where
  reader : OpaqueFileRead Error
  observed : reader () = .ok recoveryFixture

noncomputable def storeEndpointCall {Error : Type}
    (boundary : RestartedBoundary Error) (call : IssuedCall) :
    Except (Endpoint.Failure Error) (List UInt8) :=
  Minidregg.Assurance.HyperdocumentLinkEndpointController.runAt
    Endpoint.checkpoint call.caller.origin call.requestBytes boundary.reader

@[simp] theorem storeEndpointCall_command {Error : Type}
    (boundary : RestartedBoundary Error) (command : LinkCommand)
    (attempt : Attempt) :
    storeEndpointCall boundary (command.issuedCall attempt) =
      .ok Endpoint.resultBytes := by
  simpa [storeEndpointCall, LinkCommand.issuedCall,
    LinkCommand.requestBytes] using
    endpoint_accepts_exact_restarted_read command.origin boundary.reader
      boundary.observed

noncomputable def deliverStore {Error : Type}
    (boundary : RestartedBoundary Error) :
    OpaqueSubmit (Endpoint.Failure Error) :=
  fun call =>
    match storeEndpointCall boundary call with
    | .error error => .error error
    | .ok bytes => .ok (some bytes)

/-- Execute the endpoint against the restarted reader on both attempts.  The
first successful response is discarded; the after-restart attempt delivers
the canonical response bytes to `submitLink`. -/
noncomputable def loseFirstStoreResponse {Error : Type}
    (boundary : RestartedBoundary Error) :
    OpaqueSubmit (Endpoint.Failure Error) :=
  fun call =>
    match call.attempt with
    | .initial =>
        match storeEndpointCall boundary call with
        | .error error => .error error
        | .ok _bytes => .ok none
    | .afterRestart => deliverStore boundary call

@[simp] theorem loseFirstStoreResponse_initial {Error : Type}
    (boundary : RestartedBoundary Error) (command : LinkCommand) :
    loseFirstStoreResponse boundary (command.issuedCall .initial) =
      .ok none := by
  change (match storeEndpointCall boundary (command.issuedCall .initial) with
    | Except.error error => Except.error error
    | Except.ok _bytes => Except.ok none) = Except.ok none
  rw [storeEndpointCall_command]

@[simp] theorem loseFirstStoreResponse_afterRestart {Error : Type}
    (boundary : RestartedBoundary Error) (command : LinkCommand) :
    loseFirstStoreResponse boundary (command.issuedCall .afterRestart) =
      .ok (some Endpoint.resultBytes) := by
  change deliverStore boundary (command.issuedCall .afterRestart) =
    .ok (some Endpoint.resultBytes)
  unfold deliverStore
  rw [storeEndpointCall_command]

@[simp] theorem file_lost_response_restart_accepts {Error : Type}
    (boundary : RestartedBoundary Error) (command : LinkCommand) :
    submitLink (loseFirstStoreResponse boundary) command =
      .accepted (canonicalReceipt command) := by
  simp [submitLink]

@[simp] theorem file_lost_response_restart_reopens {Error : Type}
    (boundary : RestartedBoundary Error) (command : LinkCommand) :
    (submitLink (loseFirstStoreResponse boundary) command).record? =
      some Endpoint.record := by
  rw [file_lost_response_restart_accepts]
  rfl

/-! ## The exact physical-read-result/client join -/

/-- The local read-result theorem and client receipt agree on the exact same
endpoint bytes.  Retry remains journal-idempotent, the response codec reopens
the concrete `LinkRecord`, and the client retains its proof-relevant receipt. -/
theorem restarted_file_to_exact_client_receipt {Error : Type}
    (boundary : RestartedBoundary Error) (command : LinkCommand) :
    submitLink (loseFirstStoreResponse boundary) command =
        .accepted (canonicalReceipt command) ∧
      replayAll
          (DataSnapshot.install Endpoint.checkpoint
            Minidregg.Assurance.HyperdocumentLinkFramedRecovery.intent)
          [Minidregg.Assurance.HyperdocumentLinkFramedRecovery.intent] =
        .ok (DataSnapshot.install Endpoint.checkpoint
          Minidregg.Assurance.HyperdocumentLinkFramedRecovery.intent) ∧
      Endpoint.linkRecordCodec.decode
          (canonicalReceipt command).responseBytes =
        some Endpoint.record ∧
      (canonicalReceipt command).record = Endpoint.record := by
  have reopened := installed_restart_retry_reopens_exact command.origin
    boundary.reader boundary.observed
  exact ⟨file_lost_response_restart_accepts boundary command,
    reopened.2.1, (canonicalReceipt command).responseDecodes,
    (canonicalReceipt command).recordExact⟩

/-! ## Closed control-model instantiation -/

/-- The bounded store control model supplies one closed restarted boundary.
This is useful for executable proof reduction; it is not a filesystem
refinement theorem. -/
def modelBoundary : RestartedBoundary StoreModel.Failure where
  reader := fun _ => StoreModel.read (StoreModel.crash StoreModel.publishedHonest)
  observed := StoreModel.install_lost_response_restart_reads_exact

@[simp] theorem model_human_client_reopens
    (sessionId interactionId : Nat) :
    (submitLink (loseFirstStoreResponse modelBoundary)
      (humanCommand sessionId interactionId)).record? =
      some Endpoint.record :=
  file_lost_response_restart_reopens _ _

@[simp] theorem model_agent_client_reopens
    (runId toolCallId : Nat) :
    (submitLink (loseFirstStoreResponse modelBoundary)
      (agentCommand runId toolCallId)).record? =
      some Endpoint.record :=
  file_lost_response_restart_reopens _ _

/-! ## Corrupt and fallible read teeth -/

noncomputable def corruptStoreSubmit {Error : Type} :
    OpaqueSubmit (Endpoint.Failure Error) :=
  fun call =>
    match Minidregg.Assurance.HyperdocumentLinkEndpointController.runAt
        Endpoint.checkpoint call.caller.origin call.requestBytes
        (fun _ => (Except.ok corruptChecksumFixture :
          Except Error (List UInt8))) with
    | .error error => .error error
    | .ok bytes => .ok (some bytes)

@[simp] theorem corruptStoreSubmit_command {Error : Type}
    (command : LinkCommand) (attempt : Attempt) :
    corruptStoreSubmit (Error := Error) (command.issuedCall attempt) =
      .error (.malformedStorage : Endpoint.Failure Error) := by
  change (match
    Minidregg.Assurance.HyperdocumentLinkEndpointController.runAt
      Endpoint.checkpoint command.origin command.requestBytes
      (fun _ => (Except.ok corruptChecksumFixture :
        Except Error (List UInt8))) with
    | Except.error error => Except.error error
    | Except.ok bytes => Except.ok (some bytes)) =
      Except.error (.malformedStorage : Endpoint.Failure Error)
  rw [show
    Minidregg.Assurance.HyperdocumentLinkEndpointController.runAt
        Endpoint.checkpoint command.origin command.requestBytes
        (fun _ => (Except.ok corruptChecksumFixture :
          Except Error (List UInt8))) = .error .malformedStorage by
      apply corrupt_file_bytes_fail_closed command.origin
      rfl]

@[simp] theorem corrupt_store_cannot_mint_client_receipt {Error : Type}
    (command : LinkCommand) :
    submitLink (corruptStoreSubmit (Error := Error)) command =
      .native (.malformedStorage : Endpoint.Failure Error) := by
  simp [submitLink]

noncomputable def nativeFileErrorSubmit {Error : Type} (error : Error) :
    OpaqueSubmit (Endpoint.Failure Error) :=
  fun call =>
    match Minidregg.Assurance.HyperdocumentLinkEndpointController.runAt
        Endpoint.checkpoint call.caller.origin call.requestBytes
        (fun _ => (Except.error error : Except Error (List UInt8))) with
    | .error endpointError => .error endpointError
    | .ok bytes => .ok (some bytes)

@[simp] theorem nativeFileErrorSubmit_command {Error : Type}
    (error : Error) (command : LinkCommand) (attempt : Attempt) :
    nativeFileErrorSubmit error (command.issuedCall attempt) =
      .error (.native error : Endpoint.Failure Error) := by
  change (match
    Minidregg.Assurance.HyperdocumentLinkEndpointController.runAt
      Endpoint.checkpoint command.origin command.requestBytes
      (fun _ => (Except.error error : Except Error (List UInt8))) with
    | Except.error endpointError => Except.error endpointError
    | Except.ok bytes => Except.ok (some bytes)) =
      Except.error (.native error : Endpoint.Failure Error)
  rw [show
    Minidregg.Assurance.HyperdocumentLinkEndpointController.runAt
        Endpoint.checkpoint command.origin command.requestBytes
        (fun _ => (Except.error error : Except Error (List UInt8))) =
      .error (.native error) by
      apply native_file_error_blocks command.origin
      rfl]

@[simp] theorem native_file_error_cannot_mint_client_receipt {Error : Type}
    (error : Error) (command : LinkCommand) :
    submitLink (nativeFileErrorSubmit error) command =
      .native (.native error : Endpoint.Failure Error) := by
  simp [submitLink]

/-! ## Combined ceiling remains uninhabited -/

/-- Physical durability and external client delivery are deliberately both
required at this join.  Neither the store conformance test nor the client
receipt manufactures these premises. -/
structure PhysicalClientCompletion
    (FileSyncRefined DirectorySyncRefined StableMedia NetworkDelivered
      CredentialsAuthenticated ExternallyFinal HumanUiRendered
      AgentRuntimeDelivered : Prop) : Prop where
  fileSyncRefined : FileSyncRefined
  directorySyncRefined : DirectorySyncRefined
  stableMedia : StableMedia
  networkDelivered : NetworkDelivered
  credentialsAuthenticated : CredentialsAuthenticated
  externallyFinal : ExternallyFinal
  humanUiRendered : HumanUiRendered
  agentRuntimeDelivered : AgentRuntimeDelivered

/-! ## Axiom audit -/

/-- info: 'Minidregg.Assurance.HyperdocumentLinkClientCutover.LocalFile.file_lost_response_restart_accepts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
  #print axioms file_lost_response_restart_accepts
/-- info: 'Minidregg.Assurance.HyperdocumentLinkClientCutover.LocalFile.restarted_file_to_exact_client_receipt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
  #print axioms restarted_file_to_exact_client_receipt
/-- info: 'Minidregg.Assurance.HyperdocumentLinkClientCutover.LocalFile.corrupt_store_cannot_mint_client_receipt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
  #print axioms corrupt_store_cannot_mint_client_receipt

end

end Minidregg.Assurance.HyperdocumentLinkClientCutover.LocalFile
