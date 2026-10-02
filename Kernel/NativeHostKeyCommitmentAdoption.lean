/- Host adapters for the source-owned first next-key commitment action. -/
import Kernel.NativeHost
import Kernel.SubjectKeyCommitmentAdoption

namespace Minidregg.Kernel.NativeHostKeyCommitmentAdoption
open Minidregg.Compiler Minidregg.Kernel Minidregg.Theory
open Minidregg.Theory.TypedAuthorization
open NativeHost
set_option autoImplicit false

structure PlanRequest where
  subject : SubjectId
  nonce : Nat
  currentPublicKey : List UInt8
  nextPublicKey : List UInt8

def planLoaded (config : Config) (opened : Opened config) (request : PlanRequest) :
    Except String SubjectKeyCommitmentAdoption.SigningPlan := do
  let some authority := CredentialAuthorityDomainReceiver.loadDeployment config.deployment opened.durable.snapshot
    | throw "authority cell unavailable"
  let some current := CredentialAuthorityState.currentSigningKey authority.snapshot.logical request.subject
    | throw "subject has no current signing key"
  if current.publicKey != request.currentPublicKey then throw "presented key is not current"
  let command : SubjectKeyCommitmentAdoption.Command :=
    ⟨request.subject, request.nonce, current, request.nextPublicKey⟩
  let _ ← (SubjectKeyCommitmentAdoption.prepare config.deployment config.profile.semantics opened.durable command)
    .mapError (fun reason => s!"adoption preparation: {repr reason}")
  return ⟨config.deployment.domain, config.profile.semantics,
    SubjectKeyCommitmentAdoption.commandCodec.encode command,
    SubjectKeyCommitmentAdoption.authorizationFrame config.deployment.domain config.profile.semantics command,
    SubjectKeyCommitmentAdoption.possessionFrame config.deployment.domain config.profile.semantics command⟩

def assemble (plan : SubjectKeyCommitmentAdoption.SigningPlan) (currentSignature nextSignature : List UInt8) :
    Except String (List UInt8) := do
  if currentSignature.length != 64 || nextSignature.length != 64 then throw "adoption signatures must be 64 bytes"
  let some command := SubjectKeyCommitmentAdoption.commandCodec.decode plan.commandBytes
    | throw "noncanonical adoption command"
  if plan.currentAuthorizationHeader != SubjectKeyCommitmentAdoption.authorizationFrame plan.domain plan.semantics command ||
      plan.nextPossessionHeader != SubjectKeyCommitmentAdoption.possessionFrame plan.domain plan.semantics command then
    throw "adoption signing frames differ from complete command"
  return SubjectKeyCommitmentAdoption.ingressCodec.encode ⟨plan.commandBytes, currentSignature, nextSignature⟩

private def refused (reason : NativeHostCodec.RefusalReason) (detail : String) : NativeHostCodec.Outcome :=
  .refused reason "adopt-next-key".toUTF8.toList detail.toUTF8.toList

def lookupLoaded (config : Config) (opened : Opened config) (bytes : List UInt8) : NativeHostCodec.Outcome :=
  match SubjectKeyCommitmentAdoption.decodeIngress bytes with
  | none => refused .malformed "noncanonical signed adoption"
  | some ingress =>
    match SubjectKeyCommitmentAdoption.replay config.deployment.domain config.profile.semantics opened.durable ingress with
    | some (.ok receipt) =>
      match historicalReceipt config opened.durable receipt.transactionId receipt.eventId with
      | none => .uncertain "original adoption receipt unavailable".toUTF8.toList
      | some original => .confirmed .replayed original
    | some (.error _) => refused .conflict "adoption marker conflict"
    | none => .absent

def submitLoaded (config : Config) (opened : Opened config) (bytes : List UInt8) : IO NativeHostCodec.Outcome := do
  match ← SubjectKeyCommitmentAdoption.receiveLoaded config.deployment config.profile.semantics
      config.signature config.transport opened.durable bytes with
  | .confirmed kind receipt =>
    match ← openExisting config with
    | .error detail => return .uncertain s!"adoption receipt readback: {detail}".toUTF8.toList
    | .ok post =>
      match historicalReceipt config post.durable receipt.transactionId receipt.eventId with
      | none => return .uncertain "original adoption receipt unavailable".toUTF8.toList
      | some original => return .confirmed kind original
  | .rejected reason => return refused .operationRejected s!"{repr reason}"
  | .transactionConflict => return refused .conflict "adoption marker conflict"
  | .durableRejected reason => return refused .operationRejected s!"durable: {repr reason}"
  | .contention => return .contention
  | .unavailable detail => return .unavailable detail.toUTF8.toList
  | .uncertain detail => return .uncertain detail.toUTF8.toList
end Minidregg.Kernel.NativeHostKeyCommitmentAdoption
