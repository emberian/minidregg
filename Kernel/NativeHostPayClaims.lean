/-
Fixed native wrappers for v2 paid-entry receiving. These functions expose only
source status, source quote, closed claim signing/assembly, submit and exact
lookup. They neither issue chain transactions nor accept arbitrary execution.
-/
import Kernel.NativeHost
import Kernel.PayClaimQuote
import Kernel.PayClaimReceiver
import Kernel.PayClaimStatus

namespace Minidregg.Kernel.NativeHost
open Minidregg.Compiler
open Minidregg.Compiler.NativeHostCodec
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Theory.TypedAuthorization (Digest)
open Minidregg.Theory.IndexedProgram (LawfulCodec)
set_option autoImplicit false
attribute [local irreducible] Config.profile

structure ClaimSigningPlan where
  domain : Digest
  semantics : Digest
  command : PayClaimCommand.Command
  deriving DecidableEq, Repr

def claimSigningPlanStream : StreamCodec ClaimSigningPlan :=
  StreamCodec.xmap
    (StreamCodec.product digestStream (StreamCodec.product digestStream PayClaimCommand.commandStream))
    (fun plan => (plan.domain, plan.semantics, plan.command))
    (fun (domain, semantics, command) => ⟨domain, semantics, command⟩)
    (by intro plan; cases plan; rfl)

def claimSigningPlanCodec : LawfulCodec ClaimSigningPlan :=
  ParticipantKeyEnrollment.framed "DREGG/PAY/CLAIM/PLAN/v1".toUTF8.toList claimSigningPlanStream

def ClaimSigningPlan.signingBytes (plan : ClaimSigningPlan) : List UInt8 :=
  PayClaimCommand.possessionFrame plan.domain plan.semantics plan.command

/-- Prepare exactly the caller-retained closed command. Roots are checked,
never silently rebased; a deliberate later quote/preparation is another action. -/
def payClaimPlanLoaded (config : Config) (opened : Opened config) (bytes : List UInt8) :
    Except String ClaimSigningPlan := do
  check (decide (bytes.length ≤ 2048)) "claim command exceeds 2048-byte bound"
  let command ← need "noncanonical claim command" (PayClaimCommand.commandCodec.decode bytes)
  check (decide command.valid) "claim command shape refused"
  let pay ← need "pay cell unavailable" (PayCellDomain.load config.deployment opened.durable.snapshot)
  check (command.expectedAuthorityRoot == opened.authority.snapshot.cell.root) "claim authority root changed"
  check (command.expectedPayRoot == pay.cell.root) "claim pay root changed"
  pure ⟨config.deployment.domain, config.profile.semantics, command⟩

/-- Assembly is pure and verifies plan shape; only the receiving native
signature check can authorize the assembled ingress. -/
def payClaimAssemble (planBytes signature : List UInt8) : Except String (List UInt8) := do
  check (decide (planBytes.length ≤ 3072)) "claim plan exceeds 3072-byte bound"
  check (signature.length == 64) "claim possession signature must be 64 bytes"
  let plan ← need "noncanonical claim plan" (claimSigningPlanCodec.decode planBytes)
  check (decide plan.command.valid) "claim command shape refused"
  let bytes := PayClaimCommand.ingressCodec.encode
    ⟨PayClaimCommand.commandCodec.encode plan.command, signature⟩
  check (decide (bytes.length ≤ PayClaimCommand.maxIngressBytes)) "claim ingress exceeds source bound"
  pure bytes

/-- Canonical source status stays exact-key/bounded; no view/journal scan. -/
def payClaimStatusLoaded (config : Config) (opened : Opened config) (bytes : List UInt8) : Except String (List UInt8) := do
  let pay ← need "pay cell unavailable" (PayCellDomain.load config.deployment opened.durable.snapshot)
  let clock ← need "authenticated clock unavailable" (ClockCellDomain.load config.deployment opened.durable.snapshot)
  (PayClaimStatus.serve pay.cell.logical clock.clock bytes).mapError (fun reason => s!"paid status: {repr reason}")

/-- Exact quote source uses the same live birth descriptor as receiving. -/
def payClaimPricing (config : Config) (opened : Opened config) (identity : List UInt8) : PayEnrolV2Decision.Pricing :=
  ⟨config.deployment.domain, config.expectedSeed, config.profile.semantics, config.tariff, config.profile.template,
    PayEnrolReceiver.birthFee config.deployment config.profile.semantics config.profile.template
      config.tariff opened.authority.snapshot.cell (logicalHeight config opened.durable)
      (PayEnrolReceiver.ids config.deployment.domain identity) 0⟩

def payClaimSubmitLoaded (config : Config) (opened : Opened config) (bytes : List UInt8) : IO Outcome := do
  match ← PayClaimReceiver.receiveLoaded config.deployment config.profile (payEnrolAmbient config opened)
      config.expectedSeed config.signature config.transport opened.durable bytes with
  | .confirmed kind receipt => confirmed config kind receipt.transactionId receipt.eventId
  | .rejected reason => return refused .operationRejected "pay-claim" s!"{repr reason}"
  | .transactionConflict => return refused .conflict "replay" "claim transaction identity conflict"
  | .durableRejected reason => return durableRefusal reason
  | .contention => return .contention
  | .unavailable detail => return .unavailable detail.toUTF8.toList
  | .uncertain detail => return .uncertain detail.toUTF8.toList

/-- No submission or redecision occurs here. Exact old-source lookup after a
profile carry uses the retained source-profile path, not this current-profile
wrapper. Native operation records must retain their original profile pin. -/
def payClaimLookupLoaded (config : Config) (opened : Opened config) (bytes : List UInt8) : Outcome :=
  match PayClaimCommand.decodeIngress bytes with
  | none => refused .malformed "pay-claim" "noncanonical signed claim ingress"
  | some ingress =>
    match PayClaimReceiver.replay config.deployment.domain config.profile.semantics opened.durable ingress with
    | none => .absent
    | some (.error _) => refused .conflict "replay" "claim transaction identity conflict"
    | some (.ok receipt) =>
      match historicalReceipt config opened.durable receipt.transactionId receipt.eventId with
      | some original => .confirmed .replayed original
      | none => .uncertain "original claim receipt prefix unavailable".toUTF8.toList

/-- The same operator observer ingress supports v1 and canonical v2 memos.
Malformed/unsupported memo bytes retain the explicit legacy journal path. -/
def payEnrolPlanCurrentLoaded (config : Config) (opened : Opened config) (bytes : List UInt8) :
    IO (Except String PayCellDomain.SigningPlan) := do
  let some command := PayEnrolReceiver.commandCodec.decode bytes
    | return .error "noncanonical pay enrollment command"
  if (PayEnrolV2Receiver.parsedMemo command.observation).isSome then
    match ← PayEnrolV2Receiver.signingHeader config.deployment config.profile (payEnrolAmbient config opened)
        config.expectedSeed opened.durable config.signature command with
    | .error detail => return .error detail
    | .ok header => return .ok ⟨config.deployment.domain, config.profile.semantics, bytes,
        CredentialSignedEnvelopeController.headerCodec.encode header⟩
  else payEnrolPlanLoaded config opened bytes

def payEnrolSubmitCurrentLoaded (config : Config) (opened : Opened config) (bytes : List UInt8) : IO Outcome := do
  let some ingress := PayEnrolReceiver.decodeIngress bytes
    | return refused .malformed "pay-enrol" "noncanonical signed enrollment ingress"
  if (PayEnrolV2Receiver.parsedMemo ingress.command.observation).isSome then
    receivingSubmitLoaded config opened
      (PayEnrolV2Receiver.payEnrolV2Family config.deployment config.profile)
      ⟨payEnrolAmbient config opened, config.expectedSeed⟩ "pay-enrol-v2" bytes
  else payEnrolSubmitLoaded config opened bytes

end Minidregg.Kernel.NativeHost
