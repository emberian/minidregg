/-
An explicitly app-delegated, task-lifetime agent route. This canonical record is
data in an ordinary content resource. Its birth or content receipt is never an
app grant: a later distinct paid-dispatch receiver must prove historical app
delegation at the original verifier-authenticated prefix, check current law,
the installed record, and a fresh parent execution witness at the loaded tip.
The old event21 ticket and enrollment remain generation-bound.
-/
import Kernel.ApplicationShareIssueSource

namespace Minidregg.Kernel.ApplicationAgentLifetimeGrant

open Minidregg.Compiler
open Minidregg.Compiler.ResourceBirthCodec
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Theory
open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.IndexedProgram
open Minidregg.Theory.Hyperdocument
open Minidregg.Kernel.ApplicationDispatchAuthority
open Minidregg.Kernel.ApplicationShareIssueSource
open Minidregg.Kernel.NativeHost

set_option autoImplicit false

/-- Exact historical issue and the independent current grant resource. -/
structure Source where
  resource : Nat
  issueIndex : Nat
  issueReceipt : NativeHostCodec.Receipt
  ticketResource : Nat
  ticketDigest : Digest
  deriving DecidableEq

def sourceStream : StreamCodec Source :=
  StreamCodec.xmap
    (StreamCodec.product StreamCodec.nat
      (StreamCodec.product StreamCodec.nat
        (StreamCodec.product NativeHostCodec.receiptStream
          (StreamCodec.product StreamCodec.nat digestStream))))
    (fun source => (source.resource, source.issueIndex, source.issueReceipt,
      source.ticketResource, source.ticketDigest))
    (fun (resource, issueIndex, issueReceipt, ticketResource, ticketDigest) =>
      ⟨resource, issueIndex, issueReceipt, ticketResource, ticketDigest⟩)
    (by intro source; cases source; rfl)

/-- The original generation is issuance provenance, not the execution epoch
for later HTTP requests. The latter requires a fresh signed parent witness.
Task lifetime additionally relies on the fixed deployment's resource ID
non-reuse law; a recycled task ID must never inherit this grant. -/
structure Participant where
  app : Nat
  session : Nat
  subject : SubjectId
  parentTask : Nat
  originalGeneration : Int
  grantObserveCapability : CapabilityId
  deriving DecidableEq

def participantStream : StreamCodec Participant :=
  StreamCodec.xmap
    (StreamCodec.product StreamCodec.nat
      (StreamCodec.product StreamCodec.nat
        (StreamCodec.product TypedAuthorizationRequestCodec.subjectIdStream
          (StreamCodec.product StreamCodec.nat
            (StreamCodec.product IntStream.intStream
              CredentialAuthorityEntryCodec.capabilityIdStream)))))
    (fun participant => (participant.app, participant.session,
      participant.subject, participant.parentTask, participant.originalGeneration,
      participant.grantObserveCapability))
    (fun (app, session, subject, parentTask, originalGeneration,
          grantObserveCapability) =>
      ⟨app, session, subject, parentTask, originalGeneration,
        grantObserveCapability⟩)
    (by intro participant; cases participant; rfl)

/-- The app delegate's selected capability needs historical admission at the
grant installation prefix and a separate current revocation/law check. This
record does not itself certify either fact. -/
structure Approval where
  issuer : SubjectId
  delegateCapability : CapabilityId
  ceiling : ApplicationGrainSessionEnrollment.RoleAssignment
  nonce : Nat
  deriving DecidableEq

def approvalStream : StreamCodec Approval :=
  StreamCodec.xmap
    (StreamCodec.product TypedAuthorizationRequestCodec.subjectIdStream
      (StreamCodec.product CredentialAuthorityEntryCodec.capabilityIdStream
        (StreamCodec.product ApplicationGrainSessionEnrollment.roleAssignmentStream
          StreamCodec.nat)))
    (fun approval => (approval.issuer, approval.delegateCapability,
      approval.ceiling, approval.nonce))
    (fun (issuer, delegateCapability, ceiling, nonce) =>
      ⟨issuer, delegateCapability, ceiling, nonce⟩)
    (by intro approval; cases approval; rfl)

structure Grant where
  source : Source
  participant : Participant
  approval : Approval
  deriving DecidableEq

def grantStream : StreamCodec Grant :=
  StreamCodec.xmap
    (StreamCodec.product sourceStream
      (StreamCodec.product participantStream approvalStream))
    (fun grant => (grant.source, grant.participant, grant.approval))
    (fun (source, participant, approval) => ⟨source, participant, approval⟩)
    (by intro grant; cases grant; rfl)

def codec : LawfulCodec Grant := NativeHostCodec.framed
  "DREGG/APPLICATION/AGENT-LIFETIME-GRANT/v1".toUTF8.toList grantStream

def Grant.canonicalBytes (grant : Grant) : List UInt8 := codec.encode grant

theorem decode_encode (grant : Grant) :
    codec.decode grant.canonicalBytes = some grant := codec.decode_encode grant

theorem canonicalBytes_injective : Function.Injective Grant.canonicalBytes := by
  intro left right same
  have decoded := congrArg codec.decode same
  exact Option.some.inj (by simpa only [decode_encode] using decoded)

/-- This preimage identifies an issuance-time signature. It must be checked
against its historical authority snapshot, not treated as a fresh envelope
after unrelated authority or app revisions. -/
def Grant.delegationPreimage (grant : Grant) : List UInt8 :=
  "DREGG/APPLICATION/AGENT-LIFETIME-DELEGATION/v1".toUTF8.toList ++
    grant.canonicalBytes

theorem delegationPreimage_injective : Function.Injective Grant.delegationPreimage := by
  intro left right same
  apply canonicalBytes_injective
  exact List.append_cancel_left same

/-- Stable address inside the separately born ordinary content resource. -/
def grantAtom (domain : Digest) (resource : Nat) : AtomId :=
  let preimage := (StreamCodec.product digestStream StreamCodec.nat).encode
    (domain, resource)
  ⟨⟨(Sp800185Cshake256.hash
    "DREGG/APPLICATION/AGENT-LIFETIME-GRANT-ATOM/v1".toUTF8.toList
    preimage).digest.value⟩⟩

/-- Decoding present current data is not admission of app delegation. Event27
must have installed the exact atom under its own historical certificate, and
event26 must check this current physical cell, current law/capabilities, and
the separate current parent/purse states. -/
def decodeInstalled (domain : Digest) (resource : Nat)
    (page : ContentResource.ContentStore) : Option Grant := do
  let record ← Hyperdocument.lookup page .atoms (grantAtom domain resource)
  if record.document != ⟨⟨resource⟩⟩ || record.kind != .inlineObject ⟨16⟩ ||
      record.tombstonedAt.isSome then none else
  let grant ← codec.decode record.payload
  if grant.source.resource == resource && grant.approval.ceiling.valid then
    some grant else none

def initialAction (domain : Digest) (grant : Grant) : ContentResource.Action :=
  .createAtom (grantAtom domain grant.source.resource) (.inlineObject ⟨16⟩)
    grant.canonicalBytes

def ticketDigest (ticket : Ticket) : Digest :=
  (Sp800185Cshake256.hash
    "DREGG/APPLICATION/AGENT-LIFETIME-TICKET/v1".toUTF8.toList
    (ticketCodec.encode ticket)).digest

/-- Scope equality is deliberately strict for the first lifetime profile:
the lifetime grant may not increase or reinterpret the original ticket's
role ceiling. A future subset profile needs a separate checked schema proof. -/
def Grant.matchesIssued (grant : Grant) (spec : Spec) (issueIndex : Nat)
    (receipt : NativeHostCodec.Receipt) : Bool :=
  decide (grant.source.issueIndex = issueIndex ∧
    grant.source.issueReceipt = receipt ∧
    grant.source.ticketResource = spec.ticket.resource ∧
    grant.source.ticketDigest = ticketDigest spec.ticket ∧
    grant.source.resource ≠ spec.ticket.resource ∧
    grant.source.resource ≠ spec.ticket.scope.app ∧
    grant.source.resource ≠ spec.ticket.participant.session ∧
    grant.participant.app = spec.ticket.scope.app ∧
    grant.participant.session = spec.ticket.participant.session ∧
    grant.participant.subject = spec.ticket.participant.subject ∧
    spec.ticket.participant.origin = .agent grant.participant.parentTask
      grant.participant.originalGeneration ∧
    grant.approval.issuer = spec.issuer ∧
    grant.approval.delegateCapability = spec.appDelegateCapability ∧
    grant.approval.ceiling = spec.ticket.ceiling)

theorem matchesIssued_scope (grant : Grant) (spec : Spec) (issueIndex : Nat)
    (receipt : NativeHostCodec.Receipt)
    (matched : grant.matchesIssued spec issueIndex receipt = true) :
    grant.source.ticketResource = spec.ticket.resource ∧
    grant.participant.app = spec.ticket.scope.app ∧
    grant.participant.session = spec.ticket.participant.session ∧
    grant.participant.subject = spec.ticket.participant.subject ∧
    spec.ticket.participant.origin = .agent grant.participant.parentTask
      grant.participant.originalGeneration ∧
    grant.approval.ceiling = spec.ticket.ceiling := by
  simp only [Grant.matchesIssued, decide_eq_true_eq] at matched
  rcases matched with
    ⟨_, _, ticket, _, _, _, _, app, session, subject, origin, _, _, ceiling⟩
  exact ⟨ticket, app, session, subject, origin, ceiling⟩

end Minidregg.Kernel.ApplicationAgentLifetimeGrant
