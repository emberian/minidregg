/-
Canonical data for one app-governed dispatch share. A share uses its own content
resource: the bounded content page holds one stable ticket atom, so the number
of sessions is not limited by the four-atom capacity of one shared page.

This module does not authorize a ticket's issuance. The native share-issue
receiver must bind the exact ticket and resource to one admitted composite
app-delegation + resource-birth event. A dispatch receiver must select that
event from verified history, read-guard this resource's current page, and check
the current participant/app/session capabilities and laws at one image.
Participant-owned enrollment is only a requested role, never the ceiling.
-/
import Kernel.ApplicationPermissionSchema
import Kernel.ApplicationDispatchManifest
import Kernel.ContentResource

namespace Minidregg.Kernel.ApplicationDispatchAuthority
open Minidregg.Compiler
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Compiler.ResourceBirthCodec
open Minidregg.Compiler.HyperdocumentContentPageMaterializer
open Minidregg.Theory
open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.Hyperdocument
open Minidregg.Theory.IndexedProgram
open Minidregg.Kernel.ApplicationDispatchCodec
open Minidregg.Kernel.ApplicationGrainSessionEnrollment
open Minidregg.Kernel.ApplicationPermissionSchema
set_option autoImplicit false

/-- Durable app/interface/schema selector for this share. The app's serving
generation is a wake fence checked at dispatch, not a grant epoch; a restart
must not invalidate a share. A package/interface/schema change does require
explicit app-governed reissue under this conservative v1 profile. -/
structure Scope where
  app : Nat
  packageVersion : Int
  packageRoot : Digest
  interfaceId : Nat
  interfaceVersion : Nat
  interfaceRoot : Digest
  schemaRoot : Digest
  schemaVersion : Nat
  deriving DecidableEq, Repr

def scopeStream : StreamCodec Scope :=
  StreamCodec.xmap
    (StreamCodec.product StreamCodec.nat
      (StreamCodec.product DeclaredEffectPageMaterializer.intStream
          (StreamCodec.product digestStream
            (StreamCodec.product StreamCodec.nat
              (StreamCodec.product StreamCodec.nat
                (StreamCodec.product digestStream
                  (StreamCodec.product digestStream StreamCodec.nat)))))))
    (fun s => (s.app, s.packageVersion, s.packageRoot,
      s.interfaceId, s.interfaceVersion, s.interfaceRoot, s.schemaRoot, s.schemaVersion))
    (fun (app, packageVersion, packageRoot, interfaceId,
          interfaceVersion, interfaceRoot, schemaRoot, schemaVersion) =>
      ⟨app, packageVersion, packageRoot, interfaceId,
        interfaceVersion, interfaceRoot, schemaRoot, schemaVersion⟩)
    (by intro s; cases s; rfl)

/-- The session and the exact current app-observe capability selector. The
selected capability is rechecked at dispatch; its identifier alone is not a
grant. `origin` retains the mandatory agent task/generation when applicable. -/
structure Participant where
  session : Nat
  descriptorResource : Nat
  kind : InterfaceKind
  subject : SubjectId
  origin : Origin
  sessionCapability : CapabilityId
  appObserveCapability : CapabilityId
  deriving DecidableEq, Repr

def participantStream : StreamCodec Participant :=
  StreamCodec.xmap
    (StreamCodec.product StreamCodec.nat
      (StreamCodec.product StreamCodec.nat
          (StreamCodec.product interfaceKindStream
            (StreamCodec.product TypedAuthorizationRequestCodec.subjectIdStream
              (StreamCodec.product originStream
                (StreamCodec.product CredentialAuthorityEntryCodec.capabilityIdStream
                  CredentialAuthorityEntryCodec.capabilityIdStream))))))
    (fun p => (p.session, p.descriptorResource, p.kind,
      p.subject, p.origin, p.sessionCapability, p.appObserveCapability))
    (fun (session, descriptorResource, kind, subject,
          origin, sessionCapability, appObserveCapability) =>
      ⟨session, descriptorResource, kind, subject,
        origin, sessionCapability, appObserveCapability⟩)
    (by intro p; cases p; rfl)

/-- A single-share ticket. `resource` is a distinct content resource born by
the special app-authorized issue turn. The ticket has no caller-selected
issuer subject: issuer provenance is the admitted composite event, not bytes
inside the ticket. `ceiling` is resolved against the installed schema on each
dispatch, then intersected with the participant's requested enrollment role. -/
structure Ticket where
  resource : Nat
  scope : Scope
  participant : Participant
  ceiling : RoleAssignment
  issueNonce : Nat
  deriving DecidableEq, Repr

def ticketStream : StreamCodec Ticket :=
  StreamCodec.xmap
    (StreamCodec.product StreamCodec.nat
      (StreamCodec.product scopeStream
        (StreamCodec.product participantStream
          (StreamCodec.product roleAssignmentStream StreamCodec.nat))))
    (fun t => (t.resource, t.scope, t.participant, t.ceiling, t.issueNonce))
    (fun (resource, scope, participant, ceiling, issueNonce) =>
      ⟨resource, scope, participant, ceiling, issueNonce⟩)
    (by intro t; cases t; rfl)

private def ticketFrame : List UInt8 :=
  "DREGG/APPLICATION/SHARE-TICKET/v1".toUTF8.toList

private def rawTicketCodec : LawfulCodec Ticket where
  encode ticket := ticketFrame ++ ticketStream.encode ticket
  decode bytes := if bytes.take ticketFrame.length = ticketFrame then
    ticketStream.toLawful.decode (bytes.drop ticketFrame.length) else none
  decode_encode := by
    intro ticket
    have decoded := ticketStream.toLawful.decode_encode ticket
    change ticketStream.toLawful.decode (ticketStream.encode ticket) = some ticket at decoded
    simp [decoded]

def ticketCodec : LawfulCodec Ticket := ResourceBirthCodec.strictCodec rawTicketCodec

theorem ticket_decode_encode (ticket : Ticket) :
    ticketCodec.decode (ticketCodec.encode ticket) = some ticket :=
  ticketCodec.decode_encode ticket

theorem ticket_bytes_injective : Function.Injective ticketCodec.encode := by
  intro left right same
  have decoded := congrArg ticketCodec.decode same
  exact Option.some.inj (by simpa only [ticketCodec.decode_encode] using decoded)

/-- One atom in each ticket resource. Replacing a ticket requires an exact
old-record edit under the app-governed sharing law; issue provenance and any
replacement must be independently checked by the receiving selector. -/
def ticketAtom (domain : Digest) (resource : Nat) : AtomId :=
  let preimage := (StreamCodec.product digestStream StreamCodec.nat).encode (domain, resource)
  ⟨⟨(Sp800185Cshake256.hash
    "DREGG/APPLICATION/SHARE-TICKET-ATOM/v1".toUTF8.toList preimage).digest.value⟩⟩

def decodeInstalled (domain : Digest) (resource : Nat)
    (page : HyperdocumentContentPageMaterializer.Page) : Option Ticket := do
  if page.contentDomain != domain || page.document != ⟨⟨resource⟩⟩ then none else
  let record ← Hyperdocument.lookup page.toCanonicalState .atoms (ticketAtom domain resource)
  if record.document != page.document || record.kind != .inlineObject ⟨15⟩ ||
      record.tombstonedAt.isSome then none else
  let ticket ← ticketCodec.decode record.payload
  if ticket.resource == resource && ticket.ceiling.valid then some ticket else none

def initialAction (domain : Digest) (ticket : Ticket) : ContentResource.Action :=
  .createAtom (ticketAtom domain ticket.resource) (.inlineObject ⟨15⟩)
    (ticketCodec.encode ticket)

/-- These selector equalities are necessary, not sufficient, for dispatch:
the special receiver must source the installed ticket through the accepted
share-issue event and a read guard, then run current native capability/law
checks at the same image as the session and app. -/
def Ticket.matches (ticket : Ticket) (dispatch : Dispatch)
    (enrollment : Enrollment) (schema : Schema) : Bool :=
  decide (ticket.scope.app = dispatch.app.resource) &&
  decide (ticket.scope.packageVersion = dispatch.app.packageVersion) &&
  decide (ticket.scope.packageRoot = dispatch.app.packageRoot) &&
  decide (ticket.scope.interfaceId = dispatch.app.interfaceId) &&
  decide (ticket.scope.interfaceVersion = dispatch.app.interfaceVersion) &&
  decide (ticket.scope.interfaceRoot = dispatch.app.interfaceRoot) &&
  decide (ticket.scope.schemaRoot = schema.root) &&
  decide (ticket.scope.schemaVersion = schema.version) &&
  decide (ticket.scope.schemaRoot = dispatch.identity.permissionSchemaRoot) &&
  decide (ticket.participant.session = dispatch.session.resource) &&
  decide (ticket.participant.descriptorResource = enrollment.descriptorResource) &&
  decide (ticket.participant.kind = dispatch.session.kind) &&
  decide (ticket.participant.subject = dispatch.session.subject) &&
  decide (ticket.participant.origin = dispatch.session.origin) &&
  decide (ticket.participant.sessionCapability = dispatch.session.capability) &&
  decide (ticket.participant.appObserveCapability = dispatch.app.capability) &&
  enrollment.matchesSession dispatch.session

/-- Executable pointwise ceiling. The equal-length check is deliberate: an
omitted high permission bit cannot silently change the selected schema. HTTP
method does not enter this comparison. -/
def withinCeilingCheck : List Bool → List Bool → Bool
  | [], [] => true
  | requested :: rest, ceiling :: ceilingRest =>
      (!requested || ceiling) && withinCeilingCheck rest ceilingRest
  | _, _ => false

theorem withinCeilingCheck_length {requested ceiling : List Bool}
    (accepted : withinCeilingCheck requested ceiling = true) :
    requested.length = ceiling.length := by
  induction requested generalizing ceiling with
  | nil => cases ceiling <;> simp [withinCeilingCheck] at *
  | cons bit rest ih =>
      cases ceiling with
      | nil => simp [withinCeilingCheck] at accepted
      | cons limit limits =>
          have tail : withinCeilingCheck rest limits = true := by
            cases bit <;> cases limit <;> simp [withinCeilingCheck] at accepted ⊢
            all_goals assumption
          simpa only [List.length_cons, Nat.succ_inj] using ih tail

theorem withinCeilingCheck_index {requested ceiling : List Bool}
    (accepted : withinCeilingCheck requested ceiling = true) (index : Nat)
    (raised : requested[index]?.getD false = true) :
    ceiling[index]?.getD false = true := by
  induction requested generalizing ceiling index with
  | nil => simp at raised
  | cons bit rest ih =>
      cases ceiling with
      | nil => simp [withinCeilingCheck] at accepted
      | cons limit limits =>
          have tail : withinCeilingCheck rest limits = true := by
            cases bit <;> cases limit <;> simp [withinCeilingCheck] at accepted ⊢
            all_goals assumption
          cases index with
          | zero =>
              simp only [List.getElem?_cons_zero, Option.getD_some] at raised ⊢
              cases bit <;> cases limit <;> simp_all [withinCeilingCheck]
          | succ index =>
              simpa only [List.getElem?_cons_succ] using ih tail index raised

theorem withinCeilingCheck_sound {requested ceiling : List Bool}
    (accepted : withinCeilingCheck requested ceiling = true) :
    ApplicationPermissionSchema.withinCeiling requested ceiling :=
  ⟨withinCeilingCheck_length accepted, withinCeilingCheck_index accepted⟩

/-- A selector and role-math check only. `some` cannot be interpreted as
native authorization without accepted issue provenance, current read guards,
capability lineage/revocation, and the special dispatch event admission. -/
def eligibleBits (ticket : Ticket) (dispatch : Dispatch)
    (enrollment : Enrollment) (schema : Schema) : Option (List Bool) :=
  if ticket.matches dispatch enrollment schema then
    match schema.resolve enrollment.role, schema.resolve ticket.ceiling with
    | some requested, some ceiling =>
        if withinCeilingCheck requested ceiling then some requested else none
    | _, _ => none
  else none

theorem eligibleBits_within (ticket : Ticket) (dispatch : Dispatch)
    (enrollment : Enrollment) (schema : Schema) (requested : List Bool)
    (accepted : eligibleBits ticket dispatch enrollment schema = some requested) :
    ∃ ceiling, schema.resolve ticket.ceiling = some ceiling ∧
      ApplicationPermissionSchema.withinCeiling requested ceiling := by
  unfold eligibleBits at accepted
  split at accepted
  · cases hrequested : schema.resolve enrollment.role with
    | none => simp [hrequested] at accepted
    | some selected =>
        cases hceiling : schema.resolve ticket.ceiling with
        | none => simp [hrequested, hceiling] at accepted
        | some ceiling =>
            simp [hrequested, hceiling] at accepted
            rcases accepted with ⟨hwithin, rfl⟩
            exact ⟨ceiling, rfl, withinCeilingCheck_sound hwithin⟩
  · contradiction

theorem self_escalation_refused (ticket : Ticket) (dispatch : Dispatch)
    (enrollment : Enrollment) (schema : Schema)
    (requested ceiling : List Bool) (index : Nat)
    (hrequested : schema.resolve enrollment.role = some requested)
    (hceiling : schema.resolve ticket.ceiling = some ceiling)
    (raised : requested[index]?.getD false = true)
    (forbidden : ceiling[index]?.getD false = false) :
    eligibleBits ticket dispatch enrollment schema = none := by
  have notWithin : withinCeilingCheck requested ceiling = false := by
    cases check : withinCeilingCheck requested ceiling with
    | false => rfl
    | true =>
        have permitted := withinCeilingCheck_index check index raised
        simp [forbidden] at permitted
  simp [eligibleBits, hrequested, hceiling, notWithin]

end Minidregg.Kernel.ApplicationDispatchAuthority
