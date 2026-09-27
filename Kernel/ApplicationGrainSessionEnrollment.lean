/-
Canonical enrolled meaning for a revocable application session. These bytes
are data inside a separately governed content resource, not caller authority.
The native receiver must select that resource from installed session policy,
read-guard its current root, check current capability lineage, and resolve role
permissions against the currently installed app manifest before dispatch.
-/
import Kernel.ApplicationGrainSession
import Kernel.ApplicationDispatchCodec
import Kernel.ContentResource

namespace Minidregg.Kernel.ApplicationGrainSessionEnrollment
open Minidregg.Compiler
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Compiler.ResourceBirthCodec
open Minidregg.Compiler.DeclaredEffectPageMaterializer
open Minidregg.Compiler.HyperdocumentContentPageMaterializer
open Minidregg.Theory
open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.Hyperdocument
open Minidregg.Theory.IndexedProgram
open Minidregg.Kernel.ApplicationDispatchCodec
set_option autoImplicit false

/-- Sandstorm-style assigned role basis. The added/removed names are retained
separately; effective bits are recomputed from current ViewInfo/role data. -/
inductive RoleBasis where
  | none
  | allAccess
  | role (id : Nat)
  deriving DecidableEq, Repr

def RoleBasis.toWire : RoleBasis → Nat × Option Nat
  | .none => (0, Option.none)
  | .allAccess => (1, Option.none)
  | .role roleId => (2, some roleId)

def RoleBasis.ofWire : Nat × Option Nat → Option RoleBasis
  | (0, Option.none) => some .none
  | (1, Option.none) => some .allAccess
  | (2, some roleId) => some (.role roleId)
  | _ => Option.none

def roleBasisStream : StreamCodec RoleBasis :=
  StreamCodec.xmap
    (StreamCodec.product StreamCodec.nat (StreamCodec.option StreamCodec.nat))
    RoleBasis.toWire
    (fun wire => (RoleBasis.ofWire wire).getD .none)
    (by intro basis; cases basis <;> rfl)

/-- `roleSchemaRoot` is a selector to be checked against the current
installed ViewInfo schema, not a frozen effective permission bitmap. -/
structure RoleAssignment where
  basis : RoleBasis
  added : List (List UInt8)
  removed : List (List UInt8)
  roleSchemaRoot : Digest
  roleVersion : Nat
  deriving DecidableEq, Repr

def roleAssignmentStream : StreamCodec RoleAssignment :=
  StreamCodec.xmap
    (StreamCodec.product roleBasisStream
      (StreamCodec.product (StreamCodec.list bytesStream)
        (StreamCodec.product (StreamCodec.list bytesStream)
          (StreamCodec.product digestStream StreamCodec.nat))))
    (fun role => (role.basis, role.added, role.removed,
      role.roleSchemaRoot, role.roleVersion))
    (fun (basis, added, removed, schemaRoot, version) =>
      ⟨basis, added, removed, schemaRoot, version⟩)
    (by intro role; cases role; rfl)

/-- A full enrollment epoch, including origin. An agent-origin enrollment
cannot omit its parent task/generation through this sum. Capability IDs and
schema roots are selectors; admission checks current native grant and law. -/
structure Enrollment where
  session : Nat
  descriptorResource : Nat
  app : Nat
  appGeneration : Int
  sessionGeneration : Int
  kind : InterfaceKind
  subject : SubjectId
  capability : CapabilityId
  role : RoleAssignment
  origin : Origin
  deriving DecidableEq, Repr

def enrollmentStream : StreamCodec Enrollment :=
  StreamCodec.xmap
    (StreamCodec.product StreamCodec.nat
      (StreamCodec.product StreamCodec.nat
        (StreamCodec.product StreamCodec.nat
          (StreamCodec.product intStream
            (StreamCodec.product intStream
              (StreamCodec.product interfaceKindStream
                (StreamCodec.product TypedAuthorizationRequestCodec.subjectIdStream
                  (StreamCodec.product CredentialAuthorityEntryCodec.capabilityIdStream
                    (StreamCodec.product roleAssignmentStream originStream)))))))))
    (fun enrollment => (enrollment.session, enrollment.descriptorResource,
      enrollment.app, enrollment.appGeneration, enrollment.sessionGeneration,
      enrollment.kind, enrollment.subject, enrollment.capability,
      enrollment.role, enrollment.origin))
    (fun (session, descriptorResource, app, appGeneration, sessionGeneration,
          kind, subject, capability, role, origin) =>
      ⟨session, descriptorResource, app, appGeneration, sessionGeneration,
        kind, subject, capability, role, origin⟩)
    (by intro enrollment; cases enrollment; rfl)

private def enrollmentFrame : List UInt8 :=
  "DREGG/APPLICATION/SESSION-ENROLLMENT/v1".toUTF8.toList

private def rawEnrollmentCodec : LawfulCodec Enrollment where
  encode enrollment := enrollmentFrame ++ enrollmentStream.encode enrollment
  decode bytes := if bytes.take enrollmentFrame.length = enrollmentFrame then
    enrollmentStream.toLawful.decode (bytes.drop enrollmentFrame.length) else none
  decode_encode := by
    intro enrollment
    have decoded := enrollmentStream.toLawful.decode_encode enrollment
    change enrollmentStream.toLawful.decode (enrollmentStream.encode enrollment) =
      some enrollment at decoded
    simp [decoded]

def enrollmentCodec : LawfulCodec Enrollment :=
  ResourceBirthCodec.strictCodec rawEnrollmentCodec

theorem enrollment_decode_encode (enrollment : Enrollment) :
    enrollmentCodec.decode (enrollmentCodec.encode enrollment) = some enrollment :=
  enrollmentCodec.decode_encode enrollment

theorem enrollment_bytes_injective : Function.Injective enrollmentCodec.encode := by
  intro left right same
  have decoded := congrArg enrollmentCodec.decode same
  exact Option.some.inj (by simpa only [enrollmentCodec.decode_encode] using decoded)

/-- The native enrollment receiver must check this validity and root
provenance. A role assignment with conflicting names is refused. -/
def RoleAssignment.valid (role : RoleAssignment) : Bool :=
  decide role.added.Nodup && decide role.removed.Nodup &&
    role.added.all (fun name => !(role.removed.contains name)) &&
    decide (role.added.length ≤ 256) && decide (role.removed.length ≤ 256)

def Enrollment.valid (enrollment : Enrollment) : Bool :=
  enrollment.role.valid &&
    decide (enrollment.session != enrollment.descriptorResource) &&
    decide (0 ≤ enrollment.appGeneration) &&
    decide (0 < enrollment.sessionGeneration)

/-- One stable address per session. Re-enrollment edits this atom in place,
using an exact expected old record. The canonical payload still carries the
session generation, so a stale payload cannot represent a renewed session.
This avoids exhausting the four-entry content page after repeated renewals. -/
def enrollmentAtom (domain : Digest) (session : Nat) : AtomId :=
  let preimage := (StreamCodec.product digestStream
    StreamCodec.nat).encode (domain, session)
  ⟨⟨(Sp800185Cshake256.hash
    "DREGG/APPLICATION/SESSION-ENROLLMENT-ATOM/v2".toUTF8.toList preimage).digest.value⟩⟩

/-- Parse the stable atom and require its payload to match the current session
generation. An old payload fails even though its atom address remains stable.
Selecting that page/root and proving the session-policy target binding remain
native read-guard obligations. -/
def decodeInstalled (domain : Digest) (descriptorResource session : Nat)
    (generation : Int) (page : HyperdocumentContentPageMaterializer.Page) : Option Enrollment := do
  if page.contentDomain != domain || page.document != ⟨⟨descriptorResource⟩⟩ then none else
  let record ← Hyperdocument.lookup page.toCanonicalState .atoms
    (enrollmentAtom domain session)
  if record.kind != .inlineObject ⟨14⟩ || record.tombstonedAt.isSome then none else
  let enrollment ← enrollmentCodec.decode record.payload
  if enrollment.session == session &&
     enrollment.descriptorResource == descriptorResource &&
     enrollment.sessionGeneration == generation && enrollment.valid then
    some enrollment
  else none

/-- Even with a stable atom address, decoding it for a current session epoch
requires that exact epoch in the canonical payload. An old payload cannot be
accepted as the current enrollment. -/
theorem installed_generation_exact (domain : Digest) (descriptorResource session : Nat)
    (generation : Int) (page : HyperdocumentContentPageMaterializer.Page)
    (enrollment : Enrollment)
    (accepted : decodeInstalled domain descriptorResource session generation page =
      some enrollment) : enrollment.sessionGeneration = generation := by
  unfold decodeInstalled at accepted
  split at accepted <;> simp_all
  cases hrecord : Hyperdocument.lookup page.toCanonicalState .atoms
      (enrollmentAtom domain session) with
  | none => simp [hrecord] at accepted
  | some record =>
      simp [hrecord] at accepted
      rcases accepted with ⟨_, accepted⟩
      cases hdecode : enrollmentCodec.decode record.payload with
      | none => simp [hdecode] at accepted
      | some decoded =>
          simp [hdecode] at accepted
          aesop

/-- Candidate renewal action for the same physical atom. ContentResource's
ordinary receiver compares `previous` with its current stored record; the
installed descriptor policy also requires a joint session generation step.
Only the special dispatch ingress can subsequently treat the decoded current
payload as an enrollment authority input. -/
def initialAction (domain : Digest) (enrollment : Enrollment) :
    ContentResource.Action :=
  .createAtom (enrollmentAtom domain enrollment.session)
    (.inlineObject ⟨14⟩) (enrollmentCodec.encode enrollment)

def renewalAction (domain : Digest) (previous : AtomRecord)
    (next : Enrollment) : ContentResource.Action :=
  .editAtom { atomId := enrollmentAtom domain next.session, before := previous, kind := .inlineObject ⟨14⟩, payload := enrollmentCodec.encode next, tombstone := false }

/-- Compares the enrolled selectors with the signed dispatch intent. This
is not grant validation or role permission resolution. -/
def Enrollment.matchesSession (enrollment : Enrollment)
    (session : ApplicationDispatchCodec.Session) : Bool :=
  decide (enrollment.session = session.resource) &&
  decide (enrollment.app = session.appResource) &&
  decide (enrollment.appGeneration = session.appGeneration) &&
  decide (enrollment.sessionGeneration = session.generation) &&
  decide (enrollment.kind = session.kind) &&
  decide (enrollment.subject = session.subject) &&
  decide (enrollment.capability = session.capability) &&
  decide (enrollment.origin = session.origin)

theorem stale_generation_cannot_match (enrollment : Enrollment)
    (session : ApplicationDispatchCodec.Session)
    (stale : enrollment.sessionGeneration ≠ session.generation) :
    enrollment.matchesSession session = false := by
  simp [Enrollment.matchesSession, stale]

/-- Exact scalar witness state for the special receiver. A caller-supplied
state is never accepted without a DRC expected-value admission. -/
def Enrollment.activeState (enrollment : Enrollment) :
    ApplicationGrainSession.State :=
  { app := enrollment.app, appGeneration := enrollment.appGeneration,
    generation := enrollment.sessionGeneration, status := .active,
    kind := if enrollment.kind = .web then .web else .api }

end Minidregg.Kernel.ApplicationGrainSessionEnrollment
