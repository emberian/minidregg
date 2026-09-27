/-
An application session is a revocable Mini object, distinct from the shared
application lifecycle and from a transport connection. The consensus declared
page has four entries. Its final entry is a checked finite encoding of the
logical status and Web/API kind; there is no arithmetic alias for invalid tags.

The subject, capability provenance, role assignment and human/agent origin live
in a separately governed enrollment descriptor. The scalar law alone is not a
HTTP delivery permit. A special receiver must read that descriptor, current
app manifest and grants, and recompute effective permissions on each admission.
-/
import Kernel.DeclaredResourceProjection
import Kernel.ResourceTransaction
import Pred.Core

namespace Minidregg.Kernel.ApplicationGrainSession
open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.EffectDeclaration
open Minidregg.Theory.DeclaredActionLowering
open Minidregg.Compiler.DeclaredEffectPageMaterializer
open Minidregg.Pred
set_option autoImplicit false

inductive Kind where
  | web | api
  deriving DecidableEq, Repr

inductive Status where
  | inactive | active | closed | revoked
  deriving DecidableEq, Repr

/-- The complete eight-element logical status/kind product. -/
def tag : Kind → Status → Int
  | .web, .inactive => 0
  | .web, .active => 1
  | .web, .closed => 2
  | .web, .revoked => 3
  | .api, .inactive => 4
  | .api, .active => 5
  | .api, .closed => 6
  | .api, .revoked => 7

def decodeTag : Int → Option (Kind × Status)
  | 0 => some (.web, .inactive)
  | 1 => some (.web, .active)
  | 2 => some (.web, .closed)
  | 3 => some (.web, .revoked)
  | 4 => some (.api, .inactive)
  | 5 => some (.api, .active)
  | 6 => some (.api, .closed)
  | 7 => some (.api, .revoked)
  | _ => none

theorem decodeTag_tag (kind : Kind) (status : Status) :
    decodeTag (tag kind status) = some (kind, status) := by
  cases kind <;> cases status <;> rfl

theorem tag_injective : Function.Injective (fun p : Kind × Status => tag p.1 p.2) := by
  intro left right same
  have := congrArg decodeTag same
  simpa [decodeTag_tag] using this

structure State where
  app : Int
  appGeneration : Int
  generation : Int
  status : Status
  kind : Kind
  deriving DecidableEq, Repr

def State.values (s : State) : List Int :=
  [s.app, s.appGeneration, s.generation, tag s.kind s.status]

def key (session field : Nat) : StateKey := .objectField ⟨session⟩ ⟨field⟩

def State.page (s : State) (domain : Digest) (session : Nat) : Page :=
  ⟨domain, session % shardCount,
    some ⟨key session 0, s.app⟩, some ⟨key session 1, s.appGeneration⟩,
    some ⟨key session 2, s.generation⟩,
    some ⟨key session 3, tag s.kind s.status⟩⟩

def initialPage (domain : Digest) (session app : Nat) (kind : Kind) : Page :=
  (⟨app, 0, 0, .inactive, kind⟩ : State).page domain session

def readState (session : Nat) (page : Page) : Option State := do
  let read := fun n => (page.entries.find? (fun e => e.key == key session n)).map (·.value)
  let app ← read 0
  let appGeneration ← read 1
  let generation ← read 2
  let (kind, status) ← decodeTag (← read 3)
  return ⟨app, appGeneration, generation, status, kind⟩

def actions (session : Nat) (before after : State) : List Action :=
  (List.range 4).zipWith (fun n pair =>
    .write (key session n) (some pair.1) pair.2) (before.values.zip after.values)

def State.coordinates (s : State) : DeclaredResourceProjection.Values :=
  [(0,s.app),(1,s.appGeneration),(2,s.generation),(3,tag s.kind s.status)]

def slots (before after : State) : List (String × Int) :=
  DeclaredResourceProjection.scalarSlots before.coordinates after.coordinates

theorem page_projection_exact (domain : Digest) (session : Nat) (before after : State) :
    DeclaredResourceProjection.project session (before.page domain session)
      (after.page domain session) = slots before after := by
  simp [DeclaredResourceProjection.project, DeclaredResourceProjection.values,
    Page.entries, State.page, key, slots, State.coordinates]

private def unchanged (field : Nat) : Pred :=
  .eq (DeclaredResourceProjection.fieldName field "delta") 0
private def edge (old new : Int) (appGenerationDelta : Pred) (extra : List Pred) : Pred :=
  .all ([.eq "resource/field/3/before" old,
    .eq "resource/field/3/after" new,
    .eq "resource/field/2/delta" 1,
    appGenerationDelta] ++ extra)

/-- Actual content operation incidence, not a claim of a canonical descriptor
or changed bytes. The special receiver must validate the current descriptor. -/
def descriptorIncidence (target : Nat) : Pred :=
  .not (.le (s!"joint/target/{target}/content/operations") 0)

/-- A session can only be enrolled or rebound with a joint descriptor edit.
Close/revoke fence its own generation; the shared app is untouched. An active
self-edge is an exact current-state witness for a separate checked dispatch.
The app-generation value chosen on enrollment is not trusted until the special
receiver checks a current joint application read and descriptor. -/
def transitionPolicy (descriptorTarget : Nat) (kind : Kind) : Pred := .all [
  .eq "resource/field/0/delta" 0,
  .memberOf "resource/field/2/delta" [0,1],
  .memberOf "resource/field/3/before" (if kind = .web then [0,1,2,3] else [4,5,6,7]),
  .memberOf "resource/field/3/after" (if kind = .web then [0,1,2,3] else [4,5,6,7]),
  .not (.le "resource/field/1/after" (-1)),
  .not (.le "resource/field/2/before" (-1)),
  .not (.le "resource/field/2/after" (-1)),
  .any [
    edge (tag kind .inactive) (tag kind .active) (.not (.le "resource/field/1/delta" (-1)))
      [descriptorIncidence descriptorTarget],
    edge (tag kind .closed) (tag kind .active) (.not (.le "resource/field/1/delta" (-1)))
      [descriptorIncidence descriptorTarget],
    edge (tag kind .active) (tag kind .closed) (unchanged 1) [],
    edge (tag kind .active) (tag kind .revoked) (unchanged 1) [],
    .all [.eq "resource/field/3/before" (tag kind .active),
      .eq "resource/field/3/after" (tag kind .active),
      unchanged 0, unchanged 1, unchanged 2, unchanged 3]]]

/-- The participant is the installed policy subject, whether the capability
was delegated or rooted. There is no owner shortcut. Native current-grant and
signature checks still apply to every verb. -/
def policy (descriptorTarget : Nat) (kind : Kind) (participant : SubjectId)
    (management : Pred := .any []) : Pred := .any [
  .all [.eq "request/verb" 2, .eq "request/subject" participant.value,
    transitionPolicy descriptorTarget kind],
  .memberOf "request/verb" [1,3],
  .all [.memberOf "request/verb" [4,5], management]]

/-- A standalone descriptor edit is refused. The joint session must advance
its generation into the active tag. A special receiver then validates the
canonical enrollment payload and current grant before HTTP delivery. -/
def descriptorPolicy (session : Nat) (kind : Kind) (participant : SubjectId)
    (management : Pred := .any []) : Pred := .any [
  .all [.eq "request/verb" 2, .eq "request/subject" participant.value,
    .eq (s!"joint/target/{session}/resource/field/2/delta") 1,
    .eq (s!"joint/target/{session}/resource/field/3/after") (tag kind .active)],
  .memberOf "request/verb" [1,3],
  .all [.memberOf "request/verb" [4,5], management]]

inductive Operation where
  | enroll (appGeneration : Int)
  | close
  | revoke
  | activeWitness
  deriving DecidableEq, Repr

def Operation.after (operation : Operation) (s : State) : State :=
  match operation with
  | .enroll nextAppGeneration => { s with appGeneration := nextAppGeneration, generation := s.generation + 1, status := .active }
  | .close => { s with generation := s.generation + 1, status := .closed }
  | .revoke => { s with generation := s.generation + 1, status := .revoked }
  | .activeWitness => s

def Operation.target (operation : Operation) (session : Nat)
    (capability : CapabilityId) (expectedRoot : Digest) (before : State)
    (observeCapability : Option CapabilityId := none) :
    DeclaredResourceController.Target :=
  { kind := .object, target := session, capability := capability,
    observeCapability := observeCapability, schemaVersion := 1,
    expectedTargetRoot := expectedRoot,
    payload := .scalar (actions session before (operation.after before)) }

/-- The descriptor target must participate in an enrollment command. This
constructor is authoring only and never confers a physical dispatch permit. -/
def Operation.command (operation : Operation) (subject : SubjectId)
    (authorityRoot : Digest) (nonce session : Nat) (capability : CapabilityId)
    (expectedRoot : Digest) (before : State)
    (descriptorTargets : List DeclaredResourceController.Target := [])
    (observeCapability : Option CapabilityId := none) :
    DeclaredResourceController.Command :=
  { subject := subject, expectedAuthorityRoot := authorityRoot, nonce := nonce,
    targets := operation.target session capability expectedRoot before observeCapability :: descriptorTargets }

end Minidregg.Kernel.ApplicationGrainSession
