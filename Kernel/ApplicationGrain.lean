/-
An application's stable identity is an ordinary Mini object, independent of its
process, HTTP connection, and any user's AgentGrain. This four-field declared
record (a declared-effect store) records only lifecycle generation, phase, package version and snapshot
version. Full package and snapshot bytes live in separate canonical content
resources. A version step is admitted only with a content incidence on the
corresponding target in the same ordinary resource transaction.

This module constructs source predicates and candidate actions. Admission still
belongs to the installed policy, current capability, signed ingress and durable
DeclaredResourceController receiver. In particular, it does not grant an HTTP
dispatch permit or assert that an external app, package or snapshot is sound.
-/
import Kernel.DeclaredFields
import Kernel.ResourceTransaction
import Pred.Core

namespace Minidregg.Kernel.ApplicationGrain
open Minidregg.Compiler
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.IndexedProgram
open Minidregg.Theory.EffectDeclaration
open Minidregg.Theory.DeclaredActionLowering
open Minidregg.Compiler.IntStream (intStream)
open Minidregg.Theory.Store (Store)
open Minidregg.Pred
set_option autoImplicit false

/-- Phase 0 is new, 1 install pending, 2 stopped, 3 start pending,
4 serving, 5 stop pending, 6 upgrade pending, 7 retired. Phases 8, 9, 10,
and 11 are one-shot claims of the respective pending install, start, stop,
and upgrade operation. A claim is a durable reservation, not an assertion
that the physical effect occurred; uncertain host execution never licenses
automatic retry. -/
structure State where
  generation : Int
  phase : Int
  packageVersion : Int
  snapshotVersion : Int
  deriving DecidableEq, Repr

def State.values (s : State) : List Int :=
  [s.generation, s.phase, s.packageVersion, s.snapshotVersion]

abbrev key (app field : Nat) : StateKey := DeclaredFields.key app field

/-- The four coordinates in the store's canonical order (fields 1, 2, 3, 0;
see `DeclaredFields`). -/
def State.coordinates (s : State) : DeclaredResourceProjection.Values :=
  [(1,s.phase),(2,s.packageVersion),(3,s.snapshotVersion),(0,s.generation)]

theorem State.coordinates_four (s : State) :
    s.coordinates = DeclaredFields.four s.generation s.phase s.packageVersion s.snapshotVersion := rfl

/-- The application resource as a declared-effect store: exactly its four fields. -/
def State.store (s : State) (app : Nat) : Store effectLayout :=
  DeclaredFields.store app s.coordinates

def initialStore (app : Nat) : Store effectLayout :=
  DeclaredFields.birthStore app (⟨0, 0, 0, 0⟩ : State).coordinates

def readState (app : Nat) (store : Store effectLayout) : Option State := do
  let read := fun n => DeclaredFields.read app n store
  return ⟨← read 0, ← read 1, ← read 2, ← read 3⟩

theorem readState_store (app : Nat) (s : State) : readState app (s.store app) = some s := by
  obtain ⟨r0, r1, r2, r3⟩ :=
    DeclaredFields.read_four app s.generation s.phase s.packageVersion s.snapshotVersion
  simp [readState, State.store, State.coordinates_four, r0, r1, r2, r3]

/-- Expected-value writes compare every coordinate, including unchanged ones. -/
def actions (app : Nat) (before after : State) : List Action :=
  (List.range 4).zipWith (fun n pair =>
    .write (key app n) (some pair.1) pair.2) (before.values.zip after.values)

def slots (before after : State) : List (String × Int) :=
  DeclaredResourceProjection.scalarSlots before.coordinates after.coordinates

/-- The policy view of an application resource is exactly its four coordinates. -/
theorem store_projection_exact (app : Nat) (before after : State) :
    DeclaredResourceProjection.project app (before.store app) (after.store app) =
      slots before after := by
  simp only [State.store, slots, State.coordinates_four]
  exact DeclaredFields.project_four app _ _ _ _ _ _ _ _

private def nonnegative (slot : String) : Pred := .not (.le slot (-1))
private def unchanged (field : Nat) : Pred :=
  .eq (DeclaredResourceProjection.fieldName field "delta") 0
private def increased (field : Nat) : Pred :=
  .eq (DeclaredResourceProjection.fieldName field "delta") 1
def contentChanged (target : Nat) : Pred :=
  .not (.le (s!"joint/target/{target}/content/operations") 0)
private def edge (old new generationDelta : Int) (conditions : List Pred) : Pred :=
  .all ([.eq "resource/field/1/before" old,
    .eq "resource/field/1/after" new,
    .eq "resource/field/0/delta" generationDelta] ++ conditions)

/-- Only a special native receiving path may derive these slots after checking
the pending operation and physical custody evidence. Generic DRC projection
does not expose either name, and absent or zero means refusal. -/
def completionSlot : String := "application/completion/checked"
def reconciliationSlot : String := "application/reconciliation/checked"
def completionGate : Pred := .eq completionSlot 1
def reconciliationGate : Pred := .eq reconciliationSlot 1

/-- Exact original installed lifecycle policy. Keep this source value for
historical admission at an original prefix and authorized policy migration;
its old pending-to-complete edges do not grant a new one-shot launch claim. -/
def transitionPolicyV1 (packageTarget snapshotTarget : Nat) : Pred :=
  if packageTarget = snapshotTarget then .any [] else .all [
    .memberOf "resource/field/0/delta" [0,1],
    .memberOf "resource/field/2/delta" [0,1],
    .memberOf "resource/field/3/delta" [0,1],
    .memberOf "resource/field/1/before" [0,1,2,3,4,5,6],
    .memberOf "resource/field/1/after" [0,1,2,3,4,5,6,7],
    .any [.eq "resource/field/2/delta" 0, contentChanged packageTarget],
    .any [.eq "resource/field/3/delta" 0, contentChanged snapshotTarget],
    nonnegative "resource/field/0/before", nonnegative "resource/field/0/after",
    nonnegative "resource/field/2/before", nonnegative "resource/field/2/after",
    nonnegative "resource/field/3/before", nonnegative "resource/field/3/after",
    .any [
      edge 0 1 1 [unchanged 2, unchanged 3],
      edge 1 2 0 [increased 2, unchanged 3, contentChanged packageTarget,
        completionGate],
      edge 2 3 1 [unchanged 2, unchanged 3],
      edge 3 4 0 [unchanged 2, unchanged 3, completionGate],
      edge 4 5 1 [unchanged 2, unchanged 3],
      edge 5 2 0 [unchanged 2, unchanged 3, completionGate],
      edge 2 6 1 [unchanged 2, unchanged 3],
      edge 6 2 0 [increased 2, unchanged 3, contentChanged packageTarget,
        completionGate],
      edge 2 2 0 [unchanged 2, increased 3, contentChanged snapshotTarget,
        completionGate],
      edge 4 4 0 [unchanged 2, increased 3, contentChanged snapshotTarget,
        completionGate],
      edge 4 4 0 [unchanged 2, unchanged 3],
      edge 3 2 1 [unchanged 2, unchanged 3, reconciliationGate],
      edge 2 7 1 [unchanged 2, unchanged 3]]]

def policyV1 (packageTarget snapshotTarget : Nat)
    (management : Pred := .any []) : Pred := .any [
  .all [.eq "request/verb" 2, transitionPolicyV1 packageTarget snapshotTarget],
  .memberOf "request/verb" [1,3],
  .all [.memberOf "request/verb" [4,5], management]]

/-- Lifecycle changes are independent of any participant's session fence.
Version increments require same-transaction content incidences. Action count
can be a no-op; package identity and physical snapshot custody still require
the checked completion receiver before it supplies the reserved gate. -/
def transitionPolicy (packageTarget snapshotTarget : Nat) : Pred :=
  if packageTarget = snapshotTarget then .any [] else .all [
    .memberOf "resource/field/0/delta" [0,1],
    .memberOf "resource/field/2/delta" [0,1],
    .memberOf "resource/field/3/delta" [0,1],
    .memberOf "resource/field/1/before" [0,1,2,3,4,5,6,8,9,10,11],
    .memberOf "resource/field/1/after" [0,1,2,3,4,5,6,7,8,9,10,11],
    .any [.eq "resource/field/2/delta" 0, contentChanged packageTarget],
    .any [.eq "resource/field/3/delta" 0, contentChanged snapshotTarget],
    nonnegative "resource/field/0/before", nonnegative "resource/field/0/after",
    nonnegative "resource/field/2/before", nonnegative "resource/field/2/after",
    nonnegative "resource/field/3/before", nonnegative "resource/field/3/after",
    .any [
      edge 0 1 1 [unchanged 2, unchanged 3],
      edge 8 2 0 [increased 2, unchanged 3, contentChanged packageTarget,
        completionGate],
      edge 2 3 1 [unchanged 2, unchanged 3],
      edge 9 4 0 [unchanged 2, unchanged 3, completionGate],
      edge 4 5 1 [unchanged 2, unchanged 3],
      edge 10 2 0 [unchanged 2, unchanged 3, completionGate],
      edge 2 6 1 [unchanged 2, unchanged 3],
      edge 11 2 0 [increased 2, unchanged 3, contentChanged packageTarget,
        completionGate],
      edge 2 2 0 [unchanged 2, increased 3, contentChanged snapshotTarget,
        completionGate],
      edge 4 4 0 [unchanged 2, increased 3, contentChanged snapshotTarget,
        completionGate],
      -- A signed current-state witness for a separate checked dispatch path.
      -- Its generic DRC receipt is never itself a delivery permit.
      edge 4 4 0 [unchanged 2, unchanged 3],
      edge 3 2 1 [unchanged 2, unchanged 3, reconciliationGate],
      edge 9 2 1 [unchanged 2, unchanged 3, reconciliationGate],
      edge 2 7 1 [unchanged 2, unchanged 3]]]

/-- The one-shot reservation leg is separate from ordinary lifecycle
transitions. Its caller must also satisfy the installed management predicate;
the native claim receiver additionally requires the original BEGIN mutation
capability, exact historical provenance and current signed observations. -/
def claimTransitionPolicy : Pred := .all [
  .eq "resource/field/0/delta" 0,
  .eq "resource/field/2/delta" 0,
  .eq "resource/field/3/delta" 0,
  .any [edge 1 8 0 [unchanged 2, unchanged 3],
    edge 3 9 0 [unchanged 2, unchanged 3],
    edge 5 10 0 [unchanged 2, unchanged 3],
    edge 6 11 0 [unchanged 2, unchanged 3]]]

/-- Management can be deliberately locked. A separate native capability
check still governs observation and delegation. No generic mutate branch here
authorizes dispatch to an external app. -/
def policy (packageTarget snapshotTarget : Nat)
    (management : Pred := .any []) : Pred := .any [
  .all [.eq "request/verb" 2, transitionPolicy packageTarget snapshotTarget],
  .all [.eq "request/verb" 2, claimTransitionPolicy, management],
  .memberOf "request/verb" [1,3],
  .all [.memberOf "request/verb" [4,5], management]]

/-- Install on the package content target. The content resource's own law
rejects a direct edit without the application version increment in the same
authorized joint command. The application law above provides the converse. -/
def packageManifestPolicy (app : Nat) (management : Pred := .any []) : Pred := .any [
  .all [.eq "request/verb" 2,
    .eq (s!"joint/target/{app}/resource/field/2/delta") 1],
  .memberOf "request/verb" [1,3],
  .all [.memberOf "request/verb" [4,5], management]]

/-- Install on the snapshot content target. Snapshot capture and physical
retention must still be checked by the native receiver before authoring. -/
def snapshotManifestPolicy (app : Nat) (management : Pred := .any []) : Pred := .any [
  .all [.eq "request/verb" 2,
    .eq (s!"joint/target/{app}/resource/field/3/delta") 1],
  .memberOf "request/verb" [1,3],
  .all [.memberOf "request/verb" [4,5], management]]

/-- Explicit lifecycle delegation preserves the owner's administrative law.
The manager still needs a currently valid delegated object capability; this
predicate grants no capability and changes no application identity. -/
def managedPolicy (packageTarget snapshotTarget owner manager : Nat) : Pred := .any [
  .all [.eq "request/verb" 2, transitionPolicy packageTarget snapshotTarget],
  .all [.eq "request/verb" 2, claimTransitionPolicy,
    .eq "request/subject" (Int.ofNat manager)],
  .memberOf "request/verb" [1,3],
  .all [.memberOf "request/verb" [4,5],
    .eq "request/subject" (Int.ofNat owner)]]

def managedPackagePolicy (app owner manager : Nat) : Pred := .any [
  .all [.eq "request/verb" 2,
    .eq (s!"joint/target/{app}/resource/field/2/delta") 1,
    .eq "request/subject" (Int.ofNat manager)],
  .memberOf "request/verb" [1,3],
  .all [.memberOf "request/verb" [4,5],
    .eq "request/subject" (Int.ofNat owner)]]

def managedSnapshotPolicy (app owner manager : Nat) : Pred := .any [
  .all [.eq "request/verb" 2,
    .eq (s!"joint/target/{app}/resource/field/3/delta") 1,
    .eq "request/subject" (Int.ofNat manager)],
  .memberOf "request/verb" [1,3],
  .all [.memberOf "request/verb" [4,5],
    .eq "request/subject" (Int.ofNat owner)]]

private def managementOwnerCandidate (installed : Option Pred) : Option Nat :=
  match installed with
  | some (.anyL branches) =>
      match branches.toList with
      | [_, _, _, .allL admin] =>
          match admin.toList with
          | [_, .eq slot owner] =>
              if slot = "request/subject" ∧ 0 ≤ owner then some owner.toNat else none
          | _ => none
      | _ => none
  | _ => none

/-- Recover the owner only from the exact authenticated installed app law.
A caller's managementSubject names the manager, never supplies an owner hint. -/
def managedPolicyOwner (packageTarget snapshotTarget manager : Nat)
    (installed : Option Pred) : Option Nat := do
  let owner ← managementOwnerCandidate installed
  if installed = some (managedPolicy packageTarget snapshotTarget owner manager)
    then some owner else none

theorem managedPolicyOwner_exact (packageTarget snapshotTarget manager owner : Nat)
    (installed : Option Pred)
    (selected : managedPolicyOwner packageTarget snapshotTarget manager installed = some owner) :
    installed = some (managedPolicy packageTarget snapshotTarget owner manager) := by
  unfold managedPolicyOwner at selected
  cases found : managementOwnerCandidate installed with
  | none => simp [found] at selected
  | some candidate =>
      simp only [found] at selected
      change (if installed = some (managedPolicy packageTarget snapshotTarget candidate manager)
        then some candidate else none) = some owner at selected
      split at selected <;> simp_all

/-- App and package must name the same owner and manager in their exact
current source laws. Snapshot operations must check the analogous law when
they actually observe or govern that resource; BEGIN/claim/completion below
do not modify snapshotVersion or read the snapshot resource. -/
def managedPoliciesMatch (app packageTarget snapshotTarget manager : Nat)
    (appPolicy packagePolicy : Option Pred) : Bool :=
  match managedPolicyOwner packageTarget snapshotTarget manager appPolicy with
  | none => false
  | some owner => packagePolicy == some (managedPackagePolicy app owner manager)

theorem managedPoliciesMatch_exact (app packageTarget snapshotTarget manager : Nat)
    (appPolicy packagePolicy : Option Pred)
    (accepted : managedPoliciesMatch app packageTarget snapshotTarget manager
      appPolicy packagePolicy = true) :
    ∃ owner, appPolicy = some (managedPolicy packageTarget snapshotTarget owner manager) ∧
      packagePolicy = some (managedPackagePolicy app owner manager) := by
  unfold managedPoliciesMatch at accepted
  cases selected : managedPolicyOwner packageTarget snapshotTarget manager appPolicy with
  | none => simp [selected] at accepted
  | some owner =>
      refine ⟨owner, managedPolicyOwner_exact _ _ _ _ _ selected, ?_⟩
      simpa [selected] using accepted

private def managementManagerCandidate (installed : Option Pred) : Option Nat :=
  match installed with
  | some (.anyL branches) =>
      match branches.toList with
      | [_, .allL claim, _, _] =>
          match claim.toList with
          | [_, _, .eq slot manager] =>
              if slot = "request/subject" ∧ 0 ≤ manager then some manager.toNat else none
          | _ => none
      | _ => none
  | _ => none

/-- Dispatch retains the member owner as share issuer. Its manager is derived
from the exact current app law, never from a ticket or caller-supplied hint. -/
def managedPolicyManager (packageTarget snapshotTarget owner : Nat)
    (installed : Option Pred) : Option Nat := do
  let manager ← managementManagerCandidate installed
  if installed = some (managedPolicy packageTarget snapshotTarget owner manager)
    then some manager else none

theorem managedPolicyManager_exact (packageTarget snapshotTarget owner manager : Nat)
    (installed : Option Pred)
    (selected : managedPolicyManager packageTarget snapshotTarget owner installed = some manager) :
    installed = some (managedPolicy packageTarget snapshotTarget owner manager) := by
  unfold managedPolicyManager at selected
  cases found : managementManagerCandidate installed with
  | none => simp [found] at selected
  | some candidate =>
      simp only [found] at selected
      change (if installed = some (managedPolicy packageTarget snapshotTarget owner candidate)
        then some candidate else none) = some manager at selected
      split at selected <;> simp_all

def managedPoliciesMatchOwner (app packageTarget snapshotTarget owner : Nat)
    (appPolicy packagePolicy : Option Pred) : Bool :=
  match managedPolicyManager packageTarget snapshotTarget owner appPolicy with
  | none => false
  | some manager => packagePolicy == some (managedPackagePolicy app owner manager)

theorem managedPoliciesMatchOwner_exact (app packageTarget snapshotTarget owner : Nat)
    (appPolicy packagePolicy : Option Pred)
    (accepted : managedPoliciesMatchOwner app packageTarget snapshotTarget owner
      appPolicy packagePolicy = true) :
    ∃ manager, appPolicy = some (managedPolicy packageTarget snapshotTarget owner manager) ∧
      packagePolicy = some (managedPackagePolicy app owner manager) := by
  unfold managedPoliciesMatchOwner at accepted
  cases selected : managedPolicyManager packageTarget snapshotTarget owner appPolicy with
  | none => simp [selected] at accepted
  | some manager =>
      refine ⟨manager, managedPolicyManager_exact _ _ _ _ _ selected, ?_⟩
      simpa [selected] using accepted

inductive Operation where
  | beginInstall
  | completeInstall
  | beginStart
  | completeStart
  | beginStop
  | completeStop
  | beginUpgrade
  | claimInstall
  | claimStart
  | claimStop
  | claimUpgrade
  | completeUpgrade
  | checkpoint
  | servingWitness
  | reconcileFailedStart
  | retire
  deriving DecidableEq, Repr

/-- Candidate authoring only. The installed predicate checks the old and new
pages, and the generic receiver checks the current signed authority. -/
def Operation.after (operation : Operation) (s : State) : State :=
  match operation with
  | .beginInstall => { s with generation := s.generation + 1, phase := 1 }
  | .completeInstall => { s with phase := 2, packageVersion := s.packageVersion + 1 }
  | .beginStart => { s with generation := s.generation + 1, phase := 3 }
  | .completeStart => { s with phase := 4 }
  | .beginStop => { s with generation := s.generation + 1, phase := 5 }
  | .completeStop => { s with phase := 2 }
  | .beginUpgrade => { s with generation := s.generation + 1, phase := 6 }
  | .claimInstall => { s with phase := 8 }
  | .claimStart => { s with phase := 9 }
  | .claimStop => { s with phase := 10 }
  | .claimUpgrade => { s with phase := 11 }
  | .completeUpgrade => { s with phase := 2, packageVersion := s.packageVersion + 1 }
  | .checkpoint => { s with snapshotVersion := s.snapshotVersion + 1 }
  | .servingWitness => s
  | .reconcileFailedStart => { s with generation := s.generation + 1, phase := 2 }
  | .retire => { s with generation := s.generation + 1, phase := 7 }

def Operation.target (operation : Operation) (app : Nat) (capability : CapabilityId)
    (expectedRoot : Digest) (before : State)
    (observeCapability : Option CapabilityId := none) :
    DeclaredResourceController.Target :=
  { kind := .object, target := app, capability := capability,
    observeCapability := observeCapability, schemaVersion := 1,
    expectedTargetRoot := expectedRoot,
    payload := .scalar (actions app before (operation.after before)) }

/-- The caller must put the matching package or snapshot content incidence in
`contentTargets`; the installed law above refuses a version advance without it.
This command still needs ordinary DRC admission and does not prove physical
package install, process stop, or snapshot capture. -/
def Operation.command (operation : Operation) (subject : SubjectId)
    (nonce app : Nat) (capability : CapabilityId)
    (expectedRoot : Digest) (before : State)
    (contentTargets : List DeclaredResourceController.Target := [])
    (observeCapability : Option CapabilityId := none) :
    DeclaredResourceController.Command :=
  { subject := subject, nonce := nonce,
    targets := operation.target app capability expectedRoot before observeCapability :: contentTargets }

/-- Legacy incomplete request identity retained temporarily for compatibility.
It omits query, headers, cookies, generated WebSession identity, and exact body
bytes. `ApplicationDispatchCodec` supersedes it for any checked ingress. Its
generic DRC nonce or receipt is never an external delivery permit. -/
structure DispatchIntent where
  app : Nat
  appGeneration : Int
  sessionTask : Nat
  sessionGeneration : Int
  subject : SubjectId
  interfaceId : Nat
  method : List UInt8
  path : List UInt8
  bodyDigest : Digest
  bodyLength : Nat
  operationId : Nat
  deriving DecidableEq, Repr

private def headerStream :=
  StreamCodec.product StreamCodec.nat
    (StreamCodec.product intStream
      (StreamCodec.product StreamCodec.nat
        (StreamCodec.product intStream TypedAuthorizationRequestCodec.subjectIdStream)))

private def requestStream :=
  StreamCodec.product StreamCodec.nat
    (StreamCodec.product bytesStream
      (StreamCodec.product bytesStream
        (StreamCodec.product digestStream
          (StreamCodec.product StreamCodec.nat StreamCodec.nat))))

def dispatchStream : StreamCodec DispatchIntent :=
  StreamCodec.xmap (StreamCodec.product headerStream requestStream)
    (fun intent =>
      ((intent.app, intent.appGeneration, intent.sessionTask,
          intent.sessionGeneration, intent.subject),
       (intent.interfaceId, intent.method, intent.path, intent.bodyDigest,
          intent.bodyLength, intent.operationId)))
    (fun pair =>
      ⟨pair.1.1, pair.1.2.1, pair.1.2.2.1, pair.1.2.2.2.1,
       pair.1.2.2.2.2, pair.2.1, pair.2.2.1, pair.2.2.2.1,
       pair.2.2.2.2.1, pair.2.2.2.2.2.1, pair.2.2.2.2.2.2⟩)
    (by intro intent; cases intent; rfl)

private def dispatchFrame : List UInt8 :=
  "DREGG/APPLICATION/DISPATCH/v1".toUTF8.toList

private def rawDispatchCodec : LawfulCodec DispatchIntent where
  encode intent := dispatchFrame ++ dispatchStream.encode intent
  decode bytes := if bytes.take dispatchFrame.length = dispatchFrame then
    dispatchStream.toLawful.decode (bytes.drop dispatchFrame.length) else none
  decode_encode := by
    intro intent
    have decoded := dispatchStream.toLawful.decode_encode intent
    change dispatchStream.toLawful.decode (dispatchStream.encode intent) = some intent at decoded
    simp [decoded]

def dispatchCodec : LawfulCodec DispatchIntent :=
  ResourceBirthCodec.strictCodec rawDispatchCodec

def DispatchIntent.canonicalBytes (intent : DispatchIntent) : List UInt8 :=
  dispatchCodec.encode intent

theorem dispatch_decode_encode (intent : DispatchIntent) :
    dispatchCodec.decode intent.canonicalBytes = some intent := dispatchCodec.decode_encode intent

end Minidregg.Kernel.ApplicationGrain
