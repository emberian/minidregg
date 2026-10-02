/- Source-owned law graph loading. History authenticates records; component refs
and containing-room exports alone create restriction edges. -/
import Compiler.PolicyHistoryResolution

namespace Minidregg.Compiler.PolicyComponentResolution

open Minidregg.Pred
open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.LawComposition
open Minidregg.Compiler.CanonicalPolicyAdmission
open Minidregg.Compiler.CredentialAuthorityPolicyRegistry
open Minidregg.Compiler.PolicyHistoryResolution
open Minidregg.Kernel.CanonicalPolicyRegistry

set_option autoImplicit false

/-- An absent export is neutral but still follows the containing-room chain. -/
def facetComponent (record : PolicyRecord) : Facet → Component
  | .local => record.localComponent
  | .descendants => record.descendants.getD (neutralComponent (.all []))

def selectedExactly (ref : PolicyRef) (head selected : CommittedPolicy) : Prop :=
  match ref.selection with
  | .head => selected = head
  | .pinned revision address =>
      selected.record.version = revision ∧ selected.address = address

instance (ref : PolicyRef) (head selected : CommittedPolicy) :
    Decidable (selectedExactly ref head selected) := by
  unfold selectedExactly
  split <;> infer_instance

structure LoadedReference (snapshot : Snapshot) (store : PayloadStore)
    (semantics : Digest) (ref : PolicyRef) where
  head : LoadedPolicy snapshot store ref.policyId
    (snapshot.authState.policyRevision ref.policyId)
  selected : CommittedPolicy
  history : Historical store head.committed selected
  exact : selectedExactly ref head.committed selected
  semanticsExact : selected.record.semantics = semantics

private def finish {snapshot : Snapshot} {store : PayloadStore}
    (semantics : Digest) (ref : PolicyRef)
    (head : LoadedPolicy snapshot store ref.policyId
      (snapshot.authState.policyRevision ref.policyId))
    (selected : CommittedPolicy) (history : Historical store head.committed selected)
    (exact : selectedExactly ref head.committed selected) :
    Option (LoadedReference snapshot store semantics ref) :=
  if same : selected.record.semantics = semantics then
    some ⟨head, selected, history, exact, same⟩
  else none

def loadReference (snapshot : Snapshot) (store : PayloadStore)
    (semantics : Digest) (ref : PolicyRef) :
    Option (LoadedReference snapshot store semantics ref) := do
  let head ← loadPolicy snapshot store ref.policyId
    (snapshot.authState.policyRevision ref.policyId)
  match selection : ref.selection with
  | .head => finish semantics ref head head.committed .current (by simp [selectedExactly, selection])
  | .pinned revision address =>
      let selected ← loadPinned head revision address
      finish semantics ref head selected.committed selected.history
        (by simpa [selectedExactly, selection] using
          And.intro selected.revisionExact selected.addressExact)

def LoadedReference.key {snapshot : Snapshot} {store : PayloadStore}
    {semantics : Digest} {ref : PolicyRef}
    (loaded : LoadedReference snapshot store semantics ref) : Key :=
  ⟨ref.policyId, ref.facet, loaded.selected.record.version, loaded.selected.address⟩

def LoadedReference.component {snapshot : Snapshot} {store : PayloadStore}
    {semantics : Digest} {ref : PolicyRef}
    (loaded : LoadedReference snapshot store semantics ref) : Component :=
  facetComponent loaded.selected.record ref.facet

/-- Parentage belongs to the same authority snapshot as every policy head.
Only export facets automatically follow this edge; named locals do not. -/
def ambient (snapshot : Snapshot) (cell : Nat) : List PolicyRef :=
  match snapshot.authState.parent cell with
  | none => []
  | some room => [⟨⟨room⟩, .descendants, .head⟩]

def dependencyRequests {snapshot : Snapshot} {store : PayloadStore}
    {semantics : Digest} {ref : PolicyRef}
    (loaded : LoadedReference snapshot store semantics ref) : List (EdgeOrigin × PolicyRef) :=
  loaded.component.parents.map (fun parent => (.explicit, parent)) ++
    match ref.facet with
    | .local => []
    | .descendants => (ambient snapshot ref.policyId.value).map (fun parent => (.exportAncestor, parent))

def loadEdges (snapshot : Snapshot) (store : PayloadStore) (semantics : Digest)
    (requests : List (EdgeOrigin × PolicyRef)) : Option (List Edge) :=
  requests.mapM fun (origin, ref) => do
    let loaded ← loadReference snapshot store semantics ref
    pure ⟨loaded.key, origin⟩

/-- Source and dependencies are checked together. No requester-supplied component
body or edge list is accepted by the executable loader. -/
structure LoadedNode (snapshot : Snapshot) (store : PayloadStore) (semantics : Digest) where
  ref : PolicyRef
  source : LoadedReference snapshot store semantics ref
  edges : List Edge
  edgesExact : loadEdges snapshot store semantics (dependencyRequests source) = some edges

def LoadedNode.node {snapshot : Snapshot} {store : PayloadStore} {semantics : Digest}
    (loaded : LoadedNode snapshot store semantics) : Node :=
  ⟨loaded.source.key, loaded.source.component, loaded.edges⟩

def loadNode (snapshot : Snapshot) (store : PayloadStore) (semantics : Digest)
    (ref : PolicyRef) : Option (LoadedNode snapshot store semantics) := do
  let source ← loadReference snapshot store semantics ref
  match exact : loadEdges snapshot store semantics (dependencyRequests source) with
  | none => none
  | some edges => pure ⟨ref, source, edges, exact⟩

inductive Refusal where
  | unavailable (ref : PolicyRef)
  | cycle (path : List Key)
  | resolutionBudget
  | graph (reason : ResolutionError)
  deriving Repr

/-- The receiving profile owns the budget. Exhaustion refuses and cannot omit
an inherited term. The active stack detects actual resolved-record cycles. -/
private def collect (snapshot : Snapshot) (store : PayloadStore) (semantics : Digest) :
    Nat → List Key → PolicyRef → List (LoadedNode snapshot store semantics) →
      Except Refusal (List (LoadedNode snapshot store semantics))
  | 0, _, _, _ => .error .resolutionBudget
  | fuel + 1, active, ref, complete => do
      let loaded ← match loadNode snapshot store semantics ref with
        | none => .error (.unavailable ref)
        | some loaded => .ok loaded
      let key := loaded.source.key
      if active.contains key then throw (.cycle ((key :: active).reverse))
      if (complete.map (fun item => item.source.key)).contains key then return complete
      let prior ← (dependencyRequests loaded.source).foldlM
        (fun done request => collect snapshot store semantics fuel (key :: active) request.2 done)
        complete
      return prior ++ [loaded]

/-- Actual target roots are local + mandatory containing-room export. This is
not used when resolving an explicit local library reference. -/
def targetRoots (snapshot : Snapshot) (target : Nat) : List PolicyRef :=
  ⟨⟨target⟩, .local, .head⟩ :: ambient snapshot target

structure LoadedGraph (snapshot : Snapshot) (store : PayloadStore)
    (semantics : Digest) (target : Nat) where
  sources : List (LoadedNode snapshot store semantics)
  roots : List Edge
  rootsExact : loadEdges snapshot store semantics
    ((targetRoots snapshot target).map (fun ref => (.targetAmbient, ref))) = some roots
  resolved : ResolvedDAG
    { snapshot := ⟨snapshot.domain, semantics, snapshot.cell.root, snapshot.cell.root⟩
      nodes := sources.map LoadedNode.node
      roots := roots.map Edge.target }

def loadTarget (snapshot : Snapshot) (store : PayloadStore)
    (semantics : Digest) (target budget : Nat) :
    Except Refusal (LoadedGraph snapshot store semantics target) := do
  let refs := targetRoots snapshot target
  let sources ← refs.foldlM (fun done ref => collect snapshot store semantics budget [] ref done) []
  match exact : loadEdges snapshot store semantics (refs.map (fun ref => (.targetAmbient, ref))) with
  | none => throw (.unavailable ⟨⟨target⟩, .local, .head⟩)
  | some roots =>
      let input : GraphInput :=
        { snapshot := ⟨snapshot.domain, semantics, snapshot.cell.root, snapshot.cell.root⟩
          nodes := sources.map LoadedNode.node
          roots := roots.map Edge.target }
      match resolve input with
      | .error reason => throw (.graph reason)
      | .ok resolved => pure ⟨sources, roots, exact, resolved⟩

end Minidregg.Compiler.PolicyComponentResolution
