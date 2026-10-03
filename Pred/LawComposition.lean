/-
# Pred.LawComposition -- reusable restrictions over a resolved dependency DAG

The candidate predicate restriction engine shared by admission.
The declaration namespace is retained for source compatibility; this module
lives in Pred because it uses the candidate predicate AST. The receiving source must
construct GraphInput from one authenticated snapshot, checking every source
address, reference resolution and selector projection. This module does not
turn a supplied graph into policy authority. In particular, PolicyRecord's
source address is not the effective conjunction's identity.

There is no C3 or method-order rule. Identical resolved keys are evaluated once;
different authenticated revisions are distinct conjuncts. A predecessor-chain
edge used to authenticate old bytes is not a semantic dependency edge.
-/
import Pred.Core
import Theory.TypedAuthorization

namespace Minidregg.Theory.LawComposition

open Minidregg.Pred
open Minidregg.Theory.TypedAuthorization

set_option autoImplicit false

/-- CanonicalRuntimeProfile binds this receiving contract separately from source
encoding. Increment when graph resolution or mandatory source projections change. -/
def receivingContract : List UInt8 :=
  "DREGG.LAW.COMPOSITION/v1:authenticated-record-dag;key=policy,facet,revision,source-digest;distinct-revisions-conjoin;duplicate-keys-once;cycles-missing-authenticity-refuse;local-explicit-parents;target-ambient-room-exports;export-containing-room-chain;source-owned-kind-exports;selectors=physical-kind,request-kind,verb;all-guards-same-snapshot;old-law-before-candidate-validation;no-candidate-satisfiability;hidden-origin-diagnostics".toUTF8.toList

def closureCustomization : List UInt8 :=
  "DREGG.POLICY.EFFECTIVE.CLOSURE/v1".toUTF8.toList

/-- Birth exports see unchanged factory request slots plus exact source-owned
newborn coordinates and initial effects. The newborn local law is installed,
validated as a graph, and deliberately not evaluated against its own birth. -/
def birthProjectionContract : List UInt8 :=
  "DREGG.LAW.BIRTH-EXPORT-PROJECTION/v1".toUTF8.toList

inductive Facet where
  | local
  | descendants
  deriving DecidableEq, Repr

def Facet.tag : Facet → Nat
  | .local => 0
  | .descendants => 1

inductive Selection where
  | head
  | pinned (revision : PolicyRevision) (sourceDigest : Digest)
  deriving DecidableEq, Repr

structure PolicyRef where
  policyId : PolicyId
  facet : Facet
  selection : Selection
  deriving DecidableEq, Repr

/-- Physical tags are receiving-profile data, not inferred from a resource's
fields. `none` selects every value; `some []` selects none. -/
structure Selector where
  physicalKinds : Option (List Nat) := none
  requestKinds : Option (List Nat) := none
  verbs : Option (List Nat) := none
  deriving DecidableEq, Repr

private def selected (slot : String) : Option (List Nat) → Pred
  | none => Pred.all []
  | some tags => .memberOf slot (tags.map Int.ofNat)

/-- All three slots must be source-owned, unshadowable projection coordinates.
The physical target-kind slot is an integration obligation, not yet deployed. -/
def Selector.predicate (selector : Selector) : Pred :=
  Pred.all [selected "target/storageKind" selector.physicalKinds,
    selected "request/kind" selector.requestKinds,
    selected "request/verb" selector.verbs]

structure Component where
  selector : Selector
  predicate : Pred
  parents : List PolicyRef
  deriving DecidableEq, Repr

/-- Selection is a guard; it cannot override another inherited restriction. -/
def Component.guarded (component : Component) : Pred :=
  Pred.any [.not component.selector.predicate, component.predicate]

/-- The one legacy-law lift used by source migration and checked carry. -/
def neutralComponent (predicate : Pred) : Component :=
  { selector := {}, predicate := predicate, parents := [] }

theorem neutral_component_eval (predicate : Pred) (old new : State) :
    eval (neutralComponent predicate).guarded old new = eval predicate old new := by
  simp [neutralComponent, Component.guarded, Selector.predicate, selected,
    eval_any, eval_all, eval_not]

structure Key where
  policyId : PolicyId
  facet : Facet
  revision : PolicyRevision
  sourceDigest : Digest
  deriving DecidableEq, Repr

/-- Presentation ordering only; it is not an override or admission precedence. -/
def Key.before (left right : Key) : Bool :=
  if left.policyId.value != right.policyId.value then left.policyId.value < right.policyId.value
  else if left.facet.tag != right.facet.tag then left.facet.tag < right.facet.tag
  else if left.revision != right.revision then left.revision < right.revision
  else left.sourceDigest.value < right.sourceDigest.value

inductive EdgeOrigin where
  | explicit
  | targetAmbient
  | exportAncestor
  deriving DecidableEq, Repr

structure Edge where
  target : Key
  origin : EdgeOrigin
  deriving DecidableEq, Repr

/-- The component body and its dependency list have already been resolved by
receiving source. An authenticity witness must later join them to source bytes:
`parents` may not be silently omitted or supplemented by requester data. -/
structure Node where
  key : Key
  component : Component
  dependencies : List Edge
  deriving DecidableEq, Repr

structure SnapshotIdentity where
  domain : Digest
  semantics : Digest
  authorityRoot : Digest
  parentageRoot : Digest
  deriving DecidableEq, Repr

/-- Input to the pure graph pass, not a replacement for LoadedPolicy. The
receiving adapter must retain authentication and physical dependency guards. -/
structure GraphInput where
  snapshot : SnapshotIdentity
  nodes : List Node
  roots : List Key
  deriving DecidableEq, Repr

inductive ResolutionError where
  | duplicateSourceKey
  | unavailable (key : Key)
  | cycle (path : List Key)
  | traversalBound
  | closureInvariant
  deriving DecidableEq, Repr

private def findNode (nodes : List Node) (key : Key) : Option Node :=
  nodes.find? (fun node => node.key == key)

/-- DFS with a path-local cycle check and a completed-node memo. The finite
input supplies a path-length bound; exhaustion refuses, never drops parents.
Postorder lets the output checker exhibit a decreasing dependency rank. -/
private def visit (input : GraphInput) :
    Nat → List Key → Key → List Node → Except ResolutionError (List Node)
  | 0, _, _, _ => .error .traversalBound
  | fuel + 1, active, key, complete => do
      if active.contains key then
        throw (.cycle ((key :: active).reverse))
      if (complete.map Node.key).contains key then
        return complete
      let node ← match findNode input.nodes key with
        | none => .error (.unavailable key)
        | some node => .ok node
      let prior ← node.dependencies.foldlM
        (fun done edge => visit input fuel (key :: active) edge.target done) complete
      return prior ++ [node]

/-- A directly checked rank witness for the DAG, plus exact finite source and
root coverage. Edge coverage is explicit; an absent dependency cannot pass by
using idxOf's out-of-range result. -/
def checkClosure (input : GraphInput) (nodes : List Node) : Bool :=
  let keys := nodes.map Node.key
  decide keys.Nodup &&
    input.roots.all keys.contains &&
    nodes.all (fun node => input.nodes.contains node &&
      node.dependencies.all (fun edge =>
        keys.contains edge.target && keys.idxOf edge.target < keys.idxOf node.key))

structure ResolvedDAG (input : GraphInput) where
  postorder : List Node
  checked : checkClosure input postorder = true

/-- The checked result is still only graph evidence. Admission must also retain
source authentication, same-snapshot selection, and read-guard exactness. -/
def resolve (input : GraphInput) : Except ResolutionError (ResolvedDAG input) := do
  if !(decide (input.nodes.map Node.key).Nodup) then
    throw .duplicateSourceKey
  let nodes ← input.roots.foldlM
    (fun done key => visit input (input.nodes.length + 1) [] key done) []
  if checked : checkClosure input nodes = true then
    return ⟨nodes, checked⟩
  else
    throw .closureInvariant

private def insertCanonical (node : Node) : List Node → List Node
  | [] => [node]
  | first :: rest =>
      if node.key.before first.key then node :: first :: rest
      else first :: insertCanonical node rest

/-- Stable identity order for diagnostics/encoding; semantic proofs below do
not depend on this order. The synthetic target root is external to this list. -/
def canonicalOrder (nodes : List Node) : List Node :=
  nodes.foldl (fun sorted node => insertCanonical node sorted) []

/-- Exactly the Pred accepted by the existing canonical lowering backend. No
second evaluator, opaque function, or new predicate atom is introduced here. -/
def effective (nodes : List Node) : Pred :=
  Pred.all (nodes.map (fun node => node.component.guarded))

theorem effective_eval (nodes : List Node) (old new : State) :
    eval (effective nodes) old new =
      nodes.all (fun node => eval node.component.guarded old new) := by
  simp [effective, eval_all, List.all_map, Function.comp_def]

/-- A legacy target with no explicit parents or ambient exports keeps exactly
its original predicate verdict. The carry supplies the authenticated new key. -/
theorem neutral_effective_eval (key : Key) (predicate : Pred) (old new : State) :
    eval (effective [⟨key, neutralComponent predicate, []⟩]) old new =
      eval predicate old new := by
  simp [effective_eval, neutral_component_eval]

theorem effective_eval_iff (nodes : List Node) (old new : State) :
    eval (effective nodes) old new = true ↔
      ∀ node ∈ nodes, eval node.component.guarded old new = true := by
  rw [effective_eval]
  simp only [List.all_eq_true]

/-- Restriction inheritance is at one exact step and resolved snapshot. It
makes no temporal claim about an author's later law changes. -/
theorem inherited_never_widens (nodes : List Node) (old new : State)
    (accepted : eval (effective nodes) old new = true)
    (node : Node) (member : node ∈ nodes) :
    eval node.component.guarded old new = true :=
  (effective_eval_iff nodes old new).mp accepted node member

theorem effective_permutation (left right : List Node) (order : left.Perm right)
    (old new : State) :
    eval (effective left) old new = true ↔ eval (effective right) old new = true := by
  rw [effective_eval_iff, effective_eval_iff]
  constructor
  · intro accepts node member
    exact accepts node (order.mem_iff.mpr member)
  · intro accepts node member
    exact accepts node (order.mem_iff.mp member)

theorem effective_duplicate (node : Node) (rest : List Node) (old new : State) :
    eval (effective (node :: node :: rest)) old new =
      eval (effective (node :: rest)) old new := by
  simp only [effective_eval, List.all_cons]
  cases eval node.component.guarded old new <;> rfl

/-- Distinct revisions are distinct graph identities, not competing candidates
for one winner. Both may occur in the effective conjunction. -/
theorem revision_keys_distinct (left right : Key) (different : left.revision ≠ right.revision) :
    left ≠ right := by
  intro equal
  exact different (congrArg Key.revision equal)

/-! Pure executable poles. These exercise resolved graph composition only;
they do not stand in for the authenticated source loader or native receiver. -/
namespace Examples

def key (policy revision : Nat) : Key :=
  ⟨⟨policy⟩, .local, revision, ⟨100 * policy + revision⟩⟩

def node (id : Key) (predicate : Pred) (parents : List Key) : Node :=
  { key := id
    component :=
      { selector := {}
        predicate := predicate
        parents := parents.map (fun parent =>
          ⟨parent.policyId, parent.facet, .pinned parent.revision parent.sourceDigest⟩) }
    dependencies := parents.map (fun parent => ⟨parent, .explicit⟩) }

def input (nodes : List Node) (roots : List Key) : GraphInput :=
  ⟨⟨⟨1⟩, ⟨2⟩, ⟨3⟩, ⟨4⟩⟩, nodes, roots⟩

def count (graph : GraphInput) : Option Nat :=
  match resolve graph with
  | .error _ => none
  | .ok result => some result.postorder.length

def failure (graph : GraphInput) : Option ResolutionError :=
  match resolve graph with
  | .error reason => some reason
  | .ok _ => none

def atValue (graph : GraphInput) (value : Int) : Option Bool :=
  match resolve graph with
  | .error _ => none
  | .ok result =>
      let state : State := ⟨[("value", value)]⟩
      some (eval (effective (canonicalOrder result.postorder)) state state)

def nonnegative : Pred := .not (.le "value" (-1))
def atMostTen : Pred := .le "value" 10

def oppositeOrders : GraphInput :=
  input [node (key 10 1) nonnegative [], node (key 20 1) atMostTen [],
    node (key 30 1) (Pred.all []) [key 10 1, key 20 1],
    node (key 40 1) (Pred.all []) [key 20 1, key 10 1],
    node (key 50 1) (Pred.all []) [key 30 1, key 40 1]] [key 50 1]

/-- The useful intersection that C3's opposite precedence constraints reject. -/
theorem opposite_orders_are_composable :
    count oppositeOrders = some 5 ∧
    atValue oppositeOrders 0 = some true ∧
    atValue oppositeOrders 10 = some true ∧
    atValue oppositeOrders (-1) = some false ∧
    atValue oppositeOrders 11 = some false := by decide

def previousRevision : GraphInput :=
  input [node (key 7 1) nonnegative [],
    node (key 7 2) atMostTen [key 7 1]] [key 7 2]

theorem distinct_revisions_both_restrict :
    count previousRevision = some 2 ∧
    atValue previousRevision 5 = some true ∧
    atValue previousRevision (-1) = some false ∧
    atValue previousRevision 11 = some false := by decide

def selfHead : GraphInput :=
  let root := node (key 7 2) (Pred.all []) [key 7 2]
  let root := { root with component := { root.component with
    parents := [⟨⟨7⟩, .local, .head⟩] } }
  input [root] [key 7 2]

theorem resolved_self_head_refuses :
    failure selfHead = some (.cycle [key 7 2, key 7 2]) := by decide

def longerCycle : GraphInput :=
  input [node (key 7 2) (Pred.all []) [key 7 1],
    node (key 7 1) (Pred.all []) [key 8 2],
    node (key 8 2) (Pred.all []) [key 7 2]] [key 7 2]

theorem resolved_long_cycle_refuses :
    failure longerCycle = some (.cycle [key 7 2, key 7 1, key 8 2, key 7 2]) := by decide

def deliberateLockout : GraphInput :=
  input [node (key 7 1) nonnegative [],
    node (key 7 2) (.le "value" (-1)) [key 7 1]] [key 7 2]

/-- Unsatisfiable restrictions are not a malformed dependency graph. -/
theorem deliberate_lockout_is_not_graph_failure :
    count deliberateLockout = some 2 ∧
    atValue deliberateLockout 0 = some false ∧
    atValue deliberateLockout (-1) = some false := by decide

end Examples

end Minidregg.Theory.LawComposition
