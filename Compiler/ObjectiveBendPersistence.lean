/- First persistence bridge for reusable Objective Bend partial source. It seals
canonical partial Books and replaces authoring-local labels with full immutable
content identities before composition. No authority, evaluator or publication
rights are supplied by this bridge. -/
import Compiler.ObjectiveBendPrototype
import Compiler.ObjectiveBendOrder
import Compiler.ObjectiveBendElaboration

namespace Minidregg.Compiler.ObjectiveBendPersistence
open Minidregg.Theory.BendTT
open ObjectiveBendComposition
set_option autoImplicit false

structure Sealed where
  localId : Nat
  artifact : ObjectiveBendPrototype.Partial
  spec : Spec
  exact : ObjectiveBendPrototype.reflect artifact = .ok spec

/-- Requirement stubs are parsed declarations of open interfaces. Their body
is NEVER admitted or included as an executable helper by this bridge. -/
def requirementDefinition (required : Requirement) : Def :=
  { k := ObjectiveBendElaboration.authoredName required
    T := required.interface.type, v := .Efq, o := false }

def provisionName (provision : Provision) : String :=
  "prototype." ++ provision.interface.selector

def provisionDefinition (provision : Provision) : Def :=
  { k := provisionName provision, T := provision.interface.type,
    v := provision.body, o := false }

def sourceBook (spec : Spec) : Book :=
  spec.requirements.map requirementDefinition ++ spec.provisions.map provisionDefinition

private def immutableId (sealed : List Sealed) (localId : Nat) : Except String Nat :=
  match sealed.find? (fun prior => prior.localId == localId) with
  | none => .error "prototype parent or ancestor is not sealed earlier"
  | some prior => .ok prior.spec.id

/-- Current ordinary source wrappers capture immutable Data inline. Nonempty
stored environments await the world's explicit Data/type-capture loader; they
are refused rather than silently serializing reusable runtime closures. -/
def sealOne (source : BendWorldSource.Package) (earlier : List Sealed) (spec : Spec) :
    Except String Sealed := do
  if !spec.provisions.all (fun p => p.captured.isEmpty) then
    throw "stored capture environment requires explicit qualified Data loader"
  if !(decide (spec.order.getLast? = some spec.id)) then throw "prototype order omits own endpoint"
  let parents ← spec.directParents.mapM (immutableId earlier)
  let ancestors ← (spec.order.take (spec.order.length - 1)).mapM (immutableId earlier)
  let artifact : ObjectiveBendPrototype.Partial := {
    source := source, directParents := parents, ancestorOrder := ancestors
    core := BendCoreAdmission.encode (sourceBook spec)
    required := spec.requirements.map (fun r =>
      ⟨r.scope, r.interface.selector, ObjectiveBendElaboration.authoredName r⟩)
    provided := spec.provisions.map (fun p => ⟨p.interface.selector, provisionName p, []⟩) }
  match exact : ObjectiveBendPrototype.reflect artifact with
  | .error reason => throw reason
  | .ok reflected => pure ⟨spec.id, artifact, reflected, exact⟩

/-- A lawful open composition remains authorable. Closure of method interfaces
is enforced later by the common linker/Construction, not by sealing source. -/
def seal (source : BendWorldSource.Package) (specs : List Spec) : Except String (List Sealed) := do
  let some root := specs.getLast? | throw "empty prototype source composition"
  if (ObjectiveBendOrder.check root specs).isNone then throw "unlawful authoring-local ancestry"
  let sealed ← specs.foldlM (fun earlier spec => do
    let next ← sealOne source earlier spec
    pure (earlier ++ [next])) []
  let reflected := sealed.map Sealed.spec
  let some final := reflected.getLast? | throw "empty reflected prototype composition"
  if (ObjectiveBendOrder.check final reflected).isNone then throw "unlawful immutable ancestry"
  pure sealed

/-- Persistent byte roundtrip preserves exact artifact and source/reflection.
The source loader replays the same reflection; no member-supplied body replaces
what the canonical partial Book actually declared. -/
theorem sealed_roundtrip (sealed : Sealed) :
    ObjectiveBendPrototype.decode (ObjectiveBendPrototype.encode sealed.artifact) =
      some sealed.artifact := ObjectiveBendPrototype.roundtrip sealed.artifact

theorem reflected_source_exact (sealed : Sealed) :
    ObjectiveBendPrototype.reflect sealed.artifact = .ok sealed.spec := sealed.exact

#assert_axioms sealed_roundtrip
#assert_axioms reflected_source_exact
end Minidregg.Compiler.ObjectiveBendPersistence
