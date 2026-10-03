/- Generic source inspection consumes the current authorized loader token.
This projection neither enumerates world sources nor admits an executable.
Original source text and reflected core are shown separately: their semantic
correspondence is not inferred from labels or a successful core parse. -/
import Kernel.ObjectiveBendReferenceSource
import Lean.Data.Json

namespace Minidregg.Host.ObjectiveBendSourceInspection
open Minidregg.Compiler
open Minidregg.Theory
open ObjectiveBendReference
set_option autoImplicit false

variable {F : Type} [Field F] [DecidableEq F]
  {deployment : ResourceObservationAdmission.Deployment}
  {durable : ResourceObservationAdmission.Durable}
  {context : ResourceObservationAdmission.Context deployment durable}
  {profile : CanonicalRuntimeProfile.Profile F} {subject : TypedAuthorization.SubjectId}

private def ids (values : List Nat) : Lean.Json :=
  .arr (values.map (fun value => Lean.Json.str (toString value))).toArray
private def sourceModule (position : Nat) (value : BendWorldSource.Module) : Lean.Json :=
  .mkObj [
    ("index", .str (toString position)), ("name", .str value.name),
    ("sourceIdentity", .str (toString (BendWorldSource.sourceId value.bytes).value)),
    ("bytes", .str (toString value.bytes.length)),
    ("text", match String.fromUTF8? ⟨value.bytes.toArray⟩ with
      | none => .null | some text => .str text),
    ("imports", .arr (value.imports.map fun edge => Lean.Json.mkObj [
      ("alias", .str edge.importAlias), ("module", .str (toString edge.moduleIndex)),
      ("sourceIdentity", .str (toString edge.source.value))]).toArray)]

/-- The actual admitted narrowed source, pinned resource/root and immutable
content identity remain in the receiving type. A stale or unreadable source
cannot construct this token through the current loader. -/
def partial (reference : Reference)
    (loaded : Kernel.ObjectiveBendReferenceSource.PartialAt (context := context)
      (profile := profile) (subject := subject) reference) : Lean.Json :=
  let value := loaded.prototype
  let reflected := ObjectiveBendPrototype.reflect value
  .mkObj [
    ("schema", .str "dregg.objective-bend.authorized-source-inspection.v1"),
    ("resource", .str (toString reference.resource)),
    ("root", .str (toString reference.root.value)),
    ("contentIdentity", .str (toString reference.content.value)),
    ("prototypeIdentity", .str (toString (ObjectiveBendPrototype.identity value))),
    ("packageIdentity", .str (toString (BendWorldSource.packageId value.source).value)),
    ("entryModule", .str (toString value.source.entryModule)),
    ("entryDefinition", .str value.source.entryDefinition),
    ("directParents", ids value.directParents), ("ancestorOrder", ids value.ancestorOrder),
    ("modules", .arr (value.source.modules.zipIdx.map fun (value, position) =>
      sourceModule position value).toArray),
    ("canonicalOpenCore", match String.fromUTF8? ⟨value.core.toArray⟩ with
      | none => .null | some text => .str text),
    ("required", .arr (value.required.map fun entry => Lean.Json.mkObj [
      ("scope", .str (match entry.scope with | .finalSelf => "finalSelf" | .priorSuper => "priorSuper")),
      ("selector", .str entry.selector), ("typeEntry", .str entry.typeEntry)]).toArray),
    ("provided", .arr (value.provided.map fun entry => Lean.Json.mkObj [
      ("selector", .str entry.selector), ("entry", .str entry.entry),
      ("captures", .arr (entry.captures.map Lean.Json.str).toArray)]).toArray),
    ("reflection", match reflected with
      | .error diagnostic => Lean.Json.mkObj [("status", .str "refused"), ("diagnostic", .str diagnostic)]
      | .ok spec => Lean.Json.mkObj [("status", .str "reflected-partial"),
          ("requirements", .arr (spec.requirements.map fun entry => Lean.Json.mkObj [
            ("selector", .str entry.interface.selector),
            ("coreType", .str (BendTT.Term.show entry.interface.type 0))]).toArray),
          ("provisions", .arr (spec.provisions.map fun entry => Lean.Json.mkObj [
            ("selector", .str entry.interface.selector), ("coreEntry", .str entry.entry),
            ("coreType", .str (BendTT.Term.show entry.interface.type 0)),
            ("coreBody", .str (BendTT.Term.show entry.body 0))]).toArray)])]

theorem inspected_current_root (reference : Reference)
    (loaded : Kernel.ObjectiveBendReferenceSource.PartialAt (context := context)
      (profile := profile) (subject := subject) reference) :
    loaded.source.current.value.root = reference.root := loaded.source.rootExact

#assert_axioms inspected_current_root
end Minidregg.Host.ObjectiveBendSourceInspection
