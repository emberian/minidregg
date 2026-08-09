/-
# Theory.CellState -- canonical typed cells and validated patches

A logical cell contains only schema-indexed fields and resource cells.  Each
resource cell packages its value together with authority for that exact value
and evidence for that exact authority.  Canonical bytes and the root are never
independent fields: both are projections of one `Materialized` logical state.

Raw patches declare their field and resource footprints, but only a
`ValidatedPatch` can be applied.  Validation binds the expected pre-root and
forces both footprints to be exactly the keys named by the typed writes.  The
resulting frame and no-ghost theorems therefore speak about the same footprint
that application executes.
-/
import Theory.ReactiveController

namespace Minidregg.Theory.CellState

open Minidregg.Theory
open Minidregg.Theory.IndexedProgram

universe u v w x y z

/-! ## Typed logical state and canonical materialization -/

/-- A cell schema.  Resource authority is indexed by the exact resource value,
and evidence is indexed by the exact authority object it justifies. -/
structure Schema where
  Field : Type u
  FieldType : Field → Type v
  Resource : Type u
  ResourceType : Resource → Type v
  Authority : (resource : Resource) → ResourceType resource → Type w
  Evidence : (resource : Resource) → (value : ResourceType resource) →
    Authority resource value → Type x

/-- One resource value with authority and evidence that cannot be retargeted to
a different resource or value without changing the dependent package. -/
structure ResourceCell (S : Schema.{u, v, w, x}) (resource : S.Resource) where
  value : S.ResourceType resource
  authority : S.Authority resource value
  evidence : S.Evidence resource value authority

/-- The complete logical state.  There is no untyped extension map in which a
host can smuggle extra fields. -/
structure LogicalState (S : Schema.{u, v, w, x}) where
  fields : (field : S.Field) → S.FieldType field
  resources : (resource : S.Resource) → ResourceCell S resource

/-- The only canonical reading.  A root is computed from the exact bytes emitted
by the lawful state codec, so root and encoding have no independent setters. -/
structure Materializer (S : Schema.{u, v, w, x}) (Root : Type y) where
  codec : LawfulCodec (LogicalState S)
  rootBytes : List UInt8 → Root

/-- A dependent package indexed by its sole materializer.  The private
constructor prevents alternate root/encoding fields from being introduced. -/
structure Materialized
    {S : Schema.{u, v, w, x}} {Root : Type y} (M : Materializer S Root) where
  private mk ::
  logical : LogicalState S

/-- The one constructor for canonical cells. -/
def materialize
    {S : Schema.{u, v, w, x}} {Root : Type y} (M : Materializer S Root)
    (logical : LogicalState S) : Materialized M :=
  ⟨logical⟩

/-- Canonical bytes are projected from the packaged logical state. -/
def Materialized.bytes
    {S : Schema.{u, v, w, x}} {Root : Type y} {M : Materializer S Root}
    (cell : Materialized M) : List UInt8 :=
  M.codec.encode cell.logical

/-- The root is necessarily computed from those exact canonical bytes. -/
def Materialized.root
    {S : Schema.{u, v, w, x}} {Root : Type y} {M : Materializer S Root}
    (cell : Materialized M) : Root :=
  M.rootBytes cell.bytes

@[simp] theorem materialize_bytes
    {S : Schema.{u, v, w, x}} {Root : Type y} (M : Materializer S Root)
    (logical : LogicalState S) :
    (materialize M logical).bytes = M.codec.encode logical :=
  rfl

@[simp] theorem materialize_root
    {S : Schema.{u, v, w, x}} {Root : Type y} (M : Materializer S Root)
    (logical : LogicalState S) :
    (materialize M logical).root = M.rootBytes (M.codec.encode logical) :=
  rfl

/-- Root/encoding coherence is definitional, not a separately supplied proof. -/
theorem Materialized.root_encoding_coherent
    {S : Schema.{u, v, w, x}} {Root : Type y} {M : Materializer S Root}
    (cell : Materialized M) :
    cell.root = M.rootBytes cell.bytes :=
  rfl

/-- Canonical materializations are determined entirely by logical state. -/
@[ext] theorem Materialized.ext
    {S : Schema.{u, v, w, x}} {Root : Type y} {M : Materializer S Root}
    {left right : Materialized M} (h : left.logical = right.logical) :
    left = right := by
  cases left
  cases right
  cases h
  rfl

/-! ## Raw and validated typed patches -/

/-- A typed field write. -/
structure FieldWrite (S : Schema.{u, v, w, x}) where
  field : S.Field
  value : S.FieldType field

/-- A typed resource write carries its replacement authority/evidence package. -/
structure ResourceWrite (S : Schema.{u, v, w, x}) where
  resource : S.Resource
  cell : ResourceCell S resource

/-- Untrusted patch syntax.  No root, encoded post-state, or untyped field map is
accepted.  Its declared footprints become authoritative only after validation. -/
structure Patch (S : Schema.{u, v, w, x}) (Root : Type y) where
  expectedPreRoot : Root
  fieldFootprint : Finset S.Field
  resourceFootprint : Finset S.Resource
  fieldWrites : List (FieldWrite S)
  resourceWrites : List (ResourceWrite S)

/-- The field keys actually named by patch syntax. -/
def Patch.namedFields
    {S : Schema.{u, v, w, x}} {Root : Type y} [DecidableEq S.Field]
    (patch : Patch S Root) : Finset S.Field :=
  (patch.fieldWrites.map FieldWrite.field).toFinset

/-- The resource keys actually named by patch syntax. -/
def Patch.namedResources
    {S : Schema.{u, v, w, x}} {Root : Type y} [DecidableEq S.Resource]
    (patch : Patch S Root) : Finset S.Resource :=
  (patch.resourceWrites.map ResourceWrite.resource).toFinset

/-- Apply typed field writes in declaration order; later duplicates win. -/
def applyFieldWrites
    {S : Schema.{u, v, w, x}} [DecidableEq S.Field] :
    List (FieldWrite S) → ((field : S.Field) → S.FieldType field) →
      ((field : S.Field) → S.FieldType field)
  | [], fields => fields
  | write :: rest, fields =>
      applyFieldWrites rest (Function.update fields write.field write.value)

/-- Apply coherent resource packages in declaration order; later duplicates win. -/
def applyResourceWrites
    {S : Schema.{u, v, w, x}} [DecidableEq S.Resource] :
    List (ResourceWrite S) →
      ((resource : S.Resource) → ResourceCell S resource) →
      ((resource : S.Resource) → ResourceCell S resource)
  | [], resources => resources
  | write :: rest, resources =>
      applyResourceWrites rest (Function.update resources write.resource write.cell)

/-- Typed field application cannot affect an unnamed key. -/
theorem applyFieldWrites_frame
    {S : Schema.{u, v, w, x}} [DecidableEq S.Field]
    (writes : List (FieldWrite S))
    (fields : (field : S.Field) → S.FieldType field)
    (field : S.Field)
    (outside : field ∉ (writes.map FieldWrite.field).toFinset) :
    applyFieldWrites writes fields field = fields field := by
  induction writes generalizing fields with
  | nil => rfl
  | cons write rest ih =>
      simp only [List.map_cons, List.toFinset_cons, Finset.mem_insert, not_or] at outside
      rw [applyFieldWrites, ih _ outside.2]
      simp [Function.update, outside.1]

/-- Typed resource application cannot affect an unnamed key. -/
theorem applyResourceWrites_frame
    {S : Schema.{u, v, w, x}} [DecidableEq S.Resource]
    (writes : List (ResourceWrite S))
    (resources : (resource : S.Resource) → ResourceCell S resource)
    (resource : S.Resource)
    (outside : resource ∉ (writes.map ResourceWrite.resource).toFinset) :
    applyResourceWrites writes resources resource = resources resource := by
  induction writes generalizing resources with
  | nil => rfl
  | cons write rest ih =>
      simp only [List.map_cons, List.toFinset_cons, Finset.mem_insert, not_or] at outside
      rw [applyResourceWrites, ih _ outside.2]
      simp [Function.update, outside.1]

/-- Verifier-minted validation for one exact pre-cell and raw patch. -/
structure ValidatedPatch
    {S : Schema.{u, v, w, x}} {Root : Type y} [DecidableEq S.Field]
    [DecidableEq S.Resource] (M : Materializer S Root) (pre : Materialized M)
    (patch : Patch S Root) : Prop where
  private mk ::
  preRoot_bound : patch.expectedPreRoot = pre.root
  fields_exact : patch.fieldFootprint = patch.namedFields
  resources_exact : patch.resourceFootprint = patch.namedResources

/-- Exhaustive validation failures. -/
inductive RejectReason
  | stalePreRoot
  | fieldFootprintMismatch
  | resourceFootprintMismatch
deriving DecidableEq, Repr

/-- Validation is total and only acceptance exposes a `ValidatedPatch`. -/
inductive ValidationOutcome
    {S : Schema.{u, v, w, x}} {Root : Type y} [DecidableEq S.Field]
    [DecidableEq S.Resource] (M : Materializer S Root) (pre : Materialized M)
    (patch : Patch S Root) where
  | accepted (validated : ValidatedPatch M pre patch)
  | rejected (reason : RejectReason)

/-- Validate the exact pre-root and exact declared footprints. -/
def validate
    {S : Schema.{u, v, w, x}} {Root : Type y} [DecidableEq Root]
    [DecidableEq S.Field] [DecidableEq S.Resource]
    (M : Materializer S Root) (pre : Materialized M) (patch : Patch S Root) :
    ValidationOutcome M pre patch :=
  if hroot : patch.expectedPreRoot = pre.root then
    if hfields : patch.fieldFootprint = patch.namedFields then
      if hresources : patch.resourceFootprint = patch.namedResources then
        .accepted ⟨hroot, hfields, hresources⟩
      else
        .rejected .resourceFootprintMismatch
    else
      .rejected .fieldFootprintMismatch
  else
    .rejected .stalePreRoot

/-- Application exists only on the validated type.  Canonical bytes and root
are rematerialized from the resulting typed logical state. -/
def ValidatedPatch.apply
    {S : Schema.{u, v, w, x}} {Root : Type y} [DecidableEq S.Field]
    [DecidableEq S.Resource] {M : Materializer S Root} {pre : Materialized M}
    {patch : Patch S Root} (_validated : ValidatedPatch M pre patch) :
    Materialized M :=
  materialize M
    { fields := applyFieldWrites patch.fieldWrites pre.logical.fields
      resources := applyResourceWrites patch.resourceWrites pre.logical.resources }

/-- An attempt cannot carry an independently supplied post-cell. -/
inductive ApplyOutcome
    {S : Schema.{u, v, w, x}} {Root : Type y} [DecidableEq S.Field]
    [DecidableEq S.Resource] (M : Materializer S Root) (pre : Materialized M)
    (patch : Patch S Root) where
  | rejected (reason : RejectReason)
  | applied (validated : ValidatedPatch M pre patch)

/-- Validate and, only on acceptance, expose an applicable validated patch. -/
def tryApply
    {S : Schema.{u, v, w, x}} {Root : Type y} [DecidableEq Root]
    [DecidableEq S.Field] [DecidableEq S.Resource]
    (M : Materializer S Root) (pre : Materialized M) (patch : Patch S Root) :
    ApplyOutcome M pre patch :=
  match validate M pre patch with
  | .accepted validated => .applied validated
  | .rejected reason => .rejected reason

/-- State after an attempt.  Rejection is definitionally the original cell. -/
def ApplyOutcome.post
    {S : Schema.{u, v, w, x}} {Root : Type y} [DecidableEq S.Field]
    [DecidableEq S.Resource] {M : Materializer S Root} {pre : Materialized M}
    {patch : Patch S Root} : ApplyOutcome M pre patch → Materialized M
  | .rejected _ => pre
  | .applied validated => validated.apply

@[simp] theorem ApplyOutcome.rejection_atomic
    {S : Schema.{u, v, w, x}} {Root : Type y} [DecidableEq S.Field]
    [DecidableEq S.Resource] {M : Materializer S Root} {pre : Materialized M}
    {patch : Patch S Root} (reason : RejectReason) :
    (ApplyOutcome.rejected (M := M) (pre := pre) (patch := patch) reason).post = pre :=
  rfl

/-! ## Frame and no-ghost theorems -/

/-- Every field outside the exact validated footprint is unchanged. -/
theorem ValidatedPatch.field_frame
    {S : Schema.{u, v, w, x}} {Root : Type y} [DecidableEq S.Field]
    [DecidableEq S.Resource] {M : Materializer S Root} {pre : Materialized M}
    {patch : Patch S Root} (validated : ValidatedPatch M pre patch)
    (field : S.Field) (outside : field ∉ patch.fieldFootprint) :
    validated.apply.logical.fields field = pre.logical.fields field := by
  apply applyFieldWrites_frame
  have namedOutside : field ∉ patch.namedFields := by
    rw [← validated.fields_exact]
    exact outside
  simpa [Patch.namedFields] using namedOutside

/-- Every resource package outside the exact validated footprint is unchanged. -/
theorem ValidatedPatch.resource_frame
    {S : Schema.{u, v, w, x}} {Root : Type y} [DecidableEq S.Field]
    [DecidableEq S.Resource] {M : Materializer S Root} {pre : Materialized M}
    {patch : Patch S Root} (validated : ValidatedPatch M pre patch)
    (resource : S.Resource) (outside : resource ∉ patch.resourceFootprint) :
    validated.apply.logical.resources resource = pre.logical.resources resource := by
  apply applyResourceWrites_frame
  have namedOutside : resource ∉ patch.namedResources := by
    rw [← validated.resources_exact]
    exact outside
  simpa [Patch.namedResources] using namedOutside

/-- No field can change unless it occurs in the declared footprint. -/
theorem ValidatedPatch.field_changed_only_declared
    {S : Schema.{u, v, w, x}} {Root : Type y} [DecidableEq S.Field]
    [DecidableEq S.Resource] {M : Materializer S Root} {pre : Materialized M}
    {patch : Patch S Root} (validated : ValidatedPatch M pre patch)
    (field : S.Field)
    (changed : validated.apply.logical.fields field ≠ pre.logical.fields field) :
    field ∈ patch.fieldFootprint := by
  by_contra outside
  exact changed (validated.field_frame field outside)

/-- No resource, authority, or evidence package can change unless its resource
occurs in the declared footprint. -/
theorem ValidatedPatch.resource_changed_only_declared
    {S : Schema.{u, v, w, x}} {Root : Type y} [DecidableEq S.Field]
    [DecidableEq S.Resource] {M : Materializer S Root} {pre : Materialized M}
    {patch : Patch S Root} (validated : ValidatedPatch M pre patch)
    (resource : S.Resource)
    (changed : validated.apply.logical.resources resource ≠
      pre.logical.resources resource) :
    resource ∈ patch.resourceFootprint := by
  by_contra outside
  exact changed (validated.resource_frame resource outside)

/-- Declared footprints contain exactly typed writes: neither undeclared writes
nor declared-but-absent ghost keys survive validation. -/
theorem ValidatedPatch.no_ghost_keys
    {S : Schema.{u, v, w, x}} {Root : Type y} [DecidableEq S.Field]
    [DecidableEq S.Resource] {M : Materializer S Root} {pre : Materialized M}
    {patch : Patch S Root} (validated : ValidatedPatch M pre patch) :
    patch.fieldFootprint = patch.namedFields ∧
      patch.resourceFootprint = patch.namedResources :=
  ⟨validated.fields_exact, validated.resources_exact⟩

/-! ## Conceptual bridge to a reactive commit intent -/

/-- Static mapping from typed cell keys into a controller's unified footprint. -/
structure ControllerLayout
    (S : Schema.{u, v, w, x}) (T : ReactiveController.Types.{z}) where
  fieldKey : S.Field → T.Key
  resourceKey : S.Resource → T.Key

/-- The unified controller footprint derived from the two validated cell
footprints. -/
def Patch.controllerFootprint
    {S : Schema.{u, v, w, x}} {Root : Type y} {T : ReactiveController.Types.{z}}
    [DecidableEq T.Key] (layout : ControllerLayout S T) (patch : Patch S Root) :
    Finset T.Key :=
  patch.fieldFootprint.image layout.fieldKey ∪
    patch.resourceFootprint.image layout.resourceKey

/-- A proof-only bridge: a guarded `CommitIntent` may authorize a validated cell
patch exactly when both canonical roots and the unified footprint agree.  This
does not perform, or claim to perform, the external durable CAS. -/
structure IntentBinding
    {U : FirstOrderUniverse} {T : ReactiveController.Types.{z}}
    [LinearOrder T.Height]
    [DecidableEq (ReactiveController.HoleSpec U T)] [DecidableEq T.TurnId]
    [DecidableEq T.AuthorityDemand] [DecidableEq T.Commitment]
    [DecidableEq T.Root] [DecidableEq T.Key] [DecidableEq T.Value]
    [DecidableEq (GuardedAdvice.NullifierKey T.vocabulary)]
    {S : Schema.{u, v, w, x}} [DecidableEq S.Field] [DecidableEq S.Resource]
    (M : Materializer S T.Root)
    (layout : ControllerLayout S T)
    {decl : ReactiveController.Declaration U T}
    {obs : ReactiveController.HostObservation T}
    {advice : ReactiveController.Advice decl.hole}
    {proof : ReactiveController.ProofData T}
    {controllerPre : ReactiveReceipt.Store T.Key T.Value}
    (intent : ReactiveController.CommitIntent decl obs advice proof controllerPre)
    (pre : Materialized M) {patch : Patch S T.Root}
    (validated : ValidatedPatch M pre patch) : Prop where
  preRoot_bound : intent.request.preRoot = pre.root
  postRoot_bound : intent.verified.postRoot = validated.apply.root
  footprint_bound : patch.controllerFootprint layout = decl.hole.footprint

end Minidregg.Theory.CellState
