/-
# Kernel.CanonicalResourceEffect -- the resource book on the accepted-effect path

`Theory.CanonicalResourceKernel` already owns the exact resource semantics: a
transfer, issuer-backed mint, burn, fee, or prepaid lease becomes one balanced
posting and one verifier-minted book patch.  This module closes the remaining
integration seam.  It does not ask a caller to restate that patch, its digest,
its post-book, or its conservation vector.

The operation and its posting have lawful first-order codecs.  The common
authorization request derives its target, verb, argument digest, effect digest,
pre-root, and cost from the operation and exact canonical pre-cell.  An existing
`CanonicalResourceKernel.Accepted` value plus authority for that derived request
therefore constructs the ordinary `AcceptedCellEffect` without equality side
conditions.

The resource laws below read their delta from the exact accepted pre/post book.
They work for `TypedCellHyperedge` and the fixed-resource-schema specialization
of `MultiCellHyperedge`; there is no callback capable of reporting a different
balance vector from the installed patch.  Physical settlement, durable CAS,
cryptographic collision resistance, sharding, and wall-clock lease expiry remain
outside this bounded logical nucleus.
-/
import Kernel.MultiCellHyperedge
import Kernel.TypedCellHyperedge
import Compiler.CanonicalResourcePageMaterializer
import Theory.ResourceBirth

namespace Minidregg.Kernel.CanonicalResourceEffect

open Minidregg.Theory
open Minidregg.Theory.CellState
open Minidregg.Theory.IndexedProgram
open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.CanonicalResourceKernel

set_option autoImplicit false

local instance schemaFieldDecidableEq : DecidableEq CanonicalResourceKernel.schema.Field := by
  change DecidableEq CanonicalResourceKernel.Field
  infer_instance

local instance schemaResourceDecidableEq : DecidableEq CanonicalResourceKernel.schema.Resource := by
  change DecidableEq Empty
  infer_instance

/-! ## Canonical first-order operation and posting commitments -/

/-- The sole resource wire codecs are the concrete compact v2 codecs. -/
abbrev operationCodec := Compiler.CanonicalResourcePageMaterializer.operationCodec
abbrev postingCodec := Compiler.CanonicalResourcePageMaterializer.postingCodec
abbrev batchCodec := Compiler.CanonicalResourcePageMaterializer.batchCodec

def argsCustomization : List UInt8 := "DREGG.RESOURCE.ARGUMENT/v2".toUTF8.toList
def postingCustomization : List UInt8 := "DREGG.RESOURCE.POSTING/v2".toUTF8.toList
def effectCustomization : List UInt8 := "DREGG.RESOURCE.EFFECT/v2".toUTF8.toList
def batchCustomization : List UInt8 := "DREGG.RESOURCE.BATCH/v2".toUTF8.toList

def argsDigest (operation : Operation) : Digest :=
  (Compiler.Sp800185Cshake256.hash argsCustomization (operationCodec.encode operation)).digest

def resourceDigest (operation : Operation) : Digest :=
  (Compiler.Sp800185Cshake256.hash postingCustomization
    (postingCodec.encode operation.posting)).digest

/-- Both full operation and derived posting bytes enter the effect hash via
one derived product codec; no host-selected length or digest enters instead. -/
def effectBytes (operation : Operation) : List UInt8 :=
  Compiler.CanonicalResourcePageMaterializer.effectSourceCodec.encode
    (operation, operation.posting)

theorem effectBytes_injective : Function.Injective effectBytes := by
  intro left right same
  exact congrArg Prod.fst
    (Compiler.CanonicalResourcePageMaterializer.codec_encode_injective
      Compiler.CanonicalResourcePageMaterializer.effectSourceCodec same)

def effectDigest (operation : Operation) : Digest :=
  (Compiler.Sp800185Cshake256.hash effectCustomization (effectBytes operation)).digest

def batchDigest (batch : Batch) : Digest :=
  (Compiler.Sp800185Cshake256.hash batchCustomization (batchCodec.encode batch)).digest

/-- The exact compared-pair collision event. An unbounded operation language
cannot inject into a fixed 256-bit digest, so the former unconditional
`argsDigest_injective` theorem is deliberately removed. -/
structure ArgumentCollision (left right : Operation) : Prop where
  operationsDifferent : left ≠ right
  sourceBytesDifferent : operationCodec.encode left ≠ operationCodec.encode right
  hashesEqual : argsDigest left = argsDigest right

def ArgsPairBindingPremise (left right : Operation) : Prop :=
  ¬ ArgumentCollision left right

theorem argumentCollision_of_eq_of_ne {left right : Operation}
    (same : argsDigest left = argsDigest right) (different : left ≠ right) :
    ArgumentCollision left right :=
  ⟨different,
    fun bytes => different
      (Compiler.CanonicalResourcePageMaterializer.codec_encode_injective operationCodec bytes),
    same⟩

theorem argsDigest_eq_or_collision {left right : Operation}
    (same : argsDigest left = argsDigest right) : left = right ∨ ArgumentCollision left right := by
  by_cases equal : left = right
  · exact Or.inl equal
  · exact Or.inr (argumentCollision_of_eq_of_ne same equal)

theorem operation_eq_of_argsDigest_eq {left right : Operation}
    (binding : ArgsPairBindingPremise left right)
    (same : argsDigest left = argsDigest right) : left = right := by
  by_contra different
  exact binding (argumentCollision_of_eq_of_ne same different)

/-! ## The derived common authorization request -/

/-- Only genuinely ambient request data remain configurable.  Every field that
describes the resource effect itself is derived below. -/
structure RequestContext where
  domain : Digest
  semantics : Digest
  federation : FederationId
  subject : SubjectId
  subjectKeyEpoch : TypedAuthorization.Epoch
  nonce : Nat
  height : Height
  policyId : PolicyId
  policyEpoch : TypedAuthorization.Epoch

/-- Resource operations are balanced value movements from their posting source.
The operation/effect commitments distinguish mint, burn, fee, and lease from an
ordinary transfer; the account target is never supplied separately. -/
def RequestContext.request
    {M : CellState.Materializer CanonicalResourceKernel.schema Digest}
    (context : RequestContext) (pre : CellState.Materialized M)
    (operation : CanonicalResourceKernel.Operation) : Request .account where
  domain := context.domain
  semantics := context.semantics
  federation := context.federation
  subject := context.subject
  subjectKeyEpoch := context.subjectKeyEpoch
  target := ⟨operation.posting.source⟩
  verb := .transfer
  argsDigest := argsDigest operation
  effectsDigest := effectDigest operation
  nonce := context.nonce
  height := context.height
  preStateRoot := pre.root
  policyId := context.policyId
  policyEpoch := context.policyEpoch
  cost := operation.feeDebit

@[simp] theorem RequestContext.request_target
    {M : CellState.Materializer CanonicalResourceKernel.schema Digest}
    (context : RequestContext) (pre : CellState.Materialized M)
    (operation : CanonicalResourceKernel.Operation) :
    (context.request pre operation).target.value = operation.posting.source :=
  rfl

@[simp] theorem RequestContext.request_argsDigest
    {M : CellState.Materializer CanonicalResourceKernel.schema Digest}
    (context : RequestContext) (pre : CellState.Materialized M)
    (operation : CanonicalResourceKernel.Operation) :
    (context.request pre operation).argsDigest = argsDigest operation :=
  rfl

@[simp] theorem RequestContext.request_effectsDigest
    {M : CellState.Materializer CanonicalResourceKernel.schema Digest}
    (context : RequestContext) (pre : CellState.Materialized M)
    (operation : CanonicalResourceKernel.Operation) :
    (context.request pre operation).effectsDigest = effectDigest operation :=
  rfl

@[simp] theorem RequestContext.request_preRoot
    {M : CellState.Materializer CanonicalResourceKernel.schema Digest}
    (context : RequestContext) (pre : CellState.Materialized M)
    (operation : CanonicalResourceKernel.Operation) :
    (context.request pre operation).preStateRoot = pre.root :=
  rfl

def unitCodec : LawfulCodec Unit where
  encode := fun _ => []
  decode
    | [] => some ()
    | _ => none
  decode_encode := fun _ => rfl

/-! ## The canonical accepted-effect family -/

/-- The family is indexed by the exact canonical pre-cell because applying a
posting reads the current book.  Its declaration remains first-order: only the
operation crosses the boundary, while the family closes over trusted state. -/
def family
    {M : CellState.Materializer CanonicalResourceKernel.schema Digest}
    (pre : CellState.Materialized M) (context : RequestContext) :
    SemanticEffectFamily.{0, 0, 0, 0, 0, 0} CanonicalResourceKernel.schema M Unit where
  pre := pre
  Declaration := CanonicalResourceKernel.Operation
  request := fun operation => ⟨.account, context.request pre operation⟩
  declarationCodec := operationCodec
  Outcome := fun _ => Unit
  outcomeCodec := fun _ => unitCodec
  ModeEvidence := fun operation _ =>
    PLift (CanonicalResourceKernel.Admission
      (CanonicalResourceKernel.logicalBook pre.logical) operation)
  effectDigest := effectDigest
  patch := fun operation _ => operation.patch pre
  nullifier := fun _ _ => none
  Release := fun _ _ => PEmpty
  DeclassificationAuthority := fun _ _ => PEmpty
  ReleaseAuthorization := fun _ _ release => release.elim
  DisclosureAllowed := fun _ _ disclosure => disclosure = .sealed

/-- An already-admitted canonical resource transition enters the universal
accepted-effect path under authority for the one fully derived request. -/
def toCellEffect
    {M : CellState.Materializer CanonicalResourceKernel.schema Digest}
    {pre : CellState.Materialized M} {operation : CanonicalResourceKernel.Operation}
    {portal : Portal} {authState : AuthState}
    (accepted : CanonicalResourceKernel.Accepted pre operation) (context : RequestContext)
    (authorization : Authorized portal authState (context.request pre operation)) :
    AcceptedCellEffect (portal := portal) (authState := authState)
      (family pre context) (context.request pre operation) pre operation () where
  authorization := authorization
  preStateBound := rfl
  requestBound := rfl
  effectsDigestBound := rfl
  preRootBound := rfl
  modeEvidence := PLift.up accepted.admission
  validated := accepted.validated
  disclosure := .sealed
  disclosureAllowed := rfl

@[simp] theorem toCellEffect_prepared_post
    {M : CellState.Materializer CanonicalResourceKernel.schema Digest}
    {pre : CellState.Materialized M} {operation : CanonicalResourceKernel.Operation}
    {portal : Portal} {authState : AuthState}
    (accepted : CanonicalResourceKernel.Accepted pre operation) (context : RequestContext)
    (authorization : Authorized portal authState (context.request pre operation)) :
    (toCellEffect accepted context authorization).prepared.post = accepted.post :=
  rfl

@[simp] theorem toCellEffect_post_book
    {M : CellState.Materializer CanonicalResourceKernel.schema Digest}
    {pre : CellState.Materialized M} {operation : CanonicalResourceKernel.Operation}
    {portal : Portal} {authState : AuthState}
    (accepted : CanonicalResourceKernel.Accepted pre operation) (context : RequestContext)
    (authorization : Authorized portal authState (context.request pre operation)) :
    CanonicalResourceKernel.logicalBook
      (toCellEffect accepted context authorization).prepared.post.logical =
      operation.apply (CanonicalResourceKernel.logicalBook pre.logical) := by
  change CanonicalResourceKernel.logicalBook accepted.post.logical =
    operation.apply (CanonicalResourceKernel.logicalBook pre.logical)
  exact accepted.post_logicalBook

theorem toCellEffect_conserves
    {M : CellState.Materializer CanonicalResourceKernel.schema Digest}
    {pre : CellState.Materialized M} {operation : CanonicalResourceKernel.Operation}
    {portal : Portal} {authState : AuthState}
    (accepted : CanonicalResourceKernel.Accepted pre operation) (context : RequestContext)
    (authorization : Authorized portal authState (context.request pre operation))
    (asset : CanonicalResourceKernel.AssetId) :
    (CanonicalResourceKernel.logicalBook
      (toCellEffect accepted context authorization).prepared.post.logical).totalAsset asset =
      (CanonicalResourceKernel.logicalBook pre.logical).totalAsset asset := by
  simpa using accepted.conserves asset

/-! ## Birth batches retain factory and every source's old authority

The declaration is the complete birth descriptor, not an independently
supplied Book batch. Its registration and payment projection is computed by
`ResourceBirth.Descriptor.resourceBatch`. A factory authorization cannot
substitute for a payer's authorization, and a payer cannot invent namespace
authority for newly registered accounts.
-/

def sourceCustomization : List UInt8 := "DREGG.RESOURCE.BATCH.SOURCE/v2".toUTF8.toList

/-- Full birth bytes, the exact derived batch, and the operation position are
all committed. Thus identical-looking debits at different positions still
have different source preimages. Hash binding remains collision-scoped. -/
def sourceArgsBytes {registry : CellRegistry.TypeRegistry Digest}
    (encoding : ResourceBirth.SourceEncoding registry)
    (descriptor : ResourceBirth.Descriptor registry) (position : Nat) : List UInt8 :=
  let sourceCodec := Compiler.Tower256ConcreteBackend.StreamCodec.product
    Compiler.Tower256ConcreteBackend.bytesStream
    (Compiler.Tower256ConcreteBackend.StreamCodec.product
      Compiler.Tower256ConcreteBackend.bytesStream
      Compiler.Tower256ConcreteBackend.StreamCodec.nat)
  sourceCodec.encode
    (encoding.codec.encode descriptor, batchCodec.encode descriptor.resourceBatch, position)

def sourceArgsDigest {registry : CellRegistry.TypeRegistry Digest}
    (encoding : ResourceBirth.SourceEncoding registry)
    (descriptor : ResourceBirth.Descriptor registry) (position : Nat) : Digest :=
  (Compiler.Sp800185Cshake256.hash sourceCustomization
    (sourceArgsBytes encoding descriptor position)).digest

def batchSourceRequest {registry : CellRegistry.TypeRegistry Digest}
    {M : CellState.Materializer CanonicalResourceKernel.schema Digest}
    (encoding : ResourceBirth.SourceEncoding registry) (pre : CellState.Materialized M)
    (contexts : Nat → RequestContext) (descriptor : ResourceBirth.Descriptor registry)
    (position : Fin descriptor.resourceBatch.operations.length) : Request .account :=
  { (contexts position).request pre (descriptor.resourceBatch.operations.get position) with
    argsDigest := sourceArgsDigest encoding descriptor position
    effectsDigest := encoding.effectsDigest descriptor }

/-- The descriptor's fee is its final resource operation, so its authorization
also supplies the outer accepted effect request without an extra authority. -/
def feePosition {registry : CellRegistry.TypeRegistry Digest}
    (descriptor : ResourceBirth.Descriptor registry) :
    Fin descriptor.resourceBatch.operations.length :=
  ⟨descriptor.funding.length, by simp [ResourceBirth.Descriptor.resourceBatch]⟩

def birthRequest {registry : CellRegistry.TypeRegistry Digest}
    {M : CellState.Materializer CanonicalResourceKernel.schema Digest}
    (encoding : ResourceBirth.SourceEncoding registry) (pre : CellState.Materialized M)
    (contexts : Nat → RequestContext) (descriptor : ResourceBirth.Descriptor registry) :
    Request .account :=
  batchSourceRequest encoding pre contexts descriptor (feePosition descriptor)

@[simp] theorem feePosition_operation {registry : CellRegistry.TypeRegistry Digest}
    (descriptor : ResourceBirth.Descriptor registry) :
    descriptor.resourceBatch.operations.get (feePosition descriptor) = descriptor.fee.operation := by
  simp [feePosition, ResourceBirth.Descriptor.resourceBatch]

@[simp] theorem birthRequest_target {registry : CellRegistry.TypeRegistry Digest}
    {M : CellState.Materializer CanonicalResourceKernel.schema Digest}
    (encoding : ResourceBirth.SourceEncoding registry) (pre : CellState.Materialized M)
    (contexts : Nat → RequestContext) (descriptor : ResourceBirth.Descriptor registry) :
    (birthRequest encoding pre contexts descriptor).target.value = descriptor.fee.payer := by
  change (descriptor.resourceBatch.operations.get (feePosition descriptor)).posting.source = _
  rw [feePosition_operation]
  rfl

@[simp] theorem birthRequest_cost {registry : CellRegistry.TypeRegistry Digest}
    {M : CellState.Materializer CanonicalResourceKernel.schema Digest}
    (encoding : ResourceBirth.SourceEncoding registry) (pre : CellState.Materialized M)
    (contexts : Nat → RequestContext) (descriptor : ResourceBirth.Descriptor registry) :
    (birthRequest encoding pre contexts descriptor).cost = descriptor.fee.amount := by
  change (descriptor.resourceBatch.operations.get (feePosition descriptor)).feeDebit = _
  rw [feePosition_operation]
  rfl

structure BirthBatchEvidence {registry : CellRegistry.TypeRegistry Digest}
    {M : CellState.Materializer CanonicalResourceKernel.schema Digest}
    (pins : ResourceBirth.FactoryPins) (encoding : ResourceBirth.SourceEncoding registry)
    (portal : Portal) (oldAuthority : AuthState) (factoryPreRoot : Digest) (height : Height)
    (pre : CellState.Materialized M) (contexts : Nat → RequestContext)
    (descriptor : ResourceBirth.Descriptor registry) where
  factory : ResourceBirth.FactoryAuthorization pins encoding portal oldAuthority
    factoryPreRoot height descriptor
  admission : descriptor.resourceBatch.Admission (logicalBook pre.logical)
  sources : ∀ position : Fin descriptor.resourceBatch.operations.length,
    Authorized portal oldAuthority (batchSourceRequest encoding pre contexts descriptor position)

def birthFamily {registry : CellRegistry.TypeRegistry Digest}
    {M : CellState.Materializer CanonicalResourceKernel.schema Digest}
    (pins : ResourceBirth.FactoryPins) (encoding : ResourceBirth.SourceEncoding registry)
    (portal : Portal) (oldAuthority : AuthState) (factoryPreRoot : Digest) (height : Height)
    (pre : CellState.Materialized M) (contexts : Nat → RequestContext) :
    SemanticEffectFamily.{0, 0, 0, 0, 0, 0} CanonicalResourceKernel.schema M Unit where
  pre := pre
  Declaration := ResourceBirth.Descriptor registry
  declarationCodec := encoding.codec
  request := fun descriptor => ⟨.account, birthRequest encoding pre contexts descriptor⟩
  Outcome := fun _ => Unit
  outcomeCodec := fun _ => unitCodec
  ModeEvidence := fun descriptor _ =>
    BirthBatchEvidence pins encoding portal oldAuthority factoryPreRoot height pre contexts descriptor
  effectDigest := encoding.effectsDigest
  patch := fun descriptor _ => descriptor.resourceBatch.patch pre
  nullifier := fun _ _ => none
  Release := fun _ _ => PEmpty
  DeclassificationAuthority := fun _ _ => PEmpty
  ReleaseAuthorization := fun _ _ release => release.elim
  DisclosureAllowed := fun _ _ disclosure => disclosure = .sealed

def toBirthCellEffect {registry : CellRegistry.TypeRegistry Digest}
    {M : CellState.Materializer CanonicalResourceKernel.schema Digest}
    {pins : ResourceBirth.FactoryPins} {encoding : ResourceBirth.SourceEncoding registry}
    {portal : Portal} {oldAuthority : AuthState} {factoryPreRoot : Digest} {height : Height}
    {pre : CellState.Materialized M} {contexts : Nat → RequestContext}
    {descriptor : ResourceBirth.Descriptor registry}
    (evidence : BirthBatchEvidence pins encoding portal oldAuthority factoryPreRoot height
      pre contexts descriptor) :
    AcceptedCellEffect (portal := portal) (authState := oldAuthority)
      (birthFamily pins encoding portal oldAuthority factoryPreRoot height pre contexts)
      (birthRequest encoding pre contexts descriptor) pre descriptor () where
  authorization := evidence.sources (feePosition descriptor)
  preStateBound := rfl
  requestBound := rfl
  effectsDigestBound := rfl
  preRootBound := rfl
  modeEvidence := evidence
  validated := (AcceptedBatch.ofAdmission evidence.admission).validated
  disclosure := .sealed
  disclosureAllowed := rfl

theorem toBirthCellEffect_post_book {registry : CellRegistry.TypeRegistry Digest}
    {M : CellState.Materializer CanonicalResourceKernel.schema Digest}
    {pins : ResourceBirth.FactoryPins} {encoding : ResourceBirth.SourceEncoding registry}
    {portal : Portal} {oldAuthority : AuthState} {factoryPreRoot : Digest} {height : Height}
    {pre : CellState.Materialized M} {contexts : Nat → RequestContext}
    {descriptor : ResourceBirth.Descriptor registry}
    (evidence : BirthBatchEvidence pins encoding portal oldAuthority factoryPreRoot height
      pre contexts descriptor) :
    logicalBook (toBirthCellEffect evidence).prepared.post.logical =
      descriptor.resourceBatch.apply (logicalBook pre.logical) :=
  (AcceptedBatch.ofAdmission evidence.admission).post_logicalBook

theorem toBirthCellEffect_conserves {registry : CellRegistry.TypeRegistry Digest}
    {M : CellState.Materializer CanonicalResourceKernel.schema Digest}
    {pins : ResourceBirth.FactoryPins} {encoding : ResourceBirth.SourceEncoding registry}
    {portal : Portal} {oldAuthority : AuthState} {factoryPreRoot : Digest} {height : Height}
    {pre : CellState.Materialized M} {contexts : Nat → RequestContext}
    {descriptor : ResourceBirth.Descriptor registry}
    (evidence : BirthBatchEvidence pins encoding portal oldAuthority factoryPreRoot height
      pre contexts descriptor) (asset : AssetId) :
    (logicalBook (toBirthCellEffect evidence).prepared.post.logical).totalAsset asset =
      (logicalBook pre.logical).totalAsset asset :=
  (AcceptedBatch.ofAdmission evidence.admission).conserves asset

def birth_sources_authorized {registry : CellRegistry.TypeRegistry Digest}
    {M : CellState.Materializer CanonicalResourceKernel.schema Digest}
    {pins : ResourceBirth.FactoryPins} {encoding : ResourceBirth.SourceEncoding registry}
    {portal : Portal} {oldAuthority : AuthState} {factoryPreRoot : Digest} {height : Height}
    {pre : CellState.Materialized M} {contexts : Nat → RequestContext}
    {descriptor : ResourceBirth.Descriptor registry}
    (evidence : BirthBatchEvidence pins encoding portal oldAuthority factoryPreRoot height
      pre contexts descriptor) (position : Fin descriptor.resourceBatch.operations.length) :
    Authorized portal oldAuthority (batchSourceRequest encoding pre contexts descriptor position) :=
  evidence.sources position

/-- Possessing the factory authorization never authorizes an unrelated payer.
One missing source permission makes the batch evidence uninhabited. -/
theorem no_birthEvidence_of_unauthorized_source {registry : CellRegistry.TypeRegistry Digest}
    {M : CellState.Materializer CanonicalResourceKernel.schema Digest}
    {pins : ResourceBirth.FactoryPins} {encoding : ResourceBirth.SourceEncoding registry}
    {portal : Portal} {oldAuthority : AuthState} {factoryPreRoot : Digest} {height : Height}
    {pre : CellState.Materialized M} {contexts : Nat → RequestContext}
    {descriptor : ResourceBirth.Descriptor registry}
    (position : Fin descriptor.resourceBatch.operations.length)
    (refused : IsEmpty (Authorized portal oldAuthority
      (batchSourceRequest encoding pre contexts descriptor position))) :
    IsEmpty (BirthBatchEvidence pins encoding portal oldAuthority factoryPreRoot height
      pre contexts descriptor) :=
  ⟨fun evidence => refused.false (evidence.sources position)⟩

@[simp] theorem batchSourceRequest_target {registry : CellRegistry.TypeRegistry Digest}
    {M : CellState.Materializer CanonicalResourceKernel.schema Digest}
    (encoding : ResourceBirth.SourceEncoding registry) (pre : CellState.Materialized M)
    (contexts : Nat → RequestContext) (descriptor : ResourceBirth.Descriptor registry)
    (position : Fin descriptor.resourceBatch.operations.length) :
    (batchSourceRequest encoding pre contexts descriptor position).target.value =
      (descriptor.resourceBatch.operations.get position).posting.source := rfl

theorem birth_one_book_write {M : CellState.Materializer CanonicalResourceKernel.schema Digest}
    (pre : CellState.Materialized M) (batch : Batch) :
    (batch.patch pre).fieldWrites.length = 1 ∧
      (batch.patch pre).fieldFootprint = {.book} := ⟨rfl, rfl⟩

/-! ## Patch-derived resource laws -/

/-- The only balance delta used by the adapters: exact accepted post minus exact
canonical pre.  It is not an executor touch count or caller declaration. -/
def bookDelta (pre post : CellState.LogicalState CanonicalResourceKernel.schema)
    (asset : CanonicalResourceKernel.AssetId) : Int :=
  (CanonicalResourceKernel.logicalBook post).totalAsset asset -
    (CanonicalResourceKernel.logicalBook pre).totalAsset asset

/-- Same-cell resource law for `TypedCellHyperedge`, derived from every leg's
accepted patch application. -/
def typedResourceLaw
    (M : CellState.Materializer CanonicalResourceKernel.schema Digest) (portal : Portal) :
    Minidregg.Kernel.TypedCellHyperedge.ResourceLaw CanonicalResourceKernel.schema M portal CanonicalResourceKernel.AssetId Int where
  stateDelta := fun pre post _ _ asset => bookDelta pre post asset

/-- Package the canonical accepted resource effect as one typed-hyperedge leg. -/
def toTypedLeg
    {M : CellState.Materializer CanonicalResourceKernel.schema Digest}
    {pre : CellState.Materialized M} {operation : CanonicalResourceKernel.Operation}
    {portal : Portal} {authState : AuthState}
    (accepted : CanonicalResourceKernel.Accepted pre operation) (context : RequestContext)
    (authorization : Authorized portal authState (context.request pre operation)) :
    Minidregg.Kernel.TypedCellHyperedge.Leg portal authState pre where
  Nullifier := Unit
  family := family pre context
  kind := .account
  request := context.request pre operation
  declaration := operation
  outcome := ()
  accepted := toCellEffect accepted context authorization

/-- On a canonical resource leg, the generic law is the exact
operation-selected post-book difference.  The law has no independent posting
or delta input. -/
theorem typedResourceLaw_delta_eq_operation
    {M : CellState.Materializer CanonicalResourceKernel.schema Digest}
    {pre : CellState.Materialized M} {operation : CanonicalResourceKernel.Operation}
    {portal : Portal} {authState : AuthState}
    (accepted : CanonicalResourceKernel.Accepted pre operation) (context : RequestContext)
    (authorization : Authorized portal authState (context.request pre operation))
    (asset : CanonicalResourceKernel.AssetId) :
    (typedResourceLaw M portal).delta
      (toTypedLeg accepted context authorization) asset =
      (operation.apply
        (CanonicalResourceKernel.logicalBook pre.logical)).totalAsset asset -
        (CanonicalResourceKernel.logicalBook pre.logical).totalAsset asset := by
  simp only [typedResourceLaw, Minidregg.Kernel.TypedCellHyperedge.ResourceLaw.delta,
    bookDelta, toTypedLeg,
    Minidregg.Kernel.TypedCellHyperedge.Leg.post]
  rw [toCellEffect_post_book]

@[simp] theorem typedResourceLaw_delta_toTypedLeg
    {M : CellState.Materializer CanonicalResourceKernel.schema Digest}
    {pre : CellState.Materialized M} {operation : CanonicalResourceKernel.Operation}
    {portal : Portal} {authState : AuthState}
    (accepted : CanonicalResourceKernel.Accepted pre operation) (context : RequestContext)
    (authorization : Authorized portal authState (context.request pre operation))
    (asset : CanonicalResourceKernel.AssetId) :
    (typedResourceLaw M portal).delta
      (toTypedLeg accepted context authorization) asset = 0 := by
  rw [typedResourceLaw_delta_eq_operation]
  exact sub_eq_zero.mpr <|
    operation.apply_conserves (CanonicalResourceKernel.logicalBook pre.logical)
      accepted.admission.sourcePresent accepted.admission.destinationPresent asset

/-- A fixed-schema `CellFamily` for genuinely distinct resource-book cells. -/
def resourceCells
    {Incidence : Type} (M : Incidence -> CellState.Materializer CanonicalResourceKernel.schema Digest)
    (portal : Incidence -> Portal)
    (projectAuthority : Incidence -> CellState.LogicalState CanonicalResourceKernel.schema -> AuthState)
    (cellId : Incidence -> Digest) : Minidregg.Kernel.MultiCellHyperedge.CellFamily Incidence where
  schema := fun _ => CanonicalResourceKernel.schema
  fieldDecidableEq := fun _ => schemaFieldDecidableEq
  resourceDecidableEq := fun _ => schemaResourceDecidableEq
  materializer := M
  portal := portal
  projectAuthority := projectAuthority
  cellId := cellId

local instance resourceCellsFieldDecidableEq
    {Incidence : Type}
    {M : Incidence -> CellState.Materializer CanonicalResourceKernel.schema Digest}
    {portal : Incidence -> Portal}
    {projectAuthority : Incidence -> CellState.LogicalState CanonicalResourceKernel.schema -> AuthState}
    {cellId : Incidence -> Digest} (incidence : Incidence) :
    DecidableEq
      ((resourceCells M portal projectAuthority cellId).schema incidence).Field := by
  change DecidableEq CanonicalResourceKernel.schema.Field
  exact schemaFieldDecidableEq

local instance resourceCellsResourceDecidableEq
    {Incidence : Type}
    {M : Incidence -> CellState.Materializer CanonicalResourceKernel.schema Digest}
    {portal : Incidence -> Portal}
    {projectAuthority : Incidence -> CellState.LogicalState CanonicalResourceKernel.schema -> AuthState}
    {cellId : Incidence -> Digest} (incidence : Incidence) :
    DecidableEq
      ((resourceCells M portal projectAuthority cellId).schema incidence).Resource := by
  change DecidableEq CanonicalResourceKernel.schema.Resource
  exact schemaResourceDecidableEq

/-- Multi-cell resource law, again computed only from each accepted incidence's
exact local post and exact local pre. -/
def multiCellResourceLaw
    {Incidence : Type}
    {M : Incidence -> CellState.Materializer CanonicalResourceKernel.schema Digest}
    {portal : Incidence -> Portal}
    {projectAuthority : Incidence -> CellState.LogicalState CanonicalResourceKernel.schema -> AuthState}
    {cellId : Incidence -> Digest}
    (declaration : Minidregg.Kernel.MultiCellHyperedge.Declaration
      (resourceCells M portal projectAuthority cellId)) :
    Minidregg.Kernel.MultiCellHyperedge.ResourceLaw declaration CanonicalResourceKernel.AssetId Int where
  delta := fun incidence accepted asset =>
    bookDelta (declaration.pre incidence).logical
      accepted.prepared.post.logical asset

@[simp] theorem multiCellResourceLaw_delta
    {Incidence : Type}
    {M : Incidence -> CellState.Materializer CanonicalResourceKernel.schema Digest}
    {portal : Incidence -> Portal}
    {projectAuthority : Incidence -> CellState.LogicalState CanonicalResourceKernel.schema -> AuthState}
    {cellId : Incidence -> Digest}
    (declaration : Minidregg.Kernel.MultiCellHyperedge.Declaration
      (resourceCells M portal projectAuthority cellId))
    (incidence : Incidence) (accepted : declaration.AcceptedLeg incidence)
    (asset : CanonicalResourceKernel.AssetId) :
    (multiCellResourceLaw declaration).delta incidence accepted asset =
      bookDelta (declaration.pre incidence).logical
        accepted.prepared.post.logical asset :=
  rfl

theorem multiCellResourceLaw_delta_eq_zero_of_conserves
    {Incidence : Type}
    {M : Incidence -> CellState.Materializer CanonicalResourceKernel.schema Digest}
    {portal : Incidence -> Portal}
    {projectAuthority : Incidence -> CellState.LogicalState CanonicalResourceKernel.schema -> AuthState}
    {cellId : Incidence -> Digest}
    (declaration : Minidregg.Kernel.MultiCellHyperedge.Declaration
      (resourceCells M portal projectAuthority cellId))
    (incidence : Incidence) (accepted : declaration.AcceptedLeg incidence)
    (asset : CanonicalResourceKernel.AssetId)
    (conserves :
      (CanonicalResourceKernel.logicalBook
        accepted.prepared.post.logical).totalAsset asset =
      (CanonicalResourceKernel.logicalBook
        (declaration.pre incidence).logical).totalAsset asset) :
    (multiCellResourceLaw declaration).delta incidence accepted asset = 0 := by
  rw [multiCellResourceLaw_delta]
  exact sub_eq_zero.mpr conserves

/-! ## Conservation and negative teeth survive the adapter -/

/-- The accepted path cannot install a positive credit-only mint.  This is a
post-state refutation, not merely the fact that `creditOnly` has no constructor
in `Operation`. -/
theorem no_creditOnly_post
    {M : CellState.Materializer CanonicalResourceKernel.schema Digest}
    {pre : CellState.Materialized M} {operation : CanonicalResourceKernel.Operation}
    {portal : Portal} {authState : AuthState}
    (accepted : CanonicalResourceKernel.Accepted pre operation) (context : RequestContext)
    (authorization : Authorized portal authState (context.request pre operation))
    (destination : CanonicalResourceKernel.AccountId) (asset : CanonicalResourceKernel.AssetId) (amount : Nat)
    (destinationPresent : destination ∈ (CanonicalResourceKernel.logicalBook pre.logical).accounts)
    (positive : 0 < amount) :
    CanonicalResourceKernel.logicalBook
      (toCellEffect accepted context authorization).prepared.post.logical ≠
      (CanonicalResourceKernel.logicalBook pre.logical).creditOnly destination asset amount := by
  intro samePost
  have sameTotal := congrArg (fun book : CanonicalResourceKernel.Book => book.totalAsset asset) samePost
  have conserved := toCellEffect_conserves accepted context authorization asset
  have creditBreaks := (CanonicalResourceKernel.logicalBook pre.logical).creditOnly_breaks_conservation
    destination asset amount destinationPresent positive
  apply creditBreaks
  rw [← conserved]
  exact sameTotal.symm

/-! ## Closed authority/effect witness -/

def witnessContext : RequestContext where
  domain := ⟨1⟩
  semantics := ⟨2⟩
  federation := ⟨3⟩
  subject := ⟨4⟩
  subjectKeyEpoch := 2
  nonce := 7
  height := 10
  policyId := ⟨9⟩
  policyEpoch := 5

noncomputable def witnessAuthorization :
    Authorized demoPortal demoState
      (witnessContext.request CanonicalResourceKernel.witnessCell (.mint 0 1 2)) where
  evidence := .signature () rfl rfl
  policyWitness := ()
  policyMembershipWitness := ()
  policyEpochExact := rfl
  policyAddressExact := rfl
  policyMembershipVerified := rfl
  policyVerified := rfl

/-- A deployed-schema, request-indexed, authorized resource effect is inhabited. -/
noncomputable def witnessCellEffect :
    AcceptedCellEffect (portal := demoPortal) (authState := demoState)
      (family CanonicalResourceKernel.witnessCell witnessContext)
      (witnessContext.request CanonicalResourceKernel.witnessCell (.mint 0 1 2))
      CanonicalResourceKernel.witnessCell (.mint 0 1 2) () :=
  toCellEffect CanonicalResourceKernel.witnessMintAccepted
    witnessContext witnessAuthorization

theorem witnessCellEffect_nonempty :
    Nonempty (AcceptedCellEffect (portal := demoPortal) (authState := demoState)
      (family CanonicalResourceKernel.witnessCell witnessContext)
      (witnessContext.request CanonicalResourceKernel.witnessCell (.mint 0 1 2))
      CanonicalResourceKernel.witnessCell (.mint 0 1 2) ()) :=
  ⟨witnessCellEffect⟩

noncomputable def witnessTypedLeg :
    Minidregg.Kernel.TypedCellHyperedge.Leg demoPortal demoState
      CanonicalResourceKernel.witnessCell :=
  toTypedLeg CanonicalResourceKernel.witnessMintAccepted
    witnessContext witnessAuthorization

example :
    (typedResourceLaw CanonicalResourceKernel.materializer demoPortal).delta
      witnessTypedLeg 0 = 0 := by
  exact typedResourceLaw_delta_toTypedLeg
    CanonicalResourceKernel.witnessMintAccepted witnessContext witnessAuthorization 0

example :
    (CanonicalResourceKernel.logicalBook witnessCellEffect.prepared.post.logical).balance 0 0 = -10 := by
  decide

example :
    (CanonicalResourceKernel.logicalBook witnessCellEffect.prepared.post.logical).totalAsset 0 = 0 := by
  simpa using toCellEffect_conserves CanonicalResourceKernel.witnessMintAccepted
    witnessContext witnessAuthorization 0

/-! ## Axiom pins -/

/-- info: 'Minidregg.Kernel.CanonicalResourceEffect.operation_eq_of_argsDigest_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms operation_eq_of_argsDigest_eq
/-- info: 'Minidregg.Kernel.CanonicalResourceEffect.toCellEffect_conserves' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms toCellEffect_conserves
/-- info: 'Minidregg.Kernel.CanonicalResourceEffect.typedResourceLaw_delta_toTypedLeg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms typedResourceLaw_delta_toTypedLeg
/-- info: 'Minidregg.Kernel.CanonicalResourceEffect.no_creditOnly_post' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms no_creditOnly_post
/-- info: 'Minidregg.Kernel.CanonicalResourceEffect.witnessCellEffect_nonempty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms witnessCellEffect_nonempty

end Minidregg.Kernel.CanonicalResourceEffect
