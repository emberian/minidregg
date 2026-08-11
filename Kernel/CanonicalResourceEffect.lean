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
import Theory.CanonicalResourceKernel

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

/-- A constructor-disjoint natural code for the complete resource operation. -/
def operationCode : CanonicalResourceKernel.Operation -> Nat
  | .transfer source destination asset amount =>
      Nat.pair 0 (Nat.pair source (Nat.pair destination (Nat.pair asset amount)))
  | .mint asset destination amount =>
      Nat.pair 1 (Nat.pair asset (Nat.pair destination amount))
  | .burn source asset amount =>
      Nat.pair 2 (Nat.pair source (Nat.pair asset amount))
  | .fee payer collector asset amount =>
      Nat.pair 3 (Nat.pair payer (Nat.pair collector (Nat.pair asset amount)))
  | .lease leaseId holder lessor asset rate epochs startsAt =>
      Nat.pair 4
        (Nat.pair leaseId
          (Nat.pair holder
            (Nat.pair lessor
              (Nat.pair asset (Nat.pair rate (Nat.pair epochs startsAt))))))

/-- Partial inverse of `operationCode`; codes with unknown constructor tags
are rejected. -/
def operationOfCode (code : Nat) : Option CanonicalResourceKernel.Operation :=
  let tagged := Nat.unpair code
  match tagged.1 with
  | 0 =>
      let sourceRest := Nat.unpair tagged.2
      let destinationRest := Nat.unpair sourceRest.2
      let assetAmount := Nat.unpair destinationRest.2
      some (.transfer sourceRest.1 destinationRest.1 assetAmount.1 assetAmount.2)
  | 1 =>
      let assetRest := Nat.unpair tagged.2
      let destinationAmount := Nat.unpair assetRest.2
      some (.mint assetRest.1 destinationAmount.1 destinationAmount.2)
  | 2 =>
      let sourceRest := Nat.unpair tagged.2
      let assetAmount := Nat.unpair sourceRest.2
      some (.burn sourceRest.1 assetAmount.1 assetAmount.2)
  | 3 =>
      let payerRest := Nat.unpair tagged.2
      let collectorRest := Nat.unpair payerRest.2
      let assetAmount := Nat.unpair collectorRest.2
      some (.fee payerRest.1 collectorRest.1 assetAmount.1 assetAmount.2)
  | 4 =>
      let leaseRest := Nat.unpair tagged.2
      let holderRest := Nat.unpair leaseRest.2
      let lessorRest := Nat.unpair holderRest.2
      let assetRest := Nat.unpair lessorRest.2
      let rateRest := Nat.unpair assetRest.2
      let epochsStarts := Nat.unpair rateRest.2
      some (.lease leaseRest.1 holderRest.1 lessorRest.1 assetRest.1
        rateRest.1 epochsStarts.1 epochsStarts.2)
  | _ => none

@[simp] theorem operationOfCode_operationCode (operation : CanonicalResourceKernel.Operation) :
    operationOfCode (operationCode operation) = some operation := by
  cases operation <;> simp [operationCode, operationOfCode]

/-- Unary is deliberately used only as a proof-auditable canonical codec for
this bounded model.  A deployment should replace it with a compact audited
wire encoding while preserving the same round-trip theorem. -/
def operationCodec : LawfulCodec CanonicalResourceKernel.Operation where
  encode := fun operation => List.replicate (operationCode operation + 1) 0
  decode := fun bytes => operationOfCode (bytes.length - 1)
  decode_encode := by
    intro operation
    simp [operationOfCode_operationCode]

/-- The exact conserved posting also has its own lawful first-order encoding. -/
def postingCode (posting : CanonicalResourceKernel.Posting) : Nat :=
  Nat.pair posting.source
    (Nat.pair posting.destination (Nat.pair posting.asset posting.amount))

def postingOfCode (code : Nat) : CanonicalResourceKernel.Posting :=
  let sourceRest := Nat.unpair code
  let destinationRest := Nat.unpair sourceRest.2
  let assetAmount := Nat.unpair destinationRest.2
  { source := sourceRest.1
    destination := destinationRest.1
    asset := assetAmount.1
    amount := assetAmount.2 }

@[simp] theorem postingOfCode_postingCode (posting : CanonicalResourceKernel.Posting) :
    postingOfCode (postingCode posting) = posting := by
  cases posting
  simp [postingCode, postingOfCode]

def postingCodec : LawfulCodec CanonicalResourceKernel.Posting where
  encode := fun posting => List.replicate (postingCode posting + 1) 0
  decode := fun bytes => some (postingOfCode (bytes.length - 1))
  decode_encode := by
    intro posting
    simp [postingOfCode_postingCode]

/-- Domain-separated unary-code commitment.  `Digest` is an exact model-level
natural carrier here, not a claim that pairing is a production hash. -/
def digestBytes (domain : Nat) (bytes : List UInt8) : Digest :=
  ⟨Nat.pair domain bytes.length⟩

def argsDigest (operation : CanonicalResourceKernel.Operation) : Digest :=
  digestBytes 0 (operationCodec.encode operation)

def resourceDigest (operation : CanonicalResourceKernel.Operation) : Digest :=
  digestBytes 1 (postingCodec.encode operation.posting)

/-- The effect commitment binds both the complete operation and the exact
balanced posting selected by that operation. -/
def effectDigest (operation : CanonicalResourceKernel.Operation) : Digest :=
  ⟨Nat.pair (argsDigest operation).value (resourceDigest operation).value⟩

theorem operationCode_injective : Function.Injective operationCode := by
  intro left right same
  have decoded := congrArg operationOfCode same
  simpa using decoded

theorem argsDigest_injective : Function.Injective argsDigest := by
  intro left right same
  apply operationCode_injective
  have values := congrArg Digest.value same
  have paired :
      Nat.pair 0 (operationCode left + 1) =
        Nat.pair 0 (operationCode right + 1) := by
    simpa [argsDigest, digestBytes, operationCodec] using values
  have lengths : operationCode left + 1 = operationCode right + 1 := by
    exact (Nat.pair_eq_pair.mp paired).2
  omega

theorem effectDigest_injective : Function.Injective effectDigest := by
  intro left right same
  have values := congrArg Digest.value same
  have paired :
      Nat.pair (argsDigest left).value (resourceDigest left).value =
        Nat.pair (argsDigest right).value (resourceDigest right).value := by
    simpa [effectDigest] using values
  apply argsDigest_injective
  cases leftDigest : argsDigest left with
  | mk leftValue =>
      cases rightDigest : argsDigest right with
      | mk rightValue =>
          have sameValue : leftValue = rightValue := by
            simpa [leftDigest, rightDigest] using
              (Nat.pair_eq_pair.mp paired).1
          cases sameValue
          rfl

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
  decode := fun _ => some ()
  decode_encode := fun _ => rfl

/-! ## The canonical accepted-effect family -/

/-- The family is indexed by the exact canonical pre-cell because applying a
posting reads the current book.  Its declaration remains first-order: only the
operation crosses the boundary, while the family closes over trusted state. -/
def family
    {M : CellState.Materializer CanonicalResourceKernel.schema Digest}
    (pre : CellState.Materialized M) :
    SemanticEffectFamily.{0, 0, 0, 0, 0, 0} CanonicalResourceKernel.schema M Unit where
  Declaration := CanonicalResourceKernel.Operation
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
noncomputable def toCellEffect
    {M : CellState.Materializer CanonicalResourceKernel.schema Digest}
    {pre : CellState.Materialized M} {operation : CanonicalResourceKernel.Operation}
    {portal : Portal} {authState : AuthState}
    (accepted : CanonicalResourceKernel.Accepted pre operation) (context : RequestContext)
    (authorization : Authorized portal authState (context.request pre operation)) :
    AcceptedCellEffect (portal := portal) (authState := authState)
      (family pre) (context.request pre operation) pre operation () where
  authorization := authorization
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
  delta := fun {_} {pre} leg asset =>
    bookDelta pre.logical leg.post.logical asset

/-- Package the canonical accepted resource effect as one typed-hyperedge leg. -/
noncomputable def toTypedLeg
    {M : CellState.Materializer CanonicalResourceKernel.schema Digest}
    {pre : CellState.Materialized M} {operation : CanonicalResourceKernel.Operation}
    {portal : Portal} {authState : AuthState}
    (accepted : CanonicalResourceKernel.Accepted pre operation) (context : RequestContext)
    (authorization : Authorized portal authState (context.request pre operation)) :
    Minidregg.Kernel.TypedCellHyperedge.Leg portal authState pre where
  Nullifier := Unit
  family := family pre
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
  simp only [typedResourceLaw, bookDelta, toTypedLeg,
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
      (family CanonicalResourceKernel.witnessCell)
      (witnessContext.request CanonicalResourceKernel.witnessCell (.mint 0 1 2))
      CanonicalResourceKernel.witnessCell (.mint 0 1 2) () :=
  toCellEffect CanonicalResourceKernel.witnessMintAccepted
    witnessContext witnessAuthorization

theorem witnessCellEffect_nonempty :
    Nonempty (AcceptedCellEffect (portal := demoPortal) (authState := demoState)
      (family CanonicalResourceKernel.witnessCell)
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

/-- info: 'Minidregg.Kernel.CanonicalResourceEffect.operationOfCode_operationCode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms operationOfCode_operationCode
/-- info: 'Minidregg.Kernel.CanonicalResourceEffect.effectDigest_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms effectDigest_injective
/-- info: 'Minidregg.Kernel.CanonicalResourceEffect.toCellEffect_conserves' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms toCellEffect_conserves
/-- info: 'Minidregg.Kernel.CanonicalResourceEffect.typedResourceLaw_delta_toTypedLeg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms typedResourceLaw_delta_toTypedLeg
/-- info: 'Minidregg.Kernel.CanonicalResourceEffect.no_creditOnly_post' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms no_creditOnly_post
/-- info: 'Minidregg.Kernel.CanonicalResourceEffect.witnessCellEffect_nonempty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms witnessCellEffect_nonempty

end Minidregg.Kernel.CanonicalResourceEffect
