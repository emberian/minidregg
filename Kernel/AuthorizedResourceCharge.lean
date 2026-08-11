/-
# Kernel.AuthorizedResourceCharge -- bind authority to ten-lane settlement cost

`TypedAuthorization.Request.cost` is a scalar authority ceiling, while durable
settlement debits the ten independent lanes of `ResourceCost.Charge`.  Leaving
their relationship to a handler permits a request authorized at one price to
be settled with an inflated or lane-swapped vector.

This module closes that seam for the canonical resource kernel.  A first-order
deployment manifest commits the state/operation/event codec identities and the
complete tariff.  The exact charge is then a Lean function of that manifest,
the accepted operation, its exact patch footprint, and its canonical pre/post
bytes.  The authorization request takes its semantics digest and scalar cost
from that same derivation, and the durable data intent installs the exact post
bytes with the very same ten-lane vector.

The manifest identifies deployed codecs; it does not prove that a native
binary implements those codecs or that the model-level `Digest` is
collision-resistant.  Those remain explicit deployment/refinement premises.
-/
import Kernel.AdmissionPrologue
import Kernel.CanonicalResourceEffect

namespace Minidregg.Kernel.AuthorizedResourceCharge

open Minidregg.Theory
open Minidregg.Theory.CellState
open Minidregg.Theory.IndexedProgram
open Minidregg.Theory.ResourceCost
open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.CanonicalResourceKernel
open Minidregg.Kernel.DurableDataIntent

set_option autoImplicit false

local instance schemaFieldDecidableEq :
    DecidableEq CanonicalResourceKernel.schema.Field := by
  change DecidableEq CanonicalResourceKernel.Field
  infer_instance

local instance schemaResourceDecidableEq :
    DecidableEq CanonicalResourceKernel.schema.Resource := by
  change DecidableEq Empty
  infer_instance

/-! ## First-order deployment and tariff commitment -/

/-- The finite operational tariff.  `unitFee` does not recursively price the
`feeDebit` or `leaseByteBlocks` lanes; those two coordinates are derived after
all operational coordinates have been fixed. -/
structure Tariff where
  authorizationWitnessBytes : Nat
  baseProofWork : Nat
  proofWorkPerTouch : Nat
  networkCopies : Nat
  leaseEpochs : Nat
  unitFee : Charge

/-- Every native codec is named explicitly.  The manifest digest below commits
these identifiers and every tariff coordinate.  Mapping the identifiers to
audited native encoders is deliberately a deployment refinement obligation. -/
structure DeploymentManifest where
  version : Nat
  stateCodecId : Digest
  operationCodecId : Digest
  eventCodecId : Digest
  tariff : Tariff

/-- Closed encoding of all ten lanes. -/
def chargeCode (charge : Charge) : Nat :=
  Nat.pair (charge .incidences)
    (Nat.pair (charge .turnBytes)
      (Nat.pair (charge .memoryTouches)
        (Nat.pair (charge .witnessBytes)
          (Nat.pair (charge .proofWork)
            (Nat.pair (charge .storageBytes)
              (Nat.pair (charge .networkBytes)
                (Nat.pair (charge .sideEffectCount)
                  (Nat.pair (charge .feeDebit)
                    (charge .leaseByteBlocks)))))))))

theorem chargeCode_injective : Function.Injective chargeCode := by
  intro left right same
  simp only [chargeCode, Nat.pair_eq_pair] at same
  funext lane
  cases lane <;> simp_all

def Tariff.code (tariff : Tariff) : Nat :=
  Nat.pair tariff.authorizationWitnessBytes
    (Nat.pair tariff.baseProofWork
      (Nat.pair tariff.proofWorkPerTouch
        (Nat.pair tariff.networkCopies
          (Nat.pair tariff.leaseEpochs (chargeCode tariff.unitFee)))))

theorem Tariff.code_injective : Function.Injective Tariff.code := by
  rintro ⟨leftWitness, leftBase, leftPerTouch, leftCopies, leftLease, leftFee⟩
    ⟨rightWitness, rightBase, rightPerTouch, rightCopies, rightLease, rightFee⟩ same
  simp only [Tariff.code, Nat.pair_eq_pair] at same
  have fee : leftFee = rightFee := chargeCode_injective same.2.2.2.2.2
  cases same.1
  cases same.2.1
  cases same.2.2.1
  cases same.2.2.2.1
  cases same.2.2.2.2.1
  cases fee
  rfl

def DeploymentManifest.code (manifest : DeploymentManifest) : Nat :=
  Nat.pair manifest.version
    (Nat.pair manifest.stateCodecId.value
      (Nat.pair manifest.operationCodecId.value
        (Nat.pair manifest.eventCodecId.value manifest.tariff.code)))

theorem DeploymentManifest.code_injective :
    Function.Injective DeploymentManifest.code := by
  rintro ⟨leftVersion, leftState, leftOperation, leftEvent, leftTariff⟩
    ⟨rightVersion, rightState, rightOperation, rightEvent, rightTariff⟩ same
  simp only [DeploymentManifest.code, Nat.pair_eq_pair] at same
  have tariff : leftTariff = rightTariff := Tariff.code_injective same.2.2.2.2
  have state : leftState = rightState := by
    cases leftState
    cases rightState
    simp_all
  have operation : leftOperation = rightOperation := by
    cases leftOperation
    cases rightOperation
    simp_all
  have event : leftEvent = rightEvent := by
    cases leftEvent
    cases rightEvent
    simp_all
  cases same.1
  cases state
  cases operation
  cases event
  cases tariff
  rfl

/-- The request's semantic identifier is definitionally derived from the exact
codec/tariff manifest, rather than supplied independently by its caller. -/
def DeploymentManifest.semanticDigest (manifest : DeploymentManifest) : Digest :=
  ⟨Nat.pair 7919 manifest.code⟩

theorem DeploymentManifest.semanticDigest_injective :
    Function.Injective DeploymentManifest.semanticDigest := by
  intro left right same
  apply DeploymentManifest.code_injective
  have values : Nat.pair 7919 left.code = Nat.pair 7919 right.code := by
    simpa [DeploymentManifest.semanticDigest] using congrArg Digest.value same
  exact (Nat.pair_eq_pair.mp values).2

/-! ## Exact accepted-effect charge -/

/-- Canonical post selected by the operation patch itself.  This is the same
value as `Accepted.post`; validation proofs cannot affect it. -/
def canonicalPost
    {M : Materializer CanonicalResourceKernel.schema Digest}
    (pre : Materialized M) (operation : Operation) : Materialized M :=
  materialize M
    { fields := applyFieldWrites (operation.patch pre).fieldWrites pre.logical.fields
      resources := applyResourceWrites (operation.patch pre).resourceWrites
        pre.logical.resources }

@[simp] theorem accepted_post_eq_canonical
    {M : Materializer CanonicalResourceKernel.schema Digest}
    {pre : Materialized M} {operation : Operation}
    (accepted : Accepted pre operation) :
    accepted.post = canonicalPost pre operation :=
  rfl

/-- Exact footprint cardinality of the accepted canonical patch. -/
def memoryTouches
    {M : Materializer CanonicalResourceKernel.schema Digest}
    {pre : Materialized M} {operation : Operation}
    (_accepted : Accepted pre operation) : Nat :=
  (operation.patch pre).fieldFootprint.card +
    (operation.patch pre).resourceFootprint.card

/-- Operational coordinates are fixed before fee and lease pricing.  Byte
counts come from the lawful operation codec and the exact canonical pre/post
state codecs; no executor counter enters this definition. -/
def operationalChargeOf
    {M : Materializer CanonicalResourceKernel.schema Digest}
    (manifest : DeploymentManifest) (pre : Materialized M)
    (operation : Operation) : Charge
  | .incidences => 1
  | .turnBytes =>
      (CanonicalResourceEffect.operationCodec.encode operation).length +
        pre.bytes.length + (canonicalPost pre operation).bytes.length
  | .memoryTouches =>
      (operation.patch pre).fieldFootprint.card +
        (operation.patch pre).resourceFootprint.card
  | .witnessBytes => manifest.tariff.authorizationWitnessBytes
  | .proofWork => manifest.tariff.baseProofWork +
      manifest.tariff.proofWorkPerTouch *
        ((operation.patch pre).fieldFootprint.card +
          (operation.patch pre).resourceFootprint.card)
  | .storageBytes =>
      (canonicalPost pre operation).bytes.length +
        (CanonicalResourceEffect.operationCodec.encode operation).length
  | .networkBytes => manifest.tariff.networkCopies *
      ((CanonicalResourceEffect.operationCodec.encode operation).length +
        (canonicalPost pre operation).bytes.length)
  | .sideEffectCount => 2 -- one canonical write and one receipt append
  | .feeDebit => 0
  | .leaseByteBlocks => 0

def operationalCharge
    {M : Materializer CanonicalResourceKernel.schema Digest}
    {pre : Materialized M} {operation : Operation}
    (manifest : DeploymentManifest) (_accepted : Accepted pre operation) : Charge :=
  operationalChargeOf manifest pre operation

@[simp] theorem operationalCharge_memoryTouches
    {M : Materializer CanonicalResourceKernel.schema Digest}
    {pre : Materialized M} {operation : Operation}
    (manifest : DeploymentManifest) (accepted : Accepted pre operation) :
    operationalCharge manifest accepted .memoryTouches = memoryTouches accepted :=
  rfl

/-- Pricing excludes the two derived lanes and is therefore non-recursive. -/
def Tariff.billable (tariff : Tariff) (charge : Charge) : Nat :=
  charge .incidences * tariff.unitFee .incidences +
  charge .turnBytes * tariff.unitFee .turnBytes +
  charge .memoryTouches * tariff.unitFee .memoryTouches +
  charge .witnessBytes * tariff.unitFee .witnessBytes +
  charge .proofWork * tariff.unitFee .proofWork +
  charge .storageBytes * tariff.unitFee .storageBytes +
  charge .networkBytes * tariff.unitFee .networkBytes +
  charge .sideEffectCount * tariff.unitFee .sideEffectCount

/-- The sole exact ten-lane settlement vector. -/
def exactChargeOf
    {M : Materializer CanonicalResourceKernel.schema Digest}
    (manifest : DeploymentManifest) (pre : Materialized M)
    (operation : Operation) : Charge
  | .feeDebit => manifest.tariff.billable (operationalChargeOf manifest pre operation)
  | .leaseByteBlocks =>
      operationalChargeOf manifest pre operation .storageBytes * manifest.tariff.leaseEpochs
  | lane => operationalChargeOf manifest pre operation lane

def exactCharge
    {M : Materializer CanonicalResourceKernel.schema Digest}
    {pre : Materialized M} {operation : Operation}
    (manifest : DeploymentManifest) (_accepted : Accepted pre operation) : Charge :=
  exactChargeOf manifest pre operation

@[simp] theorem exactCharge_feeDebit
    {M : Materializer CanonicalResourceKernel.schema Digest}
    {pre : Materialized M} {operation : Operation}
    (manifest : DeploymentManifest) (accepted : Accepted pre operation) :
    exactCharge manifest accepted .feeDebit =
      manifest.tariff.billable (operationalCharge manifest accepted) :=
  rfl

@[simp] theorem exactCharge_leaseByteBlocks
    {M : Materializer CanonicalResourceKernel.schema Digest}
    {pre : Materialized M} {operation : Operation}
    (manifest : DeploymentManifest) (accepted : Accepted pre operation) :
    exactCharge manifest accepted .leaseByteBlocks =
      exactCharge manifest accepted .storageBytes * manifest.tariff.leaseEpochs :=
  rfl

/-- The effect commitment contains the complete operation commitment and all
ten exact charge coordinates. -/
def effectDigestWithCharge (operation : Operation) (charge : Charge) : Digest :=
  ⟨Nat.pair (CanonicalResourceEffect.effectDigest operation).value
    (chargeCode charge)⟩

def chargedEffectDigest
    {M : Materializer CanonicalResourceKernel.schema Digest}
    (manifest : DeploymentManifest) (pre : Materialized M)
    (operation : Operation) : Digest :=
  effectDigestWithCharge operation (exactChargeOf manifest pre operation)

theorem effectDigestWithCharge_charge_injective (operation : Operation) :
    Function.Injective (effectDigestWithCharge operation) := by
  intro left right same
  apply chargeCode_injective
  have values :
      Nat.pair (CanonicalResourceEffect.effectDigest operation).value
          (chargeCode left) =
        Nat.pair (CanonicalResourceEffect.effectDigest operation).value
          (chargeCode right) := by
    simpa [effectDigestWithCharge] using congrArg Digest.value same
  exact (Nat.pair_eq_pair.mp values).2

/-- This family differs from the legacy resource adapter in one load-bearing
way: its effect digest includes the exact ten-lane settlement charge. -/
def family
    {M : Materializer CanonicalResourceKernel.schema Digest}
    (manifest : DeploymentManifest) (pre : Materialized M) :
    SemanticEffectFamily.{0, 0, 0, 0, 0, 0}
      CanonicalResourceKernel.schema M Unit where
  Declaration := Operation
  declarationCodec := CanonicalResourceEffect.operationCodec
  Outcome := fun _ => Unit
  outcomeCodec := fun _ => CanonicalResourceEffect.unitCodec
  ModeEvidence := fun operation _ =>
    PLift (Admission (logicalBook pre.logical) operation)
  effectDigest := chargedEffectDigest manifest pre
  patch := fun operation _ => operation.patch pre
  nullifier := fun _ _ => none
  Release := fun _ _ => PEmpty
  DeclassificationAuthority := fun _ _ => PEmpty
  ReleaseAuthorization := fun _ _ release => release.elim
  DisclosureAllowed := fun _ _ disclosure => disclosure = .sealed

/-! ## One authorization request and one durable payload -/

/-- Ambient request fields only.  Notably, neither a semantics digest nor a
cost is caller input. -/
structure RequestContext where
  domain : Digest
  federation : FederationId
  subject : SubjectId
  subjectKeyEpoch : TypedAuthorization.Epoch
  nonce : Nat
  height : Height
  policyId : PolicyId
  policyEpoch : TypedAuthorization.Epoch

/-- The exact request authorized for this accepted effect.  Its scalar cost is
the fee coordinate of the same vector later placed in durable settlement. -/
def RequestContext.request
    {M : Materializer CanonicalResourceKernel.schema Digest}
    {pre : Materialized M} {operation : Operation}
    (context : RequestContext) (manifest : DeploymentManifest)
    (accepted : Accepted pre operation) : Request .account where
  domain := context.domain
  semantics := manifest.semanticDigest
  federation := context.federation
  subject := context.subject
  subjectKeyEpoch := context.subjectKeyEpoch
  target := ⟨operation.posting.source⟩
  verb := .transfer
  argsDigest := CanonicalResourceEffect.argsDigest operation
  effectsDigest := chargedEffectDigest manifest pre operation
  nonce := context.nonce
  height := context.height
  preStateRoot := pre.root
  policyId := context.policyId
  policyEpoch := context.policyEpoch
  cost := exactCharge manifest accepted .feeDebit

@[simp] theorem RequestContext.request_semantics
    {M : Materializer CanonicalResourceKernel.schema Digest}
    {pre : Materialized M} {operation : Operation}
    (context : RequestContext) (manifest : DeploymentManifest)
    (accepted : Accepted pre operation) :
    (context.request manifest accepted).semantics = manifest.semanticDigest :=
  rfl

@[simp] theorem RequestContext.request_cost
    {M : Materializer CanonicalResourceKernel.schema Digest}
    {pre : Materialized M} {operation : Operation}
    (context : RequestContext) (manifest : DeploymentManifest)
    (accepted : Accepted pre operation) :
    (context.request manifest accepted).cost =
      exactCharge manifest accepted .feeDebit :=
  rfl

@[simp] theorem RequestContext.request_effectsDigest
    {M : Materializer CanonicalResourceKernel.schema Digest}
    {pre : Materialized M} {operation : Operation}
    (context : RequestContext) (manifest : DeploymentManifest)
    (accepted : Accepted pre operation) :
    (context.request manifest accepted).effectsDigest =
      effectDigestWithCharge operation (exactCharge manifest accepted) :=
  rfl

/-- Resource acceptance enters the common accepted-effect path under authority
for the tariff-derived request. -/
noncomputable def toCellEffect
    {M : Materializer CanonicalResourceKernel.schema Digest}
    {pre : Materialized M} {operation : Operation}
    {portal : Portal} {authState : AuthState}
    (manifest : DeploymentManifest) (accepted : Accepted pre operation)
    (context : RequestContext)
    (authorization : Authorized portal authState
      (context.request manifest accepted)) :
    AcceptedCellEffect (portal := portal) (authState := authState)
      (family manifest pre)
      (context.request manifest accepted) pre operation () where
  authorization := authorization
  effectsDigestBound := rfl
  preRootBound := rfl
  modeEvidence := PLift.up accepted.admission
  validated := accepted.validated
  disclosure := .sealed
  disclosureAllowed := rfl

/-- Stable receipt payload.  Its domain commits the deployment manifest and
its event id commits the complete canonical resource operation. -/
def stableEvent
    {M : Materializer CanonicalResourceKernel.schema Digest}
    {pre : Materialized M} {operation : Operation}
    (manifest : DeploymentManifest) (_accepted : Accepted pre operation) : StableEvent where
  codecVersion := manifest.version
  domain := manifest.semanticDigest
  eventId := chargedEffectDigest manifest pre operation
  canonicalBytes := CanonicalResourceEffect.operationCodec.encode operation

/-- Ordinary all-or-nothing durable settlement.  The post image is precisely
the canonical bytes of the accepted post and the charge is definitionally the
same vector whose fee coordinate was authorized. -/
def durableIntent
    {M : Materializer CanonicalResourceKernel.schema Digest}
    {pre : Materialized M} {operation : Operation}
    (transactionId cellId : Digest) (manifest : DeploymentManifest)
    (accepted : Accepted pre operation) : DataIntent M.rootBytes where
  transactionId := transactionId
  writes :=
    [{ cellId := cellId
       expectedPre := pre.root
       exactPost := accepted.post.root
       canonicalPostBytes := accepted.post.bytes }]
  readGuards := []
  nullifiers := []
  exactCharge := exactCharge manifest accepted
  event := stableEvent manifest accepted
  postRootsBound := by
    intro write present
    simp only [List.mem_singleton] at present
    subst write
    rfl
  guardsReadOnly := by simp

@[simp] theorem durableIntent_exactCharge
    {M : Materializer CanonicalResourceKernel.schema Digest}
    {pre : Materialized M} {operation : Operation}
    (transactionId cellId : Digest) (manifest : DeploymentManifest)
    (accepted : Accepted pre operation) :
    (durableIntent transactionId cellId manifest accepted).exactCharge =
      exactCharge manifest accepted :=
  rfl

@[simp] theorem request_cost_eq_durable_fee
    {M : Materializer CanonicalResourceKernel.schema Digest}
    {pre : Materialized M} {operation : Operation}
    (transactionId cellId : Digest) (context : RequestContext)
    (manifest : DeploymentManifest) (accepted : Accepted pre operation) :
    (context.request manifest accepted).cost =
      (durableIntent transactionId cellId manifest accepted).exactCharge .feeDebit :=
  rfl

/-! ## Fee-first admission split -/

/-- The fee/replay prologue owns exactly the authorized scalar debit. -/
def admissionCharge
    {M : Materializer CanonicalResourceKernel.schema Digest}
    {pre : Materialized M} {operation : Operation}
    (manifest : DeploymentManifest) (accepted : Accepted pre operation) : Charge :=
  fun lane => if lane = .feeDebit then exactCharge manifest accepted lane else 0

/-- The body owns every non-fee lane and cannot charge admission a second time. -/
def bodyCharge
    {M : Materializer CanonicalResourceKernel.schema Digest}
    {pre : Materialized M} {operation : Operation}
    (manifest : DeploymentManifest) (accepted : Accepted pre operation) : Charge :=
  fun lane => if lane = .feeDebit then 0 else exactCharge manifest accepted lane

@[simp] theorem admissionCharge_feeDebit
    {M : Materializer CanonicalResourceKernel.schema Digest}
    {pre : Materialized M} {operation : Operation}
    (manifest : DeploymentManifest) (accepted : Accepted pre operation) :
    admissionCharge manifest accepted .feeDebit =
      exactCharge manifest accepted .feeDebit := by
  simp [admissionCharge]

@[simp] theorem bodyCharge_feeDebit
    {M : Materializer CanonicalResourceKernel.schema Digest}
    {pre : Materialized M} {operation : Operation}
    (manifest : DeploymentManifest) (accepted : Accepted pre operation) :
    bodyCharge manifest accepted .feeDebit = 0 := by
  simp [bodyCharge]

theorem admission_add_body_exact
    {M : Materializer CanonicalResourceKernel.schema Digest}
    {pre : Materialized M} {operation : Operation}
    (manifest : DeploymentManifest) (accepted : Accepted pre operation) :
    admissionCharge manifest accepted + bodyCharge manifest accepted =
      exactCharge manifest accepted := by
  funext lane
  by_cases fee : lane = .feeDebit
  · subst fee
    simp
  · simp [admissionCharge, bodyCharge, fee]

/-- The canonical durable body for `AdmissionPrologue`: identical roots,
bytes, and event, but with the fee lane removed because the prologue has
already settled that exact authorized debit. -/
def admissionBodyIntent
    {M : Materializer CanonicalResourceKernel.schema Digest}
    {pre : Materialized M} {operation : Operation}
    (transactionId cellId : Digest) (manifest : DeploymentManifest)
    (accepted : Accepted pre operation) : DataIntent M.rootBytes :=
  { durableIntent transactionId cellId manifest accepted with
      exactCharge := bodyCharge manifest accepted }

@[simp] theorem admissionBodyIntent_no_second_fee
    {M : Materializer CanonicalResourceKernel.schema Digest}
    {pre : Materialized M} {operation : Operation}
    (transactionId cellId : Digest) (manifest : DeploymentManifest)
    (accepted : Accepted pre operation) :
    (admissionBodyIntent transactionId cellId manifest accepted).exactCharge .feeDebit = 0 :=
  bodyCharge_feeDebit manifest accepted

/-- Exact compatibility with the existing fee-first protocol.  This theorem
does not manufacture a fee-account payload: a deployment supplies an actual
well-formed prologue intent, then proves that its charge is precisely the
derived fee projection and that its body is the canonical charged body above.
Those premises make the authorized scalar, prologue debit, zero-fee body, and
recombined ten-lane charge agree. -/
theorem admissionPrologue_exact_split
    {M : Materializer CanonicalResourceKernel.schema Digest}
    {pre : Materialized M} {operation : Operation}
    (transactionId cellId : Digest) (context : RequestContext)
    (manifest : DeploymentManifest) (accepted : Accepted pre operation)
    (admission : AdmissionPrologue.Request M.rootBytes)
    (wellFormed : admission.WellFormed)
    (prologueExact : admission.prologue.exactCharge =
      admissionCharge manifest accepted)
    (bodyExact : admission.body =
      admissionBodyIntent transactionId cellId manifest accepted) :
    (context.request manifest accepted).cost =
        admission.prologue.exactCharge .feeDebit /\
      admission.body.exactCharge .feeDebit = 0 /\
      admission.prologue.exactCharge + admission.body.exactCharge =
        exactCharge manifest accepted := by
  constructor
  · rw [prologueExact]
    rfl
  constructor
  · exact wellFormed.bodyChargesNoAdmissionFee
  · rw [prologueExact, bodyExact]
    exact admission_add_body_exact manifest accepted

/-! ## Inflation and lane-swap teeth -/

def inflateLane (charge : Charge) (lane : Lane) (increment : Nat) : Charge :=
  fun queried => if queried = lane then charge queried + increment else charge queried

theorem inflated_charge_rejected
    {M : Materializer CanonicalResourceKernel.schema Digest}
    {pre : Materialized M} {operation : Operation}
    (transactionId cellId : Digest) (manifest : DeploymentManifest)
    (accepted : Accepted pre operation) (lane : Lane) (increment : Nat)
    (positive : 0 < increment) :
    inflateLane (exactCharge manifest accepted) lane increment ≠
      (durableIntent transactionId cellId manifest accepted).exactCharge := by
  intro same
  have atLane := congrFun same lane
  simp [inflateLane] at atLane
  omega

/-- Inflation cannot retain the effect digest already authorized by the
request, even if the scalar fee coordinate itself was not the modified lane. -/
theorem inflated_charge_changes_authorized_effectDigest
    {M : Materializer CanonicalResourceKernel.schema Digest}
    {pre : Materialized M} {operation : Operation}
    (context : RequestContext) (manifest : DeploymentManifest)
    (accepted : Accepted pre operation) (lane : Lane) (increment : Nat)
    (positive : 0 < increment) :
    effectDigestWithCharge operation
        (inflateLane (exactCharge manifest accepted) lane increment) ≠
      (context.request manifest accepted).effectsDigest := by
  intro same
  have charges := effectDigestWithCharge_charge_injective operation same
  change inflateLane (exactCharge manifest accepted) lane increment =
    exactCharge manifest accepted at charges
  have atLane := congrFun charges lane
  simp [inflateLane] at atLane
  omega

def swapLanes (charge : Charge) (left right : Lane) : Charge :=
  fun lane =>
    if lane = left then charge right
    else if lane = right then charge left
    else charge lane

theorem swapped_charge_rejected
    {M : Materializer CanonicalResourceKernel.schema Digest}
    {pre : Materialized M} {operation : Operation}
    (transactionId cellId : Digest) (manifest : DeploymentManifest)
    (accepted : Accepted pre operation) (left right : Lane)
    (different : exactCharge manifest accepted left ≠
      exactCharge manifest accepted right) :
    swapLanes (exactCharge manifest accepted) left right ≠
      (durableIntent transactionId cellId manifest accepted).exactCharge := by
  intro same
  have atLeft := congrFun same left
  by_cases sameLane : left = right
  · subst sameLane
    exact different rfl
  · simp [swapLanes] at atLeft
    exact different atLeft.symm

/-- Swapping two distinguishable lanes likewise changes the effect digest
named by authorization. -/
theorem swapped_charge_changes_authorized_effectDigest
    {M : Materializer CanonicalResourceKernel.schema Digest}
    {pre : Materialized M} {operation : Operation}
    (context : RequestContext) (manifest : DeploymentManifest)
    (accepted : Accepted pre operation) (left right : Lane)
    (different : exactCharge manifest accepted left ≠
      exactCharge manifest accepted right) :
    effectDigestWithCharge operation
        (swapLanes (exactCharge manifest accepted) left right) ≠
      (context.request manifest accepted).effectsDigest := by
  intro same
  have charges := effectDigestWithCharge_charge_injective operation same
  change swapLanes (exactCharge manifest accepted) left right =
    exactCharge manifest accepted at charges
  have atLeft := congrFun charges left
  by_cases sameLane : left = right
  · subst sameLane
    exact different rfl
  · simp [swapLanes] at atLeft
    exact different atLeft.symm

/-- A different codec/tariff manifest cannot preserve the semantic identifier
that authorization signed. -/
theorem different_manifest_changes_request_semantics
    {M : Materializer CanonicalResourceKernel.schema Digest}
    {pre : Materialized M} {operation : Operation}
    (context : RequestContext) (accepted : Accepted pre operation)
    (left right : DeploymentManifest) (different : left ≠ right) :
    (context.request left accepted).semantics ≠
      (context.request right accepted).semantics := by
  intro same
  exact different (DeploymentManifest.semanticDigest_injective same)

/-! ## Closed positive witness -/

def witnessUnitFee : Charge
  | .incidences => 3
  | _ => 0

def witnessManifest : DeploymentManifest where
  version := 1
  stateCodecId := ⟨101⟩
  operationCodecId := ⟨102⟩
  eventCodecId := ⟨103⟩
  tariff :=
    { authorizationWitnessBytes := 8
      baseProofWork := 5
      proofWorkPerTouch := 2
      networkCopies := 1
      leaseEpochs := 4
      unitFee := witnessUnitFee }

def witnessContext : RequestContext where
  domain := ⟨1⟩
  federation := ⟨3⟩
  subject := ⟨4⟩
  subjectKeyEpoch := 2
  nonce := 7
  height := 10
  policyId := ⟨9⟩
  policyEpoch := 5

noncomputable def witnessAuthorization :
    Authorized demoPortal demoState
      (witnessContext.request witnessManifest
        CanonicalResourceKernel.witnessMintAccepted) where
  evidence := .signature () rfl rfl
  policyWitness := ()
  policyMembershipWitness := ()
  policyEpochExact := rfl
  policyAddressExact := rfl
  policyMembershipVerified := rfl
  policyVerified := rfl

noncomputable def witnessPlan :
    AcceptedCellEffect (portal := demoPortal) (authState := demoState)
      (family witnessManifest CanonicalResourceKernel.witnessCell)
      (witnessContext.request witnessManifest
        CanonicalResourceKernel.witnessMintAccepted)
      CanonicalResourceKernel.witnessCell (.mint 0 1 2) () :=
  toCellEffect witnessManifest CanonicalResourceKernel.witnessMintAccepted
    witnessContext witnessAuthorization

set_option maxRecDepth 10000 in
example :
    (witnessContext.request witnessManifest
      CanonicalResourceKernel.witnessMintAccepted).cost = 3 := by
  rfl

set_option maxRecDepth 10000 in
example :
    (durableIntent ⟨200⟩ ⟨201⟩ witnessManifest
      CanonicalResourceKernel.witnessMintAccepted).exactCharge .feeDebit = 3 := by
  rfl

example :
    exactCharge witnessManifest CanonicalResourceKernel.witnessMintAccepted
      .memoryTouches = 1 := by
  rfl

example :
    exactCharge witnessManifest CanonicalResourceKernel.witnessMintAccepted
      .witnessBytes = 8 := by
  rfl

example :
    exactCharge witnessManifest CanonicalResourceKernel.witnessMintAccepted
      .proofWork = 7 := by
  rfl

example :
    (admissionBodyIntent ⟨200⟩ ⟨201⟩ witnessManifest
      CanonicalResourceKernel.witnessMintAccepted).exactCharge .feeDebit = 0 := by
  rfl

/-- info: 'Minidregg.Kernel.AuthorizedResourceCharge.request_cost_eq_durable_fee' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms request_cost_eq_durable_fee
/-- info: 'Minidregg.Kernel.AuthorizedResourceCharge.admission_add_body_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms admission_add_body_exact
/-- info: 'Minidregg.Kernel.AuthorizedResourceCharge.inflated_charge_changes_authorized_effectDigest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms inflated_charge_changes_authorized_effectDigest
/-- info: 'Minidregg.Kernel.AuthorizedResourceCharge.swapped_charge_changes_authorized_effectDigest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms swapped_charge_changes_authorized_effectDigest

end Minidregg.Kernel.AuthorizedResourceCharge
