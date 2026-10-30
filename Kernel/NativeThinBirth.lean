/-
# Kernel.NativeThinBirth — the thin consent birth arm (statement first)

Design: `docs/THIN-BIRTH-2026-10-28.md`. Thin consent (`Kernel.NativeThinConsent`) reads no
Store. A birth passes through two Host steps, and this arm checks both:

* **authoring** (`Host.CurrentResourceBirthAuthoring`, op 91): the member's `source.json`
  becomes the intent's draft descriptor. The Host's authoring reads three things from the
  Store: the height (grant window), the authority epochs, and a room birth's placement lineage.
  This arm re-runs the deployed authoring of the member's own source (`author`, instantiated
  once in `Host`) at the **coordinates** read off the draft (`coordinatesOf`), and compares the
  bytes exactly. The coordinates are shown, and each is an admission gate
  (`RootGrantShape`, `BirthWindow`, `AuthorityGrant.NativeForBirth`, `BornLineage`).
* **planning** (`NativeHost.prepareLoaded`, `.birth`): the planner fills only the kernel-owned
  `auxiliaryCreates` (`PreparedDraft.sourceExact`; forced at admission by
  `PreparedBirth.auxiliaryExact`) and signs one header per branch (`policyBranches`). Every
  member-derived field of every branch request is a function of the deployment's public pins
  and the finalized descriptor (`birthValues`). `checkHeader` takes only the three authority
  coordinates from the proposal, and the plan frame zeroes height and pre-root.

The binding: every branch's `effectsDigest` is the source effects digest of the whole executed
descriptor, and admission matches a signature only to `requestBytes` of its own request
(`CredentialSignatureAdmission.Prepared.headerExact`). So an admitted consented header fixes the
executed descriptor, up to a named collision scoped to two descriptors (it occurs exactly
at a collision of the deployment's cSHAKE source digest on two different encodings). The keystone
and the teeth conclude their claim or that collision (`EffectsCollision`), taking no hash premise.

## The poles (ATLAS fields), stated below; proofs follow the auditor's verdict

* **Keystone** `DisplayIsCommitStatement`: what a thin birth shows is what commits.
* **Teeth, after consent** `SwapAfterConsentRefusedStatement`: a Host that executes any other
  descriptor has no consented signature on any branch.
* **Teeth, before consent** `SwappedPlanRefusedStatement`: a swapped plan is refused
  `birthSourceChanged`; a swapped draft is refused `draftNotAuthored`.
* **Satisfiable** `HonestPlanAcceptedStatement`: the honest planner's plan is accepted.
* **Premise inhabitation**: the keystone and teeth take no carrier (they conclude
  `EffectsCollision` as a disjunct); `HonestPlanAcceptedStatement`'s premises are those of every
  successful birth preparation, its pins discharged by `OpenedPinsPublicStatement`. The Host-side
  re-authoring fixed point (an intent the Store-reading authoring produced re-authors to itself at
  its own coordinates) is a JOURNEY ROW (jpriv2 row 19), not a theorem.
-/
module

public import Kernel.NativeThinConsent
public import Kernel.NativeHost

-- Bodies this file reduces or derives through, not exposed by their modules (module system).
import all Init.Data.Repr
import all Init.Data.ToString.Basic
import all Init.Data.ToString.Extra
import all Init.Data.Array.Basic
import all Init.Data.ByteArray.Basic
import all Init.Data.String.Decode
import all Init.Data.String.Defs
import all Init.Control.Except
import all Init.Data.List.Basic
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.String.Bootstrap
import all Init.Data.Format.Basic
import all Init.Data.List.Scan.Basic
import all Kernel.NativeHost

@[expose] public section

namespace Minidregg.Kernel.NativeThinBirth

open Minidregg.Compiler
open Minidregg.Theory
open Minidregg.Theory.ResourceBirth
open Minidregg.Theory.TypedAuthorization
open Minidregg.Kernel.NativeThinConsent (checkHeader)
open Minidregg.Kernel.ResourceBirthPolicyController.Concrete (Branch PolicyBranch policyBranches branchRequest creation)

set_option autoImplicit false

abbrev Registry := CanonicalCellRegistry.registry

/-- The member-authored part of a birth descriptor: everything but the kernel's auxiliary
allocations (`ResourceBirthPolicyController.Concrete.userCommandBytes`). -/
def userPart (descriptor : Descriptor Registry) : Descriptor Registry :=
  { descriptor with auxiliaryCreates := [] }

/-! ## What the proposal contributes: the coordinates -/

/-- What the Host's authoring read from the Store, as data: the authoring height (every
grant's `notBefore`), the issuer epoch, each newborn's policy epoch, and each room placement's
ancestor set (as sorted capability ids). -/
structure BirthCoordinates where
  height : Nat
  issuerEpoch : Nat
  policyEpochs : List (Nat × Nat)
  lineage : List (Nat × List Nat)
  /-- The platform terms the draft carries (the receiver checks them against the record of the
  image it commits against): the first grant's owner budget and lifetime, and the fee. -/
  ownerBudget : Nat
  lifetime : Nat
  fee : CreationFee
  deriving DecidableEq, Repr

/-- The coordinates a draft carries, read off its grants: the first grant's window start and
issuer epoch, every grant's (policy id, policy epoch), and for every room birth with a lineage
the owner grant's ancestors (grants are `[owner, control]` per birth, in birth order). A draft whose
grants disagree with each other on a coordinate re-authors to different bytes and is refused. -/
def coordinatesOf (descriptor : Descriptor Registry) : BirthCoordinates where
  height := (descriptor.grants.head?.map fun grant => grant.capability.head.notBefore).getD 0
  issuerEpoch := (descriptor.grants.head?.map fun grant => grant.capability.head.issuerEpoch).getD 0
  policyEpochs := descriptor.grants.map fun grant =>
    (grant.capability.head.policyId.value, grant.capability.head.policyEpoch)
  lineage := (List.range descriptor.births.length).filterMap fun position => do
    let item ← descriptor.births[position]?
    let placement ← item.placement
    let owner ← descriptor.grants[2 * position]?
    let ancestors := (owner.capability.head.ancestors.image CapabilityId.value).sort (· ≤ ·)
    if ancestors.isEmpty then none else pure (placement.value, ancestors)
  ownerBudget := (descriptor.grants.head?.map fun grant => grant.capability.head.scope.maxCost).getD 0
  lifetime := (descriptor.grants.head?.map fun grant =>
    grant.capability.head.notAfter - grant.capability.head.notBefore).getD 0
  fee := descriptor.fee

/-! ## The member's derivation of every branch request -/

/-- The deployment pins a birth request reads, all from the config
(`NativeHostContext.validateChecks`): domain, semantics, federation and the factory id, which
is also the factory policy id. -/
structure PublicPins where
  domain : Digest
  semantics : Digest
  federation : FederationId
  factory : Nat
  deriving DecidableEq, Repr

def publicPins (config : NativeHost.Config) : PublicPins :=
  ⟨config.deployment.domain, config.profile.semantics, config.federation, config.deployment.factoryId⟩

/-- The factory and authority legs (`factoryRequest`, `ResourceBirthAuthority.request`). The
three authority coordinates, height and pre-root are placeholders `checkHeader` and the plan
frame never compare. -/
def factoryValues (pins : PublicPins) (descriptor : Descriptor Registry) : Request .object where
  domain := pins.domain
  semantics := pins.semantics
  federation := pins.federation
  subject := descriptor.creator
  subjectKeyEpoch := 0
  target := ⟨pins.factory⟩
  verb := .mutateObject
  argsDigest := CanonicalCellRegistry.sourceEncoding.argsDigest descriptor
  effectsDigest := CanonicalCellRegistry.sourceEncoding.effectsDigest descriptor
  nonce := descriptor.nonce
  height := 0
  preStateRoot := ⟨0⟩
  policyId := ⟨pins.factory⟩
  policyEpoch := 0
  policyRevision := 0
  cost := descriptor.fee.amount

/-- An allocation leg (`ResourceBirthController.allocationRequest`). -/
def allocationValues (pins : PublicPins) (descriptor : Descriptor Registry) (cell : Nat) :
    Request .object :=
  { factoryValues pins descriptor with
    argsDigest := CanonicalCellRegistry.sourceEncoding.hashBytes
      ("DREGG.RESOURCE.BIRTH.ALLOCATION.ARGS/v2".toUTF8.toList ++
        Tower256ConcreteBackend.StreamCodec.nat.encode cell ++
        CanonicalCellRegistry.sourceEncoding.codec.encode descriptor) }

/-- A Book source leg (`CanonicalResourceEffect.batchSourceRequest` over
`resourceContexts`). -/
def sourceValues (pins : PublicPins) (descriptor : Descriptor Registry)
    (position : Fin descriptor.resourceBatch.operations.length) : Request .account :=
  let operation := descriptor.resourceBatch.operations.get position
  { domain := pins.domain
    semantics := pins.semantics
    federation := pins.federation
    subject := descriptor.creator
    subjectKeyEpoch := 0
    target := ⟨operation.posting.source⟩
    verb := .transfer
    argsDigest := CanonicalResourceEffect.sourceArgsDigest CanonicalCellRegistry.sourceEncoding
      descriptor position
    effectsDigest := CanonicalCellRegistry.sourceEncoding.effectsDigest descriptor
    nonce := descriptor.nonce
    height := 0
    preStateRoot := ⟨0⟩
    policyId := ⟨operation.posting.source⟩
    policyEpoch := 0
    policyRevision := 0
    cost := operation.feeDebit }

/-- The member's derivation of one branch request of a birth. -/
def birthValues (pins : PublicPins) (descriptor : Descriptor Registry) :
    Branch descriptor → AuthorizationDeclaration.SomeRequest
  | .factory => ⟨.object, factoryValues pins descriptor⟩
  | .authority => ⟨.object, factoryValues pins descriptor⟩
  | .allocation index => ⟨.object, allocationValues pins descriptor (creation descriptor index).cellId⟩
  | .source index => ⟨.account, sourceValues pins descriptor index⟩

/-- A branch's signing role and index in the plan (`NativeHost.prepareLoaded`'s `forBranch`). -/
def branchSlot {allocations sources : Nat} : PolicyBranch allocations sources → Nat × Nat
  | .factory => (0, 0)
  | .authority => (1, 0)
  | .allocation index => (2, index.val)
  | .source index => (3, index.val)

/-- The slots a birth's plan must carry, in order, with the member's derivation of each. -/
def birthSlotPlan (pins : PublicPins) (descriptor : Descriptor Registry) :
    List (Nat × Nat × AuthorizationDeclaration.SomeRequest) :=
  (policyBranches descriptor.createRequests.length descriptor.resourceBatch.operations.length).map
    fun branch => ((branchSlot branch).1, (branchSlot branch).2, birthValues pins descriptor branch)

/-- Every slot is the expected branch, in order, and its header signs the member's derivation. -/
def checkSlots (marker : Nat) :
    Nat → List NativeHostCodec.SigningSlot → List (Nat × Nat × AuthorizationDeclaration.SomeRequest) →
      Except NativeThinConsent.Refusal Unit
  | _, [], [] => .ok ()
  | position, slot :: slots, (role, index, values) :: expected =>
      if slot.role = role ∧ slot.index = index then
        match checkHeader position marker values.2 slot.header with
        | .error refusal => .error refusal
        | .ok () => checkSlots marker (position + 1) slots expected
      else .error .slotShape
  | _, _, _ => .error .slotShape

/-! ## The arm -/

/-- What thin consent shows for a birth: the member-authored descriptor bytes and source
capabilities, the coordinates the Host's authoring read, and the finalized bytes the headers sign
(the authored bytes plus the kernel-owned auxiliary creates). -/
structure BirthDisplay where
  draft : List UInt8
  capabilities : List CapabilityId
  coordinates : BirthCoordinates
  finalized : List UInt8
  deriving DecidableEq, Repr

/-- **The authoring check alone** (thin birth intent consent, before any plan exists): the
intent is an ordinary birth whose draft is a canonical descriptor without auxiliary creates, and
the deployed authoring of the member's source at the draft's own coordinates is exactly this
intent. Returns the draft bytes, source capabilities and decoded draft. -/
def checkBirthIntentThin (author : BirthCoordinates → Option NativeObservationCodec.Intent)
    (wanted : NativeObservationCodec.Intent) :
    Except NativeThinConsent.Refusal (List UInt8 × List CapabilityId × Descriptor Registry) :=
  match wanted.purpose with
  | .prepare (.birth draftBytes capabilities) =>
    if (GrainResourceBirthHostCodec.sourceCodec.decode draftBytes).isSome then
      .error (.birthRoute "grain-backed birth source")
    else
    match CanonicalCellRegistry.sourceEncoding.codec.decode draftBytes with
    | none => .error .birthMalformed
    | some draft =>
      if draft.auxiliaryCreates.isEmpty then
        if author (coordinatesOf draft) = some wanted then .ok (draftBytes, capabilities, draft)
        else .error .draftNotAuthored
      else .error .birthMalformed
  | _ => .error (.birthRoute "not a birth intent")

/-- The births the thin birth arm consents to: a birth intent whose draft is not a grain-backed
source. The thin intent and plan frames (230/232) refuse exactly these by name, so an ordinary
birth is consented only with the member's source (234/235). A grain-backed birth has no thin birth
path (`checkBirthIntentThin` refuses it `birthRoute`), and its intent consent is the provider-route
check alone (a provider purse's law against the pinned tariff, `Kernel.ProviderRouteConsent`). -/
def thinBirthIntent (wanted : NativeObservationCodec.Intent) : Bool :=
  match wanted.purpose with
  | .prepare (.birth draftBytes _) => (GrainResourceBirthHostCodec.sourceCodec.decode draftBytes).isNone
  | _ => false

/-- **The discriminator covers the arm.** Every intent the thin birth arm accepts is one the thin
intent and plan frames refuse by name, so no birth the arm checks against the member's source can
be consented without it. -/
theorem thinBirthIntent_of_checked {author : BirthCoordinates → Option NativeObservationCodec.Intent}
    {wanted : NativeObservationCodec.Intent}
    {result : List UInt8 × List CapabilityId × Descriptor Registry}
    (checked : checkBirthIntentThin author wanted = .ok result) : thinBirthIntent wanted = true := by
  unfold checkBirthIntentThin at checked
  unfold thinBirthIntent
  revert checked
  split
  · split
    · intro checked
      cases checked
    · rename_i grain
      intro _
      simpa using grain
  · intro checked
    cases checked

#assert_axioms thinBirthIntent_of_checked

/-- **Thin birth consent.** `author` is the deployed authoring of the member's own source at
given coordinates (instantiated once, in `Host`): the whole intent (subject, nonce, observe
grants, the draft's descriptor bytes and source capabilities) must be the authored one. Returns
the headers to sign and the display. -/
def checkBirthThin (pins : PublicPins) (author : BirthCoordinates → Option NativeObservationCodec.Intent)
    (wanted : NativeObservationCodec.Intent) (planBytes : List UInt8) :
    Except NativeThinConsent.Refusal (List (List UInt8) × BirthDisplay) :=
  match checkBirthIntentThin author wanted with
  | .error refusal => .error refusal
  | .ok (draftBytes, capabilities, draft) =>
    match NativeHostCodec.signingPlanCodec.decode planBytes with
    | none => .error .planMalformed
    | some plan =>
      match plan.finalizedDraft with
      | .birth finalBytes finalCapabilities =>
        if plan.domain = pins.domain ∧ plan.semantics = pins.semantics ∧
            finalCapabilities = capabilities then
          match CanonicalCellRegistry.sourceEncoding.codec.decode finalBytes with
          | none => .error .planMalformed
          | some finalized =>
            if CanonicalCellRegistry.sourceEncoding.codec.encode finalized = finalBytes then
              if CanonicalCellRegistry.sourceEncoding.codec.encode (userPart finalized) =
                  draftBytes then
                match checkSlots finalized.authorityNullifier 0 plan.slots
                    (birthSlotPlan pins finalized) with
                | .error refusal => .error refusal
                | .ok () => .ok (plan.slots.map NativeHostCodec.SigningSlot.header,
                    ⟨draftBytes, capabilities, coordinatesOf draft, finalBytes⟩)
              else .error .birthSourceChanged
            else .error .planMalformed
        else .error .planCoordinates
      | _ => .error .planCoordinates

/-! ## The named collision -/

/-- Two different descriptors with the same source effects digest: a collision of the
deployment's cSHAKE source digest at exactly these two (canonical) encodings. The keystone and
the teeth conclude their claim **or** this event, so neither takes a hash premise. -/
def EffectsCollision (signed executed : Descriptor Registry) : Prop :=
  signed ≠ executed ∧
    CanonicalCellRegistry.sourceEncoding.effectsDigest signed =
      CanonicalCellRegistry.sourceEncoding.effectsDigest executed

/-! ## The poles -/

/-- **Keystone: what a thin birth shows is what commits.** Take the executor's own preparation
of a birth of descriptor `d` (`PreparedBirth`, built from the loaded image at admission) and a
signature the receiver admitted for one of its branches
(`CredentialSignatureAdmission.Prepared`) whose header is one thin consent accepted. Under the
collision at the two descriptors, at the descriptor the headers sign:

* the deployed authoring of the member's source at the shown coordinates is the intent, whose
  draft is the shown draft and capabilities;
* the executed descriptor's member-authored part is exactly the shown draft;
* its auxiliary creates are the kernel's (the grant batch's recomputation);
* the prepared writes are the newborn allocations, the factory's (unchanged) and the Book's, and
  the authority's, and nothing else;
* the newborn writes are the shown creates, then the kernel's;
* the authority post is the shown authority entries over the pre-state;
* the Book's logical post is the shown resource batch applied to the pre-Book. -/
def DisplayIsCommitStatement : Prop :=
  ∀ {F : Type} [Field F] {profile : CanonicalRuntimeProfile.Profile F}
    {deployment : CanonicalCellRegistry.Deployment} {pins : FactoryPins}
    {durable : ResourceBirthController.Concrete.Durable} {d : Descriptor Registry}
    (prepared : ResourceBirthController.Concrete.PreparedBirth profile.compilerProfile deployment
      pins durable d)
    (height : Height) (deployed : PublicPins) (author : BirthCoordinates → Option NativeObservationCodec.Intent)
    (wanted : NativeObservationCodec.Intent) (planBytes : List UInt8)
    (headers : List (List UInt8)) (shown : BirthDisplay) (signed : Descriptor Registry)
    (branch : Branch d) (snapshot : CredentialAuthorityDomain.Snapshot) (nullifier : Nat)
    (admitted : CredentialSignatureAdmission.Prepared snapshot nullifier
      (branchRequest prepared height branch))
    (bytes : List UInt8),
    checkBirthThin deployed author wanted planBytes = .ok (headers, shown) →
    bytes ∈ headers →
    CredentialSignedEnvelopeController.headerCodec.decode bytes =
      some admitted.controller.envelope.header →
    CanonicalCellRegistry.sourceEncoding.codec.decode shown.finalized = some signed →
    EffectsCollision signed d ∨
    (author shown.coordinates = some wanted ∧
    wanted.purpose = .prepare (.birth shown.draft shown.capabilities) ∧
    CanonicalCellRegistry.sourceEncoding.codec.encode (userPart d) = shown.draft ∧
    d.auxiliaryCreates = prepared.grants.auxiliaryCreates ∧
    prepared.writes = ResourceBirthController.Concrete.planWrites deployment d
      prepared.factory.payload prepared.book.payload prepared.resources.post prepared.grants.writes ∧
    ResourceBirthController.allocationWrites d =
      (userPart d).createRequests.map ResourceBirthController.birthWrite ++
        prepared.grants.auxiliaryCreates.map ResourceBirthController.birthWrite ∧
    prepared.grants.post.logical =
      CredentialAuthorityEffects.setAll prepared.authority.snapshot.logical
        (ResourceBirthAuthority.entries (userPart d)) ∧
    CanonicalResourceKernel.logicalBook prepared.resources.post.logical =
      (userPart d).resourceBatch.apply
        (CanonicalResourceKernel.logicalBook prepared.book.payload.logical))

/-- **Teeth, after consent.** A Host that executes a birth of any descriptor `d'` other than the
one the consented headers sign gets no consented signature admitted on any branch of it: every
signature the receiver admits for a branch of `d'` has a header thin consent did not accept. -/
def SwapAfterConsentRefusedStatement : Prop :=
  ∀ {F : Type} [Field F] {profile : CanonicalRuntimeProfile.Profile F}
    {deployment : CanonicalCellRegistry.Deployment} {pins : FactoryPins}
    {durable : ResourceBirthController.Concrete.Durable} {d' : Descriptor Registry}
    (prepared : ResourceBirthController.Concrete.PreparedBirth profile.compilerProfile deployment
      pins durable d')
    (height : Height) (deployed : PublicPins) (author : BirthCoordinates → Option NativeObservationCodec.Intent)
    (wanted : NativeObservationCodec.Intent) (planBytes : List UInt8)
    (headers : List (List UInt8)) (shown : BirthDisplay) (signed : Descriptor Registry),
    checkBirthThin deployed author wanted planBytes = .ok (headers, shown) →
    CanonicalCellRegistry.sourceEncoding.codec.decode shown.finalized = some signed →
    signed ≠ d' →
    EffectsCollision signed d' ∨
    ∀ (branch : Branch d') (snapshot : CredentialAuthorityDomain.Snapshot) (nullifier : Nat)
      (admitted : CredentialSignatureAdmission.Prepared snapshot nullifier
        (branchRequest prepared height branch)),
      ∀ bytes ∈ headers,
        CredentialSignedEnvelopeController.headerCodec.decode bytes ≠
          some admitted.controller.envelope.header

/-- **Teeth, before consent.** (1) A plan whose finalized descriptor's member part is not the
intent's draft is refused `birthSourceChanged`, before anything is signed. (2) An intent draft
that is not the deployed authoring of the member's source at its own coordinates is refused
`draftNotAuthored`. -/
def SwappedPlanRefusedStatement : Prop :=
  (∀ (deployed : PublicPins) (author : BirthCoordinates → Option NativeObservationCodec.Intent)
      (wanted : NativeObservationCodec.Intent) (planBytes draftBytes finalBytes : List UInt8)
      (capabilities : List CapabilityId) (draft finalized : Descriptor Registry)
      (plan : NativeHostCodec.SigningPlan),
    wanted.purpose = .prepare (.birth draftBytes capabilities) →
    GrainResourceBirthHostCodec.sourceCodec.decode draftBytes = none →
    CanonicalCellRegistry.sourceEncoding.codec.decode draftBytes = some draft →
    draft.auxiliaryCreates = [] →
    author (coordinatesOf draft) = some wanted →
    NativeHostCodec.signingPlanCodec.decode planBytes = some plan →
    plan.finalizedDraft = .birth finalBytes capabilities →
    plan.domain = deployed.domain → plan.semantics = deployed.semantics →
    CanonicalCellRegistry.sourceEncoding.codec.decode finalBytes = some finalized →
    CanonicalCellRegistry.sourceEncoding.codec.encode finalized = finalBytes →
    CanonicalCellRegistry.sourceEncoding.codec.encode (userPart finalized) ≠ draftBytes →
    checkBirthThin deployed author wanted planBytes = .error .birthSourceChanged) ∧
  (∀ (deployed : PublicPins) (author : BirthCoordinates → Option NativeObservationCodec.Intent)
      (wanted : NativeObservationCodec.Intent) (planBytes draftBytes : List UInt8)
      (capabilities : List CapabilityId) (draft : Descriptor Registry),
    wanted.purpose = .prepare (.birth draftBytes capabilities) →
    GrainResourceBirthHostCodec.sourceCodec.decode draftBytes = none →
    CanonicalCellRegistry.sourceEncoding.codec.decode draftBytes = some draft →
    draft.auxiliaryCreates = [] →
    author (coordinatesOf draft) ≠ some wanted →
    checkBirthThin deployed author wanted planBytes = .error .draftNotAuthored)

/-- **Satisfiable: the honest Host passes.** For a canonical ordinary birth draft that is the
member's authoring at its own coordinates, the plan the deployed planner builds on any opened
image (`NativeHost.prepareLoaded`, the served path's birth arm) is accepted, and the headers to
sign are exactly the plan's. The opened image is the Host's own open (`validateLoaded`; the
session's incremental `validateLoadedFrom` is the same, `validateLoadedFrom_eq`), whose pins are
the config's (`OpenedPinsPublicStatement`). -/
def HonestPlanAcceptedStatement : Prop :=
  ∀ (config : NativeHost.Config) (durable : ResourceBirthController.Concrete.Durable)
    (opened : NativeHost.Opened config)
    (author : BirthCoordinates → Option NativeObservationCodec.Intent) (wanted : NativeObservationCodec.Intent)
    (draftBytes : List UInt8) (capabilities : List CapabilityId) (draft : Descriptor Registry)
    (plan : NativeHostCodec.SigningPlan),
    NativeHost.validateLoaded config durable = .ok opened →
    wanted.purpose = .prepare (.birth draftBytes capabilities) →
    GrainResourceBirthHostCodec.sourceCodec.decode draftBytes = none →
    CanonicalCellRegistry.sourceEncoding.codec.decode draftBytes = some draft →
    CanonicalCellRegistry.sourceEncoding.codec.encode draft = draftBytes →
    author (coordinatesOf draft) = some wanted →
    NativeHost.prepareLoaded config opened (.birth draftBytes capabilities) = .ok plan →
    ∃ shown, checkBirthThin (publicPins config) author wanted
        (NativeHostCodec.signingPlanCodec.encode plan) =
      .ok (plan.slots.map NativeHostCodec.SigningSlot.header, shown)

/-- **The Host's opened image carries the config's public pins**: `validateLoaded` builds `Opened`
from `validateChecks`' pins. -/
def OpenedPinsPublicStatement : Prop :=
  ∀ (config : NativeHost.Config) (durable : ResourceBirthController.Concrete.Durable)
    (opened : NativeHost.Opened config),
    NativeHost.validateLoaded config durable = .ok opened →
    opened.pins.federation = config.federation ∧
      opened.pins.policyId = ⟨config.deployment.factoryId⟩

/-! ## Proofs -/

section Proofs

variable {F : Type} [Field F] {profile : CanonicalRuntimeProfile.Profile F}
  {deployment : CanonicalCellRegistry.Deployment} {pins : FactoryPins}
  {durable : ResourceBirthController.Concrete.Durable} {d : Descriptor Registry}

/-- Every branch request of a birth carries the source effects digest of the whole descriptor. -/
theorem branchRequest_effects
    (prepared : ResourceBirthController.Concrete.PreparedBirth profile.compilerProfile deployment
      pins durable d) (height : Height) (branch : Branch d) :
    (branchRequest prepared height branch).2.effectsDigest =
      CanonicalCellRegistry.sourceEncoding.effectsDigest d := by
  cases branch <;> rfl

theorem birthValues_effects (deployed : PublicPins) (descriptor : Descriptor Registry)
    (branch : Branch descriptor) :
    (birthValues deployed descriptor branch).2.effectsDigest =
      CanonicalCellRegistry.sourceEncoding.effectsDigest descriptor := by
  cases branch <;> rfl

theorem birthSlotPlan_effects {deployed : PublicPins} {descriptor : Descriptor Registry}
    {entry : Nat × Nat × AuthorizationDeclaration.SomeRequest}
    (member : entry ∈ birthSlotPlan deployed descriptor) :
    entry.2.2.2.effectsDigest = CanonicalCellRegistry.sourceEncoding.effectsDigest descriptor := by
  obtain ⟨branch, _, rfl⟩ := List.mem_map.mp member
  exact birthValues_effects deployed descriptor branch

/-- Every slot `checkSlots` accepted has its header checked against some expected entry. -/
theorem checkSlots_header (marker : Nat) (slots : List NativeHostCodec.SigningSlot) :
    ∀ (position : Nat) (expected : List (Nat × Nat × AuthorizationDeclaration.SomeRequest)),
      checkSlots marker position slots expected = .ok () →
      ∀ slot ∈ slots, ∃ entry ∈ expected, ∃ n,
        checkHeader n marker entry.2.2.2 slot.header = .ok () := by
  induction slots with
  | nil => intro _ _ _ slot member; cases member
  | cons head tail ih =>
    intro position expected accepted slot member
    match expected, accepted with
    | [], accepted => simp [checkSlots] at accepted
    | (role, index, values) :: rest, accepted =>
      simp only [checkSlots] at accepted
      split at accepted
      · split at accepted
        · cases accepted
        · rename_i ok
          rcases List.mem_cons.mp member with same | inTail
          · subst same
            exact ⟨(role, index, values), List.mem_cons_self, position, ok⟩
          · obtain ⟨entry, entryMember, n, checked⟩ := ih (position + 1) rest accepted slot inTail
            exact ⟨entry, List.mem_cons_of_mem _ entryMember, n, checked⟩
      · cases accepted

/-- A header the receiver admitted for `request` that thin consent accepted against `values`
signs a request with the effects digest of `values`. -/
theorem consented_effects {marker n : Nat} {kind : ResourceKind} {values : Request kind}
    {bytes : List UInt8} {header : CredentialSignedEnvelopeController.SignedHeader}
    {request : AuthorizationDeclaration.SomeRequest}
    (accepted : checkHeader n marker values bytes = .ok ())
    (decoded : CredentialSignedEnvelopeController.headerCodec.decode bytes = some header)
    (signs : header.message = CredentialSignatureAdmission.requestBytes request) :
    request.2.effectsDigest = values.effectsDigest := by
  obtain ⟨found, decodedRequest, decodedFound, _, message, _⟩ :=
    NativeThinConsent.checkHeader_binds accepted
  rw [decoded] at decodedFound
  obtain rfl := Option.some.inj decodedFound
  rw [signs] at message
  have same := (TypedAuthorizationRequestCodec.signedRequestBytes_eq_iff _ _).mp message
  exact congrArg (fun wanted : AuthorizationDeclaration.SomeRequest => wanted.2.effectsDigest) same

/-- An admitted signature's header signs exactly the receiver's request. -/
theorem admitted_message {snapshot : CredentialAuthorityDomain.Snapshot} {nullifier : Nat}
    {request : AuthorizationDeclaration.SomeRequest}
    (admitted : CredentialSignatureAdmission.Prepared snapshot nullifier request) :
    admitted.controller.envelope.header.message = CredentialSignatureAdmission.requestBytes request := by
  rw [admitted.headerExact]
  rfl

/-- What an accepted thin birth intent consists of. -/
theorem checkBirthIntentThin_ok {author : BirthCoordinates → Option NativeObservationCodec.Intent}
    {wanted : NativeObservationCodec.Intent} {draftBytes : List UInt8}
    {capabilities : List CapabilityId} {draft : Descriptor Registry}
    (checked : checkBirthIntentThin author wanted = .ok (draftBytes, capabilities, draft)) :
    wanted.purpose = .prepare (.birth draftBytes capabilities) ∧
      author (coordinatesOf draft) = some wanted := by
  unfold checkBirthIntentThin at checked
  split at checked
  · rename_i bytes caps purpose
    split at checked
    · cases checked
    split at checked
    · cases checked
    split at checked
    · split at checked
      · rename_i authored
        simp only [Except.ok.injEq, Prod.mk.injEq] at checked
        obtain ⟨rfl, rfl, rfl⟩ := checked
        exact ⟨purpose, authored⟩
      · cases checked
    · cases checked
  · cases checked

/-- What an accepted thin birth consists of. -/
theorem checkBirthThin_ok {deployed : PublicPins}
    {author : BirthCoordinates → Option NativeObservationCodec.Intent}
    {wanted : NativeObservationCodec.Intent} {planBytes : List UInt8}
    {headers : List (List UInt8)} {shown : BirthDisplay}
    (checked : checkBirthThin deployed author wanted planBytes = .ok (headers, shown)) :
    ∃ (draft : Descriptor Registry) (plan : NativeHostCodec.SigningPlan)
      (finalized : Descriptor Registry),
      wanted.purpose = .prepare (.birth shown.draft shown.capabilities) ∧
      shown.coordinates = coordinatesOf draft ∧
      author (coordinatesOf draft) = some wanted ∧
      NativeHostCodec.signingPlanCodec.decode planBytes = some plan ∧
      plan.finalizedDraft = .birth shown.finalized shown.capabilities ∧
      CanonicalCellRegistry.sourceEncoding.codec.decode shown.finalized = some finalized ∧
      CanonicalCellRegistry.sourceEncoding.codec.encode (userPart finalized) = shown.draft ∧
      checkSlots finalized.authorityNullifier 0 plan.slots (birthSlotPlan deployed finalized) =
        .ok () ∧
      headers = plan.slots.map NativeHostCodec.SigningSlot.header := by
  unfold checkBirthThin at checked
  split at checked
  · cases checked
  rename_i draftBytes capabilities draft intentOk
  obtain ⟨purpose, authored⟩ := checkBirthIntentThin_ok intentOk
  split at checked
  · cases checked
  rename_i plan decodedPlan
  split at checked
  · rename_i finalBytes finalCapabilities finalizedDraft
    split at checked
    · rename_i coordinates
      obtain ⟨_, _, sameCapabilities⟩ := coordinates
      subst sameCapabilities
      split at checked
      · cases checked
      rename_i finalized decodedFinal
      split at checked
      · split at checked
        · rename_i userExact
          split at checked
          · cases checked
          · rename_i slotsOk
            simp only [Except.ok.injEq, Prod.mk.injEq] at checked
            obtain ⟨rfl, rfl⟩ := checked
            exact ⟨draft, plan, finalized, purpose, rfl, authored, decodedPlan,
              finalizedDraft, decodedFinal, userExact, slotsOk, rfl⟩
        · cases checked
      · cases checked
    · cases checked
  · cases checked

theorem display_is_commit : DisplayIsCommitStatement := by
  intro F _ profile deployment pins durable d prepared height deployed author wanted planBytes
    headers shown signed branch snapshot nullifier admitted bytes checked member decodedHeader
    decodedSigned
  obtain ⟨draft, plan, finalized, purpose, coordinatesExact, authored, _, _, decodedFinal,
    userExact, slotsOk, headersExact⟩ := checkBirthThin_ok checked
  rw [decodedFinal] at decodedSigned
  obtain rfl := Option.some.inj decodedSigned
  rw [headersExact] at member
  obtain ⟨slot, slotMember, rfl⟩ := List.mem_map.mp member
  obtain ⟨entry, entryMember, n, accepted⟩ :=
    checkSlots_header _ _ _ _ slotsOk slot slotMember
  have effects := consented_effects accepted decodedHeader (admitted_message admitted)
  rw [branchRequest_effects, birthSlotPlan_effects entryMember] at effects
  by_cases same : finalized = d
  · subst same
    refine Or.inr ⟨coordinatesExact ▸ authored, purpose, userExact, prepared.auxiliaryExact, rfl,
      ?_, prepared.grants.post_logical, prepared.resources.post_logicalBook⟩
    unfold ResourceBirthController.allocationWrites Descriptor.createRequests userPart
    rw [prepared.auxiliaryExact]
    simp
  · exact Or.inl ⟨same, effects.symm⟩

theorem swap_after_consent_refused : SwapAfterConsentRefusedStatement := by
  intro F _ profile deployment pins durable d' prepared height deployed author wanted planBytes
    headers shown signed checked decodedSigned differs
  by_cases collision : EffectsCollision signed d'
  · exact Or.inl collision
  · refine Or.inr ?_
    intro branch snapshot nullifier admitted bytes member decodedHeader
    obtain ⟨_, plan, finalized, _, _, _, _, _, decodedFinal, _, slotsOk, headersExact⟩ :=
      checkBirthThin_ok checked
    rw [decodedFinal] at decodedSigned
    obtain rfl := Option.some.inj decodedSigned
    rw [headersExact] at member
    obtain ⟨slot, slotMember, rfl⟩ := List.mem_map.mp member
    obtain ⟨entry, entryMember, n, accepted⟩ :=
      checkSlots_header _ _ _ _ slotsOk slot slotMember
    have effects := consented_effects accepted decodedHeader (admitted_message admitted)
    rw [branchRequest_effects, birthSlotPlan_effects entryMember] at effects
    exact collision ⟨differs, effects.symm⟩

theorem swapped_plan_refused : SwappedPlanRefusedStatement := by
  refine ⟨?_, ?_⟩
  · intro deployed author wanted planBytes draftBytes finalBytes capabilities draft finalized plan
      purpose grain decodedDraft noAuxiliary authored decodedPlan finalizedDraft domain semantics
      decodedFinal canonical changed
    simp [checkBirthThin, checkBirthIntentThin, purpose, grain, decodedDraft, noAuxiliary, authored,
      decodedPlan, finalizedDraft, domain, semantics, decodedFinal, canonical, changed]
  · intro deployed author wanted planBytes draftBytes capabilities draft purpose grain decodedDraft
      noAuxiliary notAuthored
    simp [checkBirthThin, checkBirthIntentThin, purpose, grain, decodedDraft, noAuxiliary,
      notAuthored]

end Proofs

/-! ## Completeness: the honest Host passes -/

section Completeness

local notation "hostSlot" => Minidregg.Kernel.NativeHost.slot

variable {F : Type} [Field F] {profile : CanonicalRuntimeProfile.Profile F}
  {deployment : CanonicalCellRegistry.Deployment} {pins : FactoryPins}
  {durable : ResourceBirthController.Concrete.Durable} {d : Descriptor Registry}

/-- **The member's derivation is the executor's request** up to the three authority coordinates
(which `checkHeader` takes from the proposal) and the height and pre-root (which the plan frame
zeroes), when the public pins are the executor's. -/
theorem birthValues_exact
    (prepared : ResourceBirthController.Concrete.PreparedBirth profile.compilerProfile deployment
      pins durable d) (height : Height) (branch : Branch d) (deployed : PublicPins)
    (domain : deployed.domain = pins.domain) (semantics : deployed.semantics = pins.semantics)
    (federation : deployed.federation = pins.federation)
    (factory : (⟨deployed.factory⟩ : ResourceId .object) = pins.factory)
    (policy : (⟨deployed.factory⟩ : PolicyId) = pins.policyId) :
    TypedAuthorizationRequestCodec.planOf
        (NativeThinConsent.expectedRequest
          (TypedAuthorizationRequestCodec.planOf (branchRequest prepared height branch))
          (birthValues deployed d branch).2) =
      TypedAuthorizationRequestCodec.planOf (branchRequest prepared height branch) := by
  obtain ⟨pDomain, pSemantics, pFederation, pFactory⟩ := deployed
  simp only at domain semantics federation factory policy
  cases branch with
  | factory =>
      simp only [birthValues, branchRequest, ResourceBirthPolicyController.Concrete.rawLeg,
        factoryValues, factoryRequest, NativeThinConsent.expectedRequest,
        TypedAuthorizationRequestCodec.planOf, domain, semantics, federation, factory, policy]
  | authority =>
      simp only [birthValues, branchRequest, ResourceBirthPolicyController.Concrete.rawLeg,
        ResourceBirthAuthority.request, factoryValues, factoryRequest,
        NativeThinConsent.expectedRequest, TypedAuthorizationRequestCodec.planOf, domain,
        semantics, federation, factory, policy]
  | allocation index =>
      simp only [birthValues, branchRequest, ResourceBirthPolicyController.Concrete.rawLeg,
        ResourceBirthController.allocationRequest, allocationValues, factoryValues,
        factoryRequest, NativeThinConsent.expectedRequest, TypedAuthorizationRequestCodec.planOf,
        domain, semantics, federation, factory, policy]
  | source index =>
      simp only [birthValues, branchRequest, CanonicalResourceEffect.batchSourceRequest,
        CanonicalResourceEffect.RequestContext.request,
        ResourceBirthPolicyController.Concrete.resourceContexts, sourceValues,
        NativeThinConsent.expectedRequest, TypedAuthorizationRequestCodec.planOf, domain,
        semantics, federation, List.getElem?_eq_getElem index.isLt, Option.map_some,
        Option.getD_some, List.get_eq_getElem]

/-- The signed bytes of a request decode back to its plan form. -/
theorem signedRequest_requestBytes (request : AuthorizationDeclaration.SomeRequest) :
    NativeThinConsent.signedRequest (CredentialSignatureAdmission.requestBytes request) =
      some (TypedAuthorizationRequestCodec.planOf request) := by
  unfold NativeThinConsent.signedRequest CredentialSignatureAdmission.requestBytes
    TypedAuthorizationRequestCodec.signedRequestBytes
  simp only [List.take_left', List.drop_left', if_true]
  exact TypedAuthorizationRequestCodec.someRequestCodec.decode_encode _

/-- **A slot the honest planner built passes `checkHeader`** against the member's derivation. -/
theorem slot_checked
    (prepared : ResourceBirthController.Concrete.PreparedBirth profile.compilerProfile deployment
      pins durable d) (height : Height) (branch : Branch d) (deployed : PublicPins)
    (domain : deployed.domain = pins.domain) (semantics : deployed.semantics = pins.semantics)
    (federation : deployed.federation = pins.federation)
    (factory : (⟨deployed.factory⟩ : ResourceId .object) = pins.factory)
    (policy : (⟨deployed.factory⟩ : PolicyId) = pins.policyId)
    {snapshot : CredentialAuthorityDomain.Snapshot} {marker role index : Nat}
    {built : NativeHostCodec.SigningSlot}
    (ok : hostSlot snapshot marker role index (branchRequest prepared height branch) = .ok built) :
    built.role = role ∧ built.index = index ∧
      ∀ n, checkHeader n marker (birthValues deployed d branch).2 built.header = .ok () := by
  unfold Minidregg.Kernel.NativeHost.slot at ok
  cases signed : CredentialSignatureAdmission.signingHeader snapshot marker
      (branchRequest prepared height branch) with
  | error reason => simp [signed, bind, Except.bind, Except.mapError] at ok
  | ok header =>
    simp only [signed, bind, Except.bind, Except.mapError, pure, Except.pure,
      Except.ok.injEq] at ok
    subst ok
    refine ⟨rfl, rfl, fun n => ?_⟩
    unfold CredentialSignatureAdmission.signingHeader at signed
    cases selected : CredentialSignatureAdmission.select snapshot (branchRequest prepared height branch) with
    | error reason => simp [selected, bind, Except.bind] at signed
    | ok choice =>
      simp only [selected, bind, Except.bind, Except.ok.injEq] at signed
      subst signed
      have exact := birthValues_exact prepared height branch deployed domain semantics federation
        factory policy
      unfold checkHeader
      simp only [CredentialSignedEnvelopeController.headerCodec.decode_encode,
        CredentialSignatureAdmission.header, signedRequest_requestBytes]
      rw [show CredentialSignatureAdmission.requestBytes
          (NativeThinConsent.expectedRequest
            (TypedAuthorizationRequestCodec.planOf (branchRequest prepared height branch))
            (birthValues deployed d branch).2) =
          CredentialSignatureAdmission.requestBytes (branchRequest prepared height branch) from
        (TypedAuthorizationRequestCodec.signedRequestBytes_eq_iff _ _).mpr exact]
      simp

/-- `checkSlots` accepts slot lists that match the expected entries pointwise. -/
theorem checkSlots_forall₂ (marker : Nat) :
    ∀ (position : Nat) (slots : List NativeHostCodec.SigningSlot)
      (expected : List (Nat × Nat × AuthorizationDeclaration.SomeRequest)),
      List.Forall₂ (fun slot (entry : Nat × Nat × AuthorizationDeclaration.SomeRequest) =>
        slot.role = entry.1 ∧ slot.index = entry.2.1 ∧
          ∀ n, checkHeader n marker entry.2.2.2 slot.header = .ok ()) slots expected →
      checkSlots marker position slots expected = .ok ()
  | _, [], [], _ => rfl
  | position, slot :: slots, (role, index, values) :: expected, .cons ⟨sameRole, sameIndex, checked⟩ rest => by
      simp only [checkSlots, sameRole, sameIndex, and_self, if_true, checked position]
      exact checkSlots_forall₂ marker (position + 1) slots expected rest

private theorem mapM_forall₂ {α β : Type} (f : α → Except String β) :
    ∀ (l : List α) (l' : List β), l.mapM f = .ok l' → List.Forall₂ (fun b a => f a = .ok b) l' l
  | [], l', ok => by
      simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at ok
      subst ok
      exact .nil
  | a :: as, l', ok => by
      rw [List.mapM_cons] at ok
      cases fa : f a with
      | error e => simp [fa, bind, Except.bind] at ok
      | ok b =>
        cases fas : as.mapM f with
        | error e => simp [fa, fas, bind, Except.bind] at ok
        | ok bs =>
          simp only [fa, fas, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at ok
          subst ok
          exact .cons fa (mapM_forall₂ f as bs fas)

/-- `validateChecks` builds the config's public pins. -/
theorem validateChecks_pins {config : NativeHost.Config} {seed : DurableReceiver.Seed}
    {logStart : Digest} {directory? : Option (CellRegistry.Directory Nat CanonicalCellRegistry.registry)}
    {logical? : Option (Store.Store CredentialAuthorityState.layout)} {lawful? : Option Bool}
    {platform? : Option PlatformCellLayout.Platform} {built : FactoryPins}
    (validated : NativeHost.validateChecks config seed logStart directory? logical? lawful? platform? =
      .ok built) :
    built.federation = config.federation ∧ built.policyId = ⟨config.deployment.factoryId⟩ := by
  unfold NativeHost.validateChecks at validated
  repeat' (first | split at validated | (simp only [bind, Except.bind] at validated))
  all_goals first
    | (cases validated; done)
    | (simp only [pure, Except.pure, Except.ok.injEq] at validated; subst validated; exact ⟨rfl, rfl⟩)

private theorem map_ok {α β ε : Type} {f : α → β} {value : Except ε α} {result : β}
    (mapped : value.map f = .ok result) : ∃ a, value = .ok a ∧ f a = result := by
  cases value with
  | error e => cases mapped
  | ok a => exact ⟨a, rfl, by simpa [Except.map] using mapped⟩

theorem validateCore_pins {D A : Type} {config : NativeHost.Config} {seed : DurableReceiver.Seed}
    {logStart : Digest} {directory? : Option D} {authority? : Option A}
    {directoryOf : D → CellRegistry.Directory Nat CanonicalCellRegistry.registry}
    {logicalOf : A → Store.Store CredentialAuthorityState.layout} {lawfulCheck : D → Bool}
    {platform? : Option PlatformCellLayout.Platform}
    {parts : {parts : D × A × FactoryPins // lawfulCheck parts.1 = true}}
    (validated : NativeHost.validateCore config seed logStart directory? authority? directoryOf
      logicalOf lawfulCheck platform? = .ok parts) :
    parts.1.2.2.federation = config.federation ∧
      parts.1.2.2.policyId = ⟨config.deployment.factoryId⟩ := by
  unfold NativeHost.validateCore at validated
  cases checked : NativeHost.validateChecks config seed logStart (directory?.map directoryOf)
      (authority?.map logicalOf) (directory?.map lawfulCheck) platform? with
  | error detail => simp [checked, bind, Except.bind] at validated
  | ok built =>
    simp only [checked, bind, Except.bind] at validated
    repeat' split at validated
    all_goals first
      | (simp only [pure, Except.pure, Except.ok.injEq] at validated; subst validated;
          exact validateChecks_pins checked)
      | cases validated

theorem opened_pins_public : OpenedPinsPublicStatement := by
  intro config durable opened validated
  unfold NativeHost.validateLoaded at validated
  obtain ⟨parts, partsOk, rfl⟩ := map_ok validated
  unfold NativeHost.validateParts NativeHost.validatePartsWith NativeHost.validatePartsVia at partsOk
  split at partsOk
  · contradiction
  · simp only [Except.ok.injEq] at partsOk
    subst parts
    dsimp only
    have pins := validateCore_pins (by assumption)
    exact pins

/-- The executor's pins against the config's public pins, on the Host's own open. -/
theorem publicPins_exact {config : NativeHost.Config} {durable' : ResourceBirthController.Concrete.Durable}
    {opened : NativeHost.Opened config} {descriptor : Descriptor Registry}
    (validated : NativeHost.validateLoaded config durable' = .ok opened)
    (prepared : ResourceBirthController.Concrete.PreparedBirth config.profile.compilerProfile
      config.deployment opened.pins opened.durable descriptor) :
    (publicPins config).domain = opened.pins.domain ∧
      (publicPins config).semantics = opened.pins.semantics ∧
      (publicPins config).federation = opened.pins.federation ∧
      (⟨(publicPins config).factory⟩ : ResourceId .object) = opened.pins.factory ∧
      (⟨(publicPins config).factory⟩ : PolicyId) = opened.pins.policyId := by
  obtain ⟨federation, policy⟩ := opened_pins_public config durable' opened validated
  obtain ⟨factory, domain⟩ := prepared.pinsBound
  refine ⟨domain.symm, prepared.profileBound.1.symm, federation.symm, ?_, policy.symm⟩
  cases pinned : opened.pins.factory with
  | mk value =>
    rw [pinned] at factory
    simp only at factory
    simp [publicPins, factory]

/-- **Satisfiable: the honest Host passes.** -/
theorem honest_plan_accepted : HonestPlanAcceptedStatement := by
  intro config durable' opened author wanted draftBytes capabilities draft plan validated purpose
    grain decodedDraft canonical authored planned
  unfold NativeHost.prepareLoaded at planned
  simp only [grain, Option.isSome_none, Bool.false_eq_true, if_false, bind, Except.bind,
    NativeHost.need, decodedDraft] at planned
  generalize NativeHost.logicalHeight config opened.durable = height at planned
  cases prep : ResourceBirthController.Concrete.prepareDraft config.profile.compilerProfile
      config.profile.disabledEvaluators config.deployment opened.pins opened.durable draft height with
  | error reason => simp [prep, Except.mapError] at planned
  | ok prepared =>
  obtain ⟨domain, semantics, federation, factory, policy⟩ :=
    publicPins_exact validated prepared.prepared
  simp only [prep, Except.mapError] at planned
  cases capabilityCount : NativeHost.check
      (capabilities.length == prepared.descriptor.resourceBatch.operations.length)
      "birth source capability count mismatch" with
  | error reason => simp [capabilityCount] at planned
  | ok counted =>
  simp only [capabilityCount] at planned
  cases fac : hostSlot prepared.prepared.authority.snapshot prepared.descriptor.authorityNullifier 0 0
      (branchRequest prepared.prepared height .factory) with
  | error reason => simp [fac] at planned
  | ok factorySlot =>
  cases aut : hostSlot prepared.prepared.authority.snapshot prepared.descriptor.authorityNullifier 1 0
      (branchRequest prepared.prepared height .authority) with
  | error reason => simp [fac, aut] at planned
  | ok authoritySlot =>
  cases alloc : (List.finRange prepared.descriptor.createRequests.length).mapM (fun index =>
      hostSlot prepared.prepared.authority.snapshot prepared.descriptor.authorityNullifier 2 index.val
        (branchRequest prepared.prepared height (.allocation index))) with
  | error reason => simp [fac, aut, alloc] at planned
  | ok allocationSlots =>
  cases src : (List.finRange prepared.descriptor.resourceBatch.operations.length).mapM (fun index =>
      hostSlot prepared.prepared.authority.snapshot prepared.descriptor.authorityNullifier 3 index.val
        (branchRequest prepared.prepared height (.source index))) with
  | error reason => simp [fac, aut, alloc, src] at planned
  | ok sourceSlots =>
  simp only [fac, aut, alloc, src, pure, Except.pure, Except.ok.injEq] at planned
  subst planned
  have userExact : userPart prepared.descriptor = draft := by
    have exact := prepared.sourceExact
    have none := prepared.noAuxiliaryInput
    unfold userPart
    generalize prepared.descriptor = descriptor at exact ⊢
    rw [exact]
    cases draft
    simp only at none ⊢
    subst none
    rfl
  have slots : checkSlots prepared.descriptor.authorityNullifier 0
      (factorySlot :: authoritySlot :: (allocationSlots ++ sourceSlots))
      (birthSlotPlan (publicPins config) prepared.descriptor) = .ok () := by
    apply checkSlots_forall₂
    unfold birthSlotPlan ResourceBirthPolicyController.Concrete.policyBranches
    simp only [List.map_cons, List.map_append, List.map_map]
    refine .cons ?_ (.cons ?_ (List.rel_append ?_ ?_))
    · exact slot_checked prepared.prepared height .factory (publicPins config) domain semantics federation factory policy fac
    · exact slot_checked prepared.prepared height .authority (publicPins config) domain semantics federation factory policy aut
    · have pointwise := mapM_forall₂ _ _ _ alloc
      refine (List.forall₂_map_right_iff).mpr (pointwise.imp ?_)
      intro built index ok
      exact slot_checked prepared.prepared height (.allocation index) (publicPins config) domain semantics federation factory policy ok
    · have pointwise := mapM_forall₂ _ _ _ src
      refine (List.forall₂_map_right_iff).mpr (pointwise.imp ?_)
      intro built index ok
      exact slot_checked prepared.prepared height (.source index) (publicPins config) domain semantics federation factory policy ok
  simp only [publicPins] at slots
  refine ⟨⟨draftBytes, capabilities, coordinatesOf draft,
    CanonicalCellRegistry.sourceEncoding.codec.encode prepared.descriptor⟩, ?_⟩
  simp [checkBirthThin, checkBirthIntentThin, purpose, grain, decodedDraft,
    prepared.noAuxiliaryInput, authored, NativeHostCodec.signingPlanCodec.decode_encode,
    publicPins, CanonicalCellRegistry.sourceEncoding.codec.decode_encode, userExact, canonical,
    slots]

#assert_axioms birthValues_exact signedRequest_requestBytes slot_checked checkSlots_forall₂
  validateChecks_pins opened_pins_public publicPins_exact honest_plan_accepted

end Completeness

#assert_axioms branchRequest_effects birthValues_effects checkSlots_header consented_effects
  admitted_message checkBirthIntentThin_ok checkBirthThin_ok display_is_commit swap_after_consent_refused
  swapped_plan_refused

end Minidregg.Kernel.NativeThinBirth
