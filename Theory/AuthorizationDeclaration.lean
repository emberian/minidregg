/-
# Theory.AuthorizationDeclaration — executable declaration of typed authorization

`TypedAuthorization` owns the semantic objects and proof-relevant authorization
judgment.  This file adds only the minimum executable declaration needed to
project that judgment into two artifacts:

* a structured, first-order codec for the complete dependent `Request`;
* a finite verifier decision plan, compiled to `IndexedProgram.Program`.

The emitted layer (`RequestWire`, tags, fields, checks, plans, declaration)
contains no `Prop` fields.  Raw presentations also contain witness DATA only.
Proofs live below that boundary and show that an accepted executable plan can
construct the existing `TypedAuthorization.Authorized` type.  There is no
second semantic authorization relation.
-/
import Theory.IndexedProgram
import Theory.TypedAuthorization

namespace Minidregg.Theory.AuthorizationDeclaration

open IndexedProgram
open TypedAuthorization

/-! ## §1. Structured first-order request codec -/

/-- Existential packaging erases a resource-kind index only at the codec
boundary.  Decoding reconstructs the index before constructing `Request`. -/
abbrev SomeRequest := Σ kind : ResourceKind, Request kind

/-- The exact first-order request word.  Every field is scalar data; dependency
is restored by `decodeRequest` from `resourceKind` and `verb`. -/
structure RequestWire where
  domain : Nat
  semantics : Nat
  federation : Nat
  resourceKind : Nat
  subject : Nat
  subjectKeyEpoch : Nat
  target : Nat
  verb : Nat
  argsDigest : Nat
  effectsDigest : Nat
  nonce : Nat
  height : Nat
  preStateRoot : Nat
  policyId : Nat
  policyEpoch : Nat
  cost : Nat
  deriving DecidableEq, Repr

def resourceKindTag : ResourceKind → Nat
  | .object => 1
  | .account => 2
  | .program => 3

def decodeResourceKind : Nat → Option ResourceKind
  | 1 => some .object
  | 2 => some .account
  | 3 => some .program
  | _ => none

@[simp] theorem decodeResourceKind_tag (kind : ResourceKind) :
    decodeResourceKind (resourceKindTag kind) = some kind := by
  cases kind <;> rfl

/-- Tags are assigned to the EXISTING dependent verb constructors. -/
def verbTag {kind : ResourceKind} : Verb kind → Nat
  | .observeObject => 1
  | .mutateObject => 2
  | .delegateObject => 3
  | .observeAccount => 4
  | .transfer => 5
  | .delegateAccount => 6
  | .observeProgram => 7
  | .installProgram => 8
  | .delegateProgram => 9

/-- Kind-directed decoding makes an ill-kinded verb tag fail rather than
manufacturing an equality proof after the fact. -/
def decodeVerb (kind : ResourceKind) (tag : Nat) : Option (Verb kind) :=
  match kind, tag with
  | .object, 1 => some .observeObject
  | .object, 2 => some .mutateObject
  | .object, 3 => some .delegateObject
  | .account, 4 => some .observeAccount
  | .account, 5 => some .transfer
  | .account, 6 => some .delegateAccount
  | .program, 7 => some .observeProgram
  | .program, 8 => some .installProgram
  | .program, 9 => some .delegateProgram
  | _, _ => none

@[simp] theorem decodeVerb_tag {kind : ResourceKind} (verb : Verb kind) :
    decodeVerb kind (verbTag verb) = some verb := by
  cases verb <;> rfl

def encodeRequest : SomeRequest → RequestWire
  | ⟨kind, request⟩ =>
      { domain := request.domain.value
        semantics := request.semantics.value
        federation := request.federation.value
        resourceKind := resourceKindTag kind
        subject := request.subject.value
        subjectKeyEpoch := request.subjectKeyEpoch
        target := request.target.value
        verb := verbTag request.verb
        argsDigest := request.argsDigest.value
        effectsDigest := request.effectsDigest.value
        nonce := request.nonce
        height := request.height
        preStateRoot := request.preStateRoot.value
        policyId := request.policyId.value
        policyEpoch := request.policyEpoch
        cost := request.cost }

def decodeRequest (wire : RequestWire) : Option SomeRequest := do
  let kind ← decodeResourceKind wire.resourceKind
  let verb ← decodeVerb kind wire.verb
  some ⟨kind,
    { domain := ⟨wire.domain⟩
      semantics := ⟨wire.semantics⟩
      federation := ⟨wire.federation⟩
      subject := ⟨wire.subject⟩
      subjectKeyEpoch := wire.subjectKeyEpoch
      target := ⟨wire.target⟩
      verb := verb
      argsDigest := ⟨wire.argsDigest⟩
      effectsDigest := ⟨wire.effectsDigest⟩
      nonce := wire.nonce
      height := wire.height
      preStateRoot := ⟨wire.preStateRoot⟩
      policyId := ⟨wire.policyId⟩
      policyEpoch := wire.policyEpoch
      cost := wire.cost }⟩

/-- The structured codec is lossless for every typed request. -/
@[simp] theorem decodeRequest_encodeRequest (request : SomeRequest) :
    decodeRequest (encodeRequest request) = some request := by
  rcases request with ⟨kind, request⟩
  cases request with
  | mk domain semantics federation subject subjectKeyEpoch target verb
      argsDigest effectsDigest nonce height preStateRoot policyId policyEpoch cost =>
    cases verb <;> rfl

/-! ## §2. First-order emitted declaration — no propositions -/

/-- Canonical field order of `RequestWire`. -/
inductive RequestField where
  | domain | semantics | federation | resourceKind
  | subject | subjectKeyEpoch | target | verb
  | argsDigest | effectsDigest | nonce | height
  | preStateRoot | policyId | policyEpoch | cost
  deriving DecidableEq, Repr

def requestFieldOrder : List RequestField :=
  [.domain, .semantics, .federation, .resourceKind,
   .subject, .subjectKeyEpoch, .target, .verb,
   .argsDigest, .effectsDigest, .nonce, .height,
   .preStateRoot, .policyId, .policyEpoch, .cost]

inductive Mode where
  | signature
  | proof
  | capability
  deriving DecidableEq, Repr

/-- Atomic verifier steps.  Ancestor/channel checks denote bounded iteration
over the exact finite sets committed in the presented capability. -/
inductive Check where
  | subjectKeyEpoch
  | signature
  | proof
  | capabilitySemantic
  | capabilityCommitment
  | capabilityMembership
  | issuer
  | selfNonRevocation
  | ancestorNonRevocations
  | channelNonRevocations
  | policyEpoch
  | policyAddress
  | policyMembership
  | policy
  deriving DecidableEq, Repr

structure ModePlan where
  mode : Mode
  checks : List Check
  deriving DecidableEq, Repr

/-- Every mode ends at the SAME policy checks.  There is no mode-level return
which can bypass current-policy selection. -/
def checksFor : Mode → List Check
  | .signature =>
      [.subjectKeyEpoch, .signature, .policyEpoch, .policyAddress,
       .policyMembership, .policy]
  | .proof =>
      [.proof, .policyEpoch, .policyAddress, .policyMembership, .policy]
  | .capability =>
      [.capabilitySemantic, .capabilityCommitment,
       .capabilityMembership, .issuer, .selfNonRevocation,
       .ancestorNonRevocations, .channelNonRevocations,
       .policyEpoch, .policyAddress, .policyMembership, .policy]

/-- Complete emitted declaration.  It is intentionally first-order data. -/
structure Declaration where
  schemaVersion : Nat
  requestFields : List RequestField
  modes : List ModePlan
  deriving DecidableEq, Repr

def declaration : Declaration where
  schemaVersion := 1
  requestFields := requestFieldOrder
  modes :=
    [{ mode := .signature, checks := checksFor .signature },
     { mode := .proof, checks := checksFor .proof },
     { mode := .capability, checks := checksFor .capability }]

/-! ## §3. The declaration as an indexed verifier program -/

inductive Phase where
  | checking
  | decided
  deriving DecidableEq, Repr

inductive VerifyOp : Phase → Type
  | run (check : Check) : VerifyOp .checking
  | finish : VerifyOp .checking

def verifySignature : IxSignature Phase where
  Op := VerifyOp
  Resp := fun op => match op with
    | .run _ => Bool
    | .finish => Unit
  next := fun op => match op with
    | .run _ => fun response => if response then .checking else .decided
    | .finish => fun _ => .decided

inductive Decision where
  | accepted
  | rejected (failedCheck : Check)
  deriving DecidableEq, Repr

abbrev VerifyResult : Phase → Type := fun _ => Decision

/-- Structural compilation of first-order check data into the typed free
program.  A failed check can continue only at `.decided`; a successful check
continues at `.checking`. -/
def compileChecks : List Check → Program verifySignature VerifyResult .checking
  | [] => .call .finish fun _ => .pure .accepted
  | check :: rest => .call (.run check) fun
      | true => compileChecks rest
      | false => .pure (.rejected check)

def programFor (mode : Mode) : Program verifySignature VerifyResult .checking :=
  compileChecks (checksFor mode)

/-! ## §4. Raw witness data and executable checks — still no propositions -/

structure RevocationOpening (portal : Portal) where
  key : RevocationKey
  witness : portal.NonRevocationWitness

structure CapabilityPresentation (portal : Portal) (kind : ResourceKind) where
  cap : Capability kind
  commitment : Digest
  commitmentWitness : portal.CapabilityCommitmentWitness
  membershipWitness : portal.MembershipWitness
  issuerWitness : portal.IssuerWitness
  revocationOpenings : List (RevocationOpening portal)

/-- Raw evidence DATA is request-indexed but carries no proof fields. -/
inductive PresentedEvidence (portal : Portal) {kind : ResourceKind}
    (_request : Request kind) : Type where
  | signature (witness : portal.SignatureWitness)
  | proof (witness : portal.ProofWitness)
  | capability (presentation : CapabilityPresentation portal kind)

structure Presentation (portal : Portal) {kind : ResourceKind}
    (request : Request kind) where
  evidence : PresentedEvidence portal request
  policyWitness : portal.PolicyWitness
  policyMembershipWitness : portal.MembershipWitness

def PresentedEvidence.mode {portal : Portal} {kind : ResourceKind}
    {request : Request kind} : PresentedEvidence portal request → Mode
  | .signature _ => .signature
  | .proof _ => .proof
  | .capability _ => .capability

def lookupRevocation {portal : Portal} (key : RevocationKey) :
    List (RevocationOpening portal) → Option portal.NonRevocationWitness
  | [] => none
  | opening :: rest =>
      if opening.key = key then some opening.witness
      else lookupRevocation key rest

def CapabilityPresentation.verifyKey {portal : Portal} {kind : ResourceKind}
    (presentation : CapabilityPresentation portal kind)
    (root : Digest) (key : RevocationKey) : Bool :=
  match lookupRevocation key presentation.revocationOpenings with
  | none => false
  | some witness => portal.verifyNonRevocation root key witness

def CapabilityPresentation.verifyCapabilityIds
    {portal : Portal} {kind : ResourceKind}
    (presentation : CapabilityPresentation portal kind)
    (root : Digest) (ids : Finset CapabilityId) : Bool :=
  decide (∀ id ∈ ids, presentation.verifyKey root (.capability id) = true)

def CapabilityPresentation.verifyChannelIds
    {portal : Portal} {kind : ResourceKind}
    (presentation : CapabilityPresentation portal kind)
    (root : Digest) (ids : Finset ChannelId) : Bool :=
  decide (∀ id ∈ ids, presentation.verifyKey root (.channel id) = true)

/-! ### Executable reflection of the EXISTING semantic relation -/

def holderCoversCheck (holder : Holder) (subject : SubjectId) : Bool :=
  match holder with
  | .bearer => true
  | .subject bound => decide (bound = subject)

@[simp] theorem holderCoversCheck_eq_true_iff
    (holder : Holder) (subject : SubjectId) :
    holderCoversCheck holder subject = true ↔ holder.Covers subject := by
  cases holder <;> simp [holderCoversCheck, Holder.Covers]

def scopeCoversCheck {kind : ResourceKind} (scope : Scope kind)
    (request : Request kind) : Bool :=
  decide (request.target ∈ scope.targets) &&
    (decide (request.verb ∈ scope.verbs) &&
      decide (request.cost ≤ scope.maxCost))

@[simp] theorem scopeCoversCheck_eq_true_iff {kind : ResourceKind}
    (scope : Scope kind) (request : Request kind) :
    scopeCoversCheck scope request = true ↔ scope.Covers request := by
  simp only [scopeCoversCheck, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨target, verb, cost⟩
    exact ⟨target, verb, cost⟩
  · intro covers
    exact ⟨covers.target, covers.verb, covers.cost⟩

def capabilityIdsUnrevoked (state : AuthState)
    (ids : Finset CapabilityId) : Bool :=
  decide (∀ id ∈ ids, RevocationKey.capability id ∉ state.revoked)

theorem capabilityIdsUnrevoked_eq_true_iff (state : AuthState)
    (ids : Finset CapabilityId) :
    capabilityIdsUnrevoked state ids = true ↔
      ∀ id ∈ ids, RevocationKey.capability id ∉ state.revoked := by
  simp [capabilityIdsUnrevoked]

def channelIdsUnrevoked (state : AuthState)
    (ids : Finset ChannelId) : Bool :=
  decide (∀ id ∈ ids, RevocationKey.channel id ∉ state.revoked)

theorem channelIdsUnrevoked_eq_true_iff (state : AuthState)
    (ids : Finset ChannelId) :
    channelIdsUnrevoked state ids = true ↔
      ∀ id ∈ ids, RevocationKey.channel id ∉ state.revoked := by
  simp [channelIdsUnrevoked]

/-- Executable decision procedure for the EXISTING `Capability.Admissible`.
It is not a second semantic relation; `capabilityAdmissibleCheck_iff` below is
the reflection theorem. -/
def capabilityAdmissibleCheck {kind : ResourceKind} (cap : Capability kind)
    (state : AuthState) (request : Request kind) : Bool :=
  [holderCoversCheck cap.holder request.subject,
   scopeCoversCheck cap.scope request,
   decide (cap.notBefore ≤ request.height),
   decide (request.height ≤ cap.notAfter),
   decide (cap.policyId = request.policyId),
   decide (cap.policyEpoch = request.policyEpoch),
   decide (cap.policyEpoch = state.policyEpoch cap.policyId),
   decide (cap.issuerEpoch = state.issuerEpoch cap.issuer),
   decide (RevocationKey.capability cap.id ∉ state.revoked),
   capabilityIdsUnrevoked state cap.ancestors,
   channelIdsUnrevoked state cap.channels].all (fun accepted => accepted)

theorem Capability.admissible_iff_components {kind : ResourceKind}
    (cap : Capability kind) (state : AuthState) (request : Request kind) :
    cap.Admissible state request ↔
      cap.holder.Covers request.subject ∧
      cap.scope.Covers request ∧
      cap.notBefore ≤ request.height ∧
      request.height ≤ cap.notAfter ∧
      cap.policyId = request.policyId ∧
      cap.policyEpoch = request.policyEpoch ∧
      cap.policyEpoch = state.policyEpoch cap.policyId ∧
      cap.issuerEpoch = state.issuerEpoch cap.issuer ∧
      RevocationKey.capability cap.id ∉ state.revoked ∧
      (∀ ancestor ∈ cap.ancestors,
        RevocationKey.capability ancestor ∉ state.revoked) ∧
      (∀ channel ∈ cap.channels,
        RevocationKey.channel channel ∉ state.revoked) := by
  constructor
  · intro admitted
    exact ⟨admitted.holder, admitted.scope, admitted.validFrom,
      admitted.validUntil, admitted.policyId, admitted.policyEpoch,
      admitted.policyCurrent, admitted.issuerCurrent,
      admitted.selfNotRevoked, admitted.ancestorNotRevoked,
      admitted.channelNotRevoked⟩
  · rintro ⟨holder, scope, validFrom, validUntil, policyId, policyEpoch,
      policyCurrent, issuerCurrent, selfNotRevoked,
      ancestorNotRevoked, channelNotRevoked⟩
    exact
      { holder := holder
        scope := scope
        validFrom := validFrom
        validUntil := validUntil
        policyId := policyId
        policyEpoch := policyEpoch
        policyCurrent := policyCurrent
        issuerCurrent := issuerCurrent
        selfNotRevoked := selfNotRevoked
        ancestorNotRevoked := ancestorNotRevoked
        channelNotRevoked := channelNotRevoked }

@[simp] theorem capabilityAdmissibleCheck_eq_true_iff
    {kind : ResourceKind} (cap : Capability kind)
    (state : AuthState) (request : Request kind) :
    capabilityAdmissibleCheck cap state request = true ↔
      cap.Admissible state request := by
  rw [Capability.admissible_iff_components]
  simp [capabilityAdmissibleCheck, holderCoversCheck_eq_true_iff,
    scopeCoversCheck_eq_true_iff, capabilityIdsUnrevoked_eq_true_iff,
    channelIdsUnrevoked_eq_true_iff]

theorem CapabilityPresentation.verifyKey_eq_true_iff
    {portal : Portal} {kind : ResourceKind}
    (presentation : CapabilityPresentation portal kind)
    (root : Digest) (key : RevocationKey) :
    presentation.verifyKey root key = true ↔
      ∃ witness : portal.NonRevocationWitness,
        lookupRevocation key presentation.revocationOpenings = some witness ∧
        portal.verifyNonRevocation root key witness = true := by
  unfold CapabilityPresentation.verifyKey
  cases hlookup : lookupRevocation key presentation.revocationOpenings <;>
    simp [hlookup]

theorem CapabilityPresentation.verifyCapabilityIds_eq_true_iff
    {portal : Portal} {kind : ResourceKind}
    (presentation : CapabilityPresentation portal kind)
    (root : Digest) (ids : Finset CapabilityId) :
    presentation.verifyCapabilityIds root ids = true ↔
      ∀ id ∈ ids,
        ∃ witness : portal.NonRevocationWitness,
          lookupRevocation (.capability id) presentation.revocationOpenings =
              some witness ∧
          portal.verifyNonRevocation root (.capability id) witness = true := by
  simp [CapabilityPresentation.verifyCapabilityIds,
    CapabilityPresentation.verifyKey_eq_true_iff]

theorem CapabilityPresentation.verifyChannelIds_eq_true_iff
    {portal : Portal} {kind : ResourceKind}
    (presentation : CapabilityPresentation portal kind)
    (root : Digest) (ids : Finset ChannelId) :
    presentation.verifyChannelIds root ids = true ↔
      ∀ id ∈ ids,
        ∃ witness : portal.NonRevocationWitness,
          lookupRevocation (.channel id) presentation.revocationOpenings =
              some witness ∧
          portal.verifyNonRevocation root (.channel id) witness = true := by
  simp [CapabilityPresentation.verifyChannelIds,
    CapabilityPresentation.verifyKey_eq_true_iff]

def evalCheck {portal : Portal} {state : AuthState}
    {kind : ResourceKind} {request : Request kind}
    (presentation : Presentation portal request) : Check → Bool
  | .subjectKeyEpoch =>
      decide (request.subjectKeyEpoch = state.subjectKeyEpoch request.subject)
  | .signature => match presentation.evidence with
      | .signature witness => portal.verifySignature request witness
      | _ => false
  | .proof => match presentation.evidence with
      | .proof witness => portal.verifyProof request witness
      | _ => false
  | .capabilitySemantic => match presentation.evidence with
      | .capability capPresentation =>
          capabilityAdmissibleCheck capPresentation.cap state request
      | _ => false
  | .capabilityCommitment => match presentation.evidence with
      | .capability capPresentation =>
          portal.verifyCapabilityCommitment capPresentation.cap
            capPresentation.commitment capPresentation.commitmentWitness
      | _ => false
  | .capabilityMembership => match presentation.evidence with
      | .capability capPresentation =>
          portal.verifyMembership state.capabilityRoot
            capPresentation.commitment capPresentation.membershipWitness
      | _ => false
  | .issuer => match presentation.evidence with
      | .capability capPresentation =>
          portal.verifyIssuer capPresentation.cap.issuer
            capPresentation.cap.issuerEpoch capPresentation.commitment
            capPresentation.issuerWitness
      | _ => false
  | .selfNonRevocation => match presentation.evidence with
      | .capability capPresentation =>
          capPresentation.verifyKey state.revocationRoot
            (.capability capPresentation.cap.id)
      | _ => false
  | .ancestorNonRevocations => match presentation.evidence with
      | .capability capPresentation =>
          capPresentation.verifyCapabilityIds state.revocationRoot
            capPresentation.cap.ancestors
      | _ => false
  | .channelNonRevocations => match presentation.evidence with
      | .capability capPresentation =>
          capPresentation.verifyChannelIds state.revocationRoot
            capPresentation.cap.channels
      | _ => false
  | .policyEpoch =>
      decide (request.policyEpoch = state.policyEpoch request.policyId)
  | .policyAddress =>
      decide (portal.policyAddress presentation.policyWitness =
        state.policyAddress request.policyId request.policyEpoch)
  | .policyMembership =>
      portal.verifyMembership state.policyRoot
        (state.policyAddress request.policyId request.policyEpoch)
        presentation.policyMembershipWitness
  | .policy =>
      portal.verifyCommittedPolicy
        (state.policyAddress request.policyId request.policyEpoch)
        request presentation.policyWitness

/-! ## §5. Total executable verifier and proof layer -/

def runChecks (eval : Check → Bool) : List Check → Decision
  | [] => .accepted
  | check :: rest =>
      if eval check then runChecks eval rest else .rejected check

def verify {portal : Portal} {state : AuthState}
    {kind : ResourceKind} {request : Request kind}
    (presentation : Presentation portal request) : Decision :=
  runChecks (evalCheck (state := state) presentation)
    (checksFor presentation.evidence.mode)

/-- Proof-only view of acceptance.  This proposition is not part of
`declaration`; it is the theorem interface to the executable list. -/
def PlanSatisfied {portal : Portal} {state : AuthState}
    {kind : ResourceKind} {request : Request kind}
    (presentation : Presentation portal request) : Prop :=
  ∀ check ∈ checksFor presentation.evidence.mode,
    evalCheck (state := state) presentation check = true

theorem runChecks_accepted_iff (eval : Check → Bool) (checks : List Check) :
    runChecks eval checks = .accepted ↔
      ∀ check ∈ checks, eval check = true := by
  induction checks with
  | nil => simp [runChecks]
  | cons head tail ih =>
      by_cases h : eval head = true <;> simp [runChecks, h, ih]

theorem verify_accepted_iff {portal : Portal} {state : AuthState}
    {kind : ResourceKind} {request : Request kind}
    (presentation : Presentation portal request) :
    verify (state := state) presentation = .accepted ↔
      PlanSatisfied (state := state) presentation := by
  exact runChecks_accepted_iff _ _

/-- Acceptance of the emitted plan constructs the EXISTING request-indexed
authorization object.  This theorem is the boundary between first-order
decision data and proof-relevant semantics. -/
theorem planSatisfied_authorized {portal : Portal} {state : AuthState}
    {kind : ResourceKind} {request : Request kind}
    (presentation : Presentation portal request)
    (satisfied : PlanSatisfied (state := state) presentation) :
    Nonempty (Authorized portal state request) := by
  rcases presentation with ⟨presented, policyWitness, policyMembershipWitness⟩
  cases presented with
  | signature signatureWitness =>
      have hkey := satisfied .subjectKeyEpoch
        (by simp [PresentedEvidence.mode, checksFor])
      have hsignature := satisfied .signature
        (by simp [PresentedEvidence.mode, checksFor])
      have hpolicyEpoch := satisfied .policyEpoch
        (by simp [PresentedEvidence.mode, checksFor])
      have hpolicyAddress := satisfied .policyAddress
        (by simp [PresentedEvidence.mode, checksFor])
      have hpolicyMembership := satisfied .policyMembership
        (by simp [PresentedEvidence.mode, checksFor])
      have hpolicy := satisfied .policy
        (by simp [PresentedEvidence.mode, checksFor])
      refine ⟨{
        evidence := .signature signatureWitness ?_ ?_
        policyWitness := policyWitness
        policyMembershipWitness := policyMembershipWitness
        policyEpochExact := ?_
        policyAddressExact := ?_
        policyMembershipVerified := ?_
        policyVerified := ?_ }⟩
      · simpa [evalCheck] using hkey
      · simpa [evalCheck] using hsignature
      · simpa [evalCheck] using hpolicyEpoch
      · simpa [evalCheck] using hpolicyAddress
      · simpa [evalCheck] using hpolicyMembership
      · simpa [evalCheck] using hpolicy
  | proof proofWitness =>
      have hproof := satisfied .proof
        (by simp [PresentedEvidence.mode, checksFor])
      have hpolicyEpoch := satisfied .policyEpoch
        (by simp [PresentedEvidence.mode, checksFor])
      have hpolicyAddress := satisfied .policyAddress
        (by simp [PresentedEvidence.mode, checksFor])
      have hpolicyMembership := satisfied .policyMembership
        (by simp [PresentedEvidence.mode, checksFor])
      have hpolicy := satisfied .policy
        (by simp [PresentedEvidence.mode, checksFor])
      refine ⟨{
        evidence := .proof proofWitness ?_
        policyWitness := policyWitness
        policyMembershipWitness := policyMembershipWitness
        policyEpochExact := ?_
        policyAddressExact := ?_
        policyMembershipVerified := ?_
        policyVerified := ?_ }⟩
      · simpa [evalCheck] using hproof
      · simpa [evalCheck] using hpolicyEpoch
      · simpa [evalCheck] using hpolicyAddress
      · simpa [evalCheck] using hpolicyMembership
      · simpa [evalCheck] using hpolicy
  | capability capPresentation =>
      have hsemantic := satisfied .capabilitySemantic
        (by simp [PresentedEvidence.mode, checksFor])
      have hcommitment := satisfied .capabilityCommitment
        (by simp [PresentedEvidence.mode, checksFor])
      have hmembership := satisfied .capabilityMembership
        (by simp [PresentedEvidence.mode, checksFor])
      have hissuer := satisfied .issuer
        (by simp [PresentedEvidence.mode, checksFor])
      have hself := satisfied .selfNonRevocation
        (by simp [PresentedEvidence.mode, checksFor])
      have hancestors := satisfied .ancestorNonRevocations
        (by simp [PresentedEvidence.mode, checksFor])
      have hchannels := satisfied .channelNonRevocations
        (by simp [PresentedEvidence.mode, checksFor])
      have hpolicyEpoch := satisfied .policyEpoch
        (by simp [PresentedEvidence.mode, checksFor])
      have hpolicyAddress := satisfied .policyAddress
        (by simp [PresentedEvidence.mode, checksFor])
      have hpolicyMembership := satisfied .policyMembership
        (by simp [PresentedEvidence.mode, checksFor])
      have hpolicy := satisfied .policy
        (by simp [PresentedEvidence.mode, checksFor])
      have semantic : capPresentation.cap.Admissible state request :=
        (capabilityAdmissibleCheck_eq_true_iff
          capPresentation.cap state request).mp
          (by simpa [evalCheck] using hsemantic)
      have selfOpening :=
        (capPresentation.verifyKey_eq_true_iff state.revocationRoot
          (.capability capPresentation.cap.id)).mp
          (by simpa [evalCheck] using hself)
      rcases selfOpening with ⟨selfWitness, -, selfVerified⟩
      have ancestorsVerified :=
        (capPresentation.verifyCapabilityIds_eq_true_iff
          state.revocationRoot capPresentation.cap.ancestors).mp
          (by simpa [evalCheck] using hancestors)
      have channelsVerified :=
        (capPresentation.verifyChannelIds_eq_true_iff
          state.revocationRoot capPresentation.cap.channels).mp
          (by simpa [evalCheck] using hchannels)
      refine ⟨{
        evidence := .capability capPresentation.cap capPresentation.commitment
          capPresentation.commitmentWitness capPresentation.membershipWitness
          capPresentation.issuerWitness selfWitness semantic ?_ ?_ ?_ selfVerified
          ?_ ?_
        policyWitness := policyWitness
        policyMembershipWitness := policyMembershipWitness
        policyEpochExact := ?_
        policyAddressExact := ?_
        policyMembershipVerified := ?_
        policyVerified := ?_ }⟩
      · simpa [evalCheck] using hcommitment
      · simpa [evalCheck] using hmembership
      · simpa [evalCheck] using hissuer
      · intro ancestor hmem
        rcases ancestorsVerified ancestor hmem with ⟨witness, -, verified⟩
        exact ⟨witness, verified⟩
      · intro channel hmem
        rcases channelsVerified channel hmem with ⟨witness, -, verified⟩
        exact ⟨witness, verified⟩
      · simpa [evalCheck] using hpolicyEpoch
      · simpa [evalCheck] using hpolicyAddress
      · simpa [evalCheck] using hpolicyMembership
      · simpa [evalCheck] using hpolicy

theorem verify_accepted_authorized {portal : Portal} {state : AuthState}
    {kind : ResourceKind} {request : Request kind}
    (presentation : Presentation portal request)
    (accepted : verify (state := state) presentation = .accepted) :
    Nonempty (Authorized portal state request) :=
  planSatisfied_authorized presentation
    ((verify_accepted_iff presentation).mp accepted)

/-! ## §6. Small declaration/program teeth -/

example : declaration.requestFields.length = 16 := by decide

example : (checksFor .signature).getLast? = some .policy := rfl
example : (checksFor .proof).getLast? = some .policy := rfl
example : (checksFor .capability).getLast? = some .policy := rfl

/-- Mode-specific verification cannot skip the common policy suffix. -/
theorem checksFor_policy_suffix (mode : Mode) :
    ∃ headChecks, checksFor mode = headChecks ++
      [.policyEpoch, .policyAddress, .policyMembership, .policy] := by
  cases mode
  · exact ⟨[.subjectKeyEpoch, .signature], rfl⟩
  · exact ⟨[.proof], rfl⟩
  · exact ⟨[.capabilitySemantic, .capabilityCommitment,
      .capabilityMembership, .issuer, .selfNonRevocation,
      .ancestorNonRevocations, .channelNonRevocations], rfl⟩

end Minidregg.Theory.AuthorizationDeclaration
