/-
# Kernel.NativeThinConsent — what thin consent shows is what commits

A full-peer consent provider (`Kernel.NativeClientConsent`) re-runs the planner
over the whole replayed image. A thin consent client cannot: the planner opens by
decoding the WHOLE authority cell (`CredentialAuthorityDomainReceiver.loadDeployment`),
every subject's keys, capabilities and policies, which no member may be served.

Thin consent does not need the planner. Authorization is admission's job, and a
gate can only refuse. Consent's job is that what it DISPLAYS is what COMMITS. For
an invocation, a target's committed post is the target patch
(`DeclaredResourceController.targetPatch`) run on the target's pre-state. Its
inputs are:

* the command, which the member wrote and signs (the command bytes are hashed into
  the signed request's `argsDigest` and `effectsDigest`);
* the target's pre-state, which the signed command pins by its logical root
  (`Target.expectedTargetRoot`), and which the executor checks against the loaded
  cell (`computeTarget`: `staleTarget`; `DeclaredResourceScalar.prepareCell`:
  `CellMode.rootExact`);
* for a scalar write, the admission height, which feeds only the kernel's
  blinding ratchet at one address (`DeclaredEffectCell.blinding`). That height is
  not signed (`TypedAuthorizationRequestCodec.planOf` zeroes it), so thin consent
  does not display that address. It refuses nothing on that account and defaults
  nothing: the address is kernel-owned (`KernelOwned`), and the theorem excludes
  exactly it.

Thin consent takes the served bytes of each target, checks that the deployed
logical root of those bytes is the root the signed command names (refusing
`servedRootMismatch` otherwise), and runs `memberPatch`. That is the part of
`targetPatch` whose inputs are all signed or served (`targetPatch_split`). A
payload whose patch has any other input (content, which reads the authority
snapshot's policy coordinates and the height; a stream append, which records the
height; money and compute legs, which write the shared Book) is refused by name.
It is not displayed with a default. The full-peer provider still covers those.

## Theorem

`thin_display_is_commit`: for an executor-prepared target (`PreparedTarget`, the
receiver's own object, built by `prepareTarget` from the loaded image at
admission), if thin consent accepted served bytes for it, then the committed post
equals the displayed post at every address that is not kernel-owned. The one
premise is `RootBinds`, scoped to two byte strings under the DEPLOYED
root function of that target's materializer (`Target.materializer.rootBytes`:
`StoreCodec.rootBytes` for declared cells, the world-kind materializers for world
cells). It is inhabited by the honest Host (`honest_binds`: the executor's own
pre bytes) and is a carrier, not an identity: it fails exactly at a collision of
that cSHAKE root.
-/
import Kernel.ResourceTransaction
import Kernel.NativeObservationController

namespace Minidregg.Kernel.NativeThinConsent

open Minidregg.Compiler
open Minidregg.Theory
open Minidregg.Theory.CellState
open Minidregg.Theory.Store
open Minidregg.Theory.TypedAuthorization
open Minidregg.Kernel.DeclaredResourceController
open Minidregg.Theory.AuthorizationDeclaration (SomeRequest)
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Theory.CredentialAuthorityState (readCapability isRegistered StoredCapability)
open Minidregg.Theory.CredentialAuthorityEffects (delegatedCapability DelegateDeclaration
  apply_creation_member registrationEntry setAll_frame run_assignAll)

set_option autoImplicit false

/-- Why thin consent refused to display a target. -/
inductive Refusal where
  /-- The payload's committed post has an input that is neither signed nor served. -/
  | unsupportedPayload (target : Nat) (what : String)
  /-- The served bytes are not a canonical store of the target's layout. -/
  | servedMalformed (target : Nat)
  /-- The served bytes' deployed logical root is not the root the signed command names. -/
  | servedRootMismatch (target : Nat)
  /-- The member patch does not apply to the served pre-state; admission would refuse. -/
  | patchRefused (target : Nat)
  /-- Thin consent cannot display this kind of draft. -/
  | notInvocation
  /-- A delegation reads no served view; the Host supplied one. -/
  | viewUnexpected
  | commandMalformed
  | planMalformed
  /-- The proposed plan's domain, semantics or finalized draft is not this
  deployment's and this intent's. -/
  | planCoordinates
  /-- The proposed plan's slots are not the invocation's roles in order. -/
  | slotShape
  | challengeMalformed
  /-- The proposed challenge is not for this intent, signature or deployment. -/
  | challengeCoordinates
  | headerMalformed (slot : Nat)
  /-- A member-derived field of a header differs from the local derivation. -/
  | headerMismatch (slot : Nat)
  /-- No view, or a malformed one, was served for a target. -/
  | viewMissing (target : Nat)
  | viewMalformed (target : Nat)
  /-- The served view does not hold this target's role. -/
  | viewRole (target : Nat)
  deriving DecidableEq, Repr

/-- The part of a target's patch that the member authored: every input is the
signed command or the served pre-state. -/
def memberPatch (command : Command) (target : Target) (pre : Store target.layout) :
    Except Refusal (Patch target.layout) := by
  cases target with
  | mk kind id capability version root payload observe audienceEpoch audienceRoster =>
    cases payload with
    | scalar actions =>
        exact .ok (DeclaredResourceScalar.cellPatch (scalarCommand command
          ⟨kind, id, capability, version, root, .scalar actions, observe, audienceEpoch, audienceRoster⟩
          actions))
    | world actions =>
        exact match WorldKindCell.preparePatch pre actions with
          | some patch => .ok patch
          | none => .error (.patchRefused id)
    | kindDefinition definition =>
        exact match WorldKindCell.prepareDefinition pre definition with
          | some patch => .ok patch
          | none => .error (.patchRefused id)
    | read => exact .ok []
    | kindRead => exact .ok []
    | content _ => exact .error (.unsupportedPayload id "content: reads policy coordinates and the height")
    | append _ => exact .error (.unsupportedPayload id "append: records the admission height")
    | computeFunding _ => exact .error (.unsupportedPayload id "compute funding: writes the shared Book")
    | moneyConsent _ => exact .error (.unsupportedPayload id "money: writes the shared Book")

/-- The addresses the kernel writes from an input the member did not sign: a
scalar target's blinding ratchet (admission height). -/
def KernelOwned (target : Target) (address : Address target.layout) : Prop := by
  cases target with
  | mk kind id capability version root payload observe audienceEpoch audienceRoster =>
    cases payload with
    | scalar _ => exact address = DeclaredEffectCell.blinding.address
    | _ => exact False

/-- **The split.** Whatever the authority snapshot and admission height, a
supported target's patch is the member patch followed by a tail that writes only
kernel-owned addresses. -/
theorem targetPatch_split (snapshot : AuthoritySnapshot) (semantics : Digest) (ambient : Ambient)
    (command : Command) (target : Target) (pre : TargetCell target) (patch : Patch target.layout)
    (member : memberPatch command target pre.logical = .ok patch) :
    ∃ tail : Patch target.layout,
      targetPatch snapshot semantics ambient command target pre = patch ++ tail ∧
      ∀ (store : Store target.layout) (address : Address target.layout),
        ¬ KernelOwned target address → Patch.run store tail address = store address := by
  cases target with
  | mk kind id capability version root payload observe audienceEpoch audienceRoster =>
    cases payload with
    | scalar actions =>
        simp only [memberPatch, Except.ok.injEq] at member
        subst member
        refine ⟨DeclaredEffectCell.blinding.patch pre.logical ambient.height, rfl, ?_⟩
        intro store address owned
        exact DeclaredEffectCell.blinding.run_patch_frame store pre.logical ambient.height address owned
    | world actions =>
        simp only [memberPatch] at member
        split at member
        · rename_i prepared found
          simp only [Except.ok.injEq] at member
          subst member
          refine ⟨[], ?_, fun _ _ _ => rfl⟩
          simp only [targetPatch, found, Option.getD_some]
          exact (List.append_nil _).symm
        · cases member
    | kindDefinition definition =>
        simp only [memberPatch] at member
        split at member
        · rename_i prepared found
          simp only [Except.ok.injEq] at member
          subst member
          refine ⟨[], ?_, fun _ _ _ => rfl⟩
          simp only [targetPatch, found, Option.getD_some]
          exact (List.append_nil _).symm
        · cases member
    | read =>
        simp only [memberPatch, Except.ok.injEq] at member
        subst member
        exact ⟨[], rfl, fun _ _ _ => rfl⟩
    | kindRead =>
        simp only [memberPatch, Except.ok.injEq] at member
        subst member
        exact ⟨[], rfl, fun _ _ _ => rfl⟩
    | content _ => simp [memberPatch] at member
    | append _ => simp [memberPatch] at member
    | computeFunding _ => simp [memberPatch] at member
    | moneyConsent _ => simp [memberPatch] at member

#assert_axioms targetPatch_split

/-- **A payload with an unsigned input is refused by name, never displayed
with a default.** -/
theorem memberPatch_money_refused (command : Command) (kind : ResourceKind) (id : Nat)
    (capability : CapabilityId) (version : Nat) (root : Digest) (consent : MoneyConsent)
    (observe : Option CapabilityId) (audienceEpoch : Option Nat)
    (audienceRoster : Option Minidregg.Theory.ObjectAudienceRoster.Roster)
    (pre : Store EffectDeclaration.effectLayout) :
    memberPatch command ⟨kind, id, capability, version, root, .moneyConsent consent, observe,
      audienceEpoch, audienceRoster⟩ pre =
      .error (.unsupportedPayload id "money: writes the shared Book") := rfl

#assert_axioms memberPatch_money_refused

/-- The payloads whose committed post thin consent can display. -/
def Supported (target : Target) : Prop :=
  match target.payload with
  | .scalar _ | .world _ | .kindDefinition _ | .read | .kindRead => True
  | _ => False

theorem memberPatch_supported (command : Command) (target : Target) (store : Store target.layout)
    (patch : Patch target.layout) (member : memberPatch command target store = .ok patch) :
    Supported target := by
  cases target with
  | mk kind id capability version root payload observe audienceEpoch audienceRoster =>
    cases payload <;> simp_all [memberPatch, Supported]

/-- **The executor binds the signed root.** Every payload thin consent displays
is computed by the executor only when the loaded cell's logical root is the root
the signed command names (`staleTarget` otherwise). -/
theorem computeTarget_root (snapshot : AuthoritySnapshot) (semantics : Digest) (ambient : Ambient)
    (command : Command) (target : Target) (pre : TargetCell target) (post : target.Outcome)
    (computed : computeTarget snapshot semantics ambient command target pre = .ok post)
    (supported : Supported target) :
    target.expectedTargetRoot = pre.root := by
  cases target with
  | mk kind id capability version root payload observe audienceEpoch audienceRoster =>
    cases payload with
    | scalar actions =>
        simp only [computeTarget] at computed
        split at computed
        · cases computed
        · rename_i cell _
          exact cell.candidate.modeEvidence.rootExact
    | world actions =>
        by_contra moved
        have hb : (root != pre.root) = true := bne_iff_ne.mpr moved
        simp only [computeTarget, hb, if_true] at computed
        split_ifs at computed <;> simp [bind, Except.bind, pure, Except.pure] at computed
    | kindDefinition definition =>
        by_contra moved
        have hb : (root != pre.root) = true := bne_iff_ne.mpr moved
        simp only [computeTarget, hb, if_true] at computed
        split_ifs at computed <;> simp [bind, Except.bind, pure, Except.pure] at computed
    | read =>
        by_contra moved
        have hb : (root != pre.root) = true := bne_iff_ne.mpr moved
        simp only [computeTarget, hb, if_true] at computed
        split_ifs at computed <;> simp [bind, Except.bind, pure, Except.pure] at computed
    | kindRead =>
        by_contra moved
        have hb : (root != pre.root) = true := bne_iff_ne.mpr moved
        simp only [computeTarget, hb, if_true] at computed
        split_ifs at computed <;> simp [bind, Except.bind, pure, Except.pure] at computed
    | content _ => exact supported.elim
    | append _ => exact supported.elim
    | computeFunding _ => exact supported.elim
    | moneyConsent _ => exact supported.elim

/-- What thin consent displays for one target, from the bytes the Host served:
canonical bytes of the target's layout whose DEPLOYED logical root is the root
the signed command names, and the member patch run on them. -/
def checkServed (command : Command) (target : Target) (bytes : List UInt8) :
    Except Refusal (Store target.layout) :=
  match target.materializer.codec.decode bytes with
  | none => .error (.servedMalformed target.target)
  | some logical =>
      if target.materializer.rootBytes bytes = target.expectedTargetRoot then
        match memberPatch command target logical with
        | .error refusal => .error refusal
        | .ok patch =>
            if Patch.ValidFrom logical patch then .ok (Patch.run logical patch)
            else .error (.patchRefused target.target)
      else .error (.servedRootMismatch target.target)

/-- The carrier, scoped to one pair of byte strings: the deployed root function
separates them. -/
def RootBinds (rootBytes : List UInt8 → Digest) (served actual : List UInt8) : Prop :=
  rootBytes served = rootBytes actual → served = actual

/-- **Inhabited by the honest Host.** Serving the executor's own pre bytes meets
the carrier at every root function. -/
theorem honest_binds (rootBytes : List UInt8 → Digest) (actual : List UInt8) :
    RootBinds rootBytes actual actual := fun _ => rfl

/-- **A served-root mismatch refuses by name.** -/
theorem mismatch_refused (command : Command) (target : Target) (bytes : List UInt8)
    (logical : Store target.layout) (decoded : target.materializer.codec.decode bytes = some logical)
    (mismatch : target.materializer.rootBytes bytes ≠ target.expectedTargetRoot) :
    checkServed command target bytes = .error (.servedRootMismatch target.target) := by
  simp [checkServed, decoded, mismatch]

/-- The executor's committed post is the target patch run on the loaded pre-state. -/
theorem post_run {deployment : Deployment} {directory : CellRegistry.Directory Nat Registry}
    {snapshot : AuthoritySnapshot} {semantics : Digest} {ambient : Ambient}
    {command : Command} {target : Target}
    (prepared : PreparedTarget deployment directory snapshot semantics ambient command target) :
    prepared.post = Patch.run prepared.pre.logical
      (targetPatch snapshot semantics ambient command target prepared.pre) := by
  rw [← prepared.postExact]
  rfl

/-- **What thin consent shows is what commits.** For the executor's own prepared
target, served bytes that thin consent accepted give, at every address that is
not kernel-owned, exactly the post the executor commits. -/
theorem thin_display_is_commit {deployment : Deployment} {directory : CellRegistry.Directory Nat Registry}
    {snapshot : AuthoritySnapshot} {semantics : Digest} {ambient : Ambient}
    {command : Command} {target : Target}
    (prepared : PreparedTarget deployment directory snapshot semantics ambient command target)
    {bytes : List UInt8} {shown : Store target.layout}
    (checked : checkServed command target bytes = .ok shown)
    (binds : RootBinds target.materializer.rootBytes bytes
      (target.materializer.codec.encode prepared.pre.logical)) :
    ∀ address, ¬ KernelOwned target address → prepared.post address = shown address := by
  intro address owned
  unfold checkServed at checked
  split at checked
  · cases checked
  · rename_i logical decoded
    split at checked
    · rename_i rooted
      split at checked
      · cases checked
      · rename_i patch member
        split at checked
        · simp only [Except.ok.injEq] at checked
          subst checked
          have supported := memberPatch_supported command target logical patch member
          have signedRoot := computeTarget_root snapshot semantics ambient command target prepared.pre
            prepared.post prepared.candidate.modeEvidence.down supported
          have same : bytes = target.materializer.codec.encode prepared.pre.logical :=
            binds (by rw [rooted, signedRoot]; rfl)
          have sameLogical : logical = prepared.pre.logical := by
            rw [same, target.materializer.codec.decode_encode] at decoded
            exact (Option.some.inj decoded).symm
          subst sameLogical
          obtain ⟨tail, split, frame⟩ :=
            targetPatch_split snapshot semantics ambient command target prepared.pre patch member
          rw [post_run prepared, split, Patch.run_append]
          exact frame _ address owned
        · cases checked
    · cases checked

#assert_axioms memberPatch_supported computeTarget_root honest_binds mismatch_refused
  post_run thin_display_is_commit

/-! ## Headers: every member-derived field is recomputed locally

A signing header carries the request it signs (`header.message`, the PLAN frame:
`TypedAuthorizationRequestCodec.planOf` zeroes the admission height and the
pre-state root). Thin consent decodes it, then rebuilds the request from its OWN
command and deployment, taking from the proposal only the three authority
coordinates it cannot know (`subjectKeyEpoch`, `policyEpoch`, `policyRevision`),
and the header's key selection, footprint, validity window and codec version.
Each of those is a gate: admission recomputes the request and the footprint from
the real authority cell, and a lie refuses (`wrongMessage`, `footprintStale`,
`unknownKey`, `expired`). It can never select a different effect. -/

/-- The request a header signs, when it is in the PLAN frame. -/
def signedRequest (message : List UInt8) : Option SomeRequest :=
  if message.take TypedAuthorizationRequestCodec.requestFrame.length =
      TypedAuthorizationRequestCodec.requestFrame then
    TypedAuthorizationRequestCodec.someRequestCodec.decode
      (message.drop TypedAuthorizationRequestCodec.requestFrame.length)
  else none

/-- The locally derived request, with the proposal's three authority coordinates. -/
def expectedRequest (decoded : SomeRequest) {kind : ResourceKind} (values : Request kind) : SomeRequest :=
  let gated : Request kind := { values with
    subjectKeyEpoch := decoded.2.subjectKeyEpoch
    policyEpoch := decoded.2.policyEpoch
    policyRevision := decoded.2.policyRevision }
  ⟨kind, gated⟩

/-- One header against its local derivation: same signature domain, same
operation marker, and a signed request that differs from `values` only in the
three authority coordinates. -/
def checkHeader (slot : Nat) (marker : Nat) {kind : ResourceKind} (values : Request kind)
    (bytes : List UInt8) : Except Refusal Unit :=
  match CredentialSignedEnvelopeController.headerCodec.decode bytes with
  | none => .error (.headerMalformed slot)
  | some header =>
      match signedRequest header.message with
      | none => .error (.headerMalformed slot)
      | some decoded =>
          let expected := { header with
            domain := CredentialSignatureAdmission.signatureDomain
            message := CredentialSignatureAdmission.requestBytes (expectedRequest decoded values)
            nullifier := marker }
          if CredentialSignedEnvelopeController.headerCodec.encode expected = bytes then .ok ()
          else .error (.headerMismatch slot)

/-- **An accepted header signs the local derivation.** -/
theorem checkHeader_binds {slot marker : Nat} {kind : ResourceKind} {values : Request kind}
    {bytes : List UInt8} (accepted : checkHeader slot marker values bytes = .ok ()) :
    ∃ header decoded, CredentialSignedEnvelopeController.headerCodec.decode bytes = some header ∧
      header.domain = CredentialSignatureAdmission.signatureDomain ∧
      header.message = CredentialSignatureAdmission.requestBytes (expectedRequest decoded values) ∧
      header.nullifier = marker := by
  unfold checkHeader at accepted
  split at accepted
  · cases accepted
  · rename_i header decodedHeader
    split at accepted
    · cases accepted
    · rename_i decoded _
      dsimp only at accepted
      split at accepted
      · rename_i encoded
        have again := CredentialSignedEnvelopeController.headerCodec.decode_encode
          { header with
            domain := CredentialSignatureAdmission.signatureDomain
            message := CredentialSignatureAdmission.requestBytes (expectedRequest decoded values)
            nullifier := marker }
        rw [encoded, decodedHeader] at again
        have same := Option.some.inj again
        refine ⟨header, decoded, decodedHeader, ?_, ?_, ?_⟩ <;> rw [same]
      · cases accepted

/-- A write or read leg's member-derived request (`requestFor`, by its reference
form `requestForReference`; the authority coordinates and the zeroed height and
pre-root are placeholders the comparison never reads). -/
def legValues (domain semantics : Digest) (federation : FederationId) (command : Command)
    (target : Target) : Request target.kind where
  domain := domain
  semantics := semantics
  federation := federation
  subject := command.subject
  subjectKeyEpoch := 0
  target := ⟨target.target⟩
  verb := target.verb
  argsDigest := argsDigest domain semantics command
  effectsDigest := effectsDigest domain semantics command
  nonce := command.nonce
  height := 0
  preStateRoot := ⟨0⟩
  policyId := ⟨target.target⟩
  policyEpoch := 0
  policyRevision := 0
  cost := requestCost (commandCodec.encode command) target

/-- A participant's observation leg (`readRequest`). -/
def observeValues (domain semantics : Digest) (federation : FederationId) (command : Command)
    (target : Target) : Request target.kind :=
  { legValues domain semantics federation command target with
    verb := observeVerb target.kind
    effectsDigest := (Sp800185Cshake256.hash "DREGG.RESOURCE.TRANSACTION.OBSERVE/v3".toUTF8.toList
      ((StreamCodec.product bytesStream StreamCodec.nat).encode
        (commandBytes domain semantics command, target.target))).digest }

/-- What thin consent shows for one target: its id and, for a write, the
canonical bytes and deployed root of the post at every member-authored address
(kernel-owned addresses as the served pre-state held them). -/
structure Display where
  target : Nat
  post : Option (List UInt8 × Digest)
  deriving DecidableEq, Repr

/-- The served view of one target, reduced to the canonical bytes of its typed
store, under the same role selection the executor uses (`selectTarget`). -/
def servedBytes (deployment : Deployment) (target : Target) (view : List UInt8) :
    Except Refusal (List UInt8) :=
  match NativeObservationController.resourceViewCodec.decode view with
  | none => .error (.viewMalformed target.target)
  | some (_, packedBytes, _, _, _) =>
      match CanonicalCellRegistry.cellCodec.decode packedBytes with
      | none => .error (.viewMalformed target.target)
      | some packed =>
          match selectTarget deployment target packed with
          | none => .error (.viewRole target.target)
          | some cell => .ok (target.materializer.codec.encode cell.logical)

/-- One target: its served bytes checked (`checkServed`) and its display. -/
def displayTarget (deployment : Deployment) (command : Command) (target : Target)
    (view : List UInt8) : Except Refusal Display := do
  let bytes ← servedBytes deployment target view
  let shown ← checkServed command target bytes
  if target.isRead then pure ⟨target.target, none⟩
  else
    let encoded := target.materializer.codec.encode shown
    pure ⟨target.target, some (encoded, target.materializer.rootBytes encoded)⟩

/-- **Thin invocation consent.** The proposed plan is this deployment's plan of
this intent's own invocation; every slot is the invocation's role in order and
every header signs the local derivation; every target's served view has the
signed root, and its member patch applies. Returns the headers to sign and what
to show. -/
def checkInvokeThin (deployment : Deployment) (semantics : Digest) (federation : FederationId)
    (commandBytes : List UInt8) (planBytes : List UInt8)
    (views : List (List UInt8)) : Except Refusal (List (List UInt8) × List Display) := do
  let some command := commandCodec.decode commandBytes | .error .commandMalformed
  let some plan := NativeHostCodec.signingPlanCodec.decode planBytes | .error .planMalformed
  unless plan.domain = deployment.domain ∧ plan.semantics = semantics ∧
      plan.finalizedDraft = .invoke commandBytes do .error .planCoordinates
  let domain := deployment.domain
  let marker := operationMarker domain semantics command
  let targets := command.targets
  let observeCount := if command.requiresObservation then targets.length else 0
  unless plan.slots.length = targets.length + observeCount + 1 do .error .slotShape
  unless views.length = targets.length do .error (.viewMissing (targets.length))
  let indexed := (List.range targets.length).zip targets
  -- write and read legs: role 4, then observation legs: role 8, then the authority leg: role 1
  let expected : List (Nat × Nat × Σ kind, Request kind) :=
    indexed.map (fun (i, target) => (4, i, ⟨target.kind, legValues domain semantics federation command target⟩)) ++
    (if command.requiresObservation then
      indexed.map (fun (i, target) => (8, i, ⟨target.kind, observeValues domain semantics federation command target⟩))
    else []) ++
    [(1, 0, ⟨command.first.kind, legValues domain semantics federation command command.first⟩)]
  for (slotIndex, slot, (role, index, values)) in (List.range plan.slots.length).zip (plan.slots.zip expected) do
    unless slot.role = role ∧ slot.index = index do .error .slotShape
    checkHeader slotIndex marker values.2 slot.header
  let displays ← (targets.zip views).mapM fun (target, view) => displayTarget deployment command target view
  pure (plan.slots.map NativeHostCodec.SigningSlot.header, displays)

/-! ## Thin delegation consent

A delegation writes two authority addresses
(`DelegateDeclaration.patch_writeFootprint`): the child capability's record and
its registration. The record is `delegatedCapability child parent request`:

* its head is the signed child (grantee, rights, expiry, caveats, policy), shown;
* its ancestry is `(parent.head, delegated request) :: parent.ancestry`, a
  deterministic copy of the parent the signed `parentId` names, read by the
  executor from the actual pre-state (`DescentEvidence.parentExact`). It is
  KERNEL-OWNED: not shown, and not signed beyond the parent's id.

So thin consent needs no served view. Whether the parent exists, belongs to the
signer, is live and anchored, and whether the child's rights narrow it, are
admission GATES on the actual pre-state (`delegate_gate_refuse_only`): they can
refuse, never select a different shown effect. The declaration signs no
authority-cell root (delegation command v2). -/

/-- What thin consent shows for a delegation: the signed parent id and target,
and the canonical bytes of the signed child capability. -/
structure DelegateDisplay where
  kind : ResourceKind
  parentId : CapabilityId
  target : Nat
  child : List UInt8
  deriving DecidableEq

/-- The delegation request the member derives from its own command; the four
authority coordinates and the zeroed height and pre-root are placeholders
`checkHeader` does not compare (`delegateValues_exact`). -/
def delegateValues (domain semantics : Digest) (federation : FederationId) {kind : ResourceKind}
    (command : CapabilityDelegationController.Command kind) : Request kind where
  domain := domain
  semantics := semantics
  federation := federation
  subject := command.subject
  subjectKeyEpoch := 0
  target := command.declaration.target
  verb := CredentialAuthorityFamily.delegateVerb kind
  argsDigest := (Sp800185Cshake256.hash "DREGG.CAPABILITY.DELEGATE.ARGS/v1".toUTF8.toList
    (CapabilityDelegationController.commandBytes domain semantics command command.declaration ++
      (CapabilityDelegationController.declarationCodec kind).encode command.declaration)).digest
  effectsDigest := CapabilityDelegationController.effectsDigest domain semantics command command.declaration
  nonce := command.declaration.operationNullifier
  height := 0
  preStateRoot := ⟨0⟩
  policyId := command.declaration.child.policyId
  policyEpoch := 0
  policyRevision := 0
  cost := (CapabilityDelegationController.commandCodec.encode ⟨kind, command⟩).length

/-- **The member derivation is the executor's request**, except at the fields
admission recomputes from the actual authority cell (and the plan frame zeroes
height and pre-root). -/
theorem delegateValues_exact (snapshot : CapabilityDelegationController.Snapshot) (semantics : Digest)
    (ambient : CapabilityDelegationController.Ambient) {kind : ResourceKind}
    (command : CapabilityDelegationController.Command kind) :
    CapabilityDelegationController.request snapshot semantics ambient command =
      { delegateValues snapshot.domain semantics ambient.federation command with
        subjectKeyEpoch := snapshot.authState.subjectKeyEpoch command.subject
        height := ambient.height
        preStateRoot := snapshot.cell.root
        policyEpoch := command.declaration.child.policyEpoch
        policyRevision := CredentialAuthorityState.policyRevisionAt snapshot.cell
          command.declaration.child.policyId } := rfl

/-- **Thin delegation consent.** The plan is this deployment's plan of this
intent's own delegation command: one slot, role 6, whose header signs the local
derivation. No view is read. -/
def checkDelegateThin (deployment : Deployment) (semantics : Digest) (federation : FederationId)
    (commandBytes : List UInt8) (planBytes : List UInt8) (views : List (List UInt8)) :
    Except Refusal (List (List UInt8) × DelegateDisplay) :=
  match CapabilityDelegationController.commandCodec.decode commandBytes with
  | none => .error .commandMalformed
  | some ⟨kind, command⟩ =>
    match NativeHostCodec.signingPlanCodec.decode planBytes with
    | none => .error .planMalformed
    | some plan =>
      if plan.domain = deployment.domain ∧ plan.semantics = semantics ∧
          plan.finalizedDraft = .delegate commandBytes then
        if views.isEmpty then
          match plan.slots with
          | [slot] =>
            if slot.role = 6 ∧ slot.index = 0 then
              match checkHeader 0
                  (CapabilityDelegationController.operationMarker deployment.domain semantics command)
                  (delegateValues deployment.domain semantics federation command) slot.header with
              | .error refusal => .error refusal
              | .ok () => .ok ([slot.header], ⟨kind, command.declaration.parentId,
                  command.declaration.target.value,
                  (CredentialAuthorityEntryCodec.capabilityStream kind).encode command.declaration.child⟩)
            else .error .slotShape
          | _ => .error .slotShape
        else .error .viewUnexpected
      else .error .planCoordinates

/-- The shown display is the signed command's: its parent id, target and child. -/
theorem checkDelegateThin_shows {deployment : Deployment} {semantics : Digest}
    {federation : FederationId} {commandBytes planBytes : List UInt8} {views : List (List UInt8)}
    {headers : List (List UInt8)} {shown : DelegateDisplay}
    (checked : checkDelegateThin deployment semantics federation commandBytes planBytes views =
      .ok (headers, shown)) :
    ∃ kind command, CapabilityDelegationController.commandCodec.decode commandBytes =
        some ⟨kind, command⟩ ∧
      shown = ⟨kind, command.declaration.parentId, command.declaration.target.value,
        (CredentialAuthorityEntryCodec.capabilityStream kind).encode command.declaration.child⟩ := by
  unfold checkDelegateThin at checked
  split at checked
  · cases checked
  · rename_i kind command decoded
    refine ⟨kind, command, decoded, ?_⟩
    split at checked
    · cases checked
    · split at checked
      · split at checked
        · split at checked
          · split at checked
            · split at checked
              · cases checked
              · simp only [Except.ok.injEq, Prod.mk.injEq] at checked
                exact checked.2.symm
            · cases checked
          · cases checked
        · cases checked
      · cases checked

/-- The two addresses a delegation writes. -/
def delegateFootprint {kind : ResourceKind} (child : CapabilityId) :
    List (Address CredentialAuthorityState.layout) :=
  [⟨.capability kind, child⟩, ⟨.registered, .capability child⟩]

variable {F : Type} [Field F] {deployment : Deployment}
  {profile : CanonicalRuntimeProfile.Profile F}

/-- **What a thin delegation shows is what commits.** For the executor's own
prepared delegation of the signed command (`CapabilityDelegationController.Prepared`,
built by `prepare` from the loaded authority cell at admission):

* the child's record is written with the SHOWN head (the signed child) and the
  kernel-owned lineage: a copy of the parent at the signed `parentId`, read from
  the actual pre-state;
* the child's revocation key is registered;
* every other authority address is exactly the pre-state's. -/
theorem delegate_display_is_commit {ambient : CapabilityDelegationController.Ambient}
    {ground : CapabilityDelegationController.Ground deployment} {kind : ResourceKind}
    {command : CapabilityDelegationController.Command kind}
    (prepared : CapabilityDelegationController.Prepared deployment profile ambient ground command) :
    readCapability prepared.authorityPost kind command.declaration.child.id =
        some (delegatedCapability command.declaration.child prepared.parent
          (CapabilityDelegationController.request ground.authority profile.semantics
            ambient command)) ∧
      readCapability ground.authority.cell kind command.declaration.parentId =
        some prepared.parent ∧
      isRegistered prepared.authorityPost (.capability command.declaration.child.id) = true ∧
      ∀ address, address ∉ delegateFootprint (kind := kind) command.declaration.child.id →
        prepared.authorityPost.logical address = ground.authority.cell.logical address := by
  have entryWritten := apply_creation_member prepared.validated rfl
    (command.declaration.capabilityEntry prepared.parent
      (CapabilityDelegationController.request ground.authority profile.semantics ambient command))
    (by simp)
  have registrationWritten := apply_creation_member prepared.validated rfl
    (registrationEntry (.capability command.declaration.child.id)) (by simp)
  refine ⟨entryWritten, prepared.descent.parentExact, ?_, ?_⟩
  · simp only [registrationEntry] at registrationWritten
    change (prepared.validated.apply.logical
      ⟨.registered, .capability command.declaration.child.id⟩).isSome = true
    exact (congrArg Option.isSome registrationWritten).trans rfl
  · intro address outside
    change prepared.validated.apply.logical address = _
    rw [CellState.ValidatedPatch.apply_logical]
    unfold DelegateDeclaration.patch
    change Patch.run ground.authority.cell.logical
      (CredentialAuthorityEffects.assignAll ground.authority.cell.logical _) address = _
    rw [run_assignAll]
    exact setAll_frame _ _ address (by
      simpa [DelegateDeclaration.entries, DelegateDeclaration.capabilityEntry, registrationEntry,
        delegateFootprint] using outside)

/-- **Gates refuse only.** Two executor preparations of the same signed
delegation, over ANY two grounds and admission heights (any nullifier set,
parent lineage, revocation and registration planes, issuer and policy epochs,
policy revision, target root and law), write the same shown effect: the same
child head at the same address, the same registration, and nothing else. Each
gate is a field of `Prepared` (`descent`: the parent at the signed id, its
lineage valid and anchored, the child slot fresh and unregistered, issuer and
policy epochs current, ancestors and channels registered and live; `shape`: the
child's rights narrow the parent's; `policyTarget`; `identity`: the operation
marker; `validated`; `source`: the current law), or of the receiver's
`Accepted` (the signature, and the authorization whose capability evidence names
the parent the signer holds, `Accepted.parent_authorized`). A failing gate makes
`prepare` or `authorize` refuse; none feeds the shown effect. Only the
kernel-owned lineage may differ: each is the copy of its own state's parent. -/
theorem delegate_gate_refuse_only {ambient₁ ambient₂ : CapabilityDelegationController.Ambient}
    {ground₁ ground₂ : CapabilityDelegationController.Ground deployment} {kind : ResourceKind}
    {command : CapabilityDelegationController.Command kind}
    (one : CapabilityDelegationController.Prepared deployment profile ambient₁ ground₁ command)
    (two : CapabilityDelegationController.Prepared deployment profile ambient₂ ground₂ command) :
    (readCapability one.authorityPost kind command.declaration.child.id).map StoredCapability.head =
        (readCapability two.authorityPost kind command.declaration.child.id).map StoredCapability.head ∧
      isRegistered one.authorityPost (.capability command.declaration.child.id) =
        isRegistered two.authorityPost (.capability command.declaration.child.id) ∧
      (∀ address, address ∉ delegateFootprint (kind := kind) command.declaration.child.id →
        one.authorityPost.logical address = ground₁.authority.cell.logical address ∧
        two.authorityPost.logical address = ground₂.authority.cell.logical address) := by
  obtain ⟨written₁, _, registered₁, frame₁⟩ := delegate_display_is_commit one
  obtain ⟨written₂, _, registered₂, frame₂⟩ := delegate_display_is_commit two
  refine ⟨?_, by rw [registered₁, registered₂], fun address outside =>
    ⟨frame₁ address outside, frame₂ address outside⟩⟩
  rw [written₁, written₂]
  rfl

/-- **A Host that swaps the parent is refused before signing.** A plan whose
finalized draft is a delegation command other than the intent's (for instance
the same delegation over another parent) is refused `planCoordinates`. -/
theorem delegate_swapped_draft_refused {deployment : Deployment} {semantics : Digest}
    {federation : FederationId} {commandBytes planBytes other : List UInt8}
    {views : List (List UInt8)} {kind : ResourceKind}
    {command : CapabilityDelegationController.Command kind} {plan : NativeHostCodec.SigningPlan}
    (decoded : CapabilityDelegationController.commandCodec.decode commandBytes = some ⟨kind, command⟩)
    (planDecoded : NativeHostCodec.signingPlanCodec.decode planBytes = some plan)
    (swapped : plan.finalizedDraft = .delegate other) (differs : other ≠ commandBytes) :
    checkDelegateThin deployment semantics federation commandBytes planBytes views =
      .error .planCoordinates := by
  unfold checkDelegateThin
  simp [decoded, planDecoded, swapped, differs]

/-- What thin consent shows for a plan. -/
inductive Shown where
  | invocation (targets : List Display)
  | delegation (display : DelegateDisplay)

/-- **Thin plan consent**, by the intent's draft. -/
def checkPlanThin (deployment : Deployment) (semantics : Digest) (federation : FederationId)
    (wanted : NativeObservationCodec.Intent) (planBytes : List UInt8)
    (views : List (List UInt8)) : Except Refusal (List (List UInt8) × Shown) :=
  match wanted.purpose with
  | .prepare (.invoke commandBytes) =>
      (checkInvokeThin deployment semantics federation commandBytes planBytes views).map
        fun (headers, displays) => (headers, .invocation displays)
  | .prepare (.delegate commandBytes) =>
      (checkDelegateThin deployment semantics federation commandBytes planBytes views).map
        fun (headers, display) => (headers, .delegation display)
  | _ => .error .notInvocation

#assert_axioms delegateValues_exact checkDelegateThin_shows delegate_display_is_commit
  delegate_gate_refuse_only delegate_swapped_draft_refused

/-! ## Thin observation consent

A challenge asks the member to sign observation legs: one per intent grant, each
an observe-verb request for that grant's target. Thin consent checks the
challenge is for its own retained intent and intent signature in this
deployment, and that every header signs exactly the observe leg the native
controller derives (`NativeObservationController.headerAt`), at the challenge's
own world root. An observe-verb signature authorizes a read only: a write
receiver rebuilds its request with a write verb, so the signed bytes cannot match. -/

def observationValues (deployment : Deployment) (semantics : Digest) (federation : FederationId)
    (worldRoot : Digest) (intent : NativeObservationCodec.Intent)
    (grant : NativeObservationCodec.GrantRef) : Request grant.kind where
  domain := deployment.domain
  semantics := semantics
  federation := federation
  subject := intent.subject
  subjectKeyEpoch := 0
  target := ⟨grant.target⟩
  verb := observeVerb grant.kind
  argsDigest := NativeObservationCodec.intentIdentity intent
  effectsDigest := NativeObservationController.effectIdentityAt deployment worldRoot semantics intent grant
  nonce := intent.nonce
  height := 0
  preStateRoot := ⟨0⟩
  policyId := ⟨grant.target⟩
  policyEpoch := 0
  policyRevision := 0
  cost := (NativeObservationCodec.intentCodec.encode intent).length

def checkObservationThin (deployment : Deployment) (semantics : Digest) (federation : FederationId)
    (wanted : NativeObservationCodec.Intent) (intentSignature candidate : List UInt8) :
    Except Refusal (List (List UInt8)) := do
  let some challenge := NativeObservationCodec.challengeCodec.decode candidate | .error .challengeMalformed
  unless challenge.intent = wanted ∧ challenge.intentSignature = intentSignature ∧
      challenge.domain = deployment.domain ∧ challenge.semantics = semantics ∧
      challenge.federation = federation do .error .challengeCoordinates
  unless challenge.headers.length = wanted.grants.length do .error .slotShape
  for (index, header, grant) in (List.range challenge.headers.length).zip (challenge.headers.zip wanted.grants) do
    checkHeader index
      (NativeObservationController.markerAt deployment challenge.worldRoot semantics wanted grant)
      (observationValues deployment semantics federation challenge.worldRoot wanted grant) header
  pure challenge.headers

#assert_axioms checkHeader_binds

end Minidregg.Kernel.NativeThinConsent
