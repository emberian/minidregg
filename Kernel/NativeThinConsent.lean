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

Thin consent takes the served view of each target: the narrowed packed cell and the
salted opening of its root (one item per entry, an opened entry or a sealed leaf). It
recomputes the root from the opening alone and checks it is the root the signed command
names (refusing `servedRootMismatch` otherwise), checks the packed cell is exactly the store
of the opened entries (`openingMismatch`), and runs `memberPatch` on that store. That is the
part of `targetPatch` whose inputs are all signed or served (`targetPatch_split`). A payload
whose patch has any other input (content, which reads the authority snapshot's policy
coordinates and the height; a stream append, which records the height; money and compute
legs, which write the shared Book) is refused by name. It is not displayed with a default.
The full-peer provider still covers those. World and kind-definition payloads, whose patches
read the pre-state, require an opening that seals nothing (a full-scope view).

## Theorem

`opened_display_is_commit`: for an executor-prepared target (`PreparedTarget`, the receiver's
own object, built by `prepareTarget` from the loaded image at admission), if thin consent
accepted a served view for it, then either the view's opening is a named collision of the
store hash at the actual pre-state (`OpeningCollision`), or the committed post equals the
displayed post at every address that is neither kernel-owned nor sealed in the opening, and
equals the pre-state at every sealed address that is not kernel-owned. A Host can narrow what
is shown but cannot change what commits. Teeth: `opened_view_refused`,
`pre_reading_sealed_refused`. Satisfiable, one pole per payload:
`honest_scalar_view_accepted` (declared objects),
`honest_account_scalar_view_accepted`, `honest_world_view_accepted` and
`honest_kind_definition_view_accepted` (full-scope views, which seal nothing, so the post root
is shown), `honest_content_read_view_accepted`, `honest_kind_read_view_accepted`; content writes
and stream appends reach the named refusal (`honest_content_stream_write_named`).
-/
module

public import Kernel.ResourceTransaction
public import Kernel.NativeObservationController

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

@[expose] public section

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
  /-- The root recomputed from the served opening is not the root the signed command names. -/
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
  /-- A birth this arm does not consent to: not an ordinary resource birth
  (`Kernel.NativeThinBirth`). -/
  | birthRoute (what : String)
  /-- The intent's birth draft is not a canonical descriptor without auxiliary creates. -/
  | birthMalformed
  /-- The intent's birth draft is not the deployed authoring of the member's own source at
  the draft's coordinates. -/
  | draftNotAuthored
  /-- The plan's finalized descriptor differs from the intent's draft beyond the kernel's
  auxiliary creates. -/
  | birthSourceChanged
  /-- The served view's packed cell is not exactly the store of its opened entries. -/
  | openingMismatch (target : Nat)
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
        simp only [computeTarget, scalarLeg] at computed
        repeat' split at computed
        all_goals first
          | (rename_i cell _; exact cell.candidate.modeEvidence.rootExact)
          | cases computed
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

/-- The executor's committed post is the target patch run on the loaded pre-state. -/
theorem post_run {deployment : Deployment} {directory : CellRegistry.Directory Nat Registry}
    {snapshot : AuthoritySnapshot} {semantics : Digest} {ambient : Ambient}
    {command : Command} {target : Target}
    (prepared : PreparedTarget deployment directory snapshot semantics ambient command target) :
    prepared.post = Patch.run prepared.pre.logical
      (targetPatch snapshot semantics ambient command target prepared.pre) := by
  rw [← prepared.postExact]
  rfl

#assert_axioms memberPatch_supported computeTarget_root post_run

/-! ## Served views over salted openings (statement first)

The Host never serves a cell's hiding key: every resource view drops the blinding entry
(`ResourceObservationAdmission.narrowPacked_erases_blinding`) and serves, beside the narrowed
packed cell, the cell's salted opening: one item per entry in canonical order, an opened entry
(salt and bytes) or a sealed leaf (`NativeObservationController.openingView`,
`root_opens`). The salts derive from the blinding key, so re-encoding the served store cannot
reproduce the signed root of a blinded cell (the re-encoding check this replaces refused every
write to one, `servedRootMismatch`: JP2 row 22 on candidate e89fe7b8b).

`checkOpened` checks the view by its opening: the frame is the target's store frame,
the root recomputed from the items alone is the root the signed command names, and the narrowed
packed cell is exactly the store of the opened entries. The display is the member patch run on
that store. The claim is at every address that is neither kernel-owned nor sealed in the
served opening, and it concludes **or** a named collision of the store hash at the actual
pre-state (`OpeningCollision`), taking no hash premise. -/

/-- Every target's materializer is a salted store over one wire. -/
def targetWire (target : Target) : StoreCodec.Wire target.layout := by
  cases target with
  | mk kind id capability version root payload observe audienceEpoch audienceRoster =>
    cases payload with
    | scalar _ | computeFunding _ | moneyConsent _ => exact DeclaredEffectCell.wire
    | content _ | read => exact HyperdocumentCell.contentWire
    | append _ => exact StreamCell.headWire
    | world _ => exact WorldKindCell.instanceWire
    | kindDefinition _ | kindRead => exact WorldKindCell.definitionWire

/-- The entry bytes an opening discloses, in canonical order. -/
def openedBytes (items : List StoreHiding.Item) : List (List UInt8) :=
  items.filterMap fun item => item.getLeft?.map StoreCodec.Opening.entry

/-- The parts of a served resource view that thin consent reads: the narrowed packed cell's
bytes and the opening (frame and items). -/
def servedOpening (target : Target) (view : List UInt8) :
    Except Refusal (List UInt8 × List UInt8 × List StoreHiding.Item) :=
  match NativeObservationController.resourceViewCodec.decode view with
  | none => .error (.viewMalformed target.target)
  | some (_, packedBytes, _, (frame, items), _) => .ok (packedBytes, frame, items)

/-- Payloads whose member patch is computed from the pre-state (`WorldKindCell.preparePatch`,
`prepareDefinition`). World and kind-definition payloads require an opening that seals nothing
(a full-scope view): a member cannot check a patch computed from entries it cannot see, so a
grant narrowed by field scope is refused for them (`pre_reading_sealed_refused`). Every other
payload's member patch is the command's alone (`memberPatch_pre_independent`). -/
def patchReadsPre (target : Target) : Bool :=
  match target.payload with
  | .world _ | .kindDefinition _ => true
  | _ => false

/-- **Thin consent's check of one served view.** The frame is the target's store frame; the
root recomputed from the opening's items is the root the signed command names; the narrowed
packed cell, selected under the executor's own role selection, is exactly the store of the
opened entries; the member patch applies to it. Returns the displayed post. -/
def checkOpened (deployment : Deployment) (command : Command) (target : Target)
    (view : List UInt8) : Except Refusal (Store target.layout) :=
  match servedOpening target view with
  | .error refusal => .error refusal
  | .ok (packedBytes, frame, items) =>
    if frame = StoreCodec.frame (targetWire target) then
      if StoreHiding.rootOfItems (targetWire target) items = target.expectedTargetRoot then
        match CanonicalCellRegistry.cellCodec.decode packedBytes with
        | none => .error (.viewMalformed target.target)
        | some packed =>
          match selectTarget deployment target packed with
          | none => .error (.viewRole target.target)
          | some cell =>
            if (StoreCodec.entries (targetWire target) cell.logical).map
                (StoreCodec.entryBytes (targetWire target)) = openedBytes items then
              if patchReadsPre target && items.any Sum.isRight then
                .error (.unsupportedPayload target.target "world: the patch reads entries the opening seals")
              else
              match memberPatch command target cell.logical with
              | .error refusal => .error refusal
              | .ok patch =>
                if Patch.ValidFrom cell.logical patch then .ok (Patch.run cell.logical patch)
                else .error (.patchRefused target.target)
            else .error (.openingMismatch target.target)
      else .error (.servedRootMismatch target.target)
    else .error (.viewMalformed target.target)

/-- Whether a served view's opening seals nothing. -/
def sealsNothing (target : Target) (view : List UInt8) : Bool :=
  match servedOpening target view with
  | .ok (_, _, items) => !items.any Sum.isRight
  | .error _ => false

/-- A collision of the store hash at the actual pre-state: the items' leaves are not the
actual store's leaves yet root to the same digest, or an opened item is not the actual
opening at its position yet has the same leaf. -/
def OpeningCollision {L : Layout.{0, 0, 0}} (wire : StoreCodec.Wire L)
    (items : List StoreHiding.Item) (actual : Store L) : Prop :=
  (items.map StoreHiding.Item.leaf ≠ StoreCodec.leaves wire actual ∧
      StoreCodec.rootOfLeaves wire (items.map StoreHiding.Item.leaf) =
        StoreCodec.rootOfLeaves wire (StoreCodec.leaves wire actual)) ∨
  ∃ (position : Nat) (shown : StoreCodec.Opening) (entry : Entry L),
    items[position]? = some (.inl shown) ∧ (StoreCodec.entries wire actual)[position]? = some entry ∧
    shown ≠ StoreCodec.opening wire actual entry ∧
    shown.leaf = (StoreCodec.opening wire actual entry).leaf

/-- An address the served opening seals: the actual store has an entry there whose item is a
leaf. Thin consent shows nothing at it. -/
def SealedIn {L : Layout.{0, 0, 0}} (wire : StoreCodec.Wire L) (items : List StoreHiding.Item)
    (actual : Store L) (address : Address L) : Prop :=
  ∃ (position : Nat) (entry : Entry L) (leaf : List UInt8),
    (StoreCodec.entries wire actual)[position]? = some entry ∧ entry.1 = address ∧
      items[position]? = some (.inr leaf)

/-- **Keystone: what thin consent shows over an opening is what commits.** For the executor's
own prepared target and a served view thin consent accepted: either the view's opening is a
collision of the store hash at the actual pre-state, or (1) at every address that is neither
kernel-owned nor sealed in that opening, the committed post is the displayed post, and (2) at
every sealed address that is not kernel-owned the committed post is the pre-state: a Host can
narrow what is shown but cannot change what commits (each operation of the member patch names
the value it replaces, so it cannot be enabled both on the shown store and on the actual one
at an address the opening seals). -/
def OpenedDisplayIsCommitStatement : Prop :=
  ∀ {deployment : Deployment} {directory : CellRegistry.Directory Nat Registry}
    {snapshot : AuthoritySnapshot} {semantics : Digest} {ambient : Ambient}
    {command : Command} {target : Target}
    (prepared : PreparedTarget deployment directory snapshot semantics ambient command target)
    (view : List UInt8) (shown : Store target.layout)
    (packedBytes frame : List UInt8) (items : List StoreHiding.Item),
    checkOpened deployment command target view = .ok shown →
    servedOpening target view = .ok (packedBytes, frame, items) →
    OpeningCollision (targetWire target) items prepared.pre.logical ∨
      ((∀ address, ¬ KernelOwned target address →
          ¬ SealedIn (targetWire target) items prepared.pre.logical address →
          prepared.post address = shown address) ∧
        ∀ address, ¬ KernelOwned target address →
          SealedIn (targetWire target) items prepared.pre.logical address →
          prepared.post address = prepared.pre.logical address)

/-- **Teeth.** (1) A view whose opening roots to anything but the signed root is refused
`servedRootMismatch`. (2) A view whose packed cell is not exactly the store of its opened
entries (a Host that shows one value and opens another) is refused `openingMismatch`. -/
def OpenedViewRefusedStatement : Prop :=
  (∀ (deployment : Deployment) (command : Command) (target : Target) (view packedBytes frame : List UInt8)
      (items : List StoreHiding.Item),
    servedOpening target view = .ok (packedBytes, frame, items) →
    frame = StoreCodec.frame (targetWire target) →
    StoreHiding.rootOfItems (targetWire target) items ≠ target.expectedTargetRoot →
    checkOpened deployment command target view = .error (.servedRootMismatch target.target)) ∧
  (∀ (deployment : Deployment) (command : Command) (target : Target) (view packedBytes frame : List UInt8)
      (items : List StoreHiding.Item) (packed : CellRegistry.PackedCell Registry) (cell : TargetCell target),
    servedOpening target view = .ok (packedBytes, frame, items) →
    frame = StoreCodec.frame (targetWire target) →
    StoreHiding.rootOfItems (targetWire target) items = target.expectedTargetRoot →
    CanonicalCellRegistry.cellCodec.decode packedBytes = some packed →
    selectTarget deployment target packed = some cell →
    (StoreCodec.entries (targetWire target) cell.logical).map (StoreCodec.entryBytes (targetWire target)) ≠
      openedBytes items →
    checkOpened deployment command target view = .error (.openingMismatch target.target))

/-- **Teeth (pre-reading payloads).** A world or kind-definition target whose served view passes
every earlier check (frame, signed root, opened entries) but whose opening seals an entry is
refused `unsupportedPayload`: its patch is computed from the pre-state, which the member cannot
check at entries it cannot see. World and kind-definition payloads require an opening that seals
nothing (a full-scope view). -/
def PreReadingSealedRefusedStatement : Prop :=
  ∀ (deployment : Deployment) (command : Command) (target : Target) (view packedBytes frame : List UInt8)
      (items : List StoreHiding.Item) (packed : CellRegistry.PackedCell Registry) (cell : TargetCell target),
    patchReadsPre target = true →
    servedOpening target view = .ok (packedBytes, frame, items) →
    frame = StoreCodec.frame (targetWire target) →
    StoreHiding.rootOfItems (targetWire target) items = target.expectedTargetRoot →
    CanonicalCellRegistry.cellCodec.decode packedBytes = some packed →
    selectTarget deployment target packed = some cell →
    (StoreCodec.entries (targetWire target) cell.logical).map (StoreCodec.entryBytes (targetWire target)) =
      openedBytes items →
    items.any Sum.isRight = true →
    checkOpened deployment command target view =
      .error (.unsupportedPayload target.target "world: the patch reads entries the opening seals")

/-- **Satisfiable: the honest Host's view passes.** For a scalar target over a declared object
cell whose root is the signed root, the resource view the Host serves under any field scope
(`NativeObservationController.resourceView`) is accepted whenever the narrowed cell is
selected and the member patch applies to it. Scope: **declared-object scalar targets** (the
cells JP2 writes). The other payloads have a pole each below. -/
def HonestScalarViewAcceptedStatement : Prop :=
  ∀ (deployment : Deployment) (command : Command) (kind : ResourceKind) (id : Nat)
    (capability : CapabilityId) (version : Nat) (actions : List DeclaredActionLowering.Action)
    (observe : Option CapabilityId) (audienceEpoch : Option Nat)
    (audienceRoster : Option Minidregg.Theory.ObjectAudienceRoster.Roster)
    (fields : Option (Finset CellField)) (payload : DeclaredEffectCell.Cell)
    (balances : List (Nat × Int)) (quote : Option RunComputeView.ComputeQuote)
    (narrowed : DeclaredEffectCell.Cell),
    let target : Target := ⟨kind, id, capability, version, payload.root, .scalar actions, observe,
      audienceEpoch, audienceRoster⟩
    selectTarget deployment target
        (ResourceObservationAdmission.narrowPacked fields ⟨.declaredObject, payload⟩) =
      some narrowed →
    Patch.ValidFrom narrowed.logical (DeclaredResourceScalar.cellPatch (scalarCommand command target actions)) →
    ∃ shown, checkOpened deployment command target
      (NativeObservationController.resourceViewCodec.encode
        (NativeObservationController.resourceView fields ⟨.declaredObject, payload⟩ balances quote)) =
      .ok shown

/-- **Satisfiable: account-metadata scalar targets.** As `HonestScalarViewAcceptedStatement`, for
a scalar target over an account-metadata cell. -/
def HonestAccountScalarViewAcceptedStatement : Prop :=
  ∀ (deployment : Deployment) (command : Command) (kind : ResourceKind) (id : Nat)
    (capability : CapabilityId) (version : Nat) (actions : List DeclaredActionLowering.Action)
    (observe : Option CapabilityId) (audienceEpoch : Option Nat)
    (audienceRoster : Option Minidregg.Theory.ObjectAudienceRoster.Roster)
    (fields : Option (Finset CellField)) (payload : DeclaredEffectCell.Cell)
    (balances : List (Nat × Int)) (quote : Option RunComputeView.ComputeQuote)
    (narrowed : DeclaredEffectCell.Cell),
    let target : Target := ⟨kind, id, capability, version, payload.root, .scalar actions, observe,
      audienceEpoch, audienceRoster⟩
    selectTarget deployment target
        (ResourceObservationAdmission.narrowPacked fields ⟨.accountMetadata, payload⟩) =
      some narrowed →
    Patch.ValidFrom narrowed.logical (DeclaredResourceScalar.cellPatch (scalarCommand command target actions)) →
    ∃ shown, checkOpened deployment command target
      (NativeObservationController.resourceViewCodec.encode
        (NativeObservationController.resourceView fields ⟨.accountMetadata, payload⟩ balances quote)) =
      .ok shown

/-- **Satisfiable: world instances over a full-scope view.** The resource view the Host serves a
full-scope reader (`fields = none`) of a world-instance cell is accepted whenever the cell is
selected and the patch the member's actions prepare from it applies; its opening seals nothing,
so the display carries the post root (jthin-consent's T1 compares it with the committed one). -/
def HonestWorldViewAcceptedStatement : Prop :=
  ∀ (deployment : Deployment) (command : Command) (kind : ResourceKind) (id : Nat)
    (capability : CapabilityId) (version : Nat) (actions : List WorldKindInstance.Action)
    (observe : Option CapabilityId) (audienceEpoch : Option Nat)
    (audienceRoster : Option Minidregg.Theory.ObjectAudienceRoster.Roster)
    (payload : Materialized WorldKindCell.instanceMaterializer)
    (balances : List (Nat × Int)) (quote : Option RunComputeView.ComputeQuote)
    (narrowed : Materialized WorldKindCell.instanceMaterializer)
    (patch : Patch WorldKindCell.instanceLayout),
    let target : Target := ⟨kind, id, capability, version, payload.root, .world actions, observe,
      audienceEpoch, audienceRoster⟩
    let view := NativeObservationController.resourceViewCodec.encode
      (NativeObservationController.resourceView none ⟨.worldInstance, payload⟩ balances quote)
    selectTarget deployment target
        (ResourceObservationAdmission.narrowPacked none ⟨.worldInstance, payload⟩) = some narrowed →
    WorldKindCell.preparePatch narrowed.logical actions = some patch →
    Patch.ValidFrom narrowed.logical patch →
    (∃ shown, checkOpened deployment command target view = .ok shown) ∧
      sealsNothing target view = true

/-- **Satisfiable: world-kind definitions over a full-scope view.** As
`HonestWorldViewAcceptedStatement`, for a kind-definition target over a world-kind cell. -/
def HonestKindDefinitionViewAcceptedStatement : Prop :=
  ∀ (deployment : Deployment) (command : Command) (kind : ResourceKind) (id : Nat)
    (capability : CapabilityId) (version : Nat) (definition : WorldKindCell.Definition)
    (observe : Option CapabilityId) (audienceEpoch : Option Nat)
    (audienceRoster : Option Minidregg.Theory.ObjectAudienceRoster.Roster)
    (payload : Materialized WorldKindCell.definitionMaterializer)
    (balances : List (Nat × Int)) (quote : Option RunComputeView.ComputeQuote)
    (narrowed : Materialized WorldKindCell.definitionMaterializer)
    (patch : Patch WorldKindCell.definitionLayout),
    let target : Target := ⟨kind, id, capability, version, payload.root, .kindDefinition definition,
      observe, audienceEpoch, audienceRoster⟩
    let view := NativeObservationController.resourceViewCodec.encode
      (NativeObservationController.resourceView none ⟨.worldKind, payload⟩ balances quote)
    selectTarget deployment target
        (ResourceObservationAdmission.narrowPacked none ⟨.worldKind, payload⟩) = some narrowed →
    WorldKindCell.prepareDefinition narrowed.logical definition = some patch →
    Patch.ValidFrom narrowed.logical patch →
    (∃ shown, checkOpened deployment command target view = .ok shown) ∧
      sealsNothing target view = true

/-- **Satisfiable: content reads under any field scope.** The resource view the Host serves of a
content cell under any scope is accepted for an observe-only read target whenever the narrowed
cell is selected. -/
def HonestContentReadViewAcceptedStatement : Prop :=
  ∀ (deployment : Deployment) (command : Command) (kind : ResourceKind) (id : Nat)
    (capability : CapabilityId) (version : Nat)
    (observe : Option CapabilityId) (audienceEpoch : Option Nat)
    (audienceRoster : Option Minidregg.Theory.ObjectAudienceRoster.Roster)
    (fields : Option (Finset CellField)) (payload : Materialized HyperdocumentCell.contentMaterializer)
    (balances : List (Nat × Int)) (quote : Option RunComputeView.ComputeQuote)
    (narrowed : Materialized HyperdocumentCell.contentMaterializer),
    let target : Target := ⟨kind, id, capability, version, payload.root, .read, observe,
      audienceEpoch, audienceRoster⟩
    selectTarget deployment target
        (ResourceObservationAdmission.narrowPacked fields ⟨.content, payload⟩) = some narrowed →
    ∃ shown, checkOpened deployment command target
      (NativeObservationController.resourceViewCodec.encode
        (NativeObservationController.resourceView fields ⟨.content, payload⟩ balances quote)) =
      .ok shown

/-- **Satisfiable: world-kind reads under any field scope.** As
`HonestContentReadViewAcceptedStatement`, for an observe-only kind read over a world-kind cell. -/
def HonestKindReadViewAcceptedStatement : Prop :=
  ∀ (deployment : Deployment) (command : Command) (kind : ResourceKind) (id : Nat)
    (capability : CapabilityId) (version : Nat)
    (observe : Option CapabilityId) (audienceEpoch : Option Nat)
    (audienceRoster : Option Minidregg.Theory.ObjectAudienceRoster.Roster)
    (fields : Option (Finset CellField)) (payload : Materialized WorldKindCell.definitionMaterializer)
    (balances : List (Nat × Int)) (quote : Option RunComputeView.ComputeQuote)
    (narrowed : Materialized WorldKindCell.definitionMaterializer),
    let target : Target := ⟨kind, id, capability, version, payload.root, .kindRead, observe,
      audienceEpoch, audienceRoster⟩
    selectTarget deployment target
        (ResourceObservationAdmission.narrowPacked fields ⟨.worldKind, payload⟩) = some narrowed →
    ∃ shown, checkOpened deployment command target
      (NativeObservationController.resourceViewCodec.encode
        (NativeObservationController.resourceView fields ⟨.worldKind, payload⟩ balances quote)) =
      .ok shown

/-- **Thin consent refuses content writes and stream appends by name; the full-peer provider
covers them.** The resource view the Host serves of a content or stream cell, under every field
scope and for every request, passes every opening check (frame, signed root, opened entries),
and the write is then refused `unsupportedPayload` (its patch reads inputs that are neither
signed nor served), never `servedRootMismatch` or `openingMismatch`. Compute-funding and money
payloads are likewise refused by `memberPatch` and are outside thin consent's scope. -/
def HonestContentStreamWriteNamedStatement : Prop :=
  (∀ (deployment : Deployment) (command : Command) (kind : ResourceKind) (id : Nat)
    (capability : CapabilityId) (version : Nat) (contentCommand : ContentResource.Command)
    (observe : Option CapabilityId) (audienceEpoch : Option Nat)
    (audienceRoster : Option Minidregg.Theory.ObjectAudienceRoster.Roster)
    (fields : Option (Finset CellField)) (payload : Materialized HyperdocumentCell.contentMaterializer)
    (balances : List (Nat × Int)) (quote : Option RunComputeView.ComputeQuote)
    (narrowed : Materialized HyperdocumentCell.contentMaterializer),
    let target : Target := ⟨kind, id, capability, version, payload.root, .content contentCommand,
      observe, audienceEpoch, audienceRoster⟩
    selectTarget deployment target
        (ResourceObservationAdmission.narrowPacked fields ⟨.content, payload⟩) = some narrowed →
    ∃ what, checkOpened deployment command target
      (NativeObservationController.resourceViewCodec.encode
        (NativeObservationController.resourceView fields ⟨.content, payload⟩ balances quote)) =
      .error (.unsupportedPayload id what)) ∧
  (∀ (deployment : Deployment) (command : Command) (kind : ResourceKind) (id : Nat)
    (capability : CapabilityId) (version : Nat) (request : StreamCell.Append)
    (observe : Option CapabilityId) (audienceEpoch : Option Nat)
    (audienceRoster : Option Minidregg.Theory.ObjectAudienceRoster.Roster)
    (fields : Option (Finset CellField)) (payload : Materialized StreamCell.headMaterializer)
    (balances : List (Nat × Int)) (quote : Option RunComputeView.ComputeQuote)
    (narrowed : Materialized StreamCell.headMaterializer),
    let target : Target := ⟨kind, id, capability, version, payload.root, .append request,
      observe, audienceEpoch, audienceRoster⟩
    selectTarget deployment target
        (ResourceObservationAdmission.narrowPacked fields ⟨.stream, payload⟩) = some narrowed →
    ∃ what, checkOpened deployment command target
      (NativeObservationController.resourceViewCodec.encode
        (NativeObservationController.resourceView fields ⟨.stream, payload⟩ balances quote)) =
      .error (.unsupportedPayload id what))

/-! ### Proofs -/

theorem target_rootOf (target : Target) (store : Store target.layout) :
    target.materializer.rootOf store = StoreCodec.saltedRoot (targetWire target) store := by
  cases target with
  | mk kind id capability version root payload observe audienceEpoch audienceRoster =>
    cases payload <;> exact StoreCodec.materializer_rootOf _ _

/-- Two stores that agree at an address agree there after any patch. -/
theorem run_congr_at {L : Layout.{0, 0, 0}} (address : Address L) :
    ∀ (patch : Patch L) (left right : Store L), left address = right address →
      Patch.run left patch address = Patch.run right patch address
  | [], _, _, same => same
  | op :: rest, left, right, same => by
      simp only [Patch.run]
      apply run_congr_at address rest
      by_cases written : op.writeAddress? = some address
      · have at_ := Op.writeAddress?_eq_some written
        cases op with
        | read => simp [Op.writeAddress?] at written
        | write => subst at_; simp [Op.apply, Op.address, Store.set]
        | allocate => subst at_; simp [Op.apply, Op.address, Store.set]
        | free => subst at_; simp [Op.apply, Op.address, Store.set]
      · rw [Op.apply_frame _ _ _ written, Op.apply_frame _ _ _ written, same]

/-- **An address the shown store lacks and the actual one holds is written by no patch that
is enabled on both.** -/
theorem untouched_of_both_valid {L : Layout.{0, 0, 0}} (address : Address L) :
    ∀ (patch : Patch L) (shown actual : Store L), shown address = none → actual address ≠ none →
      Patch.ValidFrom shown patch → Patch.ValidFrom actual patch →
      address ∉ Patch.writeFootprint patch
  | [], _, _, _, _, _, _ => by simp [Patch.writeFootprint]
  | op :: rest, shown, actual, absent, present, ⟨enabledShown, restShown⟩, ⟨enabledActual, restActual⟩ => by
      by_cases at_ : op.address = address
      · exfalso
        cases op with
        | read space key observed =>
            simp only [Op.Enabled, Op.address] at enabledShown enabledActual at_
            subst at_
            exact present (enabledActual.trans enabledShown.symm |>.trans absent)
        | write space key before after =>
            simp only [Op.Enabled, Op.address] at enabledShown at_
            subst at_
            rw [absent] at enabledShown
            cases enabledShown.2
        | allocate space key value =>
            simp only [Op.Enabled, Op.address, Store.Fresh] at enabledActual at_
            subst at_
            exact present enabledActual.2
        | free space key before =>
            simp only [Op.Enabled, Op.address] at enabledShown at_
            subst at_
            rw [absent] at enabledShown
            cases enabledShown.2
      · have notWritten : op.writeAddress? ≠ some address := fun written =>
          at_ (Op.writeAddress?_eq_some written)
        have rest' := untouched_of_both_valid address rest (op.apply shown) (op.apply actual)
          (by rw [Op.apply_frame _ _ _ notWritten]; exact absent)
          (by rw [Op.apply_frame _ _ _ notWritten]; exact present) restShown restActual
        intro member
        rcases (Patch.mem_writeFootprint_iff _ address).1 member with ⟨op', mem, written⟩
        rcases List.mem_cons.mp mem with rfl | inRest
        · exact notWritten written
        · exact rest' ((Patch.mem_writeFootprint_iff _ address).2 ⟨op', inRest, written⟩)

theorem mem_entries_of_present {L : Layout.{0, 0, 0}} (wire : StoreCodec.Wire L) (store : Store L)
    {address : Address L} {value : L.Value address.1} (present : store address = some value) :
    (⟨address, value⟩ : Entry L) ∈ StoreCodec.entries wire store := by
  unfold StoreCodec.entries
  refine List.mem_filterMap.mpr ⟨address, (StoreCodec.mem_sortedSupport wire store address).mpr
    (by simp [present]), by simp [present]⟩

/-- What `checkOpened` accepted. -/
theorem checkOpened_ok {deployment : Deployment} {command : Command} {target : Target}
    {view : List UInt8} {shown : Store target.layout} {packedBytes frame : List UInt8}
    {items : List StoreHiding.Item}
    (checked : checkOpened deployment command target view = .ok shown)
    (served : servedOpening target view = .ok (packedBytes, frame, items)) :
    ∃ (cell : TargetCell target) (patch : Patch target.layout),
      StoreHiding.rootOfItems (targetWire target) items = target.expectedTargetRoot ∧
      (StoreCodec.entries (targetWire target) cell.logical).map
          (StoreCodec.entryBytes (targetWire target)) = openedBytes items ∧
      (patchReadsPre target = true → ∀ item ∈ items, item.isRight = false) ∧
      memberPatch command target cell.logical = .ok patch ∧
      Patch.ValidFrom cell.logical patch ∧ shown = Patch.run cell.logical patch := by
  unfold checkOpened at checked
  rw [served] at checked
  simp only at checked
  split at checked
  · split at checked
    · rename_i rooted
      split at checked
      · cases checked
      split at checked
      · cases checked
      rename_i cell _
      split at checked
      · rename_i opened
        split at checked
        · cases checked
        rename_i noSealed
        split at checked
        · cases checked
        rename_i patch member
        split at checked
        · rename_i valid
          cases checked
          exact ⟨cell, patch, rooted, opened, by simpa using noSealed, member, valid, rfl⟩
        · cases checked
      · cases checked
    · cases checked
  · cases checked

/-- A member patch that does not read the pre-state is the same over any two stores. -/
theorem memberPatch_pre_independent (command : Command) (target : Target)
    (left right : Store target.layout) (reads : patchReadsPre target = false) :
    memberPatch command target right = memberPatch command target left := by
  cases target with
  | mk kind id capability version root payload observe audienceEpoch audienceRoster =>
    cases payload <;> simp_all [patchReadsPre, memberPatch]

theorem entries_keys_nodup {L : Layout.{0, 0, 0}} (wire : StoreCodec.Wire L) (store : Store L) :
    ((StoreCodec.entries wire store).map Sigma.fst).Nodup := by
  rw [StoreCodec.entries_keys]
  exact (StoreCodec.sortedSupport_pairwise wire store).imp fun less same => by
    rw [same] at less; exact lt_irrefl _ less

/-- The entries an aligned opening opens: the actual entries at its opened positions. -/
def openedEntries {L : Layout.{0, 0, 0}} (wire : StoreCodec.Wire L) (items : List StoreHiding.Item)
    (actual : Store L) : List (Entry L) :=
  (((StoreCodec.entries wire actual).zip items).filter fun pair => pair.2.isLeft).map Prod.fst

theorem openedBytes_aligned {L : Layout.{0, 0, 0}} (wire : StoreCodec.Wire L) (actual : Store L) :
    ∀ (entries : List (Entry L)) (items : List StoreHiding.Item), entries.length = items.length →
      (∀ pair ∈ entries.zip items, ∀ shown, pair.2 = .inl shown →
        shown = StoreCodec.opening wire actual pair.1) →
      openedBytes items =
        (((entries.zip items).filter fun pair => pair.2.isLeft).map Prod.fst).map
          (StoreCodec.entryBytes wire)
  | [], [], _, _ => rfl
  | entry :: entries, item :: items, length, aligned => by
      have rest := openedBytes_aligned wire actual entries items (by simpa using length)
        (fun pair member => aligned pair (List.mem_cons_of_mem _ member))
      cases item with
      | inl shown =>
          have exact := aligned (entry, .inl shown) List.mem_cons_self shown rfl
          simp only [openedBytes, List.filterMap_cons, Sum.getLeft?, Option.map_some,
            List.zip_cons_cons, List.filter_cons, Sum.isLeft_inl, if_true, List.map_cons]
          rw [exact]
          exact congrArg _ rest
      | inr leaf =>
          simp only [openedBytes, List.filterMap_cons, Sum.getLeft?, Option.map_none,
            List.zip_cons_cons, List.filter_cons, Sum.isLeft_inr, Bool.false_eq_true, if_false]
          exact rest
  | [], _ :: _, length, _ => by simp at length
  | _ :: _, [], length, _ => by simp at length

/-- **What an aligned opening shows.** When the items' leaves are the actual store's and every
opened item is the actual opening at its position, a shown store whose entries' bytes are the
opened bytes agrees with the actual store at every unsealed address and is empty at every
sealed one. -/
theorem shown_agrees {L : Layout.{0, 0, 0}} (wire : StoreCodec.Wire L)
    (items : List StoreHiding.Item) (actual shown : Store L)
    (sameLeaves : items.map StoreHiding.Item.leaf = StoreCodec.leaves wire actual)
    (aligned : ∀ (position : Nat) (opened : StoreCodec.Opening) (entry : Entry L),
      items[position]? = some (.inl opened) → (StoreCodec.entries wire actual)[position]? = some entry →
      opened = StoreCodec.opening wire actual entry)
    (bytes : (StoreCodec.entries wire shown).map (StoreCodec.entryBytes wire) = openedBytes items) :
    (∀ address, ¬ SealedIn wire items actual address → shown address = actual address) ∧
      ∀ address, SealedIn wire items actual address → shown address = none := by
  obtain ⟨E, hE⟩ : ∃ E, E = StoreCodec.entries wire actual := ⟨_, rfl⟩
  rw [← hE] at aligned
  have length : E.length = items.length := by
    have := congrArg List.length sameLeaves
    simp [StoreCodec.leaves, ← hE] at this
    exact this.symm
  have pairAligned : ∀ pair ∈ E.zip items, ∀ opened, pair.2 = .inl opened →
      opened = StoreCodec.opening wire actual pair.1 := by
    intro pair member opened isOpened
    obtain ⟨position, bound, found⟩ := List.getElem_of_mem member
    have boundE : position < E.length := by simp at bound; omega
    have boundI : position < items.length := by simp at bound; omega
    rw [List.getElem_zip] at found
    subst found
    have item : items[position] = .inl opened := by simpa using isOpened
    exact aligned position opened E[position] (by simp [List.getElem?_eq_getElem boundI, item])
      (List.getElem?_eq_getElem boundE)
  have entriesShown : StoreCodec.entries wire shown = openedEntries wire items actual := by
    apply List.map_injective_iff.mpr (StoreCodec.entryBytes_injective wire)
    rw [bytes, openedBytes_aligned wire actual E items length pairAligned, openedEntries, ← hE]
  have shownStore : shown = StoreCodec.fromEntries (openedEntries wire items actual) := by
    rw [← entriesShown, StoreCodec.fromEntries_entries]
  have sublist : List.Sublist (openedEntries wire items actual) E := by
    have mapped : ((E.zip items).map Prod.fst) = E := List.map_fst_zip (by omega)
    have filtered := (List.filter_sublist (p := fun pair : Entry L × StoreHiding.Item => pair.2.isLeft)
      (l := E.zip items)).map Prod.fst
    rw [mapped] at filtered
    rw [openedEntries, ← hE]
    exact filtered
  have distinctE : (E.map Sigma.fst).Nodup := hE ▸ entries_keys_nodup wire actual
  have keysNodup : ((openedEntries wire items actual).map Sigma.fst).Nodup :=
    (sublist.map Sigma.fst).nodup distinctE
  have memOpened : ∀ (position : Nat) (bound : position < E.length) (opened : StoreCodec.Opening),
      items[position]? = some (.inl opened) → E[position] ∈ openedEntries wire items actual := by
    intro position bound opened isOpened
    have boundI : position < items.length := by omega
    have item : items[position] = .inl opened := by
      rw [List.getElem?_eq_getElem boundI] at isOpened; exact Option.some.inj isOpened
    rw [openedEntries, ← hE]
    refine List.mem_map.mpr ⟨(E[position], items[position]), List.mem_filter.mpr ⟨?_, ?_⟩, rfl⟩
    · exact List.mem_iff_getElem.mpr ⟨position, by simp; omega, by simp [List.getElem_zip]⟩
    · simp [item]
  have keyPosition : ∀ entry ∈ openedEntries wire items actual, ∃ (position : Nat)
      (bound : position < E.length), E[position] = entry ∧
        ∃ opened, items[position]? = some (.inl opened) := by
    intro entry member
    rw [openedEntries, ← hE] at member
    obtain ⟨pair, filtered, rfl⟩ := List.mem_map.mp member
    obtain ⟨inZip, isLeft⟩ := List.mem_filter.mp filtered
    obtain ⟨position, bound, found⟩ := List.getElem_of_mem inZip
    have boundE : position < E.length := by simp at bound; omega
    have boundI : position < items.length := by simp at bound; omega
    rw [List.getElem_zip] at found
    subst found
    refine ⟨position, boundE, rfl, ?_⟩
    cases item : items[position] with
    | inl opened => exact ⟨opened, by simp [List.getElem?_eq_getElem boundI, item]⟩
    | inr leaf => simp [item] at isLeft
  constructor
  · intro address unsealed
    rw [shownStore]
    cases present : actual address with
    | none =>
        rw [StoreCodec.fromEntries_apply_eq_none_iff]
        intro inKeys
        obtain ⟨entry, member, keyed⟩ := List.mem_map.mp inKeys
        have inE := sublist.subset member
        rw [hE] at inE
        have stored := StoreHiding.mem_entries wire inE
        subst keyed
        rw [present] at stored
        cases stored
    | some value =>
        have inE := mem_entries_of_present wire actual present
        rw [← hE] at inE
        obtain ⟨position, bound, found⟩ := List.getElem_of_mem inE
        have boundI : position < items.length := by omega
        cases item : items[position] with
        | inr leaf =>
            exact absurd ⟨position, ⟨address, value⟩, leaf,
              by rw [← hE, List.getElem?_eq_getElem bound, found], rfl,
              by simp [List.getElem?_eq_getElem boundI, item]⟩ unsealed
        | inl opened =>
            have member := memOpened position bound opened
              (by simp [List.getElem?_eq_getElem boundI, item])
            rw [found] at member
            exact StoreCodec.fromEntries_apply_of_mem _ keysNodup member
  · intro address ⟨position, entry, leaf, atEntry, keyed, sealed⟩
    rw [← hE] at atEntry
    rw [shownStore, StoreCodec.fromEntries_apply_eq_none_iff]
    intro inKeys
    obtain ⟨other, member, keyOther⟩ := List.mem_map.mp inKeys
    obtain ⟨position', bound', found', opened, isOpened⟩ := keyPosition other member
    have bound : position < E.length := by
      by_contra outside
      rw [List.getElem?_eq_none (by omega)] at atEntry
      cases atEntry
    rw [List.getElem?_eq_getElem bound] at atEntry
    have sameEntry := Option.some.inj atEntry
    have samePosition : position' = position := by
      have keys : (E.map Sigma.fst)[position']'(by simpa using bound') =
          (E.map Sigma.fst)[position]'(by simpa using bound) := by
        simp only [List.getElem_map, found', sameEntry, keyOther, keyed]
      exact (List.Nodup.getElem_inj_iff distinctE).mp keys
    subst samePosition
    rw [isOpened] at sealed
    cases sealed

theorem opened_display_is_commit : OpenedDisplayIsCommitStatement := by
  intro deployment directory snapshot semantics ambient command target prepared view shown
    packedBytes frame items checked served
  obtain ⟨cell, patch, rooted, bytes, noSealed, member, valid, rfl⟩ := checkOpened_ok checked served
  have supported := memberPatch_supported command target cell.logical patch member
  have signedRoot := computeTarget_root snapshot semantics ambient command target prepared.pre
    prepared.post prepared.candidate.modeEvidence.down supported
  have rootActual : StoreCodec.rootOfLeaves (targetWire target) (items.map StoreHiding.Item.leaf) =
      StoreCodec.rootOfLeaves (targetWire target) (StoreCodec.leaves (targetWire target) prepared.pre.logical) := by
    have preRoot : prepared.pre.root = target.materializer.rootOf prepared.pre.logical := rfl
    rw [target_rootOf] at preRoot
    change StoreHiding.rootOfItems (targetWire target) items = _
    rw [rooted, signedRoot, preRoot]
    rfl
  by_cases sameLeaves : items.map StoreHiding.Item.leaf = StoreCodec.leaves (targetWire target) prepared.pre.logical
  swap
  · exact Or.inl (Or.inl ⟨sameLeaves, rootActual⟩)
  by_cases misaligned : ∃ (position : Nat) (opened : StoreCodec.Opening) (entry : Entry target.layout),
      items[position]? = some (.inl opened) ∧
        (StoreCodec.entries (targetWire target) prepared.pre.logical)[position]? = some entry ∧
        opened ≠ StoreCodec.opening (targetWire target) prepared.pre.logical entry
  · obtain ⟨position, opened, entry, isOpened, atEntry, different⟩ := misaligned
    refine Or.inl (Or.inr ⟨position, opened, entry, isOpened, atEntry, different, ?_⟩)
    have leafAt := congrArg (fun leaves => leaves[position]?) sameLeaves
    simp only [List.getElem?_map, isOpened, Option.map_some, StoreCodec.leaves, atEntry] at leafAt
    exact Option.some.inj leafAt
  push Not at misaligned
  obtain ⟨agrees, sealedEmpty⟩ := shown_agrees (targetWire target) items prepared.pre.logical
    cell.logical sameLeaves misaligned bytes
  have memberActual : memberPatch command target prepared.pre.logical = .ok patch := by
    cases reads : patchReadsPre target
    · rw [← member]
      exact memberPatch_pre_independent command target _ _ reads
    · have same : cell.logical = prepared.pre.logical := by
        apply Minidregg.Theory.SparseMap.ext
        intro address
        apply agrees address
        rintro ⟨position, entry, leaf, _, _, sealedAt⟩
        have inItems := List.mem_of_getElem? sealedAt
        have := noSealed reads _ inItems
        simp at this
      rw [← same]
      exact member
  obtain ⟨tail, split, frameTail⟩ :=
    targetPatch_split snapshot semantics ambient command target prepared.pre patch memberActual
  have actualValid : Patch.ValidFrom prepared.pre.logical patch := by
    have whole := prepared.candidate.validated.valid
    change Patch.ValidFrom prepared.pre.logical
      (targetPatch snapshot semantics ambient command target prepared.pre) at whole
    rw [split] at whole
    exact ((Patch.validFrom_append _ _ _).mp whole).1
  refine Or.inr ⟨fun address owned unsealed => ?_, fun address owned sealed => ?_⟩
  · rw [post_run prepared, split, Patch.run_append, frameTail _ address owned]
    exact run_congr_at address patch _ _ (agrees address unsealed).symm
  · rw [post_run prepared, split, Patch.run_append, frameTail _ address owned]
    have present : prepared.pre.logical address ≠ none := by
      obtain ⟨position, entry, leaf, atEntry, keyed, _⟩ := sealed
      have inE := List.mem_of_getElem? atEntry
      have stored := StoreHiding.mem_entries (targetWire target) inE
      intro absent
      subst keyed
      rw [absent] at stored
      cases stored
    exact Patch.run_frame _ _ _ (untouched_of_both_valid address patch cell.logical
      prepared.pre.logical (sealedEmpty address sealed) present valid actualValid)

theorem pre_reading_sealed_refused : PreReadingSealedRefusedStatement := by
  intro deployment command target view packedBytes frame items packed cell reads served framed rooted
    decoded selected opened sealed
  simp [checkOpened, served, framed, rooted, decoded, selected, opened, reads, sealed]

theorem opened_view_refused : OpenedViewRefusedStatement := by
  refine ⟨?_, ?_⟩
  · intro deployment command target view packedBytes frame items served framed unrooted
    simp [checkOpened, served, framed, unrooted]
  · intro deployment command target view packedBytes frame items packed cell served framed rooted
      decoded selected mismatch
    simp [checkOpened, served, framed, rooted, decoded, selected, mismatch]

theorem entries_filter {L : Layout.{0, 0, 0}} (wire : StoreCodec.Wire L) (keep : Address L → Prop)
    [DecidablePred keep] (store : Store L) :
    StoreCodec.entries wire (Minidregg.Theory.SparseMap.filterKeys keep store) =
      (StoreCodec.entries wire store).filter fun entry => decide (keep entry.1) := by
  have ordered : ((StoreCodec.entries wire store).filter fun entry => decide (keep entry.1)).Pairwise
      (StoreCodec.AddressLT wire) :=
    (StoreCodec.entries_pairwise wire store).sublist List.filter_sublist
  have distinct :
      (((StoreCodec.entries wire store).filter fun entry => decide (keep entry.1)).map Sigma.fst).Nodup :=
    (entries_keys_nodup wire store).sublist (List.filter_sublist.map _)
  have same : StoreCodec.fromEntries
      ((StoreCodec.entries wire store).filter fun entry => decide (keep entry.1)) =
      Minidregg.Theory.SparseMap.filterKeys keep store := by
    apply Minidregg.Theory.SparseMap.ext
    intro address
    rw [Minidregg.Theory.SparseMap.filterKeys_apply]
    by_cases kept : keep address
    · rw [if_pos kept]
      cases present : store address with
      | none =>
          rw [StoreCodec.fromEntries_apply_eq_none_iff]
          intro member
          obtain ⟨entry, inFiltered, rfl⟩ := List.mem_map.mp member
          have stored := StoreHiding.mem_entries wire (List.mem_filter.mp inFiltered).1
          rw [present] at stored
          cases stored
      | some value =>
          exact StoreCodec.fromEntries_apply_of_mem _ distinct (entry := ⟨address, value⟩)
            (List.mem_filter.mpr ⟨mem_entries_of_present wire store present, by simpa using kept⟩)
    · rw [if_neg kept]
      change _ = none
      rw [StoreCodec.fromEntries_apply_eq_none_iff]
      intro member
      obtain ⟨entry, inFiltered, rfl⟩ := List.mem_map.mp member
      exact kept (by simpa using (List.mem_filter.mp inFiltered).2)
  rw [← same]
  exact StoreCodec.entries_fromEntries_of_pairwise wire _ ordered

theorem openedBytes_items {L : Layout.{0, 0, 0}} (wire : StoreCodec.Wire L)
    (visible : Address L → Prop) [DecidablePred visible] (store : Store L) :
    openedBytes (StoreHiding.items wire visible store) =
      ((StoreCodec.entries wire store).filter fun entry => decide (visible entry.1)).map
        (StoreCodec.entryBytes wire) := by
  unfold openedBytes StoreHiding.items
  rw [List.filterMap_map]
  induction StoreCodec.entries wire store with
  | nil => rfl
  | cons entry rest induction =>
      rw [List.filterMap_cons, List.filter_cons]
      by_cases shown : visible entry.1
      · simp only [Function.comp_apply, StoreHiding.itemOf, if_pos shown, Sum.getLeft?_inl,
          Option.map_some, decide_eq_true shown, if_true, List.map_cons]
        exact congrArg₂ List.cons rfl induction
      · simp only [Function.comp_apply, StoreHiding.itemOf, if_neg shown, Sum.getLeft?_inr,
          Option.map_none, decide_eq_false shown, Bool.false_eq_true, if_false]
        exact induction

set_option backward.isDefEq.respectTransparency false in
theorem honest_scalar_view_accepted : HonestScalarViewAcceptedStatement := by
  intro deployment command kind id capability version actions observe audienceEpoch audienceRoster
    fields payload balances quote narrowed target selected valid
  have opens := NativeObservationController.root_opens fields ⟨.declaredObject, payload⟩
    (wire := DeclaredEffectCell.wire) rfl
  have narrowedLogical : narrowed.logical =
      Minidregg.Theory.SparseMap.filterKeys (ResourceObservationAdmission.Visible fields .declaredObject) payload.logical := by
    simp only [target, selectTarget, CanonicalCellRegistry.selectDeclared,
      ResourceObservationAdmission.narrowPacked] at selected
    split at selected
    · cases kind <;> simp at selected
      rw [← selected]
      exact materialize_logical _ _
    · cases selected
  have served : servedOpening target (NativeObservationController.resourceViewCodec.encode
      (NativeObservationController.resourceView fields ⟨.declaredObject, payload⟩ balances quote)) =
      .ok (CellRegistry.PackedCell.bytes CanonicalCellRegistry.registry
          (ResourceObservationAdmission.narrowPacked fields ⟨.declaredObject, payload⟩),
        (NativeObservationController.openingView fields ⟨.declaredObject, payload⟩).1,
        (NativeObservationController.openingView fields ⟨.declaredObject, payload⟩).2) := by
    unfold servedOpening
    rw [NativeObservationController.resourceViewCodec.decode_encode]
    rfl
  have narrowedEntries : (StoreCodec.entries (targetWire target) narrowed.logical).map
      (StoreCodec.entryBytes (targetWire target)) =
      openedBytes (NativeObservationController.openingView fields ⟨.declaredObject, payload⟩).2 := by
    show (StoreCodec.entries DeclaredEffectCell.wire narrowed.logical).map
        (StoreCodec.entryBytes DeclaredEffectCell.wire) =
      openedBytes (StoreHiding.items DeclaredEffectCell.wire
        (ResourceObservationAdmission.Visible fields .declaredObject) payload.logical)
    rw [narrowedLogical, entries_filter, openedBytes_items]
  have decoded : CanonicalCellRegistry.cellCodec.decode
      (CellRegistry.PackedCell.bytes CanonicalCellRegistry.registry
        (ResourceObservationAdmission.narrowPacked fields ⟨.declaredObject, payload⟩)) =
      some (ResourceObservationAdmission.narrowPacked fields ⟨.declaredObject, payload⟩) :=
    CanonicalCellRegistry.cellCodec.decode_encode _
  refine ⟨Patch.run narrowed.logical
    (DeclaredResourceScalar.cellPatch (scalarCommand command target actions)), ?_⟩
  unfold checkOpened
  rw [served]
  dsimp only
  rw [if_pos (show _ = StoreCodec.frame (targetWire target) from opens.2),
    if_pos (show StoreHiding.rootOfItems (targetWire target) _ = target.expectedTargetRoot from opens.1.symm),
    decoded]
  dsimp only
  rw [selected]
  dsimp only
  rw [if_pos narrowedEntries]
  rw [if_neg (show ¬ (patchReadsPre target && _) = true by simp [patchReadsPre, target])]
  show (if Patch.ValidFrom narrowed.logical
      (DeclaredResourceScalar.cellPatch (scalarCommand command target actions)) then _ else _) = _
  rw [if_pos valid]

/-- The parts of the honest Host's view that thin consent reads. -/
theorem servedOpening_honest (target : Target) (fields : Option (Finset CellField))
    (packed : CellRegistry.PackedCell CanonicalCellRegistry.registry) (balances : List (Nat × Int))
    (quote : Option RunComputeView.ComputeQuote) :
    servedOpening target (NativeObservationController.resourceViewCodec.encode
      (NativeObservationController.resourceView fields packed balances quote)) =
      .ok (CellRegistry.PackedCell.bytes CanonicalCellRegistry.registry
          (ResourceObservationAdmission.narrowPacked fields packed),
        (NativeObservationController.openingView fields packed).1,
        (NativeObservationController.openingView fields packed).2) := by
  unfold servedOpening
  rw [NativeObservationController.resourceViewCodec.decode_encode]
  rfl

theorem decode_narrowed (fields : Option (Finset CellField))
    (packed : CellRegistry.PackedCell CanonicalCellRegistry.registry) :
    CanonicalCellRegistry.cellCodec.decode
      (CellRegistry.PackedCell.bytes CanonicalCellRegistry.registry
        (ResourceObservationAdmission.narrowPacked fields packed)) =
      some (ResourceObservationAdmission.narrowPacked fields packed) :=
  CanonicalCellRegistry.cellCodec.decode_encode _

/-- The converse of `checkOpened_ok`: a view that passes the opening checks is shown as the
member patch run on its cell. -/
theorem checkOpened_of {deployment : Deployment} {command : Command} {target : Target}
    {view packedBytes frame : List UInt8} {items : List StoreHiding.Item}
    {packed : CellRegistry.PackedCell Registry} {cell : TargetCell target}
    (served : servedOpening target view = .ok (packedBytes, frame, items))
    (framed : frame = StoreCodec.frame (targetWire target))
    (rooted : StoreHiding.rootOfItems (targetWire target) items = target.expectedTargetRoot)
    (decoded : CanonicalCellRegistry.cellCodec.decode packedBytes = some packed)
    (selected : selectTarget deployment target packed = some cell)
    (opened : (StoreCodec.entries (targetWire target) cell.logical).map
      (StoreCodec.entryBytes (targetWire target)) = openedBytes items)
    (preOk : ¬ (patchReadsPre target && items.any Sum.isRight) = true) :
    checkOpened deployment command target view =
      match memberPatch command target cell.logical with
      | .error refusal => .error refusal
      | .ok patch =>
        if Patch.ValidFrom cell.logical patch then .ok (Patch.run cell.logical patch)
        else .error (.patchRefused target.target) := by
  unfold checkOpened
  rw [served]
  dsimp only
  rw [if_pos framed, if_pos rooted, decoded]
  dsimp only
  rw [selected]
  dsimp only
  rw [if_pos opened, if_neg preOk]

/-- A view that shows every address seals no item. -/
theorem items_none_sealed {L : Layout.{0, 0, 0}} (wire : StoreCodec.Wire L)
    (visible : Address L → Prop) [DecidablePred visible] (store : Store L)
    (all : ∀ address, visible address) :
    (StoreHiding.items wire visible store).any Sum.isRight = false := by
  simp [StoreHiding.items, StoreHiding.itemOf, all]

/-- A full-scope reader is shown every address of a cell without a hiding key. -/
theorem visible_full {kind : CanonicalCellRegistry.Kind}
    (unblinded : ∀ address, CanonicalCellRegistry.isBlinding kind address = false) :
    ∀ address, ResourceObservationAdmission.Visible none kind address := by
  intro address
  refine ⟨?_, unblinded address⟩
  unfold ResourceObservationAdmission.Kept
  split <;> trivial

set_option backward.isDefEq.respectTransparency false in
theorem honest_account_scalar_view_accepted : HonestAccountScalarViewAcceptedStatement := by
  intro deployment command kind id capability version actions observe audienceEpoch audienceRoster
    fields payload balances quote narrowed target selected valid
  have opens := NativeObservationController.root_opens fields ⟨.accountMetadata, payload⟩
    (wire := DeclaredEffectCell.wire) rfl
  have narrowedLogical : narrowed.logical =
      Minidregg.Theory.SparseMap.filterKeys (ResourceObservationAdmission.Visible fields .accountMetadata) payload.logical := by
    simp only [target, selectTarget, CanonicalCellRegistry.selectDeclared,
      ResourceObservationAdmission.narrowPacked] at selected
    split at selected
    · cases kind <;> simp at selected
      rw [← selected]
      exact materialize_logical _ _
    · cases selected
  refine ⟨Patch.run narrowed.logical
    (DeclaredResourceScalar.cellPatch (scalarCommand command target actions)), ?_⟩
  rw [checkOpened_of (servedOpening_honest target fields _ balances quote) opens.2 opens.1.symm
    (decode_narrowed fields _) selected ?opened (by simp [patchReadsPre, target])]
  · show (if Patch.ValidFrom narrowed.logical
      (DeclaredResourceScalar.cellPatch (scalarCommand command target actions)) then _ else _) = _
    rw [if_pos valid]
  · show (StoreCodec.entries DeclaredEffectCell.wire narrowed.logical).map
        (StoreCodec.entryBytes DeclaredEffectCell.wire) =
      openedBytes (StoreHiding.items DeclaredEffectCell.wire
        (ResourceObservationAdmission.Visible fields .accountMetadata) payload.logical)
    rw [narrowedLogical, entries_filter, openedBytes_items]

set_option backward.isDefEq.respectTransparency false in
theorem honest_world_view_accepted : HonestWorldViewAcceptedStatement := by
  intro deployment command kind id capability version actions observe audienceEpoch audienceRoster
    payload balances quote narrowed patch target view selected prepared valid
  have opens := NativeObservationController.root_opens none ⟨.worldInstance, payload⟩
    (wire := WorldKindCell.instanceWire) rfl
  have all := visible_full (kind := .worldInstance) (fun _ => rfl)
  have narrowedLogical : narrowed.logical =
      Minidregg.Theory.SparseMap.filterKeys (ResourceObservationAdmission.Visible none .worldInstance) payload.logical := by
    simp only [target, selectTarget, ResourceObservationAdmission.narrowPacked] at selected
    split_ifs at selected
    rw [← Option.some.inj selected]
    exact materialize_logical _ _
  have none_sealed : (NativeObservationController.openingView none ⟨.worldInstance, payload⟩).2.any
      Sum.isRight = false :=
    items_none_sealed WorldKindCell.instanceWire _ payload.logical all
  refine ⟨⟨Patch.run narrowed.logical patch, ?_⟩, ?_⟩
  · rw [checkOpened_of (servedOpening_honest target none _ balances quote) opens.2 opens.1.symm
      (decode_narrowed none _) selected ?opened (by rw [none_sealed]; simp)]
    · have member : memberPatch command target narrowed.logical = .ok patch := by
        simp [memberPatch, target, prepared]
      rw [member]
      exact if_pos valid
    · show (StoreCodec.entries WorldKindCell.instanceWire narrowed.logical).map
          (StoreCodec.entryBytes WorldKindCell.instanceWire) =
        openedBytes (StoreHiding.items WorldKindCell.instanceWire
          (ResourceObservationAdmission.Visible none .worldInstance) payload.logical)
      rw [narrowedLogical, entries_filter, openedBytes_items]
  · unfold sealsNothing
    rw [servedOpening_honest]
    dsimp only
    rw [none_sealed]
    rfl

set_option backward.isDefEq.respectTransparency false in
theorem honest_kind_definition_view_accepted : HonestKindDefinitionViewAcceptedStatement := by
  intro deployment command kind id capability version definition observe audienceEpoch audienceRoster
    payload balances quote narrowed patch target view selected prepared valid
  have opens := NativeObservationController.root_opens none ⟨.worldKind, payload⟩
    (wire := WorldKindCell.definitionWire) rfl
  have all := visible_full (kind := .worldKind) (fun _ => rfl)
  have narrowedLogical : narrowed.logical =
      Minidregg.Theory.SparseMap.filterKeys (ResourceObservationAdmission.Visible none .worldKind) payload.logical := by
    simp only [target, selectTarget, ResourceObservationAdmission.narrowPacked] at selected
    split_ifs at selected
    rw [← Option.some.inj selected]
    exact materialize_logical _ _
  have none_sealed : (NativeObservationController.openingView none ⟨.worldKind, payload⟩).2.any
      Sum.isRight = false :=
    items_none_sealed WorldKindCell.definitionWire _ payload.logical all
  refine ⟨⟨Patch.run narrowed.logical patch, ?_⟩, ?_⟩
  · rw [checkOpened_of (servedOpening_honest target none _ balances quote) opens.2 opens.1.symm
      (decode_narrowed none _) selected ?opened (by rw [none_sealed]; simp)]
    · have member : memberPatch command target narrowed.logical = .ok patch := by
        simp [memberPatch, target, prepared]
      rw [member]
      exact if_pos valid
    · show (StoreCodec.entries WorldKindCell.definitionWire narrowed.logical).map
          (StoreCodec.entryBytes WorldKindCell.definitionWire) =
        openedBytes (StoreHiding.items WorldKindCell.definitionWire
          (ResourceObservationAdmission.Visible none .worldKind) payload.logical)
      rw [narrowedLogical, entries_filter, openedBytes_items]
  · unfold sealsNothing
    rw [servedOpening_honest]
    dsimp only
    rw [none_sealed]
    rfl

set_option backward.isDefEq.respectTransparency false in
theorem honest_content_read_view_accepted : HonestContentReadViewAcceptedStatement := by
  intro deployment command kind id capability version observe audienceEpoch audienceRoster
    fields payload balances quote narrowed target selected
  have opens := NativeObservationController.root_opens fields ⟨.content, payload⟩
    (wire := HyperdocumentCell.contentWire) rfl
  have narrowedLogical : narrowed.logical =
      Minidregg.Theory.SparseMap.filterKeys (ResourceObservationAdmission.Visible fields .content) payload.logical := by
    simp only [target, selectTarget, ResourceObservationAdmission.narrowPacked] at selected
    split_ifs at selected
    rw [← Option.some.inj selected]
    exact materialize_logical _ _
  refine ⟨Patch.run narrowed.logical [], ?_⟩
  rw [checkOpened_of (servedOpening_honest target fields _ balances quote) opens.2 opens.1.symm
    (decode_narrowed fields _) selected ?opened (by simp [patchReadsPre, target])]
  · show (if Patch.ValidFrom narrowed.logical [] then _ else _) = _
    rw [if_pos (show Patch.ValidFrom narrowed.logical [] from trivial)]
  · show (StoreCodec.entries HyperdocumentCell.contentWire narrowed.logical).map
        (StoreCodec.entryBytes HyperdocumentCell.contentWire) =
      openedBytes (StoreHiding.items HyperdocumentCell.contentWire
        (ResourceObservationAdmission.Visible fields .content) payload.logical)
    rw [narrowedLogical, entries_filter, openedBytes_items]

set_option backward.isDefEq.respectTransparency false in
theorem honest_kind_read_view_accepted : HonestKindReadViewAcceptedStatement := by
  intro deployment command kind id capability version observe audienceEpoch audienceRoster
    fields payload balances quote narrowed target selected
  have opens := NativeObservationController.root_opens fields ⟨.worldKind, payload⟩
    (wire := WorldKindCell.definitionWire) rfl
  have narrowedLogical : narrowed.logical =
      Minidregg.Theory.SparseMap.filterKeys (ResourceObservationAdmission.Visible fields .worldKind) payload.logical := by
    simp only [target, selectTarget, ResourceObservationAdmission.narrowPacked] at selected
    split_ifs at selected
    rw [← Option.some.inj selected]
    exact materialize_logical _ _
  refine ⟨Patch.run narrowed.logical [], ?_⟩
  rw [checkOpened_of (servedOpening_honest target fields _ balances quote) opens.2 opens.1.symm
    (decode_narrowed fields _) selected ?opened (by simp [patchReadsPre, target])]
  · show (if Patch.ValidFrom narrowed.logical [] then _ else _) = _
    rw [if_pos (show Patch.ValidFrom narrowed.logical [] from trivial)]
  · show (StoreCodec.entries WorldKindCell.definitionWire narrowed.logical).map
        (StoreCodec.entryBytes WorldKindCell.definitionWire) =
      openedBytes (StoreHiding.items WorldKindCell.definitionWire
        (ResourceObservationAdmission.Visible fields .worldKind) payload.logical)
    rw [narrowedLogical, entries_filter, openedBytes_items]

set_option backward.isDefEq.respectTransparency false in
theorem honest_content_stream_write_named : HonestContentStreamWriteNamedStatement := by
  refine ⟨?_, ?_⟩
  · intro deployment command kind id capability version contentCommand observe audienceEpoch
      audienceRoster fields payload balances quote narrowed target selected
    have opens := NativeObservationController.root_opens fields ⟨.content, payload⟩
      (wire := HyperdocumentCell.contentWire) rfl
    have narrowedLogical : narrowed.logical =
        Minidregg.Theory.SparseMap.filterKeys (ResourceObservationAdmission.Visible fields .content) payload.logical := by
      simp only [target, selectTarget, ResourceObservationAdmission.narrowPacked] at selected
      split_ifs at selected
      rw [← Option.some.inj selected]
      exact materialize_logical _ _
    rw [checkOpened_of (servedOpening_honest target fields _ balances quote) opens.2 opens.1.symm
      (decode_narrowed fields _) selected ?openedContent (by simp [patchReadsPre, target])]
    · exact ⟨_, rfl⟩
    · show (StoreCodec.entries HyperdocumentCell.contentWire narrowed.logical).map
          (StoreCodec.entryBytes HyperdocumentCell.contentWire) =
        openedBytes (StoreHiding.items HyperdocumentCell.contentWire
          (ResourceObservationAdmission.Visible fields .content) payload.logical)
      rw [narrowedLogical, entries_filter, openedBytes_items]
  · intro deployment command kind id capability version request observe audienceEpoch
      audienceRoster fields payload balances quote narrowed target selected
    have opens := NativeObservationController.root_opens fields ⟨.stream, payload⟩
      (wire := StreamCell.headWire) rfl
    have narrowedLogical : narrowed.logical =
        Minidregg.Theory.SparseMap.filterKeys (ResourceObservationAdmission.Visible fields .stream) payload.logical := by
      simp only [target, selectTarget, ResourceObservationAdmission.narrowPacked] at selected
      split_ifs at selected
      rw [← Option.some.inj selected]
      exact materialize_logical _ _
    rw [checkOpened_of (servedOpening_honest target fields _ balances quote) opens.2 opens.1.symm
      (decode_narrowed fields _) selected ?openedStream (by simp [patchReadsPre, target])]
    · exact ⟨_, rfl⟩
    · show (StoreCodec.entries StreamCell.headWire narrowed.logical).map
          (StoreCodec.entryBytes StreamCell.headWire) =
        openedBytes (StoreHiding.items StreamCell.headWire
          (ResourceObservationAdmission.Visible fields .stream) payload.logical)
      rw [narrowedLogical, entries_filter, openedBytes_items]

#assert_axioms target_rootOf run_congr_at untouched_of_both_valid checkOpened_ok shown_agrees
  opened_display_is_commit opened_view_refused pre_reading_sealed_refused entries_filter
  openedBytes_items honest_scalar_view_accepted servedOpening_honest decode_narrowed checkOpened_of
  items_none_sealed visible_full honest_account_scalar_view_accepted honest_world_view_accepted
  honest_kind_definition_view_accepted honest_content_read_view_accepted honest_kind_read_view_accepted
  honest_content_stream_write_named

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
    effectsDigest := (Sp800185Cshake256.hash "DREGG.RESOURCE.TRANSACTION.OBSERVE/v8".toUTF8.toList
      ((StreamCodec.product bytesStream StreamCodec.nat).encode
        (commandBytes domain semantics command, target.target))).digest }

/-- What thin consent shows for one target: its id and, for a write, the canonical bytes of the
post at every member-authored address the served opening discloses (`opened_display_is_commit`),
with the post's deployed root only when the opening seals nothing. When it seals an entry, the
shown store lacks that entry, so its root is not the committed root and is not shown. -/
structure Display where
  target : Nat
  post : Option (List UInt8 × Option Digest)
  deriving DecidableEq, Repr

/-- One target: its served view checked over its salted opening (`checkOpened`) and its
display. -/
def displayTarget (deployment : Deployment) (command : Command) (target : Target)
    (view : List UInt8) : Except Refusal Display := do
  let shown ← checkOpened deployment command target view
  if target.isRead then pure ⟨target.target, none⟩
  else
    let encoded := target.materializer.codec.encode shown
    pure ⟨target.target, some (encoded,
      if sealsNothing target view then some (target.materializer.rootBytes encoded) else none)⟩

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
