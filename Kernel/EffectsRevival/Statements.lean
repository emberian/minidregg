/-
# `Kernel/EffectsRevival/Statements.lean` — the widened declaration and the dispatch keystone, STATED

The statement half of `docs/EFFECTS-REVIVAL.md` (the deputy's Phase-3 design,
`docs/review/2026-10-27-untouched-areas/EFFECTS.md`, made concrete).  Every keystone below
enters as a `Prop` with its ATLAS fields (satisfiable, teeth, premise inhabitation).  This
file proves nothing; the witnesses' DATA is built here, their proofs follow the auditor's
verdict.

## What is stated

* §1-§5 live in `Effects/Revival/Engine.lean` (kernel-free, small closure); this file
  imports it and holds §6-§7.  It lives under `Kernel/` because §6-§7 are stated over the
  deployed controller: a consumer of the Effects engine, never part of it (the namespace stays
  `Minidregg.Effects.Revival`).
* §1 `Substrate`: the guarded primitive algebra an effect emits into.  `storeSubstrate L` is
  the deployed one (`Theory.Store`'s guarded `Op`s); the Book's posting algebra is the second
  (transfer, migration step 2).
* §2 `EffectSpec`: ONE effect as ONE declaration.  Its semantics emits a first-order
  descriptor (a list of primitives) or refuses BY NAME; the kernel's rotate (the blinding
  ratchet), the field classification, the declared frame, the verb and the law's view are
  declaration data.  The checked executor `exec` is derived; nothing about it is authored.
* §3 `Handler`, `Registry`, `dispatch`, `LawfulRegistry`: the open registry and the one
  dispatcher.
* §4 `Dispatches R legacy d`: what it means for a dispatcher `d` to dispatch through `R`
  (agreement, unregistered refuses by name, frame law, no twin), a predicate on ANY candidate
  `d`, so a fail-open or misreading dispatcher is refuted, not assumed away.
* §5 Engine keystone and completeness keystone, with the two-entry pole.
* §6 The LIVE keystone: `contentSpec`, the declaration of the deployed content-cell write
  (`Payload.content`, wire code 1, what `doc append` signs), and `ContentAgreement`: the
  hand-written arm of `DeclaredResourceController.computeTarget`/`targetPatch` and its
  authority classification (`targetField`, `targetRatchet`, `targetAmount`, `payloadVerb`,
  `targetProjection`) agree with the declaration.  This is the gate of the commit that
  deletes that hand arm.

## Vacuity, said out loud

`Dispatches R [] (dispatch R)` is the engine's generic theorem (the analogue of
`EffectSpec.derived_agrees`): its content is that `Dispatches` DISCRIMINATES (§5 teeth: a
misreading, a fail-open and an unframed dispatcher are each refuted), not that `dispatch`
satisfies it.  The deployed content lives in `ContentAgreement`, stated against today's hand
arm (a real refinement, not an `rfl` through a reader this lane wrote), and in
`contentSpec.Complete`, the declared frame of the fifteen content actions (a claim that can
be false, with its own teeth).
-/
module

public import Effects.Revival.Engine
public import Kernel.DeclaredResourceController
public import Kernel.ContentEffect

@[expose] public section

namespace Minidregg.Effects.Revival

open Minidregg.Compiler
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Theory
open Minidregg.Theory.CellState
open Minidregg.Theory.Store
open Minidregg.Theory.TypedAuthorization
open Minidregg.Kernel

set_option autoImplicit false

/-! ## §6. The LIVE keystone: the content-cell write behind `doc append`. -/

/-- What a declared-resource target's computation consumes of its transaction (the
arguments of `DeclaredResourceController.computeTarget`, and the target's header fields a
semantics reads). -/
structure LiveCtx where
  snapshot : DeclaredResourceController.AuthoritySnapshot
  semantics : Digest
  ambient : DeclaredResourceController.Ambient
  command : DeclaredResourceController.Command
  kind : ResourceKind
  target : Nat
  capability : CapabilityId

/-- The registry's context of a target under a live context (`targetCtx`), its observe and
audience fields absent: what the content declaration reads. -/
def liveEffectCtx (ctx : LiveCtx) : DeclaredResourceController.EffectCtx :=
  DeclaredResourceController.targetCtx ctx.snapshot ctx.semantics ctx.ambient ctx.command
    ctx.kind ctx.target ctx.capability none none none

abbrev ContentSpec :=
  EffectSpec LiveCtx ContentSubstrate ContentResource.Command ContentResource.Reject

/-- **The first live declaration: the content-cell write** (`Kernel/ContentEffect.lean`,
`DeclaredResourceController.contentSpec`), read under a live context. -/
def contentSpec : ContentSpec := DeclaredResourceController.contentSpec.comap liveEffectCtx

/-! What the declaration is under a live context, field by field (each `rfl`): the hand arm's own
expressions, for the agreement proofs to simplify by. -/

theorem contentSpec_sem (ctx : LiveCtx) (command : ContentResource.Command)
    (s : Store Hyperdocument.layout) :
    contentSpec.sem ctx command s =
      if command.actions.isEmpty then .error .emptyActions
      else (ContentResource.run ⟨ctx.command.subject, ctx.kind, ctx.capability⟩
          (DeclaredResourceController.contentOperation ctx.snapshot ctx.semantics ctx.command)
          (ContentResource.documentOf ctx.target)
          (DeclaredResourceController.contentContext ctx.snapshot ctx.ambient ctx.command)
          s command).map Prod.snd := rfl

@[simp] theorem contentSpec_accepts (kind : ResourceKind) : contentSpec.accepts kind = (kind == .object) := rfl

@[simp] theorem contentSpec_version : contentSpec.version = ContentResource.commandVersion := rfl

@[simp] theorem contentSpec_commutes (command : ContentResource.Command) : contentSpec.commutes command = command.commutes := rfl

@[simp] theorem contentSpec_rotate (ctx : LiveCtx) (s : Store Hyperdocument.layout) :
    contentSpec.rotate ctx s = HyperdocumentCell.contentBlinding.patch s ctx.ambient.height := rfl

@[simp] theorem contentSpec_frame (command : ContentResource.Command) : contentSpec.frame command = contentFrame command := rfl

@[simp] theorem contentSpec_field : contentSpec.field = ResourceObservationAdmission.contentFieldAt := rfl

@[simp] theorem contentSpec_amount (a : Address Hyperdocument.layout) (v : Option (Hyperdocument.layout.Value a.1)) : contentSpec.amount a v = 0 := rfl

@[simp] theorem contentSpec_verb (kind : ResourceKind) (command : ContentResource.Command) : contentSpec.verb kind command = DeclaredResourceScalar.ordinaryVerb kind := rfl

@[simp] theorem contentSpec_opStream : contentSpec.opStream = ContentResource.commandStream := rfl

@[simp] theorem contentSpec_refusalName (r : ContentResource.Reject) : contentSpec.refusalName r = reprStr r := rfl

@[simp] theorem contentSpec_rotated (loc : Address Hyperdocument.layout) :
    contentSpec.rotated loc = (match loc.1 with | .blinding => true | _ => false) := rfl

@[simp] theorem contentSpec_view (site : Site) (command : ContentResource.Command)
    (before after : Store Hyperdocument.layout) :
    contentSpec.view site command before after = ContentResource.project before after command := rfl

/-- A content target with the given header. -/
abbrev contentTarget (ctx : LiveCtx) (version : Nat) (root : Digest)
    (command : ContentResource.Command) (observe : Option CapabilityId)
    (epoch : Option Nat) (roster : Option ObjectAudienceRoster.Roster) :
    DeclaredResourceController.Target :=
  ⟨ctx.kind, ctx.target, ctx.capability, version, root, .content command, observe, epoch, roster⟩

/-- **LIVE KEYSTONE: the deployed content arm agrees with the declaration.**  For every
transaction context, content command and loaded content cell:

1. header — the live arm's three header refusals are the generic ones the declaration's
   `accepts`/`version`/`commutes` determine (`wrongRole`, `unsupportedVersion`, and
   `staleTarget` exactly for a command that does not commute planned over a moved root);
2. acceptance — with the header passing (the planned root is the loaded one, or the
   command commutes, at ANY planned root), the derived executor admits with post `p`
   exactly when the live arm computes `p` AND the live patch validates at the loaded
   store (what `prepareTarget` requires before it builds a candidate);
3. refusal — a content refusal of the live arm is the declaration's, by name;
4. descriptor — the live patch IS the declaration's descriptor followed by its rotate
   (`computeTarget`/`targetPatch` stop being twins);
5. authority — `targetField`, `targetRatchet`, `targetAmount`, `payloadVerb` and
   `targetProjection` are the declaration's `field`, `rotated`, `amount`, `verb`, `view`.

Clause 2 also tests the declared frame: a live-admitted command that wrote outside
`contentFrame` would be refused `outOfFrame` by `exec`. -/
def ContentAgreement (E : ContentSpec) : Prop :=
  ∀ (ctx : LiveCtx) (command : ContentResource.Command) (pre : ContentResource.ContentCell)
    (observe : Option CapabilityId) (epoch : Option Nat) (roster : Option ObjectAudienceRoster.Roster),
  (∀ version root, E.accepts ctx.kind = false →
    DeclaredResourceController.computeTarget ctx.snapshot ctx.semantics ctx.ambient ctx.command
      (contentTarget ctx version root command observe epoch roster) pre = .error .wrongRole) ∧
  (∀ version root, E.accepts ctx.kind = true → version ≠ E.version →
    DeclaredResourceController.computeTarget ctx.snapshot ctx.semantics ctx.ambient ctx.command
      (contentTarget ctx version root command observe epoch roster) pre = .error .unsupportedVersion) ∧
  (∀ root, E.accepts ctx.kind = true → E.commutes command = false → root ≠ pre.root →
    DeclaredResourceController.computeTarget ctx.snapshot ctx.semantics ctx.ambient ctx.command
      (contentTarget ctx E.version root command observe epoch roster) pre = .error .staleTarget) ∧
  (∀ root, E.accepts ctx.kind = true → (root = pre.root ∨ E.commutes command = true) →
    (∀ post : Store Hyperdocument.layout,
      E.exec 1 ctx command pre.logical = .ok post ↔
        (DeclaredResourceController.computeTarget ctx.snapshot ctx.semantics ctx.ambient ctx.command
            (contentTarget ctx E.version root command observe epoch roster) pre = .ok post ∧
          Patch.ValidFrom pre.logical
            (DeclaredResourceController.targetPatch ctx.snapshot ctx.semantics ctx.ambient ctx.command
              (contentTarget ctx E.version root command observe epoch roster) pre))) ∧
    (∀ r : ContentResource.Reject,
      DeclaredResourceController.computeTarget ctx.snapshot ctx.semantics ctx.ambient ctx.command
          (contentTarget ctx E.version root command observe epoch roster) pre = .error (.content r) →
        E.exec 1 ctx command pre.logical = .error (.refused 1 (E.refusalName r) (E.refusalDetail r))) ∧
    (∀ ps, E.sem ctx command pre.logical = .ok ps →
      DeclaredResourceController.targetPatch ctx.snapshot ctx.semantics ctx.ambient ctx.command
          (contentTarget ctx E.version root command observe epoch roster) pre =
        ps ++ E.rotate ctx pre.logical)) ∧
  (∀ version root,
    (∀ a : Address Hyperdocument.layout,
      DeclaredResourceController.targetField
        (contentTarget ctx version root command observe epoch roster) a = E.field a) ∧
    (∀ a : Address Hyperdocument.layout,
      DeclaredResourceController.targetRatchet
        (contentTarget ctx version root command observe epoch roster) a = E.rotated a) ∧
    (∀ (a : Address Hyperdocument.layout) (v : Hyperdocument.layout.Value a.1),
      DeclaredResourceController.targetAmount
        (contentTarget ctx version root command observe epoch roster) a v = E.amount a (some v)) ∧
    DeclaredResourceController.payloadVerb ctx.kind (.content command) = E.verb ctx.kind command ∧
    (∀ before after : Store Hyperdocument.layout,
      DeclaredResourceController.targetProjection ctx.command.subject
        (contentTarget ctx version root command observe epoch roster) before after =
          E.view ⟨ctx.command.subject, ctx.target⟩ command before after))

/-- The content declaration's own obligation: every admitted content command writes only
its declared fields and its descriptor (with the rotate) replays. -/
def ContentComplete : Prop := contentSpec.Complete

/-! ### The live keystone's ATLAS fields. -/

/-- **Satisfiable / premise inhabitation (the accepted branch).**  The live arm admits some
content command (the native doc-write fixture, `Fixtures/NativeDocWriteFixture*`, is the
intended inhabitant): clause 2 is not vacuously about refusals only. -/
def ContentAccepted : Prop :=
  ∃ (ctx : LiveCtx) (command : ContentResource.Command) (pre : ContentResource.ContentCell)
    (observe : Option CapabilityId) (epoch : Option Nat) (roster : Option ObjectAudienceRoster.Roster)
    (post : Store Hyperdocument.layout),
    contentSpec.accepts ctx.kind = true ∧ command.actions ≠ [] ∧
    DeclaredResourceController.computeTarget ctx.snapshot ctx.semantics ctx.ambient ctx.command
      (contentTarget ctx contentSpec.version pre.root command observe epoch roster) pre = .ok post ∧
    Patch.ValidFrom pre.logical
      (DeclaredResourceController.targetPatch ctx.snapshot ctx.semantics ctx.ambient ctx.command
        (contentTarget ctx contentSpec.version pre.root command observe epoch roster) pre)

/-- The ghost declaration: the same lowering without the kernel's blinding ratchet. -/
def contentGhost : ContentSpec := { contentSpec with rotate := fun _ _ => [] }

/-- The narrowed declaration: the same lowering, its frame without `annotations`. -/
def contentNarrowed : ContentSpec :=
  { contentSpec with frame := fun command => (contentFrame command).erase .annotations }

/-- **Teeth.**  The agreement refutes a declaration that drops the rotate; completeness
refutes a frame that omits a field an action writes (`annotate`). -/
def ContentTeeth : Prop :=
  ¬ ContentAgreement contentGhost ∧ ¬ contentNarrowed.Complete

/-- The pinned declaration: nothing commutes (the controller before 2026-10-28). -/
def contentPinned : ContentSpec := { contentSpec with commutes := fun _ => false }

/-- The permissive declaration: everything commutes. -/
def contentPermissive : ContentSpec := { contentSpec with commutes := fun _ => true }

/-- **Teeth of `commutes`.**  The agreement fixes the declaration's `commutes` from both
sides: it refutes a declaration under which an append planned over a moved root would be
refused (the live arm admits it, `Kernel.ContentCommutingAppend`), and one under which
every command would be admitted over a moved root (the live arm still refuses a command
that is not append-only). -/
def ContentCommuteTeeth : Prop :=
  ¬ ContentAgreement contentPinned ∧ ¬ ContentAgreement contentPermissive

/-- **The live keystone, whole.** -/
def LiveKeystone : Prop := ContentAgreement contentSpec ∧ ContentComplete

/-! ## §7. The DEPLOYED keystone: the Host's target dispatch dispatches through the registry.

`ContentAgreement` alone would license keeping the hand arm beside the declaration (the
law-13 twin).  `HostKeystone` is the statement that closes it: today's target dispatch,
`hostTargetDispatch` (the payload decode, `selectTarget`, `computeTarget`, the
`targetPatch` validation and `packTarget` the controller runs per target), dispatches
through the one-entry registry `[(1, contentHandler)]` with every other payload code in
`hostLegacy`.  `noTwin` puts code 1 out of the hand arms.

**Known false today, by clause:** `unregistered`: an unknown payload tag (9-255, or a code
of 256 and up) is refused `malformed`, not by name, and code 1 is still served by the hand
arm, which `agreement` only matches if the arm is the declaration (`ContentAgreement` plus
`ContentComplete`).  The migration commit makes it true by rewiring the payload decoder
through the registry and deleting the content arms; this statement is that commit's gate.

Scope: the target dispatch, not the whole of `prepareTarget` (the post law, the policy
source, the audience freshness and the authority legs stay the controller's). -/

/-- The host dispatch's context: the target computation's, plus the deployment and the
target header (`selectTarget`'s cell law, the schema version, the expected root, the
observe capability and audience fields). -/
structure HostCtx extends LiveCtx where
  deployment : DeclaredResourceController.Deployment
  version : Nat
  root : Digest
  observe : Option CapabilityId
  epoch : Option Nat
  roster : Option ObjectAudienceRoster.Roster

/-- The cell universe of the live controller. -/
abbrev HostCell := CellRegistry.PackedCell DeclaredResourceController.Registry

/-- The live controller's target for a payload, under a host context. -/
abbrev hostTarget (ctx : HostCtx) (payload : DeclaredResourceController.Payload) :
    DeclaredResourceController.Target :=
  ⟨ctx.kind, ctx.target, ctx.capability, ctx.version, ctx.root, payload, ctx.observe, ctx.epoch, ctx.roster⟩

/-- A live refusal, named. -/
def ofReject (code : Nat) : DeclaredResourceController.Reject → DispatchRefusal
  | .wrongRole => .wrongRole code
  | .unsupportedVersion => .unsupportedVersion code
  | .staleTarget => .staleTarget code
  | .content r => .refused code (reprStr r) []
  | .effect refusal => refusal
  | r => .host code (reprStr r)

/-- **Today's target dispatch**, as the controller runs it per target: decode the payload
(`payloadStream`, the code its tag octet), select the cell (`selectTarget`), compute
(`computeTarget`), validate the target's patch at the loaded store, pack the post
(`packTarget`). -/
def hostTargetDispatch (code : Nat) (bytes : List UInt8) (ctx : HostCtx) (cell : HostCell) :
    Except DispatchRefusal HostCell :=
  if 256 ≤ code then .error (.malformed code) else
  match DeclaredResourceController.payloadStream.toLawful.decode (UInt8.ofNat code :: bytes) with
  | none => .error (.malformed code)
  | some payload =>
    match DeclaredResourceController.selectTarget ctx.deployment (hostTarget ctx payload) cell with
    | none => .error (.wrongRole code)
    | some pre =>
      match DeclaredResourceController.computeTarget ctx.snapshot ctx.semantics ctx.ambient
          ctx.command (hostTarget ctx payload) pre with
      | .error r => .error (ofReject code r)
      | .ok post =>
        if Patch.ValidFrom pre.logical (DeclaredResourceController.targetPatch ctx.snapshot
            ctx.semantics ctx.ambient ctx.command (hostTarget ctx payload) pre) then
          .ok (DeclaredResourceController.packTarget (hostTarget ctx payload)
            (CellState.materialize (hostTarget ctx payload).materializer post))
        else .error (.guardFailed code)

/-- The content cell's header, in the live order: role and cell law and shape
(`wrongRole`), then the schema version.  The expected root is not the header's: the
dispatcher's gate refuses a stale plan from `contentFresh` and the declaration's
`commutes` (`Handler.admits`). -/
def contentHeader (ctx : HostCtx) (cell : HostCell) : Except DispatchRefusal Unit :=
  if contentSpec.accepts ctx.kind = false ∨
      ¬ CanonicalCellRegistry.CellLaw ctx.deployment ctx.target cell then .error (.wrongRole 1)
  else match cell with
    | ⟨.content, value⟩ =>
      if ctx.version ≠ contentSpec.version then .error (.unsupportedVersion 1)
      else .ok ()
    | _ => .error (.wrongRole 1)

/-- Whether the plan's expected root is the content cell's loaded root (a cell of another
role is refused by the header before freshness is asked). -/
def contentFresh (ctx : HostCtx) (cell : HostCell) : Bool :=
  match cell with
  | ⟨.content, value⟩ => decide (ctx.root = value.root)
  | _ => true

/-- **The content handler**: `contentSpec` over the host context, the content header, the
content cell selected and packed. -/
def contentHandlerOf (E : ContentSpec) : Handler HostCtx HostCell where
  S := ContentSubstrate
  O := ContentResource.Command
  R := ContentResource.Reject
  spec := E.comap HostCtx.toLiveCtx
  header := contentHeader
  fresh := contentFresh
  select _ cell := match cell with
    | ⟨.content, value⟩ => some value.logical
    | _ => none
  pack _ s := ⟨.content, CellState.materialize HyperdocumentCell.contentMaterializer s⟩

def contentHandler : Handler HostCtx HostCell := contentHandlerOf contentSpec

/-- Every payload code but content's is still a hand arm. -/
def hostLegacy : List Nat := [0, 2, 3, 4, 5, 6, 7, 8]

/-- **THE DEPLOYED KEYSTONE.** -/
def HostKeystone : Prop :=
  Dispatches [(1, contentHandler)] hostLegacy hostTargetDispatch

/-- **Teeth.**  The host dispatch does not dispatch through a registry whose content
handler drops the rotate, nor through one that also keeps code 1 as a hand arm. -/
def HostTeeth : Prop :=
  ¬ Dispatches [(1, contentHandlerOf contentGhost)] hostLegacy hostTargetDispatch ∧
  ¬ Dispatches [(1, contentHandler)] (1 :: hostLegacy) hostTargetDispatch

/-- **Premise inhabitation.**  The content handler is sound (its `select`/`pack` are
inverse both ways, the store substrate is framed) and lawful. -/
def HostPremise : Prop := contentHandler.Lawful

/-- **Satisfiable (the accepted branch).**  Some content cell and well-encoded content
command are admitted by the host dispatch (the doc-write fixture is the intended
inhabitant, owed). -/
def HostAccepted : Prop :=
  ∃ (op : ContentResource.Command) (ctx : HostCtx) (cell cell' : HostCell),
    hostTargetDispatch 1 (ContentResource.commandStream.encode op) ctx cell = .ok cell'

/-- **Satisfiable (a moved root).**  A commuting content command whose plan names a root that
is NOT the cell's (`contentFresh` false) is admitted by the host dispatch: the accepting pole
of `Kernel.ContentCommutingAppend.CommutingPrepare` (through `PrepareFactors`), over the blinded
sample cell. -/
def HostMovedRootAccepted : Prop :=
  ∃ (op : ContentResource.Command) (ctx : HostCtx) (cell cell' : HostCell),
    op.commutes = true ∧ contentFresh ctx cell = false ∧
    hostTargetDispatch 1 (ContentResource.commandStream.encode op) ctx cell = .ok cell'

/-! ## §7b. The REGISTRY keystone: the deployed target dispatch dispatches code 9 through the registry.

`Payload` has an open constructor, `registered code op`, whose every arm reads the declaration
`effectAt code` (`Kernel/ResourceEffectRegistry.lean`). The cited read is bound at code 9 and
has no constructor and no hand arm; codes 0 to 8 are still hand arms.

`RegistryKeystone` is `Dispatches` of the DEPLOYED functions (`payloadStream`'s decode,
`selectTarget`, `computeTarget`, the `targetPatch` validation, `packTarget`, exactly
`hostTargetDispatch`) through `hostRegistry`, every declaration's handler at its code. Its
`agreement` clause is a refinement of the controller's registered arms against the engine's
`Handler.fire`, at every operation, context and cell; `noTwin` puts every bound code out of the
hand arms; `unregistered` is the refusal by name.

By name at the receiver too: command bytes whose payload tag nothing reads fail
`commandCodec.decode`, and the receiver answers `Reject.effect (.unregistered tag)` for them, not
`malformedCommand` (`Kernel/ResourcePayloadTag.lean`, `UnboundTagNamed`); the JSON face names the
type it did not find (`Host/Json.registeredPayload`). -/

/-- The engine context of a host dispatch. -/
def dispatchCtxOf (ctx : HostCtx) : DeclaredResourceController.DispatchCtx :=
  { DeclaredResourceController.targetCtx ctx.snapshot ctx.semantics ctx.ambient ctx.command
      ctx.kind ctx.target ctx.capability ctx.observe ctx.epoch ctx.roster with
    deployment := ctx.deployment, version := ctx.version, root := ctx.root }

/-- **The registry the Host dispatches through**: every declaration's handler, at its code. -/
def hostRegistry : Registry HostCtx HostCell :=
  DeclaredResourceController.liveRegistry.map fun entry => (entry.1, entry.2.comap dispatchCtxOf)

/-- The payload codes that are still hand arms. -/
def liveLegacy : List Nat := [0, 1, 2, 3, 4, 5, 6, 7, 8]

/-- **The deployed target dispatch.** A code neither bound nor a hand arm is refused by name;
every other code is today's dispatch (`hostTargetDispatch`: the deployed payload decode,
selection, computation, patch validation and packing). -/
def liveTargetDispatch (code : Nat) (bytes : List UInt8) (ctx : HostCtx) (cell : HostCell) :
    Except DispatchRefusal HostCell :=
  if DeclaredResourceController.registeredCode code = false ∧ code ∉ liveLegacy then
    .error (.unregistered code)
  else hostTargetDispatch code bytes ctx cell

/-- **THE REGISTRY KEYSTONE.** -/
def RegistryKeystone : Prop := Dispatches hostRegistry liveLegacy liveTargetDispatch

/-- **Premise inhabitation.** Every bound handler is lawful: sound (its `select` and `pack`
are inverse both ways under every context, the store substrate is framed) and complete. -/
def RegistryPremise : Prop := ∀ code e, hostRegistry.lookup code = some e → e.Lawful

/-- **Satisfiable (both poles of the cited read, through the deployed dispatch).** Some cited
read is admitted and returns the cell it met; and some cited read is refused BY NAME with a
structured detail that decodes to the one key that moved. -/
def RegistryAccepted : Prop :=
  (∃ (reads : List DeclaredResourceController.FieldRead) (ctx : HostCtx) (cell : HostCell),
    reads ≠ [] ∧
    liveTargetDispatch 9 ((StreamCodec.list DeclaredResourceController.fieldReadStream).encode reads)
      ctx cell = .ok cell) ∧
  (∃ (reads : List DeclaredResourceController.FieldRead) (ctx : HostCtx) (cell : HostCell)
      (detail : List UInt8) (key : EffectDeclaration.StateKey),
    liveTargetDispatch 9 ((StreamCodec.list DeclaredResourceController.fieldReadStream).encode reads)
      ctx cell = .error (.refused 9 "citedStale" detail) ∧
    DeclaredResourceController.movedStream.toLawful.decode detail = some [key])

/-- The ghost of the cited read: the same declaration, admitting whatever the cell holds (its
footprint is never compared). -/
def citedGhost : DeclaredResourceController.Effect :=
  { DeclaredResourceController.citedEffect with
    spec := { DeclaredResourceController.citedSpec with sem := fun _ _ _ => .ok [] }
    observes_silent := by
      intro ctx op s ps _ emitted
      exact (Except.ok.inj emitted).symm
    complete := by
      intro ctx op s ps ok
      have empty : ps = [] := (Except.ok.inj ok).symm
      subst empty
      exact ⟨fun loc member => absurd member (Finset.notMem_empty loc), rfl⟩
    view_unjoint := DeclaredResourceController.citedEffect.view_unjoint }

/-- **Teeth.** The deployed dispatch does not dispatch through a registry whose code 9 never
compares the footprint (agreement bites: the deployed arm refuses a stale read), nor through
the registry with code 9 also kept as a hand arm (noTwin bites), nor is a code nothing binds
read by anything (an explicit instance of the refusal by name, at a code beside the bound one
and at one past the octet). -/
def RegistryTeeth : Prop :=
  ¬ Dispatches [(9, (citedGhost.handler 9).comap dispatchCtxOf)] liveLegacy liveTargetDispatch ∧
  ¬ Dispatches hostRegistry (9 :: liveLegacy) liveTargetDispatch ∧
  (∀ bytes ctx cell, liveTargetDispatch 10 bytes ctx cell = .error (.unregistered 10)) ∧
  (∀ bytes ctx cell, liveTargetDispatch 300 bytes ctx cell = .error (.unregistered 300))

/-- A payload's tag: `payloadStream`'s tag octet. -/
def payloadTag (payload : DeclaredResourceController.Payload) : Nat :=
  ((DeclaredResourceController.payloadStream.encode payload).headD 0).toNat

/-- **THE LIVE LEGACY CENSUS, now.** The hand arms' decoder (`legacyPayloadDecode`) produces no
payload at a bound code, and the payload decoder hands a bound tag to its declaration and to
nothing else. With `Payload`'s open constructor the legacy input is what the hand decoder
reads, not the whole inductive. -/
def LiveLegacyCensus : Prop :=
  (∀ bytes payload rest, DeclaredResourceController.legacyPayloadDecode bytes = some (payload, rest) →
    DeclaredResourceController.registeredCode (payloadTag payload) = false) ∧
  (∀ (tag : UInt8) bytes, DeclaredResourceController.registeredOctet tag = true →
    DeclaredResourceController.payloadStream.decodePrefix (tag :: bytes) =
      ((DeclaredResourceController.effectAt tag.toNat).spec.opStream.decodePrefix bytes).map
        fun decoded => (.registered tag decoded.1, decoded.2))

/-- **Census teeth**: an octet nothing binds and no hand arm reads is refused by the payload
decoder itself, whatever follows it. -/
def LiveLegacyCensusTeeth : Prop :=
  ∀ (tag : UInt8) bytes, DeclaredResourceController.registeredOctet tag = false →
    tag.toNat ∉ liveLegacy → DeclaredResourceController.payloadStream.decodePrefix (tag :: bytes) = none

/-! ## §8. The deployed receiver factors through the dispatcher.

`HostKeystone` is about `hostTargetDispatch`, a wrapper this file writes; its contract alone
is not the receiver's.  `PrepareFactors` (pass 27) states the controller's own per-target
preparation, `ResourceTransaction.prepareTarget`, as the content handler's dispatch followed
by `genericChecks`, which reads only the pre and post cells, the policy source and the
audience, never the payload or the command.  The bridge's three directions (acceptance,
acceptance up to generic refusal, refusal by name) are its corollaries, and it is the shape
`prepareTarget` takes at the migration commit, where this is that commit's gate.

`HostLegacyCensus` is the structural deletion check over the live legacy input type, the
`Payload` inductive: no payload constructor at a registered code.  It is FALSE today
(`Payload.content` has tag 1); it becomes provable exactly when the migration removes that
constructor. -/

/-- The host context of a content target. -/
def hostCtxOf (ctx : LiveCtx) (deployment : DeclaredResourceController.Deployment)
    (version : Nat) (root : Digest) (observe : Option CapabilityId) (epoch : Option Nat)
    (roster : Option ObjectAudienceRoster.Roster) : HostCtx :=
  { ctx with deployment, version, root, observe, epoch, roster }

/-- The receiver's checks after the effect, payload-blind by signature: the final-post law,
the policy source, audience freshness (`prepareTarget`'s order), each refusal named. -/
def genericChecks (deployment : DeclaredResourceController.Deployment)
    (directory : CellRegistry.Directory Nat DeclaredResourceController.Registry)
    (snapshot : DeclaredResourceController.AuthoritySnapshot) (target : Nat)
    (epoch : Option Nat) (before after : HostCell) : Except DispatchRefusal HostCell :=
  if CanonicalCellRegistry.FinalPostLaw deployment target before after then
    match CanonicalCellRegistry.loadPolicySource snapshot.domain directory
        (snapshot.authState.policyAddress ⟨target⟩ (snapshot.authState.policyRevision ⟨target⟩)) with
    | none => .error (ofReject 1 .policyUnavailable)
    | some source =>
      match ObjectAudience.checkFresh source.record.audience target epoch with
      | .error reason => .error (ofReject 1 (.audience reason))
      | .ok () => .ok after
  else .error (ofReject 1 .invalidPost)

/-- **THE RECEIVER FACTORIZATION.**  For a content target whose slot is present, the
deployed preparation (its post packed, its refusals named) is the dispatch, then the
generic checks. -/
def PrepareFactors (E : ContentSpec) : Prop :=
  ∀ (deployment : DeclaredResourceController.Deployment)
    (directory : CellRegistry.Directory Nat DeclaredResourceController.Registry)
    (ctx : LiveCtx) (command : ContentResource.Command) (version : Nat) (root : Digest)
    (observe : Option CapabilityId) (epoch : Option Nat)
    (roster : Option ObjectAudienceRoster.Roster) (before : HostCell),
    directory.slots ctx.target = .present before →
    ((DeclaredResourceController.prepareTarget deployment directory ctx.snapshot ctx.semantics
        ctx.ambient ctx.command (contentTarget ctx version root command observe epoch roster)).map
        (fun prepared => DeclaredResourceController.packTarget
          (contentTarget ctx version root command observe epoch roster) prepared.candidate.post)).mapError
        (ofReject 1) =
      (dispatch [(1, contentHandlerOf E)] 1 (ContentResource.commandStream.encode command)
          (hostCtxOf ctx deployment version root observe epoch roster) before) >>=
        genericChecks deployment directory ctx.snapshot ctx.target epoch before

/-- **THE LIVE LEGACY CENSUS** (false until the content constructor is deleted). -/
def HostLegacyCensus : Prop := LegacyDisjoint payloadTag [(1, contentHandler)]

/-- **Census teeth, today**: the content payload still carries code 1, so the census is
false until the migration deletes it. -/
def HostLegacyCensusRefutedToday : Prop := ¬ HostLegacyCensus

/-! ### The deployed payload decoder, read as a prefix (review gap 3, live).

`targetStream` reads a target's payload with `payloadStream.decodePrefix` and then continues
with the target's later fields.  `ContentPrefixAgreement` says that on content's code the
deployed decoder consumes exactly what the registry's prefix reader consumes and hands back
the same suffix, so routing the payload through the registry at the migration commit does
not move a single target's bytes.  Its teeth: the agreement is not a property of every code
(binding the content handler at the observe-only read's code 3 disagrees). -/

/-- The deployed payload decoder as a prefix reader: the tag octet, the payload's bytes after
it, the suffix. -/
def payloadPrefix : PrefixReader := fun bytes =>
  (DeclaredResourceController.payloadStream.decodePrefix bytes).map fun decoded =>
    (payloadTag decoded.1, (DeclaredResourceController.payloadStream.encode decoded.1).tail, decoded.2)

/-- **LIVE PREFIX AGREEMENT.**  On content's code, every byte string is read alike by the
deployed payload decoder and by the registry's prefix reader: refused alike, or the same
operation bytes and the same suffix. -/
def ContentPrefixAgreement : Prop :=
  ∀ rest, payloadPrefix (1 :: rest) = readPrefix [(1, contentHandler)] (1 :: rest)

/-- **Satisfiable.**  The agreement's accepting side is inhabited: a content command's
encoding after code 1, with any suffix, is read as that command's bytes and that suffix. -/
def ContentPrefixAccepts : Prop :=
  ∃ (command : ContentResource.Command) (suffix : List UInt8),
    payloadPrefix (1 :: (ContentResource.commandStream.encode command ++ suffix)) =
      some (1, ContentResource.commandStream.encode command, suffix)

/-- **Teeth.**  At the read's code (3), the deployed decoder accepts `[3]` (an observe-only
read, no bytes after its tag) while the content handler bound there refuses it. -/
def ContentPrefixTeeth : Prop :=
  payloadPrefix [3] ≠ readPrefix [(3, contentHandler)] [3]

end Minidregg.Effects.Revival
