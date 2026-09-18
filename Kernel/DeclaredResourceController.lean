/-
# Kernel.DeclaredResourceController -- source-bound ordinary resource invocation

The command transports the existing declared action syntax with the shared
compact codecs. It does not evaluate `Declaration.code` or use its historical
unary exhibit codec. The receiving path selects an actual declared resource,
the complete old authority domain, and that resource's current installed
policy. Its page mutation reuses `Page.applyWrites` and the existing checked
write semantics; no proposed post-state or policy view arrives on the wire.

Ordinary resource editing and replacing its governing policy are distinct
verbs. Account money belongs to the canonical Book family, never to a declared
metadata page. Every incidence authenticates its exact request against one old
authority snapshot and one command-derived operation marker.
-/
import Compiler.CredentialAuthorityDomainReceiver
import Compiler.CredentialAuthorityPolicyRegistry
import Compiler.CredentialAuthorityReplay
import Compiler.DeclaredEffectPageMaterializer
import Compiler.CanonicalRuntimeProfile
import Kernel.MultiCellHyperedge
import Kernel.ResourceBirthController

namespace Minidregg.Kernel.DeclaredResourceController

open Minidregg.Compiler
open Minidregg.Compiler.CanonicalPolicyAdmission
open Minidregg.Compiler.CredentialAuthorityDomain
open Minidregg.Compiler.CredentialAuthorityDomainReceiver
open Minidregg.Compiler.CredentialAuthorityPolicyRegistry
open Minidregg.Compiler.DeclaredEffectPageMaterializer
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Kernel.MultiCellHyperedge
open Minidregg.Kernel.DurableDataIntent
open Minidregg.Theory
open Minidregg.Theory.CellRegistry
open Minidregg.Theory.CellState
open Minidregg.Theory.DeclaredActionLowering
open Minidregg.Theory.IndexedProgram
open Minidregg.Theory.TypedAuthorization

set_option autoImplicit false

abbrev Registry := CanonicalCellRegistry.registry
abbrev Deployment := CanonicalCellRegistry.Deployment
abbrev Durable := DurableReceiverIO.Loaded ResourceBirthCodec.rootBytes
abbrev PageCell := Materialized DeclaredEffectPageMaterializer.materializer
abbrev AuthoritySnapshot := CredentialAuthorityDomain.Snapshot

/-! ## One compact transport for the existing action syntax -/

abbrev CreateWire := EffectDeclaration.StateKey × Int
abbrev WriteWire := EffectDeclaration.StateKey × Option Int × Int
abbrev MoveWire := ResourceId .account × ResourceId .account × Digest ×
  Option Int × Option Int × Int
abbrev ActionWire := Sum CreateWire (Sum WriteWire MoveWire)

def actionWireStream : StreamCodec ActionWire :=
  StreamCodec.sum
    (StreamCodec.product stateKeyStream intStream)
    (StreamCodec.sum
      (StreamCodec.product stateKeyStream
        (StreamCodec.product (StreamCodec.option intStream) intStream))
      (StreamCodec.product (TypedAuthorizationRequestCodec.resourceIdStream .account)
        (StreamCodec.product (TypedAuthorizationRequestCodec.resourceIdStream .account)
          (StreamCodec.product digestStream
            (StreamCodec.product (StreamCodec.option intStream)
              (StreamCodec.product (StreamCodec.option intStream) intStream))))))

def actionWire : Action → ActionWire
  | .create key initial => .inl (key, initial)
  | .write key expected replacement => .inr (.inl (key, expected, replacement))
  | .move source destination resource expectedSource expectedDestination amount =>
      .inr (.inr (source, destination, resource, expectedSource, expectedDestination, amount))

def actionOfWire : ActionWire → Action
  | .inl (key, initial) => .create key initial
  | .inr (.inl (key, expected, replacement)) => .write key expected replacement
  | .inr (.inr (source, destination, resource, expectedSource, expectedDestination, amount)) =>
      .move source destination resource expectedSource expectedDestination amount

@[simp] theorem actionOfWire_wire (action : Action) : actionOfWire (actionWire action) = action := by
  cases action <;> rfl

def actionStream : StreamCodec Action :=
  StreamCodec.xmap actionWireStream actionWire actionOfWire actionOfWire_wire

/-- The caller chooses an operation and expected versions, never its policy,
authority projection, proposed post, or independently supplied effect digest.
The native signing envelopes are separate proofs over source-derived requests.
`kind` and `target` are literal command coordinates, retained in its digest. -/
structure Command where
  kind : ResourceKind
  target : Nat
  subject : SubjectId
  capability : CapabilityId
  expectedAuthorityRoot : Digest
  schemaVersion : Nat
  expectedTargetRoot : Digest
  nonce : Nat
  actions : List Action
  deriving DecidableEq, Repr

abbrev CommandWire := ResourceKind × Nat × SubjectId × CapabilityId × Digest ×
  Nat × Digest × Nat × List Action

def commandWireStream : StreamCodec CommandWire :=
  StreamCodec.product ResourceBirthCodec.resourceKindStream
    (StreamCodec.product StreamCodec.nat
      (StreamCodec.product TypedAuthorizationRequestCodec.subjectIdStream
        (StreamCodec.product CredentialAuthorityEntryCodec.capabilityIdStream
          (StreamCodec.product digestStream
            (StreamCodec.product StreamCodec.nat
              (StreamCodec.product digestStream
                (StreamCodec.product StreamCodec.nat (StreamCodec.list actionStream))))))))

def Command.toWire (command : Command) : CommandWire :=
  (command.kind, command.target, command.subject, command.capability,
    command.expectedAuthorityRoot, command.schemaVersion, command.expectedTargetRoot,
    command.nonce, command.actions)

def Command.ofWire : CommandWire → Command
  | (kind, target, subject, capability, authorityRoot, version, targetRoot, nonce, actions) =>
      ⟨kind, target, subject, capability, authorityRoot, version, targetRoot, nonce, actions⟩

@[simp] theorem Command.ofWire_toWire (command : Command) :
    Command.ofWire command.toWire = command := by cases command; rfl

def commandStream : StreamCodec Command :=
  StreamCodec.xmap commandWireStream Command.toWire Command.ofWire Command.ofWire_toWire

def commandFrame : List UInt8 := "DREGG/RESOURCE/INVOKE".toUTF8.toList ++ [1]

def rawCommandCodec : LawfulCodec Command where
  encode command := commandFrame ++ commandStream.encode command
  decode bytes :=
    if bytes.take commandFrame.length = commandFrame then
      commandStream.toLawful.decode (bytes.drop commandFrame.length)
    else none
  decode_encode := by
    intro command
    have decoded := commandStream.toLawful.decode_encode command
    change commandStream.toLawful.decode (commandStream.encode command) = some command at decoded
    simp [decoded]

def commandCodec : LawfulCodec Command := ResourceBirthCodec.strictCodec rawCommandCodec

@[simp] theorem command_decode_encode (command : Command) :
    commandCodec.decode (commandCodec.encode command) = some command :=
  commandCodec.decode_encode command

theorem command_decode_canonical {bytes : List UInt8} {command : Command}
    (decoded : commandCodec.decode bytes = some command) :
    commandCodec.encode command = bytes :=
  ResourceBirthCodec.strictCodec_canonical rawCommandCodec decoded

def Command.declaration (command : Command) :
    DeclaredActionLowering.Declaration (⟨command.target⟩ : ResourceId command.kind) :=
  ⟨command.schemaVersion, command.expectedTargetRoot, command.nonce, command.actions⟩

/-- The full command is included in every incidence's source commitment.
Domain and receiver semantics are source-owned deployment coordinates. -/
def commandBytes (domain semantics : Digest) (command : Command) : List UInt8 :=
  (StreamCodec.product digestStream (StreamCodec.product digestStream bytesStream)).encode
    (domain, semantics, commandCodec.encode command)

def argsDigest (domain semantics : Digest) (command : Command) : Digest :=
  (Sp800185Cshake256.hash "DREGG.RESOURCE.INVOKE.ARGS/v1".toUTF8.toList
    (commandBytes domain semantics command)).digest

def effectsDigest (domain semantics : Digest) (command : Command) : Digest :=
  (Sp800185Cshake256.hash "DREGG.RESOURCE.INVOKE.EFFECT/v1".toUTF8.toList
    (commandBytes domain semantics command)).digest

def operationMarker (domain semantics : Digest) (command : Command) : Nat :=
  (Sp800185Cshake256.hash "DREGG.RESOURCE.INVOKE.NULLIFIER/v1".toUTF8.toList
    ((StreamCodec.product digestStream
      (StreamCodec.product digestStream
        (StreamCodec.product ResourceBirthCodec.resourceKindStream
          (StreamCodec.product StreamCodec.nat
            (StreamCodec.product TypedAuthorizationRequestCodec.subjectIdStream StreamCodec.nat))))).encode
      (domain, semantics, command.kind, command.target, command.subject, command.nonce))).digest.value

def ordinaryVerb : (kind : ResourceKind) → Verb kind
  | .object => .mutateObject
  | .account => .transfer
  | .program => .installProgram

/-- Trusted ambient inputs are not read from an incoming command. The shared
runtime compiler profile supplies `semantics`; no per-operation policy profile
is invented by this controller. The caller's height is the receiver clock. -/
structure Ambient where
  federation : FederationId
  height : Height

def request (snapshot : AuthoritySnapshot) (semantics : Digest) (ambient : Ambient)
    (command : Command) (preRoot : Digest) : Request command.kind where
  domain := snapshot.domain
  semantics := semantics
  federation := ambient.federation
  subject := command.subject
  subjectKeyEpoch := snapshot.authState.subjectKeyEpoch command.subject
  target := ⟨command.target⟩
  verb := ordinaryVerb command.kind
  argsDigest := argsDigest snapshot.domain semantics command
  effectsDigest := effectsDigest snapshot.domain semantics command
  nonce := command.nonce
  height := ambient.height
  preStateRoot := preRoot
  policyId := ⟨command.target⟩
  policyEpoch := snapshot.authState.policyEpoch ⟨command.target⟩
  cost := (commandCodec.encode command).length

theorem request_policy_is_target (snapshot : AuthoritySnapshot) (semantics : Digest)
    (ambient : Ambient) (command : Command) (preRoot : Digest) :
    (request snapshot semantics ambient command preRoot).policyId = ⟨command.target⟩ := rfl

theorem ordinary_program_verb_distinct : ordinaryVerb .program ≠ .installPolicy := by decide

/-! ## Source-owned page preparation, before portals or authorization -/

inductive Reject where
  | malformedCommand
  | unsupportedVersion
  | accountRequiresBook
  | emptyActions
  | wrongRole
  | missingTarget
  | invalidPage
  | staleTarget
  | staleAuthority
  | inadmissibleAction
  | pageMutation (reason : DeclaredEffectPageMaterializer.RejectReason)
  | pageValidation
  | invalidPost
  | authorityUnavailable
  | directoryUnavailable
  | nullifierUsed
  | authorityPreparation
  | physicalPreparation
  | policyUnavailable
  | signature (reason : CredentialSignatureAdmission.Reject)
  | capabilityRejected
  | policyRejected
  | conflictingIncidences
  deriving Repr

def requireSome {α : Type} (reason : Reject) : Option α → Except Reject α
  | none => .error reason
  | some value => .ok value

def packDeclared (kind : ResourceKind) (payload : PageCell) : PackedCell Registry :=
  match kind with
  | .object => ⟨.declaredObject, payload⟩
  | .account => ⟨.accountMetadata, payload⟩
  | .program => ⟨.declaredProgram, payload⟩

def pagePatch (pre : PageCell) (post : Page) :
    Patch DeclaredEffectPageMaterializer.schema Digest where
  expectedPreRoot := pre.root
  fieldFootprint := {()}
  resourceFootprint := ∅
  fieldWrites := [⟨(), some post⟩]
  resourceWrites := []

theorem pagePatch_apply (pre : PageCell) (post : Page)
    (validated : ValidatedPatch DeclaredEffectPageMaterializer.materializer pre
      (pagePatch pre post)) :
    validated.apply.logical = stateOfOption (some post) := by
  have page : pageAt validated.apply.logical = some post := by
    change (applyFieldWrites (pagePatch pre post).fieldWrites pre.logical.fields) () = some post
    simp [pagePatch, applyFieldWrites, FieldStore.assign]
    rfl
  exact (state_ext validated.apply.logical).trans (congrArg stateOfOption page)

/-- The guard relation is the existing sequential action semantics, with
exact sparse presence. It says nothing about an unrelated host proposal. -/
def CanonicalActionResult (pre : PageCell) (command : Command) (post : Page) : Prop :=
  ∃ before, pageAt pre.logical = some before ∧
    command.declaration.run before.toCanonicalState.fields = some post.toCanonicalState.fields

structure PageMode (deployment : Deployment) (pre : PageCell)
    (command : Command) (post : Page) where
  before : Page
  beforeExact : pageAt pre.logical = some before
  beforeLaw : CanonicalCellRegistry.DeclaredPageLaw deployment command.kind command.target before
  rootExact : command.expectedTargetRoot = pre.root
  versionExact : command.schemaVersion = 1
  ordinary : command.kind ≠ .account
  actionsPresent : command.actions ≠ []
  admitted : command.declaration.Admitted
  computed : before.applyWrites command.declaration.checkedWrites = .ok post
  postLaw : CanonicalCellRegistry.DeclaredPageLaw deployment command.kind command.target post
  semanticsExact :
    command.declaration.run before.toCanonicalState.fields = some post.toCanonicalState.fields

def pageFamily (deployment : Deployment) (snapshot : AuthoritySnapshot)
    (semantics : Digest) (ambient : Ambient) (pre : PageCell) :
    SemanticEffectFamily DeclaredEffectPageMaterializer.schema
      DeclaredEffectPageMaterializer.materializer Nat where
  Declaration := Command
  declarationCodec := commandCodec
  pre := pre
  request := fun command => ⟨command.kind, request snapshot semantics ambient command pre.root⟩
  Outcome := fun _ => Page
  outcomeCodec := fun _ => ResourceBirthCodec.strictCodec pageStream.toLawful
  ModeEvidence := fun command post => PageMode deployment pre command post
  Postcondition := fun command post logical =>
    logical = stateOfOption (some post) ∧ CanonicalActionResult pre command post ∧
      CanonicalCellRegistry.DeclaredPageLaw deployment command.kind command.target post
  effectDigest := effectsDigest snapshot.domain semantics
  patch := fun _ post => pagePatch pre post
  nullifier := fun _ _ => none
  Release := fun _ _ => Empty
  DeclassificationAuthority := fun _ _ => Empty
  ReleaseAuthorization := fun _ _ _ => Empty
  DisclosureAllowed := fun _ _ decision => decision = .sealed

/-- Computation precedes policy admission. The retained candidate has no
authorization token; a requester cannot construct it by supplying a post. -/
structure PreparedPage (deployment : Deployment) (snapshot : AuthoritySnapshot)
    (semantics : Digest) (ambient : Ambient) (pre : PageCell) (command : Command) where
  private mk ::
  post : Page
  candidate : PolicyInstall.Candidate (pageFamily deployment snapshot semantics ambient pre)
    pre command post

def preparePage (deployment : Deployment) (snapshot : AuthoritySnapshot)
    (semantics : Digest) (ambient : Ambient) (pre : PageCell) (command : Command) :
    Except Reject (PreparedPage deployment snapshot semantics ambient pre command) := do
  if ordinary : command.kind ≠ .account then
    if version : command.schemaVersion = 1 then
      if nonempty : command.actions ≠ [] then
        if root : command.expectedTargetRoot = pre.root then
          match present : pageAt pre.logical with
          | none => .error .invalidPage
          | some before =>
              if preLaw : CanonicalCellRegistry.DeclaredPageLaw deployment
                  command.kind command.target before then
                if admitted : command.declaration.admissionCheck = true then
                  match computed : before.applyWrites command.declaration.checkedWrites with
                  | .error reason => .error (.pageMutation reason)
                  | .ok post =>
                      if postLaw : CanonicalCellRegistry.DeclaredPageLaw deployment
                          command.kind command.target post then
                        match validate DeclaredEffectPageMaterializer.materializer pre (pagePatch pre post) with
                        | .rejected _ => .error .pageValidation
                        | .accepted validated =>
                            let semantic : command.declaration.run before.toCanonicalState.fields =
                                some post.toCanonicalState.fields := by
                              simpa [Declaration.run, admitted] using
                                Page.applyWrites_checked computed
                            .ok ⟨post,
                              { preStateBound := rfl
                                modeEvidence :=
                                  ⟨before, present, preLaw, root, version, ordinary,
                                    nonempty, admitted, computed, postLaw, semantic⟩
                                validated := validated
                                postcondition :=
                                  ⟨pagePatch_apply pre post validated,
                                    ⟨before, present, semantic⟩, postLaw⟩ }⟩
                      else .error .invalidPost
                else .error .inadmissibleAction
              else .error .wrongRole
        else .error .staleTarget
      else .error .emptyActions
    else .error .unsupportedVersion
  else .error .accountRequiresBook

theorem PreparedPage.action_semantics_exact {deployment : Deployment}
    {snapshot : AuthoritySnapshot} {semantics : Digest} {ambient : Ambient}
    {pre : PageCell} {command : Command}
    (prepared : PreparedPage deployment snapshot semantics ambient pre command) :
    CanonicalActionResult pre command prepared.post :=
  prepared.candidate.postcondition.2.1

/-! ## One old physical snapshot and its command-derived marker update -/

structure ObservedTarget (deployment : Deployment) (directory : Directory Nat Registry)
    (command : Command) where
  private mk ::
  before : PackedCell Registry
  present : directory.slots command.target = .present before
  pre : PageCell
  selected : CanonicalCellRegistry.selectDeclared deployment command.target command.kind before = some pre

def observeTarget (deployment : Deployment) (directory : Directory Nat Registry)
    (command : Command) : Option (ObservedTarget deployment directory command) :=
  match present : directory.slots command.target with
  | .absent => none
  | .present before =>
      match selected : CanonicalCellRegistry.selectDeclared deployment command.target command.kind before with
      | none => none
      | some pre => some ⟨before, present, pre, selected⟩

def markerEdits (snapshot : AuthoritySnapshot) (semantics : Digest) (command : Command) :
    List CredentialAuthorityDomain.Edit :=
  [CredentialAuthorityDomain.nullifierEdit snapshot (operationMarker snapshot.domain semantics command)]

def markerPatch (snapshot : AuthoritySnapshot) (semantics : Digest) (command : Command) :
    Patch CredentialAuthorityState.schema.{0, 0} Digest :=
  CredentialAuthorityDomain.editPatch snapshot (markerEdits snapshot semantics command)

structure MarkerMode (snapshot : AuthoritySnapshot) (semantics : Digest) (command : Command) where
  rootExact : command.expectedAuthorityRoot = snapshot.cell.root
  unused : CredentialAuthorityState.isNullified snapshot.cell
    (operationMarker snapshot.domain semantics command) = false
  prepared : CredentialAuthorityDomain.Prepared snapshot (markerEdits snapshot semantics command)

def markerFamily (snapshot : AuthoritySnapshot) (semantics : Digest) (ambient : Ambient) :
    SemanticEffectFamily CredentialAuthorityState.schema.{0, 0}
      CredentialAuthorityStateCodec.materializer Nat where
  Declaration := Command
  declarationCodec := commandCodec
  pre := snapshot.cell
  request := fun command =>
    ⟨command.kind, request snapshot semantics ambient command snapshot.cell.root⟩
  Outcome := fun _ => Unit
  outcomeCodec := fun _ => DeclaredActionLowering.unitCodec
  ModeEvidence := fun command _ => MarkerMode snapshot semantics command
  Postcondition := fun command _ logical =>
    (markerPatch snapshot semantics command).ResultAt snapshot.logical logical
  effectDigest := effectsDigest snapshot.domain semantics
  patch := fun command _ => markerPatch snapshot semantics command
  nullifier := fun command _ => some (operationMarker snapshot.domain semantics command)
  Release := fun _ _ => Empty
  DeclassificationAuthority := fun _ _ => Empty
  ReleaseAuthorization := fun _ _ _ => Empty
  DisclosureAllowed := fun _ _ decision => decision = .sealed

def prepareMarker (snapshot : AuthoritySnapshot) (semantics : Digest) (command : Command) :
    Except Reject (MarkerMode snapshot semantics command) :=
  if root : command.expectedAuthorityRoot = snapshot.cell.root then
    if unused : CredentialAuthorityState.isNullified snapshot.cell
        (operationMarker snapshot.domain semantics command) = false then
      match CredentialAuthorityDomain.prepare snapshot (markerEdits snapshot semantics command) with
      | none => .error .authorityPreparation
      | some prepared => .ok ⟨root, unused, prepared⟩
    else .error .nullifierUsed
  else .error .staleAuthority

def sourceStore (domain : Digest) (directory : Directory Nat Registry) :
    CanonicalPolicyRegistry.PayloadStore where
  fetch := CanonicalCellRegistry.fetchPolicySource domain directory

/-- Every dependency comes from the same durable image. The physical lowering
retains the old catalogue/shard guards and allocates only the marker's new
internal shards, using the complete permanently-used identity directory. -/
structure PreparedInvocation {F : Type} [Field F]
    (deployment : Deployment) (profile : CanonicalRuntimeProfile.Profile F)
    (ambient : Ambient) (durable : Durable) (command : Command) where
  private mk ::
  directory : LoadedDirectory durable
  authority : Loaded deployment.authorityAnchor durable.snapshot
  target : ObservedTarget deployment directory.directory command
  page : PreparedPage deployment authority.snapshot profile.semantics ambient target.pre command
  marker : MarkerMode authority.snapshot profile.semantics command
  physical : Lowered directory authority (markerEdits authority.snapshot profile.semantics command)
    marker.prepared []
  source : CanonicalCellRegistry.LoadedPolicySource authority.snapshot.domain directory.directory
    (authority.snapshot.authState.policyAddress ⟨command.target⟩
      (authority.snapshot.authState.policyEpoch ⟨command.target⟩))
  postLaw : CanonicalCellRegistry.FinalPostLaw deployment command.target target.before
    (packDeclared command.kind page.candidate.post)

def prepare {F : Type} [Field F] (deployment : Deployment)
    (profile : CanonicalRuntimeProfile.Profile F) (ambient : Ambient)
    (durable : Durable) (command : Command) :
    Except Reject (PreparedInvocation deployment profile ambient durable command) := do
  let directory ← requireSome .directoryUnavailable (loadDirectory durable)
  let authority ← requireSome .authorityUnavailable (loadDeployment deployment durable.snapshot)
  let target ← requireSome .missingTarget (observeTarget deployment directory.directory command)
  let page ← preparePage deployment authority.snapshot profile.semantics ambient target.pre command
  let marker ← prepareMarker authority.snapshot profile.semantics command
  let physical ← requireSome .physicalPreparation (lower directory authority marker.prepared [])
  let address := authority.snapshot.authState.policyAddress ⟨command.target⟩
    (authority.snapshot.authState.policyEpoch ⟨command.target⟩)
  let source ← requireSome .policyUnavailable
    (CanonicalCellRegistry.loadPolicySource authority.snapshot.domain directory.directory address)
  if postLaw : CanonicalCellRegistry.FinalPostLaw deployment command.target target.before
      (packDeclared command.kind page.candidate.post) then
    .ok ⟨directory, authority, target, page, marker, physical, source, postLaw⟩
  else .error .invalidPost

/-! ## The raw joint tuple is the one policy later evaluates and accepts -/

inductive Incidence where
  | target
  | authority
  deriving DecidableEq, Fintype

abbrev Source (command : Command) := { actual : Command // actual = command }

variable {F : Type} [Field F] {deployment : Deployment}
  {profile : CanonicalRuntimeProfile.Profile F} {ambient : Ambient}
  {durable : Durable} {command : Command}

def layout (prepared : PreparedInvocation deployment profile ambient durable command) :
    CellLayout Incidence where
  schema
    | .target => DeclaredEffectPageMaterializer.schema
    | .authority => CredentialAuthorityState.schema.{0, 0}
  fieldDecidableEq incidence := by cases incidence <;> dsimp <;> infer_instance
  resourceDecidableEq incidence := by cases incidence <;> dsimp <;> infer_instance
  materializer
    | .target => DeclaredEffectPageMaterializer.materializer
    | .authority => CredentialAuthorityStateCodec.materializer
  projectAuthority := fun _ _ => prepared.authority.snapshot.authState
  cellId
    | .target => ⟨command.target⟩
    | .authority => deployment.authorityAnchor.catalogueCellId

local instance fieldEq (prepared : PreparedInvocation deployment profile ambient durable command)
    (incidence : Incidence) : DecidableEq ((layout prepared).schema incidence).Field :=
  (layout prepared).fieldDecidableEq incidence

local instance resourceEq (prepared : PreparedInvocation deployment profile ambient durable command)
    (incidence : Incidence) : DecidableEq ((layout prepared).schema incidence).Resource :=
  (layout prepared).resourceDecidableEq incidence

def rawLeg (prepared : PreparedInvocation deployment profile ambient durable command)
    (source : Source command) : (incidence : Incidence) → CandidateLegData (layout prepared) incidence
  | .target =>
      { pre := prepared.target.pre
        patch := pagePatch prepared.target.pre prepared.page.post
        request := ⟨source.val.kind, request prepared.authority.snapshot profile.semantics
          ambient source.val prepared.target.pre.root⟩
        Postcondition := fun logical =>
          logical = stateOfOption (some prepared.page.post) ∧
            CanonicalActionResult prepared.target.pre source.val prepared.page.post ∧
            CanonicalCellRegistry.DeclaredPageLaw deployment source.val.kind source.val.target prepared.page.post }
  | .authority =>
      { pre := prepared.authority.snapshot.cell
        patch := markerPatch prepared.authority.snapshot profile.semantics source.val
        request := ⟨source.val.kind, request prepared.authority.snapshot profile.semantics
          ambient source.val prepared.authority.snapshot.cell.root⟩
        Postcondition := fun logical =>
          (markerPatch prepared.authority.snapshot profile.semantics source.val).ResultAt
            prepared.authority.snapshot.logical logical }

def bindFamily (prepared : PreparedInvocation deployment profile ambient durable command)
    (source : Source command) (_portals : Incidence → Portal) :
    (incidence : Incidence) → SemanticLegBinding (rawLeg prepared source incidence)
  | .target =>
      { Nullifier := Nat
        family := pageFamily deployment prepared.authority.snapshot profile.semantics ambient prepared.target.pre
        declaration := source.val
        outcome := prepared.page.post
        preExact := rfl, requestExact := rfl, effectsExact := rfl, patchExact := rfl
        postconditionExact := fun _ => Iff.rfl }
  | .authority =>
      { Nullifier := Nat
        family := markerFamily prepared.authority.snapshot profile.semantics ambient
        declaration := source.val
        outcome := ()
        preExact := rfl, requestExact := rfl, effectsExact := rfl, patchExact := rfl
        postconditionExact := fun _ => Iff.rfl }

def plan (prepared : PreparedInvocation deployment profile ambient durable command) :
    PreparationPlan (layout prepared) (Source command) where
  leg := rawLeg prepared
  jointDigest := fun source => effectsDigest prepared.authority.snapshot.domain profile.semantics source.val
  legEffectsDigest := fun source _ =>
    effectsDigest prepared.authority.snapshot.domain profile.semantics source.val
  bindFamily := bindFamily prepared

def validated (prepared : PreparedInvocation deployment profile ambient durable command) :
    (incidence : Incidence) → ValidatedPatch ((layout prepared).materializer incidence)
      (rawLeg prepared ⟨command, rfl⟩ incidence).pre
      (rawLeg prepared ⟨command, rfl⟩ incidence).patch
  | .target => prepared.page.candidate.validated
  | .authority => prepared.marker.prepared.validated

theorem postconditions (prepared : PreparedInvocation deployment profile ambient durable command) :
    ∀ incidence, (rawLeg prepared ⟨command, rfl⟩ incidence).Postcondition
      (validated prepared incidence).apply.logical := by
  intro incidence
  cases incidence with
  | target => exact prepared.page.candidate.postcondition
  | authority => exact prepared.marker.prepared.validated.resultAt

def prepareTuple (prepared : PreparedInvocation deployment profile ambient durable command) :
    Option (PreparedTuple (plan prepared)) :=
  if distinct : Function.Injective (layout prepared).cellId then
    some
      { source := ⟨command, rfl⟩
        primary := .target
        validated := validated prepared
        postconditions := postconditions prepared
        cellIdsDistinct := distinct
        requestRoots := by intro incidence; cases incidence <;> rfl
        requestEffects := by intro incidence; cases incidence <;> rfl }
  else none

def bytesSlots (stem : String) : Nat → List UInt8 → List (String × Int)
  | _, [] => []
  | offset, byte :: rest =>
      (s!"{stem}/{offset}", Int.ofNat byte.toNat) :: bytesSlots stem (offset + 1) rest

/-- Source-owned request labels and exact canonical cell bytes cover both
incidences. A policy cannot evaluate a host-selected post beside another patch.
Presence/zero distinctions are retained by the native cell codecs. -/
def project (prepared : PreparedInvocation deployment profile ambient durable command)
    (source : Source command)
    (logical : (incidence : Incidence) → LogicalState ((layout prepared).schema incidence)) :
    Minidregg.Pred.State :=
  ⟨CanonicalRuntimeProfile.requestSlots
      (request prepared.authority.snapshot profile.semantics ambient source.val prepared.target.pre.root) ++
    bytesSlots "command/bytes" 0 (commandCodec.encode source.val) ++
    bytesSlots "resource/bytes" 0
      (DeclaredEffectPageMaterializer.materializer.codec.encode (logical .target)) ++
    bytesSlots "authority/bytes" 0
      (CredentialAuthorityStateCodec.materializer.codec.encode (logical .authority))⟩

def step (prepared : PreparedInvocation deployment profile ambient durable command)
    (tuple : PreparedTuple (plan prepared)) (incidence : Incidence) : PolicyStepContext :=
  PolicyStepContext.ofPreparedTuple (project prepared) profile.semantics
    { tuple with primary := incidence }

def policyConfig [DecidableEq F]
    (prepared : PreparedInvocation deployment profile ambient durable command)
    (tuple : PreparedTuple (plan prepared)) (incidence : Incidence) : CanonicalPolicyConfig F :=
  CredentialAuthorityPolicyRegistry.config profile.compilerProfile prepared.authority.snapshot
    (sourceStore prepared.authority.snapshot.domain prepared.directory.directory)
    (sourceCapabilityPortal prepared.authority.snapshot
      (operationMarker prepared.authority.snapshot.domain profile.semantics command))
    (step prepared tuple incidence)

def portals [DecidableEq F]
    (prepared : PreparedInvocation deployment profile ambient durable command)
    (tuple : PreparedTuple (plan prepared)) : Incidence → Portal :=
  fun incidence => (policyConfig prepared tuple incidence).portal

theorem source_request_epoch_current
    (prepared : PreparedInvocation deployment profile ambient durable command)
    (tuple : PreparedTuple (plan prepared)) (incidence : Incidence) :
    (tuple.request incidence).2.policyEpoch =
      prepared.authority.snapshot.authState.policyEpoch (tuple.request incidence).2.policyId := by
  cases incidence <;> rfl

def authorizeLeg [DecidableEq F]
    (prepared : PreparedInvocation deployment profile ambient durable command)
    (tuple : PreparedTuple (plan prepared)) (incidence : Incidence)
    (signature : CredentialSignatureAdmission.CheckedSignature prepared.authority.snapshot) :
    Except Reject (Authorized (portals prepared tuple incidence)
      prepared.authority.snapshot.authState (tuple.request incidence).2) := do
  let wanted := (tuple.request incidence).2
  let config := policyConfig prepared tuple incidence
  let evidence ← requireSome .capabilityRejected (sourceCapabilityOnlyEvidence profile.compilerProfile prepared.authority.snapshot
    (sourceStore prepared.authority.snapshot.domain prepared.directory.directory)
    (operationMarker prepared.authority.snapshot.domain profile.semantics command)
    (step prepared tuple incidence) wanted command.capability signature)
  let committed ← requireSome .policyUnavailable (config.registry.resolve wanted.policyId wanted.policyEpoch)
  let witness := canonicalWitness profile.compilerProfile.compiler committed
    (step prepared tuple incidence).oldState (step prepared tuple incidence).newState
  requireSome .policyRejected (CanonicalPolicyAdmission.admit config prepared.authority.snapshot.authState wanted evidence witness
    (.policy wanted.policyId wanted.policyEpoch)
    (source_request_epoch_current prepared tuple incidence))

/-- Exact per-incidence envelopes share a command marker; neither can be
retargeted to the other's root or replaced by an unrelated valid signer. -/
structure SignedCommand where
  commandBytes : List UInt8
  targetEnvelope : List UInt8
  authorityEnvelope : List UInt8

def SignedCommand.envelope (signed : SignedCommand) : Incidence → List UInt8
  | .target => signed.targetEnvelope
  | .authority => signed.authorityEnvelope

-- Retain this already-constructed portal as the indexed witness type. Expanding
-- it while elaborating dependent records unnecessarily normalizes the shared
-- semantic cSHAKE commitment; the executable source gate is unchanged.
attribute [irreducible] portals

/-- The admitted leg retains the actual private native receipt and its exact
input wire, together with the literal result of source capability/policy
admission. Journaled signatures cannot be replaced after this check. -/
structure CheckedLeg [DecidableEq F]
    (prepared : PreparedInvocation deployment profile ambient durable command)
    (tuple : PreparedTuple (plan prepared)) (incidence : Incidence) (envelope : List UInt8) where
  receipt : CredentialSignatureAdmission.CheckedSignature prepared.authority.snapshot
  envelopeExact : receipt.envelopeBytes = envelope
  authorization : Authorized (portals prepared tuple incidence)
    prepared.authority.snapshot.authState (tuple.request incidence).2
  authorized : authorizeLeg prepared tuple incidence receipt = .ok authorization

def verifyAndAuthorizeLeg [DecidableEq F]
    (native : CredentialSignatureIO.NativeConfig)
    (prepared : PreparedInvocation deployment profile ambient durable command)
    (tuple : PreparedTuple (plan prepared)) (incidence : Incidence) (envelope : List UInt8) :
    IO (Except Reject (CheckedLeg prepared tuple incidence envelope)) := do
  match ← CredentialSignatureAdmission.verifyNative native prepared.authority.snapshot
      (operationMarker prepared.authority.snapshot.domain profile.semantics command)
      (tuple.request incidence).2 envelope with
  | .error reason => return .error (.signature reason)
  | .ok signature =>
      if exactWire : signature.envelopeBytes = envelope then
        match admitted : authorizeLeg prepared tuple incidence signature with
        | .error reason => return .error reason
        | .ok authorization => return .ok ⟨signature, exactWire, authorization, admitted⟩
      else return .error (.signature .sourceBinding)

theorem tuple_source_exact
    (prepared : PreparedInvocation deployment profile ambient durable command)
    (tuple : PreparedTuple (plan prepared)) : tuple.source = ⟨command, rfl⟩ :=
  Subtype.ext tuple.source.property

theorem tuple_post_exact
    (prepared : PreparedInvocation deployment profile ambient durable command)
    (tuple : PreparedTuple (plan prepared)) (incidence : Incidence) :
    tuple.post incidence = (validated prepared incidence).apply := by
  apply Materialized.ext
  simp only [PreparedTuple.post, ValidatedPatch.apply]
  rw [tuple_source_exact prepared tuple]
  rfl

def admissionEvidence [DecidableEq F]
    (prepared : PreparedInvocation deployment profile ambient durable command)
    (tuple : PreparedTuple (plan prepared))
    (authorizations : ∀ incidence, Authorized (portals prepared tuple incidence)
      prepared.authority.snapshot.authState (tuple.request incidence).2) :
    tuple.AdmissionEvidence (portals prepared tuple) where
  modes incidence := by
    cases incidence with
    | target =>
        change PageMode deployment prepared.target.pre tuple.source.val prepared.page.post
        rw [tuple.source.property]
        exact prepared.page.candidate.modeEvidence
    | authority =>
        change MarkerMode prepared.authority.snapshot profile.semantics tuple.source.val
        rw [tuple.source.property]
        exact prepared.marker
  authorizations := authorizations
  disclosure := fun _ => .sealed
  disclosureAllowed incidence := by cases incidence <;> rfl

/-- No decoder or public constructor produces an accepted invocation. Both
native exact-request capabilities and both old-policy evaluations must pass.
This is semantic admission; physical publication still requires durable CAS. -/
structure AcceptedInvocation [DecidableEq F]
    (prepared : PreparedInvocation deployment profile ambient durable command) (signed : SignedCommand) where
  private mk ::
  ingressExact : commandCodec.encode command = signed.commandBytes
  tuple : PreparedTuple (plan prepared)
  target : CheckedLeg prepared tuple .target signed.targetEnvelope
  authority : CheckedLeg prepared tuple .authority signed.authorityEnvelope

def AcceptedInvocation.evidence [DecidableEq F]
    {prepared : PreparedInvocation deployment profile ambient durable command} {signed : SignedCommand}
    (accepted : AcceptedInvocation prepared signed) :
    accepted.tuple.AdmissionEvidence (portals prepared accepted.tuple) :=
  admissionEvidence prepared accepted.tuple fun incidence =>
    match incidence with
    | .target => accepted.target.authorization
    | .authority => accepted.authority.authorization

theorem AcceptedInvocation.native_ingress_exact [DecidableEq F]
    {prepared : PreparedInvocation deployment profile ambient durable command} {signed : SignedCommand}
    (accepted : AcceptedInvocation prepared signed) :
    accepted.target.receipt.envelopeBytes = signed.targetEnvelope ∧
      accepted.authority.receipt.envelopeBytes = signed.authorityEnvelope :=
  ⟨accepted.target.envelopeExact, accepted.authority.envelopeExact⟩

def admit [DecidableEq F] (native : CredentialSignatureIO.NativeConfig)
    (prepared : PreparedInvocation deployment profile ambient durable command) (signed : SignedCommand) :
    IO (Except Reject (AcceptedInvocation prepared signed)) := do
  if ingress : commandCodec.encode command = signed.commandBytes then
    match prepareTuple prepared with
    | none => return .error .conflictingIncidences
    | some tuple =>
        match ← verifyAndAuthorizeLeg native prepared tuple .target signed.targetEnvelope with
        | .error reason => return .error reason
        | .ok target =>
            match ← verifyAndAuthorizeLeg native prepared tuple .authority signed.authorityEnvelope with
            | .error reason => return .error reason
            | .ok authority =>
                return .ok ⟨ingress, tuple, target, authority⟩
  else return .error .malformedCommand

def AcceptedInvocation.apex [DecidableEq F]
    {prepared : PreparedInvocation deployment profile ambient durable command} {signed : SignedCommand}
    (_accepted : AcceptedInvocation prepared signed) : Digest :=
  effectsDigest prepared.authority.snapshot.domain profile.semantics command

def AcceptedInvocation.declaration [DecidableEq F]
    {prepared : PreparedInvocation deployment profile ambient durable command} {signed : SignedCommand}
    (accepted : AcceptedInvocation prepared signed) :=
  accepted.tuple.toDeclaration (portals prepared accepted.tuple) accepted.apex

def AcceptedInvocation.legs [DecidableEq F]
    {prepared : PreparedInvocation deployment profile ambient durable command} {signed : SignedCommand}
    (accepted : AcceptedInvocation prepared signed) : accepted.declaration.AcceptedLegs :=
  accepted.tuple.accept (portals prepared accepted.tuple) accepted.apex accepted.evidence

theorem AcceptedInvocation.post_exact [DecidableEq F]
    {prepared : PreparedInvocation deployment profile ambient durable command} {signed : SignedCommand}
    (accepted : AcceptedInvocation prepared signed) (incidence : Incidence) :
    accepted.declaration.post accepted.legs incidence = (validated prepared incidence).apply :=
  (accepted.tuple.accepted_posts_exact (portals prepared accepted.tuple)
    accepted.apex accepted.evidence incidence).trans
      (tuple_post_exact prepared accepted.tuple incidence)

theorem AcceptedInvocation.authority_post_exact [DecidableEq F]
    {prepared : PreparedInvocation deployment profile ambient durable command} {signed : SignedCommand}
    (accepted : AcceptedInvocation prepared signed) :
    accepted.declaration.post accepted.legs .authority = prepared.physical.post.cell := by
  rw [accepted.post_exact .authority]
  apply Materialized.ext
  exact prepared.physical.projection_exact.symm

theorem AcceptedInvocation.policy_view_exact [DecidableEq F]
    {prepared : PreparedInvocation deployment profile ambient durable command} {signed : SignedCommand}
    (accepted : AcceptedInvocation prepared signed) :
    project prepared accepted.tuple.source
        (fun incidence => (accepted.declaration.post accepted.legs incidence).logical) =
      project prepared accepted.tuple.source accepted.tuple.logicalPost := by
  congr 1
  funext incidence
  exact congrArg Materialized.logical
    (accepted.tuple.accepted_posts_exact (portals prepared accepted.tuple)
      accepted.apex accepted.evidence incidence)

/-! ## Exact physical posts, complete read guards, and stable replay -/

def targetWrite (prepared : PreparedInvocation deployment profile ambient durable command) : DataWrite :=
  ResourceBirthController.Concrete.packedWrite command.target prepared.target.before
    (packDeclared command.kind prepared.page.candidate.post)

def writes (prepared : PreparedInvocation deployment profile ambient durable command) : List DataWrite :=
  targetWrite prepared :: prepared.physical.writes ++
    prepared.physical.placement.auxiliaryCreates.map ResourceBirthController.birthWrite

def sourceGuard (prepared : PreparedInvocation deployment profile ambient durable command) : ReadGuard :=
  ⟨⟨prepared.source.readGuard.1⟩, prepared.source.readGuard.2⟩

def readGuards (prepared : PreparedInvocation deployment profile ambient durable command) : List ReadGuard :=
  sourceGuard prepared :: readonlyGuards prepared.authority.readGuards (writes prepared)

def PhysicalShape (prepared : PreparedInvocation deployment profile ambient durable command) : Prop :=
  ((writes prepared).map DataWrite.cellId).Nodup ∧
    (∀ write ∈ writes prepared, write.expectedPre = durable.snapshot.model.roots write.cellId) ∧
    (∀ write ∈ writes prepared,
      ResourceBirthController.Concrete.PhysicalPostLaw deployment write) ∧
    (sourceGuard prepared).cellId ∉ (writes prepared).map DataWrite.cellId ∧
    (∀ guard ∈ readGuards prepared, guard.expectedRoot = durable.snapshot.model.roots guard.cellId)

instance physicalShapeDecidable
    (prepared : PreparedInvocation deployment profile ambient durable command) :
    Decidable (PhysicalShape prepared) := by
  unfold PhysicalShape
  infer_instance

theorem writes_roots_bound
    (prepared : PreparedInvocation deployment profile ambient durable command) :
    ∀ write ∈ writes prepared, ResourceBirthCodec.rootBytes write.canonicalPostBytes = write.exactPost := by
  intro write member
  rcases List.mem_cons.mp member with rfl | other
  · rfl
  · rcases List.mem_append.mp other with authority | allocation
    · exact CredentialAuthorityDomainReceiver.planWrites_roots_bound
        deployment.authorityAnchor durable.snapshot prepared.authority.snapshot.catalogue
        prepared.marker.prepared.postPages prepared.physical.placement write authority
    · obtain ⟨creation, _, rfl⟩ := List.mem_map.mp allocation
      exact ResourceBirthController.birthWrite_root_bound creation

theorem readGuards_readonly
    (prepared : PreparedInvocation deployment profile ambient durable command)
    (shape : PhysicalShape prepared) :
    ∀ guard ∈ readGuards prepared, guard.cellId ∉ (writes prepared).map DataWrite.cellId := by
  intro guard member
  rcases List.mem_cons.mp member with rfl | authority
  · exact shape.2.2.2.1
  · exact of_decide_eq_true (List.mem_filter.mp authority).2

def signedBytes (domain semantics : Digest) (signed : SignedCommand) : List UInt8 :=
  "DREGG/RESOURCE/SIGNED-INGRESS".toUTF8.toList ++ [1] ++
    (StreamCodec.product digestStream
      (StreamCodec.product digestStream
        (StreamCodec.product bytesStream (StreamCodec.product bytesStream bytesStream)))).encode
      (domain, semantics, signed.commandBytes, signed.targetEnvelope, signed.authorityEnvelope)

abbrev invocationNullifier := CredentialAuthorityReplay.nullifier

def invocationEvent (domain semantics : Digest) (command : Command) (signed : SignedCommand) : StableEvent where
  codecVersion := 1
  domain := domain
  eventId := effectsDigest domain semantics command
  canonicalBytes := signedBytes domain semantics signed

def transactionId (domain semantics : Digest) (command : Command) : Digest :=
  ⟨operationMarker domain semantics command⟩

/-- Admission units, computed from the actual complete physical plan. No
monetary fee is invented for these ordinary metadata/code mutations. -/
def sourceCharge (prepared : PreparedInvocation deployment profile ambient durable command)
    (signed : SignedCommand) : ResourceCost.Charge
  | .incidences => 2
  | .turnBytes => (signedBytes prepared.authority.snapshot.domain profile.semantics signed).length
  | .memoryTouches => (writes prepared).length + (readGuards prepared).length
  | .storageBytes => ((writes prepared).map fun write => write.canonicalPostBytes.length).sum
  | .feeDebit | .witnessBytes | .proofWork | .networkBytes | .sideEffectCount | .leaseByteBlocks => 0

/-- The emitter requires the complete privately constructed semantic admission
and the actual physical refinement checks. It does not forge handler evidence
or claim that a candidate intent is already a physically committed hyperedge. -/
def AcceptedInvocation.dataIntent [DecidableEq F]
    {prepared : PreparedInvocation deployment profile ambient durable command} {signed : SignedCommand}
    (_accepted : AcceptedInvocation prepared signed) (shape : PhysicalShape prepared) :
    DataIntent ResourceBirthCodec.rootBytes where
  transactionId := transactionId prepared.authority.snapshot.domain profile.semantics command
  writes := writes prepared
  readGuards := readGuards prepared
  nullifiers := [invocationNullifier prepared.authority.snapshot.domain
    (operationMarker prepared.authority.snapshot.domain profile.semantics command)]
  exactCharge := sourceCharge prepared signed
  event := invocationEvent prepared.authority.snapshot.domain profile.semantics command signed
  postRootsBound := writes_roots_bound prepared
  guardsReadOnly := readGuards_readonly prepared shape

/-- Journal lookup is exact full signed ingress, never a spent-marker success
shortcut. The returned record is the prior complete receipt, not fresh authority.
The durable image has already replayed through the shared canonical executor. -/
def recordedInvocation (domain semantics : Digest) (command : Command) (signed : SignedCommand)
    (durable : Durable) : Except Unit (Option (DurableCommitProtocol.Intent Digest Digest
      StableNullifier ReplayEnvelope)) :=
  match DurableCommitProtocol.Snapshot.lookupRecorded (transactionId domain semantics command)
      durable.snapshot.model.journal with
  | none => .ok none
  | some recorded =>
      if recorded.transactionId = transactionId domain semantics command ∧
          recorded.event.event = invocationEvent domain semantics command signed ∧
          recorded.nullifiers = [invocationNullifier domain (operationMarker domain semantics command)] then
        .ok (some recorded)
      else .error ()

inductive ReceiveResult where
  | replayed (recorded : DurableCommitProtocol.Intent Digest Digest StableNullifier ReplayEnvelope)
  | rejected (reason : Reject)
  | transactionConflict
  | unavailable (detail : String)
  | settlement (result : DurableReceiverIO.Result ResourceBirthCodec.rootBytes)

/-- The only outer invocation receiver: bytes and exact signatures in; either
refusal, the previously recorded exact result, or shared durable publication
outcome out. All preparation is after replay lookup and before the only CAS.
No new authority, resource mutation or input consumption occurs on refusal. -/
def receive {F : Type} [Field F] [DecidableEq F]
    (deployment : Deployment) (profile : CanonicalRuntimeProfile.Profile F)
    (ambient : Ambient) (native : CredentialSignatureIO.NativeConfig)
    (transport : DurableReceiverIO.Transport) (signed : SignedCommand) (attempts : Nat := 3) :
    IO ReceiveResult := do
  match commandCodec.decode signed.commandBytes with
  | none => return .rejected .malformedCommand
  | some command =>
      match ← DurableReceiverIO.load transport ResourceBirthCodec.rootBytes with
      | .error detail => return .unavailable detail
      | .ok durable =>
          match recordedInvocation deployment.domain profile.semantics command signed durable with
          | .error _ => return .transactionConflict
          | .ok (some recorded) => return .replayed recorded
          | .ok none =>
              match prepare deployment profile ambient durable command with
              | .error reason => return .rejected reason
              | .ok prepared =>
                  if shape : PhysicalShape prepared then
                    match ← admit native prepared signed with
                    | .error reason => return .rejected reason
                    | .ok accepted =>
                        return .settlement (← DurableReceiverIO.receive transport ResourceBirthCodec.rootBytes
                          (accepted.dataIntent shape) attempts)
                  else return .rejected .physicalPreparation

end Minidregg.Kernel.DeclaredResourceController
