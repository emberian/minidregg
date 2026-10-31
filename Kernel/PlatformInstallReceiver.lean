/-
# Kernel.PlatformInstallReceiver — the controller installs a new platform record

One receiver over the platform cell (`Kernel.PlatformCellLayout`): the deployment's factory
controller replaces the current record with a valid record of a higher version. It is the
receiver of `Kernel.PlatformCell.Admits`.

Authorization, exactly as `PayBookReceiver`: the sponsor presents the control (program)
capability on the factory, verb `installPolicy`, admitted in capability mode under the
factory's current law with the operation slot `authority/operation/platform-install`, the
signature verified by the deployment's native verifier over the request. Beyond that the
sponsor must BE the controller the cell names (`PlatformCellLayout.controllerOf`, written at
genesis): holding the control capability is not enough, so a delegate cannot install.

A custodian-key rotation also carries the CURRENT custodian's raw signature over the same
signed frame the sponsor signed (`Ingress.custodianCosign`, checked by
`CredentialSignatureIO.verify`); a dropped key is refused.

The single-use marker is a function of (domain, semantics, sponsor, version): replaying an
install hits a spent marker, and its version is not above the current one anyway.

The commit gate is the pure `admitsObserved` over the oracles' answers (signature,
capability, cosignature); `admitsObserved_decides` proves it is exactly `PlatformCell.Admits`
of a deployment whose oracles answered so. `receiverContext` is the spec's context with
`encode` the exact frame the native verifier receives (`Moment.frame`, the signed header with
the command inside it by its effect digest), and `receiverDecides` runs the gate on any cell
its writers can make (`PlatformCellLayout.Reachable`: genesis, then installs), where the
controller stays genesis's (`Reachable.controller_stays`). `signed_command_admitted` takes
one signed command through the real codecs and the recorded verifier verdict.
-/
module

public import Compiler.DurableReceiverIO
public import Kernel.CapabilityRevocationController
public import Kernel.PlatformCellDomain
public import Kernel.PlatformCell
public import Kernel.PayTariff
public import Kernel.ReceivingLaw

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
import all Init.System.ST
import all Init.System.IO

@[expose] public section

namespace Minidregg.Kernel.PlatformInstallReceiver

open Minidregg.Compiler
open Minidregg.Compiler.CanonicalPolicyAdmission
open Minidregg.Compiler.CredentialAuthorityDomainReceiver
open Minidregg.Compiler.CredentialAuthorityPolicyRegistry
open Minidregg.Compiler.CredentialAuthorityEntryCodec
open Minidregg.Compiler.ResourceBirthCodec
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Kernel
open Minidregg.Kernel.DurableDataIntent
open Minidregg.Kernel.PlatformCellLayout (Platform PlatformStore recordOf controllerOf installPatch)
open Minidregg.Kernel.PayTariff (framed framed_canonical)
open Minidregg.Theory
open Minidregg.Theory.CellState
open Minidregg.Theory.CellRegistry
open Minidregg.Theory.CredentialAuthorityState
open Minidregg.Theory.CredentialAuthorityEffects
open Minidregg.Theory.IndexedProgram
open Minidregg.Theory.PolicyInstall
open Minidregg.Theory.Store (Store Patch Op Address)
open Minidregg.Theory.TypedAuthorization

set_option autoImplicit false

abbrev Registry := CanonicalCellRegistry.registry
abbrev Deployment := CanonicalCellRegistry.Deployment
abbrev Durable := DurableReceiverIO.Loaded ResourceBirthCodec.rootBytes
abbrev Snapshot := CredentialAuthorityDomain.Snapshot

/-! ## Command and ingress -/

structure Command where
  sponsor : SubjectId
  control : CapabilityId
  expectedFactoryRoot : Digest
  expectedAuthorityRoot : Digest
  expectedPlatformRoot : Digest
  next : Platform
  deriving DecidableEq, Repr

def commandStream : StreamCodec Command :=
  StreamCodec.xmap
    (StreamCodec.product TypedAuthorizationRequestCodec.subjectIdStream
      (StreamCodec.product capabilityIdStream
        (StreamCodec.product digestStream
          (StreamCodec.product digestStream
            (StreamCodec.product digestStream PlatformCellLayout.platformStream)))))
    (fun c => (c.sponsor, c.control, c.expectedFactoryRoot, c.expectedAuthorityRoot,
      c.expectedPlatformRoot, c.next))
    (fun (sponsor, control, factoryRoot, authorityRoot, platformRoot, next) =>
      ⟨sponsor, control, factoryRoot, authorityRoot, platformRoot, next⟩)
    (by intro c; cases c; rfl)

def commandFrame : List UInt8 := "DREGG/PLATFORM/INSTALL/v1".toUTF8.toList

def commandCodec : LawfulCodec Command := framed commandFrame commandStream

theorem command_roundtrip (command : Command) :
    commandCodec.decode (commandCodec.encode command) = some command :=
  commandCodec.decode_encode command

theorem commandCodec_injective {a b : Command} (same : commandCodec.encode a = commandCodec.encode b) :
    a = b :=
  PlatformCell.lawful_injective commandCodec same

/-- The signed ingress: the command bytes, the sponsor's envelope over the request, and, when
the custodian key rotates, the current custodian's raw signature over the envelope's frame. -/
structure Ingress where
  commandBytes : List UInt8
  sponsorEnvelope : List UInt8
  custodianCosign : Option (List UInt8)
  deriving DecidableEq, Repr

def ingressStream : StreamCodec Ingress :=
  StreamCodec.xmap (StreamCodec.product bytesStream
      (StreamCodec.product bytesStream (StreamCodec.option bytesStream)))
    (fun ingress => (ingress.commandBytes, ingress.sponsorEnvelope, ingress.custodianCosign))
    (fun (command, sponsor, cosign) => ⟨command, sponsor, cosign⟩)
    (by intro ingress; cases ingress; rfl)

def ingressCodec : LawfulCodec Ingress :=
  framed "DREGG/PLATFORM/INSTALL/SIGNED/v1".toUTF8.toList ingressStream

structure DecodedIngress where
  private mk ::
  ingress : Ingress
  command : Command
  canonical : commandCodec.encode command = ingress.commandBytes
  envelope : CredentialSignedEnvelopeController.SignedEnvelope
  envelopeExact : CredentialSignatureAdmission.canonicalEnvelopeCodec.decode ingress.sponsorEnvelope =
    some envelope

theorem DecodedIngress.sound (decoded : DecodedIngress) :
    commandCodec.encode decoded.command = decoded.ingress.commandBytes ∧
      CredentialSignatureAdmission.canonicalEnvelopeCodec.decode decoded.ingress.sponsorEnvelope =
        some decoded.envelope :=
  ⟨decoded.canonical, decoded.envelopeExact⟩

def decodeIngress (bytes : List UInt8) : Option DecodedIngress := do
  let ingress ← ingressCodec.decode bytes
  match commandExact : commandCodec.decode ingress.commandBytes with
  | none => none
  | some command =>
    match envelopeExact : CredentialSignatureAdmission.canonicalEnvelopeCodec.decode
        ingress.sponsorEnvelope with
    | none => none
    | some envelope =>
      some ⟨ingress, command, framed_canonical commandFrame commandStream commandExact,
        envelope, envelopeExact⟩

def DecodedIngress.bytes (ingress : DecodedIngress) : List UInt8 :=
  ingressCodec.encode ingress.ingress

/-- The single-use marker: one per (sponsor, version) in a deployment and semantics. -/
def marker (domain semantics : Digest) (command : Command) : Nat :=
  (Sp800185Cshake256.hash "DREGG.PLATFORM.INSTALL.IDENTITY/v1".toUTF8.toList
    ((StreamCodec.product digestStream (StreamCodec.product digestStream
      (StreamCodec.product TypedAuthorizationRequestCodec.subjectIdStream
        StreamCodec.nat))).encode
      (domain, semantics, command.sponsor, command.next.version))).digest.value

/-! ## The decision -/

inductive Reject where
  | malformedIngress | directoryUnavailable | authorityUnavailable | factoryUnavailable
  | platformUnavailable | staleAuthority | stalePlatform
  | notController | versionNotIncreasing | recordInvalid | custodianDropped
  | custodianNotCosigned | custodianCosignRejected
  | replayedMarker | validation | physicalPreparation
  | policyUnavailable | capabilityRejected | policyRejected | policyInputRange | policyCastAlias
  | signature (reason : CredentialSignatureAdmission.Reject)
  deriving DecidableEq, Repr

/-- What the custodian rule needs from IO: nothing, or a check of `cosign` under `old`. -/
inductive CustodianNeed where
  | none
  | check (old cosign : List UInt8)
  deriving DecidableEq, Repr

/-- The oracle-free half, run before any signature is checked: the cell holds a record and
its controller, the sponsor is that controller, the version rises, the record is valid, and
the custodian step is shaped (no drop; a rotation carries a cosignature). -/
def decideRecord (store : PlatformStore) (command : Command) (cosign : Option (List UInt8)) :
    Except Reject (Platform × CustodianNeed) :=
  match recordOf store, controllerOf store with
  | some current, some controller =>
      if command.sponsor ≠ controller then .error .notController
      else if ¬ current.version < command.next.version then .error .versionNotIncreasing
      else if command.next.valid = false then .error .recordInvalid
      else
        match current.completionCustodianKey, command.next.completionCustodianKey with
        | none, _ => .ok (current, .none)
        | some _, none => .error .custodianDropped
        | some old, some new =>
            if old = new then .ok (current, .none)
            else match cosign with
              | some s => .ok (current, .check old s)
              | none => .error .custodianNotCosigned
  | _, _ => .error .platformUnavailable

/-- What the oracles answered for one install: the sponsor's signature over the request,
the control capability under the factory's law, and the custodian's cosignature. -/
structure Observed where
  sponsorVerified : Bool
  capabilityHeld : Bool
  cosignVerified : Bool
  /-- The envelope controller's expiry check: the signed `validUntil` against the admission
  height. -/
  unexpired : Bool
  deriving DecidableEq, Repr

/-- **The commit gate.** The receiver commits an install only when this holds of the loaded
cell, the command, the presented cosignature and the oracles' answers. -/
def admitsObserved (store : PlatformStore) (command : Command) (cosign : Option (List UInt8))
    (o : Observed) : Bool :=
  match recordOf store, controllerOf store with
  | some current, some controller =>
      decide (command.sponsor = controller) && o.sponsorVerified && o.capabilityHeld &&
        decide (current.version < command.next.version) && command.next.valid &&
        PlatformCell.custodianCheck (fun _ _ _ => o.cosignVerified) [] cosign
          current.completionCustodianKey command.next.completionCustodianKey &&
        o.unexpired
  | _, _ => false

/-! ### The gate is the spec's admission -/

/-- The install the spec reads off a command and its signatures. -/
def installOf (command : Command) (envelope : List UInt8) (cosign : Option (List UInt8))
    (validUntil : Nat) : PlatformCell.Install :=
  ⟨command.next, command.sponsor, command.control, envelope, cosign, validUntil⟩

/-- The command an install stands for, at the pinned roots `roots`. -/
def commandAt (roots : Digest × Digest × Digest) (i : PlatformCell.Install) : Command :=
  ⟨i.subject, i.capability, roots.1, roots.2.1, roots.2.2, i.next⟩

theorem custodianCheck_congr (v w : List UInt8 → List UInt8 → List UInt8 → Bool)
    (b c : List UInt8) (cosign : Option (List UInt8)) (old new : Option (List UInt8))
    (agree : ∀ k s, old = some k → cosign = some s → v k b s = w k c s) :
    PlatformCell.custodianCheck v b cosign old new = PlatformCell.custodianCheck w c cosign old new := by
  rcases old with _ | k <;> rcases new with _ | n <;> simp only [PlatformCell.custodianCheck]
  rcases cosign with _ | s
  · rfl
  · simp [agree k s rfl rfl]

set_option backward.isDefEq.respectTransparency false in
/-- **`admitsObserved` is exactly `PlatformCell.Admits`** of any deployment whose oracles
answered `o` and whose controller is the one the cell names, over a history whose current
record the cell holds. -/
theorem admitsObserved_decides (ctx : PlatformCell.Context) (h : PlatformCell.History)
    (store : PlatformStore) (command : Command) (envelope : List UInt8)
    (cosign : Option (List UInt8)) (validUntil : Nat) (o : Observed)
    (cellHolds : recordOf store = some h.current)
    (controllerHolds : controllerOf store = some ctx.deployment.controller)
    (sponsor : ctx.deployment.verifies ctx.deployment.controller
      (ctx.encode h.current (installOf command envelope cosign validUntil)) envelope = o.sponsorVerified)
    (held : ctx.deployment.holdsInstall ctx.deployment.controller command.control = o.capabilityHeld)
    (cosigned : ∀ old s, h.current.completionCustodianKey = some old → cosign = some s →
      ctx.deployment.verifiesKey old (ctx.encode h.current (installOf command envelope cosign validUntil)) s =
        o.cosignVerified)
    (unexpired : decide (ctx.height ≤ validUntil) = o.unexpired) :
    admitsObserved store command cosign o = true ↔
      PlatformCell.Admits ctx h (installOf command envelope cosign validUntil) := by
  rw [← PlatformCell.decideInstall_decides]
  have custodian := custodianCheck_congr (fun _ _ _ => o.cosignVerified) ctx.deployment.verifiesKey
    [] (ctx.encode h.current (installOf command envelope cosign validUntil)) cosign h.current.completionCustodianKey
    command.next.completionCustodianKey (fun k s hk hs => (cosigned k s hk hs).symm)
  simp only [installOf] at sponsor custodian
  simp only [admitsObserved, cellHolds, controllerHolds, PlatformCell.decideInstall, installOf,
    sponsor, held, custodian, ← unexpired]

/-- The oracle answers a deployment gives for an install over a history. -/
def oracle (ctx : PlatformCell.Context) (h : PlatformCell.History) (i : PlatformCell.Install) :
    Observed :=
  ⟨ctx.deployment.verifies ctx.deployment.controller (ctx.encode h.current i) i.envelope,
    ctx.deployment.holdsInstall ctx.deployment.controller i.capability,
    match h.current.completionCustodianKey, i.custodianCosign with
    | some old, some s => ctx.deployment.verifiesKey old (ctx.encode h.current i) s
    | _, _ => false,
    decide (ctx.height ≤ i.validUntil)⟩

/-- Teeth: an unverified sponsor signature is refused whatever else holds. -/
theorem unsigned_refused (store : PlatformStore) (command : Command) (cosign : Option (List UInt8))
    (held cosigned unexpired : Bool) :
    admitsObserved store command cosign ⟨false, held, cosigned, unexpired⟩ = false := by
  unfold admitsObserved; split <;> simp

/-- Teeth: a sponsor other than the cell's controller is refused, every oracle answering yes. -/
theorem delegate_refused (controller : SubjectId) (current : Platform) (command : Command)
    (cosign : Option (List UInt8)) (other : command.sponsor ≠ controller) :
    admitsObserved (PlatformCellLayout.genesisStore controller current) command cosign
      ⟨true, true, true, true⟩ = false := by
  simp [admitsObserved, other]

/-- Satisfiable pole: the controller's signed install of its valid record one version up,
with no custodian key involved, is admitted. -/
theorem controller_install_admitted (controller : SubjectId) (current : Platform)
    (control : CapabilityId) (roots : Digest × Digest × Digest)
    (valid : current.valid = true) (noKey : current.completionCustodianKey = none) :
    admitsObserved (PlatformCellLayout.genesisStore controller current)
      ⟨controller, control, roots.1, roots.2.1, roots.2.2,
        { current with version := current.version + 1 }⟩ none
      ⟨true, true, false, true⟩ = true := by
  rcases current with ⟨v, c, g, k, o, l⟩
  simp only at noKey
  subst noKey
  simp only [PlatformCellLayout.Platform.valid, Bool.and_eq_true] at valid
  simp [admitsObserved, PlatformCell.custodianCheck, PlatformCellLayout.Platform.valid, valid]

/-! ## The effect family over the platform cell -/

structure Plan where
  current : Platform
  next : Platform
  deriving DecidableEq, Repr

def Plan.patch (plan : Plan) : Patch PlatformCellLayout.layout := installPatch plan.current plan.next

def planStream : StreamCodec Plan :=
  StreamCodec.xmap (StreamCodec.product PlatformCellLayout.platformStream PlatformCellLayout.platformStream)
    (fun plan => (plan.current, plan.next))
    (fun (current, next) => ⟨current, next⟩)
    (by intro plan; cases plan; rfl)

structure Declaration where
  plan : Plan
  expectedPreRoot : Digest
  operationNullifier : Nat

def declarationStream : StreamCodec Declaration :=
  StreamCodec.xmap (StreamCodec.product planStream (StreamCodec.product digestStream StreamCodec.nat))
    (fun d => (d.plan, d.expectedPreRoot, d.operationNullifier))
    (fun (plan, root, nullifier) => ⟨plan, root, nullifier⟩)
    (by intro d; cases d; rfl)

def declarationCodec : LawfulCodec Declaration :=
  declarationStream.toLawful

def declaration (domain semantics : Digest) (command : Command) (plan : Plan) : Declaration :=
  ⟨plan, command.expectedPlatformRoot, marker domain semantics command⟩

structure Mode {M : Materializer PlatformCellLayout.layout Digest} (pre : Materialized M)
    (d : Declaration) : Type where
  rootExact : d.expectedPreRoot = pre.root

def effectCustomization : List UInt8 := "DREGG.PLATFORM.INSTALL.EFFECT/v1".toUTF8.toList

def effectSourceStream : StreamCodec (Digest × Digest × List UInt8 × List UInt8) :=
  StreamCodec.product digestStream (StreamCodec.product digestStream
    (StreamCodec.product bytesStream bytesStream))

/-- The bytes the effect digest hashes: the deployment, the semantics, the command and the
declaration (the plan from the current record to the next). -/
def effectSource (domain semantics : Digest) (command : Command) (d : Declaration) : List UInt8 :=
  effectSourceStream.encode (domain, semantics, commandCodec.encode command, declarationCodec.encode d)

def effectDigest (domain semantics : Digest) (command : Command) (d : Declaration) : Digest :=
  PlatformCell.pinDigest effectCustomization (effectSource domain semantics command d)

structure Ambient where
  federation : FederationId
  height : Height

def context (deployment : Deployment) (snapshot : Snapshot) (semantics : Digest)
    (ambient : Ambient) (command : Command) : RequestContext where
  authority :=
    { kind := .program
      domain := snapshot.domain
      semantics := semantics
      federation := ambient.federation
      subject := command.sponsor
      subjectKeyEpoch := snapshot.authState.subjectKeyEpoch command.sponsor
      target := ⟨deployment.factoryId⟩
      verb := .installPolicy
      nonce := marker snapshot.domain semantics command
      height := ambient.height
      policyId := ⟨deployment.factoryId⟩
      policyEpoch := snapshot.authState.policyEpoch ⟨deployment.factoryId⟩
      policyRevision := snapshot.authState.policyRevision ⟨deployment.factoryId⟩
      cost := (commandCodec.encode command).length }
  argsDigestBytes := fun bytes =>
    (Sp800185Cshake256.hash "DREGG.PLATFORM.INSTALL.ARGS/v1".toUTF8.toList
      (commandCodec.encode command ++ bytes)).digest

def request (deployment : Deployment) (snapshot : Snapshot) (platform : PlatformCellDomain.Cell)
    (semantics : Digest) (ambient : Ambient) (command : Command) (plan : Plan) : Request .program :=
  ((context deployment snapshot semantics ambient command).request declarationCodec
    (effectDigest snapshot.domain semantics command) platform.root
    (marker snapshot.domain semantics command)
    (declaration snapshot.domain semantics command plan)).2

def family (deployment : Deployment) (snapshot : Snapshot) (platform : PlatformCellDomain.Cell)
    (semantics : Digest) (ambient : Ambient) (command : Command) :
    SemanticEffectFamily PlatformCellLayout.layout PlatformCellLayout.materializer Nat where
  Declaration := Declaration
  declarationCodec := declarationCodec
  pre := platform
  request := fun d => (context deployment snapshot semantics ambient command).request
    declarationCodec (effectDigest snapshot.domain semantics command) platform.root
    d.operationNullifier d
  Outcome := fun _ => Unit
  outcomeCodec := fun _ => unitCodec
  ModeEvidence := fun d _ => Mode platform d
  Postcondition := fun d _ post => d.plan.patch.ResultAt platform.logical post
  effectDigest := effectDigest snapshot.domain semantics command
  patch := fun d _ => d.plan.patch
  nullifier := fun d _ => some d.operationNullifier
  Release := fun _ _ => Unit
  DeclassificationAuthority := fun _ _ => Unit
  ReleaseAuthorization := fun _ _ _ => Unit
  DisclosureAllowed := fun _ _ => sealedOnly

def requireSome {A : Type} (reason : Reject) : Option A → Except Reject A
  | none => .error reason
  | some value => .ok value

/-! ## Preparation -/

structure Prepared {F : Type} [Field F] (deployment : Deployment)
    (profile : CanonicalRuntimeProfile.Profile F) (ambient : Ambient) (durable : Durable)
    (command : Command) (cosign : Option (List UInt8)) where
  private mk ::
  directory : LoadedDirectory durable
  authority : CredentialAuthorityDomainReceiver.Loaded deployment durable.snapshot
  factory : ResourceTargetAdmission.Observed deployment directory.directory .object
    deployment.factoryId command.expectedFactoryRoot
  platform : PlatformCellDomain.Loaded deployment durable.snapshot
  current : Platform
  need : CustodianNeed
  decided : decideRecord platform.cell.logical command cosign = .ok (current, need)
  candidate : Candidate (family deployment authority.snapshot platform.cell profile.semantics ambient command)
    platform.cell (declaration authority.snapshot.domain profile.semantics command ⟨current, command.next⟩) ()
  source : CanonicalCellRegistry.LoadedPolicySource authority.snapshot.domain directory.directory
    (authority.snapshot.authState.policyAddress ⟨deployment.factoryId⟩
      (authority.snapshot.authState.policyRevision ⟨deployment.factoryId⟩))

def prepare {F : Type} [Field F] (deployment : Deployment)
    (profile : CanonicalRuntimeProfile.Profile F) (ambient : Ambient) (durable : Durable)
    (command : Command) (cosign : Option (List UInt8)) :
    Except Reject (Prepared deployment profile ambient durable command cosign) := do
  let directory ← requireSome .directoryUnavailable (loadDirectory durable)
  let authority ← requireSome .authorityUnavailable (loadDeployment deployment durable.snapshot)
  let factory ← requireSome .factoryUnavailable
    (ResourceTargetAdmission.observe deployment directory.directory .object
      deployment.factoryId command.expectedFactoryRoot)
  let platform ← requireSome .platformUnavailable (PlatformCellDomain.load deployment durable.snapshot)
  let snapshot := authority.snapshot
  if command.expectedAuthorityRoot = snapshot.cell.root then
    if rootExact : command.expectedPlatformRoot = platform.cell.root then
      match decided : decideRecord platform.cell.logical command cosign with
      | .error reason => throw reason
      | .ok (current, need) =>
        let d := declaration snapshot.domain profile.semantics command ⟨current, command.next⟩
        if snapshot.spent d.operationNullifier = false then
          match validate PlatformCellLayout.materializer platform.cell platform.cell.root d.plan.patch with
          | .rejected _ => throw .validation
          | .accepted validated =>
              let source ← requireSome .policyUnavailable (CanonicalCellRegistry.loadPolicySource
                snapshot.domain directory.directory
                (snapshot.authState.policyAddress ⟨deployment.factoryId⟩
                  (snapshot.authState.policyRevision ⟨deployment.factoryId⟩)))
              let candidate : Candidate
                  (family deployment snapshot platform.cell profile.semantics ambient command)
                  platform.cell d () :=
                { preStateBound := rfl
                  modeEvidence := ⟨rootExact⟩
                  validated := validated
                  postcondition := validated.resultAt }
              pure ⟨directory, authority, factory, platform, current, need, decided, candidate, source⟩
        else throw .replayedMarker
    else throw .stalePlatform
  else throw .staleAuthority

variable {F : Type} [Field F] {deployment : Deployment}
  {profile : CanonicalRuntimeProfile.Profile F} {ambient : Ambient} {durable : Durable}
  {command : Command} {cosign : Option (List UInt8)}

def Prepared.plan (prepared : Prepared deployment profile ambient durable command cosign) : Plan :=
  ⟨prepared.current, command.next⟩

/-- The platform cell after the install: the validated patch applied to the loaded cell. -/
def Prepared.platformPost (prepared : Prepared deployment profile ambient durable command cosign) :
    PlatformCellDomain.Cell :=
  prepared.candidate.validated.apply

def project (prepared : Prepared deployment profile ambient durable command cosign)
    (logical : PlatformStore) : Minidregg.Pred.State :=
  ⟨WorldKindLawDependencies.targetSelectorSlots prepared.directory.directory deployment.factoryId ++
    CanonicalRuntimeProfile.requestSlots
      (request deployment prepared.authority.snapshot prepared.platform.cell profile.semantics ambient
        command prepared.plan) ++
    [("authority/operation/platform-install", 1),
     ("platform/version", Int.ofNat ((recordOf logical).map Platform.version |>.getD 0))] ++
    DeclaredResourceController.bytesSlots "command/bytes" 0 (commandCodec.encode command) ++
    DeclaredResourceController.bytesSlots "resource/bytes" 0
      (PackedCell.bytes Registry prepared.factory.before) ++
    ResourceAuthorityProjection.grantSlots "authority/control" .program command.control
      prepared.authority.snapshot.logical⟩

def step (prepared : Prepared deployment profile ambient durable command cosign) : PolicyStepContext :=
  PolicyStepContext.ofCandidate (project prepared) profile.semantics prepared.candidate

def kindDependencies (prepared : Prepared deployment profile ambient durable command cosign) :
    Option WorldKindLawDependencies.Dependencies :=
  WorldKindLawDependencies.loadTarget deployment prepared.directory.directory deployment.factoryId

def policyConfig [DecidableEq F]
    (prepared : Prepared deployment profile ambient durable command cosign) :
    ComposedPolicyAdmission.Config F :=
  PhysicalLawResolution.config profile.compilerProfile prepared.authority.snapshot
    prepared.directory.directory
    (sourceCapabilityPortal prepared.authority.snapshot
      (marker prepared.authority.snapshot.domain profile.semantics command))
    (step prepared) deployment.factoryId
    ((kindDependencies prepared).map (·.additional) |>.getD [])

def lawReadGuards (prepared : Prepared deployment profile ambient durable command cosign) :
    Option (List (Nat × Digest)) := do
  let structural ← kindDependencies prepared
  let sources ← PhysicalLawResolution.readGuards prepared.authority.snapshot
    prepared.directory.directory profile.semantics deployment.factoryId structural.additional
  pure (sources ++ structural.readGuards)

abbrev Prepared.SemanticAccepted [DecidableEq F]
    (prepared : Prepared deployment profile ambient durable command cosign) :=
  AcceptedCellEffect (portal := (policyConfig prepared).portal)
    (authState := prepared.authority.snapshot.authState)
    (family deployment prepared.authority.snapshot prepared.platform.cell profile.semantics ambient command)
    (request deployment prepared.authority.snapshot prepared.platform.cell profile.semantics ambient
      command prepared.plan)
    prepared.platform.cell
    (declaration prepared.authority.snapshot.domain profile.semantics command prepared.plan) ()

def authorize [DecidableEq F]
    (prepared : Prepared deployment profile ambient durable command cosign)
    (receipt : CredentialSignatureAdmission.CheckedSignature prepared.authority.snapshot) :
    Except Reject prepared.SemanticAccepted := do
  let wanted := request deployment prepared.authority.snapshot prepared.platform.cell profile.semantics
    ambient command prepared.plan
  let config := policyConfig prepared
  let _ ← requireSome .policyUnavailable (kindDependencies prepared)
  let evidence ← requireSome .capabilityRejected
    (config.capabilityEvidenceChecked wanted command.control () receipt () (fun _ => ())).toOption
  let law ← requireSome .policyUnavailable config.resolve?
  let witness := law.witness
  if inputsInRange profile.compilerProfile.compiler law.predicate
      (step prepared).oldState (step prepared).newState != true then
    throw .policyInputRange
  if !decide (castInjOn F
      (intsOf law.predicate (step prepared).oldState (step prepared).newState)) then
    throw .policyCastAlias
  match ComposedPolicyAdmission.admit config wanted
      evidence witness (.policy wanted.policyId wanted.policyRevision) rfl rfl with
  | none => .error .policyRejected
  | some authorization =>
      .ok (prepared.candidate.accept authorization rfl rfl rfl .sealed trivial)

/-- The custodian's answer: `true` exactly when the native verifier verified the cosignature
under the current key over the frame the sponsor signed; no check needed answers `false`,
which the gate never consults (`custodianCheck` reads it only for a rotation). -/
def cosignAnswer (native : CredentialSignatureIO.NativeConfig) (frame : List UInt8) :
    CustodianNeed → IO Bool
  | .none => pure false
  | .check old s => do
      match ← CredentialSignatureIO.verify native old frame s with
      | .ok true => pure true
      | _ => pure false

structure Accepted [DecidableEq F]
    (prepared : Prepared deployment profile ambient durable command cosign)
    (ingress : DecodedIngress) where
  private mk ::
  receipt : CredentialSignatureAdmission.CheckedSignature prepared.authority.snapshot
  envelopeExact : receipt.envelopeBytes = ingress.ingress.sponsorEnvelope
  semantic : prepared.SemanticAccepted
  cosignVerified : Bool
  gate : admitsObserved prepared.platform.cell.logical command cosign ⟨true, true, cosignVerified, true⟩ = true

theorem Accepted.sound [DecidableEq F]
    {prepared : Prepared deployment profile ambient durable command cosign} {ingress : DecodedIngress}
    (accepted : Accepted prepared ingress) :
    accepted.receipt.envelopeBytes = ingress.ingress.sponsorEnvelope ∧
      Nonempty (Authorized (policyConfig prepared).portal prepared.authority.snapshot.authState
        (request deployment prepared.authority.snapshot prepared.platform.cell profile.semantics ambient
          command prepared.plan)) ∧
      admitsObserved prepared.platform.cell.logical command cosign
        ⟨true, true, accepted.cosignVerified, true⟩ = true :=
  ⟨accepted.envelopeExact, ⟨accepted.semantic.authorization⟩, accepted.gate⟩

def admitNative [DecidableEq F] (native : CredentialSignatureIO.NativeConfig)
    (prepared : Prepared deployment profile ambient durable command cosign)
    (ingress : DecodedIngress) : IO (Except Reject (Accepted prepared ingress)) := do
  match ← CredentialSignatureAdmission.verifyNative native prepared.authority.snapshot
      (marker prepared.authority.snapshot.domain profile.semantics command)
      (request deployment prepared.authority.snapshot prepared.platform.cell profile.semantics ambient
        command prepared.plan)
      ingress.ingress.sponsorEnvelope with
  | .error reason => return .error (.signature reason)
  | .ok receipt =>
      if same : receipt.envelopeBytes = ingress.ingress.sponsorEnvelope then
        match authorize prepared receipt with
        | .error reason => return .error reason
        | .ok semantic =>
            let cosigned ← cosignAnswer native receipt.prepared.controller.frame prepared.need
            if gate : admitsObserved prepared.platform.cell.logical command cosign
                ⟨true, true, cosigned, true⟩ = true then
              return .ok ⟨receipt, same, semantic, cosigned, gate⟩
            else return .error .custodianCosignRejected
      else return .error .capabilityRejected

/-- The exact header the sponsor signs, derived from the current platform cell and authority. -/
def signingHeader (deployment : Deployment) (profile : CanonicalRuntimeProfile.Profile F)
    (ambient : Ambient) (durable : Durable) (command : Command) :
    Except String CredentialSignedEnvelopeController.SignedHeader := do
  let some authority := loadDeployment deployment durable.snapshot
    | .error "authority unavailable"
  let some platform := PlatformCellDomain.load deployment durable.snapshot
    | .error "platform cell unavailable"
  let some current := recordOf platform.cell.logical
    | .error "platform cell holds no record"
  (CredentialSignatureAdmission.signingHeader authority.snapshot
    (marker deployment.domain profile.semantics command)
    ⟨.program, request deployment authority.snapshot platform.cell profile.semantics ambient command
      ⟨current, command.next⟩⟩).mapError
      (fun reason => s!"platform-install signer key: {repr reason}")

/-! ## The spec's context at the receiver: the signed bytes, the loaded cell -/

/-- One admission moment: everything the request and the signed header read besides the
command, the current record and the signer's `validUntil`. -/
structure Moment where
  deployment : Deployment
  snapshot : Snapshot
  cell : PlatformCellDomain.Cell
  semantics : Digest
  ambient : Ambient
  key : CredentialSignedEnvelopeController.KeyRecord

def Moment.request (m : Moment) (current : Platform) (command : Command) : Request .program :=
  _root_.Minidregg.Kernel.PlatformInstallReceiver.request m.deployment m.snapshot m.cell m.semantics
    m.ambient command ⟨current, command.next⟩

/-- The header the sponsor signs at this moment (`CredentialSignatureAdmission.header`, the
header `prepare` requires an envelope to carry). -/
def Moment.header (m : Moment) (current : Platform) (command : Command) (validUntil : Nat) :
    CredentialSignedEnvelopeController.SignedHeader :=
  CredentialSignatureAdmission.header m.snapshot m.key (marker m.snapshot.domain m.semantics command)
    ⟨.program, m.request current command⟩ validUntil

/-- **The bytes the sponsor's signature covers**: the header's frame, exactly what the native
verifier receives (`SignedEnvelope.frame`). -/
def Moment.frame (m : Moment) (current : Platform) (command : Command) (validUntil : Nat) :
    List UInt8 :=
  CredentialSignedEnvelopeController.headerCodec.encode (m.header current command validUntil)

/-- Equal frames carry equal effect digests: the header holds the signed request bytes,
which determine every plan field (`signedRequestBytes_eq_iff`). -/
theorem Moment.frame_effectsDigest (m : Moment) (current : Platform) (a b : Command) (u v : Nat)
    (same : m.frame current a u = m.frame current b v) :
    (m.request current a).effectsDigest = (m.request current b).effectsDigest := by
  have headers := PlatformCell.lawful_injective CredentialSignedEnvelopeController.headerCodec same
  have messages := congrArg CredentialSignedEnvelopeController.SignedHeader.message headers
  have plans := (TypedAuthorizationRequestCodec.signedRequestBytes_eq_iff _ _).mp messages
  simpa [TypedAuthorizationRequestCodec.planOf] using
    congrArg (fun r : Minidregg.Theory.AuthorizationDeclaration.SomeRequest => r.2.effectsDigest) plans

/-- **The deployed context.** `encode` is the frame the native verifier receives for the
install's command on `current`; it pins the effect source (deployment, semantics, command and
plan) by the effect digest, and the source covers the whole record through the command codec. -/
def receiverContext (d : PlatformCell.Deployment) (m : Moment) (roots : Digest × Digest × Digest) :
    PlatformCell.Context where
  deployment := d
  height := m.ambient.height
  encode current i := m.frame current (commandAt roots i) i.validUntil
  source current i := effectSource m.snapshot.domain m.semantics (commandAt roots i)
    (declaration m.snapshot.domain m.semantics (commandAt roots i) ⟨current, i.next⟩)
  customization := effectCustomization
  pins current i j same := m.frame_effectsDigest current _ _ _ _ same
  sourceCovers current i j same := by
    have tuples := PlatformCell.lawful_injective (StreamCodec.toLawful effectSourceStream) same
    simp only [Prod.mk.injEq] at tuples
    have commands := commandCodec_injective tuples.2.2.1
    simp only [commandAt, Command.mk.injEq] at commands
    exact ⟨commands.2.2.2.2.2, commands.1, commands.2.1⟩

/-- Every lawful write of a platform cell is the install family's: the kind is kernelOnly
with that one writer (`CanonicalCellRegistry.platform_only_install`). With genesis, these
are the writers `PlatformCellLayout.Reachable` admits. -/
theorem platform_written_only_by_install {S : Type} (laws : ReceivingLaw.Laws S)
    (family : CanonicalCellRegistry.FamilyId) (state : S) (named : DataWrite → Prop) (patch : List DataWrite)
    (write : DataWrite) (step : Option PolicyStepContext)
    (lawful : ReceivingLaw.LawfulBy laws family state named patch write step)
    (platform : laws.kindOf state write = some .platform) : family = .platformInstall := by
  obtain ⟨kind, found, classes⟩ := lawful
  rw [platform] at found
  cases found
  rcases classes with ⟨bearing, -⟩ | ⟨writers, only, member, -⟩ | ⟨writers, born, -⟩
  · cases bearing
  · cases only; simpa using member
  · cases born

/-- **L1-c at the receiver: `PlatformCell.Decides` on the loaded cell.** For any loader whose
cells its writers can make (`Reachable` from genesis under the deployment's controller) and
which hold the history's current record, the gate with the deployment's oracle answers
decides exactly `Admits`. -/
theorem receiverDecides (ctx : PlatformCell.Context) (roots : Digest × Digest × Digest)
    (load : PlatformCell.History → PlatformStore)
    (reach : ∀ h, PlatformCellLayout.Reachable ctx.deployment.controller (load h))
    (holds : ∀ h, recordOf (load h) = some h.current) :
    PlatformCell.Decides ctx (fun h i =>
      admitsObserved (load h) (commandAt roots i) i.custodianCosign (oracle ctx h i)) := by
  intro h i
  have same : installOf (commandAt roots i) i.envelope i.custodianCosign i.validUntil = i := by
    cases i; rfl
  have := admitsObserved_decides ctx h (load h) (commandAt roots i) i.envelope i.custodianCosign
    i.validUntil (oracle ctx h i) (holds h) (reach h).controller_stays
    (by rw [same]; rfl) rfl
    (by intro old s hk hs; rw [same]; simp [oracle, hk, hs]) (by simp [oracle])
  rwa [same] at this

theorem frame_mk (header : CredentialSignedEnvelopeController.SignedHeader) (signature : List UInt8) :
    CredentialSignedEnvelopeController.SignedEnvelope.frame ⟨header, signature⟩ =
      CredentialSignedEnvelopeController.headerCodec.encode header := rfl

/-- The decoder returns exactly what the three codecs decode. -/
theorem decodeIngress_of {bytes : List UInt8} {ingress : Ingress} {command : Command}
    {envelope : CredentialSignedEnvelopeController.SignedEnvelope}
    (outer : ingressCodec.decode bytes = some ingress)
    (inner : commandCodec.decode ingress.commandBytes = some command)
    (signed : CredentialSignatureAdmission.canonicalEnvelopeCodec.decode ingress.sponsorEnvelope =
      some envelope) :
    ∃ decoded, decodeIngress bytes = some decoded ∧ decoded.command = command ∧
      decoded.envelope = envelope := by
  unfold decodeIngress
  simp only [outer]
  dsimp only [bind, Option.bind]
  split
  next none => rw [inner] at none; cases none
  next found foundExact =>
    rw [inner] at foundExact; cases foundExact
    split
    next none => rw [signed] at none; cases none
    next env envExact =>
      rw [signed] at envExact; cases envExact
      exact ⟨_, rfl, rfl, rfl⟩

/-- **Satisfiable pole through the real path.** The controller signs the moment's header for
its command (an unchanged custodian key); the ingress is built by the real codecs. It decodes
back to that command and envelope; the envelope's frame (what the native verifier receives)
is `receiverContext`'s `encode`; and with the verifier's verdict on that frame recorded under
the controller's enrolled key, the gate admits the install on any reachable cell holding the
current record, and so does `Admits`. -/
theorem signed_command_admitted (d : PlatformCell.Deployment) (m : Moment) (store : PlatformStore)
    (reach : PlatformCellLayout.Reachable d.controller store) (h : PlatformCell.History)
    (holds : recordOf store = some h.current) (command : Command) (validUntil : Nat)
    (signature key : List UInt8)
    (sponsor : command.sponsor = d.controller)
    (enrolled : d.keyOf d.controller = some key)
    (recorded : (key, m.frame h.current command validUntil, signature) ∈ d.transcript.verified)
    (held : d.holdsInstall d.controller command.control = true)
    (up : h.current.version < command.next.version) (valid : command.next.valid = true)
    (keyKept : command.next.completionCustodianKey = h.current.completionCustodianKey)
    (unexpired : m.ambient.height ≤ validUntil) :
    let envelope : CredentialSignedEnvelopeController.SignedEnvelope :=
      ⟨m.header h.current command validUntil, signature⟩
    let roots := (command.expectedFactoryRoot, command.expectedAuthorityRoot,
      command.expectedPlatformRoot)
    let install := installOf command signature none validUntil
    ∃ decoded, decodeIngress (ingressCodec.encode ⟨commandCodec.encode command,
          CredentialSignatureAdmission.canonicalEnvelopeCodec.encode envelope, none⟩) = some decoded ∧
      decoded.command = command ∧ decoded.envelope = envelope ∧
      decoded.envelope.frame = (receiverContext d m roots).encode h.current install ∧
      admitsObserved store command none (oracle (receiverContext d m roots) h install) = true ∧
      PlatformCell.Admits (receiverContext d m roots) h install := by
  intro envelope roots install
  have atRoots : commandAt roots install = command := by cases command; rfl
  have encodes : (receiverContext d m roots).encode h.current install =
      m.frame h.current command validUntil := by
    show m.frame h.current (commandAt roots install) validUntil = _
    rw [atRoots]
  have admits : PlatformCell.Admits (receiverContext d m roots) h install := by
    refine ⟨sponsor, ?_, held, up, valid, ?_, unexpired⟩
    · show d.verifies d.controller _ signature = true
      rw [encodes]
      simp [PlatformCell.Deployment.verifies, enrolled, recorded]
    · show PlatformCell.CustodianStep _ _ none h.current.completionCustodianKey
        command.next.completionCustodianKey
      rw [keyKept]
      cases h.current.completionCustodianKey <;> simp [PlatformCell.CustodianStep]
  have gate := (admitsObserved_decides (receiverContext d m roots) h store command signature none
    validUntil (oracle (receiverContext d m roots) h install) holds reach.controller_stays
    (by unfold oracle; rfl) (by unfold oracle; rfl) (by intro old s _ hs; cases hs)
    (by unfold oracle; rfl)).mpr admits
  let ingress : Ingress := ⟨commandCodec.encode command,
    CredentialSignatureAdmission.canonicalEnvelopeCodec.encode envelope, none⟩
  obtain ⟨decoded, decodes, sameCommand, sameEnvelope⟩ := decodeIngress_of (ingress := ingress)
    (ingressCodec.decode_encode ingress) (command_roundtrip command)
    (CredentialSignatureAdmission.canonicalEnvelopeCodec.decode_encode envelope)
  refine ⟨decoded, decodes, sameCommand, sameEnvelope, ?_, gate, admits⟩
  rw [sameEnvelope, encodes]
  exact frame_mk _ _

/-! ## The receiver -/

def transactionId (domain semantics : Digest) (ingress : DecodedIngress) : Digest :=
  ⟨marker domain semantics ingress.command⟩

def event (domain _semantics : Digest) (ingress : DecodedIngress) : StableEvent where
  codecVersion := 1
  domain := domain
  eventId := (Sp800185Cshake256.hash "DREGG.PLATFORM.INSTALL.EVENT/v1".toUTF8.toList ingress.bytes).digest
  canonicalBytes := ingress.bytes

def nullifier (domain semantics : Digest) (ingress : DecodedIngress) : StableNullifier :=
  CredentialAuthorityReplay.nullifier domain (marker domain semantics ingress.command)

def writes (prepared : Prepared deployment profile ambient durable command cosign) : List DataWrite :=
  [prepared.platform.write prepared.platformPost]

def resourceGuard (prepared : Prepared deployment profile ambient durable command cosign) : ReadGuard :=
  ⟨⟨deployment.factoryId⟩,
    rootBytes (LifecycleImage.bytes Registry (.live prepared.factory.before))⟩

def policyGuard (prepared : Prepared deployment profile ambient durable command cosign) : ReadGuard :=
  ⟨⟨prepared.source.readGuard.1⟩, prepared.source.readGuard.2⟩

def readGuards (prepared : Prepared deployment profile ambient durable command cosign) :
    List ReadGuard :=
  let written := (writes prepared).map DataWrite.cellId
  resourceGuard prepared :: policyGuard prepared ::
    (prepared.authority.readGuards ++
      ((lawReadGuards prepared).getD []).map (fun (cellIdValue, root) =>
        (⟨⟨cellIdValue⟩, root⟩ : Minidregg.Kernel.DurableDataIntent.ReadGuard))).filter
      fun guard => guard.cellId ∉ written

def PhysicalShape (prepared : Prepared deployment profile ambient durable command cosign) : Prop :=
  ((writes prepared).map DataWrite.cellId).Nodup ∧
    (∀ write ∈ writes prepared, write.expectedPre = durable.snapshot.model.roots write.cellId) ∧
    (∀ write ∈ writes prepared, ResourceBirthController.Concrete.PhysicalPostLaw deployment write) ∧
    (resourceGuard prepared).cellId ∉ (writes prepared).map DataWrite.cellId ∧
    (policyGuard prepared).cellId ∉ (writes prepared).map DataWrite.cellId ∧
    (∀ guard ∈ readGuards prepared, guard.expectedRoot = durable.snapshot.model.roots guard.cellId) ∧
    (lawReadGuards prepared).isSome = true

instance physicalShapeDecidable (prepared : Prepared deployment profile ambient durable command cosign) :
    Decidable (PhysicalShape prepared) := by
  unfold PhysicalShape
  infer_instance

theorem writes_roots_bound (prepared : Prepared deployment profile ambient durable command cosign)
    (write : DataWrite) (member : write ∈ writes prepared) :
    rootBytes write.canonicalPostBytes = write.exactPost := by
  simp only [writes, List.mem_singleton] at member
  subst write
  exact prepared.platform.write_root_bound _

theorem readGuards_readonly (prepared : Prepared deployment profile ambient durable command cosign)
    (shape : PhysicalShape prepared) (guard : ReadGuard) (member : guard ∈ readGuards prepared) :
    guard.cellId ∉ (writes prepared).map DataWrite.cellId := by
  rcases List.mem_cons.mp member with rfl | rest
  · exact shape.2.2.2.1
  · rcases List.mem_cons.mp rest with rfl | authority
    · exact shape.2.2.2.2.1
    · simpa using (List.mem_filter.mp authority).2

structure AcceptedInstall [DecidableEq F] (deployment : Deployment)
    (profile : CanonicalRuntimeProfile.Profile F) (ambient : Ambient) (durable : Durable)
    (ingress : DecodedIngress) where
  private mk ::
  prepared : Prepared deployment profile ambient durable ingress.command ingress.ingress.custodianCosign
  accepted : PlatformInstallReceiver.Accepted prepared ingress
  physical : PhysicalShape prepared

theorem AcceptedInstall.sound [DecidableEq F] {ingress : DecodedIngress}
    (accepted : AcceptedInstall deployment profile ambient durable ingress) :
    accepted.accepted.receipt.envelopeBytes = ingress.ingress.sponsorEnvelope ∧
      admitsObserved accepted.prepared.platform.cell.logical ingress.command
        ingress.ingress.custodianCosign ⟨true, true, accepted.accepted.cosignVerified, true⟩ = true ∧
      Nonempty (Authorized (policyConfig accepted.prepared).portal
        accepted.prepared.authority.snapshot.authState
        (request deployment accepted.prepared.authority.snapshot accepted.prepared.platform.cell
          profile.semantics ambient ingress.command accepted.prepared.plan)) ∧
      PhysicalShape accepted.prepared :=
  ⟨accepted.accepted.envelopeExact, accepted.accepted.gate,
    ⟨accepted.accepted.semantic.authorization⟩, accepted.physical⟩

def admitDecodedNative [DecidableEq F] (deployment : Deployment)
    (profile : CanonicalRuntimeProfile.Profile F) (ambient : Ambient) (durable : Durable)
    (native : CredentialSignatureIO.NativeConfig) (ingress : DecodedIngress) :
    IO (Except Reject (AcceptedInstall deployment profile ambient durable ingress)) := do
  match prepare deployment profile ambient durable ingress.command ingress.ingress.custodianCosign with
  | .error reason => return .error reason
  | .ok prepared =>
    if physical : PhysicalShape prepared then
      match ← admitNative native prepared ingress with
      | .error reason => return .error reason
      | .ok accepted => return .ok ⟨prepared, accepted, physical⟩
    else return .error .physicalPreparation

variable [DecidableEq F] {ingress : DecodedIngress}

def charge (accepted : AcceptedInstall deployment profile ambient durable ingress) :
    ResourceCost.Charge
  | .incidences => 1
  | .turnBytes => ingress.bytes.length
  | .memoryTouches => (writes accepted.prepared).length + (readGuards accepted.prepared).length
  | .storageBytes => DeployedCharge.storageCharge durable.snapshot
      (writes accepted.prepared)
      (event deployment.domain profile.semantics ingress)
  | .witnessBytes => ingress.ingress.sponsorEnvelope.length +
      (ingress.ingress.custodianCosign.map List.length).getD 0
  | .proofWork => 2
  | .feeDebit | .networkBytes | .sideEffectCount | .leaseByteBlocks => 0

def intent (accepted : AcceptedInstall deployment profile ambient durable ingress) :
    DataIntent rootBytes where
  transactionId := transactionId deployment.domain profile.semantics ingress
  subject := some ingress.command.sponsor
  writes := writes accepted.prepared
  readGuards := readGuards accepted.prepared
  nullifiers := [nullifier deployment.domain profile.semantics ingress]
  exactCharge := (Minidregg.Theory.ResourceCost.Charge.materialize (charge accepted)).toCharge
  event := event deployment.domain profile.semantics ingress
  postRootsBound := writes_roots_bound accepted.prepared
  guardsReadOnly := readGuards_readonly accepted.prepared accepted.physical

/-- The one cell an accepted install writes is the platform cell. -/
theorem intent_writes_platform_cell (accepted : AcceptedInstall deployment profile ambient durable ingress) :
    (intent accepted).writes.map DataWrite.cellId = [PlatformCellDomain.cellIdOf deployment] := rfl

structure Receipt where
  transactionId : Digest
  eventId : Digest
  deriving DecidableEq, Repr

def receipt (domain semantics : Digest) (ingress : DecodedIngress) : Receipt :=
  ⟨transactionId domain semantics ingress, (event domain semantics ingress).eventId⟩

def replay (domain semantics : Digest) (durable : Durable) (ingress : DecodedIngress) :
    Option (Except Unit Receipt) :=
  match DurableCommitProtocol.Snapshot.lookupRecorded
      (transactionId domain semantics ingress) durable.snapshot.model.journal with
  | none => none
  | some recorded =>
    if recorded.transactionId = transactionId domain semantics ingress ∧
        recorded.event.event = event domain semantics ingress ∧
        recorded.nullifiers = [nullifier domain semantics ingress] then
      some (.ok (receipt domain semantics ingress))
    else some (.error ())

inductive Result where
  | confirmed (kind : DurableReceiverIO.Confirmation) (receipt : Receipt)
  | rejected (reason : Reject)
  | transactionConflict
  | durableRejected (reason : DurableDataIntent.RejectReason)
  | contention
  | unavailable (detail : String)
  | uncertain (detail : String)

def receiveLoaded (deployment : Deployment) (profile : CanonicalRuntimeProfile.Profile F)
    (ambient : Ambient) (native : CredentialSignatureIO.NativeConfig)
    (transport : DurableReceiverIO.Transport) (durable : Durable)
    (bytes : List UInt8) : IO Result := do
  let some ingress := decodeIngress bytes
    | return .rejected .malformedIngress
  match replay deployment.domain profile.semantics durable ingress with
  | some (.ok prior) => return .confirmed .replayed prior
  | some (.error _) => return .transactionConflict
  | none =>
    match ← admitDecodedNative deployment profile ambient durable native ingress with
    | .error reason => return .rejected reason
    | .ok accepted =>
      match ← DurableReceiverIO.receiveLoaded transport rootBytes durable (intent accepted) with
      | .confirmed kind _ =>
          return .confirmed kind (receipt deployment.domain profile.semantics ingress)
      | .rejected reason => return .durableRejected reason
      | .contention => return .contention
      | .unavailable detail => return .unavailable detail
      | .uncertain detail => return .uncertain detail

#assert_axioms command_roundtrip
#assert_axioms commandCodec_injective
#assert_axioms custodianCheck_congr
#assert_axioms admitsObserved_decides
#assert_axioms Moment.frame_effectsDigest
#assert_axioms platform_written_only_by_install
#assert_axioms receiverDecides
#assert_axioms signed_command_admitted
#assert_axioms unsigned_refused
#assert_axioms delegate_refused
#assert_axioms controller_install_admitted

end Minidregg.Kernel.PlatformInstallReceiver
