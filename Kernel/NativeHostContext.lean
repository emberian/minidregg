/-
Shared source-owned host configuration and structural validation. Semantic
history verification imports this module; ordinary host APIs import the verifier.
There is one profile, one world-root commitment, and one validation path.
-/
module

public import Compiler.NativeHostCodec
public import Kernel.PlatformCellLayout
public import Kernel.PlatformCellDomain
public import Compiler.GenericSimplexSourceAnchor
public import Compiler.GrainResourceBirthController
public import Compiler.JointControlFrame
public import Kernel.ProtectedContentGate
public import Kernel.ObjectiveActivityGate
public import Compiler.NativeInvocationProfile
public import Compiler.GenericSimplexCodec

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
import all Init.Util

@[expose] public section

namespace Minidregg.Kernel.NativeHost

open Minidregg.Theory
open Minidregg.Theory.CellRegistry
open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.ResourceBirth
open Minidregg.Compiler
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Compiler.NativeHostCodec

set_option autoImplicit false

abbrev Durable := DurableReceiverIO.Loaded ResourceBirthCodec.rootBytes

/-- Operator-pinned identity for the local fn application gateway. The current
resource law is checked separately against this pin before new fn work. -/
structure FnGatewayPin where
  application : List UInt8
  subject : SubjectId
  target : Nat
  capability : CapabilityId
  policyAddress : Digest
  deriving DecidableEq, Repr

/-- Permission micro-units charged to a previously reserved tool grain for a
composite birth. This is independent of the conserved Book creation tariff. The structure
is the platform record's (`Kernel.PlatformCellLayout`), so the record and the runtime
parameters carry one type. -/
abbrev GrainBirthTariffPin := Kernel.PlatformCellLayout.GrainBirthTariffPin

/-- C17 (measured 2026-10-01 on persvati): the referee adds about 0.66 µs per admitted
step, so 1 s at about 1.5e6 steps; rounded down. -/
def defaultNockFSync : Nat := 1000000

/-- The source-owned configuration fields, separated so the derived profile's
exactness can be stated before the cached configuration itself. -/
structure Config.Inputs where
  deployment : CanonicalCellRegistry.Deployment
  federation : FederationId
  template : CanonicalRuntimeProfile.FactoryTemplate
  tariff : CreationTariff
  genesisHeight : Nat
  expectedSeed : Digest
  storage : DurableReceiverIO.NativeConfig
  signature : CredentialSignatureIO.NativeConfig
  fnGateway : Option FnGatewayPin := none
  grainBirthTariff : Option GrainBirthTariffPin := none
  /-- Public Ed25519 key of the separately controlled physical host custodian.
  Absence preserves the legacy profile and disables checked completion. -/
  completionCustodianKey : Option (List UInt8) := none
  /-- The operator's synchronous budget for a run claim, in Lean Nock steps
  (C17's measured `F_sync`). A run-claimed invocation above it is refused
  `overSyncBudget` before the referee re-executes it. Operator-local admission
  policy, not runtime semantics: it is not in `runtimeParameters`, and a
  history admitted under a larger budget replays unchanged. -/
  nockFSync : Nat := defaultNockFSync
  /-- Compiled-in evaluators this operator disabled (K-EVAL); committed in the profile's
  semantics, so every node of a deployment must agree. -/
  disabledEvaluators : List Digest := []
  /-- Source-owned joint control resource. Enabling changes the runtime pin;
  the physical cell/atom/schema are not selected by a submitted operation. -/
  jointControl : Option JointControlFrame.Pin := none
  /-- Separate source-owned Activity facet; no controller exception drops another gate. -/
  activityControl : Option ContentControlFrame.Pin := none
  /-- Live operator bound, excluded from source semantics and historical replay policy. -/
  activityTickLimit : Nat := 100000
  /-- Common source-log epoch/roster/keys/base, pinned by deployment semantics.
  A certificate never supplies its own verification context. -/
  jointConsensus : Option GenericSimplexCodec.Context := none
  /-- Explicit deployment-selected invocation families. Appended to the Config
  layout; absence retains the complete historical parameter preimage. -/
  invocationBindings : Option (List (NativeInvocationStatement.Route × List UInt8)) := none

/-- This manifest enters runtime semantics. The seed commitment is separate
because the genesis's source policies themselves contain that semantics. -/
def Config.Inputs.runtimeParameters (config : Config.Inputs) : List UInt8 :=
  "DREGG.NATIVE-HOST.PARAMETERS/v2".toUTF8.toList ++
  (StreamCodec.list StreamCodec.nat).encode
    [config.deployment.domain.value, config.deployment.factoryId,
     config.deployment.resourceBookId, config.deployment.authorityCellId,
     config.federation.value, config.genesisHeight, config.tariff.base,
     config.tariff.perBirth, config.tariff.perGrant, config.tariff.perInitialPayloadByte,
     config.tariff.collector, config.tariff.asset] ++
  (match config.grainBirthTariff with
  | none => []
  | some tariff =>
      "DREGG/NATIVE-HOST/GRAIN-BIRTH-TARIFF/v2".toUTF8.toList ++
        (StreamCodec.product StreamCodec.nat StreamCodec.nat).encode
          (tariff.base, tariff.perBirth)) ++
  (match config.completionCustodianKey with
  | none => []
  | some key =>
      "DREGG/NATIVE-HOST/COMPLETION-CUSTODIAN/v2".toUTF8.toList ++
        bytesStream.encode key) ++
  (match config.jointControl with
  | none => []
  | some pin => "DREGG/NATIVE-HOST/JOINT-CONTROL/v3".toUTF8.toList ++
      JointControlFrame.pinStream.encode pin) ++
  (match config.activityControl with
  | none => []
  | some pin => "DREGG/NATIVE-HOST/ACTIVITY-CONTROL/v2".toUTF8.toList ++
      ContentControlFrame.pinStream.encode pin) ++
  (match config.jointConsensus with
  | none => []
  | some context => "DREGG/NATIVE-HOST/SOURCE-CONSENSUS/v2".toUTF8.toList ++
      GenericSimplexCodec.contextStream.encode { context with instanceBytes := [] })

/-- Registration wraps the ENTIRE legacy manifest. Submitted commands never
select this policy, and registration grants no current source authority. -/
def Config.Inputs.invocationParameters (config : Config.Inputs) : List UInt8 :=
  match config.invocationBindings with
  | none => config.runtimeParameters
  | some bindings => NativeInvocationProfile.encode
      ⟨config.runtimeParameters, config.activityControl, bindings⟩

/-- The specification profile, retained separately from its compiled cache accessor. -/
def Config.Inputs.profile (config : Config.Inputs) :=
  NativeHostProfile.profile config.template config.invocationParameters config.disabledEvaluators

/-- A configuration carries its derived profile, deferred and computed at most
once per configuration value. `profileExact` binds it to all source inputs. -/
structure Config extends Config.Inputs where
  profileCache : Thunk (CanonicalRuntimeProfile.Profile NativeHostProfile.Field)
  profileExact : profileCache.get = toInputs.profile

/-- Construct a configuration and its exact profile cache together. -/
def Config.ofInputs (inputs : Config.Inputs) : Config :=
  let profile := Thunk.mk fun _ => inputs.profile
  ⟨inputs, profile, rfl⟩

def Config.grainBirthTariffValue (config : Config) :
    Except String GrainResourceBirthController.Tariff := do
  let some pinned := config.grainBirthTariff
    | throw "grain-backed birth tariff is not enabled"
  if positive : 0 < pinned.base then
    pure ⟨pinned.base, pinned.perBirth, positive⟩
  else throw "grain-backed birth tariff base must be positive"

def Config.runtimeParameters (config : Config) : List UInt8 :=
  config.toInputs.runtimeParameters

/-- Disabling the new mode preserves the complete pre-existing parameter
preimage, hence its legacy semantics/profile and genesis interpretation. -/
theorem Config.runtimeParameters_withoutOptionalModes (config : Config) :
    (Config.ofInputs { config.toInputs with grainBirthTariff := none, completionCustodianKey := none, jointControl := none, activityControl := none, jointConsensus := none }).runtimeParameters =
      "DREGG.NATIVE-HOST.PARAMETERS/v2".toUTF8.toList ++
        (StreamCodec.list StreamCodec.nat).encode
          [config.deployment.domain.value, config.deployment.factoryId,
           config.deployment.resourceBookId, config.deployment.authorityCellId,
           config.federation.value, config.genesisHeight, config.tariff.base,
           config.tariff.perBirth, config.tariff.perGrant,
           config.tariff.perInitialPayloadByte, config.tariff.collector,
           config.tariff.asset] := by
  simp [Config.runtimeParameters, Config.Inputs.runtimeParameters, Config.ofInputs]

def Config.invocationParameters (config : Config) : List UInt8 :=
  config.toInputs.invocationParameters

@[simp] theorem Config.invocationParameters_legacy (config : Config)
    (legacy : config.invocationBindings = none) :
    config.invocationParameters = config.runtimeParameters := by
  simp [Config.invocationParameters, Config.Inputs.invocationParameters,
    Config.runtimeParameters, legacy]

#assert_axioms Config.invocationParameters_legacy

def Config.profile (config : Config) :=
  config.toInputs.profile

/-- The profile as compiled code reads it: derived on the first read of this
configuration value and never again. -/
def Config.profileCached (config : Config) :=
  config.profileCache.get

@[csimp] theorem Config.profile_eq_profileCached :
    @Config.profile = @Config.profileCached := by
  funext config
  exact config.profileExact.symm

#assert_axioms Config.profile_eq_profileCached

theorem Config.profile_restorage (config : Config) (storage : DurableReceiverIO.NativeConfig) :
    { config with storage }.profile = config.profile := rfl

attribute [local irreducible] Config.profile CanonicalRuntimeProfile.Profile.compilerProfile

private def chargeTupleBEq (left right : DurableReceiverCodec.ChargeTuple) : Bool :=
  left.1 == right.1 && left.2.1 == right.2.1 && left.2.2.1 == right.2.2.1 &&
    left.2.2.2.1 == right.2.2.2.1 && left.2.2.2.2.1 == right.2.2.2.2.1 &&
    left.2.2.2.2.2.1 == right.2.2.2.2.2.1 && left.2.2.2.2.2.2.1 == right.2.2.2.2.2.2.1 &&
    left.2.2.2.2.2.2.2.1 == right.2.2.2.2.2.2.2.1 &&
    left.2.2.2.2.2.2.2.2.1 == right.2.2.2.2.2.2.2.2.1 &&
    left.2.2.2.2.2.2.2.2.2 == right.2.2.2.2.2.2.2.2.2

private theorem chargeTupleBEq_eq (left right : DurableReceiverCodec.ChargeTuple) :
    chargeTupleBEq left right = true ↔ left = right := by
  simp [chargeTupleBEq, Prod.ext_iff, and_assoc]

local instance : DecidableEq DurableReceiverCodec.ChargeTuple := fun left right =>
  decidable_of_iff (chargeTupleBEq left right = true) (chargeTupleBEq_eq left right)

/-- Seeds compare by their finite canonical contents, after object identity:
a session's next image retains the same seed object, so that path never encodes
the genesis cells merely to compare them. -/
instance : DecidableEq DurableReceiver.Seed := fun left right =>
  withPtrEqDecEq left right fun _ =>
    decidable_of_iff
      ((left.absentBytes, left.cells, DurableReceiverCodec.chargeTuple left.available) =
        (right.absentBytes, right.cells, DurableReceiverCodec.chargeTuple right.available))
      ⟨fun same => by
        cases left with
        | mk absentBytes cells available =>
          cases right with
          | mk otherAbsent otherCells otherAvailable =>
            simp only [DurableReceiver.Seed.mk.injEq, Prod.mk.injEq] at same ⊢
            refine ⟨same.1, same.2.1, ?_⟩
            have charges := congrArg DurableReceiverCodec.chargeOfTuple same.2.2
            simpa only [DurableReceiverCodec.chargeOfTuple_tuple] using charges,
       fun same => congrArg (fun seed : DurableReceiver.Seed =>
         (seed.absentBytes, seed.cells, DurableReceiverCodec.chargeTuple seed.available)) same⟩

def seedIdentity (seed : DurableReceiver.Seed) : Digest :=
  (Sp800185Cshake256.hash "DREGG.NATIVE-HOST.GENESIS/v1".toUTF8.toList
    (DurableReceiverCodec.seedStream.encode seed)).digest

/-- A runtime-optional exactness proof. `PLift` keeps the proposition in `Type`;
the proof itself remains erasable after the some/none decision is made. -/
abbrev ExactEvidence (claim : Prop) := Option (PLift claim)

/-- The world root of an image under this deployment (`NativeHostCodec.worldRoot`). -/
def worldRoot (config : Config) (image : DurableReceiver.Image) : Digest :=
  NativeHostCodec.worldRoot config.deployment.domain config.profile.semantics image

/-- The log chain's start for this deployment: C1's genesis log root, binding
domain, semantics and seed. The Store's MAC chain and the world root's system
slot are this one chain. -/
def Config.logStart (config : Config) (seed : DurableReceiver.Seed) : Digest :=
  NativeHostCodec.logRoot0 config.deployment.domain config.profile.semantics seed

theorem Config.logStart_restorage (config : Config) (storage : DurableReceiverIO.NativeConfig)
    (seed : DurableReceiver.Seed) :
    { config with storage }.logStart seed = config.logStart seed := by
  unfold Config.logStart
  rw [Config.profile_restorage]

/-- The deployment's system cell (`Kernel.SystemCell.physicalId`). -/
def Config.systemCell (config : Config) : Minidregg.Kernel.DurableDataIntent.CellId :=
  ⟨Minidregg.Kernel.SystemCell.physicalId config.deployment.domain⟩

/-- Private receiving adapters select a facet only AFTER constructing their
actual typed source-admission token. This discriminator is never decoded from
network or client input; this helper alone grants no exception authority. -/
inductive ControlFacet
  | joint
  | activity
  /-- The object kernel's own typed turns (`ObjectiveActivityReceiver.Accepted`,
  `SeatReceiver.Accepted`): the one facet that may write the protected
  coordinates. -/
  | objectKernel
  deriving DecidableEq

/-- Whole-cell roots are shared protection coordinates. This first concrete
composition requires separate physical cells; overlapping facets refuse all
source transitions rather than allowing an exception to erase another law. -/
def Config.controlLayoutValid (config : Config) : Bool :=
  match config.jointControl, config.activityControl with
  | some joint, some activity => decide (joint.cell ≠ activity.cell)
  | _, _ => true

/-- Total aggregation: a typed own-facet exception retains every OTHER facet.
Ordinary receiving uses none and checks both laws. The caller must still check
the precise private current-admitted own record and predecessor. -/
def Config.sourceGate (config : Config) (own : Option ControlFacet)
    {rootBytes : List UInt8 → Digest} (snapshot : DurableDataIntent.DataSnapshot rootBytes)
    (intent : DurableDataIntent.DataIntent rootBytes) :
    Except DurableDataIntent.RejectReason Unit := do
  if !config.controlLayoutValid then throw (.durable .transactionConflict)
  -- The protected coordinates: only the object kernel's own facet writes them.
  if own ≠ some .objectKernel then ObjectiveActivityGate.ordinaryGate intent
  match config.jointControl with
  | none => pure ()
  | some pin =>
      if own = some .joint then pure () else
        match JointControlFrame.ordinaryGate config.deployment.domain pin snapshot intent with
        | .ok () => pure ()
        | .error _ => throw (.durable .transactionConflict)
  match config.activityControl with
  | none => pure ()
  | some pin =>
      if own = some .activity then pure () else
        ProtectedContentGate.ordinaryGate pin snapshot intent

def Config.otherFacetGate (config : Config) (own : ControlFacet)
    {rootBytes : List UInt8 → Digest} (snapshot : DurableDataIntent.DataSnapshot rootBytes)
    (intent : DurableDataIntent.DataIntent rootBytes) :
    Except DurableDataIntent.RejectReason Unit :=
  config.sourceGate (some own) snapshot intent

/-- The identity the Store's durable anchor is enrolled and read under. The one
spelling: the Host's transport uses it, and `describe` prints it
(`storeAnchorIdentity`) so a script reading the Store never re-derives it. -/
def Config.anchorIdentity (config : Config) : String :=
  s!"domain:{config.deployment.domain.value};semantics:{config.profile.semantics.value};seed:{config.expectedSeed.value}"

/-- **Every facet but the kernel activity's own runs the ordinary gate.** A
source transition any other facet admits writes no protected activity
coordinate (`ObjectiveActivityGate.ordinaryGate`). -/
theorem Config.sourceGate_ordinary (config : Config) {own : Option ControlFacet}
    {rootBytes : List UInt8 → Digest}
    {snapshot : DurableDataIntent.DataSnapshot rootBytes} {intent : DurableDataIntent.DataIntent rootBytes}
    (foreign : own ≠ some .objectKernel)
    (admitted : config.sourceGate own snapshot intent = .ok ()) :
    ObjectiveActivityGate.ordinaryGate intent = .ok () := by
  cases layout : config.controlLayoutValid with
  | false =>
      have refused : config.sourceGate own snapshot intent = .error (.durable .transactionConflict) := by
        simp [Config.sourceGate, layout]
      rw [refused] at admitted
      cases admitted
  | true =>
      cases gate : ObjectiveActivityGate.ordinaryGate intent with
      | error reason =>
          simp [Config.sourceGate, layout, foreign, gate, bind, Except.bind, pure, Except.pure] at admitted
      | ok value => cases value; rfl

/-- **A write to a protected activity cell from any other facet is refused by
name**: the source gate answers `protectedWrite`, naming a protected cell the
intent writes. -/
theorem Config.sourceGate_refuses_protected (config : Config) {own : Option ControlFacet}
    {rootBytes : List UInt8 → Digest}
    {snapshot : DurableDataIntent.DataSnapshot rootBytes} {intent : DurableDataIntent.DataIntent rootBytes}
    (foreign : own ≠ some .objectKernel) (layout : config.controlLayoutValid = true)
    {write : DurableDataIntent.DataWrite} (writes : write ∈ intent.writes)
    (isProtected : ObjectiveActivityGate.Protected write.cellId) :
    ∃ cell, config.sourceGate own snapshot intent = .error (.protectedWrite cell) ∧
      ObjectiveActivityGate.Protected cell := by
  obtain ⟨cell, refused, protectedCell, _⟩ := ObjectiveActivityGate.ordinaryGate_refuses writes isProtected
  refine ⟨cell, ?_, protectedCell⟩
  simp [Config.sourceGate, layout, foreign, refused, bind, Except.bind, pure, Except.pure]

/-- **The widened physical-post law reaches only the kernel activity.** Every
write a source transition of any other facet admits that obeys
`PhysicalPostLaw` is a live cell under its registry law: the retired image
`PhysicalPostLaw` admits at protected coordinates is not available to them
(`ObjectiveActivityGate.ordinary_physicalPostLaw_live`). -/
theorem Config.sourceGate_physicalPostLaw_live (config : Config) {own : Option ControlFacet}
    {rootBytes : List UInt8 → Digest}
    {snapshot : DurableDataIntent.DataSnapshot rootBytes} {intent : DurableDataIntent.DataIntent rootBytes}
    (foreign : own ≠ some .objectKernel)
    (admitted : config.sourceGate own snapshot intent = .ok ())
    {deployment : Minidregg.Compiler.CanonicalCellRegistry.Deployment}
    {write : DurableDataIntent.DataWrite} (member : write ∈ intent.writes)
    (law : Minidregg.Kernel.ResourceBirthController.Concrete.PhysicalPostLaw deployment write) :
    ∃ cell, (Minidregg.Compiler.ResourceBirthCodec.LifecycleImage.codec
          Minidregg.Kernel.ResourceBirthController.Concrete.Registry).decode
        write.canonicalPostBytes = some (.live cell) ∧
      Minidregg.Compiler.CanonicalCellRegistry.CellLaw deployment write.cellId.value cell :=
  ObjectiveActivityGate.ordinary_physicalPostLaw_live (config.sourceGate_ordinary foreign admitted) member law

#assert_axioms Config.sourceGate_ordinary
#assert_axioms Config.sourceGate_refuses_protected
#assert_axioms Config.sourceGate_physicalPostLaw_live

/-- The Store transport keeps the actual system-cell tail law and checks every
protected facet before physical append. -/
def Config.physicalTransport (config : Config) : DurableReceiverIO.Transport :=
  let storage := { config.storage with anchorIdentity := config.anchorIdentity }
  { storage.transport config.logStart config.systemCell with sourceGate := config.sourceGate none }

/-- In an agreed domain the ordinary receiving loop must propose its source
transition. It cannot secretly append an unordered local application record.
Typed ordered receivers retain physicalTransport and its unchanged CAS/readback. -/
def Config.transport (config : Config) : DurableReceiverIO.Transport :=
  if config.jointConsensus.isSome then
    { config.physicalTransport with append := fun _ _ _ => pure .conflict }
  else config.physicalTransport

/-- A scratch Store for a portable image (a foreign accepted prefix verified with
no Store of its own): this deployment's config with its Store moved into
`directory`, which the caller owns and removes, and a fresh 32-byte MAC key written
there (mode 0600). Its `physicalTransport` names an EMPTY Store, the transport
`DurableHistoryStore.scratchReader` writes the image into. -/
def Config.scratch (config : Config) (directory : System.FilePath) : IO Config := do
  IO.FS.createDirAll directory
  let key := directory / "key"
  IO.FS.writeBinFile key (← IO.getRandomBytes 32)
  IO.setAccessRights key { user := { read := true, write := true } }
  pure { config with storage := { config.storage with root := directory / "store", key := key } }

theorem Config.transport_systemCell (config : Config) :
    config.transport.systemCell = some config.systemCell := by
  unfold Config.transport
  split <;> rfl

theorem Config.physicalTransport_systemCell (config : Config) :
    config.physicalTransport.systemCell = some config.systemCell := rfl

/-- The deployment's ordinary transport judges through `sourceGate none`, a
facet that is not the object kernel's: only `kernelTransport` is exempt. -/
theorem Config.transport_sourceGate (config : Config) {rootBytes : List UInt8 → Digest}
    (snapshot : DurableDataIntent.DataSnapshot rootBytes) (intent : DurableDataIntent.DataIntent rootBytes) :
    config.transport.sourceGate snapshot intent = config.sourceGate none snapshot intent := by
  unfold Config.transport Config.physicalTransport
  split <;> rfl

#assert_axioms Config.transport_sourceGate

/-- The transport of the object kernel's own typed turns (activity and seat): the
deployment's transport with the `objectKernel` facet, so the protected
coordinates may be written, and every other facet's law still applies. -/
def Config.kernelTransport (config : Config) : DurableReceiverIO.Transport :=
  { config.transport with sourceGate := config.sourceGate (some .objectKernel) }

theorem Config.kernelTransport_systemCell (config : Config) :
    config.kernelTransport.systemCell = some config.systemCell :=
  config.transport_systemCell

def logicalHeight (config : Config) (durable : Durable) : Height :=
  config.genesisHeight + durable.height

theorem logicalHeight_exact (config : Config) (durable : Durable) :
    logicalHeight config durable = config.genesisHeight + durable.image.accepted.length := by
  rw [logicalHeight, DurableReceiverIO.Loaded.height_eq]

/-- Every policy whose revision the authority cell records has a complete
current head, and that head's address loads a source cell of the same policy,
the same revision and this runtime's semantics. -/
def policySourced (config : Config) (directory : Directory Nat CanonicalCellRegistry.registry)
    (logical : Store.Store CredentialAuthorityState.layout) :
    Store.Address CredentialAuthorityState.layout → Bool
  | ⟨.policyRevision, identifier⟩ =>
      match CredentialAuthorityDomain.headAt logical identifier with
      | none => false
      | some head =>
          match CanonicalCellRegistry.loadPolicySource config.deployment.domain directory head.address with
          | none => false
          | some source => decide (source.record.policyId = identifier ∧
              source.record.version = head.version ∧ source.record.semantics = config.profile.semantics)
  | _ => true

def policiesSourced (config : Config) (directory : Directory Nat CanonicalCellRegistry.registry)
    (logical : Store.Store CredentialAuthorityState.layout) : Bool :=
  decide (∀ address ∈ logical.support, policySourced config directory logical address = true)

/-- `policySourced` against a given semantics digest. The profile's digest is a
hash of the runtime manifest, recomputed at every call, so `policiesSourced`
computes it once (`policiesSourced_eq_once`) rather than once per recorded policy. -/
def policySourcedAt (config : Config) (semantics : Digest)
    (directory : Directory Nat CanonicalCellRegistry.registry)
    (logical : Store.Store CredentialAuthorityState.layout) :
    Store.Address CredentialAuthorityState.layout → Bool
  | ⟨.policyRevision, identifier⟩ =>
      match CredentialAuthorityDomain.headAt logical identifier with
      | none => false
      | some head =>
          match CanonicalCellRegistry.loadPolicySource config.deployment.domain directory head.address with
          | none => false
          | some source => decide (source.record.policyId = identifier ∧
              source.record.version = head.version ∧ source.record.semantics = semantics)
  | _ => true

theorem policySourced_eq_at (config : Config) (directory : Directory Nat CanonicalCellRegistry.registry)
    (logical : Store.Store CredentialAuthorityState.layout) :
    policySourced config directory logical =
      policySourcedAt config config.profile.semantics directory logical := by
  funext address
  rcases address with ⟨kind, identifier⟩
  cases kind <;> rfl

@[noinline] def policiesSourcedAt (config : Config) (semantics : Digest)
    (directory : Directory Nat CanonicalCellRegistry.registry)
    (logical : Store.Store CredentialAuthorityState.layout) : Bool :=
  decide (∀ address ∈ logical.support, policySourcedAt config semantics directory logical address = true)

def policiesSourcedOnce (config : Config) (directory : Directory Nat CanonicalCellRegistry.registry)
    (logical : Store.Store CredentialAuthorityState.layout) : Bool :=
  policiesSourcedAt config config.profile.semantics directory logical

@[csimp] theorem policiesSourced_eq_once : @policiesSourced = @policiesSourcedOnce := by
  funext config directory logical
  unfold policiesSourced policiesSourcedOnce policiesSourcedAt
  rw [policySourced_eq_at]

#assert_axioms policiesSourced_eq_once

/-- One stored cell obeys its role and domain law (vacuous for an absent slot). -/
def cellLawful (config : Config) (directory : Directory Nat CanonicalCellRegistry.registry)
    (identifier : Digest) : Bool :=
  match directory.slots identifier.value with
  | .absent => true
  | .present cell => CanonicalCellRegistry.cellCheck config.deployment identifier.value cell

/-- Every enumerable cell of the image obeys its law. -/
def cellsLawful (config : Config) (durable : Durable)
    (directory : Directory Nat CanonicalCellRegistry.registry) : Bool :=
  durable.image.cellIds.all (cellLawful config directory)

/-- `cellsLawful` over the loaded image's cached enumeration (`Loaded.cellIds`). -/
def cellsLawfulCached (config : Config) (durable : Durable)
    (directory : Directory Nat CanonicalCellRegistry.registry) : Bool :=
  durable.cellIds.all (cellLawful config directory)

/-- **Refinement, compiled**: the host evaluates the cached enumeration
wherever it evaluates `cellsLawful`. -/
@[csimp] theorem cellsLawful_eq_cached : @cellsLawful = @cellsLawfulCached := by
  funext config durable directory
  unfold cellsLawful cellsLawfulCached
  rw [DurableReceiverIO.Loaded.cellIds_eq]

structure Opened (config : Config) where
  private mk ::
  durable : Durable
  directory : CredentialAuthorityDomainReceiver.LoadedDirectory durable
  authority : CredentialAuthorityDomainReceiver.Loaded config.deployment durable.snapshot
  pins : FactoryPins
  /-- The cell-law check this image passed; a later image of the same session
  re-checks only the cells whose bytes moved (`cellsLawfulFrom`). -/
  lawful : cellsLawful config durable directory.directory = true
  /-- The two whole-genesis checks this image passed. A later image with the
  same seed and log start reuses these instead of encoding and hashing it again. -/
  seedExact : seedIdentity durable.image.seed = config.expectedSeed
  logStartExact : durable.logStart = config.logStart durable.image.seed

/-- The same opened image under a config that differs only in its Store paths:
nothing an `Opened` holds depends on `storage`. (`Host.DryRun` uses it to state
that a dry run never names the Store's writers.) -/
def Opened.restorage {config : Config} (opened : Opened config)
    (storage : DurableReceiverIO.NativeConfig) : Opened { config with storage } :=
  { durable := opened.durable
    directory := opened.directory
    authority := opened.authority
    pins := opened.pins
    lawful := opened.lawful
    seedExact := by
      change seedIdentity opened.durable.image.seed = config.expectedSeed
      exact opened.seedExact
    logStartExact := by
      rw [Config.logStart_restorage]
      exact opened.logStartExact }

def need {α : Type} (detail : String) : Option α → Except String α
  | none => .error detail
  | some value => .ok value

def check (condition : Bool) (detail : String) : Except String Unit :=
  if condition then .ok () else .error detail

/-- Everything `validateLoaded` derives from one loaded image. -/
structure Validated (config : Config) (durable : Durable) where
  directory : CredentialAuthorityDomainReceiver.LoadedDirectory durable
  authority : CredentialAuthorityDomainReceiver.Loaded config.deployment durable.snapshot
  pins : FactoryPins
  lawful : cellsLawful config durable directory.directory = true
  seedExact : seedIdentity durable.image.seed = config.expectedSeed
  logStartExact : durable.logStart = config.logStart durable.image.seed

/-- The creation tariff an opened state's factory pins carry: the platform record's. Where
the image holds no platform record, the config's genesis tariff stands in, and every
ordinary birth on that image is refused `platformUnavailable`
(`ResourceBirthPolicyController.Concrete.preparePending`), so the stand-in prices nothing. -/
def pinnedTariff (config : Config) (platform? : Option PlatformCellLayout.Platform) :
    CreationTariff :=
  match platform? with
  | some record => record.creation
  | none => config.tariff

private def validateGenesisPrefix (config : Config) (seed : DurableReceiver.Seed)
    (seedExact? : ExactEvidence (seedIdentity seed = config.expectedSeed)) : Except String Unit := do
  if config.grainBirthTariff.isSome then
    let _ ← config.grainBirthTariffValue
  if let some key := config.completionCustodianKey then
    check (decide (key.length = 32)) "physical completion custodian key must be 32 bytes"
  check (decide config.deployment.Valid) "invalid deployment role identities"
  match seedExact? with
  | some _ => pure ()
  | none => check (seedIdentity seed == config.expectedSeed) "genesis identity mismatch"

private def validateLogChain (config : Config) (seed : DurableReceiver.Seed) (logStart : Digest)
    (logStartExact? : ExactEvidence (logStart = config.logStart seed)) : Except String Unit := do
  if let some expected := config.jointConsensus then
    check expected.wellFormed "consensus committee is not well formed"
    check (expected.scope == Tower256ConcreteBackend.digestStream.encode config.deployment.domain)
      "consensus scope differs from native deployment"
    check (expected.instanceBytes ==
      GenericSimplexSourceAnchor.anchorBytes config.genesisHeight seed)
      "consensus source anchor differs from exact Store genesis"
  match logStartExact? with
  | some _ => pure ()
  | none => check (logStart == config.logStart seed) "log chain not rooted at this deployment's genesis"

/-- The checks every opened state passes, over its seed, its log start, its
decoded directory, its authority cell's logical store and its cell-law verdict
(`none` where the directory did not decode). Shared by the full shape
(`validatePartsWith`) and the served state (`NativeHostServed.validateServed`):
the two run these checks with the same refusals in the same order. Exact prior
evidence may replace either genesis check (`validateChecks_withExact_eq`). -/
def validateChecks (config : Config) (seed : DurableReceiver.Seed) (logStart : Digest)
    (directory? : Option (Directory Nat CanonicalCellRegistry.registry))
    (logical? : Option (Store.Store CredentialAuthorityState.layout)) (lawful? : Option Bool)
    (platform? : Option PlatformCellLayout.Platform)
    (seedExact? : ExactEvidence (seedIdentity seed = config.expectedSeed) := none)
    (logStartExact? : ExactEvidence (logStart = config.logStart seed) := none) :
    Except String FactoryPins := do
  let _ ← validateGenesisPrefix config seed seedExact?
  let _ ← validateLogChain config seed logStart logStartExact?
  let directory ← need "noncanonical native directory" directory?
  let logical ← need "complete deployment authority unavailable" logical?
  let lawful ← need "noncanonical native directory" lawful?
  check lawful "native cell role or domain law refused"
  check (policiesSourced config directory logical) "selected policy source/profile mismatch"
  let factoryHead ← need "factory policy head unavailable"
    (CredentialAuthorityDomain.headAt logical ⟨config.deployment.factoryId⟩)
  pure
    { factory := ⟨config.deployment.factoryId⟩
      domain := config.deployment.domain
      semantics := config.profile.semantics
      federation := config.federation
      policyId := ⟨config.deployment.factoryId⟩
      policyAddress := factoryHead.address
      tariff := pinnedTariff config platform? }

/-- Supplying exact evidence for either genesis check skips only a check that
was already guaranteed to succeed; every other check and refusal is unchanged. -/
theorem validateChecks_withExact_eq (config : Config) (seed : DurableReceiver.Seed)
    (logStart : Digest) (directory? : Option (Directory Nat CanonicalCellRegistry.registry))
    (logical? : Option (Store.Store CredentialAuthorityState.layout)) (lawful? : Option Bool)
    (platform? : Option PlatformCellLayout.Platform)
    (seedExact? : ExactEvidence (seedIdentity seed = config.expectedSeed))
    (logStartExact? : ExactEvidence (logStart = config.logStart seed)) :
    validateChecks config seed logStart directory? logical? lawful? platform?
        seedExact? logStartExact? =
      validateChecks config seed logStart directory? logical? lawful? platform? := by
  cases seedExact? with
  | none =>
      cases logStartExact? with
      | none => rfl
      | some logStartExact =>
          obtain ⟨sameStart⟩ := logStartExact
          simp only [validateChecks, validateGenesisPrefix, validateLogChain, sameStart, beq_self_eq_true, check, if_true, pure, Except.pure]
  | some seedExact =>
      obtain ⟨sameSeed⟩ := seedExact
      cases logStartExact? with
      | none =>
          simp only [validateChecks, validateGenesisPrefix, validateLogChain, sameSeed, beq_self_eq_true, check, if_true, pure, Except.pure]
      | some logStartExact =>
          obtain ⟨sameStart⟩ := logStartExact
          simp only [validateChecks, validateGenesisPrefix, validateLogChain, sameSeed, sameStart, beq_self_eq_true, check, if_true, pure, Except.pure]

private theorem except_bind_ok {α β : Type} {value : Except String α}
    {continuation : α → Except String β} {result : β}
    (validated : (value >>= continuation) = .ok result) :
    ∃ middle, value = .ok middle ∧ continuation middle = .ok result := by
  cases value with
  | error detail => simp [bind, Except.bind] at validated
  | ok middle => exact ⟨middle, rfl, validated⟩

private theorem validateGenesisPrefix_exact {config : Config} {seed : DurableReceiver.Seed}
    {seedExact? : ExactEvidence (seedIdentity seed = config.expectedSeed)}
    (validated : validateGenesisPrefix config seed seedExact? = .ok ()) :
    seedIdentity seed = config.expectedSeed := by
  cases seedExact? with
  | some evidence => exact evidence.down
  | none =>
      simp only [validateGenesisPrefix, check] at validated
      repeat' (first | split at validated | (simp only [bind, Except.bind] at validated))
      all_goals first
        | (simp only [pure, Except.pure, Except.ok.injEq] at validated)
        | (cases validated; done)
        | skip
      all_goals simp_all only [beq_iff_eq]

private theorem validateLogChain_exact {config : Config} {seed : DurableReceiver.Seed}
    {logStart : Digest} {logStartExact? : ExactEvidence (logStart = config.logStart seed)}
    (validated : validateLogChain config seed logStart logStartExact? = .ok ()) :
    logStart = config.logStart seed := by
  cases logStartExact? with
  | some evidence => exact evidence.down
  | none =>
      simp only [validateLogChain, check] at validated
      repeat' (first | split at validated | (simp only [bind, Except.bind] at validated))
      all_goals first
        | (simp only [pure, Except.pure, Except.ok.injEq] at validated)
        | (cases validated; done)
        | skip
      all_goals simp_all only [beq_iff_eq]

private theorem validateChecks_genesis_checked {config : Config} {seed : DurableReceiver.Seed}
    {logStart : Digest} {directory? : Option (Directory Nat CanonicalCellRegistry.registry)}
    {logical? : Option (Store.Store CredentialAuthorityState.layout)} {lawful? : Option Bool}
    {platform? : Option PlatformCellLayout.Platform} {pins : FactoryPins}
    (validated : validateChecks config seed logStart directory? logical? lawful? platform? = .ok pins) :
    seedIdentity seed = config.expectedSeed ∧ logStart = config.logStart seed := by
  simp only [validateChecks] at validated
  obtain ⟨prefixUnit, prefixOk, restOk⟩ := except_bind_ok validated
  cases prefixUnit
  obtain ⟨logUnit, logOk, _⟩ := except_bind_ok restOk
  cases logUnit
  exact ⟨validateGenesisPrefix_exact prefixOk, validateLogChain_exact logOk⟩

/-- Successful validation carries precisely the genesis evidence needed by an
incremental opening of the same Store. -/
theorem validateChecks_genesis {config : Config} {seed : DurableReceiver.Seed}
    {logStart : Digest} {directory? : Option (Directory Nat CanonicalCellRegistry.registry)}
    {logical? : Option (Store.Store CredentialAuthorityState.layout)} {lawful? : Option Bool}
    {platform? : Option PlatformCellLayout.Platform}
    {seedExact? : ExactEvidence (seedIdentity seed = config.expectedSeed)}
    {logStartExact? : ExactEvidence (logStart = config.logStart seed)} {pins : FactoryPins}
    (validated : validateChecks config seed logStart directory? logical? lawful? platform?
      seedExact? logStartExact? = .ok pins) :
    seedIdentity seed = config.expectedSeed ∧ logStart = config.logStart seed := by
  have checked : validateChecks config seed logStart directory? logical? lawful? platform? = .ok pins :=
    (validateChecks_withExact_eq config seed logStart directory? logical? lawful? platform?
      seedExact? logStartExact?).symm.trans validated
  exact validateChecks_genesis_checked checked

/-- `validateChecks` over a typed directory and authority, keeping them and the
cell-law proof. -/
def validateCore {D A : Type} (config : Config) (seed : DurableReceiver.Seed) (logStart : Digest)
    (directory? : Option D) (authority? : Option A)
    (directoryOf : D → Directory Nat CanonicalCellRegistry.registry)
    (logicalOf : A → Store.Store CredentialAuthorityState.layout)
    (lawfulCheck : D → Bool) (platform? : Option PlatformCellLayout.Platform)
    (seedExact? : ExactEvidence (seedIdentity seed = config.expectedSeed) := none)
    (logStartExact? : ExactEvidence (logStart = config.logStart seed) := none) :
    Except String {parts : D × A × FactoryPins // lawfulCheck parts.1 = true} := do
  let pins ← validateChecks config seed logStart (directory?.map directoryOf) (authority?.map logicalOf)
    (directory?.map lawfulCheck) platform? seedExact? logStartExact?
  let directory ← need "noncanonical native directory" directory?
  let authority ← need "complete deployment authority unavailable" authority?
  if checked : lawfulCheck directory = true then pure ⟨(directory, authority, pins), checked⟩
  else .error "native cell role or domain law refused"

theorem validateCore_genesis {D A : Type} {config : Config} {seed : DurableReceiver.Seed}
    {logStart : Digest} {directory? : Option D} {authority? : Option A}
    {directoryOf : D → Directory Nat CanonicalCellRegistry.registry}
    {logicalOf : A → Store.Store CredentialAuthorityState.layout} {lawfulCheck : D → Bool}
    {platform? : Option PlatformCellLayout.Platform}
    {seedExact? : ExactEvidence (seedIdentity seed = config.expectedSeed)}
    {logStartExact? : ExactEvidence (logStart = config.logStart seed)}
    {parts : {parts : D × A × FactoryPins // lawfulCheck parts.1 = true}}
    (validated : validateCore config seed logStart directory? authority? directoryOf logicalOf
      lawfulCheck platform? seedExact? logStartExact? = .ok parts) :
    seedIdentity seed = config.expectedSeed ∧ logStart = config.logStart seed := by
  unfold validateCore at validated
  cases checked : validateChecks config seed logStart (directory?.map directoryOf)
      (authority?.map logicalOf) (directory?.map lawfulCheck) platform? seedExact? logStartExact? with
  | error detail => simp [checked, bind, Except.bind] at validated
  | ok pins => exact validateChecks_genesis checked

/-- `validateCore` as compiled: the cell-law check runs once, its verdict shared
by `validateChecks` and the returned proof (`validateCore` maps it into the
checks and runs it again for the proof). -/
def validateCoreFast {D A : Type} (config : Config) (seed : DurableReceiver.Seed) (logStart : Digest)
    (directory? : Option D) (authority? : Option A)
    (directoryOf : D → Directory Nat CanonicalCellRegistry.registry)
    (logicalOf : A → Store.Store CredentialAuthorityState.layout)
    (lawfulCheck : D → Bool) (platform? : Option PlatformCellLayout.Platform)
    (seedExact? : ExactEvidence (seedIdentity seed = config.expectedSeed) := none)
    (logStartExact? : ExactEvidence (logStart = config.logStart seed) := none) :
    Except String {parts : D × A × FactoryPins // lawfulCheck parts.1 = true} :=
  match directory? with
  | none => do
      let _ ← validateChecks config seed logStart none (authority?.map logicalOf) none platform?
        seedExact? logStartExact?
      need "noncanonical native directory" none
  | some directory =>
      let lawful := lawfulCheck directory
      do
        let pins ← validateChecks config seed logStart (some (directoryOf directory))
          (authority?.map logicalOf) (some lawful) platform? seedExact? logStartExact?
        let authority ← need "complete deployment authority unavailable" authority?
        if checked : lawful = true then pure ⟨(directory, authority, pins), checked⟩
        else .error "native cell role or domain law refused"

@[csimp] theorem validateCore_eq_fast : @validateCore = @validateCoreFast := by
  funext D A config seed logStart directory? authority? directoryOf logicalOf lawfulCheck platform?
    seedExact? logStartExact?
  cases directory? with
  | none =>
      simp only [validateCore, validateCoreFast, Option.map_none]
      cases validateChecks config seed logStart none (authority?.map logicalOf) none platform?
        seedExact? logStartExact? <;> rfl
  | some directory =>
      simp only [validateCore, validateCoreFast, Option.map_some]
      cases validateChecks config seed logStart (some (directoryOf directory)) (authority?.map logicalOf)
        (some (lawfulCheck directory)) platform? seedExact? logStartExact? <;> cases authority? <;> rfl

theorem validateCore_withExact_eq {D A : Type} (config : Config) (seed : DurableReceiver.Seed)
    (logStart : Digest) (directory? : Option D) (authority? : Option A)
    (directoryOf : D → Directory Nat CanonicalCellRegistry.registry)
    (logicalOf : A → Store.Store CredentialAuthorityState.layout) (lawfulCheck : D → Bool)
    (platform? : Option PlatformCellLayout.Platform)
    (seedExact? : ExactEvidence (seedIdentity seed = config.expectedSeed))
    (logStartExact? : ExactEvidence (logStart = config.logStart seed)) :
    validateCore config seed logStart directory? authority? directoryOf logicalOf lawfulCheck
        platform? seedExact? logStartExact? =
      validateCore config seed logStart directory? authority? directoryOf logicalOf lawfulCheck platform? := by
  unfold validateCore
  rw [validateChecks_withExact_eq]

/-- `validateCore` over two shapes whose inputs correspond: the same refusal,
or the same pins. -/
theorem validateCore_map {D A D' A' : Type} (config : Config) (seed : DurableReceiver.Seed)
    (logStart : Digest) (directory? : Option D) (authority? : Option A)
    (directoryOf : D → Directory Nat CanonicalCellRegistry.registry)
    (logicalOf : A → Store.Store CredentialAuthorityState.layout) (lawfulCheck : D → Bool)
    (directory'? : Option D') (authority'? : Option A')
    (directoryOf' : D' → Directory Nat CanonicalCellRegistry.registry)
    (logicalOf' : A' → Store.Store CredentialAuthorityState.layout) (lawfulCheck' : D' → Bool)
    (platform? : Option PlatformCellLayout.Platform)
    (directories : directory'?.map directoryOf' = directory?.map directoryOf)
    (lawfuls : directory'?.map lawfulCheck' = directory?.map lawfulCheck)
    (authorities : authority'?.map logicalOf' = authority?.map logicalOf) :
    (validateCore config seed logStart directory'? authority'? directoryOf' logicalOf' lawfulCheck'
        platform?).map (·.1.2.2) =
      (validateCore config seed logStart directory? authority? directoryOf logicalOf lawfulCheck
        platform?).map (·.1.2.2) := by
  unfold validateCore
  rw [directories, lawfuls, authorities]
  cases validateChecks config seed logStart (directory?.map directoryOf) (authority?.map logicalOf)
      (directory?.map lawfulCheck) platform? with
  | error detail => rfl
  | ok pins =>
      simp only [bind, Except.bind]
      cases directory? <;> cases directory'? <;> simp at directories lawfuls
      · rfl
      · rename_i d' d
        cases authority? <;> cases authority'? <;> simp at authorities
        · rfl
        · simp only [need, pure, Except.pure]
          by_cases verdict : lawfulCheck' d = true
          · rw [dif_pos verdict, dif_pos (lawfuls ▸ verdict)]
            rfl
          · rw [dif_neg verdict, dif_neg (lawfuls ▸ verdict)]
            rfl

/-- The one validation of the full shape, over a supplied directory, authority
and cell-law check. When the directory and authority are the image's own loads
and the check decides `cellsLawful` (`lawfulExact`), this is `validateParts`,
the same result and the same refusal in the same order (`validatePartsVia_eq`). -/
def validatePartsVia (config : Config) (durable : Durable)
    (directory? : Option (CredentialAuthorityDomainReceiver.LoadedDirectory durable))
    (authority? : Option (CredentialAuthorityDomainReceiver.Loaded config.deployment durable.snapshot))
    (lawfulCheck : CredentialAuthorityDomainReceiver.LoadedDirectory durable → Bool)
    (lawfulExact : ∀ loaded, lawfulCheck loaded = cellsLawful config durable loaded.directory)
    (seedExact? : ExactEvidence (seedIdentity durable.image.seed = config.expectedSeed) := none)
    (logStartExact? : ExactEvidence (durable.logStart = config.logStart durable.image.seed) := none) :
    Except String (Validated config durable) :=
  match core : validateCore config durable.image.seed durable.logStart directory? authority?
      (·.directory) (·.snapshot.logical) lawfulCheck
      (PlatformCellDomain.recordAt config.deployment durable.snapshot.canonicalBytes)
      seedExact? logStartExact? with
  | .error detail => .error detail
  | .ok parts =>
      let genesis := validateCore_genesis core
      .ok ⟨parts.1.1, parts.1.2.1, parts.1.2.2, (lawfulExact parts.1.1) ▸ parts.2,
        genesis.1, genesis.2⟩

/-- `validatePartsVia` over the image's own authority load. The caller's
directory must be the image's (`validatePartsWith_eq`). -/
def validatePartsWith (config : Config) (durable : Durable)
    (directory? : Option (CredentialAuthorityDomainReceiver.LoadedDirectory durable))
    (lawfulCheck : CredentialAuthorityDomainReceiver.LoadedDirectory durable → Bool)
    (lawfulExact : ∀ loaded, lawfulCheck loaded = cellsLawful config durable loaded.directory) :
    Except String (Validated config durable) :=
  validatePartsVia config durable directory?
    (CredentialAuthorityDomainReceiver.loadDeployment config.deployment durable.snapshot)
    lawfulCheck lawfulExact

def validateParts (config : Config) (durable : Durable) :
    Except String (Validated config durable) :=
  validatePartsWith config durable (CredentialAuthorityDomainReceiver.loadDirectory durable)
    (fun loaded => cellsLawful config durable loaded.directory) (fun _ => rfl)

theorem validatePartsWith_eq (config : Config) (durable : Durable)
    (directory? : Option (CredentialAuthorityDomainReceiver.LoadedDirectory durable))
    (lawfulCheck : CredentialAuthorityDomainReceiver.LoadedDirectory durable → Bool)
    (lawfulExact : ∀ loaded, lawfulCheck loaded = cellsLawful config durable loaded.directory)
    (loaded : directory? = CredentialAuthorityDomainReceiver.loadDirectory durable) :
    validatePartsWith config durable directory? lawfulCheck lawfulExact = validateParts config durable := by
  subst loaded
  have same : lawfulCheck = fun loaded => cellsLawful config durable loaded.directory :=
    funext lawfulExact
  subst same
  rfl

theorem validatePartsVia_withExact_eq (config : Config) (durable : Durable)
    (directory? : Option (CredentialAuthorityDomainReceiver.LoadedDirectory durable))
    (authority? : Option (CredentialAuthorityDomainReceiver.Loaded config.deployment durable.snapshot))
    (lawfulCheck : CredentialAuthorityDomainReceiver.LoadedDirectory durable → Bool)
    (lawfulExact : ∀ loaded, lawfulCheck loaded = cellsLawful config durable loaded.directory)
    (seedExact? : ExactEvidence (seedIdentity durable.image.seed = config.expectedSeed))
    (logStartExact? : ExactEvidence (durable.logStart = config.logStart durable.image.seed))
    (loaded : directory? = CredentialAuthorityDomainReceiver.loadDirectory durable)
    (authorityLoaded : authority? = CredentialAuthorityDomainReceiver.loadDeployment config.deployment durable.snapshot) :
    validatePartsVia config durable directory? authority? lawfulCheck lawfulExact
      seedExact? logStartExact? = validateParts config durable := by
  subst authorityLoaded
  subst loaded
  have same : lawfulCheck = fun loaded => cellsLawful config durable loaded.directory :=
    funext lawfulExact
  subst same
  have sameCore := validateCore_withExact_eq config durable.image.seed durable.logStart
    (CredentialAuthorityDomainReceiver.loadDirectory durable)
    (CredentialAuthorityDomainReceiver.loadDeployment config.deployment durable.snapshot)
    (·.directory) (·.snapshot.logical) (fun loaded => cellsLawful config durable loaded.directory)
    (PlatformCellDomain.recordAt config.deployment durable.snapshot.canonicalBytes)
    seedExact? logStartExact?
  unfold validateParts validatePartsWith validatePartsVia
  split <;> split <;> simp_all [sameCore]

theorem validatePartsVia_eq (config : Config) (durable : Durable)
    (directory? : Option (CredentialAuthorityDomainReceiver.LoadedDirectory durable))
    (authority? : Option (CredentialAuthorityDomainReceiver.Loaded config.deployment durable.snapshot))
    (lawfulCheck : CredentialAuthorityDomainReceiver.LoadedDirectory durable → Bool)
    (lawfulExact : ∀ loaded, lawfulCheck loaded = cellsLawful config durable loaded.directory)
    (loaded : directory? = CredentialAuthorityDomainReceiver.loadDirectory durable)
    (authorityLoaded : authority? = CredentialAuthorityDomainReceiver.loadDeployment config.deployment durable.snapshot) :
    validatePartsVia config durable directory? authority? lawfulCheck lawfulExact = validateParts config durable := by
  subst authorityLoaded
  exact validatePartsWith_eq config durable directory? lawfulCheck lawfulExact loaded

def validateLoaded (config : Config) (durable : Durable) : Except String (Opened config) :=
  (validateParts config durable).map fun parts =>
    ⟨durable, parts.directory, parts.authority, parts.pins, parts.lawful,
      parts.seedExact, parts.logStartExact⟩

/-- The pins projected from full validation depend only on the typed core. -/
theorem validateLoaded_pins_core (config : Config) (durable : Durable) :
    (validateLoaded config durable).map (·.pins) =
      (validateCore config durable.image.seed durable.logStart
        (CredentialAuthorityDomainReceiver.loadDirectory durable)
        (CredentialAuthorityDomainReceiver.loadDeployment config.deployment durable.snapshot)
        (·.directory) (·.snapshot.logical)
        (fun loaded => cellsLawful config durable loaded.directory)
        (PlatformCellDomain.recordAt config.deployment durable.snapshot.canonicalBytes)).map (·.1.2.2) := by
  unfold validateLoaded validateParts validatePartsWith validatePartsVia
  split <;> simp_all [Except.map]

/-- A validated image's cell law holds at every identifier: outside the
enumerable support the bytes are the absent default, so the slot is absent. -/
theorem Opened.cellLawful_all {config : Config} (prior : Opened config) (identifier : Digest) :
    cellLawful config prior.directory.directory identifier = true := by
  by_cases member : identifier ∈ prior.durable.image.cellIds
  · exact List.all_eq_true.mp prior.lawful identifier member
  · have bytes := prior.directory.bytes_exact identifier.value
    rw [Kernel.DurableCheckpoint.resume_outside_support ResourceBirthCodec.rootBytes
      prior.durable.image prior.durable.baseHeight prior.durable.base prior.durable.snapshot
      prior.durable.resumed ⟨identifier.value⟩ member, prior.directory.absentDefault] at bytes
    have slot := ResourceBirthCodec.LifecycleImage.view_slot CanonicalCellRegistry.registry
      prior.directory.directory identifier.value
    cases view : ResourceBirthCodec.LifecycleImage.view CanonicalCellRegistry.registry
        prior.directory.directory identifier.value with
    | fresh =>
        rw [view] at slot
        unfold cellLawful
        rw [← slot]
        rfl
    | retired =>
        rw [view] at bytes
        simp [ResourceBirthCodec.LifecycleImage.bytes] at bytes
    | live cell =>
        rw [view] at bytes
        simp [ResourceBirthCodec.LifecycleImage.bytes] at bytes

/-- The cell-law check of a later image of a session: a cell whose canonical
bytes equal the prior validated image's passed already (`Opened.cellLawful_all`)
and is not re-checked. `cellsLawfulFrom_eq`: it decides `cellsLawful`. -/
def cellsLawfulFrom (config : Config) (prior : Opened config) (durable : Durable)
    (loaded : CredentialAuthorityDomainReceiver.LoadedDirectory durable) : Bool :=
  durable.image.cellIds.all fun identifier =>
    prior.durable.snapshot.canonicalBytes identifier == durable.snapshot.canonicalBytes identifier ||
      cellLawful config loaded.directory identifier

/-- `cellsLawfulFrom` over the cached enumeration. -/
def cellsLawfulFromCached (config : Config) (prior : Opened config) (durable : Durable)
    (loaded : CredentialAuthorityDomainReceiver.LoadedDirectory durable) : Bool :=
  durable.cellIds.all fun identifier =>
    Minidregg.Compiler.CredentialAuthorityDomainReceiver.bytesBEq (prior.durable.snapshot.canonicalBytes identifier)
        (durable.snapshot.canonicalBytes identifier) ||
      cellLawful config loaded.directory identifier

@[csimp] theorem cellsLawfulFrom_eq_cached : @cellsLawfulFrom = @cellsLawfulFromCached := by
  funext config prior durable loaded
  unfold cellsLawfulFrom cellsLawfulFromCached
  simp only [Minidregg.Compiler.CredentialAuthorityDomainReceiver.bytesBEq_eq]
  rw [DurableReceiverIO.Loaded.cellIds_eq]

#assert_axioms cellsLawful_eq_cached
#assert_axioms cellsLawfulFrom_eq_cached

theorem cellsLawfulFrom_eq (config : Config) (prior : Opened config) (durable : Durable)
    (loaded : CredentialAuthorityDomainReceiver.LoadedDirectory durable) :
    cellsLawfulFrom config prior durable loaded = cellsLawful config durable loaded.directory := by
  unfold cellsLawfulFrom cellsLawful
  apply Bool.eq_iff_iff.mpr
  simp only [List.all_eq_true, Bool.or_eq_true, beq_iff_eq]
  constructor
  · intro accepted identifier member
    rcases accepted identifier member with same | lawful
    · have held := prior.cellLawful_all identifier
      unfold cellLawful at held ⊢
      rwa [← CredentialAuthorityDomainReceiver.LoadedDirectory.slots_eq_of_bytes
        prior.directory loaded identifier.value same]
    · exact lawful
  · intro lawful identifier member
    exact Or.inr (lawful identifier member)

/-- Evidence the next image can inherit without re-encoding its genesis. The
log-start proof needs both the seed and the actual chain start to be unchanged. -/
private def priorGenesisEvidence {config : Config} (prior : Opened config) (durable : Durable) :
    ExactEvidence (seedIdentity durable.image.seed = config.expectedSeed) ×
      ExactEvidence (durable.logStart = config.logStart durable.image.seed) :=
  if sameSeed : prior.durable.image.seed = durable.image.seed then
    (some ⟨sameSeed ▸ prior.seedExact⟩,
      if sameStart : prior.durable.logStart = durable.logStart then
        some ⟨by simpa only [sameSeed, sameStart] using prior.logStartExact⟩
      else none)
  else (none, none)

/-- **Validation of a session's next image, incrementally**: the directory
decodes only rows whose bytes moved (`loadDirectoryFrom`), the authority cell is
decoded only when its bytes moved (`loadDeploymentFrom`) and the cell law runs
only on cells whose bytes moved (`cellsLawfulFrom`). The two genesis hashes are
reused when the seed and log start are unchanged. `validateLoadedFrom_eq`: it
is `validateLoaded` -- the same `Opened`, the same refusal. -/
def validateLoadedFrom (config : Config) (prior : Opened config) (durable : Durable) :
    Except String (Opened config) :=
  let evidence := priorGenesisEvidence prior durable
  (validatePartsVia config durable
    (CredentialAuthorityDomainReceiver.loadDirectoryFrom prior.directory durable)
    (CredentialAuthorityDomainReceiver.loadDeploymentFromAt prior.authority durable.snapshot
      durable.height (DurableReceiverIO.Loaded.history_length_eq_height durable).symm)
    (cellsLawfulFrom config prior durable) (cellsLawfulFrom_eq config prior durable)
    evidence.1 evidence.2).map
    fun parts => ⟨durable, parts.directory, parts.authority, parts.pins, parts.lawful,
      parts.seedExact, parts.logStartExact⟩

theorem validateLoadedFrom_eq (config : Config) (prior : Opened config) (durable : Durable) :
    validateLoadedFrom config prior durable = validateLoaded config durable := by
  unfold validateLoadedFrom validateLoaded
  dsimp only
  rw [validatePartsVia_withExact_eq config durable _ _ _ _
    (priorGenesisEvidence prior durable).1 (priorGenesisEvidence prior durable).2
    (CredentialAuthorityDomainReceiver.loadDirectoryFrom_eq prior.directory durable)
    ((CredentialAuthorityDomainReceiver.loadDeploymentFromAt_eq prior.authority durable.snapshot
      durable.height (DurableReceiverIO.Loaded.history_length_eq_height durable).symm).trans
    (CredentialAuthorityDomainReceiver.loadDeploymentAt_eq config.deployment durable.snapshot
      durable.height (DurableReceiverIO.Loaded.history_length_eq_height durable).symm))]

/-- Validation wraps exactly the image it was given. -/
theorem validateLoaded_durable {config : Config} {durable : Durable} {opened : Opened config}
    (validated : validateLoaded config durable = .ok opened) : opened.durable = durable := by
  unfold validateLoaded at validated
  cases parts : validateParts config durable with
  | error detail => simp [parts, Except.map] at validated
  | ok value =>
      simp only [parts, Except.map, Except.ok.injEq] at validated
      subst validated
      rfl

/-! ## The served root and C1's specification root -/

/-- The served entries (read off a resumed snapshot) are C1's `worldEntries` of
the image when the snapshot is the genesis replay and the chain is the
deployment's log root. -/
theorem entriesOf_worldEntries (config : Config) (image : DurableReceiver.Image)
    (snapshot : DurableDataIntent.DataSnapshot ResourceBirthCodec.rootBytes) (chain : Digest)
    (restored : image.restore ResourceBirthCodec.rootBytes = some snapshot)
    (rooted : chain = NativeHostCodec.logRoot config.deployment.domain config.profile.semantics image) :
    DurableReceiverIO.entriesOf image snapshot chain =
      (NativeHostCodec.worldEntries config.deployment.domain config.profile.semantics image).map
        fun e => (e.1, NativeHostCodec.leafRoot e.2) := by
  unfold DurableReceiverIO.entriesOf NativeHostCodec.worldEntries
  rw [List.map_cons, List.map_map]
  refine congrArg₂ List.cons ?_ ?_
  · rw [rooted]
    rfl
  · apply List.map_congr_left
    intro cellId _
    show (_, snapshot.model.roots cellId) = (_, ResourceBirthCodec.rootBytes (image.currentBytes cellId))
    rw [← snapshot.coherent cellId,
      DurableReceiver.Image.currentBytes_restore ResourceBirthCodec.rootBytes image snapshot restored cellId]

/-- **The root a Loaded serves after open or rebase** (a cache built from the
served state) is C1's specification root of the image, when the resumed
snapshot is the genesis replay (`DurableCheckpoint.resume_sound`: an honest
checkpoint) and the chain is rooted at this deployment's genesis log root
(`validateLoaded` refuses otherwise; `Loaded.chainExact`). -/
theorem servedRoot_eq_worldRoot (config : Config) (image : DurableReceiver.Image)
    (snapshot : DurableDataIntent.DataSnapshot ResourceBirthCodec.rootBytes) (chain : Digest)
    (restored : image.restore ResourceBirthCodec.rootBytes = some snapshot)
    (rooted : chain = NativeHostCodec.logRoot config.deployment.domain config.profile.semantics image) :
    (WorldRootCache.RootCache.ofEntries (DurableReceiverIO.entriesOf image snapshot chain)).root =
      worldRoot config image := by
  rw [WorldRootCache.RootCache.ofEntries_root, entriesOf_worldEntries config image snapshot chain restored rooted]
  simp only [worldRoot, NativeHostCodec.worldRoot, NativeHostCodec.worldSlotRoots]

/-- **Every root a Loaded serves is C1's specification root of its image** —
after open, after any number of appends (one cached path each), after any
rebase: `Loaded.worldRoot_eq` carries the cache's agreement with the served
entries, so no full rebuild is needed to know it. Premises as above: the
snapshot is the genesis replay and the chain is rooted at this deployment. -/
theorem loadedRoot_eq_worldRoot (config : Config) (durable : Durable)
    (restored : durable.image.restore ResourceBirthCodec.rootBytes = some durable.snapshot)
    (rooted : durable.chain =
      NativeHostCodec.logRoot config.deployment.domain config.profile.semantics durable.image) :
    durable.worldRoot = worldRoot config durable.image := by
  rw [DurableReceiverIO.Loaded.worldRoot_eq,
    entriesOf_worldEntries config durable.image durable.snapshot durable.chain restored rooted]
  simp only [worldRoot, NativeHostCodec.worldRoot, NativeHostCodec.worldSlotRoots]

/-- info: 'Minidregg.Kernel.NativeHost.loadedRoot_eq_worldRoot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms loadedRoot_eq_worldRoot

/-- The chain of a loaded image validated for this deployment is its log root. -/
theorem chain_logRoot (config : Config) (durable : Durable)
    (rooted : durable.logStart = config.logStart durable.image.seed) :
    durable.chain = NativeHostCodec.logRoot config.deployment.domain config.profile.semantics durable.image := by
  rw [durable.chainExact, rooted]
  rfl

/-- info: 'Minidregg.Kernel.NativeHost.servedRoot_eq_worldRoot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms servedRoot_eq_worldRoot

end Minidregg.Kernel.NativeHost
