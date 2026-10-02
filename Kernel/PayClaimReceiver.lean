/-
Paid claim recovery uses an exact source-prepared ownership witness, not a
fictional observer or a capability the not-yet-admitted owner cannot possess.
The native signature, current custody, immutable origin, one-time consumption
and quote gate precede the witness; the actual current composed factory law is
still mandatory. This is a closed two-action receiving surface.
-/
import Kernel.PayClaimDecision
import Kernel.PayEnrolV2Receiver
import Kernel.PayClaimLaw

namespace Minidregg.Kernel.PayClaimReceiver
open Minidregg.Compiler
open Minidregg.Compiler.CanonicalPolicyAdmission
open Minidregg.Compiler.CredentialAuthorityDomainReceiver
open Minidregg.Compiler.CredentialAuthorityPolicyRegistry
open Minidregg.Compiler.ResourceBirthCodec
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Kernel
open Minidregg.Kernel.DurableDataIntent
open Minidregg.Kernel.PayCell
open Minidregg.Kernel.PayTariff
open Minidregg.Kernel.PayEnrolReceiver (Registry Deployment Durable Ambient BookCell FactoryCell Declaration Mode)
open Minidregg.Kernel.PayClaimCommand (Command DecodedIngress Checked marker decodeIngress)
open Minidregg.Theory
open Minidregg.Theory.CellState
open Minidregg.Theory.CellRegistry
open Minidregg.Theory.IndexedProgram
open Minidregg.Theory.Store (Patch)
open Minidregg.Theory.TypedAuthorization

set_option autoImplicit false
attribute [local irreducible] CanonicalRuntimeProfile.Profile.compilerProfile

/-- Stable owner identity, including when the invocation is signed by a
precommitted pending successor. -/
def identityKey (command : Command) : List UInt8 :=
  match command.action with
  | .inl accept => accept.ownerIdentityKey
  | .inr rotation => rotation.ownerIdentityKey

def subject (command : Command) : SubjectId := ⟨PayEnrolMemo.subjectOf (identityKey command)⟩

def effectDigest (domain semantics : Digest) (command : Command) (d : Declaration) : Digest :=
  (Sp800185Cshake256.hash "DREGG/PAY/CLAIM/EFFECT/v1".toUTF8.toList
    (digestStream.encode domain ++ digestStream.encode semantics ++
      bytesStream.encode (PayClaimCommand.commandCodec.encode command) ++
      bytesStream.encode (PayEnrolReceiver.declarationCodec.encode d))).digest

def context (deployment : Deployment) (snapshot : CredentialAuthorityDomain.Snapshot)
    (semantics : Digest) (ambient : Ambient) (command : Command) : RequestContext where
  authority :=
    { kind := .program
      domain := snapshot.domain
      semantics := semantics
      federation := ambient.federation
      subject := subject command
      subjectKeyEpoch := snapshot.authState.subjectKeyEpoch (subject command)
      target := ⟨deployment.factoryId⟩
      verb := .installPolicy
      nonce := (marker snapshot.domain semantics command).value
      height := ambient.height
      policyId := ⟨deployment.factoryId⟩
      policyEpoch := snapshot.authState.policyEpoch ⟨deployment.factoryId⟩
      policyRevision := snapshot.authState.policyRevision ⟨deployment.factoryId⟩
      cost := (PayClaimCommand.commandCodec.encode command).length }
  argsDigestBytes := fun bytes =>
    (Sp800185Cshake256.hash "DREGG/PAY/CLAIM/ARGS/v1".toUTF8.toList
      (PayClaimCommand.commandCodec.encode command ++ bytes)).digest

def request (deployment : Deployment) (snapshot : CredentialAuthorityDomain.Snapshot)
    (pay : PayCell.Cell) (semantics : Digest) (ambient : Ambient) (command : Command)
    (d : Declaration) : Request .program :=
  ((context deployment snapshot semantics ambient command).request
    PayEnrolReceiver.declarationCodec (effectDigest snapshot.domain semantics command)
    pay.root d.operationNullifier d).2

def family (deployment : Deployment) (snapshot : CredentialAuthorityDomain.Snapshot)
    (pay : PayCell.Cell) (semantics : Digest) (ambient : Ambient) (command : Command)
    (patch : Patch PayCell.layout) : SemanticEffectFamily PayCell.layout PayCell.materializer Nat where
  Declaration := Declaration
  declarationCodec := PayEnrolReceiver.declarationCodec
  pre := pay
  request := fun d => (context deployment snapshot semantics ambient command).request
    PayEnrolReceiver.declarationCodec (effectDigest snapshot.domain semantics command)
    pay.root d.operationNullifier d
  Outcome := fun _ => Unit
  outcomeCodec := fun _ => unitCodec
  ModeEvidence := fun d _ => Mode pay d
  Postcondition := fun _ _ post => patch.ResultAt pay.logical post
  effectDigest := effectDigest snapshot.domain semantics command
  patch := fun _ _ => patch
  nullifier := fun d _ => some d.operationNullifier
  Release := fun _ _ => Unit
  DeclassificationAuthority := fun _ _ => Unit
  ReleaseAuthorization := fun _ _ _ => Unit
  DisclosureAllowed := fun _ _ => sealedOnly

inductive Reject where
  | malformedIngress | directoryUnavailable | authorityUnavailable | payUnavailable
  | bookUnavailable | factoryUnavailable | clockUnavailable | staleAuthority | stalePay
  | claimUnavailable | malformedOrigin
  | decision (reason : PayClaimDecision.Reject)
  | legs (reason : PayEnrolV2Legs.Reject)
  | verifier (reason : CredentialSignatureIO.Error)
  | validation | physicalPreparation | policyUnavailable | policyRejected
  | policyInputRange | policyCastAlias
  deriving Repr

def requireSome {A : Type} (reason : Reject) : Option A → Except Reject A
  | none => .error reason | some value => .ok value

/-- The source identity, not a caller fee, determines the ordinary account
birth descriptor. Renewal/rotation decision ignores this birth fee. -/
def pricingAt {F : Type} [Field F] (deployment : Deployment)
    (profile : CanonicalRuntimeProfile.Profile F) (ambient : Ambient) (seed : Digest)
    (authority : CredentialAuthorityDomain.Snapshot) (command : Command) : PayClaimDecision.Pricing :=
  ⟨deployment.domain, seed, profile.semantics, ambient.tariff, profile.template,
    PayEnrolReceiver.birthFee deployment profile.semantics profile.template ambient.tariff
      authority.cell ambient.height (PayEnrolReceiver.ids deployment.domain (identityKey command)) 0⟩

section Preparation
variable {F : Type} [Field F]

/-- Normalized source decision bytes commit the exact economic origin, split,
processing evidence and membership allocation. Rotation is already fully named
by its closed signed command and guarded custody preimage. -/
def decisionBytes : PayClaimDecision.Decision → List UInt8
  | .accept (.enrol plan) => [1] ++
      PayEnrolClaim.claimCodec.encode plan.input.economic.origin ++
      PayEnrolClaim.consumptionCodec.encode plan.input.economic.consumption ++
      chainTipStream.encode plan.tip ++ bytesStream.encode plan.sshBlob ++
      (StreamCodec.option StreamCodec.nat).encode plan.index ++
      StreamCodec.nat.encode plan.leaseUntil
  | .accept (.renew plan) => [2] ++
      PayEnrolClaim.claimCodec.encode plan.input.economic.origin ++
      PayEnrolClaim.consumptionCodec.encode plan.input.economic.consumption ++
      chainTipStream.encode plan.tip ++ enrolRecordStream.encode plan.input.before ++
      StreamCodec.nat.encode plan.leaseFrom ++ StreamCodec.nat.encode plan.leaseUntil
  | .rotate _ => [3]

/-- The full signed command and source decision are committed together. Actual
pay/Book patches remain tied by private preparation and physical post-law checks;
this declaration does not pretend to expose a candidate post-root. -/
def declarationOf {deployment : Deployment} {profile : CanonicalRuntimeProfile.Profile F}
    {ambient : Ambient} {durable : Durable} {directory : LoadedDirectory durable}
    {authority : Loaded deployment durable.snapshot} {pay : PayCellDomain.Loaded deployment durable.snapshot}
    {book : BookCell deployment directory.directory} {tariff : Tariff}
    (ingress : DecodedIngress) (decision : PayClaimDecision.Decision)
    (legs : PayEnrolV2Legs.Legs deployment profile ambient directory authority pay book tariff decision.input) :
    Declaration :=
  ⟨bytesStream.encode (PayClaimCommand.commandCodec.encode ingress.command) ++
      bytesStream.encode (decisionBytes decision), legs.birthBytes,
    ingress.command.expectedPayRoot, (marker authority.snapshot.domain profile.semantics ingress.command).value⟩

structure Prepared (deployment : Deployment) (profile : CanonicalRuntimeProfile.Profile F)
    (ambient : Ambient) (durable : Durable) (ingress : DecodedIngress)
    (checked : Checked deployment.domain profile.semantics ingress) where
  private mk ::
  expectedSeed : Digest
  directory : LoadedDirectory durable
  authority : Loaded deployment durable.snapshot
  pay : PayCellDomain.Loaded deployment durable.snapshot
  book : BookCell deployment directory.directory
  factory : FactoryCell deployment directory.directory
  tariff : Tariff
  tariffExact : tariffOf pay.cell.logical = some tariff
  clock : ClockCellDomain.Loaded deployment durable.snapshot
  decision : PayClaimDecision.Decision
  decided : PayClaimDecision.decide pay.cell.logical authority.snapshot clock.clock
    (pricingAt deployment profile ambient expectedSeed authority.snapshot ingress.command) ingress checked = .ok decision
  legs : PayEnrolV2Legs.Legs deployment profile ambient directory authority pay book tariff decision.input
  candidate : Candidate (family deployment authority.snapshot pay.cell profile.semantics ambient ingress.command
      (decision.payPatch legs.account)) pay.cell (declarationOf ingress decision legs) ()
  dependencies : WorldKindLawDependencies.Dependencies
  dependenciesExact : WorldKindLawDependencies.loadTarget deployment directory.directory
    deployment.factoryId = some dependencies
  lawGuards : List (Nat × Digest)
  lawGuardsExact : PhysicalLawResolution.readGuards authority.snapshot directory.directory
    profile.semantics deployment.factoryId dependencies.additional = some lawGuards

def prepare (deployment : Deployment) (profile : CanonicalRuntimeProfile.Profile F)
    (ambient : Ambient) (seed : Digest) (durable : Durable) (ingress : DecodedIngress)
    (checked : Checked deployment.domain profile.semantics ingress) :
    Except Reject (Prepared deployment profile ambient durable ingress checked) := do
  let directory ← requireSome .directoryUnavailable (loadDirectory durable)
  let authority ← requireSome .authorityUnavailable (loadDeployment deployment durable.snapshot)
  let pay ← requireSome .payUnavailable (PayCellDomain.load deployment durable.snapshot)
  let clock ← requireSome .clockUnavailable (ClockCellDomain.load deployment durable.snapshot)
  let book ← requireSome .bookUnavailable
    (ResourceBirthController.Concrete.observeCell deployment directory.directory deployment.resourceBookId .resourceBook)
  let factory ← requireSome .factoryUnavailable
    (ResourceBirthController.Concrete.observeCell deployment directory.directory deployment.factoryId .declaredObject)
  if ingress.command.expectedAuthorityRoot ≠ authority.snapshot.cell.root then throw .staleAuthority
  if rootExact : ingress.command.expectedPayRoot = pay.cell.root then
    match tariffExact : tariffOf pay.cell.logical with
    | none => throw .payUnavailable
    | some tariff =>
      match decided : PayClaimDecision.decide pay.cell.logical authority.snapshot clock.clock
          (pricingAt deployment profile ambient seed authority.snapshot ingress.command) ingress checked with
      | .error reason => throw (.decision reason)
      | .ok decision =>
        let legs ← (PayEnrolV2Legs.prepare deployment profile ambient directory authority pay book tariff decision.input).mapError Reject.legs
        match validate PayCell.materializer pay.cell pay.cell.root (decision.payPatch legs.account) with
        | .rejected _ => throw .validation
        | .accepted validated =>
          let candidate : Candidate (family deployment authority.snapshot pay.cell profile.semantics ambient ingress.command
              (decision.payPatch legs.account)) pay.cell (declarationOf ingress decision legs) () :=
            { preStateBound := rfl
              modeEvidence := ⟨rootExact⟩
              validated := validated
              postcondition := validated.resultAt }
          match dependenciesExact : WorldKindLawDependencies.loadTarget deployment directory.directory deployment.factoryId with
          | none => throw .policyUnavailable
          | some dependencies =>
            match lawGuardsExact : PhysicalLawResolution.readGuards authority.snapshot directory.directory
                profile.semantics deployment.factoryId dependencies.additional with
            | none => throw .policyUnavailable
            | some lawGuards =>
              pure ⟨seed, directory, authority, pay, book, factory, tariff, tariffExact, clock,
                decision, decided, legs, candidate, dependencies, dependenciesExact, lawGuards, lawGuardsExact⟩
  else throw .stalePay

variable {deployment : Deployment} {profile : CanonicalRuntimeProfile.Profile F}
  {ambient : Ambient} {durable : Durable} {ingress : DecodedIngress}
  {checked : Checked deployment.domain profile.semantics ingress}

def Prepared.declaration (prepared : Prepared deployment profile ambient durable ingress checked) : Declaration :=
  declarationOf ingress prepared.decision prepared.legs

def Prepared.payPost (prepared : Prepared deployment profile ambient durable ingress checked) : PayCell.Cell :=
  prepared.candidate.validated.apply

def wanted (prepared : Prepared deployment profile ambient durable ingress checked) : Request .program :=
  request deployment prepared.authority.snapshot prepared.pay.cell profile.semantics ambient ingress.command prepared.declaration

def project (prepared : Prepared deployment profile ambient durable ingress checked) (_logical : PayStore) : Minidregg.Pred.State :=
  ⟨WorldKindLawDependencies.targetSelectorSlots prepared.directory.directory deployment.factoryId ++
    CanonicalRuntimeProfile.requestSlots (wanted prepared) ++
    [(PayClaimLaw.operationSlot, 1), (PayClaimLaw.authorizedSlot, 1),
     ("pay/claim/action", match ingress.command.action with | .inl _ => 0 | .inr _ => 1),
     ("pay/claim/minted", Int.ofNat prepared.decision.mintedCredit)]⟩

def step (prepared : Prepared deployment profile ambient durable ingress checked) : PolicyStepContext :=
  PolicyStepContext.ofCandidate (project prepared) profile.semantics prepared.candidate

/-- The witness is only available for this private, checked source preparation.
It retains the actual native-checked decision equality, not a caller boolean. -/
structure SourceWitness (prepared : Prepared deployment profile ambient durable ingress checked) where
  private mk ::
  admitted : PayClaimDecision.decide prepared.pay.cell.logical prepared.authority.snapshot
    prepared.clock.clock (pricingAt deployment profile ambient prepared.expectedSeed
      prepared.authority.snapshot ingress.command) ingress checked = .ok prepared.decision

/-- No proof witness for one claim can authorize another kind, subject, target,
quote, nonce, root or effect. All ordinary capability faces retain the source
portal; this receiver uses only the exact closed proof face. -/
def proofPortal (prepared : Prepared deployment profile ambient durable ingress checked) : Portal :=
  { sourceCapabilityPortal prepared.authority.snapshot (marker deployment.domain profile.semantics ingress.command).value with
    ProofWitness := SourceWitness prepared
    verifyProof := fun {kind} actual _ =>
      match kind, actual with
      | .program, actual => decide (actual = wanted prepared)
      | _, _ => false }

def policyConfig [DecidableEq F] (prepared : Prepared deployment profile ambient durable ingress checked) :
    ComposedPolicyAdmission.Config F :=
  PhysicalLawResolution.config profile.compilerProfile prepared.authority.snapshot
    prepared.directory.directory (proofPortal prepared) (step prepared) deployment.factoryId prepared.dependencies.additional

abbrev Prepared.SemanticAccepted [DecidableEq F]
    (prepared : Prepared deployment profile ambient durable ingress checked) :=
  AcceptedCellEffect (portal := (policyConfig prepared).portal)
    (authState := prepared.authority.snapshot.authState)
    (family deployment prepared.authority.snapshot prepared.pay.cell profile.semantics ambient ingress.command
      (prepared.decision.payPatch prepared.legs.account))
    (wanted prepared) prepared.pay.cell prepared.declaration ()

def authorize [DecidableEq F] (prepared : Prepared deployment profile ambient durable ingress checked) :
    Except Reject prepared.SemanticAccepted := do
  let config := policyConfig prepared
  let evidence : Evidence config.portal prepared.authority.snapshot.authState (wanted prepared) :=
    .proof ⟨prepared.decided⟩ (by
      simp [config, policyConfig, PhysicalLawResolution.config, ComposedPolicyAdmission.Config.portal,
        domainPortal, proofPortal])
  let law ← requireSome .policyUnavailable config.resolve?
  if inputsInRange profile.compilerProfile.compiler law.predicate (step prepared).oldState (step prepared).newState != true then
    throw .policyInputRange
  if !decide (castInjOn F (intsOf law.predicate (step prepared).oldState (step prepared).newState)) then
    throw .policyCastAlias
  match ComposedPolicyAdmission.admit config (wanted prepared) evidence law.witness
      (.policy (wanted prepared).policyId (wanted prepared).policyRevision) rfl rfl with
  | none => .error .policyRejected
  | some authorization => .ok (prepared.candidate.accept authorization rfl rfl rfl .sealed trivial)

/-- There is no clock/tip write here: claims use authenticated retained evidence,
and their exact clock and law inputs are guarded through the durable commit. -/
def writes (prepared : Prepared deployment profile ambient durable ingress checked) : List DataWrite :=
  prepared.pay.write prepared.payPost :: prepared.legs.writes prepared.factory

def readGuards (prepared : Prepared deployment profile ambient durable ingress checked) : List ReadGuard :=
  (prepared.clock.readGuard :: prepared.authority.readGuards ++
    (prepared.lawGuards ++ prepared.dependencies.readGuards).map (fun (cellIdentifier, expectedRoot) => (⟨⟨cellIdentifier⟩, expectedRoot⟩ : ReadGuard))).filter
    fun guard => guard.cellId ∉ (writes prepared).map DataWrite.cellId

def PhysicalShape (prepared : Prepared deployment profile ambient durable ingress checked) : Prop :=
  ((writes prepared).map DataWrite.cellId).Nodup ∧
    (∀ write ∈ writes prepared, write.expectedPre = durable.snapshot.model.roots write.cellId) ∧
    (∀ write ∈ writes prepared, ResourceBirthController.Concrete.PhysicalPostLaw deployment write) ∧
    (∀ write ∈ writes prepared, rootBytes write.canonicalPostBytes = write.exactPost) ∧
    (∀ guard ∈ readGuards prepared, guard.expectedRoot = durable.snapshot.model.roots guard.cellId)

instance physicalShapeDecidable (prepared : Prepared deployment profile ambient durable ingress checked) : Decidable (PhysicalShape prepared) := by
  unfold PhysicalShape; infer_instance

theorem readGuards_readonly (prepared : Prepared deployment profile ambient durable ingress checked)
    (guard : ReadGuard) (member : guard ∈ readGuards prepared) :
    guard.cellId ∉ (writes prepared).map DataWrite.cellId := by
  simpa using (List.mem_filter.mp member).2

def operationNullifier (domain semantics : Digest) (ingress : DecodedIngress) : StableNullifier :=
  CredentialAuthorityReplay.nullifier domain (marker domain semantics ingress.command).value

def nullifiers (prepared : Prepared deployment profile ambient durable ingress checked) : List StableNullifier :=
  operationNullifier deployment.domain profile.semantics ingress :: prepared.legs.nullifiers

end Preparation

section Receiver
variable {F : Type} [Field F] [DecidableEq F]

structure AcceptedClaim (deployment : Deployment) (profile : CanonicalRuntimeProfile.Profile F)
    (ambient : Ambient) (durable : Durable) (ingress : DecodedIngress) where
  private mk ::
  checked : Checked deployment.domain profile.semantics ingress
  prepared : Prepared deployment profile ambient durable ingress checked
  semantic : prepared.SemanticAccepted
  physical : PhysicalShape prepared

def admitDecodedNative (deployment : Deployment) (profile : CanonicalRuntimeProfile.Profile F)
    (ambient : Ambient) (seed : Digest) (durable : Durable) (native : CredentialSignatureIO.NativeConfig)
    (ingress : DecodedIngress) : IO (Except Reject (AcceptedClaim deployment profile ambient durable ingress)) := do
  match ← PayClaimCommand.verifyNative native deployment.domain profile.semantics ingress with
  | .error reason => return .error (.verifier reason)
  | .ok checked =>
    match prepare deployment profile ambient seed durable ingress checked with
    | .error reason => return .error reason
    | .ok prepared =>
      if physical : PhysicalShape prepared then
        match authorize prepared with
        | .error reason => return .error reason
        | .ok semantic => return .ok ⟨checked, prepared, semantic, physical⟩
      else return .error .physicalPreparation

variable {deployment : Deployment} {profile : CanonicalRuntimeProfile.Profile F}
  {ambient : Ambient} {durable : Durable} {ingress : DecodedIngress}

def ingressBytes (ingress : DecodedIngress) : List UInt8 := PayClaimCommand.ingressCodec.encode ingress.ingress

def transactionId (domain semantics : Digest) (ingress : DecodedIngress) : Digest :=
  marker domain semantics ingress.command

def event (domain semantics : Digest) (ingress : DecodedIngress) : StableEvent where
  codecVersion := 1
  domain := domain
  eventId := (Sp800185Cshake256.hash "DREGG/PAY/CLAIM/EVENT/v1".toUTF8.toList
    (digestStream.encode domain ++ digestStream.encode semantics ++ bytesStream.encode (ingressBytes ingress))).digest
  canonicalBytes := ingressBytes ingress

def charge (accepted : AcceptedClaim deployment profile ambient durable ingress) : ResourceCost.Charge
  | .incidences => (writes accepted.prepared).length
  | .turnBytes => (ingressBytes ingress).length
  | .memoryTouches => (writes accepted.prepared).length + (readGuards accepted.prepared).length
  | .storageBytes => ((writes accepted.prepared).map fun write => write.canonicalPostBytes.length).sum
  | .witnessBytes => ingress.ingress.possessionSignature.length
  | .proofWork => 1
  | .feeDebit | .networkBytes | .sideEffectCount | .leaseByteBlocks => 0

def intent (accepted : AcceptedClaim deployment profile ambient durable ingress) : DataIntent rootBytes where
  transactionId := transactionId deployment.domain profile.semantics ingress
  subject := some (subject ingress.command)
  writes := writes accepted.prepared
  readGuards := readGuards accepted.prepared
  nullifiers := nullifiers accepted.prepared
  exactCharge := charge accepted
  event := event deployment.domain profile.semantics ingress
  postRootsBound := accepted.physical.2.2.2.1
  guardsReadOnly := readGuards_readonly accepted.prepared

structure Receipt where
  transactionId : Digest
  eventId : Digest
  deriving DecidableEq, Repr

def receipt (domain semantics : Digest) (ingress : DecodedIngress) : Receipt :=
  ⟨transactionId domain semantics ingress, (event domain semantics ingress).eventId⟩

/-- Recovery is an exact retained-ingress lookup, before current freshness,
pricing, custody or law decisions. A different event at this transaction ID is
conflict rather than success. No lookup calls receiveLoaded. -/
def replay (domain semantics : Digest) (durable : Durable) (ingress : DecodedIngress) : Option (Except Unit Receipt) :=
  match DurableCommitProtocol.Snapshot.lookupRecorded (transactionId domain semantics ingress) durable.snapshot.model.journal with
  | none => none
  | some recorded =>
    if recorded.transactionId = transactionId domain semantics ingress ∧
        recorded.event.event = event domain semantics ingress ∧
        recorded.nullifiers.head? = some (operationNullifier domain semantics ingress) then
      some (.ok (receipt domain semantics ingress))
    else some (.error ())

inductive Result where
  | confirmed (kind : DurableReceiverIO.Confirmation) (receipt : Receipt)
  | rejected (reason : Reject)
  | transactionConflict
  | durableRejected (reason : DurableDataIntent.RejectReason)
  | contention | unavailable (detail : String) | uncertain (detail : String)

def receiveLoaded (deployment : Deployment) (profile : CanonicalRuntimeProfile.Profile F)
    (ambient : Ambient) (seed : Digest) (native : CredentialSignatureIO.NativeConfig)
    (transport : DurableReceiverIO.Transport) (durable : Durable) (bytes : List UInt8) : IO Result := do
  let some ingress := decodeIngress bytes | return .rejected .malformedIngress
  match replay deployment.domain profile.semantics durable ingress with
  | some (.ok prior) => return .confirmed .replayed prior
  | some (.error _) => return .transactionConflict
  | none =>
    match ← admitDecodedNative deployment profile ambient seed durable native ingress with
    | .error reason => return .rejected reason
    | .ok accepted =>
      match ← DurableReceiverIO.receiveLoaded transport rootBytes durable (intent accepted) with
      | .confirmed kind _ => return .confirmed kind (receipt deployment.domain profile.semantics ingress)
      | .rejected reason => return .durableRejected reason
      | .contention => return .contention
      | .unavailable detail => return .unavailable detail
      | .uncertain detail => return .uncertain detail

theorem accepted_source_gate (accepted : AcceptedClaim deployment profile ambient durable ingress) :
    PayClaimDecision.decide accepted.prepared.pay.cell.logical accepted.prepared.authority.snapshot
      accepted.prepared.clock.clock (pricingAt deployment profile ambient accepted.prepared.expectedSeed
        accepted.prepared.authority.snapshot ingress.command) ingress accepted.checked =
        .ok accepted.prepared.decision := accepted.prepared.decided

theorem atomic_index_and_value (accepted : AcceptedClaim deployment profile ambient durable ingress) :
    (intent accepted).writes = accepted.prepared.pay.write accepted.prepared.payPost ::
      accepted.prepared.legs.writes accepted.prepared.factory := rfl

theorem accepted_current_law (accepted : AcceptedClaim deployment profile ambient durable ingress) :
    ∃ graph : PolicyComponentResolution.LoadedGraph
        (policyConfig accepted.prepared).snapshot (policyConfig accepted.prepared).store
        (policyConfig accepted.prepared).profile.semantics (policyConfig accepted.prepared).target
        (policyConfig accepted.prepared).additional,
      PolicyComponentResolution.loadTarget (policyConfig accepted.prepared).snapshot
        (policyConfig accepted.prepared).store (policyConfig accepted.prepared).profile.semantics
        (policyConfig accepted.prepared).target (policyConfig accepted.prepared).resolutionBudget
        (policyConfig accepted.prepared).additional = .ok graph ∧
      Minidregg.Pred.eval (ResolvedLawCompilation.predicate graph.resolved)
        (step accepted.prepared).oldState (step accepted.prepared).newState = true := by
  exact ComposedPolicyAdmission.authorized_effective_law (policyConfig accepted.prepared)
    (wanted accepted.prepared) accepted.semantic.authorization

end Receiver
end Minidregg.Kernel.PayClaimReceiver
