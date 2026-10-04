/-
Compiled Mini host. The operator selects one config at startup. Binary calls
and replies use Lean's strict source-owned codecs; this process never handles
private signing keys. `assemble` combines detached custody signatures only.

stdio framing: four-byte little-endian length, then one operation byte and
payload. 0=describe, 1=authorized prepare, 2=submit, 3=lookup, 4=challenge (a pair:
intent bytes, the subject's signature over them),
5=authorized query, 20=owner-signed selected-public-release submit,
 21=selected-release lookup, 22=descriptor-bound lifecycle begin submit,
 23=lifecycle begin receipt-only lookup, 24=selected source publication submit,
25=selected source publication lookup, 26=fresh descriptor-bound lifecycle claim,
27=lifecycle claim receipt-only lookup, 28=app share issue submit,
29=app share issue lookup, 34=fresh checked dispatch permit,
35=historical dispatch receipt-only lookup, 36=private dispatch signing plan,
37=private detached dispatch assembly, 38=checked lifecycle completion submit,
39=lifecycle completion receipt-only lookup, 40=fn consumer namespace submit,
41=fn consumer namespace receipt-only lookup, 42=operator-private namespace plan,
43=operator-private namespace assembly, 44=operator-private completion plan,
45=operator-private completion assembly, 50=operator-private resident BEGIN plan,
51=operator-private resident BEGIN assembly, 52=operator-private lifecycle claim
plan, 53=operator-private lifecycle claim assembly, 46=fresh paid agent dispatch,
47=paid agent dispatch receipt-only lookup, 48=private paid dispatch plan,
49=private paid dispatch assembly, 58=private agent reserve plan,
59=private agent reserve assembly, 60=selected fn coverage submit,
61=selected fn coverage receipt-only lookup, 62=empty fn progress submit,
63=empty fn progress receipt-only lookup, 64=private fn frontier plan,
65=private fn frontier detached assembly, 66=private source-bound launch BEGIN
plan, 67=private source-bound launch BEGIN detached assembly, 68=private launch
claim plan, 69=private launch claim detached assembly, 70=private launch completion plan,
71=private launch completion detached assembly, 72=grant issue submit,
73=grant issue receipt-only lookup, 74=private grant issue plan,
75=private grant issue detached assembly, 76=fresh grant-bound paid agent dispatch,
77=lifetime dispatch receipt-only lookup, 78=private lifetime paid plan,
79=private lifetime paid assembly, 80=private lifetime reserve plan,
81=private lifetime reserve assembly. Op34/46/76 success uses a distinct
82=private session enrollment plan, 83=private detached enrollment assembly,
84=checked session enrollment submit, 85=receipt-only enrollment lookup,
86=private participant key enrollment plan, 87=private detached key assembly,
88=checked participant key enrollment submit, 89=receipt-only key lookup,
91=current resource birth intent from verified history.
201=explicit reserve resource birth plan with independent current owner consent,
202=detached reserve resource birth assembly; ordinary birth91 stays unchanged.
96=private fleet turn plan behind a signed account observation, 97=detached fleet
assembly, 98=checked fleet turn submit, 99=receipt-only fleet lookup, 100=topic
poll since a cursor behind a signed account observation, 101=agent fleet head
behind a signed account observation, 102=exact receipt by transaction id,
180=incoming ledger: fleet turns that paid the observed account (P-CREDIT),
103=pay command signing plan (either pay family), 104=pay detached assembly,
105=pay submit, 106=pay receipt-only lookup, 107=public pay-cell view,
108=payment observation signing plan, 109=observation detached assembly,
110=observation submit, 111=observation receipt-only lookup,
112=public enrollment view (`DREGG/PAY/ENROLMENT-VIEW/v3`, with the journal),
113=purse refill signing plan, 114=refill detached assembly,
115=refill submit, 116=refill receipt-only lookup,
117=self-enrollment signing plan, 118=self-enrollment detached assembly,
119=self-enrollment submit, 120=self-enrollment receipt-only lookup.
121=public enrollment/renewal quote (bounded JSON request and response).
181=exact paid status, 182=v2 quote, 183=closed claim signing plan,
184=claim signature assembly, 185=claim submit, 186=exact claim lookup.
123=realm well signing plan, 124=realm well detached assembly,
125=realm well submit (non-confirmed outcomes reply 255),
126=clock tick signing plan, 127=clock tick detached assembly,
128=clock tick submit, 129=public clock view.
160=job money (fund/claim/settle) signing plan, 161=job money detached assembly,
162=job money submit (blind, as 115), 163=job money receipt-only lookup.
170=certify signing plan, 171=certify detached assembly, 172=certify submit,
173=public system view (certified head, tail bound, current head and chain).

131=Nock program check (pair: minimal jam bytes, ABI JSON) -> JSON verdict and the
canonical DREGG/PROGRAM/v1 bytes a `storage: "nock"` birth carries,
132=Nock program show (decimal programId) -> JSON, 133=Nock sample (JSON request)
-> JSON with the kernel's canonical sample jam, 134=Nock run dry run (JSON
{programId, caller, room, targets, values}) -> JSON with the kernel's sample at
the Host's logical height, the oracle's verdict, Lean steps, output and decoded
writes. 135=NockApp door poke dry run (JSON: programId, the instance's state jam
atom or null and event number, wire and cause jams) -> JSON with the sample,
Lean steps, output and the writes a claim names; 136=door peek (JSON with a path
jam) -> the peek arm's answer; 137=door state (JSON) -> the instance's state now
(stored, or the booted trap's). 131-137 only read the Store.
140=public subject key rotation plan, 141=rotation detached assembly,
142=rotation submit, 143=rotation receipt-only lookup, 144=public key status
(JSON query of a subject and one public key the asker holds; JSON reply).
Op34/46/76 success uses a distinct
committed-permit frame; other submit outcomes carry a strict Outcome.
The frame limit is FnEvidenceCodec.maxHostFrameBytes. EOF at a
frame boundary ends normally; truncated/oversized/unknown frames terminate.
-/
import Kernel.NativeHost
import Compiler.GenericSimplexSourceAnchor
import Kernel.NativeHostObjectAudience
import Kernel.NativeHostSession
import Kernel.NativeReserveContinuity
import Kernel.NativeProviderHistory
import Kernel.NativePlanHeight
import Kernel.NativeHostGenesis
import Kernel.FnEvidence
import Kernel.FnConsumerOperation
import Kernel.FnConsumerProgress
import Kernel.FnConsumerNamespaceReceiver
import Kernel.FnSelectedPollReceiver
import Kernel.FnEmptyPollReceiverV2
import Kernel.FnCatalogOwnRProgress
import Kernel.FnReplyPublication
import Kernel.FnReplyConsumption
import Kernel.FnOriginOutbox
import Kernel.FnPortableSource
import Kernel.FnSelectiveReleaseReceiver
import Kernel.ApplicationShareIssueReceiver
import Kernel.ApplicationShareIssueAuthoring
import Kernel.ApplicationShareIssueGrainAuthoring
import Kernel.ApplicationShareIssueGrainReceiver
import Kernel.ApplicationShareIssueGrainLookup
import Kernel.ApplicationGrainSessionEnrollmentReceiver
import Kernel.ApplicationAgentLifetimeGrantLookup
import Kernel.ApplicationDispatchReceiver
import Kernel.ApplicationDispatchLookup
import Kernel.ApplicationDispatchAgentReceiver
import Kernel.ApplicationDispatchAgentLookup
import Kernel.ApplicationDispatchAgentPaidAuthoring
import Kernel.ApplicationAgentLifetimeDispatchReceiver
import Kernel.ApplicationAgentLifetimeDispatchLookup
import Kernel.ApplicationAgentLifetimeDispatchPaidAuthoring
import Kernel.ApplicationDispatchAuthoring
import Kernel.ApplicationLifecycleBeginV2Receiver
import Kernel.ApplicationLifecycleBeginV3Receiver
import Kernel.ApplicationLifecycleClaimV2Receiver
import Kernel.ApplicationLifecycleClaimV3Receiver
import Kernel.ApplicationLifecycleV2Lookup
import Kernel.ApplicationLifecycleV3Lookup
import Kernel.ApplicationLifecycleCompletionReceiver
import Kernel.ApplicationLifecycleCompletionV2Receiver
import Host.ApplicationFailedStartEndpoint
import Kernel.ApplicationLifecycleCompletionLookup
import Kernel.ApplicationLifecycleCompletionV2Lookup
import Host.ApplicationDispatchReady
import Host.ApplicationDispatchInspection
import Host.ReceiptContinuity
import Host.ApplicationStreamContinuityInspection
import Host.ApplicationRouteAdmissionInspection
import Host.CarryInspection
import Host.NeutralCarryReceiving
import Host.KeyCommitmentAdoptionInspection
import Host.RetainedSegmentInspection
import Kernel.CarriedNativeHostSession
import Kernel.CarriedSessionEnrollmentReceiver
import Kernel.CarriedApplicationDispatchReceiver
import Host.ApplicationDispatchAgentPaidInspection
import Host.ApplicationDispatchAgentInspection
import Host.ApplicationAgentLifetimeDispatchInspection
import Host.ApplicationAgentLifetimeDispatchPaidInspection
import Host.ApplicationLifecycleClaimInspection
import Host.ApplicationLifecycleCompletionOperator
import Host.ApplicationLifecycleBeginOperator
import Host.DryRun
import Host.RequestRefusal
import Host.LawSatWire
import Host.ApplicationLifecycleLaunchBeginAuthoring
import Host.ApplicationLifecycleLaunchBeginInspection
import Host.ApplicationLifecycleLaunchClaimAuthoring
import Host.ApplicationLifecycleLaunchClaimInspection
import Host.ApplicationLifecycleLaunchCompletionAuthoring
import Host.ApplicationLifecycleLaunchCompletionInspection
import Host.ApplicationLifecycleClaimV3Inspection
import Host.ApplicationLifecycleStopClaimInspection
import Host.ApplicationAgentLifetimePaidIngressInspection
import Host.ApplicationAgentLifetimeGrantInspection
import Host.ApplicationGrainSessionEnrollmentAuthoring
import Host.ApplicationGrainSessionEnrollmentInspection
import Host.ApplicationLifecycleClaimOperator
import Host.FnConsumerNamespacePlan
import Host.FnConsumerFrontierPlan
import Kernel.FnSelectiveReleaseSourceReceiver
import Host.FnSelectiveReleaseAuthoring
import Host.FnSelectiveReleaseSourceAuthoring
import Host.FnSelectiveReleaseFnReceiving
import Host.FnSelectiveReleaseFnAck
import Host.Json
import Kernel.ObjectiveBendNativeAdmission
import Host.ObjectiveInvocationQuote
import Host.ObjectiveInvocationSettings
import Host.ObjectivePackageAuthor
import Host.PayClaims
import Host.ApplicationCurrentBirthAuthoring
import Host.CurrentResourceBirthAuthoring
import Kernel.NativeHostReserveBirth
import Host.NativeReserveBirthAuthoring
import Host.FnInboxView
import Host.GrainOriginCommand
import Host.ProviderUsage
import Lean.Data.Json

open Lean
open Minidregg.Compiler
open Minidregg.Compiler.NativeHostCodec
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Kernel

namespace Minidregg.Host

structure GatewayPinSettings where
  application : String
  subject : Nat
  target : Nat
  capability : Nat
  policyAddress : Nat

instance : FromJson GatewayPinSettings where
  fromJson? json := do
    let object ← json.getObj?
    let expected := ["application", "subject", "target", "capability", "policyAddress"]
    let actual := object.foldl (init := []) (fun fields key _ => key :: fields)
    unless actual.length == expected.length && actual.all expected.contains do
      throw "fn gateway pin has missing or unknown fields"
    let application ← json.getObjValAs? String "application"
    let subject ← json.getObjValAs? Nat "subject"
    let target ← json.getObjValAs? Nat "target"
    let capability ← json.getObjValAs? Nat "capability"
    let address ← json.getObjValAs? String "policyAddress"
    let some policyAddress := address.toNat?
      | throw "fn gateway policyAddress must be canonical decimal string"
    unless toString policyAddress == address do
      throw "fn gateway policyAddress must be canonical decimal string"
    return ⟨application, subject, target, capability, policyAddress⟩

instance : ToJson GatewayPinSettings where
  toJson source := Lean.Json.mkObj
    [("application", toJson source.application),
     ("subject", toJson source.subject),
     ("target", toJson source.target),
     ("capability", toJson source.capability),
     ("policyAddress", toJson (toString source.policyAddress))]

def GatewayPinSettings.pin (source : GatewayPinSettings) : NativeHost.FnGatewayPin :=
  ⟨source.application.toUTF8.toList, ⟨source.subject⟩, source.target,
    ⟨source.capability⟩, ⟨source.policyAddress⟩⟩

/-- Paths are operator configuration, never fields in a client frame. The
service copies the four bounded manifests into its private lifetime directory
before accepting frames; the fn control endpoint remains an OS custody seam. -/
structure FnPollServiceSettings where
  originConfigPath : String
  fnPinPath : String
  scopePath : String
  policyPath : String
  controlPath : String
  deriving FromJson, ToJson

structure FnPollService where
  originConfigPath : String
  fnPinPath : String
  fnExecutable : String
  fnPublicKey : String
  scopePath : String
  policyPath : String
  controlPath : String

/-- The A reply consumer has a fixed R origin carrier and a separate live Q
consumer. None of these paths is accepted from a stdio request. -/
structure FnReplyPollServiceSettings where
  originConfigPath : String
  rPinPath : String
  rClaimPath : String
  rCarrierPath : String
  qPinPath : String
  scopePath : String
  qClaimPath : Option String := none
  policyPath : String
  controlPath : String
  deriving FromJson, ToJson

structure FnReplyPollService where
  originConfigPath : String
  rPinPath : String
  rExecutable : String
  rPublicKey : String
  rClaimPath : String
  rCarrierPath : String
  qPinPath : String
  qExecutable : String
  qPublicKey : String
  scopePath : String
  policyPath : String
  controlPath : String

/-- The long-lived A service selects each prepared R from admitted Mini
history. The operator pins only the origin verifier and Q consumer context;
no individual R pathname is part of this service or a client frame. -/
structure FnReplyCatalogServiceSettings where
  originConfigPath : String
  rPinPath : String
  qPinPath : String
  scopePath : String
  policyPath : String
  controlPath : String
  deriving FromJson, ToJson

structure FnReplyCatalogService where
  originConfig : NativeHost.Config
  rPinPath : String
  rExecutable : String
  rPublicKey : String
  qPinPath : String
  qExecutable : String
  qPublicKey : String
  scopePath : String
  policyPath : String
  controlPath : String

/-- Operator-pinned source-owned metering context. The socket caller can
submit exact retained HTTP bytes but cannot select the provider cell or tariff. -/
structure ProviderMeteringSettings where
  providerResourceId : Nat
  tariff : Lean.Json
  deriving FromJson, ToJson

structure GrainBirthTariffSettings where
  base : Nat
  perBirth : Nat
  deriving FromJson, ToJson

/-- Optional exact consensus membership/epoch/source-origin pin. The JSON value
is canonical lowercase hex of contextStream, never a committee supplied by an
incoming proposal. Malformed explicit pins refuse instead of becoming none. -/
structure JointConsensusSettings where
  context : Minidregg.Compiler.GenericSimplexCodec.Context

instance : FromJson JointConsensusSettings where
  fromJson? json := do
    let value ← json.getStr?
    let bytes ← Minidregg.Host.Json.decodeHex "jointConsensus" json
    unless Minidregg.Host.Json.encodeHex bytes == value do
      throw "jointConsensus must use canonical lowercase hex"
    let some context := Minidregg.Compiler.GenericSimplexCodec.contextStream.toLawful.decode bytes
      | throw "jointConsensus is not a canonical Context"
    unless Minidregg.Compiler.GenericSimplexCodec.contextStream.encode context == bytes &&
        context.wellFormed do
      throw "jointConsensus Context is noncanonical or committee is not well formed"
    pure ⟨context⟩

instance : ToJson JointConsensusSettings where
  toJson pin := .str (Minidregg.Host.Json.encodeHex
    (Minidregg.Compiler.GenericSimplexCodec.contextStream.encode pin.context))

/-- Operator configuration pins the physical completion custodian's exact
Ed25519 public key. It is never selected by an incoming request. -/
structure CompletionCustodianKeySettings where
  bytes : List UInt8
  deriving Repr

instance : FromJson CompletionCustodianKeySettings where
  fromJson? json := do
    let value ← json.getStr?
    unless value.length == 64 do
      throw "completionCustodianKey must be 32 bytes of canonical lowercase hex"
    let bytes ← Minidregg.Host.Json.decodeHex "completionCustodianKey" json
    unless bytes.length == 32 &&
        Minidregg.Host.Json.encodeHex bytes == value do
      throw "completionCustodianKey must be 32 bytes of canonical lowercase hex"
    pure ⟨bytes⟩

instance : ToJson CompletionCustodianKeySettings where
  toJson value := .str (Minidregg.Host.Json.encodeHex value.bytes)

/-- Operator-pinned lifecycle management identity. It is one signing subject
and key for every application the operator manages; it names no application.
Each lifecycle authoring request (ops 44/50/52/66/68/70) carries a
`LifecycleSelector` naming the application resources and the management
capabilities. The selector confers nothing: the receiver's current app and
package law (`request/subject == managementSubject`, linking the exact package
and snapshot manifests) and capability admission decide whether this identity
may manage that application. -/
structure LifecycleManagementSettings where
  managementSubject : Nat
  managementKeyId : Nat
  deriving ToJson

instance : FromJson LifecycleManagementSettings where
  fromJson? json := do
    let object ← json.getObj?
    let expected := ["managementSubject", "managementKeyId"]
    let actual := object.foldl (init := []) (fun fields key _ => key :: fields)
    unless actual.length == expected.length && actual.all expected.contains do
      throw "lifecycleManagement has missing or unknown fields"
    return ⟨← json.getObjValAs? Nat "managementSubject",
      ← json.getObjValAs? Nat "managementKeyId"⟩

/-- Request-supplied application coordinates for one lifecycle authoring call.
Fields are canonical decimal strings so full-width identifiers are exact. -/
structure LifecycleSelector where
  app : Nat
  packageManifest : Nat
  snapshotManifest : Nat
  appCapability : Nat
  appObserveCapability : Nat
  packageCapability : Nat
  packageObserveCapability : Nat

def canonicalDecimal? (text : String) : Option Nat :=
  if text.isEmpty || text.length > 78 || (text.length > 1 && text.front == '0') ||
      !text.all Char.isDigit then none
  else text.toNat?

instance : FromJson LifecycleSelector where
  fromJson? json := do
    let object ← json.getObj?
    let expected := ["app", "packageManifest", "snapshotManifest", "appCapability",
      "appObserveCapability", "packageCapability", "packageObserveCapability"]
    let actual := object.foldl (init := []) (fun fields key _ => key :: fields)
    unless actual.length == expected.length && actual.all expected.contains do
      throw "lifecycle selector has missing or unknown fields"
    let field := fun (name : String) => do
      let text ← json.getObjValAs? String name
      let some value := canonicalDecimal? text
        | throw s!"lifecycle selector {name} is not a canonical decimal"
      pure value
    return ⟨← field "app", ← field "packageManifest", ← field "snapshotManifest",
      ← field "appCapability", ← field "appObserveCapability",
      ← field "packageCapability", ← field "packageObserveCapability"⟩

def LifecycleSelector.parse (bytes : List UInt8) : Except String LifecycleSelector := do
  unless 0 < bytes.length && bytes.length ≤ 4096 do
    throw "lifecycle selector size refused"
  let some text := String.fromUTF8? (ByteArray.mk bytes.toArray)
    | throw "lifecycle selector is not UTF-8"
  let json ← Minidregg.Host.Json.parse text
  fromJson? json

def LifecycleSelector.completionPin (selector : LifecycleSelector)
    (management : LifecycleManagementSettings) :
    ApplicationLifecycleCompletionOperator.Pin :=
  { app := selector.app
    packageManifest := selector.packageManifest
    managementSubject := management.managementSubject
    managementKeyId := management.managementKeyId
    appCapability := ⟨selector.appCapability⟩
    appObserveCapability := ⟨selector.appObserveCapability⟩
    packageCapability := ⟨selector.packageCapability⟩
    packageObserveCapability := ⟨selector.packageObserveCapability⟩ }

def LifecycleSelector.beginPin (selector : LifecycleSelector)
    (management : LifecycleManagementSettings) :
    ApplicationLifecycleBeginOperator.Pin :=
  { app := selector.app
    packageManifest := selector.packageManifest
    snapshotManifest := selector.snapshotManifest
    managementSubject := management.managementSubject
    managementKeyId := management.managementKeyId
    appCapability := ⟨selector.appCapability⟩
    packageObserveCapability := ⟨selector.packageObserveCapability⟩ }

def LifecycleSelector.claimPin (selector : LifecycleSelector)
    (management : LifecycleManagementSettings) :
    ApplicationLifecycleClaimOperator.Pin :=
  { app := selector.app
    packageManifest := selector.packageManifest
    managementSubject := management.managementSubject
    managementKeyId := management.managementKeyId
    appCapability := ⟨selector.appCapability⟩
    appObserveCapability := ⟨selector.appObserveCapability⟩
    packageObserveCapability := ⟨selector.packageObserveCapability⟩ }

/-- Operator custody pins all non-HTTP selectors and the reserve/charge cap
before any event21 signing headers are exposed. HTTP bytes and the fresh
reserve operation ID vary, but the private signer must separately approve
their exact source-inspected request and headers. -/
structure AgentDispatchFixedSettings where
  issueIndex : Nat
  ticketResource : Nat
  packageManifest : Nat
  snapshotManifest : Nat
  sessionObserve : Nat
  manifestObserve : Nat
  enrollmentObserve : Nat
  parentTask : Nat
  parentCapability : Nat
  parentObserve : Nat
  purseTask : Nat
  purseCapability : Nat
  purseObserve : Nat
  payerSubject : Nat
  reserveAmount : Int
  maximumCharge : Int
  deriving ToJson, DecidableEq

instance : FromJson AgentDispatchFixedSettings where
  fromJson? json := do
    let object ← json.getObj?
    let expected := ["issueIndex", "ticketResource", "packageManifest",
      "snapshotManifest", "sessionObserve", "manifestObserve",
      "enrollmentObserve", "parentTask", "parentCapability",
      "parentObserve", "purseTask", "purseCapability", "purseObserve",
      "payerSubject", "reserveAmount", "maximumCharge"]
    let actual := object.foldl (init := []) (fun fields key _ => key :: fields)
    unless actual.length == expected.length && actual.all expected.contains do
      throw "agentDispatchFixed has missing or unknown fields"
    return ⟨← json.getObjValAs? Nat "issueIndex",
      ← json.getObjValAs? Nat "ticketResource",
      ← json.getObjValAs? Nat "packageManifest",
      ← json.getObjValAs? Nat "snapshotManifest",
      ← json.getObjValAs? Nat "sessionObserve",
      ← json.getObjValAs? Nat "manifestObserve",
      ← json.getObjValAs? Nat "enrollmentObserve",
      ← json.getObjValAs? Nat "parentTask",
      ← json.getObjValAs? Nat "parentCapability",
      ← json.getObjValAs? Nat "parentObserve",
      ← json.getObjValAs? Nat "purseTask",
      ← json.getObjValAs? Nat "purseCapability",
      ← json.getObjValAs? Nat "purseObserve",
      ← json.getObjValAs? Nat "payerSubject",
      ← json.getObjValAs? Int "reserveAmount",
      ← json.getObjValAs? Int "maximumCharge"⟩

def AgentDispatchFixedSettings.selectors (settings : AgentDispatchFixedSettings) :
    ApplicationDispatchAgentPaidAuthoring.FixedSelectors :=
  { issueIndex := settings.issueIndex
    ticketResource := settings.ticketResource
    packageManifest := settings.packageManifest
    snapshotManifest := settings.snapshotManifest
    sessionObserve := ⟨settings.sessionObserve⟩
    manifestObserve := ⟨settings.manifestObserve⟩
    enrollmentObserve := ⟨settings.enrollmentObserve⟩
    parentTask := settings.parentTask
    parentCapability := ⟨settings.parentCapability⟩
    parentObserve := ⟨settings.parentObserve⟩
    purseTask := settings.purseTask
    purseCapability := ⟨settings.purseCapability⟩
    purseObserve := ⟨settings.purseObserve⟩
    payerSubject := ⟨settings.payerSubject⟩
    reserveAmount := settings.reserveAmount
    maximumCharge := settings.maximumCharge }

/-- Event26 has an additional fixed grant selector. Its payer and dispatchTask
selectors remain the existing operator-approved event21 set. -/
structure AgentLifetimeDispatchFixedSettings where
  legacy : AgentDispatchFixedSettings
  grantIssueIndex : Nat
  grantResource : Nat
  grantObserveCapability : Nat
  deriving ToJson, DecidableEq

instance : FromJson AgentLifetimeDispatchFixedSettings where
  fromJson? json := do
    let object ← json.getObj?
    let expected := ["legacy", "grantIssueIndex", "grantResource", "grantObserveCapability"]
    let actual := object.foldl (init := []) (fun fields key _ => key :: fields)
    unless actual.length == expected.length && actual.all expected.contains do
      throw "agentLifetimeDispatchFixed has missing or unknown fields"
    return ⟨← json.getObjValAs? AgentDispatchFixedSettings "legacy",
      ← json.getObjValAs? Nat "grantIssueIndex",
      ← json.getObjValAs? Nat "grantResource",
      ← json.getObjValAs? Nat "grantObserveCapability"⟩

def AgentLifetimeDispatchFixedSettings.selectors
    (settings : AgentLifetimeDispatchFixedSettings) :
    ApplicationAgentLifetimeDispatchPaidAuthoring.FixedSelectors :=
  { legacy := settings.legacy.selectors
    grantIssueIndex := settings.grantIssueIndex
    grantResource := settings.grantResource
    grantObserveCapability := ⟨settings.grantObserveCapability⟩ }

structure Settings where
  /-- Operator-local carry registry and independently authorized handoff key.
  Neither value can be selected by a network frame. -/
  carryRegistry : Option String := none
  carryOperatorKey : Option String := none
  domain : Nat
  federation : Nat
  factoryId : Nat
  resourceBookId : Nat
  authorityCellId : Nat
  issuer : Nat
  ownerBudget : Nat
  lifetime : Nat
  /-- Heights a birth may land after its authored `notBefore`; default
  `CanonicalRuntimeProfile.defaultBirthSlack`. Part of the semantics digest. -/
  birthSlack : Option Nat := none
  tariffBase : Nat
  tariffPerBirth : Nat
  tariffPerGrant : Nat
  tariffPerInitialPayloadByte : Nat
  collector : Nat
  asset : Nat
  genesisHeight : Nat
  expectedSeed : Nat
  storageBinary : String
  storageRoot : String
  signatureBinary : String
  /-- The Store's checkpoint/log MAC key file (32 bytes, mode 0600), generated
  by `mini bootstrap` beside the pinned configuration; one per Store. -/
  checkpointKey : Option String := none
  /-- Checkpoint cadence in accepted records (default 64). -/
  checkpointEvery : Option Nat := none
  fnGateway : Option GatewayPinSettings := none
  fnPoll : Option FnPollServiceSettings := none
  fnReplyPoll : Option FnReplyPollServiceSettings := none
  fnReplyCatalog : Option FnReplyCatalogServiceSettings := none
  continuityProviderResourceId : Option Nat := none
  providerMetering : Option ProviderMeteringSettings := none
  providerServices : Option (List ProviderMeteringSettings) := none
  grainBirthTariff : Option GrainBirthTariffSettings := none
  completionCustodianKey : Option CompletionCustodianKeySettings := none
  jointConsensus : Option JointConsensusSettings := none
  objectiveInvocation : Option ObjectiveInvocationSettings := none
  lifecycleManagement : Option LifecycleManagementSettings := none
  agentDispatchFixed : Option AgentDispatchFixedSettings := none
  agentLifetimeDispatchFixed : Option AgentLifetimeDispatchFixedSettings := none
  agentLifetimeDispatchServices : Option (List AgentLifetimeDispatchFixedSettings) := none
  /-- The operator's synchronous run budget in Lean steps (default
  `NativeHost.defaultNockFSync`, C17's measured 1,000,000). -/
  nockFSync : Option Nat := none
  /-- Compiled-in evaluators (by registry name, e.g. `"nock"`) this operator disabled;
  committed in the runtime semantics, so `expectedSemantics` must be computed with the same
  list. A name the registry lacks refuses the config (`loadSettings`). -/
  disabledEvaluators : Option (List String) := none
  deriving FromJson, ToJson

/-- The disabled evaluators' registry ids, by name. `loadSettings` refuses a name the registry
lacks (`Settings.checkDisabledEvaluators`), so the fallback below — an id derived from the
name, which no compiled-in entry has, so it disables nothing — is never reached by a loaded
config; it is deterministic, never an empty list standing in for a refusal. -/
def Settings.disabledEvaluatorIds (settings : Settings) :
    List Minidregg.Theory.TypedAuthorization.Digest :=
  (settings.disabledEvaluators.getD []).map fun name =>
    (Minidregg.Compiler.Evaluator.resolveName name).getD (Minidregg.Compiler.Evaluator.idOf name "")

def Settings.checkDisabledEvaluators (settings : Settings) : Except String Unit :=
  (settings.disabledEvaluators.getD []).forM fun name =>
    if (Minidregg.Compiler.Evaluator.resolveName name).isSome then .ok ()
    else .error s!"disabledEvaluators: no compiled-in evaluator named {name}"

def Settings.config (settings : Settings) : NativeHost.Config where
  deployment := ⟨⟨settings.domain⟩, settings.factoryId, settings.resourceBookId, settings.authorityCellId⟩
  federation := ⟨settings.federation⟩
  disabledEvaluators := settings.disabledEvaluatorIds
  template := ⟨⟨settings.issuer⟩, settings.ownerBudget, settings.lifetime,
    settings.birthSlack.getD CanonicalRuntimeProfile.defaultBirthSlack⟩
  tariff := ⟨settings.tariffBase, settings.tariffPerBirth, settings.tariffPerGrant,
    settings.tariffPerInitialPayloadByte, settings.collector, settings.asset⟩
  genesisHeight := settings.genesisHeight
  expectedSeed := ⟨settings.expectedSeed⟩
  storage :=
    { binary := settings.storageBinary
      root := settings.storageRoot
      key := settings.checkpointKey.getD ""
      checkpointEvery := settings.checkpointEvery.getD 64 }
  signature := ⟨settings.signatureBinary⟩
  fnGateway := settings.fnGateway.map GatewayPinSettings.pin
  grainBirthTariff := settings.grainBirthTariff.map fun tariff =>
    ⟨tariff.base, tariff.perBirth⟩
  completionCustodianKey := settings.completionCustodianKey.map
    CompletionCustodianKeySettings.bytes
  nockFSync := settings.nockFSync.getD NativeHost.defaultNockFSync
  jointConsensus := settings.jointConsensus.map JointConsensusSettings.context
  invocationBindings := ObjectiveInvocationSettings.bindings settings.objectiveInvocation

/-- Check the complete declared source genesis before opening or authoring
under this profile. Membership enters runtime semantics with only the anchor
omitted; the exact anchor and its source policies must reconstruct together.
This pure check also works before the physical Store is initialized. -/
def Settings.checkJointConsensus (settings : Settings) : Except String Unit := do
  let some pin := settings.jointConsensus | return ()
  let config := settings.config
  unless pin.context.scope ==
      Minidregg.Compiler.Tower256ConcreteBackend.digestStream.encode config.deployment.domain do
    throw "jointConsensus scope differs from native deployment"
  let anchorTag := "MINI-SIMPLEX-SOURCE-GENESIS/v1".toUTF8.toList
  let some (height,seed) := Minidregg.Compiler.GenericSimplexSourceAnchor.anchorStream.toLawful.decode
      (pin.context.instanceBytes.drop anchorTag.length)
    | throw "jointConsensus requires an exact canonical source genesis anchor"
  unless height == config.genesisHeight &&
      Minidregg.Compiler.GenericSimplexSourceAnchor.anchorBytes height seed == pin.context.instanceBytes do
    throw "jointConsensus source anchor height or encoding mismatch"
  unless NativeHost.seedIdentity seed == config.expectedSeed do
    throw "jointConsensus source anchor differs from expectedSeed"
  let genesis ← Minidregg.Compiler.DurableReceiverIO.loadSeed
    Minidregg.Compiler.ResourceBirthCodec.rootBytes (config.logStart seed) seed
  let _ ← NativeHost.validateLoaded config genesis
  pure ()

def Settings.providerMeteringPin (settings : Settings) :
    Except String (Option (Nat × Kernel.ProviderMetering.Tariff)) := do
  let some metering := settings.providerMetering | return none
  unless metering.providerResourceId > 0 do
    throw "provider metering resource ID must be positive"
  if let some continuityId := settings.continuityProviderResourceId then
    unless continuityId == metering.providerResourceId do
      throw "provider metering and continuity resource IDs differ"
  let tariff ← ProviderUsage.parseTariff metering.tariff.compress
  return some (metering.providerResourceId, tariff)

/-- Bounded unique service table, parsed once from operator configuration. -/
def checkedProviderServices (services : List ProviderMeteringSettings) :
    Except String (List (Nat × Kernel.ProviderMetering.Tariff)) := do
  unless 0 < services.length && services.length ≤ 8 do
    throw "providerServices requires one to eight entries"
  let ids := services.map (·.providerResourceId)
  unless ids.all (fun id => decide (0 < id)) && decide ids.Nodup do
    throw "providerServices resource IDs must be positive and unique"
  services.mapM fun service => do
    let tariff ← ProviderUsage.parseTariff service.tariff.compress
    pure (service.providerResourceId, tariff)

/-- One operator-owned service list is shared by continuity and metering.
Legacy scalar pins remain byte-compatible but cannot be mixed with the list. -/
def Settings.providerServicePins (settings : Settings) :
    Except String (List (Nat × Kernel.ProviderMetering.Tariff)) := do
  let some services := settings.providerServices | return []
  unless settings.continuityProviderResourceId.isNone &&
      settings.providerMetering.isNone do
    throw "providerServices cannot be combined with legacy provider pins"
  checkedProviderServices services

/-- The per-operation fees of every pinned provider service, by resource:
the constants a provider purse born at that resource carries in its law. -/
def Settings.providerRoutes (settings : Settings) :
    Except String (List (Nat × Kernel.ProviderMetering.Schedule)) := do
  let legacy ← settings.providerMeteringPin
  let services ← settings.providerServicePins
  return (legacy.toList ++ services).map fun pin => (pin.1, pin.2.schedule)

def Settings.continuityIds (settings : Settings) : Except String (List Nat) := do
  if settings.providerServices.isSome then
    return (← settings.providerServicePins).map Prod.fst
  match settings.continuityProviderResourceId with
  | some resourceId =>
      unless resourceId > 0 do throw "provider continuity resource ID must be positive"
      return [resourceId]
  | none => return []

def checkedLifetimeDispatchServices (services : List AgentLifetimeDispatchFixedSettings) :
    Except String (List ApplicationAgentLifetimeDispatchPaidAuthoring.FixedSelectors) := do
  unless 0 < services.length && services.length ≤ 8 do
    throw "agentLifetimeDispatchServices requires one to eight entries"
  unless decide services.Nodup do
    throw "agentLifetimeDispatchServices contains duplicate full fixed selectors"
  return services.map AgentLifetimeDispatchFixedSettings.selectors

def Settings.lifetimeDispatchPins (settings : Settings) : Except String
    (List ApplicationAgentLifetimeDispatchPaidAuthoring.FixedSelectors) := do
  match settings.agentLifetimeDispatchServices with
  | some services =>
      unless settings.agentLifetimeDispatchFixed.isNone do
        throw "agentLifetimeDispatchServices cannot be combined with legacy pin"
      checkedLifetimeDispatchServices services
  | none =>
      return settings.agentLifetimeDispatchFixed.toList.map
        AgentLifetimeDispatchFixedSettings.selectors

def loadSettings (path : System.FilePath) : IO Settings := do
  let text ← IO.FS.readFile path
  let json ← IO.ofExcept (Minidregg.Host.Json.parse text)
  -- The single-application lifecycle pins were replaced by one management
  -- identity plus per-request selectors. An old config must not load as if
  -- its application pins still bounded what this operator may author.
  for legacy in ["completionManagement", "residentBeginManagement",
      "residentClaimManagement"] do
    if (json.getObjVal? legacy).toOption.isSome then
      throw (IO.userError s!"legacy single-application lifecycle pin {legacy} is no longer accepted; use lifecycleManagement")
  let settings : Settings ← IO.ofExcept (fromJson? json)
  discard <| IO.ofExcept settings.providerMeteringPin
  discard <| IO.ofExcept settings.providerServicePins
  discard <| IO.ofExcept settings.continuityIds
  discard <| IO.ofExcept settings.lifetimeDispatchPins
  IO.ofExcept settings.checkDisabledEvaluators
  IO.ofExcept settings.checkJointConsensus
  if let some tariff := settings.grainBirthTariff then
    unless 0 < tariff.base do
      throw (IO.userError "grainBirthTariff.base must be positive")
  pure settings

/-- Human-readable fn inbox projection is a pure presentation of the exact
native view bytes. Query authority remains with the signed native read. -/
def inspectHost (config : NativeHost.Config) (kind : String) (bytes : List UInt8) :
    Except String Lean.Json :=
  if kind == "fn-inbox-resource" then FnInboxView.render bytes
  else if kind == "application-route-admission-attestation" then
    ApplicationRouteAdmissionInspection.inspect bytes
  else if kind == "application-stream-continuity-attestation" then
    ApplicationStreamContinuityInspection.inspect bytes
  else if kind == "application-dispatch-committed" then
    ApplicationDispatchInspection.inspect bytes
  else if kind == "application-lifecycle-claim-committed-v2" then
    ApplicationLifecycleClaimInspection.inspect config.expectedSeed bytes
  else if kind == "application-lifecycle-claim-committed-v3" then
    ApplicationLifecycleClaimV3Inspection.inspect bytes
  else if kind == "subject-key-adoption-plan" then
    KeyCommitmentAdoptionInspection.inspectPlan bytes
  else if kind == "subject-key-adoption-ingress" then
    KeyCommitmentAdoptionInspection.inspectIngress bytes
  else if kind == "application-session-enrollment-request" then
    ApplicationGrainSessionEnrollmentInspection.inspectRequest bytes
  else if kind == "application-session-enrollment-plan" then
    ApplicationGrainSessionEnrollmentInspection.inspectPlan bytes
  else if kind == "application-session-enrollment-ingress" then
    ApplicationGrainSessionEnrollmentInspection.inspectIngress bytes
  else if kind == "fn-consumer-namespace-plan" then
    FnConsumerNamespacePlan.inspectPlanBytes bytes
  else if kind == "fn-consumer-frontier-plan" then
    FnConsumerFrontierPlan.inspectPlanBytes bytes
  else if kind == "application-agent-reserve-plan" then
    ApplicationDispatchAgentPaidInspection.inspectReservePlan bytes
  else if kind == "application-agent-paid-dispatch-plan" then
    ApplicationDispatchAgentPaidInspection.inspectPaidPlan bytes
  else if kind == "application-agent-dispatch-committed" then
    ApplicationDispatchAgentInspection.inspect bytes
  else if kind == "application-agent-lifetime-reserve-plan" then
    ApplicationAgentLifetimeDispatchPaidInspection.inspectReservePlan bytes
  else if kind == "application-agent-lifetime-paid-plan" then
    ApplicationAgentLifetimeDispatchPaidInspection.inspectPaidPlan bytes
  else if kind == "application-agent-lifetime-dispatch-committed" then
    ApplicationAgentLifetimeDispatchInspection.inspect bytes
  else if kind == "application-lifecycle-launch-begin-request" then
    ApplicationLifecycleLaunchBeginInspection.inspectRequest bytes
  else if kind == "application-lifecycle-launch-continue-request" then
    ApplicationLifecycleLaunchBeginInspection.inspectContinueRequest bytes
  else if kind == "application-lifecycle-launch-begin-plan" then
    ApplicationLifecycleLaunchBeginInspection.inspectPlan bytes
  else if kind == "application-lifecycle-launch-stop-plan" then
    ApplicationLifecycleLaunchBeginInspection.inspectStopPlan bytes
  else if kind == "application-lifecycle-launch-claim-request" then
    ApplicationLifecycleLaunchClaimInspection.inspectRequest bytes
  else if kind == "application-lifecycle-launch-claim-plan" then
    ApplicationLifecycleLaunchClaimInspection.inspectPlan bytes
  else if kind == "application-lifecycle-launch-completion-request" then
    ApplicationLifecycleLaunchCompletionInspection.inspectRequest bytes
  else if kind == "application-lifecycle-launch-completion-plan" then
    ApplicationLifecycleLaunchCompletionInspection.inspectPlan bytes
  else Minidregg.Host.Json.inspect kind bytes

/-- A STOP physical custodian may compare its retained op66 plan and fresh
op26 callback with one newly verified Mini image. This read-only join returns
the exact prior running event25 witness; it never mints a launch permit. -/
def inspectStopClaimCurrent (config : NativeHost.Config)
    (planBytes committedBytes : List UInt8) : IO (Except String Lean.Json) := do
  match ← DurableReceiverIO.load config.transport ResourceBirthCodec.rootBytes with
  | .error detail => return .error detail
  | .ok durable =>
      match ← NativeHostReplay.verifyLoaded config durable with
      | .error failure =>
          return .error s!"STOP claim history refused at entry {failure.index}: {failure.detail}"
      | .ok verified =>
          return ApplicationLifecycleStopClaimInspection.inspectVerified
            verified planBytes committedBytes

/-- Immutable operator-selected protocol metadata. Available before bootstrap;
this reads neither storage nor protected resource values. Full-width integers
are decimal strings so clients cannot silently round a digest. -/
def profileDescription (config : NativeHost.Config)
    (metering : Option (Nat × Kernel.ProviderMetering.Tariff) := none)
    (services : List (Nat × Kernel.ProviderMetering.Tariff) := []) : Lean.Json :=
  let n := fun value : Nat => toJson (toString value)
  let base :=
    [("runtime", toJson "minidregg-native"),
     -- Binary capability only: API17 exact-fence continuity plus canonical
     -- invocation height pinning. It is not a current admission receipt.
     ("providerContinuityAdmission", toJson "exact-height-v1"),
     ("semantics", n config.profile.semantics.value),
     ("domain", n config.deployment.domain.value),
     ("expectedSeed", n config.expectedSeed.value),
     -- The Store's key in physical names (resident units, volumes, slices):
     -- the SPK host reads it here and never derives its own.
     ("storeTag", toJson (Minidregg.Kernel.ApplicationLifecycleResidentProfile.storeTag
       config.expectedSeed)),
     ("federation", n config.federation.value),
     ("factoryId", n config.deployment.factoryId),
     ("resourceBookId", n config.deployment.resourceBookId),
     ("authorityCellId", n config.deployment.authorityCellId),
     ("fieldModulus", n NativeHostProfile.characteristic),
     ("orderDifferenceWidth", n NativeHostProfile.orderWidth),
     ("genesisHeight", n config.genesisHeight),
     ("template", Lean.Json.mkObj [("issuer", n config.template.issuer.value),
       ("ownerBudget", n config.template.ownerBudget), ("lifetime", n config.template.lifetime)]),
     ("tariff", Lean.Json.mkObj [("base", n config.tariff.base),
       ("perBirth", n config.tariff.perBirth), ("perGrant", n config.tariff.perGrant),
       ("perInitialPayloadByte", n config.tariff.perInitialPayloadByte),
       ("collector", n config.tariff.collector), ("asset", n config.tariff.asset)]),
     ("runtimeParameters", toJson (Minidregg.Host.Json.encodeHex config.runtimeParameters)),
     ("nativeChecked", toJson true), ("succinctProofDeployment", toJson false)]
  let meteringJson := fun (providerResourceId, tariff) => Lean.Json.mkObj [
          ("providerResourceId", n providerResourceId),
          ("tariffVersion", n tariff.version),
          ("model", toJson tariff.model),
          ("routes", ((ProviderUsage.tariffJson tariff).getObjValD "routes")),
          ("tariffDigest", n (Kernel.ProviderMetering.tariffDigest tariff).value)]
  let meteringFields := match metering with
    | none => []
    | some (providerResourceId, tariff) =>
        [("providerMetering", meteringJson (providerResourceId, tariff))]
  let serviceFields := if services.isEmpty then [] else
    [("providerMeterings", toJson (services.map meteringJson))]
  let grainBirthFields := match config.grainBirthTariff with
    | none => []
    | some tariff => [("grainBirthTariff", Lean.Json.mkObj
        [("base", n tariff.base), ("perBirth", n tariff.perBirth)])]
  Lean.Json.mkObj (base ++ grainBirthFields ++ meteringFields ++ serviceFields)

def descriptionLoaded (config : NativeHost.Config) : Lean.Json := Id.run do
  let n := fun value : Nat => toJson (toString value)
  return Lean.Json.mkObj
    [("runtime", toJson "minidregg-native"),
     ("semantics", n config.profile.semantics.value),
     ("domain", n config.deployment.domain.value),
     ("payCell", n (Kernel.PayCell.physicalId config.deployment.domain)),
     ("fieldModulus", n NativeHostProfile.characteristic),
     ("orderDifferenceWidth", n NativeHostProfile.orderWidth),
     ("nativeChecked", toJson true), ("succinctProofDeployment", toJson false),
     ("operations", toJson
       ((["birth", "invoke", "install", "delegate", "revoke", "renounce",
          "fn-selected-public-release", "application-lifecycle-begin",
          "selected-source-publication"] : List String) ++
         if config.grainBirthTariff.isSome then ["grain-birth"] else [])),
     ("nockFSync", n config.nockFSync),
     ("jointInvocation", toJson true), ("typedContent", toJson true),
     ("authorizedQueries", toJson true), ("delegation", toJson true)]

def description (config : NativeHost.Config) : IO Lean.Json := do
  discard <| IO.ofExcept (← NativeHost.openExisting config)
  return descriptionLoaded config

/-- Measurement: time the per-state costs a request pays on this Store. -/
def storeBench (config : NativeHost.Config) : IO Unit := do
  let timed {α : Type} (label : String) (action : IO α) : IO α := do
    let t0 ← IO.monoMsNow
    let result ← action
    IO.println s!"{label}: {(← IO.monoMsNow) - t0} ms"
    return result
  let durable ← timed "load" do
    IO.ofExcept (← DurableReceiverIO.load config.transport ResourceBirthCodec.rootBytes)
  IO.println s!"records {durable.image.accepted.length} base {durable.baseHeight} cells {durable.image.cellIds.length}"
  let lanes : List (String × Minidregg.Theory.ResourceCost.Lane) :=
    [("incidences", .incidences), ("turnBytes", .turnBytes), ("memoryTouches", .memoryTouches),
     ("witnessBytes", .witnessBytes), ("proofWork", .proofWork), ("storageBytes", .storageBytes),
     ("networkBytes", .networkBytes), ("sideEffectCount", .sideEffectCount),
     ("feeDebit", .feeDebit), ("leaseByteBlocks", .leaseByteBlocks)]
  for (name, lane) in lanes do
    let last := (durable.image.accepted.getLast?.map fun r => r.exactCharge lane).getD 0
    IO.println s!"allowance {name}: available {durable.snapshot.model.available lane} last-record charge {last}"
  discard <| timed "cellIds x10" do
    let mut n := 0
    for _ in [0:10] do n := n + durable.image.cellIds.length
    pure n
  discard <| timed "loadDirectory x10" do
    let mut n := 0
    for _ in [0:10] do
      if (CredentialAuthorityDomainReceiver.loadDirectory durable).isSome then n := n + 1
    pure n
  discard <| timed "loadDeployment x10" do
    let mut n := 0
    for _ in [0:10] do
      if (CredentialAuthorityDomainReceiver.loadDeployment config.deployment durable.snapshot).isSome then
        n := n + 1
    pure n
  discard <| timed "validateLoaded x10" do
    let mut n := 0
    for _ in [0:10] do
      if (NativeHost.validateLoaded config durable).toOption.isSome then n := n + 1
    pure n
  if let .ok opened := NativeHost.validateLoaded config durable then
    discard <| timed "loadDirectoryFrom (held, same image) x10" do
      let mut n := 0
      for _ in [0:10] do
        if (CredentialAuthorityDomainReceiver.loadDirectoryFrom opened.directory durable).isSome then
          n := n + 1
      pure n
    discard <| timed "validateLoadedFrom (held, same image) x10" do
      let mut n := 0
      for _ in [0:10] do
        if (NativeHost.validateLoadedFrom config opened durable).toOption.isSome then n := n + 1
      pure n
  discard <| timed "root rebuild x3" do
    let mut r := 0
    for _ in [0:3] do
      r := r + (DurableReceiverIO.RootCache.ofEntries
        (DurableReceiverIO.entriesOf durable.image durable.snapshot durable.chain)).root.value % 7
    pure r
  let some authority := CredentialAuthorityDomainReceiver.loadDeployment config.deployment durable.snapshot
    | throw (IO.userError "no authority")
  let authorityBytes := durable.snapshot.canonicalBytes ⟨config.deployment.authorityCellId⟩
  IO.println s!"authority cell bytes {authorityBytes.length}"
  discard <| timed "authState x10" do
    let mut n := 0
    for i in [0:10] do
      n := n + authority.snapshot.authState.policyEpoch ⟨i⟩ + authority.snapshot.authState.revoked.card
    pure n
  discard <| timed "authority rootBytes x10" do
    let mut n := 0
    for _ in [0:10] do n := n + (ResourceBirthCodec.rootBytes authorityBytes).value % 3
    pure n
  discard <| timed "authority decode+load x10" do
    let mut n := 0
    for _ in [0:10] do
      if (CredentialAuthorityDomainReceiver.loadDeployment config.deployment durable.snapshot).isSome then
        n := n + authority.snapshot.cell.logical.support.card
    pure n
  -- The open's and the checkpoint turn's parts, each timed alone (`IO.lazyPure`
  -- defers each pure computation to inside its timer).
  let timedPure {α : Type} (label : String) (value : Unit → α) : IO α :=
    timed label (IO.lazyPure value)
  let key ← IO.ofExcept (← config.transport.key)
  let height := durable.image.accepted.length
  let stored ← timed "open: read the Store" do
    match ← config.transport.read 1 true with
    | .ok (some stored) => pure stored
    | _ => throw (IO.userError "store read failed")
  let records ← timedPure "open: decode every record" fun _ =>
    stored.entries.filterMap fun entry => DurableCheckpointCodec.recordFrame.decode entry.record
  IO.println s!"  decoded {records.length} records"
  discard <| timedPure "open: the log chain over every record" fun _ =>
    (DurableCheckpointCodec.chainAfter durable.logStart records).value % 7
  if let some checkpoint := stored.checkpoint then
    IO.println s!"  stored checkpoint at {checkpoint.height}, {checkpoint.bytes.length} bytes"
    let body ← timedPure "open: openSealed (decode + full world root + MAC)" fun _ =>
      DurableCheckpointCodec.openSealed key ResourceBirthCodec.rootBytes checkpoint.bytes
    if let .ok body := body then
      discard <| timedPure "open: resume (materialize + replay the suffix)" fun _ =>
        (DurableCheckpoint.resume ResourceBirthCodec.rootBytes durable.image body.height body.state).isSome
  discard <| timedPure "open: root cache build (full evaluation)" fun _ =>
    (DurableReceiverIO.RootCache.ofEntries
      (DurableReceiverIO.entriesOf durable.image durable.snapshot durable.chain)).root.value % 7
  discard <| timedPure "open: cache injectivity check" fun _ => durable.roots.injectiveCheck
  discard <| timedPure "open: presence index" fun _ =>
    (PresenceIndex.ofRecords durable.image.accepted).touched.length
  let state ← timedPure "checkpoint: state (ofSnapshot)" fun _ =>
    DurableCheckpoint.State.ofSnapshot durable.image durable.snapshot
  IO.println s!"  state cells {state.cells.length} nullifiers {state.consumed.length}"
  discard <| timedPure "checkpoint: body encode" fun _ =>
    (DurableCheckpointCodec.bodyStream.encode ⟨key.id, height, durable.chain, state⟩).length
  discard <| timedPure "checkpoint: seal from the cached root (encode + MAC)" fun _ =>
    (DurableCheckpointCodec.checkpointFrame.encode
      (DurableCheckpointCodec.sealAt key height durable.chain state durable.worldRoot)).length
  discard <| timedPure "checkpoint: seal with the root in full" fun _ =>
    (DurableCheckpointCodec.checkpointFrame.encode
      (DurableCheckpointCodec.sealCheckpoint key ResourceBirthCodec.rootBytes height durable.chain
        state)).length
  discard <| timedPure "checkpoint: every cell's rootBytes" fun _ =>
    durable.image.cellIds.foldl (fun acc id =>
      acc + (ResourceBirthCodec.rootBytes (durable.snapshot.canonicalBytes id)).value % 7) 0
  discard <| timedPure "checkpoint: rebase at the head" fun _ => durable.rebase.isSome
  discard <| timedPure "checkpoint: image.cellIds" fun _ => durable.image.cellIds.length
  discard <| timedPure "checkpoint: State.snapshot at the head" fun _ =>
    (state.snapshot ResourceBirthCodec.rootBytes durable.image.accepted).model.journal.length
  discard <| timedPure "checkpoint: resume at the head" fun _ =>
    (DurableCheckpoint.resume ResourceBirthCodec.rootBytes durable.image height state).isSome
  discard <| timedPure "checkpoint: the Admissible parts (nodup, membership)" fun _ =>
    (decide (state.cells.map Prod.fst).Nodup,
      (state.cells.map Prod.fst).all fun id => decide (id ∈ durable.image.cellIds))
  discard <| timedPure "checkpoint: decide State.Admissible" fun _ =>
    decide (state.Admissible durable.image)
  discard <| timed "head receipt x10" do
    let mut n := 0
    for _ in [0:10] do
      if let some r := durable.image.accepted.getLast? then
        if (NativeHost.historicalReceipt config durable r.transactionId r.event.eventId).isSome then
          n := n + 1
    pure n
  -- Session indexes (deos efficiency B): the cached enumeration and
  -- transaction lookup beside the List functions they refine.
  discard <| timed "cellIds (cached) x10" do
    let mut n := 0
    for _ in [0:10] do n := n + durable.cellIds.length
    pure n
  let middle := durable.image.accepted[durable.image.accepted.length / 2]?
  discard <| timed "middle transaction index (cached) x1000" do
    let mut n := 0
    if let some r := middle then
      for _ in [0:1000] do n := n + (durable.firstIndex r.transactionId).getD 0
    pure n
  discard <| timed "middle transaction index (findIdx?) x1000" do
    let mut n := 0
    if let some r := middle then
      for i in [0:1000] do
        n := n + (durable.image.accepted.findIdx?
          (fun record => record.transactionId == r.transactionId || i == 1000000)).getD 0
    pure n
  discard <| timed "middle receipt x1" do
    let mut n := 0
    if let some r := middle then
      if let some receipt := NativeHost.historicalReceipt config durable r.transactionId r.event.eventId then
        n := n + receipt.worldRoot.value % 7
    pure n
  discard <| timed "middle receipt x1000" do
    let mut n := 0
    if let some r := middle then
      for _ in [0:1000] do
        if let some receipt := NativeHost.historicalReceipt config durable r.transactionId r.event.eventId then
          n := n + receipt.worldRoot.value % 7
    pure n
  -- `Image.append`'s list snoc at this height (what `Loaded.extend` pays per
  -- record for the in-memory log), x1000.
  discard <| timed "image.append list snoc x1000" do
    let mut n := 0
    if let some r := durable.image.accepted.getLast? then
      for i in [0:1000] do
        n := n + ((durable.image.accepted ++ [r]).length + i) % 7
    pure n
  -- The specification root of the same prefix, evaluated in full: what every
  -- non-head receipt paid before the log kept its roots.
  discard <| timedPure "middle receipt root, specification (prefix evaluated) x1" fun _ =>
    (NativeHost.receiptRootSpec config durable (durable.image.accepted.length / 2)).value % 7
  -- Control: every kept root against its prefix's specification root, at
  -- STORE_BENCH_ROOT_STRIDE spaced heights (0 = skip).
  let stride := ((← IO.getEnv "STORE_BENCH_ROOT_STRIDE").bind String.toNat?).getD 0
  if stride > 0 then
    let mut checked := 0
    let mut differ := 0
    for i in [0:durable.image.accepted.length:stride] do
      if let some (some kept) := durable.rootLog[i]? then
        let spec := NativeHost.worldRoot config ⟨durable.image.seed, durable.image.accepted.take (i + 1)⟩
        checked := checked + 1
        if kept != spec then
          differ := differ + 1
          IO.println s!"root differs at height {i + 1}: kept {kept.value} spec {spec.value}"
        else IO.println s!"root height {i + 1} {kept.value}"
    IO.println s!"kept roots checked {checked}, differing {differ}"

/-- The whole presence index, log heights (operator output only). -/
def presenceIndexJson (index : PresenceIndex.Index) : Lean.Json :=
  .mkObj [("lastSeen", .arr <| index.lastSeen.toArray.map fun entry =>
      .arr #[.str (toString entry.1.1.value), .str (toString entry.1.2.value), .str (toString entry.2)]),
    ("touched", .arr <| index.touched.toArray.map fun entry =>
      .arr #[.str (toString entry.1.value), .str (toString entry.2)])]

/-- The whole link index, log heights (operator output only): per source
cell, its live links with revision, height, target kind and target id. -/
def linkIndexJson (index : LinkIndex.Index) : Lean.Json :=
  .arr <| index.sources.toArray.map fun (cell, entries) =>
    .mkObj [("cell", .str (toString cell.value)), ("links", .arr <| entries.toArray.map fun entry =>
      .arr #[.str (toString entry.link.digest.value), .str (toString entry.record.operation.digest.value),
        .str (toString entry.height), .str (toString (LinkIndex.targetKind entry.record.target)),
        .str (toString (LinkIndex.targetId entry.record.target))])]

def failure (reason : RefusalReason) (phase detail : String) : List UInt8 :=
  outcomeCodec.encode (.refused reason phase.toUTF8.toList detail.toUTF8.toList)

/-- The refused signed request's own frame, naming the deciding reason. -/
def refusalFrame (phase : String) (refusal : Refusal) : List UInt8 :=
  outcomeCodec.encode (NativeHost.refusalOutcome phase refusal)

/-- Session state is poisoned on any physical read, chain, tag or replay
failure. A new process must reopen from the MAC'd checkpoint before serving. -/
def phaseTrace (label : String) (started : Nat) : IO Unit := do
  if (← IO.getEnv "MINIDREGG_HOST_TRACE").isSome then
    IO.eprintln s!"host-trace {label} {(← IO.monoMsNow) - started} ms"

def sessionCurrent (config : NativeHost.Config)
    (state : IO.Ref (Option (NativeHostSession.Session config))) :
    IO (NativeHostSession.Session config) := do
  let some prior ← state.get
    | throw (IO.userError "native host session invalidated")
  match ← NativeHostSession.refresh config prior with
  | .error detail =>
      state.set none
      throw (IO.userError detail)
  | .ok current =>
      state.set (some current)
      return current

/-- The genesis-walked history for the walk-provenance families, computed on
first use and extended by re-admission afterwards (`NativeHostSession.walked`). -/
def sessionWalked (config : NativeHost.Config)
    (state : IO.Ref (Option (NativeHostSession.Session config))) :
    IO (NativeHostSession.Walked config) := do
  let some prior ← state.get
    | throw (IO.userError "native host session invalidated")
  match ← NativeHostSession.refreshWalked config prior with
  | .error detail =>
      state.set none
      throw (IO.userError detail)
  | .ok (current, walked) =>
      state.set (some current)
      return walked

def sessionSetWalked {config : NativeHost.Config}
    (state : IO.Ref (Option (NativeHostSession.Session config)))
    {oldTarget : NativeHost.Durable} (old : NativeHostReplay.Verified config oldTarget)
    (readback : NativeHostReplay.ExactReadback config old) : IO Unit := do
  if let some current ← state.get then
    state.set (some (current.rememberReadback old readback))

def sessionOpened (config : NativeHost.Config)
    (state : IO.Ref (Option (NativeHostSession.Session config))) :
    IO (NativeHost.Opened config) := do
  return (← sessionCurrent config state).opened

/-- The live directory, for the Nock program reads (ops 131-137): the session's
held one (`LoadedDirectory.load_eq`: it is what `loadDirectory` would return),
never a per-request decode of every stored cell. -/
def nockDirectory (config : NativeHost.Config)
    (state : IO.Ref (Option (NativeHostSession.Session config))) :
    IO (Minidregg.Theory.CellRegistry.Directory Nat CanonicalCellRegistry.registry) := do
  return (← sessionOpened config state).directory.directory

/-- Unauthenticated evaluator assistance shares the operator's synchronous fuel
bound. The supplied caller is sample data, never payment authorization. Larger
runs need a separately authenticated service; they cannot spend member credit. -/
def checkNockServiceBudget (config : NativeHost.Config)
    (directory : Minidregg.Theory.CellRegistry.Directory Nat CanonicalCellRegistry.registry)
    (programId : Minidregg.Theory.TypedAuthorization.Digest) : IO Unit := do
  match CanonicalCellRegistry.loadProgram config.deployment.domain directory programId with
  | none => pure () -- the operation reports its ordinary programUnknown verdict
  | some program =>
    if config.nockFSync < program.abi.fuel then
      throw (IO.userError s!"overSyncBudget: evaluator assistance fuel {program.abi.fuel} exceeds operator nockFSync {config.nockFSync}")


def sessionConfirmed (config : NativeHost.Config)
    (state : IO.Ref (Option (NativeHostSession.Session config)))
    (kind : DurableReceiverIO.Confirmation)
    (transactionId eventId : Minidregg.Theory.TypedAuthorization.Digest) :
    IO NativeHostCodec.Outcome := do
  try
    let t0 ← IO.monoMsNow
    let opened ← sessionOpened config state
    phaseTrace "confirm refresh" t0
    match NativeHost.historicalReceipt config opened.durable transactionId eventId with
    | none => return .uncertain "original receipt prefix unavailable".toUTF8.toList
    | some receipt => return .confirmed kind receipt
  catch error => return .uncertain s!"receipt readback: {error}".toUTF8.toList

/-- The exact post-CAS branch already has the verified successor and original
receipt; retain that verifier-minted tip for the next session request. -/
def sessionExactConfirmed (config : NativeHost.Config)
    (state : IO.Ref (Option (NativeHostSession.Session config)))
    (kind : DurableReceiverIO.Confirmation) {oldTarget : NativeHost.Durable}
    (old : NativeHostReplay.Verified config oldTarget)
    (readback : NativeHostReplay.ExactReadback config old)
    (receipt : NativeHostCodec.Receipt) : IO NativeHostCodec.Outcome := do
  if let some current ← state.get then
    state.set (some (current.rememberReadback old readback))
  return .confirmed kind receipt

/-- The special receiver accepts raw strict selected-release ingress, not a
forged ordinary DRC signed command. Its current-key and law checks use the
same verifier-opened recipient image as the session. -/
def selectedReleaseSubmitSession (config : NativeHost.Config)
    (state : IO.Ref (Option (NativeHostSession.Session config)))
    (payload : List UInt8) : IO NativeHostCodec.Outcome := do
  let opened ← sessionOpened config state
  let result ← FnSelectiveReleaseReceiver.receiveLoaded config opened payload
  let outcome ← match result with
    | .confirmed kind receipt =>
        sessionConfirmed config state kind receipt.transactionId receipt.eventId
    | .rejected _ =>
        pure (.refused .operationRejected "selected-release".toUTF8.toList "request refused".toUTF8.toList)
    | .transactionConflict =>
        pure (.refused .conflict "replay".toUTF8.toList "transaction identity conflict".toUTF8.toList)
    | .contention => pure .contention
    | .unavailable detail => pure (.unavailable detail.toUTF8.toList)
    | .uncertain detail => pure (.uncertain detail.toUTF8.toList)
  return NativeHost.publicSubmissionOutcome outcome

/-- Lookup never submits missing work. An exact historical retry retains its
original receipt even after current owner authority has changed. -/
def selectedReleaseLookupSession (config : NativeHost.Config)
    (state : IO.Ref (Option (NativeHostSession.Session config)))
    (payload : List UInt8) : IO NativeHostCodec.Outcome := do
  let opened ← sessionOpened config state
  let some ingress := FnSelectiveReleaseIngress.ingressCodec.decode payload
    | return .refused .malformed "selected-release".toUTF8.toList "noncanonical ingress".toUTF8.toList
  match FnSelectiveReleaseReceiver.replay config opened ingress with
  | none => return .absent
  | some (.error _) =>
      return .refused .conflict "replay".toUTF8.toList "transaction identity conflict".toUTF8.toList
  | some (.ok receipt) =>
      match NativeHost.historicalReceipt config opened.durable
          receipt.transactionId receipt.eventId with
      | none => return .uncertain "original receipt prefix unavailable".toUTF8.toList
      | some historical => return .confirmed .replayed historical

/-- A BEGIN records source-authorized pending work. Physical launch and
completion require separate host custody and current claim validation. -/
def applicationLifecycleBeginSubmitSession (config : NativeHost.Config)
    (state : IO.Ref (Option (NativeHostSession.Session config)))
    (payload : List UInt8) : IO NativeHostCodec.Outcome := do
  let session ← sessionWalked config state
  let some _ := ApplicationLifecycleBeginV3Ingress.codec.decode payload
    | return .refused .malformed "application-lifecycle-begin".toUTF8.toList
        "fresh BEGIN requires canonical launch-bound v3 ingress".toUTF8.toList
  let result ← ApplicationLifecycleBeginV3Receiver.receiveVerified config
    session.verified payload
  match result with
    | .confirmed confirmed =>
        sessionSetWalked state confirmed.old confirmed.readback
        return .confirmed confirmed.confirmation confirmed.receipt
    | .rejected _ =>
        return .refused .operationRejected "application-lifecycle-begin".toUTF8.toList "request refused".toUTF8.toList
    | .contention => return .contention
    | .unavailable detail => return .unavailable detail.toUTF8.toList
    | .uncertain detail => return .uncertain detail.toUTF8.toList

def applicationLifecycleBeginLookupSession (config : NativeHost.Config)
    (state : IO.Ref (Option (NativeHostSession.Session config)))
    (payload : List UInt8) : IO NativeHostCodec.Outcome := do
  let session ← sessionWalked config state
  let result := if (ApplicationLifecycleBeginV3Ingress.codec.decode payload).isSome then
      (ApplicationLifecycleV3Lookup.beginVerified session.verified payload).mapError fun
        | .malformed => ApplicationLifecycleV2Lookup.Error.malformed
        | .transactionConflict => .transactionConflict
        | .nativeHistoryUnavailable => .nativeHistoryUnavailable
    else if (ApplicationLifecycleBeginV2Ingress.codec.decode payload).isSome then
      ApplicationLifecycleV2Lookup.beginVerified session.verified payload
    else ApplicationLifecycleV2Lookup.beginLegacyVerified session.verified payload
  match result with
  | .ok none => return .absent
  | .ok (some receipt) => return .confirmed .replayed receipt
  | .error .malformed =>
      return .refused .malformed "application-lifecycle-begin".toUTF8.toList
        "noncanonical ingress".toUTF8.toList
  | .error .transactionConflict =>
      return .refused .conflict "replay".toUTF8.toList
        "transaction identity conflict".toUTF8.toList
  | .error .nativeHistoryUnavailable =>
      return .uncertain "original lifecycle BEGIN receipt unavailable".toUTF8.toList

def applicationLifecycleClaimLookupSession (config : NativeHost.Config)
    (state : IO.Ref (Option (NativeHostSession.Session config)))
    (payload : List UInt8) : IO NativeHostCodec.Outcome := do
  let session ← sessionWalked config state
  let result := if (ApplicationLifecycleClaimV3Ingress.codec.decode payload).isSome then
      (ApplicationLifecycleV3Lookup.claimVerified session.verified payload).mapError fun
        | .malformed => ApplicationLifecycleV2Lookup.Error.malformed
        | .transactionConflict => .transactionConflict
        | .nativeHistoryUnavailable => .nativeHistoryUnavailable
    else if (ApplicationLifecycleClaimV2Ingress.codec.decode payload).isSome then
      ApplicationLifecycleV2Lookup.claimVerified session.verified payload
    else ApplicationLifecycleV2Lookup.claimLegacyVerified session.verified payload
  match result with
  | .ok none => return .absent
  | .ok (some receipt) => return .confirmed .replayed receipt
  | .error .malformed =>
      return .refused .malformed "application-lifecycle-claim".toUTF8.toList
        "noncanonical ingress".toUTF8.toList
  | .error .transactionConflict =>
      return .refused .conflict "replay".toUTF8.toList
        "transaction identity conflict".toUTF8.toList
  | .error .nativeHistoryUnavailable =>
      return .uncertain "original lifecycle claim receipt unavailable".toUTF8.toList

/-- A completion records the custodian's signed physical report only after
current source/history admission and exact CAS readback. It does not itself
launch or kill a process. -/
def applicationFailedStartRecoverySubmitSession (config : NativeHost.Config)
    (state : IO.Ref (Option (NativeHostSession.Session config)))
    (payload : List UInt8) : IO NativeHostCodec.Outcome := do
  let session ← sessionWalked config state
  let outcome : NativeHostCodec.Outcome ← match ← ApplicationFailedStartEndpoint.submit config session.verified payload with
    | .confirmed confirmed => do
        sessionSetWalked state confirmed.old confirmed.readback
        pure (.confirmed confirmed.confirmation confirmed.receipt)
    | .rejected detail => pure (.refused .operationRejected
        "failed-start-recovery".toUTF8.toList detail.toUTF8.toList)
    | .contention => pure .contention
    | .unavailable _ => pure (.unavailable "recovery service unavailable".toUTF8.toList)
    | .uncertain _ => pure (.uncertain "recovery outcome uncertain; use exact ingress lookup".toUTF8.toList)
  NativeHost.logOperatorRefusal outcome
  return NativeHost.publicSubmissionOutcome outcome

def applicationLifecycleCompletionSubmitSession (config : NativeHost.Config)
    (state : IO.Ref (Option (NativeHostSession.Session config)))
    (payload : List UInt8) : IO NativeHostCodec.Outcome := do
  let session ← sessionWalked config state
  let some _ := ApplicationLifecycleCompletionV2Ingress.codec.decode payload
    | return .refused .malformed "application-lifecycle-completion".toUTF8.toList
        "fresh completion requires canonical launch-bound v2 ingress".toUTF8.toList
  let result ← ApplicationLifecycleCompletionV2Receiver.receiveVerified config
    session.verified payload
  match result with
  | .confirmed confirmed =>
      sessionSetWalked state confirmed.old confirmed.readback
      return .confirmed confirmed.confirmation confirmed.receipt
  | .rejected detail =>
      return .refused .operationRejected "application-lifecycle-completion".toUTF8.toList
        detail.toUTF8.toList
  | .contention => return .contention
  | .unavailable detail => return .unavailable detail.toUTF8.toList
  | .uncertain detail => return .uncertain detail.toUTF8.toList

/-- Recovery selects only the original four-field receipt from a verified
history. It never performs a physical completion or process effect. -/
def applicationLifecycleCompletionLookupSession (config : NativeHost.Config)
    (state : IO.Ref (Option (NativeHostSession.Session config)))
    (payload : List UInt8) : IO NativeHostCodec.Outcome := do
  let session ← sessionWalked config state
  let result := if (ApplicationLifecycleCompletionV2Ingress.codec.decode payload).isSome then
      (ApplicationLifecycleCompletionV2Lookup.verified session.verified payload).mapError fun
        | .malformed => ApplicationLifecycleCompletionLookup.Error.malformed
        | .transactionConflict => .transactionConflict
        | .nativeHistoryUnavailable => .nativeHistoryUnavailable
    else ApplicationLifecycleCompletionLookup.verified session.verified payload
  match result with
  | .ok none => return .absent
  | .ok (some receipt) => return .confirmed .replayed receipt
  | .error .malformed =>
      return .refused .malformed "application-lifecycle-completion".toUTF8.toList
        "noncanonical ingress".toUTF8.toList
  | .error .transactionConflict =>
      return .refused .conflict "replay".toUTF8.toList
        "transaction identity conflict".toUTF8.toList
  | .error .nativeHistoryUnavailable =>
      return .uncertain "original lifecycle completion receipt unavailable".toUTF8.toList

/-- Event20 activates one gateway-bound consumer namespace. The receiver
rechecks current gateway authority, performs the native CAS, then reopens a
verified physical tip before returning its original receipt. -/
def fnConsumerNamespaceSubmitSession (config : NativeHost.Config)
    (state : IO.Ref (Option (NativeHostSession.Session config)))
    (payload : List UInt8) : IO NativeHostCodec.Outcome := do
  let session ← sessionWalked config state
  let result ← FnConsumerNamespaceReceiver.receiveVerified session.verified payload
  let outcome ← match result with
  | .confirmed kind receipt =>
      sessionConfirmed config state kind receipt.transactionId receipt.eventId
  | .rejected _ =>
      pure (.refused .operationRejected "fn-consumer-namespace".toUTF8.toList
        "request refused".toUTF8.toList)
  | .transactionConflict =>
      pure (.refused .conflict "replay".toUTF8.toList
        "transaction identity conflict".toUTF8.toList)
  | .contention => pure .contention
  | .unavailable detail => pure (.unavailable detail.toUTF8.toList)
  | .uncertain detail => pure (.uncertain detail.toUTF8.toList)
  return NativeHost.publicSubmissionOutcome outcome

/-- Op41 is receipt-only. A missing original is never resubmitted. -/
def fnConsumerNamespaceLookupSession (config : NativeHost.Config)
    (state : IO.Ref (Option (NativeHostSession.Session config)))
    (payload : List UInt8) : IO NativeHostCodec.Outcome := do
  let session ← sessionWalked config state
  let some ingress := FnConsumerNamespaceRegistration.ingressCodec.decode payload
    | return .refused .malformed "fn-consumer-namespace".toUTF8.toList
        "noncanonical ingress".toUTF8.toList
  match FnConsumerNamespaceReceiver.lookupVerified session.verified ingress with
  | none => return .absent
  | some (.ok receipt) => return .confirmed .replayed receipt
  | some (.error detail) => return .uncertain detail.toUTF8.toList

/-- Event17 is a verified Mini commitment to one pinned local first-match
observation. It never implies that an external fn delivery is complete. -/
def fnSelectedPollSubmitSession (config : NativeHost.Config)
    (state : IO.Ref (Option (NativeHostSession.Session config)))
    (payload : List UInt8) : IO NativeHostCodec.Outcome := do
  let session ← sessionWalked config state
  let result ← FnSelectedPollReceiver.receiveVerified session.verified payload
  let outcome ← match result with
  | .confirmed kind receipt =>
      sessionConfirmed config state kind receipt.transactionId receipt.eventId
  | .rejected _ =>
      pure (.refused .operationRejected "fn-selected-poll".toUTF8.toList "request refused".toUTF8.toList)
  | .transactionConflict =>
      pure (.refused .conflict "replay".toUTF8.toList "transaction identity conflict".toUTF8.toList)
  | .contention => pure .contention
  | .unavailable detail => pure (.unavailable detail.toUTF8.toList)
  | .uncertain detail => pure (.uncertain detail.toUTF8.toList)
  return NativeHost.publicSubmissionOutcome outcome

def fnSelectedPollLookupSession (config : NativeHost.Config)
    (state : IO.Ref (Option (NativeHostSession.Session config)))
    (payload : List UInt8) : IO NativeHostCodec.Outcome := do
  let session ← sessionWalked config state
  let some ingress := FnSelectedPollCoverage.ingressCodec.decode payload
    | return .refused .malformed "fn-selected-poll".toUTF8.toList
        "noncanonical ingress".toUTF8.toList
  match FnSelectedPollReceiver.lookupVerified session.verified ingress with
  | none => return .absent
  | some (.ok receipt) => return .confirmed .replayed receipt
  | some (.error detail) => return .uncertain detail.toUTF8.toList

/-- Event19 advances the same durable frontier for a bounded empty page. -/
def fnEmptyPollSubmitSession (config : NativeHost.Config)
    (state : IO.Ref (Option (NativeHostSession.Session config)))
    (payload : List UInt8) : IO NativeHostCodec.Outcome := do
  let session ← sessionWalked config state
  let result ← FnEmptyPollReceiverV2.receiveVerified session.verified payload
  let outcome ← match result with
  | .confirmed kind receipt =>
      sessionConfirmed config state kind receipt.transactionId receipt.eventId
  | .rejected _ =>
      pure (.refused .operationRejected "fn-empty-poll-v2".toUTF8.toList "request refused".toUTF8.toList)
  | .transactionConflict =>
      pure (.refused .conflict "replay".toUTF8.toList "transaction identity conflict".toUTF8.toList)
  | .contention => pure .contention
  | .unavailable detail => pure (.unavailable detail.toUTF8.toList)
  | .uncertain detail => pure (.uncertain detail.toUTF8.toList)
  return NativeHost.publicSubmissionOutcome outcome

def fnEmptyPollLookupSession (config : NativeHost.Config)
    (state : IO.Ref (Option (NativeHostSession.Session config)))
    (payload : List UInt8) : IO NativeHostCodec.Outcome := do
  let session ← sessionWalked config state
  let some ingress := FnEmptyPollProgressV2.ingressCodec.decode payload
    | return .refused .malformed "fn-empty-poll-v2".toUTF8.toList
        "noncanonical ingress".toUTF8.toList
  match FnEmptyPollReceiverV2.lookupVerified session.verified ingress with
  | none => return .absent
  | some (.ok receipt) => return .confirmed .replayed receipt
  | some (.error detail) => return .uncertain detail.toUTF8.toList

/-- This records current source authorization for one selected content version.
External fn delivery is a separate effect with its own uncertain outcome. -/
def selectedSourcePublicationSubmitSession (config : NativeHost.Config)
    (state : IO.Ref (Option (NativeHostSession.Session config)))
    (payload : List UInt8) : IO NativeHostCodec.Outcome := do
  let opened ← sessionOpened config state
  let result ← FnSelectiveReleaseSourceReceiver.receiveLoaded config opened payload
  let outcome ← match result with
    | .confirmed kind receipt =>
        sessionConfirmed config state kind receipt.transactionId receipt.eventId
    | .rejected _ => pure (.refused .operationRejected "selected-source-publication".toUTF8.toList
        "request refused".toUTF8.toList)
    | .transactionConflict => pure (.refused .conflict "replay".toUTF8.toList
        "transaction identity conflict".toUTF8.toList)
    | .contention => pure .contention
    | .unavailable detail => pure (.unavailable detail.toUTF8.toList)
    | .uncertain detail => pure (.uncertain detail.toUTF8.toList)
  return NativeHost.publicSubmissionOutcome outcome

def selectedSourcePublicationLookupSession (config : NativeHost.Config)
    (state : IO.Ref (Option (NativeHostSession.Session config)))
    (payload : List UInt8) : IO NativeHostCodec.Outcome := do
  let opened ← sessionOpened config state
  let some ingress := FnSelectiveReleaseSourcePublication.ingressCodec.decode payload
    | return .refused .malformed "selected-source-publication".toUTF8.toList
        "noncanonical ingress".toUTF8.toList
  match FnSelectiveReleaseSourceReceiver.replay opened ingress with
  | none => return .absent
  | some (.error _) =>
      return .refused .conflict "replay".toUTF8.toList "transaction identity conflict".toUTF8.toList
  | some (.ok receipt) =>
      match NativeHost.historicalReceipt config opened.durable
          receipt.transactionId receipt.eventId with
      | none => return .uncertain "original receipt prefix unavailable".toUTF8.toList
      | some historical => return .confirmed .replayed historical

/-- An issuer's signed app delegation and a factory ticket birth are admitted
from one verified current image. Existing exact issue receipts recover from
verified history without requiring the issuer still to hold that grant. -/
def applicationShareIssueSubmitSession (config : NativeHost.Config)
    (state : IO.Ref (Option (NativeHostSession.Session config)))
    (payload : List UInt8) : IO NativeHostCodec.Outcome := do
  let opened ← sessionOpened config state
  let result ← ApplicationShareIssueReceiver.receiveLoaded config opened.pins
    config.signature config.transport opened.durable
    (NativeHost.logicalHeight config opened.durable) payload
  let outcome ← match result with
    | .historical receipt =>
        sessionConfirmed config state .replayed receipt.transactionId receipt.eventId
    | .confirmed kind receipt =>
        sessionConfirmed config state kind receipt.transactionId receipt.eventId
    | .rejected _ => pure (.refused .operationRejected "application-share-issue".toUTF8.toList
        "request refused".toUTF8.toList)
    | .contention => pure .contention
    | .unavailable detail => pure (.unavailable detail.toUTF8.toList)
    | .uncertain detail => pure (.uncertain detail.toUTF8.toList)
  return NativeHost.publicSubmissionOutcome outcome

def applicationShareIssueLookupSession (config : NativeHost.Config)
    (state : IO.Ref (Option (NativeHostSession.Session config)))
    (payload : List UInt8) : IO NativeHostCodec.Outcome := do
  let opened ← sessionOpened config state
  let some ingress := ApplicationShareIssueSource.ingressCodec.decode payload
    | return .refused .malformed "application-share-issue".toUTF8.toList
        "noncanonical ingress".toUTF8.toList
  let some birth := ResourceBirthPolicyController.Concrete.decodeIngress ingress.birthIngress
    | return .refused .malformed "application-share-issue".toUTF8.toList
        "noncanonical birth ingress".toUTF8.toList
  match ApplicationShareIssueReceiver.replay opened.durable config.deployment.domain
      ingress birth with
  | none => return .absent
  | some (.error _) =>
      return .refused .conflict "replay".toUTF8.toList
        "transaction identity conflict".toUTF8.toList
  | some (.ok receipt) =>
      match NativeHost.historicalReceipt config opened.durable
          receipt.transactionId receipt.eventId with
      | none => return .uncertain "original receipt prefix unavailable".toUTF8.toList
      | some historical => return .confirmed .replayed historical

/-- Grain-backed issue is a distinct event-22 write. Its receiver combines
the grain birth and app delegation in one native CAS. Historical lookup is
handled separately after verifier-selected original-prefix re-admission. -/
def applicationGrainShareIssueSubmitSession (config : NativeHost.Config)
    (state : IO.Ref (Option (NativeHostSession.Session config)))
    (payload : List UInt8) : IO NativeHostCodec.Outcome := do
  let opened ← sessionOpened config state
  let ambient : DeclaredResourceController.Ambient :=
    ⟨config.federation, NativeHost.logicalHeight config opened.durable⟩
  let result ← ApplicationShareIssueGrainReceiver.receiveLoaded config opened.pins
    config.signature config.transport opened.durable ambient payload
  let outcome ← match result with
    | .historical receipt =>
        sessionConfirmed config state .replayed receipt.transactionId receipt.eventId
    | .confirmed kind receipt =>
        sessionConfirmed config state kind receipt.transactionId receipt.eventId
    | .rejected _ => pure (.refused .operationRejected "application-grain-share-issue".toUTF8.toList
        "request refused".toUTF8.toList)
    | .contention => pure .contention
    | .unavailable detail => pure (.unavailable detail.toUTF8.toList)
    | .uncertain detail => pure (.uncertain detail.toUTF8.toList)
  return NativeHost.publicSubmissionOutcome outcome

/-- Receipt recovery uses the exact event-22 certificate and original receipt
retained by the refreshed verifier walk. It performs no new admission. -/
def applicationGrainShareIssueLookupSession (config : NativeHost.Config)
    (state : IO.Ref (Option (NativeHostSession.Session config)))
    (payload : List UInt8) : IO NativeHostCodec.Outcome := do
  let session ← sessionWalked config state
  match ApplicationShareIssueGrainLookup.lookupVerified session.verified payload with
  | .error .malformed =>
      return .refused .malformed "application-grain-share-issue".toUTF8.toList
        "noncanonical ingress".toUTF8.toList
  | .error .transactionConflict =>
      return .refused .conflict "replay".toUTF8.toList
        "transaction identity conflict".toUTF8.toList
  | .error .nativeHistoryUnavailable =>
      return .uncertain "original grain share issue history unavailable".toUTF8.toList
  | .ok none => return .absent
  | .ok (some receipt) => return .confirmed .replayed receipt

/-- Event28 reselects the original event22 ticket and admits the joint edit
with separately signed current app, manifest and ticket reads before one CAS. -/
def applicationSessionEnrollmentSubmitSession (config : NativeHost.Config)
    (state : IO.Ref (Option (NativeHostSession.Session config)))
    (payload : List UInt8) : IO NativeHostCodec.Outcome := do
  let session ← sessionWalked config state
  let result ← ApplicationGrainSessionEnrollmentReceiver.receiveVerified
    session.verified payload
  let outcome : NativeHostCodec.Outcome ← match result with
    | .confirmed confirmed => do
        sessionSetWalked state confirmed.old confirmed.readback
        pure (.confirmed confirmed.confirmation confirmed.receipt)
    | .historical receipt => pure (.confirmed .replayed receipt)
    | .rejected detail => pure (.refused .operationRejected "application-session-enrollment".toUTF8.toList
        detail.toUTF8.toList)
    | .transactionConflict => pure (.refused .conflict "replay".toUTF8.toList
        "transaction identity conflict".toUTF8.toList)
    | .contention => pure .contention
    | .unavailable detail => pure (.unavailable detail.toUTF8.toList)
    | .uncertain detail => pure (.uncertain detail.toUTF8.toList)
  return outcome

/-- Historical event28 recovery returns only the verified original receipt. -/
def applicationSessionEnrollmentLookupSession (config : NativeHost.Config)
    (state : IO.Ref (Option (NativeHostSession.Session config)))
    (payload : List UInt8) : IO NativeHostCodec.Outcome := do
  let some ingress := ApplicationGrainSessionEnrollmentSource.ingressCodec.decode payload
    | return .refused .malformed "application-session-enrollment".toUTF8.toList
        "noncanonical ingress".toUTF8.toList
  unless ingress.canonicalBytes.toByteArray == payload.toByteArray do
    return .refused .malformed "application-session-enrollment".toUTF8.toList
      "noncanonical ingress".toUTF8.toList
  let session ← sessionWalked config state
  match ApplicationGrainSessionEnrollmentReceiver.lookupVerified session.verified ingress with
  | none => return .absent
  | some (.ok receipt) => return .confirmed .replayed receipt
  | some (.error _) =>
      return .refused .conflict "replay".toUTF8.toList
        "transaction identity conflict".toUTF8.toList

/-- Event27 grant installation is a durable Mini receipt, never a dispatch
permit. The receiver re-derives its original event22 ticket and exact current
app delegation before one CAS and verifies the recorded readback. -/
def agentLifetimeGrantSubmitSession (config : NativeHost.Config)
    (state : IO.Ref (Option (NativeHostSession.Session config)))
    (payload : List UInt8) : IO NativeHostCodec.Outcome := do
  let session ← sessionWalked config state
  let result ← ApplicationAgentLifetimeGrantReceiver.receiveVerified
    session.verified payload
  let outcome : NativeHostCodec.Outcome := match result with
    | .confirmed kind receipt _ _ => .confirmed kind receipt
    | .rejected _ => .refused .operationRejected "application-agent-lifetime-grant".toUTF8.toList
        "request refused".toUTF8.toList
    | .transactionConflict => .refused .conflict "replay".toUTF8.toList
        "transaction identity conflict".toUTF8.toList
    | .contention => .contention
    | .unavailable detail => .unavailable detail.toUTF8.toList
    | .uncertain detail => .uncertain detail.toUTF8.toList
  return NativeHost.publicSubmissionOutcome outcome

/-- Grant recovery selects the exact event27 original from a verified walk.
It returns its receipt only and cannot grant a later agent dispatch. -/
def agentLifetimeGrantLookupSession (config : NativeHost.Config)
    (state : IO.Ref (Option (NativeHostSession.Session config)))
    (payload : List UInt8) : IO NativeHostCodec.Outcome := do
  let session ← sessionWalked config state
  match ApplicationAgentLifetimeGrantLookup.lookupVerified session.verified payload with
  | .error _ =>
      return .refused .malformed "application-agent-lifetime-grant".toUTF8.toList
        "noncanonical or conflicting lookup ingress".toUTF8.toList
  | .ok none => return .absent
  | .ok (some original) => return .confirmed .replayed original.receipt

/-- Historical dispatch lookup is receipt-only. It rechecks the original
special event at its verifier-selected prefix and never mints a delivery
permit or replays an application effect. -/
def applicationDispatchLookupSession (config : NativeHost.Config)
    (state : IO.Ref (Option (NativeHostSession.Session config)))
    (payload : List UInt8) : IO NativeHostCodec.Outcome := do
  let session ← sessionWalked config state
  match ApplicationDispatchLookup.lookupVerified session.verified payload with
  | .ok none => return .absent
  | .ok (some receipt) => return .confirmed .replayed receipt
  | .error .malformed =>
      return .refused .malformed "application-dispatch".toUTF8.toList
        "noncanonical lookup ingress".toUTF8.toList
  | .error .transactionConflict =>
      return .refused .conflict "replay".toUTF8.toList
        "transaction identity conflict".toUTF8.toList
  | .error .nativeHistoryUnavailable =>
      return .uncertain "dispatch original history unavailable".toUTF8.toList

/-- Event21 historical lookup returns only its original receipt. It cannot
recover a fresh physical delivery permit or replay an external effect. -/
def applicationAgentDispatchLookupSession (config : NativeHost.Config)
    (state : IO.Ref (Option (NativeHostSession.Session config)))
    (payload : List UInt8) : IO NativeHostCodec.Outcome := do
  let session ← sessionWalked config state
  match ApplicationDispatchAgentLookup.lookupVerified session.verified payload with
  | .ok none => return .absent
  | .ok (some receipt) => return .confirmed .replayed receipt
  | .error .malformed =>
      return .refused .malformed "application-agent-dispatch".toUTF8.toList
        "noncanonical paid dispatch lookup ingress".toUTF8.toList
  | .error .transactionConflict =>
      return .refused .conflict "replay".toUTF8.toList
        "paid dispatch transaction identity conflict".toUTF8.toList
  | .error .nativeHistoryUnavailable =>
      return .uncertain "paid dispatch original history unavailable".toUTF8.toList

/-- Event26 recovery reports only the original receipt; it never recreates a
fresh paid delivery permit. -/
def applicationAgentLifetimeDispatchLookupSession (config : NativeHost.Config)
    (state : IO.Ref (Option (NativeHostSession.Session config)))
    (payload : List UInt8) : IO NativeHostCodec.Outcome := do
  let session ← sessionWalked config state
  match ApplicationAgentLifetimeDispatchLookup.lookupVerified session.verified payload with
  | .ok none => return .absent
  | .ok (some receipt) => return .confirmed .replayed receipt
  | .error .malformed =>
      return .refused .malformed "application-agent-lifetime-dispatch".toUTF8.toList
        "noncanonical lifetime dispatch lookup ingress".toUTF8.toList
  | .error .transactionConflict =>
      return .refused .conflict "replay".toUTF8.toList
        "lifetime dispatch transaction identity conflict".toUTF8.toList
  | .error .nativeHistoryUnavailable =>
      return .uncertain "lifetime dispatch original history unavailable".toUTF8.toList

/-- Author a current app/session birth intent from one verifier-opened image.
The JSON is only a request for source selectors; the helper derives current
height and grant epochs and checks the pinned genesis identity. -/
def applicationCurrentBirthIntentSession (config : NativeHost.Config)
    (state : IO.Ref (Option (NativeHostSession.Session config)))
    (application : Bool) (payload : List UInt8) : IO (List UInt8) := do
  unless payload.length ≤ FnEvidenceCodec.maxHostFrameBytes do
    throw (RequestRefusal.malformed "application birth request exceeds host frame bound")
  let opened ← sessionOpened config state
  let some text := String.fromUTF8? payload.toByteArray
    | throw (RequestRefusal.malformed "application birth request is not UTF-8")
  let json ← RequestRefusal.clientBytes (Minidregg.Host.Json.parse text)
  if application then
    IO.ofExcept <| Minidregg.Host.ApplicationCurrentBirthAuthoring.applicationIntentLoaded
      config opened json
  else
    IO.ofExcept <| Minidregg.Host.ApplicationCurrentBirthAuthoring.sessionIntentLoaded
      config opened json

def splitKind (payload : List UInt8) : IO (String × List UInt8) := do
  unless payload.length ≥ 2 do throw (RequestRefusal.malformed "short native host kind frame")
  let width := payload[0]!.toNat + 256 * payload[1]!.toNat
  unless width > 0 && width ≤ payload.length - 2 do
    throw (RequestRefusal.malformed "invalid native host kind length")
  let some kind := String.fromUTF8? (payload.drop 2 |>.take width).toByteArray
    | throw (RequestRefusal.malformed "native host kind is not UTF-8")
  return (kind, payload.drop (2 + width))

def splitPair (payload : List UInt8) : IO (List UInt8 × List UInt8) := do
  unless payload.length ≥ 4 do throw (RequestRefusal.malformed "short native host pair frame")
  let width := payload[0]!.toNat + 256 * payload[1]!.toNat +
    65536 * payload[2]!.toNat + 16777216 * payload[3]!.toNat
  unless width ≤ payload.length - 4 do throw (RequestRefusal.malformed "invalid native host pair length")
  return ((payload.drop 4).take width, payload.drop (4 + width))

def decodeSignatures (bytes : List UInt8) : IO (List (List UInt8)) := do
  let signaturesCodec := ResourceBirthCodec.strictCodec (StreamCodec.list bytesStream).toLawful
  let some signatures := signaturesCodec.decode bytes
    | throw (RequestRefusal.malformed "noncanonical signature list")
  return signatures

/-- Audience readback shared by standalone and persistent-session clients. -/
def objectAudienceJson (view : NativeHost.ObjectAudienceView) : Lean.Json :=
  let fields : List (String × Lean.Json) :=
    [("type", toJson "minidregg-object-audience-v1"),
     ("subject", toJson (toString view.subject.value)),
     ("object", toJson (toString view.object)),
     ("worldRoot", toJson (toString view.worldRoot.value)),
     ("policyAddress", toJson (toString view.policyAddress.value)),
     ("semanticLawDigest", toJson (toString (PolicyRecordCodec.semanticLawDigest view.sourceRecord).value)),
     ("policyEpoch", toJson (toString view.policyEpoch)),
     ("policyRevision", toJson (toString view.policyRevision)),
     ("currentAuthorityRoot", toJson (toString view.currentAuthorityRoot.value)),
     ("currentObjectRoot", toJson (toString view.currentObjectRoot.value)),
     ("source", toJson (Minidregg.Host.Json.encodeHex view.sourceBytes)),
     ("sourceRecord", Minidregg.Host.Json.policyRecordJson view.sourceRecord)]
  let metadata := match view.audience with
    | none => [("audienceState", Lean.Json.null), ("active", toJson false)]
    | some a =>
      [("audienceState", Minidregg.Host.Json.audienceStateJson a),
       ("epoch", toJson (toString a.epoch)),
       ("transition", toJson (toString a.transition)),
       ("audience", toJson (toString a.audience)),
       ("devices", toJson (toString a.devices)),
       ("history", toJson (toString a.history)),
       ("manifest", toJson (toString a.manifest)),
       ("authoritySnapshot", toJson (toString a.authoritySnapshot)),
       ("deviceSnapshot", toJson (toString a.deviceSnapshot)),
       ("active", toJson (a.mode == .active))]
  Lean.Json.mkObj (fields ++ metadata)

def objectRosterJson (bytes : List UInt8) : Except String Lean.Json := do
  let some roster := Compiler.ObjectAudienceRoster.decode bytes
    | throw "roster is not canonical"
  return .mkObj [("roster", Minidregg.Host.Json.audienceRosterJson roster),
    ("rosterBytes", toJson (Minidregg.Host.Json.encodeHex bytes)),
    ("audience", toJson (toString (Compiler.ObjectAudienceRoster.digest roster).value)),
    ("devices", toJson (toString (Compiler.ObjectAudienceRoster.deviceDigest roster).value))]

def checkedObjectRosterJson (audience : Theory.ObjectAudience.State)
    (roster : Theory.ObjectAudienceRoster.Roster) (rosterBytes : List UInt8) : Lean.Json :=
  .mkObj [("type", toJson "minidregg-checked-object-roster-v1"),
    ("audienceState", Minidregg.Host.Json.audienceStateJson audience),
    ("roster", Minidregg.Host.Json.audienceRosterJson roster),
    ("rosterBytes", toJson (Minidregg.Host.Json.encodeHex rosterBytes)),
    ("deviceSnapshot", toJson (toString audience.deviceSnapshot))]

/-- The standalone and persistent author routes share the exact source helpers. -/
def authorHost (config : NativeHost.Config)
    (providerRoutes : List (Nat × Kernel.ProviderMetering.Schedule))
    (kind : String) (source : Lean.Json) : Except String (List UInt8) :=
  if kind == "application-route-bound-dispatch" then
    ApplicationRouteAdmissionInspection.authorBoundDispatch config source
  else if kind == "application-route-admission-challenge" then
    ApplicationRouteAdmissionInspection.authorChallenge config source
  else if kind == "application-route-admission-request" then
    ApplicationRouteAdmissionInspection.authorRequest source
  else if kind == "application-stream-continuity-challenge" then
    ApplicationStreamContinuityInspection.authorChallenge config source
  else if kind == "application-stream-continuity-request" then
    ApplicationStreamContinuityInspection.authorRequest source
  else Minidregg.Host.Json.author kind source (some config) providerRoutes

/-- The live protocol keeps exact source-owned authoring and inspection in
memory, while every state-dependent operation refreshes the verified tip. -/
def dispatchSession (config : NativeHost.Config)
    (state : IO.Ref (Option (NativeHostSession.Session config)))
    (meteringProfile : Lean.Json)
    (providerRoutes : List (Nat × Kernel.ProviderMetering.Schedule))
    (fnDispatch : UInt8 → List UInt8 → IO (UInt8 × List UInt8))
    (operation : UInt8) (payload : List UInt8) : IO (UInt8 × List UInt8) := do
  match operation with
  | 0 =>
      unless payload.isEmpty do throw (RequestRefusal.malformed "describe does not accept a payload")
      discard <| sessionOpened config state
      return (0, (descriptionLoaded config).compress.toUTF8.toList)
  | 1 =>
      let t0 ← IO.monoMsNow
      let opened ← sessionOpened config state
      phaseTrace "op1 refresh" t0
      match ← NativeHost.prepareAuthorizedLoaded config opened payload with
      | .ok plan => return (1, signingPlanCodec.encode plan)
      | .error detail => return (255, refusalFrame "prepare" detail)
  | 2 | 3 => fnDispatch operation payload
  | 4 =>
      let opened ← sessionOpened config state
      ReceiptContinuity.remember config opened.durable
      match ← NativeHost.challengeWireLoaded config opened payload with
      | .ok challenges => return (4, challenges)
      | .error detail => return (255, refusalFrame "observation" detail)
  | 5 =>
      let t0 ← IO.monoMsNow
      let current ← sessionCurrent config state
      let opened := current.opened
      ReceiptContinuity.remember config opened.durable
      phaseTrace "op5 refresh" t0
      match ← NativeObservationOpeningCache.queryWireLoaded config opened current.openingCache payload with
      | .ok view => return (5, view)
      | .error detail => return (255, refusalFrame "observation" detail)
  | 6 =>
      unless payload.isEmpty do throw (RequestRefusal.malformed "profile does not accept a payload")
      return (6, meteringProfile.compress.toUTF8.toList)
  | 7 =>
      let (kind, source) ← splitKind payload
      let some text := String.fromUTF8? source.toByteArray
        | throw (RequestRefusal.malformed "native host author source is not UTF-8")
      let value ← RequestRefusal.clientBytes (Minidregg.Host.Json.parse text)
      if kind == "pay-claim-rotation" then
        unless source.length ≤ 4096 do throw (RequestRefusal.malformed "claim rotation JSON exceeds bound")
        return (7, ← RequestRefusal.clientBytes (Minidregg.Host.PayClaims.authorRotation value))
      return (7, ← RequestRefusal.clientBytes (authorHost config providerRoutes kind value))
  | 8 =>
      let (kind, source) ← splitKind payload
      if kind == "object-audience" then
        let walked ← sessionWalked config state
        match ← NativeHost.objectAudienceLoaded config walked.target walked.verified source with
        | .ok view => return (8, (objectAudienceJson view).compress.toUTF8.toList)
        | .error reason => return (255, refusalFrame "object-audience" reason)
      else if kind == "object-roster-inspect" then
        let value ← RequestRefusal.clientBytes (objectRosterJson source)
        return (8, value.compress.toUTF8.toList)
      else if kind == "object-audience-roster" then
        -- Fixed nested pairs carry bytes only, never service-side file paths.
        let (sourceObservation, rest) ← splitPair source
        let (catalogObservation, rest) ← splitPair rest
        let (plannedBytes, rosterBytes) ← splitPair rest
        let some plannedText := String.fromUTF8? plannedBytes.toByteArray
          | throw (RequestRefusal.malformed "object audience state is not UTF-8")
        let plannedJson ← RequestRefusal.clientBytes (Minidregg.Host.Json.parse plannedText)
        let planned ← RequestRefusal.clientBytes (Minidregg.Host.Json.audienceState "$" plannedJson)
        let walked ← sessionWalked config state
        let (audience, roster) ← IO.ofExcept (← NativeHost.objectAudienceRosterLoaded config
          walked.target walked.verified sourceObservation catalogObservation rosterBytes planned)
        return (8, (checkedObjectRosterJson audience roster rosterBytes).compress.toUTF8.toList)
      else
        let value ← RequestRefusal.clientBytes (if kind == "pay-claim-plan" then
          Minidregg.Host.PayClaims.claimPlanJson source
          else if kind == "pay-claim-command" then Minidregg.Host.PayClaims.claimCommandJson source
          else if kind == "pay-claim-ingress" then Minidregg.Host.PayClaims.claimIngressJson config source
          else inspectHost config kind source)
        return (8, value.compress.toUTF8.toList)
  | 9 =>
      let some text := String.fromUTF8? payload.toByteArray
        | throw (RequestRefusal.malformed "native host signatures source is not UTF-8")
      let value ← RequestRefusal.clientBytes (Minidregg.Host.Json.parse text)
      return (9, ← RequestRefusal.clientBytes (Minidregg.Host.Json.signatures value))
  | 10 =>
      let (challengeBytes, signaturesBytes) ← splitPair payload
      let some challenge := NativeObservationCodec.challengeCodec.decode challengeBytes
        | throw (RequestRefusal.malformed "noncanonical observation challenge")
      let signatures ← decodeSignatures signaturesBytes
      let signed ← RequestRefusal.clientBytes (NativeObservationCodec.assemble challenge signatures)
      return (10, NativeObservationCodec.signedCodec.encode signed)
  | 11 =>
      let (planBytes, signaturesBytes) ← splitPair payload
      let some plan := signingPlanCodec.decode planBytes
        | throw (RequestRefusal.malformed "noncanonical signing plan")
      let signatures ← decodeSignatures signaturesBytes
      let call ← RequestRefusal.clientBytes (NativeHost.assemble plan signatures)
      return (11, callCodec.encode call)
  | 130 =>
      -- Dry run (P-AFFORDANCES): plan as op 1, assemble as op 11, submit as op 2
      -- over a Store writer that never appends (`Host.DryRun`). Commits nothing.
      let (observation, signaturesBytes) ← splitPair payload
      let signatures ← decodeSignatures signaturesBytes
      let session ← sessionCurrent config state
      match ← DryRun.dryRunLoaded config session.opened observation signatures with
      | .admitted plan => return (130, signingPlanCodec.encode plan)
      | .stopped outcome => return (255, outcomeCodec.encode outcome)
  | 150 =>
      -- law-sat (C-SAT-2): a pure function of the request bytes; reads no Store.
      LawSatWire.lawSatSession payload
  | 151 => fnDispatch operation payload
  | 20 =>
      return (20, outcomeCodec.encode
        (← selectedReleaseSubmitSession config state payload))
  | 21 =>
      return (21, outcomeCodec.encode
        (← selectedReleaseLookupSession config state payload))
  | 22 =>
      return (22, outcomeCodec.encode
        (← applicationLifecycleBeginSubmitSession config state payload))
  | 23 =>
      return (23, outcomeCodec.encode
        (← applicationLifecycleBeginLookupSession config state payload))
  | 27 =>
      return (27, outcomeCodec.encode
        (← applicationLifecycleClaimLookupSession config state payload))
  | 24 =>
      return (24, outcomeCodec.encode
        (← selectedSourcePublicationSubmitSession config state payload))
  | 25 =>
      return (25, outcomeCodec.encode
        (← selectedSourcePublicationLookupSession config state payload))
  | 35 => fnDispatch operation payload
  | 47 =>
      return (47, outcomeCodec.encode
        (← applicationAgentDispatchLookupSession config state payload))
  | 77 =>
      return (77, outcomeCodec.encode
        (← applicationAgentLifetimeDispatchLookupSession config state payload))
  | 36 => fnDispatch operation payload
  | 37 =>
      let (planBytes, signaturesBytes) ← splitPair payload
      let some plan := ApplicationDispatchAuthoring.planCodec.decode planBytes
        | throw (RequestRefusal.malformed "noncanonical dispatch authoring plan")
      let signatures ← decodeSignatures signaturesBytes
      let ingress ← RequestRefusal.clientBytes (ApplicationDispatchAuthoring.assemble plan signatures)
      return (37, ingress)
  | 38 =>
      return (38, outcomeCodec.encode
        (← applicationLifecycleCompletionSubmitSession config state payload))
  | 39 =>
      return (39, outcomeCodec.encode
        (← applicationLifecycleCompletionLookupSession config state payload))
  | 41 =>
      return (41, outcomeCodec.encode
        (← fnConsumerNamespaceLookupSession config state payload))
  | _ => fnDispatch operation payload

/-- Operator-private paid-agent authoring. Exact fixed selectors come from the
startup config and are compared before exposing any signing header, including
on a retained detached plan supplied for assembly. The signed requests still
need fresh ordinary reserve/event21 native admission. -/
def agentDispatchAuthorSession (config : NativeHost.Config)
    (state : IO.Ref (Option (NativeHostSession.Session config)))
    (approved : ApplicationDispatchAgentPaidAuthoring.FixedSelectors)
    (operation : UInt8) (payload : List UInt8) : IO (UInt8 × List UInt8) := do
  match operation with
  | 58 =>
      let some request := ApplicationDispatchAgentPaidAuthoring.requestCodec.decode payload
        | throw (RequestRefusal.malformed "noncanonical agent reserve author request")
      unless request.matchesFixed approved do
        throw (IO.userError "agent reserve request differs from operator pin")
      let session ← sessionWalked config state
      let plan ← IO.ofExcept <|
        ApplicationDispatchAgentPaidAuthoring.prepareReserveVerified
          config session.verified request
      let bytes := ApplicationDispatchAgentPaidAuthoring.reservePlanCodec.encode plan
      unless bytes.length < FnEvidenceCodec.maxHostFrameBytes do
        throw (IO.userError "agent reserve plan exceeds host frame bound")
      return (58, bytes)
  | 59 =>
      let (planBytes, signaturesBytes) ← splitPair payload
      let some plan := ApplicationDispatchAgentPaidAuthoring.reservePlanCodec.decode planBytes
        | throw (RequestRefusal.malformed "noncanonical agent reserve plan")
      unless plan.request.matchesFixed approved do
        throw (IO.userError "agent reserve plan differs from operator pin")
      let signatures ← decodeSignatures signaturesBytes
      let signed ← IO.ofExcept <|
        ApplicationDispatchAgentPaidAuthoring.assembleReserve plan signatures
      let some (domain, semantics, command) :=
          DeclaredResourceController.decodeSignedBytes signed
        | throw (RequestRefusal.malformed "noncanonical agent reserve signed ingress")
      unless domain == config.deployment.domain &&
          semantics == config.profile.semantics do
        throw (IO.userError "agent reserve signed ingress differs from pinned profile")
      let callBytes := NativeHostCodec.callCodec.encode (.invoke command)
      unless callBytes.length < FnEvidenceCodec.maxHostFrameBytes do
        throw (IO.userError "agent reserve native call exceeds host frame bound")
      return (59, callBytes)
  | 48 =>
      let some request := ApplicationDispatchAgentPaidAuthoring.paidRequestCodec.decode payload
        | throw (RequestRefusal.malformed "noncanonical paid agent dispatch author request")
      unless request.fixed.matchesFixed approved do
        throw (IO.userError "paid agent request differs from operator pin")
      let session ← sessionWalked config state
      let plan ← IO.ofExcept <|
        ApplicationDispatchAgentPaidAuthoring.preparePaidVerified
          config session.verified request
      let bytes := ApplicationDispatchAgentPaidAuthoring.paidPlanCodec.encode plan
      unless bytes.length < FnEvidenceCodec.maxHostFrameBytes do
        throw (IO.userError "paid agent dispatch plan exceeds host frame bound")
      return (48, bytes)
  | 49 =>
      let (planBytes, signaturesBytes) ← splitPair payload
      let some plan := ApplicationDispatchAgentPaidAuthoring.paidPlanCodec.decode planBytes
        | throw (RequestRefusal.malformed "noncanonical paid agent dispatch plan")
      unless plan.request.fixed.matchesFixed approved do
        throw (IO.userError "paid agent plan differs from operator pin")
      let (appBytes, payerBytes) ← splitPair signaturesBytes
      let appSignatures ← decodeSignatures appBytes
      let payerSignatures ← decodeSignatures payerBytes
      let ingress ← IO.ofExcept <|
        ApplicationDispatchAgentPaidAuthoring.assemblePaid
          plan appSignatures payerSignatures
      unless ingress.length < FnEvidenceCodec.maxHostFrameBytes do
        throw (IO.userError "paid agent dispatch ingress exceeds host frame bound")
      return (49, ingress)
  | _ => throw (IO.userError "unsupported paid agent authoring operation")

/-- Event26 has independent reserve and paid plans. Only operator-pinned
selectors reach source planning; retained plans are checked again before
detached signatures are assembled. The final native submit re-admits fresh. -/
def requireOneLifetimeDispatchPin
    (approved : List ApplicationAgentLifetimeDispatchPaidAuthoring.FixedSelectors)
    (predicate : ApplicationAgentLifetimeDispatchPaidAuthoring.FixedSelectors → Bool) : IO Unit := do
  unless (approved.filter predicate).length == 1 do
    throw (IO.userError "lifetime dispatch request differs from unique full operator pin")

def agentLifetimeDispatchAuthorSession (config : NativeHost.Config)
    (state : IO.Ref (Option (NativeHostSession.Session config)))
    (approved : List ApplicationAgentLifetimeDispatchPaidAuthoring.FixedSelectors)
    (operation : UInt8) (payload : List UInt8) : IO (UInt8 × List UInt8) := do
  match operation with
  | 80 =>
      let some request := ApplicationAgentLifetimeDispatchPaidAuthoring.requestCodec.decode payload
        | throw (RequestRefusal.malformed "noncanonical lifetime reserve request")
      requireOneLifetimeDispatchPin approved request.matchesFixed
      let session ← sessionWalked config state
      let plan ← IO.ofExcept <|
        ApplicationAgentLifetimeDispatchPaidAuthoring.prepareReserveVerified
          config session.verified request
      let bytes := ApplicationAgentLifetimeDispatchPaidAuthoring.reservePlanCodec.encode plan
      unless bytes.length < FnEvidenceCodec.maxHostFrameBytes do
        throw (IO.userError "lifetime reserve plan exceeds host frame bound")
      return (80, bytes)
  | 81 =>
      let (planBytes, signaturesBytes) ← splitPair payload
      let some plan := ApplicationAgentLifetimeDispatchPaidAuthoring.reservePlanCodec.decode
          planBytes
        | throw (RequestRefusal.malformed "noncanonical lifetime reserve plan")
      requireOneLifetimeDispatchPin approved plan.request.matchesFixed
      let signatures ← decodeSignatures signaturesBytes
      let signed ← IO.ofExcept <|
        ApplicationAgentLifetimeDispatchPaidAuthoring.assembleReserve plan signatures
      let some (domain, semantics, command) :=
          DeclaredResourceController.decodeSignedBytes signed
        | throw (RequestRefusal.malformed "noncanonical lifetime reserve signed ingress")
      unless domain == config.deployment.domain &&
          semantics == config.profile.semantics do
        throw (IO.userError "lifetime reserve signed ingress differs from pinned profile")
      let callBytes := NativeHostCodec.callCodec.encode (.invoke command)
      unless callBytes.length < FnEvidenceCodec.maxHostFrameBytes do
        throw (IO.userError "lifetime reserve native call exceeds host frame bound")
      return (81, callBytes)
  | 78 =>
      let some request := ApplicationAgentLifetimeDispatchPaidAuthoring.paidRequestCodec.decode
          payload
        | throw (RequestRefusal.malformed "noncanonical lifetime paid dispatch request")
      requireOneLifetimeDispatchPin approved request.fixed.matchesFixed
      let session ← sessionWalked config state
      let plan ← IO.ofExcept <|
        ApplicationAgentLifetimeDispatchPaidAuthoring.preparePaidVerified
          config session.verified request
      let bytes := ApplicationAgentLifetimeDispatchPaidAuthoring.paidPlanCodec.encode plan
      unless bytes.length < FnEvidenceCodec.maxHostFrameBytes do
        throw (IO.userError "lifetime paid plan exceeds host frame bound")
      return (78, bytes)
  | 79 =>
      let (planBytes, signaturesBytes) ← splitPair payload
      let some plan := ApplicationAgentLifetimeDispatchPaidAuthoring.paidPlanCodec.decode planBytes
        | throw (RequestRefusal.malformed "noncanonical lifetime paid dispatch plan")
      requireOneLifetimeDispatchPin approved plan.request.fixed.matchesFixed
      let (appBytes, grantAndPayer) ← splitPair signaturesBytes
      let (grantSignature, payerBytes) ← splitPair grantAndPayer
      unless grantSignature.length == 64 do
        throw (IO.userError "lifetime grant observation signature must be 64 bytes")
      let appSignatures ← decodeSignatures appBytes
      let payerSignatures ← decodeSignatures payerBytes
      let ingress ← IO.ofExcept <|
        ApplicationAgentLifetimeDispatchPaidAuthoring.assemblePaid
          plan appSignatures grantSignature payerSignatures
      unless ingress.length < FnEvidenceCodec.maxHostFrameBytes do
        throw (IO.userError "lifetime paid ingress exceeds host frame bound")
      return (79, ingress)
  | _ => throw (IO.userError "unsupported lifetime dispatch authoring operation")

def maxFrame : Nat := FnEvidenceCodec.maxHostFrameBytes

/-- Inspection repeats the exact frame and full request as hex. A hostd
consumer must cap this JSON separately from the smaller binary input. -/
def maxDispatchInspectionJsonBytes : Nat := 8 * maxFrame

/-- Eight MiB of exact HTTP body is sixteen MiB of JSON hex before headers.
The private authoring CLI reads a bounded envelope before UTF-8/JSON parsing. -/
def maxDispatchAuthorJsonBytes : Nat := 22 * 1024 * 1024

partial def readExactly (input : IO.FS.Stream) (count : Nat) (acc : ByteArray := ByteArray.empty) :
    IO ByteArray := do
  if acc.size == count then return acc
  let chunk ← input.read (count - acc.size).toUSize
  if chunk.isEmpty then throw (IO.userError "truncated native host frame")
  readExactly input count (acc ++ chunk)

def frameLength (bytes : ByteArray) : Nat :=
  bytes.toList.foldr (fun byte rest => byte.toNat + 256 * rest) 0

def lengthBytes (length : Nat) : ByteArray :=
  [UInt8.ofNat length, UInt8.ofNat (length / 256),
    UInt8.ofNat (length / 65536), UInt8.ofNat (length / 16777216)].toByteArray

def writeSessionFrame (output : IO.FS.Stream) (operation : UInt8)
    (payload : List UInt8) : IO Unit := do
  let response := (operation :: payload).toByteArray
  if response.size > maxFrame then
    throw (IO.userError "native host response exceeds frame budget")
  output.write (lengthBytes response.size ++ response)
  output.flush

/-- Op34 writes a committed permit only inside the receiver's point-in-time
physical-tip callback. This check is not a lease against later Store writes;
the external host must fence process generation and reconcile uncertain
delivery without replaying an HTTP effect. Other outcomes carry no permit. -/
def dispatchApplicationSubmitSession (config : NativeHost.Config)
    (state : IO.Ref (Option (NativeHostSession.Session config)))
    (payload : List UInt8) (output : IO.FS.Stream) (routeBound : Bool := false) : IO Unit := do
  let session ← sessionWalked config state
  let result ← if routeBound then
      ApplicationDispatchReceiver.receiveRouteBoundVerified config session.verified payload
    else ApplicationDispatchReceiver.receiveVerified config session.verified payload
  match result with
  | .permitted permit =>
      let handed ← permit.withFreshTip fun committedBytes =>
        writeSessionFrame output 34 committedBytes
      match handed with
      | .ok _ => sessionSetWalked state permit.old permit.readback
      | .error detail =>
          writeSessionFrame output 34 <| outcomeCodec.encode <|
            NativeHost.publicSubmissionOutcome (.uncertain detail.toUTF8.toList)
  | .committed committed =>
      -- Exact durable receipt/cache recovery never authorizes another fd3 call.
      writeSessionFrame output 34 <| outcomeCodec.encode <|
        .confirmed committed.confirmation committed.receipt
      sessionSetWalked state committed.old committed.readback
  | .historical receipt =>
      writeSessionFrame output 34 <| outcomeCodec.encode <| .confirmed .replayed receipt
  | .noRecordRefused refusal =>
      match ← refusal.withFreshTip (fun bytes => writeSessionFrame output 164 bytes) with
      | .ok _ => pure ()
      | .error detail =>
          writeSessionFrame output 34 <| outcomeCodec.encode <|
            NativeHost.publicSubmissionOutcome (.uncertain detail.toUTF8.toList)
  | .rejected _ =>
      writeSessionFrame output 34 <| outcomeCodec.encode <|
        NativeHost.publicSubmissionOutcome
          (.refused .operationRejected "application-dispatch".toUTF8.toList "request refused".toUTF8.toList)
  | .contention =>
      writeSessionFrame output 34 <| outcomeCodec.encode <|
        NativeHost.publicSubmissionOutcome .contention
  | .unavailable detail =>
      writeSessionFrame output 34 <| outcomeCodec.encode <|
        NativeHost.publicSubmissionOutcome (.unavailable detail.toUTF8.toList)
  | .uncertain detail =>
      writeSessionFrame output 34 <| outcomeCodec.encode <|
        NativeHost.publicSubmissionOutcome (.uncertain detail.toUTF8.toList)

/-- Op152 is a read-only continuity challenge. It retains the same verified
session and emits no event or paid dispatch. A fresh physical-tip callback is
mandatory even when no history extension was needed at session refresh. -/
def dispatchStreamContinuitySession (config : NativeHost.Config)
    (state : IO.Ref (Option (NativeHostSession.Session config)))
    (payload : List UInt8) (output : IO.FS.Stream) : IO Unit := do
  let session ← sessionWalked config state
  match ← ApplicationStreamContinuity.receiveVerified config session.verified payload with
  | .ok attestation =>
      match ← attestation.withFreshTip (fun bytes => writeSessionFrame output 152 bytes) with
      | .ok _ => pure ()
      | .error detail =>
          writeSessionFrame output 152 <| outcomeCodec.encode <|
            NativeHost.publicSubmissionOutcome (.unavailable detail.toUTF8.toList)
  | .error _ =>
      writeSessionFrame output 152 <| outcomeCodec.encode <|
        NativeHost.publicSubmissionOutcome
          (.refused .operationRejected "stream-continuity".toUTF8.toList
            "current continuation refused".toUTF8.toList)

/-- Op154 admits a new immutable local route, never an app dispatch. -/
def dispatchRouteAdmissionSession (config : NativeHost.Config)
    (state : IO.Ref (Option (NativeHostSession.Session config)))
    (payload : List UInt8) (output : IO.FS.Stream) : IO Unit := do
  let session ← sessionWalked config state
  match ← ApplicationRouteAdmission.receiveVerified config session.verified payload with
  | .ok attestation =>
      match ← attestation.withFreshTip (fun bytes => writeSessionFrame output 154 bytes) with
      | .ok _ => pure ()
      | .error detail =>
          writeSessionFrame output 154 <| outcomeCodec.encode <|
            NativeHost.publicSubmissionOutcome (.unavailable detail.toUTF8.toList)
  | .error _ =>
      writeSessionFrame output 154 <| outcomeCodec.encode <|
        NativeHost.publicSubmissionOutcome
          (.refused .operationRejected "route-admission".toUTF8.toList
            "current route admission refused".toUTF8.toList)

/-- Op46 hands out the distinct paid agent permit only from an exact event21
CAS/readback and a final point-in-time physical tip check. Historical op47 is
receipt-only; neither result is a lease across an external fd3 delivery. -/
def dispatchAgentSubmitSession (config : NativeHost.Config)
    (state : IO.Ref (Option (NativeHostSession.Session config)))
    (payload : List UInt8) (output : IO.FS.Stream) : IO Unit := do
  let session ← sessionWalked config state
  let result ← ApplicationDispatchAgentReceiver.receiveVerified config session.verified payload
  match result with
  | .permitted permit =>
      let handed ← permit.withFreshTip fun committedBytes =>
        writeSessionFrame output 46 committedBytes
      match handed with
      | .ok _ => sessionSetWalked state permit.old permit.readback
      | .error detail =>
          writeSessionFrame output 46 <| outcomeCodec.encode <|
            NativeHost.publicSubmissionOutcome (.uncertain detail.toUTF8.toList)
  | .committed committed =>
      -- Exact receipt recovery is not another physical agent dispatch permit.
      writeSessionFrame output 46 <| outcomeCodec.encode <|
        .confirmed committed.confirmation committed.receipt
      sessionSetWalked state committed.old committed.readback
  | .rejected _ =>
      writeSessionFrame output 46 <| outcomeCodec.encode <|
        NativeHost.publicSubmissionOutcome
          (.refused .operationRejected "application-agent-dispatch".toUTF8.toList
            "request refused".toUTF8.toList)
  | .contention =>
      writeSessionFrame output 46 <| outcomeCodec.encode <|
        NativeHost.publicSubmissionOutcome .contention
  | .unavailable detail =>
      writeSessionFrame output 46 <| outcomeCodec.encode <|
        NativeHost.publicSubmissionOutcome (.unavailable detail.toUTF8.toList)
  | .uncertain detail =>
      writeSessionFrame output 46 <| outcomeCodec.encode <|
        NativeHost.publicSubmissionOutcome (.uncertain detail.toUTF8.toList)

/-- A fresh event26 CAS winner alone can emit the distinct lifetime permit.
Historical lookup at op77 is receipt-only, so an uncertain handoff cannot
resend a physical effect. -/
def dispatchAgentLifetimeSubmitSession (config : NativeHost.Config)
    (state : IO.Ref (Option (NativeHostSession.Session config)))
    (payload : List UInt8) (output : IO.FS.Stream) : IO Unit := do
  let session ← sessionWalked config state
  let result ← ApplicationAgentLifetimeDispatchReceiver.receiveVerified
    config session.verified payload
  match result with
  | .permitted permit =>
      let handed ← permit.withFreshTip fun committedBytes =>
        writeSessionFrame output 76 committedBytes
      match handed with
      | .ok _ => sessionSetWalked state permit.old permit.readback
      | .error detail =>
          writeSessionFrame output 76 <| outcomeCodec.encode <|
            NativeHost.publicSubmissionOutcome (.uncertain detail.toUTF8.toList)
  | .rejected _ =>
      writeSessionFrame output 76 <| outcomeCodec.encode <|
        NativeHost.publicSubmissionOutcome
          (.refused .operationRejected "application-agent-lifetime-dispatch".toUTF8.toList
            "request refused".toUTF8.toList)
  | .contention =>
      writeSessionFrame output 76 <| outcomeCodec.encode <|
        NativeHost.publicSubmissionOutcome .contention
  | .unavailable detail =>
      writeSessionFrame output 76 <| outcomeCodec.encode <|
        NativeHost.publicSubmissionOutcome (.unavailable detail.toUTF8.toList)
  | .uncertain detail =>
      writeSessionFrame output 76 <| outcomeCodec.encode <|
        NativeHost.publicSubmissionOutcome (.uncertain detail.toUTF8.toList)

/-- Op26 returns a launch reservation only inside the receiver's physical-tip
callback. This is a point-in-time check, not a lease against later writes or
proof that the external process has started. -/
def dispatchLifecycleClaimSubmitSession (config : NativeHost.Config)
    (state : IO.Ref (Option (NativeHostSession.Session config)))
    (payload : List UInt8) (output : IO.FS.Stream) : IO Unit := do
  let session ← sessionWalked config state
  let some _ := ApplicationLifecycleClaimV3Ingress.codec.decode payload
    | writeSessionFrame output 26 <| outcomeCodec.encode <|
        NativeHost.publicSubmissionOutcome
          (.refused .malformed "application-lifecycle-claim".toUTF8.toList
            "fresh claim requires canonical launch-bound v3 ingress".toUTF8.toList)
      return
  let result ← ApplicationLifecycleClaimV3Receiver.receiveVerified config
    session.verified payload
  match result with
  | .reserved reservation =>
      match reservation.confirmation with
      | .installed =>
          if reservation.freshCasWinner then
            let handed ← reservation.withFreshTip fun committedBytes =>
              writeSessionFrame output 26 committedBytes
            match handed with
            | .ok _ => sessionSetWalked state reservation.old reservation.readback
            | .error detail =>
                writeSessionFrame output 26 <| outcomeCodec.encode <|
                  NativeHost.publicSubmissionOutcome (.uncertain detail.toUTF8.toList)
          else
            sessionSetWalked state reservation.old reservation.readback
            writeSessionFrame output 26 <| outcomeCodec.encode <|
              NativeHost.publicSubmissionOutcome
                (.confirmed .replayed reservation.receipt)
      | .recoveredAfterUncertainResponse | .replayed =>
          sessionSetWalked state reservation.old reservation.readback
          writeSessionFrame output 26 <| outcomeCodec.encode <|
            NativeHost.publicSubmissionOutcome
              (.confirmed .replayed reservation.receipt)
  | .rejected _ =>
      writeSessionFrame output 26 <| outcomeCodec.encode <|
        NativeHost.publicSubmissionOutcome
          (.refused .operationRejected "application-lifecycle-claim".toUTF8.toList
            "request refused".toUTF8.toList)
  | .contention =>
      writeSessionFrame output 26 <| outcomeCodec.encode <|
        NativeHost.publicSubmissionOutcome .contention
  | .unavailable detail =>
      writeSessionFrame output 26 <| outcomeCodec.encode <|
        NativeHost.publicSubmissionOutcome (.unavailable detail.toUTF8.toList)
  | .uncertain detail =>
      writeSessionFrame output 26 <| outcomeCodec.encode <|
        NativeHost.publicSubmissionOutcome (.uncertain detail.toUTF8.toList)

/-- Read and discard `count` bytes in bounded chunks: an over-length frame is
skipped without buffering it, so the next frame starts where it should. -/
partial def discardExactly (input : IO.FS.Stream) (count : Nat) : IO Unit := do
  if count == 0 then return
  let chunk ← input.read (min count 65536).toUSize
  if chunk.isEmpty then throw (IO.userError "truncated native host frame")
  discardExactly input (count - chunk.size)

/-- One request. Every frame is answered: by its handler, or — when the handler
throws — by `RequestRefusal.frame` under operation 255, and the loop goes on.
The process ends only on end of input, a truncated frame (the supervisor's pipe
closed), a poisoned session (Store integrity: a new process must reopen from the
MAC'd checkpoint; the request is answered `unavailable` first), or a handler
that threw after its reply already left (a second frame would desynchronise
the pipe). `mini serve` restarts the Host in the last three cases. -/
def serveFrame (config : NativeHost.Config)
    (state : IO.Ref (Option (NativeHostSession.Session config)))
    (meteringProfile : Lean.Json)
    (providerRoutes : List (Nat × Kernel.ProviderMetering.Schedule))
    (fnDispatch : UInt8 → List UInt8 → IO (UInt8 × List UInt8))
    (applicationDispatch : Bool → List UInt8 → IO.FS.Stream → IO Unit)
    (operation : UInt8) (payload : List UInt8) (output : IO.FS.Stream) : IO Unit := do
  let wrote ← IO.mkRef false
  let tracked : IO.FS.Stream :=
    { output with write := fun bytes => do wrote.set true; output.write bytes }
  try
    if operation == 34 || operation == 164 then
      applicationDispatch (operation == 164) payload tracked
    else if operation == 154 then
      dispatchRouteAdmissionSession config state payload tracked
    else if operation == 152 then
      dispatchStreamContinuitySession config state payload tracked
    else if operation == 46 then
      dispatchAgentSubmitSession config state payload tracked
    else if operation == 76 then
      dispatchAgentLifetimeSubmitSession config state payload tracked
    else if operation == 26 then
      dispatchLifecycleClaimSubmitSession config state payload tracked
    else
      let started ← IO.monoMsNow
      let (responseOperation, responsePayload) ←
        dispatchSession config state meteringProfile providerRoutes fnDispatch operation payload
      writeSessionFrame tracked responseOperation responsePayload
      if (← IO.getEnv "MINIDREGG_HOST_TRACE").isSome then
        IO.eprintln s!"host-trace op {operation} {(← IO.monoMsNow) - started} ms"
  catch error =>
    if ← wrote.get then
      throw (IO.userError s!"op {operation} failed after its reply was written: {error}")
    if (← state.get).isNone then
      writeSessionFrame output 255 <| outcomeCodec.encode <|
        .unavailable "host session reopening".toUTF8.toList
      throw (IO.userError s!"op {operation}: native host session invalidated: {error}")
    IO.eprintln s!"minidregg-host: op {operation} refused: {error}"
    writeSessionFrame output 255 (RequestRefusal.frame operation error)
  if (← state.get).isNone then
    throw (IO.userError s!"op {operation}: native host session invalidated")

partial def serveSession (config : NativeHost.Config)
    (state : IO.Ref (Option (NativeHostSession.Session config)))
    (meteringProfile : Lean.Json)
    (providerRoutes : List (Nat × Kernel.ProviderMetering.Schedule))
    (fnDispatch : UInt8 → List UInt8 → IO (UInt8 × List UInt8))
    (applicationDispatch : Bool → List UInt8 → IO.FS.Stream → IO Unit)
    (input output : IO.FS.Stream) : IO Unit := do
  let first ← input.read 1
  if first.isEmpty then return
  let lengthWire ← readExactly input 4 first
  let length := frameLength lengthWire
  if length == 0 then
    writeSessionFrame output 255 (RequestRefusal.frame 255
      (RequestRefusal.malformed "empty native host frame"))
  else if length > RetainedSegmentInspection.maxLookupFrame then
    discardExactly input length
    writeSessionFrame output 255 (RequestRefusal.frame 255
      (RequestRefusal.malformed "native host frame exceeds frame bound"))
  else
    let opcode ← readExactly input 1
    let operation := opcode[0]!
    -- Only carried exact-call recovery needs the bounded identity-header
    -- overhead. Refuse other oversized operations before allocating payload.
    if length > maxFrame && operation != 153 then
      discardExactly input (length - 1)
      writeSessionFrame output 255 (RequestRefusal.frame operation
        (RequestRefusal.malformed "native host frame exceeds operation bound"))
    else
      let payload ← readExactly input (length - 1)
      serveFrame config state meteringProfile providerRoutes fnDispatch applicationDispatch operation payload.toList output
  serveSession config state meteringProfile providerRoutes fnDispatch applicationDispatch input output

/-- Execute from one private copy throughout this stdio process. The copy is
the pinned launch artifact; the originally configured pathname may later be
replaced or have a symlink target swapped without changing the session's
historical verifier. The OS must protect this private directory from writes
by other actors for the lifetime of the process. -/
def withPinnedSignature {α : Type} (config : NativeHost.Config)
    (body : NativeHost.Config → IO α) : IO α :=
  IO.FS.withTempDir fun directory => do
    let pinned := directory / "credential-verifier"
    let bytes ← IO.FS.readBinFile config.signature.binary
    IO.FS.writeBinFile pinned bytes
    let permission ← IO.Process.output
      { cmd := "/bin/chmod", args := #["0500", pinned.toString] }
    unless permission.exitCode == 0 do
      throw (IO.userError "cannot make pinned credential verifier executable")
    -- A launch failure is detected before the first semantic replay. The
    -- verifier's usage exit here is expected; it has no arguments yet.
    discard <| IO.Process.output { cmd := pinned.toString, args := #[] }
    body { config with signature := ⟨pinned⟩ }

partial def readOperatorSnapshot (input : IO.FS.Handle) (limit : Nat)
    (acc : ByteArray := ByteArray.empty) : IO ByteArray := do
  if acc.size > limit then
    throw (IO.userError "operator executable or key exceeds snapshot bound")
  let chunk ← input.read (min 4096 (limit + 1 - acc.size)).toUSize
  if chunk.isEmpty then return acc
  readOperatorSnapshot input limit (acc ++ chunk)

def snapshotOperatorFile (directory : System.FilePath) (name sourcePath : String)
    (limit : Nat) (mode : String) : IO String := do
  unless sourcePath.startsWith "/" do
    throw (IO.userError s!"operator {name} path must be absolute")
  let input ← IO.FS.Handle.mk sourcePath .read
  let bytes ← readOperatorSnapshot input limit
  unless !bytes.isEmpty do
    throw (IO.userError s!"operator {name} is empty")
  let destination := directory / name
  IO.FS.writeBinFile destination bytes
  let permission ← IO.Process.output
    { cmd := "/bin/chmod", args := #[mode, destination.toString] }
  unless permission.exitCode == 0 do
    throw (IO.userError s!"cannot pin operator {name} permissions")
  return destination.toString

def withPinnedStorageBinary {α : Type} (config : NativeHost.Config)
    (body : NativeHost.Config → IO α) : IO α :=
  IO.FS.withTempDir fun directory => do
    let pinned ← snapshotOperatorFile directory "origin-storage-helper"
      config.storage.binary.toString (64 * 1024 * 1024) "0500"
    body { config with storage := { config.storage with
      binary := System.FilePath.mk pinned } }

/-- The logical `fnBinary` remains in durable pollControlBinding. Execution
uses a private byte snapshot of the local helper and ML public PEM for the
whole process. A remote fn image behind a bridge remains an operator custody
assumption and must be separately qualified. -/
def snapshotFnPinFiles (directory : System.FilePath) (label pinPath : String) :
    IO (String × String) := do
  let json ← IO.ofExcept (Minidregg.Host.Json.parse (← IO.FS.readFile pinPath))
  let fnBinary ← IO.ofExcept (json.getObjValAs? String "fnBinary")
  let mlPublicKey ← IO.ofExcept (json.getObjValAs? String "mlPublicKey")
  let executable ← snapshotOperatorFile directory (label ++ "-fn-helper")
    fnBinary (64 * 1024 * 1024) "0500"
  let publicKey ← snapshotOperatorFile directory (label ++ "-ml-public.pem")
    mlPublicKey 8192 "0400"
  return (executable, publicKey)

def withFnPollService {α : Type} (settings : Settings)
    (body : Option FnPollService → IO α) : IO α := do
  let some source := settings.fnPoll | return ← body none
  unless [source.originConfigPath, source.fnPinPath, source.scopePath,
      source.policyPath, source.controlPath].all (·.startsWith "/") do
    throw (IO.userError "fn poll service paths must be operator-selected absolute paths")
  IO.FS.withTempDir fun directory => do
    let copyManifest := fun (name sourcePath : String) (bound : Nat) => do
      let bytes ← IO.FS.readBinFile sourcePath
      unless bytes.size > 0 && bytes.size ≤ bound do
        throw (IO.userError s!"fn poll service manifest {name} exceeds bound")
      let destination := directory / name
      IO.FS.writeBinFile destination bytes
      pure (destination.toString : String)
    let originConfigPath ← copyManifest "origin-config.json" source.originConfigPath 65536
    let fnPinPath ← copyManifest "fn-pin.json" source.fnPinPath 8192
    let (fnExecutable, fnPublicKey) ← snapshotFnPinFiles directory "b" fnPinPath
    let scopePath ← copyManifest "scope.json" source.scopePath 8192
    let policyPath ← copyManifest "policy.json" source.policyPath 8192
    body (some ⟨originConfigPath, fnPinPath, fnExecutable, fnPublicKey,
      scopePath, policyPath,
      source.controlPath⟩)

def readBytes (path : String) : IO (List UInt8) :=
  return (← IO.FS.readBinFile path).toList

/-- Evidence files are capped while reading, before any source-owned decoder. -/
partial def readBoundedLoop (input : IO.FS.Handle) (limit : Nat)
    (acc : ByteArray := ByteArray.empty) : IO (List UInt8) := do
  if acc.size > limit then throw (IO.userError "Mini evidence input exceeds byte bound")
  let chunk ← input.read (min 4096 (limit + 1 - acc.size)).toUSize
  if chunk.isEmpty then return acc.toList
  readBoundedLoop input limit (acc ++ chunk)

/-- Drain diagnostic stderr concurrently with stdout while retaining only a
bounded prefix. The child cannot block the projection read by filling stderr. -/
partial def readDiagnosticStderr (input : IO.FS.Handle) (limit : Nat)
    (acc : ByteArray := ByteArray.empty) : IO ByteArray := do
  let chunk ← input.read 4096
  if chunk.isEmpty then return acc
  let room := limit - acc.size
  let retained := acc ++ chunk.extract 0 (min room chunk.size)
  readDiagnosticStderr input limit retained

def readBoundedBytes (path : String) (limit : Nat) : IO (List UInt8) := do
  let input ← IO.FS.Handle.mk path .read
  readBoundedLoop input limit

/-- Bounded records, unlimited audit inventory. One verified source image owns
all response rows and the ledger header, regardless of retained payment count. -/
partial def readPaidAuditLine (input : IO.FS.Handle)
    (acc : ByteArray := ByteArray.empty) : IO (Option (List UInt8)) := do
  if acc.size > 4096 then throw (IO.userError "paid audit request exceeds byte bound")
  let byte ← input.read 1
  if byte.isEmpty then
    if acc.isEmpty then return none
    throw (IO.userError "paid audit request lacks newline")
  if byte[0]! == 10 then return some acc.toList
  readPaidAuditLine input (acc ++ byte)

partial def writePaidAuditRows (config : NativeHost.Config)
    (opened : NativeHost.Opened config) (input output : IO.FS.Handle)
    (count : Nat := 0) : IO Unit := do
  match ← readPaidAuditLine input with
  | none =>
      output.putStrLn (Lean.Json.mkObj [("type", "payClaimAuditComplete"),
        ("origins", toJson (toString count))]).compress
      output.flush
  | some bytes =>
      let some text := String.fromUTF8? bytes.toByteArray
        | throw (IO.userError "paid audit request is not UTF-8")
      let source ← IO.ofExcept (Minidregg.Host.Json.parse text)
      let result ← IO.ofExcept (Minidregg.Host.PayClaims.statusLoadedJson config opened source)
      output.putStrLn result.compress
      writePaidAuditRows config opened input output (count + 1)

def withFnReplyPollService {α : Type} (settings : Settings)
    (body : Option FnReplyPollService → IO α) : IO α := do
  let some source := settings.fnReplyPoll | return ← body none
  unless [source.originConfigPath, source.rPinPath, source.rClaimPath,
      source.rCarrierPath, source.qPinPath, source.scopePath,
      source.policyPath, source.controlPath].all
      (·.startsWith "/") do
    throw (IO.userError "A reply poll service paths must be operator-selected absolute paths")
  IO.FS.withTempDir fun directory => do
    let copyInput := fun (name sourcePath : String) (bound : Nat) => do
      let bytes ← readBoundedBytes sourcePath bound
      unless !bytes.isEmpty do
        throw (IO.userError s!"A reply poll service input {name} is empty")
      let destination := directory / name
      IO.FS.writeBinFile destination bytes.toByteArray
      pure destination.toString
    let originConfigPath ← copyInput "origin-config.json" source.originConfigPath 65536
    let rPinPath ← copyInput "r-pin.json" source.rPinPath 8192
    let (rExecutable, rPublicKey) ← snapshotFnPinFiles directory "r" rPinPath
    let rClaimPath ← copyInput "r-claim.json" source.rClaimPath 8192
    let rCarrierPath ← copyInput "r-carrier.eml" source.rCarrierPath
      FnEvidenceCodec.maxCarrierBytes
    let qPinPath ← copyInput "q-pin.json" source.qPinPath 8192
    let (qExecutable, qPublicKey) ← snapshotFnPinFiles directory "q" qPinPath
    let scopePath ← copyInput "scope.json" source.scopePath 8192
    let policyPath ← copyInput "policy.json" source.policyPath 8192
    body (some ⟨originConfigPath, rPinPath, rExecutable, rPublicKey,
      rClaimPath, rCarrierPath, qPinPath, qExecutable, qPublicKey,
      scopePath, policyPath, source.controlPath⟩)

/-- Physical directory identity catches a second pathname to the same Store,
including a bind mount that `realPath` alone cannot detect. This is a
launch-time check under the same OS custody assumption as the private helper
snapshots. -/
def directoryIdentity (path : System.FilePath) : IO String := do
  let linux ← IO.Process.output
    { cmd := "/usr/bin/stat", args := #["-c", "%d:%i", path.toString] }
  let output ← if linux.exitCode == 0 then pure linux else
    IO.Process.output
      { cmd := "/usr/bin/stat", args := #["-f", "%d:%i", path.toString] }
  unless output.exitCode == 0 && output.stdout.length ≤ 128 do
    throw (IO.userError "cannot identify Mini Store directory")
  let identity := output.stdout.trimAscii.toString
  match identity.splitOn ":" with
  | [device, inode] =>
      unless device.toNat?.isSome && inode.toNat?.isSome do
        throw (IO.userError "Mini Store directory identity is malformed")
      return identity
  | _ => throw (IO.userError "Mini Store directory identity is malformed")

def withFnReplyCatalogService {α : Type} (settings : Settings)
    (body : Option FnReplyCatalogService → IO α) : IO α := do
  let some source := settings.fnReplyCatalog | return ← body none
  unless settings.fnReplyPoll.isNone do
    throw (IO.userError "static and catalog A reply services are mutually exclusive")
  unless [source.originConfigPath, source.rPinPath, source.qPinPath,
      source.scopePath, source.policyPath, source.controlPath].all
      (·.startsWith "/") do
    throw (IO.userError "A reply catalog paths must be operator-selected absolute paths")
  IO.FS.withTempDir fun directory => do
    let copyInput := fun (name sourcePath : String) (bound : Nat) => do
      let bytes ← readBoundedBytes sourcePath bound
      unless !bytes.isEmpty do
        throw (IO.userError s!"A reply catalog input {name} is empty")
      let destination := directory / name
      IO.FS.writeBinFile destination bytes.toByteArray
      pure (destination.toString : String)
    let originConfigPath ← copyInput "origin-config.json" source.originConfigPath 65536
    let rPinPath ← copyInput "r-pin.json" source.rPinPath 8192
    let (rExecutable, rPublicKey) ← snapshotFnPinFiles directory "r" rPinPath
    let qPinPath ← copyInput "q-pin.json" source.qPinPath 8192
    let (qExecutable, qPublicKey) ← snapshotFnPinFiles directory "q" qPinPath
    let scopePath ← copyInput "scope.json" source.scopePath 8192
    let policyPath ← copyInput "policy.json" source.policyPath 8192
    let origin := (← loadSettings (System.FilePath.mk originConfigPath)).config
    unless origin.expectedSeed != settings.config.expectedSeed &&
        origin.storage.root.toString.startsWith "/" &&
        origin.storage.binary.toString.startsWith "/" &&
        origin.storage.root.toString != settings.storageRoot do
      throw (IO.userError
        "A prepared outbox needs a distinct live Mini origin deployment")
    let originRoot ← IO.FS.realPath origin.storage.root
    let replyRoot ← IO.FS.realPath settings.config.storage.root
    unless originRoot != replyRoot do
      throw (IO.userError "A prepared origin aliases the A reply Store")
    let originIdentity ← directoryIdentity originRoot
    let replyIdentity ← directoryIdentity replyRoot
    unless originIdentity != replyIdentity do
      throw (IO.userError "A prepared origin aliases the A reply Store")
    -- Use the resolved origin root for the entire session, so replacing its
    -- configured symlink cannot redirect later readback to another Store.
    let canonicalOrigin := { origin with storage :=
      { origin.storage with root := originRoot } }
    withPinnedSignature canonicalOrigin fun signedOrigin =>
      withPinnedStorageBinary signedOrigin fun pinnedOrigin =>
        body (some ⟨pinnedOrigin, rPinPath, rExecutable, rPublicKey,
          qPinPath, qExecutable, qPublicKey, scopePath,
          policyPath, source.controlPath⟩)

/-- Large source and carrier comparisons use the array primitive after the
bounded read; recursive list equality is unsuitable for the full V2 profile. -/
def sameBytes (left right : List UInt8) : Bool :=
  left.toByteArray == right.toByteArray

/-- The qualified fn owner prepends exactly these two hop-local fields to a
signed article that already supplied Date and Message-ID. Both the delivered
article and the retained outbox carrier must independently pass native hybrid
verification before a progress decision. The suffix must be the complete
retained carrier, byte for byte; arbitrary header rewriting is refused. -/
def fnAgentAtext (byte : UInt8) : Bool :=
  let n := byte.toNat
  (65 ≤ n && n ≤ 90) || (97 ≤ n && n ≤ 122) ||
    (48 ≤ n && n ≤ 57) ||
    [33, 35, 36, 37, 38, 39, 42, 43, 45, 47, 61, 63, 94, 95,
      96, 123, 124, 125, 126].contains n

def fnAgentDotAtom (agent : String) : Bool :=
  let bytes := agent.toUTF8.toList
  !bytes.isEmpty && bytes.length ≤ 128 &&
    (agent.splitOn ".").all (fun atom =>
      !atom.isEmpty && atom.toUTF8.toList.all fnAgentAtext)

def fnOwnRInjectionPrefix (injectedPrefix : List UInt8) : Bool :=
  if injectedPrefix.length > 512 ||
      !injectedPrefix.all (fun byte => byte.toNat < 128) then false
  else
    match String.fromUTF8? injectedPrefix.toByteArray with
    | none => false
    | some text =>
        match text.splitOn "Injection-Info: " with
        | [_, info] =>
            match info.splitOn "\r\n" with
            | [agent, ""] =>
                fnAgentDotAtom agent &&
                  text == "Path: " ++ agent ++
                    "!not-for-mail\r\nInjection-Info: " ++ agent ++ "\r\n"
            | _ => false
        | _ => false

def fnOwnRCarrierMatches (received authored : List UInt8) : Bool :=
  let prefixLength := received.length - authored.length
  let injectedPrefix := received.take prefixLength
  let suffix := received.drop prefixLength
  decide (suffix.toByteArray = authored.toByteArray) &&
    (injectedPrefix.isEmpty || fnOwnRInjectionPrefix injectedPrefix)

theorem fnOwnRCarrierMatches_exact_tail (received authored : List UInt8)
    (matched : fnOwnRCarrierMatches received authored = true) :
    (received.drop (received.length - authored.length)).toByteArray =
      authored.toByteArray := by
  simp only [fnOwnRCarrierMatches, Bool.and_eq_true, decide_eq_true_eq] at matched
  exact matched.1

def evidenceReceiptJson (receipt : NativeHostCodec.Receipt) : Lean.Json :=
  let n := fun value : Nat => toJson (toString value)
  Lean.Json.mkObj
    [("type", toJson "verified-mini-native-prefix-v1"),
     ("transactionId", n receipt.transactionId.value),
     ("eventId", n receipt.eventId.value),
     ("acceptedCount", n receipt.acceptedCount),
     ("worldRoot", n receipt.worldRoot.value)]

structure ConsumerReportSource where
  application : String
  operation : String
  history : String
  incarnation : String
  sourceIdentity : String
  fnVerdictRef : String
  subject : Nat
  target : Nat
  capability : Nat
  expectedTargetRoot : Nat
  deriving FromJson

structure ConsumerPolicySource where
  application : String
  subject : Nat
  target : Nat
  capability : Nat
  deriving FromJson

structure FnPortablePin where
  fnBinary : String
  mlPublicKey : String
  principal : String
  edPublicKey : String
  mlPublicKeyHex : String
  fnExecution : Option String := none
  mlPublicKeyExecution : Option String := none
  deriving FromJson

def FnPortablePin.executable (pin : FnPortablePin) : String :=
  pin.fnExecution.getD pin.fnBinary

def FnPortablePin.publicKeyFile (pin : FnPortablePin) : String :=
  pin.mlPublicKeyExecution.getD pin.mlPublicKey

def FnPortablePin.withExecution (pin : FnPortablePin)
    (executable publicKey : String) : FnPortablePin :=
  ⟨pin.fnBinary, pin.mlPublicKey, pin.principal, pin.edPublicKey,
    pin.mlPublicKeyHex, some executable, some publicKey⟩

structure FnReplyCreationSource where
  fromMailbox : String
  newsgroup : String
  messageIdDomain : String
  date : String
  deriving FromJson

def FnReplyCreationSource.context (source : FnReplyCreationSource) :
    FnReplyPublication.CreationContext :=
  ⟨source.fromMailbox, source.newsgroup, source.messageIdDomain, source.date⟩

structure FnReplySignerPin where
  principal : String
  edPublicKey : String
  mlPublicKeyHex : String
  creation : FnReplyCreationSource
  deriving FromJson

structure FnPortableClaim where
  sourceIdentity : String
  messageId : String
  groups : String
  deriving FromJson

def requireExactFields (name : String) (expected : List String)
    (json : Lean.Json) : Except String Unit := do
  let object ← json.getObj? |>.mapError (fun e => s!"{name}: {e}")
  let actual := object.foldl (init := []) (fun fields key _ => key :: fields)
  for key in expected do
    unless actual.contains key do throw s!"{name}: missing field {key}"
  for key in actual do
    unless expected.contains key do throw s!"{name}: unknown field {key}"

structure FnPortableVerified where
  principal : List UInt8
  sourceIdentity : List UInt8
  edPublicKey : List UInt8
  mlPublicKey : List UInt8
  source : List UInt8

/-- ACL2's bounded projection of one exact schema-1 poll pair. A projection of
caller-supplied files is structural evidence only; the authenticated local
consumer poll transport separately establishes historical Store provenance. -/
structure FnPollProjection where
  history : List UInt8
  incarnation : List UInt8
  consumer : List UInt8
  principal : List UInt8
  query : List UInt8
  queryVersion : Nat
  viewVersion : Nat
  registrationEpoch : Nat
  position : Nat
  sequence : Nat
  transactionId : Nat
  sourceIdentity : List UInt8
  messageId : List UInt8
  source : List UInt8
  received : List UInt8
  verdictPrincipal : List UInt8
  verdictEvent : List UInt8

structure FnPollScopePin where
  history : String
  incarnation : String
  consumer : String
  principal : String
  query : String
  queryVersion : Nat
  viewVersion : Nat
  registrationEpoch : Nat
  deriving FromJson

def decodeCanonicalHex (label value : String) : Except String (List UInt8) := do
  let bytes ← Minidregg.Host.Json.decodeHex label (.str value)
  unless Minidregg.Host.Json.encodeHex bytes == value do
    throw s!"{label} is not canonical lowercase hexadecimal"
  pure bytes

def exactDecimal (name value : String) : Except String Nat := do
  let some parsed := value.toNat? | throw s!"{name} is not a decimal number"
  unless toString parsed == value do throw s!"{name} is not canonical decimal"
  pure parsed

def parseFnPortableLine (output : String) : Except String FnPortableVerified := do
  unless output.length ≤ FnEvidenceCodec.maxPortableVerifyLineBytes do
    throw "fn portable verifier output exceeds bound"
  let line ← match output.splitOn "\n" with
    | [line, ""] => pure line
    | _ => throw "fn portable verifier output has unexpected framing"
  let (principalHex, idHex, edHex, mlHex, sourceHex) ← match line.splitOn " " with
    | [tag, principal, identifier, ed, ml, source] =>
        if tag == "fn-portable-v1" then pure (principal, identifier, ed, ml, source)
        else throw "fn portable verifier output has unexpected version"
    | _ => throw "fn portable verifier output has unexpected fields"
  let principal ← decodeCanonicalHex "principal" principalHex
  let sourceIdentity ← decodeCanonicalHex "source identity" idHex
  let edPublicKey ← decodeCanonicalHex "Ed25519 key" edHex
  let mlPublicKey ← decodeCanonicalHex "ML-DSA-65 key" mlHex
  let source ← decodeCanonicalHex "exact source" sourceHex
  unless principal.length == 32 && sourceIdentity.length == 48 &&
      edPublicKey.length == 32 && mlPublicKey.length == 1952 &&
      source.length ≤ FnEvidenceCodec.maxSourceBytes do
    throw "fn portable verifier output has invalid field width"
  pure ⟨principal, sourceIdentity, edPublicKey, mlPublicKey, source⟩

def parseFnHybridSignLine (output : String) : Except String (List UInt8 × List UInt8) := do
  unless output.length ≤ 7000 do throw "fn hybrid signer output exceeds bound"
  let (edHex, mlHex) ← match output.splitOn "\n" with
    | [edLine, mlLine, ""] =>
        match edLine.splitOn " ", mlLine.splitOn " " with
        | ["ed25519", ed], ["ml-dsa-65", ml] => pure (ed, ml)
        | _, _ => throw "fn hybrid signer output has unexpected fields"
    | _ => throw "fn hybrid signer output has unexpected framing"
  let ed ← decodeCanonicalHex "fn Ed25519 signature" edHex
  let ml ← decodeCanonicalHex "fn ML-DSA-65 signature" mlHex
  unless ed.length == 64 && ml.length == 3309 do
    throw "fn hybrid signer output has invalid signature width"
  pure (ed, ml)

def parseFnPollProjectLine (output : String) : Except String FnPollProjection := do
  unless output.length ≤ FnEvidenceCodec.maxPollProjectionLineBytes do
    throw "fn consumer projection output exceeds bound"
  let line ← match output.splitOn "\n" with
    | [line, ""] => pure line
    | _ => throw "fn consumer projection has unexpected framing"
  let fields ← match line.splitOn " " with
    | [tag, history, incarnation, consumer, principal, query,
       qver, view, epoch, position, sequence, txid, sourceId,
       msgid, source, received, verdictPrincipal, verdict] =>
        if tag == "fn-consumer-project-v1" then
          pure (history, incarnation, consumer, principal, query,
            qver, view, epoch, position, sequence, txid, sourceId,
            msgid, source, received, verdictPrincipal, verdict)
        else throw "fn consumer projection has unexpected version"
    | _ => throw "fn consumer projection has unexpected fields"
  let (history, incarnation, consumer, principal, query,
       qver, view, epoch, position, sequence, txid, sourceId,
       msgid, source, received, verdictPrincipal, verdict) := fields
  let history ← decodeCanonicalHex "fn history" history
  let incarnation ← decodeCanonicalHex "fn incarnation" incarnation
  let consumer ← decodeCanonicalHex "fn consumer" consumer
  let principal ← decodeCanonicalHex "fn local principal" principal
  let query ← decodeCanonicalHex "fn query" query
  let sourceIdentity ← decodeCanonicalHex "fn source identity" sourceId
  let messageId ← decodeCanonicalHex "fn Message-ID" msgid
  let source ← decodeCanonicalHex "fn authored source" source
  let received ← decodeCanonicalHex "fn received article" received
  let verdictPrincipal ← decodeCanonicalHex "fn verdict principal" verdictPrincipal
  let verdictEvent ← decodeCanonicalHex "fn historical verdict" verdict
  let queryVersion ← exactDecimal "fn query version" qver
  let viewVersion ← exactDecimal "fn view version" view
  let registrationEpoch ← exactDecimal "fn registration epoch" epoch
  let position ← exactDecimal "fn Store position" position
  let sequence ← exactDecimal "fn Store sequence" sequence
  let transactionId ← exactDecimal "fn Store transaction" txid
  unless [history, incarnation, consumer, principal, query].all
      (fun value => !value.isEmpty && value.length ≤ 64) &&
      sourceIdentity.length == 48 && !messageId.isEmpty &&
      messageId.length ≤ 256 && !source.isEmpty &&
      source.length ≤ FnEvidenceCodec.maxSourceBytes &&
      !received.isEmpty && received.length ≤ FnEvidenceCodec.maxCarrierBytes &&
      verdictPrincipal.length == 32 &&
      !verdictEvent.isEmpty &&
      verdictEvent.length ≤ FnEvidenceCodec.maxHistoricalVerdictEventBytes &&
      [queryVersion, viewVersion, registrationEpoch, position,
       sequence, transactionId].all (· ≤ 4294967295) &&
      registrationEpoch > 0 && position == sequence + 1 do
    throw "fn consumer projection has invalid field width or sequence binding"
  pure ⟨history, incarnation, consumer, principal, query,
    queryVersion, viewVersion, registrationEpoch, position, sequence,
    transactionId, sourceIdentity, messageId, source, received,
    verdictPrincipal, verdictEvent⟩

def FnPollScopePin.check (pin : FnPollScopePin)
    (projection : FnPollProjection) : Except String Unit := do
  let history ← decodeCanonicalHex "pinned fn history" pin.history
  let incarnation ← decodeCanonicalHex "pinned fn incarnation" pin.incarnation
  let consumer ← decodeCanonicalHex "pinned fn consumer" pin.consumer
  let principal ← decodeCanonicalHex "pinned fn local principal" pin.principal
  let query ← decodeCanonicalHex "pinned fn query" pin.query
  unless projection.history == history &&
      projection.incarnation == incarnation &&
      projection.consumer == consumer && projection.principal == principal &&
      projection.query == query &&
      projection.queryVersion == pin.queryVersion &&
      projection.viewVersion == pin.viewVersion &&
      projection.registrationEpoch == pin.registrationEpoch do
    throw "fn poll cursor differs from independently pinned consumer scope"

def FnPollScopePin.progressScope (pin : FnPollScopePin) :
    Except String FnConsumerProgress.Scope := do
  return ⟨← decodeCanonicalHex "pinned fn history" pin.history,
    ← decodeCanonicalHex "pinned fn incarnation" pin.incarnation,
    ← decodeCanonicalHex "pinned fn consumer" pin.consumer,
    ← decodeCanonicalHex "pinned fn principal" pin.principal,
    ← decodeCanonicalHex "pinned fn query" pin.query,
    pin.queryVersion, pin.viewVersion, pin.registrationEpoch⟩

def exactNamedDecimal (name field : String) : Except String Nat := do
  let [label, value] := field.splitOn "="
    | throw s!"fn {name} field has unexpected framing"
  unless label == name do throw s!"fn {name} field has unexpected label"
  exactDecimal name value

def exactNamedHex (name field : String) : Except String (List UInt8) := do
  let [label, value] := field.splitOn "="
    | throw s!"fn {name} field has unexpected framing"
  unless label == name do throw s!"fn {name} field has unexpected label"
  decodeCanonicalHex name value

structure FnConsumerStatus where
  committedAck : Nat
  frontier : Nat
  distance : Nat

def parseFnConsumerStatus (output : String) : Except String FnConsumerStatus := do
  let [line, ""] := output.splitOn "\n"
    | throw "fn consumer status has unexpected framing"
  let ["consumer", "status", "accepted", ack, frontier, distance] :=
      line.splitOn " "
    | throw "fn consumer status has unexpected fields"
  let committedAck ← exactNamedDecimal "committed-ack" ack
  let frontier ← exactNamedDecimal "committed-journal-frontier" frontier
  let distance ← exactNamedDecimal "journal-event-distance" distance
  unless committedAck ≤ frontier && distance == frontier - committedAck &&
      frontier ≤ 4294967295 do
    throw "fn consumer status has invalid positions"
  return ⟨committedAck, frontier, distance⟩

def parseFnConsumerInspect (output : String) :
    Except String (FnConsumerProgress.Scope × Nat) := do
  let [line, ""] := output.splitOn "\n"
    | throw "fn consumer inspect has unexpected framing"
  let ["fn-consumer-inspect-v1", history, incarnation, consumer, principal,
       query, qver, view, epoch, position,
       "currentness=unverified", "acceptance=unverified",
       "processing=unverified"] := line.splitOn " "
    | throw "fn consumer inspect has unexpected fields"
  let scope : FnConsumerProgress.Scope :=
    ⟨← exactNamedHex "history" history,
     ← exactNamedHex "incarnation" incarnation,
     ← exactNamedHex "consumer" consumer,
     ← exactNamedHex "principal" principal,
     ← exactNamedHex "query" query,
     ← exactNamedDecimal "query-version" qver,
     ← exactNamedDecimal "view-version" view,
     ← exactNamedDecimal "registration-epoch" epoch⟩
  let position ← exactNamedDecimal "position" position
  unless scope.valid && position ≤ 4294967295 do
    throw "fn consumer inspect has invalid scope or position"
  return (scope, position)

def projectFnPoll (fnBinary : String) (pin : FnPollScopePin)
    (cursorPath reportPath : String) : IO (List UInt8 × List UInt8 × FnPollProjection) := do
  let cursor ← readBoundedBytes cursorPath 346
  let report ← readBoundedBytes reportPath FnEvidenceCodec.maxStorePollEventBytes
  unless !cursor.isEmpty && !report.isEmpty do
    throw (IO.userError "fn poll has no schema-1 report and cursor")
  -- A malformed projection never authorizes anything. One second read-only
  -- projection of the unchanged files may recover a one-off transport fault;
  -- both failures retain bounded byte-count and hash diagnostics, not content.
  let mut selected : Option FnPollProjection := none
  let mut framingDiagnostic := "none"
  for _ in [:2] do
    if selected.isNone then do
      let child ← IO.Process.spawn
        { cmd := fnBinary, args := #["--fn", "consumer-project", cursorPath,
          reportPath], stdin := .null, stdout := .piped, stderr := .piped }
      let stderrTask ← IO.asTask (readDiagnosticStderr child.stderr 2048)
      let lineBytes ← try readBoundedLoop child.stdout FnEvidenceCodec.maxPollProjectionLineBytes
        catch error =>
          child.kill
          discard <| child.wait
          throw error
      let exitCode ← child.wait
      let stderrBytes ← match stderrTask.get with
        | .ok bytes => pure bytes
        | .error error => throw error
      let digest := fun (label : String) (bytes : List UInt8) =>
        (Sp800185Cshake256.hash label.toUTF8.toList bytes).digest.value
      let diagnostic := s!"exit={exitCode}, stdoutBytes={lineBytes.length}, stdoutLF={(lineBytes.filter (· == 10)).length}, stdoutDigest={digest "DREGG.FN.PROJECTION-STDOUT/v1" lineBytes}, stderrPrefixBytes={stderrBytes.size}, stderrPrefixDigest={digest "DREGG.FN.PROJECTION-STDERR/v1" stderrBytes.toList}"
      unless exitCode == 0 do
        throw (IO.userError s!"fn native consumer projection refused ({diagnostic})")
      unless cursor == (← readBoundedBytes cursorPath 346) &&
          sameBytes report (← readBoundedBytes reportPath FnEvidenceCodec.maxStorePollEventBytes) do
        throw (IO.userError "fn poll files changed during native projection")
      unless lineBytes.all (fun byte => byte.toNat < 128) do
        throw (IO.userError "fn consumer projection is not ASCII")
      match parseFnPollProjectLine (String.fromUTF8! lineBytes.toByteArray) with
      | .ok projection => selected := some projection
      | .error detail =>
          unless detail == "fn consumer projection has unexpected framing" do
            throw (IO.userError s!"{detail} ({diagnostic})")
          IO.eprintln s!"minidregg-host: fn projection framing retry ({diagnostic})"
          framingDiagnostic := diagnostic
  let some projection := selected
    | throw (IO.userError s!"fn consumer projection framing refused after retry ({framingDiagnostic})")
  IO.ofExcept (pin.check projection)
  pure (cursor, report, projection)

def fnConsumerAscii (scope : FnPollScopePin) : IO String := do
  let consumer ← IO.ofExcept (decodeCanonicalHex "pinned fn consumer" scope.consumer)
  unless !consumer.isEmpty && consumer.length ≤ 64 &&
      consumer.all (fun b => 33 ≤ b.toNat && b.toNat ≤ 126) do
    throw (IO.userError "pinned fn consumer is outside local CLI ASCII profile")
  pure (String.fromUTF8! consumer.toByteArray)

def queryFnConsumerStatus (fnBinary : String) (scope : FnPollScopePin)
    (controlPath : String) : IO FnConsumerStatus := do
  let consumer ← fnConsumerAscii scope
  let child ← IO.Process.spawn
    { cmd := fnBinary, args := #["--fn", "consumer", "status", controlPath, consumer],
      stdin := .null, stdout := .piped, stderr := .null }
  let output ← try readBoundedLoop child.stdout 256
    catch error =>
      child.kill
      discard <| child.wait
      throw error
  let exitCode ← child.wait
  unless exitCode == 0 && output.all (fun byte => byte.toNat < 128) do
    throw (IO.userError "fn local consumer status refused or was uncertain")
  IO.ofExcept (parseFnConsumerStatus (String.fromUTF8! output.toByteArray))

def inspectFnConsumerCursor (fnBinary : String) (cursorPath : String) :
    IO (FnConsumerProgress.Scope × Nat) := do
  let cursor ← readBoundedBytes cursorPath 346
  let mut selected : Option (FnConsumerProgress.Scope × Nat) := none
  let mut framingDiagnostic := "none"
  for _ in [:2] do
    if selected.isNone then do
      let child ← IO.Process.spawn
        { cmd := fnBinary, args := #["--fn", "consumer-inspect", cursorPath],
          stdin := .null, stdout := .piped, stderr := .piped }
      let stderrTask ← IO.asTask (readDiagnosticStderr child.stderr 2048)
      let output ← try readBoundedLoop child.stdout 1024
        catch error =>
          child.kill
          discard <| child.wait
          throw error
      let exitCode ← child.wait
      let stderrBytes ← match stderrTask.get with
        | .ok bytes => pure bytes
        | .error error => throw error
      let digest := fun (label : String) (bytes : List UInt8) =>
        (Sp800185Cshake256.hash label.toUTF8.toList bytes).digest.value
      let diagnostic := s!"exit={exitCode}, stdoutBytes={output.length}, stdoutLF={(output.filter (· == 10)).length}, stdoutDigest={digest "DREGG.FN.INSPECT-STDOUT/v1" output}, stderrPrefixBytes={stderrBytes.size}, stderrPrefixDigest={digest "DREGG.FN.INSPECT-STDERR/v1" stderrBytes.toList}"
      unless cursor == (← readBoundedBytes cursorPath 346) do
        throw (IO.userError "fn consumer cursor changed during inspect")
      unless exitCode == 0 && output.all (fun byte => byte.toNat < 128) do
        throw (IO.userError s!"fn consumer cursor inspect refused ({diagnostic})")
      match parseFnConsumerInspect (String.fromUTF8! output.toByteArray) with
      | .ok value => selected := some value
      | .error detail =>
          unless detail == "fn consumer inspect has unexpected framing" do
            throw (IO.userError s!"{detail} ({diagnostic})")
          IO.eprintln s!"minidregg-host: fn cursor inspect framing retry ({diagnostic})"
          framingDiagnostic := diagnostic
  let some value := selected
    | throw (IO.userError s!"fn consumer inspect framing refused after retry ({framingDiagnostic})")
  return value

/-- The local owner supplies a fresh committed-position cursor. Inspecting a
caller file would establish only syntax; this path binds the inspected full
scope to a live authenticated owner response and fences it with status. -/
def queryFnConsumerPosition (fnBinary : String) (scope : FnPollScopePin)
    (controlPath : String) : IO (Nat × FnConsumerStatus) := do
  unless controlPath.startsWith "/" do
    throw (IO.userError "fn consumer position control must be absolute")
  IO.FS.withTempDir fun directory => do
    let path := (directory / "current-position.fncu").toString
    let consumer ← fnConsumerAscii scope
    let child ← IO.Process.spawn
      { cmd := fnBinary, args := #["--fn", "consumer", "position",
        controlPath, consumer, path],
        stdin := .null, stdout := .piped, stderr := .null }
    let output ← try readBoundedLoop child.stdout 128
      catch error =>
        child.kill
        discard <| child.wait
        throw error
    let exitCode ← child.wait
    unless exitCode == 0 && output == "consumer accepted\n".toUTF8.toList do
      throw (IO.userError "fn current consumer position refused or uncertain")
    let cursor ← readBoundedBytes path 346
    unless !cursor.isEmpty do
      throw (IO.userError "fn current position returned no cursor")
    let (inspectedScope, position) ← inspectFnConsumerCursor fnBinary path
    let selectedScope ← IO.ofExcept scope.progressScope
    unless inspectedScope == selectedScope &&
        cursor == (← readBoundedBytes path 346) do
      throw (IO.userError "fn current position scope or cursor changed")
    let status ← queryFnConsumerStatus fnBinary scope controlPath
    unless status.committedAck ≥ position do
      throw (IO.userError "fn current position exceeds fenced durable ACK")
    return (position, status)

/-- One authenticated local poll, before choosing the article or empty-page
branch. The cursor is written last by fn; requiring both files and the exact
accepted line excludes partial or uncertain output from progress admission. -/
def invokeFnConsumerPollRaw (fnBinary : String) (scope : FnPollScopePin)
    (controlPath cursorPath reportPath : String) : IO (List UInt8 × List UInt8) := do
  unless [controlPath, cursorPath, reportPath].all (·.startsWith "/") &&
      cursorPath != reportPath do
    throw (IO.userError "fn poll control and output paths must be distinct absolute paths")
  for path in [cursorPath, reportPath] do
    if ← (System.FilePath.mk path).pathExists then
      throw (IO.userError "fn poll output path already exists")
  let consumer ← fnConsumerAscii scope
  let child ← IO.Process.spawn
    { cmd := fnBinary, args := #["--fn", "consumer", "poll", controlPath,
      consumer, cursorPath, reportPath],
      stdin := .null, stdout := .piped, stderr := .null }
  let output ← try readBoundedLoop child.stdout 512
    catch error =>
      child.kill
      discard <| child.wait
      throw error
  let exitCode ← child.wait
  unless exitCode == 0 && output == "consumer accepted\n".toUTF8.toList do
    throw (IO.userError "authenticated fn local consumer poll refused or was uncertain")
  let cursor ← readBoundedBytes cursorPath 346
  let event ← readBoundedBytes reportPath FnEvidenceCodec.maxStorePollEventBytes
  unless !cursor.isEmpty do
    throw (IO.userError "accepted fn poll did not produce a cursor")
  return (cursor, event)

/-- `none` is genuine idle at the current frontier; `some` is an observed
bounded empty page that can be recorded and ACKed after Mini admission. -/
def classifyFnEmptyPoll (fnBinary : String) (scope : FnPollScopePin)
    (controlPath cursorPath reportPath : String) (cursor : List UInt8)
    (before : FnConsumerStatus) : IO (Option (Nat × Nat)) := do
  let (inspectedScope, position) ← inspectFnConsumerCursor fnBinary cursorPath
  let selectedScope ← IO.ofExcept scope.progressScope
  let after ← queryFnConsumerStatus fnBinary scope controlPath
  unless inspectedScope == selectedScope &&
      before.committedAck == after.committedAck &&
      cursor == (← readBoundedBytes cursorPath 346) &&
      (← readBoundedBytes reportPath FnEvidenceCodec.maxStorePollEventBytes).isEmpty do
    throw (IO.userError "empty fn poll scope, ACK, or output changed")
  if position == before.committedAck && position == after.frontier then
    return none
  unless before.committedAck < position &&
      position ≤ before.committedAck + FnConsumerProgress.maxPollScan &&
      position ≤ after.frontier do
    throw (IO.userError "empty fn poll continuation is outside observed scan")
  return some (before.committedAck, position)

def idleFnPollResponse (operation : UInt8) (responseType : String)
    (position : Nat) : UInt8 × List UInt8 :=
  (operation, (Lean.Json.mkObj
    [("type", toJson responseType),
     ("status", toJson "idle"),
     ("decision", Lean.Json.mkObj
       [("type", toJson "fn-empty-page-idle-v1"),
        ("position", toJson (toString position))]),
     ("intentHex", toJson "")]).compress.toUTF8.toList)

/-- Invoke the actual same-UID fn local consumer route under an operator
selected absolute control socket and independently pinned cursor scope. The
two output files must be new; no ack is sent on any result. -/
def invokeFnConsumerPoll (fnBinary : String) (scope : FnPollScopePin)
    (controlPath cursorPath reportPath carrierPath : String) :
    IO (List UInt8 × List UInt8 × List UInt8) := do
  unless [controlPath, cursorPath, reportPath, carrierPath].all
      (fun path => path.startsWith "/") do
    throw (IO.userError "fn local control and output paths must be absolute")
  unless cursorPath != reportPath && cursorPath != carrierPath &&
      reportPath != carrierPath do
    throw (IO.userError "fn poll outputs must have distinct paths")
  for path in [cursorPath, reportPath, carrierPath] do
    if ← (System.FilePath.mk path).pathExists then
      throw (IO.userError "fn poll output path already exists")
  let consumer ← IO.ofExcept (decodeCanonicalHex "pinned fn consumer" scope.consumer)
  unless !consumer.isEmpty && consumer.length ≤ 64 &&
      consumer.all (fun b => 33 ≤ b.toNat && b.toNat ≤ 126) do
    throw (IO.userError "pinned fn consumer is outside local CLI ASCII profile")
  let child ← IO.Process.spawn
    { cmd := fnBinary, args := #["--fn", "consumer", "poll", controlPath,
      String.fromUTF8! consumer.toByteArray, cursorPath, reportPath],
      stdin := .null, stdout := .piped, stderr := .null }
  let output ← try readBoundedLoop child.stdout 512
    catch error =>
      child.kill
      discard <| child.wait
      throw error
  let exitCode ← child.wait
  unless exitCode == 0 && output.all (fun b => b.toNat < 128) do
    throw (IO.userError "authenticated fn local consumer poll refused or was uncertain")
  let (cursor, event, projected) ←
    projectFnPoll fnBinary scope cursorPath reportPath
  IO.FS.writeBinFile carrierPath projected.received.toByteArray
  pure (cursor, event, projected.received)

def verifyFnCarrierUnclaimed (pin : FnPortablePin)
    (carrierPath : String) : IO (List UInt8 × FnPortableVerified) := do
  let carrier ← readBoundedBytes carrierPath FnEvidenceCodec.maxCarrierBytes
  unless !carrier.isEmpty do throw (IO.userError "empty fn carrier")
  let expectedPrincipal ← IO.ofExcept (decodeCanonicalHex "pinned principal" pin.principal)
  let expectedEd ← IO.ofExcept (decodeCanonicalHex "pinned Ed25519 key" pin.edPublicKey)
  let expectedMl ← IO.ofExcept (decodeCanonicalHex "pinned ML-DSA-65 key" pin.mlPublicKeyHex)
  unless expectedPrincipal.length == 32 && expectedEd.length == 32 &&
      expectedMl.length == 1952 do
    throw (IO.userError "fn pin has invalid field width")
  let child ← IO.Process.spawn
    { cmd := pin.executable, args := #["--fn", "hybrid-verify-source", carrierPath,
      pin.publicKeyFile], stdin := .null, stdout := .piped, stderr := .null }
  let lineBytes ← try readBoundedLoop child.stdout FnEvidenceCodec.maxPortableVerifyLineBytes
    catch error =>
      child.kill
      discard <| child.wait
      throw error
  let exitCode ← child.wait
  unless exitCode == 0 do
    throw (IO.userError "fn native portable carrier verifier refused")
  unless sameBytes carrier (← readBoundedBytes carrierPath FnEvidenceCodec.maxCarrierBytes) do
    throw (IO.userError "fn carrier changed during native verification")
  unless lineBytes.all (fun byte => byte.toNat < 128) do
    throw (IO.userError "fn portable verifier output is not ASCII")
  let verified ← IO.ofExcept (parseFnPortableLine
    (String.fromUTF8! lineBytes.toByteArray))
  unless verified.principal == expectedPrincipal &&
      verified.edPublicKey == expectedEd &&
      verified.mlPublicKey == expectedMl &&
      verified.sourceIdentity.length == 48 do
    throw (IO.userError "fn portable identity differs from independent pin")
  pure (carrier, verified)

def verifyFnCarrier (pin : FnPortablePin) (claim : FnPortableClaim)
    (carrierPath : String) : IO (List UInt8 × FnPortableVerified) := do
  let expectedId ← IO.ofExcept (decodeCanonicalHex "claimed source identity" claim.sourceIdentity)
  unless expectedId.length == 48 do
    throw (IO.userError "claimed source identity has invalid width")
  let (carrier, verified) ← verifyFnCarrierUnclaimed pin carrierPath
  unless verified.sourceIdentity == expectedId do
    throw (IO.userError "fn portable identity differs from independent claim")
  pure (carrier, verified)

def verifyFnPortable (pin : FnPortablePin) (claim : FnPortableClaim)
    (carrierPath : String) : IO (List UInt8 × FnPortableVerified × FnPortableSource.Extracted) := do
  let (carrier, verified) ← verifyFnCarrier pin claim carrierPath
  let extracted ← IO.ofExcept (FnPortableSource.extract verified.source)
  unless extracted.messageId == claim.messageId && extracted.groups == claim.groups do
    throw (IO.userError "fn source metadata differs from claimed exact report")
  pure (carrier, verified, extracted)

/-- A prepared R must carry the exact package that this independently pinned
origin Mini currently exports for the same locally accepted signed call. The
carrier is native-verified first, and neither its receipt nor a client claim is
allowed to select a different local transaction. This establishes preparation
under local custody; fn posting remains a separate external event. -/
def verifyRLocalOrigin (origin : NativeHost.Config) (pin : FnPortablePin)
    (carrierPath : String) : IO
    (List UInt8 × FnPortableVerified × FnPortableSource.Extracted ×
      FnEvidenceCodec.Package × NativeHostCodec.Receipt) := do
  let (carrier, verified) ← verifyFnCarrierUnclaimed pin carrierPath
  let extracted ← IO.ofExcept (FnPortableSource.extract verified.source)
  let package ← IO.ofExcept (FnEvidenceCodec.decodeChecked extracted.package)
  let receipt ← IO.ofExcept (← FnEvidence.verify origin extracted.package)
  unless package.originalReceipt == receipt do
    throw (IO.userError "R carried receipt differs from re-admitted local origin")
  let exported ← IO.ofExcept (← FnEvidence.exportPackage origin package.signedCall)
  unless sameBytes exported extracted.package do
    throw (IO.userError "R carried package differs from exact local accepted origin")
  pure (carrier, verified, extracted, package, receipt)

/-- An acknowledgement is for the exact carrier and signed source retained
inside the accepted Mini operation, even after its mutation grant is revoked.
The current fn projection must match that source byte for byte. -/
def verifyAckSource (pin : FnPortablePin) (projection : FnPollProjection)
    (retainedCarrier retainedSource : List UInt8) : IO FnPortableVerified := do
  unless sameBytes projection.received retainedCarrier do
    throw (IO.userError "fn ack carrier differs from accepted Mini inbox")
  let extracted ← IO.ofExcept (FnPortableSource.extract retainedSource)
  let claim : FnPortableClaim :=
    { sourceIdentity := Minidregg.Host.Json.encodeHex projection.sourceIdentity,
      messageId := extracted.messageId,
      groups := extracted.groups }
  IO.FS.withTempDir fun directory => do
    let path := directory / "retained-carrier.eml"
    IO.FS.writeBinFile path retainedCarrier.toByteArray
    let (_, verified, _) ← verifyFnPortable pin claim path.toString
    unless sameBytes verified.source retainedSource &&
        sameBytes projection.source retainedSource &&
        verified.sourceIdentity == projection.sourceIdentity do
      throw (IO.userError "fn ack source differs from accepted Mini inbox")
    return verified

/-- A reply ACK verifies the Q reply-source profile. It cannot use the B
native-prefix parser: the accepted A inbox retains a seven-header reply source
with a different exact Message-ID construction. -/
def verifyReplyAckSource (pin : FnPortablePin) (projection : FnPollProjection)
    (retainedCarrier retainedSource : List UInt8) : IO FnPortableVerified := do
  unless sameBytes projection.received retainedCarrier do
    throw (IO.userError "A reply ack carrier differs from accepted Mini inbox")
  let extracted ← IO.ofExcept (FnReplySource.extract retainedSource)
  let claim : FnPortableClaim :=
    { sourceIdentity := Minidregg.Host.Json.encodeHex projection.sourceIdentity,
      messageId := extracted.messageId,
      groups := extracted.creation.newsgroup }
  IO.FS.withTempDir fun directory => do
    let path := directory / "retained-q-carrier.eml"
    IO.FS.writeBinFile path retainedCarrier.toByteArray
    let (_, verified) ← verifyFnCarrier pin claim path.toString
    unless sameBytes verified.source retainedSource &&
        sameBytes projection.source retainedSource &&
        verified.sourceIdentity == projection.sourceIdentity &&
        projection.messageId == extracted.messageId.toUTF8.toList do
      throw (IO.userError "A reply ack signed source differs from accepted Mini inbox")
    return verified

/-- Join ACL2's exact fn-e/fncu projection to the independent native hybrid
verifier. The caller must separately establish that these files were returned
by an authenticated consumer poll; file possession alone is not Store proof. -/
def verifyFnPollFiles (pin : FnPortablePin) (scope : FnPollScopePin)
    (claim : FnPortableClaim) (cursorPath reportPath carrierPath : String) :
    IO (List UInt8 × List UInt8 × FnPollProjection × List UInt8 ×
      FnPortableVerified × FnPortableSource.Extracted) := do
  let (cursor, report, projection) ←
    projectFnPoll pin.executable scope cursorPath reportPath
  let (carrier, verified, extracted) ← verifyFnPortable pin claim carrierPath
  unless sameBytes projection.received carrier &&
      sameBytes projection.source verified.source &&
      projection.sourceIdentity == verified.sourceIdentity &&
      projection.verdictPrincipal == verified.principal &&
      projection.messageId == extracted.messageId.toUTF8.toList do
    throw (IO.userError "fn Store projection differs from verified exact carrier")
  pure (cursor, report, projection, carrier, verified, extracted)

def ConsumerPolicySource.policy (source : ConsumerPolicySource) :
    FnConsumerOperation.Policy :=
  ⟨source.application.toUTF8.toList, ⟨source.subject⟩, source.target,
    ⟨source.capability⟩⟩

def ConsumerReportSource.report (source : ConsumerReportSource) (package : List UInt8) :
    FnConsumerOperation.Report :=
  ⟨source.application.toUTF8.toList, source.operation.toUTF8.toList,
    ⟨source.history.toUTF8.toList, source.incarnation.toUTF8.toList,
      source.sourceIdentity.toUTF8.toList, source.fnVerdictRef.toUTF8.toList⟩,
    package, ⟨source.subject⟩, source.target, ⟨source.capability⟩,
    ⟨source.expectedTargetRoot⟩, none, none⟩

/-- Portable authorship has no fn Store history, incarnation or T10 verdict.
The reserved literal fields make that absence explicit in the v1 P1 binding
codec. The operation selects the pinned Mini origin and re-admitted origin
transaction, never the fn source identity. -/
def portableConsumerReport (policy : FnConsumerOperation.Policy)
    (targetRoot : Minidregg.Theory.TypedAuthorization.Digest)
    (verified : FnPortableVerified)
    (carrier package : List UInt8) (origin : FnEvidenceCodec.Package) :
    FnConsumerOperation.Report :=
  ⟨policy.application, FnConsumerOperation.originOperation origin,
    ⟨"fn-store-unestablished".toUTF8.toList,
      "fn-store-unestablished".toUTF8.toList,
      verified.sourceIdentity,
      "fn-portable-authorship-v1".toUTF8.toList⟩,
    package, policy.subject, policy.target, policy.capability,
    targetRoot,
    some ⟨carrier, verified.sourceIdentity, verified.principal,
      verified.edPublicKey, verified.mlPublicKey⟩, none⟩

/-- Build Mini's report solely from the already joined ACL2 projection and
portable verifier. Caller-supplied scope or verdict flags never become fields
of the signed Mini command. -/
def pollConsumerReport (policy : FnConsumerOperation.Policy)
    (targetRoot : Minidregg.Theory.TypedAuthorization.Digest)
    (verified : FnPortableVerified) (carrier package : List UInt8)
    (origin : FnEvidenceCodec.Package) (cursor event : List UInt8)
    (projection : FnPollProjection) (controlBinding : Option (String × String)) :
    FnConsumerOperation.Report :=
  let base := portableConsumerReport policy targetRoot
    verified carrier package origin
  let storeInbox : FnConsumerOperation.StorePollInbox :=
    ⟨cursor, event, controlBinding.isSome, projection.sourceIdentity,
      projection.sequence, projection.transactionId, projection.messageId,
      projection.verdictPrincipal, projection.verdictEvent,
      match controlBinding with
      | none => []
      | some (fnBinary, controlPath) =>
          FnConsumerOperation.pollControlBinding fnBinary controlPath⟩
  { base with
    provenance := ⟨projection.history, projection.incarnation,
      projection.sourceIdentity,
      FnConsumerOperation.storePollVerdictRef storeInbox⟩,
    storePoll := some storeInbox }

def consumerDecisionJson (decision : FnConsumerOperation.Decision) : Lean.Json :=
  match decision with
  | .fresh _ reply => .mkObj
      [("type", "proposed-fresh"),
       ("reply", toJson (Minidregg.Host.Json.encodeHex
         (FnConsumerOperation.replyCodec.encode reply)))]
  | .repeated reply => .mkObj
      [("type", "historical-repeat"),
       ("reply", toJson (Minidregg.Host.Json.encodeHex
         (FnConsumerOperation.replyCodec.encode reply)))]
  | .carrierVariation _ reply => .mkObj
      [("type", "proposed-carrier-variation-evidence"),
       ("reply", toJson (Minidregg.Host.Json.encodeHex
         (FnConsumerOperation.replyCodec.encode reply)))]
  | .carrierVariationRecorded reply => .mkObj
      [("type", "historical-carrier-variation-evidence"),
       ("reply", toJson (Minidregg.Host.Json.encodeHex
         (FnConsumerOperation.replyCodec.encode reply)))]
  | .conflict _ => .mkObj [("type", "proposed-conflict-evidence")]
  | .conflictRecorded => .mkObj [("type", "historical-conflict-evidence")]
  | .refused detail => .mkObj [("type", "refused"), ("detail", toJson detail)]

def requireGateway (config : NativeHost.Config) : IO NativeHost.FnGatewayPin := do
  let some pin := config.fnGateway
    | throw (IO.userError "fn gateway is not pinned in operator config")
  return pin

def gatewayContentTargetRoot (config : NativeHost.Config)
    (opened : NativeHost.Opened config) (policy : FnConsumerOperation.Policy) :
    IO Minidregg.Theory.TypedAuthorization.Digest :=
  IO.ofExcept <| (do
    let probe : DeclaredResourceController.Target :=
      ⟨.object, policy.target, policy.capability, 1, ⟨0⟩,
        .content ⟨[]⟩, none, none, none⟩
    let .present cell := opened.directory.directory.slots policy.target
      | throw "fn gateway content target is absent"
    let some pre := DeclaredResourceController.selectTarget
      config.deployment probe cell
      | throw "fn gateway target is not a valid content resource"
    pure pre.root : Except String Minidregg.Theory.TypedAuthorization.Digest)

/-- Export only from a source-owned, re-admitted accepted event. The typed
inbox keeps exact carrier octets; this asserts Mini retention, not an fn Store
receipt or current fn authorship policy. -/
def exportConsumerInbox (config : NativeHost.Config) (transactionId : Nat) :
    IO (Except String (FnConsumerOperation.PortableInbox × String × Nat)) := do
  let some gateway := config.fnGateway
    | return .error "fn gateway is not pinned in operator config"
  let opened ← match ← NativeHost.openExisting config with
    | .ok opened => pure opened
    | .error detail => return .error detail
  let some record := opened.durable.image.accepted.find?
      (fun entry => entry.transactionId.value == transactionId)
    | return .error "exact Mini consumer transaction is absent"
  match FnConsumerOperation.originalBindingWithInbox gateway config.deployment.domain
      config.profile.semantics record with
  | some (binding, some inbox, _) =>
      return .ok (inbox, "operation",
        (FnConsumerOperation.operationInboxAtom config.deployment.domain
          config.profile.semantics binding.application binding.operation).digest.value)
  | _ =>
      match FnConsumerOperation.originalConflictWithInbox gateway config.deployment.domain
          config.profile.semantics record with
      | some (conflict, some inbox, store) =>
          let report : FnConsumerOperation.Report :=
            { application := conflict.application, operation := conflict.operation,
              provenance := conflict.provenance, package := conflict.package,
              subject := ⟨0⟩, target := 0, capability := ⟨0⟩,
              expectedTargetRoot := ⟨0⟩,
              portableInbox := some inbox, storePoll := store }
          return .ok (inbox, "conflict",
            (FnConsumerOperation.conflictInboxAtom config.deployment.domain
              config.profile.semantics report).digest.value)
      | _ => return .error "transaction has no canonical portable inbox"

/-- Read the exact fn poll pair from Mini's original signed accepted command,
after the ordinary native open has re-admitted its durable history. -/
def exportConsumerPoll (config : NativeHost.Config) (transactionId : Nat) :
    IO (Except String (FnConsumerOperation.StorePollInbox × String × Nat)) := do
  let some gateway := config.fnGateway
    | return .error "fn gateway is not pinned in operator config"
  let opened ← match ← NativeHost.openExisting config with
    | .ok opened => pure opened
    | .error detail => return .error detail
  let some record := opened.durable.image.accepted.find?
      (fun entry => entry.transactionId.value == transactionId)
    | return .error "exact Mini consumer transaction is absent"
  match FnConsumerOperation.originalBindingWithInbox gateway config.deployment.domain
      config.profile.semantics record with
  | some (binding, some _, some store) =>
      return .ok (store, "operation",
        (FnConsumerOperation.storeOperationAtom config.deployment.domain
          config.profile.semantics binding.application binding.operation).digest.value)
  | _ =>
      match FnConsumerOperation.originalConflictWithInbox gateway config.deployment.domain
          config.profile.semantics record with
      | some (conflict, some portable, some store) =>
          let report : FnConsumerOperation.Report :=
            { application := conflict.application, operation := conflict.operation,
              provenance := conflict.provenance, package := conflict.package,
              subject := ⟨0⟩, target := 0, capability := ⟨0⟩,
              expectedTargetRoot := ⟨0⟩,
              portableInbox := some portable, storePoll := some store }
          return .ok (store, "conflict",
            (FnConsumerOperation.storeConflictAtom config.deployment.domain
              config.profile.semantics report).digest.value)
      | _ => return .error "transaction has no canonical Store poll inbox"

def writeBytes (path : String) (bytes : List UInt8) : IO Unit :=
  IO.FS.writeBinFile path bytes.toByteArray

def readJson (path : String) : IO Lean.Json :=
  return ← IO.ofExcept (Minidregg.Host.Json.parse (← IO.FS.readFile path))

/-- Carry administration has bounded local inputs and independent configured
operator authority. The request or target capsule cannot introduce that key. -/
def readCarryJson (path : String) : IO Lean.Json := do
  let bytes ← readBoundedBytes path (1024 * 1024)
  let some source := String.fromUTF8? bytes.toByteArray
    | throw (IO.userError "carry input is not UTF-8")
  IO.ofExcept (Minidregg.Host.Json.parse source)

def carryOperator (settings : Settings) : IO (List UInt8) := do
  let some text := settings.carryOperatorKey
    | throw (IO.userError "carry requires independently configured operator authority")
  let key ← IO.ofExcept (Minidregg.Host.Json.decodeHex "carryOperatorKey" (.str text))
  if key.length != 32 || CarryInspection.encodeHex key != text then
    throw (IO.userError "carry operator key must be canonical lowercase 32-byte hexadecimal")
  pure key

/-- The registry is operator-local custody. Never send private paths or audit
process diagnostics through a public protocol failure. -/
def loadCarryRegistry (settings : Settings) : IO RetainedSegmentInspection.Registry := do
  try
    let some path := settings.carryRegistry
      | throw (IO.userError "missing registry")
    let operator ← carryOperator settings
    let json ← readCarryJson path
    IO.ofExcept (RetainedSegmentInspection.parseRegistry json operator)
  catch _ => throw (IO.userError "retained carry custody unavailable")

/-- A distinct cache holds actual target-suffix re-admission. Neither an old
record nor this certificate is cast to a genesis-walked target certificate. -/
def sessionCarriedWalked (config : NativeHost.Config)
    (state : IO.Ref (Option (NativeHostSession.Session config)))
    (carried : IO.Ref (Option (CarriedNativeHostSession.Walked config)))
    (settings : Settings) : IO (CarriedNativeHostSession.Walked config) := do
  try
    let current ← sessionCurrent config state
    let result ← match ← carried.get with
      | some prior => CarriedNativeHostSession.refresh config prior current.opened.durable
      | none => do
          let registry ← loadCarryRegistry settings
          let custody ← IO.ofExcept (← RetainedSegmentInspection.validate config
            current.opened.durable registry)
          CarriedNativeHostSession.start config current.opened.durable custody
    let walked ← IO.ofExcept result
    carried.set (some walked)
    return walked
  catch _ =>
    carried.set none
    state.set none
    throw (IO.userError "carried suffix validation failed")

def carriedEnrollmentSubmit (config : NativeHost.Config)
    (state : IO.Ref (Option (NativeHostSession.Session config)))
    (carried : IO.Ref (Option (CarriedNativeHostSession.Walked config)))
    (settings : Settings) (payload : List UInt8) : IO NativeHostCodec.Outcome := do
  let session ← sessionCarriedWalked config state carried settings
  match ← CarriedSessionEnrollmentReceiver.receiveVerified session.verified payload with
  | .confirmed confirmed =>
      carried.set (some ⟨session.anchor, confirmed.target, confirmed.verified⟩)
      return .confirmed confirmed.confirmation confirmed.receipt
  | .historical receipt => return .confirmed .replayed receipt
  | .rejected _ =>
      return .refused .operationRejected "application-session-enrollment".toUTF8.toList
        "carried enrollment refused".toUTF8.toList
  | .transactionConflict =>
      return .refused .conflict "replay".toUTF8.toList
        "transaction identity conflict".toUTF8.toList
  | .contention => return .contention
  | .unavailable _ => return .unavailable "carried enrollment unavailable".toUTF8.toList
  | .uncertain _ => return .uncertain "carried enrollment readback uncertain".toUTF8.toList

def carriedEnrollmentLookup (config : NativeHost.Config)
    (state : IO.Ref (Option (NativeHostSession.Session config)))
    (carried : IO.Ref (Option (CarriedNativeHostSession.Walked config)))
    (settings : Settings) (payload : List UInt8) : IO NativeHostCodec.Outcome := do
  let some ingress := ApplicationGrainSessionEnrollmentSource.ingressCodec.decode payload
    | return .refused .malformed "application-session-enrollment".toUTF8.toList
        "noncanonical ingress".toUTF8.toList
  unless ingress.canonicalBytes.toByteArray == payload.toByteArray do
    return .refused .malformed "application-session-enrollment".toUTF8.toList
      "noncanonical ingress".toUTF8.toList
  let session ← sessionCarriedWalked config state carried settings
  match CarriedSessionEnrollmentReceiver.lookupVerified session.verified ingress with
  | none => return .absent
  | some (.ok receipt) => return .confirmed .replayed receipt
  | some (.error _) =>
      return .refused .conflict "replay".toUTF8.toList
        "transaction identity conflict".toUTF8.toList

/-- A target identity starts at its authorized carry endpoint. Earlier
history is served only by its retained interpreter and original identity. -/
def carriedContinuitySession (config : NativeHost.Config)
    (state : IO.Ref (Option (NativeHostSession.Session config)))
    (carried : IO.Ref (Option (CarriedNativeHostSession.Walked config)))
    (settings : Settings) (payload : List UInt8) : IO (Except String (List UInt8)) := do
  let some text := String.fromUTF8? payload.toByteArray
    | return .error "receipt continuity request is not UTF-8"
  let request ← match Lean.Json.parse text >>= ReceiptContinuity.parseRequest with
    | .ok request => pure request
    | .error _ => return .error "receipt continuity request malformed"
  if request.query.identity != ReceiptContinuity.identityOf config then
    let registry ← loadCarryRegistry settings
    let opened ← sessionOpened config state
    RetainedSegmentInspection.serveContinuity config opened.durable registry payload
  else if settings.carryRegistry.isSome then
    let session ← sessionCarriedWalked config state carried settings
    if request.query.target.height < session.anchor.durable.height ||
        request.query.anchor.any (fun point => point.height < session.anchor.durable.height) then
      return .error "historical continuity requires its original profile"
    ReceiptContinuity.serve config session.verified.opened.durable payload
  else
    let opened ← sessionOpened config state
    ReceiptContinuity.serve config opened.durable payload

/-- Receipt selection never crosses a profile boundary. The carry record
itself is the authorized anchor; ordinary later records come from real replay. -/
def carriedReceipt (config : NativeHost.Config) (session : CarriedNativeHostSession.Walked config)
    (transactionId eventId : Minidregg.Theory.TypedAuthorization.Digest) :
    Option NativeHostCodec.Receipt := do
  let index ← session.verified.opened.durable.image.accepted.findIdx?
    (fun record => record.transactionId == transactionId)
  let record ← session.verified.opened.durable.image.accepted[index]?
  if record.event.eventId != eventId then none else do
    if index + 1 == session.anchor.durable.height then
      let origin ← session.verified.origin
      if transactionId != origin.edge.body.id || eventId != origin.edge.body.id then none else
      some ⟨transactionId, eventId, index + 1, session.anchor.durable.worldRoot⟩
    else session.verified.receiptAt index

/-- Old exact recovery precedes any target submission. A retained original is
never submitted again, and target confirmation is reselected under its actual
suffix certificate before the reply crosses the native boundary. -/
def carriedOrdinaryCall (config : NativeHost.Config)
    (state : IO.Ref (Option (NativeHostSession.Session config)))
    (carried : IO.Ref (Option (CarriedNativeHostSession.Walked config)))
    (settings : Settings) (submit : Bool) (payload : List UInt8) : IO NativeHostCodec.Outcome := do
  let session ← sessionCarriedWalked config state carried settings
  let registry ← loadCarryRegistry settings
  match ← RetainedSegmentInspection.serveOriginalCall config session.verified.opened.durable
      registry payload with
  | .error _ => return .unavailable "retained original lookup unavailable".toUTF8.toList
  | .ok .absent => pure ()
  | .ok (.refused .malformed _ _) => pure ()
  | .ok outcome => return outcome
  let some call := callCodec.decode payload
    | return .refused .malformed "wire".toUTF8.toList "noncanonical native host call".toUTF8.toList
  let outcome ← if submit then do
    let result ← NativeHost.submitDisclosedWith config session.verified.opened call
      (fun kind transaction event => do
        let current ← sessionCarriedWalked config state carried settings
        match carriedReceipt config current transaction event with
        | some receipt => return .confirmed kind receipt
        | none => return .uncertain "original receipt belongs to retained profile".toUTF8.toList)
    NativeHost.logOperatorRefusal result.1
    pure (NativeHost.disclose result)
  else pure (NativeHost.lookupLoaded config session.verified.opened call)
  match outcome with
  | .confirmed kind candidate =>
      let current ← sessionCarriedWalked config state carried settings
      match carriedReceipt config current candidate.transactionId candidate.eventId with
      | some receipt => return .confirmed kind receipt
      | none => return .uncertain "original receipt belongs to retained profile".toUTF8.toList
  | other => return other

/-- Select retained dispatch only by exact authenticated old event bytes.
Absence from this segment leaves target lookup/admission to its own receiver. -/
def retainedDispatchReceipt (config : NativeHost.Config)
    (session : CarriedNativeHostSession.Walked config) (settings : Settings)
    (payload : List UInt8) : IO (Option NativeHostCodec.Outcome) := do
  let some origin := session.verified.origin | return none
  unless origin.source.durable.image.accepted.any (fun record =>
      record.event.codecVersion == 11 && record.event.canonicalBytes == payload) do
    return none
  let registry ← loadCarryRegistry settings
  match ← RetainedSegmentInspection.serveDispatchLookup config
      session.verified.opened.durable registry payload with
  | .ok receipt => return some (.confirmed .replayed receipt)
  | .error _ => return some (.uncertain "retained dispatch receipt unavailable".toUTF8.toList)

/-- A real carried dispatch keeps the same private permit handoff boundary.
Route mismatch is classified before CAS; no post-durable branch claims absence. -/
def carriedApplicationSubmit (config : NativeHost.Config)
    (state : IO.Ref (Option (NativeHostSession.Session config)))
    (carried : IO.Ref (Option (CarriedNativeHostSession.Walked config)))
    (settings : Settings) (routeBound : Bool) (payload : List UInt8)
    (output : IO.FS.Stream) : IO Unit := do
  let session ← sessionCarriedWalked config state carried settings
  let original := if routeBound then
    ((ApplicationDispatchReceiver.routeBoundCodec.decode payload).map Prod.snd).getD []
    else payload
  if let some receipt ← retainedDispatchReceipt config session settings original then
    writeSessionFrame output 34 (outcomeCodec.encode receipt)
    return
  let result ← if routeBound then
    CarriedApplicationDispatchReceiver.receiveRouteBoundVerified config session.verified payload
  else CarriedApplicationDispatchReceiver.receiveVerified config session.verified payload
  match result with
  | .permitted permit =>
      let handed ← permit.withFreshTip (fun bytes => writeSessionFrame output 34 bytes)
      match handed with
      | .ok _ => carried.set (some ⟨session.anchor, permit.committed.target, permit.verified⟩)
      | .error _ => writeSessionFrame output 34 <| outcomeCodec.encode <|
          .uncertain "carried dispatch physical handoff uncertain".toUTF8.toList
  | .committed committed =>
      carried.set (some ⟨session.anchor, committed.target, committed.verified⟩)
      writeSessionFrame output 34 <| outcomeCodec.encode <|
        .confirmed .replayed committed.receipt
  | .noRecordRefused token =>
      let cleared ← token.withFreshTip (fun bytes => writeSessionFrame output 164 bytes)
      match cleared with
      | .ok _ => pure ()
      | .error _ => writeSessionFrame output 34 (outcomeCodec.encode
          (.uncertain "dispatch absence tip changed before handoff".toUTF8.toList))
  | .historical receipt =>
      writeSessionFrame output 34 (outcomeCodec.encode (.confirmed .replayed receipt))
  | .rejected _ => writeSessionFrame output 34 <| outcomeCodec.encode <|
      NativeHost.publicSubmissionOutcome (.refused .operationRejected
        "application-dispatch".toUTF8.toList "request refused".toUTF8.toList)
  | .contention => writeSessionFrame output 34 (outcomeCodec.encode .contention)
  | .unavailable _ =>
      writeSessionFrame output 34 (outcomeCodec.encode
        (.unavailable "carried dispatch unavailable".toUTF8.toList))
  | .uncertain _ =>
      writeSessionFrame output 34 (outcomeCodec.encode
        (.uncertain "carried dispatch readback uncertain".toUTF8.toList))

/-- A suffix receipt is selected at its original accepted count. A retained
old-profile dispatch requires its source interpreter and never gets a new root. -/
def carriedApplicationLookup (config : NativeHost.Config)
    (state : IO.Ref (Option (NativeHostSession.Session config)))
    (carried : IO.Ref (Option (CarriedNativeHostSession.Walked config)))
    (settings : Settings) (payload : List UInt8) : IO NativeHostCodec.Outcome := do
  let session ← sessionCarriedWalked config state carried settings
  if let some original ← retainedDispatchReceipt config session settings payload then
    return original
  match CarriedApplicationDispatchReceiver.lookupVerified session.verified payload with
  | .ok none => return .absent
  | .ok (some receipt) => return .confirmed .replayed receipt
  | .error .malformed =>
      return .refused .malformed "application-dispatch".toUTF8.toList
        "noncanonical lookup ingress".toUTF8.toList
  | .error .transactionConflict =>
      return .refused .conflict "replay".toUTF8.toList
        "transaction identity conflict".toUTF8.toList
  | .error .nativeHistoryUnavailable =>
      return .uncertain "dispatch original history requires retained profile".toUTF8.toList

def readDispatchAuthorJson (path : String) : IO Lean.Json := do
  let bytes ← readBoundedBytes path maxDispatchAuthorJsonBytes
  let some source := String.fromUTF8? bytes.toByteArray
    | throw (IO.userError "dispatch author request is not UTF-8")
  IO.ofExcept (Minidregg.Host.Json.parse source)

def writeJson (path : String) (value : Lean.Json) : IO Unit :=
  IO.FS.writeFile path value.pretty

/-- Selected release keeps fn transport and owner-signed Mini admission
separate. The caller chooses an operator-pinned local fn executable/scope, but
cannot turn a projected article into a receipt or ACK without Mini. -/
def selectedFnScope (scopePath : String) : IO FnPollScopePin := do
  let bytes ← readBoundedBytes scopePath 8192
  let some source := String.fromUTF8? bytes.toByteArray
    | throw (IO.userError "fn selected-release scope is not UTF-8")
  let json ← IO.ofExcept (Minidregg.Host.Json.parse source)
  IO.ofExcept (requireExactFields "fn selected-release scope"
    ["history", "incarnation", "consumer", "principal", "query",
     "queryVersion", "viewVersion", "registrationEpoch"] json)
  IO.ofExcept (fromJson? json)

/-- The registration author uses only lifetime-pinned operator manifests and
the qualified local fn position/status call. No stdio frame selects a binary,
control endpoint, consumer scope, or gateway. -/
def fnNamespaceLocalZero (config : NativeHost.Config)
    (service : FnPollService) : IO (FnConsumerScope.Scope × List UInt8) := do
  let gateway ← requireGateway config
  let pinJson ← readJson service.fnPinPath
  IO.ofExcept (requireExactFields "fn namespace binary pin"
    ["fnBinary", "mlPublicKey", "principal", "edPublicKey", "mlPublicKeyHex"] pinJson)
  let pin : FnPortablePin ← IO.ofExcept (fromJson? pinJson)
  let policyJson ← readJson service.policyPath
  IO.ofExcept (requireExactFields "fn namespace gateway policy"
    ["application", "subject", "target", "capability"] policyJson)
  let policy : ConsumerPolicySource ← IO.ofExcept (fromJson? policyJson)
  unless policy.policy.matchesGateway gateway do
    throw (IO.userError "fn namespace operator policy differs from configured gateway")
  let scopePin ← selectedFnScope service.scopePath
  let scope ← IO.ofExcept scopePin.progressScope
  let (position, status) ← queryFnConsumerPosition service.fnExecutable
    scopePin service.controlPath
  unless position == 0 && status.committedAck == 0 do
    throw (IO.userError "fn namespace activation requires native ACK zero")
  return (scope, FnConsumerOperation.pollControlBinding pin.fnBinary service.controlPath)

/-- Exact configured fn identity for post-registration progress. Position is
checked against the replay-minted Mini predecessor by the caller. -/
def fnFrontierLocalScope (config : NativeHost.Config)
    (service : FnPollService) : IO (FnPollScopePin × FnConsumerScope.Scope ×
      List UInt8 × NativeHost.FnGatewayPin) := do
  let gateway ← requireGateway config
  let pinJson ← readJson service.fnPinPath
  IO.ofExcept (requireExactFields "fn frontier binary pin"
    ["fnBinary", "mlPublicKey", "principal", "edPublicKey", "mlPublicKeyHex"] pinJson)
  let pin : FnPortablePin ← IO.ofExcept (fromJson? pinJson)
  let policyJson ← readJson service.policyPath
  IO.ofExcept (requireExactFields "fn frontier gateway policy"
    ["application", "subject", "target", "capability"] policyJson)
  let policy : ConsumerPolicySource ← IO.ofExcept (fromJson? policyJson)
  unless policy.policy.matchesGateway gateway do
    throw (IO.userError "fn frontier operator policy differs from configured gateway")
  let scopePin ← selectedFnScope service.scopePath
  let scope ← IO.ofExcept scopePin.progressScope
  return (scopePin, scope,
    FnConsumerOperation.pollControlBinding pin.fnBinary service.controlPath, gateway)

def fnFrontierPlanRequestCodec :=
  ResourceBirthCodec.strictCodec
    (NativeHostCodec.framed "DREGG/FN/CONSUMER-FRONTIER-PLAN-REQUEST/v2".toUTF8.toList
      (StreamCodec.option digestStream))

/-- Op64 polls only the configured local consumer. The optional transaction ID
selects an already accepted Mini event13; `none` selects a bounded empty page.
No cursor, fn status, root, gateway, or scope is accepted in the request. -/
def fnFrontierPrepareSession (config : NativeHost.Config)
    (state : IO.Ref (Option (NativeHostSession.Session config)))
    (service : FnPollService)
    (releaseKey : Option Minidregg.Theory.TypedAuthorization.Digest) :
    IO FnConsumerFrontierPlan.Plan := do
  let (scopePin, scope, binding, gateway) ← fnFrontierLocalScope config service
  let key : FnConsumerFrontierCore.Key :=
    ⟨gateway.application, scope, binding, gateway.subject, gateway.target,
      gateway.capability⟩
  let session ← sessionWalked config state
  let cursor ← IO.ofExcept (session.verified.frontierCursor key)
  let registration ← match session.verified.frontier.registrations.find?
      (fun original => original.ingress.spec.consumerNamespace == key.namespace) with
    | none => throw (IO.userError "fn frontier has no admitted namespace")
    | some original => pure original
  let _ ← IO.ofExcept (session.verified.frontierRegistration key registration.receipt)
  IO.FS.withTempDir fun directory => do
    let executable ← snapshotOperatorFile directory "fn-frontier-helper"
      service.fnExecutable (64 * 1024 * 1024) "0500"
    let (position, before) ← queryFnConsumerPosition executable scopePin
      service.controlPath
    unless position == before.committedAck && position == cursor.position do
      throw (IO.userError "fn frontier local ACK differs from verified Mini predecessor")
    let cursorPath := (directory / "cursor.fncu").toString
    let reportPath := (directory / "report.fn-e").toString
    let (cursorBytes, reportBytes) ← invokeFnConsumerPollRaw executable scopePin
      service.controlPath cursorPath reportPath
    let mut selected : Option FnSelectedPollCoverage.Spec := none
    let mut empty : Option FnEmptyPollProgressV2.Spec := none
    let mut sourceBytes : List UInt8 := []
    match releaseKey with
    | some transaction =>
        unless !reportBytes.isEmpty do
          throw (IO.userError "selected fn frontier poll produced an empty page")
        let (projectedCursor, projectedReport, projection) ←
          projectFnPoll executable scopePin cursorPath reportPath
        unless projectedCursor == cursorBytes && sameBytes projectedReport reportBytes &&
            cursor.position ≤ projection.sequence &&
            projection.sequence + 1 == projection.position &&
            projection.position ≤ cursor.position + FnConsumerScope.maxPollScan do
          throw (IO.userError "selected fn poll is outside authenticated scan window")
        let original ← IO.ofExcept <| FnSelectiveReleaseFnAck.selectOriginal
          config session.target session.verified transaction
          projection.source projection.messageId
        sourceBytes := projection.source
        selected := some
          { domain := config.deployment.domain
            semantics := config.profile.semantics
            evidence :=
              { key := key
                fromPosition := cursor.position
                selectedSequence := projection.sequence
                toPosition := projection.position
                predecessor := cursor.receipt
                cursor := cursorBytes
                reportDigest := FnConsumerFrontierCore.reportDigest reportBytes
                sourceDigest := FnConsumerFrontierCore.sourceDigest projection.source
                messageId := projection.messageId
                releaseReceipt := original.receipt
                releaseKey := transaction }
            registrationReceipt := registration.receipt
            gatewaySubject := gateway.subject
            gatewayTarget := gateway.target
            gatewayCapability := gateway.capability }
    | none =>
        unless reportBytes.isEmpty do
          throw (IO.userError "empty fn frontier poll returned an article")
        let some (fromPosition, toPosition) ← classifyFnEmptyPoll executable scopePin
            service.controlPath cursorPath reportPath cursorBytes before
          | throw (IO.userError "fn frontier poll is idle")
        unless fromPosition == cursor.position do
          throw (IO.userError "empty fn poll differs from verified Mini predecessor")
        empty := some
          { domain := config.deployment.domain
            semantics := config.profile.semantics
            evidence :=
              { key := key
                fromPosition := fromPosition
                toPosition := toPosition
                predecessor := cursor.receipt
                cursor := cursorBytes
                reportDigest := FnConsumerFrontierCore.reportDigest reportBytes }
            registrationReceipt := registration.receipt
            gatewaySubject := gateway.subject
            gatewayTarget := gateway.target
            gatewayCapability := gateway.capability }
    let (afterPosition, after) ← queryFnConsumerPosition executable scopePin
      service.controlPath
    unless afterPosition == position && after.committedAck == before.committedAck do
      throw (IO.userError "fn frontier local ACK changed during poll")
    IO.ofExcept (FnConsumerFrontierPlan.prepare config session.verified.opened
      selected empty cursorBytes reportBytes sourceBytes)

def selectedFnNewPaths (paths : List String) : IO Unit := do
  unless paths.all (·.startsWith "/") && paths.eraseDups.length == paths.length do
    throw (IO.userError "selected-release fn paths must be distinct absolute paths")
  for path in paths do
    if ← (System.FilePath.mk path).pathExists then
      throw (IO.userError s!"selected-release fn output already exists: {path}")

/-- One native fn poll and projection. The owner signature and current
recipient law are checked later by Mini op20; this route never ACKs. -/
def selectedReleaseFnPoll (fnBinary scopePath controlPath capabilitySource
    targetSource cursorPath reportPath sourcePath packetPath
    ingressPath resultPath : String) : IO Unit := do
  unless [fnBinary, scopePath, controlPath].all (·.startsWith "/") do
    throw (IO.userError "selected-release fn operator paths must be absolute")
  selectedFnNewPaths [cursorPath, reportPath, sourcePath, packetPath,
    ingressPath, resultPath]
  let capability : Minidregg.Theory.TypedAuthorization.CapabilityId :=
    ⟨← IO.ofExcept (exactDecimal "recipient capability" capabilitySource)⟩
  let targetRoot : Minidregg.Theory.TypedAuthorization.Digest :=
    ⟨← IO.ofExcept (exactDecimal "recipient target root" targetSource)⟩
  let scope ← selectedFnScope scopePath
  IO.FS.withTempDir fun directory => do
    let executable ← snapshotOperatorFile directory "selected-release-fn-helper"
      fnBinary (64 * 1024 * 1024) "0500"
    let (fromPosition, before) ← queryFnConsumerPosition executable scope controlPath
    unless fromPosition == before.committedAck do
      throw (IO.userError "selected-release fn poll lacks an exact durable start position")
    let (cursor, report) ← invokeFnConsumerPollRaw executable scope
      controlPath cursorPath reportPath
    let (selectedCursor, selectedReport, projection) ←
      projectFnPoll executable scope cursorPath reportPath
    unless cursor == selectedCursor && sameBytes report selectedReport do
      throw (IO.userError "selected-release fn poll changed during projection")
    -- Qualified fn scans at most one bounded first-match page. This route
    -- emits only an owner-signed recipient candidate, never an fn ACK.
    -- Event17 must later record the exact local observation before ACK.
    unless fromPosition ≤ projection.sequence &&
        projection.position == projection.sequence + 1 &&
        projection.position ≤ fromPosition + FnConsumerScope.maxPollScan do
      throw (IO.userError "selected-release fn poll exceeds bounded scan")
    let (afterPosition, after) ← queryFnConsumerPosition executable scope controlPath
    unless afterPosition == fromPosition && after.committedAck == before.committedAck do
      throw (IO.userError "selected-release fn poll position changed before candidate")
    let candidate ← IO.ofExcept <| FnSelectiveReleaseFnReceiving.derive
      projection.source projection.messageId capability targetRoot
    writeBytes sourcePath projection.source
    writeBytes packetPath candidate.packetBytes
    writeBytes ingressPath candidate.ingressBytes
    writeJson resultPath <| Lean.Json.mkObj
      [("type", toJson "selected-release-fn-poll-v1"),
       ("status", toJson "candidate-unacknowledged"),
       ("fnPosition", toJson (toString projection.position)),
       ("fnStoreSequence", toJson (toString projection.sequence)),
       ("fnStoreTransactionId", toJson (toString projection.transactionId)),
       ("fnSourceIdentity", toJson (Minidregg.Host.Json.encodeHex projection.sourceIdentity)),
       ("messageId", toJson (Minidregg.Host.Json.encodeHex projection.messageId)),
       ("sourceBytes", toJson (toString projection.source.length)),
       ("packetBytes", toJson (toString candidate.packetBytes.length)),
       ("ingressBytes", toJson (toString candidate.ingressBytes.length))]

/-- The older NNTP publication route is a genuine fn Store observation but
its poll report is a legacy `fn-r`, with no fn-authored-source or historical
signature verdict. Extract only the stored article through fn's ACL2 decoder,
bind its exact owner-authored suffix and Message-ID, and leave Mini admission
to the independently signed release packet and current recipient law. This
route never emits an fn-e verdict, event17 coverage, or cursor ACK. -/
def selectedReleaseFnLegacyPoll (fnBinary scopePath controlPath expectedArticlePath
    capabilitySource targetSource cursorPath reportPath storedPath
    packetPath ingressPath resultPath : String) : IO Unit := do
  unless [fnBinary, scopePath, controlPath, expectedArticlePath].all (·.startsWith "/") do
    throw (IO.userError "selected-release legacy fn inputs must be absolute")
  selectedFnNewPaths [cursorPath, reportPath, storedPath, packetPath,
    ingressPath, resultPath]
  let capability : Minidregg.Theory.TypedAuthorization.CapabilityId :=
    ⟨← IO.ofExcept (exactDecimal "recipient capability" capabilitySource)⟩
  let targetRoot : Minidregg.Theory.TypedAuthorization.Digest :=
    ⟨← IO.ofExcept (exactDecimal "recipient target root" targetSource)⟩
  let expected ← readBoundedBytes expectedArticlePath FnEvidenceCodec.maxSourceBytes
  let scope ← selectedFnScope scopePath
  IO.FS.withTempDir fun directory => do
    let executable ← snapshotOperatorFile directory "selected-release-fn-helper"
      fnBinary (64 * 1024 * 1024) "0500"
    let (fromPosition, before) ← queryFnConsumerPosition executable scope controlPath
    unless fromPosition == before.committedAck do
      throw (IO.userError "selected-release legacy fn poll lacks durable start")
    let (cursor, report) ← invokeFnConsumerPollRaw executable scope
      controlPath cursorPath reportPath
    unless report.take 5 == [68, 102, 110, 45, 114] do
      throw (IO.userError "selected-release legacy fn poll requires fn-r report")
    let (inspectedScope, position) ← inspectFnConsumerCursor executable cursorPath
    unless inspectedScope == (← IO.ofExcept scope.progressScope) &&
        fromPosition < position &&
        position ≤ fromPosition + FnConsumerProgress.maxPollScan do
      throw (IO.userError "selected-release legacy fn cursor differs from pinned scope or scan")
    let child ← IO.Process.spawn
      { cmd := executable, args := #["--fn", "consumer-article", "--json", reportPath],
        stdin := .null, stdout := .piped, stderr := .piped }
    let stderrTask ← IO.asTask (readDiagnosticStderr child.stderr 2048)
    let output ← try readBoundedLoop child.stdout 3_200_000
      catch error =>
        child.kill
        discard <| child.wait
        throw error
    let exitCode ← child.wait
    let _ ← match stderrTask.get with
      | .ok bytes => pure bytes
      | .error error => throw error
    unless exitCode == 0 do
      throw (IO.userError "fn native legacy article extraction refused")
    let some source := String.fromUTF8? output.toByteArray
      | throw (IO.userError "fn native legacy article output is not UTF-8")
    let [line, ""] := source.splitOn "\n"
      | throw (IO.userError "fn native legacy article output has unexpected framing")
    let json ← IO.ofExcept (Minidregg.Host.Json.parse line)
    IO.ofExcept (requireExactFields "fn legacy article"
      ["report", "message_id", "article_hex"] json)
    let reportType ← IO.ofExcept (json.getObjValAs? String "report")
    unless reportType == "article" do
      throw (IO.userError "fn legacy report carries no article")
    let messageId ← IO.ofExcept (json.getObjValAs? String "message_id")
    let articleHex ← IO.ofExcept (json.getObjValAs? String "article_hex")
    let stored ← IO.ofExcept (decodeCanonicalHex "fn stored article" articleHex)
    unless stored.length ≤ FnEvidenceCodec.maxStorePollEventBytes &&
        expected.length ≤ stored.length &&
        stored.drop (stored.length - expected.length) == expected do
      throw (IO.userError "fn stored article lacks exact selected owner source suffix")
    let candidate ← IO.ofExcept <| FnSelectiveReleaseFnReceiving.derive
      expected messageId.toUTF8.toList capability targetRoot
    let (afterPosition, after) ← queryFnConsumerPosition executable scope controlPath
    unless afterPosition == fromPosition &&
        after.committedAck == before.committedAck &&
        cursor == (← readBoundedBytes cursorPath 346) &&
        report == (← readBoundedBytes reportPath FnEvidenceCodec.maxStorePollEventBytes) do
      throw (IO.userError "selected-release legacy fn observation changed")
    writeBytes storedPath stored
    writeBytes packetPath candidate.packetBytes
    writeBytes ingressPath candidate.ingressBytes
    writeJson resultPath <| Lean.Json.mkObj
      [("type", toJson "selected-release-fn-legacy-poll-v1"),
       ("status", toJson "candidate-unacknowledged"),
       ("mode", toJson "fn-r-transport-only"),
       ("fnPosition", toJson (toString position)),
       ("messageId", toJson (Minidregg.Host.Json.encodeHex candidate.messageId)),
       ("storedBytes", toJson (toString stored.length)),
       ("sourceBytes", toJson (toString expected.length)),
       ("packetBytes", toJson (toString candidate.packetBytes.length))]

/-- Reproject the exact retained cursor/event and select the original accepted
Mini event 13 from a fresh verifier-opened Store. Before a new ACK, repeat the
authenticated local poll and require the fn Store to return those same bytes. -/
def selectedReleaseFnAck (config : NativeHost.Config) (service : FnPollService)
    (cursorPath reportPath transaction coveragePath resultPath : String) : IO UInt32 := do
  let fnBinary := service.fnExecutable
  let controlPath := service.controlPath
  unless [fnBinary, controlPath, cursorPath, reportPath, coveragePath,
      resultPath].all (·.startsWith "/") && cursorPath != reportPath &&
      resultPath != cursorPath && resultPath != reportPath &&
      coveragePath != cursorPath && coveragePath != reportPath &&
      coveragePath != resultPath do
    throw (IO.userError "selected-release fn ACK paths must be distinct absolute paths")
  selectedFnNewPaths [resultPath]
  let transactionId : Minidregg.Theory.TypedAuthorization.Digest :=
    ⟨← IO.ofExcept (exactDecimal "accepted Mini transaction" transaction)⟩
  let (scope, progressScope, binding, gateway) ←
    fnFrontierLocalScope config service
  IO.FS.withTempDir fun directory => do
    let executable ← snapshotOperatorFile directory "selected-release-fn-helper"
      fnBinary (64 * 1024 * 1024) "0500"
    let (cursor, report, projection) ← projectFnPoll executable scope cursorPath reportPath
    let target ← IO.ofExcept (← DurableReceiverIO.load config.transport
      ResourceBirthCodec.rootBytes)
    let verified ← match ← NativeHostReplay.verifyLoaded config target with
      | .ok verified => pure verified
      | .error failure =>
          throw (IO.userError s!"selected-release Mini history refused at {failure.index}: {failure.detail}")
    let selected ← IO.ofExcept <| FnSelectiveReleaseFnAck.selectOriginal config
      target verified transactionId projection.source projection.messageId
    let coverageBytes ← readBoundedBytes coveragePath 16384
    let some coverage := FnSelectedPollCoverage.ingressCodec.decode coverageBytes
      | throw (IO.userError "selected-release fn ACK lacks canonical event17 ingress")
    let some (.ok coverageReceipt) :=
        FnSelectedPollReceiver.lookupVerified verified coverage
      | throw (IO.userError "selected-release fn ACK lacks an admitted event17 receipt")
    let evidence := coverage.spec.evidence
    unless evidence.key.application == gateway.application &&
        evidence.key.scope == progressScope &&
        evidence.key.controlBinding == binding &&
        evidence.key.gatewaySubject == gateway.subject &&
        evidence.key.gatewayTarget == gateway.target &&
        evidence.key.gatewayCapability == gateway.capability &&
        evidence.releaseKey == transactionId &&
        evidence.releaseReceipt == selected.receipt &&
        evidence.cursor == cursor &&
        evidence.reportDigest == FnConsumerFrontierCore.reportDigest report &&
        evidence.sourceDigest == FnConsumerFrontierCore.sourceDigest projection.source &&
        evidence.messageId == projection.messageId &&
        evidence.selectedSequence == projection.sequence &&
        evidence.toPosition == projection.position do
      throw (IO.userError "selected-release fn ACK differs from durable coverage")
    let _ ← IO.ofExcept (verified.frontierRegistration evidence.key
      coverage.spec.registrationReceipt)
    let (currentPosition, currentStatus) ←
      queryFnConsumerPosition executable scope controlPath
    unless currentPosition == currentStatus.committedAck do
      throw (IO.userError "selected-release fn ACK lacks an exact durable position")
    unless currentStatus.committedAck ≥ projection.position ||
        currentStatus.committedAck == evidence.fromPosition do
      throw (IO.userError "selected-release fn ACK differs from covered predecessor")
    let mut status := "covered-by-durable-frontier"
    let mut committedAck := currentStatus.committedAck
    if committedAck < projection.position then do
      let liveCursorPath := (directory / "current-cursor.fncu").toString
      let liveReportPath := (directory / "current-report.fn-e").toString
      let (liveCursor, liveReport) ← invokeFnConsumerPollRaw executable scope
        controlPath liveCursorPath liveReportPath
      unless cursor == liveCursor && sameBytes report liveReport do
        throw (IO.userError "selected-release fn ACK poll differs from retained event")
      let child ← IO.Process.spawn
        { cmd := executable, args := #["--fn", "consumer", "ack", controlPath, liveCursorPath],
          stdin := .null, stdout := .piped, stderr := .null }
      let output ← try readBoundedLoop child.stdout 128
        catch error =>
          child.kill
          discard <| child.wait
          throw error
      let exitCode ← child.wait
      unless cursor == (← readBoundedBytes cursorPath 346) &&
          sameBytes report (← readBoundedBytes reportPath FnEvidenceCodec.maxStorePollEventBytes) do
        throw (IO.userError "selected-release fn ACK inputs changed during local call")
      status := if exitCode == 0 && output == "consumer accepted\n".toUTF8.toList then
          "durable-accepted"
        else if exitCode == 2 then "refused"
        else if exitCode == 3 then "uncertain"
        else "transport-fault"
      let (afterPosition, after) ← queryFnConsumerPosition executable scope controlPath
      unless afterPosition == after.committedAck do
        throw (IO.userError "selected-release fn ACK changed consumer scope")
      committedAck := after.committedAck
      if status == "durable-accepted" && committedAck < projection.position then
        throw (IO.userError "fn accepted selected-release ACK without durable cursor")
      if status == "refused" && committedAck ≥ projection.position then
        status := "covered-by-durable-frontier"
    writeJson resultPath <| Lean.Json.mkObj
      [("type", toJson "selected-release-fn-ack-v1"),
       ("miniTransactionId", toJson transaction),
       ("miniReceipt", evidenceReceiptJson selected.receipt),
       ("coverageReceipt", evidenceReceiptJson coverageReceipt),
       ("fnStoreSequence", toJson (toString projection.sequence)),
       ("fnStoreTransactionId", toJson (toString projection.transactionId)),
       ("fnPosition", toJson (toString projection.position)),
       ("fnCommittedAck", toJson (toString committedAck)),
       ("fnAck", toJson status)]
    if status == "durable-accepted" || status == "covered-by-durable-frontier" then pure 0
    else if status == "refused" then pure 2
    else if status == "uncertain" then pure 3
    else pure 1

/-- An empty-page ACK consumes only a durably accepted event19. The exact
retained cursor/report and a fresh pinned local poll must agree before the fn
ACK call; a transport cursor alone cannot skip a Mini predecessor. -/
def selectedEmptyFnAck (config : NativeHost.Config) (service : FnPollService)
    (cursorPath reportPath coveragePath resultPath : String) : IO UInt32 := do
  let fnBinary := service.fnExecutable
  let controlPath := service.controlPath
  unless [fnBinary, controlPath, cursorPath, reportPath, coveragePath,
      resultPath].all (·.startsWith "/") &&
      [cursorPath, reportPath, coveragePath, resultPath].eraseDups.length == 4 do
    throw (IO.userError "empty fn ACK paths must be distinct absolute paths")
  selectedFnNewPaths [resultPath]
  let (scope, progressScope, binding, gateway) ←
    fnFrontierLocalScope config service
  IO.FS.withTempDir fun directory => do
    let executable ← snapshotOperatorFile directory "fn-empty-ack-helper"
      fnBinary (64 * 1024 * 1024) "0500"
    let cursor ← readBoundedBytes cursorPath 346
    let report ← readBoundedBytes reportPath FnEvidenceCodec.maxStorePollEventBytes
    unless !cursor.isEmpty && report.isEmpty do
      throw (IO.userError "empty fn ACK retained poll is not empty")
    let (inspectedScope, position) ← inspectFnConsumerCursor executable cursorPath
    unless inspectedScope == progressScope do
      throw (IO.userError "empty fn ACK cursor differs from pinned scope")
    let target ← IO.ofExcept (← DurableReceiverIO.load config.transport
      ResourceBirthCodec.rootBytes)
    let verified ← match ← NativeHostReplay.verifyLoaded config target with
      | .ok verified => pure verified
      | .error failure =>
          throw (IO.userError s!"empty fn Mini history refused at {failure.index}: {failure.detail}")
    let coverageBytes ← readBoundedBytes coveragePath 12288
    let some coverage := FnEmptyPollProgressV2.ingressCodec.decode coverageBytes
      | throw (IO.userError "empty fn ACK lacks canonical event19 ingress")
    let some (.ok coverageReceipt) :=
        FnEmptyPollReceiverV2.lookupVerified verified coverage
      | throw (IO.userError "empty fn ACK lacks an admitted event19 receipt")
    let evidence := coverage.spec.evidence
    unless evidence.key.application == gateway.application &&
        evidence.key.scope == progressScope &&
        evidence.key.controlBinding == binding &&
        evidence.key.gatewaySubject == gateway.subject &&
        evidence.key.gatewayTarget == gateway.target &&
        evidence.key.gatewayCapability == gateway.capability &&
        evidence.cursor == cursor &&
        evidence.reportDigest == FnConsumerFrontierCore.reportDigest report &&
        evidence.toPosition == position do
      throw (IO.userError "empty fn ACK differs from durable progress")
    let _ ← IO.ofExcept (verified.frontierRegistration evidence.key
      coverage.spec.registrationReceipt)
    let (currentPosition, currentStatus) ←
      queryFnConsumerPosition executable scope controlPath
    unless currentPosition == currentStatus.committedAck &&
        (currentPosition ≥ position || currentPosition == evidence.fromPosition) do
      throw (IO.userError "empty fn ACK differs from covered predecessor")
    let mut status := "covered-by-durable-frontier"
    let mut committedAck := currentStatus.committedAck
    if committedAck < position then do
      let liveCursorPath := (directory / "current-cursor.fncu").toString
      let liveReportPath := (directory / "current-report.fn-e").toString
      let (liveCursor, liveReport) ← invokeFnConsumerPollRaw executable scope
        controlPath liveCursorPath liveReportPath
      unless cursor == liveCursor && report == liveReport && liveReport.isEmpty do
        throw (IO.userError "empty fn ACK poll differs from retained page")
      let child ← IO.Process.spawn
        { cmd := executable, args := #["--fn", "consumer", "ack", controlPath, liveCursorPath],
          stdin := .null, stdout := .piped, stderr := .null }
      let output ← try readBoundedLoop child.stdout 128
        catch error =>
          child.kill
          discard <| child.wait
          throw error
      let exitCode ← child.wait
      unless cursor == (← readBoundedBytes cursorPath 346) &&
          report == (← readBoundedBytes reportPath FnEvidenceCodec.maxStorePollEventBytes) do
        throw (IO.userError "empty fn ACK inputs changed during local call")
      status := if exitCode == 0 && output == "consumer accepted\n".toUTF8.toList then
          "durable-accepted"
        else if exitCode == 2 then "refused"
        else if exitCode == 3 then "uncertain"
        else "transport-fault"
      let (afterPosition, after) ← queryFnConsumerPosition executable scope controlPath
      unless afterPosition == after.committedAck do
        throw (IO.userError "empty fn ACK changed consumer scope")
      committedAck := after.committedAck
      if status == "durable-accepted" && committedAck < position then
        throw (IO.userError "fn accepted empty ACK without durable cursor")
      if status == "refused" && committedAck ≥ position then
        status := "covered-by-durable-frontier"
    writeJson resultPath <| Lean.Json.mkObj
      [("type", toJson "fn-empty-page-ack-v2"),
       ("coverageReceipt", evidenceReceiptJson coverageReceipt),
       ("fnPosition", toJson (toString position)),
       ("fnCommittedAck", toJson (toString committedAck)),
       ("fnAck", toJson status)]
    if status == "durable-accepted" || status == "covered-by-durable-frontier" then pure 0
    else if status == "refused" then pure 2
    else if status == "uncertain" then pure 3
    else pure 1

/-- This is the only Mini decision body for both file-only and observed
polls. Only the caller that actually invokes fn's control route can set the
local observation bit retained in the signed inbox atom. -/
def runPollConsumerDecisionLoaded (config : NativeHost.Config)
    (opened : NativeHost.Opened config)
    (controlBinding : Option (String × String))
    (originPath pinPath scopePath claimPath policyPath cursorPath reportPath
     carrierPath intentPath resultPath : String)
    (execution : Option (String × String) := none) : IO UInt32 := do
  let gateway ← requireGateway config
  let origin := (← loadSettings originPath).config
  let pinJson ← readJson pinPath
  let scopeJson ← readJson scopePath
  let claimJson ← readJson claimPath
  let policyJson ← readJson policyPath
  IO.ofExcept (requireExactFields "fn pin"
    ["fnBinary", "mlPublicKey", "principal", "edPublicKey", "mlPublicKeyHex"] pinJson)
  IO.ofExcept (requireExactFields "fn poll scope"
    ["history", "incarnation", "consumer", "principal", "query",
     "queryVersion", "viewVersion", "registrationEpoch"] scopeJson)
  IO.ofExcept (requireExactFields "fn claim"
    ["sourceIdentity", "messageId", "groups"] claimJson)
  IO.ofExcept (requireExactFields "consumer policy"
    ["application", "subject", "target", "capability"] policyJson)
  let parsedPin : FnPortablePin ← IO.ofExcept (fromJson? pinJson)
  let pin := match execution with
    | some (binary, key) => parsedPin.withExecution binary key
    | none => parsedPin
  let scope : FnPollScopePin ← IO.ofExcept (fromJson? scopeJson)
  let claim : FnPortableClaim ← IO.ofExcept (fromJson? claimJson)
  let policySource : ConsumerPolicySource ← IO.ofExcept (fromJson? policyJson)
  let (cursor, event, projection, carrier, verified, extracted) ←
    verifyFnPollFiles pin scope claim cursorPath reportPath carrierPath
  unless event.length ≤ FnConsumerOperation.maxStoreEventBytes do
    throw (IO.userError "fn report exceeds Mini's first bounded Store inbox profile")
  let receipt ← IO.ofExcept (← FnEvidence.verify origin extracted.package)
  let originPackage ← IO.ofExcept (FnEvidenceCodec.decodeChecked extracted.package)
  unless originPackage.originalReceipt == receipt do
    throw (IO.userError "poll source Mini receipt differs from re-admitted package")
  let policy := policySource.policy
  let probeTarget : DeclaredResourceController.Target :=
    ⟨.object, policy.target, policy.capability, 1, ⟨0⟩,
      .content ⟨[]⟩, none, none, none⟩
  let targetRoot ← IO.ofExcept <| (do
    let .present cell := opened.directory.directory.slots policy.target
      | throw "poll consumer target is absent"
    let some pre := DeclaredResourceController.selectTarget
      config.deployment probeTarget cell
      | throw "poll consumer target is not a valid content resource"
    pure pre.root : Except String Minidregg.Theory.TypedAuthorization.Digest)
  let report := pollConsumerReport policy
    targetRoot verified carrier extracted.package originPackage
    cursor event projection controlBinding
  let decision ← IO.ofExcept (FnConsumerOperation.evaluateVerified config
    gateway policy report receipt opened)
  writeJson resultPath <| Lean.Json.mkObj
    [("type", toJson "fn-poll-consumer-decision-v1"),
     ("portableAuthorship", toJson "verified"),
     ("storeAdmission", toJson (if controlBinding.isSome then
      "observed-control-poll" else "unestablished-from-files")),
     ("sourceIdentity", toJson
       (Minidregg.Host.Json.encodeHex projection.sourceIdentity)),
     ("storeSequence", toJson (toString projection.sequence)),
     ("storeTransactionId", toJson (toString projection.transactionId)),
     ("application", toJson policySource.application),
     ("operation", toJson (String.fromUTF8! report.operation.toByteArray)),
     ("miniOrigin", evidenceReceiptJson receipt),
     ("decision", consumerDecisionJson decision)]
  match decision.intent report with
  | some intent =>
      writeBytes intentPath (NativeObservationCodec.intentCodec.encode intent)
      pure 0
  | none =>
      match decision with
      | .refused _ => pure 1
      | _ => pure 0

def runPollConsumerDecision (config : NativeHost.Config)
    (controlBinding : Option (String × String))
    (originPath pinPath scopePath claimPath policyPath cursorPath reportPath
     carrierPath intentPath resultPath : String) : IO UInt32 := do
  let opened ← IO.ofExcept (← NativeHost.openExisting config)
  runPollConsumerDecisionLoaded config opened controlBinding originPath pinPath
    scopePath claimPath policyPath cursorPath reportPath carrierPath intentPath resultPath

/-- A's observed local Q poll is admitted only after independently reopening
the original R Mini package. The fn projection supplies Store history; the
native hybrid verifier supplies exact portable authorship. -/
def runReplyConsumerPollDecisionLoaded (config : NativeHost.Config)
    (opened : NativeHost.Opened config)
    (originPath rPinPath rClaimPath rCarrierPath qPinPath scopePath qClaimPath
     policyPath controlPath cursorPath reportPath carrierPath intentPath
     resultPath : String)
    (preObserved : Option (List UInt8 × List UInt8) := none)
    (execution : Option ((String × String) × (String × String)) := none) : IO UInt32 := do
  let gateway ← requireGateway config
  let origin := (← loadSettings originPath).config
  let rPinJson ← readJson rPinPath
  let rClaimJson ← readJson rClaimPath
  let qPinJson ← readJson qPinPath
  let scopeJson ← readJson scopePath
  let qClaimJson ← readJson qClaimPath
  let policyJson ← readJson policyPath
  for (label, value) in [("R fn pin", rPinJson), ("Q fn pin", qPinJson)] do
    IO.ofExcept (requireExactFields label
      ["fnBinary", "mlPublicKey", "principal", "edPublicKey", "mlPublicKeyHex"] value)
  for (label, value) in [("R fn claim", rClaimJson), ("Q fn claim", qClaimJson)] do
    IO.ofExcept (requireExactFields label ["sourceIdentity", "messageId", "groups"] value)
  IO.ofExcept (requireExactFields "A fn scope"
    ["history", "incarnation", "consumer", "principal", "query",
     "queryVersion", "viewVersion", "registrationEpoch"] scopeJson)
  IO.ofExcept (requireExactFields "A reply policy"
    ["application", "subject", "target", "capability"] policyJson)
  let parsedRPin : FnPortablePin ← IO.ofExcept (fromJson? rPinJson)
  let rClaim : FnPortableClaim ← IO.ofExcept (fromJson? rClaimJson)
  let parsedQPin : FnPortablePin ← IO.ofExcept (fromJson? qPinJson)
  let (rPin, qPin) := match execution with
    | some ((rBinary, rKey), (qBinary, qKey)) =>
        (parsedRPin.withExecution rBinary rKey,
         parsedQPin.withExecution qBinary qKey)
    | none => (parsedRPin, parsedQPin)
  let scope : FnPollScopePin ← IO.ofExcept (fromJson? scopeJson)
  let qClaim : FnPortableClaim ← IO.ofExcept (fromJson? qClaimJson)
  let policySource : ConsumerPolicySource ← IO.ofExcept (fromJson? policyJson)
  let (_, rVerified, rExtracted) ← verifyFnPortable rPin rClaim rCarrierPath
  let originReceipt ← IO.ofExcept (← FnEvidence.verify origin rExtracted.package)
  let originPackage ← IO.ofExcept (FnEvidenceCodec.decodeChecked rExtracted.package)
  unless originPackage.originalReceipt == originReceipt do
    throw (IO.userError "R package receipt differs from Mini's re-admitted origin")
  let (cursor, event) ← match preObserved with
    | some observed => pure observed
    | none => do
        let (cursor, event, _) ← invokeFnConsumerPoll qPin.executable scope
          controlPath cursorPath reportPath carrierPath
        pure (cursor, event)
  let (projectedCursor, projectedEvent, projection) ←
    projectFnPoll qPin.executable scope cursorPath reportPath
  unless cursor == projectedCursor && sameBytes event projectedEvent do
    throw (IO.userError "A fn poll changed before Mini projection")
  let (carrier, verified) ← verifyFnCarrier qPin qClaim carrierPath
  let extracted ← IO.ofExcept (FnReplySource.extract verified.source)
  unless sameBytes projection.received carrier &&
      sameBytes projection.source verified.source &&
      projection.sourceIdentity == verified.sourceIdentity &&
      projection.verdictPrincipal == verified.principal &&
      projection.messageId == extracted.messageId.toUTF8.toList &&
      qClaim.messageId == extracted.messageId &&
      qClaim.groups == extracted.creation.newsgroup do
    throw (IO.userError "A historical verdict differs from exact native Q carrier")
  let policy := policySource.policy
  let probeTarget : DeclaredResourceController.Target :=
    ⟨.object, policy.target, policy.capability, 1, ⟨0⟩,
      .content ⟨[]⟩, none, none, none⟩
  let targetRoot ← IO.ofExcept <| (do
    let .present cell := opened.directory.directory.slots policy.target
      | throw "A reply consumer target is absent"
    let some pre := DeclaredResourceController.selectTarget
      config.deployment probeTarget cell
      | throw "A reply consumer target is not a valid content resource"
    pure pre.root : Except String Minidregg.Theory.TypedAuthorization.Digest)
  let storePoll : FnConsumerOperation.StorePollInbox :=
    ⟨cursor, event, true, projection.sourceIdentity, projection.sequence,
      projection.transactionId, projection.messageId,
      projection.verdictPrincipal, projection.verdictEvent,
      FnConsumerOperation.pollControlBinding qPin.fnBinary controlPath⟩
  let report : FnReplyConsumption.Report :=
    ⟨policy.application, FnConsumerOperation.originOperation originPackage,
      rVerified.sourceIdentity, rExtracted.messageId.toUTF8.toList,
      originReceipt, verified.source, verified.sourceIdentity,
      extracted.messageId.toUTF8.toList,
      ⟨carrier, verified.sourceIdentity, verified.principal,
        verified.edPublicKey, verified.mlPublicKey⟩, storePoll,
      policy.subject, policy.target, policy.capability,
      targetRoot⟩
  let decision ← IO.ofExcept (FnReplyConsumption.evaluateVerified config opened
    gateway ⟨policy.application, policy.subject,
      policy.target, policy.capability⟩ report)
  let verdict := match decision with
    | .fresh _ _ => "proposed-fresh"
    | .repeated _ => "repeated"
    | .conflict _ => "proposed-conflict"
    | .conflictRecorded => "conflict-recorded"
    | .refused _ => "refused"
  writeJson resultPath <| Lean.Json.mkObj
    [("type", toJson "fn-a-reply-consumer-decision-v1"),
     ("decision", toJson verdict),
     ("operation", toJson (String.fromUTF8! report.operation.toByteArray)),
     ("qSourceIdentity", toJson
       (Minidregg.Host.Json.encodeHex verified.sourceIdentity)),
     ("fnStoreSequence", toJson (toString projection.sequence)),
     ("fnStoreTransactionId", toJson (toString projection.transactionId)),
     ("miniOrigin", evidenceReceiptJson originReceipt)]
  match decision.intent report with
  | some intent =>
      writeBytes intentPath (NativeObservationCodec.intentCodec.encode intent)
      pure 0
  | none =>
      match decision with
      | .refused _ => pure 1
      | _ => pure 0

def runReplyConsumerPollDecision (config : NativeHost.Config)
    (originPath rPinPath rClaimPath rCarrierPath qPinPath scopePath qClaimPath
     policyPath controlPath cursorPath reportPath carrierPath intentPath
     resultPath : String) : IO UInt32 := do
  let opened ← IO.ofExcept (← NativeHost.openExisting config)
  runReplyConsumerPollDecisionLoaded config opened originPath rPinPath rClaimPath
    rCarrierPath qPinPath scopePath qClaimPath policyPath controlPath cursorPath
    reportPath carrierPath intentPath resultPath

/-- An A poll of its own R is neutral only when the exact native-projected
article joins one accepted local prepared outbox. Fresh progress re-admits
the origin Mini package. Historical ACK reopens both accepted A records and
re-verifies both native carriers without requiring the origin Store anew.
The fn poll transport, rather than these portable bytes, establishes that the
article came from this selected Store. -/
def verifyCatalogOwnR (config : NativeHost.Config)
    (opened : NativeHost.Opened config) (service : FnReplyCatalogService)
    (projection : FnPollProjection) (carrierPath : String)
    (readmitOrigin : Bool) :
    IO (FnOriginOutbox.Prepared × DurableReceiver.IntentRecord) := do
  let gateway ← requireGateway config
  let rPinJson ← readJson service.rPinPath
  IO.ofExcept (requireExactFields "R fn catalog pin"
    ["fnBinary", "mlPublicKey", "principal", "edPublicKey", "mlPublicKeyHex"] rPinJson)
  let rawPin : FnPortablePin ← IO.ofExcept (fromJson? rPinJson)
  let rPin := rawPin.withExecution service.rExecutable service.rPublicKey
  let (received, observed) ← verifyFnCarrierUnclaimed rPin carrierPath
  let observedR ← IO.ofExcept (FnPortableSource.extract observed.source)
  unless sameBytes received projection.received &&
      sameBytes observed.source projection.source &&
      observed.sourceIdentity == projection.sourceIdentity &&
      observed.principal == projection.verdictPrincipal &&
      observedR.messageId.toUTF8.toList == projection.messageId do
    throw (IO.userError "A own-R poll differs from native verified article")
  let (prepared, record) ← IO.ofExcept <|
    FnOriginOutbox.selectUniqueParent gateway config.deployment.domain
      config.profile.semantics projection.messageId opened.durable.image.accepted
  unless fnOwnRCarrierMatches received prepared.carrier do
    throw (IO.userError "A own-R poll differs from exact accepted R carrier or fn injection")
  let (retainedVerified, retainedR, original) ←
    IO.FS.withTempDir fun directory => do
      let path := (directory / "accepted-r-carrier.eml").toString
      writeBytes path prepared.carrier
      if readmitOrigin then
        let (_, verified, extracted, package, receipt) ←
          verifyRLocalOrigin service.originConfig rPin path
        pure (verified, extracted, some (package, receipt))
      else
        let (_, verified) ← verifyFnCarrierUnclaimed rPin path
        let extracted ← IO.ofExcept (FnPortableSource.extract verified.source)
        pure (verified, extracted, none)
  unless sameBytes retainedVerified.source observed.source &&
      retainedVerified.sourceIdentity == observed.sourceIdentity &&
      retainedVerified.principal == observed.principal &&
      retainedVerified.edPublicKey == observed.edPublicKey &&
      retainedVerified.mlPublicKey == observed.mlPublicKey &&
      retainedR.messageId == observedR.messageId &&
      retainedR.groups == observedR.groups &&
      prepared.messageId == projection.messageId &&
      prepared.sourceIdentity == observed.sourceIdentity &&
      prepared.principal == observed.principal &&
      prepared.edPublicKey == observed.edPublicKey &&
      prepared.mlPublicKey == observed.mlPublicKey do
    throw (IO.userError "A own-R poll differs from accepted prepared R origin")
  if let some (originPackage, originReceipt) := original then
    unless prepared.operation == FnConsumerOperation.originOperation originPackage &&
        prepared.originReceipt == originReceipt &&
        prepared.packageIdentity == FnOriginOutbox.packageIdentity retainedR.package &&
        prepared.originCallIdentity == FnOriginOutbox.callIdentity originPackage.signedCall do
      throw (IO.userError "A own-R poll differs from re-admitted Mini origin")
  return (prepared, record)

/-- A non-Q first matching article advances A only after Mini has accepted a
separate tag-9 record. The qualified fn poll's first-match scan means every
earlier event in this at-most-16-event window is neutral for the selected
group; no matching Q can be hidden behind this own R. -/
def runCatalogOwnRDecisionLoaded (config : NativeHost.Config)
    (opened : NativeHost.Opened config) (service : FnReplyCatalogService)
    (fnBinary : String) (scope : FnPollScopePin) (before : FnConsumerStatus)
    (cursorPath reportPath carrierPath : String)
    (cursor event : List UInt8) (projection : FnPollProjection) :
    IO (UInt8 × List UInt8) := do
  let gateway ← requireGateway config
  let (prepared, outbox) ← verifyCatalogOwnR config opened service projection carrierPath true
  let (inspectedScope, position) ←
    inspectFnConsumerCursor service.qExecutable cursorPath
  let selectedScope ← IO.ofExcept scope.progressScope
  let after ← queryFnConsumerStatus service.qExecutable scope service.controlPath
  unless inspectedScope == selectedScope &&
      before.committedAck == after.committedAck &&
      position == projection.sequence + 1 &&
      before.committedAck < position &&
      position ≤ before.committedAck + FnConsumerProgress.maxPollScan &&
      position ≤ after.frontier &&
      cursor == (← readBoundedBytes cursorPath 346) &&
      sameBytes event (← readBoundedBytes reportPath FnEvidenceCodec.maxStorePollEventBytes) &&
      sameBytes projection.received
        (← readBoundedBytes carrierPath FnEvidenceCodec.maxCarrierBytes) do
    throw (IO.userError "A own-R poll did not cover one unchanged first-match scan window")
  let policyJson ← readJson service.policyPath
  IO.ofExcept (requireExactFields "A fn catalog policy"
    ["application", "subject", "target", "capability"] policyJson)
  let policySource : ConsumerPolicySource ← IO.ofExcept (fromJson? policyJson)
  let policy := policySource.policy
  let targetRoot ← gatewayContentTargetRoot config opened policy
  let portable : FnConsumerOperation.PortableInbox :=
    ⟨projection.received, projection.sourceIdentity, prepared.principal,
      prepared.edPublicKey, prepared.mlPublicKey⟩
  let poll : FnConsumerOperation.StorePollInbox :=
    ⟨cursor, event, true, projection.sourceIdentity, projection.sequence,
      projection.transactionId, projection.messageId,
      projection.verdictPrincipal, projection.verdictEvent,
      FnConsumerOperation.pollControlBinding fnBinary service.controlPath⟩
  let evidence : FnCatalogOwnRProgress.Evidence :=
    ⟨policy.application, selectedScope, before.committedAck, position,
      outbox.transactionId, portable, poll⟩
  let report : FnCatalogOwnRProgress.Report :=
    ⟨evidence, policy.subject, policy.target, policy.capability,
      targetRoot⟩
  let decision ← IO.ofExcept (FnCatalogOwnRProgress.evaluateVerified config
    gateway policy selectedScope report opened)
  let (decisionName, intent) ← match decision with
    | .fresh _ =>
        let some authored := decision.intent report
          | throw (IO.userError "fresh own-R progress has no Mini intent")
        pure ("proposed-fresh", Minidregg.Host.Json.encodeHex
          (NativeObservationCodec.intentCodec.encode authored))
    | .repeated => pure ("repeated", "")
    | .refused _ => pure ("refused", "")
  return (14, (Lean.Json.mkObj
    [("type", toJson "fn-a-reply-poll-session-v1"),
     ("status", toJson (if decisionName == "refused" then "refused" else "skip-decision")),
     ("decision", Lean.Json.mkObj
       [("type", toJson "fn-a-own-r-progress-decision-v1"),
        ("decision", toJson decisionName),
        ("fromPosition", toJson (toString before.committedAck)),
        ("toPosition", toJson (toString position)),
        ("outboxTransactionId", toJson (toString outbox.transactionId.value))]),
     ("intentHex", toJson intent)]).compress.toUTF8.toList)

/-- Q selects its R parent only after a real authenticated fn poll and native
hybrid verification of Q. The selected R comes from A's accepted Mini outbox;
its retained carrier and exact locally accepted origin package are verified
again before admitting the A reply result. -/
def runReplyConsumerCatalogDecisionLoaded (config : NativeHost.Config)
    (opened : NativeHost.Opened config) (service : FnReplyCatalogService)
    (qClaimPath cursorPath reportPath carrierPath intentPath resultPath : String)
    (observed : List UInt8 × List UInt8) : IO UInt32 := do
  let gateway ← requireGateway config
  let rPinJson ← readJson service.rPinPath
  let qPinJson ← readJson service.qPinPath
  let scopeJson ← readJson service.scopePath
  let qClaimJson ← readJson qClaimPath
  let policyJson ← readJson service.policyPath
  for (label, value) in [("R fn pin", rPinJson), ("Q fn pin", qPinJson)] do
    IO.ofExcept (requireExactFields label
      ["fnBinary", "mlPublicKey", "principal", "edPublicKey", "mlPublicKeyHex"] value)
  IO.ofExcept (requireExactFields "Q fn claim"
    ["sourceIdentity", "messageId", "groups"] qClaimJson)
  IO.ofExcept (requireExactFields "A fn scope"
    ["history", "incarnation", "consumer", "principal", "query",
     "queryVersion", "viewVersion", "registrationEpoch"] scopeJson)
  IO.ofExcept (requireExactFields "A reply policy"
    ["application", "subject", "target", "capability"] policyJson)
  let rawRPin : FnPortablePin ← IO.ofExcept (fromJson? rPinJson)
  let rawQPin : FnPortablePin ← IO.ofExcept (fromJson? qPinJson)
  let rPin := rawRPin.withExecution service.rExecutable service.rPublicKey
  let qPin := rawQPin.withExecution service.qExecutable service.qPublicKey
  let scope : FnPollScopePin ← IO.ofExcept (fromJson? scopeJson)
  let qClaim : FnPortableClaim ← IO.ofExcept (fromJson? qClaimJson)
  let policySource : ConsumerPolicySource ← IO.ofExcept (fromJson? policyJson)
  let policy := policySource.policy
  let (cursor, event) := observed
  let (projectedCursor, projectedEvent, projection) ←
    projectFnPoll qPin.executable scope cursorPath reportPath
  unless cursor == projectedCursor && sameBytes event projectedEvent do
    throw (IO.userError "A fn poll changed before outbox parent selection")
  let (qCarrier, qVerified) ← verifyFnCarrier qPin qClaim carrierPath
  let qExtracted ← IO.ofExcept (FnReplySource.extract qVerified.source)
  unless sameBytes projection.received qCarrier &&
      sameBytes projection.source qVerified.source &&
      projection.sourceIdentity == qVerified.sourceIdentity &&
      projection.verdictPrincipal == qVerified.principal &&
      projection.messageId == qExtracted.messageId.toUTF8.toList &&
      qClaim.messageId == qExtracted.messageId &&
      qClaim.groups == qExtracted.creation.newsgroup do
    throw (IO.userError "A Q projection differs from exact native-verified reply")
  let (prepared, _) ← IO.ofExcept (FnOriginOutbox.selectUniqueParent gateway
    config.deployment.domain config.profile.semantics
    qExtracted.parentMessageId.toUTF8.toList opened.durable.image.accepted)
  let (rCarrier, rVerified, rExtracted, originPackage, originReceipt) ←
    IO.FS.withTempDir fun directory => do
      let path := (directory / "retained-r-carrier.eml").toString
      writeBytes path prepared.carrier
      verifyRLocalOrigin service.originConfig rPin path
  unless sameBytes rCarrier prepared.carrier &&
      rVerified.sourceIdentity == prepared.sourceIdentity &&
      rVerified.principal == prepared.principal &&
      rVerified.edPublicKey == prepared.edPublicKey &&
      rVerified.mlPublicKey == prepared.mlPublicKey &&
      rExtracted.messageId.toUTF8.toList == prepared.messageId &&
      qExtracted.parentMessageId == rExtracted.messageId &&
      FnConsumerOperation.originOperation originPackage == prepared.operation &&
      originReceipt == prepared.originReceipt &&
      FnOriginOutbox.packageIdentity rExtracted.package == prepared.packageIdentity &&
      FnOriginOutbox.callIdentity originPackage.signedCall == prepared.originCallIdentity do
    throw (IO.userError "selected R outbox differs from exact retained native/local origin")
  let targetRoot ← gatewayContentTargetRoot config opened policy
  let storePoll : FnConsumerOperation.StorePollInbox :=
    ⟨cursor, event, true, projection.sourceIdentity, projection.sequence,
      projection.transactionId, projection.messageId,
      projection.verdictPrincipal, projection.verdictEvent,
      FnConsumerOperation.pollControlBinding qPin.fnBinary service.controlPath⟩
  let report : FnReplyConsumption.Report :=
    ⟨policy.application, FnConsumerOperation.originOperation originPackage,
      rVerified.sourceIdentity, rExtracted.messageId.toUTF8.toList,
      originReceipt, qVerified.source, qVerified.sourceIdentity,
      qExtracted.messageId.toUTF8.toList,
      ⟨qCarrier, qVerified.sourceIdentity, qVerified.principal,
        qVerified.edPublicKey, qVerified.mlPublicKey⟩, storePoll,
      policy.subject, policy.target, policy.capability,
      targetRoot⟩
  let decision ← IO.ofExcept (FnReplyConsumption.evaluateVerified config opened
    gateway ⟨policy.application, policy.subject,
      policy.target, policy.capability⟩ report)
  let verdict := match decision with
    | .fresh _ _ => "proposed-fresh"
    | .repeated _ => "repeated"
    | .conflict _ => "proposed-conflict"
    | .conflictRecorded => "conflict-recorded"
    | .refused _ => "refused"
  writeJson resultPath <| Lean.Json.mkObj
    [("type", toJson "fn-a-reply-consumer-decision-v1"),
     ("decision", toJson verdict),
     ("operation", toJson (String.fromUTF8! report.operation.toByteArray)),
     ("qSourceIdentity", toJson
       (Minidregg.Host.Json.encodeHex qVerified.sourceIdentity)),
     ("fnStoreSequence", toJson (toString projection.sequence)),
     ("fnStoreTransactionId", toJson (toString projection.transactionId)),
     ("miniOrigin", evidenceReceiptJson originReceipt)]
  match decision.intent report with
  | some intent =>
      writeBytes intentPath (NativeObservationCodec.intentCodec.encode intent)
      pure 0
  | none =>
      match decision with
      | .refused _ => pure 1
      | _ => pure 0

def runFnEmptyPageDecisionLoaded (config : NativeHost.Config)
    (opened : NativeHost.Opened config) (policyPath controlPath : String)
    (scope : FnPollScopePin) (fnBinary : String)
    (cursor : List UInt8) (fromPosition toPosition : Nat)
    (operation : UInt8) (responseType : String) :
    IO (UInt8 × List UInt8) := do
  let gateway ← requireGateway config
  let policyJson ← readJson policyPath
  IO.ofExcept (requireExactFields "consumer policy"
    ["application", "subject", "target", "capability"] policyJson)
  let policySource : ConsumerPolicySource ← IO.ofExcept (fromJson? policyJson)
  let policy := policySource.policy
  let selectedScope ← IO.ofExcept scope.progressScope
  let probeTarget : DeclaredResourceController.Target :=
    ⟨.object, policy.target, policy.capability, 1, ⟨0⟩,
      .content ⟨[]⟩, none, none, none⟩
  let targetRoot ← IO.ofExcept <| (do
    let .present cell := opened.directory.directory.slots policy.target
      | throw "empty-page consumer target is absent"
    let some pre := DeclaredResourceController.selectTarget
      config.deployment probeTarget cell
      | throw "empty-page consumer target is not a valid content resource"
    pure pre.root : Except String Minidregg.Theory.TypedAuthorization.Digest)
  let evidence : FnConsumerProgress.Evidence :=
    ⟨policy.application, selectedScope, cursor, fromPosition, toPosition,
      FnConsumerOperation.pollControlBinding fnBinary controlPath, true⟩
  let report : FnConsumerProgress.Report :=
    ⟨evidence, policy.subject, policy.target, policy.capability,
      targetRoot⟩
  let decision ← IO.ofExcept (FnConsumerProgress.evaluateVerified config
    gateway policy selectedScope report opened)
  let (decisionName, intent) ← match decision with
    | .fresh _ =>
        let some authored := decision.intent report
          | throw (IO.userError "fresh empty-page decision has no intent")
        pure ("proposed-fresh", Minidregg.Host.Json.encodeHex
          (NativeObservationCodec.intentCodec.encode authored))
    | .repeated => pure ("repeated", "")
    | .refused _ => pure ("refused", "")
  return (operation, (Lean.Json.mkObj
    [("type", toJson responseType),
     ("status", toJson (if decisionName == "refused" then "refused" else "skip-decision")),
     ("decision", Lean.Json.mkObj
       [("type", toJson "fn-empty-page-progress-decision-v1"),
        ("decision", toJson decisionName),
        ("fromPosition", toJson (toString fromPosition)),
        ("toPosition", toJson (toString toPosition))]),
     ("intentHex", toJson intent)]).compress.toUTF8.toList)

/-- A typed live fn poll. All paths come from the operator manifest or a
private temporary directory. The frame has no path, fn helper, policy or
claim fields; the claim is derived from the exact ACL2-projected source. -/
def runFnPollSession (config : NativeHost.Config)
    (state : IO.Ref (Option (NativeHostSession.Session config)))
    (service : FnPollService) (payload : List UInt8) : IO (UInt8 × List UInt8) := do
  unless payload.isEmpty do throw (IO.userError "fn consumer poll does not accept a payload")
  IO.FS.withTempDir fun directory => do
    let pinJson ← readJson service.fnPinPath
    let scopeJson ← readJson service.scopePath
    IO.ofExcept (requireExactFields "fn service pin"
      ["fnBinary", "mlPublicKey", "principal", "edPublicKey", "mlPublicKeyHex"] pinJson)
    IO.ofExcept (requireExactFields "fn service scope"
      ["history", "incarnation", "consumer", "principal", "query",
       "queryVersion", "viewVersion", "registrationEpoch"] scopeJson)
    let rawPin : FnPortablePin ← IO.ofExcept (fromJson? pinJson)
    let pin := rawPin.withExecution service.fnExecutable service.fnPublicKey
    let scope : FnPollScopePin ← IO.ofExcept (fromJson? scopeJson)
    let cursorPath := (directory / "cursor.fncu").toString
    let reportPath := (directory / "report.fn-e").toString
    let carrierPath := (directory / "carrier.eml").toString
    let claimPath := (directory / "claim.json").toString
    let intentPath := (directory / "intent.bin").toString
    let resultPath := (directory / "decision.json").toString
    let before ← queryFnConsumerStatus pin.executable scope service.controlPath
    let (polledCursor, polledEvent) ← invokeFnConsumerPollRaw pin.executable scope
      service.controlPath cursorPath reportPath
    if polledEvent.isEmpty then
      let empty ← classifyFnEmptyPoll pin.executable scope service.controlPath
        cursorPath reportPath polledCursor before
      match empty with
      | none =>
          return idleFnPollResponse 12 "fn-consumer-poll-session-v1"
            before.committedAck
      | some (fromPosition, toPosition) =>
          let opened ← sessionOpened config state
          return ← runFnEmptyPageDecisionLoaded config opened
            service.policyPath service.controlPath scope pin.fnBinary
            polledCursor fromPosition toPosition 12 "fn-consumer-poll-session-v1"
    let (_, projectedEvent, projection) ←
      projectFnPoll pin.executable scope cursorPath reportPath
    unless sameBytes projectedEvent polledEvent do
      throw (IO.userError "fn poll event changed before projection")
    IO.FS.writeBinFile carrierPath projection.received.toByteArray
    let polledCarrier := projection.received
    let extracted ← IO.ofExcept (FnPortableSource.extract projection.source)
    let claim := Lean.Json.mkObj
      [("sourceIdentity", toJson (Minidregg.Host.Json.encodeHex projection.sourceIdentity)),
       ("messageId", toJson extracted.messageId),
       ("groups", toJson extracted.groups)]
    writeJson claimPath claim
    let opened ← sessionOpened config state
    let exitCode ← runPollConsumerDecisionLoaded config opened
      (some (pin.fnBinary, service.controlPath)) service.originConfigPath
      service.fnPinPath service.scopePath claimPath service.policyPath
      cursorPath reportPath carrierPath intentPath resultPath
      (some (service.fnExecutable, service.fnPublicKey))
    unless polledCursor == (← readBoundedBytes cursorPath 346) &&
        sameBytes polledEvent (← readBoundedBytes reportPath FnEvidenceCodec.maxStorePollEventBytes) &&
        sameBytes polledCarrier (← readBoundedBytes carrierPath FnEvidenceCodec.maxCarrierBytes) do
      throw (IO.userError "fn poll output changed before Mini decision completed")
    let decision ← readJson resultPath
    let intent ← if ← (System.FilePath.mk intentPath).pathExists then do
        pure (Minidregg.Host.Json.encodeHex (← readBoundedBytes intentPath maxFrame))
      else pure ""
    return (12, (Lean.Json.mkObj
      [("type", toJson "fn-consumer-poll-session-v1"),
       ("status", toJson (if exitCode == 0 then "accepted-decision" else "refused")),
       ("decision", decision), ("intentHex", toJson intent)]).compress.toUTF8.toList)

/-- A previously admitted empty-page skip retains its exact fn cursor. ACK
never needs a current Mini mutation grant, but fn still checks its own scoped
cursor and durable position through the local control endpoint. -/
def coveredSkipAckResponse (operation : UInt8) (responseType transaction : String)
    (skipped : FnConsumerProgress.Evidence) (committedAck : Nat) :
    UInt8 × List UInt8 :=
  (operation, (Lean.Json.mkObj
    [("type", toJson responseType),
     ("kind", toJson "empty-page-skip"),
     ("miniTransactionId", toJson transaction),
     ("fnCursorPosition", toJson (toString skipped.toPosition)),
     ("fnCommittedAck", toJson (toString committedAck)),
     ("fnStoreSequence", toJson ""),
     ("fnStoreTransactionId", toJson ""),
     ("fnAck", toJson "covered-by-durable-frontier")]).compress.toUTF8.toList)

/-- Position-only coverage of a signed historical article inbox. This says
the scoped durable ACK frontier now lies past its cursor; it does not claim a
fresh carrier verification or identify which earlier ACK advanced the Store. -/
def coveredArticleAckResponse (operation : UInt8) (responseType transaction : String)
    (stored : FnConsumerOperation.StorePollInbox) (position committedAck : Nat) :
    UInt8 × List UInt8 :=
  (operation, (Lean.Json.mkObj
    [("type", toJson responseType),
     ("kind", toJson "article-prefix-coverage"),
     ("miniTransactionId", toJson transaction),
     ("fnCursorPosition", toJson (toString position)),
     ("fnCommittedAck", toJson (toString committedAck)),
     ("fnStoreSequence", toJson (toString stored.sequence)),
     ("fnStoreTransactionId", toJson (toString stored.transactionId)),
     ("fnAck", toJson "covered-by-durable-frontier")]).compress.toUTF8.toList)

def runFnSkipAckSession (pin : FnPortablePin) (scope : FnPollScopePin)
    (controlPath transaction : String) (skipped : FnConsumerProgress.Evidence)
    (operation : UInt8) (responseType : String) : IO (UInt8 × List UInt8) := do
  unless skipped.controlBinding ==
      FnConsumerOperation.pollControlBinding pin.fnBinary controlPath do
    throw (IO.userError "empty-page ACK control differs from accepted Mini skip")
  IO.FS.withTempDir fun directory => do
    let cursorPath := (directory / "retained-skip.fncu").toString
    writeBytes cursorPath skipped.cursor
    let (inspectedScope, position) ←
      inspectFnConsumerCursor pin.executable cursorPath
    let selectedScope ← IO.ofExcept scope.progressScope
    unless inspectedScope == selectedScope && position == skipped.toPosition &&
        skipped.cursor == (← readBoundedBytes cursorPath 346) do
      throw (IO.userError "empty-page ACK cursor differs from accepted Mini skip")
    let (currentPosition, currentStatus) ←
      queryFnConsumerPosition pin.executable scope controlPath
    if currentPosition ≥ skipped.toPosition &&
        currentStatus.committedAck > skipped.toPosition then
      return coveredSkipAckResponse operation responseType transaction skipped
        currentStatus.committedAck
    let child ← IO.Process.spawn
      { cmd := pin.executable,
        args := #["--fn", "consumer", "ack", controlPath, cursorPath],
        stdin := .null, stdout := .piped, stderr := .null }
    let output ← try readBoundedLoop child.stdout 128
      catch error =>
        child.kill
        discard <| child.wait
        throw error
    let exitCode ← child.wait
    unless skipped.cursor == (← readBoundedBytes cursorPath 346) do
      throw (IO.userError "empty-page ACK cursor changed during local call")
    let status := if exitCode == 0 && output == "consumer accepted\n".toUTF8.toList then
        "durable-accepted"
      else if exitCode == 2 then "refused"
      else if exitCode == 3 then "uncertain"
      else "transport-fault"
    if status == "refused" then
      let (latestPosition, latestStatus) ←
        queryFnConsumerPosition pin.executable scope controlPath
      if latestPosition ≥ skipped.toPosition &&
          latestStatus.committedAck > skipped.toPosition then
        return coveredSkipAckResponse operation responseType transaction skipped
          latestStatus.committedAck
    let mut committedAck := currentStatus.committedAck
    if status == "durable-accepted" then
      let after ← queryFnConsumerStatus pin.executable scope controlPath
      unless skipped.toPosition ≤ after.committedAck do
        throw (IO.userError "fn accepted skip ACK without durable position advance")
      committedAck := after.committedAck
    return (operation, (Lean.Json.mkObj
      [("type", toJson responseType),
       ("kind", toJson "empty-page-skip"),
       ("miniTransactionId", toJson transaction),
       ("fnCursorPosition", toJson (toString skipped.toPosition)),
       ("fnCommittedAck", toJson (toString committedAck)),
       ("fnStoreSequence", toJson ""),
       ("fnStoreTransactionId", toJson ""),
       ("fnAck", toJson status)]).compress.toUTF8.toList)

/-- A typed acknowledgement only for an original accepted Mini operation.
The request names that transaction, never a cursor or fn pathname. An
uncertain fn reply leaves the exact retained operation available for retry. -/
def runFnAckSession (config : NativeHost.Config)
    (state : IO.Ref (Option (NativeHostSession.Session config)))
    (service : FnPollService) (payload : List UInt8) : IO (UInt8 × List UInt8) := do
  unless !payload.isEmpty && payload.length ≤ 80 &&
      payload.all (fun byte => 48 ≤ byte.toNat && byte.toNat ≤ 57) do
    throw (IO.userError "fn ack transaction ID must be bounded decimal ASCII")
  let transaction ← pure (String.fromUTF8! payload.toByteArray)
  let transactionId ← IO.ofExcept (exactDecimal "Mini transaction ID" transaction)
  let pinJson ← readJson service.fnPinPath
  let scopeJson ← readJson service.scopePath
  IO.ofExcept (requireExactFields "fn service pin"
    ["fnBinary", "mlPublicKey", "principal", "edPublicKey", "mlPublicKeyHex"] pinJson)
  IO.ofExcept (requireExactFields "fn service scope"
    ["history", "incarnation", "consumer", "principal", "query",
     "queryVersion", "viewVersion", "registrationEpoch"] scopeJson)
  let rawPin : FnPortablePin ← IO.ofExcept (fromJson? pinJson)
  let pin := rawPin.withExecution service.fnExecutable service.fnPublicKey
  let scope : FnPollScopePin ← IO.ofExcept (fromJson? scopeJson)
  let gateway ← requireGateway config
  let opened ← sessionOpened config state
  let some record := opened.durable.image.accepted.find?
      (fun entry => entry.transactionId.value == transactionId)
    | throw (IO.userError "fn ack Mini transaction is absent")
  let selectedScope ← IO.ofExcept scope.progressScope
  if let some skipped := FnConsumerProgress.originalSkip gateway selectedScope
      config.deployment.domain config.profile.semantics record then
    return ← runFnSkipAckSession pin scope service.controlPath transaction skipped
      13 "fn-consumer-ack-session-v1"
  let some (_, some portable, some stored) :=
      FnConsumerOperation.originalBindingWithInbox gateway config.deployment.domain
        config.profile.semantics record
    | throw (IO.userError "fn ack Mini transaction has no canonical accepted inbox")
  unless stored.pollCallObserved && stored.controlBinding ==
      FnConsumerOperation.pollControlBinding pin.fnBinary service.controlPath do
    throw (IO.userError "fn ack control endpoint differs from observed poll")
  IO.FS.withTempDir fun directory => do
    let cursorPath := (directory / "retained-cursor.fncu").toString
    let eventPath := (directory / "retained-report.fn-e").toString
    writeBytes cursorPath stored.cursor
    writeBytes eventPath stored.event
    let (oldScope, oldPosition) ← inspectFnConsumerCursor pin.executable cursorPath
    unless oldScope == selectedScope && oldPosition == stored.sequence + 1 &&
        stored.cursor == (← readBoundedBytes cursorPath 346) do
      throw (IO.userError "fn ack retained cursor differs from signed Mini position")
    let (currentPosition, currentStatus) ←
      queryFnConsumerPosition pin.executable scope service.controlPath
    if currentPosition ≥ oldPosition && currentStatus.committedAck > oldPosition then
      return coveredArticleAckResponse 13 "fn-consumer-ack-session-v1"
        transaction stored oldPosition currentStatus.committedAck
    let (cursor, event, projected) ←
      projectFnPoll pin.executable scope cursorPath eventPath
    unless cursor == stored.cursor && sameBytes event stored.event &&
        projected.sourceIdentity == stored.sourceIdentity &&
        projected.sequence == stored.sequence &&
        projected.transactionId == stored.transactionId &&
        projected.messageId == stored.messageId &&
        projected.verdictPrincipal == stored.verdictPrincipal &&
        projected.verdictEvent == stored.verdictEvent do
      throw (IO.userError "fn ack cursor/report differ from accepted Mini inbox")
    let verified ← verifyAckSource pin projected portable.carrier projected.source
    unless verified.principal == portable.principal &&
        verified.sourceIdentity == portable.sourceIdentity &&
        verified.edPublicKey == portable.edPublicKey &&
        verified.mlPublicKey == portable.mlPublicKey &&
        projected.verdictPrincipal == portable.principal do
      throw (IO.userError "fn ack source differs from accepted Mini inbox")
    let child ← IO.Process.spawn
      { cmd := pin.executable,
        args := #["--fn", "consumer", "ack", service.controlPath, cursorPath],
        stdin := .null, stdout := .piped, stderr := .null }
    let output ← try readBoundedLoop child.stdout 128
      catch error =>
        child.kill
        discard <| child.wait
        throw error
    let exitCode ← child.wait
    unless cursor == (← readBoundedBytes cursorPath 346) &&
        sameBytes event (← readBoundedBytes eventPath FnEvidenceCodec.maxStorePollEventBytes) do
      throw (IO.userError "fn ack inputs changed during local control call")
    let status := if exitCode == 0 && output == "consumer accepted\n".toUTF8.toList then
        "durable-accepted"
      else if exitCode == 2 then "refused"
      else if exitCode == 3 then "uncertain"
      else "transport-fault"
    if status == "refused" then
      let (latestPosition, latestStatus) ←
        queryFnConsumerPosition pin.executable scope service.controlPath
      if latestPosition ≥ oldPosition && latestStatus.committedAck > oldPosition then
        return coveredArticleAckResponse 13 "fn-consumer-ack-session-v1"
          transaction stored oldPosition latestStatus.committedAck
    return (13, (Lean.Json.mkObj
      [("type", toJson "fn-consumer-ack-session-v1"),
       ("miniTransactionId", toJson transaction),
       ("fnStoreSequence", toJson (toString stored.sequence)),
       ("fnStoreTransactionId", toJson (toString stored.transactionId)),
       ("fnAck", toJson status)]).compress.toUTF8.toList)

/-- Record one locally prepared R in A's accepted Mini outbox. The request is
only the bounded carrier bytes; the fn verifier key, origin Mini, gateway and
target policy all come from the operator's pinned lifetime service. The
returned intent still needs the gateway signature and normal Mini admission. -/
def runFnOriginOutboxSession (config : NativeHost.Config)
    (state : IO.Ref (Option (NativeHostSession.Session config)))
    (service : FnReplyCatalogService) (payload : List UInt8) :
    IO (UInt8 × List UInt8) := do
  unless !payload.isEmpty && payload.length ≤ FnEvidenceCodec.maxCarrierBytes do
    throw (IO.userError "prepared R carrier exceeds bounded outbox input")
  let pinJson ← readJson service.rPinPath
  let policyJson ← readJson service.policyPath
  IO.ofExcept (requireExactFields "R fn catalog pin"
    ["fnBinary", "mlPublicKey", "principal", "edPublicKey", "mlPublicKeyHex"] pinJson)
  IO.ofExcept (requireExactFields "A outbox policy"
    ["application", "subject", "target", "capability"] policyJson)
  let rawPin : FnPortablePin ← IO.ofExcept (fromJson? pinJson)
  let pin := rawPin.withExecution service.rExecutable service.rPublicKey
  let policySource : ConsumerPolicySource ← IO.ofExcept (fromJson? policyJson)
  let policy := policySource.policy
  let gateway ← requireGateway config
  IO.FS.withTempDir fun directory => do
    let carrierPath := (directory / "prepared-r-carrier.eml").toString
    writeBytes carrierPath payload
    let (carrier, verified, extracted, package, receipt) ←
      verifyRLocalOrigin service.originConfig pin carrierPath
    unless sameBytes carrier payload do
      throw (IO.userError "prepared R carrier changed during local verification")
    let opened ← sessionOpened config state
    let targetRoot ← gatewayContentTargetRoot config opened policy
    let prepared : FnOriginOutbox.Prepared :=
      ⟨policy.application, FnConsumerOperation.originOperation package,
        extracted.messageId.toUTF8.toList, verified.sourceIdentity, carrier,
        FnOriginOutbox.packageIdentity extracted.package,
        FnOriginOutbox.callIdentity package.signedCall, receipt,
        verified.principal, verified.edPublicKey, verified.mlPublicKey⟩
    let report : FnOriginOutbox.Report :=
      ⟨prepared, extracted.package, policy.subject, policy.target,
        policy.capability, targetRoot,
        true, true⟩
    let decision ← IO.ofExcept (FnOriginOutbox.evaluateVerified config opened
      gateway policy report)
    let (verdict, intent) := match decision with
      | .fresh _ => ("proposed-fresh", decision.intent report)
      | .repeated => ("repeated", none)
      | .refused _ => ("refused", none)
    let intentHex := match intent with
      | some authored => Minidregg.Host.Json.encodeHex
          (NativeObservationCodec.intentCodec.encode authored)
      | none => ""
    return (16, (Lean.Json.mkObj
      [("type", toJson "fn-a-origin-outbox-session-v1"),
       ("status", toJson (if verdict == "refused" then "refused" else "prepared-decision")),
       ("decision", toJson verdict),
       ("messageId", toJson extracted.messageId),
       ("sourceIdentity", toJson
         (Minidregg.Host.Json.encodeHex verified.sourceIdentity)),
       ("miniOrigin", evidenceReceiptJson receipt),
       ("intentHex", toJson intentHex)]).compress.toUTF8.toList)

/-- Reopen the exact accepted tag-10 publication preparation. The local
gateway signature and full original command shape were checked at admission;
historical export does not require a grant that may since have been revoked.
No carrier or verifier path comes from this request. -/
def runFnOriginOutboxExportSession (config : NativeHost.Config)
    (state : IO.Ref (Option (NativeHostSession.Session config)))
    (payload : List UInt8) : IO (UInt8 × List UInt8) := do
  unless !payload.isEmpty && payload.length ≤ 80 &&
      payload.all (fun byte => 48 ≤ byte.toNat && byte.toNat ≤ 57) do
    throw (IO.userError "prepared R export transaction ID must be bounded decimal ASCII")
  let transaction := String.fromUTF8! payload.toByteArray
  let transactionId ← IO.ofExcept (exactDecimal "Mini transaction ID" transaction)
  let gateway ← requireGateway config
  let opened ← sessionOpened config state
  let refused := fun (reason : String) =>
    (18, (Lean.Json.mkObj
      [("type", toJson "fn-a-origin-outbox-export-v1"),
       ("status", toJson "refused"), ("reason", toJson reason)]).compress.toUTF8.toList)
  let some record := opened.durable.image.accepted.find?
      (fun entry => entry.transactionId.value == transactionId)
    | return refused "prepared R transaction is absent"
  let some prepared := FnOriginOutbox.originalPrepared gateway
      config.deployment.domain config.profile.semantics record
    | return refused "transaction is not an accepted prepared R outbox"
  let some outboxReceipt := NativeHost.historicalReceipt config opened.durable
      record.transactionId record.event.eventId
    | return refused "prepared R original receipt is unavailable"
  let some messageId := String.fromUTF8? prepared.messageId.toByteArray
    | return refused "prepared R Message-ID is not UTF-8"
  return (18, (Lean.Json.mkObj
    [("type", toJson "fn-a-origin-outbox-export-v1"),
     ("status", toJson "accepted"),
     ("transactionId", toJson transaction),
     ("messageId", toJson messageId),
     ("sourceIdentity", toJson
       (Minidregg.Host.Json.encodeHex prepared.sourceIdentity)),
     ("carrierHex", toJson (Minidregg.Host.Json.encodeHex prepared.carrier)),
     ("packageIdentity", toJson (toString prepared.packageIdentity.value)),
     ("originCallIdentity", toJson (toString prepared.originCallIdentity.value)),
     ("miniOrigin", evidenceReceiptJson prepared.originReceipt),
     ("miniOutbox", evidenceReceiptJson outboxReceipt)]).compress.toUTF8.toList)

/-- Select exactly one configured provider from the signed command's actual
targets. A caller-supplied provider label cannot choose a continuity cell. -/
def providerFromReserveCall (providerIds : List Nat) (reserveCall : List UInt8) :
    Except String Nat := do
  let some (.invoke signed) := NativeHostCodec.callCodec.decode reserveCall
    | throw "reserve call is not a canonical signed invocation"
  let some command := DeclaredResourceController.commandCodec.decode signed.commandBytes
    | throw "reserve call has no canonical signed command"
  match command.targets.filter (fun target => providerIds.contains target.target) with
  | [target] => return target.target
  | _ => throw "reserve call must target exactly one configured provider service"

/-- A current, read-only check of one originally confirmed provider reserve.
The caller supplies its retained canonical call and outcome bytes; the
provider resource ID comes from that signed call and the operator service list.
This check does not lease the provider resource across a later external send. -/
def runProviderContinuitySession (config : NativeHost.Config)
    (state : IO.Ref (Option (NativeHostSession.Session config)))
    (providerIds : List Nat) (payload : List UInt8) :
    IO (UInt8 × List UInt8) := do
  -- Legacy/v2 request bytes remain compatible. v3 additionally proves the
  -- original observation root at its historical index, never just a counter.
  let continuityPrefix := "DREGG/PROVIDER-CONTINUITY/v2".toUTF8.toList ++ [0]
  let prefixV3 := "DREGG/PROVIDER-CONTINUITY/v3".toUTF8.toList ++ [0]
  let (body, priorChecked) ← if payload.take prefixV3.length == prefixV3 then do
      let (body, priorBytes) ← splitPair (payload.drop prefixV3.length)
      unless !priorBytes.isEmpty && priorBytes.length ≤ 1024 do
        throw (RequestRefusal.malformed "v3 continuity needs a bounded prior checked point")
      let (countBytes, rootBytes) ← splitPair priorBytes
      let some countText := String.fromUTF8? countBytes.toByteArray
        | throw (RequestRefusal.malformed "prior checked count is not UTF-8")
      let some rootText := String.fromUTF8? rootBytes.toByteArray
        | throw (RequestRefusal.malformed "prior checked root is not UTF-8")
      let count ← IO.ofExcept (exactDecimal "prior checked count" countText)
      let root ← IO.ofExcept (exactDecimal "prior checked root" rootText)
      pure (some body, some ({ acceptedCount := count, worldRoot := ⟨root⟩ } :
        NativeProviderHistory.PriorChecked))
    else if payload.take continuityPrefix.length == continuityPrefix then
      pure (some (payload.drop continuityPrefix.length), none)
    else
      pure (none, none)
  let (reservePair, fencePair) ← match body with
    | none => pure (payload, [])
    | some bytes => splitPair bytes
  let (reserveCall, outcomeBytes) ← splitPair reservePair
  unless !reserveCall.isEmpty && !outcomeBytes.isEmpty &&
      outcomeBytes.length ≤ 1024 do
    throw (IO.userError "provider continuity needs bounded original call and outcome")
  let allowedFence ← if fencePair.isEmpty then
      pure (none : Option (List UInt8 × NativeHostCodec.Receipt))
    else do
      let (fenceCall, fenceOutcome) ← splitPair fencePair
      unless !fenceCall.isEmpty && !fenceOutcome.isEmpty && fenceOutcome.length ≤ 1024 do
        throw (IO.userError "provider continuity needs complete bounded fence evidence")
      let some (.confirmed _ receipt) := outcomeCodec.decode fenceOutcome
        | throw (IO.userError "provider fence outcome is not canonical confirmation")
      pure (some (fenceCall, receipt))
  let providerResourceId ← IO.ofExcept <|
    providerFromReserveCall providerIds reserveCall
  let some (.confirmed _ anchor) := outcomeCodec.decode outcomeBytes
    | throw (IO.userError "provider continuity outcome is not canonical confirmation")
  let current ← sessionWalked config state
  let providerCell : DurableDataIntent.CellId := ⟨providerResourceId⟩
  let checkedWorldRoot := (current.target.worldRoot).value
  let checkedCount := current.target.image.accepted.length
  let continuity : Except String Unit := match allowedFence with
    | none => (NativeReserveContinuity.check current anchor reserveCall providerCell).map (fun _ => ())
    | some (fenceCall, fenceReceipt) =>
        (NativeProviderHistory.check current anchor fenceReceipt reserveCall fenceCall providerCell).map
          (fun _ => ())
  let verdict := continuity.bind fun _ => match priorChecked with
    | none => Except.ok ()
    | some point => (NativeProviderHistory.checkPrior current anchor.acceptedCount point).map (fun _ => ())
  let (continuous, reason) := match verdict with
    | .ok _ => (true, "")
    | .error detail => (false, detail)
  return (17, (Lean.Json.mkObj
    [("type", toJson "minidregg-provider-continuity-v1"),
     ("status", toJson (if continuous then "confirmed" else "refused")),
     ("continuous", toJson continuous),
     ("providerResourceId", toJson (toString providerResourceId)),
     ("anchor", evidenceReceiptJson anchor),
     ("allowedFence", match allowedFence with
       | none => Lean.Json.null
       | some (_, receipt) => evidenceReceiptJson receipt),
     ("priorChecked", match priorChecked with
       | none => Lean.Json.null
       | some point => Lean.Json.mkObj
           [("acceptedCount", toJson (toString point.acceptedCount)),
            ("worldRoot", toJson (toString point.worldRoot.value))]),
     ("checkedWorldRoot", toJson (toString checkedWorldRoot)),
     ("checkedAcceptedCount", toJson (toString checkedCount)),
     ("reason", toJson reason)]).compress.toUTF8.toList)

/-- The A reply poll uses one operator-pinned R carrier and a live Q control
endpoint. The request carries no paths, claims, or verifier selection. -/
def runFnReplyPollSession (config : NativeHost.Config)
    (state : IO.Ref (Option (NativeHostSession.Session config)))
    (service : FnReplyPollService) (payload : List UInt8) :
    IO (UInt8 × List UInt8) := do
  unless payload.isEmpty do
    throw (IO.userError "A reply poll does not accept a payload")
  IO.FS.withTempDir fun directory => do
    let cursorPath := (directory / "cursor.fncu").toString
    let reportPath := (directory / "report.fn-e").toString
    let carrierPath := (directory / "q-carrier.eml").toString
    let claimPath := (directory / "q-claim.json").toString
    let intentPath := (directory / "intent.bin").toString
    let resultPath := (directory / "decision.json").toString
    let pinJson ← readJson service.qPinPath
    let scopeJson ← readJson service.scopePath
    IO.ofExcept (requireExactFields "Q fn service pin"
      ["fnBinary", "mlPublicKey", "principal", "edPublicKey", "mlPublicKeyHex"] pinJson)
    IO.ofExcept (requireExactFields "A fn service scope"
      ["history", "incarnation", "consumer", "principal", "query",
       "queryVersion", "viewVersion", "registrationEpoch"] scopeJson)
    let rawPin : FnPortablePin ← IO.ofExcept (fromJson? pinJson)
    let pin := rawPin.withExecution service.qExecutable service.qPublicKey
    let scope : FnPollScopePin ← IO.ofExcept (fromJson? scopeJson)
    let before ← queryFnConsumerStatus pin.executable scope service.controlPath
    let (polledCursor, polledEvent) ← invokeFnConsumerPollRaw pin.executable scope
      service.controlPath cursorPath reportPath
    if polledEvent.isEmpty then
      let empty ← classifyFnEmptyPoll pin.executable scope service.controlPath
        cursorPath reportPath polledCursor before
      match empty with
      | none =>
          return idleFnPollResponse 14 "fn-a-reply-poll-session-v1"
            before.committedAck
      | some (fromPosition, toPosition) =>
          let opened ← sessionOpened config state
          return ← runFnEmptyPageDecisionLoaded config opened
            service.policyPath service.controlPath scope pin.fnBinary
            polledCursor fromPosition toPosition 14 "fn-a-reply-poll-session-v1"
    let (_, projectedEvent, projection) ←
      projectFnPoll pin.executable scope cursorPath reportPath
    unless sameBytes projectedEvent polledEvent do
      throw (IO.userError "A fn poll event changed before projection")
    IO.FS.writeBinFile carrierPath projection.received.toByteArray
    let extracted ← IO.ofExcept (FnReplySource.extract projection.source)
    writeJson claimPath (Lean.Json.mkObj
      [("sourceIdentity", toJson
        (Minidregg.Host.Json.encodeHex projection.sourceIdentity)),
       ("messageId", toJson extracted.messageId),
       ("groups", toJson extracted.creation.newsgroup)])
    let opened ← sessionOpened config state
    let exitCode ← runReplyConsumerPollDecisionLoaded config opened
      service.originConfigPath service.rPinPath service.rClaimPath
      service.rCarrierPath service.qPinPath service.scopePath
      claimPath service.policyPath service.controlPath
      cursorPath reportPath carrierPath intentPath resultPath
      (some (polledCursor, polledEvent))
      (some ((service.rExecutable, service.rPublicKey),
        (service.qExecutable, service.qPublicKey)))
    unless polledCursor == (← readBoundedBytes cursorPath 346) &&
        sameBytes polledEvent
          (← readBoundedBytes reportPath FnEvidenceCodec.maxStorePollEventBytes) &&
        sameBytes projection.received
          (← readBoundedBytes carrierPath FnEvidenceCodec.maxCarrierBytes) do
      throw (IO.userError "A fn poll output changed before Mini decision completed")
    let decision ← readJson resultPath
    let intent ← if ← (System.FilePath.mk intentPath).pathExists then do
        pure (Minidregg.Host.Json.encodeHex (← readBoundedBytes intentPath maxFrame))
      else pure ""
    return (14, (Lean.Json.mkObj
      [("type", toJson "fn-a-reply-poll-session-v1"),
       ("status", toJson (if exitCode == 0 then "accepted-decision" else "refused")),
       ("decision", decision), ("intentHex", toJson intent)]).compress.toUTF8.toList)

/-- Long-lived A poll: derive the Q claim from the one live fn projection,
then resolve its parent from the refreshed admitted Mini outbox. -/
def runFnReplyCatalogPollSession (config : NativeHost.Config)
    (state : IO.Ref (Option (NativeHostSession.Session config)))
    (service : FnReplyCatalogService) (payload : List UInt8) :
    IO (UInt8 × List UInt8) := do
  unless payload.isEmpty do
    throw (IO.userError "A reply catalog poll does not accept a payload")
  IO.FS.withTempDir fun directory => do
    let cursorPath := (directory / "cursor.fncu").toString
    let reportPath := (directory / "report.fn-e").toString
    let carrierPath := (directory / "q-carrier.eml").toString
    let claimPath := (directory / "q-claim.json").toString
    let intentPath := (directory / "intent.bin").toString
    let resultPath := (directory / "decision.json").toString
    let pinJson ← readJson service.qPinPath
    let scopeJson ← readJson service.scopePath
    IO.ofExcept (requireExactFields "Q fn catalog pin"
      ["fnBinary", "mlPublicKey", "principal", "edPublicKey", "mlPublicKeyHex"] pinJson)
    IO.ofExcept (requireExactFields "A fn catalog scope"
      ["history", "incarnation", "consumer", "principal", "query",
       "queryVersion", "viewVersion", "registrationEpoch"] scopeJson)
    let rawPin : FnPortablePin ← IO.ofExcept (fromJson? pinJson)
    let pin := rawPin.withExecution service.qExecutable service.qPublicKey
    let scope : FnPollScopePin ← IO.ofExcept (fromJson? scopeJson)
    let before ← queryFnConsumerStatus pin.executable scope service.controlPath
    let (polledCursor, polledEvent) ← invokeFnConsumerPollRaw pin.executable scope
      service.controlPath cursorPath reportPath
    if polledEvent.isEmpty then
      let empty ← classifyFnEmptyPoll pin.executable scope service.controlPath
        cursorPath reportPath polledCursor before
      match empty with
      | none =>
          return idleFnPollResponse 14 "fn-a-reply-poll-session-v1"
            before.committedAck
      | some (fromPosition, toPosition) =>
          let opened ← sessionOpened config state
          return ← runFnEmptyPageDecisionLoaded config opened
            service.policyPath service.controlPath scope pin.fnBinary
            polledCursor fromPosition toPosition 14 "fn-a-reply-poll-session-v1"
    let (_, projectedEvent, projection) ←
      projectFnPoll pin.executable scope cursorPath reportPath
    unless sameBytes projectedEvent polledEvent do
      throw (IO.userError "A fn poll event changed before outbox projection")
    IO.FS.writeBinFile carrierPath projection.received.toByteArray
    let opened ← sessionOpened config state
    let extracted ← match FnReplySource.extract projection.source with
      | .ok q => pure q
      | .error _ =>
          return ← runCatalogOwnRDecisionLoaded config opened service pin.fnBinary scope before
            cursorPath reportPath carrierPath polledCursor polledEvent projection
    writeJson claimPath (Lean.Json.mkObj
      [("sourceIdentity", toJson
        (Minidregg.Host.Json.encodeHex projection.sourceIdentity)),
       ("messageId", toJson extracted.messageId),
       ("groups", toJson extracted.creation.newsgroup)])
    let exitCode ← runReplyConsumerCatalogDecisionLoaded config opened service
      claimPath cursorPath reportPath carrierPath intentPath resultPath
      (polledCursor, polledEvent)
    unless polledCursor == (← readBoundedBytes cursorPath 346) &&
        sameBytes polledEvent
          (← readBoundedBytes reportPath FnEvidenceCodec.maxStorePollEventBytes) &&
        sameBytes projection.received
          (← readBoundedBytes carrierPath FnEvidenceCodec.maxCarrierBytes) do
      throw (IO.userError "A fn poll output changed before catalog decision")
    let decision ← readJson resultPath
    let intent ← if ← (System.FilePath.mk intentPath).pathExists then do
        pure (Minidregg.Host.Json.encodeHex (← readBoundedBytes intentPath maxFrame))
      else pure ""
    return (14, (Lean.Json.mkObj
      [("type", toJson "fn-a-reply-poll-session-v1"),
       ("status", toJson (if exitCode == 0 then "accepted-decision" else "refused")),
       ("decision", decision), ("intentHex", toJson intent)]).compress.toUTF8.toList)

def FnReplyCatalogService.ackService (service : FnReplyCatalogService) :
    FnReplyPollService :=
  ⟨"", "", "", "", "", "", service.qPinPath,
    service.qExecutable, service.qPublicKey, service.scopePath,
    service.policyPath, service.controlPath⟩

/-- Settle only a previously accepted own-R progress record. Reopen the exact
poll pair and accepted prepared R; no caller-supplied cursor can advance fn. -/
def runCatalogOwnRAckSession (config : NativeHost.Config)
    (opened : NativeHost.Opened config) (service : FnReplyCatalogService)
    (pin : FnPortablePin) (scope : FnPollScopePin) (transaction : String)
    (evidence : FnCatalogOwnRProgress.Evidence) : IO (UInt8 × List UInt8) := do
  unless evidence.poll.controlBinding ==
      FnConsumerOperation.pollControlBinding pin.fnBinary service.controlPath do
    throw (IO.userError "A own-R ACK control differs from accepted Mini poll")
  IO.FS.withTempDir fun directory => do
    let cursorPath := (directory / "retained-own-r-cursor.fncu").toString
    let eventPath := (directory / "retained-own-r-event.fn-e").toString
    let carrierPath := (directory / "retained-own-r-carrier.eml").toString
    writeBytes cursorPath evidence.poll.cursor
    writeBytes eventPath evidence.poll.event
    writeBytes carrierPath evidence.portable.carrier
    let (inspectedScope, position) ← inspectFnConsumerCursor pin.executable cursorPath
    let selectedScope ← IO.ofExcept scope.progressScope
    unless inspectedScope == selectedScope && position == evidence.toPosition &&
        evidence.poll.sequence + 1 == position do
      throw (IO.userError "A own-R ACK cursor differs from accepted Mini progress")
    let (cursor, event, projection) ← projectFnPoll pin.executable scope
      cursorPath eventPath
    unless cursor == evidence.poll.cursor && sameBytes event evidence.poll.event &&
        projection.sourceIdentity == evidence.poll.sourceIdentity &&
        projection.sequence == evidence.poll.sequence &&
        projection.transactionId == evidence.poll.transactionId &&
        projection.messageId == evidence.poll.messageId &&
        projection.verdictPrincipal == evidence.poll.verdictPrincipal &&
        sameBytes projection.verdictEvent evidence.poll.verdictEvent &&
        sameBytes projection.received evidence.portable.carrier do
      throw (IO.userError "A own-R ACK pair differs from accepted Mini progress")
    let (_, outbox) ← verifyCatalogOwnR config opened service projection carrierPath false
    unless outbox.transactionId == evidence.outboxTransaction do
      throw (IO.userError "A own-R ACK selected a different accepted outbox")
    let response := fun (status : String) (committedAck : Nat) =>
      ((15 : UInt8), (Lean.Json.mkObj
        [("type", toJson "fn-a-reply-ack-session-v1"),
         ("kind", toJson "own-r-skip"),
         ("miniTransactionId", toJson transaction),
         ("outboxTransactionId", toJson (toString evidence.outboxTransaction.value)),
         ("fnCursorPosition", toJson (toString position)),
         ("fnCommittedAck", toJson (toString committedAck)),
         ("fnStoreSequence", toJson (toString evidence.poll.sequence)),
         ("fnStoreTransactionId", toJson (toString evidence.poll.transactionId)),
         ("fnAck", toJson status)]).compress.toUTF8.toList)
    let (currentPosition, currentStatus) ←
      queryFnConsumerPosition pin.executable scope service.controlPath
    if currentPosition ≥ position && currentStatus.committedAck > position then
      return response "covered-by-durable-frontier" currentStatus.committedAck
    let child ← IO.Process.spawn
      { cmd := pin.executable,
        args := #["--fn", "consumer", "ack", service.controlPath, cursorPath],
        stdin := .null, stdout := .piped, stderr := .null }
    let output ← try readBoundedLoop child.stdout 128
      catch error =>
        child.kill
        discard <| child.wait
        throw error
    let exitCode ← child.wait
    unless evidence.poll.cursor == (← readBoundedBytes cursorPath 346) &&
        sameBytes evidence.poll.event
          (← readBoundedBytes eventPath FnEvidenceCodec.maxStorePollEventBytes) do
      throw (IO.userError "A own-R ACK inputs changed during local control call")
    let status := if exitCode == 0 && output == "consumer accepted\n".toUTF8.toList then
        "durable-accepted"
      else if exitCode == 2 then "refused"
      else if exitCode == 3 then "uncertain"
      else "transport-fault"
    if status == "refused" then
      let (latestPosition, latestStatus) ←
        queryFnConsumerPosition pin.executable scope service.controlPath
      if latestPosition ≥ position && latestStatus.committedAck > position then
        return response "covered-by-durable-frontier" latestStatus.committedAck
    let committedAck ← if status == "durable-accepted" then do
        let after ← queryFnConsumerStatus pin.executable scope service.controlPath
        unless position ≤ after.committedAck do
          throw (IO.userError "fn accepted own-R ACK without durable position advance")
        pure after.committedAck
      else pure currentStatus.committedAck
    return response status committedAck

/-- A reply ACK is selected by the accepted A Mini transaction alone. The
retained inbox supplies the exact cursor, event, carrier, and signed source. -/
def runFnReplyAckSession (config : NativeHost.Config)
    (state : IO.Ref (Option (NativeHostSession.Session config)))
    (service : FnReplyPollService) (catalog : Option FnReplyCatalogService)
    (payload : List UInt8) :
    IO (UInt8 × List UInt8) := do
  unless !payload.isEmpty && payload.length ≤ 80 &&
      payload.all (fun byte => 48 ≤ byte.toNat && byte.toNat ≤ 57) do
    throw (IO.userError "A reply ack transaction ID must be bounded decimal ASCII")
  let transaction := String.fromUTF8! payload.toByteArray
  let transactionId ← IO.ofExcept (exactDecimal "Mini transaction ID" transaction)
  let pinJson ← readJson service.qPinPath
  let scopeJson ← readJson service.scopePath
  IO.ofExcept (requireExactFields "Q fn pin"
    ["fnBinary", "mlPublicKey", "principal", "edPublicKey", "mlPublicKeyHex"] pinJson)
  IO.ofExcept (requireExactFields "A fn scope"
    ["history", "incarnation", "consumer", "principal", "query",
     "queryVersion", "viewVersion", "registrationEpoch"] scopeJson)
  let rawPin : FnPortablePin ← IO.ofExcept (fromJson? pinJson)
  let pin := rawPin.withExecution service.qExecutable service.qPublicKey
  let scope : FnPollScopePin ← IO.ofExcept (fromJson? scopeJson)
  let gateway ← requireGateway config
  let opened ← sessionOpened config state
  let some record := opened.durable.image.accepted.find?
      (fun entry => entry.transactionId.value == transactionId)
    | throw (IO.userError "A reply result transaction is absent")
  let selectedScope ← IO.ofExcept scope.progressScope
  if let some skipped := FnConsumerProgress.originalSkip gateway selectedScope
      config.deployment.domain config.profile.semantics record then
    return ← runFnSkipAckSession pin scope service.controlPath transaction skipped
      15 "fn-a-reply-ack-session-v1"
  if let some ownR := FnCatalogOwnRProgress.originalOwnR gateway selectedScope
      config.deployment.domain config.profile.semantics record
      opened.durable.image.accepted then
    let some selected := catalog
      | throw (IO.userError "A own-R ACK requires pinned catalog service")
    return ← runCatalogOwnRAckSession config opened selected pin scope transaction ownR
  let some (_, inbox) := FnReplyConsumption.originalResult gateway
      config.deployment.domain config.profile.semantics record
    | throw (IO.userError "A reply result is not a reopened accepted operation")
  let stored := inbox.storePoll
  unless stored.pollCallObserved && stored.controlBinding ==
      FnConsumerOperation.pollControlBinding pin.fnBinary service.controlPath do
    throw (IO.userError "A reply ack control differs from durable observed poll")
  IO.FS.withTempDir fun directory => do
    let cursorPath := (directory / "retained-cursor.fncu").toString
    let eventPath := (directory / "retained-report.fn-e").toString
    writeBytes cursorPath stored.cursor
    writeBytes eventPath stored.event
    let (oldScope, oldPosition) ← inspectFnConsumerCursor pin.executable cursorPath
    unless oldScope == selectedScope && oldPosition == stored.sequence + 1 &&
        stored.cursor == (← readBoundedBytes cursorPath 346) do
      throw (IO.userError "A reply ack retained cursor differs from signed Mini position")
    let (currentPosition, currentStatus) ←
      queryFnConsumerPosition pin.executable scope service.controlPath
    if currentPosition ≥ oldPosition && currentStatus.committedAck > oldPosition then
      return coveredArticleAckResponse 15 "fn-a-reply-ack-session-v1"
        transaction stored oldPosition currentStatus.committedAck
    let (cursor, event, projected) ←
      projectFnPoll pin.executable scope cursorPath eventPath
    unless cursor == stored.cursor && sameBytes event stored.event &&
        projected.sourceIdentity == stored.sourceIdentity &&
        projected.sequence == stored.sequence &&
        projected.transactionId == stored.transactionId &&
        projected.messageId == stored.messageId &&
        projected.verdictPrincipal == stored.verdictPrincipal &&
        projected.verdictEvent == stored.verdictEvent do
      throw (IO.userError "A reply ack pair differs from durable Mini inbox")
    let verified ← verifyReplyAckSource pin projected inbox.portableInbox.carrier
      inbox.replySource
    unless projected.verdictPrincipal == inbox.portableInbox.principal &&
        verified.principal == inbox.portableInbox.principal &&
        verified.edPublicKey == inbox.portableInbox.edPublicKey &&
        verified.mlPublicKey == inbox.portableInbox.mlPublicKey do
      throw (IO.userError "A reply ack source differs from accepted Mini inbox")
    let child ← IO.Process.spawn
      { cmd := pin.executable,
        args := #["--fn", "consumer", "ack", service.controlPath, cursorPath],
        stdin := .null, stdout := .piped, stderr := .null }
    let output ← try readBoundedLoop child.stdout 128
      catch error =>
        child.kill
        discard <| child.wait
        throw error
    let exitCode ← child.wait
    unless cursor == (← readBoundedBytes cursorPath 346) &&
        sameBytes event (← readBoundedBytes eventPath FnEvidenceCodec.maxStorePollEventBytes) do
      throw (IO.userError "A reply ack inputs changed during local control call")
    let status := if exitCode == 0 && output == "consumer accepted\n".toUTF8.toList then
        "durable-accepted"
      else if exitCode == 2 then "refused"
      else if exitCode == 3 then "uncertain"
      else "transport-fault"
    if status == "refused" then
      let (latestPosition, latestStatus) ←
        queryFnConsumerPosition pin.executable scope service.controlPath
      if latestPosition ≥ oldPosition && latestStatus.committedAck > oldPosition then
        return coveredArticleAckResponse 15 "fn-a-reply-ack-session-v1"
          transaction stored oldPosition latestStatus.committedAck
    return (15, (Lean.Json.mkObj
      [("type", toJson "fn-a-reply-ack-session-v1"),
       ("miniTransactionId", toJson transaction),
       ("fnStoreSequence", toJson (toString stored.sequence)),
       ("fnStoreTransactionId", toJson (toString stored.transactionId)),
       ("fnAck", toJson status)]).compress.toUTF8.toList)

def usage : String :=
"enroll-key-plan OBSERVED.bin COMMAND.bin PLAN.bin|enroll-key-assemble PLAN.bin SPONSOR-SIG.bin POSSESSION-SIG.bin NEXT.pub NEXT-SIG.bin INGRESS.bin|enroll-key-submit INGRESS.bin OUTCOME.bin|enroll-key-lookup INGRESS.bin OUTCOME.bin\n" ++
"inspect-agent-lifetime-paid-ingress PAID-PLAN.bin INGRESS.bin RESULT.json\ninspect-stop-claim STOP-PLAN.bin FRESH-COMMITTED-CLAIM.bin RESULT.json\nfn-frontier-request selected MINI-TX REQUEST.bin|fn-frontier-request empty - REQUEST.bin|fn-frontier-plan selected MINI-TX PLAN.bin CURSOR.fncu REPORT.fn-e SOURCE.eml|fn-frontier-plan empty - PLAN.bin CURSOR.fncu REPORT.fn-e SOURCE.eml|fn-frontier-export PLAN.bin CURSOR.fncu REPORT.fn-e SOURCE.eml|fn-frontier-assemble PLAN.bin RAW64-SIGNATURE.bin INGRESS.bin|fn-selected-poll-submit INGRESS.bin OUTCOME.bin|fn-selected-poll-lookup INGRESS.bin OUTCOME.bin|fn-empty-poll-submit INGRESS.bin OUTCOME.bin|fn-empty-poll-lookup INGRESS.bin OUTCOME.bin|fn-empty-page-ack CURSOR.fncu REPORT.fn-e COVERAGE19.bin RESULT.json\n" ++
"minidregg-host CONFIG.json profile|describe|stdio|author KIND INPUT.json OUTPUT.bin|inspect KIND INPUT.bin OUTPUT.json|law-sat REQUEST.json RESULT.json|derive grain INPUT.json OUTPUT.json|signatures INPUT.json OUTPUT.bin|genesis SOURCE-CONFIG.bin GENESIS.bin PINNED-CONFIG.json|bootstrap GENESIS.bin|checkpoint-differential HEIGHT|well-ledger LEDGER.json|pay-ledger LEDGER.json|pay-purse TASK PURSE.json|pay-job JOB JOB.json|job-money-explain COMMAND.bin|pay-enrol-probe INPUT.json OUTPUT.json|pay-enrol-ids MINI-KEY-HEX OUTPUT.json|challenge INTENT.bin INTENT-SIGNATURE.bin CHALLENGE.bin|observe-assemble CHALLENGE.bin SIGNATURES.bin SIGNED.bin PLAN.bin|prepare SIGNED.bin PLAN.bin|query SIGNED.bin VIEW.bin|pin-plan-height PLAN.bin PINNED-PLAN.bin|assemble PLAN.bin SIGNATURES.bin CALL.bin|submit CALL.bin OUTCOME.bin|lookup CALL.bin OUTCOME.bin|selected-release-submit INGRESS.bin OUTCOME.bin|selected-release-lookup INGRESS.bin OUTCOME.bin|application-lifecycle-begin-submit INGRESS.bin OUTCOME.bin|application-lifecycle-begin-lookup INGRESS.bin OUTCOME.bin|application-lifecycle-completion-submit INGRESS.bin OUTCOME.bin|application-lifecycle-completion-lookup INGRESS.bin OUTCOME.bin|diagnose-completion INGRESS.bin RESULT.json|selected-source-publication-submit INGRESS.bin OUTCOME.bin|selected-source-publication-lookup INGRESS.bin OUTCOME.bin|selected-release-source-plan PACKET.bin DELEGATE-CAP-DEC SPEC.bin HEADER.bin ROOT.txt|selected-release-source-assemble SPEC.bin HEADER.bin SIGNATURE.bin INGRESS.bin|selected-release-prepare REQUEST.json PREIMAGE.bin|selected-release-check-preimage PREIMAGE.bin CANONICAL.bin|selected-release-assemble PREIMAGE.bin SIGNATURE.bin FROM_MAILBOX DATE SUBJECT PACKET.bin ARTICLE.eml|selected-release-ingress PACKET.bin CAPABILITY_DEC TARGET_ROOT_DEC INGRESS.bin|selected-release-fn-poll FN-BINARY SCOPE.json CONTROL.sock CAPABILITY_DEC TARGET_ROOT_DEC CURSOR.fncu REPORT.fn-e SOURCE.eml PACKET.bin INGRESS.bin RESULT.json|selected-release-fn-ack CURSOR.fncu REPORT.fn-e MINI-TRANSACTION COVERAGE17.bin RESULT.json|export-evidence CALL.bin PACKAGE.bin|verify-evidence PACKAGE.bin RESULT.json|grain-origin-prepare REQUEST.json PACKAGE.bin OUTPUT_DIR|portable-verify-fn FN-PIN.json CLAIM.json CARRIER.eml SOURCE.bin PACKAGE.bin RESULT.json|consumer-verify-poll-files FN-PIN.json SCOPE-PIN.json CLAIM.json CURSOR.fncu REPORT.fn-e CARRIER.eml RESULT.json|portable-consumer-decide ORIGIN-PIN.json FN-PIN.json CLAIM.json POLICY.json CARRIER.eml INTENT.bin DECISION.json|poll-consumer-decide ORIGIN-PIN.json FN-PIN.json SCOPE-PIN.json CLAIM.json POLICY.json CURSOR.fncu REPORT.fn-e CARRIER.eml INTENT.bin DECISION.json|consumer-poll-decide ORIGIN-PIN.json FN-PIN.json SCOPE-PIN.json CLAIM.json POLICY.json CONTROL.sock CURSOR.fncu REPORT.fn-e CARRIER.eml INTENT.bin DECISION.json|consumer-export-inbox TRANSACTION-ID INBOX.bin CARRIER.eml RESULT.json|consumer-export-poll TRANSACTION-ID CURSOR.fncu REPORT.fn-e RESULT.json|consumer-ack-poll FN-PIN.json SCOPE-PIN.json CONTROL.sock MINI-TRANSACTION CURSOR.fncu REPORT.fn-e RESULT.json|reply-consumer-poll-decide ORIGIN-PIN.json R-FN-PIN.json R-CLAIM.json R-CARRIER.eml Q-FN-PIN.json A-SCOPE.json Q-CLAIM.json POLICY.json A-CONTROL.sock CURSOR.fncu REPORT.fn-e Q-CARRIER.eml INTENT.bin DECISION.json|reply-consumer-export-result MINI-TRANSACTION RESULT.bin INBOX.bin CURSOR.fncu REPORT.fn-e|reply-consumer-ack-poll Q-FN-PIN.json A-SCOPE.json A-CONTROL.sock MINI-TRANSACTION CURSOR.fncu REPORT.fn-e RESULT.json|consumer-export-reply TRANSACTION-ID REPLY.bin|consumer-stage-reply-plan SIGNER.json MINI-TRANSACTION OUTBOX_ROOT CANDIDATE.bin READBACK.bin SOURCE.eml RESULT.json|consumer-stage-reply-sign FN-PIN.json PRINCIPAL.bin ED-PUBLIC.bin ED-SECRET ML-SECRET MINI-TRANSACTION PLAN_ROOT SIGNED_ROOT PLAN-READBACK.bin SOURCE.eml CARRIER.eml SIGNED-CANDIDATE.bin SIGNED-READBACK.bin ED-SIG.bin ML-SIG.bin RESULT.json|consumer-decide-test ORIGIN-PIN.json POLICY.json REPORT.json PACKAGE.bin INTENT.bin DECISION.json"

def run (arguments : List String) : IO UInt32 := do
  match arguments with
  -- Pure operator authoring before any Store exists: the policy a genesis pins
  -- and the constants it names do not read the configuration.
  | [_, "objective-constants"] =>
      IO.println Minidregg.Host.ObjectiveInvocationQuote.constants.compress
      pure 0
  | [_, "author", "objective-policy", input, output] =>
      let bytes ← readBoundedBytes input 65536
      let some text := String.fromUTF8? bytes.toByteArray
        | throw (IO.userError "Objective policy JSON is not UTF-8")
      let json ← IO.ofExcept (Lean.Json.parse text)
      IO.FS.writeFile output (← IO.ofExcept (Minidregg.Host.ObjectiveInvocationQuote.authorPolicy json))
      pure 0
  | configPath :: command :: rest =>
      let settings ← loadSettings configPath
      let config := settings.config
      match command, rest with
      | "author", ["objective-request", input, output] =>
          let bytes ← readBoundedBytes input FnEvidenceCodec.maxHostFrameBytes
          let some text := String.fromUTF8? bytes.toByteArray
            | throw (IO.userError "Objective request JSON is not UTF-8")
          let json ← IO.ofExcept (Lean.Json.parse text)
          writeBytes output (← IO.ofExcept (Minidregg.Host.ObjectiveInvocationQuote.authorRequest json))
          pure 0
      | "objective-quote", [requestPath, intentNonce, outputPath] =>
          let bytes ← readBoundedBytes requestPath FnEvidenceCodec.maxHostFrameBytes
          let some nonce := intentNonce.toNat?
            | throw (IO.userError "intent nonce must be canonical decimal")
          unless toString nonce == intentNonce do throw (IO.userError "intent nonce must be canonical decimal")
          let walked ← IO.ofExcept (← NativeHostSession.startWalked config)
          writeJson outputPath (← IO.ofExcept
            (← Minidregg.Host.ObjectiveInvocationQuote.quoteBytes config walked.verified.opened bytes nonce))
          pure 0
      | "objective-publication", [packageInputPath, corePath, outputCodec, outputDirectory] =>
          let input ← readBoundedBytes packageInputPath 25165824
          let core ← readBoundedBytes corePath 4194304
          let result ← IO.ofExcept (Minidregg.Host.ObjectivePackageAuthor.publication input core outputCodec)
          let directory := System.FilePath.mk outputDirectory
          if ← directory.pathExists then throw (IO.userError "publication output directory already exists")
          IO.FS.createDirAll directory
          IO.FS.writeBinFile (directory / "package.bin") ⟨result.package.toArray⟩
          IO.FS.writeBinFile (directory / "artifact.bin") ⟨result.artifact.toArray⟩
          IO.FS.writeBinFile (directory / "core.canonical.json") ⟨result.core.toArray⟩
          IO.FS.writeFile (directory / "publication.json") result.json.compress
          IO.println result.json.compress
          pure 0
      | "carry-plan", [requestPath, outputPath] =>
          let operator ← carryOperator settings
          let request ← readCarryJson requestPath
          let result ← IO.ofExcept (← NeutralCarryReceiving.plan config configPath operator request)
          writeJson outputPath result
          pure 0
      | "carry-receive", [requestPath, edgePath, outputPath] =>
          let operator ← carryOperator settings
          let request ← readCarryJson requestPath
          let edge ← readCarryJson edgePath
          let result ← IO.ofExcept (← NeutralCarryReceiving.receive config configPath operator request edge)
          writeJson outputPath result
          pure 0
      | "carry-edge-verify", [requestPath, outputPath] =>
          let request ← readJson requestPath
          let result ← IO.ofExcept (← CarryInspection.verifyRequest config request)
          writeJson outputPath result
          pure 0
      | "continuity-point", [challengePath, outputPath] =>
          let challenge ← readJson challengePath
          let result ← IO.ofExcept (ReceiptContinuity.challengePointJson config challenge)
          writeJson outputPath result
          pure 0
      | "continuity-verify", [requestPath, responsePath, outputPath] =>
          let request ← readJson requestPath
          let response ← readJson responsePath
          let result ← IO.ofExcept (ReceiptContinuity.verifyJson config request response)
          writeJson outputPath result
          pure 0
      | "profile", [] =>
          IO.println (profileDescription config
            (← IO.ofExcept settings.providerMeteringPin)
            (← IO.ofExcept settings.providerServicePins)).pretty
          pure 0
      | "pay-claim-status", [input, output] =>
          let bytes ← readBoundedBytes input 4096
          let some text := String.fromUTF8? bytes.toByteArray
            | throw (IO.userError "paid status JSON is not UTF-8")
          let source ← IO.ofExcept (Minidregg.Host.Json.parse text)
          let walked ← IO.ofExcept (← NativeHostSession.startWalked config)
          writeJson output (← IO.ofExcept
            (Minidregg.Host.PayClaims.statusLoadedJson config walked.verified.opened source))
          pure 0
      | "pay-claim-audit", [input, output] =>
          let walked ← IO.ofExcept (← NativeHostSession.startWalked config)
          let requests ← IO.FS.Handle.mk input .read
          let results ← IO.FS.Handle.mk output .write
          let header ← IO.ofExcept
            (Minidregg.Host.PayClaims.auditHeaderJson config walked.verified.opened)
          results.putStrLn header.compress
          writePaidAuditRows config walked.verified.opened requests results
          pure 0
      | "pay-enrol-v2-context", [input, output] =>
          let bytes ← readBoundedBytes input 4096
          let some text := String.fromUTF8? bytes.toByteArray
            | throw (IO.userError "purchase context JSON is not UTF-8")
          let source ← IO.ofExcept (Minidregg.Host.Json.parse text)
          writeJson output (← IO.ofExcept (Minidregg.Host.PayClaims.purchaseContext config source))
          pure 0
      | "author", ["pay-claim-rotation", input, output] =>
          let bytes ← readBoundedBytes input 4096
          let some text := String.fromUTF8? bytes.toByteArray
            | throw (IO.userError "claim rotation JSON is not UTF-8")
          let source ← IO.ofExcept (Minidregg.Host.Json.parse text)
          writeBytes output (← IO.ofExcept (Minidregg.Host.PayClaims.authorRotation source))
          pure 0
      | "inspect", ["pay-claim-plan", input, output] =>
          let bytes ← readBoundedBytes input 3072
          writeJson output (← IO.ofExcept (Minidregg.Host.PayClaims.claimPlanJson bytes))
          pure 0
      | "inspect", ["pay-claim-command", input, output] =>
          let bytes ← readBoundedBytes input 2048
          writeJson output (← IO.ofExcept (Minidregg.Host.PayClaims.claimCommandJson bytes))
          pure 0
      | "inspect", ["pay-claim-ingress", input, output] =>
          let bytes ← readBoundedBytes input 4096
          writeJson output (← IO.ofExcept (Minidregg.Host.PayClaims.claimIngressJson config bytes))
          pure 0
      | "author", ["application-failed-start-report", input, output] =>
          let bytes ← readBoundedBytes input maxDispatchInspectionJsonBytes
          let some text := String.fromUTF8? bytes.toByteArray
            | throw (RequestRefusal.malformed "failed START report JSON is not UTF-8")
          let source ← IO.ofExcept (Lean.Json.parse text)
          writeBytes output (← IO.ofExcept (ApplicationFailedStartRecoveryTools.authorReport source))
          pure 0
      | "author", ["application-failed-start-signed-report", input, output] =>
          let bytes ← readBoundedBytes input maxDispatchInspectionJsonBytes
          let some text := String.fromUTF8? bytes.toByteArray
            | throw (RequestRefusal.malformed "failed START report JSON is not UTF-8")
          let source ← IO.ofExcept (Lean.Json.parse text)
          writeBytes output (← IO.ofExcept (ApplicationFailedStartRecoveryTools.authorSignedReport source))
          pure 0
      | "author", ["application-failed-start-recovery-request", input, output] =>
          let bytes ← readBoundedBytes input maxDispatchInspectionJsonBytes
          let some text := String.fromUTF8? bytes.toByteArray
            | throw (RequestRefusal.malformed "failed START report JSON is not UTF-8")
          let source ← IO.ofExcept (Lean.Json.parse text)
          writeBytes output (← IO.ofExcept (ApplicationFailedStartRecoveryTools.authorRequest source))
          pure 0
      | "author", [kind, input, output] =>
          let source ← if kind == "application-route-bound-dispatch" ||
              kind == "application-route-admission-request" ||
              kind == "application-route-admission-challenge" ||
              kind == "application-stream-continuity-request" ||
              kind == "application-stream-continuity-challenge" ||
              kind == "application-dispatch-request" ||
              kind == "application-share-issue-grain-request" ||
              kind == "application-lifecycle-launch-begin-request" ||
              kind == "application-lifecycle-launch-continue-request" ||
              kind == "application-lifecycle-launch-completion-request" ||
              kind == "application-lifecycle-launch-physical-report" ||
              kind == "application-lifecycle-launch-physical-signing-frame" ||
              kind == "application-lifecycle-launch-physical-signed-report" ||
              kind == "application-agent-lifetime-grant-request" ||
              kind == "application-session-enrollment-request" ||
              kind == "participant-key-enrollment" ||
              kind == "application-agent-lifetime-reserve-request" ||
              kind == "application-agent-lifetime-paid-request" then
            readDispatchAuthorJson input else readJson input
          let bytes ← IO.ofExcept (authorHost config (← IO.ofExcept settings.providerRoutes) kind source)
          writeBytes output bytes
          pure 0
      | "inspect", ["application-failed-start-report", input, output] =>
          let bytes ← readBoundedBytes input FnEvidenceCodec.maxHostFrameBytes
          writeJson output (← IO.ofExcept (ApplicationFailedStartRecoveryTools.inspectReport bytes))
          pure 0
      | "inspect", ["application-failed-start-recovery-plan", input, output] =>
          let bytes ← readBoundedBytes input FnEvidenceCodec.maxHostFrameBytes
          writeJson output (← IO.ofExcept (ApplicationFailedStartRecoveryInspection.inspectPlan bytes))
          pure 0
      | "inspect", ["application-failed-start-recovery-request", input, output] =>
          let bytes ← readBoundedBytes input FnEvidenceCodec.maxHostFrameBytes
          writeJson output (← IO.ofExcept (ApplicationFailedStartRecoveryInspection.inspectRequest bytes))
          pure 0
      | "inspect", [kind, input, output] =>
          let bytes ← if kind == "application-route-admission-attestation" ||
              kind == "application-stream-continuity-attestation" ||
              kind == "fn-inbox-resource" ||
              kind == "application-dispatch-committed" ||
              kind == "application-lifecycle-claim-committed-v2" ||
              kind == "application-lifecycle-claim-committed-v3" ||
              kind == "fn-consumer-namespace-plan" ||
              kind == "application-agent-reserve-plan" ||
              kind == "application-agent-paid-dispatch-plan" ||
              kind == "application-agent-dispatch-committed" ||
              kind == "application-agent-lifetime-reserve-request" ||
              kind == "application-agent-lifetime-paid-request" ||
              kind == "application-agent-lifetime-reserve-plan" ||
              kind == "application-agent-lifetime-paid-plan" ||
              kind == "application-agent-lifetime-dispatch-committed" ||
              kind == "application-lifecycle-launch-begin-request" ||
              kind == "application-lifecycle-launch-continue-request" ||
              kind == "application-lifecycle-launch-begin-plan" ||
              kind == "application-lifecycle-launch-stop-plan" ||
              kind == "application-lifecycle-launch-claim-request" ||
              kind == "application-lifecycle-launch-claim-plan" ||
              kind == "application-lifecycle-launch-completion-request" ||
              kind == "application-lifecycle-launch-completion-plan" ||
              kind == "application-lifecycle-launch-physical-report" ||
              kind == "application-lifecycle-launch-physical-signed-report" ||
              kind == "application-agent-lifetime-grant-request" ||
              kind == "application-agent-lifetime-grant-plan" ||
              kind == "application-session-enrollment-request" ||
              kind == "application-session-enrollment-plan" ||
              kind == "application-session-enrollment-ingress" ||
              kind == "participant-key-enrollment" ||
              kind == "participant-key-enrollment-plan" ||
              kind == "participant-key-enrollment-ingress" ||
              kind == "application-share-issue-grain-request" ||
              kind == "application-share-issue-grain-plan" ||
              kind == "application-dispatch-plan" ||
              kind == "application-dispatch-request" then
              readBoundedBytes input maxFrame else readBytes input
          let value ← IO.ofExcept (inspectHost config kind bytes)
          if kind == "application-route-admission-attestation" ||
              kind == "application-stream-continuity-attestation" ||
              kind == "application-dispatch-committed" ||
              kind == "application-lifecycle-claim-committed-v2" ||
              kind == "application-lifecycle-claim-committed-v3" ||
              kind == "fn-consumer-namespace-plan" ||
              kind == "application-agent-reserve-plan" ||
              kind == "application-agent-paid-dispatch-plan" ||
              kind == "application-agent-dispatch-committed" ||
              kind == "application-agent-lifetime-reserve-request" ||
              kind == "application-agent-lifetime-paid-request" ||
              kind == "application-agent-lifetime-reserve-plan" ||
              kind == "application-agent-lifetime-paid-plan" ||
              kind == "application-agent-lifetime-dispatch-committed" ||
              kind == "application-lifecycle-launch-begin-request" ||
              kind == "application-lifecycle-launch-continue-request" ||
              kind == "application-lifecycle-launch-begin-plan" ||
              kind == "application-lifecycle-launch-stop-plan" ||
              kind == "application-lifecycle-launch-claim-request" ||
              kind == "application-lifecycle-launch-claim-plan" ||
              kind == "application-lifecycle-launch-completion-request" ||
              kind == "application-lifecycle-launch-completion-plan" ||
              kind == "application-lifecycle-launch-physical-report" ||
              kind == "application-lifecycle-launch-physical-signed-report" ||
              kind == "application-agent-lifetime-grant-request" ||
              kind == "application-agent-lifetime-grant-plan" ||
              kind == "application-session-enrollment-request" ||
              kind == "application-session-enrollment-plan" ||
              kind == "application-session-enrollment-ingress" ||
              kind == "participant-key-enrollment" ||
              kind == "participant-key-enrollment-plan" ||
              kind == "participant-key-enrollment-ingress" ||
              kind == "application-share-issue-grain-request" ||
              kind == "application-share-issue-grain-plan" ||
              kind == "application-dispatch-plan" ||
              kind == "application-dispatch-request" then
            let serialized := value.compress
            unless serialized.toUTF8.size ≤ maxDispatchInspectionJsonBytes do
              throw (IO.userError "application dispatch inspection exceeds JSON budget")
            IO.FS.writeFile output serialized
          else writeJson output value
          pure 0
      | "inspect-agent-lifetime-paid-ingress", [planPath, ingressPath, output] =>
          let plan ← readBoundedBytes planPath FnEvidenceCodec.maxHostFrameBytes
          let ingress ← readBoundedBytes ingressPath FnEvidenceCodec.maxHostFrameBytes
          let view ← IO.ofExcept
            (ApplicationAgentLifetimePaidIngressInspection.inspect plan ingress)
          let serialized := view.compress
          unless serialized.toUTF8.size ≤ maxDispatchInspectionJsonBytes do
            throw (IO.userError "paid ingress inspection exceeds JSON budget")
          IO.FS.writeFile output serialized
          pure 0
      | "inspect-accepted-agent-lifetime-grant", [ingressPath, output] =>
          let ingress ← readBoundedBytes ingressPath FnEvidenceCodec.maxHostFrameBytes
          let view ← IO.ofExcept (←
            Minidregg.Host.ApplicationAgentLifetimeGrantInspection.inspectAcceptedCurrent
              config ingress)
          let serialized := view.compress
          unless serialized.toUTF8.size ≤ maxDispatchInspectionJsonBytes do
            throw (IO.userError "accepted grant inspection exceeds JSON budget")
          IO.FS.writeFile output serialized
          pure 0
      | "inspect-stop-claim", [planPath, committedPath, output] =>
          let plan ← readBoundedBytes planPath FnEvidenceCodec.maxHostFrameBytes
          let committed ← readBoundedBytes committedPath FnEvidenceCodec.maxHostFrameBytes
          let view ← IO.ofExcept (← inspectStopClaimCurrent config plan committed)
          let serialized := view.compress
          unless serialized.toUTF8.size ≤ maxDispatchInspectionJsonBytes do
            throw (IO.userError "STOP claim inspection exceeds JSON budget")
          IO.FS.writeFile output serialized
          pure 0
      | "derive", [kind, input, output] =>
          let value ← IO.ofExcept (Minidregg.Host.Json.derive kind (← readJson input))
          writeJson output value
          pure 0
      | "signatures", [input, output] =>
          let bytes ← IO.ofExcept (Minidregg.Host.Json.signatures (← readJson input))
          writeBytes output bytes
          pure 0
      | "genesis", [input, imageOutput, configOutput] =>
          let ⟨source, built⟩ ← IO.ofExcept <|
            (NativeHostGenesis.buildBytes config.profile (← readBytes input)).mapError (fun error => s!"{repr error}")
          unless source.deployment == config.deployment && source.federation == config.federation &&
              source.tariff == config.tariff && source.genesisHeight == config.genesisHeight do
            throw (IO.userError "genesis source and operator runtime manifest differ")
          let keyPath := settings.checkpointKey.getD
            ((System.FilePath.mk configOutput).parent.getD "." / "checkpoint.key").toString
          let pinned := { settings with
            expectedSeed := (NativeHost.seedIdentity built.seed).value
            checkpointKey := some keyPath }
          let genesis := DurableReceiverCodec.encode built.image
          discard <| IO.ofExcept <| do
            let loaded ← DurableReceiverIO.loadBytes ResourceBirthCodec.rootBytes pinned.config.logStart genesis
            NativeHost.validateLoaded pinned.config loaded
          writeBytes imageOutput genesis
          IO.FS.writeFile configOutput (toJson pinned).pretty
          pure 0
      | "describe", [] => IO.println (← description config).pretty; pure 0
      | "stdio", [] =>
          withPinnedSignature config fun pinnedConfig => do
            withFnPollService settings fun service => do
              withFnReplyPollService settings fun replyService => do
                withFnReplyCatalogService settings fun catalogService => do
                  let session ← IO.ofExcept (← NativeHostSession.start pinnedConfig)
                  let state ← IO.mkRef (some session)
                  let carriedState ← IO.mkRef (none : Option (CarriedNativeHostSession.Walked pinnedConfig))
                  let fnDispatch : UInt8 → List UInt8 → IO (UInt8 × List UInt8) :=
                    fun operation payload => do
                      try
                        match operation with
                        | 2 | 3 =>
                            if settings.carryRegistry.isSome then
                              let outcome ← carriedOrdinaryCall pinnedConfig state carriedState
                                settings (operation == 2) payload
                              return (operation, outcomeCodec.encode outcome)
                            else if operation == 2 then
                              let session ← sessionCurrent pinnedConfig state
                              let result ← match callCodec.decode payload with
                                | none => pure (NativeHostCodec.Outcome.refused .malformed
                                    "wire".toUTF8.toList "noncanonical native host call".toUTF8.toList,
                                    NativeHost.Disclosure.uniform)
                                | some call =>
                                  NativeHost.submitDisclosedWith pinnedConfig session.opened call
                                    (sessionConfirmed pinnedConfig state)
                              NativeHost.logOperatorRefusal result.1
                              return (2, outcomeCodec.encode (NativeHost.disclose result))
                            else
                              let opened ← sessionOpened pinnedConfig state
                              let outcome := match callCodec.decode payload with
                                | none => NativeHostCodec.Outcome.refused .malformed "wire".toUTF8.toList
                                    "noncanonical native host call".toUTF8.toList
                                | some call => NativeHost.lookupLoaded pinnedConfig opened call
                              return (3, outcomeCodec.encode outcome)
                        | 12 | 13 =>
                            let some selected := service
                              | return ((255 : UInt8), failure .operationRejected "fn-poll"
                                  "fn consumer poll service is not configured")
                            if operation == 12 then
                              runFnPollSession pinnedConfig state selected payload
                            else
                              runFnAckSession pinnedConfig state selected payload
                        | 14 | 15 =>
                            match catalogService, replyService with
                            | some selected, none =>
                                if operation == 14 then
                                  runFnReplyCatalogPollSession pinnedConfig state selected payload
                                else
                                  runFnReplyAckSession pinnedConfig state
                                    selected.ackService (some selected) payload
                            | none, some selected =>
                                if operation == 14 then
                                  runFnReplyPollSession pinnedConfig state selected payload
                                else
                                  runFnReplyAckSession pinnedConfig state selected none payload
                            | _, _ => return ((255 : UInt8), failure .operationRejected "fn-reply-poll"
                                "exactly one A reply poll service must be configured")
                        | 16 =>
                            let some selected := catalogService
                              | return ((255 : UInt8), failure .operationRejected "fn-origin-outbox"
                                  "A origin outbox service is not configured")
                            runFnOriginOutboxSession pinnedConfig state selected payload
                        | 17 =>
                            let providerIds ← IO.ofExcept settings.continuityIds
                            if providerIds.isEmpty then
                              return ((255 : UInt8), failure .operationRejected "provider-continuity"
                                "provider continuity resource is not configured")
                            runProviderContinuitySession pinnedConfig state
                              providerIds payload
                        | 18 =>
                            unless catalogService.isSome do
                              return ((255 : UInt8), failure .operationRejected "fn-origin-outbox"
                                "A origin outbox service is not configured")
                            runFnOriginOutboxExportSession pinnedConfig state payload
                        | 151 =>
                            let result ← carriedContinuitySession pinnedConfig state carriedState settings payload
                            match result with
                            | .ok response => return (151, response)
                            | .error _ => return (255, failure .operationRejected "receipt-continuity"
                                "receipt continuity request refused")
                        | 153 =>
                            let registry ← loadCarryRegistry settings
                            let opened ← sessionOpened pinnedConfig state
                            let result ← RetainedSegmentInspection.serveLookup pinnedConfig opened.durable registry payload
                            match result with
                            | .ok response => return (153, response)
                            | .error _ => return (255, failure .operationRejected "carried-history"
                                "retained historical request refused")
                        | 19 =>
                            let services ← IO.ofExcept settings.providerServicePins
                            let legacy ← IO.ofExcept settings.providerMeteringPin
                            let quoted : Except String Lean.Json :=
                              match legacy.toList ++ services with
                              | [] => .error "provider metering is not configured"
                              | pins => ProviderUsage.quotePayload pins payload
                            match quoted with
                            | .ok report =>
                                return ((19 : UInt8), report.compress.toUTF8.toList)
                            | .error reason =>
                                return ((255 : UInt8), failure .operationRejected "provider-metering" reason)
                        | 28 =>
                            let outcome ← applicationShareIssueSubmitSession
                              pinnedConfig state payload
                            return ((28 : UInt8), outcomeCodec.encode outcome)
                        | 29 =>
                            let outcome ← applicationShareIssueLookupSession
                              pinnedConfig state payload
                            return ((29 : UInt8), outcomeCodec.encode outcome)
                        | 54 =>
                            let outcome ← applicationGrainShareIssueSubmitSession
                              pinnedConfig state payload
                            return ((54 : UInt8), outcomeCodec.encode outcome)
                        | 55 =>
                            let outcome ← applicationGrainShareIssueLookupSession
                              pinnedConfig state payload
                            return ((55 : UInt8), outcomeCodec.encode outcome)
                        | 72 =>
                            let outcome ← agentLifetimeGrantSubmitSession
                              pinnedConfig state payload
                            return ((72 : UInt8), outcomeCodec.encode outcome)
                        | 73 =>
                            let outcome ← agentLifetimeGrantLookupSession
                              pinnedConfig state payload
                            return ((73 : UInt8), outcomeCodec.encode outcome)
                        | 84 =>
                            let outcome ← if settings.carryRegistry.isSome then
                              carriedEnrollmentSubmit pinnedConfig state carriedState settings payload
                            else applicationSessionEnrollmentSubmitSession pinnedConfig state payload
                            return ((84 : UInt8), outcomeCodec.encode outcome)
                        | 85 =>
                            let outcome ← if settings.carryRegistry.isSome then
                              carriedEnrollmentLookup pinnedConfig state carriedState settings payload
                            else applicationSessionEnrollmentLookupSession pinnedConfig state payload
                            return ((85 : UInt8), outcomeCodec.encode outcome)
                        | 88 =>
                            let opened ← sessionOpened pinnedConfig state
                            let outcome ← NativeHost.enrollmentSubmitLoaded
                              pinnedConfig opened payload
                            return ((88 : UInt8), outcomeCodec.encode outcome)
                        | 89 =>
                            let opened ← sessionOpened pinnedConfig state
                            let outcome := NativeHost.enrollmentLookupLoaded
                              pinnedConfig opened payload
                            return ((89 : UInt8), outcomeCodec.encode outcome)
                        | 94 =>
                            let opened ← sessionOpened pinnedConfig state
                            let outcome ← NativeHost.provisionSubmitLoaded
                              pinnedConfig opened payload
                            return ((94 : UInt8), outcomeCodec.encode outcome)
                        | 95 =>
                            let opened ← sessionOpened pinnedConfig state
                            let outcome := NativeHost.provisionLookupLoaded
                              pinnedConfig opened payload
                            return ((95 : UInt8), outcomeCodec.encode outcome)
                        | 96 =>
                            let (observationBytes, draftBytes) ← splitPair payload
                            let opened ← sessionOpened pinnedConfig state
                            let plan ← match ← NativeHost.fleetPlanAuthorizedLoaded
                                pinnedConfig opened observationBytes draftBytes with
                              | .ok plan => pure plan
                              | .error refusal =>
                                  return ((255 : UInt8), refusalFrame "fleet-plan" refusal)
                            let bytes := FleetTurn.signingPlanCodec.encode plan
                            unless bytes.length ≤ FnEvidenceCodec.maxHostFrameBytes do
                              throw (IO.userError "fleet turn plan exceeds host frame bound")
                            return ((96 : UInt8), bytes)
                        | 97 =>
                            let (planBytes, signature) ← splitPair payload
                            let some plan := FleetTurn.signingPlanCodec.decode planBytes
                              | throw (RequestRefusal.malformed "noncanonical fleet turn plan")
                            let ingress ← IO.ofExcept (NativeHost.fleetAssemble plan signature)
                            unless ingress.length ≤ FnEvidenceCodec.maxHostFrameBytes do
                              throw (IO.userError "fleet turn ingress exceeds host frame bound")
                            return ((97 : UInt8), ingress)
                        | 98 =>
                            let opened ← sessionOpened pinnedConfig state
                            let outcome ← NativeHost.fleetSubmitLoaded pinnedConfig opened payload
                              (sessionConfirmed pinnedConfig state)
                            return ((98 : UInt8), outcomeCodec.encode outcome)
                        | 99 =>
                            let opened ← sessionOpened pinnedConfig state
                            let outcome := NativeHost.fleetLookupLoaded pinnedConfig opened payload
                            return ((99 : UInt8), outcomeCodec.encode outcome)
                        | 100 =>
                            let (observationBytes, requestBytes) ← splitPair payload
                            let some text := String.fromUTF8? requestBytes.toByteArray
                              | throw (IO.userError "fleet poll request is not UTF-8")
                            let request ← IO.ofExcept (Minidregg.Host.Json.parse text)
                            let (topic, cursor, limit) ← IO.ofExcept
                              (Minidregg.Host.Json.fleetPollRequest request)
                            let opened ← sessionOpened pinnedConfig state
                            match ← NativeHost.fleetPollAuthorizedLoaded pinnedConfig opened
                                observationBytes topic cursor limit with
                            | .ok view => return ((100 : UInt8),
                                (Minidregg.Host.Json.fleetPollJson view).compress.toUTF8.toList)
                            | .error refusal => return ((255 : UInt8), refusalFrame "fleet-poll" refusal)
                        | 101 =>
                            let opened ← sessionOpened pinnedConfig state
                            match ← NativeHost.fleetHeadAuthorizedLoaded pinnedConfig opened payload with
                            | .ok view => return ((101 : UInt8),
                                (Minidregg.Host.Json.fleetHeadJson view).compress.toUTF8.toList)
                            | .error refusal => return ((255 : UInt8), refusalFrame "fleet-head" refusal)
                        | 180 =>
                            let (observationBytes, requestBytes) ← splitPair payload
                            let some text := String.fromUTF8? requestBytes.toByteArray
                              | throw (IO.userError "fleet incoming request is not UTF-8")
                            let request ← IO.ofExcept (Minidregg.Host.Json.parse text)
                            let (topic, cursor, limit) ← IO.ofExcept
                              (Minidregg.Host.Json.fleetPollRequest request)
                            let opened ← sessionOpened pinnedConfig state
                            match ← NativeHost.fleetIncomingAuthorizedLoaded pinnedConfig opened
                                observationBytes topic cursor limit with
                            | .ok view => return ((180 : UInt8),
                                (Minidregg.Host.Json.fleetIncomingJson view).compress.toUTF8.toList)
                            | .error refusal => return ((255 : UInt8), refusalFrame "fleet-incoming" refusal)
                        | 102 =>
                            let some text := String.fromUTF8? payload.toByteArray
                              | throw (IO.userError "transaction id is not UTF-8")
                            let some transactionId := text.toNat?
                              | throw (IO.userError "transaction id must be canonical decimal")
                            unless toString transactionId == text do
                              throw (IO.userError "transaction id must be canonical decimal")
                            if settings.carryRegistry.isSome then
                              let session ← sessionCarriedWalked pinnedConfig state carriedState settings
                              let registry ← loadCarryRegistry settings
                              let index := session.verified.opened.durable.image.accepted.findIdx?
                                (fun record => record.transactionId.value == transactionId)
                              match index with
                              | some i =>
                                  if i < registry.edge.body.cut.height then
                                    let result ← IO.ofExcept (← RetainedSegmentInspection.serveReceiptByTransaction
                                      pinnedConfig session.verified.opened.durable registry transactionId)
                                    return (102, result.compress.toUTF8.toList)
                                  else
                                    let some record := session.verified.opened.durable.image.accepted[i]?
                                      | throw (IO.userError "receipt index unavailable")
                                    let some receipt := carriedReceipt pinnedConfig session
                                        ⟨transactionId⟩ record.event.eventId
                                      | throw (IO.userError "target suffix receipt unavailable")
                                    return (102, (Minidregg.Host.Json.fleetReceiptLookupJson
                                      transactionId (some receipt)).compress.toUTF8.toList)
                              | none => return (102, (Minidregg.Host.Json.fleetReceiptLookupJson
                                  transactionId none).compress.toUTF8.toList)
                            else
                              let opened ← sessionOpened pinnedConfig state
                              let receipt := NativeHost.receiptByTransactionLoaded pinnedConfig opened
                                ⟨transactionId⟩
                              return (102, (Minidregg.Host.Json.fleetReceiptLookupJson
                                transactionId receipt).compress.toUTF8.toList)
                        | 103 =>
                            let opened ← sessionOpened pinnedConfig state
                            let plan ← IO.ofExcept (NativeHost.payPlanLoaded pinnedConfig opened payload)
                            let bytes := PayCellDomain.signingPlanCodec.encode plan
                            unless bytes.length ≤ FnEvidenceCodec.maxHostFrameBytes do
                              throw (IO.userError "pay plan exceeds host frame bound")
                            return ((103 : UInt8), bytes)
                        | 104 =>
                            let (planBytes, signature) ← splitPair payload
                            let some plan := PayCellDomain.signingPlanCodec.decode planBytes
                              | throw (RequestRefusal.malformed "noncanonical pay plan")
                            let ingress ← IO.ofExcept (NativeHost.payAssemble plan signature)
                            unless ingress.length ≤ FnEvidenceCodec.maxHostFrameBytes do
                              throw (IO.userError "pay ingress exceeds host frame bound")
                            return ((104 : UInt8), ingress)
                        | 105 =>
                            let opened ← sessionOpened pinnedConfig state
                            let outcome ← NativeHost.paySubmitLoaded pinnedConfig opened payload
                            -- A pay submission is blind: its refusal (including the
                            -- receiver's pre-signature notOwner/bookExhausted/...) is
                            -- the uniform `undisclosed` frame (MR's rule).
                            return ((105 : UInt8),
                              outcomeCodec.encode (NativeHost.publicSubmissionOutcome outcome))
                        | 106 =>
                            let opened ← sessionOpened pinnedConfig state
                            let outcome := NativeHost.payLookupLoaded pinnedConfig opened payload
                            return ((106 : UInt8), outcomeCodec.encode outcome)
                        | 193 =>
                            let (planBytes, signatureBytes) ← splitPair payload
                            let signatures ← decodeSignatures signatureBytes
                            let ready ← if settings.carryRegistry.isSome then do
                              let session ← sessionCarriedWalked pinnedConfig state carriedState settings
                              ApplicationDispatchReady.assembledReadySuffix session.verified planBytes signatures
                            else do
                              let session ← sessionWalked pinnedConfig state
                              ApplicationDispatchReady.assembledReadyVerified session.verified planBytes signatures
                            return ((193 : UInt8), ready.compress.toUTF8.toList)
                        | 194 =>
                            let (request, authenticated) ← splitPair payload
                            let (signature, observations) ← splitPair authenticated
                            let (appRead, rest) ← splitPair observations
                            let (packageRead, rest) ← splitPair rest
                            let (sessionRead, rest) ← splitPair rest
                            let (enrollmentRead, ticketRead) ← splitPair rest
                            let reads := [appRead, packageRead, sessionRead, enrollmentRead, ticketRead]
                            let result ← if settings.carryRegistry.isSome then do
                              let session ← sessionCarriedWalked pinnedConfig state carriedState settings
                              ApplicationDispatchReady.authenticatedPlanSuffix session.verified request signature reads
                            else do
                              let session ← sessionWalked pinnedConfig state
                              ApplicationDispatchReady.authenticatedPlanVerified session.verified request signature reads
                            match result with
                            | .ok plan =>
                                let bytes := ApplicationDispatchAuthoring.planCodec.encode plan
                                unless bytes.length ≤ FnEvidenceCodec.maxHostFrameBytes do
                                  throw (RequestRefusal.malformed "member app plan exceeds host frame bound")
                                return ((194 : UInt8), bytes)
                            | .error _ => return ((255 : UInt8), failure .operationRejected
                                "application-authenticated-plan" "undisclosed")
                        | 187 =>
                            let opened ← sessionOpened pinnedConfig state
                            let bytes ← IO.ofExcept <|
                              KeyCommitmentAdoptionInspection.planLoaded pinnedConfig opened payload
                            return ((187 : UInt8), bytes)
                        | 188 =>
                            let (planBytes, signatures) ← splitPair payload
                            let (currentSignature, nextSignature) ← splitPair signatures
                            let some plan := SubjectKeyCommitmentAdoption.signingPlanCodec.decode planBytes
                              | throw (RequestRefusal.malformed "noncanonical key commitment plan")
                            let bytes ← IO.ofExcept <|
                              NativeHostKeyCommitmentAdoption.assemble plan currentSignature nextSignature
                            return ((188 : UInt8), bytes)
                        | 189 | 190 =>
                            let opened ← if settings.carryRegistry.isSome then do
                              pure (← sessionCarriedWalked pinnedConfig state carriedState settings).verified.opened
                            else sessionOpened pinnedConfig state
                            let outcome ← if operation == 189 then
                              NativeHostKeyCommitmentAdoption.submitLoaded pinnedConfig opened payload
                            else pure (NativeHostKeyCommitmentAdoption.lookupLoaded pinnedConfig opened payload)
                            let outcome ← if settings.carryRegistry.isSome then do
                              match outcome with
                              | .confirmed kind receipt =>
                                  let current ← sessionCarriedWalked pinnedConfig state carriedState settings
                                  match carriedReceipt pinnedConfig current receipt.transactionId receipt.eventId with
                                  | some exact => pure (.confirmed kind exact)
                                  | none => pure (.uncertain "key commitment suffix receipt unavailable".toUTF8.toList)
                              | other => pure other
                            else pure outcome
                            return (operation, outcomeCodec.encode (NativeHost.publicSubmissionOutcome outcome))
                        | 140 =>
                            let opened ← sessionOpened pinnedConfig state
                            match NativeHost.rotationPlanLoaded pinnedConfig opened payload with
                            | .error detail =>
                                return ((255 : UInt8), failure .operationRejected "rotate-key-plan" detail)
                            | .ok plan =>
                                let bytes := SubjectKeyRotation.signingPlanCodec.encode plan
                                unless bytes.length ≤ FnEvidenceCodec.maxHostFrameBytes do
                                  throw (IO.userError "rotation plan exceeds host frame bound")
                                return ((140 : UInt8), bytes)
                        | 141 =>
                            let (planBytes, signature) ← splitPair payload
                            let some plan := SubjectKeyRotation.signingPlanCodec.decode planBytes
                              | throw (IO.userError "noncanonical subject key rotation plan")
                            let ingress ← IO.ofExcept (NativeHost.rotationAssemble plan signature)
                            unless ingress.length ≤ FnEvidenceCodec.maxHostFrameBytes do
                              throw (IO.userError "rotation ingress exceeds host frame bound")
                            return ((141 : UInt8), ingress)
                        | 142 =>
                            let opened ← sessionOpened pinnedConfig state
                            let outcome ← NativeHost.receivingSubmitLoaded pinnedConfig opened
                              SubjectKeyRotation.family (NativeHostReplay.rotationEnv pinnedConfig)
                              "rotate-key" payload
                            return ((142 : UInt8), outcomeCodec.encode outcome)
                        | 143 =>
                            let opened ← sessionOpened pinnedConfig state
                            let outcome := NativeHost.receivingLookupLoaded pinnedConfig opened
                              SubjectKeyRotation.family (NativeHostReplay.rotationEnv pinnedConfig)
                              "rotate-key" payload
                            return ((143 : UInt8), outcomeCodec.encode outcome)
                        | 144 =>
                            let some text := String.fromUTF8? payload.toByteArray
                              | throw (IO.userError "key status query is not UTF-8")
                            let query ← IO.ofExcept (Minidregg.Host.Json.parse text)
                            let (subject, publicKey) ← IO.ofExcept
                              (Minidregg.Host.Json.subjectKeyStatusQuery query)
                            let opened ← sessionOpened pinnedConfig state
                            match NativeHost.keyStatusLoaded pinnedConfig opened ⟨subject⟩ publicKey with
                            | .error detail =>
                                return ((255 : UInt8), failure .operationRejected "key-status" detail)
                            | .ok status =>
                                return ((144 : UInt8),
                                  (Minidregg.Host.Json.subjectKeyStatusJson subject status).compress.toUTF8.toList)
                        | 107 =>
                            let opened ← sessionOpened pinnedConfig state
                            let view ← IO.ofExcept (NativeHost.payViewLoaded pinnedConfig opened)
                            return ((107 : UInt8), PayCellDomain.viewCodec.encode view)
                        | 123 =>
                            let opened ← sessionOpened pinnedConfig state
                            match NativeHost.wellPlanLoaded pinnedConfig opened payload with
                            | .ok plan => return ((123 : UInt8), RealmWellCodec.signingPlanCodec.encode plan)
                            | .error detail => return ((255 : UInt8), failure .operationRejected "well-plan" detail)
                        | 124 =>
                            let (planBytes, signature) ← splitPair payload
                            let some plan := RealmWellCodec.signingPlanCodec.decode planBytes
                              | throw (IO.userError "noncanonical realm well plan")
                            let ingress ← IO.ofExcept (NativeHost.wellAssemble plan signature)
                            return ((124 : UInt8), ingress)
                        | 125 =>
                            let opened ← sessionOpened pinnedConfig state
                            let outcome ← NativeHost.wellSubmitLoaded pinnedConfig opened payload
                            -- Blind like every submission (MR): the submitter gets
                            -- the uniform refusal, the operator log the reason.
                            NativeHost.logOperatorRefusal outcome
                            match outcome with
                            | .confirmed _ _ => return ((125 : UInt8), outcomeCodec.encode outcome)
                            | _ => return ((255 : UInt8),
                                outcomeCodec.encode (NativeHost.publicSubmissionOutcome outcome))
                        | 126 =>
                            let opened ← sessionOpened pinnedConfig state
                            let plan ← IO.ofExcept (NativeHost.clockPlanLoaded pinnedConfig opened payload)
                            let bytes := ClockTickReceiver.signingPlanCodec.encode plan
                            unless bytes.length ≤ FnEvidenceCodec.maxHostFrameBytes do
                              throw (IO.userError "clock plan exceeds host frame bound")
                            return ((126 : UInt8), bytes)
                        | 127 =>
                            let (planBytes, signature) ← splitPair payload
                            let some plan := ClockTickReceiver.signingPlanCodec.decode planBytes
                              | throw (IO.userError "noncanonical clock plan")
                            let ingress ← IO.ofExcept (NativeHost.clockAssemble plan signature)
                            unless ingress.length ≤ FnEvidenceCodec.maxHostFrameBytes do
                              throw (IO.userError "clock ingress exceeds host frame bound")
                            return ((127 : UInt8), ingress)
                        | 128 =>
                            let opened ← sessionOpened pinnedConfig state
                            let outcome ← NativeHost.clockSubmitLoaded pinnedConfig opened payload
                            return ((128 : UInt8), outcomeCodec.encode outcome)
                        | 129 =>
                            let opened ← sessionOpened pinnedConfig state
                            let view ← IO.ofExcept (NativeHost.clockViewLoaded pinnedConfig opened)
                            return ((129 : UInt8), ClockTickReceiver.viewCodec.encode view)
                        | 108 =>
                            let opened ← sessionOpened pinnedConfig state
                            let plan ← IO.ofExcept
                              (NativeHost.payObservationPlanLoaded pinnedConfig opened payload)
                            let bytes := PayCellDomain.signingPlanCodec.encode plan
                            unless bytes.length ≤ FnEvidenceCodec.maxHostFrameBytes do
                              throw (IO.userError "pay observation plan exceeds host frame bound")
                            return ((108 : UInt8), bytes)
                        | 109 =>
                            let (planBytes, signature) ← splitPair payload
                            let some plan := PayCellDomain.signingPlanCodec.decode planBytes
                              | throw (IO.userError "noncanonical pay observation plan")
                            let ingress ← IO.ofExcept (NativeHost.payObservationAssemble plan signature)
                            unless ingress.length ≤ FnEvidenceCodec.maxHostFrameBytes do
                              throw (IO.userError "pay observation ingress exceeds host frame bound")
                            return ((109 : UInt8), ingress)
                        | 110 =>
                            let opened ← sessionOpened pinnedConfig state
                            let outcome ← NativeHost.payObservationSubmitLoaded pinnedConfig opened payload
                            return ((110 : UInt8), outcomeCodec.encode outcome)
                        | 111 =>
                            let opened ← sessionOpened pinnedConfig state
                            let outcome := NativeHost.payObservationLookupLoaded pinnedConfig opened payload
                            return ((111 : UInt8), outcomeCodec.encode outcome)
                        | 112 =>
                            let opened ← sessionOpened pinnedConfig state
                            let view ← IO.ofExcept (NativeHost.payEnrolmentViewLoaded pinnedConfig opened)
                            let bytes := PayCellDomain.enrolmentViewCodec.encode view
                            unless bytes.length ≤ FnEvidenceCodec.maxHostFrameBytes do
                              throw (IO.userError "enrollment view exceeds host frame bound")
                            return ((112 : UInt8), bytes)
                        | 121 =>
                            unless payload.length ≤ 4096 do
                              throw (IO.userError "pay quote request exceeds bound")
                            let some text := String.fromUTF8? payload.toByteArray
                              | throw (IO.userError "pay quote request is not UTF-8")
                            let request ← IO.ofExcept (Minidregg.Host.Json.parse text)
                            let opened ← sessionOpened pinnedConfig state
                            let quoted ← IO.ofExcept
                              (Minidregg.Host.Json.payEnrolQuoteLoadedJson pinnedConfig opened request)
                            return ((121 : UInt8), quoted.compress.toUTF8.toList)
                        | 181 | 182 =>
                            unless payload.length ≤ 4096 do
                              throw (IO.userError "paid status/quote request exceeds bound")
                            let some text := String.fromUTF8? payload.toByteArray
                              | throw (IO.userError "paid status/quote request is not UTF-8")
                            let request ← IO.ofExcept (Minidregg.Host.Json.parse text)
                            let opened ← sessionOpened pinnedConfig state
                            let response ← IO.ofExcept (if operation == 181 then
                              Minidregg.Host.PayClaims.statusLoadedJson pinnedConfig opened request
                              else Minidregg.Host.PayClaims.quoteLoadedJson pinnedConfig opened request)
                            let bytes := response.compress.toUTF8.toList
                            unless bytes.length ≤ 8192 do
                              throw (IO.userError "paid status/quote response exceeds bound")
                            return (operation, bytes)
                        | 183 =>
                            let opened ← sessionOpened pinnedConfig state
                            let plan ← IO.ofExcept (NativeHost.payClaimPlanLoaded pinnedConfig opened payload)
                            let bytes := NativeHost.claimSigningPlanCodec.encode plan
                            unless bytes.length ≤ 3072 do
                              throw (IO.userError "claim signing plan exceeds bound")
                            return ((183 : UInt8), bytes)
                        | 184 =>
                            unless payload.length ≤ 4096 do
                              throw (IO.userError "claim assembly exceeds bound")
                            let (plan, signature) ← splitPair payload
                            let bytes ← IO.ofExcept (NativeHost.payClaimAssemble plan signature)
                            return ((184 : UInt8), bytes)
                        | 185 =>
                            unless payload.length ≤ 4096 do
                              throw (IO.userError "claim ingress exceeds bound")
                            let opened ← sessionOpened pinnedConfig state
                            let outcome ← NativeHost.payClaimSubmitLoaded pinnedConfig opened payload
                            return ((185 : UInt8), outcomeCodec.encode outcome)
                        | 186 =>
                            unless payload.length ≤ 4096 do
                              throw (IO.userError "claim lookup ingress exceeds bound")
                            let opened ← sessionOpened pinnedConfig state
                            return ((186 : UInt8), outcomeCodec.encode (NativeHost.payClaimLookupLoaded pinnedConfig opened payload))
                        | 117 =>
                            let opened ← sessionOpened pinnedConfig state
                            let plan ← IO.ofExcept
                              (← NativeHost.payEnrolPlanCurrentLoaded pinnedConfig opened payload)
                            let bytes := PayCellDomain.signingPlanCodec.encode plan
                            unless bytes.length ≤ FnEvidenceCodec.maxHostFrameBytes do
                              throw (IO.userError "pay enrolment plan exceeds host frame bound")
                            return ((117 : UInt8), bytes)
                        | 118 =>
                            let (planBytes, signature) ← splitPair payload
                            let some plan := PayCellDomain.signingPlanCodec.decode planBytes
                              | throw (IO.userError "noncanonical pay enrolment plan")
                            let ingress ← IO.ofExcept (NativeHost.payEnrolAssemble plan signature)
                            unless ingress.length ≤ FnEvidenceCodec.maxHostFrameBytes do
                              throw (IO.userError "pay enrolment ingress exceeds host frame bound")
                            return ((118 : UInt8), ingress)
                        | 119 =>
                            let opened ← sessionOpened pinnedConfig state
                            let outcome ← NativeHost.payEnrolSubmitCurrentLoaded pinnedConfig opened payload
                            return ((119 : UInt8), outcomeCodec.encode outcome)
                        | 120 =>
                            let opened ← sessionOpened pinnedConfig state
                            let outcome := NativeHost.payEnrolLookupLoaded pinnedConfig opened payload
                            return ((120 : UInt8), outcomeCodec.encode outcome)
                        | 160 =>
                            let opened ← sessionOpened pinnedConfig state
                            let plan ← IO.ofExcept
                              (NativeHost.jobMoneyPlanLoaded pinnedConfig opened payload)
                            let bytes := PayCellDomain.signingPlanCodec.encode plan
                            unless bytes.length ≤ FnEvidenceCodec.maxHostFrameBytes do
                              throw (IO.userError "job money plan exceeds host frame bound")
                            return ((160 : UInt8), bytes)
                        | 161 =>
                            let (planBytes, signature) ← splitPair payload
                            let some plan := PayCellDomain.signingPlanCodec.decode planBytes
                              | throw (IO.userError "noncanonical job money plan")
                            let ingress ← IO.ofExcept (NativeHost.jobMoneyAssemble plan signature)
                            unless ingress.length ≤ FnEvidenceCodec.maxHostFrameBytes do
                              throw (IO.userError "job money ingress exceeds host frame bound")
                            return ((161 : UInt8), ingress)
                        | 162 =>
                            let opened ← sessionOpened pinnedConfig state
                            let outcome ← NativeHost.jobMoneySubmitLoaded pinnedConfig opened payload
                            -- A blind submission like op 115: a refusal is the uniform
                            -- `undisclosed` frame (MR's rule).
                            return ((162 : UInt8),
                              outcomeCodec.encode (NativeHost.publicSubmissionOutcome outcome))
                        | 163 =>
                            let opened ← sessionOpened pinnedConfig state
                            let outcome := NativeHost.jobMoneyLookupLoaded pinnedConfig opened payload
                            return ((163 : UInt8), outcomeCodec.encode outcome)
                        | 113 =>
                            let opened ← sessionOpened pinnedConfig state
                            let plan ← IO.ofExcept
                              (NativeHost.payRefillPlanLoaded pinnedConfig opened payload)
                            let bytes := PayCellDomain.signingPlanCodec.encode plan
                            unless bytes.length ≤ FnEvidenceCodec.maxHostFrameBytes do
                              throw (IO.userError "pay refill plan exceeds host frame bound")
                            return ((113 : UInt8), bytes)
                        | 114 =>
                            let (planBytes, signature) ← splitPair payload
                            let some plan := PayCellDomain.signingPlanCodec.decode planBytes
                              | throw (IO.userError "noncanonical pay refill plan")
                            let ingress ← IO.ofExcept (NativeHost.payRefillAssemble plan signature)
                            unless ingress.length ≤ FnEvidenceCodec.maxHostFrameBytes do
                              throw (IO.userError "pay refill ingress exceeds host frame bound")
                            return ((114 : UInt8), ingress)
                        | 115 =>
                            let opened ← sessionOpened pinnedConfig state
                            let outcome ← NativeHost.payRefillSubmitLoaded pinnedConfig opened payload
                            -- A refill is a friend's blind submission, like op 105: its
                            -- refusal (notOwner, bookRefused, ...) is the uniform
                            -- `undisclosed` frame (MR's rule).
                            return ((115 : UInt8),
                              outcomeCodec.encode (NativeHost.publicSubmissionOutcome outcome))
                        | 116 =>
                            let opened ← sessionOpened pinnedConfig state
                            let outcome := NativeHost.payRefillLookupLoaded pinnedConfig opened payload
                            return ((116 : UInt8), outcomeCodec.encode outcome)
                        | 170 =>
                            let opened ← sessionOpened pinnedConfig state
                            let plan ← IO.ofExcept (NativeHost.certifyPlanLoaded pinnedConfig opened payload)
                            let bytes := CertifyReceiver.signingPlanCodec.encode plan
                            unless bytes.length ≤ FnEvidenceCodec.maxHostFrameBytes do
                              throw (IO.userError "certify plan exceeds host frame bound")
                            return ((170 : UInt8), bytes)
                        | 171 =>
                            let (planBytes, signature) ← splitPair payload
                            let some plan := CertifyReceiver.signingPlanCodec.decode planBytes
                              | throw (IO.userError "noncanonical certify plan")
                            let ingress ← IO.ofExcept (NativeHost.certifyAssemble plan signature)
                            unless ingress.length ≤ FnEvidenceCodec.maxHostFrameBytes do
                              throw (IO.userError "certify ingress exceeds host frame bound")
                            return ((171 : UInt8), ingress)
                        | 172 =>
                            let opened ← sessionOpened pinnedConfig state
                            let outcome ← NativeHost.certifySubmitLoaded pinnedConfig opened payload
                            return ((172 : UInt8), outcomeCodec.encode outcome)
                        | 173 =>
                            let opened ← sessionOpened pinnedConfig state
                            let view ← IO.ofExcept (NativeHost.certifyViewLoaded pinnedConfig opened)
                            return ((173 : UInt8), CertifyReceiver.viewCodec.encode view)
                        | 60 =>
                            let outcome ← fnSelectedPollSubmitSession
                              pinnedConfig state payload
                            return ((60 : UInt8), outcomeCodec.encode outcome)
                        | 61 =>
                            let outcome ← fnSelectedPollLookupSession
                              pinnedConfig state payload
                            return ((61 : UInt8), outcomeCodec.encode outcome)
                        | 62 =>
                            let outcome ← fnEmptyPollSubmitSession
                              pinnedConfig state payload
                            return ((62 : UInt8), outcomeCodec.encode outcome)
                        | 63 =>
                            let outcome ← fnEmptyPollLookupSession
                              pinnedConfig state payload
                            return ((63 : UInt8), outcomeCodec.encode outcome)
                        | 64 =>
                            let some service := service
                              | return ((255 : UInt8), failure .operationRejected "fn-frontier-plan"
                                  "fn consumer service is not configured")
                            let some releaseKey := fnFrontierPlanRequestCodec.decode payload
                              | throw (RequestRefusal.malformed "noncanonical fn frontier plan request")
                            let plan ← fnFrontierPrepareSession pinnedConfig state
                              service releaseKey
                            let bytes := FnConsumerFrontierPlan.planCodec.encode plan
                            unless bytes.length ≤ FnEvidenceCodec.maxHostFrameBytes do
                              throw (IO.userError "fn frontier plan exceeds host frame bound")
                            return ((64 : UInt8), bytes)
                        | 65 =>
                            let some service := service
                              | return ((255 : UInt8), failure .operationRejected "fn-frontier-assemble"
                                  "fn consumer service is not configured")
                            let (planBytes, signature) ← splitPair payload
                            let some plan := FnConsumerFrontierPlan.planCodec.decode planBytes
                              | throw (RequestRefusal.malformed "noncanonical fn frontier signing plan")
                            let releaseKey := plan.selected.map
                              (fun spec => spec.evidence.releaseKey)
                            let current ← fnFrontierPrepareSession pinnedConfig state
                              service releaseKey
                            unless current == plan do
                              throw (IO.userError "fn frontier poll or Mini history changed before assembly")
                            let opened ← sessionOpened pinnedConfig state
                            let ingress ← IO.ofExcept <|
                              FnConsumerFrontierPlan.assembleSignature
                                pinnedConfig opened plan signature
                            return ((65 : UInt8), ingress)
                        | 30 =>
                            let intent ← applicationCurrentBirthIntentSession
                              pinnedConfig state true payload
                            return ((30 : UInt8), intent)
                        | 31 =>
                            let intent ← applicationCurrentBirthIntentSession
                              pinnedConfig state false payload
                            return ((31 : UInt8), intent)
                        | 131 =>
                            let (jam, abiBytes) ← splitPair payload
                            let some abiSource := String.fromUTF8? abiBytes.toByteArray
                              | throw (IO.userError "nock program ABI is not UTF-8")
                            let program ← IO.ofExcept
                              (Minidregg.Host.Json.nockProgramOf jam abiSource)
                            let directory ← nockDirectory pinnedConfig state
                            let verdict := Minidregg.Kernel.NockProgramCell.checkProgram
                              pinnedConfig.disabledEvaluators
                              pinnedConfig.deployment.domain directory program
                            return ((131 : UInt8),
                              (Minidregg.Host.Json.nockCheckJson program verdict).compress.toUTF8.toList)
                        | 132 =>
                            let some source := String.fromUTF8? payload.toByteArray
                              | throw (IO.userError "nock program id is not UTF-8")
                            let some value := source.trimAscii.toString.toNat?
                              | throw (IO.userError "nock program id is not a decimal")
                            let directory ← nockDirectory pinnedConfig state
                            let programId : Minidregg.Theory.TypedAuthorization.Digest := ⟨value⟩
                            let program := CanonicalCellRegistry.loadProgram
                              pinnedConfig.deployment.domain directory programId
                            return ((132 : UInt8), (Minidregg.Host.Json.nockShowJson
                              pinnedConfig.deployment.domain programId program).compress.toUTF8.toList)
                        | 133 =>
                            let some source := String.fromUTF8? payload.toByteArray
                              | throw (IO.userError "nock sample request is not UTF-8")
                            let (programId, ctx, targets, values) ← IO.ofExcept
                              (Minidregg.Host.Json.nockSampleRequest source)
                            let directory ← nockDirectory pinnedConfig state
                            let verdict := Minidregg.Kernel.NockProgramCell.sampleFor
                              pinnedConfig.disabledEvaluators
                              pinnedConfig.deployment.domain directory programId ctx targets values
                            return ((133 : UInt8),
                              (Minidregg.Host.Json.nockSampleJson verdict).compress.toUTF8.toList)
                        | 134 =>
                            let some source := String.fromUTF8? payload.toByteArray
                              | throw (IO.userError "nock run request is not UTF-8")
                            let (programId, caller, room, targets, values) ← IO.ofExcept
                              (Minidregg.Host.Json.nockRunRequest source)
                            -- One session read per request: the directory is this image's held one.
                            let opened ← sessionOpened pinnedConfig state
                            let height := NativeHost.logicalHeight pinnedConfig opened.durable
                            let directory := opened.directory.directory
                            checkNockServiceBudget pinnedConfig directory programId
                            let verdict := Minidregg.Kernel.Run.dryRun
                              pinnedConfig.disabledEvaluators
                              pinnedConfig.deployment.domain directory programId
                              ⟨height, caller, room⟩ targets values
                            return ((134 : UInt8), (Minidregg.Host.Json.nockRunJson programId height
                              verdict).compress.toUTF8.toList)
                        | 135 =>
                            let some source := String.fromUTF8? payload.toByteArray
                              | throw (IO.userError "nock door poke request is not UTF-8")
                            let (programId, view, wire, cause) ← IO.ofExcept
                              (Minidregg.Host.Json.nockDoorPokeRequest source)
                            let directory ← nockDirectory pinnedConfig state
                            checkNockServiceBudget pinnedConfig directory programId
                            let verdict := match CanonicalCellRegistry.loadProgram
                                pinnedConfig.deployment.domain directory programId with
                              | none => .refused .programUnknown
                              | some program =>
                                -- The dry run renders Nock nouns: Nock's door only.
                                match Minidregg.Kernel.Run.resolve pinnedConfig.disabledEvaluators
                                    program.evaluator with
                                | .error reason => .refused reason
                                | .ok E =>
                                  if E.id ≠ Minidregg.Compiler.Evaluator.nock.id then .refused .doorUnsupported
                                  else match program.abi.door with
                                  | none => .refused .notDoor
                                  | some door => Minidregg.Kernel.NockDoor.dryPoke program door view wire cause
                            return ((135 : UInt8), (Minidregg.Host.Json.nockDoorPokeJson programId
                              verdict).compress.toUTF8.toList)
                        | 136 | 137 =>
                            let some source := String.fromUTF8? payload.toByteArray
                              | throw (IO.userError "nock door read request is not UTF-8")
                            let isPeek := operation == 136
                            let (programId, view, path) ← IO.ofExcept
                              (Minidregg.Host.Json.nockDoorReadRequest source isPeek)
                            let directory ← nockDirectory pinnedConfig state
                            checkNockServiceBudget pinnedConfig directory programId
                            let verdict : Except Minidregg.Kernel.Run.Refusal
                                (Minidregg.Theory.Eval.Ran Minidregg.Theory.Noun) :=
                              match CanonicalCellRegistry.loadProgram
                                  pinnedConfig.deployment.domain directory programId with
                              | none => .error .programUnknown
                              | some program =>
                                -- The replies render Nock nouns: Nock's door only.
                                match Minidregg.Kernel.Run.resolve pinnedConfig.disabledEvaluators
                                    program.evaluator with
                                | .error reason => .error reason
                                | .ok E =>
                                  if E.id ≠ Minidregg.Compiler.Evaluator.nock.id then .error .doorUnsupported
                                  else match program.abi.door with
                                  | none => .error .notDoor
                                  | some door =>
                                    if isPeek then Minidregg.Kernel.NockDoor.peek program door view path
                                    else Minidregg.Kernel.NockDoor.stateNow program view
                            return (operation, (if isPeek then Minidregg.Host.Json.nockDoorPeekJson verdict
                              else Minidregg.Host.Json.nockDoorStateJson verdict).compress.toUTF8.toList)
                        | 201 =>
                            unless payload.length ≤ FnEvidenceCodec.maxHostFrameBytes do
                              throw (IO.userError "reserve birth request exceeds host frame bound")
                            let opened ← sessionOpened pinnedConfig state
                            let plan ← IO.ofExcept (←
                              Minidregg.Host.NativeReserveBirthAuthoring.authorWireLoaded pinnedConfig opened payload)
                            unless plan.length ≤ FnEvidenceCodec.maxHostFrameBytes do
                              throw (IO.userError "reserve birth plan exceeds host frame bound")
                            return ((201 : UInt8), plan)
                        | 202 =>
                            unless payload.length ≤ FnEvidenceCodec.maxHostFrameBytes do
                              throw (IO.userError "reserve birth assembly exceeds host frame bound")
                            let call ← IO.ofExcept (NativeHostReserveBirth.assembleWire payload)
                            unless call.length ≤ FnEvidenceCodec.maxHostFrameBytes do
                              throw (IO.userError "reserve birth call exceeds host frame bound")
                            return ((202 : UInt8), call)
                        | 91 =>
                            unless payload.length ≤ FnEvidenceCodec.maxHostFrameBytes do
                              throw (IO.userError "resource birth request exceeds host frame bound")
                            let (signedObservationBytes, sourceBytes) ← splitPair payload
                            let opened ← sessionOpened pinnedConfig state
                            let some source := String.fromUTF8? sourceBytes.toByteArray
                              | throw (IO.userError "resource birth request is not UTF-8")
                            let json ← IO.ofExcept (Minidregg.Host.Json.parse source)
                            let intent ← IO.ofExcept (←
                              Minidregg.Host.CurrentResourceBirthAuthoring.intentLoadedAuthorized
                                pinnedConfig opened signedObservationBytes json)
                            unless intent.length ≤ FnEvidenceCodec.maxHostFrameBytes do
                              throw (IO.userError "resource birth intent exceeds host frame bound")
                            return ((91 : UInt8), intent)
                        | 32 =>
                            let opened ← sessionOpened pinnedConfig state
                            let plan ← IO.ofExcept <|
                              ApplicationShareIssueAuthoring.prepareRequestLoaded
                                pinnedConfig opened payload
                            let bytes := ApplicationShareIssueAuthoring.planCodec.encode plan
                            unless bytes.length ≤ FnEvidenceCodec.maxHostFrameBytes do
                              throw (IO.userError "share issue plan exceeds host frame bound")
                            return ((32 : UInt8), bytes)
                        | 33 =>
                            let (planBytes, signaturesBytes) ← splitPair payload
                            let some plan := ApplicationShareIssueAuthoring.planCodec.decode planBytes
                              | throw (RequestRefusal.malformed "noncanonical share issue signing plan")
                            let signatures ← decodeSignatures signaturesBytes
                            let ingress ← IO.ofExcept <|
                              ApplicationShareIssueAuthoring.assemble plan signatures
                            unless ingress.length ≤ FnEvidenceCodec.maxHostFrameBytes do
                              throw (IO.userError "share issue ingress exceeds host frame bound")
                            return ((33 : UInt8), ingress)
                        | 56 =>
                            let opened ← sessionOpened pinnedConfig state
                            let plan ← IO.ofExcept <|
                              ApplicationShareIssueGrainAuthoring.prepareRequestLoaded
                                pinnedConfig opened payload
                            let bytes := ApplicationShareIssueGrainAuthoring.planCodec.encode plan
                            unless bytes.length ≤ FnEvidenceCodec.maxHostFrameBytes do
                              throw (IO.userError "grain share issue plan exceeds host frame bound")
                            return ((56 : UInt8), bytes)
                        | 57 =>
                            let (planBytes, signaturesBytes) ← splitPair payload
                            let some plan := ApplicationShareIssueGrainAuthoring.planCodec.decode planBytes
                              | throw (RequestRefusal.malformed "noncanonical grain share issue signing plan")
                            let signatures ← decodeSignatures signaturesBytes
                            let ingress ← IO.ofExcept <|
                              ApplicationShareIssueGrainAuthoring.assemble plan signatures
                            unless ingress.length ≤ FnEvidenceCodec.maxHostFrameBytes do
                              throw (IO.userError "grain share issue ingress exceeds host frame bound")
                            return ((57 : UInt8), ingress)
                        | 40 =>
                            let some selected := service
                              | return ((255 : UInt8), failure .operationRejected "fn-consumer-namespace"
                                  "fn consumer service is not configured")
                            let some ingress := FnConsumerNamespaceRegistration.ingressCodec.decode
                                payload
                              | return ((40 : UInt8), outcomeCodec.encode <|
                                  .refused .malformed "fn-consumer-namespace".toUTF8.toList
                                    "noncanonical ingress".toUTF8.toList)
                            let (scope, binding) ← fnNamespaceLocalZero pinnedConfig selected
                            unless ingress.spec.consumerNamespace.scope == scope &&
                                ingress.spec.consumerNamespace.controlBinding == binding do
                              throw (IO.userError "fn namespace ingress differs from local consumer")
                            let outcome ← fnConsumerNamespaceSubmitSession
                              pinnedConfig state payload
                            return ((40 : UInt8), outcomeCodec.encode outcome)
                        | 42 =>
                            unless payload.isEmpty do
                              throw (IO.userError "fn namespace plan takes no caller selectors")
                            let some selected := service
                              | return ((255 : UInt8), failure .operationRejected "fn-consumer-namespace"
                                  "fn consumer service is not configured")
                            let (scope, binding) ← fnNamespaceLocalZero pinnedConfig selected
                            let gateway ← requireGateway pinnedConfig
                            let opened ← sessionOpened pinnedConfig state
                            let plan ← IO.ofExcept <| FnConsumerNamespacePlan.prepare
                              pinnedConfig opened gateway scope binding 0 0
                            let after ← fnNamespaceLocalZero pinnedConfig selected
                            unless after == (scope, binding) do
                              throw (IO.userError "fn namespace local status changed during plan")
                            return ((42 : UInt8), FnConsumerNamespacePlan.planCodec.encode plan)
                        | 43 =>
                            let some selected := service
                              | return ((255 : UInt8), failure .operationRejected "fn-consumer-namespace"
                                  "fn consumer service is not configured")
                            let (planBytes, gatewaySignature) ← splitPair payload
                            let some plan := FnConsumerNamespacePlan.planCodec.decode planBytes
                              | throw (RequestRefusal.malformed "noncanonical fn namespace plan")
                            let (scope, binding) ← fnNamespaceLocalZero pinnedConfig selected
                            unless plan.spec.consumerNamespace.scope == scope &&
                                plan.spec.consumerNamespace.controlBinding == binding do
                              throw (IO.userError "fn namespace plan differs from local consumer")
                            let opened ← sessionOpened pinnedConfig state
                            let ingress ← IO.ofExcept <| FnConsumerNamespacePlan.assembleSignature
                              pinnedConfig opened plan gatewaySignature
                            let after ← fnNamespaceLocalZero pinnedConfig selected
                            unless after == (scope, binding) do
                              throw (IO.userError "fn namespace local status changed during assembly")
                            return ((43 : UInt8),
                              FnConsumerNamespaceRegistration.ingressCodec.encode ingress)
                        | 44 =>
                            let some management := settings.lifecycleManagement
                              | return ((255 : UInt8), failure .operationRejected "application-lifecycle-completion-author"
                                  "lifecycle management identity is not configured")
                            let (selectorBytes, request) ← splitPair payload
                            let selector ← IO.ofExcept (LifecycleSelector.parse selectorBytes)
                            let session ← sessionWalked pinnedConfig state
                            let plan ← IO.ofExcept <|
                              (← ApplicationLifecycleCompletionOperator.prepareRequestVerified
                                pinnedConfig session.verified (selector.completionPin management) request)
                            let bytes := ApplicationLifecycleCompletionOperator.planCodec.encode plan
                            unless bytes.length ≤ FnEvidenceCodec.maxHostFrameBytes do
                              throw (IO.userError "lifecycle completion plan exceeds host frame bound")
                            return ((44 : UInt8), bytes)
                        | 45 =>
                            let (planBytes, signaturesBytes) ← splitPair payload
                            let some plan := ApplicationLifecycleCompletionOperator.planCodec.decode
                                planBytes
                              | throw (RequestRefusal.malformed "noncanonical lifecycle completion plan")
                            let signatures ← decodeSignatures signaturesBytes
                            let ingress ← IO.ofExcept <|
                              ApplicationLifecycleCompletionOperator.assemble plan signatures
                            unless ingress.length ≤ FnEvidenceCodec.maxHostFrameBytes do
                              throw (IO.userError "lifecycle completion ingress exceeds host frame bound")
                            return ((45 : UInt8), ingress)
                        | 50 =>
                            let some management := settings.lifecycleManagement
                              | return ((255 : UInt8), failure .operationRejected "application-lifecycle-resident-begin-author"
                                  "lifecycle management identity is not configured")
                            let (selectorBytes, request) ← splitPair payload
                            let selector ← IO.ofExcept (LifecycleSelector.parse selectorBytes)
                            let session ← sessionWalked pinnedConfig state
                            let plan ← IO.ofExcept <|
                              ApplicationLifecycleBeginOperator.prepareRequestVerified
                                pinnedConfig session.verified (selector.beginPin management) request
                            let bytes := ApplicationLifecycleBeginOperator.planCodec.encode plan
                            unless bytes.length ≤ FnEvidenceCodec.maxHostFrameBytes do
                              throw (IO.userError "resident BEGIN plan exceeds host frame bound")
                            return ((50 : UInt8), bytes)
                        | 51 =>
                            let (planBytes, signaturesBytes) ← splitPair payload
                            let some plan := ApplicationLifecycleBeginOperator.planCodec.decode
                                planBytes
                              | throw (RequestRefusal.malformed "noncanonical resident BEGIN plan")
                            let signatures ← decodeSignatures signaturesBytes
                            let ingress ← IO.ofExcept <|
                              ApplicationLifecycleBeginOperator.assemble pinnedConfig.expectedSeed plan signatures
                            unless ingress.length ≤ FnEvidenceCodec.maxHostFrameBytes do
                              throw (IO.userError "resident BEGIN ingress exceeds host frame bound")
                            return ((51 : UInt8), ingress)
                        | 52 =>
                            let some management := settings.lifecycleManagement
                              | return ((255 : UInt8), failure .operationRejected "application-lifecycle-claim-author"
                                  "lifecycle management identity is not configured")
                            let (selectorBytes, request) ← splitPair payload
                            let selector ← IO.ofExcept (LifecycleSelector.parse selectorBytes)
                            let session ← sessionWalked pinnedConfig state
                            let plan ← IO.ofExcept <|
                              ApplicationLifecycleClaimOperator.prepareRequestVerified
                                pinnedConfig session.verified (selector.claimPin management) request
                            let bytes := ApplicationLifecycleClaimOperator.planCodec.encode plan
                            unless bytes.length ≤ FnEvidenceCodec.maxHostFrameBytes do
                              throw (IO.userError "lifecycle claim plan exceeds host frame bound")
                            return ((52 : UInt8), bytes)
                        | 53 =>
                            let (planBytes, signaturesBytes) ← splitPair payload
                            let some plan := ApplicationLifecycleClaimOperator.planCodec.decode
                                planBytes
                              | throw (RequestRefusal.malformed "noncanonical lifecycle claim plan")
                            let signatures ← decodeSignatures signaturesBytes
                            let ingress ← IO.ofExcept <|
                              ApplicationLifecycleClaimOperator.assemble pinnedConfig.expectedSeed plan signatures
                            unless ingress.length ≤ FnEvidenceCodec.maxHostFrameBytes do
                              throw (IO.userError "lifecycle claim ingress exceeds host frame bound")
                            return ((53 : UInt8), ingress)
                        | 66 =>
                            let some management := settings.lifecycleManagement
                              | return ((255 : UInt8), failure .operationRejected "application-lifecycle-launch-begin-author"
                                  "lifecycle management identity is not configured")
                            let (selectorBytes, payload) ← splitPair payload
                            let selector ← IO.ofExcept (LifecycleSelector.parse selectorBytes)
                            let pin := selector.beginPin management
                            let session ← sessionWalked pinnedConfig state
                            let bytes ← if let some request :=
                                ApplicationLifecycleLaunchBeginAuthoring.requestCodec.decode payload then
                              if request.kind == .stop then do
                                let plan ← IO.ofExcept <|
                                  ApplicationLifecycleLaunchBeginAuthoring.prepareStopRequestVerified
                                    pinnedConfig session.verified pin payload
                                pure (ApplicationLifecycleLaunchBeginAuthoring.stopPlanCodec.encode plan)
                              else do
                                let plan ← IO.ofExcept <|
                                  ApplicationLifecycleLaunchBeginAuthoring.prepareVerified
                                    pinnedConfig session.verified pin request
                                pure (ApplicationLifecycleLaunchBeginAuthoring.planCodec.encode plan)
                            else do
                              let plan ← IO.ofExcept <|
                                (← ApplicationLifecycleLaunchBeginAuthoring.prepareContinueRequestVerified
                                  pinnedConfig session.verified pin payload)
                              pure (ApplicationLifecycleLaunchBeginAuthoring.planCodec.encode plan)
                            unless bytes.length ≤ FnEvidenceCodec.maxHostFrameBytes do
                              throw (IO.userError "launch BEGIN plan exceeds host frame bound")
                            return ((66 : UInt8), bytes)
                        | 67 =>
                            let (planBytes, signaturesBytes) ← splitPair payload
                            let signatures ← decodeSignatures signaturesBytes
                            let ingress ← if let some plan :=
                                ApplicationLifecycleLaunchBeginAuthoring.stopPlanCodec.decode
                                  planBytes then
                              IO.ofExcept <|
                                ApplicationLifecycleLaunchBeginAuthoring.assembleStop plan signatures
                            else if let some plan :=
                                ApplicationLifecycleLaunchBeginAuthoring.planCodec.decode
                                  planBytes then
                              IO.ofExcept <|
                                ApplicationLifecycleLaunchBeginAuthoring.assemble plan signatures
                            else throw (RequestRefusal.malformed "noncanonical launch BEGIN plan")
                            unless ingress.length ≤ FnEvidenceCodec.maxHostFrameBytes do
                              throw (IO.userError "launch BEGIN ingress exceeds host frame bound")
                            return ((67 : UInt8), ingress)
                        | 68 =>
                            let some management := settings.lifecycleManagement
                              | return ((255 : UInt8), failure .operationRejected "application-lifecycle-launch-claim-author"
                                  "lifecycle management identity is not configured")
                            let (selectorBytes, payload) ← splitPair payload
                            let selector ← IO.ofExcept (LifecycleSelector.parse selectorBytes)
                            let session ← sessionWalked pinnedConfig state
                            let plan ← IO.ofExcept <|
                              ApplicationLifecycleLaunchClaimAuthoring.prepareRequestVerified
                                pinnedConfig session.verified (selector.claimPin management) payload
                            let bytes := ApplicationLifecycleLaunchClaimAuthoring.planCodec.encode plan
                            unless bytes.length ≤ FnEvidenceCodec.maxHostFrameBytes do
                              throw (IO.userError "launch claim plan exceeds host frame bound")
                            return ((68 : UInt8), bytes)
                        | 69 =>
                            let (planBytes, signaturesBytes) ← splitPair payload
                            let some plan := ApplicationLifecycleLaunchClaimAuthoring.planCodec.decode
                                planBytes
                              | throw (RequestRefusal.malformed "noncanonical launch claim plan")
                            let signatures ← decodeSignatures signaturesBytes
                            let ingress ← IO.ofExcept <|
                              ApplicationLifecycleLaunchClaimAuthoring.assemble pinnedConfig.expectedSeed plan signatures
                            unless ingress.length ≤ FnEvidenceCodec.maxHostFrameBytes do
                              throw (IO.userError "launch claim ingress exceeds host frame bound")
                            return ((69 : UInt8), ingress)
                        | 70 =>
                            let some management := settings.lifecycleManagement
                              | return ((255 : UInt8), failure .operationRejected "application-lifecycle-launch-completion-author"
                                  "lifecycle management identity is not configured")
                            let (selectorBytes, payload) ← splitPair payload
                            let selector ← IO.ofExcept (LifecycleSelector.parse selectorBytes)
                            let session ← sessionWalked pinnedConfig state
                            let plan ← IO.ofExcept <|
                              (← ApplicationLifecycleLaunchCompletionAuthoring.prepareRequestVerified
                                pinnedConfig session.verified (selector.completionPin management) payload)
                            let bytes := ApplicationLifecycleLaunchCompletionAuthoring.planCodec.encode plan
                            unless bytes.length ≤ FnEvidenceCodec.maxHostFrameBytes do
                              throw (IO.userError "launch completion plan exceeds host frame bound")
                            return ((70 : UInt8), bytes)
                        | 71 =>
                            let (planBytes, signaturesBytes) ← splitPair payload
                            let some plan := ApplicationLifecycleLaunchCompletionAuthoring.planCodec.decode
                                planBytes
                              | throw (RequestRefusal.malformed "noncanonical launch completion plan")
                            let signatures ← decodeSignatures signaturesBytes
                            let ingress ← IO.ofExcept <|
                              ApplicationLifecycleLaunchCompletionAuthoring.assemble plan signatures
                            unless ingress.length ≤ FnEvidenceCodec.maxHostFrameBytes do
                              throw (IO.userError "launch completion ingress exceeds host frame bound")
                            return ((71 : UInt8), ingress)
                        | 206 =>
                            let some management := settings.lifecycleManagement
                              | return ((255 : UInt8), failure .operationRejected "failed-start-recovery"
                                  "lifecycle management identity is not configured")
                            let (selectorBytes, payload) ← splitPair payload
                            let selector ← IO.ofExcept (LifecycleSelector.parse selectorBytes)
                            let session ← sessionWalked pinnedConfig state
                            let plan ← IO.ofExcept <| (← ApplicationFailedStartEndpoint.prepare
                              pinnedConfig session.verified (selector.completionPin management) payload)
                            let bytes := ApplicationFailedStartRecoveryAuthoring.planCodec.encode plan
                            unless bytes.length ≤ FnEvidenceCodec.maxHostFrameBytes do
                              throw (IO.userError "failed START recovery plan exceeds host frame bound")
                            return ((206 : UInt8), bytes)
                        | 207 =>
                            let (planBytes, signatureBytes) ← splitPair payload
                            let some plan := ApplicationFailedStartRecoveryAuthoring.planCodec.decode planBytes
                              | throw (RequestRefusal.malformed "noncanonical failed START recovery plan")
                            let signatures ← decodeSignatures signatureBytes
                            let ingress ← IO.ofExcept <| ApplicationFailedStartEndpoint.assemble plan signatures
                            unless ingress.length ≤ FnEvidenceCodec.maxHostFrameBytes do
                              throw (IO.userError "failed START recovery ingress exceeds host frame bound")
                            return ((207 : UInt8), ingress)
                        | 208 =>
                            return ((208 : UInt8), outcomeCodec.encode
                              (← applicationFailedStartRecoverySubmitSession pinnedConfig state payload))
                        | 209 =>
                            let session ← sessionWalked pinnedConfig state
                            return ((209 : UInt8), outcomeCodec.encode
                              (NativeHost.publicSubmissionOutcome (ApplicationFailedStartEndpoint.lookup session.verified payload)))
                        | 74 =>
                            let session ← sessionWalked pinnedConfig state
                            let plan ← IO.ofExcept <|
                              ApplicationAgentLifetimeGrantAuthoring.prepareRequestLoaded
                                session.verified payload
                            let bytes := ApplicationAgentLifetimeGrantAuthoring.planCodec.encode plan
                            unless bytes.length ≤ FnEvidenceCodec.maxHostFrameBytes do
                              throw (IO.userError "agent lifetime grant plan exceeds host frame bound")
                            return ((74 : UInt8), bytes)
                        | 75 =>
                            let (planBytes, signaturesBytes) ← splitPair payload
                            let some plan := ApplicationAgentLifetimeGrantAuthoring.planCodec.decode
                                planBytes
                              | throw (RequestRefusal.malformed "noncanonical agent lifetime grant plan")
                            let signatures ← decodeSignatures signaturesBytes
                            let session ← sessionWalked pinnedConfig state
                            let ingress ← IO.ofExcept <|
                              ApplicationAgentLifetimeGrantAuthoring.assembleCurrent
                                session.verified plan signatures
                            unless ingress.length ≤ FnEvidenceCodec.maxHostFrameBytes do
                              throw (IO.userError "agent lifetime grant ingress exceeds host frame bound")
                            return ((75 : UInt8), ingress)
                        | 35 =>
                            let outcome ← if settings.carryRegistry.isSome then
                              carriedApplicationLookup pinnedConfig state carriedState settings payload
                            else applicationDispatchLookupSession pinnedConfig state payload
                            return (35, outcomeCodec.encode outcome)
                        | 36 =>
                            let prepared ← if settings.carryRegistry.isSome then do
                              let session ← sessionCarriedWalked pinnedConfig state carriedState settings
                              pure (ApplicationDispatchAuthoring.prepareRequestSuffix
                                pinnedConfig session.verified payload)
                            else do
                              let session ← sessionWalked pinnedConfig state
                              pure (ApplicationDispatchAuthoring.prepareRequestVerified
                                pinnedConfig session.verified payload)
                            match prepared with
                            | .ok plan => return (36, ApplicationDispatchAuthoring.planCodec.encode plan)
                            | .error detail => return (255, failure .operationRejected
                                "application-dispatch-author" detail)
                        | 82 =>
                            let plan ← if settings.carryRegistry.isSome then do
                              let session ← sessionCarriedWalked pinnedConfig state carriedState settings
                              IO.ofExcept (ApplicationGrainSessionEnrollmentAuthoring.prepareRequestSuffix
                                pinnedConfig session.verified payload)
                            else do
                              let session ← sessionWalked pinnedConfig state
                              IO.ofExcept (ApplicationGrainSessionEnrollmentAuthoring.prepareRequestVerified
                                pinnedConfig session.verified payload)
                            let bytes := ApplicationGrainSessionEnrollmentAuthoring.planCodec.encode plan
                            unless bytes.length ≤ FnEvidenceCodec.maxHostFrameBytes do
                              throw (IO.userError "session enrollment plan exceeds host frame bound")
                            return ((82 : UInt8), bytes)
                        | 83 =>
                            let (planBytes, signaturesBytes) ← splitPair payload
                            let some plan := ApplicationGrainSessionEnrollmentAuthoring.planCodec.decode
                                planBytes
                              | throw (RequestRefusal.malformed "noncanonical session enrollment plan")
                            let signatures ← decodeSignatures signaturesBytes
                            let ingress ← if settings.carryRegistry.isSome then do
                              let session ← sessionCarriedWalked pinnedConfig state carriedState settings
                              IO.ofExcept (ApplicationGrainSessionEnrollmentAuthoring.assembleCurrentSuffix
                                pinnedConfig session.verified plan signatures)
                            else do
                              let session ← sessionWalked pinnedConfig state
                              IO.ofExcept (ApplicationGrainSessionEnrollmentAuthoring.assembleCurrent
                                pinnedConfig session.verified plan signatures)
                            unless ingress.length ≤ FnEvidenceCodec.maxHostFrameBytes do
                              throw (IO.userError "session enrollment ingress exceeds host frame bound")
                            return ((83 : UInt8), ingress)
                        | 86 =>
                            let (observationBytes, commandBytes) ← splitPair payload
                            let opened ← sessionOpened pinnedConfig state
                            let plan ← match ← NativeHost.enrollmentPlanAuthorizedLoaded
                                pinnedConfig opened observationBytes commandBytes with
                              | .ok plan => pure plan
                              | .error refusal =>
                                  return ((255 : UInt8), refusalFrame "enrollment-plan" refusal)
                            let bytes := ParticipantKeyEnrollment.signingPlanCodec.encode plan
                            unless bytes.length ≤ FnEvidenceCodec.maxHostFrameBytes do
                              throw (IO.userError "participant enrollment plan exceeds host frame bound")
                            return ((86 : UInt8), bytes)
                        | 87 =>
                            let (planBytes, signaturesBytes) ← splitPair payload
                            -- pair(sponsor, possession ‖ [next public key ‖ its co-signature]):
                            -- the second half is 64 bytes, or 160 for a pre-rotated record.
                            let (sponsorSignature, rest) ← splitPair signaturesBytes
                            unless rest.length = 64 ∨ rest.length = 160 do
                              throw (IO.userError "enrollment signatures: possession (64) and, for a pre-rotated record, next key (32) and co-signature (64)")
                            let possessionSignature := rest.take 64
                            let nextPublicKey := (rest.drop 64).take 32
                            let nextSignature := rest.drop 96
                            let some plan := ParticipantKeyEnrollment.signingPlanCodec.decode
                                planBytes
                              | throw (RequestRefusal.malformed "noncanonical participant enrollment plan")
                            let ingress ← IO.ofExcept (NativeHost.enrollmentAssemble plan
                              sponsorSignature possessionSignature nextPublicKey nextSignature)
                            unless ingress.length ≤ FnEvidenceCodec.maxHostFrameBytes do
                              throw (IO.userError "participant enrollment ingress exceeds host frame bound")
                            return ((87 : UInt8), ingress)
                        | 92 =>
                            let (observationBytes, commandBytes) ← splitPair payload
                            let opened ← sessionOpened pinnedConfig state
                            let plan ← match ← NativeHost.provisionPlanAuthorizedLoaded
                                pinnedConfig opened observationBytes commandBytes with
                              | .ok plan => pure plan
                              | .error refusal =>
                                  return ((255 : UInt8), refusalFrame "provision-plan" refusal)
                            let bytes := ParticipantFactoryProvisioning.signingPlanCodec.encode plan
                            unless bytes.length ≤ FnEvidenceCodec.maxHostFrameBytes do
                              throw (IO.userError "participant provisioning plan exceeds host frame bound")
                            return ((92 : UInt8), bytes)
                        | 93 =>
                            let (planBytes, sponsorSignature) ← splitPair payload
                            let some plan := ParticipantFactoryProvisioning.signingPlanCodec.decode
                                planBytes
                              | throw (RequestRefusal.malformed "noncanonical participant provisioning plan")
                            let ingress ← IO.ofExcept (NativeHost.provisionAssemble plan
                              sponsorSignature)
                            unless ingress.length ≤ FnEvidenceCodec.maxHostFrameBytes do
                              throw (IO.userError "participant provisioning ingress exceeds host frame bound")
                            return ((93 : UInt8), ingress)
                        | 48 | 49 | 58 | 59 =>
                            let some custody := settings.agentDispatchFixed
                              | return ((255 : UInt8), failure .operationRejected "application-agent-dispatch-author"
                                  "agent dispatch operator pin is not configured")
                            agentDispatchAuthorSession pinnedConfig state custody.selectors
                              operation payload
                        | 78 | 79 | 80 | 81 =>
                            let custody ← IO.ofExcept settings.lifetimeDispatchPins
                            if custody.isEmpty then
                              return ((255 : UInt8), failure .operationRejected "application-agent-lifetime-author"
                                "lifetime dispatch operator pin is not configured")
                            agentLifetimeDispatchAuthorSession pinnedConfig state
                              custody operation payload
                        | _ => throw (IO.userError "unsupported native host operation")
                      catch error =>
                        if operation == 151 || operation == 153 then
                          return ((255 : UInt8), failure .operationRejected "carried-history"
                            "retained historical request refused")
                        else return ((255 : UInt8), failure .operationRejected "fn-session" s!"{error}")
                  let meteringProfile := profileDescription pinnedConfig
                    (← IO.ofExcept settings.providerMeteringPin)
                    (← IO.ofExcept settings.providerServicePins)
                  let applicationDispatch := fun routeBound payload output =>
                    if settings.carryRegistry.isSome then
                      carriedApplicationSubmit pinnedConfig state carriedState settings routeBound payload output
                    else dispatchApplicationSubmitSession pinnedConfig state payload output routeBound
                  serveSession pinnedConfig state meteringProfile
                    (← IO.ofExcept settings.providerRoutes) fnDispatch applicationDispatch
                    (← IO.getStdin) (← IO.getStdout)
          pure 0
      | "bootstrap", [path] =>
          IO.ofExcept (← NativeHost.bootstrap config (← readBytes path))
          pure 0
      | "store-bench", [] =>
          storeBench config
          pure 0
      | "well-ledger", [output] =>
          let ledger ← IO.ofExcept (← NativeHost.wellLedger config)
          writeJson output (Minidregg.Host.Json.wellLedgerJson ledger)
          pure 0
      | "pay-ledger", [output] =>
          let ledger ← IO.ofExcept (← NativeHost.payLedger config)
          writeJson output (Minidregg.Host.Json.payLedgerJson ledger)
          pure 0
      | "pay-enrol-ids", [miniKey, output] =>
          -- PAY P3b-2: the identities a self-enrollment derives from a Mini key.
          writeJson output
            (← IO.ofExcept (Minidregg.Host.Json.payEnrolIdsJson config.deployment.domain miniKey))
          pure 0
      | "pay-enrol-probe", [input, output] =>
          -- PAY P3b: the whole self-enrollment decision on a JSON-described
          -- pay cell, with both memo signatures checked by the pinned native
          -- verifier (Ed25519 mini-sig, SSHSIG ssh-sig). Reads no Store.
          withPinnedSignature config fun pinnedConfig => do
            let probe ← IO.ofExcept (Minidregg.Host.Json.payEnrolProbe (← readJson input))
            let mint := ((PayCell.tariffOf probe.store).map (·.mint)).getD []
            let verified ← match probe.observation.memo with
              | .present bytes =>
                  match PayEnrolMemo.parse bytes with
                  | .ok memo =>
                      match ← PayEnrolSignatureIO.verifyNative pinnedConfig.signature mint
                          probe.observation.address memo with
                      | .ok checked => pure (some checked.verified)
                      | .error error => throw (IO.userError s!"native verifier: {repr error}")
                  | .error _ => pure none
              | _ => pure none
            let decision := PayEnrolDecision.decideEnrol probe.store probe.price probe.tip
              probe.observation (verified.getD ⟨false, false⟩) probe.subjectTaken
            writeJson output (Minidregg.Host.Json.payEnrolDecisionJson verified decision)
            pure 0
      | "pay-job", [job, output] =>
          let some job := job.toNat? | throw (IO.userError "pay-job: JOB must be a natural")
          let view ← IO.ofExcept (← NativeHost.payJob config job)
          writeJson output (Minidregg.Host.Json.payJobJson view)
          pure 0
      | "job-money-explain", [command] =>
          -- The operator's local reading of a job-money command: the receiver's own
          -- preparation on the Store as it is, its refusal named (public submissions stay blind).
          let bytes ← IO.FS.readBinFile command
          IO.println (← IO.ofExcept (← NativeHost.jobMoneyExplain config bytes.toList))
          pure 0
      | "pay-purse", [task, output] =>
          let some task := task.toNat? | throw (IO.userError "pay-purse: TASK must be a natural")
          let purse ← IO.ofExcept (← NativeHost.payPurse config task)
          writeJson output (Minidregg.Host.Json.payPurseJson purse)
          pure 0
      | "object-roster-inspect", [input, output] =>
          let bytes ← readBoundedBytes input maxFrame
          writeJson output (← IO.ofExcept (objectRosterJson bytes))
          pure 0
      | "object-audience-roster", [sourceObservation, catalogObservation, plannedPath, rosterPath, output] =>
          withPinnedSignature config fun pinnedConfig => do
            let planned ← IO.ofExcept (Minidregg.Host.Json.audienceState "$" (← readJson plannedPath))
            let rosterBytes ← readBoundedBytes rosterPath maxFrame
            let session ← IO.ofExcept (← NativeHostSession.start pinnedConfig)
            let state ← IO.mkRef (some session)
            let walked ← sessionWalked pinnedConfig state
            let (audience, roster) ← IO.ofExcept (← NativeHost.objectAudienceRosterLoaded pinnedConfig
              walked.target walked.verified (← readBoundedBytes sourceObservation maxFrame)
              (← readBoundedBytes catalogObservation maxFrame) rosterBytes planned)
            writeJson output (checkedObjectRosterJson audience roster rosterBytes)
            pure 0
      | "object-audience", [observationPath, output] =>
          withPinnedSignature config fun pinnedConfig => do
            let session ← IO.ofExcept (← NativeHostSession.start pinnedConfig)
            let state ← IO.mkRef (some session)
            let walked ← sessionWalked pinnedConfig state
            let signed ← readBoundedBytes observationPath maxFrame
            let result ← NativeHost.objectAudienceLoaded pinnedConfig walked.target walked.verified signed
            let view ← match result with
              | .ok view => pure view
              | .error reason => throw (IO.userError s!"object audience observation refused: {repr reason}")
            writeJson output (objectAudienceJson view)
            pure 0
      | "audit", options =>
          -- `--receipts FILE` writes every receipt the re-admission recomputed,
          -- in order, each in the canonical receipt codec: the control that an
          -- audit-path change left every original-ingress receipt byte-identical.
          let receiptsOut ← match options with
            | [] => pure none
            | ["--receipts", path] => pure (some path)
            | _ => throw (IO.userError "usage: audit [--receipts FILE]")
          withPinnedSignature config fun pinnedConfig => do
            if settings.carryRegistry.isSome && receiptsOut.isSome then
              throw (IO.userError "audit --receipts is not available for a carried registry")
            let (count, index, links) ← if settings.carryRegistry.isSome then do
              let opened ← IO.ofExcept (← NativeHost.openExisting pinnedConfig)
              let registry ← loadCarryRegistry settings
              let custody ← IO.ofExcept (← RetainedSegmentInspection.validate pinnedConfig
                opened.durable registry)
              let walked ← IO.ofExcept (← CarriedNativeHostSession.start pinnedConfig opened.durable custody)
              pure (walked.verified.opened.durable.height, walked.verified.opened.durable.index,
                 walked.verified.opened.durable.links)
            else do
              let (receipts, index, links) ← IO.ofExcept (← NativeHost.audit pinnedConfig)
              if let some path := receiptsOut then
                writeBytes path (receipts.flatMap NativeHostCodec.receiptStream.encode)
              pure (receipts.length, index, links)
            IO.println s!"audited {count} accepted records: every signed ingress re-admitted at its original prefix"
            IO.println s!"index {(presenceIndexJson index).compress}"
            IO.println s!"links {(linkIndexJson links).compress}"
            pure 0
      | "checkpoint-differential", [height] =>
          let some h := height.toNat? | throw (IO.userError "checkpoint-differential: HEIGHT must be decimal")
          let (cached, full, stored) ← IO.ofExcept
            (← DurableReceiverIO.checkpointDifferential config.transport ResourceBirthCodec.rootBytes h)
          let storedVerdict := match stored with
            | none => "no stored checkpoint at this height"
            | some bytes => if bytes == cached then "stored checkpoint equal" else "stored checkpoint DIFFERS"
          IO.println s!"height {h}: cached seal {cached.length} bytes; full seal equal: {cached == full}; {storedVerdict}"
          pure (if cached == full && stored.all (· == cached) then 0 else 1)
      | "presence-index", [] =>
          let (base, height, index) ← IO.ofExcept (← NativeHost.presenceIndex config)
          IO.println s!"opened log height {height} from the checkpoint at {base} plus {height - base} replayed records"
          IO.println s!"index {(presenceIndexJson index).compress}"
          pure 0
      | "reserve-birth-plan", [input, output] =>
          withPinnedSignature config fun pinnedConfig => do
            let request ← readBoundedBytes input maxFrame
            let opened ← IO.ofExcept (← NativeHost.openExisting pinnedConfig)
            let plan ← IO.ofExcept (← Minidregg.Host.NativeReserveBirthAuthoring.authorWireLoaded pinnedConfig opened request)
            unless plan.length ≤ maxFrame do
              throw (IO.userError "reserve birth plan exceeds host frame bound")
            writeBytes output plan
            pure 0
      | "reserve-birth-assemble", [input, output] =>
          let request ← readBoundedBytes input maxFrame
          let call ← IO.ofExcept (NativeHostReserveBirth.assembleWire request)
          unless call.length ≤ maxFrame do
            throw (IO.userError "reserve birth call exceeds host frame bound")
          writeBytes output call
          pure 0
      | "prepare", [input, output] =>
          let plan ← IO.ofExcept (← NativeHost.prepare config (← readBytes input))
          writeBytes output (signingPlanCodec.encode plan)
          pure 0
      | "enroll-key-plan", [observationPath, commandPath, output] =>
          withPinnedSignature config fun pinnedConfig => do
            let observation ← readBoundedBytes observationPath maxFrame
            let command ← readBoundedBytes commandPath maxFrame
            let plan ← IO.ofExcept (← NativeHost.enrollmentPlan pinnedConfig
              observation command)
            let bytes := ParticipantKeyEnrollment.signingPlanCodec.encode plan
            unless bytes.length ≤ maxFrame do
              throw (IO.userError "participant enrollment plan exceeds host frame bound")
            writeBytes output bytes
            pure 0
      | "enroll-key-assemble", [planPath, sponsorPath, possessionPath, nextPath, nextSignaturePath,
          output] =>
          let planBytes ← readBoundedBytes planPath maxFrame
          let some plan := ParticipantKeyEnrollment.signingPlanCodec.decode planBytes
            | throw (RequestRefusal.malformed "noncanonical participant enrollment plan")
          let sponsor ← readBoundedBytes sponsorPath 64
          let possession ← readBoundedBytes possessionPath 64
          let next ← readBoundedBytes nextPath 32
          let nextSignature ← readBoundedBytes nextSignaturePath 64
          let ingress ← IO.ofExcept (NativeHost.enrollmentAssemble plan sponsor possession
            next nextSignature)
          unless ingress.length ≤ maxFrame do
            throw (IO.userError "participant enrollment ingress exceeds host frame bound")
          writeBytes output ingress
          pure 0
      | "enroll-key-submit", [input, output] =>
          withPinnedSignature config fun pinnedConfig => do
            let ingress ← readBoundedBytes input maxFrame
            writeBytes output (outcomeCodec.encode
              (← NativeHost.enrollmentSubmit pinnedConfig ingress))
            pure 0
      | "enroll-key-lookup", [input, output] =>
          withPinnedSignature config fun pinnedConfig => do
            let ingress ← readBoundedBytes input maxFrame
            writeBytes output (outcomeCodec.encode
              (← NativeHost.enrollmentLookup pinnedConfig ingress))
            pure 0
      | "application-share-issue-plan", [input, output] =>
          let opened ← IO.ofExcept (← NativeHost.openExisting config)
          let request ← readBoundedBytes input FnEvidenceCodec.maxHostFrameBytes
          let plan ← IO.ofExcept <|
            ApplicationShareIssueAuthoring.prepareRequestLoaded config opened request
          let bytes := ApplicationShareIssueAuthoring.planCodec.encode plan
          unless bytes.length ≤ FnEvidenceCodec.maxHostFrameBytes do
            throw (IO.userError "share issue plan exceeds host frame bound")
          writeBytes output bytes
          pure 0
      | "application-share-issue-assemble", [planPath, signaturesPath, output] =>
          let planBytes ← readBoundedBytes planPath FnEvidenceCodec.maxHostFrameBytes
          let some plan := ApplicationShareIssueAuthoring.planCodec.decode planBytes
            | throw (RequestRefusal.malformed "noncanonical share issue signing plan")
          let signatures ← decodeSignatures
            (← readBoundedBytes signaturesPath FnEvidenceCodec.maxHostFrameBytes)
          let ingress ← IO.ofExcept <|
            ApplicationShareIssueAuthoring.assemble plan signatures
          unless ingress.length ≤ FnEvidenceCodec.maxHostFrameBytes do
            throw (IO.userError "share issue ingress exceeds host frame bound")
          writeBytes output ingress
          pure 0
      | "application-grain-share-issue-plan", [input, output] =>
          let opened ← IO.ofExcept (← NativeHost.openExisting config)
          let request ← readBoundedBytes input FnEvidenceCodec.maxHostFrameBytes
          let plan ← IO.ofExcept <|
            ApplicationShareIssueGrainAuthoring.prepareRequestLoaded config opened request
          let bytes := ApplicationShareIssueGrainAuthoring.planCodec.encode plan
          unless bytes.length ≤ FnEvidenceCodec.maxHostFrameBytes do
            throw (IO.userError "grain share issue plan exceeds host frame bound")
          writeBytes output bytes
          pure 0
      | "application-grain-share-issue-assemble", [planPath, signaturesPath, output] =>
          let planBytes ← readBoundedBytes planPath FnEvidenceCodec.maxHostFrameBytes
          let some plan := ApplicationShareIssueGrainAuthoring.planCodec.decode planBytes
            | throw (RequestRefusal.malformed "noncanonical grain share issue signing plan")
          let signatures ← decodeSignatures
            (← readBoundedBytes signaturesPath FnEvidenceCodec.maxHostFrameBytes)
          let ingress ← IO.ofExcept <|
            ApplicationShareIssueGrainAuthoring.assemble plan signatures
          unless ingress.length ≤ FnEvidenceCodec.maxHostFrameBytes do
            throw (IO.userError "grain share issue ingress exceeds host frame bound")
          writeBytes output ingress
          pure 0
      | "challenge-batch", [input, output] =>
          let opened ← IO.ofExcept (← NativeHost.openExisting config)
          writeBytes output (← IO.ofExcept
            (← NativeHost.challengeBatchLoaded config opened (← readBoundedBytes input maxFrame)))
          pure 0
      | "query-batch", [input, output] =>
          let opened ← IO.ofExcept (← NativeHost.openExisting config)
          writeBytes output (← IO.ofExcept
            (← NativeHost.queryBatchLoaded config opened (← readBoundedBytes input maxFrame)))
          pure 0
      | "challenge", [input, signature, output] =>
          let challenge ← IO.ofExcept
            (← NativeHost.challenge config (← readBytes input) (← readBytes signature))
          writeBytes output (NativeObservationCodec.challengeCodec.encode challenge)
          pure 0
      | "observe-assemble", [challengePath, signaturesPath, output] =>
          let some challenge := NativeObservationCodec.challengeCodec.decode (← readBytes challengePath)
            | throw (RequestRefusal.malformed "noncanonical observation challenge")
          let signaturesCodec := ResourceBirthCodec.strictCodec (StreamCodec.list bytesStream).toLawful
          let some signatures := signaturesCodec.decode (← readBytes signaturesPath)
            | throw (RequestRefusal.malformed "noncanonical signature list")
          let signed ← IO.ofExcept (NativeObservationCodec.assemble challenge signatures)
          writeBytes output (NativeObservationCodec.signedCodec.encode signed)
          pure 0
      | "query", [input, output] =>
          writeBytes output (← IO.ofExcept (← NativeHost.query config (← readBytes input)))
          pure 0
      | "pin-plan-height", [planPath, output] =>
          let some plan := signingPlanCodec.decode (← readBytes planPath)
            | throw (RequestRefusal.malformed "noncanonical signing plan")
          let pinned ← IO.ofExcept (NativePlanHeight.pin plan)
          writeBytes output (signingPlanCodec.encode pinned)
          pure 0
      | "assemble", [planPath, signaturesPath, output] =>
          let some plan := signingPlanCodec.decode (← readBytes planPath)
            | throw (RequestRefusal.malformed "noncanonical signing plan")
          let signaturesCodec := ResourceBirthCodec.strictCodec (StreamCodec.list bytesStream).toLawful
          let some signatures := signaturesCodec.decode (← readBytes signaturesPath)
            | throw (RequestRefusal.malformed "noncanonical signature list")
          let call ← IO.ofExcept (NativeHost.assemble plan signatures)
          writeBytes output (callCodec.encode call)
          pure 0
      | "submit", [input, output] =>
          writeBytes output (outcomeCodec.encode (← NativeHost.submit config (← readBytes input)))
          pure 0
      | "law-sat", [input, output] =>
          let value ← IO.ofExcept (LawSatWire.lawSatReply (← readBytes input))
          writeBytes output value.compress.toUTF8.toList
          pure 0
      | "dry-run", [observationPath, signaturesPath, output] =>
          let signatures ← decodeSignatures (← readBytes signaturesPath)
          let opened ← IO.ofExcept (← NativeHost.openExisting config)
          match ← DryRun.dryRunLoaded config opened (← readBytes observationPath) signatures with
          | .admitted plan =>
              writeBytes output (signingPlanCodec.encode plan)
              pure 0
          | .stopped outcome =>
              writeBytes output (outcomeCodec.encode outcome)
              IO.eprintln "dry run stopped; the outcome frame is in the output file"
              pure 3
      | "lookup", [input, output] =>
          writeBytes output (outcomeCodec.encode (← NativeHost.lookup config (← readBytes input)))
          pure 0
      | "selected-release-submit", [input, output] =>
          withPinnedSignature config fun pinnedConfig => do
            let session ← IO.ofExcept (← NativeHostSession.start pinnedConfig)
            let state ← IO.mkRef (some session)
            let ingress ← readBoundedBytes input maxFrame
            writeBytes output (outcomeCodec.encode
              (← selectedReleaseSubmitSession pinnedConfig state ingress))
            pure 0
      | "selected-release-lookup", [input, output] =>
          withPinnedSignature config fun pinnedConfig => do
            let session ← IO.ofExcept (← NativeHostSession.start pinnedConfig)
            let state ← IO.mkRef (some session)
            let ingress ← readBoundedBytes input maxFrame
            writeBytes output (outcomeCodec.encode
              (← selectedReleaseLookupSession pinnedConfig state ingress))
            pure 0
      | "application-lifecycle-begin-submit", [input, output] =>
          withPinnedSignature config fun pinnedConfig => do
            let session ← IO.ofExcept (← NativeHostSession.start pinnedConfig)
            let state ← IO.mkRef (some session)
            let ingress ← readBoundedBytes input maxFrame
            writeBytes output (outcomeCodec.encode
              (← applicationLifecycleBeginSubmitSession pinnedConfig state ingress))
            pure 0
      | "application-lifecycle-begin-lookup", [input, output] =>
          withPinnedSignature config fun pinnedConfig => do
            let session ← IO.ofExcept (← NativeHostSession.start pinnedConfig)
            let state ← IO.mkRef (some session)
            let ingress ← readBoundedBytes input maxFrame
            writeBytes output (outcomeCodec.encode
              (← applicationLifecycleBeginLookupSession pinnedConfig state ingress))
            pure 0
      | "application-lifecycle-claim-lookup", [input, output] =>
          withPinnedSignature config fun pinnedConfig => do
            let session ← IO.ofExcept (← NativeHostSession.start pinnedConfig)
            let state ← IO.mkRef (some session)
            let ingress ← readBoundedBytes input maxFrame
            writeBytes output (outcomeCodec.encode
              (← applicationLifecycleClaimLookupSession pinnedConfig state ingress))
            pure 0
      | "application-lifecycle-completion-submit", [input, output] =>
          withPinnedSignature config fun pinnedConfig => do
            let session ← IO.ofExcept (← NativeHostSession.start pinnedConfig)
            let state ← IO.mkRef (some session)
            let ingress ← readBoundedBytes input maxFrame
            writeBytes output (outcomeCodec.encode
              (← applicationLifecycleCompletionSubmitSession pinnedConfig state ingress))
            pure 0
      | "application-lifecycle-completion-lookup", [input, output] =>
          withPinnedSignature config fun pinnedConfig => do
            let session ← IO.ofExcept (← NativeHostSession.start pinnedConfig)
            let state ← IO.mkRef (some session)
            let ingress ← readBoundedBytes input maxFrame
            writeBytes output (outcomeCodec.encode
              (← applicationLifecycleCompletionLookupSession pinnedConfig state ingress))
            pure 0
      | "diagnose-completion", [input, output] =>
          -- Operator-local admission diagnosis only. This does not derive an
          -- intent, send a CAS, or return a receipt or physical permit.
          withPinnedSignature config fun pinnedConfig => do
            let bytes ← readBoundedBytes input maxFrame
            let some ingress := ApplicationLifecycleCompletionV2Ingress.codec.decode bytes
              | throw (RequestRefusal.malformed "noncanonical launch-bound v2 completion ingress")
            let session ← IO.ofExcept (← NativeHostSession.startWalked pinnedConfig)
            let result ← NativeHostReplay.admitCompletionV2Verified session.verified ingress
            let (status, detail) := match result with
              | .ok _ => ("admitted", "")
              | .error detail => ("rejected", detail)
            unless detail.toUTF8.size ≤ 512 do
              throw (IO.userError "completion admission diagnostic exceeds bound")
            writeJson output (Lean.Json.mkObj
              [("type", toJson "application-lifecycle-completion-diagnostic-v1"),
               ("status", toJson status),
               ("detail", toJson detail),
               ("acceptedCount", toJson (toString session.verified.opened.durable.image.accepted.length))])
            pure 0
      | "selected-source-publication-submit", [input, output] =>
          withPinnedSignature config fun pinnedConfig => do
            let session ← IO.ofExcept (← NativeHostSession.start pinnedConfig)
            let state ← IO.mkRef (some session)
            let ingress ← readBoundedBytes input maxFrame
            writeBytes output (outcomeCodec.encode
              (← selectedSourcePublicationSubmitSession pinnedConfig state ingress))
            pure 0
      | "selected-source-publication-lookup", [input, output] =>
          withPinnedSignature config fun pinnedConfig => do
            let session ← IO.ofExcept (← NativeHostSession.start pinnedConfig)
            let state ← IO.mkRef (some session)
            let ingress ← readBoundedBytes input maxFrame
            writeBytes output (outcomeCodec.encode
              (← selectedSourcePublicationLookupSession pinnedConfig state ingress))
            pure 0
      | "application-share-issue-submit", [input, output] =>
          withPinnedSignature config fun pinnedConfig => do
            let session ← IO.ofExcept (← NativeHostSession.start pinnedConfig)
            let state ← IO.mkRef (some session)
            let ingress ← readBoundedBytes input maxFrame
            writeBytes output (outcomeCodec.encode
              (← applicationShareIssueSubmitSession pinnedConfig state ingress))
            pure 0
      | "application-share-issue-lookup", [input, output] =>
          withPinnedSignature config fun pinnedConfig => do
            let session ← IO.ofExcept (← NativeHostSession.start pinnedConfig)
            let state ← IO.mkRef (some session)
            let ingress ← readBoundedBytes input maxFrame
            writeBytes output (outcomeCodec.encode
              (← applicationShareIssueLookupSession pinnedConfig state ingress))
            pure 0
      | "application-grain-share-issue-submit", [input, output] =>
          withPinnedSignature config fun pinnedConfig => do
            let session ← IO.ofExcept (← NativeHostSession.start pinnedConfig)
            let state ← IO.mkRef (some session)
            let ingress ← readBoundedBytes input maxFrame
            writeBytes output (outcomeCodec.encode
              (← applicationGrainShareIssueSubmitSession pinnedConfig state ingress))
            pure 0
      | "application-grain-share-issue-lookup", [input, output] =>
          withPinnedSignature config fun pinnedConfig => do
            let session ← IO.ofExcept (← NativeHostSession.start pinnedConfig)
            let state ← IO.mkRef (some session)
            let ingress ← readBoundedBytes input maxFrame
            writeBytes output (outcomeCodec.encode
              (← applicationGrainShareIssueLookupSession pinnedConfig state ingress))
            pure 0
      | "selected-release-source-plan", [packetPath, capabilityText, specPath,
          headerPath, rootPath] =>
          withPinnedSignature config fun pinnedConfig => do
            let session ← IO.ofExcept (← NativeHostSession.start pinnedConfig)
            let packet ← readBoundedBytes packetPath maxFrame
            let capability ← IO.ofExcept (exactDecimal "delegate capability" capabilityText)
            let plan ← IO.ofExcept (FnSelectiveReleaseSourceAuthoring.planLoaded
              pinnedConfig session.opened packet ⟨capability⟩)
            writeBytes specPath plan.specBytes
            writeBytes headerPath plan.headerBytes
            IO.FS.writeFile rootPath (toString plan.sourceRoot.value ++ "\n")
            pure 0
      | "selected-release-source-assemble", [specPath, headerPath, signaturePath, output] =>
          let spec ← readBoundedBytes specPath maxFrame
          let header ← readBoundedBytes headerPath maxFrame
          let signature ← readBoundedBytes signaturePath 64
          let ingress ← IO.ofExcept (FnSelectiveReleaseSourceAuthoring.assemble spec header signature)
          writeBytes output ingress
          pure 0
      | "selected-release-source-check", [ingressPath, articlePath] =>
          let ingress ← readBoundedBytes ingressPath maxFrame
          let article ← readBoundedBytes articlePath FnEvidenceCodec.maxSourceBytes
          IO.ofExcept (FnSelectiveReleaseSourceAuthoring.checkIngressArticle ingress article)
          pure 0
      | "selected-release-check-preimage", [input, output] =>
          let preimage ← readBoundedBytes input (FnEvidenceCodec.maxCarrierBytes + 4096)
          let release ← IO.ofExcept (FnSelectiveReleaseAuthoring.checkPreimage preimage)
          writeBytes output (FnSelectiveRelease.signedPreimage release)
          pure 0
      -- Selection-only: this emits a candidate preimage, not publication authority.
      | "selected-release-prepare", [input, output] =>
          withPinnedSignature config fun pinnedConfig => do
            let session ← IO.ofExcept (← NativeHostSession.start pinnedConfig)
            let sourceBytes ← readBoundedBytes input maxFrame
            let some source := String.fromUTF8? sourceBytes.toByteArray
              | throw (IO.userError "selected-release request is not UTF-8")
            let selected ← IO.ofExcept
              (← FnSelectiveReleaseAuthoring.prepareJsonLoaded pinnedConfig session.opened source)
            writeBytes output selected.preimage
            pure 0
      | "selected-release-assemble", [preimagePath, signaturePath, fromMailbox, date,
          subject, packetPath, articlePath] =>
          let preimage ← readBoundedBytes preimagePath (FnEvidenceCodec.maxCarrierBytes + 4096)
          let signature ← readBoundedBytes signaturePath 64
          let (packet, article) ← IO.ofExcept
            (FnSelectiveReleaseAuthoring.assemble preimage signature fromMailbox date subject)
          writeBytes packetPath packet
          writeBytes articlePath article
          pure 0
      | "selected-release-ingress", [packetPath, capabilityText,
          targetText, output] =>
          let packet ← readBoundedBytes packetPath maxFrame
          let capability ← IO.ofExcept (exactDecimal "capability" capabilityText)
          let target ← IO.ofExcept (exactDecimal "target root" targetText)
          let ingress ← IO.ofExcept
            (FnSelectiveReleaseAuthoring.assembleIngress packet ⟨capability⟩ ⟨target⟩)
          writeBytes output ingress
          pure 0
      | "selected-release-fn-poll",
          [fnBinary, scopePath, controlPath, capabilityText,
           targetText, cursorPath, reportPath, sourcePath, packetPath,
           ingressPath, resultPath] =>
          selectedReleaseFnPoll fnBinary scopePath controlPath capabilityText
            targetText cursorPath reportPath sourcePath packetPath
            ingressPath resultPath
          pure 0
      | "selected-release-fn-legacy-poll",
          [fnBinary, scopePath, controlPath, expectedArticlePath,
           capabilityText, targetText, cursorPath, reportPath,
           storedPath, packetPath, ingressPath, resultPath] =>
          selectedReleaseFnLegacyPoll fnBinary scopePath controlPath
            expectedArticlePath capabilityText targetText
            cursorPath reportPath storedPath packetPath ingressPath resultPath
          pure 0
      | "selected-release-fn-ack",
          [cursorPath, reportPath, transaction, coveragePath, resultPath] =>
          withPinnedSignature config fun pinnedConfig =>
            withFnPollService settings fun selected => do
              let some service := selected
                | throw (IO.userError "selected-release fn service is not configured")
              selectedReleaseFnAck pinnedConfig service cursorPath reportPath
                transaction coveragePath resultPath
      | "fn-empty-page-ack",
          [cursorPath, reportPath, coveragePath, resultPath] =>
          withPinnedSignature config fun pinnedConfig =>
            withFnPollService settings fun selected => do
              let some service := selected
                | throw (IO.userError "empty fn service is not configured")
              selectedEmptyFnAck pinnedConfig service cursorPath reportPath
                coveragePath resultPath
      | "fn-frontier-request", [kind, transaction, outputPath] =>
          let releaseKey ← if kind == "selected" then do
              let id ← IO.ofExcept (exactDecimal "selected Mini transaction" transaction)
              pure (some (⟨id⟩ : Minidregg.Theory.TypedAuthorization.Digest))
            else if kind == "empty" && transaction == "-" then pure none
            else throw (IO.userError "fn frontier request kind must be selected or empty")
          selectedFnNewPaths [outputPath]
          writeBytes outputPath (fnFrontierPlanRequestCodec.encode releaseKey)
          pure 0
      | "fn-frontier-export", [planPath, cursorPath, reportPath, sourcePath] =>
          selectedFnNewPaths [cursorPath, reportPath, sourcePath]
          let bytes ← readBoundedBytes planPath FnEvidenceCodec.maxHostFrameBytes
          let some plan := FnConsumerFrontierPlan.planCodec.decode bytes
            | throw (RequestRefusal.malformed "noncanonical fn frontier signing plan")
          let _ ← IO.ofExcept plan.proposal
          writeBytes cursorPath plan.cursorBytes
          writeBytes reportPath plan.reportBytes
          writeBytes sourcePath plan.sourceBytes
          pure 0
      | "fn-frontier-plan",
          [kind, transaction, planPath, cursorPath, reportPath, sourcePath] =>
          withPinnedSignature config fun pinnedConfig =>
            withFnPollService settings fun selected => do
              let some service := selected
                | throw (IO.userError "fn frontier service is not configured")
              selectedFnNewPaths [planPath, cursorPath, reportPath, sourcePath]
              let releaseKey ← if kind == "selected" then do
                  let id ← IO.ofExcept (exactDecimal "selected Mini transaction" transaction)
                  pure (some (⟨id⟩ : Minidregg.Theory.TypedAuthorization.Digest))
                else if kind == "empty" && transaction == "-" then pure none
                else throw (IO.userError "fn frontier plan kind must be selected or empty")
              let session ← IO.ofExcept (← NativeHostSession.start pinnedConfig)
              let state ← IO.mkRef (some session)
              let plan ← fnFrontierPrepareSession pinnedConfig state service releaseKey
              writeBytes planPath (FnConsumerFrontierPlan.planCodec.encode plan)
              writeBytes cursorPath plan.cursorBytes
              writeBytes reportPath plan.reportBytes
              writeBytes sourcePath plan.sourceBytes
              pure 0
      | "fn-frontier-assemble", [planPath, signaturePath, outputPath] =>
          withPinnedSignature config fun pinnedConfig =>
            withFnPollService settings fun selected => do
              let some service := selected
                | throw (IO.userError "fn frontier service is not configured")
              let planBytes ← readBoundedBytes planPath FnEvidenceCodec.maxHostFrameBytes
              let some plan := FnConsumerFrontierPlan.planCodec.decode planBytes
                | throw (RequestRefusal.malformed "noncanonical fn frontier signing plan")
              let signature ← readBoundedBytes signaturePath 64
              let releaseKey := plan.selected.map (fun spec => spec.evidence.releaseKey)
              let session ← IO.ofExcept (← NativeHostSession.start pinnedConfig)
              let state ← IO.mkRef (some session)
              let current ← fnFrontierPrepareSession pinnedConfig state service releaseKey
              unless current == plan do
                throw (IO.userError "fn frontier poll or Mini history changed before assembly")
              let opened ← sessionOpened pinnedConfig state
              let ingress ← IO.ofExcept <| FnConsumerFrontierPlan.assembleSignature
                pinnedConfig opened plan signature
              selectedFnNewPaths [outputPath]
              writeBytes outputPath ingress
              pure 0
      | "fn-selected-poll-submit", [input, output] =>
          withPinnedSignature config fun pinnedConfig => do
            let session ← IO.ofExcept (← NativeHostSession.start pinnedConfig)
            let state ← IO.mkRef (some session)
            let ingress ← readBoundedBytes input 16384
            writeBytes output (outcomeCodec.encode
              (← fnSelectedPollSubmitSession pinnedConfig state ingress))
            pure 0
      | "fn-selected-poll-lookup", [input, output] =>
          withPinnedSignature config fun pinnedConfig => do
            let session ← IO.ofExcept (← NativeHostSession.start pinnedConfig)
            let state ← IO.mkRef (some session)
            let ingress ← readBoundedBytes input 16384
            writeBytes output (outcomeCodec.encode
              (← fnSelectedPollLookupSession pinnedConfig state ingress))
            pure 0
      | "fn-empty-poll-submit", [input, output] =>
          withPinnedSignature config fun pinnedConfig => do
            let session ← IO.ofExcept (← NativeHostSession.start pinnedConfig)
            let state ← IO.mkRef (some session)
            let ingress ← readBoundedBytes input 12288
            writeBytes output (outcomeCodec.encode
              (← fnEmptyPollSubmitSession pinnedConfig state ingress))
            pure 0
      | "fn-empty-poll-lookup", [input, output] =>
          withPinnedSignature config fun pinnedConfig => do
            let session ← IO.ofExcept (← NativeHostSession.start pinnedConfig)
            let state ← IO.mkRef (some session)
            let ingress ← readBoundedBytes input 12288
            writeBytes output (outcomeCodec.encode
              (← fnEmptyPollLookupSession pinnedConfig state ingress))
            pure 0
      | "export-evidence", [input, output] =>
          let call ← readBoundedBytes input FnEvidenceCodec.maxCallBytes
          let package ← IO.ofExcept (← FnEvidence.exportPackage config call)
          writeBytes output package
          pure 0
      | "verify-evidence", [input, output] =>
          let package ← readBoundedBytes input FnEvidenceCodec.maxPackageBytes
          let receipt ← IO.ofExcept (← FnEvidence.verify config package)
          writeJson output (evidenceReceiptJson receipt)
          pure 0
      | "grain-origin-prepare", [requestPath, packagePath, outputRoot] =>
          let requestBytes ← readBoundedBytes requestPath 8192
          let some requestText := String.fromUTF8? requestBytes.toByteArray
            | throw (IO.userError "grain origin request is not UTF-8")
          let requestJson ← IO.ofExcept <|
            Minidregg.Host.Json.parse requestText
          let request ← IO.ofExcept (GrainOriginCommand.decodeRequest requestJson)
          let package ← readBoundedBytes packagePath FnEvidenceCodec.maxPackageBytes
          withPinnedSignature config fun pinnedConfig => do
            let prepared ← IO.ofExcept (← GrainOriginPreparation.prepareForDisclosure
              pinnedConfig package request.context request.selection request.disclosureIntent)
            let directory := System.FilePath.mk outputRoot
            let sourcePath := directory / "source.eml"
            let scopePath := directory / "scope.json"
            let source := prepared.rendered.source
            let scope := (GrainOriginCommand.scopeJson prepared).pretty
            -- `mkdir` claims the final path exclusively. Make it private before
            -- writing full-prefix bytes; the operator retains custody of the
            -- parent and any same-UID writers thereafter.
            IO.FS.createDir directory
            IO.setAccessRights directory
              { user := { read := true, write := true, execution := true } }
            IO.FS.writeBinFile sourcePath source.toByteArray
            IO.setAccessRights sourcePath
              { user := { read := true, write := true } }
            IO.FS.writeFile scopePath scope
            IO.setAccessRights scopePath
              { user := { read := true, write := true } }
            unless sameBytes source (← IO.FS.readBinFile sourcePath).toList &&
                (← IO.FS.readFile scopePath) == scope do
              throw (IO.userError "grain origin preparation output changed before exact readback")
            pure 0
      | "portable-verify-fn", [pinPath, claimPath, carrierPath, sourcePath, packagePath, resultPath] =>
          let pinJson ← readJson pinPath
          let claimJson ← readJson claimPath
          IO.ofExcept (requireExactFields "fn pin"
            ["fnBinary", "mlPublicKey", "principal", "edPublicKey", "mlPublicKeyHex"] pinJson)
          IO.ofExcept (requireExactFields "fn claim"
            ["sourceIdentity", "messageId", "groups"] claimJson)
          let pin : FnPortablePin ← IO.ofExcept (fromJson? pinJson)
          let claim : FnPortableClaim ← IO.ofExcept (fromJson? claimJson)
          let (_, verified, extracted) ← verifyFnPortable pin claim carrierPath
          let receipt ← IO.ofExcept (← FnEvidence.verify config extracted.package)
          writeBytes sourcePath verified.source
          writeBytes packagePath extracted.package
          writeJson resultPath <| Lean.Json.mkObj
            [("type", toJson "verified-fn-portable-mini-e1-v1"),
             ("sourceIdentity", toJson (Minidregg.Host.Json.encodeHex verified.sourceIdentity)),
             ("principal", toJson (Minidregg.Host.Json.encodeHex verified.principal)),
             ("edPublicKey", toJson (Minidregg.Host.Json.encodeHex verified.edPublicKey)),
             ("mlPublicKey", toJson (Minidregg.Host.Json.encodeHex verified.mlPublicKey)),
             ("messageId", toJson extracted.messageId),
             ("groups", toJson extracted.groups),
             ("portableAuthorship", toJson "verified"),
             ("storeAdmission", toJson "unestablished"),
             ("miniOrigin", evidenceReceiptJson receipt)]
          pure 0
      | "consumer-verify-poll-files",
          [pinPath, scopePath, claimPath, cursorPath, reportPath,
           carrierPath, resultPath] =>
          let pinJson ← readJson pinPath
          let scopeJson ← readJson scopePath
          let claimJson ← readJson claimPath
          IO.ofExcept (requireExactFields "fn pin"
            ["fnBinary", "mlPublicKey", "principal", "edPublicKey", "mlPublicKeyHex"] pinJson)
          IO.ofExcept (requireExactFields "fn poll scope"
            ["history", "incarnation", "consumer", "principal", "query",
             "queryVersion", "viewVersion", "registrationEpoch"] scopeJson)
          IO.ofExcept (requireExactFields "fn claim"
            ["sourceIdentity", "messageId", "groups"] claimJson)
          let pin : FnPortablePin ← IO.ofExcept (fromJson? pinJson)
          let scope : FnPollScopePin ← IO.ofExcept (fromJson? scopeJson)
          let claim : FnPortableClaim ← IO.ofExcept (fromJson? claimJson)
          let (cursor, report, projected, _, _, extracted) ←
            verifyFnPollFiles pin scope claim cursorPath reportPath carrierPath
          let receipt ← IO.ofExcept (← FnEvidence.verify config extracted.package)
          writeJson resultPath <| Lean.Json.mkObj
            [("type", toJson "fn-consumer-poll-files-joined-v1"),
             ("sourceIdentity", toJson
               (Minidregg.Host.Json.encodeHex projected.sourceIdentity)),
             ("storeSequence", toJson (toString projected.sequence)),
             ("storeTransactionId", toJson (toString projected.transactionId)),
             ("cursorOctets", toJson cursor.length),
             ("reportOctets", toJson report.length),
             ("portableAuthorship", toJson "verified"),
             ("storeAdmission", toJson "unestablished-from-files"),
             ("miniOrigin", evidenceReceiptJson receipt)]
          pure 0
      | "portable-consumer-decide",
          [originPath, pinPath, claimPath, policyPath,
           carrierPath, intentPath, resultPath] =>
          let origin := (← loadSettings originPath).config
          let pinJson ← readJson pinPath
          let claimJson ← readJson claimPath
          let policyJson ← readJson policyPath
          IO.ofExcept (requireExactFields "fn pin"
            ["fnBinary", "mlPublicKey", "principal", "edPublicKey", "mlPublicKeyHex"] pinJson)
          IO.ofExcept (requireExactFields "fn claim"
            ["sourceIdentity", "messageId", "groups"] claimJson)
          IO.ofExcept (requireExactFields "consumer policy"
            ["application", "subject", "target", "capability"] policyJson)
          let pin : FnPortablePin ← IO.ofExcept (fromJson? pinJson)
          let claim : FnPortableClaim ← IO.ofExcept (fromJson? claimJson)
          let policySource : ConsumerPolicySource ← IO.ofExcept (fromJson? policyJson)
          let started : Nat ← IO.monoNanosNow
          let (carrier, verified, extracted) ← verifyFnPortable pin claim carrierPath
          let afterFn : Nat ← IO.monoNanosNow
          let receipt ← IO.ofExcept (← FnEvidence.verify origin extracted.package)
          let originPackage ← IO.ofExcept (FnEvidenceCodec.decodeChecked extracted.package)
          unless originPackage.originalReceipt == receipt do
            throw (IO.userError "portable origin receipt differs from re-admitted package")
          let afterOrigin : Nat ← IO.monoNanosNow
          let policy := policySource.policy
          let opened ← IO.ofExcept (← NativeHost.openExisting config)
          let afterConsumer : Nat ← IO.monoNanosNow
          let probeTarget : DeclaredResourceController.Target :=
            ⟨.object, policy.target, policy.capability, 1, ⟨0⟩,
              .content ⟨[]⟩, none, none, none⟩
          let targetRoot ← IO.ofExcept <| (do
            let .present cell := opened.directory.directory.slots policy.target
              | throw "portable consumer target is absent"
            let some pre := DeclaredResourceController.selectTarget
              config.deployment probeTarget cell
              | throw "portable consumer target is not a valid content resource"
            pure pre.root : Except String Minidregg.Theory.TypedAuthorization.Digest)
          let report := portableConsumerReport policy
            targetRoot verified carrier
            extracted.package originPackage
          let gateway ← requireGateway config
          let decision ← IO.ofExcept (FnConsumerOperation.evaluateVerified config
            gateway policy report receipt opened)
          let afterDecision : Nat ← IO.monoNanosNow
          let intent := decision.intent report
          let intentBytes := intent.map NativeObservationCodec.intentCodec.encode
          let afterEncoding : Nat ← IO.monoNanosNow
          writeJson resultPath <| Lean.Json.mkObj
            [("type", toJson "fn-portable-consumer-decision-v1"),
             ("portableAuthorship", toJson "verified"),
             ("storeAdmission", toJson "unestablished"),
             ("sourceIdentity", toJson (Minidregg.Host.Json.encodeHex verified.sourceIdentity)),
             ("application", toJson policySource.application),
             ("operation", toJson (String.fromUTF8! report.operation.toByteArray)),
             ("miniOrigin", evidenceReceiptJson receipt),
             ("timingNs", Lean.Json.mkObj
               [("fnPortableAndExtraction", toJson (toString (afterFn - started))),
                ("miniOriginReplay", toJson (toString (afterOrigin - afterFn))),
                ("miniConsumerReplay", toJson (toString (afterConsumer - afterOrigin))),
                ("grantAndDecision", toJson (toString (afterDecision - afterConsumer))),
                ("intentEncoding", toJson (toString (afterEncoding - afterDecision)))]),
             ("decision", consumerDecisionJson decision)]
          match intentBytes with
          | some bytes =>
              writeBytes intentPath bytes
              pure 0
          | none =>
              match decision with
              | .refused _ => pure 1
              | _ => pure 0
      | "poll-consumer-decide",
          [originPath, pinPath, scopePath, claimPath, policyPath,
           cursorPath, reportPath, carrierPath, intentPath, resultPath] =>
          runPollConsumerDecision config none originPath pinPath scopePath
            claimPath policyPath cursorPath reportPath carrierPath intentPath resultPath
      | "consumer-poll-decide",
          [originPath, pinPath, scopePath, claimPath, policyPath,
           controlPath, cursorPath, reportPath, carrierPath,
           intentPath, resultPath] =>
          let pinJson ← readJson pinPath
          let scopeJson ← readJson scopePath
          IO.ofExcept (requireExactFields "fn pin"
            ["fnBinary", "mlPublicKey", "principal", "edPublicKey", "mlPublicKeyHex"] pinJson)
          IO.ofExcept (requireExactFields "fn poll scope"
            ["history", "incarnation", "consumer", "principal", "query",
             "queryVersion", "viewVersion", "registrationEpoch"] scopeJson)
          let pin : FnPortablePin ← IO.ofExcept (fromJson? pinJson)
          let scope : FnPollScopePin ← IO.ofExcept (fromJson? scopeJson)
          let (polledCursor, polledEvent, polledCarrier) ←
            invokeFnConsumerPoll pin.fnBinary scope controlPath
              cursorPath reportPath carrierPath
          let exitCode ← runPollConsumerDecision config
            (some (pin.fnBinary, controlPath)) originPath pinPath
            scopePath claimPath policyPath cursorPath reportPath carrierPath
            intentPath resultPath
          unless polledCursor == (← readBoundedBytes cursorPath 346) &&
              sameBytes polledEvent (← readBoundedBytes reportPath FnEvidenceCodec.maxStorePollEventBytes) &&
              sameBytes polledCarrier (← readBoundedBytes carrierPath FnEvidenceCodec.maxCarrierBytes) do
            throw (IO.userError "fn poll output changed before Mini decision completed")
          pure exitCode
      | "reply-consumer-poll-decide",
          [originPath, rPinPath, rClaimPath, rCarrierPath,
           qPinPath, scopePath, qClaimPath, policyPath, controlPath,
           cursorPath, reportPath, carrierPath, intentPath, resultPath] =>
          runReplyConsumerPollDecision config originPath rPinPath rClaimPath
            rCarrierPath qPinPath scopePath qClaimPath policyPath controlPath
            cursorPath reportPath carrierPath intentPath resultPath
      | "reply-consumer-export-result",
          [transaction, resultPath, inboxPath, cursorPath, reportPath] =>
          let gateway ← requireGateway config
          let transactionId ← IO.ofExcept (exactDecimal "Mini transaction ID" transaction)
          let opened ← IO.ofExcept (← NativeHost.openExisting config)
          let some record := opened.durable.image.accepted.find?
              (fun entry => entry.transactionId.value == transactionId)
            | throw (IO.userError "A reply result transaction is absent")
          let some (result, inbox) :=
              FnReplyConsumption.originalResult gateway config.deployment.domain
                config.profile.semantics record
            | throw (IO.userError "A reply result is not a canonical accepted operation")
          unless inbox.storePoll.pollCallObserved do
            throw (IO.userError "A reply result lacks an observed fn poll")
          writeBytes resultPath (FnReplyConsumption.resultCodec.encode result)
          writeBytes inboxPath (FnReplyConsumption.reportCodec.encode inbox)
          writeBytes cursorPath inbox.storePoll.cursor
          writeBytes reportPath inbox.storePoll.event
          pure 0
      | "reply-consumer-ack-poll",
          [pinPath, scopePath, controlPath, transaction,
           cursorPath, eventPath, resultPath] =>
          let gateway ← requireGateway config
          let transactionId ← IO.ofExcept (exactDecimal "Mini transaction ID" transaction)
          unless controlPath.startsWith "/" && cursorPath.startsWith "/" &&
              eventPath.startsWith "/" do
            throw (IO.userError "A reply ack paths must be absolute")
          let pinJson ← readJson pinPath
          let scopeJson ← readJson scopePath
          IO.ofExcept (requireExactFields "Q fn pin"
            ["fnBinary", "mlPublicKey", "principal", "edPublicKey", "mlPublicKeyHex"] pinJson)
          IO.ofExcept (requireExactFields "A fn scope"
            ["history", "incarnation", "consumer", "principal", "query",
             "queryVersion", "viewVersion", "registrationEpoch"] scopeJson)
          let pin : FnPortablePin ← IO.ofExcept (fromJson? pinJson)
          let scope : FnPollScopePin ← IO.ofExcept (fromJson? scopeJson)
          let opened ← IO.ofExcept (← NativeHost.openExisting config)
          let some record := opened.durable.image.accepted.find?
              (fun entry => entry.transactionId.value == transactionId)
            | throw (IO.userError "A reply result transaction is absent")
          let some (_, inbox) := FnReplyConsumption.originalResult gateway
              config.deployment.domain config.profile.semantics record
            | throw (IO.userError "A reply result is not a reopened accepted operation")
          let stored := inbox.storePoll
          unless stored.pollCallObserved && stored.controlBinding ==
              FnConsumerOperation.pollControlBinding pin.fnBinary controlPath do
            throw (IO.userError "A reply ack control differs from durable observed poll")
          let (cursor, event, projected) ←
            projectFnPoll pin.fnBinary scope cursorPath eventPath
          unless cursor == stored.cursor && sameBytes event stored.event &&
              projected.sourceIdentity == stored.sourceIdentity &&
              projected.sequence == stored.sequence &&
              projected.transactionId == stored.transactionId &&
              projected.messageId == stored.messageId &&
              projected.verdictPrincipal == stored.verdictPrincipal &&
              projected.verdictEvent == stored.verdictEvent do
            throw (IO.userError "A reply ack pair differs from durable Mini inbox")
          let verified ← verifyReplyAckSource pin projected inbox.portableInbox.carrier inbox.replySource
          unless projected.verdictPrincipal == inbox.portableInbox.principal &&
              verified.principal == inbox.portableInbox.principal &&
              verified.edPublicKey == inbox.portableInbox.edPublicKey &&
              verified.mlPublicKey == inbox.portableInbox.mlPublicKey do
            throw (IO.userError "A reply ack principal differs from accepted Mini inbox")
          let child ← IO.Process.spawn
            { cmd := pin.fnBinary,
              args := #["--fn", "consumer", "ack", controlPath, cursorPath],
              stdin := .null, stdout := .piped, stderr := .null }
          let output ← try readBoundedLoop child.stdout 128
            catch error =>
              child.kill
              discard <| child.wait
              throw error
          let exitCode ← child.wait
          unless cursor == (← readBoundedBytes cursorPath 346) &&
              sameBytes event (← readBoundedBytes eventPath FnEvidenceCodec.maxStorePollEventBytes) do
            throw (IO.userError "A reply ack inputs changed during local call")
          let status := if exitCode == 0 && output == "consumer accepted\n".toUTF8.toList then
              "durable-accepted"
            else if exitCode == 2 then "refused"
            else if exitCode == 3 then "uncertain"
            else "transport-fault"
          writeJson resultPath <| Lean.Json.mkObj
            [("type", toJson "fn-a-reply-ack-after-mini-v1"),
             ("miniTransactionId", toJson transaction),
             ("miniResult", toJson "reopened-accepted"),
             ("fnStoreSequence", toJson (toString stored.sequence)),
             ("fnStoreTransactionId", toJson (toString stored.transactionId)),
             ("fnAck", toJson status)]
          if status == "durable-accepted" then pure 0
          else if status == "refused" then pure 2
          else if status == "uncertain" then pure 3
          else pure 4
      | "consumer-export-inbox", [transaction, inboxPath, carrierPath, resultPath] =>
          let transactionId ← IO.ofExcept (exactDecimal "transaction ID" transaction)
          let (inbox, kind, atomId) ← IO.ofExcept
            (← exportConsumerInbox config transactionId)
          writeBytes inboxPath (FnConsumerOperation.portableInboxCodec.encode inbox)
          writeBytes carrierPath inbox.carrier
          writeJson resultPath <| Lean.Json.mkObj
            [("type", toJson "retained-mini-portable-inbox-v1"),
             ("miniTransactionId", toJson transaction),
             ("kind", toJson kind),
             ("atomId", toJson (toString atomId)),
             ("sourceIdentity", toJson (Minidregg.Host.Json.encodeHex inbox.sourceIdentity)),
             ("storeAdmission", toJson "unestablished")]
          pure 0
      | "consumer-export-poll", [transaction, cursorPath, eventPath, resultPath] =>
          let transactionId ← IO.ofExcept (exactDecimal "transaction ID" transaction)
          let (poll, kind, atomId) ← IO.ofExcept
            (← exportConsumerPoll config transactionId)
          writeBytes cursorPath poll.cursor
          writeBytes eventPath poll.event
          writeJson resultPath <| Lean.Json.mkObj
            [("type", toJson "retained-mini-fn-poll-inbox-v1"),
             ("miniTransactionId", toJson transaction),
             ("kind", toJson kind),
             ("atomId", toJson (toString atomId)),
             ("sourceIdentity", toJson
               (Minidregg.Host.Json.encodeHex poll.sourceIdentity)),
             ("fnStoreSequence", toJson (toString poll.sequence)),
             ("fnStoreTransactionId", toJson (toString poll.transactionId)),
             ("pollCallObserved", toJson poll.pollCallObserved),
             ("controlBinding", toJson
               (Minidregg.Host.Json.encodeHex poll.controlBinding)),
             ("fnStoreAttribution", toJson "unestablished-from-files")]
          pure 0
      | "consumer-ack-poll",
          [pinPath, scopePath, controlPath, transaction,
           cursorPath, eventPath, resultPath] =>
          let transactionId ← IO.ofExcept (exactDecimal "Mini transaction ID" transaction)
          unless controlPath.startsWith "/" && cursorPath.startsWith "/" &&
              eventPath.startsWith "/" do
            throw (IO.userError "fn control and poll paths must be absolute")
          let pinJson ← readJson pinPath
          let scopeJson ← readJson scopePath
          IO.ofExcept (requireExactFields "fn pin"
            ["fnBinary", "mlPublicKey", "principal", "edPublicKey", "mlPublicKeyHex"] pinJson)
          IO.ofExcept (requireExactFields "fn poll scope"
            ["history", "incarnation", "consumer", "principal", "query",
             "queryVersion", "viewVersion", "registrationEpoch"] scopeJson)
          let pin : FnPortablePin ← IO.ofExcept (fromJson? pinJson)
          let scope : FnPollScopePin ← IO.ofExcept (fromJson? scopeJson)
          let (stored, kind, _) ← IO.ofExcept (← exportConsumerPoll config transactionId)
          unless kind == "operation" && stored.pollCallObserved do
            throw (IO.userError "Mini has no durable operation from observed fn poll")
          unless stored.controlBinding ==
              FnConsumerOperation.pollControlBinding pin.fnBinary controlPath do
            throw (IO.userError "fn ack control endpoint differs from observed poll")
          let (cursor, event, projected) ←
            projectFnPoll pin.fnBinary scope cursorPath eventPath
          unless cursor == stored.cursor && sameBytes event stored.event &&
              projected.sourceIdentity == stored.sourceIdentity &&
              projected.sequence == stored.sequence &&
              projected.transactionId == stored.transactionId &&
              projected.messageId == stored.messageId &&
              projected.verdictPrincipal == stored.verdictPrincipal &&
              projected.verdictEvent == stored.verdictEvent do
            throw (IO.userError "fn ack cursor/report differ from durable Mini inbox")
          let (portable, portableKind, _) ← IO.ofExcept
            (← exportConsumerInbox config transactionId)
          unless portableKind == "operation" do
            throw (IO.userError "fn ack has no accepted portable operation inbox")
          let extracted ← IO.ofExcept (FnPortableSource.extract projected.source)
          let verified ← verifyAckSource pin projected portable.carrier projected.source
          unless extracted.messageId.toUTF8.toList == stored.messageId &&
              projected.verdictPrincipal == portable.principal &&
              portable.sourceIdentity == stored.sourceIdentity &&
              verified.principal == portable.principal &&
              verified.edPublicKey == portable.edPublicKey &&
              verified.mlPublicKey == portable.mlPublicKey do
            throw (IO.userError "fn ack source metadata differs from accepted Mini inbox")
          let child ← IO.Process.spawn
            { cmd := pin.fnBinary,
              args := #["--fn", "consumer", "ack", controlPath, cursorPath],
              stdin := .null, stdout := .piped, stderr := .null }
          let output ← try readBoundedLoop child.stdout 128
            catch error =>
              child.kill
              discard <| child.wait
              throw error
          let exitCode ← child.wait
          unless cursor == (← readBoundedBytes cursorPath 346) &&
              sameBytes event (← readBoundedBytes eventPath FnEvidenceCodec.maxStorePollEventBytes) do
            throw (IO.userError "fn ack inputs changed during local control call")
          let status := if exitCode == 0 && output == "consumer accepted\n".toUTF8.toList then
              "durable-accepted"
            else if exitCode == 2 then "refused"
            else if exitCode == 3 then "uncertain"
            else "transport-fault"
          writeJson resultPath <| Lean.Json.mkObj
            [("type", toJson "fn-consumer-ack-after-mini-v1"),
             ("miniTransactionId", toJson transaction),
             ("miniOperation", toJson "reopened-accepted"),
             ("fnStoreSequence", toJson (toString stored.sequence)),
             ("fnStoreTransactionId", toJson (toString stored.transactionId)),
             ("fnAck", toJson status)]
          if status == "durable-accepted" then pure 0
          else if status == "refused" then pure 2
          else if status == "uncertain" then pure 3
          else pure 4
      | "consumer-export-reply", [transaction, replyPath] =>
          let gateway ← requireGateway config
          let transactionId ← IO.ofExcept (exactDecimal "transaction ID" transaction)
          let opened ← IO.ofExcept (← NativeHost.openExisting config)
          let some record := opened.durable.image.accepted.find?
              (fun entry => entry.transactionId.value == transactionId)
            | throw (IO.userError "exact Mini consumer transaction is absent")
          let some (binding, some _, _) :=
              FnConsumerOperation.originalBindingWithInbox gateway config.deployment.domain
                config.profile.semantics record
            | throw (IO.userError "transaction has no canonical portable Q")
          writeBytes replyPath (FnConsumerOperation.replyCodec.encode binding.reply)
          pure 0
      | "consumer-stage-reply-plan",
          [signerPath, transaction, outboxRoot, candidatePath,
           readbackPath, sourcePath, resultPath] =>
          let gateway ← requireGateway config
          unless [outboxRoot, candidatePath, readbackPath, sourcePath,
              resultPath].all (·.startsWith "/") &&
              ([(candidatePath, readbackPath), (candidatePath, sourcePath),
                (readbackPath, sourcePath)].all (fun pair => pair.1 != pair.2)) do
            throw (IO.userError "reply plan paths must be absolute and distinct")
          for path in [candidatePath, readbackPath, sourcePath, resultPath] do
            if ← (System.FilePath.mk path).pathExists then
              throw (IO.userError "reply plan output path already exists")
          let transactionId ← IO.ofExcept (exactDecimal "Mini transaction ID" transaction)
          let signerJson ← readJson signerPath
          IO.ofExcept (requireExactFields "fn reply signer"
            ["principal", "edPublicKey", "mlPublicKeyHex", "creation"] signerJson)
          let creationJson ← IO.ofExcept (signerJson.getObjVal? "creation")
          IO.ofExcept (requireExactFields "fn reply creation"
            ["fromMailbox", "newsgroup", "messageIdDomain", "date"] creationJson)
          let signer : FnReplySignerPin ← IO.ofExcept (fromJson? signerJson)
          unless signer.creation.context.valid do
            throw (IO.userError "fn reply creation context is invalid")
          let principal ← IO.ofExcept (decodeCanonicalHex "fn reply principal" signer.principal)
          let edPublicKey ← IO.ofExcept (decodeCanonicalHex "fn reply Ed25519 key" signer.edPublicKey)
          let mlPublicKey ← IO.ofExcept (decodeCanonicalHex "fn reply ML-DSA-65 key" signer.mlPublicKeyHex)
          let opened ← IO.ofExcept (← NativeHost.openExisting config)
          let some record := opened.durable.image.accepted.find?
              (fun entry => entry.transactionId.value == transactionId)
            | throw (IO.userError "exact Mini consumer transaction is absent")
          let some (binding, some _, some store) :=
              FnConsumerOperation.originalBindingWithInbox gateway config.deployment.domain
                config.profile.semantics record
            | throw (IO.userError "transaction has no canonical observed fn poll and Q")
          unless store.pollCallObserved do
            throw (IO.userError "reply plan requires durable observed fn poll")
          let selection : FnReplyPublication.Selection :=
            { domain := config.deployment.domain,
              semantics := config.profile.semantics,
              miniTransaction := record.transactionId,
              miniEvent := record.event.eventId,
              reply := binding.reply,
              parentSourceIdentity := store.sourceIdentity,
              parentMessageId := store.messageId,
              principal := principal, edPublicKey := edPublicKey,
              mlPublicKey := mlPublicKey,
              creation := signer.creation.context }
          let prepared ← IO.ofExcept selection.prepare
          writeBytes candidatePath (FnReplyPublication.preparedCodec.encode prepared)
          let publish ← IO.Process.spawn
            { cmd := settings.storageBinary,
              args := #["publish", outboxRoot, candidatePath],
              stdin := .null, stdout := .piped, stderr := .null }
          let _ ← readBoundedLoop publish.stdout 128
          let _ ← publish.wait
          let readback ← IO.Process.spawn
            { cmd := settings.storageBinary,
              args := #["read-to", outboxRoot, readbackPath],
              stdin := .null, stdout := .piped, stderr := .null }
          let _ ← readBoundedLoop readback.stdout 128
          let readbackExit ← readback.wait
          if readbackExit != 0 then
            writeJson resultPath <| Lean.Json.mkObj
              [("type", toJson "fn-reply-plan-stage-v1"),
               ("stage", toJson "uncertain")]
            pure 3
          else
            let bytes? ← try pure (some (← readBoundedBytes readbackPath 8192))
              catch _ => pure none
            let some bytes := bytes?
              | do
                  writeJson resultPath <| Lean.Json.mkObj
                    [("type", toJson "fn-reply-plan-stage-v1"),
                     ("stage", toJson "uncertain")]
                  return 3
            let some retained := FnReplyPublication.preparedCodec.decode bytes
              | do
                  writeJson resultPath <| Lean.Json.mkObj
                    [("type", toJson "fn-reply-plan-stage-v1"),
                     ("stage", toJson "uncertain")]
                  return 3
            unless retained.valid do
              writeJson resultPath <| Lean.Json.mkObj
                [("type", toJson "fn-reply-plan-stage-v1"),
                 ("stage", toJson "uncertain")]
              return 3
            let accepted := retained == prepared
            if accepted then writeBytes sourcePath retained.source
            writeJson resultPath <| Lean.Json.mkObj
              [("type", toJson "fn-reply-plan-stage-v1"),
               ("stage", toJson (if accepted then "durable-accepted" else "conflict")),
               ("miniTransactionId", toJson transaction),
               ("messageId", toJson retained.selection.messageId)]
            pure (if accepted then 0 else 2)
      | "consumer-stage-reply-sign",
          [fnPinPath, principalPath, edPublicPath, edSecretPath,
           mlSecretPath, transaction, preparedRoot, signedRoot,
           planPath, sourcePath, carrierPath, signedCandidatePath,
           signedReadbackPath, edSignaturePath, mlSignaturePath, resultPath] =>
          let gateway ← requireGateway config
          unless [principalPath, edPublicPath, edSecretPath, mlSecretPath,
              preparedRoot, signedRoot, planPath, sourcePath, carrierPath,
              signedCandidatePath, signedReadbackPath, edSignaturePath,
              mlSignaturePath, resultPath].all (·.startsWith "/") do
            throw (IO.userError "reply signer paths must be absolute")
          for path in [planPath, sourcePath, carrierPath, signedCandidatePath,
              signedReadbackPath, edSignaturePath, mlSignaturePath, resultPath] do
            if ← (System.FilePath.mk path).pathExists then
              throw (IO.userError "reply signer output path already exists")
          let transactionId ← IO.ofExcept (exactDecimal "Mini transaction ID" transaction)
          let pinJson ← readJson fnPinPath
          IO.ofExcept (requireExactFields "fn reply signing pin"
            ["fnBinary", "mlPublicKey", "principal", "edPublicKey",
             "mlPublicKeyHex"] pinJson)
          let pin : FnPortablePin ← IO.ofExcept (fromJson? pinJson)
          unless pin.fnBinary.startsWith "/" && pin.mlPublicKey.startsWith "/" do
            throw (IO.userError "fn reply signer and public key paths must be absolute")
          let principal ← IO.ofExcept (decodeCanonicalHex "fn reply principal" pin.principal)
          let edPublicKey ← IO.ofExcept (decodeCanonicalHex "fn reply Ed25519 key" pin.edPublicKey)
          let mlPublicKey ← IO.ofExcept (decodeCanonicalHex "fn reply ML-DSA-65 key" pin.mlPublicKeyHex)
          unless principal == (← readBoundedBytes principalPath 32) &&
              edPublicKey == (← readBoundedBytes edPublicPath 32) do
            throw (IO.userError "fn reply signer public files differ from pin")
          let opened ← IO.ofExcept (← NativeHost.openExisting config)
          let some record := opened.durable.image.accepted.find?
              (fun entry => entry.transactionId.value == transactionId)
            | throw (IO.userError "exact Mini consumer transaction is absent")
          let some (binding, some _, some store) :=
              FnConsumerOperation.originalBindingWithInbox gateway config.deployment.domain
                config.profile.semantics record
            | throw (IO.userError "transaction has no canonical observed fn poll and Q")
          unless store.pollCallObserved do
            throw (IO.userError "reply signing requires durable observed fn poll")
          let planRead ← IO.Process.spawn
            { cmd := settings.storageBinary,
              args := #["read-to", preparedRoot, planPath],
              stdin := .null, stdout := .piped, stderr := .null }
          let _ ← readBoundedLoop planRead.stdout 128
          let planExit ← planRead.wait
          if planExit != 0 then
            writeJson resultPath <| Lean.Json.mkObj
              [("type", toJson "fn-reply-sign-stage-v1"),
               ("stage", toJson (if planExit == 3 then "unprepared" else "uncertain"))]
            pure (if planExit == 3 then 2 else 3)
          else
            let preparedBytes? ← try pure (some (← readBoundedBytes planPath 8192))
              catch _ => pure none
            let some preparedBytes := preparedBytes?
              | do
                  writeJson resultPath <| Lean.Json.mkObj
                    [("type", toJson "fn-reply-sign-stage-v1"),
                     ("stage", toJson "uncertain")]
                  return 3
            let some prepared := FnReplyPublication.preparedCodec.decode preparedBytes
              | do
                  writeJson resultPath <| Lean.Json.mkObj
                    [("type", toJson "fn-reply-sign-stage-v1"),
                     ("stage", toJson "uncertain")]
                  return 3
            let selection : FnReplyPublication.Selection :=
              { domain := config.deployment.domain,
                semantics := config.profile.semantics,
                miniTransaction := record.transactionId,
                miniEvent := record.event.eventId,
                reply := binding.reply,
                parentSourceIdentity := store.sourceIdentity,
                parentMessageId := store.messageId,
                principal := principal, edPublicKey := edPublicKey,
                mlPublicKey := mlPublicKey,
                creation := prepared.selection.creation }
            let expected ← IO.ofExcept selection.prepare
            unless prepared.valid && prepared == expected do
              writeJson resultPath <| Lean.Json.mkObj
                [("type", toJson "fn-reply-sign-stage-v1"),
                 ("stage", toJson "conflict")]
              return 2
            let prior ← IO.Process.spawn
              { cmd := settings.storageBinary,
                args := #["read-to", signedRoot, signedReadbackPath],
                stdin := .null, stdout := .piped, stderr := .null }
            let _ ← readBoundedLoop prior.stdout 128
            let priorExit ← prior.wait
            if priorExit != 0 && priorExit != 3 then
              writeJson resultPath <| Lean.Json.mkObj
                [("type", toJson "fn-reply-sign-stage-v1"),
                 ("stage", toJson "uncertain")]
              return 3
            if priorExit == 3 then
              writeBytes sourcePath prepared.source
              let carrier ← IO.Process.spawn
                { cmd := pin.fnBinary,
                  args := #["--fn", "hybrid-sign-carrier", principalPath,
                    edPublicPath, edSecretPath, pin.mlPublicKey, mlSecretPath,
                    sourcePath, carrierPath],
                  stdin := .null, stdout := .piped, stderr := .null }
              let _ ← readBoundedLoop carrier.stdout 128
              let carrierExit ← carrier.wait
              if carrierExit != 0 then
                let stage := if carrierExit == 1 then "refused"
                  else if carrierExit == 3 then "uncertain" else "transport-fault"
                writeJson resultPath <| Lean.Json.mkObj
                  [("type", toJson "fn-reply-sign-stage-v1"),
                   ("stage", toJson stage)]
                return if carrierExit == 1 then 2 else if carrierExit == 3 then 3 else 4
              let verified ← IO.Process.spawn
                { cmd := pin.fnBinary,
                  args := #["--fn", "hybrid-verify-source", carrierPath,
                    pin.mlPublicKey],
                  stdin := .null, stdout := .piped, stderr := .null }
              let verifiedOutput ← readBoundedLoop verified.stdout
                FnEvidenceCodec.maxPortableVerifyLineBytes
              let verifiedExit ← verified.wait
              if verifiedExit != 0 then
                let stage := if verifiedExit == 1 then "refused"
                  else if verifiedExit == 3 then "uncertain" else "transport-fault"
                writeJson resultPath <| Lean.Json.mkObj
                  [("type", toJson "fn-reply-sign-stage-v1"),
                   ("stage", toJson stage)]
                return if verifiedExit == 1 then 2 else if verifiedExit == 3 then 3 else 4
              let verifiedSource ← IO.ofExcept (parseFnPortableLine
                (String.fromUTF8! verifiedOutput.toByteArray))
              unless sameBytes verifiedSource.source prepared.source &&
                  verifiedSource.principal == principal &&
                  verifiedSource.edPublicKey == edPublicKey &&
                  verifiedSource.mlPublicKey == mlPublicKey do
                throw (IO.userError "fn reply signed carrier differs from prepared key/source")
              let signer ← IO.Process.spawn
                { cmd := pin.fnBinary,
                  args := #["--fn", "hybrid-sign", principalPath,
                    edPublicPath, edSecretPath, pin.mlPublicKey, mlSecretPath,
                    sourcePath],
                  stdin := .null, stdout := .piped, stderr := .null }
              let signatureOutput ← readBoundedLoop signer.stdout 7000
              let signerExit ← signer.wait
              if signerExit != 0 then
                let stage := if signerExit == 1 then "refused"
                  else if signerExit == 3 then "uncertain" else "transport-fault"
                writeJson resultPath <| Lean.Json.mkObj
                  [("type", toJson "fn-reply-sign-stage-v1"),
                   ("stage", toJson stage)]
                return if signerExit == 1 then 2 else if signerExit == 3 then 3 else 4
              let (edSignature, mlSignature) ← IO.ofExcept (parseFnHybridSignLine
                (String.fromUTF8! signatureOutput.toByteArray))
              let candidate : FnReplyPublication.Signed :=
                ⟨prepared, verifiedSource.sourceIdentity, edSignature, mlSignature⟩
              unless candidate.valid do
                throw (IO.userError "fn reply signed artifact exceeds bound")
              writeBytes signedCandidatePath (FnReplyPublication.signedCodec.encode candidate)
              let publisher ← IO.Process.spawn
                { cmd := settings.storageBinary,
                  args := #["publish", signedRoot, signedCandidatePath],
                  stdin := .null, stdout := .piped, stderr := .null }
              let _ ← readBoundedLoop publisher.stdout 128
              let _ ← publisher.wait
              let reopened ← IO.Process.spawn
                { cmd := settings.storageBinary,
                  args := #["read-to", signedRoot, signedReadbackPath],
                  stdin := .null, stdout := .piped, stderr := .null }
              let _ ← readBoundedLoop reopened.stdout 128
              let reopenedExit ← reopened.wait
              unless reopenedExit == 0 do
                writeJson resultPath <| Lean.Json.mkObj
                  [("type", toJson "fn-reply-sign-stage-v1"),
                   ("stage", toJson "uncertain")]
                return 3
            let signedBytes? ← try pure (some (← readBoundedBytes signedReadbackPath 12288))
              catch _ => pure none
            let some signedBytes := signedBytes?
              | do
                  writeJson resultPath <| Lean.Json.mkObj
                    [("type", toJson "fn-reply-sign-stage-v1"),
                     ("stage", toJson "uncertain")]
                  return 3
            let some retained := FnReplyPublication.signedCodec.decode signedBytes
              | do
                  writeJson resultPath <| Lean.Json.mkObj
                    [("type", toJson "fn-reply-sign-stage-v1"),
                     ("stage", toJson "uncertain")]
                  return 3
            unless retained.valid do
              writeJson resultPath <| Lean.Json.mkObj
                [("type", toJson "fn-reply-sign-stage-v1"),
                 ("stage", toJson "uncertain")]
              return 3
            unless retained.prepared == prepared do
              writeJson resultPath <| Lean.Json.mkObj
                [("type", toJson "fn-reply-sign-stage-v1"),
                 ("stage", toJson "conflict")]
              return 2
            if priorExit == 0 then writeBytes sourcePath retained.prepared.source
            writeBytes edSignaturePath retained.edSignature
            writeBytes mlSignaturePath retained.mlSignature
            writeJson resultPath <| Lean.Json.mkObj
              [("type", toJson "fn-reply-sign-stage-v1"),
               ("stage", toJson "durable-accepted"),
               ("miniTransactionId", toJson transaction),
               ("messageId", toJson retained.prepared.selection.messageId),
               ("sourceIdentity", toJson
                 (Minidregg.Host.Json.encodeHex retained.sourceIdentity))]
            pure 0
      | "consumer-decide-test", [originPath, policyPath, reportPath, packagePath, intentPath, resultPath] =>
          let gateway ← requireGateway config
          let origin := (← loadSettings originPath).config
          let policySource : ConsumerPolicySource ← IO.ofExcept (fromJson? (← readJson policyPath))
          let source : ConsumerReportSource ← IO.ofExcept (fromJson? (← readJson reportPath))
          let report := source.report
            (← readBoundedBytes packagePath FnEvidenceCodec.maxPackageBytes)
          let decision ← IO.ofExcept (← FnConsumerOperation.evaluate origin config
            gateway policySource.policy report)
          writeJson resultPath (consumerDecisionJson decision)
          match decision.intent report with
          | some intent =>
              writeBytes intentPath (NativeObservationCodec.intentCodec.encode intent)
              pure 0
          | none =>
              match decision with
              | .refused _ => pure 1
              | _ => pure 0
      | _, _ => throw (IO.userError usage)
  | _ => throw (IO.userError usage)

end Minidregg.Host

def main (arguments : List String) : IO UInt32 := do
  try Minidregg.Host.run arguments
  catch error =>
    (← IO.getStderr).putStrLn s!"minidregg-host: {error}"
    pure 1
