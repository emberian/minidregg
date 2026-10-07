/- Local full-peer consent process. Settings and executable are selected by
local custody. The operator supplies proposed frames only. History is admitted
before the first full-peer consent frame: from genesis, or,
when custody offers its retained anchor (frame 228) first, natively after that
anchor once the Store is shown to extend it (`Kernel.ConsentAnchor`). Later
frames admit only the exact new suffix (`DurableReceiverIO.extendFrom`). Frame
229 returns the anchor of what this provider admitted, for custody to retain.
No protected Store is transmitted by this process. Frames 230-232 are thin
consent (`Kernel.NativeThinConsent`): they read no Store and check what custody
signs against its own command and the target views the Host served under the
member's observe grants.
-/
import Kernel.NativeClientConsent
import Kernel.NativeThinConsent
import Kernel.ConsentAnchor
import Kernel.NativeSpecializedConsent
import Kernel.NativeHostGenesis
import Compiler.GenericSimplexSourceAnchor
import Compiler.FnEvidenceCodec
import Host.SourceAgreementJson
import Host.ObjectiveInvocationSettings
import Host.RequestRefusal
import Lean.Data.Json

open Lean Minidregg.Compiler Minidregg.Compiler.NativeHostCodec
open Minidregg.Compiler.Tower256ConcreteBackend Minidregg.Kernel
namespace Minidregg.Host.ClientConsentCore
structure JointConsensusSettings where
  context : Minidregg.Compiler.GenericSimplexCodec.Context

instance : FromJson JointConsensusSettings where
  fromJson? json := do
    let value ← json.getStr?
    let bytes ← Minidregg.Host.SourceAgreementJson.decodeHex "jointConsensus" json
    unless Minidregg.Host.SourceAgreementJson.encodeHex bytes == value do
      throw "jointConsensus must use canonical lowercase hex"
    let some context := Minidregg.Compiler.GenericSimplexCodec.contextStream.toLawful.decode bytes
      | throw "jointConsensus is not a canonical Context"
    unless Minidregg.Compiler.GenericSimplexCodec.contextStream.encode context == bytes &&
        context.wellFormed do
      throw "jointConsensus Context is noncanonical or committee is not well formed"
    pure ⟨context⟩

instance : ToJson JointConsensusSettings where
  toJson pin := .str (Minidregg.Host.SourceAgreementJson.encodeHex
    (Minidregg.Compiler.GenericSimplexCodec.contextStream.encode pin.context))

structure GatewayPinSettings where
  application : String
  subject : Nat
  target : Nat
  capability : Nat
  policyAddress : String
  deriving FromJson, ToJson

structure GrainBirthTariffSettings where
  base : Nat
  perBirth : Nat
  deriving FromJson, ToJson

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
    pure ⟨← json.getObjValAs? Nat "managementSubject", ← json.getObjValAs? Nat "managementKeyId"⟩

structure Settings where
  domain : Nat
  federation : Nat
  factoryId : Nat
  resourceBookId : Nat
  authorityCellId : Nat
  issuer : Nat
  ownerBudget : Nat
  lifetime : Nat
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
  checkpointKey : Option String := none
  checkpointEvery : Option Nat := none
  jointConsensus : Option JointConsensusSettings := none
  fnGateway : Option GatewayPinSettings := none
  grainBirthTariff : Option GrainBirthTariffSettings := none
  completionCustodianKey : Option String := none
  nockFSync : Option Nat := none
  disabledEvaluators : Option (List String) := none
  lifecycleManagement : Option LifecycleManagementSettings := none
  objectiveInvocation : Option ObjectiveInvocationSettings := none
  deriving FromJson, ToJson

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
  nockFSync := settings.nockFSync.getD NativeHost.defaultNockFSync
  jointConsensus := settings.jointConsensus.map JointConsensusSettings.context
  invocationBindings := ObjectiveInvocationSettings.bindings settings.objectiveInvocation
  fnGateway := settings.fnGateway.map fun pin =>
    ⟨pin.application.toUTF8.toList, ⟨pin.subject⟩, pin.target,
      ⟨pin.capability⟩, ⟨pin.policyAddress.toNat!⟩⟩
  grainBirthTariff := settings.grainBirthTariff.map fun tariff => ⟨tariff.base, tariff.perBirth⟩
  completionCustodianKey := settings.completionCustodianKey.map fun key =>
    (SourceAgreementJson.decodeHex "completionCustodianKey" (.str key)).toOption.getD []

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


def loadSettings (path : System.FilePath) : IO Settings := do
  let json ← IO.ofExcept (SourceAgreementJson.parse (← IO.FS.readFile path))
  let object ← IO.ofExcept json.getObj?
  let allowed := ["domain", "federation", "factoryId", "resourceBookId",
    "authorityCellId", "issuer", "ownerBudget", "lifetime", "birthSlack",
    "tariffBase", "tariffPerBirth", "tariffPerGrant", "tariffPerInitialPayloadByte",
    "collector", "asset", "genesisHeight", "expectedSeed", "storageBinary",
    "storageRoot", "signatureBinary", "checkpointKey", "checkpointEvery",
    "jointConsensus", "nockFSync", "disabledEvaluators", "fnGateway",
    "grainBirthTariff", "completionCustodianKey", "lifecycleManagement", "objectiveInvocation"]
  -- A deployment config written by `mini bootstrap` spells every absent Host
  -- option as null. Null is absence; any other value of a key this provider
  -- cannot honor refuses, since it would change the semantics it verifies.
  unless object.foldl (init := true) (fun valid key value =>
      valid && (allowed.contains key || value == Json.null)) do
    throw (IO.userError "unsupported settings in client consent provider")
  let settings : Settings ← IO.ofExcept (fromJson? json)
  if let some pin := settings.fnGateway then
    let some address := pin.policyAddress.toNat? | throw (IO.userError "invalid gateway policy address")
    unless toString address == pin.policyAddress do
      throw (IO.userError "noncanonical gateway policy address")
  if let some tariff := settings.grainBirthTariff then
    unless 0 < tariff.base do throw (IO.userError "grain birth tariff base must be positive")
  if let some key := settings.completionCustodianKey then
    let bytes ← IO.ofExcept (SourceAgreementJson.decodeHex "completionCustodianKey" (.str key))
    unless bytes.length == 32 && SourceAgreementJson.encodeHex bytes == key do
      throw (IO.userError "noncanonical completion custodian key")
  IO.ofExcept settings.checkDisabledEvaluators
  IO.ofExcept settings.checkJointConsensus
  pure settings

def splitPair (payload : List UInt8) : IO (List UInt8 × List UInt8) := do
  unless payload.length ≥ 4 do throw (RequestRefusal.malformed "short native host pair frame")
  let width := payload[0]!.toNat + 256 * payload[1]!.toNat +
    65536 * payload[2]!.toNat + 16777216 * payload[3]!.toNat
  unless width ≤ payload.length - 4 do throw (RequestRefusal.malformed "invalid native host pair length")
  return ((payload.drop 4).take width, payload.drop (4 + width))

def maxFrame : Nat := FnEvidenceCodec.maxHostFrameBytes

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



/-- The retained proof is updated only by independent native admission. The
physical Store/MAC is merely an input reader, never a semantic trust source.
The basis is the full re-admission from genesis, or native admission of every
record after this client's retained anchor (`ConsentAnchor.Basis`). -/
abbrev Session (config : NativeHost.Config) := Sigma (ConsentAnchor.Basis config)

/-- The full re-admission, for consent that selects from chronology. -/
abbrev FullSession (config : NativeHost.Config) := Sigma (NativeHostReplay.Verified config)

/-- First admission. A retained anchor the Store contradicts (another genesis
log, a rolled-back head, a rewritten prefix, another root at the anchor)
refuses and terminates the provider. A suffix whose admission fails after the
anchor is re-admitted from genesis instead, which accepts or refuses it. -/
def verifyInitial (config : NativeHost.Config) (retained : Option ConsentAnchor.Anchor) :
    IO (Session config) := do
  let ⟨target, chains, chainsExact⟩ ← IO.ofExcept
    (← DurableReceiverIO.loadChained config.transport ResourceBirthCodec.rootBytes)
  if let some anchor := retained then
    match ← ConsentAnchor.resume config anchor target chains chainsExact with
    | .ok anchored => return ⟨target, .anchored anchored⟩
    | .error (.contradicted detail) => throw (IO.userError s!"consent refused: {detail}")
    | .error (.suffix _) => pure ()
  match ← NativeHostReplay.verifyLoaded config target with
  | .error failure => throw (IO.userError s!"consent prefix refused at {failure.index}: {failure.detail}")
  | .ok verified => pure ⟨target, .full verified⟩

/-- Admit only the records the Store appended since `old` (`extendFrom`: the
chain continues from the held one and every new tag verifies). An anchored
basis whose suffix admission fails is re-admitted from genesis. -/
def refresh (config : NativeHost.Config) (old : Session config) : IO (Session config) := do
  let ⟨target, seedExact, acceptedExact, logStartExact⟩ ← IO.ofExcept
    (← DurableReceiverIO.extendFrom config.transport ResourceBirthCodec.rootBytes old.1)
  if target.height = old.1.image.accepted.length then return old
  match ← old.2.extendAppended config target seedExact acceptedExact logStartExact with
  | .ok basis => pure ⟨target, basis⟩
  | .error failure =>
      match old.2 with
      | .full _ => throw (IO.userError s!"consent extension refused at {failure.index}: {failure.detail}")
      | .anchored _ =>
          match ← NativeHostReplay.verifyLoaded config target with
          | .error failure =>
              throw (IO.userError s!"consent extension refused at {failure.index}: {failure.detail}")
          | .ok verified => pure ⟨target, .full verified⟩

/-- The full re-admission of the held target; an anchored session is
re-admitted from genesis once and then held in full. -/
def upgrade (config : NativeHost.Config) (session : Session config) :
    IO (FullSession config × Session config) := do
  match ← session.2.full? config with
  | .error failure =>
      throw (IO.userError s!"consent prefix refused at {failure.index}: {failure.detail}")
  | .ok verified => pure (⟨session.1, verified⟩, ⟨session.1, .full verified⟩)

def headersBytes (headers : List (List UInt8)) : List UInt8 :=
  (Lean.toJson (headers.map SourceAgreementJson.encodeHex)).compress.toUTF8.toList

def selectedHeaders (config : NativeHost.Config) (session : Session config)
    (wanted : NativeObservationCodec.Intent) (headers : List (List UInt8)) : IO (List UInt8) := do
  let some key := Minidregg.Theory.CredentialAuthorityState.currentSigningKey session.2.opened.authority.snapshot.logical wanted.subject
    | throw (IO.userError "local custody subject has no current key")
  for bytes in headers do
    let some header := CredentialSignedEnvelopeController.headerCodec.decode bytes
      | throw (IO.userError "local planner produced a noncanonical header")
    unless header.keyId == key.keyId && header.keyEpoch == key.keyEpoch &&
        header.algorithm == key.algorithm do
      throw (IO.userError "prepared role selects another custody signer")
  pure (headersBytes headers)

def consent (config : NativeHost.Config) (session : Session config) (operation : UInt8)
    (payload : List UInt8) : IO (List UInt8) := do
  let (intentBytes, rest) ← splitPair payload
  let some wanted := NativeObservationCodec.intentCodec.decode intentBytes
    | throw (IO.userError "noncanonical retained local intent")
  let (signer, rest) ← splitPair rest
  -- Bind the selected custody key at EACH source extension, including a key
  -- change between intent signing and observation/transaction signing.
  let key ← IO.ofExcept ((NativeObservationController.intentKey
    (NativeHost.observationContext config session.2.opened) wanted.subject).mapError
    (fun _ => "local intent subject has no current signing key"))
  unless signer.length == 32 && key == signer do
    throw (IO.userError "local intent subject differs from custody signer")
  match operation with
  | 220 =>
      unless rest.isEmpty do throw (IO.userError "intent consent has unexpected trailing bytes")
      pure intentBytes
  | 221 =>
      let (signature, candidate) ← splitPair rest
      let checked ← IO.ofExcept (NativeClientConsent.checkObservation config session.2 wanted signature candidate)
      selectedHeaders config session wanted checked.headers
  | 222 =>
      let headers ← IO.ofExcept (NativeClientConsent.checkIntentPlan config session.2 wanted rest)
      selectedHeaders config session wanted headers
  | _ => throw (IO.userError "unsupported consent operation")

/-- Thin consent frames (230 intent, 231 observation, 232 plan): answered from
local custody alone, with no Store and no replay (`Kernel.NativeThinConsent`).
A refusal names what thin consent cannot show; nothing falls back to a replay
or to signing what was not checked. -/
def thinRefusal (refusal : NativeThinConsent.Refusal) : String :=
  match refusal with
  | .unsupportedPayload target what =>
      s!"thin consent cannot display this turn: target {target}: {what} unsigned"
  | other => s!"thin consent refused: {repr other}"

def displayJson (display : NativeThinConsent.Display) : Json :=
  match display.post with
  | none => Json.mkObj [("target", toJson (toString display.target)), ("read", true)]
  | some (bytes, root) => Json.mkObj [("target", toJson (toString display.target)),
      ("postRoot", toJson (toString root.value)),
      ("postBytes", toJson (SourceAgreementJson.encodeHex bytes))]

/-- A delegation's display: the signed parent id, target and child capability
bytes. The child's lineage is the kernel's copy of that parent, not shown. -/
def delegateJson (display : NativeThinConsent.DelegateDisplay) : Json :=
  Json.mkObj [("delegate", true), ("parent", toJson (toString display.parentId.value)),
    ("target", toJson (toString display.target)),
    ("childBytes", toJson (SourceAgreementJson.encodeHex display.child))]

def shownJson : NativeThinConsent.Shown → Json
  | .invocation displays => Json.arr (displays.map displayJson).toArray
  | .delegation display => Json.arr #[delegateJson display]

def thin (config : NativeHost.Config) (operation : UInt8) (payload : List UInt8) : IO (List UInt8) := do
  let (intentBytes, rest) ← splitPair payload
  let some wanted := NativeObservationCodec.intentCodec.decode intentBytes
    | throw (IO.userError "noncanonical retained local intent")
  unless NativeObservationCodec.intentCodec.encode wanted == intentBytes do
    throw (IO.userError "noncanonical retained local intent")
  let (signer, rest) ← splitPair rest
  unless signer.length == 32 do throw (IO.userError "custody signer is not an Ed25519 key")
  let semantics := config.profile.semantics
  match operation with
  | 230 =>
      unless rest.isEmpty do throw (IO.userError "intent consent has unexpected trailing bytes")
      pure intentBytes
  | 231 =>
      let (signature, candidate) ← splitPair rest
      match NativeThinConsent.checkObservationThin config.deployment semantics config.federation
          wanted signature candidate with
      | .error refusal => throw (IO.userError (thinRefusal refusal))
      | .ok headers => pure (headersBytes headers)
  | 232 =>
      let (planBytes, viewsBytes) ← splitPair rest
      let viewsCodec := ResourceBirthCodec.strictCodec (StreamCodec.list bytesStream).toLawful
      let some views := viewsCodec.decode viewsBytes
        | throw (IO.userError "noncanonical served view list")
      match NativeThinConsent.checkPlanThin config.deployment semantics config.federation
          wanted planBytes views with
      | .error refusal => throw (IO.userError (thinRefusal refusal))
      | .ok (headers, shown) =>
          pure (Json.mkObj [("headers", toJson (headers.map SourceAgreementJson.encodeHex)),
            ("display", shownJson shown)]).compress.toUTF8.toList
  | _ => throw (IO.userError "unsupported thin consent operation")

/-- Entry adapters (lifecycle families) select from the admitted chronology,
so they receive the full re-admission (`upgrade`). -/
abbrev ExtraExpected := (settings : Settings) → (config : NativeHost.Config) →
  FullSession config → UInt8 → List UInt8 → IO (List UInt8)

/-- Whether a specialized frame goes to an entry adapter, which needs the full
re-admission. A malformed frame answers `false` and refuses in `specialized`. -/
def specializedNeedsFull (payload : List UInt8) : Bool :=
  match payload.take 4 with
  | [b0, b1, b2, b3] =>
      let width := b0.toNat + 256 * b1.toNat + 65536 * b2.toNat + 16777216 * b3.toNat
      match (payload.drop 4).take width with
      | operation :: _ => 0 < width && !NativeSpecializedConsent.supported operation
      | [] => false
  | _ => false

def specialized (extraExpected : ExtraExpected) (settings : Settings) (config : NativeHost.Config)
    (session : Session config) (full : Option (FullSession config))
    (payload : List UInt8) : IO (List UInt8) := do
  let (retained, candidate) ← splitPair payload
  let operation :: request := retained | throw (IO.userError "missing retained specialized operation")
  let expected ← if NativeSpecializedConsent.supported operation then
    NativeSpecializedConsent.expectedPlanBytes config session.2 operation request
  else match full with
    | some verified => extraExpected settings config verified operation request
    | none => throw (IO.userError "entry consent adapter requires the full re-admission")
  let _ ← IO.ofExcept (NativeSpecializedConsent.checkExact expected candidate)
  pure candidate

def possession (config : NativeHost.Config) (payload : List UInt8) : IO (List UInt8) := do
  let (commandBytes, rest) ← splitPair payload
  let (selectedBytes, candidate) ← splitPair rest
  let some command := ParticipantKeyEnrollment.commandCodec.decode commandBytes
    | throw (IO.userError "noncanonical retained possession command")
  let some selectedText := String.fromUTF8? selectedBytes.toByteArray
    | throw (IO.userError "possession custody selection is not UTF-8")
  let selected ← IO.ofExcept (SourceAgreementJson.parse selectedText)
  let subjectValue ← IO.ofExcept (selected.getObjVal? "subject")
  let subjectText ← IO.ofExcept subjectValue.getStr?
  let some subject := subjectText.toNat? | throw (IO.userError "invalid possession subject")
  unless toString subject == subjectText do throw (IO.userError "noncanonical possession subject")
  let publicValue ← IO.ofExcept (selected.getObjVal? "publicKey")
  let publicKey ← IO.ofExcept (SourceAgreementJson.decodeHex "publicKey" publicValue)
  unless command.key.subject == subject && command.key.publicKey == publicKey do
    throw (IO.userError "retained enrollment command selects another possession subject or key")
  let expected := ParticipantKeyEnrollment.possessionFrame config.deployment.domain config.profile.semantics command
  let _ ← IO.ofExcept (NativeSpecializedConsent.checkExact expected candidate)
  pure expected

/-- An entry's source-derived Objective adapter consumes the independently
retained original request, reproduces its quote/execution from this exact
Verified prefix, compares the entire canonical signing plan, and binds the
selected current key. It returns only its derived headers. -/
abbrev ExtraObjective := (settings : Settings) → (config : NativeHost.Config) →
  Session config → List UInt8 → List UInt8 → String → List UInt8 → IO (List (List UInt8))

/-- Entries without an installed adapter refuse, naming the missing adapter. -/
def refuseObjective : ExtraObjective := fun _ _ _ _ _ _ _ =>
  throw (IO.userError "no source-derived Objective consent adapter is installed")

def objectiveHeaders (extraObjective : ExtraObjective) (settings : Settings)
    (config : NativeHost.Config) (session : Session config)
    (payload : List UInt8) : IO (List UInt8) := do
  let (originalRequest, rest) ← splitPair payload
  let (selectionBytes, candidate) ← splitPair rest
  unless !originalRequest.isEmpty && !candidate.isEmpty do
    throw (IO.userError "missing original Objective request or proposed plan")
  let some text := String.fromUTF8? selectionBytes.toByteArray
    | throw (IO.userError "Objective custody selection is not UTF-8")
  let selected ← IO.ofExcept (SourceAgreementJson.parse text)
  let object ← IO.ofExcept selected.getObj?
  unless object.foldl (init := true) (fun valid key _ =>
      valid && (key == "publicKey" || key == "role")) do
    throw (IO.userError "unexpected Objective custody selection field")
  let publicValue ← IO.ofExcept (selected.getObjVal? "publicKey")
  let publicText ← IO.ofExcept publicValue.getStr?
  let publicKey ← IO.ofExcept (SourceAgreementJson.decodeHex "publicKey" publicValue)
  unless publicKey.length == 32 && SourceAgreementJson.encodeHex publicKey == publicText do
    throw (IO.userError "noncanonical Objective custody public key")
  let roleValue ← IO.ofExcept (selected.getObjVal? "role")
  let role ← IO.ofExcept roleValue.getStr?
  unless !role.isEmpty && role.toUTF8.size ≤ 128 do
    throw (IO.userError "invalid Objective custody role")
  let headers ← extraObjective settings config session originalRequest publicKey role candidate
  unless !headers.isEmpty && headers.length ≤ 32 do
    throw (IO.userError "source-derived Objective adapter returned invalid header count")
  pure (headersBytes headers)

/-- Frame 228 offers custody's retained anchor before the first admission;
frame 229 returns the anchor of the current admission. Possession (226) is a
function of the retained command and the configuration, and thin consent
frames (230–232) read no Store: they admit nothing. This process serves no
codec frames: the one pure codec implementation is the Host's storeless
`codec` loop (`Host.Main.serveCodec`). Every other frame first admits the Store (`verifyInitial`
once, then `refresh`); a failed admission terminates the provider, so no cached
success survives an observed rollback, rewritten prefix, or failed suffix. -/
partial def serve (extraExpected : ExtraExpected) (extraObjective : ExtraObjective) (settings : Settings)
    (config : NativeHost.Config) (retained : Option ConsentAnchor.Anchor)
    (held : Option (Session config)) (input output : IO.FS.Stream) : IO Unit := do
  let first ← input.read 1
  if first.isEmpty then return
  let lengthWire ← readExactly input 4 first
  let length := frameLength lengthWire
  unless 0 < length && length ≤ maxFrame do throw (IO.userError "consent frame exceeds bound")
  let body ← readExactly input length
  let operation := body[0]!
  let payload := body.toList.drop 1
  if operation ≥ 230 && operation ≤ 232 || operation == 226 then
    let answer ← try pure (operation, ← if operation == 226 then possession config payload
        else thin config operation payload)
      catch error => pure (255, error.toString.toUTF8.toList)
    writeSessionFrame output answer.1 answer.2
    serve extraExpected extraObjective settings config retained held input output
  else if operation == 228 then
    if held.isSome then
      writeSessionFrame output 255
        "a retained consent anchor is offered only before the first admission".toUTF8.toList
      serve extraExpected extraObjective settings config retained held input output
    else
      match ConsentAnchor.decode payload with
      | .error detail =>
          writeSessionFrame output 255 detail.toUTF8.toList
          serve extraExpected extraObjective settings config retained held input output
      | .ok anchor =>
          writeSessionFrame output 228 []
          serve extraExpected extraObjective settings config (some anchor) held input output
  else if operation == 229 then
    match held with
    | none =>
        writeSessionFrame output 255 "no admitted prefix to anchor yet".toUTF8.toList
    | some session =>
        writeSessionFrame output 229 (ConsentAnchor.encode session.2.anchor)
    serve extraExpected extraObjective settings config retained held input output
  else
    let admitted ← match held with
      | none => verifyInitial config retained
      | some session => refresh config session
    let (full, updated) ← if operation == 224 && specializedNeedsFull payload then do
        let (full, upgraded) ← upgrade config admitted
        pure (some full, upgraded)
      else pure (none, admitted)
    let answer ← try pure (operation, ← if operation == 224 then
        specialized extraExpected settings config updated full payload
      else if operation == 227 then objectiveHeaders extraObjective settings config updated payload
      else consent config updated operation payload)
      catch error => pure (255, error.toString.toUTF8.toList)
    writeSessionFrame output answer.1 answer.2
    serve extraExpected extraObjective settings config retained (some updated) input output

def run (extraExpected : ExtraExpected) (arguments : List String)
    (extraObjective : ExtraObjective := refuseObjective) : IO UInt32 := do
  match arguments with
  | [path, "stdio"] =>
      let settings ← loadSettings path
      withPinnedSignature settings.config fun config => do
        serve extraExpected extraObjective settings config none none (← IO.getStdin) (← IO.getStdout)
        pure 0
  | _ => throw (IO.userError "usage: minidregg-client-consent CONFIG stdio")
end Minidregg.Host.ClientConsentCore
