/-
Real source fixture for four independently stored Mini agreement participants.
The initializer derives a fresh source genesis under the actual agreed runtime
profile, then binds its exact seed to the committee context. Every subsequent
setup/workdesk ingress goes through GenericSimplexSourceHarness.runCall. No supplied
record, validation callback, checked engine input, or accepted history is seeded.
This source is WIP until checked with the common receiver's qualified outputs.
-/
import Kernel.NativeHostGenesis
import Kernel.NativeHostContext
import Compiler.GenericSimplexSourceAnchor
import Verify.GenericSimplexOperatorBridge
import Lean

namespace Minidregg.Verify.NativeJointSourceFixture
open Minidregg.Theory
open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.CredentialSigningKey
open Minidregg.Compiler
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Compiler.GenericSimplexCodec
open Minidregg.Compiler.GenericSimplexIO
open Minidregg.Compiler.GenericSimplexNative
open Minidregg.Compiler.GenericSimplexParticipant
open Minidregg.Kernel
open Lean
set_option autoImplicit false

structure Helpers where
  store : System.FilePath
  signature : System.FilePath
  agreement : System.FilePath

def require (condition : Bool) (detail : String) : IO Unit :=
  unless condition do throw (IO.userError detail)

def helper (binary : System.FilePath) (args : Array String) : IO Unit := do
  let result ← IO.Process.output {cmd := binary.toString, args := args}
  require (result.exitCode == 0 && result.stderr.isEmpty)
    s!"fixture helper refused: {result.stderr}"

def privateDirectory (path : System.FilePath) : IO Unit := do
  IO.FS.createDirAll path
  helper "chmod" #["700", path.toString]

def replicaDirectory (root : System.FilePath) (index : Nat) : System.FilePath :=
  root / s!"replica-{index}"

def pairPath (root : System.FilePath) (left right : Nat) : System.FilePath :=
  root / s!"pair-{min left right}-{max left right}.key"

def native (root : System.FilePath) (helpers : Helpers) (index : Nat) : Native :=
  { binary := helpers.agreement
    journal := replicaDirectory root index / "agreement.bin"
    signingKey := replicaDirectory root index / "committee.sk"
    pairKey := pairPath root index
    storageBinary := some helpers.agreement }

def baseConfig (root : System.FilePath) (helpers : Helpers)
    (context : Context) (index : Nat) : NativeHost.Config :=
  { deployment := ⟨⟨8500⟩, 10, 11, 12⟩
    federation := ⟨9⟩
    template := {issuer := ⟨5⟩, ownerBudget := 100000, lifetime := 10000}
    tariff := ⟨3, 2, 1, 0, 99, 0⟩
    genesisHeight := 10
    expectedSeed := ⟨0⟩
    storage := { binary := helpers.store, root := replicaDirectory root index / "source", key := replicaDirectory root index / "checkpoint.key", checkpointEvery := 8 }
    signature := ⟨helpers.signature⟩
    jointControl := none
    activityControl := none
    jointConsensus := some context }

def subjectKey (subject : Nat) (bytes : List UInt8) : KeyRecord :=
  ⟨7000 + subject, 2, CredentialSignatureAdmission.ed25519Algorithm,
    subject, bytes, 0, 10000, none⟩

def genesis (config : NativeHost.Config) (alice bob : List UInt8) :
    NativeHostGenesis.Config :=
  { deployment := config.deployment
    federation := config.federation
    tariff := config.tariff
    expectedSemantics := config.profile.semantics
    issuerEpoch := 2
    genesisHeight := config.genesisHeight
    factoryPredicate := .any [.memberOf "request/creator" [7,8], .eq "request/subject" 7]
    enrollments :=
      [⟨subjectKey 7 alice, 7, ⟨41⟩, ⟨44⟩, ⟨46⟩, 100000, .all []⟩,
       ⟨subjectKey 8 bob, 8, ⟨42⟩, ⟨45⟩, ⟨47⟩, 100000, .all []⟩]
    factoryController := ⟨⟨7⟩, ⟨43⟩⟩
    meterAllowance := fun _ => 10000000
    clockTickers := []
    tailBound := 10000 }

def derive (root : System.FilePath) (helpers : Helpers) (context : Context)
    (alice bob : List UInt8) : IO (NativeHostGenesis.Built
      (baseConfig root helpers context 0).profile (genesis (baseConfig root helpers context 0) alice bob)) :=
  IO.ofExcept ((NativeHostGenesis.build (baseConfig root helpers context 0).profile
    (genesis (baseConfig root helpers context 0) alice bob)).mapError
      (fun detail => s!"fixture source genesis refused: {repr detail}"))

/-- Same explicit fresh-genesis bootstrap as NativeHost.bootstrap, factored here
so the fixture consumes the coherent Context/Genesis/Replay cohort without a
foreign Host/Main overlay. Validation and physical exact-seed readback remain. -/
def bootstrapFresh (config : NativeHost.Config) (canonicalImage : List UInt8) :
    IO (Except String Unit) := do
  match DurableReceiverIO.loadBytes ResourceBirthCodec.rootBytes config.logStart canonicalImage with
  | .error detail => return .error detail
  | .ok durable =>
      if !durable.image.accepted.isEmpty then return .error "bootstrap image contains accepted history"
      match NativeHost.validateLoaded config durable with
      | .error detail => return .error detail
      | .ok _ =>
          return ← DurableReceiverIO.bootstrap config.transport ResourceBirthCodec.rootBytes durable.image.seed

def initializeStores (root : System.FilePath) (helpers : Helpers)
    (alicePath bobPath : System.FilePath) : IO Unit := do
  require (!(← root.pathExists)) "fixture root exists; use a fresh owner-private directory"
  privateDirectory root
  let alice := (← IO.FS.readBinFile alicePath).toList
  let bob := (← IO.FS.readBinFile bobPath).toList
  require (alice.length == 32 && bob.length == 32 && alice != bob)
    "fixture requires two distinct real Ed25519 enrollment public keys"
  writePrivate (root / "subject-7.pub") alice.toByteArray
  writePrivate (root / "subject-8.pub") bob.toByteArray
  let mut publicKeys := []
  for index in List.range 4 do
    let dir := replicaDirectory root index
    privateDirectory dir
    helper helpers.agreement #["keygen", (dir / "committee.pk").toString,
      (dir / "committee.sk").toString]
    helper helpers.agreement #["mac-keygen", (dir / "checkpoint.key").toString]
    publicKeys := publicKeys ++ [(← IO.FS.readBinFile (dir / "committee.pk")).toList]
  for left in List.range 4 do
    for right in List.range 4 do
      if left ≤ right then
        helper helpers.agreement #["mac-keygen", (pairPath root left right).toString]
  let context : Context :=
    ⟨digestStream.encode ⟨8500⟩, 0, [], ⟨4,1,100000,8⟩, publicKeys⟩
  require context.wellFormed "real committee context is malformed"
  let built ← derive root helpers context alice bob
  require built.image.accepted.isEmpty "genesis unexpectedly contains accepted history"
  let bound := GenericSimplexSourceAnchor.bind context 10 built.image.seed
  writePrivate (root / "context.bin") (contextStream.encode bound).toByteArray
  writePrivate (root / "genesis.bin") (DurableReceiverCodec.encode built.image).toByteArray
  for index in List.range 4 do
    let config := {baseConfig root helpers bound index with
      expectedSeed := NativeHost.seedIdentity built.image.seed}
    require (config.runtimeParameters == (baseConfig root helpers context 0).runtimeParameters)
      "binding exact source anchor changed the normalized runtime semantics"
    IO.ofExcept (← bootstrapFresh config (DurableReceiverCodec.encode built.image))
    writePrivate (native root helpers index).journal
      (journalStream.encode (⟨bound,index,0,[],[]⟩ : Journal)).toByteArray
  IO.FS.writeFile (root / "manifest.json") (Json.mkObj
    [("state", .str "initialized-source-genesis-no-accepted-history"),
     ("participants", toJson (4 : Nat)), ("faults", toJson (1 : Nat)),
     ("subject7", toJson (7 : Nat)), ("subject8", toJson (8 : Nat)),
     ("semantics", .str (toString (baseConfig root helpers bound 0).profile.semantics.value)),
     ("expectedSeed", .str (toString (NativeHost.seedIdentity built.image.seed).value)),
     ("genesisHeight", toJson (10 : Nat)),
     ("storeBinary", .str helpers.store.toString),
     ("signatureBinary", .str helpers.signature.toString),
     ("agreementBinary", .str helpers.agreement.toString)]).compress
  IO.println "INITIALIZED four actual source stores; no source transition accepted yet"

def openReplicas (root : System.FilePath) (helpers : Helpers) :
    IO (Array GenericSimplexSourceHarness.Replica) := do
  let encoded := (← IO.FS.readBinFile (root / "context.bin")).toList
  let some context := contextStream.toLawful.decode encoded
    | throw (IO.userError "invalid source fixture context")
  require (contextStream.encode context == encoded && context.wellFormed)
    "noncanonical source fixture context"
  let alice := (← IO.FS.readBinFile (root / "subject-7.pub")).toList
  let bob := (← IO.FS.readBinFile (root / "subject-8.pub")).toList
  let built ← derive root helpers context alice bob
  require (context.instanceBytes == GenericSimplexSourceAnchor.anchorBytes 10 built.image.seed)
    "source fixture context does not bind this exact source genesis"
  let mut replicas := #[]
  for index in List.range 4 do
    let config := {baseConfig root helpers context index with
      expectedSeed := NativeHost.seedIdentity built.image.seed}
    let loaded ← IO.ofExcept (← DurableReceiverIO.load config.physicalTransport ResourceBirthCodec.rootBytes)
    let verified ← IO.ofExcept ((← NativeHostReplay.verifyLoaded config loaded).mapError
      (fun failure => s!"source fixture replay refused: {failure.detail}"))
    let participant ← IO.ofExcept (← openParticipant config (native root helpers index)
      context ⟨loaded,verified⟩)
    replicas := replicas.push ⟨config,participant⟩
  return replicas

def runCall (root : System.FilePath) (helpers : Helpers)
    (ingress : System.FilePath) (fuel : Nat) : IO Unit := do
  let replicas ← openReplicas root helpers
  let _ ← GenericSimplexSourceHarness.runCallChecked fuel replicas (← IO.FS.readBinFile ingress).toList
  pure ()

/-- Operator output is a native Outcome frame in a private file. Diagnostic
stdout never substitutes for a receipt. Original signed call bytes are retained. -/
def submitCall (root : System.FilePath) (helpers : Helpers)
    (callFile outputFile : System.FilePath) (fuel : Nat) : IO Unit := do
  let replicas ← openReplicas root helpers
  let (_, outcome) ← GenericSimplexOperatorBridge.submit fuel replicas
    (← IO.FS.readBinFile callFile).toList
  writePrivate outputFile (NativeHostCodec.outcomeCodec.encode outcome).toByteArray

end Minidregg.Verify.NativeJointSourceFixture

open Minidregg.Verify.NativeJointSourceFixture

def main (args : List String) : IO Unit := do
  match args with
  | ["init", root, store, signature, agreement, alice, bob] =>
      initializeStores root ⟨store,signature,agreement⟩ alice bob
  | ["run", root, store, signature, agreement, ingress, fuel] =>
      let some fuel := fuel.toNat? | throw (IO.userError "invalid finite service fuel")
      runCall root ⟨store,signature,agreement⟩ ingress fuel
  | ["submit-call", root, store, signature, agreement, callFile, outputFile, fuel] =>
      let some fuel := fuel.toNat? | throw (IO.userError "invalid finite service fuel")
      submitCall root ⟨store,signature,agreement⟩ callFile outputFile fuel
  | _ => throw (IO.userError "usage: NativeJointSourceFixture init ROOT STORE SIGNATURE AGREEMENT ALICE_PUB BOB_PUB | run ROOT STORE SIGNATURE AGREEMENT ORIGINAL_SIGNED_CALL FUEL")
