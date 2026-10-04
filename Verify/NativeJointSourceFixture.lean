/-
Real source fixture for four independently stored Mini agreement participants.
The initializer derives a fresh source genesis under the actual agreed runtime
profile, then binds its exact seed to the committee context. Each replica then
runs as its own standing `serve-replica` process; a client only places the exact
original call with `await-call` and waits for four identical receipts. No supplied
record, validation callback, checked engine input, or accepted history is seeded.
This source is WIP until checked with the common receiver's qualified outputs.
-/
import Kernel.NativeHostGenesis
import Kernel.NativeHostContext
import Compiler.GenericSimplexSourceAnchor
import Verify.GenericSimplexOperatorBridge
import Lean

set_option stderrAsMessages false
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

/-- Append-only engine journal. The legacy whole-image `agreement.bin` is not
read by this fixture; `convert-journal` re-encodes it explicitly. -/
def journalPath (root : System.FilePath) (index : Nat) : System.FilePath :=
  replicaDirectory root index / "agreement.log"

/-- One replica's long-lived helper: its own signing key, the pairwise keys it
shares with each other member, and (when serving) its listener and peers. -/
def replicaSpec (root : System.FilePath) (helpers : Helpers) (index : Nat)
    (listen : Option String := none) (peers : List (Nat × String) := []) : HelperSpec :=
  { binary := helpers.agreement
    signingKey := some (replicaDirectory root index / "committee.sk")
    listen := listen
    peers := peers
    pairKeys := ((List.range 4).filter (· != index)).map fun peer => (peer,pairPath root index peer) }

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
    ⟨digestStream.encode ⟨8500⟩, 0, [], ⟨4,1,100000,8,3⟩, publicKeys⟩
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
    createJournal helpers.agreement (journalPath root index) ⟨bound,index,0,[],[]⟩
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

/-- Open one replica: verified source store, exact committee context bound to
this source genesis, and its engine journal (writer lock when `writable`). -/
def openReplica (root : System.FilePath) (helpers : Helpers) (index : Nat) (writable : Bool)
    (listen : Option String := none) (peers : List (Nat × String) := []) :
    IO GenericSimplexSourceHarness.Replica := do
  let encoded := (← IO.FS.readBinFile (root / "context.bin")).toList
  let some context := contextStream.toLawful.decode encoded
    | throw (IO.userError "invalid source fixture context: context.bin does not decode as a five-field Config context (a pre-timeout-backoff four-field context.bin refuses here; re-genesis with init)")
  require (contextStream.encode context == encoded && context.wellFormed)
    "noncanonical source fixture context"
  let alice := (← IO.FS.readBinFile (root / "subject-7.pub")).toList
  let bob := (← IO.FS.readBinFile (root / "subject-8.pub")).toList
  let built ← derive root helpers context alice bob
  require (context.instanceBytes == GenericSimplexSourceAnchor.anchorBytes 10 built.image.seed)
    "source fixture context does not bind this exact source genesis"
  let config := {baseConfig root helpers context index with
    expectedSeed := NativeHost.seedIdentity built.image.seed}
  let loaded ← IO.ofExcept (← DurableReceiverIO.load config.physicalTransport ResourceBirthCodec.rootBytes)
  let verified ← IO.ofExcept ((← NativeHostReplay.verifyLoaded config loaded).mapError
    (fun failure => s!"source fixture replay refused: {failure.detail}"))
  let runtime ← openRuntime (replicaSpec root helpers index listen peers)
    (journalPath root index) context writable
  let participant ← IO.ofExcept (← openParticipant config runtime ⟨loaded,verified⟩)
  return ⟨config,participant⟩

def openReplicas (root : System.FilePath) (helpers : Helpers) (writable : Bool) :
    IO (Array GenericSimplexSourceHarness.Replica) := do
  let mut replicas := #[]
  for index in List.range 4 do
    replicas := replicas.push (← openReplica root helpers index writable)
  return replicas

/-- `run`: one call through in-process agreement among the four actual
replicas (the same per-replica `iteration` the standing service runs, packets
handed over directly), then the lost-response/restart test: every helper
session is stopped, every journal reopened from disk, every source store
reloaded, and the exact original receipt must be there with exactly one
append. Test fixture only: it holds all four writer locks. -/
def runCall (root : System.FilePath) (helpers : Helpers) (callFile : System.FilePath)
    (fuel : Nat) : IO Unit := do
  let replicas ← openReplicas root helpers true
  let _ ← GenericSimplexSourceHarness.runCallChecked fuel replicas (← IO.FS.readBinFile callFile).toList

/-- Independent process readback: no drive, proposal, or admission is called. -/
def lookupAllCall (root : System.FilePath) (helpers : Helpers)
    (callFile outputFile : System.FilePath) : IO Unit := do
  let replicas ← openReplicas root helpers false
  require (replicas.size == 4) "lookup requires four actual participants"
  let call := (← IO.FS.readBinFile callFile).toList
  let some first := replicas[0]? | throw (IO.userError "missing first source participant")
  let ingress ← IO.ofExcept (sourceIngressOfCall first.config call)
  match completedCall first.participant call with
  | none =>
    for replica in replicas do
      require (completedCall replica.participant call).isNone "partial completion retained; use exact recovery"
    IO.println "LOOKUP-ALL absent on four; pending voting liabilities may remain; no drive or resubmit"
  | some receipt =>
    let some acceptedPrefix := GenericSimplexOperatorBridge.receiptPrefix first ingress
      | throw (IO.userError "source receipt lacks retained prefix")
    for replica in replicas do
      let some actual := completedCall replica.participant call
        | throw (IO.userError "partial source completion")
      require (NativeHostCodec.receiptStream.encode actual == NativeHostCodec.receiptStream.encode receipt) "source receipts differ"
      require (GenericSimplexOperatorBridge.receiptPrefix replica ingress == some acceptedPrefix)
        "source prefixes through original call differ"
    writePrivate outputFile (NativeHostCodec.outcomeCodec.encode (.confirmed .replayed receipt)).toByteArray
    let counts := replicas.toList.map fun r => r.participant.source.verified.opened.durable.image.accepted.length
    IO.println s!"LOOKUP-ALL exact original receipt and complete prefix on four reopened stores; accepted records per store {counts}; call at height {acceptedPrefix.length}"

/-- `serve-replica`: one standing replica process. The replica index is the
`replica-N` directory name; PEERS lists all four `host:port` addresses in index
order, this replica's own entry being its listener. Never returns. -/
def serveReplica (replica : System.FilePath) (peers : String) (helpers : Helpers)
    (tickMs : Nat) : IO Unit := do
  let some root := replica.parent | throw (IO.userError "replica directory has no parent")
  let some name := replica.fileName | throw (IO.userError "replica directory name")
  let some index := (name.toList.drop 8).asString.toNat?
    | throw (IO.userError "replica directory must be named replica-N")
  require (name.startsWith "replica-" && index < 4) "replica directory must be named replica-N"
  let addresses := peers.splitOn ","
  require (addresses.length == 4 && addresses.all (· != "")) "PEERS must list four host:port addresses"
  let peerList := ((List.range 4).filter (· != index)).map fun peer => (peer,addresses[peer]!)
  let replicaState ← openReplica root helpers index true (some addresses[index]!) peerList
  IO.eprintln s!"SERVE replica {index} listening on {addresses[index]!}"
  GenericSimplexServe.serveLoop replicaState.participant
    (GenericSimplexServe.requestDirectory replica) {} tickMs 30000 []

/-- `await-call`: place the exact original call at the proposer and watches at
the others, then wait for four identical receipts and prefixes. On the deadline
the outcome is `uncertain`; requests remain and the engines keep serving them.
Never opens a journal, never signals an engine. -/
def awaitCall (root : System.FilePath) (callFile outputFile : System.FilePath)
    (seconds : Nat) (id : String) (proposer : Nat) : IO Unit := do
  require (proposer < 4 && !id.isEmpty && id.all (fun c => c.isAlphanum || c == '-'))
    "await-call requires a proposer index and an alphanumeric request id"
  let call := (← IO.FS.readBinFile callFile).toList
  let replicas := (List.range 4).map (replicaDirectory root)
  let outcome : NativeHostCodec.Outcome ←
    match ← GenericSimplexServe.awaitCall replicas proposer id call (seconds * 1000) with
    | .confirmed kind receipt => pure (.confirmed kind receipt)
    | .uncertain => pure (.uncertain "agreement completion unavailable; use exact original-call lookup".toUTF8.toList)
  writePrivate outputFile (NativeHostCodec.outcomeCodec.encode outcome).toByteArray

/-- `convert-journal`: explicit one-time re-encoding of a legacy whole-image
`agreement.bin` into the append-only log. The new log is created exclusively and
must replay to the identical engine state; the legacy file is left untouched. -/
def convertJournal (root : System.FilePath) (helpers : Helpers) (index : Nat) : IO Unit := do
  let encoded := (← IO.FS.readBinFile (root / "context.bin")).toList
  let some context := contextStream.toLawful.decode encoded
    | throw (IO.userError "invalid source fixture context: context.bin does not decode as a five-field Config context (a pre-timeout-backoff four-field context.bin refuses here; re-genesis with init)")
  let legacy := (← IO.FS.readBinFile (replicaDirectory root index / "agreement.bin")).toList
  let some (journal,state) := restore context legacy
    | throw (IO.userError "legacy journal does not replay under this exact context")
  require (journal.self == index) "legacy journal belongs to another replica"
  createJournal helpers.agreement (journalPath root index) journal
  let converted := (← IO.FS.readBinFile (journalPath root index)).toList
  let some reopened := openRestored context converted
    | throw (IO.userError "converted log does not replay")
  require (reopened.state == state && reopened.log.merged == journal)
    "converted log replays to a different engine state"
  IO.println s!"CONVERTED replica {index}: {journal.events.length} events, {journal.commitWitnesses.length} witnesses, view {state.current}, identical replayed state"

end Minidregg.Verify.NativeJointSourceFixture

open Minidregg.Verify.NativeJointSourceFixture

def main (args : List String) : IO Unit := do
  match args with
  | ["init", root, store, signature, agreement, alice, bob] =>
      initializeStores root ⟨store,signature,agreement⟩ alice bob
  | ["serve-replica", replica, peers, store, signature, agreement, tick] =>
      let some tick := tick.toNat? | throw (IO.userError "invalid tick milliseconds")
      serveReplica replica peers ⟨store,signature,agreement⟩ tick
  | ["await-call", root, callFile, outputFile, seconds, id, proposer] =>
      let some seconds := seconds.toNat? | throw (IO.userError "invalid deadline seconds")
      let some proposer := proposer.toNat? | throw (IO.userError "invalid proposer index")
      awaitCall root callFile outputFile seconds id proposer
  | ["run", root, store, signature, agreement, callFile, fuel] =>
      let some fuel := fuel.toNat? | throw (IO.userError "invalid fuel")
      runCall root ⟨store,signature,agreement⟩ callFile fuel
  | ["lookup-all-call", root, store, signature, agreement, callFile, outputFile] =>
      lookupAllCall root ⟨store,signature,agreement⟩ callFile outputFile
  | ["convert-journal", root, store, signature, agreement, index] =>
      let some index := index.toNat? | throw (IO.userError "invalid replica index")
      convertJournal root ⟨store,signature,agreement⟩ index
  | _ => throw (IO.userError "usage: NativeJointSourceFixture init ROOT STORE SIGNATURE AGREEMENT ALICE_PUB BOB_PUB | serve-replica REPLICA_DIR PEERS STORE SIGNATURE AGREEMENT TICK_MS | await-call ROOT CALL OUTCOME SECONDS ID PROPOSER | run ROOT STORE SIGNATURE AGREEMENT CALL FUEL | lookup-all-call ROOT STORE SIGNATURE AGREEMENT CALL OUTCOME | convert-journal ROOT STORE SIGNATURE AGREEMENT INDEX")
