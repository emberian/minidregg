/-
Real source fixture for four independently stored Mini agreement participants.
The initializer derives a fresh source genesis under the actual agreed runtime
profile, then binds its exact seed to the committee context. Each replica then
runs as its own standing `serve-replica` process; a client only places the exact
original call with `await-call` and waits for a quorum of identical receipts. No supplied
record, validation callback, checked engine input, or accepted history is seeded.
This source is WIP until checked with the common receiver's qualified outputs.
-/
module

public import Kernel.NativeHostGenesis
public import Kernel.NativeHostContext
public import Compiler.GenericSimplexSourceAnchor
public import Verify.GenericSimplexOperatorBridge
public import Verify.ResourceReserveBirthFixture
public import Lean.Data.Json

@[expose] public section

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

/-- Append-only engine journal. A legacy whole-image `agreement.bin` is not read
by this fixture: older meshes are re-genesised, never converted. -/
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
    (context : Context) (index : Nat) (expectedSeed : Digest := ⟨0⟩) : NativeHost.Config :=
  NativeHost.Config.ofInputs
    { deployment := ⟨⟨8500⟩, 10, 11, 12⟩
      federation := ⟨9⟩
      template := {issuer := ⟨5⟩, ownerBudget := 100000, lifetime := 10000}
      tariff := ⟨3, 2, 1, 0, 99, 0⟩
      genesisHeight := 10
      expectedSeed := expectedSeed
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
    payControlCapabilityId := ⟨48⟩
    clockControlCapabilityId := ⟨49⟩
    clockTickers := []
    tailBound := 10000
    clockGenesisNow := 0
    clockMaxStepSeconds := 300
    issuanceCap := 1000000000000000
    platformGrainBirth := none
    platformCustodianKey := none
    platformOwnerBudget := config.template.ownerBudget
    platformLifetime := config.template.lifetime }

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
      if durable.height != 0 then return .error "bootstrap image contains accepted history"
      match NativeHost.validateLoaded config durable with
      | .error detail => return .error detail
      | .ok _ =>
          return ← DurableReceiverIO.bootstrap config.transport ResourceBirthCodec.rootBytes durable.image.seed

def initializeStores (root : System.FilePath) (helpers : Helpers)
    (alicePath bobPath : System.FilePath) (timeoutMs : Nat := 100000) : IO Unit := do
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
    ⟨digestStream.encode ⟨8500⟩, 0, [], ⟨4,1,timeoutMs,8,3⟩, publicKeys⟩
  require context.wellFormed "real committee context is malformed"
  let built ← derive root helpers context alice bob
  require built.image.accepted.isEmpty "genesis unexpectedly contains accepted history"
  let bound := GenericSimplexSourceAnchor.bind context 10 built.image.seed
  writePrivate (root / "context.bin") (contextStream.encode bound).toByteArray
  writePrivate (root / "genesis.bin") (DurableReceiverCodec.encode built.image).toByteArray
  for index in List.range 4 do
    let config := baseConfig root helpers bound index (NativeHost.seedIdentity built.image.seed)
    require (config.runtimeParameters == (baseConfig root helpers context 0).runtimeParameters)
      "binding exact source anchor changed the normalized runtime semantics"
    IO.ofExcept (← bootstrapFresh config (DurableReceiverCodec.encode built.image))
    createJournal helpers.agreement (journalPath root index) ⟨bound,index,0,[],[],none⟩
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
this source genesis, and its engine journal (writer lock when `writable`). With
`foreignHistory` (the `foreign-history` plant) the running digest of its source records is
that of another domain's history (the next epoch's): a certified record is then never
ordered, because the digest its certificate signs is not the one this source extends. -/
def openReplica (root : System.FilePath) (helpers : Helpers) (index : Nat) (writable : Bool)
    (listen : Option String := none) (peers : List (Nat × String) := [])
    (foreignHistory : Bool := false) :
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
  let config := baseConfig root helpers context index (NativeHost.seedIdentity built.image.seed)
  let loaded ← IO.ofExcept (← DurableReceiverIO.load config.physicalTransport ResourceBirthCodec.rootBytes)
  let ⟨_, reader⟩ ← IO.ofExcept ((← DurableHistoryStore.readerOf config.physicalTransport
    ResourceBirthCodec.rootBytes loaded).mapError (fun detail => s!"source fixture history reader: {detail}"))
  let verified ← IO.ofExcept ((← NativeHostReplay.verifyLoaded config reader loaded).mapError
    (fun failure => s!"source fixture replay refused: {failure.detail}"))
  let runtime ← openRuntime (replicaSpec root helpers index listen peers)
    (journalPath root index) context writable
  let participant ← IO.ofExcept (← openParticipant config runtime
    (Source.read (if foreignHistory then {context with epoch := context.epoch + 1} else context) verified))
  return ⟨config,participant⟩

def openReplicas (root : System.FilePath) (helpers : Helpers) (writable : Bool)
    (foreignHistory : Bool := false) : IO (Array GenericSimplexSourceHarness.Replica) := do
  let mut replicas := #[]
  for index in List.range 4 do
    replicas := replicas.push (← openReplica root helpers index writable none [] foreignHistory)
  return replicas

/-- The test signer (`credential-signature-verifier`'s `sign-probe` example): the Ed25519
key of a seed octet signs one frame. Test fixture only. -/
def probeSign (signer : System.FilePath) (seed : Nat) (frame : ByteArray) :
    IO (ByteArray × ByteArray) :=
  IO.FS.withTempDir fun directory => do
    IO.FS.writeBinFile (directory / "frame.bin") frame
    -- the signer announces on stderr that its key is public; only its exit code is read
    let result ← IO.Process.output {cmd := signer.toString, args := #[toString seed,
      (directory / "frame.bin").toString, (directory / "public.bin").toString,
      (directory / "signature.bin").toString]}
    require (result.exitCode == 0) s!"test signer refused: {result.stderr}"
    pure (← IO.FS.readBinFile (directory / "public.bin"),
      ← IO.FS.readBinFile (directory / "signature.bin"))

/-- `probe-key`: write the test signer's public key for a seed octet. -/
def probeKey (signer : System.FilePath) (seed : Nat) (output : System.FilePath) : IO Unit := do
  writePrivate output (← probeSign signer seed ByteArray.empty).1

/-- The canonical `SignedCall` of one ordinary content birth by subject 7 at cell TARGET,
planned by `NativeHost.prepareLoaded` on an opened source and signed slot by slot by the
test signer (seed 7 is subject 7's enrolled key when `init` was given `probe-key 7`). Reads
only; the call is what a client would hand to `run`, `await-call` or the operator bridge.
Returned with its number of signed slots. -/
def authorOn (config : NativeHost.Config) (source : NativeHostGenesis.Config)
    (opened : NativeHost.Opened config) (signer : System.FilePath) (target nonce : Nat) :
    IO (ByteArray × Nat) := do
  let born := ResourceReserveBirthFixture.content target ⟨7⟩ ⟨target + 1000⟩ ⟨target + 2000⟩
  let descriptor := ResourceReserveBirthFixture.ordinaryDescriptor config source opened ⟨7⟩ nonce 7 [born]
  let plan ← IO.ofExcept ((NativeHost.prepareLoaded config opened
    (.birth (CanonicalCellRegistry.sourceEncoding.codec.encode descriptor)
      (List.replicate descriptor.resourceBatch.operations.length ⟨41⟩))).mapError
        (fun detail => s!"birth plan refused: {detail}"))
  let mut signatures := []
  for slot in plan.slots do
    signatures := signatures ++ [(← probeSign signer 7 slot.header.toByteArray).2.toList]
  let call ← IO.ofExcept ((NativeHost.assemble plan signatures).mapError
    (fun detail => s!"birth assembly refused: {detail}"))
  return ((NativeHostCodec.callCodec.encode call).toByteArray,plan.slots.length)

/-- `author-birth`: `authorOn` replica 0's source store as a fresh process opens it. -/
def authorBirth (root : System.FilePath) (helpers : Helpers) (signer : System.FilePath)
    (target nonce : Nat) (output : System.FilePath) : IO Unit := do
  let encoded := (← IO.FS.readBinFile (root / "context.bin")).toList
  let some context := contextStream.toLawful.decode encoded
    | throw (IO.userError "invalid source fixture context")
  let alice := (← IO.FS.readBinFile (root / "subject-7.pub")).toList
  let bob := (← IO.FS.readBinFile (root / "subject-8.pub")).toList
  let built ← derive root helpers context alice bob
  let config := baseConfig root helpers context 0 (NativeHost.seedIdentity built.image.seed)
  let source := genesis (baseConfig root helpers context 0) alice bob
  let opened ← IO.ofExcept (← NativeHost.openExisting config)
  let (call,slots) ← authorOn config source opened signer target nonce
  writePrivate output call
  IO.println s!"AUTHORED ordinary birth of cell {target} by subject 7: {slots} signed slots"

def median (samples : Array Nat) : Nat :=
  (samples.qsort (· < ·))[samples.size / 2]?.getD 0

/-- One round of the in-process mesh: every live replica takes the packets addressed to it
and runs the per-replica `iteration` the standing service runs. A packet to a replica that
is not live is lost, as on a stopped process. Returned: the packets sent, and each live
replica's report. -/
def round (replicas : Array GenericSimplexSourceHarness.Replica) (live : Nat → Bool)
    (packets : List (Nat × ByteArray)) :
    IO (Array GenericSimplexSourceHarness.Replica × List (Nat × ByteArray) ×
      List (Nat × GenericSimplexServe.IterationReport)) := do
  let mut replicas := replicas
  let mut sent := []
  let mut reports := []
  for index in List.range replicas.size do
    if live index then
      let some replica := replicas[index]? | throw (IO.userError "replica index")
      let inbound := (packets.filter (·.1 == index)).map (·.2)
      let (participant,out,report) ← GenericSimplexServe.iteration replica.participant inbound {}
      if report.refused != 0 then
        throw (IO.userError "honest in-process packet failed authentication")
      replicas := replicas.set! index ⟨replica.config,participant⟩
      sent := sent ++ out
      reports := reports ++ [(index,report)]
  return (replicas,sent,reports)

def sourceHeight (replica : GenericSimplexSourceHarness.Replica) : Nat :=
  replica.participant.source.verified.opened.durable.height

/-- Drive the live replicas until each has `target` source records, with no real waiting:
after three rounds in a row that move no packet, the live replicas' logical clocks jump one
view timeout, so the next slice ticks a deadline that is then due (the view of a stopped
leader ends without anyone sleeping through it). -/
def settle (replicas : Array GenericSimplexSourceHarness.Replica) (live : Nat → Bool)
    (target fuel : Nat) : IO (Array GenericSimplexSourceHarness.Replica) := do
  let mut replicas := replicas
  let mut packets : List (Nat × ByteArray) := []
  let mut quiet := 0
  for _ in List.range fuel do
    if replicas.zipIdx.all (fun (replica,index) => !live index || target ≤ sourceHeight replica) then
      return replicas
    let (next,sent,_) ← round replicas live packets
    replicas := next
    packets := sent
    quiet := if sent.isEmpty then quiet + 1 else 0
    if quiet ≥ 3 then
      quiet := 0
      replicas := replicas.mapIdx fun index (replica : GenericSimplexSourceHarness.Replica) =>
        if live index then
          let runtime := replica.participant.runtime
          let jumped := {runtime with logicalBase := runtime.logicalBase + runtime.context.config.timeout}
          (⟨replica.config,{replica.participant with runtime := jumped}⟩ :
            GenericSimplexSourceHarness.Replica)
        else replica
  throw (IO.userError s!"in-process agreement did not reach source height {target} on the live replicas")

/-- One birth authored on replica 0's verified tip and offered there. -/
def offerBirth (replicas : Array GenericSimplexSourceHarness.Replica) (source : NativeHostGenesis.Config)
    (signer : System.FilePath) (serial : Nat) : IO (Array GenericSimplexSourceHarness.Replica) := do
  let some proposer := replicas[0]? | throw (IO.userError "missing first source participant")
  let (call,_) ← authorOn proposer.config source proposer.participant.source.verified.opened
    signer (7001 + serial) (71 + serial)
  let ingress ← IO.ofExcept (sourceIngressOfCall proposer.config call.toList)
  let (proposed,proposal) ← propose proposer.participant ingress
  if let .error detail := proposal then
    throw (IO.userError s!"admission of birth {serial} refused: {detail}")
  return replicas.set! 0 ⟨proposer.config,proposed⟩

def fixtureGenesis (root : System.FilePath) (helpers : Helpers) : IO NativeHostGenesis.Config := do
  let encoded := (← IO.FS.readBinFile (root / "context.bin")).toList
  let some context := contextStream.toLawful.decode encoded
    | throw (IO.userError "invalid source fixture context")
  let alice := (← IO.FS.readBinFile (root / "subject-7.pub")).toList
  let bob := (← IO.FS.readBinFile (root / "subject-8.pub")).toList
  return genesis (baseConfig root helpers context 0) alice bob

/-- `append-flatness`: COUNT births, one after another, through in-process agreement among
the world's four participants (the per-replica `iteration` the standing service runs), each
authored on the proposer's own verified tip. Printed per height: the wall time of the call,
the size of the appended record (and of its original ingress and its largest write), and the
time each replica's application hand-off took when it applied the record (`applyNext`: the certificate, the ordered append with its readback,
the acknowledgement).

A birth's record is not of constant size: it rewrites a cell that accumulates with every
birth, so the record grows with the height (about 160 bytes per birth in this world) and
every cost proportional to the record's bytes grows with it. The row therefore judges the
hand-off per KB of appended record: it fails when that median over the last WINDOW heights
exceeds FACTOR times the median over the first WINDOW. What it bounds is the growth of the
append beyond the growth of the record it appends.

With `revalidate` (the `revalidate-prefix` plant) every replica also replays its whole source
prefix from the genesis after each append (`JointSourcePrefixValidation.validate`), which is
what a participant without a retained verified tip would do; that time is counted. -/
def appendFlatness (root : System.FilePath) (helpers : Helpers) (signer : System.FilePath)
    (count window factor : Nat) (revalidate : Bool := false) : IO Unit := do
  require (0 < window && 2 * window ≤ count) "append-flatness needs COUNT of at least two windows"
  let source ← fixtureGenesis root helpers
  let mut replicas ← openReplicas root helpers true
  let some opening := replicas[0]? | throw (IO.userError "missing first source participant")
  let base := sourceHeight opening
  let mut series : Array (Array Nat) := #[]
  let mut sizes : Array Nat := #[]
  let mut times : Array Nat := #[]
  for k in List.range count do
    let started ← IO.monoNanosNow
    replicas ← offerBirth replicas source signer (base + k)
    let target := base + k + 1
    let mut packets : List (Nat × ByteArray) := []
    let mut samples : Array Nat := #[]
    let mut recordBytes := 0
    let mut largest : Nat × Nat := (0,0)
    let mut eventBytes := 0
    let mut writeCount := 0
    let mut fuel := 400
    while replicas.any (fun replica => sourceHeight replica < target) do
      if fuel == 0 then
        throw (IO.userError s!"append-flatness: height {target} not reached by all four")
      fuel := fuel - 1
      let (next,sent,reports) ← round replicas (fun _ => true) packets
      replicas := next
      packets := sent
      for (index,report) in reports do
        if report.status == "applied" then
          let mut spent := report.applyNanos
          let some replica := replicas[index]? | throw (IO.userError "replica index")
          if let some record := replica.participant.source.verified.opened.durable.image.acceptedRev.head? then
            recordBytes := (DurableCheckpointCodec.recordFrame.encode record).length
            largest := record.writes.foldl (fun best write =>
              if best.2 < write.canonicalPostBytes.length then
                (write.cellId.value,write.canonicalPostBytes.length) else best) (0,0)
            eventBytes := record.event.canonicalBytes.length
            writeCount := record.writes.length
          if revalidate then
            let before ← IO.monoNanosNow
            match ← JointSourcePrefixValidation.validate replica.config
                replica.participant.source.verified.origin replica.participant.runtime.context
                (JointReceiver.sourcePrefix replica.participant.source.verified.opened.durable) with
            | .accepted _ => pure ()
            | _ => throw (IO.userError "revalidate-prefix: the applied source prefix did not replay")
            spent := spent + ((← IO.monoNanosNow) - before)
          samples := samples.push (spent / 1000)
    series := series.push (samples.map fun spent => spent * 1024 / (max 1 recordBytes))
    sizes := sizes.push recordBytes
    times := times.push (median samples)
    IO.println s!"{target}\t{((← IO.monoNanosNow) - started) / 1000000}\t{recordBytes}\t{median samples}\t{samples.toList}\tevent {eventBytes} B, {writeCount} writes, largest {largest.2} B to cell {largest.1}"
  let pool := fun (part : Array (Array Nat)) => part.foldl (· ++ ·) #[]
  let head := median (pool (series.extract 0 window))
  let tail := median (pool (series.extract (count - window) count))
  let shape := fun (first last : Nat) =>
    s!"{median (times.extract first last)} us for a {median (sizes.extract first last)}-byte record"
  require (tail ≤ factor * head)
    s!"append flatness: the median application hand-off per KB of appended record over the last {window} heights took {tail} us ({shape (count - window) count}), more than {factor} times the {head} us of the first {window} ({shape 0 window})"
  IO.println s!"FLAT ordered append over heights {base + 1}..{base + count}: median hand-off per KB of appended record {head} us over the first {window} ({shape 0 window}), {tail} us over the last {window} ({shape (count - window) count}); bound: {factor} times the first"

/-- `rejoin`: one replica stopped for two calls and restarted catches up, in process and
with no timer. Call 1 is agreed by all four. Replica 3 then takes no input: calls 2 and 3
are agreed by the other three (the views it leads end by logical clock jumps, `settle`).
It is restarted from its journal and its source store alone, into a domain with no further
operation and no clock jump: it tells its peers its height, they send the COMMITs it is
behind by (`GenericSimplexNative.answerHeight`), and it validates, commits and appends both
records. With `silent` (the `silent-rejoin` plant) the restarted replica never announces its
height, as before this row existed, and stays behind. -/
def rejoin (root : System.FilePath) (helpers : Helpers) (signer : System.FilePath)
    (silent : Bool := false) : IO Unit := do
  let source ← fixtureGenesis root helpers
  let mut replicas ← openReplicas root helpers true
  let some opening := replicas[0]? | throw (IO.userError "missing first source participant")
  let base := sourceHeight opening
  let everyone := fun (_ : Nat) => true
  let others := fun (index : Nat) => index != 3
  replicas ← offerBirth replicas source signer base
  replicas ← settle replicas everyone (base + 1) 400
  for k in [1,2] do
    replicas ← offerBirth replicas source signer (base + k)
    replicas ← settle replicas others (base + k + 1) 400
  let some stopped := replicas[3]? | throw (IO.userError "missing stopped replica")
  require (sourceHeight stopped == base + 1) "rejoin: the stopped replica took input"
  let runtime ← stopped.participant.runtime.reopen
  let reopened ← IO.ofExcept (← openParticipant stopped.config runtime stopped.participant.source)
  let (reloaded,_) ← reloadSource reopened
  let silenced := {reloaded.schedule with announced := true}
  let restarted := if silent then {reloaded with schedule := silenced} else reloaded
  require (restarted.source.verified.opened.durable.height == base + 1)
    "rejoin: the restarted replica's source is not where it stopped"
  replicas := replicas.set! 3 ⟨stopped.config,restarted⟩
  let mut packets : List (Nat × ByteArray) := []
  let mut quiet := 0
  for _ in List.range 400 do
    let (next,sent,_) ← round replicas everyone packets
    replicas := next
    packets := sent
    quiet := if sent.isEmpty then quiet + 1 else 0
    if quiet ≥ 8 then break
  let some rejoined := replicas[3]? | throw (IO.userError "missing restarted replica")
  let some first := replicas[0]? | throw (IO.userError "missing first source participant")
  require (sourceHeight rejoined == base + 3)
    s!"rejoin: the restarted replica stayed behind (source height {sourceHeight rejoined} of {base + 3}) in an idle domain"
  require (GenericSimplexSourceHarness.tipKey rejoined.participant ==
      GenericSimplexSourceHarness.tipKey first.participant)
    "rejoin: the restarted replica's source differs from its peers'"
  IO.println s!"PASS rejoin: replica 3 stopped at source height {base + 1}, restarted into an idle domain at {base + 3}, caught up from its peers' kept COMMITs with no further operation and no timer"

/-- `run`: one call through in-process agreement among the four actual
replicas (the same per-replica `iteration` the standing service runs, packets
handed over directly), then the lost-response/restart test: every helper
session is stopped, every journal reopened from disk, every source store
reloaded, and the exact original receipt must be there with exactly one
append. Test fixture only: it holds all four writer locks. -/
def runCall (root : System.FilePath) (helpers : Helpers) (callFile : System.FilePath)
    (fuel : Nat) (foreignHistory : Bool := false) : IO Unit := do
  let replicas ← openReplicas root helpers true foreignHistory
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
    let counts := replicas.toList.map fun r => r.participant.source.verified.opened.durable.height
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
  GenericSimplexServe.serveLoop replicaState.participant replica {} tickMs 30000 []

/-- `await-call`: place the exact original call at the proposer and watches at
the others, then wait for a quorum of identical receipts (three of the four; every receipt
present must be the same one). On the deadline the outcome is `uncertain`; requests remain
and the engines keep serving them, and the command fails after writing that outcome. Never
opens a journal, never signals an engine. With `quorum := false` (`--all`) it waits for all
four: the question "has every replica caught up", which a stopped replica leaves open. -/
def awaitCall (root : System.FilePath) (callFile outputFile : System.FilePath)
    (seconds : Nat) (id : String) (proposer : Nat) (quorum : Bool := true) : IO Unit := do
  require (proposer < 4 && !id.isEmpty && id.all (fun c => c.isAlphanum || c == '-'))
    "await-call requires a proposer index and an alphanumeric request id"
  let call := (← IO.FS.readBinFile callFile).toList
  let replicas := (List.range 4).map (replicaDirectory root)
  match ← GenericSimplexServe.awaitCall replicas proposer id call (seconds * 1000) quorum with
  | .confirmed kind receipt receipts =>
    writePrivate outputFile (NativeHostCodec.outcomeCodec.encode (.confirmed kind receipt)).toByteArray
    IO.println s!"AWAIT {id} confirmed by {receipts} of 4 identical receipts"
  | .uncertain =>
    writePrivate outputFile (NativeHostCodec.outcomeCodec.encode
      (.uncertain "agreement completion unavailable; use exact original-call lookup".toUTF8.toList)).toByteArray
    throw (IO.userError s!"AWAIT {id} uncertain after {seconds} s: fewer than {if quorum then 3 else 4} receipts")

/-- `audit-journal`: replay one replica's whole retained input history, every
checkpoint segment `agreement.log.upto-N` in increasing N and then the live
journal, through `auditSegments`. Read-only; safe beside a running replica. -/
def auditJournal (root : System.FilePath) (index : Nat) : IO Unit := do
  let encoded := (← IO.FS.readBinFile (root / "context.bin")).toList
  let some context := contextStream.toLawful.decode encoded
    | throw (IO.userError "invalid source fixture context: context.bin does not decode as a five-field Config context (a pre-timeout-backoff four-field context.bin refuses here; re-genesis with init)")
  let directory := replicaDirectory root index
  let segmentPrefix := "agreement.log.upto-"
  let mut segments : List (Nat × System.FilePath) := []
  for entry in ← directory.readDir do
    if entry.fileName.startsWith segmentPrefix then
      let some n := (entry.fileName.drop segmentPrefix.length).toNat?
        | throw (IO.userError s!"unexpected segment name {entry.fileName}")
      segments := segments ++ [(n,entry.path)]
  let ordered := (segments.mergeSort (fun a b => a.1 ≤ b.1)).map Prod.snd ++ [journalPath root index]
  let mut images := []
  for path in ordered do images := images ++ [(← IO.FS.readBinFile path).toList]
  match auditSegments context images with
  | .ok s => IO.println s!"AUDITED replica {index}: {ordered.length} segments from genesis, view {s.core.current}, committed height {s.height}"
  | .error detail => throw (IO.userError s!"audit of replica {index} failed: {detail}")

/-- `write-audit-fixture`: build a deterministic 2-segment replica-0 journal
fixture in `ROOT` (an archived genesis segment `agreement.log.upto-1` and a live
checkpointed `agreement.log` continuing from its replayed state) so
`audit-journal ROOT 0` is exercised in-process by `scripts/gates/check-generic-simplex`.
With `--plant corrupt-segment`, the live segment's snapshot disagrees with the
previous segment's replayed state. -/
def writeAuditFixture (root : System.FilePath) (corrupt : Bool) : IO Unit := do
  privateDirectory root
  let dir := replicaDirectory root 0
  privateDirectory dir
  let context : Context :=
    ⟨[1,2,3], 0, [4,5,6], ⟨4,1,100000,8,3⟩,
      (List.range 4).map fun i => List.replicate 1952 (UInt8.ofNat (i + 1))⟩
  writePrivate (root / "context.bin") (contextStream.encode context).toByteArray
  let empty : Journal := ⟨context,0,0,[],[],none⟩
  let some r0 := openRestored context (Log.encode ⟨empty,[]⟩)
    | throw (IO.userError "audit fixture base journal refused")
  let some (r1,frame1) := appendRestored r0 [encodeEntry (.input (.offer [1,2,3])), encodeEntry (.input (.tick 1))] []
    | throw (IO.userError "audit fixture segment 0 append refused")
  writePrivate (dir / "agreement.log.upto-1") (Log.encode ⟨empty,[]⟩ ++ frame1).toByteArray
  let (cp,cpBytes) := checkpointRestored r1
  let liveBytes ← if corrupt then
      let (_,badBytes) := checkpointRestored r0
      pure badBytes
    else
      let some (_,frame2) := appendRestored cp [encodeEntry (.input (.tick 2))] []
        | throw (IO.userError "audit fixture segment 1 append refused")
      pure (cpBytes ++ frame2)
  writePrivate (journalPath root 0) liveBytes.toByteArray

end Minidregg.Verify.NativeJointSourceFixture

open Minidregg.Verify.NativeJointSourceFixture

def main (args : List String) : IO Unit := do
  match args with
  | ["init", root, store, signature, agreement, alice, bob] =>
      initializeStores root ⟨store,signature,agreement⟩ alice bob
  | ["init", root, store, signature, agreement, alice, bob, timeout] =>
      let some timeout := timeout.toNat? | throw (IO.userError "invalid view timeout milliseconds")
      initializeStores root ⟨store,signature,agreement⟩ alice bob timeout
  | ["serve-replica", replica, peers, store, signature, agreement, tick] =>
      let some tick := tick.toNat? | throw (IO.userError "invalid tick milliseconds")
      serveReplica replica peers ⟨store,signature,agreement⟩ tick
  | ["await-call", root, callFile, outputFile, seconds, id, proposer] =>
      let some seconds := seconds.toNat? | throw (IO.userError "invalid deadline seconds")
      let some proposer := proposer.toNat? | throw (IO.userError "invalid proposer index")
      awaitCall root callFile outputFile seconds id proposer
  | ["await-call", root, callFile, outputFile, seconds, id, proposer, "--all"] =>
      let some seconds := seconds.toNat? | throw (IO.userError "invalid deadline seconds")
      let some proposer := proposer.toNat? | throw (IO.userError "invalid proposer index")
      awaitCall root callFile outputFile seconds id proposer false
  | ["probe-key", signer, seed, output] =>
      let some seed := seed.toNat? | throw (IO.userError "invalid seed octet")
      probeKey signer seed output
  | ["author-birth", root, store, signature, agreement, signer, target, nonce, output] =>
      let some target := target.toNat? | throw (IO.userError "invalid target cell")
      let some nonce := nonce.toNat? | throw (IO.userError "invalid nonce")
      authorBirth root ⟨store,signature,agreement⟩ signer target nonce output
  | ["run", root, store, signature, agreement, callFile, fuel] =>
      let some fuel := fuel.toNat? | throw (IO.userError "invalid fuel")
      runCall root ⟨store,signature,agreement⟩ callFile fuel
  | ["run", root, store, signature, agreement, callFile, fuel, "--plant", "foreign-history"] =>
      let some fuel := fuel.toNat? | throw (IO.userError "invalid fuel")
      runCall root ⟨store,signature,agreement⟩ callFile fuel true
  | ["append-flatness", root, store, signature, agreement, signer, count, window, factor] =>
      let some count := count.toNat? | throw (IO.userError "invalid count")
      let some window := window.toNat? | throw (IO.userError "invalid window")
      let some factor := factor.toNat? | throw (IO.userError "invalid factor")
      appendFlatness root ⟨store,signature,agreement⟩ signer count window factor
  | ["append-flatness", root, store, signature, agreement, signer, count, window, factor, "--plant", "revalidate-prefix"] =>
      let some count := count.toNat? | throw (IO.userError "invalid count")
      let some window := window.toNat? | throw (IO.userError "invalid window")
      let some factor := factor.toNat? | throw (IO.userError "invalid factor")
      appendFlatness root ⟨store,signature,agreement⟩ signer count window factor true
  | ["rejoin", root, store, signature, agreement, signer] =>
      rejoin root ⟨store,signature,agreement⟩ signer
  | ["rejoin", root, store, signature, agreement, signer, "--plant", "silent-rejoin"] =>
      rejoin root ⟨store,signature,agreement⟩ signer true
  | ["lookup-all-call", root, store, signature, agreement, callFile, outputFile] =>
      lookupAllCall root ⟨store,signature,agreement⟩ callFile outputFile
  | ["audit-journal", root, index] =>
      let some index := index.toNat? | throw (IO.userError "invalid replica index")
      auditJournal root index
  | ["write-audit-fixture", root] =>
      writeAuditFixture root false
  | ["write-audit-fixture", root, "--plant", "corrupt-segment"] =>
      writeAuditFixture root true
  | _ => throw (IO.userError "usage: NativeJointSourceFixture audit-journal ROOT INDEX | write-audit-fixture ROOT [--plant corrupt-segment] | init ROOT STORE SIGNATURE AGREEMENT ALICE_PUB BOB_PUB [VIEW_TIMEOUT_MS] | serve-replica REPLICA_DIR PEERS STORE SIGNATURE AGREEMENT TICK_MS | await-call ROOT CALL OUTCOME SECONDS ID PROPOSER [--all] | probe-key SIGN_PROBE SEED PUBLIC_OUT | author-birth ROOT STORE SIGNATURE AGREEMENT SIGN_PROBE TARGET NONCE CALL_OUT | run ROOT STORE SIGNATURE AGREEMENT CALL FUEL [--plant foreign-history] | append-flatness ROOT STORE SIGNATURE AGREEMENT SIGN_PROBE COUNT WINDOW FACTOR [--plant revalidate-prefix] | rejoin ROOT STORE SIGNATURE AGREEMENT SIGN_PROBE [--plant silent-rejoin] | lookup-all-call ROOT STORE SIGNATURE AGREEMENT CALL OUTCOME")
