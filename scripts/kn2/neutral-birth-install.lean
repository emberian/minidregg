/- KN2-NEUTRAL-BIRTHS executed probe, cluster (4): a policy installation births its
successor policy-source cell, and commits only when the install step the OLD source's law
admitted names it (`birth/<id>` ↦ the successor's exact post root).

A source-built genesis (subject 7 holds the factory's control capability 43, with a real
Ed25519 key from the fixture signer) is booted into a native Store.  Subject 7 installs a
successor of the factory's policy: the declaration is authored from the current head
(version+1, previous = the head's address), planned by `NativeHost.prepareLoaded`, signed,
assembled, and submitted through the real Host path `NativeHost.submitLoaded` on the light
opening (`submitInstallLight`: basis, admission on `Ground.ofBasis`, the served commit).

 control  the installation commits (`confirmed`), and the installed head is the successor;
 refusal  printed by name when a plant (plant-neutral-birth-install.sh) drops the newborn
          slot from the install step: `neutralBirthUnjudged <successor cell>`.

frontier-reads checks the migrated admission cut against full replay at physical checkpoint
heights 4 and 40, with two later admitted calls and a cold SQLite prefix-read trap.

Native frontier probe: scripts/kn2/run-frontier-reads.sh HOST-BUILD-OUTPUT VERIFIER SIGN-PROBE STORE-BINARY -/
module

public import Kernel.NativeHostGenesis
public import Kernel.NativeHost
public import Kernel.NativeHostSession
public import Kernel.FnFrontierCheckpoint
public import Kernel.FnConsumerNamespaceReceiver
public import Kernel.FnSelectedPollReceiver
public import Kernel.FnEmptyPollReceiverV2
public import Host.FnConsumerFrontierPlan
public import Verify.ResourceReserveBirthFixture

meta import Kernel.NativeHostGenesis
meta import Kernel.NativeHost
meta import Kernel.NativeHostSession
meta import Kernel.FnFrontierCheckpoint
meta import Kernel.FnConsumerNamespaceReceiver
meta import Kernel.FnSelectedPollReceiver
meta import Kernel.FnEmptyPollReceiverV2
meta import Host.FnConsumerFrontierPlan
meta import Verify.ResourceReserveBirthFixture

public section

open Minidregg.Theory
open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.ResourceBirth
open Minidregg.Compiler
open Minidregg.Kernel

namespace NeutralBirthInstallProbe

def require (label : String) (yes : Bool) : IO Unit :=
  unless yes do throw (IO.userError s!"FAIL neutral birth install: {label}")

def sign (binary : System.FilePath) (seed : Nat) (frame : List UInt8) :
    IO (List UInt8 × List UInt8) :=
  IO.FS.withTempDir fun directory => do
    let framePath := directory / "frame.bin"
    let keyPath := directory / "public.bin"
    let sigPath := directory / "signature.bin"
    IO.FS.writeBinFile framePath frame.toByteArray
    let output ← IO.Process.output
      { cmd := binary.toString
        args := #[toString seed, framePath.toString, keyPath.toString, sigPath.toString] }
    require s!"fixture signer: {output.stderr}" (output.exitCode == 0)
    pure ((← IO.FS.readBinFile keyPath).toList, (← IO.FS.readBinFile sigPath).toList)

def tariff : CreationTariff := ⟨0, 0, 0, 0, 99, 0⟩

def hostTemplate : NativeHost.Config := NativeHost.Config.ofInputs {
  deployment := ⟨⟨8500⟩, 10, 11, 12⟩
  federation := ⟨9⟩
  template := ⟨⟨5⟩, 100000, 10000, 64⟩
  tariff := tariff
  genesisHeight := 10
  expectedSeed := ⟨0⟩
  storage := { binary := "unused", root := "unused", key := "unused", checkpointEvery := 16 }
  signature := ⟨"unused"⟩ }

def profile := hostTemplate.profile

def genesis (creatorKey : List UInt8) : NativeHostGenesis.Config where
  deployment := hostTemplate.deployment
  federation := hostTemplate.federation
  tariff := tariff
  expectedSemantics := profile.semantics
  issuerEpoch := 2
  genesisHeight := 10
  factoryPredicate := .all []
  enrollments :=
    [⟨⟨7007, 2, 1, 7, creatorKey, 0, 100, none⟩, 7,
      ⟨41⟩, ⟨44⟩, ⟨46⟩, 100, .all []⟩]
  factoryController := ⟨⟨7⟩, ⟨43⟩⟩
  meterAllowance := fun _ => 10000000
  clockTickers := []
  tailBound := 1000
  clockGenesisNow := 0
  clockMaxStepSeconds := 300
  issuanceCap := 1000000000000000
  payControlCapabilityId := ⟨47⟩
  clockControlCapabilityId := ⟨48⟩
  platformGrainBirth := none
  platformCustodianKey := none
  platformOwnerBudget := 100000
  platformLifetime := 10000

def describe : NativeHostCodec.Outcome → String
  | .confirmed _ _ => "committed"
  | .charged _ receipt causeBytes =>
      let cause := match ObjectiveActivityReceiver.rejectCodec.decode causeBytes with
        | some typed => reprStr typed
        | none => s!"invalid canonical cause {repr causeBytes}"
      s!"charged failure at height {receipt.acceptedCount}: {cause}"
  | .refused _ phase detail _ =>
      s!"refused {String.fromUTF8! ⟨phase.toArray⟩}: {String.fromUTF8! ⟨detail.toArray⟩}"
  | .contention => "contention"
  | .unavailable detail => s!"unavailable {String.fromUTF8! ⟨detail.toArray⟩}"
  | .uncertain detail => s!"uncertain {String.fromUTF8! ⟨detail.toArray⟩}"
  | .absent => "absent"

private def nextDeclaration (host : NativeHost.Config) (opened : NativeHost.Opened host)
    (nonce : Nat) : IO PolicyInstallController.Declaration := do
  let factory : PolicyId := ⟨host.deployment.factoryId⟩
  let some head := opened.authority.snapshot.currentHead factory
    | throw (IO.userError "factory has no policy head")
  let some old := CanonicalCellRegistry.loadPolicySource host.deployment.domain
      opened.directory.directory head.address
    | throw (IO.userError "factory policy source unavailable")
  let source := { old.record with
    version := head.version + 1
    previous := some head.address
    predicate := .any [.all []] }
  return ⟨opened.authority.snapshot.cell.root, some head, nonce, source⟩

private def install (host : NativeHost.Config) (signer : System.FilePath) (nonce : Nat) : IO Unit := do
  let opened ← IO.ofExcept (← NativeHost.openExisting host)
  let factory : PolicyId := ⟨host.deployment.factoryId⟩
  let declaration ← nextDeclaration host opened nonce
  let source := declaration.source
  let bytes := PolicyInstallController.encodeDeclaration declaration
  let successor := CanonicalCellRegistry.policySourceCreate host.deployment.domain source
  IO.println s!"successor policy-source cell {successor.cellId}"
  let plan ← match NativeHost.prepareLoaded host opened (.install ⟨7⟩ ⟨43⟩ bytes) with
    | .error reason => throw (IO.userError s!"install plan: {reason}")
    | .ok value => pure value
  let signatures ← plan.slots.mapM fun slot => do
    let (_, signature) ← sign signer 7 slot.header
    pure signature
  let call ← match NativeHost.assemble plan signatures with
    | .error reason => throw (IO.userError s!"assemble: {reason}")
    | .ok value => pure value
  let light ← match ← NativeHostLight.start host with
    | .ok light => pure light
    | .error detail => throw (IO.userError s!"light open: {detail}")
  let (outcome, _) ← FnFrontierCheckpoint.submitOrdinary host light call (NativeHost.confirmed host)
    (fun _ _ _ => pure ())
  let verdict := describe outcome
  IO.println s!"install submission: {verdict}"
  require s!"install commits (got {verdict})" (verdict == "committed")
  let reopened ← match ← NativeHost.openExisting host with
    | .error reason => throw (IO.userError s!"reopen: {reason}")
    | .ok value => pure value
  require "installed head is the successor"
    ((reopened.authority.snapshot.currentHead factory).map (·.version) == some source.version)
  require "successor source cell is live"
    ((CanonicalCellRegistry.loadPolicySource host.deployment.domain reopened.directory.directory
      (PolicyRecordCodec.digest source)).isSome)

private def prefixTrap (host : NativeHost.Config) (height : Nat) : IO Unit := do
  let db := host.storage.root / "forward-link.sqlite3"
  let trap ← IO.Process.output { cmd := "python3", args := #["-c",
    "import sqlite3,sys
db=sqlite3.connect(sys.argv[1])
h=int(sys.argv[2])
assert db.execute('select max(height) from durable_checkpoint').fetchone()==(h,)
db.execute('alter table durable_log rename to bench_log')
db.execute(f'create view durable_log as select height,tag, case when height < {h} then abs(-9223372036854775808) else record end as record from bench_log')
db.commit()
try: db.execute('select record from durable_log where height=1').fetchone()
except sqlite3.OperationalError as err: assert 'integer overflow' in str(err)
else: raise AssertionError('prefix trap did not fire')",
    db.toString, toString height] }
  unless trap.exitCode == 0 do throw (IO.userError trap.stderr)

/-- A cold session starts with no retained materialization. Trap physical prefix reads
in SQLite while opening it and resolving the current factory's authority. -/
private def measure (host : NativeHost.Config) (older : Nat) : IO Unit := do
  let full ← IO.ofExcept (← NativeHost.openExisting host)
  let ⟨_, reader⟩ ← IO.ofExcept (← DurableHistoryStore.readerOf host.transport ResourceBirthCodec.rootBytes full.durable)
  let walk ← IO.ofExcept ((← NativeHostReplay.verifyLoaded host reader full.durable).mapError (·.detail))
  prefixTrap host (older + 1)
  let session ← IO.ofExcept (← NativeHostSession.start host)
  let basis ← IO.ofExcept (← session.light.basis ⟨[], []⟩)
  let ground := ServedBasis.Ground.ofBasis basis
  let authority := host.deployment.authorityCellId
  require "cold light session does not materialize history" (session.full.isNone && session.walked.isNone)
  require "height and root agree with the full admission walk"
    (session.light.opening.head.height == older + 3 && session.light.opening.head.root == walk.opened.durable.worldRoot)
  require "authority bytes and current policy agree with the full admission walk"
    (session.light.opening.served.canonicalBytes ⟨authority⟩ == walk.opened.durable.snapshot.canonicalBytes ⟨authority⟩ &&
     ground.authority.currentHead ⟨host.deployment.factoryId⟩ == walk.opened.authority.snapshot.currentHead ⟨host.deployment.factoryId⟩)
  let declaration ← nextDeclaration host walk.opened (older + 4)
  let bytes := PolicyInstallController.encodeDeclaration declaration
  let fullPlan ← IO.ofExcept (NativeHost.prepareLoaded host walk.opened (.install ⟨7⟩ ⟨43⟩ bytes))
  let lightPlan ← IO.ofExcept ((← NativeHost.prepareInstallLight host session.light ⟨7⟩ ⟨43⟩ bytes none).mapError (·.detail))
  require "light and full consent planners produce identical signing bytes"
    (NativeHostCodec.signingPlanCodec.encode lightPlan == NativeHostCodec.signingPlanCodec.encode fullPlan)
  let stale := PolicyInstallController.encodeDeclaration
    { declaration with expectedPreRoot := ⟨declaration.expectedPreRoot.value + 1⟩ }
  let .error expected := NativeHost.prepareLoaded host walk.opened (.install ⟨7⟩ ⟨43⟩ stale)
    | throw (IO.userError "full planner accepted a forged authority root")
  let .error refusal ← NativeHost.prepareInstallLight host session.light ⟨7⟩ ⟨43⟩ stale none
    | throw (IO.userError "light planner accepted a forged authority root")
  require "light and full consent planners refuse the same stale preimage" (refusal.detail == expected)
  IO.println s!"PASS native session authority: prefix={older} tail=2 pre-checkpoint record reads=0"

private def signedCall (host : NativeHost.Config) (signer : System.FilePath)
    (descriptor : NativeHostCodec.Draft) : IO NativeHostCodec.SignedCall := do
  let opened ← IO.ofExcept (← NativeHost.openExisting host)
  let plan ← IO.ofExcept (NativeHost.prepareLoaded host opened descriptor)
  let signatures ← plan.slots.mapM fun slot => return (← sign signer 7 slot.header).2
  IO.ofExcept (NativeHost.assemble plan signatures)

private def submitOrdinary (host : NativeHost.Config) (call : NativeHostCodec.SignedCall) :
    IO NativeHostCodec.Receipt := do
  let light ← IO.ofExcept (← NativeHostLight.start host)
  let (outcome, _) ← FnFrontierCheckpoint.submitOrdinary host light call (NativeHost.confirmed host)
    (fun _ _ _ => pure ())
  let .confirmed _ receipt := outcome | throw (IO.userError (describe outcome))
  return receipt

private def invoke (host : NativeHost.Config) (signer : System.FilePath)
    (target capability nonce : Nat) : IO (List UInt8 × NativeHostCodec.Receipt) := do
  let opened ← IO.ofExcept (← NativeHost.openExisting host)
  let .present packed := opened.directory.directory.slots target | throw (IO.userError "missing content")
  let command := Minidregg.Verify.ResourceReserveBirthFixture.initializationCommand ⟨7⟩ nonce target
    ⟨capability⟩ packed.payload.root ⟨⟨nonce⟩⟩ ⟨3⟩ [1,2,3]
  let call ← signedCall host signer (.invoke (DeclaredResourceController.commandCodec.encode command))
  return (NativeHostCodec.callCodec.encode call, ← submitOrdinary host call)

private def withFrontier (host : NativeHost.Config) (poll : FnFrontierCheckpoint.Poll) (phase : String) :
    IO NativeHostCodec.Outcome := do
  let light ← IO.ofExcept (← NativeHostLight.start host)
  let some cut ← FnFrontierCheckpoint.loadAt host light.opening.head
    | throw (IO.userError "migrated cut did not advance")
  FnFrontierCheckpoint.receive host light cut poll phase (fun _ _ _ => pure ())

private def frontierProbe (host : NativeHost.Config) (cfg : NativeHostGenesis.Config)
    (signer : System.FilePath) (prefixHeight : Nat) : IO Unit := do
  let some pin := host.fnGateway | throw (IO.userError "missing fixture gateway")
  let scope : FnConsumerScope.Scope := ⟨[1],[2],[3],[4],[5],1,0,1⟩
  let opened ← IO.ofExcept (← NativeHost.openExisting host)
  let born := [Minidregg.Verify.ResourceReserveBirthFixture.content 7001 ⟨7⟩ ⟨1001⟩ ⟨1101⟩,
               Minidregg.Verify.ResourceReserveBirthFixture.content 7002 ⟨7⟩ ⟨1002⟩ ⟨1102⟩]
  let descriptor := Minidregg.Verify.ResourceReserveBirthFixture.ordinaryDescriptor host cfg opened ⟨7⟩ 71 7 born
  let law := NativeHostGenesis.policy host.profile cfg 7001 (.eq "request/subject" 7)
  let policies := descriptor.initialPolicies.map fun p => if p.policyId == law.policyId then
    ⟨law.policyId, PolicyRecordCodec.digest law, PolicyRecordCodec.encode law⟩ else p
  let descriptor := { descriptor with initialPolicies := policies }
  let call ← signedCall host signer (.birth (CanonicalCellRegistry.sourceEncoding.codec.encode descriptor)
    (List.replicate descriptor.resourceBatch.operations.length ⟨41⟩))
  discard <| submitOrdinary host call
  let opened ← IO.ofExcept (← NativeHost.openExisting host)
  let plan ← IO.ofExcept (Minidregg.Host.FnConsumerNamespacePlan.prepare host opened pin scope [6] 0 0)
  let registration ← IO.ofExcept (Minidregg.Host.FnConsumerNamespacePlan.assembleSignature host opened plan
    (← sign signer 7 plan.signingHeader).2)
  require "migration after birth" ((← FnFrontierCheckpoint.migrate host) == 1)
  let regResult ← withFrontier host (.registration registration) "fn-consumer-namespace"
  let .confirmed .installed registered := regResult | throw (IO.userError ("registration: " ++ describe regResult))
  let key := registration.spec.key
  let empty : FnEmptyPollProgressV2.Spec :=
    ⟨host.deployment.domain, host.profile.semantics, ⟨key,0,1,none,[8],FnConsumerFrontierCore.reportDigest []⟩,
      registered, pin.subject, pin.target, pin.capability⟩
  let opened ← IO.ofExcept (← NativeHost.openExisting host)
  let plan ← IO.ofExcept (Minidregg.Host.FnConsumerFrontierPlan.prepare host opened none (some empty) [8] [] [])
  let bytes ← IO.ofExcept (Minidregg.Host.FnConsumerFrontierPlan.assembleSignature host opened plan
    (← sign signer 7 plan.signingHeader).2)
  let some emptyIngress := FnEmptyPollProgressV2.ingressCodec.decode bytes | throw (IO.userError "empty frame")
  let result ← withFrontier host (.empty emptyIngress) "fn-empty-poll-v2"
  let .confirmed .installed progressed := result | throw (IO.userError ("empty: " ++ describe result))
  for i in List.range (prefixHeight - 4) do install host signer (200 + i)
  let (anchorCall, anchor) ← invoke host signer 7001 1001 800
  let _ ← invoke host signer 7002 1002 801
  let _ ← invoke host signer 7002 1002 802
  DurableServed.runAfterReply
  let opened ← IO.ofExcept (← NativeHost.openExisting host)
  let ⟨_, reader⟩ ← IO.ofExcept (← DurableHistoryStore.readerOf host.transport ResourceBirthCodec.rootBytes opened.durable)
  let full ← IO.ofExcept ((← NativeHostReplay.verifyLoaded host reader opened.durable).mapError (·.detail))
  let walked : NativeHostSession.Walked host := ⟨_, full⟩
  let sealed := FnFrontierCheckpoint.sealVerified full
  let restore := FnFrontierCheckpoint.restore host full.store.key
  require "cut rejects a different physical head"
    ((restore (opened.durable.height + 1) opened.durable.chain opened.durable.worldRoot sealed).isNone)
  require "cut rejects an altered authenticator"
    ((restore opened.durable.height opened.durable.chain opened.durable.worldRoot
      (sealed.set! 1 (sealed[1]! ^^^ 1))).isNone)
  let selected : FnSelectedPollCoverage.Ingress :=
    ⟨⟨host.deployment.domain, host.profile.semantics, ⟨key,1,1,2,some progressed,[9],⟨5⟩,⟨4⟩,[1],
      registered,⟨321⟩⟩, registered, pin.subject, pin.target, pin.capability⟩, [],⟨0⟩,⟨0⟩⟩
  let .confirmed .replayed oldReg ← FnConsumerNamespaceReceiver.receiveVerified full
      (FnConsumerNamespaceRegistration.ingressCodec.encode registration) | throw (IO.userError "full registration retry")
  let .confirmed .replayed oldEmpty ← FnEmptyPollReceiverV2.receiveVerified full bytes
    | throw (IO.userError "full empty retry")
  let .rejected oldReason ← FnSelectedPollReceiver.receiveVerified full (FnSelectedPollCoverage.ingressCodec.encode selected)
    | throw (IO.userError "full selected accepted missing original")
  let following := { empty with evidence := { empty.evidence with
    fromPosition := 1, toPosition := 2, predecessor := some progressed } }
  let planned ← IO.ofExcept (Minidregg.Host.FnConsumerFrontierPlan.prepare host opened none (some following) [8] [] [])
  let check := fun receipt => (NativeReserveContinuity.check walked receipt anchorCall ⟨7001⟩).map fun _ => ()
  let forged := { anchor with worldRoot := ⟨anchor.worldRoot.value + 1⟩ }
  require "full replay accepts reserve and refuses forged root" ((check anchor).isOk && !(check forged).isOk)
  prefixTrap host prefixHeight
  let light ← IO.ofExcept (← NativeHostLight.start host)
  let some cut ← FnFrontierCheckpoint.loadAt host light.opening.head | throw (IO.userError "cold cut")
  require "full and restored audits encode identically"
    (FnFrontierCheckpoint.auditStream.encode cut.snapshot.audit == FnFrontierCheckpoint.auditStream.encode full.frontier)
  let outcome := NativeHostCodec.outcomeCodec.encode
  require "registration replay bytes" (outcome (← withFrontier host (.registration registration) "fn-consumer-namespace")
    == outcome (.confirmed .replayed oldReg))
  require "selected refusal bytes" (outcome (← withFrontier host (.selected selected) "fn-selected-poll")
    == outcome (.refused .operationRejected "fn-selected-poll".toUTF8.toList oldReason.toUTF8.toList))
  require "empty replay bytes" (outcome (← withFrontier host (.empty emptyIngress) "fn-empty-poll-v2")
    == outcome (.confirmed .replayed oldEmpty))
  let cursor ← IO.ofExcept (cut.snapshot.audit.cursor key)
  let _ ← IO.ofExcept (cut.snapshot.audit.registrationFor key registered)
  require "ordered predecessor" (cursor.position == 1 && cursor.receipt == some progressed)
  let ground := ServedBasis.Ground.ofBasis (← IO.ofExcept (← light.basis ⟨[], []⟩))
  let next ← IO.ofExcept (Minidregg.Host.FnConsumerFrontierPlan.prepareAt host ground none (some following) [8] [] [])
  require "full and restored planning bytes"
    (Minidregg.Host.FnConsumerFrontierPlan.planCodec.encode next == Minidregg.Host.FnConsumerFrontierPlan.planCodec.encode planned)
  for receipt in [anchor, forged] do
    let indexed := cut.snapshot.provider.check host (NativeReserveContinuity.authorityCellsAt host ground.authority)
      receipt anchorCall.toByteArray ⟨7001⟩ none none
    require "provider continuity and exact refusal" (reprStr indexed == reprStr (check receipt))
  let prior : NativeProviderHistory.PriorChecked := ⟨anchor.acceptedCount, anchor.worldRoot⟩
  for point in [prior, { prior with worldRoot := forged.worldRoot }] do
    let historical := (NativeProviderHistory.checkPrior walked anchor.acceptedCount point).map fun _ => ()
    let indexed := cut.snapshot.provider.check host (NativeReserveContinuity.authorityCellsAt host ground.authority)
      anchor anchorCall.toByteArray ⟨7001⟩ none (some point)
    require "prior checked prefix verdict" (reprStr indexed == reprStr historical)
  IO.println s!"PASS admitted frontier: prefix={prefixHeight} tail=2; registration, selected refusal, empty, plan, provider; pre-checkpoint payload reads=0"


def run (verifier signer storeBinary : System.FilePath) (benchmark : Option Nat := none) (frontier := false) : IO Unit := do
  let (creatorPublic, _) ← sign signer 7 []
  let cfg := genesis creatorPublic
  let built ← match NativeHostGenesis.build profile cfg with
    | .error reason => throw (IO.userError s!"genesis build: {repr reason}")
    | .ok value => pure value
  IO.FS.withTempDir fun directory => do
    IO.FS.writeBinFile (directory / "key") ((List.range 32).map (fun i => UInt8.ofNat (i * 7 + 3))).toByteArray
    let storage : DurableReceiverIO.NativeConfig :=
      { binary := storeBinary, root := directory / "store", key := directory / "key", checkpointEvery := (benchmark.map (fun n => if frontier then n else n + 1)).getD 16 }
    let host : NativeHost.Config := NativeHost.Config.ofInputs
      { hostTemplate.toInputs with
        expectedSeed := NativeHost.seedIdentity built.seed
        storage := storage
        signature := ⟨verifier⟩
        fnGateway := if frontier then some ⟨[1],⟨7⟩,7001,⟨1001⟩,
          PolicyRecordCodec.digest (NativeHostGenesis.policy profile cfg 7001 (.eq "request/subject" 7))⟩ else none }
    match ← DurableReceiverIO.bootstrap host.transport ResourceBirthCodec.rootBytes built.seed with
    | .error reason => throw (IO.userError s!"native bootstrap: {reason}")
    | .ok () => pure ()
    match benchmark with
    | none =>
      install host signer 1
      IO.println "PASS neutral birth install (control)"
    | some older =>
      if frontier then return ← frontierProbe host cfg signer older
      for i in List.range (older + 3) do install host signer (i + 1)
      DurableServed.runAfterReply
      measure host older


end NeutralBirthInstallProbe

def main (args : List String) : IO Unit := do
  match args with
  | [verifier, signer, store, "frontier-reads"] => do
      for prefixHeight in [4, 40] do NeutralBirthInstallProbe.run verifier signer store (some prefixHeight) true
  | [verifier, signer, store, "session-reads"] => do
      for older in [2, 20] do NeutralBirthInstallProbe.run verifier signer store (some older)
  | [verifier, signer, store] => NeutralBirthInstallProbe.run verifier signer store
  | _ => throw (IO.userError "usage: neutral-birth-install VERIFIER SIGN-PROBE STORE-BINARY [session-reads|frontier-reads]")
