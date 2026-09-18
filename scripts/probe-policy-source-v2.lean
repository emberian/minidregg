import Compiler.CredentialAuthorityPolicyRegistry
import Kernel.PolicyInstallController

open Minidregg.Compiler.CanonicalPolicyAdmission
open Minidregg.Compiler.PolicyRecordCodec
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Pred

/-! These helpers build semantic fixtures through the checked domain editor
and complete catalogue assembler. They do not claim physical store provenance;
the production receiver obtains that from DomainReceiver.Loaded. -/
namespace AuthorityFixture

open Minidregg.Compiler
open Minidregg.Compiler.CredentialAuthorityPageMaterializer
open Minidregg.Theory.CellState
open Minidregg.Theory.TypedAuthorization

def fromPages (domain : Digest) (revision : Nat) (pages : List Page) :
    IO CredentialAuthorityDomain.Snapshot := do
  let catalogue : CredentialAuthorityDomain.Catalogue :=
    { domain := domain, revision := revision
      pages := pages.map fun page =>
        { number := page.pageNumber, cellId := ⟨1000 + page.pageNumber⟩
          physicalRoot := (materialize materializer (stateOfOption (some page))).root } }
  match CredentialAuthorityDomain.assemble catalogue pages with
  | none => throw (IO.userError "FAIL: complete semantic authority fixture rejected")
  | some snapshot => pure snapshot

def fromEntries (domain : Digest) (entries : List Entry) :
    IO CredentialAuthorityDomain.Snapshot := do
  match CredentialAuthorityDomain.runEdits domain []
      (entries.map fun entry => { before := none, after := entry }) with
  | none => throw (IO.userError "FAIL: routed authority fixture rejected")
  | some pages => fromPages domain 0 pages

end AuthorityFixture

namespace PolicySourceV2Probe

def record (predicate : Pred) : PolicyRecord where
  policyId := ⟨17⟩
  version := 3
  domain := ⟨100⟩
  semantics := ⟨200⟩
  previous := some ⟨300⟩
  predicate := predicate

def specimens : List Pred :=
  [ .eq "λ🐉" (Int.ofNat (2 ^ 512))
  , .le "" (-73)
  , .memberOf "member" [-1, 0, 1, -1]
  , .writeOnce "once"
  , .monotone "clock"
  , .witnessed ⟨"proof/v2"⟩
  , .not (.eq "key" 2)
  , .allL .nil
  , .anyL .nil
  , Pred.all [.writeOnce "once", Pred.any [.eq "key" 2, .not (.eq "key" 3)]] ]

def require (label : String) (accepted : Bool) : IO Unit := do
  unless accepted do throw (IO.userError s!"FAIL: {label}")

def main : IO Unit := do
  for predicate in specimens do
    let source := record predicate
    let bytes := encode source
    require "all AST constructors round-trip" (decide (decode bytes = some source))
    require "trailing bytes refuse" ((decode (bytes ++ [0])).isNone)
    require "v1 enumeration frame refuses" ((decode [165, 17, 255]).isNone)
  let source := record (Pred.all specimens)
  let bytes := encode source
  let payload := recordTupleStream.encode (recordTuple source)
  -- Policy id 17 has two canonical bytes [17,255]. Insert a redundant high
  -- zero digit; the primitive parser accepts it but the source decoder must not.
  let alternate := wireFrame ++ [17, 0, 255] ++ payload.drop 2
  require "noncanonical bytes reach raw parser"
    (decide (decodeRaw alternate = some source))
  require "redundant natural digit refuses" ((decode alternate).isNone)
  require "wrong token stack sort refuses" ((decodePred [.nil, .not]).isNone)
  require "token stack underflow refuses" ((decodePred [.cons]).isNone)
  require "unknown token refuses" ((decodeToken [255]).isNone)
  let changed := { source with predicate := .eq "different" 0 }
  require "complete AST affects source" (decide (encode changed ≠ bytes))
  require "complete AST affects address for probe pair"
    (decide (digest changed ≠ digest source))
  require "digest is a 256-bit value" (decide ((digest source).value < 256 ^ 32))
  let deployed := Minidregg.Compiler.CredentialAuthorityPolicyRegistry.Example.committedPolicy
  let fetched := Minidregg.Compiler.CredentialAuthorityPolicyRegistry.Example.payloadStore.fetch
    deployed.address
  require "existing payload consumer serves v2 source"
    (decide (fetched = some (encode deployed.record)))
  require "existing digest consumer selects v2 address"
    (decide (deployed.address = digest deployed.record))
  let selectedEntry := Minidregg.Compiler.CredentialAuthorityPageMaterializer.Entry.policy
    deployed.record.policyId deployed.record.version deployed.address
  let snapshot ← AuthorityFixture.fromEntries ⟨91000⟩ [selectedEntry]
  require "receiving resolver refuses domain mismatch"
    ((Minidregg.Compiler.CredentialAuthorityPolicyRegistry.loadPolicy snapshot
      Minidregg.Compiler.CredentialAuthorityPolicyRegistry.Example.payloadStore
      deployed.record.policyId deployed.record.version).isNone)
  let current ← AuthorityFixture.fromEntries deployed.record.domain [selectedEntry]
  require "actual receiving resolver loads current canonical source"
    ((Minidregg.Compiler.CredentialAuthorityPolicyRegistry.loadPolicy current
      Minidregg.Compiler.CredentialAuthorityPolicyRegistry.Example.payloadStore
      deployed.record.policyId deployed.record.version).isSome)
  require "full canonical authority codec accepts actual state bytes"
    ((Minidregg.Compiler.CredentialAuthorityStateCodec.decode current.cell.bytes).isSome)
  require "missing catalogue shard refuses complete snapshot"
    ((Minidregg.Compiler.CredentialAuthorityDomain.assemble current.catalogue []).isNone)
  require "actual receiving resolver refuses changed payload"
    ((Minidregg.Compiler.CredentialAuthorityPolicyRegistry.loadPolicy current
      { fetch := fun _ => some (encode { deployed.record with previous := some ⟨9876⟩ }) }
      deployed.record.policyId deployed.record.version).isNone)
  IO.println s!"PASS policy-source-v2: {specimens.length} constructors/closures, canonical decoding, malformed input, cSHAKE and existing registry consumer; combined source {bytes.length} bytes"

end PolicySourceV2Probe

namespace PolicyInstallPreparationProbe

open Minidregg.Compiler
open Minidregg.Compiler.CredentialAuthorityPageMaterializer
open Minidregg.Compiler.CredentialAuthorityPolicyRegistry
open Minidregg.Kernel
open Minidregg.Kernel.CanonicalPolicyRegistry
open Minidregg.Theory.TypedAuthorization

local instance : Fact (Nat.Prime 65537) := ⟨by norm_num⟩
abbrev F := ZMod 65537

/-- Executable arithmetic/profile fixture, not a deployment-field choice. -/
def runtime : CanonicalRuntimeProfile.Profile F :=
  .source ⟨⟨99⟩, 10000, 1000⟩ ⟨65537⟩ 65537 inferInstance 8
    (PredOrder.noWrap_zmod (by norm_num))

def source (version : Nat) (previous : Option Digest) (predicate : Pred) : PolicyRecord where
  policyId := ⟨17⟩
  version := version
  domain := ⟨500⟩
  semantics := runtime.semantics
  previous := previous
  predicate := predicate

def initialSource := source 0 none
  (Pred.all [.eq "request/subject" 7, .eq "policy/version" 1, .monotone "policy/version"])

def initialEntries : List Entry :=
  [ .policy initialSource.policyId 0 (policyRecordDigest initialSource)
  , .subjectKeyEpoch ⟨7⟩ 2
  , .issuerEpoch ⟨99⟩ 3
  , .nullifier 123 false
  , .subjectKeyEpoch ⟨111⟩ 4
  , .revocation (.channel ⟨42⟩) true ]

def context (epoch : Nat) : PolicyInstallController.RequestContext where
  federation := ⟨20⟩
  subject := ⟨7⟩
  subjectKeyEpoch := 2
  height := 50
  policyEpoch := epoch

/-- The source-only fixture intentionally has no signature verifier or receipt
constructor. Actual accepted installs run in the native capability-use probe. -/
def store (sources : List PolicyRecord) : PayloadStore where
  fetch := fun address => sources.findSome? fun record =>
    if policyRecordDigest record = address then some (policyRecordCodec.encode record) else none

def declaration (snapshot : Snapshot) (old next : PolicyRecord) (nonce : Nat) :
    PolicyInstallController.Declaration where
  expectedPreRoot := snapshot.cell.root
  expected := some ⟨old.version, policyRecordDigest old⟩
  nonce := nonce
  source := next

def requireError {α : Type} (label : String) (expected : PolicyInstallController.Reject)
    (result : Except PolicyInstallController.Reject α) : IO Unit :=
  match result with
  | .error reason => PolicySourceV2Probe.require label (decide (reason = expected))
  | .ok _ => throw (IO.userError s!"FAIL: {label} was accepted")

def prepare (snapshot : Snapshot) (epoch : Nat) (decl : PolicyInstallController.Declaration) :
    IO (PolicyInstallController.Prepared runtime snapshot (context epoch)) :=
  match PolicyInstallController.prepare runtime snapshot (context epoch)
      (PolicyInstallController.encodeDeclaration decl) with
  | .error reason => throw (IO.userError s!"FAIL: source preparation {repr reason}")
  | .ok prepared => pure prepared

def compiledVerdict {snapshot : Snapshot} {epoch : Nat}
    (prepared : PolicyInstallController.Prepared runtime snapshot (context epoch))
    (sources : List PolicyRecord) : Bool :=
  let config := prepared.policyConfig (store sources)
  let wanted := PolicyInstallController.request runtime snapshot (context epoch) prepared.declaration
  match config.registry.resolve wanted.policyId wanted.policyEpoch with
  | none => false
  | some committed => config.verifies wanted
      (canonicalWitness runtime.compilerProfile.compiler committed prepared.step.oldState prepared.step.newState)

def main : IO Unit := do
  let initial ← AuthorityFixture.fromEntries initialSource.domain initialEntries
  PolicySourceV2Probe.require "complete authority spans several shards"
    (decide (initial.pages.length > 1 ∧ initial.entries.length = initialEntries.length))
  let firstSource := source 1 (some (policyRecordDigest initialSource))
    (Pred.all [.eq "policy/version" 2, .monotone "policy/version"])
  let firstDecl := declaration initial initialSource firstSource 11
  let first ← prepare initial 0 firstDecl
  PolicySourceV2Probe.require "old compiled policy accepts exact candidate including scalar order"
    (compiledVerdict first [initialSource])
  let firstSnapshot ← AuthorityFixture.fromPages initial.domain 1 first.postPages
  PolicySourceV2Probe.require "routed candidate has exact new canonical head"
    (decide (firstSnapshot.currentHead ⟨17⟩ = some ⟨1, policyRecordDigest firstSource⟩))
  let marker := (PolicyInstallController.requestDigest runtime initial (context 0) firstDecl).value
  PolicySourceV2Probe.require "same candidate consumes exact signature marker"
    (Minidregg.Theory.CredentialAuthorityState.isNullified firstSnapshot.cell marker)
  PolicySourceV2Probe.require "retired version removed from complete authority"
    (decide (firstSnapshot.logical.fields (.policyAddress ⟨17⟩ 0) = none))
  PolicySourceV2Probe.require "unrelated key epoch and channel retained"
    (decide (firstSnapshot.authState.subjectKeyEpoch ⟨7⟩ = 2 ∧
      RevocationKey.channel ⟨42⟩ ∈ firstSnapshot.authState.revoked))
  let other ← prepare initial 0 { firstDecl with nonce := 12 }
  let leftStep := PolicyStepContext.ofCandidate (fun _ => ⟨[]⟩) runtime.semantics first.candidate
  let rightStep := PolicyStepContext.ofCandidate (fun _ => ⟨[]⟩) runtime.semantics other.candidate
  PolicySourceV2Probe.require "same lossy probe views have distinct real source commitments"
    (decide (leftStep.oldState = rightStep.oldState ∧ leftStep.newState = rightStep.newState ∧
      leftStep.effectsDigest ≠ rightStep.effectsDigest))
  PolicySourceV2Probe.require "equal views cannot substitute another declaration"
    (!(PolicyStepBinding.canonical rightStep).matches
      (PolicyInstallController.request runtime initial (context 0) firstDecl)
      leftStep.oldState leftStep.newState)
  let firstBytes := PolicyInstallController.encodeDeclaration firstDecl
  requireError "noncanonical bytes refuse" .malformedDeclaration
    (PolicyInstallController.prepare runtime initial (context 0) (firstBytes ++ [0]))
  for (label, expected, changed) in
      [("stale pre-root", .staleRoot, { firstDecl with expectedPreRoot := ⟨0⟩ }),
       ("stale head", .staleHead, { firstDecl with expected := some ⟨0, ⟨9⟩⟩ }),
       ("skipped version", .invalidSuccessor, { firstDecl with source := { firstSource with version := 2 } }),
       ("wrong predecessor", .invalidSuccessor, { firstDecl with source := { firstSource with previous := some ⟨9⟩ } }),
       ("wrong domain", .wrongDomain, { firstDecl with source := { firstSource with domain := ⟨501⟩ } }),
       ("wrong semantics", .wrongSemantics, { firstDecl with source := { firstSource with semantics := ⟨0⟩ } })] do
    requireError label expected (PolicyInstallController.prepare runtime initial (context 0)
      (PolicyInstallController.encodeDeclaration changed))
  let secondSource := source 2 (some (policyRecordDigest firstSource)) (.eq "policy/version" 9)
  let second ← prepare firstSnapshot 1 (declaration firstSnapshot firstSource secondSource 12)
  PolicySourceV2Probe.require "newly selected source compiled on next candidate"
    (compiledVerdict second [firstSource, initialSource])
  let secondSnapshot ← AuthorityFixture.fromPages initial.domain 2 second.postPages
  let weakening := source 3 (some (policyRecordDigest secondSource)) (.allL .nil)
  let third ← prepare secondSnapshot 2 (declaration secondSnapshot secondSource weakening 13)
  PolicySourceV2Probe.require "weaker proposed source cannot satisfy old compiled policy"
    (!(compiledVerdict third [secondSource, firstSource, initialSource]))
  PolicySourceV2Probe.require "missing selected source refuses compiler gate" (!(compiledVerdict first []))
  IO.println "PASS policy preparation: complete multishard head+marker candidate, actual bounded order fold, old-source selection and weakening refusal, exact request/source binding. Native accepted installs are checked by probe-native-capability-use; no signature fixture or fabricated accepted token here."

end PolicyInstallPreparationProbe

def main : IO Unit := do
  PolicySourceV2Probe.main
  PolicyInstallPreparationProbe.main
