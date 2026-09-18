import Compiler.CredentialAuthorityPolicyRegistry
import Kernel.PolicyInstallController

open Minidregg.Compiler.CanonicalPolicyAdmission
open Minidregg.Compiler.PolicyRecordCodec
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Pred

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
  let snapshot := Minidregg.Compiler.CredentialAuthorityPolicyRegistry.Snapshot.ofPage
    Minidregg.Compiler.CredentialAuthorityPolicyRegistry.Example.policyPage
    Minidregg.Compiler.CredentialAuthorityPolicyRegistry.Example.policyPage_valid
  -- The historical example record deliberately used another authority domain;
  -- the actual receiving resolver must refuse it even though its hash matches.
  require "receiving resolver refuses domain mismatch"
    ((Minidregg.Compiler.CredentialAuthorityPolicyRegistry.loadPolicy snapshot
      Minidregg.Compiler.CredentialAuthorityPolicyRegistry.Example.payloadStore
      deployed.record.policyId deployed.record.version).isNone)
  let page : Minidregg.Compiler.CredentialAuthorityPageMaterializer.Page :=
    { Minidregg.Compiler.CredentialAuthorityPolicyRegistry.Example.policyPage with
    authorityDomain := deployed.record.domain }
  have pageValid : page.Valid := by
    simpa [page, Minidregg.Compiler.CredentialAuthorityPageMaterializer.Page.Valid,
      Minidregg.Compiler.CredentialAuthorityPageMaterializer.Page.fields,
      Minidregg.Compiler.CredentialAuthorityPageMaterializer.Page.entries] using
      Minidregg.Compiler.CredentialAuthorityPolicyRegistry.Example.policyPage_valid
  let current := Minidregg.Compiler.CredentialAuthorityPolicyRegistry.Snapshot.ofPage page pageValid
  require "actual receiving resolver loads current canonical source"
    ((Minidregg.Compiler.CredentialAuthorityPolicyRegistry.loadPolicy current
      Minidregg.Compiler.CredentialAuthorityPolicyRegistry.Example.payloadStore
      deployed.record.policyId deployed.record.version).isSome)
  require "actual canonical page decoder accepts current bytes"
    ((Minidregg.Compiler.CredentialAuthorityPolicyRegistry.decodeSnapshot current.cell.bytes).isSome)
  require "actual receiving resolver refuses changed payload"
    ((Minidregg.Compiler.CredentialAuthorityPolicyRegistry.loadPolicy current
      { fetch := fun _ => some (encode { deployed.record with previous := some ⟨9876⟩ }) }
      deployed.record.policyId deployed.record.version).isNone)
  IO.println s!"PASS policy-source-v2: {specimens.length} constructors/closures, canonical decoding, malformed input, cSHAKE and existing registry consumer; combined source {bytes.length} bytes"

end PolicySourceV2Probe

namespace PolicyInstallProbe

open Minidregg.Compiler.CredentialAuthorityPageMaterializer
open Minidregg.Compiler.CredentialAuthorityPolicyRegistry
open Minidregg.Kernel
open Minidregg.Kernel.CanonicalPolicyRegistry
open Minidregg.Theory.TypedAuthorization

local instance : Fact (Nat.Prime 65537) := ⟨by norm_num⟩

abbrev F := ZMod 65537

def source (version : Nat) (previous : Option Digest) (predicate : Pred) : PolicyRecord where
  policyId := ⟨17⟩
  version := version
  domain := ⟨500⟩
  semantics := PolicyInstallController.semantics
  previous := previous
  predicate := predicate

def initialSource := source 0 none
  (Pred.all [.eq "request/subject" 7, .eq "policy/version" 1])

def initialPage : Page where
  authorityDomain := initialSource.domain
  pageNumber := 4
  slot0 := some (.policy initialSource.policyId 0 (policyRecordDigest initialSource))
  slot1 := some (.subjectKeyEpoch ⟨7⟩ 2)
  slot2 := some (.issuerEpoch ⟨99⟩ 3)
  slot3 := some (.nullifier 123 false)

theorem initialPage_valid : initialPage.Valid := by decide

def initial := Snapshot.ofPage initialPage initialPage_valid

def context (epoch : Nat) : PolicyInstallController.RequestContext where
  federation := ⟨20⟩
  subject := ⟨7⟩
  subjectKeyEpoch := 2
  height := 50
  policyEpoch := epoch

/-- Explicit verifier fixture: this checks the controller calls the verifier
and propagates refusal. It makes no cryptographic signature-soundness claim. -/
def signatureFixture : Portal :=
  { Minidregg.Theory.TypedAuthorization.demoPortal with
    SignatureWitness := Bool
    verifySignature := fun _ accepted => accepted }

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

def main : IO Unit := do
  let firstSource := source 1 (some (policyRecordDigest initialSource)) (.eq "policy/version" 2)
  let firstDecl := declaration initial initialSource firstSource 11
  let firstBytes := PolicyInstallController.encodeDeclaration firstDecl
  let first ← match PolicyInstallController.run (F := F) initial (context 0)
      (store [initialSource]) signatureFixture firstBytes true with
    | .error reason => throw (IO.userError s!"FAIL: first install {repr reason}")
    | .ok installed => pure installed
  let firstSnapshot ← match decodeSnapshot first.post.bytes with
    | none => throw (IO.userError "FAIL: first actual post did not decode")
    | some decoded => pure decoded.val
  let other ← match PolicyInstallController.prepare initial (context 0)
      (PolicyInstallController.encodeDeclaration { firstDecl with nonce := 12 }) with
    | .error reason => throw (IO.userError s!"FAIL: second declaration candidate {repr reason}")
    | .ok prepared => pure prepared
  -- This deliberately lossy view exercises the general candidate/context seam.
  -- It is fixed here in the probe, never supplied to the production receiver.
  let leftStep := PolicyStepContext.ofCandidate (fun _ => ⟨[]⟩)
    PolicyInstallController.semantics first.prepared.candidate
  let rightStep := PolicyStepContext.ofCandidate (fun _ => ⟨[]⟩)
    PolicyInstallController.semantics other.candidate
  PolicySourceV2Probe.require "equal predicate views are inhabited"
    (decide (leftStep.oldState = rightStep.oldState ∧ leftStep.newState = rightStep.newState))
  PolicySourceV2Probe.require "distinct declaration commitments are inhabited"
    (decide (leftStep.effectsDigest ≠ rightStep.effectsDigest))
  PolicySourceV2Probe.require "same views do not permit declaration substitution"
    (!(PolicyStepBinding.canonical rightStep).matches
      (PolicyInstallController.request initial (context 0) firstDecl)
      leftStep.oldState leftStep.newState)
  PolicySourceV2Probe.require "installed source selected in actual post"
    (decide (PolicyInstallController.currentHead firstSnapshot.page ⟨17⟩ =
      some ⟨1, policyRecordDigest firstSource⟩))
  PolicySourceV2Probe.require "unrelated key epoch retained"
    (decide ((Minidregg.Compiler.CredentialAuthorityPolicyRegistry.projection.authState
      firstSnapshot.cell).subjectKeyEpoch ⟨7⟩ = 2))
  requireError "signature refusal reaches actual controller" .signature
    (PolicyInstallController.run (F := F) initial (context 0) (store [initialSource])
      signatureFixture firstBytes false)
  requireError "stale signing epoch refuses" .subjectKeyEpoch
    (PolicyInstallController.run (F := F) initial
      { context 0 with subjectKeyEpoch := 1 } (store [initialSource])
      signatureFixture firstBytes true)
  requireError "stale policy epoch refuses" .policyEpoch
    (PolicyInstallController.run (F := F) initial (context 1) (store [initialSource])
      signatureFixture firstBytes true)
  requireError "authored subject restriction uses fixed request view" .policyRejected
    (PolicyInstallController.run (F := F) initial
      { context 0 with subject := ⟨8⟩, subjectKeyEpoch := 0 } (store [initialSource])
      signatureFixture firstBytes true)
  requireError "noncanonical install bytes refuse" .malformedDeclaration
    (PolicyInstallController.run (F := F) initial (context 0) (store [initialSource])
      signatureFixture (firstBytes ++ [0]) true)
  requireError "stale actual pre root refuses" .staleRoot
    (PolicyInstallController.run (F := F) initial (context 0) (store [initialSource])
      signatureFixture
      (PolicyInstallController.encodeDeclaration { firstDecl with expectedPreRoot := ⟨0⟩ }) true)
  requireError "exact old head refuses substitution" .staleHead
    (PolicyInstallController.run (F := F) initial (context 0) (store [initialSource])
      signatureFixture
      (PolicyInstallController.encodeDeclaration { firstDecl with expected := some ⟨0, ⟨9⟩⟩ }) true)
  requireError "version skip refuses" .invalidSuccessor
    (PolicyInstallController.run (F := F) initial (context 0) (store [initialSource])
      signatureFixture
      (PolicyInstallController.encodeDeclaration
        { firstDecl with source := { firstSource with version := 2 } }) true)
  requireError "wrong predecessor refuses" .invalidSuccessor
    (PolicyInstallController.run (F := F) initial (context 0) (store [initialSource])
      signatureFixture
      (PolicyInstallController.encodeDeclaration
        { firstDecl with source := { firstSource with previous := some ⟨9⟩ } }) true)
  requireError "wrong source domain refuses" .wrongDomain
    (PolicyInstallController.run (F := F) initial (context 0) (store [initialSource])
      signatureFixture
      (PolicyInstallController.encodeDeclaration
        { firstDecl with source := { firstSource with domain := ⟨501⟩ } }) true)
  requireError "wrong source semantics refuses" .wrongSemantics
    (PolicyInstallController.run (F := F) initial (context 0) (store [initialSource])
      signatureFixture
      (PolicyInstallController.encodeDeclaration
        { firstDecl with source := { firstSource with semantics := ⟨0⟩ } }) true)
  requireError "missing old source refuses" .policyUnavailable
    (PolicyInstallController.run (F := F) initial (context 0) (store [])
      signatureFixture firstBytes true)
  requireError "unsupported AST cannot be installed as executable policy" .unsupportedPolicy
    (PolicyInstallController.run (F := F) initial (context 0) (store [initialSource])
      signatureFixture
      (PolicyInstallController.encodeDeclaration
        { firstDecl with source := { firstSource with predicate := .monotone "policy/version" } }) true)
  let secondSource := source 2 (some (policyRecordDigest firstSource)) (.eq "policy/version" 9)
  let secondDecl := declaration firstSnapshot firstSource secondSource 12
  let second ← match PolicyInstallController.run (F := F) firstSnapshot (context 1)
      (store [firstSource, initialSource]) signatureFixture
      (PolicyInstallController.encodeDeclaration secondDecl) true with
    | .error reason => throw (IO.userError s!"FAIL: installed predicate invocation {repr reason}")
    | .ok installed => pure installed
  let secondSnapshot ← match decodeSnapshot second.post.bytes with
    | none => throw (IO.userError "FAIL: second actual post did not decode")
    | some decoded => pure decoded.val
  let weakening := source 3 (some (policyRecordDigest secondSource)) (.allL .nil)
  requireError "new weaker policy cannot authorize its own install" .policyRejected
    (PolicyInstallController.run (F := F) secondSnapshot (context 2)
      (store [secondSource, firstSource, initialSource]) signatureFixture
      (PolicyInstallController.encodeDeclaration
        (declaration secondSnapshot secondSource weakening 13)) true)
  PolicySourceV2Probe.require "old epoch no longer resolves after installation"
    ((loadPolicy secondSnapshot (store [secondSource, firstSource, initialSource]) ⟨17⟩ 1).isNone)
  IO.println "PASS policy-install: actual page install, newly installed rule invoked, old rule prevents self-authorized weakening, distinct declarations with equal views refuse, canonical bytes and signature/key/policy/root/head/version/domain/semantics/source refusals (verifier fixture, not cryptographic signature proof)"

end PolicyInstallProbe

def main : IO Unit := do
  PolicySourceV2Probe.main
  PolicyInstallProbe.main
