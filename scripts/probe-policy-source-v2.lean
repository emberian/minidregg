import Compiler.CredentialAuthorityPolicyRegistry

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

def main : IO Unit := PolicySourceV2Probe.main
