/-
Bounded JSON authoring for the native host. JSON is only a human-facing
notation: successful authoring constructs the real source values and invokes
their canonical codecs. All unbounded integers are decimal strings.
-/
import Kernel.NativeHost
import Host.BirthRuntimeProfile
import Host.CapabilityInspection
import Kernel.NativeHostGenesis
import Kernel.AgentGrain
import Kernel.CapabilityRevocationController
import Kernel.ContentResource
import Kernel.ApplicationGrainBirth
import Kernel.ApplicationGrainSessionBirth
import Kernel.ApplicationShareIssueAuthoring
import Kernel.ApplicationDispatchAuthoring
import Host.ApplicationLifecycleCompletionAuthoring
import Host.ApplicationLifecycleCompletionOperator
import Host.ApplicationLifecycleBeginOperator
import Host.ApplicationLifecycleLaunchBeginInspection
import Host.ApplicationLifecycleLaunchClaimInspection
import Host.ApplicationLifecycleLaunchCompletionInspection
import Host.ApplicationLifecycleLaunchReportAuthoring
import Host.ApplicationAgentLifetimeGrantInspection
import Host.ApplicationLifecycleClaimOperator
import Host.ApplicationDispatchAgentPaidInspection
import Host.ApplicationAgentLifetimeDispatchPaidInspection
import Host.ApplicationShareIssueGrainInspection
import Host.ApplicationGrainSessionEnrollmentInspection
import Kernel.ApplicationDispatchAgentReserveContext
import Kernel.ApplicationDispatchCodec
import Kernel.ParticipantKeyEnrollment
import Kernel.ApplicationLifecycleResidentProfile
import Host.ApplicationPermissionSchemaAuthoring
import Host.ApplicationSpkLaunchDescriptorAuthoring
import Lean.Data.Json

namespace Minidregg.Host.Json

open Lean
open Minidregg
open Minidregg.Pred
open Minidregg.Theory
open Minidregg.Theory.CellRegistry
open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.CredentialSigningKey
open Minidregg.Theory.DeclaredActionLowering
open Minidregg.Compiler
open Minidregg.Compiler.CanonicalPolicyAdmission
open Minidregg.Compiler.NativeHostCodec
open Minidregg.Compiler.NativeObservationCodec
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Kernel

set_option autoImplicit false

abbrev Result := Except String

private structure ScanFrame where
  object : Bool
  expectKey : Bool := false
  keys : List String := []

private def scanString : List Char → List Char → Result (List Char × List Char)
  | [], _ => .error "unterminated JSON string"
  | '"' :: rest, reversed => pure (('"' :: reversed).reverse, rest)
  | '\\' :: escaped :: rest, reversed => scanString rest (escaped :: '\\' :: reversed)
  | '\\' :: [], _ => .error "unterminated JSON escape"
  | c :: rest, reversed => scanString rest (c :: reversed)

private partial def duplicateScan : List Char → List ScanFrame → Result Unit
  | [], [] => pure ()
  | [], _ => .error "unterminated JSON container"
  | c :: rest, stack =>
      if c.isWhitespace then duplicateScan rest stack else
      match c, stack with
      | '{', _ => duplicateScan rest (⟨true, true, []⟩ :: stack)
      | '[', _ => duplicateScan rest (⟨false, false, []⟩ :: stack)
      | '}', frame :: tail =>
          if frame.object then duplicateScan rest tail else .error "mismatched JSON container"
      | ']', frame :: tail =>
          if frame.object then .error "mismatched JSON container" else duplicateScan rest tail
      | ',', frame :: tail =>
          if frame.object then duplicateScan rest ({ frame with expectKey := true } :: tail)
          else duplicateScan rest stack
      | '"', frame :: tail => do
          let (token, suffix) ← scanString rest ['"']
          if frame.object ∧ frame.expectKey then
            let keyJson ← Lean.Json.parse (String.ofList token)
            let key ← keyJson.getStr?
            if frame.keys.contains key then throw s!"duplicate JSON object field: {key}"
            duplicateScan suffix ({ frame with expectKey := false, keys := key :: frame.keys } :: tail)
          else duplicateScan suffix stack
      | '"', [] => do
          let (_, suffix) ← scanString rest ['"']
          duplicateScan suffix []
      | _, _ => duplicateScan rest stack

/-- Parse JSON without Lean's usual duplicate-key overwrite. Main must use
this boundary before calling `author` or `signatures`. -/
def parse (source : String) : Result Lean.Json := do
  duplicateScan source.toList []
  Lean.Json.parse source

private def failAt {α : Type} (path message : String) : Result α :=
  .error s!"{path}: {message}"

private def object (path : String) (json : Lean.Json) :
    Result (Std.TreeMap.Raw String Lean.Json compare) :=
  (json.getObj?).mapError (fun e => s!"{path}: {e}")

private def exactObject (path : String) (fields : List String) (json : Lean.Json) :
    Result (Std.TreeMap.Raw String Lean.Json compare) := do
  let value ← object path json
  let actual := value.foldl (init := []) (fun names key _ => key :: names)
  for key in fields do
    unless actual.contains key do throw s!"{path}: missing field {key}"
  for key in actual do
    unless fields.contains key do throw s!"{path}: unknown field {key}"
  pure value

private def field (path name : String)
    (obj : Std.TreeMap.Raw String Lean.Json compare) : Result Lean.Json :=
  match obj.get? name with
  | some value => pure value
  | none => failAt path s!"missing field {name}"

private def string (path : String) (json : Lean.Json) : Result String :=
  json.getStr?.mapError (fun _ => s!"{path}: string expected")

private def nat (path : String) (json : Lean.Json) : Result Nat := do
  let source ← string path json
  match source.toNat? with
  | some value =>
      if toString value = source then pure value
      else failAt path "canonical unsigned decimal string expected"
  | none => failAt path "unsigned decimal string expected"

private def int (path : String) (json : Lean.Json) : Result Int := do
  let source ← string path json
  match source.toInt? with
  | some value =>
      if toString value = source then pure value
      else failAt path "canonical signed decimal string expected"
  | none => failAt path "signed decimal string expected"

private def bool (path : String) (json : Lean.Json) : Result Bool :=
  json.getBool?.mapError (fun _ => s!"{path}: boolean expected")

private def array (path : String) (json : Lean.Json) : Result (Array Lean.Json) :=
  json.getArr?.mapError (fun _ => s!"{path}: array expected")

private def list {α : Type} (path : String) (decode : String → Lean.Json → Result α)
    (json : Lean.Json) : Result (List α) := do
  let values ← array path json
  let mut out := []
  for i in [:values.size] do
    out := out ++ [← decode s!"{path}[{i}]" values[i]!]
  pure out

private def optional {α : Type} (path : String) (decode : String → Lean.Json → Result α)
    (json : Lean.Json) : Result (Option α) :=
  if json.isNull then pure none else some <$> decode path json

private def hexNibble (c : Char) : Option Nat :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (10 + c.toNat - 'a'.toNat)
  else if 'A' ≤ c ∧ c ≤ 'F' then some (10 + c.toNat - 'A'.toNat)
  else none

def decodeHex (path : String) (json : Lean.Json) : Result (List UInt8) := do
  let source ← string path json
  let input := source.toUTF8
  unless input.size % 2 = 0 do
    failAt path "even-length hexadecimal string expected"
  let mut output := ByteArray.empty
  for i in [:input.size / 2] do
    let high := hexNibble (Char.ofNat (input[2 * i]!.toNat))
    let low := hexNibble (Char.ofNat (input[2 * i + 1]!.toNat))
    match high, low with
    | some h, some l => output := output.push (UInt8.ofNat (16 * h + l))
    | _, _ => failAt path "even-length hexadecimal string expected"
  pure output.toList

private def hexDigit (n : Nat) : Char :=
  Char.ofNat (if n < 10 then '0'.toNat + n else 'a'.toNat + n - 10)

def encodeHex (bytes : List UInt8) : String :=
  Id.run do
    let mut output := ByteArray.empty
    for byte in bytes do
      output := output.push (UInt8.ofNat ((hexDigit (byte.toNat / 16)).toNat))
      output := output.push (UInt8.ofNat ((hexDigit (byte.toNat % 16)).toNat))
    return String.fromUTF8! output

private def decimal (value : Nat) : Lean.Json := .str (toString value)
private def signedDecimal (value : Int) : Lean.Json := .str (toString value)
private def hexJson (value : List UInt8) : Lean.Json := .str (encodeHex value)

private def tagged (path : String) (json : Lean.Json) : Result
    (String × Std.TreeMap.Raw String Lean.Json compare) := do
  let obj ← object path json
  let tag ← string (path ++ ".type") (← field path "type" obj)
  pure (tag, obj)

partial def predicate (path : String) (json : Lean.Json) : Result Pred := do
  let (tag, _) ← tagged path json
  match tag with
  | "eq" | "le" =>
      let obj ← exactObject path ["type", "slot", "value"] json
      let slot ← string (path ++ ".slot") (← field path "slot" obj)
      let value ← int (path ++ ".value") (← field path "value" obj)
      pure <| if tag = "eq" then .eq slot value else .le slot value
  | "memberOf" =>
      let obj ← exactObject path ["type", "slot", "values"] json
      pure (.memberOf (← string (path ++ ".slot") (← field path "slot" obj))
        (← list (path ++ ".values") int (← field path "values" obj)))
  | "writeOnce" | "monotone" =>
      let obj ← exactObject path ["type", "slot"] json
      let slot ← string (path ++ ".slot") (← field path "slot" obj)
      pure <| if tag = "writeOnce" then .writeOnce slot else .monotone slot
  | "witnessed" =>
      let obj ← exactObject path ["type", "identifier"] json
      pure (.witnessed ⟨← string (path ++ ".identifier") (← field path "identifier" obj)⟩)
  | "not" =>
      let obj ← exactObject path ["type", "predicate"] json
      pure (.not (← predicate (path ++ ".predicate") (← field path "predicate" obj)))
  | "all" | "any" =>
      let obj ← exactObject path ["type", "predicates"] json
      let children ← list (path ++ ".predicates") predicate (← field path "predicates" obj)
      pure <| if tag = "all" then Pred.all children else Pred.any children
  | _ => failAt (path ++ ".type") "unknown predicate constructor"

private partial def predicateJson : Pred → Lean.Json
  | .eq slot value => .mkObj [("type", "eq"), ("slot", .str slot),
      ("value", signedDecimal value)]
  | .le slot value => .mkObj [("type", "le"), ("slot", .str slot),
      ("value", signedDecimal value)]
  | .memberOf slot values => .mkObj [("type", "memberOf"), ("slot", .str slot),
      ("values", .arr (values.toArray.map signedDecimal))]
  | .writeOnce slot => .mkObj [("type", "writeOnce"), ("slot", .str slot)]
  | .monotone slot => .mkObj [("type", "monotone"), ("slot", .str slot)]
  | .witnessed identifier => .mkObj [("type", "witnessed"),
      ("identifier", .str identifier.id)]
  | .not child => .mkObj [("type", "not"), ("predicate", predicateJson child)]
  | .allL children => .mkObj [("type", "all"),
      ("predicates", .arr (children.toList.toArray.map predicateJson))]
  | .anyL children => .mkObj [("type", "any"),
      ("predicates", .arr (children.toList.toArray.map predicateJson))]

private def resourceKind (path : String) (json : Lean.Json) : Result ResourceKind := do
  match ← string path json with
  | "object" => pure .object
  | "account" => pure .account
  | "program" => pure .program
  | _ => failAt path "expected object, account, or program"

private def policyRecord (path : String) (json : Lean.Json) : Result PolicyRecord := do
  let obj ← exactObject path
    ["policyId", "version", "domain", "semantics", "previous", "predicate"] json
  pure {
    policyId := ⟨← nat (path ++ ".policyId") (← field path "policyId" obj)⟩
    version := ← nat (path ++ ".version") (← field path "version" obj)
    domain := ⟨← nat (path ++ ".domain") (← field path "domain" obj)⟩
    semantics := ⟨← nat (path ++ ".semantics") (← field path "semantics" obj)⟩
    previous := (← optional (path ++ ".previous") nat (← field path "previous" obj)).map Digest.mk
    predicate := ← predicate (path ++ ".predicate") (← field path "predicate" obj) }

private def holder (path : String) (json : Lean.Json) : Result Holder := do
  let (tag, _) ← tagged path json
  match tag with
  | "bearer" => exactObject path ["type"] json *> pure .bearer
  | "subject" =>
      let obj ← exactObject path ["type", "subject"] json
      pure (.subject ⟨← nat (path ++ ".subject") (← field path "subject" obj)⟩)
  | _ => failAt (path ++ ".type") "expected bearer or subject"

private def verb (kind : ResourceKind) (path : String) (json : Lean.Json) : Result (Verb kind) := do
  let name ← string path json
  match kind, name with
  | .object, "observe" => pure .observeObject
  | .object, "mutate" => pure .mutateObject
  | .object, "delegate" => pure .delegateObject
  | .account, "observe" => pure .observeAccount
  | .account, "transfer" => pure .transfer
  | .account, "delegate" => pure .delegateAccount
  | .program, "observe" => pure .observeProgram
  | .program, "install" => pure .installProgram
  | .program, "delegate" => pure .delegateProgram
  | .program, "installPolicy" => pure .installPolicy
  | .program, "revokeCapability" => pure .revokeCapability
  | _, _ => failAt path "verb is not defined for this resource kind"

private def capability (kind : ResourceKind) (path : String) (json : Lean.Json) :
    Result (Capability kind) := do
  -- A scope names its targets either explicitly (`targets`) or as a room
  -- (`room`); exactly one of the two keys is accepted.
  let targetKey := if ((← object path json).get? "room").isSome then "room" else "targets"
  let names := ["id", "root", "parent", "issuer", "holder", targetKey, "verbs", "maxCost",
    "notBefore", "notAfter", "issuerEpoch", "policyId", "policyEpoch", "ancestors", "channels"]
  let obj ← exactObject path names json
  let targets : TargetSet kind ← if targetKey = "room" then
      TargetSet.under <$> nat (path ++ ".room") (← field path "room" obj)
    else do
      let explicit ← list (path ++ ".targets")
        (fun p j => ResourceId.mk <$> nat p j) (← field path "targets" obj)
      pure (TargetSet.explicit explicit.toFinset)
  let verbs ← list (path ++ ".verbs") (verb kind) (← field path "verbs" obj)
  let ancestors ← list (path ++ ".ancestors")
    (fun p j => CapabilityId.mk <$> nat p j) (← field path "ancestors" obj)
  let channels ← list (path ++ ".channels")
    (fun p j => ChannelId.mk <$> nat p j) (← field path "channels" obj)
  pure {
    id := ⟨← nat (path ++ ".id") (← field path "id" obj)⟩
    root := ⟨← nat (path ++ ".root") (← field path "root" obj)⟩
    parent := (← optional (path ++ ".parent") nat (← field path "parent" obj)).map CapabilityId.mk
    issuer := ⟨← nat (path ++ ".issuer") (← field path "issuer" obj)⟩
    holder := ← holder (path ++ ".holder") (← field path "holder" obj)
    scope := ⟨targets, verbs.toFinset,
      ← nat (path ++ ".maxCost") (← field path "maxCost" obj)⟩
    notBefore := ← nat (path ++ ".notBefore") (← field path "notBefore" obj)
    notAfter := ← nat (path ++ ".notAfter") (← field path "notAfter" obj)
    issuerEpoch := ← nat (path ++ ".issuerEpoch") (← field path "issuerEpoch" obj)
    policyId := ⟨← nat (path ++ ".policyId") (← field path "policyId" obj)⟩
    policyEpoch := ← nat (path ++ ".policyEpoch") (← field path "policyEpoch" obj)
    ancestors := ancestors.toFinset
    channels := channels.toFinset }

private def policyInstall (path : String) (json : Lean.Json) :
    Result PolicyInstallController.Declaration := do
  let obj ← exactObject path ["expectedPreRoot", "expected", "nonce", "source"] json
  let expected ← optional (path ++ ".expected") (fun p value => do
    let head ← exactObject p ["version", "address"] value
    pure (Minidregg.Theory.PolicyInstall.Head.mk
      (← nat (p ++ ".version") (← field p "version" head))
      ⟨← nat (p ++ ".address") (← field p "address" head)⟩)) (← field path "expected" obj)
  pure ⟨⟨← nat (path ++ ".expectedPreRoot") (← field path "expectedPreRoot" obj)⟩,
    expected, ← nat (path ++ ".nonce") (← field path "nonce" obj),
    ← policyRecord (path ++ ".source") (← field path "source" obj)⟩

private def policyInstallDraft (path : String) (json : Lean.Json) : Result Draft := do
  let obj ← exactObject path ["subject", "control", "declaration"] json
  let declaration ← policyInstall (path ++ ".declaration") (← field path "declaration" obj)
  pure (.install ⟨← nat (path ++ ".subject") (← field path "subject" obj)⟩
    ⟨← nat (path ++ ".control") (← field path "control" obj)⟩
    (PolicyInstallController.declarationCodec.encode declaration))

private def delegationFor (kind : ResourceKind) (path : String)
    (domain semantics : Digest) (obj : Std.TreeMap.Raw String Lean.Json compare) :
    Result (List UInt8) := do
  let child ← capability kind (path ++ ".child") (← field path "child" obj)
  let parentId := CapabilityId.mk (← nat (path ++ ".parentId") (← field path "parentId" obj))
  let target := ResourceId.mk (← nat (path ++ ".target") (← field path "target" obj))
  let expectedPreRoot := Digest.mk
    (← nat (path ++ ".expectedPreRoot") (← field path "expectedPreRoot" obj))
  let command : CapabilityDelegationController.Command kind := {
    subject := ⟨← nat (path ++ ".subject") (← field path "subject" obj)⟩
    nonce := ← nat (path ++ ".nonce") (← field path "nonce" obj)
    expectedTargetRoot := ⟨← nat (path ++ ".expectedTargetRoot")
      (← field path "expectedTargetRoot" obj)⟩
    declaration := ⟨child, parentId, target, expectedPreRoot, 0⟩ }
  let marker := CapabilityDelegationController.operationMarker domain semantics command
  let finalized := { command with declaration := { command.declaration with operationNullifier := marker } }
  pure (CapabilityDelegationController.commandCodec.encode ⟨kind, finalized⟩)

private def delegation (path : String) (json : Lean.Json) : Result (List UInt8) := do
  let names := ["kind", "domain", "semantics", "subject", "nonce", "expectedTargetRoot",
    "child", "parentId", "target", "expectedPreRoot"]
  let obj ← exactObject path names json
  let kind ← resourceKind (path ++ ".kind") (← field path "kind" obj)
  let domain := Digest.mk (← nat (path ++ ".domain") (← field path "domain" obj))
  let semantics := Digest.mk (← nat (path ++ ".semantics") (← field path "semantics" obj))
  delegationFor kind path domain semantics obj

private def revocationFor (kind : ResourceKind) (path : String)
    (obj : Std.TreeMap.Raw String Lean.Json compare) :
    Result (List UInt8) := do
  let command : CapabilityRevocationController.Command kind := {
    subject := ⟨← nat (path ++ ".subject") (← field path "subject" obj)⟩
    nonce := ← nat (path ++ ".nonce") (← field path "nonce" obj)
    target := ⟨← nat (path ++ ".target") (← field path "target" obj)⟩
    victimKind := ← resourceKind (path ++ ".victimKind") (← field path "victimKind" obj)
    capability := ⟨← nat (path ++ ".capability") (← field path "capability" obj)⟩
    controlCapability := ⟨← nat (path ++ ".controlCapability")
      (← field path "controlCapability" obj)⟩
    expectedTargetRoot := ⟨← nat (path ++ ".expectedTargetRoot")
      (← field path "expectedTargetRoot" obj)⟩
    expectedAuthorityRoot := ⟨← nat (path ++ ".expectedAuthorityRoot")
      (← field path "expectedAuthorityRoot" obj)⟩ }
  pure (CapabilityRevocationController.commandCodec.encode ⟨kind, command⟩)

private def revocation (path : String) (json : Lean.Json) : Result (List UInt8) := do
  let names := ["kind", "subject", "nonce", "target", "victimKind", "capability",
    "controlCapability", "expectedTargetRoot", "expectedAuthorityRoot"]
  let obj ← exactObject path names json
  let kind ← resourceKind (path ++ ".kind") (← field path "kind" obj)
  revocationFor kind path obj

private def action (path : String) (json : Lean.Json) : Result Action := do
  let (tag, _) ← tagged path json
  match tag with
  | "create" | "write" =>
      let names := if tag = "create" then ["type", "key", "value"]
        else ["type", "key", "expected", "value"]
      let obj ← exactObject path names json
      let keyObj ← exactObject (path ++ ".key") ["type", "resource", "field"]
        (← field path "key" obj)
      let keyType ← string (path ++ ".key.type") (← field (path ++ ".key") "type" keyObj)
      let resource ← nat (path ++ ".key.resource") (← field (path ++ ".key") "resource" keyObj)
      let fieldId ← nat (path ++ ".key.field") (← field (path ++ ".key") "field" keyObj)
      let key := match keyType with
        | "object" => Minidregg.Theory.EffectDeclaration.StateKey.objectField ⟨resource⟩ ⟨fieldId⟩
        | "program" => Minidregg.Theory.EffectDeclaration.StateKey.programCode ⟨resource⟩
        | _ => Minidregg.Theory.EffectDeclaration.StateKey.objectField ⟨resource⟩ ⟨fieldId⟩
      unless keyType = "object" ∨ keyType = "program" do
        throw s!"{path}.key.type: expected object or program"
      let value ← int (path ++ ".value") (← field path "value" obj)
      if tag = "create" then pure (.create key value)
      else pure (.write key (← optional (path ++ ".expected") int
        (← field path "expected" obj)) value)
  | "move" =>
      let obj ← exactObject path ["type", "source", "destination", "resource",
        "sourceExpected", "destinationExpected", "amount"] json
      pure (.move ⟨← nat (path ++ ".source") (← field path "source" obj)⟩
        ⟨← nat (path ++ ".destination") (← field path "destination" obj)⟩
        ⟨← nat (path ++ ".resource") (← field path "resource" obj)⟩
        (← optional (path ++ ".sourceExpected") int (← field path "sourceExpected" obj))
        (← optional (path ++ ".destinationExpected") int (← field path "destinationExpected" obj))
        (← int (path ++ ".amount") (← field path "amount" obj)))
  | _ => failAt (path ++ ".type") "unknown action constructor"

private def identifier {version : Hyperdocument.CodecVersion} {domain : Hyperdocument.IdDomain}
    (path : String) (json : Lean.Json) : Result (Hyperdocument.Identifier version domain) := do
  pure ⟨⟨← nat path json⟩⟩

private def principal (path : String) (json : Lean.Json) : Result Hyperdocument.PrincipalRef := do
  let obj ← exactObject path ["subject", "capabilityKind", "capability"] json
  pure ⟨⟨← nat (path ++ ".subject") (← field path "subject" obj)⟩,
    ← resourceKind (path ++ ".capabilityKind") (← field path "capabilityKind" obj),
    ⟨← nat (path ++ ".capability") (← field path "capability" obj)⟩⟩

private def atomKind (path : String) (json : Lean.Json) : Result Hyperdocument.AtomKind := do
  let (tag, _) ← tagged path json
  match tag with
  | "text" => exactObject path ["type"] json *> pure .text
  | "inlineObject" =>
      let obj ← exactObject path ["type", "schema"] json
      pure (.inlineObject ⟨← nat (path ++ ".schema") (← field path "schema" obj)⟩)
  | _ => failAt (path ++ ".type") "expected text or inlineObject"

private def transclusionMode (path : String) (json : Lean.Json) :
    Result Hyperdocument.TransclusionMode := do
  match ← string path json with
  | "snapshot" => pure .snapshot | "live" => pure .live
  | _ => failAt path "expected snapshot or live"

private def elementBody (path : String) (json : Lean.Json) : Result Hyperdocument.ElementBody := do
  let (tag, _) ← tagged path json
  match tag with
  | "container" | "runs" =>
      let name := if tag = "container" then "children" else "runs"
      let obj ← exactObject path ["type", name] json
      if tag = "container" then
        pure (.container (← list (path ++ ".children") identifier (← field path "children" obj)))
      else
        pure (.runs (← list (path ++ ".runs") identifier (← field path "runs" obj)))
  | "embed" =>
      let obj ← exactObject path ["type", "transclusion"] json
      pure (.embed (← identifier (path ++ ".transclusion") (← field path "transclusion" obj)))
  | "opaque" =>
      let obj ← exactObject path ["type", "schema", "payload"] json
      pure (.opaque ⟨← nat (path ++ ".schema") (← field path "schema" obj)⟩
        (← decodeHex (path ++ ".payload") (← field path "payload" obj)))
  | _ => failAt (path ++ ".type") "unknown element body"

private def atomRecord (path : String) (json : Lean.Json) : Result Hyperdocument.AtomRecord := do
  let obj ← exactObject path ["document", "kind", "payload", "createdBy", "createdAt", "revision",
    "tombstonedAt"] json
  pure ⟨← identifier (path ++ ".document") (← field path "document" obj),
    ← atomKind (path ++ ".kind") (← field path "kind" obj),
    ← decodeHex (path ++ ".payload") (← field path "payload" obj),
    ← principal (path ++ ".createdBy") (← field path "createdBy" obj),
    ← identifier (path ++ ".createdAt") (← field path "createdAt" obj),
    ← identifier (path ++ ".revision") (← field path "revision" obj),
    ← optional (path ++ ".tombstonedAt") identifier (← field path "tombstonedAt" obj)⟩

private def anchorBias (path : String) (json : Lean.Json) : Result Hyperdocument.AnchorBias := do
  match ← string path json with
  | "before" => pure .before | "after" => pure .after
  | _ => failAt path "expected before or after"

private def deathPolicy (path : String) (json : Lean.Json) : Result Hyperdocument.EndpointDeathPolicy := do
  match ← string path json with
  | "invalidate" => pure .invalidate
  | "keepTombstone" => pure .keepTombstone
  | "preferPrevious" => pure .preferPrevious
  | "preferNext" => pure .preferNext
  | "preferPreviousThenNext" => pure .preferPreviousThenNext
  | "preferNextThenPrevious" => pure .preferNextThenPrevious
  | _ => failAt path "unknown endpoint death policy"

private def stablePoint (path : String) (json : Lean.Json) : Result Hyperdocument.StablePoint := do
  let obj ← exactObject path ["run", "neighbor", "bias", "death"] json
  pure ⟨← identifier (path ++ ".run") (← field path "run" obj),
    ← optional (path ++ ".neighbor") identifier (← field path "neighbor" obj),
    ← anchorBias (path ++ ".bias") (← field path "bias" obj),
    ← deathPolicy (path ++ ".death") (← field path "death" obj)⟩

private def stableRange (path : String) (json : Lean.Json) : Result Hyperdocument.StableRange := do
  let obj ← exactObject path ["start", "finish"] json
  pure ⟨← stablePoint (path ++ ".start") (← field path "start" obj),
    ← stablePoint (path ++ ".finish") (← field path "finish" obj)⟩

private def pin (path : String) (json : Lean.Json) :
    Result (Hyperdocument.AtomId × Hyperdocument.OperationId) := do
  let obj ← exactObject path ["atom", "revision"] json
  pure (← identifier (path ++ ".atom") (← field path "atom" obj),
    ← identifier (path ++ ".revision") (← field path "revision" obj))

private def transcludeRequest (path : String) (json : Lean.Json) :
    Result ContentResource.TranscludeRequest := do
  let obj ← exactObject path ["source", "range", "mode", "pins"] json
  pure ⟨← nat (path ++ ".source") (← field path "source" obj),
    ← stableRange (path ++ ".range") (← field path "range" obj),
    ← transclusionMode (path ++ ".mode") (← field path "mode" obj),
    ← list (path ++ ".pins") pin (← field path "pins" obj)⟩

private def linkTarget (path : String) (json : Lean.Json) : Result Hyperdocument.LinkTarget := do
  let (tag, _) ← tagged path json
  match tag with
  | "document" =>
      let obj ← exactObject path ["type", "id"] json
      pure (.document (← identifier (path ++ ".id") (← field path "id" obj)))
  | "element" =>
      let obj ← exactObject path ["type", "id"] json
      pure (.element (← identifier (path ++ ".id") (← field path "id" obj)))
  | "range" =>
      let obj ← exactObject path ["type", "document", "range"] json
      pure (.range (← identifier (path ++ ".document") (← field path "document" obj))
        (← stableRange (path ++ ".range") (← field path "range" obj)))
  | "external" =>
      let obj ← exactObject path ["type", "scheme", "authority", "path"] json
      pure (.external (← decodeHex (path ++ ".scheme") (← field path "scheme" obj))
        (← decodeHex (path ++ ".authority") (← field path "authority" obj))
        (← decodeHex (path ++ ".path") (← field path "path" obj)))
  | _ => failAt (path ++ ".type") "unknown link target"

private def contentAction (path : String) (json : Lean.Json) : Result ContentResource.Action := do
  let (tag, _) ← tagged path json
  match tag with
  | "createDocument" =>
      let obj ← exactObject path ["type", "rootElement", "schema", "body"] json
      pure (.createDocument (← identifier (path ++ ".rootElement") (← field path "rootElement" obj))
        ⟨← nat (path ++ ".schema") (← field path "schema" obj)⟩
        (← elementBody (path ++ ".body") (← field path "body" obj)))
  | "createAtom" =>
      let obj ← exactObject path ["type", "atom", "kind", "payload"] json
      pure (.createAtom (← identifier (path ++ ".atom") (← field path "atom" obj))
        (← atomKind (path ++ ".kind") (← field path "kind" obj))
        (← decodeHex (path ++ ".payload") (← field path "payload" obj)))
  | "createRun" =>
      let obj ← exactObject path ["type", "run", "atoms"] json
      pure (.createRun (← identifier (path ++ ".run") (← field path "run" obj))
        (← list (path ++ ".atoms") identifier (← field path "atoms" obj)))
  | "editAtom" =>
      let obj ← exactObject path ["type", "atom", "before", "kind", "payload", "tombstone"] json
      pure (.editAtom ⟨← identifier (path ++ ".atom") (← field path "atom" obj),
        ← atomRecord (path ++ ".before") (← field path "before" obj),
        ← atomKind (path ++ ".kind") (← field path "kind" obj),
        ← decodeHex (path ++ ".payload") (← field path "payload" obj),
        ← bool (path ++ ".tombstone") (← field path "tombstone" obj)⟩)
  | "link" =>
      let obj ← exactObject path ["type", "link", "source", "target", "relation"] json
      pure (.link (← identifier (path ++ ".link") (← field path "link" obj))
        (← optional (path ++ ".source") stableRange (← field path "source" obj))
        (← linkTarget (path ++ ".target") (← field path "target" obj))
        ⟨← nat (path ++ ".relation") (← field path "relation" obj)⟩)
  | "annotate" =>
      let obj ← exactObject path ["type", "annotation", "atom", "revision", "body"] json
      pure (.annotate (← identifier (path ++ ".annotation") (← field path "annotation" obj))
        (← identifier (path ++ ".atom") (← field path "atom" obj))
        (← identifier (path ++ ".revision") (← field path "revision" obj))
        (← decodeHex (path ++ ".body") (← field path "body" obj)))
  | "transclude" =>
      let obj ← exactObject path ["type", "transclusion", "link", "request"] json
      pure (.transclude (← identifier (path ++ ".transclusion") (← field path "transclusion" obj))
        (← identifier (path ++ ".link") (← field path "link" obj))
        (← transcludeRequest (path ++ ".request") (← field path "request" obj)))
  | _ => failAt (path ++ ".type") "unknown content action"

private def contentCommand (path : String) (json : Lean.Json) : Result ContentResource.Command := do
  let obj ← exactObject path ["actions"] json
  pure ⟨← list (path ++ ".actions") contentAction (← field path "actions" obj)⟩

private def targetPayload (path : String) (json : Lean.Json) :
    Result DeclaredResourceController.Payload := do
  let (tag, _) ← tagged path json
  match tag with
  | "scalar" =>
      let obj ← exactObject path ["type", "actions"] json
      pure (.scalar (← list (path ++ ".actions") action (← field path "actions" obj)))
  | "content" =>
      let obj ← exactObject path ["type", "actions"] json
      let actionsJson ← field path "actions" obj
      let command ← contentCommand path (.mkObj [("actions", actionsJson)])
      pure (.content command)
  | "read" =>
      let _ ← exactObject path ["type"] json
      pure .read
  | _ => failAt (path ++ ".type") "expected scalar, content or read"

private def commandTarget (path : String) (json : Lean.Json) :
    Result DeclaredResourceController.Target := do
  let obj ← exactObject path
    ["kind", "target", "capability", "observeCapability", "schemaVersion",
      "expectedTargetRoot", "payload"] json
  pure {
    kind := ← resourceKind (path ++ ".kind") (← field path "kind" obj)
    target := ← nat (path ++ ".target") (← field path "target" obj)
    capability := ⟨← nat (path ++ ".capability") (← field path "capability" obj)⟩
    observeCapability := (← optional (path ++ ".observeCapability") nat
      (← field path "observeCapability" obj)).map CapabilityId.mk
    schemaVersion := ← nat (path ++ ".schemaVersion") (← field path "schemaVersion" obj)
    expectedTargetRoot := ⟨← nat (path ++ ".expectedTargetRoot") (← field path "expectedTargetRoot" obj)⟩
    payload := ← targetPayload (path ++ ".payload") (← field path "payload" obj) }

private def command (path : String) (json : Lean.Json) : Result DeclaredResourceController.Command := do
  let obj ← exactObject path ["subject", "nonce", "targets"] json
  pure {
    subject := ⟨← nat (path ++ ".subject") (← field path "subject" obj)⟩
    nonce := ← nat (path ++ ".nonce") (← field path "nonce" obj)
    targets := ← list (path ++ ".targets") commandTarget (← field path "targets" obj) }

private def canonicalSource {α : Type} (path : String) (codec : IndexedProgram.LawfulCodec α)
    (json : Lean.Json) : Result (List UInt8) := do
  let bytes ← decodeHex path json
  match codec.decode bytes with
  | some value => pure (codec.encode value)
  | none => failAt path "noncanonical source bytes"

private def draft (path : String) (json : Lean.Json) : Result Draft := do
  let (tag, _) ← tagged path json
  match tag with
  | "invoke" =>
      let obj ← exactObject path ["type", "command"] json
      let source ← command (path ++ ".command") (← field path "command" obj)
      pure (.invoke (DeclaredResourceController.commandCodec.encode source))
  | "birth" =>
      let obj ← exactObject path ["type", "descriptor", "sourceCapabilities"] json
      let descriptor ← canonicalSource (path ++ ".descriptor")
        (ResourceBirthCodec.descriptorCodec CanonicalCellRegistry.registry) (← field path "descriptor" obj)
      let capabilities ← list (path ++ ".sourceCapabilities")
        (fun p j => CapabilityId.mk <$> nat p j) (← field path "sourceCapabilities" obj)
      pure (.birth descriptor capabilities)
  | "grain-birth" =>
      let obj ← exactObject path ["type", "source", "sourceCapabilities"] json
      let source ← canonicalSource (path ++ ".source")
        GrainResourceBirthHostCodec.sourceCodec (← field path "source" obj)
      let capabilities ← list (path ++ ".sourceCapabilities")
        (fun p j => CapabilityId.mk <$> nat p j) (← field path "sourceCapabilities" obj)
      pure (.birth source capabilities)
  | "install" =>
      let obj ← exactObject path ["type", "subject", "control", "declaration"] json
      let declaration ← canonicalSource (path ++ ".declaration")
        PolicyInstallController.declarationCodec (← field path "declaration" obj)
      pure (.install ⟨← nat (path ++ ".subject") (← field path "subject" obj)⟩
        ⟨← nat (path ++ ".control") (← field path "control" obj)⟩ declaration)
  | "install-source" =>
      let obj ← exactObject path ["type", "subject", "control", "declaration"] json
      let declaration ← policyInstall (path ++ ".declaration") (← field path "declaration" obj)
      pure (.install ⟨← nat (path ++ ".subject") (← field path "subject" obj)⟩
        ⟨← nat (path ++ ".control") (← field path "control" obj)⟩
        (PolicyInstallController.declarationCodec.encode declaration))
  | "delegate" =>
      let obj ← exactObject path ["type", "command"] json
      let bytes ← decodeHex (path ++ ".command") (← field path "command" obj)
      match CapabilityDelegationController.commandCodec.decode bytes with
      | some value => pure (.delegate (CapabilityDelegationController.commandCodec.encode value))
      | none => failAt (path ++ ".command") "noncanonical delegation command"
  | "delegate-source" =>
      let obj ← exactObject path ["type", "command"] json
      pure (.delegate (← delegation (path ++ ".command") (← field path "command" obj)))
  | "revoke" =>
      let obj ← exactObject path ["type", "command"] json
      let bytes ← decodeHex (path ++ ".command") (← field path "command" obj)
      match CapabilityRevocationController.commandCodec.decode bytes with
      | some value => pure (.revoke (CapabilityRevocationController.commandCodec.encode value))
      | none => failAt (path ++ ".command") "noncanonical revocation command"
  | "revoke-source" =>
      let obj ← exactObject path ["type", "command"] json
      pure (.revoke (← revocation (path ++ ".command") (← field path "command" obj)))
  | _ => failAt (path ++ ".type") "unknown draft constructor"

private def grant (path : String) (json : Lean.Json) : Result GrantRef := do
  let obj ← exactObject path ["kind", "target", "capability"] json
  pure ⟨← resourceKind (path ++ ".kind") (← field path "kind" obj),
    ← nat (path ++ ".target") (← field path "target" obj),
    ⟨← nat (path ++ ".capability") (← field path "capability" obj)⟩⟩

private def intent (path : String) (json : Lean.Json) : Result Intent := do
  let obj ← exactObject path ["subject", "nonce", "purpose", "grants"] json
  let purposeJson ← field path "purpose" obj
  let (tag, _) ← tagged (path ++ ".purpose") purposeJson
  let purpose ← match tag with
    | "prepare" => do
        let p ← exactObject (path ++ ".purpose") ["type", "draft"] purposeJson
        pure (.prepare (← draft (path ++ ".purpose.draft") (← field (path ++ ".purpose") "draft" p)))
    | "query" => do
        let at_ := path ++ ".purpose"
        -- `since` and `at` carry a height; the other views carry none.
        let hasHeight := (purposeJson.getObjVal? "height").toOption.isSome
        let p ← exactObject at_ (if hasHeight then ["type", "kind", "target", "view", "height"]
          else ["type", "kind", "target", "view"]) purposeJson
        let view ← match ← string (at_ ++ ".view") (← field at_ "view" p), hasHeight with
          | "resource", false => pure QueryView.resource
          | "policy", false => pure .policy
          | "capability", false => pure .capability
          | "who", false => pure .who
          | "since", true => do pure (.since (← nat (at_ ++ ".height") (← field at_ "height" p)))
          | "at", true => do pure (.atHeight (← nat (at_ ++ ".height") (← field at_ "height" p)))
          | _, _ => failAt (at_ ++ ".view") "unknown query view, or a height on a view that takes none"
        pure (.query ⟨← resourceKind (path ++ ".purpose.kind") (← field (path ++ ".purpose") "kind" p),
          ← nat (path ++ ".purpose.target") (← field (path ++ ".purpose") "target" p), view⟩)
    | _ => failAt (path ++ ".purpose.type") "expected prepare or query"
  pure ⟨⟨← nat (path ++ ".subject") (← field path "subject" obj)⟩,
    ← nat (path ++ ".nonce") (← field path "nonce" obj), purpose,
    ← list (path ++ ".grants") grant (← field path "grants" obj)⟩

private def keyRecord (path : String) (json : Lean.Json) : Result KeyRecord := do
  let obj ← exactObject path ["keyId", "keyEpoch", "algorithm", "subject", "publicKey",
    "activeFrom", "activeUntil"] json
  pure ⟨← nat (path ++ ".keyId") (← field path "keyId" obj),
    ← nat (path ++ ".keyEpoch") (← field path "keyEpoch" obj),
    ← nat (path ++ ".algorithm") (← field path "algorithm" obj),
    ← nat (path ++ ".subject") (← field path "subject" obj),
    ← decodeHex (path ++ ".publicKey") (← field path "publicKey" obj),
    ← nat (path ++ ".activeFrom") (← field path "activeFrom" obj),
    ← nat (path ++ ".activeUntil") (← field path "activeUntil" obj)⟩

private def enrollment (path : String) (json : Lean.Json) : Result NativeHostGenesis.Enrollment := do
  let obj ← exactObject path ["key", "accountId", "spendCapabilityId", "controlCapabilityId",
    "factoryObserveCapabilityId", "initialBalance", "accountPredicate"] json
  pure ⟨← keyRecord (path ++ ".key") (← field path "key" obj),
    ← nat (path ++ ".accountId") (← field path "accountId" obj),
    ⟨← nat (path ++ ".spendCapabilityId") (← field path "spendCapabilityId" obj)⟩,
    ⟨← nat (path ++ ".controlCapabilityId") (← field path "controlCapabilityId" obj)⟩,
    ⟨← nat (path ++ ".factoryObserveCapabilityId") (← field path "factoryObserveCapabilityId" obj)⟩,
    ← nat (path ++ ".initialBalance") (← field path "initialBalance" obj),
    ← predicate (path ++ ".accountPredicate") (← field path "accountPredicate" obj)⟩

private def charge (path : String) (json : Lean.Json) : Result ResourceCost.Charge := do
  let names := ["incidences", "turnBytes", "memoryTouches", "witnessBytes", "proofWork",
    "storageBytes", "networkBytes", "sideEffectCount", "feeDebit", "leaseByteBlocks"]
  let obj ← exactObject path names json
  let values ← names.mapM fun name => do
    nat (path ++ "." ++ name) (← field path name obj)
  pure fun lane => (values[(match lane with
    | .incidences => 0 | .turnBytes => 1 | .memoryTouches => 2 | .witnessBytes => 3
    | .proofWork => 4 | .storageBytes => 5 | .networkBytes => 6 | .sideEffectCount => 7
    | .feeDebit => 8 | .leaseByteBlocks => 9)]?).getD 0

private def genesis (path : String) (json : Lean.Json) : Result NativeHostGenesis.Config := do
  let names := ["domain", "factoryId", "resourceBookId", "authorityCellId", "federation",
    "tariffBase", "tariffPerBirth", "tariffPerGrant", "tariffPerInitialPayloadByte",
    "collector", "asset", "expectedSemantics", "issuerEpoch", "genesisHeight",
    "factoryPredicate", "enrollments", "factoryControllerSubject",
    "factoryControllerCapability", "meterAllowance"]
  let obj ← exactObject path names json
  pure {
    deployment := ⟨⟨← nat (path ++ ".domain") (← field path "domain" obj)⟩,
      ← nat (path ++ ".factoryId") (← field path "factoryId" obj),
      ← nat (path ++ ".resourceBookId") (← field path "resourceBookId" obj),
      ← nat (path ++ ".authorityCellId") (← field path "authorityCellId" obj)⟩
    federation := ⟨← nat (path ++ ".federation") (← field path "federation" obj)⟩
    tariff := ⟨← nat (path ++ ".tariffBase") (← field path "tariffBase" obj),
      ← nat (path ++ ".tariffPerBirth") (← field path "tariffPerBirth" obj),
      ← nat (path ++ ".tariffPerGrant") (← field path "tariffPerGrant" obj),
      ← nat (path ++ ".tariffPerInitialPayloadByte") (← field path "tariffPerInitialPayloadByte" obj),
      ← nat (path ++ ".collector") (← field path "collector" obj),
      ← nat (path ++ ".asset") (← field path "asset" obj)⟩
    expectedSemantics := ⟨← nat (path ++ ".expectedSemantics") (← field path "expectedSemantics" obj)⟩
    issuerEpoch := ← nat (path ++ ".issuerEpoch") (← field path "issuerEpoch" obj)
    genesisHeight := ← nat (path ++ ".genesisHeight") (← field path "genesisHeight" obj)
    factoryPredicate := ← predicate (path ++ ".factoryPredicate") (← field path "factoryPredicate" obj)
    enrollments := ← list (path ++ ".enrollments") enrollment (← field path "enrollments" obj)
    factoryController := ⟨⟨← nat (path ++ ".factoryControllerSubject")
      (← field path "factoryControllerSubject" obj)⟩,
      ⟨← nat (path ++ ".factoryControllerCapability")
      (← field path "factoryControllerCapability" obj)⟩⟩
    meterAllowance := ← charge (path ++ ".meterAllowance") (← field path "meterAllowance" obj) }

private def funding (path : String) (json : Lean.Json) : Result ResourceBirth.InitialFunding := do
  let obj ← exactObject path ["source", "destination", "asset", "amount"] json
  pure ⟨← nat (path ++ ".source") (← field path "source" obj),
    ← nat (path ++ ".destination") (← field path "destination" obj),
    ← nat (path ++ ".asset") (← field path "asset" obj),
    ← nat (path ++ ".amount") (← field path "amount" obj)⟩

private def shareIssueOrigin (path : String) (json : Lean.Json) :
    Result ApplicationDispatchCodec.Origin := do
  let (tag, _) ← tagged path json
  match tag with
  | "human" =>
      let _ ← exactObject path ["type"] json
      pure .human
  | "agent" =>
      let obj ← exactObject path ["type", "task", "generation"] json
      pure <| .agent
        (← nat (path ++ ".task") (← field path "task" obj))
        (← int (path ++ ".generation") (← field path "generation" obj))
  | _ => failAt path "expected human or agent origin"

private def shareIssueRoleBasis (path : String) (json : Lean.Json) :
    Result ApplicationGrainSessionEnrollment.RoleBasis := do
  let (tag, _) ← tagged path json
  match tag with
  | "none" =>
      let _ ← exactObject path ["type"] json
      pure .none
  | "allAccess" =>
      let _ ← exactObject path ["type"] json
      pure .allAccess
  | "role" =>
      let obj ← exactObject path ["type", "id"] json
      pure <| .role (← nat (path ++ ".id") (← field path "id" obj))
  | _ => failAt path "expected none, allAccess, or role basis"

private def shareIssueRole (path : String) (json : Lean.Json) :
    Result ApplicationGrainSessionEnrollment.RoleAssignment := do
  let obj ← exactObject path
    ["basis", "added", "removed", "roleSchemaRoot", "roleVersion"] json
  let role : ApplicationGrainSessionEnrollment.RoleAssignment :=
    ⟨← shareIssueRoleBasis (path ++ ".basis") (← field path "basis" obj),
     ← list (path ++ ".added")
       (fun p j => (·.toUTF8.toList) <$> string p j) (← field path "added" obj),
     ← list (path ++ ".removed")
       (fun p j => (·.toUTF8.toList) <$> string p j) (← field path "removed" obj),
     ⟨← nat (path ++ ".roleSchemaRoot") (← field path "roleSchemaRoot" obj)⟩,
     ← nat (path ++ ".roleVersion") (← field path "roleVersion" obj)⟩
  unless role.valid do failAt path "invalid role assignment"
  pure role

private def shareIssueTicket (path : String) (json : Lean.Json) :
    Result ApplicationDispatchAuthority.Ticket := do
  let obj ← exactObject path
    ["resource", "scope", "participant", "ceiling", "issueNonce"] json
  let scopePath := path ++ ".scope"
  let scopeObj ← exactObject scopePath
    ["app", "packageVersion", "packageRoot", "interfaceId", "interfaceVersion",
     "interfaceRoot", "schemaRoot", "schemaVersion"]
    (← field path "scope" obj)
  let scope : ApplicationDispatchAuthority.Scope :=
    ⟨← nat (scopePath ++ ".app") (← field scopePath "app" scopeObj),
     ← int (scopePath ++ ".packageVersion") (← field scopePath "packageVersion" scopeObj),
     ⟨← nat (scopePath ++ ".packageRoot") (← field scopePath "packageRoot" scopeObj)⟩,
     ← nat (scopePath ++ ".interfaceId") (← field scopePath "interfaceId" scopeObj),
     ← nat (scopePath ++ ".interfaceVersion") (← field scopePath "interfaceVersion" scopeObj),
     ⟨← nat (scopePath ++ ".interfaceRoot") (← field scopePath "interfaceRoot" scopeObj)⟩,
     ⟨← nat (scopePath ++ ".schemaRoot") (← field scopePath "schemaRoot" scopeObj)⟩,
     ← nat (scopePath ++ ".schemaVersion") (← field scopePath "schemaVersion" scopeObj)⟩
  let participantPath := path ++ ".participant"
  let participantObj ← exactObject participantPath
    ["session", "descriptorResource", "kind", "subject", "origin",
     "sessionCapability", "appObserveCapability", "ticketObserveCapability"]
    (← field path "participant" obj)
  let kind ← string (participantPath ++ ".kind")
    (← field participantPath "kind" participantObj)
  let kind : ApplicationDispatchCodec.InterfaceKind ← match kind with
    | "web" => pure .web
    | "api" => pure .api
    | _ => failAt (participantPath ++ ".kind") "expected web or api"
  let participant : ApplicationDispatchAuthority.Participant :=
    ⟨← nat (participantPath ++ ".session") (← field participantPath "session" participantObj),
     ← nat (participantPath ++ ".descriptorResource")
       (← field participantPath "descriptorResource" participantObj),
     kind,
     ⟨← nat (participantPath ++ ".subject") (← field participantPath "subject" participantObj)⟩,
     ← shareIssueOrigin (participantPath ++ ".origin")
       (← field participantPath "origin" participantObj),
     ⟨← nat (participantPath ++ ".sessionCapability")
       (← field participantPath "sessionCapability" participantObj)⟩,
     ⟨← nat (participantPath ++ ".appObserveCapability")
       (← field participantPath "appObserveCapability" participantObj)⟩,
     ⟨← nat (participantPath ++ ".ticketObserveCapability")
       (← field participantPath "ticketObserveCapability" participantObj)⟩⟩
  pure ⟨← nat (path ++ ".resource") (← field path "resource" obj),
    scope, participant,
    ← shareIssueRole (path ++ ".ceiling") (← field path "ceiling" obj),
    ← nat (path ++ ".issueNonce") (← field path "issueNonce" obj)⟩

/-- Operator-only JSON authoring of a canonical share-issue signing request.
This does not authorize a plan or sign any header. -/
def shareIssueRequest (json : Lean.Json) : Result (List UInt8) := do
  let obj ← exactObject "$" ["spec", "payer", "funding", "sourceCapabilities"] json
  let specPath := "$.spec"
  let specObj ← exactObject specPath
    ["ticket", "issuer", "appDelegateCapability", "ticketOwnerCapability",
     "ticketControlCapability"] (← field "$" "spec" obj)
  let spec : ApplicationShareIssueSource.Spec :=
    ⟨← shareIssueTicket (specPath ++ ".ticket") (← field specPath "ticket" specObj),
     ⟨← nat (specPath ++ ".issuer") (← field specPath "issuer" specObj)⟩,
     ⟨← nat (specPath ++ ".appDelegateCapability")
       (← field specPath "appDelegateCapability" specObj)⟩,
     ⟨← nat (specPath ++ ".ticketOwnerCapability")
       (← field specPath "ticketOwnerCapability" specObj)⟩,
     ⟨← nat (specPath ++ ".ticketControlCapability")
       (← field specPath "ticketControlCapability" specObj)⟩⟩
  let request : ApplicationShareIssueAuthoring.Request :=
    ⟨spec,
     ← nat "$.payer" (← field "$" "payer" obj),
     ← list "$.funding" funding (← field "$" "funding" obj),
     ← list "$.sourceCapabilities"
       (fun p j => return ⟨← nat p j⟩) (← field "$" "sourceCapabilities" obj)⟩
  pure (ApplicationShareIssueAuthoring.requestCodec.encode request)

private def grainShareSelector (path : String) (json : Lean.Json) :
    Result ApplicationShareIssueGrainAuthoring.GrainSelector := do
  let obj ← exactObject path ["task", "capability", "observeCapability"] json
  return ⟨← nat (path ++ ".task") (← field path "task" obj),
    ⟨← nat (path ++ ".capability") (← field path "capability" obj)⟩,
    ⟨← nat (path ++ ".observeCapability")
      (← field path "observeCapability" obj)⟩⟩

/-- Reuse the existing full ticket/spec/payer/funding parser, then add the
two fixed grain selectors. No current task state or root comes from JSON. -/
private def grainShareIssueRequest (json : Lean.Json) : Result (List UInt8) := do
  let obj ← exactObject "$" ["spec", "payer", "funding", "sourceCapabilities",
    "tool", "parent"] json
  let baseJson := Lean.Json.mkObj
    [("spec", ← field "$" "spec" obj),
     ("payer", ← field "$" "payer" obj),
     ("funding", ← field "$" "funding" obj),
     ("sourceCapabilities", ← field "$" "sourceCapabilities" obj)]
  let baseBytes ← shareIssueRequest baseJson
  let some base := ApplicationShareIssueAuthoring.requestCodec.decode baseBytes
    | failAt "$" "noncanonical base share issue request"
  let request : ApplicationShareIssueGrainAuthoring.Request :=
    { spec := base.spec, payer := base.payer, funding := base.funding,
      sourceCapabilities := base.sourceCapabilities,
      tool := ← grainShareSelector "$.tool" (← field "$" "tool" obj),
      parent := ← grainShareSelector "$.parent" (← field "$" "parent" obj) }
  return ApplicationShareIssueGrainAuthoring.requestCodec.encode request

/-- Human-readable selectors for a lifetime grant. Every nested field is
translated by Mini into its strict source codec; the birth and app signing
headers still come only from the verified current image. -/
private def agentLifetimeGrantRequest (json : Lean.Json) : Result (List UInt8) := do
  let obj ← exactObject "$" ["grant", "grantOwnerCapability",
    "grantControlCapability", "payer", "funding", "sourceCapabilities"] json
  let grantObj ← exactObject "$.grant" ["source", "participant", "approval"]
    (← field "$" "grant" obj)
  let sourceObj ← exactObject "$.grant.source"
    ["resource", "issueIndex", "issueReceipt", "ticketResource", "ticketDigest"]
    (← field "$.grant" "source" grantObj)
  let receiptObj ← exactObject "$.grant.source.issueReceipt"
    ["transactionId", "eventId", "acceptedCount", "worldRoot"]
    (← field "$.grant.source" "issueReceipt" sourceObj)
  let receipt : NativeHostCodec.Receipt := {
    transactionId := ⟨← nat "$.grant.source.issueReceipt.transactionId"
      (← field "$.grant.source.issueReceipt" "transactionId" receiptObj)⟩
    eventId := ⟨← nat "$.grant.source.issueReceipt.eventId"
      (← field "$.grant.source.issueReceipt" "eventId" receiptObj)⟩
    acceptedCount := ← nat "$.grant.source.issueReceipt.acceptedCount"
      (← field "$.grant.source.issueReceipt" "acceptedCount" receiptObj)
    worldRoot := ⟨← nat "$.grant.source.issueReceipt.worldRoot"
      (← field "$.grant.source.issueReceipt" "worldRoot" receiptObj)⟩ }
  let participantObj ← exactObject "$.grant.participant"
    ["app", "session", "subject", "parentTask", "originalGeneration",
      "grantObserveCapability"] (← field "$.grant" "participant" grantObj)
  let approvalObj ← exactObject "$.grant.approval"
    ["issuer", "delegateCapability", "ceiling", "nonce"]
    (← field "$.grant" "approval" grantObj)
  let grant : ApplicationAgentLifetimeGrant.Grant := {
    source := {
      resource := ← nat "$.grant.source.resource" (← field "$.grant.source" "resource" sourceObj)
      issueIndex := ← nat "$.grant.source.issueIndex" (← field "$.grant.source" "issueIndex" sourceObj)
      issueReceipt := receipt
      ticketResource := ← nat "$.grant.source.ticketResource"
        (← field "$.grant.source" "ticketResource" sourceObj)
      ticketDigest := ⟨← nat "$.grant.source.ticketDigest"
        (← field "$.grant.source" "ticketDigest" sourceObj)⟩ }
    participant := {
      app := ← nat "$.grant.participant.app" (← field "$.grant.participant" "app" participantObj)
      session := ← nat "$.grant.participant.session"
        (← field "$.grant.participant" "session" participantObj)
      subject := ⟨← nat "$.grant.participant.subject"
        (← field "$.grant.participant" "subject" participantObj)⟩
      parentTask := ← nat "$.grant.participant.parentTask"
        (← field "$.grant.participant" "parentTask" participantObj)
      originalGeneration := ← int "$.grant.participant.originalGeneration"
        (← field "$.grant.participant" "originalGeneration" participantObj)
      grantObserveCapability := ⟨← nat "$.grant.participant.grantObserveCapability"
        (← field "$.grant.participant" "grantObserveCapability" participantObj)⟩ }
    approval := {
      issuer := ⟨← nat "$.grant.approval.issuer"
        (← field "$.grant.approval" "issuer" approvalObj)⟩
      delegateCapability := ⟨← nat "$.grant.approval.delegateCapability"
        (← field "$.grant.approval" "delegateCapability" approvalObj)⟩
      ceiling := ← shareIssueRole "$.grant.approval.ceiling"
        (← field "$.grant.approval" "ceiling" approvalObj)
      nonce := ← nat "$.grant.approval.nonce"
        (← field "$.grant.approval" "nonce" approvalObj) } }
  let spec : ApplicationAgentLifetimeGrantSource.Spec := {
    grant := grant
    grantOwnerCapability := ⟨← nat "$.grantOwnerCapability"
      (← field "$" "grantOwnerCapability" obj)⟩
    grantControlCapability := ⟨← nat "$.grantControlCapability"
      (← field "$" "grantControlCapability" obj)⟩ }
  unless decide spec.valid do
    failAt "$.grant" "invalid lifetime grant selectors"
  let request : ApplicationAgentLifetimeGrantAuthoring.Request := {
    spec := spec
    payer := ← nat "$.payer" (← field "$" "payer" obj)
    funding := ← list "$.funding" funding (← field "$" "funding" obj)
    sourceCapabilities := ← list "$.sourceCapabilities"
      (fun path value => return ⟨← nat path value⟩)
      (← field "$" "sourceCapabilities" obj) }
  return ApplicationAgentLifetimeGrantAuthoring.requestCodec.encode request

private structure BirthParts where
  item : ResourceBirth.BirthItem CanonicalCellRegistry.registry
  ownerGrant : ResourceBirth.AuthorityGrant
  controlGrant : ResourceBirth.AuthorityGrant
  policy : ResourceBirth.InitialPolicy

/-- The worker clause is tied to one execution generation. Grant caveats
cannot currently carry arbitrary Pred, so the native resource policy itself
must constrain a delegated worker. -/
private def grainWorkerClause (subject : Nat) (generation : Int) : Minidregg.Pred.Pred :=
  .all [.eq "request/subject" (Int.ofNat subject), AgentGrain.witnessCaveat generation]

private def grainPolicy (owner : Nat) (worker : Option (List Nat × Int)) : Minidregg.Pred.Pred :=
  let base := AgentGrain.policy (.eq "request/subject" (Int.ofNat owner))
  match worker with
  | none => base
  | some ([subject], generation) => .all [base, .any [
      .eq "request/subject" (Int.ofNat owner),
      .memberOf "request/verb" [1, 3],
      grainWorkerClause subject generation]]
  | some (subjects, generation) => .all [base, .any <|
      [.eq "request/subject" (Int.ofNat owner), .memberOf "request/verb" [1, 3]] ++
        subjects.map (fun subject => grainWorkerClause subject generation)]

/-- Every named worker in a plural policy gets the same pinned-generation,
no-op witness clause. This is a construction fact, not an IO admission claim. -/
theorem grainPolicy_plural_worker_clause (owner : Nat) (subjects : List Nat)
    (generation : Int) (subject : Nat) (named : subject ∈ subjects) :
    grainWorkerClause subject generation ∈
      ([.eq "request/subject" (Int.ofNat owner), .memberOf "request/verb" [1, 3]] ++
        subjects.map (fun worker => grainWorkerClause worker generation)) := by
  apply List.mem_append.mpr
  right
  exact List.mem_map.mpr ⟨subject, named, rfl⟩

#print axioms grainPolicy_plural_worker_clause

/-- Plural authoring with one subject retains the exact historical policy
bytes, so adding a provider cannot silently alter the existing tool rule. -/
theorem grainPolicy_singleton_bytes (owner subject : Nat) (generation : Int) :
    NativeHostGenesis.predicateStream.encode
      (grainPolicy owner (some ([subject], generation))) =
    NativeHostGenesis.predicateStream.encode
      (.all [AgentGrain.policy (.eq "request/subject" (Int.ofNat owner)), .any [
        .eq "request/subject" (Int.ofNat owner),
        .memberOf "request/verb" [1, 3],
        .all [.eq "request/subject" (Int.ofNat subject),
          AgentGrain.witnessCaveat generation]]]) := rfl

#print axioms grainPolicy_singleton_bytes

/-- A worker witness with a different old generation cannot satisfy even its
own clause. This uses the deployed predicate evaluator, not list membership. -/
theorem grainWorkerClause_wrong_generation (subject : Nat) (generation actual : Int)
    (old new : Minidregg.Pred.State)
    (before : new.get "resource/field/0/before" = some actual)
    (stale : actual ≠ generation) :
    Minidregg.Pred.eval (grainWorkerClause subject generation) old new = false := by
  have witnessFalse : Minidregg.Pred.eval (AgentGrain.witnessCaveat generation)
      old new = false := by
    simp [AgentGrain.witnessCaveat, Minidregg.Pred.eval_all,
      Minidregg.Pred.eval, Minidregg.Pred.evalWith, before, stale]
  simp [grainWorkerClause, Minidregg.Pred.eval_all, witnessFalse]

/-- The subject check refuses a caller absent from a worker clause. -/
theorem grainWorkerClause_wrong_subject (subject caller : Nat) (generation : Int)
    (old new : Minidregg.Pred.State)
    (requestSubject : new.get "request/subject" = some (Int.ofNat caller))
    (different : caller ≠ subject) :
    Minidregg.Pred.eval (grainWorkerClause subject generation) old new = false := by
  simp [grainWorkerClause, Minidregg.Pred.eval_all,
    Minidregg.Pred.eval, Minidregg.Pred.evalWith, requestSubject,
    Nat.cast_inj, different]

/-- For a mutation, no worker can reuse a previous pinned generation, even
if that worker can observe a newer state. Owner and management branches are
explicitly excluded by the request subject and verb. -/
theorem grainPolicy_stale_worker_refused (owner : Nat) (subjects : List Nat)
    (generation actual : Int) (caller : Nat)
    (old new : Minidregg.Pred.State)
    (verb : new.get "request/verb" = some 2)
    (requestSubject : new.get "request/subject" = some (Int.ofNat caller))
    (notOwner : caller ≠ owner)
    (before : new.get "resource/field/0/before" = some actual)
    (stale : actual ≠ generation) :
    Minidregg.Pred.eval (grainPolicy owner (some (subjects, generation))) old new = false := by
  have workerFalse : ∀ worker ∈ subjects,
      Minidregg.Pred.eval (grainWorkerClause worker generation) old new = false := by
    intro worker _
    exact grainWorkerClause_wrong_generation worker generation actual old new before stale
  have workerFalseWith : ∀ worker ∈ subjects,
      Minidregg.Pred.evalWith Minidregg.Pred.failClosed
        (grainWorkerClause worker generation) old new = false := workerFalse
  cases subjects with
  | nil =>
      simp [grainPolicy, Minidregg.Pred.eval_all, Minidregg.Pred.eval_any,
        Minidregg.Pred.eval, Minidregg.Pred.evalWith, requestSubject, verb,
        Nat.cast_inj, notOwner]
  | cons first rest =>
      cases rest with
      | nil =>
          have firstFalse := workerFalseWith first (by simp)
          simp [grainPolicy, Minidregg.Pred.eval_all, Minidregg.Pred.eval_any,
            Minidregg.Pred.eval, Minidregg.Pred.evalWith, requestSubject, verb,
            Nat.cast_inj, notOwner, firstFalse]
      | cons second tail =>
          simp [grainPolicy, Minidregg.Pred.eval_all, Minidregg.Pred.eval_any,
            Minidregg.Pred.eval, Minidregg.Pred.evalWith, requestSubject, verb,
            Nat.cast_inj, notOwner]
          intro _
          refine ⟨workerFalseWith first (by simp), workerFalseWith second (by simp), ?_⟩
          intro worker named
          exact workerFalseWith worker (by simp [named])

#print axioms grainPolicy_stale_worker_refused

/-- A non-owner subject absent from the bounded worker list cannot mutate
through the plural resource policy, even when it presents a valid generation. -/
theorem grainPolicy_unnamed_worker_refused (owner : Nat) (subjects : List Nat)
    (generation : Int) (caller : Nat)
    (old new : Minidregg.Pred.State)
    (verb : new.get "request/verb" = some 2)
    (requestSubject : new.get "request/subject" = some (Int.ofNat caller))
    (notOwner : caller ≠ owner)
    (unnamed : caller ∉ subjects) :
    Minidregg.Pred.eval (grainPolicy owner (some (subjects, generation))) old new = false := by
  have workerFalseWith : ∀ worker ∈ subjects,
      Minidregg.Pred.evalWith Minidregg.Pred.failClosed
        (grainWorkerClause worker generation) old new = false := by
    intro worker named
    have different : caller ≠ worker := by
      intro same
      exact unnamed (by simpa [same] using named)
    exact grainWorkerClause_wrong_subject worker caller generation old new
      requestSubject different
  cases subjects with
  | nil =>
      simp [grainPolicy, Minidregg.Pred.eval_all, Minidregg.Pred.eval_any,
        Minidregg.Pred.eval, Minidregg.Pred.evalWith, requestSubject, verb,
        Nat.cast_inj, notOwner]
  | cons first rest =>
      cases rest with
      | nil =>
          have firstFalse := workerFalseWith first (by simp)
          simp [grainPolicy, Minidregg.Pred.eval_all, Minidregg.Pred.eval_any,
            Minidregg.Pred.eval, Minidregg.Pred.evalWith, requestSubject, verb,
            Nat.cast_inj, notOwner, firstFalse]
      | cons second tail =>
          simp [grainPolicy, Minidregg.Pred.eval_all, Minidregg.Pred.eval_any,
            Minidregg.Pred.eval, Minidregg.Pred.evalWith, requestSubject, verb,
            Nat.cast_inj, notOwner]
          intro _
          refine ⟨workerFalseWith first (by simp), workerFalseWith second (by simp), ?_⟩
          intro worker named
          exact workerFalseWith worker (by simp [named])

#print axioms grainPolicy_unnamed_worker_refused

private def grainWorker (path : String)
    (obj : Std.TreeMap.Raw String Lean.Json compare) : Result (Option (List Nat × Int)) := do
  match obj.get? "workerSubject", obj.get? "workerSubjects", obj.get? "workerGeneration" with
  | none, none, none => pure none
  | some subject, none, some generation =>
      pure (some ([← nat (path ++ ".workerSubject") subject],
        ← int (path ++ ".workerGeneration") generation))
  | none, some subjects, some generation =>
      let values ← list (path ++ ".workerSubjects") nat subjects
      unless 1 ≤ values.length ∧ values.length ≤ 4 do
        failAt (path ++ ".workerSubjects") "expected 1 through 4 subjects"
      unless values.Nodup do
        failAt (path ++ ".workerSubjects") "subjects must be distinct"
      pure (some (values, ← int (path ++ ".workerGeneration") generation))
  | _, _, _ => failAt path "workerSubject or workerSubjects and workerGeneration must be supplied exclusively"

private def grainWorkerFields (obj : Std.TreeMap.Raw String Lean.Json compare) : List String :=
  if (obj.get? "workerSubject").isSome then ["workerSubject", "workerGeneration"]
  else if (obj.get? "workerSubjects").isSome then ["workerSubjects", "workerGeneration"]
  else []

private def birthRootCapability {kind : ResourceKind}
    (profile : CanonicalRuntimeProfile.Profile NativeHostProfile.Field)
    (source : NativeHostGenesis.Config) (height : Nat)
    (identifier : CapabilityId) (owner : SubjectId) (target : Nat)
    (verbs : Finset (Verb kind)) : Capability kind :=
  { NativeHostGenesis.rootCapability profile source kind identifier owner target verbs with
    notBefore := height, notAfter := height + profile.template.lifetime }

/-- Existing offline authoring retains the genesis epochs. Loaded birth
authoring substitutes the two epochs from the same verified authority image
used by the receiver; all other grant fields keep their source derivation. -/
private def birthRootCapabilityAt {kind : ResourceKind}
    (profile : CanonicalRuntimeProfile.Profile NativeHostProfile.Field)
    (source : NativeHostGenesis.Config) (height : Nat)
    (authority : Option AuthState) (identifier : CapabilityId)
    (owner : SubjectId) (target : Nat) (verbs : Finset (Verb kind)) : Capability kind :=
  let grant := birthRootCapability profile source height identifier owner target verbs
  match authority with
  | none => grant
  | some current =>
      { grant with issuerEpoch := current.issuerEpoch profile.template.issuer
                   policyEpoch := current.policyEpoch ⟨target⟩ }

private theorem birthRootCapability_time_window {kind : ResourceKind}
    (profile : CanonicalRuntimeProfile.Profile NativeHostProfile.Field)
    (source : NativeHostGenesis.Config) (height : Nat)
    (identifier : CapabilityId) (owner : SubjectId) (target : Nat)
    (verbs : Finset (Verb kind)) :
    (birthRootCapability profile source height identifier owner target verbs).notBefore = height ∧
    (birthRootCapability profile source height identifier owner target verbs).notAfter =
      height + profile.template.lifetime := by
  constructor <;> rfl

private def birthParts (path : String)
    (profile : CanonicalRuntimeProfile.Profile NativeHostProfile.Field)
    (source : NativeHostGenesis.Config) (height : Nat) (json : Lean.Json)
    (authority : Option AuthState := none) : Result BirthParts := do
  let raw ← object path json
  let storage ← string (path ++ ".storage") (← field path "storage" raw)
  let worker ← if storage = "grain" then grainWorker path raw else pure none
  let roomField := if (raw.get? "room").isSome then ["room"] else []
  let obj ← exactObject path
    ((if storage = "grain" then
      ["kind", "storage", "target", "owner", "ownerCapability", "controlCapability", "budget"] ++
        (if worker.isSome then grainWorkerFields raw else [])
    else
      ["kind", "storage", "target", "owner", "ownerCapability", "controlCapability", "predicate"]) ++
      roomField) json
  let room ← match obj.get? "room" with
    | none => pure none
    | some value => some <$> nat (path ++ ".room") value
  let kind ← resourceKind (path ++ ".kind") (← field path "kind" obj)
  unless storage = "declared" ∨ storage = "content" ∨ storage = "grain" do
    throw s!"{path}.storage: expected declared, content or grain"
  unless (storage = "declared" ∧ (kind = .object ∨ kind = .account)) ∨
      ((storage = "content" ∨ storage = "grain") ∧ kind = .object) do
    throw s!"{path}: declared storage is object/account; content and grain storage are object"
  let target ← nat (path ++ ".target") (← field path "target" obj)
  let owner := SubjectId.mk (← nat (path ++ ".owner") (← field path "owner" obj))
  let ownerId := CapabilityId.mk
    (← nat (path ++ ".ownerCapability") (← field path "ownerCapability" obj))
  let controlId := CapabilityId.mk
    (← nat (path ++ ".controlCapability") (← field path "controlCapability" obj))
  let rulePredicate ← if storage = "grain" then
      pure (grainPolicy owner.value worker)
    else predicate (path ++ ".predicate") (← field path "predicate" obj)
  let rule := NativeHostGenesis.policy profile source target rulePredicate
  let cell : PackedCell CanonicalCellRegistry.registry ←
    if storage = "content" then
      pure ⟨.content, CellState.materialize HyperdocumentCell.contentMaterializer ContentResource.initialStore⟩
    else if storage = "grain" then
      let budget ← nat (path ++ ".budget") (← field path "budget" obj)
      pure ⟨.declaredObject, CellState.materialize DeclaredEffectCell.materializer
        (AgentGrain.initialStore target budget)⟩
    else pure (NativeHostGenesis.declaredCell source target (kind = .account))
  let item : ResourceBirth.BirthItem CanonicalCellRegistry.registry :=
    ⟨⟨target, CellSlot.root CanonicalCellRegistry.registry .absent, cell⟩, kind, owner, room⟩
  -- A workspace resource's owner holds it as a room: `under target`, the
  -- resource and everything later born into it.
  let asRoom {kind : ResourceKind} (cap : Capability kind) : Capability kind :=
    { cap with scope := { cap.scope with targets := .under target } }
  let ownerGrant : ResourceBirth.AuthorityGrant := match kind with
    | .object => ⟨.object, ⟨asRoom (birthRootCapabilityAt profile source height authority
        ownerId owner target (ResourceBirthPolicyController.Concrete.ownerVerbs .object)), []⟩⟩
    | .account => ⟨.account, ⟨asRoom (birthRootCapabilityAt profile source height authority
        ownerId owner target (ResourceBirthPolicyController.Concrete.ownerVerbs .account)), []⟩⟩
    | .program => ⟨.program, ⟨asRoom (birthRootCapabilityAt profile source height authority
        ownerId owner target (ResourceBirthPolicyController.Concrete.ownerVerbs .program)), []⟩⟩
  let control : Capability .program := birthRootCapabilityAt profile source height authority
    controlId owner target {.installPolicy, .revokeCapability}
  pure ⟨item, ownerGrant, ⟨.program, ⟨control, []⟩⟩,
    ⟨rule.policyId, PolicyRecordCodec.digest rule, PolicyRecordCodec.encode rule⟩⟩

/-- A standard birth is built entirely through the deployed source helpers:
absent roots, declared cells, owner/control grants, policy addresses, identity,
nullifier and quoted fee are never supplied as JSON assertions. -/
private def birth (path : String) (json : Lean.Json)
    (grainBirthTariff : Option NativeHost.GrainBirthTariffPin := none)
    (deployed : Option NativeHost.Config := none)
    (currentHeight : Option Nat := none)
    (authority : Option AuthState := none) : Result Draft := do
  let raw ← object path json
  let obj ← exactObject path (["genesis", "template", "creator", "nonce", "resources",
    "sourceCapabilities", "funding", "feePayer"] ++
      (if (raw.get? "grainBirthTariff").isSome then ["grainBirthTariff"] else []) ++
      (if (raw.get? "height").isSome then ["height"] else [])) json
  let suppliedTariff ← match obj.get? "grainBirthTariff" with
    | none => pure none
    | some encoded => do
        let pin ← exactObject (path ++ ".grainBirthTariff") ["base", "perBirth"] encoded
        let value : NativeHost.GrainBirthTariffPin :=
          ⟨← nat (path ++ ".grainBirthTariff.base")
              (← field (path ++ ".grainBirthTariff") "base" pin),
            ← nat (path ++ ".grainBirthTariff.perBirth")
              (← field (path ++ ".grainBirthTariff") "perBirth" pin)⟩
        unless 0 < value.base do throw s!"{path}.grainBirthTariff.base: must be positive"
        pure (some value)
  if let some expected := grainBirthTariff then
    if let some supplied := suppliedTariff then
      unless supplied == expected do
        throw s!"{path}.grainBirthTariff: differs from enclosing grain birth tariff"
  let grainBirthTariff := if grainBirthTariff.isSome then grainBirthTariff
    else if suppliedTariff.isSome then suppliedTariff else deployed.bind (·.grainBirthTariff)
  let source ← genesis (path ++ ".genesis") (← field path "genesis" obj)
  let height ← match obj.get? "height" with
    | none => pure (currentHeight.getD source.genesisHeight)
    | some encoded => nat (path ++ ".height") encoded
  if let some expected := currentHeight then
    unless height == expected do
      throw s!"{path}.height: differs from the verified current image"
  let templateObj ← exactObject (path ++ ".template") ["issuer", "ownerBudget", "lifetime"]
    (← field path "template" obj)
  let template : CanonicalRuntimeProfile.FactoryTemplate :=
    ⟨⟨← nat (path ++ ".template.issuer") (← field (path ++ ".template") "issuer" templateObj)⟩,
      ← nat (path ++ ".template.ownerBudget")
        (← field (path ++ ".template") "ownerBudget" templateObj),
      ← nat (path ++ ".template.lifetime")
        (← field (path ++ ".template") "lifetime" templateObj)⟩
  let nativeConfig : NativeHost.Config := {
    deployment := source.deployment, federation := source.federation, template := template,
    tariff := source.tariff, genesisHeight := source.genesisHeight, expectedSeed := ⟨0⟩,
    storage := { binary := "", root := "", key := "" }, signature := ⟨""⟩,
    grainBirthTariff := grainBirthTariff }
  let profile ← BirthRuntimeProfile.select nativeConfig deployed
  unless source.expectedSemantics = profile.semantics do
    throw s!"{path}.genesis.expectedSemantics: does not match the source-derived native profile"
  let creator := SubjectId.mk (← nat (path ++ ".creator") (← field path "creator" obj))
  let nonce ← nat (path ++ ".nonce") (← field path "nonce" obj)
  let parts ← list (path ++ ".resources")
    (fun itemPath value => birthParts itemPath profile source height value authority)
    (← field path "resources" obj)
  let movements ← list (path ++ ".funding") funding (← field path "funding" obj)
  let payer ← nat (path ++ ".feePayer") (← field path "feePayer" obj)
  let identity := ResourceBirthController.Concrete.sourceIdentity profile.compilerProfile
    source.deployment creator nonce
  let descriptor : ResourceBirth.Descriptor CanonicalCellRegistry.registry := {
    factory := ⟨source.deployment.factoryId⟩, creator := creator,
    transactionId := identity, nonce := nonce, births := parts.map (·.item), auxiliaryCreates := [],
    grants := parts.flatMap fun part => [part.ownerGrant, part.controlGrant],
    initialPolicies := parts.map (·.policy), authorityNullifier := identity.value,
    funding := movements, fee := ⟨payer, source.tariff.collector, source.tariff.asset, 0⟩ }
  let priced := { descriptor with fee := { descriptor.fee with amount := descriptor.quotedFee source.tariff } }
  let capabilities ← list (path ++ ".sourceCapabilities")
    (fun p value => CapabilityId.mk <$> nat p value) (← field path "sourceCapabilities" obj)
  pure (.birth ((ResourceBirthCodec.descriptorCodec CanonicalCellRegistry.registry).encode priced) capabilities)

/-- Author an ordinary resource birth against a verifier-loaded image. The
caller supplies its checked current height and authority state; this parser
checks the supplied genesis against the pinned seed before using it for
immutable deployment coordinates. Current grant epochs come only from the
loaded authority, never from that genesis description. -/
def birthCurrent (path : String) (json : Lean.Json)
    (deployed : NativeHost.Config) (height : Nat) (authority : AuthState) :
    Result Draft := do
  let raw ← object path json
  let source ← genesis (path ++ ".genesis") (← field path "genesis" raw)
  let built ← (NativeHostGenesis.build deployed.profile source).mapError
    (fun reason => s!"{path}.genesis: refused: {repr reason}")
  unless NativeHost.seedIdentity built.seed == deployed.expectedSeed do
    throw s!"{path}.genesis: differs from the pinned seed"
  birth path json none (some deployed) (some height) (some authority)

structure ApplicationBirthContext where
  source : NativeHostGenesis.Config
  profile : CanonicalRuntimeProfile.Profile NativeHostProfile.Field
  height : Nat
  creator : SubjectId
  nonce : Nat
  funding : List ResourceBirth.InitialFunding
  feePayer : Nat
  sourceCapabilities : List CapabilityId

/-- Shared source context for the two typed application births. Every profile
coordinate and the fee source follow the existing native birth authoring path;
JSON may select IDs and the signer capabilities but cannot inject cells,
policies, grants, roots or a fee amount. -/
def applicationBirthContext (path specField : String) (json : Lean.Json)
    (expectedTariff : Option NativeHost.GrainBirthTariffPin := none)
    (loadedHeight : Option Nat := none)
    (deployed : Option NativeHost.Config := none) :
    Result (ApplicationBirthContext × Lean.Json) := do
  let raw ← object path json
  let obj ← exactObject path
    (["genesis", "template", "creator", "nonce", specField,
      "sourceCapabilities", "funding", "feePayer"] ++
      (if (raw.get? "grainBirthTariff").isSome then ["grainBirthTariff"] else []) ++
      if (raw.get? "height").isSome then ["height"] else []) json
  let suppliedTariff ← match obj.get? "grainBirthTariff" with
    | none => pure none
    | some encoded => do
        let pin ← exactObject (path ++ ".grainBirthTariff") ["base", "perBirth"] encoded
        let value : NativeHost.GrainBirthTariffPin :=
          ⟨← nat (path ++ ".grainBirthTariff.base")
              (← field (path ++ ".grainBirthTariff") "base" pin),
            ← nat (path ++ ".grainBirthTariff.perBirth")
              (← field (path ++ ".grainBirthTariff") "perBirth" pin)⟩
        unless 0 < value.base do throw s!"{path}.grainBirthTariff.base: must be positive"
        pure (some value)
  if let some expected := expectedTariff then
    if let some supplied := suppliedTariff then
      unless supplied == expected do
        throw s!"{path}.grainBirthTariff: differs from enclosing grain birth tariff"
  let grainBirthTariff := if expectedTariff.isSome then expectedTariff
    else if suppliedTariff.isSome then suppliedTariff else deployed.bind (·.grainBirthTariff)
  let source ← genesis (path ++ ".genesis") (← field path "genesis" obj)
  let height ← match obj.get? "height" with
    | none => pure (loadedHeight.getD source.genesisHeight)
    | some encoded => do
        let supplied ← nat (path ++ ".height") encoded
        if let some current := loadedHeight then
          unless supplied == current do
            throw s!"{path}.height: differs from verifier-loaded current height"
        pure supplied
  let templateObj ← exactObject (path ++ ".template") ["issuer", "ownerBudget", "lifetime"]
    (← field path "template" obj)
  let template : CanonicalRuntimeProfile.FactoryTemplate :=
    ⟨⟨← nat (path ++ ".template.issuer") (← field (path ++ ".template") "issuer" templateObj)⟩,
      ← nat (path ++ ".template.ownerBudget")
        (← field (path ++ ".template") "ownerBudget" templateObj),
      ← nat (path ++ ".template.lifetime")
        (← field (path ++ ".template") "lifetime" templateObj)⟩
  let nativeConfig : NativeHost.Config := {
    deployment := source.deployment, federation := source.federation, template := template,
    tariff := source.tariff, genesisHeight := source.genesisHeight, expectedSeed := ⟨0⟩,
    storage := { binary := "", root := "", key := "" }, signature := ⟨""⟩, grainBirthTariff := grainBirthTariff }
  let profile ← BirthRuntimeProfile.select nativeConfig deployed
  unless source.expectedSemantics = profile.semantics do
    throw s!"{path}.genesis.expectedSemantics: does not match the source-derived native profile"
  let creator := SubjectId.mk (← nat (path ++ ".creator") (← field path "creator" obj))
  let nonce ← nat (path ++ ".nonce") (← field path "nonce" obj)
  let movements ← list (path ++ ".funding") funding (← field path "funding" obj)
  let payer ← nat (path ++ ".feePayer") (← field path "feePayer" obj)
  let capabilities ← list (path ++ ".sourceCapabilities")
    (fun p value => CapabilityId.mk <$> nat p value) (← field path "sourceCapabilities" obj)
  pure (⟨source, profile, height, creator, nonce, movements, payer, capabilities⟩,
    ← field path specField obj)

def applicationSpec (path : String) (json : Lean.Json) :
    Result ApplicationGrainBirth.Spec := do
  let obj ← exactObject path ["app", "packageManifest", "snapshotManifest", "owner",
    "appOwnerCapability", "appControlCapability", "packageOwnerCapability",
    "packageControlCapability", "snapshotOwnerCapability", "snapshotControlCapability"] json
  pure {
    app := ← nat (path ++ ".app") (← field path "app" obj)
    packageManifest := ← nat (path ++ ".packageManifest") (← field path "packageManifest" obj)
    snapshotManifest := ← nat (path ++ ".snapshotManifest") (← field path "snapshotManifest" obj)
    owner := ⟨← nat (path ++ ".owner") (← field path "owner" obj)⟩
    appOwnerCapability := ⟨← nat (path ++ ".appOwnerCapability") (← field path "appOwnerCapability" obj)⟩
    appControlCapability := ⟨← nat (path ++ ".appControlCapability") (← field path "appControlCapability" obj)⟩
    packageOwnerCapability := ⟨← nat (path ++ ".packageOwnerCapability")
      (← field path "packageOwnerCapability" obj)⟩
    packageControlCapability := ⟨← nat (path ++ ".packageControlCapability")
      (← field path "packageControlCapability" obj)⟩
    snapshotOwnerCapability := ⟨← nat (path ++ ".snapshotOwnerCapability")
      (← field path "snapshotOwnerCapability" obj)⟩
    snapshotControlCapability := ⟨← nat (path ++ ".snapshotControlCapability")
      (← field path "snapshotControlCapability" obj)⟩ }

private def applicationSessionKind (path : String) (json : Lean.Json) :
    Result ApplicationGrainSession.Kind := do
  match ← string path json with
  | "web" => pure .web
  | "api" => pure .api
  | _ => failAt path "expected web or api"

def applicationSessionSpec (path : String) (json : Lean.Json) :
    Result ApplicationGrainSessionBirth.Spec := do
  let obj ← exactObject path ["app", "session", "descriptor", "participant", "kind",
    "sessionOwnerCapability", "sessionControlCapability",
    "descriptorOwnerCapability", "descriptorControlCapability"] json
  pure {
    app := ← nat (path ++ ".app") (← field path "app" obj)
    session := ← nat (path ++ ".session") (← field path "session" obj)
    descriptor := ← nat (path ++ ".descriptor") (← field path "descriptor" obj)
    participant := ⟨← nat (path ++ ".participant") (← field path "participant" obj)⟩
    kind := ← applicationSessionKind (path ++ ".kind") (← field path "kind" obj)
    sessionOwnerCapability := ⟨← nat (path ++ ".sessionOwnerCapability")
      (← field path "sessionOwnerCapability" obj)⟩
    sessionControlCapability := ⟨← nat (path ++ ".sessionControlCapability")
      (← field path "sessionControlCapability" obj)⟩
    descriptorOwnerCapability := ⟨← nat (path ++ ".descriptorOwnerCapability")
      (← field path "descriptorOwnerCapability" obj)⟩
    descriptorControlCapability := ⟨← nat (path ++ ".descriptorControlCapability")
      (← field path "descriptorControlCapability" obj)⟩ }

private def applicationBirth (path : String) (json : Lean.Json)
    (grainBirthTariff : Option NativeHost.GrainBirthTariffPin := none)
    (deployed : Option NativeHost.Config := none) : Result Draft := do
  let (context, specJson) ← applicationBirthContext path "application" json grainBirthTariff none deployed
  let spec ← applicationSpec (path ++ ".application") specJson
  let ready ← ApplicationGrainBirth.prepare spec
  let descriptor := ready.descriptor context.profile context.source context.height
    context.creator context.nonce context.feePayer context.funding
  pure (.birth ((ResourceBirthCodec.descriptorCodec CanonicalCellRegistry.registry).encode descriptor)
    context.sourceCapabilities)

private def applicationSessionBirth (path : String) (json : Lean.Json)
    (grainBirthTariff : Option NativeHost.GrainBirthTariffPin := none)
    (deployed : Option NativeHost.Config := none) : Result Draft := do
  let (context, specJson) ← applicationBirthContext path "session" json grainBirthTariff none deployed
  let spec ← applicationSessionSpec (path ++ ".session") specJson
  let ready ← ApplicationGrainSessionBirth.prepare spec
  let descriptor := ready.descriptor context.profile context.source context.height
    context.creator context.nonce context.feePayer context.funding
  pure (.birth ((ResourceBirthCodec.descriptorCodec CanonicalCellRegistry.registry).encode descriptor)
    context.sourceCapabilities)

private structure GrainBirthPeer where
  task : Nat
  capability : CapabilityId
  observeCapability : CapabilityId
  root : Digest
  before : AgentGrain.State

private def grainBirthPeer (path : String) (json : Lean.Json) : Result GrainBirthPeer := do
  let obj ← exactObject path ["task", "capability", "observeCapability", "targetRoot", "before"] json
  let beforeObj ← exactObject (path ++ ".before")
    ["generation", "status", "remaining", "reserved"] (← field path "before" obj)
  pure {
    task := ← nat (path ++ ".task") (← field path "task" obj)
    capability := ⟨← nat (path ++ ".capability") (← field path "capability" obj)⟩
    observeCapability := ⟨← nat (path ++ ".observeCapability")
      (← field path "observeCapability" obj)⟩
    root := ⟨← nat (path ++ ".targetRoot") (← field path "targetRoot" obj)⟩
    before := ⟨← int (path ++ ".before.generation") (← field (path ++ ".before") "generation" beforeObj),
      ← int (path ++ ".before.status") (← field (path ++ ".before") "status" beforeObj),
      ← int (path ++ ".before.remaining") (← field (path ++ ".before") "remaining" beforeObj),
      ← int (path ++ ".before.reserved") (← field (path ++ ".before") "reserved" beforeObj)⟩ }

/-- Wrap one source-authored canonical birth descriptor in the same Book and
tool/parent composite. `authorBirth` derives all born cells, policies, grants
and native fee; this wrapper cannot accept Rust-supplied descriptor bytes. -/
def grainBirthFrom (path sourceField : String) (json : Lean.Json)
    (authorBirth : String → Lean.Json → Option NativeHost.GrainBirthTariffPin → Result Draft) :
    Result Draft := do
  let obj ← exactObject path ["tariff", sourceField, "tool", "parent"] json
  let tariffObj ← exactObject (path ++ ".tariff") ["base", "perBirth"]
    (← field path "tariff" obj)
  let pinned : NativeHost.GrainBirthTariffPin :=
    ⟨← nat (path ++ ".tariff.base") (← field (path ++ ".tariff") "base" tariffObj),
      ← nat (path ++ ".tariff.perBirth") (← field (path ++ ".tariff") "perBirth" tariffObj)⟩
  unless 0 < pinned.base do throw s!"{path}.tariff.base: must be positive"
  let .birth birthBytes capabilities ← authorBirth (path ++ "." ++ sourceField)
      (← field path sourceField obj) (some pinned)
    | throw s!"{path}.{sourceField}: expected a birth draft"
  let some born := (ResourceBirthCodec.descriptorCodec CanonicalCellRegistry.registry).decode birthBytes
    | throw s!"{path}.{sourceField}: noncanonical descriptor"
  let tool ← grainBirthPeer (path ++ ".tool") (← field path "tool" obj)
  let parent ← grainBirthPeer (path ++ ".parent") (← field path "parent" obj)
  let source : GrainResourceBirthController.Source := {
    birth := born
    toolTask := tool.task, toolCapability := tool.capability
    toolObserveCapability := tool.observeCapability, toolRoot := tool.root
    toolBefore := tool.before
    parentTask := parent.task, parentCapability := parent.capability
    parentObserveCapability := parent.observeCapability, parentRoot := parent.root
    parentBefore := parent.before }
  pure (.birth (GrainResourceBirthHostCodec.sourceCodec.encode source) capabilities)

/-- Existing content-family composite. -/
private def grainBirth (path : String) (json : Lean.Json)
    (deployed : Option NativeHost.Config := none) : Result Draft :=
  grainBirthFrom path "birth" json (fun path source tariff => birth path source tariff deployed)

private def grainBirthIntent (path : String) (json : Lean.Json)
    (deployed : Option NativeHost.Config := none) : Result Intent := do
  let obj ← exactObject path ["subject", "nonce", "grainBirth", "grants"] json
  pure ⟨⟨← nat (path ++ ".subject") (← field path "subject" obj)⟩,
    ← nat (path ++ ".nonce") (← field path "nonce" obj),
    .prepare (← grainBirth (path ++ ".grainBirth") (← field path "grainBirth" obj) deployed),
    ← list (path ++ ".grants") grant (← field path "grants" obj)⟩

def grainBirthIntentFrom (path intentField sourceField : String) (json : Lean.Json)
    (authorBirth : String → Lean.Json → Option NativeHost.GrainBirthTariffPin → Result Draft) :
    Result Intent := do
  let obj ← exactObject path ["subject", "nonce", intentField, "grants"] json
  pure ⟨⟨← nat (path ++ ".subject") (← field path "subject" obj)⟩,
    ← nat (path ++ ".nonce") (← field path "nonce" obj),
    .prepare (← grainBirthFrom (path ++ "." ++ intentField) sourceField
      (← field path intentField obj) authorBirth),
    ← list (path ++ ".grants") grant (← field path "grants" obj)⟩

private def applicationGrainBirthIntent (path : String) (json : Lean.Json)
    (deployed : Option NativeHost.Config := none) : Result Intent :=
  grainBirthIntentFrom path "applicationGrainBirth" "applicationBirth" json
    (fun path source tariff => applicationBirth path source tariff deployed)

private def applicationSessionGrainBirthIntent (path : String) (json : Lean.Json)
    (deployed : Option NativeHost.Config := none) : Result Intent :=
  grainBirthIntentFrom path "applicationSessionGrainBirth" "applicationSessionBirth" json
    (fun path source tariff => applicationSessionBirth path source tariff deployed)

def birthIntentFrom (path : String) (json : Lean.Json)
    (authorBirth : String → Lean.Json → Result Draft) : Result Intent := do
  let obj ← exactObject path ["subject", "nonce", "birth", "grants"] json
  pure ⟨⟨← nat (path ++ ".subject") (← field path "subject" obj)⟩,
    ← nat (path ++ ".nonce") (← field path "nonce" obj),
    .prepare (← authorBirth (path ++ ".birth") (← field path "birth" obj)),
    ← list (path ++ ".grants") grant (← field path "grants" obj)⟩

private def birthIntent (path : String) (json : Lean.Json)
    (deployed : Option NativeHost.Config := none) : Result Intent :=
  birthIntentFrom path json (fun birthPath source => birth birthPath source none deployed)

private def applicationBirthIntent (path : String) (json : Lean.Json)
    (deployed : Option NativeHost.Config := none) : Result Intent := do
  let obj ← exactObject path ["subject", "nonce", "applicationBirth", "grants"] json
  pure ⟨⟨← nat (path ++ ".subject") (← field path "subject" obj)⟩,
    ← nat (path ++ ".nonce") (← field path "nonce" obj),
    .prepare (← applicationBirth (path ++ ".applicationBirth")
      (← field path "applicationBirth" obj) none deployed),
    ← list (path ++ ".grants") grant (← field path "grants" obj)⟩

private def applicationSessionBirthIntent (path : String) (json : Lean.Json)
    (deployed : Option NativeHost.Config := none) : Result Intent := do
  let obj ← exactObject path ["subject", "nonce", "applicationSessionBirth", "grants"] json
  pure ⟨⟨← nat (path ++ ".subject") (← field path "subject" obj)⟩,
    ← nat (path ++ ".nonce") (← field path "nonce" obj),
    .prepare (← applicationSessionBirth (path ++ ".applicationSessionBirth")
      (← field path "applicationSessionBirth" obj) none deployed),
    ← list (path ++ ".grants") grant (← field path "grants" obj)⟩

private def grainSource (path : String) (json : Lean.Json) :
    Result (DeclaredResourceController.Command × AgentGrain.State) := do
  let obj ← object path json
  for key in obj.foldl (init := []) (fun names key _ => key :: names) do
    unless ["task", "subject", "capability",
      "schemaVersion", "expectedTargetRoot", "context", "before", "operation",
      "publications", "observeCapability", "parentWitness"].contains key do
      throw s!"{path}: unknown field {key}"
  let stateObj ← exactObject (path ++ ".before") ["generation", "status", "remaining", "reserved"]
    (← field path "before" obj)
  let state : AgentGrain.State := ⟨← int (path ++ ".before.generation") (← field (path ++ ".before") "generation" stateObj),
    ← int (path ++ ".before.status") (← field (path ++ ".before") "status" stateObj),
    ← int (path ++ ".before.remaining") (← field (path ++ ".before") "remaining" stateObj),
    ← int (path ++ ".before.reserved") (← field (path ++ ".before") "reserved" stateObj)⟩
  let operationJson ← field path "operation" obj
  let (tag, _) ← tagged (path ++ ".operation") operationJson
  let operation ← match tag with
    | "input" => exactObject (path ++ ".operation") ["type"] operationJson *> pure .input
    | "attach" | "mode" => do
        let op ← exactObject (path ++ ".operation") ["type", "soft"] operationJson
        let soft ← bool (path ++ ".operation.soft") (← field (path ++ ".operation") "soft" op)
        pure <| if tag = "attach" then AgentGrain.Operation.attach soft else .mode soft
    | "reserve" | "settle" => do
        let name := if tag = "reserve" then "amount" else "charge"
        let op ← exactObject (path ++ ".operation") ["type", name] operationJson
        let value ← int (path ++ ".operation." ++ name) (← field (path ++ ".operation") name op)
        pure <| if tag = "reserve" then .reserve value else .settle value
    | "disconnect" => exactObject (path ++ ".operation") ["type"] operationJson *> pure .disconnect
    | "interrupt" => exactObject (path ++ ".operation") ["type"] operationJson *> pure .interrupt
    | "cancel" => exactObject (path ++ ".operation") ["type"] operationJson *> pure .cancel
    | _ => failAt (path ++ ".operation.type") "unknown grain operation"
  let task ← nat (path ++ ".task") (← field path "task" obj)
  let contextObj ← exactObject (path ++ ".context") ["operationId", "payload"]
    (← field path "context" obj)
  let operationId ← nat (path ++ ".context.operationId")
    (← field (path ++ ".context") "operationId" contextObj)
  let payload ← string (path ++ ".context.payload")
    (← field (path ++ ".context") "payload" contextObj)
  let contextBytes := (StreamCodec.product StreamCodec.nat PolicyRecordCodec.stringStream).encode
    (operationId, payload)
  let subject := SubjectId.mk (← nat (path ++ ".subject") (← field path "subject" obj))
  let capability := CapabilityId.mk (← nat (path ++ ".capability") (← field path "capability" obj))
  let targetRoot := Digest.mk
    (← nat (path ++ ".expectedTargetRoot") (← field path "expectedTargetRoot" obj))
  let schemaVersion ← nat (path ++ ".schemaVersion") (← field path "schemaVersion" obj)
  unless schemaVersion = 1 do throw s!"{path}.schemaVersion: grain schema version must be 1"
  let publications ← match obj.get? "publications" with
    | some value => list (path ++ ".publications") commandTarget value
    | none => pure []
  let observeCapability ← match obj.get? "observeCapability" with
    | some selected => do
        let capability ← optional (path ++ ".observeCapability")
          (fun p j => CapabilityId.mk <$> nat p j) selected
        pure capability
    | none => pure none
  let publications ← match obj.get? "parentWitness" with
    | none => pure publications
    | some value => do
        let witnessPath := path ++ ".parentWitness"
        let witness ← exactObject witnessPath
          ["task", "capability", "observeCapability", "expectedTargetRoot", "before"] value
        let parentTask ← nat (witnessPath ++ ".task") (← field witnessPath "task" witness)
        let parentCapability := CapabilityId.mk
          (← nat (witnessPath ++ ".capability") (← field witnessPath "capability" witness))
        let parentObserve := CapabilityId.mk
          (← nat (witnessPath ++ ".observeCapability")
            (← field witnessPath "observeCapability" witness))
        let parentRoot := Digest.mk
          (← nat (witnessPath ++ ".expectedTargetRoot")
            (← field witnessPath "expectedTargetRoot" witness))
        let parentBeforePath := witnessPath ++ ".before"
        let parentBeforeObj ← exactObject parentBeforePath
          ["generation", "status", "remaining", "reserved"]
          (← field witnessPath "before" witness)
        let parentBefore : AgentGrain.State :=
          ⟨← int (parentBeforePath ++ ".generation")
              (← field parentBeforePath "generation" parentBeforeObj),
           ← int (parentBeforePath ++ ".status")
              (← field parentBeforePath "status" parentBeforeObj),
           ← int (parentBeforePath ++ ".remaining")
              (← field parentBeforePath "remaining" parentBeforeObj),
           ← int (parentBeforePath ++ ".reserved")
              (← field parentBeforePath "reserved" parentBeforeObj)⟩
        pure <| (AgentGrain.Operation.input).target parentTask parentCapability
          parentRoot parentBefore (some parentObserve) :: publications
  let command := operation.command subject (AgentGrain.contextNonce contextBytes)
    task capability targetRoot state publications observeCapability
  pure (command, operation.after state)

/-- Wrap a source-authored grain transition in the ordinary prepare intent. -/
private def grainIntent (path : String) (json : Lean.Json) : Result Intent := do
  let obj ← exactObject path ["grain", "grants", "intentNonce"] json
  let source ← grainSource (path ++ ".grain") (← field path "grain" obj)
  let grants ← list (path ++ ".grants") grant (← field path "grants" obj)
  let nonce ← nat (path ++ ".intentNonce") (← field path "intentNonce" obj)
  pure ⟨source.1.subject, nonce,
    .prepare (.invoke (DeclaredResourceController.commandCodec.encode source.1)), grants⟩

/-- Re-pin a worker's no-op witness to a newly attached generation through
the ordinary signed policy-install receiver. The caller supplies the observed
current head and authority root; neither is trusted without native checks. -/
private def grainPolicyInstallIntent (path : String) (json : Lean.Json) : Result Intent := do
  let raw ← object path json
  let some worker ← grainWorker path raw
    | failAt path "worker subject and generation required"
  let obj ← exactObject path (["subject", "intentNonce", "declarationNonce", "task",
    "owner", "control", "domain", "semantics", "expectedPreRoot", "expectedVersion",
    "expectedAddress", "grants"] ++ grainWorkerFields raw) json
  let subject := SubjectId.mk (← nat (path ++ ".subject") (← field path "subject" obj))
  let owner ← nat (path ++ ".owner") (← field path "owner" obj)
  let task ← nat (path ++ ".task") (← field path "task" obj)
  let version ← nat (path ++ ".expectedVersion") (← field path "expectedVersion" obj)
  let address := Digest.mk (← nat (path ++ ".expectedAddress")
    (← field path "expectedAddress" obj))
  let source : PolicyRecord :=
    ⟨⟨task⟩, version + 1,
      ⟨← nat (path ++ ".domain") (← field path "domain" obj)⟩,
      ⟨← nat (path ++ ".semantics") (← field path "semantics" obj)⟩,
      some address, grainPolicy owner (some worker)⟩
  let declaration : PolicyInstallController.Declaration :=
    ⟨⟨← nat (path ++ ".expectedPreRoot") (← field path "expectedPreRoot" obj)⟩,
      some ⟨version, address⟩,
      ← nat (path ++ ".declarationNonce") (← field path "declarationNonce" obj), source⟩
  let control := CapabilityId.mk (← nat (path ++ ".control") (← field path "control" obj))
  let grants ← list (path ++ ".grants") grant (← field path "grants" obj)
  let nonce ← nat (path ++ ".intentNonce") (← field path "intentNonce" obj)
  pure ⟨subject, nonce,
    .prepare (.install subject control (PolicyInstallController.declarationCodec.encode declaration)),
    grants⟩

private def dispatchHttpHeader (path : String) (json : Lean.Json) : Result ApplicationDispatchCodec.Header := do
  let obj ← exactObject path ["nameHex", "valueHex", "generated"] json
  pure ⟨← decodeHex (path ++ ".nameHex") (← field path "nameHex" obj),
    ← decodeHex (path ++ ".valueHex") (← field path "valueHex" obj),
    ← bool (path ++ ".generated") (← field path "generated" obj)⟩

private def dispatchHttpRequest (path : String) (json : Lean.Json) :
    Result ApplicationDispatchCodec.Request := do
  let obj ← exactObject path
    ["operationId", "methodHex", "pathHex", "queryHex", "headers", "bodyHex"] json
  pure ⟨← nat (path ++ ".operationId") (← field path "operationId" obj),
    ← decodeHex (path ++ ".methodHex") (← field path "methodHex" obj),
    ← decodeHex (path ++ ".pathHex") (← field path "pathHex" obj),
    ← decodeHex (path ++ ".queryHex") (← field path "queryHex" obj),
    ← list (path ++ ".headers") dispatchHttpHeader (← field path "headers" obj),
    ← decodeHex (path ++ ".bodyHex") (← field path "bodyHex" obj)⟩

private def dispatchAuthorRequest (json : Lean.Json) : Result (List UInt8) := do
  let obj ← exactObject "$"
    ["issueIndex", "ticketResource", "packageManifest", "snapshotManifest",
     "sessionObserveCapability", "manifestObserveCapability",
     "enrollmentObserveCapability", "http"] json
  let request : ApplicationDispatchAuthoring.Request :=
    ⟨← nat "$.issueIndex" (← field "$" "issueIndex" obj),
     ← nat "$.ticketResource" (← field "$" "ticketResource" obj),
     ← nat "$.packageManifest" (← field "$" "packageManifest" obj),
     ← nat "$.snapshotManifest" (← field "$" "snapshotManifest" obj),
     ⟨← nat "$.sessionObserveCapability" (← field "$" "sessionObserveCapability" obj)⟩,
     ⟨← nat "$.manifestObserveCapability" (← field "$" "manifestObserveCapability" obj)⟩,
     ⟨← nat "$.enrollmentObserveCapability" (← field "$" "enrollmentObserveCapability" obj)⟩,
     ← dispatchHttpRequest "$.http" (← field "$" "http" obj)⟩
  pure (ApplicationDispatchAuthoring.requestCodec.encode request)

private def agentPaidReserveRequest (json : Lean.Json) : Result (List UInt8) := do
  let obj ← exactObject "$" ["base", "parentTask", "parentCapability",
    "parentObserve", "purseTask", "purseCapability", "purseObserve",
    "payerSubject", "reserveAmount", "maximumCharge", "reserveOperationId"] json
  let baseBytes ← dispatchAuthorRequest (← field "$" "base" obj)
  let some dispatch := ApplicationDispatchAuthoring.requestCodec.decode baseBytes
    | failAt "$.base" "noncanonical dispatch request"
  let request : ApplicationDispatchAgentPaidAuthoring.Request :=
    { base :=
        { base := dispatch
          task := ← nat "$.parentTask" (← field "$" "parentTask" obj)
          parentCapability := ⟨← nat "$.parentCapability"
            (← field "$" "parentCapability" obj)⟩
          parentObserveCapability := ⟨← nat "$.parentObserve"
            (← field "$" "parentObserve" obj)⟩ }
      purseTask := ← nat "$.purseTask" (← field "$" "purseTask" obj)
      purseCapability := ⟨← nat "$.purseCapability"
        (← field "$" "purseCapability" obj)⟩
      purseObserve := ⟨← nat "$.purseObserve"
        (← field "$" "purseObserve" obj)⟩
      payerSubject := ⟨← nat "$.payerSubject" (← field "$" "payerSubject" obj)⟩
      reserveAmount := ← int "$.reserveAmount" (← field "$" "reserveAmount" obj)
      maximumCharge := ← int "$.maximumCharge" (← field "$" "maximumCharge" obj)
      reserveOperationId := ← nat "$.reserveOperationId"
        (← field "$" "reserveOperationId" obj) }
  unless request.reserveAmount >= 0 && request.maximumCharge >= 0 &&
      request.maximumCharge <= request.reserveAmount do
    failAt "$" "invalid fixed reserve or charge bound"
  return ApplicationDispatchAgentPaidAuthoring.requestCodec.encode request

private def agentPaidRequest (json : Lean.Json) : Result (List UInt8) := do
  let obj ← exactObject "$" ["fixedRequestHex", "contextHex", "reserveIndex"] json
  let fixedBytes ← decodeHex "$.fixedRequestHex" (← field "$" "fixedRequestHex" obj)
  let some fixed := ApplicationDispatchAgentPaidAuthoring.requestCodec.decode fixedBytes
    | failAt "$.fixedRequestHex" "noncanonical paid fixed request"
  let contextBytes ← decodeHex "$.contextHex" (← field "$" "contextHex" obj)
  let some context := ApplicationDispatchAgentReserveContext.codec.decode contextBytes
    | failAt "$.contextHex" "noncanonical reserve context"
  let request : ApplicationDispatchAgentPaidAuthoring.PaidRequest :=
    { fixed := fixed, context := context
      reserveIndex := ← nat "$.reserveIndex" (← field "$" "reserveIndex" obj) }
  return ApplicationDispatchAgentPaidAuthoring.paidRequestCodec.encode request

private def agentLifetimeReserveRequest (json : Lean.Json) : Result (List UInt8) := do
  let obj ← exactObject "$" ["fixed", "grantIssueIndex", "grantResource",
    "grantObserveCapability"] json
  let fixedBytes ← agentPaidReserveRequest (← field "$" "fixed" obj)
  let some fixed := ApplicationDispatchAgentPaidAuthoring.requestCodec.decode fixedBytes
    | failAt "$.fixed" "noncanonical agent reserve request"
  let request : ApplicationAgentLifetimeDispatchPaidAuthoring.Request :=
    { fixed := fixed
      grantIssueIndex := ← nat "$.grantIssueIndex" (← field "$" "grantIssueIndex" obj)
      grantResource := ← nat "$.grantResource" (← field "$" "grantResource" obj)
      grantObserveCapability := ⟨← nat "$.grantObserveCapability"
        (← field "$" "grantObserveCapability" obj)⟩ }
  return ApplicationAgentLifetimeDispatchPaidAuthoring.requestCodec.encode request

private def agentLifetimePaidRequest (json : Lean.Json) : Result (List UInt8) := do
  let obj ← exactObject "$" ["fixedRequestHex", "contextHex", "reserveIndex"] json
  let fixedBytes ← decodeHex "$.fixedRequestHex" (← field "$" "fixedRequestHex" obj)
  let some fixed := ApplicationAgentLifetimeDispatchPaidAuthoring.requestCodec.decode fixedBytes
    | failAt "$.fixedRequestHex" "noncanonical lifetime reserve request"
  let contextBytes ← decodeHex "$.contextHex" (← field "$" "contextHex" obj)
  let some context := ApplicationAgentLifetimeDispatchReserveContext.codec.decode contextBytes
    | failAt "$.contextHex" "noncanonical lifetime reserve context"
  let request : ApplicationAgentLifetimeDispatchPaidAuthoring.PaidRequest :=
    { fixed := fixed, context := context
      reserveIndex := ← nat "$.reserveIndex" (← field "$" "reserveIndex" obj) }
  return ApplicationAgentLifetimeDispatchPaidAuthoring.paidRequestCodec.encode request

private def completionDigest (path : String) (json : Lean.Json) : Result Digest :=
  return ⟨← nat path json⟩

/-- Validate an already signed BEGIN-v2 frame for this physical host profile.
The generic native BEGIN route and historical replay remain unchanged. -/
private def residentBegin (json : Lean.Json) : Result (List UInt8) := do
  let obj ← exactObject "$" ["begin"] json
  let bytes ← decodeHex "$.begin" (← field "$" "begin" obj)
  let some ingress := ApplicationLifecycleBeginV2Ingress.codec.decode bytes
    | throw "noncanonical BEGIN-v2 ingress"
  unless ApplicationLifecycleResidentProfile.beginMatches ingress do
    throw "BEGIN-v2 is outside the resident signed-SPK physical hosting profile"
  return ingress.canonicalBytes

private def completionReport (json : Lean.Json) : Result (List UInt8) := do
  let obj ← exactObject "$" ["begin", "claim", "nonce", "unit", "materializedImage",
    "outcome", "invocationId", "controlGroup", "pid", "stopAudit"] json
  let outcome ← string "$.outcome" (← field "$" "outcome" obj)
  let outcome ← match outcome with
    | "materialized" => pure ApplicationLifecycleCompletionReport.Outcome.materialized
    | "running" => pure .running
    | "stopped" => pure .stopped
    | _ => failAt "$.outcome" "expected materialized, running, or stopped"
  let observed : ApplicationLifecycleCompletionAuthoring.PhysicalObservation :=
    { nonce := ← nat "$.nonce" (← field "$" "nonce" obj)
      unit := ← decodeHex "$.unit" (← field "$" "unit" obj)
      materializedImage := ← decodeHex "$.materializedImage" (← field "$" "materializedImage" obj)
      outcome := outcome
      invocationId := ← decodeHex "$.invocationId" (← field "$" "invocationId" obj)
      controlGroup := ← decodeHex "$.controlGroup" (← field "$" "controlGroup" obj)
      pid := ← nat "$.pid" (← field "$" "pid" obj)
      stopAudit := ← decodeHex "$.stopAudit" (← field "$" "stopAudit" obj) }
  let report ← ApplicationLifecycleCompletionAuthoring.reportPlan
    (← decodeHex "$.begin" (← field "$" "begin" obj))
    (← decodeHex "$.claim" (← field "$" "claim" obj)) observed
  return ApplicationLifecycleCompletionReport.codec.encode report

private def completionSigningFrame (json : Lean.Json) : Result (List UInt8) := do
  let obj ← exactObject "$" ["domain", "semantics", "begin", "report"] json
  ApplicationLifecycleCompletionAuthoring.signingPlan
    (← completionDigest "$.domain" (← field "$" "domain" obj))
    (← completionDigest "$.semantics" (← field "$" "semantics" obj))
    (← decodeHex "$.begin" (← field "$" "begin" obj))
    (← decodeHex "$.report" (← field "$" "report" obj))

private def completionSignedReport (json : Lean.Json) : Result (List UInt8) := do
  let obj ← exactObject "$" ["begin", "report", "signature"] json
  ApplicationLifecycleCompletionAuthoring.signedReport
    (← decodeHex "$.begin" (← field "$" "begin" obj))
    (← decodeHex "$.report" (← field "$" "report" obj))
    (← decodeHex "$.signature" (← field "$" "signature" obj))

private def launchStopAudit (json : Lean.Json) : Result ApplicationLifecycleCompletionReport.StopAudit := do
  let obj ← exactObject "$.stopAudit" ["unit", "recordedInvocationId",
    "recordedControlGroup", "managerLoaded", "managerInactive", "managerMainPid",
    "managerJobEmpty", "managerInvocationCleared", "cgroupUnpopulated",
    "observationDigest"] json
  return {
    unit := ← decodeHex "$.stopAudit.unit" (← field "$.stopAudit" "unit" obj)
    recordedInvocationId := ← decodeHex "$.stopAudit.recordedInvocationId"
      (← field "$.stopAudit" "recordedInvocationId" obj)
    recordedControlGroup := ← decodeHex "$.stopAudit.recordedControlGroup"
      (← field "$.stopAudit" "recordedControlGroup" obj)
    managerLoaded := ← bool "$.stopAudit.managerLoaded" (← field "$.stopAudit" "managerLoaded" obj)
    managerInactive := ← bool "$.stopAudit.managerInactive" (← field "$.stopAudit" "managerInactive" obj)
    managerMainPid := ← nat "$.stopAudit.managerMainPid" (← field "$.stopAudit" "managerMainPid" obj)
    managerJobEmpty := ← bool "$.stopAudit.managerJobEmpty" (← field "$.stopAudit" "managerJobEmpty" obj)
    managerInvocationCleared := ← bool "$.stopAudit.managerInvocationCleared"
      (← field "$.stopAudit" "managerInvocationCleared" obj)
    cgroupUnpopulated := ← bool "$.stopAudit.cgroupUnpopulated"
      (← field "$.stopAudit" "cgroupUnpopulated" obj)
    observationDigest := ← completionDigest "$.stopAudit.observationDigest"
      (← field "$.stopAudit" "observationDigest" obj) }

/-- Physical observations are supplied by the protected host. The source
helper derives the volume identity and canonical v2 report. -/
private def launchPhysicalReport (json : Lean.Json) : Result (List UInt8) := do
  let obj ← exactObject "$" ["begin", "committedClaim", "nonce", "unit",
    "materializedImage", "outcome", "invocationId", "controlGroup", "pid",
    "stopAudit", "volumeWitness"] json
  let outcome ← match ← string "$.outcome" (← field "$" "outcome" obj) with
    | "materialized" => pure ApplicationLifecycleCompletionReport.Outcome.materialized
    | "running" => pure .running
    | "stopped" => pure .stopped
    | _ => failAt "$.outcome" "expected materialized, running, or stopped"
  let observed : ApplicationLifecycleLaunchReportAuthoring.PhysicalObservation := {
    nonce := ← nat "$.nonce" (← field "$" "nonce" obj)
    unit := ← decodeHex "$.unit" (← field "$" "unit" obj)
    materializedImage := ← decodeHex "$.materializedImage" (← field "$" "materializedImage" obj)
    outcome := outcome
    invocationId := ← decodeHex "$.invocationId" (← field "$" "invocationId" obj)
    controlGroup := ← decodeHex "$.controlGroup" (← field "$" "controlGroup" obj)
    pid := ← nat "$.pid" (← field "$" "pid" obj)
    stopAudit := ← optional "$.stopAudit" (fun _ value => launchStopAudit value)
      (← field "$" "stopAudit" obj)
    volumeWitness := ← optional "$.volumeWitness" decodeHex
      (← field "$" "volumeWitness" obj) }
  let report ← ApplicationLifecycleLaunchReportAuthoring.reportPlan
    (← decodeHex "$.begin" (← field "$" "begin" obj))
    (← decodeHex "$.committedClaim" (← field "$" "committedClaim" obj)) observed
  return ApplicationLifecycleCompletionV2Report.codec.encode report

private def launchPhysicalSigningFrame (json : Lean.Json) : Result (List UInt8) := do
  let obj ← exactObject "$" ["begin", "report"] json
  ApplicationLifecycleLaunchReportAuthoring.signingPlan
    (← decodeHex "$.begin" (← field "$" "begin" obj))
    (← decodeHex "$.report" (← field "$" "report" obj))

private def launchPhysicalSignedReport (json : Lean.Json) : Result (List UInt8) := do
  let obj ← exactObject "$" ["begin", "report", "signature"] json
  ApplicationLifecycleLaunchReportAuthoring.signedReport
    (← decodeHex "$.begin" (← field "$" "begin" obj))
    (← decodeHex "$.report" (← field "$" "report" obj))
    (← decodeHex "$.signature" (← field "$" "signature" obj))

private def completionSource (json : Lean.Json) : Result (List UInt8) := do
  let obj ← exactObject "$" ["begin", "claimIngress", "signedReport",
    "appRoot", "packageRoot", "appCapability", "appObserveCapability",
    "packageCapability", "packageObserveCapability", "packageAtomBefore"] json
  let current : ApplicationLifecycleCompletionAuthoring.CurrentObservation :=
    { appRoot := ← completionDigest "$.appRoot" (← field "$" "appRoot" obj)
      packageRoot := ← completionDigest "$.packageRoot" (← field "$" "packageRoot" obj)
      appCapability := ⟨← nat "$.appCapability" (← field "$" "appCapability" obj)⟩
      appObserveCapability := ⟨← nat "$.appObserveCapability" (← field "$" "appObserveCapability" obj)⟩
      packageCapability := ⟨← nat "$.packageCapability" (← field "$" "packageCapability" obj)⟩
      packageObserveCapability := ⟨← nat "$.packageObserveCapability" (← field "$" "packageObserveCapability" obj)⟩
      packageAtomBefore := ← optional "$.packageAtomBefore" atomRecord
        (← field "$" "packageAtomBefore" obj) }
  let source ← ApplicationLifecycleCompletionAuthoring.sourcePlan
    (← decodeHex "$.begin" (← field "$" "begin" obj))
    (← decodeHex "$.claimIngress" (← field "$" "claimIngress" obj))
    (← decodeHex "$.signedReport" (← field "$" "signedReport" obj)) current
  return ApplicationLifecycleCompletionSource.codec.encode source

private def completionCommand (json : Lean.Json) : Result (List UInt8) := do
  let obj ← exactObject "$" ["domain", "semantics", "source"] json
  ApplicationLifecycleCompletionAuthoring.commandPlan
    (← completionDigest "$.domain" (← field "$" "domain" obj))
    (← completionDigest "$.semantics" (← field "$" "semantics" obj))
    (← decodeHex "$.source" (← field "$" "source" obj))

private def completionSignedCommand (json : Lean.Json) : Result (List UInt8) := do
  let obj ← exactObject "$" ["command", "targetEnvelopes", "observeEnvelopes",
    "authorityEnvelope"] json
  ApplicationLifecycleCompletionAuthoring.signedCommandPlan
    (← decodeHex "$.command" (← field "$" "command" obj))
    (← list "$.targetEnvelopes" decodeHex (← field "$" "targetEnvelopes" obj))
    (← list "$.observeEnvelopes" decodeHex (← field "$" "observeEnvelopes" obj))
    (← decodeHex "$.authorityEnvelope" (← field "$" "authorityEnvelope" obj))

private def completionIngress (json : Lean.Json) : Result (List UInt8) := do
  let obj ← exactObject "$" ["domain", "semantics", "source", "signedCommand",
    "packageObservationEnvelope"] json
  ApplicationLifecycleCompletionAuthoring.assemble
    (← completionDigest "$.domain" (← field "$" "domain" obj))
    (← completionDigest "$.semantics" (← field "$" "semantics" obj))
    (← decodeHex "$.source" (← field "$" "source" obj))
    (← decodeHex "$.signedCommand" (← field "$" "signedCommand" obj))
    (← decodeHex "$.packageObservationEnvelope"
      (← field "$" "packageObservationEnvelope" obj))

private def completionOperatorRequest (json : Lean.Json) : Result (List UInt8) := do
  let obj ← exactObject "$" ["begin", "claimIngress", "signedReport"] json
  let request : ApplicationLifecycleCompletionOperator.Request :=
    { beginBytes := ← decodeHex "$.begin" (← field "$" "begin" obj)
      claimIngressBytes := ← decodeHex "$.claimIngress" (← field "$" "claimIngress" obj)
      signedReportBytes := ← decodeHex "$.signedReport" (← field "$" "signedReport" obj) }
  return ApplicationLifecycleCompletionOperator.requestCodec.encode request

private def launchCompletionOperatorRequest (json : Lean.Json) : Result (List UInt8) := do
  let obj ← exactObject "$" ["begin", "claimIngress", "signedReport"] json
  let request : ApplicationLifecycleLaunchCompletionAuthoring.Request :=
    { beginBytes := ← decodeHex "$.begin" (← field "$" "begin" obj)
      claimIngressBytes := ← decodeHex "$.claimIngress" (← field "$" "claimIngress" obj)
      signedReportBytes := ← decodeHex "$.signedReport" (← field "$" "signedReport" obj) }
  let bytes := ApplicationLifecycleLaunchCompletionAuthoring.requestCodec.encode request
  let _ ← ApplicationLifecycleLaunchCompletionInspection.inspectRequest bytes
  return bytes

private def residentBeginOperatorRequest (json : Lean.Json) : Result (List UInt8) := do
  let obj ← exactObject "$" ["kind", "operationId", "descriptor"] json
  let kind ← string "$.kind" (← field "$" "kind" obj)
  let kind ← match kind with
    | "install" => pure ApplicationLifecycleBegin.Kind.install
    | "start" => pure .start
    | _ => failAt "$.kind" "expected install or start"
  let request : ApplicationLifecycleBeginOperator.Request :=
    { kind := kind
      operationId := ← nat "$.operationId" (← field "$" "operationId" obj)
      descriptorBytes := ← decodeHex "$.descriptor" (← field "$" "descriptor" obj) }
  return ApplicationLifecycleBeginOperator.requestCodec.encode request

private def launchBeginOperatorRequest (json : Lean.Json) : Result (List UInt8) := do
  let obj ← exactObject "$" ["kind", "clientOperationId", "descriptor", "createIndex"] json
  let kind ← string "$.kind" (← field "$" "kind" obj)
  let kind ← match kind with
    | "install" => pure ApplicationLifecycleBegin.Kind.install
    | "start" => pure .start
    | "stop" => pure .stop
    | _ => failAt "$.kind" "expected install, start or stop"
  let request : ApplicationLifecycleLaunchBeginAuthoring.Request :=
    { kind := kind
      clientOperationId := ← nat "$.clientOperationId" (← field "$" "clientOperationId" obj)
      descriptorBytes := ← decodeHex "$.descriptor" (← field "$" "descriptor" obj)
      createIndex := ← optional "$.createIndex" nat (← field "$" "createIndex" obj) }
  let bytes := ApplicationLifecycleLaunchBeginAuthoring.requestCodec.encode request
  let _ ← ApplicationLifecycleLaunchBeginInspection.inspectRequest bytes
  return bytes

private def launchContinueOperatorRequest (json : Lean.Json) : Result (List UInt8) := do
  let obj ← exactObject "$" ["clientOperationId", "descriptor", "createdIndex"] json
  let request : ApplicationLifecycleLaunchBeginAuthoring.ContinueRequest :=
    { clientOperationId := ← nat "$.clientOperationId"
        (← field "$" "clientOperationId" obj)
      descriptorBytes := ← decodeHex "$.descriptor" (← field "$" "descriptor" obj)
      createdIndex := ← nat "$.createdIndex" (← field "$" "createdIndex" obj) }
  let bytes := ApplicationLifecycleLaunchBeginAuthoring.continueRequestCodec.encode request
  let _ ← ApplicationLifecycleLaunchBeginInspection.inspectContinueRequest bytes
  return bytes

private def lifecycleClaimOperatorRequest (json : Lean.Json) : Result (List UInt8) := do
  let obj ← exactObject "$" ["originalIndex", "queryNonce"] json
  let request : ApplicationLifecycleClaimOperator.Request :=
    { originalIndex := ← nat "$.originalIndex" (← field "$" "originalIndex" obj)
      queryNonce := ← nat "$.queryNonce" (← field "$" "queryNonce" obj) }
  return ApplicationLifecycleClaimOperator.requestCodec.encode request

private def launchClaimOperatorRequest (json : Lean.Json) : Result (List UInt8) := do
  let obj ← exactObject "$" ["originalIndex", "queryNonce"] json
  let request : ApplicationLifecycleLaunchClaimAuthoring.Request :=
    { originalIndex := ← nat "$.originalIndex" (← field "$" "originalIndex" obj)
      queryNonce := ← nat "$.queryNonce" (← field "$" "queryNonce" obj) }
  return ApplicationLifecycleLaunchClaimAuthoring.requestCodec.encode request

/-- This authors Mini's fixed web/API mapping from the host's one verified
signed-SPK parse. The caller supplies the signed ViewInfo projection, not Mini
interface IDs, kinds, versions, or a chosen package root. Physical custody
must independently compare every field with that same verified parse. -/
private def applicationSpkPackageIdentity (json : Lean.Json) : Result (List UInt8) := do
  let obj ← exactObject "$" ["rawSha256", "rawLength", "signedAppId",
    "signedAppVersion", "manifestSha256", "bridgeConfigSha256",
    "bridgeApiPath", "signedSchema"] json
  let rawSha ← decodeHex "$.rawSha256" (← field "$" "rawSha256" obj)
  let manifestSha ← decodeHex "$.manifestSha256" (← field "$" "manifestSha256" obj)
  let bridgeSha ← decodeHex "$.bridgeConfigSha256" (← field "$" "bridgeConfigSha256" obj)
  let appId ← string "$.signedAppId" (← field "$" "signedAppId" obj)
  let apiPath ← string "$.bridgeApiPath" (← field "$" "bridgeApiPath" obj)
  let schema ← ApplicationPermissionSchemaAuthoring.decodeSource
    (← field "$" "signedSchema" obj)
  let web : ApplicationDispatchManifest.Interface := ⟨1, 1, .web, schema⟩
  let interfaces : List ApplicationDispatchManifest.Interface :=
    if apiPath.isEmpty then [web] else [web, ⟨2, 1, .api, schema⟩]
  let descriptor : ApplicationSpkPackageIdentity.Descriptor :=
    { rawSha256 := rawSha
      rawLength := ← nat "$.rawLength" (← field "$" "rawLength" obj)
      signedAppId := appId.toUTF8.toList
      signedAppVersion := ← nat "$.signedAppVersion"
        (← field "$" "signedAppVersion" obj)
      manifestSha256 := manifestSha
      bridgeConfigSha256 := bridgeSha
      bridgeApiPath := apiPath.toUTF8.toList
      interfaces := interfaces }
  unless descriptor.valid do
    failAt "$" "signed SPK descriptor or fixed bridge mapping refused"
  return descriptor.canonicalBytes

/-- Source-owned authoring for a participant's proposed signing key. The
sponsor capability and proof of possession are checked only by the receiving
path; these bytes do not claim that the new key is admitted. -/
private def participantKeyEnrollment (json : Lean.Json) : Result (List UInt8) := do
  let obj ← exactObject "$" ["sponsor", "control", "nonce",
    "expectedFactoryRoot", "expectedAuthorityRoot", "key"] json
  let command : ParticipantKeyEnrollment.Command :=
    { sponsor := ⟨← nat "$.sponsor" (← field "$" "sponsor" obj)⟩
      control := ⟨← nat "$.control" (← field "$" "control" obj)⟩
      nonce := ← nat "$.nonce" (← field "$" "nonce" obj)
      expectedFactoryRoot := ⟨← nat "$.expectedFactoryRoot"
        (← field "$" "expectedFactoryRoot" obj)⟩
      expectedAuthorityRoot := ⟨← nat "$.expectedAuthorityRoot"
        (← field "$" "expectedAuthorityRoot" obj)⟩
      key := ← keyRecord "$.key" (← field "$" "key" obj) }
  return ParticipantKeyEnrollment.commandCodec.encode command

/-- Encode an operator's chosen issue, role and capability selectors. -/
private def sessionEnrollmentRequest (json : Lean.Json) : Result (List UInt8) := do
  let obj ← exactObject "$"
    ["issueIndex", "ticketResource", "packageManifest", "role",
     "descriptorCapability", "sessionObserveCapability",
     "descriptorObserveCapability", "manifestObserveCapability", "nonce"] json
  let request : ApplicationGrainSessionEnrollmentSource.Request :=
    ⟨← nat "$.issueIndex" (← field "$" "issueIndex" obj),
     ← nat "$.ticketResource" (← field "$" "ticketResource" obj),
     ← nat "$.packageManifest" (← field "$" "packageManifest" obj),
     ← shareIssueRole "$.role" (← field "$" "role" obj),
     ⟨← nat "$.descriptorCapability" (← field "$" "descriptorCapability" obj)⟩,
     ⟨← nat "$.sessionObserveCapability" (← field "$" "sessionObserveCapability" obj)⟩,
     ⟨← nat "$.descriptorObserveCapability" (← field "$" "descriptorObserveCapability" obj)⟩,
     ⟨← nat "$.manifestObserveCapability" (← field "$" "manifestObserveCapability" obj)⟩,
     ← nat "$.nonce" (← field "$" "nonce" obj)⟩
  pure <| ApplicationGrainSessionEnrollmentSource.requestCodec.encode request

/-- Author JSON into source-owned canonical bytes. -/
def author (kind : String) (json : Lean.Json)
    (deployed : Option NativeHost.Config := none) : Result (List UInt8) :=
  match kind with
  | "application-lifecycle-resident-begin" => residentBegin json
  | "application-lifecycle-completion-report" => completionReport json
  | "application-lifecycle-completion-signing-frame" => completionSigningFrame json
  | "application-lifecycle-completion-signed-report" => completionSignedReport json
  | "application-lifecycle-launch-physical-report" => launchPhysicalReport json
  | "application-lifecycle-launch-physical-signing-frame" => launchPhysicalSigningFrame json
  | "application-lifecycle-launch-physical-signed-report" => launchPhysicalSignedReport json
  | "application-lifecycle-completion-source" => completionSource json
  | "application-lifecycle-completion-command" => completionCommand json
  | "application-lifecycle-completion-signed-command" => completionSignedCommand json
  | "application-lifecycle-completion-ingress" => completionIngress json
  | "application-lifecycle-completion-operator-request" => completionOperatorRequest json
  | "application-lifecycle-resident-begin-operator-request" => residentBeginOperatorRequest json
  | "application-lifecycle-launch-begin-request" => launchBeginOperatorRequest json
  | "application-lifecycle-launch-continue-request" => launchContinueOperatorRequest json
  | "application-lifecycle-launch-claim-request" => launchClaimOperatorRequest json
  | "application-lifecycle-launch-completion-request" => launchCompletionOperatorRequest json
  | "application-lifecycle-claim-operator-request" => lifecycleClaimOperatorRequest json
  | "application-spk-package-identity" => applicationSpkPackageIdentity json
  | "participant-key-enrollment" => participantKeyEnrollment json
  | "application-spk-launch-descriptor" =>
      (ApplicationSpkLaunchDescriptorAuthoring.author json).map Prod.fst
  | "application-dispatch-request" => dispatchAuthorRequest json
  | "application-agent-reserve-request" => agentPaidReserveRequest json
  | "application-agent-paid-request" => agentPaidRequest json
  | "application-agent-lifetime-reserve-request" => agentLifetimeReserveRequest json
  | "application-agent-lifetime-paid-request" => agentLifetimePaidRequest json
  | "application-share-issue-request" => shareIssueRequest json
  | "application-share-issue-grain-request" => grainShareIssueRequest json
  | "application-agent-lifetime-grant-request" => agentLifetimeGrantRequest json
  | "application-session-enrollment-request" => sessionEnrollmentRequest json
  | "predicate" => NativeHostGenesis.predicateStream.encode <$> predicate "$" json
  | "grain-policy" => do
      let raw ← object "$" json
      let worker ← grainWorker "$" raw
      let obj ← exactObject "$" (["owner"] ++
        if worker.isSome then grainWorkerFields raw else []) json
      let owner ← nat "$.owner" (← field "$" "owner" obj)
      pure (NativeHostGenesis.predicateStream.encode (grainPolicy owner worker))
  | "grain-caveat" => do
      let obj ← exactObject "$" ["generation"] json
      let generation ← int "$.generation" (← field "$" "generation" obj)
      pure (NativeHostGenesis.predicateStream.encode (AgentGrain.executionCaveat generation))
  | "policy" => PolicyRecordCodec.encode <$> policyRecord "$" json
  | "policy-install" => PolicyInstallController.declarationCodec.encode <$> policyInstall "$" json
  | "policy-install-draft" => draftCodec.encode <$> policyInstallDraft "$" json
  | "delegation" => delegation "$" json
  | "delegation-draft" => do
      let bytes ← delegation "$" json
      pure (draftCodec.encode (.delegate bytes))
  | "revocation" => revocation "$" json
  | "revocation-draft" => do
      let bytes ← revocation "$" json
      pure (draftCodec.encode (.revoke bytes))
  | "birth" => draftCodec.encode <$> birth "$" json none deployed
  | "birth-intent" => intentCodec.encode <$> birthIntent "$" json deployed
  | "application-birth" => draftCodec.encode <$> applicationBirth "$" json none deployed
  | "application-birth-intent" => intentCodec.encode <$> applicationBirthIntent "$" json deployed
  | "application-session-birth" => draftCodec.encode <$> applicationSessionBirth "$" json none deployed
  | "application-session-birth-intent" => intentCodec.encode <$> applicationSessionBirthIntent "$" json deployed
  | "application-grain-birth-intent" => intentCodec.encode <$> applicationGrainBirthIntent "$" json deployed
  | "application-session-grain-birth-intent" =>
      intentCodec.encode <$> applicationSessionGrainBirthIntent "$" json deployed
  | "application-permission-schema" => do
      pure (← ApplicationPermissionSchemaAuthoring.author json).1
  | "grain-birth" => draftCodec.encode <$> grainBirth "$" json deployed
  | "grain-birth-intent" => intentCodec.encode <$> grainBirthIntent "$" json deployed
  | "content" => ContentResource.commandCodec.encode <$> contentCommand "$" json
  | "resource" | "joint" => DeclaredResourceController.commandCodec.encode <$> command "$" json
  | "joint-draft" => do
      let source ← command "$" json
      pure (draftCodec.encode (.invoke (DeclaredResourceController.commandCodec.encode source)))
  | "grain" => do
      let source ← grainSource "$" json
      pure (DeclaredResourceController.commandCodec.encode source.1)
  | "grain-intent" => intentCodec.encode <$> grainIntent "$" json
  | "grain-policy-install-intent" => intentCodec.encode <$> grainPolicyInstallIntent "$" json
  | "draft" => draftCodec.encode <$> draft "$" json
  | "intent" => intentCodec.encode <$> intent "$" json
  | "genesis" => NativeHostGenesis.configCodec.encode <$> genesis "$" json
  | _ => failAt "kind"
      "expected predicate, grain-policy, grain-caveat, grain-policy-install-intent, policy, policy-install[-draft], delegation[-draft], revocation[-draft], birth, grain-birth[-intent], application-birth[-intent], application-session-birth[-intent], application-grain-birth-intent, application-session-grain-birth-intent, application-permission-schema, application-spk-launch-descriptor, content, resource, joint[-draft], grain[-intent], draft, intent, or genesis"

private def authorRefused (kind : String) (value : Lean.Json) : Bool :=
  match author kind value with
  | .error _ => true
  | .ok _ => false

/-- Negative authoring checks run through the same exact JSON parser used by
native requests. Duplicate and overbound examples use the compiled evaluator;
the mixed-form example is kernel-decided. Their printed axioms disclose that
distinction, and none are used to prove the general policy theorems. -/
theorem grainPolicy_duplicate_workers_refused :
    authorRefused "grain-policy" (.mkObj [
      ("owner", .str "7"), ("workerSubjects", .arr #[.str "8", .str "8"]),
      ("workerGeneration", .str "1")]) = true := by native_decide

theorem grainPolicy_overbound_workers_refused :
    authorRefused "grain-policy" (.mkObj [
      ("owner", .str "7"), ("workerSubjects", .arr #[.str "8", .str "9",
        .str "10", .str "11", .str "12"]),
      ("workerGeneration", .str "1")]) = true := by native_decide

theorem grainPolicy_mixed_worker_forms_refused :
    authorRefused "grain-policy" (.mkObj [
      ("owner", .str "7"), ("workerSubject", .str "8"),
      ("workerSubjects", .arr #[.str "8", .str "9"]),
      ("workerGeneration", .str "1")]) = true := by decide

#print axioms grainPolicy_duplicate_workers_refused
#print axioms grainPolicy_overbound_workers_refused
#print axioms grainPolicy_mixed_worker_forms_refused

/-- Source-derived, non-authoritative presentation data. This lets clients
display the resulting grain generation/state without duplicating the state
machine; admission remains the receiver's decision. -/
def derive (kind : String) (json : Lean.Json) : Result Lean.Json :=
  match kind with
  | "grain" => do
      let source ← grainSource "$" json
      let state := source.2
      pure <| .mkObj [("generation", signedDecimal state.generation),
        ("status", signedDecimal state.status), ("remaining", signedDecimal state.remaining),
        ("reserved", signedDecimal state.reserved),
        ("command", hexJson (DeclaredResourceController.commandCodec.encode source.1))]
  | _ => failAt "kind" "expected grain"

/-- Detached Ed25519 signatures use the sole strict list-of-bytes codec. -/
def signatures (json : Lean.Json) : Result (List UInt8) := do
  let values ← list "$" decodeHex json
  for signature in values do
    unless signature.length = 64 do throw "$: every signature must contain exactly 64 bytes"
  pure <| (ResourceBirthCodec.strictCodec (StreamCodec.list bytesStream).toLawful).encode values

private def draftJson : Draft → Lean.Json
  | .birth bytes capabilities =>
      if let some finalized := GrainResourceBirthHostCodec.finalizedCodec.decode bytes then
        .mkObj [("type", "grain-birth-finalized"),
          ("source", hexJson finalized.sourceBytes),
          ("command", hexJson finalized.commandBytes),
          ("sourceCapabilities", .arr <| capabilities.toArray.map fun c => decimal c.value)]
      else if (GrainResourceBirthHostCodec.sourceCodec.decode bytes).isSome then
        .mkObj [("type", "grain-birth"), ("source", hexJson bytes),
          ("sourceCapabilities", .arr <| capabilities.toArray.map fun c => decimal c.value)]
      else
        .mkObj [("type", "birth"), ("descriptor", hexJson bytes),
          ("sourceCapabilities", .arr <| capabilities.toArray.map fun c => decimal c.value)]
  | .invoke bytes => .mkObj [("type", "invoke"), ("command", hexJson bytes)]
  | .install subject control bytes => .mkObj [("type", "install"), ("subject", decimal subject.value),
      ("control", decimal control.value), ("declaration", hexJson bytes)]
  | .delegate bytes => .mkObj [("type", "delegate"), ("command", hexJson bytes)]
  | .revoke bytes => .mkObj [("type", "revoke"), ("command", hexJson bytes)]

/-- The plan's authority footprint as (address, value) pairs, both as canonical
hex (value `null` = absent): the values the signature binds. -/
def footprintJson (bytes : List UInt8) : Lean.Json :=
  match PlanFootprintCodec.decode CredentialAuthorityCell.wire bytes with
  | none => .mkObj [("canonical", hexJson bytes), ("decoded", false)]
  | some reads => .arr <| reads.toArray.map fun read => .mkObj
      [("address", hexJson (PlanFootprintCodec.addressBytes CredentialAuthorityCell.wire read.address)),
       ("value", match read.observed with
         | none => .null
         | some value => hexJson ((CredentialAuthorityCell.wire.valueStream read.address.1).encode value))]

private def signedHeaderJson (bytes : List UInt8) : Lean.Json :=
  match CredentialSignedEnvelopeController.headerCodec.decode bytes with
  | none => .mkObj [("canonical", hexJson bytes), ("decoded", false)]
  | some header => .mkObj
      [("canonical", hexJson bytes), ("decoded", true),
       ("codecVersion", decimal header.codecVersion),
       ("footprint", footprintJson header.footprint),
       ("validUntil", decimal header.validUntil),
       ("keyId", decimal header.keyId), ("keyEpoch", decimal header.keyEpoch),
       ("algorithm", decimal header.algorithm), ("domain", hexJson header.domain),
       ("message", hexJson header.message), ("nullifier", decimal header.nullifier)]

private def participantKeyRecordJson (key : KeyRecord) : Lean.Json := .mkObj
  [("keyId", decimal key.keyId), ("keyEpoch", decimal key.keyEpoch),
   ("algorithm", decimal key.algorithm), ("subject", decimal key.subject),
   ("publicKey", hexJson key.publicKey),
   ("activeFrom", decimal key.activeFrom),
   ("activeUntil", decimal key.activeUntil)]

private def participantKeyCommandJson
    (command : ParticipantKeyEnrollment.Command) : Lean.Json := .mkObj
  [("type", "participant-key-enrollment-v1"),
   ("canonical", hexJson (ParticipantKeyEnrollment.commandCodec.encode command)),
   ("sponsor", decimal command.sponsor.value),
   ("control", decimal command.control.value),
   ("nonce", decimal command.nonce),
   ("expectedFactoryRoot", decimal command.expectedFactoryRoot.value),
   ("expectedAuthorityRoot", decimal command.expectedAuthorityRoot.value),
   ("key", participantKeyRecordJson command.key)]

private def planJson (plan : SigningPlan) : Lean.Json := .mkObj
  [("domain", decimal plan.domain.value), ("semantics", decimal plan.semantics.value),
   ("worldRoot", decimal plan.worldRoot.value), ("height", decimal plan.height),
   ("finalizedDraft", draftJson plan.finalizedDraft),
   ("slots", .arr <| plan.slots.toArray.map fun slot => .mkObj
     [("role", decimal slot.role), ("index", decimal slot.index),
      ("header", hexJson slot.header), ("signing", signedHeaderJson slot.header)])]

/-- Custody presentation of a composite share-issue plan. Every signing header
is exposed in its exact order; this presentation does not authorize signing. -/
private def shareIssuePlanJson
    (plan : ApplicationShareIssueAuthoring.Plan) : Lean.Json :=
  let ticket := plan.request.spec.ticket
  let scope := ticket.scope
  let participant := ticket.participant
  let slotJson := fun (slot : SigningSlot) => .mkObj
    [("role", decimal slot.role), ("index", decimal slot.index),
     ("header", hexJson slot.header), ("signing", signedHeaderJson slot.header)]
  .mkObj
    [("type", "application-share-issue-plan-v2"),
     ("canonicalRequest", hexJson (ApplicationShareIssueAuthoring.requestCodec.encode plan.request)),
     ("canonicalSpec", hexJson (ApplicationShareIssueSource.specCodec.encode plan.request.spec)),
     ("spec", .mkObj
       [("issuer", decimal plan.request.spec.issuer.value),
        ("appDelegateCapability", decimal plan.request.spec.appDelegateCapability.value),
        ("ticketOwnerCapability", decimal plan.request.spec.ticketOwnerCapability.value),
        ("ticketControlCapability", decimal plan.request.spec.ticketControlCapability.value),
        ("ticket", .mkObj
          [("canonical", hexJson (ApplicationDispatchAuthority.ticketCodec.encode ticket)),
           ("resource", decimal ticket.resource),
           ("issueNonce", decimal ticket.issueNonce),
           ("scope", .mkObj
             [("app", decimal scope.app), ("packageVersion", signedDecimal scope.packageVersion),
              ("packageRoot", decimal scope.packageRoot.value),
              ("interfaceId", decimal scope.interfaceId),
              ("interfaceVersion", decimal scope.interfaceVersion),
              ("interfaceRoot", decimal scope.interfaceRoot.value),
              ("schemaRoot", decimal scope.schemaRoot.value),
              ("schemaVersion", decimal scope.schemaVersion)]),
           ("participant", .mkObj
             [("session", decimal participant.session),
              ("descriptorResource", decimal participant.descriptorResource),
              ("subject", decimal participant.subject.value),
              ("sessionCapability", decimal participant.sessionCapability.value),
              ("appObserveCapability", decimal participant.appObserveCapability.value),
              ("ticketObserveCapability", decimal participant.ticketObserveCapability.value)])])]),
     ("birth", planJson plan.birth),
     ("appSlot", slotJson plan.appSlot),
     ("slots", .arr <| (plan.birth.slots ++ [plan.appSlot]).toArray.map slotJson)]

/-- The same source codec supplies both custody projections. Comparing these
canonical spec bytes binds all ticket fields, including origin and ceiling,
without a second ticket codec in the client. -/
private def shareIssueRequestJson
    (request : ApplicationShareIssueAuthoring.Request) : Lean.Json :=
  .mkObj
    [("type", "application-share-issue-request-v1"),
     ("canonicalRequest", hexJson (ApplicationShareIssueAuthoring.requestCodec.encode request)),
     ("canonicalSpec", hexJson (ApplicationShareIssueSource.specCodec.encode request.spec)),
     ("payer", decimal request.payer),
     ("funding", .arr <| request.funding.toArray.map fun item => .mkObj
       [("source", decimal item.source), ("destination", decimal item.destination),
        ("asset", decimal item.asset), ("amount", decimal item.amount)]),
     ("sourceCapabilities", .arr <| request.sourceCapabilities.toArray.map
       (fun capability => decimal capability.value))]

private def dispatchRequestJson
    (request : ApplicationDispatchAuthoring.Request) : Lean.Json :=
  let http := request.http
  .mkObj
    [("type", "application-dispatch-author-request-v1"),
     ("canonicalRequest", hexJson <| ApplicationDispatchAuthoring.requestCodec.encode request),
     ("issueIndex", decimal request.issueIndex),
     ("ticketResource", decimal request.ticketResource),
     ("packageManifest", decimal request.packageManifest),
     ("snapshotManifest", decimal request.snapshotManifest),
     ("sessionObserveCapability", decimal request.sessionObserveCapability.value),
     ("manifestObserveCapability", decimal request.manifestObserveCapability.value),
     ("enrollmentObserveCapability", decimal request.enrollmentObserveCapability.value),
     ("http", .mkObj
       [("operationId", decimal http.operationId),
        ("methodHex", hexJson http.method),
        ("pathHex", hexJson http.path),
        ("queryHex", hexJson http.query),
        ("headers", .arr <| http.headers.toArray.map fun header => .mkObj
          [("nameHex", hexJson header.name),
           ("valueHex", hexJson header.value),
           ("generated", .bool header.generated)]),
        ("bodyHex", hexJson http.body)])]

private def agentPaidReserveRequestJson
    (request : ApplicationDispatchAgentPaidAuthoring.Request) : Lean.Json :=
  .mkObj
    [("type", "application-agent-reserve-request-v2"),
     ("canonicalRequestHex", hexJson <|
       ApplicationDispatchAgentPaidAuthoring.requestCodec.encode request),
     ("base", dispatchRequestJson request.base.base),
     ("parentTask", decimal request.base.task),
     ("parentCapability", decimal request.base.parentCapability.value),
     ("parentObserve", decimal request.base.parentObserveCapability.value),
     ("purseTask", decimal request.purseTask),
     ("purseCapability", decimal request.purseCapability.value),
     ("purseObserve", decimal request.purseObserve.value),
     ("payerSubject", decimal request.payerSubject.value),
     ("reserveAmount", signedDecimal request.reserveAmount),
     ("maximumCharge", signedDecimal request.maximumCharge),
     ("reserveOperationId", decimal request.reserveOperationId),
     ("httpRequestDigest", decimal <|
       (ApplicationDispatchCodec.requestDigest request.base.base.http).value)]

private def agentPaidRequestJson
    (request : ApplicationDispatchAgentPaidAuthoring.PaidRequest) : Lean.Json :=
  let context := request.context
  .mkObj
    [("type", "application-agent-paid-request-v2"),
     ("canonicalRequestHex", hexJson <|
       ApplicationDispatchAgentPaidAuthoring.paidRequestCodec.encode request),
     ("fixed", agentPaidReserveRequestJson request.fixed),
     ("canonicalContextHex", hexJson context.canonicalBytes),
     ("reserveIndex", decimal request.reserveIndex),
     ("appResource", decimal context.app.resource),
     ("appGeneration", signedDecimal context.app.generation),
     ("sessionResource", decimal context.session.resource),
     ("sessionGeneration", signedDecimal context.session.generation),
     ("ticketResource", decimal context.ticketResource),
     ("ticketRoot", decimal context.ticketRoot.value),
     ("parentTask", decimal context.parentTask),
     ("parentGeneration", signedDecimal context.parentGeneration),
     ("purseTask", decimal context.purseTask),
     ("purseGeneration", signedDecimal context.purseGeneration),
     ("payerSubject", decimal context.payerSubject.value),
     ("reserveAmount", signedDecimal context.reserveAmount),
     ("maximumCharge", signedDecimal context.maximumCharge),
     ("reserveOperationId", decimal context.reserveOperationId),
     ("httpOperationId", decimal context.httpOperationId),
     ("httpRequestDigest", decimal context.requestDigest.value)]

private def agentLifetimePaidRequestJson
    (bytes : List UInt8)
    (request : ApplicationAgentLifetimeDispatchPaidAuthoring.PaidRequest) : Result Lean.Json := do
  let fixed ← ApplicationAgentLifetimeDispatchPaidInspection.inspectRequest
    (ApplicationAgentLifetimeDispatchPaidAuthoring.requestCodec.encode request.fixed)
  pure <| .mkObj
    [("type", "application-agent-lifetime-paid-request-v3"),
     ("canonicalRequestHex", hexJson bytes),
     ("fixed", fixed),
     ("contextHex", hexJson <| ApplicationAgentLifetimeDispatchReserveContext.codec.encode
       request.context),
     ("reserveIndex", decimal request.reserveIndex)]

/-- Presentation of the complete detached challenge. It repeats the exact
canonical request and ordered signing headers but confers no authority; op34
independently re-admits the assembled ingress at the current verified tip. -/
private def dispatchPlanJson (plan : ApplicationDispatchAuthoring.Plan) :
    Result Lean.Json := do
  let some unsigned := ApplicationDispatchAdmissionIngress.codec.decode plan.unsignedIngress
    | failAt "application-dispatch-plan" "noncanonical unsigned ingress"
  let slotJson := fun (slot : SigningSlot) => .mkObj
    [("role", decimal slot.role), ("index", decimal slot.index),
     ("header", hexJson slot.header), ("signing", signedHeaderJson slot.header)]
  let dispatch := unsigned.dispatch.dispatch
  pure <| .mkObj
    [("type", "application-dispatch-author-plan-v1"),
     ("canonicalPlan", hexJson <| ApplicationDispatchAuthoring.planCodec.encode plan),
     ("request", dispatchRequestJson plan.request),
     ("unsignedIngress", hexJson plan.unsignedIngress),
     ("domain", decimal plan.invocation.domain.value),
     ("semantics", decimal plan.invocation.semantics.value),
     ("worldRoot", decimal plan.invocation.worldRoot.value),
     ("height", decimal plan.invocation.height),
     ("appResource", decimal dispatch.app.resource),
     ("appGeneration", signedDecimal dispatch.app.generation),
     ("sessionResource", decimal dispatch.session.resource),
     ("sessionGeneration", signedDecimal dispatch.session.generation),
     ("subject", decimal dispatch.session.subject.value),
     ("principalHex", hexJson dispatch.identity.principal),
     ("permissionSchemaRoot", decimal dispatch.identity.permissionSchemaRoot.value),
     ("permissionBits", decimal dispatch.identity.permissionBits),
     ("slots", .arr <|
     (plan.invocation.slots ++ plan.observationSlots).toArray.map slotJson)]

private def completionOperatorPlanJson
    (plan : ApplicationLifecycleCompletionOperator.Plan) : Result Lean.Json := do
  let some source := ApplicationLifecycleCompletionSource.codec.decode plan.sourceBytes
    | failAt "application-lifecycle-completion-operator-plan"
        "noncanonical completion source"
  let slotJson := fun (slot : SigningSlot) => .mkObj
    [("role", decimal slot.role), ("index", decimal slot.index),
     ("header", hexJson slot.header), ("signing", signedHeaderJson slot.header)]
  let command := source.command plan.invocation.domain plan.invocation.semantics
  pure <| .mkObj
    [("type", "application-lifecycle-completion-operator-plan-v1"),
     ("canonicalPlan", hexJson <| ApplicationLifecycleCompletionOperator.planCodec.encode plan),
     ("source", hexJson plan.sourceBytes),
     ("command", hexJson <| DeclaredResourceController.commandCodec.encode command),
     ("domain", decimal plan.invocation.domain.value),
     ("semantics", decimal plan.invocation.semantics.value),
     ("worldRoot", decimal plan.invocation.worldRoot.value),
     ("height", decimal plan.invocation.height),
     ("app", decimal source.app),
     ("packageManifest", decimal source.originalBegin.base.source.packageManifest),
     ("managementSubject", decimal command.subject.value),
     ("physicalNonce", decimal source.physical.report.nonce),
     ("claimTransaction", decimal
        source.physical.report.claim.core.claimReceipt.transactionId.value),
     ("slots", .arr <| (plan.invocation.slots ++
        [plan.packageObservationSlot]).toArray.map slotJson)]

private def residentBeginOperatorPlanJson
    (plan : ApplicationLifecycleBeginOperator.Plan) : Result Lean.Json := do
  let some source := ApplicationLifecycleBegin.sourceCodec.decode plan.sourceBytes
    | failAt "application-lifecycle-resident-begin-operator-plan"
        "noncanonical resident BEGIN source"
  let some descriptor := ApplicationSpkPackageIdentity.decodeCanonical plan.descriptorBytes
    | failAt "application-lifecycle-resident-begin-operator-plan"
        "noncanonical signed-SPK descriptor"
  let slotJson := fun (slot : SigningSlot) => .mkObj
    [("role", decimal slot.role), ("index", decimal slot.index),
     ("header", hexJson slot.header), ("signing", signedHeaderJson slot.header)]
  pure <| .mkObj
    [("type", "application-lifecycle-resident-begin-operator-plan-v1"),
     ("canonicalPlan", hexJson <| ApplicationLifecycleBeginOperator.planCodec.encode plan),
     ("source", hexJson plan.sourceBytes),
     ("descriptor", hexJson plan.descriptorBytes),
     ("domain", decimal plan.invocation.domain.value),
     ("semantics", decimal plan.invocation.semantics.value),
     ("worldRoot", decimal plan.invocation.worldRoot.value),
     ("height", decimal plan.invocation.height),
     ("kind", (match source.kind with
       | .install => "install" | .start => "start"
       | .stop => "stop" | .upgrade => "upgrade")),
     ("app", decimal source.app),
     ("packageManifest", decimal source.packageManifest),
     ("snapshotManifest", decimal source.snapshotManifest),
     ("operationId", decimal source.operationId),
     ("managementSubject", decimal source.managementSubject.value),
     ("beforeGeneration", signedDecimal source.before.generation),
     ("beforePhase", signedDecimal source.before.phase),
     ("beforePackageVersion", signedDecimal source.before.packageVersion),
     ("processGeneration", signedDecimal source.processGeneration),
     ("processIdentity", hexJson source.processIdentity),
     ("imageIdentity", hexJson source.imageIdentity),
     ("descriptorRoot", decimal descriptor.root.value),
     ("slots", .arr <| (plan.invocation.slots ++
        [plan.packageObservationSlot]).toArray.map slotJson)]

private def lifecycleClaimOperatorPlanJson
    (plan : ApplicationLifecycleClaimOperator.Plan) : Result Lean.Json := do
  let some source := ApplicationLifecycleClaim.codec.decode plan.sourceBytes
    | failAt "application-lifecycle-claim-operator-plan" "noncanonical claim source"
  let some begin := ApplicationLifecycleBeginV2Ingress.codec.decode plan.originalBeginBytes
    | failAt "application-lifecycle-claim-operator-plan" "noncanonical original BEGIN"
  let slotJson := fun (slot : SigningSlot) => .mkObj
    [("role", decimal slot.role), ("index", decimal slot.index),
     ("header", hexJson slot.header), ("signing", signedHeaderJson slot.header)]
  pure <| .mkObj
    [("type", "application-lifecycle-claim-operator-plan-v1"),
     ("canonicalPlan", hexJson <| ApplicationLifecycleClaimOperator.planCodec.encode plan),
     ("source", hexJson plan.sourceBytes),
     ("originalBegin", hexJson plan.originalBeginBytes),
     ("descriptor", hexJson begin.descriptor.canonicalBytes),
     ("domain", decimal plan.invocation.domain.value),
     ("semantics", decimal plan.invocation.semantics.value),
     ("worldRoot", decimal plan.invocation.worldRoot.value),
     ("height", decimal plan.invocation.height),
     ("app", decimal source.begin.source.app),
     ("originalIndex", decimal source.originalIndex),
     ("queryNonce", decimal source.queryNonce),
     ("managementSubject", decimal source.begin.source.managementSubject.value),
     ("beforeGeneration", signedDecimal source.before.generation),
     ("beforePhase", signedDecimal source.before.phase),
     ("currentAppRoot", decimal source.currentAppRoot.value),
     ("currentPackageRoot", decimal source.currentPackageRoot.value),
     ("currentWorldRoot", decimal source.currentWorldRoot.value),
     ("slots", .arr <| (plan.invocation.slots ++
        [plan.appObservationSlot, plan.packageObservationSlot]).toArray.map slotJson)]

private def applicationSpkPackageIdentityJson
    (descriptor : ApplicationSpkPackageIdentity.Descriptor) : Result Lean.Json := do
  unless descriptor.valid do
    failAt "application-spk-package-identity" "invalid descriptor or bridge mapping"
  let interfaces := descriptor.interfaces.toArray.map fun interface => .mkObj
    [("id", decimal interface.id),
     ("version", decimal interface.version),
     ("kind", match interface.kind with | .web => "web" | .api => "api"),
     ("canonical", hexJson <| ApplicationDispatchManifest.interfaceCodec.encode interface),
     ("root", decimal interface.root.value),
     ("schemaRoot", decimal interface.schema.root.value),
     ("schema", hexJson <| ApplicationPermissionSchema.schemaCodec.encode interface.schema)]
  pure <| .mkObj
    [("type", if descriptor.legacyProfile then
        "application-spk-package-identity-v1" else
        "application-spk-package-identity-v2"),
     ("canonical", hexJson descriptor.canonicalBytes),
     ("root", decimal descriptor.root.value),
     ("imageIdentity", hexJson descriptor.imageIdentity),
     ("rawSha256", hexJson descriptor.rawSha256),
     ("rawLength", decimal descriptor.rawLength),
     ("rawShaDigest", decimal descriptor.rawShaDigest.value),
     ("signedAppId", hexJson descriptor.signedAppId),
     ("signedAppVersion", decimal descriptor.signedAppVersion),
     ("manifestSha256", hexJson descriptor.manifestSha256),
     ("bridgeConfigSha256", hexJson descriptor.bridgeConfigSha256),
     ("bridgeApiPath", hexJson descriptor.bridgeApiPath),
     ("interfaces", .arr interfaces)]

private def intentJson (value : Intent) : Lean.Json := .mkObj
  [("subject", decimal value.subject.value), ("nonce", decimal value.nonce),
   ("purpose", match value.purpose with
     | .prepare d => .mkObj [("type", "prepare"), ("draft", draftJson d)]
     | .query q => Lean.Json.mkObj (([("type", "query"),
       ("kind", match q.kind with | .object => "object" | .account => "account" | .program => "program"),
       ("target", decimal q.target),
       ("view", match q.view with
         | .resource => "resource" | .policy => "policy" | .capability => "capability"
         | .who => "who" | .since _ => "since" | .atHeight _ => "at")] : List (String × Lean.Json)) ++
       (match q.view with | .since h | .atHeight h => [("height", decimal h)] | _ => []))),
   ("grants", .arr <| value.grants.toArray.map fun g => .mkObj
     [("kind", match g.kind with | .object => "object" | .account => "account" | .program => "program"),
      ("target", decimal g.target), ("capability", decimal g.capability.value)])]

private def challengeJson (value : Challenge) : Lean.Json := .mkObj
  [("intent", intentJson value.intent), ("domain", decimal value.domain.value),
   ("semantics", decimal value.semantics.value), ("federation", decimal value.federation.value),
   ("worldRoot", decimal value.worldRoot.value),
   ("authorityRoot", decimal value.authorityRoot.value), ("height", decimal value.height),
   ("headers", .arr <| value.headers.toArray.map hexJson),
   ("signing", .arr <| value.headers.toArray.map signedHeaderJson)]

private def outcomeJson : Outcome → Lean.Json
  | .confirmed kind receipt =>
      let confirmation : Lean.Json := match kind with
        | .installed => "installed"
        | .recoveredAfterUncertainResponse => "recoveredAfterUncertainResponse"
        | .replayed => "replayed"
      .mkObj [("type", "confirmed"), ("confirmation", confirmation),
      ("transactionId", decimal receipt.transactionId.value), ("eventId", decimal receipt.eventId.value),
      ("acceptedCount", decimal receipt.acceptedCount), ("worldRoot", decimal receipt.worldRoot.value)]
  | .refused phase detail => .mkObj [("type", "refused"), ("phase", hexJson phase), ("detail", hexJson detail)]
  | .contention => .mkObj [("type", "contention")]
  | .unavailable detail => .mkObj [("type", "unavailable"), ("detail", hexJson detail)]
  | .uncertain detail => .mkObj [("type", "uncertain"), ("detail", hexJson detail)]
  | .absent => .mkObj [("type", "absent")]

private def stateKeyJson : Minidregg.Theory.EffectDeclaration.StateKey → Lean.Json
  | .objectField resource field => .mkObj [("type", "object"),
      ("resource", decimal resource.value), ("field", decimal field.value)]
  | .accountBalance account resource => .mkObj [("type", "account"),
      ("resource", decimal account.value), ("field", decimal resource.value)]
  | .programCode resource => .mkObj [("type", "program"),
      ("resource", decimal resource.value)]

private def declaredCellJson (root : Digest)
    (store : Store.Store EffectDeclaration.effectLayout) : Lean.Json :=
  let entries := StoreCodec.entries DeclaredEffectCell.wire store
  let base := [("root", decimal root.value),
    ("entries", .arr <| entries.toArray.map fun entry => .mkObj
      [("key", stateKeyJson entry.1.2), ("value", signedDecimal (entry.2 : Int))])]
  let grain := entries.findSome? fun entry => match entry.1.2 with
    | .objectField task field => if field.value = 0 then some task.value else none
    | _ => none
  match grain with
  | none => .mkObj base
  | some task => match AgentGrain.readState task store with
    | none => .mkObj base
    | some state => .mkObj <| base ++ [("grain", .mkObj
        [("task", decimal task), ("generation", signedDecimal state.generation),
         ("status", signedDecimal state.status), ("remaining", signedDecimal state.remaining),
         ("reserved", signedDecimal state.reserved)])]

private def principalJson (value : Hyperdocument.PrincipalRef) : Lean.Json := .mkObj
  [("subject", decimal value.subject.value),
   ("capabilityKind", match value.capabilityKind with
     | .object => "object" | .account => "account" | .program => "program"),
   ("capability", decimal value.capabilityId.value)]

private def atomKindJson : Hyperdocument.AtomKind → Lean.Json
  | .text => .mkObj [("type", "text")]
  | .inlineObject schema => .mkObj [("type", "inlineObject"), ("schema", decimal schema.value)]

private def optionalOperationJson (value : Option Hyperdocument.OperationId) : Lean.Json :=
  value.map (fun id => decimal id.digest.value) |>.getD .null

private def modeJson : Hyperdocument.TransclusionMode → Lean.Json
  | .snapshot => "snapshot"
  | .live => "live"

private def biasJson : Hyperdocument.AnchorBias → Lean.Json
  | .before => "before"
  | .after => "after"

private def deathJson : Hyperdocument.EndpointDeathPolicy → Lean.Json
  | .invalidate => "invalidate"
  | .keepTombstone => "keepTombstone"
  | .preferPrevious => "preferPrevious"
  | .preferNext => "preferNext"
  | .preferPreviousThenNext => "preferPreviousThenNext"
  | .preferNextThenPrevious => "preferNextThenPrevious"

private def stablePointJson (point : Hyperdocument.StablePoint) : Lean.Json :=
  .mkObj [("run", decimal point.run.digest.value),
    ("neighbor", (point.neighbor.map fun atom => decimal atom.digest.value).getD .null),
    ("bias", biasJson point.bias), ("death", deathJson point.death)]

/-- The opening a transclusion record carries: source cell, range, pinned
atoms at their revisions, and the height; never bytes. -/
private def openingJson (opening : ContentResource.RangeOpening) : Lean.Json :=
  .mkObj [("source", decimal opening.source),
    ("range", .mkObj [("start", stablePointJson opening.range.start),
      ("finish", stablePointJson opening.range.finish)]),
    ("pins", .arr <| opening.pins.toArray.map fun pin =>
      .mkObj [("atom", decimal pin.1.digest.value), ("revision", decimal pin.2.digest.value)]),
    ("atoms", decimal opening.pins.length), ("height", decimal opening.height)]

private def transclusionRecordJson (record : Hyperdocument.TransclusionRecord) : List (String × Lean.Json) :=
  [("host", decimal record.hostDocument.digest.value),
   ("mode", modeJson record.reference.mode),
   ("opening", ((ContentResource.openingOfReference record.reference).map openingJson).getD .null),
   ("reference", decimal record.reference.referenceRoot.value),
   ("disclosurePolicy", decimal record.disclosurePolicy.value)]

private def elementBodyJson : Hyperdocument.ElementBody → Lean.Json
  | .container children => .mkObj [("type", "container"),
      ("children", .arr <| children.toArray.map fun child => decimal child.digest.value)]
  | .runs runs => .mkObj [("type", "runs"),
      ("runs", .arr <| runs.toArray.map fun run => decimal run.digest.value)]
  | .embed transclusion => .mkObj [("type", "embed"),
      ("transclusion", decimal transclusion.digest.value)]
  | .opaque schema payload => .mkObj [("type", "opaque"), ("schema", decimal schema.value),
      ("payload", hexJson payload)]

private def annotationAnchorJson : Hyperdocument.AnnotationAnchor → Lean.Json
  | .document => .mkObj [("type", "document")]
  | .range _ => .mkObj [("type", "range")]
  | .atom atom revision => .mkObj [("type", "atom"), ("atom", decimal atom.digest.value),
      ("revision", decimal revision.digest.value)]

private def annotationBodyJson : Hyperdocument.AnnotationBody → Lean.Json
  | .inline bytes => .mkObj [("type", "inline"), ("bytes", hexJson bytes)]
  | .reference document => .mkObj [("type", "reference"),
      ("document", decimal document.digest.value)]

/-- One entry of a content cell. Documents, elements, links, atoms, runs and
annotations are spelled out (an annotation with `fresh`: is its atom still at
the anchored revision in this same cell); every entry carries its canonical
`StoreCodec` entry bytes. -/
private def contentEntryJson (store : ContentResource.ContentStore)
    (entry : Minidregg.Theory.Store.Entry Hyperdocument.layout) : Lean.Json :=
  let canonical := hexJson ((StoreCodec.entryStream HyperdocumentCell.contentWire).encode entry)
  match entry with
  | ⟨⟨.documents, identifier⟩, _⟩ =>
      let identifier : Hyperdocument.DocumentId := identifier
      .mkObj [("type", "document"), ("id", decimal identifier.digest.value), ("canonical", canonical)]
  | ⟨⟨.elements, identifier⟩, record⟩ =>
      let identifier : Hyperdocument.ElementId := identifier
      let record : Hyperdocument.ElementRecord := record
      .mkObj [("type", "element"), ("id", decimal identifier.digest.value),
        ("body", elementBodyJson record.body), ("createdBy", principalJson record.createdBy),
        ("canonical", canonical)]
  | ⟨⟨.annotations, identifier⟩, record⟩ =>
      let identifier : Hyperdocument.AnnotationId := identifier
      let record : Hyperdocument.AnnotationRecord := record
      .mkObj [("type", "annotation"), ("id", decimal identifier.digest.value),
        ("anchor", annotationAnchorJson record.anchor), ("body", annotationBodyJson record.body),
        ("author", principalJson record.author),
        ("fresh", .bool (ContentResource.annotationFresh store record)),
        ("canonical", canonical)]
  | ⟨⟨.links, identifier⟩, _⟩ =>
      let identifier : Hyperdocument.LinkId := identifier
      .mkObj [("type", "link"), ("id", decimal identifier.digest.value), ("canonical", canonical)]
  | ⟨⟨.transclusions, identifier⟩, record⟩ =>
      let identifier : Hyperdocument.TransclusionId := identifier
      let record : Hyperdocument.TransclusionRecord := record
      .mkObj <| ([("type", "transclusion"), ("id", decimal identifier.digest.value)] :
          List (String × Lean.Json)) ++
        transclusionRecordJson record ++
        [("author", principalJson record.author), ("canonical", canonical)]
  | ⟨⟨.atoms, identifier⟩, record⟩ =>
      let identifier : Hyperdocument.AtomId := identifier
      let record : Hyperdocument.AtomRecord := record
      .mkObj [("type", "atom"),
        ("id", decimal identifier.digest.value), ("document", decimal record.document.digest.value),
        ("kind", atomKindJson record.kind), ("payload", hexJson record.payload),
        ("createdBy", principalJson record.createdBy),
        ("createdAt", decimal record.createdAt.digest.value),
        ("revision", decimal record.revision.digest.value),
        ("tombstonedAt", optionalOperationJson record.tombstonedAt),
        ("canonical", canonical)]
  | ⟨⟨.runs, identifier⟩, record⟩ =>
      let identifier : Hyperdocument.RunId := identifier
      let record : Hyperdocument.RunRecord := record
      .mkObj [("type", "run"),
        ("id", decimal identifier.digest.value), ("document", decimal record.document.digest.value),
        ("atoms", .arr <| record.atoms.toArray.map fun atom => decimal atom.digest.value),
        ("createdBy", principalJson record.createdBy),
        ("createdAt", decimal record.createdAt.digest.value),
        ("tombstonedAt", optionalOperationJson record.tombstonedAt),
        ("canonical", canonical)]
  | ⟨⟨space, _⟩, _⟩ => .mkObj [("type", "namespace"),
      ("namespace", decimal (HyperdocumentCell.namespaceTag space).toNat), ("canonical", canonical)]

private def contentCellJson (root : Digest) (store : ContentResource.ContentStore) : Lean.Json :=
  .mkObj [("root", decimal root.value),
    ("entries", .arr <| (StoreCodec.entries HyperdocumentCell.contentWire store).toArray.map
      (contentEntryJson store))]

private def resourceJson (value : List UInt8 × List (Nat × Int)) : Result Lean.Json := do
  let packed ← match Minidregg.Theory.CellRegistry.PackedCell.decode
      CanonicalCellRegistry.registry value.1 with
    | some packed => pure packed
    | none => failAt "view-resource.cell" "noncanonical packed cell"
  let view := match packed with
    | ⟨.content, payload⟩ => contentCellJson payload.root payload.logical
    | ⟨.declaredObject, payload⟩ => declaredCellJson payload.root payload.logical
    | _ => .mkObj [("root", decimal packed.payload.root.value), ("canonical", hexJson value.1)]
  pure <| .mkObj [("type", "resource"), ("cell", view),
    ("balances", .arr <| value.2.toArray.map fun p => .arr #[decimal p.1, signedDecimal p.2])]

private def decoded {α : Type} (path : String) (codec : IndexedProgram.LawfulCodec α)
    (bytes : List UInt8) : Result α :=
  match codec.decode bytes with
  | some value => pure value
  | none => failAt path "noncanonical or wrong-family binary input"

/-- The content store inside one signed resource view. -/
private def contentOfView (path : String) (bytes : List UInt8) :
    Result ContentResource.ContentStore := do
  let value ← decoded path NativeObservationController.resourceViewCodec bytes
  match Minidregg.Theory.CellRegistry.PackedCell.decode CanonicalCellRegistry.registry value.1 with
  | some ⟨.content, payload⟩ => pure payload.logical
  | _ => failAt path "not a content cell"

private def transclusionViewJson : ContentResource.TransclusionView → Lean.Json
  | .unavailable atoms source => .mkObj [("view", "unavailable"), ("atoms", decimal atoms),
      ("source", decimal source)]
  | .snapshot lines => .mkObj [("view", "snapshot"), ("lines", .arr <| lines.toArray.map hexJson)]
  | .moved height => .mkObj [("view", "moved"), ("height", decimal height)]
  | .live lines revised => .mkObj [("view", "live"), ("lines", .arr <| lines.toArray.map hexJson),
      ("revised", .bool revised)]
  | .invalidated => .mkObj [("view", "invalidated")]
  | .unresolved => .mkObj [("view", "unresolved")]

/-- The content store inside one signed `at`-height read. -/
private def contentOfAtView (path : String) (bytes : List UInt8) :
    Result ContentResource.ContentStore := do
  let (_, lifecycle) ← decoded path NativeObservationController.atViewCodec bytes
  match ResourceBirthCodec.LifecycleImage.rawDecode CanonicalCellRegistry.registry lifecycle with
  | some (.live ⟨.content, payload⟩) => pure payload.logical
  | _ => failAt path "not a live content cell at that height"

/-- `view-transclusions`: every transclusion record of the host view rendered
by `ContentResource.renderTransclusion` against the source views the reader
itself obtained.  Input: `{"host": HEX, "sources": [{"target": DEC, "view": HEX}
| {"target": DEC, "at": HEX}]}`: a signed `view-resource` binary, or a signed
`view-at` binary of the source at a past height.  A transclusion whose source
cell has no supplied view renders `unavailable`, with its shape only. -/
private def transclusionsJson (bytes : List UInt8) : Result Lean.Json := do
  let text ← match String.fromUTF8? (ByteArray.mk bytes.toArray) with
    | some text => pure text | none => failAt "view-transclusions" "input is not UTF-8"
  let json ← match Lean.Json.parse text with
    | .ok json => pure json | .error message => failAt "view-transclusions" message
  let obj ← exactObject "$" ["host", "sources"] json
  let host ← contentOfView "$.host" (← decodeHex "$.host" (← field "$" "host" obj))
  let sources ← list "$.sources" (fun path entry => do
      let atHeight := (entry.getObjVal? "at").toOption.isSome
      let source ← exactObject path ["target", if atHeight then "at" else "view"] entry
      let target ← nat (path ++ ".target") (← field path "target" source)
      let store ← if atHeight then
          contentOfAtView (path ++ ".at") (← decodeHex (path ++ ".at") (← field path "at" source))
        else
          contentOfView (path ++ ".view") (← decodeHex (path ++ ".view") (← field path "view" source))
      pure (target, store)) (← field "$" "sources" obj)
  let rendered := (StoreCodec.entries HyperdocumentCell.contentWire host).filterMap fun entry =>
    match entry with
    | ⟨⟨.transclusions, identifier⟩, record⟩ =>
        let identifier : Hyperdocument.TransclusionId := identifier
        let record : Hyperdocument.TransclusionRecord := record
        some <| match ContentResource.openingOfReference record.reference with
          | none => .mkObj [("id", decimal identifier.digest.value), ("render", .mkObj [("view", "unresolved")])]
          | some opening =>
              let source := (sources.find? (fun pair => pair.1 = opening.source)).map Prod.snd
              .mkObj [("id", decimal identifier.digest.value), ("mode", modeJson record.reference.mode),
                ("opening", openingJson opening),
                ("render", transclusionViewJson
                  (ContentResource.renderTransclusion source opening record.reference.mode))]
    | _ => none
  pure <| .mkObj [("type", "transclusions"), ("transclusions", .arr rendered.toArray)]

private def launchPhysicalReportJson
    (report : ApplicationLifecycleCompletionV2Report.Report) : Result Lean.Json := do
  let begin := report.claim.originalClaim.originalBegin
  unless report.validFor begin do
    throw "launch physical report differs from its BEGIN-v3/claim/volume"
  let custody := match report.volumeCustody with
    | none => Lean.Json.null
    | some value => .mkObj [
        ("volumeIdHex", hexJson (Sp800185Cshake256.digestBytesLE value.volume)),
        ("physicalWitnessHex", hexJson value.physicalWitness)]
  return .mkObj [
    ("type", .str "application-lifecycle-launch-physical-report-v2"),
    ("frameHex", hexJson report.canonicalBytes),
    ("originalBeginHex", hexJson (ApplicationLifecycleBeginV3Ingress.codec.encode begin)),
    ("committedClaimHex", hexJson
      (ApplicationLifecycleClaimV3Projection.codec.encode report.claim)),
    ("nonce", decimal report.nonce),
    ("unitHex", hexJson report.unit),
    ("materializedImageHex", hexJson report.materializedImage),
    ("outcome", .str <| match report.outcome with
      | .materialized => "materialized" | .running => "running" | .stopped => "stopped"),
    ("invocationIdHex", hexJson report.invocationId),
    ("controlGroupHex", hexJson report.controlGroup),
    ("pid", decimal report.pid),
    ("stopAuditHex", hexJson report.stopAudit),
    ("installedManifestHex", hexJson report.installedManifest),
    ("volumeCustody", custody)]

/-- Inspect bounded public host products. Header/envelope bytes remain exact hex. -/
def inspect (kind : String) (bytes : List UInt8) : Result Lean.Json :=
  match kind with
  | "challenge" => challengeJson <$> decoded "challenge" challengeCodec bytes
  | "plan" => planJson <$> decoded "plan" signingPlanCodec bytes
  | "application-share-issue-plan" => shareIssuePlanJson <$>
      decoded "application-share-issue-plan" ApplicationShareIssueAuthoring.planCodec bytes
  | "application-share-issue-request" => shareIssueRequestJson <$>
      decoded "application-share-issue-request" ApplicationShareIssueAuthoring.requestCodec bytes
  | "application-share-issue-grain-request" =>
      ApplicationShareIssueGrainInspection.inspectRequest bytes
  | "application-share-issue-grain-plan" =>
      ApplicationShareIssueGrainInspection.inspectPlan bytes
  | "application-agent-lifetime-grant-request" =>
      ApplicationAgentLifetimeGrantInspection.inspectRequest bytes
  | "application-agent-lifetime-grant-plan" =>
      ApplicationAgentLifetimeGrantInspection.inspectPlan bytes
  | "application-session-enrollment-request" =>
      ApplicationGrainSessionEnrollmentInspection.inspectRequest bytes
  | "application-session-enrollment-plan" =>
      ApplicationGrainSessionEnrollmentInspection.inspectPlan bytes
  | "application-session-enrollment-ingress" =>
      ApplicationGrainSessionEnrollmentInspection.inspectIngress bytes
  | "application-dispatch-request" => dispatchRequestJson <$>
      decoded "application-dispatch-request" ApplicationDispatchAuthoring.requestCodec bytes
  | "application-agent-reserve-request" => agentPaidReserveRequestJson <$>
      decoded "application-agent-reserve-request"
        ApplicationDispatchAgentPaidAuthoring.requestCodec bytes
  | "application-agent-paid-request" => agentPaidRequestJson <$>
      decoded "application-agent-paid-request"
        ApplicationDispatchAgentPaidAuthoring.paidRequestCodec bytes
  | "application-agent-lifetime-reserve-request" =>
      ApplicationAgentLifetimeDispatchPaidInspection.inspectRequest bytes
  | "application-agent-lifetime-paid-request" =>
      do
        let request ← decoded "application-agent-lifetime-paid-request"
          ApplicationAgentLifetimeDispatchPaidAuthoring.paidRequestCodec bytes
        agentLifetimePaidRequestJson bytes request
  | "application-dispatch-plan" => do
      let plan ← decoded "application-dispatch-plan" ApplicationDispatchAuthoring.planCodec bytes
      dispatchPlanJson plan
  | "application-lifecycle-completion-operator-plan" => do
      let plan ← decoded "application-lifecycle-completion-operator-plan"
        ApplicationLifecycleCompletionOperator.planCodec bytes
      completionOperatorPlanJson plan
  | "application-lifecycle-resident-begin-operator-plan" => do
      let plan ← decoded "application-lifecycle-resident-begin-operator-plan"
        ApplicationLifecycleBeginOperator.planCodec bytes
      residentBeginOperatorPlanJson plan
  | "application-lifecycle-launch-begin-request" =>
      ApplicationLifecycleLaunchBeginInspection.inspectRequest bytes
  | "application-lifecycle-launch-continue-request" =>
      ApplicationLifecycleLaunchBeginInspection.inspectContinueRequest bytes
  | "application-lifecycle-launch-begin-plan" =>
      ApplicationLifecycleLaunchBeginInspection.inspectPlan bytes
  | "application-lifecycle-launch-stop-plan" =>
      ApplicationLifecycleLaunchBeginInspection.inspectStopPlan bytes
  | "application-lifecycle-launch-claim-request" =>
      ApplicationLifecycleLaunchClaimInspection.inspectRequest bytes
  | "application-lifecycle-launch-claim-plan" =>
      ApplicationLifecycleLaunchClaimInspection.inspectPlan bytes
  | "application-lifecycle-launch-completion-request" =>
      ApplicationLifecycleLaunchCompletionInspection.inspectRequest bytes
  | "application-lifecycle-launch-completion-plan" =>
      ApplicationLifecycleLaunchCompletionInspection.inspectPlan bytes
  | "application-lifecycle-launch-physical-report" => do
      let report ← decoded "application-lifecycle-launch-physical-report"
        ApplicationLifecycleCompletionV2Report.codec bytes
      launchPhysicalReportJson report
  | "application-lifecycle-launch-physical-signed-report" => do
      let signed ← decoded "application-lifecycle-launch-physical-signed-report"
        ApplicationLifecycleCompletionV2Report.signedCodec bytes
      unless signed.signature.length == 64 do
        throw "physical signature must be 64 bytes"
      let report ← launchPhysicalReportJson signed.report
      pure <| .mkObj [
        ("type", .str "application-lifecycle-launch-physical-signed-report-v2"),
        ("frameHex", hexJson bytes),
        ("report", report),
        ("signatureHex", hexJson signed.signature)]
  | "application-lifecycle-claim-operator-plan" => do
      let plan ← decoded "application-lifecycle-claim-operator-plan"
        ApplicationLifecycleClaimOperator.planCodec bytes
      lifecycleClaimOperatorPlanJson plan
  | "application-spk-package-identity" => do
      let some descriptor := ApplicationSpkPackageIdentity.decodeCanonical bytes
        | failAt "application-spk-package-identity" "noncanonical package identity profile"
      applicationSpkPackageIdentityJson descriptor
  | "application-spk-launch-descriptor" =>
      ApplicationSpkLaunchDescriptorAuthoring.inspect bytes
  | "participant-key-enrollment" => do
      let command ← decoded "participant-key-enrollment"
        ParticipantKeyEnrollment.commandCodec bytes
      pure (participantKeyCommandJson command)
  | "participant-key-enrollment-plan" => do
      let plan ← decoded "participant-key-enrollment-plan"
        ParticipantKeyEnrollment.signingPlanCodec bytes
      let some command := ParticipantKeyEnrollment.commandCodec.decode plan.commandBytes
        | failAt "participant-key-enrollment-plan" "noncanonical nested command"
      pure <| .mkObj
        [("type", "participant-key-enrollment-plan-v1"),
         ("canonical", hexJson bytes),
         ("domain", decimal plan.domain.value),
         ("semantics", decimal plan.semantics.value),
         ("commandBytes", hexJson plan.commandBytes),
         ("command", participantKeyCommandJson command),
         ("sponsorHeader", signedHeaderJson plan.sponsorHeader),
         ("possessionHeader", hexJson plan.possessionHeader)]
  | "participant-key-enrollment-ingress" => do
      let some parsed := ParticipantKeyEnrollment.decodeIngress bytes
        | failAt "participant-key-enrollment-ingress" "noncanonical ingress or nested bytes"
      pure <| .mkObj
        [("type", "participant-key-enrollment-ingress-v1"),
         ("canonical", hexJson bytes),
         ("commandBytes", hexJson parsed.ingress.commandBytes),
         ("command", participantKeyCommandJson parsed.command),
         ("sponsorEnvelope", hexJson parsed.ingress.sponsorEnvelope),
         ("possessionSignature", hexJson parsed.ingress.possessionSignature),
         ("possessionSignatureLength", decimal parsed.ingress.possessionSignature.length),
         ("signatureVerified", .bool false)]
  | "outcome" => outcomeJson <$> decoded "outcome" outcomeCodec bytes
  | "application-permission-schema" => do
      let schema ← decoded "application-permission-schema"
        ApplicationPermissionSchema.schemaCodec bytes
      unless schema.valid do
        failAt "application-permission-schema" "invalid permission schema"
      pure <| .mkObj [
        ("type", "minidregg-application-permission-schema-v1"),
        ("version", decimal schema.version),
        ("root", decimal schema.root.value),
        ("canonical", hexJson bytes),
        ("permissions", .arr <| schema.permissions.toArray.map fun p => .mkObj [
          ("name", String.fromUTF8! p.name.toByteArray),
          ("obsolete", .bool p.obsolete)]),
        ("roles", .arr <| schema.roles.toArray.map fun role => .mkObj [
          ("permissions", .arr <| role.permissions.toArray.map (fun bit => .bool bit)),
          ("obsolete", .bool role.obsolete),
          ("default", .bool role.default)]),
        ("denied", .arr <| schema.denied.toArray.map (fun bit => .bool bit))]
  | "view-resource" => do
      let value ← decoded "view-resource" NativeObservationController.resourceViewCodec bytes
      resourceJson value
  | "view-transclusions" => transclusionsJson bytes
  | "view-policy" => do
      let value ← match PolicyRecordCodec.decode bytes with
        | some value => pure value | none => failAt "view-policy" "noncanonical policy source"
      pure <| .mkObj [("type", "policy"), ("canonical", hexJson (PolicyRecordCodec.encode value)),
        ("policyId", decimal value.policyId.value), ("version", decimal value.version),
        ("address", decimal (PolicyRecordCodec.digest value).value),
        ("domain", decimal value.domain.value), ("semantics", decimal value.semantics.value),
        ("previous", value.previous.map (fun d => decimal d.value) |>.getD .null),
        ("predicate", predicateJson value.predicate)]
  | "view-who" => do
      let value ← decoded "view-who" NativeObservationController.whoViewCodec bytes
      pure <| .mkObj [("type", "who"), ("members", .arr <| value.toArray.map fun (subject, seen) =>
        .mkObj [("subject", decimal subject), ("lastSeen", (seen.map decimal).getD .null)])]
  | "view-since" => do
      let value ← decoded "view-since" NativeObservationController.sinceViewCodec bytes
      pure <| .mkObj [("type", "since"), ("entries", .arr <| value.toArray.map fun entry =>
        .mkObj [("height", decimal entry.height), ("subject", (entry.subject.map decimal).getD .null),
          ("transaction", decimal entry.transaction),
          ("cells", .arr <| entry.cells.toArray.map decimal)])]
  | "view-at" => do
      let (height, lifecycle) ← decoded "view-at" NativeObservationController.atViewCodec bytes
      match ResourceBirthCodec.LifecycleImage.rawDecode CanonicalCellRegistry.registry lifecycle with
      | some .fresh => pure <| .mkObj [("type", "at"), ("height", decimal height), ("state", "fresh")]
      | some .retired => pure <| .mkObj [("type", "at"), ("height", decimal height), ("state", "retired")]
      | some (.live cell) => do
          let view ← resourceJson (PackedCell.bytes CanonicalCellRegistry.registry cell, [])
          pure <| .mkObj [("type", "at"), ("height", decimal height), ("state", "live"),
            ("canonical", hexJson lifecycle), ("resource", view)]
      | none => failAt "view-at" "noncanonical lifecycle bytes"
  | "view-object-capability" => CapabilityInspection.inspect .object bytes
  | "view-account-capability" => CapabilityInspection.inspect .account bytes
  | "view-program-capability" => CapabilityInspection.inspect .program bytes
  | "view-capability" =>
      let accepted :=
        ((CredentialAuthorityEntryCodec.storedCapabilityStream .object).toLawful.decode bytes).isSome ||
        ((CredentialAuthorityEntryCodec.storedCapabilityStream .account).toLawful.decode bytes).isSome ||
        ((CredentialAuthorityEntryCodec.storedCapabilityStream .program).toLawful.decode bytes).isSome
      if accepted then pure <| .mkObj [("type", "capability"), ("canonical", hexJson bytes)]
      else failAt "view-capability" "noncanonical capability source"
  | _ => failAt "kind" "expected challenge, plan, outcome, application-permission-schema, view-resource, view-transclusions, view-policy, view-capability, view-who, view-since, or view-at"

end Minidregg.Host.Json
