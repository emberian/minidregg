/-
Bounded JSON authoring for the native host. JSON is only a human-facing
notation: successful authoring constructs the real source values and invokes
their canonical codecs. All unbounded integers are decimal strings.
-/
import Kernel.NativeHost
import Kernel.NativeHostGenesis
import Kernel.AgentGrain
import Kernel.CapabilityRevocationController
import Kernel.ContentResource
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
  let names := ["id", "root", "parent", "issuer", "holder", "targets", "verbs", "maxCost",
    "notBefore", "notAfter", "issuerEpoch", "policyId", "policyEpoch", "ancestors", "channels"]
  let obj ← exactObject path names json
  let targets ← list (path ++ ".targets")
    (fun p j => ResourceId.mk <$> nat p j) (← field path "targets" obj)
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
    scope := ⟨targets.toFinset, verbs.toFinset,
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
      let obj ← exactObject path ["type", "document", "element", "snapshot"] json
      pure (.embed ⟨← identifier (path ++ ".document") (← field path "document" obj),
        ← optional (path ++ ".element") identifier (← field path "element" obj),
        ← optional (path ++ ".snapshot") identifier (← field path "snapshot" obj)⟩)
  | "opaque" =>
      let obj ← exactObject path ["type", "schema", "payload"] json
      pure (.opaque ⟨← nat (path ++ ".schema") (← field path "schema" obj)⟩
        (← decodeHex (path ++ ".payload") (← field path "payload" obj)))
  | _ => failAt (path ++ ".type") "unknown element body"

private def atomRecord (path : String) (json : Lean.Json) : Result Hyperdocument.AtomRecord := do
  let obj ← exactObject path ["document", "kind", "payload", "createdBy", "createdAt", "tombstonedAt"] json
  pure ⟨← identifier (path ++ ".document") (← field path "document" obj),
    ← atomKind (path ++ ".kind") (← field path "kind" obj),
    ← decodeHex (path ++ ".payload") (← field path "payload" obj),
    ← principal (path ++ ".createdBy") (← field path "createdBy" obj),
    ← identifier (path ++ ".createdAt") (← field path "createdAt" obj),
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

private def pageRef (path : String) (json : Lean.Json) : Result HyperdocumentContentPageMaterializer.PageRef := do
  let obj ← exactObject path ["contentDomain", "pageNumber", "expectedRoot"] json
  pure ⟨⟨← nat (path ++ ".contentDomain") (← field path "contentDomain" obj)⟩,
    ← nat (path ++ ".pageNumber") (← field path "pageNumber" obj),
    ⟨← nat (path ++ ".expectedRoot") (← field path "expectedRoot" obj)⟩⟩

private def forwardTarget (path : String) (json : Lean.Json) :
    Result HyperdocumentContentPageMaterializer.ForwardTarget := do
  let (tag, _) ← tagged path json
  match tag with
  | "document" | "element" =>
      let obj ← exactObject path ["type", "page", "id"] json
      let page ← pageRef (path ++ ".page") (← field path "page" obj)
      if tag = "document" then pure (.document page (← identifier (path ++ ".id") (← field path "id" obj)))
      else pure (.element page (← identifier (path ++ ".id") (← field path "id" obj)))
  | "range" =>
      let obj ← exactObject path ["type", "page", "document", "range"] json
      pure (.range (← pageRef (path ++ ".page") (← field path "page" obj))
        (← identifier (path ++ ".document") (← field path "document" obj))
        (← stableRange (path ++ ".range") (← field path "range" obj)))
  | "external" =>
      let obj ← exactObject path ["type", "scheme", "authority", "path"] json
      pure (.external (← decodeHex (path ++ ".scheme") (← field path "scheme" obj))
        (← decodeHex (path ++ ".authority") (← field path "authority" obj))
        (← decodeHex (path ++ ".path") (← field path "path" obj)))
  | _ => failAt (path ++ ".type") "unknown forward target"

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
        (← forwardTarget (path ++ ".target") (← field path "target" obj))
        ⟨← nat (path ++ ".relation") (← field path "relation" obj)⟩)
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
  | _ => failAt (path ++ ".type") "expected scalar or content"

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
  let obj ← exactObject path ["subject", "expectedAuthorityRoot", "nonce", "targets"] json
  pure {
    subject := ⟨← nat (path ++ ".subject") (← field path "subject" obj)⟩
    expectedAuthorityRoot := ⟨← nat (path ++ ".expectedAuthorityRoot")
      (← field path "expectedAuthorityRoot" obj)⟩
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
        let p ← exactObject (path ++ ".purpose") ["type", "kind", "target", "view"] purposeJson
        let view ← match ← string (path ++ ".purpose.view") (← field (path ++ ".purpose") "view" p) with
          | "resource" => pure QueryView.resource | "policy" => pure .policy
          | "capability" => pure .capability | _ => failAt (path ++ ".purpose.view") "unknown query view"
        pure (.query ⟨← resourceKind (path ++ ".purpose.kind") (← field (path ++ ".purpose") "kind" p),
          ← nat (path ++ ".purpose.target") (← field (path ++ ".purpose") "target" p), view⟩)
    | _ => failAt (path ++ ".purpose.type") "expected prepare or query"
  pure ⟨⟨← nat (path ++ ".subject") (← field path "subject" obj)⟩,
    ← nat (path ++ ".nonce") (← field path "nonce" obj), purpose,
    ← list (path ++ ".grants") grant (← field path "grants" obj)⟩

private def keyRecord (path : String) (json : Lean.Json) : Result KeyRecord := do
  let obj ← exactObject path ["keyId", "keyEpoch", "algorithm", "subject", "publicKey",
    "activeFrom", "activeUntil", "revoked"] json
  pure ⟨← nat (path ++ ".keyId") (← field path "keyId" obj),
    ← nat (path ++ ".keyEpoch") (← field path "keyEpoch" obj),
    ← nat (path ++ ".algorithm") (← field path "algorithm" obj),
    ← nat (path ++ ".subject") (← field path "subject" obj),
    ← decodeHex (path ++ ".publicKey") (← field path "publicKey" obj),
    ← nat (path ++ ".activeFrom") (← field path "activeFrom" obj),
    ← nat (path ++ ".activeUntil") (← field path "activeUntil" obj),
    ← bool (path ++ ".revoked") (← field path "revoked" obj)⟩

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
  let names := ["domain", "factoryId", "resourceBookId", "authorityCatalogueId", "federation",
    "tariffBase", "tariffPerBirth", "tariffPerGrant", "tariffPerInitialPayloadByte",
    "collector", "asset", "expectedSemantics", "issuerEpoch", "genesisHeight",
    "factoryPredicate", "enrollments", "factoryControllerSubject",
    "factoryControllerCapability", "meterAllowance"]
  let obj ← exactObject path names json
  pure {
    deployment := ⟨⟨← nat (path ++ ".domain") (← field path "domain" obj)⟩,
      ← nat (path ++ ".factoryId") (← field path "factoryId" obj),
      ← nat (path ++ ".resourceBookId") (← field path "resourceBookId" obj),
      ← nat (path ++ ".authorityCatalogueId") (← field path "authorityCatalogueId" obj)⟩
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

private structure BirthParts where
  item : ResourceBirth.BirthItem CanonicalCellRegistry.registry
  ownerGrant : ResourceBirth.AuthorityGrant
  controlGrant : ResourceBirth.AuthorityGrant
  policy : ResourceBirth.InitialPolicy

/-- The worker clause is tied to one execution generation. Grant caveats
cannot currently carry arbitrary Pred, so the native resource policy itself
must constrain a delegated worker. -/
private def grainPolicy (owner : Nat) (worker : Option (Nat × Int)) : Minidregg.Pred.Pred :=
  let base := AgentGrain.policy (.eq "request/subject" (Int.ofNat owner))
  match worker with
  | none => base
  | some (subject, generation) => .all [base, .any [
      .eq "request/subject" (Int.ofNat owner),
      .memberOf "request/verb" [1, 3],
      .all [.eq "request/subject" (Int.ofNat subject),
        AgentGrain.witnessCaveat generation]]]

private def grainWorker (path : String)
    (obj : Std.TreeMap.Raw String Lean.Json compare) : Result (Option (Nat × Int)) := do
  match obj.get? "workerSubject", obj.get? "workerGeneration" with
  | none, none => pure none
  | some subject, some generation =>
      pure (some (← nat (path ++ ".workerSubject") subject,
        ← int (path ++ ".workerGeneration") generation))
  | _, _ => failAt path "workerSubject and workerGeneration must be supplied together"

private def birthParts (path : String)
    (profile : CanonicalRuntimeProfile.Profile NativeHostProfile.Field)
    (source : NativeHostGenesis.Config) (json : Lean.Json) : Result BirthParts := do
  let raw ← object path json
  let storage ← string (path ++ ".storage") (← field path "storage" raw)
  let worker ← if storage = "grain" then grainWorker path raw else pure none
  let obj ← exactObject path
    (if storage = "grain" then
      ["kind", "storage", "target", "owner", "ownerCapability", "controlCapability", "budget"] ++
        (if worker.isSome then ["workerSubject", "workerGeneration"] else [])
    else
      ["kind", "storage", "target", "owner", "ownerCapability", "controlCapability", "predicate"]) json
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
      pure ⟨.content, CellState.materialize HyperdocumentContentPageMaterializer.materializer
        (HyperdocumentContentPageMaterializer.stateOfOption
          (some (ContentResource.initialPage source.deployment.domain target)))⟩
    else if storage = "grain" then
      let budget ← nat (path ++ ".budget") (← field path "budget" obj)
      pure ⟨.declaredObject, CellState.materialize DeclaredEffectPageMaterializer.materializer
        (DeclaredEffectPageMaterializer.stateOfOption
          (some (AgentGrain.initialPage source.deployment.domain target budget)))⟩
    else pure (NativeHostGenesis.declaredCell source target (kind = .account))
  let item : ResourceBirth.BirthItem CanonicalCellRegistry.registry :=
    ⟨⟨target, CellSlot.root CanonicalCellRegistry.registry .absent, cell⟩, kind, owner⟩
  let ownerGrant : ResourceBirth.AuthorityGrant := match kind with
    | .object => ⟨.object, ⟨NativeHostGenesis.rootCapability profile source .object
        ownerId owner target (ResourceBirthPolicyController.Concrete.ownerVerbs .object), []⟩⟩
    | .account => ⟨.account, ⟨NativeHostGenesis.rootCapability profile source .account
        ownerId owner target (ResourceBirthPolicyController.Concrete.ownerVerbs .account), []⟩⟩
    | .program => ⟨.program, ⟨NativeHostGenesis.rootCapability profile source .program
        ownerId owner target (ResourceBirthPolicyController.Concrete.ownerVerbs .program), []⟩⟩
  let control : Capability .program := NativeHostGenesis.rootCapability profile source .program
    controlId owner target {.installPolicy, .revokeCapability}
  pure ⟨item, ownerGrant, ⟨.program, ⟨control, []⟩⟩,
    ⟨rule.policyId, PolicyRecordCodec.digest rule, PolicyRecordCodec.encode rule⟩⟩

/-- A standard birth is built entirely through the deployed source helpers:
absent roots, declared cells, owner/control grants, policy addresses, identity,
nullifier and quoted fee are never supplied as JSON assertions. -/
private def birth (path : String) (json : Lean.Json) : Result Draft := do
  let obj ← exactObject path ["genesis", "template", "creator", "nonce", "resources",
    "sourceCapabilities", "funding", "feePayer"] json
  let source ← genesis (path ++ ".genesis") (← field path "genesis" obj)
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
    storage := ⟨"", ""⟩, signature := ⟨""⟩ }
  let profile := nativeConfig.profile
  unless source.expectedSemantics = profile.semantics do
    throw s!"{path}.genesis.expectedSemantics: does not match the source-derived native profile"
  let creator := SubjectId.mk (← nat (path ++ ".creator") (← field path "creator" obj))
  let nonce ← nat (path ++ ".nonce") (← field path "nonce" obj)
  let parts ← list (path ++ ".resources") (fun itemPath => birthParts itemPath profile source)
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

private def birthIntent (path : String) (json : Lean.Json) : Result Intent := do
  let obj ← exactObject path ["subject", "nonce", "birth", "grants"] json
  pure ⟨⟨← nat (path ++ ".subject") (← field path "subject" obj)⟩,
    ← nat (path ++ ".nonce") (← field path "nonce" obj),
    .prepare (← birth (path ++ ".birth") (← field path "birth" obj)),
    ← list (path ++ ".grants") grant (← field path "grants" obj)⟩

private def grainSource (path : String) (json : Lean.Json) :
    Result (DeclaredResourceController.Command × AgentGrain.State) := do
  let obj ← object path json
  for key in obj.foldl (init := []) (fun names key _ => key :: names) do
    unless ["task", "subject", "capability", "expectedAuthorityRoot",
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
  let authorityRoot := Digest.mk
    (← nat (path ++ ".expectedAuthorityRoot") (← field path "expectedAuthorityRoot" obj))
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
  let command := operation.command subject authorityRoot (AgentGrain.contextNonce contextBytes)
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
  let obj ← exactObject path ["subject", "intentNonce", "declarationNonce", "task",
    "owner", "workerSubject", "workerGeneration", "control", "domain", "semantics",
    "expectedPreRoot", "expectedVersion", "expectedAddress", "grants"] json
  let subject := SubjectId.mk (← nat (path ++ ".subject") (← field path "subject" obj))
  let owner ← nat (path ++ ".owner") (← field path "owner" obj)
  let worker ← nat (path ++ ".workerSubject") (← field path "workerSubject" obj)
  let generation ← int (path ++ ".workerGeneration") (← field path "workerGeneration" obj)
  let task ← nat (path ++ ".task") (← field path "task" obj)
  let version ← nat (path ++ ".expectedVersion") (← field path "expectedVersion" obj)
  let address := Digest.mk (← nat (path ++ ".expectedAddress")
    (← field path "expectedAddress" obj))
  let source : PolicyRecord :=
    ⟨⟨task⟩, version + 1,
      ⟨← nat (path ++ ".domain") (← field path "domain" obj)⟩,
      ⟨← nat (path ++ ".semantics") (← field path "semantics" obj)⟩,
      some address, grainPolicy owner (some (worker, generation))⟩
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

/-- Author JSON into source-owned canonical bytes. -/
def author (kind : String) (json : Lean.Json) : Result (List UInt8) :=
  match kind with
  | "predicate" => NativeHostGenesis.predicateStream.encode <$> predicate "$" json
  | "grain-policy" => do
      let raw ← object "$" json
      let worker ← grainWorker "$" raw
      let obj ← exactObject "$" (["owner"] ++
        if worker.isSome then ["workerSubject", "workerGeneration"] else []) json
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
  | "birth" => draftCodec.encode <$> birth "$" json
  | "birth-intent" => intentCodec.encode <$> birthIntent "$" json
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
      "expected predicate, grain-policy, grain-caveat, grain-policy-install-intent, policy, policy-install[-draft], delegation[-draft], revocation[-draft], birth, content, resource, joint[-draft], grain[-intent], draft, intent, or genesis"

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
  | .birth descriptor capabilities => .mkObj [("type", "birth"), ("descriptor", hexJson descriptor),
      ("sourceCapabilities", .arr <| capabilities.toArray.map fun c => decimal c.value)]
  | .invoke bytes => .mkObj [("type", "invoke"), ("command", hexJson bytes)]
  | .install subject control bytes => .mkObj [("type", "install"), ("subject", decimal subject.value),
      ("control", decimal control.value), ("declaration", hexJson bytes)]
  | .delegate bytes => .mkObj [("type", "delegate"), ("command", hexJson bytes)]
  | .revoke bytes => .mkObj [("type", "revoke"), ("command", hexJson bytes)]

private def signedHeaderJson (bytes : List UInt8) : Lean.Json :=
  match CredentialSignedEnvelopeController.headerCodec.decode bytes with
  | none => .mkObj [("canonical", hexJson bytes), ("decoded", false)]
  | some header => .mkObj
      [("canonical", hexJson bytes), ("decoded", true),
       ("codecVersion", decimal header.codecVersion),
       ("authorityRoot", decimal header.authorityRoot.value),
       ("registryCommitment", decimal header.registryCommitment.value),
       ("keyId", decimal header.keyId), ("keyEpoch", decimal header.keyEpoch),
       ("algorithm", decimal header.algorithm), ("domain", hexJson header.domain),
       ("message", hexJson header.message), ("nullifier", decimal header.nullifier)]

private def planJson (plan : SigningPlan) : Lean.Json := .mkObj
  [("domain", decimal plan.domain.value), ("semantics", decimal plan.semantics.value),
   ("imageBoundary", decimal plan.imageBoundary.value), ("height", decimal plan.height),
   ("finalizedDraft", draftJson plan.finalizedDraft),
   ("slots", .arr <| plan.slots.toArray.map fun slot => .mkObj
     [("role", decimal slot.role), ("index", decimal slot.index),
      ("header", hexJson slot.header), ("signing", signedHeaderJson slot.header)])]

private def intentJson (value : Intent) : Lean.Json := .mkObj
  [("subject", decimal value.subject.value), ("nonce", decimal value.nonce),
   ("purpose", match value.purpose with
     | .prepare d => .mkObj [("type", "prepare"), ("draft", draftJson d)]
     | .query q => .mkObj [("type", "query"),
       ("kind", match q.kind with | .object => "object" | .account => "account" | .program => "program"),
       ("target", decimal q.target),
       ("view", match q.view with | .resource => "resource" | .policy => "policy" | .capability => "capability")]),
   ("grants", .arr <| value.grants.toArray.map fun g => .mkObj
     [("kind", match g.kind with | .object => "object" | .account => "account" | .program => "program"),
      ("target", decimal g.target), ("capability", decimal g.capability.value)])]

private def challengeJson (value : Challenge) : Lean.Json := .mkObj
  [("intent", intentJson value.intent), ("domain", decimal value.domain.value),
   ("semantics", decimal value.semantics.value), ("federation", decimal value.federation.value),
   ("imageBoundary", decimal value.imageBoundary.value), ("height", decimal value.height),
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
      ("acceptedCount", decimal receipt.acceptedCount), ("imageBoundary", decimal receipt.imageBoundary.value)]
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

private def declaredPageJson (root : Digest)
    (page : DeclaredEffectPageMaterializer.Page) : Lean.Json :=
  let base := [("root", decimal root.value), ("effectDomain", decimal page.effectDomain.value),
    ("shardNumber", decimal page.shardNumber),
    ("entries", .arr <| page.entries.toArray.map fun entry => .mkObj
      [("key", stateKeyJson entry.key), ("value", signedDecimal entry.value)])]
  let grain := page.entries.findSome? fun entry => match entry.key with
    | .objectField task field => if field.value = 0 then some task.value else none
    | _ => none
  match grain with
  | none => .mkObj base
  | some task => match AgentGrain.readState task page with
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

private def contentEntryJson (entry : HyperdocumentContentPageMaterializer.Entry) : Lean.Json :=
  let canonical := hexJson (HyperdocumentContentPageMaterializer.entryStream.encode entry)
  match entry with
  | .document identifier _ => .mkObj [("type", "document"),
      ("id", decimal identifier.digest.value), ("canonical", canonical)]
  | .element identifier _ => .mkObj [("type", "element"),
      ("id", decimal identifier.digest.value), ("canonical", canonical)]
  | .link identifier _ => .mkObj [("type", "link"),
      ("id", decimal identifier.digest.value), ("canonical", canonical)]
  | .atom identifier record => .mkObj [("type", "atom"),
      ("id", decimal identifier.digest.value), ("document", decimal record.document.digest.value),
      ("kind", atomKindJson record.kind), ("payload", hexJson record.payload),
      ("createdBy", principalJson record.createdBy),
      ("createdAt", decimal record.createdAt.digest.value),
      ("tombstonedAt", record.tombstonedAt.map (fun id => decimal id.digest.value) |>.getD .null),
      ("canonical", canonical)]
  | .run identifier record => .mkObj [("type", "run"),
      ("id", decimal identifier.digest.value), ("document", decimal record.document.digest.value),
      ("atoms", .arr <| record.atoms.toArray.map fun atom => decimal atom.digest.value),
      ("createdBy", principalJson record.createdBy),
      ("createdAt", decimal record.createdAt.digest.value),
      ("tombstonedAt", record.tombstonedAt.map (fun id => decimal id.digest.value) |>.getD .null),
      ("canonical", canonical)]

private def contentPageJson (root : Digest)
    (page : HyperdocumentContentPageMaterializer.Page) : Lean.Json := .mkObj
  [("root", decimal root.value), ("contentDomain", decimal page.contentDomain.value),
   ("document", decimal page.document.digest.value), ("pageNumber", decimal page.pageNumber),
   ("canonicalPage", hexJson (HyperdocumentContentPageMaterializer.pageStream.encode page)),
   ("entries", .arr <| page.entries.toArray.map contentEntryJson)]

private def resourceJson (value : List UInt8 × List (Nat × Int)) : Result Lean.Json := do
  let packed ← match Minidregg.Theory.CellRegistry.PackedCell.decode
      CanonicalCellRegistry.registry value.1 with
    | some packed => pure packed
    | none => failAt "view-resource.page" "noncanonical packed cell"
  let view ← match value.1 with
    | 68 :: 82 :: 1 :: 1 :: payloadBytes =>
        match HyperdocumentContentPageMaterializer.materializer.codec.decode payloadBytes with
        | some logical =>
            match HyperdocumentContentPageMaterializer.pageAt logical with
            | some page => pure (contentPageJson
                (HyperdocumentContentPageMaterializer.materializer.rootBytes payloadBytes) page)
            | none => failAt "view-resource.page" "content object has no page"
        | none => failAt "view-resource.page" "noncanonical content object"
    | 68 :: 82 :: 1 :: 5 :: payloadBytes =>
        match DeclaredEffectPageMaterializer.stateCodec.decode payloadBytes with
        | some logical =>
            match DeclaredEffectPageMaterializer.pageAt logical with
            | some page => pure (declaredPageJson
                (DeclaredEffectPageMaterializer.materializer.rootBytes payloadBytes) page)
            | none => failAt "view-resource.page" "declared object has no page"
        | none => failAt "view-resource.page" "noncanonical declared object"
    | _ => pure <| .mkObj [("root", decimal packed.payload.root.value),
          ("canonical", hexJson value.1)]
  pure <| .mkObj [("type", "resource"), ("page", view),
    ("balances", .arr <| value.2.toArray.map fun p => .arr #[decimal p.1, signedDecimal p.2])]

private def decoded {α : Type} (path : String) (codec : IndexedProgram.LawfulCodec α)
    (bytes : List UInt8) : Result α :=
  match codec.decode bytes with
  | some value => pure value
  | none => failAt path "noncanonical or wrong-family binary input"

/-- Inspect bounded public host products. Header/envelope bytes remain exact hex. -/
def inspect (kind : String) (bytes : List UInt8) : Result Lean.Json :=
  match kind with
  | "challenge" => challengeJson <$> decoded "challenge" challengeCodec bytes
  | "plan" => planJson <$> decoded "plan" signingPlanCodec bytes
  | "outcome" => outcomeJson <$> decoded "outcome" outcomeCodec bytes
  | "view-resource" => do
      let value ← decoded "view-resource" NativeObservationController.resourceViewCodec bytes
      resourceJson value
  | "view-policy" => do
      let value ← match PolicyRecordCodec.decode bytes with
        | some value => pure value | none => failAt "view-policy" "noncanonical policy source"
      pure <| .mkObj [("type", "policy"), ("canonical", hexJson (PolicyRecordCodec.encode value)),
        ("policyId", decimal value.policyId.value), ("version", decimal value.version),
        ("address", decimal (PolicyRecordCodec.digest value).value),
        ("domain", decimal value.domain.value), ("semantics", decimal value.semantics.value),
        ("previous", value.previous.map (fun d => decimal d.value) |>.getD .null),
        ("predicate", predicateJson value.predicate)]
  | "view-capability" =>
      let accepted :=
        ((CredentialAuthorityEntryCodec.storedCapabilityStream .object).toLawful.decode bytes).isSome ||
        ((CredentialAuthorityEntryCodec.storedCapabilityStream .account).toLawful.decode bytes).isSome ||
        ((CredentialAuthorityEntryCodec.storedCapabilityStream .program).toLawful.decode bytes).isSome
      if accepted then pure <| .mkObj [("type", "capability"), ("canonical", hexJson bytes)]
      else failAt "view-capability" "noncanonical capability source"
  | _ => failAt "kind" "expected challenge, plan, outcome, view-resource, view-policy, or view-capability"

end Minidregg.Host.Json
