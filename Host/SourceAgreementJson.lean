/- Ordinary author/inspect projection of the existing Host.Json source.
Supported branches preserve original grammar and canonical codecs. Unsupported
families fail closed. Native source admission remains in NativeHost. -/
import Kernel.NativeHost
import Kernel.NativeHostGenesis
import Kernel.ProviderRoute
import Host.BirthRuntimeProfile
import Host.SourceAgreementLegacyView
import Host.SourceAgreementContextInspection
import Host.CapabilityInspection
import Lean.Data.Json

namespace Minidregg.Host.SourceAgreementJson
open Lean Minidregg Minidregg.Pred Minidregg.Theory
open Minidregg.Theory.CellRegistry Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.CredentialSigningKey Minidregg.Theory.DeclaredActionLowering
open Minidregg.Compiler Minidregg.Compiler.CanonicalPolicyAdmission
open Minidregg.Compiler.NativeHostCodec Minidregg.Compiler.NativeObservationCodec
open Minidregg.Compiler.Tower256ConcreteBackend Minidregg.Kernel
set_option autoImplicit false
abbrev Result := Except String

def admitKey (keys : Std.HashSet String) (key : String) : Result (Std.HashSet String) :=
  if keys.contains key then .error s!"duplicate JSON object field: {key}"
  else .ok (keys.insert key)

private structure ScanFrame where
  object : Bool
  expectKey : Bool := false
  keys : Std.HashSet String := {}

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
      | '{', _ => duplicateScan rest (⟨true, true, {}⟩ :: stack)
      | '[', _ => duplicateScan rest (⟨false, false, {}⟩ :: stack)
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
            let keys ← admitKey frame.keys key
            duplicateScan suffix ({ frame with expectKey := false, keys } :: tail)
          else duplicateScan suffix stack
      | '"', [] => do
          let (_, suffix) ← scanString rest ['"']
          duplicateScan suffix []
      | _, _ => duplicateScan rest stack

def nestingDepth (source : List Char) : Nat :=
  go source false false 0 0
where
  go : List Char → (inString escaped : Bool) → (depth deepest : Nat) → Nat
    | [], _, _, _, deepest => deepest
    | _ :: rest, true, true, depth, deepest => go rest true false depth deepest
    | '\\' :: rest, true, false, depth, deepest => go rest true true depth deepest
    | '"' :: rest, true, false, depth, deepest => go rest false false depth deepest
    | _ :: rest, true, false, depth, deepest => go rest true false depth deepest
    | '"' :: rest, false, _, depth, deepest => go rest true false depth deepest
    | '[' :: rest, false, _, depth, deepest => go rest false false (depth + 1) (max deepest (depth + 1))
    | '{' :: rest, false, _, depth, deepest => go rest false false (depth + 1) (max deepest (depth + 1))
    | ']' :: rest, false, _, depth, deepest => go rest false false (depth - 1) deepest
    | '}' :: rest, false, _, depth, deepest => go rest false false (depth - 1) deepest
    | _ :: rest, false, _, depth, deepest => go rest false false depth deepest

def maxNesting : Nat := 64

def parse (source : String) : Result Lean.Json := do
  unless nestingDepth source.toList ≤ maxNesting do
    throw s!"$: JSON nesting deeper than {maxNesting}"
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
  | "eqSlots" | "leSlots" =>
      let obj ← exactObject path ["type", "left", "right"] json
      let left ← string (path ++ ".left") (← field path "left" obj)
      let right ← string (path ++ ".right") (← field path "right" obj)
      pure <| if tag = "eqSlots" then .eqSlots left right else .leSlots left right
  | "leSlotsOff" =>
      let obj ← exactObject path ["type", "left", "right", "offset"] json
      let left ← string (path ++ ".left") (← field path "left" obj)
      let right ← string (path ++ ".right") (← field path "right" obj)
      let offset ← int (path ++ ".offset") (← field path "offset" obj)
      pure (.leSlotsOff left right offset)
  | "witnessed" =>
      let obj ← exactObject path ["type", "identifier"] json
      pure (.witnessed ⟨← string (path ++ ".identifier") (← field path "identifier" obj)⟩)
  | "hashEq" =>
      let obj ← exactObject path ["type", "values", "blinder", "commit"] json
      let values ← list (path ++ ".values") string (← field path "values" obj)
      if values.isEmpty then failAt (path ++ ".values") "a hashEq opens at least one value slot"
      pure (.hashEq values
        (← string (path ++ ".blinder") (← field path "blinder" obj))
        (← string (path ++ ".commit") (← field path "commit" obj)))
  | "ran" =>
      let obj ← exactObject path ["type", "program"] json
      pure (.ran (← nat (path ++ ".program") (← field path "program" obj)))
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
  | .eqSlots left right => .mkObj [("type", "eqSlots"), ("left", .str left),
      ("right", .str right)]
  | .leSlots left right => .mkObj [("type", "leSlots"), ("left", .str left),
      ("right", .str right)]
  | .leSlotsOff left right offset => .mkObj [("type", "leSlotsOff"), ("left", .str left),
      ("right", .str right), ("offset", signedDecimal offset)]
  | .witnessed identifier => .mkObj [("type", "witnessed"),
      ("identifier", .str identifier.id)]
  | .hashEq values blinder commit => .mkObj [("type", "hashEq"),
      ("values", .arr (values.toArray.map .str)), ("blinder", .str blinder),
      ("commit", .str commit)]
  | .ran program => .mkObj [("type", "ran"), ("program", .str (toString program))]
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

private def lawSelector (path : String) (json : Lean.Json) : Result LawComposition.Selector := do
  if json.isNull then return {}
  let raw ← object path json
  let keys := ["physicalKinds", "requestKinds", "verbs"].filter (fun key => (raw.get? key).isSome)
  let obj ← exactObject path keys json
  let values (key : String) : Result (Option (List Nat)) :=
    match obj.get? key with
    | none => pure none
    | some value => optional (path ++ "." ++ key) (fun valuePath => list valuePath nat) value
  pure {
    physicalKinds := ← values "physicalKinds"
    requestKinds := ← values "requestKinds"
    verbs := ← values "verbs" }

private def lawReference (path : String) (json : Lean.Json) : Result LawComposition.PolicyRef := do
  let obj ← exactObject path ["policyId", "facet", "selection"] json
  let facet ← match ← string (path ++ ".facet") (← field path "facet" obj) with
    | "local" => pure LawComposition.Facet.local
    | "descendants" => pure LawComposition.Facet.descendants
    | _ => failAt (path ++ ".facet") "expected local or descendants"
  let raw ← field path "selection" obj
  let valuePath := path ++ ".selection"
  let (tag, _) ← tagged valuePath raw
  let selection ← match tag with
    | "head" => exactObject valuePath ["type"] raw *> pure LawComposition.Selection.head
    | "pinned" => do
        let selected ← exactObject valuePath ["type", "revision", "sourceDigest"] raw
        pure (.pinned (← nat (valuePath ++ ".revision") (← field valuePath "revision" selected))
          ⟨← nat (valuePath ++ ".sourceDigest") (← field valuePath "sourceDigest" selected)⟩)
    | _ => failAt (valuePath ++ ".type") "expected head or pinned"
  pure {
    policyId := ⟨← nat (path ++ ".policyId") (← field path "policyId" obj)⟩
    facet := facet
    selection := selection }

private def lawComponent (path : String) (json : Lean.Json) : Result LawComposition.Component := do
  let obj ← exactObject path ["selector", "predicate", "parents"] json
  pure {
    selector := ← lawSelector (path ++ ".selector") (← field path "selector" obj)
    predicate := ← predicate (path ++ ".predicate") (← field path "predicate" obj)
    parents := ← list (path ++ ".parents") lawReference (← field path "parents" obj) }

private def lawSelectorJson (value : LawComposition.Selector) : Lean.Json :=
  let selected (values : Option (List Nat)) : Lean.Json :=
    values.map (fun xs => .arr (xs.toArray.map decimal)) |>.getD .null
  .mkObj [("physicalKinds", selected value.physicalKinds),
    ("requestKinds", selected value.requestKinds), ("verbs", selected value.verbs)]

private def lawReferenceJson (value : LawComposition.PolicyRef) : Lean.Json :=
  .mkObj [("policyId", decimal value.policyId.value),
    ("facet", match value.facet with | .local => "local" | .descendants => "descendants"),
    ("selection", match value.selection with
      | .head => .mkObj [("type", "head")]
      | .pinned revision digest => .mkObj [("type", "pinned"),
          ("revision", decimal revision), ("sourceDigest", decimal digest.value)])]

private def lawComponentJson (value : LawComposition.Component) : Lean.Json :=
  .mkObj [("selector", lawSelectorJson value.selector),
    ("predicate", predicateJson value.predicate),
    ("parents", .arr (value.parents.toArray.map lawReferenceJson))]

def audienceStateJson (state : Minidregg.Theory.ObjectAudience.State) : Lean.Json := .mkObj
  [("object", decimal state.object), ("epoch", decimal state.epoch),
   ("parent", decimal state.parent), ("transition", decimal state.transition),
   ("audience", decimal state.audience), ("devices", decimal state.devices),
   ("history", decimal state.history), ("manifest", decimal state.manifest),
   ("mode", .str (if state.mode == .active then "active" else "frozen")),
   ("authoritySnapshot", decimal state.authoritySnapshot),
   ("deviceSnapshot", decimal state.deviceSnapshot)]

def audienceState (path : String) (json : Lean.Json) :
    Result Minidregg.Theory.ObjectAudience.State := do
  let obj ← exactObject path ["object", "epoch", "parent", "transition", "audience",
    "devices", "history", "manifest", "mode", "authoritySnapshot", "deviceSnapshot"] json
  let mode ← match ← string (path ++ ".mode") (← field path "mode" obj) with
    | "active" => pure Minidregg.Theory.ObjectAudience.Mode.active
    | "frozen" => pure Minidregg.Theory.ObjectAudience.Mode.frozen
    | _ => failAt (path ++ ".mode") "expected active or frozen"
  pure {
    object := ← nat (path ++ ".object") (← field path "object" obj)
    epoch := ← nat (path ++ ".epoch") (← field path "epoch" obj)
    parent := ← nat (path ++ ".parent") (← field path "parent" obj)
    transition := ← nat (path ++ ".transition") (← field path "transition" obj)
    audience := ← nat (path ++ ".audience") (← field path "audience" obj)
    devices := ← nat (path ++ ".devices") (← field path "devices" obj)
    history := ← nat (path ++ ".history") (← field path "history" obj)
    manifest := ← nat (path ++ ".manifest") (← field path "manifest" obj)
    mode := mode
    authoritySnapshot := ← nat (path ++ ".authoritySnapshot") (← field path "authoritySnapshot" obj)
    deviceSnapshot := ← nat (path ++ ".deviceSnapshot") (← field path "deviceSnapshot" obj) }

def policyRecordJson (record : PolicyRecord) : Lean.Json := .mkObj
  [("policyId", decimal record.policyId.value), ("version", decimal record.version),
   ("domain", decimal record.domain.value), ("semantics", decimal record.semantics.value),
   ("previous", record.previous.map (fun d => decimal d.value) |>.getD .null),
   ("predicate", predicateJson record.predicate),
   ("localSelector", lawSelectorJson record.localSelector),
   ("parents", .arr (record.parents.toArray.map lawReferenceJson)),
   ("descendants", record.descendants.map lawComponentJson |>.getD .null),
   ("audience", record.audience.map audienceStateJson |>.getD .null),
   ("objectDescriptor", record.objectDescriptor.map (fun d => decimal d.value) |>.getD .null)]

private def policyRecord (path : String) (json : Lean.Json) : Result PolicyRecord := do
  let raw ← object path json
  let extras := ["localSelector", "parents", "descendants", "audience", "objectDescriptor"].filter
    (fun key => (raw.get? key).isSome)
  let obj ← exactObject path
    (["policyId", "version", "domain", "semantics", "previous", "predicate"] ++ extras) json
  pure {
    policyId := ⟨← nat (path ++ ".policyId") (← field path "policyId" obj)⟩
    version := ← nat (path ++ ".version") (← field path "version" obj)
    domain := ⟨← nat (path ++ ".domain") (← field path "domain" obj)⟩
    semantics := ⟨← nat (path ++ ".semantics") (← field path "semantics" obj)⟩
    previous := (← optional (path ++ ".previous") nat (← field path "previous" obj)).map Digest.mk
    predicate := ← predicate (path ++ ".predicate") (← field path "predicate" obj)
    localSelector := ← match obj.get? "localSelector" with
      | none => pure {} | some value => lawSelector (path ++ ".localSelector") value
    parents := ← match obj.get? "parents" with
      | none => pure [] | some value => list (path ++ ".parents") lawReference value
    descendants := ← match obj.get? "descendants" with
      | none => pure none | some value => optional (path ++ ".descendants") lawComponent value
    audience := ← match obj.get? "audience" with
      | none => pure none | some value => optional (path ++ ".audience") audienceState value
    objectDescriptor := ← match obj.get? "objectDescriptor" with
      | none => pure none
      | some value => (·.map Digest.mk) <$> optional (path ++ ".objectDescriptor") nat value }

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
  | .object, "append" => pure .appendObject
  | .object, "place" => pure .placeObject
  | .account, "observe" => pure .observeAccount
  | .account, "transfer" => pure .transfer
  | .account, "delegate" => pure .delegateAccount
  | .account, "mintAsset" => pure .mintAsset
  | .account, "burnAsset" => pure .burnAsset
  | .program, "observe" => pure .observeProgram
  | .program, "install" => pure .installProgram
  | .program, "delegate" => pure .delegateProgram
  | .program, "installPolicy" => pure .installPolicy
  | .program, "revokeCapability" => pure .revokeCapability
  | .program, "observePayment" => pure .observePayment
  | .program, "tickClock" => pure .tickClock
  | _, _ => failAt path "verb is not defined for this resource kind"

private def capability (kind : ResourceKind) (path : String) (json : Lean.Json) :
    Result (Capability kind) := do
  -- A scope names its targets either explicitly (`targets`) or as a room
  -- (`room`); exactly one of the two keys is accepted.
  let raw ← object path json
  let targetKey := if (raw.get? "room").isSome then "room" else "targets"
  -- K-FIELDS: optional `fields` (absent = every field) and `maxDelta`
  -- (absent = no per-field bound).
  let optionalKeys := ["fields", "maxDelta"].filter fun key => (raw.get? key).isSome
  let names := ["id", "root", "parent", "issuer", "holder", targetKey, "verbs", "maxCost",
    "notBefore", "notAfter", "issuerEpoch", "policyId", "policyEpoch", "ancestors", "channels"] ++
    optionalKeys
  let obj ← exactObject path names json
  let cellField := fun (p : String) (j : Lean.Json) => do
    match CredentialAuthorityEntryCodec.cellFieldOfName (← string p j) with
    | some named => pure named
    | none => failAt p "expected a field: decimal slot, balance:N, code, body or annotations"
  let fields ← match obj.get? "fields" with
    | none => pure none
    | some value => some <$> (List.toFinset <$> list (path ++ ".fields") cellField value)
  let bounds ← match obj.get? "maxDelta" with
    | none => pure ∅
    | some value => List.toFinset <$> list (path ++ ".maxDelta") (fun p j => do
        let bound ← exactObject p ["field", "max"] j
        pure (← cellField (p ++ ".field") (← field p "field" bound),
          ← nat (p ++ ".max") (← field p "max" bound))) value
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
      ← nat (path ++ ".maxCost") (← field path "maxCost" obj), fields, bounds⟩
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

private def renunciation (path : String) (json : Lean.Json) : Result (List UInt8) := do
  let obj ← exactObject path ["subject", "nonce", "kind", "capability"] json
  let command : CapabilityRenounce.Command :=
    { subject := ⟨← nat (path ++ ".subject") (← field path "subject" obj)⟩
      nonce := ← nat (path ++ ".nonce") (← field path "nonce" obj)
      kind := ← resourceKind (path ++ ".kind") (← field path "kind" obj)
      capability := ⟨← nat (path ++ ".capability") (← field path "capability" obj)⟩ }
  pure (CapabilityRenounce.commandCodec.encode command)

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

private def authoredFragment (path : String) (json : Lean.Json) : Result Hyperdocument.AuthoredFragment := do
  let obj ← exactObject path ["ciphertext", "wrapping", "author", "operation", "wrappedBy", "wrappedAt"] json
  pure ⟨← decodeHex (path ++ ".ciphertext") (← field path "ciphertext" obj),
    ← decodeHex (path ++ ".wrapping") (← field path "wrapping" obj),
    ← principal (path ++ ".author") (← field path "author" obj),
    ← identifier (path ++ ".operation") (← field path "operation" obj),
    ← principal (path ++ ".wrappedBy") (← field path "wrappedBy" obj),
    ← identifier (path ++ ".wrappedAt") (← field path "wrappedAt" obj)⟩

private def atomKind (path : String) (json : Lean.Json) : Result Hyperdocument.AtomKind := do
  let (tag, _) ← tagged path json
  match tag with
  | "text" => exactObject path ["type"] json *> pure .text
  | "inlineObject" =>
      let obj ← exactObject path ["type", "schema"] json
      pure (.inlineObject ⟨← nat (path ++ ".schema") (← field path "schema" obj)⟩)
  | "sealedObject" =>
      let obj ← exactObject path ["type", "schema", "fragment"] json
      pure (.sealedObject ⟨← nat (path ++ ".schema") (← field path "schema" obj)⟩
        (← authoredFragment (path ++ ".fragment") (← field path "fragment" obj)))
  | _ => failAt (path ++ ".type") "expected text, inlineObject or sealedObject"

private def transclusionMode (path : String) (json : Lean.Json) :
    Result Hyperdocument.TransclusionMode := do
  match ← string path json with
  | "snapshot" => pure .snapshot | "live" => pure .live
  | _ => failAt path "expected snapshot or live"

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

private def elementOp (path : String) (json : Lean.Json) : Result ContentResource.ElementOp := do
  let (tag, _) ← tagged path json
  match tag with
  | "splice" =>
      let obj ← exactObject path ["type", "index", "child"] json
      pure (.splice (← nat (path ++ ".index") (← field path "index" obj))
        (← identifier (path ++ ".child") (← field path "child" obj)))
  | "move" =>
      let obj ← exactObject path ["type", "child", "index"] json
      pure (.move (← identifier (path ++ ".child") (← field path "child" obj))
        (← nat (path ++ ".index") (← field path "index" obj)))
  | "remove" =>
      let obj ← exactObject path ["type", "child"] json
      pure (.remove (← identifier (path ++ ".child") (← field path "child" obj)))
  | _ => failAt (path ++ ".type") "expected splice, move or remove"

private def markTarget (path : String) (json : Lean.Json) : Result ContentResource.MarkTarget := do
  let (tag, _) ← tagged path json
  match tag with
  | "atom" =>
      let obj ← exactObject path ["type", "atom"] json
      pure (.atom (← identifier (path ++ ".atom") (← field path "atom" obj)))
  | "element" =>
      let obj ← exactObject path ["type", "element"] json
      pure (.element (← identifier (path ++ ".element") (← field path "element" obj)))
  | _ => failAt (path ++ ".type") "noSuchTarget: expected atom or element"

private def markSpec (path : String) (json : Lean.Json) : Result ContentResource.MarkSpec := do
  let (tag, _) ← tagged path json
  match tag with
  | "bold" =>
      let _ ← exactObject path ["type"] json
      pure ContentResource.MarkSpec.bold
  | "italic" =>
      let _ ← exactObject path ["type"] json
      pure ContentResource.MarkSpec.italic
  | "code" =>
      let _ ← exactObject path ["type"] json
      pure ContentResource.MarkSpec.code
  | "heading" =>
      let _ ← exactObject path ["type"] json
      pure ContentResource.MarkSpec.heading
  | "link" =>
      let obj ← exactObject path ["type", "link", "target"] json
      pure (.link (← identifier (path ++ ".link") (← field path "link" obj))
        (← linkTarget (path ++ ".target") (← field path "target" obj)))
  | other =>
      failAt (path ++ ".type") s!"unknownKind: {other} (expected bold, italic, code, heading or link)"

private def annotationBody (path : String) (json : Lean.Json) : Result Hyperdocument.AnnotationBody := do
  match json with
  | .str _ => pure (.inline (← decodeHex path json))
  | _ =>
      let obj ← exactObject path ["type", "fragment"] json
      if (← string (path ++ ".type") (← field path "type" obj)) != "sealed" then
        failAt path "expected sealed annotation body"
      else pure (.sealed (← authoredFragment (path ++ ".fragment") (← field path "fragment" obj)))

private def annotationBefore (path : String) (json : Lean.Json) : Result Hyperdocument.AnnotationRecord := do
  let bytes ← decodeHex path json
  match HyperdocumentCell.annotationRecordStream.toLawful.decode bytes with
  | some value =>
      if HyperdocumentCell.annotationRecordStream.encode value = bytes then pure value
      else failAt path "annotation guard is not canonical"
  | none => failAt path "invalid exact annotation guard"

private def contentAction (path : String) (json : Lean.Json) : Result ContentResource.Action := do
  let (tag, _) ← tagged path json
  match tag with
  | "createDocument" =>
      let obj ← exactObject path ["type", "rootElement", "schema"] json
      pure (.createDocument (← identifier (path ++ ".rootElement") (← field path "rootElement" obj))
        ⟨← nat (path ++ ".schema") (← field path "schema" obj)⟩)
  | "createContainer" =>
      let obj ← exactObject path ["type", "element"] json
      pure (.createContainer (← identifier (path ++ ".element") (← field path "element" obj)))
  | "editElement" =>
      let obj ← exactObject path ["type", "element", "revision", "op"] json
      pure (.editElement ⟨← identifier (path ++ ".element") (← field path "element" obj),
        ← identifier (path ++ ".revision") (← field path "revision" obj),
        ← elementOp (path ++ ".op") (← field path "op" obj)⟩)
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
        (← annotationBody (path ++ ".body") (← field path "body" obj)))
  | "rewrapAtom" =>
      let obj ← exactObject path ["type", "atom", "before", "wrapping"] json
      pure (.rewrapAtom (← identifier (path ++ ".atom") (← field path "atom" obj))
        (← atomRecord (path ++ ".before") (← field path "before" obj))
        (← decodeHex (path ++ ".wrapping") (← field path "wrapping" obj)))
  | "rewrapAnnotation" =>
      let obj ← exactObject path ["type", "annotation", "before", "wrapping"] json
      pure (.rewrapAnnotation (← identifier (path ++ ".annotation") (← field path "annotation" obj))
        (← annotationBefore (path ++ ".before") (← field path "before" obj))
        (← decodeHex (path ++ ".wrapping") (← field path "wrapping" obj)))
  | "unlink" =>
      let obj ← exactObject path ["type", "link"] json
      pure (.unlink (← identifier (path ++ ".link") (← field path "link" obj)))
  | "mark" =>
      let obj ← exactObject path ["type", "mark", "target", "revision", "kind"] json
      pure (.mark (← identifier (path ++ ".mark") (← field path "mark" obj))
        ⟨← markTarget (path ++ ".target") (← field path "target" obj),
          ← identifier (path ++ ".revision") (← field path "revision" obj),
          ← markSpec (path ++ ".kind") (← field path "kind" obj)⟩)
  | "unmark" =>
      let obj ← exactObject path ["type", "mark"] json
      pure (.unmark (← identifier (path ++ ".mark") (← field path "mark" obj)))
  | "transclude" =>
      let obj ← exactObject path ["type", "transclusion", "link", "request"] json
      pure (.transclude (← identifier (path ++ ".transclusion") (← field path "transclusion" obj))
        (← identifier (path ++ ".link") (← field path "link" obj))
        (← transcludeRequest (path ++ ".request") (← field path "request" obj)))
  | _ => failAt (path ++ ".type") "unknown content action"

private def contentCommand (path : String) (json : Lean.Json) : Result ContentResource.Command := do
  let obj ← exactObject path ["actions"] json
  pure ⟨← list (path ++ ".actions") contentAction (← field path "actions" obj)⟩

private def streamRef (path : String) (json : Lean.Json) : Result (Nat × Nat) := do
  let obj ← exactObject path ["cell", "sequence"] json
  pure (← nat (path ++ ".cell") (← field path "cell" obj),
    ← nat (path ++ ".sequence") (← field path "sequence" obj))

private def worldScalarCodec (path : String) (json : Lean.Json) :
    Result WorldKindDescriptor.ScalarCodec := do
  match ← string path json with
  | "nat" => pure .natural
  | "int" => pure .integer
  | "bytes" => pure .bytes
  | _ => failAt path "expected nat, int or bytes"

private def worldDiscipline (path : String) (json : Lean.Json) :
    Result Store.Discipline := do
  match ← string path json with
  | "rom" => pure .rom
  | "ram" => pure .ram
  | "append" => pure .appendOnly
  | _ => failAt path "expected rom, ram or append"

private def worldField (path : String) (json : Lean.Json) : Result WorldKindDescriptor.Field := do
  let obj ← exactObject path ["id", "name", "meaning", "codec", "discipline"] json
  pure ⟨← nat (path ++ ".id") (← field path "id" obj),
    ← string (path ++ ".name") (← field path "name" obj),
    ← string (path ++ ".meaning") (← field path "meaning" obj),
    ← worldScalarCodec (path ++ ".codec") (← field path "codec" obj),
    ← worldDiscipline (path ++ ".discipline") (← field path "discipline" obj)⟩

private def worldDescriptor (path : String) (json : Lean.Json) :
    Result WorldKindDescriptor.Descriptor := do
  let obj ← exactObject path ["kind", "revision", "fields"] json
  let descriptor : WorldKindDescriptor.Descriptor :=
    ⟨← nat (path ++ ".kind") (← field path "kind" obj),
      ← nat (path ++ ".revision") (← field path "revision" obj),
      ← list (path ++ ".fields") worldField (← field path "fields" obj)⟩
  unless descriptor.Valid do
    failAt path "descriptor needs unique field ids/names and nonempty names/meanings"
  pure descriptor

private def worldValue : (codec : WorldKindDescriptor.ScalarCodec) →
    String → Lean.Json → Result codec.Value
  | .natural, path, json => nat path json
  | .integer, path, json => int path json
  | .bytes, path, json => decodeHex path json

private def worldMethodOutput (path : String) (json : Lean.Json) :
    Result WorldKindMethods.OutputBinding := do
  let obj ← exactObject path ["output", "field", "key"] json
  pure ⟨← nat (path ++ ".output") (← field path "output" obj),
    ← nat (path ++ ".field") (← field path "field" obj),
    ← nat (path ++ ".key") (← field path "key" obj)⟩

private def worldMethod (path : String) (json : Lean.Json) : Result WorldKindMethods.Method := do
  let obj ← exactObject path ["name", "program", "outputs"] json
  pure ⟨← string (path ++ ".name") (← field path "name" obj),
    ⟨← nat (path ++ ".program") (← field path "program" obj)⟩,
    ← list (path ++ ".outputs") worldMethodOutput (← field path "outputs" obj)⟩

private def worldMethodJson (method : WorldKindMethods.Method) : Lean.Json :=
  .mkObj [("name", .str method.name), ("program", decimal method.program.value),
    ("outputs", .arr (method.outputs.toArray.map fun output =>
      .mkObj [("output", decimal output.output), ("field", decimal output.field),
        ("key", decimal output.key)]))]

private def worldMethodsJson (value : WorldKindInstance.Instance) : Lean.Json :=
  match WorldKindMethods.tableOf value with
  | none => .null
  | some methods => .arr (methods.toArray.map worldMethodJson)

private def worldDefinition (path : String) (json : Lean.Json) :
    Result WorldKindCell.Definition := do
  let obj ← exactObject path ["descriptor", "defaults"] json
  let descriptor ← worldDescriptor (path ++ ".descriptor") (← field path "descriptor" obj)
  let defaults ← array (path ++ ".defaults") (← field path "defaults" obj)
  let mut store : Store.Store (WorldKindDescriptor.layout descriptor) := 0
  for i in [:defaults.size] do
    let entryPath := s!"{path}.defaults[{i}]"
    let entry ← exactObject entryPath ["field", "key", "value"] defaults[i]!
    let id ← nat (entryPath ++ ".field") (← field entryPath "field" entry)
    let space ← match WorldKindInstance.findField descriptor id with
      | some space => pure space
      | none => failAt (entryPath ++ ".field") "unknown descriptor field"
    let key ← nat (entryPath ++ ".key") (← field entryPath "key" entry)
    let address : Store.Address (WorldKindDescriptor.layout descriptor) := ⟨space, key⟩
    if (store address).isSome then failAt entryPath "duplicate default field/key"
    let raw ← field entryPath "value" entry
    let definition := descriptor.fields.get space
    let value ← if definition.meaning == WorldKindMethods.tableMeaning && raw.getArr?.isOk then do
        unless definition.codec = .bytes ∧ definition.discipline = .rom ∧ key = 0 do
          failAt entryPath "method table must be ROM bytes at key zero"
        let methods ← list (entryPath ++ ".value") worldMethod raw
        unless WorldKindMethods.valid descriptor methods do
          failAt entryPath "ambiguous or invalid method output bindings"
        match WorldKindInstance.decodeValue descriptor space
            (WorldKindDescriptor.ScalarCodec.bytes.stream.encode (WorldKindMethods.encode methods)) with
        | some value => pure value
        | none => failAt entryPath "method table field is not bytes"
      else worldValue definition.codec (entryPath ++ ".value") raw
    store := store.set address (some value)
  let definition : WorldKindCell.Definition :=
    ⟨descriptor, StoreCodec.encode (WorldKindDescriptor.wire descriptor) store⟩
  if descriptor.fields.any (fun field => field.meaning == WorldKindMethods.tableMeaning) then
    let value ← match definition.instantiate with
      | some value => pure value
      | none => failAt path "invalid method-bearing definition"
    if (WorldKindMethods.tableOf value).isNone then
      failAt path "method table requires one canonical ROM bytes slot and unambiguous bindings"
  pure definition

private def worldAction (descriptor : WorldKindDescriptor.Descriptor)
    (path : String) (json : Lean.Json) : Result WorldKindInstance.Action := do
  let (tag, _) ← tagged path json
  let keys ← match tag with
    | "read" => pure ["type", "field", "key", "expected"]
    | "create" => pure ["type", "field", "key", "value"]
    | "write" => pure ["type", "field", "key", "before", "after"]
    | "erase" => pure ["type", "field", "key", "before"]
    | _ => failAt (path ++ ".type") "expected read, create, write or erase"
  let obj ← exactObject path keys json
  let id ← nat (path ++ ".field") (← field path "field" obj)
  let key ← nat (path ++ ".key") (← field path "key" obj)
  let space ← match WorldKindInstance.findField descriptor id with
    | some space => pure space
    | none => failAt (path ++ ".field") "unknown descriptor field"
  let codec := (descriptor.fields.get space).codec
  let value (key : String) : Result (List UInt8) := do
    pure (codec.stream.encode (← worldValue codec (path ++ "." ++ key) (← field path key obj)))
  match tag with
  | "read" =>
      let raw ← field path "expected" obj
      let expected ← if raw.isNull then pure none else some <$> value "expected"
      pure (.read id key expected)
  | "create" => pure (.create id key (← value "value"))
  | "write" => pure (.write id key (← value "before") (← value "after"))
  | "erase" => pure (.erase id key (← value "before"))
  | _ => failAt (path ++ ".type") "unknown world action"

private def worldFieldJson (value : WorldKindDescriptor.Field) : Lean.Json :=
  .mkObj [("id", decimal value.id), ("name", .str value.name), ("meaning", .str value.meaning),
    ("codec", match value.codec with | .natural => "nat" | .integer => "int" | .bytes => "bytes"),
    ("discipline", match value.discipline with | .rom => "rom" | .ram => "ram" | .appendOnly => "append")]

private def worldDescriptorJson (value : WorldKindDescriptor.Descriptor) : Lean.Json :=
  .mkObj [("kind", decimal value.kind), ("revision", decimal value.revision),
    ("fields", .arr (value.fields.toArray.map worldFieldJson))]

private def worldValueJson : (codec : WorldKindDescriptor.ScalarCodec) → codec.Value → Lean.Json
  | .natural, value => decimal value
  | .integer, value => signedDecimal value
  | .bytes, value => hexJson value

private def worldEntriesJson (descriptor : WorldKindDescriptor.Descriptor)
    (store : Store.Store (WorldKindDescriptor.layout descriptor)) : Lean.Json :=
  .arr <| (StoreCodec.entries (WorldKindDescriptor.wire descriptor) store).toArray.map fun entry =>
    .mkObj [("field", decimal (descriptor.fields.get entry.1.1).id),
      ("key", decimal entry.1.2),
      ("value", worldValueJson (descriptor.fields.get entry.1.1).codec entry.2)]

private def worldKindJson (root : Digest) (store : Store.Store WorldKindCell.definitionLayout) :
    Result Lean.Json := do
  let definition ← match store WorldKindCell.definitionAddress with
    | some definition => pure definition
    | none => failAt "view-resource.worldKind" "missing definition"
  let value ← match definition.instantiate with
    | some value => pure value
    | none => failAt "view-resource.worldKind" "invalid definition/defaults"
  pure <| .mkObj [("root", decimal root.value), ("worldKind", .mkObj
    [("descriptor", worldDescriptorJson value.descriptor),
     ("defaults", worldEntriesJson value.descriptor value.store),
     ("methods", worldMethodsJson value)])]

private def worldInstanceJson (root : Digest) (store : Store.Store WorldKindCell.instanceLayout) :
    Result Lean.Json := do
  let value ← match WorldKindCell.instanceAt store with
    | some value => pure value
    | none => failAt "view-resource.worldInstance" "invalid binding/payload"
  let binding ← match store WorldKindCell.descriptorAddress with
    | some binding => pure binding
    | none => failAt "view-resource.worldInstance" "missing birth binding"
  pure <| .mkObj [("root", decimal root.value), ("worldInstance", .mkObj
    [("descriptor", worldDescriptorJson value.descriptor),
     ("kindRoot", decimal binding.kindRoot.value),
     ("entries", worldEntriesJson value.descriptor value.store),
     ("sampleSlots", .arr <| ((WorldKindProjection.stateSlots "before" value ++
       WorldKindProjection.stateSlots "after" value).toArray.map fun slot =>
         Lean.Json.arr #[.str ("world/" ++ slot.1), signedDecimal slot.2])),
     ("methods", worldMethodsJson value)])]

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
  | "append" =>
      let obj ← exactObject path ["type", "topic", "payload", "to", "ref"] json
      let topic ← decodeHex (path ++ ".topic") (← field path "topic" obj)
      let payload ← decodeHex (path ++ ".payload") (← field path "payload" obj)
      let recipient ← optional (path ++ ".to") nat (← field path "to" obj)
      let ref ← optional (path ++ ".ref") streamRef (← field path "ref" obj)
      pure (.append ⟨topic, payload, recipient.map SubjectId.mk, ref⟩)
  | "world" =>
      let obj ← exactObject path ["type", "descriptor", "actions"] json
      let descriptor ← worldDescriptor (path ++ ".descriptor") (← field path "descriptor" obj)
      pure (.world (← list (path ++ ".actions") (worldAction descriptor) (← field path "actions" obj)))
  | "kindDefinition" =>
      let obj ← exactObject path ["type", "definition"] json
      pure (.kindDefinition (← worldDefinition (path ++ ".definition") (← field path "definition" obj)))
  | "computeFunding" =>
      let obj ← exactObject path ["type", "asset", "credits", "expectedPayerBalance", "expectedBookRoot"] json
      pure (.computeFunding ⟨← nat (path ++ ".asset") (← field path "asset" obj),
        ← nat (path ++ ".credits") (← field path "credits" obj),
        ← int (path ++ ".expectedPayerBalance") (← field path "expectedPayerBalance" obj),
        ⟨← nat (path ++ ".expectedBookRoot") (← field path "expectedBookRoot" obj)⟩⟩)
  | "read" =>
      let _ ← exactObject path ["type"] json
      pure .read
  | _ => failAt (path ++ ".type") "expected scalar, content, append, read, world, kindDefinition or computeFunding"

private def audienceRosterEntry (path : String) (json : Lean.Json) :
    Result Minidregg.Theory.ObjectAudienceRoster.Entry := do
  let obj ← exactObject path ["subject", "capability", "deviceSource", "deviceGeneration", "keyCommitment"] json
  pure ⟨← nat (path ++ ".subject") (← field path "subject" obj),
    ← nat (path ++ ".capability") (← field path "capability" obj),
    ← nat (path ++ ".deviceSource") (← field path "deviceSource" obj),
    ← nat (path ++ ".deviceGeneration") (← field path "deviceGeneration" obj),
    ← nat (path ++ ".keyCommitment") (← field path "keyCommitment" obj)⟩

def audienceRoster (path : String) (json : Lean.Json) :
    Result Minidregg.Theory.ObjectAudienceRoster.Roster := do
  let obj ← exactObject path ["object", "epoch", "transition", "entries"] json
  pure ⟨← nat (path ++ ".object") (← field path "object" obj),
    ← nat (path ++ ".epoch") (← field path "epoch" obj),
    ← nat (path ++ ".transition") (← field path "transition" obj),
    ← list (path ++ ".entries") audienceRosterEntry (← field path "entries" obj)⟩

private def commandTarget (path : String) (json : Lean.Json) :
    Result DeclaredResourceController.Target := do
  let raw ← object path json
  let extras := ["audienceEpoch", "audienceRoster"].filter (fun key => (raw.get? key).isSome)
  let obj ← exactObject path
    (["kind", "target", "capability", "observeCapability", "schemaVersion",
      "expectedTargetRoot", "payload"] ++ extras) json
  pure {
    kind := ← resourceKind (path ++ ".kind") (← field path "kind" obj)
    target := ← nat (path ++ ".target") (← field path "target" obj)
    capability := ⟨← nat (path ++ ".capability") (← field path "capability" obj)⟩
    observeCapability := (← optional (path ++ ".observeCapability") nat
      (← field path "observeCapability" obj)).map CapabilityId.mk
    schemaVersion := ← nat (path ++ ".schemaVersion") (← field path "schemaVersion" obj)
    expectedTargetRoot := ⟨← nat (path ++ ".expectedTargetRoot") (← field path "expectedTargetRoot" obj)⟩
    payload := ← targetPayload (path ++ ".payload") (← field path "payload" obj)
    audienceEpoch := ← match obj.get? "audienceEpoch" with
      | none => pure none | some value => optional (path ++ ".audienceEpoch") nat value
    audienceRoster := ← match obj.get? "audienceRoster" with
      | none => pure none | some value => optional (path ++ ".audienceRoster") audienceRoster value }

def runClaim (path : String) (json : Lean.Json) : Result Kernel.Run.RunClaim := do
  let obj ← exactObject path ["programId", "sample", "output", "steps"] json
  pure ⟨⟨← nat (path ++ ".programId") (← field path "programId" obj)⟩,
    ← decodeHex (path ++ ".sample") (← field path "sample" obj),
    ← decodeHex (path ++ ".output") (← field path "output" obj),
    ← nat (path ++ ".steps") (← field path "steps" obj)⟩

private def command (path : String) (json : Lean.Json) : Result DeclaredResourceController.Command := do
  let claimed := ((← object path json).get? "run").isSome
  let obj ← exactObject path
    (if claimed then ["subject", "nonce", "targets", "run"] else ["subject", "nonce", "targets"]) json
  let run ← if claimed then do pure (some (← runClaim (path ++ ".run") (← field path "run" obj)))
    else pure none
  pure {
    subject := ⟨← nat (path ++ ".subject") (← field path "subject" obj)⟩
    nonce := ← nat (path ++ ".nonce") (← field path "nonce" obj)
    targets := ← list (path ++ ".targets") commandTarget (← field path "targets" obj)
    run := run }

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
      let raw ← object path json
      let obj ← exactObject path (["type", "subject", "control", "declaration"] ++
        if (raw.get? "audienceRoster").isSome then ["audienceRoster"] else []) json
      let declaration ← policyInstall (path ++ ".declaration") (← field path "declaration" obj)
      let subject : SubjectId := ⟨← nat (path ++ ".subject") (← field path "subject" obj)⟩
      let control : CapabilityId := ⟨← nat (path ++ ".control") (← field path "control" obj)⟩
      let bytes := PolicyInstallController.declarationCodec.encode declaration
      match obj.get? "audienceRoster" with
      | none | some .null => pure (.install subject control bytes)
      | some value => pure (.installWithRoster subject control bytes
          (Compiler.ObjectAudienceRoster.encode (← audienceRoster (path ++ ".audienceRoster") value)))
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
  | "renounce" =>
      let obj ← exactObject path ["type", "command"] json
      let bytes ← decodeHex (path ++ ".command") (← field path "command" obj)
      match CapabilityRenounce.commandCodec.decode bytes with
      | some value => pure (.renounce (CapabilityRenounce.commandCodec.encode value))
      | none => failAt (path ++ ".command") "noncanonical renounce command"
  | "renounce-source" =>
      let obj ← exactObject path ["type", "command"] json
      pure (.renounce (← renunciation (path ++ ".command") (← field path "command" obj)))
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
        -- `since` and `at` carry a height, `tail` a window (start, count); the
        -- other views carry nothing.
        let hasHeight := (purposeJson.getObjVal? "height").toOption.isSome
        let windowed := (purposeJson.getObjVal? "start").toOption.isSome
        let p ← exactObject at_ (["type", "kind", "target", "view"] ++
          (if hasHeight then ["height"] else []) ++ (if windowed then ["start", "count"] else []))
          purposeJson
        let view ← match ← string (at_ ++ ".view") (← field at_ "view" p), hasHeight, windowed with
          | "resource", false, false => pure QueryView.resource
          | "resource-scope", false, false => pure .resourceScope
          | "policy", false, false => pure .policy
          | "capability", false, false => pure .capability
          | "who", false, false => pure .who
          | "backlinks", false, false => pure .backlinks
          | "links", false, false => pure .links
          | "since", true, false => do pure (.since (← nat (at_ ++ ".height") (← field at_ "height" p)))
          | "at", true, false => do pure (.atHeight (← nat (at_ ++ ".height") (← field at_ "height" p)))
          | "tail", false, true => do
              pure (.tail (← nat (at_ ++ ".start") (← field at_ "start" p))
                (← nat (at_ ++ ".count") (← field at_ "count" p)))
          | _, _, _ => failAt (at_ ++ ".view") "unknown query view, or a height/window on a view that takes none"
        pure (.query ⟨← resourceKind (path ++ ".purpose.kind") (← field (path ++ ".purpose") "kind" p),
          ← nat (path ++ ".purpose.target") (← field (path ++ ".purpose") "target" p), view⟩)
    | _ => failAt (path ++ ".purpose.type") "expected prepare or query"
  pure ⟨⟨← nat (path ++ ".subject") (← field path "subject" obj)⟩,
    ← nat (path ++ ".nonce") (← field path "nonce" obj), purpose,
    ← list (path ++ ".grants") grant (← field path "grants" obj)⟩

private def keyRecord (path : String) (json : Lean.Json) : Result KeyRecord := do
  let obj ← exactObject path ["keyId", "keyEpoch", "algorithm", "subject", "publicKey",
    "activeFrom", "activeUntil", "nextKeyDigest"] json
  let nextKeyDigest ← match ← field path "nextKeyDigest" obj with
    | .null => pure none
    | value => pure (some ⟨← nat (path ++ ".nextKeyDigest") value⟩)
  pure ⟨← nat (path ++ ".keyId") (← field path "keyId" obj),
    ← nat (path ++ ".keyEpoch") (← field path "keyEpoch" obj),
    ← nat (path ++ ".algorithm") (← field path "algorithm" obj),
    ← nat (path ++ ".subject") (← field path "subject" obj),
    ← decodeHex (path ++ ".publicKey") (← field path "publicKey" obj),
    ← nat (path ++ ".activeFrom") (← field path "activeFrom" obj),
    ← nat (path ++ ".activeUntil") (← field path "activeUntil" obj),
    nextKeyDigest⟩

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

private def clockTicker (path : String) (json : Lean.Json) : Result NativeHostGenesis.ClockTicker := do
  let obj ← exactObject path ["subject", "capability"] json
  pure ⟨⟨← nat (path ++ ".subject") (← field path "subject" obj)⟩,
    ⟨← nat (path ++ ".capability") (← field path "capability" obj)⟩⟩

private def genesis (path : String) (json : Lean.Json) : Result NativeHostGenesis.Config := do
  let names := ["domain", "factoryId", "resourceBookId", "authorityCellId", "federation",
    "tariffBase", "tariffPerBirth", "tariffPerGrant", "tariffPerInitialPayloadByte",
    "collector", "asset", "expectedSemantics", "issuerEpoch", "genesisHeight",
    "factoryPredicate", "enrollments", "factoryControllerSubject",
    "factoryControllerCapability", "meterAllowance", "clockTickers", "tailBound"]
  let observed := (json.getObjVal? "payObserver").toOption.isSome
  let obj ← exactObject path (if observed then names ++ ["payObserver"] else names) json
  let payObserver ← if observed then do
      let observerPath := path ++ ".payObserver"
      let observer ← exactObject observerPath
        ["subject", "capability", "controlCapability", "enrolCapability"]
        (← field path "payObserver" obj)
      pure (some (⟨⟨← nat (observerPath ++ ".subject") (← field observerPath "subject" observer)⟩,
        ⟨← nat (observerPath ++ ".capability") (← field observerPath "capability" observer)⟩,
        ⟨← nat (observerPath ++ ".controlCapability")
          (← field observerPath "controlCapability" observer)⟩,
        ⟨← nat (observerPath ++ ".enrolCapability")
          (← field observerPath "enrolCapability" observer)⟩⟩ :
          NativeHostGenesis.PayObserver))
    else pure none
  let tailBound ← nat (path ++ ".tailBound") (← field path "tailBound" obj)
  unless 0 < tailBound do
    throw s!"{path}.tailBound must be positive: with L = 0 no record but a certify is ever admitted"
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
    meterAllowance := ← charge (path ++ ".meterAllowance") (← field path "meterAllowance" obj)
    payObserver := payObserver
    clockTickers := ← list (path ++ ".clockTickers") clockTicker (← field path "clockTickers" obj)
    tailBound := tailBound }

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

private def grainWorkerClause (subject : Nat) (generation : Int) : Minidregg.Pred.Pred :=
  .all [.eq "request/subject" (Int.ofNat subject), AgentGrain.witnessCaveat generation]

private def grainPolicy (owner : Nat) (worker : Option (List Nat × Int)) : Minidregg.Pred.Pred :=
  let base := AgentGrain.policy (.eq "request/subject" (Int.ofNat owner))
  match worker with
  | none => base
  | some ([subject], generation) => .all [base, .any [
      .eq "request/subject" (Int.ofNat owner),
      .memberOf "request/verb" [1, 3],
      AgentGrain.refillPolicy,
      grainWorkerClause subject generation]]
  | some (subjects, generation) => .all [base, .any <|
      [.eq "request/subject" (Int.ofNat owner), .memberOf "request/verb" [1, 3],
        AgentGrain.refillPolicy] ++
        subjects.map (fun subject => grainWorkerClause subject generation)]

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

private def factoryTemplate (path : String) (json : Lean.Json) :
    Result CanonicalRuntimeProfile.FactoryTemplate := do
  let raw ← object path json
  let slackField := if (raw.get? "birthSlack").isSome then ["birthSlack"] else []
  let templateObj ← exactObject path (["issuer", "ownerBudget", "lifetime"] ++ slackField) json
  let birthSlack ← match templateObj.get? "birthSlack" with
    | none => pure CanonicalRuntimeProfile.defaultBirthSlack
    | some encoded => nat (path ++ ".birthSlack") encoded
  pure ⟨⟨← nat (path ++ ".issuer") (← field path "issuer" templateObj)⟩,
    ← nat (path ++ ".ownerBudget") (← field path "ownerBudget" templateObj),
    ← nat (path ++ ".lifetime") (← field path "lifetime" templateObj), birthSlack⟩

private def birthRootCapability {kind : ResourceKind}
    (profile : CanonicalRuntimeProfile.Profile NativeHostProfile.Field)
    (source : NativeHostGenesis.Config) (height : Nat)
    (identifier : CapabilityId) (owner : SubjectId) (target : Nat)
    (verbs : Finset (Verb kind)) : Capability kind :=
  { NativeHostGenesis.rootCapability profile source kind identifier owner target verbs with
    notBefore := height, notAfter := height + profile.template.lifetime }

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

private def withBlinding (path : String) (blinding : Option Nat)
    (cell : PackedCell CanonicalCellRegistry.registry) :
    Result (PackedCell CanonicalCellRegistry.registry) := do
  let some value := blinding | pure cell
  unless 0 < value ∧ value < 2 ^ 256 do
    throw s!"{path}.blinding: must be a nonzero 256-bit value"
  match cell with
  | ⟨.declaredObject, payload⟩ => pure ⟨.declaredObject, CellState.materialize _
      (payload.logical.set EffectDeclaration.StateKey.blinding.address (some (Int.ofNat value)))⟩
  | ⟨.accountMetadata, payload⟩ => pure ⟨.accountMetadata, CellState.materialize _
      (payload.logical.set EffectDeclaration.StateKey.blinding.address (some (Int.ofNat value)))⟩
  | ⟨.declaredProgram, payload⟩ => pure ⟨.declaredProgram, CellState.materialize _
      (payload.logical.set EffectDeclaration.StateKey.blinding.address (some (Int.ofNat value)))⟩
  | ⟨.content, payload⟩ => pure ⟨.content, CellState.materialize _
      (payload.logical.set ⟨.blinding, ()⟩ (some (⟨value⟩ : Digest)))⟩
  | _ => throw s!"{path}.blinding: this storage carries no blinding"

private def birthParts (path : String)
    (profile : CanonicalRuntimeProfile.Profile NativeHostProfile.Field)
    (source : NativeHostGenesis.Config) (height : Nat) (json : Lean.Json)
    (authority : Option AuthState := none)
    (providerRoutes : List (Nat × ProviderMetering.Schedule) := [])
    (lineage : Option (CapabilityId → Option (Finset CapabilityId)) := none) : Result BirthParts := do
  let raw ← object path json
  let storage ← string (path ++ ".storage") (← field path "storage" raw)
  let worker ← if storage = "grain" then grainWorker path raw else pure none
  let roomField := if (raw.get? "room").isSome then ["room", "placement"] else []
  let blindingField := if (raw.get? "blinding").isSome then ["blinding"] else []
  -- K-FIELD-CLOSURE: a declared resource names the fields it may hold, or
  -- `"open"`; absent, it declares none and holds none.
  let fieldsField := if storage = "declared" ∧ (raw.get? "fields").isSome then ["fields"] else []
  let worldFields := if storage = "world-kind" then ["definition"]
    else if storage = "world-instance" then
      ["definition", "fromKind", "expectedKindRoot", "expectedKindRevision"] else []
  let obj ← exactObject path
    ((if storage = "grain" then
      ["kind", "storage", "target", "owner", "ownerCapability", "controlCapability", "budget"] ++
        (if worker.isSome then grainWorkerFields raw else [])
    else if storage = "nock" then
      ["kind", "storage", "program", "owner", "ownerCapability", "controlCapability", "predicate"]
    else
      ["kind", "storage", "target", "owner", "ownerCapability", "controlCapability", "predicate"]) ++
      roomField ++ blindingField ++ fieldsField ++ worldFields) json
  let declaration : Minidregg.Kernel.FieldClosure.FieldSet ← match obj.get? "fields" with
    | none => pure (.closed [])
    | some (.str "open") => pure .open
    | some value => .closed <$> list (path ++ ".fields") nat value
  let room ← match obj.get? "room" with
    | none => pure none
    | some value => some <$> nat (path ++ ".room") value
  let placement ← match obj.get? "placement" with
    | none => pure none
    | some value => (some ∘ CapabilityId.mk) <$> nat (path ++ ".placement") value
  let kind ← resourceKind (path ++ ".kind") (← field path "kind" obj)
  unless storage = "declared" ∨ storage = "content" ∨ storage = "grain" ∨ storage = "stream" ∨
      storage = "nock" ∨ storage = "job" ∨ storage = "world-kind" ∨ storage = "world-instance" do
    throw s!"{path}.storage: expected declared, content, grain, stream, nock, job, world-kind or world-instance"
  unless (storage = "declared" ∧ (kind = .object ∨ kind = .account)) ∨
      ((storage = "content" ∨ storage = "grain" ∨ storage = "stream" ∨ storage = "nock" ∨
        storage = "job" ∨ storage = "world-kind" ∨ storage = "world-instance") ∧ kind = .object) do
    throw s!"{path}: declared storage is object/account; content, grain, stream, nock, job and world storage are object"
  -- A Nock program cell has no chosen identifier: it is born at its content
  -- address, so the request names the program and the source derives the target.
  let program : Option NockProgramCodec.Program ← if storage = "nock" then do
      let bytes ← decodeHex (path ++ ".program") (← field path "program" obj)
      match NockProgramCodec.programCodec.decode bytes with
      | some program => pure (some program)
      | none => failAt (path ++ ".program") "noncanonical DREGG/PROGRAM/v1 bytes"
    else pure none
  let target ← match program with
    | some program => pure (CanonicalCellRegistry.programCellId source.deployment.domain program)
    | none => nat (path ++ ".target") (← field path "target" obj)
  let owner := SubjectId.mk (← nat (path ++ ".owner") (← field path "owner" obj))
  let ownerId := CapabilityId.mk
    (← nat (path ++ ".ownerCapability") (← field path "ownerCapability" obj))
  let controlId := CapabilityId.mk
    (← nat (path ++ ".controlCapability") (← field path "controlCapability" obj))
  let schedule := if storage = "grain" then providerRoutes.lookup target else none
  let rulePredicate ← if storage = "grain" then
      pure <| match schedule with
        | some routes => ProviderRoute.policy routes (grainPolicy owner.value worker)
        | none => grainPolicy owner.value worker
    else predicate (path ++ ".predicate") (← field path "predicate" obj)
  let rule := NativeHostGenesis.policy profile source target rulePredicate
  let cell : PackedCell CanonicalCellRegistry.registry ←
    if let some program := program then
      pure (CanonicalCellRegistry.programCell program)
    else if storage = "world-kind" then
      let definition ← worldDefinition (path ++ ".definition") (← field path "definition" obj)
      unless definition.descriptor.kind = target do
        failAt (path ++ ".definition.descriptor.kind") "must equal the newborn target"
      let store := (0 : Store.Store WorldKindCell.definitionLayout).set
        WorldKindCell.definitionAddress (some definition)
      pure ⟨.worldKind, CellState.materialize WorldKindCell.definitionMaterializer store⟩
    else if storage = "world-instance" then
      let definition ← worldDefinition (path ++ ".definition") (← field path "definition" obj)
      let fromKind ← nat (path ++ ".fromKind") (← field path "fromKind" obj)
      let revision ← nat (path ++ ".expectedKindRevision") (← field path "expectedKindRevision" obj)
      let expectedRoot : Digest := ⟨← nat (path ++ ".expectedKindRoot") (← field path "expectedKindRoot" obj)⟩
      unless definition.descriptor.kind = fromKind ∧ definition.descriptor.revision = revision do
        failAt (path ++ ".definition") "descriptor differs from selected kind/revision"
      let definitionStore := (0 : Store.Store WorldKindCell.definitionLayout).set
        WorldKindCell.definitionAddress (some definition)
      let definitionCell := CellState.materialize WorldKindCell.definitionMaterializer definitionStore
      unless definitionCell.root = expectedRoot do
        failAt (path ++ ".expectedKindRoot") "supplied definition does not reproduce signed kind root"
      let value ← match definition.instantiate with
        | some value => pure value
        | none => failAt (path ++ ".definition") "invalid defaults"
      pure ⟨.worldInstance, CellState.materialize WorldKindCell.instanceMaterializer
        (WorldKindCell.instanceOf expectedRoot value)⟩
    else if storage = "content" then
      pure ⟨.content, CellState.materialize HyperdocumentCell.contentMaterializer ContentResource.initialStore⟩
    else if storage = "stream" then
      pure ⟨.stream, CellState.materialize StreamCell.headMaterializer
        (StreamCell.headStore StreamCell.emptyRoomHead)⟩
    else if storage = "grain" then
      let budget ← nat (path ++ ".budget") (← field path "budget" obj)
      pure ⟨.declaredObject, CellState.materialize DeclaredEffectCell.materializer
        (if schedule.isSome then ProviderRoute.initialStore target budget
         else AgentGrain.initialStore target budget)⟩
    else pure (NativeHostGenesis.declaredCell source target (kind = .account) declaration)
  let blinding ← match obj.get? "blinding" with
    | none => pure none
    | some value => some <$> nat (path ++ ".blinding") value
  let cell ← withBlinding path blinding cell
  let item : ResourceBirth.BirthItem CanonicalCellRegistry.registry :=
    ⟨⟨target, CellSlot.root CanonicalCellRegistry.registry .absent, cell⟩, kind, owner, room, placement⟩
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
  -- A room birth's grants carry the creator's placing capability and its
  -- ancestors (`ResourceBirthPolicyController.Concrete.BornLineage`): a kick
  -- that revokes that grant takes down the born cell's owner and control
  -- grants and every delegation of them. Offline authoring (no loaded
  -- authority) leaves them empty and the receiver refuses a room birth; so
  -- does a placement that names no stored capability (the room gate refuses
  -- it first, `notRoomMember … noGrant`).
  let ancestors : Finset CapabilityId := match placement, lineage with
    | some named, some find => ((find named).map (insert named)).getD ∅
    | _, _ => ∅
  let ownerGrant : ResourceBirth.AuthorityGrant := match ownerGrant with
    | ⟨kind, stored⟩ => ⟨kind, { stored with head := { stored.head with ancestors := ancestors } }⟩
  let control : Capability .program := { control with ancestors := ancestors }
  pure ⟨item, ownerGrant, ⟨.program, ⟨control, []⟩⟩,
    ⟨rule.policyId, PolicyRecordCodec.digest rule, PolicyRecordCodec.encode rule⟩⟩

private def birth (path : String) (json : Lean.Json)
    (grainBirthTariff : Option NativeHost.GrainBirthTariffPin := none)
    (deployed : Option NativeHost.Config := none)
    (currentHeight : Option Nat := none)
    (authority : Option AuthState := none)
    (providerRoutes : List (Nat × ProviderMetering.Schedule) := [])
    (lineage : Option (CapabilityId → Option (Finset CapabilityId)) := none) : Result Draft := do
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
  let template ← factoryTemplate (path ++ ".template") (← field path "template" obj)
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
    (fun itemPath value => birthParts itemPath profile source height value authority
      providerRoutes lineage)
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

def birthIntentFrom (path : String) (json : Lean.Json)
    (authorBirth : String → Lean.Json → Result Draft) : Result Intent := do
  let obj ← exactObject path ["subject", "nonce", "birth", "grants"] json
  pure ⟨⟨← nat (path ++ ".subject") (← field path "subject" obj)⟩,
    ← nat (path ++ ".nonce") (← field path "nonce" obj),
    .prepare (← authorBirth (path ++ ".birth") (← field path "birth" obj)),
    ← list (path ++ ".grants") grant (← field path "grants" obj)⟩

private def birthIntent (path : String) (json : Lean.Json)
    (deployed : Option NativeHost.Config := none)
    (providerRoutes : List (Nat × ProviderMetering.Schedule) := []) : Result Intent :=
  birthIntentFrom path json (fun birthPath source =>
    birth birthPath source none deployed none none providerRoutes)

def author (kind : String) (json : Lean.Json)
    (deployed : Option NativeHost.Config := none)
    (providerRoutes : List (Nat × ProviderMetering.Schedule) := []) : Result (List UInt8) :=
  match kind with
  | "observation-batch" => do
      let reads ← list "$" decodeHex json
      unless NativeObservationCodec.validBatch reads do
        failAt "$" "observation batch requires 1 through 16 reads"
      let bytes := NativeObservationCodec.batchCodec.encode reads
      unless bytes.length ≤ NativeObservationCodec.maxBatchBytes do
        failAt "$" "observation batch exceeds its bounded presentation size"
      pure bytes
  | "predicate" => NativeHostGenesis.predicateStream.encode <$> predicate "$" json
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
  | "renunciation" => renunciation "$" json
  | "renunciation-draft" => do
      let bytes ← renunciation "$" json
      pure (draftCodec.encode (.renounce bytes))
  | "birth" => draftCodec.encode <$> birth "$" json none deployed none none providerRoutes
  | "birth-intent" => intentCodec.encode <$> birthIntent "$" json deployed providerRoutes
  | "content" => ContentResource.commandCodec.encode <$> contentCommand "$" json
  | "resource" | "joint" => DeclaredResourceController.commandCodec.encode <$> command "$" json
  | "joint-draft" => do
      let source ← command "$" json
      pure (draftCodec.encode (.invoke (DeclaredResourceController.commandCodec.encode source)))
  | "draft" => draftCodec.encode <$> draft "$" json
  | "intent" => intentCodec.encode <$> intent "$" json
  | _ => failAt "kind" "unsupported ordinary source-agreement grammar"


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
  | .installWithRoster subject control bytes roster => .mkObj
      [("type", "install-with-roster"), ("subject", decimal subject.value),
       ("control", decimal control.value), ("declaration", hexJson bytes),
       ("rosterBytes", hexJson roster)]
  | .delegate bytes => .mkObj [("type", "delegate"), ("command", hexJson bytes)]
  | .revoke bytes => .mkObj [("type", "revoke"), ("command", hexJson bytes)]
  | .renounce bytes => .mkObj [("type", "renounce"), ("command", hexJson bytes)]

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

private def planJson (plan : SigningPlan) : Lean.Json := .mkObj
  [("domain", decimal plan.domain.value), ("semantics", decimal plan.semantics.value),
   ("worldRoot", decimal plan.worldRoot.value), ("height", decimal plan.height),
   ("finalizedDraft", draftJson plan.finalizedDraft),
   ("slots", .arr <| plan.slots.toArray.map fun slot => .mkObj
     [("role", decimal slot.role), ("index", decimal slot.index),
      ("header", hexJson slot.header), ("signing", signedHeaderJson slot.header)])]

private def intentJson (value : Intent) : Lean.Json := .mkObj
  [("subject", decimal value.subject.value), ("nonce", decimal value.nonce),
   ("purpose", match value.purpose with
     | .prepare d => .mkObj [("type", "prepare"), ("draft", draftJson d)]
     | .query q => .mkObj (([("type", "query"),
       ("kind", match q.kind with | .object => "object" | .account => "account" | .program => "program"),
       ("target", decimal q.target),
       ("view", match q.view with
         | .resource => "resource" | .resourceScope => "resource-scope" | .policy => "policy" | .capability => "capability"
         | .who => "who" | .since _ => "since" | .atHeight _ => "at"
         | .tail _ _ => "tail" | .backlinks => "backlinks" | .links => "links")] : List (String × Lean.Json)) ++
       (match q.view with
         | .since h | .atHeight h => [("height", decimal h)]
         | .tail start count => [("start", decimal start), ("count", decimal count)]
         | _ => []))),
   ("grants", .arr <| value.grants.toArray.map fun g => .mkObj
     [("kind", match g.kind with | .object => "object" | .account => "account" | .program => "program"),
      ("target", decimal g.target), ("capability", decimal g.capability.value)])]

private def challengeJson (value : Challenge) : Lean.Json := .mkObj
  [("intent", intentJson value.intent), ("domain", decimal value.domain.value),
   ("semantics", decimal value.semantics.value), ("federation", decimal value.federation.value),
   ("worldRoot", decimal value.worldRoot.value),
   ("authorityRoot", decimal value.authorityRoot.value), ("height", decimal value.height),
   ("clock", .mkObj [("now", decimal value.clockNow),
     ("day", decimal (value.clockNow / Kernel.ClockCell.secondsPerDay)),
     ("slot", decimal value.clockSlot)]),
   ("headers", .arr <| value.headers.toArray.map hexJson),
   ("signing", .arr <| value.headers.toArray.map signedHeaderJson),
   ("intentSignature", hexJson value.intentSignature)]

private def lawLeafJson (leaf : LawLeaf) : Lean.Json :=
  let value : Option Int → Lean.Json := fun
    | some v => signedDecimal v
    | none => .null
  .mkObj [("path", .arr (leaf.path.toArray.map decimal)), ("clause", predicateJson leaf.clause),
    ("text", .str (LawLeaf.renderClause leaf.clause)), ("before", value leaf.before),
    ("after", value leaf.after)]

private def outcomeJson : Outcome → Lean.Json
  | .confirmed kind receipt =>
      let confirmation : Lean.Json := match kind with
        | .installed => "installed"
        | .recoveredAfterUncertainResponse => "recoveredAfterUncertainResponse"
        | .replayed => "replayed"
      .mkObj [("type", "confirmed"), ("confirmation", confirmation),
      ("transactionId", decimal receipt.transactionId.value), ("eventId", decimal receipt.eventId.value),
      ("acceptedCount", decimal receipt.acceptedCount), ("worldRoot", decimal receipt.worldRoot.value)]
  | .refused .tailBound phase detail none => .mkObj [("type", "refused"),
      ("reason", RefusalReason.tailBound.name), ("phase", hexJson phase), ("detail", hexJson detail),
      ("explain", .str s!"head/height <= certified/height + L fails: {(String.fromUTF8? (ByteArray.mk detail.toArray)).getD "?"}; certify (mini checkpoint) to resume")]
  | .refused reason phase detail none => .mkObj [("type", "refused"), ("reason", reason.name),
      ("phase", hexJson phase), ("detail", hexJson detail)]
  | .refused reason phase detail (some leaf) => .mkObj [("type", "refused"), ("reason", reason.name),
      ("phase", hexJson phase), ("detail", hexJson detail), ("leaf", lawLeafJson leaf),
      ("explain", .str (leaf.explain reason))]
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
  | .blinding => .mkObj [("type", "blinding")]
  -- The declaration renders without a `field` member: a reader selecting a
  -- field's value by `key.field` never matches a declaration entry.
  | .fieldDeclared object field => .mkObj [("type", "declared"),
      ("resource", decimal object.value), ("declares", decimal field.value)]
  | .fieldsOpen object => .mkObj [("type", "open"), ("resource", decimal object.value)]

private def isDeclarationKey : Minidregg.Theory.EffectDeclaration.StateKey → Bool
  | .fieldDeclared _ _ | .fieldsOpen _ => true
  | _ => false

private def declaredCellJson (root : Digest)
    (store : Store.Store EffectDeclaration.effectLayout) : Lean.Json :=
  let all := StoreCodec.entries DeclaredEffectCell.wire store
  let entries := all.filter fun entry => !isDeclarationKey entry.1.2
  let isOpen := all.any fun entry => match entry.1.2 with
    | .fieldsOpen _ => true
    | _ => false
  let declared := all.filterMap fun entry => match entry.1.2 with
    | .fieldDeclared _ field => some (decimal field.value)
    | _ => none
  let base := [("root", decimal root.value),
    ("entries", .arr <| entries.toArray.map fun entry => .mkObj
      [("key", stateKeyJson entry.1.2), ("value", signedDecimal (entry.2 : Int))]),
    ("declaration", if isOpen then "open" else .arr declared.toArray)]
  let grain := entries.findSome? fun entry => match entry.1.2 with
    | .objectField task field => if field.value = 0 then some task.value else none
    | _ => none
  match grain with
  | none => .mkObj base
  | some task => match AgentGrain.readState task store with
    | none => .mkObj base
    | some state => .mkObj <| base ++ [("grain", .mkObj
        ([("task", decimal task), ("generation", signedDecimal state.generation),
         ("status", signedDecimal state.status), ("remaining", signedDecimal state.remaining),
         ("reserved", signedDecimal state.reserved)] ++
         (match DeclaredFields.read task ProviderRoute.routeField store with
          | some route => [("route", signedDecimal route)]
          | none => [])))]

private def principalJson (value : Hyperdocument.PrincipalRef) : Lean.Json := .mkObj
  [("subject", decimal value.subject.value),
   ("capabilityKind", match value.capabilityKind with
     | .object => "object" | .account => "account" | .program => "program"),
   ("capability", decimal value.capabilityId.value)]

private def authoredFragmentJson (fragment : Hyperdocument.AuthoredFragment) : Lean.Json :=
  .mkObj [("ciphertext", hexJson fragment.ciphertext), ("wrapping", hexJson fragment.wrapping),
    ("author", principalJson fragment.author), ("operation", decimal fragment.operation.digest.value),
    ("wrappedBy", principalJson fragment.wrappedBy), ("wrappedAt", decimal fragment.wrappedAt.digest.value)]

private def atomKindJson : Hyperdocument.AtomKind → Lean.Json
  | .text => .mkObj [("type", "text")]
  | .inlineObject schema => .mkObj [("type", "inlineObject"), ("schema", decimal schema.value)]
  | .sealedObject schema fragment => .mkObj [("type", "sealedObject"), ("schema", decimal schema.value), ("fragment", authoredFragmentJson fragment)]

private def optionalOperationJson (value : Option Hyperdocument.OperationId) : Lean.Json :=
  value.map (fun id => decimal id.digest.value) |>.getD .null

private def modeJson : Hyperdocument.TransclusionMode → Lean.Json
  | .snapshot => "snapshot"
  | .live => "live"

private def identifierJson {version : Hyperdocument.CodecVersion} {domain : Hyperdocument.IdDomain}
    (value : Hyperdocument.Identifier version domain) : Lean.Json :=
  decimal value.digest.value

private def optionalIdentifierJson {version : Hyperdocument.CodecVersion}
    {domain : Hyperdocument.IdDomain} :
    Option (Hyperdocument.Identifier version domain) → Lean.Json
  | some value => identifierJson value
  | none => .null

private def deathJson : Hyperdocument.EndpointDeathPolicy → Lean.Json
  | .invalidate => "invalidate"
  | .keepTombstone => "keepTombstone"
  | .preferPrevious => "preferPrevious"
  | .preferNext => "preferNext"
  | .preferPreviousThenNext => "preferPreviousThenNext"
  | .preferNextThenPrevious => "preferNextThenPrevious"

private def stablePointJson (point : Hyperdocument.StablePoint) : Lean.Json := .mkObj
  [("run", identifierJson point.run), ("neighbor", optionalIdentifierJson point.neighbor),
   ("bias", match point.bias with | .before => "before" | .after => "after"),
   ("death", deathJson point.death)]

private def stableRangeJson (range : Hyperdocument.StableRange) : Lean.Json := .mkObj
  [("start", stablePointJson range.start), ("finish", stablePointJson range.finish)]

private def linkTargetJson : Hyperdocument.LinkTarget → Lean.Json
  | .document target => .mkObj [("type", "document"), ("id", identifierJson target)]
  | .element target => .mkObj [("type", "element"), ("id", identifierJson target)]
  | .range document range => .mkObj [("type", "range"), ("document", identifierJson document),
      ("range", stableRangeJson range)]
  | .transclusion target _ => .mkObj [("type", "transclusion"), ("id", identifierJson target)]
  | .external scheme authority path => .mkObj [("type", "external"),
      ("scheme", hexJson scheme), ("authority", hexJson authority), ("path", hexJson path)]

private def openingJson (opening : ContentResource.RangeOpening) : Lean.Json :=
  .mkObj [("source", decimal opening.source),
    ("range", stableRangeJson opening.range),
    ("pins", .arr <| opening.pins.toArray.map fun pin =>
      .mkObj [("atom", decimal pin.1.digest.value), ("revision", decimal pin.2.digest.value)]),
    ("atoms", decimal opening.pins.length), ("height", decimal opening.height)]

private def transclusionRecordJson (record : Hyperdocument.TransclusionRecord) : List (String × Lean.Json) :=
  [("host", decimal record.hostDocument.digest.value),
   ("mode", modeJson record.reference.mode),
   ("opening", ((ContentResource.openingOfReference record.reference).map openingJson).getD .null),
   ("reference", decimal record.reference.referenceRoot.value),
   ("disclosurePolicy", decimal record.disclosurePolicy.value)] ++ SourceAgreementLegacyView.referenceFields record.reference

private def elementBodyJson : Hyperdocument.ElementBody → Lean.Json
  | .container children => .mkObj [("type", "container"),
      ("children", .arr <| children.toArray.map fun child => decimal child.digest.value)]
  | .runs runs => .mkObj [("type", "runs"),
      ("runs", .arr <| runs.toArray.map fun run => decimal run.digest.value)]
  | .embed transclusion => .mkObj [("type", "embed"),
      ("transclusion", decimal transclusion.digest.value)]
  | .atom atom => .mkObj [("type", "atom"), ("atom", decimal atom.digest.value)]
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
  | .sealed fragment => .mkObj [("type", "sealed"), ("fragment", authoredFragmentJson fragment)]

private def markAnchorJson : Hyperdocument.MarkAnchor → Lean.Json
  | .range range => .mkObj [("type", "range"), ("range", stableRangeJson range)]
  | .atom atom revision => .mkObj [("type", "atom"), ("atom", decimal atom.digest.value),
      ("revision", decimal revision.digest.value)]
  | .element element revision => .mkObj [("type", "element"),
      ("element", decimal element.digest.value), ("revision", decimal revision.digest.value)]

private def markJson (store : ContentResource.ContentStore) (identifier : Hyperdocument.MarkId)
    (record : Hyperdocument.MarkRecord) : List (String × Lean.Json) :=
  let kind : List (String × Lean.Json) := match record.kind with
    | .bold => [("kind", "bold")]
    | .italic => [("kind", "italic")]
    | .code => [("kind", "code")]
    | .heading => [("kind", "heading")]
    | .link link =>
        let linkRecord := Hyperdocument.lookup store .links link
        [("kind", "link"), ("link", decimal link.digest.value),
          ("target", (linkRecord.map fun found => linkTargetJson found.target).getD .null),
          ("linkLive", .bool ((linkRecord.map fun found => found.tombstonedAt.isNone).getD false))]
  [("mark", decimal identifier.digest.value)] ++ kind ++
    [("anchor", markAnchorJson record.anchor), ("author", principalJson record.author),
      ("fresh", .bool (ContentResource.markFresh store record)),
      ("tombstonedAt", optionalOperationJson record.tombstonedAt)]

private def contentEntryJson (store : ContentResource.ContentStore)
    (entry : Minidregg.Theory.Store.Entry Hyperdocument.layout) : Lean.Json :=
  let canonical := hexJson ((StoreCodec.entryStream HyperdocumentCell.contentWire).encode entry)
  match entry with
  | ⟨⟨.documents, identifier⟩, record⟩ =>
      let identifier : Hyperdocument.DocumentId := identifier
      let record : Hyperdocument.DocumentRecord := record
      .mkObj [("type", "document"), ("id", decimal identifier.digest.value),
        ("rootElement", identifierJson record.rootElement), ("schema", decimal record.schema.value),
        ("createdBy", principalJson record.createdBy), ("createdAt", identifierJson record.createdAt),
        ("canonical", canonical)]
  | ⟨⟨.elements, identifier⟩, record⟩ =>
      let identifier : Hyperdocument.ElementId := identifier
      let record : Hyperdocument.ElementRecord := record
      .mkObj [("type", "element"), ("id", decimal identifier.digest.value),
        ("document", identifierJson record.document), ("parent", optionalIdentifierJson record.parent),
        ("body", elementBodyJson record.body), ("createdBy", principalJson record.createdBy),
        ("createdAt", identifierJson record.createdAt),
        ("revision", decimal record.revision.digest.value),
        ("tombstonedAt", optionalIdentifierJson record.tombstonedAt), ("canonical", canonical)]
  | ⟨⟨.annotations, identifier⟩, record⟩ =>
      let identifier : Hyperdocument.AnnotationId := identifier
      let record : Hyperdocument.AnnotationRecord := record
      .mkObj (([("type", "annotation"), ("id", decimal identifier.digest.value),
        ("anchor", annotationAnchorJson record.anchor), ("body", annotationBodyJson record.body),
        ("author", principalJson record.author), ("operation", decimal record.operation.digest.value),
        ("tombstonedAt", optionalIdentifierJson record.tombstonedAt),
        ("fresh", .bool (ContentResource.annotationFresh store record)),
        ("canonical", canonical)] : List (String × Lean.Json)) ++
          SourceAgreementLegacyView.markFields stableRangeJson record)
  | ⟨⟨.links, identifier⟩, record⟩ =>
      let identifier : Hyperdocument.LinkId := identifier
      let record : Hyperdocument.LinkRecord := record
      .mkObj [("type", "link"), ("id", decimal identifier.digest.value),
        ("document", identifierJson record.sourceDocument),
        ("source", match record.source with | some range => stableRangeJson range | none => .null),
        ("target", linkTargetJson record.target), ("relation", decimal record.relation.value),
        ("createdBy", principalJson record.author), ("createdAt", identifierJson record.operation),
        ("tombstonedAt", optionalIdentifierJson record.tombstonedAt), ("canonical", canonical)]
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
  | ⟨⟨.marks, identifier⟩, record⟩ =>
      let identifier : Hyperdocument.MarkId := identifier
      let record : Hyperdocument.MarkRecord := record
      .mkObj (([("type", "mark"), ("id", decimal identifier.digest.value),
        ("document", decimal record.document.digest.value)] : List (String × Lean.Json)) ++
        markJson store identifier record ++
        [("canonical", canonical)])
  | ⟨⟨space, _⟩, _⟩ => .mkObj [("type", "namespace"),
      ("namespace", decimal (HyperdocumentCell.namespaceTag space).toNat), ("canonical", canonical)]

private def contentCellJson (root : Digest) (store : ContentResource.ContentStore) : Lean.Json :=
  .mkObj [("root", decimal root.value),
    ("entries", .arr <| (StoreCodec.entries HyperdocumentCell.contentWire store).toArray.map
      (contentEntryJson store))]

private def streamCellJson (root : Digest) (store : StreamCell.HeadStore) : Lean.Json :=
  match StreamCell.headOf store with
  | none => .mkObj [("root", decimal root.value), ("head", .null)]
  | some head => .mkObj [("root", decimal root.value), ("nextSeq", decimal head.nextSeq),
      ("count", decimal head.count),
      ("tail", head.tail.map (fun d => decimal d.value) |>.getD .null),
      ("binding", match head.binding with
        | .room => "room"
        | .topic stream => .mkObj [("topic", decimal stream.value)])]

private def rootOpeningJson (opening : NativeObservationController.OpeningView) : Lean.Json :=
  .mkObj [("frame", hexJson opening.1),
    ("items", .arr <| opening.2.toArray.map fun
      | .inl opened => .mkObj [("salt", hexJson opened.salt), ("entry", hexJson opened.entry)]
      | .inr leaf => .mkObj [("leaf", hexJson leaf)])]

private def resourceJson (value : NativeObservationController.ResourceView) : Result Lean.Json := do
  let (root, bytes, balances, opening, computeQuote) := value
  let packed ← match Minidregg.Theory.CellRegistry.PackedCell.decode
      CanonicalCellRegistry.registry bytes with
    | some packed => pure packed
    | none => failAt "view-resource.cell" "noncanonical packed cell"
  let view ← match packed with
    | ⟨.content, payload⟩ => pure (contentCellJson root payload.logical)
    | ⟨.declaredObject, payload⟩ => pure (declaredCellJson root payload.logical)
    | ⟨.stream, payload⟩ => pure (streamCellJson root payload.logical)
    | ⟨.worldKind, payload⟩ => worldKindJson root payload.logical
    | ⟨.worldInstance, payload⟩ => worldInstanceJson root payload.logical
    | _ => pure (.mkObj [("root", decimal root.value), ("canonical", hexJson bytes)])
  pure <| .mkObj [("type", "resource"), ("cell", view),
    ("balances", .arr <| balances.toArray.map fun p => .arr #[decimal p.1, signedDecimal p.2]),
    ("opening", rootOpeningJson opening),
    ("computeQuote", (computeQuote.map fun quote => .mkObj
      [("subject", decimal quote.subject), ("bookRoot", decimal quote.bookRoot.value),
       ("day", decimal quote.day), ("usedSteps", decimal quote.usedSteps),
       ("freeSteps", decimal quote.freeSteps), ("creditsPerStep", decimal quote.creditsPerStep),
       ("creditAsset", (quote.creditAsset.map decimal).getD .null)]).getD .null)]

private def decoded {α : Type} (path : String) (codec : IndexedProgram.LawfulCodec α)
    (bytes : List UInt8) : Result α :=
  match codec.decode bytes with
  | some value => pure value
  | none => failAt path "noncanonical or wrong-family binary input"

def birthCurrent (path : String) (json : Lean.Json)
    (deployed : NativeHost.Config) (height : Nat) (authority : AuthState)
    (lineage : CapabilityId → Option (Finset CapabilityId)) :
    Result Draft := do
  let raw ← object path json
  let source ← genesis (path ++ ".genesis") (← field path "genesis" raw)
  let built ← (NativeHostGenesis.build deployed.profile source).mapError
    (fun reason => s!"{path}.genesis: refused: {repr reason}")
  unless NativeHost.seedIdentity built.seed == deployed.expectedSeed do
    throw s!"{path}.genesis: differs from the pinned seed"
  birth path json none (some deployed) (some height) (some authority) [] (some lineage)

def subjectKeyStatusJson (subject : Nat) (status : SubjectKeyRotation.Status) : Lean.Json := .mkObj
  [("type", "subject-key-status-v1"),
   ("subject", decimal subject),
   ("keyEpoch", decimal status.epoch),
   ("keyId", decimal status.keyId),
   ("prerotated", .bool status.prerotated),
   ("isCurrent", .bool status.isCurrent),
   ("isCommittedNext", .bool status.isCommittedNext),
   ("currentRevoked", .bool status.currentRevoked)]

def subjectKeyStatusQuery (json : Lean.Json) : Result (Nat × List UInt8) := do
  let obj ← exactObject "$" ["subject", "publicKey"] json
  let subject ← nat "$.subject" (← field "$" "subject" obj)
  let publicKey ← decodeHex "$.publicKey" (← field "$" "publicKey" obj)
  unless publicKey.length = 32 do failAt "$.publicKey" "expected 32 bytes"
  pure (subject, publicKey)

private def marksOf (store : ContentResource.ContentStore) :
    List (Hyperdocument.MarkId × Hyperdocument.MarkRecord) :=
  (StoreCodec.entries HyperdocumentCell.contentWire store).filterMap fun entry =>
    match entry with
    | ⟨⟨.marks, identifier⟩, record⟩ =>
        let identifier : Hyperdocument.MarkId := identifier
        let record : Hyperdocument.MarkRecord := record
        some (identifier, record)
    | _ => none

private def pageOfView (path : String) (bytes : List UInt8) :
    Result (Option Nat × String × Option Digest × ContentResource.ContentStore) := do
  match NativeObservationController.resourceViewCodec.decode bytes with
  | some value =>
      match Minidregg.Theory.CellRegistry.PackedCell.decode CanonicalCellRegistry.registry value.2.1 with
      | some ⟨.content, payload⟩ => pure (none, "live", some value.1, payload.logical)
      | _ => failAt path "not a content cell"
  | none =>
      let (height, root, lifecycle, _opening) ← decoded path NativeObservationController.atViewCodec bytes
      match ResourceBirthCodec.LifecycleImage.rawDecode CanonicalCellRegistry.registry lifecycle with
      | some .fresh => pure (some height, "fresh", none, ContentResource.initialStore)
      | some .retired => pure (some height, "retired", none, ContentResource.initialStore)
      | some (.live ⟨.content, payload⟩) => pure (some height, "live", root, payload.logical)
      | some (.live _) => failAt path "not a content cell"
      | none => failAt path "noncanonical lifecycle bytes"

private def transclusionViewJson : ContentResource.TransclusionView → Lean.Json
  | .unavailable atoms source => .mkObj [("view", "unavailable"), ("atoms", decimal atoms),
      ("source", decimal source)]
  | .snapshot lines => .mkObj [("view", "snapshot"), ("lines", .arr <| lines.toArray.map hexJson)]
  | .moved height => .mkObj [("view", "moved"), ("height", decimal height)]
  | .live lines revised => .mkObj [("view", "live"), ("lines", .arr <| lines.toArray.map hexJson),
      ("revised", .bool revised)]
  | .invalidated => .mkObj [("view", "invalidated")]
  | .unresolved => .mkObj [("view", "unresolved")]

private def transclusionProjectionJson (source : Option ContentResource.ContentStore)
    (opening : ContentResource.RangeOpening) (mode : Hyperdocument.TransclusionMode) : Lean.Json :=
  let rendered := ContentResource.renderTransclusion source opening mode
  let pins := match source, mode with
    | some _, .snapshot => opening.pins
    | some store, .live =>
        match ContentResource.resolveRange store (ContentResource.documentOf opening.source) opening.range with
        | .slots atoms => ContentResource.livePins store (ContentResource.documentOf opening.source) atoms
        | _ => []
    | _, _ => []
  let selected := Lean.Json.arr <| pins.toArray.map fun pin => .mkObj
    [("atom", decimal pin.1.digest.value), ("revision", decimal pin.2.digest.value)]
  match rendered with
  | .snapshot lines => .mkObj [("view", "snapshot"),
      ("lines", .arr <| lines.toArray.map hexJson), ("selected", selected)]
  | .live lines revised => .mkObj [("view", "live"),
      ("lines", .arr <| lines.toArray.map hexJson), ("revised", .bool revised), ("selected", selected)]
  | other => transclusionViewJson other

private def documentOf? (store : ContentResource.ContentStore) : Option Hyperdocument.DocumentId :=
  ((StoreCodec.entries HyperdocumentCell.contentWire store).findSome? fun entry =>
    match entry with
    | ⟨⟨.documents, identifier⟩, _⟩ => some identifier
    | _ => none).orElse fun _ => SourceAgreementLegacyView.documentOf? store

private def pageLines (store : ContentResource.ContentStore) :
    List (Hyperdocument.ElementId × DocumentHistory.Line) :=
  match documentOf? store with
  | some document => SourceAgreementLegacyView.lines store document (marksOf store)
  | none => []

private def lineValueJson (store : ContentResource.ContentStore) :
    DocumentHistory.Line → List (String × Lean.Json)
  | .atom atom record marks =>
      [("kind", .str "atom"), ("atom", decimal atom.digest.value)] ++
      (match record with
        | some record => [("payload", hexJson record.bodyBytes),
            ("revision", decimal record.revision.digest.value),
            ("createdBy", principalJson record.createdBy), ("struck", .bool record.tombstonedAt.isSome)]
        | none => [("payload", .null)]) ++
      [("marks", marksJson store marks)]
  | .embed transclusion marks => [("kind", .str "embed"),
      ("transclusion", decimal transclusion.digest.value), ("marks", marksJson store marks)]
  | .section revision marks => [("kind", .str "container"), ("revision", decimal revision.digest.value),
      ("marks", marksJson store marks)]
  | .runs => [("kind", .str "runs")]
  | .opaque => [("kind", .str "opaque")]
  | .missing => [("kind", .str "missing")]
where
  marksJson (store : ContentResource.ContentStore)
      (marks : List (Hyperdocument.MarkId × Hyperdocument.MarkRecord)) : Lean.Json :=
    .arr <| marks.toArray.map fun (identifier, record) => .mkObj (markJson store identifier record)

private def orderEntryJson (store : ContentResource.ContentStore)
    (row : Hyperdocument.ElementId × DocumentHistory.Line) : Lean.Json :=
  let element := row.1
  .mkObj <| [("element", decimal element.digest.value),
    ("parent", match ContentResource.parentOf store element with
      | some parent => decimal parent.digest.value
      | none => .null)] ++ lineValueJson store row.2 ++
    match row.2 with
    | .section _ _ => [("children", decimal (ContentResource.childrenOf store element).length)]
    | .embed _ _ => [("revision", match ContentResource.elementAt store element with
        | some record => decimal record.revision.digest.value
        | none => .null)]
    | _ => []

private def pageJson (page : Option Nat × String × Option Digest × ContentResource.ContentStore) :
    List (String × Lean.Json) :=
  let store := page.2.2.2
  let root := (documentOf? store).bind (SourceAgreementLegacyView.rootOf? store)
  [("height", (page.1.map decimal).getD .null), ("state", .str page.2.1),
    ("cellRoot", (page.2.2.1.map fun root => decimal root.value).getD .null),
    ("root", (root.map fun element => decimal element.digest.value).getD .null),
    ("rootRevision", match root.bind (ContentResource.elementAt store) with
      | some record => decimal record.revision.digest.value
      | none => .null),
    ("order", .arr <| (pageLines store).toArray.map (orderEntryJson store))]

private def jsonInput (kind : String) (bytes : List UInt8) : Result Lean.Json := do
  let text ← match String.fromUTF8? (ByteArray.mk bytes.toArray) with
    | some text => pure text | none => failAt kind "input is not UTF-8"
  match Lean.Json.parse text with
  | .ok json => pure json | .error message => failAt kind message

private def documentJson (bytes : List UInt8) : Result Lean.Json := do
  let obj ← exactObject "$" ["host", "sources"] (← jsonInput "view-document" bytes)
  let page ← pageOfView "$.host" (← decodeHex "$.host" (← field "$" "host" obj))
  let host := page.2.2.2
  let sources ← list "$.sources" (fun path entry => do
      let atHeight := (entry.getObjVal? "at").toOption.isSome
      let key := if atHeight then "at" else "view"
      let source ← exactObject path ["target", key] entry
      let target ← nat (path ++ ".target") (← field path "target" source)
      let read ← pageOfView (path ++ "." ++ key) (← decodeHex (path ++ "." ++ key) (← field path key source))
      unless read.2.1 = "live" do
        failAt (path ++ "." ++ key) "not a live content cell at that height"
      pure (target, read.2.2.2)) (← field "$" "sources" obj)
  let rendered := (StoreCodec.entries HyperdocumentCell.contentWire host).filterMap fun entry =>
    match entry with
    | ⟨⟨.transclusions, identifier⟩, record⟩ =>
        let identifier : Hyperdocument.TransclusionId := identifier
        let record : Hyperdocument.TransclusionRecord := record
        some <| match ContentResource.openingOfReference record.reference with
          | none =>
              match SourceAgreementLegacyCodec.inspectReference record.reference with
              | none => .mkObj [("id", decimal identifier.digest.value),
                  ("render", .mkObj [("view", "unresolved")])]
              | some legacy =>
                  let source := (sources.find? (fun pair => pair.1 = legacy.document.digest.value)).map Prod.snd
                  .mkObj [("id", decimal identifier.digest.value), ("mode", modeJson legacy.mode),
                    ("legacyReference", SourceAgreementLegacyView.referenceJson legacy),
                    ("render", SourceAgreementLegacyView.renderReference source legacy)]
          | some opening =>
              let source := (sources.find? (fun pair => pair.1 = opening.source)).map Prod.snd
              .mkObj [("id", decimal identifier.digest.value), ("mode", modeJson record.reference.mode),
                ("opening", openingJson opening),
                ("render", transclusionProjectionJson source opening record.reference.mode)]
    | _ => none
  pure <| .mkObj ([("type", Lean.Json.str "document")] ++ pageJson page ++
    [("transclusions", .arr rendered.toArray)])

def inspect (kind : String) (bytes : List UInt8) : Result Lean.Json :=
  match kind with
  | "predicate" => predicateJson <$> decoded "predicate"
      (ResourceBirthCodec.strictCodec NativeHostGenesis.predicateStream.toLawful) bytes
  | "observation-batch" => do
      unless bytes.length ≤ NativeObservationCodec.maxBatchBytes do
        failAt "observation-batch" "observation batch exceeds its bounded presentation size"
      let reads ← decoded "observation-batch" NativeObservationCodec.batchCodec bytes
      unless NativeObservationCodec.validBatch reads do
        failAt "observation-batch" "observation batch requires 1 through 16 reads"
      pure (.arr (reads.map hexJson).toArray)
  | "challenge" => challengeJson <$> decoded "challenge" challengeCodec bytes
  | "plan" => planJson <$> decoded "plan" signingPlanCodec bytes
  | "outcome" => outcomeJson <$> decoded "outcome" outcomeCodec bytes
  | "view-resource" => do
      let value ← decoded "view-resource" NativeObservationController.resourceViewCodec bytes
      resourceJson value
  | "view-policy" => do
      let value ← match PolicyRecordCodec.decode bytes with
        | some value => pure value | none => failAt "view-policy" "noncanonical policy source"
      pure <| (policyRecordJson value).mergeObj (.mkObj
        [("type", "policy"), ("canonical", hexJson (PolicyRecordCodec.encode value)),
         ("address", decimal (PolicyRecordCodec.digest value).value),
         ("semanticLawDigest", decimal (PolicyRecordCodec.semanticLawDigest value).value),
         ("text", .str (LawLeaf.renderClause value.predicate))])
  | "view-who" => do
      let value ← decoded "view-who" NativeObservationController.whoViewCodec bytes
      let grants := fun (held : List (Nat × Nat)) => Lean.Json.arr <| held.toArray.map fun (cap, policy) =>
        Lean.Json.mkObj [("capability", decimal cap), ("policy", decimal policy)]
      pure <| .mkObj [("type", "who"),
        ("members", .arr <| (value.filter (·.2.2.1)).toArray.map fun (subject, seen, _, held) =>
          .mkObj [("subject", decimal subject), ("lastSeen", (seen.map decimal).getD .null),
            ("capabilities", .arr <| held.toArray.map fun grant => decimal grant.1)]),
        ("holders", .arr <| value.toArray.map fun (subject, seen, member, held) =>
          .mkObj [("subject", decimal subject), ("member", .bool member),
            ("lastSeen", (seen.map decimal).getD .null), ("grants", grants held)])]
  | "view-since" => do
      let value ← decoded "view-since" NativeObservationController.sinceViewCodec bytes
      pure <| .mkObj [("type", "since"), ("entries", .arr <| value.toArray.map fun entry =>
        .mkObj [("height", decimal entry.height), ("subject", (entry.subject.map decimal).getD .null),
          ("transaction", decimal entry.transaction),
          ("cells", .arr <| entry.cells.toArray.map decimal)])]
  | "view-at" => do
      let (height, root, lifecycle, opening) ← decoded "view-at" NativeObservationController.atViewCodec bytes
      match ResourceBirthCodec.LifecycleImage.rawDecode CanonicalCellRegistry.registry lifecycle with
      | some .fresh => pure <| .mkObj [("type", "at"), ("height", decimal height), ("state", "fresh")]
      | some .retired => pure <| .mkObj [("type", "at"), ("height", decimal height), ("state", "retired")]
      | some (.live cell) => do
          let view ← resourceJson (root.getD cell.payload.root,
            PackedCell.bytes CanonicalCellRegistry.registry cell, [], opening, none)
          pure <| .mkObj [("type", "at"), ("height", decimal height), ("state", "live"),
            ("canonical", hexJson lifecycle), ("resource", view)]
      | none => failAt "view-at" "noncanonical lifecycle bytes"
  | "view-backlinks" | "view-links" => do
      let (backward, rows) ← decoded kind NativeObservationController.linkViewCodec bytes
      unless backward = (kind == "view-backlinks") do
        failAt kind s!"the bytes are a {if backward then "backlinks" else "links"} view"
      pure <| .mkObj [("type", if backward then "backlinks" else "links"),
        ("rows", .arr <| rows.toArray.map fun row => .mkObj
          [("source", decimal row.source), ("link", decimal row.link),
           ("anchor", (row.anchor.map decimal).getD .null), ("revision", decimal row.revision),
           ("height", decimal row.height),
           ("kind", match row.kind with
             | 0 => "document" | 1 => "element" | 2 => "range" | 3 => "transclusion" | _ => "external"),
           ("target", decimal row.target), ("relation", decimal row.relation)])]
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
  -- K-INSPECT-VIEWS: renderers over bytes the client holds (Host/InspectRender).
  | "view-resource-scope" => do
      let (kind, capability, fields, resource) ← decoded "view-resource-scope"
        NativeObservationController.resourceScopeViewCodec bytes
      pure <| .mkObj [("type", "resource-scope"), ("resource", ← resourceJson resource),
        ("capability", .mkObj [("kind", match kind with | .object => "object" | .account => "account" | .program => "program"),
          ("head", .mkObj [("id", decimal capability),
            ("fields", (fields.map fun values => .arr <| ((values.image CredentialAuthorityEntryCodec.fieldLabel).sort (· ≤ ·)).toArray.map
              (fun label => .str (CredentialAuthorityEntryCodec.cellFieldName
                (CredentialAuthorityEntryCodec.fieldOfLabel label)))).getD .null)])])]
  | "context-document" => SourceAgreementContextInspection.document bytes
  | "context-support" => SourceAgreementContextInspection.support bytes
  | "view-document" => documentJson bytes
  | _ => failAt "kind" "unsupported ordinary source-agreement grammar"

end Minidregg.Host.SourceAgreementJson
