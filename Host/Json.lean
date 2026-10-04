/-
Bounded JSON authoring for the native host. JSON is only a human-facing
notation: successful authoring constructs the real source values and invokes
their canonical codecs. All unbounded integers are decimal strings.
-/
import Kernel.NativeHost
import Kernel.PayStarterAllowance
import Host.BirthRuntimeProfile
import Host.CapabilityInspection
import Host.InspectRender
import Kernel.NativeHostGenesis
import Kernel.AgentGrain
import Kernel.ProviderRoute
import Kernel.CapabilityRevocationController
import Kernel.ContentResource
import Host.LegacyContentView
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
import Host.ApplicationLifecycleRetryLaunchReportAuthoring
import Host.ApplicationLifecycleRetryBeginV4Inspection
import Host.ApplicationLifecycleRetryClaimV4Inspection
import Host.ApplicationLifecycleRetryCompletionV4Inspection
import Host.ApplicationAgentLifetimeGrantInspection
import Host.ApplicationLifecycleClaimOperator
import Host.ApplicationDispatchAgentPaidInspection
import Host.ApplicationAgentLifetimeDispatchPaidInspection
import Host.ApplicationShareIssueGrainInspection
import Host.ApplicationGrainSessionEnrollmentInspection
import Kernel.ApplicationDispatchAgentReserveContext
import Kernel.ApplicationDispatchCodec
import Kernel.ParticipantKeyEnrollment
import Kernel.Receivers.SubjectKeyRotation
import Kernel.ParticipantFactoryProvisioning
import Kernel.FleetTurn
import Kernel.PayBookReceiver
import Kernel.PayAssignmentReceiver
import Kernel.ClockTickReceiver
import Kernel.PayObservationReceiver
import Kernel.PayEnrolReceiver
import Kernel.PayEnrolQuote
import Compiler.PayEnrolSignatureIO
import Kernel.CertifyReceiver
import Kernel.ApplicationLifecycleResidentProfile
import Host.ApplicationPermissionSchemaAuthoring
import Host.ApplicationSpkLaunchDescriptorAuthoring
import Kernel.NockProgramCell
import Kernel.NockDoor
import Kernel.DocumentHistory
import Host.ResidentContextInspection
import Host.ObjectiveActivityJson
import Host.SeatJson
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

/-- One object key of the duplicate scan: refused when the object already holds
it, recorded otherwise. A hash set, so an object of n keys costs O(n): with a
list it cost O(n^2), and one 1.6 MB public op 7 body of 160k keys held the one
Host for minutes (SERVE-ROBUST, measured: 40k keys +7 s, 1M keys > 330 s). -/
def admitKey (keys : Std.HashSet String) (key : String) : Result (Std.HashSet String) :=
  if keys.contains key then .error s!"duplicate JSON object field: {key}"
  else .ok (keys.insert key)

/-- A key the object already holds is refused, by name. -/
theorem admitKey_refuses_held (keys : Std.HashSet String) (key : String)
    (held : keys.contains key = true) :
    admitKey keys key = .error s!"duplicate JSON object field: {key}" := by
  simp [admitKey, held]

/-- A key the object does not hold is admitted, and afterwards it is held along
with every key held before: a later repeat of any of them is refused. -/
theorem admitKey_records (keys : Std.HashSet String) (key : String)
    (fresh : keys.contains key = false) :
    ∃ after, admitKey keys key = .ok after ∧ after.contains key = true ∧
      ∀ k, keys.contains k = true → after.contains k = true := by
  refine ⟨keys.insert key, by simp [admitKey, fresh], by simp, ?_⟩
  intro k held
  simp [Std.HashSet.contains_insert, held]

#assert_axioms admitKey_refuses_held
#assert_axioms admitKey_records

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

/-- The deepest `[`/`{` nesting outside string literals. Tail recursive, so it
runs in constant stack on any input. -/
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

/-- No request this Host authors from nests deeper than this. The bound runs
before either recursive parser sees the text: Lean's JSON parser recurses once
per level, so unbounded nesting is a stack exhaustion, not a refusal. -/
def maxNesting : Nat := 64

theorem nestingDepth_flat : nestingDepth "{\"a\":[\"[{\"]}".toList = 2 := by decide
#assert_axioms nestingDepth_flat

/-- Parse JSON without Lean's usual duplicate-key overwrite. Main must use
this boundary before calling `author` or `signatures`. -/
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

/-- Selectors describe source-owned projection tags. Absence/null selects all;
`[]` selects none. JSON defaults author v6 only, never reinterpret old wire. -/
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

/-- Exact authorable combined-v6 record. Every extension facet is explicit in
signed readback so changing one cannot erase another by omission. -/
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

/-- K-RENOUNCE: `{"subject","nonce","kind","capability"}`. -/
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

/-- `{"type":"splice","index":N,"child":E}`, `{"type":"move","child":E,"index":N}` or
`{"type":"remove","child":E}`. -/
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

/-- `{"type":"atom","atom":A}` or `{"type":"element","element":E}`. -/
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

/-- `{"type":"bold"|"italic"|"code"|"heading"}` or
`{"type":"link","link":L,"target":TARGET}`; any other kind is refused
`unknownKind` here, since the kernel's grammar cannot carry one. -/
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

/-- Protected body provenance is normalized by the content receiver. -/
private def annotationBody (path : String) (json : Lean.Json) : Result Hyperdocument.AnnotationBody := do
  match json with
  | .str _ => pure (.inline (← decodeHex path json))
  | _ =>
      let obj ← exactObject path ["type", "fragment"] json
      if (← string (path ++ ".type") (← field path "type" obj)) != "sealed" then
        failAt path "expected sealed annotation body"
      else pure (.sealed (← authoredFragment (path ++ ".fragment") (← field path "fragment" obj)))

/-- The guard of `rewrapAnnotation` is the annotation's exact canonical store entry: the
bytes a signed view carries as the entry's `canonical`, address then record. It must be
canonical and must name the annotation being rewrapped; the record it carries is the
prior state the action is guarded on. -/
private def annotationBefore (path : String) (annotation : Hyperdocument.AnnotationId)
    (json : Lean.Json) : Result Hyperdocument.AnnotationRecord := do
  let bytes ← decodeHex path json
  let codec := StoreCodec.entryStream HyperdocumentCell.contentWire
  match codec.toLawful.decode bytes with
  | some entry =>
      if codec.encode entry != bytes then failAt path "annotation guard is not canonical"
      else
        match entry with
        | ⟨⟨.annotations, identifier⟩, record⟩ =>
            let identifier : Hyperdocument.AnnotationId := identifier
            let record : Hyperdocument.AnnotationRecord := record
            if identifier.digest.value != annotation.digest.value then
              failAt path "annotation guard names another annotation"
            else pure record
        | _ => failAt path "annotation guard is not an annotation entry"
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
      let annotation ← identifier (path ++ ".annotation") (← field path "annotation" obj)
      pure (.rewrapAnnotation annotation
        (← annotationBefore (path ++ ".before") annotation (← field path "before" obj))
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

/-! World-resident descriptor authoring stays in source. JSON values are
primitive human spellings; StoreCodec supplies every canonical store byte. -/
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
     ("methods", worldMethodsJson value),
     ("definitionBytes", hexJson (WorldKindCell.definitionStream.encode definition)),
     ("sampleSlots", .arr <| (WorldPrototypeConstruction.observeProject store).toArray.map fun slot =>
       Lean.Json.arr #[.str slot.1, signedDecimal slot.2])])]

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

private def moneyOperation (path : String) (json : Lean.Json) :
    Result Minidregg.Theory.CanonicalResourceKernel.Operation := do
  let (tag, _) ← tagged path json
  match tag with
  | "transfer" | "fee" =>
      let obj ← exactObject path ["type", "source", "destination", "asset", "amount"] json
      let source ← nat (path ++ ".source") (← field path "source" obj)
      let destination ← nat (path ++ ".destination") (← field path "destination" obj)
      let asset ← nat (path ++ ".asset") (← field path "asset" obj)
      let amount ← nat (path ++ ".amount") (← field path "amount" obj)
      pure (if tag = "transfer" then .transfer source destination asset amount
        else .fee source destination asset amount)
  | "mint" =>
      let obj ← exactObject path ["type", "asset", "destination", "amount"] json
      pure (.mint (← nat (path ++ ".asset") (← field path "asset" obj))
        (← nat (path ++ ".destination") (← field path "destination" obj))
        (← nat (path ++ ".amount") (← field path "amount" obj)))
  | "burn" =>
      let obj ← exactObject path ["type", "source", "asset", "amount"] json
      pure (.burn (← nat (path ++ ".source") (← field path "source" obj))
        (← nat (path ++ ".asset") (← field path "asset" obj))
        (← nat (path ++ ".amount") (← field path "amount" obj)))
  | "lease" =>
      let obj ← exactObject path
        ["type", "leaseId", "holder", "lessor", "asset", "rate", "epochs", "startsAt"] json
      pure (.lease (← nat (path ++ ".leaseId") (← field path "leaseId" obj))
        (← nat (path ++ ".holder") (← field path "holder" obj))
        (← nat (path ++ ".lessor") (← field path "lessor" obj))
        (← nat (path ++ ".asset") (← field path "asset" obj))
        (← nat (path ++ ".rate") (← field path "rate" obj))
        (← nat (path ++ ".epochs") (← field path "epochs" obj))
        (← nat (path ++ ".startsAt") (← field path "startsAt" obj)))
  | _ => failAt (path ++ ".type") "expected transfer, mint, burn, fee or lease"

private def moneyFunding (path : String) (json : Lean.Json) :
    Result Minidregg.Kernel.ResourceMoneyWire.FundingConsent := do
  let obj ← exactObject path ["asset", "credits", "expectedPayerBalance", "expectedBookRoot"] json
  pure ⟨← nat (path ++ ".asset") (← field path "asset" obj),
    ← nat (path ++ ".credits") (← field path "credits" obj),
    ← int (path ++ ".expectedPayerBalance") (← field path "expectedPayerBalance" obj),
    ⟨← nat (path ++ ".expectedBookRoot") (← field path "expectedBookRoot" obj)⟩⟩

private def moneyBatch (path : String) (json : Lean.Json) :
    Result Minidregg.Kernel.ResourceMoneyWire.ApplicationBatch := do
  let obj ← exactObject path ["expectedBookRoot", "operations"] json
  pure ⟨⟨← nat (path ++ ".expectedBookRoot") (← field path "expectedBookRoot" obj)⟩,
    ← list (path ++ ".operations") moneyOperation (← field path "operations" obj)⟩

private def moneyOperationJson : Minidregg.Theory.CanonicalResourceKernel.Operation → Lean.Json
  | .transfer source destination asset amount => .mkObj
      [("type", .str "transfer"), ("source", decimal source), ("destination", decimal destination),
       ("asset", decimal asset), ("amount", decimal amount)]
  | .fee source destination asset amount => .mkObj
      [("type", .str "fee"), ("source", decimal source), ("destination", decimal destination),
       ("asset", decimal asset), ("amount", decimal amount)]
  | .mint asset destination amount => .mkObj
      [("type", .str "mint"), ("asset", decimal asset), ("destination", decimal destination),
       ("amount", decimal amount)]
  | .burn source asset amount => .mkObj
      [("type", .str "burn"), ("source", decimal source), ("asset", decimal asset),
       ("amount", decimal amount)]
  | .lease leaseId holder lessor asset rate epochs startsAt => .mkObj
      [("type", .str "lease"), ("leaseId", decimal leaseId), ("holder", decimal holder),
       ("lessor", decimal lessor), ("asset", decimal asset), ("rate", decimal rate),
       ("epochs", decimal epochs), ("startsAt", decimal startsAt)]

/-- Complete typed declaration view. Values become authoritative only through
canonical native preparation, signatures, current law and joint admission. -/
def moneyConsentJson (consent : Minidregg.Kernel.ResourceMoneyWire.Consent) : Lean.Json :=
  .mkObj [("type", .str "moneyConsent"),
    ("batch", (consent.batch.map fun batch => .mkObj
      [("expectedBookRoot", decimal batch.expectedBookRoot.value),
       ("operations", .arr (batch.operations.toArray.map moneyOperationJson))]).getD .null),
    ("positions", .arr (consent.positions.toArray.map decimal)),
    ("funding", (consent.funding.map fun funding => .mkObj
      [("asset", decimal funding.asset), ("credits", decimal funding.credits),
       ("expectedPayerBalance", signedDecimal funding.expectedPayerBalance),
       ("expectedBookRoot", decimal funding.expectedBookRoot.value)]).getD .null)]

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
  | "moneyConsent" =>
      let obj ← exactObject path ["type", "batch", "positions", "funding"] json
      pure (.moneyConsent ⟨
        ← optional (path ++ ".batch") moneyBatch (← field path "batch" obj),
        ← list (path ++ ".positions") nat (← field path "positions" obj),
        ← optional (path ++ ".funding") moneyFunding (← field path "funding" obj)⟩)
  | "computeFunding" =>
      let obj ← exactObject path ["type", "asset", "credits", "expectedPayerBalance", "expectedBookRoot"] json
      pure (.computeFunding ⟨← nat (path ++ ".asset") (← field path "asset" obj),
        ← nat (path ++ ".credits") (← field path "credits" obj),
        ← int (path ++ ".expectedPayerBalance") (← field path "expectedPayerBalance" obj),
        ⟨← nat (path ++ ".expectedBookRoot") (← field path "expectedBookRoot" obj)⟩⟩)
  | "read" =>
      let _ ← exactObject path ["type"] json
      pure .read
  | "kindRead" =>
      let _ ← exactObject path ["type"] json
      pure .kindRead
  | _ => failAt (path ++ ".type") "expected scalar, content, append, read, kindRead, world, kindDefinition, moneyConsent or computeFunding"

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

def audienceRosterJson (roster : Minidregg.Theory.ObjectAudienceRoster.Roster) : Lean.Json := .mkObj
  [("object", decimal roster.object), ("epoch", decimal roster.epoch),
   ("transition", decimal roster.transition), ("entries", .arr (roster.entries.map (fun e =>
      .mkObj [("subject", decimal e.subject), ("capability", decimal e.capability),
        ("deviceSource", decimal e.deviceSource), ("deviceGeneration", decimal e.deviceGeneration),
        ("keyCommitment", decimal e.keyCommitment)])).toArray)]

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

/-- `DREGG/NOCK/RUN/v1` as JSON: decimal program id and steps, hex jams. -/
def runClaim (path : String) (json : Lean.Json) : Result Kernel.Run.RunClaim := do
  let obj ← exactObject path ["programId", "sample", "output", "steps"] json
  pure ⟨⟨← nat (path ++ ".programId") (← field path "programId" obj)⟩,
    ← decodeHex (path ++ ".sample") (← field path "sample" obj),
    ← decodeHex (path ++ ".output") (← field path "output" obj),
    ← nat (path ++ ".steps") (← field path "steps" obj)⟩

/-- Generic family authoring preserves the complete route/context in the actual
canonical command. Admission, source registration and route permits remain native. -/
private def invocationFamily (path : String) (json : Lean.Json) :
    Result Compiler.NativeInvocationStatement.Family := do
  let obj ← exactObject path ["route", "contextBytes"] json
  let routeName ← string (path ++ ".route") (← field path "route" obj)
  let route ← match routeName with
    | "ordinary" => pure Compiler.NativeInvocationStatement.Route.ordinary
    | "objectiveMethod" => pure .objectiveMethod
    | "activityDispatch" => pure .activityDispatch
    | "roomRelease" => pure .roomRelease
    | "roomPublish" => pure .roomPublish
    | _ => failAt (path ++ ".route") "unknown invocation family route"
  pure ⟨route, ← decodeHex (path ++ ".contextBytes") (← field path "contextBytes" obj)⟩

private def command (path : String) (json : Lean.Json) : Result DeclaredResourceController.Command := do
  let raw ← object path json
  let extras := ["run", "family"].filter (fun key => (raw.get? key).isSome)
  let obj ← exactObject path (["subject", "nonce", "targets"] ++ extras) json
  let run ← match obj.get? "run" with
    | none => pure none
    | some value => some <$> runClaim (path ++ ".run") value
  let family ← match obj.get? "family" with
    | none => pure none
    | some value => some <$> invocationFamily (path ++ ".family") value
  pure {
    subject := ⟨← nat (path ++ ".subject") (← field path "subject" obj)⟩
    nonce := ← nat (path ++ ".nonce") (← field path "nonce" obj)
    targets := ← list (path ++ ".targets") commandTarget (← field path "targets" obj)
    run := run
    family := family }

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

/-- A clock ticker: its enrolled subject and the identifier of its `C_tick`. -/
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
    ["resource", "scope", "participant", "ceiling", "issueNonce", "notAfter"] json
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
    ← nat (path ++ ".issueNonce") (← field path "issueNonce" obj),
    ← nat (path ++ ".notAfter") (← field path "notAfter" obj)⟩

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
      AgentGrain.refillPolicy,
      grainWorkerClause subject generation]]
  | some (subjects, generation) => .all [base, .any <|
      [.eq "request/subject" (Int.ofNat owner), .memberOf "request/verb" [1, 3],
        AgentGrain.refillPolicy] ++
        subjects.map (fun subject => grainWorkerClause subject generation)]

/-- Every named worker in a plural policy gets the same pinned-generation,
no-op witness clause. This is a construction fact, not an IO admission claim. -/
theorem grainPolicy_plural_worker_clause (owner : Nat) (subjects : List Nat)
    (generation : Int) (subject : Nat) (named : subject ∈ subjects) :
    grainWorkerClause subject generation ∈
      ([.eq "request/subject" (Int.ofNat owner), .memberOf "request/verb" [1, 3],
        AgentGrain.refillPolicy] ++
        subjects.map (fun worker => grainWorkerClause worker generation)) := by
  apply List.mem_append.mpr
  right
  exact List.mem_map.mpr ⟨subject, named, rfl⟩

/-- info: 'Minidregg.Host.Json.grainPolicy_plural_worker_clause' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms grainPolicy_plural_worker_clause

/-- Plural authoring with one subject retains the exact historical policy
bytes, so adding a provider cannot silently alter the existing tool rule. -/
theorem grainPolicy_singleton_bytes (owner subject : Nat) (generation : Int) :
    NativeHostGenesis.predicateStream.encode
      (grainPolicy owner (some ([subject], generation))) =
    NativeHostGenesis.predicateStream.encode
      (.all [AgentGrain.policy (.eq "request/subject" (Int.ofNat owner)), .any [
        .eq "request/subject" (Int.ofNat owner),
        .memberOf "request/verb" [1, 3],
        AgentGrain.refillPolicy,
        .all [.eq "request/subject" (Int.ofNat subject),
          AgentGrain.witnessCaveat generation]]]) := rfl

/-- info: 'Minidregg.Host.Json.grainPolicy_singleton_bytes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms grainPolicy_singleton_bytes

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

/-- The managed law's refill alternative is the refill edge itself, which
needs the slot only the purse-refill receiver projects. -/
private theorem refillPolicy_needs_slot (old new : Minidregg.Pred.State)
    (noRefill : new.get AgentGrain.refillSlot ≠ some 1) :
    Minidregg.Pred.evalWith Minidregg.Pred.failClosed AgentGrain.refillPolicy old new = false := by
  simp [AgentGrain.refillPolicy, Minidregg.Pred.Pred.all, Minidregg.Pred.PredList.ofList,
    Minidregg.Pred.evalWith, Minidregg.Pred.evalWithAll, noRefill]

/-- For a mutation, no worker can reuse a previous pinned generation, even
if that worker can observe a newer state. Owner and management branches are
explicitly excluded by the request subject and verb, and the refill edge by
the absent refill slot (no receiver but the purse refill projects it). -/
theorem grainPolicy_stale_worker_refused (owner : Nat) (subjects : List Nat)
    (generation actual : Int) (caller : Nat)
    (old new : Minidregg.Pred.State)
    (verb : new.get "request/verb" = some 2)
    (requestSubject : new.get "request/subject" = some (Int.ofNat caller))
    (notOwner : caller ≠ owner)
    (noRefill : new.get AgentGrain.refillSlot ≠ some 1)
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
        Nat.cast_inj, notOwner, refillPolicy_needs_slot old new noRefill]
  | cons first rest =>
      cases rest with
      | nil =>
          have firstFalse := workerFalseWith first (by simp)
          simp [grainPolicy, Minidregg.Pred.eval_all, Minidregg.Pred.eval_any,
            Minidregg.Pred.eval, Minidregg.Pred.evalWith, requestSubject, verb,
            Nat.cast_inj, notOwner, firstFalse, refillPolicy_needs_slot old new noRefill]
      | cons second tail =>
          simp [grainPolicy, Minidregg.Pred.eval_all, Minidregg.Pred.eval_any,
            Minidregg.Pred.eval, Minidregg.Pred.evalWith, requestSubject, verb,
            Nat.cast_inj, notOwner, refillPolicy_needs_slot old new noRefill]
          intro _
          refine ⟨workerFalseWith first (by simp), workerFalseWith second (by simp), ?_⟩
          intro worker named
          exact workerFalseWith worker (by simp [named])

/-- info: 'Minidregg.Host.Json.grainPolicy_stale_worker_refused' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms grainPolicy_stale_worker_refused

/-- A non-owner subject absent from the bounded worker list cannot mutate
through the plural resource policy, even when it presents a valid generation. -/
theorem grainPolicy_unnamed_worker_refused (owner : Nat) (subjects : List Nat)
    (generation : Int) (caller : Nat)
    (old new : Minidregg.Pred.State)
    (verb : new.get "request/verb" = some 2)
    (requestSubject : new.get "request/subject" = some (Int.ofNat caller))
    (notOwner : caller ≠ owner)
    (noRefill : new.get AgentGrain.refillSlot ≠ some 1)
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
        Nat.cast_inj, notOwner, refillPolicy_needs_slot old new noRefill]
  | cons first rest =>
      cases rest with
      | nil =>
          have firstFalse := workerFalseWith first (by simp)
          simp [grainPolicy, Minidregg.Pred.eval_all, Minidregg.Pred.eval_any,
            Minidregg.Pred.eval, Minidregg.Pred.evalWith, requestSubject, verb,
            Nat.cast_inj, notOwner, firstFalse, refillPolicy_needs_slot old new noRefill]
      | cons second tail =>
          simp [grainPolicy, Minidregg.Pred.eval_all, Minidregg.Pred.eval_any,
            Minidregg.Pred.eval, Minidregg.Pred.evalWith, requestSubject, verb,
            Nat.cast_inj, notOwner, refillPolicy_needs_slot old new noRefill]
          intro _
          refine ⟨workerFalseWith first (by simp), workerFalseWith second (by simp), ?_⟩
          intro worker named
          exact workerFalseWith worker (by simp [named])

/-- info: 'Minidregg.Host.Json.grainPolicy_unnamed_worker_refused' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms grainPolicy_unnamed_worker_refused

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

/-- The factory template an authoring request names. `birthSlack` is optional
and defaults to the runtime default; the receiver's own template decides it
either way, because the template is inside the semantics digest the request
is pinned to. -/
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

/-- K-NARROW-HIDE: put the owner-derived blinding into a newborn cell.  Only
declared and content cells carry one; the owner's client derives it from its
own key material and the cell id (`mini`, `hiding.rs`), so the host never
chooses it. -/
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

/-- A grain birth at a target the Host pins as a provider service is a
provider purse: its law carries the pinned per-route fees and its store the
route field. The schedule comes from the Host's own pinned tariff, never from
the birth request. -/
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
  -- `"open"`; absent, it declares none and holds none.  `fieldsFrom` adds the
  -- unbounded tail (every field at or above it) to a closed declaration.
  let fieldsField := if storage = "declared" ∧ (raw.get? "fields").isSome then ["fields"] else []
  let fieldsFromField :=
    if storage = "declared" ∧ (raw.get? "fieldsFrom").isSome then ["fieldsFrom"] else []
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
      roomField ++ blindingField ++ fieldsField ++ fieldsFromField ++ worldFields) json
  let tail ← match obj.get? "fieldsFrom" with
    | none => pure none
    | some value => some <$> nat (path ++ ".fieldsFrom") value
  let declaration : Minidregg.Kernel.FieldClosure.FieldSet ← match obj.get? "fields", tail with
    | none, tail => pure (.closed [] tail)
    | some (.str "open"), none => pure .open
    | some (.str "open"), some _ =>
        throw s!"{path}.fieldsFrom: an open cell already declares every field"
    | some value, tail => do
        let fields ← list (path ++ ".fields") nat value
        pure (Minidregg.Kernel.FieldClosure.FieldSet.closed fields tail)
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

/-- A standard birth is built entirely through the deployed source helpers:
absent roots, declared cells, owner/control grants, policy addresses, identity,
nullifier and quoted fee are never supplied as JSON assertions. -/
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

/-- Author an ordinary resource birth against a verifier-loaded image. The
caller supplies its checked current height and authority state; this parser
checks the supplied genesis against the pinned seed before using it for
immutable deployment coordinates. Current grant epochs come only from the
loaded authority, never from that genesis description. -/
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
  let template ← factoryTemplate (path ++ ".template") (← field path "template" obj)
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

/-- Pure closed authoring only. Current owner program authority is still
required by ordinary policy installation; authoring does not install a law. -/
def applicationManagedPolicy (path : String) (json : Lean.Json) : Result Minidregg.Pred.Pred := do
  let obj ← exactObject path ["kind", "app", "packageManifest", "snapshotManifest",
    "owner", "manager"] json
  let app ← nat (path ++ ".app") (← field path "app" obj)
  let package ← nat (path ++ ".packageManifest") (← field path "packageManifest" obj)
  let snapshot ← nat (path ++ ".snapshotManifest") (← field path "snapshotManifest" obj)
  unless app ≠ package ∧ app ≠ snapshot ∧ package ≠ snapshot do
    failAt path "app, packageManifest and snapshotManifest must be distinct"
  let owner ← nat (path ++ ".owner") (← field path "owner" obj)
  let manager ← nat (path ++ ".manager") (← field path "manager" obj)
  match ← string (path ++ ".kind") (← field path "kind" obj) with
  | "app" => pure (ApplicationGrain.managedPolicy package snapshot owner manager)
  | "package" => pure (ApplicationGrain.managedPackagePolicy app owner manager)
  | "snapshot" => pure (ApplicationGrain.managedSnapshotPolicy app owner manager)
  | _ => failAt (path ++ ".kind") "expected app, package or snapshot"

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
    (deployed : Option NativeHost.Config := none)
    (providerRoutes : List (Nat × ProviderMetering.Schedule) := []) : Result Draft :=
  grainBirthFrom path "birth" json (fun path source tariff =>
    birth path source tariff deployed none none providerRoutes)

private def grainBirthIntent (path : String) (json : Lean.Json)
    (deployed : Option NativeHost.Config := none)
    (providerRoutes : List (Nat × ProviderMetering.Schedule) := []) : Result Intent := do
  let obj ← exactObject path ["subject", "nonce", "grainBirth", "grants"] json
  pure ⟨⟨← nat (path ++ ".subject") (← field path "subject" obj)⟩,
    ← nat (path ++ ".nonce") (← field path "nonce" obj),
    .prepare (← grainBirth (path ++ ".grainBirth") (← field path "grainBirth" obj) deployed
      providerRoutes),
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
    (deployed : Option NativeHost.Config := none)
    (providerRoutes : List (Nat × ProviderMetering.Schedule) := []) : Result Intent :=
  birthIntentFrom path json (fun birthPath source =>
    birth birthPath source none deployed none none providerRoutes)

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

/-- A grain transition. A provider purse's `before` carries its fifth
coordinate, `route`; its reserve names the route the call takes and its settle
names the route it is charged by, which must be the one the purse recorded.
The command then writes all five coordinates, so the receiver compares the
recorded route against the durable store as well. The third component is the
route after the transition (provider purses only). -/
private def grainSource (path : String) (json : Lean.Json) :
    Result (DeclaredResourceController.Command × AgentGrain.State × Option Int) := do
  let obj ← object path json
  for key in obj.foldl (init := []) (fun names key _ => key :: names) do
    unless ["task", "subject", "capability",
      "schemaVersion", "expectedTargetRoot", "context", "before", "operation",
      "publications", "observeCapability", "parentWitness"].contains key do
      throw s!"{path}: unknown field {key}"
  let beforeRaw ← object (path ++ ".before") (← field path "before" obj)
  let routed := (beforeRaw.get? "route").isSome
  let stateObj ← exactObject (path ++ ".before")
    (["generation", "status", "remaining", "reserved"] ++ (if routed then ["route"] else []))
    (← field path "before" obj)
  let state : AgentGrain.State := ⟨← int (path ++ ".before.generation") (← field (path ++ ".before") "generation" stateObj),
    ← int (path ++ ".before.status") (← field (path ++ ".before") "status" stateObj),
    ← int (path ++ ".before.remaining") (← field (path ++ ".before") "remaining" stateObj),
    ← int (path ++ ".before.reserved") (← field (path ++ ".before") "reserved" stateObj)⟩
  let routeBefore ← if routed then
      some <$> int (path ++ ".before.route") (← field (path ++ ".before") "route" stateObj)
    else pure none
  let operationJson ← field path "operation" obj
  let (tag, _) ← tagged (path ++ ".operation") operationJson
  let (operation, routeCode) ← (match tag with
    | "input" => exactObject (path ++ ".operation") ["type"] operationJson *>
        pure (AgentGrain.Operation.input, routeBefore.getD 0)
    | "attach" | "mode" => do
        let op ← exactObject (path ++ ".operation") ["type", "soft"] operationJson
        let soft ← bool (path ++ ".operation.soft") (← field (path ++ ".operation") "soft" op)
        pure (if tag = "attach" then AgentGrain.Operation.attach soft else .mode soft,
          routeBefore.getD 0)
    | "reserve" | "settle" => do
        let name := if tag = "reserve" then "amount" else "charge"
        let op ← exactObject (path ++ ".operation")
          (["type", name] ++ (if routed then ["route"] else [])) operationJson
        let value ← int (path ++ ".operation." ++ name) (← field (path ++ ".operation") name op)
        let route ← if routed then do
            let named ← string (path ++ ".operation.route") (← field (path ++ ".operation") "route" op)
            match ProviderMetering.Route.ofName? named with
            | some route => pure route.code
            | none => failAt (path ++ ".operation.route") "expected user, pool or homelab"
          else pure 0
        if tag = "settle" ∧ routed ∧ some route ≠ routeBefore then
          failAt (path ++ ".operation.route")
            "route-mismatch: the settle names another route than the purse recorded at reserve"
        pure (if tag = "reserve" then AgentGrain.Operation.reserve value
          else AgentGrain.Operation.settle value, route)
    | "disconnect" => exactObject (path ++ ".operation") ["type"] operationJson *>
        pure (AgentGrain.Operation.disconnect, routeBefore.getD 0)
    | "interrupt" => exactObject (path ++ ".operation") ["type"] operationJson *>
        pure (AgentGrain.Operation.interrupt, routeBefore.getD 0)
    | "cancel" => exactObject (path ++ ".operation") ["type"] operationJson *>
        pure (AgentGrain.Operation.cancel, routeBefore.getD 0)
    | _ => failAt (path ++ ".operation.type") "unknown grain operation" :
      Result (AgentGrain.Operation × Int))
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
  match routeBefore with
  | none =>
      let command := operation.command subject (AgentGrain.contextNonce contextBytes)
        task capability targetRoot state publications observeCapability
      pure (command, operation.after state, none)
  | some recorded =>
      let before : ProviderRoute.State := ⟨state, recorded⟩
      let after := ProviderRoute.after operation routeCode before
      let command : DeclaredResourceController.Command :=
        { subject := subject, nonce := AgentGrain.contextNonce contextBytes,
          targets := ProviderRoute.target operation routeCode task capability targetRoot before
            observeCapability :: publications }
      pure (command, after.grain, some after.route)

/-- Wrap a source-authored grain transition in the ordinary prepare intent. -/
private def grainIntent (path : String) (json : Lean.Json) : Result Intent := do
  let obj ← exactObject path ["grain", "grants", "intentNonce"] json
  let source ← grainSource (path ++ ".grain") (← field path "grain" obj)
  let grants ← list (path ++ ".grants") grant (← field path "grants" obj)
  let nonce ← nat (path ++ ".intentNonce") (← field path "intentNonce" obj)
  pure ⟨source.1.subject, nonce,
    .prepare (.invoke (DeclaredResourceController.commandCodec.encode source.1)), grants⟩

/-- Re-pin a worker's no-op witness to a newly attached generation through
the ordinary signed policy-install receiver. Canonical currentSourceHex must
match every supplied source pin; the update retains composition, audience and
program descriptor metadata. Current authority/head admission still belongs to
the receiver: authoring neither authenticates a caller's snapshot nor asserts
cryptographic digest injectivity. -/
private def grainPolicyInstallIntent (path : String) (json : Lean.Json)
    (providerRoutes : List (Nat × ProviderMetering.Schedule) := []) : Result Intent := do
  let raw ← object path json
  let some worker ← grainWorker path raw
    | failAt path "worker subject and generation required"
  let obj ← exactObject path (["subject", "intentNonce", "declarationNonce", "task",
    "owner", "control", "domain", "semantics", "expectedPreRoot", "expectedVersion",
    "expectedAddress", "currentSourceHex", "grants"] ++ grainWorkerFields raw) json
  let subject := SubjectId.mk (← nat (path ++ ".subject") (← field path "subject" obj))
  let owner ← nat (path ++ ".owner") (← field path "owner" obj)
  let task ← nat (path ++ ".task") (← field path "task" obj)
  let version ← nat (path ++ ".expectedVersion") (← field path "expectedVersion" obj)
  let address := Digest.mk (← nat (path ++ ".expectedAddress")
    (← field path "expectedAddress" obj))
  let domain := Digest.mk (← nat (path ++ ".domain") (← field path "domain" obj))
  let semantics := Digest.mk (← nat (path ++ ".semantics") (← field path "semantics" obj))
  let currentBytes ← decodeHex (path ++ ".currentSourceHex")
    (← field path "currentSourceHex" obj)
  let some current := PolicyRecordCodec.decode currentBytes
    | failAt (path ++ ".currentSourceHex") "expected canonical current policy source"
  unless PolicyRecordCodec.digest current = address do
    failAt (path ++ ".expectedAddress") "does not match current policy source"
  unless current.policyId.value = task do
    failAt (path ++ ".task") "does not match current policy source"
  unless current.version = version do
    failAt (path ++ ".expectedVersion") "does not match current policy source"
  unless current.domain = domain do
    failAt (path ++ ".domain") "does not match current policy source"
  unless current.semantics = semantics do
    failAt (path ++ ".semantics") "does not match current policy source"
  let nextPredicate := match providerRoutes.lookup task with
    | some routes => ProviderRoute.policy routes (grainPolicy owner (some worker))
    | none => grainPolicy owner (some worker)
  let source : PolicyRecord :=
    { current with
      version := version + 1
      previous := some address
      predicate := nextPredicate }
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

/-- The resident signed-SPK profile names units by Store (`Config.expectedSeed`):
its authoring kinds run only against a deployed config. -/
private def residentStore (deployed : Option NativeHost.Config) : Result Digest :=
  match deployed with
  | some config => pure config.expectedSeed
  | none => throw "resident signed-SPK authoring needs the deployed config (its Store names the unit)"

/-- Validate an already signed BEGIN-v2 frame for this physical host profile.
The generic native BEGIN route and historical replay remain unchanged. -/
private def residentBegin (store : Digest) (json : Lean.Json) : Result (List UInt8) := do
  let obj ← exactObject "$" ["begin"] json
  let bytes ← decodeHex "$.begin" (← field "$" "begin" obj)
  let some ingress := ApplicationLifecycleBeginV2Ingress.codec.decode bytes
    | throw "noncanonical BEGIN-v2 ingress"
  unless ApplicationLifecycleResidentProfile.beginMatches store ingress do
    throw "BEGIN-v2 is outside the resident signed-SPK physical hosting profile"
  return ingress.canonicalBytes

private def completionReport (store : Digest) (json : Lean.Json) : Result (List UInt8) := do
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
  let report ← ApplicationLifecycleCompletionAuthoring.reportPlan store
    (← decodeHex "$.begin" (← field "$" "begin" obj))
    (← decodeHex "$.claim" (← field "$" "claim" obj)) observed
  return ApplicationLifecycleCompletionReport.codec.encode report

private def completionSigningFrame (store : Digest) (json : Lean.Json) : Result (List UInt8) := do
  let obj ← exactObject "$" ["domain", "semantics", "begin", "report"] json
  ApplicationLifecycleCompletionAuthoring.signingPlan store
    (← completionDigest "$.domain" (← field "$" "domain" obj))
    (← completionDigest "$.semantics" (← field "$" "semantics" obj))
    (← decodeHex "$.begin" (← field "$" "begin" obj))
    (← decodeHex "$.report" (← field "$" "report" obj))

private def completionSignedReport (store : Digest) (json : Lean.Json) : Result (List UInt8) := do
  let obj ← exactObject "$" ["begin", "report", "signature"] json
  ApplicationLifecycleCompletionAuthoring.signedReport store
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

private def completionSource (store : Digest) (json : Lean.Json) : Result (List UInt8) := do
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
  let source ← ApplicationLifecycleCompletionAuthoring.sourcePlan store
    (← decodeHex "$.begin" (← field "$" "begin" obj))
    (← decodeHex "$.claimIngress" (← field "$" "claimIngress" obj))
    (← decodeHex "$.signedReport" (← field "$" "signedReport" obj)) current
  return ApplicationLifecycleCompletionSource.codec.encode source

/-- Physical observations are supplied by the protected host. The source
helper derives the volume identity and canonical retry v4 report. -/
private def retryPhysicalReport (json : Lean.Json) : Result (List UInt8) := do
  let obj ← exactObject "$" ["begin", "committedClaim", "nonce", "unit",
    "materializedImage", "outcome", "invocationId", "controlGroup", "pid",
    "stopAudit", "volumeWitness"] json
  let outcome ← match ← string "$.outcome" (← field "$" "outcome" obj) with
    | "materialized" => pure ApplicationLifecycleCompletionReport.Outcome.materialized
    | "running" => pure .running
    | "stopped" => pure .stopped
    | _ => failAt "$.outcome" "expected materialized, running, or stopped"
  let observed : ApplicationLifecycleRetryLaunchReportAuthoring.PhysicalObservation := {
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
  let report ← ApplicationLifecycleRetryLaunchReportAuthoring.reportPlan
    (← decodeHex "$.begin" (← field "$" "begin" obj))
    (← decodeHex "$.committedClaim" (← field "$" "committedClaim" obj)) observed
  return ApplicationLifecycleRetryCompletionV4Report.codec.encode report

private def retryPhysicalSigningFrame (json : Lean.Json) : Result (List UInt8) := do
  let obj ← exactObject "$" ["begin", "report"] json
  ApplicationLifecycleRetryLaunchReportAuthoring.signingPlan
    (← decodeHex "$.begin" (← field "$" "begin" obj))
    (← decodeHex "$.report" (← field "$" "report" obj))

private def retryPhysicalSignedReport (json : Lean.Json) : Result (List UInt8) := do
  let obj ← exactObject "$" ["begin", "report", "signature"] json
  ApplicationLifecycleRetryLaunchReportAuthoring.signedReport
    (← decodeHex "$.begin" (← field "$" "begin" obj))
    (← decodeHex "$.report" (← field "$" "report" obj))
    (← decodeHex "$.signature" (← field "$" "signature" obj))

private def retryCompletionSource (store : Minidregg.Theory.TypedAuthorization.Digest) (json : Lean.Json) : Result (List UInt8) := do
  let obj ← exactObject "$" ["begin", "claimIngress", "signedReport",
    "appRoot", "packageRoot", "appCapability", "appObserveCapability",
    "packageCapability", "packageObserveCapability", "packageAtomBefore"] json
  let current : ApplicationLifecycleRetryLaunchReportAuthoring.CurrentObservation :=
    { appRoot := ← completionDigest "$.appRoot" (← field "$" "appRoot" obj)
      packageRoot := ← completionDigest "$.packageRoot" (← field "$" "packageRoot" obj)
      appCapability := ⟨← nat "$.appCapability" (← field "$" "appCapability" obj)⟩
      appObserveCapability := ⟨← nat "$.appObserveCapability" (← field "$" "appObserveCapability" obj)⟩
      packageCapability := ⟨← nat "$.packageCapability" (← field "$" "packageCapability" obj)⟩
      packageObserveCapability := ⟨← nat "$.packageObserveCapability" (← field "$" "packageObserveCapability" obj)⟩
      packageAtomBefore := ← optional "$.packageAtomBefore" atomRecord
        (← field "$" "packageAtomBefore" obj) }
  let source ← ApplicationLifecycleRetryLaunchReportAuthoring.sourcePlan store
    (← decodeHex "$.begin" (← field "$" "begin" obj))
    (← decodeHex "$.claimIngress" (← field "$" "claimIngress" obj))
    (← decodeHex "$.signedReport" (← field "$" "signedReport" obj)) current
  return ApplicationLifecycleRetryCompletionV4Source.codec.encode source

private def retryCompletionCommand (json : Lean.Json) : Result (List UInt8) := do
  let obj ← exactObject "$" ["domain", "semantics", "source"] json
  ApplicationLifecycleRetryLaunchReportAuthoring.commandPlan
    (← completionDigest "$.domain" (← field "$" "domain" obj))
    (← completionDigest "$.semantics" (← field "$" "semantics" obj))
    (← decodeHex "$.source" (← field "$" "source" obj))

private def retryCompletionIngress (json : Lean.Json) : Result (List UInt8) := do
  let obj ← exactObject "$" ["domain", "semantics", "source", "signedCommand",
    "packageObservationEnvelope"] json
  ApplicationLifecycleRetryLaunchReportAuthoring.assemble
    (← completionDigest "$.domain" (← field "$" "domain" obj))
    (← completionDigest "$.semantics" (← field "$" "semantics" obj))
    (← decodeHex "$.source" (← field "$" "source" obj))
    (← decodeHex "$.signedCommand" (← field "$" "signedCommand" obj))
    (← decodeHex "$.packageObservationEnvelope"
      (← field "$" "packageObservationEnvelope" obj))

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

private def retrySelector (json : Lean.Json) :
    Result ApplicationFailedCreateRetryEvidence.Selector := do
  let obj ← exactObject "$.retry" ["recoveryIndex", "recoveryIngress"] json
  let recoveryBytes ← decodeHex "$.retry.recoveryIngress" (← field "$.retry" "recoveryIngress" obj)
  let some recovery := ApplicationFailedStartRecoveryIngress.codec.decode recoveryBytes
    | failAt "$.retry.recoveryIngress" "noncanonical failed-start recovery ingress"
  return { recoveryIndex := ← nat "$.retry.recoveryIndex" (← field "$.retry" "recoveryIndex" obj)
           recovery := recovery }

private def retryBeginOperatorRequest (json : Lean.Json) : Result (List UInt8) := do
  let obj ← exactObject "$" ["clientOperationId", "descriptor", "createIndex", "retry"] json
  let request : ApplicationLifecycleRetryBeginV4Authoring.Request :=
    { launch :=
        { kind := .start
          clientOperationId := ← nat "$.clientOperationId" (← field "$" "clientOperationId" obj)
          descriptorBytes := ← decodeHex "$.descriptor" (← field "$" "descriptor" obj)
          createIndex := some (← nat "$.createIndex" (← field "$" "createIndex" obj)) }
      retry := ← retrySelector (← field "$" "retry" obj) }
  let bytes := ApplicationLifecycleRetryBeginV4Authoring.requestCodec.encode request
  let _ ← ApplicationLifecycleRetryBeginV4Inspection.inspectRequest bytes
  return bytes

private def retryClaimOperatorRequest (json : Lean.Json) : Result (List UInt8) := do
  let obj ← exactObject "$" ["originalIndex", "queryNonce"] json
  let request : ApplicationLifecycleRetryClaimV4Authoring.Request :=
    { originalIndex := ← nat "$.originalIndex" (← field "$" "originalIndex" obj)
      queryNonce := ← nat "$.queryNonce" (← field "$" "queryNonce" obj) }
  return ApplicationLifecycleRetryClaimV4Authoring.requestCodec.encode request

private def retryCompletionOperatorRequest (json : Lean.Json) : Result (List UInt8) := do
  let obj ← exactObject "$" ["begin", "claimIngress", "signedReport"] json
  let request : ApplicationLifecycleRetryCompletionV4Authoring.Request :=
    { beginBytes := ← decodeHex "$.begin" (← field "$" "begin" obj)
      claimIngressBytes := ← decodeHex "$.claimIngress" (← field "$" "claimIngress" obj)
      signedReportBytes := ← decodeHex "$.signedReport" (← field "$" "signedReport" obj) }
  let bytes := ApplicationLifecycleRetryCompletionV4Authoring.requestCodec.encode request
  let _ ← ApplicationLifecycleRetryCompletionV4Inspection.inspectRequest bytes
  return bytes

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

/-- A certify: the certifier names the current head and its chain value,
pinning the current factory, authority and system roots (all from the
certify view). -/
private def certify (json : Lean.Json) : Result (List UInt8) := do
  let obj ← exactObject "$" ["sponsor", "control", "nonce", "expectedFactoryRoot",
    "expectedAuthorityRoot", "expectedSystemRoot", "height", "digest"] json
  let command : CertifyReceiver.Command :=
    { sponsor := ⟨← nat "$.sponsor" (← field "$" "sponsor" obj)⟩
      control := ⟨← nat "$.control" (← field "$" "control" obj)⟩
      nonce := ← nat "$.nonce" (← field "$" "nonce" obj)
      expectedFactoryRoot := ⟨← nat "$.expectedFactoryRoot" (← field "$" "expectedFactoryRoot" obj)⟩
      expectedAuthorityRoot :=
        ⟨← nat "$.expectedAuthorityRoot" (← field "$" "expectedAuthorityRoot" obj)⟩
      expectedSystemRoot := ⟨← nat "$.expectedSystemRoot" (← field "$" "expectedSystemRoot" obj)⟩
      height := ← nat "$.height" (← field "$" "height" obj)
      digest := ⟨← nat "$.digest" (← field "$" "digest" obj)⟩ }
  return CertifyReceiver.commandCodec.encode command

/-- A clock tick: a ticker asserts `now` (unix seconds) and `slot` under its
`C_tick` (`capability`), pinning the current authority and clock roots (from
the clock view). -/
private def clockTick (json : Lean.Json) : Result (List UInt8) := do
  let obj ← exactObject "$" ["sponsor", "capability", "nonce",
    "expectedAuthorityRoot", "expectedClockRoot", "now", "slot"] json
  let command : ClockTickReceiver.Command :=
    { sponsor := ⟨← nat "$.sponsor" (← field "$" "sponsor" obj)⟩
      capability := ⟨← nat "$.capability" (← field "$" "capability" obj)⟩
      nonce := ← nat "$.nonce" (← field "$" "nonce" obj)
      expectedAuthorityRoot :=
        ⟨← nat "$.expectedAuthorityRoot" (← field "$" "expectedAuthorityRoot" obj)⟩
      expectedClockRoot := ⟨← nat "$.expectedClockRoot" (← field "$" "expectedClockRoot" obj)⟩
      now := ← nat "$.now" (← field "$" "now" obj)
      slot := ← nat "$.slot" (← field "$" "slot" obj) }
  return ClockTickReceiver.commandCodec.encode command

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

/-- Source-owned authoring of a subject key rotation command.  These bytes
claim nothing: admission checks the commitment and the new key's signature. -/
private def subjectKeyRotation (json : Lean.Json) : Result (List UInt8) := do
  let obj ← exactObject "$" ["subject", "nonce", "key"] json
  let command : SubjectKeyRotation.Command :=
    { subject := ⟨← nat "$.subject" (← field "$" "subject" obj)⟩
      nonce := ← nat "$.nonce" (← field "$" "nonce" obj)
      key := ← keyRecord "$.key" (← field "$" "key" obj) }
  return SubjectKeyRotation.commandCodec.encode command

/-- The pre-rotation commitment to one public key, as the canonical decimal of
`ParticipantKeyEnrollment.nextKeyDigest` (UTF-8).  The client never hashes; this is
the one place the digest is computed for it. -/
private def signingKeyNextDigest (json : Lean.Json) : Result (List UInt8) := do
  let obj ← exactObject "$" ["publicKey"] json
  let publicKey ← decodeHex "$.publicKey" (← field "$" "publicKey" obj)
  unless publicKey.length = 32 do failAt "$.publicKey" "expected 32 bytes"
  return (toString (ParticipantKeyEnrollment.nextKeyDigest publicKey).value).toUTF8.toList

/-- The exact bytes a committed next key co-signs at enrollment
(`ParticipantKeyEnrollment.nextPossessionFrame`).  A client that made the
co-signature offline checks it against these bytes before planning. -/
private def enrollmentNextPossession (json : Lean.Json) : Result (List UInt8) := do
  let obj ← exactObject "$" ["publicKey", "nextPublicKey"] json
  let publicKey ← decodeHex "$.publicKey" (← field "$" "publicKey" obj)
  unless publicKey.length = 32 do failAt "$.publicKey" "expected 32 bytes"
  let nextPublicKey ← decodeHex "$.nextPublicKey" (← field "$" "nextPublicKey" obj)
  unless nextPublicKey.length = 32 do failAt "$.nextPublicKey" "expected 32 bytes"
  return ParticipantKeyEnrollment.nextPossessionFrame publicKey nextPublicKey

/-- Source-owned authoring for a factory-observation provisioning request.
These bytes name a holder and a fresh identifier; they do not claim that the
holder is enrolled, that the identifier is fresh, or that the sponsor may act. -/
private def participantFactoryProvisioning (json : Lean.Json) : Result (List UInt8) := do
  let obj ← exactObject "$" ["sponsor", "control", "nonce",
    "expectedFactoryRoot", "expectedAuthorityRoot", "holder", "capability"] json
  let command : ParticipantFactoryProvisioning.Command :=
    { sponsor := ⟨← nat "$.sponsor" (← field "$" "sponsor" obj)⟩
      control := ⟨← nat "$.control" (← field "$" "control" obj)⟩
      nonce := ← nat "$.nonce" (← field "$" "nonce" obj)
      expectedFactoryRoot := ⟨← nat "$.expectedFactoryRoot"
        (← field "$" "expectedFactoryRoot" obj)⟩
      expectedAuthorityRoot := ⟨← nat "$.expectedAuthorityRoot"
        (← field "$" "expectedAuthorityRoot" obj)⟩
      holder := ⟨← nat "$.holder" (← field "$" "holder" obj)⟩
      capability := ⟨← nat "$.capability" (← field "$" "capability" obj)⟩ }
  return ParticipantFactoryProvisioning.commandCodec.encode command

/-- A realm-well command (lane K-WELL): `op` is `mint` or `burn`. -/
private def wellCommand (json : Lean.Json) : Result (List UInt8) := do
  let obj ← exactObject "$" ["subject", "capability", "well", "op", "account", "amount", "nonce"] json
  let op ← match ← string "$.op" (← field "$" "op" obj) with
    | "mint" => pure RealmWellCodec.WellOp.mint
    | "burn" => pure RealmWellCodec.WellOp.burn
    | _ => failAt "$.op" "expected mint or burn"
  let command : RealmWellCodec.Command :=
    { subject := ⟨← nat "$.subject" (← field "$" "subject" obj)⟩
      capability := ⟨← nat "$.capability" (← field "$" "capability" obj)⟩
      well := ← nat "$.well" (← field "$" "well" obj)
      op := op
      account := ← nat "$.account" (← field "$" "account" obj)
      amount := ← nat "$.amount" (← field "$" "amount" obj)
      nonce := ← nat "$.nonce" (← field "$" "nonce" obj) }
  return RealmWellCodec.commandCodec.encode command

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

/-- Source-owned authoring for one fleet turn draft. `fee` and a zero
publication `sequence` are finalized by the Host plan from pinned tariff and
current topic head; the signer then signs the finalized command. -/
private def fleetTurnCommand (json : Lean.Json) : Result (List UInt8) := do
  let obj ← exactObject "$" ["subject", "payer", "spend", "nonce", "fee",
    "transfer", "publication"] json
  let transfer ← optional "$.transfer" (fun path value => do
    let t ← exactObject path ["destination", "asset", "amount"] value
    pure ({ destination := ← nat (path ++ ".destination") (← field path "destination" t)
            asset := ← nat (path ++ ".asset") (← field path "asset" t)
            amount := ← nat (path ++ ".amount") (← field path "amount" t) } :
      FleetTurn.Transfer)) (← field "$" "transfer" obj)
  let publication ← optional "$.publication" (fun path value => do
    let p ← exactObject path ["topic", "sequence", "payload"] value
    pure ({ topic := ← decodeHex (path ++ ".topic") (← field path "topic" p)
            sequence := ← nat (path ++ ".sequence") (← field path "sequence" p)
            payload := ← decodeHex (path ++ ".payload") (← field path "payload" p) } :
      FleetTurn.Publication)) (← field "$" "publication" obj)
  let command : FleetTurn.Command :=
    { subject := ⟨← nat "$.subject" (← field "$" "subject" obj)⟩
      payer := ← nat "$.payer" (← field "$" "payer" obj)
      spend := ⟨← nat "$.spend" (← field "$" "spend" obj)⟩
      nonce := ← nat "$.nonce" (← field "$" "nonce" obj)
      fee := ← nat "$.fee" (← field "$" "fee" obj)
      transfer := transfer
      publication := publication }
  -- A draft may leave the topic position zero for the Host plan to assign;
  -- every other shape rule is the receiver's own.
  let assigned : FleetTurn.Command := { command with
    publication := command.publication.map fun (p : FleetTurn.Publication) =>
      ({ p with sequence := max p.sequence 1 } : FleetTurn.Publication) }
  unless assigned.shapeOk do
    failAt "$" "a fleet turn needs a positive transfer to another account or a 1..64-byte topic event with at most 16384 payload bytes"
  return FleetTurn.commandCodec.encode command
/-- A pay tariff: every field a canonical decimal string except `mint` and
`tokenProgram`, which are lowercase hex of the raw 32 bytes. -/
private def payTariff (path : String) (json : Lean.Json) : Result PayTariff.Tariff := do
  let obj ← exactObject path ["version", "asset", "mint", "tokenProgram", "decimals",
    "creditPerAtomic", "maxPerObservation", "minTickSlots", "nodeWeekRate", "enrolIndex",
    "journalFloor", "slashCallerPermille"] json
  pure
    { version := ← nat s!"{path}.version" (← field path "version" obj)
      asset := ← nat s!"{path}.asset" (← field path "asset" obj)
      mint := ← decodeHex s!"{path}.mint" (← field path "mint" obj)
      tokenProgram := ← decodeHex s!"{path}.tokenProgram" (← field path "tokenProgram" obj)
      decimals := ← nat s!"{path}.decimals" (← field path "decimals" obj)
      creditPerAtomic := ← nat s!"{path}.creditPerAtomic" (← field path "creditPerAtomic" obj)
      maxPerObservation := ← nat s!"{path}.maxPerObservation" (← field path "maxPerObservation" obj)
      minTickSlots := ← nat s!"{path}.minTickSlots" (← field path "minTickSlots" obj)
      nodeWeekRate := ← nat s!"{path}.nodeWeekRate" (← field path "nodeWeekRate" obj)
      enrolIndex := ← optional s!"{path}.enrolIndex" nat (← field path "enrolIndex" obj)
      journalFloor := ← nat s!"{path}.journalFloor" (← field path "journalFloor" obj)
      slashCallerPermille := ← nat s!"{path}.slashCallerPermille"
        (← field path "slashCallerPermille" obj) }

/-- The operator's pay-cell change: deposit rows (hex) appended from
`bookStart`, and/or a new tariff (`null` for none).  The bytes claim nothing:
the receiver decides the rows, the tariff version and the authority. -/
private def payBook (json : Lean.Json) : Result (List UInt8) := do
  let obj ← exactObject "$" ["sponsor", "control", "nonce", "expectedFactoryRoot",
    "expectedAuthorityRoot", "expectedPayRoot", "bookStart", "book", "tariff"] json
  let command : PayBookReceiver.Command :=
    { sponsor := ⟨← nat "$.sponsor" (← field "$" "sponsor" obj)⟩
      control := ⟨← nat "$.control" (← field "$" "control" obj)⟩
      nonce := ← nat "$.nonce" (← field "$" "nonce" obj)
      expectedFactoryRoot := ⟨← nat "$.expectedFactoryRoot" (← field "$" "expectedFactoryRoot" obj)⟩
      expectedAuthorityRoot := ⟨← nat "$.expectedAuthorityRoot"
        (← field "$" "expectedAuthorityRoot" obj)⟩
      expectedPayRoot := ⟨← nat "$.expectedPayRoot" (← field "$" "expectedPayRoot" obj)⟩
      bookStart := ← nat "$.bookStart" (← field "$" "bookStart" obj)
      book := ← list "$.book" decodeHex (← field "$" "book" obj)
      tariff := ← optional "$.tariff" payTariff (← field "$" "tariff" obj) }
  return PayBookReceiver.commandCodec.encode command

/-- A subject's request that book index `index` be bound to `account`. -/
private def payAssign (json : Lean.Json) : Result (List UInt8) := do
  let obj ← exactObject "$" ["subject", "capability", "account", "index", "nonce",
    "expectedAuthorityRoot", "expectedPayRoot"] json
  let command : PayAssignmentReceiver.Command :=
    { subject := ⟨← nat "$.subject" (← field "$" "subject" obj)⟩
      capability := ⟨← nat "$.capability" (← field "$" "capability" obj)⟩
      account := ← nat "$.account" (← field "$" "account" obj)
      index := ← nat "$.index" (← field "$" "index" obj)
      nonce := ← nat "$.nonce" (← field "$" "nonce" obj)
      expectedAuthorityRoot := ⟨← nat "$.expectedAuthorityRoot"
        (← field "$" "expectedAuthorityRoot" obj)⟩
      expectedPayRoot := ⟨← nat "$.expectedPayRoot" (← field "$" "expectedPayRoot" obj)⟩ }
  return PayAssignmentReceiver.commandCodec.encode command

/-- The owner's refill: burn `amount` credit from `account` into the purse of
AgentGrain task `task`, whose leg claims `gain` (the joint turn refuses
`unbalanced` unless they agree). -/
private def payRefill (json : Lean.Json) : Result (List UInt8) := do
  let obj ← exactObject "$" ["subject", "capability", "account", "task", "amount", "gain",
    "nonce", "expectedAuthorityRoot"] json
  let command : PurseRefillReceiver.Command :=
    { subject := ⟨← nat "$.subject" (← field "$" "subject" obj)⟩
      capability := ⟨← nat "$.capability" (← field "$" "capability" obj)⟩
      account := ← nat "$.account" (← field "$" "account" obj)
      task := ← nat "$.task" (← field "$" "task" obj)
      amount := ← nat "$.amount" (← field "$" "amount" obj)
      gain := ← nat "$.gain" (← field "$" "gain" obj)
      nonce := ← nat "$.nonce" (← field "$" "nonce" obj)
      expectedAuthorityRoot := ⟨← nat "$.expectedAuthorityRoot"
        (← field "$" "expectedAuthorityRoot" obj)⟩ }
  return PurseRefillReceiver.commandCodec.encode command

/-- A job-money command (lane C3): `action` 1 fund · 2 claim · 3 settle.
The bytes claim nothing: the receiver decides every amount a settle pays. -/
private def jobMoney (json : Lean.Json) : Result (List UInt8) := do
  let obj ← exactObject "$" ["subject", "capability", "jobCapability", "job", "action",
    "account", "amount", "nonce", "expectedAuthorityRoot"] json
  let command : JobMoneyReceiver.Command :=
    { subject := ⟨← nat "$.subject" (← field "$" "subject" obj)⟩
      capability := ⟨← nat "$.capability" (← field "$" "capability" obj)⟩
      jobCapability := ⟨← nat "$.jobCapability" (← field "$" "jobCapability" obj)⟩
      job := ← nat "$.job" (← field "$" "job" obj)
      action := ← nat "$.action" (← field "$" "action" obj)
      account := ← nat "$.account" (← field "$" "account" obj)
      amount := ← nat "$.amount" (← field "$" "amount" obj)
      nonce := ← nat "$.nonce" (← field "$" "nonce" obj)
      expectedAuthorityRoot := ⟨← nat "$.expectedAuthorityRoot"
        (← field "$" "expectedAuthorityRoot" obj)⟩ }
  return JobMoneyReceiver.commandCodec.encode command

/-- A natural number as the pay watcher emits it (a JSON integer) or as the
Host's own JSON writes it (a canonical unsigned decimal string). -/
private def natOrNumber (path : String) (json : Lean.Json) : Result Nat :=
  match json with
  | .num number =>
      if number.exponent = 0 ∧ 0 ≤ number.mantissa then pure number.mantissa.toNat
      else failAt path "unsigned integer expected"
  | _ => nat path json

/-- The watcher's memo pair (P1b): `memo` is hex of the one memo's raw bytes
or `null`; `memoError` is `null`, `"memoUnbound"` (two or more memo
instructions) or `"memoInvalid"` (not UTF-8, or over 566 bytes).  Both set is
refused. -/
private def payMemoField (path : String) (memo memoError : Lean.Json) :
    Result PayEnrolMemo.MemoField := do
  let bytes ← optional s!"{path}.memo" decodeHex memo
  let error ← optional s!"{path}.memoError" string memoError
  match bytes, error with
  | none, none => pure .absent
  | some bytes, none => pure (.present bytes)
  | none, some "memoUnbound" => pure .unbound
  | none, some "memoInvalid" => pure .invalid
  | none, some other => failAt s!"{path}.memoError" s!"unknown memo error {other}"
  | some _, some _ => failAt path "memo and memoError are both set"

/-- One observation in the pay watcher's record shape (lanes P1/P1b
`observations.json`): byte fields are lowercase hex of the raw bytes. -/
private def payObservationRecord (path : String) (json : Lean.Json) :
    Result PayObservation.Observation := do
  let obj ← exactObject path ["index", "address", "signature", "slot", "blockTime", "amount",
    "mint", "tokenProgram", "memo", "memoError"] json
  pure
    { index := ← natOrNumber s!"{path}.index" (← field path "index" obj)
      address := ← decodeHex s!"{path}.address" (← field path "address" obj)
      signature := ← decodeHex s!"{path}.signature" (← field path "signature" obj)
      slot := ← natOrNumber s!"{path}.slot" (← field path "slot" obj)
      blockTime := ← natOrNumber s!"{path}.blockTime" (← field path "blockTime" obj)
      amount := ← natOrNumber s!"{path}.amount" (← field path "amount" obj)
      mint := ← decodeHex s!"{path}.mint" (← field path "mint" obj)
      tokenProgram := ← decodeHex s!"{path}.tokenProgram" (← field path "tokenProgram" obj)
      memo := ← payMemoField path (← field path "memo" obj) (← field path "memoError" obj) }

private def payClock (path : String) (json : Lean.Json) : Result PayCell.ChainTip := do
  let obj ← exactObject path ["slot", "blockTime"] json
  pure ⟨← natOrNumber s!"{path}.slot" (← field path "slot" obj),
    ← natOrNumber s!"{path}.blockTime" (← field path "blockTime" obj)⟩

/-- The observer's report: the watcher's `tip` and `observations` (`[]` is a
heartbeat) under the observer, its capability, a nonce and the two roots it
read.  The bytes claim nothing: the receiver decides every credit. -/
private def payObservationCommand (json : Lean.Json) : Result (List UInt8) := do
  let obj ← exactObject "$" ["observer", "capability", "nonce", "expectedAuthorityRoot",
    "expectedPayRoot", "tip", "observations"] json
  let command : PayObservation.Command :=
    { observer := ⟨← nat "$.observer" (← field "$" "observer" obj)⟩
      capability := ⟨← nat "$.capability" (← field "$" "capability" obj)⟩
      nonce := ← nat "$.nonce" (← field "$" "nonce" obj)
      expectedAuthorityRoot := ⟨← nat "$.expectedAuthorityRoot"
        (← field "$" "expectedAuthorityRoot" obj)⟩
      expectedPayRoot := ⟨← nat "$.expectedPayRoot" (← field "$" "expectedPayRoot" obj)⟩
      tip := ← payClock "$.tip" (← field "$" "tip" obj)
      observations := ← list "$.observations" payObservationRecord (← field "$" "observations" obj) }
  return PayObservation.commandCodec.encode command

/-- The observer's submission of ONE enrollment-index transfer (PAY §11.4,
P3b-2): the watcher's record, the tip, `C_enrol` and the two roots read. -/
private def payEnrolCommand (json : Lean.Json) : Result (List UInt8) := do
  let obj ← exactObject "$" ["observer", "capability", "nonce", "expectedAuthorityRoot",
    "expectedPayRoot", "tip", "observation"] json
  let command : PayEnrolReceiver.Command :=
    { observer := ⟨← nat "$.observer" (← field "$" "observer" obj)⟩
      capability := ⟨← nat "$.capability" (← field "$" "capability" obj)⟩
      nonce := ← nat "$.nonce" (← field "$" "nonce" obj)
      expectedAuthorityRoot := ⟨← nat "$.expectedAuthorityRoot"
        (← field "$" "expectedAuthorityRoot" obj)⟩
      expectedPayRoot := ⟨← nat "$.expectedPayRoot" (← field "$" "expectedPayRoot" obj)⟩
      tip := ← payClock "$.tip" (← field "$" "tip" obj)
      observation := ← payObservationRecord "$.observation" (← field "$" "observation" obj) }
  return PayEnrolReceiver.commandCodec.encode command

/-- Author JSON into source-owned canonical bytes. -/
def author (kind : String) (json : Lean.Json)
    (deployed : Option NativeHost.Config := none)
    (providerRoutes : List (Nat × ProviderMetering.Schedule) := []) : Result (List UInt8) :=
  match kind with
  | "application-lifecycle-resident-begin" => do residentBegin (← residentStore deployed) json
  | "application-lifecycle-completion-report" => do completionReport (← residentStore deployed) json
  | "application-lifecycle-completion-signing-frame" => do
      completionSigningFrame (← residentStore deployed) json
  | "application-lifecycle-completion-signed-report" => do
      completionSignedReport (← residentStore deployed) json
  | "application-lifecycle-launch-physical-report" => launchPhysicalReport json
  | "application-lifecycle-launch-physical-signing-frame" => launchPhysicalSigningFrame json
  | "application-lifecycle-launch-physical-signed-report" => launchPhysicalSignedReport json
  | "application-lifecycle-completion-source" => do completionSource (← residentStore deployed) json
  | "application-lifecycle-retry-physical-report" => retryPhysicalReport json
  | "application-lifecycle-retry-physical-signing-frame" => retryPhysicalSigningFrame json
  | "application-lifecycle-retry-physical-signed-report" => retryPhysicalSignedReport json
  | "application-lifecycle-retry-completion-source" => do retryCompletionSource (← residentStore deployed) json
  | "application-lifecycle-retry-completion-command" => retryCompletionCommand json
  | "application-lifecycle-retry-completion-ingress" => retryCompletionIngress json
  | "application-lifecycle-retry-begin-request" => retryBeginOperatorRequest json
  | "application-lifecycle-retry-claim-request" => retryClaimOperatorRequest json
  | "application-lifecycle-retry-completion-request" => retryCompletionOperatorRequest json
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
  | "subject-key-rotation" => subjectKeyRotation json
  | "signing-key-next-digest" => signingKeyNextDigest json
  | "participant-key-enrollment-next-possession" => enrollmentNextPossession json
  | "participant-factory-provisioning" => participantFactoryProvisioning json
  | "fleet-turn" => fleetTurnCommand json
  | "pay-book" => payBook json
  | "pay-assign" => payAssign json
  | "well-command" => wellCommand json
  | "clock-tick" => clockTick json
  | "pay-observation" => payObservationCommand json
  | "pay-enrol" => payEnrolCommand json
  | "pay-refill" => payRefill json
  | "job-money" => jobMoney json
  | "objective-activity" => ObjectiveActivityJson.author predicate json
  | "seat" => SeatJson.author predicate json
  | "certify" => certify json
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
  | "observation-batch" => do
      let reads ← list "$" decodeHex json
      unless NativeObservationCodec.validBatch reads do
        failAt "$" "observation batch requires 1 through 16 reads"
      let bytes := NativeObservationCodec.batchCodec.encode reads
      unless bytes.length ≤ NativeObservationCodec.maxBatchBytes do
        failAt "$" "observation batch exceeds its bounded presentation size"
      pure bytes
  | "predicate" => NativeHostGenesis.predicateStream.encode <$> predicate "$" json
  | "grain-policy" => do
      -- With `task`, the policy a birth at that task installs: a provider
      -- purse's (the Host's pinned per-route fees) when the Host pins one.
      let raw ← object "$" json
      let worker ← grainWorker "$" raw
      let obj ← exactObject "$" (["owner"] ++
        (if (raw.get? "task").isSome then ["task"] else []) ++
        if worker.isSome then grainWorkerFields raw else []) json
      let owner ← nat "$.owner" (← field "$" "owner" obj)
      let task ← match obj.get? "task" with
        | some value => some <$> nat "$.task" value
        | none => pure none
      let policy := match task.bind (fun t => providerRoutes.lookup t) with
        | some routes => ProviderRoute.policy routes (grainPolicy owner worker)
        | none => grainPolicy owner worker
      pure (NativeHostGenesis.predicateStream.encode policy)
  | "grain-caveat" => do
      let obj ← exactObject "$" ["generation"] json
      let generation ← int "$.generation" (← field "$" "generation" obj)
      pure (NativeHostGenesis.predicateStream.encode (AgentGrain.executionCaveat generation))
  | "object-audience-roster" => Compiler.ObjectAudienceRoster.encode <$> audienceRoster "$" json
  | "object-device-catalog" =>
      (fun r => (StreamCodec.list Compiler.ObjectAudienceRoster.entryStream).encode r.entries) <$> audienceRoster "$" json
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
  | "application-managed-policy" => NativeHostGenesis.predicateStream.encode <$> applicationManagedPolicy "$" json
  | "application-birth" => draftCodec.encode <$> applicationBirth "$" json none deployed
  | "application-birth-intent" => intentCodec.encode <$> applicationBirthIntent "$" json deployed
  | "application-session-birth" => draftCodec.encode <$> applicationSessionBirth "$" json none deployed
  | "application-session-birth-intent" => intentCodec.encode <$> applicationSessionBirthIntent "$" json deployed
  | "application-grain-birth-intent" => intentCodec.encode <$> applicationGrainBirthIntent "$" json deployed
  | "application-session-grain-birth-intent" =>
      intentCodec.encode <$> applicationSessionGrainBirthIntent "$" json deployed
  | "application-permission-schema" => do
      pure (← ApplicationPermissionSchemaAuthoring.author json).1
  | "grain-birth" => draftCodec.encode <$> grainBirth "$" json deployed providerRoutes
  | "grain-birth-intent" => intentCodec.encode <$> grainBirthIntent "$" json deployed
      providerRoutes
  | "content" => ContentResource.commandCodec.encode <$> contentCommand "$" json
  | "resource" | "joint" => DeclaredResourceController.commandCodec.encode <$> command "$" json
  | "joint-draft" => do
      let source ← command "$" json
      pure (draftCodec.encode (.invoke (DeclaredResourceController.commandCodec.encode source)))
  | "grain" => do
      let source ← grainSource "$" json
      pure (DeclaredResourceController.commandCodec.encode source.1)
  | "grain-intent" => intentCodec.encode <$> grainIntent "$" json
  | "grain-policy-install-intent" =>
      intentCodec.encode <$> grainPolicyInstallIntent "$" json providerRoutes
  | "draft" => draftCodec.encode <$> draft "$" json
  | "intent" => intentCodec.encode <$> intent "$" json
  | "genesis" => NativeHostGenesis.configCodec.encode <$> genesis "$" json
  | _ => failAt "kind"
      "expected predicate, grain-policy, grain-caveat, grain-policy-install-intent, policy, policy-install[-draft], application-managed-policy, delegation[-draft], revocation[-draft], birth, grain-birth[-intent], application-birth[-intent], application-session-birth[-intent], application-grain-birth-intent, application-session-grain-birth-intent, application-permission-schema, application-spk-launch-descriptor, content, resource, joint[-draft], grain[-intent], draft, intent, or genesis"

private def authorRefused (kind : String) (value : Lean.Json) : Bool :=
  match author kind value with
  | .error _ => true
  | .ok _ => false

/-- A deliberately extended source: every new facet is nonneutral, so an
accidental six-field reconstruction cannot pass the authoring round trip. -/
private def grainRepinFixture : PolicyRecord where
  policyId := ⟨41⟩
  version := 5
  domain := ⟨31⟩
  semantics := ⟨37⟩
  previous := some ⟨23⟩
  predicate := grainPolicy 7 (some ([8], 1))
  localSelector := {
    physicalKinds := some [1, 2]
    requestKinds := some [0]
    verbs := some [2] }
  parents := [⟨⟨43⟩, .local, .pinned 3 ⟨47⟩⟩]
  descendants := some {
    selector := { verbs := some [1, 2] }
    predicate := .eq "request/subject" 7
    parents := [⟨⟨53⟩, .descendants, .head⟩] }
  audience := some {
    object := 41
    epoch := 2
    parent := 3
    transition := 5
    audience := 7
    devices := 11
    history := 13
    manifest := 17
    mode := .active
    authoritySnapshot := 19
    deviceSnapshot := 23 }
  objectDescriptor := some ⟨59⟩

private def grainRepinFixtureFields : List (String × Lean.Json) :=
  [("subject", .str "7"), ("intentNonce", .str "61"),
   ("declarationNonce", .str "67"), ("task", .str "41"), ("owner", .str "7"),
   ("control", .str "71"), ("domain", .str "31"), ("semantics", .str "37"),
   ("expectedPreRoot", .str "73"), ("expectedVersion", .str "5"),
   ("expectedAddress", decimal (PolicyRecordCodec.digest grainRepinFixture).value),
   ("currentSourceHex", hexJson (PolicyRecordCodec.encode grainRepinFixture)),
   ("grants", .arr #[]), ("workerSubject", .str "8"), ("workerGeneration", .str "2")]

private def grainRepinFixtureJson (replacements : List (String × Lean.Json) := []) : Lean.Json :=
  .mkObj (grainRepinFixtureFields.map fun (key, value) =>
    (key, (replacements.lookup key).getD value))

/-- Decode the output of the public authoring dispatch, including its actual
intent and policy-install codecs, to inspect the resulting source. -/
private def grainRepinAuthoredSource (json : Lean.Json) : Option PolicyRecord := do
  let bytes ← match author "grain-policy-install-intent" json with
    | .ok bytes => some bytes | .error _ => none
  let intent ← intentCodec.decode bytes
  let .prepare (.install _ _ declarationBytes) := intent.purpose | none
  let declaration ← PolicyInstallController.declarationCodec.decode declarationBytes
  some declaration.source

/-- The worker generation changes while the complete v6 extension metadata
survives the actual JSON author → intent → install-source round trip. -/
theorem grainPolicy_repin_preserves_extensions :
    grainRepinAuthoredSource (grainRepinFixtureJson []) =
      some { grainRepinFixture with
        version := 6
        previous := some (PolicyRecordCodec.digest grainRepinFixture)
        predicate := grainPolicy 7 (some ([8], 2)) } := by native_decide

/-- Wrong/stale source pins, malformed/trailing source bytes, absent canonical
source, and unknown JSON fields refuse before an intent can be authored. -/
theorem grainPolicy_repin_wrong_pins_refused :
    (([("expectedAddress", decimal ((PolicyRecordCodec.digest grainRepinFixture).value + 1)),
       ("expectedVersion", .str "4"), ("task", .str "42"),
       ("domain", .str "32"), ("semantics", .str "38"),
       ("currentSourceHex", .str "00"),
       ("currentSourceHex", hexJson (PolicyRecordCodec.encode grainRepinFixture ++ [0]))] :
        List (String × Lean.Json)).all fun replacement =>
      authorRefused "grain-policy-install-intent" (grainRepinFixtureJson [replacement])) = true ∧
    authorRefused "grain-policy-install-intent"
      (.mkObj (grainRepinFixtureFields.filter fun field => field.1 != "currentSourceHex")) = true ∧
    authorRefused "grain-policy-install-intent"
      (.mkObj (grainRepinFixtureFields ++ [("unexpected", .null)])) = true := by native_decide

/-- info: 'Minidregg.Host.Json.grainPolicy_repin_preserves_extensions' depends on axioms: [propext, Classical.choice, Quot.sound, grainPolicy_repin_preserves_extensions._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in #print axioms grainPolicy_repin_preserves_extensions
/-- info: 'Minidregg.Host.Json.grainPolicy_repin_wrong_pins_refused' depends on axioms: [propext, Classical.choice, Quot.sound, grainPolicy_repin_wrong_pins_refused._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in #print axioms grainPolicy_repin_wrong_pins_refused

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

/-- info: 'Minidregg.Host.Json.grainPolicy_duplicate_workers_refused' depends on axioms: [propext, Classical.choice, Quot.sound, grainPolicy_duplicate_workers_refused._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in #print axioms grainPolicy_duplicate_workers_refused
/-- info: 'Minidregg.Host.Json.grainPolicy_overbound_workers_refused' depends on axioms: [propext, Classical.choice, Quot.sound, grainPolicy_overbound_workers_refused._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in #print axioms grainPolicy_overbound_workers_refused
/-- info: 'Minidregg.Host.Json.grainPolicy_mixed_worker_forms_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms grainPolicy_mixed_worker_forms_refused

/-- Source-derived, non-authoritative presentation data. This lets clients
display the resulting grain generation/state without duplicating the state
machine; admission remains the receiver's decision. -/
def derive (kind : String) (json : Lean.Json) : Result Lean.Json :=
  match kind with
  | "grain" => do
      let (command, state, route) ← grainSource "$" json
      pure <| .mkObj ([("generation", signedDecimal state.generation),
        ("status", signedDecimal state.status), ("remaining", signedDecimal state.remaining),
        ("reserved", signedDecimal state.reserved)] ++
        (match route with | some code => [("route", signedDecimal code)] | none => []) ++
        [("command", hexJson (DeclaredResourceController.commandCodec.encode command))])
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
  | .installWithRoster subject control bytes roster => .mkObj
      [("type", "install-with-roster"), ("subject", decimal subject.value),
       ("control", decimal control.value), ("declaration", hexJson bytes),
       ("rosterBytes", hexJson roster)]
  | .delegate bytes => .mkObj [("type", "delegate"), ("command", hexJson bytes)]
  | .revoke bytes => .mkObj [("type", "revoke"), ("command", hexJson bytes)]
  | .renounce bytes => .mkObj [("type", "renounce"), ("command", hexJson bytes)]

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
   ("activeUntil", decimal key.activeUntil),
   ("nextKeyDigest", match key.nextKeyDigest with
      | none => .null
      | some digest => decimal digest.value)]

private def payTariffJson (tariff : PayTariff.Tariff) : Lean.Json := .mkObj
  [("version", decimal tariff.version), ("asset", decimal tariff.asset),
   ("mint", hexJson tariff.mint), ("tokenProgram", hexJson tariff.tokenProgram),
   ("decimals", decimal tariff.decimals), ("creditPerAtomic", decimal tariff.creditPerAtomic),
   ("maxPerObservation", decimal tariff.maxPerObservation),
   ("minTickSlots", decimal tariff.minTickSlots),
   ("nodeWeekRate", decimal tariff.nodeWeekRate),
   ("enrolIndex", match tariff.enrolIndex with
     | none => .null
     | some index => decimal index),
   ("journalFloor", decimal tariff.journalFloor),
   ("slashCallerPermille", decimal tariff.slashCallerPermille),
   ("valid", .bool (decide tariff.valid))]

private def payBookCommandJson (command : PayBookReceiver.Command) : Lean.Json := .mkObj
  [("type", "pay-book-v1"),
   ("canonical", hexJson (PayBookReceiver.commandCodec.encode command)),
   ("sponsor", decimal command.sponsor.value), ("control", decimal command.control.value),
   ("nonce", decimal command.nonce),
   ("expectedFactoryRoot", decimal command.expectedFactoryRoot.value),
   ("expectedAuthorityRoot", decimal command.expectedAuthorityRoot.value),
   ("expectedPayRoot", decimal command.expectedPayRoot.value),
   ("bookStart", decimal command.bookStart),
   ("book", .arr (command.book.map hexJson).toArray),
   ("tariff", match command.tariff with
     | none => .null
     | some tariff => payTariffJson tariff)]

private def payAssignCommandJson (command : PayAssignmentReceiver.Command) : Lean.Json := .mkObj
  [("type", "pay-assign-v1"),
   ("canonical", hexJson (PayAssignmentReceiver.commandCodec.encode command)),
   ("subject", decimal command.subject.value), ("capability", decimal command.capability.value),
   ("account", decimal command.account), ("index", decimal command.index),
   ("nonce", decimal command.nonce),
   ("expectedAuthorityRoot", decimal command.expectedAuthorityRoot.value),
   ("expectedPayRoot", decimal command.expectedPayRoot.value)]

private def payClockJson (clock : PayCell.ChainTip) : Lean.Json :=
  .mkObj [("slot", decimal clock.slot), ("blockTime", decimal clock.blockTime)]

private def payObservationRecordJson (o : PayObservation.Observation) : Lean.Json := .mkObj
  [("index", decimal o.index), ("address", hexJson o.address),
   ("signature", hexJson o.signature), ("slot", decimal o.slot),
   ("blockTime", decimal o.blockTime), ("amount", decimal o.amount),
   ("mint", hexJson o.mint), ("tokenProgram", hexJson o.tokenProgram),
   ("memo", match o.memo with
     | .present bytes => hexJson bytes
     | _ => .null),
   ("memoError", match o.memo with
     | .unbound => "memoUnbound"
     | .invalid => "memoInvalid"
     | _ => .null),
   ("nullifierBytes", hexJson (PayObservation.nullifierBytes o))]

private def payObservationCommandJson (command : PayObservation.Command) : Lean.Json := .mkObj
  [("type", "pay-observation-v2"),
   ("canonical", hexJson (PayObservation.commandCodec.encode command)),
   ("observer", decimal command.observer.value),
   ("capability", decimal command.capability.value),
   ("nonce", decimal command.nonce),
   ("expectedAuthorityRoot", decimal command.expectedAuthorityRoot.value),
   ("expectedPayRoot", decimal command.expectedPayRoot.value),
   ("tip", payClockJson command.tip),
   ("heartbeat", .bool command.observations.isEmpty),
   ("observations", .arr (command.observations.map payObservationRecordJson).toArray)]

private def payEnrolCommandJson (command : PayEnrolReceiver.Command) : Lean.Json := .mkObj
  [("type", "pay-enrol-v1"),
   ("canonical", hexJson (PayEnrolReceiver.commandCodec.encode command)),
   ("observer", decimal command.observer.value),
   ("capability", decimal command.capability.value),
   ("nonce", decimal command.nonce),
   ("expectedAuthorityRoot", decimal command.expectedAuthorityRoot.value),
   ("expectedPayRoot", decimal command.expectedPayRoot.value),
   ("tip", payClockJson command.tip),
   ("observation", payObservationRecordJson command.observation)]

private def payRefillCommandJson (command : PurseRefillReceiver.Command) : Lean.Json := .mkObj
  [("type", "pay-refill-v1"),
   ("canonical", hexJson (PurseRefillReceiver.commandCodec.encode command)),
   ("subject", decimal command.subject.value), ("capability", decimal command.capability.value),
   ("account", decimal command.account), ("task", decimal command.task),
   ("amount", decimal command.amount), ("gain", decimal command.gain),
   ("nonce", decimal command.nonce),
   ("expectedAuthorityRoot", decimal command.expectedAuthorityRoot.value)]

private def jobMoneyCommandJson (command : JobMoneyReceiver.Command) : Lean.Json := .mkObj
  [("type", "job-money-v2"),
   ("canonical", hexJson (JobMoneyReceiver.commandCodec.encode command)),
   ("subject", decimal command.subject.value), ("capability", decimal command.capability.value),
   ("jobCapability", decimal command.jobCapability.value),
   ("job", decimal command.job), ("action", decimal command.action),
   ("account", decimal command.account), ("amount", decimal command.amount),
   ("nonce", decimal command.nonce),
   ("expectedAuthorityRoot", decimal command.expectedAuthorityRoot.value)]

private def payCommandJson (bytes : List UInt8) : Lean.Json :=
  match PayBookReceiver.commandCodec.decode bytes with
  | some command => payBookCommandJson command
  | none =>
      match PayAssignmentReceiver.commandCodec.decode bytes with
      | some command => payAssignCommandJson command
      | none =>
          match PayObservation.commandCodec.decode bytes with
          | some command => payObservationCommandJson command
          | none =>
              match PayEnrolReceiver.commandCodec.decode bytes with
              | some command => payEnrolCommandJson command
              | none =>
                  match PurseRefillReceiver.commandCodec.decode bytes with
                  | some command => payRefillCommandJson command
                  | none =>
                      match JobMoneyReceiver.commandCodec.decode bytes with
                      | some command => jobMoneyCommandJson command
                      | none => .mkObj [("canonical", hexJson bytes), ("decoded", false)]

private def payMemoRefusalName : PayEnrolMemo.Refusal → String
  | .shape => "memoShape" | .version => "memoVersion" | .badMiniKey => "memoBadMiniKey"
  | .badSshKey => "memoBadSshKey" | .badMiniSig => "memoBadMiniSig" | .badSshSig => "memoBadSshSig"

/-- The kernel's reading of raw memo bytes (PAY §11.3): the four fields and
what each signature is over, or the named refusal. -/
def payEnrolMemoJson (bytes : List UInt8) : Lean.Json :=
  match PayEnrolMemo.parse bytes with
  | .error refusal => .mkObj [("type", "pay-enrol-memo-v1"), ("accepted", .bool false),
      ("refusal", payMemoRefusalName refusal)]
  | .ok memo => .mkObj [("type", "pay-enrol-memo-v1"), ("accepted", .bool true),
      ("miniKey", hexJson memo.miniKey), ("sshBlob", hexJson memo.sshBlob),
      ("miniSig", hexJson memo.miniSig), ("sshSig", hexJson memo.sshSig),
      ("subject", decimal (PayEnrolMemo.subjectOf memo.miniKey)),
      ("sshsigNamespace", hexJson PayEnrolMemo.sshsigNamespace)]

/-- A self-enrollment decision probe (`minidregg-host CONFIG pay-enrol-probe`):
a pay cell described in JSON, the price's birth fee, the authority's answer
for the derived subject, a tip and one watcher observation. -/
structure PayEnrolProbe where
  store : PayCell.PayStore
  price : PayEnrolDecision.Price
  tip : PayCell.ChainTip
  observation : PayObservation.Observation
  subjectTaken : Bool

private def payEnrolRecordEntry (path : String) (json : Lean.Json) :
    Result (List UInt8 × PayCell.EnrolRecord) := do
  let obj ← exactObject path ["miniKey", "sshBlob", "account", "index", "leaseUntil",
    "enrolledSlot"] json
  pure (← decodeHex s!"{path}.miniKey" (← field path "miniKey" obj),
    ⟨← decodeHex s!"{path}.sshBlob" (← field path "sshBlob" obj),
      ← nat s!"{path}.account" (← field path "account" obj),
      ← optional s!"{path}.index" nat (← field path "index" obj),
      ← nat s!"{path}.leaseUntil" (← field path "leaseUntil" obj),
      ← nat s!"{path}.enrolledSlot" (← field path "enrolledSlot" obj)⟩)

private def payAssignmentEntry (path : String) (json : Lean.Json) : Result (Nat × Nat) := do
  let obj ← exactObject path ["index", "account"] json
  pure (← nat s!"{path}.index" (← field path "index" obj),
    ← nat s!"{path}.account" (← field path "account" obj))

private def paySshIndexEntry (path : String) (json : Lean.Json) :
    Result (List UInt8 × List UInt8) := do
  let obj ← exactObject path ["sshBlob", "miniKey"] json
  pure (← decodeHex s!"{path}.sshBlob" (← field path "sshBlob" obj),
    ← decodeHex s!"{path}.miniKey" (← field path "miniKey" obj))

/-- The probe's pay cell is built with the same `set`s a receiver's patch
performs; each enrolment also indexes its ssh blob (the cell law), and
`sshIndex` adds extra index rows (a squat). -/
def payEnrolProbe (json : Lean.Json) : Result PayEnrolProbe := do
  let obj ← exactObject "$" ["tariff", "book", "assignments", "enrolments", "sshIndex",
    "birthFee", "subjectTaken", "tip", "observation"] json
  let tariff ← payTariff "$.tariff" (← field "$" "tariff" obj)
  let book ← list "$.book" decodeHex (← field "$" "book" obj)
  let assignments ← list "$.assignments" payAssignmentEntry (← field "$" "assignments" obj)
  let enrolments ← list "$.enrolments" payEnrolRecordEntry (← field "$" "enrolments" obj)
  let extra ← list "$.sshIndex" paySshIndexEntry (← field "$" "sshIndex" obj)
  let base := PayCell.genesisStore.set PayCell.tariffAddress (some tariff)
  let withBook := (book.zipIdx).foldl (fun store (row, index) =>
    store.set (PayCell.bookAddress index) (some row)) base
  let withAssign := assignments.foldl (fun store (index, account) =>
    store.set (PayCell.assignmentAddress index) (some account)) withBook
  let withEnrol := enrolments.foldl (fun store (miniKey, record) =>
    (store.set (PayCell.enrolmentAddress miniKey) (some record)).set
      (PayCell.sshIndexAddress record.sshBlob) (some miniKey)) withAssign
  let store := extra.foldl (fun store (blob, miniKey) =>
    store.set (PayCell.sshIndexAddress blob) (some miniKey)) withEnrol
  pure { store
         price := ⟨← nat "$.birthFee" (← field "$" "birthFee" obj)⟩
         tip := ← payClock "$.tip" (← field "$" "tip" obj)
         observation := ← payObservationRecord "$.observation" (← field "$" "observation" obj)
         subjectTaken := ← bool "$.subjectTaken" (← field "$" "subjectTaken" obj) }

private def payJournalReasonName : PayEnrolMemo.JournalReason → String
  | .memoMissing => "memoMissing" | .memoUnbound => "memoUnbound"
  | .memoInvalid => "memoInvalid"
  | .memoMalformed refusal => s!"memoMalformed:{payMemoRefusalName refusal}"
  | .miniSigInvalid => "miniSigInvalid" | .sshSigInvalid => "sshSigInvalid"
  | .belowPrice => "belowPrice" | .sshKeyTaken => "sshKeyTaken"
  | .sshKeyMismatch => "sshKeyMismatch" | .subjectTaken => "subjectTaken"

/-- The public enrollment view (op 112): `{"view", "clock": {"hour"},
"entries": [{"subject", "miniKey", "sshBlob", "lease": {"expiresAt"} | null,
"index"}], "journal": [{"signature", "address", "index", "amount", "slot",
"reason"}]}`.  Hours, expiries and journal numbers are JSON integers; the
subject is a decimal string.  v2 adds `journal` (P3b-2). -/
def payEnrolmentViewJson (view : PayCellDomain.EnrolmentView) : Lean.Json := .mkObj
  [("view", "DREGG/PAY/ENROLMENT-VIEW/v3"),
   ("clock", .mkObj [("hour", .num (Lean.JsonNumber.fromNat view.hour))]),
   ("entries", .arr (view.entries.map fun entry => Lean.Json.mkObj
     [("subject", decimal entry.subject),
      ("miniKey", hexJson entry.miniKey),
      ("sshBlob", hexJson entry.sshBlob),
      ("lease", match entry.leaseUntil with
        | none => .null
        | some hour => .mkObj [("expiresAt", .num (Lean.JsonNumber.fromNat hour))]),
      ("index", match entry.index with
        | none => .null
        | some index => .num (Lean.JsonNumber.fromNat index))]).toArray),
   ("journal", .arr (view.journal.map fun (key, row) => Lean.Json.mkObj
     [("signature", hexJson ((key.drop 6).take 64)),
      ("address", hexJson (key.drop 70)),
      ("index", .num (Lean.JsonNumber.fromNat row.index)),
      ("amount", .num (Lean.JsonNumber.fromNat row.amount)),
      ("slot", .num (Lean.JsonNumber.fromNat row.slot)),
      ("reason", payJournalReasonName row.reason)]).toArray)]

/-- Public, read-only quote over the same loaded authority and pay cell as the
receiver. No price is reserved and no admission or mint takes place here. -/
def payEnrolQuoteLoadedJson (config : NativeHost.Config) (opened : NativeHost.Opened config)
    (json : Lean.Json) : Result Lean.Json := do
  let obj ← exactObject "$" ["miniKey", "mode", "weeks", "starterCredit"] json
  let miniKey ← decodeHex "$.miniKey" (← field "$" "miniKey" obj)
  unless miniKey.length = 32 do failAt "$.miniKey" "a Mini key is 32 bytes"
  let mode ← string "$.mode" (← field "$" "mode" obj)
  unless mode = "enrol" ∨ mode = "renew" do failAt "$.mode" "expected enrol or renew"
  let weeks ← nat "$.weeks" (← field "$" "weeks" obj)
  let view ← NativeHost.payViewLoaded config opened
  let some tariff := view.tariff | throw "pay quote: tariff unavailable"
  unless tariff.valid do throw "pay quote: tariff invalid"
  let some index := tariff.enrolIndex | throw "pay quote: self-enrollment disabled"
  let some address := view.book[index]? | throw "pay quote: enrollment address unavailable"
  let some pay := PayCellDomain.load config.deployment opened.durable.snapshot
    | throw "pay quote: pay cell unavailable"
  let enrolled := (PayCell.enrolmentAt pay.cell.logical miniKey).isSome
  if mode = "enrol" ∧ enrolled then throw "pay quote: key already enrolled; request renewal"
  if mode = "renew" ∧ !enrolled then throw "pay quote: key not enrolled"
  let height := NativeHost.logicalHeight config opened.durable
  let identities := PayEnrolReceiver.ids config.deployment.domain miniKey
  let birthFee := if mode = "renew" then 0 else
    PayEnrolReceiver.birthFee config.deployment config.profile.semantics config.profile.template
      config.tariff opened.authority.snapshot.cell height identities 0
  -- One room+founder stream, document, application and application session,
  -- plus one hundred ordinary transaction base charges for an initial work
  -- session: 105 transactions, eight births, sixteen grants. Provider tokens
  -- and compute have separate tariffs and are not promised by this allowance.
  -- Byte-priced deployments choose a budget explicitly; counts cannot quote bytes.
  let suggestion := PayStarterAllowance.recommendation config.tariff (mode == "renew")
  let starterInput ← field "$" "starterCredit" obj
  let starter ← if starterInput == .null then
      match suggestion with
      | some amount => pure amount
      | none => throw "pay quote: byte-priced deployment requires explicit starterCredit"
    else nat "$.starterCredit" starterInput
  let quoted ← match PayEnrolQuote.quote tariff birthFee weeks starter with
    | .ok quoted => pure quoted
    | .error reason => throw s!"pay quote: {repr reason}; choose an explicit duration/budget or use a separate account deposit"
  pure <| .mkObj
    [("type", "minidregg-pay-enrollment-quote-v1"), ("mode", .str mode),
     ("miniKey", hexJson miniKey), ("domain", decimal config.deployment.domain.value),
     ("semantics", decimal config.profile.semantics.value),
     ("payRoot", decimal view.payRoot.value), ("authorityRoot", decimal view.authorityRoot.value),
     ("factoryRoot", decimal view.factoryRoot.value), ("height", decimal height),
     ("tariffVersion", decimal tariff.version), ("mint", hexJson tariff.mint),
     ("tokenProgram", hexJson tariff.tokenProgram), ("decimals", decimal tariff.decimals),
     ("enrolIndex", decimal index), ("enrolAddress", hexJson address),
     ("birthFee", decimal quoted.birthFee), ("weekCredit", decimal tariff.nodeWeekRate),
     ("requestedWeeks", decimal quoted.requestedWeeks), ("grantedWeeks", decimal quoted.actualWeeks),
     ("membershipCredit", decimal quoted.leaseCredit),
     ("requestedStarterCredit", decimal quoted.minimumStarterCredit),
     ("spendableRemainder", decimal quoted.creditedRemainder),
     ("recommendedStarterCredit", match suggestion with | some n => decimal n | none => .null),
     ("atomicAmount", decimal quoted.amountAtomic), ("totalCredit", decimal quoted.credit),
     ("minimumEntryCredit", decimal quoted.minimumEntryCredit),
     ("roundingCredit", decimal (quoted.credit -
       (birthFee + weeks * tariff.nodeWeekRate + starter))),
     ("priceReserved", .bool false)]

/-- The identities a self-enrollment derives from a Mini key in this
deployment (`PayEnrolReceiver.ids`): what a friend's client needs to act as
its new subject (its account, its owner/control capabilities on it, its
factory-observation capability, its key id and epoch). -/
def payEnrolIdsJson (domain : Digest) (miniKeyHex : String) : Result Lean.Json := do
  let miniKey ← decodeHex "$.miniKey" (.str miniKeyHex)
  unless miniKey.length = 32 do failAt "$.miniKey" "a Mini key is 32 bytes"
  let ids := PayEnrolReceiver.ids domain miniKey
  pure <| .mkObj
    [("type", "pay-enrol-ids-v1"), ("miniKey", hexJson miniKey),
     ("subject", decimal ids.subject), ("account", decimal ids.account),
     ("ownerCapability", decimal ids.ownerCapability),
     ("controlCapability", decimal ids.controlCapability),
     ("observeCapability", decimal ids.observeCapability),
     ("keyId", decimal ids.keyId), ("keyEpoch", decimal PayEnrolReceiver.keyEpoch)]

private def optionalNatJson : Option Nat → Lean.Json
  | none => .null
  | some value => decimal value

def payEnrolDecisionJson (verified : Option PayEnrolDecision.Verified)
    (decision : Except PayEnrolDecision.Reject PayEnrolDecision.Decision) : Lean.Json :=
  let verifiedJson : Lean.Json := match verified with
    | none => .null
    | some bits => .mkObj [("mini", .bool bits.mini), ("ssh", .bool bits.ssh)]
  let body : List (String × Lean.Json) := match decision with
    | .error reason => [("verdict", "refused"), ("reason", toString (repr reason))]
    | .ok (.journal reason) => [("verdict", "journal"), ("reason", payJournalReasonName reason)]
    | .ok (.enrol plan) =>
        [("verdict", "enrol"), ("miniKey", hexJson plan.memo.miniKey),
         ("subject", decimal (PayEnrolMemo.subjectOf plan.memo.miniKey)),
         ("float", decimal plan.float), ("credit", decimal plan.credit),
         ("weeks", decimal plan.weeks), ("index", optionalNatJson plan.index),
         ("leaseUntil", decimal plan.leaseUntil)]
    | .ok (.renew plan) =>
        [("verdict", "renew"), ("miniKey", hexJson plan.memo.miniKey),
         ("account", decimal plan.account), ("credit", decimal plan.credit),
         ("weeks", decimal plan.weeks), ("leaseFrom", decimal plan.leaseFrom),
         ("leaseUntil", decimal plan.leaseUntil)]
  let head : List (String × Lean.Json) :=
    [("type", "pay-enrol-probe-v1"), ("verified", verifiedJson)]
  .mkObj (head ++ body)

/-- The public pay view: roots to pin, tariff, next free index and the
published deposit book (index order, lowercase hex). -/
def subjectKeyStatusJson (subject : Nat) (status : SubjectKeyRotation.Status) : Lean.Json := .mkObj
  [("type", "subject-key-status-v1"),
   ("subject", decimal subject),
   ("keyEpoch", decimal status.epoch),
   ("keyId", decimal status.keyId),
   ("prerotated", .bool status.prerotated),
   ("isCurrent", .bool status.isCurrent),
   ("isCommittedNext", .bool status.isCommittedNext),
   ("currentRevoked", .bool status.currentRevoked)]

/-- The status query: a subject and one public key the asker holds. -/
def subjectKeyStatusQuery (json : Lean.Json) : Result (Nat × List UInt8) := do
  let obj ← exactObject "$" ["subject", "publicKey"] json
  let subject ← nat "$.subject" (← field "$" "subject" obj)
  let publicKey ← decodeHex "$.publicKey" (← field "$" "publicKey" obj)
  unless publicKey.length = 32 do failAt "$.publicKey" "expected 32 bytes"
  pure (subject, publicKey)

def payViewJson (view : PayCellDomain.View) : Lean.Json := .mkObj
  [("type", "pay-view-v2"),
   ("payRoot", decimal view.payRoot.value),
   ("authorityRoot", decimal view.authorityRoot.value),
   ("factoryRoot", decimal view.factoryRoot.value),
   ("tariff", match view.tariff with
     | none => .null
     | some tariff => payTariffJson tariff),
   ("nextFree", decimal view.nextFree),
   ("bookSize", decimal view.book.length),
   ("book", .arr (view.book.map hexJson).toArray)]

/-- The operator's local ledger read (`minidregg-host CONFIG pay-ledger`). -/
def payLedgerJson (ledger : NativeHost.PayLedger) : Lean.Json := .mkObj
  [("type", "pay-ledger-v1"),
   ("payRoot", decimal ledger.payRoot.value),
   ("tariff", match ledger.tariff with
     | none => .null
     | some tariff => payTariffJson tariff),
   ("clock", match ledger.clock with
     | none => .null
     | some clock => .mkObj [("now", decimal clock.now), ("slot", decimal clock.slot)]),
   ("asset", decimal ledger.asset),
   ("well", .str (toString ledger.well)),
   ("total", .str (toString ledger.total)),
   ("payers", .arr (ledger.rows.map fun row => Lean.Json.mkObj
     [("index", decimal row.index), ("account", decimal row.account),
      ("balance", .str (toString row.balance))]).toArray)]

/-- The operator's local read of one job's money fields. -/
def payJobJson (view : NativeHost.PayJob) : Lean.Json := .mkObj
  [("type", "pay-job-v1"),
   ("job", decimal view.job),
   ("root", decimal view.root.value),
   ("state", decimal view.state.state),
   ("caller", decimal view.state.caller),
   ("callerAcct", decimal view.state.callerAcct),
   ("price", decimal view.state.price),
   ("escrow", decimal view.state.escrow),
   ("provider", decimal view.state.provider),
   ("providerAcct", decimal view.state.providerAcct),
   ("bond", decimal view.state.bond),
   ("held", decimal view.state.held),
   ("bookHeld", .str (toString view.bookHeld))]

/-- The operator's local read of one AgentGrain purse. -/
def payPurseJson (purse : NativeHost.PayPurse) : Lean.Json := .mkObj
  [("type", "pay-purse-v1"),
   ("task", decimal purse.task),
   ("root", decimal purse.root.value),
   ("generation", .str (toString purse.state.generation)),
   ("status", .str (toString purse.state.status)),
   ("remaining", .str (toString purse.state.remaining)),
   ("reserved", .str (toString purse.state.reserved))]

private def subjectKeyRotationJson
    (command : SubjectKeyRotation.Command) : Lean.Json := .mkObj
  [("type", "subject-key-rotation-v1"),
   ("canonical", hexJson (SubjectKeyRotation.commandCodec.encode command)),
   ("subject", decimal command.subject.value),
   ("nonce", decimal command.nonce),
   ("key", participantKeyRecordJson command.key)]

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

private def participantProvisioningCommandJson
    (command : ParticipantFactoryProvisioning.Command) : Lean.Json := .mkObj
  [("type", "participant-factory-provisioning-v1"),
   ("canonical", hexJson (ParticipantFactoryProvisioning.commandCodec.encode command)),
   ("sponsor", decimal command.sponsor.value),
   ("control", decimal command.control.value),
   ("nonce", decimal command.nonce),
   ("expectedFactoryRoot", decimal command.expectedFactoryRoot.value),
   ("expectedAuthorityRoot", decimal command.expectedAuthorityRoot.value),
   ("holder", decimal command.holder.value),
   ("capability", decimal command.capability.value)]

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
           ("notAfter", decimal ticket.notAfter),
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

/-- The failing clause of a law refusal, as data and as the Host's own rendering
in the shell's law grammar. -/
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
  | .fieldsFrom object => .mkObj [("type", "from"), ("resource", decimal object.value)]

private def isDeclarationKey : Minidregg.Theory.EffectDeclaration.StateKey → Bool
  | .fieldDeclared _ _ | .fieldsOpen _ | .fieldsFrom _ => true
  | _ => false

/-- A declared cell's view: `entries` are the values it holds; its declaration
(K-FIELD-CLOSURE) is the separate `declaration` member, `"open"` or the declared
field numbers, so a reader iterating values never meets the cell's shape. -/
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
  -- The declaration's tail (ROOM-SCHEMA v2): every field at or above it.
  let tail := all.findSome? fun entry => match entry.1.2 with
    | .fieldsFrom _ => some (signedDecimal (entry.2 : Int))
    | _ => none
  let base := [("root", decimal root.value),
    ("entries", .arr <| entries.toArray.map fun entry => .mkObj
      [("key", stateKeyJson entry.1.2), ("value", signedDecimal (entry.2 : Int))]),
    ("declaration", if isOpen then "open" else .arr declared.toArray)] ++
    (match tail with
     | some first => [("declaredFrom", first)]
     | none => [])
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

private def biasJson : Hyperdocument.AnchorBias → Lean.Json
  | .before => "before"
  | .after => "after"

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

/-- The inverse spelling of `stablePoint`/`stableRange` above: what a reader of a
content cell sees is exactly what an author would write. -/
private def stablePointJson (point : Hyperdocument.StablePoint) : Lean.Json := .mkObj
  [("run", identifierJson point.run), ("neighbor", optionalIdentifierJson point.neighbor),
   ("bias", match point.bias with | .before => "before" | .after => "after"),
   ("death", deathJson point.death)]

private def stableRangeJson (range : Hyperdocument.StableRange) : Lean.Json := .mkObj
  [("start", stablePointJson range.start), ("finish", stablePointJson range.finish)]

/-- The inverse spelling of `linkTarget`. A transclusion target is named by its
id only (its stored reference is not an authoring input). -/
private def linkTargetJson : Hyperdocument.LinkTarget → Lean.Json
  | .document target => .mkObj [("type", "document"), ("id", identifierJson target)]
  | .element target => .mkObj [("type", "element"), ("id", identifierJson target)]
  | .range document range => .mkObj [("type", "range"), ("document", identifierJson document),
      ("range", stableRangeJson range)]
  | .transclusion target _ => .mkObj [("type", "transclusion"), ("id", identifierJson target)]
  | .external scheme authority path => .mkObj [("type", "external"),
      ("scheme", hexJson scheme), ("authority", hexJson authority), ("path", hexJson path)]

/-- The opening a transclusion record carries: source cell, range, pinned
atoms at their revisions, and the height; never bytes. -/
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
   ("disclosurePolicy", decimal record.disclosurePolicy.value)] ++ LegacyContentView.referenceFields record.reference

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

/-- A mark as a renderer reads it: kind (a link mark with its link record's
target and whether that link is live), anchor, author, and `fresh` — is its
target still at the anchored revision in this same store.  A stale mark is
shown struck; it is never re-anchored. -/
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

/-- The marks of a content store, in canonical entry order. -/
private def marksOf (store : ContentResource.ContentStore) :
    List (Hyperdocument.MarkId × Hyperdocument.MarkRecord) :=
  (StoreCodec.entries HyperdocumentCell.contentWire store).filterMap fun entry =>
    match entry with
    | ⟨⟨.marks, identifier⟩, record⟩ =>
        let identifier : Hyperdocument.MarkId := identifier
        let record : Hyperdocument.MarkRecord := record
        some (identifier, record)
    | _ => none

/-- One entry of a content cell. Documents, elements, links, atoms, runs and
annotations are spelled out (an annotation with `fresh`: is its atom still at
the anchored revision in this same cell); every entry carries its canonical
`StoreCodec` entry bytes. -/
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
          LegacyContentView.markFields stableRangeJson record)
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

private def streamRecordJson (sequence : Nat) (record : StreamCell.StreamRecord) : Lean.Json :=
  .mkObj [("sequence", decimal sequence), ("author", decimal record.author.value),
    ("height", decimal record.height), ("transaction", decimal record.transaction.value),
    ("topic", hexJson record.entry.topic), ("payloadDigest", decimal record.entry.payloadDigest.value),
    ("to", record.entry.recipient.map (fun s => decimal s.value) |>.getD .null),
    ("ref", record.entry.ref.map (fun r => Lean.Json.mkObj
      [("cell", decimal r.1), ("sequence", decimal r.2)]) |>.getD .null)]

/-- A tail entry with its text. The reader's own check, over the bytes it holds:
`payload` is shown only when it reproduces the digest the cell committed
(`payloadState` "verified"); a payload the view did not carry is "absent", and
one that does not reproduce the digest is "mismatch" and is not shown. -/
private def streamTailEntryJson (sequence : Nat) (record : StreamCell.StreamRecord)
    (payload : Option (List UInt8)) : Lean.Json :=
  let (state, shown) : String × Lean.Json := match payload with
    | none => ("absent", .null)
    | some bytes =>
        if StreamCell.payloadDigest bytes = record.entry.payloadDigest then ("verified", hexJson bytes)
        else ("mismatch", .null)
  .mkObj [("sequence", decimal sequence), ("author", decimal record.author.value),
    ("height", decimal record.height), ("transaction", decimal record.transaction.value),
    ("topic", hexJson record.entry.topic), ("payloadDigest", decimal record.entry.payloadDigest.value),
    ("to", record.entry.recipient.map (fun s => decimal s.value) |>.getD .null),
    ("ref", record.entry.ref.map (fun r => Lean.Json.mkObj
      [("cell", decimal r.1), ("sequence", decimal r.2)]) |>.getD .null),
    ("payload", shown), ("payloadState", .str state)]

/-- A stream read shows its head; the entries are read by position with `tail`. -/
private def streamCellJson (root : Digest) (store : StreamCell.HeadStore) : Lean.Json :=
  match StreamCell.headOf store with
  | none => .mkObj [("root", decimal root.value), ("head", .null)]
  | some head => .mkObj [("root", decimal root.value), ("nextSeq", decimal head.nextSeq),
      ("count", decimal head.count),
      ("tail", head.tail.map (fun d => decimal d.value) |>.getD .null),
      ("binding", match head.binding with
        | .room => "room"
        | .topic stream => .mkObj [("topic", decimal stream.value)])]

/-- The opening of a view's root (K-NARROW-HIDE): the store frame and one item
per entry in canonical order — `{salt, entry}` where the reader may see the
entry, `{leaf}` where it may not.  The client recomputes every opened leaf and
the root from these alone. -/
private def rootOpeningJson (opening : NativeObservationController.OpeningView) : Lean.Json :=
  .mkObj [("frame", hexJson opening.1),
    ("items", .arr <| opening.2.toArray.map fun
      | .inl opened => .mkObj [("salt", hexJson opened.salt), ("entry", hexJson opened.entry)]
      | .inr leaf => .mkObj [("leaf", hexJson leaf)])]

/-- `cell.root` is the cell's own root (the view's leading digest); the
entries are the cell as the reader's scope narrows it. -/
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

private def wellCommandJson (command : RealmWellCodec.Command) : Lean.Json :=
  .mkObj [("type", "well-command-v1"), ("subject", decimal command.subject.value),
    ("capability", decimal command.capability.value), ("well", decimal command.well),
    ("op", match command.op with | .mint => "mint" | .burn => "burn"),
    ("account", decimal command.account), ("amount", decimal command.amount),
    ("nonce", decimal command.nonce)]

/-- The operator-local realm-well ledger (`well-ledger`). -/
def wellLedgerJson (ledger : NativeHost.WellLedger) : Lean.Json :=
  .mkObj
    [("type", "well-ledger-v1"),
     ("bookRoot", decimal ledger.bookRoot.value),
     ("creditAsset", decimal ledger.creditAsset),
     ("creditWell", signedDecimal ledger.creditWell),
     ("creditTotal", signedDecimal ledger.creditTotal),
     ("wells", .arr (ledger.wells.toArray.map fun row => .mkObj
       [("asset", decimal row.asset), ("realm", decimal row.realm),
        ("well", signedDecimal row.well),
        ("holders", .arr (row.holders.toArray.map fun (holder, balance) =>
          .mkObj [("account", decimal holder), ("balance", signedDecimal balance)])),
        ("holdersSum", signedDecimal row.holdersSum),
        ("total", signedDecimal row.total)]))]

private def decoded {α : Type} (path : String) (codec : IndexedProgram.LawfulCodec α)
    (bytes : List UInt8) : Result α :=
  match codec.decode bytes with
  | some value => pure value
  | none => failAt path "noncanonical or wrong-family binary input"

/-! ## Documents: one renderer for the current page, a page at a height, and history

Every page is the reader's own signed read of a content cell: a current
`view-resource` read, or an `at` read, which the Host answers only when the
reader's grant stood at that height (`NativeObservationController.atCovered`).
`view-document` renders one page in the kernel's order (`DocumentHistory.lines`,
whose keys are `ContentResource.documentOrder`) with its transclusions rendered
against the source reads the reader supplied; `view-diff` and `view-history`
diff two such pages with `DocumentHistory.diff` over the same line lists, so
`doc diff`, `doc history` and `doc show [--at H]` cannot disagree on order. -/

/-- One signed page: an `at` read's height, the lifecycle state, the cell root,
and the content store (empty when the cell is fresh or retired at that height). -/
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

/-- Presentation selectors come from the same kernel range resolution as the
bytes. Readers can open exactly these source atoms using their own custody;
no payload equality or destination authority identifies a source fragment. -/
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

/-- A content cell holds one document (`ContentLaw`); a view does not carry the
cell's identifier, so the document is the one record of `documents`. -/
private def documentOf? (store : ContentResource.ContentStore) : Option Hyperdocument.DocumentId :=
  ((StoreCodec.entries HyperdocumentCell.contentWire store).findSome? fun entry =>
    match entry with
    | ⟨⟨.documents, identifier⟩, _⟩ => some identifier
    | _ => none).orElse fun _ => LegacyContentView.documentOf? store

/-- The page's lines: `DocumentHistory.lines`, the kernel's document order. -/
private def pageLines (store : ContentResource.ContentStore) :
    List (Hyperdocument.ElementId × DocumentHistory.Line) :=
  match documentOf? store with
  | some document => LegacyContentView.lines store document (marksOf store)
  | none => []

/-- What stands at one place: a line's atom (bytes, revision, author, struck or
not), a transclusion's embed, or a section (the revision of its children's
positions), each with the live marks laid on it (`markJson`: kind, anchor,
author, `fresh` as `ContentResource.markFresh` decides it in this store). -/
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

/-- One element of the document order: its place (parent), its line, and what
placing it needs (a section's child count; an embed's element revision, which
a mark on a transclusion line names). -/
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
  let root := (documentOf? store).bind (LegacyContentView.rootOf? store)
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

/-- `view-document`: one page of the host document (`host`: a signed
`view-resource` binary, or a signed `view-at` binary of the host at a past
height) in the kernel's order, and every transclusion record of that page
rendered by `ContentResource.renderTransclusion` against the source pages the
reader itself obtained (`sources: [{"target": DEC, "view": HEX} | {"target":
DEC, "at": HEX}]`). A transclusion whose source has no supplied live page
renders `unavailable`, with its shape only. -/
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
              match LegacyContentCarry.inspectReference record.reference with
              | none => .mkObj [("id", decimal identifier.digest.value),
                  ("render", .mkObj [("view", "unresolved")])]
              | some legacy =>
                  let source := (sources.find? (fun pair => pair.1 = legacy.document.digest.value)).map Prod.snd
                  .mkObj [("id", decimal identifier.digest.value), ("mode", modeJson legacy.mode),
                    ("legacyReference", LegacyContentView.referenceJson legacy),
                    ("render", LegacyContentView.renderReference source legacy)]
          | some opening =>
              let source := (sources.find? (fun pair => pair.1 = opening.source)).map Prod.snd
              .mkObj [("id", decimal identifier.digest.value), ("mode", modeJson record.reference.mode),
                ("opening", openingJson opening),
                ("render", transclusionProjectionJson source opening record.reference.mode)]
    | _ => none
  pure <| .mkObj ([("type", Lean.Json.str "document")] ++ pageJson page ++
    [("transclusions", .arr rendered.toArray)])

/-- Compatibility spelling for quoted ranges. The atom-embed renderer was
superseded by range transclusion: reuse the current document renderer and its
reader-supplied narrowed source pages instead of maintaining another fetch path. -/
private def quotesJson (bytes : List UInt8) : Result Lean.Json := do
  let document ← documentJson bytes
  let quotes ← match document.getObjVal? "transclusions" with
    | .ok value => pure value
    | .error _ => failAt "view-quotes" "document rendering lacks transclusions"
  pure <| .mkObj [("type", "quotes"), ("quotes", quotes)]

private def changeJson (left right : ContentResource.ContentStore) :
    DocumentHistory.Change Hyperdocument.ElementId DocumentHistory.Line → Lean.Json
  | .added element after => .mkObj [("type", "added"), ("element", decimal element.digest.value),
      ("after", .mkObj (lineValueJson right after))]
  | .removed element before => .mkObj [("type", "removed"), ("element", decimal element.digest.value),
      ("before", .mkObj (lineValueJson left before))]
  | .changed element before after => .mkObj [("type", "changed"),
      ("element", decimal element.digest.value),
      ("before", .mkObj (lineValueJson left before)), ("after", .mkObj (lineValueJson right after))]
  | .moved element before after => .mkObj [("type", "moved"),
      ("element", decimal element.digest.value),
      ("before", (before.map fun other => decimal other.digest.value).getD .null),
      ("after", (after.map fun other => decimal other.digest.value).getD .null)]

private def pageDiff (left right : ContentResource.ContentStore) : Lean.Json :=
  .arr ((DocumentHistory.diff (pageLines left) (pageLines right)).map (changeJson left right)).toArray

/-- `view-diff`: `{"left": HEX, "right": HEX}`, each a signed page; the changes
from left to right (`DocumentHistory.diff` over the two pages' lines). -/
private def diffJson (bytes : List UInt8) : Result Lean.Json := do
  let obj ← exactObject "$" ["left", "right"] (← jsonInput "view-diff" bytes)
  let left ← pageOfView "$.left" (← decodeHex "$.left" (← field "$" "left" obj))
  let right ← pageOfView "$.right" (← decodeHex "$.right" (← field "$" "right" obj))
  pure <| .mkObj [("type", "diff"), ("from", .mkObj (pageJson left)), ("to", .mkObj (pageJson right)),
    ("changes", pageDiff left.2.2.2 right.2.2.2)]

/-- `view-history`: `{"target": DEC, "since": HEX, "at": [HEX]}` — a signed
`since` read and the signed `at` reads the reader obtained. One row per
`historyOf target` entry; `before`/`after` are the `at` reads at the row's
height minus one and at its height, when the reader's grant covered them. -/
private def historyJson (bytes : List UInt8) : Result Lean.Json := do
  let obj ← exactObject "$" ["target", "since", "at"] (← jsonInput "view-history" bytes)
  let target ← nat "$.target" (← field "$" "target" obj)
  let entries ← decoded "$.since" NativeObservationController.sinceViewCodec
    (← decodeHex "$.since" (← field "$" "since" obj))
  let pages ← list "$.at" (fun path entry => do
      let page ← pageOfView path (← decodeHex path entry)
      match page.1 with
      | some height => pure (height, page)
      | none => failAt path "not an at read") (← field "$" "at" obj)
  let pageAt := fun (height : Nat) => (pages.find? (·.1 = height)).map Prod.snd
  let rows := (NativeObservationController.historyOf target entries).map fun entry =>
    let before := if entry.height = 0 then none else pageAt (entry.height - 1)
    let after := pageAt entry.height
    .mkObj ([("height", decimal entry.height), ("subject", (entry.subject.map decimal).getD .null),
      ("transaction", decimal entry.transaction),
      ("before", (before.map fun page => Lean.Json.mkObj (pageJson page)).getD .null),
      ("after", (after.map fun page => Lean.Json.mkObj (pageJson page)).getD .null)] ++
      match before, after with
      | some left, some right => [("changes", pageDiff left.2.2.2 right.2.2.2)]
      | _, _ => [("changes", .null)])
  pure <| .mkObj [("type", "history"), ("target", decimal target), ("rows", .arr rows.toArray)]

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

private def retryPhysicalReportJson
    (report : ApplicationLifecycleRetryCompletionV4Report.Report) : Result Lean.Json := do
  let begin := report.claim.originalClaim.originalBegin
  unless report.validFor begin do
    throw "retry physical report differs from its BEGIN-v4/claim/volume"
  let custody := match report.volumeCustody with
    | none => Lean.Json.null
    | some value => .mkObj [
        ("volumeIdHex", hexJson (Sp800185Cshake256.digestBytesLE value.volume)),
        ("physicalWitnessHex", hexJson value.physicalWitness)]
  return .mkObj <| ([
    ("type", .str "application-lifecycle-retry-physical-report-v4"),
    ("frameHex", hexJson report.canonicalBytes),
    ("originalBeginHex", hexJson (ApplicationLifecycleRetryBeginV4Ingress.codec.encode begin)),
    ("committedClaimHex", hexJson
      (ApplicationLifecycleRetryClaimV4Projection.codec.encode report.claim)),
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
    ("volumeCustody", custody)] : List (String × Lean.Json)) ++
    ApplicationLifecycleRetryBeginV4Inspection.selectorFields begin.retry

private def fleetCommandJson (command : FleetTurn.Command) : Lean.Json := .mkObj
  [("type", "fleet-turn-v1"),
   ("canonical", hexJson (FleetTurn.commandCodec.encode command)),
   ("subject", decimal command.subject.value), ("payer", decimal command.payer),
   ("spend", decimal command.spend.value), ("nonce", decimal command.nonce),
   ("fee", decimal command.fee),
   ("transfer", match command.transfer with
     | none => .null
     | some t => .mkObj [("destination", decimal t.destination), ("asset", decimal t.asset),
         ("amount", decimal t.amount)]),
   ("publication", match command.publication with
     | none => .null
     | some p => .mkObj [("topic", hexJson p.topic), ("sequence", decimal p.sequence),
         ("payload", hexJson p.payload), ("payloadBytes", decimal p.payload.length)])]

/-- Inspect bounded public host products. Header/envelope bytes remain exact hex. -/
def inspect (kind : String) (bytes : List UInt8) : Result Lean.Json :=
  match kind with
  | "world-prototype-output" => do
      let noun ← match Noun.cue bytes with
        | some noun => if Noun.jam noun = bytes then pure noun else failAt kind "noncanonical output jam"
        | none => failAt kind "malformed output jam"
      let value ← match noun with
        | .cell (.cell key value) (.atom 0) =>
            if key = NockProgramCell.cord "definition" then pure value
            else failAt kind "expected sole definition output"
        | _ => failAt kind "expected sole definition output"
      let source ← match WorldPrototypeConstruction.bytesOfNoun value with
        | some source => pure source
        | none => failAt kind "expected canonical byte-list noun"
      let definition ← decoded kind (ResourceBirthCodec.strictCodec WorldKindCell.definitionStream.toLawful) source
      let instantiated ← match definition.instantiate with
        | some instantiated => pure instantiated
        | none => failAt kind "invalid descriptor/defaults"
      pure <| .mkObj [("definition", .mkObj
        [("descriptor", worldDescriptorJson instantiated.descriptor),
         ("defaults", worldEntriesJson instantiated.descriptor instantiated.store)]),
        ("definitionBytes", hexJson source)]
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
  | "application-lifecycle-retry-physical-report" => do
      let report ← decoded "application-lifecycle-retry-physical-report"
        ApplicationLifecycleRetryCompletionV4Report.codec bytes
      retryPhysicalReportJson report
  | "application-lifecycle-retry-physical-signed-report" => do
      let signed ← decoded "application-lifecycle-retry-physical-signed-report"
        ApplicationLifecycleRetryCompletionV4Report.signedCodec bytes
      unless signed.signature.length == 64 do
        throw "physical signature must be 64 bytes"
      let report ← retryPhysicalReportJson signed.report
      pure <| .mkObj [
        ("type", .str "application-lifecycle-retry-physical-signed-report-v4"),
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
  | "certify" => do
      let c ← decoded "certify" CertifyReceiver.commandCodec bytes
      pure <| .mkObj
        [("type", "certify-v1"), ("sponsor", decimal c.sponsor.value),
         ("control", decimal c.control.value), ("nonce", decimal c.nonce),
         ("expectedFactoryRoot", decimal c.expectedFactoryRoot.value),
         ("expectedAuthorityRoot", decimal c.expectedAuthorityRoot.value),
         ("expectedSystemRoot", decimal c.expectedSystemRoot.value),
         ("height", decimal c.height), ("digest", decimal c.digest.value)]
  | "objective-activity" => ObjectiveActivityJson.inspectCommand bytes
  | "objective-activity-plan" => ObjectiveActivityJson.inspectPlan bytes
  | "objective-activity-ingress" => ObjectiveActivityJson.inspectIngress bytes
  | "seat" => SeatJson.inspectCommand bytes
  | "seat-plan" => SeatJson.inspectPlan bytes
  | "seat-ingress" => SeatJson.inspectIngress bytes
  | "certify-plan" => do
      let plan ← decoded "certify-plan" CertifyReceiver.signingPlanCodec bytes
      pure <| .mkObj
        [("type", "certify-plan-v1"), ("canonical", hexJson bytes),
         ("domain", decimal plan.domain.value), ("semantics", decimal plan.semantics.value),
         ("commandBytes", hexJson plan.commandBytes),
         ("header", signedHeaderJson plan.header)]
  | "certify-view" => do
      let view ← decoded "certify-view" CertifyReceiver.viewCodec bytes
      pure <| .mkObj
        [("type", "certify-view-v1"), ("systemRoot", decimal view.systemRoot.value),
         ("authorityRoot", decimal view.authorityRoot.value),
         ("factoryRoot", decimal view.factoryRoot.value),
         ("certifiedHeight", decimal view.system.certifiedHeight),
         ("certifiedDigest", decimal view.system.certifiedDigest.value),
         ("tailBound", decimal view.system.tailBound),
         ("head", decimal view.head), ("chain", decimal view.chain.value),
         ("tail", decimal (view.head - view.system.certifiedHeight)),
         ("remaining", decimal (view.system.certifiedHeight + view.system.tailBound - view.head))]
  | "clock-tick" => do
      let c ← decoded "clock-tick" ClockTickReceiver.commandCodec bytes
      pure <| .mkObj
        [("type", "clock-tick-v2"), ("sponsor", decimal c.sponsor.value),
         ("capability", decimal c.capability.value), ("nonce", decimal c.nonce),
         ("expectedAuthorityRoot", decimal c.expectedAuthorityRoot.value),
         ("expectedClockRoot", decimal c.expectedClockRoot.value),
         ("now", decimal c.now), ("slot", decimal c.slot)]
  | "clock-plan" => do
      let plan ← decoded "clock-plan" ClockTickReceiver.signingPlanCodec bytes
      pure <| .mkObj
        [("type", "clock-plan-v1"), ("canonical", hexJson bytes),
         ("domain", decimal plan.domain.value), ("semantics", decimal plan.semantics.value),
         ("commandBytes", hexJson plan.commandBytes),
         ("header", signedHeaderJson plan.header)]
  | "clock-view" => do
      let view ← decoded "clock-view" ClockTickReceiver.viewCodec bytes
      pure <| .mkObj
        [("type", "clock-view-v2"), ("clockRoot", decimal view.clockRoot.value),
         ("authorityRoot", decimal view.authorityRoot.value),
         ("now", decimal view.clock.now),
         ("day", decimal (view.clock.now / Kernel.ClockCell.secondsPerDay)),
         ("slot", decimal view.clock.slot)]
  | "participant-key-enrollment" => do
      let command ← decoded "participant-key-enrollment"
        ParticipantKeyEnrollment.commandCodec bytes
      pure (participantKeyCommandJson command)
  | "pay-book" => payBookCommandJson <$> decoded "pay-book" PayBookReceiver.commandCodec bytes
  | "pay-assign" => payAssignCommandJson <$>
      decoded "pay-assign" PayAssignmentReceiver.commandCodec bytes
  | "pay-view" => payViewJson <$> decoded "pay-view" PayCellDomain.viewCodec bytes
  | "pay-enrolment-view" => payEnrolmentViewJson <$>
      decoded "pay-enrolment-view" PayCellDomain.enrolmentViewCodec bytes
  | "pay-enrol-memo" => pure (payEnrolMemoJson bytes)
  | "pay-observation" => payObservationCommandJson <$>
      decoded "pay-observation" PayObservation.commandCodec bytes
  | "pay-enrol" => payEnrolCommandJson <$>
      decoded "pay-enrol" PayEnrolReceiver.commandCodec bytes
  | "pay-enrol-ingress" => do
      let ingress ← decoded "pay-enrol-ingress" PayEnrolReceiver.ingressCodec bytes
      let command ← decoded "pay-enrol-ingress" PayEnrolReceiver.commandCodec ingress.commandBytes
      pure <| .mkObj [("type", "pay-enrol-ingress-v1"),
        ("command", payEnrolCommandJson command), ("envelope", hexJson ingress.envelope)]
  | "pay-observation-ingress" => do
      let ingress ← decoded "pay-observation-ingress" PayObservation.ingressCodec bytes
      let command ← decoded "pay-observation-ingress" PayObservation.commandCodec
        ingress.commandBytes
      pure <| .mkObj [("type", "pay-observation-ingress-v2"),
        ("command", payObservationCommandJson command), ("envelope", hexJson ingress.envelope)]
  | "pay-refill" => payRefillCommandJson <$>
      decoded "pay-refill" PurseRefillReceiver.commandCodec bytes
  | "job-money" => jobMoneyCommandJson <$>
      decoded "job-money" JobMoneyReceiver.commandCodec bytes
  | "job-money-ingress" => do
      let ingress ← decoded "job-money-ingress" JobMoneyReceiver.ingressCodec bytes
      let command ← decoded "job-money-ingress" JobMoneyReceiver.commandCodec
        ingress.commandBytes
      pure <| .mkObj [("type", "job-money-ingress-v1"),
        ("command", jobMoneyCommandJson command), ("envelope", hexJson ingress.envelope)]
  | "pay-refill-ingress" => do
      let ingress ← decoded "pay-refill-ingress" PurseRefillReceiver.ingressCodec bytes
      let command ← decoded "pay-refill-ingress" PurseRefillReceiver.commandCodec
        ingress.commandBytes
      pure <| .mkObj [("type", "pay-refill-ingress-v1"),
        ("command", payRefillCommandJson command), ("envelope", hexJson ingress.envelope)]
  | "pay-plan" => do
      let plan ← decoded "pay-plan" PayCellDomain.signingPlanCodec bytes
      pure <| .mkObj
        [("type", "pay-plan-v1"),
         ("canonical", hexJson bytes),
         ("domain", decimal plan.domain.value),
         ("semantics", decimal plan.semantics.value),
         ("commandBytes", hexJson plan.commandBytes),
         ("command", payCommandJson plan.commandBytes),
         ("header", signedHeaderJson plan.header)]
  | "subject-key-rotation" => do
      let command ← decoded "subject-key-rotation" SubjectKeyRotation.commandCodec bytes
      pure (subjectKeyRotationJson command)
  | "subject-key-rotation-plan" => do
      let plan ← decoded "subject-key-rotation-plan" SubjectKeyRotation.signingPlanCodec bytes
      let some command := SubjectKeyRotation.commandCodec.decode plan.commandBytes
        | failAt "subject-key-rotation-plan" "noncanonical nested command"
      if plan.possessionHeader != SubjectKeyRotation.possessionFrame plan.domain plan.semantics command then
        failAt "subject-key-rotation-plan" "possession header differs from described command"
      pure <| .mkObj
        [("type", "subject-key-rotation-plan-v1"),
         ("canonical", hexJson bytes),
         ("domain", decimal plan.domain.value),
         ("semantics", decimal plan.semantics.value),
         ("commandBytes", hexJson plan.commandBytes),
         ("command", subjectKeyRotationJson command),
         ("possessionFrameValidated", .bool true),
         ("possessionHeader", hexJson plan.possessionHeader)]
  | "subject-key-rotation-ingress" => do
      let some parsed := SubjectKeyRotation.decodeIngress bytes
        | failAt "subject-key-rotation-ingress" "noncanonical ingress or nested bytes"
      pure <| .mkObj
        [("type", "subject-key-rotation-ingress-v1"),
         ("canonical", hexJson bytes),
         ("command", subjectKeyRotationJson parsed.command),
         ("possessionSignature", hexJson parsed.ingress.possessionSignature)]
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
        [("type", "participant-key-enrollment-ingress-v2"),
         ("canonical", hexJson bytes),
         ("commandBytes", hexJson parsed.ingress.commandBytes),
         ("command", participantKeyCommandJson parsed.command),
         ("sponsorEnvelope", hexJson parsed.ingress.sponsorEnvelope),
         ("possessionSignature", hexJson parsed.ingress.possessionSignature),
         ("possessionSignatureLength", decimal parsed.ingress.possessionSignature.length),
         ("nextPublicKey", hexJson parsed.ingress.nextPublicKey),
         ("nextPossessionSignature", hexJson parsed.ingress.nextPossessionSignature),
         ("signatureVerified", .bool false)]
  | "participant-factory-provisioning" => do
      let command ← decoded "participant-factory-provisioning"
        ParticipantFactoryProvisioning.commandCodec bytes
      pure (participantProvisioningCommandJson command)
  | "participant-factory-provisioning-plan" => do
      let plan ← decoded "participant-factory-provisioning-plan"
        ParticipantFactoryProvisioning.signingPlanCodec bytes
      let some command := ParticipantFactoryProvisioning.commandCodec.decode plan.commandBytes
        | failAt "participant-factory-provisioning-plan" "noncanonical nested command"
      pure <| .mkObj
        [("type", "participant-factory-provisioning-plan-v1"),
         ("canonical", hexJson bytes),
         ("domain", decimal plan.domain.value),
         ("semantics", decimal plan.semantics.value),
         ("commandBytes", hexJson plan.commandBytes),
         ("command", participantProvisioningCommandJson command),
         ("sponsorHeader", signedHeaderJson plan.sponsorHeader)]
  | "participant-factory-provisioning-ingress" => do
      let some parsed := ParticipantFactoryProvisioning.decodeIngress bytes
        | failAt "participant-factory-provisioning-ingress" "noncanonical ingress or nested bytes"
      pure <| .mkObj
        [("type", "participant-factory-provisioning-ingress-v1"),
         ("canonical", hexJson bytes),
         ("commandBytes", hexJson parsed.ingress.commandBytes),
         ("command", participantProvisioningCommandJson parsed.command),
         ("sponsorEnvelope", hexJson parsed.ingress.sponsorEnvelope),
         ("signatureVerified", .bool false)]
  | "fleet-turn" => fleetCommandJson <$> decoded "fleet-turn" FleetTurn.commandCodec bytes
  | "fleet-turn-plan" => do
      let plan ← decoded "fleet-turn-plan" FleetTurn.signingPlanCodec bytes
      let some command := FleetTurn.commandCodec.decode plan.commandBytes
        | failAt "fleet-turn-plan" "noncanonical nested command"
      pure <| .mkObj
        [("type", "fleet-turn-plan-v1"), ("canonical", hexJson bytes),
         ("domain", decimal plan.domain.value), ("semantics", decimal plan.semantics.value),
         ("commandBytes", hexJson plan.commandBytes), ("command", fleetCommandJson command),
         ("header", hexJson plan.header), ("signing", signedHeaderJson plan.header)]
  | "fleet-turn-ingress" => do
      let some parsed := FleetTurn.decodeIngress bytes
        | failAt "fleet-turn-ingress" "noncanonical ingress or nested bytes"
      pure <| .mkObj
        [("type", "fleet-turn-ingress-v1"), ("canonical", hexJson bytes),
         ("commandBytes", hexJson parsed.ingress.commandBytes),
         ("command", fleetCommandJson parsed.command),
         ("envelope", hexJson parsed.ingress.envelope), ("signatureVerified", .bool false)]
  | "well-command" => wellCommandJson <$> decoded "well-command" RealmWellCodec.commandCodec bytes
  | "well-plan" => do
      let plan ← decoded "well-plan" RealmWellCodec.signingPlanCodec bytes
      let some command := RealmWellCodec.commandCodec.decode plan.commandBytes
        | failAt "well-plan" "noncanonical nested command"
      pure <| .mkObj
        [("type", "well-plan-v1"),
         ("canonical", hexJson bytes),
         ("domain", decimal plan.domain.value),
         ("semantics", decimal plan.semantics.value),
         ("commandBytes", hexJson plan.commandBytes),
         ("command", wellCommandJson command),
         ("header", hexJson plan.header),
         ("signedHeader", signedHeaderJson plan.header)]
  | "well-ingress" => do
      let some parsed := RealmWellReceiver.decodeIngress bytes
        | failAt "well-ingress" "noncanonical ingress or nested bytes"
      pure <| .mkObj
        [("type", "well-ingress-v1"),
         ("canonical", hexJson bytes),
         ("command", wellCommandJson parsed.command),
         ("envelope", hexJson parsed.ingress.envelope)]
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
  | "view-resource-scope" => do
      let (kind, capability, fields, resource) ← decoded "view-resource-scope"
        NativeObservationController.resourceScopeViewCodec bytes
      pure <| .mkObj [("type", "resource-scope"), ("resource", ← resourceJson resource),
        ("capability", .mkObj [("kind", match kind with | .object => "object" | .account => "account" | .program => "program"),
          ("head", .mkObj [("id", decimal capability),
            ("fields", (fields.map fun values => .arr <| ((values.image CredentialAuthorityEntryCodec.fieldLabel).sort (· ≤ ·)).toArray.map
              (fun label => .str (CredentialAuthorityEntryCodec.cellFieldName
                (CredentialAuthorityEntryCodec.fieldOfLabel label)))).getD .null)])])]
  | "view-tail" => do
      let (root, next, entries) ← decoded "view-tail" NativeObservationController.tailViewCodec bytes
      pure <| .mkObj [("type", "stream-tail"), ("root", decimal root.value), ("nextSeq", decimal next),
        ("entries", .arr <| entries.toArray.map fun (k, r, p) => streamTailEntryJson k r p)]
  | "view-quotes" => quotesJson bytes
  | "context-document" => ResidentContextInspection.document bytes
  | "context-support" => ResidentContextInspection.support bytes
  | "view-document" => documentJson bytes
  | "view-diff" => diffJson bytes
  | "view-history" => historyJson bytes
  | "view-marks" => do
      let store := (← pageOfView "view-marks" bytes).2.2.2
      pure <| .mkObj [("type", "marks"), ("marks", .arr <| (marksOf store).toArray.map
        fun (identifier, record) => .mkObj (markJson store identifier record))]
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
  | "cap-tree" => InspectRender.capTreeView bytes
  | "law" => InspectRender.lawView bytes
  | "why" => InspectRender.whyView bytes
  | "turn" => InspectRender.turnView "turn" bytes
  | "receipt" => InspectRender.turnView "receipt" bytes
  | _ => failAt "kind" "expected challenge, plan, outcome, application-permission-schema, view-resource, view-document, view-diff, view-history, view-marks, view-backlinks, view-links, view-quotes, view-tail, view-policy, view-capability, view-who, view-since, view-at, cap-tree, law, why, turn, or receipt"

private def fleetReceiptJson (receipt : Receipt) : Lean.Json := .mkObj
  [("transactionId", decimal receipt.transactionId.value), ("eventId", decimal receipt.eventId.value),
   ("acceptedCount", decimal receipt.acceptedCount),
   ("worldRoot", decimal receipt.worldRoot.value)]

/-- The topic poll view. `payload` is null when the accepted ingress does not
reproduce the committed digest; the reader must then treat the event as unreadable. -/
def fleetPollJson (view : NativeHost.FleetPollView) : Lean.Json := .mkObj
  [("type", "minidregg-fleet-topic-poll-v2"), ("subject", decimal view.subject.value),
   ("payer", decimal view.payer), ("topic", hexJson view.topic),
   ("stream", decimal view.stream.value), ("cursor", decimal view.cursor),
   ("head", decimal view.head),
   ("tail", view.tail.map (fun d => decimal d.value) |>.getD .null),
   ("events", .arr <| view.events.toArray.map fun event => .mkObj
     [("sequence", decimal event.sequence), ("eventKey", decimal event.eventKey.value),
      ("parent", event.parent.map (fun d => decimal d.value) |>.getD .null),
      ("transactionId", decimal event.transactionId.value),
      ("height", decimal event.height),
      ("author", decimal event.author.value),
      ("payloadDigest", decimal event.payloadDigest.value),
      ("payload", match event.payload with | none => .null | some bytes => hexJson bytes)])]

def fleetHeadJson (view : NativeHost.FleetHeadView) : Lean.Json := .mkObj
  [("type", "minidregg-fleet-agent-head-v1"), ("subject", decimal view.subject.value),
   ("payer", decimal view.payer), ("turns", decimal view.turns),
   ("head", match view.head with
     | none => .null
     | some (_, receipt) => fleetReceiptJson receipt)]

def fleetReceiptLookupJson (transactionId : Nat) (receipt : Option Receipt) : Lean.Json :=
  match receipt with
  | none => .mkObj [("type", "absent"), ("transactionId", decimal transactionId)]
  | some r => .mkObj [("type", "confirmed"), ("receipt", fleetReceiptJson r)]

/-- The incoming ledger view (op 180): fleet turns that paid the observed
account. Payload bytes are the turn's own signed publication. -/
def fleetIncomingJson (view : NativeHost.FleetIncomingView) : Lean.Json := .mkObj
  [("type", "minidregg-fleet-incoming-v1"), ("subject", decimal view.subject.value),
   ("account", decimal view.account), ("topic", hexJson view.topic),
   ("cursor", decimal view.cursor), ("tip", decimal view.tip),
   ("entries", .arr <| view.entries.toArray.map fun entry => .mkObj
     [("height", decimal entry.height), ("transactionId", decimal entry.transactionId.value),
      ("subject", decimal entry.subject.value), ("payer", decimal entry.payer),
      ("asset", decimal entry.asset), ("amount", decimal entry.amount),
      ("topic", hexJson entry.topic), ("payload", hexJson entry.payload)])]

/-- `{"topic": HEX, "cursor": DECIMAL, "limit": DECIMAL}` -/
def fleetPollRequest (json : Lean.Json) : Result (List UInt8 × Nat × Nat) := do
  let obj ← exactObject "$" ["topic", "cursor", "limit"] json
  pure (← decodeHex "$.topic" (← field "$" "topic" obj),
    ← nat "$.cursor" (← field "$" "cursor" obj), ← nat "$.limit" (← field "$" "limit" obj))

/-! ## Nock program cells (host ops 117–119)

Op 117 takes the minimal jam bytes and this ABI JSON and answers what a birth
of that program would meet, with the canonical `DREGG/PROGRAM/v1` bytes the
birth's `"program"` field carries. The ABI JSON is Nock's: its `"arm"` becomes the
record's params (`Kernel.NockEntry.encodeParams`), not an ABI field. Op 118 shows a stored program by id. Op 119
builds the kernel's sample jam for a stored program. -/

private def nockSlotType (path : String) (json : Lean.Json) :
    Result NockProgramCodec.SlotType := do
  match ← string path json with
  | "nat" => pure .nat
  | "int" => pure .int
  | "noun" => pure .noun
  | _ => failAt path "expected nat, int or noun"

private def nockSlotTypeName : NockProgramCodec.SlotType → String
  | .nat => "nat"
  | .int => "int"
  | .noun => "noun"

private def nockSampleSlot (path : String) (json : Lean.Json) :
    Result NockProgramCodec.SampleSlot := do
  let hasMax := ((← object path json).get? "max").isSome
  let obj ← exactObject path
    (["target", "slot", "key", "type"] ++ if hasMax then ["max"] else []) json
  let max ← if hasMax then some <$> nat (path ++ ".max") (← field path "max" obj) else pure none
  pure ⟨← nat (path ++ ".target") (← field path "target" obj),
    ← string (path ++ ".slot") (← field path "slot" obj),
    ← string (path ++ ".key") (← field path "key" obj),
    ← nockSlotType (path ++ ".type") (← field path "type" obj), max⟩

private def nockOutputSlot (path : String) (json : Lean.Json) :
    Result NockProgramCodec.OutputSlot := do
  let obj ← exactObject path ["key", "target", "field", "type"] json
  pure ⟨← string (path ++ ".key") (← field path "key" obj),
    ← nat (path ++ ".target") (← field path "target" obj),
    ← nat (path ++ ".field") (← field path "field" obj),
    ← nockSlotType (path ++ ".type") (← field path "type" obj)⟩

/-- `"live"` or `"pinned"` (ABI v3, K-RUN-PIN). Required: a v3 ABI says which. -/
private def nockContext (path : String) (json : Lean.Json) :
    Result NockProgramCodec.ContextMode := do
  match ← string path json with
  | "live" => pure .live
  | "pinned" => pure .pinned
  | _ => failAt path "expected live or pinned"

private def nockContextName : NockProgramCodec.ContextMode → String
  | .live => "live"
  | .pinned => "pinned"

/-- `{"peek", "state", "event"}`: a NockApp kernel door's peek axis and the
object fields of target 0 holding its state jam atom and event number. -/
private def nockDoor (path : String) (json : Lean.Json) : Result NockProgramCodec.Door := do
  let obj ← exactObject path ["peek", "state", "event"] json
  pure ⟨← nat (path ++ ".peek") (← field path "peek" obj),
    ← nat (path ++ ".state") (← field path "state" obj),
    ← nat (path ++ ".event") (← field path "event" obj)⟩

def nockAbi (path : String) (json : Lean.Json) (extra : List String := []) :
    Result NockProgramCodec.Abi := do
  let isDoor := ((← object path json).get? "door").isSome
  let obj ← exactObject path
    (["version", "sample", "outputs", "libraries", "fuel", "context"] ++ extra ++
      if isDoor then ["door"] else [])
    json
  let door ← if isDoor then some <$> nockDoor (path ++ ".door") (← field path "door" obj)
    else pure none
  pure {
    door := door
    context := ← nockContext (path ++ ".context") (← field path "context" obj)
    version := ← nat (path ++ ".version") (← field path "version" obj)
    sample := ← list (path ++ ".sample") nockSampleSlot (← field path "sample" obj)
    outputs := ← list (path ++ ".outputs") nockOutputSlot (← field path "outputs" obj)
    libraries := ← list (path ++ ".libraries") (fun p j => Digest.mk <$> nat p j)
      (← field path "libraries" obj)
    fuel := ← nat (path ++ ".fuel") (← field path "fuel" obj) }

def nockAbiJson (abi : NockProgramCodec.Abi) : Lean.Json :=
  Lean.Json.mkObj [("version", toString abi.version),
    ("sample", .arr (abi.sample.map fun slot => .mkObj (([("target", toString slot.target),
      ("slot", slot.slot), ("key", slot.key), ("type", nockSlotTypeName slot.type)] :
        List (String × Lean.Json)) ++
        match slot.max with
        | some m => [("max", Lean.Json.str (toString m))]
        | none => [])).toArray),
    ("outputs", .arr (abi.outputs.map fun slot => .mkObj [("key", slot.key),
      ("target", toString slot.target), ("field", toString slot.field),
      ("type", nockSlotTypeName slot.type)]).toArray),
    ("libraries", .arr (abi.libraries.map fun d => Lean.Json.str (toString d.value)).toArray),
    ("fuel", toString abi.fuel), ("context", nockContextName abi.context)] |>.mergeObj (match abi.door with
      | none => Lean.Json.mkObj []
      | some d => Lean.Json.mkObj [("door", Lean.Json.mkObj [("peek", toString d.peek),
          ("state", toString d.state), ("event", toString d.event)])])

/-- The evaluator a record names: a compiled-in one by its registry name (`"nock"`; a name
the registry lacks is refused here), or any `{"name", "semantics"}`, whose id is derived
exactly as a registry entry's would be (`Evaluator.idOf`). The record carries the id, never
the name. A record naming an id the registry lacks is the KERNEL's to refuse, by name:
`unknownEvaluator`, at the check (op 131), at birth and at run (E3). -/
def evaluatorNamed (path : String) (json : Lean.Json) : Result Digest := do
  match json with
  | .str name =>
    match Evaluator.registry.find? (fun E => E.name == name) with
    | some E => pure E.id
    | none => failAt path s!"no compiled-in evaluator named {name}"
  | _ =>
    let obj ← exactObject path ["name", "semantics"] json
    pure (Evaluator.idOf (← string (path ++ ".name") (← field path "name" obj))
      (← string (path ++ ".semantics") (← field path "semantics" obj)))

/-- Op 131 request: the code bytes and the ABI source, which also names the
record's evaluator (`"evaluator": "nock"`) and Nock's arm (`"arm"`, the record's params). -/
def nockProgramOf (jam : List UInt8) (abiSource : String) : Result NockProgramCodec.Program := do
  let json ← parse abiSource
  let obj ← object "abi" json
  let evaluator ← evaluatorNamed "abi.evaluator" (← field "abi" "evaluator" obj)
  let arm ← nat "abi.arm" (← field "abi" "arm" obj)
  pure ⟨evaluator, jam, ← nockAbi "abi" json ["evaluator", "arm"],
    Kernel.NockEntry.encodeParams ⟨arm⟩⟩

/-- The record's params, shown: their bytes, and Nock's arm when they are Nock's. -/
private def paramsJson (params : List UInt8) : List (String × Lean.Json) :=
  [("params", hexJson params),
   ("arm", match Kernel.NockEntry.decodeParams params with
     | some p => Lean.Json.str (toString p.arm)
     | none => Lean.Json.null)]

/-- The verdict, and the canonical record bytes in every case: a refused record
is still the exact bytes a birth would carry, so the kernel's own refusal of it
can be exercised end to end. -/
def nockCheckJson (submitted : NockProgramCodec.Program) :
    Kernel.NockProgramCell.CheckVerdict → Lean.Json
  | .malformed => .mkObj [("type", "nock-check"), ("verdict", "malformed")]
  | .refused reason => .mkObj [("type", "nock-check"), ("verdict", "refused"),
      ("reason", reason.name), ("evaluator", toString submitted.evaluator.value),
      ("program", hexJson (NockProgramCodec.programCodec.encode submitted))]
  | .admissible program pid code cellId present => Lean.Json.mkObj [("type", "nock-check"),
      ("verdict", "admissible"), ("programId", toString pid.value),
      ("evaluator", toString program.evaluator.value),
      ("codeDigest", toString code.value), ("cellId", toString cellId),
      ("present", Lean.Json.bool present), ("jamBytes", toString program.jam.length),
      ("program", hexJson (NockProgramCodec.programCodec.encode program))] |>.mergeObj
      (Lean.Json.mkObj (paramsJson program.params))

/-- Op 118: a stored program, or its absence. -/
def nockShowJson (domain : Digest) (id : Digest) :
    Option NockProgramCodec.Program → Lean.Json
  | none => .mkObj [("type", "nock-program"), ("programId", toString id.value),
      ("present", Lean.Json.bool false)]
  | some program => Lean.Json.mkObj [("type", "nock-program"), ("programId", toString id.value),
      ("present", Lean.Json.bool true), ("evaluator", toString program.evaluator.value),
      ("cellId", toString (CanonicalCellRegistry.programCellId domain program)),
      ("codeDigest", toString (NockProgramCodec.codeDigest program.jam).value),
      ("jamBytes", toString program.jam.length), ("abi", nockAbiJson program.abi),
      ("jam", hexJson program.jam)] |>.mergeObj (Lean.Json.mkObj (paramsJson program.params))

/-- Op 119 request: `{"programId", "context": {height, caller, room}, "targets",
"values": [[index, slot, value], …]}`. -/
def nockSampleRequest (source : String) :
    Result (Digest × Kernel.NockProgramCell.Context × List Nat × List (Nat × String × Int)) := do
  let json ← parse source
  let obj ← exactObject "sample" ["programId", "context", "targets", "values"] json
  let ctxObj ← exactObject "sample.context" ["height", "caller", "room"]
    (← field "sample" "context" obj)
  let ctx : Kernel.NockProgramCell.Context := ⟨
    ← nat "sample.context.height" (← field "sample.context" "height" ctxObj),
    ← nat "sample.context.caller" (← field "sample.context" "caller" ctxObj),
    ← nat "sample.context.room" (← field "sample.context" "room" ctxObj)⟩
  let value (path : String) (json : Lean.Json) : Result (Nat × String × Int) := do
    let parts ← array path json
    unless parts.size = 3 do failAt path "expected [index, slot, value]"
    pure (← nat (path ++ "[0]") parts[0]!, ← string (path ++ "[1]") parts[1]!,
      ← int (path ++ "[2]") parts[2]!)
  pure (Digest.mk (← nat "sample.programId" (← field "sample" "programId" obj)), ctx,
    ← list "sample.targets" nat (← field "sample" "targets" obj),
    ← list "sample.values" value (← field "sample" "values" obj))

/-- Op 120 request: `{"programId", "caller", "room", "targets", "values"}`; the
height is the Host's own logical height. -/
def nockRunRequest (source : String) :
    Result (Digest × Nat × Nat × List Nat × List (Nat × String × Int)) := do
  let json ← parse source
  let obj ← exactObject "run" ["programId", "caller", "room", "targets", "values"] json
  let value (path : String) (json : Lean.Json) : Result (Nat × String × Int) := do
    let parts ← array path json
    unless parts.size = 3 do failAt path "expected [index, slot, value]"
    pure (← nat (path ++ "[0]") parts[0]!, ← string (path ++ "[1]") parts[1]!,
      ← int (path ++ "[2]") parts[2]!)
  pure (Digest.mk (← nat "run.programId" (← field "run" "programId" obj)),
    ← nat "run.caller" (← field "run" "caller" obj),
    ← nat "run.room" (← field "run" "room" obj),
    ← list "run.targets" nat (← field "run" "targets" obj),
    ← list "run.values" value (← field "run" "values" obj))

private def fieldWritesJson (writes : List Theory.Eval.FieldWrite) : Lean.Json :=
  .arr (writes.map fun w => Lean.Json.arr #[toString w.target, toString w.field,
    toString w.value]).toArray

/-- Op 120 reply: the kernel's sample, the oracle's verdict and Lean steps at the
ABI fuel, the product and its decoded writes; `claim` is what a runner signs. -/
def nockRunJson (programId : Digest) (height : Nat) :
    Kernel.Run.DryRun → Lean.Json
  | .missingProgram => .mkObj [("type", "nock-run"), ("verdict", "refused"),
      ("reason", "programUnknown")]
  | .ambiguousValues => .mkObj [("type", "nock-run"), ("verdict", "refused"),
      ("reason", "ambiguousValues")]
  | .refused reason => .mkObj [("type", "nock-run"), ("verdict", "refused"),
      ("reason", reason.name)]
  | .ran sample result writes =>
      let base : List (String × Lean.Json) := [("type", "nock-run"), ("height", toString height),
        ("sample", hexJson sample)]
      match result with
      | .ok output steps =>
        .mkObj (base ++ ([("verdict", "ok"), ("steps", toString steps), ("output", hexJson output),
          ("writes", match writes with | some ws => fieldWritesJson ws | none => Lean.Json.null),
          ("claim", .mkObj [("programId", toString programId.value), ("sample", hexJson sample),
            ("output", hexJson output), ("steps", toString steps)])] : List (String × Lean.Json)))
      | .crash steps => .mkObj (base ++ ([("verdict", "crash"), ("steps", toString steps)] :
          List (String × Lean.Json)))
      | .exhausted steps => .mkObj (base ++ ([("verdict", "exhausted"), ("steps", toString steps)] :
          List (String × Lean.Json)))

/-! ## NockApp kernel doors (host ops 121–123, N11)

Each request names a stored door program and the instance's view as the caller
read it (`"state"`: the decimal jam atom of field `door.state`, or null for an
instance never poked; `"event"`: field `door.event`, `"0"` when unloaded). The
ops read no target cell: values are the caller's own signed views, as op 120. -/

/-- A canonical jam (hex) as a noun. -/
private def nounHex (path : String) (json : Lean.Json) : Result Noun := do
  let bytes ← decodeHex path json
  match Noun.cue bytes with
  | some n => if Noun.jam n = bytes then pure n else failAt path "non-canonical jam"
  | none => failAt path "not a jam"

private def doorView (path : String) (obj : Std.TreeMap.Raw String Lean.Json compare) :
    Result Kernel.Door.View := do
  pure ⟨← optional (path ++ ".state") nat (← field path "state" obj),
    ← nat (path ++ ".event") (← field path "event" obj)⟩

/-- Op 121: `{"programId", "state", "event", "wire": <jam hex>, "cause": <jam hex>}`. -/
def nockDoorPokeRequest (source : String) :
    Result (Digest × Kernel.Door.View × Noun × Noun) := do
  let json ← parse source
  let obj ← exactObject "poke" ["programId", "state", "event", "wire", "cause"] json
  pure (Digest.mk (← nat "poke.programId" (← field "poke" "programId" obj)), ← doorView "poke" obj,
    ← nounHex "poke.wire" (← field "poke" "wire" obj), ← nounHex "poke.cause" (← field "poke" "cause" obj))

/-- Op 122: `{"programId", "state", "event", "path": <jam hex>}`; op 123 without `path`. -/
def nockDoorReadRequest (source : String) (withPath : Bool) :
    Result (Digest × Kernel.Door.View × Noun) := do
  let json ← parse source
  let obj ← exactObject "door" (["programId", "state", "event"] ++ if withPath then ["path"] else [])
    json
  let path ← if withPath then do nounHex "door.path" (← field "door" "path" obj)
    else pure (.atom 0)
  pure (Digest.mk (← nat "door.programId" (← field "door" "programId" obj)), ← doorView "door" obj,
    path)

/-- `[~ ~ x]` with an atom `x`: the atom, for display. -/
private def peekAtom : Noun → Option Nat
  | .cell (.atom 0) (.cell (.atom 0) (.atom x)) => some x
  | _ => none

private def ranJson (type : String) (extra : Noun → Nat → List (String × Lean.Json)) :
    Except Kernel.Run.Refusal (Theory.Eval.Ran Noun) → Lean.Json
  | .error reason => .mkObj [("type", type), ("verdict", "refused"), ("reason", reason.name)]
  | .ok (.crash k) => .mkObj [("type", type), ("verdict", "crash"), ("steps", toString k)]
  | .ok (.exhausted k) => .mkObj [("type", type), ("verdict", "exhausted"), ("steps", toString k)]
  | .ok (.ok out k) => .mkObj (([("type", type), ("verdict", "ok"), ("steps", toString k)] :
      List (String × Lean.Json)) ++ extra out k)

/-- Op 122 reply: the peek arm's answer (a `(unit (unit *))` jam). -/
def nockDoorPeekJson : Except Kernel.Run.Refusal (Theory.Eval.Ran Noun) → Lean.Json :=
  ranJson "nock-door-peek" fun out _ =>
    [("answer", hexJson (Noun.jam out)),
     ("value", match peekAtom out with | some x => Lean.Json.str (toString x) | none => Lean.Json.null)]

/-- Op 123 reply: the instance's state now (stored, or the booted trap's). -/
def nockDoorStateJson : Except Kernel.Run.Refusal (Theory.Eval.Ran Noun) → Lean.Json :=
  ranJson "nock-door-state" fun out _ =>
    [("state", hexJson (Noun.jam out)), ("stateAtom", toString (Kernel.NockProgramCell.jamAtom out)),
     ("value", match out with | .atom x => Lean.Json.str (toString x) | _ => Lean.Json.null)]

/-- Op 121 reply: what a runner claims for one poke. `claim` appears when the
run finished; `writes` when every effect is a write (else `writesRefusal`). -/
def nockDoorPokeJson (programId : Digest) : Kernel.NockDoor.DryPoke → Lean.Json
  | .refused reason => .mkObj [("type", "nock-door-poke"), ("verdict", "refused"),
      ("reason", reason.name)]
  | .ran sample s f result decoded =>
    let base : List (String × Lean.Json) := [("type", "nock-door-poke"),
      ("sample", hexJson (Noun.jam sample)), ("subjectFormula", hexJson (Noun.jam (.cell s f)))]
    match result with
    | .crash k => .mkObj (base ++ ([("verdict", "crash"), ("steps", toString k)] :
        List (String × Lean.Json)))
    | .exhausted k => .mkObj (base ++ ([("verdict", "exhausted"), ("steps", toString k)] :
        List (String × Lean.Json)))
    | .ok product k =>
      let ran := base ++ ([("verdict", "ok"), ("steps", toString k),
        ("product", hexJson (Noun.jam product))] : List (String × Lean.Json))
      match decoded with
      | none => .mkObj (ran ++ ([("reason", "doorShape")] : List (String × Lean.Json)))
      | some (effects, state, writes) =>
        let output := Noun.jam (.cell effects state)
        .mkObj (ran ++ ([("output", hexJson output), ("stateJam", hexJson (Noun.jam state)),
          ("stateOut", toString (Kernel.NockProgramCell.jamAtom state)),
          ("value", match state with | .atom x => Lean.Json.str (toString x) | _ => Lean.Json.null),
          ("writes", match writes with | .ok ws => fieldWritesJson ws | .error _ => Lean.Json.null),
          ("writesRefusal", match writes with | .ok _ => Lean.Json.null | .error r => Lean.Json.str r.name),
          ("claim", .mkObj [("programId", toString programId.value), ("sample", hexJson (Noun.jam sample)),
            ("output", hexJson output), ("steps", toString k)])] : List (String × Lean.Json)))

def nockSampleJson : Kernel.NockProgramCell.SampleVerdict → Lean.Json
  | .missingProgram => .mkObj [("type", "nock-sample"), ("verdict", "refused"),
      ("reason", "missingProgram")]
  | .unresolved reason => .mkObj [("type", "nock-sample"), ("verdict", "refused"),
      ("reason", match reason with
        | .unknownEvaluator => "unknownEvaluator"
        | .evaluatorDisabled => "evaluatorDisabled")]
  | .ambiguousValues => .mkObj [("type", "nock-sample"), ("verdict", "refused"),
      ("reason", "ambiguousValues")]
  | .refused => .mkObj [("type", "nock-sample"), ("verdict", "refused"),
      ("reason", "sampleUnavailable")]
  | .sample jam => .mkObj [("type", "nock-sample"), ("verdict", "sample"),
      ("sample", hexJson jam)]

end Minidregg.Host.Json
