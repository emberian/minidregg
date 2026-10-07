/- The kernel activity's JSON surface: authoring a signed command's bytes
(`author objective-activity`), inspecting a command or a signing plan, and the
public activity view (session op 214). An activity artifact is the Host's
`objective-publication SPEC activity DIR` (`ObjectivePackageAuthor`, output
codec `activity`).

Nothing here decides anything: commands are judged by
`Kernel.ObjectiveActivityReceiver`, artifacts by the kernel's `publish`. -/
import Kernel.NativeHost
import Compiler.ObjectiveBendDataWire
import Host.CapacityJson

namespace Minidregg.Host.ObjectiveActivityJson
open Lean (Json toJson)
open Minidregg.Theory Minidregg.Compiler
open Minidregg.Theory.TypedAuthorization (Digest SubjectId CapabilityId)
open Minidregg.Kernel
open Minidregg.Kernel.ObjectiveActivityWire
open Minidregg.Kernel.ObjectiveActivityReceiver (Command Turn AnswerWire)
open Minidregg.Compiler.ObjectiveBendDataWire (dataJson)
open Minidregg.Compiler.ObjectiveInvocationClaim (Capacity)
open Minidregg.Host.CapacityJson (Result decimal field nat capacity capacityJson)
set_option autoImplicit false

def hexDigit (n : Nat) : Char := "0123456789abcdef".toList.getD n '0'
def hex (bytes : List UInt8) : String :=
  String.ofList (bytes.flatMap fun b => [hexDigit (b.toNat / 16), hexDigit (b.toNat % 16)])

def unhexDigit (c : Char) : Option Nat :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10) else none

def unhex (text : String) : Result (List UInt8) :=
  let rec go : List Char → Result (List UInt8)
    | [] => .ok []
    | a :: b :: rest => do
        let some high := unhexDigit a | throw s!"not lowercase hex: {text.take 16}"
        let some low := unhexDigit b | throw s!"not lowercase hex: {text.take 16}"
        pure ((high * 16 + low).toUInt8 :: (← go rest))
    | [_] => throw "odd hex length"
  go text.toList

def str (path : String) (json : Json) (name : String) : Result String := do
  let some text := (← field path json name).getStr?.toOption | throw s!"{path}.{name} must be a string"
  pure text

def data (path : String) (json : Json) (name : String) : Result (List UInt8) := do
  let value ← ObjectiveBendDataWire.decodeData 64 (← field path json name)
  pure (dataBytes value)

/-- A creation's initial declared state: `seed` (a data value), or none (the object starts without
state). -/
def seed (path : String) (json : Json) : Result (Option (List UInt8)) :=
  match json.getObjVal? "seed" with
  | .ok _ => do pure (some (← data path json "seed"))
  | .error _ => .ok none

def answer (json : Json) : Result AnswerWire :=
  match json.getObjVal? "reply" with
  | .ok value => do pure (.reply (dataBytes (← ObjectiveBendDataWire.decodeData 64 value)))
  | .error _ =>
    match json.getObjValAs? String "refused" with
    | .ok reason => .ok (.refused reason)
    | .error _ => match json.getObjValAs? String "broken" with
      | .ok reason => .ok (.broken reason)
      | .error _ => match json.getObjVal? "unknown" with
        | .ok _ => .ok .unknown
        | .error _ => .error "$.turn.answer must be reply, refused, broken or unknown"

/-- An upgrade policy: `{"frozen": {}}` or `{"governed": {"authority": PRED, "floors": [PRED..]}}`. -/
def upgrade (law : String → Json → Result Minidregg.Pred.Pred) (path : String) (json : Json) :
    Result ObjectRecord.UpgradePolicy :=
  match json.getObjVal? "frozen" with
  | .ok _ => .ok .frozen
  | .error _ => do
    let governed ← field path json "governed"
    let authority ← law (path ++ ".governed.authority") (← field path governed "authority")
    let floors ← match (← field path governed "floors").getArr? with
      | .ok items => pure items.toList
      | .error _ => throw s!"{path}.governed.floors must be an array"
    pure (.governed authority (← floors.mapM (law (path ++ ".governed.floors"))))

/-- An array of strings (absent: none). -/
def strings (path : String) (json : Json) (name : String) : Result (List String) :=
  match json.getObjVal? name with
  | .error _ => .ok []
  | .ok value => match value.getArr? with
    | .error _ => .error s!"{path}.{name} must be an array"
    | .ok items => items.toList.mapM fun item => match item.getStr? with
      | .ok text => .ok text
      | .error _ => .error s!"{path}.{name} must hold strings"

/-- An array of decimal digests (absent: none). -/
def digests (path : String) (json : Json) (name : String) : Result (List Digest) :=
  match json.getObjVal? name with
  | .error _ => .ok []
  | .ok value => match value.getArr? with
    | .error _ => .error s!"{path}.{name} must be an array"
    | .ok items => items.toList.mapM fun item => match item.getStr?.toOption.bind String.toNat? with
      | some n => .ok ⟨n⟩
      | none => .error s!"{path}.{name} must hold decimal strings"

/-- An optional string (absent: none). -/
def optString (path : String) (json : Json) (name : String) : Result (Option String) :=
  match json.getObjVal? name with
  | .error _ => .ok none
  | .ok _ => do pure (some (← str path json name))

/-- An added envelope: `extra` (a `Capacity`), or none (the zero envelope). -/
def extra (path : String) (json : Json) : Result Capacity :=
  match json.getObjVal? "extra" with
  | .ok value => capacity (path ++ ".extra") value
  | .error _ => .ok ObjectiveTariff.zeroCapacity

/-- An invocation's sends' delivery envelope: `postage` (a `Capacity`), or none
(the zero envelope, which no deployment covers: such an invocation may not send). -/
def postage (path : String) (json : Json) : Result Capacity :=
  match json.getObjVal? "postage" with
  | .ok value => capacity (path ++ ".postage") value
  | .error _ => .ok ObjectiveTariff.zeroCapacity

/-- The total continuation allowance an invocation's sends may carry (GPT-6 row F):
`allowance` (a decimal), or 0 when absent (its sends then carry none). -/
def allowance (path : String) (json : Json) : Result Nat :=
  match json.getObjVal? "allowance" with
  | .ok _ => nat path json "allowance"
  | .error _ => .ok 0

/-- An optional decimal (absent or null: none). -/
def optDecimal (path : String) (json : Json) (name : String) : Result (Option Nat) :=
  match json.getObjVal? name with
  | .error _ => .ok none
  | .ok .null => .ok none
  | .ok _ => do pure (some (← nat path json name))

/-- A path into a call's arguments: `path` (an array of field names; absent: the arguments). -/
def argsPath (path : String) (json : Json) : Result (List String) := strings path json "path"

/-- A cumulative cap: `{path, limit}`. -/
def grantCap (path : String) (json : Json) : Result (List String × Nat) := do
  pure (← argsPath path json, ← nat path json "limit")

/-- What a grant admits of the arguments: `{exact: DATA}` (its canonical digest), `{exactDigest}`,
`{recipient: {path, value: DATA}, cap?: {path, limit}}` or `{cap: {path, limit}}`. Nothing else:
no bound admits every argument. -/
def argsBound (path : String) (json : Json) : Result ObjectiveCall.ArgsBound := do
  match json.getObjVal? "exact", json.getObjVal? "exactDigest", json.getObjVal? "recipient",
      json.getObjVal? "cap" with
  | .ok value, .error _, .error _, .error _ =>
    pure (.exact (ObjectiveCall.argsDigest (← ObjectiveBendDataWire.decodeData 64 value)))
  | .error _, .ok _, .error _, .error _ => pure (.exact ⟨← nat path json "exactDigest"⟩)
  | .error _, .error _, .ok recipient, cap =>
    let cap ← match cap with
      | .ok value => do pure (some (← grantCap (path ++ ".cap") value))
      | .error _ => pure none
    pure (.recipient (← argsPath (path ++ ".recipient") recipient) (← data (path ++ ".recipient") recipient "value") cap)
  | .error _, .error _, .error _, .ok value => do
    let (at_, limit) ← grantCap (path ++ ".cap") value
    pure (.capped at_ limit)
  | _, _, _, _ => throw (path ++ " must hold exactly one of exact, exactDigest, recipient (with an optional cap), cap")

/-- An invocation's scoped grants (v2): `[{object, method, code, args, caller?, uses}]` (absent:
none). `code` is the package the target must run (its active pin). -/
def grants (path : String) (json : Json) : Result (List ObjectiveCall.Grant) :=
  match json.getObjVal? "grants" with
  | .error _ => .ok []
  | .ok value => match value.getArr? with
    | .error _ => .error s!"{path}.grants must be an array"
    | .ok items => items.toList.mapM fun item => do
      let p := path ++ ".grants"
      pure ⟨← nat p item "object", ← str p item "method", ⟨← nat p item "code"⟩,
        ← argsBound (p ++ ".args") (← field p item "args"), ← optDecimal p item "caller", ← nat p item "uses"⟩

/-- A declared Core4 type, in the checker's own type JSON
(`ObjectiveBendTyping.decodeType`, no table). -/
def tyField (path : String) (json : Json) (name : String) : Result Minidregg.Theory.ObjectiveBendTypes.Ty := do
  match ObjectiveBendTyping.decodeType #[] (← field path json name) with
  | .ok type => pure type
  | .error reason => throw s!"{path}.{name}: {reason}"

/-- A domain registration's members: `[{object, capability}..]`, at least one. -/
def members (path : String) (json : Json) : Result (List (Nat × CapabilityId)) := do
  let items ← match (← field path json "members").getArr? with
    | .ok items => pure items
    | .error _ => throw s!"{path}.members must be an array"
  items.toList.mapM fun item => do
    pure (← nat (path ++ ".members") item "object", ⟨← nat (path ++ ".members") item "capability"⟩)

/-- The turn of a command. `law` reads a predicate (the Host's `predicate` JSON
reader), for a creation's law and upgrade policy. -/
def turn (law : String → Json → Result Minidregg.Pred.Pred) (json : Json) : Result Turn := do
  let p := "$.turn"
  match ← str p json "kind" with
  | "publish" => pure (.publish (← unhex (← str p json "artifact")) (← unhex (← str p json "package"))
      (← nat p json "payer") ⟨← nat p json "payerCapability"⟩)
  | "create" => pure (.create (← nat p json "object") ⟨← nat p json "objectCapability"⟩ ⟨← nat p json "pin"⟩
      (← tyField p json "stateType") (← law (p ++ ".law") (← field p json "law"))
      (← upgrade law (p ++ ".upgrade") (← field p json "upgrade"))
      (← seed p json) (← nat p json "payer") ⟨← nat p json "payerCapability"⟩)
  | "birth" => pure (.birth (← nat p json "object") ⟨← nat p json "objectCapability"⟩
      (← nat p json "account") ⟨← nat p json "accountCapability"⟩ ⟨← nat p json "pin"⟩
      (← data p json "input") (← capacity (p ++ ".envelope") (← field p json "envelope"))
      (← capacity (p ++ ".resume") (← field p json "resume")) (← capacity (p ++ ".timeout") (← field p json "timeout"))
      (← nat p json "deposit"))
  | "resolve" => pure (.resolve ⟨← nat p json "slot"⟩ (← answer (← field p json "answer")))
  | "deliver" => pure (.deliver ⟨← nat p json "record"⟩ ⟨← nat p json "await"⟩ (← extra p json)
      (← nat p json "account") ⟨← nat p json "accountCapability"⟩)
  | "topUp" => pure (.topUp ⟨← nat p json "record"⟩ (← nat p json "account") ⟨← nat p json "accountCapability"⟩
      (← nat p json "amount"))
  | "exhaust" => pure (.exhaust ⟨← nat p json "record"⟩ ⟨← nat p json "await"⟩ (← extra p json)
      (← nat p json "account") ⟨← nat p json "accountCapability"⟩)
  | "abandon" => pure (.abandon ⟨← nat p json "record"⟩ ⟨← nat p json "await"⟩)
  | "invoke" => pure (.invoke (← nat p json "object") ⟨← nat p json "objectCapability"⟩ (← str p json "method")
      (← data p json "args") (← grants p json) (← capacity (p ++ ".envelope") (← field p json "envelope"))
      (← postage p json) (← allowance p json) (← nat p json "account") ⟨← nat p json "accountCapability"⟩)
  | "deliverMessage" => pure (.deliverMessage (← nat p json "sender") (← nat p json "target")
      ⟨← nat p json "message"⟩)
  | "adopt" => pure (.adopt (← nat p json "object") ⟨← nat p json "objectCapability"⟩ ⟨← nat p json "pin"⟩
      (← tyField p json "stateType") (← optString p json "migration") (← strings p json "dropped")
      (← law (p ++ ".law") (← field p json "law")) (← upgrade law (p ++ ".upgrade") (← field p json "upgrade"))
      (← digests p json "rebirth") (← capacity (p ++ ".envelope") (← field p json "envelope"))
      (← nat p json "patience") (← nat p json "account") ⟨← nat p json "accountCapability"⟩)
  | "migrate" => pure (.migrate (← nat p json "object") (← nat p json "account") ⟨← nat p json "accountCapability"⟩)
  | "abortDrained" => pure (.abortDrained ⟨← nat p json "record"⟩ ⟨← nat p json "await"⟩ (← extra p json)
      (← nat p json "account") ⟨← nat p json "accountCapability"⟩)
  | "rebirth" => pure (.rebirth ⟨← nat p json "record"⟩ ⟨← nat p json "await"⟩
      (← capacity (p ++ ".envelope") (← field p json "envelope")))
  | "registerDomain" => pure (.registerDomain (← members p json) (← law (p ++ ".law") (← field p json "law"))
      (← nat p json "payer") ⟨← nat p json "payerCapability"⟩ (← capacity (p ++ ".envelope") (← field p json "envelope")))
  | other => throw s!"$.turn.kind {other} is not publish, create, birth, resolve, deliver, topUp, \
      exhaust, abandon, invoke, deliverMessage, adopt, migrate, abortDrained, rebirth or registerDomain"

/-- `author objective-activity`: `{subject, nonce, expectedAuthorityRoot, turn}`, except that an
invoke's nonce is its operation id: `{subject, expectedAuthorityRoot, turn: {kind: "invoke", opId, ...}}`.
The caller mints the op id once per operation and reuses it on every retry. A retry then answers the
original's receipt (`ObjectiveActivityReceiver.replay`) or is refused `replayedMarker`; it is never
a second invocation. An invoke without `$.turn.opId`, or with a top-level `$.nonce`, is refused by
name. -/
def author (law : String → Json → Result Minidregg.Pred.Pred) (json : Json) : Result (List UInt8) := do
  let turnJson ← field "$" json "turn"
  let decided ← turn law turnJson
  let nonce ← match decided with
    | .invoke .. => do
      if (json.getObjVal? "nonce").toOption.isSome then
        throw "$.nonce: an invoke's nonce is its operation id, $.turn.opId"
      nat "$.turn" turnJson "opId"
    | _ => nat "$" json "nonce"
  let command : Command :=
    { subject := ⟨← nat "$" json "subject"⟩, nonce := nonce
      expectedAuthorityRoot := ⟨← nat "$" json "expectedAuthorityRoot"⟩
      turn := decided }
  pure (ObjectiveActivityReceiver.commandCodec.encode command)

def dataOf (bytes : List UInt8) : Json :=
  match decodeDataBytes bytes with
  | some value => dataJson value
  | none => .mkObj [("undecodable", toJson (hex bytes))]

def argsBoundJson : ObjectiveCall.ArgsBound → Json
  | .exact digest => .mkObj [("exactDigest", decimal digest.value)]
  | .recipient path value cap => .mkObj ([("recipient", .mkObj [("path", toJson path), ("value", dataOf value)])] ++
      (cap.map fun (at_, limit) => ("cap", .mkObj [("path", toJson at_), ("limit", decimal limit)])).toList)
  | .capped path limit => .mkObj [("cap", .mkObj [("path", toJson path), ("limit", decimal limit)])]

def grantJson (grant : ObjectiveCall.Grant) : Json :=
  .mkObj ([("object", decimal grant.object), ("method", toJson grant.method), ("code", decimal grant.code.value),
    ("args", argsBoundJson grant.args)] ++ (grant.caller.map fun c => ("caller", decimal c)).toList ++
    [("uses", decimal grant.uses)])

def answerJson : AnswerWire → Json
  | .reply value => .mkObj [("reply", dataOf value)]
  | .refused reason => .mkObj [("refused", toJson reason)]
  | .unknown => .mkObj [("unknown", toJson true)]
  | .broken reason => .mkObj [("broken", toJson reason)]

def upgradeJson : ObjectRecord.UpgradePolicy → Json
  | .frozen => .mkObj [("frozen", .mkObj [])]
  | .governed authority floors => .mkObj [("governed", .mkObj [("authority", toJson (reprStr authority)),
      ("floors", toJson (floors.map reprStr))])]

def turnJson : Turn → Json
  | .publish artifact package payer pc => .mkObj [("kind", "publish"), ("artifactBytes", decimal artifact.length),
      ("packageBytes", decimal package.length), ("payer", decimal payer), ("payerCapability", decimal pc.value)]
  | .create object oc pin stateType law policy seed payer pc => .mkObj
      (([("kind", "create"), ("object", decimal object), ("objectCapability", decimal oc.value),
       ("pin", decimal pin.value), ("stateType", ObjectiveBendTyping.typeJson stateType),
       ("law", toJson (reprStr law)), ("upgrade", upgradeJson policy)] :
          List (String × Json)) ++
       (match seed with | some bytes => [("seed", dataOf bytes)] | none => []) ++
       [("payer", decimal payer), ("payerCapability", decimal pc.value)])
  | .birth object oc account ac pin input envelope resume timeout deposit => .mkObj
      [("kind", "birth"), ("object", decimal object), ("objectCapability", decimal oc.value),
       ("account", decimal account), ("accountCapability", decimal ac.value), ("pin", decimal pin.value),
       ("input", dataOf input), ("envelope", capacityJson envelope), ("resume", capacityJson resume),
       ("timeout", capacityJson timeout), ("deposit", decimal deposit)]
  | .resolve slot answer => .mkObj [("kind", "resolve"), ("slot", decimal slot.value), ("answer", answerJson answer)]
  | .deliver record await extra account ac => .mkObj
      [("kind", "deliver"), ("record", decimal record.value), ("await", decimal await.value),
       ("extra", capacityJson extra), ("account", decimal account), ("accountCapability", decimal ac.value)]
  | .topUp record account ac amount => .mkObj
      [("kind", "topUp"), ("record", decimal record.value), ("account", decimal account),
       ("accountCapability", decimal ac.value), ("amount", decimal amount)]
  | .exhaust record await extra account ac => .mkObj
      [("kind", "exhaust"), ("record", decimal record.value), ("await", decimal await.value),
       ("extra", capacityJson extra), ("account", decimal account), ("accountCapability", decimal ac.value)]
  | .abandon record await => .mkObj
      [("kind", "abandon"), ("record", decimal record.value), ("await", decimal await.value)]
  | .invoke object oc method args grants envelope postage allowance account ac => .mkObj
      [("kind", "invoke"), ("object", decimal object), ("objectCapability", decimal oc.value),
       ("method", toJson method), ("args", dataOf args),
       ("grants", .arr (grants.map grantJson).toArray),
       ("envelope", capacityJson envelope), ("postage", capacityJson postage), ("allowance", decimal allowance),
       ("account", decimal account),
       ("accountCapability", decimal ac.value)]
  | .deliverMessage sender target message => .mkObj
      [("kind", "deliverMessage"), ("sender", decimal sender), ("target", decimal target),
       ("message", decimal message.value)]
  | .adopt object oc pin stateType migration dropped law policy chosen envelope patience account ac => .mkObj
      [("kind", "adopt"), ("object", decimal object), ("objectCapability", decimal oc.value),
       ("pin", decimal pin.value), ("stateType", ObjectiveBendTyping.typeJson stateType),
       ("migration", match migration with | some name => toJson name | none => .null),
       ("dropped", toJson dropped), ("law", toJson (reprStr law)), ("upgrade", upgradeJson policy),
       ("rebirth", .arr (chosen.map fun activity => decimal activity.value).toArray),
       ("envelope", capacityJson envelope), ("patience", decimal patience), ("account", decimal account),
       ("accountCapability", decimal ac.value)]
  | .migrate object account ac => .mkObj
      [("kind", "migrate"), ("object", decimal object), ("account", decimal account),
       ("accountCapability", decimal ac.value)]
  | .abortDrained record await extra account ac => .mkObj
      [("kind", "abortDrained"), ("record", decimal record.value), ("await", decimal await.value),
       ("extra", capacityJson extra), ("account", decimal account), ("accountCapability", decimal ac.value)]
  | .rebirth record await envelope => .mkObj
      [("kind", "rebirth"), ("record", decimal record.value), ("await", decimal await.value),
       ("envelope", capacityJson envelope)]
  | .registerDomain members law payer pc envelope => .mkObj
      [("kind", "registerDomain"),
       ("members", .arr (members.map fun (object, c) =>
          Json.mkObj [("object", decimal object), ("capability", decimal c.value)]).toArray),
       ("law", toJson (reprStr law)),
       ("domain", decimal (ObjectiveActivity.domainId (members.map fun (object, _) => ⟨object⟩) law).value),
       ("payer", decimal payer), ("payerCapability", decimal pc.value), ("envelope", capacityJson envelope)]

def commandJson (command : Command) : Json := .mkObj
  [("type", "objective-activity-command-v4"),
   ("canonical", toJson (hex (ObjectiveActivityReceiver.commandCodec.encode command))),
   ("subject", decimal command.subject.value),
   (if ObjectiveActivityReceiver.Command.isInvoke command then "opId" else "nonce", decimal command.nonce),
   ("expectedAuthorityRoot", decimal command.expectedAuthorityRoot.value),
   ("transaction", match ObjectiveActivityReceiver.transactionOf command with
     | some tx => decimal tx.value | none => .null),
   ("turn", turnJson command.turn)]

def inspectCommand (bytes : List UInt8) : Result Json :=
  match ObjectiveActivityReceiver.commandCodec.decode bytes with
  | some command => .ok (commandJson command)
  | none => .error "noncanonical activity command"

def inspectPlan (bytes : List UInt8) : Result Json :=
  match ObjectiveActivityReceiver.signingPlanCodec.decode bytes with
  | none => .error "noncanonical activity plan"
  | some plan => .ok (.mkObj
      [("type", "objective-activity-plan-v3"), ("canonical", toJson (hex bytes)),
       ("report", if plan.report.isEmpty then .null else dataOf plan.report),
       -- What a submission at the planning snapshot commits (GPT-6 row E): null when admitted,
       -- `charged failure: ...` (the price of the envelope, nothing else) or `refused: ...`.
       ("verdict", match String.fromUTF8? ⟨plan.verdict.toArray⟩ with
         | some "" => .null | some text => toJson text | none => .null),
       ("outcome", decimal plan.outcome.value),
       ("domain", decimal plan.domain.value), ("semantics", decimal plan.semantics.value),
       ("command", match ObjectiveActivityReceiver.commandCodec.decode plan.commandBytes with
         | some command => commandJson command | none => .null),
       ("header", .mkObj [("canonical", toJson (hex plan.header))])])

def inspectIngress (bytes : List UInt8) : Result Json :=
  match ObjectiveActivityReceiver.decodeIngress bytes with
  | none => .error "noncanonical activity ingress"
  | some ingress => .ok (.mkObj
      [("type", "objective-activity-ingress-v1"), ("command", commandJson ingress.command),
       ("envelopeBytes", decimal ingress.ingress.envelope.length)])

/-! ## The public view -/

open Minidregg.Kernel.ObjectiveActivity in
def awaitJson (domain : Digest) (await : Await) : Json :=
  .mkObj [("id", decimal await.id.value),
    ("source", match await.source with
      | .reply slot decider => .mkObj [("kind", "reply"), ("slot", decimal slot.value),
          ("slotCell", decimal (AnswerSlot.cell domain slot).value), ("decider", decimal decider.value)]
      | .height due => .mkObj [("kind", "height"), ("due", decimal due)]),
    ("deadline", decimal await.deadline), ("yieldedAt", decimal await.yieldedAt)]

open Minidregg.Kernel.ObjectiveActivity in
def recordJson (domain : Digest) (record : Record) : Json :=
  .mkObj [("object", decimal record.object.value), ("activity", decimal record.activity.value),
    ("pin", decimal record.pin.value), ("input", dataOf record.input),
    ("generation", decimal record.generation),
    ("checkpointBytes", decimal record.checkpoint.length),
    ("checkpointDigest", decimal record.checkpointDigest.value),
    ("checkpointDecodes", toJson (decodeCheckpoint record.checkpoint).isSome),
    ("escrow", .mkObj [("payer", decimal record.escrow.payer.value), ("account", decimal record.escrow.account),
      ("resume", capacityJson record.escrow.resume), ("timeout", capacityJson record.escrow.timeout),
      ("resumeFee", decimal record.escrow.resumeFee), ("timeoutFee", decimal record.escrow.timeoutFee)]),
    ("tried", decimal record.tried),
    ("phase", match record.phase with
      | .awaiting await => .mkObj [("kind", "awaiting"), ("await", awaitJson domain await)]
      | .done result => .mkObj [("kind", "done"), ("result", dataOf result)]
      | .faulted reason => .mkObj [("kind", "faulted"), ("reason", toJson reason)])]

def decisionJson : AnswerSlot.Decision → Json
  | .reply value => .mkObj [("kind", "reply"), ("value", dataOf value)]
  | .refused reason => .mkObj [("kind", "refused"), ("reason", toJson reason)]
  | .unknown => .mkObj [("kind", "unknown")]
  | .broken reason => .mkObj [("kind", "broken"), ("reason", toJson reason)]
  | .expired => .mkObj [("kind", "expired")]
  | .cancelled => .mkObj [("kind", "cancelled")]

def messageJson (message : Inbox.Message) : Json :=
  .mkObj [("id", decimal message.id.value), ("sender", decimal message.sender), ("method", toJson message.method),
    ("args", dataOf message.args), ("envelope", capacityJson message.envelope), ("postage", decimal message.postage),
    ("refund", decimal message.refund), ("allowance", decimal message.allowance), ("depth", decimal message.depth),
    ("deposit", decimal message.deposit)]

def slotJson (slot : AnswerSlot.Slot) : Json :=
  .mkObj [("name", decimal slot.name.value), ("activity", decimal slot.activity.value),
    ("decider", match slot.decider with
      | .subject subject => .mkObj [("subject", decimal subject.value)]
      | .delivery message sender => .mkObj [("delivery", decimal message.value), ("sender", decimal sender)]),
    ("deadline", decimal slot.deadline),
    ("phase", match slot.phase with
      | .opened => "open"
      | .decided decision height => .mkObj [("decision", decisionJson decision), ("height", decimal height)]),
    ("queued", Json.arr (slot.queued.map messageJson).toArray), ("watched", toJson slot.watched)]

def inboxJson (inbox : Inbox.Inbox) : Json :=
  .mkObj [("sender", decimal inbox.sender), ("target", decimal inbox.target), ("head", decimal inbox.head),
    ("tail", decimal inbox.tail), ("messages", Json.arr (inbox.messages.map messageJson).toArray)]

def cellJson (domain : Digest) (cell : Nat) (root : Digest) (bytes : List UInt8) : Json :=
  let described : List (String × Json) :=
    match ObjectiveActivity.payloadOf bytes with
    | none => [("kind", if bytes.isEmpty then "absent"
        else if bytes = ObjectiveActivity.retiredImage then "retired" else "not-an-activity-cell")]
    | some payload =>
      let at_ := decide (cell = ObjectiveActivityCell.coordinate domain payload.role payload.key)
      [("atCoordinate", toJson at_)] ++
      match payload.role with
      | .record => match ObjectiveActivity.decodeRecord payload.body with
        | some record => [("kind", "activity-record"), ("record", recordJson domain record),
            ("purseAccount", decimal cell)]
        | none => [("kind", "record-undecodable")]
      | .slot => match AnswerSlot.decode payload.body with
        | some slot => [("kind", "answer-slot"), ("slot", slotJson slot)]
        | none => [("kind", "slot-undecodable")]
      | .state => match ObjectState.decodeObjectState payload.body with
        | some state => [("kind", "declared-state"), ("version", decimal state.version),
            ("value", dataOf (ObjectiveActivityWire.dataBytes state.value))]
        | none => [("kind", "state-undecodable")]
      | .package => match (ObjectiveActivity.decodeStored payload.body).bind
            (fun stored => (ObjectiveBendSourceArtifact.decode stored.artifact).map (stored, ·)) with
        | some (stored, artifact) => [("kind", "package"), ("declaration", toJson artifact.declaration),
            ("pin", decimal (ObjectiveBendSourceArtifact.identity artifact).value),
            ("artifactBytes", decimal stored.artifact.length), ("packageBytes", decimal stored.package.length),
            ("payer", decimal stored.payer)]
        | none => [("kind", "package-undecodable")]
      | .object => match ObjectRecord.decodeRecord payload.body with
        | some record => [("kind", "object-record"), ("pin", decimal record.pin.value),
            ("schemaVersion", decimal record.schemaVersion), ("law", toJson (reprStr record.law)),
            ("effectiveLaw", toJson (reprStr record.effectiveLaw)),
            ("upgrade", upgradeJson record.upgrade), ("continuity", decimal record.continuity),
            ("payer", decimal record.payer),
            ("domains", .arr (record.domains.map fun id => decimal id.value).toArray),
            ("live", decimal record.live), ("rebirths", decimal record.rebirths),
            ("phase", match record.phase with
              | .steady => .mkObj [("steady", .mkObj [])]
              | .draining next deadline => .mkObj [("draining", .mkObj [("pin", decimal next.pin.value),
                  ("deadline", decimal deadline), ("live", decimal next.live),
                  ("migration", match next.migration with | some m => toJson m | none => .null),
                  ("rebirth", .arr (next.rebirth.map fun d => decimal d.value).toArray)])])]
        | none => [("kind", "object-undecodable")]
      | .inbox => match Inbox.decode payload.body with
        | some inbox => [("kind", "inbox"), ("inbox", inboxJson inbox), ("purseAccount", decimal cell)]
        | none => [("kind", "inbox-undecodable")]
      | .domain => match ObjectiveActivity.decodeDomain payload.body with
        | some found => [("kind", "invariant-domain"),
            ("members", .arr (found.members.map fun member => decimal member.value).toArray),
            ("law", toJson (reprStr found.law)), ("payer", decimal found.payer)]
        | none => [("kind", "domain-undecodable")]
  .mkObj ([("cell", decimal cell), ("root", decimal root.value)] ++ described)

/-- The view request: `{cells: [id..], accounts: [id..], objects: [id..], pins: [pin..],
births: [{object, transaction}..], inboxes: [{sender, target}..], slots: [name..],
quotes: [{record, await}..]}`; objects
name their state and record cells, pins their package cells, births (an object and a birth's
transaction) their record cells, inboxes their cells, and slots (a slot or message id) their
answer-slot cells; `quotes: [{record, await}..]` asks the heap a delivery or exhaustion of that await must
declare. -/
structure ViewRequest where
  cells : List Nat
  accounts : List Nat
  objects : List Nat
  pins : List Nat
  births : List (Nat × Nat)
  inboxes : List (Nat × Nat)
  slots : List Nat
  /-- `(record, await)` pairs whose delivery or exhaustion heap is asked (`quotes` in the reply). -/
  quotes : List (Nat × Nat)

def natList (json : Json) (name : String) : Result (List Nat) :=
  match json.getObjVal? name with
  | .error _ => .ok []
  | .ok value => do
    let items ← match value.getArr? with | .ok items => pure items | .error _ => throw s!"$.{name} must be an array"
    items.toList.mapM fun item => do
      let some text := item.getStr?.toOption | throw s!"$.{name} items are decimal strings"
      let some n := text.toNat? | throw s!"$.{name} items are decimal strings"
      pure n

def births (json : Json) : Result (List (Nat × Nat)) :=
  match json.getObjVal? "births" with
  | .error _ => .ok []
  | .ok value => do
    let items ← match value.getArr? with | .ok items => pure items | .error _ => throw "$.births must be an array"
    items.toList.mapM fun item => do pure (← nat "$.births" item "object", ← nat "$.births" item "transaction")

def inboxPairs (json : Json) : Result (List (Nat × Nat)) :=
  match json.getObjVal? "inboxes" with
  | .error _ => .ok []
  | .ok value => do
    let items ← match value.getArr? with | .ok items => pure items | .error _ => throw "$.inboxes must be an array"
    items.toList.mapM fun item => do pure (← nat "$.inboxes" item "sender", ← nat "$.inboxes" item "target")

def quotePairs (json : Json) : Result (List (Nat × Nat)) :=
  match json.getObjVal? "quotes" with
  | .error _ => .ok []
  | .ok value => do
    let items ← match value.getArr? with | .ok items => pure items | .error _ => throw "$.quotes must be an array"
    items.toList.mapM fun item => do pure (← nat "$.quotes" item "record", ← nat "$.quotes" item "await")

def parseViewRequest (bytes : List UInt8) : Result ViewRequest := do
  if bytes.isEmpty then return ⟨[], [], [], [], [], [], [], []⟩
  let some text := String.fromUTF8? ⟨bytes.toArray⟩ | throw "view request is not UTF-8"
  let json ← Json.parse text
  pure ⟨← natList json "cells", ← natList json "accounts", ← natList json "objects", ← natList json "pins",
    ← births json, ← inboxPairs json, ← natList json "slots", ← quotePairs json⟩

def stateCellOf (domain : Digest) (object : Nat) : Nat := (ObjectiveActivity.stateCell domain ⟨object⟩).value
def objectCellOf (domain : Digest) (object : Nat) : Nat := (ObjectiveActivity.objectCell domain ⟨object⟩).value
def packageCellOf (domain : Digest) (pin : Nat) : Nat := (ObjectiveActivity.packageCell domain ⟨pin⟩).value

/-- The record cell of the activity a birth transaction made on an object. -/
def recordCellOf (domain : Digest) (object transaction : Nat) : Nat :=
  (ObjectiveActivity.recordCell domain ⟨object⟩ (ObjectiveActivity.activityId ⟨object⟩ ⟨transaction⟩)).value

def inboxCellOf (domain : Digest) (sender target : Nat) : Nat := (Inbox.cell domain sender target).value
def slotCellOf (domain : Digest) (name : Nat) : Nat := (AnswerSlot.cell domain ⟨name⟩).value

def viewCells (domain : Digest) (request : ViewRequest) : List Nat :=
  request.cells ++ request.objects.map (stateCellOf domain) ++ request.objects.map (objectCellOf domain) ++
    request.pins.map (packageCellOf domain) ++
    request.births.map (fun (object, transaction) => recordCellOf domain object transaction) ++
    request.inboxes.map (fun (sender, target) => inboxCellOf domain sender target) ++
    request.slots.map (slotCellOf domain)

def viewJson (domain : Digest) (asset : Nat) (request : ViewRequest) (view : NativeHost.ActivityView) : Json :=
  let book := view.book.map fun cell => Minidregg.Theory.CanonicalResourceKernel.logicalBook cell.logical
  .mkObj [("type", "objective-activity-view-v1"), ("height", decimal view.height),
    ("authorityRoot", decimal view.authorityRoot.value),
    ("asset", decimal asset),
    ("cells", Json.arr (view.cells.map fun (cell, root, bytes) => cellJson domain cell root bytes).toArray),
    ("objects", Json.arr (request.objects.map fun object =>
      .mkObj [("object", decimal object), ("stateCell", decimal (stateCellOf domain object)),
        ("objectCell", decimal (objectCellOf domain object))]).toArray),
    ("births", Json.arr (request.births.map fun (object, transaction) =>
      .mkObj [("object", decimal object), ("transaction", decimal transaction),
        ("record", decimal (recordCellOf domain object transaction))]).toArray),
    ("pins", Json.arr (request.pins.map fun pin =>
      .mkObj ([("pin", decimal pin), ("packageCell", decimal (packageCellOf domain pin))] ++
        -- The front-end quote (`ObjectiveActivity.frontEndQuote`): what a paying envelope declares as
        -- `replayBytes` and `coreBytes` for this package (`frontEndPaid_at_quote`); absent when the
        -- cell holds no canonical package.
        match (view.cells.find? fun (cell, _, _) => cell == packageCellOf domain pin).bind fun (_, _, bytes) =>
            ObjectiveActivity.frontEndQuote ((ObjectiveActivity.bodyOf .package bytes).getD []) with
        | some (replayBytes, coreBytes) =>
          [("frontEnd", .mkObj [("replayBytes", decimal replayBytes), ("coreBytes", decimal coreBytes)])]
        | none => [])).toArray),
    ("inboxes", Json.arr (request.inboxes.map fun (sender, target) =>
      .mkObj [("sender", decimal sender), ("target", decimal target),
        ("cell", decimal (inboxCellOf domain sender target))]).toArray),
    ("slots", Json.arr (request.slots.map fun name =>
      .mkObj [("name", decimal name), ("cell", decimal (slotCellOf domain name))]).toArray),
    ("limits", .mkObj [("extractTicks", match view.extractTicks with
      | some ticks => decimal ticks
      | none => .null)]),
    ("quotes", Json.arr (view.quotes.map fun (record, await, quote) =>
      match quote with
      | .ok quote => .mkObj [("record", decimal record), ("await", decimal await),
          ("needed", decimal quote.needed), ("escrow", decimal quote.escrow)]
      | .error reason => .mkObj [("record", decimal record), ("await", decimal await),
          ("refused", toJson reason)]).toArray),
    ("balances", match book with
      | none => .null
      | some book => Json.arr (request.accounts.map fun account =>
          .mkObj [("account", decimal account), ("registered", toJson (decide (account ∈ book.accounts))),
            ("balance", toJson (toString (book.balance account asset)))]).toArray),
    ("total", match book with
      | none => .null
      | some book => toJson (toString (book.totalAsset asset)))]

end Minidregg.Host.ObjectiveActivityJson
