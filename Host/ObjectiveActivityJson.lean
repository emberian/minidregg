/- The kernel activity's JSON surface: authoring a signed command's bytes
(`author objective-activity`), inspecting a command or a signing plan, and the
public activity view (session op 214). An activity artifact is the Host's
`objective-publication SPEC activity DIR` (`ObjectivePackageAuthor`, output
codec `activity`).

Nothing here decides anything: commands are judged by
`Kernel.ObjectiveActivityReceiver`, artifacts by the kernel's `publish`. -/
import Kernel.NativeHost
import Compiler.ObjectiveBendDataWire

namespace Minidregg.Host.ObjectiveActivityJson
open Lean (Json toJson)
open Minidregg.Theory Minidregg.Compiler
open Minidregg.Theory.TypedAuthorization (Digest SubjectId CapabilityId)
open Minidregg.Kernel
open Minidregg.Kernel.ObjectiveActivityWire
open Minidregg.Kernel.ObjectiveActivityReceiver (Command Turn AnswerWire)
open Minidregg.Compiler.ObjectiveBendDataWire (dataJson)
open Minidregg.Compiler.ObjectiveInvocationClaim (Capacity)
set_option autoImplicit false

abbrev Result := Except String

def decimal (value : Nat) : Json := .str (toString value)

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

def field (path : String) (json : Json) (name : String) : Result Json :=
  match json.getObjVal? name with
  | .ok value => .ok value
  | .error _ => .error s!"{path}.{name} missing"

def nat (path : String) (json : Json) (name : String) : Result Nat := do
  let value ← field path json name
  let some text := value.getStr?.toOption | throw s!"{path}.{name} must be a decimal string"
  let some n := text.toNat? | throw s!"{path}.{name} must be a decimal string"
  unless toString n == text do throw s!"{path}.{name} must be canonical decimal"
  pure n

def str (path : String) (json : Json) (name : String) : Result String := do
  let some text := (← field path json name).getStr?.toOption | throw s!"{path}.{name} must be a string"
  pure text

def data (path : String) (json : Json) (name : String) : Result (List UInt8) := do
  let value ← ObjectiveBendDataWire.decodeData 64 (← field path json name)
  pure (dataBytes value)

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

/-- A declared envelope: every `Capacity` field as a decimal string. -/
def capacity (path : String) (json : Json) : Result Capacity := do
  let n := nat path json
  pure ⟨← n "typeFuel", ← n "sourceTicks", ← n "heap", ← n "stack", ← n "outputNodes", ← n "outputBytes",
    ← n "inputBytes", ← n "scalarBits", ← n "memoryTouches", ← n "proofWork", ← n "feeDebit", ← n "turnBytes",
    ← n "witnessBytes", ← n "storageBytes", ← n "sideEffectCount", ← n "networkBytes", ← n "leaseByteBlocks",
    ← n "incidences"⟩

def capacityJson (c : Capacity) : Json := .mkObj
  [("typeFuel", decimal c.typeFuel), ("sourceTicks", decimal c.sourceTicks), ("heap", decimal c.heap),
   ("stack", decimal c.stack), ("outputNodes", decimal c.outputNodes), ("outputBytes", decimal c.outputBytes),
   ("inputBytes", decimal c.inputBytes), ("scalarBits", decimal c.scalarBits),
   ("memoryTouches", decimal c.memoryTouches), ("proofWork", decimal c.proofWork), ("feeDebit", decimal c.feeDebit),
   ("turnBytes", decimal c.turnBytes), ("witnessBytes", decimal c.witnessBytes),
   ("storageBytes", decimal c.storageBytes), ("sideEffectCount", decimal c.sideEffectCount),
   ("networkBytes", decimal c.networkBytes), ("leaseByteBlocks", decimal c.leaseByteBlocks),
   ("incidences", decimal c.incidences)]

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

/-- An added envelope: `extra` (a `Capacity`), or none (the zero envelope). -/
def extra (path : String) (json : Json) : Result Capacity :=
  match json.getObjVal? "extra" with
  | .ok value => capacity (path ++ ".extra") value
  | .error _ => .ok ObjectiveTariff.zeroCapacity

/-- The turn of a command. `law` reads a predicate (the Host's `predicate` JSON
reader), for a creation's law and upgrade policy. -/
def turn (law : String → Json → Result Minidregg.Pred.Pred) (json : Json) : Result Turn := do
  let p := "$.turn"
  match ← str p json "kind" with
  | "publish" => pure (.publish (← unhex (← str p json "artifact")) (← unhex (← str p json "package"))
      (← nat p json "payer") ⟨← nat p json "payerCapability"⟩)
  | "create" => pure (.create (← nat p json "object") ⟨← nat p json "objectCapability"⟩ ⟨← nat p json "pin"⟩
      (← law (p ++ ".law") (← field p json "law")) (← upgrade law (p ++ ".upgrade") (← field p json "upgrade"))
      (← nat p json "payer") ⟨← nat p json "payerCapability"⟩)
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
  | "writeState" => pure (.writeState (← nat p json "object") ⟨← nat p json "objectCapability"⟩
      (← data p json "value"))
  | "exhaust" => pure (.exhaust ⟨← nat p json "record"⟩ ⟨← nat p json "await"⟩ (← extra p json)
      (← nat p json "account") ⟨← nat p json "accountCapability"⟩)
  | "abandon" => pure (.abandon ⟨← nat p json "record"⟩ ⟨← nat p json "await"⟩)
  | other => throw s!"$.turn.kind {other} is not publish, create, birth, resolve, deliver, topUp, writeState, \
      exhaust or abandon"

/-- `author objective-activity`: `{subject, nonce, expectedAuthorityRoot, turn}`. -/
def author (law : String → Json → Result Minidregg.Pred.Pred) (json : Json) : Result (List UInt8) := do
  let command : Command :=
    { subject := ⟨← nat "$" json "subject"⟩, nonce := ← nat "$" json "nonce"
      expectedAuthorityRoot := ⟨← nat "$" json "expectedAuthorityRoot"⟩
      turn := ← turn law (← field "$" json "turn") }
  pure (ObjectiveActivityReceiver.commandCodec.encode command)

def dataOf (bytes : List UInt8) : Json :=
  match decodeDataBytes bytes with
  | some value => dataJson value
  | none => .mkObj [("undecodable", toJson (hex bytes))]

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
  | .create object oc pin law policy payer pc => .mkObj
      [("kind", "create"), ("object", decimal object), ("objectCapability", decimal oc.value),
       ("pin", decimal pin.value), ("law", toJson (reprStr law)), ("upgrade", upgradeJson policy),
       ("payer", decimal payer), ("payerCapability", decimal pc.value)]
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
  | .writeState object oc value => .mkObj
      [("kind", "writeState"), ("object", decimal object), ("objectCapability", decimal oc.value),
       ("value", dataOf value)]
  | .exhaust record await extra account ac => .mkObj
      [("kind", "exhaust"), ("record", decimal record.value), ("await", decimal await.value),
       ("extra", capacityJson extra), ("account", decimal account), ("accountCapability", decimal ac.value)]
  | .abandon record await => .mkObj
      [("kind", "abandon"), ("record", decimal record.value), ("await", decimal await.value)]

def commandJson (command : Command) : Json := .mkObj
  [("type", "objective-activity-command-v2"),
   ("canonical", toJson (hex (ObjectiveActivityReceiver.commandCodec.encode command))),
   ("subject", decimal command.subject.value), ("nonce", decimal command.nonce),
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
      [("type", "objective-activity-plan-v1"), ("canonical", toJson (hex bytes)),
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

def slotJson (slot : AnswerSlot.Slot) : Json :=
  .mkObj [("name", decimal slot.name.value), ("activity", decimal slot.activity.value),
    ("decider", decimal slot.decider.value), ("deadline", decimal slot.deadline),
    ("phase", match slot.phase with
      | .opened => "open"
      | .decided decision height => .mkObj [("decision", decisionJson decision), ("height", decimal height)])]

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
            ("upgrade", upgradeJson record.upgrade), ("continuity", decimal record.continuity),
            ("payer", decimal record.payer)]
        | none => [("kind", "object-undecodable")]
  .mkObj ([("cell", decimal cell), ("root", decimal root.value)] ++ described)

/-- The view request: `{cells: [id..], accounts: [id..], objects: [id..], pins: [pin..],
births: [{object, transaction}..]}`; objects name their state and record cells, pins their
package cells, and births (an object and a birth's transaction) their record cells. -/
structure ViewRequest where
  cells : List Nat
  accounts : List Nat
  objects : List Nat
  pins : List Nat
  births : List (Nat × Nat)

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

def parseViewRequest (bytes : List UInt8) : Result ViewRequest := do
  if bytes.isEmpty then return ⟨[], [], [], [], []⟩
  let some text := String.fromUTF8? ⟨bytes.toArray⟩ | throw "view request is not UTF-8"
  let json ← Json.parse text
  pure ⟨← natList json "cells", ← natList json "accounts", ← natList json "objects", ← natList json "pins",
    ← births json⟩

def stateCellOf (domain : Digest) (object : Nat) : Nat := (ObjectiveActivity.stateCell domain ⟨object⟩).value
def objectCellOf (domain : Digest) (object : Nat) : Nat := (ObjectiveActivity.objectCell domain ⟨object⟩).value
def packageCellOf (domain : Digest) (pin : Nat) : Nat := (ObjectiveActivity.packageCell domain ⟨pin⟩).value

/-- The record cell of the activity a birth transaction made on an object. -/
def recordCellOf (domain : Digest) (object transaction : Nat) : Nat :=
  (ObjectiveActivity.recordCell domain ⟨object⟩ (ObjectiveActivity.activityId ⟨object⟩ ⟨transaction⟩)).value

def viewCells (domain : Digest) (request : ViewRequest) : List Nat :=
  request.cells ++ request.objects.map (stateCellOf domain) ++ request.objects.map (objectCellOf domain) ++
    request.pins.map (packageCellOf domain) ++
    request.births.map fun (object, transaction) => recordCellOf domain object transaction

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
      .mkObj [("pin", decimal pin), ("packageCell", decimal (packageCellOf domain pin))]).toArray),
    ("balances", match book with
      | none => .null
      | some book => Json.arr (request.accounts.map fun account =>
          .mkObj [("account", decimal account), ("registered", toJson (decide (account ∈ book.accounts))),
            ("balance", toJson (toString (book.balance account asset)))]).toArray),
    ("total", match book with
      | none => .null
      | some book => toJson (toString (book.totalAsset asset)))]

end Minidregg.Host.ObjectiveActivityJson
