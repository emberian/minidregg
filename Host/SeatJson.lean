/- Seats and invitations, JSON surface: authoring a signed seat command's bytes
(`author seat`), inspecting a command, a signing plan or an ingress, the public
seat view (session op 219), and the contract artifact of a package spec
(`seat-contract-artifact`).

Nothing here decides anything: commands are judged by `Kernel.SeatReceiver`,
artifacts by the seat kernel's `publish`. -/
import Kernel.NativeHost
import Compiler.ObjectiveBendDataWire
import Host.ObjectivePackageAuthor
import Host.ObjectiveBendFrontEnd

namespace Minidregg.Host.SeatJson
open Lean (Json toJson)
open Minidregg.Theory Minidregg.Compiler
open Minidregg.Theory.TypedAuthorization (Digest SubjectId CapabilityId)
open Minidregg.Kernel
open Minidregg.Kernel.ObjectiveActivityWire
open Minidregg.Kernel.SeatStore (Turn)
open Minidregg.Kernel.SeatReceiver (Command Grants)
open Minidregg.Compiler.ObjectiveBendDataWire (dataJson)
open Minidregg.Pred (Pred)
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

def natOf (path : String) (value : Json) : Result Nat := do
  let some text := value.getStr?.toOption | throw s!"{path} must be a decimal string"
  let some n := text.toNat? | throw s!"{path} must be a decimal string"
  unless toString n == text do throw s!"{path} must be canonical decimal"
  pure n

def nat (path : String) (json : Json) (name : String) : Result Nat := do
  natOf s!"{path}.{name}" (← field path json name)

def optNat (path : String) (json : Json) (name : String) : Result (Option Nat) :=
  match json.getObjVal? name with
  | .error _ => .ok none
  | .ok .null => .ok none
  | .ok value => (natOf s!"{path}.{name}" value).map some

def str (path : String) (json : Json) (name : String) : Result String := do
  let some text := (← field path json name).getStr?.toOption | throw s!"{path}.{name} must be a string"
  pure text

def arr (path : String) (json : Json) (name : String) : Result (List Json) :=
  match json.getObjVal? name with
  | .error _ => .ok []
  | .ok value => match value.getArr? with
    | .ok items => .ok items.toList
    | .error _ => .error s!"{path}.{name} must be an array"

def amounts (path : String) (json : Json) (name : String) : Result (List (Nat × Nat)) := do
  (← arr path json name).mapM fun item => do pure (← nat path item "asset", ← nat path item "amount")

def proposal (json : Json) : Result Seats.Proposal := do
  let p := "$.turn.proposal"
  let exit ← match ← optNat p json "afterDeadline" with
    | none => pure Seats.ExitRule.onDemand
    | some due => pure (Seats.ExitRule.afterDeadline due)
  pure ⟨← amounts p json "give", ← amounts p json "want", exit⟩

/-- `$.turn`: `{kind: publish|create|handOver|offer|invoke|exit, ...}`. The
clause of `create` is a policy predicate JSON (`predicate`, the Host's own parser). -/
def turn (predicate : String → Json → Result Pred) (json : Json) : Result Turn := do
  let p := "$.turn"
  match ← str p json "kind" with
  | "publish" => pure (.publish (← unhex (← str p json "artifact")))
  | "create" => pure (.create (← nat p json "instance") ⟨← nat p json "pin"⟩
      (← predicate (p ++ ".clause") (← field p json "clause")))
  | "handOver" => pure (.handOver (← nat p json "invitation") ⟨← nat p json "recipient"⟩)
  | "offer" =>
      let expect ← field p json "expect"
      pure (.offer (← nat p json "invitation")
        ⟨← nat (p ++ ".expect") expect "instance", ⟨← nat (p ++ ".expect") expect "package"⟩,
          ← str (p ++ ".expect") expect "role"⟩
        (← nat p json "funding") (← nat p json "payee") (← proposal (← field p json "proposal"))
        (← optNat p json "holder"))
  | "invoke" => pure (.invoke (← nat p json "instance")
      (dataBytes (← ObjectiveBendDataWire.decodeData 64 (← field p json "input")))
      (← nat p json "ticks") (← nat p json "account"))
  | "exit" => pure (.exit (← nat p json "seat"))
  | other => throw s!"$.turn.kind {other} is not publish, create, handOver, offer, invoke or exit"

/-- `author seat`: `{subject, nonce, expectedAuthorityRoot, turn, objectCapability?, accountCapability?}`. -/
def author (predicate : String → Json → Result Pred) (json : Json) : Result (List UInt8) := do
  let command : Command :=
    { subject := ⟨← nat "$" json "subject"⟩, nonce := ← nat "$" json "nonce"
      expectedAuthorityRoot := ⟨← nat "$" json "expectedAuthorityRoot"⟩
      turn := ← turn predicate (← field "$" json "turn")
      grants := ⟨(← optNat "$" json "objectCapability").map (⟨·⟩), (← optNat "$" json "accountCapability").map (⟨·⟩)⟩ }
  pure (SeatReceiver.commandCodec.encode command)

def dataOf (bytes : List UInt8) : Json :=
  match decodeDataBytes bytes with
  | some value => dataJson value
  | none => .mkObj [("undecodable", toJson (hex bytes))]

def amountsJson (entries : List (Nat × Nat)) : Json :=
  Json.arr (entries.map fun (asset, amount) => Json.mkObj [("asset", decimal asset), ("amount", decimal amount)]).toArray

def proposalJson (p : Seats.Proposal) : Json :=
  .mkObj [("give", amountsJson p.give), ("want", amountsJson p.want),
    ("exit", match p.exit with
      | .onDemand => "onDemand"
      | .afterDeadline due => .mkObj [("afterDeadline", decimal due)])]

def turnJson : Turn → Json
  | .publish artifact => .mkObj [("kind", "publish"), ("artifactBytes", decimal artifact.length)]
  | .create inst pin _ => .mkObj [("kind", "create"), ("instance", decimal inst), ("pin", decimal pin.value)]
  | .handOver invitation recipient => .mkObj [("kind", "handOver"), ("invitation", decimal invitation),
      ("recipient", decimal recipient.value)]
  | .offer invitation expect funding payee p holder => .mkObj
      [("kind", "offer"), ("invitation", decimal invitation),
       ("expect", .mkObj [("instance", decimal expect.inst), ("package", decimal expect.package.value),
         ("role", toJson expect.role)]),
       ("funding", decimal funding), ("payee", decimal payee), ("proposal", proposalJson p),
       ("holder", match holder with | some r => decimal r | none => .null)]
  | .invoke inst input ticks account => .mkObj [("kind", "invoke"), ("instance", decimal inst),
      ("input", dataOf input), ("ticks", decimal ticks), ("account", decimal account)]
  | .exit seat => .mkObj [("kind", "exit"), ("seat", decimal seat)]

def commandJson (domain : Option Digest) (command : Command) : Json :=
  let transaction := SeatStore.transactionOf command.request
  .mkObj
  [("type", "seat-command-v1"),
   ("canonical", toJson (hex (SeatReceiver.commandCodec.encode command))),
   ("subject", decimal command.subject.value), ("nonce", decimal command.nonce),
   ("expectedAuthorityRoot", decimal command.expectedAuthorityRoot.value),
   ("transaction", decimal transaction.value),
   ("seatAccount", match domain, command.turn with
     | some d, .offer .. => decimal (SeatStore.seatAccount d transaction)
     | _, _ => .null),
   ("turn", turnJson command.turn)]

def inspectCommand (bytes : List UInt8) : Result Json :=
  match SeatReceiver.commandCodec.decode bytes with
  | some command => .ok (commandJson none command)
  | none => .error "noncanonical seat command"

def inspectPlan (bytes : List UInt8) : Result Json :=
  match SeatReceiver.signingPlanCodec.decode bytes with
  | none => .error "noncanonical seat plan"
  | some plan => .ok (.mkObj
      [("type", "seat-plan-v1"), ("canonical", toJson (hex bytes)),
       ("domain", decimal plan.domain.value), ("semantics", decimal plan.semantics.value),
       ("command", match SeatReceiver.commandCodec.decode plan.commandBytes with
         | some command => commandJson (some plan.domain) command | none => .null),
       ("header", .mkObj [("canonical", toJson (hex plan.header))])])

def inspectIngress (bytes : List UInt8) : Result Json :=
  match SeatReceiver.decodeIngress bytes with
  | none => .error "noncanonical seat ingress"
  | some ingress => .ok (.mkObj
      [("type", "seat-ingress-v1"), ("command", commandJson none ingress.command),
       ("envelopeBytes", decimal ingress.ingress.envelope.length)])

/-! ## The public view -/

def seatJson (body : SeatStore.SeatBody) : Json :=
  .mkObj [("account", decimal body.seat.account), ("instance", decimal body.seat.inst),
    ("offerer", decimal body.seat.offerer.value), ("payee", decimal body.seat.payee),
    ("proposal", proposalJson body.seat.proposal),
    ("holder", match body.seat.holder with | some r => decimal r | none => .null),
    ("open", toJson body.seat.isOpen), ("role", toJson body.role),
    ("terms", Json.arr (body.terms.map fun (n, v) => Json.mkObj [("name", toJson n), ("value", decimal v)]).toArray)]

def invitationJson (body : SeatStore.InvitationBody) : Json :=
  let v := body.invitation
  .mkObj [("id", decimal v.id), ("instance", decimal v.inst), ("package", decimal v.package.value),
    ("role", toJson v.role), ("holder", decimal v.holder.value), ("spent", toJson body.spent),
    ("terms", Json.arr (v.terms.map fun (n, x) => Json.mkObj [("name", toJson n), ("value", decimal x)]).toArray)]

def instanceJson (body : SeatStore.InstanceBody) : Json :=
  .mkObj [("instance", decimal body.inst.id), ("package", decimal body.inst.package.value),
    ("openSeats", Json.arr (body.seats.map decimal).toArray), ("retired", toJson body.retired)]

def cellJson (domain : Digest) (cell : Nat) (root : Digest) (bytes : List UInt8) : Json :=
  let described : List (String × Json) :=
    match SeatStore.payloadOf bytes with
    | none => [("kind", if bytes.isEmpty then "absent" else "not-a-seat-cell")]
    | some payload =>
      let at_ := decide (cell = SeatCell.coordinate domain payload.role payload.key)
      [("atCoordinate", toJson at_)] ++
      match payload.role with
      | .inst => match SeatStore.instanceCodec.decode payload.body with
        | some body => [("kind", "instance"), ("instance", instanceJson body)]
        | none => [("kind", "instance-undecodable")]
      | .invitation => match SeatStore.invitationCodec.decode payload.body with
        | some body => [("kind", "invitation"), ("invitation", invitationJson body)]
        | none => [("kind", "invitation-undecodable")]
      | .seat => match SeatStore.seatCodec.decode payload.body with
        | some body => [("kind", "seat"), ("seat", seatJson body)]
        | none => [("kind", "seat-undecodable")]
      | .holdings => match SeatStore.holdingsCodec.decode payload.body with
        | some seats => [("kind", "holdings"), ("seats", Json.arr (seats.map decimal).toArray)]
        | none => [("kind", "holdings-undecodable")]
      | .package => match ObjectiveBendSourceArtifact.decode payload.body with
        | some artifact => [("kind", "package"), ("declaration", toJson artifact.declaration),
            ("pin", decimal (ObjectiveBendSourceArtifact.identity artifact).value)]
        | none => [("kind", "package-undecodable")]
  .mkObj ([("cell", decimal cell), ("root", decimal root.value)] ++ described)

/-- The view request: `{instances, invitations, seats, holdings, pins, accounts, assets}`
(decimal strings): instance ids, invitation ids, seat accounts, activity record
cells, package pins name their cells; accounts and assets name Book balances. -/
structure ViewRequest where
  instances : List Nat
  invitations : List Nat
  seats : List Nat
  holdings : List Nat
  pins : List Nat
  accounts : List Nat
  assets : List Nat

def natList (json : Json) (name : String) : Result (List Nat) := do
  (← arr "$" json name).mapM (natOf s!"$.{name}[]")

def parseViewRequest (bytes : List UInt8) : Result ViewRequest := do
  if bytes.isEmpty then return ⟨[], [], [], [], [], [], []⟩
  let some text := String.fromUTF8? ⟨bytes.toArray⟩ | throw "view request is not UTF-8"
  let json ← Json.parse text
  pure ⟨← natList json "instances", ← natList json "invitations", ← natList json "seats",
    ← natList json "holdings", ← natList json "pins", ← natList json "accounts", ← natList json "assets"⟩

def viewCells (domain : Digest) (request : ViewRequest) : List Nat :=
  request.instances.map (fun i => (SeatStore.instanceCell domain i).value) ++
    request.invitations.map (fun i => (SeatStore.invitationCell domain i).value) ++
    request.seats ++
    request.holdings.map (fun r => (SeatStore.holdingsCell domain r).value) ++
    request.pins.map (fun p => (SeatStore.packageCell domain ⟨p⟩).value)

def viewJson (domain : Digest) (request : ViewRequest) (view : NativeHost.SeatView) : Json :=
  let book := view.book.map fun cell => Minidregg.Theory.CanonicalResourceKernel.logicalBook cell.logical
  .mkObj [("type", "seat-view-v1"), ("height", decimal view.height),
    ("authorityRoot", decimal view.authorityRoot.value),
    ("cells", Json.arr (view.cells.map fun (cell, root, bytes) => cellJson domain cell root bytes).toArray),
    ("balances", match book with
      | none => .null
      | some book => Json.arr (request.accounts.flatMap fun account => request.assets.map fun asset =>
          Json.mkObj [("account", decimal account), ("asset", decimal asset),
            ("registered", toJson (decide (account ∈ book.accounts))),
            ("balance", toJson (toString (book.balance account asset)))]).toArray),
    ("totals", match book with
      | none => .null
      | some book => Json.arr (request.assets.map fun asset =>
          Json.mkObj [("asset", decimal asset), ("total", toJson (toString (book.totalAsset asset)))]).toArray)]

/-! ## The contract artifact of a package spec -/

/-- `seat-contract-artifact SPEC OUT`: capture the spec's sources, lower the
selected definition with this Host's own front end, and make the contract
artifact (the seat kernel's output codec `SeatStore.contractCodecId`). -/
def artifact (specPath : String) : IO (List UInt8 × Json) := do
  let captured ← match ← (Minidregg.Host.ObjectiveBendFrontEnd.captureSpec specPath false).run with
    | .ok c => pure c
    | .error d => throw (IO.userError d.json.compress)
  let package := Minidregg.Host.ObjectivePackageAuthor.packageOf
    (captured.modules.toList.zip (captured.bytes.toList.map (·.toList))) captured.entryModule captured.entryDefinition
  let core ← match ObjectiveBendPublication.publishedCore package with
    | .ok core => pure core
    | .error d => throw (IO.userError (d.stage ++ ": " ++ d.message))
  let some declaration := ObjectiveSourcePackage.selectedDeclaration package
    | throw (IO.userError "selected declaration missing")
  let artifact : ObjectiveBendSourceArtifact.Artifact := ⟨ObjectiveSourcePackage.identity package, declaration,
    core, Minidregg.Kernel.ObjectiveBendNativeInput.codecId, SeatStore.contractCodecId⟩
  let bytes := ObjectiveBendSourceArtifact.encode artifact
  pure (bytes, .mkObj [("pin", decimal (ObjectiveBendSourceArtifact.identity artifact).value),
    ("package", decimal artifact.package.value), ("declaration", toJson declaration),
    ("bytes", decimal bytes.length), ("hex", toJson (hex bytes))])

end Minidregg.Host.SeatJson
