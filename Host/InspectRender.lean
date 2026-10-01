/-
# Host.InspectRender — the K-INSPECT-VIEWS renderers (`inspect cap-tree|law|why|turn|receipt`)

Each `inspect` kind here takes one JSON document naming bytes the client already
holds (hex), decodes every frame with the Host's own codecs, runs the pure view
of `Host.InspectViews`, and returns JSON whose `text` field is the plain-text
rendering. Nothing here opens a Store or reads anything but its input.
-/
import Host.InspectViews
import Kernel.NativeHost
import Lean.Data.Json

namespace Minidregg.Host.InspectRender

open Lean
open Minidregg.Pred
open Minidregg.Compiler
open Minidregg.Compiler.NativeHostCodec
open Minidregg.Theory
open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.CredentialAuthorityState
open Minidregg.Kernel
open Minidregg.Host.InspectViews

set_option autoImplicit false

abbrev Result := Except String

private def decimal (n : Nat) : Json := .str (toString n)

private def hexDigit (c : Char) : Option Nat :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else none

private def unhexChars : List Char → Option (List UInt8)
  | [] => some []
  | a :: b :: rest => do
      let hi ← hexDigit a
      let lo ← hexDigit b
      let tail ← unhexChars rest
      pure (UInt8.ofNat (hi * 16 + lo) :: tail)
  | [_] => none

private def unhex (path : String) (s : String) : Result (List UInt8) :=
  match unhexChars s.toList with
  | some bytes => pure bytes
  | none => throw s!"{path}: not lowercase hex"

private def hexText (bytes : List UInt8) : String := String.ofList <|
  bytes.flatMap fun byte =>
    let digits := "0123456789abcdef".toList
    [digits[byte.toNat / 16]?.getD '0', digits[byte.toNat % 16]?.getD '0']

private def input (bytes : List UInt8) : Result Json := do
  let some text := String.fromUTF8? (ByteArray.mk bytes.toArray)
    | throw "inspect input: not UTF-8"
  Json.parse text

private def field (path : String) (json : Json) (key : String) : Result Json :=
  match json.getObjVal? key with
  | .ok value => pure value
  | .error _ => throw s!"{path}: missing {key}"

private def str (path : String) (json : Json) (key : String) : Result String := do
  match (← field path json key).getStr? with
  | .ok s => pure s
  | .error _ => throw s!"{path}.{key}: expected a string"

private def optHex (path : String) (json : Json) (key : String) : Result (Option (List UInt8)) :=
  match json.getObjVal? key with
  | .ok .null | .error _ => pure none
  | .ok (.str s) => some <$> unhex s!"{path}.{key}" s
  | .ok _ => throw s!"{path}.{key}: expected hex or null"

private def kindName : ResourceKind → String
  | .object => "object" | .account => "account" | .program => "program"

private def kindOf (path : String) : String → Result ResourceKind
  | "object" => pure .object | "account" => pure .account | "program" => pure .program
  | other => throw s!"{path}: unknown resource kind {other}"

private def verbText (tag : Nat) : String :=
  match tag with
  | 1 => "observe" | 2 => "mutate/transfer/install" | 3 => "delegate"
  | 4 => "installPolicy" | 5 => "revokeCapability" | n => toString n

private def verbNames {kind : ResourceKind} (verbs : Finset (Verb kind)) : List String :=
  let tags := (verbs.image CredentialAuthorityEntryCodec.verbTag).sort (· ≤ ·)
  tags.map fun tag => match kind, tag with
    | .object, 2 => "mutate" | .account, 2 => "transfer" | .program, 2 => "install"
    | _, t => verbText t

private def braces (xs : List String) : String := "{" ++ ",".intercalate xs ++ "}"

private def holderText : Holder → String
  | .bearer => "bearer"
  | .subject s => s!"subject {s.value}"

private def decodeOutcome (path : String) (bytes : List UInt8) : Result Outcome :=
  match outcomeCodec.decode bytes with
  | some outcome => pure outcome
  | none => throw s!"{path}: not an OUTCOME/v4 frame"

/-! ## cap-tree -/

private def sourceText : Source → String
  | .record => "record"
  | .lineage => "lineage"
  | .delegated proposal none => s!"my delegation {proposal} (no outcome held)"
  | .delegated proposal (some true) => s!"my delegation {proposal}, installed"
  | .delegated proposal (some false) => s!"my delegation {proposal}, refused"

private def item (kind : ResourceKind) (index : Nat) (json : Json) : Result (Item kind) := do
  let path := s!"items[{index}]"
  match ← str path json "type" with
  | "record" =>
      let frame ← unhex s!"{path}.frame" (← str path json "frame")
      let codec := (CredentialAuthorityEntryCodec.storedCapabilityStream kind).toLawful
      let some stored := codec.decode frame | throw s!"{path}: not a stored {kindName kind} capability"
      unless codec.encode stored == frame do throw s!"{path}: stored capability encoding alias"
      pure (.record stored)
  | "refused" =>
      let id ← match (← str path json "capability").toNat? with
        | some id => pure id | none => throw s!"{path}.capability: expected a decimal id"
      match ← decodeOutcome s!"{path}.frame" (← unhex s!"{path}.frame" (← str path json "frame")) with
      | .refused reason _ _ _ => pure (.refused id reason)
      | _ => throw s!"{path}: the frame is not a refusal"
  | "delegated" =>
      let proposal ← str path json "proposal"
      let plan ← unhex s!"{path}.plan" (← str path json "plan")
      let some signing := signingPlanCodec.decode plan | throw s!"{path}.plan: not a SIGNING-PLAN/v4 frame"
      let .delegate command := signing.finalizedDraft
        | throw s!"{path}.plan: not a delegation plan"
      let some ⟨commandKind, decoded⟩ := CapabilityDelegationController.commandCodec.decode command
        | throw s!"{path}.plan: noncanonical delegation command"
      let confirmed ← match ← optHex path json "outcome" with
        | none => pure none
        | some bytes => match ← decodeOutcome s!"{path}.outcome" bytes with
          | .confirmed _ _ => pure (some true)
          | .refused .. => pure (some false)
          | _ => pure none
      if same : commandKind = kind then
        pure (.delegated proposal (same ▸ decoded.declaration.child) confirmed)
      else throw s!"{path}: the delegation is over a {kindName commandKind} resource"
  | other => throw s!"{path}: unknown item type {other}"

private def capJson {kind : ResourceKind} (cap : Capability kind) : List (String × Json) :=
  [("holder", holderText cap.holder),
   ("targets", .arr <| ((cap.scope.targets.image (·.value)).sort (· ≤ ·)).toArray.map decimal),
   ("verbs", .arr <| (verbNames cap.scope.verbs).toArray.map Json.str),
   ("maxCost", decimal cap.scope.maxCost), ("notBefore", decimal cap.notBefore),
   ("notAfter", decimal cap.notAfter), ("root", decimal cap.root.value),
   ("parent", cap.parent.map (fun p => decimal p.value) |>.getD .null),
   ("issuer", decimal cap.issuer.value)]

private def nodeJson {kind : ResourceKind} (node : Node kind) : Json :=
  .mkObj <| [("id", decimal node.id), ("readable", .bool node.cap.isSome),
    ("sources", .arr <| (node.sources.map sourceText).toArray.map Json.str),
    ("refusals", .arr <| (node.refusals.map RefusalReason.name).toArray.map Json.str),
    ("revoked", .bool node.revoked), ("conflict", .bool node.conflict)] ++
    (match node.cap with | some cap => capJson cap | none => [])

private def narrowText {kind : ResourceKind} (edge : Edge kind) : String :=
  s!"targets ⊆, verbs ⊆, maxCost {edge.child.scope.maxCost} ≤ {edge.parent.scope.maxCost}"

private def nodeLine {kind : ResourceKind} (node : Node kind) : String :=
  let flags := (if node.revoked then " REVOKED" else "") ++
    (if node.conflict then " CONFLICTING-EVIDENCE" else "")
  match node.cap with
  | none =>
      let why := match node.refusals with
        | [] => "named as a parent; no record of it is held"
        | reasons => ", ".intercalate (reasons.map RefusalReason.name)
      s!"{node.id}  [not readable] ({why}){flags}"
  | some cap =>
      s!"{node.id}  {holderText cap.holder}  targets {braces ((cap.scope.targets.image (·.value)).sort (· ≤ ·) |>.map toString)}  verbs {braces (verbNames cap.scope.verbs)}  maxCost {cap.scope.maxCost}  heights {cap.notBefore}..{cap.notAfter}  [{", ".intercalate (node.sources.map sourceText)}]{flags}"

private partial def treeLines {kind : ResourceKind} (tree : CapTree kind) (fuel : Nat)
    (indent : String) (node : Node kind) : List String :=
  let children := tree.edges.filter (fun e => e.parent.id.value = node.id)
  let line := indent ++ nodeLine node
  match fuel with
  | 0 => [line]
  | fuel + 1 =>
    line :: children.flatMap fun edge =>
      match tree.nodes.find? (fun n => n.id = edge.child.id.value) with
      | none => []
      | some child =>
          (indent ++ "  └─ narrows: " ++ narrowText edge) ::
            treeLines tree fuel (indent ++ "     ") child

def capTreeView (bytes : List UInt8) : Result Json := do
  let json ← input bytes
  let kind ← kindOf "kind" (← str "input" json "kind")
  let target ← str "input" json "target"
  let items ← match (← field "input" json "items").getArr? with
    | .ok items => pure items.toList
    | .error _ => throw "items: expected an array"
  let parsed ← (items.zipIdx).mapM fun (j, i) => item kind i j
  let tree := capTree parsed
  let childIds := tree.edges.map (·.child.id.value)
  let tops := tree.nodes.filter (fun node => !childIds.contains node.id)
  let lines := s!"cap-tree {kindName kind} {target}: {tree.nodes.length} nodes, {tree.edges.length} edges, {tree.widenings.length} widenings" ::
    tops.flatMap (treeLines tree tree.nodes.length "") ++
    tree.widenings.map (fun e => s!"WIDENING (not drawn): {e.child.id.value} names parent {e.parent.id.value} but does not narrow it")
  pure <| .mkObj [("type", "cap-tree"), ("kind", kindName kind), ("target", target),
    ("nodes", .arr <| tree.nodes.toArray.map nodeJson),
    ("edges", .arr <| tree.edges.toArray.map fun e => .mkObj
      [("child", decimal e.child.id.value), ("parent", decimal e.parent.id.value),
       ("narrows", narrowText e)]),
    ("widenings", .arr <| tree.widenings.toArray.map fun e => .mkObj
      [("child", decimal e.child.id.value), ("parent", decimal e.parent.id.value)]),
    ("text", "\n".intercalate lines)]

/-! ## law -/

/-- The scalar fields of a reader's own resource view, `(field, value)`. -/
def fieldValues (bytes : List UInt8) : Option (List (Nat × Int)) := do
  let value ← NativeObservationController.resourceViewCodec.decode bytes
  let packed ← CellRegistry.PackedCell.decode CanonicalCellRegistry.registry value.1
  match packed with
  | ⟨.declaredObject, payload⟩ =>
      some <| (StoreCodec.entries DeclaredEffectCell.wire payload.logical).filterMap fun entry =>
        match entry.1.2 with
        | .objectField _ field => some (field.value, (entry.2 : Int))
        | _ => none
  | _ => some []

private def slotNow (fields : Option (List (Nat × Int))) (slot : Slot) : String :=
  match slot.splitOn "/" with
  | ["resource", "field", n, view] =>
      if view = "delta" then "(the step's change; no current value)" else
      match fields, n.toNat? with
      | none, _ => "(not in your read)"
      | some fields, some field => match fields.find? (·.1 = field) with
        | some (_, value) => s!"{value} now" ++ (if view = "before" then " (this is the value a step starts from)" else "")
        | none => "absent now"
      | some _, none => "(not in your read)"
  | ["request", _] => "(the request's own value)"
  | _ => "(not in your read)"

def lawView (bytes : List UInt8) : Result Json := do
  let json ← input bytes
  let name ← str "input" json "name"
  let policyBytes ← unhex "policy" (← str "input" json "policy")
  let some record := PolicyRecordCodec.decode policyBytes | throw "policy: noncanonical policy record"
  let fields ← match ← optHex "input" json "resource" with
    | none => pure none
    | some view => match fieldValues view with
      | some fields => pure (some fields)
      | none => throw "resource: not a resource view"
  let law := record.predicate
  let clauses := lawClauses law
  let line := "; ".intercalate (clauses.map LawLeaf.renderClause)
  let slots := (slotsOfList (PredList.ofList clauses)).eraseDups
  let lines := [s!"law {name}  (policy {record.policyId.value} version {record.version})", s!"  {line}"] ++
    (clauses.zipIdx.map fun (clause, i) => s!"  [{i}] {LawLeaf.renderClause clause}") ++
    (if slots.isEmpty then [] else "  slots:" :: slots.map fun slot =>
      s!"    {LawLeaf.renderSlot slot} = {slotNow fields slot}")
  pure <| .mkObj [("type", "law"), ("name", name),
    ("policyId", decimal record.policyId.value), ("version", decimal record.version),
    ("law", line), ("roundTrip", .bool (parseLaw (lawTokens law) == some law)),
    ("clauses", .arr <| clauses.zipIdx.toArray.map fun (clause, i) => .mkObj
      [("index", decimal i), ("text", LawLeaf.renderClause clause)]),
    ("slots", .arr <| slots.toArray.map fun (slot : Slot) => .mkObj
      [("slot", Json.str slot), ("rendered", LawLeaf.renderSlot slot), ("now", slotNow fields slot)]),
    ("text", "\n".intercalate lines)]

/-! ## why -/

private def relationText (clause : Pred) (before : Option Int) : String :=
  match clause with
  | .eq _ v => s!"== {v}"
  | .le _ v => s!"<= {v}"
  | .memberOf s xs => s!"in {LawLeaf.renderSet s xs}"
  | .monotone _ => s!">= {before.map toString |>.getD "its old value"}"
  | .writeOnce _ => s!"== {before.map toString |>.getD "its old value"} (it was already written)"
  | .not (.eq _ v) => s!"!= {v}"
  | .not (.le _ v) => s!"> {v}"
  | .not (.memberOf s xs) => s!"not in {LawLeaf.renderSet s xs}"
  | _ => ""

private def shown : Option Int → String
  | some v => toString v | none => "absent"

/-- The explanation of one refusal: only what the Host's refusal frame carries. -/
def explain (outcome : Outcome) : List String × List (String × Json) :=
  match outcome with
  | .refused reason _ _ (some leaf) =>
      let clause := LawLeaf.explained leaf.clause
      let slot := LawLeaf.slotOf clause
      let suggestion := suggest clause leaf.before leaf.after
      let judged := match slot with
        | some s => [s!"  judged on: {LawLeaf.renderSlot s} before {shown leaf.before}, after {shown leaf.after}"]
        | none => ["  it reads no single slot of the request"]
      let fix := match suggestion, slot with
        | some (s, v), _ => [s!"  to pass it: {LawLeaf.renderSlot s} {relationText clause leaf.before} — e.g. {v} (you asked {shown leaf.after})"]
        | none, none => ["  no change to the request passes it"]
        | none, some _ => ["  no request value passes it: it reads who you are, which verb you used, or a value the request does not write"]
      let place := if leaf.path.isEmpty then "the whole law" else s!"clause [{",".intercalate (leaf.path.map toString)}]"
      ([s!"refused: {reason.name}", s!"  failing {place}: {LawLeaf.renderClause clause}"] ++ judged ++ fix,
       [("reason", reason.name), ("clause", LawLeaf.renderClause clause),
        ("path", .arr <| leaf.path.toArray.map decimal),
        ("slot", (slot.map Json.str).getD .null),
        ("before", (leaf.before.map (fun v => Json.str (toString v))).getD .null),
        ("after", (leaf.after.map (fun v => Json.str (toString v))).getD .null),
        ("suggestion", match suggestion with
          | some (s, v) => .mkObj [("slot", s), ("value", toString v),
              ("relation", relationText clause leaf.before)]
          | none => .null)])
  | .refused .undisclosed _ _ none =>
      (["refused: undisclosed — a blind submission names no reason, by design"],
       [("reason", "undisclosed")])
  | .refused reason _ _ none =>
      ([s!"refused: {reason.name}: {reason.describe}"], [("reason", reason.name)])
  | .confirmed _ receipt => ([s!"not refused: confirmed at height {receipt.acceptedCount}"], [("reason", .null)])
  | .contention => (["not decided: contention"], [("reason", .null)])
  | .unavailable _ => (["not decided: unavailable"], [("reason", .null)])
  | .uncertain _ => (["not decided: uncertain"], [("reason", .null)])
  | .absent => (["not decided: absent"], [("reason", .null)])

/-- `why`'s output is a function of the refusal frame's reason and leaf alone:
two frames that agree on them render identically, whatever their phase or
detail bytes. It reads no other input, so it discloses nothing the Host's
refusal did not already carry to this requester. -/
theorem explain_reads_only_the_refusal (reason : RefusalReason) (leaf : Option LawLeaf)
    (phase phase' detail detail' : List UInt8) :
    explain (.refused reason phase detail leaf) = explain (.refused reason phase' detail' leaf) := by
  cases leaf <;> cases reason <;> rfl

#assert_axioms explain_reads_only_the_refusal

def whyView (bytes : List UInt8) : Result Json := do
  let json ← input bytes
  let attempt ← str "input" json "attempt"
  let outcome ← decodeOutcome "frame" (← unhex "frame" (← str "input" json "frame"))
  let (lines, fields) := explain outcome
  let (dryLines, dryJson) ← match json.getObjVal? "dryRun" with
    | .ok (.str "admitted") =>
        pure (["  dry run (op 130) of the same command, now: admitted (the state may have moved since)"],
          Json.str "admitted")
    | .ok (.str hex) => do
        let dry ← decodeOutcome "dryRun" (← unhex "dryRun" hex)
        let (more, moreJson) := explain dry
        pure ("  dry run (op 130) of the same command, now:" :: more.map ("    " ++ ·), Json.mkObj moreJson)
    | _ => pure ([], Json.null)
  pure <| .mkObj <| [("type", Json.str "why"), ("attempt", Json.str attempt)] ++ fields ++
    [("dryRun", dryJson), ("text", "\n".intercalate ((s!"why {attempt}" :: lines) ++ dryLines))]

/-! ## turn / receipt -/

private def revocationText : RevocationKey → String
  | .capability id => s!"capability {id.value}"
  | .channel id => s!"channel {id.value}"
  | .signingKey s e => s!"signing key of subject {s.value} epoch {e}"

def addressText : AuthAddress → String
  | ⟨.capability kind, id⟩ => s!"capability ({kindName kind}) {id.value}"
  | ⟨.issuerEpoch, issuer⟩ => s!"issuer epoch of {issuer.value}"
  | ⟨.policyEpoch, policy⟩ => s!"policy epoch of {policy.value}"
  | ⟨.policyRevision, policy⟩ => s!"policy revision of {policy.value}"
  | ⟨.policyAddress, (policy, revision)⟩ => s!"policy address of {policy.value} revision {revision}"
  | ⟨.subjectKeyEpoch, subject⟩ => s!"key epoch of subject {subject.value}"
  | ⟨.subjectKey, (subject, epoch)⟩ => s!"key of subject {subject.value} epoch {epoch}"
  | ⟨.revoked, key⟩ => s!"revocation of {revocationText key}"
  | ⟨.registered, key⟩ => s!"registration of {revocationText key}"

private def actionText : DeclaredActionLowering.Action → String
  | .create (.objectField _ f) v => s!"create field {f.value} = {v}"
  | .create key v => s!"create {repr key} = {v}"
  | .write (.objectField _ f) e v => s!"write field {f.value} := {v} (expected {e.map toString |>.getD "absent"})"
  | .write key _ v => s!"write {repr key} := {v}"
  | .move src dst _ _ _ amount => s!"move {amount} from {src.value} to {dst.value}"

private def draftLines : Draft → List String
  | .invoke bytes => match DeclaredResourceController.commandCodec.decode bytes with
    | none => ["  invoke: noncanonical command"]
    | some command => s!"  invoke by subject {command.subject.value}, nonce {command.nonce}" ::
        command.targets.flatMap fun target =>
          s!"  writes cell {kindName target.kind} {target.target} (via capability {target.capability.value}; read at root {target.expectedTargetRoot.value})" ::
            match target.payload with
            | .scalar actions => actions.map (fun a => "    " ++ actionText a)
            | .content command => [s!"    content command ({(ContentResource.commandCodec.encode command).length} bytes)"]
  | .delegate bytes => match CapabilityDelegationController.commandCodec.decode bytes with
    | none => ["  delegate: noncanonical command"]
    | some ⟨kind, command⟩ =>
        let child := command.declaration.child
        [s!"  delegate by subject {command.subject.value} on {kindName kind} {command.declaration.target.value}",
         s!"  writes the authority cell: capability {child.id.value} for {holderText child.holder}, verbs {braces (verbNames child.scope.verbs)}, maxCost {child.scope.maxCost}, parent {child.parent.map (·.value) |>.getD 0}"]
  | .install subject control bytes =>
      [s!"  install a law by subject {subject.value} under control capability {control.value} ({bytes.length}-byte declaration)",
       "  writes the authority cell: the resource's policy revision"]
  | .revoke bytes => [s!"  revoke ({bytes.length}-byte command); writes the authority cell's revocation plane"]
  | .birth bytes capabilities => [s!"  birth ({bytes.length}-byte descriptor, {capabilities.length} source capabilities)"]

private def slotLines (entry : SigningSlot × Option SlotLegs) : List String :=
  match entry.2 with
  | none => [s!"  slot role {entry.1.role} index {entry.1.index}: header does not decode canonically"]
  | some legs =>
      s!"  slot role {entry.1.role} index {entry.1.index}: key {legs.header.keyId} epoch {legs.header.keyEpoch}, valid until height {legs.header.validUntil}, nullifier {legs.header.nullifier}" ::
        legs.reads.map fun read =>
          s!"    reads {addressText read.address}{if read.observed.isSome then "" else " (absent)"}"

private def slotJson (entry : SigningSlot × Option SlotLegs) : Json :=
  .mkObj <| [("role", decimal entry.1.role), ("index", decimal entry.1.index)] ++
    match entry.2 with
    | none => [("decoded", .bool false)]
    | some legs => [("decoded", .bool true), ("keyId", decimal legs.header.keyId),
        ("keyEpoch", decimal legs.header.keyEpoch), ("validUntil", decimal legs.header.validUntil),
        ("reads", .arr <| legs.reads.toArray.map fun read => .mkObj
          [("address", addressText read.address),
           ("canonical", hexText (PlanFootprintCodec.addressBytes CredentialAuthorityCell.wire read.address)),
           ("present", .bool read.observed.isSome)])]

/-- `turn` (what a plan would write; `outcome` absent) and `receipt` (a plan and
the Host's confirmed outcome for it). -/
def turnView (mode : String) (bytes : List UInt8) : Result Json := do
  let json ← input bytes
  let label ← str "input" json "label"
  let planBytes ← unhex "plan" (← str "input" json "plan")
  let some plan := signingPlanCodec.decode planBytes | throw "plan: not a SIGNING-PLAN/v4 frame"
  let outcome ← match ← optHex "input" json "outcome" with
    | none => pure none
    | some frame => some <$> decodeOutcome "outcome" frame
  let slots := turnSlots plan
  let head := if mode = "turn" then s!"turn {label}: what this command would do (nothing was submitted)"
    else s!"receipt {label}"
  let (receiptLines, receiptJson) := match outcome with
    | some (.confirmed kind receipt) =>
        let how := match kind with
          | .installed => "installed" | .recoveredAfterUncertainResponse => "recovered" | .replayed => "replayed"
        ([s!"  committed ({how}): receipt height {receipt.acceptedCount} (accepted entries through this turn), world root {receipt.worldRoot.value}",
          s!"  transaction {receipt.transactionId.value}"],
         Json.mkObj [("confirmation", how), ("height", decimal receipt.acceptedCount),
          ("worldRoot", decimal receipt.worldRoot.value), ("transactionId", decimal receipt.transactionId.value),
          ("eventId", decimal receipt.eventId.value)])
    | some other => ((explain other).1.map ("  " ++ ·), Json.mkObj (explain other).2)
    | none => (if mode = "turn" then ["  not submitted"] else ["  no outcome held for this attempt"], Json.null)
  let lines := head :: s!"  planned at plan height {plan.height} against world root {plan.worldRoot.value}" ::
    draftLines plan.finalizedDraft ++ slots.flatMap slotLines ++ receiptLines
  pure <| .mkObj [("type", mode), ("label", label), ("height", decimal plan.height),
    ("worldRoot", decimal plan.worldRoot.value),
    ("legs", .arr <| (draftLines plan.finalizedDraft).toArray.map Json.str),
    ("slots", .arr <| slots.toArray.map slotJson), ("outcome", receiptJson),
    ("text", "\n".intercalate lines)]

end Minidregg.Host.InspectRender
