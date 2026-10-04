/- A durable scratch world for the kernel activity (`Kernel.ObjectiveActivity`).

The world is one durable image (`Kernel.DurableReceiver.Image`: a seed and the
accepted intent records) in canonical bytes (`Compiler.DurableReceiverCodec`).
Every command is its own process: it recovers the image through the ONLY
recovery path (`DurableReceiverCodec.recover`, which replays every accepted
record through `DurableDataIntent.execute`), asks the kernel for one turn at
the current height (the number of accepted records), executes that turn's one
intent with the same executor, and appends it when it is accepted. A replayed
or refused intent appends nothing. Roots are the deployed cell roots
(`ResourceBirthCodec.rootBytes`).

What this world is not: there is no signature layer (a command's `--subject`
is the subject the kernel judges; in the native Host a signed command supplies
it), no Store binary, MAC chain or system tail law; fee accounts are the
kernel's own cells. It is the kernel, its codecs and the durable executor,
driven from a command line. -/
import Kernel.ObjectiveActivity
import Kernel.DurableReceiver
import Compiler.DurableReceiverCodec
import Compiler.ObjectiveBendDataWire
import Host.ObjectivePackageAuthor

namespace Minidregg.Host.ObjectiveActivityWorld
open Lean (Json toJson)
open Minidregg.Theory Minidregg.Compiler
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Theory.TypedAuthorization (Digest SubjectId)
open Minidregg.Kernel.DurableDataIntent
open Minidregg.Kernel.DurableReceiver
open Minidregg.Kernel.ObjectiveActivityWire
open Minidregg.Kernel.ObjectiveActivity
open Minidregg.Theory.ObjectiveBendDemandData (Data)
open Minidregg.Compiler.ObjectiveBendDataWire (dataJson)
set_option autoImplicit false

abbrev rootBytes : Bytes → Digest := ResourceBirthCodec.rootBytes

/-- The world's kernel configuration: the envelope ceiling, the patience
ceiling, the Plan extraction budget and the public tariff. -/
def config : Config where
  limits := ⟨100000, 100000⟩
  planBudget := ⟨10000, 100000, 1048576⟩
  maxTicks := 200000
  maxPatience := 16
  typeFuel := 16384
  maxArtifactBytes := 4194304
  tariff := ⟨10, 1⟩

def objectCell (name : String) : CellId :=
  tagged "DREGG/OBJECTIVE/ACTIVITY/WORLD-OBJECT/v1" name.toUTF8.toList

def clockCell : CellId := tagged "DREGG/OBJECTIVE/ACTIVITY/WORLD-CLOCK/v1" []

def digestText (digest : Digest) : String := toString digest.value
def digestJson (digest : Digest) : Json := toJson (digestText digest)

def parseDigest (text : String) : Except String Digest :=
  match text.toNat? with
  | some value => if toString value == text then .ok ⟨value⟩ else .error s!"noncanonical decimal {text}"
  | none => .error s!"not a decimal digest: {text}"

def parseNat (text : String) : Except String Nat :=
  match text.toNat? with
  | some value => .ok value
  | none => .error s!"not a natural: {text}"

/-! ## The image -/

def imagePath (world : System.FilePath) : System.FilePath := world / "image.bin"

def readImage (world : System.FilePath) : IO Image := do
  let bytes := (← IO.FS.readBinFile (imagePath world)).toList
  let some image := DurableReceiverCodec.decode bytes | throw (IO.userError "world image does not decode")
  pure image

def writeImage (world : System.FilePath) (image : Image) : IO Unit := do
  let temporary := world / "image.bin.tmp"
  IO.FS.writeBinFile temporary ⟨(DurableReceiverCodec.encode image).toArray⟩
  IO.FS.rename temporary (imagePath world)

def recover (world : System.FilePath) : IO (Image × Snapshot rootBytes) := do
  let bytes := (← IO.FS.readBinFile (imagePath world)).toList
  let some image := DurableReceiverCodec.decode bytes | throw (IO.userError "world image does not decode")
  let some snapshot := DurableReceiverCodec.recover rootBytes bytes
    | throw (IO.userError "world image does not replay through the durable executor")
  pure (image, snapshot)

def height (image : Image) : Nat := image.accepted.length

/-! ## Describing cells -/

def awaitJson (await : Await) : Json :=
  let source := match await.source with
    | .reply slot decider => Json.mkObj [("kind", toJson "reply"), ("slot", digestJson slot),
        ("slotCell", digestJson (Minidregg.Kernel.AnswerSlot.cell slot)), ("decider", toJson decider.value)]
    | .height due => Json.mkObj [("kind", toJson "height"), ("due", toJson due)]
  Json.mkObj [("id", digestJson await.id), ("source", source), ("deadline", toJson await.deadline),
    ("yieldedAt", toJson await.yieldedAt)]

def recordJson (record : Record) : Json :=
  let phase := match record.phase with
    | .awaiting await => Json.mkObj [("kind", toJson "awaiting"), ("await", awaitJson await)]
    | .done result => Json.mkObj [("kind", toJson "done"),
        ("result", match decodeDataBytes result with | some data => dataJson data | none => Json.null)]
    | .faulted reason => Json.mkObj [("kind", toJson "faulted"), ("reason", toJson reason)]
  Json.mkObj [("object", digestJson record.object), ("activity", digestJson record.activity),
    ("pin", digestJson record.pin), ("generation", toJson record.generation),
    ("checkpointBytes", toJson record.checkpoint.length),
    ("checkpointDigest", digestJson record.checkpointDigest),
    ("checkpointDecodes", toJson (decodeCheckpoint record.checkpoint).isSome),
    ("reads", Json.arr (record.reads.map fun guard =>
      Json.mkObj [("cell", digestJson guard.cellId), ("root", digestJson guard.expectedRoot)]).toArray),
    ("escrow", Json.mkObj [("payer", toJson record.escrow.payer.value),
      ("resumeTicks", toJson record.escrow.resumeTicks), ("timeoutTicks", toJson record.escrow.timeoutTicks),
      ("resumeFee", toJson record.escrow.resumeFee), ("timeoutFee", toJson record.escrow.timeoutFee)]),
    ("phase", phase)]

def decisionJson : Minidregg.Kernel.AnswerSlot.Decision → Json
  | .reply value => Json.mkObj [("kind", toJson "reply"),
      ("value", match decodeDataBytes value with | some data => dataJson data | none => Json.null)]
  | .refused reason => Json.mkObj [("kind", toJson "refused"), ("reason", toJson reason)]
  | .unknown => Json.mkObj [("kind", toJson "unknown")]
  | .broken reason => Json.mkObj [("kind", toJson "broken"), ("reason", toJson reason)]
  | .expired => Json.mkObj [("kind", toJson "expired")]

def slotJson (slot : Minidregg.Kernel.AnswerSlot.Slot) : Json :=
  Json.mkObj [("name", digestJson slot.name), ("activity", digestJson slot.activity),
    ("decider", toJson slot.decider.value), ("deadline", toJson slot.deadline),
    ("phase", match slot.phase with
      | .opened => toJson "open"
      | .decided decision when => Json.mkObj [("decision", decisionJson decision), ("height", toJson when)])]

def cellJson (snapshot : Snapshot rootBytes) (cell : CellId) : Json :=
  let bytes := snapshot.canonicalBytes cell
  let described : List (String × Json) :=
    match decodeRecord bytes with
    | some record => [("kind", toJson "activity-record"), ("record", recordJson record)]
    | none => match Minidregg.Kernel.AnswerSlot.decode bytes with
      | some slot => [("kind", toJson "answer-slot"), ("slot", slotJson slot)]
      | none => match decodeBalance bytes with
        | some balance => [("kind", toJson "fee-account"), ("balance", toJson balance)]
        | none => match ObjectiveBendSourceArtifact.decode bytes with
          | some artifact => [("kind", toJson "package"), ("declaration", toJson artifact.declaration)]
          | none => match decodeDataBytes bytes with
            | some data => [("kind", toJson "declared-state"), ("value", dataJson data)]
            | none => [("kind", toJson "opaque"), ("bytes", toJson bytes.length)]
  Json.mkObj ([("cell", digestJson cell), ("root", digestJson (snapshot.model.roots cell))] ++ described)

/-! ## Turn outcomes -/

/-- One line of `repr`, for transcripts. -/
def oneLine (text : String) : String :=
  String.intercalate " " ((text.splitOn "\n").map fun line => String.ofList (line.toList.dropWhile Char.isWhitespace))

def refusalJson (refusal : Minidregg.Kernel.ObjectiveActivity.Refusal) : Json :=
  Json.mkObj [("verdict", toJson "refused-by-kernel"), ("reason", toJson (oneLine (reprStr refusal)))]

def segmentJson : Segment → Json
  | .yielded state plan => Json.mkObj [("kind", toJson "yielded"),
      ("checkpointBytes", toJson (checkpointBytes state).length),
      ("plan", Json.mkObj [("state", dataJson plan.state), ("patience", toJson plan.patience),
        ("on", match plan.source with
          | .reply decider => Json.mkObj [("reply", toJson decider.value)]
          | .height due => Json.mkObj [("height", toJson due)])])]
  | .finished result => Json.mkObj [("kind", toJson "finished"), ("result", dataJson result)]
  | .faulted reason => Json.mkObj [("kind", toJson "faulted"), ("reason", toJson reason)]

/-- Execute one intent at the recovered snapshot and append it when accepted. -/
def commit (world : System.FilePath) (image : Image) (snapshot : Snapshot rootBytes)
    (intent : DataIntent rootBytes) (detail : List (String × Json)) : IO Json := do
  let base := [("height", toJson (height image)), ("transaction", digestJson intent.transactionId)] ++ detail
  match Minidregg.Kernel.DurableDataIntent.execute .complete snapshot intent with
  | .accepted _ =>
    writeImage world (image.append intent)
    -- Read back through the one recovery path: the appended image must replay.
    let (after, _) ← recover world
    pure (Json.mkObj ([("verdict", toJson "accepted"), ("heightAfter", toJson (height after))] ++ base))
  | .replayed _ =>
    pure (Json.mkObj ([("verdict", toJson "replayed"),
      ("note", toJson "the journal holds this exact intent; nothing was appended")] ++ base))
  | .rejected reason =>
    pure (Json.mkObj ([("verdict", toJson "rejected-by-durable-executor"), ("reason", toJson (oneLine (reprStr reason)))] ++ base))
  | .crashed _ _ => pure (Json.mkObj ([("verdict", toJson "crashed")] ++ base))

def saveIntent (path : System.FilePath) (intent : DataIntent rootBytes) : IO Unit :=
  IO.FS.writeBinFile path ⟨(DurableReceiverCodec.intentStream.encode (IntentRecord.ofIntent intent)).toArray⟩

def loadIntent (path : System.FilePath) : IO (DataIntent rootBytes) := do
  let bytes := (← IO.FS.readBinFile path).toList
  let some record := DurableReceiverCodec.intentStream.toLawful.decode bytes
    | throw (IO.userError "saved intent does not decode")
  let some intent := record.bind? rootBytes | throw (IO.userError "saved intent is not root-bound")
  pure intent

/-! ## Commands -/

structure Options where
  values : List (String × String)

def Options.parse : List String → Except String Options
  | [] => .ok ⟨[]⟩
  | key :: value :: rest =>
    if key.startsWith "--" then do
      let others ← Options.parse rest
      pure ⟨(String.ofList (key.toList.drop 2), value) :: others.values⟩
    else .error s!"expected --option, got {key}"
  | [key] => .error s!"option {key} needs a value"

def Options.get (options : Options) (key : String) : Except String String :=
  match options.values.lookup key with
  | some value => .ok value
  | none => .error s!"missing --{key}"

def Options.getD (options : Options) (key : String) (fallback : String) : String :=
  (options.values.lookup key).getD fallback

def Options.nat (options : Options) (key : String) : Except String Nat := do parseNat (← options.get key)
def Options.natD (options : Options) (key : String) (fallback : Nat) : Except String Nat :=
  match options.values.lookup key with
  | some text => parseNat text
  | none => .ok fallback
def Options.digest (options : Options) (key : String) : Except String Digest := do parseDigest (← options.get key)

def liftExcept {α : Type} (value : Except String α) : IO α :=
  match value with
  | .ok result => pure result
  | .error message => throw (IO.userError message)

def readJson (path : String) : IO Json := do
  liftExcept (Json.parse (← IO.FS.readFile path))

def readData (path : String) : IO Data := do
  liftExcept (ObjectiveBendDataWire.decodeData 64 (← readJson path))

/-- `genesis --world DIR --accounts SUBJECT:BALANCE,...` -/
def genesis (options : Options) : IO Json := do
  let world : System.FilePath := ← liftExcept (options.get "world")
  if ← (imagePath world).pathExists then throw (IO.userError "world exists")
  IO.FS.createDirAll world
  let accounts ← liftExcept <| (options.getD "accounts" "").splitOn "," |>.filter (· ≠ "") |>.mapM fun entry =>
    match entry.splitOn ":" with
    | [subject, balance] => do
      let subject ← parseNat subject
      let balance ← parseNat balance
      pure (accountCell ⟨subject⟩, balanceBytes balance)
    | _ => .error s!"account entry {entry} is not SUBJECT:BALANCE"
  let seed : Seed := ⟨[], (clockCell, balanceBytes 0) :: accounts, fun _ => 1000000000000⟩
  writeImage world ⟨seed, []⟩
  let (image, snapshot) ← recover world
  pure (Json.mkObj [("verdict", toJson "genesis"), ("height", toJson (height image)),
    ("cells", Json.arr ((image.cellIds.map (cellJson snapshot)).toArray))])

/-- `artifact --package-input P.json --core def.typed.json --out A.bin`: the
activity artifact of an elaborated definition (package identity, the selected
declaration, the canonical typed core, and the activity output codec). -/
def artifact (options : Options) : IO Json := do
  let input := (← IO.FS.readBinFile (← liftExcept (options.get "package-input"))).toList
  let core := (← IO.FS.readBinFile (← liftExcept (options.get "core"))).toList
  let some text := String.fromUTF8? ⟨input.toArray⟩ | throw (IO.userError "package input is not UTF-8")
  let package ← liftExcept (ObjectivePackageAuthor.load (← liftExcept (Json.parse text)))
  let canonical ← liftExcept (ObjectiveBendSourceArtifact.canonicalizePacket 4194304 core)
  let some declaration := ObjectiveSourcePackage.selectedDeclaration package
    | throw (IO.userError "selected declaration missing")
  let artifact : ObjectiveBendSourceArtifact.Artifact := ⟨ObjectiveSourcePackage.identity package, declaration,
    canonical, Minidregg.Kernel.ObjectiveBendNativeInput.codecId, codecId⟩
  let bytes := ObjectiveBendSourceArtifact.encode artifact
  IO.FS.writeBinFile (← liftExcept (options.get "out")) ⟨bytes.toArray⟩
  pure (Json.mkObj [("artifact", digestJson (ObjectiveBendSourceArtifact.identity artifact)),
    ("package", digestJson artifact.package), ("declaration", toJson declaration), ("bytes", toJson bytes.length)])

def subjectOf (options : Options) : Except String SubjectId := do pure ⟨← options.nat "subject"⟩

def publishCommand (options : Options) : IO Json := do
  let world : System.FilePath := ← liftExcept (options.get "world")
  let (image, snapshot) ← recover world
  let subject ← liftExcept (subjectOf options)
  let bytes := (← IO.FS.readBinFile (← liftExcept (options.get "artifact"))).toList
  match publish config snapshot subject bytes with
  | .error refusal => pure (refusalJson refusal)
  | .ok (pin, intent) => commit world image snapshot intent [("pin", digestJson pin),
      ("packageCell", digestJson (packageCell pin))]

def birthCommand (options : Options) : IO Json := do
  let world : System.FilePath := ← liftExcept (options.get "world")
  let (image, snapshot) ← recover world
  let request : BirthRequest := {
    subject := ← liftExcept (subjectOf options)
    object := objectCell (← liftExcept (options.get "object"))
    pin := ← liftExcept (options.digest "pin")
    input := ← readData (← liftExcept (options.get "input"))
    nonce := ← liftExcept (options.natD "nonce" 0)
    ticks := ← liftExcept (options.natD "ticks" 20000)
    resumeTicks := ← liftExcept (options.natD "resume-ticks" 20000)
    timeoutTicks := ← liftExcept (options.natD "timeout-ticks" 20000) }
  match birth config snapshot (height image) request with
  | .error refusal => pure (refusalJson refusal)
  | .ok born =>
    commit world image snapshot born.intent [("record", digestJson born.cell),
      ("object", digestJson request.object), ("segment", segmentJson born.segment),
      ("stored", recordJson born.record)]

def answerOf (options : Options) : IO Answer := do
  match options.values.lookup "reply" with
  | some path => pure (.reply (← readData path))
  | none => match options.values.lookup "refuse" with
    | some reason => pure (.refused reason)
    | none => match options.values.lookup "break" with
      | some reason => pure (.broken reason)
      | none => match options.values.lookup "unknown" with
        | some _ => pure .unknown
        | none => throw (IO.userError "resolve needs --reply FILE, --refuse REASON, --break REASON or --unknown yes")

def resolveCommand (options : Options) : IO Json := do
  let world : System.FilePath := ← liftExcept (options.get "world")
  let (image, snapshot) ← recover world
  let request : ResolveRequest := {
    subject := ← liftExcept (subjectOf options)
    slot := ← liftExcept (options.digest "slot")
    answer := ← answerOf options }
  match resolve config snapshot (height image) request with
  | .error refusal => pure (refusalJson refusal)
  | .ok resolution =>
    commit world image snapshot resolution.intent [("slot", slotJson resolution.decided)]

def deliverCommand (options : Options) : IO Json := do
  let world : System.FilePath := ← liftExcept (options.get "world")
  let (image, snapshot) ← recover world
  let request : DeliverRequest := {
    subject := ← liftExcept (subjectOf options)
    record := ← liftExcept (options.digest "record")
    extraTicks := ← liftExcept (options.natD "extra-ticks" 0) }
  match deliver config snapshot (height image) request with
  | .error refusal => pure (refusalJson refusal)
  | .ok delivery =>
    let detail : List (String × Json) := [("await", awaitJson delivery.await),
      ("path", toJson (reprStr delivery.settlement.path)),
      ("settled", toJson delivery.settlement.decided.label),
      ("stale", toJson (staleCount snapshot delivery.record.reads)),
      ("delivered", dataJson delivery.outcome.data), ("envelope", toJson delivery.envelope),
      ("refund", toJson (delivery.record.escrow.unused delivery.settlement.path)),
      ("segment", segmentJson delivery.segment), ("stored", recordJson delivery.next)]
    match options.values.lookup "save-intent" with
    | some path =>
      saveIntent path delivery.intent
      pure (Json.mkObj ([("verdict", toJson "prepared"), ("height", toJson (height image)),
        ("transaction", digestJson delivery.intent.transactionId), ("saved", toJson path)] ++ detail))
    | none => commit world image snapshot delivery.intent detail

/-- Submit a saved intent to the durable executor as it stands now. -/
def submitCommand (options : Options) : IO Json := do
  let world : System.FilePath := ← liftExcept (options.get "world")
  let (image, snapshot) ← recover world
  let intent ← loadIntent (← liftExcept (options.get "intent"))
  commit world image snapshot intent [("submitted", toJson (← liftExcept (options.get "intent")))]

/-- An intent that claims an await's nullifier and writes only the clock: a
second path to the same await that bypasses the record. The executor must
refuse it once the await was spent. -/
def claimCommand (options : Options) : IO Json := do
  let world : System.FilePath := ← liftExcept (options.get "world")
  let (image, snapshot) ← recover world
  let id ← liftExcept (options.digest "await")
  let transaction := tagged "DREGG/OBJECTIVE/ACTIVITY/WORLD/FORGED-CLAIM/v1" (digestStream.encode id)
  let intent := intentOf rootBytes transaction
    [⟨clockCell, snapshot.model.roots clockCell, balanceBytes (height image + 1)⟩] [] [awaitClaim id]
    (event "forged-claim" (digestStream.encode id)) none
  commit world image snapshot intent [("claims", digestJson id)]

/-- A raw durable write of an activity record whose checkpoint bytes were
altered (one byte) but whose digest and await id were kept: what a corrupted
or forged record cell looks like to the next delivery. The durable executor
accepts it (it judges roots, claims and guards, not meaning); the delivery
must refuse it. -/
def forgeCommand (options : Options) : IO Json := do
  let world : System.FilePath := ← liftExcept (options.get "world")
  let (image, snapshot) ← recover world
  let cell ← liftExcept (options.digest "record")
  let some record := decodeRecord (snapshot.canonicalBytes cell) | throw (IO.userError "no record")
  let tampered := match record.checkpoint.reverse with
    | last :: rest => (rest.reverse ++ [last + 1])
    | [] => [0]
  let forged := {record with checkpoint := tampered}
  let transaction := tagged "DREGG/OBJECTIVE/ACTIVITY/WORLD/FORGED-RECORD/v1" (digestStream.encode cell)
  let intent := intentOf rootBytes transaction
    [⟨cell, snapshot.model.roots cell, encodeRecord forged⟩] [] []
    (event "forged-record" (digestStream.encode cell)) none
  commit world image snapshot intent [("forged", toJson "checkpoint bytes altered, digest and await id kept")]

def writeStateCommand (options : Options) : IO Json := do
  let world : System.FilePath := ← liftExcept (options.get "world")
  let (image, snapshot) ← recover world
  let request : StateWriteRequest := {
    subject := ← liftExcept (subjectOf options)
    record := ← liftExcept (options.digest "record")
    value := ← readData (← liftExcept (options.get "value"))
    nonce := ← liftExcept (options.natD "nonce" 0) }
  match writeState snapshot request with
  | .error refusal => pure (refusalJson refusal)
  | .ok intent => commit world image snapshot intent []

/-- One accepted record that only advances the clock cell: heights pass. -/
def tickCommand (options : Options) : IO Json := do
  let world : System.FilePath := ← liftExcept (options.get "world")
  let (image, snapshot) ← recover world
  let transaction := tagged "DREGG/OBJECTIVE/ACTIVITY/WORLD/TICK/v1" (StreamCodec.nat.encode (height image))
  let intent := intentOf rootBytes transaction
    [⟨clockCell, snapshot.model.roots clockCell, balanceBytes (height image + 1)⟩] [] []
    (event "tick" (StreamCodec.nat.encode (height image))) none
  commit world image snapshot intent []

def showCommand (options : Options) : IO Json := do
  let world : System.FilePath := ← liftExcept (options.get "world")
  let (image, snapshot) ← recover world
  match options.values.lookup "cell", options.values.lookup "account" with
  | some text, _ => pure (cellJson snapshot (← liftExcept (parseDigest text)))
  | none, some subject => pure (cellJson snapshot (accountCell ⟨← liftExcept (parseNat subject)⟩))
  | none, none => pure (Json.mkObj [("height", toJson (height image)),
      ("cells", Json.arr ((image.cellIds.map (cellJson snapshot)).toArray))])

def run : List String → IO Json
  | "genesis" :: rest => do genesis (← liftExcept (Options.parse rest))
  | "artifact" :: rest => do artifact (← liftExcept (Options.parse rest))
  | "publish" :: rest => do publishCommand (← liftExcept (Options.parse rest))
  | "birth" :: rest => do birthCommand (← liftExcept (Options.parse rest))
  | "resolve" :: rest => do resolveCommand (← liftExcept (Options.parse rest))
  | "deliver" :: rest => do deliverCommand (← liftExcept (Options.parse rest))
  | "submit" :: rest => do submitCommand (← liftExcept (Options.parse rest))
  | "claim" :: rest => do claimCommand (← liftExcept (Options.parse rest))
  | "write-state" :: rest => do writeStateCommand (← liftExcept (Options.parse rest))
  | "forge-record" :: rest => do forgeCommand (← liftExcept (Options.parse rest))
  | "tick" :: rest => do tickCommand (← liftExcept (Options.parse rest))
  | "show" :: rest => do showCommand (← liftExcept (Options.parse rest))
  | _ => throw (IO.userError
      "usage: objective-activity-world (genesis|artifact|publish|birth|resolve|deliver|submit|claim|write-state|forge-record|tick|show) --option value ...")

def main (arguments : List String) : IO UInt32 := do
  try
    let output ← run arguments
    IO.println output.compress
    return 0
  catch error =>
    IO.eprintln (Json.mkObj [("error", toJson error.toString)]).compress
    return 2

end Minidregg.Host.ObjectiveActivityWorld
