/-
# Host.FnArchivePublisher — Mini's finalized history posted to fn, read back, followed

`minidregg-host PINNED.json fn-archive VERB ...`:

* `publish ARCHIVE.json FIRST FINALIZED|- KEYS.json|- RESULT.json` bundles the
  committed (and, in a committee domain, finalized) heights `[FIRST, FIRST+k)`,
  renders the article (`Kernel.FnArchive`), charges the non-refundable archive
  fee, persists the signed article in the archive journal under the Store's
  anchor BEFORE the first send, and posts the persisted bytes through fn's
  control socket (`hybrid-author`), never NNTP POST (N10). With `-` for keys
  only persisted bytes can be sent: a resend never re-signs (N2).
* `lookup ARCHIVE.json MSGID RESULT.json` resolves `Unknown` and reads back:
  `ARTICLE <msgid>`, the served article verified by fn's native verifier under
  Mini's pinned keys, the authored source extracted against the identity Mini
  recorded (`FnArchiveJournal.readBack`); `430 withdrawn` is reported as
  withdrawn, never as absent.
* `reconcile ARCHIVE.json RESULT.json [lookup]` lists every acknowledged
  identity recovered from the journal after reopen, the pending (`Unknown`)
  ones, and with `lookup` what fn serves for each acknowledged one.
* `follow ARCHIVE.json CURSOR RESULT.json` advances a follower's cursor past one
  verified acknowledged bundle, or holds it with a named refusal.
* `fund ARCHIVE.json AMOUNT TXID EVENTID RESULT.json` credits archive funding
  against a transaction this Store accepted.

fn's transport outcome is the journal's (the sender's outbox); nothing here
writes an answer slot.
-/
import Kernel.FnArchiveJournal
import Kernel.NativeHost
import Host.FnOutcome
import Std.Internal.Async.TCP

namespace Minidregg.Host.FnArchivePublisher

open Minidregg.Theory.TypedAuthorization
open Minidregg.Compiler
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Kernel
open Minidregg.Kernel.FnArchive
open Minidregg.Kernel.FnArchiveJournal

set_option autoImplicit false

/-! ## fn's answer to a post, as Mini reads it (requirements §3.5) -/

inductive PostOutcome where
  | acknowledged (basis : Basis)
  | conflict
  | transient (word : String)
  | awaitsFunding (word : String)
  | refused (word : String)
  | unknown (detail : String)
  | miniDefect
  deriving DecidableEq, Repr

def PostOutcome.word : PostOutcome → String
  | .acknowledged .duplicate => "acknowledged-duplicate"
  | .acknowledged _ => "acknowledged"
  | .conflict => "conflict"
  | .transient w => s!"transient {w}"
  | .awaitsFunding w => s!"awaits-funding {w}"
  | .refused w => s!"refused {w}"
  | .unknown d => s!"unknown ({d})"
  | .miniDefect => "mini-defect (fn answered usage)"

/-- fn's transient refusals: retry the same bytes. -/
def transientWords : List String := ["BUSY", "CLOCK-UNUSABLE", "NO-OWNER"]

/-- A budget refusal word becomes `AwaitsFunding` (fn's tariff words). -/
def budgetWord (word : String) : Bool :=
  word.startsWith "BUDGET" || word.startsWith "TARIFF" || word.startsWith "RESOURCE"

/-- fn's exit 1 with its reason word. `resend` is true for every send of
bytes persisted before this attempt: after a possible earlier landing, a
refusal other than `conflict` or a transient word may be fn refusing a resend
of an accepted article (a revoked enrolment), so it stays `Unknown`. -/
def classifyRefusal (word : Option String) (resend : Bool) : PostOutcome :=
  match word with
  | none => if resend then .unknown "refused without a reason word on a resend" else .refused "-"
  | some w =>
      if w = "CONFLICT" then .conflict
      else if transientWords.contains w then .transient w
      else if resend then .unknown s!"refused {w} on a resend; the original may have landed"
      else if budgetWord w then .awaitsFunding w
      else .refused w

def classifyPost (code : Nat) (word : Option String) (resend : Bool) : PostOutcome :=
  match FnOutcome.classify code with
  | some .accepted => .acknowledged (if word == some "DUPLICATE" then .duplicate else .accepted)
  | some .refused => classifyRefusal word resend
  | some .notConnected => .transient "not-connected"
  | some .usage => .miniDefect
  | some c => .unknown c.word
  | none => .unknown s!"exit {code} is no fn outcome class"

theorem classifyRefusal_not_acknowledged (word : Option String) (resend : Bool) (basis : Basis) :
    classifyRefusal word resend ≠ .acknowledged basis := by
  unfold classifyRefusal
  cases word with
  | none => cases resend <;> simp
  | some w => simp only; split_ifs <;> simp

/-- Acknowledged exactly when fn exited 0. -/
theorem classifyPost_acknowledged_iff {code : Nat} {word : Option String} {resend : Bool} :
    (∃ basis, classifyPost code word resend = .acknowledged basis) ↔ code = 0 := by
  constructor
  · rintro ⟨basis, h⟩
    unfold classifyPost at h
    cases hc : FnOutcome.classify code with
    | none => simp [hc] at h
    | some c =>
        have e := FnOutcome.classify_eq_some hc
        cases c
        · exact e
        · simp only [hc] at h; exact absurd h (classifyRefusal_not_acknowledged _ _ _)
        all_goals simp [hc, FnOutcome.Class.word] at h
  · intro zero; subst zero; exact ⟨_, rfl⟩

/-- A definite refusal (conflict, refused, awaits-funding) is only ever fn's
exit 1 refusal: an answer under which fn did not act. -/
theorem classifyPost_definite_is_refusal {code : Nat} {word : Option String} {resend : Bool}
    (definite : classifyPost code word resend = .conflict ∨
      (∃ w, classifyPost code word resend = .refused w) ∨
      (∃ w, classifyPost code word resend = .awaitsFunding w)) :
    FnOutcome.classify code = some .refused ∧ FnOutcome.mayHaveActed code = false := by
  have refusal : FnOutcome.classify code = some .refused := by
    unfold classifyPost at definite
    cases hc : FnOutcome.classify code with
    | none => simp [hc] at definite
    | some c => cases c <;> simp_all [FnOutcome.Class.word]
  exact ⟨refusal, FnOutcome.mayHaveActed_false_iff.mpr (.inl refusal)⟩

/-- On a resend, exit 1 is never a definite refusal unless fn named the
conflict or a transient word: the original may have landed. -/
theorem classifyPost_resend_refusal_unknown {word : String}
    (notConflict : word ≠ "CONFLICT") (notTransient : transientWords.contains word = false) :
    ∃ detail, classifyPost 1 (some word) true = .unknown detail := by
  have absent : word ∉ transientWords := by simpa using notTransient
  exact ⟨s!"refused {word} on a resend; the original may have landed", by
    simp [classifyPost, FnOutcome.classify, classifyRefusal, notConflict, absent]⟩

theorem classifyPost_samples :
    classifyPost 0 (some "ACCEPTED") false = .acknowledged .accepted ∧
    classifyPost 0 (some "DUPLICATE") true = .acknowledged .duplicate ∧
    classifyPost 1 (some "CONFLICT") false = .conflict ∧
    classifyPost 1 (some "BUSY") true = .transient "BUSY" ∧
    classifyPost 3 (some "UNCERTAIN") false = .unknown "uncertain" ∧
    classifyPost 4 none false = .unknown "fault" ∧
    classifyPost 5 none false = .miniDefect ∧
    classifyPost 7 none false = .transient "not-connected" ∧
    classifyPost 1 (some "AUTHOR-NOT-ENROLLED") false = .refused "AUTHOR-NOT-ENROLLED" := by
  decide +kernel

/-- The journal event a post outcome records; transient and unknown record
nothing (the slot stays pending and the same bytes are resent or looked up). -/
def PostOutcome.event (outcome : PostOutcome) (signed : Signed) (pin : List UInt8) :
    Option Event :=
  match outcome with
  | .acknowledged basis => some (.acknowledged ⟨signed.messageId, signed.identity, pin, basis⟩)
  | .conflict => some (.conflicted signed.messageId)
  | .refused w | .awaitsFunding w => some (.refused signed.messageId w)
  | .transient _ | .unknown _ | .miniDefect => none

#assert_axioms classifyRefusal_not_acknowledged classifyPost_acknowledged_iff classifyPost_definite_is_refusal
  classifyPost_resend_refusal_unknown classifyPost_samples

/-! ## Configuration -/

structure FnSide where
  control : String
  generation : Nat
  mlPublicPem : String
  nntpPort : Nat
  /-- The fn pin recorded with each acknowledgement (running image digest and
  the store identity fields Mini pins), opaque. -/
  pin : List UInt8

structure ArchiveConfig where
  profile : Profile
  fn : FnSide
  tariff : Tariff
  /-- Who receives the archive fee: QE-6, a configured parameter with no
  default. Absent, every publication is refused. -/
  recipient : Option String

private def need {α : Type} (label : String) : Option α → IO α
  | some value => pure value
  | none => throw (IO.userError s!"fn archive config: {label}")

private def natAt (json : Lean.Json) (key : String) : IO Nat :=
  need s!"{key} must be a natural number" ((json.getObjValAs? Nat key).toOption)

private def strAt (json : Lean.Json) (key : String) : IO String :=
  need s!"{key} must be a string" ((json.getObjValAs? String key).toOption)

def hexDecode (text : String) : Option (List UInt8) :=
  let digit (c : Char) : Option Nat :=
    if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
    else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10) else none
  let rec go : List Char → Option (List UInt8)
    | [] => some []
    | a :: b :: rest => do
        let hi ← digit a; let lo ← digit b
        pure (UInt8.ofNat (hi * 16 + lo) :: (← go rest))
    | [_] => none
  go text.toList

def loadConfig (path : String) : IO ArchiveConfig := do
  let json ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile path))
  let profile ← need "profile" (json.getObjVal? "profile").toOption
  let fn ← need "fn" (json.getObjVal? "fn").toOption
  let fee ← need "fee" (json.getObjVal? "fee").toOption
  let creation : FnReplyPublication.CreationContext :=
    ⟨← strAt profile "fromMailbox", ← strAt profile "newsgroup",
      ← strAt profile "messageIdDomain", ← strAt profile "date"⟩
  let profileValue : Profile :=
    ⟨creation, ← natAt profile "k", ← natAt profile "maxBlockOctets",
      ← natAt profile "articleBound",
      ((profile.getObjValAs? Nat "pageBudget").toOption.getD defaultPageBudget),
      ((profile.getObjValAs? Nat "carrierOverhead").toOption.getD defaultCarrierOverhead)⟩
  match profileValue.check with
  | .error refusal => throw (IO.userError s!"fn archive profile refused: {refusal.word}")
  | .ok () => pure ()
  let pin ← need "fn.pin must be lowercase hex" (hexDecode (← strAt fn "pin"))
  let recipient := match fee.getObjVal? "recipient" with
    | .ok (.str value) => if value.isEmpty then none else some value
    | _ => none
  pure ⟨profileValue,
    ⟨← strAt fn "control", ← natAt fn "generation", ← strAt fn "mlPublicPem",
      ← natAt fn "nntpPort", pin⟩,
    ⟨← natAt fee "perOctet", ← natAt fee "perTransaction"⟩, recipient⟩

/-- The signing key paths of one publication; never persisted by Mini. -/
structure Keys where
  principal : String
  edPublic : String
  edSecret : String
  mlPublic : String
  mlSecret : String

def loadKeys (path : String) : IO (Option Keys) := do
  if path == "-" then return none
  let json ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile path))
  pure (some ⟨← strAt json "principal", ← strAt json "edPublic", ← strAt json "edSecret",
    ← strAt json "mlPublic", ← strAt json "mlSecret"⟩)

/-- The fn-facing helpers the Host already has (`Host/Main.lean`): local fn
invocation with a drained stderr prefix, the hybrid signer, and the native
verifier under Mini's independent key pin. Their text decoding is FN-WIRE's
to replace; this module never parses fn's CLI text itself beyond
`FnOutcome.authorAnswer`. -/
structure Ops where
  runFn : Array String → IO (Nat × List UInt8 × ByteArray)
  sign : Keys → String → IO (List UInt8 × List UInt8)
  /-- Carrier path → the exact authored source, signatures checked under the pin. -/
  verifySource : String → IO (List UInt8)

/-! ## The archive journal under the Store's anchor -/

/-- The Store helper configured exactly as the Host's physical transport. -/
def storage (config : NativeHost.Config) : DurableReceiverIO.NativeConfig :=
  { config.storage with anchorIdentity :=
    s!"domain:{config.deployment.domain.value};semantics:{config.profile.semantics.value};seed:{config.expectedSeed.value}" }

/-- The journal's helper is the one the durable log's reads go through. -/
theorem storage_read (config : NativeHost.Config) :
    config.physicalTransport.read = (storage config).read := rfl

private def u64At (bytes : ByteArray) (position : Nat) : Option Nat :=
  if position + 8 ≤ bytes.size then
    some <| (List.range 8).foldl (fun value index => value * 256 + (bytes.get! (position + index)).toNat) 0
  else none

private def blobAt (bytes : ByteArray) (position : Nat) : Option (List UInt8 × Nat) := do
  let length ← u64At bytes position
  let start := position + 8
  if start + length ≤ bytes.size then
    some ((bytes.extract start (start + length)).toList, start + length)
  else none

private def entriesAt (bytes : ByteArray) :
    Nat → Nat → Nat → List (List UInt8 × List UInt8) → Option (List (List UInt8 × List UInt8))
  | 0, position, _, acc => if position = bytes.size then some acc.reverse else none
  | count + 1, position, expected, acc => do
      let seq ← u64At bytes position
      if seq ≠ expected then none else
      let (record, afterRecord) ← blobAt bytes (position + 8)
      let (tag, afterTag) ← blobAt bytes afterRecord
      entriesAt bytes count afterTag (expected + 1) ((record, tag) :: acc)

/-- `journal-read`'s file: head, count, then `(seq, record, tag)` from seq 1. -/
def parseJournal (bytes : ByteArray) : Option (List (List UInt8 × List UInt8)) := do
  let head ← u64At bytes 0
  let count ← u64At bytes 8
  if count ≠ head then none else entriesAt bytes count 16 1 []

structure Journal where
  state : State
  chain : Digest
  count : Nat

def readJournal (config : NativeHost.Config) : IO Journal := do
  let key ← IO.ofExcept (← config.storage.readKey)
  IO.FS.withTempDir fun directory => do
    let path := directory / "journal.bin"
    let output ← DurableReceiverIO.runNative (storage config)
      #["journal-read", config.storage.root.toString, "1", path.toString]
    unless output.exitCode == 0 && output.stderr == "" do
      throw (IO.userError s!"fn archive journal read failed (exit {output.exitCode}): {output.stderr}")
    let some entries := parseJournal (← IO.FS.readBinFile path)
      | throw (IO.userError "fn archive journal read is malformed")
    let start := journalStart config.deployment.domain config.profile.semantics config.expectedSeed
    match load key start entries with
    | .ok (state, chain) => pure ⟨state, chain, entries.length⟩
    | .error refusal => throw (IO.userError refusal.word)

/-- Append one event at the journal head, then re-read: the event is
installed only if the reopened journal replays to the expected state. -/
def appendEvent (config : NativeHost.Config) (journal : Journal) (event : Event) : IO Journal := do
  let expected ← match apply journal.state event with
    | .ok next => pure next
    | .error refusal => throw (IO.userError refusal.word)
  let key ← IO.ofExcept (← config.storage.readKey)
  let seq := journal.count + 1
  let (record, tag) := nextEntry key seq journal.chain event
  let observed ← IO.FS.withTempDir fun directory => do
    let recordPath := directory / "record.bin"
    let tagPath := directory / "tag.bin"
    IO.FS.writeBinFile recordPath record.toByteArray
    IO.FS.writeBinFile tagPath tag.toByteArray
    pure (DurableReceiverIO.parseCasOutput (← DurableReceiverIO.runNative (storage config)
      #["journal-append", config.storage.root.toString, toString seq,
        recordPath.toString, tagPath.toString]))
  match observed with
  | .conflict => throw (IO.userError s!"fn archive journal moved under seq {seq}: another writer")
  | _ => pure ()
  let reopened ← readJournal config
  unless reopened.count == seq && reopened.state == expected do
    throw (IO.userError s!"fn archive journal append at seq {seq} is uncertain: the reopened journal differs")
  pure reopened

/-! ## Mini's side: the finalized bundle -/

/-- The output gate (N6): only committed heights, and in a committee domain
only heights the operator states final; bundles are aligned to `k`. -/
def gate (profile : Profile) (committed : Nat) (committee : Bool) (finalized : Option Nat)
    (first : Nat) : Except String Nat := do
  unless 1 ≤ first ∧ (first - 1) % profile.k = 0 do
    throw s!"archive bundles start at 1 + j*k (k = {profile.k}); {first} is not a bundle start"
  let last := first + profile.k - 1
  unless last ≤ committed do throw s!"heights through {last} are not committed (head {committed})"
  if committee then
    let some final := finalized
      | throw "a committee domain publishes only final heights: state the finalized height"
    unless last ≤ final do throw s!"heights through {last} are not final (final {final})"
  pure last

def bundleAt (config : NativeHost.Config) (opened : NativeHost.Opened config) (first last : Nat) :
    Except String Bundle := do
  let accepted := opened.durable.image.accepted
  let blocks ← (List.range (last + 1 - first)).mapM fun offset => do
    let index := first - 1 + offset
    let some record := accepted[index]? | throw s!"height {index + 1} is not in the Store"
    let some receipt := NativeHost.historicalReceipt config opened.durable
        record.transactionId record.event.eventId
      | throw s!"height {index + 1} has no sealed receipt"
    pure (⟨DurableCheckpointCodec.recordFrame.encode record, receipt⟩ : Block)
  pure ⟨config.deployment.domain, config.profile.semantics, first, blocks⟩

/-! ## NNTP `ARTICLE` (fn's served bytes; no POST ever) -/

open Std.Internal.IO.Async in
private partial def recvUntil (client : TCP.Socket.Client) (acc : ByteArray) (limit : Nat)
    (done : ByteArray → Bool) : Async ByteArray := do
  if done acc then return acc
  if acc.size > limit then throw (IO.userError "fn NNTP answer exceeds bound")
  match ← client.recv? 65536 with
  | none => return acc
  | some chunk => recvUntil client (acc ++ chunk) limit done

private def endsWith (bytes : ByteArray) (suffix : List UInt8) : Bool :=
  bytes.size ≥ suffix.length && bytes.toList.drop (bytes.size - suffix.length) == suffix

private def lineEnd (bytes : List UInt8) : Option Nat :=
  (bytes.zip (bytes.drop 1)).findIdx? fun (a, b) => a == 13 && b == 10

/-- Undo NNTP dot-stuffing of a multi-line block (without its `.` line). -/
private def unstuff (lines : List (List UInt8)) : List UInt8 :=
  (lines.map fun line => match line with
    | 46 :: 46 :: rest => 46 :: rest
    | other => other).foldr (fun line acc => line ++ [13, 10] ++ acc) []

private def splitCrlfAux : List UInt8 → List UInt8 → List (List UInt8)
  | [], current => if current = [] then [] else [current.reverse]
  | 13 :: 10 :: rest, current => current.reverse :: splitCrlfAux rest []
  | b :: rest, current => splitCrlfAux rest (b :: current)

private def splitCrlf (bytes : List UInt8) : List (List UInt8) := splitCrlfAux bytes []

open Std.Internal.IO.Async in
/-- One `ARTICLE <msgid>` on the loopback listener. -/
def fetchArticle (port : Nat) (messageIdText : String) (limit : Nat) : IO Served := do
  let raw : ByteArray ← (do
    let client ← TCP.Socket.Client.mk
    client.connect (.v4 ⟨Std.Net.IPv4Addr.ofParts 127 0 0 1, port.toUInt16⟩)
    let greeting ← recvUntil client .empty 4096 (fun b => (lineEnd b.toList).isSome)
    unless greeting.toList.take 3 == "200".toUTF8.toList || greeting.toList.take 3 == "201".toUTF8.toList do
      throw (IO.userError "fn NNTP listener did not greet")
    client.send ("ARTICLE " ++ messageIdText ++ "\r\n").toUTF8
    let answer ← recvUntil client .empty limit fun b =>
      match lineEnd b.toList with
      | none => false
      | some _ =>
          if b.toList.take 4 == "220 ".toUTF8.toList then endsWith b [13, 10, 46, 13, 10]
          else true
    client.send "QUIT\r\n".toUTF8
    pure answer : Async ByteArray).block
  let bytes := raw.toList
  let some i := lineEnd bytes | throw (IO.userError "fn NNTP answer has no status line")
  let status := bytes.take i
  if status == "430 withdrawn".toUTF8.toList then return .withdrawn
  if status == "430 no article with that message-id".toUTF8.toList then return .absent
  if status == "430 article reclaimed".toUTF8.toList then return .reclaimed
  unless status.take 4 == "220 ".toUTF8.toList do
    throw (IO.userError s!"fn ARTICLE answered {String.fromUTF8! status.toByteArray}")
  let body := splitCrlf (bytes.drop (i + 2))
  -- the block ends with the "." line
  let some last := body.getLast? | throw (IO.userError "fn ARTICLE block is empty")
  unless last == [46] do throw (IO.userError "fn ARTICLE block is not terminated")
  return .article (unstuff body.dropLast)

/-- `fetchArticle`, then fn's native verifier over the served article (the
carrier) under Mini's pinned keys, which yields the exact authored source. -/
def fetchServed (ops : Ops) (archive : ArchiveConfig) (messageIdText : String) : IO Served := do
  match ← fetchArticle archive.fn.nntpPort messageIdText (archive.profile.sourceBound + 2 * archive.profile.carrierOverhead) with
  | .article served =>
      IO.FS.withTempDir fun directory => do
        let path := directory / "served.eml"
        IO.FS.writeBinFile path served.toByteArray
        pure (.article (← ops.verifySource path.toString))
  | other => pure other

/-! ## Verbs -/

private def digestHex (digest : Digest) : String :=
  FnReplyPublication.hexBytes (digestStream.encode digest)

private def identityJson (id : Identity) : Lean.Json :=
  Lean.Json.mkObj [("first", Lean.toJson id.first), ("last", Lean.toJson id.last),
    ("bundleDigest", Lean.toJson (digestHex id.digest))]

private def writeResult (path : String) (fields : List (String × Lean.Json)) : IO Unit :=
  IO.FS.writeFile path (Lean.Json.mkObj fields).pretty

/-- Post the persisted bytes once and record fn's answer. -/
def send (config : NativeHost.Config) (ops : Ops) (archive : ArchiveConfig) (journal : Journal)
    (signed : Signed) (resend : Bool) : IO (Journal × PostOutcome × Nat × Option String) := do
  let (code, _, stderr) ← IO.FS.withTempDir fun directory => do
    let sourcePath := directory / "source.eml"
    let edPath := directory / "ed.sig"
    let mlPath := directory / "ml.sig"
    IO.FS.writeBinFile sourcePath signed.source.toByteArray
    IO.FS.writeBinFile edPath signed.edSignature.toByteArray
    IO.FS.writeBinFile mlPath signed.mlSignature.toByteArray
    ops.runFn #["hybrid-author", archive.fn.control, toString archive.fn.generation,
      sourcePath.toString, edPath.toString, mlPath.toString, archive.fn.mlPublicPem]
  let word := (FnOutcome.authorAnswer stderr.toList).map fun (_, w) =>
    String.fromUTF8! w.toByteArray
  let outcome := classifyPost code word resend
  let answered := match journal.state.lookup signed.messageId with
    | some slot => slot.ack.isSome || slot.terminal.isSome
    | none => false
  let journal ← match outcome.event signed archive.fn.pin, answered with
    | some event, false => appendEvent config journal event
    | _, _ => pure journal
  pure (journal, outcome, code, word)

def publish (config : NativeHost.Config) (ops : Ops) (archivePath firstText finalizedText keysPath
    resultPath : String) : IO UInt32 := do
  let archive ← loadConfig archivePath
  let some first := firstText.toNat? | throw (IO.userError "FIRST must be a decimal height")
  let finalized := if finalizedText == "-" then none else finalizedText.toNat?
  let opened ← IO.ofExcept (← NativeHost.openExisting config)
  let committed := opened.durable.image.accepted.length
  let last ← IO.ofExcept (gate archive.profile committed config.jointConsensus.isSome finalized first)
  let bundle ← IO.ofExcept (bundleAt config opened first last)
  let source ← match render archive.profile bundle with
    | .ok bytes => pure bytes
    | .error refusal => throw (IO.userError refusal.word)
  let messageIdText := messageId archive.profile bundle
  let charge := fee archive.tariff archive.profile source
  let mut journal ← readJournal config
  let mut resend := true
  match journal.state.lookup messageIdText with
  | some slot =>
      if slot.ack.isSome || slot.terminal.isSome then
        writeResult resultPath [("type", "fn-archive-publish-v1"), ("messageId", Lean.toJson messageIdText),
          ("outcome", Lean.toJson (if slot.ack.isSome then "already-acknowledged" else "already-answered")),
          ("identity", identityJson slot.signed.identity)]
        return 0
  | none =>
      let some _ := archive.recipient
        | throw (IO.userError "archive fee recipient is not configured (QE-6); publication refused before signing")
      unless charge ≤ available journal.state do
        throw (IO.userError (Refusal.unfunded charge (available journal.state)).word)
      let some keys ← loadKeys keysPath
        | throw (IO.userError s!"{messageIdText} has no persisted signed article and no signing keys were given")
      let sourcePath ← IO.FS.withTempDir fun directory => do
        let path := directory / "source.eml"
        IO.FS.writeBinFile path source.toByteArray
        let signatures ← ops.sign keys path.toString
        pure signatures
      let (ed, ml) := sourcePath
      unless ed.length == 64 && ml.length == 3309 do
        throw (IO.userError "fn hybrid signer returned signatures of the wrong width")
      let signed : Signed := ⟨bundle.identity, messageIdText, source, ed, ml, charge⟩
      journal ← appendEvent config journal (.signed signed)
      resend := false
  let some signed := sendable journal.state messageIdText
    | throw (IO.userError "fn archive journal holds no sendable bytes after persisting")
  let (_, outcome, code, word) ← send config ops archive journal signed resend
  writeResult resultPath [("type", "fn-archive-publish-v1"), ("messageId", Lean.toJson messageIdText),
    ("identity", identityJson signed.identity), ("fee", Lean.toJson signed.fee),
    ("resend", Lean.toJson resend), ("exit", Lean.toJson code),
    ("word", Lean.toJson (word.getD "-")), ("outcome", Lean.toJson outcome.word),
    ("sourceOctets", Lean.toJson signed.source.length)]
  pure (match outcome with
    | .acknowledged _ => 0 | .transient _ | .unknown _ => 3 | .miniDefect => 5 | _ => 1)

/-- Send the persisted bytes of a Message-ID again, whatever its state (an
answered slot records nothing new). No keys are read: a resend is the
persisted artifact byte for byte (N2). -/
def resendPersisted (config : NativeHost.Config) (ops : Ops) (archivePath messageIdText resultPath : String) :
    IO UInt32 := do
  let archive ← loadConfig archivePath
  let journal ← readJournal config
  let some slot := journal.state.lookup messageIdText
    | throw (IO.userError s!"{messageIdText} has no persisted signed article")
  let (_, outcome, code, word) ← send config ops archive journal slot.signed true
  writeResult resultPath [("type", "fn-archive-resend-v1"), ("messageId", Lean.toJson messageIdText),
    ("identity", identityJson slot.signed.identity), ("exit", Lean.toJson code),
    ("word", Lean.toJson (word.getD "-")), ("outcome", Lean.toJson outcome.word)]
  pure (match outcome with
    | .acknowledged _ => 0 | .transient _ | .unknown _ => 3 | .miniDefect => 5 | _ => 1)

def lookup (config : NativeHost.Config) (ops : Ops) (archivePath messageIdText resultPath : String) :
    IO UInt32 := do
  let archive ← loadConfig archivePath
  let journal ← readJournal config
  let some slot := journal.state.lookup messageIdText
    | throw (IO.userError s!"{messageIdText} is not in this Store's archive journal")
  let served ← fetchServed ops archive messageIdText
  let outcome := readBack archive.profile messageIdText served
  let recorded ← match outcome with
    | .verified bundle =>
        if bundle.identity == slot.signed.identity then
          if slot.ack.isNone then
            discard <| appendEvent config journal
              (.acknowledged ⟨messageIdText, slot.signed.identity, archive.fn.pin, .lookup⟩)
            pure "acknowledged-by-lookup"
          else pure "verified"
        else pure "identity-differs"
    | .withdrawn =>
        if slot.withdrawn then pure "withdrawn" else do
          discard <| appendEvent config journal (.withdrawn messageIdText); pure "withdrawn"
    | .absent => pure (if slot.ack.isSome then "absent-after-acknowledgement: evidence against fn"
        else "absent: resend the same bytes")
    | .reclaimed => pure "reclaimed: evidence against fn (PRF-088)"
    | .refused refusal => pure s!"refused: {refusal.word}"
  writeResult resultPath [("type", "fn-archive-lookup-v1"), ("messageId", Lean.toJson messageIdText),
    ("readBack", Lean.toJson outcome.word), ("recorded", Lean.toJson recorded),
    ("identity", identityJson slot.signed.identity)]
  pure (match outcome with | .verified _ => 0 | .withdrawn => 2 | .absent => 3 | _ => 1)

def reconcile (config : NativeHost.Config) (ops : Ops) (archivePath resultPath : String)
    (withLookup : Bool) : IO UInt32 := do
  let archive ← loadConfig archivePath
  let journal ← readJournal config
  let mut rows : Array Lean.Json := #[]
  for slot in acknowledged journal.state do
    let served ← if withLookup then
        some <$> (readBack archive.profile slot.signed.messageId <$>
          fetchServed ops archive slot.signed.messageId)
      else pure none
    rows := rows.push (Lean.Json.mkObj [("messageId", Lean.toJson slot.signed.messageId),
      ("identity", identityJson slot.signed.identity),
      ("withdrawn", Lean.toJson slot.withdrawn),
      ("readBack", Lean.toJson ((served.map ReadBack.word).getD "-"))])
  let pendingRows := (pending journal.state).map fun s =>
    Lean.Json.mkObj [("messageId", Lean.toJson s.messageId), ("identity", identityJson s.identity),
      ("status", Lean.toJson "unknown: resolve by lookup or a same-bytes resend")]
  writeResult resultPath [("type", "fn-archive-reconcile-v1"),
    ("journalEntries", Lean.toJson journal.count),
    ("acknowledged", Lean.Json.arr rows), ("pending", Lean.Json.arr pendingRows.toArray),
    ("funded", Lean.toJson journal.state.funded), ("charged", Lean.toJson journal.state.charged)]
  pure 0

def follow (config : NativeHost.Config) (ops : Ops) (archivePath cursorPath resultPath : String) :
    IO UInt32 := do
  let archive ← loadConfig archivePath
  let journal ← readJournal config
  let text := (← IO.FS.readFile cursorPath).trimAscii.toString
  let some next := text.toNat? | throw (IO.userError "cursor file must hold one decimal height")
  let cursor : Cursor := ⟨next⟩
  let some slot := (acknowledged journal.state).find? (·.signed.identity.first == next)
    | writeResult resultPath [("type", "fn-archive-follow-v1"), ("cursor", Lean.toJson next),
        ("outcome", Lean.toJson s!"cursor held: nothing acknowledged starts at {next}")]
      return 3
  let some ack := slot.ack | throw (IO.userError "acknowledged slot without its acknowledgement")
  let served ← fetchServed ops archive ack.messageId
  let (after, outcome) := cursor.step archive.profile ack served
  if after != cursor then IO.FS.writeFile cursorPath s!"{after.next}\n"
  writeResult resultPath [("type", "fn-archive-follow-v1"), ("messageId", Lean.toJson ack.messageId),
    ("cursorBefore", Lean.toJson next), ("cursorAfter", Lean.toJson after.next),
    ("outcome", Lean.toJson outcome.word)]
  pure (if after != cursor then 0 else 3)

def fund (config : NativeHost.Config) (archivePath amountText txText eventText resultPath : String) :
    IO UInt32 := do
  let _ ← loadConfig archivePath
  let some amount := amountText.toNat? | throw (IO.userError "AMOUNT must be decimal")
  let some tx := txText.toNat? | throw (IO.userError "TXID must be decimal")
  let some ev := eventText.toNat? | throw (IO.userError "EVENTID must be decimal")
  let opened ← IO.ofExcept (← NativeHost.openExisting config)
  let some receipt := NativeHost.historicalReceipt config opened.durable ⟨tx⟩ ⟨ev⟩
    | throw (IO.userError "funding evidence names no transaction this Store accepted")
  let journal ← readJournal config
  let evidence := NativeHostCodec.receiptStream.encode receipt
  let journal ← appendEvent config journal (.funded amount evidence)
  writeResult resultPath [("type", "fn-archive-fund-v1"), ("funded", Lean.toJson journal.state.funded),
    ("charged", Lean.toJson journal.state.charged), ("height", Lean.toJson receipt.acceptedCount)]
  pure 0

def run (config : NativeHost.Config) (ops : Ops) : List String → IO UInt32
  | ["publish", archive, first, finalized, keys, result] =>
      publish config ops archive first finalized keys result
  | ["lookup", archive, messageIdText, result] => lookup config ops archive messageIdText result
  | ["resend", archive, messageIdText, result] => resendPersisted config ops archive messageIdText result
  | ["reconcile", archive, result] => reconcile config ops archive result false
  | ["reconcile", archive, result, "lookup"] => reconcile config ops archive result true
  | ["follow", archive, cursor, result] => follow config ops archive cursor result
  | ["fund", archive, amount, tx, ev, result] => fund config archive amount tx ev result
  | _ => throw (IO.userError
      "usage: fn-archive publish ARCHIVE FIRST FINALIZED|- KEYS|- RESULT | resend ARCHIVE MSGID RESULT | lookup ARCHIVE MSGID RESULT | reconcile ARCHIVE RESULT [lookup] | follow ARCHIVE CURSOR RESULT | fund ARCHIVE AMOUNT TXID EVENTID RESULT")

end Minidregg.Host.FnArchivePublisher
