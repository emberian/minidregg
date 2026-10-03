/- Strict operator session/key handle ingress and concrete file commands.
All observations, writes and release receipts come from BendSessionDriver's
actual current native receiver path. Raw JSON IDs are not authority tokens. -/
import Host.BendSessionDriver
import Host.BendSessionCursor

namespace Minidregg.Host.BendSessionDriverJson
open Lean
open Minidregg.Compiler
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Theory
open Minidregg.Theory.IndexedProgram
open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.Hyperdocument
open Minidregg.Kernel
open Minidregg.Host.BendSessionDriver
set_option autoImplicit false

def string (j : Json) (name : String) : Except String String :=
  (j.getObjVal? name).bind Json.getStr?
def natural (j : Json) (name : String) : Except String Nat := do
  let raw ← string j name
  let some n := raw.toNat? | throw s!"{name}: expected decimal natural"
  if toString n == raw then pure n else throw s!"{name}: noncanonical natural"
def sha (j : Json) (name : String) : Except String String := do
  let value ← string j name
  unless BendOwnerManifestJson.sha256Shape value do throw s!"{name}: SHA256 shape"
  pure value
def exact (j : Json) (names : List String) : Except String Unit := do
  let obj ← j.getObj?
  let found := obj.foldl (init := []) (fun keys k _ => k :: keys)
  unless found.length == names.length && found.all names.contains do
    throw "missing or unknown session fields"
def natList (j : Json) (name : String) : Except String (List Nat) := do
  let values ← (← j.getObjVal? name).getArr?
  values.toList.mapM fun value => do
    let raw ← value.getStr?
    let some n := raw.toNat? | throw "non-natural capacity"
    if toString n == raw then pure n else throw "noncanonical capacity"

structure Config where
  session : Session
  custody : Custody
  nativeConfigPath : String
  physicalSnapshotRoot : String
  cursorPath : String

def parseConfig (raw : String) : Except String Config := do
  unless raw.toUTF8.size ≤ 2000000 do throw "native session config capacity"
  let j ← Minidregg.Host.Json.parse raw
  exact j ["schema","subject","nonce","sourceResource","sourceCapability","sourceRoot","sourceAtom",
    "keyResource","keyCapability","keyRoot","keyAtom","resultResource","resultCapability","resultRoot",
    "releaseCapability","audience","generation","purpose","returnName","predecessor","capacity",
    "compilerSHA256","physicalBinary","physicalBinarySHA256","physicalTransformerSHA256",
    "custodyClient","custodyClientSHA256","nativeHost","nativeHostSHA256","nativeConfigPath",
    "authoritySeedPath","privateRoot","physicalSnapshotRoot","cursorPath"]
  unless (← string j "schema") == "dregg.fhe-bend.native-session.v1" do
    throw "unsupported native session schema"
  let capacity ← natList j "capacity"
  unless capacity.length == 10 do throw "native capacity requires ten lanes"
  let nativeConfigPath ← string j "nativeConfigPath"
  let session : Session := {
    subject := ⟨← natural j "subject"⟩, nonce := ← natural j "nonce"
    sourceResource := ← natural j "sourceResource"
    sourceCapability := ⟨← natural j "sourceCapability"⟩
    sourceRoot := ⟨← natural j "sourceRoot"⟩, sourceAtom := ⟨⟨← natural j "sourceAtom"⟩⟩
    keyResource := ← natural j "keyResource", keyCapability := ⟨← natural j "keyCapability"⟩
    keyRoot := ⟨← natural j "keyRoot"⟩, keyAtom := ⟨⟨← natural j "keyAtom"⟩⟩
    resultResource := ← natural j "resultResource"
    resultCapability := ⟨← natural j "resultCapability"⟩
    resultRoot := ⟨← natural j "resultRoot"⟩
    releaseCapability := ⟨← natural j "releaseCapability"⟩
    audience := ⟨← natural j "audience"⟩, generation := ← natural j "generation"
    purpose := ← string j "purpose", returnName := ← string j "returnName"
    predecessor := ⟨← natural j "predecessor"⟩, capacity := capacity
    compilerSHA256 := ← sha j "compilerSHA256", physicalBinary := ← string j "physicalBinary"
    physicalBinarySHA256 := ← sha j "physicalBinarySHA256"
    physicalTransformerSHA256 := ← sha j "physicalTransformerSHA256" }
  let custody : Custody := {
    client := ← string j "custodyClient", clientSHA256 := ← sha j "custodyClientSHA256"
    nativeHost := ← string j "nativeHost", nativeHostSHA256 := ← sha j "nativeHostSHA256"
    nativeConfigPath := nativeConfigPath, authoritySeedPath := ← string j "authoritySeedPath"
    privateRoot := ← string j "privateRoot" }
  pure ⟨session,custody,nativeConfigPath,← string j "physicalSnapshotRoot",← string j "cursorPath"⟩

structure KeyHandle where
  resource : Nat
  root : Digest
  registered : BendKeyRecord.Registered
  receipt : NativeHostCodec.Receipt

def receiptCodec : LawfulCodec NativeHostCodec.Receipt :=
  ResourceBirthCodec.strictCodec NativeHostCodec.receiptStream.toLawful

def keyJson (h : KeyHandle) : Json := Json.mkObj [
  ("schema", .str "dregg.fhe-bend.native-key-handle.v1"),
  ("resource", .str (toString h.resource)),("root", .str (toString h.root.value)),
  ("registered", .str (Minidregg.Host.Json.encodeHex (BendKeyRecord.encode h.registered))),
  ("receipt", .str (Minidregg.Host.Json.encodeHex (receiptCodec.encode h.receipt)))]

def parseKey (raw : String) : Except String KeyHandle := do
  unless raw.toUTF8.size ≤ 2000000 do throw "key handle capacity"
  let j ← Minidregg.Host.Json.parse raw
  exact j ["schema","resource","root","registered","receipt"]
  unless (← string j "schema") == "dregg.fhe-bend.native-key-handle.v1" do
    throw "key handle schema"
  let bytes ← Minidregg.Host.Json.decodeHex "registered" (← j.getObjVal? "registered")
  let some registered := BendKeyRecord.decode bytes | throw "noncanonical registered key"
  let receiptBytes ← Minidregg.Host.Json.decodeHex "receipt" (← j.getObjVal? "receipt")
  let some receipt := receiptCodec.decode receiptBytes | throw "noncanonical key storage receipt"
  pure ⟨← natural j "resource", ⟨← natural j "root"⟩, registered, receipt⟩

/-- Decoder alone is not storage/key admission: prepareContext independently
looks up these EXACT registered bytes through current signed native observation. -/
def withKey (s : Session) (h : KeyHandle) : Except String Session := do
  unless h.resource == s.keyResource && h.registered.subject == s.subject do
    throw "key handle resource/subject differs from operator session"
  pure { s with keyRoot := h.root, keyAtom := ⟨BendKeyRecord.keyId h.registered⟩ }

/-- Public ingress and local recovery have different physical shapes. A mux
request retains three ciphertexts plus pk/rk; its crash record also retains the
exact signed storage command and canonical candidate. This larger bound never
changes the public config, key, request or result admission bounds. -/
def ingressCapacity : Nat := 2000000
def retainedCapacity : Nat := 8388608
partial def readLoop (limit : Nat) (input : IO.FS.Handle)
    (acc : ByteArray := ByteArray.empty) : IO (List UInt8) := do
  if acc.size > limit then throw (IO.userError "Bend driver file capacity")
  let chunk ← input.read (min 4096 (limit + 1 - acc.size)).toUSize
  if chunk.isEmpty then return acc.toList
  readLoop limit input (acc ++ chunk)
def readAtMost (path : String) (limit : Nat) : IO (List UInt8) := do
  readLoop limit (← IO.FS.Handle.mk path .read)
def read (path : String) : IO (List UInt8) := readAtMost path ingressCapacity
def writeFresh (path : String) (bytes : List UInt8) : IO Unit := do
  let file : System.FilePath := path
  if ← file.pathExists then throw (IO.userError "Bend driver output already exists")
  IO.FS.writeBinFile file ⟨bytes.toArray⟩
def load (path : String) : IO Config := do
  IO.ofExcept (parseConfig (String.fromUTF8! ⟨(← read path).toArray⟩))

/-- Readback after actual registration selects current stored canonical bytes.
This local lookup is not exported as an independent read authority credential. -/
def keyHandleCurrent (config : NativeHost.Config) (s : Session)
    (registered : BendKeyRecord.Registered) (receipt : NativeHostCodec.Receipt) :
    IO (Except String KeyHandle) := do
  let .ok opened ← NativeHost.openExisting config | return .error "key readback image unavailable"
  let .present packed := opened.directory.directory.slots s.keyResource
    | return .error "key readback resource absent"
  match packed with
  | ⟨.content, materialized⟩ =>
      let some selected := BendKeyRegistration.lookup materialized.logical ⟨BendKeyRecord.keyId registered⟩
        | return .error "key canonical atom absent on readback"
      if BendKeyRecord.encode selected == BendKeyRecord.encode registered then
        return .ok ⟨s.keyResource,materialized.root,selected,receipt⟩
      else return .error "key canonical readback payload differs"
  | _ => return .error "key readback resource kind differs"

def resultRootCurrent (config : NativeHost.Config) (s : Session)
    (candidate : BendInvocation.Result) : IO (Except String Digest) := do
  let .ok opened ← NativeHost.openExisting config | return .error "result readback image unavailable"
  let .present packed := opened.directory.directory.slots s.resultResource
    | return .error "result readback resource absent"
  match packed with
  | ⟨.content, materialized⟩ =>
      let some selected := BendOpaqueResultReceiver.lookup materialized.logical
          ⟨BendInvocation.resultId candidate⟩
        | return .error "result exact atom absent on readback"
      if BendInvocation.encode selected == BendInvocation.encode candidate then
        return .ok materialized.root
      else return .error "result exact readback payload differs"
  | _ => return .error "result readback resource kind differs"

/-- An interruption after syncing a staging file but before rename retains
that exact original attempt too. Its decoder/actual native gate still decide;
existence of either local file is never journal admission. -/
def retainedExists (path : String) : IO Bool := do
  let file : System.FilePath := path
  let pending : System.FilePath := path ++ ".pending"
  return (← file.pathExists) || (← pending.pathExists)
def readRetained (path : String) : IO (List UInt8) := do
  let file : System.FilePath := path
  let pending : System.FilePath := path ++ ".pending"
  if ← pending.pathExists then readAtMost pending.toString retainedCapacity
  else readAtMost path retainedCapacity

def selectedSession (config : NativeHost.Config) (selected : Config)
    (initial : Session) (signer : Signer) : IO (Except String Session) := do
  let path : System.FilePath := selected.cursorPath
  unless ← retainedExists selected.cursorPath do return .ok initial
  let some cursor := BendSessionCursor.codec.decode (← readRetained selected.cursorPath)
    | return .error "noncanonical retained native session cursor"
  let .ok admitted ← BendSessionCursor.admit config initial signer cursor
    | return .error "retained predecessor current read/history admission refused"
  return .ok (BendSessionCursor.nextSession initial admitted)

/-- Linux hosted deployment: fsync the exact retained bytes before rename,
then the containing directory. A sync failure produces no native mutation. -/
def writeRetained (path : String) (bytes : List UInt8) : IO Unit := do
  unless bytes.length ≤ retainedCapacity do throw (IO.userError "retained session journal capacity")
  let file : System.FilePath := path
  let temporary : System.FilePath := path ++ ".pending"
  if ← temporary.pathExists then
    unless (← readAtMost temporary.toString retainedCapacity) == bytes do
      throw (IO.userError "different pending retention requires original receipt reconciliation")
  else IO.FS.writeBinFile temporary ⟨bytes.toArray⟩
  let syncFile ← IO.Process.output { cmd := "sync", args := #["-f",temporary.toString] }
  unless syncFile.exitCode == 0 do throw (IO.userError "retained file sync refused")
  IO.FS.rename temporary file
  let parent := file.parent.getD "."
  let syncDirectory ← IO.Process.output { cmd := "sync", args := #["-f",parent.toString] }
  unless syncDirectory.exitCode == 0 do throw (IO.userError "retained directory sync refused")

def retainCursor (selected : Config) (stored : Stored) (released : Released) : IO Unit := do
  let cursor ← IO.ofExcept (BendSessionCursor.retain stored released)
  writeRetained selected.cursorPath (BendSessionCursor.codec.encode cursor)

def attemptPath (selected : Config) : String := selected.cursorPath ++ ".attempt"

def writeReleased (path : String) (bytes : List UInt8) : IO Unit := do
  let file : System.FilePath := path
  if ← file.pathExists then
    unless (← read path) == bytes do throw (IO.userError "existing released bytes differ")
  else writeFresh path bytes

/-- This branch precedes cursor advancement. Reconcile the ORIGINAL signed
storage and release identities, rather than minting a new invocation on retry. -/
def recoverAttempt (config : NativeHost.Config) (selected : Config) (initial : Session)
    (signer : Signer) (source compiler key request completion : List UInt8) :
    IO (Except String (Option Released)) := do
  let path : System.FilePath := attemptPath selected
  unless ← retainedExists (attemptPath selected) do return .ok none
  let some attempt := BendSessionCursor.attemptCodec.decode (← readRetained path.toString)
    | return .error "noncanonical original session attempt"
  if attempt.publication.candidate.result.bytes != completion then
    let cursorPath : System.FilePath := selected.cursorPath
    unless ← retainedExists selected.cursorPath do
      return .error "incomplete prior attempt must reconcile before another invocation"
    let some cursor := BendSessionCursor.codec.decode (← readRetained selected.cursorPath)
      | return .error "noncanonical prior cursor"
    unless BendInvocation.encode cursor.publication.candidate ==
        BendInvocation.encode attempt.publication.candidate do
      return .error "retained attempt has no completed matching predecessor"
    return .ok none
  let some sourceArtifact := BendWorldProgramCodec.decode source
    | return .error "retained source canonical artifact refused"
  let .ok _ := BendArtifactBinding.check sourceArtifact compiler
    | return .error "retained original source/compiler constructive binding refused"
  let .ok () := BendFheArtifact.checkWireProfile sourceArtifact compiler
    | return .error "retained physical input/output/disclosure profile refused"
  unless attempt.source == source && attempt.compiler == compiler &&
      attempt.key == key && attempt.request == request &&
      attempt.publication.subject == initial.subject &&
      attempt.publication.sourceResource == initial.sourceResource &&
      attempt.publication.sourceAtom == initial.sourceAtom &&
      attempt.publication.resultResource == initial.resultResource &&
      attempt.publication.nonce ≥ 2 do
    return .error "retry differs from exact retained original source/key/request"
  let candidate := attempt.publication.candidate
  let session : Session := { initial with
    nonce := attempt.publication.nonce - 2
    generation := candidate.result.generation
    predecessor := candidate.execution.predecessor
    sourceRoot := attempt.publication.sourceRoot
    resultRoot := attempt.publication.resultRoot }
  unless candidate.definition.artifact == session.sourceAtom.digest &&
      candidate.result.keyEpoch == session.keyAtom.digest &&
      candidate.result.recipient == session.subject &&
      candidate.result.audience == session.audience do
    return .error "retained original candidate is outside this source/key/audience"
  if let some ingress := attempt.release then
    unless ingress.spec.subject == session.subject &&
        ingress.spec.nonce == session.nonce + 3 &&
        ingress.spec.source.resource == session.resultResource &&
        ingress.spec.destination.recipient == session.subject &&
        ingress.spec.destination.keyEpoch == session.keyAtom.digest &&
        ingress.spec.destination.audience == session.audience &&
        ingress.spec.destination.generation == session.generation &&
        ingress.spec.destination.purpose == session.purpose &&
        ingress.spec.capability == session.releaseCapability do
      return .error "retry release destination/current purpose differs"
  let .ok stored ← resumeStorage config attempt.publication attempt.signed
    | return .error "original storage receipt remains refused/uncertain"
  let .ok released ← (match attempt.release with
    | some ingress => resumeRelease config candidate ingress
    | none => do
      let .ok root ← resultRootCurrent config session candidate
        | return .error "original stored result current readback unavailable"
      releaseExact config session signer root candidate (fun ingress => do
        writeRetained (attemptPath selected)
          (BendSessionCursor.attemptCodec.encode {attempt with release := some ingress})
        return .ok ()))
    | return .error "original current release remains refused/uncertain"
  retainCursor selected stored released
  return .ok (some released)

/-- Called by existing source-matched Host.Main using its Settings.config.
The operator config path is the SAME one passed to custody's native Host.
Only exact receipt-backed released completion bytes are written at the last step. -/
def runFiles (config : NativeHost.Config) (nativeConfigPath : String)
    (args : List String) : IO (Except String Unit) := do
  match args with
  | ["register-key",sourcePath,materialPath,sessionPath,keyPath] =>
      let selected ← load sessionPath
      unless selected.nativeConfigPath == nativeConfigPath do return .error "native operator config path differs"
      let sourceBytes ← read sourcePath
      let some source := BendWorldProgramCodec.decode sourceBytes
        | return .error "noncanonical source artifact"
      let material ← IO.ofExcept (BendOwnerManifestJson.parse
        (String.fromUTF8! ⟨(← read materialPath).toArray⟩))
      let .ok signer ← clientSigner selected.custody | return .error "native custody signer unavailable"
      let attemptFile : System.FilePath := keyPath ++ ".attempt"
      let .ok (registered,receipt) ← (if ← retainedExists attemptFile.toString then do
        let some original := BendSessionCursor.keyAttemptCodec.decode (← readRetained attemptFile.toString)
          | return .error "noncanonical original key registration"
        let expected : BendKeyRecord.Registered :=
          ⟨selected.session.subject,BendWorldProgramCodec.artifactId source,
            BendInvocation.methodId source,material⟩
        unless original.source == sourceBytes &&
            BendKeyRecord.encode original.publication.registered == BendKeyRecord.encode expected &&
            original.publication.subject == selected.session.subject &&
            original.publication.nonce == selected.session.nonce &&
            original.publication.sourceResource == selected.session.sourceResource &&
            original.publication.sourceAtom == selected.session.sourceAtom &&
            original.publication.keyResource == selected.session.keyResource do
          return .error "retry differs from original authored key registration"
        resumeKey config original.publication original.signed
      else registerKey config selected.session signer source material (fun publication signed => do
        writeRetained attemptFile.toString
          (BendSessionCursor.keyAttemptCodec.encode ⟨publication,signed,sourceBytes⟩)
        return .ok ()))
        | return .error "native original key registration refused/uncertain"
      let .ok handle ← keyHandleCurrent config selected.session registered receipt
        | return .error "native key registration readback refused"
      writeReleased keyPath (keyJson handle).compress.toUTF8.toList
      return .ok ()
  | ["prepare-context",sourcePath,compilerPath,keyPath,sessionPath,contextPath] =>
      let selected ← load sessionPath
      unless selected.nativeConfigPath == nativeConfigPath do return .error "native operator config path differs"
      let handle ← IO.ofExcept (parseKey (String.fromUTF8! ⟨(← read keyPath).toArray⟩))
      let initial ← IO.ofExcept (withKey selected.session handle)
      let .ok signer ← clientSigner selected.custody | return .error "native custody signer unavailable"
      let session ← IO.ofExcept (← selectedSession config selected initial signer)
      let .ok pin ← fileSHA256 compilerPath | return .error "compiler pin unavailable"
      unless pin == session.compilerSHA256 do return .error "compiler differs from independently admitted deployment pin"
      let .ok prepared ← prepareContext config session signer (← read sourcePath)
          (BendKeyRecord.encode handle.registered) (← read compilerPath)
        | return .error "current source/key/result preparation refused"
      writeFresh contextPath (contextJson session prepared).compress.toUTF8.toList
      return .ok ()
  | ["commit-release",sourcePath,compilerPath,keyPath,requestPath,completionPath,sessionPath,releasedPath] =>
      let selected ← load sessionPath
      unless selected.nativeConfigPath == nativeConfigPath do return .error "native operator config path differs"
      let handle ← IO.ofExcept (parseKey (String.fromUTF8! ⟨(← read keyPath).toArray⟩))
      let initial ← IO.ofExcept (withKey selected.session handle)
      let .ok signer ← clientSigner selected.custody | return .error "native custody signer unavailable"
      let sourceBytes ← read sourcePath
      let compilerBytes ← read compilerPath
      let keyBytes := BendKeyRecord.encode handle.registered
      let requestBytes ← read requestPath
      let completionBytes ← read completionPath
      let .ok recovered ← recoverAttempt config selected initial signer
          sourceBytes compilerBytes keyBytes requestBytes completionBytes
        | return .error "original receipt reconciliation refused/uncertain"
      if let some released := recovered then
        writeReleased releasedPath released.bytes
        return .ok ()
      let session ← IO.ofExcept (← selectedSession config selected initial signer)
      let .ok prepared ← prepareContext config session signer sourceBytes keyBytes compilerBytes
        | return .error "current commit context unavailable"
      let .ok physical ← checkPhysical session prepared selected.physicalSnapshotRoot
          compilerBytes requestBytes completionBytes
        | return .error "independent pinned ciphertext replay/context binding refused"
      let retained ← IO.mkRef (none : Option BendSessionCursor.Attempt)
      let .ok stored ← commitChecked config session signer sourceBytes keyBytes prepared physical
          (fun publication signed => do
            let attempt : BendSessionCursor.Attempt :=
              ⟨publication,signed,sourceBytes,compilerBytes,keyBytes,requestBytes,none⟩
            writeRetained (attemptPath selected) (BendSessionCursor.attemptCodec.encode attempt)
            retained.set (some attempt)
            return .ok ())
        | return .error "current opaque result custody refused/uncertain"
      let candidate := stored.publication.candidate
      let .ok resultRoot ← resultRootCurrent config session candidate
        | return .error "current opaque result readback unavailable"
      let some attempt ← retained.get | return .error "original stored command retention absent"
      let .ok released ← releaseExact config session signer resultRoot candidate
          (fun ingress => do
            writeRetained (attemptPath selected)
              (BendSessionCursor.attemptCodec.encode {attempt with release := some ingress})
            return .ok ())
        | return .error "current exact return release refused/uncertain"
      retainCursor selected stored released
      writeReleased releasedPath released.bytes
      return .ok ()
  | _ => return .error "expected register-key / prepare-context / commit-release exact file arguments"

end Minidregg.Host.BendSessionDriverJson
