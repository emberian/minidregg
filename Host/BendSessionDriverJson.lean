/- Strict operator session/key handle ingress and concrete file commands.
All observations, writes and release receipts come from BendSessionDriver's
actual current native receiver path. Raw JSON IDs are not authority tokens. -/
import Host.BendSessionDriver

namespace Minidregg.Host.BendSessionDriverJson
open Lean
open Minidregg.Compiler
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Theory
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

def parseConfig (raw : String) : Except String Config := do
  unless raw.toUTF8.size ≤ 2000000 do throw "native session config capacity"
  let j ← Minidregg.Host.Json.parse raw
  exact j ["schema","subject","nonce","sourceResource","sourceCapability","sourceRoot","sourceAtom",
    "keyResource","keyCapability","keyRoot","keyAtom","resultResource","resultCapability","resultRoot",
    "releaseCapability","audience","generation","purpose","returnName","predecessor","capacity",
    "compilerSHA256","physicalBinary","physicalBinarySHA256","physicalTransformerSHA256",
    "custodyClient","custodyClientSHA256","nativeHost","nativeHostSHA256","nativeConfigPath",
    "authoritySeedPath","privateRoot","physicalSnapshotRoot"]
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
  pure ⟨session,custody,nativeConfigPath,← string j "physicalSnapshotRoot"⟩

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

partial def readLoop (input : IO.FS.Handle) (acc : ByteArray := ByteArray.empty) :
    IO (List UInt8) := do
  if acc.size > 2000000 then throw (IO.userError "Bend driver file capacity")
  let chunk ← input.read (min 4096 (2000001 - acc.size)).toUSize
  if chunk.isEmpty then return acc.toList
  readLoop input (acc ++ chunk)
def read (path : String) : IO (List UInt8) := do
  readLoop (← IO.FS.Handle.mk path .read)
def writeFresh (path : String) (bytes : List UInt8) : IO Unit := do
  let file : System.FilePath := path
  if ← file.pathExists then throw (IO.userError "Bend driver output already exists")
  IO.FS.writeBinFile file ⟨bytes.toArray⟩
def load (path : String) : IO Config :=
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
  | ⟨.content materialized⟩ =>
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
  | ⟨.content materialized⟩ =>
      let some selected := BendOpaqueResultReceiver.lookup materialized.logical
          ⟨BendInvocation.resultId candidate⟩
        | return .error "result exact atom absent on readback"
      if BendInvocation.encode selected == BendInvocation.encode candidate then
        return .ok materialized.root
      else return .error "result exact readback payload differs"
  | _ => return .error "result readback resource kind differs"

/-- Called by existing source-matched Host.Main using its Settings.config.
The operator config path is the SAME one passed to custody's native Host.
Only exact receipt-backed released completion bytes are written at the last step. -/
def runFiles (config : NativeHost.Config) (nativeConfigPath : String)
    (args : List String) : IO (Except String Unit) := do
  match args with
  | ["register-key",sourcePath,materialPath,sessionPath,keyPath] =>
      let selected ← load sessionPath
      unless selected.nativeConfigPath == nativeConfigPath do return .error "native operator config path differs"
      let some source := BendWorldProgramCodec.decode (← read sourcePath)
        | return .error "noncanonical source artifact"
      let material ← IO.ofExcept (BendOwnerManifestJson.parse
        (String.fromUTF8! ⟨(← read materialPath).toArray⟩))
      let .ok signer ← clientSigner selected.custody | return .error "native custody signer unavailable"
      let .ok (registered,receipt) ← registerKey config selected.session signer source material
        | return .error "native key registration refused/uncertain"
      let .ok handle ← keyHandleCurrent config selected.session registered receipt
        | return .error "native key registration readback refused"
      writeFresh keyPath (keyJson handle).compress.toUTF8.toList
      return .ok ()
  | ["prepare-context",sourcePath,compilerPath,keyPath,sessionPath,contextPath] =>
      let selected ← load sessionPath
      unless selected.nativeConfigPath == nativeConfigPath do return .error "native operator config path differs"
      let handle ← IO.ofExcept (parseKey (String.fromUTF8! ⟨(← read keyPath).toArray⟩))
      let session ← IO.ofExcept (withKey selected.session handle)
      let .ok pin ← fileSHA256 compilerPath | return .error "compiler pin unavailable"
      unless pin == session.compilerSHA256 do return .error "compiler differs from independently admitted deployment pin"
      let .ok signer ← clientSigner selected.custody | return .error "native custody signer unavailable"
      let .ok prepared ← prepareContext config session signer (← read sourcePath)
          (BendKeyRecord.encode handle.registered)
        | return .error "current source/key/result preparation refused"
      writeFresh contextPath (contextJson session prepared).compress.toUTF8.toList
      return .ok ()
  | ["commit-release",sourcePath,compilerPath,keyPath,requestPath,completionPath,sessionPath,releasedPath] =>
      let selected ← load sessionPath
      unless selected.nativeConfigPath == nativeConfigPath do return .error "native operator config path differs"
      let handle ← IO.ofExcept (parseKey (String.fromUTF8! ⟨(← read keyPath).toArray⟩))
      let session ← IO.ofExcept (withKey selected.session handle)
      let sourceBytes ← read sourcePath
      let keyBytes := BendKeyRecord.encode handle.registered
      let .ok signer ← clientSigner selected.custody | return .error "native custody signer unavailable"
      let .ok prepared ← prepareContext config session signer sourceBytes keyBytes
        | return .error "current commit context unavailable"
      let .ok physical ← checkPhysical session prepared selected.physicalSnapshotRoot
          (← read compilerPath) (← read requestPath) (← read completionPath)
        | return .error "independent pinned ciphertext replay/context binding refused"
      let .ok (candidate,_storageReceipt) ← commitChecked config session signer sourceBytes keyBytes prepared physical
        | return .error "current opaque result custody refused/uncertain"
      let .ok resultRoot ← resultRootCurrent config session candidate
        | return .error "current opaque result readback unavailable"
      let .ok (_releaseReceipt,exactBytes) ← releaseExact config session signer resultRoot candidate
        | return .error "current exact return release refused/uncertain"
      writeFresh releasedPath exactBytes
      return .ok ()
  | _ => return .error "expected register-key / prepare-context / commit-release exact file arguments"

end Minidregg.Host.BendSessionDriverJson
