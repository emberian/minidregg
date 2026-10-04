import Compiler.GenericSimplexIO
namespace Minidregg.Compiler.GenericSimplexNative
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Compiler.GenericSimplexCodec
open Minidregg.Compiler.GenericSimplexIO
open Minidregg.Kernel.GenericSimplex
set_option autoImplicit false
/-- Callers use fresh names inside an owner-private directory. Complete file
permissions before passing a descriptor to the independent storage helper. -/
def writePrivate (path : System.FilePath) (bytes : ByteArray) : IO Unit := do
  IO.FS.writeBinFile path bytes
  IO.setAccessRights path {user := {read := true,write := true}}

/-! ## Long-lived helper session

One `mini-joint-agreement-crypto session` process per replica keeps the
ML-DSA-65 signing key and pairwise MAC keys loaded, holds the replica's journal
under an exclusive lock for its whole lifetime, and keeps persistent TCP
connections to the peers. A strict request/response protocol over its stdio
replaces one subprocess (and temp files) per MAC, signature, CAS and packet. -/

def opSign : UInt8 := 1
def opVerify : UInt8 := 2
def opMac : UInt8 := 3
def opVerifyMac : UInt8 := 4
def opOpen : UInt8 := 5
def opAppend : UInt8 := 6
def opSend : UInt8 := 7
def opRecv : UInt8 := 8
def opCreate : UInt8 := 9

def beBytes (width value : Nat) : ByteArray :=
  ⟨((List.range width).reverse.map fun i => ((value >>> (8 * i)) % 256).toUInt8).toArray⟩
def u32 (value : Nat) : ByteArray := beBytes 4 value
def u64 (value : Nat) : ByteArray := beBytes 8 value
def blob (bytes : Bytes) : ByteArray := u32 bytes.length ++ bytes.toByteArray
def readBE (bytes : ByteArray) (start width : Nat) : Nat :=
  (List.range width).foldl (fun acc i => acc * 256 + (bytes.get! (start + i)).toNat) 0

structure Helper where
  call : UInt8 → ByteArray → IO (UInt8 × ByteArray)
  close : IO Unit
  deriving Inhabited

def readExact (handle : IO.FS.Handle) (count : Nat) : IO ByteArray := do
  let mut out := ByteArray.empty
  while out.size < count do
    let chunk ← handle.read (count - out.size).toUSize
    if chunk.isEmpty then throw (IO.userError "agreement helper session closed")
    out := out ++ chunk
  return out

structure HelperSpec where
  binary : System.FilePath
  signingKey : Option System.FilePath := none
  journal : Option System.FilePath := none
  listen : Option String := none
  peers : List (Nat × String) := []
  pairKeys : List (Nat × System.FilePath) := []
  deriving Inhabited

def HelperSpec.args (spec : HelperSpec) : Array String := Id.run do
  let mut args := #["session"]
  if let some sk := spec.signingKey then args := args ++ #["--sk",sk.toString]
  if let some journal := spec.journal then args := args ++ #["--journal",journal.toString]
  if let some listen := spec.listen then args := args ++ #["--listen",listen]
  for (index,address) in spec.peers do args := args ++ #["--peer",s!"{index}={address}"]
  for (index,path) in spec.pairKeys do args := args ++ #["--pair",s!"{index}={path}"]
  return args

def spawnHelper (spec : HelperSpec) : IO Helper := do
  let child ← IO.Process.spawn
    { cmd := spec.binary.toString, args := spec.args,
      stdin := .piped, stdout := .piped, stderr := .inherit }
  let call := fun (op : UInt8) (body : ByteArray) => do
    child.stdin.write (ByteArray.mk #[op] ++ u32 body.size ++ body)
    child.stdin.flush
    let header ← readExact child.stdout 5
    let reply ← readExact child.stdout (readBE header 1 4)
    let status := header.get! 0
    if status == 2 then
      throw (IO.userError ("agreement helper: " ++ (String.fromUTF8? reply).getD "error"))
    return (status,reply)
  let close := do
    child.kill
    let _ ← child.wait
  return ⟨call,close⟩

def Helper.positive (h : Helper) (op : UInt8) (body : ByteArray) : IO Bool := do
  let (status,_) ← h.call op body
  return status == 0

def Helper.mac (h : Helper) (peer : Nat) (frame : Bytes) : IO Bytes := do
  let (status,tag) ← h.call opMac (u32 peer ++ blob frame)
  if status != 0 || tag.size != 32 then throw (IO.userError "agreement MAC helper failed")
  return tag.toList

def Helper.verifyMac (h : Helper) (peer : Nat) (frame tag : Bytes) : IO Bool :=
  h.positive opVerifyMac (u32 peer ++ blob frame ++ blob tag)

def Helper.send (h : Helper) (peer : Nat) (packet : Bytes) : IO Unit := do
  let (status,_) ← h.call opSend (u32 peer ++ blob packet)
  if status != 0 then throw (IO.userError "agreement transport refused a send")

/-- Drain at most `max` verbatim inbound frames. Nothing here is authenticated. -/
def Helper.receive (h : Helper) (max : Nat) : IO (List Bytes) := do
  let (_,reply) ← h.call opRecv (u32 max)
  let count := readBE reply 0 4
  let mut offset := 4
  let mut frames := []
  for _ in List.range count do
    let size := readBE reply offset 4
    frames := frames ++ [(reply.extract (offset + 4) (offset + 4 + size)).toList]
    offset := offset + 4 + size
  return frames

def Helper.crypto (h : Helper) : Crypto where
  verify pk frame signature := try h.positive opVerify (blob pk ++ blob frame ++ blob signature)
    catch _ => return false
  sign frame := do
    let (status,signature) ← h.call opSign (blob frame)
    if status != 0 then throw (IO.userError "agreement signature helper failed")
    return signature.toList

structure Native where
  journal : System.FilePath
  helper : Helper
  storage : Storage
  /-- The exact helper session this replica was opened with, so a restart
  reopens the same keys, listener and peers from the durable journal alone. -/
  spec : HelperSpec
  writable : Bool
  deriving Inhabited

def storage (n : Native) : Storage := n.storage
def crypto (n : Native) : Crypto := n.helper.crypto

/-- Journal storage over an in-memory authoritative image and the helper's
exclusive, length-checked, fsynced append. -/
def journalStorage (helper : Helper) (writable : Bool) (initial : Sigma Restored) : IO Storage := do
  let image ← IO.mkRef (some initial)
  return {
    current := image.get
    install := image.set
    append := fun expected frame => do
      if !writable then return .conflict
      try
        let (status,_) ← helper.call opAppend (u64 expected ++ blob frame)
        return if status == 0 then .durable else .conflict
      catch _ => return .uncertain }

/-- Create a fresh journal (exclusive, fsynced) holding only its base frame. -/
def createJournal (binary journal : System.FilePath) (base : Journal) : IO Unit := do
  let helper ← spawnHelper {binary := binary,journal := some journal}
  try
    let (status,_) ← helper.call opCreate (blob (Log.encode ⟨base,[]⟩))
    if status != 0 then throw (IO.userError "agreement journal create refused")
  finally helper.close

/-- Open the replica's journal. A writable open takes the exclusive writer lock
and removes only a torn unacknowledged tail; a read-only open ignores it. -/
def openNative (spec : HelperSpec) (journal : System.FilePath) (context : Context)
    (writable : Bool) : IO Native := do
  let bytes := (← IO.FS.readBinFile journal).toList
  if let some version := logFormatVersion bytes then
    if some version != logMagic.getLast? then
      throw (IO.userError s!"agreement journal {journal} is log format version {version}; this build reads only version {(logMagic.getLast?.map UInt8.toNat).getD 0} (the timeout-backoff epoch, five-field Config). An older mesh is re-genesised with init, never converted")
  let some valid := scanLog bytes
    | throw (IO.userError "agreement journal is not an append-only log or has a corrupt frame")
  let some restored := openRestored context (bytes.take valid)
    | throw (IO.userError "agreement journal does not replay under this exact context")
  let spec := {spec with journal := if writable then some journal else none}
  let helper ← spawnHelper spec
  if writable then
    let (status,_) ← helper.call opOpen (u64 bytes.length ++ u64 valid)
    if status != 0 then
      helper.close
      throw (IO.userError "agreement journal writer open refused")
  return ⟨journal,helper,← journalStorage helper writable ⟨context,restored⟩,spec,writable⟩

structure Envelope where
  context : Context
  recipient : Nat
  sequence : Nat
  message : Message
  deriving DecidableEq, BEq, Repr
def envelopeStream : StreamCodec Envelope :=
  StreamCodec.xmap
    (StreamCodec.product contextStream (StreamCodec.product StreamCodec.nat
      (StreamCodec.product StreamCodec.nat messageStream)))
    (fun e => (e.context,e.recipient,e.sequence,e.message))
    (fun (c,r,s,m) => ⟨c,r,s,m⟩) (by intro e; cases e; rfl)
/-- Exact configured context is authenticated but need not repeat its complete
public-key roster on the wire. Both peers reconstruct the SAME canonical prefix,
so this optimization does not identify configurations by an unproved digest. -/
def wireBodyStream : StreamCodec (Nat × Nat × Message × Bytes) :=
  StreamCodec.product StreamCodec.nat
    (StreamCodec.product StreamCodec.nat (StreamCodec.product messageStream bytesStream))
def wireBody (e : Envelope) (signature : Bytes) : Bytes :=
  wireBodyStream.encode (e.recipient,e.sequence,e.message,signature)
def packetStream : StreamCodec (Bytes × Bytes) := StreamCodec.product bytesStream bytesStream
/-- The pairwise MAC covers the exact transferable signature too. Empty signature
is canonical for other protocol kinds; COMMIT always carries real ML-DSA proof. -/
def authenticatedFrame (e : Envelope) (signature : Bytes) : Bytes :=
  (StreamCodec.product envelopeStream bytesStream).encode (e,signature)
def sealPacket (n : Native) (e : Envelope) : IO Bytes := do
  let signature ← if e.message.kind == .commit then do
      let some block := e.message.value
        | throw (IO.userError "COMMIT without block")
      let some attestation ← exportCommitment (storage n) (crypto n) e.context e.message.view block
        | throw (IO.userError "COMMIT lacks durable send cause")
      if attestation.signer != e.message.sender then
        throw (IO.userError "COMMIT sender differs from durable signer")
      pure attestation.signature
    else pure []
  let tag ← n.helper.mac e.recipient (authenticatedFrame e signature)
  return packetStream.encode (wireBody e signature,tag)
/-- An authenticated COMMIT includes transferable evidence. Its witness is
returned with the message so the caller persists both in the same source-neutral
engine journal transaction. No wire decoder constructs source-validation input. -/
def authenticate (n : Native) (context : Context) (self : Nat)
    (packet : Bytes) : IO (Option (Message × Option CommitWitness)) := do
  let some (body,tag) := packetStream.toLawful.decode packet | return none
  if packetStream.encode (body,tag) != packet || tag.length != 32 then return none
  let some (recipient,sequence,message,signature) := wireBodyStream.toLawful.decode body
    | return none
  if wireBodyStream.encode (recipient,sequence,message,signature) != body || recipient != self ||
      message.sender ≥ context.config.parties || message.sender == self then return none
  let e : Envelope := ⟨context,recipient,sequence,message⟩
  let macValid ← try n.helper.verifyMac message.sender (authenticatedFrame e signature) tag
    catch _ => pure false
  if !macValid then return none
  if message.kind == .commit then
    let some block := message.value | return none
    let witness : CommitWitness := ⟨message.view,block,⟨message.sender,signature⟩⟩
    if !(← verifyCommitWitness (crypto n) context witness) then return none
    return some (message,some witness)
  else
    if !signature.isEmpty then return none
    return some (message,none)
/-- A reboot resets the OS monotonic clock. Rebase it at the persisted logical
clock instead of waiting for the new uptime to catch the old machine's uptime. -/
structure Runtime where
  native : Native
  context : Context
  logicalBase : Nat
  monotonicBase : Nat
  deriving Inhabited
def openRuntime (spec : HelperSpec) (journal : System.FilePath) (context : Context)
    (writable : Bool := true) : IO Runtime := do
  let n ← openNative spec journal context writable
  let some prior ← current (storage n) context
    | throw (IO.userError "invalid agreement journal")
  return ⟨n,context,prior.state.now,(← IO.monoMsNow)⟩
def Runtime.now (r : Runtime) : IO Nat := do
  return r.logicalBase + ((← IO.monoMsNow) - r.monotonicBase)
def Runtime.close (r : Runtime) : IO Unit := r.native.helper.close
/-- Process restart: stop this helper session (releasing the writer lock) and
open the same replica again from its durable journal alone. Every volatile
image, cursor and connection of the old session is lost. -/
def Runtime.reopen (r : Runtime) : IO Runtime := do
  r.close
  openRuntime r.native.spec r.native.journal r.context r.native.writable
def Runtime.current (r : Runtime) : IO (Option (Restored r.context)) :=
  GenericSimplexIO.current (storage r.native) r.context
/-- Network ingress admits ONLY authenticated protocol delivery, never checked,
offer, tick or arbitrary serialized controller inputs. -/
def receive (runtime : Runtime) (packet : Bytes) : IO Result := do
  let n := runtime.native
  let some prior ← runtime.current | return .invalid
  let some (m,witness) ← authenticate n runtime.context prior.self packet | return .invalid
  match witness with
  | some w => receiveCommitWitness (storage n) (crypto n) runtime.context (← runtime.now) w
  | none => receiveAuthenticated (storage n) runtime.context (← runtime.now) m
/-- A recovered certificate relays original transferable COMMIT sends. Pairwise
MAC authority is not promoted to another member's signature authority. -/
def receiveFinality (runtime : Runtime) (certificateBytes : Bytes) : IO Result := do
  receiveCommitment (storage runtime.native) (crypto runtime.native) runtime.context
    (← runtime.now) certificateBytes
/-- Driver drains currently due authenticated arrivals and fair continuation
slices before firing a timer at the same timestamp. -/
def tick (runtime : Runtime) : IO Result := do
  persist (storage runtime.native) runtime.context (.tick (← runtime.now))
def poll (runtime : Runtime) : IO Result :=
  persist (storage runtime.native) runtime.context .poll
/-- Application-candidate traffic is separate from 1/3VA candidate messages.
The MAC commits the exact configured context and complete source prefix. It is
availability/discovery input only; neither sender nor receiver grants checked. -/
def candidateBodyStream : StreamCodec (Nat × Nat × Block) :=
  StreamCodec.product StreamCodec.nat (StreamCodec.product StreamCodec.nat blockStream)

def candidateMACFrame (context : Context) (body : Bytes) : Bytes :=
  [77,73,78,73,45,65,80,80,45,67,65,78,68,73,68,65,84,69,1] ++
    contextStream.encode context ++ body

def sealCandidate (runtime : Runtime) (recipient : Nat) (block : Block) : IO Bytes := do
  let some prior ← runtime.current | throw (IO.userError "candidate sender journal refused")
  let body := candidateBodyStream.encode (prior.self,recipient,block)
  let tag ← runtime.native.helper.mac recipient (candidateMACFrame runtime.context body)
  return packetStream.encode (body,tag)

def authenticateCandidate (n : Native) (context : Context) (self : Nat)
    (bytes : Bytes) : IO (Option Block) := do
  let some (body,tag) := packetStream.toLawful.decode bytes | return none
  if packetStream.encode (body,tag) != bytes || tag.length != 32 then return none
  let some (sender,recipient,block) := candidateBodyStream.toLawful.decode body | return none
  if candidateBodyStream.encode (sender,recipient,block) != body || recipient != self ||
      sender ≥ context.config.parties || sender == self || block.isEmpty then return none
  let valid ← try n.helper.verifyMac sender (candidateMACFrame context body) tag
    catch _ => pure false
  return if valid then some block else none

def receiveCandidate (runtime : Runtime) (bytes : Bytes) : IO (Result × Option Block) := do
  let some prior ← runtime.current | return (.invalid,none)
  let some block ← authenticateCandidate runtime.native runtime.context prior.self bytes
    | return (.invalid,none)
  let result ← retainCandidateOffers (storage runtime.native) runtime.context block
  match result with
  | .durable _ => return (result,some block)
  | _ => return (result,none)
end Minidregg.Compiler.GenericSimplexNative
