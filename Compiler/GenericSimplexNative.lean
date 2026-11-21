module

public import Compiler.GenericSimplexIO

-- Bodies this file reduces or derives through, not exposed by their modules (module system).
import all Init.Data.Repr
import all Init.Data.ToString.Basic
import all Init.Data.ToString.Extra
import all Init.Data.Array.Basic
import all Init.Data.ByteArray.Basic
import all Init.Data.String.Decode
import all Init.Data.String.Defs
import all Init.Control.Except
import all Init.Data.List.Basic
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.String.Bootstrap
import all Init.Data.Format.Basic
import all Init.Data.List.Scan.Basic
import all Init.System.ST
import all Init.System.IO

@[expose] public section

namespace Minidregg.Compiler.GenericSimplexNative
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Compiler.GenericSimplexCodec
open Minidregg.Compiler.GenericSimplexIO
open Minidregg.Kernel.GenericSimplex
open Minidregg.Kernel.GenericSimplexRelative
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
def opReplace : UInt8 := 10

def beBytes (width value : Nat) : ByteArray :=
  ⟨((List.range width).reverse.map fun i => ((value >>> (8 * i)) % 256).toUInt8).toArray⟩
def u32 (value : Nat) : ByteArray := beBytes 4 value
def u64 (value : Nat) : ByteArray := beBytes 8 value
def blob (bytes : Bytes) : ByteArray := u32 bytes.length ++ bytes.toByteArray
def frame (bytes : ByteArray) : ByteArray := u32 bytes.size ++ bytes
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

def Helper.mac (h : Helper) (peer : Nat) (body : ByteArray) : IO ByteArray := do
  let (status,tag) ← h.call opMac (u32 peer ++ frame body)
  if status != 0 || tag.size != 32 then throw (IO.userError "agreement MAC helper failed")
  return tag

def Helper.verifyMac (h : Helper) (peer : Nat) (body tag : ByteArray) : IO Bool :=
  h.positive opVerifyMac (u32 peer ++ frame body ++ frame tag)

def Helper.send (h : Helper) (peer : Nat) (packet : ByteArray) : IO Unit := do
  let (status,_) ← h.call opSend (u32 peer ++ frame packet)
  if status != 0 then throw (IO.userError "agreement transport refused a send")

/-- Drain at most `max` verbatim inbound frames. Nothing here is authenticated. -/
def Helper.receive (h : Helper) (max : Nat) : IO (Array ByteArray) := do
  let (_,reply) ← h.call opRecv (u32 max)
  let count := readBE reply 0 4
  let mut offset := 4
  let mut frames := #[]
  for _ in List.range count do
    let size := readBE reply offset 4
    frames := frames.push (reply.extract (offset + 4) (offset + 4 + size))
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
exclusive, length-checked append. -/
def journalStorage (helper : Helper) (writable : Bool) (initial : Sigma Restored) : IO Storage := do
  let image ← IO.mkRef (some initial)
  return {
    current := image.get
    install := image.set
    append := fun expected appended => do
      if !writable then return .conflict
      try
        let (status,_) ← helper.call opAppend (u64 expected ++ frame appended)
        return if status == 0 then .durable else .conflict
      catch _ => return .uncertain
    replace := fun expected image => do
      if !writable then return .conflict
      try
        let (status,_) ← helper.call opReplace (u64 expected ++ image)
        return if status == 0 then .durable else .conflict
      catch _ => return .uncertain }

/-- Create a fresh journal (exclusive) holding only its base frame. -/
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
      throw (IO.userError s!"agreement journal {journal} is log format version {version}; this build reads only version {(logMagic.getLast?.map UInt8.toNat).getD 0} (its inputs were recorded under a different step). An older mesh is re-genesised with init, never converted")
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

/-- One packet: the member whose pairwise MAC covers it (`origin`), the recipient, and a
message as the replica wrote it. `origin` is the message's sender except for a COMMIT, which
any member may pass on: its authority is its signer's ML-DSA signature, not the MAC. -/
structure Envelope where
  context : Context
  origin : Nat
  recipient : Nat
  message : WireMessage
  deriving DecidableEq, BEq, Repr
def envelopeStream : StreamCodec Envelope :=
  StreamCodec.xmap
    (StreamCodec.product contextStream (StreamCodec.product StreamCodec.nat
      (StreamCodec.product StreamCodec.nat wireMessageStream)))
    (fun e => (e.context,e.origin,e.recipient,e.message))
    (fun (c,o,r,m) => ⟨c,o,r,m⟩) (by intro e; cases e; rfl)
/-- Exact configured context is authenticated but need not repeat its complete
public-key roster on the wire. Both peers reconstruct the SAME canonical prefix,
so this optimization does not identify configurations by an unproved digest. -/
def wireBodyStream : StreamCodec (Nat × Nat × WireMessage × Bytes) :=
  StreamCodec.product StreamCodec.nat
    (StreamCodec.product StreamCodec.nat (StreamCodec.product wireMessageStream bytesStream))
def packetStream : StreamCodec (Bytes × Bytes) := StreamCodec.product bytesStream bytesStream
/-- The pairwise MAC covers the exact transferable signature too. Empty signature
is canonical for other protocol kinds; COMMIT always carries real ML-DSA proof. -/
def authenticatedFrame (e : Envelope) (signature : Bytes) : ByteArray :=
  (StreamCodec.product envelopeStream bytesStream).encodeBytes (e,signature)
/-- The transferable proof a message of this replica's durable output leaves with: none for
anything but a COMMIT, its signer's signature for a COMMIT (`commitProof`). A COMMIT that has
no signature is not sent. Made once per message, whatever the number of recipients. -/
def messageProof (n : Native) (context : Context) (message : WireMessage) : IO (Option Bytes) :=
  if message.kind == .commit then commitProof (storage n) (crypto n) context message
  else pure (some [])
/-- Seal one message for one recipient. -/
def sealPacket (n : Native) (e : Envelope) (signature : Bytes) : IO ByteArray := do
  let tag ← n.helper.mac e.recipient (authenticatedFrame e signature)
  return packetStream.encodeBytes
    (wireBodyStream.encode (e.origin,e.recipient,e.message,signature),tag.toList)
/-- Authenticate one packet: the MAC is its origin's, over the exact envelope and signature.
A message that is not a COMMIT must be its origin's own. A COMMIT is returned with the
signature it carries, which `receiveCommit` verifies against the statement before the
message is counted. No wire decoder constructs source-validation input. -/
def authenticate (n : Native) (context : Context) (self : Nat)
    (packet : ByteArray) : IO (Option (WireMessage × Bytes)) := do
  let some (body,tag) := packetStream.decodeBytes packet | return none
  if tag.length != 32 then return none
  let some (origin,recipient,message,signature) := wireBodyStream.toLawful.decode body
    | return none
  if recipient != self || origin ≥ context.config.parties || origin == self ||
      message.sender ≥ context.config.parties then return none
  let e : Envelope := ⟨context,origin,recipient,message⟩
  let macValid ← try n.helper.verifyMac origin (authenticatedFrame e signature) tag.toByteArray
    catch _ => pure false
  if !macValid then return none
  if message.kind == .commit then
    if message.statement.isNone then return none
    return some (message,signature)
  else
    if !signature.isEmpty || message.sender != origin || message.statement.isSome then return none
    return some (message,signature)
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
  -- A writer that had to replay many deltas checkpoints at once, so the next
  -- reopen decodes the state instead of replaying them again.
  if writable && prior.deltas ≥ checkpointEvery then
    match ← checkpoint (storage n) context with
    | .durable => pure ()
    | _ => throw (IO.userError "agreement journal checkpoint at open refused")
  return ⟨n,context,prior.state.core.now,(← IO.monoMsNow)⟩
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
def receive (runtime : Runtime) (packet : ByteArray) : IO Result := do
  let n := runtime.native
  let some prior ← runtime.current | return .invalid
  let some (m,signature) ← authenticate n runtime.context prior.self packet | return .invalid
  if m.kind == .commit then
    receiveCommit (storage n) (crypto n) runtime.context (← runtime.now) m signature
  else receiveDelivery (storage n) runtime.context (← runtime.now) m none
/-- Driver drains currently due authenticated arrivals and fair continuation
slices before firing a timer at the same timestamp. -/
def tick (runtime : Runtime) : IO Result := do
  persist (storage runtime.native) runtime.context (.input (.tick (← runtime.now)))
def poll (runtime : Runtime) : IO Result :=
  persist (storage runtime.native) runtime.context (.input .poll)
/-- Application-candidate traffic is separate from 1/3VA candidate messages.
The MAC commits the exact configured context and complete source prefix. It is
availability/discovery input only; neither sender nor receiver grants checked. -/
def candidateBodyStream : StreamCodec (Nat × Nat × Nat × Block) :=
  StreamCodec.product StreamCodec.nat (StreamCodec.product StreamCodec.nat
    (StreamCodec.product StreamCodec.nat blockStream))

def candidateMACFrame (context : Context) (body : Bytes) : ByteArray :=
  ([77,73,78,73,45,65,80,80,45,67,65,78,68,73,68,65,84,69,2] ++
    contextStream.encode context ++ body).toByteArray

/-- `records` are checked source records from application height `height`. -/
def sealCandidate (runtime : Runtime) (recipient height : Nat) (records : Block) : IO ByteArray := do
  let some prior ← runtime.current | throw (IO.userError "candidate sender journal refused")
  let body := candidateBodyStream.encode (prior.self,recipient,height,records)
  let tag ← runtime.native.helper.mac recipient (candidateMACFrame runtime.context body)
  return packetStream.encodeBytes (body,tag.toList)

def authenticateCandidate (n : Native) (context : Context) (self : Nat)
    (bytes : ByteArray) : IO (Option (Nat × Block)) := do
  let some (body,tag) := packetStream.decodeBytes bytes | return none
  if tag.length != 32 then return none
  let some (sender,recipient,height,records) := candidateBodyStream.toLawful.decode body | return none
  if recipient != self ||
      sender ≥ context.config.parties || sender == self || records.isEmpty then return none
  let valid ← try n.helper.verifyMac sender (candidateMACFrame context body) tag.toByteArray
    catch _ => pure false
  return if valid then some (height,records) else none

def receiveCandidate (runtime : Runtime) (bytes : ByteArray) : IO (Result × Option (Nat × Block)) := do
  let some prior ← runtime.current | return (.invalid,none)
  let some (height,records) ← authenticateCandidate runtime.native runtime.context prior.self bytes
    | return (.invalid,none)
  let result ← retainCandidateOffers (storage runtime.native) runtime.context height records
  match result with
  | .durable _ => return (result,some (height,records))
  | _ => return (result,none)
/-! ## Height announcements

A replica that restarts into an idle domain hears nothing: its peers have no work, so they
send nothing, and it cannot know that they committed while it was stopped. On start it
therefore tells each peer its committed height and asks for theirs. A peer that is asked
answers with its own height, and, when it has committed more and still keeps the evidence
from the asker's height on, with the COMMITs of those commits (`keptCommits`): the same
messages the kernel owes a member that asks to leave a view from that height, each under its
signer's signature. The asker takes them by the ordinary COMMIT path (`receiveCommit`), so an
announcement carries no authority: a false height costs its sender or its reader at most
the kept COMMITs once more. Nothing of this is journalled and no replica state changes on
either side except through those COMMITs. -/

structure HeightNote where
  sender : Nat
  height : Nat
  ask : Bool
  deriving DecidableEq, BEq, Repr, Inhabited

def heightBodyStream : StreamCodec (Nat × Nat × Nat × Bool) :=
  StreamCodec.product StreamCodec.nat (StreamCodec.product StreamCodec.nat
    (StreamCodec.product StreamCodec.nat StreamCodec.bool))

/-- "MINI-SIMPLEX-HEIGHT", version 1, the exact context, the body. -/
def heightMACFrame (context : Context) (body : Bytes) : ByteArray :=
  ([77,73,78,73,45,83,73,77,80,76,69,88,45,72,69,73,71,72,84,1] ++
    contextStream.encode context ++ body).toByteArray

def sealHeight (runtime : Runtime) (recipient : Nat) (ask : Bool) : IO ByteArray := do
  let some prior ← runtime.current | throw (IO.userError "height announcement: journal refused")
  let body := heightBodyStream.encode (prior.self,recipient,prior.state.height,ask)
  let tag ← runtime.native.helper.mac recipient (heightMACFrame runtime.context body)
  return packetStream.encodeBytes (body,tag.toList)

def authenticateHeight (runtime : Runtime) (bytes : ByteArray) : IO (Option HeightNote) := do
  let some prior ← runtime.current | return none
  let some (body,tag) := packetStream.decodeBytes bytes | return none
  if tag.length != 32 then return none
  let some (sender,recipient,height,ask) := heightBodyStream.toLawful.decode body | return none
  if recipient != prior.self || sender ≥ runtime.context.config.parties || sender == prior.self then
    return none
  let valid ← try runtime.native.helper.verifyMac sender (heightMACFrame runtime.context body) tag.toByteArray
    catch _ => pure false
  return if valid then some ⟨sender,height,ask⟩ else none

/-- The kept COMMITs a member at `height` is behind by, sealed for it (`keptCommits`). A
COMMIT without a signature to leave with is not sent. -/
def answerHeight (runtime : Runtime) (peer height : Nat) : IO (List ByteArray) := do
  let some prior ← runtime.current | return []
  let mut packets := []
  for message in keptCommits prior.chain prior.state height do
    if let some proof ← messageProof runtime.native runtime.context message then
      packets := (← sealPacket runtime.native ⟨runtime.context,prior.self,peer,message⟩ proof) :: packets
  return packets.reverse

end Minidregg.Compiler.GenericSimplexNative
