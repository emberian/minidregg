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

structure Native where
  binary : System.FilePath
  journal : System.FilePath
  signingKey : System.FilePath
  /-- Private per-recipient pairwise keys, installed by deployment setup. -/
  pairKey : Nat → System.FilePath
  /-- Optional streaming exact-file CAS helper, independent of bounded wire
  frames and the cryptographic helper. No history truncation is implied. -/
  storageBinary : Option System.FilePath := none
  deriving Inhabited
def run (n : Native) (args : Array String) : IO IO.Process.Output :=
  IO.Process.output {cmd := n.binary.toString,args := args}
def runStorage (n : Native) (args : Array String) : IO IO.Process.Output :=
  IO.Process.output {cmd := (n.storageBinary.getD n.binary).toString,args := args}
def positive (o : IO.Process.Output) : Bool :=
  o.exitCode == 0 && o.stderr.isEmpty && o.stdout == "verified\n"
def crypto (n : Native) : Crypto where
  verify pk frame signature := try
    IO.FS.withTempDir fun dir => do
      let p := dir / "pk"
      let m := dir / "frame"
      let s := dir / "sig"
      writePrivate p pk.toByteArray
      writePrivate m frame.toByteArray
      writePrivate s signature.toByteArray
      return positive (← run n #["verify",p.toString,m.toString,s.toString])
    catch _ => return false
  sign frame := IO.FS.withTempDir fun dir => do
    let m := dir / "frame"
    let s := dir / "sig"
    writePrivate m frame.toByteArray
    let o ← run n #["sign",n.signingKey.toString,m.toString,s.toString]
    if o.exitCode != 0 || !o.stderr.isEmpty || !o.stdout.isEmpty then
      throw (IO.userError "agreement signature helper failed")
    return (← IO.FS.readBinFile s).toList
def storage (n : Native) : Storage where
  read := return (← IO.FS.readBinFile n.journal).toList
  compareAppend expected next := try
    IO.FS.withTempDir fun dir => do
      let e := dir / "expected"
      let p := dir / "next"
      writePrivate e expected.toByteArray
      writePrivate p next.toByteArray
      let o ← runStorage n #["cas",n.journal.toString,e.toString,p.toString]
      if o.exitCode != 0 || !o.stderr.isEmpty then return .uncertain
      if o.stdout == "durable\n" then return .durable
      if o.stdout == "conflict\n" then return .conflict
      return .uncertain
    catch _ => return .uncertain
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
def sealPacket (n : Native) (e : Envelope) : IO Bytes := IO.FS.withTempDir fun dir => do
  let signature ← if e.message.kind == .commit then do
      let some block := e.message.value
        | throw (IO.userError "COMMIT without block")
      let some attestation ← exportCommitment (storage n) (crypto n) e.context e.message.view block
        | throw (IO.userError "COMMIT lacks durable send cause")
      if attestation.signer != e.message.sender then
        throw (IO.userError "COMMIT sender differs from durable signer")
      pure attestation.signature
    else pure []
  let frame := authenticatedFrame e signature
  let p := dir / "frame"
  let t := dir / "tag"
  writePrivate p frame.toByteArray
  let o ← run n #["mac",(n.pairKey e.recipient).toString,p.toString,t.toString]
  if o.exitCode != 0 || !o.stderr.isEmpty || !o.stdout.isEmpty then
    throw (IO.userError "agreement MAC helper failed")
  return packetStream.encode (wireBody e signature,(← IO.FS.readBinFile t).toList)
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
      message.sender ≥ context.config.parties then return none
  let e : Envelope := ⟨context,recipient,sequence,message⟩
  let frame := authenticatedFrame e signature
  let macValid ← try
    IO.FS.withTempDir fun dir => do
      let p := dir / "frame"
      let t := dir / "tag"
      writePrivate p frame.toByteArray
      writePrivate t tag.toByteArray
      let o ← run n #["verify-mac",(n.pairKey e.message.sender).toString,p.toString,t.toString]
      return positive o
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
def openRuntime (n : Native) (context : Context) : IO Runtime := do
  let some (_,s) := restore context (← (storage n).read)
    | throw (IO.userError "invalid agreement journal")
  return ⟨n,context,s.now,(← IO.monoMsNow)⟩
def Runtime.now (r : Runtime) : IO Nat := do
  return r.logicalBase + ((← IO.monoMsNow) - r.monotonicBase)
/-- Network ingress admits ONLY authenticated protocol delivery, never checked,
offer, tick or arbitrary serialized controller inputs. -/
def receive (runtime : Runtime) (packet : Bytes) : IO Result := do
  let n := runtime.native
  let context := runtime.context
  let bytes ← (storage n).read
  let some (j,_) := restore context bytes | return .invalid
  let some (m,witness) ← authenticate n context j.self packet | return .invalid
  match witness with
  | some w => receiveCommitWitness (storage n) (crypto n) context bytes (← runtime.now) w
  | none => persist (storage n) context bytes (.deliveryAt (← runtime.now) m)
/-- A recovered certificate relays original transferable COMMIT sends. Pairwise
MAC authority is not promoted to another member's signature authority. -/
def receiveFinality (runtime : Runtime) (certificateBytes : Bytes) : IO Result := do
  let bytes ← (storage runtime.native).read
  receiveCommitment (storage runtime.native) (crypto runtime.native) runtime.context
    bytes (← runtime.now) certificateBytes
/-- Driver drains currently due authenticated arrivals and fair continuation
slices before firing a timer at the same timestamp. -/
def tick (runtime : Runtime) : IO Result := do
  let bytes ← (storage runtime.native).read
  persist (storage runtime.native) runtime.context bytes (.tick (← runtime.now))
def poll (runtime : Runtime) : IO Result := do
  let bytes ← (storage runtime.native).read
  persist (storage runtime.native) runtime.context bytes .poll
/-- Retry over fresh traffic envelopes is permitted. The retained inner
sender/view/kind/value is stable and idempotent at the receiving engine. -/
def outgoing (n : Native) (context : Context) : IO (List (Nat × Bytes)) := do
  let bytes ← (storage n).read
  let some (j,s) := restore context bytes | throw (IO.userError "invalid agreement journal")
  let mut packets := []
  for (sequence,m) in s.outbox.zipIdx |>.map (fun (m,i) => (i,m)) do
    for recipient in List.range context.config.parties do
      if recipient != j.self then
        let packet ← sealPacket n ⟨context,recipient,sequence,m⟩
        packets := packets ++ [(recipient,packet)]
  return packets
end Minidregg.Compiler.GenericSimplexNative
