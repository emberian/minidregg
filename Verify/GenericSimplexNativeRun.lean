import Compiler.GenericSimplexNative
/-!
The native agreement layer, executed in one process without the Rust helper: four replicas'
`Runtime`s over in-memory journals, every message sealed (`sealPacket`), authenticated
(`authenticate`), journalled (`receiveDelivery`, `receiveCommit`) and drained (`Entry.flush`)
exactly as a standing replica does it. Called by `generic-simplex-harness`.

The helper session is a stand-in (`stubHelper`): a signature is cSHAKE256 of the signer's
index and the signed bytes, a MAC is cSHAKE256 of the pair and the body. It is not
cryptography. It makes the layer's own checks executable: which member's signature a COMMIT
leaves with, which statement it is over, whose MAC covers which envelope.

Not covered here: the participant's source side (`GenericSimplexParticipant.applyNext`,
validation, the request spool), which needs four native source stores.
-/
namespace Minidregg.Verify.GenericSimplexNativeRun
open Minidregg.Compiler.GenericSimplexCodec
open Minidregg.Compiler.GenericSimplexIO
open Minidregg.Compiler.GenericSimplexNative
open Minidregg.Kernel.GenericSimplex
open Minidregg.Kernel.GenericSimplexRelative
set_option autoImplicit false

def context : Context :=
  ⟨[1,2,3], 0, [4,5,6], ⟨4,1,100000000,64,0⟩,
    (List.range 4).map fun i => List.replicate 1952 (UInt8.ofNat (i + 1))⟩

def stubSign (signer : Nat) (bytes : List UInt8) : List UInt8 :=
  let digest := (Minidregg.Compiler.Sp800185Cshake256.hash [115] (UInt8.ofNat signer :: bytes)).bytes
  digest ++ List.replicate (3309 - digest.length) (UInt8.ofNat signer)

def stubMac (left right : Nat) (body : List UInt8) : List UInt8 :=
  (Minidregg.Compiler.Sp800185Cshake256.hash [109]
    (UInt8.ofNat (min left right) :: UInt8.ofNat (max left right) :: body)).bytes

def stubHelper (self : Nat) : Helper where
  call op body := do
    if op == opSign then
      return (0, (stubSign self (body.extract 4 body.size).toList).toByteArray)
    else if op == opVerify then
      let keySize := readBE body 0 4
      let signed := readBE body (4 + keySize) 4
      let frame := body.extract (8 + keySize) (8 + keySize + signed)
      let signature := body.extract (12 + keySize + signed) body.size
      let signer := (body.get! 4).toNat - 1
      return (if signature.toList == stubSign signer frame.toList then 0 else 1, ByteArray.empty)
    else if op == opMac then
      return (0, (stubMac self (readBE body 0 4) (body.extract 8 body.size).toList).toByteArray)
    else if op == opVerifyMac then
      let size := readBE body 4 4
      let tag := body.extract (12 + size) body.size
      return (if tag.toList == stubMac self (readBE body 0 4) (body.extract 8 (8 + size)).toList then 0 else 1,
        ByteArray.empty)
    else if op == opAppend || op == opReplace then return (0, ByteArray.empty)
    else return (2, "unsupported".toUTF8)
  close := pure ()

def ensure (condition : Bool) (message : String) : IO Unit :=
  if condition then pure () else throw (IO.userError message)

def openStub (index : Nat) : IO Runtime := do
  let some restored := openRestored context (Log.encode ⟨⟨context,index,0,[],[],none⟩,[]⟩)
    | throw (IO.userError "native run: base journal refused")
  let helper := stubHelper index
  let storage ← journalStorage helper true ⟨context,restored⟩
  return ⟨⟨"stub",helper,storage,{binary := "stub"},true⟩,context,0,(← IO.monoMsNow)⟩

def durable (result : Result) : Bool :=
  match result with
  | .durable _ => true
  | _ => false

def refused (result : Result) : Bool :=
  match result with
  | .invalid => true
  | _ => false

def stateOf (runtime : Runtime) : IO (Restored context) := do
  let some prior ← Minidregg.Compiler.GenericSimplexIO.current (storage runtime.native) context
    | throw (IO.userError "native run: journal image lost")
  return prior

/-- One operation through four native replicas, and the checks a COMMIT packet must pass. -/
def run : IO Unit := do
  let mut nodes : Array Runtime := #[]
  for index in List.range 4 do nodes := nodes.push (← openStub index)
  for node in nodes do
    ensure (durable (← persist (storage node.native) context (.input (.checked 0 [[7]]))))
      "native run: the checked input was refused"
  let mut probed := false
  let mut sealed := 0
  for _ in List.range 32 do
    let mut packets : List (Nat × ByteArray) := []
    for index in List.range 4 do
      let some node := nodes[index]? | throw (IO.userError "native run: replica index")
      let prior ← stateOf node
      let replica := prior.state
      let outputs := replica.sends.flatMap (fun m =>
        ((List.range 4).filter (· != index)).map fun peer => (peer,m)) ++ replica.owed
      for (peer,message) in outputs do
        let some proof ← messageProof node.native context message
          | throw (IO.userError "native run: a message of the durable output has no proof")
        if message.kind == .commit && !probed then
          probed := true
          let next := (index + 1) % 4
          let third := (index + 2) % 4
          let some receiver := nodes[next]? | throw (IO.userError "native run: replica index")
          let some other := nodes[third]? | throw (IO.userError "native run: replica index")
          let some (length,digest) := message.statement
            | throw (IO.userError "native run: a COMMIT left without its statement")
          -- Another member's signature on the same statement does not make this COMMIT.
          let foreign ← (crypto receiver.native).sign (commitStatementBytes context message.view length digest)
          ensure (refused (← receive receiver
              (← sealPacket node.native ⟨context,index,next,message⟩ foreign)))
            "native run: a COMMIT was taken with another member's signature"
          -- A packet whose MAC does not cover it is dropped.
          let genuine ← sealPacket node.native ⟨context,index,next,message⟩ proof
          ensure (refused (← receive receiver
              (genuine.set! (genuine.size - 1) (genuine.get! (genuine.size - 1) ^^^ 1))))
            "native run: a packet with a broken MAC was taken"
          let before := (← stateOf receiver).length
          ensure (durable (← receive receiver genuine)) "native run: a genuine COMMIT was refused"
          let after ← stateOf receiver
          ensure (before < after.length && after.witnesses.any (·.signs message))
            "native run: a counted COMMIT was journalled without its signature"
          -- The receiver passes the COMMIT on under its own MAC, with the signer's signature.
          let some kept ← messageProof receiver.native context message
            | throw (IO.userError "native run: a received COMMIT cannot be passed on")
          ensure (kept == proof) "native run: the kept signature is not the signer's"
          let seen := (← stateOf other).length
          ensure (durable (← receive other
              (← sealPacket receiver.native ⟨context,next,third,message⟩ kept)))
            "native run: a relayed COMMIT was refused"
          ensure (seen < (← stateOf other).length) "native run: a relayed COMMIT was not counted"
          -- A message that is not a COMMIT may not be passed on.
          ensure (refused (← receive other (← sealPacket receiver.native
              ⟨context,next,third,{ message with kind := .vote, statement := none }⟩ [])))
            "native run: a VOTE was taken from a member that is not its sender"
        packets := (peer,← sealPacket node.native ⟨context,index,peer,message⟩ proof) :: packets
      if !outputs.isEmpty then
        ensure (durable (← persist (storage node.native) context
            (.flush replica.sends.length replica.owed.length)))
          "native run: the drain was refused"
    if packets.isEmpty then break
    sealed := sealed + packets.length
    for (peer,packet) in packets.reverse do
      let some node := nodes[peer]? | throw (IO.userError "native run: replica index")
      ensure (durable (← receive node packet)) "native run: an honest packet was refused"
  ensure probed "native run: no COMMIT was sent"
  for node in nodes do
    let prior ← stateOf node
    ensure (prior.state.height == 1 && prior.state.committed == [[7]] && prior.state.records == 1)
      "native run: a replica did not commit the operation"
    ensure (prior.state.sends.isEmpty && prior.state.owed.isEmpty)
      "native run: a replica kept output it had handed to its transport"
    -- The journal is the replica: its image reopens to the same state.
    let some reopened := openRestored context prior.log.encode
      | throw (IO.userError "native run: a journal does not reopen")
    ensure (reopened.state == prior.state) "native run: a journal reopens to another state"
    -- A checkpoint is the live replica, and reopens to it.
    let (checkpointed,image) := checkpointRestored prior
    let some again := openRestored context image
      | throw (IO.userError "native run: a checkpoint does not reopen")
    ensure (again.state == prior.state && checkpointed.witnesses.length ≥ 2)
      "native run: a checkpoint lost the replica or the signatures of its newest commit"
  let some first := nodes[0]? | throw (IO.userError "native run: replica index")
  let some certificate ← recoverCommitment (storage first.native) (crypto first.native) context
    | throw (IO.userError "native run: no certificate for the newest commit")
  ensure (certificate.view == 1 && certificate.length == 1 && certificate.signerIds.length ≥ 3)
    "native run: the certificate is not a quorum on the commit's statement"
  ensure (decide (certificate.Reads [[7]]) && !decide (certificate.Reads [[8]]))
    "native run: the certificate does not bind the committed history"
  IO.println s!"PASS native layer: four replicas, {sealed} sealed packets, one certificate of {certificate.signerIds.length} signatures on the statement, no chain carried"

end Minidregg.Verify.GenericSimplexNativeRun
