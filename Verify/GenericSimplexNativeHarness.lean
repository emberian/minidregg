import Compiler.GenericSimplexNative
import Kernel.JointSimplexBinding
namespace Minidregg.Verify.GenericSimplexNativeHarness
open Minidregg.Compiler.GenericSimplexCodec
open Minidregg.Compiler.GenericSimplexIO
open Minidregg.Compiler.GenericSimplexNative
open Minidregg.Kernel.GenericSimplex
set_option autoImplicit false
def ensure (b : Bool) (why : String) : IO Unit :=
  if b then pure () else throw (IO.userError why)
def helper (binary : String) (args : Array String) : IO Unit := do
  let o ← IO.Process.output {cmd := binary,args := args}
  if o.exitCode != 0 || !o.stderr.isEmpty then throw (IO.userError s!"helper: {o.stderr}")
def state (n : Native) (c : Context) : IO State := do
  let some (_,s) := restore c (← (storage n).read) | throw (IO.userError "restore")
  return s
def freshPackets (n : Native) (c : Context) (cursor : Nat) : IO (Nat × List (Nat × Bytes)) := do
  let s ← state n c
  let mut packets := []
  for (m,index) in s.outbox.zipIdx do
    if index ≥ cursor then
      for recipient in List.range c.config.parties do
        if recipient != s.self && m.view == 1 then
          let p ← sealPacket n ⟨c,recipient,index,m⟩
          packets := packets ++ [(recipient,p)]
  return (s.outbox.length,packets)
def drive (binary : String) (nodes : Array Native) (runtimes : Array Runtime) (c : Context)
    (fuel : Nat) (cursors : Array Nat) (queue : List (Nat × Bytes)) : IO Unit := do
  match fuel with
  | 0 => throw (IO.userError "network fuel exhausted")
  | fuel+1 =>
    let states ← nodes.toList.mapM (fun n => state n c)
    if queue.isEmpty then
      ensure (states.all (fun s => !s.committedTip.isEmpty)) "network stalled"
      return
    let (recipient,packet)::rest := queue | throw (IO.userError "network stalled")
    let some node := nodes[recipient]? | throw (IO.userError "recipient")
    -- Every delivered packet actually crosses a framed TCP connection.
    let received ← IO.FS.withTempDir fun dir => do
      let p := dir / "sent"
      let q := dir / "received"
      writePrivate p packet.toByteArray
      helper binary #["tcp-hop",p.toString,q.toString]
      return (← IO.FS.readBinFile q).toList
    let some runtime := runtimes[recipient]? | throw (IO.userError "runtime")
    match ← receive runtime received with
    | .durable _ => pure ()
    | _ => throw (IO.userError "network receive not durable")
    let (cursor,outgoing) ← freshPackets node c cursors[recipient]!
    drive binary nodes runtimes c fuel (cursors.set! recipient cursor) (rest ++ outgoing)
/-- Byzantine test sender has its own real key, but may sign without following
the honest durable-send rule. This is deliberately confined to the harness. -/
def faultyCommitPacket (n : Native) (context : Context) (recipient : Nat) : IO Bytes :=
  IO.FS.withTempDir fun dir => do
    let signature ← (crypto n).sign (commitmentBytes context 1 [[]])
    let envelope : Envelope := ⟨context,recipient,0,⟨3,1,.commit,some [[]]⟩⟩
    let frame := dir / "frame"
    let tag := dir / "tag"
    writePrivate frame (authenticatedFrame envelope signature).toByteArray
    helper n.binary.toString #["mac",(n.pairKey recipient).toString,frame.toString,tag.toString]
    return packetStream.encode (wireBody envelope signature,(← IO.FS.readBinFile tag).toList)
def deliverTCP (binary : String) (runtime : Runtime) (packet : Bytes) : IO Unit :=
  IO.FS.withTempDir fun dir => do
    let sent := dir / "sent"
    let received := dir / "received"
    writePrivate sent packet.toByteArray
    helper binary #["tcp-hop",sent.toString,received.toString]
    match ← receive runtime (← IO.FS.readBinFile received).toList with
    | .durable _ => pure ()
    | _ => throw (IO.userError "selective delivery did not persist")
/-- Actual selective-Byzantine trace: A and B send COMMIT, C first disables,
and faulty D sends its COMMIT only to A. Exactly A doCommits. A recovers and
relays the q original COMMIT signatures without asking B or C to doCommit first. -/
def selectiveCommitRecovery (binary : String) (original : Array Native) (c : Context) : IO Unit := do
  let nodes := original.map (fun n => {n with journal := n.journal.toString ++ "-selective"})
  for i in List.range 4 do
    writePrivate nodes[i]!.journal (journalStream.encode (⟨c,i,0,[],[]⟩ : Journal)).toByteArray
  let runtimes ← nodes.mapM (fun n => openRuntime n c)
  match ← persist (storage nodes[2]!) c (← (storage nodes[2]!).read) (.tick 70) with
  | .durable _ => pure ()
  | _ => throw (IO.userError "C disable persistence")
  let proposal : Message := ⟨0,1,.propose,some [[]]⟩
  deliverTCP binary runtimes[1]! (← sealPacket nodes[0]! ⟨c,1,0,proposal⟩)
  for receiver in [0,1,2] do
    for voter in [0,1,3] do
      if receiver != voter then
        deliverTCP binary runtimes[receiver]!
          (← sealPacket nodes[voter]! ⟨c,receiver,0,⟨voter,1,.vote,some [[]]⟩⟩)
  for receiver in [0,1,2] do
    for sender in [0,1] do
      if receiver != sender then
        deliverTCP binary runtimes[receiver]!
          (← sealPacket nodes[sender]! ⟨c,receiver,0,⟨sender,1,.commit,some [[]]⟩⟩)
  deliverTCP binary runtimes[0]! (← faultyCommitPacket nodes[3]! c 0)
  let a ← state nodes[0]! c
  let b ← state nodes[1]! c
  let third ← state nodes[2]! c
  ensure ((viewAt a 1).committed == some [[]] &&
      (viewAt b 1).committed.isNone && (viewAt third 1).committed.isNone)
    "selective COMMIT counterexample not reached"
  ensure ((← exportCommitment (storage nodes[1]!) (crypto nodes[1]!) c 1 [[]]).isSome)
    "durable COMMIT sender incorrectly requires local doCommit"
  ensure ((← exportCommitment (storage nodes[2]!) (crypto nodes[2]!) c 1 [[]]).isNone)
    "disabled non-sender exported COMMIT"
  let some recovered ← recoverCommitment (storage nodes[0]!) (crypto nodes[0]!) c 1 [[]]
    | throw (IO.userError "one committed replica could not recover transferable certificate")
  -- Reopen the runtime: the witness is journaled, not ephemeral packet state.
  let restarted ← openRuntime nodes[0]! c
  let some recoveredAgain ← recoverCommitment (storage restarted.native) (crypto restarted.native) c 1 [[]]
    | throw (IO.userError "restart lost COMMIT witness")
  ensure (recoveredAgain.block == recovered.block) "restart changed recovered block"
  for receiver in [1,2] do
    match ← receiveFinality runtimes[receiver]! recovered.bytes with
    | .durable after =>
      ensure ((viewAt after 1).committed == some [[]]) "relayed quorum did not catch up"
    | _ => throw (IO.userError "recovered quorum import failed")
  IO.println "PASS selective COMMIT: exactly one local output, durable q-send certificate, restart and two-replica catchup"

def main (args : List String) : IO Unit := do
  let some binary := args.head? | throw (IO.userError "expected crypto helper path")
  let storageBinary := args[1]?.map System.FilePath.mk
  IO.FS.withTempDir fun dir => do
    let mut keys := []
    for i in List.range 4 do
      let pk := dir / s!"pk-{i}"
      let sk := dir / s!"sk-{i}"
      helper binary #["keygen",pk.toString,sk.toString]
      keys := keys ++ [(← IO.FS.readBinFile pk).toList]
      for j in List.range 4 do
        if i < j then helper binary #["mac-keygen",(dir / s!"pair-{i}-{j}").toString]
    let c : Context := ⟨[10],0,[20],⟨4,1,70,8⟩,keys⟩
    let nodes : Array Native := ((List.range 4).map fun i =>
      {binary := binary,storageBinary := storageBinary,
       journal := dir / s!"journal-{i}",signingKey := dir / s!"sk-{i}",
       pairKey := fun j => dir / s!"pair-{min i j}-{max i j}"}).toArray
    let mut queue := []
    let mut cursors := Array.replicate 4 0
    for i in List.range 4 do
      let some node := nodes[i]? | throw (IO.userError "node")
      let j : Journal := ⟨c,i,0,[],[]⟩
      writePrivate node.journal (journalStream.encode j).toByteArray
      let (cursor,packets) ← freshPackets node c 0
      cursors := cursors.set! i cursor
      queue := queue ++ packets
    let runtimes ← nodes.mapM (fun node => openRuntime node c)
    let some (recipient,packet) := queue.head? | throw (IO.userError "no initial packet")
    let some recipientNode := nodes[recipient]? | throw (IO.userError "recipient")
    let tampered := packet.dropLast ++ [if packet.getLast? == some 0 then 1 else 0]
    ensure ((← authenticate recipientNode c recipient tampered).isNone) "tampered MAC accepted"
    ensure ((← authenticate recipientNode {c with epoch := 1} recipient packet).isNone) "cross-epoch packet accepted"
    let some byzantine := nodes[3]? | throw (IO.userError "byzantine")
    let forged ← sealPacket byzantine ⟨c,recipient,0,⟨0,1,.vote,some [[]]⟩⟩
    ensure ((← authenticate recipientNode c recipient forged).isNone) "Byzantine peer forged honest sender"
    drive binary nodes runtimes c 1000 cursors queue
    let states ← nodes.toList.mapM (fun n => state n c)
    ensure (states.all fun s => s.committedTip == [[]]) "TCP four-node common commit"
    let mut attestations := []
    for node in nodes do
      let some a ← exportCommitment (storage node) (crypto node) c 1 [[]]
        | throw (IO.userError "durable export")
      attestations := attestations ++ [a]
    let cert : Certificate := ⟨c,1,[[]],attestations.take 3⟩
    let mut deliveries := 0
    let mut wireBytes := 0
    for s in states do
      for (m,index) in s.outbox.zipIdx do
        if m.view == 1 then
          for recipient in List.range c.config.parties do
            if recipient != s.self then
              deliveries := deliveries + 1
              let frame := wireBody ⟨c,recipient,index,m⟩
                (if m.kind == .commit then List.replicate 3309 0 else [])
              wireBytes := wireBytes + 8 + (packetStream.encode (frame,List.replicate 32 0)).length
    IO.println s!"SERIALIZED n=4 f=1 inert first view: TCP deliveries={deliveries}, framed bytes={wireBytes}, engine certificate bytes={(certificateStream.encode cert).length}; all continuation waves included"
    let some first := nodes[0]? | throw (IO.userError "first")
    ensure (← verifyCertificate (crypto first) c cert) "real PQ certificate"
    let some verified ← verifyCommitted (crypto first) c cert
      | throw (IO.userError "typed commitment verification")
    ensure (verified.context == c && verified.block == cert.block) "typed commitment changed scope/block"
    ensure (!(← verifyAttestations (crypto first) c
      (Minidregg.Kernel.JointSimplexBinding.sourceAppliedBytes c [7]) cert.signers))
      "engine commit signature accepted as source Applied"
    ensure (!(← verifyCertificate (crypto first) c {cert with block := [[99]]})) "tampered block accepted"
    ensure (!(← verifyCertificate (crypto first) c {cert with signers := [attestations[0]!,attestations[0]!,attestations[1]!] })) "duplicate signer accepted"
    -- Lost CAS reply/restart is reconstructed from the durable input/outbox.
    let prior ← (storage first).read
    let some (j,_) := restore c prior | throw (IO.userError "precrash restore")
    let next := journalStream.encode {j with events := j.events ++ [encodeInput (.tick 1000)]}
    IO.FS.withTempDir fun faultDir => do
      let e := faultDir / "expected"
      let p := faultDir / "next"
      writePrivate e prior.toByteArray
      writePrivate p next.toByteArray
      let lost ← IO.Process.output {cmd := (first.storageBinary.getD first.binary).toString, args := #["cas-lose-reply",first.journal.toString,e.toString,p.toString]}
      ensure (lost.exitCode != 0) "lost reply was not injected"
    ensure ((← (storage first).read) == next) "lost reply lost durable append"
    match ← persist (storage first) c prior (.tick 2000) with
    | .conflict => pure ()
    | _ => throw (IO.userError "stale CAS accepted")
    let recovered ← state first c
    ensure (!recovered.committedTip.isEmpty && !recovered.outbox.isEmpty) "crash replay lost decision/outbox"
    let resumed ← openRuntime first c
    ensure ((← resumed.now) ≥ recovered.now) "reboot clock moved backwards"
    selectiveCommitRecovery binary nodes c
    IO.println "PASS GenericSimplex native harness: four nodes, authenticated TCP packets, durable replay/CAS, real MLDSA65 quorum, tamper/duplicate rejection"
end Minidregg.Verify.GenericSimplexNativeHarness
def main (args : List String) : IO Unit :=
  Minidregg.Verify.GenericSimplexNativeHarness.main args
