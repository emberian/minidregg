import Compiler.GenericSimplexNative
import Kernel.JointSimplexBinding
namespace Minidregg.Verify.GenericSimplexNativeHarness
open Minidregg.Compiler.Tower256ConcreteBackend
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
def image (r : Runtime) : IO (Restored r.context) := do
  let some prior ← r.current | throw (IO.userError "restore")
  return prior
def state (r : Runtime) : IO State := return (← image r).state

/-- The single operation every scenario agrees on. A leader proposes only with
work, so each node first records the locally validated offer (the native
controller's `checked` grant, injected here as the harness's validator). -/
def opBlock : Block := [[7]]
def grantChecked (r : Runtime) : IO Unit := do
  match ← persist (storage r.native) r.context (.checked opBlock) with
  | .durable _ => pure ()
  | _ => throw (IO.userError "checked grant did not persist")

structure Keys where
  dir : System.FilePath
  binary : String

def spec (k : Keys) (i : Nat) (listen : Option String := none)
    (peers : List (Nat × String) := []) : HelperSpec :=
  { binary := k.binary
    signingKey := some (k.dir / s!"sk-{i}")
    listen := listen
    peers := peers
    pairKeys := ((List.range 4).filter (· != i)).map fun j => (j,k.dir / s!"pair-{min i j}-{max i j}") }

/-- Wait for the next verbatim frame at this replica's listener. -/
def await (r : Runtime) : IO Bytes := do
  for _ in List.range 500 do
    if let some frame := (← r.native.helper.receive 1).head? then return frame
    IO.sleep 10
  throw (IO.userError "persistent TCP frame did not arrive")

/-- Send over the sender's persistent connection; deliver at the recipient. -/
def hop (sender recipient : Runtime) (index : Nat) (packet : Bytes) : IO Result := do
  sender.native.helper.send index packet
  receive recipient (← await recipient)

/-- Every node seals its new view-1 outbox to every peer over its persistent
connections; every node then journals whatever arrived. -/
def drive (nodes : Array Runtime) (c : Context) (fuel : Nat) (cursors : Array Nat) : IO Unit := do
  match fuel with
  | 0 => throw (IO.userError "network fuel exhausted")
  | fuel+1 =>
    let states ← nodes.toList.mapM state
    if states.all (fun s => !s.committedTip.isEmpty) then return
    let mut cursors := cursors
    for i in List.range 4 do
      let s ← state nodes[i]!
      for (m,index) in s.outbox.zipIdx do
        if index ≥ cursors[i]! && m.view == 1 then
          for recipient in List.range 4 do
            if recipient != i then
              nodes[i]!.native.helper.send recipient (← sealPacket nodes[i]!.native ⟨c,recipient,index,m⟩)
      cursors := cursors.set! i s.outbox.length
    IO.sleep 20
    for i in List.range 4 do
      for frame in ← nodes[i]!.native.helper.receive 512 do
        match ← receive nodes[i]! frame with
        | .durable _ => pure ()
        | _ => throw (IO.userError "network receive not durable")
    drive nodes c fuel cursors

/-- Byzantine test sender has its own real key, but may sign without following
the honest durable-send rule. This is deliberately confined to the harness. -/
def faultyCommitPacket (n : Native) (context : Context) (recipient : Nat) : IO Bytes := do
  let signature ← (crypto n).sign (commitmentBytes context 1 opBlock)
  let envelope : Envelope := ⟨context,recipient,0,⟨3,1,.commit,some opBlock⟩⟩
  let tag ← n.helper.mac recipient (authenticatedFrame envelope signature)
  return packetStream.encode (wireBody envelope signature,tag)

def deliver (runtime : Runtime) (packet : Bytes) : IO Unit := do
  match ← receive runtime packet with
  | .durable _ => pure ()
  | _ => throw (IO.userError "selective delivery did not persist")

/-- Actual selective-Byzantine trace: A and B send COMMIT, C first disables,
and faulty D sends its COMMIT only to A. Exactly A doCommits. A recovers and
relays the q original COMMIT signatures without asking B or C to doCommit first.
Selective delivery is injected in-process; the TCP path is exercised above. -/
def selectiveCommitRecovery (k : Keys) (base : Context) : IO Unit := do
  -- Independent test execution: fresh journals must never reset an existing
  -- committee instance while reusing its signed protocol identity.
  let c := {base with instanceBytes := base.instanceBytes ++ [83,69,76,69,67,84]}
  let journal := fun (i : Nat) => k.dir / s!"journal-{i}-selective"
  for i in List.range 4 do
    createJournal k.binary (journal i) ⟨c,i,0,[],[],none⟩
  let nodes ← (List.range 4).toArray.mapM fun i => openRuntime (spec k i) (journal i) c
  match ← persist (storage nodes[2]!.native) c (.tick 70) with
  | .durable _ => pure ()
  | _ => throw (IO.userError "C disable persistence")
  for node in nodes do grantChecked node
  let proposal : Message := ⟨0,1,.propose,some opBlock⟩
  deliver nodes[1]! (← sealPacket nodes[0]!.native ⟨c,1,0,proposal⟩)
  for receiver in [0,1,2] do
    for voter in [0,1,3] do
      if receiver != voter then
        deliver nodes[receiver]!
          (← sealPacket nodes[voter]!.native ⟨c,receiver,0,⟨voter,1,.vote,some opBlock⟩⟩)
  for receiver in [0,1,2] do
    for sender in [0,1] do
      if receiver != sender then
        deliver nodes[receiver]!
          (← sealPacket nodes[sender]!.native ⟨c,receiver,0,⟨sender,1,.commit,some opBlock⟩⟩)
  deliver nodes[0]! (← faultyCommitPacket nodes[3]!.native c 0)
  let a ← state nodes[0]!
  let b ← state nodes[1]!
  let third ← state nodes[2]!
  ensure ((viewAt a 1).committed == some opBlock &&
      (viewAt b 1).committed.isNone && (viewAt third 1).committed.isNone)
    "selective COMMIT counterexample not reached"
  ensure ((← exportCommitment (storage nodes[1]!.native) (crypto nodes[1]!.native) c 1 opBlock).isSome)
    "durable COMMIT sender incorrectly requires local doCommit"
  ensure ((← exportCommitment (storage nodes[2]!.native) (crypto nodes[2]!.native) c 1 opBlock).isNone)
    "disabled non-sender exported COMMIT"
  let some recovered ← recoverCommitment (storage nodes[0]!.native) (crypto nodes[0]!.native) c 1 opBlock
    | throw (IO.userError "one committed replica could not recover transferable certificate")
  -- Reopen the runtime: the witness is journaled, not ephemeral packet state.
  nodes[0]!.close
  let restarted ← openRuntime (spec k 0) (journal 0) c
  let some recoveredAgain ← recoverCommitment (storage restarted.native) (crypto restarted.native) c 1 opBlock
    | throw (IO.userError "restart lost COMMIT witness")
  ensure (recoveredAgain.block == recovered.block) "restart changed recovered block"
  for receiver in [1,2] do
    match ← receiveFinality nodes[receiver]! recovered.bytes with
    | .durable after =>
      ensure ((viewAt after 1).committed == some opBlock) "relayed quorum did not catch up"
    | _ => throw (IO.userError "recovered quorum import failed")
  -- A repeated certificate must leave the durable log untouched, while the
  -- first certificate above had to retain the previously missing witness.
  let oldLength := (← IO.FS.readBinFile (journal 2)).size
  nodes[2]!.close
  let reopened ← openRuntime (spec k 2) (journal 2) c
  match ← receiveFinality reopened recovered.bytes with
  | .durable _ => pure ()
  | _ => throw (IO.userError "duplicate finality acknowledgement refused")
  ensure ((← IO.FS.readBinFile (journal 2)).size == oldLength)
    "duplicate certificate grew the durable journal"
  for r in [restarted,reopened,nodes[1]!,nodes[3]!] do r.close
  IO.println "PASS duplicate certificate: cold restart retains exact journal, late first witness still catches up"
  IO.println "PASS selective COMMIT: exactly one local output, durable q-send certificate, restart and two-replica catchup"

def persistTick (r : Runtime) (time : Nat) : IO Unit := do
  match ← persist (storage r.native) r.context (.tick time) with
  | .durable _ => pure ()
  | _ => throw (IO.userError "tick did not persist")

/-- Checkpoint through the real writer: the image becomes one snapshot frame
with the same state, the replaced image stays as the previous segment, appends
continue, a reopen replays only the later deltas, a stale replace conflicts. -/
def checkpointJournal (k : Keys) (c : Context) : IO Unit := do
  let path := k.dir / "journal-checkpoint"
  createJournal k.binary path ⟨c,0,0,[],[],none⟩
  let r ← openRuntime (spec k 0) path c
  for t in List.range 5 do persistTick r (1000 * (t + 1))
  let before ← image r
  let oldBytes := (← IO.FS.readBinFile path).toList
  match ← checkpoint (storage r.native) c with
  | .durable => pure ()
  | _ => throw (IO.userError "checkpoint refused")
  let after ← image r
  ensure (after.state == before.state && after.log.recent.isEmpty &&
      after.log.base.snapshot == some before.state) "checkpoint changed the engine state"
  ensure ((← IO.FS.readBinFile (System.FilePath.mk (path.toString ++ s!".upto-{before.length}"))).toList == oldBytes)
    "replaced image not kept as the previous segment"
  ensure ((← IO.FS.readBinFile path).toList == after.log.encode) "checkpoint image differs on disk"
  persistTick r 9000
  let continued ← state r
  r.close
  let reopened ← openRuntime (spec k 0) path c
  ensure ((← state reopened) == continued) "reopen after checkpoint changed the state"
  ensure ((← image reopened).log.recent.length == 1) "reopen replayed more than the post-checkpoint delta"
  match ← (storage reopened.native).replace before.length [1,2,3] with
  | .conflict => pure ()
  | _ => throw (IO.userError "stale checkpoint accepted")
  reopened.close
  -- The retained history audits as a chain; the live image alone does not.
  let live := (← IO.FS.readBinFile path).toList
  match auditSegments c [oldBytes,live] with
  | .ok audited => ensure (audited == continued) "audited history ends at a different state"
  | .error detail => throw (IO.userError s!"retained history did not audit: {detail}")
  match auditSegments c [live] with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError "a checkpoint alone audited as a whole history")
  match auditSegments c [oldBytes,oldBytes] with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError "a broken segment chain audited")
  IO.println "PASS checkpoint: one snapshot frame with the same state, previous segment kept, appends continue, reopen replays only later deltas, stale replace conflicts"

/-- Append-only journal faults: an acknowledged append whose reply was lost is
replayed on reopen; a torn unacknowledged tail is removed only on a writable
open; a stale expected length conflicts; a complete corrupt frame, a legacy
whole image, or a different context never opens. -/
def journalFaults (k : Keys) (c : Context) : IO Unit := do
  let path := k.dir / "journal-faults"
  createJournal k.binary path ⟨c,0,0,[],[],none⟩
  let r ← openRuntime (spec k 0) path c
  let prior ← image r
  let some (next,frame) := appendRestored prior [encodeInput (.tick 1000)] []
    | throw (IO.userError "append continuation refused")
  -- Lost reply: the frame reached the disk, the writer died before replying.
  r.close
  let h ← IO.FS.Handle.mk path .append
  h.write frame.toByteArray
  h.flush
  let reopened ← openRuntime (spec k 0) path c
  ensure ((← state reopened) == next.state) "lost reply lost the durable append"
  -- Stale writer: an append at the old length conflicts and drops the image.
  match ← (storage reopened.native).append prior.length frame with
  | .conflict => pure ()
  | _ => throw (IO.userError "stale append accepted")
  ensure ((← IO.FS.readBinFile path).size == next.length) "stale append changed the log"
  reopened.close
  -- Torn tail: half of a further frame. Read-only ignores it; writable truncates it.
  let some (_,more) := appendRestored next [encodeInput (.tick 2000)] []
    | throw (IO.userError "second continuation refused")
  let torn ← IO.FS.Handle.mk path .append
  torn.write (more.take (more.length / 2)).toByteArray
  torn.flush
  let readOnly ← openRuntime (spec k 0) path c (writable := false)
  ensure ((← state readOnly) == next.state) "torn tail changed read-only state"
  readOnly.close
  let writer ← openRuntime (spec k 0) path c
  ensure ((← IO.FS.readBinFile path).size == next.length) "torn tail not removed by the writer"
  writer.close
  -- Corruption: a complete frame whose payload is not a Delta never opens.
  let corrupt ← IO.FS.Handle.mk path .append
  corrupt.write (bytesStream.encode [7,7,7]).toByteArray
  corrupt.flush
  let refused ← try
      let _ ← openRuntime (spec k 0) path c
      pure false
    catch _ => pure true
  ensure refused "complete corrupt frame opened"
  -- A legacy whole-image journal and a crossed context never open.
  let legacy := k.dir / "journal-legacy"
  writePrivate legacy (journalStream.encode (⟨c,0,0,[],[],none⟩ : Journal)).toByteArray
  let legacyRefused ← try
      let _ ← openRuntime (spec k 0) legacy c
      pure false
    catch _ => pure true
  ensure legacyRefused "legacy whole-image journal opened as a log"
  let fresh := k.dir / "journal-context"
  createJournal k.binary fresh ⟨c,0,0,[],[],none⟩
  let crossed ← try
      let _ ← openRuntime (spec k 0) fresh {c with epoch := c.epoch + 1}
      pure false
    catch _ => pure true
  ensure crossed "journal opened under a different exact context"
  -- Exclusive writer: a second writable open of a held journal refuses.
  let held ← openRuntime (spec k 0) fresh c
  let second ← try
      let _ ← openRuntime (spec k 0) fresh c
      pure false
    catch _ => pure true
  ensure second "second writer opened a held journal"
  held.close
  IO.println "PASS append-only journal: lost reply replayed, stale append conflicts, torn tail removed only by the writer, corrupt/legacy/crossed-context logs refused, single writer"

def main (args : List String) : IO Unit := do
  let some binary := args.head? | throw (IO.userError "expected crypto helper path")
  IO.FS.withTempDir fun dir => do
    let mut keys := []
    for i in List.range 4 do
      let pk := dir / s!"pk-{i}"
      let sk := dir / s!"sk-{i}"
      helper binary #["keygen",pk.toString,sk.toString]
      keys := keys ++ [(← IO.FS.readBinFile pk).toList]
      for j in List.range 4 do
        if i < j then helper binary #["mac-keygen",(dir / s!"pair-{i}-{j}").toString]
    let k : Keys := ⟨dir,binary⟩
    let c : Context := ⟨[10],0,[20],⟨4,1,70,8,3⟩,keys⟩
    let base := 20000 + (← IO.monoMsNow) % 30000
    let address := fun (i : Nat) => s!"127.0.0.1:{base + i}"
    for i in List.range 4 do
      createJournal binary (dir / s!"journal-{i}") ⟨c,i,0,[],[],none⟩
    let nodes ← (List.range 4).toArray.mapM fun i =>
      openRuntime (spec k i (some (address i))
        (((List.range 4).filter (· != i)).map fun j => (j,address j))) (dir / s!"journal-{i}") c
    for node in nodes do grantChecked node
    let s1 ← state nodes[0]!
    let some first := s1.outbox.head? | throw (IO.userError "no initial message")
    let packet ← sealPacket nodes[0]!.native ⟨c,1,0,first⟩
    let tampered := packet.dropLast ++ [if packet.getLast? == some 0 then 1 else 0]
    ensure ((← authenticate nodes[1]!.native c 1 tampered).isNone) "tampered MAC accepted"
    ensure ((← authenticate nodes[1]!.native {c with epoch := 1} 1 packet).isNone) "cross-epoch packet accepted"
    let forged ← sealPacket nodes[3]!.native ⟨c,1,0,⟨0,1,.vote,some opBlock⟩⟩
    ensure ((← authenticate nodes[1]!.native c 1 forged).isNone) "Byzantine peer forged honest sender"
    drive nodes c 2000 (Array.replicate 4 0)
    let states ← nodes.toList.mapM state
    ensure (states.all fun s => s.committedTip == opBlock) "TCP four-node common commit"
    IO.println "PASS persistent TCP four-node commit: one long-lived helper per node, authenticated packets, append-only journals"
    let senderState ← state nodes[0]!
    let some vote := senderState.outbox.find? (fun message => message.kind == .vote && message.view == 1)
      | throw (IO.userError "missing real durable vote")
    let beforeDuplicate := (← image nodes[1]!).length
    match ← hop nodes[0]! nodes[1]! 1 (← sealPacket nodes[0]!.native ⟨c,1,0,vote⟩) with
    | .durable _ => pure ()
    | _ => throw (IO.userError "duplicate vote refused")
    ensure ((← image nodes[1]!).length == beforeDuplicate &&
        (← IO.FS.readBinFile (dir / "journal-1")).size == beforeDuplicate)
      "duplicate authenticated vote grew the journal"
    IO.println "PASS duplicate authenticated vote: actual TCP/MAC, durable log unchanged"

    -- Application availability uses a separate authenticated domain. The peer
    -- persists offers and never receives a source-validation grant over wire.
    let candidate : Block := [[90],[91]]
    let envelope ← sealCandidate nodes[0]! 1 candidate
    ensure ((← authenticateCandidate nodes[1]!.native {c with epoch := 1} 1 envelope).isNone)
      "candidate crossed exact context"
    ensure ((← authenticateCandidate nodes[1]!.native c 2 envelope).isNone)
      "candidate crossed recipient"
    let corrupted := envelope.dropLast ++ [if envelope.getLast? == some 0 then 1 else 0]
    ensure ((← authenticateCandidate nodes[1]!.native c 1 corrupted).isNone)
      "candidate MAC tamper accepted"
    let beforeCandidate ← state nodes[1]!
    nodes[0]!.native.helper.send 1 envelope
    let arrived ← await nodes[1]!
    let (accepted,body) ← receiveCandidate nodes[1]! arrived
    match accepted with
    | .durable after =>
      ensure (body == some candidate && after.checked == beforeCandidate.checked)
        "candidate became a checked grant"
      ensure (candidate.all after.offers.contains) "candidate records not retained"
    | _ => throw (IO.userError "authenticated candidate did not persist")
    let durableCandidate := (← IO.FS.readBinFile (dir / "journal-1")).size
    let (again,_) ← receiveCandidate nodes[1]! arrived
    match again with
    | .durable _ => pure ()
    | _ => throw (IO.userError "candidate retry refused")
    ensure ((← IO.FS.readBinFile (dir / "journal-1")).size == durableCandidate)
      "candidate retransmission grew journal"
    IO.println "PASS candidate relay: actual TCP, context/recipient/MAC binding, durable unvalidated offers and retransmission dedup"
    let mut attestations := []
    for node in nodes do
      let some a ← exportCommitment (storage node.native) (crypto node.native) c 1 opBlock
        | throw (IO.userError "durable export")
      attestations := attestations ++ [a]
    let cert : Certificate := ⟨c,1,opBlock,attestations.take 3⟩
    let firstNative := nodes[0]!.native
    ensure (← verifyCertificate (crypto firstNative) c cert) "real PQ certificate"
    let some verified ← verifyCommitted (crypto firstNative) c cert
      | throw (IO.userError "typed commitment verification")
    ensure (verified.context == c && verified.block == cert.block) "typed commitment changed scope/block"
    ensure (!(← verifyAttestations (crypto firstNative) c
      (Minidregg.Kernel.JointSimplexBinding.sourceAppliedBytes c [7]) cert.signers))
      "engine commit signature accepted as source Applied"
    ensure (!(← verifyCertificate (crypto firstNative) c {cert with block := [[99]]})) "tampered block accepted"
    ensure (!(← verifyCertificate (crypto firstNative) c {cert with signers := [attestations[0]!,attestations[0]!,attestations[1]!] })) "duplicate signer accepted"
    let recovered ← state nodes[0]!
    ensure (!recovered.committedTip.isEmpty && !recovered.outbox.isEmpty) "decision/outbox missing"
    nodes[0]!.close
    let resumed ← openRuntime (spec k 0) (dir / "journal-0") c
    ensure ((← state resumed) == recovered) "restart replay changed the engine state"
    ensure ((← resumed.now) ≥ recovered.now) "reboot clock moved backwards"
    resumed.close
    for i in [1,2,3] do nodes[i]!.close
    journalFaults k c
    checkpointJournal k c
    selectiveCommitRecovery k c
    IO.println "PASS GenericSimplex native harness: four nodes, persistent authenticated TCP, append-only durable replay, real MLDSA65 quorum, tamper/duplicate rejection"
end Minidregg.Verify.GenericSimplexNativeHarness
def main (args : List String) : IO Unit :=
  Minidregg.Verify.GenericSimplexNativeHarness.main args
