import Compiler.GenericSimplexParticipant
namespace Minidregg.Verify.GenericSimplexSourceHarness
open Minidregg.Kernel.GenericSimplex
open Minidregg.Compiler.GenericSimplexCodec
open Minidregg.Compiler.GenericSimplexNative
open Minidregg.Compiler.GenericSimplexParticipant
set_option autoImplicit false

/-- Each replica has its own physical storage configuration. Common source
semantics and committee are checked separately from those local paths/MAC keys. -/
structure Replica where
  config : SourceConfig
  participant : Participant config

def require (condition : Bool) (detail : String) : IO Unit :=
  unless condition do throw (IO.userError detail)

def crossTCP (binary : System.FilePath) (packet : Bytes) : IO Bytes :=
  IO.FS.withTempDir fun dir => do
    let sent := dir / "sent"
    let received := dir / "received"
    writePrivate sent packet.toByteArray
    let result ← IO.Process.output {cmd := binary.toString,
      args := #["tcp-hop",sent.toString,received.toString]}
    if result.exitCode != 0 || !result.stderr.isEmpty then
      throw (IO.userError ("actual TCP exchange failed: " ++ result.stderr))
    return (← IO.FS.readBinFile received).toList

def drive (fuel : Nat) (replicas : Array Replica) (payload : Bytes)
    (packets : List (Nat × Bytes)) : IO (Array Replica) := do
  match fuel with
  | 0 => throw (IO.userError "native source agreement exhausted finite harness service")
  | fuel+1 =>
    if replicas.toList.all (fun r => (completedReceipt r.participant payload).isSome) then
      return replicas
    let mut replicas := replicas
    let mut later := packets
    -- Drain a bounded batch before local timers, so retransmission does not
    -- create a harness-only one-packet bottleneck behind fresh fanout.
    for _ in List.range 64 do
      if let (recipient,packet)::rest := later then
        let some replica := replicas[recipient]? | throw (IO.userError "unknown recipient")
        let delivered ← crossTCP replica.participant.runtime.native.binary packet
        let (participant,result) ← Minidregg.Compiler.GenericSimplexParticipant.receive
          replica.participant delivered
        match result with
        | .durable _ => pure ()
        | _ => throw (IO.userError "native participant ingress was not durable")
        replicas := replicas.set! recipient ⟨replica.config,participant⟩
        later := rest
    for index in List.range replicas.size do
      let some replica := replicas[index]? | throw (IO.userError "replica index")
      let (participant,outgoing,_,_) ← service replica.participant 1 4 1
      replicas := replicas.set! index ⟨replica.config,participant⟩
      later := later ++ outgoing
    drive fuel replicas payload later

/-- First real source consumer accepts initialized, source-verified replicas and
a real signed ingress from the source fixture owner. It checks exact replicated
record bytes and actual native source receipts. There is no toy policy or
placeholder signature/validation callback in this driver. The factory/CLI fixture
must initialize four independent stores before calling this function. -/
def run (fuel : Nat) (replicas : Array Replica) (signedIngress : Bytes) : IO (Array Replica) := do
  require (replicas.size == 4) "source harness requires n=4 replicas"
  let some first := replicas[0]? | throw (IO.userError "missing first replica")
  require (first.participant.runtime.context.config.parties == 4 &&
    first.participant.runtime.context.config.faults == 1) "source harness requires n4/f1"
  for replica in replicas do
    require (replica.participant.runtime.context == first.participant.runtime.context)
      "replicas use different exact contexts"
    require (replica.participant.source.verified.opened.durable.image ==
      first.participant.source.verified.opened.durable.image) "replicas start at different source histories"
  let before := replicas
  let initialCount := first.participant.source.verified.opened.durable.image.accepted.length
  let (participant,proposal) ← propose first.participant signedIngress
  let payload ← match proposal with
    | .ok payload => pure payload
    | .error detail => throw (IO.userError ("actual ordinary admission refused: " ++ detail))
  let replicas := replicas.set! 0 ⟨first.config,participant⟩
  let finished ← drive fuel replicas payload []
  let some final := finished[0]? | throw (IO.userError "missing final replica")
  for replica in finished do
    require (replica.participant.source.verified.opened.durable.image ==
      final.participant.source.verified.opened.durable.image) "source replicas diverged"
    require ((completedReceipt replica.participant payload).isSome)
      "engine output occurred without actual source receipt"
  -- Deliberately lose all caller completion responses and volatile participant
  -- state. Reopen protocol journals from the original fixture state, then load
  -- and reverify actual physical source stores. Nothing resubmits the mutation.
  let mut restarted : Array Replica := #[]
  for original in before do
    let opened ← openParticipant original.config original.participant.runtime.native
      original.participant.runtime.context original.participant.source
    let participant ← match opened with
      | .ok participant => pure participant
      | .error detail => throw (IO.userError ("protocol restart refused: " ++ detail))
    let (participant,_) ← reloadSource participant
    require ((completedIngress participant signedIngress).isSome)
      "lost-response recovery lacks exact original-ingress receipt"
    require (participant.source.verified.opened.durable.image.accepted.length == initialCount + 1)
      "lost-response recovery did not preserve exactly one append"
    require (participant.source.verified.opened.durable.image ==
      final.participant.source.verified.opened.durable.image) "restart source readback differs"
    restarted := restarted.push ⟨original.config,participant⟩
  IO.println "PASS source lost-response/restart: four independently reread stores, original signed-ingress receipts, exactly one append"
  IO.println "PASS actual source agreement: four independent configured receivers, real admission/replay, TCP, exact common record, physical source readback receipts"
  return restarted
end Minidregg.Verify.GenericSimplexSourceHarness
