/- Executable lifecycle probe for the INTERNAL durable receiver.

These are bound durable-intent fixtures, not a claim that their mutations are
authorized resource effects. Production ResourceBirthController supplies that
separate accepted-effect join. The probe runs the actual Lean codec/executor,
native SQLite CAS, process-exit crash hooks, and cold byte readback together.
-/
import Compiler.DurableReceiverIO
import Compiler.Sp800185Cshake256

open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.ResourceCost
open Minidregg.Kernel
open Minidregg.Kernel.DurableDataIntent
open Minidregg.Kernel.DurableReceiver
open Minidregg.Compiler
open Minidregg.Compiler.DurableReceiverCodec
open Minidregg.Compiler.DurableReceiverIO

namespace DurableReceiverProbe

def rootBytes (bytes : List UInt8) : Digest :=
  (Sp800185Cshake256.hash "DREGG.DURABLE.RECEIVER.PROBE/v1".toUTF8.toList bytes).digest

def seed : Seed :=
  { absentBytes := []
    cells := [(⟨1⟩, [1]), (⟨2⟩, [2]), (⟨3⟩, [3])]
    available := fun _ => 100 }

def nullifier (number : Nat) : StableNullifier :=
  ⟨1, ⟨700⟩, ⟨number⟩, [UInt8.ofNat number]⟩

def event (number : Nat) : StableEvent :=
  ⟨1, ⟨800⟩, ⟨number⟩, [UInt8.ofNat number]⟩

def twoWrites (number : Nat) (oldA oldB newA newB observed : List UInt8) :
    DataIntent rootBytes where
  transactionId := ⟨number⟩
  writes :=
    [⟨⟨1⟩, rootBytes oldA, rootBytes newA, newA⟩,
     ⟨⟨2⟩, rootBytes oldB, rootBytes newB, newB⟩]
  readGuards := [⟨⟨3⟩, rootBytes observed⟩]
  nullifiers := [nullifier number]
  exactCharge := fun _ => 1
  event := event number
  postRootsBound := by simp
  guardsReadOnly := by simp

def moveObserved (number : Nat) (old new : List UInt8) : DataIntent rootBytes where
  transactionId := ⟨number⟩
  writes := [⟨⟨3⟩, rootBytes old, rootBytes new, new⟩]
  readGuards := []
  nullifiers := [nullifier number]
  exactCharge := fun _ => 1
  event := event number
  postRootsBound := by simp
  guardsReadOnly := by simp

def require (label : String) (condition : Bool) : IO Unit :=
  unless condition do throw (IO.userError s!"FAIL durable receiver: {label}")

def confirmed (label : String) (kind : Confirmation) (result : Result rootBytes) :
    IO (DataSnapshot rootBytes) :=
  match result with
  | .confirmed actual snapshot => do
      require (label ++ ": confirmation kind") (actual == kind)
      return snapshot
  | .rejected reason => throw (IO.userError s!"FAIL {label}: rejected {repr reason}")
  | .unavailable detail => throw (IO.userError s!"FAIL {label}: unavailable {detail}")
  | .uncertain detail => throw (IO.userError s!"FAIL {label}: uncertain {detail}")
  | .contention => throw (IO.userError s!"FAIL {label}: contention")

def expectRejected (label : String) (expected : RejectReason) (result : Result rootBytes) : IO Unit :=
  require label (match result with | .rejected reason => reason == expected | _ => false)

def loadExact (transport : Transport) : IO (Loaded rootBytes) := do
  match ← load transport rootBytes with
  | .ok loaded => return loaded
  | .error detail => throw (IO.userError s!"FAIL reopen: {detail}")

def run (binary : System.FilePath) (directory : System.FilePath) : IO Unit := do
  let config : NativeConfig := ⟨binary, directory / "store"⟩
  let transport := config.transport
  match ← bootstrap transport rootBytes seed with
  | .error message => throw (IO.userError message)
  | .ok () => pure ()

  let first := twoWrites 11 [1] [2] [11] [22] [3]
  let one ← confirmed "first multicell commit" .installed (← receive transport rootBytes first 3)
  require "both post images exact" (one.canonicalBytes ⟨1⟩ == [11] && one.canonicalBytes ⟨2⟩ == [22])
  require "charge, nullifier, history together"
    (one.model.available .feeDebit == 99 && one.model.consumed (nullifier 11) &&
      one.model.history.length == 1 && one.model.journal.length == 1)

  let second := twoWrites 12 [11] [22] [111] [222] [3]
  let two ← confirmed "second commit" .installed (← receive transport rootBytes second 3)
  require "repeated commit changes image" (two.canonicalBytes ⟨1⟩ == [111])
  let retried ← confirmed "retry earlier commit after later commit" .replayed
    (← receive transport rootBytes first 3)
  require "retry does not charge or append" (retried.model.available .feeDebit == 98 && retried.model.history.length == 2)
  let beforeRefusals ← loadExact transport

  expectRejected "same-id changed bytes conflicts" (.durable .transactionConflict)
    (← receive transport rootBytes (twoWrites 11 [1] [2] [99] [22] [3]) 3)
  expectRejected "stale write refuses" (.durable .stalePreRoot)
    (← receive transport rootBytes (twoWrites 13 [11] [22] [1] [2] [3]) 3)
  expectRejected "stale read refuses" .staleReadGuard
    (← receive transport rootBytes (twoWrites 14 [111] [222] [1] [2] [30]) 3)
  let reused := { twoWrites 15 [111] [222] [1] [2] [3] with nullifiers := [nullifier 11] }
  expectRejected "nullifier reuse refuses" (.durable .alreadyConsumed)
    (← receive transport rootBytes reused 3)
  let unaffordable := { twoWrites 16 [111] [222] [1] [2] [3] with exactCharge := fun _ => 1000 }
  expectRejected "meter shortfall refuses" (.durable .insufficientBudget)
    (← receive transport rootBytes unaffordable 3)
  let beforeCrash ← loadExact transport
  require "all refusals preserve exact image" (beforeCrash.bytes == beforeRefusals.bytes)

  let third := twoWrites 17 [111] [222] [31] [32] [3]
  let precommitCrash : Transport :=
    { transport with cas := fun expected proposed => config.cas expected proposed (some "after-insert") }
  require "precommit process exit is explicit uncertainty"
    (match ← receive precommitCrash rootBytes third 3 with | .uncertain _ => true | _ => false)
  require "precommit crash preserves whole image" ((← loadExact transport).bytes == beforeCrash.bytes)
  let _ ← confirmed "retry after precommit crash" .installed (← receive transport rootBytes third 3)

  let fourth := twoWrites 18 [31] [32] [41] [42] [3]
  let lostResponse : Transport :=
    { transport with cas := fun expected proposed => config.cas expected proposed (some "after-commit") }
  let recovered ← confirmed "lost successful response" .recoveredAfterUncertainResponse
    (← receive lostResponse rootBytes fourth 3)
  require "cold reopen recovers all fields" (recovered.model.history.length == 4 &&
    recovered.model.available .proofWork == 96 && recovered.model.consumed (nullifier 18) &&
    recovered.canonicalBytes ⟨1⟩ == [41] && recovered.canonicalBytes ⟨2⟩ == [42])
  let _ ← confirmed "lost response retry" .replayed (← receive transport rootBytes fourth 3)

  let injected ← IO.mkRef false
  let racing : Transport :=
    { transport with cas := fun expected proposed => do
        unless ← injected.get do
          injected.set true
          let _ ← confirmed "concurrent read-cell move" .installed
            (← receive transport rootBytes (moveObserved 19 [3] [33]) 3)
        transport.cas expected proposed }
  expectRejected "CAS conflict reloads and rejects stale read" .staleReadGuard
    (← receive racing rootBytes (twoWrites 20 [41] [42] [51] [52] [3]) 3)
  let raced ← loadExact transport
  require "stale candidate never published" (raced.snapshot.canonicalBytes ⟨1⟩ == [41] &&
    raced.snapshot.canonicalBytes ⟨3⟩ == [33] && raced.snapshot.model.history.length == 5)

  require "codec rejects trailing bytes" ((decode (raced.bytes ++ [0])).isNone)
  require "codec rejects redundant natural digit"
    ((decode (raced.bytes.take 1 ++ [0] ++ raced.bytes.drop 1)).isNone)
  require "malformed native success is uncertain"
    (match parseCasOutput ⟨0, "Installed\nextra\n", ""⟩ with | .uncertain _ => true | _ => false)
  let duplicate : Image := { raced.image with accepted := raced.image.accepted ++ [IntentRecord.ofIntent fourth] }
  require "recovery rejects duplicate journal append" ((recover rootBytes (encode duplicate)).isNone)
  let _ ← transport.cas (some raced.bytes) [0, 1, 2]
  require "corrupt image refuses without implicit reset"
    (match ← receive transport rootBytes fourth 3 with | .unavailable _ => true | _ => false)
  require "corrupt image remains visible to operator"
    (match ← transport.read with | .ok (some bytes) => bytes == [0, 1, 2] | _ => false)
  IO.println s!"PASS durable receiver: Lean codec/executor + SQLite CAS, two-cell repeated commit, replay/conflict/read/write/nullifier/budget refusal, process-exit rollback, lost-response reopen, concurrent guard move, corruption; final valid image {raced.bytes.length} bytes / 5 commits"

end DurableReceiverProbe

def main (arguments : List String) : IO Unit := do
  match arguments with
  | [binary] => IO.FS.withTempDir (DurableReceiverProbe.run binary)
  | _ => throw (IO.userError "usage: lean --run scripts/durable-receiver.lean /absolute/native-store-binary")
