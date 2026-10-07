/-
# Compiler.DurableHistoryStore — the Store-backed `Reader`

The implementation of `Compiler.DurableHistoryReader.Reader` over a durable
transport (`durable-history`, `durable-checkpoint-at`). Every value it returns
was produced by a check: records by `DurableHistory.verifyAt` against the
MAC-bound `Head`, spent answers by `DurableSpent.lookupRows` against the head's
spent root, states by `openSealed` + verified records + `replay`. The types
make anything else unrepresentable; this module only does the IO.
-/
import Compiler.DurableHistoryReader
import Compiler.DurableReceiverIO

namespace Minidregg.Compiler.DurableHistoryStore

open Minidregg.Theory
open Minidregg.Theory.TypedAuthorization
open Minidregg.Kernel.DurableDataIntent (TransactionId StableNullifier DataSnapshot)
open Minidregg.Kernel.DurableReceiver (IntentRecord Seed replay)
open Minidregg.Kernel.DurableCheckpoint (State)
open Minidregg.Compiler.DurableHistory
open Minidregg.Compiler.DurableHistoryReader
open Minidregg.Compiler.DurableReceiverIO (Transport Loaded spentRows)
open Minidregg.Compiler.DurableCheckpointCodec (recordFrame chainAfter openSealed MacKey)

set_option autoImplicit false

/-- The sibling node keys a read of `height` needs under `head`. -/
def pathOf {store : StoreIdentity} (head : Head store) (height : Nat) : List (Nat × Nat) :=
  match LogAccumulator.locate height head.height head.frontier with
  | none => []
  | some (k, e, _) => LogAccumulator.pathKeys height k e

/-- Decode a verified record exactly. -/
def toRecord {store : StoreIdentity} {head : Head store} {height : Nat} (verified : Verified head.frontier head.height height) :
    Except Refusal (Record head height) :=
  match decoded : recordFrame.decode verified.record with
  | some record => .ok ⟨verified, record, decoded⟩
  | none => .error (.undecodable height)

/-- Verify each requested height against the fetched entries and nodes. -/
def verifyAll {store : StoreIdentity} (head : Head store) (entries : List (Nat × DurableReceiverIO.Entry)) (nodes : List RawNode) :
    List Nat → Except Refusal (List ((at_ : Nat) × Record head at_))
  | [] => .ok []
  | height :: rest => do
      let some (_, entry) := entries.find? (·.1 = height)
        | throw (.unavailable height "the Store returned no entry at this height")
      let verified ← verifyAt head.frontier head.height height
        (RawEntry.ofStore height entry.record entry.tag) nodes
      let record ← toRecord verified
      let later ← verifyAll head entries nodes rest
      return ⟨height, record⟩ :: later

/-- One Store call for the entries at `heights` and every node their paths need. -/
def fetch (transport : Transport) {store : StoreIdentity} (head : Head store) (heights : List Nat) :
    IO (Except Refusal (List ((at_ : Nat) × Record head at_))) := do
  if heights.length > 4096 then
    return .error (.unavailable (heights.headD 0) "a history read is bounded to 4096 records")
  for height in heights do
    if height = 0 ∨ height > head.height then return .error (.beyondHead height head.height)
  let keys := (heights.flatMap (pathOf head)).eraseDups
  match ← transport.history ⟨head.height, heights,
      keys.map fun key => (DurableSpent.accumulatorSpace, nodeKey key.1 key.2)⟩ with
  | .error message => return .error (.unavailable (heights.headD 0) message)
  | .ok read =>
      if read.head < head.height then
        return .error (.unavailable (heights.headD 0) "the Store's head is below the authenticated head")
      let nodes : List RawNode := (keys.zip read.nodes).filterMap fun pair =>
        pair.2.2.2.map fun version => RawNode.ofStore pair.1.1 pair.1.2 version.2
      return verifyAll head read.entries nodes heights

def atHeight (transport : Transport) {store : StoreIdentity} (head : Head store) (height : Nat) :
    IO (Except Refusal (Record head height)) := do
  match ← fetch transport head [height] with
  | .error refusal => return .error refusal
  | .ok reads =>
      match reads with
      | [⟨found, record⟩] =>
          if same : found = height then return .ok (same ▸ record)
          else return .error (.wrongHeight height found)
      | _ => return .error (.unavailable height "one record requested, another count returned")

/-- A spent-map answer for one key, verified against the head's spent root. -/
def spentAnswer (transport : Transport) {store : StoreIdentity} (head : Head store) (key : Digest) :
    IO (Except String (DurableSpent.Answer head.spentRoot key)) := do
  match ← spentRows transport head.height [key] with
  | .error message => return .error message
  | .ok rows => return DurableSpent.lookupRows rows head.spentRoot key

def spent (transport : Transport) {store : StoreIdentity} (head : Head store) (nullifier : StableNullifier) :
    IO (Except Refusal (Spent head nullifier)) := do
  match ← spentAnswer transport head (DurableSpent.nullifierKey nullifier) with
  | .error message => return .error (.unavailable 0 message)
  | .ok answer => return .ok answer

def byTx (transport : Transport) {store : StoreIdentity} (head : Head store) (transactionId : TransactionId) :
    IO (Except Refusal (TxAnswer head transactionId)) := do
  match ← spentAnswer transport head (DurableSpent.transactionKey transactionId) with
  | .error message => return .error (.unavailable 0 message)
  | .ok ⟨none, opens⟩ => return .ok (.absent opens)
  | .ok ⟨some height, opens⟩ =>
      match ← atHeight transport head height with
      | .error refusal => return .error refusal
      | .ok read =>
          if carries : read.record.transactionId = transactionId then
            return .ok (.present ⟨height, opens, read, carries⟩)
          else return .error (.unavailable height
            "the spent map names a height whose record carries another transaction")

def range (transport : Transport) {store : StoreIdentity} (head : Head store) (first last : Nat) :
    IO (Except Refusal (List ((at_ : Nat) × Record head at_))) :=
  fetch transport head (List.range' first (last + 1 - first))

/-- The base a past state resumes from, with what makes it authentic. -/
structure Base (rootBytes : List UInt8 → Digest) (seed : Seed) {store : StoreIdentity} (head : Head store) where
  height : Nat
  chain : Digest
  state : State
  authentic : (height = 0 ∧ state = State.ofSeed seed ∧ chain = store.logStart) ∨
    ((∃ bytes, ∃ body : DurableCheckpointCodec.Body, openSealed store.key rootBytes bytes = .ok body ∧
        body.height = height ∧ body.chain = chain ∧ body.state = state) ∧
      ∃ base : Record head height, base.verified.chain = chain)

/-- The latest retained checkpoint at or below `height` (MAC verified under the
head's key, sitting on the verified log), or the seed. -/
def baseOf (transport : Transport) (rootBytes : List UInt8 → Digest) (seed : Seed)
    {store : StoreIdentity} (head : Head store) (height : Nat) : IO (Except Refusal (Base rootBytes seed head)) := do
  match ← transport.checkpointAt height with
  | .error message => return .error (.unavailable height message)
  | .ok none => return .ok ⟨0, store.logStart, State.ofSeed seed, Or.inl ⟨rfl, rfl, rfl⟩⟩
  | .ok (some checkpoint) =>
      match opened : openSealed store.key rootBytes checkpoint.bytes with
      | .error reason =>
          return .error (.unavailable checkpoint.height s!"checkpoint refused: {repr reason}")
      | .ok body =>
          if body.height = 0 ∨ body.height > height then
            return .error (.unavailable checkpoint.height "checkpoint height outside the requested state")
          match ← atHeight transport head body.height with
          | .error refusal => return .error refusal
          | .ok baseRecord =>
              if onLog : baseRecord.verified.chain = body.chain then
                return .ok ⟨body.height, body.chain, body.state,
                  Or.inr ⟨⟨checkpoint.bytes, body, opened, rfl, rfl, rfl⟩, baseRecord, onLog⟩⟩
              else return .error (.notIncluded body.height)

/-- The authentic state after `height` records. -/
def stateAt (transport : Transport) (rootBytes : List UInt8 → Digest) (seed : Seed)
    {store : StoreIdentity} (head : Head store) (height : Nat) :
    IO (Except Refusal (StateAt rootBytes seed head height)) := do
  if height > head.height then return .error (.beyondHead height head.height)
  match ← baseOf transport rootBytes seed head height with
  | .error refusal => return .error refusal
  | .ok base =>
      let reads ← if base.height + 1 > height then pure [] else
        match ← range transport head (base.height + 1) height with
        | .error refusal => return .error refusal
        | .ok reads => pure reads
      if heights : reads.map (·.1) = (List.range reads.length).map (base.height + · + 1) then
        if sized : base.height + reads.length = height then
          if chained : reads.map (·.2.verified.chain) =
              (List.range reads.length).map fun i =>
                chainAfter base.chain ((reads.map (·.2.record)).take (i + 1)) then
            match replayed : replay rootBytes (base.state.snapshot rootBytes []) (reads.map (·.2.record)) with
            | some snapshot =>
                return .ok ⟨base.height, base.chain, base.state, base.authentic, reads, heights, sized,
                  chained, snapshot, replayed⟩
            | none => return .error (.unavailable height "the verified records do not replay from the base")
          else return .error (.notIncluded (base.height + 1))
        else return .error (.unavailable height "the Store returned another record count")
      else return .error (.unavailable height "the Store returned records out of order")

/-- The Reader of an opened Store at its head. The open mints the Store's
identity (its key, its genesis log start) and the head: `Head.verify` of the
head entry's tag (read with the image, or from the Store) under that key, for
the opening's chain and accumulator frontier; `Head.genesis` only when the
image is empty. -/
def readerOf (transport : Transport) (rootBytes : List UInt8 → Digest) (loaded : Loaded rootBytes) :
    IO (Except String ((store : StoreIdentity) × Reader rootBytes store)) := do
  let key ← match ← transport.key with
    | .error message => return .error message
    | .ok key => pure key
  let some frontier := loaded.frontier
    | return .error "this opening carries no accumulator frontier (it was not read from the Store)"
  let store := StoreIdentity.ofOpen key loaded.logStart
  let height := loaded.image.accepted.length
  let head ← if height = 0 then pure (Head.genesis store loaded.worldRoot) else do
    let tag ← match loaded.headTag with
      | some tag => pure tag
      | none =>
          match ← transport.read height false with
          | .ok (some stored) =>
              match stored.entries.head? with
              | some entry => pure entry.tag
              | none => return .error "durable head entry missing"
          | .ok none => return .error "durable store is not initialized"
          | .error message => return .error message
    match Head.verify store height tag loaded.chain frontier with
    | .ok head => pure head
    | .error refusal => return .error refusal.message
  return .ok ⟨store,
    { head, seed := loaded.image.seed
      atHeight := atHeight transport head
      byTx := byTx transport head
      spent := spent transport head
      range := range transport head
      stateAt := stateAt transport rootBytes loaded.image.seed head }⟩

end Minidregg.Compiler.DurableHistoryStore
