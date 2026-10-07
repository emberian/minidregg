/-
# Compiler.DurableHistoryReader — the pinned history API (KN2-STORE-OPEN stage 2)

THIS FILE IS THE CONTRACT the port lanes build against. After stage (2) the
opened Store (`DurableReceiverIO.Loaded`) holds NO decoded history prefix:
`Loaded.image`, `chainExact`, `resumed`, `indexExact`, `txsExact`, `idsExact`,
`rootLog` are gone. Its snapshot's journal / consumed / history carry the
records since its checkpoint only; roots, canonical bytes and allowance are
complete. Every read of an older record goes through a `Reader`, and each
operation returns only values that carry their verification:

| census group (STATUS.txt PART 2)               | replace with                              |
|------------------------------------------------|-------------------------------------------|
| `image.accepted.length`, `history.length`       | `Loaded.height` (a field)                 |
| `accepted[i]?`, prior-record re-validation      | `Reader.atHeight (i + 1)`                     |
| `findIdx?`/`find?` by transaction id, receipts  | `Reader.byTx`                             |
| `model.journal` / `lookupRecorded` (receivers)  | `Reader.footprint` → `DurableView.view`   |
| `model.consumed` (markersCurrent, spentOf)      | `Reader.spent` (or the footprint)         |
| `rootLog[i]` (receipt roots)                    | `(Reader.atHeight (i+1)).root`                  |
| prefix cut + genesis replay, `atPrefix`         | `Reader.stateAt` (checkpoint + ≤ 63 recs) |
| full scans (since/tail/fleetHead/Fn*Progress)   | an index or `Reader.range` over a BOUNDED window; an unbounded `range` on a request path is a port defect |

Rules for port lanes:
* Never rebuild the history per request. A view is the served snapshot plus the
  request's footprint answers, nothing more (`DurableView.view`, `execute_view`).
* The footprint of a request is every transaction id its receivers pass to
  `lookupRecorded` (its own `intent.transactionId` AND any prior one it consults,
  e.g. `binding.openCell.transactionId`) and every nullifier whose consumed bit
  it reads. A receiver that would need the whole journal is rewritten to ask
  `byTx`/`spent` for the keys it means.
* A `Refusal` is surfaced by its `message` (it names the height); never mapped
  to "absent".
-/
import Compiler.DurableHistory
import Compiler.DurableSpent
import Compiler.DurableReceiverCodec
import Kernel.DurableView

namespace Minidregg.Compiler.DurableHistoryReader

open Minidregg.Theory.TypedAuthorization
open Minidregg.Kernel.DurableDataIntent (TransactionId StableNullifier DataSnapshot)
open Minidregg.Kernel.DurableReceiver (IntentRecord)
open Minidregg.Compiler.DurableHistory (Verified Refusal)
open Minidregg.Compiler.DurableCheckpointCodec (recordFrame)

set_option autoImplicit false

/-- A record read by height: verified at use (`DurableHistory.verifyAt`), then
decoded exactly from the verified bytes. -/
structure Record (frontier : List (Nat × Digest)) (head height : Nat) where
  verified : Verified frontier head height
  record : IntentRecord
  decoded : recordFrame.decode verified.record = some record

/-- A transaction id's record: the spent map's verified answer names its
height, and the record read there carries that id. -/
structure ByTx (frontier : List (Nat × Digest)) (head : Nat) (spentRoot : Digest)
    (transactionId : TransactionId) where
  height : Nat
  answer : DurableSpent.Opens spentRoot (DurableSpent.transactionKey transactionId) (some height)
  read : Record frontier head height
  carries : read.record.transactionId = transactionId

/-- The spent bit of a nullifier: the inserting height, or absence, opened
against the authenticated spent root. -/
abbrev Spent (spentRoot : Digest) (nullifier : StableNullifier) :=
  DurableSpent.Answer spentRoot (DurableSpent.nullifierKey nullifier)

/-- What a request's executor and receivers consult beyond the served snapshot. -/
structure FootprintKeys where
  transactions : List TransactionId
  nullifiers : List StableNullifier

/-- The history of one opened Store at its authenticated head (`frontier`
and `spentRoot` come from the head tag the open verified with the key and
the MINIANC2 anchor fixed). -/
structure Reader (rootBytes : List UInt8 → Digest) where
  head : Nat
  frontier : List (Nat × Digest)
  spentRoot : Digest
  /-- One record by height (1-based). -/
  atHeight : (height : Nat) → IO (Except Refusal (Record frontier head height))
  /-- The accepted record of a transaction id, or verified absence. -/
  byTx : (transactionId : TransactionId) →
    IO (Except Refusal (Option (ByTx frontier head spentRoot transactionId)))
  /-- The height that consumed a nullifier, or verified absence. -/
  spent : (nullifier : StableNullifier) → IO (Except Refusal (Spent spentRoot nullifier))
  /-- Records `from..to` (inclusive), each verified. Bounded windows only on request paths. -/
  range : (first last : Nat) →
    IO (Except Refusal (List ((height : Nat) × Record frontier head height)))
  /-- The state after `height` records: the retained checkpoint at or below it,
  then at most `checkpointEvery - 1` verified records replayed. -/
  stateAt : (height : Nat) → IO (Except Refusal (DataSnapshot rootBytes))

/-- The footprint answers as `DurableView.Footprint`: every recorded intent
and spent bit in it was verified at use. -/
def Reader.footprint {rootBytes : List UInt8 → Digest} (reader : Reader rootBytes)
    (keys : FootprintKeys) : IO (Except Refusal Kernel.DurableView.Footprint) := do
  let mut recorded := []
  for transactionId in keys.transactions do
    match ← reader.byTx transactionId with
    | .error refusal => return .error refusal
    | .ok none => pure ()
    | .ok (some found) =>
        recorded := recorded ++
          [(transactionId, Kernel.DurableCheckpoint.IntentRecord.erase found.read.record)]
  let mut spent := []
  for nullifier in keys.nullifiers do
    match ← reader.spent nullifier with
    | .error refusal => return .error refusal
    | .ok answer => spent := spent ++ [(nullifier, answer.value.isSome)]
  return .ok ⟨recorded, spent⟩

end Minidregg.Compiler.DurableHistoryReader
