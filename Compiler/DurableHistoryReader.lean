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
| `model.journal` / `lookupRecorded` (receivers)  | the receiver as a `DurableView.Family` (declared keys + `covers`); `Reader.footprint` → `toFootprint` → `DurableView.view` |
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
  to "absent". Absence is `TxAnswer.absent` / a `Spent` answer with `value = none`,
  each carrying the spent map's opening.
* Nothing here can be built by a port: `Head store` is indexed by the opened
  Store's identity and has a private constructor (only the open's `Head.verify`
  / `Head.genesis` make one; both, and `StoreIdentity.ofOpen`, are on the token
  audit list), `Verified`/`Opens` need real inclusion
  checks, `StateAt` carries its base's MAC and its records' verification.
  `scripts/kn2/check-planted-api-faults.sh` keeps that true.
-/
import Compiler.DurableHistory
import Compiler.DurableSpent
import Compiler.DurableReceiverCodec
import Compiler.DurableCheckpointCodec
import Kernel.DurableView

namespace Minidregg.Compiler.DurableHistoryReader

open Minidregg.Theory.TypedAuthorization
open Minidregg.Kernel.DurableDataIntent (TransactionId StableNullifier DataSnapshot)
open Minidregg.Kernel.DurableCommitProtocol (Intent Snapshot)
open Minidregg.Kernel.DurableReceiver (IntentRecord Seed replay)
open Minidregg.Kernel.DurableCheckpoint (State)
open Minidregg.Compiler.DurableHistory (Verified Refusal Head StoreIdentity)
open Minidregg.Compiler.DurableCheckpointCodec (recordFrame chainAfter openSealed)
open Minidregg.Kernel.DurableView (Keys)

set_option autoImplicit false

/-- A record read by height, verified at use against the authenticated head
(`DurableHistory.verifyAt`), then decoded exactly from the verified bytes. -/
structure Record {store : StoreIdentity} (head : Head store) (height : Nat) where
  verified : Verified head.frontier head.height height
  record : IntentRecord
  decoded : recordFrame.decode verified.record = some record

/-- A transaction id's record: the spent map's opening names its height, the
record read there carries that id. -/
structure ByTx {store : StoreIdentity} (head : Head store) (transactionId : TransactionId) where
  height : Nat
  answer : DurableSpent.Opens head.spentRoot (DurableSpent.transactionKey transactionId) (some height)
  read : Record head height
  carries : read.record.transactionId = transactionId

/-- A transaction id's answer. ABSENCE IS A VALUE THAT CARRIES ITS OPENING: a
reader cannot report "not accepted" without the spent map's verified absence. -/
inductive TxAnswer {store : StoreIdentity} (head : Head store) (transactionId : TransactionId) where
  | present (found : ByTx head transactionId)
  | absent (opens : DurableSpent.Opens head.spentRoot (DurableSpent.transactionKey transactionId) none)

/-- The spent bit of a nullifier: the inserting height or absence, opened
against the head's spent root. -/
abbrev Spent {store : StoreIdentity} (head : Head store) (nullifier : StableNullifier) :=
  DurableSpent.Answer head.spentRoot (DurableSpent.nullifierKey nullifier)

/-- The state after `height` records, with what makes it authentic:
* the base is the seed (height 0, the pinned genesis) or a checkpoint whose
  MAC verified under the head's key (`openSealed`), sitting on the log: the
  verified record at its height carries its chain;
* every record after the base is a verified `Record` at the next height,
  chained from the base's chain (none can be spliced in from another history);
* the snapshot is exactly the executor's replay of those records from the base. -/
structure StateAt (rootBytes : List UInt8 → Digest) (seed : Seed) {store : StoreIdentity} (head : Head store)
    (height : Nat) where
  baseHeight : Nat
  baseChain : Digest
  baseState : State
  baseAuthentic : (baseHeight = 0 ∧ baseState = State.ofSeed seed ∧ baseChain = store.logStart) ∨
    ((∃ bytes, ∃ body : DurableCheckpointCodec.Body, openSealed store.key rootBytes bytes = .ok body ∧
        body.height = baseHeight ∧ body.chain = baseChain ∧ body.state = baseState) ∧
      ∃ base : Record head baseHeight, base.verified.chain = baseChain)
  reads : List ((at_ : Nat) × Record head at_)
  heights : reads.map (·.1) = (List.range reads.length).map (baseHeight + · + 1)
  sized : baseHeight + reads.length = height
  chained : reads.map (·.2.verified.chain) =
    (List.range reads.length).map fun i => chainAfter baseChain ((reads.map (·.2.record)).take (i + 1))
  snapshot : DataSnapshot rootBytes
  replayed : replay rootBytes (baseState.snapshot rootBytes []) (reads.map (·.2.record)) = some snapshot

/-- The answers to a request's declared keys, each verified. -/
structure VerifiedFootprint {store : StoreIdentity} (head : Head store) (keys : Keys) where
  transactions : List ((transactionId : TransactionId) × TxAnswer head transactionId)
  transactionsExact : transactions.map (·.1) = keys.transactions
  nullifiers : List ((nullifier : StableNullifier) × Spent head nullifier)
  nullifiersExact : nullifiers.map (·.1) = keys.nullifiers

/-- The recorded intent an answer contributes to the view's journal. -/
def TxAnswer.recorded {store : StoreIdentity} {head : Head store} {transactionId : TransactionId} :
    TxAnswer head transactionId → Option (Intent TransactionId Kernel.DurableDataIntent.CellId
      StableNullifier Kernel.DurableDataIntent.ReplayEnvelope)
  | .present found => some (Kernel.DurableCheckpoint.IntentRecord.erase found.read.record)
  | .absent _ => none

def VerifiedFootprint.toFootprint {store : StoreIdentity} {head : Head store} {keys : Keys} (footprint : VerifiedFootprint head keys) :
    Kernel.DurableView.Footprint :=
  ⟨footprint.transactions.filterMap fun answer => answer.2.recorded.map (answer.1, ·),
    footprint.nullifiers.map fun answer => (answer.1, answer.2.value.isSome)⟩

theorem lookup_answers_some {store : StoreIdentity} {head : Head store} (transactionId : TransactionId)
    {intent : Intent TransactionId Kernel.DurableDataIntent.CellId StableNullifier
      Kernel.DurableDataIntent.ReplayEnvelope} :
    ∀ (answers : List ((id : TransactionId) × TxAnswer head id)),
      Snapshot.lookupRecorded transactionId
          (answers.filterMap fun answer => answer.2.recorded.map (answer.1, ·)) = some intent →
        ∃ found : ByTx head transactionId,
          intent = Kernel.DurableCheckpoint.IntentRecord.erase found.read.record
  | [], hit => by simp [Snapshot.lookupRecorded] at hit
  | ⟨id, .absent _⟩ :: rest, hit => lookup_answers_some transactionId rest (by
      simpa [List.filterMap_cons, TxAnswer.recorded] using hit)
  | ⟨id, .present found⟩ :: rest, hit => by
      simp only [List.filterMap_cons, TxAnswer.recorded, Option.map_some, Snapshot.lookupRecorded] at hit
      split at hit
      · rename_i same
        subst same
        exact ⟨found, (Option.some.inj hit).symm⟩
      · exact lookup_answers_some transactionId rest hit

/-- **Every journal answer the view adds is a verified record**: a lookup that
hits the footprint hits a `present` answer for that id, i.e. the erasure of a
record verified at use. -/
theorem toFootprint_lookup_some {store : StoreIdentity} {head : Head store} {keys : Keys} (footprint : VerifiedFootprint head keys)
    (transactionId : TransactionId) {intent : Intent TransactionId Kernel.DurableDataIntent.CellId
      StableNullifier Kernel.DurableDataIntent.ReplayEnvelope}
    (hit : Snapshot.lookupRecorded transactionId footprint.toFootprint.recorded = some intent) :
    ∃ found : ByTx head transactionId,
      intent = Kernel.DurableCheckpoint.IntentRecord.erase found.read.record :=
  lookup_answers_some transactionId footprint.transactions hit

theorem lookup_answers_none {store : StoreIdentity} {head : Head store} (transactionId : TransactionId) :
    ∀ (answers : List ((id : TransactionId) × TxAnswer head id)),
      Snapshot.lookupRecorded transactionId
          (answers.filterMap fun answer => answer.2.recorded.map (answer.1, ·)) = none →
      ∀ answer ∈ answers, answer.1 = transactionId →
        ∃ opens : DurableSpent.Opens head.spentRoot (DurableSpent.transactionKey answer.1) none,
          answer.2 = .absent opens
  | [], _, _, member, _ => by cases member
  | ⟨id, reply⟩ :: rest, miss, answer, member, same => by
      rcases List.mem_cons.mp member with rfl | inRest
      · cases reply with
        | absent opens => exact ⟨opens, rfl⟩
        | present found =>
            simp only at same
            subst same
            simp [List.filterMap_cons, TxAnswer.recorded, Snapshot.lookupRecorded] at miss
      · have missRest : Snapshot.lookupRecorded transactionId
            (rest.filterMap fun answer => answer.2.recorded.map (answer.1, ·)) = none := by
          cases reply with
          | absent _ => simpa [List.filterMap_cons, TxAnswer.recorded] using miss
          | present found =>
              simp only [List.filterMap_cons, TxAnswer.recorded, Option.map_some, Snapshot.lookupRecorded] at miss
              split at miss
              · cases miss
              · exact miss
        exact lookup_answers_none transactionId rest missRest answer inRest same

/-- **A miss on a declared key is a verified absence**: if a declared id is
not in the view's added journal, every answer for it carries the spent map's
absence opening. -/
theorem toFootprint_lookup_none {store : StoreIdentity} {head : Head store} {keys : Keys} (footprint : VerifiedFootprint head keys)
    (transactionId : TransactionId)
    (miss : Snapshot.lookupRecorded transactionId footprint.toFootprint.recorded = none)
    (answer : (id : TransactionId) × TxAnswer head id) (member : answer ∈ footprint.transactions)
    (same : answer.1 = transactionId) :
    ∃ opens : DurableSpent.Opens head.spentRoot (DurableSpent.transactionKey answer.1) none,
      answer.2 = .absent opens :=
  lookup_answers_none transactionId footprint.transactions miss answer member same

/-- The history of one opened Store at its authenticated `head`. Every
operation's result type carries its verification relative to `head`, which
only the open can produce (`Head store`, indexed by the opened Store). -/
structure Reader (rootBytes : List UInt8 → Digest) (store : StoreIdentity) where
  head : Head store
  seed : Seed
  /-- One record by height (1-based). -/
  atHeight : (height : Nat) → IO (Except Refusal (Record head height))
  /-- The accepted record of a transaction id, or its verified absence. -/
  byTx : (transactionId : TransactionId) → IO (Except Refusal (TxAnswer head transactionId))
  /-- The height that consumed a nullifier, or its verified absence. -/
  spent : (nullifier : StableNullifier) → IO (Except Refusal (Spent head nullifier))
  /-- Records `first..last` (inclusive), each verified. Bounded windows only on request paths. -/
  range : (first last : Nat) →
    IO (Except Refusal (List ((height : Nat) × Record head height)))
  /-- The authentic state after `height` records. -/
  stateAt : (height : Nat) → IO (Except Refusal (StateAt rootBytes seed head height))

/-- The verified answers to a request's declared keys. -/
def Reader.footprint {rootBytes : List UInt8 → Digest} {store : StoreIdentity} (reader : Reader rootBytes store)
    (keys : Keys) :
    IO (Except Refusal (VerifiedFootprint reader.head keys)) := do
  let mut transactions : List ((transactionId : TransactionId) × TxAnswer reader.head transactionId) := []
  for transactionId in keys.transactions do
    match ← reader.byTx transactionId with
    | .error refusal => return .error refusal
    | .ok answer => transactions := transactions ++ [⟨transactionId, answer⟩]
  let mut nullifiers : List ((nullifier : StableNullifier) × Spent reader.head nullifier) := []
  for nullifier in keys.nullifiers do
    match ← reader.spent nullifier with
    | .error refusal => return .error refusal
    | .ok answer => nullifiers := nullifiers ++ [⟨nullifier, answer⟩]
  if exact : transactions.map (·.1) = keys.transactions ∧ nullifiers.map (·.1) = keys.nullifiers then
    return .ok ⟨transactions, exact.1, nullifiers, exact.2⟩
  else return .error (.unavailable 0 "footprint answers do not cover the declared keys")

#assert_axioms toFootprint_lookup_some
#assert_axioms toFootprint_lookup_none

end Minidregg.Compiler.DurableHistoryReader
