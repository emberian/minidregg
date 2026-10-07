/-
Conditional selection of one original record and its exact prefix state from
the Store's authenticated history. The record is read through the `Reader`
(verified against the head at use) and the prefix is `Reader.stateAt index`
(checkpoint plus at most a bounded run of verified records), served as a
`Basis` whose footprint is verified under the SAME head. Nothing replays from
genesis and no full image is held. This lower module does not certify that
earlier records were semantically admitted and exposes no commit or host
permit. The upper native history verifier supplies that separate inductive
provenance.
-/
import Kernel.NativeHostContext
import Compiler.DurableHistoryReader
import Compiler.DurableServed
import Kernel.NativeHostServed

namespace Minidregg.Kernel.NativeHistorySelection

open Minidregg.Compiler
open Minidregg.Compiler.ResourceBirthCodec
open Minidregg.Kernel.DurableDataIntent
open Minidregg.Kernel.NativeHost
open Minidregg.Theory.TypedAuthorization (Digest)
open Minidregg.Compiler.DurableHistory (Head StoreIdentity)
open Minidregg.Compiler.DurableHistoryReader (Reader Record StateAt)
open Minidregg.Compiler.ServedBasis (Basis Ground Grounded)
open Minidregg.Compiler.DurableServed (Served)
open Minidregg.Kernel.NativeHostServed (OpenedServed validateServed validateServed_served)

set_option autoImplicit false

/-- A selected record and its prefix, both read from the authenticated history
under one head: the record at height `index + 1` is verified against `head`,
and `prior` is the basis at the state after `index` records (`Reader.stateAt`,
served by `Served.ofStateAt`, validated by `validateServed`) with the footprint
of the keys the caller will read, verified under the same head. -/
structure Candidate (config : Config) {store : StoreIdentity} (head : Head store) (index : Nat) where
  private mk ::
  prior : Basis config.deployment store
  /-- The height of the state the selection is made from: a record is only selected
  from a state that already holds it (as `accepted[index]?` of a prefix did). -/
  bound : Nat
  indexBelow : index < bound
  record : DurableReceiver.IntentRecord
  read : Record head (index + 1)
  recordExact : read.record = record
  priorHeight : prior.height = index
  priorHead : prior.head = head
  /-- The prior as a ground at the history head (its light ground is the basis). -/
  grounded : Grounded config.deployment head
  groundedLight : grounded.ground = .light prior
  priorPast : ∃ (seed : DurableReceiver.Seed) (state : StateAt rootBytes seed head index),
    prior.served = Served.ofStateAt state

/-- The ground a historical admission re-runs on: the prior basis. -/
def Candidate.ground {config : Config} {store : StoreIdentity} {head : Head store} {index : Nat}
    (candidate : Candidate config head index) : Ground config.deployment :=
  candidate.grounded.ground

/-- Select the record at 0-based `index` and the state before it. `keys` are the
transaction ids and nullifiers the historical admission reads at the prior state;
the footprint answers them under the reader's head. Every refusal surfaces by
message (a `Refusal` names its height). -/
def select (config : Config) {store : StoreIdentity}
    (reader : Reader rootBytes store) (bound index : Nat) (keys : DurableView.Keys) :
    IO (Except String (Candidate config reader.head index)) := do
  if indexBelow : index < bound then
   if below : index + 1 ≤ reader.head.height then
    match ← reader.atHeight (index + 1) with
    | .error refusal => return .error refusal.message
    | .ok read =>
        match ← reader.stateAt index with
        | .error refusal => return .error refusal.message
        | .ok state =>
            match validated : validateServed config (Served.ofStateAt state) with
            | .error detail => return .error detail
            | .ok opened =>
                match ← reader.footprint keys with
                | .error refusal => return .error refusal.message
                | .ok footprint =>
                    let served : opened.served = Served.ofStateAt state := validateServed_served validated
                    let basis := opened.basis reader.head (by
                      rw [served]
                      exact Nat.le_trans (Nat.le_succ index) below) footprint
                    return .ok ⟨basis, bound, indexBelow, read.record, read, rfl,
                      (by show opened.served.height = index; rw [served]; rfl), rfl,
                      ⟨.light basis, Ground.At.light basis⟩, rfl, ⟨_, state, served⟩⟩
   else return .error "historical record index unavailable"
  else return .error "historical record index unavailable"

/-- The state after a selected record (`Reader.stateAt (index + 1)`), validated like
every served state: what a selection's post-prefix checks (its world root and
physical roots) read. -/
structure After (config : Config) {store : StoreIdentity} (head : Head store) (index : Nat) where
  private mk ::
  opened : OpenedServed config store
  height : opened.served.height = index + 1
  past : ∃ (seed : DurableReceiver.Seed) (state : StateAt rootBytes seed head (index + 1)),
    opened.served = Served.ofStateAt state

def selectAfter (config : Config) {store : StoreIdentity}
    (reader : Reader rootBytes store) (index : Nat) :
    IO (Except String (After config reader.head index)) := do
  match ← reader.stateAt (index + 1) with
  | .error refusal => return .error refusal.message
  | .ok state =>
      match validated : validateServed config (Served.ofStateAt state) with
      | .error detail => return .error detail
      | .ok opened =>
          let served : opened.served = Served.ofStateAt state := validateServed_served validated
          return .ok ⟨opened, by rw [served]; rfl, ⟨_, state, served⟩⟩

/-- The same canonical intent-record stream used by the native replay
verifier compares all writes, guards, ten charge lanes, nullifiers and event. -/
def recordMatches (record : DurableReceiver.IntentRecord)
    (intent : DataIntent rootBytes) : Bool :=
  decide (DurableReceiverCodec.intentStream.encode record =
    DurableReceiverCodec.intentStream.encode (DurableReceiver.IntentRecord.ofIntent intent))

theorem recordMatches_iff (record : DurableReceiver.IntentRecord)
    (intent : DataIntent rootBytes) :
    recordMatches record intent = true ↔
      record = DurableReceiver.IntentRecord.ofIntent intent := by
  simp only [recordMatches, decide_eq_true_eq]
  exact (lawful_encode_injective DurableReceiverCodec.intentStream.toLawful).eq_iff

structure Matched {config : Config} {store : StoreIdentity} {head : Head store} {index : Nat}
    (candidate : Candidate config head index) (intent : DataIntent rootBytes) where
  private mk ::
  selectedRecord : DurableReceiver.IntentRecord
  selected : selectedRecord = candidate.record
  exact : selectedRecord = DurableReceiver.IntentRecord.ofIntent intent

def matchIntent {config : Config} {store : StoreIdentity} {head : Head store} {index : Nat}
    (candidate : Candidate config head index) (intent : DataIntent rootBytes) :
    Except String (Matched candidate intent) :=
  if same : recordMatches candidate.record intent = true then
    .ok ⟨candidate.record, rfl, (recordMatches_iff candidate.record intent).mp same⟩
  else .error "historical record differs from source-admitted intent"

/-! ## Bounded windows over the Store's verified records

Operator and validation paths that must compare or export a long run of
records read them through the `Reader` in windows of at most `windowSize`
records, handing each window to a step that either threads its state or
refuses. A `Refusal` surfaces by its message (it names the height); nothing is
mapped to "absent". Callers that carry a size bound stop inside `step`, so the
scan is bounded by the bound they state, not by the history. -/

def windowSize : Nat := 1024

def foldRange {root : List UInt8 → Digest} {store : Minidregg.Compiler.DurableHistory.StoreIdentity}
    {σ : Type}
    (reader : Minidregg.Compiler.DurableHistoryReader.Reader root store)
    (first last : Nat) (init : σ)
    (step : σ → List DurableReceiver.IntentRecord → Except String σ) :
    IO (Except String σ) := do
  let mut state := init
  let mut cursor := first
  for _ in List.range ((last + 1 - first) / windowSize + 1) do
    if cursor > last then break
    let upto := min last (cursor + windowSize - 1)
    match ← reader.range cursor upto with
    | .error refusal => return .error refusal.message
    | .ok reads =>
        match step state (reads.map (·.2.record)) with
        | .error detail => return .error detail
        | .ok next => state := next
    cursor := upto + 1
  return .ok state

end Minidregg.Kernel.NativeHistorySelection
