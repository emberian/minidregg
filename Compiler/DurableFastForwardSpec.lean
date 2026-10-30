import Compiler.DurableReceiverCore

/-!
# The fast-forward open: statements (HOT-PATH §2(h), checkpoint v4)

A cold open restores the newest checkpoint and fast-forwards the entries after it; the genesis
replay is `store audit`. These are the statements the v4 change proves, entered before any proof
(the statements auditor's fifth pass folded in). The v4 pieces that do not exist yet are the
parameters of each statement: `open4` (the v4 checkpoint open), `step` (one append on a session),
`bodyOf` (the ONE body every sealer seals), `ff` (the fast-forward open) and `audit`. They are the
fields of ONE `Impl`, and every law is a field of ONE `Spec impl` over those shared fields: an
instance that satisfies one law by a degenerate field (an `open4` that never decodes) fails
`sealOpens` and `inhabited`.

`Derived` is the derived state a session serves from: the six indexes, the journal and history
the snapshot's model reads, and the fold's World. Option A (coordinator, 2026-10-27): the v4 body
carries the fold's World and its `semantics`; the open reads the prefix RECORD BYTES (no tags),
authenticates them by recomputing the chain to the MAC'd `body.chain`, and rebuilds the indexes,
journal and history from them without executing any (`ffState` below holds the World and the
state and has no prefix in its type). The open stays linear in log bytes with no execution; the
journal read at use (no prefix read at all) is the next unit. `Body4` moves into
`DurableCheckpointCodec` with its codec when v4 lands (a move: this module then imports it).

`ff` is not a free field: `Impl.ff` is `ffState` (the executing part: the head's state and World
from the checkpoint and the suffix; no prefix in its type) composed with the chain gate and the
non-executing rebuild (`rebuildDerived`, `State.snapshot` over the decoded records, the receipt
roots read from the tags). The reader's tamper guarantee for the prefix rests on the MAC: every
prefix tag is a KMAC under the Store key, verified chained from the seed's chain, and the
recomputed chain must equal the MAC'd `body.chain`.

A session is built from an open by `ofOpened`, which may refuse: `Loaded`'s resume proof is over
the whole image, so the build decides, over the decoded records and without executing any, that
the checkpoint state is admissible for the whole log and that no suffix record carries a prefix
nullifier or transaction id (then the executing part's prefix-free replay is the protocol's resume:
preflight reads the consumed set only at the intent's own nullifiers). `reopens` says the build
succeeds on a Store's own entries, so a refusing `ofOpened` is not a vacuous instance; `buildSound`
says what a successful build is on ANY Store that passes the gates: the protocol's resume of the
whole image from the checkpoint state, so a MAC-valid suffix that reuses a prefix nullifier or
transaction id (no replay accepts it) makes the build refuse. The deployed `Loaded` carries that
resume proof as a field, so the law holds by its type.

What changes, said once: the open trusts the MAC'd checkpoint for the prefix's World as v3 already
trusts it for the prefix's state. A fold that diverges from the genesis replay under the same key
and semantics is caught by `store audit` (item 5), never at open.
-/

namespace Minidregg.Compiler.DurableFastForwardSpec

open Minidregg.Theory.TypedAuthorization
open Minidregg.Kernel
open Minidregg.Kernel.DurableCommitProtocol
open Minidregg.Kernel.DurableDataIntent
open Minidregg.Kernel.DurableReceiver
open Minidregg.Kernel.DurableCheckpoint
open Minidregg.Compiler.DurableReceiverCodec
open Minidregg.Compiler.DurableCheckpointCodec
open Minidregg.Compiler.DurableReceiverIO
open Minidregg.Compiler.DurableLogTags (chainPrefixesStored verifyTags)
open Minidregg.Compiler.Sp800185Cshake256 (kmac256Bytes)

set_option autoImplicit false

/-! ## What a checkpoint carries beyond v3, and what makes it the replay's -/

/-- The derived state at a height, as a session serves from it. -/
structure Derived where
  presence : PresenceIndex.Index
  links : LinkIndex.Index
  ids : SessionIndex.CellIds
  txs : SessionIndex.TxIndex
  spentAt : SessionIndex.KeyIndex StableNullifier
  writesAt : SessionIndex.KeyIndex CellId
  /-- Newest first, as `State.snapshot` builds it from the prefix. -/
  journal : List (TransactionId × Intent TransactionId CellId StableNullifier ReplayEnvelope)
  /-- Newest first, as `State.snapshot` builds it from the prefix. -/
  history : List ReplayEnvelope
  /-- The fold's World: cells and the whole system store (journal, head, retired, parent,
  spent, allowance), not a `representsCheck` verdict. `none` when the fold is lost. -/
  world : Option HostRefinesWorld.DWorld

/-- The v4 checkpoint body is `DurableCheckpointCodec.Body`: v3's fields, the fold's World's
system store and the fold's `semantics`; its World is `Body.world` (the system store beside the
state's decoded cells). -/
abbrev Body4 := Body

abbrev Sealed4 := Sealed

inductive OpenRefusal where
  | malformed
  | foreignKey
  | foreignSemantics
  | rootMismatch
  | badMac

variable (rootBytes : List UInt8 → Digest) (logStart : Seed → Digest) (semanticsId : Digest)

/-- The genesis replay's World after an image's records. -/
def worldAt (image : Image) : Option HostRefinesWorld.DWorld :=
  match TurnLog.genesisOfSeed image.seed with
  | .error _ => none
  | .ok genesis => (foldRecords rootBytes genesis 0 image.accepted).toOption

/-- The genesis replay's snapshot after an image's records. -/
def replaySnapshot (image : Image) : Option (DataSnapshot rootBytes) :=
  resume rootBytes image 0 (State.ofSeed image.seed)

/-- `derived` is the replay's value at `image`. Every field is pinned: equality where the
open's `Loaded` states equality, the index's own `Exact` where it states that. -/
structure Derived.Honest (image : Image) (derived : Derived) : Prop where
  presence : derived.presence = PresenceIndex.ofRecords image.accepted
  links : derived.links = LinkIndex.ofRecords image.accepted
  ids : derived.ids.Exact (SessionIndex.rawIds image)
  txs : derived.txs.Exact image.accepted
  spentAt : derived.spentAt.Exact IntentRecord.nullifiers image.accepted
  writesAt : derived.writesAt.Exact (fun record => record.writes.map DataWrite.cellId) image.accepted
  journal : derived.journal =
    (image.accepted.map fun record => (record.transactionId, IntentRecord.erase record)).reverse
  history : derived.history = (image.accepted.map fun record => (IntentRecord.erase record).event).reverse
  world : derived.world = worldAt rootBytes image

/-- A v4 body is the replay's value at `image`: height, chain, state, semantics, World. -/
structure Body4.Honest (image : Image) (body : Body4) : Prop where
  height : body.height = image.accepted.length
  chain : body.chain = chainAfter (logStart image.seed) image.accepted
  state : replaySnapshot rootBytes image = some (body.state.snapshot rootBytes image.accepted)
  semantics : body.semantics = semanticsId
  world : body.world = worldAt rootBytes image

/-- What an open serves from: the checkpoint-relative `Loaded`'s observable part. -/
structure View where
  height : Nat
  chain : Digest
  derived : Derived
  snapshot : DataSnapshot rootBytes
  /-- The receipt root after each record, oldest first (read from the verified tags). -/
  rootLog : List Digest

/-- The genesis replay's world root at an image's head. -/
def replayRoot (image : Image) : Option Digest :=
  (replaySnapshot rootBytes image).map fun snapshot =>
    Kernel.WorldRoot.deployedRoot
      (DurableReceiverIO.entriesOf image snapshot (chainAfter (logStart image.seed) image.accepted))

structure View.Honest (image : Image) (view : View rootBytes) : Prop where
  height : view.height = image.accepted.length
  chain : view.chain = chainAfter (logStart image.seed) image.accepted
  snapshot : replaySnapshot rootBytes image = some view.snapshot
  derived : Derived.Honest rootBytes image view.derived
  /-- Every served receipt root is the replay's world root at that height. -/
  rootLogLength : view.rootLog.length = image.accepted.length
  rootLog : ∀ i (lt : i < view.rootLog.length),
    replayRoot rootBytes logStart ⟨image.seed, image.accepted.take (i + 1)⟩ = some view.rootLog[i]

/-! ## The implementation's v4 pieces, shared by every law -/

/-- A fast-forward open: from the checkpoint's bytes, the stored entries below its height (record
bytes and tags: the tags carry each height's receipt root, so an old receipt is a lookup), the
stored entries after it and the Store's head height. -/
abbrev FastForward (α : Type) := MacKey → Seed → Option (List UInt8) → List Entry → List Entry →
  Nat → Except String α

/-- The executing part of an open: the World and the state at the head, from the checkpoint and the
suffix (the suffix replayed with no prefix nullifier or transaction id known: the session build
decides the suffix carries none). It has no prefix in its type, so it cannot execute a prefix record. -/
abbrev FastForwardState (σ : Type) := MacKey → Seed → Option (List UInt8) → List Entry → Nat →
  Except String σ

/-- The non-executing rebuild: the indexes, journal and history as functions of the records (index
folds and maps, no turn executed), beside a World the executing part supplies. -/
def rebuildDerived (seed : Seed) (records : List IntentRecord) (world : Option HostRefinesWorld.DWorld) :
    Derived where
  presence := PresenceIndex.ofRecords records
  links := LinkIndex.ofRecords records
  ids := SessionIndex.CellIds.ofImage ⟨seed, records⟩
  txs := SessionIndex.TxIndex.ofRecords records
  spentAt := SessionIndex.KeyIndex.ofRecords IntentRecord.nullifiers records
  writesAt := SessionIndex.KeyIndex.ofRecords (fun record => record.writes.map DataWrite.cellId) records
  journal := (records.map fun record => (record.transactionId, IntentRecord.erase record)).reverse
  history := (records.map fun record => (IntentRecord.erase record).event).reverse
  world := world

structure Impl where
  /-- A full session (the `Loaded` of this change). -/
  Loaded4 : Type
  /-- The light session's state. -/
  Light : Type
  /-- The `LoadedView` projection: what a session serves from. -/
  view : Loaded4 → View rootBytes
  lightView : Light → View rootBytes
  /-- `representsCheck` on a session: decided from `Derived` and the snapshot. -/
  representsCheck4 : Loaded4 → Bool
  decode4 : List UInt8 → Option Sealed4
  macInput : Body4 × Digest → List UInt8
  macInputDecode : List UInt8 → Option (Body4 × Digest)
  macDomain : List UInt8
  open4 : MacKey → List UInt8 → Except OpenRefusal Body4
  seal4 : MacKey → Body4 → List UInt8
  /-- The ONE body every sealer seals (`storeCheckpoint`, the light session, `checkpointDifferential`,
  the head seal, the clean-shutdown seal), from the session's view. -/
  bodyOf : MacKey → View rootBytes → Body4
  genesis : Seed → Loaded4
  /-- One accepted append on a full session (chain, indexes, journal, World: `ofIntent_run`'s step). -/
  step : Loaded4 → IntentRecord → Option Loaded4
  /-- One accepted append on the light session (the same advance, its own representation). -/
  lightStep : Light → IntentRecord → Option Light
  /-- A full session handing over to the light one. -/
  toLight : Loaded4 → Light
  /-- The executing part's result. -/
  State4 : Type
  ffState : FastForwardState State4
  /-- The checkpoint height and chain the state part started from (`(0, logStart seed)` from genesis). -/
  stateBase : State4 → Nat × Digest
  /-- The checkpoint state the state part started from (`State.ofSeed seed` from genesis). -/
  stateCheckpoint : State4 → State
  /-- The executed state at the head: cells, absent bytes, available charge. -/
  stateHead : State4 → State
  /-- The executed World at the head. -/
  stateWorld : State4 → Option HostRefinesWorld.DWorld
  audit : MacKey → Seed → List IntentRecord → List (Nat × List UInt8) → Except (Nat × String) Unit

variable {rootBytes} in
/-- What an open yields: the executed part and the decoded records. -/
structure Opened (impl : Impl rootBytes) where
  seed : Seed
  state : impl.State4
  records : List IntentRecord
  /-- The receipt root after each record, read from its verified tag. -/
  rootLog : List Digest
  /-- The gated entries below the checkpoint, as opaque bytes: the session build reads their tags
  (the accumulator at the checkpoint's height, the head tag) and their bytes (the chain proof);
  nothing executes them. -/
  below : List Entry

variable {rootBytes} in
/-- `ff`: the executing part, then the gate over the prefix entries (their count is the checkpoint
height, every tag verifies chained from the seed's chain, and the recomputed chain is the
checkpoint's), then the records decoded and the receipt roots read from the tags. Nothing of the
prefix is executed: `ffState` never sees it. -/
def Impl.ff (impl : Impl rootBytes) : FastForward (Opened impl) :=
  fun key seed checkpoint below suffix head =>
    match impl.ffState key seed checkpoint suffix head with
    | .error message => .error message
    | .ok state =>
        if below.length ≠ (impl.stateBase state).1 then .error "the prefix is not the checkpoint's height"
        else if verifyTags key 0 (chainPrefixesStored (logStart seed) (below.map (·.record)))
            (below.map (·.tag)) ≠ .ok () then .error "a prefix tag does not verify"
        else if (chainPrefixesStored (logStart seed) (below.map (·.record))).getLastD (logStart seed) ≠
            (impl.stateBase state).2 then .error "the prefix's chain is not the checkpoint's"
        else match ((below ++ suffix).map (·.record)).mapM recordFrame.decode with
          | none => .error "a stored record does not decode"
          | some records => .ok ⟨seed, state, records, (below ++ suffix).map (fun entry =>
              ((DurableHistory.trailerCarried entry.tag).map (·.root)).getD ⟨0⟩), below⟩

variable {rootBytes} in
/-- The view of an open: the executed part paired with the non-executing rebuild. -/
def Opened.view {impl : Impl rootBytes} (opened : Opened impl) : View rootBytes where
  height := opened.records.length
  chain := chainAfter (logStart opened.seed) opened.records
  derived := rebuildDerived opened.seed opened.records (impl.stateWorld opened.state)
  snapshot := (impl.stateHead opened.state).snapshot rootBytes opened.records
  rootLog := opened.rootLog

variable {rootBytes} in
/-- A session of either kind. -/
abbrev Session (impl : Impl rootBytes) := impl.Loaded4 ⊕ impl.Light

variable {rootBytes} in
def Impl.sessionView (impl : Impl rootBytes) : Session impl → View rootBytes
  | .inl loaded => impl.view loaded
  | .inr light => impl.lightView light

/-- A Store as the Host leaves it: the seed, the accepted records, the sealed checkpoints. -/
structure Written where
  seed : Seed
  records : List IntentRecord
  checkpoints : List (Nat × Body4)

def Written.image (store : Written) : Image := ⟨store.seed, store.records⟩

/-- The stored entries of a Store's records: each record decodes from its entry and every tag
verifies chained from the seed's chain. -/
def OwnEntries (key : MacKey) (seed : Seed) (entries : List Entry) (records : List IntentRecord) : Prop :=
  List.Forall₂ (fun entry record => recordFrame.decode entry.record = some record) entries records ∧
  verifyTags key 0 (chainPrefixesStored (logStart seed) (entries.map (·.record)))
    (entries.map (·.tag)) = .ok ()

/-- The backup rule: open from the newest checkpoint at a positive height at or below the head,
else from genesis. A non-atomic restore that left the prefix short fails the chain gate. -/
def newestAtOrBelow (checkpoints : List (Nat × Body4)) (head : Nat) : Option (Nat × Body4) :=
  (checkpoints.filter fun checkpoint => 0 < checkpoint.1 ∧ checkpoint.1 ≤ head).foldl
    (fun best checkpoint => match best with
      | some held => if held.1 < checkpoint.1 then some checkpoint else some held
      | none => some checkpoint) none

variable {rootBytes} in
/-- What `ff` is handed for a Store cut at `head` under the backup rule: the checkpoint, the
entries below it, the entries from it to the cut. -/
def openInputs (impl : Impl rootBytes) (key : MacKey) (checkpoints : List (Nat × Body4))
    (entries : List Entry) (head : Nat) : Option (List UInt8) × List Entry × List Entry :=
  match newestAtOrBelow checkpoints head with
  | none => (none, [], entries.take head)
  | some (height, body) =>
      (some (impl.seal4 key body), entries.take height, (entries.take head).drop height)

/-- The Stores this Host writes, with the session that wrote them: genesis; an append a full
session accepted (`step`); an append the light session accepted (`lightStep`); a hand-over to the
light session; a seal at ANY height through the one `bodyOf` of the session's view (the due
cadence, the on-demand head seal, the clean-shutdown seal: item 6); a reopen through `ff` of THIS
Store's own entries from genesis or from one of its own sealed checkpoints, served as a full
session (`ofOpened`). Its inhabitant is every Store a Host run produced (`Spec.inhabited`). -/
inductive Wrote (impl : Impl rootBytes) (ofOpened : Opened impl → Except String impl.Loaded4) (key : MacKey) :
    Written → Session impl → Prop
  | genesis (seed : Seed) : Wrote impl ofOpened key ⟨seed, [], []⟩ (.inl (impl.genesis seed))
  | append {store loaded loaded'} (record : IntentRecord) :
      Wrote impl ofOpened key store (.inl loaded) → impl.step loaded record = some loaded' →
      Wrote impl ofOpened key { store with records := store.records ++ [record] } (.inl loaded')
  | lightAppend {store light light'} (record : IntentRecord) :
      Wrote impl ofOpened key store (.inr light) → impl.lightStep light record = some light' →
      Wrote impl ofOpened key { store with records := store.records ++ [record] } (.inr light')
  | goLight {store loaded} :
      Wrote impl ofOpened key store (.inl loaded) →
      Wrote impl ofOpened key store (.inr (impl.toLight loaded))
  | seal {store session} :
      Wrote impl ofOpened key store session →
      Wrote impl ofOpened key
        { store with checkpoints :=
            (store.records.length, impl.bodyOf key (impl.sessionView session)) :: store.checkpoints }
        session
  | reopenGenesis {store session opened loaded} (entries : List Entry) :
      Wrote impl ofOpened key store session → OwnEntries logStart key store.seed entries store.records →
      impl.ff logStart key store.seed none [] entries entries.length = .ok opened →
      ofOpened opened = .ok loaded →
      Wrote impl ofOpened key store (.inl loaded)
  | reopenCheckpoint {store session opened loaded} (entries : List Entry) (height : Nat) (body : Body4) :
      Wrote impl ofOpened key store session → OwnEntries logStart key store.seed entries store.records →
      (height, body) ∈ store.checkpoints → height ≠ 0 →
      impl.ff logStart key store.seed (some (impl.seal4 key body)) (entries.take height)
        (entries.drop height) entries.length = .ok opened →
      ofOpened opened = .ok loaded →
      Wrote impl ofOpened key store (.inl loaded)

/-! ## The laws -/

structure Spec (impl : Impl rootBytes) (ofOpened : Opened impl → Except String impl.Loaded4) : Prop where
  -- ### 1. The MAC gate
  /-- The MAC input is an injective encoding of everything the body carries (no field outside it). -/
  macInjective : ∀ carried, impl.macInputDecode (impl.macInput carried) = some carried
  /-- Accept IFF decode, this key, this semantics, the recomputed root, the MAC. -/
  macGate : ∀ key bytes body, impl.open4 key bytes = .ok body ↔
    ∃ sealed, impl.decode4 bytes = some sealed ∧ sealed.body = body ∧ body.keyId = key.id ∧
      body.semantics = semanticsId ∧ sealed.root = worldRoot rootBytes body ∧
      sealed.mac = kmac256Bytes key.bytes impl.macDomain (impl.macInput (body, sealed.root))
  /-- Teeth by name: another fold's body under this key; a wrong MAC. -/
  macRefusals : ∀ key bytes sealed, impl.decode4 bytes = some sealed → sealed.body.keyId = key.id →
    (sealed.body.semantics ≠ semanticsId → impl.open4 key bytes = .error .foreignSemantics) ∧
    (sealed.body.semantics = semanticsId → sealed.root = worldRoot rootBytes sealed.body →
      sealed.mac ≠ kmac256Bytes key.bytes impl.macDomain (impl.macInput (sealed.body, sealed.root)) →
      impl.open4 key bytes = .error .badMac)
  /-- What is sealed opens, as itself: the gate is not vacuous. -/
  sealOpens : ∀ key view, impl.open4 key (impl.seal4 key (impl.bodyOf key view)) = .ok (impl.bodyOf key view)
  -- ### 2. The suffix gate (on the executing part; the chain gate over the prefix is `Impl.ff`'s)
  /-- The executing part accepts only an opening checkpoint, starts from its height and chain,
  verifies the suffix's tags chained from that chain, decodes every suffix record and reaches the head. -/
  suffixGate : ∀ key seed bytes suffix head state,
    impl.ffState key seed (some bytes) suffix head = .ok state →
    ∃ body, impl.open4 key bytes = .ok body ∧
      impl.stateBase state = (body.height, body.chain) ∧ impl.stateCheckpoint state = body.state ∧
      verifyTags key body.height
        (chainPrefixesStored body.chain (suffix.map (·.record))) (suffix.map (·.tag)) = .ok () ∧
      (∀ entry ∈ suffix, (recordFrame.decode entry.record).isSome) ∧
      body.height + suffix.length = head
  /-- From genesis the executing part starts at the seed's chain and verifies every entry's tag. -/
  genesisGate : ∀ key seed suffix head state,
    impl.ffState key seed none suffix head = .ok state →
    impl.stateBase state = (0, logStart seed) ∧ impl.stateCheckpoint state = State.ofSeed seed ∧
      verifyTags key 0 (chainPrefixesStored (logStart seed) (suffix.map (·.record)))
        (suffix.map (·.tag)) = .ok () ∧ suffix.length = head
  -- ### 3. Exactness over the pair (executed part, non-executing rebuild), and the session shape
  /-- On a Store's own entries, a checkpoint honest for `pre` (or none, `pre = []`) yields an
  executed head state whose snapshot over the records is the replay's, and the fold's World. -/
  exact : ∀ key seed (entries : List Entry) (pre suf : List IntentRecord) checkpoint snapshot,
    OwnEntries logStart key seed entries (pre ++ suf) →
    replaySnapshot rootBytes ⟨seed, pre ++ suf⟩ = some snapshot →
    (match checkpoint with
      | none => pre = []
      | some bytes => ∃ body, impl.open4 key bytes = .ok body ∧
          Body4.Honest rootBytes logStart semanticsId ⟨seed, pre⟩ body ∧ pre ≠ []) →
    ∃ state, impl.ffState key seed checkpoint (entries.drop pre.length) entries.length = .ok state ∧
      (impl.stateHead state).snapshot rootBytes (pre ++ suf) = snapshot ∧
      impl.stateWorld state = worldAt rootBytes ⟨seed, pre ++ suf⟩
  /-- A reopened session serves the open's view. -/
  viewOpened : ∀ opened loaded, ofOpened opened = .ok loaded → impl.view loaded = Opened.view logStart opened
  /-- A successful build serves the protocol's resume of the whole image from the checkpoint state
  at its height, on any Store that passed the gates (not only Stores this Host wrote). -/
  buildSound : ∀ opened loaded, ofOpened opened = .ok loaded →
    resume rootBytes ⟨opened.seed, opened.records⟩ (impl.stateBase opened.state).1
      (impl.stateCheckpoint opened.state) = some (impl.view loaded).snapshot
  /-- The session build succeeds on a Store's own entries, from genesis or an honest checkpoint
  (the hypotheses of `exact`): its admissibility and disjointness checks refuse only what no
  replay accepts. -/
  reopens : ∀ key seed (entries : List Entry) (pre suf : List IntentRecord) checkpoint snapshot opened,
    OwnEntries logStart key seed entries (pre ++ suf) →
    replaySnapshot rootBytes ⟨seed, pre ++ suf⟩ = some snapshot →
    (match checkpoint with
      | none => pre = []
      | some bytes => ∃ body, impl.open4 key bytes = .ok body ∧
          Body4.Honest rootBytes logStart semanticsId ⟨seed, pre⟩ body ∧ pre ≠ []) →
    impl.ff logStart key seed checkpoint (entries.take pre.length) (entries.drop pre.length)
      entries.length = .ok opened →
    ∃ loaded, ofOpened opened = .ok loaded
  /-- `representsCheck` from `Derived`: the session's check decides the snapshot's representation
  by the carried World, with no log. -/
  representsFromDerived : ∀ loaded, impl.representsCheck4 loaded = true ↔
    ∃ world, (impl.view loaded).derived.world = some world ∧
      HostRefinesWorld.SnapRepresents DeployedBridge.bridge (impl.view loaded).snapshot
        (impl.view loaded).height world
  -- ### 4. The keystone
  /-- In every Store this Host wrote, the session (full or light) is the replay's value at the
  head and every checkpoint is the replay's value at its height, World included (whole-World
  equality: every system row). -/
  keystone : ∀ key store session, Wrote rootBytes logStart impl ofOpened key store session →
    View.Honest rootBytes logStart store.image (impl.sessionView session) ∧
    ∀ height body, (height, body) ∈ store.checkpoints →
      Body4.Honest rootBytes logStart semanticsId ⟨store.seed, store.records.take height⟩ body
  /-- Inhabitation: an append, a seal at height 1, a reopen from that checkpoint and the session
  build succeed. -/
  inhabited : ∃ (key : MacKey) (seed : Seed) (record : IntentRecord) (loaded1 loaded2 : impl.Loaded4)
      (entries : List Entry) (opened : Opened impl),
    impl.step (impl.genesis seed) record = some loaded1 ∧
    OwnEntries logStart key seed entries [record] ∧
    impl.ff logStart key seed (some (impl.seal4 key (impl.bodyOf key (impl.view loaded1))))
      entries [] 1 = .ok opened ∧
    ofOpened opened = .ok loaded2
  -- ### 2'. Every cut height, under the backup rule
  /-- A Store this Host wrote, cut at ANY height (below the newest checkpoint included), opens by
  the backup rule to the replay's value at the cut: a tail rollback opens as the genesis replay
  opens it; detecting one rests on the signer's `headTag`, not on this open. -/
  cutHonest : ∀ key store session (entries : List Entry) head,
    Wrote rootBytes logStart impl ofOpened key store session →
    OwnEntries logStart key store.seed entries store.records → head ≤ entries.length →
    ∃ opened,
      impl.ff logStart key store.seed (openInputs impl key store.checkpoints entries head).1
        (openInputs impl key store.checkpoints entries head).2.1
        (openInputs impl key store.checkpoints entries head).2.2 head = .ok opened ∧
      View.Honest rootBytes logStart ⟨store.seed, store.records.take head⟩ (Opened.view logStart opened)
  -- ### 5. `store audit`
  auditSound : ∀ key seed records checkpoints, impl.audit key seed records checkpoints = .ok () →
    ∀ height bytes, (height, bytes) ∈ checkpoints →
      ∃ body, impl.open4 key bytes = .ok body ∧
        Body4.Honest rootBytes logStart semanticsId ⟨seed, records.take height⟩ body
  /-- A dishonest checkpoint (a fold divergence included: caught here, never at open) makes the
  audit refuse, naming a height whose checkpoint is dishonest. -/
  auditRefuses : ∀ key seed records checkpoints,
    (∃ height bytes, (height, bytes) ∈ checkpoints ∧ ∀ body, impl.open4 key bytes = .ok body →
      ¬ Body4.Honest rootBytes logStart semanticsId ⟨seed, records.take height⟩ body) →
    ∃ height message, impl.audit key seed records checkpoints = .error (height, message) ∧
      ∃ bytes, (height, bytes) ∈ checkpoints ∧ ∀ body, impl.open4 key bytes = .ok body →
        ¬ Body4.Honest rootBytes logStart semanticsId ⟨seed, records.take height⟩ body
  -- ### 6. A head seal fast-forwards zero records
  headSealZero : ∀ key seed (entries : List Entry) (records : List IntentRecord) (view : View rootBytes),
    OwnEntries logStart key seed entries records →
    View.Honest rootBytes logStart ⟨seed, records⟩ view → records ≠ [] →
    ∃ opened, impl.ff logStart key seed (some (impl.seal4 key (impl.bodyOf key view)))
        entries [] entries.length = .ok opened ∧
      (Opened.view logStart opened).height = view.height ∧
      (Opened.view logStart opened).chain = view.chain ∧
      (Opened.view logStart opened).derived.world = view.derived.world

end Minidregg.Compiler.DurableFastForwardSpec
