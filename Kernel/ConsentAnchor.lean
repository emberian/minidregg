/-
# A client's retained consent anchor

A full-peer consent provider (`Host.ClientConsentCore`) admits the Store's
history before it signs anything: every signed ingress re-admitted at its
original prefix. Each client process starts a provider, so without a retained
result every client start re-admitted the whole history from genesis.

An `Anchor` is what one admission leaves under the client's own custody: the
height it reached, the genesis log start, the log chain after that height and
the world root there. A later provider (`resume`):

* refuses a Store whose log start differs, whose head is below the anchor (the
  accepted history was rolled back), or whose chain after the anchor's height
  is not the anchor's chain (the prefix this client admitted was rewritten or
  forked) — `checkStore_ok`, `checkStore_refuses_rewritten`;
* cuts the Store at the anchor folded from the seed (`Loaded.prefixOwn`: the
  Store's checkpoint is the operator's seal and is never a client base),
  validates that image, and refuses unless it reproduces the anchor exactly,
  world root included;
* natively admits every record after the anchor (`verifySuffixFrom`).

Trust premise, stated once: the anchor bytes are the client's custody, written
by a provider that had admitted that prefix (`Basis.anchor`). A Lean proof
cannot cross a process boundary; the anchor file is the same kind of input as
the signing key beside it. The chain is what makes it a commitment: equal
chains are equal prefixes, up to a collision of the deployed hash.
-/
import Kernel.NativeHostReplay

namespace Minidregg.Kernel.ConsentAnchor

open Minidregg.Theory.TypedAuthorization
open Minidregg.Compiler
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Compiler.DurableCheckpointCodec (chainAfter)
open Minidregg.Kernel.NativeHost

set_option autoImplicit false

/-- The height a consent provider admitted, the genesis log start, the log
chain after that many records, and the world root there. -/
structure Anchor where
  height : Nat
  logStart : Digest
  chain : Digest
  root : Digest
  deriving DecidableEq, Repr

/-- The epoch of the retained bytes. Another epoch refuses by name. -/
def epochTag : List UInt8 := "MINI-CONSENT-ANCHOR/v1".toUTF8.toList

def anchorStream : StreamCodec Anchor :=
  StreamCodec.xmap
    (StreamCodec.product StreamCodec.nat
      (StreamCodec.product digestStream (StreamCodec.product digestStream digestStream)))
    (fun anchor => (anchor.height, anchor.logStart, anchor.chain, anchor.root))
    (fun tuple => ⟨tuple.1, tuple.2.1, tuple.2.2.1, tuple.2.2.2⟩)
    (by intro value; cases value; rfl)

def encode (anchor : Anchor) : List UInt8 := epochTag ++ anchorStream.encode anchor

/-- Exact decode: the v1 tag, then the canonical record and nothing after it. -/
def decode (bytes : List UInt8) : Except String Anchor :=
  if bytes.take epochTag.length = epochTag then
    match anchorStream.toLawful.decode
        (bytes.drop epochTag.length) with
    | some anchor => .ok anchor
    | none => .error "retained consent anchor is not a canonical MINI-CONSENT-ANCHOR/v1 record"
  else .error "retained consent anchor is not of epoch MINI-CONSENT-ANCHOR/v1"

theorem decode_encode (anchor : Anchor) : decode (encode anchor) = .ok anchor := by
  have tagged : (epochTag ++ anchorStream.encode anchor).take epochTag.length = epochTag :=
    List.take_left' rfl
  have body : (epochTag ++ anchorStream.encode anchor).drop epochTag.length =
      anchorStream.encode anchor :=
    List.drop_left' rfl
  have exact := anchorStream.toLawful.decode_encode anchor
  unfold decode encode
  rw [if_pos tagged, body]
  rw [show anchorStream.toLawful.decode
      (anchorStream.encode anchor) = some anchor from exact]

#assert_axioms decode_encode

/-- The anchor of a validated opening. -/
def Anchor.ofOpened {config : Config} (opened : Opened config) : Anchor :=
  ⟨opened.durable.image.accepted.length, opened.durable.logStart, opened.durable.chain,
    opened.durable.worldRoot⟩

/-- The physical comparisons an anchor makes against a full open of the
Store, before any image is cut or record admitted. -/
def checkStore (anchor : Anchor) (loaded : Durable) (chains : List Digest) : Except String Unit :=
  if loaded.logStart ≠ anchor.logStart then
    .error "the Store's genesis log differs from the retained consent anchor's"
  else if loaded.image.accepted.length < anchor.height then
    .error s!"the Store's head {loaded.image.accepted.length} is below the retained consent anchor at {anchor.height}: the accepted history was rolled back"
  else if chains[anchor.height]? ≠ some anchor.chain then
    .error s!"the Store's accepted history up to height {anchor.height} differs from the retained consent anchor: the prefix this client admitted was rewritten"
  else .ok ()

/-- **An accepted comparison is the anchor's commitment**: the Store's chain
after the anchor's height of records is the anchor's chain. -/
theorem checkStore_ok {anchor : Anchor} {loaded : Durable} {chains : List Digest}
    (chainsExact : chains = DurableLogTags.chainPrefixes loaded.logStart loaded.image.accepted)
    (accepted : checkStore anchor loaded chains = .ok ()) :
    loaded.logStart = anchor.logStart ∧ anchor.height ≤ loaded.image.accepted.length ∧
      chainAfter loaded.logStart (loaded.image.accepted.take anchor.height) = anchor.chain := by
  unfold checkStore at accepted
  by_cases started : loaded.logStart = anchor.logStart
  · by_cases low : loaded.image.accepted.length < anchor.height
    · simp [started, low] at accepted
    · by_cases differs : chains[anchor.height]? = some anchor.chain
      · have within : anchor.height ≤ loaded.image.accepted.length := Nat.le_of_not_lt low
        refine ⟨started, within, ?_⟩
        rw [chainsExact, DurableLogTags.chainPrefixes_getElem? _ _ _ within] at differs
        exact Option.some.inj differs
      · simp [started, low, differs] at accepted
  · simp [started] at accepted

/-- **A rewritten prefix refuses.** If the Store's records up to the anchor's
height do not chain to the anchor's chain, the comparison refuses. -/
theorem checkStore_refuses_rewritten {anchor : Anchor} {loaded : Durable} {chains : List Digest}
    (chainsExact : chains = DurableLogTags.chainPrefixes loaded.logStart loaded.image.accepted)
    (rewritten : chainAfter loaded.logStart (loaded.image.accepted.take anchor.height) ≠ anchor.chain) :
    ∃ detail, checkStore anchor loaded chains = .error detail := by
  cases checked : checkStore anchor loaded chains with
  | error detail => exact ⟨detail, rfl⟩
  | ok done =>
      cases done
      exact absurd (checkStore_ok chainsExact checked).2.2 rewritten

#assert_axioms checkStore_ok
#assert_axioms checkStore_refuses_rewritten

/-- `checkStore` over a chain-only read of the Store: its genesis log start,
its head height and the chain after every stored record. -/
def checkStored (anchor : Anchor) (logStart : Digest) (head : Nat) (chains : List Digest) :
    Except String Unit :=
  if logStart ≠ anchor.logStart then
    .error "the Store's genesis log differs from the retained consent anchor's"
  else if head < anchor.height then
    .error s!"the Store's head {head} is below the retained consent anchor at {anchor.height}: the accepted history was rolled back"
  else if chains[anchor.height]? ≠ some anchor.chain then
    .error s!"the Store's accepted history up to height {anchor.height} differs from the retained consent anchor: the prefix this client admitted was rewritten"
  else .ok ()

/-- **The re-check is the resume's comparison**: on a full open's head and
chain prefixes, `checkStored` is `checkStore`, refusal text included. -/
theorem checkStore_eq_checkStored (anchor : Anchor) (loaded : Durable) (chains : List Digest) :
    checkStore anchor loaded chains =
      checkStored anchor loaded.logStart loaded.image.accepted.length chains := rfl

/-- An accepted re-check: the same genesis log, a head at or above the anchor,
and the anchor's chain after its height of records. -/
theorem checkStored_ok {anchor : Anchor} {logStart : Digest} {head : Nat} {chains : List Digest}
    (accepted : checkStored anchor logStart head chains = .ok ()) :
    logStart = anchor.logStart ∧ anchor.height ≤ head ∧ chains[anchor.height]? = some anchor.chain := by
  unfold checkStored at accepted
  by_cases started : logStart = anchor.logStart
  · by_cases low : head < anchor.height
    · simp [started, low] at accepted
    · by_cases same : chains[anchor.height]? = some anchor.chain
      · exact ⟨started, Nat.le_of_not_lt low, same⟩
      · simp [started, low, same] at accepted
  · simp [started] at accepted

#assert_axioms checkStore_eq_checkStored
#assert_axioms checkStored_ok

/-- Re-check, from the Store's stored bytes alone, that it still carries the
prefix an anchor commits to: the seed's log start, the head, and the chain over
every STORED record (`chainPrefixesStored`, which equals the specification
chain over the records the bytes decode to: `chainPrefixesStored_eq`). Nothing
is decoded, replayed or validated beyond that: the caller holds its own admitted
image and never re-reads one from the Store. A resident consent provider runs it
once per client connection, so a rollback or prefix rewrite between commands is
refused exactly as a per-process `resume` refuses it (`checkStore_eq_checkStored`). -/
def recheckStore (transport : DurableReceiverIO.Transport) (anchor : Anchor) :
    IO (Except String Unit) := do
  match ← transport.read 1 true with
  | .error message => return .error message
  | .ok none => return .error "durable store is not initialized"
  | .ok (some stored) =>
      let some seedBytes := stored.seed | return .error "durable seed missing"
      if let some refusal := (DurableCheckpointCodec.SeedEpoch.ofBytes seedBytes).refusal then
        return .error s!"durable store refused: {refusal}"
      let some seed := DurableCheckpointCodec.seedFrame.decode seedBytes
        | return .error "noncanonical durable seed"
      if stored.entries.length ≠ stored.head then
        return .error "durable log head does not match its entries"
      let logStart := transport.logStart seed
      return checkStored anchor logStart stored.head
        (DurableLogTags.chainPrefixesStored logStart (stored.entries.map (·.record)))

/-! ## The O(1) re-check (HOT-PATH 2f)

`recheckStore` reads the whole log and re-hashes its chain from genesis: O(history) per client
connection, twice per signed write, the term that made consent grow 1.6 ms per record
(L11-PERF §0). A resident provider holds more than an anchor: `Loaded.headTag`, the exact bytes
of the Store's tag at its height, whose MAC it verified when it admitted that height
(`DurableLogTags.verifyTags`). The re-check below reads the Store's entry AT that height (one
`transport.read height`, no records before it) and compares the bytes.

What it refuses exactly: a rollback (`recheckHeld_head`: the head is at or above the held
height). What it refuses up to a KMAC256 collision: a rewrite the Store re-tagged (a different
chain is a different MAC input, so different bytes). What it defers: a rewrite that left the
old tag in place is not seen here; every read of those records goes through the Reader, which
verifies each record against the MAC'd head (`DurableHistoryReader.fetch`), and the signer's
state is never re-read from the Store (`Anchored`/`Verified` hold it). The exact-prefix
guarantee -- the signer signs over the fold of exactly the records it admitted -- never rested
on this re-check; `trailer_eq_carried` says equal tag bytes carry equal (root, chain, frontier,
index root), so the held comparison is a comparison of the chain at the height.

RULING (ember, 2026-10-27): ACCEPTED. Detection of a self-inconsistent prefix rewrite moves to the
verified read that touches it; rollback and re-tagged rewrites stay refused; the exact-prefix
guarantee (`headTag` equality at the provider's height + exact prefix) is unchanged. -/

/-- Equal stored tags carry equal values: the trailer encodes `Carried` in the clear through a
lawful codec, so no two carried values share tag bytes. -/
theorem trailer_eq_carried (key : DurableCheckpointCodec.MacKey) (height : Nat)
    (left right : DurableHistory.Carried)
    (same : DurableHistory.trailer key height left = DurableHistory.trailer key height right) :
    left = right := by
  have encoded : DurableHistory.trailerStream.toLawful.encode (left, DurableHistory.tagMac key height left) =
      DurableHistory.trailerStream.toLawful.encode (right, DurableHistory.tagMac key height right) := same
  exact congrArg Prod.fst (ResourceBirthCodec.lawful_encode_injective DurableHistory.trailerStream.toLawful encoded)

/-- The held re-check: the Store's entry at `height` still carries the exact tag this provider
verified there, and the head has not fallen below it. -/
def recheckHeld (transport : DurableReceiverIO.Transport) (height : Nat) (heldTag : List UInt8) :
    IO (Except String Unit) := do
  match ← transport.read height false with
  | .error message => return .error message
  | .ok none => return .error "durable store is not initialized"
  | .ok (some stored) =>
      if stored.head < height then
        return .error s!"the Store's head {stored.head} is below the height {height} this provider admitted: the accepted history was rolled back"
      match stored.entries.head? with
      | none => return .error s!"the Store carries no entry at the height {height} this provider admitted"
      | some entry =>
          if entry.tag = heldTag then return .ok ()
          else return .error s!"the Store's entry at height {height} no longer carries the tag this provider verified: the prefix this client admitted was rewritten or re-keyed"

/-- The judgement `recheckHeld` makes of what it read, as data: head, and the first entry's tag. -/
def checkHeld (height : Nat) (heldTag : List UInt8) (head : Nat) (first : Option (List UInt8)) :
    Except String Unit :=
  if head < height then .error "rolled back"
  else match first with
    | none => .error "no entry"
    | some tag => if tag = heldTag then .ok () else .error "rewritten"

/-- An accepted held re-check is a head at or above the held height carrying exactly the held tag. -/
theorem checkHeld_ok {height : Nat} {heldTag : List UInt8} {head : Nat} {first : Option (List UInt8)}
    (accepted : checkHeld height heldTag head first = .ok ()) :
    height ≤ head ∧ first = some heldTag := by
  unfold checkHeld at accepted
  by_cases below : head < height
  · simp [below] at accepted
  · refine ⟨Nat.le_of_not_lt below, ?_⟩
    cases first with
    | none => simp [below] at accepted
    | some tag =>
        by_cases same : tag = heldTag
        · rw [same]
        · simp [below, same] at accepted

/-- **Teeth**: a rolled-back head refuses, and a different tag refuses. -/
theorem checkHeld_refuses_rollback (height : Nat) (heldTag : List UInt8) (head : Nat)
    (first : Option (List UInt8)) (below : head < height) :
    checkHeld height heldTag head first ≠ .ok () := by
  simp [checkHeld, below]

theorem checkHeld_refuses_other_tag (height : Nat) (heldTag other : List UInt8) (head : Nat)
    (fits : height ≤ head) (differs : other ≠ heldTag) :
    checkHeld height heldTag head (some other) ≠ .ok () := by
  simp [checkHeld, Nat.not_lt.mpr fits, differs]

/-- **Satisfiable**: the held tag at a head at the height is accepted. -/
theorem checkHeld_satisfiable (height : Nat) (heldTag : List UInt8) :
    checkHeld height heldTag height (some heldTag) = .ok () := by
  simp [checkHeld]

/-- A target admitted after a retained anchor: the anchor's exact opening, cut
from this target and validated, then native admission of every later record.
Constructed only by `resume`. -/
structure Anchored (config : Config) (target : Durable) where
  private mk ::
  anchor : Anchor
  start : Opened config
  startExact : Anchor.ofOpened start = anchor
  /-- The opening is folded from the seed (`Loaded.prefixOwn`): no Store
  checkpoint is its base. -/
  startGenesis : start.durable.baseHeight = 0 ∧
    start.durable.base = DurableCheckpoint.State.ofSeed start.durable.image.seed
  suffix : NativeHostReplay.SuffixVerified config start target

/-- **The target's prefix is the one the anchor commits to**: its chain after
the anchor's height of records is the anchor's chain. -/
theorem Anchored.prefix_committed {config : Config} {target : Durable}
    (anchored : Anchored config target) :
    chainAfter target.logStart (target.image.accepted.take anchored.anchor.height) =
      anchored.anchor.chain := by
  rw [← anchored.startExact]
  show chainAfter target.logStart
      (target.image.accepted.take anchored.start.durable.image.accepted.length) =
    anchored.start.durable.chain
  rw [anchored.suffix.logStartExact, anchored.suffix.prefixExact, anchored.start.durable.chainExact]

#assert_axioms Anchored.prefix_committed

/-- The head state of an opening, `State.ofSnapshot` of its image and snapshot
(`headState_eq`), with the cells read off the opening's cached enumeration
(`Loaded.cells`, compiled to `cellsCached`): `Image.cellIds` itself flattens every
write of the log and deduplicates it, and a consent provider builds its own bases
after every admission. -/
def headState (durable : Durable) : DurableCheckpoint.State :=
  ⟨durable.image.seed.absentBytes, durable.cells, durable.snapshot.model.available⟩

theorem headState_eq (durable : Durable) :
    headState durable = DurableCheckpoint.State.ofSnapshot durable.image durable.snapshot := rfl

/-- **The own base of a genesis-based image** (CONSENT-OWN): its head state,
which is the genesis fold of its records (`resume_genesis` on the image's own
`resumed`), so a past read from it needs no premise about who sealed it. -/
def ownOfGenesis (durable : Durable)
    (genesis : durable.baseHeight = 0 ∧
      durable.base = DurableCheckpoint.State.ofSeed durable.image.seed) :
    DurableHistoryReader.OwnBase ResourceBirthCodec.rootBytes :=
  ⟨durable.image.seed, durable.logStart, durable.image.accepted.length, durable.chain,
    Thunk.mk fun _ => headState durable,
    ⟨durable.image.accepted, rfl, durable.chainExact.symm, durable.snapshot, by
      have folded := durable.resumed
      rw [genesis.1, genesis.2, DurableCheckpoint.resume_genesis] at folded
      simpa only [DurableReceiver.Image.ofAccepted_accepted] using folded,
      by show headState durable = _; rw [headState_eq, DurableReceiver.Image.ofAccepted_accepted]⟩⟩

/-- **The held image of an anchored admission is genesis-based**: the suffix
walk keeps its anchor's base (`AdmittedSuffix.base`), and the anchor's is the
seed. -/
theorem Anchored.opened_genesis {config : Config} {target : Durable}
    (anchored : Anchored config target) :
    anchored.suffix.opened.durable.baseHeight = 0 ∧
      anchored.suffix.opened.durable.base =
        DurableCheckpoint.State.ofSeed anchored.suffix.opened.durable.image.seed := by
  obtain ⟨height, base⟩ := anchored.suffix.admitted.base
  have imaged := anchored.suffix.exactImage
  refine ⟨height.trans anchored.startGenesis.1, ?_⟩
  rw [base, anchored.startGenesis.2, imaged, anchored.suffix.seedExact]

#assert_axioms Anchored.opened_genesis

/-- The own bases an anchored admission holds: its opening at the anchor and
its head. -/
def Anchored.own {config : Config} {target : Durable} (anchored : Anchored config target) :
    List (DurableHistoryReader.OwnBase ResourceBirthCodec.rootBytes) :=
  [ownOfGenesis anchored.suffix.opened.durable anchored.opened_genesis,
    ownOfGenesis anchored.start.durable anchored.startGenesis]

/-- Why a resume did not produce an anchored target. A contradiction is a
refusal: the Store disagrees with what this client admitted, and no fallback
may hide it. A suffix failure may be a record whose admission needs history
before the anchor (a claim of an older BEGIN, say); the caller re-admits from
genesis, which either accepts it or refuses it for good. -/
inductive ResumeError where
  | contradicted (detail : String)
  | suffix (failure : NativeHostReplay.Failure)

private theorem take_length_take {α : Type} (list : List α) (count : Nat) :
    list.take (list.take count).length = list.take count := by
  rw [List.length_take]
  by_cases within : count ≤ list.length
  · rw [Nat.min_eq_left within]
  · have beyond : list.length ≤ count := Nat.le_of_lt (Nat.lt_of_not_le within)
    rw [Nat.min_eq_right beyond, List.take_length, List.take_of_length_le beyond]

/-- Resume after a retained anchor over a full open that kept its chain
prefixes (`DurableReceiverIO.loadChained`). -/
def resume (config : Config) {store : DurableHistory.StoreIdentity}
    (reader : DurableHistoryReader.Reader ResourceBirthCodec.rootBytes store)
    (anchor : Anchor) (target : Durable) (chains : List Digest)
    (chainsExact : chains = DurableLogTags.chainPrefixes target.logStart target.image.accepted) :
    IO (Except ResumeError (Anchored config target)) := do
  if let .error detail := checkStore anchor target chains then
    return .error (.contradicted detail)
  -- The opening is folded from the seed: the Store's checkpoint (the operator's
  -- seal) is never a client base, and no operator tag root is kept.
  match target.prefixOwn anchor.height chains chainsExact with
  | .error detail => return .error (.contradicted s!"retained consent anchor prefix: {detail}")
  | .ok ⟨cut, imaged, started, zero, seeded, _⟩ =>
    match validated : validateLoaded config cut with
    | .error detail =>
        return .error (.contradicted s!"the Store's image at the retained consent anchor is invalid: {detail}")
    | .ok start =>
      if exact : Anchor.ofOpened start = anchor then
        have wraps := validateLoaded_durable validated
        have seedExact : target.image.seed = start.durable.image.seed := by
          rw [wraps, imaged, DurableReceiver.Image.ofAccepted_seed]
        have anchorWithin : start.durable.image.accepted.length ≤ target.image.accepted.length := by
          rw [wraps, imaged, DurableReceiver.Image.accepted_ofAccepted, List.length_take]
          exact Nat.min_le_right _ _
        have prefixExact : target.image.accepted.take start.durable.image.accepted.length =
            start.durable.image.accepted := by
          rw [wraps, imaged, DurableReceiver.Image.accepted_ofAccepted]
          exact take_length_take _ _
        have logStartExact : target.logStart = start.durable.logStart := by rw [wraps, started]
        have startGenesis : start.durable.baseHeight = 0 ∧
            start.durable.base = DurableCheckpoint.State.ofSeed start.durable.image.seed := by
          refine ⟨by rw [wraps]; exact zero, ?_⟩
          rw [wraps, seeded, imaged, DurableReceiver.Image.ofAccepted_seed]
        -- Past states the suffix admission reads resume from this opening or the seed.
        let own := reader.ownOnly config.transport [ownOfGenesis start.durable startGenesis]
        match ← NativeHostReplay.verifySuffixFrom config start own target none seedExact anchorWithin
            prefixExact logStartExact with
        | .error failure => return .error (.suffix failure)
        | .ok suffix => return .ok ⟨anchor, start, exact, startGenesis, suffix⟩
      else
        return .error (.contradicted
          "the Store's image at the retained consent anchor does not reproduce the anchor's world root")

/-- What a consent provider holds for its current target: either the full
re-admission from genesis, or an anchored admission of the records after a
retained anchor. Lifecycle consent, which selects from chronology before the
anchor, upgrades to `full` (`Basis.full?`). -/
inductive Basis (config : Config) (target : Durable) where
  | full (verified : NativeHostReplay.Verified config target)
  | anchored (anchored : Anchored config target)

def Basis.opened {config : Config} {target : Durable} : Basis config target → Opened config
  | .full verified => verified.opened
  | .anchored held => held.suffix.opened

/-- Either way the held opening is the target's exact image. -/
theorem Basis.image_exact {config : Config} {target : Durable} :
    (basis : Basis config target) → basis.opened.durable.image = target.image
  | .full verified => verified.exactImage
  | .anchored held => held.suffix.exactImage

/-- The own bases this basis holds (`Anchored.own`); a full re-admission
contributes none, so its past reads fold from the seed. -/
def Basis.own {config : Config} {target : Durable} :
    Basis config target → List (DurableHistoryReader.OwnBase ResourceBirthCodec.rootBytes)
  | .full _ => []
  | .anchored held => held.own

/-- The anchor this basis leaves for the next provider. -/
def Basis.anchor {config : Config} {target : Durable} (basis : Basis config target) : Anchor :=
  Anchor.ofOpened basis.opened

/-- The full re-admission, running it from genesis when the basis is anchored. -/
def Basis.full? (config : Config) {store : DurableHistory.StoreIdentity}
    (reader : DurableHistoryReader.Reader ResourceBirthCodec.rootBytes store) {target : Durable} :
    Basis config target → IO (Except NativeHostReplay.Failure (NativeHostReplay.Verified config target))
  | .full verified => pure (.ok verified)
  | .anchored _ => NativeHostReplay.verifyLoaded config reader target

/-- Extend either basis over a target that is the old one followed by more
records (`DurableReceiverIO.extendFrom`): only those records are admitted. -/
def Basis.extendAppended (config : Config) {store : DurableHistory.StoreIdentity}
    (reader : DurableHistoryReader.Reader ResourceBirthCodec.rootBytes store) {oldTarget : Durable}
    (basis : Basis config oldTarget) (target : Durable)
    (seedExact : target.image.seed = oldTarget.image.seed)
    (acceptedExact : target.image.accepted = oldTarget.image.accepted ++
      target.image.accepted.drop oldTarget.image.accepted.length)
    (logStartExact : target.logStart = oldTarget.logStart) :
    IO (Except NativeHostReplay.Failure (Basis config target)) := do
  match basis with
  | .full verified =>
      return (← NativeHostReplay.extendVerifiedAppended config reader verified target seedExact
        acceptedExact).map .full
  | .anchored held =>
      have within : oldTarget.image.accepted.length ≤ target.image.accepted.length := by
        rw [acceptedExact, List.length_append]
        exact Nat.le_add_right _ _
      have prefixExact : target.image.accepted.take oldTarget.image.accepted.length =
          oldTarget.image.accepted := by
        rw [acceptedExact]
        exact List.take_left' rfl
      return (← NativeHostReplay.extendSuffixAppended config reader held.suffix target seedExact
        within prefixExact logStartExact).map fun suffix =>
          .anchored ⟨held.anchor, held.start, held.startExact, held.startGenesis, suffix⟩

/-! ## The Store epoch names the deployed constants

The epoch reads the actual state-key identity and the content-derived schema
digest. The imported census closes that digest's registry over the receiving
codecs, including frames nested in opaque persisted byte fields. -/

theorem storeEpoch_stateKey :
    DurableCheckpointCodec.StoreEpoch.current.stateKey = DeclaredEffectCell.stateKeyCodecId := rfl

theorem storeEpoch_schemaRefs :
    DurableCheckpointCodec.StoreEpoch.current.schemaRefs =
      DurableCheckpointCodec.persistedSchemaRefs := rfl

#assert_axioms storeEpoch_stateKey
#assert_axioms storeEpoch_schemaRefs

/-- The command-codec component and the delegation command frame version it
replays, pinned together: moving either alone breaks this theorem. -/
theorem storeEpoch_commands :
    DurableCheckpointCodec.StoreEpoch.current.commands = "commands/v2" ∧
      CapabilityDelegationController.commandFrame.getLast? = some 2 :=
  ⟨rfl, by simp [CapabilityDelegationController.commandFrame]⟩

#assert_axioms storeEpoch_commands

end Minidregg.Kernel.ConsentAnchor
