/-
# Where a consent provider starts: the Store's snapshot, then every record after it

A full-peer consent provider (`Host.ClientConsentCore`) admits the Store's
history before it signs anything. Each client process (or resident) starts a
provider, so where it starts is the cost of every first command.

**CONSENT-STORE** (ruling, ember 2026-10-31: "We trust the storage device.
That isn't 'operator trust', that's just the threat model we're working
within."). A provider starts from the base the Store's open uses: its latest
MAC-verified checkpoint (`DurableReceiverIO.loadChained`, at most one checkpoint
interval below the head), or the seed. It natively admits EVERY record after
its start (`NativeHostReplay.verifySuffixFrom`): full-record comparison,
tail-law judgement and post-image validation at each original height. Past
states its admissions read resume from the Store's checkpoints too (the plain
`Reader.stateAt`). Nothing is folded from genesis.

An `Anchor` is what one admission leaves under the client's custody: the
height it reached, the genesis log start, the log chain after that height and
the world root there. A later provider (`resume`):

* refuses a Store whose log start differs, whose head is below the anchor (the
  accepted history was rolled back), or whose chain after the anchor's height
  is not the anchor's chain (the prefix this client admitted was rewritten or
  forked) — `checkStore_ok`, `checkStore_refuses_rewritten`, `startHeight_refuses_rewritten`;
* starts at the Store's base, or at the anchor when the anchor is above it
  (`startHeight`): then the cut there must reproduce the anchor exactly, world
  root included, and only the records after the anchor are admitted.

Trust premises, stated once: the storage device (the Store's checkpoint is
the state after its height, as its MAC says), and the anchor bytes, which are
the client's custody beside its signing key. A Lean proof cannot cross a
process boundary; neither can be established here. The chain is what makes an
anchor a commitment: equal chains are equal prefixes, up to a collision of the
deployed hash.
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

/-- The epoch of the retained bytes: it names the consent statement an anchor was
admitted under (v2: CONSENT-STORE). A record of another epoch is set aside, never
refused (`decode`): an anchor is bound to admission semantics, and a provider
whose statement moved starts from the Store's base instead. -/
def epochTag : List UInt8 := "MINI-CONSENT-ANCHOR/v2".toUTF8.toList

def anchorStream : StreamCodec Anchor :=
  StreamCodec.xmap
    (StreamCodec.product StreamCodec.nat
      (StreamCodec.product digestStream (StreamCodec.product digestStream digestStream)))
    (fun anchor => (anchor.height, anchor.logStart, anchor.chain, anchor.root))
    (fun tuple => ⟨tuple.1, tuple.2.1, tuple.2.2.1, tuple.2.2.2⟩)
    (by intro value; cases value; rfl)

def encode (anchor : Anchor) : List UInt8 := epochTag ++ anchorStream.encode anchor

/-- Exact decode: the v2 tag, then the canonical record and nothing after it. A
record under another epoch tag decodes to `none` (set aside); a v2-tagged record
that is not canonical refuses (the custody file is damaged). -/
def decode (bytes : List UInt8) : Except String (Option Anchor) :=
  if bytes.take epochTag.length = epochTag then
    match anchorStream.toLawful.decode
        (bytes.drop epochTag.length) with
    | some anchor => .ok (some anchor)
    | none => .error "retained consent anchor is not a canonical MINI-CONSENT-ANCHOR/v2 record"
  else .ok none

theorem decode_encode (anchor : Anchor) : decode (encode anchor) = .ok (some anchor) := by
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

/-- **Another epoch is set aside**: bytes that do not start with the v2 tag carry no anchor. -/
theorem decode_other_epoch (bytes : List UInt8) (other : bytes.take epochTag.length ≠ epochTag) :
    decode bytes = .ok none := by
  unfold decode
  rw [if_neg other]

#assert_axioms decode_other_epoch
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

/-! ## The start (CONSENT-STORE) -/

/-- **Where native admission starts**: the Store's own base (its MAC-verified
checkpoint, or the seed), or a retained anchor above it. A retained anchor the
Store contradicts (`checkStore`) refuses. -/
def startHeight (retained : Option Anchor) (loaded : Durable) (chains : List Digest) :
    Except String Nat :=
  match retained with
  | none => .ok loaded.baseHeight
  | some anchor =>
      match checkStore anchor loaded chains with
      | .error detail => .error detail
      | .ok () => .ok (max loaded.baseHeight anchor.height)

/-- **Satisfiable**: with no retained anchor, admission starts at the Store's base. -/
theorem startHeight_none (loaded : Durable) (chains : List Digest) :
    startHeight none loaded chains = .ok loaded.baseHeight := rfl

/-- **What an accepted start is**: at or above the Store's base, within the log, and
at or above a retained anchor whose genesis log and prefix are the Store's. -/
theorem startHeight_ok {retained : Option Anchor} {loaded : Durable} {chains : List Digest}
    {height : Nat}
    (chainsExact : chains = DurableLogTags.chainPrefixes loaded.logStart loaded.image.accepted)
    (accepted : startHeight retained loaded chains = .ok height) :
    loaded.baseHeight ≤ height ∧ height ≤ loaded.image.accepted.length ∧
      ∀ anchor, retained = some anchor →
        anchor.height ≤ height ∧ loaded.logStart = anchor.logStart ∧
          chainAfter loaded.logStart (loaded.image.accepted.take anchor.height) = anchor.chain := by
  cases retained with
  | none =>
      cases accepted
      exact ⟨Nat.le_refl _, loaded.withinLog, fun _ absent => by cases absent⟩
  | some anchor =>
      cases checked : checkStore anchor loaded chains with
      | error detail => simp only [startHeight, checked] at accepted; cases accepted
      | ok done =>
          cases done
          simp only [startHeight, checked, Except.ok.injEq] at accepted
          subst accepted
          obtain ⟨started, within, chained⟩ := checkStore_ok chainsExact checked
          refine ⟨Nat.le_max_left _ _, Nat.max_le.mpr ⟨loaded.withinLog, within⟩, ?_⟩
          intro other same
          cases same
          exact ⟨Nat.le_max_right _ _, started, chained⟩

/-- **Teeth**: a retained anchor whose prefix the Store rewrote refuses the start. -/
theorem startHeight_refuses_rewritten {anchor : Anchor} {loaded : Durable} {chains : List Digest}
    (chainsExact : chains = DurableLogTags.chainPrefixes loaded.logStart loaded.image.accepted)
    (rewritten : chainAfter loaded.logStart (loaded.image.accepted.take anchor.height) ≠ anchor.chain) :
    ∃ detail, startHeight (some anchor) loaded chains = .error detail := by
  obtain ⟨detail, refused⟩ := checkStore_refuses_rewritten chainsExact rewritten
  exact ⟨detail, by simp only [startHeight, refused]⟩

#assert_axioms startHeight_ok
#assert_axioms startHeight_refuses_rewritten

/-- Whether an opening reproduces a retained anchor where it must: an anchor above
the Store's base is the start itself, world root included. -/
def AnchorExact {config : Config} (base : Nat) (retained : Option Anchor) (start : Opened config) : Prop :=
  ∀ anchor, retained = some anchor → base < anchor.height → Anchor.ofOpened start = anchor

instance {config : Config} (base : Nat) (retained : Option Anchor) (start : Opened config) :
    Decidable (AnchorExact base retained start) :=
  match retained with
  | none => isTrue fun _ absent => by cases absent
  | some anchor =>
      if above : base < anchor.height then
        if same : Anchor.ofOpened start = anchor then
          isTrue fun other present _ => by cases present; exact same
        else isFalse fun holds => same (holds anchor rfl above)
      else isTrue fun other present within => by cases present; exact absurd within above

/-- What a retained anchor commits to, against an opening: its height is within the
opening, and the opening's genesis log and prefix up to that height are the anchor's. -/
def AnchorCommitted {config : Config} (retained : Option Anchor) (start : Opened config) : Prop :=
  ∀ anchor, retained = some anchor →
    anchor.height ≤ start.durable.image.accepted.length ∧ start.durable.logStart = anchor.logStart ∧
      chainAfter start.durable.logStart (start.durable.image.accepted.take anchor.height) = anchor.chain

/-- **A target admitted from the Store's snapshot** (CONSENT-STORE): the opening
at the start, cut on the base the Store's open used (`storeBase`: its MAC-verified
checkpoint, or the seed) and validated, then native admission of every later
record. Constructed only by `resume`, which records the open's own base. -/
structure Anchored (config : Config) (target : Durable) where
  private mk ::
  retained : Option Anchor
  /-- The base (height, state) of the Store's open this admission resumed over. -/
  storeBase : Nat × DurableCheckpoint.State
  start : Opened config
  /-- The start's base is the Store's. -/
  startBase : start.durable.baseHeight = storeBase.1 ∧ start.durable.base = storeBase.2
  /-- A retained anchor is at or below the start, and is the start's prefix. -/
  anchorCommitted : AnchorCommitted retained start
  /-- An anchor above the Store's base is the start, world root included. -/
  anchorExact : AnchorExact storeBase.1 retained start
  /-- Every record after the start, natively admitted at its original height. -/
  suffix : NativeHostReplay.SuffixVerified config start target

/-- **The admitted records are exactly the target's after the start**, and the
start is the target's prefix: nothing after the snapshot is taken on trust. -/
theorem Anchored.admits_after_start {config : Config} {target : Durable}
    (anchored : Anchored config target) :
    target.image.accepted.take anchored.start.durable.image.accepted.length =
        anchored.start.durable.image.accepted ∧
      NativeHostReplay.AdmittedSuffix config anchored.start
        (target.image.accepted.drop anchored.start.durable.image.accepted.length)
        anchored.suffix.opened anchored.suffix.receipts :=
  ⟨anchored.suffix.prefixExact, anchored.suffix.accepted_suffix⟩

private theorem take_of_prefix {α : Type} {whole part : List α} {count height : Nat}
    (prefixed : whole.take count = part) (within : height ≤ count) :
    part.take height = whole.take height := by
  rw [← prefixed, List.take_take]
  congr 1
  omega

/-- **The target's prefix is the one a retained anchor commits to**: its genesis
log is the anchor's and its chain after the anchor's height is the anchor's chain. -/
theorem Anchored.prefix_committed {config : Config} {target : Durable}
    (anchored : Anchored config target) {anchor : Anchor} (present : anchored.retained = some anchor) :
    target.logStart = anchor.logStart ∧
      chainAfter target.logStart (target.image.accepted.take anchor.height) = anchor.chain := by
  obtain ⟨within, started, chained⟩ := anchored.anchorCommitted anchor present
  have logStart := anchored.suffix.logStartExact
  refine ⟨logStart.trans started, ?_⟩
  rw [logStart, ← take_of_prefix anchored.suffix.prefixExact within]
  exact chained

#assert_axioms Anchored.admits_after_start
#assert_axioms Anchored.prefix_committed

/-- Why a resume did not produce an anchored target. A contradiction is a
refusal: the Store disagrees with what this client admitted, and no fallback
may hide it. A suffix failure may be a record whose admission needs history
before the start (a claim of an older BEGIN, say); the caller re-admits from
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

/-- Resume over a full open (`DurableReceiverIO.loadChained`): start at the Store's
base or the retained anchor above it (`startHeight`), cut there (`Chained.cutAbove`,
replaying only the records between the base and the start), validate, and admit
every record after it. -/
def resume (config : Config) {store : DurableHistory.StoreIdentity}
    (reader : DurableHistoryReader.Reader ResourceBirthCodec.rootBytes store)
    (retained : Option Anchor) (opened : DurableReceiverIO.Chained ResourceBirthCodec.rootBytes) :
    IO (Except ResumeError (Anchored config opened.loaded)) := do
  match started : startHeight retained opened.loaded opened.chains with
  | .error detail => return .error (.contradicted detail)
  | .ok height =>
    have bounds := startHeight_ok opened.chainsExact started
    match opened.cutAbove height with
    | .error detail => return .error (.contradicted s!"consent start at {height}: {detail}")
    | .ok ⟨cut, imaged, logStarted, based, baseExact⟩ =>
      match validated : validateLoaded config cut with
      | .error detail =>
          return .error (.contradicted s!"the Store's image at the consent start {height} is invalid: {detail}")
      | .ok start =>
        if exact : AnchorExact (opened.loaded.baseHeight, opened.loaded.base).1 retained start then
          have wraps := validateLoaded_durable validated
          have startLength : start.durable.image.accepted.length = height := by
            rw [wraps, imaged, DurableReceiver.Image.accepted_ofAccepted, List.length_take]
            exact Nat.min_eq_left bounds.2.1
          have seedExact : opened.loaded.image.seed = start.durable.image.seed := by
            rw [wraps, imaged, DurableReceiver.Image.ofAccepted_seed]
          have anchorWithin : start.durable.image.accepted.length ≤ opened.loaded.image.accepted.length := by
            rw [startLength]; exact bounds.2.1
          have prefixExact : opened.loaded.image.accepted.take start.durable.image.accepted.length =
              start.durable.image.accepted := by
            rw [wraps, imaged, DurableReceiver.Image.accepted_ofAccepted]
            exact take_length_take _ _
          have logStartExact : opened.loaded.logStart = start.durable.logStart := by rw [wraps, logStarted]
          have startBase : start.durable.baseHeight = (opened.loaded.baseHeight, opened.loaded.base).1 ∧
              start.durable.base = (opened.loaded.baseHeight, opened.loaded.base).2 := by
            rw [wraps]; exact ⟨based, baseExact⟩
          have anchorCommitted : AnchorCommitted retained start := by
            intro anchor present
            obtain ⟨below, sameStart, chained⟩ := bounds.2.2 anchor present
            have within : anchor.height ≤ start.durable.image.accepted.length := by
              rw [startLength]; exact below
            refine ⟨within, logStartExact.symm.trans sameStart, ?_⟩
            rw [← logStartExact, take_of_prefix prefixExact within]
            exact chained
          match ← NativeHostReplay.verifySuffixFrom config start reader opened.loaded none seedExact anchorWithin
              prefixExact logStartExact with
          | .error failure => return .error (.suffix failure)
          | .ok suffix =>
              return .ok ⟨retained, (opened.loaded.baseHeight, opened.loaded.base), start, startBase, anchorCommitted,
                exact, suffix⟩
        else
          return .error (.contradicted
            "the Store's image at the retained consent anchor does not reproduce the anchor's world root")

/-- What a consent provider holds for its current target: either the full
re-admission from genesis, or native admission of the records after its start
(the Store's snapshot or a retained anchor above it). Lifecycle consent, which
selects from chronology before the start, upgrades to `full` (`Basis.full?`). -/
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
          .anchored ⟨held.retained, held.storeBase, held.start, held.startBase, held.anchorCommitted,
            held.anchorExact, suffix⟩

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
