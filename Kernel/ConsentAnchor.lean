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
* cuts the Store at the anchor (`Loaded.prefixAt`), validates that image, and
  refuses unless it reproduces the anchor exactly, world root included;
* natively admits every record after the anchor (`verifySuffixFrom`).

Trust premise, stated once: the anchor bytes are the client's custody, written
by a provider that had admitted that prefix (`Basis.anchor`). A Lean proof
cannot cross a process boundary; the anchor file is the same kind of input as
the signing key beside it. The chain is what makes it a commitment: equal
chains are equal prefixes, up to a collision of the deployed hash.
-/
import Kernel.NativeHostReplay
import Compiler.DeployedCellRegistry

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
    match (ResourceBirthCodec.strictCodec anchorStream.toLawful).decode
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
  have exact := (ResourceBirthCodec.strictCodec anchorStream.toLawful).decode_encode anchor
  unfold decode encode
  rw [if_pos tagged, body]
  rw [show (ResourceBirthCodec.strictCodec anchorStream.toLawful).decode
      (anchorStream.encode anchor) = some anchor from exact]

#assert_axioms decode_encode

/-- The anchor of a validated opening. -/
def Anchor.ofOpened {config : Config} (opened : Opened config) : Anchor :=
  ⟨opened.durable.height, opened.durable.logStart, opened.durable.chain,
    opened.durable.worldRoot⟩

/-- The physical comparisons an anchor makes against a full open of the
Store, before any image is cut or record admitted. -/
def checkStore (anchor : Anchor) (loaded : Durable) (chains : List Digest) : Except String Unit :=
  if loaded.logStart ≠ anchor.logStart then
    .error "the Store's genesis log differs from the retained consent anchor's"
  else if loaded.height < anchor.height then
    .error s!"the Store's head {loaded.height} is below the retained consent anchor at {anchor.height}: the accepted history was rolled back"
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

/-- A target admitted after a retained anchor: the anchor's exact opening, cut
from this target and validated, then native admission of every later record.
Constructed only by `resume`. -/
structure Anchored (config : Config) (target : Durable) where
  private mk ::
  anchor : Anchor
  start : Opened config
  startExact : Anchor.ofOpened start = anchor
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
def resume (config : Config) (anchor : Anchor) (target : Durable) (chains : List Digest)
    (chainsExact : chains = DurableLogTags.chainPrefixes target.logStart target.image.accepted) :
    IO (Except ResumeError (Anchored config target)) := do
  if let .error detail := checkStore anchor target chains then
    return .error (.contradicted detail)
  match target.prefixAt anchor.height chains chainsExact with
  | .error detail => return .error (.contradicted s!"retained consent anchor prefix: {detail}")
  | .ok ⟨cut, imaged, started⟩ =>
    match validated : validateLoaded config cut with
    | .error detail =>
        return .error (.contradicted s!"the Store's image at the retained consent anchor is invalid: {detail}")
    | .ok start =>
      if exact : Anchor.ofOpened start = anchor then
        have wraps := validateLoaded_durable validated
        have seedExact : target.image.seed = start.durable.image.seed := by rw [wraps, imaged]
        have anchorWithin : start.durable.height ≤ target.height := by
          rw [wraps, imaged]
          show (target.image.accepted.take anchor.height).length ≤ _
          rw [List.length_take]
          exact Nat.min_le_right _ _
        have prefixExact : target.image.accepted.take start.durable.height =
            start.durable.image.accepted := by
          rw [wraps, imaged]
          exact take_length_take _ _
        have logStartExact : target.logStart = start.durable.logStart := by rw [wraps, started]
        match ← NativeHostReplay.verifySuffixFrom config start target none seedExact anchorWithin
            prefixExact logStartExact with
        | .error failure => return .error (.suffix failure)
        | .ok suffix => return .ok ⟨anchor, start, exact, suffix⟩
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

/-- The anchor this basis leaves for the next provider. -/
def Basis.anchor {config : Config} {target : Durable} (basis : Basis config target) : Anchor :=
  Anchor.ofOpened basis.opened

/-- The full re-admission, running it from genesis when the basis is anchored. -/
def Basis.full? (config : Config) {target : Durable} :
    Basis config target → IO (Except NativeHostReplay.Failure (NativeHostReplay.Verified config target))
  | .full verified => pure (.ok verified)
  | .anchored _ => NativeHostReplay.verifyLoaded config target

/-- Extend either basis over a target that is the old one followed by more
records (`DurableReceiverIO.extendFrom`): only those records are admitted. -/
def Basis.extendAppended (config : Config) {oldTarget : Durable}
    (basis : Basis config oldTarget) (target : Durable)
    (seedExact : target.image.seed = oldTarget.image.seed)
    (acceptedExact : target.image.accepted = oldTarget.image.accepted ++
      target.image.accepted.drop oldTarget.image.accepted.length)
    (logStartExact : target.logStart = oldTarget.logStart) :
    IO (Except NativeHostReplay.Failure (Basis config target)) := do
  match basis with
  | .full verified =>
      return (← NativeHostReplay.extendVerifiedAppended config verified target seedExact
        acceptedExact).map .full
  | .anchored held =>
      have within : oldTarget.image.accepted.length ≤ target.height := by
        rw [acceptedExact, List.length_append]
        exact Nat.le_add_right _ _
      have prefixExact : target.image.accepted.take oldTarget.image.accepted.length =
          oldTarget.image.accepted := by
        rw [acceptedExact]
        exact List.take_left' rfl
      return (← NativeHostReplay.extendSuffixAppended config held.suffix target seedExact
        within prefixExact logStartExact).map fun suffix =>
          .anchored ⟨held.anchor, held.start, held.startExact, suffix⟩

/-! ## The Store epoch names the deployed constants

`DurableCheckpointCodec.StoreEpoch.current` sits below the modules that define
the state-key codec and the schema references, so it spells them; these two
equations break the build when either constant moves without the epoch. -/

theorem storeEpoch_stateKey :
    DurableCheckpointCodec.StoreEpoch.current.stateKey = DeclaredEffectCell.stateKeyCodecId := rfl

theorem storeEpoch_schemaRefs :
    DurableCheckpointCodec.StoreEpoch.current.schemaRefs =
      s!"schema-refs/v{DeployedCellRegistry.declaredEffectSchemaRef.version}" := by
  decide

#assert_axioms storeEpoch_stateKey
#assert_axioms storeEpoch_schemaRefs

end Minidregg.Kernel.ConsentAnchor
