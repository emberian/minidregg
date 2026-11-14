/- Complete executable Generic Simplex, arXiv:2609.32985v1 Figures 1,3,4,5.
Fixed static n=3f+1 committee, authenticated reliable delivery, known delay bound
after unknown GST. Past views remain active. Exact block ancestry replaces hashes.
Source checking is an INTERNAL controller input, never a network packet.

Commit floor (not in the paper): `lastCommitted` is the highest view this replica has
committed. A view at or below it accepts no further message (`ingest`), a view strictly
below it keeps its send guards and outputs but drops its received messages (`retire`),
and a replica at or below it enters the view after it (`floorJump`).

Deviation from the paper's known-Delta timer: a view's timeout doubles with each
consecutive view entered since this replica's last local commit, up to
2^backoffCap (backoffCap = 0 is the paper's fixed timer). The deadline only
decides when this replica sends CANDIDATE(⊥); no safety rule reads it. -/
module

public import Std

-- Bodies this file reduces or derives through, not exposed by their modules (module system).
import all Init.Data.Repr
import all Init.Data.ToString.Basic
import all Init.Data.ToString.Extra
import all Init.Data.Array.Basic
import all Init.Data.ByteArray.Basic
import all Init.Data.String.Decode
import all Init.Data.String.Defs
import all Init.Control.Except
import all Init.Data.List.Basic
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.String.Bootstrap
import all Init.Data.Format.Basic
import all Init.Data.List.Scan.Basic
import all Init.Util

@[expose] public section

namespace Minidregg.Kernel.GenericSimplex
set_option autoImplicit false
abbrev Bytes := List UInt8
abbrev Block := List Bytes
abbrev Argument := Option Block
inductive Kind where
  | propose | vote | commit | candidate | ready
  deriving DecidableEq, BEq, Repr, Inhabited
structure Message where
  sender : Nat
  view : Nat
  kind : Kind
  value : Argument
  deriving DecidableEq, BEq, Repr, Inhabited
structure Config where
  parties : Nat
  faults : Nat
  timeout : Nat
  pumpBudget : Nat := 64
  /-- Exponent cap for the view-timeout backoff; 0 keeps the fixed timer. -/
  backoffCap : Nat := 0
  deriving DecidableEq, BEq, Repr, Inhabited
def Config.wellFormed (c : Config) : Bool :=
  c.parties == 3 * c.faults + 1 && c.timeout > 0 && c.pumpBudget > 0
def Config.quorum (c : Config) : Nat := c.parties - c.faults
def Config.leader (c : Config) (view : Nat) : Nat := (view - 1) % c.parties
structure View where
  number : Nat
  proposal : Option Block := none
  voted : Bool := false
  disableRequested : Bool := false
  sentCommit : Option Block := none
  sentCandidates : List Argument := []
  sentReadyCore : List Argument := []
  sentReadyRelay : List Argument := []
  prepared : List Block := []
  disabled : Bool := false
  committed : Option Block := none
  received : List Message := []
  deriving DecidableEq, BEq, Repr, Inhabited
/-- Ordered actual internal actions, retained across outbox drain and replay.
Clear outputs are recorded only on their first state change, so an enabled
already-satisfied rule does not keep the continuation pump alive. -/
inductive AuditEvent where
  | send (message : Message)
  | prepare (party view : Nat) (block : Block)
  | disable (party view : Nat)
  | commit (party view : Nat) (block : Block)
  | idle
  deriving DecidableEq, BEq, Repr, Inhabited
structure State where
  self : Nat
  current : Nat := 1
  deadline : Nat
  now : Nat := 0
  views : List View := []
  checked : List Block := []
  offers : List Bytes := []
  outbox : List Message := []
  audit : List AuditEvent := []
  delivered : List Block := []
  committedTip : Block := []
  needsPoll : Bool := false
  failed : Bool := false
  /-- The commit floor: the highest locally committed view (0 if none), maintained by
  `raiseFloor`. `lastCommittedView` is its specification. No rule writes a view at or
  below it, and none reads a view below it: the floor view is kept only as the parent it
  offers (`preparedAt`). -/
  lastCommitted : Nat := 0
  /-- The COMMIT messages that committed the floor view: what a peer still at or below the
  floor needs to commit it too. -/
  floorEvidence : List Message := []
  /-- Peers already served `floorEvidence` for this floor. -/
  served : List Nat := []
  /-- Evidence owed to a peer (destination, message); the driver forwards and drains it. -/
  relay : List (Nat × Message) := []
  deriving DecidableEq, BEq, Repr, Inhabited
def viewAt (s : State) (number : Nat) : View :=
  (s.views.find? (fun v => v.number == number)).getD { number := number }
def putView (s : State) (v : View) : State :=
  { s with views := if s.views.any (fun old => old.number == v.number) then
      s.views.map (fun old => if old.number == v.number then v else old)
    else s.views ++ [v] }
def addUnique {α : Type} [BEq α] (xs : List α) (x : α) : List α :=
  if xs.contains x then xs else xs ++ [x]
/-- Empty protocol blocks do not change the native source record history.
Consensus ancestry remains the full Block everywhere else. -/
def applicationHistory (block : Block) : Block :=
  block.filter (fun payload => !payload.isEmpty)

def isPrefix (a b : Block) : Bool := b.take a.length == a
/-- `State.checked` is the set of source histories the native checker has replayed from the
pinned genesis, kept as its maximal elements: a replay of a history replays every prefix of
it, so a history that is a prefix of a kept one is not kept, and a new history replaces the
kept ones it extends. One chain of source records is one entry, whatever its length. -/
def addChecked (checked : List Block) (block : Block) : List Block :=
  let history := applicationHistory block
  if history.isEmpty || checked.any (fun kept => isPrefix history kept) then checked
  else checked.filter (fun kept => !isPrefix kept history) ++ [history]
/-- A block is valid when its source history is a prefix of a checked one. Protocol-only
empty blocks neither modify source state nor consume a source height, so they do not count;
a different nonempty ancestor never matches. One walk of the block per kept history. -/
def validBlock (s : State) (block : Block) : Bool :=
  let history := applicationHistory block
  history.isEmpty || s.checked.any (fun kept => isPrefix history kept)
def register (s : State) (m : Message) : State :=
  let v := viewAt s m.view
  putView s { v with received := addUnique v.received m }
/-- Counts self locally once and retains broadcast for reliable other-member send. -/
def broadcast (s : State) (view : Nat) (kind : Kind) (value : Argument) : State :=
  let m : Message := ⟨s.self, view, kind, value⟩
  let s := register s m
  { s with outbox := s.outbox ++ [m], audit := s.audit ++ [.send m] }
def valuesFor (v : View) (kind : Kind) : List Argument :=
  ((v.received.filter (fun m => m.kind == kind)).map Message.value).eraseDups
/-- Detected equivocation permanently excludes the sender from VOTE counts only. -/
def voteEquivocator (v : View) (sender : Nat) : Bool :=
  ((v.received.filter (fun m => m.kind == .vote && m.sender == sender)).map Message.value).eraseDups.length > 1
def count (v : View) (kind : Kind) (value : Argument) : Nat :=
  ((v.received.filter fun m => m.kind == kind && m.value == value &&
    (kind != .vote || !voteEquivocator v m.sender)).map Message.sender).eraseDups.length
def clear (s : State) (number : Nat) (value : Argument) : State :=
  let v := viewAt s number
  match value with
  | none =>
      if v.disabled then s else
      let next := putView s { v with disabled := true }
      { next with audit := next.audit ++ [.disable s.self number] }
  | some block =>
      if validBlock s block && !v.prepared.contains block then
        let next := putView s { v with prepared := v.prepared ++ [block] }
        { next with audit := next.audit ++ [.prepare s.self number block] }
      else s
def doCommit (s : State) (number : Nat) (block : Block) : State :=
  if !validBlock s block then s else
  let s := clear s number (some block)
  let v := viewAt s number
  if v.committed.isSome then s else
  let s := putView s { v with committed := some block }
  let s := { s with audit := s.audit ++ [.commit s.self number block] }
  if isPrefix s.committedTip block then
    if s.committedTip == block then s else
      -- A committed payload is no longer work: the offers keep only what is still pending.
      { s with committedTip := block, delivered := s.delivered ++ [block],
               offers := s.offers.filter fun payload =>
                 !(block.drop s.committedTip.length).contains payload }
  else if isPrefix block s.committedTip then s
  else { s with failed := true }
/-- A commit above the floor raises the floor to its view. The floor keeps the COMMIT
messages that committed it; no view below it is read again (`forget` drops them). -/
def raiseFloor (s : State) (number : Nat) (block : Block) : State :=
  let v := viewAt s number
  if s.lastCommitted < number && v.committed == some block then
    { s with lastCommitted := number, served := [],
             floorEvidence := v.received.filter fun m => m.kind == .commit && m.value == some block }
  else s
def commitAt (s : State) (number : Nat) (block : Block) : State :=
  raiseFloor (doCommit s number block) number block
def sendCandidate (s : State) (number : Nat) (arg : Argument) : State :=
  let v := viewAt s number
  if v.sentCandidates.contains arg ||
      (v.sentCommit.isSome && v.sentCommit != arg) then s else
  let s := putView s { v with sentCandidates := v.sentCandidates ++ [arg] }
  broadcast s number .candidate arg
/-- The rules of one view for one block. A view at or below the floor has none. The commit
rule runs last: it can raise the floor to this view, after which nothing here may act. -/
def valueRules (c : Config) (s : State) (number : Nat) (block : Block) : State :=
  if number ≤ s.lastCommitted then s else Id.run do
  let mut s := s
  let arg := some block
  let v := viewAt s number
  if count v .vote arg ≥ c.quorum && validBlock s block then
    s := clear s number arg
    let v := viewAt s number
    if v.sentCommit.isNone && v.sentCandidates.all (fun a => a == arg) then
      s := putView s { v with sentCommit := some block }
      s := broadcast s number .commit arg
  let v := viewAt s number
  if count v .vote arg ≥ c.faults + 1 && validBlock s block then
    s := sendCandidate s number arg
  let v := viewAt s number
  if count v .commit arg ≥ c.quorum then s := commitAt s number block
  return s
def argumentRules (c : Config) (s : State) (number : Nat) (arg : Argument) : State :=
  if number ≤ s.lastCommitted then s else Id.run do
  let mut s := s
  let v := viewAt s number
  if count v .candidate arg ≥ 2 * c.faults + 1 && !v.sentReadyCore.contains arg then
    s := putView s { v with sentReadyCore := v.sentReadyCore ++ [arg] }
    s := broadcast s number .ready arg
  let v := viewAt s number
  if count v .ready arg ≥ c.faults + 1 && !v.sentReadyRelay.contains arg then
    s := putView s { v with sentReadyRelay := v.sentReadyRelay ++ [arg] }
    s := broadcast s number .ready arg
  let v := viewAt s number
  if count v .ready arg ≥ 2 * c.faults + 1 then s := clear s number arg
  return s
def progressView (c : Config) (s : State) (number : Nat) : State := Id.run do
  let v := viewAt s number
  let values := (valuesFor v .vote ++ valuesFor v .commit).filterMap id |>.eraseDups
  let mut s := values.foldl (fun state b => valueRules c state number b) s
  let v := viewAt s number
  let args := (valuesFor v .candidate ++ valuesFor v .ready).eraseDups
  s := args.foldl (fun state a => argumentRules c state number a) s
  return s
def preparedAt (s : State) (view : Nat) : List Block :=
  if view == 0 then [[]] else (viewAt s view).prepared
def disabledAt (s : State) (view : Nat) : Bool :=
  if view == 0 then false else (viewAt s view).disabled
/-- The views a parent may come from: the floor and every view above it below `current`. -/
def parentViews (s : State) : List Nat :=
  (List.range (s.current - s.lastCommitted)).map (s.lastCommitted + ·)
def isSafe (s : State) (block : Block) : Bool :=
  !block.isEmpty && (parentViews s).any fun old =>
    (preparedAt s old).contains block.dropLast &&
    (List.range (s.current - (old + 1))).all (fun offset => disabledAt s (old + 1 + offset))
def bestParent (s : State) : Block :=
  ((parentViews s).reverse.findSome? fun old => (preparedAt s old).head?).getD []
def castVote (s : State) (number : Nat) (block : Block) : State :=
  let v := viewAt s number
  if v.voted || v.disableRequested then s else
  broadcast (putView s { v with voted := true }) number .vote (some block)
/-- The view of `bestParent`: the highest view below `current` with a prepared
block (the floor, if none above it). -/
def bestParentView (s : State) : Nat :=
  ((parentViews s).reverse.find? fun old => !(preparedAt s old).isEmpty).getD s.lastCommitted
/-- A leader has work when a checked offer extends the best parent, or when the
best parent is prepared at least two views back (the view after it ended
without a block) and is still not locally committed: an empty extension then
lets a later view commit it. A parent prepared in the immediately preceding
view is normally committed by that view's own COMMITs, so it is not work. -/
def hasWork (s : State) : Bool :=
  let parent := bestParent s
  s.offers.any (fun bytes => validBlock s (parent ++ [bytes])) ||
    (bestParentView s + 1 < s.current && !isPrefix parent s.committedTip)
/-- Quiescent proposal: with no work the leader proposes nothing and its view
ends by CANDIDATE(⊥). An idle domain therefore adds no blocks. -/
def propose (s : State) : State :=
  if !hasWork s then s else
  let parent := bestParent s
  let payload := (s.offers.find? (fun bytes => validBlock s (parent ++ [bytes]))).getD []
  let block := parent ++ [payload]
  if validBlock s block then
    let s := broadcast s s.current .propose (some block)
    let v := viewAt s s.current
    if v.proposal.isNone then putView s { v with proposal := some block } else s
  else { s with failed := true }
/-- The highest view this replica has locally committed (0 if none): the specification of
the maintained field `State.lastCommitted`. -/
def lastCommittedView (s : State) : Nat :=
  s.views.foldl (fun acc v => if v.committed.isSome then max acc v.number else acc) 0
/-- View timer: `timeout · 2^min(k, backoffCap)` where `k` counts the views
after the last local commit. An underestimated Delta is outgrown after
finitely many views instead of failing every view forever. -/
def viewTimeout (c : Config) (s : State) (number : Nat) : Nat :=
  c.timeout * 2 ^ min (number - (s.lastCommitted + 1)) c.backoffCap
def enterView (c : Config) (s : State) (number : Nat) : State :=
  let s := { s with current := number, deadline := s.now + viewTimeout c s number }
  let s := putView s (viewAt s number)
  if c.leader number == s.self then propose s else s
def progressOuter (c : Config) (s : State) : State := Id.run do
  let mut s := s
  -- Late proposal: work (an offer) can arrive after the leader entered its
  -- view. It proposes at most once per view (the recorded proposal guards it)
  -- and never after requesting the view's disable.
  let v := viewAt s s.current
  if c.leader s.current == s.self && v.proposal.isNone && !v.disableRequested then
    s := propose s
  let v := viewAt s s.current
  if !v.voted && !v.disableRequested then
    if let some block := v.proposal then
      if validBlock s block && isSafe s block then s := castVote s s.current block
  let v := viewAt s s.current
  if !v.prepared.isEmpty || v.disabled then
    if !v.voted && !v.disableRequested then
      if let some block := v.prepared.head? then s := castVote s s.current block
    s := enterView c s (s.current + 1)
  return s
/-- Commit-floor catch-up: a replica at or below its floor enters the view after it.
Everything it skips is at or below a view it has committed, so no vote it could still
cast there is pending. The entered view runs on the base timer (`viewTimeout`). -/
def floorJump (c : Config) (s : State) : State :=
  if s.current ≤ s.lastCommitted then enterView c s (s.lastCommitted + 1) else s
/-- Every view above the floor remains active. Fair poll slices preserve pending work. The
floor jump runs before the outer rules, so they act in a view above the floor. -/
def pass (c : Config) (s : State) : State :=
  let numbers := s.views.filterMap fun v => if s.lastCommitted < v.number then some v.number else none
  progressOuter c (floorJump c
    (numbers.foldl (fun state number => progressView c state number) s))
/-- What a running replica keeps: the floor view and the views above it. Every view below
the floor, and the audit, are history no rule reads (`GenericSimplexErasure`). -/
def forget (s : State) : State :=
  { s with views := s.views.filter (fun v => s.lastCommitted ≤ v.number), audit := [] }
/-- Passes repeat until one changes nothing a running replica keeps. -/
def pump (c : Config) : Nat → State → State
  | 0, s => { s with needsPoll := true }
  | fuel + 1, s =>
      let s := { s with needsPoll := false }
      let next := pass c s
      if forget next == forget s then next else pump c fuel next

deriving instance ReflBEq for Kind, Message, View, AuditEvent, State

/-- Executable `pump`. A pass that changes nothing returns the very object it was
given, and the whole-state `==` that detects that fixpoint walks every retained
view, message and block byte, on every input (on the four-source
evidence copy this dominated both a replica's per-input cost and its reopen
replay). `withPtrEq` answers that case by pointer equality first; it is
logically `forget next == forget s` (`withPtrEq a b k h = k ()`), so `pump` stays the
definition every proof reads. -/
def pumpFast (c : Config) : Nat → State → State
  | 0, s => { s with needsPoll := true }
  | fuel + 1, s =>
      let s := { s with needsPoll := false }
      let next := pass c s
      if withPtrEq next s (fun _ => forget next == forget s) (fun same => by simp only [same, beq_self_eq_true])
      then next else pumpFast c fuel next

@[csimp] theorem pump_eq_pumpFast : @pump = @pumpFast := by
  funext c fuel s
  induction fuel generalizing s with
  | zero => rfl
  | succ fuel ih =>
    show pump c (fuel + 1) s = pumpFast c (fuel + 1) s
    rw [pump, pumpFast]
    simp only [withPtrEq, ih]
    rfl
inductive Input where
  | delivery (message : Message)
  | tick (now : Nat)
  | deliveryAt (now : Nat) (message : Message)
  | checked (block : Block)
  | offer (payload : Bytes)
  | poll
  deriving DecidableEq, BEq, Repr, Inhabited
/-- A peer that asks to leave a view at or below the floor (CANDIDATE(⊥): what a replica
sends on timeout and repeats while stuck) is owed the floor's COMMIT evidence, once per peer
per floor. -/
def serveFloor (s : State) (peer : Nat) : State :=
  if peer == s.self || s.served.contains peer || s.floorEvidence.isEmpty then s else
  { s with relay := s.relay ++ s.floorEvidence.map (fun m => (peer, m)),
           served := s.served ++ [peer] }
/-- A payload already in the committed tip is not work and is not offered again. -/
def addOffer (s : State) (payload : Bytes) : List Bytes :=
  if s.committedTip.contains payload then s.offers else addUnique s.offers payload
def ingest (c : Config) (s : State) (m : Message) : State :=
  if m.sender ≥ c.parties || m.view == 0 then s else
  if m.view ≤ s.lastCommitted then
    if m.kind == .candidate && m.value.isNone then serveFloor s m.sender else s
  else
  if (m.kind == .propose || m.kind == .vote || m.kind == .commit) && m.value.isNone then s else
  if m.kind == .propose then
    if m.sender != c.leader m.view then s else
    let v := viewAt s m.view
    if v.proposal.isSome then s else
    putView s { v with proposal := m.value }
  else register s m
def step (c : Config) (s : State) (input : Input) : State :=
  if !c.wellFormed || s.self ≥ c.parties || s.failed then { s with failed := true } else
  let next := match input with
    | .delivery m => ingest c s m
    | .deliveryAt now m => ingest c {s with now := max s.now now} m
    | .checked block =>
        -- Register eligibility and offer atomically, before any leader action.
        -- A separate offer append could otherwise miss the just-enabled view.
        let offers := match block.getLast? with
          | some payload => if payload.isEmpty then s.offers else addOffer s payload
          | none => s.offers
        { s with checked := addChecked s.checked block, offers := offers }
    | .offer payload => { s with offers := addOffer s payload }
    | .poll => s
    | .tick now =>
        -- Due authenticated arrivals must be delivered before this input.
        -- Drain already enabled local actions before a same-time timeout.
        let s := pump c c.pumpBudget s
        let s := { s with now := max s.now now }
        if !s.needsPoll && s.now ≥ s.deadline then
          let s := { s with deadline := s.now + viewTimeout c s s.current }
          let v := viewAt s s.current
          if !v.disableRequested then
            sendCandidate (putView s { v with disableRequested := true }) s.current none
          else if v.sentCandidates.contains none then
            -- Still in the view a whole timeout after asking to leave it: ask again. A peer
            -- whose floor has passed the view answers with its floor evidence (`serveFloor`).
            { s with outbox := s.outbox ++ [⟨s.self, s.current, .candidate, none⟩] }
          else s
        else s
  pump c c.pumpBudget next
def start (c : Config) (self now : Nat) (offers : List Bytes := [])
    (checked : List Block := []) : State :=
  if !c.wellFormed || self ≥ c.parties then
    { self := self, now := now, deadline := now, failed := true }
  else
    pump c c.pumpBudget (enterView c
      { self := self, now := now, deadline := now + c.timeout,
        offers := offers, checked := checked } 1)
/-- The physical driver persists messages before draining this ephemeral queue. -/
def drainOutbox (s : State) : List Message × State := (s.outbox, { s with outbox := [] })
def drainRelay (s : State) : List (Nat × Message) × State := (s.relay, { s with relay := [] })
/-- The executable transition: `step`, then forget. -/
def liveStep (c : Config) (s : State) (input : Input) : State := forget (step c s input)
@[simp] theorem empty_block_valid (s : State) : validBlock s [] = true := by
  simp [validBlock, applicationHistory]
theorem applicationHistory_preserves_prefix {a b : Block} (hprefix : a.IsPrefix b) :
    (applicationHistory a).IsPrefix (applicationHistory b) := by
  obtain ⟨suffix,rfl⟩ := hprefix
  simp [applicationHistory]

theorem validBlock_same_application_history (s : State) (a b : Block)
    (same : applicationHistory a = applicationHistory b) :
    validBlock s a = validBlock s b := by
  simp only [validBlock, same]
theorem validBlock_append_inert (s : State) (block : Block) :
    validBlock s (block ++ [[]]) = validBlock s block := by
  apply validBlock_same_application_history
  simp [applicationHistory]
theorem disabled_cannot_cast_vote (s : State) (view : Nat) (block : Block)
    (disabled : (viewAt s view).disableRequested = true) : castVote s view block = s := by
  simp [castVote, disabled]
theorem voted_cannot_cast_again (s : State) (view : Nat) (block : Block)
    (voted : (viewAt s view).voted = true) : castVote s view block = s := by
  simp [castVote, voted]
end Minidregg.Kernel.GenericSimplex
