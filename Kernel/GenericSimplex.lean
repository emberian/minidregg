/- Complete executable Generic Simplex, arXiv:2609.32985v1 Figures 1,3,4,5.
Fixed static n=3f+1 committee, authenticated reliable delivery, known delay bound
after unknown GST. Past views remain active. Exact block ancestry replaces hashes.
Source checking is an INTERNAL controller input, never a network packet. -/
import Std
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

/-- Check every exact application-bearing source prefix. A check remains valid
when protocol-only empty blocks are inserted, since those neither modify source
state nor consume a source height. A different nonempty ancestor never matches.
The native checker replays this same canonical source history from pinned genesis. -/
def validBlock (s : State) (block : Block) : Bool :=
  let history := applicationHistory block
  (List.range history.length).all fun i =>
    s.checked.any (fun checked => applicationHistory checked == history.take (i + 1))
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
def isPrefix (a b : Block) : Bool := b.take a.length == a
def doCommit (s : State) (number : Nat) (block : Block) : State :=
  if !validBlock s block then s else
  let s := clear s number (some block)
  let v := viewAt s number
  if v.committed.isSome then s else
  let s := putView s { v with committed := some block }
  let s := { s with audit := s.audit ++ [.commit s.self number block] }
  if isPrefix s.committedTip block then
    if s.committedTip == block then s else
      { s with committedTip := block, delivered := s.delivered ++ [block] }
  else if isPrefix block s.committedTip then s
  else { s with failed := true }
def sendCandidate (s : State) (number : Nat) (arg : Argument) : State :=
  let v := viewAt s number
  if v.sentCandidates.contains arg ||
      (v.sentCommit.isSome && v.sentCommit != arg) then s else
  let s := putView s { v with sentCandidates := v.sentCandidates ++ [arg] }
  broadcast s number .candidate arg
def valueRules (c : Config) (s : State) (number : Nat) (block : Block) : State := Id.run do
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
  if count v .commit arg ≥ c.quorum then s := doCommit s number block
  let v := viewAt s number
  if count v .vote arg ≥ c.faults + 1 && validBlock s block then
    s := sendCandidate s number arg
  return s
def argumentRules (c : Config) (s : State) (number : Nat) (arg : Argument) : State := Id.run do
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
def isSafe (s : State) (block : Block) : Bool :=
  !block.isEmpty && (List.range s.current).any fun old =>
    (preparedAt s old).contains block.dropLast &&
    (List.range (s.current - (old + 1))).all (fun offset => disabledAt s (old + 1 + offset))
def bestParent (s : State) : Block :=
  ((List.range s.current).reverse.findSome? fun old => (preparedAt s old).head?).getD []
def castVote (s : State) (number : Nat) (block : Block) : State :=
  let v := viewAt s number
  if v.voted || v.disableRequested then s else
  broadcast (putView s { v with voted := true }) number .vote (some block)
def propose (s : State) : State :=
  let parent := bestParent s
  let payload := (s.offers.find? (fun bytes => validBlock s (parent ++ [bytes]))).getD []
  let block := parent ++ [payload]
  if validBlock s block then
    let s := broadcast s s.current .propose (some block)
    let v := viewAt s s.current
    if v.proposal.isNone then putView s { v with proposal := some block } else s
  else { s with failed := true }
def enterView (c : Config) (s : State) (number : Nat) : State :=
  let s := { s with current := number, deadline := s.now + c.timeout }
  let s := putView s (viewAt s number)
  if c.leader number == s.self then propose s else s
def progressOuter (c : Config) (s : State) : State := Id.run do
  let mut s := s
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
/-- Every known view remains active. Fair poll slices preserve pending work. -/
def pass (c : Config) (s : State) : State :=
  let numbers := (s.views.map View.number).eraseDups
  progressOuter c (numbers.foldl (fun state number => progressView c state number) s)
def pump (c : Config) : Nat → State → State
  | 0, s => { s with needsPoll := true }
  | fuel + 1, s =>
      let s := { s with needsPoll := false }
      let next := pass c s
      if next == s then next else pump c fuel next
inductive Input where
  | delivery (message : Message)
  | tick (now : Nat)
  | deliveryAt (now : Nat) (message : Message)
  | checked (block : Block)
  | offer (payload : Bytes)
  | poll
  deriving DecidableEq, BEq, Repr, Inhabited
def ingest (c : Config) (s : State) (m : Message) : State :=
  if m.sender ≥ c.parties || m.view == 0 then s else
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
          | some payload => if payload.isEmpty then s.offers else addUnique s.offers payload
          | none => s.offers
        { s with checked := addUnique s.checked block, offers := offers }
    | .offer payload => { s with offers := addUnique s.offers payload }
    | .poll => s
    | .tick now =>
        -- Due authenticated arrivals must be delivered before this input.
        -- Drain already enabled local actions before a same-time timeout.
        let s := pump c c.pumpBudget s
        let s := { s with now := max s.now now }
        let v := viewAt s s.current
        if !s.needsPoll && s.now ≥ s.deadline && !v.disableRequested then
          sendCandidate (putView s { v with disableRequested := true }) s.current none
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
