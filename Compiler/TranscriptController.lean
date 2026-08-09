/-
# Compiler.TranscriptController -- Lean-owned proof transcript control

This module isolates the control plane which must not be delegated to a native
prover or verifier kernel.  `Command` is a first-order, intrinsically typed
schedule language.  Its typestate has three security-critical consequences:

* public context and commitments are absorbed before the first challenge;
* a canonical native reply is absorbed before the next challenge;
* query randomness is unavailable until both the terminal value and terminal
  commitment root have been absorbed.

Challenge values are deliberately absent from the syntax and from
`CanonicalData`.  The only constructor of an execution-time challenge record
is `deriveAs`, which calls the Lean-owned `XofPortal`.  Native code contributes
canonical messages, roots, and openings only.  Final acceptance is likewise a
Lean predicate over the completed controller state, never a native return bit.
-/

import Mathlib.Tactic

namespace Minidregg.Compiler.TranscriptController

universe u v w

/-! ## First-order boundary data -/

/-- Data returned across the native boundary, accompanied by its canonical
encoding/representation proof.  There is intentionally no challenge or
acceptance field. -/
structure CanonicalData (Blob : Type u) (Canonical : Blob → Prop) where
  value : Blob
  isCanonical : Canonical value

/-- Domain-separated transcript frames.  Proofs of canonicality are checked
at the boundary and erased from the bytes absorbed by the portal. -/
inductive Frame (Blob : Type u) where
  | publicContext (context : Blob)
  | commitments (roots : List Blob)
  | roundReply (remaining : Nat) (reply : Blob)
  | terminalValue (value : Blob)
  | terminalRoot (root : Blob)
  | openings (values : List Blob)
deriving Repr

/-- The two kinds of randomness owned by this controller.  `remaining`
domain-separates each decreasing round number. -/
inductive DrawLabel where
  | roundChallenge (remaining : Nat)
  | querySeed
deriving DecidableEq, Repr

/-! ## Intrinsically ordered schedule syntax -/

/-- Transcript phases.  States `awaitingReply (n+1)` and
`replyAbsorbed (n+1)` are the live round states; no command enters a live state
with zero remaining rounds. -/
inductive Phase where
  | start
  | publicAbsorbed
  | commitmentsAbsorbed
  | awaitingReply (remaining : Nat)
  | replyAbsorbed (remaining : Nat)
  | awaitingTerminal
  | terminalAbsorbed
  | terminalRootAbsorbed
  | awaitingOpenings
  | complete
deriving DecidableEq, Repr

/-- One first-order schedule instruction.  The indices encode all legal phase
transitions.  In particular, challenge instructions carry a round count but no
challenge value. -/
inductive Command (Blob : Type u) (Canonical : Blob → Prop) :
    Phase → Phase → Type (max u 1) where
  | absorbPublic (context : Blob) :
      Command Blob Canonical .start .publicAbsorbed
  | absorbCommitments (roots : List Blob) :
      Command Blob Canonical .publicAbsorbed .commitmentsAbsorbed
  | firstChallenge (n : Nat) :
      Command Blob Canonical .commitmentsAbsorbed (.awaitingReply (n + 1))
  | absorbReply (n : Nat) (reply : CanonicalData Blob Canonical) :
      Command Blob Canonical (.awaitingReply (n + 1)) (.replyAbsorbed (n + 1))
  | nextChallenge (n : Nat) :
      Command Blob Canonical (.replyAbsorbed (n + 2)) (.awaitingReply (n + 1))
  | roundsDone :
      Command Blob Canonical (.replyAbsorbed 1) .awaitingTerminal
  | absorbTerminal (terminal : CanonicalData Blob Canonical) :
      Command Blob Canonical .awaitingTerminal .terminalAbsorbed
  | absorbTerminalRoot (root : CanonicalData Blob Canonical) :
      Command Blob Canonical .terminalAbsorbed .terminalRootAbsorbed
  | deriveQueries :
      Command Blob Canonical .terminalRootAbsorbed .awaitingOpenings
  | absorbOpenings (openings : List (CanonicalData Blob Canonical)) :
      Command Blob Canonical .awaitingOpenings .complete

/-- A first-order typed AST made by sequencing commands.  There are no
continuation functions or native callbacks in this syntax. -/
inductive Schedule (Blob : Type u) (Canonical : Blob → Prop) :
    Phase → Phase → Type (max u 1) where
  | done : Schedule Blob Canonical p p
  | step (command : Command Blob Canonical p q)
      (rest : Schedule Blob Canonical q r) : Schedule Blob Canonical p r

/-- The statically declared draw labels of a command. -/
def Command.drawLabels {Blob : Type u} {Canonical : Blob → Prop} :
    {p q : Phase} → Command Blob Canonical p q → List DrawLabel
  | _, _, .firstChallenge n => [.roundChallenge (n + 1)]
  | _, _, .nextChallenge n => [.roundChallenge (n + 1)]
  | _, _, .deriveQueries => [.querySeed]
  | _, _, _ => []

/-- The statically declared draw order of a schedule. -/
def Schedule.drawLabels {Blob : Type u} {Canonical : Blob → Prop} :
    {p q : Phase} → Schedule Blob Canonical p q → List DrawLabel
  | _, _, .done => []
  | _, _, .step command rest => command.drawLabels ++ rest.drawLabels

/-! ## The Lean-owned hash/XOF portal -/

/-- Abstract hash/XOF portal.  A concrete implementation may cross into a
small hash kernel for compression, but `squeeze` is invoked only by this Lean
controller.  `squeeze_xof_law` is the named semantic law connecting the
executable portal to its XOF specification. -/
structure XofPortal (Blob : Type u) (State : Type v) (Coin : Type w) where
  absorb : State → Frame Blob → State
  squeeze : State → DrawLabel → Coin × State
  xof : State → DrawLabel → Coin
  squeeze_xof_law : ∀ state label,
    (squeeze state label).1 = xof state label

/-- Every recorded coin carries its exact pre-squeeze state and the portal law
which derived it.  A native reply cannot construct one through `Command`. -/
structure DerivedDraw {Blob : Type u} {State : Type v} {Coin : Type w}
    (portal : XofPortal Blob State Coin) where
  preState : State
  label : DrawLabel
  coin : Coin
  portalLaw : coin = portal.xof preState label

/-- Controller state indexed by the phase reached by the schedule. -/
structure ControllerState {Blob : Type u} {State : Type v} {Coin : Type w}
    (portal : XofPortal Blob State Coin) (phase : Phase) where
  sponge : State
  absorbed : List (Frame Blob)
  draws : List (DerivedDraw portal)

private def absorbAs {Blob : Type u} {State : Type v} {Coin : Type w}
    (portal : XofPortal Blob State Coin) {p q : Phase}
    (frame : Frame Blob) (state : ControllerState portal p) :
    ControllerState portal q :=
  { sponge := portal.absorb state.sponge frame
    absorbed := state.absorbed ++ [frame]
    draws := state.draws }

/-- The sole execution path which mints a challenge record. -/
private def deriveAs {Blob : Type u} {State : Type v} {Coin : Type w}
    (portal : XofPortal Blob State Coin) {p q : Phase}
    (label : DrawLabel) (state : ControllerState portal p) :
    ControllerState portal q :=
  let result := portal.squeeze state.sponge label
  let draw : DerivedDraw portal :=
    { preState := state.sponge
      label := label
      coin := result.1
      portalLaw := portal.squeeze_xof_law state.sponge label }
  { sponge := result.2
    absorbed := state.absorbed
    draws := state.draws ++ [draw] }

/-- Execute one typed controller command. -/
def runCommand {Blob : Type u} {State : Type v} {Coin : Type w}
    {Canonical : Blob → Prop} (portal : XofPortal Blob State Coin)
    {p q : Phase} (command : Command Blob Canonical p q)
    (state : ControllerState portal p) : ControllerState portal q :=
  match command with
  | .absorbPublic context =>
      absorbAs portal (.publicContext context) state
  | .absorbCommitments roots =>
      absorbAs portal (.commitments roots) state
  | .firstChallenge n =>
      deriveAs portal (.roundChallenge (n + 1)) state
  | .absorbReply n reply =>
      absorbAs portal (.roundReply (n + 1) reply.value) state
  | .nextChallenge n =>
      deriveAs portal (.roundChallenge (n + 1)) state
  | .roundsDone =>
      { sponge := state.sponge
        absorbed := state.absorbed
        draws := state.draws }
  | .absorbTerminal terminal =>
      absorbAs portal (.terminalValue terminal.value) state
  | .absorbTerminalRoot root =>
      absorbAs portal (.terminalRoot root.value) state
  | .deriveQueries =>
      deriveAs portal .querySeed state
  | .absorbOpenings openings =>
      absorbAs portal (.openings (openings.map CanonicalData.value)) state

/-- Execute a complete typed schedule. -/
def run {Blob : Type u} {State : Type v} {Coin : Type w}
    {Canonical : Blob → Prop} (portal : XofPortal Blob State Coin) :
    {p q : Phase} → Schedule Blob Canonical p q →
      ControllerState portal p → ControllerState portal q
  | _, _, .done, state => state
  | _, _, .step command rest, state =>
      run portal rest (runCommand portal command state)

/-- The unique empty controller state. -/
def initial {Blob : Type u} {State : Type v} {Coin : Type w}
    (portal : XofPortal Blob State Coin) (seed : State) :
    ControllerState portal .start :=
  { sponge := seed, absorbed := [], draws := [] }

/-- Execute a schedule from an empty transcript log. -/
def execute {Blob : Type u} {State : Type v} {Coin : Type w}
    {Canonical : Blob → Prop} (portal : XofPortal Blob State Coin)
    (schedule : Schedule Blob Canonical .start q) (seed : State) :
    ControllerState portal q :=
  run portal schedule (initial portal seed)

/-! ## Control-plane theorems -/

@[simp] theorem runCommand_drawLabels {Blob : Type u} {State : Type v}
    {Coin : Type w} {Canonical : Blob → Prop}
    (portal : XofPortal Blob State Coin) {p q : Phase}
    (command : Command Blob Canonical p q)
    (state : ControllerState portal p) :
    (runCommand portal command state).draws.map DerivedDraw.label =
      state.draws.map DerivedDraw.label ++ command.drawLabels := by
  cases command <;>
    simp [runCommand, absorbAs, deriveAs, Command.drawLabels]

/-- Execution preserves exactly the statically typed draw order.  Thus an
executor cannot insert, omit, or reorder a challenge relative to the AST. -/
theorem run_drawLabels {Blob : Type u} {State : Type v} {Coin : Type w}
    {Canonical : Blob → Prop} (portal : XofPortal Blob State Coin)
    {p q : Phase} (schedule : Schedule Blob Canonical p q)
    (state : ControllerState portal p) :
    (run portal schedule state).draws.map DerivedDraw.label =
      state.draws.map DerivedDraw.label ++ schedule.drawLabels := by
  induction schedule with
  | done => simp [run, Schedule.drawLabels]
  | step command rest ih =>
      rw [run, ih, runCommand_drawLabels]
      simp only [Schedule.drawLabels, List.append_assoc]

/-- From an empty log, the execution draw order is exactly the schedule draw
order. -/
theorem execute_drawLabels {Blob : Type u} {State : Type v} {Coin : Type w}
    {Canonical : Blob → Prop} (portal : XofPortal Blob State Coin)
    (schedule : Schedule Blob Canonical .start q) (seed : State) :
    (execute portal schedule seed).draws.map DerivedDraw.label =
      schedule.drawLabels := by
  simpa [execute, initial] using
    run_drawLabels portal schedule (initial portal seed)

/-- **No supplied challenges.** Every challenge in every execution is equal
to the XOF applied to its recorded Lean transcript prefix and domain label.
The native packets do not occur on the right-hand side. -/
theorem execution_draw_portal_law {Blob : Type u} {State : Type v}
    {Coin : Type w} {Canonical : Blob → Prop}
    (portal : XofPortal Blob State Coin)
    (schedule : Schedule Blob Canonical .start q) (seed : State)
    (draw : DerivedDraw portal)
    (_member : draw ∈ (execute portal schedule seed).draws) :
    draw.coin = portal.xof draw.preState draw.label :=
  draw.portalLaw

/-! ## Concrete two-round schedule -/

/-- A small, generic two-round schedule.  The constructor sequence itself is
the protocol: public data, roots, challenge, reply, challenge, reply, terminal,
terminal root, query seed, and openings. -/
def twoRoundSchedule {Blob : Type u} {Canonical : Blob → Prop}
    (context : Blob) (roots : List Blob)
    (firstReply secondReply terminal terminalRoot : CanonicalData Blob Canonical)
    (openings : List (CanonicalData Blob Canonical)) :
    Schedule Blob Canonical .start .complete :=
  .step (.absorbPublic context) <|
  .step (.absorbCommitments roots) <|
  .step (.firstChallenge 1) <|
  .step (.absorbReply 1 firstReply) <|
  .step (.nextChallenge 0) <|
  .step (.absorbReply 0 secondReply) <|
  .step .roundsDone <|
  .step (.absorbTerminal terminal) <|
  .step (.absorbTerminalRoot terminalRoot) <|
  .step .deriveQueries <|
  .step (.absorbOpenings openings) .done

/-- The concrete witness has exactly two ordered round challenges, followed by
the query draw which is structurally after the terminal root. -/
theorem twoRound_draw_order {Blob : Type u} {State : Type v} {Coin : Type w}
    {Canonical : Blob → Prop} (portal : XofPortal Blob State Coin)
    (context : Blob) (roots : List Blob)
    (firstReply secondReply terminal terminalRoot : CanonicalData Blob Canonical)
    (openings : List (CanonicalData Blob Canonical)) (seed : State) :
    (execute portal
      (twoRoundSchedule context roots firstReply secondReply terminal terminalRoot openings)
      seed).draws.map DerivedDraw.label =
      [.roundChallenge 2, .roundChallenge 1, .querySeed] := by
  rw [execute_drawLabels]
  rfl

/-! ## Lean-owned final acceptance -/

/-- Final acceptance is a Lean checker over completed transcript state.  The
only Boolean in this interface is the result of `leanCheck`; no native command
or `CanonicalData` supplies one. -/
def accept {Blob : Type u} {State : Type v} {Coin : Type w}
    (portal : XofPortal Blob State Coin)
    (leanCheck : ControllerState portal .complete → Bool)
    (state : ControllerState portal .complete) : Bool :=
  leanCheck state

/-- **No native acceptance bit.** The controller's final decision is exactly
the Lean check applied to the completed, transcript-bound state. -/
@[simp] theorem acceptance_is_lean_owned {Blob : Type u} {State : Type v}
    {Coin : Type w} (portal : XofPortal Blob State Coin)
    (leanCheck : ControllerState portal .complete → Bool)
    (state : ControllerState portal .complete) :
    accept portal leanCheck state = leanCheck state :=
  rfl

end Minidregg.Compiler.TranscriptController
