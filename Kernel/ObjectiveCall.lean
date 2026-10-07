/- Synchronous cross-object `call` (OB7): a signed invocation runs a method of
an object's pinned package, and that method may call methods of other objects
in the same turn, depth-first, each callee on its own pinned package.

**What a method is.** A declaration of the entry module of the package an object
pins (`ObjectRecord.pin`, the published pair of `Kernel.ObjectiveActivity`),
lowered by the kernel's own front end with that declaration selected
(`loadMethod`: the pinned sources, replayed, never an offered core). Its type is

    method(view: {version: Nat, state: S}, args: X) -> Activity<P, R, {result: A, write: W}>

where the Plan type `P` has labels among `call | send` and the response type `R`
among `returned | queued`. A method can therefore yield nothing but a call or a
send, each answered in the same turn: no frame ever suspends across turns (the
design's "an Activity cannot be called", stated as a type rule the loader checks
before anything runs: `notCallable`). A method that never calls is a pure
function whose body is its `{result, write}` record.

**The frame.** Entering a call (`exec`, task `enter`):
* RE-ENTRY IS REFUSED: a call whose target is already on the stack is refused
  `reentry`, naming the target and the stack (`reentry_refused`). Mandatory: no
  configuration turns it off.
* the stack is at most `callDepth` deep (`depth`);
* the callee must be an object (`notAnObject`) with declared state (`stateMissing`);
* the callee is shown a VIEW of its declared state as the turn's journal holds
  it: the snapshot, plus every write an earlier frame of this turn already
  applied at its return;
* the callee's authority (`Facts`): the root frame carries the signer's subject;
  a nested frame carries it ONLY if a scoped grant of the invocation names
  (callee, method), and each such frame spends one use of the grant
  (`grantSpent` when its uses are gone). Without a grant the subject slot is
  absent and every law atom reading it fails closed: the signer's authority does
  not flow to callees it did not grant (Daml's non-transitive delegation; Pact's
  scoped, counted capabilities). `request/caller` names the calling object, so
  a callee's law can admit chosen callers (an object's facet, as a clause).

**Upgrades.** A frame enters an object only while it admits new frames
(`ObjectRecord.admitsNew`: steady, or draining under the identity migration,
else `draining`); it runs the package the object runs for new frames
(`activePin`); and its write is judged by `ObjectRecord.judge`: the object's law,
and while draining, the next record's judgment of the new state under the
migration's facts, so a draining object's state stays one MIGRATE admits.

**Writes are applied at frame return** (the root's ruling on OPEN 1): the
returned `write` (per field: keep, set or add, `ObjectiveActivity.applyWrite`) is
applied to the frame's own object only, judged THEN by that object's law on
(the state the frame was shown, the new state) under the frame's own facts, and
a refusal names the object, the method and the failing clause (`lawDenied`).
Because a frame writes only its own object and re-entry is refused, nothing
writes an object while its frame is on the stack, so every write is computed
from exactly the state its frame was shown (`exec_writes_from_view`): a callee
never sees a caller's pending write and no write is lost. That answers the
design's Scribe note D4: under apply-at-return with own-object writes, the
frame-conflict abort has nothing left to catch, and two sequential calls to one
object (`A` calls `B.deposit` twice) compose in order.

**One envelope.** The whole call tree runs within the invocation's declared
source ticks (`runCounted`, proven equal to the machine's own `runBounded`,
`runCounted_outcome`); the invocation pays the public tariff of its declared
envelope (`ObjectiveTariff`), never a measured amount. Exhaustion refuses the
invocation: nothing commits, nothing is charged.

**Sends (OB8).** A frame may also yield `send {to, method, args}`: an
asynchronous message to an object's inbox (`to: object n`) or to the reply of
an earlier send not yet delivered (`to: slot n`, pipelined: queued on that reply
slot and forwarded by the turn that decides it, `Kernel.ObjectiveSend`). A send
is answered in the same turn with `queued {slot}`, the message's id
(`Inbox.sendId`: this turn's transaction and the send's index), which is also
the name of its reply slot. A frame's Plan type therefore has labels among
`call | send` and its response type among `returned | queued`. The turn's sends
(`Journal.outbox`, in order) become its MAIL (`postMail`): each message is
pushed onto the per-(sender, target) inbox, bounded at `Inbox.bound` (a full
queue refuses the turn by name, `queueFull`), with its reply slot opened (decided
only by the message's delivery, `AnswerSlot.Decider.delivery`), and its postage
(the public price of the invocation's declared `postage` envelope, the envelope
its delivery runs under) moved from the invocation's account into the purse of
the queue holding it. Every inbox and slot the mail writes is a cell the turn
read: its post is a lawful change (`Inbox.Lawful`) of what the cell held.

**The turn** (`invoke`) commits every written object's state cell, its mail and
the fee and escrow postings, as ONE intent, guarded on every object record,
package cell and state cell it read, so a concurrent change refuses it. -/
import Kernel.ObjectiveActivity

namespace Minidregg.Kernel.ObjectiveCall
open Minidregg.Theory Minidregg.Compiler
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Theory.TypedAuthorization (Digest SubjectId)
open Minidregg.Kernel.DurableDataIntent
open Minidregg.Kernel.ObjectiveActivityWire
open Minidregg.Theory.ObjectiveBendTypes (Ty Bounds)
open Minidregg.Theory.ObjectiveBendTyping
open Minidregg.Theory.ObjectiveBendDemandMachine (State Limits Outcome Suspension initial runBounded resume step)
open Minidregg.Theory.ObjectiveBendDemandData (Data)
open Minidregg.Kernel.ObjectRecord (ObjectRecord Facts WriteRefusal admitWrite)
open Minidregg.Kernel.ObjectiveActivity
open Minidregg.Compiler.ObjectiveInvocationClaim (Capacity)
open Minidregg.Theory.CanonicalResourceKernel (Book Batch Operation AccountId AssetId logicalBook)
set_option autoImplicit false

/-! ## Counting ticks across frames -/

/-- `runBounded` that also reports the ticks it left unused. -/
def runCounted (limits : Limits) : Nat → State → Outcome × Nat
  | 0, state => (runBounded limits 0 state, 0)
  | ticks + 1, state =>
    match step limits state with
    | .suspended .ticks next => runCounted limits ticks next
    | other => (other, ticks)

/-- **The counted run IS the machine's run**: the outcome is `runBounded`'s. -/
theorem runCounted_outcome (limits : Limits) : ∀ (ticks : Nat) (state : State),
    (runCounted limits ticks state).1 = runBounded limits ticks state
  | 0, _ => rfl
  | ticks + 1, state => by
    unfold runCounted runBounded
    cases stepped : step limits state with
    | suspended reason next =>
      cases reason with
      | ticks => exact runCounted_outcome limits ticks next
      | capacity => rfl
    | finished _ _ => rfl
    | divergent _ _ => rfl
    | refused _ _ => rfl
    | yielded _ _ => rfl

/-- A run never leaves more ticks than it was given. -/
theorem runCounted_left_le (limits : Limits) : ∀ (ticks : Nat) (state : State),
    (runCounted limits ticks state).2 ≤ ticks
  | 0, _ => Nat.le_refl 0
  | ticks + 1, state => by
    unfold runCounted
    cases stepped : step limits state with
    | suspended reason next =>
      cases reason with
      | ticks => exact Nat.le_succ_of_le (runCounted_left_le limits ticks next)
      | capacity => exact Nat.le_succ ticks
    | finished _ _ => exact Nat.le_succ ticks
    | divergent _ _ => exact Nat.le_succ ticks
    | refused _ _ => exact Nat.le_succ ticks
    | yielded _ _ => exact Nat.le_succ ticks

/-! ## Refusals -/

inductive CallRefusal where
  /-- A refusal of the object kernel (package, state, write shape, Book, ...). -/
  | kernel (reason : ObjectiveActivity.Refusal)
  /-- The call's target is already on the stack. Mandatory. -/
  | reentry (target : Nat) (stack : List Nat)
  /-- The stack would exceed `callDepth`. -/
  | depth (limit : Nat)
  /-- The target cell has no object record. -/
  | notAnObject (target : Nat)
  /-- The target object has no declared state to show the callee. -/
  | stateMissing (target : Nat)
  /-- The declaration is not a call method of the pinned package (it does not
  lower, its type is not `view -> args -> Activity<call-only, returned-only, _>`). -/
  | notCallable (target : Nat) (method : String) (reason : String)
  /-- The view or the arguments do not type at the method's declared domains. -/
  | argumentType (target : Nat) (method : String)
  /-- The frame yielded a Plan that is not `call {target, method, args}`. -/
  | callShape (target : Nat) (method : String) (reason : String)
  /-- The frame's machine run faulted (divergence, a machine refusal, a Plan or
  result that does not extract, a return that is not `{result, write}`). -/
  | frameFault (target : Nat) (method : String) (reason : String)
  /-- A callee's result does not type at the caller's response type. -/
  | resultType (caller : Nat) (method : String)
  /-- A scoped grant names (target, method) and has no use left. -/
  | grantSpent (target : Nat) (method : String)
  /-- The object's law refuses the frame's write: the frame and the clause. -/
  | lawDenied (target : Nat) (method : String) (reason : WriteRefusal)
  /-- The invocation's declared envelope ran out (nothing commits). -/
  | exhausted
  /-- The inbox of (sender, target) holds `Inbox.bound` messages: the send is refused. -/
  | queueFull (sender target : Nat)
  /-- The reply slot a pipelined send names already queues `Inbox.bound` sends. -/
  | slotQueueFull (slot : Nat)
  /-- A pipelined send names no open delivery slot (no such slot, decided, or a
  subject's slot: only the reply of a message in an inbox queues sends). -/
  | notPipelinable (slot : Nat)
  /-- The reply slot a send would open is already a cell. -/
  | slotTaken (slot : Nat)
  /-- The inbox cell of (sender, target) holds something that is not that inbox. -/
  | inboxCodec (sender target : Nat)
  /-- A mail write would land on a cell that holds a package (never, for a cell read as an inbox or a slot). -/
  | packageCell (cell : Nat)
  /-- The state the call tree leaves on a draining object is one MIGRATE would refuse
  (`Journal.drained`; every frame's write already passed `ObjectRecord.judge`, this re-judges
  what the turn commits). -/
  | drainConflict (target : Nat)
  deriving Repr

/-- The deepest call stack a turn may build. -/
def callDepth : Nat := 8

/-- The `turn` request fact of a call frame's write. -/
def callTurn : Nat := 5

/-! ## Method programs -/

/-- The labels of a closed row. -/
def rowLabels (bounds : Bounds) : Nat → Ty → Option (List String)
  | 0, _ => none
  | _ + 1, .emptyRow => some []
  | fuel + 1, .field name _ tail => (rowLabels bounds fuel tail).map (name :: ·)
  | fuel + 1, .variable index => (bounds.lookup index).bind (rowLabels bounds fuel)
  | _ + 1, _ => none

/-- A sum type with at least one label, every label among `allowed`. -/
def labelsWithin (assumptions : Assumptions) (type : Ty) (allowed : List String) : Bool :=
  match unalias assumptions.bounds type with
  | .variant row => match rowLabels assumptions.bounds 64 row with
    | some labels => !labels.isEmpty && labels.all (fun label => allowed.contains label)
    | none => false
  | _ => false

/-- The Plan labels a call frame may yield: both answered in the same turn. -/
def framePlans : List String := ["call", "send"]

/-- The responses a call frame is resumed with. -/
def frameResponses : List String := ["returned", "queued"]

/-- The package `pin` names with `method` selected: the same sources. -/
def methodPackage (package : ObjectiveSourcePackage.Package) (method : String) :
    ObjectiveSourcePackage.Package :=
  { package with entryDefinition := method }

/-- A method of an object's pinned package, lowered by the kernel's own front end
from the pinned sources, applied to the frame's view and arguments, and checked. -/
structure Method (config : Config) (pin : Digest) (method : String) (view args : Data) where
  private mk ::
  definition : Replay config pin
  lowering : ObjectiveBendFrontEnd.Lowering
  replayExact : ObjectiveBendPublication.replay (methodPackage definition.package method) = .ok lowering
  accepted : ObjectiveBendFrontEnd.Accepted lowering
  fuelWithin : accepted.packet.fuel ≤ config.typeFuel
  applied : AnnotatedTerm
  checked : Checked applied []
  planType : Ty
  responseType : Ty
  resultType : Ty
  typeExact : checked.type = .computation planType responseType resultType
  callsOnly : labelsWithin applied.assumptions planType framePlans = true
  returnsOnly : labelsWithin applied.assumptions responseType frameResponses = true

def loadMethod (config : Config) (target : Nat) (bytes : Bytes) (pin : Digest) (method : String)
    (view args : Data) : Except CallRefusal (Method config pin method view args) :=
  match decodeStored bytes with
  | none => .error (.kernel .packageMissing)
  | some stored =>
  match replayPackage config stored pin with
  | .error reason => .error (.kernel reason)
  | .ok definition =>
  match replayExact : ObjectiveBendPublication.replay (methodPackage definition.package method) with
  | .error d => .error (.notCallable target method d.message)
  | .ok lowering =>
  match ObjectiveBendFrontEnd.accept lowering with
  | .error d => .error (.notCallable target method d.message)
  | .ok accepted =>
  if fuelWithin : accepted.packet.fuel ≤ config.typeFuel then
    match callable accepted.typed.type with
    | .arrow _ _ viewType (.arrow _ _ argsType _) =>
      let source := accepted.source
      let applied : AnnotatedTerm := ⟨.app (.app source.term view.term) args.term,
        fun path => match path with
          | 0 :: 0 :: rest => source.annotations rest
          | 0 :: 1 :: rest => annotationsOf (dataAnnotations source.assumptions.bounds 64 view viewType []) rest
          | 1 :: rest => annotationsOf (dataAnnotations source.assumptions.bounds 64 args argsType []) rest
          | _ => none,
        source.assumptions⟩
      match check applied [] config.typeFuel with
      | none => .error (.argumentType target method)
      | some checked =>
        match typeExact : checked.type with
        | .computation planType responseType resultType =>
          if callsOnly : labelsWithin applied.assumptions planType framePlans = true then
            if returnsOnly : labelsWithin applied.assumptions responseType frameResponses = true then
              .ok ⟨definition, lowering, replayExact, accepted, fuelWithin, applied, checked, planType,
                responseType, resultType, typeExact, callsOnly, returnsOnly⟩
            else .error (.notCallable target method "its response type is not within `returned | queued`")
          else .error (.notCallable target method
            "its Plan type is not within `call | send`: a method that awaits is not callable")
        | _ => .error (.notCallable target method "it does not return an Activity")
    | _ => .error (.notCallable target method "it does not take a view and arguments")
  else .error (.notCallable target method "typed core checker fuel exceeds the kernel's capacity")

/-! ## Plans, returns, grants -/

/-- A call a frame yields: `call {target, method, args}`. -/
structure CallPlan where
  target : CellId
  method : String
  args : Data

/-- Where a send goes: an object's inbox, or the reply slot of an earlier send
(pipelined: queued there and forwarded when that slot is decided). -/
inductive Destination where
  | object (target : Nat)
  | slot (name : Digest)
  deriving DecidableEq, Repr

/-- A send a frame yields: `send {to, method, args}`. -/
structure SendPlan where
  destination : Destination
  method : String
  args : Data

inductive Yield where
  | call (plan : CallPlan)
  | send (plan : SendPlan)

def decodeYield (target : Nat) (method : String) : Data → Except CallRefusal Yield
  | .variant "call" (.record fields) =>
    match fieldOf fields "target", fieldOf fields "method", fieldOf fields "args" with
    | some (.natural object), some (.label name), some args => .ok (.call ⟨⟨object⟩, name, args⟩)
    | _, _, _ => .error (.callShape target method "call needs target (Nat), method (String) and args")
  | .variant "send" (.record fields) =>
    match fieldOf fields "to", fieldOf fields "method", fieldOf fields "args" with
    | some (.variant "object" (.natural object)), some (.label name), some args =>
      .ok (.send ⟨.object object, name, args⟩)
    | some (.variant "slot" (.natural slot)), some (.label name), some args =>
      .ok (.send ⟨.slot ⟨slot⟩, name, args⟩)
    | _, _, _ => .error (.callShape target method "send needs to (object Nat | slot Nat), method (String) and args")
  | _ => .error (.callShape target method "a frame yields only `call` or `send`")

/-- The response a frame is resumed with after a send: its message id, which is
also its reply slot's name. -/
def queuedData (id : Digest) : Data := .variant "queued" (.record [("slot", .natural id.value)])

/-- The response a frame is resumed with after its callee returned. -/
def returnedData (result : Data) : Data := .variant "returned" (.record [("result", result)])

/-- A frame's return: `{result, write}`. -/
def decodeReturn (target : Nat) (method : String) : Data → Except CallRefusal (Data × Data)
  | .record fields =>
    match fieldOf fields "result", fieldOf fields "write" with
    | some result, some write => .ok (result, write)
    | _, _ => .error (.frameFault target method "a method returns {result, write}")
  | _ => .error (.frameFault target method "a method returns {result, write}")

/-- A scoped grant: the signer lends its authority to `uses` frames of
`method` on the object `object`. -/
structure Grant where
  object : Nat
  method : String
  uses : Nat
  deriving DecidableEq, Repr

inductive Spend where
  | ungranted
  | spent (grants : List Grant)
  | exhausted
  deriving Repr

/-- Spend one use of the first grant naming (object, method). -/
def spendGrant (object : Nat) (method : String) : List Grant → Spend
  | [] => .ungranted
  | grant :: rest =>
    if grant.object = object ∧ grant.method = method then
      if grant.uses = 0 then .exhausted else .spent ({grant with uses := grant.uses - 1} :: rest)
    else match spendGrant object method rest with
      | .spent rest' => .spent (grant :: rest')
      | other => other

/-! ## The turn's journal -/

/-- An object a frame of this turn touched: its record and its declared state
as the turn now holds it. -/
structure Entry where
  object : CellId
  record : ObjectRecord
  current : Option ObjectState
  dirty : Bool

/-- A frame return that wrote: the object, the method, the facts it was judged
under, the state the frame was SHOWN, the state the journal held at its return
(the one the write is applied to), and the new state. -/
structure Written where
  object : CellId
  method : String
  record : ObjectRecord
  facts : Facts
  viewed : ObjectState
  before : ObjectState
  after : ObjectState

/-- A send a frame of this turn made. -/
structure Outgoing where
  /-- `Inbox.sendId turn index`. -/
  id : Digest
  /-- The sending frame's object. -/
  sender : Nat
  destination : Destination
  method : String
  args : Data

structure Journal where
  entries : List Entry
  grants : List Grant
  /-- Every frame entered, in order: the objects on the stack at its entry,
  innermost first (the frame's own object at the head). -/
  frames : List (List Nat)
  writes : List Written
  /-- Every send, in the order the frames made them. -/
  outbox : List Outgoing

def Journal.start (grants : List Grant) : Journal := ⟨[], grants, [], [], []⟩

/-- Who a call tree runs for: the root frame's subject (an invocation's signer;
none for a delivered message) and the root's caller (none for an invocation;
the sending object for a delivered message). -/
structure Authority where
  signer : Option SubjectId
  origin : Option Nat


/-- The state the journal holds for an object (`none`: not touched). -/
def Journal.lookup (journal : Journal) (object : CellId) : Option (Option ObjectState) :=
  (journal.entries.find? (fun entry => entry.object == object)).map Entry.current

/-- The entry of an object: the journal's, or read from the snapshot. -/
def touch {rootBytes : Bytes → Digest} (config : Config) (snapshot : Snapshot rootBytes)
    (journal : Journal) (object : CellId) : Except CallRefusal (Entry × Journal) :=
  match journal.entries.find? (fun entry => entry.object == object) with
  | some entry => .ok (entry, journal)
  | none =>
    match readObject config snapshot object with
    | .error reason => .error (.kernel reason)
    | .ok none => .error (.notAnObject object.value)
    | .ok (some record) =>
      match readState config snapshot object with
      | .error reason => .error (.kernel reason)
      | .ok current =>
        let entry : Entry := ⟨object, record, current, false⟩
        .ok (entry, { journal with entries := journal.entries ++ [entry] })

/-- A frame on the stack. -/
structure Ctx where
  object : CellId
  method : String
  record : ObjectRecord
  assumptions : Assumptions
  responseType : Ty
  view : ObjectState
  /-- The subject whose authority the frame's write carries (`Facts.subject`). -/
  subject : Option SubjectId
  height : Nat
  /-- `request/caller` (`callerOf`). -/
  caller : Option Nat

/-- **The request facts a frame's write is judged under**, derived from the frame itself:
the frame is for `ctx.object` and runs `ctx.method` of the package its record pins
(`loadMethod` on `record.activePin`: the pin, or while draining under the identity the next
pin), so the artifact slot reads that package and nothing else. The
facts are not a field: no frame can be built that claims another package. -/
def Ctx.facts (ctx : Ctx) : Facts :=
  ⟨ctx.subject, ctx.height, ctx.object.value, callTurn, ctx.caller, some ctx.record.activePin.value⟩

/-- A frame's write is made by its object's pinned package: the slot names it. -/
theorem Ctx.facts_artifact (ctx : Ctx) : ctx.facts.artifact = some ctx.record.activePin.value := rfl

/-- `request/caller` of a frame entered on `stack`: the calling frame's object,
or the root's origin. -/
def callerOf (authority : Authority) (stack : List Ctx) : Option Nat :=
  match stack.head? with
  | some ctx => some ctx.object.value
  | none => authority.origin

/-- Replace the current state of one object. -/
def Journal.install (journal : Journal) (object : CellId) (state : ObjectState) : Journal :=
  { journal with entries := journal.entries.map fun entry =>
      if entry.object == object then { entry with current := some state, dirty := true } else entry }

/-- **Frame return**: the frame's write, applied to its own object's state as
the journal holds it, judged by that object's law under the frame's facts. -/
def frameReturn (ctx : Ctx) (write : Data) (journal : Journal) : Except CallRefusal Journal :=
  match decodeWrite write with
  | .error reason => .error (.frameFault ctx.object.value ctx.method (reprStr reason))
  | .ok edits =>
    match journal.lookup ctx.object with
    | some (some before) =>
      match applyWrite edits (some before.value) with
      | .error reason => .error (.frameFault ctx.object.value ctx.method (reprStr reason))
      | .ok none => .ok journal
      | .ok (some value) =>
        match ctx.record.judge ctx.facts (some before.value) value with
        | .error reason => .error (.lawDenied ctx.object.value ctx.method reason)
        | .ok () =>
          let after : ObjectState := ⟨before.version + 1, value⟩
          .ok { journal.install ctx.object after with
            writes := journal.writes ++ [⟨ctx.object, ctx.method, ctx.record, ctx.facts, ctx.view, before, after⟩] }
    | _ => .error (.stateMissing ctx.object.value)

/-! ## The executor -/

inductive Task where
  | enter (call : CallPlan)
  | run (state : State)

/-- Run the call tree. `enter` pushes a frame for a call (refusing re-entry),
`run` runs the top frame from a machine state to its return, entering every call
it yields depth-first and resuming it with the callee's result. The result is
the frame's `result`, the journal, and the ticks left. `fuel` only bounds the
recursion; the envelope's ticks bound the work. -/
def exec {rootBytes : Bytes → Digest} (config : Config) (snapshot : Snapshot rootBytes) (height : Nat)
    (authority : Authority) (turn : TransactionId) :
    Nat → List Ctx → Task → Journal → Nat → Except CallRefusal (Data × Journal × Nat)
  | 0, _, _, _, _ => .error .exhausted
  | fuel + 1, stack, .enter call, journal, ticks =>
    if stack.any (fun ctx => ctx.object == call.target) then
      .error (.reentry call.target.value (stack.map (·.object.value)))
    else if callDepth ≤ stack.length then .error (.depth callDepth)
    else
    match touch config snapshot journal call.target with
    | .error reason => .error reason
    | .ok (entry, journal) =>
    match entry.current, entry.record.admitsNew with
    | none, _ => .error (.stateMissing call.target.value)
    -- A draining object admits no new frame unless its upgrade's migration is the identity.
    | some _, false => .error (.kernel .draining)
    | some view, true =>
    let granted : Except CallRefusal (Option SubjectId × List Grant) :=
      match stack with
      | [] => .ok (authority.signer, journal.grants)
      | _ :: _ => match spendGrant call.target.value call.method journal.grants with
        | .ungranted => .ok (none, journal.grants)
        | .spent grants => .ok (authority.signer, grants)
        | .exhausted => .error (.grantSpent call.target.value call.method)
    match granted with
    | .error reason => .error reason
    | .ok (subject, grants) =>
    match loadMethod config call.target.value (packageBytes config snapshot entry.record.activePin) entry.record.activePin
        call.method (viewData view) call.args with
    | .error reason => .error reason
    | .ok program =>
    let ctx : Ctx := ⟨call.target, call.method, entry.record, program.applied.assumptions, program.responseType,
      view, subject, height, callerOf authority stack⟩
    let journal : Journal := ⟨journal.entries, grants,
      journal.frames ++ [call.target.value :: stack.map (·.object.value)], journal.writes, journal.outbox⟩
    exec config snapshot height authority turn fuel (ctx :: stack) (.run (initial program.applied.erase)) journal ticks
  | _ + 1, [], .run _, _, _ => .error .exhausted
  | fuel + 1, ctx :: rest, .run state, journal, ticks =>
    match runCounted config.limits ticks state with
    | (.yielded _ yielded, left) =>
      match ObjectiveBendDemandData.yieldedPlan config.limits config.planBudget yielded with
      | .error (failure, _) => .error (.frameFault ctx.object.value ctx.method s!"plan extraction: {reprStr failure}")
      | .ok extracted =>
      match decodeYield ctx.object.value ctx.method extracted.value with
      | .error reason => .error reason
      | .ok (.call call) =>
        match exec config snapshot height authority turn fuel (ctx :: rest) (.enter call) journal left with
        | .error reason => .error reason
        | .ok (result, journal, left) =>
        match typeData ctx.assumptions config.typeFuel (returnedData result) ctx.responseType with
        | none => .error (.resultType ctx.object.value ctx.method)
        | some _ =>
        match resume (returnedData result).term yielded with
        | none => .error (.frameFault ctx.object.value ctx.method "resume")
        | some next => exec config snapshot height authority turn fuel (ctx :: rest) (.run next) journal left
      | .ok (.send send) =>
        let id := Inbox.sendId turn journal.outbox.length
        match typeData ctx.assumptions config.typeFuel (queuedData id) ctx.responseType with
        | none => .error (.resultType ctx.object.value ctx.method)
        | some _ =>
        match resume (queuedData id).term yielded with
        | none => .error (.frameFault ctx.object.value ctx.method "resume")
        | some next => exec config snapshot height authority turn fuel (ctx :: rest) (.run next)
            { journal with outbox := journal.outbox ++ [⟨id, ctx.object.value, send.destination, send.method, send.args⟩] }
            left
    | (.finished _ finished, left) =>
      match ObjectiveBendDemandData.complete config.limits config.planBudget finished with
      | .error (failure, _) => .error (.frameFault ctx.object.value ctx.method s!"result extraction: {reprStr failure}")
      | .ok out =>
      match decodeReturn ctx.object.value ctx.method out.value with
      | .error reason => .error reason
      | .ok (result, write) =>
      match frameReturn ctx write journal with
      | .error reason => .error reason
      | .ok journal => .ok (result, journal, left)
    | (.suspended _ _, _) => .error .exhausted
    | (.divergent _ _, _) => .error (.frameFault ctx.object.value ctx.method "divergent")
    | (.refused reason _, _) => .error (.frameFault ctx.object.value ctx.method (reprStr reason))


/-! ## The turn's mail: inboxes and reply slots -/

/-- An inbox as this turn holds it: what its cell held when the turn read it
(`none`: no inbox yet) and what the turn will post, a LAWFUL change of it
(`Inbox.Lawful`: pushes within the bound and pops of the head). A cell is held
only after it was read and found to be that inbox or empty. -/
structure HeldInbox {rootBytes : Bytes → Digest} (config : Config) (snapshot : Snapshot rootBytes) where
  sender : Nat
  target : Nat
  read : Option Inbox.Inbox
  readExact : readInbox snapshot (Inbox.cell config.domain sender target) = some read
  clean : bodyOf .package (snapshot.canonicalBytes (Inbox.cell config.domain sender target)) = none
  now : Inbox.Inbox
  lawful : Inbox.Lawful (read.getD (Inbox.Inbox.empty sender target)) now
  ends : now.sender = sender ∧ now.target = target

def HeldInbox.cell {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    (held : HeldInbox config snapshot) : CellId :=
  Inbox.cell config.domain held.sender held.target

/-- A reply slot this turn writes, open: one it opens for a message entering an
inbox (`read = none`), or an open delivery slot it read and queues a send on. -/
structure HeldSlot {rootBytes : Bytes → Digest} (config : Config) (snapshot : Snapshot rootBytes) where
  name : Digest
  read : Option AnswerSlot.Slot
  clean : bodyOf .package (snapshot.canonicalBytes (AnswerSlot.cell config.domain name)) = none
  /-- The cell held nothing (a slot this turn opens) or a slot (one it read). -/
  slotted : ∀ payload, payloadOf (snapshot.canonicalBytes (AnswerSlot.cell config.domain name)) = some payload →
    payload.role = .slot
  now : AnswerSlot.Slot
  named : now.name = name
  opened : now.phase = .opened

structure Mail {rootBytes : Bytes → Digest} (config : Config) (snapshot : Snapshot rootBytes) where
  inboxes : List (HeldInbox config snapshot)
  slots : List (HeldSlot config snapshot)
  /-- The postage each queued message escrows, in order: the purse of the queue
  holding it (an inbox's, or the inbox holding the message a slot answers). -/
  credits : List (AccountId × Nat)
  /-- Every object a message was addressed to (read as an object; guarded). -/
  targets : List Nat

def Mail.empty {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes} :
    Mail config snapshot := ⟨[], [], [], []⟩

/-- The inbox of (sender, target): the one this turn holds, else read from the
snapshot. Returns it and the other held inboxes. -/
def holdInbox {rootBytes : Bytes → Digest} (config : Config) (snapshot : Snapshot rootBytes)
    (mail : Mail config snapshot) (sender target : Nat) :
    Except CallRefusal (HeldInbox config snapshot × List (HeldInbox config snapshot)) :=
  match mail.inboxes.find? (fun held => held.sender == sender && held.target == target) with
  | some held => .ok (held, mail.inboxes.filter (fun other => !(other.sender == sender && other.target == target)))
  | none =>
    match readExact : readInbox snapshot (Inbox.cell config.domain sender target) with
    | none => .error (.inboxCodec sender target)
    | some read =>
      if ends : (read.getD (Inbox.Inbox.empty sender target)).sender = sender ∧
          (read.getD (Inbox.Inbox.empty sender target)).target = target then
        if clean : bodyOf .package (snapshot.canonicalBytes (Inbox.cell config.domain sender target)) = none then
          .ok (⟨sender, target, read, readExact, clean, read.getD (Inbox.Inbox.empty sender target), .refl _, ends⟩,
            mail.inboxes)
        else .error (.packageCell (Inbox.cell config.domain sender target).value)
      else .error (.inboxCodec sender target)

/-- Open the reply slot of a message entering the inbox `inbox`: its cell must
hold nothing (no slot, never retired) and no slot of this turn may name it. -/
def openSlot {rootBytes : Bytes → Digest} (config : Config) (snapshot : Snapshot rootBytes)
    (mail : Mail config snapshot) (name : Digest) (inbox : CellId) : Except CallRefusal (HeldSlot config snapshot) :=
  let bytes := snapshot.canonicalBytes (AnswerSlot.cell config.domain name)
  if taken : (payloadOf bytes).isSome || isRetired bytes || mail.slots.any (fun held => held.name == name) then
    .error (.slotTaken name.value)
  else if clean : bodyOf .package bytes = none then
    have slotted : ∀ payload, payloadOf bytes = some payload → payload.role = .slot := by
      intro payload found
      simp [found] at taken
    .ok ⟨name, none, clean, slotted, ⟨name, inbox, .delivery name, 0, .opened, []⟩, rfl, rfl⟩
  else .error (.packageCell (AnswerSlot.cell config.domain name).value)

/-- The open slot a pipelined send names: the one this turn holds, else read. -/
def holdSlot {rootBytes : Bytes → Digest} (config : Config) (snapshot : Snapshot rootBytes)
    (mail : Mail config snapshot) (name : Digest) :
    Except CallRefusal (HeldSlot config snapshot × List (HeldSlot config snapshot)) :=
  match mail.slots.find? (fun held => held.name == name) with
  | some held => .ok (held, mail.slots.filter (fun other => !(other.name == name)))
  | none =>
    match readExact : readSlot config snapshot name with
    | none => .error (.notPipelinable name.value)
    | some slot =>
      if named : slot.name = name then
        if opened : slot.phase = .opened then
          if clean : bodyOf .package (snapshot.canonicalBytes (AnswerSlot.cell config.domain name)) = none then
            have slotted : ∀ payload, payloadOf (snapshot.canonicalBytes (AnswerSlot.cell config.domain name)) =
                some payload → payload.role = .slot := by
              intro payload found
              by_contra wrong
              have empty : bodyOf .slot (snapshot.canonicalBytes (AnswerSlot.cell config.domain name)) = none := by
                simp [bodyOf, found, wrong]
              simp [readSlot, empty] at readExact
            .ok (⟨name, some slot, clean, slotted, slot, named, opened⟩, mail.slots)
          else .error (.packageCell (AnswerSlot.cell config.domain name).value)
        else .error (.notPipelinable name.value)
      else .error (.notPipelinable name.value)

/-- **Queue one message.** To an object: it must be an object; the message is
pushed onto the inbox (sender, target), refused `queueFull` at the bound, and
its reply slot is opened, decided only by its delivery. To a slot: the slot must
be an open delivery slot (the reply of a message in an inbox); the message is
queued on it, refused `slotQueueFull` at the bound. Either way its postage is
credited to the purse of the queue that holds it. -/
def Mail.send {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    (mail : Mail config snapshot) (message : Inbox.Message) :
    Destination → Except CallRefusal (Mail config snapshot)
  | .object target =>
    match readObject config snapshot ⟨target⟩ with
    | .error reason => .error (.kernel reason)
    | .ok none => .error (.notAnObject target)
    | .ok (some _) =>
    match holdInbox config snapshot mail message.sender target with
    | .error reason => .error reason
    | .ok (held, others) =>
    match pushed : held.now.push message with
    | none => .error (.queueFull message.sender target)
    | some next =>
    match openSlot config snapshot mail message.id held.cell with
    | .error reason => .error reason
    | .ok slot =>
      have keeps := (Inbox.push_step pushed).keeps
      let updated : HeldInbox config snapshot :=
        ⟨held.sender, held.target, held.read, held.readExact, held.clean, next,
          held.lawful.snoc (Inbox.push_step pushed), ⟨keeps.1.trans held.ends.1, keeps.2.1.trans held.ends.2⟩⟩
      .ok ⟨others ++ [updated], mail.slots ++ [slot], mail.credits ++ [(held.cell.value, message.postage)],
        mail.targets ++ [target]⟩
  | .slot name =>
    match holdSlot config snapshot mail name with
    | .error reason => .error reason
    | .ok (held, others) =>
      match held.now.decider with
      | .subject _ => .error (.notPipelinable name.value)
      | .delivery _ =>
        if held.now.queued.length < Inbox.bound then
          let updated : HeldSlot config snapshot :=
            ⟨held.name, held.read, held.clean, held.slotted, { held.now with queued := held.now.queued ++ [message] },
              held.named, held.opened⟩
          .ok ⟨mail.inboxes, others ++ [updated], mail.credits ++ [(held.now.activity.value, message.postage)],
            mail.targets⟩
        else .error (.slotQueueFull name.value)

/-- The message a send queues: its delivery runs under `postage`, whose public
price it escrows, refunded to `refund` if it is never delivered. -/
def messageOf (config : Config) (postage : Capacity) (refund : AccountId) (out : Outgoing) : Inbox.Message :=
  ⟨out.id, out.sender, out.method, dataBytes out.args, postage, config.tariff.workOf postage, refund⟩

/-- The mail of a turn's sends, in order. -/
def postMail {rootBytes : Bytes → Digest} (config : Config) (snapshot : Snapshot rootBytes)
    (postage : Capacity) (refund : AccountId) : Mail config snapshot → List Outgoing → Except CallRefusal (Mail config snapshot)
  | mail, [] => .ok mail
  | mail, out :: rest =>
    match mail.send (messageOf config postage refund out) out.destination with
    | .error reason => .error reason
    | .ok mail => postMail config snapshot postage refund mail rest

/-- The posts of the mail: every held inbox and every held slot, against the
roots the turn read them at. -/
def Mail.posts {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    (mail : Mail config snapshot) : List Post :=
  mail.inboxes.map (fun held => postAt snapshot held.cell (inboxImage held.now)) ++
    mail.slots.map (fun held => slotPost config snapshot held.now)

/-- The purses of inboxes the mail opens: registered on the Book in its batch. -/
def Mail.registrations {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    (mail : Mail config snapshot) (book : Book) : List AccountId :=
  (mail.inboxes.map fun held => held.cell.value).filter fun account => !decide (account ∈ book.accounts)

/-- Postage credits as transfers from `source` (zero amounts and self-transfers dropped). -/
def creditTransfers (config : Config) (source : AccountId) (credits : List (AccountId × Nat)) : List Operation :=
  credits.filterMap fun (purse, amount) =>
    if amount = 0 ∨ purse = source then none else some (.transfer source purse config.asset amount)

/-- Every post of the mail is an inbox or slot image at a cell that holds no package. -/
theorem Mail.posts_shape {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    (mail : Mail config snapshot) :
    ∀ post ∈ mail.posts, ∃ cell role key body, role ≠ .record ∧
      bodyOf .package (snapshot.canonicalBytes cell) = none ∧ post = postAt snapshot cell (image role key body) := by
  intro post member
  rcases List.mem_append.mp member with inInbox | inSlot
  · obtain ⟨held, _, rfl⟩ := List.mem_map.mp inInbox
    exact ⟨held.cell, .inbox, Inbox.key held.now.sender held.now.target, Inbox.encode held.now,
      (by decide : ObjectiveActivityCell.Role.inbox ≠ .record), held.clean, rfl⟩
  · obtain ⟨held, _, rfl⟩ := List.mem_map.mp inSlot
    refine ⟨AnswerSlot.cell config.domain held.name, .slot, AnswerSlot.key held.now.name, AnswerSlot.encode held.now,
      (by decide : ObjectiveActivityCell.Role.slot ≠ .record), held.clean, ?_⟩
    unfold slotPost
    rw [held.named]

/-- **Every inbox the mail posts is a lawful change of what its cell held**
(condition (b) of OB8, for the mail): the cell was read in this turn, held
that inbox or nothing, and the post is pushes within the bound and pops of the
head, at that cell, under that inbox's own key. -/
theorem Mail.inboxes_lawful {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    (mail : Mail config snapshot) :
    ∀ held ∈ mail.inboxes,
      readInbox snapshot (Inbox.cell config.domain held.sender held.target) = some held.read ∧
      Inbox.Lawful (held.read.getD (Inbox.Inbox.empty held.sender held.target)) held.now ∧
      postAt snapshot held.cell (inboxImage held.now) =
        postAt snapshot (Inbox.cell config.domain held.now.sender held.now.target) (inboxImage held.now) := by
  intro held _
  refine ⟨held.readExact, held.lawful, ?_⟩
  rw [held.ends.1, held.ends.2]; rfl

/-! ## The invocation turn -/

structure InvokeRequest where
  subject : SubjectId
  object : CellId
  method : String
  args : Data
  grants : List Grant
  /-- The one declared envelope of the whole call tree. -/
  envelope : Capacity
  /-- The signer's Book account: pays the envelope's public price and every send's postage. -/
  account : AccountId
  nonce : Nat
  /-- The declared envelope every message this invocation sends is delivered
  under; each send escrows its public price (`Inbox.Message.postage`). -/
  postage : Capacity

def grantStream : StreamCodec Grant :=
  StreamCodec.xmap (StreamCodec.product StreamCodec.nat (StreamCodec.product stringStream StreamCodec.nat))
    (fun grant => (grant.object, grant.method, grant.uses)) (fun (o, m, u) => ⟨o, m, u⟩)
    (by intro grant; cases grant; rfl)

def invokeTransaction (request : InvokeRequest) : TransactionId :=
  tagged "DREGG/OBJECTIVE/OBJECT/TX/INVOKE/v1"
    (subjectStream.encode request.subject ++ digestStream.encode request.object ++
      stringStream.encode request.method ++ bytesStream.encode (dataBytes request.args) ++
      (StreamCodec.list grantStream).encode request.grants ++ StreamCodec.nat.encode request.nonce)

/-- The recursion bound: every frame entry and every segment costs at least one
unit of it. A call tree that would need more is refused `exhausted`. -/
def callFuel (envelope : Capacity) : Nat := 2 * envelope.sourceTicks + 2 * callDepth + 2

def rootCall (request : InvokeRequest) : CallPlan := ⟨request.object, request.method, request.args⟩

/-- **What a call tree commits on a draining object is migratable**: a written entry of an
object that drains (under the identity: a frame never enters one under a migration term)
leaves a state the record MIGRATE will install admits under the migration's facts. -/
def Entry.drained (entry : Entry) : Bool :=
  !entry.dirty ||
    match entry.current, entry.record.phase with
    | some state, .draining next _ =>
      next.migration.isNone &&
        (match admitWrite (entry.record.successor next) (ObjectRecord.migrateFacts entry.object.value next)
            (some state.value) state.value with
          | .ok () => true
          | .error _ => false)
    | _, _ => true

/-- Every written entry of the journal is `drained`. -/
def Journal.drained (journal : Journal) : Bool := journal.entries.all Entry.drained

/-- The posts of the written objects' state cells. -/
def Journal.posts {rootBytes : Bytes → Digest} (journal : Journal) (config : Config)
    (snapshot : Snapshot rootBytes) : List Post :=
  journal.entries.filterMap fun entry =>
    if entry.dirty then entry.current.map fun state =>
      postAt snapshot (stateCell config.domain entry.object) (stateImage entry.object state)
    else none

/-- Every object a frame read: its record, its package and its state, as of the snapshot. -/
def Journal.guards {rootBytes : Bytes → Digest} (journal : Journal) (config : Config)
    (snapshot : Snapshot rootBytes) : List ReadGuard :=
  journal.entries.flatMap fun entry =>
    [guardAt snapshot (objectCell config.domain entry.object),
     guardAt snapshot (packageCell config.domain entry.record.activePin),
     guardAt snapshot (stateCell config.domain entry.object)]

/-- The root authority of an invocation: the signer, no caller. -/
def InvokeRequest.authority (request : InvokeRequest) : Authority := ⟨some request.subject, none⟩

/-- An invocation's Book batch: register the purses of inboxes its mail opens,
pay the envelope's public price, escrow every send's postage in its queue's purse. -/
def invokeBatch {rootBytes : Bytes → Digest} {snapshot : Snapshot rootBytes} (config : Config) (book : Book)
    (request : InvokeRequest) (mail : Mail config snapshot) : Batch :=
  ⟨mail.registrations book,
    .fee request.account config.collector config.asset (config.tariff.workOf request.envelope) ::
      creditTransfers config request.account mail.credits, []⟩

/-- An admitted invocation: the call tree ran to the root's return within the
envelope, every frame write passed its object's law, its sends are queued (each
inbox within its bound, each reply slot opened), and the fee and postage are posted. -/
structure Invocation {rootBytes : Bytes → Digest} (config : Config) (snapshot : Snapshot rootBytes)
    (height : Nat) (request : InvokeRequest) where
  private mk ::
  covered : config.covers request.envelope = true
  result : Data
  journal : Journal
  left : Nat
  execExact : exec config snapshot height request.authority (invokeTransaction request) (callFuel request.envelope) []
    (.enter (rootCall request)) (Journal.start request.grants) request.envelope.sourceTicks = .ok (result, journal, left)
  /-- A turn that sends declares a postage envelope the deployment covers. -/
  postageCovered : journal.outbox ≠ [] → config.covers request.postage = true
  /-- What the call tree commits on a draining object is migratable. -/
  drainedOk : journal.drained = true
  mail : Mail config snapshot
  mailExact : postMail config snapshot request.postage request.account Mail.empty journal.outbox = .ok mail
  book : BookCell
  bookExact : loadBook config snapshot = .ok book
  posted : Postings book
  batchExact : posted.batch = invokeBatch config (logicalBook book.logical) request mail
  posts : List Post
  postsExact : posts = journal.posts config snapshot ++ mail.posts ++ [posted.write config snapshot]

def invoke {rootBytes : Bytes → Digest} (config : Config) (snapshot : Snapshot rootBytes)
    (height : Nat) (request : InvokeRequest) : Except CallRefusal (Invocation config snapshot height request) :=
  if covered : config.covers request.envelope = true then
    match execExact : exec config snapshot height request.authority (invokeTransaction request)
        (callFuel request.envelope) [] (.enter (rootCall request)) (Journal.start request.grants)
        request.envelope.sourceTicks with
    | .error reason => .error reason
    | .ok (result, journal, left) =>
      if postageCovered : journal.outbox ≠ [] → config.covers request.postage = true then
      if drainedOk : journal.drained = true then
      match mailExact : postMail config snapshot request.postage request.account Mail.empty journal.outbox with
      | .error reason => .error reason
      | .ok mail =>
      match bookExact : loadBook config snapshot with
      | .error reason => .error (.kernel reason)
      | .ok book =>
        let batch := invokeBatch config (logicalBook book.logical) request mail
        match postedExact : postings book batch with
        | .error reason => .error (.kernel reason)
        | .ok posted =>
          have batchExact : posted.batch = batch := by
            unfold postings at postedExact
            split at postedExact
            · cases postedExact; rfl
            · cases postedExact
          .ok ⟨covered, result, journal, left, execExact, postageCovered, drainedOk, mail, mailExact, book, bookExact,
            posted, batchExact, _, rfl⟩
      else .error (.drainConflict request.object.value)
      else .error (.kernel (.uncovered request.postage))
  else .error (.kernel (.uncovered request.envelope))

def Invocation.guards {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height : Nat} {request : InvokeRequest} (invoked : Invocation config snapshot height request) : List ReadGuard :=
  invoked.journal.guards config snapshot ++
    invoked.mail.targets.map fun target => guardAt snapshot (objectCell config.domain ⟨target⟩)

def Invocation.intent {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height : Nat} {request : InvokeRequest} (invoked : Invocation config snapshot height request) (sealing : Seal) :
    DataIntent rootBytes :=
  intentOf rootBytes (invokeTransaction request) invoked.posts invoked.guards [] sealing

/-- **An invocation conserves every asset**: its fee is one admitted batch. -/
theorem Invocation.conserves {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height : Nat} {request : InvokeRequest} (invoked : Invocation config snapshot height request) (asset : AssetId) :
    (logicalBook invoked.posted.post.logical).totalAsset asset = (logicalBook invoked.book.logical).totalAsset asset :=
  invoked.posted.conserves asset

/-! ## T2: the re-entry guard -/

/-- **Re-entry is refused**: a call whose target is on the stack is refused by
name, whatever the journal, ticks or fuel. -/
theorem reentry_refused {rootBytes : Bytes → Digest} (config : Config) (snapshot : Snapshot rootBytes)
    (height : Nat) (authority : Authority) (turn : TransactionId) (fuel : Nat) (stack : List Ctx) (call : CallPlan)
    (journal : Journal) (ticks : Nat) (onStack : ∃ ctx ∈ stack, ctx.object = call.target) :
    exec config snapshot height authority turn (fuel + 1) stack (.enter call) journal ticks =
      .error (.reentry call.target.value (stack.map (·.object.value))) := by
  have hit : stack.any (fun ctx => ctx.object == call.target) = true := by
    obtain ⟨ctx, member, same⟩ := onStack
    exact List.any_eq_true.mpr ⟨ctx, member, by simp [same]⟩
  simp only [exec, hit, if_true]


/-! ### The journal lemmas -/

theorem lookup_entries {journal journal' : Journal} (same : journal'.entries = journal.entries) (object : CellId) :
    journal'.lookup object = journal.lookup object := by
  simp [Journal.lookup, same]

theorem touch_spec {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {journal journal' : Journal} {object : CellId} {entry : Entry}
    (touched : touch config snapshot journal object = .ok (entry, journal')) :
    (∀ other, other ≠ object → journal'.lookup other = journal.lookup other) ∧
      journal'.lookup object = some entry.current ∧
      journal'.writes = journal.writes ∧ journal'.frames = journal.frames ∧ journal'.grants = journal.grants := by
  unfold touch at touched
  split at touched
  · rename_i found hit
    cases touched
    refine ⟨fun _ _ => rfl, ?_, rfl, rfl, rfl⟩
    simp [Journal.lookup, hit]
  · rename_i missing
    split at touched
    · cases touched
    · cases touched
    · split at touched
      · cases touched
      · rename_i record _ current _
        cases touched
        refine ⟨?_, ?_, rfl, rfl, rfl⟩
        · intro other differs
          have skip : (object == other) = false := by simp [Ne.symm differs]
          simp [Journal.lookup, List.find?_append, skip]
        · simp [Journal.lookup, List.find?_append, missing]

/-- Every object the journal holds was read from the snapshot: its state cell
decodes there (what makes its state post safe for the checkpoint invariant) and
its object record is the one the entry carries (what names the payer of the
state cell it may write, `ObjectiveActivity.payerOf`). -/
def ObjectsRead {rootBytes : Bytes → Digest} (config : Config) (snapshot : Snapshot rootBytes)
    (journal : Journal) : Prop :=
  ∀ entry ∈ journal.entries, (∃ current, readState config snapshot entry.object = .ok current) ∧
    readObject config snapshot entry.object = .ok (some entry.record)

theorem touch_read {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {journal journal' : Journal} {object : CellId} {entry : Entry}
    (touched : touch config snapshot journal object = .ok (entry, journal'))
    (read : ObjectsRead config snapshot journal) : ObjectsRead config snapshot journal' := by
  unfold touch at touched
  split at touched
  · cases touched; exact read
  · split at touched
    · cases touched
    · cases touched
    · split at touched
      · cases touched
      · rename_i _ record readObj _ current readOk
        cases touched
        intro e member
        simp only [List.mem_append, List.mem_singleton] at member
        rcases member with old | new
        · exact read e old
        · subst new; exact ⟨⟨current, readOk⟩, readObj⟩

theorem install_read {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    (journal : Journal) (object : CellId) (state : ObjectState)
    (read : ObjectsRead config snapshot journal) : ObjectsRead config snapshot (journal.install object state) := by
  intro e member
  simp only [Journal.install, List.mem_map] at member
  obtain ⟨e0, m0, rfl⟩ := member
  obtain ⟨⟨c, h⟩, o⟩ := read e0 m0
  exact ⟨⟨c, by split <;> exact h⟩, by split <;> exact o⟩

theorem frameReturn_read {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {ctx : Ctx} {write : Data} {journal journal' : Journal}
    (returned : frameReturn ctx write journal = .ok journal')
    (read : ObjectsRead config snapshot journal) : ObjectsRead config snapshot journal' := by
  unfold frameReturn at returned
  split at returned
  · cases returned
  · split at returned
    · split at returned
      · cases returned
      · cases returned; exact read
      · split at returned
        · cases returned
        · cases returned
          exact install_read journal ctx.object _ read
    · cases returned

theorem lookup_install_ne (journal : Journal) (object other : CellId) (state : ObjectState)
    (differs : other ≠ object) : (journal.install object state).lookup other = journal.lookup other := by
  unfold Journal.lookup Journal.install
  simp only [List.find?_map]
  have keeps : ((fun entry : Entry => entry.object == other) ∘ fun entry : Entry =>
      if entry.object == object then { entry with current := some state, dirty := true } else entry) =
      fun entry : Entry => entry.object == other := by
    funext entry
    simp only [Function.comp]
    split <;> rfl
  rw [keeps]
  cases found : journal.entries.find? (fun entry => entry.object == other) with
  | none => rfl
  | some entry =>
    have at_ : entry.object = other := by
      have := List.find?_some found
      simpa using this
    have notTarget : entry.object ≠ object := by rw [at_]; exact differs
    simp [notTarget]

theorem frameReturn_spec {ctx : Ctx} {write : Data} {journal journal' : Journal}
    (returned : frameReturn ctx write journal = .ok journal') :
    (∀ other, other ≠ ctx.object → journal'.lookup other = journal.lookup other) ∧
      journal'.frames = journal.frames ∧
      ∃ new, journal'.writes = journal.writes ++ new ∧ ∀ w ∈ new,
        journal.lookup ctx.object = some (some w.before) ∧ w.viewed = ctx.view ∧ w.object = ctx.object ∧
          w.record = ctx.record ∧ w.facts = ctx.facts ∧
          w.record.judge w.facts (some w.before.value) w.after.value = .ok () := by
  unfold frameReturn at returned
  split at returned
  · cases returned
  · split at returned
    · rename_i before found
      split at returned
      · cases returned
      · cases returned
        exact ⟨fun _ _ => rfl, rfl, [], by simp, by simp⟩
      · rename_i value _
        split at returned
        · cases returned
        · rename_i admitted
          cases returned
          refine ⟨fun other differs => lookup_install_ne journal ctx.object other _ differs, rfl, ?_⟩
          refine ⟨[_], rfl, ?_⟩
          intro w member
          simp only [List.mem_singleton] at member
          subst member
          exact ⟨found, rfl, rfl, rfl, rfl, admitted⟩
    · cases returned

theorem nodup_values {stack : List Ctx} (distinct : (stack.map (·.object)).Nodup) :
    (stack.map (·.object.value)).Nodup := by
  have : stack.map (·.object.value) = (stack.map (·.object)).map Digest.value := by simp
  rw [this]
  exact distinct.map (fun a b same => by cases a; cases b; simp_all)

/-! ### T2 over the real executor -/

/-- The frames a task leaves alone: an entered call, every frame on the stack;
a running frame, every frame below it. -/
def Task.below : Task → List Ctx → List Ctx
  | .enter _, stack => stack
  | .run _, stack => stack.tail

/-- **What the executor maintains** (by induction over its recursion):
* a call subtree never changes the state of an object on the stack below it
  (`enter`: every object on the stack; `run`: every object below the running frame);
* every write it appends was applied to exactly the state its frame was shown,
  under that frame's object's law and facts;
* every stack it enters holds each object at most once. -/
theorem exec_invariant {rootBytes : Bytes → Digest} (config : Config) (snapshot : Snapshot rootBytes)
    (height : Nat) (authority : Authority) (turn : TransactionId) :
    ∀ (fuel : Nat) (stack : List Ctx) (task : Task) (journal : Journal) (ticks : Nat)
      (result : Data) (journal' : Journal) (left : Nat),
    exec config snapshot height authority turn fuel stack task journal ticks = .ok (result, journal', left) →
    (stack.map (·.object)).Nodup →
    (∀ ctx state, task = .run state → stack.head? = some ctx → journal.lookup ctx.object = some (some ctx.view)) →
    ObjectsRead config snapshot journal →
    ObjectsRead config snapshot journal' ∧
    (∀ ctx ∈ task.below stack,
        journal'.lookup ctx.object = journal.lookup ctx.object) ∧
      (∃ new, journal'.writes = journal.writes ++ new ∧ ∀ w ∈ new, w.before = w.viewed ∧
        w.record.judge w.facts (some w.before.value) w.after.value = .ok () ∧
        w.facts.artifact = some w.record.activePin.value) ∧
      (∃ new, journal'.frames = journal.frames ++ new ∧ ∀ frame ∈ new, frame.Nodup) := by
  intro fuel
  induction fuel with
  | zero => intro stack task journal ticks result journal' left ran; simp [exec] at ran
  | succ fuel ih =>
    intro stack task journal ticks result journal' left ran distinct running read
    cases task with
    | enter call =>
      simp only [exec] at ran
      split at ran
      · cases ran
      · rename_i free
        split at ran
        · cases ran
        · split at ran
          · cases ran
          · rename_i entry journal1 touched
            obtain ⟨others, here, writes1, frames1, _⟩ := touch_spec touched
            split at ran
            · cases ran
            · cases ran
            · rename_i view current _
              split at ran
              · cases ran
              · rename_i subject grants _
                split at ran
                · cases ran
                · rename_i program _
                  have notOn : ∀ ctx ∈ stack, ctx.object ≠ call.target := by
                    intro ctx member same
                    apply free
                    exact List.any_eq_true.mpr ⟨ctx, member, by simp [same]⟩
                  have distinct' : ((⟨call.target, call.method, entry.record, program.applied.assumptions,
                      program.responseType, view, subject, height,
                      callerOf authority stack⟩ : Ctx) :: stack).map (·.object) |>.Nodup := by
                    simp only [List.map_cons, List.nodup_cons, List.mem_map]
                    exact ⟨fun ⟨ctx, member, same⟩ => notOn ctx member same, distinct⟩
                  obtain ⟨read', kept, ⟨new, writes', fresh⟩, ⟨frames, frames', nodupFrames⟩⟩ :=
                    ih _ _ _ _ _ _ _ ran distinct' (by
                      intro ctx state _ head
                      simp only [List.head?_cons, Option.some.injEq] at head
                      subst head
                      simp only [Journal.lookup] at here ⊢
                      simpa [current] using here) (by
                        have read1 := touch_read touched read
                        intro e member; exact read1 e member)
                  refine ⟨read', ?_, ⟨new, ?_, fresh⟩,
                    ⟨(call.target.value :: stack.map (·.object.value)) :: frames, ?_, ?_⟩⟩
                  · intro ctx member
                    simp only [Task.below] at member
                    have := kept ctx (by simpa [Task.below] using member)
                    rw [this]
                    exact (lookup_entries (journal := journal1) rfl ctx.object).trans
                      (others ctx.object (notOn ctx member))
                  · rw [writes']; simp [writes1]
                  · rw [frames']; simp [frames1, List.append_assoc]
                  · intro frame member
                    simp only [List.mem_cons] at member
                    rcases member with first | later
                    · subst first
                      have values := nodup_values distinct
                      refine List.nodup_cons.mpr ⟨?_, values⟩
                      simp only [List.mem_map]
                      rintro ⟨ctx, member, same⟩
                      exact notOn ctx member (by cases h : ctx.object; cases call.target; simp_all)
                    · exact nodupFrames frame later
    | run state =>
      cases stack with
      | nil => simp [exec] at ran
      | cons ctx rest =>
        have viewed := running ctx state rfl rfl
        simp only [exec] at ran
        split at ran
        · -- yielded
          split at ran
          · cases ran
          · split at ran
            · cases ran
            · rename_i call _
              split at ran
              · cases ran
              · rename_i called journal1 left1 entered
                split at ran
                · cases ran
                · split at ran
                  · cases ran
                  · rename_i next _
                    obtain ⟨read1, kept1, ⟨new1, writes1, fresh1⟩, ⟨frames1, framesEq1, nodup1⟩⟩ :=
                      ih _ _ _ _ _ _ _ entered distinct (by intro _ _ h; cases h) read
                    have viewed1 : journal1.lookup ctx.object = some (some ctx.view) := by
                      rw [kept1 ctx (by simp [Task.below])]; exact viewed
                    obtain ⟨read2, kept2, ⟨new2, writes2, fresh2⟩, ⟨frames2, framesEq2, nodup2⟩⟩ :=
                      ih _ _ _ _ _ _ _ ran distinct (by
                        intro c _ _ head
                        simp only [List.head?_cons, Option.some.injEq] at head
                        subst head; exact viewed1) read1
                    refine ⟨read2, ?_, ⟨new1 ++ new2, ?_, ?_⟩, ⟨frames1 ++ frames2, ?_, ?_⟩⟩
                    · intro c member
                      simp only [Task.below, List.tail_cons] at member
                      rw [kept2 c (by simpa [Task.below] using member),
                        kept1 c (by simp [Task.below, member])]
                    · rw [writes2, writes1, List.append_assoc]
                    · intro w member
                      rcases List.mem_append.mp member with a | b
                      · exact fresh1 w a
                      · exact fresh2 w b
                    · rw [framesEq2, framesEq1, List.append_assoc]
                    · intro frame member
                      rcases List.mem_append.mp member with a | b
                      · exact nodup1 frame a
                      · exact nodup2 frame b
            · -- a send: only the outbox grows
              rename_i send _
              split at ran
              · cases ran
              · split at ran
                · cases ran
                · rename_i next _
                  obtain ⟨read2, kept2, ⟨new2, writes2, fresh2⟩, ⟨frames2, framesEq2, nodup2⟩⟩ :=
                    ih _ _ _ _ _ _ _ ran distinct (by
                      intro c _ _ head
                      simp only [List.head?_cons, Option.some.injEq] at head
                      subst head; exact viewed) read
                  refine ⟨read2, ?_, ⟨new2, writes2, fresh2⟩, ⟨frames2, framesEq2, nodup2⟩⟩
                  intro c member
                  simp only [Task.below, List.tail_cons] at member
                  exact kept2 c (by simpa [Task.below] using member)
        · -- finished
          split at ran
          · cases ran
          · split at ran
            · cases ran
            · split at ran
              · cases ran
              · rename_i journal1 returned
                cases ran
                obtain ⟨others, framesEq, new, writesEq, each⟩ := frameReturn_spec returned
                have distinctCons : (∀ x ∈ rest, ¬x.object = ctx.object) ∧ (rest.map (·.object)).Nodup := by
                  simpa using distinct
                refine ⟨frameReturn_read returned read, ?_, ⟨new, writesEq, ?_⟩, ⟨[], by simp [framesEq], by simp⟩⟩
                · intro c member
                  simp only [Task.below, List.tail_cons] at member
                  exact others c.object (distinctCons.1 c member)
                · intro w member
                  obtain ⟨found, viewedEq, _, recordEq, factsEq, admitted⟩ := each w member
                  rw [viewed] at found
                  simp only [Option.some.injEq] at found
                  refine ⟨by rw [viewedEq, found], admitted, ?_⟩
                  simpa [factsEq, recordEq] using ctx.facts_artifact
        · cases ran
        · cases ran
        · cases ran

/-- **T2 (a): no object occurs twice on any call stack the executor enters**,
in every admitted invocation. -/
theorem invocation_reentry_free {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height : Nat} {request : InvokeRequest} (invoked : Invocation config snapshot height request) :
    ∀ frame ∈ invoked.journal.frames, frame.Nodup := by
  obtain ⟨_, _, _, ⟨new, frames, nodup⟩⟩ :=
    exec_invariant config snapshot height request.authority (invokeTransaction request) _ [] _ _ _ _ _ _ invoked.execExact (by simp)
      (by intro _ _ h; cases h) (by intro _ h; cases h)
  intro frame member
  rw [frames] at member
  simp only [Journal.start, List.nil_append] at member
  exact nodup frame member

/-- **T2 (d): every write is computed from exactly the state its frame was
shown, and passed its object's law under that frame's facts.** Under
apply-at-return, with own-object writes and re-entry refused, no frame reads a
write of a frame still below it on the stack and no write is lost: the
frame-conflict abort of decision D1 has nothing left to catch (Scribe note D4). -/
theorem invocation_writes_from_view {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height : Nat} {request : InvokeRequest} (invoked : Invocation config snapshot height request) :
    ∀ w ∈ invoked.journal.writes, w.before = w.viewed ∧
      w.record.judge w.facts (some w.before.value) w.after.value = .ok () := by
  obtain ⟨_, _, ⟨new, writes, fresh⟩, _⟩ :=
    exec_invariant config snapshot height request.authority (invokeTransaction request) _ [] _ _ _ _ _ _ invoked.execExact (by simp)
      (by intro _ _ h; cases h) (by intro _ h; cases h)
  intro w member
  rw [writes] at member
  simp only [Journal.start, List.nil_append] at member
  exact ⟨(fresh w member).1, (fresh w member).2.1⟩

/-- **Active-frame view stability** (GPT-6 row A). A call subtree entered from any stack leaves
the state of every object on that stack exactly as it was, and every write a frame returns is
applied to exactly the state that frame was shown at its entry. So between a frame's entry and its
`frameReturn`, no descendant changes the frame's own object's state. `frameReturn` applies edits to
the CURRENT state, so it is the re-entry guard that buys this: no descendant may be a frame of an
object on the stack. Remove the guard and this theorem goes red (the DAO mutant: bank 40 / thief 60,
journey C5). -/
theorem active_frame_view_stability {rootBytes : Bytes → Digest} (config : Config) (snapshot : Snapshot rootBytes)
    (height : Nat) (authority : Authority) (turn : TransactionId) {fuel : Nat} {stack : List Ctx} {call : CallPlan}
    {journal journal' : Journal} {ticks left : Nat} {result : Data}
    (ran : exec config snapshot height authority turn fuel stack (.enter call) journal ticks = .ok (result, journal', left))
    (distinct : (stack.map (·.object)).Nodup) (read : ObjectsRead config snapshot journal) :
    (∀ ctx ∈ stack, journal'.lookup ctx.object = journal.lookup ctx.object) ∧
    ∃ new, journal'.writes = journal.writes ++ new ∧ ∀ w ∈ new, w.before = w.viewed := by
  obtain ⟨_, kept, ⟨new, writes, fresh⟩, _⟩ := exec_invariant config snapshot height authority turn fuel stack _
    journal ticks result journal' left ran distinct (by intro _ _ h; cases h) read
  exact ⟨fun ctx member => kept ctx member, new, writes, fun w member => (fresh w member).1⟩

/-- **Every frame write of an admitted invocation is made under the pin of its own object**:
the facts it was judged under name the package the written object's record pins, so the
object's pin clause (`ObjectRecord.pinClause`) accepts it (`pinClause_accepts_run`), and a
frame of another package would be refused there. The artifact is derived from the frame
(`Ctx.facts`), carried through the executor by `exec_invariant`. -/
theorem invocation_writes_pinned {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height : Nat} {request : InvokeRequest} (invoked : Invocation config snapshot height request) :
    ∀ w ∈ invoked.journal.writes, w.facts.artifact = some w.record.activePin.value := by
  obtain ⟨_, _, ⟨new, writes, fresh⟩, _⟩ :=
    exec_invariant config snapshot height request.authority (invokeTransaction request) _ [] _ _ _ _ _ _ invoked.execExact (by simp)
      (by intro _ _ h; cases h) (by intro _ h; cases h)
  intro w member
  rw [writes] at member
  simp only [Journal.start, List.nil_append] at member
  exact (fresh w member).2.2

/-- **Every post of a journal is the state image of an object the journal holds**:
the state cell of one of its entries, at that entry's own coordinate. -/
theorem Journal.posts_state {rootBytes : Bytes → Digest} (journal : Journal) (config : Config)
    (snapshot : Snapshot rootBytes) :
    ∀ post ∈ journal.posts config snapshot, ∃ entry ∈ journal.entries, ∃ state,
      post = postAt snapshot (stateCell config.domain entry.object) (stateImage entry.object state) := by
  intro post member
  simp only [Journal.posts, List.mem_filterMap] at member
  obtain ⟨entry, entryIn, made⟩ := member
  split at made
  · cases found : entry.current with
    | none => simp [found] at made
    | some state =>
      simp only [found, Option.map_some, Option.some.injEq] at made
      exact ⟨entry, entryIn, state, made.symm⟩
  · cases made

/-- **What an invocation posts**: the Book, or the state cell of an object its
call tree read from the snapshot (the premise of the checkpoint invariant's
`state_post_safe`). -/
theorem Invocation.posts_shape {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height : Nat} {request : InvokeRequest} (invoked : Invocation config snapshot height request) :
    ∀ post ∈ invoked.posts, post = invoked.posted.write config snapshot ∨
      (∃ object current state, readState config snapshot object = .ok current ∧
        post = postAt snapshot (stateCell config.domain object) (stateImage object state)) ∨
      ∃ cell role key body, role ≠ .record ∧ bodyOf .package (snapshot.canonicalBytes cell) = none ∧
        post = postAt snapshot cell (image role key body) := by
  obtain ⟨read, _⟩ :=
    exec_invariant config snapshot height request.authority (invokeTransaction request) _ [] _ _ _ _ _ _ invoked.execExact (by simp)
      (by intro _ _ h; cases h) (by intro _ h; cases h)
  rw [invoked.postsExact]
  intro post member
  rcases List.mem_append.mp member with inJournal | isBook
  rcases List.mem_append.mp inJournal with inJournal | inMail
  · right; left
    simp only [Journal.posts, List.mem_filterMap] at inJournal
    obtain ⟨entry, entryIn, made⟩ := inJournal
    obtain ⟨⟨current, readOk⟩, _⟩ := read entry entryIn
    split at made
    · cases found : entry.current with
      | none => simp [found] at made
      | some state =>
        simp only [found, Option.map_some, Option.some.injEq] at made
        exact ⟨entry.object, current, state, readOk, made.symm⟩
    · cases made
  · right; right; exact invoked.mail.posts_shape post inMail
  · left; simpa using isBook

#assert_axioms Journal.posts_state
#assert_axioms Invocation.posts_shape
#assert_axioms touch_read
#assert_axioms frameReturn_read
#assert_axioms runCounted_outcome
#assert_axioms runCounted_left_le
#assert_axioms reentry_refused
#assert_axioms touch_spec
#assert_axioms lookup_install_ne
#assert_axioms frameReturn_spec
#assert_axioms exec_invariant
#assert_axioms invocation_reentry_free
#assert_axioms invocation_writes_from_view
#assert_axioms active_frame_view_stability
#assert_axioms invocation_writes_pinned
#assert_axioms Ctx.facts_artifact
#assert_axioms Invocation.conserves
#assert_axioms Mail.posts_shape
#assert_axioms Mail.inboxes_lawful

end Minidregg.Kernel.ObjectiveCall
