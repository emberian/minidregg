/- Synchronous cross-object `call` (OB7): a signed invocation runs a method of
an object's pinned package, and that method may call methods of other objects
in the same turn, depth-first, each callee on its own pinned package.

**What a method is.** A declaration of the entry module of the package an object
pins (`ObjectRecord.pin`, the published pair of `Kernel.ObjectiveActivity`),
lowered by the kernel's own front end with that declaration selected
(`loadMethod`: the pinned sources, replayed, never an offered core). Its type is

    method(view: {version: Nat, state: S}, args: X) -> Activity<P, R, {result: A, write: W}>

where the Plan type `P` has labels among `call | send | stop | cancel` and the
response type `R` among `returned | queued | acked`. A method can therefore yield
nothing but a call, a send or a control of a message it sent, each answered in the
same turn: no frame ever suspends across turns (the
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
  a nested frame carries it ONLY through a scoped grant (v2) of the invocation
  that admits it: the grant names (callee, method) and binds the code the callee
  runs (its `activePin`), the call's arguments (an exact digest, or a recipient
  field and/or a cumulative cap on a Nat field) and optionally the direct caller;
  each such frame spends one use and is recorded as a `Delegation`. A grant that
  names the frame but does not admit it refuses the call tree by name
  (`grantMismatch`, or `grantSpent` when its uses are gone). Without a grant
  naming it the subject slot is absent and every law atom reading it fails
  closed: the signer's authority does not flow to callees it did not grant
  (Daml's non-transitive delegation; Pact's scoped, counted capabilities).
  `invocation_delegated_authority`: every frame receiving delegated authority
  has a matching unconsumed authorization. Delegation is not consent: the
  frame's write is still judged by its object's law. `request/caller` names the
  calling object, so a callee's law can admit chosen callers (an object's facet,
  as a clause).

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
(`Journal.outbox`, in order) become its MAIL (`postMail`). A send to an object names
a method its delivery can run (`Deliverable`, decided before anything is escrowed:
the method loads there, and its Plan is within `call`, or within `call | send` when the
message carries a CONTINUATION ALLOWANCE covering an onward send within the depth bound
(`Inbox.Message.continues`); else `notDeliverable`, `continuationDepth`, `notCallable`, ...;
`Invocation.sends_deliverable`). A send may carry an `allowance` (`send {to, method, args,
allowance}`, absent = 0): escrowed with its postage, it is the only money the delivered
method may send onward with (`ObjectiveSend.continueMessage`); an invocation's sends carry
in total at most the `allowance` its signer declared (`allowanceExceeded`). Each message is
pushed onto the per-(sender, target) inbox, bounded at `Inbox.bound` (a full
queue refuses the turn by name, `queueFull`), with its reply slot opened (decided
only by the message's delivery, `AnswerSlot.Decider.delivery`), and its postage
(the public price of the invocation's declared `postage` envelope, the envelope
its delivery runs under) moved from the invocation's account into the purse of
the queue holding it. Every inbox and slot the mail writes is a cell the turn
read: its post is a lawful change (`Inbox.Lawful`) of what the cell held.

**Stop-waiting is not cancel-if-queued (GPT-6 row F).** A frame may also yield
`stop {slot}` or `cancel {slot}` naming the reply slot of a message its OBJECT sent
(the authority: the inbox the slot answers to has that object as its sender, else
`notSender`), answered `acked {slot}` at the yield and applied when the turn commits,
after all its sends (`postControls`, `Mail.control`). `cancel` withdraws a message that
is still queued (`Inbox.Step.withdraw`: the others keep their order), refunds its
postage and that of every send pipelined on its slot (`cancelRefunds`, exactly:
`cancelRefunds_escrow`, `Mail.control_cancel_refunds`), and decides the slot
`cancelled`; a message already delivered is left alone (a no-op that refunds nothing).
`stop` keeps the message queued, refunds the pipelined sends and unwatches the slot,
which then takes no pipelined send (`notPipelinable`) and is retired by its delivery
(`ObjectiveSend.replyPost`); a slot already decided it retires at once.

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

/-- **A call frame's limits are its segment limits**: every frame is entered at the method's
`initial` state, whose heap is empty, so the absolute `config.limits` the frame runs under (at entry
and at every resume, `runCounted config.limits`) equal the room-past-the-start `segmentLimits` an
activity segment from that state would get. A frame never starts from a non-empty heap: its
resumes continue its own run, they do not restart a segment. -/
theorem frame_limits_are_segment_limits (config : Config) (term : _) :
    segmentLimits config (initial term) = config.limits := by
  simp [segmentLimits, ObjectiveBendDemandCollect.limitsPast, initial]

/-! ## Refusals -/

/-- The field a grant naming a frame's (object, method) refused it on. -/
inductive GrantField where
  | code
  | caller
  | args
  | cap
  deriving DecidableEq, Repr

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
  /-- A send names a method whose Plan type admits `send` while the message carries no
  continuation allowance covering an onward send (`Inbox.Message.continues`): a delivered
  method spends only its message's allowance, so the send is refused at the interface,
  before anything is escrowed (`Mail.send`, `Deliverable`). -/
  | notDeliverable (target : Nat) (method : String) (reason : String)
  /-- A send to a sending method at the depth bound (`Inbox.continuationDepth`): its onward
  sends would be one hop deeper. Also the backstop of a delivery whose message is there. -/
  | continuationDepth (limit : Nat)
  /-- A delivery's method sent more than `Inbox.fanOut` messages onward. -/
  | fanOut (limit : Nat)
  /-- Onward sends that would escrow `needed` while the allowance holds `held`: a delivered
  method's out of its message's allowance, an invocation's allowances out of the `allowance`
  its signer declared. -/
  | allowanceExceeded (needed held : Nat)
  /-- A send whose message would not fit what its storage deposit is charged for: an id that
  is not a 256-bit value or a deposit of 8 octets or more (`Inbox.chargedBytes_covers`). -/
  | messageWide (id : Nat)
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
  /-- A grant names (target, method) but does not admit the frame: its code, its caller, its
  arguments or its cumulative cap (`spendGrant`). The whole call tree co-fails. -/
  | grantMismatch (target : Nat) (method : String) (field : GrantField)
  /-- A `stop` or `cancel` names no delivery slot (no such slot, or a subject's). -/
  | notControllable (slot : Nat)
  /-- A `stop` or `cancel` of a slot whose message another object sent: only the sending
  object's frames control a message's slot. -/
  | notSender (slot sender : Nat)
  /-- A delivery slot whose activity cell is not the inbox holding its message (or whose
  open message is missing from it). -/
  | slotInbox (slot : Nat) (reason : String)
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

/-- The Plan labels a call frame may yield, every one answered in the same turn: a call
(`returned`), a send (`queued`), and the two controls of a message the frame's object sent
(`stop`, `cancel`, both `acked`; row F). -/
def framePlans : List String := ["call", "send", "stop", "cancel"]

/-- The responses a call frame is resumed with. -/
def frameResponses : List String := ["returned", "queued", "acked"]

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
            else .error (.notCallable target method "its response type is not within `returned | queued | acked`")
          else .error (.notCallable target method
            "its Plan type is not within `call | send | stop | cancel`: a method that awaits is not callable")
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

/-- A send a frame yields: `send {to, method, args, allowance?}`. -/
structure SendPlan where
  destination : Destination
  method : String
  args : Data
  /-- The continuation allowance the message carries (absent: 0). -/
  allowance : Nat

/-- The two controls of a message's sender over the message's reply slot (GPT-6 row F:
stop-waiting is not cancel-if-queued). -/
inductive ControlKind where
  /-- Stop waiting: the pipelined sends are refunded, nothing more may be pipelined, the
  message stays queued and is delivered as ever; its delivery retires the slot. A slot
  already decided is retired at once. -/
  | stop
  /-- Cancel if queued: a message still queued is withdrawn and refunded (with its
  pipelined sends) and its slot decided `cancelled`; a message already delivered is left
  as it is (a no-op that refunds nothing). -/
  | cancel
  deriving DecidableEq, Repr

inductive Yield where
  | call (plan : CallPlan)
  | send (plan : SendPlan)
  /-- `stop {slot}` / `cancel {slot}`. -/
  | control (kind : ControlKind) (slot : Digest)

/-- The send of `send {to, method, args, allowance?}`, its allowance decoded. -/
def decodeSend (target : Nat) (method : String) (fields : List (String × Data)) (allowance : Nat) :
    Except CallRefusal Yield :=
  match fieldOf fields "to", fieldOf fields "method", fieldOf fields "args" with
  | some (.variant "object" (.natural object)), some (.label name), some args =>
    .ok (.send ⟨.object object, name, args, allowance⟩)
  | some (.variant "slot" (.natural slot)), some (.label name), some args =>
    .ok (.send ⟨.slot ⟨slot⟩, name, args, allowance⟩)
  | _, _, _ => .error (.callShape target method "send needs to (object Nat | slot Nat), method (String) and args")

def decodeYield (target : Nat) (method : String) : Data → Except CallRefusal Yield
  | .variant "call" (.record fields) =>
    match fieldOf fields "target", fieldOf fields "method", fieldOf fields "args" with
    | some (.natural object), some (.label name), some args => .ok (.call ⟨⟨object⟩, name, args⟩)
    | _, _, _ => .error (.callShape target method "call needs target (Nat), method (String) and args")
  | .variant "send" (.record fields) =>
    match fieldOf fields "allowance" with
    | none => decodeSend target method fields 0
    | some (.natural allowance) => decodeSend target method fields allowance
    | some _ => .error (.callShape target method "a send's allowance is a Nat")
  | .variant "stop" (.record fields) =>
    match fieldOf fields "slot" with
    | some (.natural slot) => .ok (.control .stop ⟨slot⟩)
    | _ => .error (.callShape target method "stop needs slot (Nat)")
  | .variant "cancel" (.record fields) =>
    match fieldOf fields "slot" with
    | some (.natural slot) => .ok (.control .cancel ⟨slot⟩)
    | _ => .error (.callShape target method "cancel needs slot (Nat)")
  | _ => .error (.callShape target method "a frame yields only `call`, `send`, `stop` or `cancel`")

/-- The response a frame is resumed with after a send: its message id, which is
also its reply slot's name. -/
def queuedData (id : Digest) : Data := .variant "queued" (.record [("slot", .natural id.value)])

/-- The response a frame is resumed with after a `stop` or `cancel`: acknowledged at the
yield; its effect is decided when the turn commits (`postControls`), against the state
then (a message delivered before the cancel commits is not withdrawn). -/
def ackedData (slot : Digest) : Data := .variant "acked" (.record [("slot", .natural slot.value)])

/-- The response a frame is resumed with after its callee returned. -/
def returnedData (result : Data) : Data := .variant "returned" (.record [("result", result)])

/-- A frame's return: `{result, write}`. -/
def decodeReturn (target : Nat) (method : String) : Data → Except CallRefusal (Data × Data)
  | .record fields =>
    match fieldOf fields "result", fieldOf fields "write" with
    | some result, some write => .ok (result, write)
    | _, _ => .error (.frameFault target method "a method returns {result, write}")
  | _ => .error (.frameFault target method "a method returns {result, write}")

/-! ### Grants (v2): what a delegation may be used for

A grant lends the signer's authority to nested frames, and binds WHAT it lends it to: the
target object and method, the CODE the target runs (its `activePin`: a frame of the target
running any other package is not granted), the ARGUMENTS (an exact digest of their canonical
bytes, or a bounded constraint: a recipient field's value and/or a cumulative cap on a Nat field;
no constructor admits every argument), optionally the frame's DIRECT CALLER, and a count of uses.

Matching (`spendGrant`): a frame whose (object, method) no grant names is ungranted (subject none,
today's rule: delegation is opt-in). Among the grants naming it, the first that admits the frame
(code, caller, args, a use left, the cap) is spent and recorded as a `Delegation`. If grants name
it but none admits it, the call tree is REFUSED BY NAME: `grantSpent` when the first naming grant
is exhausted, else `grantMismatch` with the first field it fails. A mismatch is never a silent
downgrade to a subjectless frame (that would render a mismatch as a law refusal, or let a law that
ignores the subject commit it). -/

/-- The part of a call's arguments at a path of record field names (`[]`: the arguments). -/
def argsAt : List String → Data → Option Data
  | [], args => some args
  | name :: rest, .record fields => (fieldOf fields name).bind (argsAt rest)
  | _ :: _, _ => none

/-- The digest a `.exact` grant names: the canonical bytes of the arguments. -/
def argsDigest (args : Data) : Digest := tagged "DREGG/OBJECTIVE/CALL/GRANT-ARGS/v1" (dataBytes args)

/-- What a grant admits of a frame's arguments. -/
inductive ArgsBound where
  /-- Exactly the arguments whose canonical bytes have this digest (`argsDigest`). -/
  | exact (digest : Digest)
  /-- The arguments at `path` encode (`dataBytes`) to `value`; with `cap = some (amount, limit)` the
  Nat at `amount` is also charged against `limit` across the grant's uses. -/
  | recipient (path : List String) (value : List UInt8) (cap : Option (List String × Nat))
  /-- The Nat at `path` is charged against `limit`, cumulatively across the grant's uses. -/
  | capped (path : List String) (limit : Nat)
  deriving DecidableEq, Repr

/-- The cumulative cap of a bound: the charged path and the limit. -/
def ArgsBound.cap : ArgsBound → Option (List String × Nat)
  | .exact _ => none
  | .recipient _ _ cap => cap
  | .capped path limit => some (path, limit)

/-- What one use charges: the Nat at the capped path (0 without a cap; none: no Nat there). -/
def ArgsBound.amount (bound : ArgsBound) (args : Data) : Option Nat :=
  match bound.cap with
  | none => some 0
  | some (path, _) => match argsAt path args with
    | some (.natural amount) => some amount
    | _ => none

/-- The value constraint of a bound (the cap is checked against the uses, `Grant.judge`). -/
def ArgsBound.admits : ArgsBound → Data → Bool
  | .exact digest, args => decide (argsDigest args = digest)
  | .recipient path value _, args => decide ((argsAt path args).map dataBytes = some value)
  | .capped _ _, _ => true

/-- A scoped grant (v2): the signer lends its authority to at most `uses` frames of `method` on
`object` running `code`, whose arguments `args` admits, entered directly by `caller` (when set). -/
structure Grant where
  object : Nat
  method : String
  code : Digest
  args : ArgsBound
  caller : Option Nat
  uses : Nat
  deriving DecidableEq, Repr

/-- A frame that received delegated authority: the grant (its index in the invocation's grants)
and what it was spent on, with the amount it charged the grant's cap. -/
structure Delegation where
  grant : Nat
  object : Nat
  method : String
  code : Digest
  args : Data
  caller : Option Nat
  amount : Nat

/-- The delegations of grant `index`. -/
def usesOf (delegations : List Delegation) (index : Nat) : List Delegation :=
  delegations.filter (fun d => d.grant == index)

/-- What the delegations of grant `index` charged its cap. -/
def chargedOf (delegations : List Delegation) (index : Nat) : Nat :=
  ((usesOf delegations index).map Delegation.amount).sum

/-- A grant's caller restriction holds of a frame's direct caller (none: any caller). -/
def callerOk : Option Nat → Option Nat → Bool
  | none, _ => true
  | some restriction, caller => decide (caller = some restriction)

/-- One grant's judgment of a frame it names. -/
inductive Verdict where
  | admit (amount : Nat)
  | mismatch (field : GrantField)
  | spent

/-- Grant `index` judges a frame of (code, args, caller), given the turn's delegations so far. -/
def Grant.judge (grant : Grant) (used : List Delegation) (index : Nat) (code : Digest) (args : Data)
    (caller : Option Nat) : Verdict :=
  if grant.code ≠ code then .mismatch .code
  else if callerOk grant.caller caller = false then .mismatch .caller
  else if grant.args.admits args = false then .mismatch .args
  else match grant.args.amount args with
    | none => .mismatch .args
    | some amount =>
      if grant.uses ≤ (usesOf used index).length then .spent
      else match grant.args.cap with
        | none => .admit amount
        | some (_, limit) => if chargedOf used index + amount ≤ limit then .admit amount else .mismatch .cap

/-- The refusal of the first grant that named the frame and did not admit it. -/
def Verdict.refusal (object : Nat) (method : String) : Verdict → Option CallRefusal
  | .admit _ => none
  | .mismatch field => some (.grantMismatch object method field)
  | .spent => some (.grantSpent object method)

/-- Scan the grants from index `index`; `first` is the refusal of the first grant that named the
frame and did not admit it. -/
def spendFrom (used : List Delegation) (object : Nat) (method : String) (code : Digest) (args : Data)
    (caller : Option Nat) : List Grant → Nat → Option CallRefusal → Except CallRefusal (Option Delegation)
  | [], _, none => .ok none
  | [], _, some reason => .error reason
  | grant :: rest, index, first =>
    if grant.object = object ∧ grant.method = method then
      match grant.judge used index code args caller with
      | .admit amount => .ok (some ⟨index, object, method, code, args, caller, amount⟩)
      | verdict => spendFrom used object method code args caller rest (index + 1)
          (first.orElse fun _ => verdict.refusal object method)
    else spendFrom used object method code args caller rest (index + 1) first

/-- **Spend a grant on a nested frame**: `none` (no grant names (object, method): ungranted), the
delegation of the first grant that admits it, or the refusal of the first that named it. -/
def spendGrant (grants : List Grant) (used : List Delegation) (object : Nat) (method : String) (code : Digest)
    (args : Data) (caller : Option Nat) : Except CallRefusal (Option Delegation) :=
  spendFrom used object method code args caller grants 0 none

/-- A grant authorizes a delegation: it names its object and method, its code, admits its
arguments, its caller restriction holds, and the delegation's amount is what its cap charges. -/
def Grant.Authorizes (grant : Grant) (d : Delegation) : Prop :=
  grant.object = d.object ∧ grant.method = d.method ∧ grant.code = d.code ∧
    callerOk grant.caller d.caller = true ∧ grant.args.admits d.args = true ∧
    grant.args.amount d.args = some d.amount

/-- **Every delegation has a matching unconsumed authorization**: each names a grant that
authorizes it, no grant is used more than `uses` times, and the uses of a capped grant charge at
most its limit in sum. -/
def Authorized (grants : List Grant) (delegations : List Delegation) : Prop :=
  (∀ d ∈ delegations, ∃ grant, grants[d.grant]? = some grant ∧ grant.Authorizes d) ∧
    ∀ index grant, grants[index]? = some grant →
      (usesOf delegations index).length ≤ grant.uses ∧
      ∀ path limit, grant.args.cap = some (path, limit) → chargedOf delegations index ≤ limit

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
  /-- The frame's arguments. -/
  args : Data
  /-- The delegation that lent the frame the signer's authority (none: the root, or ungranted). -/
  delegation : Option Delegation

/-- A control a frame of this turn yielded: the yielding frame's object, the kind, the slot. -/
structure Control where
  sender : Nat
  kind : ControlKind
  slot : Digest
  deriving DecidableEq, Repr

/-- A send a frame of this turn made. -/
structure Outgoing where
  /-- `Inbox.sendId turn index`. -/
  id : Digest
  /-- The sending frame's object. -/
  sender : Nat
  destination : Destination
  method : String
  args : Data
  /-- The continuation allowance its message carries. -/
  allowance : Nat

structure Journal where
  entries : List Entry
  /-- The invocation's grants, as signed (never changed: their uses are the delegations). -/
  grants : List Grant
  /-- Every frame that received delegated authority, in entry order (`spendGrant`). -/
  delegations : List Delegation
  /-- Every frame entered, in order: the objects on the stack at its entry,
  innermost first (the frame's own object at the head). -/
  frames : List (List Nat)
  writes : List Written
  /-- Every send, in the order the frames made them. -/
  outbox : List Outgoing
  /-- The turn's extraction tick allowance still unspent: the envelope declares it
  (`Capacity.extractTicks`), and every Plan or result extraction of the call tree draws the
  deployment's extraction budget (`planBudget.ticks`) from it, refused by name when it is
  short (`extractUncovered`). -/
  extracts : Nat
  /-- Every `stop`/`cancel`, in the order the frames yielded them. They are applied after
  ALL the turn's sends (`postControls` after `postMail`), so a turn may cancel a message it
  sent itself. -/
  controls : List Control

def Journal.start (grants : List Grant) (extracts : Nat) : Journal := ⟨[], grants, [], [], [], [], extracts, []⟩

/-- **Debit an extraction's actual tick spend** from the turn's allowance, refused by name when
the allowance left is below it. The spend is deterministic (the extraction's own tick count),
so re-execution agrees; an extraction never reserves the deployment's per-extraction ceiling. -/
def Journal.draw (journal : Journal) (spent : Nat) : Except CallRefusal Journal :=
  if journal.extracts < spent then .error (.kernel (.extractUncovered spent journal.extracts))
  else .ok { journal with extracts := journal.extracts - spent }

theorem Journal.draw_ok {journal journal' : Journal} {spent : Nat} (drawn : journal.draw spent = .ok journal') :
    journal' = { journal with extracts := journal.extracts - spent } := by
  unfold Journal.draw at drawn
  split at drawn
  · cases drawn
  · cases drawn; rfl

/-- **Two draws within the allowance both succeed** (a frame that yields once and finishes, each
extraction debited what it spent). -/
theorem Journal.draw_two (journal : Journal) {first second : Nat}
    (within : first + second ≤ journal.extracts) :
    (journal.draw first >>= fun j => j.draw second) =
      .ok { journal with extracts := journal.extracts - first - second } := by
  have one : ¬ journal.extracts < first := by omega
  have two : ¬ journal.extracts - first < second := by omega
  simp [Journal.draw, one, two, bind, Except.bind]

/-- **An under-declared allowance is refused by name**, with the spend it could not cover. -/
theorem Journal.draw_short (journal : Journal) {spent : Nat} (short : journal.extracts < spent) :
    journal.draw spent = .error (.kernel (.extractUncovered spent journal.extracts)) := by
  simp [Journal.draw, short]

/-- The refuted design (planted pole): reserving the per-extraction CEILING at every extraction
refuses a frame that yields once and finishes within an allowance that covers both actual spends,
whenever the ceiling is more than half the allowance. -/
theorem ceiling_reservation_refuses (journal : Journal) {ceiling first second : Nat}
    (within : first + second ≤ journal.extracts) (big : journal.extracts < 2 * ceiling) :
    ∃ reason, (journal.draw ceiling >>= fun j => j.draw ceiling) = .error reason := by
  by_cases h : journal.extracts < ceiling
  · exact ⟨.kernel (.extractUncovered ceiling journal.extracts), by simp [Journal.draw, h, bind, Except.bind]⟩
  · have two : journal.extracts - ceiling < ceiling := by omega
    exact ⟨.kernel (.extractUncovered ceiling (journal.extracts - ceiling)),
      by simp [Journal.draw, h, two, bind, Except.bind]⟩

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
  /-- The call's arguments. -/
  args : Data
  /-- The delegation that lent this frame the signer's authority (`spendGrant`). -/
  delegation : Option Delegation

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
            writes := journal.writes ++ [⟨ctx.object, ctx.method, ctx.record, ctx.facts, ctx.view, before, after,
              ctx.args, ctx.delegation⟩] }
    | _ => .error (.stateMissing ctx.object.value)

/-! ## The executor -/

/-- **A frame's authority**: the root frame carries the signer's subject; a nested frame carries it
only through a grant that admits it (`spendGrant`, against the code its target runs and the
call's arguments and direct caller), and then records the delegation; a nested frame no grant
names carries none; a grant that names it and does not admit it refuses the call tree. -/
def frameAuthority (authority : Authority) (stack : List Ctx) (journal : Journal) (call : CallPlan) (code : Digest) :
    Except CallRefusal (Option SubjectId × Option Delegation) :=
  match stack with
  | [] => .ok (authority.signer, none)
  | _ :: _ =>
    match spendGrant journal.grants journal.delegations call.target.value call.method code call.args
        (callerOf authority stack) with
    | .error reason => .error reason
    | .ok none => .ok (none, none)
    | .ok (some d) => .ok (authority.signer, some d)

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
    match frameAuthority authority stack journal call entry.record.activePin with
    | .error reason => .error reason
    | .ok (subject, delegation) =>
    match loadMethod config call.target.value (packageBytes config snapshot entry.record.activePin) entry.record.activePin
        call.method (viewData view) call.args with
    | .error reason => .error reason
    | .ok program =>
    let ctx : Ctx := ⟨call.target, call.method, entry.record, program.applied.assumptions, program.responseType,
      view, subject, height, callerOf authority stack, call.args, delegation⟩
    let journal : Journal := ⟨journal.entries, journal.grants, journal.delegations ++ delegation.toList,
      journal.frames ++ [call.target.value :: stack.map (·.object.value)], journal.writes, journal.outbox,
      journal.extracts, journal.controls⟩
    exec config snapshot height authority turn fuel (ctx :: stack) (.run (initial program.applied.erase)) journal ticks
  | _ + 1, [], .run _, _, _ => .error .exhausted
  | fuel + 1, ctx :: rest, .run state, journal, ticks =>
    match runCounted config.limits ticks state with
    | (.yielded _ yielded, left) =>
      match ObjectiveBendDemandData.yieldedPlan config.limits config.planBudget yielded with
      | .error (failure, _) => .error (.frameFault ctx.object.value ctx.method s!"plan extraction: {reprStr failure}")
      | .ok extracted =>
      match journal.draw (config.planBudget.ticks - extracted.remaining.ticks) with
      | .error reason => .error reason
      | .ok journal =>
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
            { journal with outbox := journal.outbox ++ [⟨id, ctx.object.value, send.destination, send.method, send.args, send.allowance⟩] }
            left
      | .ok (.control kind slot) =>
        match typeData ctx.assumptions config.typeFuel (ackedData slot) ctx.responseType with
        | none => .error (.resultType ctx.object.value ctx.method)
        | some _ =>
        match resume (ackedData slot).term yielded with
        | none => .error (.frameFault ctx.object.value ctx.method "resume")
        | some next => exec config snapshot height authority turn fuel (ctx :: rest) (.run next)
            { journal with controls := journal.controls ++ [⟨ctx.object.value, kind, slot⟩] }
            left
    | (.finished _ finished, left) =>
      match ObjectiveBendDemandData.complete config.limits config.planBudget finished with
      | .error (failure, _) => .error (.frameFault ctx.object.value ctx.method s!"result extraction: {reprStr failure}")
      | .ok out =>
      match journal.draw (config.planBudget.ticks - out.remaining.ticks) with
      | .error reason => .error reason
      | .ok journal =>
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

/-- A delivery slot this turn's controls CLOSE: decided `cancelled` (`decided = some slot`,
a cancel of a still-queued message) or retired (`none`: a stop of a decided slot, or a
cancel of an unwatched one). Its cell was read as a slot and holds no package. -/
structure ClosedSlot {rootBytes : Bytes → Digest} (config : Config) (snapshot : Snapshot rootBytes) where
  name : Digest
  clean : bodyOf .package (snapshot.canonicalBytes (AnswerSlot.cell config.domain name)) = none
  slotted : ∀ payload, payloadOf (snapshot.canonicalBytes (AnswerSlot.cell config.domain name)) = some payload →
    payload.role = .slot
  decided : Option AnswerSlot.Slot
  named : ∀ slot, decided = some slot → slot.name = name

/-- The post of a closed slot: its decided image, or the retired image. -/
def ClosedSlot.post {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    (closed : ClosedSlot config snapshot) : Post :=
  match closed.decided with
  | some slot => slotPost config snapshot slot
  | none => slotRetire config snapshot closed.name

/-- Escrow a control returns: `amount` from the purse of the queue that held it to the
account that paid it. -/
structure Refund where
  purse : AccountId
  payer : AccountId
  amount : Nat
  deriving DecidableEq, Repr

structure Mail {rootBytes : Bytes → Digest} (config : Config) (snapshot : Snapshot rootBytes) where
  inboxes : List (HeldInbox config snapshot)
  slots : List (HeldSlot config snapshot)
  /-- The postage each queued message escrows, in order: the purse of the queue
  holding it (an inbox's, or the inbox holding the message a slot answers). -/
  credits : List (AccountId × Nat)
  /-- Every object a message was addressed to (read as an object; guarded). -/
  targets : List Nat
  /-- The slots this turn's controls closed (`Mail.control`). -/
  closed : List (ClosedSlot config snapshot)
  /-- The escrow this turn's controls return, in order. -/
  refunds : List Refund

def Mail.empty {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes} :
    Mail config snapshot := ⟨[], [], [], [], [], []⟩

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
    (mail : Mail config snapshot) (name : Digest) (sender : Nat) (inbox : CellId) :
    Except CallRefusal (HeldSlot config snapshot) :=
  let bytes := snapshot.canonicalBytes (AnswerSlot.cell config.domain name)
  if taken : (payloadOf bytes).isSome || isRetired bytes || mail.slots.any (fun held => held.name == name) then
    .error (.slotTaken name.value)
  else if clean : bodyOf .package bytes = none then
    have slotted : ∀ payload, payloadOf bytes = some payload → payload.role = .slot := by
      intro payload found
      simp [found] at taken
    .ok ⟨name, none, clean, slotted, ⟨name, inbox, .delivery name sender, 0, .opened, [], true⟩, rfl, rfl⟩
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

/-- The Plan labels the method a message is DELIVERED to may yield: calls, and sends only when
the message continues (`Inbox.Message.continues`: within the depth bound, its allowance
covering an onward send). A delivered message has no paying account but its own allowance,
so a method whose Plan admits `send` is refused at the interface for any other message. -/
def deliveredPlans (message : Inbox.Message) : List String :=
  if message.continues then ["call", "send"] else ["call"]

/-- **A method a message to `target` can be delivered to**, decided at the send from the
snapshot: `target` is an object with declared state, the message's arguments decode, the
method loads exactly as its delivery's root frame will (`loadMethod` on the record's
`activePin`, applied to the object's view and the arguments: the same front end, the same
type check), and its Plan type is within `deliveredPlans message`. -/
structure Deliverable {rootBytes : Bytes → Digest} (config : Config) (snapshot : Snapshot rootBytes)
    (target : Nat) (message : Inbox.Message) where
  private mk ::
  record : ObjectRecord
  recordExact : readObject config snapshot ⟨target⟩ = .ok (some record)
  view : ObjectState
  viewExact : readState config snapshot ⟨target⟩ = .ok (some view)
  args : Data
  argsExact : decodeDataBytes message.args = some args
  method : Method config record.activePin message.method (viewData view) args
  methodExact : loadMethod config target (packageBytes config snapshot record.activePin) record.activePin
    message.method (viewData view) args = .ok method
  callsOnly : labelsWithin method.applied.assumptions method.planType (deliveredPlans message) = true

/-- Decide `Deliverable`, refusing by name: `notAnObject`, `stateMissing` (an object with no
declared state: its delivery could not enter it), `argumentType` (arguments that do not
decode or type), `notCallable` (anything `loadMethod` refuses: an unknown method, a Plan that
awaits), `continuationDepth` (a sending method, the message at the depth bound),
`notDeliverable` (a sending method and an allowance that covers no onward send, or a Plan
that admits `stop`/`cancel`). -/
def deliverable {rootBytes : Bytes → Digest} (config : Config) (snapshot : Snapshot rootBytes)
    (target : Nat) (message : Inbox.Message) : Except CallRefusal (Deliverable config snapshot target message) :=
  match recordExact : readObject config snapshot ⟨target⟩ with
  | .error reason => .error (.kernel reason)
  | .ok none => .error (.notAnObject target)
  | .ok (some record) =>
  match viewExact : readState config snapshot ⟨target⟩ with
  | .error reason => .error (.kernel reason)
  | .ok none => .error (.stateMissing target)
  | .ok (some view) =>
  match argsExact : decodeDataBytes message.args with
  | none => .error (.argumentType target message.method)
  | some args =>
  match methodExact : loadMethod config target (packageBytes config snapshot record.activePin) record.activePin
      message.method (viewData view) args with
  | .error reason => .error reason
  | .ok method =>
    if callsOnly : labelsWithin method.applied.assumptions method.planType (deliveredPlans message) = true then
      .ok ⟨record, recordExact, view, viewExact, args, argsExact, method, methodExact, callsOnly⟩
    else if !labelsWithin method.applied.assumptions method.planType ["call", "send"] then
      .error (.notDeliverable target message.method "its Plan admits stop or cancel: a delivered method controls nothing")
    else if Inbox.continuationDepth ≤ message.depth then .error (.continuationDepth Inbox.continuationDepth)
    else .error (.notDeliverable target message.method
      "its Plan admits send and the message's allowance does not cover an onward send")

/-- **Queue one message.** To an object: the target method must be `Deliverable` (decided
before anything is escrowed: an object, with state, the method loads, its Plan within
`call`); the message is pushed onto the inbox (sender, target), refused `queueFull` at the
bound, and its reply slot is opened, decided only by its delivery. To a slot: the slot must
be an open delivery slot (the reply of a message in an inbox); the message is queued on it,
refused `slotQueueFull` at the bound. Its target is known only when that reply resolves, so
`Deliverable` is decided then, when `ObjectiveSend.forward` queues it into the RESOLVED
destination through this same function, and a refusal there refunds it. Either way its
postage is credited to the purse of the queue that holds it. -/
def Mail.send {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    (mail : Mail config snapshot) (message : Inbox.Message) :
    Destination → Except CallRefusal (Mail config snapshot)
  | .object target =>
    match deliverable config snapshot target message with
    | .error reason => .error reason
    | .ok _ =>
    match holdInbox config snapshot mail message.sender target with
    | .error reason => .error reason
    | .ok (held, others) =>
    match pushed : held.now.push message with
    | none => .error (.queueFull message.sender target)
    | some next =>
    match openSlot config snapshot mail message.id message.sender held.cell with
    | .error reason => .error reason
    | .ok slot =>
      have keeps := (Inbox.push_step pushed).keeps
      let updated : HeldInbox config snapshot :=
        ⟨held.sender, held.target, held.read, held.readExact, held.clean, next,
          held.lawful.snoc (Inbox.push_step pushed), ⟨keeps.1.trans held.ends.1, keeps.2.1.trans held.ends.2⟩⟩
      .ok { mail with
        inboxes := others ++ [updated]
        slots := mail.slots ++ [slot]
        credits := mail.credits ++ [(held.cell.value, message.escrow)]
        targets := mail.targets ++ [target] }
  | .slot name =>
    match holdSlot config snapshot mail name with
    | .error reason => .error reason
    | .ok (held, others) =>
      match held.now.decider with
      | .subject _ => .error (.notPipelinable name.value)
      | .delivery _ _ =>
        -- Its sender stopped waiting (`ControlKind.stop`): nothing more is pipelined on it.
        if !held.now.watched then .error (.notPipelinable name.value) else
        if held.now.queued.length < Inbox.bound then
          let updated : HeldSlot config snapshot :=
            ⟨held.name, held.read, held.clean, held.slotted, { held.now with queued := held.now.queued ++ [message] },
              held.named, held.opened⟩
          .ok { mail with
            slots := others ++ [updated]
            credits := mail.credits ++ [(held.now.activity.value, message.escrow)] }
        else .error (.slotQueueFull name.value)

/-- The message a send queues: its delivery runs under `postage`, whose public
price it escrows with the send's allowance, both refunded to `refund` if it is never
delivered; `depth` is its place in its continuation chain. -/
def messageOf (config : Config) (postage : Capacity) (refund : AccountId) (depth : Nat) (out : Outgoing) :
    Inbox.Message :=
  let bare : Inbox.Message := ⟨out.id, out.sender, out.method, dataBytes out.args, postage,
    config.tariff.workOf postage, refund, out.allowance, depth, 0⟩
  { bare with deposit := Inbox.storageDeposit config.storageRate bare }

/-- The mail of a turn's sends, in order. -/
def postMail {rootBytes : Bytes → Digest} (config : Config) (snapshot : Snapshot rootBytes)
    (postage : Capacity) (refund : AccountId) (depth : Nat) :
    Mail config snapshot → List Outgoing → Except CallRefusal (Mail config snapshot)
  | mail, [] => .ok mail
  | mail, out :: rest =>
    if !(messageOf config postage refund depth out).fits then .error (.messageWide out.id.value) else
    match mail.send (messageOf config postage refund depth out) out.destination with
    | .error reason => .error reason
    | .ok mail => postMail config snapshot postage refund depth mail rest

/-- One step of an admitted `postMail`: the message fits what its deposit covers, it is sent,
and the rest is posted from there. -/
theorem postMail_cons {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {postage : Capacity} {refund : AccountId} {depth : Nat} {mail next : Mail config snapshot}
    {out : Outgoing} {rest : List Outgoing}
    (ok : postMail config snapshot postage refund depth mail (out :: rest) = .ok next) :
    (messageOf config postage refund depth out).fits = true ∧
      ∃ mail', mail.send (messageOf config postage refund depth out) out.destination = .ok mail' ∧
        postMail config snapshot postage refund depth mail' rest = .ok next := by
  simp only [postMail] at ok
  split at ok
  · cases ok
  · rename_i fits
    split at ok
    · cases ok
    · rename_i mail' sent
      exact ⟨by simpa using fits, mail', sent, ok⟩


/-! ### The sender's controls: stop-waiting and cancel-if-queued (GPT-6 row F)

A frame's `stop {slot}` / `cancel {slot}` is acknowledged at the yield (`acked`) and takes
effect when the turn commits, after all its sends (`postControls`), against the state the
turn reads. The AUTHORITY is the sending object: the slot's activity cell is the inbox
holding its message, and that inbox's sender must be the yielding frame's object
(`notSender`). -/

/-- What a control finds at a slot name. -/
inductive Controlled {rootBytes : Bytes → Digest} (config : Config) (snapshot : Snapshot rootBytes) where
  /-- Retired, or closed by an earlier control of this turn: every control is a no-op. -/
  | gone
  /-- A delivery slot decided before this turn (read from the snapshot). -/
  | decided (slot : AnswerSlot.Slot) (closing : ClosedSlot config snapshot)
  /-- An open delivery slot: the one this turn holds, else read; and the other held slots. -/
  | held (slot : HeldSlot config snapshot) (others : List (HeldSlot config snapshot))

/-- The delivery slot a control names, by name: `notControllable` when there is none (never
a slot, or a subject's slot). -/
def controlSlot {rootBytes : Bytes → Digest} (config : Config) (snapshot : Snapshot rootBytes)
    (mail : Mail config snapshot) (name : Digest) : Except CallRefusal (Controlled config snapshot) :=
  if mail.closed.any (fun closed => closed.name == name) then .ok .gone else
  match mail.slots.find? (fun held => held.name == name) with
  | some held =>
    match held.now.decider with
    | .subject _ => .error (.notControllable name.value)
    | .delivery _ _ => .ok (.held held (mail.slots.filter (fun other => !(other.name == name))))
  | none =>
    if isRetired (snapshot.canonicalBytes (AnswerSlot.cell config.domain name)) then .ok .gone else
    match readExact : readSlot config snapshot name with
    | none => .error (.notControllable name.value)
    | some slot =>
      if named : slot.name = name then
        if clean : bodyOf .package (snapshot.canonicalBytes (AnswerSlot.cell config.domain name)) = none then
          have slotted : ∀ payload, payloadOf (snapshot.canonicalBytes (AnswerSlot.cell config.domain name)) =
              some payload → payload.role = .slot := by
            intro payload found
            by_contra wrong
            have empty : bodyOf .slot (snapshot.canonicalBytes (AnswerSlot.cell config.domain name)) = none := by
              simp [bodyOf, found, wrong]
            simp [readSlot, empty] at readExact
          match slot.decider with
          | .subject _ => .error (.notControllable name.value)
          | .delivery _ _ =>
            match opened : slot.phase with
            | .opened => .ok (.held ⟨name, some slot, clean, slotted, slot, named, opened⟩ mail.slots)
            | .decided _ _ => .ok (.decided slot ⟨name, clean, slotted, none, fun _ none_ => by cases none_⟩)
        else .error (.packageCell (AnswerSlot.cell config.domain name).value)
      else .error (.notControllable name.value)

/-- The inbox a delivery slot answers to (its `activity` cell), held: located by the
(sender, target) of the inbox this turn holds at that cell, else of the inbox read there,
and `slotInbox` unless that inbox's cell IS the activity cell. -/
def inboxEnds {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    (mail : Mail config snapshot) (activity : CellId) : Option (Nat × Nat) :=
  match mail.inboxes.find? (fun held => held.cell == activity) with
  | some held => some (held.sender, held.target)
  | none => match readInbox snapshot activity with
    | some (some inbox) => some (inbox.sender, inbox.target)
    | _ => none

def controlInbox {rootBytes : Bytes → Digest} (config : Config) (snapshot : Snapshot rootBytes)
    (mail : Mail config snapshot) (name : Digest) (activity : CellId) :
    Except CallRefusal (HeldInbox config snapshot × List (HeldInbox config snapshot)) :=
  match inboxEnds mail activity with
  | none => .error (.slotInbox name.value "its activity cell holds no inbox")
  | some (sender, target) =>
    match holdInbox config snapshot mail sender target with
    | .error reason => .error reason
    | .ok (held, others) =>
      if held.cell = activity then .ok (held, others)
      else .error (.slotInbox name.value "its activity cell is not its inbox's")

/-- The refunds of a cancel: the withdrawn message and every send pipelined on its slot,
each its whole escrow (postage and continuation allowance), from the purse of the inbox that
held them back to its payer. -/
def cancelRefunds (purse : AccountId) (message : Inbox.Message) (queued : List Inbox.Message) : List Refund :=
  (message :: queued).map fun refunded => ⟨purse, refunded.refund, refunded.escrow⟩

/-- The refunds of a stop: every send pipelined on the slot, each its whole escrow. -/
def stopRefunds (purse : AccountId) (queued : List Inbox.Message) : List Refund :=
  queued.map fun refunded => ⟨purse, refunded.refund, refunded.escrow⟩

/-- **Apply one control.** The authority check comes first wherever the slot is still there
(`notSender`); then:
* `stop` of an open slot: its pipelined sends are refunded, it is unwatched and empty
  (`AnswerSlot.stopWaiting`); the message stays queued.
* `stop` of a decided slot: the slot is retired. Its authority is the sender its decider
  names, since its inbox may already be retired.
* `cancel` of an open slot: its message is withdrawn from the inbox (`Inbox.Step.withdraw`;
  `slotInbox` if it is not there), the message and every pipelined send are refunded
  (`cancelRefunds`), and the slot is decided `cancelled` (`AnswerSlot.cancelDelivery`), or
  retired when nobody watches it.
* `cancel` of a decided slot (the message was delivered first): a no-op, nothing refunded.
* either, on a retired slot or one closed earlier in this turn: a no-op. -/
def Mail.control {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    (mail : Mail config snapshot) (height : Nat) (control : Control) : Except CallRefusal (Mail config snapshot) :=
  match controlSlot config snapshot mail control.slot with
  | .error reason => .error reason
  | .ok .gone => .ok mail
  | .ok (.decided slot closing) =>
    -- A decided slot's sender is named by its decider: its inbox may be retired already
    -- (an emptied inbox retains nothing, cv 01a113fe-1390).
    match slot.decider with
    | .subject _ => .error (.notControllable control.slot.value)
    | .delivery _ sender =>
    if sender ≠ control.sender then .error (.notSender control.slot.value control.sender) else
    match control.kind with
    | .cancel => .ok mail
    | .stop => .ok { mail with closed := mail.closed ++ [closing] }
  | .ok (.held held others) =>
    match controlInbox config snapshot mail control.slot held.now.activity with
    | .error reason => .error reason
    | .ok (inbox, inboxes) =>
    if inbox.sender ≠ control.sender then .error (.notSender control.slot.value control.sender) else
    let purse := held.now.activity.value
    match control.kind with
    | .stop =>
      match stopped : AnswerSlot.stopWaiting held.now with
      | .error _ => .error (.notControllable control.slot.value)
      | .ok now =>
        have same := AnswerSlot.stopWaiting_spec stopped
        let updated : HeldSlot config snapshot :=
          ⟨held.name, held.read, held.clean, held.slotted, now,
            by rw [same.2.2]; exact held.named, by rw [same.2.2]; exact held.opened⟩
        .ok { mail with
          slots := others ++ [updated]
          refunds := mail.refunds ++ stopRefunds purse held.now.queued }
    | .cancel =>
      match withdrawn : inbox.now.withdraw control.slot with
      | none => .error (.slotInbox control.slot.value "its open message is not queued in its inbox")
      | some (message, next) =>
      match cancelled : AnswerSlot.cancelDelivery held.now height with
      | .error _ => .error (.notControllable control.slot.value)
      | .ok decided =>
        have step := (Inbox.withdraw_step withdrawn).1
        have keeps := step.keeps
        let updated : HeldInbox config snapshot :=
          ⟨inbox.sender, inbox.target, inbox.read, inbox.readExact, inbox.clean, next, inbox.lawful.snoc step,
            ⟨keeps.1.trans inbox.ends.1, keeps.2.1.trans inbox.ends.2⟩⟩
        have named : decided.name = held.name := by
          rw [(AnswerSlot.cancelDelivery_spec cancelled).2.2]; exact held.named
        let closing : ClosedSlot config snapshot :=
          ⟨held.name, held.clean, held.slotted, if held.now.watched then some decided else none, by
            intro slot isSome
            split at isSome
            · cases isSome; exact named
            · cases isSome⟩
        .ok { mail with
          inboxes := inboxes ++ [updated]
          slots := others
          closed := mail.closed ++ [closing]
          refunds := mail.refunds ++ cancelRefunds purse message held.now.queued }

/-- The turn's controls, in order, after its sends. -/
def postControls {rootBytes : Bytes → Digest} (config : Config) (snapshot : Snapshot rootBytes) (height : Nat) :
    Mail config snapshot → List Control → Except CallRefusal (Mail config snapshot)
  | mail, [] => .ok mail
  | mail, control :: rest =>
    match mail.control height control with
    | .error reason => .error reason
    | .ok mail => postControls config snapshot height mail rest

theorem controlInbox_spec {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {mail : Mail config snapshot} {name : Digest} {activity : CellId} {held : HeldInbox config snapshot}
    {others : List (HeldInbox config snapshot)}
    (ok : controlInbox config snapshot mail name activity = .ok (held, others)) :
    held.cell = activity ∧ holdInbox config snapshot mail held.sender held.target = .ok (held, others) := by
  unfold controlInbox at ok
  split at ok
  · cases ok
  · rename_i sender target _
    split at ok
    · cases ok
    · rename_i pair hold
      split at ok
      · rename_i same
        cases ok
        refine ⟨same, ?_⟩
        have sides : held.sender = sender ∧ held.target = target := by
          unfold holdInbox at hold
          split at hold
          · rename_i found hit
            cases hold
            have hits := List.find?_some hit
            simp only [Bool.and_eq_true, beq_iff_eq] at hits
            exact hits
          · split at hold
            · cases hold
            · split at hold
              · split at hold
                · cases hold; exact ⟨rfl, rfl⟩
                · cases hold
              · cases hold
        rw [sides.1, sides.2]; exact hold
      · cases ok

/-- **What one control does to the mail**, case by case (`Mail.control`): nothing; a decided
slot retired (stop); an open slot unwatched with its pipelined sends refunded (stop); or a
still-queued message withdrawn from its sender's inbox, refunded with the sends pipelined
on it, its slot closed (cancel). The authority is in every case that changes anything: the
inbox the slot answers to has the controlling object as its sender. -/
theorem Mail.control_cases {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {mail next : Mail config snapshot} {height : Nat} {control : Control}
    (ok : mail.control height control = .ok next) :
    next = mail ∨
    (control.kind = .stop ∧ ∃ (slot : AnswerSlot.Slot) (closing : ClosedSlot config snapshot) (message : Digest),
      controlSlot config snapshot mail control.slot = .ok (.decided slot closing) ∧ closing.decided = none ∧
      slot.decider = .delivery message control.sender ∧
      next = { mail with closed := mail.closed ++ [closing] }) ∨
    (control.kind = .stop ∧ ∃ (held updated : HeldSlot config snapshot) (others : List (HeldSlot config snapshot))
      (inbox : HeldInbox config snapshot) (inboxes : List (HeldInbox config snapshot)),
      controlSlot config snapshot mail control.slot = .ok (.held held others) ∧
      controlInbox config snapshot mail control.slot held.now.activity = .ok (inbox, inboxes) ∧
      inbox.sender = control.sender ∧
      updated.read = held.read ∧ updated.now = { held.now with queued := [], watched := false } ∧
      next = { mail with
        slots := others ++ [updated]
        refunds := mail.refunds ++ stopRefunds held.now.activity.value held.now.queued }) ∨
    (control.kind = .cancel ∧ ∃ (held : HeldSlot config snapshot) (others : List (HeldSlot config snapshot))
      (inbox updatedInbox : HeldInbox config snapshot) (inboxes : List (HeldInbox config snapshot)) (message : Inbox.Message) (closing : ClosedSlot config snapshot),
      controlSlot config snapshot mail control.slot = .ok (.held held others) ∧
      controlInbox config snapshot mail control.slot held.now.activity = .ok (inbox, inboxes) ∧
      inbox.sender = control.sender ∧ inbox.cell = held.now.activity ∧
      inbox.now.withdraw control.slot = some (message, updatedInbox.now) ∧ message.id = control.slot ∧
      updatedInbox.sender = inbox.sender ∧ updatedInbox.target = inbox.target ∧
      closing.name = held.name ∧
      (∀ slot, closing.decided = some slot → held.now.watched = true ∧
        slot = { held.now with phase := .decided .cancelled height, queued := [] }) ∧
      (held.now.watched = true → closing.decided.isSome = true) ∧
      next = { mail with
        inboxes := inboxes ++ [updatedInbox]
        slots := others
        closed := mail.closed ++ [closing]
        refunds := mail.refunds ++ cancelRefunds held.now.activity.value message held.now.queued }) := by
  unfold Mail.control at ok
  split at ok
  · cases ok
  · cases ok; exact .inl rfl
  · rename_i slot closing found
    have closedNone : closing.decided = none := by
      unfold controlSlot at found
      repeat' split at found
      all_goals first | (cases found; done) | (cases found; rfl)
    split at ok
    · cases ok
    · rename_i message sender decider
      split at ok
      · cases ok
      · rename_i authority
        have same : sender = control.sender := Classical.not_not.mp authority
        subst same
        cases kind : control.kind with
        | cancel => rw [kind] at ok; cases ok; exact .inl rfl
        | stop =>
          rw [kind] at ok; cases ok
          exact .inr (.inl ⟨rfl, slot, closing, message, found, closedNone, decider, rfl⟩)
  · rename_i held others found
    split at ok
    · cases ok
    · rename_i inbox inboxes heldOk
      split at ok
      · cases ok
      · rename_i authority
        have sender : inbox.sender = control.sender := Classical.not_not.mp authority
        cases kind : control.kind with
        | stop =>
          rw [kind] at ok
          simp only at ok
          split at ok
          · cases ok
          · rename_i now stopped
            cases ok
            refine .inr (.inr (.inl ⟨rfl, held, _, others, inbox, inboxes, found, heldOk, sender, ?_, ?_, rfl⟩))
            · rfl
            · exact (AnswerSlot.stopWaiting_spec stopped).2.2
        | cancel =>
          rw [kind] at ok
          simp only at ok
          split at ok
          · cases ok
          · rename_i message next' withdrawn
            split at ok
            · cases ok
            · rename_i decided cancelled
              cases ok
              have spec := AnswerSlot.cancelDelivery_spec cancelled
              refine .inr (.inr (.inr ⟨rfl, held, others, inbox, _, inboxes, message, _, found, heldOk, sender,
                (controlInbox_spec heldOk).1, ?_, (Inbox.withdraw_step withdrawn).2.1, ?_, ?_, ?_,
                ?_, ?_, rfl⟩))
              · exact withdrawn
              · rfl
              · rfl
              · rfl
              · intro slot isSome
                dsimp only at isSome
                split at isSome
                · rename_i watched
                  cases isSome
                  exact ⟨watched, spec.2.2⟩
                · cases isSome
              · intro watched
                simp [watched]

/-- **A cancel refunds exactly the escrow it withdraws**: the message's postage and
continuation allowance plus the escrow of every send pipelined on its slot, and nothing else. -/
theorem cancelRefunds_escrow (purse : AccountId) (message : Inbox.Message) (queued : List Inbox.Message) :
    ((cancelRefunds purse message queued).map Refund.amount).sum =
      message.escrow + (queued.map Inbox.Message.escrow).sum ∧
    ∀ refund ∈ cancelRefunds purse message queued, refund.purse = purse := by
  refine ⟨?_, ?_⟩
  · simp [cancelRefunds, List.map_map, Function.comp_def]
  · intro refund member
    simp only [cancelRefunds, List.mem_map] at member
    obtain ⟨_, _, rfl⟩ := member
    rfl

theorem controlSlot_held_name {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {mail : Mail config snapshot} {name : Digest} {held : HeldSlot config snapshot}
    {others : List (HeldSlot config snapshot)}
    (ok : controlSlot config snapshot mail name = .ok (.held held others)) : held.name = name := by
  unfold controlSlot at ok
  split at ok
  · cases ok
  · split at ok
    · rename_i found hit
      split at ok
      · cases ok
      · cases ok
        simpa using List.find?_some hit
    · repeat' split at ok
      all_goals first | (cases ok; done) | (cases ok; rfl)

/-- **The control-level escrow theorem** (OB-ENG condition 3). A cancel either changes no
refund (the message was delivered first, or its slot is gone), or it withdrew the message
named by its slot from an inbox whose SENDER is the cancelling object, and the refunds it
adds are exactly `cancelRefunds` of that message and the sends pipelined on its slot: in
total the message's postage plus the sum of their postage, all out of the purse of the
inbox that held them. -/
theorem Mail.control_cancel_refunds {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {mail next : Mail config snapshot} {height : Nat} {control : Control}
    (ok : mail.control height control = .ok next) (cancel : control.kind = .cancel) :
    next.refunds = mail.refunds ∨
    ∃ (held : HeldSlot config snapshot) (inbox : HeldInbox config snapshot) (message : Inbox.Message)
      (rest : Inbox.Inbox),
      held.name = control.slot ∧ inbox.cell = held.now.activity ∧ inbox.sender = control.sender ∧
      inbox.now.withdraw control.slot = some (message, rest) ∧ message.id = control.slot ∧
      next.refunds = mail.refunds ++ cancelRefunds held.now.activity.value message held.now.queued ∧
      ((cancelRefunds held.now.activity.value message held.now.queued).map Refund.amount).sum =
        message.escrow + (held.now.queued.map Inbox.Message.escrow).sum ∧
      ∀ refund ∈ cancelRefunds held.now.activity.value message held.now.queued,
        refund.purse = held.now.activity.value := by
  rcases Mail.control_cases ok with same | ⟨stop, _⟩ | ⟨stop, _⟩ |
      ⟨_, held, others, inbox, updated, inboxes, message, closing, found, _, sender, cell, withdrawn, named,
        _, _, _, _, _, rfl⟩
  · exact .inl (by rw [same])
  · rw [cancel] at stop; cases stop
  · rw [cancel] at stop; cases stop
  · obtain ⟨sum, purse⟩ := cancelRefunds_escrow held.now.activity.value message held.now.queued
    exact .inr ⟨held, inbox, message, updated.now, controlSlot_held_name found, cell, sender, withdrawn, named, rfl,
      sum, purse⟩

theorem controlSlot_held_delivery {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {mail : Mail config snapshot} {name : Digest} {held : HeldSlot config snapshot}
    {others : List (HeldSlot config snapshot)}
    (ok : controlSlot config snapshot mail name = .ok (.held held others)) :
    ∃ message sender, held.now.decider = .delivery message sender := by
  unfold controlSlot at ok
  split at ok
  · cases ok
  · split at ok
    · split at ok
      · cases ok
      · rename_i message sender decider
        cases ok
        exact ⟨message, sender, decider⟩
    · split at ok
      · cases ok
      · split at ok
        · cases ok
        · split at ok
          · split at ok
            · split at ok
              · cases ok
              · rename_i message sender decider
                split at ok
                · cases ok
                  exact ⟨message, sender, decider⟩
                · cases ok
            · cases ok
          · cases ok

/-- **A cancel of a withdrawable message is never a silent no-op** (the converse of
`Mail.control_cancel_refunds`, OB-ENG): when the slot a cancel names is an open delivery
slot, the inbox it answers to has the cancelling object as sender, and its message is
queued there, an admitted cancel takes the withdraw branch: it adds exactly
`cancelRefunds` of that message and the sends pipelined on the slot. So the no-op
alternative of `Mail.control_cancel_refunds` happens only when the message was not
withdrawable (delivered first, slot gone or decided). -/
theorem Mail.control_cancel_withdraws {rootBytes : Bytes → Digest} {config : Config}
    {snapshot : Snapshot rootBytes} {mail next : Mail config snapshot} {height : Nat} {control : Control}
    {held : HeldSlot config snapshot} {others : List (HeldSlot config snapshot)}
    {inbox : HeldInbox config snapshot} {inboxes : List (HeldInbox config snapshot)}
    {message : Inbox.Message} {rest : Inbox.Inbox}
    (ok : mail.control height control = .ok next) (cancel : control.kind = .cancel)
    (found : controlSlot config snapshot mail control.slot = .ok (.held held others))
    (located : controlInbox config snapshot mail control.slot held.now.activity = .ok (inbox, inboxes))
    (sender : inbox.sender = control.sender)
    (queued : inbox.now.withdraw control.slot = some (message, rest)) :
    next.refunds = mail.refunds ++ cancelRefunds held.now.activity.value message held.now.queued := by
  obtain ⟨delivery, _, decider⟩ := controlSlot_held_delivery found
  unfold Mail.control at ok
  rw [found] at ok
  simp only at ok
  rw [located] at ok
  simp only [sender, ne_eq, not_true_eq_false, if_false, cancel] at ok
  split at ok
  · rename_i none_
    rw [queued] at none_; cases none_
  · rename_i message' next' withdrawn
    rw [queued] at withdrawn
    simp only [Option.some.injEq, Prod.mk.injEq] at withdrawn
    obtain ⟨rfl, rfl⟩ := withdrawn
    split at ok
    · rename_i reason refused
      unfold AnswerSlot.cancelDelivery at refused
      rw [held.opened, decider] at refused
      cases refused
    · cases ok; rfl

/-- The posts of the mail: every held inbox, every held slot and every closed slot,
against the roots the turn read them at. -/
def Mail.posts {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    (mail : Mail config snapshot) : List Post :=
  mail.inboxes.map (fun held => postAt snapshot held.cell (inboxImage held.now)) ++
    mail.slots.map (fun held => slotPost config snapshot held.now) ++
    mail.closed.map ClosedSlot.post

/-- The purses of inboxes the mail opens: registered on the Book in its batch. -/
def Mail.registrations {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    (mail : Mail config snapshot) (book : Book) : List AccountId :=
  (mail.inboxes.map fun held => held.cell.value).filter fun account => !decide (account ∈ book.accounts)

/-- **The purses of the inboxes the mail leaves empty**, closed at the end of its batch
(cv 01a113fe-1390): each one the Book admits closing once the batch's operations ran
(kernel-held, registered, no balance in any asset, no lease naming it). A purse that cannot
close yet (it holds something a stranger paid in, or a lease names it) stays registered,
and a later send to the pair reuses it. The inbox cell itself is retired by its image
(`inboxImage` of an empty inbox). -/
def Mail.deregistrations {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    (mail : Mail config snapshot) (book : Book) (registered : List AccountId) (operations : List Operation) :
    List AccountId :=
  let after := CanonicalResourceKernel.applyOperations (CanonicalResourceKernel.registerAccounts book registered)
    operations
  (((mail.inboxes.filter fun held => held.now.messages.isEmpty).map fun held => held.cell.value).dedup).filter
    fun account => (CanonicalResourceKernel.deregistrationRefusal? after account).isNone

/-- Closing one account leaves every other account's closing admitted as it was. -/
theorem deregistrationAdmission_other {book : Book} {account other : AccountId} (ne : account ≠ other)
    (admitted : CanonicalResourceKernel.DeregistrationAdmission book account) :
    CanonicalResourceKernel.DeregistrationAdmission (book.deregisterAccount other) account :=
  ⟨admitted.1, Finset.mem_erase.mpr ⟨ne, admitted.2.1⟩, admitted.2.2.1, admitted.2.2.2⟩

/-- Distinct accounts each admitted alone are admitted in sequence. -/
theorem deregistrations_admitted_of_each :
    ∀ (book : Book) (accounts : List AccountId), accounts.Nodup →
      (∀ account ∈ accounts, CanonicalResourceKernel.DeregistrationAdmission book account) →
      CanonicalResourceKernel.DeregistrationsAdmitted book accounts
  | _, [], _, _ => trivial
  | book, account :: rest, nodup, each => by
    obtain ⟨notIn, restNodup⟩ := List.nodup_cons.mp nodup
    refine ⟨each account (List.mem_cons_self ..), ?_⟩
    apply deregistrations_admitted_of_each _ rest restNodup
    intro other member
    have ne : other ≠ account := fun same => notIn (by rw [← same]; exact member)
    exact deregistrationAdmission_other ne (each other (List.mem_cons_of_mem _ member))

/-- **The purses a mail closes are admitted closing** on the book its batch's operations
leave: the batch is never refused for them (a purse that could not close is not listed). -/
theorem Mail.deregistrations_admitted {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    (mail : Mail config snapshot) (book : Book) (registered : List AccountId) (operations : List Operation) :
    CanonicalResourceKernel.DeregistrationsAdmitted
      (CanonicalResourceKernel.applyOperations (CanonicalResourceKernel.registerAccounts book registered) operations)
      (mail.deregistrations book registered operations) := by
  apply deregistrations_admitted_of_each
  · exact (List.nodup_dedup _).filter _
  · intro account member
    simp only [Mail.deregistrations, List.mem_filter, Option.isNone_iff_eq_none] at member
    exact (CanonicalResourceKernel.deregistrationRefusal?_eq_none_iff _ account).mp member.2

/-- Control refunds as transfers out of each purse (zero amounts and self-transfers dropped). -/
def refundTransfers (config : Config) (refunds : List Refund) : List Operation :=
  refunds.filterMap fun refund =>
    if refund.amount = 0 ∨ refund.purse = refund.payer then none
    else some (.transfer refund.purse refund.payer config.asset refund.amount)

/-- Postage credits as transfers from `source` (zero amounts and self-transfers dropped). -/
def creditTransfers (config : Config) (source : AccountId) (credits : List (AccountId × Nat)) : List Operation :=
  credits.filterMap fun (purse, amount) =>
    if amount = 0 ∨ purse = source then none else some (.transfer source purse config.asset amount)

/-- Every post of the mail is, at a cell that holds no package, an inbox or slot image or
the retired image (a slot a control retired, or an inbox the mail left empty). (Restated
for row F: before the controls, the retired alternative did not occur.) -/
theorem Mail.posts_shape {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    (mail : Mail config snapshot) :
    ∀ post ∈ mail.posts, ∃ cell, bodyOf .package (snapshot.canonicalBytes cell) = none ∧
      ((∃ role key body, role ≠ .record ∧ post = postAt snapshot cell (image role key body)) ∨
        post = postAt snapshot cell retiredImage) := by
  intro post member
  rcases List.mem_append.mp member with front | inClosed
  · rcases List.mem_append.mp front with inInbox | inSlot
    · obtain ⟨held, _, rfl⟩ := List.mem_map.mp inInbox
      refine ⟨held.cell, held.clean, ?_⟩
      by_cases empty : held.now.messages = []
      · exact .inr (by simp [inboxImage, empty])
      · exact .inl ⟨.inbox, Inbox.key held.now.sender held.now.target, Inbox.encode held.now,
          (by decide : ObjectiveActivityCell.Role.inbox ≠ .record), by simp [inboxImage, empty]⟩
    · obtain ⟨held, _, rfl⟩ := List.mem_map.mp inSlot
      refine ⟨AnswerSlot.cell config.domain held.name, held.clean, .inl ⟨.slot, AnswerSlot.key held.now.name,
        AnswerSlot.encode held.now, (by decide : ObjectiveActivityCell.Role.slot ≠ .record), ?_⟩⟩
      unfold slotPost
      rw [held.named]
  · obtain ⟨closed, _, rfl⟩ := List.mem_map.mp inClosed
    refine ⟨AnswerSlot.cell config.domain closed.name, closed.clean, ?_⟩
    unfold ClosedSlot.post
    cases decided : closed.decided with
    | none => exact .inr rfl
    | some slot =>
      refine .inl ⟨.slot, AnswerSlot.key slot.name, AnswerSlot.encode slot,
        (by decide : ObjectiveActivityCell.Role.slot ≠ .record), ?_⟩
      simp only [slotPost]
      rw [closed.named slot decided]

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

/-- **An admitted send to an object names a deliverable method** (row F, at the interface):
whenever `Mail.send` queues a message on an object's inbox, the target method loads from the
object's pinned package exactly as its delivery will (`loadMethod`, the record's `activePin`,
the object's view, the message's arguments) and its Plan type is within `deliveredPlans
message`: `call`, and `send` only for a message whose allowance continues.
The run-time refusal in `ObjectiveSend.runMessage` stays as the backstop for what the send
cannot see (a nested call into a sending method, an upgrade between send and delivery). -/
theorem Mail.send_object_deliverable {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {mail mail' : Mail config snapshot} {message : Inbox.Message} {target : Nat}
    (sent : mail.send message (.object target) = .ok mail') :
    ∃ d : Deliverable config snapshot target message, deliverable config snapshot target message = .ok d ∧
      loadMethod config target (packageBytes config snapshot d.record.activePin) d.record.activePin message.method
        (viewData d.view) d.args = .ok d.method ∧
      labelsWithin d.method.applied.assumptions d.method.planType (deliveredPlans message) = true := by
  cases found : deliverable config snapshot target message with
  | error reason => simp only [Mail.send, found] at sent; cases sent
  | ok d => exact ⟨d, rfl, d.methodExact, d.callsOnly⟩

/-- Every send of a posted mail addressed to an object is `Deliverable` there. -/
theorem postMail_deliverable {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {postage : Capacity} {refund : AccountId} {depth : Nat} :
    ∀ {outs : List Outgoing} {mail mail' : Mail config snapshot},
      postMail config snapshot postage refund depth mail outs = .ok mail' →
      ∀ out ∈ outs, ∀ target, out.destination = .object target →
        ∃ d : Deliverable config snapshot target (messageOf config postage refund depth out),
          deliverable config snapshot target (messageOf config postage refund depth out) = .ok d
  | [], _, _, _, out, member, _, _ => nomatch member
  | out :: rest, mail, mail', posted, other, member, target, destination => by
    obtain ⟨_, next, sent, posted⟩ := postMail_cons posted
    rcases List.mem_cons.mp member with same | inRest
    · subst same
      rw [destination] at sent
      obtain ⟨d, found, _⟩ := Mail.send_object_deliverable sent
      exact ⟨d, found⟩
    · exact postMail_deliverable posted other inRest target destination

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
  /-- The most the turn's sends may carry, in total, as continuation allowances
  (`Inbox.Message.allowance`), each escrowed from `account` with its postage. -/
  allowance : Nat

def pathStream : StreamCodec (List String) := StreamCodec.list stringStream

def argsBoundStream : StreamCodec ArgsBound :=
  StreamCodec.xmap
    (StreamCodec.sum digestStream
      (StreamCodec.sum
        (StreamCodec.product pathStream
          (StreamCodec.product bytesStream (StreamCodec.option (StreamCodec.product pathStream StreamCodec.nat))))
        (StreamCodec.product pathStream StreamCodec.nat)))
    (fun bound => match bound with
      | .exact digest => .inl digest
      | .recipient path value cap => .inr (.inl (path, value, cap))
      | .capped path limit => .inr (.inr (path, limit)))
    (fun wire => match wire with
      | .inl digest => .exact digest
      | .inr (.inl (path, value, cap)) => .recipient path value cap
      | .inr (.inr (path, limit)) => .capped path limit)
    (by intro bound; cases bound <;> rfl)

/-- v2: a grant binds the code, the arguments and (optionally) the caller (`COMMAND/v8`). -/
def grantStream : StreamCodec Grant :=
  StreamCodec.xmap
    (StreamCodec.product StreamCodec.nat (StreamCodec.product stringStream (StreamCodec.product digestStream
      (StreamCodec.product argsBoundStream (StreamCodec.product (StreamCodec.option StreamCodec.nat) StreamCodec.nat)))))
    (fun grant => (grant.object, grant.method, grant.code, grant.args, grant.caller, grant.uses))
    (fun (o, m, c, a, k, u) => ⟨o, m, c, a, k, u⟩)
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
pay the envelope's public price, escrow every send's postage in its queue's purse,
return the escrow its controls release (`refundTransfers`, out of the purses holding it),
and close the purse of every inbox it left empty that can close (`Mail.deregistrations`). -/
def invokeOperations {rootBytes : Bytes → Digest} {snapshot : Snapshot rootBytes} (config : Config)
    (request : InvokeRequest) (mail : Mail config snapshot) : List Operation :=
  .fee request.account config.collector config.asset (config.tariff.workOf request.envelope) ::
    (creditTransfers config request.account mail.credits ++ refundTransfers config mail.refunds)

def invokeBatch {rootBytes : Bytes → Digest} {snapshot : Snapshot rootBytes} (config : Config) (book : Book)
    (request : InvokeRequest) (mail : Mail config snapshot) : Batch :=
  ⟨mail.registrations book, invokeOperations config request mail,
    mail.deregistrations book (mail.registrations book) (invokeOperations config request mail)⟩

/-- The continuation allowances a list of sends carries, in total. -/
def outboxAllowance (outs : List Outgoing) : Nat := (outs.map Outgoing.allowance).sum

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
    (.enter (rootCall request)) (Journal.start request.grants request.envelope.extractTicks) request.envelope.sourceTicks =
      .ok (result, journal, left)
  /-- A turn that sends declares a postage envelope the deployment covers. -/
  postageCovered : journal.outbox ≠ [] → config.covers request.postage = true
  /-- What the call tree commits on a draining object is migratable. -/
  drainedOk : journal.drained = true
  /-- The sends' continuation allowances are within the one the signer declared. -/
  allowanceCovered : outboxAllowance journal.outbox ≤ request.allowance
  /-- The mail of the turn's sends (each at depth 0). -/
  sent : Mail config snapshot
  sentExact : postMail config snapshot request.postage request.account 0 Mail.empty journal.outbox = .ok sent
  /-- That mail after the turn's controls. -/
  mail : Mail config snapshot
  mailExact : postControls config snapshot height sent journal.controls = .ok mail
  book : BookCell
  bookExact : loadBook config snapshot = .ok book
  posted : Postings book
  batchExact : posted.batch = invokeBatch config (logicalBook book.logical) request mail
  posts : List Post
  postsExact : posts = journal.posts config snapshot ++ mail.posts ++ [posted.write config snapshot]

def invoke {rootBytes : Bytes → Digest} (config : Config) (snapshot : Snapshot rootBytes)
    (height : Nat) (request : InvokeRequest) : Except CallRefusal (Invocation config snapshot height request) :=
  if covered : config.covers request.envelope = true then
    -- The root frame's front-end work account (GPT-6 row E), judged from the stored pair of the
    -- package the root frame will load, before any frame replays it. Nested frames and the root's
    -- second (method) replay are not yet in the account (cv task 01a11636-201e).
    match (match readObject config snapshot request.object with
        | .ok (some record) => frontEndPaid config (packageBytes config snapshot record.activePin) [request.envelope]
        | _ => .ok ()) with
    | .error reason => .error (.kernel reason)
    | .ok () =>
    match execExact : exec config snapshot height request.authority (invokeTransaction request)
        (callFuel request.envelope) [] (.enter (rootCall request)) (Journal.start request.grants request.envelope.extractTicks)
        request.envelope.sourceTicks with
    | .error reason => .error reason
    | .ok (result, journal, left) =>
      if postageCovered : journal.outbox ≠ [] → config.covers request.postage = true then
      if drainedOk : journal.drained = true then
      if allowanceCovered : outboxAllowance journal.outbox ≤ request.allowance then
      match sentExact : postMail config snapshot request.postage request.account 0 Mail.empty journal.outbox with
      | .error reason => .error reason
      | .ok sent =>
      match mailExact : postControls config snapshot height sent journal.controls with
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
          .ok ⟨covered, result, journal, left, execExact, postageCovered, drainedOk, allowanceCovered, sent, sentExact,
            mail, mailExact, book, bookExact, posted, batchExact, _, rfl⟩
      else .error (.allowanceExceeded (outboxAllowance journal.outbox) request.allowance)
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

/-- **An admitted invocation sends only to deliverable methods**: every send of its call
tree addressed to an object names a method that loads there with a Plan within `call`
(`Deliverable`). A send to a sending method was refused `notDeliverable` before the
invocation's fee or any postage was posted. -/
theorem Invocation.sends_deliverable {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height : Nat} {request : InvokeRequest} (invoked : Invocation config snapshot height request) :
    ∀ out ∈ invoked.journal.outbox, ∀ target, out.destination = .object target →
      ∃ d : Deliverable config snapshot target (messageOf config request.postage request.account 0 out),
        deliverable config snapshot target (messageOf config request.postage request.account 0 out) = .ok d :=
  postMail_deliverable invoked.sentExact

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
                      callerOf authority stack, call.args, grants⟩ : Ctx) :: stack).map (·.object) |>.Nodup := by
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
          rename_i extracted _
          split at ran
          · cases ran
          rename_i _ drawn
          obtain rfl := Journal.draw_ok drawn
          have viewed : ({ journal with extracts := journal.extracts -
              (config.planBudget.ticks - extracted.remaining.ticks) } : Journal).lookup
              ctx.object = some (some ctx.view) := viewed
          have read : ObjectsRead config snapshot { journal with extracts := journal.extracts -
              (config.planBudget.ticks - extracted.remaining.ticks) } := read
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
                      rfl
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
            · -- a control: only the controls grow
              rename_i kind slot _
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
          rename_i out _
          split at ran
          · cases ran
          rename_i _ drawn
          obtain rfl := Journal.draw_ok drawn
          have viewed : ({ journal with extracts := journal.extracts -
              (config.planBudget.ticks - out.remaining.ticks) } : Journal).lookup
              ctx.object = some (some ctx.view) := viewed
          have read : ObjectsRead config snapshot { journal with extracts := journal.extracts -
              (config.planBudget.ticks - out.remaining.ticks) } := read
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
      ∃ cell, bodyOf .package (snapshot.canonicalBytes cell) = none ∧
        ((∃ role key body, role ≠ .record ∧ post = postAt snapshot cell (image role key body)) ∨
          post = postAt snapshot cell retiredImage) := by
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

/-! ## Delegation: every frame receiving delegated authority has a matching unconsumed authorization

Delegation (which subject a frame's request carries) and consent (whether the frame's object
admits its write) stay separate: a delegated frame's write is still judged by its object's law
(`invocation_writes_from_view`); a grant only decides whether `request/subject` is present. -/

/-- What a grant's admitting verdict establishes. -/
theorem Grant.judge_admit {grant : Grant} {used : List Delegation} {index : Nat} {code : Digest} {args : Data}
    {caller : Option Nat} {amount : Nat} (admitted : grant.judge used index code args caller = .admit amount) :
    grant.code = code ∧ callerOk grant.caller caller = true ∧ grant.args.admits args = true ∧
      grant.args.amount args = some amount ∧ (usesOf used index).length < grant.uses ∧
      ∀ path limit, grant.args.cap = some (path, limit) → chargedOf used index + amount ≤ limit := by
  unfold Grant.judge at admitted
  split at admitted
  · cases admitted
  · rename_i sameCode
    split at admitted
    · cases admitted
    · rename_i callerHolds
      split at admitted
      · cases admitted
      · rename_i argsHold
        split at admitted
        · cases admitted
        · rename_i charged chargedEq
          split at admitted
          · cases admitted
          · rename_i usesLeft
            split at admitted
            · rename_i noCap
              cases admitted
              refine ⟨by simpa using sameCode, by simpa using callerHolds, by simpa using argsHold, chargedEq,
                by omega, ?_⟩
              intro path limit capped
              rw [noCap] at capped; cases capped
            · rename_i path limit capped
              split at admitted
              · rename_i within
                cases admitted
                refine ⟨by simpa using sameCode, by simpa using callerHolds, by simpa using argsHold, chargedEq,
                  by omega, ?_⟩
                intro path' limit' capped'
                rw [capped] at capped'
                cases capped'
                exact within
              · cases admitted

/-- **A spent grant names the frame it was spent on**: the delegation points at a grant (by index)
that names the frame's (object, method) and admitted it, and records exactly the frame. -/
theorem spendFrom_some {used : List Delegation} {object : Nat} {method : String} {code : Digest} {args : Data}
    {caller : Option Nat} : ∀ (grants : List Grant) (index : Nat) (first : Option CallRefusal) (d : Delegation),
    spendFrom used object method code args caller grants index first = .ok (some d) →
    ∃ k grant, grants[k]? = some grant ∧ d.grant = index + k ∧ grant.object = object ∧ grant.method = method ∧
      d.object = object ∧ d.method = method ∧ d.code = code ∧ d.args = args ∧ d.caller = caller ∧
      grant.judge used d.grant code args caller = .admit d.amount := by
  intro grants
  induction grants with
  | nil =>
    intro index first d spent
    cases first <;> simp [spendFrom] at spent
  | cons grant rest ih =>
    intro index first d spent
    unfold spendFrom at spent
    split at spent
    · rename_i names
      split at spent
      · rename_i amount judged
        cases spent
        exact ⟨0, grant, rfl, by simp, names.1, names.2, rfl, rfl, rfl, rfl, rfl, judged⟩
      · obtain ⟨k, g, at_, idx, rest'⟩ := ih _ _ d spent
        exact ⟨k + 1, g, by simpa using at_, by rw [idx]; omega, rest'⟩
    · obtain ⟨k, g, at_, idx, rest'⟩ := ih _ _ d spent
      exact ⟨k + 1, g, by simpa using at_, by rw [idx]; omega, rest'⟩

theorem usesOf_snoc (used : List Delegation) (d : Delegation) (index : Nat) :
    usesOf (used ++ [d]) index = usesOf used index ++ (if d.grant = index then [d] else []) := by
  unfold usesOf
  rw [List.filter_append]
  by_cases same : d.grant = index <;> simp [same]

theorem chargedOf_snoc (used : List Delegation) (d : Delegation) (index : Nat) :
    chargedOf (used ++ [d]) index = chargedOf used index + (if d.grant = index then d.amount else 0) := by
  unfold chargedOf
  rw [usesOf_snoc]
  by_cases same : d.grant = index <;> simp [same]

theorem Authorized.start (grants : List Grant) : Authorized grants [] :=
  ⟨by simp, fun index grant _ => ⟨by simp [usesOf], fun _ _ _ => by simp [chargedOf, usesOf]⟩⟩

/-- **Spending keeps every delegation authorized**: the new delegation names a grant that
authorizes it, that grant had a use left, and its cap covers the new amount. -/
theorem Authorized.spend {grants : List Grant} {used : List Delegation} {object : Nat} {method : String}
    {code : Digest} {args : Data} {caller : Option Nat} {d : Delegation} (held : Authorized grants used)
    (spent : spendGrant grants used object method code args caller = .ok (some d)) :
    Authorized grants (used ++ [d]) ∧ d.object = object ∧ d.method = method ∧ d.code = code ∧ d.args = args ∧
      d.caller = caller := by
  obtain ⟨k, grant, at_, idx, gObject, gMethod, dObject, dMethod, dCode, dArgs, dCaller, judged⟩ :=
    spendFrom_some grants 0 none d spent
  simp only [Nat.zero_add] at idx
  obtain ⟨sameCode, callerHolds, argsHold, amountEq, usesLeft, capOk⟩ := Grant.judge_admit judged
  refine ⟨⟨?_, ?_⟩, dObject, dMethod, dCode, dArgs, dCaller⟩
  · intro x member
    rcases List.mem_append.mp member with old | new
    · exact held.1 x old
    · simp only [List.mem_singleton] at new
      subst new
      refine ⟨grant, by rw [idx]; exact at_, ?_⟩
      refine ⟨by rw [gObject, dObject], by rw [gMethod, dMethod], by rw [sameCode, dCode], ?_, ?_, ?_⟩
      · rw [dCaller]; exact callerHolds
      · rw [dArgs]; exact argsHold
      · rw [dArgs]; exact amountEq
  · intro index g found
    obtain ⟨usesOk, capsOk⟩ := held.2 index g found
    rw [usesOf_snoc]
    by_cases same : d.grant = index
    · have : g = grant := by
        rw [← same, idx, at_] at found
        exact (Option.some.inj found).symm
      subst this
      refine ⟨by simp [same]; rw [← same]; omega, ?_⟩
      intro path limit capped
      rw [chargedOf_snoc]
      simp only [same, if_true]
      have := capOk path limit capped
      rw [same] at this
      omega
    · refine ⟨by simpa [same] using usesOk, ?_⟩
      intro path limit capped
      rw [chargedOf_snoc]
      simpa [same] using capsOk path limit capped

/-- **What `frameAuthority` decides**: the root frame carries the signer and no delegation; a
nested frame carries no subject and no delegation, or the signer together with a delegation
`spendGrant` spent on exactly this call. -/
theorem frameAuthority_spec {authority : Authority} {stack : List Ctx} {journal : Journal} {call : CallPlan}
    {code : Digest} {subject : Option SubjectId} {delegation : Option Delegation}
    (decided : frameAuthority authority stack journal call code = .ok (subject, delegation)) :
    (stack = [] ∧ subject = authority.signer ∧ delegation = none) ∨
      (subject = none ∧ delegation = none) ∨
      ∃ d, delegation = some d ∧ subject = authority.signer ∧
        spendGrant journal.grants journal.delegations call.target.value call.method code call.args
          (callerOf authority stack) = .ok (some d) := by
  unfold frameAuthority at decided
  split at decided
  · cases decided; exact .inl ⟨rfl, rfl, rfl⟩
  · split at decided
    · cases decided
    · cases decided; exact .inr (.inl ⟨rfl, rfl⟩)
    · rename_i d spent
      cases decided
      exact .inr (.inr ⟨d, rfl, rfl, spent⟩)

/-- A frame's subject is accounted for: the root's (the signer, with the root's caller, which in
an invocation no nested frame has), none, or a recorded delegation spent on exactly this frame. -/
def Ctx.Delegated (authority : Authority) (ctx : Ctx) (delegations : List Delegation) : Prop :=
  (ctx.subject = authority.signer ∧ ctx.caller = authority.origin) ∨ ctx.subject = none ∨
    ∃ d, ctx.delegation = some d ∧ d ∈ delegations ∧ d.object = ctx.object.value ∧ d.method = ctx.method ∧
      d.code = ctx.record.activePin ∧ d.args = ctx.args ∧ d.caller = ctx.caller

/-- A write's subject is accounted for (`Ctx.Delegated`, over the facts it was judged under). -/
def Written.Delegated (authority : Authority) (w : Written) (delegations : List Delegation) : Prop :=
  (w.facts.subject = authority.signer ∧ w.facts.caller = authority.origin) ∨ w.facts.subject = none ∨
    ∃ d, w.delegation = some d ∧ d ∈ delegations ∧ d.object = w.object.value ∧ d.method = w.method ∧
      d.code = w.record.activePin ∧ d.args = w.args ∧ d.caller = w.facts.caller

theorem Ctx.Delegated.grow {authority : Authority} {ctx : Ctx} {ds : List Delegation} (more : List Delegation)
    (held : ctx.Delegated authority ds) : ctx.Delegated authority (ds ++ more) := by
  rcases held with root | none_ | ⟨d, at_, member, rest⟩
  · exact .inl root
  · exact .inr (.inl none_)
  · exact .inr (.inr ⟨d, at_, List.mem_append_left _ member, rest⟩)

theorem Written.Delegated.grow {authority : Authority} {w : Written} {ds : List Delegation} (more : List Delegation)
    (held : w.Delegated authority ds) : w.Delegated authority (ds ++ more) := by
  rcases held with root | none_ | ⟨d, at_, member, rest⟩
  · exact .inl root
  · exact .inr (.inl none_)
  · exact .inr (.inr ⟨d, at_, List.mem_append_left _ member, rest⟩)

theorem touch_delegations {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {journal journal' : Journal} {object : CellId} {entry : Entry}
    (touched : touch config snapshot journal object = .ok (entry, journal')) :
    journal'.grants = journal.grants ∧ journal'.delegations = journal.delegations ∧ journal'.writes = journal.writes := by
  unfold touch at touched
  split at touched
  · cases touched; exact ⟨rfl, rfl, rfl⟩
  · split at touched
    · cases touched
    · cases touched
    · split at touched
      · cases touched
      · cases touched; exact ⟨rfl, rfl, rfl⟩

theorem frameReturn_delegations {ctx : Ctx} {write : Data} {journal journal' : Journal}
    (returned : frameReturn ctx write journal = .ok journal') :
    journal'.grants = journal.grants ∧ journal'.delegations = journal.delegations ∧
      ∃ new, journal'.writes = journal.writes ++ new ∧ ∀ w ∈ new,
        w.facts = ctx.facts ∧ w.delegation = ctx.delegation ∧ w.object = ctx.object ∧ w.method = ctx.method ∧
          w.record = ctx.record ∧ w.args = ctx.args := by
  unfold frameReturn at returned
  split at returned
  · cases returned
  · split at returned
    · split at returned
      · cases returned
      · cases returned; exact ⟨rfl, rfl, [], by simp, by simp⟩
      · split at returned
        · cases returned
        · cases returned
          refine ⟨rfl, rfl, [_], rfl, ?_⟩
          intro w member
          simp only [List.mem_singleton] at member
          subst member
          exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
    · cases returned

/-- **What the executor maintains about delegation** (by induction over its recursion): the grants
never change; delegations are only appended; every delegation stays authorized by a grant (no grant
used more than `uses` times, no cap exceeded); and every write's subject is accounted for. -/
theorem exec_delegations {rootBytes : Bytes → Digest} (config : Config) (snapshot : Snapshot rootBytes)
    (height : Nat) (authority : Authority) (turn : TransactionId) :
    ∀ (fuel : Nat) (stack : List Ctx) (task : Task) (journal : Journal) (ticks : Nat)
      (result : Data) (journal' : Journal) (left : Nat),
    exec config snapshot height authority turn fuel stack task journal ticks = .ok (result, journal', left) →
    Authorized journal.grants journal.delegations →
    (∀ ctx state, task = .run state → stack.head? = some ctx → ctx.Delegated authority journal.delegations) →
    journal'.grants = journal.grants ∧ (∃ new, journal'.delegations = journal.delegations ++ new) ∧
      Authorized journal'.grants journal'.delegations ∧
      ∃ new, journal'.writes = journal.writes ++ new ∧ ∀ w ∈ new, w.Delegated authority journal'.delegations := by
  intro fuel
  induction fuel with
  | zero => intro stack task journal ticks result journal' left ran; simp [exec] at ran
  | succ fuel ih =>
    intro stack task journal ticks result journal' left ran held running
    cases task with
    | enter call =>
      simp only [exec] at ran
      split at ran
      · cases ran
      · split at ran
        · cases ran
        · split at ran
          · cases ran
          · rename_i entry journal1 touched
            obtain ⟨grants1, delegations1, _⟩ := touch_delegations touched
            split at ran
            · cases ran
            · cases ran
            · rename_i view current _
              split at ran
              · cases ran
              · rename_i subject delegation decided
                split at ran
                · cases ran
                · rename_i program _
                  have decided' := frameAuthority_spec decided
                  rw [grants1, delegations1] at decided'
                  -- the journal the frame runs under
                  have held' : Authorized journal.grants (journal.delegations ++ delegation.toList) := by
                    rcases decided' with ⟨_, _, rfl⟩ | ⟨_, rfl⟩ | ⟨d, rfl, _, spent⟩
                    · simpa using held
                    · simpa using held
                    · exact (Authorized.spend held spent).1
                  obtain ⟨grantsEq, ⟨new, delegationsEq⟩, authorized, writesNew⟩ :=
                    ih _ _ _ _ _ _ _ ran (by simpa [grants1, delegations1] using held') (by
                      intro ctx state _ head
                      simp only [List.head?_cons, Option.some.injEq] at head
                      subst head
                      rcases decided' with ⟨empty, rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨d, rfl, rfl, spent⟩
                      · subst empty; exact .inl ⟨rfl, rfl⟩
                      · exact .inr (.inl rfl)
                      · obtain ⟨_, dObject, dMethod, dCode, dArgs, dCaller⟩ := Authorized.spend held spent
                        exact .inr (.inr ⟨d, rfl, by simp, dObject, dMethod, dCode, dArgs, dCaller⟩))
                  refine ⟨by rw [grantsEq, grants1], ⟨delegation.toList ++ new, ?_⟩, authorized, ?_⟩
                  · rw [delegationsEq, delegations1, List.append_assoc]
                  · obtain ⟨newW, writesEq, each⟩ := writesNew
                    obtain ⟨_, _, writes1⟩ := touch_delegations touched
                    exact ⟨newW, by rw [writesEq]; simp [writes1], each⟩
    | run state =>
      cases stack with
      | nil => simp [exec] at ran
      | cons ctx rest =>
        have mine := running ctx state rfl rfl
        simp only [exec] at ran
        split at ran
        · -- yielded
          split at ran
          · cases ran
          split at ran
          · cases ran
          · rename_i _ drawn
            obtain rfl := Journal.draw_ok drawn
            split at ran
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
                    obtain ⟨grants1, ⟨new1, dels1⟩, auth1, ⟨w1, writes1, each1⟩⟩ :=
                      ih _ _ _ _ _ _ _ entered held (by intro _ _ h; cases h)
                    obtain ⟨grants2, ⟨new2, dels2⟩, auth2, ⟨w2, writes2, each2⟩⟩ :=
                      ih _ _ _ _ _ _ _ ran auth1 (by
                        intro c _ _ head
                        simp only [List.head?_cons, Option.some.injEq] at head
                        subst head
                        rw [dels1]; exact mine.grow new1)
                    refine ⟨by rw [grants2, grants1], ⟨new1 ++ new2, by rw [dels2, dels1, List.append_assoc]⟩,
                      auth2, ⟨w1 ++ w2, by rw [writes2, writes1, List.append_assoc], ?_⟩⟩
                    intro w member
                    rcases List.mem_append.mp member with a | b
                    · rw [dels2]; exact (each1 w a).grow new2
                    · exact each2 w b
            · -- a send: only the outbox grows
              split at ran
              · cases ran
              · split at ran
                · cases ran
                · have step := ih _ _ _ _ _ _ _ ran held (by
                    intro c _ _ head
                    have same : ctx = c := by simpa using head
                    subst same; exact mine)
                  exact step
            · -- a control: only the controls grow
              split at ran
              · cases ran
              · split at ran
                · cases ran
                · have step := ih _ _ _ _ _ _ _ ran held (by
                    intro c _ _ head
                    have same : ctx = c := by simpa using head
                    subst same; exact mine)
                  exact step
        · -- finished
          split at ran
          · cases ran
          split at ran
          · cases ran
          · rename_i _ drawn
            obtain rfl := Journal.draw_ok drawn
            split at ran
            · cases ran
            · split at ran
              · cases ran
              · rename_i journal1 returned
                cases ran
                obtain ⟨grantsEq, delsEq, new, writesEq, each⟩ := frameReturn_delegations returned
                refine ⟨grantsEq, ⟨[], by simpa using delsEq⟩, by rw [grantsEq, delsEq]; exact held, new, writesEq, ?_⟩
                intro w member
                obtain ⟨facts, delegation, object, method, record, args⟩ := each w member
                rw [delsEq]
                rcases mine with ⟨subject, caller⟩ | none_ | ⟨d, at_, dMember, dObject, dMethod, dCode, dArgs, dCaller⟩
                · exact .inl ⟨by rw [facts]; exact subject, by rw [facts]; exact caller⟩
                · exact .inr (.inl (by rw [facts]; exact none_))
                · refine .inr (.inr ⟨d, by rw [delegation]; exact at_, dMember, ?_, ?_, ?_, ?_, ?_⟩)
                  · rw [object]; exact dObject
                  · rw [method]; exact dMethod
                  · rw [record]; exact dCode
                  · rw [args]; exact dArgs
                  · rw [facts]; exact dCaller
        · cases ran
        · cases ran
        · cases ran

/-- **Every frame receiving delegated authority has a matching unconsumed authorization** (GPT-6
row A), in every admitted invocation: each recorded delegation names one of the signed grants that
authorizes it (object, method, the code the frame ran, its arguments, its direct caller), no grant
is used more than its `uses`, no capped grant is charged past its limit; and every frame write
carries the signer's subject only as the root frame (`request/caller` none, which no nested frame
has) or through a delegation recorded for exactly that frame. The write itself was judged by its
object's law under those facts (`invocation_writes_from_view`): delegation is not consent. -/
theorem invocation_delegated_authority {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height : Nat} {request : InvokeRequest} (invoked : Invocation config snapshot height request) :
    Authorized request.grants invoked.journal.delegations ∧
      ∀ w ∈ invoked.journal.writes,
        (w.facts.subject = some request.subject ∧ w.facts.caller = none) ∨ w.facts.subject = none ∨
          ∃ d, w.delegation = some d ∧ d ∈ invoked.journal.delegations ∧ d.object = w.object.value ∧
            d.method = w.method ∧ d.code = w.record.activePin ∧ d.args = w.args ∧ d.caller = w.facts.caller := by
  obtain ⟨grantsEq, _, authorized, new, writes, each⟩ :=
    exec_delegations config snapshot height request.authority (invokeTransaction request) _ [] _ _ _ _ _ _
      invoked.execExact (Authorized.start _) (by intro _ _ h; cases h)
  refine ⟨by simpa [grantsEq, Journal.start] using authorized, ?_⟩
  intro w member
  rw [writes] at member
  simp only [Journal.start, List.nil_append] at member
  exact each w member

#assert_axioms Journal.posts_state
#assert_axioms Invocation.posts_shape
#assert_axioms touch_read
#assert_axioms frameReturn_read
#assert_axioms runCounted_outcome
#assert_axioms runCounted_left_le
#assert_axioms frame_limits_are_segment_limits
#assert_axioms reentry_refused
#assert_axioms touch_spec
#assert_axioms lookup_install_ne
#assert_axioms frameReturn_spec
#assert_axioms exec_invariant
#assert_axioms Journal.draw_ok Journal.draw_two Journal.draw_short ceiling_reservation_refuses
#assert_axioms invocation_reentry_free
#assert_axioms invocation_writes_from_view
#assert_axioms active_frame_view_stability
#assert_axioms invocation_writes_pinned
#assert_axioms Ctx.facts_artifact
#assert_axioms Invocation.conserves
#assert_axioms Mail.posts_shape
#assert_axioms Mail.inboxes_lawful
#assert_axioms Grant.judge_admit
#assert_axioms spendFrom_some
#assert_axioms Authorized.spend
#assert_axioms frameAuthority_spec
#assert_axioms exec_delegations
#assert_axioms invocation_delegated_authority
#assert_axioms controlInbox_spec
#assert_axioms Mail.control_cases
#assert_axioms controlSlot_held_name
#assert_axioms cancelRefunds_escrow
#assert_axioms Mail.control_cancel_refunds
#assert_axioms controlSlot_held_delivery
#assert_axioms Mail.deregistrations_admitted
#assert_axioms Mail.control_cancel_withdraws

end Minidregg.Kernel.ObjectiveCall
