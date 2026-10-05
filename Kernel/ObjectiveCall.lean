/- Synchronous cross-object `call` (OB7): a signed invocation runs a method of
an object's pinned package, and that method may call methods of other objects
in the same turn, depth-first, each callee on its own pinned package.

**What a method is.** A declaration of the entry module of the package an object
pins (`ObjectRecord.pin`, the published pair of `Kernel.ObjectiveActivity`),
lowered by the kernel's own front end with that declaration selected
(`loadMethod`: the pinned sources, replayed, never an offered core). Its type is

    method(view: {version: Nat, state: S}, args: X) -> Activity<P, R, {result: A, write: W}>

where the Plan type `P` has exactly one label, `call`, and the response type `R`
exactly one, `returned`. A method can therefore yield nothing but a call, and
a call is answered in the same turn: no frame ever suspends across turns (the
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

**The turn** (`invoke`) commits every written object's state cell and the fee,
as ONE intent, guarded on every object record, package cell and state cell it
read, so a concurrent change refuses it. -/
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

/-- A sum type whose ONLY label is `label`. -/
def soleLabel (assumptions : Assumptions) (type : Ty) (label : String) : Bool :=
  match unalias assumptions.bounds type with
  | .variant row => rowLabels assumptions.bounds 64 row == some [label]
  | _ => false

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
  callsOnly : soleLabel applied.assumptions planType "call" = true
  returnsOnly : soleLabel applied.assumptions responseType "returned" = true

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
          if callsOnly : soleLabel applied.assumptions planType "call" = true then
            if returnsOnly : soleLabel applied.assumptions responseType "returned" = true then
              .ok ⟨definition, lowering, replayExact, accepted, fuelWithin, applied, checked, planType,
                responseType, resultType, typeExact, callsOnly, returnsOnly⟩
            else .error (.notCallable target method "its response type is not `returned` alone")
          else .error (.notCallable target method "its Plan type is not `call` alone: a method that awaits is not callable")
        | _ => .error (.notCallable target method "it does not return an Activity")
    | _ => .error (.notCallable target method "it does not take a view and arguments")
  else .error (.notCallable target method "typed core checker fuel exceeds the kernel's capacity")

/-! ## Plans, returns, grants -/

/-- A call a frame yields: `call {target, method, args}`. -/
structure CallPlan where
  target : CellId
  method : String
  args : Data

def decodeCall (target : Nat) (method : String) : Data → Except CallRefusal CallPlan
  | .variant "call" (.record fields) =>
    match fieldOf fields "target", fieldOf fields "method", fieldOf fields "args" with
    | some (.natural object), some (.label name), some args => .ok ⟨⟨object⟩, name, args⟩
    | _, _, _ => .error (.callShape target method "call needs target (Nat), method (String) and args")
  | _ => .error (.callShape target method "a frame yields only `call`")

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

structure Journal where
  entries : List Entry
  grants : List Grant
  /-- Every frame entered, in order: the objects on the stack at its entry,
  innermost first (the frame's own object at the head). -/
  frames : List (List Nat)
  writes : List Written

def Journal.start (grants : List Grant) : Journal := ⟨[], grants, [], []⟩

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
  facts : Facts

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
        match admitWrite ctx.record ctx.facts (some before.value) value with
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
    (signer : SubjectId) : Nat → List Ctx → Task → Journal → Nat → Except CallRefusal (Data × Journal × Nat)
  | 0, _, _, _, _ => .error .exhausted
  | fuel + 1, stack, .enter call, journal, ticks =>
    if stack.any (fun ctx => ctx.object == call.target) then
      .error (.reentry call.target.value (stack.map (·.object.value)))
    else if callDepth ≤ stack.length then .error (.depth callDepth)
    else
    match touch config snapshot journal call.target with
    | .error reason => .error reason
    | .ok (entry, journal) =>
    match entry.current with
    | none => .error (.stateMissing call.target.value)
    | some view =>
    let granted : Except CallRefusal (Option SubjectId × List Grant) :=
      match stack with
      | [] => .ok (some signer, journal.grants)
      | _ :: _ => match spendGrant call.target.value call.method journal.grants with
        | .ungranted => .ok (none, journal.grants)
        | .spent grants => .ok (some signer, grants)
        | .exhausted => .error (.grantSpent call.target.value call.method)
    match granted with
    | .error reason => .error reason
    | .ok (subject, grants) =>
    match loadMethod config call.target.value (packageBytes config snapshot entry.record.pin) entry.record.pin
        call.method (viewData view) call.args with
    | .error reason => .error reason
    | .ok program =>
    let ctx : Ctx := ⟨call.target, call.method, entry.record, program.applied.assumptions, program.responseType,
      view, ⟨subject, height, call.target.value, callTurn, stack.head?.map (·.object.value)⟩⟩
    let journal : Journal := ⟨journal.entries, grants,
      journal.frames ++ [call.target.value :: stack.map (·.object.value)], journal.writes⟩
    exec config snapshot height signer fuel (ctx :: stack) (.run (initial program.applied.erase)) journal ticks
  | _ + 1, [], .run _, _, _ => .error .exhausted
  | fuel + 1, ctx :: rest, .run state, journal, ticks =>
    match runCounted config.limits ticks state with
    | (.yielded _ yielded, left) =>
      match ObjectiveBendDemandData.yieldedPlan config.limits config.planBudget yielded with
      | .error (failure, _) => .error (.frameFault ctx.object.value ctx.method s!"plan extraction: {reprStr failure}")
      | .ok extracted =>
      match decodeCall ctx.object.value ctx.method extracted.value with
      | .error reason => .error reason
      | .ok call =>
      match exec config snapshot height signer fuel (ctx :: rest) (.enter call) journal left with
      | .error reason => .error reason
      | .ok (result, journal, left) =>
      match typeData ctx.assumptions config.typeFuel (returnedData result) ctx.responseType with
      | none => .error (.resultType ctx.object.value ctx.method)
      | some _ =>
      match resume (returnedData result).term yielded with
      | none => .error (.frameFault ctx.object.value ctx.method "resume")
      | some next => exec config snapshot height signer fuel (ctx :: rest) (.run next) journal left
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

/-! ## The invocation turn -/

structure InvokeRequest where
  subject : SubjectId
  object : CellId
  method : String
  args : Data
  grants : List Grant
  /-- The one declared envelope of the whole call tree. -/
  envelope : Capacity
  /-- The signer's Book account: pays the envelope's public price. -/
  account : AccountId
  nonce : Nat

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
     guardAt snapshot (packageCell config.domain entry.record.pin),
     guardAt snapshot (stateCell config.domain entry.object)]

/-- An admitted invocation: the call tree ran to the root's return within the
envelope, every frame write passed its object's law, and the fee is posted. -/
structure Invocation {rootBytes : Bytes → Digest} (config : Config) (snapshot : Snapshot rootBytes)
    (height : Nat) (request : InvokeRequest) where
  private mk ::
  covered : config.covers request.envelope = true
  result : Data
  journal : Journal
  left : Nat
  execExact : exec config snapshot height request.subject (callFuel request.envelope) []
    (.enter (rootCall request)) (Journal.start request.grants) request.envelope.sourceTicks = .ok (result, journal, left)
  book : BookCell
  bookExact : loadBook config snapshot = .ok book
  posted : Postings book
  batchExact : posted.batch = ⟨[], [.fee request.account config.collector config.asset
    (config.tariff.workOf request.envelope)], []⟩
  posts : List Post
  postsExact : posts = journal.posts config snapshot ++ [posted.write config snapshot]

def invoke {rootBytes : Bytes → Digest} (config : Config) (snapshot : Snapshot rootBytes)
    (height : Nat) (request : InvokeRequest) : Except CallRefusal (Invocation config snapshot height request) :=
  if covered : config.covers request.envelope = true then
    match execExact : exec config snapshot height request.subject (callFuel request.envelope) []
        (.enter (rootCall request)) (Journal.start request.grants) request.envelope.sourceTicks with
    | .error reason => .error reason
    | .ok (result, journal, left) =>
      match bookExact : loadBook config snapshot with
      | .error reason => .error (.kernel reason)
      | .ok book =>
        let batch : Batch := ⟨[], [.fee request.account config.collector config.asset
          (config.tariff.workOf request.envelope)], []⟩
        match postedExact : postings book batch with
        | .error reason => .error (.kernel reason)
        | .ok posted =>
          have batchExact : posted.batch = batch := by
            unfold postings at postedExact
            split at postedExact
            · cases postedExact; rfl
            · cases postedExact
          .ok ⟨covered, result, journal, left, execExact, book, bookExact, posted, batchExact, _, rfl⟩
  else .error (.kernel (.uncovered request.envelope))

def Invocation.guards {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height : Nat} {request : InvokeRequest} (invoked : Invocation config snapshot height request) : List ReadGuard :=
  invoked.journal.guards config snapshot

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
    (height : Nat) (signer : SubjectId) (fuel : Nat) (stack : List Ctx) (call : CallPlan) (journal : Journal)
    (ticks : Nat) (onStack : ∃ ctx ∈ stack, ctx.object = call.target) :
    exec config snapshot height signer (fuel + 1) stack (.enter call) journal ticks =
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

/-- Every object the journal holds was read from the snapshot (its state cell
decodes there): what makes its state post safe for the checkpoint invariant. -/
def ObjectsRead {rootBytes : Bytes → Digest} (config : Config) (snapshot : Snapshot rootBytes)
    (journal : Journal) : Prop :=
  ∀ entry ∈ journal.entries, ∃ current, readState config snapshot entry.object = .ok current

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
      · rename_i record _ current readOk
        cases touched
        intro e member
        simp only [List.mem_append, List.mem_singleton] at member
        rcases member with old | new
        · exact read e old
        · subst new; exact ⟨current, readOk⟩

theorem install_read {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    (journal : Journal) (object : CellId) (state : ObjectState)
    (read : ObjectsRead config snapshot journal) : ObjectsRead config snapshot (journal.install object state) := by
  intro e member
  simp only [Journal.install, List.mem_map] at member
  obtain ⟨e0, m0, rfl⟩ := member
  obtain ⟨c, h⟩ := read e0 m0
  exact ⟨c, by split <;> exact h⟩

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
          admitWrite w.record w.facts (some w.before.value) w.after.value = .ok () := by
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
    (height : Nat) (signer : SubjectId) :
    ∀ (fuel : Nat) (stack : List Ctx) (task : Task) (journal : Journal) (ticks : Nat)
      (result : Data) (journal' : Journal) (left : Nat),
    exec config snapshot height signer fuel stack task journal ticks = .ok (result, journal', left) →
    (stack.map (·.object)).Nodup →
    (∀ ctx state, task = .run state → stack.head? = some ctx → journal.lookup ctx.object = some (some ctx.view)) →
    ObjectsRead config snapshot journal →
    ObjectsRead config snapshot journal' ∧
    (∀ ctx ∈ task.below stack,
        journal'.lookup ctx.object = journal.lookup ctx.object) ∧
      (∃ new, journal'.writes = journal.writes ++ new ∧ ∀ w ∈ new, w.before = w.viewed ∧
        admitWrite w.record w.facts (some w.before.value) w.after.value = .ok ()) ∧
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
            · rename_i view current
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
                      program.responseType, view, ⟨subject, height, call.target.value, callTurn,
                      stack.head?.map (·.object.value)⟩⟩ : Ctx) :: stack).map (·.object) |>.Nodup := by
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
                  obtain ⟨found, viewedEq, _, _, _, admitted⟩ := each w member
                  rw [viewed] at found
                  simp only [Option.some.injEq] at found
                  exact ⟨by rw [viewedEq, found], admitted⟩
        · cases ran
        · cases ran
        · cases ran

/-- **T2 (a): no object occurs twice on any call stack the executor enters**,
in every admitted invocation. -/
theorem invocation_reentry_free {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height : Nat} {request : InvokeRequest} (invoked : Invocation config snapshot height request) :
    ∀ frame ∈ invoked.journal.frames, frame.Nodup := by
  obtain ⟨_, _, _, ⟨new, frames, nodup⟩⟩ :=
    exec_invariant config snapshot height request.subject _ [] _ _ _ _ _ _ invoked.execExact (by simp)
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
      admitWrite w.record w.facts (some w.before.value) w.after.value = .ok () := by
  obtain ⟨_, _, ⟨new, writes, fresh⟩, _⟩ :=
    exec_invariant config snapshot height request.subject _ [] _ _ _ _ _ _ invoked.execExact (by simp)
      (by intro _ _ h; cases h) (by intro _ h; cases h)
  intro w member
  rw [writes] at member
  simp only [Journal.start, List.nil_append] at member
  exact fresh w member

/-- **What an invocation posts**: the Book, or the state cell of an object its
call tree read from the snapshot (the premise of the checkpoint invariant's
`state_post_safe`). -/
theorem Invocation.posts_shape {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height : Nat} {request : InvokeRequest} (invoked : Invocation config snapshot height request) :
    ∀ post ∈ invoked.posts, post = invoked.posted.write config snapshot ∨
      ∃ object current state, readState config snapshot object = .ok current ∧
        post = postAt snapshot (stateCell config.domain object) (stateImage object state) := by
  obtain ⟨read, _⟩ :=
    exec_invariant config snapshot height request.subject _ [] _ _ _ _ _ _ invoked.execExact (by simp)
      (by intro _ _ h; cases h) (by intro _ h; cases h)
  rw [invoked.postsExact]
  intro post member
  rcases List.mem_append.mp member with inJournal | isBook
  · right
    simp only [Journal.posts, List.mem_filterMap] at inJournal
    obtain ⟨entry, entryIn, made⟩ := inJournal
    obtain ⟨current, readOk⟩ := read entry entryIn
    split at made
    · cases found : entry.current with
      | none => simp [found] at made
      | some state =>
        simp only [found, Option.map_some, Option.some.injEq] at made
        exact ⟨entry.object, current, state, readOk, made.symm⟩
    · cases made
  · left; simpa using isBook

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
#assert_axioms Invocation.conserves

end Minidregg.Kernel.ObjectiveCall
