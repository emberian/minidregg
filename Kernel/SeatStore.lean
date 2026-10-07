/-
# Kernel.SeatStore — the seat world in stored cells, and the turns the seat kernel decides

The seat kernel (`Kernel.Seat`) decides over a `World`: a Book, a registry of
instances and invitations, and seats. On the native route that world lives in
cells of the seat kind (`Kernel.SeatCell`, protected coordinates) and in the
deployment's Book. A turn LOADS the part of the stored world it acts on (the
cells its request names, decoded strictly), runs the kernel's own transition
on it (`Seats.step`, `Seats.runPlan`: never a second transition function),
and writes back exactly the cells whose bodies changed, plus the Book under one
admitted batch. `Decided` carries the loaded world, the kernel's next world,
the batch and the posts, with the equations that tie them together; so every
kernel theorem (`step_inv`, `runPlan_posts`, `seat_conserves`, ...) holds of
what a decided turn commits (`Decided.inv`, `Decided.conserves`,
`Decided.seat_balances`).

Six turns:

* `publish`: a contract package (the stored artifact and its source package,
  `ObjectiveActivity.Stored`, whose artifact names `contractCodecId` and whose
  package this kernel's front end replays to the artifact's core,
  `replayPackage`; its definition is a function, not an `Activity`) into its
  content-addressed package cell; its payer is a registered Book account.
* `create`: instantiate a published package as a contract instance on an
  object: the instance cell (package pin, the instance's clause, its open seats).
* `handOver`: the holder moves an invitation.
* `offer`: present an invitation and a proposal; the seat's Book account is the
  seat cell's coordinate `H(offer transaction)`; the invitation is spent (its
  cell marked and its durable claim consumed); the seat joins the instance's
  open seats; an activity may be named as its holder (`holdings` cell).
* `invoke`: run the instance's own package method on the canonical view of its
  open seats (`callData`) and perform the Plan it returns (`decodePlan`,
  `Seats.runPlan`): reallocations judged by every touched seat's law and the
  instance's clause, mints under derived ids with the instance's own package,
  contract exits, termination. The declared envelope (`Config.covers`) is paid
  to the collector at the native tariff (`Tariff.workOf`).
* `exit`: a seat's offerer (on demand), anyone (after its deadline): the seat's
  whole allocation to its payee. Never consults the instance's clause.

Offerers are protected by offer safety, exit and conservation whoever invokes
the method; the contract can propose only what its code computes.
-/
import Kernel.Seat
import Kernel.SeatCell
import Kernel.ObjectiveKernelConfig
import Compiler.RefusalReason

namespace Minidregg.Kernel.SeatStore

open Minidregg.Theory Minidregg.Compiler
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Theory.TypedAuthorization (Digest SubjectId)
open Minidregg.Kernel.DurableDataIntent
open Minidregg.Kernel.ObjectiveActivityWire
open Minidregg.Theory.ObjectiveBendDemandData (Data)
open Minidregg.Theory.ObjectiveBendDemandMachine (initial runBounded)
open Minidregg.Compiler.ResourceBirthCodec (LifecycleImage)
open Minidregg.Theory.CanonicalResourceKernel (Book Batch Operation AccountId AssetId logicalBook AcceptedBatch registerAccounts applyOperations)
open Minidregg.Kernel.ObjectiveActivity (Config BookCell Postings loadBook postings postAt guardAt Stored
  decodeStored encodeStored replayPackage)
open Minidregg.Compiler.ObjectiveInvocationClaim (Capacity capacityStream)
open Minidregg.Kernel.Invitations
open Minidregg.Kernel.Seats
open Minidregg.Pred (Pred)
set_option autoImplicit false

abbrev Snapshot (rootBytes : Bytes → Digest) := DataSnapshot rootBytes

/-! ## Stored bodies -/

def proposalStream : StreamCodec Proposal :=
  let amounts := StreamCodec.list (StreamCodec.product StreamCodec.nat StreamCodec.nat)
  let exitRule : StreamCodec ExitRule := StreamCodec.xmap (StreamCodec.option StreamCodec.nat)
    (fun rule => match rule with | .onDemand => none | .afterDeadline due => some due)
    (fun wire => match wire with | none => .onDemand | some due => .afterDeadline due)
    (by intro rule; cases rule <;> rfl)
  StreamCodec.xmap (StreamCodec.product amounts (StreamCodec.product amounts (StreamCodec.product exitRule StreamCodec.bool)))
    (fun p => (p.give, p.want, p.exit, p.donate)) (fun w => ⟨w.1, w.2.1, w.2.2.1, w.2.2.2⟩)
    (by intro p; cases p; rfl)

def termsStream : StreamCodec (List (String × Nat)) :=
  StreamCodec.list (StreamCodec.product stringStream StreamCodec.nat)

def instanceStream : StreamCodec Instance :=
  StreamCodec.xmap (StreamCodec.product StreamCodec.nat (StreamCodec.product digestStream LawLeaf.predStream))
    (fun i => (i.id, i.package, i.clause)) (fun w => ⟨w.1, w.2.1, w.2.2⟩) (by intro i; cases i; rfl)

def invitationStream : StreamCodec Invitation :=
  StreamCodec.xmap
    (StreamCodec.product StreamCodec.nat (StreamCodec.product StreamCodec.nat (StreamCodec.product digestStream
      (StreamCodec.product stringStream (StreamCodec.product termsStream subjectStream)))))
    (fun v => (v.id, v.inst, v.package, v.role, v.terms, v.holder))
    (fun w => ⟨w.1, w.2.1, w.2.2.1, w.2.2.2.1, w.2.2.2.2.1, w.2.2.2.2.2⟩) (by intro v; cases v; rfl)

def seatStream : StreamCodec Seat :=
  StreamCodec.xmap
    (StreamCodec.product StreamCodec.nat (StreamCodec.product StreamCodec.nat (StreamCodec.product subjectStream
      (StreamCodec.product StreamCodec.nat (StreamCodec.product proposalStream
        (StreamCodec.option StreamCodec.nat))))))
    (fun s => (s.account, s.inst, s.offerer, s.payee, s.proposal, s.holder))
    (fun w => ⟨w.1, w.2.1, w.2.2.1, w.2.2.2.1, w.2.2.2.2.1, w.2.2.2.2.2⟩) (by intro s; cases s; rfl)

/-- An instance cell: the instance, its OPEN seats (the index its method sees),
and whether it was terminated. -/
structure InstanceBody where
  inst : Instance
  seats : List AccountId
  retired : Bool
  deriving DecidableEq, Repr

/-- An invitation cell: the invitation and whether an offer spent it. -/
structure InvitationBody where
  invitation : Invitation
  spent : Bool
  deriving DecidableEq, Repr

/-- A seat cell: the kernel's seat, the role and terms of the invitation
that made it, and the height of the offer that opened it (what the contract's
method is shown). -/
structure SeatBody where
  seat : Seat
  role : String
  terms : List (String × Nat)
  opened : Nat
  deriving DecidableEq, Repr

def instanceBodyStream : StreamCodec InstanceBody :=
  StreamCodec.xmap (StreamCodec.product instanceStream
      (StreamCodec.product (StreamCodec.list StreamCodec.nat) StreamCodec.bool))
    (fun b => (b.inst, b.seats, b.retired)) (fun w => ⟨w.1, w.2.1, w.2.2⟩) (by intro b; cases b; rfl)

def invitationBodyStream : StreamCodec InvitationBody :=
  StreamCodec.xmap (StreamCodec.product invitationStream StreamCodec.bool)
    (fun b => (b.invitation, b.spent)) (fun w => ⟨w.1, w.2⟩) (by intro b; cases b; rfl)

def seatBodyStream : StreamCodec SeatBody :=
  StreamCodec.xmap (StreamCodec.product seatStream
      (StreamCodec.product stringStream (StreamCodec.product termsStream StreamCodec.nat)))
    (fun b => (b.seat, b.role, b.terms, b.opened)) (fun w => ⟨w.1, w.2.1, w.2.2.1, w.2.2.2⟩)
    (by intro b; cases b; rfl)

def instanceCodec := framed "DREGG/SEAT/INSTANCE/v1".toUTF8.toList instanceBodyStream
def invitationCodec := framed "DREGG/SEAT/INVITATION/v1".toUTF8.toList invitationBodyStream
/-- Frame v3: a seat body no longer carries an open flag (a closed seat's cell is
retired, never rewritten) and its proposal carries the donation marker; a v1 or v2 body refuses
to decode. -/
def seatCodec := framed "DREGG/SEAT/SEAT/v4".toUTF8.toList seatBodyStream
def holdingsCodec := framed "DREGG/SEAT/HOLDINGS/v1".toUTF8.toList (StreamCodec.list StreamCodec.nat)

/-! ## Cells: protected coordinates -/

def instanceKey (inst : InstanceId) : Bytes := StreamCodec.nat.encode inst
def invitationKey (id : InvitationId) : Bytes := StreamCodec.nat.encode id
def holdingsKey (record : Nat) : Bytes := StreamCodec.nat.encode record
def packageKey (pin : Digest) : Bytes := digestStream.encode pin
def seatKey (transaction : TransactionId) : Bytes := digestStream.encode transaction

def instanceCell (domain : Digest) (inst : InstanceId) : CellId :=
  ⟨SeatCell.coordinate domain .inst (instanceKey inst)⟩
def invitationCell (domain : Digest) (id : InvitationId) : CellId :=
  ⟨SeatCell.coordinate domain .invitation (invitationKey id)⟩
def holdingsCell (domain : Digest) (record : Nat) : CellId :=
  ⟨SeatCell.coordinate domain .holdings (holdingsKey record)⟩
def packageCell (domain : Digest) (pin : Digest) : CellId :=
  ⟨SeatCell.coordinate domain .package (packageKey pin)⟩

/-- **A seat's Book account is its seat cell's coordinate**, keyed by the
offer's transaction: the offerer never names it. -/
def seatAccount (domain : Digest) (transaction : TransactionId) : AccountId :=
  SeatCell.coordinate domain .seat (seatKey transaction)

def seatCell (account : AccountId) : CellId := ⟨account⟩

theorem seatAccount_protected (domain : Digest) (transaction : TransactionId) :
    reservedBase ≤ seatAccount domain transaction := SeatCell.coordinate_reserved _ _ _

/-- The registry image of a seat-kind cell. -/
def image (role : SeatCell.Role) (key body : Bytes) : Bytes :=
  LifecycleImage.bytes CanonicalCellRegistry.registry (.live ⟨.seat, SeatCell.cellOf ⟨role, key, body⟩⟩)

def payloadOf (bytes : Bytes) : Option SeatCell.Payload :=
  match (LifecycleImage.codec CanonicalCellRegistry.registry).decode bytes with
  | some (.live ⟨.seat, payload⟩) => SeatCell.payloadAt payload.logical
  | _ => none

def bodyOf (role : SeatCell.Role) (bytes : Bytes) : Option Bytes := do
  let payload ← payloadOf bytes
  if payload.role = role then some payload.body else none

def instanceImage (body : InstanceBody) : Bytes :=
  image .inst (instanceKey body.inst.id) (instanceCodec.encode body)
def invitationImage (body : InvitationBody) : Bytes :=
  image .invitation (invitationKey body.invitation.id) (invitationCodec.encode body)
/-- A seat image needs its key: the offer transaction its coordinate hashes. -/
def seatImage (key : Bytes) (body : SeatBody) : Bytes := image .seat key (seatCodec.encode body)
def holdingsImage (record : Nat) (seats : List AccountId) : Bytes :=
  image .holdings (holdingsKey record) (holdingsCodec.encode seats)

def readInstance {rootBytes : Bytes → Digest} (snapshot : Snapshot rootBytes) (domain : Digest)
    (inst : InstanceId) : Option InstanceBody :=
  (bodyOf .inst (snapshot.canonicalBytes (instanceCell domain inst))).bind instanceCodec.decode
def readInvitation {rootBytes : Bytes → Digest} (snapshot : Snapshot rootBytes) (domain : Digest)
    (id : InvitationId) : Option InvitationBody :=
  (bodyOf .invitation (snapshot.canonicalBytes (invitationCell domain id))).bind invitationCodec.decode
/-- A seat cell's body. A seat is written once, at its offer, and then retired:
no turn rewrites a live seat cell, so its key is never needed again. -/
def readSeat {rootBytes : Bytes → Digest} (snapshot : Snapshot rootBytes) (account : AccountId) :
    Option SeatBody := do
  let payload ← payloadOf (snapshot.canonicalBytes (seatCell account))
  if payload.role = .seat then
    let body ← seatCodec.decode payload.body
    if body.seat.account = account then some body else none
  else none
def readHoldings {rootBytes : Bytes → Digest} (snapshot : Snapshot rootBytes) (domain : Digest)
    (record : Nat) : List AccountId :=
  ((bodyOf .holdings (snapshot.canonicalBytes (holdingsCell domain record))).bind holdingsCodec.decode).getD []

/-! ## Refusals -/

inductive Refusal where
  | kernel (reason : Seats.Refusal)
  | program (reason : ObjectiveActivity.Refusal)
  | packageMissing | packageExists | notAContract (reason : String)
  | instanceMissing (inst : InstanceId)
  | cellUndecodable (cell : Nat)
  /-- An offer onto a seat cell that is retired (its seat closed) or already holds a seat: a seat
  account is its cell's coordinate and is never reused. -/
  | seatRetired (account : AccountId) | seatExists (account : AccountId)
  /-- A post of a seat turn or of an ending activity's closing would sit on, or write, a
  kernel-activity cell (`checkInert`). -/
  | activityCellInSeatSpace (cell : Nat)
  | inputUndecodable
  | plan (reason : String)
  | methodYielded | methodFaulted (reason : String)
  | uncovered (envelope : Capacity)
  | payerInvalid (account : AccountId)
  | bookUnavailable | bookRefused
  deriving Repr

def kernel {α : Type} : Except Seats.Refusal α → Except Refusal α
  | .ok value => .ok value
  | .error reason => .error (.kernel reason)

def program {α : Type} : Except ObjectiveActivity.Refusal α → Except Refusal α
  | .ok value => .ok value
  | .error reason => .error (.program reason)

/-! ## The contract method: its view and its Plan

The method's input is canonical and total: the caller's `input`, the height,
and the instance's OPEN seats sorted by coordinate, each with its role, terms,
proposal, its exit rule (`onDemand {}` | `afterDeadline h`: the rule the kernel
judges `exitAuthorized` by), the height at which its offer opened it (`opened`, the
height of the admitting turn, written once into the seat cell), and its
allocation over EVERY asset its proposal names (the total view, as the law
reads it). The method never sees a funding account or anything
outside the instance's open seats, and `Seats.step` refuses any transfer outside
them (`addressed`). Lists are `nil {}` / `cons {head, tail}` sums. -/

def listData : List Data → Data
  | [] => .variant "nil" (.record [])
  | head :: tail => .variant "cons" (.record [("head", head), ("tail", listData tail)])

def amountsData (entries : List (AssetId × Nat)) : Data :=
  listData (entries.map fun entry => .record [("asset", .natural entry.1), ("amount", .natural entry.2)])

def termsData (terms : List (String × Nat)) : Data :=
  listData (terms.map fun term => .record [("name", .label term.1), ("value", .natural term.2)])

def exitData : ExitRule → Data
  | .onDemand => .variant "onDemand" (.record [])
  | .afterDeadline due => .variant "afterDeadline" (.natural due)

def seatView (book : Book) (body : SeatBody) : Data :=
  .record [("seat", .natural body.seat.account), ("role", .label body.role), ("terms", termsData body.terms),
    ("give", amountsData body.seat.proposal.give), ("want", amountsData body.seat.proposal.want),
    ("exit", exitData body.seat.proposal.exit), ("opened", .natural body.opened),
    ("allocation", amountsData (body.seat.proposal.assets.map fun asset =>
      (asset, (book.balance body.seat.account asset).toNat)))]

def sortSeats (seats : List SeatBody) : List SeatBody :=
  seats.mergeSort fun a b => decide (a.seat.account ≤ b.seat.account)

def callData (input : Data) (height : Nat) (book : Book) (seats : List SeatBody) : Data :=
  .record [("input", input), ("height", .natural height),
    ("seats", listData ((sortSeats seats).map (seatView book)))]

def natField (fields : List (String × Data)) (name : String) : Option Nat :=
  match ObjectiveActivity.fieldOf fields name with
  | some (.natural value) => some value
  | _ => none

def labelField (fields : List (String × Data)) (name : String) : Option String :=
  match ObjectiveActivity.fieldOf fields name with
  | some (.label value) => some value
  | _ => none

def decodeList {α : Type} (item : Data → Option α) : Nat → Data → Option (List α)
  | 0, _ => none
  | _ + 1, .variant "nil" _ => some []
  | fuel + 1, .variant "cons" (.record fields) => do
    let head ← ObjectiveActivity.fieldOf fields "head"
    let tail ← ObjectiveActivity.fieldOf fields "tail"
    pure ((← item head) :: (← decodeList item fuel tail))
  | _ + 1, _ => none

def decodeTransfer : Data → Option Transfer
  | .record fields => do
    pure ⟨← natField fields "source", ← natField fields "destination", ← natField fields "asset",
      ← natField fields "amount"⟩
  | _ => none

def decodeTerm : Data → Option (String × Nat)
  | .record fields => do pure (← labelField fields "name", ← natField fields "value")
  | _ => none

def decodeAction (fuel : Nat) : Data → Option PlanAction
  | .variant "reallocate" (.record fields) => do
    pure (.reallocate (← decodeList decodeTransfer fuel (← ObjectiveActivity.fieldOf fields "moves")))
  | .variant "mint" (.record fields) => do
    pure (.mint (← labelField fields "role") (← decodeList decodeTerm fuel (← ObjectiveActivity.fieldOf fields "terms"))
      ⟨← natField fields "holder"⟩)
  | .variant "exit" (.record fields) => do pure (.exit (← natField fields "seat"))
  | .variant "terminate" _ => some .terminate
  | _ => none

/-- The Plan a method returned: a list of `reallocate {moves}`, `mint {role,
terms, holder}`, `exit {seat}`, `terminate {}`. The same members an
offer-triggered resident contract (an activity) will one day yield. -/
def decodePlan (fuel : Nat) (data : Data) : Except Refusal (List PlanAction) :=
  match decodeList (decodeAction fuel) fuel data with
  | some plan => .ok plan
  | none => .error (.plan "the method must return a list of reallocate | mint | exit | terminate")

/-- The output codec a contract artifact names: its entry is a function from
the call to a Plan, never an `Activity`. -/
def contractCodecId : Digest := tagged "DREGG/SEAT/CONTRACT/OUTPUT-CODEC/v1" []

/-- Re-execute the instance's method: replay its stored package and
instantiate the replayed definition with the call (typed at its declared
domain; `Instantiated.runs_front_end_output`), run it to completion within the
declared envelope, and extract its result. A method that yields, diverges,
refuses or exhausts its envelope commits nothing. -/
def runMethod (config : Config) (bytes : Bytes) (pin : Digest) (call : Data) (envelope : Capacity) :
    Except Refusal Data := do
  if !config.covers envelope then throw (.uncovered envelope)
  let ticks := envelope.sourceTicks
  let instantiated ← program (ObjectiveActivity.instantiate config bytes pin call)
  match instantiated.checked.type with
  | .computation _ _ _ => throw (.notAContract "the method returns an Activity")
  | _ =>
    match runBounded config.limits ticks (initial instantiated.applied.erase) with
    | .finished _ finished =>
      match ObjectiveBendDemandData.complete config.limits config.planBudget finished with
      | .ok result => pure result.value
      | .error (failure, _) => throw (.program (.resultExtraction (reprStr failure)))
    | .yielded _ _ => throw .methodYielded
    | .divergent _ _ => throw (.methodFaulted "divergent")
    | .refused reason _ => throw (.methodFaulted (reprStr reason))
    | .suspended _ _ => throw (.program .exhausted)

/-! ## Loading a part of the stored world -/

/-- The cells a turn loaded, decoded. -/
structure Loaded where
  instances : List InstanceBody := []
  invitations : List InvitationBody := []
  seats : List SeatBody := []
  holdings : List (Nat × List AccountId) := []
  deriving Repr

/-- The kernel's world over what a turn loaded and the loaded Book. -/
def Loaded.world (loaded : Loaded) (book : Book) : World where
  book := book
  registry :=
    { instances := (loaded.instances.filter fun body => !body.retired).map InstanceBody.inst
      live := (loaded.invitations.filter fun body => !body.spent).map InvitationBody.invitation
      spent := (loaded.invitations.filter InvitationBody.spent).map fun body => body.invitation.id
      retired := (loaded.instances.filter InstanceBody.retired).map fun body => body.inst.id }
  seats := loaded.seats.map SeatBody.seat

/-- The instance's open-seat index after a turn: the loaded index without the
seats the turn closed (a seat that was loaded and is gone from the next world),
then the instance's seats it opened. The index keeps its order: surviving seats
in the order they were opened, new ones after. -/
def openIndex (base loaded : List AccountId) (next : List Seat) (inst : InstanceId) : List AccountId :=
  base.filter (fun account => !loaded.contains account || next.any fun seat => seat.account == account) ++
    ((next.filter fun seat => seat.inst == inst && !(base.contains seat.account)).map Seat.account)

def changed {rootBytes : Bytes → Digest} (snapshot : Snapshot rootBytes) (cell : CellId) (bytes : Bytes) :
    Option Post :=
  if bytes = snapshot.canonicalBytes cell then none else some (postAt snapshot cell bytes)

/-- A seat that is new in this turn: its coordinate's key and the role and
terms of the invitation that made it. -/
structure Fresh where
  key : Bytes
  role : String
  terms : List (String × Nat)
  opened : Nat

/-- The posts that write the next world's changed cells: seats, invitations,
instances, holdings. A cell whose body did not change is not written (it is
guarded). A seat a turn closed is gone from the next world: its cell is RETIRED
(the registry's retired lifecycle image, the activity record's precedent: never
reused, the id enters the World's retired set), one post per loaded seat the next
world no longer holds. A live seat cell is never rewritten (a seat does not
change after its offer). -/
def statePosts {rootBytes : Bytes → Digest} (domain : Digest) (snapshot : Snapshot rootBytes)
    (loaded : Loaded) (fresh : Option Fresh) (next : World) : List Post :=
  let retired := (loaded.seats.filter fun body =>
      !(next.seats.any fun seat => seat.account == body.seat.account)).map fun body =>
    postAt snapshot (seatCell body.seat.account) ObjectiveActivity.retiredImage
  let opened := next.seats.filterMap fun seat =>
    if loaded.seats.any (fun body => body.seat.account == seat.account) then none
    else fresh.bind fun made =>
        changed snapshot (seatCell seat.account) (seatImage made.key ⟨seat, made.role, made.terms, made.opened⟩)
  let invitations :=
    (next.registry.live.map fun invitation => (⟨invitation, false⟩ : InvitationBody)) ++
      loaded.invitations.filterMap fun body =>
        if next.registry.spent.contains body.invitation.id then some { body with spent := true } else none
  let invitationPosts := invitations.filterMap fun body =>
    changed snapshot (invitationCell domain body.invitation.id) (invitationImage body)
  let ids := (loaded.instances.map (fun body => body.inst.id) ++ next.registry.instances.map Instance.id).dedup
  let instancePosts := ids.filterMap fun id =>
    let base := ((loaded.instances.find? fun body => body.inst.id == id).map InstanceBody.seats).getD []
    let inst := (next.registry.instance? id).orElse fun _ =>
      (loaded.instances.find? fun body => body.inst.id == id).map InstanceBody.inst
    inst.bind fun inst =>
      changed snapshot (instanceCell domain id)
        (instanceImage ⟨inst, openIndex base (loaded.seats.map fun body => body.seat.account) next.seats id,
          next.registry.retired.contains id⟩)
  let made := next.seats.filter fun seat => !(loaded.seats.any fun body => body.seat.account == seat.account)
  let holdingsPosts := (made.filterMap Seat.holder).dedup.filterMap fun record =>
    changed snapshot (holdingsCell domain record)
      (holdingsImage record (((loaded.holdings.lookup record).getD []) ++
        (made.filter fun seat => seat.holder == some record).map Seat.account))
  retired ++ opened ++ invitationPosts ++ instancePosts ++ holdingsPosts

/-- Guards on every loaded cell: a decision is bound to the state it read. -/
def loadedCells (domain : Digest) (loaded : Loaded) : List CellId :=
  loaded.instances.map (fun body => instanceCell domain body.inst.id) ++
    loaded.invitations.map (fun body => invitationCell domain body.invitation.id) ++
    loaded.seats.map (fun body => seatCell body.seat.account) ++
    loaded.holdings.map (fun entry => holdingsCell domain entry.1)

/-! ## What the kernel ran -/

/-- The kernel transition a turn ran on its loaded world: nothing (a
publication), one `Seats.step`, a method's Plan (`Seats.runPlan`), or an
activity's end (`Seats.closeHeld`). -/
inductive KernelRun (height : Nat) (world : World) : World → Batch → Prop
  | nothing : KernelRun height world world noPostings
  | stepped {actor : Actor} {action : Action} {next : World} {batch : Batch} :
      Seats.step world height actor action = .ok (next, batch) → KernelRun height world next batch
  | planned {inst : Instance} {mintId : Nat → InvitationId} {plan : List PlanAction} {next : World} {batch : Batch} :
      runPlan height inst mintId world 0 plan = .ok (next, batch) → KernelRun height world next batch
  | ended {record : Nat} {next : World} {batch : Batch} :
      closeHeld world height record = .ok (next, batch) → KernelRun height world next batch

theorem KernelRun.posts {height : Nat} {world next : World} {batch : Batch}
    (run : KernelRun height world next batch) : Posts world.book batch next.book := by
  cases run with
  | nothing => exact posts_none _
  | stepped ran => exact (step_posts ran).1
  | planned ran => exact (runPlan_posts ran).1
  | ended ran => exact (exitEach_posts ran).1

theorem KernelRun.reachable {height : Nat} {genesis world next : World} {batch : Batch}
    (run : KernelRun height world next batch) (reachable : Reachable genesis world) : Reachable genesis next := by
  cases run with
  | nothing => exact reachable
  | stepped ran => exact Reachable.admit height _ _ reachable ran
  | planned ran => exact runPlan_reachable reachable ran
  | ended ran => exact closeHeld_reachable reachable ran

/-- Every kernel run preserves the seat invariant (T3 (a)'s inductive step). -/
theorem KernelRun.inv {height : Nat} {world next : World} {batch : Batch}
    (run : KernelRun height world next batch) (inv : Inv world) : Inv next :=
  reachable_inv_from inv (run.reachable Reachable.start)
where
  reachable_inv_from {world next : World} (inv : Inv world) (reachable : Reachable world next) : Inv next := by
    induction reachable with
    | start => exact inv
    | admit _ _ _ _ admitted ih => exact step_inv ih admitted

/-! ## Turns -/

/-- A seat turn as the kernel decides it (the signed command adds the
capabilities that authorize it, `Kernel.SeatReceiver`). -/
inductive Turn where
  | publish (stored : Bytes)
  | create (inst : InstanceId) (pin : Digest) (clause : Pred)
  | handOver (id : InvitationId) (recipient : SubjectId)
  | offer (id : InvitationId) (expect : Expectation) (funding payee : AccountId) (proposal : Proposal)
      (holder : Option Nat)
  | invoke (inst : InstanceId) (input : Bytes) (envelope : Capacity) (account : AccountId)
  | exit (seat : AccountId)
  deriving DecidableEq, Repr

abbrev TurnWire :=
  Sum Bytes (Sum (Nat × Digest × Pred) (Sum (Nat × SubjectId)
    (Sum (Nat × (Nat × Digest × String) × Nat × Nat × Proposal × Option Nat)
      (Sum (Nat × Bytes × Capacity × Nat) Nat))))

def Turn.toWire : Turn → TurnWire
  | .publish artifact => .inl artifact
  | .create inst pin clause => .inr (.inl (inst, pin, clause))
  | .handOver invitation recipient => .inr (.inr (.inl (invitation, recipient)))
  | .offer invitation expect funding payee proposal holder =>
      .inr (.inr (.inr (.inl (invitation, (expect.inst, expect.package, expect.role), funding, payee, proposal, holder))))
  | .invoke inst input envelope account => .inr (.inr (.inr (.inr (.inl (inst, input, envelope, account)))))
  | .exit seat => .inr (.inr (.inr (.inr (.inr seat))))

def Turn.ofWire : TurnWire → Turn
  | .inl artifact => .publish artifact
  | .inr (.inl (inst, pin, clause)) => .create inst pin clause
  | .inr (.inr (.inl (invitation, recipient))) => .handOver invitation recipient
  | .inr (.inr (.inr (.inl (invitation, (i, p, r), funding, payee, proposal, holder)))) =>
      .offer invitation ⟨i, p, r⟩ funding payee proposal holder
  | .inr (.inr (.inr (.inr (.inl (inst, input, envelope, account))))) => .invoke inst input envelope account
  | .inr (.inr (.inr (.inr (.inr seat)))) => .exit seat

def turnStream : StreamCodec Turn :=
  StreamCodec.xmap
    (StreamCodec.sum bytesStream
      (StreamCodec.sum (StreamCodec.product StreamCodec.nat (StreamCodec.product digestStream LawLeaf.predStream))
        (StreamCodec.sum (StreamCodec.product StreamCodec.nat subjectStream)
          (StreamCodec.sum
            (StreamCodec.product StreamCodec.nat
              (StreamCodec.product (StreamCodec.product StreamCodec.nat (StreamCodec.product digestStream stringStream))
                (StreamCodec.product StreamCodec.nat (StreamCodec.product StreamCodec.nat
                  (StreamCodec.product proposalStream (StreamCodec.option StreamCodec.nat))))))
            (StreamCodec.sum
              (StreamCodec.product StreamCodec.nat (StreamCodec.product bytesStream
                (StreamCodec.product capacityStream StreamCodec.nat)))
              StreamCodec.nat)))))
    Turn.toWire Turn.ofWire (by intro turn; cases turn <;> rfl)

/-- The pin a publication's stored bytes name (0 when they do not decode). -/
def publishedPin (stored : Bytes) : Digest :=
  ((decodeStored stored).bind fun s => (ObjectiveBendSourceArtifact.decode s.artifact).map
    ObjectiveBendSourceArtifact.identity).getD ⟨0⟩

structure Request where
  subject : SubjectId
  nonce : Nat
  turn : Turn
  deriving DecidableEq, Repr

/-- The transaction a turn commits under. A publication's is its package pin
(publishing the same package twice is one transaction); every other turn's
is its signer, nonce and exact turn bytes, so a retry finds its record. -/
def transactionOf (request : Request) : TransactionId :=
  match request.turn with
  | .publish stored => tagged "DREGG/SEAT/TX/PUBLISH/v1" (digestStream.encode (publishedPin stored))
  | turn => tagged "DREGG/SEAT/TX/v1"
      (subjectStream.encode request.subject ++ StreamCodec.nat.encode request.nonce ++ turnStream.encode turn)

/-- The id of the `index`-th member of the Plan an invoking turn performs, if
it mints: a digest of the turn and the instance, so the contract never chooses
an id (a re-mint of a spent id would need a digest collision). -/
def mintId (transaction : TransactionId) (inst : InstanceId) (index : Nat) : InvitationId :=
  (tagged "DREGG/SEAT/INVITATION-ID/v1"
    (digestStream.encode transaction ++ StreamCodec.nat.encode inst ++ StreamCodec.nat.encode index)).value

/-- The domain of seat claims. -/
def domain : Digest := tagged "DREGG/SEAT/DOMAIN/v1" []

/-- An invitation's durable claim: an offer consumes it, so an invitation
is spent at most once whatever its cell says. -/
def invitationClaim (id : InvitationId) : StableNullifier :=
  { codecVersion := 1, domain := domain,
    nullifierId := tagged "DREGG/SEAT/CLAIM/invitation" (StreamCodec.nat.encode id),
    canonicalBytes := "invitation".toUTF8.toList ++ StreamCodec.nat.encode id }

/-- The one kernel step a signed turn is (an invocation runs a Plan instead;
a publication runs nothing). -/
def Turn.kernelAction (domain : Digest) (transaction : TransactionId) (subject : SubjectId) :
    Turn → Option (Actor × Action)
  | .create inst pin clause => some (.subject subject, .create ⟨inst, pin, clause⟩)
  | .handOver invitation recipient => some (.subject subject, .handOver invitation recipient)
  | .offer invitation expect funding payee proposal holder =>
      some (.subject subject, .offer invitation expect (seatAccount domain transaction) funding payee proposal holder)
  | .exit seat => some (.subject subject, .exit seat)
  | .publish _ | .invoke _ _ _ _ => none

/-- The claims a turn consumes: an offer spends its invitation's. -/
def Turn.claims : Turn → List StableNullifier
  | .offer invitation _ _ _ _ _ => [invitationClaim invitation]
  | _ => []

/-! ## A decided turn -/

def packageBytes {rootBytes : Bytes → Digest} (domain : Digest) (snapshot : Snapshot rootBytes)
    (pin : Digest) : Bytes :=
  (bodyOf .package (snapshot.canonicalBytes (packageCell domain pin))).getD []

def bookPost {rootBytes : Bytes → Digest} (config : Config) (snapshot : Snapshot rootBytes) {pre : BookCell}
    {batch : Batch} (accepted : AcceptedBatch pre batch) : List Post :=
  if batch = noPostings then []
  else [postAt snapshot config.bookCell
    (LifecycleImage.bytes CanonicalCellRegistry.registry (.live ⟨.resourceBook, accepted.post⟩))]

/-! ## Seat posts never touch a kernel-activity cell

The seat kernel writes its own protected coordinates under the object kernel's
facet (`ControlFacet.objectKernel`), which the ordinary gate does not judge. What
keeps that sound for the activity side is this check, made by the kernel itself on
every seat turn and every closing: no post sits on a cell that holds a
kernel-activity cell, and none writes one. The checkpoint invariant
(`ObjectiveCheckpointInvariant.Step.inert`) needs nothing else about seat cells,
in particular no coordinate-disjointness assumption. -/

/-- The post sits on, or writes, a kernel-activity cell. -/
def touchesActivity {rootBytes : Bytes → Digest} (snapshot : Snapshot rootBytes) (post : Post) : Bool :=
  (ObjectiveActivity.payloadOf (snapshot.canonicalBytes post.cell)).isSome ||
    (ObjectiveActivity.payloadOf post.bytes).isSome

/-- Every post leaves kernel-activity cells alone: the cell it sits on holds none,
and it writes none. -/
def Inert {rootBytes : Bytes → Digest} (snapshot : Snapshot rootBytes) (posts : List Post) : Prop :=
  ∀ post ∈ posts, ObjectiveActivity.payloadOf (snapshot.canonicalBytes post.cell) = none ∧
    ObjectiveActivity.payloadOf post.bytes = none

theorem inert_of_find {rootBytes : Bytes → Digest} {snapshot : Snapshot rootBytes} {posts : List Post}
    (none : posts.find? (touchesActivity snapshot) = none) : Inert snapshot posts := by
  intro post member
  have untouched := List.find?_eq_none.mp none post member
  simp only [touchesActivity, Bool.or_eq_true, Option.isSome_iff_ne_none, ne_eq, not_or, Decidable.not_not] at untouched
  exact untouched

/-- Check `Inert`, refusing by the first offending cell. -/
def checkInert {rootBytes : Bytes → Digest} (snapshot : Snapshot rootBytes) (posts : List Post) :
    Except Refusal (PLift (Inert snapshot posts)) :=
  match found : posts.find? (touchesActivity snapshot) with
  | none => .ok ⟨inert_of_find found⟩
  | some post => .error (.activityCellInSeatSpace post.cell.value)

/-- A turn the seat kernel decided: the loaded cells and Book, the kernel's run
on them, the fees, the ONE admitted batch on the loaded Book, and the posts. -/
structure Decided {rootBytes : Bytes → Digest} (config : Config) (snapshot : Snapshot rootBytes)
    (height : Nat) (request : Request) where
  private mk ::
  loaded : Loaded
  book : BookCell
  bookExact : loadBook config snapshot = .ok book
  world : World
  worldExact : world = loaded.world (logicalBook book.logical)
  next : World
  batch : Batch
  run : KernelRun height world next batch
  fees : Batch
  feesNone : fees.registrations = []
  accepted : AcceptedBatch book (seqBatch batch fees)
  fresh : Option Fresh
  extra : List Post
  posts : List Post
  postsExact : posts = extra ++ statePosts config.domain snapshot loaded fresh next ++ bookPost config snapshot accepted
  /-- The kernel checked it (`checkInert`). -/
  inert : Inert snapshot posts
  guards : List ReadGuard
  nullifiers : List StableNullifier
  nullifiersExact : nullifiers = request.turn.claims
  /-- A signed step turn ran exactly the kernel step it names. -/
  stepExact : ∀ actor action, request.turn.kernelAction config.domain (transactionOf request) request.subject =
    some (actor, action) → Seats.step world height actor action = .ok (next, batch)

def Decided.intent {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height : Nat} {request : Request} (decided : Decided config snapshot height request) (sealing : Seal) :
    DataIntent rootBytes :=
  intentOf rootBytes (transactionOf request) decided.posts decided.guards decided.nullifiers sealing

/-- **A decided turn conserves every asset**: its postings are one admitted
batch on the loaded Book. -/
theorem Decided.conserves {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height : Nat} {request : Request} (decided : Decided config snapshot height request) (asset : AssetId) :
    (logicalBook decided.accepted.post.logical).totalAsset asset = (logicalBook decided.book.logical).totalAsset asset :=
  decided.accepted.conserves asset

/-- **The seat invariant holds of what a decided turn commits**: if it held of
the loaded world, it holds of the kernel's next world, whose seats are exactly
what the turn's seat posts encode. -/
theorem Decided.inv {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height : Nat} {request : Request} (decided : Decided config snapshot height request)
    (inv : Inv decided.world) : Inv decided.next :=
  decided.run.inv inv

/-- **The committed Book is the kernel's next Book with the fees applied**:
the fees move value only between the payer and the collector. -/
theorem Decided.book_post {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height : Nat} {request : Request} (decided : Decided config snapshot height request) :
    logicalBook decided.accepted.post.logical = decided.fees.apply decided.next.book := by
  rw [AcceptedBatch.post_logicalBook]
  have posts := decided.run.posts
  rw [decided.worldExact] at posts
  simp only [Loaded.world] at posts
  rw [posts.2]
  unfold Batch.apply seqBatch
  simp only [decided.feesNone, List.append_nil, applyOperations_append_eq, registerAccounts,
    applyOperations_deregisterAccounts, deregisterAccounts_append]

/-! ## Deciding a turn -/

def present {rootBytes : Bytes → Digest} (snapshot : Snapshot rootBytes) (cell : CellId) : Bool :=
  (payloadOf (snapshot.canonicalBytes cell)).isSome

/-- A present cell must decode, and decode as itself: an undecodable cell is
refused, never read as absent. -/
def loadInstance {rootBytes : Bytes → Digest} (snapshot : Snapshot rootBytes) (domain : Digest)
    (inst : InstanceId) : Except Refusal (Option InstanceBody) :=
  if present snapshot (instanceCell domain inst) then
    match readInstance snapshot domain inst with
    | some body => if body.inst.id = inst then .ok (some body) else .error (.cellUndecodable (instanceCell domain inst).value)
    | none => .error (.cellUndecodable (instanceCell domain inst).value)
  else .ok none

def loadInvitation {rootBytes : Bytes → Digest} (snapshot : Snapshot rootBytes) (domain : Digest)
    (id : InvitationId) : Except Refusal (Option InvitationBody) :=
  if present snapshot (invitationCell domain id) then
    match readInvitation snapshot domain id with
    | some body => if body.invitation.id = id then .ok (some body)
        else .error (.cellUndecodable (invitationCell domain id).value)
    | none => .error (.cellUndecodable (invitationCell domain id).value)
  else .ok none

def loadSeat {rootBytes : Bytes → Digest} (snapshot : Snapshot rootBytes) (account : AccountId) :
    Except Refusal (Option SeatBody) :=
  if present snapshot (seatCell account) then
    match readSeat snapshot account with
    | some entry => .ok (some entry)
    | none => .error (.cellUndecodable account)
  else .ok none

def requireSeat {rootBytes : Bytes → Digest} (snapshot : Snapshot rootBytes) (account : AccountId) :
    Except Refusal SeatBody := do
  match ← loadSeat snapshot account with
  | some entry => pure entry
  | none => throw (.cellUndecodable account)

/-- Assemble a decision: the fees after the kernel's batch, admitted as ONE
batch on the loaded Book. -/
def finish {rootBytes : Bytes → Digest} (config : Config) (snapshot : Snapshot rootBytes) (height : Nat)
    (request : Request) (loaded : Loaded) (book : BookCell) (bookExact : loadBook config snapshot = .ok book)
    (next : World) (batch : Batch) (run : KernelRun height (loaded.world (logicalBook book.logical)) next batch)
    (fees : Batch) (feesNone : fees.registrations = []) (fresh : Option Fresh) (extra : List Post)
    (cells : List CellId) (nullifiers : List StableNullifier) (nullifiersExact : nullifiers = request.turn.claims)
    (stepExact : ∀ actor action, request.turn.kernelAction config.domain (transactionOf request) request.subject =
      some (actor, action) → Seats.step (loaded.world (logicalBook book.logical)) height actor action = .ok (next, batch)) :
    Except Refusal (Decided config snapshot height request) :=
  if admitted : (seqBatch batch fees).Admission (logicalBook book.logical) then do
    let accepted := AcceptedBatch.ofAdmission admitted
    let ⟨inert⟩ ← checkInert snapshot
      (extra ++ statePosts config.domain snapshot loaded fresh next ++ bookPost config snapshot accepted)
    .ok ⟨loaded, book, bookExact, _, rfl, next, batch, run, fees, feesNone, accepted, fresh, extra, _, rfl, inert,
      (loadedCells config.domain loaded ++ cells).map (guardAt snapshot), nullifiers, nullifiersExact, stepExact⟩
  else .error .bookRefused

/-- The kernel's decision of an offer turn: the invitation, its instance and the activity holdings
loaded, the seat account (its cell's coordinate) required to sit on a FRESH cell, then the kernel's
own `Seats.step`. -/
def decideOffer {rootBytes : Bytes → Digest} (config : Config) (snapshot : Snapshot rootBytes) (height : Nat)
    (request : Request) (book : BookCell) (bookExact : loadBook config snapshot = .ok book)
    (invitation : InvitationId) (expect : Expectation) (funding payee : AccountId) (proposal : Proposal)
    (holder : Option Nat)
    (hturn : request.turn = .offer invitation expect funding payee proposal holder) :
    Except Refusal (Decided config snapshot height request) := do
  let logical := logicalBook book.logical
  let transaction := transactionOf request
  let domain := config.domain
  let account := seatAccount domain transaction
  -- the seat account is its cell's coordinate: never offered onto a retired or occupied cell
  if ObjectiveActivity.isRetired (snapshot.canonicalBytes (seatCell account)) then throw (.seatRetired account)
  if present snapshot (seatCell account) then throw (.seatExists account)
  let found ← loadInvitation snapshot domain invitation
  let inst ← match found with
    | some body => loadInstance snapshot domain body.invitation.inst
    | none => pure none
  let holdings := match holder with
    | some record => [(record, readHoldings snapshot domain record)]
    | none => []
  let loaded : Loaded := { instances := inst.toList, invitations := found.toList, holdings := holdings }
  let fresh : Option Fresh := found.map fun body => ⟨seatKey transaction, body.invitation.role, body.invitation.terms, height⟩
  match ran : Seats.step (loaded.world logical) height (.subject request.subject)
      (.offer invitation expect account funding payee proposal holder) with
  | .error reason => throw (.kernel reason)
  | .ok (next, batch) =>
    finish config snapshot height request loaded book bookExact next batch (.stepped ran) noPostings rfl fresh []
      [seatCell account] [invitationClaim invitation] (by rw [hturn]; rfl)
      (by intro _ _ h; rw [hturn] at h; simp only [Turn.kernelAction, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h; exact ran)

/-- The kernel's decision of one turn on a snapshot at a height. -/
def decideTurn {rootBytes : Bytes → Digest} (config : Config) (snapshot : Snapshot rootBytes) (height : Nat)
    (request : Request) : Except Refusal (Decided config snapshot height request) :=
  match bookExact : loadBook config snapshot with
  | .error _ => .error .bookUnavailable
  | .ok book =>
    let logical := logicalBook book.logical
    let transaction := transactionOf request
    let domain := config.domain
    match hturn : request.turn with
    | .publish storedBytes => do
      let some stored := decodeStored storedBytes | throw .packageMissing
      let some artifact := ObjectiveBendSourceArtifact.decode stored.artifact | throw .packageMissing
      if artifact.outputCodec ≠ contractCodecId then throw (.notAContract "the artifact is not a contract package")
      let pin := ObjectiveBendSourceArtifact.identity artifact
      let cell := packageCell domain pin
      if present snapshot cell then throw .packageExists
      if stored.payer = config.asset ∨ stored.payer = config.collector ∨ reservedBase ≤ stored.payer ∨
          stored.payer ∉ logical.accounts then throw (.payerInvalid stored.payer)
      let definition ← program (replayPackage config stored pin)
      match ObjectiveBendTyping.callable definition.replayed.accepted.typed.type with
      | .arrow _ _ _ (.computation _ _ _) => throw (.notAContract "a contract method returns a Plan, not an Activity")
      | .arrow _ _ _ _ => pure ()
      | _ => throw (.notAContract "a contract method takes the call")
      let loaded : Loaded := {}
      finish config snapshot height request loaded book bookExact (loaded.world logical) noPostings .nothing
        noPostings rfl none [postAt snapshot cell (image .package (packageKey pin) (encodeStored stored))]
        [config.bookCell] [] (by rw [hturn]; rfl) (by intro _ _ h; rw [hturn] at h; cases h)
    | .create inst pin clause => do
      if !present snapshot (packageCell domain pin) then throw .packageMissing
      let found ← loadInstance snapshot domain inst
      let loaded : Loaded := { instances := found.toList }
      match ran : Seats.step (loaded.world logical) height (.subject request.subject) (.create ⟨inst, pin, clause⟩) with
      | .error reason => throw (.kernel reason)
      | .ok (next, batch) =>
        finish config snapshot height request loaded book bookExact next batch (.stepped ran) noPostings rfl none []
          [packageCell domain pin, instanceCell domain inst] [] (by rw [hturn]; rfl)
          (by intro _ _ h; rw [hturn] at h; simp only [Turn.kernelAction, Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h; exact ran)
    | .handOver invitation recipient => do
      let found ← loadInvitation snapshot domain invitation
      let loaded : Loaded := { invitations := found.toList }
      match ran : Seats.step (loaded.world logical) height (.subject request.subject) (.handOver invitation recipient) with
      | .error reason => throw (.kernel reason)
      | .ok (next, batch) =>
        finish config snapshot height request loaded book bookExact next batch (.stepped ran) noPostings rfl none [] [] []
          (by rw [hturn]; rfl)
          (by intro _ _ h; rw [hturn] at h; simp only [Turn.kernelAction, Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h; exact ran)
    | .offer invitation expect funding payee proposal holder =>
      decideOffer config snapshot height request book bookExact invitation expect funding payee proposal holder hturn
    | .invoke inst inputBytes envelope account => do
      let some input := decodeDataBytes inputBytes | throw .inputUndecodable
      let some body ← loadInstance snapshot domain inst | throw (.instanceMissing inst)
      if body.retired then throw (.instanceMissing inst)
      if reservedBase ≤ account ∨ account = config.collector ∨ account = config.asset then throw (.payerInvalid account)
      let seats ← body.seats.mapM (requireSeat snapshot)
      let call := callData input height logical seats
      let result ← runMethod config (packageBytes domain snapshot body.inst.package) body.inst.package call envelope
      let plan ← decodePlan (config.planBudget.nodes + 1) result
      let ids := plan.zipIdx.filterMap fun (member, index) => match member with
        | .mint _ _ _ => some (mintId transaction inst index)
        | _ => none
      let minted ← ids.mapM (loadInvitation snapshot domain)
      let loaded : Loaded := { instances := [body], invitations := minted.filterMap (fun found => found), seats := seats }
      match ran : runPlan height body.inst (mintId transaction inst) (loaded.world logical) 0 plan with
      | .error reason => throw (.kernel reason)
      | .ok (next, batch) =>
        finish config snapshot height request loaded book bookExact next batch (.planned ran)
          ⟨[], [.fee account config.collector config.asset (config.tariff.workOf envelope)], []⟩ rfl none []
          (packageCell domain body.inst.package :: ids.map (invitationCell domain)) [] (by rw [hturn]; rfl)
          (by intro _ _ h; rw [hturn] at h; cases h)
    | .exit seat => do
      let found ← loadSeat snapshot seat
      let inst ← match found with
        | some body => loadInstance snapshot domain body.seat.inst
        | none => pure none
      let loaded : Loaded := { instances := inst.toList, seats := found.toList }
      match ran : Seats.step (loaded.world logical) height (.subject request.subject) (.exit seat) with
      | .error reason => throw (.kernel reason)
      | .ok (next, batch) =>
        finish config snapshot height request loaded book bookExact next batch (.stepped ran) noPostings rfl none []
          [seatCell seat] [] (by rw [hturn]; rfl)
          (by intro _ _ h; rw [hturn] at h; simp only [Turn.kernelAction, Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h; exact ran)

/-- **`offer_refuses_taken_cell`: a seat account is never reused.** A seat account is its seat cell's
coordinate `H(offer transaction)`. An offer whose cell is retired (its seat closed) or already holds
a seat is refused by name, before anything else is read. (The Book alone cannot refuse a
re-registration of a deregistered id; this is what does.) -/
theorem offer_refuses_taken_cell {rootBytes : Bytes → Digest} (config : Config) (snapshot : Snapshot rootBytes)
    (height : Nat) (request : Request) {invitation : InvitationId} {expect : Expectation}
    {funding payee : AccountId} {proposal : Proposal} {holder : Option Nat}
    (turn : request.turn = .offer invitation expect funding payee proposal holder)
    (taken : ObjectiveActivity.isRetired (snapshot.canonicalBytes
        (seatCell (seatAccount config.domain (transactionOf request)))) = true ∨
      present snapshot (seatCell (seatAccount config.domain (transactionOf request))) = true) :
    ∃ reason, decideTurn config snapshot height request = .error reason := by
  unfold decideTurn
  split
  · exact ⟨_, rfl⟩
  · rename_i book bookExact
    split
    all_goals (first | (rename_i heq; exfalso; rw [turn] at heq; cases heq; done) | skip)
    rename_i invitation' expect' funding' payee' proposal' holder' hturn
    show ∃ reason, decideOffer config snapshot height request book bookExact invitation' expect' funding'
      payee' proposal' holder' hturn = .error reason
    unfold decideOffer
    dsimp only
    rcases taken with h | h
    · rw [if_pos h]; exact ⟨_, rfl⟩
    · by_cases r : ObjectiveActivity.isRetired (snapshot.canonicalBytes
          (seatCell (seatAccount config.domain (transactionOf request)))) = true
      · rw [if_pos r]; exact ⟨_, rfl⟩
      · rw [if_neg r, if_pos h]; exact ⟨_, rfl⟩

/-! ## An activity's end: the seats it holds

The activity kernel's ending turn (`done`, `faulted`, and any later disposal
turn that ends an activity) calls `endHeld` with the Book its own ending batch
produced: the activity's holdings cell names its seats; they are loaded, the
kernel's own `Seats.closeHeld` exits every open one as a step of
`Actor.activity record` (each pays its whole allocation to its payee), and the
activity route appends `batch` to its ending batch (ONE Book batch for the turn,
`Posts.seq`) and writes `posts` in the same intent. -/

structure HeldEnd {rootBytes : Bytes → Digest} (domain : Digest) (snapshot : Snapshot rootBytes)
    (height record : Nat) (book : Book) where
  private mk ::
  loaded : Loaded
  next : World
  batch : Batch
  ended : closeHeld (loaded.world book) height record = .ok (next, batch)
  posts : List Post
  postsExact : posts = statePosts domain snapshot loaded none next
  /-- The kernel checked it (`checkInert`): the closing touches no kernel-activity cell. -/
  inert : Inert snapshot posts
  guards : List ReadGuard
  guardsExact : guards = (loadedCells domain loaded).map (guardAt snapshot)

def endHeld {rootBytes : Bytes → Digest} (domain : Digest) (snapshot : Snapshot rootBytes) (height record : Nat)
    (book : Book) : Except Refusal (HeldEnd domain snapshot height record book) := do
  let accounts := readHoldings snapshot domain record
  -- a held seat that already exited has a retired cell (its holdings entry stays): nothing to close
  let live := accounts.filter fun account => !ObjectiveActivity.isRetired (snapshot.canonicalBytes (seatCell account))
  let seats ← live.mapM (requireSeat snapshot)
  let instances ← (seats.map fun body => body.seat.inst).dedup.mapM (loadInstance snapshot domain)
  let loaded : Loaded := { instances := instances.filterMap (fun found => found), seats := seats,
                           holdings := [(record, accounts)] }
  match ended : closeHeld (loaded.world book) height record with
  | .error reason => throw (.kernel reason)
  | .ok (next, batch) =>
    let ⟨inert⟩ ← checkInert snapshot (statePosts domain snapshot loaded none next)
    pure ⟨loaded, next, batch, ended, _, rfl, inert, _, rfl⟩

/-- **An activity's end closes every seat it holds** (the kernel's
`activity_end_closes_seats` on the loaded holdings): every held seat is gone from
the written world and its account is no Book account, and the end's batch is
admitted on the Book it was given and conserves every asset. -/
theorem HeldEnd.closes {rootBytes : Bytes → Digest} {domain : Digest} {snapshot : Snapshot rootBytes}
    {height record : Nat} {book : Book} (held : HeldEnd domain snapshot height record book) :
    (∀ seat ∈ heldOpen (held.loaded.world book) height record, ∀ after ∈ held.next.seats,
        after.account ≠ seat.account) ∧
      (∀ seat ∈ heldOpen (held.loaded.world book) height record, seat.account ∉ held.next.book.accounts) ∧
      Posts book held.batch held.next.book ∧ held.batch.registrations = [] ∧
      ∀ asset, held.next.book.totalAsset asset = book.totalAsset asset := by
  obtain ⟨closes, gone, posted, conserves⟩ := activity_end_closes_seats held.ended
  exact ⟨closes, gone, posted, (exitEach_posts held.ended).2.1, conserves⟩

/-- **A loaded seat the next world no longer holds is written to the retired
image**: the cell is retired, never rewritten, never reused. -/
theorem statePosts_retires {rootBytes : Bytes → Digest} {domain : Digest} {snapshot : Snapshot rootBytes}
    {loaded : Loaded} {fresh : Option Fresh} {next : World} {body : SeatBody} (member : body ∈ loaded.seats)
    (gone : ∀ seat ∈ next.seats, seat.account ≠ body.seat.account) :
    postAt snapshot (seatCell body.seat.account) ObjectiveActivity.retiredImage ∈
      statePosts domain snapshot loaded fresh next := by
  unfold statePosts
  dsimp only
  refine List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
    (List.mem_append_left _ ?_)))
  refine List.mem_map.mpr ⟨body, List.mem_filter.mpr ⟨member, ?_⟩, rfl⟩
  have absent : (next.seats.any fun seat => seat.account == body.seat.account) = false := by
    cases h : (next.seats.any fun seat => seat.account == body.seat.account)
    · rfl
    · obtain ⟨seat, inNext, same⟩ := List.any_eq_true.mp h
      exact absurd (by simpa using same) (gone seat inNext)
  show (!(next.seats.any fun seat => seat.account == body.seat.account)) = true
  rw [absent]; rfl

/-- **An activity's end retires the seat cells it closes.** -/
theorem HeldEnd.retires {rootBytes : Bytes → Digest} {domain : Digest} {snapshot : Snapshot rootBytes}
    {height record : Nat} {book : Book} (held : HeldEnd domain snapshot height record book) :
    ∀ seat ∈ heldOpen (held.loaded.world book) height record,
      postAt snapshot (seatCell seat.account) ObjectiveActivity.retiredImage ∈ held.posts := by
  intro seat member
  have mem : seat ∈ held.loaded.seats.map SeatBody.seat := (List.mem_filter.mp member).1
  obtain ⟨body, bodyMem, bodySeat⟩ := List.mem_map.mp mem
  have gone := (held.closes).1 seat member
  rw [held.postsExact]
  have := statePosts_retires (domain := domain) (snapshot := snapshot) (fresh := none) (next := held.next)
    bodyMem (fun s hs => by rw [bodySeat]; exact gone s hs)
  rw [bodySeat] at this
  exact this

/-- **A decided turn retires the cell of every loaded seat it closed.** -/
theorem Decided.retires_closed {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height : Nat} {request : Request} (decided : Decided config snapshot height request) {body : SeatBody}
    (member : body ∈ decided.loaded.seats) (gone : ∀ seat ∈ decided.next.seats, seat.account ≠ body.seat.account) :
    postAt snapshot (seatCell body.seat.account) ObjectiveActivity.retiredImage ∈ decided.posts := by
  rw [decided.postsExact]
  exact List.mem_append_left _ (List.mem_append_right _ (statePosts_retires member gone))

/-- **`exit_retires_cell`.** A decided exit turn writes the seat's cell to the
retired image: the cell is emptied and its id enters the World's retired set. -/
theorem Decided.exit_retires_cell {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height : Nat} {request : Request} (decided : Decided config snapshot height request) {seat : Nat}
    (turn : request.turn = .exit seat) :
    postAt snapshot (seatCell seat) ObjectiveActivity.retiredImage ∈ decided.posts := by
  have ran := decided.stepExact (.subject request.subject) (.exit seat) (by simp [turn, Turn.kernelAction])
  obtain ⟨found, foundMem, foundAccount, _, _⟩ := exit_spec ran
  have closes := step_exit_closes ran
  have inWorld : found ∈ decided.loaded.seats.map SeatBody.seat := by
    rw [decided.worldExact] at foundMem
    exact foundMem
  obtain ⟨body, bodyMem, bodySeat⟩ := List.mem_map.mp inWorld
  have retired := decided.retires_closed bodyMem (fun s hs => by
    rw [closes] at hs
    rw [bodySeat, foundAccount]
    exact (mem_removeSeat.mp hs).2)
  rw [bodySeat, foundAccount] at retired
  exact retired

#assert_axioms seatAccount_protected KernelRun.posts KernelRun.reachable KernelRun.inv Decided.conserves
  Decided.inv Decided.book_post HeldEnd.closes offer_refuses_taken_cell HeldEnd.retires statePosts_retires Decided.exit_retires_cell

end Minidregg.Kernel.SeatStore
