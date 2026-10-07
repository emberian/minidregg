/- The governed upgrade of an object (ROOT ruling UPGRADE, brief
`work/UPGRADE-BRIEF-20261005.md`): ADOPT, the drain, ABORT, MIGRATE, REBIRTH.

* **ADOPT** (`adopt`, one turn, `Facts.turn` 7). The object's policy decides who
  may: `frozen` refuses by name; a `governed authority floors` policy admits a
  request whose facts satisfy `authority` (`adopt_requires_authority`), whose next
  policy only tightens (`UpgradePolicy.permits`), and whose next law entails every
  floor: `law ∧ ¬floor` is decided unsatisfiable with a certificate the checker
  accepts (`Pred.Sat.certificate_unsat`; `adopt_floors_entailed`). The next
  package must be published and differ from the pin; the next state type is
  first-order. The migration (a declaration of the next package, or the
  identity) is checked at ADOPT: the identity needs the old state type to be a
  value subtype of the new; a term must be typed `old -> new` by the checker
  and LINEAR (`forgotten`: every top-level field of the old state is read by the
  term, `get (bound d) field` on its own parameter, or named in `dropped`). The
  current state must migrate and pass the next record's judgment (so MIGRATE can
  never fail on it). Every activity chosen for REBIRTH must be an awaiting
  activity of the object whose stored input the next package takes. The record
  is written `draining next (height + patience)`, the chosen activities move from
  the `live` counter to `rebirths`, the continuity rises by one.
* **The drain.** Old activities keep running their own pinned package on the
  unmigrated state; every declared-state write while draining passes the
  drained-write judgment (`ObjectiveActivity.judgeDrained`,
  `drained_write_migratable`): its state, migrated, is admitted by the record
  MIGRATE will install, under the migration's facts. New births, calls and
  messages wait unless the migration is the identity (`ObjectRecord.admitsNew`,
  `draining_refuses_births`).
* **ABORT** (`abortDrained`, anyone, `Facts.turn` 8) at or after the drain
  deadline, of an old activity not chosen for rebirth: the activity is resumed
  with `upgraded` (its own package, the unmigrated state) for ONE segment that
  must end it (a yield ends it `faulted`), its await claim is spent
  (`abort_after_deadline_exclusive`), its slot reclaimed, its purse returned and
  closed, its counter released.
* **MIGRATE** (`migrate`, anyone paying the migration's price, `Facts.turn` 6)
  when no old activity outside the rebirth set awaits (`live = 0`): the state is
  migrated and judged by the next record under the migration's facts, the record
  becomes `ObjectRecord.successor` (`migrate_judged`); given the drained
  judgment holds of the current state, it cannot fail (`migrate_cannot_fail`).
* **REBIRTH** (`rebirth`, anyone, `Facts.turn` 9) of an activity left on the old
  package after MIGRATE: ONE turn ends it (claim spent, slot reclaimed) and births
  it again on the object's (new) pin from its stored input, generation 0, on the
  migrated state, never blind, its purse swept into the new purse and closed, its
  escrow terms kept (`rebirth_from_stored_input`). It is literally a `birth` with a
  `Predecessor`.

Not built here: the multi-turn `migrating` phase (a cursor over a large state):
MIGRATE is one turn. Interface compatibility (design C, "the new interface
contains every facet a holder references") has no substrate: the kernel holds no
facet table. Both are the next items. -/
import Kernel.ObjectiveActivity
import Pred.Satisfiable

namespace Minidregg.Kernel.ObjectiveActivity
open Minidregg.Theory Minidregg.Compiler
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Theory.TypedAuthorization (Digest SubjectId)
open Minidregg.Kernel.DurableDataIntent
open Minidregg.Kernel.ObjectiveActivityWire
open Minidregg.Theory.ObjectiveBendOpenRecursion (Term)
open Minidregg.Theory.ObjectiveBendTypes (Ty)
open Minidregg.Theory.ObjectiveBendTyping
open Minidregg.Theory.ObjectiveBendDemandMachine (State resume)
open Minidregg.Theory.ObjectiveBendDemandData (Data)
open Minidregg.Theory.CanonicalResourceKernel (Book Batch Operation AccountId AssetId logicalBook)
open Minidregg.Kernel.ObjectRecord (ObjectRecord Pending UpgradePhase UpgradePolicy Facts WriteRefusal admitWrite
  migrateFacts)
open Minidregg.Kernel.ObjectStateType (typedAt stateSubtype)
open Minidregg.Kernel.ObjectiveTariff (addCapacity)
open Minidregg.Compiler.ObjectiveInvocationClaim (Capacity)
set_option autoImplicit false

/-! ## Floors: `law → floor`, decided with a certificate -/

/-- `law ∧ ¬floor`: unsatisfiable exactly when the law entails the floor. -/
def floorProblem (law floor : Minidregg.Pred.Pred) : Minidregg.Pred.Pred :=
  .allL (.cons law (.cons (.not floor) .nil))

/-- The floor is entailed: `law ∧ ¬floor` translates (`Pred.difference?`) and the
decision returns `unsat` with a certificate `checkAll` accepted. Any other answer
(outside the fragment, past the DNF cap, a witness) refuses. -/
def floorEntailed (law floor : Minidregg.Pred.Pred) : Bool :=
  match (floorProblem law floor).difference? with
  | some problem =>
    match problem.decide with
    | .unsat _ => true
    | _ => false
  | none => false

/-- **An entailed floor holds wherever the law does** (through `certificate_unsat`). -/
theorem floorEntailed_sound {law floor : Minidregg.Pred.Pred} (entailed : floorEntailed law floor = true)
    (old new : Minidregg.Pred.State) (holds : Minidregg.Pred.eval law old new = true) :
    Minidregg.Pred.eval floor old new = true := by
  unfold floorEntailed at entailed
  split at entailed
  · rename_i problem defined
    split at entailed
    · rename_i certificate unsat
      have none_ := Minidregg.Pred.Sat.certificate_unsat defined unsat old new
      cases f : Minidregg.Pred.eval floor old new with
      | true => rfl
      | false =>
        exfalso
        unfold Minidregg.Pred.eval at holds f none_
        simp [floorProblem, Minidregg.Pred.evalWith, Minidregg.Pred.evalWithAll, holds, f] at none_
    · cases entailed
  · cases entailed

/-- The index of the first floor the law does not provably entail. -/
def firstUnentailed (law : Minidregg.Pred.Pred) : Nat → List Minidregg.Pred.Pred → Option Nat
  | _, [] => none
  | index, floor :: rest => if floorEntailed law floor then firstUnentailed law (index + 1) rest else some index

theorem firstUnentailed_none (law : Minidregg.Pred.Pred) (floors : List Minidregg.Pred.Pred) :
    ∀ (index : Nat), firstUnentailed law index floors = none → ∀ floor ∈ floors, floorEntailed law floor = true := by
  induction floors with
  | nil => intro _ _ floor member; cases member
  | cons first rest ih =>
    intro index none_ floor member
    unfold firstUnentailed at none_
    split at none_
    · rename_i entailed
      rcases List.mem_cons.mp member with same | later
      · subst same; exact entailed
      · exact ih (index + 1) none_ floor later
    · cases none_

/-! ## Linearity: no old field is silently forgotten

The syntactic check (brief trap 3), exactly: the migration's checked term must
have the elaborator's package shape `get (fix (specification _ (lam (lam (extend
(bound 0) fields)))) _) key` with `fields.lookup key = lam body`; the check
collects every `name` such that `get (bound d) name` occurs in `body`, where
`bound d` is the migration's own parameter (`d` counts the binders between:
a lambda, a case arm and `ifZero`'s successor body each bind one). Every
top-level field of the OLD state type must be collected or named in `dropped`.
A whole use of the parameter (not under `get`) accounts for no field. What it
does not say: that a field it reads reaches the new state. -/

/-- The fields a term projects off the parameter at `depth`. Running out of
`fuel` collects fewer, so the check refuses more, never less. -/
def parameterReads : Nat → Nat → Term → List String
  | 0, _, _ => []
  | fuel + 1, depth, term =>
    match term with
    | .get (.bound index) name => if index = depth then [name] else []
    | .get target _ => parameterReads fuel depth target
    | .bound _ | .nat _ | .boolean _ | .label _ => []
    | .lam body => parameterReads fuel (depth + 1) body
    | .app first second | .mix first second | .fix first second | .specification first second
    | .prototype first second | .binary _ first second =>
      parameterReads fuel depth first ++ parameterReads fuel depth second
    | .reflect inner | .metadata inner | .project inner | .inject _ inner | .perform inner | .done inner =>
      parameterReads fuel depth inner
    | .extend inherited fields =>
      parameterReads fuel depth inherited ++ fields.flatMap (fun field => parameterReads fuel depth field.2)
    | .record fields => fields.flatMap (fun field => parameterReads fuel depth field.2)
    | .ifZero value zero successor =>
      parameterReads fuel depth value ++ parameterReads fuel depth zero ++ parameterReads fuel (depth + 1) successor
    | .case scrutinee arms =>
      parameterReads fuel depth scrutinee ++ arms.flatMap (fun arm => parameterReads fuel (depth + 1) arm.2)
    | .ifBool condition whenTrue whenFalse =>
      parameterReads fuel depth condition ++ parameterReads fuel depth whenTrue ++ parameterReads fuel depth whenFalse

/-- The body of the selected one-parameter declaration in the elaborator's package term. -/
def migrationBody : Term → Option Term
  | .get (.fix (.specification _ (.lam (.lam (.extend (.bound 0) fields)))) _) key =>
    match fields.lookup key with
    | some (.lam body) => some body
    | _ => none
  | _ => none

/-- The top-level fields of a record row. -/
def topFields : Ty → List String
  | .field name _ tail => name :: topFields tail
  | _ => []

/-- The walk bound of the linearity check. -/
def linearityFuel : Nat := 100000

/-- The old fields neither read by the migration's body nor dropped. -/
def forgotten (oldType : Ty) (body : Term) (dropped : List String) : List String :=
  let reads := parameterReads linearityFuel 0 body
  (topFields oldType).filter (fun field => !(reads.contains field) && !(dropped.contains field))

/-! ## ADOPT -/

structure AdoptRequest where
  subject : SubjectId
  object : CellId
  /-- The next package. -/
  pin : Digest
  stateType : Ty
  /-- A declaration of the next package `old -> new`, or `none` (the identity). -/
  migration : Option String
  dropped : List String
  law : Minidregg.Pred.Pred
  upgrade : UpgradePolicy
  /-- The activities to re-birth on the next package after MIGRATE. -/
  rebirth : List Digest
  /-- The declared envelope of one migration run. -/
  envelope : Capacity
  /-- Heights the old activities have before an abort may end them. -/
  patience : Nat
  /-- The signer's Book account: pays the public price of `envelope` for the ADOPT's checks. -/
  account : AccountId
  nonce : Nat

def adoptTransaction (request : AdoptRequest) : TransactionId :=
  tagged "DREGG/OBJECTIVE/OBJECT/TX/ADOPT/v1"
    (subjectStream.encode request.subject ++ digestStream.encode request.object ++ digestStream.encode request.pin ++
      StreamCodec.nat.encode request.nonce)

/-- The facts the upgrade authority judges (turn 7). -/
def adoptFacts (request : AdoptRequest) (height : Nat) : Facts :=
  ⟨some request.subject, height, request.object.value, 7, none, none⟩

/-- The request facts as a state the authority predicate reads (as old and new). -/
def factsState (facts : Facts) : Minidregg.Pred.State := ⟨facts.slots⟩

/-- **The policy half of ADOPT**: `frozen` refuses; the facts must satisfy the
authority; the next policy only tightens; the next law entails every floor. A
function of the policy, the facts and the request (never of the payer). -/
def adoptPolicy (upgrade : UpgradePolicy) (facts : Facts) (request : AdoptRequest) : Except Refusal Unit :=
  match upgrade with
  | .frozen => .error .frozen
  | .governed authority floors =>
    if Minidregg.Pred.eval authority (factsState facts) (factsState facts) then
      if UpgradePolicy.permits (.governed authority floors) request.upgrade then
        match firstUnentailed request.law 0 floors with
        | none => .ok ()
        | some index => .error (.floorNotEntailed index)
      else .error .policyLoosened
    else .error .notUpgradeAuthority

theorem adoptPolicy_ok {upgrade : UpgradePolicy} {facts : Facts} {request : AdoptRequest}
    (ok : adoptPolicy upgrade facts request = .ok ()) :
    ∃ authority floors, upgrade = .governed authority floors ∧
      Minidregg.Pred.eval authority (factsState facts) (factsState facts) = true ∧
      UpgradePolicy.permits upgrade request.upgrade = true ∧
      ∀ floor ∈ floors, floorEntailed request.law floor = true := by
  unfold adoptPolicy at ok
  split at ok
  · cases ok
  · rename_i authority floors
    split at ok
    · rename_i authorized
      split at ok
      · rename_i permitted
        split at ok
        · rename_i none_
          exact ⟨authority, floors, rfl, authorized, permitted, firstUnentailed_none _ _ 0 none_⟩
        · cases ok
      · cases ok
    · cases ok

/-- The migration check of ADOPT: the identity needs a value subtype; a term must
be typed `old -> new` by the checker at the declared state types and be linear. -/
def migrationCheck {rootBytes : Bytes → Digest} (config : Config) (snapshot : Snapshot rootBytes)
    (record : ObjectRecord) (next : Pending) : Except Refusal Unit :=
  match next.migration with
  | none => if stateSubtype record.stateType next.stateType then .ok () else .error .notSubtype
  | some name =>
    match loadMigration config (packageBytes config snapshot next.pin) next.pin name with
    | .error reason => .error reason
    | .ok migration =>
      if sameType migration.accepted.source.assumptions migration.domain record.stateType &&
          sameType migration.accepted.source.assumptions migration.codomain next.stateType then
        match migrationBody migration.accepted.source.term with
        | none => .error (.migrationShape "the selected declaration is not a one-parameter function of the package")
        | some body =>
          match forgotten record.stateType body next.dropped with
          | [] => .ok ()
          | fields => .error (.fieldsForgotten fields)
      else .error (.migrationShape "its type is not `old -> new` at the declared state types")

/-- The current state, migrated and judged (`judgeMigrated`); nothing when the
object has no state yet. -/
def migrateCurrent {rootBytes : Bytes → Digest} (config : Config) (snapshot : Snapshot rootBytes)
    (record : ObjectRecord) (object : CellId) (next : Pending) : Option ObjectState → Except Refusal (Option Data)
  | none => .ok none
  | some state =>
    match judgeMigrated config snapshot record object next state.value with
    | .ok migrated => .ok (some migrated)
    | .error reason => .error reason

theorem migrateCurrent_some {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {record : ObjectRecord} {object : CellId} {next : Pending} {state : ObjectState} {migrated : Option Data}
    (ok : migrateCurrent config snapshot record object next (some state) = .ok migrated) :
    ∃ value, migrated = some value ∧ judgeMigrated config snapshot record object next state.value = .ok value := by
  cases judged : judgeMigrated config snapshot record object next state.value with
  | ok value => simp only [migrateCurrent, judged] at ok; cases ok; exact ⟨value, rfl, rfl⟩
  | error reason => simp only [migrateCurrent, judged] at ok; cases ok

/-- A chosen rebirth: an awaiting activity of the object on its pin whose stored
input instantiates the next package as an activity. -/
def rebirthTarget {rootBytes : Bytes → Digest} (config : Config) (snapshot : Snapshot rootBytes) (object : CellId)
    (record : ObjectRecord) (pin : Digest) (activity : Digest) : Except Refusal Unit :=
  match readRecord snapshot (recordCell config.domain object activity) with
  | none => .error (.rebirthTarget "no awaiting record")
  | some target =>
    if target.object = object ∧ target.activity = activity ∧ target.pin = record.pin ∧ target.phase.awaits = true then
      match decodeDataBytes target.input with
      | none => .error (.rebirthTarget "its stored input does not decode")
      | some input =>
        match loadProgram config (packageBytes config snapshot pin) pin input with
        | .ok _ => .ok ()
        | .error reason => .error (.rebirthTarget s!"the next package does not take its stored input: {reprStr reason}")
    else .error (.rebirthTarget "not an awaiting activity of the object on its pin")

def rebirthTargets {rootBytes : Bytes → Digest} (config : Config) (snapshot : Snapshot rootBytes) (object : CellId)
    (record : ObjectRecord) (pin : Digest) : List Digest → Except Refusal Unit
  | [] => .ok ()
  | activity :: rest => do
    rebirthTarget config snapshot object record pin activity
    rebirthTargets config snapshot object record pin rest

/-- The pending upgrade an ADOPT installs. -/
def AdoptRequest.pending (request : AdoptRequest) (height : Nat) : Pending :=
  ⟨request.pin, request.stateType, request.migration, request.dropped, request.law, request.upgrade, request.rebirth,
    request.envelope, height, 0⟩

/-- The record an ADOPT writes: draining, the chosen activities counted as
rebirths, the continuity one higher. -/
def adoptedRecord (record : ObjectRecord) (next : Pending) (deadline : Nat) : ObjectRecord :=
  { record with
    phase := .draining next deadline
    live := record.live - next.rebirth.length
    rebirths := next.rebirth.length
    continuity := record.continuity + 1 }

/-- The ADOPT's fee: the public price of the migration envelope, from the signer's account. -/
def adoptBatch (config : Config) (request : AdoptRequest) : Batch :=
  ⟨[], [.fee request.account config.collector config.asset (config.tariff.workOf request.envelope)], []⟩

theorem postings_batch {pre : BookCell} {batch : Batch} {posted : Postings pre}
    (ok : postings pre batch = .ok posted) : posted.batch = batch := by
  unfold postings at ok
  split at ok
  · cases ok; rfl
  · cases ok

structure Adoption {rootBytes : Bytes → Digest} (config : Config) (snapshot : Snapshot rootBytes)
    (height : Nat) (request : AdoptRequest) where
  private mk ::
  record : ObjectRecord
  recordExact : readObject config snapshot request.object = .ok (some record)
  policy : adoptPolicy record.upgrade (adoptFacts request height) request = .ok ()
  steady : record.phase = .steady
  noRebirths : record.rebirths = 0
  distinct : request.pin ≠ record.pin
  patienceWithin : 0 < request.patience ∧ request.patience ≤ config.maxPatience
  covered : config.covers request.envelope = true
  data : request.stateType.isData = true
  published : (bodyOf .package (snapshot.canonicalBytes (packageCell config.domain request.pin))).isSome = true
  migrationChecked : migrationCheck config snapshot record (request.pending height) = .ok ()
  current : Option ObjectState
  currentExact : readState config snapshot request.object = .ok current
  migrated : Option Data
  migratedExact : migrateCurrent config snapshot record request.object (request.pending height) current = .ok migrated
  nodup : request.rebirth.Nodup
  rebirthsChecked : rebirthTargets config snapshot request.object record request.pin request.rebirth = .ok ()
  book : BookCell
  bookExact : loadBook config snapshot = .ok book
  posted : Postings book
  postedBatch : posted.batch = adoptBatch config request
  posts : List Post
  postsExact : posts = [postAt snapshot (objectCell config.domain request.object)
      (objectImage request.object (adoptedRecord record (request.pending height) (height + request.patience))),
    posted.write config snapshot]
  guards : List ReadGuard
  guardsExact : guards = guardAt snapshot (packageCell config.domain request.pin) ::
    guardAt snapshot (stateCell config.domain request.object) ::
    request.rebirth.map (fun activity => guardAt snapshot (recordCell config.domain request.object activity))

def adopt {rootBytes : Bytes → Digest} (config : Config) (snapshot : Snapshot rootBytes) (height : Nat)
    (request : AdoptRequest) : Except Refusal (Adoption config snapshot height request) :=
  match recordExact : readObject config snapshot request.object with
  | .error reason => .error reason
  | .ok none => .error .notAnObject
  | .ok (some record) =>
  match policy : adoptPolicy record.upgrade (adoptFacts request height) request with
  | .error reason => .error reason
  | .ok () =>
  if steady : record.phase = .steady then
  if noRebirths : record.rebirths = 0 then
  if distinct : request.pin ≠ record.pin then
  if patienceWithin : 0 < request.patience ∧ request.patience ≤ config.maxPatience then
  if covered : config.covers request.envelope = true then
  if data : request.stateType.isData = true then
  if published : (bodyOf .package (snapshot.canonicalBytes (packageCell config.domain request.pin))).isSome = true then
  match migrationChecked : migrationCheck config snapshot record (request.pending height) with
  | .error reason => .error reason
  | .ok () =>
  match currentExact : readState config snapshot request.object with
  | .error reason => .error reason
  | .ok current =>
  match migratedExact : migrateCurrent config snapshot record request.object (request.pending height) current with
  | .error reason => .error reason
  | .ok migrated =>
  if nodup : request.rebirth.Nodup then
  match rebirthsChecked : rebirthTargets config snapshot request.object record request.pin request.rebirth with
  | .error reason => .error reason
  | .ok () =>
  match bookExact : loadBook config snapshot with
  | .error reason => .error reason
  | .ok book =>
  match postedExact : postings book (adoptBatch config request) with
  | .error reason => .error reason
  | .ok posted =>
    .ok ⟨record, recordExact, policy, steady, noRebirths, distinct, patienceWithin, covered, data, published,
      migrationChecked, current, currentExact, migrated, migratedExact, nodup, rebirthsChecked, book, bookExact,
      posted, postings_batch postedExact, _, rfl, _, rfl⟩
  else .error (.rebirthTarget "the rebirth list names an activity twice")
  else .error .pinUnpublished
  else .error .stateTypeNotData
  else .error (.uncovered request.envelope)
  else .error (.drainPatience request.patience config.maxPatience)
  else .error .samePin
  else .error .upgradeUnderWay
  else .error .upgradeUnderWay

def Adoption.intent {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height : Nat} {request : AdoptRequest} (adopted : Adoption config snapshot height request) (sealing : Seal) :
    DataIntent rootBytes :=
  intentOf rootBytes (adoptTransaction request) adopted.posts adopted.guards [] sealing

/-! ## MIGRATE -/

structure MigrateRequest where
  subject : SubjectId
  object : CellId
  /-- Pays the public price of the migration envelope (when the migration is a term). -/
  account : AccountId

/-- One MIGRATE per ADOPT: the object and the continuity the ADOPT left. -/
def migrateTransaction (object : CellId) (continuity : Nat) : TransactionId :=
  tagged "DREGG/OBJECTIVE/OBJECT/TX/MIGRATE/v1" (digestStream.encode object ++ StreamCodec.nat.encode continuity)

/-- The MIGRATE's fee: the migration envelope's public price when a term runs. -/
def migrateFee (config : Config) (next : Pending) : Nat :=
  if next.migration.isSome then config.tariff.workOf next.envelope else 0

def migrateBatch (config : Config) (request : MigrateRequest) (next : Pending) : Batch :=
  ⟨[], if migrateFee config next = 0 then [] else
    [.fee request.account config.collector config.asset (migrateFee config next)], []⟩

/-- The migrated state's post: version one higher, when the object has state. -/
def migratedStatePosts {rootBytes : Bytes → Digest} (config : Config) (snapshot : Snapshot rootBytes)
    (object : CellId) : Option ObjectState → Option Data → List Post
  | some state, some value => [postAt snapshot (stateCell config.domain object) (stateImage object ⟨state.version + 1, value⟩)]
  | _, _ => []

structure Migrated {rootBytes : Bytes → Digest} (config : Config) (snapshot : Snapshot rootBytes)
    (height : Nat) (request : MigrateRequest) where
  private mk ::
  record : ObjectRecord
  recordExact : readObject config snapshot request.object = .ok (some record)
  next : Pending
  deadline : Nat
  draining : record.phase = .draining next deadline
  /-- No activity pinned to the old package and not chosen for rebirth awaits. -/
  drained : record.live = 0
  current : Option ObjectState
  currentExact : readState config snapshot request.object = .ok current
  migrated : Option Data
  migratedExact : migrateCurrent config snapshot record request.object next current = .ok migrated
  book : BookCell
  bookExact : loadBook config snapshot = .ok book
  posted : Postings book
  postedBatch : posted.batch = migrateBatch config request next
  posts : List Post
  postsExact : posts = postAt snapshot (objectCell config.domain request.object)
      (objectImage request.object (record.successor next)) ::
    (migratedStatePosts config snapshot request.object current migrated ++ [posted.write config snapshot])

def migrate {rootBytes : Bytes → Digest} (config : Config) (snapshot : Snapshot rootBytes) (height : Nat)
    (request : MigrateRequest) : Except Refusal (Migrated config snapshot height request) :=
  match recordExact : readObject config snapshot request.object with
  | .error reason => .error reason
  | .ok none => .error .notAnObject
  | .ok (some record) =>
  match draining : record.phase with
  | .steady => .error .notDraining
  | .draining next deadline =>
  if drained : record.live = 0 then
  match currentExact : readState config snapshot request.object with
  | .error reason => .error reason
  | .ok current =>
  match migratedExact : migrateCurrent config snapshot record request.object next current with
  | .error reason => .error reason
  | .ok migrated =>
  match bookExact : loadBook config snapshot with
  | .error reason => .error reason
  | .ok book =>
  match postedExact : postings book (migrateBatch config request next) with
  | .error reason => .error reason
  | .ok posted =>
    .ok ⟨record, recordExact, next, deadline, draining, drained, current, currentExact, migrated, migratedExact,
      book, bookExact, posted, postings_batch postedExact, _, rfl⟩
  else .error (.liveActivities record.live)

def Migrated.intent {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height : Nat} {request : MigrateRequest} (migrated : Migrated config snapshot height request) (sealing : Seal) :
    DataIntent rootBytes :=
  intentOf rootBytes (migrateTransaction request.object migrated.record.continuity) migrated.posts
    [guardAt snapshot (packageCell config.domain migrated.next.pin)] [] sealing

/-! ## ABORT after the drain deadline -/

structure AbortRequest where
  subject : SubjectId
  record : CellId
  /-- Envelope the submitter adds (and pays for) on top of the escrowed timeout envelope. -/
  extra : Capacity
  account : AccountId

def abortTransaction (await : Digest) : TransactionId :=
  tagged "DREGG/OBJECTIVE/ACTIVITY/TX/ABORT/v1" (digestStream.encode await)

/-- The one segment an aborted activity runs after `upgraded`: it must end. A
yield ends it `faulted`; a program fault ends it `faulted`; any other refusal
refuses the turn. -/
def abortSegment (config : Config) (ticks : Nat) (start : State) : Except Refusal Segment :=
  match runSegment config ticks start with
  | .ok (.yielded _ _) => .ok (.faulted "yielded after upgraded")
  | .ok segment => .ok segment
  | .error refusal =>
    match programFault config ticks refusal with
    | some reason => .ok (.faulted reason)
    | none => .error refusal

theorem abortSegment_ends {config : Config} {ticks : Nat} {start : State} {segment : Segment}
    (ok : abortSegment config ticks start = .ok segment) : segment.yields = false := by
  unfold abortSegment at ok
  cases ran : runSegment config ticks start with
  | ok ran' =>
    rw [ran] at ok
    cases ran' with
    | yielded _ _ => simp at ok; subst ok; rfl
    | finished _ => simp at ok; subst ok; rfl
    | faulted _ => simp at ok; subst ok; rfl
  | error refusal =>
    rw [ran] at ok
    simp only at ok
    split at ok
    · simp at ok; subst ok; rfl
    · cases ok

/-- The deliver-request shape the abort's charges are computed from. -/
def AbortRequest.charging (request : AbortRequest) : DeliverRequest :=
  ⟨request.subject, request.record, request.extra, request.account⟩

structure Abort {rootBytes : Bytes → Digest} (config : Config) (snapshot : Snapshot rootBytes)
    (height : Nat) (request : AbortRequest) where
  private mk ::
  record : Record
  recordExact : readRecord snapshot request.record = some record
  located : request.record = recordCell config.domain record.object record.activity
  await : Await
  awaiting : record.phase = .awaiting await
  idExact : await.id = awaitId request.record record.generation record.checkpointDigest
  digestExact : checkpointDigest record.checkpoint = record.checkpointDigest
  input : Data
  inputExact : decodeDataBytes record.input = some input
  program : Program config record.pin input
  programExact : loadProgram config (packageBytes config snapshot record.pin) record.pin input = .ok program
  object : ObjectRecord
  objectExact : readObject config snapshot record.object = .ok (some object)
  next : Pending
  deadline : Nat
  draining : object.phase = .draining next deadline
  /-- At or after the drain deadline. -/
  due : deadline ≤ height
  /-- An old activity (on the object's pin), not chosen for rebirth. -/
  old : record.pin = object.pin
  notChosen : record.activity ∉ next.rebirth
  slotPosts : List Post
  slotClaims : List StableNullifier
  slotExact : abandonSlot config snapshot await = .ok (slotPosts, slotClaims)
  view : ObjectState
  viewExact : readState config snapshot record.object = .ok (some view)
  response : TypedData program.assumptions (responseData .upgraded view) program.responseType
  state : State
  stateExact : decodeCheckpoint record.checkpoint = some state
  resumed : State
  resumeExact : resume (responseData .upgraded view).term state = some resumed
  envelope : Capacity
  envelopeExact : envelope = addCapacity record.escrow.timeout request.extra
  covered : config.covers envelope = true
  segment : Segment
  segmentExact : abortSegment config envelope.sourceTicks resumed = .ok segment
  ended : Record
  endedExact : ended = nextRecord record (record.generation + 1) segment none
  book : BookCell
  bookExact : loadBook config snapshot = .ok book
  batch : Batch
  batchExact : settlePurse config (logicalBook book.logical) (heldAccount request.record) record.escrow 0
    (deliveryCharges config record request.record .timedOut request.charging 0) segment = .ok batch
  posted : Postings book
  postedBatch : posted.batch = batch
  posts : List Post
  postsExact : posts = recordPost config snapshot request.record ended ::
    (slotPosts ++ [posted.write config snapshot] ++
      countPosts config snapshot record.object object record.pin record.activity true false)
  claims : List StableNullifier
  claimsExact : claims = awaitClaim await.id :: slotClaims

def abortDrained {rootBytes : Bytes → Digest} (config : Config) (snapshot : Snapshot rootBytes) (height : Nat)
    (request : AbortRequest) : Except Refusal (Abort config snapshot height request) :=
  match recordExact : readRecord snapshot request.record with
  | none => .error (absentRecord snapshot request.record)
  | some record =>
  if located : request.record = recordCell config.domain record.object record.activity then
  match awaiting : record.phase with
  | .done _ | .faulted _ => .error .notAwaiting
  | .awaiting await =>
  if idExact : await.id = awaitId request.record record.generation record.checkpointDigest then
  if digestExact : checkpointDigest record.checkpoint = record.checkpointDigest then
  match inputExact : decodeDataBytes record.input with
  | none => .error .inputType
  | some input =>
  match programExact : loadProgram config (packageBytes config snapshot record.pin) record.pin input with
  | .error reason => .error reason
  | .ok program =>
  match objectExact : readObject config snapshot record.object with
  | .error reason => .error reason
  | .ok none => .error .notAnObject
  | .ok (some object) =>
  match draining : object.phase with
  | .steady => .error .notDraining
  | .draining next deadline =>
  if due : deadline ≤ height then
  if old : record.pin = object.pin then
  if notChosen : record.activity ∉ next.rebirth then
  match slotExact : abandonSlot config snapshot await with
  | .error reason => .error reason
  | .ok (slotPosts, slotClaims) =>
  match viewExact : readState config snapshot record.object with
  | .error reason => .error reason
  | .ok none => .error .stateMissing
  | .ok (some view) =>
  match typeResponse program .upgraded view with
  | .error reason => .error reason
  | .ok response =>
  match stateExact : decodeCheckpoint record.checkpoint with
  | none => .error .checkpointCodec
  | some state =>
  match resumeExact : resume (responseData .upgraded view).term state with
  | none => .error .checkpointCodec
  | some resumed =>
  let envelope := addCapacity record.escrow.timeout request.extra
  if covered : config.covers envelope = true then
  match segmentExact : abortSegment config envelope.sourceTicks resumed with
  | .error reason => .error reason
  | .ok segment =>
  let ended := nextRecord record (record.generation + 1) segment none
  match bookExact : loadBook config snapshot with
  | .error reason => .error reason
  | .ok book =>
  match batchExact : settlePurse config (logicalBook book.logical) (heldAccount request.record) record.escrow 0
      (deliveryCharges config record request.record .timedOut request.charging 0) segment with
  | .error reason => .error reason
  | .ok batch =>
  match postedExact : postings book batch with
  | .error reason => .error reason
  | .ok posted =>
    .ok ⟨record, recordExact, located, await, awaiting, idExact, digestExact, input, inputExact, program, programExact,
      object, objectExact, next, deadline, draining, due, old, notChosen, slotPosts, slotClaims, slotExact, view,
      viewExact, response, state, stateExact, resumed, resumeExact, envelope, rfl, covered, segment, segmentExact,
      ended, rfl, book, bookExact, batch, batchExact, posted, postings_batch postedExact, _, rfl, _, rfl⟩
  else .error (.uncovered envelope)
  else .error .rebirthDisposition
  else .error .notDraining
  else .error (.notYetDeadline deadline height)
  else .error .checkpointDigest
  else .error .awaitMismatch
  else .error .recordMisplaced

def Abort.intent {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height : Nat} {request : AbortRequest} (aborted : Abort config snapshot height request) (sealing : Seal) :
    DataIntent rootBytes :=
  intentOf rootBytes (abortTransaction aborted.await.id) aborted.posts
    [guardAt snapshot (packageCell config.domain aborted.record.pin),
      guardAt snapshot (stateCell config.domain aborted.record.object)] aborted.claims sealing

/-! ## REBIRTH -/

structure RebirthRequest where
  subject : SubjectId
  /-- The record cell of the activity left on the old package. -/
  record : CellId
  /-- The declared envelope of the new first segment (paid from the old purse). -/
  envelope : Capacity

/-- The birth a rebirth makes: the old activity's principal, object and stored
input, on the object's pin, under the old escrow terms; paid from the old purse
(the deposit is what the purse holds of the credit asset after the birth's own
price); the old activity its predecessor. -/
def rebirthRequest (config : Config) (book : Book) (request : RebirthRequest) (old : Record) (object : ObjectRecord)
    (input : Data) : BirthRequest :=
  ⟨old.escrow.payer, old.object, object.pin, input, old.activity.value, request.envelope, old.escrow.resume,
    old.escrow.timeout, heldAccount request.record,
    purse book config.asset (heldAccount request.record) - config.tariff.workOf request.envelope,
    some ⟨old.pin, old.activity, heldAccount request.record, old.escrow.account⟩⟩

def rebirthTransaction (await : Digest) : TransactionId :=
  tagged "DREGG/OBJECTIVE/ACTIVITY/TX/REBIRTH/v1" (digestStream.encode await)

structure Rebirth {rootBytes : Bytes → Digest} (config : Config) (snapshot : Snapshot rootBytes)
    (height : Nat) (request : RebirthRequest) where
  private mk ::
  old : Record
  oldExact : readRecord snapshot request.record = some old
  located : request.record = recordCell config.domain old.object old.activity
  await : Await
  awaiting : old.phase = .awaiting await
  idExact : await.id = awaitId request.record old.generation old.checkpointDigest
  object : ObjectRecord
  objectExact : readObject config snapshot old.object = .ok (some object)
  steady : object.phase = .steady
  /-- Left on another package by a migration: chosen for rebirth. -/
  frozen : old.pin ≠ object.pin
  input : Data
  inputExact : decodeDataBytes old.input = some input
  slotPosts : List Post
  slotClaims : List StableNullifier
  slotExact : abandonSlot config snapshot await = .ok (slotPosts, slotClaims)
  book : BookCell
  bookExact : loadBook config snapshot = .ok book
  born : Birth config snapshot height (rebirthRequest config (logicalBook book.logical) request old object input)
  bornExact : birth config snapshot height (rebirthRequest config (logicalBook book.logical) request old object input) =
    .ok born
  posts : List Post
  postsExact : posts = born.posts ++ (postAt snapshot request.record retiredImage :: slotPosts)
  claims : List StableNullifier
  claimsExact : claims = awaitClaim await.id :: slotClaims

def rebirth {rootBytes : Bytes → Digest} (config : Config) (snapshot : Snapshot rootBytes) (height : Nat)
    (request : RebirthRequest) : Except Refusal (Rebirth config snapshot height request) :=
  match oldExact : readRecord snapshot request.record with
  | none => .error (absentRecord snapshot request.record)
  | some old =>
  if located : request.record = recordCell config.domain old.object old.activity then
  match awaiting : old.phase with
  | .done _ | .faulted _ => .error .notAwaiting
  | .awaiting await =>
  if idExact : await.id = awaitId request.record old.generation old.checkpointDigest then
  match objectExact : readObject config snapshot old.object with
  | .error reason => .error reason
  | .ok none => .error .notAnObject
  | .ok (some object) =>
  if steady : object.phase = .steady then
  if frozen : old.pin ≠ object.pin then
  match inputExact : decodeDataBytes old.input with
  | none => .error .inputType
  | some input =>
  match slotExact : abandonSlot config snapshot await with
  | .error reason => .error reason
  | .ok (slotPosts, slotClaims) =>
  match bookExact : loadBook config snapshot with
  | .error reason => .error reason
  | .ok book =>
  match bornExact : birth config snapshot height (rebirthRequest config (logicalBook book.logical) request old object input) with
  | .error reason => .error reason
  | .ok born =>
    .ok ⟨old, oldExact, located, await, awaiting, idExact, object, objectExact, steady, frozen, input, inputExact,
      slotPosts, slotClaims, slotExact, book, bookExact, born, bornExact, _, rfl, _, rfl⟩
  else .error .rebirthDisposition
  else .error .notDraining
  else .error .awaitMismatch
  else .error .recordMisplaced

def Rebirth.intent {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height : Nat} {request : RebirthRequest} (reborn : Rebirth config snapshot height request) (sealing : Seal) :
    DataIntent rootBytes :=
  intentOf rootBytes (rebirthTransaction reborn.await.id) reborn.posts reborn.born.guards reborn.claims sealing

end Minidregg.Kernel.ObjectiveActivity
