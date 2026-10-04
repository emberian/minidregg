/- Every stored checkpoint is typed, in every reachable world (ObjectiveProofs).

`Kernel.ObjectiveResumeContract` proves the STEP: a birth stores a typed
checkpoint (`birth_checkpoint_typed`), and a delivery that decoded a typed
checkpoint stores one (`delivery_checkpoint_typed`, whose premise `prior` is the
induction hypothesis). This module closes the induction:

* `stored_checkpoints_typed`: in every snapshot reachable from a genesis whose
  record cells are typed, every record cell (a cell holding an activity record
  at its own coordinate `recordCell domain object activity`) holds an awaiting
  record whose checkpoint decodes to a state typed at the program its pinned
  package and input instantiate (`CheckpointTyped`);
* `reachable_delivery_typed`: so every delivery admitted on a reachable snapshot
  stores a typed checkpoint, with no premise left.

A step is one of two things (`Step`), and the node commits nothing else:

1. an admitted kernel turn (`ObjectiveActivity.AdmittedTurn`: `publish`,
   `create`, `birth`, `resolve`, `deliver`, `topUp`, `writeState`, `exhaust`,
   `abandon`), executed under any schedule and any receiver's sealing;
2. any other intent the ordinary gate admits (`ObjectiveActivityGate.ordinaryGate`:
   it writes no protected activity coordinate), under any schedule. The deployed
   source gate runs that gate for every facet but the kernel activity's own
   (`NativeHost.Config.sourceGate_ordinary`), and the replay walk's judge admits nothing
   else (`ObjectiveActivityGateRoute.derived_route`).

The induction rests on three things, and needs no hash or coordinate
disjointness:

* every kernel turn writes a cell only after reading it, so its admission knows
  the cell's role. It never writes over a cell that holds a package (`PostSafe`,
  first conjunct), so a program's package is never replaced;
* the only posts that hold a record are the record posts of `birth`, `deliver`
  and `exhaust`. Every other post is an image of another role or the Book, and
  `readRecord` reads none from it;
* foreign intents never write a protected coordinate, and records and packages
  live only there.

What it does NOT state: liveness. A typed record may still await for ever (its
decider silent, nobody delivering); that is the disposal turn `abandon`'s job,
not this invariant's. -/
import Kernel.ObjectiveResumeContract
import Kernel.ObjectiveActivityGate

namespace Minidregg.Kernel.ObjectiveCheckpointInvariant
open Minidregg.Theory Minidregg.Compiler
open Minidregg.Theory.TypedAuthorization (Digest SubjectId)
open Minidregg.Kernel.DurableDataIntent
open Minidregg.Kernel.ObjectiveActivityWire
open Minidregg.Kernel.ObjectiveActivity
open Minidregg.Kernel.ObjectiveResumeContract
open Minidregg.Theory.ObjectiveBendTyping
open Minidregg.Theory.ObjectiveBendDemandMachine (State)
open Minidregg.Theory.ObjectiveBendDemandData (Data)
open Minidregg.Theory.ObjectiveBendDemandTyping
open Minidregg.Compiler.ResourceBirthCodec (LifecycleImage)
set_option autoImplicit false

/-! ## Reading a cell's role -/

/-- The record a cell's bytes hold (`readRecord` of one cell). -/
def recordIn (bytes : Bytes) : Option Record := (bodyOf .record bytes).bind decodeRecord

theorem readRecord_eq {rootBytes : Bytes → Digest} (snapshot : Snapshot rootBytes) (cell : CellId) :
    readRecord snapshot cell = recordIn (snapshot.canonicalBytes cell) := rfl

/-- An activity image decodes to exactly its payload. -/
theorem payloadOf_image (role : ObjectiveActivityCell.Role) (key body : Bytes) :
    payloadOf (image role key body) = some ⟨role, key, body⟩ := by
  unfold payloadOf image
  rw [show LifecycleImage.bytes CanonicalCellRegistry.registry
        (.live ⟨.objectiveActivity, ObjectiveActivityCell.cellOf ⟨role, key, body⟩⟩) =
      (LifecycleImage.codec CanonicalCellRegistry.registry).encode
        (.live ⟨.objectiveActivity, ObjectiveActivityCell.cellOf ⟨role, key, body⟩⟩) from rfl,
    LifecycleImage.decode_encode]
  simp

theorem bodyOf_some {role : ObjectiveActivityCell.Role} {bytes body : Bytes}
    (found : bodyOf role bytes = some body) :
    ∃ payload, payloadOf bytes = some payload ∧ payload.role = role := by
  unfold bodyOf at found
  cases present : payloadOf bytes with
  | none => simp [present] at found
  | some payload =>
    refine ⟨payload, rfl, ?_⟩
    simp only [present, Option.bind_eq_bind, Option.bind_some] at found
    by_cases same : payload.role = role
    · exact same
    · simp [same] at found

theorem bodyOf_of_payload_none {role : ObjectiveActivityCell.Role} {bytes : Bytes}
    (absent : payloadOf bytes = none) : bodyOf role bytes = none := by
  simp [bodyOf, absent]

/-- A cell whose bytes hold an activity body of one role holds none of another. -/
theorem bodyOf_other {role other : ObjectiveActivityCell.Role} {bytes body : Bytes}
    (found : bodyOf role bytes = some body) (distinct : role ≠ other) : bodyOf other bytes = none := by
  obtain ⟨payload, present, named⟩ := bodyOf_some found
  simp only [bodyOf, present, Option.bind_eq_bind, Option.bind_some]
  rw [if_neg (by rw [named]; exact distinct)]

theorem bodyOf_image_other {role other : ObjectiveActivityCell.Role} (key body : Bytes)
    (distinct : role ≠ other) : bodyOf other (image role key body) = none :=
  bodyOf_other (bodyOf_image role key body) distinct

theorem recordIn_image_other {role : ObjectiveActivityCell.Role} (key body : Bytes)
    (distinct : role ≠ .record) : recordIn (image role key body) = none := by
  simp [recordIn, bodyOf_image_other key body distinct]

/-- The Book's image is no activity cell. -/
theorem payloadOf_book (book : BookCell) :
    payloadOf (LifecycleImage.bytes CanonicalCellRegistry.registry (.live ⟨.resourceBook, book⟩)) = none := by
  unfold payloadOf
  rw [show LifecycleImage.bytes CanonicalCellRegistry.registry (.live ⟨.resourceBook, book⟩) =
      (LifecycleImage.codec CanonicalCellRegistry.registry).encode (.live ⟨.resourceBook, book⟩) from rfl,
    LifecycleImage.decode_encode]

/-- A loaded Book cell holds no activity cell. -/
theorem loadBook_payload {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {book : BookCell} (loaded : loadBook config snapshot = .ok book) :
    payloadOf (snapshot.canonicalBytes config.bookCell) = none := by
  unfold loadBook at loaded
  cases found : bookOf (snapshot.canonicalBytes config.bookCell) with
  | none => simp [found] at loaded
  | some held =>
    unfold bookOf at found
    unfold payloadOf
    split at found
    · rename_i payload decoded
      rw [decoded]
    · cases found

/-- A cell `readState` accepts holds no package. -/
theorem readState_package {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {object : CellId} {current : Option ObjectState}
    (read : readState config snapshot object = .ok current) :
    bodyOf .package (snapshot.canonicalBytes (stateCell config.domain object)) = none := by
  cases found : bodyOf .state (snapshot.canonicalBytes (stateCell config.domain object)) with
  | some body => exact bodyOf_other found (by decide)
  | none =>
    cases present : payloadOf (snapshot.canonicalBytes (stateCell config.domain object)) with
    | none => exact bodyOf_of_payload_none present
    | some payload => simp [readState, found, present] at read

/-- A cell `readObject` finds empty holds no activity cell at all. -/
theorem readObject_none_payload {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {object : CellId} (read : readObject config snapshot object = .ok none) :
    payloadOf (snapshot.canonicalBytes (objectCell config.domain object)) = none := by
  cases found : bodyOf .object (snapshot.canonicalBytes (objectCell config.domain object)) with
  | some body =>
    simp only [readObject, found] at read
    split at read <;> cases read
  | none =>
    cases present : payloadOf (snapshot.canonicalBytes (objectCell config.domain object)) with
    | none => rfl
    | some payload => simp [readObject, found, present] at read

theorem readSlot_package {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {name : Digest} {slot : AnswerSlot.Slot} (read : readSlot config snapshot name = some slot) :
    bodyOf .package (snapshot.canonicalBytes (AnswerSlot.cell config.domain name)) = none := by
  unfold readSlot at read
  cases found : bodyOf .slot (snapshot.canonicalBytes (AnswerSlot.cell config.domain name)) with
  | none => simp [found] at read
  | some body => exact bodyOf_other found (by decide)

theorem readRecord_package {rootBytes : Bytes → Digest} {snapshot : Snapshot rootBytes}
    {cell : CellId} {record : Record} (read : readRecord snapshot cell = some record) :
    bodyOf .package (snapshot.canonicalBytes cell) = none := by
  unfold readRecord at read
  cases found : bodyOf .record (snapshot.canonicalBytes cell) with
  | none => simp [found] at read
  | some body => exact bodyOf_other found (by decide)

/-- A retired cell holds no record. -/
theorem recordIn_retired : recordIn retiredImage = none := by
  simp [recordIn, bodyOf, payloadOf_retired]

/-- The only record a record post holds is the record it posts, and only while it awaits:
an ended record is the retired image, which holds none. -/
theorem recordIn_recordImage {record found : Record}
    (read : recordIn (recordImage record) = some found) :
    found = record ∧ ∃ await, record.phase = .awaiting await := by
  unfold recordImage at read
  split at read
  · rename_i await awaiting
    simp only [recordIn, bodyOf_image, Option.bind_some, record_roundTrip, Option.some.injEq] at read
    exact ⟨read.symm, await, awaiting⟩
  · rw [recordIn_retired] at read; cases read
  · rw [recordIn_retired] at read; cases read

/-! ## The invariant -/

/-- The package body a snapshot holds for a pin. -/
def PackageBody {rootBytes : Bytes → Digest} (config : Config) (snapshot : Snapshot rootBytes)
    (pin : Digest) : Option Bytes :=
  bodyOf .package (snapshot.canonicalBytes (packageCell config.domain pin))

theorem packageBytes_eq {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {pin : Digest} {body : Bytes} (present : PackageBody config snapshot pin = some body) :
    packageBytes config snapshot pin = body := by
  unfold packageBytes; unfold PackageBody at present; rw [present]; rfl

theorem decodeStored_nil : decodeStored [] = none := by
  have frame : storedFrame ≠ [] := by decide +kernel
  simp [decodeStored, storedCodec, framed, framedRaw, ResourceBirthCodec.strictCodec, frame.symm]

/-- A program loads only from a package the snapshot holds. -/
theorem loadProgram_present {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {pin : Digest} {input : Data} {program : Program config pin input}
    (loaded : loadProgram config (packageBytes config snapshot pin) pin input = .ok program) :
    ∃ body, PackageBody config snapshot pin = some body ∧ packageBytes config snapshot pin = body := by
  cases present : PackageBody config snapshot pin with
  | some body => exact ⟨body, rfl, packageBytes_eq present⟩
  | none =>
    have empty : packageBytes config snapshot pin = [] := by
      unfold packageBytes; unfold PackageBody at present; rw [present]; rfl
    rw [empty] at loaded
    simp [loadProgram, decodeStored_nil, bind, Except.bind] at loaded

/-- **A record's checkpoint is typed.** The record awaits; the snapshot holds
its pinned package; its input decodes; the package and input instantiate a
program (`loadProgram`, the kernel's own loader, which re-checks the package at
every turn); and its checkpoint decodes to a state typed at that program's
checked type. -/
def CheckpointTyped (config : Config) (packageBody : Option Bytes) (record : Record) : Prop :=
  (∃ await, record.phase = .awaiting await) ∧
    ∃ body input, packageBody = some body ∧ decodeDataBytes record.input = some input ∧
      ∃ program : Program config record.pin input, loadProgram config body record.pin input = .ok program ∧
        ∃ state, decodeCheckpoint record.checkpoint = some state ∧
          ∃ types, Nonempty (StateTyping program.assumptions types state program.checked.type)

/-- **Every record cell of a snapshot is typed**: every cell that holds an
activity record at that record's own coordinate. -/
def RecordCellsTyped {rootBytes : Bytes → Digest} (config : Config) (snapshot : Snapshot rootBytes) : Prop :=
  ∀ cell record, readRecord snapshot cell = some record →
    cell = recordCell config.domain record.object record.activity →
      CheckpointTyped config (PackageBody config snapshot record.pin) record

theorem CheckpointTyped.transfer {config : Config} {before after : Option Bytes} {record : Record}
    (typed : CheckpointTyped config before record) (kept : ∀ body, before = some body → after = some body) :
    CheckpointTyped config after record := by
  obtain ⟨awaiting, body, input, present, rest⟩ := typed
  exact ⟨awaiting, body, input, kept body present, rest⟩

/-- A snapshot with no records is typed (the genesis condition). -/
theorem recordCellsTyped_of_empty {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    (empty : ∀ cell, readRecord snapshot cell = none) : RecordCellsTyped config snapshot := by
  intro cell record read _
  rw [empty cell] at read; cases read

/-! ## Posts that keep the invariant -/

/-- A post keeps the invariant: it does not write over a package, and a record
it holds at that record's own coordinate is typed (under the packages of the
snapshot it was decided on). -/
def PostSafe {rootBytes : Bytes → Digest} (config : Config) (snapshot : Snapshot rootBytes) (post : Post) : Prop :=
  bodyOf .package (snapshot.canonicalBytes post.cell) = none ∧
    ∀ record, recordIn post.bytes = some record →
      post.cell = recordCell config.domain record.object record.activity →
        CheckpointTyped config (PackageBody config snapshot record.pin) record

theorem postSafe_inert {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {post : Post} (pre : bodyOf .package (snapshot.canonicalBytes post.cell) = none)
    (inert : recordIn post.bytes = none) : PostSafe config snapshot post :=
  ⟨pre, fun record read => by rw [inert] at read; cases read⟩

theorem lookupPostBytes_posts {rootBytes : Bytes → Digest} {cell : CellId} {posts : List Post} {bytes : Bytes}
    (found : DataSnapshot.lookupPostBytes cell (posts.map (Post.write rootBytes)) = some bytes) :
    ∃ post ∈ posts, post.cell = cell ∧ post.bytes = bytes := by
  induction posts with
  | nil => simp [DataSnapshot.lookupPostBytes] at found
  | cons post rest ih =>
    simp only [List.map_cons, DataSnapshot.lookupPostBytes, Post.write] at found
    split at found
    · rename_i same
      cases found
      exact ⟨post, List.mem_cons_self .., same, rfl⟩
    · obtain ⟨other, member, named, exact⟩ := ih found
      exact ⟨other, List.mem_cons_of_mem _ member, named, exact⟩

theorem lookupPostBytes_absent {rootBytes : Bytes → Digest} {cell : CellId} {posts : List Post}
    (absent : ∀ post ∈ posts, post.cell ≠ cell) :
    DataSnapshot.lookupPostBytes cell (posts.map (Post.write rootBytes)) = none := by
  induction posts with
  | nil => rfl
  | cons post rest ih =>
    simp only [List.map_cons, DataSnapshot.lookupPostBytes, Post.write]
    rw [if_neg (absent post (List.mem_cons_self ..))]
    exact ih (fun other member => absent other (List.mem_cons_of_mem _ member))

/-- An installation of safe posts keeps every package the snapshot holds. -/
theorem install_package_kept {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {intent : DataIntent rootBytes} {posts : List Post}
    (writes : intent.writes = posts.map (Post.write rootBytes))
    (safe : ∀ post ∈ posts, PostSafe config snapshot post) (pin : Digest) (body : Bytes)
    (present : PackageBody config snapshot pin = some body) :
    PackageBody config (DataSnapshot.install snapshot intent) pin = some body := by
  unfold PackageBody at present ⊢
  rw [DataSnapshot.install_canonicalBytes, writes, lookupPostBytes_absent]
  · exact present
  · intro post member same
    have pre := (safe post member).1
    rw [same, present] at pre
    cases pre

/-- **An installation of safe posts keeps the invariant.** -/
theorem install_preserves {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {intent : DataIntent rootBytes} {posts : List Post} (typed : RecordCellsTyped config snapshot)
    (writes : intent.writes = posts.map (Post.write rootBytes))
    (safe : ∀ post ∈ posts, PostSafe config snapshot post) :
    RecordCellsTyped config (DataSnapshot.install snapshot intent) := by
  intro cell record read located
  have kept := install_package_kept writes safe record.pin
  rw [readRecord_eq, DataSnapshot.install_canonicalBytes, writes] at read
  cases found : DataSnapshot.lookupPostBytes cell (posts.map (Post.write rootBytes)) with
  | none =>
    rw [found, Option.getD_none] at read
    exact (typed cell record read located).transfer kept
  | some bytes =>
    rw [found, Option.getD_some] at read
    obtain ⟨post, member, named, exact⟩ := lookupPostBytes_posts found
    rw [← exact] at read
    exact ((safe post member).2 record read (named ▸ located)).transfer kept

/-- Whatever the schedule (accepted, crashed before or after the atomic install,
replayed, rejected), executing safe posts keeps the invariant. -/
theorem execute_preserves {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {intent : DataIntent rootBytes} {posts : List Post} (typed : RecordCellsTyped config snapshot)
    (writes : intent.writes = posts.map (Post.write rootBytes))
    (safe : ∀ post ∈ posts, PostSafe config snapshot post) (schedule : DurableCommitProtocol.Schedule) :
    RecordCellsTyped config ((execute schedule snapshot intent).storeAfter snapshot) := by
  rcases execute_no_partial_data_commit schedule snapshot intent with same | installed
  · rw [same]; exact typed
  · rw [installed]; exact install_preserves typed writes safe

/-! ## Every kernel turn's posts are safe -/

theorem book_post_safe {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {book : BookCell} (loaded : loadBook config snapshot = .ok book) (posted : Postings book) :
    PostSafe config snapshot (posted.write config snapshot) :=
  postSafe_inert (bodyOf_of_payload_none (loadBook_payload loaded))
    (by simp [recordIn, Postings.write, postAt, bodyOf, payloadOf_book])

theorem state_post_safe {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {object : CellId} {current : Option ObjectState} (read : readState config snapshot object = .ok current)
    (state : ObjectState) :
    PostSafe config snapshot (postAt snapshot (stateCell config.domain object) (stateImage object state)) :=
  postSafe_inert (readState_package read) (recordIn_image_other _ _ (by decide))

theorem slot_post_safe {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {name : Digest} (pre : bodyOf .package (snapshot.canonicalBytes (AnswerSlot.cell config.domain name)) = none)
    (bytes : Bytes) :
    PostSafe config snapshot (postAt snapshot (AnswerSlot.cell config.domain name) (image .slot (AnswerSlot.key name) bytes)) :=
  postSafe_inert pre (recordIn_image_other _ _ (by decide))

theorem slot_retire_safe {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {name : Digest} (pre : bodyOf .package (snapshot.canonicalBytes (AnswerSlot.cell config.domain name)) = none) :
    PostSafe config snapshot (slotRetire config snapshot name) :=
  postSafe_inert pre recordIn_retired

/-- A yield's posts (its declared-state write and the answer slot it opens) are safe. -/
theorem commitYield_safe {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height : Nat} {transaction : TransactionId} {cell object : CellId} {generation : Nat} {checkpoint : Digest}
    {current : Option ObjectState} {viewed : Bool} {plan : PlanAwait} {committed : YieldCommit}
    {seen : Option ObjectState} (read : readState config snapshot object = .ok seen)
    (ok : commitYield config snapshot height transaction cell object generation checkpoint current viewed plan =
      .ok committed) :
    ∀ post ∈ committed.posts, PostSafe config snapshot post := by
  unfold commitYield at ok
  split at ok
  · cases ok
  · split at ok
    · cases ok
    · rename_i written wrote
      have stateSafe : ∀ post ∈ (written.map StateWritten.post).toList, PostSafe config snapshot post := by
        intro post member
        cases written with
        | none => simp at member
        | some one =>
          simp only [Option.map_some, Option.toList_some, List.mem_singleton] at member
          subst member
          obtain ⟨_, _, _, _, exact⟩ := stateWrite_spec wrote
          rw [exact]
          exact state_post_safe read _
      split at ok
      · split at ok
        · cases ok
        · rename_i fresh
          simp only [Except.ok.injEq] at ok
          subst ok
          intro post member
          simp only [List.mem_append, List.mem_singleton] at member
          rcases member with inState | isSlot
          · exact stateSafe post inState
          · subst isSlot
            refine slot_post_safe (bodyOf_of_payload_none ?_) _
            have both := fresh
            simp only [Bool.or_eq_true, not_or, Option.isSome_iff_ne_none, ne_eq, not_not] at both
            exact both.1
      · split at ok
        · cases ok
        · simp only [Except.ok.injEq] at ok
          subst ok
          exact stateSafe

theorem segmentCommit_safe {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height : Nat} {transaction : TransactionId} {cell object : CellId} {generation : Nat}
    {current : Option ObjectState} {viewed : Bool} {segment : Segment} {committed : YieldCommit}
    {seen : Option ObjectState} (read : readState config snapshot object = .ok seen)
    (ok : segmentCommit config snapshot height transaction cell object generation current viewed segment =
      .ok (some committed)) :
    ∀ post ∈ committed.posts, PostSafe config snapshot post := by
  obtain ⟨_, _, _, committedExact⟩ := segmentCommit_spec ok
  exact commitYield_safe read committedExact

/-- A settlement's posts (the reclaimed slot, if the await had one) are safe. -/
theorem settle_safe {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height : Nat} {cell : CellId} {await : Await} {settlement : Settlement}
    (settled : settle config snapshot height cell await = .ok settlement) :
    ∀ post ∈ settlement.posts, PostSafe config snapshot post := by
  unfold settle at settled
  split at settled
  · rename_i name _ _
    cases read : readSlot config snapshot name with
    | none => simp [read] at settled
    | some slot =>
      have vacate : ∀ post ∈ [slotRetire config snapshot name], PostSafe config snapshot post := by
        intro post member
        simp only [List.mem_singleton] at member
        subst member
        exact slot_retire_safe (readSlot_package read)
      simp only [read] at settled
      split at settled
      · cases settled
      · split at settled
        · simp only [bind, Except.bind] at settled
          split at settled
          · cases settled
          · simp only [pure, Except.pure, Except.ok.injEq] at settled
            subst settled
            exact vacate
        · split at settled
          · simp only [Except.ok.injEq] at settled
            subst settled
            exact vacate
          · cases settled
  · split at settled
    · simp only [Except.ok.injEq] at settled; subst settled; simp
    · split at settled
      · simp only [Except.ok.injEq] at settled; subst settled; simp
      · cases settled

theorem abandonSlot_safe {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {await : Await} {posts : List Post} {claims : List StableNullifier}
    (ok : abandonSlot config snapshot await = .ok (posts, claims)) :
    ∀ post ∈ posts, PostSafe config snapshot post := by
  unfold abandonSlot at ok
  split at ok
  · simp only [Except.ok.injEq, Prod.mk.injEq] at ok
    rw [← ok.1]; simp
  · rename_i name _ _
    cases read : readSlot config snapshot name with
    | none => simp [read] at ok
    | some slot =>
      simp only [read] at ok
      have vacate : ∀ post ∈ [slotRetire config snapshot name], PostSafe config snapshot post := by
        intro post member
        simp only [List.mem_singleton] at member
        subst member
        exact slot_retire_safe (readSlot_package read)
      split at ok <;>
      · simp only [Except.ok.injEq, Prod.mk.injEq] at ok
        rw [← ok.1]; exact vacate

/-! ### Records: births, deliveries, exhaustions -/

theorem nextRecord_pin (base : Record) (generation : Nat) (segment : Segment) (yielded : Option YieldCommit) :
    (nextRecord base generation segment yielded).pin = base.pin := by
  cases segment <;> cases yielded <;> rfl

theorem nextRecord_input (base : Record) (generation : Nat) (segment : Segment) (yielded : Option YieldCommit) :
    (nextRecord base generation segment yielded).input = base.input := by
  cases segment <;> cases yielded <;> rfl

theorem nextRecord_awaiting {base : Record} {generation : Nat} {segment : Segment}
    {yielded : Option YieldCommit} {await : Await}
    (awaiting : (nextRecord base generation segment yielded).phase = .awaiting await) :
    ∃ state plan committed, segment = .yielded state plan ∧ yielded = some committed := by
  cases segment with
  | yielded state plan =>
    cases yielded with
    | some committed => exact ⟨state, plan, committed, rfl, rfl⟩
    | none => simp [nextRecord] at awaiting
  | finished _ => cases yielded <;> simp [nextRecord] at awaiting
  | faulted _ => cases yielded <;> simp [nextRecord] at awaiting

/-- The invariant at a delivery's record gives `delivery_checkpoint_typed` its premise. -/
theorem Delivery.prior {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height : Nat} {request : DeliverRequest} (delivery : Delivery config snapshot height request)
    (typed : CheckpointTyped config (PackageBody config snapshot delivery.record.pin) delivery.record) :
    ∃ types, Nonempty (StateTyping delivery.program.assumptions types delivery.state
      delivery.program.checked.type) := by
  obtain ⟨_, body, input, present, decoded, program, loaded, state, decodedState, types⟩ := typed
  have inputs : input = delivery.input := Option.some.inj (decoded.symm.trans delivery.inputExact)
  subst inputs
  have programs : program = delivery.program := by
    have exact := delivery.programExact
    rw [packageBytes_eq present, loaded] at exact
    exact Except.ok.inj exact
  have states : state = delivery.state := Option.some.inj (decodedState.symm.trans delivery.stateExact)
  subst programs states
  exact types

theorem birth_safe {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height : Nat} {request : BirthRequest} (born : Birth config snapshot height request) :
    ∀ post ∈ born.posts, PostSafe config snapshot post := by
  rw [born.postsExact]
  intro post member
  simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at member
  rcases member with isRecord | (inYield | isBook)
  · subst isRecord
    refine ⟨bodyOf_of_payload_none born.fresh, fun found read _ => ?_⟩
    obtain ⟨same, await, awaiting⟩ := recordIn_recordImage read
    subst same
    obtain ⟨state, plan, committed, yieldedSegment, _⟩ :=
      nextRecord_awaiting (born.recordExact ▸ awaiting)
    obtain ⟨decoded, types⟩ := birth_checkpoint_typed born yieldedSegment
    obtain ⟨body, present, bytes⟩ := loadProgram_present born.programExact
    have loaded := born.programExact
    rw [bytes] at loaded
    have pinIs : born.record.pin = request.pin := by rw [born.recordExact, nextRecord_pin]
    have inputIs : born.record.input = dataBytes request.input := by rw [born.recordExact, nextRecord_input]
    unfold CheckpointTyped
    rw [pinIs, inputIs]
    exact ⟨⟨await, awaiting⟩, body, request.input, present, decodeDataBytes_dataBytes _, born.program, loaded,
      state, decoded, types⟩
  · cases yielded : born.yielded with
    | none => simp [yielded] at inYield
    | some committed =>
      simp only [yielded, Option.map_some, Option.getD_some] at inYield
      have commit := born.yieldedExact
      rw [yielded] at commit
      exact segmentCommit_safe born.currentExact commit post inYield
  · subst isBook
    exact book_post_safe born.bookExact born.posted

theorem delivery_safe {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height : Nat} {request : DeliverRequest} (typed : RecordCellsTyped config snapshot)
    (delivery : Delivery config snapshot height request) :
    ∀ post ∈ delivery.posts, PostSafe config snapshot post := by
  have recordTyped := typed request.record delivery.record delivery.recordExact delivery.located
  rw [delivery.postsExact]
  intro post member
  simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at member
  rcases member with isRecord | ((inSettlement | inYield) | isBook)
  · subst isRecord
    refine ⟨readRecord_package delivery.recordExact, fun found read _ => ?_⟩
    obtain ⟨same, await, awaiting⟩ := recordIn_recordImage read
    subst same
    obtain ⟨state, plan, committed, yieldedSegment, _⟩ :=
      nextRecord_awaiting (delivery.nextExact ▸ awaiting)
    obtain ⟨decoded, types⟩ :=
      delivery_checkpoint_typed delivery (Delivery.prior delivery recordTyped) yieldedSegment
    obtain ⟨_, body, input, present, inputDecoded, _⟩ := recordTyped
    have inputs : input = delivery.input := Option.some.inj (inputDecoded.symm.trans delivery.inputExact)
    subst inputs
    have loaded := delivery.programExact
    rw [packageBytes_eq present] at loaded
    have pinIs : delivery.next.pin = delivery.record.pin := by rw [delivery.nextExact, nextRecord_pin]
    have inputIs : delivery.next.input = delivery.record.input := by rw [delivery.nextExact, nextRecord_input]
    unfold CheckpointTyped
    rw [pinIs, inputIs]
    exact ⟨⟨await, awaiting⟩, body, delivery.input, present, inputDecoded, delivery.program, loaded,
      state, decoded, types⟩
  · exact settle_safe delivery.settled post inSettlement
  · cases yielded : delivery.yielded with
    | none => simp [yielded] at inYield
    | some committed =>
      simp only [yielded, Option.map_some, Option.getD_some] at inYield
      have ended := delivery.endExact
      rw [yielded] at ended
      exact segmentCommit_safe delivery.viewExact (resumedSegment_committed ended).2 post inYield
  · subst isBook
    exact book_post_safe delivery.bookExact delivery.posted

theorem exhaustion_safe {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height : Nat} {request : ExhaustRequest} (typed : RecordCellsTyped config snapshot)
    (exhausted : Exhaustion config snapshot height request) :
    ∀ post ∈ exhausted.posts, PostSafe config snapshot post := by
  have recordTyped := typed request.record exhausted.record exhausted.recordExact exhausted.located
  rw [exhausted.postsExact]
  intro post member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with isRecord | isBook
  · subst isRecord
    refine ⟨readRecord_package exhausted.recordExact, fun found read _ => ?_⟩
    obtain ⟨same, _, _⟩ := recordIn_recordImage read
    subst same
    rw [exhausted.nextExact]
    exact recordTyped
  · subst isBook
    exact book_post_safe exhausted.bookExact exhausted.posted

theorem abandonment_safe {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height : Nat} {request : AbandonRequest} (abandoned : Abandonment config snapshot height request) :
    ∀ post ∈ abandoned.posts, PostSafe config snapshot post := by
  rw [abandoned.postsExact]
  intro post member
  simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at member
  rcases member with isRecord | (inSlot | isBook)
  · subst isRecord
    exact postSafe_inert (readRecord_package abandoned.recordExact) (recordIn_retired)
  · exact abandonSlot_safe abandoned.slotExact post inSlot
  · subst isBook
    exact book_post_safe abandoned.bookExact abandoned.posted

theorem resolution_safe {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height : Nat} {request : ResolveRequest} (resolution : Resolution config snapshot height request) :
    ∀ post ∈ resolution.posts, PostSafe config snapshot post := by
  rw [resolution.postsExact]
  intro post member
  simp only [List.mem_singleton] at member
  subst member
  obtain ⟨_, _, _, decided, _⟩ := AnswerSlot.decide_single_decider resolution.decidedExact
  have named : resolution.decided.name = request.slot := by rw [decided]; exact resolution.named
  have pre := readSlot_package resolution.slotExact
  unfold slotPost
  rw [named]
  exact slot_post_safe pre _

theorem publication_safe {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {stored : Stored} (publication : Publication config snapshot stored) :
    ∀ post ∈ publication.posts, PostSafe config snapshot post := by
  rw [publication.postsExact]
  intro post member
  simp only [List.mem_singleton] at member
  subst member
  exact postSafe_inert (bodyOf_of_payload_none publication.fresh) (recordIn_image_other _ _ (by decide))

theorem creation_safe {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {request : CreateRequest} (created : Creation config snapshot request) :
    ∀ post ∈ created.posts, PostSafe config snapshot post := by
  rw [created.postsExact]
  intro post member
  simp only [List.mem_singleton] at member
  subst member
  exact postSafe_inert (bodyOf_of_payload_none (readObject_none_payload created.absent))
    (recordIn_image_other _ _ (by decide))

theorem stateWrite_safe {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height : Nat} {request : StateWriteRequest} (written : StateWrite config snapshot height request) :
    ∀ post ∈ written.posts, PostSafe config snapshot post := by
  rw [written.postsExact]
  intro post member
  simp only [List.mem_singleton] at member
  subst member
  exact state_post_safe written.currentExact _

/-- **Every admitted kernel turn's posts are safe** on a typed snapshot. -/
theorem AdmittedTurn.safe {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height : Nat} (typed : RecordCellsTyped config snapshot) (turn : AdmittedTurn config snapshot height) :
    ∀ post ∈ turn.posts, PostSafe config snapshot post := by
  cases turn with
  | publish _ publication => exact publication_safe publication
  | create _ created => exact creation_safe created
  | birth _ born => exact birth_safe born
  | resolve _ resolution => exact resolution_safe resolution
  | deliver _ delivery => exact delivery_safe typed delivery
  | topUp _ topped =>
    intro post member
    simp only [AdmittedTurn.posts, List.mem_singleton] at member
    subst member
    exact book_post_safe topped.bookExact topped.posted
  | writeState _ written => exact stateWrite_safe written
  | exhaust _ exhausted => exact exhaustion_safe typed exhausted
  | abandon _ abandoned => exact abandonment_safe abandoned

/-! ## Reachable worlds -/

/-- One committed step of a world: an admitted kernel turn, or an intent the
ordinary gate admits; each under any schedule and (for a turn) any sealing. -/
inductive Step {rootBytes : Bytes → Digest} (config : Config) : Snapshot rootBytes → Snapshot rootBytes → Prop
  | turn {snapshot : Snapshot rootBytes} {height : Nat} (turn : AdmittedTurn config snapshot height)
      (sealing : Seal) (schedule : DurableCommitProtocol.Schedule) :
      Step config snapshot ((execute schedule snapshot (turn.intent sealing)).storeAfter snapshot)
  | foreign {snapshot : Snapshot rootBytes} (intent : DataIntent rootBytes)
      (admitted : ObjectiveActivityGate.ordinaryGate intent = .ok ()) (schedule : DurableCommitProtocol.Schedule) :
      Step config snapshot ((execute schedule snapshot intent).storeAfter snapshot)

/-- The worlds reachable from a genesis by steps. -/
inductive Reachable {rootBytes : Bytes → Digest} (config : Config) (genesis : Snapshot rootBytes) :
    Snapshot rootBytes → Prop
  | genesis : Reachable config genesis genesis
  | step {before after : Snapshot rootBytes} :
      Reachable config genesis before → Step config before after → Reachable config genesis after

/-- An intent the ordinary gate admits leaves every record cell and every
package cell as it was, so it keeps the invariant. -/
theorem foreign_preserves {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {intent : DataIntent rootBytes} (typed : RecordCellsTyped config snapshot)
    (admitted : ObjectiveActivityGate.ordinaryGate intent = .ok ()) (schedule : DurableCommitProtocol.Schedule) :
    RecordCellsTyped config ((execute schedule snapshot intent).storeAfter snapshot) := by
  intro cell record read located
  have recordKept := ObjectiveActivityGate.ordinary_execute_protected schedule snapshot admitted
    (cell := cell) (by rw [located]; exact ObjectiveActivityCell.coordinate_reserved _ _ _)
  have packageKept := ObjectiveActivityGate.ordinary_execute_protected schedule snapshot admitted
    (cell := packageCell config.domain record.pin) (ObjectiveActivityCell.coordinate_reserved _ _ _)
  rw [readRecord_eq, recordKept] at read
  unfold PackageBody
  rw [packageKept]
  exact typed cell record read located

/-- **Every step keeps the invariant.** -/
theorem Step.preserves {rootBytes : Bytes → Digest} {config : Config} {before after : Snapshot rootBytes}
    (typed : RecordCellsTyped config before) (step : Step config before after) :
    RecordCellsTyped config after := by
  cases step with
  | turn turn sealing schedule =>
    exact execute_preserves typed (AdmittedTurn.intent_writes sealing turn) (AdmittedTurn.safe typed turn) schedule
  | foreign intent admitted schedule => exact foreign_preserves typed admitted schedule

/-- **`stored_checkpoints_typed`.** In every world reachable from a genesis whose
record cells are typed, every record cell holds an awaiting record whose
checkpoint decodes to a state typed at the program its pinned package and its
input instantiate. -/
theorem stored_checkpoints_typed {rootBytes : Bytes → Digest} {config : Config}
    {genesis snapshot : Snapshot rootBytes} (genesisTyped : RecordCellsTyped config genesis)
    (reachable : Reachable config genesis snapshot) : RecordCellsTyped config snapshot := by
  induction reachable with
  | genesis => exact genesisTyped
  | step _ step typed => exact step.preserves typed

/-- **A delivery on a reachable world stores a typed checkpoint**, with no
premise left: `delivery_checkpoint_typed`'s `prior` is the invariant. -/
theorem reachable_delivery_typed {rootBytes : Bytes → Digest} {config : Config}
    {genesis snapshot : Snapshot rootBytes} (genesisTyped : RecordCellsTyped config genesis)
    (reachable : Reachable config genesis snapshot) {height : Nat} {request : DeliverRequest}
    (delivery : Delivery config snapshot height request)
    {state : State} {plan : PlanAwait} (yieldedSegment : delivery.segment = .yielded state plan) :
    decodeCheckpoint delivery.next.checkpoint = some state ∧
      ∃ types, Nonempty (StateTyping delivery.program.assumptions types state delivery.program.checked.type) :=
  delivery_checkpoint_typed delivery
    (Delivery.prior delivery (stored_checkpoints_typed genesisTyped reachable request.record delivery.record
      delivery.recordExact delivery.located)) yieldedSegment

#assert_axioms readRecord_eq
#assert_axioms payloadOf_image
#assert_axioms bodyOf_some
#assert_axioms bodyOf_of_payload_none
#assert_axioms bodyOf_other
#assert_axioms bodyOf_image_other
#assert_axioms recordIn_image_other
#assert_axioms payloadOf_book
#assert_axioms loadBook_payload
#assert_axioms readState_package
#assert_axioms readObject_none_payload
#assert_axioms readSlot_package
#assert_axioms readRecord_package
#assert_axioms recordIn_recordImage
#assert_axioms recordIn_retired
#assert_axioms packageBytes_eq
#assert_axioms decodeStored_nil
#assert_axioms loadProgram_present
#assert_axioms CheckpointTyped.transfer
#assert_axioms recordCellsTyped_of_empty
#assert_axioms postSafe_inert
#assert_axioms lookupPostBytes_posts
#assert_axioms lookupPostBytes_absent
#assert_axioms install_package_kept
#assert_axioms install_preserves
#assert_axioms execute_preserves
#assert_axioms book_post_safe
#assert_axioms state_post_safe
#assert_axioms slot_post_safe
#assert_axioms slot_retire_safe
#assert_axioms commitYield_safe
#assert_axioms segmentCommit_safe
#assert_axioms settle_safe
#assert_axioms abandonSlot_safe
#assert_axioms nextRecord_pin
#assert_axioms nextRecord_input
#assert_axioms nextRecord_awaiting
#assert_axioms Delivery.prior
#assert_axioms birth_safe
#assert_axioms delivery_safe
#assert_axioms exhaustion_safe
#assert_axioms abandonment_safe
#assert_axioms resolution_safe
#assert_axioms publication_safe
#assert_axioms creation_safe
#assert_axioms stateWrite_safe
#assert_axioms AdmittedTurn.safe
#assert_axioms foreign_preserves
#assert_axioms Step.preserves
#assert_axioms stored_checkpoints_typed
#assert_axioms reachable_delivery_typed
end Minidregg.Kernel.ObjectiveCheckpointInvariant
