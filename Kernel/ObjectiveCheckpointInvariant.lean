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
  stores a typed checkpoint, with no premise left;
* `reachable_delivery_stored_complete`: and that checkpoint is the checkpoint of the yield
  the delivery's own run retained, and resumes as that yield, under the kernel's own limits
  (`ObjectiveResumeContract.StoredComplete`), with no premise left.

A step is one of three things (`Step`), and the node commits nothing else:

1. an admitted kernel turn (`ObjectiveActivity.AdmittedTurn`: `publish`,
   `create`, `birth`, `resolve`, `deliver`, `topUp`, `exhaust`,
   `abandon`, `invoke`, `deliverMessage`, and the upgrade turns `adopt`, `migrate`,
   `abortDrained`, `rebirth`), executed under any schedule and any receiver's sealing, with its
   final posts (`ActivitySeatEnd.finalize`: an ending turn also closes the seats
   its activity holds);
2. a seat turn: an intent whose posts the seat kernel checked inert
   (`SeatStore.Inert`: no post sits on or writes a kernel-activity cell);
3. any other intent the ordinary gate admits (`ObjectiveActivityGate.ordinaryGate`:
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
import Kernel.ActivitySeatEnd
import Kernel.ObjectiveAdmittedTurn

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
  unfold readState stateFor at read
  cases present : payloadOf (snapshot.canonicalBytes (stateCell config.domain object)) with
  | none => exact bodyOf_of_payload_none present
  | some payload =>
    rw [present] at read
    simp only at read
    split at read
    · rename_i owned
      simp [bodyOf, present, owned.1]
    · cases read

/-- A cell `readObject` finds empty holds no activity cell at all. -/
theorem readObject_none_payload {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {object : CellId} (read : readObject config snapshot object = .ok none) :
    payloadOf (snapshot.canonicalBytes (objectCell config.domain object)) = none := by
  unfold readObject objectFor at read
  cases present : payloadOf (snapshot.canonicalBytes (objectCell config.domain object)) with
  | none => rfl
  | some payload =>
    rw [present] at read
    simp only at read
    split at read
    · split at read <;> cases read
    · cases read

/-- A cell `readObject` reads a record from holds no package. -/
theorem readObject_package {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {object : CellId} {record : ObjectRecord.ObjectRecord} (read : readObject config snapshot object = .ok (some record)) :
    bodyOf .package (snapshot.canonicalBytes (objectCell config.domain object)) = none := by
  unfold readObject objectFor at read
  cases present : payloadOf (snapshot.canonicalBytes (objectCell config.domain object)) with
  | none => exact bodyOf_of_payload_none present
  | some payload =>
    rw [present] at read
    simp only at read
    split at read
    · rename_i owned
      simp [bodyOf, present, owned.1]
    · cases read

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
theorem recordIn_recordImage {record found : Record} (fits : record.Fits)
    (read : recordIn (recordImage record) = some found) :
    found = record ∧ ∃ await, record.phase = .awaiting await := by
  unfold recordImage at read
  split at read
  · rename_i await awaiting
    simp only [recordIn, bodyOf_image, Option.bind_some, record_roundTrip record fits, Option.some.injEq] at read
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
    have refused : instantiate config [] pin input = .error .packageMissing := by
      simp [instantiate, decodeStored_nil, bind, Except.bind]; rfl
    simp [loadProgram, refused, bind, Except.bind] at loaded

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

/-- The counters' post of a turn (the object record image) is safe. -/
theorem countPosts_safe {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {object : CellId} {record : ObjectRecord.ObjectRecord} (read : readObject config snapshot object = .ok (some record))
    (pin activity : Digest) (before after : Bool) :
    ∀ post ∈ countPosts config snapshot object record pin activity before after, PostSafe config snapshot post := by
  intro post member
  rw [mem_countPosts member]
  exact postSafe_inert (readObject_package read) (recordIn_image_other _ _ (by decide))

theorem birth_safe {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height : Nat} {request : BirthRequest} (born : Birth config snapshot height request) :
    ∀ post ∈ born.posts, PostSafe config snapshot post := by
  rw [born.postsExact]
  intro post member
  simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at member
  rcases member with isRecord | ((inYield | isBook) | inCount)
  · subst isRecord
    refine ⟨bodyOf_of_payload_none born.fresh, fun found read _ => ?_⟩
    obtain ⟨same, await, awaiting⟩ := recordIn_recordImage born.record_fits read
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
  · rw [mem_objectPost inCount]
    exact postSafe_inert (readObject_package born.objectExact) (recordIn_image_other _ _ (by decide))

theorem delivery_safe {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height : Nat} {request : DeliverRequest} (typed : RecordCellsTyped config snapshot)
    (delivery : Delivery config snapshot height request) :
    ∀ post ∈ delivery.posts, PostSafe config snapshot post := by
  have recordTyped := typed request.record delivery.record delivery.recordExact delivery.located
  rw [delivery.postsExact]
  intro post member
  simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at member
  rcases member with isRecord | (((inSettlement | inYield) | isBook) | inCount)
  · subst isRecord
    refine ⟨readRecord_package delivery.recordExact, fun found read _ => ?_⟩
    obtain ⟨same, await, awaiting⟩ := recordIn_recordImage delivery.next_fits read
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
  · exact countPosts_safe delivery.objectExact _ _ _ _ post inCount

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
    obtain ⟨same, _, _⟩ := recordIn_recordImage exhausted.next_fits read
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
  rcases member with isRecord | ((inSlot | isBook) | inCount)
  · subst isRecord
    exact postSafe_inert (readRecord_package abandoned.recordExact) (recordIn_retired)
  · exact abandonSlot_safe abandoned.slotExact post inSlot
  · subst isBook
    exact book_post_safe abandoned.bookExact abandoned.posted
  · exact countPosts_safe abandoned.objectExact _ _ _ _ post inCount

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
    {height : Nat} {request : CreateRequest} (created : Creation config snapshot height request) :
    ∀ post ∈ created.posts, PostSafe config snapshot post := by
  rw [created.postsExact]
  intro post member
  rcases List.mem_cons.mp member with head | tail
  · subst head
    exact postSafe_inert (bodyOf_of_payload_none (readObject_none_payload created.absent))
      (recordIn_image_other _ _ (by decide))
  · cases seeded : request.seed with
    | none => simp [seeded] at tail
    | some seed =>
      simp only [seeded, Option.map_some, Option.toList_some, List.mem_singleton] at tail
      subst tail
      exact state_post_safe (created.stateFresh seed seeded) _

theorem readDomain_none_payload {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {id : Digest} (read : readDomain config snapshot id = .ok none) :
    payloadOf (snapshot.canonicalBytes (domainCell config.domain id)) = none := by
  unfold readDomain domainFor at read
  cases present : payloadOf (snapshot.canonicalBytes (domainCell config.domain id)) with
  | none => rfl
  | some payload =>
    rw [present] at read
    simp only at read
    split at read
    · split at read <;> cases read
    · cases read

/-- What `mapM` returned is what each element gave. -/
theorem mapM_zip {α β ε : Type} {f : α → Except ε β} :
    ∀ {xs : List α} {ys : List β}, xs.mapM f = .ok ys → ∀ pair ∈ xs.zip ys, f pair.1 = .ok pair.2
  | [], ys, _ => by simp
  | x :: xs, ys, done => by
    simp only [List.mapM_cons, bind, Except.bind, pure, Except.pure] at done
    cases fx : f x with
    | error e => rw [fx] at done; cases done
    | ok y =>
      rw [fx] at done
      simp only at done
      cases rest : xs.mapM f with
      | error e => rw [rest] at done; cases done
      | ok ys' =>
        rw [rest] at done
        simp only [Except.ok.injEq] at done
        subst done
        intro pair member
        simp only [List.zip_cons_cons, List.mem_cons] at member
        rcases member with rfl | inRest
        · exact fx
        · exact mapM_zip rest pair inRest

/-- A registration writes the fresh domain cell and the records of its members. -/
theorem registration_safe {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height : Nat} {request : RegisterRequest} (registered : Registration config snapshot height request) :
    ∀ post ∈ registered.posts, PostSafe config snapshot post := by
  rw [registered.postsExact]
  intro post member
  rcases List.mem_cons.mp member with head | tail
  · subst head
    exact postSafe_inert (bodyOf_of_payload_none (readDomain_none_payload registered.absent))
      (recordIn_image_other _ _ (by decide))
  · obtain ⟨⟨object, record⟩, inZip, rfl⟩ := List.mem_map.mp tail
    have read := mapM_zip registered.recordsExact _ inZip
    simp only [readMember] at read
    split at read
    · cases read
    · cases read
    · rename_i found
      cases read
      exact postSafe_inert (readObject_package found) (recordIn_image_other _ _ (by decide))

/-- An invocation writes only the Book and the state cells of objects its call
tree read: no record or package cell. -/
theorem invocation_safe {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height : Nat} {request : ObjectiveCall.InvokeRequest}
    (invoked : ObjectiveCall.Invocation config snapshot height request) :
    ∀ post ∈ invoked.posts, PostSafe config snapshot post := by
  intro post member
  rcases ObjectiveCall.Invocation.posts_shape invoked post member with
    isBook | ⟨_, _, state, readOk, isState⟩ | ⟨cell, clean, ⟨role, key, body, notRecord, isMail⟩ | isRetire⟩
  · subst isBook; exact book_post_safe invoked.bookExact invoked.posted
  · subst isState; exact state_post_safe readOk state
  · subst isMail; exact postSafe_inert clean (recordIn_image_other key body notRecord)
  · subst isRetire; exact postSafe_inert clean recordIn_retired

/-- A delivery's call tree posts only state cells of objects it read. -/
theorem outcome_posts_safe {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height : Nat} {target : Nat} {message : Inbox.Message} {outcome : ObjectiveSend.Outcome}
    (ran : ObjectiveSend.runMessage config snapshot height target message = outcome) :
    ∀ post ∈ outcome.posts config snapshot, PostSafe config snapshot post := by
  intro post member
  cases outcome with
  | failed _ => cases member
  | replied result journal =>
    simp only [ObjectiveSend.Outcome.posts] at member
    unfold ObjectiveSend.runMessage at ran
    split at ran
    · cases ran
    · split at ran
      · cases ran
      · rename_i execExact
        split at ran
        · cases ran
          obtain ⟨read, _⟩ := ObjectiveCall.exec_invariant config snapshot height _ _ _ [] _ _ _ _ _ _ execExact
            (by simp) (by intro _ _ h; cases h) (by intro _ h; cases h)
          simp only [ObjectiveCall.Journal.posts, List.mem_filterMap] at member
          obtain ⟨entry, entryIn, made⟩ := member
          obtain ⟨⟨current, readOk⟩, _⟩ := read entry entryIn
          split at made
          · cases found : entry.current with
            | none => simp [found] at made
            | some state =>
              simp only [found, Option.map_some, Option.some.injEq] at made
              subst made
              exact state_post_safe readOk state
          · cases made
        · cases ran

/-- A message delivery writes its inboxes and slots (cells it read), the slot it
decides, its call tree's state cells and the Book: no record or package cell. -/
theorem messageDelivery_safe {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height : Nat} {request : ObjectiveSend.MessageRequest}
    (delivered : ObjectiveSend.MessageDelivery config snapshot height request) :
    ∀ post ∈ delivered.posts, PostSafe config snapshot post := by
  rw [delivered.postsExact]
  intro post member
  rcases List.mem_append.mp member with front | last
  · rcases List.mem_append.mp front with fromCalls | fromMail
    · exact outcome_posts_safe delivered.outcomeExact post fromCalls
    · obtain ⟨cell, clean, ⟨role, key, body, notRecord, isMail⟩ | isRetire⟩ := delivered.mail.posts_shape post fromMail
      · subst isMail; exact postSafe_inert clean (recordIn_image_other key body notRecord)
      · subst isRetire; exact postSafe_inert clean recordIn_retired
  · simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at last
    rcases last with isSlot | isBook
    · subst isSlot
      unfold ObjectiveSend.replyPost
      split
      swap
      · rw [delivered.slotNamed]
        exact slot_retire_safe (readSlot_package delivered.slotExact)
      obtain ⟨_, _, _, decided⟩ := AnswerSlot.decideDelivery_single delivered.decidedExact
      have named : delivered.decided.name = delivered.message.id := by rw [decided]; exact delivered.slotNamed
      unfold slotPost
      rw [named]
      exact slot_post_safe (readSlot_package delivered.slotExact) _
    · subst isBook; exact book_post_safe delivered.bookExact delivered.posted

/-! ### The upgrade turns -/

/-- An ADOPT writes the object record and the Book. -/
theorem adoption_safe {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height : Nat} {request : AdoptRequest} (adopted : Adoption config snapshot height request) :
    ∀ post ∈ adopted.posts, PostSafe config snapshot post := by
  rw [adopted.postsExact]
  intro post member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with isObject | isBook
  · subst isObject
    exact postSafe_inert (readObject_package adopted.recordExact) (recordIn_image_other _ _ (by decide))
  · subst isBook
    exact book_post_safe adopted.bookExact adopted.posted

/-- A MIGRATE writes the object record, the migrated state and the Book. -/
theorem migration_safe {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height : Nat} {request : MigrateRequest} (migrated : Migrated config snapshot height request) :
    ∀ post ∈ migrated.posts, PostSafe config snapshot post := by
  rw [migrated.postsExact]
  intro post member
  simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at member
  rcases member with isObject | inState | isBook
  · subst isObject
    exact postSafe_inert (readObject_package migrated.recordExact) (recordIn_image_other _ _ (by decide))
  · unfold migratedStatePosts at inState
    split at inState
    · simp only [List.mem_singleton] at inState
      subst inState
      exact state_post_safe migrated.currentExact _
    · cases inState
  · subst isBook
    exact book_post_safe migrated.bookExact migrated.posted

/-- An abort retires the record, reclaims the slot, writes the Book and the counters. -/
theorem abort_safe {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height : Nat} {request : AbortRequest} (aborted : Abort config snapshot height request) :
    ∀ post ∈ aborted.posts, PostSafe config snapshot post := by
  rw [aborted.postsExact]
  intro post member
  simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at member
  rcases member with isRecord | ((inSlot | isBook) | inCount)
  · subst isRecord
    have ended : ∀ await, aborted.ended.phase ≠ .awaiting await := by
      rw [aborted.endedExact]
      exact nextRecord_ended _ _ _ _ (abortSegment_ends aborted.segmentExact)
    refine postSafe_inert (readRecord_package aborted.recordExact) ?_
    simp only [recordPost, postAt, recordImage_ended _ ended]
    exact recordIn_retired
  · exact abandonSlot_safe aborted.slotExact post inSlot
  · subst isBook
    exact book_post_safe aborted.bookExact aborted.posted
  · exact countPosts_safe aborted.objectExact _ _ _ _ post inCount

/-- A rebirth is a birth, plus the old record retired and its slot reclaimed. -/
theorem rebirth_safe {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height : Nat} {request : RebirthRequest} (reborn : Rebirth config snapshot height request) :
    ∀ post ∈ reborn.posts, PostSafe config snapshot post := by
  rw [reborn.postsExact]
  intro post member
  rcases List.mem_append.mp member with inBirth | inOld
  · exact birth_safe reborn.born post inBirth
  · rcases List.mem_cons.mp inOld with isOld | inSlot
    · subst isOld
      exact postSafe_inert (readRecord_package reborn.oldExact) recordIn_retired
    · exact abandonSlot_safe reborn.slotExact post inSlot

/-- **Every admitted kernel turn's posts are safe** on a typed snapshot. -/
theorem AdmittedTurn.safe {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height : Nat} (typed : RecordCellsTyped config snapshot) (turn : AdmittedTurn config snapshot height) :
    ∀ post ∈ turn.posts, PostSafe config snapshot post := by
  cases turn with
  | publish _ publication => exact publication_safe publication
  | create _ created => exact creation_safe created
  | birth _ _ born => exact birth_safe born
  | resolve _ resolution => exact resolution_safe resolution
  | deliver _ delivery => exact delivery_safe typed delivery
  | topUp _ topped =>
    intro post member
    simp only [AdmittedTurn.posts, List.mem_singleton] at member
    subst member
    exact book_post_safe topped.bookExact topped.posted
  | exhaust _ exhausted => exact exhaustion_safe typed exhausted
  | abandon _ abandoned => exact abandonment_safe abandoned
  | invoke _ invoked => exact invocation_safe invoked
  | deliverMessage _ delivered => exact messageDelivery_safe delivered
  | adopt _ adopted => exact adoption_safe adopted
  | migrate _ migrated => exact migration_safe migrated
  | abortDrained _ aborted => exact abort_safe aborted
  | rebirth _ reborn => exact rebirth_safe reborn
  | registerDomain _ registered => exact registration_safe registered

/-! ## An ending turn's final posts are safe

A turn that ends an activity holding seats commits the joint posts: its own with
the Book post replaced by the joint batch's, then the seat cells the closing
changed (`ActivitySeatEnd.Joined.rewrite`). The replaced Book post sits on the
cell its original sat on and holds the Book; a closing post sits on a cell that
holds no kernel-activity cell and is none (`HeldEnd.inert`, the closing's own
check). -/

/-- The writes of an admitted turn's final intent are exactly its final posts. -/
theorem finalIntent_writes {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height : Nat} (sealing : Seal) {turn : AdmittedTurn config snapshot height} {posts : List Post}
    {extra : List ReadGuard} :
    (ActivitySeatEnd.AdmittedTurn.finalIntent sealing posts extra turn).writes = posts.map (Post.write rootBytes) := by
  cases turn <;> rfl

/-- **Posts the seat kernel checked inert are safe**: they sit on no package and
write no record. -/
theorem inert_safe {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {posts : List Post} (inert : SeatStore.Inert snapshot posts) :
    ∀ post ∈ posts, PostSafe config snapshot post := fun post member =>
  postSafe_inert (bodyOf_of_payload_none (inert post member).1)
    (by simp [recordIn, bodyOf_of_payload_none (inert post member).2])

/-- **An ending turn's final posts are safe.** -/
theorem finalize_safe {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height : Nat} (typed : RecordCellsTyped config snapshot) (turn : AdmittedTurn config snapshot height)
    {posts : List Post} {extra : List ReadGuard}
    (final : ActivitySeatEnd.finalize config snapshot height turn = .ok (posts, extra)) :
    ∀ post ∈ posts, PostSafe config snapshot post := by
  have safe := AdmittedTurn.safe typed turn
  unfold ActivitySeatEnd.finalize at final
  cases ending : ActivitySeatEnd.AdmittedTurn.ending turn with
  | none =>
    rw [ending] at final
    simp only [Except.ok.injEq, Prod.mk.injEq] at final
    rw [← final.1]; exact safe
  | some found =>
    obtain ⟨record, pre, posted⟩ := found
    rw [ending] at final
    cases joined : ActivitySeatEnd.join config snapshot height record posted with
    | error reason => simp [joined] at final
    | ok optional =>
      cases optional with
      | none =>
        simp only [joined, Except.ok.injEq, Prod.mk.injEq] at final
        rw [← final.1]; exact safe
      | some made =>
        simp only [joined, Except.ok.injEq, Prod.mk.injEq] at final
        rw [← final.1]
        intro post member
        unfold ActivitySeatEnd.Joined.rewrite at member
        rcases List.mem_append.mp member with mapped | closing
        · obtain ⟨original, inOriginal, replaced⟩ := List.mem_map.mp mapped
          by_cases isBook : original.cell = config.bookCell
          · rw [if_pos isBook] at replaced
            subst replaced
            have base := safe original inOriginal
            refine ⟨?_, fun found read _ => ?_⟩
            · simpa [ActivitySeatEnd.Joined.bookPost, postAt, isBook] using base.1
            · simp [recordIn, ActivitySeatEnd.Joined.bookPost, postAt, bodyOf, payloadOf_book] at read
          · rw [if_neg isBook] at replaced
            subst replaced
            exact safe original inOriginal
        · exact inert_safe made.held.inert post closing

/-! ## Who may write an inbox, who may decide a delivery slot (OB8, over the WHOLE turn sum)

Two facts about the object kernel's turns that the per-turn theorems
(`MessageDelivery.decides_own_slot`, `Inbox.Lawful`) do not state, because each
speaks about one turn:

* `AdmittedTurn.inbox_writers`: a post of an admitted turn's final posts that
  installs an inbox (an activity payload of role `inbox`: `HoldsInbox`) comes from
  a turn that SENDS (`AdmittedTurn.Sends`: an invocation whose call tree sent, or a
  `deliverMessage`, which forwards).
* `AdmittedTurn.delivery_deciders`: a post that DECIDES a delivery slot
  (`DecidesDelivery`: a slot payload whose decider is `delivery m` and whose phase
  is decided) comes from `deliverMessage`, and from no other turn.

Both are proved by cases over the WHOLE `AdmittedTurn` sum, with NO wildcard arm,
and `AdmittedTurn.Sends` / `AdmittedTurn.DeliversMessage` list every constructor:
a new turn constructor makes the definitions and the proofs fail to elaborate
until its author has said, arm by arm, whether it writes an inbox or decides a
delivery slot. That is the point of stating the facts here and not per turn. The
facts are about the turn's FINAL posts (`ActivitySeatEnd.finalize`, which adds the
seat cells an ending activity closes and rewrites the Book post), and, through
`finalIntent_writes`, about every write of its final intent
(`AdmittedTurn.final_writes_inbox_writers`, `AdmittedTurn.final_writes_delivery_deciders`).

They are statements about BYTES (the role tag of the activity payload a write
installs), not about coordinates: which coordinate an inbox sits at is a hash
(`Inbox.cell`), and the checkpoint invariant needs no coordinate disjointness.
The detectors are non-vacuous (`holdsInbox_inboxImage`, `decidesDelivery_decided_slot`,
`MessageDelivery.decides_delivery_slot`): the images a send and a delivery write
satisfy them. -/

/-- The bytes hold an inbox: an activity payload of role `inbox`. -/
def HoldsInbox (bytes : Bytes) : Prop := bodyOf .inbox bytes ≠ none

/-- The bytes hold a delivery slot that is DECIDED: a slot payload whose decider
is the role `delivery message` and whose phase is `decided`. -/
def DecidesDelivery (bytes : Bytes) : Prop :=
  ∃ (body : Bytes) (slot : AnswerSlot.Slot) (message : Digest) (decision : AnswerSlot.Decision) (at_ : Nat),
    bodyOf .slot bytes = some body ∧ AnswerSlot.decode body = some slot ∧
      slot.decider = .delivery message ∧ slot.phase = .decided decision at_

theorem holdsInbox_inboxImage (inbox : Inbox.Inbox) : HoldsInbox (inboxImage inbox) := by
  intro absent
  unfold inboxImage at absent
  rw [bodyOf_image] at absent
  cases absent

theorem decidesDelivery_decided_slot {slot : AnswerSlot.Slot} {message : Digest}
    {decision : AnswerSlot.Decision} {at_ : Nat} (role : slot.decider = .delivery message)
    (decided : slot.phase = .decided decision at_) :
    DecidesDelivery (image .slot (AnswerSlot.key slot.name) (AnswerSlot.encode slot)) :=
  ⟨AnswerSlot.encode slot, slot, message, decision, at_, bodyOf_image _ _ _, AnswerSlot.roundTrip slot, role,
    decided⟩

theorem not_holdsInbox_of_payload_none {bytes : Bytes} (absent : payloadOf bytes = none) :
    ¬ HoldsInbox bytes := fun held => held (bodyOf_of_payload_none absent)

theorem not_holdsInbox_image {bytes : Bytes} {role : ObjectiveActivityCell.Role} {key body : Bytes}
    (shape : bytes = image role key body) (other : role ≠ .inbox) : ¬ HoldsInbox bytes := by
  subst shape
  exact fun held => held (bodyOf_image_other key body other)

theorem not_decidesDelivery_of_payload_none {bytes : Bytes} (absent : payloadOf bytes = none) :
    ¬ DecidesDelivery bytes := by
  rintro ⟨_, _, _, _, _, found, _⟩
  rw [bodyOf_of_payload_none absent] at found
  cases found

theorem not_decidesDelivery_image {bytes : Bytes} {role : ObjectiveActivityCell.Role} {key body : Bytes}
    (shape : bytes = image role key body) (other : role ≠ .slot) : ¬ DecidesDelivery bytes := by
  subst shape
  rintro ⟨_, _, _, _, _, found, _⟩
  rw [bodyOf_image_other key body other] at found
  cases found

/-- A slot image decides no delivery slot when the slot it holds does not. -/
theorem not_decidesDelivery_slot {bytes : Bytes} {slot : AnswerSlot.Slot}
    (shape : bytes = image .slot (AnswerSlot.key slot.name) (AnswerSlot.encode slot))
    (undecided : ∀ (message : Digest) (decision : AnswerSlot.Decision) (at_ : Nat),
      slot.decider = .delivery message → slot.phase ≠ .decided decision at_) :
    ¬ DecidesDelivery bytes := by
  subst shape
  rintro ⟨stored, other, message, decision, at_, found, decoded, role, phase⟩
  rw [bodyOf_image] at found
  cases found
  rw [AnswerSlot.roundTrip] at decoded
  cases decoded
  exact undecided message decision at_ role phase

/-- A post that holds no inbox and decides no delivery slot. -/
def Quiet (bytes : Bytes) : Prop := ¬ HoldsInbox bytes ∧ ¬ DecidesDelivery bytes

theorem quiet_of_payload_none {bytes : Bytes} (absent : payloadOf bytes = none) : Quiet bytes :=
  ⟨not_holdsInbox_of_payload_none absent, not_decidesDelivery_of_payload_none absent⟩

theorem quiet_image {bytes : Bytes} {role : ObjectiveActivityCell.Role} {key body : Bytes}
    (shape : bytes = image role key body) (notInbox : role ≠ .inbox) (notSlot : role ≠ .slot) : Quiet bytes :=
  ⟨not_holdsInbox_image shape notInbox, not_decidesDelivery_image shape notSlot⟩

theorem quiet_recordPost {rootBytes : Bytes → Digest} (config : Config) (snapshot : Snapshot rootBytes)
    (cell : CellId) (record : Record) : Quiet (recordPost config snapshot cell record).bytes := by
  cases hp : record.phase with
  | awaiting await =>
    exact quiet_image (role := .record) (key := recordKey record.object record.activity)
      (body := encodeRecord record) (by simp [recordPost, recordImage, postAt, hp]) (by decide) (by decide)
  | done result =>
    exact quiet_of_payload_none (by simp [recordPost, recordImage, postAt, hp, payloadOf_retired])
  | faulted reason =>
    exact quiet_of_payload_none (by simp [recordPost, recordImage, postAt, hp, payloadOf_retired])

/-- A yield's posts (its declared-state write, the slot it opens) are quiet: the
slot it opens is open. -/
theorem yielded_posts_quiet {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height : Nat} {transaction : TransactionId} {cell object : CellId} {generation : Nat}
    {current : Option ObjectState} {viewed : Bool} {segment : Segment} {yielded : Option YieldCommit}
    (ok : segmentCommit config snapshot height transaction cell object generation current viewed segment =
      .ok yielded) :
    ∀ post ∈ (yielded.map YieldCommit.posts).getD [], Quiet post.bytes := by
  intro post member
  cases yielded with
  | none => simp at member
  | some committed =>
    obtain ⟨_, _, _, committedOk⟩ := segmentCommit_spec ok
    rcases commitYield_posts committedOk post member with ⟨state, isState⟩ | ⟨slot, _, opened, isSlot⟩
    · exact quiet_image (role := .state) (key := stateKey object) (body := ObjectState.encodeObjectState state)
        (isState.trans rfl) (by decide) (by decide)
    · exact ⟨not_holdsInbox_image isSlot (by decide),
        not_decidesDelivery_slot isSlot (fun _ _ _ _ phase => by rw [opened] at phase; cases phase)⟩

theorem birth_quiet {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height : Nat} {request : BirthRequest} (born : Birth config snapshot height request) :
    ∀ post ∈ born.posts, Quiet post.bytes := by
  rw [born.postsExact]
  intro post member
  simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at member
  rcases member with isRecord | ((inYield | isBook) | inCount)
  · subst isRecord; exact quiet_recordPost config snapshot born.cell born.record
  · exact yielded_posts_quiet born.yieldedExact post inYield
  · subst isBook; exact quiet_of_payload_none (Postings.write_payload config snapshot born.posted)
  · rw [mem_objectPost inCount]; exact quiet_image (role := .object) rfl (by decide) (by decide)

theorem delivery_quiet {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height : Nat} {request : DeliverRequest} (delivery : Delivery config snapshot height request) :
    ∀ post ∈ delivery.posts, Quiet post.bytes := by
  have retired := settle_posts_retired delivery.settled
  rw [delivery.postsExact]
  intro post member
  simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at member
  rcases member with isRecord | (((inSettlement | inYield) | isBook) | inCount)
  · subst isRecord; exact quiet_recordPost config snapshot request.record delivery.next
  · exact quiet_of_payload_none (by rw [retired post inSettlement]; exact payloadOf_retired)
  · exact yielded_posts_quiet (resumedSegment_commit delivery.endExact) post inYield
  · subst isBook; exact quiet_of_payload_none (Postings.write_payload config snapshot delivery.posted)
  · rw [mem_countPosts inCount]; exact quiet_image (role := .object) rfl (by decide) (by decide)

theorem exhaustion_quiet {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height : Nat} {request : ExhaustRequest} (exhausted : Exhaustion config snapshot height request) :
    ∀ post ∈ exhausted.posts, Quiet post.bytes := by
  rw [exhausted.postsExact]
  intro post member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with isRecord | isBook
  · subst isRecord; exact quiet_recordPost config snapshot request.record exhausted.next
  · subst isBook; exact quiet_of_payload_none (Postings.write_payload config snapshot exhausted.posted)

theorem abandonSlot_quiet {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {await : Await} {posts : List Post} {claims : List StableNullifier}
    (ok : abandonSlot config snapshot await = .ok (posts, claims)) :
    ∀ post ∈ posts, Quiet post.bytes := by
  unfold abandonSlot at ok
  split at ok
  · simp only [Except.ok.injEq, Prod.mk.injEq] at ok
    rw [← ok.1]; simp
  · rename_i name _ _
    cases read : readSlot config snapshot name with
    | none => simp [read] at ok
    | some slot =>
      simp only [read] at ok
      have vacate : ∀ post ∈ [slotRetire config snapshot name], Quiet post.bytes := by
        intro post member
        simp only [List.mem_singleton] at member
        subst member
        exact quiet_of_payload_none payloadOf_retired
      split at ok <;>
      · simp only [Except.ok.injEq, Prod.mk.injEq] at ok
        rw [← ok.1]; exact vacate

theorem abandonment_quiet {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height : Nat} {request : AbandonRequest} (abandoned : Abandonment config snapshot height request) :
    ∀ post ∈ abandoned.posts, Quiet post.bytes := by
  rw [abandoned.postsExact]
  intro post member
  simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at member
  rcases member with isRecord | ((inSlot | isBook) | inCount)
  · subst isRecord; exact quiet_of_payload_none payloadOf_retired
  · exact abandonSlot_quiet abandoned.slotExact post inSlot
  · subst isBook; exact quiet_of_payload_none (Postings.write_payload config snapshot abandoned.posted)
  · rw [mem_countPosts inCount]; exact quiet_image (role := .object) rfl (by decide) (by decide)

/-- A resolution decides a SUBJECT slot (`AnswerSlot.decide_single_decider`): its
decided slot keeps the decider `subject`, never `delivery`. -/
theorem resolution_quiet {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height : Nat} {request : ResolveRequest} (resolution : Resolution config snapshot height request) :
    ∀ post ∈ resolution.posts, Quiet post.bytes := by
  rw [resolution.postsExact]
  intro post member
  simp only [List.mem_singleton] at member
  subst member
  obtain ⟨subject, _, _, decided, _⟩ := AnswerSlot.decide_single_decider resolution.decidedExact
  have role : resolution.decided.decider = .subject request.subject := by rw [decided]; exact subject
  exact ⟨not_holdsInbox_image (role := .slot) (key := AnswerSlot.key resolution.decided.name)
      (body := AnswerSlot.encode resolution.decided) rfl (by decide),
    not_decidesDelivery_slot (slot := resolution.decided) rfl
      (fun message _ _ isDelivery _ => by rw [role] at isDelivery; cases isDelivery)⟩

theorem publication_quiet {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {stored : Stored} (publication : Publication config snapshot stored) :
    ∀ post ∈ publication.posts, Quiet post.bytes := by
  rw [publication.postsExact]
  intro post member
  simp only [List.mem_singleton] at member
  subst member
  exact quiet_image (role := .package) rfl (by decide) (by decide)

/-- A creation posts its object record and, when it carries a seed, that state cell's
first image: neither is an inbox or a delivery slot. -/
theorem creation_quiet {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height : Nat} {request : CreateRequest} (created : Creation config snapshot height request) :
    ∀ post ∈ created.posts, Quiet post.bytes := by
  rw [created.postsExact]
  intro post member
  rcases List.mem_cons.mp member with head | tail
  · subst head
    exact quiet_image (role := .object) rfl (by decide) (by decide)
  · cases seeded : request.seed with
    | none => simp [seeded] at tail
    | some seed =>
      simp only [seeded, Option.map_some, Option.toList_some, List.mem_singleton] at tail
      subst tail
      exact quiet_image (role := .state) rfl (by decide) (by decide)

theorem registration_quiet {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height : Nat} {request : RegisterRequest} (registered : Registration config snapshot height request) :
    ∀ post ∈ registered.posts, Quiet post.bytes := by
  rw [registered.postsExact]
  intro post member
  rcases List.mem_cons.mp member with head | tail
  · subst head; exact quiet_image (role := .domain) rfl (by decide) (by decide)
  · obtain ⟨_, _, rfl⟩ := List.mem_map.mp tail
    exact quiet_image (role := .object) rfl (by decide) (by decide)

theorem adoption_quiet {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height : Nat} {request : AdoptRequest} (adopted : Adoption config snapshot height request) :
    ∀ post ∈ adopted.posts, Quiet post.bytes := by
  rw [adopted.postsExact]
  intro post member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with isObject | isBook
  · subst isObject; exact quiet_image (role := .object) rfl (by decide) (by decide)
  · subst isBook; exact quiet_of_payload_none (Postings.write_payload config snapshot adopted.posted)

theorem migration_quiet {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height : Nat} {request : MigrateRequest} (migrated : Migrated config snapshot height request) :
    ∀ post ∈ migrated.posts, Quiet post.bytes := by
  rw [migrated.postsExact]
  intro post member
  simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at member
  rcases member with isObject | inState | isBook
  · subst isObject; exact quiet_image (role := .object) rfl (by decide) (by decide)
  · unfold migratedStatePosts at inState
    split at inState
    · simp only [List.mem_singleton] at inState
      subst inState
      exact quiet_image (role := .state) rfl (by decide) (by decide)
    · cases inState
  · subst isBook; exact quiet_of_payload_none (Postings.write_payload config snapshot migrated.posted)

theorem abort_quiet {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height : Nat} {request : AbortRequest} (aborted : Abort config snapshot height request) :
    ∀ post ∈ aborted.posts, Quiet post.bytes := by
  rw [aborted.postsExact]
  intro post member
  simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at member
  rcases member with isRecord | ((inSlot | isBook) | inCount)
  · subst isRecord; exact quiet_recordPost config snapshot request.record aborted.ended
  · exact abandonSlot_quiet aborted.slotExact post inSlot
  · subst isBook; exact quiet_of_payload_none (Postings.write_payload config snapshot aborted.posted)
  · rw [mem_countPosts inCount]; exact quiet_image (role := .object) rfl (by decide) (by decide)

theorem rebirth_quiet {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height : Nat} {request : RebirthRequest} (reborn : Rebirth config snapshot height request) :
    ∀ post ∈ reborn.posts, Quiet post.bytes := by
  rw [reborn.postsExact]
  intro post member
  rcases List.mem_append.mp member with inBirth | inOld
  · exact birth_quiet reborn.born post inBirth
  · rcases List.mem_cons.mp inOld with isOld | inSlot
    · subst isOld; exact quiet_of_payload_none payloadOf_retired
    · exact abandonSlot_quiet reborn.slotExact post inSlot

/-- What an invocation posts, by payload: the Book, a state image, or its mail. -/
theorem invocation_posts_cases {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height : Nat} {request : ObjectiveCall.InvokeRequest}
    (invoked : ObjectiveCall.Invocation config snapshot height request) :
    ∀ post ∈ invoked.posts, payloadOf post.bytes = none ∨
      (∃ (object : CellId) (state : ObjectState), post.bytes = stateImage object state) ∨
      post ∈ invoked.mail.posts := by
  rw [invoked.postsExact]
  intro post member
  rcases List.mem_append.mp member with inFront | isBook
  · rcases List.mem_append.mp inFront with inJournal | inMail
    · obtain ⟨entry, _, state, shape⟩ := ObjectiveCall.Journal.posts_state invoked.journal config snapshot post inJournal
      exact .inr (.inl ⟨entry.object, state, (congrArg Post.bytes shape).trans rfl⟩)
    · exact .inr (.inr inMail)
  · simp only [List.mem_singleton] at isBook
    subst isBook
    exact .inl (Postings.write_payload config snapshot invoked.posted)

/-- The mail of an invocation whose call tree sent nothing: no inbox, no slot, no credit;
and when it cancelled nothing either, every slot it closed is retired. -/
theorem invocation_mail_silent {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height : Nat} {request : ObjectiveCall.InvokeRequest}
    (invoked : ObjectiveCall.Invocation config snapshot height request)
    (silent : invoked.journal.outbox = [])
    (noCancel : ∀ control ∈ invoked.journal.controls, control.kind ≠ .cancel) :
    invoked.mail.inboxes = [] ∧ ∀ closed ∈ invoked.mail.closed, closed.decided = none := by
  have sent := invoked.sentExact
  rw [silent] at sent
  have same : (Except.ok ObjectiveCall.Mail.empty : Except ObjectiveCall.CallRefusal (ObjectiveCall.Mail config snapshot)) =
      Except.ok invoked.sent :=
    (show ObjectiveCall.postMail config snapshot request.postage request.account ObjectiveCall.Mail.empty [] =
      .ok ObjectiveCall.Mail.empty from rfl).symm.trans sent
  have empty := Except.ok.inj same
  obtain ⟨inboxes, closed⟩ := ObjectiveSend.postControls_stops height _ _ _ invoked.mailExact noCancel
    (by rw [← empty]; intro _ member; cases member)
  exact ⟨by rw [inboxes, ← empty]; rfl, closed⟩

/-- **An invocation whose call tree neither sent nor controlled anything has no mail.**
(Restated for row F: the premise `controls = []` is new; a stop or cancel posts mail.) -/
theorem invocation_mail_nil {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height : Nat} {request : ObjectiveCall.InvokeRequest}
    (invoked : ObjectiveCall.Invocation config snapshot height request)
    (silent : invoked.journal.outbox = []) (still : invoked.journal.controls = []) : invoked.mail.posts = [] := by
  have sent := invoked.sentExact
  rw [silent] at sent
  have same : (Except.ok ObjectiveCall.Mail.empty : Except ObjectiveCall.CallRefusal (ObjectiveCall.Mail config snapshot)) =
      Except.ok invoked.sent :=
    (show ObjectiveCall.postMail config snapshot request.postage request.account ObjectiveCall.Mail.empty [] =
      .ok ObjectiveCall.Mail.empty from rfl).symm.trans sent
  rw [ObjectiveSend.Invocation.mail_of_silent invoked still, ← Except.ok.inj same]
  rfl

/-- **The mail of a turn decides a delivery slot only through a cancel**: its inboxes and
held slots (open) decide nothing, and a closed slot decides only when a cancel decided it.
(Restated for row F: the premise is new; before the controls no mail closed a slot.) -/
theorem mail_decides_nothing {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    (mail : ObjectiveCall.Mail config snapshot) (retired : ∀ closed ∈ mail.closed, closed.decided = none) :
    ∀ post ∈ mail.posts, ¬ DecidesDelivery post.bytes := by
  intro post member
  rcases List.mem_append.mp member with front | inClosed
  · rcases List.mem_append.mp front with inInbox | inSlot
    · obtain ⟨held, _, rfl⟩ := List.mem_map.mp inInbox
      exact not_decidesDelivery_image (role := .inbox) (key := Inbox.key held.now.sender held.now.target)
        (body := Inbox.encode held.now) rfl (by decide)
    · obtain ⟨held, _, rfl⟩ := List.mem_map.mp inSlot
      exact not_decidesDelivery_slot (slot := held.now) rfl
        (fun _ _ _ _ phase => by rw [held.opened] at phase; cases phase)
  · obtain ⟨closed, hm, rfl⟩ := List.mem_map.mp inClosed
    unfold ObjectiveCall.ClosedSlot.post
    rw [retired closed hm]
    exact not_decidesDelivery_of_payload_none payloadOf_retired

/-- No mail post holds an inbox but its inboxes' own. -/
theorem mail_inboxes_hold {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    (mail : ObjectiveCall.Mail config snapshot) (none_ : mail.inboxes = []) :
    ∀ post ∈ mail.posts, ¬ HoldsInbox post.bytes := by
  intro post member
  rcases List.mem_append.mp member with front | inClosed
  · rcases List.mem_append.mp front with inInbox | inSlot
    · rw [none_] at inInbox; cases inInbox
    · obtain ⟨held, _, rfl⟩ := List.mem_map.mp inSlot
      exact not_holdsInbox_image (role := .slot) (key := AnswerSlot.key held.now.name)
        (body := AnswerSlot.encode held.now) (by simp only [slotPost, postAt]) (by decide)
  · obtain ⟨closed, hm, rfl⟩ := List.mem_map.mp inClosed
    unfold ObjectiveCall.ClosedSlot.post
    cases closed.decided with
    | none => exact not_holdsInbox_of_payload_none payloadOf_retired
    | some slot => exact not_holdsInbox_image (role := .slot) rfl (by decide)

/-- **An invocation decides no delivery slot unless it cancels.** (Restated for row F: the
premise `noCancel` is new; `AdmittedTurn.CancelsMessage` is the other arm.) -/
theorem invocation_decides_nothing {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height : Nat} {request : ObjectiveCall.InvokeRequest}
    (invoked : ObjectiveCall.Invocation config snapshot height request)
    (noCancel : ∀ control ∈ invoked.journal.controls, control.kind ≠ .cancel) :
    ∀ post ∈ invoked.posts, ¬ DecidesDelivery post.bytes := by
  intro post member
  rcases invocation_posts_cases invoked post member with absent | ⟨object, state, shape⟩ | inMail
  · exact not_decidesDelivery_of_payload_none absent
  · exact not_decidesDelivery_image (role := .state) (key := stateKey object) (body := ObjectState.encodeObjectState state)
      (shape.trans rfl) (by decide)
  · have sentKeeps := (ObjectiveSend.postMail_keeps request.postage request.account _ _ _ invoked.sentExact).1
    have retired := (ObjectiveSend.postControls_stops height _ _ _ invoked.mailExact noCancel
      (by rw [sentKeeps]; intro _ member; cases member)).2
    exact mail_decides_nothing invoked.mail retired post inMail

/-- An invocation whose call tree sent nothing and cancelled nothing holds no inbox.
(Restated for row F: the premise `noCancel` is new; a cancel withdraws from an inbox.) -/
theorem invocation_silent_holds_no_inbox {rootBytes : Bytes → Digest} {config : Config}
    {snapshot : Snapshot rootBytes} {height : Nat} {request : ObjectiveCall.InvokeRequest}
    (invoked : ObjectiveCall.Invocation config snapshot height request)
    (silent : invoked.journal.outbox = [])
    (noCancel : ∀ control ∈ invoked.journal.controls, control.kind ≠ .cancel) :
    ∀ post ∈ invoked.posts, ¬ HoldsInbox post.bytes := by
  intro post member
  rcases invocation_posts_cases invoked post member with absent | ⟨object, state, shape⟩ | inMail
  · exact not_holdsInbox_of_payload_none absent
  · exact not_holdsInbox_image (role := .state) (key := stateKey object) (body := ObjectState.encodeObjectState state)
      (shape.trans rfl) (by decide)
  · exact mail_inboxes_hold invoked.mail (invocation_mail_silent invoked silent noCancel).1 post inMail

/-- **The turns that may write an inbox.** An invocation whose call tree sent a
message (its mail is then non-empty) or cancelled one (withdrawing it from its inbox),
and a message delivery (which forwards the sends queued on the slot it decides). Every
constructor is listed: a new turn constructor must say here whether it may write an inbox. -/
def AdmittedTurn.Sends {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height : Nat} : AdmittedTurn config snapshot height → Prop
  | .publish _ _ => False
  | .create _ _ => False
  | .birth _ _ _ => False
  | .resolve _ _ => False
  | .deliver _ _ => False
  | .topUp _ _ => False
  | .exhaust _ _ => False
  | .abandon _ _ => False
  | .invoke _ invoked => invoked.journal.outbox ≠ [] ∨ ∃ control ∈ invoked.journal.controls, control.kind = .cancel
  | .deliverMessage _ _ => True
  | .adopt _ _ => False
  | .migrate _ _ => False
  | .abortDrained _ _ => False
  | .rebirth _ _ => False
  | .registerDomain _ _ => False

/-- **The turn that may decide a delivery slot**: `deliverMessage`, and no other.
Every constructor is listed. -/
def AdmittedTurn.DeliversMessage {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height : Nat} : AdmittedTurn config snapshot height → Prop
  | .publish _ _ => False
  | .create _ _ => False
  | .birth _ _ _ => False
  | .resolve _ _ => False
  | .deliver _ _ => False
  | .topUp _ _ => False
  | .exhaust _ _ => False
  | .abandon _ _ => False
  | .invoke _ _ => False
  | .deliverMessage _ _ => True
  | .adopt _ _ => False
  | .migrate _ _ => False
  | .abortDrained _ _ => False
  | .rebirth _ _ => False
  | .registerDomain _ _ => False

/-- **The turn that may CANCEL a message**, deciding its delivery slot `cancelled`: an
invocation whose call tree yielded a `cancel` (row F). Every constructor is listed. -/
def AdmittedTurn.CancelsMessage {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height : Nat} : AdmittedTurn config snapshot height → Prop
  | .publish _ _ => False
  | .create _ _ => False
  | .birth _ _ _ => False
  | .resolve _ _ => False
  | .deliver _ _ => False
  | .topUp _ _ => False
  | .exhaust _ _ => False
  | .abandon _ _ => False
  | .invoke _ invoked => ∃ control ∈ invoked.journal.controls, control.kind = .cancel
  | .deliverMessage _ _ => False
  | .adopt _ _ => False
  | .migrate _ _ => False
  | .abortDrained _ _ => False
  | .rebirth _ _ => False
  | .registerDomain _ _ => False

/-- Every turn but the sending ones posts no inbox: by cases over the whole sum. -/
theorem AdmittedTurn.posts_hold_no_inbox {rootBytes : Bytes → Digest} {config : Config}
    {snapshot : Snapshot rootBytes} {height : Nat} (turn : AdmittedTurn config snapshot height)
    (silent : ¬ AdmittedTurn.Sends turn) : ∀ post ∈ turn.posts, ¬ HoldsInbox post.bytes := by
  cases turn with
  | publish _ publication => exact fun post member => (publication_quiet publication post member).1
  | create _ created => exact fun post member => (creation_quiet created post member).1
  | birth _ _ born => exact fun post member => (birth_quiet born post member).1
  | resolve _ resolution => exact fun post member => (resolution_quiet resolution post member).1
  | deliver _ delivery => exact fun post member => (delivery_quiet delivery post member).1
  | topUp _ topped =>
    intro post member
    simp only [AdmittedTurn.posts, List.mem_singleton] at member
    subst member
    exact not_holdsInbox_of_payload_none (Postings.write_payload config snapshot topped.posted)
  | exhaust _ exhausted => exact fun post member => (exhaustion_quiet exhausted post member).1
  | abandon _ abandoned => exact fun post member => (abandonment_quiet abandoned post member).1
  | invoke _ invoked =>
    exact invocation_silent_holds_no_inbox invoked (Classical.byContradiction fun sends => silent (.inl sends))
      (fun control member cancel => silent (.inr ⟨control, member, cancel⟩))
  | deliverMessage _ delivered => exact (silent trivial).elim
  | adopt _ adopted => exact fun post member => (adoption_quiet adopted post member).1
  | migrate _ migrated => exact fun post member => (migration_quiet migrated post member).1
  | abortDrained _ aborted => exact fun post member => (abort_quiet aborted post member).1
  | rebirth _ reborn => exact fun post member => (rebirth_quiet reborn post member).1
  | registerDomain _ registered => exact fun post member => (registration_quiet registered post member).1

/-- Every turn but `deliverMessage` and a cancelling invocation decides no delivery slot: by
cases over the whole sum. -/
theorem AdmittedTurn.posts_decide_no_delivery {rootBytes : Bytes → Digest} {config : Config}
    {snapshot : Snapshot rootBytes} {height : Nat} (turn : AdmittedTurn config snapshot height)
    (other : ¬ AdmittedTurn.DeliversMessage turn) (noCancel : ¬ AdmittedTurn.CancelsMessage turn) :
    ∀ post ∈ turn.posts, ¬ DecidesDelivery post.bytes := by
  cases turn with
  | publish _ publication => exact fun post member => (publication_quiet publication post member).2
  | create _ created => exact fun post member => (creation_quiet created post member).2
  | birth _ _ born => exact fun post member => (birth_quiet born post member).2
  | resolve _ resolution => exact fun post member => (resolution_quiet resolution post member).2
  | deliver _ delivery => exact fun post member => (delivery_quiet delivery post member).2
  | topUp _ topped =>
    intro post member
    simp only [AdmittedTurn.posts, List.mem_singleton] at member
    subst member
    exact not_decidesDelivery_of_payload_none (Postings.write_payload config snapshot topped.posted)
  | exhaust _ exhausted => exact fun post member => (exhaustion_quiet exhausted post member).2
  | abandon _ abandoned => exact fun post member => (abandonment_quiet abandoned post member).2
  | invoke _ invoked =>
    exact invocation_decides_nothing invoked (fun control member cancel => noCancel ⟨control, member, cancel⟩)
  | deliverMessage _ delivered => exact (other trivial).elim
  | adopt _ adopted => exact fun post member => (adoption_quiet adopted post member).2
  | migrate _ migrated => exact fun post member => (migration_quiet migrated post member).2
  | abortDrained _ aborted => exact fun post member => (abort_quiet aborted post member).2
  | rebirth _ reborn => exact fun post member => (rebirth_quiet reborn post member).2
  | registerDomain _ registered => exact fun post member => (registration_quiet registered post member).2

/-- **An ending turn's final posts are as quiet as its own** (a Book post or a seat
closing post holds no activity payload). -/
theorem finalize_posts_of {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height : Nat} {P : Post → Prop} (absent : ∀ post : Post, payloadOf post.bytes = none → P post)
    (turn : AdmittedTurn config snapshot height) {posts : List Post} {extra : List ReadGuard}
    (final : ActivitySeatEnd.finalize config snapshot height turn = .ok (posts, extra))
    (base : ∀ post ∈ turn.posts, P post) : ∀ post ∈ posts, P post := by
  unfold ActivitySeatEnd.finalize at final
  cases ending : ActivitySeatEnd.AdmittedTurn.ending turn with
  | none =>
    rw [ending] at final
    simp only [Except.ok.injEq, Prod.mk.injEq] at final
    rw [← final.1]; exact base
  | some found =>
    obtain ⟨record, pre, posted⟩ := found
    rw [ending] at final
    cases joined : ActivitySeatEnd.join config snapshot height record posted with
    | error reason => simp [joined] at final
    | ok optional =>
      cases optional with
      | none =>
        simp only [joined, Except.ok.injEq, Prod.mk.injEq] at final
        rw [← final.1]; exact base
      | some made =>
        simp only [joined, Except.ok.injEq, Prod.mk.injEq] at final
        rw [← final.1]
        intro post member
        unfold ActivitySeatEnd.Joined.rewrite at member
        rcases List.mem_append.mp member with mapped | closing
        · obtain ⟨original, inOriginal, replaced⟩ := List.mem_map.mp mapped
          by_cases isBook : original.cell = config.bookCell
          · rw [if_pos isBook] at replaced
            subst replaced
            apply absent
            simp [ActivitySeatEnd.Joined.bookPost, postAt, payloadOf_book]
          · rw [if_neg isBook] at replaced
            subst replaced
            exact base original inOriginal
        · exact absent post (made.held.inert post closing).2

/-- **Only a sending turn writes an inbox.** For every admitted turn and every
post of its final posts: if the post installs an inbox, the turn is an invocation
whose call tree sent, or a `deliverMessage`. By cases over the whole `AdmittedTurn`
sum; a new constructor breaks this proof (and `AdmittedTurn.Sends`) until it is
classified. -/
theorem AdmittedTurn.inbox_writers {rootBytes : Bytes → Digest} {config : Config}
    {snapshot : Snapshot rootBytes} {height : Nat} (turn : AdmittedTurn config snapshot height)
    {posts : List Post} {extra : List ReadGuard}
    (final : ActivitySeatEnd.finalize config snapshot height turn = .ok (posts, extra)) :
    ∀ post ∈ posts, HoldsInbox post.bytes → AdmittedTurn.Sends turn := by
  intro post member holds
  by_cases sends : AdmittedTurn.Sends turn
  · exact sends
  · have quiet := finalize_posts_of (P := fun post => ¬ HoldsInbox post.bytes)
      (fun _ absent => not_holdsInbox_of_payload_none absent) turn final
      (AdmittedTurn.posts_hold_no_inbox turn sends)
    exact absurd holds (quiet post member)

/-- **Only `deliverMessage`, or its sender's cancel, decides a delivery slot.** For every
admitted turn and every post of its final posts: if the post decides a delivery slot, the
turn is a `deliverMessage` or an invocation that cancelled a message (row F, OB-ENG
condition 1: the `CancelsMessage` disjunct is new; before the controls the conclusion was
`DeliversMessage` alone). By cases over the whole sum, as `AdmittedTurn.inbox_writers`. -/
theorem AdmittedTurn.delivery_deciders {rootBytes : Bytes → Digest} {config : Config}
    {snapshot : Snapshot rootBytes} {height : Nat} (turn : AdmittedTurn config snapshot height)
    {posts : List Post} {extra : List ReadGuard}
    (final : ActivitySeatEnd.finalize config snapshot height turn = .ok (posts, extra)) :
    ∀ post ∈ posts, DecidesDelivery post.bytes →
      AdmittedTurn.DeliversMessage turn ∨ AdmittedTurn.CancelsMessage turn := by
  intro post member decides
  by_cases delivers : AdmittedTurn.DeliversMessage turn
  · exact .inl delivers
  by_cases cancels : AdmittedTurn.CancelsMessage turn
  · exact .inr cancels
  · have quiet := finalize_posts_of (P := fun post => ¬ DecidesDelivery post.bytes)
      (fun _ absent => not_decidesDelivery_of_payload_none absent) turn final
      (AdmittedTurn.posts_decide_no_delivery turn delivers cancels)
    exact absurd decides (quiet post member)

/-- `AdmittedTurn.inbox_writers`, stated over the WRITES of the turn's final intent. -/
theorem AdmittedTurn.final_writes_inbox_writers {rootBytes : Bytes → Digest} {config : Config}
    {snapshot : Snapshot rootBytes} {height : Nat} (sealing : Seal) (turn : AdmittedTurn config snapshot height)
    {posts : List Post} {extra : List ReadGuard}
    (final : ActivitySeatEnd.finalize config snapshot height turn = .ok (posts, extra)) :
    ∀ w ∈ (ActivitySeatEnd.AdmittedTurn.finalIntent sealing posts extra turn).writes,
      HoldsInbox w.canonicalPostBytes → AdmittedTurn.Sends turn := by
  intro w member holds
  rw [finalIntent_writes sealing] at member
  obtain ⟨post, inPosts, rfl⟩ := List.mem_map.mp member
  exact AdmittedTurn.inbox_writers turn final post inPosts holds

/-- `AdmittedTurn.delivery_deciders`, stated over the WRITES of the turn's final intent. -/
theorem AdmittedTurn.final_writes_delivery_deciders {rootBytes : Bytes → Digest} {config : Config}
    {snapshot : Snapshot rootBytes} {height : Nat} (sealing : Seal) (turn : AdmittedTurn config snapshot height)
    {posts : List Post} {extra : List ReadGuard}
    (final : ActivitySeatEnd.finalize config snapshot height turn = .ok (posts, extra)) :
    ∀ w ∈ (ActivitySeatEnd.AdmittedTurn.finalIntent sealing posts extra turn).writes,
      DecidesDelivery w.canonicalPostBytes →
        AdmittedTurn.DeliversMessage turn ∨ AdmittedTurn.CancelsMessage turn := by
  intro w member decides
  rw [finalIntent_writes sealing] at member
  obtain ⟨post, inPosts, rfl⟩ := List.mem_map.mp member
  exact AdmittedTurn.delivery_deciders turn final post inPosts decides

/-- The delivery's own decided slot IS a delivery decision: the arm
`AdmittedTurn.delivery_deciders` names is not empty. -/
theorem MessageDelivery.decides_delivery_slot {rootBytes : Bytes → Digest} {config : Config}
    {snapshot : Snapshot rootBytes} {height : Nat} {request : ObjectiveSend.MessageRequest}
    (delivered : ObjectiveSend.MessageDelivery config snapshot height request) :
    DecidesDelivery (slotPost config snapshot delivered.decided).bytes := by
  obtain ⟨_, role, _, _, decided⟩ := delivered.decides_own_slot
  exact decidesDelivery_decided_slot (slot := delivered.decided) (message := delivered.message.id)
    (decision := delivered.outcome.decision) (at_ := height)
    ((congrArg AnswerSlot.Slot.decider decided).trans role) ((congrArg AnswerSlot.Slot.phase decided).trans rfl)

/-! ## Reachable worlds -/

/-- One committed step of a world: an admitted kernel activity turn (its final,
possibly seat-closing, intent), an intent whose posts the seat kernel checked
inert, or an intent the ordinary gate admits; each under any schedule and (for a
turn) any sealing. -/
inductive Step {rootBytes : Bytes → Digest} (config : Config) : Snapshot rootBytes → Snapshot rootBytes → Prop
  | turn {snapshot : Snapshot rootBytes} {height : Nat} (turn : AdmittedTurn config snapshot height)
      (sealing : Seal) (posts : List Post) (extra : List ReadGuard)
      (final : ActivitySeatEnd.finish config snapshot height turn = .ok (posts, extra))
      (schedule : DurableCommitProtocol.Schedule) :
      Step config snapshot ((execute schedule snapshot
        (ActivitySeatEnd.AdmittedTurn.finalIntent sealing posts extra turn)).storeAfter snapshot)
  | inert {snapshot : Snapshot rootBytes} (intent : DataIntent rootBytes) (posts : List Post)
      (writes : intent.writes = posts.map (Post.write rootBytes)) (inert : SeatStore.Inert snapshot posts)
      (schedule : DurableCommitProtocol.Schedule) :
      Step config snapshot ((execute schedule snapshot intent).storeAfter snapshot)
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
  | turn turn sealing posts extra final schedule =>
    obtain ⟨_, _, final, _, _⟩ := ActivitySeatEnd.finish_finalize final
    exact execute_preserves typed (finalIntent_writes sealing) (finalize_safe typed turn final) schedule
  | inert intent posts writes inert schedule => exact execute_preserves typed writes (inert_safe inert) schedule
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

/-- **What a delivery on a reachable world stores resumes as the program's own yield**, with
no premise left: `delivery_stored_complete`'s `prior` is the invariant. -/
theorem reachable_delivery_stored_complete {rootBytes : Bytes → Digest} {config : Config}
    {genesis snapshot : Snapshot rootBytes} (genesisTyped : RecordCellsTyped config genesis)
    (reachable : Reachable config genesis snapshot) {height : Nat} {request : DeliverRequest}
    (delivery : Delivery config snapshot height request)
    {state : State} {plan : PlanAwait} (yieldedSegment : delivery.segment = .yielded state plan) :
    StoredComplete config delivery.envelope.sourceTicks delivery.resumed state :=
  delivery_stored_complete delivery
    (Delivery.prior delivery (stored_checkpoints_typed genesisTyped reachable request.record delivery.record
      delivery.recordExact delivery.located)) yieldedSegment

#assert_axioms reachable_delivery_stored_complete
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
#assert_axioms readObject_package
#assert_axioms countPosts_safe
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
#assert_axioms invocation_safe
#assert_axioms adoption_safe
#assert_axioms migration_safe
#assert_axioms abort_safe
#assert_axioms rebirth_safe
#assert_axioms AdmittedTurn.safe
#assert_axioms finalIntent_writes
#assert_axioms finalize_safe
#assert_axioms inert_safe
#assert_axioms foreign_preserves
#assert_axioms Step.preserves
#assert_axioms stored_checkpoints_typed
#assert_axioms reachable_delivery_typed
#assert_axioms holdsInbox_inboxImage
#assert_axioms decidesDelivery_decided_slot
#assert_axioms not_holdsInbox_of_payload_none
#assert_axioms not_holdsInbox_image
#assert_axioms not_decidesDelivery_of_payload_none
#assert_axioms not_decidesDelivery_image
#assert_axioms not_decidesDelivery_slot
#assert_axioms quiet_of_payload_none
#assert_axioms quiet_image
#assert_axioms quiet_recordPost
#assert_axioms yielded_posts_quiet
#assert_axioms birth_quiet
#assert_axioms delivery_quiet
#assert_axioms exhaustion_quiet
#assert_axioms abandonSlot_quiet
#assert_axioms abandonment_quiet
#assert_axioms resolution_quiet
#assert_axioms publication_quiet
#assert_axioms creation_quiet
#assert_axioms adoption_quiet
#assert_axioms migration_quiet
#assert_axioms abort_quiet
#assert_axioms rebirth_quiet
#assert_axioms invocation_posts_cases
#assert_axioms invocation_mail_nil
#assert_axioms invocation_mail_silent
#assert_axioms mail_inboxes_hold
#assert_axioms mail_decides_nothing
#assert_axioms invocation_decides_nothing
#assert_axioms invocation_silent_holds_no_inbox
#assert_axioms AdmittedTurn.posts_hold_no_inbox
#assert_axioms AdmittedTurn.posts_decide_no_delivery
#assert_axioms finalize_posts_of
#assert_axioms AdmittedTurn.inbox_writers
#assert_axioms AdmittedTurn.delivery_deciders
#assert_axioms AdmittedTurn.final_writes_inbox_writers
#assert_axioms AdmittedTurn.final_writes_delivery_deciders
#assert_axioms MessageDelivery.decides_delivery_slot
end Minidregg.Kernel.ObjectiveCheckpointInvariant
