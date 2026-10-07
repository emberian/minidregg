/- The upgrade's two invariants over every reachable world (`ObjectiveCheckpointInvariant.Reachable`):

* **`live_counts`**: every object record's counters (`ObjectRecord.count`, by class `classOf`)
  equal the number of awaiting activity records of that object, at their own coordinates, in that
  class. So MIGRATE's `live = 0` means no old activity outside the rebirth set awaits (brief trap 4).
* **`migrate_cannot_fail`**: on a draining object, the declared state passes the drained
  judgment (`judgeMigrated`: migrated, it is admitted by the record MIGRATE will install), in
  every reachable world: the ADOPT established it for the state it found (`Adoption.migratable`),
  and every turn that writes the state of a draining object re-establishes it (a delivery and a
  birth by `judgeDrained`, a call tree and a delivered message by `Journal.drained`). Hence, with
  no old activity left and the fee payable, MIGRATE is admitted (brief §2, theorem 6).

Both are stated over the PAYLOADS of protected cells (`views`), which is all the kernel reads of
records, object records, states and packages; so an intent the ordinary gate admits, a seat
turn's inert posts and a seat closing's posts leave them as they are.

Hypotheses, by name:
* `BookUnprotected`: the deployment's Book cell is not a protected coordinate (a seat closing
  rewrites the Book post; no protected cell is the Book). Decidable of the configuration.
* the genesis holds no activity records and no object records (`GenesisClean`).
No coordinate-hash injectivity is assumed: a state or object record is read only as its own
object's (`stateFor`, `objectFor` check the payload key), and every count is per object. -/
import Kernel.ObjectiveCheckpointInvariant

namespace Minidregg.Kernel.ObjectiveUpgradeInvariant
open Minidregg.Theory Minidregg.Compiler
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Theory.TypedAuthorization (Digest SubjectId)
open Minidregg.Kernel.DurableDataIntent
open Minidregg.Kernel.ObjectiveActivityWire
open Minidregg.Kernel.ObjectiveActivity
open Minidregg.Kernel.ObjectiveCheckpointInvariant
open Minidregg.Kernel.ObjectRecord (ObjectRecord Pending LiveClass admitWrite)
open Minidregg.Theory.ObjectiveBendDemandData (Data)
set_option autoImplicit false

abbrev Payload := ObjectiveActivityCell.Payload
abbrev Payloads := CellId → Option Payload

/-- The activity payloads a byte map holds. -/
def payloads (bytesAt : CellId → Bytes) : Payloads := fun cell => payloadOf (bytesAt cell)

/-! ## Views -/

def recordView (payload : Option Payload) : Option Record :=
  match payload with
  | some p => if p.role = .record then decodeRecord p.body else none
  | none => none

/-- The awaiting activity record a cell holds at its own coordinate. -/
def awaitingView (config : Config) (P : Payloads) (cell : CellId) : Option Record :=
  match recordView (P cell) with
  | some record =>
    if cell = recordCell config.domain record.object record.activity ∧ record.phase.awaits = true then some record
    else none
  | none => none

/-- The object record of `object` its cell holds (key-checked, as `readObject`). -/
def objectView (object : CellId) (payload : Option Payload) : Option ObjectRecord :=
  match payload with
  | some p => if p.role = .object ∧ p.key = objectKey object then ObjectRecord.decodeRecord p.body else none
  | none => none

/-- The declared state of `object` its cell holds (key-checked, as `readState`). -/
def stateView (object : CellId) (payload : Option Payload) : Option ObjectState :=
  match payload with
  | some p => if p.role = .state ∧ p.key = stateKey object then ObjectState.decodeObjectState p.body else none
  | none => none

/-- The package body a cell holds (`[]` when none, as `packageBytes`). -/
def packageView (payload : Option Payload) : Bytes :=
  match payload with
  | some p => if p.role = .package then p.body else []
  | none => []

theorem readObject_some {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {object : CellId} {record : ObjectRecord} (read : readObject config snapshot object = .ok (some record)) :
    objectView object (payloads snapshot.canonicalBytes (objectCell config.domain object)) = some record := by
  unfold readObject objectFor at read
  unfold objectView payloads
  cases present : payloadOf (snapshot.canonicalBytes (objectCell config.domain object)) with
  | none => rw [present] at read; cases read
  | some payload =>
    rw [present] at read
    simp only at read ⊢
    split at read
    · rename_i owned
      rw [if_pos owned]
      split at read
      · rename_i found decoded; cases read; exact decoded
      · cases read
    · cases read

theorem readObject_none {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {object : CellId} (read : readObject config snapshot object = .ok none) :
    payloads snapshot.canonicalBytes (objectCell config.domain object) = none :=
  readObject_none_payload read

theorem objectView_readObject {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {object : CellId} {record : ObjectRecord}
    (view : objectView object (payloads snapshot.canonicalBytes (objectCell config.domain object)) = some record) :
    readObject config snapshot object = .ok (some record) := by
  unfold objectView payloads at view
  unfold readObject objectFor
  cases present : payloadOf (snapshot.canonicalBytes (objectCell config.domain object)) with
  | none => rw [present] at view; cases view
  | some payload =>
    rw [present] at view
    simp only at view ⊢
    split at view
    · rename_i owned
      rw [if_pos owned, view]
    · cases view

theorem readState_some {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {object : CellId} {state : ObjectState} (read : readState config snapshot object = .ok (some state)) :
    stateView object (payloads snapshot.canonicalBytes (stateCell config.domain object)) = some state := by
  unfold readState stateFor at read
  unfold stateView payloads
  cases present : payloadOf (snapshot.canonicalBytes (stateCell config.domain object)) with
  | none => rw [present] at read; cases read
  | some payload =>
    rw [present] at read
    simp only at read ⊢
    split at read
    · rename_i owned
      rw [if_pos owned]
      split at read
      · rename_i found decoded; cases read; exact decoded
      · cases read
    · cases read

theorem stateView_readState {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {object : CellId} {state : ObjectState}
    (view : stateView object (payloads snapshot.canonicalBytes (stateCell config.domain object)) = some state) :
    readState config snapshot object = .ok (some state) := by
  unfold stateView payloads at view
  unfold readState stateFor
  cases present : payloadOf (snapshot.canonicalBytes (stateCell config.domain object)) with
  | none => rw [present] at view; cases view
  | some payload =>
    rw [present] at view
    simp only at view ⊢
    split at view
    · rename_i owned
      rw [if_pos owned, view]
    · cases view

theorem packageBytes_view {rootBytes : Bytes → Digest} (config : Config) (snapshot : Snapshot rootBytes) (pin : Digest) :
    packageBytes config snapshot pin = packageView (payloads snapshot.canonicalBytes (packageCell config.domain pin)) := by
  unfold packageBytes packageView payloads bodyOf
  cases payloadOf (snapshot.canonicalBytes (packageCell config.domain pin)) with
  | none => rfl
  | some p => by_cases role : p.role = .package <;> simp [role]

/-! ## The invariants -/

/-- Whether a cell holds an awaiting activity of `object` in class `c` under `record`. -/
def counts (config : Config) (P : Payloads) (object : CellId) (record : ObjectRecord) (c : LiveClass)
    (cell : CellId) : Bool :=
  match awaitingView config P cell with
  | some activity => decide (activity.object = object) && decide (record.classOf activity.pin activity.activity = c)
  | none => false

/-- **The census**: a duplicate-free list of cells holding every awaiting activity record; each
awaiting activity's object has a record; each object record's counters count its awaiting
activities, class by class. -/
structure Census (config : Config) (P : Payloads) (cells : List CellId) : Prop where
  nodup : cells.Nodup
  covers : ∀ cell activity, awaitingView config P cell = some activity → cell ∈ cells
  homed : ∀ cell activity, awaitingView config P cell = some activity →
    ∃ record, objectView activity.object (P (objectCell config.domain activity.object)) = some record
  counted : ∀ object record, objectView object (P (objectCell config.domain object)) = some record →
    ∀ c, record.count c = cells.countP (counts config P object record c)

def LiveCounts (config : Config) (P : Payloads) : Prop := ∃ cells, Census config P cells

/-- A state migrates and the record MIGRATE would install admits it. -/
def Migratable (config : Config) (package : Bytes) (record : ObjectRecord) (object : CellId) (next : Pending)
    (value : Data) : Prop :=
  ∃ migrated, migrateValue config package next value = .ok migrated ∧
    admitWrite (record.successor next) (ObjectRecord.migrateFacts object.value next) (some migrated) migrated = .ok ()

/-- **Every draining object's state is migratable.** -/
def MigratableStates (config : Config) (P : Payloads) : Prop :=
  ∀ object record next deadline state,
    objectView object (P (objectCell config.domain object)) = some record →
    record.phase = .draining next deadline →
    stateView object (P (stateCell config.domain object)) = some state →
    Migratable config (packageView (P (packageCell config.domain next.pin))) record object next state.value

/-- Both. -/
def Upgradable (config : Config) (P : Payloads) : Prop := LiveCounts config P ∧ MigratableStates config P

theorem judgeMigrated_iff {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {record : ObjectRecord} {object : CellId} {next : Pending} {value : Data} :
    (∃ migrated, judgeMigrated config snapshot record object next value = .ok migrated) ↔
      Migratable config (packageBytes config snapshot next.pin) record object next value := by
  constructor
  · rintro ⟨migrated, judged⟩
    obtain ⟨ran, admitted⟩ := judgeMigrated_ok judged
    exact ⟨migrated, ran, admitted⟩
  · rintro ⟨migrated, ran, admitted⟩
    exact ⟨migrated, by simp [judgeMigrated, ran, admitted]⟩

/-- The next record's judgment reads only the pending upgrade. -/
theorem successor_admits (record other : ObjectRecord) (next : Pending) (facts : ObjectRecord.Facts)
    (old : Option Data) (new : Data) :
    admitWrite (record.successor next) facts old new = admitWrite (other.successor next) facts old new := rfl

theorem migrateValue_live (config : Config) (package : Bytes) (next : Pending) (live : Nat) (value : Data) :
    migrateValue config package { next with live := live } value = migrateValue config package next value := by
  unfold migrateValue
  cases next.migration with
  | none => rfl
  | some name => dsimp only; cases loadMigration config package next.pin name <;> rfl

/-- `Migratable` reads the record only through the pending upgrade, and not its counter. -/
theorem migratable_record (config : Config) (package : Bytes) (record other : ObjectRecord) (object : CellId)
    (next : Pending) (live : Nat) (value : Data)
    (holds : Migratable config package record object next value) :
    Migratable config package other object { next with live := live } value := by
  obtain ⟨migrated, ran, admitted⟩ := holds
  refine ⟨migrated, ?_, ?_⟩
  · rw [migrateValue_live]; exact ran
  · exact admitted

/-! ## Agreement at protected cells -/

abbrev Protected := ObjectiveActivityGate.Protected

def Agree (P Q : Payloads) : Prop := ∀ cell, Protected cell → P cell = Q cell

theorem recordCell_protected (config : Config) (object : CellId) (activity : Digest) :
    Protected (recordCell config.domain object activity) := ObjectiveActivityCell.coordinate_reserved _ _ _
theorem objectCell_protected (config : Config) (object : CellId) : Protected (objectCell config.domain object) :=
  ObjectiveActivityCell.coordinate_reserved _ _ _
theorem stateCell_protected (config : Config) (object : CellId) : Protected (stateCell config.domain object) :=
  ObjectiveActivityCell.coordinate_reserved _ _ _
theorem packageCell_protected (config : Config) (pin : Digest) : Protected (packageCell config.domain pin) :=
  ObjectiveActivityCell.coordinate_reserved _ _ _

theorem awaiting_protected {config : Config} {P : Payloads} {cell : CellId} {record : Record}
    (found : awaitingView config P cell = some record) : Protected cell := by
  unfold awaitingView at found
  split at found
  · rename_i record' _
    split at found
    · rename_i at_
      rw [at_.1]; exact recordCell_protected config _ _
    · cases found
  · cases found

theorem awaiting_agree {config : Config} {P Q : Payloads} (agree : Agree P Q) (cell : CellId) :
    awaitingView config P cell = awaitingView config Q cell := by
  by_cases guarded : Protected cell
  · unfold awaitingView; rw [agree cell guarded]
  · cases hp : awaitingView config P cell with
    | some record => exact absurd (awaiting_protected hp) guarded
    | none =>
      cases hq : awaitingView config Q cell with
      | some record => exact absurd (awaiting_protected hq) guarded
      | none => rfl

theorem counts_agree {config : Config} {P Q : Payloads} (agree : Agree P Q) (object : CellId)
    (record : ObjectRecord) (c : LiveClass) : counts config P object record c = counts config Q object record c := by
  funext cell
  unfold counts
  rw [awaiting_agree agree cell]

theorem census_transfer {config : Config} {P Q : Payloads} {cells : List CellId} (agree : Agree P Q)
    (census : Census config P cells) : Census config Q cells where
  nodup := census.nodup
  covers := fun cell activity found => census.covers cell activity (by rw [awaiting_agree agree]; exact found)
  homed := fun cell activity found => by
    obtain ⟨record, held⟩ := census.homed cell activity (by rw [awaiting_agree agree]; exact found)
    exact ⟨record, by rw [← agree _ (objectCell_protected config _)]; exact held⟩
  counted := fun object record held c => by
    rw [← counts_agree agree]
    exact census.counted object record (by rw [agree _ (objectCell_protected config _)]; exact held) c

theorem migratable_transfer {config : Config} {P Q : Payloads} (agree : Agree P Q)
    (states : MigratableStates config P) : MigratableStates config Q := by
  intro object record next deadline state held draining stated
  rw [← agree _ (packageCell_protected config _)]
  exact states object record next deadline state (by rw [agree _ (objectCell_protected config _)]; exact held)
    draining (by rw [agree _ (stateCell_protected config _)]; exact stated)

theorem upgradable_transfer {config : Config} {P Q : Payloads} (agree : Agree P Q)
    (holds : Upgradable config P) : Upgradable config Q :=
  ⟨let ⟨cells, census⟩ := holds.1; ⟨cells, census_transfer agree census⟩, migratable_transfer agree holds.2⟩

/-! ## Installing posts -/

/-- The payloads after an intent whose writes are a list of posts installs. -/
theorem install_payloads {rootBytes : Bytes → Digest} (snapshot : Snapshot rootBytes) {intent : DataIntent rootBytes}
    {posts : List Post} (writes : intent.writes = posts.map (Post.write rootBytes)) :
    payloads (DataSnapshot.install snapshot intent).canonicalBytes = payloads (afterPosts snapshot posts) := by
  funext cell
  unfold payloads
  rw [DataSnapshot.install_canonicalBytes, writes, ObjectiveActivity.lookupPostBytes_posts]
  rfl

/-- A seat turn's inert posts change no payload. -/
theorem inert_agree {rootBytes : Bytes → Digest} {snapshot : Snapshot rootBytes} {posts : List Post}
    (inert : SeatStore.Inert snapshot posts) :
    payloads (afterPosts snapshot posts) = payloads snapshot.canonicalBytes := by
  funext cell
  unfold payloads afterPosts
  cases found : posts.find? (fun post => post.cell = cell) with
  | none => rfl
  | some post =>
    have member := List.mem_of_find?_eq_some found
    have at_ : post.cell = cell := by simpa using List.find?_some found
    simp only [Option.map_some, Option.getD_some]
    rw [(inert post member).2, ← at_, (inert post member).1]

/-- The Book is not a protected coordinate. -/
def BookUnprotected (config : Config) : Prop := ¬ Protected config.bookCell

/-- **A seat closing changes no protected payload a turn's own posts set**: the final posts
agree with the turn's own at every protected cell. -/
theorem finalize_agree {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height : Nat} (book : BookUnprotected config) (turn : AdmittedTurn config snapshot height)
    {posts : List Post} {extra : List ReadGuard}
    (final : ActivitySeatEnd.finalize config snapshot height turn = .ok (posts, extra)) :
    Agree (payloads (afterPosts snapshot posts)) (payloads (afterPosts snapshot turn.posts)) := by
  intro cell guarded
  have notBook : cell ≠ config.bookCell := fun same => book (same ▸ guarded)
  unfold ActivitySeatEnd.finalize at final
  cases ending : ActivitySeatEnd.AdmittedTurn.ending turn with
  | none =>
    rw [ending] at final
    simp only [Except.ok.injEq, Prod.mk.injEq] at final
    rw [← final.1]
  | some found =>
    obtain ⟨record, pre, posted⟩ := found
    rw [ending] at final
    cases joined : ActivitySeatEnd.join config snapshot height record posted with
    | error reason => simp [joined] at final
    | ok optional =>
      cases optional with
      | none =>
        simp only [joined, Except.ok.injEq, Prod.mk.injEq] at final
        rw [← final.1]
      | some made =>
        simp only [joined, Except.ok.injEq, Prod.mk.injEq] at final
        rw [← final.1]
        unfold payloads afterPosts ActivitySeatEnd.Joined.rewrite
        rw [List.find?_append, List.find?_map]
        have keep : ((fun post : Post => decide (post.cell = cell)) ∘
            fun post => if post.cell = config.bookCell then made.bookPost else post) =
            fun post : Post => decide (post.cell = cell) := by
          funext post
          simp only [Function.comp]
          split
          · rename_i isBook
            show decide (made.bookPost.cell = cell) = decide (post.cell = cell)
            rw [isBook]
            rfl
          · rfl
        rw [keep]
        cases first : turn.posts.find? (fun post => decide (post.cell = cell)) with
        | some post =>
          have at_ : post.cell = cell := by simpa using List.find?_some first
          have notAt : post.cell ≠ config.bookCell := at_ ▸ notBook
          simp [notAt]
        | none =>
          simp only [Option.map_none, Option.none_or, Option.getD_none]
          cases held : made.held.posts.find? (fun post => decide (post.cell = cell)) with
          | none => rfl
          | some post =>
            have member := List.mem_of_find?_eq_some held
            have at_ : post.cell = cell := by simpa using List.find?_some held
            have inert := made.held.inert post member
            simp only [Option.map_some, Option.getD_some]
            rw [inert.2, ← at_, inert.1]

#assert_axioms readObject_some
#assert_axioms objectView_readObject
#assert_axioms readState_some
#assert_axioms stateView_readState
#assert_axioms packageBytes_view
#assert_axioms judgeMigrated_iff
#assert_axioms successor_admits
#assert_axioms migrateValue_live
#assert_axioms migratable_record
#assert_axioms awaiting_agree
#assert_axioms census_transfer
#assert_axioms migratable_transfer
#assert_axioms install_payloads
#assert_axioms inert_agree
#assert_axioms finalize_agree

/-! ## Kinded posts: a post changes only the views of its own role -/

/-- A payload is absent or of `role`. -/
def OfRole (role : ObjectiveActivityCell.Role) (payload : Option Payload) : Prop :=
  ∀ p, payload = some p → p.role = role

/-- A post is KINDED `role`: its cell held nothing or a `role` payload, and it writes nothing or one. -/
def Kinded {rootBytes : Bytes → Digest} (snapshot : Snapshot rootBytes) (role : ObjectiveActivityCell.Role)
    (post : Post) : Prop :=
  OfRole role (payloadOf (snapshot.canonicalBytes post.cell)) ∧ OfRole role (payloadOf post.bytes)

theorem recordView_of_role {role : ObjectiveActivityCell.Role} {payload : Option Payload} (other : role ≠ .record)
    (of : OfRole role payload) : recordView payload = none := by
  cases payload with
  | none => rfl
  | some p => simp [recordView, of p rfl, other]

theorem objectView_of_role {role : ObjectiveActivityCell.Role} {payload : Option Payload} (other : role ≠ .object)
    (of : OfRole role payload) (object : CellId) : objectView object payload = none := by
  cases payload with
  | none => rfl
  | some p => simp [objectView, of p rfl, other]

theorem stateView_of_role {role : ObjectiveActivityCell.Role} {payload : Option Payload} (other : role ≠ .state)
    (of : OfRole role payload) (object : CellId) : stateView object payload = none := by
  cases payload with
  | none => rfl
  | some p => simp [stateView, of p rfl, other]

theorem packageView_of_role {role : ObjectiveActivityCell.Role} {payload : Option Payload} (other : role ≠ .package)
    (of : OfRole role payload) : packageView payload = [] := by
  cases payload with
  | none => rfl
  | some p => simp [packageView, of p rfl, other]

theorem awaitingView_of_recordView {config : Config} {P : Payloads} {cell : CellId}
    (none_ : recordView (P cell) = none) : awaitingView config P cell = none := by
  simp [awaitingView, none_]

/-- After posts, a cell holds what its first post writes, or what it held. -/
theorem payloads_after {rootBytes : Bytes → Digest} (snapshot : Snapshot rootBytes) (posts : List Post)
    (cell : CellId) :
    (payloads (afterPosts snapshot posts) cell = payloads snapshot.canonicalBytes cell ∧ ∀ p ∈ posts, p.cell ≠ cell) ∨
      ∃ p ∈ posts, p.cell = cell ∧ payloads (afterPosts snapshot posts) cell = payloadOf p.bytes := by
  unfold payloads afterPosts
  cases found : posts.find? (fun post => decide (post.cell = cell)) with
  | none =>
    left
    refine ⟨rfl, fun p member same => ?_⟩
    have := List.find?_eq_none.mp found p member
    simp [same] at this
  | some p =>
    right
    exact ⟨p, List.mem_of_find?_eq_some found, by simpa using List.find?_some found, rfl⟩

/-- A cell whose posts are all kinded `role` changes no view of another role. -/
theorem awaiting_after_kinded {rootBytes : Bytes → Digest} (config : Config) (snapshot : Snapshot rootBytes)
    (posts : List Post) (cell : CellId)
    (kinded : ∀ p ∈ posts, p.cell = cell → ∃ role, role ≠ .record ∧ Kinded snapshot role p) :
    awaitingView config (payloads (afterPosts snapshot posts)) cell =
      awaitingView config (payloads snapshot.canonicalBytes) cell := by
  rcases payloads_after snapshot posts cell with ⟨same, _⟩ | ⟨p, member, at_, after⟩
  · unfold awaitingView; rw [same]
  · obtain ⟨role, other, pre, post⟩ := kinded p member at_
    rw [awaitingView_of_recordView (by rw [after]; exact recordView_of_role other post),
      awaitingView_of_recordView (by unfold payloads; rw [← at_]; exact recordView_of_role other pre)]

theorem objectView_after_kinded {rootBytes : Bytes → Digest} (snapshot : Snapshot rootBytes)
    (posts : List Post) (object cell : CellId)
    (kinded : ∀ p ∈ posts, p.cell = cell → ∃ role, role ≠ .object ∧ Kinded snapshot role p) :
    objectView object (payloads (afterPosts snapshot posts) cell) =
      objectView object (payloads snapshot.canonicalBytes cell) := by
  rcases payloads_after snapshot posts cell with ⟨same, _⟩ | ⟨p, member, at_, after⟩
  · rw [same]
  · obtain ⟨role, other, pre, post⟩ := kinded p member at_
    rw [after, objectView_of_role other post, show payloads snapshot.canonicalBytes cell =
      payloadOf (snapshot.canonicalBytes p.cell) by rw [at_]; rfl, objectView_of_role other pre]

theorem stateView_after_kinded {rootBytes : Bytes → Digest} (snapshot : Snapshot rootBytes)
    (posts : List Post) (object cell : CellId)
    (kinded : ∀ p ∈ posts, p.cell = cell → ∃ role, role ≠ .state ∧ Kinded snapshot role p) :
    stateView object (payloads (afterPosts snapshot posts) cell) =
      stateView object (payloads snapshot.canonicalBytes cell) := by
  rcases payloads_after snapshot posts cell with ⟨same, _⟩ | ⟨p, member, at_, after⟩
  · rw [same]
  · obtain ⟨role, other, pre, post⟩ := kinded p member at_
    rw [after, stateView_of_role other post, show payloads snapshot.canonicalBytes cell =
      payloadOf (snapshot.canonicalBytes p.cell) by rw [at_]; rfl, stateView_of_role other pre]

theorem packageView_after_kinded {rootBytes : Bytes → Digest} (snapshot : Snapshot rootBytes)
    (posts : List Post) (cell : CellId)
    (kinded : ∀ p ∈ posts, p.cell = cell → ∃ role, role ≠ .package ∧ Kinded snapshot role p) :
    packageView (payloads (afterPosts snapshot posts) cell) = packageView (payloads snapshot.canonicalBytes cell) := by
  rcases payloads_after snapshot posts cell with ⟨same, _⟩ | ⟨p, member, at_, after⟩
  · rw [same]
  · obtain ⟨role, other, pre, post⟩ := kinded p member at_
    rw [after, packageView_of_role other post, show payloads snapshot.canonicalBytes cell =
      payloadOf (snapshot.canonicalBytes p.cell) by rw [at_]; rfl, packageView_of_role other pre]

/-- A kinded post does not land on a cell holding a payload of another role. -/
theorem kinded_cell_ne {rootBytes : Bytes → Digest} {snapshot : Snapshot rootBytes} {role : ObjectiveActivityCell.Role}
    {post : Post} (kinded : Kinded snapshot role post) {cell : CellId} {p : Payload}
    (held : payloadOf (snapshot.canonicalBytes cell) = some p) (other : p.role ≠ role) : post.cell ≠ cell := by
  intro same
  rw [← same] at held
  exact other (kinded.1 p held)

/-! ## Counting -/

theorem countP_congr_mem {l : List CellId} {f g : CellId → Bool} (same : ∀ x ∈ l, f x = g x) :
    l.countP f = l.countP g := by
  induction l with
  | nil => rfl
  | cons x rest ih =>
    simp only [List.countP_cons]
    rw [same x (List.mem_cons_self ..), ih (fun y member => same y (List.mem_cons_of_mem _ member))]

/-- Changing a predicate at one element of a duplicate-free list. -/
theorem countP_change_one {l : List CellId} (nodup : l.Nodup) {y : CellId} (member : y ∈ l) {f g : CellId → Bool}
    (agree : ∀ x ∈ l, x ≠ y → f x = g x) :
    l.countP g + (if f y then 1 else 0) = l.countP f + (if g y then 1 else 0) := by
  induction l with
  | nil => cases member
  | cons x rest ih =>
    rw [List.nodup_cons] at nodup
    have restAgree : ∀ z ∈ rest, z ≠ y → f z = g z := fun z mem ne => agree z (List.mem_cons_of_mem _ mem) ne
    simp only [List.countP_cons]
    by_cases same : x = y
    · subst same
      have countF : rest.countP f = rest.countP g := countP_congr_mem (fun z mem => restAgree z mem
        (fun h => nodup.1 (h ▸ mem)))
      rw [countF]
      cases f x <;> cases g x <;> simp <;> omega
    · have fx := agree x (List.mem_cons_self ..) same
      have inRest : y ∈ rest := (List.mem_cons.mp member).resolve_left (fun e => same e.symm)
      have step := ih nodup.2 inRest restAgree
      rw [fx]
      split <;> omega

#assert_axioms recordView_of_role
#assert_axioms objectView_of_role
#assert_axioms stateView_of_role
#assert_axioms packageView_of_role
#assert_axioms payloads_after
#assert_axioms awaiting_after_kinded
#assert_axioms objectView_after_kinded
#assert_axioms stateView_after_kinded
#assert_axioms packageView_after_kinded
#assert_axioms kinded_cell_ne
#assert_axioms countP_congr_mem
#assert_axioms countP_change_one

/-! ## Transfer under equal views -/

theorem census_views {config : Config} {P Q : Payloads} {cells : List CellId}
    (awaiting : ∀ cell, awaitingView config Q cell = awaitingView config P cell)
    (objects : ∀ object, objectView object (Q (objectCell config.domain object)) =
      objectView object (P (objectCell config.domain object)))
    (census : Census config P cells) : Census config Q cells where
  nodup := census.nodup
  covers := fun cell activity found => census.covers cell activity (by rw [← awaiting]; exact found)
  homed := fun cell activity found => by
    obtain ⟨record, held⟩ := census.homed cell activity (by rw [← awaiting]; exact found)
    exact ⟨record, by rw [objects]; exact held⟩
  counted := fun object record held c => by
    have same : counts config Q object record c = counts config P object record c := by
      funext cell; unfold counts; rw [awaiting]
    rw [same]
    exact census.counted object record (by rw [← objects]; exact held) c

theorem migratable_views {config : Config} {P Q : Payloads}
    (objects : ∀ object, objectView object (Q (objectCell config.domain object)) =
      objectView object (P (objectCell config.domain object)))
    (states : ∀ object, stateView object (Q (stateCell config.domain object)) =
      stateView object (P (stateCell config.domain object)))
    (packages : ∀ pin, packageView (Q (packageCell config.domain pin)) = packageView (P (packageCell config.domain pin)))
    (holds : MigratableStates config P) : MigratableStates config Q := by
  intro object record next deadline state held draining stated
  rw [packages]
  exact holds object record next deadline state (by rw [← objects]; exact held) draining (by rw [← states]; exact stated)

/-- A SILENT post: of a role no invariant reads (a slot, an inbox, or nothing: the Book). -/
def Silent {rootBytes : Bytes → Digest} (snapshot : Snapshot rootBytes) (post : Post) : Prop :=
  ∃ role, role ≠ .record ∧ role ≠ .object ∧ role ≠ .state ∧ role ≠ .package ∧ Kinded snapshot role post

/-- **A turn whose posts are all quiet keeps both invariants.** -/
theorem silent_preserves {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {posts : List Post} (quiet : ∀ post ∈ posts, Silent snapshot post)
    (holds : Upgradable config (payloads snapshot.canonicalBytes)) :
    Upgradable config (payloads (afterPosts snapshot posts)) := by
  have awaiting := fun cell => awaiting_after_kinded config snapshot posts cell (fun p member _ => by
    obtain ⟨role, r, _, _, _, k⟩ := quiet p member; exact ⟨role, r, k⟩)
  have objects := fun object => objectView_after_kinded snapshot posts object (objectCell config.domain object)
    (fun p member _ => by obtain ⟨role, _, o, _, _, k⟩ := quiet p member; exact ⟨role, o, k⟩)
  have states := fun object => stateView_after_kinded snapshot posts object (stateCell config.domain object)
    (fun p member _ => by obtain ⟨role, _, _, st, _, k⟩ := quiet p member; exact ⟨role, st, k⟩)
  have packages := fun pin => packageView_after_kinded snapshot posts (packageCell config.domain pin)
    (fun p member _ => by obtain ⟨role, _, _, _, pk, k⟩ := quiet p member; exact ⟨role, pk, k⟩)
  obtain ⟨⟨cells, census⟩, migratable⟩ := holds
  exact ⟨⟨cells, census_views awaiting objects census⟩, migratable_views objects states packages migratable⟩

/-- The Book post: nothing before (a loaded Book is no activity cell), nothing after. -/
theorem book_silent {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {book : BookCell} (loaded : loadBook config snapshot = .ok book) (posted : Postings book) :
    Silent snapshot (posted.write config snapshot) := by
  refine ⟨.slot, by decide, by decide, by decide, by decide, ?_, ?_⟩
  · intro p found
    rw [show (posted.write config snapshot).cell = config.bookCell from rfl, loadBook_payload loaded] at found
    cases found
  · intro p found
    rw [Postings.write_payload] at found
    cases found

theorem payloadOf_image_role (role : ObjectiveActivityCell.Role) (key body : Bytes) :
    OfRole role (payloadOf (image role key body)) := by
  intro p found
  rw [ObjectiveActivity.payloadOf_image] at found
  cases found
  rfl

theorem readSlot_role {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {name : Digest} {slot : AnswerSlot.Slot} (read : readSlot config snapshot name = some slot) :
    OfRole .slot (payloadOf (snapshot.canonicalBytes (AnswerSlot.cell config.domain name))) := by
  intro payload found
  by_contra wrong
  have empty : bodyOf .slot (snapshot.canonicalBytes (AnswerSlot.cell config.domain name)) = none := by
    simp [bodyOf, found, wrong]
  simp [readSlot, empty] at read

theorem resolution_silent {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height : Nat} {request : ResolveRequest} (resolution : Resolution config snapshot height request) :
    ∀ post ∈ resolution.posts, Silent snapshot post := by
  rw [resolution.postsExact]
  intro post member
  simp only [List.mem_singleton] at member
  subst member
  obtain ⟨_, _, _, decided, _⟩ := AnswerSlot.decide_single_decider resolution.decidedExact
  have named : resolution.decided.name = request.slot := by rw [decided]; exact resolution.named
  refine ⟨.slot, by decide, by decide, by decide, by decide, ?_, ?_⟩
  · have pre := readSlot_role resolution.slotExact
    simp only [slotPost, postAt]
    rw [named]
    exact pre
  · simp only [slotPost, postAt]
    exact payloadOf_image_role _ _ _

#assert_axioms census_views
#assert_axioms migratable_views
#assert_axioms silent_preserves
#assert_axioms book_silent
#assert_axioms payloadOf_image_role
#assert_axioms readSlot_role
#assert_axioms resolution_silent

/-! ## Packages and records that keep their key -/

/-- A state migrates under an absent package only by the identity. -/
theorem migratable_empty_package {config : Config} {record : ObjectRecord} {object : CellId} {next : Pending}
    {value : Data} (holds : Migratable config [] record object next value) (package : Bytes) :
    Migratable config package record object next value := by
  obtain ⟨migrated, ran, admitted⟩ := holds
  refine ⟨migrated, ?_, admitted⟩
  unfold migrateValue at ran ⊢
  cases name : next.migration with
  | none => rw [name] at ran; exact ran
  | some name' =>
    rw [name] at ran
    simp [loadMigration, decodeStored_nil] at ran

/-- Transfer when a package may only appear where there was none. -/
theorem migratable_views' {config : Config} {P Q : Payloads}
    (objects : ∀ object, objectView object (Q (objectCell config.domain object)) =
      objectView object (P (objectCell config.domain object)))
    (states : ∀ object, stateView object (Q (stateCell config.domain object)) =
      stateView object (P (stateCell config.domain object)))
    (packages : ∀ pin, packageView (Q (packageCell config.domain pin)) = packageView (P (packageCell config.domain pin)) ∨
      packageView (P (packageCell config.domain pin)) = [])
    (holds : MigratableStates config P) : MigratableStates config Q := by
  intro object record next deadline state held draining stated
  have before := holds object record next deadline state (by rw [← objects]; exact held) draining
    (by rw [← states]; exact stated)
  rcases packages next.pin with same | empty
  · rw [same]; exact before
  · rw [empty] at before; exact migratable_empty_package before _

/-- The key of an awaiting record the census reads. -/
def recordKey' (record : Record) : CellId × Digest × Digest := (record.object, record.pin, record.activity)

theorem census_keys {config : Config} {P Q : Payloads} {cells : List CellId}
    (awaiting : ∀ cell, (awaitingView config Q cell).map recordKey' = (awaitingView config P cell).map recordKey')
    (objects : ∀ object, objectView object (Q (objectCell config.domain object)) =
      objectView object (P (objectCell config.domain object)))
    (census : Census config P cells) : Census config Q cells where
  nodup := census.nodup
  covers := fun cell activity found => by
    cases before : awaitingView config P cell with
    | none => have := awaiting cell; rw [found, before] at this; cases this
    | some old => exact census.covers cell old before
  homed := fun cell activity found => by
    cases before : awaitingView config P cell with
    | none => have := awaiting cell; rw [found, before] at this; cases this
    | some old =>
      have keys := awaiting cell
      rw [found, before] at keys
      simp only [Option.map_some, Option.some.injEq, recordKey', Prod.mk.injEq] at keys
      obtain ⟨record, held⟩ := census.homed cell old before
      exact ⟨record, by rw [objects, keys.1]; exact held⟩
  counted := fun object record held c => by
    have same : counts config Q object record c = counts config P object record c := by
      funext cell
      have keys := awaiting cell
      unfold counts
      cases hq : awaitingView config Q cell with
      | none => cases hp : awaitingView config P cell with
        | none => rfl
        | some old => rw [hq, hp] at keys; cases keys
      | some new => cases hp : awaitingView config P cell with
        | none => rw [hq, hp] at keys; cases keys
        | some old =>
          rw [hq, hp] at keys
          simp only [Option.map_some, Option.some.injEq, recordKey', Prod.mk.injEq] at keys
          simp only [keys.1, keys.2.1, keys.2.2]
    rw [same]
    exact census.counted object record (by rw [← objects]; exact held) c

theorem readRecord_role {rootBytes : Bytes → Digest} {snapshot : Snapshot rootBytes} {cell : CellId}
    {record : Record} (read : readRecord snapshot cell = some record) :
    OfRole .record (payloadOf (snapshot.canonicalBytes cell)) := by
  intro payload found
  by_contra wrong
  have empty : bodyOf .record (snapshot.canonicalBytes cell) = none := by simp [bodyOf, found, wrong]
  simp [readRecord, empty] at read

theorem recordImage_role (record : Record) : OfRole .record (payloadOf (recordImage record)) := by
  unfold recordImage
  split
  · exact payloadOf_image_role _ _ _
  · intro p found; rw [payloadOf_retired] at found; cases found
  · intro p found; rw [payloadOf_retired] at found; cases found

/-- The awaiting view of a cell holding a record image at the record's own coordinate. -/
theorem awaiting_recordImage (config : Config) (P : Payloads) (cell : CellId) (record : Record)
    (holds : P cell = payloadOf (recordImage record)) (located : cell = recordCell config.domain record.object record.activity) :
    awaitingView config P cell = if record.phase.awaits then some record else none := by
  unfold awaitingView recordView
  rw [holds]
  unfold recordImage
  cases phase : record.phase with
  | awaiting await =>
    simp [phase, ObjectiveActivity.payloadOf_image, record_roundTrip, located, Phase.awaits]
  | done result => simp [phase, payloadOf_retired, Phase.awaits]
  | faulted reason => simp [phase, payloadOf_retired, Phase.awaits]

/-- The awaiting view of a cell holding a record payload, read through `readRecord`. -/
theorem awaiting_readRecord {rootBytes : Bytes → Digest} (config : Config) (snapshot : Snapshot rootBytes)
    {cell : CellId} {record : Record} (read : readRecord snapshot cell = some record)
    (located : cell = recordCell config.domain record.object record.activity) :
    awaitingView config (payloads snapshot.canonicalBytes) cell = if record.phase.awaits then some record else none := by
  have view : recordView (payloads snapshot.canonicalBytes cell) = some record := by
    unfold readRecord bodyOf at read
    unfold recordView payloads
    cases found : payloadOf (snapshot.canonicalBytes cell) with
    | none => rw [found] at read; cases read
    | some p =>
      rw [found] at read
      by_cases role : p.role = .record
      · simp [role] at read ⊢; exact read
      · simp [role] at read
  unfold awaitingView
  rw [view]
  by_cases awaits : record.phase.awaits = true <;> simp [awaits, located]

#assert_axioms migratable_empty_package
#assert_axioms migratable_views'
#assert_axioms census_keys
#assert_axioms readRecord_role
#assert_axioms recordImage_role
#assert_axioms awaiting_recordImage
#assert_axioms awaiting_readRecord

/-! ## The quiet turns, publication, exhaustion -/

theorem head_payload_at {rootBytes : Bytes → Digest} (snapshot : Snapshot rootBytes) (cell : CellId) (bytes : Bytes)
    (rest : List Post) : payloads (afterPosts snapshot (postAt snapshot cell bytes :: rest)) cell = payloadOf bytes := by
  unfold payloads afterPosts; simp [postAt]

theorem head_payload {rootBytes : Bytes → Digest} (snapshot : Snapshot rootBytes) (first : Post) (rest : List Post) :
    payloads (afterPosts snapshot (first :: rest)) first.cell = payloadOf first.bytes := by
  unfold payloads; rw [afterPosts_first]

theorem Resolution.upgradable {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height : Nat} {request : ResolveRequest} (resolution : Resolution config snapshot height request)
    (holds : Upgradable config (payloads snapshot.canonicalBytes)) :
    Upgradable config (payloads (afterPosts snapshot resolution.posts)) :=
  silent_preserves (resolution_silent resolution) holds

theorem TopUp.upgradable {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {request : TopUpRequest} (topped : TopUp config snapshot request)
    (holds : Upgradable config (payloads snapshot.canonicalBytes)) :
    Upgradable config (payloads (afterPosts snapshot [topped.posted.write config snapshot])) :=
  silent_preserves (fun post member => by
    simp only [List.mem_singleton] at member; subst member; exact book_silent topped.bookExact topped.posted) holds

theorem Publication.upgradable {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {stored : Stored} (publication : Publication config snapshot stored)
    (holds : Upgradable config (payloads snapshot.canonicalBytes)) :
    Upgradable config (payloads (afterPosts snapshot publication.posts)) := by
  have kinded : ∀ p ∈ publication.posts, Kinded snapshot .package p ∧
      payloadOf (snapshot.canonicalBytes p.cell) = none := by
    rw [publication.postsExact]
    intro p member
    simp only [List.mem_singleton] at member
    subst member
    have fresh : payloadOf (snapshot.canonicalBytes (postAt snapshot (packageCell config.domain publication.pin)
        (image .package (packageKey publication.pin) (encodeStored stored))).cell) = none := publication.fresh
    exact ⟨⟨fun q found => (by rw [fresh] at found; cases found), payloadOf_image_role _ _ _⟩, fresh⟩
  have awaiting := fun cell => awaiting_after_kinded config snapshot publication.posts cell
    (fun p member _ => ⟨.package, by decide, (kinded p member).1⟩)
  have objects := fun object => objectView_after_kinded snapshot publication.posts object
    (objectCell config.domain object) (fun p member _ => ⟨.package, by decide, (kinded p member).1⟩)
  have states := fun object => stateView_after_kinded snapshot publication.posts object
    (stateCell config.domain object) (fun p member _ => ⟨.package, by decide, (kinded p member).1⟩)
  have packages : ∀ pin, packageView (payloads (afterPosts snapshot publication.posts) (packageCell config.domain pin)) =
      packageView (payloads snapshot.canonicalBytes (packageCell config.domain pin)) ∨
      packageView (payloads snapshot.canonicalBytes (packageCell config.domain pin)) = [] := by
    intro pin
    rcases payloads_after snapshot publication.posts (packageCell config.domain pin) with ⟨same, _⟩ | ⟨p, member, at_, _⟩
    · left; rw [same]
    · right
      have empty := (kinded p member).2
      rw [at_] at empty
      simp [payloads, empty, packageView]
  obtain ⟨⟨cells, census⟩, migratable⟩ := holds
  exact ⟨⟨cells, census_views awaiting objects census⟩, migratable_views' objects states packages migratable⟩

theorem Exhaustion.upgradable {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height : Nat} {request : ExhaustRequest} (exhausted : Exhaustion config snapshot height request)
    (holds : Upgradable config (payloads snapshot.canonicalBytes)) :
    Upgradable config (payloads (afterPosts snapshot exhausted.posts)) := by
  have recordKinded : Kinded snapshot .record (recordPost config snapshot request.record exhausted.next) :=
    ⟨readRecord_role exhausted.recordExact, recordImage_role _⟩
  have bookQuiet := book_silent (config := config) exhausted.bookExact exhausted.posted
  have kinded : ∀ p ∈ exhausted.posts, ∃ role, role ≠ .object ∧ role ≠ .state ∧ role ≠ .package ∧
      Kinded snapshot role p := by
    rw [exhausted.postsExact]
    intro p member
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at member
    rcases member with isRecord | isBook
    · subst isRecord; exact ⟨.record, by decide, by decide, by decide, recordKinded⟩
    · subst isBook
      obtain ⟨role, _, o, st, pk, k⟩ := bookQuiet
      exact ⟨role, o, st, pk, k⟩
  have objects := fun object => objectView_after_kinded snapshot exhausted.posts object
    (objectCell config.domain object) (fun p member _ => by
      obtain ⟨role, o, _, _, k⟩ := kinded p member; exact ⟨role, o, k⟩)
  have states := fun object => stateView_after_kinded snapshot exhausted.posts object
    (stateCell config.domain object) (fun p member _ => by
      obtain ⟨role, _, st, _, k⟩ := kinded p member; exact ⟨role, st, k⟩)
  have packages := fun pin => packageView_after_kinded snapshot exhausted.posts (packageCell config.domain pin)
    (fun p member _ => by obtain ⟨role, _, _, pk, k⟩ := kinded p member; exact ⟨role, pk, k⟩)
  have nextExact := exhausted.nextExact
  have awaiting : ∀ cell, (awaitingView config (payloads (afterPosts snapshot exhausted.posts)) cell).map recordKey' =
      (awaitingView config (payloads snapshot.canonicalBytes) cell).map recordKey' := by
    intro cell
    by_cases at_ : cell = request.record
    · subst at_
      have before := awaiting_readRecord config snapshot exhausted.recordExact exhausted.located
      have after := awaiting_recordImage config (payloads (afterPosts snapshot exhausted.posts)) request.record
        exhausted.next (by rw [exhausted.postsExact]; exact head_payload snapshot _ _)
        (by rw [nextExact]; exact exhausted.located)
      rw [before, after, nextExact]
      simp [exhausted.awaiting, Phase.awaits, recordKey']
    · rw [awaiting_after_kinded config snapshot exhausted.posts cell (fun p member pat => by
        rw [exhausted.postsExact] at member
        simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at member
        rcases member with isRecord | isBook
        · subst isRecord; exact absurd pat.symm at_
        · subst isBook
          obtain ⟨role, r, _, _, _, k⟩ := bookQuiet
          exact ⟨role, r, k⟩)]
  obtain ⟨⟨cells, census⟩, migratable⟩ := holds
  exact ⟨⟨cells, census_keys awaiting objects census⟩, migratable_views objects states packages migratable⟩

#assert_axioms head_payload
#assert_axioms head_payload_at
#assert_axioms Resolution.upgradable
#assert_axioms TopUp.upgradable
#assert_axioms Publication.upgradable
#assert_axioms Exhaustion.upgradable

/-! ## Turns that write declared state (call trees) -/

theorem stateKey_inj {a b : CellId} (same : stateKey a = stateKey b) : a = b := by
  have ka : digestStream.toLawful.decode (stateKey a) = some a := digestStream.toLawful.decode_encode a
  have kb : digestStream.toLawful.decode (stateKey b) = some b := digestStream.toLawful.decode_encode b
  rw [same, kb] at ka
  exact (Option.some.inj ka).symm

theorem readState_role {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {object : CellId} {current : Option ObjectState} (read : readState config snapshot object = .ok current) :
    OfRole .state (payloadOf (snapshot.canonicalBytes (stateCell config.domain object))) := by
  intro payload found
  unfold readState stateFor at read
  rw [found] at read
  simp only at read
  split at read
  · rename_i owned; exact owned.1
  · cases read

theorem readInbox_role {rootBytes : Bytes → Digest} {snapshot : Snapshot rootBytes} {cell : CellId}
    {read : Option Inbox.Inbox} (found : readInbox snapshot cell = some read) :
    OfRole .inbox (payloadOf (snapshot.canonicalBytes cell)) := by
  intro payload present
  by_contra wrong
  have empty : bodyOf .inbox (snapshot.canonicalBytes cell) = none := by simp [bodyOf, present, wrong]
  simp [readInbox, empty, present] at found

theorem stateView_stateImage (object other : CellId) (state : ObjectState) :
    stateView other (payloadOf (stateImage object state)) =
      if other = object then some state else none := by
  unfold stateView stateImage
  rw [ObjectiveActivity.payloadOf_image]
  by_cases same : other = object
  · subst same; simp [ObjectState.objectState_roundTrip]
  · have keys : stateKey object ≠ stateKey other := fun h => same (stateKey_inj h).symm
    simp [same, keys]

/-- A state post's obligation: on a draining object, the state is migratable. -/
def StateJudged {rootBytes : Bytes → Digest} (config : Config) (snapshot : Snapshot rootBytes) (object : CellId)
    (state : ObjectState) : Prop :=
  ∀ record next deadline, readObject config snapshot object = .ok (some record) → record.phase = .draining next deadline →
    Migratable config (packageBytes config snapshot next.pin) record object next state.value

/-- A post of a turn that writes declared state: quiet, or a judged state post on a state
cell read in the turn. -/
def StatePostOk {rootBytes : Bytes → Digest} (config : Config) (snapshot : Snapshot rootBytes) (post : Post) : Prop :=
  Silent snapshot post ∨ ∃ object state, post = postAt snapshot (stateCell config.domain object) (stateImage object state) ∧
    (∃ current, readState config snapshot object = .ok current) ∧ StateJudged config snapshot object state

theorem statePostOk_kinded {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {post : Post} (ok : StatePostOk config snapshot post) :
    ∃ role, role ≠ .record ∧ role ≠ .object ∧ role ≠ .package ∧ Kinded snapshot role post := by
  rcases ok with ⟨role, r, o, _, pk, k⟩ | ⟨object, state, isState, ⟨current, read⟩, _⟩
  · exact ⟨role, r, o, pk, k⟩
  · subst isState
    exact ⟨.state, by decide, by decide, by decide, readState_role read, payloadOf_image_role _ _ _⟩

/-- **A turn whose posts are quiet or judged state posts keeps both invariants.** -/
theorem stateful_preserves {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {posts : List Post} (ok : ∀ post ∈ posts, StatePostOk config snapshot post)
    (holds : Upgradable config (payloads snapshot.canonicalBytes)) :
    Upgradable config (payloads (afterPosts snapshot posts)) := by
  have awaiting := fun cell => awaiting_after_kinded config snapshot posts cell (fun p member _ => by
    obtain ⟨role, r, _, _, k⟩ := statePostOk_kinded (ok p member); exact ⟨role, r, k⟩)
  have objects := fun object => objectView_after_kinded snapshot posts object (objectCell config.domain object)
    (fun p member _ => by obtain ⟨role, _, o, _, k⟩ := statePostOk_kinded (ok p member); exact ⟨role, o, k⟩)
  have packages := fun pin => packageView_after_kinded snapshot posts (packageCell config.domain pin)
    (fun p member _ => by obtain ⟨role, _, _, pk, k⟩ := statePostOk_kinded (ok p member); exact ⟨role, pk, k⟩)
  obtain ⟨⟨cells, census⟩, migratable⟩ := holds
  refine ⟨⟨cells, census_views awaiting objects census⟩, ?_⟩
  intro object record next deadline state held draining stated
  rw [packages]
  have heldBefore : objectView object (payloads snapshot.canonicalBytes (objectCell config.domain object)) = some record := by
    rw [← objects]; exact held
  rcases payloads_after snapshot posts (stateCell config.domain object) with ⟨same, _⟩ | ⟨p, member, at_, after⟩
  · exact migratable object record next deadline state heldBefore draining (by rw [← same]; exact stated)
  · rw [after] at stated
    rcases ok p member with ⟨role, _, _, st, _, k⟩ | ⟨object', state', isState, _, judged⟩
    · rw [stateView_of_role st k.2] at stated; cases stated
    · subst isState
      simp only [postAt] at stated at_
      rw [stateView_stateImage] at stated
      split at stated
      · rename_i same
        cases stated
        subst same
        have migr := judged record next deadline (objectView_readObject heldBefore) draining
        rw [packageBytes_view] at migr
        exact migr
      · cases stated

theorem mail_kinded {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    (mail : ObjectiveCall.Mail config snapshot) : ∀ post ∈ mail.posts, Silent snapshot post := by
  intro post member
  rcases List.mem_append.mp member with inInbox | inSlot
  · obtain ⟨held, _, rfl⟩ := List.mem_map.mp inInbox
    exact ⟨.inbox, by decide, by decide, by decide, by decide, readInbox_role held.readExact,
      payloadOf_image_role _ _ _⟩
  · obtain ⟨held, _, rfl⟩ := List.mem_map.mp inSlot
    refine ⟨.slot, by decide, by decide, by decide, by decide, ?_, ?_⟩
    · simp only [slotPost, postAt]
      rw [held.named]
      exact held.slotted
    · simp only [slotPost, postAt]
      exact payloadOf_image_role _ _ _

/-- The state posts of a call tree whose every dirty entry is drained and was read. -/
theorem journal_posts_ok {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {journal : ObjectiveCall.Journal} (read : ObjectiveCall.ObjectsRead config snapshot journal)
    (drained : journal.drained = true) : ∀ post ∈ journal.posts config snapshot, StatePostOk config snapshot post := by
  intro post member
  simp only [ObjectiveCall.Journal.posts, List.mem_filterMap] at member
  obtain ⟨entry, entryIn, made⟩ := member
  have entryDrained : entry.drained = true := List.all_eq_true.mp drained entry entryIn
  obtain ⟨current, readOk⟩ := (read entry entryIn).1
  have recordOk := (read entry entryIn).2
  split at made
  · rename_i dirty
    cases found : entry.current with
    | none => simp [found] at made
    | some state =>
      simp only [found, Option.map_some, Option.some.injEq] at made
      subst made
      refine .inr ⟨entry.object, state, rfl, ⟨current, readOk⟩, ?_⟩
      intro record next deadline readObj draining
      rw [recordOk] at readObj
      cases readObj
      unfold ObjectiveCall.Entry.drained at entryDrained
      simp only [dirty, Bool.not_true, Bool.false_or, found, draining, Bool.and_eq_true] at entryDrained
      obtain ⟨identity, admits⟩ := entryDrained
      refine ⟨state.value, ?_, ?_⟩
      · cases name : next.migration with
        | none => simp [migrateValue, name]
        | some n => rw [name] at identity; cases identity
      · split at admits
        · assumption
        · cases admits
  · cases made

theorem Invocation.upgradable {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height : Nat} {request : ObjectiveCall.InvokeRequest} (invoked : ObjectiveCall.Invocation config snapshot height request)
    (holds : Upgradable config (payloads snapshot.canonicalBytes)) :
    Upgradable config (payloads (afterPosts snapshot invoked.posts)) := by
  obtain ⟨read, _⟩ := ObjectiveCall.exec_invariant config snapshot height request.authority
    (ObjectiveCall.invokeTransaction request) _ [] _ _ _ _ _ _ invoked.execExact (by simp)
    (by intro _ _ h; cases h) (by intro _ h; cases h)
  apply stateful_preserves _ holds
  rw [invoked.postsExact]
  intro post member
  rcases List.mem_append.mp member with front | isBook
  · rcases List.mem_append.mp front with inJournal | inMail
    · exact journal_posts_ok read invoked.drainedOk post inJournal
    · exact .inl (mail_kinded invoked.mail post inMail)
  · simp only [List.mem_singleton] at isBook
    subst isBook
    exact .inl (book_silent invoked.bookExact invoked.posted)

theorem runMessage_drained {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height target : Nat} {message : Inbox.Message} {result : Data} {journal : ObjectiveCall.Journal}
    (ran : ObjectiveSend.runMessage config snapshot height target message = .replied result journal) :
    journal.drained = true := by
  unfold ObjectiveSend.runMessage at ran
  split at ran
  · cases ran
  · split at ran
    · cases ran
    · split at ran
      · rename_i both
        cases ran
        simp only [Bool.and_eq_true] at both
        exact both.2
      · cases ran

theorem MessageDelivery.upgradable {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height : Nat} {request : ObjectiveSend.MessageRequest}
    (delivered : ObjectiveSend.MessageDelivery config snapshot height request)
    (holds : Upgradable config (payloads snapshot.canonicalBytes)) :
    Upgradable config (payloads (afterPosts snapshot delivered.posts)) := by
  apply stateful_preserves _ holds
  rw [delivered.postsExact]
  intro post member
  rcases List.mem_append.mp member with front | last
  · rcases List.mem_append.mp front with fromCalls | fromMail
    · cases outcome : delivered.outcome with
      | failed reason => rw [outcome] at fromCalls; cases fromCalls
      | replied result journal =>
        rw [outcome] at fromCalls
        have ran := delivered.outcomeExact.trans outcome
        exact journal_posts_ok (ObjectiveSend.runMessage_read ran) (runMessage_drained ran) post fromCalls
    · exact .inl (mail_kinded delivered.mail post fromMail)
  · simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at last
    rcases last with isSlot | isBook
    · subst isSlot
      obtain ⟨_, _, _, decided⟩ := AnswerSlot.decideDelivery_single delivered.decidedExact
      have named : delivered.decided.name = delivered.message.id := by rw [decided]; exact delivered.slotNamed
      refine .inl ⟨.slot, by decide, by decide, by decide, by decide, ?_, ?_⟩
      · simp only [slotPost, postAt]
        rw [named]
        exact readSlot_role delivered.slotExact
      · simp only [slotPost, postAt]
        exact payloadOf_image_role _ _ _
    · subst isBook
      exact .inl (book_silent delivered.bookExact delivered.posted)

#assert_axioms stateKey_inj
#assert_axioms readState_role
#assert_axioms readInbox_role
#assert_axioms stateView_stateImage
#assert_axioms statePostOk_kinded
#assert_axioms stateful_preserves
#assert_axioms mail_kinded
#assert_axioms journal_posts_ok
#assert_axioms Invocation.upgradable
#assert_axioms runMessage_drained
#assert_axioms MessageDelivery.upgradable

/-! ## The census step: one object's activities change -/

/-- Awaiting views agree on every activity of objects other than `object`. -/
def OthersAgree (config : Config) (P Q : Payloads) (object : CellId) : Prop :=
  ∀ cell, ∀ other, other ≠ object →
    (awaitingView config Q cell).filter (fun a => decide (a.object = other)) =
      (awaitingView config P cell).filter (fun a => decide (a.object = other))

theorem counts_filter (config : Config) (P : Payloads) (object : CellId) (record : ObjectRecord) (c : LiveClass)
    (cell : CellId) :
    counts config P object record c cell =
      match (awaitingView config P cell).filter (fun a => decide (a.object = object)) with
      | some a => decide (record.classOf a.pin a.activity = c)
      | none => false := by
  unfold counts
  cases awaitingView config P cell with
  | none => rfl
  | some a => by_cases m : a.object = object <;> simp [Option.filter, m]

theorem counts_others {config : Config} {P Q : Payloads} {object : CellId} (agree : OthersAgree config P Q object)
    {other : CellId} (differs : other ≠ object) (record : ObjectRecord) (c : LiveClass) (cell : CellId) :
    counts config Q other record c cell = counts config P other record c cell := by
  rw [counts_filter, counts_filter, agree cell other differs]

/-- `counts` reads the object record only through its classification. -/
theorem counts_classOf {config : Config} {P : Payloads} {object : CellId} {record other : ObjectRecord}
    (same : record.classOf = other.classOf) (c : LiveClass) :
    counts config P object record c = counts config P object other c := by
  funext cell; unfold counts; rw [same]

theorem countP_append_false {l extra : List CellId} {f : CellId → Bool} (none_ : ∀ x ∈ extra, f x = false) :
    (l ++ extra).countP f = l.countP f := by
  rw [List.countP_append]
  have zero : extra.countP f = 0 := List.countP_eq_zero.mpr (fun x member => by simp [none_ x member])
  omega

/-- **The census step.** Every cell's awaiting activity of another object, and every other
object's record, is unchanged; the new list adds `extra` cells; the touched object meets its
own counting obligation. -/
theorem census_step {config : Config} {P Q : Payloads} {cells extra : List CellId} {object : CellId}
    (census : Census config P cells) (nodup : (cells ++ extra).Nodup)
    (covers : ∀ cell activity, awaitingView config Q cell = some activity → cell ∈ cells ++ extra)
    (homed : ∀ cell activity, awaitingView config Q cell = some activity →
      ∃ record, objectView activity.object (Q (objectCell config.domain activity.object)) = some record)
    (others : OthersAgree config P Q object)
    (objects : ∀ other, other ≠ object →
      objectView other (Q (objectCell config.domain other)) = objectView other (P (objectCell config.domain other)))
    (mine : ∀ record, objectView object (Q (objectCell config.domain object)) = some record →
      ∀ c, record.count c = (cells ++ extra).countP (counts config Q object record c)) :
    Census config Q (cells ++ extra) where
  nodup := nodup
  covers := covers
  homed := homed
  counted := fun other record held c => by
    by_cases same : other = object
    · subst same; exact mine record held c
    · rw [census.counted other record (by rw [← objects other same]; exact held) c]
      have extraFalse : ∀ x ∈ extra, counts config Q other record c x = false := by
        intro x member
        rw [counts_others others same]
        unfold counts
        cases hp : awaitingView config P x with
        | none => rfl
        | some a =>
          have inCells := census.covers x a hp
          exact absurd member (List.disjoint_of_nodup_append nodup inCells)
      rw [countP_append_false extraFalse]
      exact countP_congr_mem (fun x _ => (counts_others others same record c x).symm)

#assert_axioms counts_filter
#assert_axioms counts_others
#assert_axioms counts_classOf
#assert_axioms countP_append_false
#assert_axioms census_step

/-! ## Object record posts -/

theorem objectKey_inj {a b : CellId} (same : objectKey a = objectKey b) : a = b := by
  have ka : digestStream.toLawful.decode (objectKey a) = some a := digestStream.toLawful.decode_encode a
  have kb : digestStream.toLawful.decode (objectKey b) = some b := digestStream.toLawful.decode_encode b
  rw [same, kb] at ka
  exact (Option.some.inj ka).symm

theorem objectView_objectImage (object other : CellId) (record : ObjectRecord) :
    objectView other (payloadOf (objectImage object record)) = if other = object then some record else none := by
  unfold objectView objectImage
  rw [ObjectiveActivity.payloadOf_image]
  by_cases same : other = object
  · subst same; simp [ObjectRecord.record_roundTrip]
  · have keys : objectKey object ≠ objectKey other := fun h => same (objectKey_inj h).symm
    simp [same, keys]

/-- An object's record payload is keyed by the object: no other object reads it. -/
theorem objectView_held_other {payload : Option Payload} {object other : CellId} {record : ObjectRecord}
    (held : objectView object payload = some record) (differs : other ≠ object) : objectView other payload = none := by
  cases payload with
  | none => rfl
  | some p =>
    simp only [objectView] at held ⊢
    by_cases owned : p.role = .object ∧ p.key = objectKey object
    · have keys : ¬ (p.role = .object ∧ p.key = objectKey other) := fun h =>
        differs (objectKey_inj (h.2.symm.trans owned.2))
      rw [if_neg keys]
    · rw [if_neg owned] at held; cases held

theorem objectView_role {object : CellId} {payload : Option Payload} {record : ObjectRecord}
    (held : objectView object payload = some record) : ∃ p, payload = some p ∧ p.role = .object := by
  cases payload with
  | none => cases held
  | some p =>
    simp only [objectView] at held
    by_cases owned : p.role = .object ∧ p.key = objectKey object
    · exact ⟨p, rfl, owned.1⟩
    · rw [if_neg owned] at held; cases held

/-- **One object post, effective, invisible to other objects.** If a turn's posts are its one
object post (at the object's cell, the first post there) or kinded posts of another role, the
object reads the posted record and every other object reads what it read. -/
theorem objects_after_one {rootBytes : Bytes → Digest} (config : Config) (snapshot : Snapshot rootBytes)
    (posts : List Post) (object : CellId) (record : ObjectRecord)
    (effective : payloads (afterPosts snapshot posts) (objectCell config.domain object) =
      payloadOf (objectImage object record))
    (kinded : ∀ p ∈ posts, p = postAt snapshot (objectCell config.domain object) (objectImage object record) ∨
      ∃ role, role ≠ .object ∧ Kinded snapshot role p)
    (before : ∀ other, other ≠ object →
      objectView other (payloads snapshot.canonicalBytes (objectCell config.domain object)) = none) :
    ∀ other, objectView other (payloads (afterPosts snapshot posts) (objectCell config.domain other)) =
      if other = object then some record else objectView other (payloads snapshot.canonicalBytes (objectCell config.domain other)) := by
  intro other
  by_cases same : other = object
  · subst same; rw [effective, objectView_objectImage]; simp
  · rw [if_neg same]
    rcases payloads_after snapshot posts (objectCell config.domain other) with ⟨kept, _⟩ | ⟨p, member, at_, after⟩
    · rw [kept]
    · rw [after]
      rcases kinded p member with isObject | ⟨role, o, pre, post⟩
      · subst isObject
        simp only [postAt] at at_ ⊢
        rw [objectView_objectImage, if_neg same, ← at_]
        exact (before other same).symm
      · rw [objectView_of_role o post, show payloads snapshot.canonicalBytes (objectCell config.domain other) =
          payloadOf (snapshot.canonicalBytes p.cell) by rw [at_]; rfl, objectView_of_role o pre]

/-- The object post is the first post at the object's cell when every other post is kinded
of another role and the cell holds the object's record. -/
theorem object_post_effective {rootBytes : Bytes → Digest} (config : Config) (snapshot : Snapshot rootBytes)
    (posts : List Post) (object : CellId) (record held : ObjectRecord)
    (member : postAt snapshot (objectCell config.domain object) (objectImage object record) ∈ posts)
    (kinded : ∀ p ∈ posts, p = postAt snapshot (objectCell config.domain object) (objectImage object record) ∨
      ∃ role, role ≠ .object ∧ Kinded snapshot role p)
    (holds : objectView object (payloads snapshot.canonicalBytes (objectCell config.domain object)) = some held) :
    payloads (afterPosts snapshot posts) (objectCell config.domain object) = payloadOf (objectImage object record) := by
  obtain ⟨payload, present, role⟩ := objectView_role holds
  rcases payloads_after snapshot posts (objectCell config.domain object) with ⟨_, none_⟩ | ⟨p, inPosts, at_, after⟩
  · exact absurd (show (postAt snapshot (objectCell config.domain object) (objectImage object record)).cell =
      objectCell config.domain object from rfl) (none_ _ member)
  · rw [after]
    rcases kinded p inPosts with isObject | ⟨r, o, pre, _⟩
    · subst isObject; simp only [postAt]
    · exfalso
      have := pre payload (by rw [at_]; exact present)
      rw [role] at this
      exact o this.symm

/-- A bumped record drains toward the same upgrade, up to its pending counter. -/
theorem bump_draining {record : ObjectRecord} {f : Nat → Nat} {c : LiveClass} {next : Pending} {deadline : Nat}
    (draining : (record.bump f c).phase = .draining next deadline) :
    ∃ old live, record.phase = .draining old deadline ∧ next = { old with live := live } := by
  cases c with
  | live => exact ⟨next, next.live, draining, rfl⟩
  | rebirth => exact ⟨next, next.live, draining, rfl⟩
  | pending =>
    unfold ObjectRecord.bump at draining
    cases phase : record.phase with
    | steady => rw [phase] at draining; simp at draining; rw [phase] at draining; cases draining
    | draining old d =>
      rw [phase] at draining
      simp only at draining
      cases draining
      exact ⟨old, f old.live, rfl, rfl⟩

theorem recount_draining {record : ObjectRecord} {pin activity : Digest} {before after : Bool} {next : Pending}
    {deadline : Nat} (draining : (recount record pin activity before after).phase = .draining next deadline) :
    ∃ old live, record.phase = .draining old deadline ∧ next = { old with live := live } := by
  unfold recount ObjectRecord.retain ObjectRecord.release at draining
  split at draining
  · exact bump_draining draining
  · split at draining
    · exact bump_draining draining
    · exact ⟨next, next.live, draining, rfl⟩

theorem recount_classOf (record : ObjectRecord) (pin activity : Digest) (before after : Bool) :
    (recount record pin activity before after).classOf = record.classOf := by
  unfold recount ObjectRecord.retain ObjectRecord.release
  split
  · exact ObjectRecord.bump_classOf _ _ _
  · split
    · exact ObjectRecord.bump_classOf _ _ _
    · rfl

#assert_axioms objectKey_inj
#assert_axioms objectView_objectImage
#assert_axioms objectView_held_other
#assert_axioms objectView_role
#assert_axioms objects_after_one
#assert_axioms object_post_effective
#assert_axioms bump_draining
#assert_axioms recount_draining
#assert_axioms recount_classOf

/-! ## Ending an activity: abandonment, abort -/

theorem abandonSlot_silent {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {await : Await} {posts : List Post} {claims : List StableNullifier}
    (ok : abandonSlot config snapshot await = .ok (posts, claims)) : ∀ post ∈ posts, Silent snapshot post := by
  unfold abandonSlot at ok
  split at ok
  · simp only [Except.ok.injEq, Prod.mk.injEq] at ok
    rw [← ok.1]; simp
  · rename_i name _ _
    cases read : readSlot config snapshot name with
    | none => simp [read] at ok
    | some slot =>
      simp only [read] at ok
      have vacate : ∀ post ∈ [slotRetire config snapshot name], Silent snapshot post := by
        intro post member
        simp only [List.mem_singleton] at member
        subst member
        refine ⟨.slot, by decide, by decide, by decide, by decide, readSlot_role read, ?_⟩
        intro p found
        rw [show (slotRetire config snapshot name).bytes = retiredImage from rfl, payloadOf_retired] at found
        cases found
      split at ok <;>
      · simp only [Except.ok.injEq, Prod.mk.injEq] at ok
        rw [← ok.1]; exact vacate

theorem countPosts_ending {rootBytes : Bytes → Digest} (config : Config) (snapshot : Snapshot rootBytes)
    (object : CellId) (record : ObjectRecord) (pin activity : Digest) :
    countPosts config snapshot object record pin activity true false =
      [postAt snapshot (objectCell config.domain object) (objectImage object (record.release pin activity))] := by
  simp [countPosts, recount]

theorem object_post_kinded {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {object : CellId} {held record : ObjectRecord}
    (holds : objectView object (payloads snapshot.canonicalBytes (objectCell config.domain object)) = some held) :
    Kinded snapshot .object (postAt snapshot (objectCell config.domain object) (objectImage object record)) := by
  refine ⟨?_, payloadOf_image_role _ _ _⟩
  intro p found
  simp only [postAt] at found
  obtain ⟨payload, present, role⟩ := objectView_role holds
  have same : payload = p := by
    have h : payloadOf (snapshot.canonicalBytes (objectCell config.domain object)) = some payload := present
    rw [found] at h
    exact (Option.some.inj h).symm
  rw [← same]; exact role

/-- **The census after a turn that ENDS one awaiting activity** at its record cell (its own
coordinate), releasing its counter in the object record it posts, and changes no other awaiting
cell. -/
theorem census_end {config : Config} {P Q : Payloads} {cells : List CellId} {cell : CellId} {record : Record}
    {object : ObjectRecord} (census : Census config P cells)
    (before : awaitingView config P cell = some record)
    (after : awaitingView config Q cell = none)
    (elsewhere : ∀ other, other ≠ cell → awaitingView config Q other = awaitingView config P other)
    (held : objectView record.object (P (objectCell config.domain record.object)) = some object)
    (objects : ∀ other, objectView other (Q (objectCell config.domain other)) =
      if other = record.object then some (object.release record.pin record.activity)
      else objectView other (P (objectCell config.domain other))) :
    Census config Q cells := by
  have nodup : (cells ++ []).Nodup := by rw [List.append_nil]; exact census.nodup
  have awaitingSame : ∀ other activity, awaitingView config Q other = some activity →
      awaitingView config P other = some activity := by
    intro other activity found
    by_cases at_ : other = cell
    · subst at_; rw [after] at found; cases found
    · rw [← elsewhere other at_]; exact found
  have step : Census config Q (cells ++ []) := by
    apply census_step (extra := []) (object := record.object) census nodup
    · intro other activity found
      rw [List.append_nil]
      exact census.covers other activity (awaitingSame other activity found)
    · intro other activity found
      obtain ⟨r0, h0⟩ := census.homed other activity (awaitingSame other activity found)
      rw [objects]
      split
      · exact ⟨_, rfl⟩
      · exact ⟨r0, h0⟩
    · intro other who differs
      by_cases at_ : other = cell
      · subst at_
        rw [after, before]
        have notMine : record.object ≠ who := fun h => differs h.symm
        simp [Option.filter, notMine]
      · rw [elsewhere other at_]
    · intro other differs
      rw [objects, if_neg differs]
    · intro released found c
      rw [objects, if_pos rfl] at found
      cases found
      have inCells := census.covers cell record before
      have classes : (object.release record.pin record.activity).classOf = object.classOf :=
        ObjectRecord.bump_classOf _ _ _
      have counted := census.counted record.object object held c
      have change := countP_change_one census.nodup inCells
        (f := counts config P record.object (object.release record.pin record.activity) c)
        (g := counts config Q record.object (object.release record.pin record.activity) c)
        (fun other _ differs => by unfold counts; rw [elsewhere other differs])
      rw [List.append_nil]
      rw [counts_classOf (P := P) (object := record.object) classes c] at change
      rw [ObjectRecord.release_count, counted]
      have fy : counts config P record.object object c cell = decide (object.classOf record.pin record.activity = c) := by
        simp [counts, before]
      have gy : counts config Q record.object (object.release record.pin record.activity) c cell = false := by
        simp [counts, after]
      rw [fy, gy] at change
      by_cases cls : c = object.classOf record.pin record.activity
      · subst cls; simp at change ⊢; omega
      · have ncls : ¬ object.classOf record.pin record.activity = c := fun h => cls h.symm
        simp [ncls, cls] at change ⊢; omega
  rw [List.append_nil] at step
  exact step

/-- **The migratable states after a turn that rewrites one object record's counters**, and
neither the states nor the packages. -/
theorem migratable_counter {config : Config} {P Q : Payloads} {objectId : CellId} {object posted : ObjectRecord}
    (holds : MigratableStates config P)
    (held : objectView objectId (P (objectCell config.domain objectId)) = some object)
    (objects : ∀ other, objectView other (Q (objectCell config.domain other)) =
      if other = objectId then some posted else objectView other (P (objectCell config.domain other)))
    (draining : ∀ next deadline, posted.phase = .draining next deadline →
      ∃ old live, object.phase = .draining old deadline ∧ next = { old with live := live })
    (states : ∀ other, stateView other (Q (stateCell config.domain other)) = stateView other (P (stateCell config.domain other)))
    (packages : ∀ pin, packageView (Q (packageCell config.domain pin)) = packageView (P (packageCell config.domain pin))) :
    MigratableStates config Q := by
  intro other record next deadline state found phase stated
  rw [states] at stated
  rw [objects] at found
  split at found
  · rename_i same
    subst same
    cases found
    obtain ⟨old, live, oldPhase, nextIs⟩ := draining next deadline phase
    subst nextIs
    have before := holds other object old deadline state held oldPhase stated
    rw [packages]
    exact migratable_record config _ object posted other old live state.value before
  · rw [packages]
    exact holds other record next deadline state found phase stated

/-- **A turn that ends one awaiting activity keeps both invariants**: it retires the record
cell, retires slots, posts the Book and the object record with the activity released. -/
theorem ending_upgradable {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {posts slotPosts : List Post} {bookPost : Post} {cell : CellId} {record : Record} {object : ObjectRecord}
    (recordExact : readRecord snapshot cell = some record)
    (located : cell = recordCell config.domain record.object record.activity)
    (awaits : record.phase.awaits = true)
    (objectExact : readObject config snapshot record.object = .ok (some object))
    (slotsSilent : ∀ p ∈ slotPosts, Silent snapshot p) (bookSilent : Silent snapshot bookPost)
    (postsIs : posts = postAt snapshot cell retiredImage ::
      (slotPosts ++ [bookPost] ++
        [postAt snapshot (objectCell config.domain record.object)
          (objectImage record.object (object.release record.pin record.activity))]))
    (holds : Upgradable config (payloads snapshot.canonicalBytes)) :
    Upgradable config (payloads (afterPosts snapshot posts)) := by
  have heldObject := readObject_some objectExact
  have retireKinded : Kinded snapshot .record (postAt snapshot cell retiredImage) :=
    ⟨readRecord_role recordExact, fun p found => by
      rw [show (postAt snapshot cell retiredImage).bytes = retiredImage from rfl, payloadOf_retired] at found
      cases found⟩
  have kinded : ∀ p ∈ posts, p = postAt snapshot (objectCell config.domain record.object)
      (objectImage record.object (object.release record.pin record.activity)) ∨
      ∃ role, role ≠ .object ∧ role ≠ .state ∧ role ≠ .package ∧ Kinded snapshot role p := by
    rw [postsIs]
    intro p member
    simp only [List.mem_cons, List.mem_append, List.mem_singleton, List.not_mem_nil, or_false] at member
    rcases member with isRetire | ((inSlot | isBook) | isObject)
    · exact .inr ⟨.record, by decide, by decide, by decide, isRetire ▸ retireKinded⟩
    · obtain ⟨role, _, o, st, pk, k⟩ := slotsSilent p inSlot
      exact .inr ⟨role, o, st, pk, k⟩
    · subst isBook
      obtain ⟨role, _, o, st, pk, k⟩ := bookSilent
      exact .inr ⟨role, o, st, pk, k⟩
    · exact .inl isObject
  have notObject : ∀ p ∈ posts, p = postAt snapshot (objectCell config.domain record.object)
      (objectImage record.object (object.release record.pin record.activity)) ∨
      ∃ role, role ≠ .object ∧ Kinded snapshot role p := by
    intro p member
    rcases kinded p member with isObject | ⟨role, o, _, _, k⟩
    · exact .inl isObject
    · exact .inr ⟨role, o, k⟩
  have objectKinded := object_post_kinded (record := object.release record.pin record.activity) heldObject
  have otherRole : ∀ p ∈ posts, ∃ role, role ≠ .state ∧ role ≠ .package ∧ Kinded snapshot role p := by
    intro p member
    rcases kinded p member with isObject | ⟨role, _, st, pk, k⟩
    · subst isObject; exact ⟨.object, by decide, by decide, objectKinded⟩
    · exact ⟨role, st, pk, k⟩
  have effective := object_post_effective config snapshot posts record.object _ object
    (by rw [postsIs]; simp) notObject heldObject
  have objects := objects_after_one config snapshot posts record.object _ effective notObject
    (fun other differs => objectView_held_other heldObject differs)
  have states := fun object => stateView_after_kinded snapshot posts object (stateCell config.domain object)
    (fun p member _ => by obtain ⟨role, st, _, k⟩ := otherRole p member; exact ⟨role, st, k⟩)
  have packages := fun pin => packageView_after_kinded snapshot posts (packageCell config.domain pin)
    (fun p member _ => by obtain ⟨role, _, pk, k⟩ := otherRole p member; exact ⟨role, pk, k⟩)
  have before := awaiting_readRecord config snapshot recordExact located
  rw [awaits, if_pos rfl] at before
  have after : awaitingView config (payloads (afterPosts snapshot posts)) cell = none := by
    apply awaitingView_of_recordView
    rw [postsIs, head_payload_at]
    simp [recordView, payloadOf_retired]
  have elsewhere : ∀ other, other ≠ cell →
      awaitingView config (payloads (afterPosts snapshot posts)) other =
        awaitingView config (payloads snapshot.canonicalBytes) other := by
    intro other differs
    apply awaiting_after_kinded
    intro p member at_
    rcases kinded p member with isObject | ⟨role, _, _, _, k⟩
    · subst isObject; exact ⟨.object, by decide, objectKinded⟩
    · by_cases isRecord : role = .record
      · subst isRecord
        rw [postsIs] at member
        simp only [List.mem_cons, List.mem_append, List.mem_singleton, List.not_mem_nil, or_false] at member
        rcases member with isRetire | ((inSlot | isBook) | isObject)
        · subst isRetire; exact absurd at_.symm (by simpa [postAt] using differs)
        · obtain ⟨role', r', _, _, _, k'⟩ := slotsSilent p inSlot; exact ⟨role', r', k'⟩
        · subst isBook
          obtain ⟨role', r', _, _, _, k'⟩ := bookSilent
          exact ⟨role', r', k'⟩
        · subst isObject; exact ⟨.object, by decide, objectKinded⟩
      · exact ⟨role, isRecord, k⟩
  obtain ⟨⟨cells, census⟩, migratable⟩ := holds
  refine ⟨⟨cells, census_end census (cell := cell) before after elsewhere heldObject objects⟩, ?_⟩
  exact migratable_counter migratable heldObject objects
    (fun next deadline phase => by
      have := recount_draining (record := object) (pin := record.pin) (activity := record.activity)
        (before := true) (after := false) (next := next) (deadline := deadline)
        (by simpa [recount] using phase)
      exact this) states packages

theorem Abandonment.upgradable {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height : Nat} {request : AbandonRequest} (ab : Abandonment config snapshot height request)
    (holds : Upgradable config (payloads snapshot.canonicalBytes)) :
    Upgradable config (payloads (afterPosts snapshot ab.posts)) :=
  ending_upgradable ab.recordExact ab.located (by rw [ab.awaiting]; rfl) ab.objectExact
    (abandonSlot_silent ab.slotExact) (book_silent ab.bookExact ab.posted)
    (by rw [ab.postsExact, countPosts_ending]) holds

theorem Abort.upgradable {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height : Nat} {request : AbortRequest} (aborted : Abort config snapshot height request)
    (holds : Upgradable config (payloads snapshot.canonicalBytes)) :
    Upgradable config (payloads (afterPosts snapshot aborted.posts)) := by
  have ended : ∀ await, aborted.ended.phase ≠ .awaiting await := by
    rw [aborted.endedExact]
    exact nextRecord_ended _ _ _ _ (abortSegment_ends aborted.segmentExact)
  exact ending_upgradable aborted.recordExact aborted.located (by rw [aborted.awaiting]; rfl) aborted.objectExact
    (abandonSlot_silent aborted.slotExact) (book_silent aborted.bookExact aborted.posted)
    (by rw [aborted.postsExact, countPosts_ending]; simp [recordPost, recordImage_ended _ ended]) holds

#assert_axioms abandonSlot_silent
#assert_axioms countPosts_ending
#assert_axioms object_post_kinded
#assert_axioms census_end
#assert_axioms migratable_counter
#assert_axioms ending_upgradable
#assert_axioms Abandonment.upgradable
#assert_axioms Abort.upgradable

/-! ## Yields: a state write and a fresh slot -/

/-- What a yield commit posts: its state write, or a fresh slot. -/
theorem commitYield_posts_shape {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height : Nat} {transaction : TransactionId} {cell object : CellId} {generation : Nat} {checkpoint : Digest}
    {current : Option ObjectState} {viewed : Bool} {plan : PlanAwait} {committed : YieldCommit}
    (ok : commitYield config snapshot height transaction cell object generation checkpoint current viewed plan =
      .ok committed) :
    ∀ post ∈ committed.posts, (∃ written, committed.written = some written ∧ post = written.post) ∨
      (payloadOf (snapshot.canonicalBytes post.cell) = none ∧ OfRole .slot (payloadOf post.bytes)) := by
  have stateShape : ∀ written : Option StateWritten, ∀ post ∈ (written.map StateWritten.post).toList,
      ∃ one, written = some one ∧ post = one.post := by
    intro written post member
    cases written with
    | none => simp at member
    | some one => simp only [Option.map_some, Option.toList_some, List.mem_singleton] at member; exact ⟨one, rfl, member⟩
  unfold commitYield at ok
  split at ok
  · cases ok
  · split at ok
    · cases ok
    · rename_i written wrote
      split at ok
      · split at ok
        · cases ok
        · rename_i fresh
          simp only [Except.ok.injEq] at ok
          subst ok
          intro post member
          simp only [List.mem_append, List.mem_singleton] at member
          rcases member with inState | isSlot
          · exact .inl (stateShape _ post inState)
          · subst isSlot
            refine .inr ⟨?_, payloadOf_image_role _ _ _⟩
            have both := fresh
            simp only [Bool.or_eq_true, not_or, Option.isSome_iff_ne_none, ne_eq, not_not] at both
            exact both.1
      · split at ok
        · cases ok
        · simp only [Except.ok.injEq] at ok
          subst ok
          intro post member
          exact .inl (stateShape _ post member)

/-- A state write's post is the next version of the object's state, at its state cell. -/
theorem stateWrite_post {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {object : CellId} {current : Option ObjectState} {viewed : Bool} {write : Data} {written : StateWritten}
    (ok : stateWrite config snapshot object current viewed write = .ok (some written)) :
    written.post = postAt snapshot (stateCell config.domain object) (stateImage object written.after) := by
  obtain ⟨_, _, _, _, exact⟩ := stateWrite_spec ok
  subst exact; rfl

/-- The posts of a segment's yield commit: its judged state write, or a fresh slot. -/
theorem segmentCommit_posts_ok {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height : Nat} {transaction : TransactionId} {cell object : CellId} {generation : Nat}
    {current : Option ObjectState} {viewed : Bool} {segment : Segment} {yielded : Option YieldCommit}
    (ok : segmentCommit config snapshot height transaction cell object generation current viewed segment = .ok yielded)
    (read : ∃ c, readState config snapshot object = .ok c)
    (judged : ∀ written, yielded.bind YieldCommit.written = some written → StateJudged config snapshot object written.after) :
    ∀ post ∈ (yielded.map YieldCommit.posts).getD [], StatePostOk config snapshot post := by
  intro post member
  cases yielded with
  | none => simp at member
  | some committed =>
    simp only [Option.map_some, Option.getD_some] at member
    obtain ⟨_, _, _, commitOk⟩ := segmentCommit_spec ok
    rcases commitYield_posts_shape commitOk post member with ⟨written, isWritten, isPost⟩ | ⟨fresh, slot⟩
    · have wrote := (commitYield_spec commitOk).1
      rw [isWritten] at wrote
      rw [isPost, stateWrite_post wrote]
      obtain ⟨c, readOk⟩ := read
      exact .inr ⟨object, written.after, rfl, ⟨c, readOk⟩, judged written (by simp [isWritten])⟩
    · exact .inl ⟨.slot, by decide, by decide, by decide, by decide, ⟨fun p found => (by rw [fresh] at found; cases found), slot⟩⟩

/-- The drained judgment of a turn's write makes its state post judged. -/
theorem drained_stateJudged {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {object : CellId} {held : ObjectRecord} (read : readObject config snapshot object = .ok (some held))
    {written : Option StateWritten} (drained : judgeDrained config snapshot held object written = .ok ()) :
    ∀ one, written = some one → StateJudged config snapshot object one.after := by
  intro one isOne record next deadline readAgain draining
  rw [read] at readAgain
  cases readAgain
  subst isOne
  obtain ⟨migrated, judged⟩ := judgeDrained_draining draining drained
  exact judgeMigrated_iff.mp ⟨migrated, judged⟩

#assert_axioms commitYield_posts_shape
#assert_axioms stateWrite_post
#assert_axioms segmentCommit_posts_ok
#assert_axioms drained_stateJudged

/-! ## Deliveries -/

/-- States after posts that are kinded of another role or judged state posts. -/
theorem states_migratable {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {posts : List Post}
    (each : ∀ p ∈ posts, (∃ role, role ≠ .state ∧ Kinded snapshot role p) ∨
      ∃ object state, p = postAt snapshot (stateCell config.domain object) (stateImage object state) ∧
        StateJudged config snapshot object state)
    (objects : ∀ object, objectView object (payloads (afterPosts snapshot posts) (objectCell config.domain object)) =
      objectView object (payloads snapshot.canonicalBytes (objectCell config.domain object)))
    (packages : ∀ pin, packageView (payloads (afterPosts snapshot posts) (packageCell config.domain pin)) =
      packageView (payloads snapshot.canonicalBytes (packageCell config.domain pin)))
    (holds : MigratableStates config (payloads snapshot.canonicalBytes)) :
    MigratableStates config (payloads (afterPosts snapshot posts)) := by
  intro object record next deadline state held draining stated
  rw [packages]
  have heldBefore : objectView object (payloads snapshot.canonicalBytes (objectCell config.domain object)) = some record := by
    rw [← objects]; exact held
  rcases payloads_after snapshot posts (stateCell config.domain object) with ⟨same, _⟩ | ⟨p, member, at_, after⟩
  · exact holds object record next deadline state heldBefore draining (by rw [← same]; exact stated)
  · rw [after] at stated
    rcases each p member with ⟨role, st, k⟩ | ⟨object', state', isState, judged⟩
    · rw [stateView_of_role st k.2] at stated; cases stated
    · subst isState
      simp only [postAt] at stated at_
      rw [stateView_stateImage] at stated
      split at stated
      · rename_i same
        cases stated
        subst same
        have migr := judged record next deadline (objectView_readObject heldBefore) draining
        rw [packageBytes_view] at migr
        exact migr
      · cases stated

theorem statePostOk_each {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes} {post : Post}
    (ok : StatePostOk config snapshot post) :
    (∃ role, role ≠ .state ∧ Kinded snapshot role post) ∨
      ∃ object state, post = postAt snapshot (stateCell config.domain object) (stateImage object state) ∧
        StateJudged config snapshot object state := by
  rcases ok with ⟨role, _, _, st, _, k⟩ | ⟨object, state, isState, _, judged⟩
  · exact .inl ⟨role, st, k⟩
  · exact .inr ⟨object, state, isState, judged⟩

/-- **A turn that rewrites one awaiting record in place** (same object, pin, activity, still
awaiting) at the head of its posts, the rest quiet or judged state posts, keeps both invariants. -/
theorem yield_upgradable {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {posts rest : List Post} {cell : CellId} {old new : Record}
    (postsIs : posts = postAt snapshot cell (recordImage new) :: rest)
    (recordExact : readRecord snapshot cell = some old)
    (located : cell = recordCell config.domain old.object old.activity)
    (oldAwaits : old.phase.awaits = true) (newAwaits : new.phase.awaits = true)
    (sameKey : recordKey' new = recordKey' old)
    (restOk : ∀ p ∈ rest, StatePostOk config snapshot p)
    (holds : Upgradable config (payloads snapshot.canonicalBytes)) :
    Upgradable config (payloads (afterPosts snapshot posts)) := by
  have headKinded : Kinded snapshot .record (postAt snapshot cell (recordImage new)) :=
    ⟨readRecord_role recordExact, recordImage_role _⟩
  have kinded : ∀ p ∈ posts, ∃ role, role ≠ .object ∧ role ≠ .package ∧ Kinded snapshot role p := by
    rw [postsIs]
    intro p member
    rcases List.mem_cons.mp member with isHead | inRest
    · subst isHead; exact ⟨.record, by decide, by decide, headKinded⟩
    · obtain ⟨role, _, o, pk, k⟩ := statePostOk_kinded (restOk p inRest)
      exact ⟨role, o, pk, k⟩
  have objects := fun object => objectView_after_kinded snapshot posts object (objectCell config.domain object)
    (fun p member _ => by obtain ⟨role, o, _, k⟩ := kinded p member; exact ⟨role, o, k⟩)
  have packages := fun pin => packageView_after_kinded snapshot posts (packageCell config.domain pin)
    (fun p member _ => by obtain ⟨role, _, pk, k⟩ := kinded p member; exact ⟨role, pk, k⟩)
  have keysNew : new.object = old.object ∧ new.pin = old.pin ∧ new.activity = old.activity := by
    simpa [recordKey'] using sameKey
  have awaiting : ∀ c, (awaitingView config (payloads (afterPosts snapshot posts)) c).map recordKey' =
      (awaitingView config (payloads snapshot.canonicalBytes) c).map recordKey' := by
    intro c
    by_cases at_ : c = cell
    · subst at_
      rw [awaiting_readRecord config snapshot recordExact located,
        awaiting_recordImage config _ c new (by rw [postsIs]; exact head_payload_at snapshot c _ rest)
          (by rw [keysNew.1, keysNew.2.2]; exact located)]
      simp [oldAwaits, newAwaits, sameKey]
    · rw [awaiting_after_kinded config snapshot posts c (fun p member pat => by
        rw [postsIs] at member
        rcases List.mem_cons.mp member with isHead | inRest
        · subst isHead; exact absurd pat.symm at_
        · obtain ⟨role, r, _, _, k⟩ := statePostOk_kinded (restOk p inRest); exact ⟨role, r, k⟩)]
  obtain ⟨⟨cells, census⟩, migratable⟩ := holds
  refine ⟨⟨cells, census_keys awaiting objects census⟩, states_migratable ?_ objects packages migratable⟩
  rw [postsIs]
  intro p member
  rcases List.mem_cons.mp member with isHead | inRest
  · subst isHead; exact .inl ⟨.record, by decide, headKinded⟩
  · exact statePostOk_each (restOk p inRest)

/-- A settlement's posts reclaim slots it read. -/
theorem settle_silent {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height : Nat} {cell : CellId} {await : Await} {settlement : Settlement}
    (settled : settle config snapshot height cell await = .ok settlement) :
    ∀ post ∈ settlement.posts, Silent snapshot post := by
  unfold settle at settled
  split at settled
  · rename_i name _ _
    cases read : readSlot config snapshot name with
    | none => simp [read] at settled
    | some slot =>
      have vacate : ∀ post ∈ [slotRetire config snapshot name], Silent snapshot post := by
        intro post member
        simp only [List.mem_singleton] at member
        subst member
        refine ⟨.slot, by decide, by decide, by decide, by decide, readSlot_role read, ?_⟩
        intro p found
        rw [show (slotRetire config snapshot name).bytes = retiredImage from rfl, payloadOf_retired] at found
        cases found
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

theorem Delivery.upgradable {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height : Nat} {request : DeliverRequest} (delivery : Delivery config snapshot height request)
    (holds : Upgradable config (payloads snapshot.canonicalBytes)) :
    Upgradable config (payloads (afterPosts snapshot delivery.posts)) := by
  have oldAwaits : delivery.record.phase.awaits = true := by rw [delivery.awaiting]; rfl
  have names := nextRecord_names delivery.record (delivery.record.generation + 1) delivery.segment delivery.yielded
  have pinKept := ObjectiveCheckpointInvariant.nextRecord_pin delivery.record (delivery.record.generation + 1)
    delivery.segment delivery.yielded
  have judgedWrites := drained_stateJudged delivery.objectExact delivery.drained
  have yieldOk := segmentCommit_posts_ok (resumedSegment_commit delivery.endExact) ⟨_, delivery.viewExact⟩ judgedWrites
  by_cases newAwaits : delivery.next.phase.awaits = true
  · apply yield_upgradable (rest := delivery.settlement.posts ++ (delivery.yielded.map YieldCommit.posts).getD [] ++
        [delivery.posted.write config snapshot]) (old := delivery.record) (new := delivery.next)
        (cell := request.record) _ delivery.recordExact delivery.located oldAwaits newAwaits _ _ holds
    · rw [delivery.postsExact]
      simp [countPosts, newAwaits, recordPost]
    · rw [delivery.nextExact]; simp [recordKey', names.1, names.2, pinKept]
    · intro p member
      rcases List.mem_append.mp member with front | isBook
      · rcases List.mem_append.mp front with inSettle | inYield
        · exact .inl (settle_silent delivery.settled p inSettle)
        · exact yieldOk p inYield
      · simp only [List.mem_singleton] at isBook
        subst isBook
        exact .inl (book_silent delivery.bookExact delivery.posted)
  · have yieldedNone : delivery.yielded = none := by
      cases found : delivery.yielded with
      | none => rfl
      | some committed =>
        exfalso
        have commit := resumedSegment_commit delivery.endExact
        rw [found] at commit
        obtain ⟨state, plan, isYield, _⟩ := segmentCommit_spec commit
        apply newAwaits
        rw [delivery.nextExact, isYield, found]
        rfl
    have ended : ∀ await, delivery.next.phase ≠ .awaiting await := by
      intro await isAwaiting
      rw [isAwaiting] at newAwaits
      exact newAwaits rfl
    apply ending_upgradable (slotPosts := delivery.settlement.posts) (bookPost := delivery.posted.write config snapshot)
      delivery.recordExact delivery.located oldAwaits delivery.objectExact (settle_silent delivery.settled)
      (book_silent delivery.bookExact delivery.posted) _ holds
    rw [delivery.postsExact, yieldedNone]
    have notAwaits : delivery.next.phase.awaits = false := by simpa using newAwaits
    simp [countPosts, notAwaits, recount, recordPost, recordImage_ended _ ended]

#assert_axioms states_migratable
#assert_axioms statePostOk_each
#assert_axioms yield_upgradable
#assert_axioms settle_silent
#assert_axioms Delivery.upgradable

/-! ## One object's counters and its judged state writes -/

/-- **Migratable states after a turn that rewrites one object record's counters and writes
judged states.** -/
theorem migratable_counter_states {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {posts : List Post} {objectId : CellId} {object posted : ObjectRecord}
    (holds : MigratableStates config (payloads snapshot.canonicalBytes))
    (held : objectView objectId (payloads snapshot.canonicalBytes (objectCell config.domain objectId)) = some object)
    (objects : ∀ other, objectView other (payloads (afterPosts snapshot posts) (objectCell config.domain other)) =
      if other = objectId then some posted
      else objectView other (payloads snapshot.canonicalBytes (objectCell config.domain other)))
    (draining : ∀ next deadline, posted.phase = .draining next deadline →
      ∃ old live, object.phase = .draining old deadline ∧ next = { old with live := live })
    (each : ∀ p ∈ posts, (∃ role, role ≠ .state ∧ Kinded snapshot role p) ∨
      ∃ object state, p = postAt snapshot (stateCell config.domain object) (stateImage object state) ∧
        StateJudged config snapshot object state)
    (packages : ∀ pin, packageView (payloads (afterPosts snapshot posts) (packageCell config.domain pin)) =
      packageView (payloads snapshot.canonicalBytes (packageCell config.domain pin))) :
    MigratableStates config (payloads (afterPosts snapshot posts)) := by
  intro other record next deadline state found phase stated
  rw [packages]
  -- the record and the pending upgrade the other object had before
  have before : ∃ prior old live, objectView other (payloads snapshot.canonicalBytes (objectCell config.domain other)) =
      some prior ∧ prior.phase = .draining old deadline ∧ next = { old with live := live } := by
    rw [objects] at found
    split at found
    · rename_i same
      subst same
      cases found
      obtain ⟨old, live, oldPhase, nextIs⟩ := draining next deadline phase
      exact ⟨object, old, live, held, oldPhase, nextIs⟩
    · exact ⟨record, next, next.live, found, phase, rfl⟩
  obtain ⟨prior, old, live, priorHeld, priorPhase, nextIs⟩ := before
  subst nextIs
  apply migratable_record config _ prior record other old live state.value
  rcases payloads_after snapshot posts (stateCell config.domain other) with ⟨same, _⟩ | ⟨p, member, at_, after⟩
  · exact holds other prior old deadline state priorHeld priorPhase (by rw [← same]; exact stated)
  · rw [after] at stated
    rcases each p member with ⟨role, st, k⟩ | ⟨object', state', isState, judged⟩
    · rw [stateView_of_role st k.2] at stated; cases stated
    · subst isState
      simp only [postAt] at stated at_
      rw [stateView_stateImage] at stated
      split at stated
      · rename_i same
        cases stated
        subst same
        have migr := judged prior old deadline (objectView_readObject priorHeld) priorPhase
        rw [packageBytes_view] at migr
        exact migr
      · cases stated

#assert_axioms migratable_counter_states

/-! ## Births -/

theorem recount_birth_count (record : ObjectRecord) (pin activity : Digest) (awaits : Bool) (c : LiveClass) :
    (recount record pin activity false awaits).count c =
      record.count c + (if awaits = true ∧ c = record.classOf pin activity then 1 else 0) := by
  cases awaits with
  | false => simp [recount]
  | true =>
    simp only [recount, Bool.not_false, Bool.and_self, if_true]
    rw [ObjectRecord.retain_count]
    by_cases cls : c = record.classOf pin activity <;> simp [cls]

/-- **A turn that starts one activity at a fresh record cell** (awaiting or already ended),
whose other posts are a yield's judged state write and fresh slot, the Book, and the object
record with the activity retained, keeps both invariants. -/
theorem starting_upgradable {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {posts rest : List Post} {cell : CellId} {record : Record} {object : ObjectRecord} {bookPost : Post}
    (fresh : payloadOf (snapshot.canonicalBytes cell) = none)
    (located : cell = recordCell config.domain record.object record.activity)
    (objectExact : readObject config snapshot record.object = .ok (some object))
    (restOk : ∀ p ∈ rest, StatePostOk config snapshot p) (bookSilent : Silent snapshot bookPost)
    (postsIs : posts = postAt snapshot cell (recordImage record) :: (rest ++ [bookPost] ++
      objectPost config snapshot record.object object
        (recount object record.pin record.activity false record.phase.awaits)))
    (holds : Upgradable config (payloads snapshot.canonicalBytes)) :
    Upgradable config (payloads (afterPosts snapshot posts)) := by
  set posted := recount object record.pin record.activity false record.phase.awaits with postedIs
  have heldObject := readObject_some objectExact
  have headKinded : Kinded snapshot .record (postAt snapshot cell (recordImage record)) :=
    ⟨fun p found => (by simp only [postAt] at found; rw [fresh] at found; cases found), recordImage_role _⟩
  have objectKinded := object_post_kinded (record := posted) heldObject
  -- every post: the object post, or kinded of another role than `object`
  have classified : ∀ p ∈ posts, p = postAt snapshot (objectCell config.domain record.object)
      (objectImage record.object posted) ∨
      ∃ role, role ≠ .object ∧ role ≠ .package ∧ Kinded snapshot role p := by
    rw [postsIs]
    intro p member
    simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at member
    rcases member with isHead | ((inRest | isBook) | inObject)
    · subst isHead; exact .inr ⟨.record, by decide, by decide, headKinded⟩
    · obtain ⟨role, _, o, pk, k⟩ := statePostOk_kinded (restOk p inRest); exact .inr ⟨role, o, pk, k⟩
    · subst isBook
      obtain ⟨role, _, o, _, pk, k⟩ := bookSilent
      exact .inr ⟨role, o, pk, k⟩
    · exact .inl (mem_objectPost inObject)
  have notObject : ∀ p ∈ posts, p = postAt snapshot (objectCell config.domain record.object)
      (objectImage record.object posted) ∨ ∃ role, role ≠ .object ∧ Kinded snapshot role p := by
    intro p member
    rcases classified p member with isObject | ⟨role, o, _, k⟩
    · exact .inl isObject
    · exact .inr ⟨role, o, k⟩
  have packages := fun pin => packageView_after_kinded snapshot posts (packageCell config.domain pin)
    (fun p member _ => by
      rcases classified p member with isObject | ⟨role, _, pk, k⟩
      · subst isObject; exact ⟨.object, by decide, objectKinded⟩
      · exact ⟨role, pk, k⟩)
  have objects : ∀ other, objectView other (payloads (afterPosts snapshot posts) (objectCell config.domain other)) =
      if other = record.object then some posted
      else objectView other (payloads snapshot.canonicalBytes (objectCell config.domain other)) := by
    by_cases unchanged : posted = object
    · have noObject : ∀ p ∈ posts, ∃ role, role ≠ .object ∧ Kinded snapshot role p := by
        intro p member
        rw [postsIs] at member
        simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at member
        rcases member with isHead | ((inRest | isBook) | inObject)
        · subst isHead; exact ⟨.record, by decide, headKinded⟩
        · obtain ⟨role, _, o, _, k⟩ := statePostOk_kinded (restOk p inRest); exact ⟨role, o, k⟩
        · subst isBook
          obtain ⟨role, _, o, _, _, k⟩ := bookSilent
          exact ⟨role, o, k⟩
        · unfold objectPost at inObject
          rw [if_pos unchanged] at inObject
          cases inObject
      intro other
      rw [objectView_after_kinded snapshot posts other _ (fun p member _ => noObject p member)]
      split
      · rename_i same; subst same; rw [heldObject, unchanged]
      · rfl
    · have member : postAt snapshot (objectCell config.domain record.object) (objectImage record.object posted) ∈ posts := by
        rw [postsIs]
        simp [objectPost, unchanged]
      have effective := object_post_effective config snapshot posts record.object posted object member notObject heldObject
      exact objects_after_one config snapshot posts record.object posted effective notObject
        (fun other differs => objectView_held_other heldObject differs)
  have before : awaitingView config (payloads snapshot.canonicalBytes) cell = none := by
    apply awaitingView_of_recordView
    simp [payloads, fresh, recordView]
  have after : awaitingView config (payloads (afterPosts snapshot posts)) cell =
      if record.phase.awaits then some record else none :=
    awaiting_recordImage config _ cell record (by rw [postsIs]; exact head_payload_at snapshot cell _ _) located
  have elsewhere : ∀ other, other ≠ cell →
      awaitingView config (payloads (afterPosts snapshot posts)) other =
        awaitingView config (payloads snapshot.canonicalBytes) other := by
    intro other differs
    apply awaiting_after_kinded
    intro p member at_
    rw [postsIs] at member
    simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at member
    rcases member with isHead | ((inRest | isBook) | inObject)
    · subst isHead; exact absurd at_.symm (by simpa [postAt] using differs)
    · obtain ⟨role, r, _, _, k⟩ := statePostOk_kinded (restOk p inRest); exact ⟨role, r, k⟩
    · subst isBook
      obtain ⟨role, r, _, _, _, k⟩ := bookSilent
      exact ⟨role, r, k⟩
    · rw [mem_objectPost inObject]; exact ⟨.object, by decide, objectKinded⟩
  obtain ⟨⟨cells, census⟩, migratable⟩ := holds
  have classes : posted.classOf = object.classOf := recount_classOf _ _ _ _ _
  let extra : List CellId := if cell ∈ cells then [] else [cell]
  have nodup : (cells ++ extra).Nodup := by
    by_cases inCells : cell ∈ cells
    · simp [extra, inCells, census.nodup]
    · simp only [extra, inCells, if_false]
      refine List.nodup_append.mpr ⟨census.nodup, List.nodup_singleton _, ?_⟩
      intro a ha b hb same
      simp only [List.mem_singleton] at hb
      exact inCells (by rw [← hb, ← same]; exact ha)
  have cellIn : cell ∈ cells ++ extra := by
    by_cases inCells : cell ∈ cells
    · exact List.mem_append_left _ inCells
    · simp [extra, inCells]
  refine ⟨⟨cells ++ extra, ?_⟩, ?_⟩
  · apply census_step (object := record.object) census nodup
    · intro other activity found
      by_cases at_ : other = cell
      · subst at_; exact cellIn
      · rw [elsewhere other at_] at found
        exact List.mem_append_left _ (census.covers other activity found)
    · intro other activity found
      by_cases at_ : other = cell
      · subst at_
        rw [after] at found
        split at found
        · cases found; rw [objects, if_pos rfl]; exact ⟨_, rfl⟩
        · cases found
      · rw [elsewhere other at_] at found
        obtain ⟨r0, h0⟩ := census.homed other activity found
        rw [objects]
        split
        · exact ⟨_, rfl⟩
        · exact ⟨r0, h0⟩
    · intro other who differs
      by_cases at_ : other = cell
      · subst at_
        rw [after, before]
        split
        · have notMine : record.object ≠ who := fun h => differs h.symm
          simp [Option.filter, notMine]
        · rfl
      · rw [elsewhere other at_]
    · intro other differs; rw [objects, if_neg differs]
    · intro found held c
      rw [objects, if_pos rfl] at held
      cases held
      have counted := census.counted record.object object heldObject c
      rw [recount_birth_count, counted]
      have gy : counts config (payloads (afterPosts snapshot posts)) record.object posted c cell =
          (record.phase.awaits && decide (object.classOf record.pin record.activity = c)) := by
        rw [counts, after]
        cases record.phase.awaits
        · simp
        · simp [classes]
      have fy : counts config (payloads snapshot.canonicalBytes) record.object object c cell = false := by
        simp [counts, before]
      have ind : (if record.phase.awaits = true ∧ c = object.classOf record.pin record.activity then 1 else 0) =
          (if counts config (payloads (afterPosts snapshot posts)) record.object posted c cell = true then 1 else 0) := by
        rw [gy]
        cases record.phase.awaits <;> by_cases cls : c = object.classOf record.pin record.activity <;>
          simp [cls, eq_comm]
      have fsame : ∀ x, x ≠ cell → counts config (payloads snapshot.canonicalBytes) record.object object c x =
          counts config (payloads (afterPosts snapshot posts)) record.object posted c x := by
        intro x differs; unfold counts; rw [elsewhere x differs, classes]
      rw [ind]
      by_cases inCells : cell ∈ cells
      · simp only [extra, inCells, if_true, List.append_nil]
        have change := countP_change_one census.nodup inCells
          (f := counts config (payloads snapshot.canonicalBytes) record.object object c)
          (g := counts config (payloads (afterPosts snapshot posts)) record.object posted c)
          (fun x _ differs => fsame x differs)
        rw [fy] at change
        simp only [Bool.false_eq_true, if_false, Nat.add_zero] at change
        omega
      · simp only [extra, inCells, if_false]
        rw [List.countP_append]
        have restSame : cells.countP (counts config (payloads (afterPosts snapshot posts)) record.object posted c) =
            cells.countP (counts config (payloads snapshot.canonicalBytes) record.object object c) :=
          countP_congr_mem (fun x member => (fsame x (fun h => inCells (h ▸ member))).symm)
        rw [restSame]
        simp only [List.countP_singleton]
  · apply migratable_counter_states migratable heldObject objects
      (fun next deadline phase => recount_draining phase) _ packages
    intro p member
    rcases classified p member with isObject | ⟨role, o, pk, k⟩
    · subst isObject; exact .inl ⟨.object, by decide, objectKinded⟩
    · rw [postsIs] at member
      simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at member
      rcases member with isHead | ((inRest | isBook) | inObject)
      · subst isHead; exact .inl ⟨.record, by decide, headKinded⟩
      · exact statePostOk_each (restOk p inRest)
      · subst isBook
        obtain ⟨role', _, _, st, _, k'⟩ := bookSilent
        exact .inl ⟨role', st, k'⟩
      · rw [mem_objectPost inObject]; exact .inl ⟨.object, by decide, objectKinded⟩

#assert_axioms recount_birth_count
#assert_axioms starting_upgradable

/-- The record a birth installs: on the request's object, as the birth's activity, pinned to
the request's package. -/
theorem Birth.record_names {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height : Nat} {request : BirthRequest} (born : Birth config snapshot height request) :
    born.record.object = request.object ∧
      born.record.activity = activityId request.object (birthTransaction request) ∧
      born.record.pin = request.pin := by
  have names := nextRecord_names
    ⟨request.object, activityId request.object (birthTransaction request), request.pin, dataBytes request.input,
      0, [], checkpointDigest [],
      escrowOf config.tariff request.subject request.escrowAccount request.resume request.timeout,
      0, .faulted "unborn"⟩ 0 born.segment born.yielded
  have pin := ObjectiveCheckpointInvariant.nextRecord_pin
    ⟨request.object, activityId request.object (birthTransaction request), request.pin, dataBytes request.input,
      0, [], checkpointDigest [],
      escrowOf config.tariff request.subject request.escrowAccount request.resume request.timeout,
      0, .faulted "unborn"⟩ 0 born.segment born.yielded
  rw [born.recordExact]
  exact ⟨names.1, names.2, pin⟩

theorem Birth.upgradable {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height : Nat} {request : BirthRequest} (born : Birth config snapshot height request)
    (signed : request.predecessor = none)
    (holds : Upgradable config (payloads snapshot.canonicalBytes)) :
    Upgradable config (payloads (afterPosts snapshot born.posts)) := by
  obtain ⟨isObject, isActivity, isPin⟩ := Birth.record_names born
  apply starting_upgradable (cell := born.cell) (record := born.record) (object := born.object)
    (rest := (born.yielded.map YieldCommit.posts).getD []) (bookPost := born.posted.write config snapshot)
    born.fresh (by rw [born.cellExact, isObject, isActivity]) (by rw [isObject]; exact born.objectExact)
    (segmentCommit_posts_ok born.yieldedExact ⟨_, born.currentExact⟩
      (drained_stateJudged born.objectExact born.drained))
    (book_silent born.bookExact born.posted) _ holds
  rw [born.postsExact]
  simp [birthCount, signed, recordPost, isObject, isActivity, isPin]

#assert_axioms Birth.record_names
#assert_axioms Birth.upgradable

/-! ## Rebirths -/

/-- **One object post, or none when the record is unchanged**: the object reads the posted
record and every other object reads what it read. -/
theorem objects_after_general {rootBytes : Bytes → Digest} (config : Config) (snapshot : Snapshot rootBytes)
    (posts : List Post) (object : CellId) (posted held : ObjectRecord)
    (kinded : ∀ p ∈ posts, p = postAt snapshot (objectCell config.domain object) (objectImage object posted) ∨
      ∃ role, role ≠ .object ∧ Kinded snapshot role p)
    (holds : objectView object (payloads snapshot.canonicalBytes (objectCell config.domain object)) = some held)
    (presentOrSame : postAt snapshot (objectCell config.domain object) (objectImage object posted) ∈ posts ∨
      posted = held) :
    ∀ other, objectView other (payloads (afterPosts snapshot posts) (objectCell config.domain other)) =
      if other = object then some posted
      else objectView other (payloads snapshot.canonicalBytes (objectCell config.domain other)) := by
  obtain ⟨payload, present, role⟩ := objectView_role holds
  intro other
  by_cases same : other = object
  · subst same
    rw [if_pos rfl]
    rcases payloads_after snapshot posts (objectCell config.domain other) with ⟨kept, none_⟩ | ⟨p, member, at_, after⟩
    · rcases presentOrSame with isIn | isSame
      · exact absurd (show (postAt snapshot (objectCell config.domain other) (objectImage other posted)).cell =
          objectCell config.domain other from rfl) (none_ _ isIn)
      · rw [kept, holds, isSame]
    · rw [after]
      rcases kinded p member with isObject | ⟨r, o, pre, _⟩
      · subst isObject; simp only [postAt]; rw [objectView_objectImage]; simp
      · exfalso
        have := pre payload (by rw [at_]; exact present)
        rw [role] at this
        exact o this.symm
  · rw [if_neg same]
    rcases payloads_after snapshot posts (objectCell config.domain other) with ⟨kept, _⟩ | ⟨p, member, at_, after⟩
    · rw [kept]
    · rw [after]
      rcases kinded p member with isObject | ⟨r, o, pre, post⟩
      · subst isObject
        simp only [postAt] at at_ ⊢
        rw [objectView_objectImage, if_neg same, ← at_]
        exact (objectView_held_other holds same).symm
      · rw [objectView_of_role o post, show payloads snapshot.canonicalBytes (objectCell config.domain other) =
          payloadOf (snapshot.canonicalBytes p.cell) by rw [at_]; rfl, objectView_of_role o pre]

/-- The first post at a cell holding a payload of role `r0` is kinded `r0` (its kind admits what
the cell held). -/
theorem effective_role {rootBytes : Bytes → Digest} {snapshot : Snapshot rootBytes}
    {cell : CellId} {held : Payload} (present : payloadOf (snapshot.canonicalBytes cell) = some held)
    {p : Post} (at_ : p.cell = cell) {role : ObjectiveActivityCell.Role} (kinded : Kinded snapshot role p) :
    role = held.role := by
  have := kinded.1 held (by rw [at_]; exact present)
  exact this.symm

theorem rebirth_count (object : ObjectRecord) (oldPin oldActivity pin activity : Digest) (awaits : Bool)
    (c : LiveClass) :
    (recount (object.release oldPin oldActivity) pin activity false awaits).count c =
      object.count c - (if c = object.classOf oldPin oldActivity then 1 else 0) +
        (if awaits = true ∧ c = object.classOf pin activity then 1 else 0) := by
  rw [recount_birth_count, ObjectRecord.release_count]
  have classes : (object.release oldPin oldActivity).classOf = object.classOf := ObjectRecord.bump_classOf _ _ _
  rw [classes]
  by_cases cls : c = object.classOf oldPin oldActivity <;> simp [cls]

/-- **A turn that ends one awaiting activity at its cell and starts one at a fresh cell** (a
rebirth), releasing the old and retaining the new in the object record it posts, keeps both
invariants. -/
theorem rebirth_upgradable {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {posts rest slotPosts : List Post} {cell oldCell : CellId} {record old : Record} {object : ObjectRecord}
    {bookPost : Post}
    (fresh : payloadOf (snapshot.canonicalBytes cell) = none)
    (located : cell = recordCell config.domain record.object record.activity)
    (oldExact : readRecord snapshot oldCell = some old)
    (oldLocated : oldCell = recordCell config.domain old.object old.activity)
    (oldAwaits : old.phase.awaits = true) (sameObject : old.object = record.object)
    (objectExact : readObject config snapshot record.object = .ok (some object))
    (restOk : ∀ p ∈ rest, StatePostOk config snapshot p) (bookSilent : Silent snapshot bookPost)
    (slotsSilent : ∀ p ∈ slotPosts, Silent snapshot p)
    (postsIs : posts = postAt snapshot cell (recordImage record) :: (rest ++ [bookPost] ++
      objectPost config snapshot record.object object
        (recount (object.release old.pin old.activity) record.pin record.activity false record.phase.awaits)) ++
      (postAt snapshot oldCell retiredImage :: slotPosts))
    (holds : Upgradable config (payloads snapshot.canonicalBytes)) :
    Upgradable config (payloads (afterPosts snapshot posts)) := by
  set posted := recount (object.release old.pin old.activity) record.pin record.activity false record.phase.awaits
    with postedIs
  have heldObject := readObject_some objectExact
  have headKinded : Kinded snapshot .record (postAt snapshot cell (recordImage record)) :=
    ⟨fun p found => (by simp only [postAt] at found; rw [fresh] at found; cases found), recordImage_role _⟩
  have retireKinded : Kinded snapshot .record (postAt snapshot oldCell retiredImage) :=
    ⟨readRecord_role oldExact, fun p found => by
      rw [show (postAt snapshot oldCell retiredImage).bytes = retiredImage from rfl, payloadOf_retired] at found
      cases found⟩
  have objectKinded := object_post_kinded (record := posted) heldObject
  -- the old cell holds a record payload
  obtain ⟨oldPayload, oldPresent, oldRole⟩ : ∃ p, payloadOf (snapshot.canonicalBytes oldCell) = some p ∧
      p.role = .record := by
    cases found : payloadOf (snapshot.canonicalBytes oldCell) with
    | none => simp [readRecord, bodyOf, found] at oldExact
    | some p => exact ⟨p, rfl, readRecord_role oldExact p found⟩
  have cellsDiffer : cell ≠ oldCell := by
    intro same; rw [same, oldPresent] at fresh; cases fresh
  /- every post, by its role -/
  have classify : ∀ p ∈ posts, p = postAt snapshot cell (recordImage record) ∨
      p = postAt snapshot oldCell retiredImage ∨
      p = postAt snapshot (objectCell config.domain record.object) (objectImage record.object posted) ∨
      StatePostOk config snapshot p := by
    rw [postsIs]
    intro p member
    simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at member
    rcases member with (isHead | ((inRest | isBook) | inObject)) | (isRetire | inSlot)
    · exact .inl isHead
    · exact .inr (.inr (.inr (restOk p inRest)))
    · subst isBook; exact .inr (.inr (.inr (.inl bookSilent)))
    · exact .inr (.inr (.inl (mem_objectPost inObject)))
    · exact .inr (.inl isRetire)
    · exact .inr (.inr (.inr (.inl (slotsSilent p inSlot))))
  have kindedAll : ∀ p ∈ posts, ∃ role, role ≠ .package ∧ Kinded snapshot role p ∧
      (role = .record → p = postAt snapshot cell (recordImage record) ∨ p = postAt snapshot oldCell retiredImage) ∧
      (role = .object → p = postAt snapshot (objectCell config.domain record.object) (objectImage record.object posted)) := by
    intro p member
    rcases classify p member with isHead | isRetire | isObject | ok
    · subst isHead; exact ⟨.record, by decide, headKinded, (fun _ => .inl rfl), (fun h => by cases h)⟩
    · subst isRetire; exact ⟨.record, by decide, retireKinded, (fun _ => .inr rfl), (fun h => by cases h)⟩
    · subst isObject; exact ⟨.object, by decide, objectKinded, (fun h => by cases h), (fun _ => rfl)⟩
    · obtain ⟨role, r, o, pk, k⟩ := statePostOk_kinded ok
      exact ⟨role, pk, k, fun h => absurd h r, fun h => absurd h o⟩
  have notObject : ∀ p ∈ posts, p = postAt snapshot (objectCell config.domain record.object)
      (objectImage record.object posted) ∨ ∃ role, role ≠ .object ∧ Kinded snapshot role p := by
    intro p member
    obtain ⟨role, _, k, _, isObj⟩ := kindedAll p member
    by_cases o : role = .object
    · exact .inl (isObj o)
    · exact .inr ⟨role, o, k⟩
  have packages := fun pin => packageView_after_kinded snapshot posts (packageCell config.domain pin)
    (fun p member _ => by obtain ⟨role, pk, k, _, _⟩ := kindedAll p member; exact ⟨role, pk, k⟩)
  have objects := objects_after_general config snapshot posts record.object posted object notObject heldObject
    (by
      by_cases unchanged : posted = object
      · exact .inr unchanged
      · left; rw [postsIs]; simp [objectPost, unchanged])
  have newAfter : awaitingView config (payloads (afterPosts snapshot posts)) cell =
      if record.phase.awaits then some record else none :=
    awaiting_recordImage config _ cell record (by rw [postsIs]; exact head_payload_at snapshot cell _ _) located
  have newBefore : awaitingView config (payloads snapshot.canonicalBytes) cell = none := by
    apply awaitingView_of_recordView
    simp [payloads, fresh, recordView]
  have oldBefore := awaiting_readRecord config snapshot oldExact oldLocated
  rw [oldAwaits, if_pos rfl] at oldBefore
  have oldAfter : awaitingView config (payloads (afterPosts snapshot posts)) oldCell = none := by
    apply awaitingView_of_recordView
    rcases payloads_after snapshot posts oldCell with ⟨_, none_⟩ | ⟨p, member, at_, after⟩
    · exfalso
      exact none_ (postAt snapshot oldCell retiredImage) (by rw [postsIs]; simp) rfl
    · rw [after]
      obtain ⟨role, _, k, isRecord, _⟩ := kindedAll p member
      have roleIs := effective_role oldPresent at_ k
      rw [oldRole] at roleIs
      rcases isRecord roleIs with isHead | isRetire
      · subst isHead; exact absurd at_ (by simpa [postAt] using cellsDiffer)
      · subst isRetire; simp [recordView, postAt, payloadOf_retired]
  have elsewhere : ∀ other, other ≠ cell → other ≠ oldCell →
      awaitingView config (payloads (afterPosts snapshot posts)) other =
        awaitingView config (payloads snapshot.canonicalBytes) other := by
    intro other notNew notOld
    apply awaiting_after_kinded
    intro p member at_
    obtain ⟨role, _, k, isRecord, _⟩ := kindedAll p member
    by_cases r : role = .record
    · rcases isRecord r with isHead | isRetire
      · subst isHead; exact absurd at_.symm (by simpa [postAt] using notNew)
      · subst isRetire; exact absurd at_.symm (by simpa [postAt] using notOld)
    · exact ⟨role, r, k⟩
  obtain ⟨⟨cells, census⟩, migratable⟩ := holds
  have classes : posted.classOf = object.classOf := by
    rw [postedIs, recount_classOf]; exact ObjectRecord.bump_classOf _ _ _
  have oldIn := census.covers oldCell old oldBefore
  let extra : List CellId := if cell ∈ cells then [] else [cell]
  have nodup : (cells ++ extra).Nodup := by
    by_cases inCells : cell ∈ cells
    · simp [extra, inCells, census.nodup]
    · simp only [extra, inCells, if_false]
      refine List.nodup_append.mpr ⟨census.nodup, List.nodup_singleton _, ?_⟩
      intro a ha b hb same
      simp only [List.mem_singleton] at hb
      exact inCells (by rw [← hb, ← same]; exact ha)
  have awaitingSame : ∀ other activity, awaitingView config (payloads (afterPosts snapshot posts)) other = some activity →
      other = cell ∨ awaitingView config (payloads snapshot.canonicalBytes) other = some activity := by
    intro other activity found
    by_cases n : other = cell
    · exact .inl n
    · by_cases o : other = oldCell
      · subst o; rw [oldAfter] at found; cases found
      · rw [elsewhere other n o] at found; exact .inr found
  refine ⟨⟨cells ++ extra, ?_⟩, ?_⟩
  · apply census_step (object := record.object) census nodup
    · intro other activity found
      rcases awaitingSame other activity found with n | f
      · subst n
        by_cases inCells : other ∈ cells
        · exact List.mem_append_left _ inCells
        · simp [extra, inCells]
      · exact List.mem_append_left _ (census.covers other activity f)
    · intro other activity found
      rcases awaitingSame other activity found with n | f
      · subst n
        rw [newAfter] at found
        split at found
        · cases found; rw [objects, if_pos rfl]; exact ⟨_, rfl⟩
        · cases found
      · obtain ⟨r0, h0⟩ := census.homed other activity f
        rw [objects]
        split
        · exact ⟨_, rfl⟩
        · exact ⟨r0, h0⟩
    · intro other who differs
      have notMine : record.object ≠ who := fun h => differs h.symm
      by_cases n : other = cell
      · subst n
        rw [newAfter, newBefore]
        split
        · simp [Option.filter, notMine]
        · rfl
      · by_cases o : other = oldCell
        · subst o
          rw [oldAfter, oldBefore]
          simp [Option.filter, sameObject, notMine]
        · rw [elsewhere other n o]
    · intro other differs; rw [objects, if_neg differs]
    · intro found held c
      rw [objects, if_pos rfl] at held
      cases held
      have counted := census.counted record.object object heldObject c
      rw [postedIs, rebirth_count, counted]
      -- the census predicates before (under `object`) and after (under `posted`)
      set f := counts config (payloads snapshot.canonicalBytes) record.object object c with fIs
      set g := counts config (payloads (afterPosts snapshot posts)) record.object posted c with gIs
      have fOld : f oldCell = decide (object.classOf old.pin old.activity = c) := by
        simp [fIs, counts, oldBefore, sameObject]
      have gOld : g oldCell = false := by simp [gIs, counts, oldAfter]
      have fNew : f cell = false := by simp [fIs, counts, newBefore]
      have gNew : g cell = (record.phase.awaits && decide (object.classOf record.pin record.activity = c)) := by
        rw [gIs, counts, newAfter]
        cases record.phase.awaits
        · simp
        · simp [classes]
      have fg : ∀ x, x ≠ cell → x ≠ oldCell → f x = g x := by
        intro x n o; rw [fIs, gIs]; unfold counts; rw [elsewhere x n o, classes]
      -- step 1: from f to h, which is g at the old cell
      let h : CellId → Bool := fun x => if x = oldCell then false else f x
      have step1 := countP_change_one census.nodup oldIn (f := f) (g := h)
        (fun x _ differs => by simp [h, differs])
      have hOld : h oldCell = false := by simp [h]
      rw [hOld, fOld] at step1
      simp only [Bool.false_eq_true, if_false, Nat.add_zero] at step1
      have indOld : (if c = object.classOf old.pin old.activity then 1 else 0) =
          (if decide (object.classOf old.pin old.activity = c) = true then 1 else 0) := by
        by_cases cls : c = object.classOf old.pin old.activity <;> simp [cls, eq_comm]
      have indNew : (if record.phase.awaits = true ∧ c = object.classOf record.pin record.activity then 1 else 0) =
          (if g cell = true then 1 else 0) := by
        rw [gNew]
        cases record.phase.awaits <;> by_cases cls : c = object.classOf record.pin record.activity <;>
          simp [cls, eq_comm]
      rw [indOld, indNew]
      have hg : ∀ x, x ≠ cell → h x = g x := by
        intro x n
        by_cases o : x = oldCell
        · simp [h, o, ← gOld]
        · simp only [h, o, if_false]; exact fg x n o
      by_cases inCells : cell ∈ cells
      · simp only [extra, inCells, if_true, List.append_nil]
        have step2 := countP_change_one census.nodup inCells (f := h) (g := g) (fun x _ n => hg x n)
        have hNew : h cell = false := by simp [h, cellsDiffer, fNew]
        rw [hNew] at step2
        simp only [Bool.false_eq_true, if_false, Nat.add_zero] at step2
        omega
      · simp only [extra, inCells, if_false]
        rw [List.countP_append]
        have restSame : cells.countP g = cells.countP h :=
          countP_congr_mem (fun x member => (hg x (fun e => inCells (e ▸ member))).symm)
        rw [restSame]
        simp only [List.countP_singleton]
        omega
  · apply migratable_counter_states migratable heldObject objects
      (fun next deadline phase => by
        obtain ⟨mid, live, midPhase, nextIs⟩ := recount_draining phase
        obtain ⟨old', live', oldPhase, midIs⟩ := bump_draining midPhase
        subst nextIs; subst midIs
        exact ⟨old', live, oldPhase, rfl⟩) _ packages
    intro p member
    rcases classify p member with isHead | isRetire | isObject | ok
    · subst isHead; exact .inl ⟨.record, by decide, headKinded⟩
    · subst isRetire; exact .inl ⟨.record, by decide, retireKinded⟩
    · subst isObject; exact .inl ⟨.object, by decide, objectKinded⟩
    · exact statePostOk_each ok

#assert_axioms objects_after_general
#assert_axioms effective_role
#assert_axioms rebirth_count
#assert_axioms rebirth_upgradable

theorem Rebirth.upgradable {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height : Nat} {request : RebirthRequest} (reborn : Rebirth config snapshot height request)
    (holds : Upgradable config (payloads snapshot.canonicalBytes)) :
    Upgradable config (payloads (afterPosts snapshot reborn.posts)) := by
  obtain ⟨isObject, isActivity, isPin⟩ := Birth.record_names reborn.born
  have objectIs : reborn.born.record.object = reborn.old.object := isObject
  apply rebirth_upgradable (cell := reborn.born.cell) (record := reborn.born.record) (old := reborn.old)
    (object := reborn.born.object) (oldCell := request.record)
    (rest := (reborn.born.yielded.map YieldCommit.posts).getD []) (slotPosts := reborn.slotPosts)
    (bookPost := reborn.born.posted.write config snapshot)
    reborn.born.fresh (by rw [reborn.born.cellExact, isObject, isActivity]) reborn.oldExact reborn.located
    (by rw [reborn.awaiting]; rfl) objectIs.symm (by rw [isObject]; exact reborn.born.objectExact)
    (segmentCommit_posts_ok reborn.born.yieldedExact ⟨_, reborn.born.currentExact⟩
      (drained_stateJudged reborn.born.objectExact reborn.born.drained))
    (book_silent reborn.born.bookExact reborn.born.posted) (abandonSlot_silent reborn.slotExact) _ holds
  rw [reborn.postsExact, reborn.born.postsExact]
  simp [birthCount, rebirthRequest, recordPost, isObject, isActivity, isPin]

#assert_axioms Rebirth.upgradable

/-! ## Creation -/

theorem Creation.upgradable {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height : Nat} {request : CreateRequest} (created : Creation config snapshot height request)
    (holds : Upgradable config (payloads snapshot.canonicalBytes)) :
    Upgradable config (payloads (afterPosts snapshot created.posts)) := by
  have absent : payloads snapshot.canonicalBytes (objectCell config.domain request.object) = none :=
    readObject_none created.absent
  have headKinded : Kinded snapshot .object
      (postAt snapshot (objectCell config.domain request.object) (objectImage request.object (request.record created.laws))) :=
    ⟨fun p found => (by simp only [postAt] at found; rw [show payloadOf (snapshot.canonicalBytes
      (objectCell config.domain request.object)) = none from absent] at found; cases found), payloadOf_image_role _ _ _⟩
  have seedShape : ∀ p ∈ (request.seed.map (seedPost config snapshot request)).toList,
      ∃ seed, request.seed = some seed ∧ p = seedPost config snapshot request seed := by
    intro p member
    cases seeded : request.seed with
    | none => rw [seeded] at member; cases member
    | some seed =>
      rw [seeded] at member
      simp only [Option.map_some, Option.toList_some, List.mem_singleton] at member
      exact ⟨seed, rfl, member⟩
  have seedKinded : ∀ p ∈ (request.seed.map (seedPost config snapshot request)).toList, Kinded snapshot .state p := by
    intro p member
    obtain ⟨seed, seeded, isSeed⟩ := seedShape p member
    subst isSeed
    exact ⟨readState_role (created.stateFresh seed seeded), payloadOf_image_role _ _ _⟩
  have kinded : ∀ p ∈ created.posts, p = postAt snapshot (objectCell config.domain request.object)
      (objectImage request.object (request.record created.laws)) ∨ ∃ role, role ≠ .object ∧ Kinded snapshot role p := by
    rw [created.postsExact]
    intro p member
    rcases List.mem_cons.mp member with isHead | inSeed
    · exact .inl isHead
    · exact .inr ⟨.state, by decide, seedKinded p inSeed⟩
  have effective : payloads (afterPosts snapshot created.posts) (objectCell config.domain request.object) =
      payloadOf (objectImage request.object (request.record created.laws)) := by
    rw [created.postsExact]; exact head_payload_at snapshot _ _ _
  have objects := objects_after_one config snapshot created.posts request.object (request.record created.laws) effective kinded
    (fun other _ => by rw [absent]; rfl)
  have notRecord : ∀ p ∈ created.posts, ∃ role, role ≠ .record ∧ role ≠ .package ∧ Kinded snapshot role p := by
    intro p member
    rcases kinded p member with isHead | ⟨role, _, k⟩
    · subst isHead; exact ⟨.object, by decide, by decide, headKinded⟩
    · rw [created.postsExact] at member
      rcases List.mem_cons.mp member with isHead | inSeed
      · subst isHead; exact ⟨.object, by decide, by decide, headKinded⟩
      · exact ⟨.state, by decide, by decide, seedKinded p inSeed⟩
  have awaiting := fun cell => awaiting_after_kinded config snapshot created.posts cell (fun p member _ => by
    obtain ⟨role, r, _, k⟩ := notRecord p member; exact ⟨role, r, k⟩)
  have packages := fun pin => packageView_after_kinded snapshot created.posts (packageCell config.domain pin)
    (fun p member _ => by obtain ⟨role, _, pk, k⟩ := notRecord p member; exact ⟨role, pk, k⟩)
  obtain ⟨⟨cells, census⟩, migratable⟩ := holds
  have noneOfMine : ∀ cell activity, awaitingView config (payloads snapshot.canonicalBytes) cell = some activity →
      activity.object ≠ request.object := by
    intro cell activity found same
    obtain ⟨record, held⟩ := census.homed cell activity found
    rw [same, absent] at held
    cases held
  refine ⟨⟨cells, ?_⟩, ?_⟩
  · have nodup : (cells ++ []).Nodup := by rw [List.append_nil]; exact census.nodup
    have step : Census config (payloads (afterPosts snapshot created.posts)) (cells ++ []) := by
      apply census_step (object := request.object) census nodup
      · intro cell activity found
        rw [List.append_nil]; rw [awaiting] at found; exact census.covers cell activity found
      · intro cell activity found
        rw [awaiting] at found
        obtain ⟨r0, h0⟩ := census.homed cell activity found
        rw [objects]
        split
        · exact ⟨_, rfl⟩
        · exact ⟨r0, h0⟩
      · intro cell who _; rw [awaiting]
      · intro other differs; rw [objects, if_neg differs]
      · intro record held c
        rw [objects, if_pos rfl] at held
        cases held
        rw [List.append_nil]
        have zero : cells.countP (counts config (payloads (afterPosts snapshot created.posts)) request.object
            (request.record created.laws) c) = 0 := by
          apply List.countP_eq_zero.mpr
          intro cell _ isCounted
          unfold counts at isCounted
          rw [awaiting] at isCounted
          cases found : awaitingView config (payloads snapshot.canonicalBytes) cell with
          | none => rw [found] at isCounted; cases isCounted
          | some activity =>
            rw [found] at isCounted
            simp only [Bool.and_eq_true, decide_eq_true_eq] at isCounted
            exact noneOfMine cell activity found isCounted.1
        rw [zero]
        cases c <;> rfl
    rw [List.append_nil] at step
    exact step
  · intro other record next deadline state found phase stated
    rw [objects] at found
    split at found
    · cases found; cases phase
    · rw [packages]
      have stateBefore : stateView other (payloads snapshot.canonicalBytes (stateCell config.domain other)) = some state := by
        rcases payloads_after snapshot created.posts (stateCell config.domain other) with ⟨same, _⟩ | ⟨p, member, at_, after⟩
        · rw [← same]; exact stated
        · rw [after] at stated
          rw [created.postsExact] at member
          rcases List.mem_cons.mp member with isHead | inSeed
          · subst isHead
            rw [stateView_of_role (by decide : ObjectiveActivityCell.Role.object ≠ .state) headKinded.2] at stated
            cases stated
          · obtain ⟨seed, _, isSeed⟩ := seedShape p inSeed
            subst isSeed
            simp only [seedPost, postAt] at stated
            rw [stateView_stateImage, if_neg (by assumption)] at stated
            cases stated
      exact migratable other record next deadline state found phase stateBefore

#assert_axioms Creation.upgradable

/-! ## ADOPT: the chosen activities change class -/

theorem awaitingView_located {config : Config} {P : Payloads} {cell : CellId} {r : Record}
    (found : awaitingView config P cell = some r) :
    cell = recordCell config.domain r.object r.activity ∧ r.phase.awaits = true := by
  unfold awaitingView at found
  split at found
  · split at found
    · rename_i h; cases found; exact h
    · cases found
  · cases found

/-- A turn that rewrites one existing object record and no awaiting cell keeps the census
exactly when the new record's counters count the same cells under its own classification. -/
theorem census_reclassify {config : Config} {P Q : Payloads} {cells : List CellId} {object : CellId}
    {new : ObjectRecord} (census : Census config P cells)
    (awaiting : ∀ cell, awaitingView config Q cell = awaitingView config P cell)
    (objects : ∀ other, objectView other (Q (objectCell config.domain other)) =
      if other = object then some new else objectView other (P (objectCell config.domain other)))
    (mine : ∀ c, new.count c = cells.countP (counts config P object new c)) :
    Census config Q cells where
  nodup := census.nodup
  covers := fun cell activity found => census.covers cell activity (by rw [← awaiting]; exact found)
  homed := fun cell activity found => by
    obtain ⟨record, held⟩ := census.homed cell activity (by rw [← awaiting]; exact found)
    rw [objects]
    split
    · exact ⟨new, rfl⟩
    · exact ⟨record, held⟩
  counted := fun other record held c => by
    have same : counts config Q other record c = counts config P other record c := by
      funext cell; unfold counts; rw [awaiting]
    rw [same]
    rw [objects] at held
    split at held
    · rename_i isObject; subst isObject; cases held; exact mine c
    · exact census.counted other record held c

theorem countP_split (l : List CellId) (f g : CellId → Bool) :
    l.countP f = l.countP (fun x => f x && g x) + l.countP (fun x => f x && !g x) := by
  induction l with
  | nil => rfl
  | cons x rest ih =>
    simp only [List.countP_cons]
    rw [ih]
    cases f x <;> cases g x <;> simp <;> omega

/-- Whether a cell holds an awaiting activity of `object` named in `chosen`. -/
def chosenIn (config : Config) (P : Payloads) (object : CellId) (chosen : List Digest) (cell : CellId) : Bool :=
  match awaitingView config P cell with
  | some a => decide (a.object = object) && decide (a.activity ∈ chosen)
  | none => false

/-- **Distinct named activities, each awaiting at its own record cell, are counted once each.**
No coordinate injectivity: the record a cell holds names the activity, so two names never
share a cell. -/
theorem countP_chosen {config : Config} {P : Payloads} {cells : List CellId} {object : CellId}
    (nodup : cells.Nodup)
    (covers : ∀ cell activity, awaitingView config P cell = some activity → cell ∈ cells) :
    ∀ (chosen : List Digest), chosen.Nodup →
      (∀ a ∈ chosen, ∃ r, awaitingView config P (recordCell config.domain object a) = some r ∧
        r.object = object ∧ r.activity = a) →
      cells.countP (chosenIn config P object chosen) = chosen.length
  | [], _, _ => by
    apply List.countP_eq_zero.mpr
    intro cell _ hit
    unfold chosenIn at hit
    split at hit
    · simp at hit
    · cases hit
  | a :: rest, nd, targets => by
    rw [List.nodup_cons] at nd
    have ih := countP_chosen nodup covers rest nd.2 (fun b m => targets b (List.mem_cons_of_mem _ m))
    obtain ⟨r, found, isObject, isActivity⟩ := targets a (List.mem_cons_self ..)
    have member := covers _ r found
    have agree : ∀ x ∈ cells, x ≠ recordCell config.domain object a →
        chosenIn config P object (a :: rest) x = chosenIn config P object rest x := by
      intro x _ differs
      unfold chosenIn
      cases view : awaitingView config P x with
      | none => rfl
      | some b =>
        simp only
        by_cases s : b.object = object
        · have notA : b.activity ≠ a := by
            intro isA
            apply differs
            rw [(awaitingView_located view).1, s, isA]
          simp [s, notA]
        · simp [s]
    have one := countP_change_one nodup member agree
    have atY : chosenIn config P object (a :: rest) (recordCell config.domain object a) = true := by
      simp [chosenIn, found, isObject, isActivity]
    have notY : chosenIn config P object rest (recordCell config.domain object a) = false := by
      simp [chosenIn, found, isObject, isActivity, nd.1]
    rw [atY, notY, ih] at one
    simp only [if_true, if_false, Bool.false_eq_true, List.length_cons] at one ⊢
    omega

theorem rebirthTarget_ok {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {object : CellId} {record : ObjectRecord} {pin activity : Digest}
    (ok : rebirthTarget config snapshot object record pin activity = .ok ()) :
    ∃ target, readRecord snapshot (recordCell config.domain object activity) = some target ∧
      target.object = object ∧ target.activity = activity ∧ target.pin = record.pin ∧
      target.phase.awaits = true := by
  unfold rebirthTarget at ok
  split at ok
  · cases ok
  · rename_i target found
    split at ok
    · rename_i named
      exact ⟨target, found, named.1, named.2.1, named.2.2.1, named.2.2.2⟩
    · cases ok

theorem rebirthTargets_ok {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {object : CellId} {record : ObjectRecord} {pin : Digest} :
    ∀ activities, rebirthTargets config snapshot object record pin activities = .ok () →
      ∀ a ∈ activities, ∃ target, readRecord snapshot (recordCell config.domain object a) = some target ∧
        target.object = object ∧ target.activity = a ∧ target.pin = record.pin ∧ target.phase.awaits = true
  | [], _, a, member => by cases member
  | b :: rest, ok, a, member => by
    simp only [rebirthTargets, bind, Except.bind] at ok
    split at ok
    · cases ok
    · rename_i first
      rcases List.mem_cons.mp member with isB | inRest
      · subst isB; exact rebirthTarget_ok first
      · exact rebirthTargets_ok rest ok a inRest

/-- **ADOPT keeps both invariants.** The record turns draining: the chosen activities (all
awaiting, of this object, on its pin, distinct) move from `live` to `rebirths`; nothing is
pending (no activity was pinned to the next package: steady with no rebirths, every awaiting
activity is on the pin). The state it found migrates under the record it installs. -/
theorem Adoption.upgradable {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height : Nat} {request : AdoptRequest}
    (adopted : Adoption config snapshot height request)
    (holds : Upgradable config (payloads snapshot.canonicalBytes)) :
    Upgradable config (payloads (afterPosts snapshot adopted.posts)) := by
  have heldObject := readObject_some adopted.recordExact
  have headKinded := object_post_kinded
    (record := adoptedRecord adopted.record (request.pending height adopted.laws)
      (height + request.patience)) heldObject
  have bookSilent := book_silent adopted.bookExact adopted.posted
  have kinded : ∀ p ∈ adopted.posts, p = postAt snapshot (objectCell config.domain request.object)
      (objectImage request.object (adoptedRecord adopted.record (request.pending height adopted.laws)
        (height + request.patience))) ∨ ∃ role, role ≠ .object ∧ Kinded snapshot role p := by
    rw [adopted.postsExact]
    intro p member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with isHead | isBook
    · exact .inl isHead
    · subst isBook
      obtain ⟨role, _, o, _, _, k⟩ := bookSilent
      exact .inr ⟨role, o, k⟩
  have quiet : ∀ p ∈ adopted.posts, ∃ role, role ≠ .record ∧ role ≠ .state ∧ role ≠ .package ∧
      Kinded snapshot role p := by
    rw [adopted.postsExact]
    intro p member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with isHead | isBook
    · subst isHead; exact ⟨.object, by decide, by decide, by decide, headKinded⟩
    · subst isBook
      obtain ⟨role, r, _, st, pk, k⟩ := bookSilent
      exact ⟨role, r, st, pk, k⟩
  have effective := object_post_effective config snapshot adopted.posts request.object _ adopted.record
    (by rw [adopted.postsExact]; simp) kinded heldObject
  have objects := objects_after_one config snapshot adopted.posts request.object _ effective kinded
    (fun other differs => objectView_held_other heldObject differs)
  have awaiting := fun cell => awaiting_after_kinded config snapshot adopted.posts cell (fun p member _ => by
    obtain ⟨role, r, _, _, k⟩ := quiet p member; exact ⟨role, r, k⟩)
  have states := fun object => stateView_after_kinded snapshot adopted.posts object (stateCell config.domain object)
    (fun p member _ => by obtain ⟨role, _, st, _, k⟩ := quiet p member; exact ⟨role, st, k⟩)
  have packages := fun pin => packageView_after_kinded snapshot adopted.posts (packageCell config.domain pin)
    (fun p member _ => by obtain ⟨role, _, _, pk, k⟩ := quiet p member; exact ⟨role, pk, k⟩)
  obtain ⟨⟨cells, census⟩, migratable⟩ := holds
  -- Before: steady, no rebirths, so every awaiting activity of the object is on its pin.
  have noRebirth := census.counted request.object adopted.record heldObject .rebirth
  rw [show adopted.record.count .rebirth = 0 from adopted.noRebirths] at noRebirth
  have pinned : ∀ cell ∈ cells, ∀ a, awaitingView config (payloads snapshot.canonicalBytes) cell = some a →
      a.object = request.object → a.pin = adopted.record.pin := by
    intro cell member a view mine
    have zero := (List.countP_eq_zero.mp noRebirth.symm) cell member
    unfold counts at zero
    rw [view] at zero
    by_contra off
    simp [mine, ObjectRecord.classOf, adopted.steady, off] at zero
  have targets : ∀ a ∈ request.rebirth, ∃ r, awaitingView config (payloads snapshot.canonicalBytes)
      (recordCell config.domain request.object a) = some r ∧ r.object = request.object ∧ r.activity = a := by
    intro a member
    obtain ⟨target, read, isObject, isActivity, _, awaits⟩ := rebirthTargets_ok _ adopted.rebirthsChecked a member
    refine ⟨target, ?_, isObject, isActivity⟩
    rw [awaiting_readRecord config snapshot read (by rw [isObject, isActivity]), if_pos awaits]
  have chosen := countP_chosen census.nodup census.covers request.rebirth adopted.nodup targets
  have liveBefore := census.counted request.object adopted.record heldObject .live
  have split := countP_split cells (counts config (payloads snapshot.canonicalBytes) request.object adopted.record .live)
    (chosenIn config (payloads snapshot.canonicalBytes) request.object request.rebirth)
  have distinct : adopted.record.pin ≠ request.pin := fun same => adopted.distinct same.symm
  refine ⟨⟨cells, census_reclassify census awaiting objects ?_⟩, ?_⟩
  · intro c
    cases c with
    | pending =>
      show 0 = _
      symm
      apply List.countP_eq_zero.mpr
      intro cell member hit
      unfold counts at hit
      cases view : awaitingView config (payloads snapshot.canonicalBytes) cell with
      | none => rw [view] at hit; cases hit
      | some a =>
        rw [view] at hit
        by_cases mine : a.object = request.object
        · have pin := pinned cell member a view mine
          simp [mine, pin, ObjectRecord.classOf, adoptedRecord,
            AdoptRequest.pending, distinct] at hit
          split at hit <;> cases hit
        · simp [mine] at hit
    | rebirth =>
      show request.rebirth.length = _
      rw [← chosen]
      apply countP_congr_mem
      intro cell member
      unfold counts chosenIn
      cases view : awaitingView config (payloads snapshot.canonicalBytes) cell with
      | none => rfl
      | some a =>
        by_cases mine : a.object = request.object
        · have pin := pinned cell member a view mine
          by_cases inR : a.activity ∈ request.rebirth <;>
            simp [mine, pin, inR, ObjectRecord.classOf, adoptedRecord,
              AdoptRequest.pending, distinct]
        · simp [mine]
    | live =>
      show adopted.record.live - request.rebirth.length = _
      have both : cells.countP (fun x => counts config (payloads snapshot.canonicalBytes) request.object
          adopted.record .live x && chosenIn config (payloads snapshot.canonicalBytes) request.object
            request.rebirth x) = request.rebirth.length := by
        rw [← chosen]
        apply countP_congr_mem
        intro cell member
        unfold counts chosenIn
        cases view : awaitingView config (payloads snapshot.canonicalBytes) cell with
        | none => rfl
        | some a =>
          by_cases mine : a.object = request.object
          · have pin := pinned cell member a view mine
            simp [mine, pin, ObjectRecord.classOf, adopted.steady]
          · simp [mine]
      have rest : cells.countP (fun x => counts config (payloads snapshot.canonicalBytes) request.object
          adopted.record .live x && !chosenIn config (payloads snapshot.canonicalBytes) request.object
            request.rebirth x) =
          cells.countP (counts config (payloads snapshot.canonicalBytes) request.object
            (adoptedRecord adopted.record (request.pending height adopted.laws)
              (height + request.patience)) .live) := by
        apply countP_congr_mem
        intro cell member
        unfold counts chosenIn
        cases view : awaitingView config (payloads snapshot.canonicalBytes) cell with
        | none => rfl
        | some a =>
          by_cases mine : a.object = request.object
          · have pin := pinned cell member a view mine
            by_cases inR : a.activity ∈ request.rebirth <;>
              simp [mine, pin, inR, ObjectRecord.classOf, adopted.steady, adoptedRecord,
                AdoptRequest.pending, distinct]
          · simp [mine]
      have liveIs : adopted.record.live = adopted.record.count .live := rfl
      rw [liveIs, liveBefore, split, both, rest]
      omega
  · intro other record next deadline state found phase stated
    rw [states] at stated
    rw [objects] at found
    split at found
    · rename_i same
      subst same
      cases found
      simp only [adoptedRecord] at phase
      cases phase
      have current := adopted.currentExact
      rw [stateView_readState stated] at current
      have isCurrent : adopted.current = some state := (Except.ok.inj current).symm
      obtain ⟨migrated, judged⟩ := adopted.migratable isCurrent
      obtain ⟨m, ran, admitted⟩ := judgeMigrated_iff.mp ⟨migrated, judged⟩
      rw [packages, ← packageBytes_view]
      exact ⟨m, ran, by rw [successor_admits _ adopted.record]; exact admitted⟩
    · rw [packages]
      exact migratable other record next deadline state found phase stated

#assert_axioms awaitingView_located
#assert_axioms census_reclassify
#assert_axioms countP_split
#assert_axioms countP_chosen
#assert_axioms rebirthTarget_ok
#assert_axioms rebirthTargets_ok
#assert_axioms Adoption.upgradable

/-! ## MIGRATE: the pending activities become live -/

/-- **MIGRATE keeps both invariants.** The record turns steady on the next pin: the activities
born on it while draining (`pending`) are now `live`, the chosen ones stay `rebirths`, and no
old activity outside them awaits (`live = 0`, by the census). The object is steady, so its
migrated state owes nothing; every other object's views are as they were. -/
theorem Migrated.upgradable {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height : Nat} {request : MigrateRequest} (migrated : Migrated config snapshot height request)
    (holds : Upgradable config (payloads snapshot.canonicalBytes)) :
    Upgradable config (payloads (afterPosts snapshot migrated.posts)) := by
  have heldObject := readObject_some migrated.recordExact
  have headKinded := object_post_kinded (record := migrated.record.successor migrated.next) heldObject
  have bookSilent := book_silent migrated.bookExact migrated.posted
  have stateShape : ∀ p ∈ migratedStatePosts config snapshot request.object migrated.current migrated.migrated,
      ∃ version value, p = postAt snapshot (stateCell config.domain request.object)
        (stateImage request.object ⟨version, value⟩) := by
    intro p member
    unfold migratedStatePosts at member
    split at member
    · simp only [List.mem_singleton] at member; exact ⟨_, _, member⟩
    · cases member
  have stateKinded : ∀ p ∈ migratedStatePosts config snapshot request.object migrated.current migrated.migrated,
      Kinded snapshot .state p := by
    intro p member
    obtain ⟨version, value, isState⟩ := stateShape p member
    subst isState
    exact ⟨readState_role migrated.currentExact, payloadOf_image_role _ _ _⟩
  have kinded : ∀ p ∈ migrated.posts, p = postAt snapshot (objectCell config.domain request.object)
      (objectImage request.object (migrated.record.successor migrated.next)) ∨
      ∃ role, role ≠ .object ∧ role ≠ .record ∧ role ≠ .package ∧ Kinded snapshot role p := by
    rw [migrated.postsExact]
    intro p member
    simp only [List.mem_cons, List.mem_append, List.mem_singleton, List.not_mem_nil, or_false] at member
    rcases member with isHead | inState | isBook
    · exact .inl isHead
    · exact .inr ⟨.state, by decide, by decide, by decide, stateKinded p inState⟩
    · subst isBook
      obtain ⟨role, r, o, _, pk, k⟩ := bookSilent
      exact .inr ⟨role, o, r, pk, k⟩
  have notObject : ∀ p ∈ migrated.posts, p = postAt snapshot (objectCell config.domain request.object)
      (objectImage request.object (migrated.record.successor migrated.next)) ∨
      ∃ role, role ≠ .object ∧ Kinded snapshot role p := by
    intro p member
    rcases kinded p member with isHead | ⟨role, o, _, _, k⟩
    · exact .inl isHead
    · exact .inr ⟨role, o, k⟩
  have quiet : ∀ p ∈ migrated.posts, ∃ role, role ≠ .record ∧ role ≠ .package ∧ Kinded snapshot role p := by
    intro p member
    rcases kinded p member with isHead | ⟨role, _, r, pk, k⟩
    · subst isHead; exact ⟨.object, by decide, by decide, headKinded⟩
    · exact ⟨role, r, pk, k⟩
  have effective := object_post_effective config snapshot migrated.posts request.object _ migrated.record
    (by rw [migrated.postsExact]; simp) notObject heldObject
  have objects := objects_after_one config snapshot migrated.posts request.object _ effective notObject
    (fun other differs => objectView_held_other heldObject differs)
  have awaiting := fun cell => awaiting_after_kinded config snapshot migrated.posts cell (fun p member _ => by
    obtain ⟨role, r, _, k⟩ := quiet p member; exact ⟨role, r, k⟩)
  have packages := fun pin => packageView_after_kinded snapshot migrated.posts (packageCell config.domain pin)
    (fun p member _ => by obtain ⟨role, _, pk, k⟩ := quiet p member; exact ⟨role, pk, k⟩)
  obtain ⟨⟨cells, census⟩, migratable⟩ := holds
  have count := fun c => census.counted request.object migrated.record heldObject c
  have liveZero := count .live
  rw [show migrated.record.count .live = 0 from migrated.drained] at liveZero
  have rebirthsBefore := count .rebirth
  have pendingBefore := count .pending
  have phase := migrated.draining
  refine ⟨⟨cells, census_reclassify census awaiting objects ?_⟩, ?_⟩
  · intro c
    cases c with
    | pending =>
      show 0 = _
      symm
      apply List.countP_eq_zero.mpr
      intro cell _ hit
      unfold counts at hit
      split at hit
      · simp only [ObjectRecord.classOf, ObjectRecord.successor, Bool.and_eq_true, decide_eq_true_eq] at hit
        split at hit <;> simp at hit
      · cases hit
    | live =>
      show migrated.next.live = _
      have nextLive : migrated.next.live = migrated.record.count .pending := by
        simp [ObjectRecord.count, phase]
      rw [nextLive, pendingBefore]
      apply countP_congr_mem
      intro cell _
      unfold counts
      split
      · rename_i a _
        by_cases p : a.pin = migrated.next.pin <;> by_cases r : a.activity ∈ migrated.next.rebirth <;>
          simp [p, r, ObjectRecord.classOf, ObjectRecord.successor, phase]
      · rfl
    | rebirth =>
      show migrated.record.rebirths = _
      have split := countP_split cells
        (counts config (payloads snapshot.canonicalBytes) request.object (migrated.record.successor migrated.next) .rebirth)
        (counts config (payloads snapshot.canonicalBytes) request.object migrated.record .rebirth)
      have both : cells.countP (fun x => counts config (payloads snapshot.canonicalBytes) request.object
          (migrated.record.successor migrated.next) .rebirth x &&
          counts config (payloads snapshot.canonicalBytes) request.object migrated.record .rebirth x) =
          cells.countP (counts config (payloads snapshot.canonicalBytes) request.object migrated.record .rebirth) := by
        apply countP_congr_mem
        intro cell _
        unfold counts
        split
        · rename_i a _
          by_cases p : a.pin = migrated.next.pin <;> by_cases r : a.activity ∈ migrated.next.rebirth <;>
            simp [p, r, ObjectRecord.classOf, ObjectRecord.successor, phase]
        · rfl
      have rest : cells.countP (fun x => counts config (payloads snapshot.canonicalBytes) request.object
          (migrated.record.successor migrated.next) .rebirth x &&
          !counts config (payloads snapshot.canonicalBytes) request.object migrated.record .rebirth x) =
          cells.countP (counts config (payloads snapshot.canonicalBytes) request.object migrated.record .live) := by
        apply countP_congr_mem
        intro cell _
        unfold counts
        split
        · rename_i a _
          by_cases p : a.pin = migrated.next.pin <;> by_cases r : a.activity ∈ migrated.next.rebirth <;>
            simp [p, r, ObjectRecord.classOf, ObjectRecord.successor, phase]
        · rfl
      have rebirthsIs : migrated.record.rebirths = migrated.record.count .rebirth := rfl
      rw [split, both, rest, ← liveZero, ← rebirthsBefore, rebirthsIs]
      rfl
  · intro other record next deadline state found draining stated
    rw [objects] at found
    split at found
    · cases found; cases draining
    · rename_i differs
      rw [packages]
      have stateBefore : stateView other (payloads snapshot.canonicalBytes (stateCell config.domain other)) =
          some state := by
        rcases payloads_after snapshot migrated.posts (stateCell config.domain other) with
          ⟨same, _⟩ | ⟨p, member, at_, after⟩
        · rw [← same]; exact stated
        · rw [after] at stated
          rcases kinded p member with isHead | ⟨role, _, _, _, k⟩
          · subst isHead
            rw [stateView_of_role (by decide : ObjectiveActivityCell.Role.object ≠ .state) headKinded.2] at stated
            cases stated
          · rw [migrated.postsExact] at member
            simp only [List.mem_cons, List.mem_append, List.mem_singleton, List.not_mem_nil, or_false] at member
            rcases member with isHead | inState | isBook
            · subst isHead
              rw [stateView_of_role (by decide : ObjectiveActivityCell.Role.object ≠ .state) headKinded.2] at stated
              cases stated
            · obtain ⟨version, value, isState⟩ := stateShape p inState
              subst isState
              simp only [postAt] at stated
              rw [stateView_stateImage, if_neg differs] at stated
              cases stated
            · subst isBook
              obtain ⟨role', _, _, st, _, k'⟩ := bookSilent
              rw [stateView_of_role st k'.2] at stated
              cases stated
      exact migratable other record next deadline state found draining stateBefore

#assert_axioms Migrated.upgradable

/-! ## Every reachable world -/

/-- **Every admitted kernel turn keeps both invariants** (its own posts). -/
theorem AdmittedTurn.upgradable {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height : Nat} (turn : AdmittedTurn config snapshot height)
    (holds : Upgradable config (payloads snapshot.canonicalBytes)) :
    Upgradable config (payloads (afterPosts snapshot turn.posts)) := by
  cases turn with
  | publish _ publication => exact Publication.upgradable publication holds
  | create _ created => exact Creation.upgradable created holds
  | birth _ signed born => exact Birth.upgradable born signed holds
  | resolve _ resolution => exact Resolution.upgradable resolution holds
  | deliver _ delivery => exact Delivery.upgradable delivery holds
  | topUp _ topped => exact TopUp.upgradable topped holds
  | exhaust _ exhausted => exact Exhaustion.upgradable exhausted holds
  | abandon _ abandoned => exact Abandonment.upgradable abandoned holds
  | invoke _ invoked => exact Invocation.upgradable invoked holds
  | deliverMessage _ delivered => exact MessageDelivery.upgradable delivered holds
  | adopt _ adopted => exact Adoption.upgradable adopted holds
  | migrate _ migrated => exact Migrated.upgradable migrated holds
  | abortDrained _ aborted => exact Abort.upgradable aborted holds
  | rebirth _ reborn => exact Rebirth.upgradable reborn holds

/-- **Every committed step keeps both invariants**: a kernel turn with its seat closing, a
seat turn's inert posts, an intent the ordinary gate admits; installed or not. -/
theorem Step.upgradable {rootBytes : Bytes → Digest} {config : Config} {before after : Snapshot rootBytes}
    (book : BookUnprotected config) (step : Step config before after)
    (holds : Upgradable config (payloads before.canonicalBytes)) :
    Upgradable config (payloads after.canonicalBytes) := by
  cases step with
  | turn turn sealing posts extra final schedule =>
    rcases execute_no_partial_data_commit schedule _
      (ActivitySeatEnd.AdmittedTurn.finalIntent sealing posts extra turn) with same | installed
    · rw [same]; exact holds
    · rw [installed, install_payloads _ (finalIntent_writes sealing final)]
      exact upgradable_transfer (fun cell guarded => (finalize_agree book turn final cell guarded).symm)
        (AdmittedTurn.upgradable turn holds)
  | inert intent posts writes inert schedule =>
    rcases execute_no_partial_data_commit schedule _ intent with same | installed
    · rw [same]; exact holds
    · rw [installed, install_payloads _ writes, inert_agree inert]; exact holds
  | foreign intent admitted schedule =>
    refine upgradable_transfer ?_ holds
    intro cell guarded
    unfold payloads
    rw [ObjectiveActivityGate.ordinary_execute_protected schedule _ admitted guarded]

/-- A genesis that holds no awaiting activity record and no object record. -/
def GenesisClean {rootBytes : Bytes → Digest} (config : Config) (genesis : Snapshot rootBytes) : Prop :=
  (∀ cell, awaitingView config (payloads genesis.canonicalBytes) cell = none) ∧
  ∀ object, objectView object (payloads genesis.canonicalBytes (objectCell config.domain object)) = none

/-- `GenesisClean` is inhabited: a genesis that holds no activity payload at all. -/
theorem genesisClean_of_empty {rootBytes : Bytes → Digest} {config : Config} {genesis : Snapshot rootBytes}
    (empty : ∀ cell, payloadOf (genesis.canonicalBytes cell) = none) : GenesisClean config genesis := by
  refine ⟨fun cell => ?_, fun object => ?_⟩
  · unfold awaitingView recordView payloads; rw [empty]
  · unfold objectView payloads; rw [empty]

/-- `BookUnprotected` is inhabited: a deployment whose Book coordinate is below the reserved base. -/
theorem bookUnprotected_of_lt {config : Config}
    (below : config.deployment.resourceBookId < ObjectiveActivityCell.reservedBase) : BookUnprotected config := by
  intro reserved
  exact Nat.not_le.mpr below reserved

theorem genesis_upgradable {rootBytes : Bytes → Digest} {config : Config} {genesis : Snapshot rootBytes}
    (clean : GenesisClean config genesis) : Upgradable config (payloads genesis.canonicalBytes) := by
  refine ⟨⟨[], ⟨List.nodup_nil, ?_, ?_, ?_⟩⟩, ?_⟩
  · intro cell activity found; rw [clean.1 cell] at found; cases found
  · intro cell activity found; rw [clean.1 cell] at found; cases found
  · intro object record held; rw [clean.2 object] at held; cases held
  · intro object record next deadline state held; rw [clean.2 object] at held; cases held

/-- **Both invariants hold in every reachable world.** -/
theorem reachable_upgradable {rootBytes : Bytes → Digest} {config : Config} {genesis snapshot : Snapshot rootBytes}
    (book : BookUnprotected config) (clean : GenesisClean config genesis)
    (reachable : Reachable config genesis snapshot) : Upgradable config (payloads snapshot.canonicalBytes) := by
  induction reachable with
  | genesis => exact genesis_upgradable clean
  | step _ step holds => exact Step.upgradable book step holds

/-- **`live_counts`.** In every reachable world there is one duplicate-free list of cells
holding every awaiting activity record (each at its own coordinate), and every object record the
kernel reads counts them exactly: `live` the awaiting activities of the object in class `live`
(pinned to its pin; while draining, not chosen for rebirth), `rebirths` those chosen for rebirth
(after MIGRATE: those left on an older pin), and, while draining, `next.live` those born on the
next pin. One retain and one release per turn keep them (brief trap 4). -/
theorem live_counts {rootBytes : Bytes → Digest} {config : Config} {genesis snapshot : Snapshot rootBytes}
    (book : BookUnprotected config) (clean : GenesisClean config genesis)
    (reachable : Reachable config genesis snapshot) :
    ∃ cells : List CellId, cells.Nodup ∧
      (∀ cell activity, awaitingView config (payloads snapshot.canonicalBytes) cell = some activity →
        cell ∈ cells) ∧
      ∀ object record, readObject config snapshot object = .ok (some record) →
        record.live = cells.countP (counts config (payloads snapshot.canonicalBytes) object record .live) ∧
        record.rebirths = cells.countP (counts config (payloads snapshot.canonicalBytes) object record .rebirth) ∧
        ∀ next deadline, record.phase = .draining next deadline →
          next.live = cells.countP (counts config (payloads snapshot.canonicalBytes) object record .pending) := by
  obtain ⟨⟨cells, census⟩, _⟩ := reachable_upgradable book clean reachable
  refine ⟨cells, census.nodup, census.covers, ?_⟩
  intro object record found
  have held := readObject_some found
  refine ⟨census.counted object record held .live, census.counted object record held .rebirth, ?_⟩
  intro next deadline draining
  have pending := census.counted object record held .pending
  simpa [ObjectRecord.count, draining] using pending

/-- **Theorem 6, `migrate_cannot_fail`** (brief §2). In every reachable world, on an object
that was ADOPTed (its record drains) and has drained (`live = 0`), MIGRATE is admitted whenever
the Book admits its declared fee. Nothing is assumed of the state: the invariant
`MigratableStates` supplies that it migrates and the next record admits it (`Adoption.migratable`
at the ADOPT, every drained write since by `judgeDrained`, births and calls identity-only).
`readState` succeeding is the kernel's own read of the cell (it refuses only a cell holding
another object's state). -/
theorem migrate_cannot_fail {rootBytes : Bytes → Digest} {config : Config} {genesis snapshot : Snapshot rootBytes}
    (book : BookUnprotected config) (clean : GenesisClean config genesis)
    (reachable : Reachable config genesis snapshot)
    {height : Nat} {request : MigrateRequest} {record : ObjectRecord} {next : Pending} {deadline : Nat}
    (found : readObject config snapshot request.object = .ok (some record))
    (draining : record.phase = .draining next deadline)
    (drained : record.live = 0)
    {current : Option ObjectState} (state : readState config snapshot request.object = .ok current)
    {bookCell : BookCell} (loaded : loadBook config snapshot = .ok bookCell)
    (payable : ∃ posted, postings bookCell (migrateBatch config request next) = .ok posted) :
    ∃ migrated, migrate config snapshot height request = .ok migrated := by
  obtain ⟨_, states⟩ := reachable_upgradable book clean reachable
  refine migrate_admitted_of_migratable found draining drained state ?_ loaded payable
  intro s isCurrent
  subst isCurrent
  have holds := states request.object record next deadline s (readObject_some found) draining (readState_some state)
  rw [← packageBytes_view] at holds
  exact judgeMigrated_iff.mpr holds

#assert_axioms AdmittedTurn.upgradable
#assert_axioms Step.upgradable
#assert_axioms genesisClean_of_empty
#assert_axioms bookUnprotected_of_lt
#assert_axioms genesis_upgradable
#assert_axioms reachable_upgradable
#assert_axioms live_counts
#assert_axioms migrate_cannot_fail

end Minidregg.Kernel.ObjectiveUpgradeInvariant
