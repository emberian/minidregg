/- Registered invariant domains (GPT-6 row A, A3): a set of member objects with a JOINT law.

An object's own law judges each write of its declared state on that object's views alone, so no
object law can say "these two balances sum to the reserve". A domain can: it names its members
(objects) and a law over their joint view, in which member `i`'s state slots appear under
`member/<i>/` (`state/total` of member 0 is `member/0/state/total`).

* **Registration** (`register`): a holder of a capability on EVERY member (checked by the native
  route) registers the domain. Each member consents under its upgrade policy: `frozen` refuses by
  name (`memberFrozen`, joining adds a law to the object), `governed authority _` must admit the
  registration's facts (turn 10). The law must hold on the members' current states. The turn writes
  the domain cell (role `domain`, at the domain's id: a digest of its members and law, so a domain
  is content-addressed) and every member's record with the domain added to `domains`. Membership is
  permanent in this range (leave and change are filed separately).
* **Judgment at turn end** (`judgeDomains`, run by `ActivitySeatEnd.finish` after the seat join on
  the FINAL posts of EVERY admitted turn): every object whose declared state the turn writes is
  looked up (its record as the turn leaves it); each domain it belongs to is judged on the joint
  state of all members' FINAL states (a posted state if the turn writes it, the snapshot's
  otherwise). The law is a STATE predicate (`judgeJoint`: no request slots, judged as both views),
  so it is an invariant of the members' states. A refusal is `domainLawDenied domain leaf`. The
  judgment only adds refusals: every frame and object law still judged its own write. It returns
  read guards on the domain cell, on every member's state cell and on every written object's
  record cell, so a concurrent turn that changes an unwritten member's state, or registers a domain
  over a written object, conflicts instead of slipping past the joint law.
-/
import Kernel.ObjectiveActivityUpgrade

namespace Minidregg.Kernel.ObjectiveActivity
open Minidregg.Theory Minidregg.Compiler
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Theory.TypedAuthorization (Digest SubjectId)
open Minidregg.Kernel.DurableDataIntent
open Minidregg.Kernel.ObjectiveActivityWire
open Minidregg.Kernel.ObjectRecord (ObjectRecord Facts stateSlots)
open Minidregg.Theory.CanonicalResourceKernel (AccountId Batch)
open Minidregg.Compiler.ObjectiveInvocationClaim (Capacity)

set_option autoImplicit false

/-! ## The domain record and its cell -/

/-- A domain's id: its members and law, content-addressed. -/
def domainId (members : List CellId) (law : Minidregg.Pred.Pred) : Digest :=
  tagged "DREGG/OBJECTIVE/DOMAIN/ID/v1"
    ((StreamCodec.product (StreamCodec.list digestStream) LawLeaf.predStream).encode (members, law))

def domainKey (id : Digest) : Bytes := digestStream.encode id

def domainCell (domain : Digest) (id : Digest) : CellId :=
  ⟨ObjectiveActivityCell.coordinate domain .domain (domainKey id)⟩

def domainImage (id : Digest) (domain : Domain) : Bytes :=
  image .domain (domainKey id) (encodeDomain domain)

/-- The domain a cell's bytes hold as `id`'s: `none` when the cell holds no activity payload,
refused when it holds anything else. -/
def domainFor (id : Digest) (bytes : Bytes) : Except Refusal (Option Domain) :=
  match payloadOf bytes with
  | none => .ok none
  | some payload =>
    if payload.role = .domain ∧ payload.key = domainKey id then
      match decodeDomain payload.body with
      | some domain => .ok (some domain)
      | none => .error (.domainCodec id)
    else .error (.domainCodec id)

def readDomain {rootBytes : Bytes → Digest} (config : Config) (snapshot : Snapshot rootBytes) (id : Digest) :
    Except Refusal (Option Domain) :=
  domainFor id (snapshot.canonicalBytes (domainCell config.domain id))

/-- At most this many members in one domain, and this many domains per object: a domain's
judgment reads every member, so its work is bounded by the registration. -/
def domainMemberCap : Nat := 16
def domainsPerObject : Nat := 8

/-! ## The joint judgment -/

def memberSlots (index : Nat) (slots : List (Minidregg.Pred.Slot × Int)) : List (Minidregg.Pred.Slot × Int) :=
  slots.map fun (slot, value) => ("member/" ++ toString index ++ "/" ++ slot, value)

/-- The joint slots of the members' states, member `i` under `member/<i>/`; a member with no
state contributes none (every atom reading it fails closed). -/
def jointSlots : Nat → List (Option ObjectState) → Option (List (Minidregg.Pred.Slot × Int))
  | _, [] => some []
  | index, none :: rest => jointSlots (index + 1) rest
  | index, some state :: rest => do
      let here ← stateSlots state.value
      let later ← jointSlots (index + 1) rest
      pure (memberSlots index here ++ later)

/-- **A domain's law is a STATE predicate**: it is judged on the members' joint state alone, as
both the old and the new view, with no request slots. So it states an invariant of the members'
states that holds after every turn (it cannot read the height, which moves without any turn, nor
compare old and new, which the members' own laws do). -/
def judgeJoint (law : Minidregg.Pred.Pred) (id : Digest) (states : List (Option ObjectState)) :
    Except Refusal Unit :=
  match jointSlots 0 states with
  | some joint =>
    match LawLeaf.of law ⟨joint⟩ ⟨joint⟩ with
    | none => .ok ()
    | some leaf => .error (.domainLawDenied id leaf)
  | none => .error (.domainUnprojectable id)

/-- The post a turn's intent installs at `cell`, if any: the first (`afterPosts`). -/
def firstAt (posts : List Post) (cell : CellId) : Option Post :=
  posts.find? fun post => post.cell = cell

/-- An object's declared state as the turn leaves it. -/
def finalState {rootBytes : Bytes → Digest} (config : Config) (snapshot : Snapshot rootBytes) (posts : List Post)
    (object : CellId) : Except Refusal (Option ObjectState) :=
  match firstAt posts (stateCell config.domain object) with
  | some post => stateFor object post.bytes
  | none => readState config snapshot object

/-- An object's record as the turn leaves it. -/
def finalRecord {rootBytes : Bytes → Digest} (config : Config) (snapshot : Snapshot rootBytes) (posts : List Post)
    (object : CellId) : Except Refusal (Option ObjectRecord) :=
  match firstAt posts (objectCell config.domain object) with
  | some post => objectFor object post.bytes
  | none => readObject config snapshot object

/-- A domain as the turn leaves its cell. -/
def finalDomain {rootBytes : Bytes → Digest} (config : Config) (snapshot : Snapshot rootBytes) (posts : List Post)
    (id : Digest) : Except Refusal (Option Domain) :=
  match firstAt posts (domainCell config.domain id) with
  | some post => domainFor id post.bytes
  | none => readDomain config snapshot id

/-- The object an activity payload of `role` belongs to (its key, decoded). -/
def objectOwner (role : ObjectiveActivityCell.Role) : Option ObjectiveActivityCell.Payload → Option CellId
  | some payload => if payload.role = role then digestStream.toLawful.decode payload.key else none
  | none => none

/-- The domain a domain payload holds (its key, decoded). -/
def domainOwner : Option ObjectiveActivityCell.Payload → Option Digest
  | some payload => if payload.role = .domain then digestStream.toLawful.decode payload.key else none
  | none => none

/-- What a post touches: the payload it writes and the payload its cell holds now. -/
def touched {rootBytes : Bytes → Digest} (snapshot : Snapshot rootBytes) (post : Post) :
    List (Option ObjectiveActivityCell.Payload) :=
  [payloadOf post.bytes, payloadOf (snapshot.canonicalBytes post.cell)]

/-- **The objects whose declared state a turn's posts can change**: every post whose written
payload OR whose cell's current payload is a state payload, by the object its key names. A post
that retires or blanks a state cell counts as a write of that object's state. -/
def writtenObjects {rootBytes : Bytes → Digest} (snapshot : Snapshot rootBytes) (posts : List Post) :
    List CellId :=
  posts.flatMap fun post => (touched snapshot post).filterMap (objectOwner .state)

/-- The domains whose cells the turn's posts touch (written or held). -/
def postedDomains {rootBytes : Bytes → Digest} (snapshot : Snapshot rootBytes) (posts : List Post) :
    List Digest :=
  posts.flatMap fun post => (touched snapshot post).filterMap domainOwner

/-- **A post keeps its record's domains**: when the post's cell holds an object record, what the
post writes is that object's record and names every domain the held one does. -/
def keepsDomains {rootBytes : Bytes → Digest} (snapshot : Snapshot rootBytes) (post : Post) :
    Except Refusal Unit :=
  match objectOwner .object (payloadOf (snapshot.canonicalBytes post.cell)) with
  | none => .ok ()
  | some object =>
    match objectFor object (snapshot.canonicalBytes post.cell) with
    | .ok (some held) =>
      match objectFor object post.bytes with
      | .ok (some written) =>
        if held.domains.all (· ∈ written.domains) then .ok () else .error (.domainsDropped object.value)
      | _ => if held.domains.isEmpty then .ok () else .error (.domainsDropped object.value)
    | _ => .ok ()

def keepAll {rootBytes : Bytes → Digest} (snapshot : Snapshot rootBytes) : List Post → Except Refusal Unit
  | [] => .ok ()
  | post :: rest =>
    match keepsDomains snapshot post with
    | .error reason => .error reason
    | .ok () => keepAll snapshot rest

/-- The domains of the written objects (each object's record as the turn leaves it). -/
def touchedDomains {rootBytes : Bytes → Digest} (config : Config) (snapshot : Snapshot rootBytes)
    (posts : List Post) : List CellId → Except Refusal (List Digest)
  | [] => .ok []
  | object :: rest =>
    match finalRecord config snapshot posts object, touchedDomains config snapshot posts rest with
    | .error reason, _ => .error reason
    | _, .error reason => .error reason
    | .ok none, .ok later => .ok later
    | .ok (some record), .ok later => .ok (record.domains ++ later)

/-- Judge one domain, as the turn leaves its cell, on the turn's final posts; its read guards. -/
def judgeDomain {rootBytes : Bytes → Digest} (config : Config) (snapshot : Snapshot rootBytes)
    (posts : List Post) (id : Digest) : Except Refusal (List ReadGuard) :=
  match finalDomain config snapshot posts id with
  | .error reason => .error reason
  | .ok none => .error (.domainMissing id)
  | .ok (some domain) =>
    match domain.members.mapM (finalState config snapshot posts) with
    | .error reason => .error reason
    | .ok states =>
      match judgeJoint domain.law id states with
      | .error reason => .error reason
      | .ok () => .ok (guardAt snapshot (domainCell config.domain id) ::
          domain.members.map fun member => guardAt snapshot (stateCell config.domain member))

def judgeEach {rootBytes : Bytes → Digest} (config : Config) (snapshot : Snapshot rootBytes)
    (posts : List Post) : List Digest → Except Refusal (List ReadGuard)
  | [] => .ok []
  | domain :: rest =>
    match judgeDomain config snapshot posts domain, judgeEach config snapshot posts rest with
    | .error reason, _ => .error reason
    | _, .error reason => .error reason
    | .ok here, .ok later => .ok (here ++ later)

/-- Every member's record, as the turn leaves it, names `id`. -/
def indexMembers {rootBytes : Bytes → Digest} (config : Config) (snapshot : Snapshot rootBytes)
    (posts : List Post) (id : Digest) : List CellId → Except Refusal Unit
  | [] => .ok ()
  | member :: rest =>
    match finalRecord config snapshot posts member with
    | .error reason => .error reason
    | .ok none => .error (.domainUnindexed id member.value)
    | .ok (some record) =>
      if id ∈ record.domains then indexMembers config snapshot posts id rest
      else .error (.domainUnindexed id member.value)

/-- A domain whose cell the turn writes is named by every member's record; its read guards
(the members' record cells). -/
def indexDomain {rootBytes : Bytes → Digest} (config : Config) (snapshot : Snapshot rootBytes)
    (posts : List Post) (id : Digest) : Except Refusal (List ReadGuard) :=
  match finalDomain config snapshot posts id with
  | .error reason => .error reason
  | .ok none => .ok []
  | .ok (some domain) =>
    match indexMembers config snapshot posts id domain.members with
    | .error reason => .error reason
    | .ok () => .ok (domain.members.map fun member => guardAt snapshot (objectCell config.domain member))

def indexEach {rootBytes : Bytes → Digest} (config : Config) (snapshot : Snapshot rootBytes)
    (posts : List Post) : List Digest → Except Refusal (List ReadGuard)
  | [] => .ok []
  | first :: rest =>
    match indexDomain config snapshot posts first, indexEach config snapshot posts rest with
    | .error reason, _ => .error reason
    | _, .error reason => .error reason
    | .ok here, .ok later => .ok (here ++ later)

/-- **The domain judgment at turn end** (the one choke point every admitted turn passes,
`ActivitySeatEnd.finish`):
1. every post on a cell holding an object record keeps that record's domains (`domainsDropped`);
2. every domain of every object whose state the posts can change (written OR held at a posted
   cell), and every domain whose cell the posts touch, holds on all its members' final states;
3. every domain whose cell the posts touch is named by each member's final record
   (`domainUnindexed`).
The read guards it returns go into the turn's intent (`ActivitySeatEnd.AdmittedTurn.finalIntent`);
what it reads at a posted cell is pinned by that post's own `pre`.

It also returns its UNITS of work (`Capacity.domainWork`, priced by `Tariff.domainWork`): one per
cell it reads for a domain and guards. Each DISTINCT domain is judged once (a state post names its
object twice, by the payload it writes and the one its cell holds, and two written objects may share a
domain: the list is deduplicated, `eraseDups`). Judging a domain reads its cell and every member's
state (`|members| + 1`, `judgeDomain_length`; the `+ 1` is the law's evaluation); indexing a posted
domain reads every member's record (`|members|`). `ActivitySeatEnd.finish` refuses a turn whose declared
allowance is below the units (`domainUncovered`). -/
def judgeDomains {rootBytes : Bytes → Digest} (config : Config) (snapshot : Snapshot rootBytes)
    (posts : List Post) : Except Refusal (List ReadGuard × Nat) :=
  match keepAll snapshot posts with
  | .error reason => .error reason
  | .ok () =>
    let written := writtenObjects snapshot posts
    let posted := postedDomains snapshot posts
    match touchedDomains config snapshot posts written with
    | .error reason => .error reason
    | .ok ids =>
      match judgeEach config snapshot posts (ids ++ posted).eraseDups with
      | .error reason => .error reason
      | .ok guards =>
        match indexEach config snapshot posts posted.eraseDups with
        | .error reason => .error reason
        | .ok index =>
          .ok (guards ++ index ++ written.map fun object => guardAt snapshot (objectCell config.domain object),
            guards.length + index.length)

/-! ## The judgment is sound: what an admitted turn end guarantees -/

/-- A domain judgment that admits means the law EVALUATES true on the members' joint slots. -/
theorem judgeJoint_holds {law : Minidregg.Pred.Pred} {id : Digest} {states : List (Option ObjectState)}
    (judged : judgeJoint law id states = .ok ()) :
    ∃ joint, jointSlots 0 states = some joint ∧ Minidregg.Pred.eval law ⟨joint⟩ ⟨joint⟩ = true := by
  unfold judgeJoint at judged
  cases hj : jointSlots 0 states with
  | none => rw [hj] at judged; cases judged
  | some joint =>
    rw [hj] at judged
    simp only at judged
    cases hl : LawLeaf.of law ⟨joint⟩ ⟨joint⟩ with
    | some leaf => rw [hl] at judged; cases judged
    | none => exact ⟨joint, rfl, (LawLeaf.of_none_iff law _ _).mp hl⟩

/-- `finalState` is the state the turn's posts leave at the object's state cell (`afterPosts`:
the first post there, else the snapshot's bytes). -/
theorem finalState_after {rootBytes : Bytes → Digest} (config : Config) (snapshot : Snapshot rootBytes)
    (posts : List Post) (object : CellId) :
    finalState config snapshot posts object =
      stateFor object (afterPosts snapshot posts (stateCell config.domain object)) := by
  unfold finalState firstAt afterPosts readState
  cases posts.find? (fun post => decide (post.cell = stateCell config.domain object)) <;> rfl

theorem finalRecord_after {rootBytes : Bytes → Digest} (config : Config) (snapshot : Snapshot rootBytes)
    (posts : List Post) (object : CellId) :
    finalRecord config snapshot posts object =
      objectFor object (afterPosts snapshot posts (objectCell config.domain object)) := by
  unfold finalRecord firstAt afterPosts readObject
  cases posts.find? (fun post => decide (post.cell = objectCell config.domain object)) <;> rfl

theorem finalDomain_after {rootBytes : Bytes → Digest} (config : Config) (snapshot : Snapshot rootBytes)
    (posts : List Post) (id : Digest) :
    finalDomain config snapshot posts id =
      domainFor id (afterPosts snapshot posts (domainCell config.domain id)) := by
  unfold finalDomain firstAt afterPosts readDomain
  cases posts.find? (fun post => decide (post.cell = domainCell config.domain id)) <;> rfl

theorem touchedDomains_mem {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {posts : List Post} {objects : List CellId} {ids : List Digest}
    (touched : touchedDomains config snapshot posts objects = .ok ids) :
    ∀ object ∈ objects, ∀ record, finalRecord config snapshot posts object = .ok (some record) →
      ∀ named ∈ record.domains, named ∈ ids := by
  induction objects generalizing ids with
  | nil => intro object member; cases member
  | cons first rest ih =>
    intro object member record found named inDomains
    unfold touchedDomains at touched
    cases hf : finalRecord config snapshot posts first with
    | error reason => rw [hf] at touched; cases touched
    | ok r =>
      cases hr : touchedDomains config snapshot posts rest with
      | error reason => rw [hf, hr] at touched; cases r <;> cases touched
      | ok later =>
        rw [hf, hr] at touched
        rcases List.mem_cons.mp member with rfl | inRest
        · rw [hf] at found
          cases found
          simp only [Except.ok.injEq] at touched
          subst touched
          exact List.mem_append_left _ inDomains
        · have := ih hr object inRest record found named inDomains
          cases r with
          | none => simp only [Except.ok.injEq] at touched; subst touched; exact this
          | some _ => simp only [Except.ok.injEq] at touched; subst touched; exact List.mem_append_right _ this

theorem judgeEach_mem {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {posts : List Post} {ids : List Digest} {guards : List ReadGuard}
    (judged : judgeEach config snapshot posts ids = .ok guards) :
    ∀ want ∈ ids, ∃ here, judgeDomain config snapshot posts want = .ok here ∧ ∀ g ∈ here, g ∈ guards := by
  induction ids generalizing guards with
  | nil => intro want member; cases member
  | cons first rest ih =>
    intro want member
    unfold judgeEach at judged
    cases hd : judgeDomain config snapshot posts first with
    | error reason => rw [hd] at judged; cases judged
    | ok here =>
      cases he : judgeEach config snapshot posts rest with
      | error reason => rw [hd, he] at judged; cases judged
      | ok later =>
        rw [hd, he] at judged
        simp only [Except.ok.injEq] at judged
        subst judged
        rcases List.mem_cons.mp member with rfl | inRest
        · exact ⟨here, hd, fun g inHere => List.mem_append_left _ inHere⟩
        · obtain ⟨found, judgedHere, within⟩ := ih he want inRest
          exact ⟨found, judgedHere, fun g inFound => List.mem_append_right _ (within g inFound)⟩

theorem indexEach_mem {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {posts : List Post} {ids : List Digest} {guards : List ReadGuard}
    (indexed : indexEach config snapshot posts ids = .ok guards) :
    ∀ want ∈ ids, ∃ here, indexDomain config snapshot posts want = .ok here ∧ ∀ g ∈ here, g ∈ guards := by
  induction ids generalizing guards with
  | nil => intro want member; cases member
  | cons first rest ih =>
    intro want member
    unfold indexEach at indexed
    cases hd : indexDomain config snapshot posts first with
    | error reason => rw [hd] at indexed; cases indexed
    | ok here =>
      cases he : indexEach config snapshot posts rest with
      | error reason => rw [hd, he] at indexed; cases indexed
      | ok later =>
        rw [hd, he] at indexed
        simp only [Except.ok.injEq] at indexed
        subst indexed
        rcases List.mem_cons.mp member with rfl | inRest
        · exact ⟨here, hd, fun g inHere => List.mem_append_left _ inHere⟩
        · obtain ⟨found, judgedHere, within⟩ := ih he want inRest
          exact ⟨found, judgedHere, fun g inFound => List.mem_append_right _ (within g inFound)⟩

theorem keepAll_mem {rootBytes : Bytes → Digest} {snapshot : Snapshot rootBytes} {posts : List Post}
    (kept : keepAll snapshot posts = .ok ()) : ∀ post ∈ posts, keepsDomains snapshot post = .ok () := by
  induction posts with
  | nil => intro post member; cases member
  | cons first rest ih =>
    intro post member
    unfold keepAll at kept
    cases hk : keepsDomains snapshot first with
    | error reason => rw [hk] at kept; cases kept
    | ok u =>
      rw [hk] at kept
      rcases List.mem_cons.mp member with rfl | inRest
      · exact hk
      · exact ih kept post inRest

theorem indexMembers_mem {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {posts : List Post} {id : Digest} {members : List CellId}
    (indexed : indexMembers config snapshot posts id members = .ok ()) :
    ∀ member ∈ members, ∃ record, finalRecord config snapshot posts member = .ok (some record) ∧
      id ∈ record.domains := by
  induction members with
  | nil => intro member inMembers; cases inMembers
  | cons first rest ih =>
    intro member inMembers
    unfold indexMembers at indexed
    cases hf : finalRecord config snapshot posts first with
    | error reason => rw [hf] at indexed; cases indexed
    | ok found =>
      cases found with
      | none => rw [hf] at indexed; cases indexed
      | some record =>
        rw [hf] at indexed
        simp only at indexed
        by_cases named : id ∈ record.domains
        · rw [if_pos named] at indexed
          rcases List.mem_cons.mp inMembers with rfl | inRest
          · exact ⟨record, hf, named⟩
          · exact ih indexed member inRest
        · rw [if_neg named] at indexed; cases indexed

theorem judgeDomain_ok {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {posts : List Post} {id : Digest} {guards : List ReadGuard}
    (judged : judgeDomain config snapshot posts id = .ok guards) :
    ∃ domain states, finalDomain config snapshot posts id = .ok (some domain) ∧
      domain.members.mapM (finalState config snapshot posts) = .ok states ∧
      judgeJoint domain.law id states = .ok () ∧
      guardAt snapshot (domainCell config.domain id) ∈ guards ∧
      ∀ member ∈ domain.members, guardAt snapshot (stateCell config.domain member) ∈ guards := by
  unfold judgeDomain at judged
  cases hr : finalDomain config snapshot posts id with
  | error reason => rw [hr] at judged; cases judged
  | ok found =>
    cases found with
    | none => rw [hr] at judged; cases judged
    | some domain =>
      rw [hr] at judged
      simp only at judged
      cases hs : domain.members.mapM (finalState config snapshot posts) with
      | error reason => rw [hs] at judged; cases judged
      | ok states =>
        rw [hs] at judged
        simp only at judged
        cases hj : judgeJoint domain.law id states with
        | error reason => rw [hj] at judged; cases judged
        | ok u =>
          rw [hj] at judged
          simp only [Except.ok.injEq] at judged
          subst judged
          exact ⟨domain, states, rfl, hs, hj, List.mem_cons_self .., fun member inMembers =>
            List.mem_cons_of_mem _ (List.mem_map_of_mem inMembers)⟩

theorem indexDomain_ok {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {posts : List Post} {id : Digest} {guards : List ReadGuard}
    (indexed : indexDomain config snapshot posts id = .ok guards) :
    ∀ domain, finalDomain config snapshot posts id = .ok (some domain) →
      ∀ member ∈ domain.members, (∃ record, finalRecord config snapshot posts member = .ok (some record) ∧
        id ∈ record.domains) ∧ guardAt snapshot (objectCell config.domain member) ∈ guards := by
  intro domain found member inMembers
  unfold indexDomain at indexed
  rw [found] at indexed
  simp only at indexed
  cases hi : indexMembers config snapshot posts id domain.members with
  | error reason => rw [hi] at indexed; cases indexed
  | ok u =>
    rw [hi] at indexed
    simp only [Except.ok.injEq] at indexed
    subst indexed
    exact ⟨indexMembers_mem hi member inMembers, List.mem_map_of_mem inMembers⟩

/-- **What an admitting turn-end judgment guarantees**, in parts: every post keeps its record's
domains; every domain it must judge (named by a written object's final record, or whose cell
a post touches) exists as the turn leaves it and holds on its members' final states, with the
domain cell and every member's state cell guarded; every domain whose cell a post touches is
named by each member's final record, with the member's record cell guarded; every written
object's record cell is guarded. -/
theorem judgeDomains_parts {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {posts : List Post} {guards : List ReadGuard} {units : Nat}
    (judged : judgeDomains config snapshot posts = .ok (guards, units)) :
    (∀ post ∈ posts, keepsDomains snapshot post = .ok ()) ∧
    (∀ id, ((∃ object ∈ writtenObjects snapshot posts, ∃ record,
        finalRecord config snapshot posts object = .ok (some record) ∧ id ∈ record.domains) ∨
        id ∈ postedDomains snapshot posts) →
      ∃ here, judgeDomain config snapshot posts id = .ok here ∧ ∀ g ∈ here, g ∈ guards) ∧
    (∀ id ∈ postedDomains snapshot posts,
      ∃ here, indexDomain config snapshot posts id = .ok here ∧ ∀ g ∈ here, g ∈ guards) ∧
    (∀ object ∈ writtenObjects snapshot posts, guardAt snapshot (objectCell config.domain object) ∈ guards) := by
  unfold judgeDomains at judged
  cases hk : keepAll snapshot posts with
  | error reason => rw [hk] at judged; cases judged
  | ok u =>
    rw [hk] at judged
    simp only at judged
    cases ht : touchedDomains config snapshot posts (writtenObjects snapshot posts) with
    | error reason => rw [ht] at judged; cases judged
    | ok ids =>
      rw [ht] at judged
      simp only at judged
      cases he : judgeEach config snapshot posts (ids ++ postedDomains snapshot posts).eraseDups with
      | error reason => rw [he] at judged; cases judged
      | ok domainGuards =>
        rw [he] at judged
        simp only at judged
        cases hx : indexEach config snapshot posts (postedDomains snapshot posts).eraseDups with
        | error reason => rw [hx] at judged; cases judged
        | ok index =>
          rw [hx] at judged
          simp only [Except.ok.injEq, Prod.mk.injEq] at judged
          obtain ⟨rfl, -⟩ := judged
          refine ⟨keepAll_mem hk, ?_, ?_, fun object written =>
            List.mem_append_right _ (List.mem_map_of_mem written)⟩
          · intro id which
            have inIds : id ∈ ids ++ postedDomains snapshot posts := by
              rcases which with ⟨object, written, record, found, named⟩ | posted
              · exact List.mem_append_left _ (touchedDomains_mem ht object written record found id named)
              · exact List.mem_append_right _ posted
            obtain ⟨here, judgedHere, within⟩ := judgeEach_mem he id (List.mem_eraseDups.mpr inIds)
            exact ⟨here, judgedHere, fun g inHere =>
              List.mem_append_left _ (List.mem_append_left _ (within g inHere))⟩
          · intro id posted
            obtain ⟨here, indexedHere, within⟩ := indexEach_mem hx id (List.mem_eraseDups.mpr posted)
            exact ⟨here, indexedHere, fun g inHere =>
              List.mem_append_left _ (List.mem_append_right _ (within g inHere))⟩

/-- **The domain judgment at turn end, stated.** When it admits a turn's final posts, then for
every object whose declared state the posts can change, every domain its record (as the turn
leaves it) names exists, and its law holds on ALL its members' final states (the written ones as
posted, the others as they stand); and the judgment's guards cover every cell it read: the
domain cell, every member's state cell, and every written object's record cell. -/
theorem judgeDomains_sound {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {posts : List Post} {guards : List ReadGuard} {units : Nat}
    (judged : judgeDomains config snapshot posts = .ok (guards, units)) :
    ∀ object ∈ writtenObjects snapshot posts,
      guardAt snapshot (objectCell config.domain object) ∈ guards ∧
      ∀ record, finalRecord config snapshot posts object = .ok (some record) →
        ∀ id ∈ record.domains, ∃ domain states, finalDomain config snapshot posts id = .ok (some domain) ∧
          domain.members.mapM (finalState config snapshot posts) = .ok states ∧
          (∃ joint, jointSlots 0 states = some joint ∧ Minidregg.Pred.eval domain.law ⟨joint⟩ ⟨joint⟩ = true) ∧
          guardAt snapshot (domainCell config.domain id) ∈ guards ∧
          ∀ member ∈ domain.members, guardAt snapshot (stateCell config.domain member) ∈ guards := by
  obtain ⟨_, judgedAll, _, objectGuards⟩ := judgeDomains_parts judged
  intro object written
  refine ⟨objectGuards object written, fun record found id named => ?_⟩
  obtain ⟨here, judgedHere, within⟩ := judgedAll id (.inl ⟨object, written, record, found, named⟩)
  obtain ⟨domain, states, read, mapped, holds, guardDomain, guardStates⟩ := judgeDomain_ok judgedHere
  exact ⟨domain, states, read, mapped, judgeJoint_holds holds, within _ guardDomain,
    fun member inMembers => within _ (guardStates member inMembers)⟩

/-! ## The judgment's units of work -/

/-- Judging a domain reads (and guards) its cell and every member's state: `|members| + 1` reads. -/
theorem judgeDomain_length {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {posts : List Post} {id : Digest} {here : List ReadGuard}
    (judged : judgeDomain config snapshot posts id = .ok here) :
    ∃ domain, finalDomain config snapshot posts id = .ok (some domain) ∧
      here.length = domain.members.length + 1 := by
  unfold judgeDomain at judged
  cases hr : finalDomain config snapshot posts id with
  | error reason => rw [hr] at judged; cases judged
  | ok found =>
    cases found with
    | none => rw [hr] at judged; cases judged
    | some domain =>
      rw [hr] at judged
      simp only at judged
      cases hs : domain.members.mapM (finalState config snapshot posts) with
      | error reason => rw [hs] at judged; cases judged
      | ok states =>
        rw [hs] at judged
        simp only at judged
        cases hj : judgeJoint domain.law id states with
        | error reason => rw [hj] at judged; cases judged
        | ok u =>
          rw [hj] at judged
          simp only [Except.ok.injEq] at judged
          subst judged
          exact ⟨domain, rfl, by simp⟩

theorem judgeEach_length {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {posts : List Post} {ids : List Digest} {guards : List ReadGuard}
    (judged : judgeEach config snapshot posts ids = .ok guards) :
    ∀ want ∈ ids, ∃ here, judgeDomain config snapshot posts want = .ok here ∧ here.length ≤ guards.length := by
  induction ids generalizing guards with
  | nil => intro want member; cases member
  | cons first rest ih =>
    intro want member
    unfold judgeEach at judged
    cases hd : judgeDomain config snapshot posts first with
    | error reason => rw [hd] at judged; cases judged
    | ok here =>
      cases he : judgeEach config snapshot posts rest with
      | error reason => rw [hd, he] at judged; cases judged
      | ok later =>
        rw [hd, he] at judged
        simp only [Except.ok.injEq] at judged
        subst judged
        rcases List.mem_cons.mp member with rfl | inRest
        · exact ⟨here, hd, by simp⟩
        · obtain ⟨found, judgedHere, short⟩ := ih he want inRest
          exact ⟨found, judgedHere, by simp; omega⟩

/-- **The judgment counts every domain it judges at its reads.** When it admits, every domain
it must judge (named by a written object's final record, or posted) exists as the turn leaves
it, and the units it reports are at least that domain's `|members| + 1`. (`ActivitySeatEnd`:
a finished turn's declared allowance covers the units, so the payer paid for them.) -/
theorem judgeDomains_units {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {posts : List Post} {guards : List ReadGuard} {units : Nat}
    (judged : judgeDomains config snapshot posts = .ok (guards, units)) :
    ∀ id, ((∃ object ∈ writtenObjects snapshot posts, ∃ record,
        finalRecord config snapshot posts object = .ok (some record) ∧ id ∈ record.domains) ∨
        id ∈ postedDomains snapshot posts) →
      ∃ domain, finalDomain config snapshot posts id = .ok (some domain) ∧
        domain.members.length + 1 ≤ units := by
  unfold judgeDomains at judged
  cases hk : keepAll snapshot posts with
  | error reason => rw [hk] at judged; cases judged
  | ok u =>
    rw [hk] at judged
    simp only at judged
    cases ht : touchedDomains config snapshot posts (writtenObjects snapshot posts) with
    | error reason => rw [ht] at judged; cases judged
    | ok ids =>
      rw [ht] at judged
      simp only at judged
      cases he : judgeEach config snapshot posts (ids ++ postedDomains snapshot posts).eraseDups with
      | error reason => rw [he] at judged; cases judged
      | ok domainGuards =>
        rw [he] at judged
        simp only at judged
        cases hx : indexEach config snapshot posts (postedDomains snapshot posts).eraseDups with
        | error reason => rw [hx] at judged; cases judged
        | ok index =>
          rw [hx] at judged
          simp only [Except.ok.injEq, Prod.mk.injEq] at judged
          obtain ⟨-, rfl⟩ := judged
          intro id which
          have inIds : id ∈ ids ++ postedDomains snapshot posts := by
            rcases which with ⟨object, written, record, found, named⟩ | posted
            · exact List.mem_append_left _ (touchedDomains_mem ht object written record found id named)
            · exact List.mem_append_right _ posted
          obtain ⟨here, judgedHere, short⟩ := judgeEach_length he id (List.mem_eraseDups.mpr inIds)
          obtain ⟨domain, found, length⟩ := judgeDomain_length judgedHere
          exact ⟨domain, found, by omega⟩

/-! ## Registration -/

structure RegisterRequest where
  subject : SubjectId
  members : List CellId
  law : Minidregg.Pred.Pred
  /-- The Book account that funds the domain cell's retention and pays the registration's fee;
  never authority. -/
  payer : AccountId
  /-- The declared envelope of the registration turn: its public price (`Tariff.workOf`) is the
  fee `payer` pays (`registerBatch`), and its `domainWork` is the allowance the turn end's
  judgment of the new domain must fit (`ActivitySeatEnd.AdmittedTurn.domainAllowance`). -/
  envelope : Capacity
  nonce : Nat

def RegisterRequest.id (request : RegisterRequest) : Digest := domainId request.members request.law

def registerTransaction (request : RegisterRequest) : TransactionId :=
  tagged "DREGG/OBJECTIVE/DOMAIN/TX/REGISTER/v1"
    (subjectStream.encode request.subject ++ digestStream.encode request.id ++ StreamCodec.nat.encode request.nonce)

/-- The facts a member's upgrade authority judges a registration by: turn 10, the member as target. -/
def registerFacts (request : RegisterRequest) (height : Nat) (member : CellId) : Facts :=
  ⟨some request.subject, height, member.value, 10, none, none⟩

/-- A member's consent: `frozen` refuses, a governed authority must admit the facts, and the
member has room for one more domain. -/
def memberConsent (request : RegisterRequest) (height : Nat) (member : CellId) (record : ObjectRecord) :
    Except Refusal Unit :=
  match record.upgrade with
  | .frozen => .error (.memberFrozen member.value)
  | .governed authority _ =>
    if Minidregg.Pred.eval authority (factsState (registerFacts request height member))
        (factsState (registerFacts request height member)) then
      if record.domains.length < domainsPerObject then .ok () else .error (.memberDomainsFull member.value)
    else .error (.memberDenied member.value)

def readMember {rootBytes : Bytes → Digest} (config : Config) (snapshot : Snapshot rootBytes) (member : CellId) :
    Except Refusal ObjectRecord :=
  match readObject config snapshot member with
  | .error reason => .error reason
  | .ok none => .error (.domainMember member.value)
  | .ok (some record) => .ok record

def consentAll (request : RegisterRequest) (height : Nat) : List (CellId × ObjectRecord) → Except Refusal Unit
  | [] => .ok ()
  | (member, record) :: rest =>
    match memberConsent request height member record with
    | .error reason => .error reason
    | .ok () => consentAll request height rest

/-- The record a member is left with: the domain added. -/
def joined (record : ObjectRecord) (id : Digest) : ObjectRecord := { record with domains := record.domains ++ [id] }

def RegisterRequest.domain (request : RegisterRequest) : Domain := ⟨request.members, request.law, request.payer⟩

/-- The registration's fee: the public price of its declared envelope, from the payer's account. -/
def registerBatch (config : Config) (request : RegisterRequest) : Batch :=
  ⟨[], [.fee request.payer config.collector config.asset (config.tariff.workOf request.envelope)], []⟩

structure Registration {rootBytes : Bytes → Digest} (config : Config) (snapshot : Snapshot rootBytes)
    (height : Nat) (request : RegisterRequest) where
  private mk ::
  shape : request.members ≠ [] ∧ request.members.Nodup ∧ request.members.length ≤ domainMemberCap
  absent : readDomain config snapshot request.id = .ok none
  records : List ObjectRecord
  recordsExact : request.members.mapM (readMember config snapshot) = .ok records
  consented : consentAll request height (request.members.zip records) = .ok ()
  states : List (Option ObjectState)
  statesExact : request.members.mapM (readState config snapshot) = .ok states
  /-- The law holds on the members' current states. -/
  judged : judgeJoint request.law request.id states = .ok ()
  book : BookCell
  bookExact : loadBook config snapshot = .ok book
  posted : Postings book
  postedBatch : posted.batch = registerBatch config request
  posts : List Post
  postsExact : posts = postAt snapshot (domainCell config.domain request.id) (domainImage request.id request.domain) ::
    ((request.members.zip records).map (fun (member, record) =>
      postAt snapshot (objectCell config.domain member) (objectImage member (joined record request.id))) ++
      [posted.write config snapshot])

def register {rootBytes : Bytes → Digest} (config : Config) (snapshot : Snapshot rootBytes) (height : Nat)
    (request : RegisterRequest) : Except Refusal (Registration config snapshot height request) :=
  if shape : request.members ≠ [] ∧ request.members.Nodup ∧ request.members.length ≤ domainMemberCap then
    match absent : readDomain config snapshot request.id with
    | .error reason => .error reason
    | .ok (some _) => .error (.domainExists request.id)
    | .ok none =>
    match recordsExact : request.members.mapM (readMember config snapshot) with
    | .error reason => .error reason
    | .ok records =>
    match consented : consentAll request height (request.members.zip records) with
    | .error reason => .error reason
    | .ok () =>
    match statesExact : request.members.mapM (readState config snapshot) with
    | .error reason => .error reason
    | .ok states =>
    match judged : judgeJoint request.law request.id states with
    | .error reason => .error reason
    | .ok () =>
    match bookExact : loadBook config snapshot with
    | .error reason => .error reason
    | .ok book =>
    match postedExact : postings book (registerBatch config request) with
    | .error reason => .error reason
    | .ok posted => .ok ⟨shape, absent, records, recordsExact, consented, states, statesExact, judged, book,
        bookExact, posted, postings_batch postedExact, _, rfl⟩
  else .error (.domainShape "members must be 1..16 distinct objects")

/-- A registration reads every member's state: it conflicts with a concurrent write of any. -/
def Registration.guards {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height : Nat} {request : RegisterRequest} (_registered : Registration config snapshot height request) :
    List ReadGuard :=
  request.members.map fun member => guardAt snapshot (stateCell config.domain member)

def Registration.intent {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height : Nat} {request : RegisterRequest} (registered : Registration config snapshot height request)
    (sealing : Seal) : DataIntent rootBytes :=
  intentOf rootBytes (registerTransaction request) registered.posts registered.guards [] sealing

#assert_axioms domain_roundTrip judgeJoint_holds finalState_after finalRecord_after finalDomain_after judgeDomains_parts
  judgeDomains_sound judgeDomain_length judgeEach_length judgeDomains_units

end Minidregg.Kernel.ObjectiveActivity
