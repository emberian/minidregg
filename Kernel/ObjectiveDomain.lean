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
open Minidregg.Theory.CanonicalResourceKernel (AccountId)

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

/-- The objects whose declared state a turn's posts write: every post holding a state payload,
by the object its key names. -/
def writtenObjects (posts : List Post) : List CellId :=
  posts.filterMap fun post =>
    match payloadOf post.bytes with
    | some payload => if payload.role = .state then digestStream.toLawful.decode payload.key else none
    | none => none

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

/-- Judge one domain on the turn's final posts; its read guards. -/
def judgeDomain {rootBytes : Bytes → Digest} (config : Config) (snapshot : Snapshot rootBytes)
    (posts : List Post) (id : Digest) : Except Refusal (List ReadGuard) :=
  match readDomain config snapshot id with
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

/-- **The domain judgment at turn end**: every domain of every object whose state the turn's
final posts write holds on the members' final states. The read guards it returns go into the
turn's intent (`ActivitySeatEnd.AdmittedTurn.finalIntent`). -/
def judgeDomains {rootBytes : Bytes → Digest} (config : Config) (snapshot : Snapshot rootBytes)
    (posts : List Post) : Except Refusal (List ReadGuard) :=
  let written := writtenObjects posts
  match touchedDomains config snapshot posts written with
  | .error reason => .error reason
  | .ok ids =>
    match judgeEach config snapshot posts ids with
    | .error reason => .error reason
    | .ok guards => .ok (guards ++ written.map fun object => guardAt snapshot (objectCell config.domain object))

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

theorem judgeDomain_ok {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {posts : List Post} {id : Digest} {guards : List ReadGuard}
    (judged : judgeDomain config snapshot posts id = .ok guards) :
    ∃ domain states, readDomain config snapshot id = .ok (some domain) ∧
      domain.members.mapM (finalState config snapshot posts) = .ok states ∧
      judgeJoint domain.law id states = .ok () ∧
      guardAt snapshot (domainCell config.domain id) ∈ guards ∧
      ∀ member ∈ domain.members, guardAt snapshot (stateCell config.domain member) ∈ guards := by
  unfold judgeDomain at judged
  cases hr : readDomain config snapshot id with
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

/-- **The domain judgment at turn end, stated.** When it admits a turn's final posts, then for
every object whose declared state the posts write, every domain its record (as the turn leaves
it) names exists, and its law holds on ALL its members' final states (the written ones as
posted, the others as they stand); and the judgment's guards cover every cell it read: the
domain cell, every member's state cell, and every written object's record cell. -/
theorem judgeDomains_sound {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {posts : List Post} {guards : List ReadGuard} (judged : judgeDomains config snapshot posts = .ok guards) :
    ∀ object ∈ writtenObjects posts,
      guardAt snapshot (objectCell config.domain object) ∈ guards ∧
      ∀ record, finalRecord config snapshot posts object = .ok (some record) →
        ∀ id ∈ record.domains, ∃ domain states, readDomain config snapshot id = .ok (some domain) ∧
          domain.members.mapM (finalState config snapshot posts) = .ok states ∧
          (∃ joint, jointSlots 0 states = some joint ∧ Minidregg.Pred.eval domain.law ⟨joint⟩ ⟨joint⟩ = true) ∧
          guardAt snapshot (domainCell config.domain id) ∈ guards ∧
          ∀ member ∈ domain.members, guardAt snapshot (stateCell config.domain member) ∈ guards := by
  unfold judgeDomains at judged
  cases ht : touchedDomains config snapshot posts (writtenObjects posts) with
  | error reason => simp only [ht] at judged; cases judged
  | ok ids =>
    cases he : judgeEach config snapshot posts ids with
    | error reason => simp only [ht, he] at judged; cases judged
    | ok domainGuards =>
      simp only [ht, he, Except.ok.injEq] at judged
      subst judged
      intro object written
      refine ⟨List.mem_append_right _ (List.mem_map_of_mem written), fun record found want named => ?_⟩
      obtain ⟨here, judgedHere, within⟩ := judgeEach_mem he want (touchedDomains_mem ht object written record found want named)
      obtain ⟨domain, states, read, mapped, holds, guardDomain, guardStates⟩ := judgeDomain_ok judgedHere
      exact ⟨domain, states, read, mapped, judgeJoint_holds holds, List.mem_append_left _ (within _ guardDomain),
        fun member inMembers => List.mem_append_left _ (within _ (guardStates member inMembers))⟩

/-! ## Registration -/

structure RegisterRequest where
  subject : SubjectId
  members : List CellId
  law : Minidregg.Pred.Pred
  /-- The Book account that funds the domain cell's retention; never authority. -/
  payer : AccountId
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
  posts : List Post
  postsExact : posts = postAt snapshot (domainCell config.domain request.id) (domainImage request.id request.domain) ::
    (request.members.zip records).map fun (member, record) =>
      postAt snapshot (objectCell config.domain member) (objectImage member (joined record request.id))

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
    | .ok () => .ok ⟨shape, absent, records, recordsExact, consented, states, statesExact, judged, _, rfl⟩
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

#assert_axioms domain_roundTrip judgeJoint_holds finalState_after judgeDomains_sound

end Minidregg.Kernel.ObjectiveActivity
