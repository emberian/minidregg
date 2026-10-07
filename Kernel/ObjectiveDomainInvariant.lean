/- **`domain_holds_forever`**: in every reachable world (`ObjectiveCheckpointInvariant.Reachable`),
every registered invariant domain's law holds on its members' declared states, and every member's
object record names the domain.

Why it holds for EVERY step, with no case split on the kind of turn:
* a kernel turn's intent is the output of `ActivitySeatEnd.finish` (`Step.turn` carries
  `finish … = .ok (posts, extra)`, and its intent's writes are exactly `posts`,
  `finalIntent_writes`); `finish` ends with `judgeDomains`, which admits only posts that
  (1) keep every domain of every object record they rewrite (`keepsDomains`), (2) leave every
  domain they could affect satisfied on the members' final states: the domains of every object
  whose state a post writes OR whose state a posted cell holds (a retired or blanked state
  counts), and every domain whose cell a post touches, and (3) leave every domain whose cell
  they touch named by each member's final record. So the theorem holds for every constructor of
  `AdmittedTurn`, present and future, by the choke point rather than by a per-turn list;
* a seat turn's posts are inert (`inert_agree`: no payload changes);
* an intent the ordinary gate admits writes no protected cell, and the domain, object-record
  and state cells are protected (`ObjectiveActivityCell.coordinate_reserved`).

Stated over the payloads of protected cells, like `ObjectiveUpgradeInvariant`; the genesis
must satisfy it (`genesis_domainsHold` for a genesis with no activity payload). -/
import Kernel.ObjectiveUpgradeInvariant

namespace Minidregg.Kernel.ObjectiveDomainInvariant
open Minidregg.Theory Minidregg.Compiler
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Theory.TypedAuthorization (Digest SubjectId)
open Minidregg.Kernel.DurableDataIntent
open Minidregg.Kernel.ObjectiveActivityWire
open Minidregg.Kernel.ObjectiveActivity
open Minidregg.Kernel.ObjectiveCheckpointInvariant
open Minidregg.Kernel.ObjectiveUpgradeInvariant
open Minidregg.Kernel.ObjectRecord (ObjectRecord)
set_option autoImplicit false

/-! ## The invariant -/

/-- The domain `id` a payload holds (key-checked, as `domainFor`). -/
def domainView (id : Digest) (payload : Option Payload) : Option Domain :=
  match payload with
  | some p => if p.role = .domain ∧ p.key = domainKey id then decodeDomain p.body else none
  | none => none

/-- The members' declared states, as a payload map holds them. -/
def memberStates (config : Config) (P : Payloads) (members : List CellId) : List (Option ObjectState) :=
  members.map fun member => stateView member (P (stateCell config.domain member))

/-- A law holds on the members' joint state (the view `judgeJoint` judges). -/
def JointHolds (law : Minidregg.Pred.Pred) (states : List (Option ObjectState)) : Prop :=
  ∃ joint, jointSlots 0 states = some joint ∧ Minidregg.Pred.eval law ⟨joint⟩ ⟨joint⟩ = true

/-- **Every domain holds**: each member's record names it, and its law holds on the members'
states. -/
def DomainsHold (config : Config) (P : Payloads) : Prop :=
  ∀ id domain, domainView id (P (domainCell config.domain id)) = some domain →
    (∀ member ∈ domain.members, ∃ record,
      objectView member (P (objectCell config.domain member)) = some record ∧ id ∈ record.domains) ∧
    JointHolds domain.law (memberStates config P domain.members)

/-! ## Reading bytes as views -/

theorem stateFor_view {object : CellId} {bytes : Bytes} {state : Option ObjectState}
    (read : stateFor object bytes = .ok state) : stateView object (payloadOf bytes) = state := by
  unfold stateFor at read
  unfold stateView
  cases present : payloadOf bytes with
  | none => rw [present] at read; cases read; rfl
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

theorem objectFor_view {object : CellId} {bytes : Bytes} {record : ObjectRecord}
    (read : objectFor object bytes = .ok (some record)) : objectView object (payloadOf bytes) = some record := by
  unfold objectFor at read
  unfold objectView
  cases present : payloadOf bytes with
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

theorem view_objectFor {object : CellId} {bytes : Bytes} {record : ObjectRecord}
    (view : objectView object (payloadOf bytes) = some record) : objectFor object bytes = .ok (some record) := by
  unfold objectView at view
  unfold objectFor
  cases present : payloadOf bytes with
  | none => rw [present] at view; cases view
  | some payload =>
    rw [present] at view
    simp only at view ⊢
    split at view
    · rename_i owned
      rw [if_pos owned, view]
    · cases view

theorem domainFor_view {id : Digest} {bytes : Bytes} {domain : Domain}
    (read : domainFor id bytes = .ok (some domain)) : domainView id (payloadOf bytes) = some domain := by
  unfold domainFor at read
  unfold domainView
  cases present : payloadOf bytes with
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

theorem view_domainFor {id : Digest} {bytes : Bytes} {domain : Domain}
    (view : domainView id (payloadOf bytes) = some domain) : domainFor id bytes = .ok (some domain) := by
  unfold domainView at view
  unfold domainFor
  cases present : payloadOf bytes with
  | none => rw [present] at view; cases view
  | some payload =>
    rw [present] at view
    simp only at view ⊢
    split at view
    · rename_i owned
      rw [if_pos owned, view]
    · cases view

/-- A payload holding `object`'s state is owned by `object`. -/
theorem owner_of_stateView {object : CellId} {payload : Option Payload} {state : ObjectState}
    (view : stateView object payload = some state) : objectOwner .state payload = some object := by
  cases payload with
  | none => cases view
  | some p =>
    unfold stateView at view
    simp only at view
    split at view
    · rename_i owned
      simp only [objectOwner, owned.1, if_true, owned.2]
      exact digestStream.toLawful.decode_encode object
    · cases view

theorem owner_of_objectView {object : CellId} {payload : Option Payload} {record : ObjectRecord}
    (view : objectView object payload = some record) : objectOwner .object payload = some object := by
  cases payload with
  | none => cases view
  | some p =>
    unfold objectView at view
    simp only at view
    split at view
    · rename_i owned
      simp only [objectOwner, owned.1, if_true, owned.2]
      exact digestStream.toLawful.decode_encode object
    · cases view

theorem owner_of_domainView {id : Digest} {payload : Option Payload} {domain : Domain}
    (view : domainView id payload = some domain) : domainOwner payload = some id := by
  cases payload with
  | none => cases view
  | some p =>
    unfold domainView at view
    simp only at view
    split at view
    · rename_i owned
      simp only [domainOwner, owned.1, if_true, owned.2]
      exact digestStream.toLawful.decode_encode id
    · cases view

theorem mem_written {rootBytes : Bytes → Digest} {snapshot : Snapshot rootBytes} {posts : List Post}
    {post : Post} (member : post ∈ posts) {object : CellId}
    (owned : objectOwner .state (payloadOf post.bytes) = some object ∨
      objectOwner .state (payloadOf (snapshot.canonicalBytes post.cell)) = some object) :
    object ∈ writtenObjects snapshot posts := by
  unfold writtenObjects
  refine List.mem_flatMap.mpr ⟨post, member, List.mem_filterMap.mpr ?_⟩
  rcases owned with owned | owned
  · exact ⟨_, by simp [touched], owned⟩
  · exact ⟨_, by simp [touched], owned⟩

theorem mem_posted {rootBytes : Bytes → Digest} {snapshot : Snapshot rootBytes} {posts : List Post}
    {post : Post} (member : post ∈ posts) {id : Digest}
    (owned : domainOwner (payloadOf post.bytes) = some id) : id ∈ postedDomains snapshot posts := by
  unfold postedDomains
  exact List.mem_flatMap.mpr ⟨post, member, List.mem_filterMap.mpr ⟨_, by simp [touched], owned⟩⟩

/-- The members' final states are the states the posts leave. -/
theorem mapM_finalState {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {posts : List Post} : ∀ (members : List CellId) (states : List (Option ObjectState)),
      members.mapM (finalState config snapshot posts) = .ok states →
      states = memberStates config (payloads (afterPosts snapshot posts)) members
  | [], states, mapped => by
    simp only [List.mapM_nil] at mapped
    cases mapped
    rfl
  | member :: rest, states, mapped => by
    simp only [List.mapM_cons] at mapped
    cases here : finalState config snapshot posts member with
    | error reason => rw [here] at mapped; cases mapped
    | ok state =>
      rw [here] at mapped
      cases later : rest.mapM (finalState config snapshot posts) with
      | error reason => rw [later] at mapped; cases mapped
      | ok others =>
        rw [later] at mapped
        cases mapped
        rw [finalState_after] at here
        simp only [memberStates, List.map_cons, payloads, stateFor_view here]
        exact congrArg _ (mapM_finalState rest others later)

/-! ## The turn-end judgment keeps the invariant -/

section Judged

variable {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
  {posts : List Post} {guards : List ReadGuard} {units : Nat}

/-- A judged domain holds on the states the posts leave. -/
theorem judged_holds {id : Digest} {here : List ReadGuard} {domain : Domain}
    (judged : judgeDomain config snapshot posts id = .ok here)
    (view : domainView id (payloads (afterPosts snapshot posts) (domainCell config.domain id)) = some domain) :
    JointHolds domain.law (memberStates config (payloads (afterPosts snapshot posts)) domain.members) := by
  obtain ⟨found, states, final, mapped, holds, _, _⟩ := judgeDomain_ok judged
  rw [finalDomain_after, view_domainFor view] at final
  cases final
  rw [← mapM_finalState _ _ mapped]
  exact judgeJoint_holds holds

/-- A record a post rewrites keeps every domain it named. -/
theorem records_keep (judged : judgeDomains config snapshot posts = .ok (guards, units)) {object : CellId}
    {record : ObjectRecord}
    (held : objectView object (payloads snapshot.canonicalBytes (objectCell config.domain object)) = some record) :
    ∀ id ∈ record.domains, ∃ after,
      objectView object (payloads (afterPosts snapshot posts) (objectCell config.domain object)) = some after ∧
      id ∈ after.domains := by
  intro id named
  rcases payloads_after snapshot posts (objectCell config.domain object) with ⟨same, _⟩ | ⟨post, member, at_, after⟩
  · exact ⟨record, by rw [same]; exact held, named⟩
  · have kept := (judgeDomains_parts judged).1 post member
    have prior : payloadOf (snapshot.canonicalBytes post.cell) =
        payloads snapshot.canonicalBytes (objectCell config.domain object) := by rw [at_]; rfl
    unfold keepsDomains at kept
    rw [prior, owner_of_objectView held] at kept
    simp only at kept
    rw [show snapshot.canonicalBytes post.cell = snapshot.canonicalBytes (objectCell config.domain object) by
      rw [at_], view_objectFor held] at kept
    simp only at kept
    cases written : objectFor object post.bytes with
    | error reason =>
      rw [written] at kept
      simp only at kept
      split at kept
      · rename_i empty
        simp only [List.isEmpty_iff] at empty
        rw [empty] at named; cases named
      · cases kept
    | ok found =>
      cases found with
      | none =>
        rw [written] at kept
        simp only at kept
        split at kept
        · rename_i empty
          simp only [List.isEmpty_iff] at empty
          rw [empty] at named; cases named
        · cases kept
      | some rewritten =>
        rw [written] at kept
        simp only at kept
        split at kept
        · rename_i all
          refine ⟨rewritten, by rw [after]; exact objectFor_view written, ?_⟩
          exact of_decide_eq_true (List.all_eq_true.mp all id named)
        · cases kept

/-- A member whose state view the posts change is a written object. -/
theorem changed_written {object : CellId}
    (changed : stateView object (payloads (afterPosts snapshot posts) (stateCell config.domain object)) ≠
      stateView object (payloads snapshot.canonicalBytes (stateCell config.domain object))) :
    object ∈ writtenObjects snapshot posts := by
  rcases payloads_after snapshot posts (stateCell config.domain object) with ⟨same, _⟩ | ⟨post, member, at_, after⟩
  · exact absurd (by rw [same]) changed
  · rw [after] at changed
    have prior : payloads snapshot.canonicalBytes (stateCell config.domain object) =
        payloadOf (snapshot.canonicalBytes post.cell) := by rw [at_]; rfl
    rw [prior] at changed
    cases now : stateView object (payloadOf post.bytes) with
    | some state => exact mem_written member (.inl (owner_of_stateView now))
    | none =>
      cases was : stateView object (payloadOf (snapshot.canonicalBytes post.cell)) with
      | some state => exact mem_written member (.inr (owner_of_stateView was))
      | none => rw [now, was] at changed; exact absurd rfl changed

/-- **The turn-end judgment keeps every domain**: posts it admits leave every domain satisfied
and indexed. -/
theorem judged_preserves (judged : judgeDomains config snapshot posts = .ok (guards, units))
    (holds : DomainsHold config (payloads snapshot.canonicalBytes)) :
    DomainsHold config (payloads (afterPosts snapshot posts)) := by
  obtain ⟨_, judgedAll, indexedAll, _⟩ := judgeDomains_parts judged
  intro id domain view
  -- The index: posted domain cells by `indexDomain`; others by the held index and `records_keep`.
  have indexed : ∀ member ∈ domain.members, ∃ record,
      objectView member (payloads (afterPosts snapshot posts) (objectCell config.domain member)) = some record ∧
      id ∈ record.domains := by
    rcases payloads_after snapshot posts (domainCell config.domain id) with ⟨same, _⟩ | ⟨post, member, at_, after⟩
    · rw [same] at view
      intro member inMembers
      obtain ⟨record, held, named⟩ := (holds id domain view).1 member inMembers
      exact records_keep judged held id named
    · have posted := mem_posted (snapshot := snapshot) member
        (owner_of_domainView (show domainView id (payloadOf post.bytes) = some domain by rw [← after]; exact view))
      obtain ⟨here, indexedHere, _⟩ := indexedAll id posted
      have final : finalDomain config snapshot posts id = .ok (some domain) := by
        rw [finalDomain_after]; exact view_domainFor view
      intro other inMembers
      obtain ⟨⟨record, found, named⟩, _⟩ := indexDomain_ok indexedHere domain final other inMembers
      rw [finalRecord_after] at found
      exact ⟨record, objectFor_view found, named⟩
  refine ⟨indexed, ?_⟩
  -- The law: judged whenever a member's state changed or the domain cell was posted.
  by_cases changed : ∃ member ∈ domain.members,
      stateView member (payloads (afterPosts snapshot posts) (stateCell config.domain member)) ≠
        stateView member (payloads snapshot.canonicalBytes (stateCell config.domain member))
  · obtain ⟨member, inMembers, differs⟩ := changed
    obtain ⟨record, found, named⟩ := indexed member inMembers
    have final : finalRecord config snapshot posts member = .ok (some record) := by
      rw [finalRecord_after]; exact view_objectFor found
    obtain ⟨here, judgedHere, _⟩ := judgedAll id (.inl ⟨member, changed_written differs, record, final, named⟩)
    exact judged_holds judgedHere view
  · have same : memberStates config (payloads (afterPosts snapshot posts)) domain.members =
        memberStates config (payloads snapshot.canonicalBytes) domain.members := by
      unfold memberStates
      refine List.map_congr_left fun member inMembers => ?_
      by_contra differs
      exact changed ⟨member, inMembers, differs⟩
    rcases payloads_after snapshot posts (domainCell config.domain id) with ⟨cell, _⟩ | ⟨post, member, at_, after⟩
    · rw [cell] at view
      rw [same]
      exact (holds id domain view).2
    · have posted := mem_posted (snapshot := snapshot) member
        (owner_of_domainView (show domainView id (payloadOf post.bytes) = some domain by rw [← after]; exact view))
      obtain ⟨here, judgedHere, _⟩ := judgedAll id (.inr posted)
      exact judged_holds judgedHere view

end Judged

/-! ## Every step, every reachable world -/

theorem domainCell_protected (config : Config) (id : Digest) : Protected (domainCell config.domain id) :=
  ObjectiveActivityCell.coordinate_reserved _ _ _

/-- Agreement on protected cells carries the invariant. -/
theorem domainsHold_transfer {config : Config} {P Q : Payloads} (agree : Agree P Q)
    (holds : DomainsHold config P) : DomainsHold config Q := by
  intro id domain view
  rw [← agree _ (domainCell_protected config id)] at view
  obtain ⟨indexed, joint⟩ := holds id domain view
  refine ⟨fun member inMembers => ?_, ?_⟩
  · obtain ⟨record, held, named⟩ := indexed member inMembers
    exact ⟨record, by rw [← agree _ (objectCell_protected config member)]; exact held, named⟩
  · have same : memberStates config Q domain.members = memberStates config P domain.members := by
      unfold memberStates
      exact List.map_congr_left fun member _ => by rw [agree _ (stateCell_protected config member)]
    rw [same]
    exact joint

/-- **Every committed step keeps every domain**: a kernel turn (its intent is `finish`'s output,
so `judgeDomains` admitted its posts), a seat turn's inert posts, an intent the ordinary gate
admits; installed or not. -/
theorem Step.domainsHold {rootBytes : Bytes → Digest} {config : Config} {before after : Snapshot rootBytes}
    (step : Step config before after) (holds : DomainsHold config (payloads before.canonicalBytes)) :
    DomainsHold config (payloads after.canonicalBytes) := by
  cases step with
  | turn turn sealing posts extra final schedule =>
    rcases execute_no_partial_data_commit schedule _
      (ActivitySeatEnd.AdmittedTurn.finalIntent sealing posts extra turn) with same | installed
    · rw [same]; exact holds
    · obtain ⟨_, _, _, _, judged, _, _⟩ := ActivitySeatEnd.finish_finalize final
      rw [installed, install_payloads _ (finalIntent_writes sealing)]
      exact judged_preserves judged holds
  | inert intent posts writes inert schedule =>
    rcases execute_no_partial_data_commit schedule _ intent with same | installed
    · rw [same]; exact holds
    · rw [installed, install_payloads _ writes, inert_agree inert]; exact holds
  | foreign intent admitted schedule =>
    refine domainsHold_transfer ?_ holds
    intro cell guarded
    unfold payloads
    rw [ObjectiveActivityGate.ordinary_execute_protected schedule _ admitted guarded]

/-- A genesis with no activity payload holds no domain. -/
theorem genesis_domainsHold {rootBytes : Bytes → Digest} {config : Config} {genesis : Snapshot rootBytes}
    (empty : ∀ cell, payloadOf (genesis.canonicalBytes cell) = none) :
    DomainsHold config (payloads genesis.canonicalBytes) := by
  intro id domain view
  unfold payloads at view
  rw [empty] at view
  cases view

theorem reachable_domainsHold {rootBytes : Bytes → Digest} {config : Config} {genesis snapshot : Snapshot rootBytes}
    (start : DomainsHold config (payloads genesis.canonicalBytes))
    (reachable : Reachable config genesis snapshot) : DomainsHold config (payloads snapshot.canonicalBytes) := by
  induction reachable with
  | genesis => exact start
  | step _ step holds => exact Step.domainsHold step holds

/-- **`domain_holds_forever`.** In every world reachable from a genesis that holds it, every
domain the kernel reads (`readDomain`) is named by each member's object record (`readObject`),
and its law holds on the members' declared states as the kernel reads them (`readState`). -/
theorem domain_holds_forever {rootBytes : Bytes → Digest} {config : Config} {genesis snapshot : Snapshot rootBytes}
    (start : DomainsHold config (payloads genesis.canonicalBytes))
    (reachable : Reachable config genesis snapshot) :
    ∀ id domain, readDomain config snapshot id = .ok (some domain) →
      (∀ member ∈ domain.members, ∃ record, readObject config snapshot member = .ok (some record) ∧
        id ∈ record.domains) ∧
      ∀ states, domain.members.mapM (readState config snapshot) = .ok states →
        JointHolds domain.law states := by
  intro id domain read
  have holds := reachable_domainsHold start reachable id domain (domainFor_view read)
  refine ⟨fun member inMembers => ?_, fun states mapped => ?_⟩
  · obtain ⟨record, held, named⟩ := holds.1 member inMembers
    exact ⟨record, objectView_readObject held, named⟩
  · have same : states = memberStates config (payloads snapshot.canonicalBytes) domain.members := by
      have := mapM_finalState (config := config) (snapshot := snapshot) (posts := []) domain.members states
        (by simpa [finalState, firstAt] using mapped)
      simpa [afterPosts] using this
    rw [same]
    exact holds.2

#assert_axioms stateFor_view objectFor_view view_objectFor domainFor_view view_domainFor mapM_finalState
  judged_holds records_keep changed_written judged_preserves domainsHold_transfer Step.domainsHold
  genesis_domainsHold reachable_domainsHold domain_holds_forever

end Minidregg.Kernel.ObjectiveDomainInvariant
