/-
# Theory.Renounce — a holder gives up a capability it holds

Revocation by the resource's management grant (`CapabilityRevocationController`)
is the founder's tool: kick. Renunciation is the holder's: the subject a
capability names, signing with its current key, revokes THAT capability and
nothing else. It needs no management grant and consults no policy.

The decision is `gate`: admitted iff a capability is stored at the named id,
its holder is exactly `.subject signer` (a bearer grant has no holder to
renounce it), its revocation key is registered, and it is not yet revoked. A
signer who does not hold the named id is refused `notHolder` whether or not the
id exists, so the gate reveals nothing about another subject's grants; the
revocation status of an id is revealed only to its holder (`alreadyRevoked`).

The write is the existing revocation record: one presence entry
`⟨.revoked, .capability id⟩` (`CredentialAuthorityEffects.RevokeDeclaration`).
The revoked set grows by exactly that key (`RevokedOne`). Everything delegated
from the capability dies with it by the existing lineage rule
(`ancestor_revocation_rejected`): a holder who delegated onward and then
renounces takes its delegates with it. Every capability outside that lineage is
admissible after exactly when it was before (`renounce_preserves_others`).

The revocation key is an identifier, not a secret: `RevocationKey.capability id`
is registered at issue by the issuing family (`registrationEntry`) and the gate
reads its registration from the cell. A renounce therefore does not depend on
the holder possessing any revocation secret; it depends on the holder's
current signing key (checked by the kernel, `Kernel.CapabilityRenounce`).
-/
import Theory.CredentialAuthorityEffects

namespace Minidregg.Theory.Renounce

open TypedAuthorization
open CredentialAuthorityState
open CredentialAuthorityEffects
open Minidregg.Theory.Store (Store Address)

set_option autoImplicit false

/-! ## The gate -/

inductive Reject where
  /-- The signer holds no capability at the named id: none is stored there, or
  the stored one names another holder (another subject, or a bearer). -/
  | notHolder
  /-- The holder's capability has no registered revocation key. -/
  | unregistered
  /-- The holder's capability is already revoked. -/
  | alreadyRevoked
  deriving DecidableEq, Repr

/-- The renounce decision on the stored capability at `id`, its registration
and revocation presence, and the authenticated signer. -/
def gate {kind : ResourceKind} (stored : Option (Capability kind)) (id : CapabilityId)
    (signer : SubjectId) (registered revoked : Bool) : Except Reject (Capability kind) :=
  match stored with
  | none => .error .notHolder
  | some cap =>
      if cap.id = id ∧ cap.holder = .subject signer then
        if registered then
          if revoked then .error .alreadyRevoked else .ok cap
        else .error .unregistered
      else .error .notHolder

/-- The gate at an authority cell: the stored capability of `kind` at `id`,
and the registration and revocation presence of its revocation key. -/
def gateAt {M : Materializer} (pre : Cell M) (kind : ResourceKind) (id : CapabilityId)
    (signer : SubjectId) : Except Reject (Capability kind) :=
  gate ((readCapability pre kind id).map StoredCapability.head) id signer
    (isRegistered pre (.capability id)) (isRevoked pre (.capability id))

theorem gate_ok_iff {kind : ResourceKind} (stored : Option (Capability kind)) (id : CapabilityId)
    (signer : SubjectId) (registered revoked : Bool) (cap : Capability kind) :
    gate stored id signer registered revoked = .ok cap ↔
      stored = some cap ∧ cap.id = id ∧ cap.holder = .subject signer ∧
        registered = true ∧ revoked = false := by
  constructor
  · intro admitted
    cases stored with
    | none => simp [gate] at admitted
    | some stored =>
        simp only [gate] at admitted
        split_ifs at admitted with held registeredTrue revokedTrue <;> cases admitted
        exact ⟨rfl, held.1, held.2, registeredTrue, by simpa using revokedTrue⟩
  · rintro ⟨rfl, idEq, holderEq, rfl, rfl⟩
    simp [gate, idEq, holderEq]

/-- **`renounce_requires_holder`.** An admitted renounce names a capability
stored at the id whose holder is exactly the signer. -/
theorem renounce_requires_holder {kind : ResourceKind} {stored : Option (Capability kind)}
    {id : CapabilityId} {signer : SubjectId} {registered revoked : Bool} {cap : Capability kind}
    (admitted : gate stored id signer registered revoked = .ok cap) :
    stored = some cap ∧ cap.id = id ∧ cap.holder = .subject signer := by
  obtain ⟨storedExact, idExact, holderExact, _, _⟩ :=
    (gate_ok_iff stored id signer registered revoked cap).1 admitted
  exact ⟨storedExact, idExact, holderExact⟩

/-- **`holder_cannot_renounce_others`.** A capability naming any other holder
(another subject, or a bearer) is refused `notHolder`, whatever its
registration or revocation presence: a non-holder learns nothing about it. -/
theorem holder_cannot_renounce_others {kind : ResourceKind} (cap : Capability kind)
    (id : CapabilityId) (signer : SubjectId) (registered revoked : Bool)
    (other : cap.holder ≠ .subject signer) :
    gate (some cap) id signer registered revoked = .error .notHolder := by
  simp only [gate]
  rw [if_neg (fun held => other held.2)]

/-- An id with no stored capability is refused with the same name. -/
theorem absent_refused_notHolder {kind : ResourceKind} (id : CapabilityId) (signer : SubjectId)
    (registered revoked : Bool) :
    gate (none : Option (Capability kind)) id signer registered revoked = .error .notHolder := rfl

/-- A revoked capability is refused to its holder by name. -/
theorem revoked_refused_alreadyRevoked {kind : ResourceKind} (cap : Capability kind)
    (id : CapabilityId) (signer : SubjectId)
    (held : cap.id = id ∧ cap.holder = .subject signer) :
    gate (some cap) id signer true true = .error .alreadyRevoked := by
  simp only [gate]
  rw [if_pos held]
  rfl

/-! ## The post: the revoked set grows by exactly one key -/

/-- `post` is `pre` with exactly one more revoked key and the same rows the
admission of a capability reads besides revocation. -/
structure RevokedOne (pre post : AuthState) (key : RevocationKey) : Prop where
  revoked : ∀ other, other ∈ post.revoked ↔ other = key ∨ other ∈ pre.revoked
  policyEpoch : post.policyEpoch = pre.policyEpoch
  issuerEpoch : post.issuerEpoch = pre.issuerEpoch
  parent : post.parent = pre.parent

/-- A capability is in the lineage of `id`: it is the capability `id`, or it was
delegated (transitively) from it. -/
def InLineage {kind : ResourceKind} (id : CapabilityId) (cap : Capability kind) : Prop :=
  cap.id = id ∨ id ∈ cap.ancestors

private theorem admissible_transfer {kind : ResourceKind} {before after : AuthState}
    {key : RevocationKey} (cap : Capability kind) (request : Request kind)
    (policyEpoch : after.policyEpoch = before.policyEpoch)
    (issuerEpoch : after.issuerEpoch = before.issuerEpoch)
    (parent : after.parent = before.parent)
    (revoked : ∀ other, other ≠ key → other ∈ after.revoked → other ∈ before.revoked)
    (selfOutside : RevocationKey.capability cap.id ≠ key)
    (ancestorsOutside : ∀ ancestor, ancestor ∈ cap.ancestors → RevocationKey.capability ancestor ≠ key)
    (channelsOutside : ∀ channel, RevocationKey.channel channel ≠ key)
    (admitted : cap.Admissible before request) : cap.Admissible after request where
  holder := admitted.holder
  scope := by rw [parent]; exact admitted.scope
  validFrom := admitted.validFrom
  validUntil := admitted.validUntil
  requestLaw := admitted.requestLaw
  policyCurrent := by rw [policyEpoch]; exact admitted.policyCurrent
  issuerCurrent := by rw [issuerEpoch]; exact admitted.issuerCurrent
  selfNotRevoked := fun member => admitted.selfNotRevoked (revoked _ selfOutside member)
  ancestorNotRevoked := fun ancestor isAncestor member =>
    admitted.ancestorNotRevoked ancestor isAncestor
      (revoked _ (ancestorsOutside ancestor isAncestor) member)
  channelNotRevoked := fun channel isChannel member =>
    admitted.channelNotRevoked channel isChannel (revoked _ (channelsOutside channel) member)

/-- **`renounce_preserves_others`.** Every capability outside the renounced
lineage is admissible after the renounce exactly when it was before, for every
request. -/
theorem renounce_preserves_others {pre post : AuthState} {id : CapabilityId}
    (one : RevokedOne pre post (.capability id)) {kind : ResourceKind} (cap : Capability kind)
    (outside : ¬ InLineage id cap) (request : Request kind) :
    cap.Admissible post request ↔ cap.Admissible pre request := by
  have selfOutside : RevocationKey.capability cap.id ≠ .capability id := by
    intro same
    injection same with same
    exact outside (Or.inl same)
  have ancestorsOutside : ∀ ancestor, ancestor ∈ cap.ancestors →
      RevocationKey.capability ancestor ≠ .capability id := by
    intro ancestor isAncestor same
    injection same with same
    subst same
    exact outside (Or.inr isAncestor)
  have channelsOutside : ∀ channel, RevocationKey.channel channel ≠ .capability id := by
    intro channel same
    cases same
  constructor
  · exact admissible_transfer cap request one.policyEpoch.symm one.issuerEpoch.symm one.parent.symm
      (fun other _ member => (one.revoked other).2 (Or.inr member))
      selfOutside ancestorsOutside channelsOutside
  · exact admissible_transfer cap request one.policyEpoch one.issuerEpoch one.parent
      (fun other different member => by
        rcases (one.revoked other).1 member with same | before
        · exact (different same).elim
        · exact before)
      selfOutside ancestorsOutside channelsOutside

/-- **`renounce_then_use_refused`.** After the renounce, the renounced
capability is refused for every request (its own revocation key is present). -/
theorem renounce_then_use_refused {pre post : AuthState} {id : CapabilityId}
    (one : RevokedOne pre post (.capability id)) {kind : ResourceKind} (cap : Capability kind)
    (same : cap.id = id) (request : Request kind) : ¬ cap.Admissible post request := by
  intro admitted
  apply admitted.selfNotRevoked
  rw [same]
  exact (one.revoked _).2 (Or.inl rfl)

/-- A delegate of the renounced capability dies with it (the existing lineage
rule). -/
theorem renounce_kills_delegates {pre post : AuthState} {id : CapabilityId}
    (one : RevokedOne pre post (.capability id)) {kind : ResourceKind} (cap : Capability kind)
    (delegated : id ∈ cap.ancestors) (request : Request kind) : ¬ cap.Admissible post request :=
  ancestor_revocation_rejected cap post request id delegated ((one.revoked _).2 (Or.inl rfl))

/-- **`renounce_revokes_exactly_lineage`.** The revoked set grows by exactly
the renounced capability's key; every capability in its lineage (itself and
everything delegated from it) is refused; every other capability's
admissibility is unchanged. -/
theorem renounce_revokes_exactly_lineage {pre post : AuthState} {id : CapabilityId}
    (one : RevokedOne pre post (.capability id)) :
    (∀ key, key ∈ post.revoked ↔ key = .capability id ∨ key ∈ pre.revoked) ∧
    (∀ (kind : ResourceKind) (cap : Capability kind) (request : Request kind),
      InLineage id cap → ¬ cap.Admissible post request) ∧
    (∀ (kind : ResourceKind) (cap : Capability kind) (request : Request kind),
      ¬ InLineage id cap → (cap.Admissible post request ↔ cap.Admissible pre request)) := by
  refine ⟨one.revoked, ?_, ?_⟩
  · intro kind cap request lineage
    rcases lineage with same | delegated
    · exact renounce_then_use_refused one cap same request
    · exact renounce_kills_delegates one cap delegated request
  · intro kind cap request outside
    exact renounce_preserves_others one cap outside request

/-! ## The cell: the revocation record, and it stays -/

theorem patch_post_logical {M : Materializer} {pre : Cell M} {root : Digest}
    {declaration : RevokeDeclaration}
    (validated : CellState.ValidatedPatch M pre root (declaration.patch pre.logical)) :
    validated.apply.logical = setAll pre.logical [declaration.revokedEntry] := by
  rw [CellState.ValidatedPatch.apply_logical]
  exact run_assignAll _ _

/-- The renounce's patch is the existing revocation record: `RevokeDeclaration`
for the capability's key. Its validated post is exactly `RevokedOne`. -/
theorem revokedOne_of_patch {M : Materializer} {pre : Cell M} {root : Digest}
    {declaration : RevokeDeclaration}
    (validated : CellState.ValidatedPatch M pre root (declaration.patch pre.logical)) :
    RevokedOne (authState pre) (authState validated.apply) declaration.key := by
  have post := patch_post_logical validated
  have rows : ∀ address : Address layout, address ≠ ⟨.revoked, declaration.key⟩ →
      validated.apply.logical address = pre.logical address := by
    intro address different
    rw [post]
    apply setAll_frame
    simp only [List.map_cons, List.map_nil, List.mem_singleton]
    exact different
  refine
    { revoked := ?_
      policyEpoch := ?_
      issuerEpoch := ?_
      parent := ?_ }
  · intro other
    rw [mem_authState_revoked_iff, mem_authState_revoked_iff]
    by_cases same : other = declaration.key
    · rw [same]
      have written : validated.apply.logical ⟨.revoked, declaration.key⟩ = some () := by
        rw [post]
        exact setAll_single _ _
      simp only [isRevoked]
      rw [written]
      exact ⟨fun _ => Or.inl trivial, fun _ => rfl⟩
    · have framed := rows ⟨.revoked, other⟩ (by intro h; injection h with _ h; exact same h)
      simp only [isRevoked]
      rw [framed]
      simp [same]
  · funext policy
    simp only [authState_policyEpoch]
    unfold policyEpochAt
    rw [rows ⟨.policyEpoch, policy⟩ (by intro h; cases h)]
  · funext issuer
    simp only [authState_issuerEpoch]
    unfold issuerEpochAt
    rw [rows ⟨.issuerEpoch, issuer⟩ (by intro h; cases h)]
  · exact parentageOf_congr fun cell => rows ⟨.parent, cell⟩ (by intro h; cases h)

/-- **`renounced_stays_revoked`.** The renounced key is in the post's revoked
set, and every later valid patch of the authority cell keeps it there (the
`revoked` plane is append-only): no admission resurrects it. Re-issue is a new
capability with a new id. -/
theorem renounced_stays_revoked {M : Materializer} {pre : Cell M} {root : Digest}
    {declaration : RevokeDeclaration}
    (validated : CellState.ValidatedPatch M pre root (declaration.patch pre.logical)) :
    declaration.key ∈ (authState validated.apply).revoked ∧
      ∀ patch : Store.Patch layout, Store.Patch.ValidFrom validated.apply.logical patch →
        Store.Patch.run validated.apply.logical patch ⟨.revoked, declaration.key⟩ = some () := by
  have written : validated.apply.logical ⟨.revoked, declaration.key⟩ = some () := by
    rw [patch_post_logical validated]
    exact setAll_single _ _
  refine ⟨(revokedOne_of_patch validated).revoked _ |>.2 (Or.inl rfl), ?_⟩
  intro patch valid
  exact revocation_permanent _ patch declaration.key valid written

/-- A second renounce of a revoked capability by its holder is refused
`alreadyRevoked` at the cell. -/
theorem second_renounce_refused {M : Materializer} (pre : Cell M) (kind : ResourceKind)
    (id : CapabilityId) (signer : SubjectId) (stored : StoredCapability kind)
    (storedExact : readCapability pre kind id = some stored)
    (held : stored.head.id = id ∧ stored.head.holder = .subject signer)
    (registered : isRegistered pre (.capability id) = true)
    (revoked : isRevoked pre (.capability id) = true) :
    gateAt pre kind id signer = .error .alreadyRevoked := by
  unfold gateAt
  rw [storedExact, registered, revoked]
  exact revoked_refused_alreadyRevoked stored.head id signer held

/-! ## Poles (concrete) -/

/-- The renounced state: the demo capability 20 (held by subject 4) renounced. -/
def renouncedState : AuthState := { demoState with revoked := {.capability ⟨20⟩} }

theorem renounced_revokedOne : RevokedOne demoState renouncedState (.capability ⟨20⟩) where
  revoked := by intro other; simp [renouncedState, demoState]
  policyEpoch := rfl
  issuerEpoch := rfl
  parent := rfl

/-- A grant capability 20 delegated onward (to subject 5). -/
def demoDelegate : Capability .object :=
  { demoCapability with
    id := ⟨22⟩
    parent := some ⟨20⟩
    holder := .subject ⟨5⟩
    ancestors := {⟨20⟩} }

/-- Satisfiable pole: the holder (subject 4) renounces its capability 20. -/
theorem holder_renounce_admitted :
    gate (some demoCapability) ⟨20⟩ ⟨4⟩ true false = .ok demoCapability := by
  rw [gate_ok_iff]
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Refuting pole: subject 5 (the delegate's holder) cannot renounce its
parent, capability 20. -/
theorem delegate_cannot_renounce_parent :
    gate (some demoCapability) ⟨20⟩ ⟨5⟩ true false = .error .notHolder :=
  holder_cannot_renounce_others demoCapability ⟨20⟩ ⟨5⟩ true false (by decide)

/-- Refuting pole: the holder of 20 cannot renounce its delegate 22, which
names subject 5. -/
theorem holder_cannot_renounce_delegate :
    gate (some demoDelegate) ⟨22⟩ ⟨4⟩ true false = .error .notHolder :=
  holder_cannot_renounce_others demoDelegate ⟨22⟩ ⟨4⟩ true false (by decide)

/-- Refuting pole: a bearer grant has no holder to renounce it. -/
theorem bearer_renounce_refused :
    gate (some { demoCapability with holder := .bearer }) ⟨20⟩ ⟨4⟩ true false = .error .notHolder :=
  holder_cannot_renounce_others _ ⟨20⟩ ⟨4⟩ true false (by decide)

/-- Refuting pole: a second renounce by the holder is refused by name. -/
theorem demo_second_renounce_refused :
    gate (some demoCapability) ⟨20⟩ ⟨4⟩ true true = .error .alreadyRevoked :=
  revoked_refused_alreadyRevoked demoCapability ⟨20⟩ ⟨4⟩ ⟨rfl, rfl⟩

/-- After the renounce the demo capability is refused. -/
theorem demo_renounced_use_refused : ¬ demoCapability.Admissible renouncedState demoRequest :=
  renounce_then_use_refused renounced_revokedOne demoCapability rfl demoRequest

/-- After the renounce the delegate is refused too. -/
theorem demo_delegate_dies (request : Request .object) :
    ¬ demoDelegate.Admissible renouncedState request :=
  renounce_kills_delegates renounced_revokedOne demoDelegate (by simp [demoDelegate]) request

/-- Another subject's renounce of its own capability 23 leaves capability 20
admissible: it is outside 23's lineage. -/
theorem demo_other_unaffected :
    demoCapability.Admissible { demoState with revoked := {.capability ⟨23⟩} } demoRequest := by
  have one : RevokedOne demoState { demoState with revoked := {.capability ⟨23⟩} }
      (.capability ⟨23⟩) :=
    { revoked := by intro other; simp [demoState]
      policyEpoch := rfl
      issuerEpoch := rfl
      parent := rfl }
  have outside : ¬ InLineage ⟨23⟩ demoCapability := by
    simp [InLineage, demoCapability]
  exact (renounce_preserves_others one demoCapability outside demoRequest).2
    demoCapability_admissible

/-- info: 'Minidregg.Theory.Renounce.gate_ok_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms gate_ok_iff
/-- info: 'Minidregg.Theory.Renounce.renounce_requires_holder' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms renounce_requires_holder
/-- info: 'Minidregg.Theory.Renounce.holder_cannot_renounce_others' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms holder_cannot_renounce_others
/-- info: 'Minidregg.Theory.Renounce.renounce_preserves_others' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms renounce_preserves_others
/-- info: 'Minidregg.Theory.Renounce.renounce_then_use_refused' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms renounce_then_use_refused
/-- info: 'Minidregg.Theory.Renounce.renounce_kills_delegates' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms renounce_kills_delegates
/-- info: 'Minidregg.Theory.Renounce.renounce_revokes_exactly_lineage' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms renounce_revokes_exactly_lineage
/-- info: 'Minidregg.Theory.Renounce.revokedOne_of_patch' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms revokedOne_of_patch
/-- info: 'Minidregg.Theory.Renounce.renounced_stays_revoked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms renounced_stays_revoked
/-- info: 'Minidregg.Theory.Renounce.second_renounce_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms second_renounce_refused
/-- info: 'Minidregg.Theory.Renounce.holder_renounce_admitted' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms holder_renounce_admitted
/-- info: 'Minidregg.Theory.Renounce.delegate_cannot_renounce_parent' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms delegate_cannot_renounce_parent
/-- info: 'Minidregg.Theory.Renounce.demo_delegate_dies' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms demo_delegate_dies
/-- info: 'Minidregg.Theory.Renounce.demo_other_unaffected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms demo_other_unaffected
/-- info: 'Minidregg.Theory.Renounce.absent_refused_notHolder' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms absent_refused_notHolder
/-- info: 'Minidregg.Theory.Renounce.revoked_refused_alreadyRevoked' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms revoked_refused_alreadyRevoked
/-- info: 'Minidregg.Theory.Renounce.holder_cannot_renounce_delegate' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms holder_cannot_renounce_delegate
/-- info: 'Minidregg.Theory.Renounce.bearer_renounce_refused' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms bearer_renounce_refused
/-- info: 'Minidregg.Theory.Renounce.demo_second_renounce_refused' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms demo_second_renounce_refused
/-- info: 'Minidregg.Theory.Renounce.demo_renounced_use_refused' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms demo_renounced_use_refused

end Minidregg.Theory.Renounce
