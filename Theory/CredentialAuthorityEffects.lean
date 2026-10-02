/-
# Theory.CredentialAuthorityEffects -- canonical authority mutations

Issuance, strict attenuation, authorized subject delegation, revocation,
and epoch rotation are ordinary
`AcceptedCellEffect` families over `CredentialAuthorityState.layout`.  Each
family writes one exact authority address in a validated `Store.Patch`; the
three creating families (issue, attenuate, delegate) also allocate the
`registered` entry of the capability they create, so "registered" is presence
in that plane and nothing else, and revocation requires it.  The family's
operation nullifier (`SemanticEffectFamily.nullifier`) is not written here:
the receiver lifts it into the durable protocol's append-only consumed set
(`CredentialAuthorityReplay.nullifier`), which refuses a second use, so the
authority cell does not grow per operation.  No receipt-side authority cache or
host callback can replace these Lean indices.

Every positive construction below is indexed by
`CredentialAuthorityState.authState pre`.  Consequently authorization,
capability membership, revocation, epochs, the request pre-root, and the patch
all consult the same canonical pre-cell.

Each family patch is a list of guarded assignments (`assignOp`): an address the
pre-store holds is overwritten by a `write` guarded at that exact prior value,
and an absent address is `allocate`d.  Every guard is read from the store the
operation's prefix produced, so a family patch is valid exactly at the pre-cell
it was generated from, and replaying it against any other value at a written
address is refused by `Patch.ValidFrom`.
-/
import Theory.CredentialAuthorityState
import Theory.CredentialLineageAdmission

namespace Minidregg.Theory.CredentialAuthorityEffects

open IndexedProgram
open TypedAuthorization
open CredentialAuthorityState
open CredentialAuthorityFamily
open CredentialLineageAdmission
open Minidregg.Theory.Store

/-! ## Common sealed family plumbing -/

def unitCodec : LawfulCodec Unit where
  encode := fun _ => []
  decode := fun bytes => if bytes = [] then some () else none
  decode_encode := by simp

def sealedOnly : DisclosureDecision Unit Unit (fun _ => Unit) → Prop
  | .sealed => True
  | .reveal _ _ => False
  | .declassify _ _ _ => False

/-- Canonical operation wrappers use eager nullifier identifiers.  The id is the
request nonce and the key the receiver consumes in the durable nullifier set. -/
abbrev OperationNullifier := Nat

/-- The deployment fixes the authority-control resource and ambient identity
in first-order data.  Each operation derives its argument address from the
whole lawful declaration codec, its nonce from its eager nullifier, and its
root from the exact canonical authority cell. -/
structure RequestContext where
  authority : EffectRequestContext
  argsDigestBytes : List UInt8 → Digest

def RequestContext.request {Declaration : Type}
    (context : RequestContext) (codec : LawfulCodec Declaration)
    (effectDigest : Declaration → Digest) (preRoot : Digest)
    (nonce : Nat) (declaration : Declaration) : PackedEffectRequest :=
  ⟨context.authority.kind,
    { context.authority.request
        (context.argsDigestBytes (codec.encode declaration))
        (effectDigest declaration) preRoot with nonce := nonce }⟩

variable {context : RequestContext}

/-! ## Guarded assignment over the authority layout -/

/-- Assign `value` at `address`, guarded at the value `store` holds there:
`write` from the exact prior value if present, `allocate` if absent. -/
def assignOp (store : Store layout) (address : Address layout)
    (value : layout.Value address.1) : Op layout :=
  match store address with
  | none => .allocate address.1 address.2 value
  | some before => .write address.1 address.2 before value

@[simp] theorem assignOp_writeAddress (store : Store layout) (address : Address layout)
    (value : layout.Value address.1) :
    (assignOp store address value).writeAddress? = some address := by
  unfold assignOp
  split <;> rfl

/-- No authority plane is ROM: each is RAM or append-only. -/
theorem discipline_ne_rom (plane : AuthorityPlane) : layout.discipline plane ≠ .rom := by
  cases plane <;> nofun

/-- An address may be assigned at `store` when its plane is RAM or it is absent
there.  A present address on an append-only plane (revoked,
registered) is not assignable: its only modification is an allocation. -/
def Assignable (store : Store layout) (address : Address layout) : Prop :=
  layout.discipline address.1 = .ram ∨ store address = none

/-- The guard of an assignment holds at the store it was generated from exactly
when the address is assignable there. -/
theorem assignOp_enabled (store : Store layout) (address : Address layout)
    (value : layout.Value address.1) (assignable : Assignable store address) :
    (assignOp store address value).Enabled store := by
  unfold assignOp
  split
  · rename_i absent
    exact ⟨discipline_ne_rom _, absent⟩
  · rename_i before present
    rcases assignable with ram | absent
    · exact ⟨ram, present⟩
    · rw [present] at absent
      cases absent

/-- Refuting pole: a present entry on an append-only plane cannot be assigned. -/
theorem assignOp_enabled_iff (store : Store layout) (address : Address layout)
    (value : layout.Value address.1) :
    (assignOp store address value).Enabled store ↔ Assignable store address := by
  refine ⟨fun enabled => ?_, assignOp_enabled store address value⟩
  unfold assignOp at enabled
  split at enabled
  · rename_i absent
    exact Or.inr absent
  · exact Or.inl enabled.1

@[simp] theorem assignOp_apply (store : Store layout) (address : Address layout)
    (value : layout.Value address.1) :
    (assignOp store address value).apply store = store.set address (some value) := by
  unfold assignOp
  split <;> rfl

/-- A guarded assignment is refused at any store whose value at the address
differs from the one it was generated against: the guard is not decorative. -/
theorem assignOp_not_enabled_of_ne (store other : Store layout) (address : Address layout)
    (value : layout.Value address.1) (different : other address ≠ store address) :
    ¬ (assignOp store address value).Enabled other := by
  unfold assignOp
  split
  · rename_i absent
    rintro ⟨_, fresh⟩
    exact different (fresh.trans absent.symm)
  · rename_i before present
    rintro ⟨_, prior⟩
    exact different (prior.trans present.symm)

/-- Guarded assignment of a list of entries, each guard read at the store its
prefix produced. -/
def assignAll : Store layout → List (Entry layout) → Patch layout
  | _, [] => []
  | store, entry :: rest =>
      assignOp store entry.1 entry.2 ::
        assignAll (store.set entry.1 (some entry.2)) rest

/-- A family patch is refused at any store that disagrees with the store it was
generated from at its first written address: e.g. an issuance replayed after
its capability slot moved. -/
theorem assignAll_refused_of_changed (store other : Store layout) (entry : Entry layout)
    (rest : List (Entry layout)) (changed : other entry.1 ≠ store entry.1) :
    ¬ Patch.ValidFrom other (assignAll store (entry :: rest)) :=
  fun valid => assignOp_not_enabled_of_ne store other entry.1 entry.2 changed valid.1

/-- Unconditional pointwise installation of entries, in order. -/
def setAll : Store layout → List (Entry layout) → Store layout
  | store, [] => store
  | store, entry :: rest => setAll (store.set entry.1 (some entry.2)) rest

/-- Every entry is assignable at the store its prefix produced. -/
def AssignableAll : Store layout → List (Entry layout) → Prop
  | _, [] => True
  | store, entry :: rest =>
      Assignable store entry.1 ∧ AssignableAll (store.set entry.1 (some entry.2)) rest

/-- A family patch is valid at the store it was generated from exactly when
every entry is assignable at its prefix: RAM planes always are, and an
append-only entry must be fresh. -/
theorem assignAll_valid_iff (store : Store layout) (entries : List (Entry layout)) :
    Patch.ValidFrom store (assignAll store entries) ↔ AssignableAll store entries := by
  induction entries generalizing store with
  | nil => exact Iff.rfl
  | cons entry rest ih =>
      change (assignOp store entry.1 entry.2).Enabled store ∧
          Patch.ValidFrom ((assignOp store entry.1 entry.2).apply store)
            (assignAll (store.set entry.1 (some entry.2)) rest) ↔ _
      rw [assignOp_apply, assignOp_enabled_iff, ih]
      rfl

theorem assignAll_valid (store : Store layout) (entries : List (Entry layout))
    (assignable : AssignableAll store entries) :
    Patch.ValidFrom store (assignAll store entries) :=
  (assignAll_valid_iff store entries).mpr assignable

/-- The one-entry families: a record assignable at the pre-store. -/
theorem assignableAll_single (store : Store layout) (record : Entry layout)
    (recordOk : Assignable store record.1) : AssignableAll store [record] :=
  ⟨recordOk, trivial⟩

/-- A run of RAM entries followed by one final entry is assignable exactly when
the final entry is assignable at the pre-store: RAM entries never share a plane
with an append-only one, so they cannot occupy its address first. -/
theorem assignableAll_ram_append_iff (store : Store layout) (ram : List (Entry layout)) (last : Entry layout)
    (allRam : ∀ entry ∈ ram, layout.discipline entry.1.1 = .ram) :
    AssignableAll store (ram ++ [last]) ↔ Assignable store last.1 := by
  induction ram generalizing store with
  | nil => exact ⟨fun both => both.1, fun lastOk => ⟨lastOk, trivial⟩⟩
  | cons entry rest ih =>
      have entryRam := allRam entry (List.mem_cons_self ..)
      have restRam : ∀ other ∈ rest, layout.discipline other.1.1 = .ram :=
        fun other member => allRam other (List.mem_cons_of_mem _ member)
      change Assignable store entry.1 ∧
          AssignableAll (store.set entry.1 (some entry.2)) (rest ++ [last]) ↔ _
      rw [ih _ restRam]
      constructor
      · rintro ⟨_, lastRam | absent⟩
        · exact Or.inl lastRam
        · by_cases same : last.1 = entry.1
          · exact Or.inl (same ▸ entryRam)
          · exact Or.inr ((Store.set_ne _ _ _ _ same).symm.trans absent)
      · intro lastOk
        refine ⟨Or.inl entryRam, ?_⟩
        rcases lastOk with lastRam | absent
        · exact Or.inl lastRam
        · by_cases same : last.1 = entry.1
          · exact Or.inl (same ▸ entryRam)
          · exact Or.inr ((Store.set_ne _ _ _ _ same).trans absent)

/-- A batch with pairwise distinct addresses is assignable when each entry is
assignable at the pre-store: no entry's prefix can occupy another's address. -/
theorem assignableAll_of_nodup (store : Store layout) (entries : List (Entry layout))
    (distinct : (entries.map Sigma.fst).Nodup)
    (each : ∀ entry ∈ entries, Assignable store entry.1) :
    AssignableAll store entries := by
  induction entries generalizing store with
  | nil => trivial
  | cons entry rest ih =>
      have pieces := List.nodup_cons.mp distinct
      refine ⟨each entry (List.mem_cons_self ..), ih _ pieces.2 fun other member => ?_⟩
      have different : other.1 ≠ entry.1 := fun same =>
        pieces.1 (List.mem_map.mpr ⟨other, member, same⟩)
      rcases each other (List.mem_cons_of_mem _ member) with ram | absent
      · exact Or.inl ram
      · exact Or.inr ((Store.set_ne _ _ _ _ different).trans absent)

/-- The last entry of an assignable batch is assignable at the store its prefix
produced. -/
theorem assignableAll_append_last (store : Store layout) (front : List (Entry layout)) (last : Entry layout)
    (assignable : AssignableAll store (front ++ [last])) :
    Assignable (setAll store front) last.1 := by
  induction front generalizing store with
  | nil => exact assignable.1
  | cons entry rest ih => exact ih _ assignable.2

theorem assignable_of_ram (store : Store layout) (address : Address layout)
    (ram : layout.discipline address.1 = .ram) : Assignable store address :=
  Or.inl ram

/-- A batch of RAM entries is assignable at every store. -/
theorem assignableAll_of_ram (store : Store layout) (entries : List (Entry layout))
    (allRam : ∀ entry ∈ entries, layout.discipline entry.1.1 = .ram) :
    AssignableAll store entries := by
  induction entries generalizing store with
  | nil => trivial
  | cons entry rest ih =>
      exact ⟨Or.inl (allRam entry (List.mem_cons_self ..)),
        ih _ fun other member => allRam other (List.mem_cons_of_mem _ member)⟩

theorem assignable_of_absent (store : Store layout) (address : Address layout)
    (absent : (store address).isSome = false) : Assignable store address :=
  Or.inr (Option.not_isSome_iff_eq_none.mp (by simp [absent]))

@[simp] theorem run_assignAll (store : Store layout) (entries : List (Entry layout)) :
    Patch.run store (assignAll store entries) = setAll store entries := by
  induction entries generalizing store with
  | nil => rfl
  | cons entry rest ih =>
      simp only [assignAll, setAll, Patch.run_cons, assignOp_apply]
      exact ih _

theorem assignAll_writeFootprint (store : Store layout) (entries : List (Entry layout)) :
    Patch.writeFootprint (assignAll store entries) = (entries.map Sigma.fst).toFinset := by
  induction entries generalizing store with
  | nil => rfl
  | cons entry rest ih =>
      have split : assignAll store (entry :: rest) =
          [assignOp store entry.1 entry.2] ++
            assignAll (store.set entry.1 (some entry.2)) rest := rfl
      rw [split, Patch.writeFootprint_append, ih]
      ext address
      simp [Patch.writeFootprint, eq_comm]

/-- Installing entries frames every address none of them names. -/
theorem setAll_frame (store : Store layout) (entries : List (Entry layout)) (address : Address layout)
    (outside : address ∉ entries.map Sigma.fst) :
    setAll store entries address = store address := by
  induction entries generalizing store with
  | nil => rfl
  | cons entry rest ih =>
      simp only [List.map_cons, List.mem_cons, not_or] at outside
      simp only [setAll]
      rw [ih _ outside.2]
      exact Store.set_ne _ _ _ _ outside.1

/-- In a batch with pairwise distinct addresses, every entry is installed
exactly. -/
theorem setAll_member (store : Store layout) (entries : List (Entry layout))
    (distinct : (entries.map Sigma.fst).Nodup) (entry : Entry layout) (member : entry ∈ entries) :
    setAll store entries entry.1 = some entry.2 := by
  induction entries generalizing store with
  | nil => simp at member
  | cons first rest ih =>
      have pieces := List.nodup_cons.mp distinct
      rcases List.mem_cons.mp member with same | inRest
      · subst same
        simp only [setAll]
        rw [setAll_frame _ rest _ pieces.1, Store.set_eq]
      · exact ih _ pieces.2 inRest

/-- The revoke and rotate families write exactly one entry: their authority record. -/
theorem setAll_single (store : Store layout) (record : Entry layout) :
    setAll store [record] record.1 = some record.2 := by
  simp only [setAll, Store.set_eq]

/-- A family patch generated from `pre` validates at `pre`'s own root and at no
other quoted root. -/
theorem validated_of_assign {M : Materializer} {pre : Cell M}
    {expectedPreRoot : Digest} (entries : List (Entry layout))
    (preRootExact : expectedPreRoot = pre.root)
    (assignable : AssignableAll pre.logical entries) :
    CellState.ValidatedPatch M pre expectedPreRoot (assignAll pre.logical entries) := by
  obtain ⟨validated, _⟩ := CellState.validate_accepts M pre expectedPreRoot
    (assignAll pre.logical entries) preRootExact (assignAll_valid _ _ assignable)
  exact validated

/-- The registration entry a creating family allocates for the revocation key
of the capability it creates.  `registered` is append-only, so this is an
allocation that no later patch can undo. -/
def registrationEntry (key : RevocationKey) : Entry layout :=
  ⟨⟨.registered, key⟩, ()⟩

/-- A creating family (a RAM record, then the registration of the created key)
is assignable at `pre` when the key is not yet registered. -/
theorem assignableAll_creation {M : Materializer} (pre : Cell M) (record : Entry layout)
    (key : RevocationKey)
    (recordRam : layout.discipline record.1.1 = .ram)
    (unregistered : isRegistered pre key = false) :
    AssignableAll pre.logical [record, registrationEntry key] := by
  have recordNotRegistration : (registrationEntry key).1 ≠ record.1 := by
    intro same
    have planes := congrArg Sigma.fst same
    change AuthorityPlane.registered = record.1.1 at planes
    rw [← planes] at recordRam
    cases recordRam
  refine ⟨Or.inl recordRam, ?_, trivial⟩
  unfold Assignable
  rw [Store.set_ne _ _ _ _ recordNotRegistration]
  exact Or.inr (Option.not_isSome_iff_eq_none.mp (by simpa [isRegistered] using unregistered))

/-- The two addresses of a creating family are distinct whenever its record is
on a RAM plane. -/
theorem creation_addresses_nodup (record : Entry layout) (key : RevocationKey)
    (recordRam : layout.discipline record.1.1 = .ram) :
    ([record, registrationEntry key].map Sigma.fst).Nodup := by
  have recordPlane : record.1.1 ≠ .registered := by
    intro same; rw [same] at recordRam; cases recordRam
  simp only [List.map_cons, List.map_nil, List.nodup_cons, List.mem_cons,
    or_false, List.not_mem_nil, not_false_eq_true, List.nodup_nil, and_true]
  exact fun same => recordPlane (congrArg Sigma.fst same)

/-- The applied post of a creating family holds each of its two entries. -/
theorem apply_creation_member {M : Materializer} {pre : Cell M} {expectedPreRoot : Digest}
    {record : Entry layout} {key : RevocationKey}
    (validated : CellState.ValidatedPatch M pre expectedPreRoot
      (assignAll pre.logical [record, registrationEntry key]))
    (recordRam : layout.discipline record.1.1 = .ram) (entry : Entry layout)
    (member : entry ∈ [record, registrationEntry key]) :
    validated.apply.logical entry.1 = some entry.2 := by
  rw [CellState.ValidatedPatch.apply_logical, run_assignAll]
  exact setAll_member _ _ (creation_addresses_nodup record key recordRam) entry member

/-- The applied post of a one-entry family patch holds its entry. -/
theorem apply_single {M : Materializer} {pre : Cell M} {expectedPreRoot : Digest}
    {record : Entry layout}
    (validated : CellState.ValidatedPatch M pre expectedPreRoot
      (assignAll pre.logical [record])) :
    validated.apply.logical record.1 = some record.2 := by
  rw [CellState.ValidatedPatch.apply_logical, run_assignAll]
  exact setAll_single _ _

/-! ## Capability issuance -/

structure IssueDeclaration (kind : ResourceKind) where
  capability : Capability kind
  expectedPreRoot : Digest
  operationNullifier : OperationNullifier

/-- The root capability record written by issuance. -/
def IssueDeclaration.capabilityEntry {kind : ResourceKind}
    (declaration : IssueDeclaration kind) : Entry layout :=
  ⟨⟨.capability kind, declaration.capability.id⟩,
    (⟨declaration.capability, []⟩ : StoredCapability kind)⟩

/-- Issuance writes the root record, registers the issued capability's own
revocation key, in one patch. -/
def IssueDeclaration.entries {kind : ResourceKind}
    (declaration : IssueDeclaration kind) : List (Entry layout) :=
  [declaration.capabilityEntry, registrationEntry (.capability declaration.capability.id)]

/-- The issuance patch generated from an authority store. -/
def IssueDeclaration.patch {kind : ResourceKind}
    (declaration : IssueDeclaration kind) (store : Store layout) : Patch layout :=
  assignAll store declaration.entries

@[simp] theorem IssueDeclaration.patch_writeFootprint {kind : ResourceKind}
    (declaration : IssueDeclaration kind) (store : Store layout) :
    Patch.writeFootprint (declaration.patch store) =
      {⟨.capability kind, declaration.capability.id⟩,
        ⟨.registered, .capability declaration.capability.id⟩} := by
  simp [IssueDeclaration.patch, assignAll_writeFootprint, IssueDeclaration.entries,
    IssueDeclaration.capabilityEntry, registrationEntry]

/-- Issuance is root-only, fresh and current-epoch.  The issued capability's own
key is not yet registered (issuance registers it); every ancestor and channel it
names is already registered and live, read from the planes (a root's ancestors
are revocation dependencies: a grant born under a room carries the creator's
room-grant lineage, so revoking that grant refuses it).  Single use is the
durable consumed set's, keyed by the operation nullifier. -/
structure IssueEvidence {M : Materializer}
    (pre : Cell M) {kind : ResourceKind}
    (declaration : IssueDeclaration kind) : Type where
  preRootExact : declaration.expectedPreRoot = pre.root
  slotFresh : CapabilityIdFresh pre declaration.capability.id
  rootParent : declaration.capability.parent = none
  rootSelf : declaration.capability.root = declaration.capability.id
  ancestorsRegistered : ∀ ancestor ∈ declaration.capability.ancestors,
    isRegistered pre (.capability ancestor) = true
  issuerCurrent : declaration.capability.issuerEpoch =
    issuerEpochAt pre declaration.capability.issuer
  policyCurrent : declaration.capability.policyEpoch =
    policyEpochAt pre declaration.capability.policyId
  selfUnregistered : isRegistered pre (.capability declaration.capability.id) = false
  channelsRegistered : ∀ channel ∈ declaration.capability.channels,
    isRegistered pre (.channel channel) = true
  selfLive : isRevoked pre (.capability declaration.capability.id) = false
  channelsLive : ∀ channel ∈ declaration.capability.channels,
    isRevoked pre (.channel channel) = false
  ancestorsLive : ∀ ancestor ∈ declaration.capability.ancestors,
    isRevoked pre (.capability ancestor) = false

theorem IssueEvidence.reject_existing_id {M : Materializer}
    {pre : Cell M} {kind : ResourceKind}
    {declaration : IssueDeclaration kind}
    (mode : IssueEvidence pre declaration)
    (otherKind : ResourceKind) (existing : StoredCapability otherKind)
    (present : readCapability pre otherKind declaration.capability.id = some existing) :
    False := by
  rw [mode.slotFresh otherKind] at present
  cases present

def issueFamily {M : Materializer} (pre : Cell M)
    {kind : ResourceKind} (codec : LawfulCodec (IssueDeclaration kind))
    (effectDigest : IssueDeclaration kind → Digest) (context : RequestContext) :
    SemanticEffectFamily layout M OperationNullifier where
  Declaration := IssueDeclaration kind
  declarationCodec := codec
  pre := pre
  request := fun declaration => context.request codec effectDigest pre.root
    declaration.operationNullifier declaration
  Outcome := fun _ => Unit
  outcomeCodec := fun _ => unitCodec
  ModeEvidence := fun declaration _ => IssueEvidence pre declaration
  Postcondition := fun declaration _ post =>
    (declaration.patch pre.logical).ResultAt pre.logical post
  effectDigest := effectDigest
  patch := fun declaration _ => declaration.patch pre.logical
  nullifier := fun declaration _ => some declaration.operationNullifier
  Release := fun _ _ => Unit
  DeclassificationAuthority := fun _ _ => Unit
  ReleaseAuthorization := fun _ _ _ => Unit
  DisclosureAllowed := fun _ _ => sealedOnly

/-- Positive issuance path.  The validator token is derived from the patch
generated at the canonical pre-cell, quoted at the request's pre-root. -/
def acceptIssue
    {M : Materializer} (pre : Cell M)
    (context : RequestContext)
    {portal : Portal} {kind : ResourceKind} {request : Request kind}
    (codec : LawfulCodec (IssueDeclaration kind))
    (effectDigest : IssueDeclaration kind → Digest)
    (declaration : IssueDeclaration kind)
    (authorization : Authorized portal (authState pre) request)
    (requestBound : (⟨kind, request⟩ : PackedEffectRequest) =
      context.request codec effectDigest pre.root declaration.operationNullifier declaration)
    (requestDigestExact : request.effectsDigest = effectDigest declaration)
    (requestPreExact : request.preStateRoot = pre.root)
    (modeEvidence : IssueEvidence pre declaration) :
    AcceptedCellEffect (portal := portal) (authState := authState pre)
      (issueFamily pre codec effectDigest context) request pre declaration () where
  authorization := authorization
  preStateBound := rfl
  requestBound := requestBound
  effectsDigestBound := requestDigestExact
  modeEvidence := modeEvidence
  validated := validated_of_assign declaration.entries requestPreExact
    (assignableAll_creation pre _ _ rfl modeEvidence.selfUnregistered)
  postcondition := CellState.ValidatedPatch.resultAt _
  disclosure := .sealed
  disclosureAllowed := trivial

/-! ## Strict capability attenuation -/

structure AttenuateDeclaration (kind : ResourceKind) where
  child : Capability kind
  parentId : CapabilityId
  expectedPreRoot : Digest
  operationNullifier : OperationNullifier

def descendedCapability {kind : ResourceKind} (child : Capability kind)
    (parent : StoredCapability kind) : StoredCapability kind :=
  ⟨child, ⟨parent.head, .strict⟩ :: parent.ancestry⟩

def AttenuateDeclaration.capabilityEntry {kind : ResourceKind}
    (declaration : AttenuateDeclaration kind) (parent : StoredCapability kind) : Entry layout :=
  ⟨⟨.capability kind, declaration.child.id⟩, descendedCapability declaration.child parent⟩

def AttenuateDeclaration.entries {kind : ResourceKind}
    (declaration : AttenuateDeclaration kind) (parent : StoredCapability kind) :
    List (Entry layout) :=
  [declaration.capabilityEntry parent, registrationEntry (.capability declaration.child.id)]

def AttenuateDeclaration.patch {kind : ResourceKind}
    (declaration : AttenuateDeclaration kind)
    (parent : StoredCapability kind) (store : Store layout) : Patch layout :=
  assignAll store (declaration.entries parent)

@[simp] theorem AttenuateDeclaration.patch_writeFootprint {kind : ResourceKind}
    (declaration : AttenuateDeclaration kind) (parent : StoredCapability kind)
    (store : Store layout) :
    Patch.writeFootprint (declaration.patch parent store) =
      {⟨.capability kind, declaration.child.id⟩,
        ⟨.registered, .capability declaration.child.id⟩} := by
  simp [AttenuateDeclaration.patch, assignAll_writeFootprint, AttenuateDeclaration.entries,
    AttenuateDeclaration.capabilityEntry, registrationEntry]

/-- Shared pre-state requirements for strict narrowing and explicit
subject delegation. Both use the same canonical lookup, anchored lineage,
across-kind identity freshness and current revocation/epoch planes.  The
child's own key is not yet registered (the family registers it); its ancestors
and channels are registered and live, read from the planes. -/
structure DescentEvidence {M : Materializer}
    (pre : Cell M) {kind : ResourceKind} (expectedPreRoot : Digest)
    (parentId : CapabilityId) (child : Capability kind)
    (parent : StoredCapability kind) : Type where
  preRootExact : expectedPreRoot = pre.root
  parentExact : readCapability pre kind parentId = some parent
  parentIdExact : parent.head.id = parentId
  parentLineageValid : LineageValid (authState pre).parent parent
  parentLineageAnchored : LineageAnchored pre parent
  childSlotFresh : CapabilityIdFresh pre child.id
  issuerCurrent : child.issuerEpoch = issuerEpochAt pre child.issuer
  policyCurrent : child.policyEpoch = policyEpochAt pre child.policyId
  selfUnregistered : isRegistered pre (.capability child.id) = false
  ancestorsRegistered : ∀ ancestor ∈ child.ancestors,
    isRegistered pre (.capability ancestor) = true
  channelsRegistered : ∀ channel ∈ child.channels,
    isRegistered pre (.channel channel) = true
  selfLive : isRevoked pre (.capability child.id) = false
  ancestorsLive : ∀ ancestor ∈ child.ancestors,
    isRevoked pre (.capability ancestor) = false
  channelsLive : ∀ channel ∈ child.channels,
    isRevoked pre (.channel channel) = false

theorem DescentEvidence.reject_existing_child {M : Materializer}
    {pre : Cell M} {kind : ResourceKind}
    {expectedPreRoot : Digest} {parentId : CapabilityId} {child : Capability kind}
    {parent : StoredCapability kind}
    (mode : DescentEvidence pre expectedPreRoot parentId child parent)
    (otherKind : ResourceKind) (existing : StoredCapability otherKind)
    (present : readCapability pre otherKind child.id = some existing) : False := by
  rw [mode.childSlotFresh otherKind] at present
  cases present

/-- Fresh capability production preserves every already-present capability,
even when storage kinds differ. This is the shared frame fact needed to keep
canonical ancestry anchored after appending a child. -/
theorem capabilityProduction_preserves_present {M : Materializer}
    {pre : Cell M} {expectedPreRoot : Digest} {patch : Patch layout}
    {kind : ResourceKind} {identifier : CapabilityId}
    (validated : CellState.ValidatedPatch M pre expectedPreRoot patch)
    (footprint : Patch.writeFootprint patch =
      {⟨.capability kind, identifier⟩, ⟨.registered, .capability identifier⟩})
    (fresh : CapabilityIdFresh pre identifier)
    (otherKind : ResourceKind) (otherId : CapabilityId)
    (stored : StoredCapability otherKind)
    (present : readCapability pre otherKind otherId = some stored) :
    readCapability validated.apply otherKind otherId = some stored := by
  have different : (⟨.capability otherKind, otherId⟩ : Address layout) ≠
      ⟨.capability kind, identifier⟩ := by
    intro same
    have sameId : otherId = identifier := by
      simp only [Sigma.mk.injEq, AuthorityPlane.capability.injEq] at same
      rcases same with ⟨rfl, same⟩
      exact eq_of_heq same
    subst otherId
    rw [fresh otherKind] at present
    cases present
  calc
    readCapability validated.apply otherKind otherId =
        readCapability pre otherKind otherId :=
      Patch.run_frame pre.logical patch ⟨.capability otherKind, otherId⟩ (by
        intro member
        rw [footprint] at member
        rcases Finset.mem_insert.mp member with same | registration
        · exact different same
        · have impossible := Finset.mem_singleton.mp registration
          cases impossible)
    _ = some stored := present

/-- The strict operation retains its original holder-narrowing relation. -/
structure AttenuateEvidence {M : Materializer}
    (pre : Cell M) {kind : ResourceKind}
    (declaration : AttenuateDeclaration kind) (parent : StoredCapability kind)
    extends DescentEvidence pre declaration.expectedPreRoot declaration.parentId
      declaration.child parent where
  strict : declaration.child.StrictAttenuates parent.head (authState pre).parent

theorem AttenuateEvidence.childLineageAnchored {M : Materializer}
    {pre : Cell M} {kind : ResourceKind}
    {declaration : AttenuateDeclaration kind} {parent : StoredCapability kind}
    {expectedPreRoot : Digest}
    (evidence : AttenuateEvidence pre declaration parent)
    (validated : CellState.ValidatedPatch M pre expectedPreRoot
      (declaration.patch parent pre.logical)) :
    LineageAnchored validated.apply (descendedCapability declaration.child parent) := by
  have preserved := capabilityProduction_preserves_present validated
    (declaration.patch_writeFootprint parent pre.logical) evidence.childSlotFresh
  have parentPresent : readCapability pre kind parent.head.id = some parent := by
    rw [evidence.parentIdExact]
    exact evidence.parentExact
  change readCapability validated.apply kind parent.head.id = some parent ∧
    LineageAnchored validated.apply parent
  exact ⟨preserved kind parent.head.id parent parentPresent,
    evidence.parentLineageAnchored.of_present_reads_preserved preserved⟩

def attenuateFamily {M : Materializer} (pre : Cell M)
    {kind : ResourceKind} (codec : LawfulCodec (AttenuateDeclaration kind))
    (parentCodec : LawfulCodec (StoredCapability kind))
    (effectDigest : AttenuateDeclaration kind → Digest) (context : RequestContext) :
    SemanticEffectFamily layout M OperationNullifier where
  Declaration := AttenuateDeclaration kind
  declarationCodec := codec
  pre := pre
  request := fun declaration => context.request codec effectDigest pre.root
    declaration.operationNullifier declaration
  Outcome := fun _ => StoredCapability kind
  outcomeCodec := fun _ => parentCodec
  ModeEvidence := fun declaration parent =>
    AttenuateEvidence pre declaration parent
  Postcondition := fun declaration parent post =>
    (declaration.patch parent pre.logical).ResultAt pre.logical post ∧
    LineageAnchored (CellState.materialize M post)
      (descendedCapability declaration.child parent)
  effectDigest := effectDigest
  patch := fun declaration parent => declaration.patch parent pre.logical
  nullifier := fun declaration _ => some declaration.operationNullifier
  Release := fun _ _ => Unit
  DeclassificationAuthority := fun _ _ => Unit
  ReleaseAuthorization := fun _ _ _ => Unit
  DisclosureAllowed := fun _ _ => sealedOnly

def acceptAttenuation
    {M : Materializer} (pre : Cell M)
    (context : RequestContext)
    {portal : Portal} {kind : ResourceKind} {request : Request kind}
    (codec : LawfulCodec (AttenuateDeclaration kind))
    (parentCodec : LawfulCodec (StoredCapability kind))
    (effectDigest : AttenuateDeclaration kind → Digest)
    (declaration : AttenuateDeclaration kind)
    (parent : StoredCapability kind)
    (authorization : Authorized portal (authState pre) request)
    (requestBound : (⟨kind, request⟩ : PackedEffectRequest) =
      context.request codec effectDigest pre.root declaration.operationNullifier declaration)
    (requestDigestExact : request.effectsDigest = effectDigest declaration)
    (requestPreExact : request.preStateRoot = pre.root)
    (modeEvidence : AttenuateEvidence pre declaration parent) :
    AcceptedCellEffect (portal := portal) (authState := authState pre)
      (attenuateFamily pre codec parentCodec effectDigest context)
      request pre declaration parent := by
  have validated := validated_of_assign (M := M) (pre := pre)
    (declaration.entries parent) requestPreExact
    (assignableAll_creation pre _ _ rfl modeEvidence.selfUnregistered)
  exact
    { authorization := authorization
      preStateBound := rfl
      requestBound := requestBound
      effectsDigestBound := requestDigestExact
      modeEvidence := modeEvidence
      validated := validated
      postcondition := ⟨validated.resultAt, modeEvidence.childLineageAnchored validated⟩
      disclosure := .sealed
      disclosureAllowed := trivial }

theorem AttenuateEvidence.childLineageValid {M : Materializer}
    {pre : Cell M} {kind : ResourceKind}
    {declaration : AttenuateDeclaration kind}
    {parent : StoredCapability kind}
    (evidence : AttenuateEvidence pre declaration parent) :
    LineageValid (authState pre).parent (descendedCapability declaration.child parent) :=
  .attenuate declaration.child parent.head parent.ancestry
    evidence.parentLineageValid evidence.strict

/-! ## Explicit authorized subject delegation -/

structure DelegateDeclaration (kind : ResourceKind) where
  child : Capability kind
  parentId : CapabilityId
  target : ResourceId kind
  expectedPreRoot : Digest
  operationNullifier : OperationNullifier

/-- Ambient values are fixed by the receiving source before a complete request
is built. Target, verb, nonce, policy, arguments, effects and root are derived
from the typed declaration and actual pre-state, not a request callback. -/
structure DelegationContext where
  domain : Digest
  semantics : Digest
  federation : FederationId
  subject : SubjectId
  subjectKeyEpoch : Epoch
  height : Height
  cost : Nat
  argsDigestBytes : List UInt8 → Digest

def DelegationContext.request (context : DelegationContext) {M : Materializer} {kind : ResourceKind}
    (codec : LawfulCodec (DelegateDeclaration kind))
    (effectDigest : DelegateDeclaration kind → Digest) (pre : Cell M)
    (declaration : DelegateDeclaration kind) : Request kind where
  domain := context.domain
  semantics := context.semantics
  federation := context.federation
  subject := context.subject
  subjectKeyEpoch := context.subjectKeyEpoch
  target := declaration.target
  verb := delegateVerb kind
  argsDigest := context.argsDigestBytes (codec.encode declaration)
  effectsDigest := effectDigest declaration
  nonce := declaration.operationNullifier
  height := context.height
  preStateRoot := pre.root
  policyId := declaration.child.policyId
  policyEpoch := declaration.child.policyEpoch
  policyRevision := policyRevisionAt pre declaration.child.policyId
  cost := context.cost

def delegatedCapability {kind : ResourceKind} (child : Capability kind)
    (parent : StoredCapability kind) (request : Request kind) : StoredCapability kind :=
  ⟨child, ⟨parent.head, .delegated request⟩ :: parent.ancestry⟩

def DelegateDeclaration.capabilityEntry {kind : ResourceKind}
    (declaration : DelegateDeclaration kind) (parent : StoredCapability kind)
    (request : Request kind) : Entry layout :=
  ⟨⟨.capability kind, declaration.child.id⟩,
    delegatedCapability declaration.child parent request⟩

def DelegateDeclaration.entries {kind : ResourceKind}
    (declaration : DelegateDeclaration kind) (parent : StoredCapability kind)
    (request : Request kind) : List (Entry layout) :=
  [declaration.capabilityEntry parent request,
    registrationEntry (.capability declaration.child.id)]

def DelegateDeclaration.patch {kind : ResourceKind}
    (declaration : DelegateDeclaration kind) (parent : StoredCapability kind)
    (request : Request kind) (store : Store layout) : Patch layout :=
  assignAll store (declaration.entries parent request)

@[simp] theorem DelegateDeclaration.patch_writeFootprint {kind : ResourceKind}
    (declaration : DelegateDeclaration kind) (parent : StoredCapability kind)
    (request : Request kind) (store : Store layout) :
    Patch.writeFootprint (declaration.patch parent request store) =
      {⟨.capability kind, declaration.child.id⟩,
        ⟨.registered, .capability declaration.child.id⟩} := by
  simp [DelegateDeclaration.patch, assignAll_writeFootprint, DelegateDeclaration.entries,
    DelegateDeclaration.capabilityEntry, registrationEntry]

/-- The parent invocation is mandatory inside family mode evidence, not only
inside a convenience constructor. Its commitment is the one verified by the
same source portal's exact stored-capability check; an unrelated signature,
proof token or another capability cannot discharge `parentNamed`. -/
structure DelegationEvidence {M : Materializer}
    (pre : Cell M) (portal : Portal) (context : DelegationContext)
    {kind : ResourceKind} (codec : LawfulCodec (DelegateDeclaration kind))
    (effectDigest : DelegateDeclaration kind → Digest)
    (declaration : DelegateDeclaration kind) (parent : StoredCapability kind)
    extends DescentEvidence pre declaration.expectedPreRoot declaration.parentId
      declaration.child parent where
  parentCommitment : Digest
  parentAuthorization : Authorized portal (authState pre)
    (context.request codec effectDigest pre declaration)
  parentNamed : parentAuthorization.evidence.capabilityValue =
    some (parent.head, parentCommitment)
  shape : DelegationShape (context.request codec effectDigest pre declaration)
    declaration.child parent.head (authState pre).parent

theorem DelegationEvidence.childLineageValid {M : Materializer}
    {pre : Cell M} {portal : Portal}
    {context : DelegationContext} {kind : ResourceKind}
    {codec : LawfulCodec (DelegateDeclaration kind)}
    {effectDigest : DelegateDeclaration kind → Digest}
    {declaration : DelegateDeclaration kind} {parent : StoredCapability kind}
    (evidence : DelegationEvidence pre portal context codec effectDigest declaration parent) :
    LineageValid (authState pre).parent (delegatedCapability declaration.child parent
      (context.request codec effectDigest pre declaration)) :=
  .delegate declaration.child parent.head parent.ancestry
    (context.request codec effectDigest pre declaration)
    evidence.parentLineageValid evidence.shape

theorem DelegationEvidence.childLineageAnchored {M : Materializer}
    {pre : Cell M} {portal : Portal}
    {context : DelegationContext} {kind : ResourceKind}
    {codec : LawfulCodec (DelegateDeclaration kind)}
    {effectDigest : DelegateDeclaration kind → Digest}
    {declaration : DelegateDeclaration kind} {parent : StoredCapability kind}
    {expectedPreRoot : Digest}
    (evidence : DelegationEvidence pre portal context codec effectDigest declaration parent)
    (validated : CellState.ValidatedPatch M pre expectedPreRoot
      (declaration.patch parent (context.request codec effectDigest pre declaration)
        pre.logical)) :
    LineageAnchored validated.apply (delegatedCapability declaration.child parent
      (context.request codec effectDigest pre declaration)) := by
  have preserved := capabilityProduction_preserves_present validated
    (declaration.patch_writeFootprint parent _ pre.logical) evidence.childSlotFresh
  have parentPresent : readCapability pre kind parent.head.id = some parent := by
    rw [evidence.parentIdExact]
    exact evidence.parentExact
  change readCapability validated.apply kind parent.head.id = some parent ∧
    LineageAnchored validated.apply parent
  exact ⟨preserved kind parent.head.id parent parentPresent,
    evidence.parentLineageAnchored.of_present_reads_preserved preserved⟩

def delegateFamily {M : Materializer} (pre : Cell M)
    (portal : Portal) (context : DelegationContext) {kind : ResourceKind}
    (codec : LawfulCodec (DelegateDeclaration kind))
    (parentCodec : LawfulCodec (StoredCapability kind))
    (effectDigest : DelegateDeclaration kind → Digest) :
    SemanticEffectFamily layout M OperationNullifier where
  Declaration := DelegateDeclaration kind
  declarationCodec := codec
  pre := pre
  request := fun declaration =>
    ⟨kind, context.request codec effectDigest pre declaration⟩
  Outcome := fun _ => StoredCapability kind
  outcomeCodec := fun _ => parentCodec
  ModeEvidence := fun declaration parent =>
    DelegationEvidence pre portal context codec effectDigest declaration parent
  Postcondition := fun declaration parent post =>
    (declaration.patch parent (context.request codec effectDigest pre declaration)
      pre.logical).ResultAt pre.logical post ∧
    LineageAnchored (CellState.materialize M post) (delegatedCapability declaration.child parent
      (context.request codec effectDigest pre declaration))
  effectDigest := effectDigest
  patch := fun declaration parent =>
    declaration.patch parent (context.request codec effectDigest pre declaration) pre.logical
  nullifier := fun declaration _ => some declaration.operationNullifier
  Release := fun _ _ => Unit
  DeclassificationAuthority := fun _ _ => Unit
  ReleaseAuthorization := fun _ _ _ => Unit
  DisclosureAllowed := fun _ _ => sealedOnly

/-- This constructor uses the exact parent grant already retained inside mode.
It accepts neither a caller-selected request nor replacement authorization. -/
def acceptDelegation {M : Materializer}
    (pre : Cell M) (portal : Portal)
    (context : DelegationContext) {kind : ResourceKind}
    (codec : LawfulCodec (DelegateDeclaration kind))
    (parentCodec : LawfulCodec (StoredCapability kind))
    (effectDigest : DelegateDeclaration kind → Digest)
    (declaration : DelegateDeclaration kind) (parent : StoredCapability kind)
    (mode : DelegationEvidence pre portal context codec effectDigest declaration parent) :
    AcceptedCellEffect (portal := portal) (authState := authState pre)
      (delegateFamily pre portal context codec parentCodec effectDigest)
      (context.request codec effectDigest pre declaration) pre declaration parent := by
  let request := context.request codec effectDigest pre declaration
  have validated := validated_of_assign (M := M) (pre := pre)
    (expectedPreRoot := request.preStateRoot) (declaration.entries parent request) rfl
    (assignableAll_creation pre _ _ rfl mode.selfUnregistered)
  exact
    { authorization := mode.parentAuthorization
      preStateBound := rfl
      requestBound := rfl
      effectsDigestBound := rfl
      modeEvidence := mode
      validated := validated
      postcondition := ⟨validated.resultAt, mode.childLineageAnchored validated⟩
      disclosure := .sealed
      disclosureAllowed := trivial }

theorem DelegationEvidence.parent_use_verified {M : Materializer}
    {pre : Cell M} {portal : Portal}
    {context : DelegationContext} {kind : ResourceKind}
    {codec : LawfulCodec (DelegateDeclaration kind)}
    {effectDigest : DelegateDeclaration kind → Digest}
    {declaration : DelegateDeclaration kind} {parent : StoredCapability kind}
    (mode : DelegationEvidence pre portal context codec effectDigest declaration parent) :
    ∃ witness, portal.verifyCapabilityUse
      (context.request codec effectDigest pre declaration) parent.head
      mode.parentCommitment witness = true :=
  capability_evidence_requires_use mode.parentAuthorization.evidence
    parent.head mode.parentCommitment mode.parentNamed

theorem DelegationEvidence.reject_missing_delegate {M : Materializer}
    {pre : Cell M} {portal : Portal}
    {context : DelegationContext} {kind : ResourceKind}
    {codec : LawfulCodec (DelegateDeclaration kind)}
    {effectDigest : DelegateDeclaration kind → Digest}
    {declaration : DelegateDeclaration kind} {parent : StoredCapability kind}
    (mode : DelegationEvidence pre portal context codec effectDigest declaration parent)
    (missing : delegateVerb kind ∉ parent.head.scope.verbs) : False :=
  missing mode.shape.requires_delegate_verb

theorem DelegationEvidence.reject_non_capability_mode {M : Materializer}
    {pre : Cell M} {portal : Portal}
    {context : DelegationContext} {kind : ResourceKind}
    {codec : LawfulCodec (DelegateDeclaration kind)}
    {effectDigest : DelegateDeclaration kind → Digest}
    {declaration : DelegateDeclaration kind} {parent : StoredCapability kind}
    (mode : DelegationEvidence pre portal context codec effectDigest declaration parent)
    (notCapability : mode.parentAuthorization.evidence.capabilityValue = none) : False := by
  have named := mode.parentNamed
  rw [notCapability] at named
  cases named

section DelegationObligations

variable {M : Materializer} {pre : Cell M}
  {portal : Portal} {context : DelegationContext} {kind : ResourceKind}
  {codec : LawfulCodec (DelegateDeclaration kind)}
  {effectDigest : DelegateDeclaration kind → Digest}
  {declaration : DelegateDeclaration kind} {parent : StoredCapability kind}

/-- The mandatory mode opens and authorizes the same exact parent, whose full
retained suffix is checked against the same canonical pre-state. -/
theorem DelegationEvidence.parent_exact
    (mode : DelegationEvidence pre portal context codec effectDigest declaration parent) :
    readCapability pre kind declaration.parentId = some parent ∧
      mode.parentAuthorization.evidence.capabilityValue =
        some (parent.head, mode.parentCommitment) ∧
      LineageValid (authState pre).parent parent ∧ LineageAnchored pre parent :=
  ⟨mode.parentExact, mode.parentNamed, mode.parentLineageValid, mode.parentLineageAnchored⟩

theorem DelegationEvidence.reject_wrong_parent
    (mode : DelegationEvidence pre portal context codec effectDigest declaration parent)
    (actual : StoredCapability kind)
    (present : readCapability pre kind declaration.parentId = some actual)
    (different : actual ≠ parent) : False := by
  exact different (Option.some.inj (present.symm.trans mode.parentExact))

theorem DelegationEvidence.reject_wrong_grantor
    (mode : DelegationEvidence pre portal context codec effectDigest declaration parent)
    (different : parent.head.holder ≠ .subject context.subject) : False :=
  different mode.shape.grantor

theorem DelegationEvidence.reject_bearer_child
    (mode : DelegationEvidence pre portal context codec effectDigest declaration parent)
    (bearer : declaration.child.holder = .bearer) : False :=
  mode.shape.recipient bearer

theorem DelegationEvidence.child_bounds
    (mode : DelegationEvidence pre portal context codec effectDigest declaration parent) :
    Capability.LineageBounds declaration.child parent.head (authState pre).parent :=
  mode.shape.payload.lineageBounds

end DelegationObligations

@[simp] theorem delegation_post_capability_exact {M : Materializer}
    {pre : Cell M} {portal : Portal}
    {context : DelegationContext} {kind : ResourceKind}
    {codec : LawfulCodec (DelegateDeclaration kind)}
    {parentCodec : LawfulCodec (StoredCapability kind)}
    {effectDigest : DelegateDeclaration kind → Digest}
    {declaration : DelegateDeclaration kind} {parent : StoredCapability kind}
    (accepted : AcceptedCellEffect (portal := portal) (authState := authState pre)
      (delegateFamily pre portal context codec parentCodec effectDigest)
      (context.request codec effectDigest pre declaration) pre declaration parent) :
    readCapability accepted.prepared.post kind declaration.child.id =
      some (delegatedCapability declaration.child parent
        (context.request codec effectDigest pre declaration)) :=
  apply_creation_member accepted.validated rfl
    (declaration.capabilityEntry parent (context.request codec effectDigest pre declaration))
    (List.mem_cons_self ..)

/-- **Delegation registers** the delegated child's own revocation key. -/
@[simp] theorem delegation_post_registered {M : Materializer}
    {pre : Cell M} {portal : Portal}
    {context : DelegationContext} {kind : ResourceKind}
    {codec : LawfulCodec (DelegateDeclaration kind)}
    {parentCodec : LawfulCodec (StoredCapability kind)}
    {effectDigest : DelegateDeclaration kind → Digest}
    {declaration : DelegateDeclaration kind} {parent : StoredCapability kind}
    (accepted : AcceptedCellEffect (portal := portal) (authState := authState pre)
      (delegateFamily pre portal context codec parentCodec effectDigest)
      (context.request codec effectDigest pre declaration) pre declaration parent) :
    isRegistered accepted.prepared.post (.capability declaration.child.id) = true := by
  have written : accepted.validated.apply.logical
      ⟨.registered, .capability declaration.child.id⟩ = some () :=
    apply_creation_member accepted.validated rfl
      (registrationEntry (.capability declaration.child.id)) (by simp)
  simp only [isRegistered, AcceptedCellEffect.prepared_post, written]
  rfl

theorem delegation_post_lineage_valid {M : Materializer}
    {pre : Cell M} {portal : Portal}
    {context : DelegationContext} {kind : ResourceKind}
    {codec : LawfulCodec (DelegateDeclaration kind)}
    {parentCodec : LawfulCodec (StoredCapability kind)}
    {effectDigest : DelegateDeclaration kind → Digest}
    {declaration : DelegateDeclaration kind} {parent : StoredCapability kind}
    (accepted : AcceptedCellEffect (portal := portal) (authState := authState pre)
      (delegateFamily pre portal context codec parentCodec effectDigest)
      (context.request codec effectDigest pre declaration) pre declaration parent) :
    ∃ stored, readCapability accepted.prepared.post kind declaration.child.id = some stored ∧
      LineageValid (authState pre).parent stored ∧
        LineageAnchored accepted.prepared.post stored := by
  exact ⟨_, delegation_post_capability_exact accepted,
    accepted.modeEvidence.childLineageValid, accepted.postcondition.2⟩

/-! ## Revocation -/

structure RevokeDeclaration where
  key : RevocationKey
  expectedPreRoot : Digest
  operationNullifier : OperationNullifier

def RevokeDeclaration.revokedEntry (declaration : RevokeDeclaration) : Entry layout :=
  ⟨⟨.revoked, declaration.key⟩, ()⟩

def RevokeDeclaration.entries (declaration : RevokeDeclaration) : List (Entry layout) :=
  [declaration.revokedEntry]

def RevokeDeclaration.patch
    (declaration : RevokeDeclaration) (store : Store layout) : Patch layout :=
  assignAll store declaration.entries

@[simp] theorem RevokeDeclaration.patch_writeFootprint (declaration : RevokeDeclaration)
    (store : Store layout) :
    Patch.writeFootprint (declaration.patch store) =
      {⟨.revoked, declaration.key⟩} := by
  simp [RevokeDeclaration.patch, assignAll_writeFootprint, RevokeDeclaration.entries,
    RevokeDeclaration.revokedEntry]

/-- Revocation requires the key to be registered, read from the append-only
`registered` plane: an unregistered key has nothing to revoke.  So every
accepted history keeps "revoked ⇒ registered". -/
structure RevokeEvidence {M : Materializer}
    (pre : Cell M) (declaration : RevokeDeclaration) : Type where
  preRootExact : declaration.expectedPreRoot = pre.root
  registered : isRegistered pre declaration.key = true
  live : isRevoked pre declaration.key = false

def revokeFamily {M : Materializer} (pre : Cell M)
    (codec : LawfulCodec RevokeDeclaration)
    (effectDigest : RevokeDeclaration → Digest) (context : RequestContext) :
    SemanticEffectFamily layout M OperationNullifier where
  Declaration := RevokeDeclaration
  declarationCodec := codec
  pre := pre
  request := fun declaration => context.request codec effectDigest pre.root
    declaration.operationNullifier declaration
  Outcome := fun _ => Unit
  outcomeCodec := fun _ => unitCodec
  ModeEvidence := fun declaration _ => RevokeEvidence pre declaration
  Postcondition := fun declaration _ post =>
    (declaration.patch pre.logical).ResultAt pre.logical post
  effectDigest := effectDigest
  patch := fun declaration _ => declaration.patch pre.logical
  nullifier := fun declaration _ => some declaration.operationNullifier
  Release := fun _ _ => Unit
  DeclassificationAuthority := fun _ _ => Unit
  ReleaseAuthorization := fun _ _ _ => Unit
  DisclosureAllowed := fun _ _ => sealedOnly

def acceptRevocation
    {M : Materializer} (pre : Cell M)
    (context : RequestContext)
    {portal : Portal} {kind : ResourceKind} {request : Request kind}
    (codec : LawfulCodec RevokeDeclaration)
    (effectDigest : RevokeDeclaration → Digest)
    (declaration : RevokeDeclaration)
    (authorization : Authorized portal (authState pre) request)
    (requestBound : (⟨kind, request⟩ : PackedEffectRequest) =
      context.request codec effectDigest pre.root declaration.operationNullifier declaration)
    (requestDigestExact : request.effectsDigest = effectDigest declaration)
    (requestPreExact : request.preStateRoot = pre.root)
    (modeEvidence : RevokeEvidence pre declaration) :
    AcceptedCellEffect (portal := portal) (authState := authState pre)
      (revokeFamily pre codec effectDigest context) request pre declaration () where
  authorization := authorization
  preStateBound := rfl
  requestBound := requestBound
  effectsDigestBound := requestDigestExact
  modeEvidence := modeEvidence
  validated := validated_of_assign declaration.entries requestPreExact
    (assignableAll_single _ _ (assignable_of_absent _ _ modeEvidence.live))
  postcondition := CellState.ValidatedPatch.resultAt _
  disclosure := .sealed
  disclosureAllowed := trivial

/-! ## Epoch rotation -/

inductive EpochTarget where
  | issuer (issuer : IssuerId)
  | policy (policy : PolicyId)
  | subjectKey (subject : SubjectId)
  deriving DecidableEq, Repr

/-- The authority address an epoch target names. -/
def EpochTarget.address : EpochTarget → Address layout
  | EpochTarget.issuer issuerId => ⟨.issuerEpoch, issuerId⟩
  | EpochTarget.policy policyId => ⟨.policyEpoch, policyId⟩
  | EpochTarget.subjectKey subjectId => ⟨.subjectKeyEpoch, subjectId⟩

def EpochTarget.read {M : Materializer} (pre : Cell M) : EpochTarget → Epoch
  | EpochTarget.issuer issuerId => issuerEpochAt pre issuerId
  | EpochTarget.policy policyId => policyEpochAt pre policyId
  | EpochTarget.subjectKey subjectId => subjectKeyEpochAt pre subjectId

def EpochTarget.readAuth (state : AuthState) : EpochTarget → Epoch
  | EpochTarget.issuer issuerId => state.issuerEpoch issuerId
  | EpochTarget.policy policyId => state.policyEpoch policyId
  | EpochTarget.subjectKey subjectId => state.subjectKeyEpoch subjectId

@[simp] theorem EpochTarget.readAuth_authState {M : Materializer}
    (pre : Cell M) (target : EpochTarget) :
    target.readAuth (authState pre) = target.read pre := by
  cases target <;> rfl

/-- The typed entry installing `epoch` at the target's address. -/
def EpochTarget.entry (target : EpochTarget) (epoch : Epoch) : Entry layout :=
  match target with
  | EpochTarget.issuer issuerId => ⟨⟨.issuerEpoch, issuerId⟩, epoch⟩
  | EpochTarget.policy policyId => ⟨⟨.policyEpoch, policyId⟩, epoch⟩
  | EpochTarget.subjectKey subjectId => ⟨⟨.subjectKeyEpoch, subjectId⟩, epoch⟩

@[simp] theorem EpochTarget.entry_address (target : EpochTarget) (epoch : Epoch) :
    (target.entry epoch).1 = target.address := by
  cases target <;> rfl

theorem EpochTarget.entry_ram (target : EpochTarget) (epoch : Epoch) :
    layout.discipline (target.entry epoch).1.1 = .ram := by
  cases target <;> rfl

/-- A cell holding a target's entry reads that epoch back through the target's
own reader. -/
theorem EpochTarget.read_of_entry {M : Materializer} (target : EpochTarget)
    (cell : Cell M) {epoch : Epoch}
    (holds : cell.logical (target.entry epoch).1 = some (target.entry epoch).2) :
    target.read cell = epoch := by
  cases target <;>
    simp only [EpochTarget.entry, EpochTarget.read, issuerEpochAt, policyEpochAt,
      subjectKeyEpochAt] at holds ⊢ <;>
    rw [holds] <;> rfl

structure RotateEpochDeclaration where
  target : EpochTarget
  expectedEpoch : Epoch
  nextEpoch : Epoch
  expectedPreRoot : Digest
  operationNullifier : OperationNullifier

def RotateEpochDeclaration.entries (declaration : RotateEpochDeclaration) : List (Entry layout) :=
  [declaration.target.entry declaration.nextEpoch]

def RotateEpochDeclaration.patch
    (declaration : RotateEpochDeclaration) (store : Store layout) : Patch layout :=
  assignAll store declaration.entries

@[simp] theorem RotateEpochDeclaration.patch_writeFootprint
    (declaration : RotateEpochDeclaration) (store : Store layout) :
    Patch.writeFootprint (declaration.patch store) =
      {declaration.target.address} := by
  simp [RotateEpochDeclaration.patch, assignAll_writeFootprint,
    RotateEpochDeclaration.entries]

/-- Rotating a grant generation leaves that resource's selected policy source
unchanged in the ACTUAL joint post. A deliberate combined source-and-generation
change requires its own ordered batch semantics, not two same-pre writes. -/
def EpochTarget.SourceFramed (target : EpochTarget)
    (pre post : Store layout) : Prop :=
  match target with
  | .policy policyId =>
      post ⟨.policyRevision, policyId⟩ = pre ⟨.policyRevision, policyId⟩ ∧
      ∀ revision, post ⟨.policyAddress, (policyId, revision)⟩ =
        pre ⟨.policyAddress, (policyId, revision)⟩
  | _ => True

theorem RotateEpochDeclaration.source_framed {M : Materializer} {pre : Cell M}
    {expectedPreRoot : Digest} (declaration : RotateEpochDeclaration)
    (validated : CellState.ValidatedPatch M pre expectedPreRoot
      (declaration.patch pre.logical)) :
    declaration.target.SourceFramed pre.logical validated.apply.logical := by
  have footprint := declaration.patch_writeFootprint pre.logical
  cases target : declaration.target with
  | issuer _ => trivial
  | subjectKey _ => trivial
  | policy policy =>
      rw [target] at footprint
      constructor
      · exact Patch.run_frame pre.logical _ ⟨.policyRevision, policy⟩ (by
          rw [footprint]
          simp [EpochTarget.address])
      · intro revision
        exact Patch.run_frame pre.logical _ ⟨.policyAddress, (policy, revision)⟩ (by
          rw [footprint]
          simp [EpochTarget.address])

structure RotateEpochEvidence {M : Materializer} (pre : Cell M)
    (declaration : RotateEpochDeclaration) : Type where
  preRootExact : declaration.expectedPreRoot = pre.root
  currentExact : declaration.target.read pre = declaration.expectedEpoch
  successorExact : declaration.nextEpoch = declaration.expectedEpoch + 1

def rotateEpochFamily {M : Materializer} (pre : Cell M)
    (codec : LawfulCodec RotateEpochDeclaration)
    (effectDigest : RotateEpochDeclaration → Digest) (context : RequestContext) :
    SemanticEffectFamily layout M OperationNullifier where
  Declaration := RotateEpochDeclaration
  declarationCodec := codec
  pre := pre
  request := fun declaration => context.request codec effectDigest pre.root
    declaration.operationNullifier declaration
  Outcome := fun _ => Unit
  outcomeCodec := fun _ => unitCodec
  ModeEvidence := fun declaration _ => RotateEpochEvidence pre declaration
  Postcondition := fun declaration _ post =>
    (declaration.patch pre.logical).ResultAt pre.logical post ∧
    declaration.target.SourceFramed pre.logical post
  effectDigest := effectDigest
  patch := fun declaration _ => declaration.patch pre.logical
  nullifier := fun declaration _ => some declaration.operationNullifier
  Release := fun _ _ => Unit
  DeclassificationAuthority := fun _ _ => Unit
  ReleaseAuthorization := fun _ _ _ => Unit
  DisclosureAllowed := fun _ _ => sealedOnly

def acceptEpochRotation
    {M : Materializer} (pre : Cell M)
    (context : RequestContext)
    {portal : Portal} {kind : ResourceKind} {request : Request kind}
    (codec : LawfulCodec RotateEpochDeclaration)
    (effectDigest : RotateEpochDeclaration → Digest)
    (declaration : RotateEpochDeclaration)
    (authorization : Authorized portal (authState pre) request)
    (requestBound : (⟨kind, request⟩ : PackedEffectRequest) =
      context.request codec effectDigest pre.root declaration.operationNullifier declaration)
    (requestDigestExact : request.effectsDigest = effectDigest declaration)
    (requestPreExact : request.preStateRoot = pre.root)
    (modeEvidence : RotateEpochEvidence pre declaration) :
    AcceptedCellEffect (portal := portal) (authState := authState pre)
      (rotateEpochFamily pre codec effectDigest context) request pre declaration () :=
  have assignable : AssignableAll pre.logical declaration.entries :=
    assignableAll_single _ _
      (assignable_of_ram _ _ (EpochTarget.entry_ram declaration.target declaration.nextEpoch))
  {
  authorization := authorization
  preStateBound := rfl
  requestBound := requestBound
  effectsDigestBound := requestDigestExact
  modeEvidence := modeEvidence
  validated := validated_of_assign declaration.entries requestPreExact
    assignable
  postcondition := ⟨CellState.ValidatedPatch.resultAt _,
    declaration.source_framed (validated_of_assign declaration.entries requestPreExact
      assignable)⟩
  disclosure := .sealed
  disclosureAllowed := trivial }

/-! ## The common canonical-pre theorem and atomic patch teeth -/

/-- A formulation without typeclass magic, suitable for every portal. -/
theorem authorization_consults_same_canonical_pre
    {M : Materializer} {pre : Cell M}
    {portal : Portal} {kind : ResourceKind} {request : Request kind}
    {family : SemanticEffectFamily layout M OperationNullifier}
    {declaration : family.Declaration} {outcome : family.Outcome declaration}
    (accepted : AcceptedCellEffect (portal := portal)
      (authState := authState pre) family request pre declaration outcome) :
    request.preStateRoot = pre.root ∧
      (authState pre).capabilityRoot = pre.root ∧
      (authState pre).revocationRoot = pre.root :=
  ⟨accepted.preRootBound, rfl, rfl⟩

@[simp] theorem issue_post_capability_exact
    {M : Materializer} {pre : Cell M}
    {portal : Portal} {kind : ResourceKind} {request : Request kind}
    {codec : LawfulCodec (IssueDeclaration kind)}
    {effectDigest : IssueDeclaration kind → Digest}
    {declaration : IssueDeclaration kind}
    (accepted : AcceptedCellEffect (portal := portal)
      (authState := authState pre)
      (issueFamily pre codec effectDigest context) request pre declaration ()) :
    accepted.prepared.post.logical ⟨.capability kind, declaration.capability.id⟩ =
      some (⟨declaration.capability, []⟩ : StoredCapability kind) :=
  apply_creation_member accepted.validated rfl declaration.capabilityEntry
    (List.mem_cons_self ..)

/-- **Issuance registers.**  The issued capability's own revocation key is in
the `registered` plane of the post-cell, allocated by the same patch. -/
@[simp] theorem issue_post_registered
    {M : Materializer} {pre : Cell M}
    {portal : Portal} {kind : ResourceKind} {request : Request kind}
    {codec : LawfulCodec (IssueDeclaration kind)}
    {effectDigest : IssueDeclaration kind → Digest}
    {declaration : IssueDeclaration kind}
    (accepted : AcceptedCellEffect (portal := portal)
      (authState := authState pre)
      (issueFamily pre codec effectDigest context) request pre declaration ()) :
    isRegistered accepted.prepared.post (.capability declaration.capability.id) = true := by
  have written : accepted.validated.apply.logical
      ⟨.registered, .capability declaration.capability.id⟩ = some () :=
    apply_creation_member accepted.validated rfl
      (registrationEntry (.capability declaration.capability.id)) (by simp)
  simp only [isRegistered, AcceptedCellEffect.prepared_post, written]
  rfl

theorem issue_post_lineage_valid
    {M : Materializer} {pre : Cell M}
    {portal : Portal} {kind : ResourceKind} {request : Request kind}
    {codec : LawfulCodec (IssueDeclaration kind)}
    {effectDigest : IssueDeclaration kind → Digest}
    {declaration : IssueDeclaration kind}
    (accepted : AcceptedCellEffect (portal := portal)
      (authState := authState pre)
      (issueFamily pre codec effectDigest context) request pre declaration ()) :
    ∃ stored, readCapability accepted.prepared.post kind declaration.capability.id = some stored ∧
      LineageValid (authState pre).parent stored ∧
        LineageAnchored accepted.prepared.post stored := by
  refine ⟨⟨declaration.capability, []⟩, issue_post_capability_exact accepted, ?_, trivial⟩
  exact .root declaration.capability accepted.modeEvidence.rootParent
    accepted.modeEvidence.rootSelf

@[simp] theorem attenuation_post_capability_exact
    {M : Materializer} {pre : Cell M}
    {portal : Portal} {kind : ResourceKind} {request : Request kind}
    {codec : LawfulCodec (AttenuateDeclaration kind)}
    {parentCodec : LawfulCodec (StoredCapability kind)}
    {effectDigest : AttenuateDeclaration kind → Digest}
    {declaration : AttenuateDeclaration kind} {parent : StoredCapability kind}
    (accepted : AcceptedCellEffect (portal := portal)
      (authState := authState pre)
      (attenuateFamily pre codec parentCodec effectDigest context)
      request pre declaration parent) :
    readCapability accepted.prepared.post kind declaration.child.id =
      some (descendedCapability declaration.child parent) :=
  apply_creation_member accepted.validated rfl (declaration.capabilityEntry parent)
    (List.mem_cons_self ..)

/-- **Attenuation registers** the child's own revocation key. -/
@[simp] theorem attenuation_post_registered
    {M : Materializer} {pre : Cell M}
    {portal : Portal} {kind : ResourceKind} {request : Request kind}
    {codec : LawfulCodec (AttenuateDeclaration kind)}
    {parentCodec : LawfulCodec (StoredCapability kind)}
    {effectDigest : AttenuateDeclaration kind → Digest}
    {declaration : AttenuateDeclaration kind} {parent : StoredCapability kind}
    (accepted : AcceptedCellEffect (portal := portal)
      (authState := authState pre)
      (attenuateFamily pre codec parentCodec effectDigest context)
      request pre declaration parent) :
    isRegistered accepted.prepared.post (.capability declaration.child.id) = true := by
  have written : accepted.validated.apply.logical
      ⟨.registered, .capability declaration.child.id⟩ = some () :=
    apply_creation_member accepted.validated rfl
      (registrationEntry (.capability declaration.child.id)) (by simp)
  simp only [isRegistered, AcceptedCellEffect.prepared_post, written]
  rfl

/-- The written child is not just present: its retained first-order ancestry is
validated by the exact strict edge and parent lineage read from canonical pre. -/
theorem attenuation_post_lineage_valid
    {M : Materializer} {pre : Cell M}
    {portal : Portal} {kind : ResourceKind} {request : Request kind}
    {codec : LawfulCodec (AttenuateDeclaration kind)}
    {parentCodec : LawfulCodec (StoredCapability kind)}
    {effectDigest : AttenuateDeclaration kind → Digest}
    {declaration : AttenuateDeclaration kind} {parent : StoredCapability kind}
    (accepted : AcceptedCellEffect (portal := portal)
      (authState := authState pre)
      (attenuateFamily pre codec parentCodec effectDigest context)
      request pre declaration parent) :
    ∃ stored,
      readCapability accepted.prepared.post kind declaration.child.id = some stored ∧
      LineageValid (authState pre).parent stored := by
  exact ⟨descendedCapability declaration.child parent,
    attenuation_post_capability_exact accepted,
    accepted.modeEvidence.childLineageValid⟩

/-- Strict descent also preserves the exact retained canonical parent chain
in the actual post-cell, including when the parent already has mixed lineage. -/
theorem attenuation_post_lineage_anchored
    {M : Materializer} {pre : Cell M}
    {portal : Portal} {kind : ResourceKind} {request : Request kind}
    {codec : LawfulCodec (AttenuateDeclaration kind)}
    {parentCodec : LawfulCodec (StoredCapability kind)}
    {effectDigest : AttenuateDeclaration kind → Digest}
    {declaration : AttenuateDeclaration kind} {parent : StoredCapability kind}
    (accepted : AcceptedCellEffect (portal := portal)
      (authState := authState pre)
      (attenuateFamily pre codec parentCodec effectDigest context)
      request pre declaration parent) :
    LineageAnchored accepted.prepared.post (descendedCapability declaration.child parent) :=
  accepted.postcondition.2

@[simp] theorem revocation_post_exact
    {M : Materializer} {pre : Cell M}
    {portal : Portal} {kind : ResourceKind} {request : Request kind}
    {codec : LawfulCodec RevokeDeclaration}
    {effectDigest : RevokeDeclaration → Digest}
    {declaration : RevokeDeclaration}
    (accepted : AcceptedCellEffect (portal := portal)
      (authState := authState pre)
      (revokeFamily pre codec effectDigest context) request pre declaration ()) :
    isRevoked accepted.prepared.post declaration.key = true := by
  have written : accepted.validated.apply.logical ⟨.revoked, declaration.key⟩ = some () :=
    apply_single (record := declaration.revokedEntry) accepted.validated
  simp only [isRevoked, AcceptedCellEffect.prepared_post, written]
  rfl

/-- A committed revocation is immediately visible to the next canonical
authorization projection; there is no stale host revocation cache. -/
theorem revocation_post_is_authorizer_member
    {M : Materializer} {pre : Cell M}
    {portal : Portal} {kind : ResourceKind} {request : Request kind}
    {codec : LawfulCodec RevokeDeclaration}
    {effectDigest : RevokeDeclaration → Digest}
    {declaration : RevokeDeclaration}
    (accepted : AcceptedCellEffect (portal := portal)
      (authState := authState pre)
      (revokeFamily pre codec effectDigest context) request pre declaration ()) :
    declaration.key ∈ (authState accepted.prepared.post).revoked := by
  exact (mem_authState_revoked_iff accepted.prepared.post declaration.key).2
    (revocation_post_exact accepted)

/-- **Revocation requires registration, refuting pole.**  No revocation of a key
the pre-cell has not registered has mode evidence. -/
theorem RevokeEvidence.reject_unregistered {M : Materializer} {pre : Cell M}
    {declaration : RevokeDeclaration}
    (unregistered : isRegistered pre declaration.key = false) :
    IsEmpty (RevokeEvidence pre declaration) :=
  ⟨fun evidence => by
    have registered := evidence.registered
    rw [unregistered] at registered
    cases registered⟩

/-- **Revoked ⇒ registered, at every accepted revocation.**  The post-cell of an
accepted revocation holds the key in BOTH presence planes: registration was
required at pre and the append-only plane kept it. -/
theorem revocation_post_registered_and_revoked
    {M : Materializer} {pre : Cell M}
    {portal : Portal} {kind : ResourceKind} {request : Request kind}
    {codec : LawfulCodec RevokeDeclaration}
    {effectDigest : RevokeDeclaration → Digest}
    {declaration : RevokeDeclaration}
    (accepted : AcceptedCellEffect (portal := portal)
      (authState := authState pre)
      (revokeFamily pre codec effectDigest context) request pre declaration ()) :
    isRegistered accepted.prepared.post declaration.key = true ∧
      isRevoked accepted.prepared.post declaration.key = true := by
  refine ⟨?_, revocation_post_exact accepted⟩
  have present : pre.logical ⟨.registered, declaration.key⟩ = some () := by
    have registered := accepted.modeEvidence.registered
    simp only [isRegistered, Option.isSome_iff_exists] at registered
    obtain ⟨value, present⟩ := registered
    exact present.trans (congrArg some (Subsingleton.elim (α := Unit) value ()))
  have kept := registration_permanent pre.logical _ declaration.key
    accepted.validated.valid present
  simp only [isRegistered, AcceptedCellEffect.prepared_post,
    CellState.ValidatedPatch.apply_logical, kept]
  rfl

@[simp] theorem rotation_post_exact
    {M : Materializer} {pre : Cell M}
    {portal : Portal} {kind : ResourceKind} {request : Request kind}
    {codec : LawfulCodec RotateEpochDeclaration}
    {effectDigest : RotateEpochDeclaration → Digest}
    {declaration : RotateEpochDeclaration}
    (accepted : AcceptedCellEffect (portal := portal)
      (authState := authState pre)
      (rotateEpochFamily pre codec effectDigest context) request pre declaration ()) :
    declaration.target.read accepted.prepared.post = declaration.nextEpoch :=
  EpochTarget.read_of_entry declaration.target accepted.prepared.post
    (apply_single (record := declaration.target.entry declaration.nextEpoch) accepted.validated)

/-- The family postcondition retains source framing through joint composition,
not merely on the standalone patch that initially produced the token. -/
theorem rotation_joint_post_source_framed
    {M : Materializer} {pre : Cell M}
    {codec : LawfulCodec RotateEpochDeclaration}
    {effectDigest : RotateEpochDeclaration → Digest}
    {declaration : RotateEpochDeclaration} {post : Store layout}
    (postcondition : (rotateEpochFamily pre codec effectDigest context).Postcondition
      declaration () post) :
    declaration.target.SourceFramed pre.logical post := postcondition.2

theorem rotation_post_source_framed
    {M : Materializer} {pre : Cell M}
    {portal : Portal} {kind : ResourceKind} {request : Request kind}
    {codec : LawfulCodec RotateEpochDeclaration}
    {effectDigest : RotateEpochDeclaration → Digest}
    {declaration : RotateEpochDeclaration}
    (accepted : AcceptedCellEffect (portal := portal)
      (authState := authState pre)
      (rotateEpochFamily pre codec effectDigest context) request pre declaration ()) :
    declaration.target.SourceFramed pre.logical accepted.prepared.post.logical :=
  accepted.postcondition.2

/-- Epoch rotation changes the exact epoch read by the next authorization
judgment, not merely an auxiliary receipt field. -/
theorem rotation_post_is_authorizer_epoch
    {M : Materializer} {pre : Cell M}
    {portal : Portal} {kind : ResourceKind} {request : Request kind}
    {codec : LawfulCodec RotateEpochDeclaration}
    {effectDigest : RotateEpochDeclaration → Digest}
    {declaration : RotateEpochDeclaration}
    (accepted : AcceptedCellEffect (portal := portal)
      (authState := authState pre)
      (rotateEpochFamily pre codec effectDigest context) request pre declaration ()) :
    declaration.target.readAuth (authState accepted.prepared.post) =
      declaration.nextEpoch := by
  rw [declaration.target.readAuth_authState]
  exact rotation_post_exact accepted

/-- Revocation acceptance changes only its exact revocation key; every other
typed address is framed by the canonical delta. -/
theorem revoke_frame
    {M : Materializer} {pre : Cell M}
    {portal : Portal} {kind : ResourceKind} {request : Request kind}
    {codec : LawfulCodec RevokeDeclaration}
    {effectDigest : RevokeDeclaration → Digest}
    {declaration : RevokeDeclaration}
    (accepted : AcceptedCellEffect (portal := portal)
      (authState := authState pre)
      (revokeFamily pre codec effectDigest context) request pre declaration ())
    (address : Address layout)
    (outside : address ∉ ({⟨.revoked, declaration.key⟩} : Finset (Address layout))) :
    accepted.prepared.post.logical address = pre.logical address :=
  accepted.frame address (by
    change address ∉ Patch.writeFootprint (declaration.patch pre.logical)
    rw [RevokeDeclaration.patch_writeFootprint]
    exact outside)

/-- Every family exposes the exact eager nullifier the receiver consumes. -/
theorem revoke_nullifier_exact
    {M : Materializer} {pre : Cell M}
    {portal : Portal} {kind : ResourceKind} {request : Request kind}
    {codec : LawfulCodec RevokeDeclaration}
    {effectDigest : RevokeDeclaration → Digest}
    {declaration : RevokeDeclaration}
    (accepted : AcceptedCellEffect (portal := portal)
      (authState := authState pre)
      (revokeFamily pre codec effectDigest context) request pre declaration ()) :
    accepted.prepared.nullifier = some declaration.operationNullifier := rfl

/-- info: 'Minidregg.Theory.CredentialAuthorityEffects.AttenuateEvidence.childLineageValid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms AttenuateEvidence.childLineageValid
/-- info: 'Minidregg.Theory.CredentialAuthorityEffects.authorization_consults_same_canonical_pre' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms authorization_consults_same_canonical_pre
/-- info: 'Minidregg.Theory.CredentialAuthorityEffects.revocation_post_is_authorizer_member' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms revocation_post_is_authorizer_member
/-- info: 'Minidregg.Theory.CredentialAuthorityEffects.rotation_post_is_authorizer_epoch' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms rotation_post_is_authorizer_epoch
/-- info: 'Minidregg.Theory.CredentialAuthorityEffects.revoke_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms revoke_frame
/-- info: 'Minidregg.Theory.CredentialAuthorityEffects.assignAll_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms assignAll_valid
/-- info: 'Minidregg.Theory.CredentialAuthorityEffects.assignAll_refused_of_changed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms assignAll_refused_of_changed
/-- info: 'Minidregg.Theory.CredentialAuthorityEffects.setAll_member' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms setAll_member
/-- info: 'Minidregg.Theory.CredentialAuthorityEffects.rotation_post_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms rotation_post_exact
/-- info: 'Minidregg.Theory.CredentialAuthorityEffects.assignAll_valid_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms assignAll_valid_iff
/-- info: 'Minidregg.Theory.CredentialAuthorityEffects.assignableAll_ram_append_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms assignableAll_ram_append_iff

/-- info: 'Minidregg.Theory.CredentialAuthorityEffects.issue_post_registered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms issue_post_registered
/-- info: 'Minidregg.Theory.CredentialAuthorityEffects.attenuation_post_registered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms attenuation_post_registered
/-- info: 'Minidregg.Theory.CredentialAuthorityEffects.delegation_post_registered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms delegation_post_registered
/-- info: 'Minidregg.Theory.CredentialAuthorityEffects.RevokeEvidence.reject_unregistered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms RevokeEvidence.reject_unregistered
/-- info: 'Minidregg.Theory.CredentialAuthorityEffects.revocation_post_registered_and_revoked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms revocation_post_registered_and_revoked
/-- info: 'Minidregg.Theory.CredentialAuthorityEffects.assignableAll_of_nodup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms assignableAll_of_nodup
end Minidregg.Theory.CredentialAuthorityEffects
