/-
Closed neutral policy-source carry. This is a byte/state transformation, not
permission to cross profiles: CarriedSegmentIO must authenticate the complete
old image with its retained interpreter and pin an unchanged deployment and
schema before calling `derive` or `deriveStoreV2`. It then binds `Plan.changes` in the signed carry
body and validates the complete target through NativeHost.validateLoaded.

No request supplies writes, replacement grants, records, or predecessor maps.
Only the tuple-hashEq legacy v4 source is accepted. Every retained live source
is converted, including historical revisions. A foreign v4 predecessor is
resolved through the checked old chain to its freshly derived v6 counterpart.
-/
import Compiler.PolicyRecordCodec
import Compiler.CredentialAuthorityDomainReceiver
import Compiler.LegacyStoreCarry
import Compiler.LegacyContentCarry

namespace Minidregg.Compiler.NeutralPolicyCarry

open Minidregg.Theory
open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.Store
open Minidregg.Theory.CellState
open Minidregg.Theory.CredentialAuthorityState
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Kernel.DurableDataIntent
open Minidregg.Compiler.CanonicalCellRegistry (registry)
open Minidregg.Compiler.ResourceBirthCodec

set_option autoImplicit false

abbrev LegacyRecord := PolicyRecordCodec.LegacyV4.Record
abbrev CurrentRecord := CanonicalPolicyAdmission.PolicyRecord
abbrev Durable := DurableReceiverIO.Loaded ResourceBirthCodec.rootBytes

private def need {α : Type} (detail : String) : Option α → Except String α
  | none => .error detail
  | some value => .ok value

private def legacyRecordStream : StreamCodec LegacyRecord where
  encode record := bytesStream.encode (PolicyRecordCodec.LegacyV4.encode record)
  decodePrefix bytes := do
    let (source, suffix) ← bytesStream.decodePrefix bytes
    let record ← PolicyRecordCodec.LegacyV4.decode source
    some (record, suffix)
  decodePrefix_encode := by
    intro record suffix
    simp [bytesStream.decodePrefix_encode, PolicyRecordCodec.LegacyV4.decode_encode]

private def legacyPayloadStream :=
  StreamCodec.product StreamCodec.nat (StreamCodec.option legacyRecordStream)

/-- These are the original outer lifecycle and PackedCell envelopes, including
role tag 10. The SOURCE payload retains its original version/option framing. -/
def legacySourceBytes (record : LegacyRecord) : List UInt8 :=
  [68, 82, 2, 1, 68, 82, 1, 10] ++ PolicySourceCell.wireFrame ++
    legacyPayloadStream.encode (PolicySourceCell.wireVersion, some record)

private def sourcePrefix : List UInt8 :=
  [68, 82, 2, 1, 68, 82, 1, 10] ++ PolicySourceCell.wireFrame

/-- Full consumption and exact re-encoding close every wrapper, not only the
inner record. An empty source cell is unsupported and explicitly refused. -/
def decodeLegacySource (bytes : List UInt8) : Option LegacyRecord := do
  if bytes.take sourcePrefix.length != sourcePrefix then none else do
    let (version, record?) ← legacyPayloadStream.toLawful.decode (bytes.drop sourcePrefix.length)
    if version != PolicySourceCell.wireVersion then none else do
      let record ← record?
      if legacySourceBytes record = bytes then some record else none

private def hasSourceRole : List UInt8 → Bool
  | 68 :: 82 :: 2 :: 1 :: 68 :: 82 :: 1 :: 10 :: _ => true
  | _ => false

structure Source where
  cellId : CellId
  record : LegacyRecord

/-- The mapping is reconstructed from exact old sources. It becomes
 authenticated when the parent carry binds the old image and derived writes. -/
structure Binding where
  source : Source
  target : CurrentRecord

private def oldAddress (source : Source) : Digest :=
  PolicyRecordCodec.LegacyV4.digest source.record

def Binding.sourceAddress (binding : Binding) : Digest :=
  oldAddress binding.source

def Binding.targetAddress (binding : Binding) : Digest :=
  PolicyRecordCodec.digest binding.target

def Binding.targetCellId (binding : Binding) : CellId :=
  ⟨PolicySourceCell.physicalId binding.target.domain binding.targetAddress⟩

private def checkUnchangedNonPolicy (deployment : CanonicalCellRegistry.Deployment)
    (identifier : CellId) (bytes : List UInt8) : Except String Unit := do
  -- The audited legacy registry stopped at role 16. A target decoder must
  -- never grant an old image new meanings for introduced roles 17/18 (or
  -- any later role), even if the target bytes happen to decode.
  match bytes with
  | 68 :: 82 :: 2 :: 1 :: 68 :: 82 :: 1 :: role :: _ =>
      if role.toNat > 16 then
        throw "carry refuses a cell role absent from the legacy profile"
  | _ => pure ()
  -- Other roles must already have precisely the unchanged target layout.
  -- They are checked, never re-encoded or rewritten by this transformation.
  let image ← need "carry refuses unsupported lifecycle or changed cell role"
    ((LifecycleImage.codec registry).decode bytes)
  match image with
  | .live cell =>
      if !CanonicalCellRegistry.cellCheck deployment identifier.value cell then
        throw "carry non-policy source violates deployment role/domain"
      if cell.kind == .policySource then
        throw "carry refuses policy source outside the legacy wrapper"
  | _ => pure ()

private def collectSources (deployment : CanonicalCellRegistry.Deployment)
    (sourceSemantics : Digest) (loaded : Durable) : Except String (List Source) := do
  let mut sources := []
  for (identifier, bytes) in loaded.cells do
    if hasSourceRole bytes then
      let record ← need "carry refuses non-v4, empty, or noncanonical policy source"
        (decodeLegacySource bytes)
      if record.domain != deployment.domain || record.semantics != sourceSemantics then
        throw "carry source policy domain/profile differs from audited source"
      if identifier.value != PolicySourceCell.physicalId deployment.domain
          (PolicyRecordCodec.LegacyV4.digest record) then
        throw "carry source physical address differs from exact v4 digest"
      sources := sources ++ [⟨identifier, record⟩]
  if sources.isEmpty then throw "carry has no legacy policy sources"
  if !decide (sources.map fun source =>
      (source.record.policyId, source.record.version)).Nodup then
    throw "carry source has ambiguous policy revisions"
  if !decide (sources.map oldAddress).Nodup then
    throw "carry source policy digest collision"
  pure sources

/-- Ordering is only construction order: predecessor identity, version and
old digest are all checked against actual retained records. Missing historical
sources, cycles, gaps and cross-policy predecessor aliases refuse. -/
private def liftSources (sources : List Source) (targetSemantics : Digest) :
    Except String (List Binding) := do
  let ordered := sources.mergeSort fun left right =>
    decide (left.record.version ≤ right.record.version)
  let mut bindings : List Binding := []
  for source in ordered do
    let previous ← match source.record.previous with
      | none => do
          if source.record.version != 0 then throw "carry policy has nonzero revision without predecessor"
          pure none
      | some old => do
          let predecessor ← need "carry lacks an exact historical predecessor"
            (bindings.find? fun binding =>
              oldAddress binding.source == old &&
              binding.source.record.policyId == source.record.policyId &&
              binding.source.record.version + 1 == source.record.version)
          pure (some predecessor.targetAddress)
    let target := PolicyRecordCodec.LegacyV4.neutralLift source.record targetSemantics previous
    bindings := bindings ++ [⟨source, target⟩]
  pure bindings

abbrev AddressUpdate := (PolicyId × Nat) × Digest

/-- Only this authority plane is rewritten. In particular no grant, key,
revocation, registration, epoch, revision or room parent is regenerated. -/
def updateAddresses (state : Store CredentialAuthorityState.layout) :
    List AddressUpdate → Store CredentialAuthorityState.layout
  | [] => state
  | (key, value) :: rest =>
      updateAddresses (state.set ⟨.policyAddress, key⟩
        ((state ⟨.policyAddress, key⟩).map fun _ => value)) rest

theorem updateAddresses_other (state : Store CredentialAuthorityState.layout)
    (updates : List AddressUpdate) (address : Address CredentialAuthorityState.layout)
    (other : address.1 ≠ .policyAddress) :
    updateAddresses state updates address = state address := by
  induction updates generalizing state with
  | nil => rfl
  | cons first rest ih =>
      rcases first with ⟨key, value⟩
      rw [updateAddresses, ih]
      apply Store.set_ne
      intro same
      exact other (congrArg Sigma.fst same)

/-- Retired address entries stay absent. This holds for the actual updater,
independently of the plan's additional filter to existing address support. -/
theorem updateAddresses_absent (state : Store CredentialAuthorityState.layout)
    (updates : List AddressUpdate) (address : Address CredentialAuthorityState.layout)
    (absent : state address = none) :
    updateAddresses state updates address = none := by
  induction updates generalizing state with
  | nil => exact absent
  | cons first rest ih =>
      rcases first with ⟨key, value⟩
      unfold updateAddresses
      apply ih
      by_cases same : address = ⟨.policyAddress, key⟩
      · subst address
        simp [Store.set_eq, absent]
      · rw [Store.set_ne _ _ _ _ same]
        exact absent

/-- The only constructor is the closed derivation below. The receiver may read
these writes, but cannot obtain a checked plan by handing in arbitrary writes. -/
structure Plan where
  private mk ::
  deployment : CanonicalCellRegistry.Deployment
  bindings : List Binding
  authority : CredentialAuthorityCell.Cell
  otherChanges : List (CellId × List UInt8)
  transformation : Nat

def Plan.addressUpdates (plan : Plan) : List AddressUpdate :=
  plan.bindings.filterMap fun binding =>
    let key := (binding.source.record.policyId, binding.source.record.version)
    if (plan.authority.logical ⟨.policyAddress, key⟩).isSome then
      some (key, binding.targetAddress)
    else none

def Plan.authorityAfter (plan : Plan) : Store CredentialAuthorityState.layout :=
  updateAddresses plan.authority.logical plan.addressUpdates

def Plan.changes (plan : Plan) : List (CellId × List UInt8) :=
  (⟨plan.deployment.authorityCellId⟩,
    CredentialAuthorityDomainReceiver.cellBytes
      (materialize CredentialAuthorityCell.materializer plan.authorityAfter)) ::
  (plan.bindings.flatMap fun binding =>
    [(binding.source.cellId, LifecycleImage.bytes registry .retired),
     (binding.targetCellId, LifecycleImage.bytes registry
       (.live (CanonicalCellRegistry.policySourceCell binding.target)))]) ++ plan.otherChanges

theorem Plan.authority_other (plan : Plan)
    (address : Address CredentialAuthorityState.layout)
    (other : address.1 ≠ .policyAddress) :
    plan.authorityAfter address = plan.authority.logical address :=
  updateAddresses_other plan.authority.logical plan.addressUpdates address other

theorem Plan.authority_absent (plan : Plan)
    (address : Address CredentialAuthorityState.layout)
    (absent : plan.authority.logical address = none) :
    plan.authorityAfter address = none :=
  updateAddresses_absent plan.authority.logical plan.addressUpdates address absent

/-- Explicit shared-evaluator fact: neutral composition retains the legacy
predicate, without a second evaluator or an assumption about hash equality. -/
theorem neutral_predicate (record : LegacyRecord) (semantics : Digest)
    (previous : Option Digest) (old new : Minidregg.Pred.State) :
    Minidregg.Pred.eval
      (PolicyRecordCodec.LegacyV4.neutralLift record semantics previous).localComponent.guarded old new =
      Minidregg.Pred.eval record.predicate old new :=
  PolicyRecordCodec.LegacyV4.neutralLift_local_eval record semantics previous old new

private def finishPlan (deployment : CanonicalCellRegistry.Deployment)
    (bindings : List Binding) (authority : CredentialAuthorityCell.Cell)
    (loaded : Durable) (otherChanges : List (CellId × List UInt8))
    (transformation : Nat) : Except String Plan := do
  -- A normal policy update frees the superseded authority address while its
  -- immutable source remains live. Historical sources authenticate through
  -- the unique contiguous predecessor chain of the currently indexed head;
  -- they do not gain a resurrected authority address.
  for binding in bindings do
    let head ← need "carry source policy has no current authority head"
      (CredentialAuthorityDomain.headAt authority.logical binding.source.record.policyId)
    if binding.source.record.version > head.version then
      throw "carry source contains a future or orphan policy revision"
    if !(bindings.any fun current =>
        current.source.record.policyId == binding.source.record.policyId &&
        current.source.record.version == head.version &&
        current.sourceAddress == head.address) then
      throw "carry current authority head lacks its exact source"
    -- [] is the unique fresh lifecycle spelling; a tombstone is not fresh.
    if loaded.snapshot.canonicalBytes binding.targetCellId != [] then
      throw "carry target policy source identifier is occupied or retired"
  -- Every actually present authority address must map to its exact source.
  -- Absent historical addresses remain absent; only this existing support
  -- contributes to Plan.addressUpdates.
  for address in StoreCodec.sortedSupport CredentialAuthorityCell.wire authority.logical do
    match address with
    | ⟨.policyRevision, policy⟩ =>
        let head ← need "carry authority revision has no current head"
          (CredentialAuthorityDomain.headAt authority.logical policy)
        if !(bindings.any fun binding =>
            binding.source.record.policyId == policy &&
            binding.source.record.version == head.version &&
            binding.sourceAddress == head.address) then
          throw "carry authority revision has no exact current source"
    | ⟨.policyAddress, key⟩ =>
        let current : Option Digest := authority.logical ⟨AuthorityPlane.policyAddress, key⟩
        if !(bindings.any fun binding =>
            (binding.source.record.policyId, binding.source.record.version) == key &&
            current == some (oldAddress binding.source)) then
          throw "carry authority names unsupported or missing historical source"
    | _ => pure ()
  let plan : Plan := ⟨deployment, bindings, authority, otherChanges, transformation⟩
  -- Covers target/target hash collisions and target/source/authority aliases.
  if !decide (plan.changes.map Prod.fst).Nodup then
    throw "carry derived physical identifier collision"
  pure plan

/-- Closed neutral derivation from the complete resumed snapshot. Deployment
and profile identities must come from the parent's independently pinned source
and target configurations; this function does not grant profile-selection
 authority. Schema/field-role changes (including title→membership) are outside
this transformation and must be refused by that receiving boundary. -/
def derive (deployment : CanonicalCellRegistry.Deployment)
    (sourceSemantics targetSemantics : Digest) (loaded : Durable) : Except String Plan := do
  if !decide deployment.Valid then throw "carry deployment role collision"
  if sourceSemantics == targetSemantics then throw "carry requires a distinct target profile"
  let sources ← collectSources deployment sourceSemantics loaded
  for (identifier, bytes) in loaded.cells do
    if !hasSourceRole bytes then checkUnchangedNonPolicy deployment identifier bytes
  let bindings ← liftSources sources targetSemantics
  let authority ← need "carry needs the exact canonical authority cell"
    (CredentialAuthorityDomainReceiver.decodeCell
      (loaded.snapshot.canonicalBytes ⟨deployment.authorityCellId⟩))
  finishPlan deployment bindings authority loaded [] 1


/-- Decode the original lifecycle and role envelope, select a fixed source
codec, then construct a target cell at the same role and physical identifier.
No caller supplies a codec, a replacement grant, or a proposed post-state. -/
private def convertLiveStoreV2 (deployment : CanonicalCellRegistry.Deployment)
    (identifier : CellId) (height : Nat) (bytes : List UInt8) :
    Except String (CellRegistry.PackedCell registry) := do
  let (tag, payload) ← match bytes with
    | 68 :: 82 :: 2 :: 1 :: 68 :: 82 :: 1 :: tag :: payload => pure (tag, payload)
    | _ => throw "carry refuses noncanonical source lifecycle/role envelope"
  let kind ← need "carry source has an unknown role" (CanonicalCellRegistry.kindAtTag tag)
  let cell : CellRegistry.PackedCell registry ← match kind with
    | .content => do
        let store ← LegacyContentCarry.convertPayload height payload
        pure ⟨.content, materialize HyperdocumentCell.contentMaterializer store⟩
    | other => do
        let store ← LegacyStoreCarry.convertPayload other height payload
        pure ⟨other, materialize (CanonicalCellRegistry.materializer other) store⟩
  if !CanonicalCellRegistry.cellCheck deployment identifier.value cell then
    throw "carry converted cell violates target role/domain invariants"
  pure cell

/-- Transformation 2 is the closed Store2 boundary: policy sources are lifted
with authenticated predecessor mapping; other physical ids retain their roles.
Unchanged-layout stores retain every logical entry except the declared blinding
ratchet, authority keys gain only an absent future commitment, and content uses
its separate lossless legacy projection. Original source bytes and receipts
remain in the audited prefix; these writes do not reinterpret that history.
The receiver must authenticate the old capsule and validate the full target. -/
def deriveStoreV2 (deployment : CanonicalCellRegistry.Deployment)
    (sourceSemantics targetSemantics : Digest) (loaded : Durable) : Except String Plan := do
  if !decide deployment.Valid then throw "carry deployment role collision"
  if sourceSemantics == targetSemantics then throw "carry requires a distinct target profile"
  let sources ← collectSources deployment sourceSemantics loaded
  let bindings ← liftSources sources targetSemantics
  let mut authority : Option CredentialAuthorityCell.Cell := none
  let mut changes : List (CellId × List UInt8) := []
  for (identifier, bytes) in loaded.cells do
    if hasSourceRole bytes then
      pure ()
    else if bytes == [] || bytes == [68, 82, 2, 0] then
      pure ()
    else
      let cell ← convertLiveStoreV2 deployment identifier loaded.height bytes
      match cell with
      | ⟨.authority, payload⟩ =>
          if authority.isSome then throw "carry source has multiple authority cells"
          authority := some payload
      | cell =>
          let after := LifecycleImage.bytes registry (.live cell)
          if after != bytes then changes := changes ++ [(identifier, after)]
  let sourceAuthority ← need "carry needs the exact source authority cell" authority
  finishPlan deployment bindings sourceAuthority loaded changes 2

end Minidregg.Compiler.NeutralPolicyCarry
