/-
# Compiler.CanonicalCellRegistry — one executable receiving registry

The production registry of deployed cell roles.  Every role's materializer is
a `StoreCodec` cell at its layout (docs/DATAMODEL.md §5 B1): the hyperdocument content and
event-log cells (`HyperdocumentCell`), the one credential-authority cell
(`CredentialAuthorityCell`), the declared-effect cells (`DeclaredEffectCell`),
the canonical resource Book, and immutable policy source cells.  There are no
pages, shards or catalogue: the authority domain is one cell at the
deployment's pinned `authorityCellId`.

Kinds are semantic roles, even when their layout is shared.  Object/program/
account-metadata roles have source-owned field laws and typed dispatch.  No
such role may carry an `accountBalance` field: only the domain's configured
resource Book owns money.

`CellLaw` is an invariant for loaded and FINAL post cells, not only a birth
check.  `UserInitial` further refuses internal authority, Book and
event-history payloads.  Those cells are produced by their source-owned
semantic lowerings.  The registry supplies no public raw-state installation
endpoint.

**Domain.**  A store cell carries no in-cell domain tag: the cell's deployment
is the directory that holds it.  The one place a domain is semantic data is
the hyperdocument event record (`VersionEventRecord.historyDomain`, hashed into
the event id and supplied by the authoring request), so the event-history law
requires every recorded event to name this deployment's domain
(`foreign_domain_event_refused`).

**Laws on write (`Kind.lawClass`).**  Every kind is classified, with no default
arm: a `lawBearing` cell carries a committed law (`PhysicalLawResolution`, keyed
by the cell's id) and the Receiver (`Kernel.ReceivingLaw`) judges that law on
every write, whoever proposes it; a `kernelOnly` cell carries no user law and
only the families its row names may write it (`Kernel.ReceivingLaw.kernelOnly_writers`).  The
table was measured at main 3b709c87 (lane LAWS-RECEIVER census).  Three kinds
have writers today that do not judge the cell's own law: `pay` (PayBook,
PayClaim, PayEnrol, PayAssignment judge the factory or account law; DRC compute
judges none), `clock` (PayObservation and PayEnrol advance it under the pay or
factory law) and `stream` (FleetTurn checks only `CellLaw` on a topic head).
They are `lawBearing` here, and each of those families meets the cell's own law
when it moves onto `Kernel.Receiving.Family`.

**Births.**  A newborn has no committed law at its fresh pre-image; it is
judged by its EXPORT law: the descendants law of its birth parent, the room it is
born in (its `parent` entry in the authority cell the same patch writes,
`Kernel.ReceivingLaw.birthRoom`), and the structural restrictions its kind
carries (a world instance's world kind, `WorldKindLawDependencies.loadNewborn`).
`Kernel.ReceivingLaw` judges every law-bearing birth by them, on the family's
view of the birth, with no second judge in the family.  A newborn's law source
(`policySource`) is born the same way (`kernelOnlyOrBorn`).  A birth with no export
root is NEUTRAL: admitted only when a judged authorizer of the same patch names it.
-/
module

public import Compiler.PersistedCodecTags.Core
public import Compiler.WorldKindCell
public import Compiler.DeclaredEffectCell
public import Compiler.CredentialAuthorityCell
public import Compiler.HyperdocumentCell
public import Compiler.CanonicalResourcePageMaterializer
public import Compiler.ResourceBirthCodec
public import Compiler.PolicySourceCell
public import Kernel.PayCell
public import Compiler.StreamCell
public import Kernel.DomainEpochLaw
public import Compiler.NockProgramCodec
public import Compiler.Evaluator
public import Kernel.ClockCell
public import Kernel.FieldClosure
public import Kernel.SystemCell
public import Theory.CanonicalResourceBookInvariant
public import Kernel.ObjectiveActivityCell
public import Kernel.SeatCell
public import Kernel.PlatformCellLayout

-- Bodies this file reduces or derives through, not exposed by their modules (module system).
import all Init.Data.Repr
import all Init.Data.ToString.Basic
import all Init.Data.ToString.Extra
import all Init.Data.Array.Basic
import all Init.Data.ByteArray.Basic
import all Init.Data.String.Decode
import all Init.Data.String.Defs
import all Init.Control.Except
import all Init.Data.List.Basic
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.String.Bootstrap
import all Init.Data.Format.Basic
import all Init.Data.List.Scan.Basic

@[expose] public section

namespace Minidregg.Compiler.CanonicalCellRegistry

open Minidregg.Theory
open Minidregg.Theory.CellRegistry
open Minidregg.Theory.CellState
open Minidregg.Theory.CausalVersionDag
open Minidregg.Theory.IndexedProgram
open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.DeclaredActionLowering
open Minidregg.Theory.EffectDeclaration
open Minidregg.Theory.Hyperdocument
open Minidregg.Theory.Store (Store)

set_option autoImplicit false

inductive Kind where
  | content
  | eventHistory
  | authority
  | declaredObject
  | resourceBook
  | accountMetadata
  | declaredProgram
  | policySource
  /-- The deployment's pay cell (`Kernel.PayCell`): tariff, deposit address
  book and assignment. Time is the clock cell's. -/
  | pay
  /-- A stream's head (`StreamCell.Head`): its binding, entry count and last
  entry key. A room stream or a fleet topic. -/
  | stream
  /-- One stream entry (`StreamCell.Entry`), at the cell its head and position
  derive. Born by an append, never written again. -/
  | streamEntry
  /-- A Nock program cell (`NockProgramCodec`): jam + ABI, keyed by programId. -/
  | nockProgram
  /-- The deployment's one clock (`Kernel.ClockCell`): unix seconds and the
  last observed chain slot.  `lawBearing`: its own committed law
  (`Kernel.ClockLaw.clockPredicate`) judges EVERY write, whoever proposes it:
  the ticker's `ClockTickReceiver`, and the three pay families that advance it
  to their verified chain tip (`PayObservationReceiver`, `PayEnrolReceiver`,
  `PayEnrolV2Receiver`), each a `Kernel.Receiving.Family` whose `lawStepOf`
  projects the clock write's step (`ClockLaw.step`, their `lawStepOf_clock`),
  so `Receiving.Family.receive_committed_lawful` covers it: their
  `committed_lawful` theorems carry the clock clause.  Until 5d0b452d
  (2026-10-04) the three advanced it unjudged (cv task 01a1087d-8a58, measured
  at 3b709c87); dropping a family's clock arm of `lawStepOf` would reopen that,
  and `receive_committed_lawful` refuses the shape. -/
  | clock
  /-- The deployment's system cell (`Kernel.SystemCell`): the certified head
  and the tail bound `L`, written only by a certify record. -/
  | system
  | worldKind
  | worldInstance
  /-- A kernel activity cell (`Kernel.ObjectiveActivityCell`): an activity
  record, an answer slot, an object's declared state or an activity package,
  each at its coordinate; written only by `ObjectiveActivityReceiver`. -/
  | objectiveActivity
  /-- A seat-kernel cell (`Kernel.SeatCell`): a contract instance, an invitation,
  a seat, an activity's seat holdings or a contract package, each at its
  coordinate; written only by `SeatReceiver` (and an ending activity's turn). -/
  | seat
  /-- The deployment's platform cell (`Kernel.PlatformCellLayout`): the current platform
  record (creation and grain-birth tariffs, completion custodian key, owner budget,
  lifetime) under its version; written only by the platform-install family. -/
  | platform
  deriving DecidableEq, Repr

def Kind.all : List Kind :=
  [.content, .eventHistory, .authority, .declaredObject,
    .resourceBook, .accountMetadata, .declaredProgram, .policySource, .pay, .stream, .nockProgram, .clock, .streamEntry, .system, .worldKind, .worldInstance, .objectiveActivity, .seat, .platform]

/-! ## Who may write which kind -/

/-- The receiving families, one constructor each: the writers a `kernelOnly` row
names.  A family on `Kernel.Receiving.Family` carries its own constructor. -/
inductive FamilyId where
  | declaredResourceController
  | subjectKeyRotation
  | subjectKeyCommitmentAdoption
  | participantKeyEnrollment
  | participantFactoryProvisioning
  | capabilityDelegation
  | capabilityRevocation
  | capabilityRenounce
  | policyInstall
  | resourceBirth
  | grainResourceBirth
  | applicationShareIssue
  | applicationShareIssueGrain
  | applicationAgentLifetimeGrant
  | clockTick
  | certify
  | payBook
  | payAssignment
  | payObservation
  | payClaim
  | payEnrol
  | payEnrolV2
  | realmWell
  | purseRefill
  | jobMoney
  | fleetTurn
  | objectiveActivity
  | seat
  | platformInstall
  deriving DecidableEq, Repr

/-- How a cell kind is judged on write. -/
inductive LawClass where
  /-- Its committed law (`PhysicalLawResolution`, at the cell's id) judges every write. -/
  | lawBearing
  /-- No user law; only the named kernel families may write it. -/
  | kernelOnly (writers : List FamilyId)
  /-- Written in place only by the named kernel families, with no step; BORN by any
  family, judged like a law-bearing birth: by a non-empty export law, or, when the
  newborn has no export root, named (id and post root) by the step of a judged,
  law-bearing, non-birth write of the same patch (`Kernel.ReceivingLaw.Named`).
  A newborn's initial law source is born with the resource it governs. -/
  | kernelOnlyOrBorn (writers : List FamilyId)
  deriving DecidableEq, Repr

/-- The writers of the authority cell, each with what it changes there.  A
writer here is permitted to skip a user law, never to write arbitrary authority:
bounding each family's authority fields by a shape lemma is cv task 01a10887-e79f. -/
def authorityWriters : List FamilyId :=
  [ .subjectKeyRotation               -- the subject's key rows (KeyPreRotation.patch)
  , .subjectKeyCommitmentAdoption     -- the subject's next-key commitment
  , .participantKeyEnrollment         -- a new participant's key record
  , .participantFactoryProvisioning   -- a participant's factory grant
  , .capabilityDelegation             -- a delegated capability grant
  , .capabilityRevocation             -- a revocation entry
  , .capabilityRenounce               -- the holder's own grant, removed
  , .policyInstall                    -- policy head/revision/address rows
  , .resourceBirth                    -- the newborns' control grants, the spent marker
  , .grainResourceBirth               -- the same, for grain-backed births
  , .applicationShareIssue            -- the issued share's grants
  , .applicationShareIssueGrain       -- the same, grain-backed
  , .applicationAgentLifetimeGrant    -- the agent's lifetime grant
  , .payClaim                         -- the claim's spent marker
  , .payEnrol                         -- the enrolled account's grants and marker
  , .payEnrolV2 ]                     -- the same, v2

/-- The writers of the resource Book: every family that moves money or meters it.
The Book carries no user law (`LogicalLaw` pins only its id); conservation is
the Book's own kernel invariant, which every writer's plan proves. -/
def bookWriters : List FamilyId :=
  [.declaredResourceController, .resourceBirth, .grainResourceBirth, .applicationShareIssue,
    .applicationShareIssueGrain, .applicationAgentLifetimeGrant, .payObservation, .payClaim,
    .payEnrol, .payEnrolV2, .realmWell, .purseRefill, .jobMoney, .fleetTurn, .objectiveActivity, .seat]

/-- **The law class of every kind**: reviewed data, one row per kind, no default arm. -/
def Kind.lawClass : Kind → LawClass
  | .content => .lawBearing
  | .declaredObject => .lawBearing
  | .accountMetadata => .lawBearing
  | .declaredProgram => .lawBearing
  | .worldKind => .lawBearing
  | .worldInstance => .lawBearing
  | .stream => .lawBearing
  | .pay => .lawBearing
  | .clock => .lawBearing
  | .authority => .kernelOnly authorityWriters
  | .resourceBook => .kernelOnly bookWriters
  -- Installed by `PolicyInstall` under the OLD law's judgement of the candidate; the new
  -- source is never judged against its own install (`LawComposition`).
  | .policySource => .kernelOnlyOrBorn [.policyInstall]
  -- The certified head and tail bound, written only by a certify record.
  | .system => .kernelOnly [.certify]
  -- Born by an append (DRC stream append, FleetTurn topic append), never written again;
  -- judged at its birth by the head's law once `birthParent` exists (cv task 01a1087d-8a12).
  | .streamEntry => .kernelOnly [.declaredResourceController, .fleetTurn]
  -- Activity records, answer slots, declared state and packages at ids >= 2^256, written
  -- only by the activity kernel turns (their object law is ObjectRecord's).
  | .objectiveActivity => .kernelOnly [.objectiveActivity]
  -- Seat instances, invitations, seats, holdings and contract packages at ids >= 2^256,
  -- written by the seat kernel turns and by an activity's end (which closes the seats
  -- the activity holds, `ActivitySeatEnd`).
  | .seat => .kernelOnly [.seat, .objectiveActivity]
  -- The controller's signed install of a valid record above the current version
  -- (`Kernel.PlatformCell.Admits`); no user law sits at its id.
  | .platform => .kernelOnly [.platformInstall]
  -- A Nock program is not an external resource (`ResourceTargetAdmission.externalKind`):
  -- no law sits at its id; it is born by a birth plan and immutable after.
  | .nockProgram => .kernelOnly [.resourceBirth, .grainResourceBirth, .applicationShareIssue,
      .applicationShareIssueGrain, .applicationAgentLifetimeGrant]
  -- Written by no receiving family: produced at genesis only (`UserShape` refuses its birth;
  -- no event-log writer is in the Host closure, measured at d27d1cad).
  | .eventHistory => .kernelOnly []

/-- A law source is written in place only by `PolicyInstall`, and otherwise only
born, under its birth parent's export law. -/
theorem policySource_policyInstall_or_born :
    Kind.policySource.lawClass = .kernelOnlyOrBorn [.policyInstall] := rfl

theorem system_only_certify : Kind.system.lawClass = .kernelOnly [.certify] := rfl

theorem activity_kernelOnly :
    Kind.objectiveActivity.lawClass = .kernelOnly [.objectiveActivity] := rfl

theorem seat_kernelOnly : Kind.seat.lawClass = .kernelOnly [.seat, .objectiveActivity] := rfl

theorem platform_only_install : Kind.platform.lawClass = .kernelOnly [.platformInstall] := rfl

/-- The pinned exemption list: exactly these kinds carry no user law. -/
theorem kernelOnly_kinds :
    Kind.all.filter (fun kind => kind.lawClass != .lawBearing) =
      [.eventHistory, .authority, .resourceBook, .policySource, .nockProgram, .streamEntry,
        .system, .objectiveActivity, .seat, .platform] := by decide

/-- Tags 1/2/3/5/6/8/9/10/11/12/13/14/15/16 are deployment pins. The final table across
lanes: 11 pay, 12 stream (head), 13 nockProgram, 14 clock, 15 streamEntry, 16 system.  Tag 3 is the one authority
cell (it was the authority page shard).  Tag 7 (the authority catalogue) is
retired and decodes to nothing; tag 4 was never assigned. -/
def Kind.tag : Kind → UInt8
  | .content => 1
  | .eventHistory => 2
  | .authority => 3
  | .declaredObject => 5
  | .resourceBook => 6
  | .accountMetadata => 8
  | .declaredProgram => 9
  | .policySource => PolicySourceCell.registryTag
  | .pay => 11
  | .stream => 12
  | .nockProgram => NockProgramCodec.registryTag
  | .clock => 14
  | .streamEntry => 15
  | .system => 16
  | .worldKind => 17
  | .worldInstance => 18
  | .objectiveActivity => Kernel.ObjectiveActivityCell.registryTag
  | .seat => Kernel.SeatCell.registryTag
  | .platform => Kernel.PlatformCellLayout.registryTag

def kindAtTag : UInt8 → Option Kind
  | 1 => some .content
  | 2 => some .eventHistory
  | 3 => some .authority
  | 5 => some .declaredObject
  | 6 => some .resourceBook
  | 8 => some .accountMetadata
  | 9 => some .declaredProgram
  | 10 => some .policySource
  | 11 => some .pay
  | 12 => some .stream
  | 13 => some .nockProgram
  | 14 => some .clock
  | 15 => some .streamEntry
  | 16 => some .system
  | 17 => some .worldKind
  | 18 => some .worldInstance
  | 19 => some .objectiveActivity
  | 20 => some .seat
  | 21 => some .platform
  | _ => none

@[simp] theorem kindAtTag_tag (kind : Kind) : kindAtTag kind.tag = some kind := by
  cases kind <;> rfl

/-- The tag table has no aliases: a tag that names a kind is that kind's tag. -/
theorem tag_of_kindAtTag (t : UInt8) (kind : Kind) (found : kindAtTag t = some kind) :
    kind.tag = t := by
  unfold kindAtTag at found
  split at found <;> first | (cases found; rfl) | cases found

/-- The retired catalogue tag selects no role: a packed catalogue cell refuses
to decode. -/
theorem retired_catalogue_tag : kindAtTag 7 = none := rfl

/-- Store-cell wire versions.  Content, event and authority moved from page
frames to `StoreCodec` frames; authority v6 tags every capability scope's
target set (explicit or `under` a room); the Book's balance codec became the zigzag
integer codec; the declared roles moved in S2c, and to v4 when the declared-effect key codec
`state-key/tagged-v3` carried both the blinding (tag 3, K-NARROW-HIDE) and a cell's declaration
(tags 4/5, K-FIELD-CLOSURE); the compute braid's v3 had the declaration alone at tags 3/4.
The declared roles are v5 since `state-key/tagged-v4` added the declaration tail `fieldsFrom`
(tag 6, ROOM-SCHEMA v2); a v4 declared cell refuses to decode. -/
def schemaRef : Kind → SchemaRef
  | .content => ⟨⟨91001⟩, 3⟩
  | .eventHistory => ⟨⟨91002⟩, 2⟩
  | .authority => ⟨⟨91003⟩, 8⟩
  | .declaredObject => ⟨⟨91004⟩, 5⟩
  | .resourceBook => ⟨⟨91005⟩, 3⟩
  | .accountMetadata => ⟨⟨91007⟩, 5⟩
  | .declaredProgram => ⟨⟨91008⟩, 5⟩
  | .policySource => ⟨⟨PolicySourceCell.schemaId⟩, PolicySourceCell.wireVersion⟩
  | .pay => ⟨⟨91010⟩, 4⟩
  | .stream => ⟨⟨91012⟩, 3⟩
  | .nockProgram => ⟨⟨NockProgramCodec.schemaId⟩, NockProgramCodec.wireVersion⟩
  | .clock => ⟨⟨91013⟩, Minidregg.Compiler.PersistedCodecTags.clockWireVersion⟩
  | .streamEntry => ⟨⟨91014⟩, 1⟩
  | .system => ⟨⟨91015⟩, 1⟩
  | .worldKind => ⟨⟨91016⟩, 1⟩
  | .worldInstance => ⟨⟨91017⟩, 1⟩
  | .objectiveActivity => ⟨⟨Kernel.ObjectiveActivityCell.schemaId⟩, Kernel.ObjectiveActivityCell.wireVersion⟩
  | .seat => ⟨⟨Kernel.SeatCell.schemaId⟩, Kernel.SeatCell.wireVersion⟩
  | .platform => ⟨⟨Kernel.PlatformCellLayout.schemaId⟩, Kernel.PlatformCellLayout.wireVersion⟩

theorem schemaRef_injective : Function.Injective schemaRef := by
  intro left right same
  cases left <;> cases right <;>
    simp [schemaRef, PolicySourceCell.schemaId, PolicySourceCell.wireVersion,
      NockProgramCodec.schemaId, NockProgramCodec.wireVersion,
      Kernel.ObjectiveActivityCell.schemaId, Kernel.ObjectiveActivityCell.wireVersion,
      Kernel.SeatCell.schemaId, Kernel.SeatCell.wireVersion,
      Kernel.PlatformCellLayout.schemaId, Kernel.PlatformCellLayout.wireVersion] at same ⊢

abbrev layout : Kind → Store.Layout.{0, 0, 0}
  | .content => Hyperdocument.layout
  | .eventHistory => Kernel.HyperdocumentEventLog.Sparse.layout
  | .authority => CredentialAuthorityState.layout
  | .declaredObject => EffectDeclaration.effectLayout
  | .resourceBook => CanonicalResourceKernel.layout
  | .accountMetadata => EffectDeclaration.effectLayout
  | .declaredProgram => EffectDeclaration.effectLayout
  | .policySource => PolicySourceCell.layout
  | .pay => Kernel.PayCell.layout
  | .stream => StreamCell.headLayout
  | .nockProgram => NockProgramCodec.layout
  | .clock => Kernel.ClockCell.layout
  | .streamEntry => StreamCell.entryLayout
  | .system => Kernel.SystemCell.layout
  | .worldKind => WorldKindCell.definitionLayout
  | .worldInstance => WorldKindCell.instanceLayout
  | .objectiveActivity => Kernel.ObjectiveActivityCell.layout
  | .seat => Kernel.SeatCell.layout
  | .platform => Kernel.PlatformCellLayout.layout

def materializer : (kind : Kind) → Materializer (layout kind) Digest
  | .content => HyperdocumentCell.contentMaterializer
  | .eventHistory => HyperdocumentCell.eventMaterializer
  | .authority => CredentialAuthorityCell.materializer
  | .declaredObject => DeclaredEffectCell.materializer
  | .resourceBook => CanonicalResourcePageMaterializer.materializer
  | .accountMetadata => DeclaredEffectCell.materializer
  | .declaredProgram => DeclaredEffectCell.materializer
  | .policySource => PolicySourceCell.materializer
  | .pay => Kernel.PayCell.materializer
  | .stream => StreamCell.headMaterializer
  | .nockProgram => NockProgramCodec.materializer
  | .clock => Kernel.ClockCell.materializer
  | .streamEntry => StreamCell.entryMaterializer
  | .system => Kernel.SystemCell.materializer
  | .worldKind => WorldKindCell.definitionMaterializer
  | .worldInstance => WorldKindCell.instanceMaterializer
  | .objectiveActivity => Kernel.ObjectiveActivityCell.materializer
  | .seat => Kernel.SeatCell.materializer
  | .platform => Kernel.PlatformCellLayout.materializer

/-- Every materializer codec accepts only encodings: the `StoreCodec` frames by
`StoreCodec.decode_reencodes`, the resource book by its framed stream
(`framedCodec_canonical`), and the
policy-source, Nock-program and protected cells by their own `decode_canonical`. -/
theorem materializer_canonical (kind : Kind) (bytes : List UInt8)
    (logical : Store (layout kind))
    (accepted : (materializer kind).codec.decode bytes = some logical) :
    (materializer kind).codec.encode logical = bytes := by
  cases kind
  all_goals first
    | exact StoreCodec.decode_reencodes _ accepted
    | exact CanonicalResourcePageMaterializer.framedCodec_canonical 0
        CanonicalResourcePageMaterializer.stateStream accepted
    | exact PolicySourceCell.decode_canonical accepted
    | exact NockProgramCodec.decode_canonical accepted
    | exact Kernel.ProtectedCell.decode_canonical _ accepted

/-- The store wire of every kind whose materializer is the generic
`StoreCodec.materializer` (K-NARROW-HIDE): its salted root opens per entry. -/
def wire? : (kind : Kind) → Option (StoreCodec.Wire (layout kind))
  | .content => some HyperdocumentCell.contentWire
  | .eventHistory => some HyperdocumentCell.eventWire
  | .authority => some CredentialAuthorityCell.wire
  | .declaredObject => some DeclaredEffectCell.wire
  | .accountMetadata => some DeclaredEffectCell.wire
  | .declaredProgram => some DeclaredEffectCell.wire
  | .pay => some Kernel.PayCell.wire
  | .stream => some StreamCell.headWire
  | .streamEntry => some StreamCell.entryWire
  | .clock => some Kernel.ClockCell.wire
  | .system => some Kernel.SystemCell.wire
  | .worldKind => some WorldKindCell.definitionWire
  | .worldInstance => some WorldKindCell.instanceWire
  | .platform => some Kernel.PlatformCellLayout.wire
  | .resourceBook | .policySource | .nockProgram | .objectiveActivity | .seat => none

/-- A kind with a store wire is materialized by it, so its cell root is that
wire's salted root. -/
theorem materializer_of_wire {kind : Kind} {wire : StoreCodec.Wire (layout kind)}
    (selected : wire? kind = some wire) : materializer kind = StoreCodec.materializer wire := by
  cases kind <;> simp [wire?] at selected <;> subst selected <;> rfl

/-- Whether a cell holds its hiding key. -/
def blinded : (kind : Kind) → Store (layout kind) → Bool
  | kind, store =>
      match wire? kind with
      | some wire => (StoreCodec.blindingKey wire store).isSome
      | none => false

/-- Whether an address is a kind's blinding address. -/
def isBlinding (kind : Kind) (address : Store.Address (layout kind)) : Bool :=
  match wire? kind with
  | some wire => decide (wire.blinding = some address)
  | none => false

def registry : TypeRegistry Digest where
  Kind := Kind
  tag := Kind.tag
  kindAtTag := kindAtTag
  kindAtTag_tag := kindAtTag_tag
  tag_of_kindAtTag := tag_of_kindAtTag
  schemaRef := schemaRef
  schemaRef_injective := schemaRef_injective
  layout := layout
  materializer := materializer
  materializer_canonical := materializer_canonical
  rootBytes := ResourceBirthCodec.rootBytes

instance registryKindDecidableEq : DecidableEq registry.Kind :=
  inferInstanceAs (DecidableEq Kind)

/-- This is a source-fixed role mapping, never a caller-supplied callback.
Book is an internal account resource; accountMetadata is the user's identity. -/
def resourceKindOf : Kind → ResourceKind
  | .accountMetadata | .resourceBook => .account
  | .declaredProgram => .program
  | _ => .object

def factoryKind : Kind := .declaredObject

def sourceEncoding : ResourceBirth.SourceEncoding registry :=
  ResourceBirthCodec.sourceEncoding registry resourceKindOf

@[simp] theorem registry_content_materializer :
    registry.materializer .content = HyperdocumentCell.contentMaterializer := rfl
@[simp] theorem registry_event_materializer :
    registry.materializer .eventHistory = HyperdocumentCell.eventMaterializer := rfl
@[simp] theorem registry_authority_materializer :
    registry.materializer .authority = CredentialAuthorityCell.materializer := rfl
@[simp] theorem registry_book_materializer :
    registry.materializer .resourceBook = CanonicalResourcePageMaterializer.materializer := rfl
@[simp] theorem registry_factory_materializer :
    registry.materializer factoryKind = DeclaredEffectCell.materializer := rfl
@[simp] theorem registry_account_materializer :
    registry.materializer .accountMetadata = DeclaredEffectCell.materializer := rfl
@[simp] theorem registry_policy_source_materializer :
    registry.materializer .policySource = PolicySourceCell.materializer := rfl
@[simp] theorem registry_pay_materializer :
    registry.materializer .pay = Kernel.PayCell.materializer := rfl
@[simp] theorem registry_stream_materializer :
    registry.materializer .stream = StreamCell.headMaterializer := rfl
@[simp] theorem registry_nock_program_materializer :
    registry.materializer .nockProgram = NockProgramCodec.materializer := rfl
@[simp] theorem registry_program_materializer :
    registry.materializer .declaredProgram = DeclaredEffectCell.materializer := rfl
@[simp] theorem registry_lifecycle_root :
    registry.rootBytes = ResourceBirthCodec.rootBytes := rfl

/-- Dependent decoding preserves the exact selected native codec/root. The
envelope is canonical (`PackedCell.bytes_of_decode`: the tag cannot alias and
every materializer codec accepts only encodings), so nothing is re-encoded. -/
def cellCodec : LawfulCodec (PackedCell registry) := PackedCell.codec registry

@[simp] theorem cell_roundtrip (cell : PackedCell registry) :
    cellCodec.decode (cellCodec.encode cell) = some cell := cellCodec.decode_encode cell

theorem decoded_cell_canonical {bytes : List UInt8} {cell : PackedCell registry}
    (accepted : cellCodec.decode bytes = some cell) : PackedCell.bytes registry cell = bytes :=
  PackedCell.bytes_of_decode registry accepted

/-! ## Source-owned role and identity laws -/

/-- Pins belong to one deployment/authority domain. They do not impose one
Book across all nodes or domains. A request cannot choose a different Book or
authority cell merely because its payload has the right schema tag. -/
structure Deployment where
  domain : Digest
  factoryId : Nat
  resourceBookId : Nat
  authorityCellId : Nat
  deriving DecidableEq, Repr

def Deployment.Valid (deployment : Deployment) : Prop :=
  [deployment.factoryId, deployment.resourceBookId, deployment.authorityCellId].Nodup

instance deploymentValidDecidable (deployment : Deployment) : Decidable deployment.Valid := by
  unfold Deployment.Valid
  infer_instance

/-- Field constructors, not textual key names, determine role membership.
The account role's cell contains metadata only; it cannot encode money. -/
def KeyAllowed (kind : ResourceKind) (cellId : Nat) : StateKey → Prop
  | .objectField object _ =>
      (kind = .object ∨ kind = .account) ∧ object.value = cellId
  | .programCode program => kind = .program ∧ program.value = cellId
  | .accountBalance _ _ => False
  | .blinding => True
  -- A cell's declaration (K-FIELD-CLOSURE) is its own: it names this cell.
  | .fieldDeclared object _ =>
      (kind = .object ∨ kind = .account) ∧ object.value = cellId
  | .fieldsOpen object =>
      (kind = .object ∨ kind = .account) ∧ object.value = cellId
  | .fieldsFrom object =>
      (kind = .object ∨ kind = .account) ∧ object.value = cellId

instance keyAllowedDecidable (kind : ResourceKind) (cellId : Nat) (key : StateKey) :
    Decidable (KeyAllowed kind cellId key) := by
  cases key <;> unfold KeyAllowed <;> infer_instance

theorem accountBalance_never_allowed (kind : ResourceKind) (cellId : Nat)
    (account : ResourceId .account) (asset : Digest) :
    ¬KeyAllowed kind cellId (.accountBalance account asset) := fun impossible => impossible

/-- The key law: every present key is a key this role allows at this cell.
There is no capacity, no shard number and no in-cell domain tag: the cell's
domain is the directory that holds it. -/
def KeyLaw (kind : ResourceKind) (cellId : Nat) (store : Store effectLayout) : Prop :=
  ∀ address ∈ store.support, KeyAllowed kind cellId address.2

instance keyLawDecidable (kind : ResourceKind) (cellId : Nat)
    (store : Store effectLayout) : Decidable (KeyLaw kind cellId store) := by
  unfold KeyLaw
  infer_instance

/-- The declared-cell law: the key law, and the cell holds only the fields it
declares (K-FIELD-CLOSURE, `FieldClosure.Closed`).  A cell that declares
nothing holds no object field; an open cell declares `fieldsOpen`. -/
def DeclaredCellLaw (kind : ResourceKind) (cellId : Nat) (store : Store effectLayout) : Prop :=
  KeyLaw kind cellId store ∧ Kernel.FieldClosure.Closed cellId store

instance declaredCellLawDecidable (kind : ResourceKind) (cellId : Nat)
    (store : Store effectLayout) : Decidable (DeclaredCellLaw kind cellId store) := by
  unfold DeclaredCellLaw
  infer_instance

theorem DeclaredCellLaw.no_balance (kind : ResourceKind) (cellId : Nat)
    (store : Store effectLayout) (law : DeclaredCellLaw kind cellId store)
    (account : ResourceId .account) (asset : Digest) :
    store (StateKey.accountBalance account asset).address = none := by
  by_contra present
  exact law.1 _ (DFinsupp.mem_support_toFun _ _ |>.mpr present)

/-- **`declared_fields_admit_as_before`.** For a write from a lawful cell that
leaves its declaration unchanged and changes only declared fields
(`FieldClosure.check` names nothing), the cell law decides exactly what the key
law decided before K-FIELD-CLOSURE: nothing inside the declaration got stricter
or looser. -/
theorem declared_fields_admit_as_before {kind : ResourceKind} {cellId : Nat}
    {pre post : Store effectLayout} (preLaw : DeclaredCellLaw kind cellId pre)
    (sameDeclaration : ∀ n, Kernel.FieldClosure.declaredIn cellId post n =
      Kernel.FieldClosure.declaredIn cellId pre n)
    (inside : Kernel.FieldClosure.check cellId pre post = none) :
    DeclaredCellLaw kind cellId post ↔ KeyLaw kind cellId post :=
  ⟨And.left, fun keys =>
    ⟨keys, Kernel.FieldClosure.closed_preserved preLaw.2 sameDeclaration inside⟩⟩

def PresentLaw {α : Type} (law : α → Prop) : Option α → Prop
  | none => False
  | some value => law value

instance presentLawDecidable {α : Type} (law : α → Prop) [∀ value, Decidable (law value)]
    (value : Option α) : Decidable (PresentLaw law value) := by
  cases value <;> unfold PresentLaw <;> infer_instance

/-! ### Hyperdocument content: one document per cell -/

/-- The document a content record belongs to, where the record names one.
Element-owned fields and their conflicts are located through the element. -/
def recordDocument? : (space : Hyperdocument.Namespace) → Hyperdocument.Key space →
    Hyperdocument.Value space → Option DocumentId
  | .documents, document, _ => some document
  | .atoms, _, record => some record.document
  | .runs, _, record => some record.document
  | .elements, _, record => some record.document
  | .fields, key, _ =>
      match key.owner with
      | .document document => some document
      | .element _ => none
  | .conflicts, _, record =>
      match record.field.owner with
      | .document document => some document
      | .element _ => none
  | .links, _, record => some record.sourceDocument
  | .transclusions, _, record => some record.hostDocument
  | .marks, _, record => some record.document
  | .annotations, _, record => some record.document
  | .blinding, _, _ => none

/-- The document named by the record at `address`, if any. -/
def documentAt (store : Store Hyperdocument.layout)
    (address : Store.Address Hyperdocument.layout) : Option DocumentId :=
  (store address).bind (recordDocument? address.1 address.2)

/-- A content cell holds one document: every record that names a document
names the same one (the retired content page's `Entry.LocalTo`, over every
namespace). -/
def ContentLaw (store : Store Hyperdocument.layout) : Prop :=
  ∀ left ∈ store.support, ∀ right ∈ store.support,
    documentAt store left = none ∨ documentAt store right = none ∨
      documentAt store left = documentAt store right

/-- All present values in one computed list agree. Absent values carry no
constraint; the first present value is the candidate for the single `all` pass. -/
private def allPresentEqual {α : Type} [DecidableEq α] (values : List (Option α)) : Bool :=
  match values.filterMap id with
  | [] => true
  | first :: rest => rest.all fun value => decide (value = first)

private theorem allPresentEqual_iff {α : Type} [DecidableEq α] (values : List (Option α)) :
    allPresentEqual values = true ↔
      ∀ left ∈ values, ∀ right ∈ values,
        left = none ∨ right = none ∨ left = right := by
  have original_of_present : ∀ {value : α}, value ∈ values.filterMap id → some value ∈ values := by
    intro value member
    obtain ⟨entry, entryMember, selected⟩ := List.mem_filterMap.mp member
    cases entry with
    | none => simp at selected
    | some actual =>
      simp only [id_eq, Option.some.injEq] at selected
      subst actual
      exact entryMember
  unfold allPresentEqual
  cases present : values.filterMap id with
  | nil =>
    simp only [true_iff]
    intro left leftMember right _
    cases left with
    | none => exact Or.inl rfl
    | some left =>
      cases right with
      | none => exact Or.inr (Or.inl rfl)
      | some right =>
        have member : left ∈ values.filterMap id :=
          List.mem_filterMap.mpr ⟨some left, leftMember, rfl⟩
        rw [present] at member
        simp at member
  | cons first rest =>
    constructor
    · intro checked left leftMember right rightMember
      have equal_first : ∀ {value : α}, value ∈ first :: rest → value = first := by
        intro value member
        rcases List.mem_cons.mp member with rfl | member
        · rfl
        · exact of_decide_eq_true (List.all_eq_true.mp checked value member)
      have present_of_original : ∀ {value : α}, some value ∈ values → value ∈ first :: rest := by
        intro value member
        rw [← present]
        exact List.mem_filterMap.mpr ⟨some value, member, rfl⟩
      cases left with
      | none => exact Or.inl rfl
      | some left =>
        cases right with
        | none => exact Or.inr (Or.inl rfl)
        | some right =>
          exact Or.inr (Or.inr (congrArg some ((equal_first (present_of_original leftMember)).trans
            (equal_first (present_of_original rightMember)).symm)))
    · intro law
      apply List.all_eq_true.mpr
      intro value member
      apply decide_eq_true
      have firstPresent : first ∈ values.filterMap id := by
        rw [present]
        exact List.mem_cons_self
      have valuePresent : value ∈ values.filterMap id := by
        rw [present]
        exact List.mem_cons_of_mem _ member
      rcases law (some first) (original_of_present firstPresent)
          (some value) (original_of_present valuePresent) with absent | absent | same
      · cases absent
      · cases absent
      · exact (Option.some.inj same).symm

/-- The same linear check on a multiset, using its computable list representative.
The result does not depend on which representative the quotient exposes. -/
private def allPresentEqualMultiset {α : Type} [DecidableEq α] (values : Multiset (Option α)) : Bool :=
  Quot.liftOn values allPresentEqual fun left right perm => by
    have same : allPresentEqual left = true ↔ allPresentEqual right = true := by
      rw [allPresentEqual_iff, allPresentEqual_iff]
      constructor
      · intro law l leftMember r rightMember
        exact law l (perm.mem_iff.mpr leftMember) r (perm.mem_iff.mpr rightMember)
      · intro law l leftMember r rightMember
        exact law l (perm.mem_iff.mp leftMember) r (perm.mem_iff.mp rightMember)
    cases leftResult : allPresentEqual left <;> cases rightResult : allPresentEqual right <;> simp_all

private theorem allPresentEqualMultiset_iff {α : Type} [DecidableEq α]
    (values : Multiset (Option α)) :
    allPresentEqualMultiset values = true ↔
      ∀ left ∈ values, ∀ right ∈ values,
        left = none ∨ right = none ∨ left = right := by
  induction values using Quot.inductionOn with
  | _ values => exact allPresentEqual_iff values

instance contentLawDecidable (store : Store Hyperdocument.layout) :
    Decidable (ContentLaw store) := by
  -- The support by the cached canonical-key sort (`supportCached_eq`), not `Multiset.toFinset`'s
  -- quadratic dedup: this check runs on every content read and write.
  apply decidable_of_iff
    (allPresentEqualMultiset ((FiniteDependentMapCachedOrdering.supportCached
      (StoreCodec.addressKey HyperdocumentCell.contentWire)
      (StoreCodec.addressKey_injective HyperdocumentCell.contentWire) store).val.map
        (documentAt store)) = true)
  rw [FiniteDependentMapCachedOrdering.supportCached_eq]
  symm
  unfold ContentLaw
  rw [allPresentEqualMultiset_iff]
  constructor
  · intro law left leftMember right rightMember
    obtain ⟨leftAddress, leftSupport, rfl⟩ := Multiset.mem_map.mp leftMember
    obtain ⟨rightAddress, rightSupport, rfl⟩ := Multiset.mem_map.mp rightMember
    exact law leftAddress (by simpa using leftSupport) rightAddress (by simpa using rightSupport)
  · intro checked left leftSupport right rightSupport
    exact checked (documentAt store left)
      (Multiset.mem_map.mpr ⟨left, by simpa using leftSupport, rfl⟩)
      (documentAt store right)
      (Multiset.mem_map.mpr ⟨right, by simpa using rightSupport, rfl⟩)

/-! ### Hyperdocument event history: this domain's well-formed, addressed events -/

local instance eventWellFormedDecidable (event : CausalVersionDag.EventPreimage) :
    Decidable event.WellFormed :=
  decidable_of_iff
    (event.parentFrontier.Pairwise (fun left right => left.value < right.value) ∧
      event.parentFrontier.Nodup)
    ⟨fun valid => ⟨valid.1, valid.2⟩,
      fun valid => ⟨valid.parentFrontierCanonical, valid.parentFrontierUnique⟩⟩

/-- One recorded event is valid in this deployment: it names this deployment's
history domain, its parent frontier is canonical, and its key is the derived
event address of its causal preimage. -/
def EventValid (deployment : Deployment) (key : VersionEventId) :
    Option VersionEventRecord → Prop
  | none => True
  | some record =>
      record.historyDomain = deployment.domain ∧ record.CausallyWellFormed ∧
        key.digest = HyperdocumentCell.eventScheme.address record.toCausalPreimage

instance eventValidDecidable (deployment : Deployment) (key : VersionEventId)
    (record : Option VersionEventRecord) : Decidable (EventValid deployment key record) := by
  cases record <;> unfold EventValid <;> infer_instance

/-- The event-log law: every recorded event is valid here, and all events are
of one document (the retired event page's scope). -/
def EventHistoryLaw (deployment : Deployment)
    (store : Store Kernel.HyperdocumentEventLog.Sparse.layout) : Prop :=
  (∀ address ∈ store.support, EventValid deployment address.2 (store address)) ∧
    ∀ left ∈ store.support, ∀ right ∈ store.support,
      (store left).map VersionEventRecord.document = (store right).map VersionEventRecord.document

instance eventHistoryLawDecidable (deployment : Deployment)
    (store : Store Kernel.HyperdocumentEventLog.Sparse.layout) :
    Decidable (EventHistoryLaw deployment store) := by
  -- The support by the cached canonical-key sort, as in `contentLawDecidable`: the event log
  -- grows by one record per document version, and this check runs on every append.
  apply decidable_of_iff
    ((∀ address ∈ FiniteDependentMapCachedOrdering.supportCached
        (StoreCodec.addressKey HyperdocumentCell.eventWire)
        (StoreCodec.addressKey_injective HyperdocumentCell.eventWire) store,
        EventValid deployment address.2 (store address)) ∧
      allPresentEqualMultiset ((FiniteDependentMapCachedOrdering.supportCached
        (StoreCodec.addressKey HyperdocumentCell.eventWire)
        (StoreCodec.addressKey_injective HyperdocumentCell.eventWire) store).val.map fun address =>
        (store address).map VersionEventRecord.document) = true)
  rw [FiniteDependentMapCachedOrdering.supportCached_eq]
  symm
  unfold EventHistoryLaw
  constructor
  · rintro ⟨valid, same⟩
    refine ⟨valid, ?_⟩
    rw [allPresentEqualMultiset_iff]
    intro left leftMember right rightMember
    obtain ⟨leftAddress, leftSupport, rfl⟩ := Multiset.mem_map.mp leftMember
    obtain ⟨rightAddress, rightSupport, rfl⟩ := Multiset.mem_map.mp rightMember
    exact Or.inr (Or.inr (same leftAddress (by simpa using leftSupport)
      rightAddress (by simpa using rightSupport)))
  · rintro ⟨valid, checked⟩
    refine ⟨valid, ?_⟩
    rw [allPresentEqualMultiset_iff] at checked
    intro left leftSupport right rightSupport
    have compared := checked
      ((store left).map VersionEventRecord.document)
      (Multiset.mem_map.mpr ⟨left, by simpa using leftSupport, rfl⟩)
      ((store right).map VersionEventRecord.document)
      (Multiset.mem_map.mpr ⟨right, by simpa using rightSupport, rfl⟩)
    cases leftValue : store left with
    | none => exact ((DFinsupp.mem_support_toFun _ _).mp leftSupport leftValue).elim
    | some leftRecord =>
      cases rightValue : store right with
      | none => exact ((DFinsupp.mem_support_toFun _ _).mp rightSupport rightValue).elim
      | some rightRecord => simpa [leftValue, rightValue] using compared

/-- **The domain restoration (S3 decision 1).**  An event record naming any
other history domain cannot sit in this deployment's event log. -/
theorem foreign_domain_event_refused (deployment : Deployment)
    (store : Store Kernel.HyperdocumentEventLog.Sparse.layout)
    (address : Store.Address Kernel.HyperdocumentEventLog.Sparse.layout) (record : VersionEventRecord)
    (present : store address = some record) (foreign : record.historyDomain ≠ deployment.domain) :
    ¬ EventHistoryLaw deployment store := by
  intro law
  have valid := law.1 address (DFinsupp.mem_support_toFun _ _ |>.mpr (by rw [present]; intro same; cases same))
  rw [present] at valid
  exact foreign valid.1

/-- Satisfiable pole: the empty event log is lawful in every deployment. -/
theorem empty_event_history_lawful (deployment : Deployment) :
    EventHistoryLaw deployment 0 := by
  constructor <;> intro address member <;> simp at member

/-- Semantic identity of the source-owned loaded/final law.  v11 (INTEGRATOR-3): the proof braid's
v9 (CH-EPOCH stream law, store encoding v2, blinded cells) and the compute braid's v10
(K-FIELD-CLOSURE: declared cells closed by default; C14's tail-bound genesis cell) meet here. Each
of v9 and v10 named a law set without the other, so a Store under any earlier label refuses. -/
def logicalLawVersion : List UInt8 :=
  Minidregg.Compiler.PersistedCodecTags.registry_loaded_and_final_store_cells_v17.toUTF8.toList

/-- Checked both on the loaded cell and on the ACTUAL final joint post, after
all effects have composed. Local candidate validity alone does not imply this. -/
def LogicalLaw (deployment : Deployment) (cellId : Nat) :
    (kind : Kind) → Store (layout kind) → Prop
  | .worldKind, state => WorldKindCell.definitionLaw cellId state
  | .worldInstance, state => WorldKindCell.instanceLaw state
  | .declaredObject, state => DeclaredCellLaw .object cellId state
  | .accountMetadata, state => DeclaredCellLaw .account cellId state
  | .declaredProgram, state => DeclaredCellLaw .program cellId state
  | .content, state => ContentLaw state
  | .eventHistory, state => EventHistoryLaw deployment state
  | .authority, _ => cellId = deployment.authorityCellId
  | .resourceBook, state => cellId = deployment.resourceBookId ∧
      (CanonicalResourcePageMaterializer.bookAt state).isSome = true ∧
      (CanonicalResourceKernel.logicalBook state).AccountSupported
  | .policySource, state => PresentLaw (PolicySourceCell.SourceValid deployment.domain cellId)
      (PolicySourceCell.recordAt state)
  | .pay, state => cellId = Kernel.PayCell.physicalId deployment.domain ∧ Kernel.PayCell.Law state
  | .stream, state => StreamCell.HeadLaw cellId state ∧ Kernel.DomainEpoch.ChannelStoreLaw state
  | .streamEntry, state => StreamCell.EntryLaw cellId state
  | .nockProgram, state => PresentLaw (NockProgramCodec.CellValid deployment.domain cellId)
      (NockProgramCodec.programAt state)
  | .clock, state => cellId = Kernel.ClockCell.physicalId deployment.domain ∧
      Kernel.ClockCell.Law state
  | .system, state => cellId = Kernel.SystemCell.physicalId deployment.domain ∧
      Kernel.SystemCell.Law state
  | .objectiveActivity, state => PresentLaw (Kernel.ObjectiveActivityCell.CellValid deployment.domain cellId)
      (Kernel.ObjectiveActivityCell.payloadAt state)
  | .seat, state => PresentLaw (Kernel.SeatCell.CellValid deployment.domain cellId)
      (Kernel.SeatCell.payloadAt state)
  | .platform, state => cellId = Kernel.PlatformCellLayout.physicalId deployment.domain ∧
      Kernel.PlatformCellLayout.Law state

instance logicalLawDecidable (deployment : Deployment) (cellId : Nat)
    (kind : Kind) (state : Store (layout kind)) :
    Decidable (LogicalLaw deployment cellId kind state) := by
  cases kind <;> unfold LogicalLaw <;> infer_instance

def CellLaw (deployment : Deployment) (cellId : Nat) (cell : PackedCell registry) : Prop :=
  deployment.Valid ∧ LogicalLaw deployment cellId cell.kind cell.payload.logical

set_option backward.isDefEq.respectTransparency false in
instance cellLawDecidable (deployment : Deployment) (cellId : Nat) (cell : PackedCell registry) :
    Decidable (CellLaw deployment cellId cell) := by
  unfold CellLaw
  infer_instance

def cellCheck (deployment : Deployment) (cellId : Nat) (cell : PackedCell registry) : Bool :=
  decide (CellLaw deployment cellId cell)

@[simp] theorem cellCheck_iff (deployment : Deployment) (cellId : Nat) (cell : PackedCell registry) :
    cellCheck deployment cellId cell = true ↔ CellLaw deployment cellId cell := by
  simp [cellCheck]

/-- The final-state admission uses the same fixed logical law as loaded-state
admission. A family must run this on the composed joint post, not cache a local
candidate's Boolean. The role is selected from the actual old packed cell. -/
def postStateCheck (deployment : Deployment) (cellId : Nat) (kind : Kind)
    (state : Store (layout kind)) : Bool :=
  decide (deployment.Valid ∧ LogicalLaw deployment cellId kind state)

@[simp] theorem postStateCheck_iff (deployment : Deployment) (cellId : Nat) (kind : Kind)
    (state : Store (layout kind)) :
    postStateCheck deployment cellId kind state = true ↔
      deployment.Valid ∧ LogicalLaw deployment cellId kind state := by
  simp [postStateCheck]

/-- The retained descriptor is immutable even for receivers whose outer patch
is supplied by a semantic family rather than the generic Store patch checker. -/
def instanceBinding (cell : PackedCell registry) : Option WorldKindCell.Binding :=
  match cell with
  | ⟨.worldInstance, payload⟩ => payload.logical WorldKindCell.descriptorAddress
  | _ => none

def instanceDescriptor (cell : PackedCell registry) : Option WorldKindDescriptor.Descriptor :=
  (instanceBinding cell).map WorldKindCell.Binding.descriptor

/-- The mandatory kind dependency is derived from the authenticated instance
payload, never from a command-provided list of extra policy parents. -/
def instanceKind (cell : PackedCell registry) : Option Nat :=
  (instanceDescriptor cell).map WorldKindDescriptor.Descriptor.kind

/-- A kind lookup reads a real live kind-definition cell and validates it at its
actual identity. Retired, absent, malformed and other-role cells return none. -/
def kindDefinition (deployment : Deployment) (directory : Directory Nat registry)
    (kindId : Nat) : Option WorldKindCell.Definition :=
  match directory.slots kindId with
  | .present cell =>
      if CellLaw deployment kindId cell then
        match cell with
        | ⟨.worldKind, payload⟩ => payload.logical WorldKindCell.definitionAddress
        | _ => none
      else none
  | _ => none

/-- Birth authenticates the chosen kind at the same old directory as the
allocation. Existing instances do not repeat this old-root comparison: their
current exported law is resolved separately for every admitted operation. -/
def kindBirthValid (deployment : Deployment) (directory : Directory Nat registry)
    (cell : PackedCell registry) : Bool :=
  match cell with
  | ⟨.worldInstance, payload⟩ =>
      match payload.logical WorldKindCell.descriptorAddress with
      | none => false
      | some binding =>
          match directory.slots binding.descriptor.kind with
          | .present ⟨.worldKind, source⟩ =>
              if CellLaw deployment binding.descriptor.kind ⟨.worldKind, source⟩ then
                match source.logical WorldKindCell.definitionAddress with
                | some definition => binding.kindRoot == source.root &&
                    WorldKindCell.birthMatches definition payload.logical
                | none => false
              else false
          | _ => false
  | _ => true

def FinalPostLaw (deployment : Deployment) (cellId : Nat)
    (before after : PackedCell registry) : Prop :=
  before.kind = after.kind ∧ CellLaw deployment cellId before ∧ CellLaw deployment cellId after ∧
    instanceBinding before = instanceBinding after ∧
    (before.kind = .policySource ∨ before.kind = .nockProgram →
      PackedCell.bytes registry before = PackedCell.bytes registry after)

set_option backward.isDefEq.respectTransparency false in
instance finalPostLawDecidable (deployment : Deployment) (cellId : Nat)
    (before after : PackedCell registry) : Decidable (FinalPostLaw deployment cellId before after) := by
  unfold FinalPostLaw
  infer_instance

/-- Neutral content genesis is an empty document cell, holding at most its
hiding key: the cell's identifier is the new document's identity.  Historical provenance, authority grants, Book
balances and policy sources are generated by their semantic controllers, never
injected as raw user initial payloads. -/
def UserShape : (kind : Kind) → Store (layout kind) → Prop
  | .worldKind, _ => True
  | .worldInstance, _ => True -- kindBirthValid is mandatory in concrete birth preparation
  | .declaredObject, _ | .accountMetadata, _ | .declaredProgram, _ => True
  | .content, state => ∀ address ∈ state.support, address = ⟨.blinding, ()⟩
  | .stream, state => StreamCell.headOf state = some StreamCell.emptyRoomHead
  | .nockProgram, state => PresentLaw Evaluator.RecordAdmissible (NockProgramCodec.programAt state)
  | .eventHistory, _ | .authority, _ | .resourceBook, _ | .policySource, _ | .pay, _ | .clock, _
  | .streamEntry, _ | .system, _ | .objectiveActivity, _ | .seat, _ | .platform, _ => False

instance userShapeDecidable (kind : Kind) (state : Store (layout kind)) :
    Decidable (UserShape kind state) := by
  cases kind <;> unfold UserShape <;> infer_instance

/-- A user birth: lawful at its id, of a user shape, and outside the activity
kernel families' protected coordinate space (`ProtectedCell.reservedBase`: activity and seat cells). -/
def UserInitial (deployment : Deployment) (cellId : Nat) (cell : PackedCell registry) : Prop :=
  (CellLaw deployment cellId cell ∧ UserShape cell.kind cell.payload.logical) ∧
    cellId < Kernel.ProtectedCell.reservedBase

set_option backward.isDefEq.respectTransparency false in
instance userInitialDecidable (deployment : Deployment) (cellId : Nat) (cell : PackedCell registry) :
    Decidable (UserInitial deployment cellId cell) := by
  unfold UserInitial
  infer_instance

def userInitialCheck (deployment : Deployment) (cellId : Nat) (cell : PackedCell registry) : Bool :=
  decide (UserInitial deployment cellId cell)

@[simp] theorem userInitialCheck_iff (deployment : Deployment) (cellId : Nat) (cell : PackedCell registry) :
    userInitialCheck deployment cellId cell = true ↔ UserInitial deployment cellId cell := by
  simp [userInitialCheck]

/-- **No birth squats an activity coordinate.** -/
theorem userInitial_not_activity_coordinate {deployment : Deployment} {cellId : Nat} {cell : PackedCell registry}
    (admitted : UserInitial deployment cellId cell) (domain : Digest) (role : Kernel.ObjectiveActivityCell.Role)
    (key : List UInt8) : cellId ≠ Kernel.ObjectiveActivityCell.coordinate domain role key := by
  exact Nat.ne_of_lt (lt_of_lt_of_le admitted.2 (Kernel.ObjectiveActivityCell.coordinate_reserved domain role key))

/-- **No birth squats a seat coordinate**: a seat account, an invitation, an
instance cell or a contract package. -/
theorem userInitial_not_seat_coordinate {deployment : Deployment} {cellId : Nat} {cell : PackedCell registry}
    (admitted : UserInitial deployment cellId cell) (domain : Digest) (role : Kernel.SeatCell.Role)
    (key : List UInt8) : cellId ≠ Kernel.SeatCell.coordinate domain role key :=
  Nat.ne_of_lt (lt_of_lt_of_le admitted.2 (Kernel.SeatCell.coordinate_reserved domain role key))

def BirthsAdmissible (deployment : Deployment) (descriptor : ResourceBirth.Descriptor registry) : Prop :=
  ∀ item ∈ descriptor.births, UserInitial deployment item.create.cellId item.create.cell

instance birthsAdmissibleDecidable (deployment : Deployment) (descriptor : ResourceBirth.Descriptor registry) :
    Decidable (BirthsAdmissible deployment descriptor) := by unfold BirthsAdmissible; infer_instance

/-- The shared layout is not authority to select another role's family.
Object requests cannot select account metadata with the same id. -/
def selectDeclared (deployment : Deployment) (cellId : Nat) (requested : ResourceKind)
    (cell : PackedCell registry) : Option (Materialized DeclaredEffectCell.materializer) :=
  if CellLaw deployment cellId cell then
    match requested, cell with
    | .object, ⟨.declaredObject, payload⟩ => some payload
    | .account, ⟨.accountMetadata, payload⟩ => some payload
    | .program, ⟨.declaredProgram, payload⟩ => some payload
    | _, _ => none
  else none

theorem object_cannot_select_account (deployment : Deployment) (cellId : Nat)
    (payload : Materialized DeclaredEffectCell.materializer) :
    selectDeclared deployment cellId .object ⟨.accountMetadata, payload⟩ = none := by
  unfold selectDeclared
  split <;> rfl

theorem book_identity_is_pinned (deployment : Deployment) (cellId : Nat)
    (payload : Materialized CanonicalResourcePageMaterializer.materializer)
    (valid : CellLaw deployment cellId ⟨.resourceBook, payload⟩) :
    cellId = deployment.resourceBookId := valid.2.1

/-- The one authority cell lives at the deployment's pinned identifier. -/
theorem authority_identity_is_pinned (deployment : Deployment) (cellId : Nat)
    (payload : Materialized CredentialAuthorityCell.materializer)
    (valid : CellLaw deployment cellId ⟨.authority, payload⟩) :
    cellId = deployment.authorityCellId := valid.2

/-- Loaded and final canonical Books cannot carry balances for unregistered
accounts. The lossless wire codec deliberately imposes no such semantic law. -/
theorem book_accountSupported (deployment : Deployment) (cellId : Nat)
    (payload : Materialized CanonicalResourcePageMaterializer.materializer)
    (valid : CellLaw deployment cellId ⟨.resourceBook, payload⟩) :
    (CanonicalResourceKernel.logicalBook payload.logical).AccountSupported := valid.2.2.2

theorem hidden_book_refused (deployment : Deployment) (cellId : Nat)
    (payload : Materialized CanonicalResourcePageMaterializer.materializer)
    (account asset : Nat)
    (absent : account ∉ (CanonicalResourceKernel.logicalBook payload.logical).accounts)
    (hidden : (CanonicalResourceKernel.logicalBook payload.logical).balance account asset ≠ 0) :
    ¬ CellLaw deployment cellId ⟨.resourceBook, payload⟩ := by
  intro valid
  exact hidden ((book_accountSupported _ _ _ valid).balance_zero absent asset)

theorem no_user_book_birth (deployment : Deployment) (cellId : Nat)
    (payload : Materialized CanonicalResourcePageMaterializer.materializer) :
    ¬UserInitial deployment cellId ⟨.resourceBook, payload⟩ := fun admitted => admitted.1.2

theorem no_user_authority_birth (deployment : Deployment) (cellId : Nat)
    (payload : Materialized CredentialAuthorityCell.materializer) :
    ¬UserInitial deployment cellId ⟨.authority, payload⟩ := fun admitted => admitted.1.2

theorem no_user_event_birth (deployment : Deployment) (cellId : Nat)
    (payload : Materialized HyperdocumentCell.eventMaterializer) :
    ¬UserInitial deployment cellId ⟨.eventHistory, payload⟩ := fun admitted => admitted.1.2

/-- The metadata identity is exactly the account registered by the existing
source-derived resource batch; it is not an independently funded Book. -/
theorem account_metadata_registered
    (descriptor : ResourceBirth.Descriptor registry) (item : ResourceBirth.BirthItem registry)
    (member : item ∈ descriptor.births)
    (actualKind : item.create.cell.kind = .accountMetadata)
    (kindBound : item.resourceKind = resourceKindOf item.create.cell.kind) :
    item.create.cellId ∈ descriptor.registeredAccounts := by
  have account : item.resourceKind = .account := by
    simpa [actualKind, resourceKindOf] using kindBound
  simp only [ResourceBirth.Descriptor.registeredAccounts, List.mem_filterMap]
  exact ⟨item, member, by simp [account]⟩

/-! ## Immutable policy source cells and same-directory source resolution -/

def policySourceCell (record : CanonicalPolicyAdmission.PolicyRecord) : PackedCell registry :=
  ⟨.policySource, materialize PolicySourceCell.materializer
    (PolicySourceCell.stateOfOption (some record))⟩

def policySourceCreate (domain : Digest) (record : CanonicalPolicyAdmission.PolicyRecord) :
    CreateRequest (CellId := Nat) registry where
  cellId := PolicySourceCell.physicalId domain (PolicyRecordCodec.digest record)
  expectedPreRoot := CellSlot.root registry .absent
  cell := policySourceCell record

theorem policySourceCreate_cell_law (deployment : Deployment)
    (record : CanonicalPolicyAdmission.PolicyRecord) (valid : deployment.Valid)
    (domainExact : record.domain = deployment.domain) :
    CellLaw deployment (policySourceCreate deployment.domain record).cellId
      (policySourceCreate deployment.domain record).cell := by
  change deployment.Valid ∧ PolicySourceCell.SourceValid deployment.domain
    (PolicySourceCell.physicalId deployment.domain (PolicyRecordCodec.digest record)) record
  exact ⟨valid, domainExact, rfl⟩

/-- Only records returned by the fixed initial-policy checker are used by the
birth receiver. This helper derives bytes and identifiers; lifecycle admission
still checks actual absence, permanent freshness and duplicate identifiers. -/
def initialSourceCreates (domain : Digest) (records : List CanonicalPolicyAdmission.PolicyRecord) :
    List (CreateRequest (CellId := Nat) registry) := records.map (policySourceCreate domain)

theorem initialSourceCreates_ids {F : Type} [Field F] {domain : Digest}
    {profile : CanonicalPolicyAdmission.PolicyCompilerProfile F}
    {initials : List ResourceBirth.InitialPolicy}
    (checked : PolicySourceCell.CheckedInitials domain profile initials) :
    (initialSourceCreates domain checked.records).map CreateRequest.cellId =
      PolicySourceCell.initialIds domain initials := by
  have hsimpa := checked.ids_exact
  simp [initialSourceCreates, policySourceCreate, List.map_map] at hsimpa ⊢
  exact hsimpa

structure LoadedPolicySource (domain : Digest) (directory : Directory Nat registry)
    (address : Digest) where
  payload : Materialized PolicySourceCell.materializer
  present : directory.slots (PolicySourceCell.physicalId domain address) =
    .present ⟨.policySource, payload⟩
  record : CanonicalPolicyAdmission.PolicyRecord
  recordExact : PolicySourceCell.recordAt payload.logical = some record
  domainExact : record.domain = domain
  addressExact : PolicyRecordCodec.digest record = address

def LoadedPolicySource.cell {domain : Digest} {directory : Directory Nat registry}
    {address : Digest} (loaded : LoadedPolicySource domain directory address) :
    PackedCell registry := ⟨.policySource, loaded.payload⟩

def LoadedPolicySource.cellId {domain : Digest} {directory : Directory Nat registry}
    {address : Digest} (_loaded : LoadedPolicySource domain directory address) : Nat :=
  PolicySourceCell.physicalId domain address

def LoadedPolicySource.canonicalBytes {domain : Digest} {directory : Directory Nat registry}
    {address : Digest} (loaded : LoadedPolicySource domain directory address) : List UInt8 :=
  PolicyRecordCodec.encode loaded.record

/-- The guard is over the actual outer physical cell, not the content digest
or the singleton payload's native materializer root. -/
def LoadedPolicySource.readGuard {domain : Digest} {directory : Directory Nat registry}
    {address : Digest} (loaded : LoadedPolicySource domain directory address) : Nat × Digest :=
  (loaded.cellId, ResourceBirthCodec.physicalRoot (.live loaded.cell))

theorem LoadedPolicySource.lifecycle_exact {domain : Digest} {directory : Directory Nat registry}
    {address : Digest} (loaded : LoadedPolicySource domain directory address) :
    ResourceBirthCodec.LifecycleImage.view registry directory loaded.cellId = .live loaded.cell :=
  (ResourceBirthCodec.LifecycleImage.view_live_iff registry directory loaded.cellId loaded.cell).mpr
    loaded.present

theorem LoadedPolicySource.readGuard_exact {domain : Digest} {directory : Directory Nat registry}
    {address : Digest} (loaded : LoadedPolicySource domain directory address) :
    loaded.readGuard.2 = ResourceBirthCodec.rootBytes
      (ResourceBirthCodec.LifecycleImage.bytes registry
        (ResourceBirthCodec.LifecycleImage.view registry directory loaded.cellId)) := by
  rw [loaded.lifecycle_exact]
  rfl

theorem LoadedPolicySource.cell_exact {domain : Digest} {directory : Directory Nat registry}
    {address : Digest} (loaded : LoadedPolicySource domain directory address) :
    loaded.cell = policySourceCell loaded.record := by
  have stateExact := PolicySourceCell.state_ext loaded.payload.logical
  rw [loaded.recordExact] at stateExact
  exact congrArg (fun (payload : Materialized PolicySourceCell.materializer) =>
      (⟨.policySource, payload⟩ : PackedCell registry))
    (Materialized.ext stateExact)

theorem LoadedPolicySource.record_of_present {domain : Digest} {directory : Directory Nat registry}
    {address : Digest} (loaded : LoadedPolicySource domain directory address)
    (record : CanonicalPolicyAdmission.PolicyRecord)
    (present : directory.slots loaded.cellId = .present (policySourceCell record)) :
    loaded.record = record := by
  have sameCell : loaded.cell = policySourceCell record :=
    CellSlot.present.inj (loaded.present.symm.trans present)
  have sameRecord := congrArg (fun (cell : PackedCell registry) =>
    match cell with
    | ⟨.policySource, payload⟩ => PolicySourceCell.recordAt payload.logical
    | _ => none) sameCell
  change PolicySourceCell.recordAt loaded.payload.logical = some record at sameRecord
  rw [loaded.recordExact] at sameRecord
  exact Option.some.inj sameRecord

theorem LoadedPolicySource.bytes_decode {domain : Digest} {directory : Directory Nat registry}
    {address : Digest} (loaded : LoadedPolicySource domain directory address) :
    PolicyRecordCodec.decode loaded.canonicalBytes = some loaded.record :=
  PolicyRecordCodec.decode_encode loaded.record

theorem LoadedPolicySource.bytes_digest {domain : Digest} {directory : Directory Nat registry}
    {address : Digest} (loaded : LoadedPolicySource domain directory address) :
    PolicyRecordCodec.hashBytes loaded.canonicalBytes = address := loaded.addressExact

def loadPolicySource (domain : Digest) (directory : Directory Nat registry) (address : Digest) :
    Option (LoadedPolicySource domain directory address) :=
  match present : directory.slots (PolicySourceCell.physicalId domain address) with
  | .present ⟨.policySource, payload⟩ =>
      match found : PolicySourceCell.recordAt payload.logical with
      | none => none
      | some record =>
          if valid : record.domain = domain ∧ PolicyRecordCodec.digest record = address then
            some ⟨payload, present, record, found, valid.1, valid.2⟩
          else none
  | _ => none

def fetchPolicySource (domain : Digest) (directory : Directory Nat registry) (address : Digest) :
    Option (List UInt8) :=
  (loadPolicySource domain directory address).map LoadedPolicySource.canonicalBytes

/-- `fetchPolicySource`, compiled: the record is encoded once, for both its digest and the bytes
returned (`fetchPolicySource_eq_fast`). -/
def fetchPolicySourceFast (domain : Digest) (directory : Directory Nat registry) (address : Digest) :
    Option (List UInt8) :=
  match directory.slots (PolicySourceCell.physicalId domain address) with
  | .present ⟨.policySource, payload⟩ =>
      match PolicySourceCell.recordAt payload.logical with
      | none => none
      | some record =>
          let bytes := PolicyRecordCodec.encode record
          if record.domain = domain ∧ PolicyRecordCodec.hashBytes bytes = address then some bytes
          else none
  | _ => none

@[csimp] theorem fetchPolicySource_eq_fast : @fetchPolicySource = @fetchPolicySourceFast := by
  funext domain directory address
  unfold fetchPolicySource fetchPolicySourceFast loadPolicySource
  split
  next payload slot =>
    simp only [slot]
    split
    next found => simp [found]
    next record found =>
      simp only [found]
      by_cases valid : record.domain = domain ∧ PolicyRecordCodec.digest record = address
      · rw [dif_pos valid, if_pos (by simpa [PolicyRecordCodec.digest] using valid)]
        rfl
      · rw [dif_neg valid, if_neg (by simpa [PolicyRecordCodec.digest] using valid)]
        rfl
  next absent =>
    split
    next payload slot => exact absurd slot (absent payload)
    next => rfl

set_option backward.isDefEq.respectTransparency false in
theorem fetchPolicySource_exact (domain : Digest) (directory : Directory Nat registry)
    (address : Digest) (record : CanonicalPolicyAdmission.PolicyRecord)
    (present : directory.slots (PolicySourceCell.physicalId domain address) =
      .present (policySourceCell record))
    (domainExact : record.domain = domain)
    (addressExact : PolicyRecordCodec.digest record = address) :
    fetchPolicySource domain directory address = some (PolicyRecordCodec.encode record) := by
  unfold fetchPolicySource loadPolicySource
  split
  next payload found =>
    have actual := congrArg (fun (slot : CellSlot registry) =>
      match slot with
      | .present ⟨.policySource, payload⟩ => PolicySourceCell.recordAt payload.logical
      | _ => none) (found.symm.trans present)
    change PolicySourceCell.recordAt payload.logical = some record at actual
    split
    next absent => simp [actual] at absent
    next selected selectedAt =>
      have same : selected = record := Option.some.inj (selectedAt.symm.trans actual)
      subst selected
      simp [domainExact, addressExact, LoadedPolicySource.canonicalBytes]
  next => simp_all [policySourceCell]

set_option backward.isDefEq.respectTransparency false in
theorem missing_policy_source_refused (domain : Digest) (directory : Directory Nat registry)
    (address : Digest)
    (missing : directory.slots (PolicySourceCell.physicalId domain address) = .absent) :
    fetchPolicySource domain directory address = none := by
  simp [fetchPolicySource, loadPolicySource, missing]

set_option backward.isDefEq.respectTransparency false in
theorem wrong_policy_source_kind_refused (domain : Digest) (directory : Directory Nat registry)
    (address : Digest) (cell : PackedCell registry)
    (present : directory.slots (PolicySourceCell.physicalId domain address) = .present cell)
    (wrongKind : cell.kind ≠ .policySource) :
    fetchPolicySource domain directory address = none := by
  rcases cell with ⟨kind, payload⟩
  cases kind <;> simp_all [fetchPolicySource, loadPolicySource]

theorem wrong_policy_source_domain_refused (domain : Digest) (directory : Directory Nat registry)
    (address : Digest) (record : CanonicalPolicyAdmission.PolicyRecord)
    (present : directory.slots (PolicySourceCell.physicalId domain address) =
      .present (policySourceCell record))
    (wrongDomain : record.domain ≠ domain) :
    fetchPolicySource domain directory address = none := by
  cases result : loadPolicySource domain directory address with
  | none => simp [fetchPolicySource, result]
  | some loaded =>
      have same := loaded.record_of_present record present
      have domainExact := loaded.domainExact
      rw [same] at domainExact
      exact False.elim (wrongDomain domainExact)

theorem wrong_policy_source_digest_refused (domain : Digest) (directory : Directory Nat registry)
    (address : Digest) (record : CanonicalPolicyAdmission.PolicyRecord)
    (present : directory.slots (PolicySourceCell.physicalId domain address) =
      .present (policySourceCell record))
    (wrongDigest : PolicyRecordCodec.digest record ≠ address) :
    fetchPolicySource domain directory address = none := by
  cases result : loadPolicySource domain directory address with
  | none => simp [fetchPolicySource, result]
  | some loaded =>
      have same := loaded.record_of_present record present
      have addressExact := loaded.addressExact
      rw [same] at addressExact
      exact False.elim (wrongDigest addressExact)

theorem policy_source_no_user_birth (deployment : Deployment) (cellId : Nat)
    (payload : Materialized PolicySourceCell.materializer) :
    ¬UserInitial deployment cellId ⟨.policySource, payload⟩ := fun admitted => admitted.1.2

theorem policy_source_final_bytes_immutable (deployment : Deployment) (cellId : Nat)
    (before after : PackedCell registry) (source : before.kind = .policySource)
    (valid : FinalPostLaw deployment cellId before after) :
    PackedCell.bytes registry before = PackedCell.bytes registry after := valid.2.2.2.2 (Or.inl source)

theorem policy_source_final_state_immutable (deployment : Deployment) (cellId : Nat)
    (before after : PackedCell registry) (source : before.kind = .policySource)
    (valid : FinalPostLaw deployment cellId before after) : before = after := by
  have bytesExact : cellCodec.encode before = cellCodec.encode after :=
    policy_source_final_bytes_immutable deployment cellId before after source valid
  have same := congrArg cellCodec.decode bytesExact
  rw [cellCodec.decode_encode, cellCodec.decode_encode] at same
  exact Option.some.inj same

theorem policy_source_occupied_refused (domain : Digest) (directory : Directory Nat registry)
    (record : CanonicalPolicyAdmission.PolicyRecord) (occupant : PackedCell registry)
    (occupied : directory.slots (policySourceCreate domain record).cellId = .present occupant) :
    CellRegistry.create registry directory (policySourceCreate domain record) =
      .error .duplicateCreate := by
  simp [CellRegistry.create, occupied]

theorem policy_source_retired_refused (domain : Digest) (directory : Directory Nat registry)
    (record : CanonicalPolicyAdmission.PolicyRecord)
    (absent : directory.slots (policySourceCreate domain record).cellId = .absent)
    (used : (policySourceCreate domain record).cellId ∈ directory.used) :
    CellRegistry.create registry directory (policySourceCreate domain record) =
      .error .retiredIdentifier := by
  simp [CellRegistry.create, absent, used]

theorem policy_source_identifier_collision_refused (domain : Digest)
    (directory : Directory Nat registry) (left right : CanonicalPolicyAdmission.PolicyRecord)
    (collision : (policySourceCreate domain left).cellId =
      (policySourceCreate domain right).cellId) :
    CellRegistry.create registry
      (Directory.insert registry directory (policySourceCreate domain left).cellId
        (policySourceCell left))
      (policySourceCreate domain right) = .error .duplicateCreate := by
  apply policy_source_occupied_refused domain _ right (policySourceCell left)
  rw [collision]
  exact Directory.insert_slot registry directory _ _

/-! ## Nock program cells: content-addressed, immutable, born by friends

A program cell is born through the ordinary resource birth (its creator's law,
its creator's owner grant), never by a special capability. Its identifier is its
content address, so the same record born twice meets an occupied identifier
(`program_occupied_refused`); a different ABI over the same jam is a different
program at a different identifier. -/

def programCell (program : NockProgramCodec.Program) : PackedCell registry :=
  ⟨.nockProgram, materialize NockProgramCodec.materializer
    (NockProgramCodec.stateOfOption (some program))⟩

def programCellId (domain : Digest) (program : NockProgramCodec.Program) : Nat :=
  NockProgramCodec.physicalId domain (NockProgramCodec.programId program)

def programCreate (domain : Digest) (program : NockProgramCodec.Program) :
    CreateRequest (CellId := Nat) registry where
  cellId := programCellId domain program
  expectedPreRoot := CellSlot.root registry .absent
  cell := programCell program

/-- The program a packed cell holds, if it is a program cell. -/
def cellProgram : PackedCell registry → Option NockProgramCodec.Program
  | ⟨.nockProgram, payload⟩ => NockProgramCodec.programAt payload.logical
  | _ => none

@[simp] theorem cellProgram_programCell (program : NockProgramCodec.Program) :
    cellProgram (programCell program) = some program := by
  simp [cellProgram, programCell]

/-- The program at `id`'s address in this directory, checked against the address. -/
def loadProgram (domain : Digest) (directory : Directory Nat registry) (id : Digest) :
    Option NockProgramCodec.Program :=
  match directory.slots (NockProgramCodec.physicalId domain id) with
  | .present cell =>
      match cellProgram cell with
      | some program => if NockProgramCodec.programId program = id then some program else none
      | none => none
  | _ => none

theorem loadProgram_present (domain : Digest) (directory : Directory Nat registry)
    (program : NockProgramCodec.Program)
    (present : directory.slots (programCellId domain program) = .present (programCell program)) :
    loadProgram domain directory (NockProgramCodec.programId program) = some program := by
  unfold loadProgram
  rw [show NockProgramCodec.physicalId domain (NockProgramCodec.programId program) =
    programCellId domain program from rfl, present]
  simp

theorem loadProgram_programId {domain : Digest} {directory : Directory Nat registry}
    {id : Digest} {program : NockProgramCodec.Program}
    (loaded : loadProgram domain directory id = some program) :
    NockProgramCodec.programId program = id := by
  unfold loadProgram at loaded
  split at loaded
  · split at loaded
    · split at loaded
      · rename_i same
        cases loaded
        exact same
      · cases loaded
    · cases loaded
  · cases loaded

theorem missing_program_refused (domain : Digest) (directory : Directory Nat registry)
    (id : Digest) (missing : directory.slots (NockProgramCodec.physicalId domain id) = .absent) :
    loadProgram domain directory id = none := by
  simp [loadProgram, missing]

/-- Every library a program names is a program cell present here. -/
def librariesPresent (domain : Digest) (directory : Directory Nat registry)
    (program : NockProgramCodec.Program) : Bool :=
  program.abi.libraries.all fun library => (loadProgram domain directory library).isSome

/-- Every program born by `descriptor` names only libraries already present. -/
def birthLibrariesPresent (domain : Digest) (directory : Directory Nat registry)
    (descriptor : ResourceBirth.Descriptor registry) : Bool :=
  descriptor.births.all fun item =>
    match cellProgram item.create.cell with
    | none => true
    | some program => librariesPresent domain directory program

theorem missing_library_refused (domain : Digest) (directory : Directory Nat registry)
    (program : NockProgramCodec.Program) (library : Digest)
    (named : library ∈ program.abi.libraries)
    (missing : loadProgram domain directory library = none) :
    librariesPresent domain directory program = false := by
  unfold librariesPresent
  rw [List.all_eq_false]
  exact ⟨library, named, by simp [missing]⟩

theorem birth_missing_library_refused (domain : Digest) (directory : Directory Nat registry)
    (descriptor : ResourceBirth.Descriptor registry) (item : ResourceBirth.BirthItem registry)
    (member : item ∈ descriptor.births) (program : NockProgramCodec.Program)
    (holds : cellProgram item.create.cell = some program)
    (missing : librariesPresent domain directory program = false) :
    birthLibrariesPresent domain directory descriptor = false := by
  unfold birthLibrariesPresent
  rw [List.all_eq_false]
  exact ⟨item, member, by simp [holds, missing]⟩

/-- A friend may birth exactly an admissible program at its content address: one naming a
compiled-in evaluator, admitted by that evaluator (`Evaluator.RecordAdmissible`). -/
theorem program_user_initial_iff (deployment : Deployment) (cellId : Nat)
    (program : NockProgramCodec.Program) :
    UserInitial deployment cellId (programCell program) ↔
      deployment.Valid ∧ cellId = programCellId deployment.domain program ∧
        Evaluator.RecordAdmissible program ∧ cellId < Kernel.ProtectedCell.reservedBase := by
  simp [UserInitial, CellLaw, LogicalLaw, UserShape, programCell, PresentLaw,
    NockProgramCodec.CellValid, programCellId, and_assoc]

theorem nonCanonical_birth_refused (deployment : Deployment) (cellId : Nat)
    (program : NockProgramCodec.Program)
    (bad : Noun.canonical program.jam = false) :
    ¬ UserInitial deployment cellId (programCell program) := by
  rw [program_user_initial_iff]
  rintro ⟨_, _, admitted, _⟩
  unfold Evaluator.RecordAdmissible Evaluator.admitRecord at admitted
  cases hr : Evaluator.resolve [] program.evaluator with
  | error e => rw [hr] at admitted; cases e <;> simp [Evaluator.admitResolved, Except.toBool] at admitted
  | ok E =>
    obtain rfl := Evaluator.resolve_nock hr
    have refused : ∃ r, Evaluator.nock.admit program = .error r := by
      cases hcue : Noun.cue program.jam with
      | none => exact ⟨_, Machine.admit_noCue (M := Evaluator.nock.toMachine) hcue⟩
      | some n =>
        exact ⟨_, Machine.admit_nonCanonical (M := Evaluator.nock.toMachine)
          (show (Noun.cue program.jam).isSome = true by rw [hcue]; rfl) bad⟩
    obtain ⟨r, hr'⟩ := refused
    rw [hr] at admitted
    unfold Evaluator.admitResolved at admitted
    simp only [hr'] at admitted
    simp [Except.toBool] at admitted

theorem wrong_address_birth_refused (deployment : Deployment) (cellId : Nat)
    (program : NockProgramCodec.Program)
    (elsewhere : cellId ≠ programCellId deployment.domain program) :
    ¬ UserInitial deployment cellId (programCell program) := by
  rw [program_user_initial_iff]
  rintro ⟨_, same, _⟩
  exact elsewhere same

theorem program_occupied_refused (domain : Digest) (directory : Directory Nat registry)
    (program : NockProgramCodec.Program) (occupant : PackedCell registry)
    (occupied : directory.slots (programCreate domain program).cellId = .present occupant) :
    CellRegistry.create registry directory (programCreate domain program) =
      .error .duplicateCreate := by
  simp [CellRegistry.create, occupied]

/-! ## A birth names an evaluator this deployment runs (E3)

`Evaluator.RecordAdmissible` (the cell law) already refuses a record naming an id no
compiled-in evaluator has; the birth path checks it first, by name, and also refuses an
evaluator the operator disabled — a deployment parameter (`Profile.disabledEvaluators`,
committed in the runtime semantics digest), the same list a run resolves against. -/

/-- The evaluator ids of the program records a descriptor births. -/
def birthProgramEvaluators (descriptor : ResourceBirth.Descriptor registry) : List Digest :=
  descriptor.births.filterMap fun item => (cellProgram item.create.cell).map (·.evaluator)

/-- Each id resolves (`Evaluator.resolve`), in order; the first that does not names the
refusal. (`Except.bind`, not a `match`: a proof never has to compare two matchers over
`resolve`, whose whnf would compute the registry's cSHAKE ids.) -/
def resolveAll (disabled : List Digest) : List Digest → Except Evaluator.Unresolved Unit
  | [] => .ok ()
  | id :: rest => (Evaluator.resolve disabled id).bind fun _ => resolveAll disabled rest

theorem resolveAll_cons (disabled : List Digest) (id : Digest) (rest : List Digest) :
    resolveAll disabled (id :: rest) =
      (Evaluator.resolve disabled id).bind fun _ => resolveAll disabled rest := rfl

/-- **`birthEvaluators`**: every program record a birth carries names an evaluator this
deployment runs (compiled in, not disabled) — or the birth is refused by name. The run's
resolution (`Evaluator.resolve`), at birth. -/
def birthEvaluators (disabled : List Digest) (descriptor : ResourceBirth.Descriptor registry) :
    Except Evaluator.Unresolved Unit :=
  resolveAll disabled (birthProgramEvaluators descriptor)

theorem resolveAll_ok_iff (disabled : List Digest) : ∀ (ids : List Digest),
    resolveAll disabled ids = .ok () ↔ ∀ id ∈ ids, ∃ E, Evaluator.resolve disabled id = .ok E
  | [] => ⟨fun _ _ m => absurd m List.not_mem_nil, fun _ => rfl⟩
  | id :: rest => by
    rw [resolveAll_cons]
    cases h : Evaluator.resolve disabled id with
    | error e =>
      constructor
      · intro bad; cases bad
      · intro all
        obtain ⟨E, hE⟩ := all id (List.mem_cons_self ..)
        rw [h] at hE; cases hE
    | ok E =>
      show resolveAll disabled rest = .ok () ↔ _
      rw [resolveAll_ok_iff disabled rest]
      constructor
      · intro hr x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact ⟨E, h⟩
        · exact hr x hx
      · intro all x hx
        exact all x (List.mem_cons_of_mem _ hx)

/-- **`birthEvaluators_ok_iff`** (both poles): a birth passes exactly when each program it
carries names an evaluator that resolves. -/
theorem birthEvaluators_ok_iff (disabled : List Digest) (descriptor : ResourceBirth.Descriptor registry) :
    birthEvaluators disabled descriptor = .ok () ↔
      ∀ id ∈ birthProgramEvaluators descriptor, ∃ E, Evaluator.resolve disabled id = .ok E :=
  resolveAll_ok_iff disabled _

theorem birthEvaluators_single {disabled : List Digest} {descriptor : ResourceBirth.Descriptor registry}
    {id : Digest} (single : birthProgramEvaluators descriptor = [id]) :
    birthEvaluators disabled descriptor = (Evaluator.resolve disabled id).map fun _ => () := by
  unfold birthEvaluators
  rw [single, resolveAll_cons]
  cases Evaluator.resolve disabled id <;> rfl

/-- **`birth_unknownEvaluator_refused`** (E3): a birth whose program record names an id no
compiled-in evaluator has is refused `unknownEvaluator` — at birth, not at its first run. -/
theorem birth_unknownEvaluator_refused {disabled : List Digest}
    {descriptor : ResourceBirth.Descriptor registry} {id : Digest}
    (single : birthProgramEvaluators descriptor = [id])
    (absent : ∀ E ∈ Evaluator.registry, E.id ≠ id) :
    birthEvaluators disabled descriptor = .error .unknownEvaluator := by
  rw [birthEvaluators_single single, Evaluator.resolve_unknown absent]; rfl

/-- **`birth_evaluatorDisabled_refused`** (E3): in a deployment whose operator disabled Nock,
the birth of a Nock program is refused `evaluatorDisabled`. -/
theorem birth_evaluatorDisabled_refused {disabled : List Digest}
    {descriptor : ResourceBirth.Descriptor registry}
    (single : birthProgramEvaluators descriptor = [Evaluator.nock.id])
    (off : Evaluator.nock.id ∈ disabled) :
    birthEvaluators disabled descriptor = .error .evaluatorDisabled := by
  rw [birthEvaluators_single single, Evaluator.pole_evaluatorDisabled disabled off]; rfl

/-- The admitting pole: where Nock is enabled, a Nock program's birth passes this check. -/
theorem birth_nock_admitted {disabled : List Digest} {descriptor : ResourceBirth.Descriptor registry}
    (single : birthProgramEvaluators descriptor = [Evaluator.nock.id])
    (enabled : Evaluator.nock.id ∉ disabled) :
    birthEvaluators disabled descriptor = .ok () := by
  rw [birthEvaluators_single single, Evaluator.pole_nock_resolves disabled enabled]; rfl

theorem nock_program_final_state_immutable (deployment : Deployment) (cellId : Nat)
    (before after : PackedCell registry) (program : before.kind = .nockProgram)
    (valid : FinalPostLaw deployment cellId before after) : before = after := by
  have bytesExact : cellCodec.encode before = cellCodec.encode after :=
    valid.2.2.2.2 (Or.inr program)
  have same := congrArg cellCodec.decode bytesExact
  rw [cellCodec.decode_encode, cellCodec.decode_encode] at same
  exact Option.some.inj same

namespace Witness

def deployment : Deployment := ⟨⟨42⟩, 1, 2, 3⟩

/-- Account metadata with one field of its own identity, which it declares. -/
def payload : Materialized DeclaredEffectCell.materializer :=
  materialize DeclaredEffectCell.materializer
    (Kernel.FieldClosure.declare 10 (.closed [1])
      (StoreCodec.fromEntries [⟨(StateKey.objectField ⟨10⟩ ⟨1⟩).address, (17 : Int)⟩]))

/-- The same cell without its declaration holds an undeclared field: refused. -/
def undeclaredPayload : Materialized DeclaredEffectCell.materializer :=
  materialize DeclaredEffectCell.materializer
    (StoreCodec.fromEntries [⟨(StateKey.objectField ⟨10⟩ ⟨1⟩).address, (17 : Int)⟩])

/-- **A cell holding a field it does not declare is not lawful** (K-FIELD-CLOSURE): a
birth or a post holding it is refused by every receiver's cell law. -/
theorem undeclared_account_refused :
    ¬ UserInitial deployment 10 ⟨.accountMetadata, undeclaredPayload⟩ := by decide

def account : PackedCell registry := ⟨.accountMetadata, payload⟩

theorem user_account_inhabited : UserInitial deployment 10 account := by decide

theorem account_dispatch_inhabited :
    (selectDeclared deployment 10 .account account).isSome = true := by decide

theorem object_dispatch_refused : selectDeclared deployment 10 .object account = none :=
  object_cannot_select_account deployment 10 payload

/-- Neutral content genesis: the empty document cell. -/
def emptyContent : PackedCell registry :=
  ⟨.content, materialize HyperdocumentCell.contentMaterializer 0⟩

theorem user_content_inhabited : UserInitial deployment 11 emptyContent := by
  refine ⟨⟨⟨by decide, ?_⟩, ?_⟩, ?_⟩
  · intro left member
    exact ((DFinsupp.mem_support_toFun _ _).mp member rfl).elim
  · intro address member
    exact ((DFinsupp.mem_support_toFun _ _).mp member rfl).elim
  · unfold Kernel.ProtectedCell.reservedBase; decide

end Witness

#assert_axioms userInitial_not_activity_coordinate userInitial_not_seat_coordinate
end Minidregg.Compiler.CanonicalCellRegistry

/-- info: 'Minidregg.Compiler.CanonicalCellRegistry.registry_lifecycle_root' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Compiler.CanonicalCellRegistry.registry_lifecycle_root
/-- info: 'Minidregg.Compiler.CanonicalCellRegistry.decoded_cell_canonical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Compiler.CanonicalCellRegistry.decoded_cell_canonical
/-- info: 'Minidregg.Compiler.CanonicalCellRegistry.DeclaredCellLaw.no_balance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Compiler.CanonicalCellRegistry.DeclaredCellLaw.no_balance
/-- info: 'Minidregg.Compiler.CanonicalCellRegistry.Witness.undeclared_account_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Compiler.CanonicalCellRegistry.Witness.undeclared_account_refused
/-- info: 'Minidregg.Compiler.CanonicalCellRegistry.declared_fields_admit_as_before' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Compiler.CanonicalCellRegistry.declared_fields_admit_as_before
/-- info: 'Minidregg.Compiler.CanonicalCellRegistry.Witness.user_account_inhabited' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Compiler.CanonicalCellRegistry.Witness.user_account_inhabited
/-- info: 'Minidregg.Compiler.CanonicalCellRegistry.foreign_domain_event_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Compiler.CanonicalCellRegistry.foreign_domain_event_refused
/-- info: 'Minidregg.Compiler.CanonicalCellRegistry.empty_event_history_lawful' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Compiler.CanonicalCellRegistry.empty_event_history_lawful
/-- info: 'Minidregg.Compiler.CanonicalCellRegistry.authority_identity_is_pinned' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Compiler.CanonicalCellRegistry.authority_identity_is_pinned
/-- info: 'Minidregg.Compiler.CanonicalCellRegistry.Witness.user_content_inhabited' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Compiler.CanonicalCellRegistry.Witness.user_content_inhabited
/-- info: 'Minidregg.Compiler.CanonicalCellRegistry.program_user_initial_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Compiler.CanonicalCellRegistry.program_user_initial_iff
/-- info: 'Minidregg.Compiler.CanonicalCellRegistry.nonCanonical_birth_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Compiler.CanonicalCellRegistry.nonCanonical_birth_refused
/-- info: 'Minidregg.Compiler.CanonicalCellRegistry.missing_library_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Compiler.CanonicalCellRegistry.missing_library_refused
/-- info: 'Minidregg.Compiler.CanonicalCellRegistry.birth_missing_library_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Compiler.CanonicalCellRegistry.birth_missing_library_refused
/-- info: 'Minidregg.Compiler.CanonicalCellRegistry.loadProgram_present' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Compiler.CanonicalCellRegistry.loadProgram_present
/-- info: 'Minidregg.Compiler.CanonicalCellRegistry.program_occupied_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Compiler.CanonicalCellRegistry.program_occupied_refused
/-- info: 'Minidregg.Compiler.CanonicalCellRegistry.nock_program_final_state_immutable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Compiler.CanonicalCellRegistry.nock_program_final_state_immutable
/-- info: 'Minidregg.Compiler.CanonicalCellRegistry.birthEvaluators_ok_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Compiler.CanonicalCellRegistry.birthEvaluators_ok_iff
/-- info: 'Minidregg.Compiler.CanonicalCellRegistry.birth_unknownEvaluator_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Compiler.CanonicalCellRegistry.birth_unknownEvaluator_refused
/-- info: 'Minidregg.Compiler.CanonicalCellRegistry.birth_evaluatorDisabled_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Compiler.CanonicalCellRegistry.birth_evaluatorDisabled_refused
/-- info: 'Minidregg.Compiler.CanonicalCellRegistry.birth_nock_admitted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Compiler.CanonicalCellRegistry.birth_nock_admitted
