/-
# Compiler.ServedBasis — what a request is prepared against (KN2 stage 2b-1 CONTRACT)

THIS FILE PINS THE INDEX the write-path controllers are re-typed onto
(DeclaredResourceController / ResourceTransaction / ResourceInvocationSignatureFirst,
and the application-lifecycle cores and admissions over them). Today every
one of them is indexed by `durable : Durable` (the full verified
materialization, whole history). After the re-type each is indexed by
`basis : Basis deployment store`, with the SAME field and function names:

| today (over `durable : Durable`)                   | re-typed (over `basis : Basis deployment store`)      |
|----------------------------------------------------|-------------------------------------------------------|
| `durable.snapshot` (roots, bytes, available)        | `basis.view` (`Served.viewAt` of the footprint)        |
| `durable.snapshot.model.journal` / `lookupRecorded` | `basis.view`'s journal: DECLARED keys only (`basis.keys.transactions`) |
| `durable.snapshot.model.consumed`                   | `basis.view`'s consumed: DECLARED keys only (`basis.keys.nullifiers`) |
| `durable.image.accepted.findIdx?` / `[i]?` by tx id | `basis.byTx t` (a verified record at or below the height, or a verified absence) |
| `durable.height`                                    | `basis.height`                                         |
| `logicalHeight config durable`                      | `config.genesisHeight + basis.height`                  |
| `durable.worldRoot`                                 | `basis.worldRoot`                                      |
| `durable.logStart`                                  | `basis.logStart`                                       |
| `durable.image.seed`                                | `basis.seed`                                           |
| `LoadedDirectory durable`                           | `ServedDirectory basis.served` (`basis.directory`)     |
| `CredentialAuthorityDomainReceiver.Loaded deployment durable.snapshot` (`.snapshot`) | `basis.authority` (`ServedAuthority`) and `basis.authoritySnapshot` (clock = `basis.height`, spent markers from the footprint) |
| `ClockCellDomain.Loaded deployment durable.snapshot`, `RunComputeBudgetDomain.Prepared … durable.snapshot`, `ResourceMoneyReceiver.Prepared … durable.snapshot` | the same types at `basis.view` (they read cell state only) |

Controllers are indexed by `ground : Ground deployment` (below): `Ground.ofBasis basis`
on the light route, `Ground.ofLoaded` (`Opened.ground`) for the ratchet-listed
full-shape callers. In the table, read `basis.Y` as `ground.Y`; a `LoadedDirectory`'s
`.directory` is `ground.directory`, an authority load's `.snapshot` is
`ground.authority`, its `readGuards` / `writes` are `ground.authorityReadGuards` /
`ground.authorityWrites`. The re-typed declared-resource controller (COMPILED; the
names are unchanged, only the index moved from `durable` to `ground`):

    structure PreparedInvocation deployment profile ambient (ground : Ground deployment) command
      -- markerDeclared: the ground answers the operation marker's replay nullifier
    def DeclaredResourceController.prepare deployment profile ambient ground command
        : Except Reject (PreparedInvocation deployment profile ambient ground command)
    def DeclaredResourceController.prepareAuthenticated deployment profile ambient native ground
        command authorityEnvelope : IO (Except Reject (PreparedInvocation … ground command))
    def DeclaredResourceController.withAcceptedOn deployment profile ambient native ground signed
        acceptedResult ordinaryResult objective     -- opcode 2's admission (was withAcceptedLoadedFrom)
    def DeclaredResourceController.invocationKeys domain semantics command : Keys
        -- the command's transaction id and marker nullifier; a light basis declares at least these
    ResourceObservationAdmission.Context deployment := Ground deployment

Undeclared keys are refused by name, never read as absent: `Reject.undeclaredMarker`
(`prepare_undeclared`, `PreparedInvocation.markerSpent_false`), `Reject.undeclaredTransaction`
(`withAcceptedOn`); a prior transaction a core looks up is read with `ground.recorded t`
(`none` = undeclared; `recorded_light_some` / `recorded_light_none` /
`recorded_undeclared` / `recorded_full`). A PAST state (a claim core's original
BEGIN) is a second basis whose `served` is `Served.ofStateAt (← reader.stateAt h)` and
whose footprint is verified under the CURRENT head (`Basis.below : served.height ≤
head.height`); its records are `Record`s verified at use, so two such prefixes agree
record by record or exhibit a cSHAKE256 node collision (`DurableHistory.verifyAt_sound`).

Rules: a controller reads journal or consumed answers ONLY for keys its
request declares (`Basis.Declares`); `Basis.view_lookup_declared` /
`Basis.view_consumed_declared` say what those answers are. The full route of an
operation is deleted in the commit that ports it (no operation is dispatchable
both ways).
-/
import Compiler.CredentialAuthorityServed

namespace Minidregg.Compiler.ServedBasis

open Minidregg.Theory.TypedAuthorization
open Minidregg.Kernel.DurableDataIntent (DataSnapshot TransactionId StableNullifier CellId ReplayEnvelope)
open Minidregg.Kernel.DurableCommitProtocol (Intent Snapshot)
open Minidregg.Kernel.DurableReceiver (Seed)
open Minidregg.Kernel.DurableView (Keys)
open Minidregg.Compiler.DurableServed (Served)
open Minidregg.Compiler.DurableHistory (Head StoreIdentity)
open Minidregg.Compiler.DurableHistoryReader (VerifiedFootprint TxAnswer ByTx StateAt Reader)
open Minidregg.Compiler.CredentialAuthorityServed

set_option autoImplicit false

/-- A request's basis: a served state of the opened Store, its directory and
authority cell (as `validateServed` decoded them), the Store's authenticated
head, and the verified answers to the request's declared keys. -/
structure Basis (deployment : CanonicalCellRegistry.Deployment) (store : StoreIdentity) where
  served : State store
  directory : ServedDirectory served
  authority : ServedAuthority deployment served
  head : Head store
  /-- The served state is at or below the head the answers are verified under. -/
  below : served.height ≤ head.height
  keys : Keys
  footprint : VerifiedFootprint head keys

namespace Basis

variable {deployment : CanonicalCellRegistry.Deployment} {store : StoreIdentity}

/-- The snapshot a controller prepares against: the served state plus the
footprint's answers at the served height. -/
def view (basis : Basis deployment store) : DataSnapshot ResourceBirthCodec.rootBytes :=
  basis.served.viewAt basis.footprint

def height (basis : Basis deployment store) : Nat := basis.served.height
def worldRoot (basis : Basis deployment store) : Digest := basis.served.worldRoot
def logStart (basis : Basis deployment store) : Digest := basis.served.logStart
def seed (basis : Basis deployment store) : Seed := basis.served.seed

/-- The authority snapshot: the cell, the clock at the served height, the spent
markers from the footprint. -/
def authoritySnapshot (basis : Basis deployment store) : CredentialAuthorityDomain.Snapshot :=
  basis.authority.snapshotOn basis.footprint

/-- The basis declares every key of `wanted`. -/
def Declares (basis : Basis deployment store) (wanted : Keys) : Prop :=
  (∀ t ∈ wanted.transactions, t ∈ basis.keys.transactions) ∧
    ∀ n ∈ wanted.nullifiers, n ∈ basis.keys.nullifiers

instance (basis : Basis deployment store) (wanted : Keys) : Decidable (basis.Declares wanted) := by
  unfold Declares; infer_instance

/-- A transaction id's verified answer in the footprint (the first one), if declared. -/
def byTx (basis : Basis deployment store) (transactionId : TransactionId) :
    Option (TxAnswer basis.head transactionId) :=
  (basis.footprint.transactions.find? (·.1 = transactionId)).bind fun answer =>
    if same : answer.1 = transactionId then some (same ▸ answer.2) else none

@[simp] theorem view_roots (basis : Basis deployment store) :
    basis.view.model.roots = basis.served.roots := rfl
@[simp] theorem view_canonicalBytes (basis : Basis deployment store) :
    basis.view.canonicalBytes = basis.served.canonicalBytes := rfl

/-- **A journal answer of a basis is a record verified at use, accepted at or
below the served height** (`Served.recordedAt_some`). -/
theorem view_lookup_declared (basis : Basis deployment store) (transactionId : TransactionId)
    {intent : Intent TransactionId CellId StableNullifier ReplayEnvelope}
    (hit : Snapshot.lookupRecorded transactionId basis.view.model.journal = some intent) :
    ∃ found : ByTx basis.head transactionId, found.height ≤ basis.height ∧
      intent = Kernel.DurableCheckpoint.IntentRecord.erase found.read.record :=
  Served.recordedAt_some basis.footprint basis.served.height transactionId hit

/-- **A consumed bit of a basis is the index's verified answer at the
served height** (`Served.spentAt_true`). -/
theorem view_consumed_declared (basis : Basis deployment store) (nullifier : StableNullifier)
    (consumed : basis.view.model.consumed nullifier = true) :
    ∃ answer ∈ basis.footprint.nullifiers, answer.1 = nullifier ∧
      ∃ inserted, answer.2.value = some inserted ∧ inserted ≤ basis.height :=
  Served.spentAt_true basis.footprint basis.served.height nullifier consumed

/-- The authority clock of a basis is its height. -/
theorem authoritySnapshot_revision (basis : Basis deployment store) :
    basis.authoritySnapshot.revision = basis.height := rfl

end Basis

/-! ## Ground: what a controller prepares against, from either shape

A write-path controller is indexed by a `Ground`: the snapshot it reads (its
state, and journal/consumed answers), the authority clock, the decoded directory
and the authority cell. It is one of two verified shapes (its only constructors):
`Ground.ofBasis` (the light route: the served state plus the request's verified
footprint) and `Ground.ofLoaded` (the full verified materialization, for the
ratchet-listed callers such as the audit walk). On the light route the journal
and consumed answers exist only for the request's declared keys
(`Basis.view_lookup_declared`), so a controller's port declares every key it
reads (`DurableView.Family.covers`). -/

/-- A ground is one of the two verified shapes, as built: there is no other
constructor and no field to forge (each constructor's arguments are themselves
authenticated types: a `Basis` holds a MAC-bound `Head` and a `VerifiedFootprint`;
the full shape's directory and authority are private-constructed loads). -/
inductive Ground (deployment : CanonicalCellRegistry.Deployment) where
  | light {store : StoreIdentity} (basis : Basis deployment store)
  | full (durable : DurableReceiverIO.Loaded ResourceBirthCodec.rootBytes)
      (directory : CredentialAuthorityDomainReceiver.LoadedDirectory durable)
      (authority : CredentialAuthorityDomainReceiver.Loaded deployment durable.snapshot)

namespace Ground

open CredentialAuthorityDomainReceiver (cellIdOf cellBytes cellRoot)

variable {deployment : CanonicalCellRegistry.Deployment}

abbrev ofBasis {store : StoreIdentity} (basis : Basis deployment store) : Ground deployment := .light basis

/-- The full shape's ground (ratchet-listed callers). -/
abbrev ofLoaded (durable : DurableReceiverIO.Loaded ResourceBirthCodec.rootBytes)
    (directory : CredentialAuthorityDomainReceiver.LoadedDirectory durable)
    (authority : CredentialAuthorityDomainReceiver.Loaded deployment durable.snapshot) : Ground deployment :=
  .full durable directory authority

/-- The snapshot a controller reads: the basis's view, or the full snapshot. -/
def view : Ground deployment → DataSnapshot ResourceBirthCodec.rootBytes
  | .light basis => basis.view
  | .full durable _ _ => durable.snapshot

/-- The cell state a preparation reads: the view with its history removed (roots,
bytes, allowance; no journal, nothing consumed). The light shape's view differs
from the full snapshot only in the journal and consumed answers, which reach a
controller solely through declared keys (`recorded`, `markerSpent`,
`declaresNullifier`); its cells are the full shape's cells on the same state
(`cells_ofLoaded`). -/
def cells (ground : Ground deployment) : DataSnapshot ResourceBirthCodec.rootBytes :=
  Minidregg.Compiler.DurableServed.bare ground.view

@[simp] theorem cells_roots (ground : Ground deployment) :
    ground.cells.model.roots = ground.view.model.roots := rfl
@[simp] theorem cells_canonicalBytes (ground : Ground deployment) :
    ground.cells.canonicalBytes = ground.view.canonicalBytes := rfl
@[simp] theorem cells_available (ground : Ground deployment) :
    ground.cells.model.available = ground.view.model.available := rfl

/-- The authority clock: the durable height. -/
def height : Ground deployment → Nat
  | .light basis => basis.height
  | .full durable _ _ => durable.height

def worldRoot : Ground deployment → Digest
  | .light basis => basis.worldRoot
  | .full durable _ _ => durable.worldRoot

def logStart : Ground deployment → Digest
  | .light basis => basis.logStart
  | .full durable _ _ => durable.logStart

def seed : Ground deployment → Seed
  | .light basis => basis.seed
  | .full durable _ _ => durable.image.seed

/-- The accepted image a ground was materialized from: the full shape's own image;
a light ground holds no history, so it has none (a check that names the source
image — a joint promise — is admissible only on the full shape). -/
def sourceImage : Ground deployment → Option Minidregg.Kernel.DurableReceiver.Image
  | .light _ => none
  | .full durable _ _ => some durable.image

def directory : Ground deployment → Minidregg.Theory.CellRegistry.Directory Nat CanonicalCellRegistry.registry
  | .light basis => basis.directory.directory
  | .full _ directory _ => directory.directory

def authority : Ground deployment → CredentialAuthorityDomain.Snapshot
  | .light basis => basis.authoritySnapshot
  | .full _ _ authority => authority.snapshot

theorem bytes_exact (ground : Ground deployment) (identifier : Nat) :
    ResourceBirthCodec.LifecycleImage.bytes CanonicalCellRegistry.registry
        (ResourceBirthCodec.LifecycleImage.view CanonicalCellRegistry.registry ground.directory identifier) =
      ground.view.canonicalBytes ⟨identifier⟩ := by
  cases ground with
  | light basis => exact basis.directory.bytes_exact identifier
  | full durable directory _ => exact directory.bytes_exact identifier

/-- **A live cell of the ground's directory has its physical root in the
ground's state** (the CAS read guard of an event-only read). -/
theorem physicalCurrent (ground : Ground deployment) (target : Nat)
    (packed : Minidregg.Theory.CellRegistry.PackedCell CanonicalCellRegistry.registry)
    (present : ground.directory.slots target = .present packed) :
    ResourceBirthCodec.physicalRoot (.live packed) = ground.view.model.roots ⟨target⟩ := by
  have lifecycle : ResourceBirthCodec.LifecycleImage.view
      CanonicalCellRegistry.registry ground.directory target = .live packed :=
    (ResourceBirthCodec.LifecycleImage.view_live_iff
      CanonicalCellRegistry.registry ground.directory target packed).mpr present
  calc
    ResourceBirthCodec.physicalRoot (.live packed) =
        ResourceBirthCodec.rootBytes
          (ResourceBirthCodec.LifecycleImage.bytes CanonicalCellRegistry.registry
            (ResourceBirthCodec.LifecycleImage.view CanonicalCellRegistry.registry
              ground.directory target)) := by rw [lifecycle]; rfl
    _ = ResourceBirthCodec.rootBytes (ground.view.canonicalBytes ⟨target⟩) :=
      congrArg ResourceBirthCodec.rootBytes (ground.bytes_exact target)
    _ = ground.view.model.roots ⟨target⟩ := ground.view.coherent _

theorem valid (ground : Ground deployment) : deployment.Valid := by
  cases ground with
  | light basis => exact basis.authority.valid
  | full _ _ authority => exact authority.valid

theorem authorityDomain (ground : Ground deployment) : ground.authority.domain = deployment.domain := by
  cases ground with
  | light basis => rfl
  | full _ _ authority => exact authority.domainExact

/-- **The authority clock is the height** on both shapes (the full shape's clock,
its history length, is its height: `Served.history_length_eq_height`). -/
theorem authorityRevision (ground : Ground deployment) : ground.authority.revision = ground.height := by
  cases ground with
  | light basis => rfl
  | full durable _ authority => exact authority.revisionExact.trans (Served.history_length_eq_height durable)

theorem authoritySpent (ground : Ground deployment) :
    ground.authority.spent = CredentialAuthorityDomainReceiver.spentOf deployment.domain ground.view := by
  cases ground with
  | light basis => rfl
  | full _ _ authority => exact authority.spentExact

theorem authorityObserved (ground : Ground deployment) :
    ground.view.canonicalBytes (cellIdOf deployment) = cellBytes ground.authority.cell := by
  cases ground with
  | light basis => exact basis.authority.observed
  | full _ _ authority => exact authority.observed

/-- Whether this ground answers a nullifier: on the light route only a declared
one (`Basis.keys`); the full shape answers every one. -/
def declaresNullifier : Ground deployment → Minidregg.Kernel.DurableDataIntent.StableNullifier → Bool
  | .light basis, nullifier => decide (nullifier ∈ basis.keys.nullifiers)
  | .full .., _ => true

/-- Whether this ground answers a transaction id's journal lookup: on the light
route only a declared one; the full shape answers every one. -/
def declaresTransaction : Ground deployment → Minidregg.Kernel.DurableDataIntent.TransactionId → Bool
  | .light basis, transactionId => decide (transactionId ∈ basis.keys.transactions)
  | .full .., _ => true

/-- **A declared transaction's journal answer is the verified history's**: on the
light route a record the view answers was verified at use and accepted at or below
the served height (`Basis.view_lookup_declared`). -/
theorem declaresTransaction_full (durable : DurableReceiverIO.Loaded ResourceBirthCodec.rootBytes)
    (directory : CredentialAuthorityDomainReceiver.LoadedDirectory durable)
    (authority : CredentialAuthorityDomainReceiver.Loaded deployment durable.snapshot)
    (transactionId : Minidregg.Kernel.DurableDataIntent.TransactionId) :
    (Ground.ofLoaded durable directory authority).declaresTransaction transactionId = true := rfl

theorem declaresTransaction_undeclared {store : StoreIdentity} (basis : Basis deployment store)
    (transactionId : Minidregg.Kernel.DurableDataIntent.TransactionId)
    (undeclared : transactionId ∉ basis.keys.transactions) :
    (Ground.ofBasis basis).declaresTransaction transactionId = false := by
  simp [declaresTransaction, undeclared]

/-- A transaction's recorded intent, where this ground answers it: `some r` with
`r` the journal's answer for a declared transaction id; `none` for an undeclared
one — a consumer refuses that by name, never reads it as "not recorded". -/
def recorded (ground : Ground deployment) (transactionId : TransactionId) :
    Option (Option (Intent TransactionId CellId StableNullifier ReplayEnvelope)) :=
  if ground.declaresTransaction transactionId then
    some (Snapshot.lookupRecorded transactionId ground.view.model.journal)
  else none

/-- **An undeclared transaction gets no answer** (refuting pole of a silent
"not recorded"). -/
theorem recorded_undeclared {store : StoreIdentity} (basis : Basis deployment store)
    (transactionId : TransactionId) (undeclared : transactionId ∉ basis.keys.transactions) :
    (Ground.ofBasis basis).recorded transactionId = none := by
  simp [recorded, declaresTransaction, undeclared]

/-- **A light answer that names a record is a record verified at use**, accepted at
or below the served height (`Basis.view_lookup_declared`). -/
theorem recorded_light_some {store : StoreIdentity} (basis : Basis deployment store)
    (transactionId : TransactionId) {intent : Intent TransactionId CellId StableNullifier ReplayEnvelope}
    (answered : (Ground.ofBasis basis).recorded transactionId = some (some intent)) :
    ∃ found : ByTx basis.head transactionId, found.height ≤ basis.height ∧
      intent = Kernel.DurableCheckpoint.IntentRecord.erase found.read.record := by
  unfold recorded at answered
  split at answered
  · exact basis.view_lookup_declared transactionId (Option.some.inj answered)
  · cases answered

/-- **A light answer of "not recorded" is a verified absence at the served
height**: the index opens the transaction id as absent, or the transaction
was accepted above the served height (`Served.recordedAt_none`). -/
theorem recorded_light_none {store : StoreIdentity} (basis : Basis deployment store)
    (transactionId : TransactionId)
    (answered : (Ground.ofBasis basis).recorded transactionId = some none) :
    ∃ answer ∈ basis.footprint.transactions, answer.1 = transactionId ∧
      ((∃ opens : DurableIndex.Opens basis.head.indexRoot (DurableIndex.transactionKey answer.1) none,
          answer.2 = .absent opens) ∨
        ∃ found : ByTx basis.head answer.1, answer.2 = .present found ∧ basis.height < found.height) := by
  unfold recorded at answered
  split at answered
  · rename_i declared
    have member : transactionId ∈ basis.keys.transactions := by
      simpa [declaresTransaction] using declared
    rw [← basis.footprint.transactionsExact] at member
    obtain ⟨answer, inList, same⟩ := List.mem_map.mp member
    exact ⟨answer, inList, same, Served.recordedAt_none basis.footprint basis.served.height transactionId
      (Option.some.inj answered) answer inList same⟩
  · cases answered

/-- The full shape answers every transaction id with its journal's answer. -/
theorem recorded_full (durable : DurableReceiverIO.Loaded ResourceBirthCodec.rootBytes)
    (directory : CredentialAuthorityDomainReceiver.LoadedDirectory durable)
    (authority : CredentialAuthorityDomainReceiver.Loaded deployment durable.snapshot)
    (transactionId : TransactionId) :
    (Ground.ofLoaded durable directory authority).recorded transactionId =
      some (Snapshot.lookupRecorded transactionId durable.snapshot.model.journal) := rfl

/-- A receiver's replay verdict for its transaction id on a ground: the ground
does not answer the id (`undeclared`: the light basis did not declare it — refused
by name, never read as "not recorded"), the id is not recorded (`fresh`), the
recorded intent is exactly this ingress's (`original`), or another intent holds
the id (`conflict`). -/
inductive Replay (R : Type) where
  | undeclared
  | fresh
  | original (receipt : R)
  | conflict

/-- The replay verdict through `recorded`: the one journal read a receiver makes. -/
def replayOf {R : Type} (ground : Ground deployment) (transactionId : TransactionId)
    (exact : Intent TransactionId CellId StableNullifier ReplayEnvelope → Bool) (receipt : R) : Replay R :=
  match ground.recorded transactionId with
  | none => .undeclared
  | some none => .fresh
  | some (some recorded) => if exact recorded then .original receipt else .conflict

/-- **An undeclared transaction id is refused by name**: on a light basis that did
not declare it, the verdict is `undeclared`, never `fresh`. -/
theorem replayOf_undeclared {R : Type} {store : StoreIdentity} (basis : Basis deployment store)
    (transactionId : TransactionId)
    (exact : Intent TransactionId CellId StableNullifier ReplayEnvelope → Bool) (receipt : R)
    (undeclared : transactionId ∉ basis.keys.transactions) :
    (Ground.ofBasis basis).replayOf transactionId exact receipt = .undeclared := by
  simp [replayOf, recorded_undeclared basis transactionId undeclared]

/-- **An original verdict names a recorded intent**: the ground's journal holds an
intent under the id and it is exact. -/
theorem replayOf_original {R : Type} (ground : Ground deployment) (transactionId : TransactionId)
    (exact : Intent TransactionId CellId StableNullifier ReplayEnvelope → Bool) (receipt result : R)
    (original : ground.replayOf transactionId exact receipt = .original result) :
    result = receipt ∧ ∃ recorded,
      Snapshot.lookupRecorded transactionId ground.view.model.journal = some recorded ∧
        exact recorded = true := by
  unfold replayOf at original
  split at original
  · cases original
  · cases original
  · rename_i recorded found
    split at original
    · rename_i isExact
      cases original
      refine ⟨rfl, recorded, ?_, isExact⟩
      unfold Ground.recorded at found
      split at found
      · exact Option.some.inj found
      · cases found
    · cases original

/-- **The verdict depends only on the ground's answer for the id**: two grounds
that answer the transaction id alike (on the light route, the verified journal
answer of a declared id, `recorded_light_some` / `recorded_light_none`) reach the
same verdict. -/
theorem replayOf_agrees {R : Type} (first second : Ground deployment) (transactionId : TransactionId)
    (exact : Intent TransactionId CellId StableNullifier ReplayEnvelope → Bool) (receipt : R)
    (answers : first.recorded transactionId = second.recorded transactionId) :
    first.replayOf transactionId exact receipt = second.replayOf transactionId exact receipt := by
  unfold replayOf
  rw [answers]

/-- **A different intent under the id is a conflict**: when the ground's journal
answer for the id is an intent this ingress does not reproduce exactly, the
verdict is `conflict` (never `fresh`, never `original`). -/
theorem replayOf_conflict {R : Type} (ground : Ground deployment) (transactionId : TransactionId)
    (exact : Intent TransactionId CellId StableNullifier ReplayEnvelope → Bool) (receipt : R)
    {recorded : Intent TransactionId CellId StableNullifier ReplayEnvelope}
    (found : ground.recorded transactionId = some (some recorded)) (differs : exact recorded = false) :
    ground.replayOf transactionId exact receipt = .conflict := by
  simp [replayOf, found, differs]

#assert_axioms replayOf_conflict
#assert_axioms replayOf_undeclared
#assert_axioms replayOf_original
#assert_axioms replayOf_agrees

/-- An authority operation marker's spent bit, where this ground answers it;
`none` for a marker whose replay nullifier the request did not declare — a
controller refuses it by name, never reads it as unspent. -/
def markerSpent (ground : Ground deployment) (marker : Nat) : Option Bool :=
  if ground.declaresNullifier (CredentialAuthorityReplay.nullifier deployment.domain marker) then
    some (ground.authority.spent marker)
  else none

/-- **A marker answer is the authority's spent bit**, and on the light route the
index's verified answer at the served height (`Basis.view_consumed_declared`). -/
theorem markerSpent_some (ground : Ground deployment) {marker : Nat} {spent : Bool}
    (answered : ground.markerSpent marker = some spent) : spent = ground.authority.spent marker := by
  unfold markerSpent at answered
  split at answered
  · exact (Option.some.inj answered).symm
  · cases answered

/-- **An undeclared marker gets no answer** (refuting pole of a silent "unspent"). -/
theorem markerSpent_undeclared {store : StoreIdentity} (basis : Basis deployment store) (marker : Nat)
    (undeclared : CredentialAuthorityReplay.nullifier deployment.domain marker ∉ basis.keys.nullifiers) :
    (Ground.ofBasis basis).markerSpent marker = none := by
  simp [markerSpent, declaresNullifier, undeclared]

/-- The full shape answers every marker with its spent bit. -/
theorem markerSpent_full (durable : DurableReceiverIO.Loaded ResourceBirthCodec.rootBytes)
    (directory : CredentialAuthorityDomainReceiver.LoadedDirectory durable)
    (authority : CredentialAuthorityDomainReceiver.Loaded deployment durable.snapshot) (marker : Nat) :
    (Ground.ofLoaded durable directory authority).markerSpent marker = some (authority.snapshot.spent marker) := by
  simp [markerSpent, declaresNullifier, Ground.authority]

/-- The one authority write: the post cell at the authority cell, guarded at
its root in this ground. -/
def authorityWrite (ground : Ground deployment) (post : CredentialAuthorityDomain.Cell) :
    Minidregg.Kernel.DurableDataIntent.DataWrite where
  cellId := cellIdOf deployment
  expectedPre := ground.view.model.roots (cellIdOf deployment)
  exactPost := cellRoot post
  canonicalPostBytes := cellBytes post

def authorityWrites (ground : Ground deployment) (post : CredentialAuthorityDomain.Cell) :
    List Minidregg.Kernel.DurableDataIntent.DataWrite := [ground.authorityWrite post]

def authorityReadGuard (ground : Ground deployment) : Minidregg.Kernel.DurableDataIntent.ReadGuard :=
  { cellId := cellIdOf deployment, expectedRoot := ground.view.model.roots (cellIdOf deployment) }

def authorityReadGuards (ground : Ground deployment) : List Minidregg.Kernel.DurableDataIntent.ReadGuard :=
  [ground.authorityReadGuard]

theorem authorityWrite_root_bound (ground : Ground deployment) (post : CredentialAuthorityDomain.Cell) :
    ResourceBirthCodec.rootBytes (ground.authorityWrite post).canonicalPostBytes =
      (ground.authorityWrite post).exactPost := rfl

/-- The authority write's guard is the authority cell's own root. -/
theorem authorityWrite_pre_is_root (ground : Ground deployment) (post : CredentialAuthorityDomain.Cell) :
    (ground.authorityWrite post).expectedPre = cellRoot ground.authority.cell := by
  show ground.view.model.roots _ = ResourceBirthCodec.rootBytes (cellBytes _)
  rw [← ground.authorityObserved]
  exact (ground.view.coherent _).symm

theorem authorityReadGuards_exact (ground : Ground deployment) (guard : Minidregg.Kernel.DurableDataIntent.ReadGuard)
    (member : guard ∈ ground.authorityReadGuards) :
    guard.expectedRoot = ground.view.model.roots guard.cellId := by
  simp only [authorityReadGuards, List.mem_singleton] at member
  subst guard
  rfl

/-- **The light and full shapes prepare on the same cells.** A basis whose served
state is the full materialization's state has the full shape's cell state. -/
theorem cells_ofLoaded {store : StoreIdentity} (basis : Basis deployment store)
    (loaded : DurableReceiverIO.Loaded ResourceBirthCodec.rootBytes)
    (sameStart : store.logStart = loaded.logStart)
    (served : basis.served = Served.ofLoaded loaded sameStart)
    (directory : CredentialAuthorityDomainReceiver.LoadedDirectory loaded)
    (authority : CredentialAuthorityDomainReceiver.Loaded deployment loaded.snapshot) :
    (ofBasis basis).cells = (Ground.full loaded directory authority).cells := by
  simp only [cells, view, Basis.view, served]
  rfl

#assert_axioms cells_ofLoaded

end Ground

/-- **A ground at a head.** The light shape is at the head its basis's answers are
verified under (its served height is at or below the head's). The full shape is a state
of the head's history at the ground's own height: at the head (`full`: its height and
chain are the head's), or at a past height (`fullPast`: its chain is that of the
verified `StateAt` the head's Reader gives at that height; the audit walk's openings). A caller that holds a history `Reader` at head `h` takes its
ground as `Grounded deployment h`, so a ground prepared under another head
cannot be paired with that Reader (no inhabitant of `At`). -/
inductive Ground.At {deployment : CanonicalCellRegistry.Deployment} {store : StoreIdentity} :
    Ground deployment → Head store → Prop
  | light (basis : Basis deployment store) : Ground.At (.light basis) basis.head
  | full (durable : DurableReceiverIO.Loaded ResourceBirthCodec.rootBytes)
      (directory : CredentialAuthorityDomainReceiver.LoadedDirectory durable)
      (authority : CredentialAuthorityDomainReceiver.Loaded deployment durable.snapshot)
      (head : Head store) (sameStart : durable.logStart = store.logStart)
      (height : durable.height = head.height) (chain : durable.chain = head.chain) :
      Ground.At (.full durable directory authority) head
  /-- The full shape at a PAST height of the Store: its chain is the chain of the
  head's verified history after its own `durable.height` records (a `StateAt` read
  from the Store under this head), the same Store start. The audit walk's
  intermediate openings are grounds of this shape. -/
  | fullPast (durable : DurableReceiverIO.Loaded ResourceBirthCodec.rootBytes)
      (directory : CredentialAuthorityDomainReceiver.LoadedDirectory durable)
      (authority : CredentialAuthorityDomainReceiver.Loaded deployment durable.snapshot)
      (head : Head store) (sameStart : durable.logStart = store.logStart)
      (seed : Seed) (state : StateAt ResourceBirthCodec.rootBytes seed head durable.height)
      (chain : durable.chain = (Served.ofStateAt state).chain) :
      Ground.At (.full durable directory authority) head

/-- A ground bound to the head a history `Reader` is indexed by. -/
structure Grounded (deployment : CanonicalCellRegistry.Deployment) {store : StoreIdentity}
    (head : Head store) where
  ground : Ground deployment
  atHead : ground.At head

namespace Grounded

variable {deployment : CanonicalCellRegistry.Deployment} {store : StoreIdentity}

instance {head : Head store} : CoeOut (Grounded deployment head) (Ground deployment) := ⟨Grounded.ground⟩

/-- The light ground of a basis, at its own head. -/
def ofBasis (basis : Basis deployment store) : Grounded deployment basis.head :=
  ⟨.light basis, .light basis⟩

/-- The full shape at `head`, checked: the same Store, height and chain, or refused by name. -/
def ofLoaded (head : Head store) (durable : DurableReceiverIO.Loaded ResourceBirthCodec.rootBytes)
    (directory : CredentialAuthorityDomainReceiver.LoadedDirectory durable)
    (authority : CredentialAuthorityDomainReceiver.Loaded deployment durable.snapshot) :
    Except String (Grounded deployment head) :=
  if sameStart : durable.logStart = store.logStart then
    if height : durable.height = head.height then
      if chain : durable.chain = head.chain then
        .ok ⟨.full durable directory authority, .full durable directory authority head sameStart height chain⟩
      else .error s!"the opened Store's chain is not the history head's at height {head.height}"
    else .error s!"the opened Store is at height {durable.height}, the history head at {head.height}"
  else .error "the opened Store is not the history head's Store"

/-- **The check behind a full ground at a past height.** A state claimed to be the
Store's after `height` records (its log start, its chain) is one of the head's
verified history: the same Store start, and the chain equals the chain of
`Reader.stateAt height` (checkpoint plus verified records), or it is refused by name.
Pure of any deployment, so a probe Store can plant it. -/
def pastWitness {store : StoreIdentity} (reader : Reader ResourceBirthCodec.rootBytes store)
    (logStart : Digest) (height : Nat) (chain : Digest) :
    IO (Except String ((state : StateAt ResourceBirthCodec.rootBytes reader.seed reader.head height) ×'
      (logStart = store.logStart ∧ chain = (Served.ofStateAt state).chain))) := do
  if sameStart : logStart = store.logStart then
    match ← reader.stateAt height with
    | .error refusal => return .error refusal.message
    | .ok state =>
        if same : chain = (Served.ofStateAt state).chain then
          return .ok ⟨state, sameStart, same⟩
        else return .error s!"the opened state's chain is not the history's at height {height}"
  else return .error "the opened Store is not the history head's Store"

/-- The full shape at the height it holds, checked against the Store's history
(`pastWitness`): a ground of the head's history at its own height. -/
def ofLoadedAt {store : StoreIdentity} (reader : Reader ResourceBirthCodec.rootBytes store)
    (durable : DurableReceiverIO.Loaded ResourceBirthCodec.rootBytes)
    (directory : CredentialAuthorityDomainReceiver.LoadedDirectory durable)
    (authority : CredentialAuthorityDomainReceiver.Loaded deployment durable.snapshot) :
    IO (Except String (PLift (Ground.At (.full durable directory authority) reader.head))) := do
  match ← pastWitness reader durable.logStart durable.height durable.chain with
  | .error detail => return .error detail
  | .ok ⟨state, sameStart, chain⟩ =>
      return .ok ⟨.fullPast durable directory authority reader.head sameStart reader.seed state chain⟩

/-- A grounded light basis's head is the head it is indexed by. -/
theorem light_head {head : Head store} (grounded : Grounded deployment head)
    {basis : Basis deployment store} (light : grounded.ground = .light basis) : basis.head = head := by
  have at' := grounded.atHead
  rw [light] at at'
  cases at'
  rfl

#assert_axioms light_head

end Grounded

#assert_axioms Basis.view_lookup_declared
#assert_axioms Basis.view_consumed_declared
#assert_axioms Ground.authorityWrite_pre_is_root
#assert_axioms Ground.markerSpent_some
#assert_axioms Ground.markerSpent_undeclared
#assert_axioms Ground.markerSpent_full

end Minidregg.Compiler.ServedBasis
