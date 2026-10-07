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
open Minidregg.Compiler.DurableHistoryReader (VerifiedFootprint TxAnswer ByTx)
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

/-- **A consumed bit of a basis is the spent map's verified answer at the
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
height**: the spent map opens the transaction id as absent, or the transaction
was accepted above the served height (`Served.recordedAt_none`). -/
theorem recorded_light_none {store : StoreIdentity} (basis : Basis deployment store)
    (transactionId : TransactionId)
    (answered : (Ground.ofBasis basis).recorded transactionId = some none) :
    ∃ answer ∈ basis.footprint.transactions, answer.1 = transactionId ∧
      ((∃ opens : DurableSpent.Opens basis.head.spentRoot (DurableSpent.transactionKey answer.1) none,
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

/-- An authority operation marker's spent bit, where this ground answers it;
`none` for a marker whose replay nullifier the request did not declare — a
controller refuses it by name, never reads it as unspent. -/
def markerSpent (ground : Ground deployment) (marker : Nat) : Option Bool :=
  if ground.declaresNullifier (CredentialAuthorityReplay.nullifier deployment.domain marker) then
    some (ground.authority.spent marker)
  else none

/-- **A marker answer is the authority's spent bit**, and on the light route the
spent map's verified answer at the served height (`Basis.view_consumed_declared`). -/
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

end Ground

#assert_axioms Basis.view_lookup_declared
#assert_axioms Basis.view_consumed_declared
#assert_axioms Ground.authorityWrite_pre_is_root
#assert_axioms Ground.markerSpent_some
#assert_axioms Ground.markerSpent_undeclared
#assert_axioms Ground.markerSpent_full

end Minidregg.Compiler.ServedBasis
