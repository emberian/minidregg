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

Signatures after the re-type (bodies land after P5-READ-TARGET-LEG is on `next`;
P5 does not change these indices):

    structure PreparedInvocation (deployment) (profile) (ambient) (basis : Basis deployment store) (command)
    def prepareServed (deployment) (profile) (ambient) (native) (basis : Basis deployment store)
        (command) (authorityEnvelope) : IO (Except Reject (PreparedInvocation deployment profile ambient basis command))
    def invocationKeys (deployment) (profile) (command) : Keys     -- the command's tx id and marker nullifier
    -- a basis is usable for `command` only when it declares them: `basis.Declares (invocationKeys …)`
    ApplicationLifecycle*.admitServed … (basis : Basis deployment store) (ingress)
        : IO (Except String (Accepted deployment profile ambient basis ingress))

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

#assert_axioms Basis.view_lookup_declared
#assert_axioms Basis.view_consumed_declared

end Minidregg.Compiler.ServedBasis
