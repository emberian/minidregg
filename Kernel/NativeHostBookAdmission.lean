/-
Actual native loading refuses Books with balances for unregistered accounts.
The codec remains lossless on malformed Books; the source-owned cell law is
the gate. This module connects that gate to the native image loader rather
than proving only a free-standing predicate on a hand-picked balance.
-/
import Kernel.NativeHostContext
import Theory.CanonicalResourceBookInvariant

namespace Minidregg.Kernel.NativeHost

open Minidregg.Theory
open Minidregg.Theory.CellState
open Minidregg.Theory.CellRegistry
open Minidregg.Theory.CanonicalResourceKernel
open Minidregg.Theory.TypedAuthorization
open Minidregg.Compiler

set_option autoImplicit false

/-- Every listed live cell has passed the actual loaded-image cell-law loop.
The directory premise names the very canonical directory loaded by this call. -/
theorem validateLoaded_cellLaw (config : Config) (durable : Durable)
    (directory : CredentialAuthorityDomainReceiver.LoadedDirectory durable)
    (loadedDirectory : CredentialAuthorityDomainReceiver.loadDirectory durable = some directory)
    (identifier : Digest) (cell : PackedCell CanonicalCellRegistry.registry)
    (listed : identifier ∈ durable.image.cellIds)
    (present : directory.directory.slots identifier.value = .present cell)
    {opened : Opened config} (accepted : validateLoaded config durable = .ok opened) :
    CanonicalCellRegistry.CellLaw config.deployment identifier.value cell := by
  by_contra invalid
  cases deploymentValid : decide config.deployment.Valid <;>
    cases seedValid : (seedIdentity durable.image.seed == config.expectedSeed) <;>
    cases authorityLoaded : CredentialAuthorityDomainReceiver.loadDeployment
        config.deployment durable.snapshot <;>
    simp only [validateLoaded, check, need, deploymentValid, seedValid,
      loadedDirectory, authorityLoaded, bind, Except.bind,
      Bool.false_eq_true, ↓reduceIte] at accepted <;> try cases accepted
  split_ifs at accepted with cellLaws <;> try cases accepted
  all_goals
    have checked := (List.all_eq_true.mp cellLaws) identifier listed
    rw [present] at checked
    exact invalid ((CanonicalCellRegistry.cellCheck_iff _ _ _).mp checked)

/-- A malformed but canonically encoded Book cannot enter a successful native
loaded-image result, at any balance amount or hidden account/asset coordinate. -/
theorem validateLoaded_refuses_hidden_book (config : Config) (durable : Durable)
    (directory : CredentialAuthorityDomainReceiver.LoadedDirectory durable)
    (loadedDirectory : CredentialAuthorityDomainReceiver.loadDirectory durable = some directory)
    (identifier : Digest)
    (payload : Materialized CanonicalResourcePageMaterializer.materializer)
    (listed : identifier ∈ durable.image.cellIds)
    (present : directory.directory.slots identifier.value = .present ⟨.resourceBook, payload⟩)
    (account asset : Nat)
    (absent : account ∉ (logicalBook payload.logical).accounts)
    (hidden : (logicalBook payload.logical).balance account asset ≠ 0)
    (opened : Opened config) : validateLoaded config durable ≠ .ok opened := by
  intro accepted
  have law := validateLoaded_cellLaw config durable directory loadedDirectory identifier
    ⟨.resourceBook, payload⟩ listed present accepted
  exact hidden ((CanonicalCellRegistry.book_accountSupported _ _ _ law).balance_zero absent asset)

/-- Explicit counterexample data still roundtrips; the actual loading gate
rejects every canonical image containing that decoded Book. -/
theorem validateLoaded_refuses_witnessHiddenBook (config : Config) (durable : Durable)
    (directory : CredentialAuthorityDomainReceiver.LoadedDirectory durable)
    (loadedDirectory : CredentialAuthorityDomainReceiver.loadDirectory durable = some directory)
    (identifier : Digest) (listed : identifier ∈ durable.image.cellIds)
    (present : directory.directory.slots identifier.value = .present
      ⟨.resourceBook, materialize CanonicalResourcePageMaterializer.materializer
        (CanonicalResourcePageMaterializer.stateOfOption (some witnessHiddenBook))⟩)
    (opened : Opened config) : validateLoaded config durable ≠ .ok opened := by
  apply validateLoaded_refuses_hidden_book config durable directory loadedDirectory identifier
    _ listed present 9 0
  · change 9 ∉ witnessHiddenBook.accounts
    decide
  · change witnessHiddenBook.balance 9 0 ≠ 0
    decide

end Minidregg.Kernel.NativeHost
