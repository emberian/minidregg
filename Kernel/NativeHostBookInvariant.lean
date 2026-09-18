/-
The source-owned native genesis and actual resource patches preserve account
support. Registration sees public account names only once the loaded Book law
has established support. Pure Book codecs retain arbitrary data; malformed
support is refused by the receiving cell law.
-/
import Kernel.NativeHostGenesis
import Theory.CanonicalResourceBookInvariant

namespace Minidregg.Kernel.NativeHostGenesis

open Minidregg.Theory
open Minidregg.Theory.CanonicalResourceKernel

set_option autoImplicit false

theorem fund_accountSupported (asset : Nat) (book : Book) (enrollments : List Enrollment)
    (supported : book.AccountSupported)
    (issuerPresent : asset ∈ book.accounts)
    (recipientsPresent : ∀ enrollment ∈ enrollments, enrollment.accountId ∈ book.accounts) :
    (fund asset book enrollments).AccountSupported := by
  induction enrollments generalizing book with
  | nil => exact supported
  | cons enrollment rest ih =>
    exact ih _
      (book.applyPosting_accountSupported
        ⟨asset, enrollment.accountId, asset, enrollment.initialBalance⟩ supported
        issuerPresent (recipientsPresent enrollment (List.mem_cons_self)))
      issuerPresent (fun selected member =>
        recipientsPresent selected (List.mem_cons_of_mem _ member))

/-- No configuration can bootstrap hidden balances through source funding.
This is independent of balance amounts, enrollment count, or policy contents. -/
theorem initialBook_accountSupported (config : Config) : config.initialBook.AccountSupported := by
  apply fund_accountSupported
  · exact Book.zero_accountSupported _ _
  · simp [Config.accounts]
  · intro enrollment member
    simp only [Config.accounts, List.mem_toFinset, List.mem_append]
    exact Or.inl (List.mem_map.mpr ⟨enrollment, member, rfl⟩)

end Minidregg.Kernel.NativeHostGenesis

namespace Minidregg.Kernel.ResourceBirthController.Concrete

open Minidregg.Theory
open Minidregg.Theory.CanonicalResourceKernel
open Minidregg.Theory.ResourceBirth
open Minidregg.Compiler
open Minidregg.Compiler.CanonicalPolicyAdmission

set_option autoImplicit false

variable {F : Type} [Field F] {profile : PolicyCompilerProfile F}

/-- The actual receiving preparation carries support from its loaded Book. -/
theorem PreparedBirth.book_accountSupported {deployment : Deployment} {pins : FactoryPins}
    {durable : Durable} {descriptor : Descriptor Registry}
    (prepared : PreparedBirth profile deployment pins durable descriptor) :
    (logicalBook prepared.book.payload.logical).AccountSupported :=
  CanonicalCellRegistry.book_accountSupported _ _ _ prepared.book.law

/-- The actual source-derived birth patch preserves support, with no premise
about hidden balances supplied by the caller. -/
theorem PreparedBirth.post_book_accountSupported {deployment : Deployment} {pins : FactoryPins}
    {durable : Durable} {descriptor : Descriptor Registry}
    (prepared : PreparedBirth profile deployment pins durable descriptor) :
    (logicalBook prepared.resources.post.logical).AccountSupported :=
  prepared.resources.accountSupported prepared.book_accountSupported

theorem PreparedBirth.registration_accounts_only {deployment : Deployment} {pins : FactoryPins}
    {durable : Durable} {descriptor : Descriptor Registry}
    (prepared : PreparedBirth profile deployment pins durable descriptor) :
    RegistrationsAdmitted (logicalBook prepared.book.payload.logical)
        descriptor.resourceBatch.registrations ↔
      RegistrationsFresh (logicalBook prepared.book.payload.logical).accounts
        descriptor.resourceBatch.registrations :=
  registrationsAdmitted_iff_fresh _ _ prepared.book_accountSupported

end Minidregg.Kernel.ResourceBirthController.Concrete
