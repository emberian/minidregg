/- Exact axiom accounting for source support, genesis, and native rejection. -/
import Kernel.NativeHostBookInvariant
import Kernel.NativeHostBookAdmission

open Minidregg.Theory.CanonicalResourceKernel

/-- info: 'Minidregg.Theory.CanonicalResourceKernel.Book.AccountSupported.balance_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Book.AccountSupported.balance_zero
/-- info: 'Minidregg.Theory.CanonicalResourceKernel.Book.accountSupported_iff_zero_outside' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Book.accountSupported_iff_zero_outside
/-- info: 'Minidregg.Theory.CanonicalResourceKernel.Book.empty_accountSupported' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Book.empty_accountSupported
/-- info: 'Minidregg.Theory.CanonicalResourceKernel.Book.zero_accountSupported' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Book.zero_accountSupported
/-- info: 'Minidregg.Theory.CanonicalResourceKernel.Book.registerAccount_accountSupported' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Book.registerAccount_accountSupported
/-- info: 'Minidregg.Theory.CanonicalResourceKernel.Book.applyPosting_accountSupported' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Book.applyPosting_accountSupported
/-- info: 'Minidregg.Theory.CanonicalResourceKernel.Operation.apply_accountSupported' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Operation.apply_accountSupported
/-- info: 'Minidregg.Theory.CanonicalResourceKernel.Accepted.accountSupported' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Accepted.accountSupported
/-- info: 'Minidregg.Theory.CanonicalResourceKernel.registrationAdmission_iff_fresh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms registrationAdmission_iff_fresh
/-- info: 'Minidregg.Theory.CanonicalResourceKernel.registerAccounts_accountSupported' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms registerAccounts_accountSupported
/-- info: 'Minidregg.Theory.CanonicalResourceKernel.registrationsAdmitted_iff_fresh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms registrationsAdmitted_iff_fresh
/-- info: 'Minidregg.Theory.CanonicalResourceKernel.registrationsAdmitted_accounts_only' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms registrationsAdmitted_accounts_only
/-- info: 'Minidregg.Theory.CanonicalResourceKernel.applyOperations_accountSupported' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms applyOperations_accountSupported
/-- info: 'Minidregg.Theory.CanonicalResourceKernel.Batch.apply_accountSupported' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Batch.apply_accountSupported
/-- info: 'Minidregg.Theory.CanonicalResourceKernel.Batch.run_accountSupported' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Batch.run_accountSupported
/-- info: 'Minidregg.Theory.CanonicalResourceKernel.AcceptedBatch.accountSupported' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms AcceptedBatch.accountSupported
/-- info: 'Minidregg.Theory.CanonicalResourceKernel.witnessHiddenBook_not_accountSupported' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms witnessHiddenBook_not_accountSupported
/-- info: 'Minidregg.Kernel.NativeHostGenesis.fund_accountSupported' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.NativeHostGenesis.fund_accountSupported
/-- info: 'Minidregg.Kernel.NativeHostGenesis.initialBook_accountSupported' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.NativeHostGenesis.initialBook_accountSupported
/-- info: 'Minidregg.Kernel.ResourceBirthController.Concrete.PreparedBirth.book_accountSupported' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.ResourceBirthController.Concrete.PreparedBirth.book_accountSupported
/-- info: 'Minidregg.Kernel.ResourceBirthController.Concrete.PreparedBirth.post_book_accountSupported' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.ResourceBirthController.Concrete.PreparedBirth.post_book_accountSupported
/-- info: 'Minidregg.Kernel.ResourceBirthController.Concrete.PreparedBirth.registration_accounts_only' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.ResourceBirthController.Concrete.PreparedBirth.registration_accounts_only
/-- info: 'Minidregg.Kernel.NativeHost.validateLoaded_cellLaw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.NativeHost.validateLoaded_cellLaw
/-- info: 'Minidregg.Kernel.NativeHost.validateLoaded_refuses_hidden_book' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.NativeHost.validateLoaded_refuses_hidden_book
/-- info: 'Minidregg.Kernel.NativeHost.validateLoaded_refuses_witnessHiddenBook' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.NativeHost.validateLoaded_refuses_witnessHiddenBook
