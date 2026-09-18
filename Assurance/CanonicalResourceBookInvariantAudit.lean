/- Exact axiom accounting for source support, genesis, and native rejection. -/
import Kernel.NativeHostBookInvariant
import Kernel.NativeHostBookAdmission

open Minidregg.Theory.CanonicalResourceKernel

#print axioms Book.AccountSupported.balance_zero
#print axioms Book.accountSupported_iff_zero_outside
#print axioms Book.empty_accountSupported
#print axioms Book.zero_accountSupported
#print axioms Book.registerAccount_accountSupported
#print axioms Book.applyPosting_accountSupported
#print axioms Operation.apply_accountSupported
#print axioms Accepted.accountSupported
#print axioms registrationAdmission_iff_fresh
#print axioms registerAccounts_accountSupported
#print axioms registrationsAdmitted_iff_fresh
#print axioms registrationsAdmitted_accounts_only
#print axioms applyOperations_accountSupported
#print axioms Batch.apply_accountSupported
#print axioms Batch.run_accountSupported
#print axioms AcceptedBatch.accountSupported
#print axioms witnessHiddenBook_not_accountSupported
#print axioms Minidregg.Kernel.NativeHostGenesis.fund_accountSupported
#print axioms Minidregg.Kernel.NativeHostGenesis.initialBook_accountSupported
#print axioms Minidregg.Kernel.ResourceBirthController.Concrete.PreparedBirth.book_accountSupported
#print axioms Minidregg.Kernel.ResourceBirthController.Concrete.PreparedBirth.post_book_accountSupported
#print axioms Minidregg.Kernel.ResourceBirthController.Concrete.PreparedBirth.registration_accounts_only
#print axioms Minidregg.Kernel.NativeHost.validateLoaded_cellLaw
#print axioms Minidregg.Kernel.NativeHost.validateLoaded_refuses_hidden_book
#print axioms Minidregg.Kernel.NativeHost.validateLoaded_refuses_witnessHiddenBook
