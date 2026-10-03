/- Kernel axiom accounting and general refuters for canonical money preparation.
No native execution or authority claim is inferred from these statements. -/
import Kernel.ResourceMoneyOperationDomain
import Theory.AssertAxioms

namespace Minidregg.Assurance.ResourceMoneyOperationDomainAudit

open Minidregg.Kernel.ResourceMoneyOperationDomain
open Minidregg.Theory.CanonicalResourceKernel
open Minidregg.Theory.TypedAuthorization

set_option autoImplicit false

variable {deployment : Deployment} {physical : Physical}
  {book : LoadedBook deployment physical} {root : Digest}
  {funding : Minidregg.Kernel.RunComputeBudget.PreparedBook book.cell}
  {operations : List Operation}
  {prepared : Prepared book root funding operations} {samples : List Sample}

theorem spoofed_balance_cannot_be_checked (checked : CheckedSamples prepared samples)
    (sample : Sample) (member : sample ∈ samples)
    (spoofed : prepared.applicationPre.balance sample.account sample.asset ≠
      Int.ofNat sample.balance) : False :=
  spoofed (checked.balance_exact sample member)

theorem absent_account_cannot_be_checked (checked : CheckedSamples prepared samples)
    (sample : Sample) (member : sample ∈ samples)
    (absent : sample.account ∉ prepared.applicationPre.accounts) : False :=
  absent (checked.account_present sample member)

theorem stale_book_cannot_be_sampled
    (checked : SampledFunding book root funding samples)
    (stale : root ≠ physical.model.roots
      (Minidregg.Kernel.RunComputeBudgetDomain.bookId deployment)) : False :=
  stale checked.rootExact

theorem ordered_overdraft_cannot_be_prepared
    (prior suffix : List Operation) (operation : Operation)
    (position : operations = prior ++ operation :: suffix)
    (notMint : operation.isIssuerMint ≠ true)
    (overdrawn : (applyOperations prepared.applicationPre prior).balance
      operation.posting.source operation.posting.asset < Int.ofNat operation.posting.amount) :
    False :=
  (not_le_of_gt overdrawn) (prepared.source_solvent_at prior suffix operation position notMint)

#assert_axioms applyOperations_append
#assert_axioms combined_admitted
#assert_axioms Prepared.post_funding_first
#assert_axioms Prepared.conserves
#assert_axioms Prepared.accountSupported
#assert_axioms Prepared.at_most_one_book_write
#assert_axioms Prepared.writes_pre_exact
#assert_axioms Prepared.writes_roots_bound
#assert_axioms stale_root_refused
#assert_axioms Prepared.source_solvent_at
#assert_axioms spoofed_balance_cannot_be_checked
#assert_axioms absent_account_cannot_be_checked
#assert_axioms stale_book_cannot_be_sampled
#assert_axioms ordered_overdraft_cannot_be_prepared

end Minidregg.Assurance.ResourceMoneyOperationDomainAudit
