/- Concrete poles for the actual account-policy cut. These are Lean-evaluated
source cases, not claims about a launched native service. -/
import Compiler.CanonicalAccountView
import Pred.Core

namespace Minidregg.Compiler.CanonicalAccountView.Audit

open Minidregg.Theory
set_option autoImplicit false

def book (own other : Int) : CanonicalResourceKernel.Book where
  accounts := {7, 8}
  balances := DFinsupp.single (7, 3) own + DFinsupp.single (8, 3) other
  leaseRecords := 0

theorem selected_balance_map (own other : Int) :
    accountBalanceMap (book own other) 7 = DFinsupp.single 3 own := by
  ext asset
  change (book own other).balance 7 asset = _
  simp [book, CanonicalResourceKernel.Book.balance]

theorem selected_cut (other : Int) : accountCut (book 42 other) 7 = [(3, 42)] := by
  unfold accountCut
  rw [selected_balance_map]
  simp [CanonicalResourcePageMaterializer.entries_eq]

theorem own_balance_is_visible :
    (Minidregg.Pred.State.mk (slots (book 42 99) 7)).get "account/balance/3" = some 42 := by
  simp only [slots, selected_cut]
  decide

theorem own_balance_policy_accepts :
    Minidregg.Pred.eval (.eq "account/balance/3" 42)
      ⟨slots (book 42 99) 7⟩ ⟨slots (book 42 99) 7⟩ = true := by
  simp only [slots, selected_cut]
  decide

theorem wrong_own_balance_policy_refuses :
    Minidregg.Pred.eval (.eq "account/balance/3" 99)
      ⟨slots (book 42 99) 7⟩ ⟨slots (book 42 99) 7⟩ = false := by
  simp only [slots, selected_cut]
  decide

theorem unrelated_balance_change_invisible :
    slots (book 42 99) 7 = slots (book 42 10000) 7 := by
  apply slots_noninterference
  intro asset
  simp [book, CanonicalResourceKernel.Book.balance]

theorem old_whole_book_byte_oracle_absent :
    (Minidregg.Pred.State.mk (slots (book 42 99) 7)).get "cell/book/bytes/0" = none := by
  simp only [slots, selected_cut]
  decide

theorem old_whole_authority_byte_oracle_absent :
    (Minidregg.Pred.State.mk (slots (book 42 99) 7)).get "cell/authority/bytes/0" = none := by
  simp only [slots, selected_cut]
  decide

/-- info: 'Minidregg.Compiler.CanonicalAccountView.Audit.unrelated_balance_change_invisible' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms unrelated_balance_change_invisible

end Minidregg.Compiler.CanonicalAccountView.Audit
