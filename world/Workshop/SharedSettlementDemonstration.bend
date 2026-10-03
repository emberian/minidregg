# Actual source cases for shared backing: two orders debit the same account.
# The repeated role references must agree, and aggregate worst-case budgets
# must fit one sampled balance. No sample copied per order creates new money.
import Base
import ./SingleSellerAllocation.bend as Seller
import ./CanonicalBookSettlement.bend as Book
import ./SharedBookSettlement.bend as Shared

def input(root: List<&2, Nat>, +subject: List<&2, Nat>, +audience: List<&2, Nat>,
    +epoch: List<&2, Nat>, firstFunds: Nat, secondFunds: Nat) -> Book.Input:
  Book.Input{9n, root, Book.Account{1n, 7n, 7n}, Book.Account{1n, 8n, 10n},
    Con{Book.Bid{Seller.Order{subject, Con{21n, Nil{}}, 5n, 4n},
      Book.Account{2n, 8n, firstFunds}, Book.Account{2n, 7n, 0n}, audience, epoch},
      Con{Book.Bid{Seller.Order{subject, Con{22n, Nil{}}, 3n, 5n},
        Book.Account{2n, 8n, secondFunds}, Book.Account{2n, 7n, 0n}, audience, epoch}, Nil{}}}}

def expected(root: List<&2, Nat>, +subject: List<&2, Nat>, +audience: List<&2, Nat>,
    +epoch: List<&2, Nat>) -> Shared.Result:
  Shared.Prepared{9n, root,
    Con{Book.Account{1n, 7n, 7n}, Con{Book.Account{1n, 8n, 10n},
      Con{Book.Account{2n, 8n, 35n}, Con{Book.Account{2n, 7n, 0n}, Nil{}}}}},
    Con{Book.Transfer{1n, 2n, 7n, 4n},
      Con{Book.Transfer{2n, 1n, 8n, 12n},
        Con{Book.Transfer{1n, 2n, 7n, 3n},
          Con{Book.Transfer{2n, 1n, 8n, 9n}, Nil{}}}}},
    Con{Shared.PrivateResult{subject, audience, epoch, Con{21n, Nil{}}, 20n, 4n, 3n, 12n, 8n},
      Con{Shared.PrivateResult{subject, audience, epoch, Con{22n, Nil{}}, 15n, 3n, 3n, 9n, 6n}, Nil{}}},
    Seller.Allocation{3n,
      Con{Seller.Fill{0n, subject, Con{21n, Nil{}}, 4n},
        Con{Seller.Fill{1n, subject, Con{22n, Nil{}}, 3n}, Nil{}}}, 0n}}

law shared_orders_actual:
  for +root: List<&2, Nat>
  for +subject: List<&2, Nat>
  for +audience: List<&2, Nat>
  for +epoch: List<&2, Nat>
  {Shared.settle(input(root, subject, audience, epoch, 35n, 35n)) ==
    expected(root, subject, audience, epoch) : Shared.Result}

def shared_orders_actual(root, subject, audience, epoch):
  {==}

# Each order is individually backed by 20, but their 20+15 reservations are not.
law copied_balance_does_not_multiply_backing:
  for root: List<&2, Nat>
  for subject: List<&2, Nat>
  for audience: List<&2, Nat>
  for epoch: List<&2, Nat>
  {Shared.settle(input(root, subject, audience, epoch, 20n, 20n)) == Shared.Refused{} : Shared.Result}

def copied_balance_does_not_multiply_backing(root, subject, audience, epoch):
  {==}

law inconsistent_alias_refused:
  for root: List<&2, Nat>
  for subject: List<&2, Nat>
  for audience: List<&2, Nat>
  for epoch: List<&2, Nat>
  {Shared.settle(input(root, subject, audience, epoch, 35n, 36n)) == Shared.Refused{} : Shared.Result}

def inconsistent_alias_refused(root, subject, audience, epoch):
  {==}

