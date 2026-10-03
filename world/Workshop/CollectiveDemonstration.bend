# Source-derived receiving scenario: account 1 owns both goods asset 7 and
# money asset 8. Roots and all identity/audience bytes remain native inputs.
# This is a closed numeric example under a general identity/root binder; it is
# separate from the general conservation theorem in SingleSellerAllocation.
import Base
import ./SingleSellerAllocation.bend as Seller
import ./CanonicalBookSettlement.bend as Book

def input(root: List<&2, Nat>, a: List<&2, Nat>, b: List<&2, Nat>,
    audienceA: List<&2, Nat>, audienceB: List<&2, Nat>, +epoch: List<&2, Nat>) -> Book.Input:
  Book.Input{9n, root, Book.Account{1n, 7n, 7n}, Book.Account{1n, 8n, 10n},
    Con{Book.Bid{Seller.Order{a, Con{21n, Nil{}}, 5n, 4n},
      Book.Account{2n, 8n, 20n}, Book.Account{2n, 7n, 0n}, audienceA, epoch},
      Con{Book.Bid{Seller.Order{b, Con{31n, Nil{}}, 3n, 5n},
        Book.Account{3n, 8n, 15n}, Book.Account{3n, 7n, 2n}, audienceB, epoch}, Nil{}}}}

def expected(root: List<&2, Nat>, +a: List<&2, Nat>, +b: List<&2, Nat>,
    audienceA: List<&2, Nat>, audienceB: List<&2, Nat>, +epoch: List<&2, Nat>) -> Book.Result:
  Book.Prepared{9n, root,
    Con{Book.Transfer{1n, 2n, 7n, 4n},
      Con{Book.Transfer{2n, 1n, 8n, 12n},
        Con{Book.Transfer{1n, 3n, 7n, 3n},
          Con{Book.Transfer{3n, 1n, 8n, 9n}, Nil{}}}}},
    Con{Book.PrivateResult{a, audienceA, epoch, Con{21n, Nil{}}, 4n, 3n, 12n, 8n},
      Con{Book.PrivateResult{b, audienceB, epoch, Con{31n, Nil{}}, 3n, 3n, 9n, 6n}, Nil{}}},
    Seller.Allocation{3n,
      Con{Seller.Fill{0n, a, Con{21n, Nil{}}, 4n},
        Con{Seller.Fill{1n, b, Con{31n, Nil{}}, 3n}, Nil{}}}, 0n}}

law actual_source_settlement:
  for +root: List<&2, Nat>
  for +a: List<&2, Nat>
  for +b: List<&2, Nat>
  for +audienceA: List<&2, Nat>
  for +audienceB: List<&2, Nat>
  for +epoch: List<&2, Nat>
  {Book.settle(input(root, a, b, audienceA, audienceB, epoch)) ==
    expected(root, a, b, audienceA, audienceB, epoch) : Book.Result}

def actual_source_settlement(root, a, b, audienceA, audienceB, epoch):
  {==}

