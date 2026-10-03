# Shared-coordinate single-seller consumer. Repeated roles are projections of
# ONE exact sampled account table; they do not manufacture additional funding.
# Worst-case reservation budgets aggregate by funding coordinate. Each order's
# private unspent value names its own reserved budget, not repeated whole balance.
import Base
import ./MarketMath.bend as Math
import ./SingleSellerAllocation.bend as Seller
import ./CanonicalBookSettlement.bend as Book

type Lookup is Data:
  Missing{}
  Found{balance: Nat}

type PrivateResult is Data:
  PrivateResult{recipient: List<&2, Nat>, audience: List<&2, Nat>,
    keyEpoch: List<&2, Nat>, reservation: List<&2, Nat>,
    reservedBudget: Nat, units: Nat, price: Nat, payment: Nat, unspentBudget: Nat}

type Result is Data:
  Refused{}
  Prepared{book: Nat, expectedRoot: List<&2, Nat>,
    samples: List<&2, Book.Account>, operations: List<&2, Book.Transfer>,
    returns: List<&2, PrivateResult>, allocation: Seller.Allocation}

def lookup_choice(balance: Nat, later: Lookup, same: Bool) -> Lookup:
  match same:
    case False{}:
      later
    case True{}:
      Found{balance}

def lookup(+wanted: Book.Coordinate, accounts: List<&2, Book.Account>) -> Lookup:
  match accounts:
    case Nil{}:
      Missing{}
    case Con{+account, rest}:
      match account:
        case Book.Account{id, asset, balance}:
          lookup_choice(balance, lookup(wanted, rest),
            Book.coordinate_eq(wanted, Book.coordinate(account)))

def append_accounts(bids: List<&2, Book.Bid>) -> List<&2, Book.Account>:
  match bids:
    case Nil{}:
      Nil{}
    case Con{Book.Bid{order, funds, goods, audience, keyEpoch}, rest}:
      Con{funds, Con{goods, append_accounts(rest)}}

def same_balance(balance: Nat, lookup: Lookup) -> Bool:
  match lookup:
    case Missing{}:
      True{}
    case Found{other}:
      Nat.eq(balance, other)

# Repeated role inputs must be exactly the same post-funding sampled balance.
def consistent(accounts: List<&2, Book.Account>) -> Bool:
  match accounts:
    case Nil{}:
      True{}
    case Con{+account, +rest}:
      match account:
        case Book.Account{id, asset, balance}:
          Bool.and(same_balance(balance, lookup(Book.coordinate(account), rest)), consistent(rest))

def unique_choice(account: Book.Account, rest: List<&2, Book.Account>, lookup: Lookup) -> List<&2, Book.Account>:
  match lookup:
    case Missing{}:
      Con{account, rest}
    case Found{balance}:
      rest

# Dedupe is deterministic last occurrence order. Native sampleFunding checks
# this unique table; current root and every role projection must bind to it.
def unique(accounts: List<&2, Book.Account>) -> List<&2, Book.Account>:
  match accounts:
    case Nil{}:
      Nil{}
    case Con{+account, +rest}:
      unique_choice(account, unique(rest), lookup(Book.coordinate(account), rest))

def reservation_used(+reservation: List<&2, Nat>, bids: List<&2, Book.Bid>) -> Bool:
  match bids:
    case Nil{}:
      False{}
    case Con{Book.Bid{Seller.Order{subject, other, price, quantity}, funds, goods, audience, keyEpoch}, rest}:
      Math.choose_bool(True{}, reservation_used(reservation, rest), Bytes.eq(reservation, other))

def reservations_unique(bids: List<&2, Book.Bid>) -> Bool:
  match bids:
    case Nil{}:
      True{}
    case Con{Book.Bid{Seller.Order{subject, reservation, price, quantity}, funds, goods, audience, keyEpoch}, +rest}:
      Bool.and(Math.not(reservation_used(reservation, rest)), reservations_unique(rest))

def reserved(+coordinate: Book.Coordinate, bids: List<&2, Book.Bid>) -> Nat:
  match bids:
    case Nil{}:
      0n
    case Con{Book.Bid{Seller.Order{subject, reservation, price, quantity}, funds, goods, audience, keyEpoch}, rest}:
      Math.add(Math.choose_nat(Math.mul(price, quantity), 0n,
        Book.coordinate_eq(coordinate, Book.coordinate(funds))), reserved(coordinate, rest))

def backed(accounts: List<&2, Book.Account>, +bids: List<&2, Book.Bid>) -> Bool:
  match accounts:
    case Nil{}:
      True{}
    case Con{+account, rest}:
      match account:
        case Book.Account{id, asset, balance}:
          Bool.and(Math.le(reserved(Book.coordinate(account), bids), balance), backed(rest, bids))

def returns(bids: List<&2, Book.Bid>, +fills: List<&2, Seller.Fill>, +price: Nat,
    +position: Nat) -> List<&2, PrivateResult>:
  match bids:
    case Nil{}:
      Nil{}
    case Con{Book.Bid{Seller.Order{subject, reservation, limit, quantity},
        funds, goods, audience, keyEpoch}, rest}:
      +units = Book.units_at(position, fills)
      +payment = Math.mul(price, units)
      +budget = Math.mul(limit, quantity)
      Con{PrivateResult{subject, audience, keyEpoch, reservation, budget, units, price,
        payment, Math.sub(budget, payment)}, returns(rest, fills, price, Succ{position})}

def choose(book: Nat, root: List<&2, Nat>, samples: List<&2, Book.Account>,
    batch: Book.Batch, returns: List<&2, PrivateResult>, allocation: Seller.Allocation,
    allowed: Bool) -> Result:
  match batch allowed:
    case batch False{}:
      Refused{}
    case Book.Batch{operations, legacyReturns} True{}:
      Prepared{book, root, samples, operations, returns, allocation}

def prepare(book: Nat, root: List<&2, Nat>, +stock: Book.Account, +proceeds: Book.Account,
    +bids: List<&2, Book.Bid>, +allocation: Seller.Allocation) -> Result:
  match stock proceeds allocation:
    case Book.Account{stockId, +goodsAsset, stockBalance}
        Book.Account{proceedsId, +paymentAsset, proceedsBalance}
        Seller.Allocation{+price, +fills, remaining}:
      +roles = {Con{stock, Con{proceeds, append_accounts(bids)}} : List<&2, Book.Account>}
      +samples = unique(roles)
      choose(book, root, samples, Book.batch(bids, fills, stock, proceeds, price, 0n),
        returns(bids, fills, price, 0n), allocation,
        Bool.and(consistent(roles), Bool.and(reservations_unique(bids),
          Bool.and(backed(samples, bids),
            Book.valid_bids(bids, fills, paymentAsset, goodsAsset, price, 0n)))))

def settle(input: Book.Input) -> Result:
  match input:
    case Book.Input{book, root, +stock, proceeds, +bids}:
      match stock:
        case Book.Account{id, asset, supply}:
          prepare(book, root, stock, proceeds, bids, Seller.allocate(supply, Book.orders(bids)))

# A successful native table check is still required; this law preserves every
# sample/operation/return/root exactly through the source's guarded constructor.
def ExactPrepared(-book: Nat, -root: List<&2, Nat>, -samples: List<&2, Book.Account>,
    batch: Book.Batch, -returns: List<&2, PrivateResult>, -allocation: Seller.Allocation,
    result: Result) -> Type:
  match batch result:
    case batch Refused{}:
      Unit
    case Book.Batch{operations, legacyReturns}
        Prepared{chosenBook, expectedRoot, chosenSamples, chosenOperations, chosenReturns, chosenAllocation}:
      {Prepared{chosenBook, expectedRoot, chosenSamples, chosenOperations, chosenReturns, chosenAllocation}
        == Prepared{book, root, samples, operations, returns, allocation} : Result}

law prepared_exact:
  for +book: Nat
  for +root: List<&2, Nat>
  for +samples: List<&2, Book.Account>
  for +batch: Book.Batch
  for +returns: List<&2, PrivateResult>
  for +allocation: Seller.Allocation
  for allowed: Bool
  ExactPrepared(book, root, samples, batch, returns, allocation,
    choose(book, root, samples, batch, returns, allocation, allowed))

def prepared_exact(book, root, samples, batch, returns, allocation, allowed):
  match batch allowed:
    case batch False{}:
      Unit{}
    case Book.Batch{operations, legacyReturns} True{}:
      {==}

