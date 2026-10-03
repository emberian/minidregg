# Actual production-money boundary: ONE canonical resource book.
# This module emits canonical Operation.transfer-shaped intents, never scalar
# accountBalance writes or per-account effect-cell replicas. The input adapter
# must derive every Account coordinate from the same authenticated book/root and
# establish membership in book.accounts. Zero is then the book's exact balance.
# The ordinary receiver must authorize every debit and atomically admit the batch.
import Base
import ./MarketMath.bend as Math
import ./SingleSellerAllocation.bend as Seller

type Account is Data:
  Account{account: Nat, asset: Nat, balance: Nat}

type Bid is Data:
  Bid{order: Seller.Order, funds: Account, goods: Account,
    audience: List<&2, Nat>, keyEpoch: List<&2, Nat>}

type Input is Data:
  Input{book: Nat, root: List<&2, Nat>, stock: Account, proceeds: Account, bids: List<&2, Bid>}

# Exactly the four Nat arguments of CanonicalResourceKernel.Operation.transfer.
type Transfer is Data:
  Transfer{source: Nat, destination: Nat, asset: Nat, amount: Nat}

type PrivateResult is Data:
  PrivateResult{recipient: List<&2, Nat>, audience: List<&2, Nat>,
    keyEpoch: List<&2, Nat>, reservation: List<&2, Nat>,
    units: Nat, price: Nat, payment: Nat, unspentReserved: Nat}

type Batch is Data:
  Batch{operations: List<&2, Transfer>, returns: List<&2, PrivateResult>}

type Result is Data:
  Refused{}
  Prepared{book: Nat, expectedRoot: List<&2, Nat>, operations: List<&2, Transfer>,
    returns: List<&2, PrivateResult>, allocation: Seller.Allocation}

# A coordinate, not an account alone, is the reusable-value identity. The same
# account may own money and goods in distinct assets; this is not forbidden.
type Coordinate is Data:
  Coordinate{account: Nat, asset: Nat}

def coordinate(account: Account) -> Coordinate:
  match account:
    case Account{id, asset, balance}:
      Coordinate{id, asset}

def coordinate_eq(a: Coordinate, b: Coordinate) -> Bool:
  match a b:
    case Coordinate{ai, aa} Coordinate{bi, ba}:
      Bool.and(Nat.eq(ai, bi), Nat.eq(aa, ba))

def contains(+coordinate: Coordinate, coordinates: List<&2, Coordinate>) -> Bool:
  match coordinates:
    case Nil{}:
      False{}
    case Con{head, rest}:
      Math.choose_bool(True{}, contains(coordinate, rest), coordinate_eq(coordinate, head))

def distinct(coordinates: List<&2, Coordinate>) -> Bool:
  match coordinates:
    case Nil{}:
      True{}
    case Con{head, +rest}:
      Bool.and(Math.not(contains(head, rest)), distinct(rest))

def coordinates(bids: List<&2, Bid>) -> List<&2, Coordinate>:
  match bids:
    case Nil{}:
      Nil{}
    case Con{Bid{order, funds, goods, audience, keyEpoch}, rest}:
      Con{coordinate(funds), Con{coordinate(goods), coordinates(rest)}}

def orders(bids: List<&2, Bid>) -> List<&2, Seller.Order>:
  match bids:
    case Nil{}:
      Nil{}
    case Con{Bid{order, funds, goods, audience, keyEpoch}, rest}:
      Con{order, orders(rest)}

def units_at(+position: Nat, fills: List<&2, Seller.Fill>) -> Nat:
  match fills:
    case Nil{}:
      0n
    case Con{Seller.Fill{otherPosition, subject, reservation, units}, rest}:
      Math.choose_nat(units, units_at(position, rest), Nat.eq(position, otherPosition))

def valid_bids(bids: List<&2, Bid>, +fills: List<&2, Seller.Fill>,
    +paymentAsset: Nat, +goodsAsset: Nat, +price: Nat, +position: Nat) -> Bool:
  match bids:
    case Nil{}:
      True{}
    case Con{Bid{Seller.Order{subject, reservation, +limit, +quantity},
        Account{fundsId, fundsAsset, +funds}, Account{goodsId, heldAsset, goods},
        audience, keyEpoch}, rest}:
      +units = units_at(position, fills)
      Bool.and(Nat.eq(paymentAsset, fundsAsset),
        Bool.and(Nat.eq(goodsAsset, heldAsset),
          Bool.and(Math.le(Math.mul(limit, quantity), funds),
            Bool.and(Math.le(units, quantity),
              Bool.and(Math.le(Math.mul(price, units), funds),
                Bool.and(Math.choose_bool(True{}, Math.le(price, limit), Nat.eq(units, 0n)),
                  valid_bids(rest, fills, paymentAsset, goodsAsset, price, Succ{position})))))))

def prepend(stock: Account, proceeds: Account, bid: Bid,
    +units: Nat, +price: Nat, batch: Batch) -> Batch:
  match stock proceeds bid batch:
    case Account{stockId, goodsAsset, stockBalance}
        Account{proceedsId, paymentAsset, proceedsBalance}
        Bid{Seller.Order{subject, reservation, limit, quantity},
          Account{fundsId, fundsAsset, funds}, Account{goodsId, heldAsset, goods},
          audience, keyEpoch} Batch{operations, returns}:
      +payment = Math.mul(price, units)
      Batch{Con{Transfer{stockId, goodsId, goodsAsset, units},
        Con{Transfer{fundsId, proceedsId, paymentAsset, payment}, operations}},
        Con{PrivateResult{subject, audience, keyEpoch, reservation, units, price,
          payment, Math.sub(funds, payment)}, returns}}

# All operations belong to one book batch, in admitted book order. Canonical
# native Batch.Admission applies each operation to the preceding resulting book.
def batch(bids: List<&2, Bid>, +fills: List<&2, Seller.Fill>,
    +stock: Account, +proceeds: Account, +price: Nat, +position: Nat) -> Batch:
  match bids:
    case Nil{}:
      Batch{Nil{}, Nil{}}
    case Con{bid, rest}:
      prepend(stock, proceeds, bid, units_at(position, fills), price,
        batch(rest, fills, stock, proceeds, price, Succ{position}))

def choose(book: Nat, root: List<&2, Nat>, allocation: Seller.Allocation,
    batch: Batch, allowed: Bool) -> Result:
  match batch allowed:
    case batch False{}:
      Refused{}
    case Batch{operations, returns} True{}:
      Prepared{book, root, operations, returns, allocation}

def prepare(book: Nat, root: List<&2, Nat>, +stock: Account, +proceeds: Account,
    +bids: List<&2, Bid>, +allocation: Seller.Allocation) -> Result:
  match stock proceeds allocation:
    case Account{stockId, +goodsAsset, stockBalance}
        Account{proceedsId, +paymentAsset, proceedsBalance}
        Seller.Allocation{+price, +fills, remaining}:
      choose(book, root, allocation, batch(bids, fills, stock, proceeds, price, 0n),
        Bool.and(distinct(Con{coordinate(stock), Con{coordinate(proceeds), coordinates(bids)}}),
          valid_bids(bids, fills, paymentAsset, goodsAsset, price, 0n)))

def settle(input: Input) -> Result:
  match input:
    case Input{book, root, +stock, proceeds, +bids}:
      match stock:
        case Account{id, asset, supply}:
          prepare(book, root, stock, proceeds, bids, Seller.allocate(supply, orders(bids)))

def ExactBook(-book: Nat, -root: List<&2, Nat>, result: Result) -> Type:
  match result:
    case Refused{}:
      Unit
    case Prepared{chosen, expectedRoot, operations, returns, allocation}:
      Pair({chosen == book : Nat}, {expectedRoot == root : List<&2, Nat>})

law chosen_book_exact:
  for +book: Nat
  for +root: List<&2, Nat>
  for allocation: Seller.Allocation
  for batch: Batch
  for allowed: Bool
  ExactBook(book, root, choose(book, root, allocation, batch, allowed))

def chosen_book_exact(book, root, allocation, batch, allowed):
  match batch allowed:
    case batch False{}:
      Unit{}
    case Batch{operations, returns} True{}:
      ({==}, {==})

