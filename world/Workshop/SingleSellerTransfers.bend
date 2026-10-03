# Monetary consumer: lowers only to native DeclaredActionLowering.Action.move.
# Presence is explicit in this profile: all sampled balances must be PRESENT.
# Missing accounts/asset coordinates are refused by the input bridge, not read as 0.
# Scalar BalanceWrite from SingleSellerSettlement is only a logical reference.
import Base
import ./MarketMath.bend as Math
import ./SingleSellerAllocation.bend as Seller
import ./SingleSellerSettlement.bend as Settlement

type Move is Data:
  Move{source: List<&2, Nat>, destination: List<&2, Nat>, asset: List<&2, Nat>,
    sourceExpected: Nat, destinationExpected: Nat, amount: Nat}

type Group is Data:
  Group{source: List<&2, Nat>, expectedRoot: List<&2, Nat>, moves: List<&2, Move>}

type Goods is Data:
  Goods{moves: List<&2, Move>, remaining: Nat}

type Payments is Data:
  Payments{groups: List<&2, Group>, returns: List<&2, Settlement.PrivateResult>, proceeds: Nat}

type Result is Data:
  Refused{}
  Prepared{groups: List<&2, Group>, returns: List<&2, Settlement.PrivateResult>,
    allocation: Seller.Allocation}

def move(source: Settlement.Account, destination: Settlement.Account,
    sourceExpected: Nat, destinationExpected: Nat, amount: Nat) -> Move:
  match source destination:
    case Settlement.Account{sourceId, sourceRoot, sourceOwner, asset, sourceField, sourceBalance}
        Settlement.Account{destinationId, destinationRoot, destinationOwner, destinationAsset,
          destinationField, destinationBalance}:
      Move{sourceId, destinationId, asset, sourceExpected, destinationExpected, amount}

def prepend_goods(next: Move, goods: Goods) -> Goods:
  match goods:
    case Goods{moves, remaining}:
      Goods{Con{next, moves}, remaining}

# Groups preserve the native one-debited-source-per-target discipline.
# Every later goods debit reads the preceding debit's resulting stock.
def goods(bids: List<&2, Settlement.Bid>, +fills: List<&2, Seller.Fill>,
    +stock: Settlement.Account, +available: Nat, +position: Nat) -> Goods:
  match bids:
    case Nil{}:
      Goods{Nil{}, available}
    case Con{Settlement.Bid{order, funds, +target, audience, keyEpoch}, rest}:
      match target:
        case Settlement.Account{resource, root, owner, asset, field, balance}:
          +units = Settlement.units_at(position, fills)
          prepend_goods(move(stock, target, available, balance, units),
            goods(rest, fills, stock, Math.sub(available, units), Succ{position}))

def prepend_payment(source: Settlement.Account, payment: Move,
    result: Settlement.PrivateResult, tail: Payments) -> Payments:
  match source tail:
    case Settlement.Account{resource, root, owner, asset, field, balance}
        Payments{groups, returns, proceeds}:
      Payments{Con{Group{resource, root, Con{payment, Nil{}}}, groups},
        Con{result, returns}, proceeds}

# Seller proceeds are shared by the ordered bidder payments, so its expected
# value is threaded. Repeating the initial proceeds snapshot would be stale.
def payments(bids: List<&2, Settlement.Bid>, +fills: List<&2, Seller.Fill>,
    +price: Nat, +destination: Settlement.Account, +received: Nat, +position: Nat) -> Payments:
  match bids:
    case Nil{}:
      Payments{Nil{}, Nil{}, received}
    case Con{+bid, rest}:
      match bid:
        case Settlement.Bid{order, +funds, target, audience, keyEpoch}:
          match funds:
            case Settlement.Account{resource, root, owner, asset, field, +balance}:
              +units = Settlement.units_at(position, fills)
              +payment = Math.mul(price, units)
              prepend_payment(funds, move(funds, destination, balance, received, payment),
                Settlement.bid_result(bid, price, units),
                payments(rest, fills, price, destination, Math.add(received, payment), Succ{position}))

def join(stock: Settlement.Account, allocation: Seller.Allocation,
    goods: Goods, payments: Payments, allowed: Bool) -> Result:
  match stock goods payments allowed:
    case stock goods payments False{}:
      Refused{}
    case Settlement.Account{resource, root, owner, asset, field, balance}
        Goods{moves, remaining} Payments{groups, returns, proceeds} True{}:
      Prepared{Con{Group{resource, root, moves}, groups}, returns, allocation}

def prepare(+stock: Settlement.Account, +proceeds: Settlement.Account,
    +bids: List<&2, Settlement.Bid>, +allocation: Seller.Allocation, valid: Bool) -> Result:
  match stock proceeds allocation:
    case Settlement.Account{resource, root, owner, asset, field, supply}
        Settlement.Account{proceedsResource, proceedsRoot, proceedsOwner,
          proceedsAsset, proceedsField, initialProceeds}
        Seller.Allocation{+price, +fills, remaining}:
      join(stock, allocation, goods(bids, fills, stock, supply, 0n),
        payments(bids, fills, price, proceeds, initialProceeds, 0n),
        Bool.and(valid, Settlement.backed_results(bids, fills, price, 0n)))

def settle(+stock: Settlement.Account, +proceeds: Settlement.Account,
    +bids: List<&2, Settlement.Bid>) -> Result:
  match stock proceeds:
    case Settlement.Account{stockResource, stockRoot, +seller, +goodsAsset, stockField, supply}
        Settlement.Account{proceedsResource, proceedsRoot, proceedsOwner,
          +paymentAsset, proceedsField, balance}:
      prepare(stock, proceeds, bids, Seller.allocate(supply, Settlement.order_list(bids)),
        Bool.and(Bytes.eq(seller, proceedsOwner),
          Bool.and(Settlement.distinct(Con{stockResource,
            Con{proceedsResource, Settlement.identifiers(bids)}}),
            Settlement.valid_bids(paymentAsset, goodsAsset, bids))))

def ExactMove(source: Settlement.Account, destination: Settlement.Account,
    -sourceExpected: Nat, -destinationExpected: Nat, -amount: Nat, result: Move) -> Type:
  match source destination:
    case Settlement.Account{sourceId, sourceRoot, sourceOwner, asset, sourceField, sourceBalance}
        Settlement.Account{destinationId, destinationRoot, destinationOwner, destinationAsset,
          destinationField, destinationBalance}:
      {result == Move{sourceId, destinationId, asset, sourceExpected, destinationExpected, amount} : Move}

law move_bound:
  for +source: Settlement.Account
  for +destination: Settlement.Account
  for +sourceExpected: Nat
  for +destinationExpected: Nat
  for +amount: Nat
  ExactMove(source, destination, sourceExpected, destinationExpected, amount,
    move(source, destination, sourceExpected, destinationExpected, amount))

def move_bound(source, destination, sourceExpected, destinationExpected, amount):
  match source destination:
    case Settlement.Account{sourceId, sourceRoot, sourceOwner, asset, sourceField, sourceBalance}
        Settlement.Account{destinationId, destinationRoot, destinationOwner, destinationAsset,
          destinationField, destinationBalance}:
      {==}

