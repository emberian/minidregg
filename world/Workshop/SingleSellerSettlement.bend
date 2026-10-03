# Authored consumer of the exact SingleSellerAllocation source.
# These are logical native write/return requests, NOT capabilities or encrypted
# evidence. The shared Plan bridge supplies canonical native payload construction.
# Each account is taken from the same authenticated source sample. Current native
# authorization and expected-root admission still govern the atomic whole.
import Base
import ./MarketMath.bend as Math
import ./SingleSellerAllocation.bend as Seller

type Account is Data:
  Account{resource: List<&2, Nat>, root: List<&2, Nat>, owner: List<&2, Nat>,
    asset: List<&2, Nat>, field: Nat, balance: Nat}

type Bid is Data:
  Bid{order: Seller.Order, funds: Account, goods: Account,
    audience: List<&2, Nat>, keyEpoch: List<&2, Nat>}

type BalanceWrite is Data:
  BalanceWrite{resource: List<&2, Nat>, expectedRoot: List<&2, Nat>,
    field: Nat, before: Nat, after: Nat}

type PrivateResult is Data:
  PrivateResult{recipient: List<&2, Nat>, audience: List<&2, Nat>,
    keyEpoch: List<&2, Nat>, reservation: List<&2, Nat>,
    units: Nat, price: Nat, payment: Nat, unspentReserved: Nat}

type Batch is Data:
  Batch{writes: List<&2, BalanceWrite>, returns: List<&2, PrivateResult>, proceeds: Nat}

type Result is Data:
  Refused{}
  Prepared{writes: List<&2, BalanceWrite>, returns: List<&2, PrivateResult>,
    allocation: Seller.Allocation}

def order_list(bids: List<&2, Bid>) -> List<&2, Seller.Order>:
  match bids:
    case Nil{}:
      Nil{}
    case Con{Bid{order, funds, goods, audience, keyEpoch}, rest}:
      Con{order, order_list(rest)}

def account_id(account: Account) -> List<&2, Nat>:
  match account:
    case Account{resource, root, owner, asset, field, balance}:
      resource

def identifiers(bids: List<&2, Bid>) -> List<&2, List<&2, Nat>>:
  match bids:
    case Nil{}:
      Nil{}
    case Con{Bid{order, funds, goods, audience, keyEpoch}, rest}:
      Con{account_id(funds), Con{account_id(goods), identifiers(rest)}}

def contains(+resource: List<&2, Nat>, ids: List<&2, List<&2, Nat>>) -> Bool:
  match ids:
    case Nil{}:
      False{}
    case Con{head, rest}:
      Math.choose_bool(True{}, contains(resource, rest), Bytes.eq(resource, head))

def distinct(ids: List<&2, List<&2, Nat>>) -> Bool:
  match ids:
    case Nil{}:
      True{}
    case Con{head, +rest}:
      Bool.and(Math.not(contains(head, rest)), distinct(rest))

def valid_bid(+paymentAsset: List<&2, Nat>, +goodsAsset: List<&2, Nat>, bid: Bid) -> Bool:
  match bid:
    case Bid{Seller.Order{+subject, reservation, price, quantity},
        Account{fundResource, fundRoot, fundOwner, fundAsset, fundField, funds},
        Account{goodsResource, goodsRoot, goodsOwner, heldAsset, goodsField, goods},
        audience, keyEpoch}:
      Bool.and(Bytes.eq(subject, fundOwner),
        Bool.and(Bytes.eq(subject, goodsOwner),
          Bool.and(Bytes.eq(reservation, fundResource),
            Bool.and(Bytes.eq(paymentAsset, fundAsset),
              Bool.and(Bytes.eq(goodsAsset, heldAsset),
                Math.le(Math.mul(price, quantity), funds))))))

def valid_bids(+paymentAsset: List<&2, Nat>, +goodsAsset: List<&2, Nat>,
    bids: List<&2, Bid>) -> Bool:
  match bids:
    case Nil{}:
      True{}
    case Con{bid, rest}:
      Bool.and(valid_bid(paymentAsset, goodsAsset, bid), valid_bids(paymentAsset, goodsAsset, rest))

def write(account: Account, after: Nat) -> BalanceWrite:
  match account:
    case Account{resource, root, owner, asset, field, before}:
      BalanceWrite{resource, root, field, before, after}

def units_at(+position: Nat, fills: List<&2, Seller.Fill>) -> Nat:
  match fills:
    case Nil{}:
      0n
    case Con{Seller.Fill{otherPosition, subject, reservation, units}, rest}:
      Math.choose_nat(units, units_at(position, rest), Nat.eq(position, otherPosition))

def append_bid(funds: Account, goods: Account, result: PrivateResult, batch: Batch) -> Batch:
  match funds goods result batch:
    case Account{fundResource, fundRoot, fundOwner, fundAsset, fundField, fundBefore}
        Account{goodsResource, goodsRoot, goodsOwner, goodsAsset, goodsField, +goodsBefore}
        PrivateResult{recipient, audience, keyEpoch, reservation, +units, price, +payment, +unspent}
        Batch{writes, returns, proceeds}:
      Batch{Con{BalanceWrite{fundResource, fundRoot, fundField, fundBefore, unspent},
        Con{BalanceWrite{goodsResource, goodsRoot, goodsField, goodsBefore,
          Math.add(goodsBefore, units)}, writes}},
        Con{PrivateResult{recipient, audience, keyEpoch, reservation, units, price, payment, unspent}, returns},
        Math.add(payment, proceeds)}

def bid_result(bid: Bid, +price: Nat, +units: Nat) -> PrivateResult:
  match bid:
    case Bid{Seller.Order{subject, reservation, limit, quantity},
        Account{resource, root, owner, asset, field, funds}, goods, audience, keyEpoch}:
      +payment = Math.mul(price, units)
      PrivateResult{subject, audience, keyEpoch, reservation, units, price, payment, Math.sub(funds, payment)}

def bid_batch(bids: List<&2, Bid>, +fills: List<&2, Seller.Fill>, +price: Nat, +position: Nat) -> Batch:
  match bids:
    case Nil{}:
      Batch{Nil{}, Nil{}, 0n}
    case Con{+bid, rest}:
      match bid:
        case Bid{order, funds, goods, audience, keyEpoch}:
          append_bid(funds, goods, bid_result(bid, price, units_at(position, fills)),
            bid_batch(rest, fills, price, Succ{position}))

# Post-computation validation is a fail-closed guard while price/order fairness
# proofs are joined. It cannot substitute for source derivation of the allocation.
def backed_results(bids: List<&2, Bid>, +fills: List<&2, Seller.Fill>, +price: Nat, +position: Nat) -> Bool:
  match bids:
    case Nil{}:
      True{}
    case Con{Bid{Seller.Order{subject, reservation, +limit, +quantity},
        Account{resource, root, owner, asset, field, funds}, goods, audience, keyEpoch}, rest}:
      +units = units_at(position, fills)
      Bool.and(Math.le(units, quantity),
        Bool.and(Math.le(Math.mul(price, units), funds),
          Bool.and(Math.choose_bool(True{}, Math.le(price, limit), Nat.eq(units, 0n)),
            backed_results(rest, fills, price, Succ{position}))))

def prepare_batch(stock: Account, proceeds: Account, +allocation: Seller.Allocation,
    batch: Batch, allowed: Bool) -> Result:
  match stock proceeds allocation batch allowed:
    case stock proceeds allocation batch False{}:
      Refused{}
    case stock Account{resource, root, owner, asset, field, +balance}
        Seller.Allocation{price, fills, remaining} Batch{writes, returns, payments} True{}:
      Prepared{Con{write(stock, remaining),
        Con{BalanceWrite{resource, root, field, balance, Math.add(balance, payments)}, writes}},
        returns, allocation}

def prepare_allocation(stock: Account, proceeds: Account, +bids: List<&2, Bid>,
    +allocation: Seller.Allocation, valid: Bool) -> Result:
  match allocation:
    case Seller.Allocation{+price, +fills, remaining}:
      prepare_batch(stock, proceeds, allocation, bid_batch(bids, fills, price, 0n),
        Bool.and(valid, backed_results(bids, fills, price, 0n)))

def settle(+stock: Account, +proceeds: Account, +bids: List<&2, Bid>) -> Result:
  match stock proceeds:
    case Account{stockResource, stockRoot, +seller, +goodsAsset, stockField, supply}
        Account{proceedsResource, proceedsRoot, proceedsOwner, +paymentAsset, proceedsField, balance}:
      prepare_allocation(stock, proceeds, bids, Seller.allocate(supply, order_list(bids)),
        Bool.and(Bytes.eq(seller, proceedsOwner),
          Bool.and(distinct(Con{stockResource, Con{proceedsResource, identifiers(bids)}}),
            valid_bids(paymentAsset, goodsAsset, bids))))

# Every write retains its sampled resource/root/field/exact preimage.
def ExactWrite(before: Account, result: BalanceWrite) -> Type:
  match before result:
    case Account{resource, root, owner, asset, field, balance}
        BalanceWrite{chosen, expectedRoot, chosenField, expectedBalance, after}:
      Pair({chosen == resource : List<&2, Nat>},
        Pair({expectedRoot == root : List<&2, Nat>},
          Pair({chosenField == field : Nat}, {expectedBalance == balance : Nat})))

law write_bound:
  for +before: Account
  for after: Nat
  ExactWrite(before, write(before, after))

def write_bound(before, after):
  match before:
    case Account{resource, root, owner, asset, field, balance}:
      ({==}, ({==}, ({==}, {==})))

