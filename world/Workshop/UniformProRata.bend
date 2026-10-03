# Distinct DrEX mechanism: two-sided uniform price, lowest-grid-index volume
# argmax, exact integer largest-remainder allocation, original-index tie-break.
# The complete admitted ordered book and public grid are inputs, never worker output.
import Base
import ./MarketMath.bend as Math

type Side is Data:
  Bid{}
  Ask{}

type Order is Data:
  Order{subject: List<&2, Nat>, reservation: List<&2, Nat>,
    side: Side, limit: Nat, quantity: Nat}

type Fill is Data:
  Fill{position: Nat, order: Order, units: Nat}

type Clearing is Data:
  Clearing{price: Nat, volume: Nat, fills: List<&2, Fill>}

type Result is Data:
  InvalidGrid{}
  Cleared{clearing: Clearing}

type Crossing is Data:
  Crossing{price: Nat, volume: Nat}

type Share is Data:
  Share{position: Nat, order: Order, active: Bool, floor: Nat, remainder: Nat}

def same_side(a: Side, b: Side) -> Bool:
  match a b:
    case Bid{} Bid{}:
      True{}
    case Ask{} Ask{}:
      True{}
    case Bid{} Ask{}:
      False{}
    case Ask{} Bid{}:
      False{}

def active(side: Side, limit: Nat, price: Nat) -> Bool:
  match side:
    case Bid{}:
      Math.le(price, limit)
    case Ask{}:
      Math.le(limit, price)

def total(+side: Side, +price: Nat, orders: List<&2, Order>) -> Nat:
  match orders:
    case Nil{}:
      0n
    case Con{Order{subject, reservation, +oside, limit, qty}, rest}:
      Math.add(Math.choose_nat(qty, 0n,
        Bool.and(same_side(side, oside), active(oside, limit, price))),
        total(side, price, rest))

def volume(+price: Nat, +orders: List<&2, Order>) -> Nat:
  Math.min(total(Bid{}, price, orders), total(Ask{}, price, orders))

def scan(levels: Nat, +price: Nat, +orders: List<&2, Order>,
    bestPrice: Nat, +bestVolume: Nat) -> Crossing:
  match levels:
    case 0n:
      Crossing{bestPrice, bestVolume}
    case 1n+remaining:
      +current = volume(price, orders)
      +better = Math.lt(bestVolume, current)
      scan(remaining, Succ{price}, orders,
        Math.choose_nat(price, bestPrice, better),
        Math.choose_nat(current, bestVolume, better))

def side_value(side: Side, bid: Nat, ask: Nat) -> Nat:
  match side:
    case Bid{}:
      bid
    case Ask{}:
      ask

def make_share(position: Nat, order: Order, enabled: Bool, division: Math.Division) -> Share:
  match division:
    case Math.Division{floor, remainder}:
      Share{position, order, enabled, floor, remainder}

def share_division(quantity: Nat, volume: Nat, denominator: Nat, enabled: Bool) -> Math.Division:
  match enabled:
    case True{}:
      Math.divide(Math.mul(quantity, volume), denominator)
    case False{}:
      Math.Division{0n, 0n}

def shares(+price: Nat, +volume: Nat, +bidTotal: Nat, +askTotal: Nat,
    orders: List<&2, Order>, +position: Nat) -> List<&2, Share>:
  match orders:
    case Nil{}:
      Nil{}
    case Con{+order, rest}:
      match order:
        case Order{subject, reservation, +side, limit, quantity}:
          +enabled = active(side, limit, price)
          Con{make_share(position, order, enabled,
            share_division(quantity, volume, side_value(side, bidTotal, askTotal), enabled)),
            shares(price, volume, bidTotal, askTotal, rest, Succ{position})}

def floors(+side: Side, entries: List<&2, Share>) -> Nat:
  match entries:
    case Nil{}:
      0n
    case Con{Share{position, Order{subject, reservation, oside, limit, qty},
        enabled, floor, remainder}, rest}:
      Math.add(Math.choose_nat(floor, 0n, same_side(side, oside)), floors(side, rest))

# Number of active same-side entries with strictly better remainder/index.
# Deriving rank from the complete book prevents a certificate-selected tie order.
def rank(+side: Side, +position: Nat, +remainder: Nat, entries: List<&2, Share>) -> Nat:
  match entries:
    case Nil{}:
      0n
    case Con{Share{+otherPosition, Order{subject, reservation, otherSide, limit, qty},
        enabled, floor, +otherRemainder}, rest}:
      +better = Math.choose_bool(Math.lt(otherPosition, position),
        Math.lt(remainder, otherRemainder), Nat.eq(remainder, otherRemainder))
      Math.add(Math.choose_nat(1n, 0n,
        Bool.and(enabled, Bool.and(same_side(side, otherSide), better))),
        rank(side, position, remainder, rest))

def finish(entries: List<&2, Share>, +all: List<&2, Share>,
    +bidBonus: Nat, +askBonus: Nat) -> List<&2, Fill>:
  match entries:
    case Nil{}:
      Nil{}
    case Con{Share{+position, +order, enabled, +floor, remainder}, rest}:
      match order:
        case Order{subject, reservation, +side, limit, qty}:
          +bonus = side_value(side, bidBonus, askBonus)
          +units = Math.choose_nat(Succ{floor}, floor,
            Bool.and(enabled, Math.lt(rank(side, position, remainder, all), bonus)))
          Con{Fill{position, order, units}, finish(rest, all, bidBonus, askBonus)}

def clear(+orders: List<&2, Order>, crossing: Crossing) -> Result:
  match crossing:
    case Crossing{+price, +vol}:
      +entries = shares(price, vol, total(Bid{}, price, orders),
        total(Ask{}, price, orders), orders, 0n)
      Cleared{Clearing{price, vol, finish(entries, entries,
        Math.sub(vol, floors(Bid{}, entries)), Math.sub(vol, floors(Ask{}, entries)))}}

def allocate(levels: Nat, +orders: List<&2, Order>) -> Result:
  match levels:
    case 0n:
      InvalidGrid{}
    case 1n+remaining:
      clear(orders, scan(Succ{remaining}, 0n, orders, 0n, 0n))

law invalid_grid_refused:
  for orders: List<&2, Order>
  {allocate(0n, orders) == InvalidGrid{} : Result}

def invalid_grid_refused(orders):
  {==}

