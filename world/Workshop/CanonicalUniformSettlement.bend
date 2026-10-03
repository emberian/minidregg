# Two-sided DrEX source consumer over the SAME canonical book contract.
# Collect all admitted debits, then distribute from the two clearing pools.
# Pool coordinates are distinct from each participant coordinate; same-account
# different-asset coordinates are supported. Pools finish at their pre-balances
# when the checked per-side totals equal the computed clearing volume.
import Base
import ./MarketMath.bend as Math
import ./UniformProRata.bend as Uniform
import ./CanonicalBookSettlement.bend as Book

type Participant is Data:
  Participant{order: Uniform.Order, funds: Book.Account, goods: Book.Account,
    audience: List<&2, Nat>, keyEpoch: List<&2, Nat>}

type Input is Data:
  Input{book: Nat, root: List<&2, Nat>, currencyPool: Book.Account, goodsPool: Book.Account,
    levels: Nat, participants: List<&2, Participant>}

type PrivateResult is Data:
  PrivateResult{recipient: List<&2, Nat>, audience: List<&2, Nat>, keyEpoch: List<&2, Nat>,
    reservation: List<&2, Nat>, side: Uniform.Side, price: Nat, units: Nat,
    payment: Nat, unspentReserved: Nat}

type Result is Data:
  Refused{}
  Prepared{book: Nat, expectedRoot: List<&2, Nat>, operations: List<&2, Book.Transfer>,
    returns: List<&2, PrivateResult>, clearing: Uniform.Clearing}

def orders(participants: List<&2, Participant>) -> List<&2, Uniform.Order>:
  match participants:
    case Nil{}:
      Nil{}
    case Con{Participant{order, funds, goods, audience, keyEpoch}, rest}:
      Con{order, orders(rest)}

def coordinates(participants: List<&2, Participant>) -> List<&2, Book.Coordinate>:
  match participants:
    case Nil{}:
      Nil{}
    case Con{Participant{order, funds, goods, audience, keyEpoch}, rest}:
      Con{Book.coordinate(funds), Con{Book.coordinate(goods), coordinates(rest)}}

def units_at(+position: Nat, fills: List<&2, Uniform.Fill>) -> Nat:
  match fills:
    case Nil{}:
      0n
    case Con{Uniform.Fill{otherPosition, order, units}, rest}:
      Math.choose_nat(units, units_at(position, rest), Nat.eq(position, otherPosition))

def side_valid(side: Uniform.Side, +limit: Nat, +quantity: Nat,
    +price: Nat, +units: Nat, +funds: Nat, +goods: Nat) -> Bool:
  match side:
    case Uniform.Bid{}:
      Bool.and(Math.le(Math.mul(limit, quantity), funds),
        Bool.and(Math.le(Math.mul(price, units), funds),
          Math.choose_bool(True{}, Math.le(price, limit), Nat.eq(units, 0n))))
    case Uniform.Ask{}:
      Bool.and(Math.le(quantity, goods),
        Bool.and(Math.le(units, goods),
          Math.choose_bool(True{}, Math.le(limit, price), Nat.eq(units, 0n))))

def valid_participants(participants: List<&2, Participant>, +fills: List<&2, Uniform.Fill>,
    +paymentAsset: Nat, +goodsAsset: Nat, +price: Nat, +position: Nat) -> Bool:
  match participants:
    case Nil{}:
      True{}
    case Con{Participant{Uniform.Order{subject, reservation, side, limit, +quantity},
        Book.Account{fundsId, fundsAsset, funds}, Book.Account{goodsId, heldAsset, goods},
        audience, keyEpoch}, rest}:
      +units = units_at(position, fills)
      Bool.and(Nat.eq(paymentAsset, fundsAsset),
        Bool.and(Nat.eq(goodsAsset, heldAsset),
          Bool.and(Math.le(units, quantity),
            Bool.and(side_valid(side, limit, quantity, price, units, funds, goods),
              valid_participants(rest, fills, paymentAsset, goodsAsset, price, Succ{position})))))

def side_total(+side: Uniform.Side, fills: List<&2, Uniform.Fill>) -> Nat:
  match fills:
    case Nil{}:
      0n
    case Con{Uniform.Fill{position, Uniform.Order{subject, reservation, otherSide, limit, quantity},
        units}, rest}:
      Math.add(Math.choose_nat(units, 0n, Uniform.same_side(side, otherSide)), side_total(side, rest))

def transfer_for(side: Uniform.Side, collect: Bool,
    currencyPool: Nat, goodsPool: Nat, funds: Nat, goods: Nat,
    paymentAsset: Nat, goodsAsset: Nat, price: Nat, units: Nat) -> Book.Transfer:
  match side collect:
    case Uniform.Bid{} True{}:
      Book.Transfer{funds, currencyPool, paymentAsset, Math.mul(price, units)}
    case Uniform.Ask{} True{}:
      Book.Transfer{goods, goodsPool, goodsAsset, units}
    case Uniform.Bid{} False{}:
      Book.Transfer{goodsPool, goods, goodsAsset, units}
    case Uniform.Ask{} False{}:
      Book.Transfer{currencyPool, funds, paymentAsset, Math.mul(price, units)}

def transfers(participants: List<&2, Participant>, +fills: List<&2, Uniform.Fill>,
    +currencyPool: Nat, +goodsPool: Nat, +paymentAsset: Nat, +goodsAsset: Nat,
    +price: Nat, +position: Nat, +collect: Bool) -> List<&2, Book.Transfer>:
  match participants:
    case Nil{}:
      Nil{}
    case Con{Participant{Uniform.Order{subject, reservation, side, limit, quantity},
        Book.Account{funds, fundsAsset, fundsBalance}, Book.Account{goods, heldAsset, goodsBalance},
        audience, keyEpoch}, rest}:
      Con{transfer_for(side, collect, currencyPool, goodsPool, funds, goods,
        paymentAsset, goodsAsset, price, units_at(position, fills)),
        transfers(rest, fills, currencyPool, goodsPool, paymentAsset, goodsAsset,
          price, Succ{position}, collect)}

def append(left: List<&2, Book.Transfer>, right: List<&2, Book.Transfer>) -> List<&2, Book.Transfer>:
  match left:
    case Nil{}:
      right
    case Con{head, rest}:
      Con{head, append(rest, right)}

def remaining(side: Uniform.Side, funds: Nat, goods: Nat, price: Nat, units: Nat) -> Nat:
  match side:
    case Uniform.Bid{}:
      Math.sub(funds, Math.mul(price, units))
    case Uniform.Ask{}:
      Math.sub(goods, units)

def returns(participants: List<&2, Participant>, +fills: List<&2, Uniform.Fill>,
    +price: Nat, +position: Nat) -> List<&2, PrivateResult>:
  match participants:
    case Nil{}:
      Nil{}
    case Con{Participant{Uniform.Order{subject, reservation, +side, limit, quantity},
        Book.Account{fundsId, fundsAsset, funds}, Book.Account{goodsId, heldAsset, goods},
        audience, keyEpoch}, rest}:
      +units = units_at(position, fills)
      Con{PrivateResult{subject, audience, keyEpoch, reservation, side, price, units,
        Math.mul(price, units), remaining(side, funds, goods, price, units)},
        returns(rest, fills, price, Succ{position})}

def choose(book: Nat, root: List<&2, Nat>, operations: List<&2, Book.Transfer>,
    returns: List<&2, PrivateResult>, clearing: Uniform.Clearing, allowed: Bool) -> Result:
  match allowed:
    case False{}:
      Refused{}
    case True{}:
      Prepared{book, root, operations, returns, clearing}

def prepare(book: Nat, root: List<&2, Nat>, +currencyPool: Book.Account, +goodsPool: Book.Account,
    +participants: List<&2, Participant>, +clearing: Uniform.Clearing) -> Result:
  match currencyPool goodsPool clearing:
    case Book.Account{+currencyId, +paymentAsset, currencyBalance}
        Book.Account{+goodsId, +goodsAsset, goodsBalance}
        Uniform.Clearing{+price, +volume, +fills}:
      choose(book, root,
        append(transfers(participants, fills, currencyId, goodsId, paymentAsset, goodsAsset, price, 0n, True{}),
          transfers(participants, fills, currencyId, goodsId, paymentAsset, goodsAsset, price, 0n, False{})),
        returns(participants, fills, price, 0n), clearing,
        Bool.and(Book.distinct(Con{Book.coordinate(currencyPool),
          Con{Book.coordinate(goodsPool), coordinates(participants)}}),
          Bool.and(Nat.eq(side_total(Uniform.Bid{}, fills), volume),
            Bool.and(Nat.eq(side_total(Uniform.Ask{}, fills), volume),
              valid_participants(participants, fills, paymentAsset, goodsAsset, price, 0n)))))

def accept(book: Nat, root: List<&2, Nat>, currencyPool: Book.Account, goodsPool: Book.Account,
    participants: List<&2, Participant>, candidate: Uniform.Result) -> Result:
  match candidate:
    case Uniform.InvalidGrid{}:
      Refused{}
    case Uniform.Cleared{clearing}:
      prepare(book, root, currencyPool, goodsPool, participants, clearing)

def settle(input: Input) -> Result:
  match input:
    case Input{book, root, currencyPool, goodsPool, levels, +participants}:
      accept(book, root, currencyPool, goodsPool, participants, Uniform.allocate(levels, orders(participants)))

# Soundness of the exact equality checker used by the accepted-output guards.
law volume_equality:
  for +bidTotal: Nat
  for +askTotal: Nat
  for +volume: Nat
  for +accepted: Truth(Bool.and(Nat.eq(bidTotal, volume), Nat.eq(askTotal, volume)))
  Pair({bidTotal == volume : Nat}, {askTotal == volume : Nat})

def volume_equality(bidTotal, askTotal, volume, accepted):
  (Nat.eq_sound(bidTotal, volume, Bool.and_left(Nat.eq(bidTotal, volume), Nat.eq(askTotal, volume), accepted)),
    Nat.eq_sound(askTotal, volume, Bool.and_right(Nat.eq(bidTotal, volume), Nat.eq(askTotal, volume), accepted)))

