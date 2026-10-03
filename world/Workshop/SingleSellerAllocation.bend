# Existing Mini single-seller rule, now expressed as authored source:
# descending price, then original admitted-book order; one last-filled price.
# Every order retains its exact principal/reservation and original position.
import Base
import ./MarketMath.bend as Math

type Order is Data:
  Order{subject: List<&2, Nat>, reservation: List<&2, Nat>, price: Nat, quantity: Nat}

type Ranked is Data:
  Ranked{position: Nat, order: Order}

type Fill is Data:
  Fill{position: Nat, subject: List<&2, Nat>, reservation: List<&2, Nat>, units: Nat}

type Allocation is Data:
  Allocation{price: Nat, fills: List<&2, Fill>, remaining: Nat}

def index(orders: List<&2, Order>, +position: Nat) -> List<&2, Ranked>:
  match orders:
    case Nil{}:
      Nil{}
    case Con{order, rest}:
      Con{Ranked{position, order}, index(rest, Succ{position})}

def precedes(a: Ranked, b: Ranked) -> Bool:
  match a b:
    case Ranked{ai, Order{asubject, areservation, +aprice, aqty}}
        Ranked{bi, Order{bsubject, breservation, +bprice, bqty}}:
      Math.choose_bool(Math.le(ai, bi), Math.lt(bprice, aprice),
        Nat.eq(aprice, bprice))

def insert_choice(item: Ranked, head: Ranked, tail: List<&2, Ranked>,
    after: List<&2, Ranked>, before: Bool) -> List<&2, Ranked>:
  match before:
    case True{}:
      Con{item, Con{head, tail}}
    case False{}:
      Con{head, after}

def insert(+item: Ranked, items: List<&2, Ranked>) -> List<&2, Ranked>:
  match items:
    case Nil{}:
      Con{item, Nil{}}
    case Con{+head, +tail}:
      insert_choice(item, head, tail, insert(item, tail), precedes(item, head))

def sort(items: List<&2, Ranked>) -> List<&2, Ranked>:
  match items:
    case Nil{}:
      Nil{}
    case Con{head, tail}:
      insert(head, sort(tail))

def take(price: Nat, quantity: Nat, supply: Nat) -> Nat:
  match price:
    case 0n:
      0n
    case 1n+p:
      Math.min(quantity, supply)

def last_price(taken: Nat, old: Nat, price: Nat) -> Nat:
  match taken:
    case 0n:
      old
    case 1n+p:
      price

def prepend(position: Nat, subject: List<&2, Nat>, reservation: List<&2, Nat>,
    taken: Nat, result: Allocation) -> Allocation:
  match result:
    case Allocation{clearingPrice, fills, remaining}:
      Allocation{clearingPrice, Con{Fill{position, subject, reservation, taken}, fills}, remaining}

def fill(orders: List<&2, Ranked>, +supply: Nat, lastPrice: Nat) -> Allocation:
  match orders:
    case Nil{}:
      Allocation{lastPrice, Nil{}, supply}
    case Con{Ranked{position, Order{subject, reservation, +price, quantity}}, rest}:
      +taken = take(price, quantity, supply)
      prepend(position, subject, reservation, taken,
        fill(rest, Math.sub(supply, taken), last_price(taken, lastPrice, price)))

def allocate(supply: Nat, orders: List<&2, Order>) -> Allocation:
  fill(sort(index(orders, 0n)), supply, 0n)

law empty_preserves_supply:
  for +supply: Nat
  {allocate(supply, Nil{}) == Allocation{0n, Nil{}, supply} : Allocation}

def empty_preserves_supply(supply):
  {==}

def sum_with_remaining(fills: List<&2, Fill>, remaining: Nat) -> Nat:
  match fills:
    case Nil{}:
      remaining
    case Con{Fill{position, subject, reservation, units}, rest}:
      Math.add(units, sum_with_remaining(rest, remaining))

def accounted(result: Allocation) -> Nat:
  match result:
    case Allocation{price, fills, remaining}:
      sum_with_remaining(fills, remaining)

law take_balance:
  for +price: Nat
  for +quantity: Nat
  for +supply: Nat
  {Math.add(take(price, quantity, supply),
    Math.sub(supply, take(price, quantity, supply))) == supply : Nat}

def take_balance(price, quantity, supply):
  match price:
    case 0n:
      Math.sub_zero(supply)
    case 1n+p:
      Math.min_balance(quantity, supply)

law prepend_accounted:
  for position: Nat
  for subject: List<&2, Nat>
  for reservation: List<&2, Nat>
  for +taken: Nat
  for +result: Allocation
  {accounted(prepend(position, subject, reservation, taken, result)) ==
    Math.add(taken, accounted(result)) : Nat}

def prepend_accounted(position, subject, reservation, taken, result):
  match result:
    case Allocation{price, fills, remaining}:
      {==}

# General conservation over the actual recursive allocation, not one example.
# This does not assert price optimality or receiver authorization.
law fill_conserves:
  for +orders: List<&2, Ranked>
  for +supply: Nat
  for +lastPrice: Nat
  {accounted(fill(orders, supply, lastPrice)) == supply : Nat}

def fill_conserves(orders, supply, lastPrice):
  match orders:
    case Nil{}:
      {==}
    case Con{Ranked{+position, Order{+subject, +reservation, +price, +quantity}}, +rest}:
      +taken = take(price, quantity, supply)
      +remaining = Math.sub(supply, taken)
      +nextPrice = last_price(taken, lastPrice, price)
      %take_balance(price, quantity, supply) :
        {accounted(prepend(position, subject, reservation, taken, fill(rest, remaining, nextPrice))) == _ : Nat}
      %fill_conserves(rest, remaining, nextPrice) :
        {accounted(prepend(position, subject, reservation, taken, fill(rest, remaining, nextPrice))) ==
          Math.add(taken, _) : Nat}
      prepend_accounted(position, subject, reservation, taken, fill(rest, remaining, nextPrice))

law allocation_conserves:
  for +supply: Nat
  for orders: List<&2, Order>
  {accounted(allocate(supply, orders)) == supply : Nat}

def allocation_conserves(supply, orders):
  fill_conserves(sort(index(orders, 0n)), supply, 0n)
