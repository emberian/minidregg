# Exact structural naturals; no f64 tolerance, host overflow or worker-selected grid.
import Base

def add(a: Nat, b: Nat) -> Nat:
  match a:
    case 0n:
      b
    case 1n+p:
      Succ{add(p, b)}

def sub(a: Nat, b: Nat) -> Nat:
  match a b:
    case a 0n:
      a
    case 0n 1n+q:
      0n
    case 1n+p 1n+q:
      sub(p, q)

def le(a: Nat, b: Nat) -> Bool:
  match a b:
    case 0n b:
      True{}
    case 1n+p 0n:
      False{}
    case 1n+p 1n+q:
      le(p, q)

def lt(a: Nat, b: Nat) -> Bool:
  le(Succ{a}, b)

def choose_nat(a: Nat, b: Nat, choose: Bool) -> Nat:
  match choose:
    case True{}:
      a
    case False{}:
      b

def choose_bool(a: Bool, b: Bool, choose: Bool) -> Bool:
  match choose:
    case True{}:
      a
    case False{}:
      b

def min(a: Nat, b: Nat) -> Nat:
  match a b:
    case 0n b:
      0n
    case 1n+p 0n:
      0n
    case 1n+p 1n+q:
      Succ{min(p, q)}

def mul(a: Nat, +b: Nat) -> Nat:
  match a:
    case 0n:
      0n
    case 1n+p:
      add(b, mul(p, b))

def not(b: Bool) -> Bool:
  match b:
    case False{}:
      True{}
    case True{}:
      False{}

# Euclidean division by a positive divisor, structurally recursing on numerator.
# count is the current remainder, always below divisor for divide's initialization.
type Division is Data:
  Division{quotient: Nat, remainder: Nat}

def increment_quotient(result: Division, increment: Bool) -> Division:
  match result increment:
    case Division{quotient, remainder} False{}:
      Division{quotient, remainder}
    case Division{quotient, remainder} True{}:
      Division{Succ{quotient}, remainder}

def divide_step(n: Nat, +divisor: Nat, count: Nat) -> Division:
  match n:
    case 0n:
      Division{0n, count}
    case 1n+p:
      +next = {Succ{count} : Nat}
      +reset = Nat.eq(next, divisor)
      increment_quotient(divide_step(p, divisor, choose_nat(0n, next, reset)), reset)

def divide(n: Nat, divisor: Nat) -> Division:
  match divisor:
    case 0n:
      Division{0n, n}
    case 1n+p:
      divide_step(n, Succ{p}, 0n)

law add_zero:
  for n: Nat
  {add(0n, n) == n : Nat}

def add_zero(n):
  {==}

law sub_zero:
  for +n: Nat
  {sub(n, 0n) == n : Nat}

def sub_zero(n):
  match n:
    case 0n:
      {==}
    case 1n+p:
      {==}

# The executable bounded take conserves the stock for every natural input.
law min_balance:
  for +quantity: Nat
  for +supply: Nat
  {add(min(quantity, supply), sub(supply, min(quantity, supply))) == supply : Nat}

def min_balance(quantity, supply):
  match quantity supply:
    case 0n supply:
      sub_zero(supply)
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      %min_balance(p, q) :
        {Succ{add(min(p, q), sub(q, min(p, q)))} == Succ{_} : Nat}
      {==}
