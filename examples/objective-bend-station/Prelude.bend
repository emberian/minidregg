# Pure source subset of pinned bend2/base.bend: exact Nat and List declarations.
# This sealed library contains no foreign IO, opaque law or unsafe definition.
type Nat is Data:
  Zero{}
  Succ{pred: Nat}

type List<a, -A: Kind(a)> is Kind(a):
  Nil{}
  Con{head: A, tail: List<a, A>}

type Bool is Data:
  False{}
  True{}

type Empty is Data:

type Unit is Data:
  Unit{}

def Empty.absurd(-A: Type, e: Empty) -> A:
  match e:

type Sigma<a, b, -A: Kind(a), -B: @-x: A -> Kind(b)> is Kind(a <&> b):
  Tuple{fst: A, snd: B(fst)}

def Pair(-A: Type, -B: Type) -> Type:
  Sigma<&1, &1, A, _ => B>

def Nat.eq(a: Nat, b: Nat) -> Bool:
  match a b:
    case 0n 0n:
      True{}
    case 0n 1n+q:
      False{}
    case 1n+p 0n:
      False{}
    case 1n+p 1n+q:
      Nat.eq(p, q)

def Bool.and(a: Bool, b: Bool) -> Bool:
  match a:
    case False{}:
      False{}
    case True{}:
      b

def Bytes.eq(a: List<&2, Nat>, b: List<&2, Nat>) -> Bool:
  match a b:
    case Nil{} Nil{}:
      True{}
    case Nil{} Con{head, tail}:
      False{}
    case Con{head, tail} Nil{}:
      False{}
    case Con{left, more} Con{right, rest}:
      Bool.and(Nat.eq(left, right), Bytes.eq(more, rest))

def Truth(b: Bool) -> Data:
  match b:
    case False{}:
      Empty
    case True{}:
      Unit

def Bool.and_left(+a: Bool, +b: Bool, e: Truth(Bool.and(a, b))) -> Truth(a):
  match a:
    case False{}:
      Empty.absurd(Truth(False{}), e)
    case True{}:
      Unit{}

def Bool.and_right(+a: Bool, +b: Bool, e: Truth(Bool.and(a, b))) -> Truth(b):
  match a:
    case False{}:
      Empty.absurd(Truth(b), e)
    case True{}:
      e

def Nat.eq_sound(+a: Nat, +b: Nat, e: Truth(Nat.eq(a, b))) -> {a == b : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      Empty.absurd({0n == 1n+q : Nat}, e)
    case 1n+p 0n:
      Empty.absurd({1n+p == 0n : Nat}, e)
    case 1n+p 1n+q:
      %Nat.eq_sound(p, q, e) : {1n+p == 1n+_ : Nat}
      {==}

def Bytes.eq_sound(+a: List<&2, Nat>, +b: List<&2, Nat>, +e: Truth(Bytes.eq(a, b))) ->
    {a == b : List<&2, Nat>}:
  match a b:
    case Nil{} Nil{}:
      {==}
    case Nil{} Con{head, tail}:
      Empty.absurd({Nil{} == Con{head, tail} : List<&2, Nat>}, e)
    case Con{head, tail} Nil{}:
      Empty.absurd({Con{head, tail} == Nil{} : List<&2, Nat>}, e)
    case Con{+left, +more} Con{+right, +rest}:
      %Nat.eq_sound(left, right, Bool.and_left(Nat.eq(left, right), Bytes.eq(more, rest), e)) :
        {Con{left, more} == Con{_, rest} : List<&2, Nat>}
      %Bytes.eq_sound(more, rest, Bool.and_right(Nat.eq(left, right), Bytes.eq(more, rest), e)) :
        {Con{left, more} == Con{left, _} : List<&2, Nat>}
      {==}
