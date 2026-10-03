import Base
import ./NaturalHelper.bend as Math

def combine(+a: Nat, +b: Nat) -> Nat:
  Math.plus(Math.plus(a, b), a)
