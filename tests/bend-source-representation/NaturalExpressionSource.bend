import Base

def SourceNat.doubleSum(+a: Nat, +b: Nat) -> Nat:
  Nat.add(Nat.add(a, b), Nat.add(a, b))
