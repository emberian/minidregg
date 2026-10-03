# One real two-sided DrEX source clearing, through the same generic native ABI.
import Base
import ./DrEXSettlementPlan.bend as Plan
import ./CanonicalSettlementPlan.bend as Bridge
import ./CanonicalUniformSettlement.bend as DrEX
import ./CanonicalBookSettlement.bend as Book
import ./UniformProRata.bend as Uniform
import ./WorldPlanMoney.bend as World
import ./WorldPlanScalarBytes.bend as Scalar

def id(value: Nat) -> List<&2, Nat>:
  Con{value, Con{255n, Nil{}}}

def context() -> Bridge.Context:
  Bridge.Context{Scalar.Ref{id(9n), id(17n)}, 0n,
    Bridge.Table{Con{Bridge.Binding{0n, id(10n)}, Con{Bridge.Binding{1n, id(20n)},
      Con{Bridge.Binding{2n, id(30n)}, Nil{}}}},
      Con{Bridge.Binding{0n, id(7n)}, Con{Bridge.Binding{1n, id(8n)}, Nil{}}}},
    Scalar.Ref{id(11n), id(18n)}, 0n, Nil{}, id(21n), id(22n), 0n}

def input(+recipient: List<&2, Nat>, +audience: List<&2, Nat>,
    +epoch: List<&2, Nat>, levels: Nat) -> DrEX.Input:
  DrEX.Input{0n, id(17n), Book.Account{0n, 1n, 0n}, Book.Account{0n, 0n, 0n}, levels,
    Con{DrEX.Participant{Uniform.Order{recipient, Con{31n, Nil{}}, Uniform.Bid{}, 5n, 3n},
      Book.Account{1n, 1n, 15n}, Book.Account{1n, 0n, 0n}, audience, epoch},
      Con{DrEX.Participant{Uniform.Order{recipient, Con{32n, Nil{}}, Uniform.Ask{}, 2n, 3n},
        Book.Account{2n, 1n, 0n}, Book.Account{2n, 0n, 3n}, audience, epoch}, Nil{}}}}

def operations(result: World.PlanResult) -> List<&2, World.Transfer>:
  match result:
    case World.Refused{reason}: Nil{}
    case World.Planned{World.NativePlan{book, operations, reads, effects, returns}}:
      operations

law actual_uniform_collects_then_distributes:
  for recipient: List<&2, Nat>
  for audience: List<&2, Nat>
  for epoch: List<&2, Nat>
  {operations(Plan.settle(context(), input(recipient, audience, epoch, 6n))) ==
    Con{World.Transfer{id(20n), id(10n), id(8n), 6n},
      Con{World.Transfer{id(30n), id(10n), id(7n), 3n},
        Con{World.Transfer{id(10n), id(20n), id(7n), 3n},
          Con{World.Transfer{id(10n), id(30n), id(8n), 6n}, Nil{}}}}} : List<&2, World.Transfer>}
def actual_uniform_collects_then_distributes(recipient, audience, epoch):
  {==}

law invalid_grid_never_plans:
  for recipient: List<&2, Nat>
  for audience: List<&2, Nat>
  for epoch: List<&2, Nat>
  {Plan.settle(context(), input(recipient, audience, epoch, 0n)) ==
    World.Refused{0n} : World.PlanResult}
def invalid_grid_never_plans(recipient, audience, epoch):
  {==}

law side_encoding_bid:
  {Plan.side_byte(Uniform.Bid{}) == 0n : Nat}
def side_encoding_bid():
  {==}

law side_encoding_ask:
  {Plan.side_byte(Uniform.Ask{}) == 1n : Nat}
def side_encoding_ask():
  {==}
