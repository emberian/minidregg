# Source-level mapping and actual shared-allocation consumer. Native sampling,
# signatures, strict root/subject codecs and receiving are separate gates.
import Base
import ./CanonicalSettlementPlan.bend as Plan
import ./CanonicalBookSettlement.bend as Book
import ./SingleSellerAllocation.bend as Seller
import ./WorldPlanMoney.bend as World
import ./WorldPlanScalarBytes.bend as Scalar

def id(value: Nat) -> List<&2, Nat>:
  Con{value, Con{255n, Nil{}}}

def table() -> Plan.Table:
  Plan.Table{
    Con{Plan.Binding{0n, id(1n)}, Con{Plan.Binding{1n, id(2n)}, Nil{}}},
    Con{Plan.Binding{0n, id(7n)}, Con{Plan.Binding{1n, id(8n)}, Nil{}}}}

def input(root: List<&2, Nat>, +recipient: List<&2, Nat>,
    +audience: List<&2, Nat>, +epoch: List<&2, Nat>, +balance: Nat) -> Book.Input:
  Book.Input{0n, root, Book.Account{0n, 0n, 7n}, Book.Account{0n, 1n, 10n},
    Con{Book.Bid{Seller.Order{recipient, Con{21n, Nil{}}, 5n, 4n},
      Book.Account{1n, 1n, balance}, Book.Account{1n, 0n, 0n}, audience, epoch},
      Con{Book.Bid{Seller.Order{recipient, Con{22n, Nil{}}, 3n, 5n},
        Book.Account{1n, 1n, balance}, Book.Account{1n, 0n, 0n}, audience, epoch}, Nil{}}}}

def context() -> Plan.Context:
  Plan.Context{Scalar.Ref{id(9n), id(17n)}, 0n, table(),
    Scalar.Ref{id(10n), id(18n)}, 0n, Nil{}, id(19n), id(20n), 0n}

def operations(result: World.PlanResult) -> List<&2, World.Transfer>:
  match result:
    case World.Refused{reason}: Nil{}
    case World.Planned{World.NativePlan{book, operations, reads, effects, returns}}:
      operations

def phase(result: World.PlanResult) -> List<&2, Scalar.ScalarEffect>:
  match result:
    case World.Refused{reason}: Nil{}
    case World.Planned{World.NativePlan{book, operations, reads, effects, returns}}:
      effects

law ordered_transfer_resolution:
  for +goods: Nat
  for +payment: Nat
  {Plan.transfers(Con{Book.Transfer{0n, 1n, 0n, goods},
      Con{Book.Transfer{1n, 0n, 1n, payment}, Nil{}}}, table()) ==
    Plan.Resolved{Con{World.Transfer{id(1n), id(2n), id(7n), goods},
      Con{World.Transfer{id(2n), id(1n), id(8n), payment}, Nil{}}}} : Plan.Transfers}
def ordered_transfer_resolution(goods, payment):
  {==}

law duplicate_tokens_refused:
  {Plan.distinct(Con{Plan.Binding{0n, id(1n)},
    Con{Plan.Binding{0n, id(2n)}, Nil{}}}) == False{} : Bool}
def duplicate_tokens_refused():
  {==}

law native_alias_split_refused:
  {Plan.distinct(Con{Plan.Binding{0n, id(1n)},
    Con{Plan.Binding{1n, id(1n)}, Nil{}}}) == False{} : Bool}
def native_alias_split_refused():
  {==}

law absent_asset_refused:
  for amount: Nat
  {Plan.transfers(Con{Book.Transfer{0n, 1n, 2n, amount}, Nil{}}, table()) ==
    Plan.MissingTransfer{} : Plan.Transfers}
def absent_asset_refused(amount):
  {==}

law actual_shared_source_operations:
  for recipient: List<&2, Nat>
  for audience: List<&2, Nat>
  for epoch: List<&2, Nat>
  {operations(Plan.settle_shared(context(), input(id(17n), recipient, audience, epoch, 35n))) ==
    Con{World.Transfer{id(1n), id(2n), id(7n), 4n},
      Con{World.Transfer{id(2n), id(1n), id(8n), 12n},
        Con{World.Transfer{id(1n), id(2n), id(7n), 3n},
          Con{World.Transfer{id(2n), id(1n), id(8n), 9n}, Nil{}}}}} : List<&2, World.Transfer>}
def actual_shared_source_operations(recipient, audience, epoch):
  {==}

law actual_shared_source_phase:
  for recipient: List<&2, Nat>
  for audience: List<&2, Nat>
  for epoch: List<&2, Nat>
  {phase(Plan.settle_shared(context(), input(id(17n), recipient, audience, epoch, 35n))) ==
    Con{Scalar.ScalarEffect{Scalar.Ref{id(10n), id(18n)},
      Con{Scalar.Write{0n, 0n, 1n}, Nil{}}}, Nil{}} : List<&2, Scalar.ScalarEffect>}
def actual_shared_source_phase(recipient, audience, epoch):
  {==}

law unaffordable_shared_has_no_plan:
  for recipient: List<&2, Nat>
  for audience: List<&2, Nat>
  for epoch: List<&2, Nat>
  {Plan.settle_shared(context(), input(id(17n), recipient, audience, epoch, 20n)) ==
    World.Refused{0n} : World.PlanResult}
def unaffordable_shared_has_no_plan(recipient, audience, epoch):
  {==}

law stale_book_has_no_plan:
  for recipient: List<&2, Nat>
  for audience: List<&2, Nat>
  for epoch: List<&2, Nat>
  {Plan.settle_shared(context(), input(id(18n), recipient, audience, epoch, 35n)) ==
    World.Refused{1n} : World.PlanResult}
def stale_book_has_no_plan(recipient, audience, epoch):
  {==}
