# Distinct DrEX integer-pro-rata program, sharing the canonical money Plan ABI.
# This is not the single-seller pricing rule. Its exact source identity and
# side-indexed return schema must be retained by the admitted method profile.
import Base
import ./CanonicalSettlementPlan.bend as Plan
import ./CanonicalUniformSettlement.bend as DrEX
import ./UniformProRata.bend as Uniform
import ./WorldPlanMoney.bend as World
import ./WorldPlanScalarBytes.bend as Scalar

def side_byte(side: Uniform.Side) -> Nat:
  match side:
    case Uniform.Bid{}: 0n
    case Uniform.Ask{}: 1n

# Side byte, length-framed reservation, units, uniform price, payment, unspent.
def returns(values: List<&2, DrEX.PrivateResult>, +schema: List<&2, Nat>,
    +encoding: List<&2, Nat>, +generation: Nat, +ordinal: Nat) -> List<&2, World.ReturnSlot>:
  match values:
    case Nil{}: Nil{}
    case Con{DrEX.PrivateResult{recipient, audience, epoch, reservation, side,
        price, units, payment, unspent}, rest}:
      Con{World.ReturnSlot{Plan.slot_name(ordinal), schema, encoding, recipient, epoch,
        audience, generation, Con{side_byte(side),
          Plan.payload(reservation, units, price, payment, unspent)}},
        returns(rest, schema, encoding, generation, Succ{ordinal})}

def from_result(context: Plan.Context, result: DrEX.Result) -> World.PlanResult:
  match context result:
    case context DrEX.Refused{}: World.Refused{0n}
    case Plan.Context{Scalar.Ref{bookBytes, +root}, +bookToken,
        Plan.Table{+accounts, +assets}, room, field, reads, schema, encoding, generation}
        DrEX.Prepared{book, expectedRoot, operations, values, clearing}:
      Plan.finish(Scalar.Ref{bookBytes, root}, room, field, reads,
        returns(values, schema, encoding, generation, 0n),
        Plan.transfers(operations, Plan.Table{accounts, assets}),
        Bool.and(Nat.eq(bookToken, book), Bool.and(Bytes.eq(root, expectedRoot),
          Bool.and(Plan.distinct(accounts), Plan.distinct(assets)))))

def settle(context: Plan.Context, input: DrEX.Input) -> World.PlanResult:
  from_result(context, DrEX.settle(input))

law refused_rule_inert:
  for context: Plan.Context
  {from_result(context, DrEX.Refused{}) == World.Refused{0n} : World.PlanResult}
def refused_rule_inert(context):
  match context:
    case Plan.Context{Scalar.Ref{book, root}, token, Plan.Table{accounts, assets},
        room, field, reads, schema, encoding, generation}:
      {==}

law bid_ask_distinct:
  {side_byte(Uniform.Bid{}) == 0n : Nat}
def bid_ask_distinct():
  {==}
