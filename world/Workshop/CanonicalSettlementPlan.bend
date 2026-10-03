# Actual settlement result -> generic native money Plan. Neither operations nor
# return values are caller-authored; settle invokes the existing source rule.
# The native input binder constructs Table and all account balances together
# from the SAME after-funding SampledFunding token before source execution.
import Base
import ./MarketMath.bend as Math
import ./CanonicalBookSettlement.bend as Book
import ./SharedBookSettlement.bend as Shared
import ./WorldPlanMoney.bend as World
import ./WorldPlanScalarBytes.bend as Scalar

type Binding is Data:
  Binding{token: Nat, native: List<&2, Nat>}
type Table is Data:
  Table{accounts: List<&2, Binding>, assets: List<&2, Binding>}
type Lookup is Data:
  Missing{}
  Found{native: List<&2, Nat>}
type Transfers is Data:
  MissingTransfer{}
  Resolved{operations: List<&2, World.Transfer>}

type Context is Data:
  Context{book: Scalar.Ref, bookToken: Nat, table: Table,
    room: Scalar.Ref, settledField: Nat, reads: List<&2, Scalar.Ref>,
    valueSchema: List<&2, Nat>, encoding: List<&2, Nat>, generation: Nat}

def lookup_choose(native: List<&2, Nat>, rest: Lookup, same: Bool) -> Lookup:
  match same:
    case False{}: rest
    case True{}: Found{native}

def lookup(+token: Nat, bindings: List<&2, Binding>) -> Lookup:
  match bindings:
    case Nil{}:
      Missing{}
    case Con{Binding{other, native}, rest}:
      lookup_choose(native, lookup(token, rest), Nat.eq(token, other))

def clashes(+head: Binding, bindings: List<&2, Binding>) -> Bool:
  match head bindings:
    case Binding{token, native} Nil{}: False{}
    case Binding{+token, +native} Con{Binding{other, bytes}, rest}:
      Math.choose_bool(True{}, clashes(Binding{token, native}, rest),
        Math.not(Bool.and(Math.not(Nat.eq(token, other)), Math.not(Bytes.eq(native, bytes)))))

# A table is injective in both directions. Native producer uses first-occurrence
# ordinals; source refuses duplicate/conflicting identities even before decoding.
def distinct(bindings: List<&2, Binding>) -> Bool:
  match bindings:
    case Nil{}: True{}
    case Con{head, +rest}:
      Bool.and(Math.not(clashes(head, rest)), distinct(rest))

def cons_transfer(source: Lookup, destination: Lookup, asset: Lookup,
    amount: Nat, remaining: Transfers) -> Transfers:
  match source destination asset remaining:
    case Found{source} Found{destination} Found{asset} Resolved{rest}:
      Resolved{Con{World.Transfer{source, destination, asset, amount}, rest}}
    case source destination asset remaining:
      MissingTransfer{}

def transfers(operations: List<&2, Book.Transfer>, +table: Table) -> Transfers:
  match operations table:
    case Nil{} table: Resolved{Nil{}}
    case Con{Book.Transfer{source, destination, asset, amount}, rest}
        Table{+accounts, +assets}:
      cons_transfer(lookup(source, accounts), lookup(destination, accounts),
        lookup(asset, assets), amount, transfers(rest, Table{accounts, assets}))

def append(left: List<&2, Nat>, right: List<&2, Nat>) -> List<&2, Nat>:
  match left:
    case Nil{}: right
    case Con{head, rest}: Con{head, append(rest, right)}

def length(bytes: List<&2, Nat>) -> Nat:
  match bytes:
    case Nil{}: 0n
    case Con{head, rest}: Succ{length(rest)}

# Canonical base-255 little-endian digits, terminator 255. Fuel is the original
# number and decreases structurally; production compact arithmetic refinement
# remains a compiler obligation, not a machine-width truncation here.
def digits(fuel: Nat, division: Math.Division) -> List<&2, Nat>:
  match fuel division:
    case 0n division: Nil{}
    case 1n+fuel Math.Division{0n, remainder}: Con{remainder, Nil{}}
    case 1n+fuel Math.Division{1n+quotient, remainder}:
      Con{remainder, digits(fuel, Math.divide(Succ{quotient}, 255n))}

def encode_nat(+value: Nat) -> List<&2, Nat>:
  match value:
    case 0n: Con{255n, Nil{}}
    case 1n+pred:
      append(digits(Succ{pred}, Math.divide(Succ{pred}, 255n)), Con{255n, Nil{}})

def encode_bytes(+bytes: List<&2, Nat>) -> List<&2, Nat>:
  append(encode_nat(length(bytes)), bytes)

# The named source profile fixes this exact return schema and encoding.
# Reservation is length-framed, followed by units, clearing price, paid amount,
# and the rule-specific remaining reservation/budget. No ciphertext claim.
def payload(reservation: List<&2, Nat>, units: Nat, price: Nat,
    payment: Nat, unspent: Nat) -> List<&2, Nat>:
  append(encode_bytes(reservation), append(encode_nat(units),
    append(encode_nat(price), append(encode_nat(payment), encode_nat(unspent)))))

def suffix(ordinal: Nat) -> List<&2, Nat>:
  match ordinal:
    case 0n: Nil{}
    case 1n+pred: Con{120n, suffix(pred)}

# ASCII "r/" followed by x repeated ordinal times is valid and unique.
def slot_name(ordinal: Nat) -> List<&2, Nat>:
  Con{114n, Con{47n, suffix(ordinal)}}

def book_returns(returns: List<&2, Book.PrivateResult>, +schema: List<&2, Nat>,
    +encoding: List<&2, Nat>, +generation: Nat, +ordinal: Nat) -> List<&2, World.ReturnSlot>:
  match returns:
    case Nil{}: Nil{}
    case Con{Book.PrivateResult{recipient, audience, epoch, reservation,
        units, price, payment, unspent}, rest}:
      Con{World.ReturnSlot{slot_name(ordinal), schema, encoding, recipient,
        epoch, audience, generation, payload(reservation, units, price, payment, unspent)},
        book_returns(rest, schema, encoding, generation, Succ{ordinal})}

def shared_returns(returns: List<&2, Shared.PrivateResult>, +schema: List<&2, Nat>,
    +encoding: List<&2, Nat>, +generation: Nat, +ordinal: Nat) -> List<&2, World.ReturnSlot>:
  match returns:
    case Nil{}: Nil{}
    case Con{Shared.PrivateResult{recipient, audience, epoch, reservation, reservedBudget,
        units, price, payment, unspent}, rest}:
      Con{World.ReturnSlot{slot_name(ordinal), schema, encoding, recipient,
        epoch, audience, generation, append(encode_nat(reservedBudget),
          payload(reservation, units, price, payment, unspent))},
        shared_returns(rest, schema, encoding, generation, Succ{ordinal})}

def finish(book: Scalar.Ref, room: Scalar.Ref, field: Nat,
    reads: List<&2, Scalar.Ref>, returns: List<&2, World.ReturnSlot>,
    operations: Transfers, valid: Bool) -> World.PlanResult:
  match operations valid:
    case Resolved{operations} True{}:
      World.Planned{World.NativePlan{book, operations, reads,
        Con{Scalar.ScalarEffect{room, Con{Scalar.Write{field, 0n, 1n}, Nil{}}}, Nil{}}, returns}}
    case operations valid: World.Refused{1n}

def from_book(context: Context, result: Book.Result) -> World.PlanResult:
  match context result:
    case context Book.Refused{}: World.Refused{0n}
    case Context{Scalar.Ref{bookBytes, +root}, +bookToken, Table{+accounts, +assets},
        room, field, reads, schema, encoding, generation}
        Book.Prepared{book, expectedRoot, operations, returns, allocation}:
      finish(Scalar.Ref{bookBytes, root}, room, field, reads,
        book_returns(returns, schema, encoding, generation, 0n),
        transfers(operations, Table{accounts, assets}),
        Bool.and(Nat.eq(bookToken, book), Bool.and(Bytes.eq(root, expectedRoot),
          Bool.and(distinct(accounts), distinct(assets)))))

def from_shared(context: Context, result: Shared.Result) -> World.PlanResult:
  match context result:
    case context Shared.Refused{}: World.Refused{0n}
    case Context{Scalar.Ref{bookBytes, +root}, +bookToken, Table{+accounts, +assets},
        room, field, reads, schema, encoding, generation}
        Shared.Prepared{book, expectedRoot, samples, operations, returns, allocation}:
      finish(Scalar.Ref{bookBytes, root}, room, field, reads,
        shared_returns(returns, schema, encoding, generation, 0n),
        transfers(operations, Table{accounts, assets}),
        Bool.and(Nat.eq(bookToken, book), Bool.and(Bytes.eq(root, expectedRoot),
          Bool.and(distinct(accounts), distinct(assets)))))

def settle(context: Context, input: Book.Input) -> World.PlanResult:
  from_book(context, Book.settle(input))

def settle_shared(context: Context, input: Book.Input) -> World.PlanResult:
  from_shared(context, Shared.settle(input))

law refused_book_inert:
  for context: Context
  {from_book(context, Book.Refused{}) == World.Refused{0n} : World.PlanResult}
def refused_book_inert(context):
  match context:
    case Context{Scalar.Ref{book, root}, token, Table{accounts, assets}, room, field, reads, schema, encoding, generation}:
      {==}

law refused_shared_inert:
  for context: Context
  {from_shared(context, Shared.Refused{}) == World.Refused{0n} : World.PlanResult}
def refused_shared_inert(context):
  match context:
    case Context{Scalar.Ref{book, root}, token, Table{accounts, assets}, room, field, reads, schema, encoding, generation}:
      {==}

# General constructor correspondence: no fixed account, amount, order-count or
# byte width is built into the resolution step.
law resolved_cons_exact:
  for +source: List<&2, Nat>
  for +destination: List<&2, Nat>
  for +asset: List<&2, Nat>
  for +amount: Nat
  for +remaining: List<&2, World.Transfer>
  {cons_transfer(Found{source}, Found{destination}, Found{asset}, amount,
      Resolved{remaining}) ==
    Resolved{Con{World.Transfer{source, destination, asset, amount}, remaining}} : Transfers}
def resolved_cons_exact(source, destination, asset, amount, remaining):
  {==}
