# OrderedCapacity: contributed capacity, allocated by frozen request order.
# This is an ordinary Bend source module, not a kernel or a market mechanism.
# Authenticated samples supply exact canonical subject/resource/root bytes.
# A copied token reference confers no authority. World.Plan admission must still
# check the actual right, expected root, recipient, audience and current policy.
import Base

type Capacity is Data:
  Capacity{target: Nat, token: List<&2, Nat>, root: List<&2, Nat>}

type Stock is Data:
  NoStock{}
  StockItem{capacity: Capacity, rest: Stock}

type Requests is Data:
  NoRequests{}
  Request{subject: List<&2, Nat>, units: Nat, rest: Requests}

type Grants is Data:
  NoGrants{}
  Grant{subject: List<&2, Nat>, stock: Stock, rest: Grants}

def join(xs: Stock, ys: Stock) -> Stock:
  match xs:
    case NoStock{}:
      ys
    case StockItem{capacity, rest}:
      StockItem{capacity, join(rest, ys)}

def prefix(n: Nat, xs: Stock) -> Stock:
  match n xs:
    case 0n xs:
      NoStock{}
    case 1n+p NoStock{}:
      NoStock{}
    case 1n+p StockItem{capacity, rest}:
      StockItem{capacity, prefix(p, rest)}

def suffix(n: Nat, xs: Stock) -> Stock:
  match n xs:
    case 0n xs:
      xs
    case 1n+p NoStock{}:
      NoStock{}
    case 1n+p StockItem{capacity, rest}:
      suffix(p, rest)

# A zero/exhausted request still has its own empty grant, in the same position.
# No member, demand or request is silently dropped; ties use this frozen order.
def allocate(requests: Requests, +stock: Stock) -> Grants:
  match requests:
    case NoRequests{}:
      NoGrants{}
    case Request{subject, +units, rest}:
      Grant{subject, prefix(units, stock), allocate(rest, suffix(units, stock))}

def allocate_from_stock(+stock: Stock, requests: Requests) -> Grants:
  allocate(requests, stock)

def remaining(requests: Requests, stock: Stock) -> Stock:
  match requests:
    case NoRequests{}:
      stock
    case Request{subject, units, rest}:
      remaining(rest, suffix(units, stock))

def assigned(grants: Grants) -> Stock:
  match grants:
    case NoGrants{}:
      NoStock{}
    case Grant{subject, stock, rest}:
      join(stock, assigned(rest))

# Exact token conservation includes every reference byte and token order, not
# only a quantity sum. It implies no loss/duplication for unique input tokens.
law split_conserves:
  for +n: Nat
  for +stock: Stock
  {join(prefix(n, stock), suffix(n, stock)) == stock : Stock}

law allocation_conserves:
  for +requests: Requests
  for +stock: Stock
  {join(assigned(allocate(requests, stock)), remaining(requests, stock)) == stock : Stock}

law allocation_policy:
  for +subject: List<&2, Nat>
  for +units: Nat
  for +rest: Requests
  for +stock: Stock
  {allocate(Request{subject, units, rest}, stock) ==
    Grant{subject, prefix(units, stock), allocate(rest, suffix(units, stock))} : Grants}

def join_assoc(+xs: Stock, +ys: Stock, +zs: Stock) ->
    {join(join(xs, ys), zs) == join(xs, join(ys, zs)) : Stock}:
  match xs:
    case NoStock{}:
      {==}
    case StockItem{capacity, rest}:
      %join_assoc(rest, ys, zs) :
        {StockItem{capacity, join(join(rest, ys), zs)} == StockItem{capacity, _} : Stock}
      {==}

def split_conserves(n, stock):
  match n stock:
    case 0n stock:
      {==}
    case 1n+p NoStock{}:
      {==}
    case 1n+p StockItem{capacity, rest}:
      %split_conserves(p, rest) :
        {StockItem{capacity, join(prefix(p, rest), suffix(p, rest))} == StockItem{capacity, _} : Stock}
      {==}

def allocation_conserves(requests, stock):
  match requests:
    case NoRequests{}:
      {==}
    case Request{subject, +units, +rest}:
      +lhs = join(assigned(allocate(Request{subject, units, rest}, stock)),
        remaining(Request{subject, units, rest}, stock))
      %split_conserves(units, stock) : {lhs == _ : Stock}
      %allocation_conserves(rest, suffix(units, stock)) :
        {lhs == join(prefix(units, stock), _) : Stock}
      %join_assoc(prefix(units, stock), assigned(allocate(rest, suffix(units, stock))),
        remaining(rest, suffix(units, stock))) : {lhs == _ : Stock}
      {==}

def allocation_policy(subject, units, rest, stock):
  {==}
