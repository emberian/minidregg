# Readable source-only example. These tiny token/reference values are synthetic
# source inputs; they are not deployed resources, grants or runtime receipts.
import Base
import ./OrderedCapacity.bend as Capacity

def first() -> Capacity.Capacity:
  Capacity.Capacity{1n, [1n], [11n]}

def second() -> Capacity.Capacity:
  Capacity.Capacity{2n, [2n], [12n]}

def third() -> Capacity.Capacity:
  Capacity.Capacity{3n, [3n], [13n]}

def contributed_stock() -> Capacity.Stock:
  Capacity.StockItem{first(),
    Capacity.StockItem{second(), Capacity.StockItem{third(), Capacity.NoStock{}}}}

# Member A requests two places; member B requests two. Frozen order is A, B.
def member_requests() -> Capacity.Requests:
  Capacity.Request{[1n], 2n, Capacity.Request{[2n], 2n, Capacity.NoRequests{}}}

def demonstration() -> Capacity.Grants:
  Capacity.allocate(member_requests(), contributed_stock())

# Result: A receives the first two tokens; B receives the last token.
# This closed source example accompanies the general allocation_conserves law.
law demonstration_result:
  {demonstration() ==
    Capacity.Grant{[1n], Capacity.StockItem{first(), Capacity.StockItem{second(), Capacity.NoStock{}}},
      Capacity.Grant{[2n], Capacity.StockItem{third(), Capacity.NoStock{}}, Capacity.NoGrants{}}} : Capacity.Grants}

def demonstration_result():
  {==}

law demonstration_remaining:
  {Capacity.remaining(member_requests(), contributed_stock()) == Capacity.NoStock{} : Capacity.Stock}

def demonstration_remaining():
  {==}
