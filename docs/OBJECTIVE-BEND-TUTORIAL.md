# Objective Bend: a tutorial

This is a short course in the Objective Bend language. It assumes you have never
seen it. Each chapter has one to three small programs. Every program is a real
file under [docs/tutorial/](tutorial/). Every result printed below is the output
of running that file through the front end and the preview. No printed result
was written by hand.

This tutorial covers the language as the preview runs it. It says nothing about
admission, receipts or deployment. The preview carries no authority: it reads a
program, checks it and runs it, and it prints what happened. For the language
guide and its formal status see [OBJECTIVE-BEND.md](OBJECTIVE-BEND.md).

## Before you start

You need `bun`, a `lean` binary, and the compiled Lean modules that
[Host/ObjectiveBendPreview.lean](../Host/ObjectiveBendPreview.lean) imports
(`Theory.ObjectiveBendTyping`, `Theory.ObjectiveBendDemandMachine`,
`Theory.ObjectiveBendDemandData` and `Theory.ObjectiveBendCheckpoint`). The
runner looks for `lean` on your `PATH` and for the compiled modules in
`.lake/build/lib/lean`. Set `LEAN` and `OLEAN_ROOT` to use other places. This
tutorial was run against an existing build; it did not build Lean.

Every command below is run from the repository root. They all have the same shape:

```text
bun docs/tutorial/run.ts FILE ENTRY [ARGS] [RESPONSES] [--ticks N] [--json]
```

`FILE` is an `.obend` file. `ENTRY` is the name of one `def` in it. `ARGS` is a
JSON array of arguments: a Nat is a decimal string such as `"7"`, a Bool is
`true` or `false`. `RESPONSES` is used only in chapter 8. `--ticks N` sets how
many machine steps the run may take (the default is 100000). `--json` prints the
preview's own result, unchanged, instead of the short form used here.

[run.ts](tutorial/run.ts) does four things. It captures the file as a package. It
elaborates the source to a core term and a typing proposal. The preview then
asks the checker to type that term. If the checker accepts, the preview runs the
same term on the machine. See [OBJECTIVE-BEND-FRONTEND.md](OBJECTIVE-BEND-FRONTEND.md)
and [OBJECTIVE-BEND-PREVIEW.md](OBJECTIVE-BEND-PREVIEW.md).

The short form prints these lines:

- `status`: `finished`, `suspended` (ran out of ticks), `divergent`, `yielded`
  (an activity is waiting, chapter 8) or `refused`.
- `type`: the type the checker gave the entry.
- `result`: the value, when there is one.

A refusal prints `stage` and `message` instead, and the command exits with
status 2.

## 1. Values, functions, records, laziness

A file starts with `edition ObjectiveBend 1`. A line that starts with `#` is a
comment. Indent with spaces, never tabs. A natural number is written with an `n`
after it: `21n`. A function is `def name(parameters) -> Type:` followed by its
body on the next line, indented. The body is the value.

A `record` declares a type with named fields. `{x: 0n, y: 0n}` builds one, and
`p.x` reads one field.

```text
edition ObjectiveBend 1
# Chapter 1: values, functions, records.

record Point:
  x: Nat
  y: Nat

def double(n: Nat) -> Nat:
  n + n

def answer() -> Nat:
  double(21n)

def origin() -> Point:
  {x: 0n, y: 0n}

def shifted(p: Point, by: Nat) -> Point:
  {x: p.x + by, y: p.y}

def shiftedX() -> Nat:
  shifted(origin(), 5n).x
```

```sh
$ bun docs/tutorial/run.ts docs/tutorial/ch1-values.obend answer
status: finished
type: Nat
result: 42

$ bun docs/tutorial/run.ts docs/tutorial/ch1-values.obend shiftedX
status: finished
type: Nat
result: 5

$ bun docs/tutorial/run.ts docs/tutorial/ch1-values.obend origin
status: finished
type: {x: Nat, y: Nat}
result: {x: 0, y: 0}
```

`origin` returns a record. The preview prints a result in full: to print the
record it forces every field, with a tick budget of its own. A record holds its
fields as suspended computations, and nothing else computes a field until
something reads it. In `shiftedX`, the `.x` reads one field of the shifted
record, and that read is what runs.

### A field that is never forced

```text
edition ObjectiveBend 1
# Chapter 1: laziness. A field is computed only when something reads it.

record Pair:
  good: Nat
  bad: Nat

# Running spin never finishes: it calls itself forever.
def spin(n: Nat) -> Nat:
  spin(n)

def pair() -> Pair:
  {good: 7n, bad: spin(0n)}

def good() -> Nat:
  pair().good

def bad() -> Nat:
  pair().bad
```

`spin` calls itself forever. The record `pair()` has a field `bad` that would run
it. Building the record does not run it.

```sh
$ bun docs/tutorial/run.ts docs/tutorial/ch1-lazy.obend pair
status: finished
type: {good: Nat, bad: Nat}
result: {good, bad}

$ bun docs/tutorial/run.ts docs/tutorial/ch1-lazy.obend good
status: finished
type: Nat
result: 7

$ bun docs/tutorial/run.ts docs/tutorial/ch1-lazy.obend bad
status: suspended
type: Nat
diagnostic: Minidregg.Theory.ObjectiveBendDemandMachine.Suspension.ticks
```

`pair` and `good` finish. Printing `pair` in full would force `bad`, which runs
`spin`; the preview spends its budget on that, gives up, and prints only the
field names `{good, bad}`. Nothing returned a value for `bad`. `bad` reads the
field, so it runs `spin`. It never finishes, and the preview stops it when the
tick budget is used up. The status
is `suspended` and the diagnostic names `Suspension.ticks`. That is the preview
stopping, not an error in the program.

### Sharing: a thunk is evaluated once

An argument is passed as a suspended computation. The first read computes it.
Later reads reuse the answer. (`match` is explained in chapter 2. Here, read
`work(n)` as a slow way to compute 2 to the power n.)

```text
edition ObjectiveBend 1
# Chapter 1: sharing. An argument is evaluated at most once, however
# often the function reads it. (match is explained in chapter 2; read
# work(n) as a slow way to compute 2 to the power n.)

def work(n: Nat) -> Nat:
  match n:
    case 0n: 1n
    case 1n+p: work(p) + work(p)

def twice(x: Nat) -> Nat:
  x + x

# work(8n) is passed once and read twice.
def shared() -> Nat:
  twice(work(8n))

# work(8n) is written twice, so it is computed twice.
def separate() -> Nat:
  work(8n) + work(8n)
```

`shared` passes `work(8n)` once, and `twice` reads it twice. `separate` writes
`work(8n)` twice, so it computes it twice. Both give 512 with the default
budget:

```sh
$ bun docs/tutorial/run.ts docs/tutorial/ch1-sharing.obend separate
status: finished
type: Nat
result: 512
```

Give both the same smaller budget and they differ:

```sh
$ bun docs/tutorial/run.ts docs/tutorial/ch1-sharing.obend shared --ticks 12000
status: finished
type: Nat
result: 512

$ bun docs/tutorial/run.ts docs/tutorial/ch1-sharing.obend separate --ticks 12000
status: suspended
type: Nat
diagnostic: Minidregg.Theory.ObjectiveBendDemandMachine.Suspension.ticks
```

Searching for the smallest budget that finishes gave these edges:

```sh
$ bun docs/tutorial/run.ts docs/tutorial/ch1-sharing.obend shared --ticks 8220
status: finished
type: Nat
result: 512

$ bun docs/tutorial/run.ts docs/tutorial/ch1-sharing.obend shared --ticks 8219
status: suspended
type: Nat
diagnostic: Minidregg.Theory.ObjectiveBendDemandMachine.Suspension.ticks

$ bun docs/tutorial/run.ts docs/tutorial/ch1-sharing.obend separate --ticks 16380
status: finished
type: Nat
result: 512

$ bun docs/tutorial/run.ts docs/tutorial/ch1-sharing.obend separate --ticks 16379
status: suspended
type: Nat
diagnostic: Minidregg.Theory.ObjectiveBendDemandMachine.Suspension.ticks
```

`shared` needs 8220 ticks. `separate` needs 16380, about twice as many. The
second computation of `work(8n)` is the difference.

## 2. Natural numbers, `match`, booleans and `if`

A Nat is either zero or one more than another Nat. `match` takes a Nat apart
with exactly two cases: `case 0n:` and `case 1n+p:`, where `p` names the Nat
below. You must write both. There is no wildcard (chapter 9).

A Bool is `true` or `false`. You can `match` on a Bool with `case true:` and
`case false:`, or write `if c then a else b`. `==` and `!=` compare two Nats.
`&&` and `||` join two Bools. `+` and `*` work on Nats, and so do `-`, `/`, `<`,
`<=`, `>` and `>=`, which are shown after `minus` below. `minus` is written out by
recursion first, because that recursion is what `-` means.

```text
edition ObjectiveBend 1
# Chapter 2: natural numbers, match, booleans and if.
# A Nat is 0n or 1n+p, where p is the one below it. There is no negative.

def pred(n: Nat) -> Nat:
  match n:
    case 0n: 0n
    case 1n+p: p

def isZero(n: Nat) -> Bool:
  match n:
    case 0n: true
    case 1n+p: false

# Subtract b from a, stopping at zero. This is the recursion that a - b means.
def minus(a: Nat, b: Nat) -> Nat:
  match b:
    case 0n: a
    case 1n+q: minus(pred(a), q)

def even(n: Nat) -> Bool:
  match n:
    case 0n: true
    case 1n+p: if even(p) then false else true

def pick(flag: Bool, a: Nat, b: Nat) -> Nat:
  match flag:
    case true: a
    case false: b

# == and != compare two Nats and give a Bool. && and || join two Bools.
def small(n: Nat) -> Bool:
  isZero(n) && n == 0n

def differ(a: Nat, b: Nat) -> Bool:
  a != b

def either(a: Bool, b: Bool) -> Bool:
  a || b

def clamp(n: Nat) -> Nat:
  if n == 10n then 9n else n
```

```sh
$ bun docs/tutorial/run.ts docs/tutorial/ch2-naturals.obend pred '["5"]'
status: finished
type: Nat
result: 4

$ bun docs/tutorial/run.ts docs/tutorial/ch2-naturals.obend pred '["0"]'
status: finished
type: Nat
result: 0

$ bun docs/tutorial/run.ts docs/tutorial/ch2-naturals.obend minus '["7","3"]'
status: finished
type: Nat
result: 4

$ bun docs/tutorial/run.ts docs/tutorial/ch2-naturals.obend minus '["3","7"]'
status: finished
type: Nat
result: 0
```

`pred` of zero is zero, and `minus` stops at zero. A Nat cannot go below it.

```sh
$ bun docs/tutorial/run.ts docs/tutorial/ch2-naturals.obend even '["10"]'
status: finished
type: Bool
result: true

$ bun docs/tutorial/run.ts docs/tutorial/ch2-naturals.obend even '["7"]'
status: finished
type: Bool
result: false

$ bun docs/tutorial/run.ts docs/tutorial/ch2-naturals.obend pick '[true,"1","2"]'
status: finished
type: Nat
result: 1

$ bun docs/tutorial/run.ts docs/tutorial/ch2-naturals.obend pick '[false,"1","2"]'
status: finished
type: Nat
result: 2

$ bun docs/tutorial/run.ts docs/tutorial/ch2-naturals.obend differ '["3","4"]'
status: finished
type: Bool
result: true

$ bun docs/tutorial/run.ts docs/tutorial/ch2-naturals.obend differ '["4","4"]'
status: finished
type: Bool
result: false

$ bun docs/tutorial/run.ts docs/tutorial/ch2-naturals.obend either '[false,true]'
status: finished
type: Bool
result: true

$ bun docs/tutorial/run.ts docs/tutorial/ch2-naturals.obend either '[false,false]'
status: finished
type: Bool
result: false

$ bun docs/tutorial/run.ts docs/tutorial/ch2-naturals.obend clamp '["10"]'
status: finished
type: Nat
result: 9
```

The type line tells you which are Nats and which are Bools. The checker has
checked every call against those types before anything runs.

### Subtraction, order, division and `let`

Each of these is one step of the machine, exact on any Nat however large: `a - b`
on two billion-sized Nats costs what `3n - 1n` costs.

`a - b` stops at zero. `a / b` is whole-number division, rounding down, and
`a / 0n` is `0n`: the language has no catchable exception, so a zero divisor has
to mean something, and a program whose zero divisor is a real case tests it
first. `a < b`, `a <= b`, `a > b` and `a >= b` give a Bool.

`let name = value` followed by the rest of the body at the same indent, or
`let name = value in expression`, names a value. It is a suspended computation
like an argument: computed the first time something reads it, once, and not at
all if nothing does. `let` never copies the work.

```text
edition ObjectiveBend 1
# Chapter 2: subtraction, order, division and let.
# a - b stops at zero. a / b is whole-number division and a / 0n is 0n.
# a < b, a <= b, a > b and a >= b give a Bool.

def difference(a: Nat, b: Nat) -> Nat:
  a - b

def ordered(a: Nat, b: Nat) -> Bool:
  a <= b

def share(total: Nat, parts: Nat) -> Nat:
  total / parts

# let names a value. It is computed the first time something reads it, once.
def surcharge(price: Nat, units: Nat) -> Nat:
  let base = price * units
  base + base / 10n

def spread(a: Nat, b: Nat) -> Nat:
  let high = if a < b then b else a
  let low = if a < b then a else b
  high - low
```

```sh
$ bun docs/tutorial/run.ts docs/tutorial/ch2-operators.obend difference '["7","3"]'
status: finished
type: Nat
result: 4

$ bun docs/tutorial/run.ts docs/tutorial/ch2-operators.obend difference '["3","7"]'
status: finished
type: Nat
result: 0

$ bun docs/tutorial/run.ts docs/tutorial/ch2-operators.obend ordered '["3","4"]'
status: finished
type: Bool
result: true

$ bun docs/tutorial/run.ts docs/tutorial/ch2-operators.obend ordered '["5","4"]'
status: finished
type: Bool
result: false

$ bun docs/tutorial/run.ts docs/tutorial/ch2-operators.obend share '["17","5"]'
status: finished
type: Nat
result: 3

$ bun docs/tutorial/run.ts docs/tutorial/ch2-operators.obend share '["17","0"]'
status: finished
type: Nat
result: 0

$ bun docs/tutorial/run.ts docs/tutorial/ch2-operators.obend surcharge '["7","10"]'
status: finished
type: Nat
result: 77

$ bun docs/tutorial/run.ts docs/tutorial/ch2-operators.obend spread '["3","10"]'
status: finished
type: Nat
result: 7

$ bun docs/tutorial/run.ts docs/tutorial/ch2-operators.obend spread '["10","3"]'
status: finished
type: Nat
result: 7
```

## 3. Sums

A sum is a value that is exactly one of several labelled cases. You declare it
with `sum`. Each line is `label: Type`, and the payload type can be a Nat or a
record written inline like `{side: Nat}`. A record may mention the sum itself. You build a value
with `Sum.label(payload)`. `List.nil()` has an empty payload.

You take a sum apart with `match` and one `case label(binder):` per label. The
binder names the payload. Every label needs an arm, and there is no wildcard.
Write `_` for a payload you do not use.

```text
edition ObjectiveBend 1
# Chapter 3: sums. A sum value is one of several labelled cases.

sum Shape:
  circle: Nat
  square: {side: Nat}

def area(s: Shape) -> Nat:
  match s:
    case circle(r): r * r * 3n
    case square(q): q.side * q.side

def bigSquare() -> Nat:
  area(Shape.square({side: 4n}))

def smallCircle() -> Nat:
  area(Shape.circle(2n))

# A list is a sum that mentions itself.
sum List:
  nil: {}
  cons: {head: Nat, tail: List}

def length(xs: List) -> Nat:
  match xs:
    case nil(_): 0n
    case cons(c): 1n + length(c.tail)

def sum(xs: List) -> Nat:
  match xs:
    case nil(_): 0n
    case cons(c): c.head + sum(c.tail)

def numbers() -> List:
  List.cons({head: 2n, tail: List.cons({head: 7n, tail: List.cons({head: 5n, tail: List.nil()})})})

def count() -> Nat:
  length(numbers())

def total() -> Nat:
  sum(numbers())
```

```sh
$ bun docs/tutorial/run.ts docs/tutorial/ch3-sums.obend bigSquare
status: finished
type: Nat
result: 16

$ bun docs/tutorial/run.ts docs/tutorial/ch3-sums.obend smallCircle
status: finished
type: Nat
result: 12
```

A circle of radius 2 has area `2 * 2 * 3`, and a square of side 4 has area 16.

`List` mentions itself in `cons`, so it is a list. `length` and `sum` walk it.
`numbers()` is the list 2, 7, 5.

```sh
$ bun docs/tutorial/run.ts docs/tutorial/ch3-sums.obend count
status: finished
type: Nat
result: 3

$ bun docs/tutorial/run.ts docs/tutorial/ch3-sums.obend total
status: finished
type: Nat
result: 14

$ bun docs/tutorial/run.ts docs/tutorial/ch3-sums.obend numbers
status: finished
type: variable 1
result: cons({head: 2, tail: cons({head: 7, tail: cons({head: 5, tail: nil({})})})})
```

`numbers` returns the list itself. The preview forces every payload to print the
whole list. The type is printed as `variable 1`, the preview's name for the
recursive `List`.

## 4. Specifications and `extension(self, super)`

An **extension** is one layer. It takes two values and returns a new one:

- `super` is what the layers below produced.
- `self` is the final result of all the layers, once they are stacked.

`fix(layer, seed)` stacks a layer on a starting value and returns the result.
`compose(a, b)` puts `a` first and `b` on top. `extend(super, {f: e})` is
`super` with the field `f` replaced.

Because every layer sees the same `self`, a field can read another field that a
later layer changes. This is late binding.

```text
edition ObjectiveBend 1
# Chapter 4: extensions. extension(self, super) builds a value in layers.
# super is what the layers below produced. self is the final result of all
# the layers, so a layer can read a field that a later layer changes.

record Account:
  base: Nat
  total: Nat

# total is computed from base, read through self.
extension Defaults(self: Account, super: Account) -> Account:
  {base: 10n, total: self.base + 1n}

# This layer changes base and keeps everything else from below.
extension Raised(self: Account, super: Account) -> Account:
  extend(super, {base: super.base + 5n})

def seed() -> Account:
  {base: 0n, total: 0n}

def plain() -> Account:
  fix(Defaults, seed())

def raised() -> Account:
  fix(compose(Defaults, Raised), seed())

def plainTotal() -> Nat:
  plain().total

def raisedBase() -> Nat:
  raised().base

def raisedTotal() -> Nat:
  raised().total
```

`Defaults` computes `total` from `self.base`. Alone, `base` is 10:

```sh
$ bun docs/tutorial/run.ts docs/tutorial/ch4-late-binding.obend plainTotal
status: finished
type: Nat
result: 11
```

`Raised` sits on top and adds 5 to `base`. `Defaults` is not touched.

```sh
$ bun docs/tutorial/run.ts docs/tutorial/ch4-late-binding.obend raisedBase
status: finished
type: Nat
result: 15

$ bun docs/tutorial/run.ts docs/tutorial/ch4-late-binding.obend raisedTotal
status: finished
type: Nat
result: 16
```

`total` is now 16, not 11. The same `self.base + 1n` read a different `base`.
Nobody edited `Defaults`.

### Specifications

A **spec** is a named layer for a record type. `spec Name for Record:` holds
`def` methods. A method can call `super.m(...)`, the same method from the layers
below, and `self.m(...)`, the method of the final object. The record
declaration lists the methods, with their parameters.

```text
edition ObjectiveBend 1
# Chapter 4: specifications. A spec is a named, reusable layer for a record.
# def adds or replaces a method. super.m is the method below; self.m is the
# method of the final object.

record Shop:
  price(n: Nat) -> Nat
  bill(n: Nat) -> Nat

spec Base for Shop:
  def price(n: Nat) -> Nat:
    n * 3n

spec Billing for Shop:
  def bill(n: Nat) -> Nat:
    self.price(n) + 1n

spec Surcharge for Shop:
  def price(n: Nat) -> Nat:
    super.price(n) + 2n

# fix needs something to start from. These methods are replaced by the specs.
def blank() -> Shop:
  {price: fn(n: Nat) -> Nat: 0n, bill: fn(n: Nat) -> Nat: 0n}

def shop() -> Shop:
  fix(compose(Base, Billing), blank())

def surcharged() -> Shop:
  fix(compose(Base, Billing, Surcharge), blank())

def billOfTwo() -> Nat:
  shop().bill(2n)

def surchargedBillOfTwo() -> Nat:
  surcharged().bill(2n)

def surchargedPriceOfTwo() -> Nat:
  surcharged().price(2n)
```

`blank()` is the starting value for `fix`. The specs replace both methods, so
its zeros are never seen.

```sh
$ bun docs/tutorial/run.ts docs/tutorial/ch4-specs.obend billOfTwo
status: finished
type: Nat
result: 7

$ bun docs/tutorial/run.ts docs/tutorial/ch4-specs.obend surchargedPriceOfTwo
status: finished
type: Nat
result: 8

$ bun docs/tutorial/run.ts docs/tutorial/ch4-specs.obend surchargedBillOfTwo
status: finished
type: Nat
result: 9
```

Without `Surcharge`, `bill(2)` is 7: the price is 6 and the fee is 1. With it,
the price is 8, and `Billing` now gives 9. `Billing` calls `self.price`, so it
sees the surcharge that was added later.

## 5. Composition and declared ancestry

`compose(a, b, c)` stacks specs in the order you write them. A spec can also
say what it extends: `spec S extends A, B for T:`. The front end then computes
one order for the whole family, called the C4 linearization. A shared ancestor
appears once in it, however many paths reach it.

The file below has a diamond. `Both` reaches `Root` through `Left` and through
`Right`. The method `trace` adds one digit per layer, so its result spells the
order the layers ran. The method `weight` is declared `combine +`: each layer's
number is added to the next layer's.

```text
edition ObjectiveBend 1
# Chapter 5: declared ancestry. A spec can say which specs it extends.
# Each trace method adds its own digit after the one from below, so the
# result spells the order the layers ran in. weight adds up the weights of
# the layers. combine + adds the layers own result to the next one.

record Doc:
  trace() -> Nat
  weight() -> Nat

spec Root for Doc:
  def trace() -> Nat:
    1n
  combine + weight() -> Nat:
    1n

spec Left extends Root for Doc:
  def trace() -> Nat:
    super.trace() * 10n + 2n
  combine + weight() -> Nat:
    20n

spec Right extends Root for Doc:
  def trace() -> Nat:
    super.trace() * 10n + 3n
  combine + weight() -> Nat:
    300n

# Both reaches Root by two paths (through Left and through Right).
spec Both extends Left, Right for Doc:
  def trace() -> Nat:
    super.trace() * 10n + 4n
  combine + weight() -> Nat:
    4000n

# around wraps the whole chain, including layers more specific than itself.
spec Logged extends Both for Doc:
  around trace() -> Nat:
    super.trace() + 50000n

spec Last extends Logged for Doc:
  def trace() -> Nat:
    super.trace() * 10n + 5n

def blank() -> Doc:
  {trace: 0n, weight: 0n}

def bothTrace() -> Nat:
  fix(Both, blank()).trace

def bothWeight() -> Nat:
  fix(Both, blank()).weight

def loggedTrace() -> Nat:
  fix(Logged, blank()).trace

def lastTrace() -> Nat:
  fix(Last, blank()).trace

# compose copies each spec as written, so Root runs twice here.
def composedWeight() -> Nat:
  fix(compose(Left, Right), blank()).weight

def interface() -> String:
  metadata(Last).interface
```

```sh
$ bun docs/tutorial/run.ts docs/tutorial/ch5-ancestry.obend bothTrace
status: finished
type: Nat
result: 1324

$ bun docs/tutorial/run.ts docs/tutorial/ch5-ancestry.obend bothWeight
status: finished
type: Nat
result: 4321
```

The digits read 1, 3, 2, 4: `Root`, then `Right`, then `Left`, then `Both`.
`Root` ran first and once. The weight is 1 + 20 + 300 + 4000. If `Root` had
counted twice it would be 4322.

An `around` method wraps the whole chain. It sits outside every `def`, including
the `def` of a spec that is more specific than the one that declares it.

```sh
$ bun docs/tutorial/run.ts docs/tutorial/ch5-ancestry.obend loggedTrace
status: finished
type: Nat
result: 51324

$ bun docs/tutorial/run.ts docs/tutorial/ch5-ancestry.obend lastTrace
status: finished
type: Nat
result: 63245
```

`Logged` adds 50000 to whatever the chain below it gives. For `Logged` alone
that is 1324 + 50000 = 51324. `Last` is more specific and adds a digit first:
1324 becomes 13245, and then `around` adds 50000, giving 63245.

The linearization is recorded in the spec's metadata, most specific first. The
names carry the module name, which `run.ts` takes from the file name:

```sh
$ bun docs/tutorial/run.ts docs/tutorial/ch5-ancestry.obend interface
status: finished
type: String
result: "{\"methods\":[{\"name\":\"trace\",\"parameters\":[],\"qualifier\":\"primary\",\"resultType\":\"Nat\",\"span\":{\"end\":1103,\"line\":42,\"start\":1084}}],\"parents\":[\"Logged\"],\"precedence\":[\"ch5_ancestry.Last\",\"ch5_ancestry.Logged\",\"ch5_ancestry.Both\",\"ch5_ancestry.Left\",\"ch5_ancestry.Right\",\"ch5_ancestry.Root\"],\"requirements\":[],\"suffix\":false,\"targetType\":\"Doc\"}"
```

### Composing specs by hand

`compose(Left, Right)` is not the same as declaring `Both`. Each spec brings
its own copy of its ancestors, and the `combine +` method starts again from zero
in each spec's own chain:

```sh
$ bun docs/tutorial/run.ts docs/tutorial/ch5-ancestry.obend composedWeight
status: finished
type: Nat
result: 301
```

The result is 1 + 300. The 20 from `Left` is gone. The front-end guide describes
the zero that each chain starts with
([OBJECTIVE-BEND-FRONTEND.md](OBJECTIVE-BEND-FRONTEND.md), "Declared ancestry
and method combination"). When specs share an ancestor, declare the ancestry
instead of composing them by hand.

## 6. Prototypes and reflection

`prototype(spec, target)` pairs a spec with an object. Three functions take the
pair apart:

- `reflect(p)` gives the spec.
- `metadata(s)` gives the spec's metadata, a record. This chapter reads its
  `name` and `interface` fields.
- `targetOf(p)` gives the object.

`reflect` and `metadata` do not run the object. `targetOf` does.

```text
edition ObjectiveBend 1
# Chapter 6: prototypes and reflection. prototype(spec, target) keeps a spec
# and the object built from it together. reflect, metadata and targetOf take
# them apart without running the other half.

record Tally:
  n: Nat

spec Start for Tally:
  law nonNegative: true
  def n() -> Nat:
    41n

def seed() -> Tally:
  {n: 0n}

def built() -> Tally:
  fix(Start, seed())

def firstName() -> String:
  metadata(reflect(prototype(Start, built()))).name

def target() -> Nat:
  targetOf(prototype(Start, built())).n

def interface() -> String:
  metadata(Start).interface

# stuck never finishes. The prototype is never asked for its target, so
# reflecting on it still works.
def stuck() -> Tally:
  stuck()

def name() -> String:
  metadata(reflect(prototype(Start, stuck()))).name

# Asking for the target of the same prototype does run it.
def stuckTarget() -> Nat:
  targetOf(prototype(Start, stuck())).n
```

```sh
$ bun docs/tutorial/run.ts docs/tutorial/ch6-reflection.obend firstName
status: finished
type: String
result: "ch6_reflection.Start"

$ bun docs/tutorial/run.ts docs/tutorial/ch6-reflection.obend target
status: finished
type: Nat
result: 41

$ bun docs/tutorial/run.ts docs/tutorial/ch6-reflection.obend interface
status: finished
type: String
result: "{\"methods\":[{\"name\":\"n\",\"parameters\":[],\"qualifier\":\"primary\",\"resultType\":\"Nat\",\"span\":{\"end\":311,\"line\":11,\"start\":296}}],\"parents\":[],\"precedence\":[\"ch6_reflection.Start\"],\"requirements\":[],\"suffix\":false,\"targetType\":\"Tally\"}"
```

`stuck()` never finishes. The prototype built from it can still be reflected on,
because nothing asks for its target:

```sh
$ bun docs/tutorial/run.ts docs/tutorial/ch6-reflection.obend name
status: finished
type: String
result: "ch6_reflection.Start"

$ bun docs/tutorial/run.ts docs/tutorial/ch6-reflection.obend stuckTarget
status: divergent
type: Nat
diagnostic: blackhole; no catchable source exception
```

`name` finishes. `stuckTarget` asks for the object and runs `stuck()`. That
definition has no parameters, so it is one shared value that needs itself to
finish. The machine reports `divergent`. `spin` in chapter 1 was different: it
ran until its budget ended and reported `suspended`.

The `law` line in `Start` is kept in the spec and is never checked. The
language guide says so.

## 7. Quantities

A parameter can carry a quantity. `affine x: Nat` may be used at most once.
`linear y: Nat` is checked the same way: at most once, not exactly once. A plain
`x: Nat` may be used any number of times, as `twice` did in chapter 1.

```text
edition ObjectiveBend 1
# Chapter 7: an affine parameter may be used at most once.

def once(affine x: Nat) -> Nat:
  x + 1n

# At most once includes not at all.
def dropped(affine x: Nat) -> Nat:
  0n

# linear is checked the same way: at most once, not exactly once.
def droppedLinear(linear y: Nat) -> Nat:
  0n
```

All three are accepted. Using a parameter zero times is within "at most once".

```sh
$ bun docs/tutorial/run.ts docs/tutorial/ch7-once.obend once '["4"]'
status: finished
type: Nat
result: 5

$ bun docs/tutorial/run.ts docs/tutorial/ch7-once.obend dropped '["4"]'
status: finished
type: Nat
result: 0

$ bun docs/tutorial/run.ts docs/tutorial/ch7-once.obend droppedLinear '["4"]'
status: finished
type: Nat
result: 0
```

Using an affine parameter twice is refused:

```text
edition ObjectiveBend 1
# Chapter 7: used twice, the checker refuses the program.

def twice(affine x: Nat) -> Nat:
  x + x
```

```sh
$ bun docs/tutorial/run.ts docs/tutorial/ch7-twice.obend twice '["4"]'
status: refused
stage: objective-typed-preview
message: ownership refused: an affine or linear parameter is used more than once (both mean at most once), or one is captured by a closure that may run again (the program checks with every quantity unrestricted)
(exit status 2)
```

The checker refuses the whole program. The checker itself only answers
accepted or refused; the preview names the kind of rule by asking the same
checker about two variations of the program (see `refusalReason` in
[Host/ObjectiveBendPreview.lean](../Host/ObjectiveBendPreview.lean)): with ample
type fuel (a `checker budget refused` message), and with every quantity made
unrestricted (this `ownership refused` message: relaxing `affine` is exactly
what makes `twice` check). Anything else is reported as `typing refused`. It
names the kind of rule, not the line. Nothing runs
after a refusal. The command also exits with status 2, and the same message goes
to standard error as JSON.

## 8. Activities

An **activity** is a computation that hands a Plan to a host, waits, and
continues with the host's response. Its type is `Activity<P, R, A>`:

- `P` is the type of the Plans it yields, a sum.
- `R` is the type of the responses it accepts, also a sum.
- `A` is the type of the value it finishes with.

`perform(plan)` yields a Plan. You use it as `match perform(...):`, and the arms
of the match are the handlers for the response. A plain value at the end of an
arm is lifted into the activity for you.

```text
edition ObjectiveBend 1
# Chapter 8: an activity. It hands a Plan to its host, waits for a response,
# and carries on with the response in hand.

record Write:
  field: Nat
  before: Nat
  after: Nat

sum Plan:
  write: Write

sum Response:
  written: {}
  refused: {}

# One turn: ask for count to become count + 1, and report the new count.
def bump(count: Nat) -> Activity<Plan, Response, Nat>:
  match perform(Plan.write({field: 0n, before: count, after: count + 1n})):
    case written(_): count + 1n
    case refused(_): count

# A resident: it asks again after every response, and never finishes.
def serve(count: Nat) -> Activity<Plan, Response, Nat>:
  match perform(Plan.write({field: 0n, before: count, after: count + 1n})):
    case written(_): serve(count + 1n)
    case refused(_): serve(count)
```

`bump` asks to change a counter from `count` to `count + 1` and finishes with
the new count. The preview has no host, so you supply the responses yourself,
one per yield. A bare label such as `written` means that label with an empty
payload. (That shorthand belongs to `run.ts`.)

```sh
$ bun docs/tutorial/run.ts docs/tutorial/ch8-counter.obend bump '["4"]'
status: yielded
type: Activity<sum {write: {field: Nat, before: Nat, after: Nat}}, sum {written: {}, refused: {}}, Nat>
turn 1: yield write({field: 0, before: 4, after: 5})  (waiting)
diagnostic: waiting for a response

$ bun docs/tutorial/run.ts docs/tutorial/ch8-counter.obend bump '["4"]' '["written"]'
status: finished
type: Activity<sum {write: {field: Nat, before: Nat, after: Nat}}, sum {written: {}, refused: {}}, Nat>
turn 1: yield write({field: 0, before: 4, after: 5})  <- written({})
result: 5

$ bun docs/tutorial/run.ts docs/tutorial/ch8-counter.obend bump '["4"]' '["refused"]'
status: finished
type: Activity<sum {write: {field: Nat, before: Nat, after: Nat}}, sum {written: {}, refused: {}}, Nat>
turn 1: yield write({field: 0, before: 4, after: 5})  <- refused({})
result: 4
```

With no response the activity stops at its first yield and the status is
`yielded`. With `written` it finishes with 5. With `refused` it finishes with 4.
Each `turn` line is one yield and the response that resumed it.

`serve` never finishes. After each response it asks again. Run it one turn at a
time:

```sh
$ bun docs/tutorial/run.ts docs/tutorial/ch8-counter.obend serve '["0"]'
status: yielded
type: Activity<sum {write: {field: Nat, before: Nat, after: Nat}}, sum {written: {}, refused: {}}, Nat>
turn 1: yield write({field: 0, before: 0, after: 1})  (waiting)
diagnostic: waiting for a response

$ bun docs/tutorial/run.ts docs/tutorial/ch8-counter.obend serve '["0"]' '["written","written","refused"]'
status: yielded
type: Activity<sum {write: {field: Nat, before: Nat, after: Nat}}, sum {written: {}, refused: {}}, Nat>
turn 1: yield write({field: 0, before: 0, after: 1})  <- written({})
turn 2: yield write({field: 0, before: 1, after: 2})  <- written({})
turn 3: yield write({field: 0, before: 2, after: 3})  <- refused({})
turn 4: yield write({field: 0, before: 2, after: 3})  (waiting)
diagnostic: waiting for a response
```

Turn 3 is refused, so the count stays 2 and turn 4 asks for the same write
again. It is waiting for a response. These responses are only what you typed.
Nothing here admits a write.

The Plan and Response types in this chapter are the chapter's own. An activity the
kernel itself runs uses the kernel's shapes: its Plan is `await {write, on, patience}`
and its response is `resumed {outcome, view}`, the settled outcome together with the
object's declared state read in the resuming turn.
[world/activity/Tally.obend](../world/activity/Tally.obend) is the reference program, and
[OBJECTIVE-BEND-EVENTS.md](OBJECTIVE-BEND-EVENTS.md#the-kernel-activity) describes the
kernel's side.

### An effect may not hide in a shared value

An argument and a record field are shared suspended computations. An effect
inside one would be cached and shared. The front end refuses it and names the
rule.

```text
edition ObjectiveBend 1
# Chapter 8: an effect may not hide in an argument. An argument is a shared
# thunk, so the effect would run once and be cached.

sum Plan:
  go: {}

sum Response:
  ok: {}

def keep(x: Nat) -> Nat:
  x

def run(n: Nat) -> Activity<Plan, Response, Nat>:
  keep(perform(Plan.go({})))
```

```sh
$ bun docs/tutorial/run.ts docs/tutorial/ch8-hidden-argument.obend run '["0"]'
status: refused
stage: objective-core-elaboration
message: refused (effect-as-argument): an Activity cannot be used here; an argument is a shared lazy thunk, so its effect would be cached and shared. Match on it first.
(exit status 2)
```

The same rule applies to a record field:

```text
edition ObjectiveBend 1
# Chapter 8: nor in a record field, which is also a shared thunk.

sum Plan:
  go: {}

sum Response:
  ok: {}

def run(n: Nat) -> Activity<Plan, Response, Nat>:
  match perform(Plan.go({})):
    case ok(_): {x: perform(Plan.go({}))}.x
```

```sh
$ bun docs/tutorial/run.ts docs/tutorial/ch8-hidden-field.obend run '["0"]'
status: refused
stage: objective-core-elaboration
message: refused (effect-in-field): an Activity cannot be used here; a record field is a shared lazy cell, so its effect would be cached and shared. Match on it first.
(exit status 2)
```

Match on the activity first, then use the response. The language guide
([OBJECTIVE-BEND-EVENTS.md](OBJECTIVE-BEND-EVENTS.md)) lists the other named
refusals: `effect-in-payload`, `effect-in-plan`, `perform-outside-activity` and
`nullary-activity`. This tutorial did not run those four.

## 9. What the language does not do yet

One thing you will meet quickly. It was run:

```text
edition ObjectiveBend 1
# Chapter 9: a Nat match takes exactly a zero case and a successor case.

def f(n: Nat) -> Nat:
  match n:
    case 0n: 1n
    case _: 2n
```

```sh
$ bun docs/tutorial/run.ts docs/tutorial/ch9-wildcard.obend f '["3"]'
status: refused
stage: objective-core-elaboration
message: Nat match currently requires exactly zero and successor branches
(exit status 2)
```

The rest of this chapter is the list the language guide keeps. It is quoted
from [OBJECTIVE-BEND.md](OBJECTIVE-BEND.md), "What Core4 lacks: the roadmap". The
tutorial did not run these items.

Roadmap, in the guide's order:

1. A native route for activities. The kernel's turns (persist the checkpoint,
   resume with a typed response and a view of the object's state) are built and
   proved, but no Host operation reaches them yet.
2. A guardedness check, so that a well-typed resident never diverges inside a
   turn.
3. The theorem for declared ancestry. Declared ancestry with C4 linearization
   and method combination has landed: chapter 5 ran it in the preview, and
   [OBJECTIVE-BEND-FRONTEND.md](OBJECTIVE-BEND-FRONTEND.md) documents it. What
   the guide lists as missing is the linearization invariance theorem
   (`OrderedPresentationInvariant`), which is stated and not proved. `before`
   and `after` methods are still refused.
4. Checked `requires` and closed final-self assumptions. Today `requires` is
   recorded as a string and not checked.
5. Dynamic `get`, and a surface form that names another package's root. (The
   package root is a specification and label equality is a primitive; both
   have landed.)

Further gaps the guide names, unranked: sealing, `final` and suffix
declarations; reflection beyond `reflect`, `metadata` and `project` (listing
fields, asking whether a field exists); a consumed mark for linear values;
fresh persistent instances; governed live upgrade; and a canonical cost law on
the machine (native admission already charges a public price for a declared
envelope; the machine itself has no cost law).

[OBJECTIVE-BEND-EVENTS.md](OBJECTIVE-BEND-EVENTS.md) adds what activities cannot
do yet: a view library (Plans and responses must be non-recursive data, so lists
of children wait); live authoring and governed evolution; more than
one action per yield; crawling the world from inside a program; snapshot and
rewind; string operations beyond equality; and the `before` and `after`
method qualifiers.

## Where the examples live

The sixteen programs are in [docs/tutorial/](tutorial/). The programs the
language's own checks use are in
[tests/objective-bend-source/](../tests/objective-bend-source/). The checks that
run them are listed at the end of
[OBJECTIVE-BEND-FRONTEND.md](OBJECTIVE-BEND-FRONTEND.md).
