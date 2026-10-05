# Objective Bend reflection contract (draft, OB-LTUO LT1/LT4)

Status: DRAFT. LT1 landed the representation this contract is written against
(`Specification<T>` = `specification(SpecMeta, Extension<T>)`); LT4 owns the rest
(the provenance-establishing prototype constructor, the R(Y M) / Y(R∘M) placement, and
the resource observers stated as theorems). Nothing below that says "LT4" exists yet.

## Why a contract first

A specification's metadata is observable. Every observer a program has is a reason two
programs that compute the same answers are nonetheless different, and every law an
optimizer may use ("compose is associative") is only true for the observers that cannot
see the difference. So the observers are listed here, and every equivalence the
language promises names the observers it is stated against.

## The representation (landed, LT1)

```
sum SpecLaws:
  none: {}
  law: {name: String, status: String, rest: SpecLaws}

sum SpecMeta:
  declared: {name: String, interface: String, laws: SpecLaws}
  composed: {inherited: SpecMeta, wrapping: SpecMeta}
  extension: {}
```

Both sums are built-in types (module `$builtin`, no definitions), resolved by bare name in every module; a module may not
declare `SpecMeta` or `SpecLaws` (`refused (builtin-type)`).

- A `spec S for T` declaration is `specification(SpecMeta.declared{name: "M.S",
  interface: <C4 + requires + method signatures JSON>, laws: <law names>}, ext)`.
- `compose(a, b)` is `specification(SpecMeta.composed{inherited: P a, wrapping: P b},
  mix a b)`, where `P x = metadata(x)` when `x` is a specification and
  `SpecMeta.extension{}` when it is a bare `Extension<T>` (decided statically from
  the operand's type).
- Laws are NOT in the metadata value: each `law l(...)` is checked code in its own
  hidden knot field `M.S#law#l`, typed `(self: T, super: T, params...) -> Bool`, and
  the metadata lists its name with a status. Today every status is `unchecked`
  (typed, retained, never evaluated); LT6 adds `checked`/`discharged`/`refuted`.

Consequence (the LT1 acceptance): the type of a specification depends only on `T`.
Laws, ancestry and composition change the metadata VALUE, never the TYPE
(`Compiler/ObjectiveBendSpecificationClosure.lean`: `composeTy_closed`,
`compose_wrapper_checked`, `twice_accepted`, `law_spec_accepted`).

Decision and reason. The alternative was an opaque/existential metadata parameter
(`Specification<T>` = "some metadata type μ"). That needs a new Core4 type former and a
packing rule, so every machine preservation proof grows a case, and it leaves a client
of `s: Specification<T>` unable to observe anything about `s`'s provenance. A uniform
first-order representation needs no Core4 change at all (the checker, the demand
machine and every safety theorem are untouched; `accepted_never_refused` keeps its
statement and covers the new programs because they are checked programs), and it makes
provenance inspectable by ordinary `match`. The cost is that metadata is data, not
code: law closures could no longer ride in it, and that is the right outcome, because a
closure nobody calls is a promise nobody keeps (LT6).

## Observers (complete list for edition 1)

| observer | sees | runs the extension? |
|---|---|---|
| `metadata(s)` | the `SpecMeta` value of a specification | no |
| `reflect(p)` | the specification stored in a prototype pair | no |
| `targetOf(p)` | the target stored in a prototype pair | forces the target only |
| application / `fix(s, seed)` / `mix` | the extension's behaviour | yes |
| `==` on `String` fields of `SpecMeta` | names, interfaces, law names/statuses | no |

There is no observer of a closure's code, of a law's code, of the interface label's
structure other than as a string, or of heap identity.

## Two equivalences, kept apart

- **Behavioural equivalence** of specifications `a ≈b b` (DRAFT definition): for every
  well-typed seed and every context that uses `a`/`b` only through application, `fix`
  and `mix`, the observations of completed runs agree. `mix` is associative up to `≈b`:
  `compose(compose(A,B),C)` and `compose(A,compose(B,C))` both run
  `C self (B self (A self super))`.
- **Reflective equivalence** `a ≈r b`: `≈b` AND equal `metadata` values. Associativity
  does NOT hold up to `≈r`: the two associations have different `SpecMeta` trees
  (`composed{composed{A,B},C}` vs `composed{A,composed{B,C}}`), and a program can
  `match` on the difference (LTUO probe W03 picks between them at one type).

Rule for optimizers and rewriters: a rewrite justified by `≈b` may be applied only
where no `metadata` observer can reach the rewritten specification. Reassociating a
`compose` under `metadata` changes program output and is forbidden.

## Resource observations (stated separately; LT4)

Equal answers on completed runs do not imply equal ticks, heap or outcome under one
fixed budget: the demand machine distinguishes `finished`, `suspended` (budget),
`blackholed` and `yielded`. `≈b` above is about completed runs only. A rewrite that
preserves `≈b` may change which budget suffices; the preview's limits are part of what
a caller observes, so resource-preserving rewrites need their own statement.

## Prototypes and provenance (LT4, open)

`prototype(spec, target)` is a raw lazy pair: its typing checks the components
independently, so `reflect(p)` returns the stored spec and proves nothing about how
`targetOf(p)` was built. LT4 adds a constructor that establishes provenance by
construction (`instantiate(spec, seed)` = `prototype(spec, fix(spec, seed))`, with a
theorem relating `targetOf` to `fix`), keeps the raw pair as the low-level form, and
decides explicitly whether reflective self-reference goes inside the knot (`Y(R∘M)`:
`self` is the prototype, so `reflect(self)` works) or outside it (`R(Y M)`: the
prototype wraps a finished target). Until then, `reflect` is "what was stored", never
"what produced this".
