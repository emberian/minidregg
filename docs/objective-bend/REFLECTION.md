# The reflection contract

What an Objective Bend program may observe about a specification, and which equivalences hold
against which observers (OB-LTUO rows LT1 and LT4). Every observer is a reason two programs
that compute the same answers are nonetheless different, and every law a rewriter may use
("compose is associative") holds only for the observers that cannot see the difference; so
the observers are listed, and every equivalence names the observers it is stated against.

## The representation

```text
sum SpecClaims:
  none: {}
  claim: {name: String, status: String, rest: SpecClaims}

sum SpecMeta:
  declared: {name: String, interface: String, claims: SpecClaims}
  composed: {inherited: SpecMeta, wrapping: SpecMeta}
  extension: {}
```

Both are built-in sums (module `$builtin`), resolved by bare name in every module, and no
module may declare them (`refused (builtin-type)`).

- `spec S for T` is `specification(SpecMeta.declared{name: "M.S", interface: <C4, requires
  and signatures as JSON>, laws: <law names>}, ext)`.
- `compose(a, b)` is `specification(SpecMeta.composed{inherited: P a, wrapping: P b}, mix a b)`,
  where `P x` is `metadata(x)` for a specification and `SpecMeta.extension{}` for a bare
  extension, decided statically from the operand's type.
- A law is not in the metadata value: each `law l(...)` is checked code in its own hidden knot
  field `M.S#claim#l`, typed to return Bool, and the metadata lists its name with a status. Every
  status is `unchecked` (typed, retained, never evaluated).

So the type of a specification depends only on `T`: laws, ancestry and composition change the
metadata value, never the type (`Compiler/ObjectiveBendSpecificationClosure.lean`:
`composeTy_closed`, `twice_accepted`, `claim_spec_accepted`).

**Why a uniform first-order representation** rather than an opaque metadata parameter
(`Specification<T>` = "some metadata type μ"): an existential needs a new Core4 type former and
a packing rule, so every machine preservation proof grows a case, and it leaves a client unable
to observe anything of provenance. Metadata as ordinary data needs no Core4 change, keeps every
safety theorem as it is, and makes provenance inspectable by `match`. The cost is that metadata
cannot carry closures, which is right: a closure nobody calls is a promise nobody keeps.

## Observers (edition 1, complete)

| Observer | Sees | Runs the extension? |
| --- | --- | --- |
| `metadata(s)` | the `SpecMeta` value | no |
| `reflect(p)` | the specification stored in a prototype | no |
| `targetOf(p)` | the target stored in a prototype | forces the target only |
| application, `fix(s, seed)`, `mix` | the extension's behaviour | yes |
| `==` on `String` fields of `SpecMeta` | names, interfaces, law names and statuses | no |

There is no observer of a closure's code, of a law's code, of the interface label's structure
other than as a string, or of heap identity.

## Two equivalences

- **Behavioural** `a ≈b b`: for every well-typed seed and every context that uses `a` and `b`
  only through application, `fix` and `mix`, the observations of completed runs agree. `mix` is
  associative up to `≈b`: both associations run `C self (B self (A self super))`.
- **Reflective** `a ≈r b`: `≈b` and equal `metadata`. Associativity fails up to `≈r`: the two
  associations have different `SpecMeta` trees, and a program tells them apart (probes R01 and
  R02, `tests/objective-bend-source/ltuo/AssociationProvenance.obend`).

A rewrite justified by `≈b` may be applied only where no `metadata` observer can reach the
rewritten specification. Neither equivalence is a theorem yet: `composition_associative` is
proved on the separate list model `Theory/ObjectiveBendExtensions.lean`, not on `Term.mix`.

## Resource observations

Equal answers on completed runs do not imply equal ticks, heap, or outcome under one budget:
the machine distinguishes `finished`, `suspended`, `divergent` and `yielded`. `≈b` is about
completed runs only; the preview's limits are part of what a caller observes, so a
resource-preserving rewrite needs its own statement. None is stated.

## Prototypes and provenance (open)

`prototype(spec, target)` is a raw lazy pair: its typing checks the components independently,
so `reflect(p)` returns what was stored and proves nothing about how `targetOf(p)` was built.
Open (LT4): a constructor that establishes provenance by construction (`instantiate(spec,
seed)` = `prototype(spec, fix(spec, seed))`, with a theorem relating `targetOf` to `fix`),
keeping the raw pair as the low-level form; and an explicit decision whether reflective
self-reference goes inside the knot (`Y(R∘M)`: `self` is the prototype) or outside it
(`R(Y M)`: the prototype wraps a finished target).
