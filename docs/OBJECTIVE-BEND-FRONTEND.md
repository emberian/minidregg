# Objective Bend front end, edition 1

The front end turns `.obend` source into the Core4 term that
`Theory.ObjectiveBendDemandMachine` runs, plus a typing proposal that the
proof-producing checker (`Theory.ObjectiveBendTyping.check`) either accepts
with a derivation or refuses. Everything here is trusted tooling except the
checker and the machine: see "Trust boundary" below.

| Stage | File | Output |
| --- | --- | --- |
| Parse | `native/bend-source/objective-parser.ts` | `dregg.objective-bend.module.v1` AST |
| Capture | `native/bend-source/objective-frontend.ts` | locked package (`objective.json`, sources, ASTs) |
| Elaborate | `native/bend-source/objective-elaborate.ts` (TS) and `Compiler/ObjectiveBendElaborate.lean` (Lean) | `PREFIX.core.json`, `PREFIX.typed.json` |
| Linearize | `native/bend-source/objective-c4.ts`, `Compiler/ObjectiveBendC4.lean` | C4 precedence lists |
| Preview | `native/bend-source/objective-preview.ts` → `Host/ObjectiveBendPreview.lean` | check + `runBounded` result |

## Capture

`objective-frontend.ts` reads `dregg.objective-bend.package-input.v1`
(edition `objective-bend-1`): modules `{name, sourcePath, imports:[{alias,
path, module, sha256?}], sha256?}`, canonical decimal module indices,
`entryModule`, `entryDefinition`. Imports name earlier modules only, by
`./NAME.obend`; the manifest locks alias and path. Gen-1 `./NAME.bend`
imports are refused by the parser and the frontend. Each source is read once
and parsed as strict UTF-8; optional expected hashes refuse changed bytes. The
explicit `--objective-edition-1` option adopts a `dregg.bend.package-input.v1`
Studio capture (same `.obend` import rule). SHA-256 values here are byte
fingerprints, not Mini package identities.

## Surface language and its core lowering

| Surface | Core4 |
| --- | --- |
| `def f(x: T, ...) -> R:` | a field `M.f` of the package knot: curried `lam`s |
| `extension E(self: S, super: I) -> P:` | `λself λsuper. body` |
| `spec S for T:` with `def m(...)` | `specification({name, interface, laws}, λself λsuper. extend super {m: ...})` |
| `spec S extends A, B for T:` | C4 precedence list; extension = `mix` chain of ancestor layers (below) |
| `suffix spec S ...` | S must stay a suffix of every descendant's precedence list |
| `requires m(...)` | recorded in the interface label only (not checked) |
| `law l(x): e` | a Bool-valued closure in the spec metadata (retained, never discharged) |
| `compose(a, b, ...)` | `(λl λr. specification({operator, inherited: l, wrapping: r}, mix l r)) a b`, folded left; the inherited composite is bound once, so size is linear |
| `fix(s, seed)` | `fix` |
| `extend(x, {f: e})`, `{f: e}`, `x.f`, `()` | `extend`, `record`, `get`, empty record |
| `prototype(s, t)`, `reflect(p)`, `metadata(s)`, `targetOf(p)` | `prototype`, `reflect`, `metadata`, `project` |
| `fn(x: T) -> R: e`, `extension(self: S, super: I) -> P: e` | `lam` |
| `+`, `*`, `&&` | `binary add / multiply / conjunction` |
| `==` / `!=` on Nat; on String | `equal`; `labelEqual` (negated through `ifBool` for `!=`) |
| `==` / `!=` on Bool | `(λr. if a then r else not r) b` |
| `a \|\| b`, `if c then a else b` | `ifBool` |
| `match n:` `case 0n:` / `case 1n+p:` | `ifZero` (exactly those two branches) |
| `match b:` `case true:` / `case false:` | `ifBool` |
| `sum S:` `l: T`; `S.l(e)`; `match s:` `case l(x):` | variant type; `inject l e`; `case` (exhaustive, no wildcard) |
| `<`, `>`, `<=`, `>=`, `-`, `/` | refused: no `Primitive.less / subtract / divide` exists |

The `==` dispatch needs both operand types; an unannotated operand is refused.
`inject`, `case`, `ifBool` and `Primitive.labelEqual` are Core4 constructors
(SUMS-DESIGN §9, §11): the Lean decoder in `Theory/ObjectiveBendTyping.lean` reads
them and the Lean elaborator erases them.

The package is one lazy knot whose root is a specification:
`fix(specification({package: [modules]}, λ$globals λ$seed. extend $seed {M.decl: ...}), {})`.
A global reference is `get $globals "M.name"`. The root extends its inherited
row instead of ignoring it, so a package is an extensible value in the core;
no surface form yet names another package's root.

### Parameters and quantities

`x: T` and `+x: T` are unrestricted; `-x: T` is erased; `affine x: T` and
`linear x: T` are at most once (the checker's `safeQuantity`; exact-once for
`linear` is not enforced). Every closure built after an affine or linear
parameter is one-shot (`reuse = once`) in its proposal and in the declared
arrow type. An omitted type is `_`: a function result `_` is inferred from
the body when the inference reaches a single type; otherwise the typing
proposal is unsupported and preview refuses.

### Declared ancestry and method combination

Identity is the qualified declaration key, fixed at elaboration (generative,
static): a diamond's shared ancestor appears once, while `compose(E, E)`
applies `E` twice. The precedence list is the C4 linearization (C3 plus the
suffix property; ltuo §7.4.4); refusals: no C3 candidate, incompatible
suffixes, an ancestor out of order against the suffix tail, ancestry cycles,
unknown parents, ancestors with another target type.

Method qualifiers: `def` (primary; `super.m` calls the next method), `around`,
and the pure simple combinations `combine +`, `combine *`, `combine and` (own
result combined with the next method's result; identity 0, 1, true at the
bottom). A spec with ancestry or qualifiers stores its own layers as hidden
globals `M.S#primary` and `M.S#around`; its extension is the mix chain,
least specific lowest: combination identities, every ancestor's primary layer,
every ancestor's around layer. So an around method wraps every primary,
including primaries of specs more specific than itself. `before` and `after`
are refused: they run for effects and discard their result. Core4 has `perform`
now, so they are buildable ([activities and events](OBJECTIVE-BEND-EVENTS.md)) and
are not built; a pure one would be silently discarded. A method may not be primary in one
ancestor and combined in another.

The spec interface label (canonical JSON) records target type, suffix mark,
parents, precedence list, requirements and method signatures; reflection reads
it with `metadata(S).interface`.

## Typing proposal

`literalAnnotations` emits `dregg.objective-bend.typed-core.v2`: the term, one
annotation per `lam` (domain, codomain, quantity, reuse) and per `inject`
(payload → variant), the global row as bound 0, recursive sums as further
bounded shareable variables. It is a proposal: `Host/ObjectiveBendPreview`
runs `check` on the same decoded term and refuses anything outside the
checker's fragment (for example a scalar-target spec, whose `extend` needs a
row, or an affine parameter used twice).

## The Lean elaborator and translation validation

`Compiler/ObjectiveBendElaborate.lean` is a port of the TS elaborator over the
same AST: same term, same proposal, fuel-bounded total functions. It erases to
the Core4 `Term`, sums and `perform` included. There is no adequacy
theorem: "surface meaning preserved" needs a surface semantics, which does
not exist. The evidence is translation validation:

```
bun native/bend-source/objective-elaborate-tv.ts NEW_DIR \
  lake env lean --run Host/ObjectiveBendElaborateRun.lean
```

compares the two elaborators on every declaration of every
`tests/objective-bend-source/*.obend`, every preview-cohort invocation and 19
inline refusal/acceptance probes (canonical JSON, both must refuse or both
must agree on term and proposal), and checks that a mutated term and a
mutated annotation are caught. `OrderedPresentationInvariant` in
`Compiler/ObjectiveBendC4.lean` states renaming invariance of C4 on ordered
presentations; it is not proved. `objective-c4-tests.ts` checks pommette's
published vectors and the invariance property on 4000 seeded DAGs.

## Checks

```
bun native/bend-source/objective-elaborate-tests.ts
bun native/bend-source/objective-c4-tests.ts
bun tests/objective-bend-source/check-parser.ts
bun tests/objective-bend-source/check-preview.ts \
  tests/objective-bend-source/preview-cohort.json NEW_DIR LEAN OLEAN_ROOT [BUN]
```

`check-preview.ts` captures each cohort item with the real frontend,
elaborates it and runs the compiled checker and `runBounded`; it also checks a
wrong capture pin and a typing-budget refusal, and tick and heap suspensions.

## Trust boundary

Trusted (not checked by anything): the TS parser and frontend, the TS and Lean
elaborators (translation validation shows only that the two agree), the
typing proposal's choices, the C4 implementation. Checked: typing of the
emitted term (proof-producing `check`), and evaluation (`runBounded`, with the
soundness theorems in `Theory/ObjectiveBendDemandAdequacy.lean`). Laws are
retained, never discharged; `requires` is not checked.
