# Objective Bend front end

Reference for the one front end: the Lean program that turns `.obend` source into the Core4
term `Theory.ObjectiveBendDemandMachine` runs, plus a typing proposal that the
proof-producing checker (`Theory.ObjectiveBendTyping.check`) accepts with a derivation or
refuses. There is no other parser or elaborator. The overview, including what is proved and
what is open, is [OBJECTIVE-BEND.md](OBJECTIVE-BEND.md).

| Stage | Module | Output |
| --- | --- | --- |
| Parse | `Compiler/ObjectiveBendParse.lean` | `dregg.objective-bend.module.v1` AST |
| Capture | `Host/ObjectiveBendFrontEnd.lean` (`capture`) | a locked package (`objective.json`, `source/<i>.obend`) |
| Elaborate | `Compiler/ObjectiveBendElaborate.lean`, driven by `Compiler/ObjectiveBendFrontEnd.lean` | `PREFIX.core.json`, `PREFIX.typed.json` |
| Linearize | `Compiler/ObjectiveBendC4.lean` | C4 precedence lists |
| Preview | `Host/ObjectiveBendFrontEnd.lean` (`preview`) → `Host/ObjectiveBendPreview.lean` | check, then `runBounded` |
| Publish | `Compiler/ObjectiveBendPublication.lean` (`publishedCore`) | the typed core a package publishes |

## Commands

```text
lake env lean --run Host/ObjectiveBendFrontEndMain.lean COMMAND ...
minidregg-host /dev/null objective-front COMMAND ...          # the same code, compiled
```

`identity`; `parse FILE`; `capture PACKAGE_INPUT NEW_DIR [--objective-edition-1]`;
`elaborate CAPTURE PREFIX ARGUMENTS LIMITS ... [application|definition]`;
`preview REQUEST NEW_DIR`; `batch JOBS OUT`. The Host's `objective-publication` and the
receiver's admission run the same code. For one file, `bun docs/tutorial/run.ts FILE.obend
ENTRY [ARGS] [RESPONSES]` captures and previews it (see the
[tutorial](OBJECTIVE-BEND-TUTORIAL.md#before-you-start)).

## Identity

`Compiler/ObjectiveBendFrontEndIdentity.lean` fingerprints the front end compiled into a
program: `manifest` lists the SHA-256 of `ObjectiveBendParse`, `ObjectiveBendElaborate`,
`ObjectiveBendC4`, `ObjectiveBendTermWire`, `ObjectiveBendFrontEnd` and `Sha256`, and
`identity` is the SHA-256 of the manifest. A source package names the front end that lowered
it, the operator policy pins one, and admission requires the package's pin to be the policy's
and the policy's to be the receiver's own, then recomputes the core. Any edit to a listed file,
comments included, is a new identity: re-pin the policy (a re-genesis) and re-publish.

## Capture

`capture` reads `dregg.objective-bend.package-input.v1` (edition `objective-bend-1`): modules
`{name, sourcePath, imports: [{alias, path, module, sha256?}], sha256?}`, `entryModule`,
`entryDefinition`. Imports name earlier modules only, by `./NAME.obend`. Each source is read
once as strict UTF-8; optional expected hashes refuse changed bytes. The capture
(`dregg.objective-bend.captured-package.v2`) records the front-end identity, each module's
source copy and SHA-256, and each import edge; there is no stored AST. A capture made by
another front end refuses.

## Preview wire

Request `dregg.objective-bend.preview-input.v2`: `capturePath` and its exact `captureSha256`;
`argumentEncoding` (`legacy-values-v1`, the default: canonical decimal Nat strings, Booleans,
records; or `typed-values-v1`: `{tag: natural|boolean|label, value}` and
`{tag: record, fields: [{name, value}]}`, so a string is never read as a number); `arguments`;
`projections` (`{field, argument?}`); `responses` (at most 64 typed data values, one per yield
of an activity); `limits` with positive canonical decimal `ticks`, `heap`, `stack` (each at
most 100000) and `typeFuel` (at most 16384).

The preview re-reads the retained source, elaborates, writes the core and the typed packet,
decodes the packet, runs `check`, and only on acceptance runs `runBounded` on that same term.
An activity runs to its first yield; each supplied response is checked against the entry's
declared response type and resumes it to the next yield.

Result `dregg.objective-bend.preview-result.v2`: `status` (`finished`, `suspended`,
`divergent`, `yielded` or `refused`), `binding` (capture, source, core and typed-packet hashes,
the front-end identity, the limits, the responses' hash), and `preview`: the checked type and
uses, the weak-head `result`, the deep `resultData` (every field and payload forced by the
machine's own budgeted materialization; `null` with a `resultDataStatus` such as
`executableValue`, `suspended` or `budget` when the result is not first-order data or exhausts
the allowance), the per-turn Plans and checkpoint observations, and capacity observations. A
source, type or tooling refusal has `status: refused` with a structured `diagnostic` and exit
status 2; machine outcomes exit 0. The result carries `authority: none`: responses are
supplied, not admitted.

## Surface language and its core lowering

| Surface | Core4 |
| --- | --- |
| `def f(x: T, ...) -> R:` | a field `M.f` of the package knot: curried `lam`s |
| `fn(x: T) -> R: e`, `extension(self: S, super: I) -> P: e` | `lam` |
| `extension E(self: S, super: I) -> P:` | `λself λsuper. body` |
| `extension E[Self has R, Super has R'](self: Self, super: Super) -> Super with {...}:` | an open template, instantiated at each `fix` (below) |
| `spec S for T:` with `def m(...)` | `specification(SpecMeta.declared{name, interface, laws}, λself λsuper. extend super {m: ...})` |
| `spec S[Self has R, Super has R']:` | an open spec; its provided type is `Super with {defs}` |
| `spec S extends A, B for T:`, `suffix spec`, `around`, `combine + / * / and` | the C4 precedence list; the extension is the `mix` chain of the ancestors' hidden layers |
| `requires m(...) -> R` | a member of the Self bound; checked against the target (below) |
| `claim l(x): e` | a hidden knot field `M.S#claim#l` typed to return Bool, never evaluated; `SpecMeta` lists `l` with status `unchecked` |
| `compose(a, b, ...)` | left fold of `specification(SpecMeta.composed{inherited: P a, wrapping: P b}, mix a b)`, `P x` = `metadata(x)` for a specification and `SpecMeta.extension{}` for a bare extension; the inherited composite is bound once, so size is linear |
| `fix(s, seed)` | `fix`, with each layer instantiated at the row beneath it (below) |
| `extend(x, {f: e})`, `{f: e}`, `x.f`, `()` | `extend`, `record`, `get`, empty record |
| `prototype(s, t)`, `reflect(p)`, `metadata(s)`, `targetOf(p)` | `prototype`, `reflect`, `metadata`, `project` |
| `+ * - / % < <=` | `binary add / multiply / subtract / divide / modulo / less / lessEqual` |
| `a > b`, `a >= b` | `!(a <= b)`, `!(a < b)` through `ifBool`, so the left operand is evaluated first |
| `&&` | `binary conjunction` (strict) |
| `a \|\| b`, `if c then a else b` | `ifBool` (lazy in the untaken branch) |
| `==` / `!=` on Nat; on String; on Bool | `equal`; `labelEqual`; `(λr. if a then r else not r) b`; `!=` negates through `ifBool` |
| `match n:` `case 0n:` / `case 1n+p:` | `ifZero` (exactly those two arms) |
| `match b:` `case true:` / `case false:` | `ifBool` |
| `sum S:` `l: T`; `S.l(e)`; `match s:` `case l(x):` | variant type; `inject`; `case` (exhaustive, no wildcard) |
| `-> Activity<P, R, A>`, `perform(plan)`, `match perform(...):` | `perform`; a pure tail becomes `done`; the match is a `case` typed as an effect case |
| `let x = v` + the rest of the body, `let x: T = v in e` | `(λx. body) v`: one lazy cell, evaluated at most once |
| `true`/`false`, `"text"`, `7n` | `boolean`, `label`, `nat` |

The `==` dispatch needs both operand types; an unannotated operand is refused. The machine
primitives take naturals only (`nat_primitive_label_operand_refused`); `a / 0n = 0n` and
`a % 0n = a`, because the machine has no catchable exception. There is no unary `!` and no
string operation but equality.

### Parameters and quantities

`x: T` and `+x: T` are unrestricted; `-x: T` is erased; `affine x: T` and `linear x: T` are at
most once (exactly-once for `linear` is not enforced). Every closure built after an affine or
linear parameter is one-shot. An omitted type is `_`: a function result `_` is inferred from
the body when inference reaches a single type; otherwise the typing proposal is unsupported
and the preview refuses with a reason.

### Ancestry and method combination

Identity is the qualified declaration key, fixed at elaboration: a diamond's shared ancestor
appears once, while `compose(E, E)` applies `E` twice. The precedence list is C4 (C3 plus the
suffix property); refusals: no C3 candidate, incompatible suffixes, an ancestor out of order
against the suffix tail, cycles, unknown parents, ancestors with another target type.
`def` is primary (`super.m` calls the next method); `around` wraps every primary, including
those of more specific specs; `combine +`, `combine *`, `combine and` combine the own result
with the next method's (identities 0, 1, true at the bottom). A spec with ancestry stores its
layers as hidden globals `M.S#primary` and `M.S#around`. `before` and `after` are parsed and
refused. A method may not be primary in one ancestor and combined in another.

### Specifications, `requires` and `fix`

`SpecMeta` and `SpecClaims` are built-in sums (module `$builtin`) that no module may declare
(`refused (builtin-type)`); every specification has the type `Specification<T>`, so laws,
ancestry and composition never change it. The interface label (canonical JSON) records target,
suffix mark, parents, precedence list, requirements and signatures.

`fix` over a chain of declared plain specs and open declarations types each layer at the row
beneath it, bottom up from the seed, and refuses by name: `inherited-unprovided`,
`requires-unprovided`, `requires-signature`, `seed-extra`, `provided-mismatch`,
`inherited-mismatch`, `self-bound`, `self-conflict`, `self-undetermined`. An open declaration
is checked once at its own bounds with `Self` rigid (`self-rigid`, `self-unbound-member`), and
instantiated per use as a memoized knot field `M.E@i`. A whole-target seed, or an operand that
is not a declared plain spec or open declaration (ancestry specs, computed values), keeps the
closed lowering. A record may name itself (`record Node: combine(other: Node) -> Node`), a
recursive type like a recursive sum. Rules and design:
[OBJECTIVE-BEND.md](OBJECTIVE-BEND.md#modular-typing),
[objective-bend/MODULAR-TYPING.md](objective-bend/MODULAR-TYPING.md).

## Typing proposal

The elaborator emits `dregg.objective-bend.typed-core.v3`: the term, a type table `types`, one
annotation per `lam` (domain, codomain, quantity, reuse) and per `inject`, the global row as
bound 0, recursive sums and records as further bounded variables, and `fuel` (the request's
`typeFuel`). Each composite type is one table entry whose children are leaves or references
to earlier entries; identical entries are stored once, so the proposal is linear in the number
of distinct types (on `world/commons`'s `CommonsEscrowAmount`: 1,018,985 bytes, where fully
inlined types took 245,444,831). `decodeTypeWith` decodes a reference to exactly the type it
names. It is a proposal: the checker runs on the decoded term and refuses anything outside its
fragment.

## Publication

`ObjectiveBendPublication.replay` is the front end on a package's own source bytes: decode and
fingerprint each module, parse it, lock every import edge to the module the package names, and
lower the selected declaration in definition mode with type fuel 16384; `publishedCore` is the
canonical bytes of the typed packet. Native admission and the activity kernel recompute it and
accept only an identical artifact (`SourceSelection`, `Replayed`; `publish` and `loadProgram`
in `Kernel/ObjectiveActivity.lean`). The source package is edition 3 (sources, import locks,
entry, one `frontEnd` pin); the policy is edition 4. Earlier editions do not decode.

## Provenance

The parser and elaborator were ported from TypeScript and translation-validated before the
TypeScript was deleted (2026-10-04): the parser on every in-repo `.obend` plus 2720 seeded
mutants and 66 probes (identical ASTs and refusals, except two deliberate fixes), and the whole
pipeline on every declaration of `tests/objective-bend-source/*.obend`, every preview-cohort
invocation and the elaborator probes (302 jobs, 0 disagreements). Report:
`docs/objective-bend/evidence/front-end-port-20261004.json`.

## Checks

```text
bash scripts/check-objective-frontend.sh
```

Every row drives the Lean front end and is red, saying "needs warm base", without a built tree:
`identity`; `elaborate-tests` (`tests/objective-bend-source/check-elaborate.ts`); `c4-tests`
(`Compiler/ObjectiveBendC4Vectors`: published vectors, refusals, ordered-presentation invariance
on 4000 seeded DAGs); `check-parser`; `check-preview` (`preview-cohort.json`: each item
captured, elaborated, checked and run, pinning a scalar, a structured result, a no-deep-view
reason or a suspension; a wrong capture pin, a typing-budget refusal, tick and heap
suspensions); `ltuo-probes` (`ltuo/probe-cohort.json`: each probe pinned at its current outcome
with the target its LTUO row owes); `publication`; `activity-replay`; `examples`
(`scripts/check-objective-examples.sh`); `tutorial` and `overview`
(`scripts/check-objective-tutorial.ts` over [the tutorial](OBJECTIVE-BEND-TUTORIAL.md) and
[the overview](OBJECTIVE-BEND.md): every command re-run, every listing equal to its file).

## Trust boundary

Trusted, with no theorem: the parser, the elaborator and its typing proposal's choices, the C4
implementation. There is no surface semantics, so nothing states that the core means what the
source means. What is proved of the output: `Compiler/ObjectiveBendFrontEndAdequacy`
(`accepted_typed`, `accepted_never_refused`, `accepted_execution_semantics`, inhabited by
`accept_inhabited`); `decode_json` and `decodePacket_term` (the checker's decoder inverts the
front end's rendering, so a receiver types the front end's own term, never a parse of published
bytes); `admitted_front_end` (an admitted invocation's typed core is this front end's lowering
of the package's sources).
