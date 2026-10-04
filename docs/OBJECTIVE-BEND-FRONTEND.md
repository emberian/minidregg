# Objective Bend front end, edition 1

The front end turns `.obend` source into the Core4 term that
`Theory.ObjectiveBendDemandMachine` runs, plus a typing proposal that the
proof-producing checker (`Theory.ObjectiveBendTyping.check`) either accepts
with a derivation or refuses. It is ONE program, in Lean; there is no other
parser or elaborator. See "Trust boundary" for what is proved of it.

| Stage | Module | Output |
| --- | --- | --- |
| Parse | `Compiler/ObjectiveBendParse.lean` | `dregg.objective-bend.module.v1` AST |
| Capture | `Host/ObjectiveBendFrontEnd.lean` (`capture`) | locked package (`objective.json`, `source/<i>.obend`) |
| Elaborate | `Compiler/ObjectiveBendElaborate.lean`, driven by `Compiler/ObjectiveBendFrontEnd.lean` | `PREFIX.core.json`, `PREFIX.typed.json` |
| Linearize | `Compiler/ObjectiveBendC4.lean` | C4 precedence lists |
| Preview | `Host/ObjectiveBendFrontEnd.lean` (`preview`) → `Host/ObjectiveBendPreview.lean` | check + `runBounded` result |
| Publish | `Compiler/ObjectiveBendPublication.lean` (`publishedCore`) | the typed core a package publishes |

The commands (`identity`, `parse`, `capture`, `elaborate`, `preview`, `batch`) run
as `lake env lean --run Host/ObjectiveBendFrontEndMain.lean COMMAND ...` or, compiled,
as `minidregg-host /dev/null objective-front COMMAND ...`; the Host's
`objective-publication PACKAGE_SPEC CODEC NEW_DIR` and the receiver's admission run the
same code.

## Identity

`Compiler/ObjectiveBendFrontEndIdentity.lean` fingerprints the front end compiled
into a program: `manifest` lists the SHA-256 of the parser, elaborator, C4, driver and
SHA-256 sources (read when that module is elaborated; it imports all of them, so an
edit rebuilds it), and `identity` is the SHA-256 of the manifest. `objective-front
identity` prints both; the `identity` row of `scripts/check-objective-frontend.sh`
recomputes them with `sha256sum`. A source package names the front end that lowered
it (`ObjectiveSourcePackage.Package.frontEnd`), the operator policy pins one
(`ObjectiveBendNativeAdmission.Policy.frontEnd`, printed by `objective-constants`),
and admission requires the package's pin to be the policy's and the policy's to be the
receiver's own, then recomputes the core (below). Any edit to a fingerprinted file is a
new identity: re-pin the policy (a re-genesis) and re-publish.

## Capture

`capture` reads `dregg.objective-bend.package-input.v1` (edition
`objective-bend-1`): modules `{name, sourcePath, imports:[{alias, path, module,
sha256?}], sha256?}`, canonical decimal module indices, `entryModule`,
`entryDefinition`. Imports name earlier modules only, by `./NAME.obend`; the
manifest locks alias and path. Gen-1 `./NAME.bend` imports are refused by the parser
and the capture. Each source is read once and decoded as strict UTF-8 (a leading
byte-order mark is consumed); optional expected hashes refuse changed bytes. The
explicit `--objective-edition-1` option adopts a `dregg.bend.package-input.v1` Studio
capture (same `.obend` import rule). The capture
(`dregg.objective-bend.captured-package.v2`) records the front-end identity, each
module's source copy and SHA-256, and each import edge with its lock; there is no
stored AST (the source is the package; `parse` prints the AST on demand). A v1 capture
(with ASTs and TypeScript tool hashes) does not load. SHA-256 values here are byte
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
| `-`, `/`, `<`, `<=`, `>`, `>=` | a call of one prelude definition (`$prelude.sub / divide / lt / le`; `>` and `>=` swap the operands of `<` and `<=`): see below |
| `let x = v` + rest of the body, `let x: T = v in e` | `(λx. body) v`, one lazy cell for `v`: see below |

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

## Operators without a core primitive, and `let`

Core4 has no `subtract`, `less` or `divide` primitive, so the elaborator adds a
module `$prelude` (not a legal source module name) to the package knot, holding
exactly the definitions the program's operators need, after the user's modules:

| Operator | Prelude definition | Meaning |
| --- | --- | --- |
| `a - b` | `sub` | truncated: `0n` when `b` exceeds `a` |
| `a < b`, `a > b` | `lt` (`>` swaps the operands) | Bool |
| `a <= b`, `a >= b` | `le` (`>=` swaps the operands) | Bool |
| `a / b` | `divide`, via `quotient`, `lt`, `sub` | floor division, and `a / 0n = 0n` |

Each is a recursion over `ifZero`, so it is exact on every Nat and costs about
one machine step per unit of the smaller operand (`/`: of the dividend). A zero
divisor must mean something because the machine has no catchable exception; `0n`
is the `Nat.div` convention, and a program whose zero divisor is a real case must
test it first. A package using none of these operators is unchanged. The prelude is
Objective Bend source (`preludeSource` in `Compiler/ObjectiveBendElaborate.lean`) read
by the same parser as any module (`prelude_parses`). Replacing this by machine primitives (O(1)) is a core change and is
not done: the lowering is the one place to swap.

`let x = v` (statement form: the rest of the body follows at the same indent) and
`let x: T = v in e` (expression form) lower to `app (lam body) v`. An application
allocates one lazy cell for its argument and the machine caches it on first demand
(`DemandMachine`, frame `argument`), so `v` is evaluated at most once however often
`x` is used and not at all when unused: call-by-need, never a copy. The value is
elaborated outside the binder (`let x = x + 1n` reads the outer `x`), `x` is
unrestricted, and an omitted type is synthesized from `v` (an unresolvable one makes
the typing proposal unsupported with a reason, never a guess). A `let` in an
activity's tail has the activity type as its lambda codomain; `let x = perform(..)`
is refused like any activity in a shared position.

## Typing proposal

`literalAnnotations` emits `dregg.objective-bend.typed-core.v3`: the term, a type
table `types`, one annotation per `lam` (domain, codomain, quantity, reuse) and per
`inject` (payload → variant), the global row as bound 0, recursive sums as further
bounded shareable variables, and `fuel` (the request's `typeFuel`: the packet the
elaborator writes, `PREFIX.typed.json`, is exactly the packet the checker reads).

Types are named through the table: each composite type (arrow, field,
specification, prototype, variant, computation) is one entry whose children are
inline leaves (`natural`, `boolean`, `label`, `emptyRow`, `variable`, `custody`) or
`{"tag":"ref","index":"N"}` naming an EARLIER entry; identical entries are stored
once, in post-order over the annotations, then the bounds. A fully expanded type of
a record whose fields are records of records is exponential in its depth; the table
is linear in the number of distinct types. Measured on `world/commons`
(`CommonsEscrowAmount`): the proposal was 245,444,831 bytes (and the preview wrote a
byte-identical second copy, `typed-input.json`); it is 1,018,985 bytes and one file.
`Theory.ObjectiveBendTyping.decodeTypeWith` decodes a ref to exactly the type it names,
depth included, so a table-form proposal decodes to the same `Ty` as its inlined
expansion under the same nesting capacity (256); the checker's judgment is unchanged.
The v2 schema (every type inlined) no longer loads. It is a proposal: `Host/ObjectiveBendPreview`
runs `check` on the same decoded term and refuses anything outside the
checker's fragment (for example a scalar-target spec, whose `extend` needs a
row, or an affine parameter used twice).

## Publication and the receiver

`ObjectiveBendPublication.replay` is the front end on a package's own source bytes:
decode and fingerprint each module, parse it, lock every parsed import edge to the
module the package names, lower the selected declaration in definition mode with type
fuel 16384; `publishedCore` is the canonical bytes of the typed packet.
`objective-publication` publishes exactly those bytes for a package naming this Host's
front end, and native admission recomputes them: an artifact whose typed core differs
from the receiver's own `publishedCore` of its package is refused
(`SourceSelection.replayExact`), as is a package naming another front end. The source
package is edition 3 (`frame` byte 3: sources, import locks, entry, one `frontEnd`
pin; no ASTs, no parser/frontend/elaborator pin triple); the policy is edition 4 (one
`frontEnd` pin). Earlier editions do not decode. The activity kernel holds the same replay
token: `publish` stores an activity artifact and its package together only after this
replay, and every later turn reloads the pair and replays it again
(`Kernel/ObjectiveActivity.lean:1131`, `:622`).

## Provenance

The parser and elaborator were ported from TypeScript and translation-validated
against it before the TypeScript was deleted (2026-10-04): the parser on every
in-repo `.obend` plus 2720 seeded mutants and 66 probes (2854 jobs: identical ASTs and
identical refusal messages and spans, except two deliberate divergences where the
TypeScript accepted what it should not: an identifier such as `valueOf` read as a
binary operator through `Object.prototype`, and a string literal holding a lone UTF-16
surrogate escape); and the whole pipeline, source to core term and typing proposal, on
every declaration of every `tests/objective-bend-source/*.obend`, every
preview-cohort invocation and the elaborator probes (302 jobs, 0 disagreements; a
mutated term is caught). Reports: `docs/objective-bend/evidence/front-end-port-20261004.json`.

## Checks

```
bash scripts/check-objective-frontend.sh
```

runs every row through the Lean front end: `identity` (the compiled-in manifest is
`sha256sum` of the files), `elaborate-tests` (`tests/objective-bend-source/check-elaborate.ts`:
the elaboration cohort, one batch), `c4-tests` (`Compiler/ObjectiveBendC4Vectors`:
pommette's vectors and refusals, and the ordered-presentation invariance on 4000
seeded DAGs, compiled theorems), `check-parser`, `check-preview` (each cohort item
captured, elaborated, checked and run; a wrong capture pin and a typing-budget
refusal; tick and heap suspensions), `publication`
(`tests/objective-native/PublicationReplay.lean`: the Host's publication of
`world/NativeReceipt.obend` is what the receiver's replay recomputes; a foreign pin, a
changed source and a tampered core are refused), `activity-replay`
(`tests/objective-native/ActivityReplay.lean`: the activity kernel replays the package
stored with an activity artifact and loads the program from it; a foreign core, a foreign
front end, a missing package and another source are refused), `examples`, `tutorial`. A cohort item pins a
scalar result (`expected`), or a whole structured result (`expectedData`, typed data
compared with record fields ordered by name), or the reason a result has no deep view
(`expectedDataStatus`), or exhaustion of the preview's tick budget
(`expectedStatus: "suspended"`).

## Trust boundary

Trusted (no theorem): the parser, the elaborator and its typing proposal's choices,
the C4 implementation. Their output is not trusted blindly:
`Compiler/ObjectiveBendFrontEndAdequacy` proves that whenever the checker accepts the
front end's own packet (`ObjectiveBendFrontEnd.accept`), the erasure of the
elaborator's term is closed and typed by the checker's derivation (`accepted_typed`),
is never refused by the bounded demand machine at any budget
(`accepted_never_refused`), and a finished run of it extracts the unique deep source
evaluation of it (`accepted_execution_semantics`); `accept_inhabited` exhibits a surface program it
holds for. `Kernel/ObjectiveBendAdmissionSemantics.admitted_front_end` proves an
admitted invocation's typed core is byte-for-byte this front end's lowering of the
package's sources. The link from the packet to the term is a theorem: the checker's decoder inverts the
front end's rendering (`decode_json`, `Compiler/ObjectiveBendTermWire.lean:69`;
`decodePacket_term`, `:280`), so the term the checker reads from the packet is the
elaborator's erasure by proof, and a receiver types that term, never a parse of the
published bytes (`Compiler/ObjectiveBendPublication.lean:1-20`). Open: there is no
surface semantics, so nothing states that the core means what the source means. Laws are retained,
never discharged; `requires` is not checked.
