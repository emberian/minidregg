# Objective Bend

Objective Bend is Mini's authored language for a shared, governed computing
world. People and agents should be able to define tools, documents, services and
worlds, extend one another's behavior, inspect the resulting programs, and retain
instances and activities across sessions. Its language model is **lazy open
recursion with first-class reusable extensions**. Mini supplies durable identity,
current authority, effect admission and controlled disclosure around execution.

The new Objective edition has its own source syntax, reference semantics, shared
thunk machine and annotated type checker. Actual captured source has passed that
checker and run on that machine. The retained BendTT checked-Book path is a
separate language/backend profile; its call-by-value proofs do not establish the
new edition's semantics. Native source storage and pinned instances already
exist, while dispatch from this new language through native effects is still
being connected. The sections below distinguish these boundaries without making
them the language's definition.

## Extensions before objects

An extension receives a context and an inherited value and returns a new value.
The inherited and resulting types may differ. In object use, the context contains
**final self**, and the inherited value is **whole super**. An extension can add
fields, wrap behavior, replace a value, or construct a function; it is not limited
to overriding a method selector.

For extensions `lower` and `upper`, composition means:

```text
compose(lower, upper)(self, super) = upper(self, lower(self, super))
```

Both layers see the same final self. The upper layer receives the whole result of
the lower layer as its super. Composition is associative and generally not
commutative. An extension remains meaningful before its eventual self exists.
[The extension algebra](../Theory/ObjectiveBendExtensions.lean) states this with
independent context, inherited and resulting types. Its homogeneous `mix` operation
is one useful specialization, not the limit of the language model.

`fix(extension, inherited)` ties the recursive knot: it computes a target whose
self reference denotes that target. The [operational semantics](../Theory/ObjectiveBendOpenRecursion.lean)
define how this computation proceeds; the equation `self = extension(self, inherited)`
alone would not do so. Fixed points may diverge. They may also produce a useful
function or a record without evaluating every recursive component.

A **specification** retains an extension and inspectable metadata, including
requirements and laws. Partial specifications are values in their own right;
inspecting one need not complete its requirements or instantiate its target.
A **prototype** pairs a retained specification with its target. Generic `fix`
returns the target directly; the explicit prototype construction places the
wrapper inside the knot when reflection through self is required. Treating every
fixed point as a prototype would change the language.

### A reusable captured extension

This is the working part of
[GenericExtension.obend](../tests/objective-bend-source/GenericExtension.obend):

```text
edition ObjectiveBend 1

def addCaptured(delta: Nat) -> Extension<Nat>:
  extension(self: Nat, super: Nat) -> Nat: super + delta

def reuseCaptured(seed: Nat) -> Nat:
  fix(compose(addCaptured(2n), addCaptured(3n)), seed)
```

`addCaptured` returns a first-class extension closing over `delta`. Applied to
seed `7`, the composition returns `12`. Neither layer needs to force self. The
same source file also contains a self-demanding composition; retaining that
unused definition does not force it. The
[heterogeneous example](../tests/objective-bend-source/Heterogeneous.obend)
adds `y = 2 * self.x` and then `z = self.y` to an inherited record. Starting from
`{x: 5}`, observing `z` returns `10`, through the shared final self.

With the repository's Lean toolchain and matching compiled imports prepared
under the [bounded build policy](DEVELOPING.md#build-and-verify-without-disturbing-another-run), run:

```sh
lake env lean --run examples/objective-bend-world/reference/GenericExtension.lean
```

This [driver](../examples/objective-bend-world/reference/GenericExtension.lean)
runs the retained core term for `reuseCaptured(7)` on the actual demand machine
and prints a completed natural `12` plus heap/stack observations. It is a core
reproduction, not a compiler invocation: editing the `.obend` file requires a new
capture and elaboration.

For that source-to-execution route, the actual tools are:

```sh
bun native/bend-source/objective-frontend.ts \
  tests/objective-bend-source/GenericExtension-package.json EMPTY_CAPTURE_DIR
bun native/bend-source/objective-preview-request.ts \
  EMPTY_CAPTURE_DIR/objective.json NEW_REQUEST_JSON '["7"]' '[]'
bun native/bend-source/objective-preview.ts \
  NEW_REQUEST_JSON EMPTY_RESULT_DIR PINNED_TOOLING_CONFIG
```

Run from the source root, using new owned paths for the uppercase placeholders.
Use the [capture schema](OBJECTIVE-BEND-FRONTEND.md) and
[preview schema](OBJECTIVE-BEND-PREVIEW.md) to construct those inputs. The preview
needs a server-owned configuration pinning matching compiled tools and semantic
modules; a fresh checkout does not contain an installed preview service. It
reparses the captured source, elaborates it, checks the proposed typed term, and
executes that same decoded term. The captured-extension and heterogeneous
examples passed this route under the qualified wire-v1 cohort. The current
request helper targets the explicit-Boolean wire-v2 cohort, which needs its own
matching tools and qualification. Unsupported annotations produce diagnostics;
parsing a construct alone does not establish that the typed preview supports it.

## Demand, sharing and reflection

The reference semantics are weak-head and lazy: applying a lambda does not first
evaluate its argument; constructing a record does not force its fields. The
[demand machine](../Theory/ObjectiveBendDemandMachine.lean) gives delayed work
identity in a heap. Entering a suspended cell marks it as evaluating; returning
caches its value at the same address, preserving its origin. Repeated demand then
uses that cached value. A recursive fixed point allocates a shared cell referring
to itself, rather than repeatedly copying an unfolding term.

The machine distinguishes a finished value, resource suspension, a refused
operation and re-entry into an evaluating cell (a blackhole). Tick exhaustion
retains the current state; a capacity refusal retains the state before the
transition that would exceed capacity. A blackhole is a non-result, not a
catchable source exception. Other nonterminating programs can continue until
suspended; this is not a decision procedure for termination.

Reflection of a prototype returns its retained specification without forcing the
target. Specification metadata can likewise be observed without evaluating its
extension. These are operational properties with named source reduction lemmas,
not permissions to inspect private execution state. Shared evaluation changes
work and storage behavior relative to the reference reduction; general
correspondence between the two still needs proof.

## Types, captures and laws

[Types](../Theory/ObjectiveBendTypes.lean) and
[typing](../Theory/ObjectiveBendTyping.lean) distinguish erased, affine, linear and
unrestricted use, and one-shot from reusable functions. A reusable extension may
capture only values admitted as unrestricted and shareable. Wrapping custody or a
one-shot value in an immutable record, specification or prototype does not make
it duplicable. The repaired composition rule enforces this capture restriction.

The current checker handles an annotated fragment with finite records and
canonical row comparison. It is not a complete dependent type inference or
subtyping implementation. Its future-self/super examples quantify over future
shareable types under explicit row premises; they do not prove arbitrary future
extensions type-correct. Linear syntax currently has an at-most-once use bound:
partial computation may retain a resource indefinitely. A world protocol's
terminal discharge obligation is a separate contract.

A successful `Checked` value contains an actual typing derivation for the erased
term and its use conditions. This establishes what was checked, not preservation
of typing through every machine transition. In particular, full semantic type
preservation and exclusion of every bad operand remain open.

Laws are propositions about behavior, including partial behavior. A total Lean
proof can establish a relational law about a partial program's syntax without
making that program total. `LawProvider` carries such evidence. Retained source
`law` bodies are currently callable declarations, not automatically discharged
proofs. An extension may deliberately change behavior; preserving an earlier law
is an explicit compatibility requirement when the chosen contract demands it.
The extension algebra's retained-law theorem assumes a closed composition that
already satisfies its laws. It does not prove every override preserves them.

## What the machine proofs establish

The source names make the current proof boundary reviewable:

| Result | Actual scope |
| --- | --- |
| `mix_append`, `composition_associative` | Algebraic composition of extensions, with the stated common context and type relationships. |
| `safe_use_bound`, `reusable_capture_member` | Syntactic use bounds and unrestricted/shareable used captures, under the checker's explicit premises. |
| `checked_erasure` | A checked annotated source has the recorded erased-term typing derivation. |
| `ignores_any_partial_argument` | The reference constant function returns its natural result for any argument term, including a divergent one. |
| `stepRaw_lexicalInvariant`, `stepRaw_busyInvariant` | Preservation of the respective invariants by raw machine steps, from their stated preconditions. |
| `stepRaw_preservesOrigins`, `stepRaw_preservesCached` | Existing cell origins and cached values survive raw transitions. |
| `reachable_no_internalRefusal` | A reachable execution of closed scoped source cannot refuse for an unbound variable, missing cell or invalid update. It does not exclude missing fields or wrong operands. |
| `graph_cache_update`, `graph_complete_natural_sound` | Local cache/ground-result correspondence, assuming the substantive `GraphRepresents` relation. |
| `adequate_trace_completion` | An existing terminating raw-machine trace supplies sufficient executor bounds. It does not prove that a source term terminates. |

The [demand invariants](../Theory/ObjectiveBendDemandInvariant.lean),
[adequacy foundations](../Theory/ObjectiveBendDemandAdequacy.lean) and
[typed machine relations](../Theory/ObjectiveBendDemandPreservation.lean) are
separate from a completed general refinement. The `Representation` structure in
the reference semantics specifies simulation, progress, observation and suspension
obligations; defining that structure does not construct an implementation of it.
Full source-elaboration adequacy, graph/source correspondence and completeness,
blackhole/divergence correspondence and all-step type preservation remain open.
Concrete source runs are useful evidence for their actual cases, not substitutes
for those theorems.

## From authored source to a live world

Source capture retains exact module bytes, locked imports, source spans and AST
identities. The preview binds its source, core, typed packet, tools and limits to
its result. Versions matter: the initial qualified lazy-core preview used its own
core/typed wire format; the explicit Boolean-constructor repair changes that
format. It must not reinterpret arbitrary string labels as Booleans or inherit a
previous cohort's qualification merely because the surface edition name matches.

Studio captures editable modules and imports with history, forks and pinned
source. Its served preview runs a selected capture through server-pinned tools,
the actual type checker and the same-term demand executor. Editing a module and
capturing it again produces a new checked preview while retaining earlier preview
history. Results, types and diagnostics retain their source and tooling bindings;
reading a stored preview rechecks current document grants. This received route
uses the frozen wire-v1 tooling; newer wire-v2 tools require separate receiving.
Native storage has also received governed source, pinned instance births and kind
evolution with old instances retaining their old pin and state. New-edition
authored dispatch through call context, current observation, typed effects and
private return remains open.

The common [Plan](../Compiler/BendWorldPlan.lean) describes ordered typed effects,
read guards and independent return slots. The receiving path must bind the actual
execution result to the actual proposed command and check current grants, laws,
source revision, observations, funding and release policy. A typing witness,
source identity or cached executable grants no current authority. Money uses the
conserving account operation; speculative evaluation has no ambient host I/O.

Persistent instances retain identity, state and behavior pins. Persistent
**activities** additionally retain control, environment, heap, pending arguments,
cost position and execution context. The
[persistence contract](BEND-PERSISTENT-COMPUTATION-20261003.txt) covers suspension,
uncertain replies, generation fencing and governed evolution. New lazy-machine
continuations need their own admitted representation and restoration connection;
the existing activity machinery is not automatically a native runner for them.
Restoration must recheck current authority and cannot replay an uncertain external
effect under a new operation identity.

## Execution and privacy

The retained [BendTT profile](../Theory/BendTTSource.lean), adapted from
[upstream revision 947db722](https://github.com/bendlang/bend/blob/947db722640c86247849343657bf2f7ef01cb7f1/bend2/bendtt.lean),
has dependent affine checking and live call-by-value execution. Its
[Workshop linker](OBJECTIVE-BEND-LINKER.md), checked Books and source evaluator
remain useful. They do not establish lazy Objective semantics, and the older
method-prefix linker is not the definition of whole-super extension composition.
Bend and its representations may evolve when concrete programs need it, with
versioned semantics and explicit refinement obligations.

Numeric representation also belongs to the profile. The older source's unary
naturals cannot efficiently carry native 63-bit identities; canonical byte codecs
address that boundary. The new lazy core's natural scalar representation does
not by itself establish an efficient, privately executable arithmetic backend.
Overflow, equality, bounds and charging require explicit contracts.

Native compilation, an oblivious controller, a zkVM, reusable circuits and
homomorphic execution each need a real correspondence to the selected language,
input domain, result and charge. Existing fixed-access closure-machine checks
and the executed Bool/BFV fragment concern their retained profiles and bounded
cases. They do not qualify general lazy Objective programs. A privacy profile
also names permitted observations of branches, memory access, timing, output
shape and failure; encrypted data alone does not hide these. Distributed effects
add agreement, delivery and recovery obligations.

Use the [system map](README.md) and [developer guide](DEVELOPING.md) for surrounding
contracts, and the [dated evidence index](evidence/2026-10-03-objective-bend.md) for
receiving checkpoints. The language guide should change with its contracts and
examples; it is not a per-run status log.

## Design sources

Rideau, Knauth and Amin's
[The Land of the Ultimate Object](https://fare.tunes.org/files/cs/poof/ltuo.html)
develops incremental definitions, heterogeneous extension, final self, whole super
and lazy prototype construction. Rideau's
[orthogonal persistence model](https://github.com/mighty-gerbils/gerbil-persist/blob/master/persist.md)
and [First-Class Implementations](https://fare.tunes.org/files/fci2017/fci.html)
connect live computation, bounded observation and implementation change. These
are design sources; the repository's semantics, theorem premises and actual
receiving paths determine Objective Bend's implemented guarantees.
