# Objective Bend

Objective Bend is Mini's authored language for a shared, governed computing
world. People and agents should be able to define tools, documents, services and
worlds, extend one another's behavior, inspect the resulting programs, and retain
instances and activities across sessions. Its language model is **lazy open
recursion with first-class reusable extensions**. Mini supplies durable identity,
current authority, effect admission and controlled disclosure around execution.

Objective Bend is the project's sole Bend language target. It has its own source
syntax, reference semantics, shared thunk machine and annotated type checker.
Captured source runs through that checker and machine, including in Studio. The
machine now has general soundness theorems connecting successful executions to
the independent lazy reference semantics. Native source storage and pinned
instances exist; complete authored dispatch and effect admission are being
connected to this language. Older strict-backend code is migration work, not an
alternative language developers should target.

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

A **specification** retains an extension and inspectable requirements and laws.
Partial specifications are values: inspection need not complete their requirements
or instantiate a target. A **prototype** pairs a specification with its target.
Generic `fix` returns the target directly; explicit prototype construction places
the wrapper inside the knot when reflection through self is required.

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
examples have passed the current explicit-Boolean wire-v2 route, as well as the
older wire-v1 cohort. Wire-v2 keeps Boolean `true` distinct from String `"true"`
and refuses String conjunction. Match the configuration to the request's wire
version. Unsupported annotations produce diagnostics;
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
work and storage behavior relative to the reference reduction. Successful machine
results have a proved reference meaning; the reverse direction—completeness—and
a general account of divergent execution remain open.

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
term and its use conditions. The
[typed transition proofs](../Theory/ObjectiveBendDemandPreservation.lean) establish
`typed_stepRaw_preserved` for every demand-machine constructor. Allocation
extends the address assignment while preserving each existing address's type;
lexical origins and continuation frames retain their quantity and shareability
evidence, including captured closures, composition and cyclic `Fix`.

For closed checked source, `checked_reachable_no_refusal` excludes wrong operands,
missing fields and internal-reference refusals throughout raw-machine execution.
`check_runBounded_no_refusal` connects actual checker success to the same erased
term and bounded executor, for arbitrary tick, heap and stack limits. Evaluation
may still diverge, encounter a blackhole or suspend for resources. These safety
results do not establish runtime custody conservation or terminal discharge.

Laws are propositions about behavior, including partial behavior. A total Lean
proof can establish a relational law about a partial program's syntax without
making that program total. `LawProvider` carries such evidence. Retained source
`law` bodies are currently callable declarations, not automatically discharged
proofs. An extension may deliberately change behavior; preserving an earlier law
is an explicit compatibility requirement when the chosen contract demands it.
The extension algebra's retained-law theorem assumes a closed composition that
already satisfies its laws. It does not prove every override preserves them.

## What execution proves

The [demand-machine soundness theorems](../Theory/ObjectiveBendDemandAdequacy.lean)
cover **every closed source term that the actual bounded executor finishes**.
For any heap/stack limits and tick budget, if `runBounded` from `initial source`
returns a natural, Boolean or String, the independent reference semantics
`Evaluates` returns that same scalar. These results require source scope and the
actual finished execution. They do not require a caller-supplied graph simulation
witness, a typing token or a special supported-program subset.

`runBounded_value_sound` also covers functions and structured results: it
constructs closed meanings for heap addresses, proves the final heap realizes
them, and derives reference evaluation to the returned value's meaning. It does
not establish external contextual equivalence. The main source entry points are:

| Result | Actual scope |
| --- | --- |
| `mix_append`, `composition_associative` | Extension composition with the stated common context and type relationships. |
| `safe_use_bound`, `reusable_capture_member`, `checked_erasure` | Checked syntactic use/capture conditions and an actual erased-term typing derivation. |
| `ignores_any_partial_argument` | The reference constant function returns its natural result for any argument term, including a divergent one. |
| `stepRaw_lexicalInvariant`, `stepRaw_busyInvariant` | Raw transitions preserve the respective pre-invariants. Origins and existing cached values are also preserved. |
| `reachable_no_internalRefusal` | Closed scoped executions cannot refuse for an unbound variable, missing cell or invalid update. Missing fields and wrong operands are different cases. |
| `runBounded_natural_sound`, `runBounded_boolean_sound`, `runBounded_label_sound` | Any actual finished scalar run of closed source agrees with independent reference evaluation. |
| `runBounded_value_sound`, `runBounded_observes_sound` | Finished values have a realized reference meaning; finished ground results have the corresponding reference observation. |
| `typed_stepRaw_preserved` | Every raw-machine constructor preserves typed heap, control and continuation frames under its state-typing premises, with a monotonically extended address assignment. |
| `checked_reachable_no_refusal`, `check_runBounded_no_refusal` | Closed checked erasures cannot reach raw refusals or return bounded-executor refusals, including wrong operands and missing fields. Divergence, blackholes and resource suspension remain possible. |
| `adequate_trace_completion` | An existing terminating raw-machine trace supplies sufficient executor bounds. It does not establish termination of an arbitrary source program. |

The [invariant proofs](../Theory/ObjectiveBendDemandInvariant.lean) support the
soundness result; [typed transition proofs](../Theory/ObjectiveBendDemandPreservation.lean)
address a separate safety obligation. Source-elaboration adequacy, completeness
of the shared machine relative to reference evaluation, administrative progress,
and blackhole/divergence correspondence remain open.
In particular, reference termination has not yet been shown to guarantee machine
termination with sufficient resources. The `Representation` structure in the
reference semantics records the larger implementation contract; the completed
soundness direction alone does not inhabit that whole contract.

## From authored source to a live world

Source capture retains exact module bytes, locked imports, source spans and AST
identities. The preview binds its source, core, typed packet, tools and limits to
its result. The current core and typed wire format has distinct Boolean and
String constructors; source edition and runtime wire version are separate
identities. Earlier captured artifacts keep their interpretation rather than
silently adopting a changed representation.

Studio captures editable modules and imports with history, forks and pinned
source. Its served preview runs a selected capture through server-pinned tools,
the actual type checker and the same-term demand executor. Editing a module and
capturing it again produces a new checked preview while retaining earlier preview
history. Results, types and diagnostics retain their source and tooling bindings;
reading a stored preview rechecks current document grants. Studio now accepts
explicit wire-v1 or wire-v2 preview selection within Objective source edition 1,
using separate server-pinned configurations. Wire-v2 carries tagged arguments:
Boolean `true` and String `"true"` retain their distinct types and results, and
incompatible source or arguments are refused by the actual checker. Earlier
captures and preview history keep their original tooling interpretation.
Native storage has received governed source, pinned instance births and kind
evolution with old instances retaining their old pin and state.

The [prepared-output path](../Kernel/ObjectiveBendPreparedOutput.lean) now checks
closed annotated source, executes that same term, and fully demands its returned
data under a shared root-and-field budget. The
[scalar Plan adapter](../Compiler/ObjectiveBendPlanAdapter.lean) decodes the exact
record schema and binds it against the actual loaded native directory and
command. This has run on a real loaded directory, including refusal of a stale
command, mismatched resource root and wrong prior scalar value. `native_matches`
proves that the bound Plan matches the command; `no_returns` states that this
slice has no return slots. Previewing a lazy record's field names alone would not
establish any of these properties.

The common [Plan](../Compiler/BendWorldPlan.lean) supports ordered typed effects,
read guards and independent returns, but the current Objective adapter implements
the narrower scalar-write slice. A `BoundPlan` is a checked proposal, not an
accepted effect or receipt. The complete receiving path must additionally bind
source and invocation identity and check current grants, governing laws, funding,
profile/capacity and release policy before admission. General authored method
dispatch, private returns and the full effect family remain to be joined. Source
identity, a typing proof and a cached executable confer no authority; speculative
evaluation has no ambient host I/O. Money requires the conserving account
operation, not a raw scalar balance write.

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

Objective Bend's lazy semantics is the target for native compilation, bounded
oblivious execution, proof systems and homomorphic execution. Each implementation
must relate its actual input, result, resource behavior and disclosure to this
language. The reference semantics and shared demand machine are the starting
point for that work.

Older BendTT and call-by-value backend machinery is being removed or migrated
into this sole target. Its proofs—even general decoded-output soundness—and
strict-machine circuit/BFV experiments do not qualify lazy Objective execution.
Useful representations and proof infrastructure need an explicit Objective
refinement before they can support that claim.

Natural scalars, native identifiers and private arithmetic need explicit
representations. Canonical byte codecs can transport identities without unary
expansion; they do not themselves implement arithmetic. Word bounds, overflow,
equality, charging and backend numeric domains cannot silently change the source
promise.

A private execution profile names observers and permitted leakage from code,
branches, memory access, timing, output shape and failure. Encryption alone does
not hide those observations. A zkVM or reusable circuit must verify the exact
program/result relation; homomorphic execution also needs a qualified arithmetic
and key/noise model. Private result custody, release authority and outcome agreement remain separate.
Distributed effects also require real delivery, reservation and recovery.

Use the [system map](README.md) and [developer guide](DEVELOPING.md) for surrounding
contracts, and the [dated evidence index](evidence/2026-10-03-objective-bend.md) for
receiving checkpoints. Update this guide with changes to its contracts and examples; keep individual
receiving runs in the evidence index.

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
