# Objective Bend

Objective Bend is Mini's authored language and its only Bend language. Its model
is François-René Rideau's ("Faré") account of object orientation as modularity and
incrementality made available as ordinary in-language computation: **lazy open
recursion over first-class, partial, composable specifications**. Mini supplies
what the language does not: durable identity, current authority, effect admission,
funding and controlled disclosure.

This page has five parts: the language in Faré's terms (what the core has, and what
it lacks, ranked), its formal status, its execution paths and trust boundary, how
surface syntax becomes core terms, and a note on the deleted first generation.
Evidence classes used below: *authored* (source exists), *compiled* (Lean checked
it), *executed* (it ran), *integrated* (a native Host admitted it), *deployed*.

## The language in Faré's terms

### Extensions, self and super

A **specification** is a first-class partial extension `C → V → W`: given the
eventual context `C` (the **final self**) and an inherited value `V` (the **whole
super**), it produces `W`. It can add fields, wrap behaviour, replace a value or
build a function; it is not limited to overriding a method selector, and it is a
value before any target exists (Faré, ltuo §2.1, §5.4.1–4; EOOMI §3.3.5).

Composition passes the same final self to every layer and feeds each layer the
whole result of the layers below it (Faré, poof §1.2.3, §1.3.2):

```text
mix(lower, upper) = λself. λsuper. upper self (lower self super)
```

`fix(spec, inherited)` closes the knot: it is a computation, not an equation
(ltuo §5.3.2). Every value satisfies `x = identity(x)`, yet `fix(identity)`
produces no result; the operational rule is what gives `fix` meaning. Laziness is
part of the meaning, not an optimisation: `{good = 7, bad = self.bad}.good` is `7`,
and an unused divergent argument is never forced (EOOMI §5.1; ltuo §10.3.2).
A **prototype** pairs a specification with its target so that reflection can reach
the specification without forcing the target (ltuo §2.3.3, §6.1.2–4).

### What Core4 has

The core calculus ("Core4") is `Term` in
[ObjectiveBendOpenRecursion](../Theory/ObjectiveBendOpenRecursion.lean). Each
constructor, with its one-line semantics:

| Constructor | Semantics | Faré concept |
| --- | --- | --- |
| `bound i` | de Bruijn variable; the machine enters the heap cell at that environment address | — |
| `lam body` | weak-head value; the machine builds a closure | — |
| `app f a` | call-by-name β in the reference semantics; the machine makes `a` a shared heap thunk (call-by-need) | laziness, shared suspensions |
| `mix lower upper` | steps to `λself.λsuper. upper self (lower self super)` | mixin composition, one final self, whole super |
| `fix spec inherited` | steps to `spec (fix spec inherited) inherited`; the machine ties one heap address to itself | fixpoint as computation |
| `specification metadata extension` | value; applying it applies `extension`; `metadata` is reachable without forcing the extension | first-class partial specification |
| `prototype spec target` | value pairing a specification with its target | conflation of spec and target |
| `reflect` / `metadata` / `project` | eliminators: spec of a prototype, metadata of a spec, target of a prototype, each without forcing the other part | reflection (partial) |
| `nat n`, `boolean b`, `label s` | scalars; labels are opaque strings | — |
| `binary p l r` | strict, left to right; `p` ∈ {add, multiply, equal (Nat → Bool), conjunction (Bool)} | — |
| `record fields` | fields are separate suspensions; lookup takes the first match | records of suspensions (slots and methods are not distinguished) |
| `extend inherited fields` | defined only when `inherited` is a record; new fields shadow | method override |
| `get t name` | field selection by a static name | — |
| `ifZero v z s` | case on a Nat; the successor branch binds the predecessor | — |
| `inject l p`, `case s arms`, `ifBool c t f` | sums: a lazy injection, case on its label (first matching arm), the Boolean branch | variants, lists, branching |
| `perform plan`, `done v` | an activity yields a typed Plan and is resumed with a typed response; `done` returns a pure value from an activity | effects as yield ([activities and events](OBJECTIVE-BEND-EVENTS.md)) |

**Types and quantities** ([Types](../Theory/ObjectiveBendTypes.lean),
[Typing](../Theory/ObjectiveBendTyping.lean)). `check` is proof-producing: it returns
a typing derivation for the actual term. Rows are compared canonically; there is
no subtyping, and type equality is exact up to one bounded head unfolding. Rigid
type variables carry explicit bounds and keep row tails, so a method can be typed
against a future self it has not seen (ltuo §8.2.1–4). `fix` is typed
homogeneously (`target → inherited → target`); heterogeneity lives only in `mix`.
Quantities are erased, affine, linear and unrestricted; the checker enforces
at-most-once for both affine and linear (not exactly-once), and a reusable closure
may capture only unrestricted, shareable bindings. Nothing creates a custody value,
so `Ty.custody` is unused by any closed program.

The whole package is one lazy fixpoint: every global declaration is a field of one
record knot, so mutually recursive definitions (the `EvenOdd` example) work through
it. That is Faré's "global fixed point of the namespace" (ltuo §9.3.7), except that
the root ignores `super` and is not itself a specification, so another package
cannot extend it.

### An example

[ReviewBase](../tests/objective-bend-source/ReviewBase.obend) declares a `Review`
record and a `Base` spec. [ReviewMember](../tests/objective-bend-source/ReviewMember.obend),
written separately, imports it and adds `Twice` (which uses `self.review`) and
`Augmented` (which wraps `super.review`):

```text
def review(inherited: Prior.Review) -> Prior.Review:
  fix(compose(Prior.Base, Twice, Augmented), inherited)
```

`twice` sees the final, augmented `review` through self, so `twice(3)` reads as
`7`. That is the expected value read from the source (authored); the generated driver
[reference/Review.lean](../examples/objective-bend-world/reference/Review.lean)
prints the machine's final state with no assertion, and because the package declares
specs it cannot reach the typed preview today (see the front-end defects below).
Smaller probes in
`tests/objective-bend-source/` separate the lazy cases (`LazyUnusedArgument`,
`LazyUnusedField`, `LazySharedField`), heterogeneous extension (`Heterogeneous`),
captured reusable extensions (`GenericExtension`) and reflection of an incomplete
prototype (`ReflectLazyPrototype`).

### What Core4 lacks: the roadmap

Ranked by how much later work each one unblocks. *Elaboration* means expressible
by compiling into existing constructors; *core* means new constructors, new machine
frames and new preservation and adequacy cases.

Landed since this list was written: **sums with case** (`inject`, `case`,
`ifBool`, `labelEqual`; design [SUMS-DESIGN.txt](../SUMS-DESIGN.txt)) and **an
activity** (`perform`/`done`, a yielded machine state with a resume rule, effects as
a type, an effect never inside a forced shared thunk, and a checkpoint codec with a
proved round trip; [activities and events](OBJECTIVE-BEND-EVENTS.md)).

1. **Kernel delivery of activities** (integration). The kernel admits a yielded
   Plan, persists the checkpoint in the activity record, resumes with a typed
   response under one generation per resume. Not built.
2. **A guardedness check** (typing). Every self-call of a resident under a perform,
   so that a well-typed resident never diverges inside a turn.
3. **Declared ancestry with C4 linearization and method combination**
   (elaboration; poof §4.3; ltuo §7.3–7.4, §9.2). Today `compose(a, b, c)` is a left
   fold of `mix`: mixin inheritance, which ltuo §11.1.8 ranks below the two
   multiple-inheritance forms. No dependency DAG, no generative identity, so a
   diamond cannot count once. A static DAG can be linearized at elaboration with no
   new constructors; it needs its own theorem (invariance under renaming of the
   ordered presentation, and suffix soundness).
4. **Checked `requires` and closed final-self assumptions** (typing rules only;
   ltuo §8.2). `requires` survives only as a JSON string inside the metadata label.
   Checking the required row against the composed provided row at `fix` turns
   partial specifications into checked collaborations.
5. **An extensible package root, label equality and dynamic `get`** (ltuo §9.3.7,
   §9.2.9; Houyhnhnm ch.7). Root as a specification is elaboration; label equality is
   a primitive; dynamic `get` is one constructor. Makes "extend what you do not own"
   true.

Further gaps, unranked: sealing, `final` and suffix declarations (ltuo §9.4.4.1,
§10.4.2), which are what let a backend reduce dynamic dispatch to static; reflection
beyond `reflect`/`metadata`/`project` (field enumeration, has-field), which must wait
for a decision on what reflection may observe, because every observer forbids an
optimisation (ltuo §10.7); a consumed mark for linear values in the heap; fresh
persistent instances (poof §1.3.1), which are Mini's identity rather than a core
construct; governed live upgrade (Houyhnhnm ch.5; ltuo §6.3.2); and a canonical cost
law on the machine.

### Relation to Preoscript

Preoscript (in the separate `lean-uwueave` library) is a contract language about
promises over replicated state: invariants, future-indexed certificates, status,
coordination obligations. It has nothing about self, super or open recursion, and
Core4 has nothing about futures or merge; the two do not overlap at the constructor
level. They meet at Core4's weak spots: laws kept separate from authority, `requires`
checked at compose and fix, and a Plan as data. Preoscript is a contract language
Core4 specifications should carry and check, not a projection target to emit. An
ordered override can delete an obligation, so the obligation profile of a `mix` is
not simply a sum; that needs a theorem.

## Formal status

The proofs are in `Theory/ObjectiveBend*.lean` (compiled). Every theorem below has
`#print axioms` pinned to `propext`, `Classical.choice` and `Quot.sound`; there is
no `sorry`, `axiom`, `native_decide`, `partial` or `extern` in those files.

### What is proven

| Theorem | In plain words | Hypotheses |
| --- | --- | --- |
| `sourceStep_deterministic` | The reference step relation is deterministic. | none |
| `runBounded_natural_sound`, `_boolean_sound`, `_label_sound` | If the bounded machine finishes a source term with a scalar, the reference semantics evaluates that term to the same scalar. | the term is closed (`Scoped 0`, met by every elaborated program); the run finished. Holds for every heap/stack limit and tick count. |
| `runBounded_value_sound` | A finished run of any value (closure, record, spec, prototype) has a meaning for every heap address, the final heap realizes it, and the source evaluates to the returned value's meaning. Weak-head only. | closed; finished |
| `runBounded_observes_sound`, `runBounded_observation_sound`, `runBounded_resource_independent` | Ground observations of finished runs agree with the reference semantics, and two finished runs under different limits observe the same result. | closed; finished |
| `typed_stepRaw_preserved` | Every raw machine step preserves heap, control and stack typing, over an address typing that only grows. | a typed state (`checked_initial_state` builds one from any `Checked` term) |
| `checked_reachable_no_refusal`, `check_runBounded_no_refusal` | A closed term the checker accepts never reaches any refusal (wrong operand, missing field, unbound reference, an effect inside a forced shared thunk), for every limit and tick count. Divergence, blackholes and resource suspension remain possible. | `Checked source []` |
| `reachable_no_internalRefusal` | Closed scoped executions never refuse for an unbound variable, a missing cell or an invalid update. | closed |
| `typed_yield_quiescent`, `stack_activity_signature`, `typed_resume_preserved` | A typed yield forces no shared cell and has no half-evaluated cell; it carries the program's own Plan/Response types; resuming it with a closed response of that type gives a typed state. | a typed state; the response typed at the program's Response type |
| `state_roundTrip` | The checkpoint codec restores every machine state exactly. | none |
| `mix_append`, `composition_associative` | Folding a list of homogeneous extensions distributes over append, and specification composition is associative, on the list model in `ObjectiveBendExtensions`. | none; but it is a separate model, and no theorem ties it to `Term.mix` |

The no-refusal theorems are about the same function the preview runs: the preview
calls `check` on the empty context and then `runBounded` on the same decoded term.

### What is open

- **Completeness.** That a source term which evaluates makes the machine finish,
  given enough resources. `adequate_trace_completion` sounds like it and is not: its
  premise is that the unbounded run already finished, and it concludes only that
  bounded limits suffice. `Representation`, the structure that would package
  soundness, completeness and observation, has no instance; nothing in its type
  stops a degenerate `Supported := fun _ => False` instance, only its docstring.
- **`forceWith`/`executeWith` ≡ `runBounded`.** The Plan path does not run
  `runBounded`. It runs `executeWith` under a capacity policy, which repeatedly calls
  `forceWith` and then `materializeWith` to extract deep Data. No theorem mentions
  `forceWith`, `materializeWith`, `executeWith` or `allows`.
- **Deep Data soundness.** The extracted first-order Data that becomes a Plan has no
  theorem relating it to the source meaning.
- **Front-end adequacy.** No theorem relates `.obend` source to the core term (see
  [the trust boundary](#the-trusted-front-end-boundary)).
- **Quantities at run time.** Use counts are static only; no theorem says a value is
  used at most once at run time.

Some facts read like semantics and are not: `TotalProof law := law`; the prepared
output's `native_matches` and `no_returns`, and `checked_erasure`, are field
projections; `ExecutionWith.runExact` records that a value is the output of the very
call that produced it. Spec `law`s are callable closures stored in metadata; nothing
discharges them.

### What the default build checks

At c8fdd000 the `Theory/ObjectiveBend*` modules are imported only by the opt-in
`ResearchWip` library. `Theory.lean`, the default `Minidregg` target and
`BendQualification` do not import them, and `Host/ObjectiveBendPreview` imports only
`Typing` and `DemandMachine`. A green default build therefore re-checks none of the
proofs above. Bringing them into a default gate is configuration, not proof work.

### The honest label for executed results

Until `forceWith ≡ runBounded` and deep Data soundness are proved, a Plan or result
produced on the native path is **"Core4 `executeWith` output"**: what the evaluator
computed, re-executed deterministically at admission and on every replay. It is not
"the meaning of the source".

## Execution paths

### Preview: `runBounded`

Studio's preview runs: Rust `native/resource-client/src/workspace/studio_preview.rs`
spawns bun; `objective-frontend.ts` captures the package and `objective-parser.ts`
parses it; `objective-preview.ts` runs `objective-elaborate.ts`, writes the core and
typed packets and checks that the typed term equals the core term; then
`lean --run Host/ObjectiveBendPreview.lean` decodes the packet, runs `check`, then
`runBounded`. This is the function the soundness and no-refusal theorems describe.
On main the route is wire-broken: the Rust side writes `preview-input.v1` and accepts
only `preview-result.v1`, while the in-tree TypeScript requires `preview-input.v2`
and emits `preview-result.v2`. The fix (Rust speaking v2, v1 deleted) exists in a
lane and has not landed. To drive the tools directly from the repository root:

```sh
bun native/bend-source/objective-frontend.ts \
  tests/objective-bend-source/GenericExtension-package.json NEW_CAPTURE_DIR
bun native/bend-source/objective-preview-request.ts \
  NEW_CAPTURE_DIR/objective.json NEW_REQUEST_JSON '["7"]' '[]'
bun native/bend-source/objective-preview.ts \
  NEW_REQUEST_JSON NEW_RESULT_DIR PINNED_TOOLING_CONFIG
```

The tooling config pins compiled tools and semantic modules; a fresh checkout does
not contain one. Schemas: [capture](OBJECTIVE-BEND-FRONTEND.md),
[preview](OBJECTIVE-BEND-PREVIEW.md). The preview carries `authority: none`.

### Native admission

A member invocation of an Objective method is designed to reach an accepted
receipt through the ordinary native path; Objective needs no new receipt type. The
path, most of it assembled in lanes and not yet one coherent build: Studio
publishes the source package and its elaborated core as two content atoms in one
ordinary invocation; the caller builds a claim naming the artifact atom, arguments,
input references and a capacity envelope, and the client signs it as an invocation
with family `objectiveMethod` (that Rust half is on main). The Host pins the operator
policy for Objective into its runtime parameters. `ResourceTransaction.prepareFrom`
decodes the claim and prepares compute funding; `DeclaredResourceController.admit`
dispatches to Objective admission, which checks every signature and capability
first, then the policy, the selected artifact and package pins, the inputs against
the claim's commitment, the typed check of the applied term, and runs `executeWith`,
lowers the result to a Plan and requires the Plan's effects to equal the command's
effects exactly. Commit and receipt are the existing durable path; on reopen the
Host re-executes the program during replay. **On main, no Objective Bend source has
produced a native accepted receipt.** The admission modules
(`Kernel/ObjectiveBendNativeAdmission`, the claim, the published-package lookup, the
family-aware controller) compiled in lanes against a mixed file set and are being
integrated into one coherent build. Known design holes on that path: the claim's
`proofWork` is chosen by the caller and nothing relates it to measured work (zero
work means free execution up to the policy maximum); the policy's elaborator pin is
checked for hex format only; the route's guard list is empty for every route.

### The trusted front-end boundary

Trusted (no theorem; checked only by replay):

- the TypeScript parser, capture and elaborator (`objective-parser.ts`,
  `objective-frontend.ts`, `objective-elaborate.ts`) and `literalAnnotations`;
- the package capture and fingerprint tooling; `ObjectiveSourcePackage.wellFormed`
  is structural only;
- source-to-core correspondence: native loading establishes a live, immutable,
  canonical package and a typed core term, not that the core is what the source
  says. A third party who publishes benign source with a different core is caught
  only by a signer who replays the elaboration (publication compares the offered
  core with an independent replay);
- the elaborator pin, which binds nothing until the package carries a lowerer hash
  that admission compares;
- spec laws (closures, never checked); affine and linear quantities, which the front
  end cannot produce;
- the meaning of a Plan extracted from deep Data, until the two open theorems above
  exist.

Not trusted, because native admission re-executes it: argument JSON to `Term`
(bounded, canonical), the typed check, `executeWith`, the exact effect match,
authority and funding.

## Execution and privacy

The lazy semantics is the target for native, oblivious, proof-producing and
homomorphic execution; on main none of those routes runs Objective Bend. The
oblivious-execution and circuit families (`BendOblivious*`, `BendLogic*`,
`BendNatural*`) target the retiring BendTT machine. The zk statements for Objective
(`Assurance/ObjectiveBendCommittedSource`) are conditional on a `PackedRefinement`
hypothesis that nothing inhabits for a real program. The FHE route that runs today
evaluates a public natural-number expression, not an Objective method. Laziness
leaks through access pattern and timing: forcing order and cache state are
data-dependent. So a private backend needs a both-arms (mux) lowering of `case` and
an explicit public resource bound; the type system already keeps every effect out of
forced shared thunks.
Source `Nat` is unbounded; a native or circuit backend needs a bounded domain that
fails stop, never wraps. A private profile names observers and permitted leakage
(code, branches, memory access, timing, output shape, failure); encryption alone
hides none of these.

## Surface → core elaboration

`objective-elaborate.ts`, as it is:

| Surface | Core |
| --- | --- |
| global declarations | fields of one record knot: `fix (λglobals λseed. record{Module.name: …}) (record [])`; a global reference is `get globals "Module.name"` through the tied address |
| `def f(x…) -> T: body` | nested `lam`s with binder hints and annotations |
| `extension(self, super) -> T: e` | `lam lam e`, typed `T → T → T` (homogeneous) |
| `spec S for T: …` | `specification (record{name, interface: <signatures as a JSON label>, laws: record of law closures}) (λself λsuper. extend super {methods})` |
| `compose(a, b, c…)` | left fold to `specification (record{operator, inherited: v, wrapping: r}) (mix v r)` |
| `fix(s, i)`, `extend(x, {…})` | `fix`, `extend` |
| `prototype`, `reflect`, `metadata`, `targetOf` | `prototype`, `reflect`, `metadata`, `project` |
| `x.f`, `f(a, b)`, `()` | `get`, curried `app`, `record []` |
| `+ * == &&` | `add`, `multiply`, `equal`, `conjunction` |
| `match n: case 0n / case 1n+p` | `ifZero`; exactly those two branches |
| `sum S: …`, `S.l(e)`, `match s: case l(x): …`, `if c then a else b` | `inject`, `case` (exhaustive), `ifBool` |
| `-> Activity<P, R, A>`, `perform(plan)`, `match perform(…): case l(x): …` | `perform`; a pure tail becomes `done`; the match is the same `case`, typed as an effect case |
| `true`/`false`, strings, `7n` | `boolean`, `label`, `nat` |

Arguments and fields stay thunks; laziness is preserved.

Known front-end defects:

- `compose` copies `v` and `r` syntactically into both the metadata and the `mix`,
  so term size grows as 2^k in the number of composed specs, and the inherited
  composite is not shared between the copies.
- `literalAnnotations` throws for any `spec` declaration anywhere in the package, so
  a package that declares a spec (EvenOdd, Review, the lazy-specification probes)
  cannot produce a typed packet, even when the entry never uses the spec. Spec method
  lambdas get no binder hints.
- `!= < > <= >= || - /` parse but are refused at elaboration.
- `match` refuses wildcards.
- Quantities map `default`/`copy` to unrestricted and `dead` to erased; the surface
  cannot express affine or linear.
- `requires` is carried as a string and never checked; the parser's `record`
  declaration is skipped by the elaborator.
- The parser still accepts `./NAME.bend` imports.

The generated drivers in `examples/objective-bend-world/reference/` are untyped,
print state without assertions, and some are stale against the current elaborator
(EvenOdd encodes Booleans as labels).

## What was Gen-1, and why it is gone

The first generation elaborated this OO surface into checked BendTT Books
(`Compiler/ObjectiveBendLinker`, `ObjectiveBendElaboration`, the Workshop and its
instance loaders), which bound the language to the restrictions of that embedding:
data-only reusable captures, acyclic linking and total strict calls. On 2026-10-03
Objective Bend became its own lazy language with Core4 as its only core, and Gen-1
was deleted on 2026-10-04 so that its claims (pinned instance births, kind
evolution, a persistence contract over the strict closure machine) stop being read
as claims about Core4.

## Sources

Faré's work cited above, by short name:

- **ltuo**: Rideau, Knauth and Amin, *The Land of the Ultimate Object*
  (<https://fare.tunes.org/files/cs/poof/ltuo.html>).
- **poof**: *Prototypes: Object-Orientation, Functionally*
  (<https://fare.tunes.org/files/cs/poof.pdf>).
- **EOOMI**: *The Essence of Object-Orientation: Modularity and Incrementality*,
  2024 draft (<https://fare.tunes.org/files/cs/poof/eoomi2024.pdf>).
- **Houyhnhnm**: *Houyhnhnm Computing*, chapters 1–11
  (<https://ngnghm.github.io/>).
- **FCI**: *First-Class Implementations* (<https://fare.tunes.org/files/fci2017/fci.html>)
  and *Climbing* (<https://fare.tunes.org/files/climbing/climbing.html>).
- **Persistence model**: gerbil-persist
  (<https://github.com/mighty-gerbils/gerbil-persist/blob/master/persist.md>).

The original Bend calculus remains pinned in `vendor/bend` and
`Theory/BendTTSource.lean` as a reference only; strict-machine proofs say nothing
about the demand machine.

These are design sources. The repository's semantics, theorem premises and admitted
receiving paths determine what Objective Bend guarantees.
