# Objective Bend

Objective Bend is Mini's authored language and its only Bend language. Its model
is François-René Rideau's ("Faré") account of object orientation as modularity and
incrementality made available as ordinary in-language computation: **lazy open
recursion over first-class, partial, composable specifications**. Mini supplies
what the language does not: durable identity, current authority, effect admission,
funding and controlled disclosure.

This page has five parts: the language in Faré's terms (what the core has, and what
it lacks, ranked), its formal status, its execution paths and trust boundary (the
preview, native admission, the kernel's activities, objects and seats, and the laws that
judge them), how surface syntax becomes core terms, and a note on the deleted first
generation.
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
| `binary p l r` | strict, left to right; `p` ∈ {add, multiply, equal (Nat → Bool), conjunction (Bool), labelEqual (label → Bool)} | — |
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
it. That is Faré's "global fixed point of the namespace" (ltuo §9.3.7). The root is
itself a specification, `fix(specification(package, λglobals λseed. extend seed
{…}), {})`: its extension overlays the declarations on the inherited row
(`Compiler/ObjectiveBendElaborate.lean`, the package knot in `elaborateM`), so a
package is an extensible value in the core. No surface form yet names another
package's root, so another package still cannot extend it from source.

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
`7`. [reference/TwiceReview.lean](../examples/objective-bend-world/reference/TwiceReview.lean)
embeds the typed packet the front end produces for the source, and pins the result
`7` (checked type `natural`, no uses) as a `native_decide` theorem under
`scripts/check-objective-examples.sh`.
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
`ifBool`, and the `labelEqual` primitive; design [SUMS-DESIGN.txt](../SUMS-DESIGN.txt)),
**an activity** (`perform`/`done`, a yielded machine state with a resume rule, effects as
a type, an effect never inside a forced shared thunk, and a checkpoint codec with a
proved round trip; [activities and events](OBJECTIVE-BEND-EVENTS.md)) and its kernel
half (persisted records, answer slots, the resume contract, resume with a view of the
object's state, paid exhaustion and disposal; compiled and proved, no native route yet),
**declared
ancestry with C4 linearization and method combination** in the elaborator (`spec S
extends A, B`, `suffix spec`, `around`, `combine`; a diamond's shared ancestor counts
once; [front end](OBJECTIVE-BEND-FRONTEND.md#declared-ancestry-and-method-combination)),
and **the package root as a specification**.

1. **A native route for activities** (integration). The kernel's turns are built and
   proved (publish, create, birth, resolve, deliver, exhaust, abandon, topUp, writeState;
   [the kernel activity](OBJECTIVE-BEND-EVENTS.md#the-kernel-activity)), but no Host
   operation reaches them: `Kernel.ObjectiveActivity` is not in the Host closure
   (`scripts/gates/host-closure.pin`). In flight: ACTIVITY-ROUTE.
2. **A guardedness check** (typing). Every self-call of a resident under a perform,
   so that a well-typed resident never diverges inside a turn.
3. **The theorem for declared ancestry** (proof; poof §4.3; ltuo §7.3–7.4, §9.2). The
   elaborator linearizes a declared static DAG with C4 and builds the `mix` chain from
   it, with no new constructors (see "landed" above). What is missing is the theorem:
   invariance under renaming of the ordered presentation, and suffix soundness.
   `OrderedPresentationInvariant` (`Compiler/ObjectiveBendC4.lean`) is stated as a
   `Prop` and not proved; the evidence is `Compiler/ObjectiveBendC4Vectors.lean`
   (56 published precedence vectors and 4000 seeded random DAGs, compiled theorems). `before` and `after`
   methods are still refused by the elaborator; Core4 has `perform` now, so they are
   buildable and not built.
4. **Checked `requires` and closed final-self assumptions** (typing rules only;
   ltuo §8.2). `requires` survives only as a JSON string inside the metadata label.
   Checking the required row against the composed provided row at `fix` turns
   partial specifications into checked collaborations.
5. **Dynamic `get`, and a surface form that names another package's root** (ltuo
   §9.3.7, §9.2.9; Houyhnhnm ch.7). The root is a specification and label equality is
   a primitive (both landed); dynamic `get` is one constructor. Makes "extend what you
   do not own" true.

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

The proofs are in `Theory/ObjectiveBend*.lean` (compiled, in the `ObjectiveProofs`
library). Every theorem's exact axiom set is pinned in `scripts/gates/objective-axioms.pin`
(each set is within `propext`, `Classical.choice`, `Quot.sound`; none uses `sorryAx` or
`Lean.ofReduceBool`) and its statement in `scripts/gates/objective-statements.snapshot`;
there is no `sorry`, `axiom`, `native_decide`, `partial` or `extern` in those files. The
compiled machine runs through proven-equal `@[csimp]` replacements
(`Theory/ObjectiveBendDemandMachineFast.lean:77`, `:171`, `:207`; `forceWith_eq_fast`,
`Theory/ObjectiveBendDemandData.lean:54`): the compiler's substitution is trusted, the
equalities are theorems.

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
| `machine_evaluation_complete` (from `rawRun_finite_completion`) | Completeness: a closed source that the reference semantics evaluates to a value with a ground observation is finished by the machine with that observation, in finitely many transitions. `coreRepresentation` inhabits `Representation` (soundness, completeness, observation) for every closed source. | `Scoped 0 source`, `Evaluates source value`, `Observes value result`; the machine step is the bounded `step` at limits that admit each next transition. |
| `forceWith_unrestricted`, `forceWith_policy_suspends` | `forceWith` under the always-true policy is `runBounded`; any other policy can only stop early with a capacity suspension that retains the state the unrestricted bounded run had reached at that point. | none |
| `materialize_sound`, `execution_source_semantics` | The Plan path is source semantics: a successful `executeWith` on a closed term, under any policy, limits and budget, is a finished `runBounded` of the same term, and the extracted Data is a deep reference evaluation (`DeepEvaluates`) of the source term. | `Scoped 0 term`; an `ExecutionWith` value |
| `mix_append`, `composition_associative` | Folding a list of homogeneous extensions distributes over append, and specification composition is associative, on the list model in `ObjectiveBendExtensions`. | none; but it is a separate model, and no theorem ties it to `Term.mix` |

The no-refusal theorems are about the same function the preview runs: the preview
calls `check` on the empty context and then `runBounded` on the same decoded term.

### What is open

- **A resource bound for completeness.** `machine_evaluation_complete` gives finite
  completion, not a bound on the limits that suffice. `adequate_trace_completion` is
  not it either: its premise is that the unbounded run already finished, and it
  concludes only that bounded limits suffice. `Representation` is inhabited
  (`coreRepresentation`) at `Supported := Scoped 0`, closedness; nothing in its type
  stops a degenerate `Supported := fun _ => False` instance, so what makes the
  instance mean something is that `Supported` is the real admission predicate, which
  is a reading of the definition, not a theorem; the non-vacuity theorems are
`lazyFixedSeed_supported_by_representation` and `open_term_not_started`. (The docstring on `Representation`, `Theory/ObjectiveBendOpenRecursion.lean:361-365`, still says "no instance is claimed here"; `coreRepresentation` at `Theory/ObjectiveBendDemandCompleteness.lean:1127` is the instance.)
- **Uniqueness of deep Data.** `DeepEvaluates` relates the extracted Data to the
  source term. No theorem says the Data is the only Data it relates to, so "the Data"
  means "a deep evaluation", not "the unique one".
- **`OrderedPresentationInvariant`.** The C4 renaming-invariance statement is a `Prop`
  that nothing proves (see the roadmap).
- **Front-end adequacy.** No theorem relates `.obend` source to the core term (see
  [the trust boundary](#the-trusted-front-end-boundary)).
- **Quantities at run time.** Use counts are static only; no theorem says a value is
  used at most once at run time.
- **Forcing transparency.** The kernel stores the checkpoint of the Plan extraction's
  state, not of the machine's own yielded state. That resuming it is equivalent is
  proved only under the open premise `ForcingTransparent`
  (`Kernel/ObjectiveResumeContract.lean:501`), which has a satisfying instance and
  refuting ones (`:506`, `:652`, `:310`); the `transparency` gate compares the two
  by execution ([activities and events](OBJECTIVE-BEND-EVENTS.md#the-resume-contract)).

Some facts read like semantics and are not: `TotalProof law := law`; the prepared
output's `native_matches` and `no_returns`, and `checked_erasure`, are field
projections; `ExecutionWith.runExact` records that a value is the output of the very
call that produced it. Spec `law`s are callable closures stored in metadata; nothing
discharges them.

### What the default build checks

The `Theory/ObjectiveBend*` definition modules (term syntax, types and checker, the
demand machine and its data and capacity layers) and the kernel, compiler and Host
modules that use them are in the default build (`defaultTargets = ["Minidregg"]`,
`lakefile.toml:2`). The proofs about them are a separate library, `ObjectiveProofs`
(`ObjectiveProofs.lean`; `lakefile.toml:128-131`), gated by
`scripts/check-objective-proofs.sh proofs`: it builds the library, then requires the
statement snapshot and the axiom pin to equal the scan of the elaborated environment byte
for byte, and self-tests its instrument on every run (a planted theorem must turn the diff
red; a copy with the scan loop deleted must fail its floor). A default build alone
therefore re-checks none of the proofs above; the gate does. The opt-in `ResearchWip`
library holds the Objective zk assurance modules (`Assurance/ObjectiveBend*`,
`Assurance/ObjectiveZk*`) and the C emitter, not the Core4 definitions or proofs. The
front-end checks (elaborator and C4 tests, parser, preview cohort, publication and
activity-replay, typed examples, the tutorial re-run) are the gate `objective-frontend`
(`scripts/check-objective-frontend.sh`): its Lean rows are red, naming "needs warm base",
when no built tree exists, and its TypeScript rows only drive the Lean front end through
`bun`. The C-backend differential and the checkpoint-transparency differential are
`check-objective-proofs.sh c` and `transparency`. All are rows of `scripts/local-gates.sh`.

### The honest label for executed results

A Plan or result produced on the native path is **"Core4 `executeWith` output"**: what
the evaluator computed, re-executed deterministically at admission and on every
replay. `execution_source_semantics` relates it to the source: the run is a finished
`runBounded` of the same term and the Data is *a* deep reference evaluation of it.
That is not "the meaning of the source" as a unique value (see the open list), and it
says nothing about the front end that produced the term.

## Execution paths

### Preview: `runBounded`

Studio's preview runs: Rust `native/resource-client/src/workspace/studio_preview.rs`
runs the pinned native Host's `objective-front` command, the Lean front end
(`Host/ObjectiveBendFrontEnd`): `capture` locks the package's sources, `preview`
parses (`Compiler/ObjectiveBendParse`), elaborates (`Compiler/ObjectiveBendElaborate`),
writes the core and the typed packet, decodes the packet, runs `check`, then
`runBounded`, in one process. This is the function the soundness and no-refusal
theorems describe. An activity runs to its first yield; the preview prints the typed
Plan, resumes with each supplied response (checked against the entry's declared
response type) and runs to the next yield. Responses stand in for the kernel: nothing
is admitted. From the repository root, against built oleans:

```sh
F="lake env lean --run Host/ObjectiveBendFrontEndMain.lean"
$F capture tests/objective-bend-source/GenericExtension-package.json NEW_CAPTURE_DIR
# a preview-input.v2 request naming NEW_CAPTURE_DIR/objective.json and its sha256
$F preview NEW_REQUEST_JSON NEW_RESULT_DIR
```

or `bun docs/tutorial/run.ts FILE.obend ENTRY [ARGS]` for one file. Schemas:
[capture](OBJECTIVE-BEND-FRONTEND.md), [preview](OBJECTIVE-BEND-PREVIEW.md). The
preview carries `authority: none`.

### Native admission

A member invocation of an Objective method reaches an accepted receipt through the
ordinary native path; Objective needs no new receipt type. **Evidence class: integrated on
scratch worlds (a native Host admitted the signed invocations), not deployed.** `native/resource-client/objective-native-acceptance.py all`
(the journey row `objective`, `scripts/pipeline/journey-rows:40`) builds a fresh
one-sponsor Store whose genesis pins an Objective invocation policy, publishes a method,
invokes it with a signed claim and checks the Accepted receipt and the stored result; a
dishonest signer then tries every refusal below, the world is stopped and reopened, and
every receipt must replay or look up as the same receipt. The path:

- **Publish.** The Host's `objective-publication` (`Host/ObjectivePackageAuthor.lean`) runs
  its own front end on the package and signs exactly `publishedCore`
  (`Compiler/ObjectiveBendPublication.lean:67`); the package (edition 3) and the artifact
  are two content atoms in one ordinary content proposal. Publication creates no authority.
- **Quote and sign.** From the member's retained request (signed source and input queries
  inside it) the local Host derives the final command (`Host/ObjectiveInvocationQuote.lean`:
  it never accepts a remote final command, claimed output or `expectedInput`, and re-runs
  the receiver's full gate unsigned). The client signs a prepare intent for exactly that
  command (`mini objective-invoke`, `native/resource-client/src/objective_invoke.rs`); the
  local consent endpoint 227 re-derives the command and compares the whole plan before any
  header is signed. A lost reply is recovered by `mini retry --mode lookup`, never by
  resubmitting.
- **Admit.** `DeclaredResourceController.admit` dispatches to Objective admission, which
  checks every signature and capability first, then (`prepareCore`,
  `Kernel/ObjectiveBendNativeAdmission.lean:85`): the closed registered policy (edition 4,
  `:512`), the declared envelope within the policy maximum (`capacityWithin`, `:115`), **the
  tariff** (the claim's `proofWork` must equal the policy tariff's price of its declared
  envelope, `tariffExact`, `:468`; a decodable policy's tariff is valid, so no admitted
  invocation costs zero, `Core.proofWork_pos`, `:487`), the authenticated reads (sources and
  inputs enter only as current signed queries, `:1-14`) with their consumed-read guards
  (`guardsExact`, `:475`; `readGuardsOf`, `:370`), source selection (`SourceSelection`,
  `:378`: the package names the policy's front end, which is the receiver's own, and the
  receiver **re-runs that front end** on the package, so the artifact's typed core must be
  byte-identical to the replay, `Replayed`), the inputs against the claim's commitment, and
  the typed check of the applied term. `admit` (`:650`) then runs `executeWith` under the
  declared limits, lowers the result to a Plan, requires the Plan's effects to equal the
  command's (`Output.exact`, `:219`) and the measured usage to fit the declared envelope
  (`fits`, `:578`).
- **Commit.** The existing durable path; on reopen the Host re-executes the program during
  replay.

The refusals the acceptance exercises (`native/resource-client/objective-native-acceptance.py`,
the `refuse` rows of `all`): a source atom that is the package itself, a core that differs
from the replay, a foreign front-end pin, a foreign capability, a wrong query nonce, a stale
and a moved source, a fee that is not the quote, a wrong tariff, an altered argument, an
injected output, and a world whose operator disabled the evaluator `objective-core4` by name.
Admission is by re-execution; no proof carrier gates anything ([ZK.md](ZK.md)).

### Objects, activities and seats

The kernel also has a second family of Objective-adjacent modules, compiled and proved,
that no native route reaches yet (`Kernel.ObjectiveActivity`, `Kernel.AnswerSlot`,
`Kernel.ObjectRecord`, `Kernel.ObjectState`, `Kernel.Seat` and `Kernel.Invitation` are not
in `scripts/gates/host-closure.pin`):

- **Activities** ([activities and events](OBJECTIVE-BEND-EVENTS.md#the-kernel-activity)):
  an activity is a persisted checkpoint plus an await; answer slots with one decider;
  `deliver` resumes it with `resumed {outcome, view}`, the settled outcome and the object's
  declared state read in the same turn; the resume contract (consume-once, one generation per
  resume); exhaustion is a paid turn, ended activities leave tombstones, and anyone may
  abandon an await after its deadline plus a grace.
- **The object record** (`Kernel/ObjectRecord.lean`): a cell is an object to the kernel only
  with a record (id, package `pin`, schema version, `law`, upgrade policy, continuity,
  payer). `create` installs it, a birth refuses a cell without one
  (`birth_refuses_non_object`, `Kernel/ObjectiveActivity.lean:2933`) and a package other
  than the pin (`birth_refuses_other_pin`, `:2943`), and **every declared-state write is
  judged by the object's law** over the old and new state plus the request facts
  (`admitWrite`, `Kernel/ObjectRecord.lean:202`; `Birth.write_judged`,
  `Kernel/ObjectiveActivity.lean:2904`, `Delivery.write_judged`, `:2915`,
  `StateWrite.write_judged`, `:2925`). Those statements are about this module's three
  producers of the state cell; the receiver that would be its only writer is not on main.
- **One shared tariff** (`Kernel/ObjectiveTariff.lean`, in the Host closure): the public
  price of a declared envelope, `Tariff.workOf` (`:49`), used by native admission (above)
  and by the activity kernel for every turn, so there is one shape for "what a declared
  envelope costs" and no price depends on measured work.
- **Declared state types** (`Kernel/ObjectStateType.lean`): a strict `Ty` codec, closed
  first-order typing of a value (`typedAt`) and value subtyping (`stateSubtype`). Defined
  and proved; no turn consumes it, and `ObjectRecord` has no state-type field yet.
- **Seats and invitations** ([SEATS.md](SEATS.md)): offer safety as a law judged on every
  reallocation of a seat's Book balances, with an exit no contract clause can forbid.

In flight (lane names): ACTIVITY-ROUTE (the signed route: receiver, Host ops, `mini`
verbs), RETENTION-PAYERS (a storage charge for packages and checkpoints), UPGRADE (record
v2: state type, upgrade turns), CHECKPOINT-INVARIANT (the turn gate), FORCING-TRANSPARENT,
SCHOLAR-CALLS (a faulted resumed program), SEATS-NATIVE, LAWS-RECEIVER, W17-MACHINE-OPS
(`- < <= > >= /` as O(1) machine steps) and W18-STEPRAW-LINEAR (`stepRaw` linear in the heap).

### Which code wrote: the `objective/artifact` slot and the package pin

Every cell law judges a step whose projected state begins with the slot
`objective/artifact` (`Pred.objectiveArtifactSlot`, `Pred/Core.lean:156`). For a command with an Objective
claim it holds the claimed method artifact's identity, which commits the package, the
selected declaration and the typed core; for any other command it holds `-1`, never an
identity (`objectiveArtifactValue`, `Kernel/DeclaredResourceController.lean:214`). It is first in every law state, so no target, request or content projection
can shadow it (`DeclaredResourceController.objective_artifact_slot_exact`, `Kernel/DeclaredResourceController.lean:514`). Laws run
BEFORE the method executes (a refused law costs no execution); judging the claim is
sound because `AcceptedInvocation` exists only after the executed artifact is shown to
be the claimed one (`AcceptedInvocation.objective_artifact_slot_sound`, `Kernel/DeclaredResourceController.lean:1684`).

`Pred.objectivePin artifacts` (`Pred/Core.lean:372`) is the package pin as a law clause: the step's writes are
the product of one of the named artifacts. A command without an Objective claim is
refused by it whatever its writes (`ordinary_objectivePin_refused`, `Kernel/DeclaredResourceController.lean:523`); a claim naming a
pinned artifact passes it (`pinned_objectivePin_accepts`, `:534`). Installed on an object's state
cells, it makes the object's package pin a law the ordinary resource route cannot
bypass. No turn installs the pin yet. The object record's `create`
(`Kernel/ObjectiveActivity.lean:1993`) stores whatever `law` its caller supplies, and the
kernel's own law views (`views`, `Kernel/ObjectRecord.lean:185`) carry the request facts
and the state slots only, with no `objective/artifact` slot, so a pin placed inside an
object's law would read an absent slot and refuse every kernel write (`eval_objectivePin`,
`Pred/Core.lean:376`: an absent slot is false). Joining the two is not built (in flight:
LAWS-RECEIVER). Before this slot, the Objective route projected no `run/` slot (`run =
none` for an Objective claim), so no law could tell an Objective method's write from an
ordinary command with the same writes.

### Three different things called "law" and "requires"

The surface language and the kernel use the same words for different things. Keep them
apart:

- **A cell law (`Pred`)** is a decidable predicate over a write's (old, new) projected
  state and the request. It is the admission judge: every write is checked by its cell's
  committed law, whoever proposed it.
- **A spec `law name(args): expr`** in `.obend` is a universally quantified property of a
  specification's *methods* (`law positive(n: Nat): self.v(n) < n`). It elaborates to a
  closure in spec metadata and nothing discharges it. It is package evidence (proved by the
  certifying checker where it can be, otherwise reported as unproved). It never reaches
  admission.
- **A spec `requires m(x: T) -> U`** declares a member the specification needs from final
  self (a mixin dependency, checked at composition). It is not a precondition.

A design exists to declare admission rules in `.obend` with their own clause kinds,
`invariant` (a state law), `guard` (a method guard over arguments and request slots),
`permit` and `forbid`, compiled by the Lean elaborator to `Pred` (refusing any clause
outside the fragment), so that `Pred` stays the one judge. None of it is built: the parser
knows `law` and `requires` and no admission clause (`Compiler/ObjectiveBendParse.lean:640`
is the `law` form), so a program cannot yet state the law of its own object.

### The trusted front-end boundary

Trusted (no theorem; one Lean implementation, recomputed by the receiver):

- the Lean parser, capture and elaborator (`Compiler/ObjectiveBendParse`,
  `Host/ObjectiveBendFrontEnd`, `Compiler/ObjectiveBendElaborate`) and the typing
  proposal: there is no surface semantics, so no theorem says the core means what the
  source says. What IS proved of the front end's output is in
  `Compiler/ObjectiveBendFrontEndAdequacy` (typed when the checker accepts, never
  refused by the machine, finished runs are source evaluations of it), and the link from
  the published typed-core bytes to the term the front end built is a theorem, not a
  comparison (`decode_json`, `Compiler/ObjectiveBendTermWire.lean:69`: the checker's
  decoder inverts the front end's rendering; the receiver types the front end's own term,
  never a parse of the core bytes);
- the package capture and fingerprint tooling; `ObjectiveSourcePackage.wellFormed`
  is structural only;
- source-to-core correspondence beyond "this core is what the Lean front end computes
  from these sources": admission recomputes the core from the package and admits only
  an identical artifact (`ObjectiveBendAdmissionSemantics.admitted_front_end`), so a
  publisher cannot pair benign source with a different core; whether that front end is
  right is the first item above;
- spec laws (closures, never checked); `linear`, which the checker enforces as at most
  once, not exactly once;
- the meaning of a Plan extracted from deep Data, until the two open theorems above
  exist.

Not trusted, because native admission re-executes it: argument JSON to `Term`
(bounded, canonical), the typed check, `executeWith`, the exact effect match,
authority and funding.

## Execution and privacy

The lazy semantics is the target for native, oblivious, proof-producing and
homomorphic execution; on main none of those routes runs Objective Bend. The
oblivious-execution, circuit, natural-number and FHE families built for the upstream
Bend machine were deleted with it on 2026-10-04. The zk statements for Objective
(`Assurance/ObjectiveBendCommittedSource`) take a refinement premise. The audit
(`Assurance/ObjectiveZkRefinementAudit`) shows the original `PackedRefinement` is inhabited
for every network by an administrative stutter, so it certifies nothing alone; the corrected
`PackedCodec` has an instance for five programs of the literal tranche
(`Assurance/ObjectiveZkLiteralInstance`) and for no real program, and native proof
verification is not connected to the arithmetic relation ([ZK.md](ZK.md), Part 2). Mini
admits by re-execution only. No FHE route runs today. Laziness
leaks through access pattern and timing: forcing order and cache state are
data-dependent. So a private backend needs a both-arms (mux) lowering of `case` and
an explicit public resource bound; the type system already keeps every effect out of
forced shared thunks.
Source `Nat` is unbounded; a native or circuit backend needs a bounded domain that
fails stop, never wraps. A private profile names observers and permitted leakage
(code, branches, memory access, timing, output shape, failure); encryption alone
hides none of these.

## Surface → core elaboration

`Compiler/ObjectiveBendElaborate.lean`, as it is:

| Surface | Core |
| --- | --- |
| global declarations | fields of one record knot: `fix (λglobals λseed. record{Module.name: …}) (record [])`; a global reference is `get globals "Module.name"` through the tied address |
| `def f(x…) -> T: body` | nested `lam`s with binder hints and annotations |
| `extension(self, super) -> T: e` | `lam lam e`, typed `T → T → T` (homogeneous) |
| `spec S for T: …` | `specification (record{name, interface: <signatures as a JSON label>, laws: record of law closures}) (λself λsuper. extend super {methods})` |
| `compose(a, b, c…)` | left fold to `specification (record{operator, inherited: v, wrapping: r}) (mix v r)`, the inherited composite bound once |
| `spec S extends A, B for T`, `suffix spec`, `around` and `combine` methods | the C4 precedence list; the extension is the `mix` chain of the ancestors' hidden layers `M.S#primary` and `M.S#around` |
| `fix(s, i)`, `extend(x, {…})` | `fix`, `extend` |
| `prototype`, `reflect`, `metadata`, `targetOf` | `prototype`, `reflect`, `metadata`, `project` |
| `x.f`, `f(a, b)`, `()` | `get`, curried `app`, `record []` |
| `+ * == &&` | `add`, `multiply`, `equal`, `conjunction`; `==` on String is `labelEqual`, and `!=` and `\|\|` go through `ifBool` |
| `match n: case 0n / case 1n+p` | `ifZero`; exactly those two branches |
| `sum S: …`, `S.l(e)`, `match s: case l(x): …`, `if c then a else b` | `inject`, `case` (exhaustive), `ifBool` |
| `-> Activity<P, R, A>`, `perform(plan)`, `match perform(…): case l(x): …` | `perform`; a pure tail becomes `done`; the match is the same `case`, typed as an effect case |
| `let x = v` (statement or expression form) | `app (lam body) v`: one lazy cell for `v`, evaluated at most once (call-by-need) |
| `true`/`false`, strings, `7n` | `boolean`, `label`, `nat` |

Arguments and fields stay thunks; laziness is preserved.

Known front-end defects:

- `< > <= >= - /` have no Core4 primitive: they lower to recursion over the successor
  structure (a package prelude, see [front end](OBJECTIVE-BEND-FRONTEND.md#operators-without-a-core-primitive-and-let)),
  so each costs O(value) machine steps, not O(1). A Primitive.less/subtract/divide in the
  machine would make them constant-time; it is a core change (new frames, new proof cases)
  and is not built (in flight: W17-MACHINE-OPS). (`!=` and `||` elaborate through
  `labelEqual` and `ifBool`.)
- A `match` on a sum takes only `label(binder)` cases; wildcards are refused because
  there is no default arm.
- Quantities: `default`/`copy` map to unrestricted and `dead` to erased; `affine x`
  and `linear x` are at most once in the checker, exactly once is not enforced, and
  every closure built after one is one-shot.
- `requires` is carried as a string and never checked.
- `before` and `after` methods are refused (`Compiler/ObjectiveBendElaborate.lean:1160`).
- `compose` is shared: the inherited composite is bound once, so term size is linear in
  the number of composed specs (`tests/objective-bend-source/check-elaborate.ts`, "COMPOSE SHARING").

The drivers in `examples/objective-bend-world/reference/` embed packets from the
current front end; `scripts/check-objective-examples.sh` fails when one is stale.

## What was Gen-1

The first generation elaborated this OO surface into checked Books of the upstream
Bend kernel (`Compiler/ObjectiveBendLinker`, `ObjectiveBendElaboration`, the Workshop
and its instance loaders), which bound the language to the restrictions of that
embedding: data-only reusable captures, acyclic linking and total strict calls. On
2026-10-03 Objective Bend became its own lazy language with Core4 as its only core.
The cut (2026-10-04) deleted Gen-1; the same day the vendored kernel and every module
that reached it (its closure machine, the oblivious, logic, natural-number, FHE and
activity families, and their artifacts and checks) were deleted too. Git history holds
them; `./NAME.bend` imports are refused by the parser and the front end, and nothing in
this guide claims anything about them.

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

The original Bend calculus (upstream pin `947db722`) was vendored as a reference
until 2026-10-04 and is in Git history; strict-machine proofs say nothing about the
demand machine.

These are design sources. The repository's semantics, theorem premises and admitted
receiving paths determine what Objective Bend guarantees.
