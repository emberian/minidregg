# Objective Bend

Objective Bend is Mini's authored language. Its model is François-René Rideau's
("Faré") account of object orientation as modularity plus incrementality: **lazy open
recursion over first-class, partial, composable specifications**. A program is a
package of `.obend` source; the one front end (in Lean) lowers it to a term of the core
calculus, **Core4**; the proof-producing checker types that term; the demand machine
runs it. Mini supplies what the language does not: durable identity (objects), current
authority, admission, funding and the laws that judge every write.

This page is the overview. It is written against the code; where it names a theorem, the
theorem is pinned in its module's contract manifest, `scripts/gates/objective-manifest/<Module>.tsv`
(Core4, kernel and front end alike). Companion
documents:

- [OBJECTIVE-BEND-TUTORIAL.md](OBJECTIVE-BEND-TUTORIAL.md): the language from zero, every
  result re-run by a gate.
- [OBJECTIVE-BEND-FRONTEND.md](OBJECTIVE-BEND-FRONTEND.md): reference for the front end
  (commands, capture, preview wire, surface-to-core lowering, publication).
- [OBJECTIVE-BEND-EVENTS.md](OBJECTIVE-BEND-EVENTS.md): reference for activities and the
  object kernel (turns, cells, fees, calls, sends).
- [objective-bend/MODULAR-TYPING.md](objective-bend/MODULAR-TYPING.md) and
  [objective-bend/REFLECTION.md](objective-bend/REFLECTION.md): the design records behind
  modular typing and the reflection contract.
- [OBJECTIVE-BEND-BACKENDS.md](OBJECTIVE-BEND-BACKENDS.md): executors other than the Lean
  machine; [SEATS.md](SEATS.md): seats and invitations.

Evidence words used below: *compiled* (Lean checked it), *proved* (a theorem in a
snapshot), *executed* (a gate or lane ran it), *integrated* (a native Host admitted it on
a scratch world), *deployed* (nothing here is).

## Core4

### Specifications, `mix` and `fix`

A **specification** is a first-class partial extension `C → V → W`: given the eventual
whole (the **final self**, `C`) and the value inherited from the layers below (the **whole
super**, `V`), it produces `W`. It can add fields, wrap behaviour, replace a value or build
a function, and it is a value before any target exists (ltuo §2.1, §5.4). Composition
passes one final self to every layer and feeds each layer the whole result below it
(poof §1.2.3, §1.3.2). The reference relation `Step`
(`Theory/ObjectiveBendOpenRecursion.lean`) says exactly that:

```text
mix lower upper     ⟶  λself. λsuper. upper self (lower self super)
fix spec inherited  ⟶  spec (fix spec inherited) inherited
```

`fix` is a computation, not an equation (ltuo §5.3.2): the operational rule is its
meaning. **Laziness is part of the meaning**: `{good = 7, bad = self.bad}.good` is `7`, and
an unused divergent argument is never forced (EOOMI §5.1). The reference semantics is
call-by-name; the demand machine is call-by-need (an argument or field is one shared heap
cell, evaluated at most once), and `fix` ties one heap address to itself.

A **prototype** pairs a specification with its target so reflection can reach the
specification without forcing the target (ltuo §2.3.3, §6.1).

### The terms

`Term` in `Theory/ObjectiveBendOpenRecursion.lean`, all of it:

| Term | Meaning |
| --- | --- |
| `bound i`, `lam b`, `app f a` | de Bruijn variable, abstraction, application (β; the machine makes `a` a shared thunk) |
| `mix lower upper`, `fix spec inherited` | the two rules above |
| `specification meta ext` | a value; applying it applies `ext`; `meta` is reachable without forcing `ext` |
| `prototype spec target` | a value pairing a specification with its target |
| `reflect p`, `metadata s`, `project p` | the spec of a prototype, the metadata of a spec, the target of a prototype; none forces the other part |
| `nat n`, `boolean b`, `label s` | scalars; naturals are unbounded, labels are opaque strings |
| `binary p l r` | strict, left to right; `p` ∈ `add multiply equal conjunction labelEqual subtract divide less lessEqual modulo`, each one machine step |
| `record fs`, `extend r fs`, `get t name` | records of separate suspensions (first match wins), override, selection by a static name |
| `ifZero v z s` | case on a Nat; the successor branch binds the predecessor |
| `inject l p`, `case s arms`, `ifBool c t f` | sums: a lazy injection, case on its label, the Boolean branch |
| `perform plan`, `done v` | an activity yields a Plan and is resumed with a response; `done` returns a pure value from an activity |

`subtract` is truncated, `divide` floors with `a / 0 = 0`, `modulo` is its remainder
(`subtract_truncated_exact`, `divide_floor_exact`, `divide_modulo_reconstruct`,
`order_exact`). There is no digest primitive and no dynamic (computed-name) `get`.

### Types and quantities

`Theory/ObjectiveBendTypes.lean` and `Theory/ObjectiveBendTyping.lean`. `check` is
proof-producing: it returns a typing derivation for the actual term (`Checked`). Rows are
compared canonically; there is no subtyping, and type equality is exact up to one bounded
head unfolding of an alias variable. Bounded type variables keep row tails, so a method can
be typed against a future self it has not seen (`future_row_instantiation_accepted`,
`future_binary_instantiation_accepted`; ltuo §8.2). `fix` is typed homogeneously
(`target → inherited → target`); heterogeneity lives in `mix`
(`heterogeneous_runtime_mix_accepted`). Effects are a type, `Ty.computation P R A`; an
activity type is never shareable, so no effect can sit in a field, argument, payload or
Plan (`effect_as_argument_refused`, `effect_in_record_field_refused`, ...). Quantities are
erased, affine, linear and unrestricted; the checker enforces at most once for both affine
and linear (`duplicate_affine_refused`), not exactly once, and a reusable closure captures
only unrestricted, shareable bindings (`reusable_lambda_capture_rule`).

### The package is a specification

Every global declaration is a field of one record knot, so mutual recursion works through
it (ltuo §9.3.7). The root is itself a specification:
`fix(specification({package: …}, λ$globals λ$seed. extend $seed {M.decl: …}), {})`, a
global reference is `get $globals "M.name"`, and the root extends its inherited row. No
surface form names another package's root, so another package cannot yet extend it.

### Ancestry and method combination

`spec S extends A, B for T` is linearized by C4 (C3 plus the suffix property, ltuo §7.4;
`Compiler/ObjectiveBendC4.lean`) in the elaborator; the extension is the `mix` chain of the
ancestors' hidden layers, with no new constructors. Identity is the qualified declaration
key, so a diamond's shared ancestor counts once while `compose(E, E)` applies `E` twice.
Qualifiers: `def` (primary), `suffix spec`, `around`, and the pure combinations
`combine +`, `combine *`, `combine and`. `before` and `after` are parsed and refused by the
elaborator.

### Specification metadata

Every specification has the one type `Specification<T>` =
`specification(SpecMeta, Extension<T>)`, where `SpecMeta` and `SpecClaims` are built-in sums:

```text
sum SpecClaims:  none: {}  |  claim: {name: String, status: String, rest: SpecClaims}
sum SpecMeta:  declared: {name: String, interface: String, claims: SpecClaims}
            |  composed: {inherited: SpecMeta, wrapping: SpecMeta}
            |  extension: {}
```

`compose(a, b)` is `specification(SpecMeta.composed{…}, mix a b)`. Laws, ancestry and
composition change the metadata *value*, never the type, so
`def twice(e: Extension<Nat>) -> Specification<Nat>: compose(e, e)` checks
(`Compiler/ObjectiveBendSpecificationClosure.lean`: `composeTy_closed`, `twice_accepted`,
`claim_spec_accepted`). Reflection sees exactly: `metadata`, `reflect`, `targetOf`, the
behaviour of application/`fix`/`mix`, and string equality on `SpecMeta` fields. Because
`metadata` observes construction history, `compose` is associative for behaviour but not
for reflection: the two associations are told apart by a program (probes R01/R02). The
contract and its open half (a provenance-establishing prototype constructor) are in
[REFLECTION.md](objective-bend/REFLECTION.md).

## Writing a program

A source file starts with `edition ObjectiveBend 1`. Here a `Review` record is built from
three separately written specifications. `Twice` declares that it needs `review` from the
final self; `Augmented` wraps the inherited `review` through `super`:

```obend docs/objective-bend/examples/Review.obend
edition ObjectiveBend 1

record Review:
  review(value: Nat) -> Nat
  twice(value: Nat) -> Nat

spec Base for Review:
  def review(value: Nat) -> Nat:
    value + 1n

spec Twice for Review:
  requires review(value: Nat) -> Nat
  def twice(value: Nat) -> Nat:
    self.review(self.review(value))

spec Augmented for Review:
  def review(value: Nat) -> Nat:
    super.review(value) + 1n

def reviewOfThree() -> Nat:
  fix(compose(Base, Twice, Augmented), {}).review(3n)

def twiceOfThree() -> Nat:
  fix(compose(Base, Twice, Augmented), {}).twice(3n)
```

`super.review(3)` is `Base`'s `4`, so the final `review(3)` is `5`. `twice` reads `review`
through `self`, which is the final, augmented `review`, so `twice(3)` is
`review(review(3)) = review(5) = 7`. The seed is `{}`: each layer is typed at the row
actually beneath it, so no placeholder methods are needed.

The preview runs it. `docs/tutorial/run.ts` captures the file, runs the Lean front end,
asks the checker to type the term and, only on acceptance, runs the same term on the
machine (the tutorial's "Before you start" says what it needs):

```sh
$ bun docs/tutorial/run.ts docs/objective-bend/examples/Review.obend reviewOfThree
status: finished
type: Nat
result: 5

$ bun docs/tutorial/run.ts docs/objective-bend/examples/Review.obend twiceOfThree
status: finished
type: Nat
result: 7
```

Every source block and command on this page is re-run by the `overview` row of
`scripts/check-objective-frontend.sh`: each ```` ```obend PATH ```` block must equal the
file byte for byte, and each command must print exactly what is shown.

The surface in brief (the full lowering table is in the
[front-end reference](OBJECTIVE-BEND-FRONTEND.md#surface-language-and-its-core-lowering)):
`def` (curried `lam`s in the package knot), `record`, `sum`, `extension(self, super)`,
`spec … for T` / `spec …[Self has …, Super has …]`, `compose`, `fix`, `extend`, `prototype`,
`reflect`, `metadata`, `targetOf`, `match` on Nats (`0n` / `1n+p`), Booleans and sums,
`if … then … else`, `let` (one lazy cell), `fn`, `+ * - / % == != < <= > >= && ||`
(`&&` is the strict primitive; `||` lowers to `ifBool` and is lazy in its right operand;
`>`/`>=` are negations so the left operand is still evaluated first). There is no unary
`!`, no wildcard arm, and no string operation but equality.

## Modular typing

A specification is typed against what it uses, not against a whole target it has seen
(Faré's distinction between "trivial non-modular" and modular types, ltuo §8.2). The rules,
as built in `Compiler/ObjectiveBendElaborate.lean` (`chainFix`, `checkTemplates`) and
pinned by `tests/objective-bend-source/ltuo/probe-cohort.json`:

- **Closed specs.** `spec S for T` types `self` as `T` but `super` as an open row: the
  members `S` reads through `super`. `requires m(…) -> R` must name a member of `T` at its
  exact type, else `refused (requires-signature)`.
- **`fix` discharges.** `fix(compose(L1, …, Ln), seed)` over declared plain specs types each
  layer at the row beneath it, bottom up from the seed. A `super.m` that nothing below
  provides is `refused (inherited-unprovided)`; a target member that no layer and not the
  seed provides is `refused (requires-unprovided)`, naming the specs that require it; a
  seed field outside the target is `refused (seed-extra)`. A seed that provides a member
  discharges a requirement for it: that is inheritance from the seed.
- **Open declarations.** An extension or spec may bind its assumptions:

  ```obend docs/objective-bend/examples/Modular.obend
  edition ObjectiveBend 1

  record XY:
    x: Nat
    y: Nat
  record XYZW:
    x: Nat
    y: Nat
    z: Nat
    w: Nat

  extension AddY[Self has {x: Nat}, Super has {x: Nat}](self: Self, super: Super) -> Super with {y: Nat}:
    extend(super, {y: 2n * self.x})

  extension AddZW(self: XYZW, super: XY) -> XYZW:
    extend(super, {z: self.y, w: self.z + 1n})

  def wOfFive() -> Nat:
    fix(compose(AddY, AddZW), {x: 5n}).w
  ```

  `AddY` is checked once, at its own bounds, with `Self` and `Super` **rigid**: each is a
  lower bound, not an alias of its row, so the body may read `self.x` and nothing else, and may
  not use `self` (or `super`) where a value of exactly its bound row is expected
  (`refused (self-rigid)`, `refused (super-rigid)`, `refused (self-unbound-member)`). `Super with {y: Nat}` keeps whatever else `Super` has.
  At `fix`, each open layer is instantiated at the final self and the row beneath it, after
  both bounds are discharged (`refused (self-bound)`, `refused (inherited-unprovided)`). The
  final self comes from the closed layers, else the enclosing definition's result type or
  an annotated `let`, else `refused (self-undetermined)`. Here `AddY`, written without
  knowing about `z` or `w`, is used under a four-field self:

  ```sh
  $ bun docs/tutorial/run.ts docs/objective-bend/examples/Modular.obend wOfFive
  status: finished
  type: Nat
  result: 11
  ```

- **F-bounds and recursive records.** A bound may mention `Self`, so a binary method is
  typed against the future self, and a record may name itself:

  ```obend docs/objective-bend/examples/Heavier.obend
  edition ObjectiveBend 1

  record Node:
    weight: Nat
    heavier(other: Node) -> Node
  record ColoredNode:
    weight: Nat
    color: Nat
    heavier(other: ColoredNode) -> ColoredNode

  spec Heavier[Self has {weight: Nat, heavier(other: Self) -> Self}, Super has {weight: Nat}]:
    def heavier(other: Self) -> Self:
      if other.weight <= self.weight then self else other

  def node(n: Nat) -> Node:
    fix(Heavier, {weight: n})

  def colored(n: Nat, c: Nat) -> ColoredNode:
    fix(Heavier, {weight: n, color: c})

  def pick() -> Nat:
    node(3n).heavier(node(5n)).weight + colored(2n, 7n).heavier(colored(1n, 9n)).color
  ```

  ```sh
  $ bun docs/tutorial/run.ts docs/objective-bend/examples/Heavier.obend pick
  status: finished
  type: Nat
  result: 12
  ```

**Design.** Templates, not polymorphic core terms. An open declaration is checked ONCE, at its
own bounds, with `Self` and `Super` both rigid bounded variables (`checkTemplates`): a body that
uses `self` or `super` where a value of exactly its bound row is expected is refused
(`self-rigid`, `super-rigid`), because the actual self or row beneath may have more members. At
`fix` every use is EMITTED as that checked template under its substitution
(`ATerm.instantiate σ template`, σ = {Self ↦ the final self, Super ↦ the row beneath}); nothing
is re-elaborated per instance. The emitted program is an ordinary closed Core4 program, so every
machine theorem keeps its statement (D1, D2 of [MODULAR-TYPING.md](objective-bend/MODULAR-TYPING.md)).

**The composition contract** (GPT-6 row D, `Compiler/ObjectiveBendContract.lean`). Each layer of
`fix(compose(L₁, …, Lₙ), seed)` has a contract: what it ASSUMES of the final self (its `Self`
bound and `requires`), what it CONSUMES from the row beneath (its `Super` bound), and what it
PROVIDES. `chainFix` decides every contract refusal by running that one algebra, nothing else:
- `self-bound` / `inherited-unprovided`: an assumption or consumption is missing, or present at
  another type (`checkBounds`);
- `replace-undeclared`: a layer gives a member beneath it a different type. A layer may ADD a
  member absent beneath or OVERRIDE one at the same type; a type change is a replacement, and no
  source form declares one (before, a replacement a later layer undid passed silently);
- `requires-unprovided`, `seed-extra`, `provided-mismatch`: at the end, the final row must be
  exactly the final self (`close`).

Proved over the algebra: `run_append` (C_{A;B}(S, I) = C_A(S, I) ∧ C_B(S, F_A(S, I)) and
F_{A;B} = F_B ∘ F_A), `run_assoc`, `checkLayer_ok`, `discharge_ok`. The acceptance case is
`tests/objective-bend-source/three-package/` (preview rows D1/D1b): a package integrates two
separately written specs without editing them, and both read its final definitions (300 against
30 without it).

**What is proved at the checker** (`Theory/ObjectiveBendTemplates.lean`): `canonical_instantiate`;
`Discharges.infer_instantiate` and `Discharges.check_instantiate` (a template the checker accepts
under rigid bounds is accepted at every substitution that discharges them, at the instantiated
type, with the same uses, given `extra` more fuel), inhabited by `coloured_discharges` /
`coloured_instance_accepted`; the rigidity tooth `self_as_bound_row_alias_accepted` /
`self_as_bound_row_rigid_refused`. **What admission relies on** is not that theorem: the closed
program, instances included, is checked again by the checker. No front-end corollary is
claimed, because no check depends on one. Ancestry specs and non-plain operands in a `fix` chain
keep the closed whole-target rule; instances across package roots are not addressed.

## Activities

An **activity** hands a typed Plan to its host, waits, and continues with the typed
response. `Activity<P, R, A>` yields Plans of the sum `P`, is resumed with data of type `R`,
and finishes with an `A`. `match perform(plan):` sequences: its arms are the handlers, and a
pure tail is lifted with `done`.

```obend docs/objective-bend/examples/Counter.obend
edition ObjectiveBend 1

record Write:
  field: Nat
  before: Nat
  after: Nat

sum Plan:
  write: Write

sum Response:
  written: {}
  refused: {}

def bump(count: Nat) -> Activity<Plan, Response, Nat>:
  match perform(Plan.write({field: 0n, before: count, after: count + 1n})):
    case written(_): count + 1n
    case refused(_): count
```

The preview has no kernel; responses are supplied on the command line and checked against
the declared response type:

```sh
$ bun docs/tutorial/run.ts docs/objective-bend/examples/Counter.obend bump '["4"]'
status: yielded
type: Activity<sum {write: {field: Nat, before: Nat, after: Nat}}, sum {written: {}, refused: {}}, Nat>
turn 1: yield write({field: 0, before: 4, after: 5})  (waiting)
diagnostic: waiting for a response

$ bun docs/tutorial/run.ts docs/objective-bend/examples/Counter.obend bump '["4"]' '["written"]'
status: finished
type: Activity<sum {write: {field: Nat, before: Nat, after: Nat}}, sum {written: {}, refused: {}}, Nat>
turn 1: yield write({field: 0, before: 4, after: 5})  <- written({})
result: 5
```

Semantics. `perform` is not a value and never a reduction: a term whose next redex is a
perform has **yielded** (`yields_no_step`, `yields_deterministic`). On the machine,
`perform` under an update frame (a shared cell being forced) is refused `sharedEffect`
(`perform_under_update_refused`); otherwise the Plan becomes a heap cell and the state is
`yielded` (`perform_yields`); `resume` is defined only on a yielded state and changes
nothing but the control (`resume_requires_yield`, `resume_keeps_heap_and_stack`). The
front end refuses, by name, an activity as an argument, field, payload or Plan
(`effect-as-argument`, `effect-in-field`, `effect-in-payload`, `effect-in-plan`), a
`perform` outside an activity and a parameterless activity (`nullary-activity`: it would be
a shared value, its effect cached). The checker proves the same at the core
(`checked_reachable_no_refusal` covers `sharedEffect`). Inside a turn, recursion is lazy
`fix` and may diverge or exhaust its ticks; across turns a resident's self-call sits under a
perform, so each unfolding costs one resume. No check yet guarantees that a well-typed
resident's pure segment terminates.

## Objects and the activity kernel

The kernel runs activities on objects. Detail, with every turn and theorem, is in
[OBJECTIVE-BEND-EVENTS.md](OBJECTIVE-BEND-EVENTS.md); the shape:

- **An object** is a cell with an `ObjectRecord` (`Kernel/ObjectRecord.lean`: package `pin`,
  declared `stateType`, the package's laws, the creator's `law`, upgrade policy, the upgrade
  phase and its live-activity counters, the invariant domains it belongs to, payer), installed
  by `create`. Its declared state is an `ObjectState {version, value}`.
- **What judges a declared-state write** (`admitWrite`), in order, all ENFORCED by the kernel
  on every route (`Birth.write_judged`, `Delivery.write_judged`, `invocation_writes_from_view`):
  1. the value must type at the record's `stateType` (`illTyped`);
  2. the pin clause: the write was made by the pinned package (`ObjectRecord.pinClause`, derived
     from the record, never stored, so no creator law omits it; `create_installs_pin`,
     `Birth.write_passes_pin`, `Delivery.write_passes_pin`, `invocation_writes_pinned`,
     `MessageDelivery.writes_pinned`);
  3. the PACKAGE's laws, copied from the pinned package at create and ADOPT and never taken from
     a request (`package_law_enforced`, `package_law_not_removable`; see "law" below);
  4. the creator's law;
  5. at turn end, every invariant domain the object belongs to (below).
  A refusal names the clause (`LawLeaf`). There is no direct write of declared state: a creation
  may carry the object's initial state (`seed`, judged by the package's and the creator's laws,
  `create_seed_judged`, `create_seed_refused_names_clause`), and every later write is a birth, a
  delivery, a call frame or a delivered message under the pinned package. A birth must run the
  pinned package (`birth_refuses_non_object`, `birth_refuses_other_pin`). The kernel's cells sit
  at reserved coordinates (≥ 2^256) that the ordinary route cannot write (`ObjectiveActivityGate`:
  `ordinaryGate_refuses`, `forged_protected_write_refused`).
- **Upgrade** (`Kernel/ObjectiveActivityUpgrade.lean`, `Kernel/ObjectiveUpgradeInvariant.lean`).
  ADOPT moves an object toward a new package under its upgrade policy (`adopt_requires_authority`,
  `frozen_never_adopts`); the new law must entail the policy's floors (`adopt_floors_entailed`,
  refused `floorNotEntailed` otherwise); a new pin is required (`samePin`); the migration is a
  declaration of the NEW package, checked by the existing checker at `old state -> new state`, and
  must read every field of the old state or drop it by name (`migrationShape`). While the object
  DRAINS, an old activity's write is judged by the old law AND its migrated value by the new one
  (`drained_write_migratable`; `upgradeConflict` otherwise); births and calls are admitted only
  for an identity migration; a call tree that writes the object is drained-judged
  (`drainConflict`); messages to it wait (`draining`). MIGRATE (single turn, when no old activity
  is live) runs the migration under the new package's envelope: `migrate_cannot_fail` holds over
  every reachable world with no premise on the state, and `live_counts` proves the counters equal
  the awaiting records. `abortDrained` (anyone, after the drain deadline) resumes a straggler with `upgraded` for one
  segment on its own package and ends it (`abort_after_deadline_exclusive`); activities chosen for REBIRTH are frozen after MIGRATE
  (`awaitingRebirth`) until `rebirth` restarts them on the new package from their stored input
  (`rebirth_from_stored_input`).
- **Invariant domains** (GPT-6 row A, `Kernel/ObjectiveDomain.lean`). `registerDomain` names
  member objects and one law over their JOINT state (member `i`'s slots under `member/<i>/`). Every
  member consents under its upgrade policy (`memberFrozen` refuses a frozen one) and the law must
  hold on the current states. At the end of EVERY admitted turn, each domain of every object whose
  state the turn wrote is judged on all members' FINAL states, written or not
  (`judgeDomains_sound`, `finish_domains`), and refused `domainLawDenied domain leaf`. The judgment
  only adds refusals. It reads its members under guards, so a concurrent write to an unwritten
  member conflicts instead of slipping past (`finalIntent_guards`). A domain law is a state
  predicate (no request slots). Membership is permanent.
- **The program is the front end's output.** `publish` stores an artifact and its source package
  only after re-running the Lean front end; every later turn reloads and replays the pair
  (`Program.runs_front_end_output`). The artifact commits the package's laws; a tampered or
  dropped law is refused at replay.
- **Kernel Plans and responses.** A resident yields `await {write, on, patience}`: a record
  of per-field edits (`keep | set v | add n`) and what it waits for (an answer slot with one
  decider, or a height), with a mandatory deadline. It is resumed with
  `resumed {outcome, view}`: the settled outcome (`reply | refused | unknown | timedOut |
  broken | upgraded`) and the object's declared state **read in the resuming turn**. The
  kernel applies the edits to that view, so no write is computed from a stale read
  (`resume_view_current`, `moved_state_refuses`, `yield_write_from_current_read`).
  Reference program: [world/activity/Tally.obend](../world/activity/Tally.obend).
- **Answer slots** (`Kernel/AnswerSlot.lean`): a name no submitter chooses, one decider,
  one deadline, one terminal decision (`decide_single_decider`, `slot_decided_once`).
- **The resume contract.** A delivery spends the await as a nullifier bound to the
  checkpoint digest and writes the record against its current root: consume-once
  (`resume_consumes_once`, `native_delivery_consumes_once`), the outcome arrives exactly as
  decided (`resume_outcome_preserved`), one generation per resume
  (`delivery_advances_generation`).
- **The checkpoint** is the Plan extraction's state, settled and garbage-collected
  (`ObjectiveBendDemandCollect.checkpoint`), stored as `encodeState` tokens
  (`state_roundTrip`). It is typed (`birth_checkpoint_typed`, `delivery_checkpoint_typed`),
  and across every reachable snapshot every awaiting record's checkpoint is typed
  (`stored_checkpoints_typed`, `Kernel/ObjectiveCheckpointInvariant.lean`, over the three
  kinds of step the replay walk admits, `derived_route`).
- **The checkpoint changes only what a run costs.** Whatever resuming the stored checkpoint
  commits, resuming the program's own yield commits alike under every resource vector above a
  threshold (heap and stack room, ticks, extraction ticks), with the deployment's output sizes
  (`runSegment_stored_converse`, `ResourcesOnly`; it is not "the same budget, the same result",
  which `stored_commits_where_lazy_exhausts` refutes). After a stored yield the program's own
  next yield is in a `Chain` (forcing, settling, collection) with the stored next checkpoint,
  and every response keeps it so (`runSegment_stored_next`, `Chain.resume`). Proof: backward
  simulation (`Theory/ObjectiveBendDemandForcingBack.lean`, `...Converse.lean`): a forced run
  that halts has a lazy run that halts, which redoes the closed demands the extraction cached.
  Planted fault: a checkpoint that lost its stack is not resources-only
  (`not_resourcesOnly_lostStack`).
- **Activities against their reference interaction tree.** The reference meaning of an activity
  is the interaction tree of the program's own machine (`Theory/ObjectiveBendInteraction.lean`:
  `observe`, nodes `vis d` with continuation `k r` = the program's own yield resumed, `ret`,
  faults, `malformed`, and `spin`, silent divergence, a node of its own). Along every history
  of one record (birth, deliveries, exhaustions), every committed segment that is the run's own
  is the reference node after the same responses, resources only (`History.reference`,
  `Kernel/ObjectiveReferenceLift.lean`); where the reference spins, nothing is ever committed
  (`History.spin`, `chain_spin`); a committed program fault is classified against the reference
  (`delivery_refusal_reference`). Call frames run the reference machine directly
  (`Kernel/ObjectiveCallReference.lean`).
- **Metering.** One public tariff (`Kernel/ObjectiveTariff.lean`, `Tariff.workOf`) prices a
  **declared** envelope (heap, stack, ticks, extraction ticks); no fee depends on measured work
  (`refund_measurement_free`, `submitter_charge_declared`). Each turn decides its coverage BEFORE
  any Core4 run, by name: `uncovered` (the envelope exceeds the deployment's policy);
  `heapUncovered needed declared` (a resumed segment's heap limit is the stored checkpoint's size
  plus the declared heap, `segmentLimits`, so a stored checkpoint resumes exactly,
  `largerYield_resumes_exactly`, where absolute limits would not, `absolute_limits_refuted`; the
  price covers it, `Delivery.heap_priced`; the Host quotes `needed` from the same function,
  `resumeQuote`, op 214); `extractUncovered` (extraction ticks spent forcing Plans and results
  are declared and priced like any resource, against a per-turn ceiling `Config.maxExtractTicks`
  that op 214 publishes; a call tree draws each extraction's ACTUAL spend from that declaration,
  `Journal.draw_two`, `Journal.draw_short`, and `ceiling_reservation_refuses` is the pole showing
  why reserving the maximum per extraction would refuse honest trees). A yield reserves its
  resume/timeout fee pair and a **storage deposit** (`storageDeposit`, the rate per octet of the
  record) in the activity's purse. The charged record spells its digests and heights at fixed
  width, so its length, and so the deposit, is the same for the quote and the submission
  (`encodeRecord_length_mask`, `birth_not_underfunded_at_quote`; executed: fifty quote-then-submit
  births, one quote, none refused). **Exhaustion is a paid turn**: an attempt that runs out of its
  envelope commits a charge and changes nothing else; an attempt at or below the largest envelope
  already tried is refused before it runs (`exhaustion_charges_declared`,
  `exhaustion_spends_nothing`, `exhaustion_excludes_delivery`). Every turn's postings conserve
  every asset (`Birth.conserves`, `Delivery.conserves`, …).
- **Disposal.** An ended activity's record and settled slots are retired: the id never
  returns, and a late delivery or decision is refused by name. Anyone may `abandon` an await
  past its deadline plus a grace; the purse returns to the payer
  (`abandon_returns_escrow`, `abandon_delivery_exclusive`).
- **Faults.** A resumed segment that diverges, refuses, yields a malformed Plan or ends
  with an unextractable result commits `faulted` and returns the unused escrow; it never
  refuses the turn, so a faulty program cannot park its activity
  (`resumedSegment_never_refuses_program_fault`).
- **Route.** Fifteen turns, each a signed native command (`Kernel/ObjectiveActivityReceiver.lean`;
  Host operations 210-214; `mini activity`): `publish`, `create`, `birth`, `resolve`, `deliver`,
  `exhaust`, `abandon`, `topUp`, `invoke`, `deliverMessage`, `adopt`, `migrate`, `abortDrained`,
  `rebirth`, `registerDomain`. The receiver writes only kernel cells and the Book
  (`intent_writes_activity_or_book`). Proofs that classify every turn (`AdmittedTurn`, no
  wildcard) break when a turn is added, by design. **Executed on scratch worlds**: the pipeline
  journey rows `activity`, `objectrecord`, `call`, `send`, `seats`, `bounty`; the domain journey
  (`objective-domain-native-journey.py`, D1-D4) runs from its driver but is not a pipeline row.
  **No executed row** drives the upgrade turns (`world/activity/TallyV2.obend` lowers and is
  checked; cv 01a1141b-d4f6).

## Calls and sends

**Call** (`Kernel/ObjectiveCall.lean`). An `invoke` turn calls one method of one object; the
method may call other objects' methods in the same turn, depth first, to depth 8. A method is a
declaration of the object's pinned package, lowered by the kernel's own front end, of type
`method(view: {version, state}, args: X) -> Activity<P, R, {result, write}>` with `P` among
`call | send | stop | cancel` and `R` among `returned | queued`: every yield is answered in the
same turn, so no frame suspends across turns (a method whose Plan admits `await` is refused
`notCallable`). The whole tree co-fails: any refusal refuses the turn.

- **View stability.** Re-entry is refused (`reentry_refused`; `invocation_reentry_free`). So a
  call subtree leaves the state of every object on the stack it was entered from exactly as it
  was, and each frame's write is applied to exactly the state that frame was shown
  (`active_frame_view_stability`, `invocation_writes_from_view`; for a delivered message's tree,
  `runMessage_writes_from_view`). Remove the re-entry guard and the theorem goes red: that is
  the DAO mutant (bank 40 / thief 60, journey row C5).
- **Authority is delegated by signed grants, and delegation is not consent.** The root frame
  carries the signer (`request/subject`; `request/caller` none). A nested frame carries the
  signer only under a grant of the invocation that names its object, method, the CODE it runs
  (its package pin), its arguments (`exact` digest of the canonical arguments, or a `recipient`
  field equal to a value, or a `capped` Nat charged cumulatively against a limit), optionally its
  direct caller, and a number of uses. A frame a grant names but does not admit refuses the whole
  tree `grantMismatch` (the field that mismatched is named); an exhausted grant `grantSpent`; a
  frame no grant names runs without the subject. Every delegation is recorded, and
  `invocation_delegated_authority` proves each one matches a signed grant, no grant is used past
  its uses or charged past its cap, and every write carries the subject only at the root or
  through a delegation recorded for exactly that frame. Each write is still judged by its
  object's law. `request/caller` names the calling object, so a law can admit chosen callers.
- **One declared envelope** for the whole tree, priced by the tariff. Each frame's Plan and
  result extraction draws its actual spend from the envelope's extraction ticks, refused
  `extractUncovered` when short (`Journal.draw_two`, `Journal.draw_short`); a frame enters at an
  empty heap (`frame_limits_are_segment_limits`).

**Send** (`Kernel/ObjectiveSend.lean`, `Kernel/Inbox.lean`). A frame may yield
`send {to: object n | slot n, method, args, allowance?}`, answered at once with `queued {slot}`;
the message id names its reply slot, whose only decider is that message's delivery
(`decide_delivery_refused`, `decides_own_slot`). The invocation declares `postage`, the envelope
each message is delivered under, and each send escrows its price (and its allowance) into the
purse of the queue holding it (`uncovered` otherwise; `Invocation.escrows_every_send`).
- **The target must be deliverable, decided at the send before anything is escrowed**: an object,
  with state, whose method loads at the target's pin, types the arguments, and whose Plan is
  within what a delivered method may do (`Mail.send_object_deliverable`). Refusals:
  `notAnObject`, `stateMissing`, `notCallable`, `argumentType`, `notDeliverable` (its Plan admits
  `send` and the message carries no allowance covering an onward send, or admits `stop`/`cancel`).
  A send to `slot n` (the reply of an undelivered message) queues on that slot and is checked the
  same way when the reply resolves to an object; otherwise it is refunded.
- **Inboxes** are per-(sender, target) FIFO queues of at most 16 (`queueFull`). The queue
  discipline is push, pop or withdraw, nothing else (`Inbox.Lawful`, `lawful_fifo`;
  `reorder_unlawful` is the tooth). `deliverMessage` (anyone) pops the head, checks that the reply
  slot answers to that inbox, and runs the target's method with `request/caller` the sender and no
  subject, paid from the inbox purse only (`debits_only_purse`). A failed delivery pops, decides
  `broken` naming the reason and commits no write (`failed_delivery_pops`).
- **Continuations** (GPT-6 row F). A message may carry a prepaid `allowance`, escrowed beside its
  postage, capped by the `allowance` the invoker signed (`allowanceExceeded`). Its delivered method
  may send onward only out of it, within fan-out `Inbox.fanOut` (4) and depth
  `Inbox.continuationDepth` (3); a send over a bound is refused by name (`fanOut 4`,
  `continuationDepth 3`, `allowanceExceeded need held`), the delivery decided `broken` and the
  whole allowance refunded: postage buys the attempt, the allowance only the continuation. What
  it does not spend returns to the payer. `escrow_conservation` proves, over the committed batch's
  own postings, that a send credits exactly its escrow, a delivery pays out exactly the popped
  escrow plus what was pipelined on its slot (with spent ≤ allowance), and a cancel refunds exactly
  what it withdrew. `MessageDelivery.onward_bounded` and `chain_total` bound what one message's
  chain can post.
- **The sender controls its own speech.** A frame of the SENDING object may yield `stop {slot}`
  (stop waiting: pipelined sends refunded, the slot unwatched and retired when decided; the
  message is still delivered) or `cancel {slot}` (withdraw a still-queued message: it and every
  send pipelined on its slot are refunded, the slot decided `cancelled`). Both are acked at the
  yield and applied at commit; anyone else is refused `notSender`. A cancel of a message that is
  still queued takes the withdraw branch (`Mail.control_cancel_withdraws`), and the refunds equal
  the escrow (`cancelRefunds_escrow`); a cancel that arrives after delivery is a no-op that
  refunds nothing.

**Evidence:** compiled and proved; executed on scratch native worlds by the pipeline rows `call`
(`objective-call-native-journey.py`, C1-C10: grants, view stability, the DAO row) and `send`
(`objective-send-native-journey.py`, S1-S18), each with planted Hosts that turn exactly their
rows red.

**Not built:** an activity's segment yielding `call` or `send` (the kernel performs only `await`
there), an activity awaiting a message reply (`messageAwaitNeedsInbox`), pipelining deeper than
one reply, objects holding capabilities.

## Seats

A seat (`Kernel/Seat.lean`, [SEATS.md](SEATS.md)) holds Book balances under an offer whose
safety is a law judged on every reallocation, with an exit no clause can forbid
(`seat_offer_safe_forever`, `exit_enabled`, `exit_pays_allocation`, `seat_conserves`). An offer
that wants nothing gives its holding away, so it must say so: an unmarked one is refused
`donationUnmarked`, and the marker on an offer that wants something `donationMarkedWithWant`
(`empty_want_requires_marker`, `marked_offer_has_empty_want`). A holding activity's end exits a
deadline seat only at or after its due height (`holder_respects_deadline`). A closed seat's account
is deregistered and its cell retired.
A contract's method is shown each open seat identity-blind: coordinate, role, terms, proposal
and allocation, and a principal (offerer, payee, holding activity) only if the offerer's
proposal discloses it (`Proposal.disclose`, default none; `SeatStore.seatView_identity_blind`).
The invoker is hidden the same way unless its `invoke` sets `discloseInvoker` (the call record's
`invoker` field; `SeatStore.callData_invoker_blind`).
Seats have a signed native route (`Kernel/SeatReceiver.lean`, Host operations 215-219,
`mini seat`; journey row `seats`), an activity may hold a seat, and an ending activity closes
the seats it holds in the same Book batch (`Kernel/ActivitySeatEnd.lean`).

## Liveness claims name their actors

No kernel turn runs by itself: every "can always", "is never stuck" or "is available" in this
document is an ENABLING theorem: the named turn is admitted when the named actor submits it and
its price is covered. The actors:

| progress | actor | paid from | theorem |
| --- | --- | --- | --- |
| an on-demand seat exits | its offerer | (no fee beyond the turn) | `exit_enabled` |
| a deadline seat exits | anyone, at or after the due height | the turn's submitter | `exit_after_deadline` |
| a held seat exits | the holding activity's end, deadline respected | that activity's ending turn | `exit_by_holder`, `holder_respects_deadline` |
| an await is abandoned | anyone, after its timeout | the activity's escrow | `abandon_returns_escrow`, `abandon_delivery_exclusive` |
| a queued message is delivered | anyone | the inbox purse | `MessageDelivery.decides_own_slot` |
| a parked activity resumes past grown state | any submitter adding `extra.heap` | the submitter | `Delivery.heap_priced` |
| a draining object's straggler ends | anyone, after the drain deadline | the activity's escrow | `abort_after_deadline_exclusive` |
| an activity chosen for rebirth restarts | anyone, after MIGRATE | its moved purse | `rebirth_from_stored_input` |
| an object migrates | anyone, once no old activity is live | the submitter (the migration's price) | `migrate_cannot_fail` |

If no such actor acts, nothing happens: an unclaimed deadline seat stays open and keeps its
allocation, an unabandoned await keeps its escrow.

## Native admission by re-execution

A member's invocation of an Objective method reaches an ordinary accepted receipt; there is
no proof carrier ([ZK.md](ZK.md)). Admission re-executes:

- **Publish.** `objective-publication` (`Host/ObjectivePackageAuthor.lean`) runs the Host's
  own front end on the package and publishes exactly `publishedCore`
  (`Compiler/ObjectiveBendPublication.lean`); package edition 3 names one front-end
  identity. Publication creates no authority.
- **Quote and sign.** The local Host derives the final command from the member's retained
  request and never accepts a remote command, output or input (`Host/ObjectiveInvocationQuote.lean`);
  `mini objective-invoke` signs a prepare intent for exactly that command, and the consent
  endpoint re-derives it before any header is signed.
- **Admit** (`Kernel/ObjectiveBendNativeAdmission.lean`, `prepareCore` then `admit`): the
  registered policy (edition 4) decodes and re-encodes exactly; the declared envelope is
  within the policy maximum (`capacityWithin`); the claim's `proofWork` is exactly the
  tariff's price of it (`tariffExact`; `Core.proofWork_pos`); the evaluator `objective-core4`
  is not disabled; funding is checked before execution; sources and inputs enter only as
  current authenticated reads with exact guards (`guardsExact`); the package must name the
  policy's front end, which must be the receiver's own, and the receiver **re-runs that front
  end**, admitting only a byte-identical typed core (`SourceSelection`, `Replayed`); the
  applied term is type-checked; then `executeWith` runs under the declared limits, the
  result is lowered to a Plan whose effects must equal the command's (`Output.exact`), and
  measured usage must fit the declared envelope (`fits`).
- **Commit and replay.** The ordinary durable path; a reopened Host re-executes during
  replay.

`objective-native-acceptance.py all` (journey row `objective`) publishes, invokes, checks the
Accepted receipt, tries thirteen refusals (the package as its own source, a core that differs
from the replay, a foreign front-end pin, a foreign capability, a wrong query nonce, stale,
moved and stale-queried sources, a fee that is not the quote, a wrong tariff, an altered
argument, an injected output, and, on a second world, the evaluator disabled by name), then
stops, reopens and looks every receipt up again. **Integrated on scratch worlds.**

What admission proves (`Kernel/ObjectiveBendAdmissionSemantics.lean`):
`admitted_front_end` (the admitted typed core is byte-for-byte this front end's lowering of
the package's sources, and neither it nor the applied term is ever refused by the machine);
`admitted_source_semantics` (the admitted run is a finished `runBounded` of the applied term,
and the extracted Data is *the* deep reference evaluation of that term);
`admitted_data_unique` (two admissions of one term extract the same Data under any
capacities). An accepted receipt reaches these through
`AcceptedInvocation.objective_artifact_slot_sound`.

Every cell law sees, first in its state, the slot `objective/artifact`: the claimed method
artifact's identity, or `-1` for a command with no Objective claim
(`objective_artifact_slot_exact`). `Pred.objectivePin` is the package pin as a law clause
(`ordinary_objectivePin_refused`, `pinned_objectivePin_accepts`). The object kernel's law
view (`ObjectRecord.views`) carries the same slot, first, and every object's judged law leads
with the clause for its pinned package (`ObjectRecord.effectiveLaw`; see the object bullet
above), so the creator's own law can read `objective/artifact` too.

## What "law", "claim" and "requires" mean

- **A cell law** (`Pred`) is a decidable predicate over a write's old and new projected
  state and the request: the admission judge for every write, whoever proposed it. ENFORCED.
  An object's creator `law` in its record is one.
- **A package `law NAME: EXPR`** (top level of the package's entry module) is ENFORCED: the
  kernel installs it on every object created from the package and judges every write of the
  object's declared state by it. The fragment (`Compiler/ObjectiveBendLaw.lean`) is exactly
  what compiles to `Pred`: `REF == INT`, `REF <= INT`, `REF in [INT, ...]`, `REF == REF`,
  `REF <= REF`, `REF <= REF + INT`, `monotone(FIELD)`, `writeOnce(FIELD)`, combined with
  `not`, `and`, `or`, `implies`; `REF` is `new.FIELD` (a top-level natural or boolean field of
  the declared state) or `request.subject`/`caller`/`height`/`turn`. Anything else refuses at
  parse (`law outside the enforced fragment: ...`). The source artifact carries the laws and its
  identity commits them; the receiver's replay recomputes them (a tampered law is refused,
  `PublicationReplay` row 5). `create` and ADOPT read them from the pinned package's cell, never
  from the request, and refuse a law reading a field the declared state type does not hold
  (`lawField`). The judged law is `all [pin, package laws, creator's law]`; the seed is judged by
  `all [package laws, creator's law]`. Theorems: `Kernel.ObjectLaw.compile_sound` (the compiled
  predicate evaluates to the law's own meaning over the data, `LawExpr.denote`),
  `package_law_enforced` (every admitted write satisfies every package law),
  `Kernel.ObjectLawEnforced.package_law_not_removable`, and the teeth `capped_tally_teeth` over
  `tests/objective-native/CappedTally.obend`.
- **A domain law** (`registerDomain`, above) is a cell law over several objects' JOINT state,
  ENFORCED at the end of every turn that writes a member.
- **A spec `claim name(args): expr`** in `.obend` elaborates to a hidden knot field typed to
  return Bool and is listed in `SpecMeta` with status `unchecked`. Nothing evaluates or
  discharges it, and it never reaches admission; `claim impossible: false` is accepted (probe
  W08). It was spelled `law` until 2026-10-07; that spelling now refuses at parse
  (`law_keyword_refused`): in `.obend`, `law` names an ENFORCED predicate (GPT-6 row G: a
  top-level package law, above), and an unchecked property must not borrow the word.
- **A spec `requires m(…)`** declares a member needed from the final self; it is checked
  (above). It is not a precondition.

A package states its objects' admission law with top-level `law` declarations (above). A law
reads the declared state only through the fragment; nested paths (`new.a.b`) are refused in
edition 1.

## What is proved

The Core4 proofs live in `Theory/ObjectiveBend*.lean`; the kernel's and front end's in the
named modules. They build in the `ObjectiveProofs` library (`ObjectiveProofs.lean`), not the
default target. The gate `scripts/check-objective-proofs.sh proofs` builds it and requires the
every declaration's statement, definition closure (a SHA-256 Merkle hash of the body of every
repository definition its statement reaches) and exact axiom set to match its row in the
per-module contract manifests, or a reviewed line of `scripts/gates/objective-contract-changes.txt`
to admit that exact change (additions pass); every pinned axiom set is within `propext`, `Classical.choice`, `Quot.sound`. Compiled code
runs the machine through proven-equal `@[csimp]` replacements (`stepRaw_eq_fast`,
`step_eq_fast`, `runBounded_eq_fast`, `forceWith_eq_fast`): the compiler's substitution is
trusted, the equalities are theorems.

**Core4 semantics** (scope: closed Core4 terms; nothing here mentions `.obend`):

| Theorem | Statement in words | Premises |
| --- | --- | --- |
| `sourceStep_deterministic`, `source_evaluates_unique` | the reference step and evaluation are deterministic | none |
| `runBounded_natural_sound`, `_boolean_sound`, `_label_sound`, `runBounded_value_sound` | a finished bounded run's result is the reference evaluation of the term (scalars; for any value, weak head) | `Scoped 0`; the run finished |
| `runBounded_observation_sound`, `runBounded_resource_independent` | ground observations agree with the reference; two finished runs under different limits observe the same | closed; finished |
| `machine_evaluation_complete` (`rawRun_finite_completion`) | a closed term the reference evaluates to an observable value is finished by the machine in finitely many steps; `coreRepresentation` inhabits `Representation` | `Scoped 0`, `Evaluates`, `Observes` |
| `typed_stepRaw_preserved` | every machine step preserves heap, control and stack typing | a typed state (`checked_initial_state`) |
| `checked_reachable_no_refusal`, `check_runBounded_no_refusal` | a checked closed term never reaches any refusal (wrong operand, missing field, unbound reference, `sharedEffect`) at any limits; divergence, blackholes and suspension remain possible | `Checked source []` |
| `typed_yield_quiescent`, `stack_activity_signature`, `typed_resume_preserved` | a typed yield forces no shared cell, carries the program's own Plan/Response types, and resuming it with a typed response gives a typed state | a typed state; a typed response |
| `state_roundTrip` | the checkpoint codec restores every machine state | none |
| `execution_source_semantics`, `deepEvaluates_unique`, `execution_data_unique` | a successful `executeWith` is a finished `runBounded`, its Data is the deep reference evaluation, and two executions of one term under any policies extract the same Data | `Scoped 0`; an `ExecutionWith` |
| `forceWith_unrestricted`, `forceWith_policy_suspends` | a capacity policy can only stop a run early, retaining its state | none |
| `mix_append`, `composition_associative` | homogeneous extension lists compose associatively | on the separate list model `ObjectiveBendExtensions`; no theorem ties it to `Term.mix` |

**Templates** (scope: the checker): `Discharges.infer_instantiate`,
`Discharges.check_instantiate` (above).

**Composition contract** (scope: the contract algebra `chainFix` runs, not the source):
`run_append`, `run_assoc`, `checkLayer_ok`, `discharge_ok` (above).

**Front end** (scope: the elaborator's output, not the source):
`Compiler/ObjectiveBendFrontEndAdequacy.lean` proves that whenever the checker accepts the
front end's own packet, the erased term is closed and typed (`accepted_typed`), never refused
by the machine (`accepted_never_refused`), and a finished run extracts its unique deep
evaluation (`accepted_execution_semantics`); `accept_inhabited` exhibits a program.
`decode_json` and `decodePacket_term` prove that the checker's decoder inverts the front
end's rendering, so the receiver types the front end's own term, never a parse of the
published bytes.

**Kernel** (scope: the Lean kernel model of each turn): the theorems named in the sections
above, and `admitted_front_end`, `admitted_source_semantics`, `admitted_data_unique`.

**Not proved, though it reads like it:** `TotalProof law := law`; `checked_erasure` and the
prepared output's `native_matches`/`no_returns` are projections; `ExecutionWith.runExact`
records that a value came from the call that produced it.

## What is open

- **Surface semantics** (OB1, LT3). `.obend` has no meaning of its own, so nothing states that
  the core means what the source says; the front end is trusted, and what is proved is about
  its output. This includes compose order, C4 ancestry and method combination:
  `OrderedPresentationInvariant` (`Compiler/ObjectiveBendC4.lean`) is a `Prop` nothing proves;
  the evidence is compiled vector theorems (`Compiler/ObjectiveBendC4Vectors.lean`: published
  precedence vectors and 4000 seeded DAGs).
- **Laws** (LT6, OB5): a package `law` is enforced, but only its fragment (no nested paths, no
  `old.` beyond `monotone`/`writeOnce`, no witnessed or hashed atoms); a spec `claim` is never
  checked; laws are not re-checked at each template instance's types.
- **Ecosystem** (LT5, OB5): no surface form names another package's root; no dynamic
  selection by label; no generative identity beyond the kernel's object ids.
- **Reflection** (LT4): a provenance-establishing prototype constructor; `R(Y M)` vs `Y(R∘M)`;
  resource observations stated as theorems; `composition_associative` tied to `Term.mix`.
- **Guardedness** (LT6): no check that a well-typed resident's segment terminates.
- **Machine**: a resource bound for completeness (completion is finite, not bounded); use
  counts at run time (quantities are static); `stepRaw` linear in the heap.
- **Kernel**: upgrade is single-turn MIGRATE only (no multi-turn `migrating` phase, cv
  01a1141b-d4b5), has no interface-compatibility check (no facet table, cv 01a1141b-d4d6) and no
  executed journey row (cv 01a1141b-d4f6); domains cannot be left or changed (cv 01a115c9-d990)
  and their judgment is not priced (cv 01a115c9-d9b7); a storage charge for packages, object
  records and state cells (an activity's record carries a refundable deposit); activities that call, send or await a message (above); objects holding capabilities.
- **Language** (OB3, OB6): a digest primitive callable from source (`Theory/ObjectiveBendDigest`
  exists; Core4 has no digest term); sum-typed entry arguments and unary `!`; `before` and
  `after` methods; sealing, `final`, field enumeration.
- **Registry** (OB4): Core4 is a named evaluator identity (`Compiler/Evaluator.lean`,
  `resolveName_objectiveCore4`), not an entry of `registry`, which holds only `nock`.

## Backends and privacy

The preview and admission run the Lean machine (`runBounded`, compiled through the `@[csimp]`
replacements). A hand-written C machine is checked against it by differential gates
(`check-objective-proofs.sh c` and `cgen`), with no refinement theorem and no Mini path that
invokes it. No route on main runs Objective Bend obliviously, in a circuit, or under FHE; the
oblivious-network and zk modules are in the opt-in `ResearchWip` library, and their refinement
premise is open ([ZK.md](ZK.md) Part 2). Laziness leaks through access pattern and timing, so a
private backend needs a both-arms lowering of `case` and a public resource bound; source `Nat`
is unbounded, so a bounded backend must fail stop, never wrap. Details:
[OBJECTIVE-BEND-BACKENDS.md](OBJECTIVE-BEND-BACKENDS.md).

## Sources

- **ltuo**: Rideau, Knauth and Amin, *The Land of the Ultimate Object*
  (<https://fare.tunes.org/files/cs/poof/ltuo.html>).
- **poof**: *Prototypes: Object-Orientation, Functionally*
  (<https://fare.tunes.org/files/cs/poof.pdf>).
- **EOOMI**: *The Essence of Object-Orientation: Modularity and Incrementality*, 2024 draft
  (<https://fare.tunes.org/files/cs/poof/eoomi2024.pdf>).
- **Houyhnhnm**: *Houyhnhnm Computing*, chapters 1–11 (<https://ngnghm.github.io/>).

These are design sources. The repository's semantics, theorem premises and admitted paths
determine what Objective Bend guarantees.
