# Objective Bend activities and events

An Objective Bend method can be an **activity**: a computation that hands a
typed Plan to the kernel, waits, and continues with the kernel's typed response.
A long-lived object built this way is a **resident**, and an **event** is an admitted
turn that resumes it. This page describes the language construct, its semantics and
typing, what is proved, how events are handled, and how it compares with deos-js,
Bread's JavaScript host. Design record: [EVENTS-DESIGN.txt](../EVENTS-DESIGN.txt).

Evidence classes as in [OBJECTIVE-BEND.md](OBJECTIVE-BEND.md): *authored*,
*compiled*, *executed*, *integrated*, *deployed*. The language half below is compiled
and, where it says so, executed in the clear preview. The kernel half, which persists
an activity and delivers its responses, is [below](#the-kernel-activity): compiled and
proved in Lean on main, with the stored checkpoint's transparency executed by a gate.
**No native route reaches it on main**: `Kernel.ObjectiveActivity`, `Kernel.AnswerSlot`,
`Kernel.ObjectRecord` and `Kernel.ObjectState` are not in the Host closure
(`scripts/gates/host-closure.pin:490-500` lists only `Kernel.ObjectiveActivityCell` of
them), so no Host operation births, delivers to or writes an activity, and no activity
has run on a native Host. In flight: ACTIVITY-ROUTE (the receiver and Host ops),
RETENTION-PAYERS, UPGRADE, CHECKPOINT-INVARIANT, FORCING-TRANSPARENT, SCHOLAR-CALLS.

## In the source

```text
sum Plan:
  write: {field: Nat, before: Nat, after: Nat}
sum Response:
  written: {}
  refused: {}

def serve(count: Nat) -> Activity<Plan, Response, Nat>:
  match perform(Plan.write({field: 0n, before: count, after: count + 1n})):
    case written(_): serve(count + 1n)
    case refused(_): serve(count)
```

- `Activity<P, R, A>` is the type of a computation that may yield Plans of type `P`
  (a sum of first-order actions), is resumed with responses of type `R` (first-order
  data) and finishes with an `A`.
- `perform(plan)` yields `plan`. It is allowed only in a definition whose result is an
  Activity.
- Matching on a `perform`, or on a call to another activity, sequences: the arms are
  the handlers for the response. A pure result in tail position is lifted
  automatically; you never write a `return`.
- An activity is never a value you can store. The elaborators refuse, by name, an
  activity used as an argument (`effect-as-argument`), in a record or extend field
  (`effect-in-field`), as a sum payload (`effect-in-payload`) or inside a Plan
  (`effect-in-plan`), `perform` outside an activity (`perform-outside-activity`), and
  an activity definition without parameters (`nullary-activity`): a parameterless
  definition is a shared lazy value, so its effect would run once and be cached.

Examples, all in `tests/objective-bend-source/` and in the preview cohort:
`EventCounter` (a write, then its outcome; `serve` loops forever),
`DocumentWatcher` (handles append events), `TimerResident` (yields a reservation,
counts firings until cancelled), `DeosCounter` (Bread's counter applet; see below).

## Semantics

Core4 gains two terms ([OpenRecursion](../Theory/ObjectiveBendOpenRecursion.lean)):

| Term | Meaning |
| --- | --- |
| `perform plan` | not a value and never a reduction: a program whose next redex is a perform has **yielded** |
| `done v` | reduces to `v`; the elaborator inserts it for pure tails of an activity |

The reference relation `Step` is unchanged apart from `done`. `Yields t plan ctx`
says the next redex of `t` is `perform plan` in evaluation context `ctx` (one context
frame per congruence rule of `Step`); resuming plugs the response into `ctx`.
`Interaction t turns v` runs a program against a list of (plan, response) turns.
A yielded term does not `Step` (`yields_no_step`), and its plan and context are unique
(`yields_deterministic`).

The demand machine ([DemandMachine](../Theory/ObjectiveBendDemandMachine.lean)):

- `evaluate (perform p)` with an update frame on the stack (a shared cell is being
  forced) is **refused** with `sharedEffect`. Otherwise the plan becomes one lazy heap
  cell and the control becomes `yielded address`. The yielded state is the whole
  checkpoint; `step`/`runBounded` report `Outcome.yielded`.
- `resume response state` is defined only on a yielded state. It sets the control to
  evaluate the (closed) response and changes nothing else.
- The Plan is extracted with the same budgeted materialization as any data
  (`DemandData.yieldedPlan`); a response is decoded data checked against the declared
  response type (`Data.conforms`) and turned into a term (`Data.term`).

## Types

Effects are a **type**; partiality stays a **judgment** (this answers the Objective
council's open question). An effect has to be visible at every call site, because
calling an effectful method inside a field or argument would suspend the effect into
a shared thunk, and only the callee's type tells the caller. Divergence needs no such
visibility: sharing a divergent thunk changes nothing, and the blackhole already
observes it.

[Typing](../Theory/ObjectiveBendTyping.lean) adds `Ty.computation P R A` and three
rules: `perform` (plan is a sum of first-order data, response is data), `done`, and
`effectCase` (case on an activity, every arm an activity of the same P, R). An
activity type is never shareable, and every rule that allocates a heap cell (record
and extend fields, specification and prototype components, sum payloads, arguments)
refuses it. Type agreement never crosses between an activity and a suspendable type
(`sameType_isComputation`). Named checker facts: `effect_case_accepted`,
`pure_arm_without_done_refused`, `effect_as_argument_refused` (with
`pure_affine_argument_accepted` as its control), `effect_in_record_field_refused`,
`effect_in_payload_refused`, `effect_in_specification_refused`, `scalar_plan_refused`,
`closure_response_refused`.

## What is proved

All in `Theory/ObjectiveBend*.lean`, compiled, no `sorry`; each theorem's exact axiom set
is pinned in `scripts/gates/objective-axioms.pin` and its statement in
`scripts/gates/objective-statements.snapshot` (gate `scripts/check-objective-proofs.sh
proofs`). The kernel's theorems about activities are
[further down](#the-kernel-activity).

| Theorem | In plain words |
| --- | --- |
| `typed_stepRaw_preserved` (statement unchanged) | Typing is preserved by every step, now including perform, done and a yield. |
| `checked_reachable_no_refusal` (statement unchanged) | A checked program never reaches any refusal, which now includes `sharedEffect`: an effect is never inside a forced shared thunk. |
| `typed_yield_quiescent` | At a typed yield no frame forces a shared cell and no cell is half-evaluated: every yield is a safe point. |
| `stack_activity_signature` | Every yield of a checked program carries the program's own Plan and Response types, so the host may check responses against the entry's declared type. |
| `typed_resume_preserved` | Resuming a typed yield with a closed response typed at the program's Response type gives a typed state. `written_response_typed` inhabits the premise. |
| `ObjectiveBendCheckpointRoundTrip.state_roundTrip` | `decodeState (encodeState s) = some s` for every machine state. |
| `rawRun_terminating_resultControl` (statement unchanged) | A terminating pure source never yields. |
| `yields_no_step`, `yields_deterministic`, `one_turn_interaction` | Reference-level yield facts and a worked one-turn interaction. |

Not proved: that a well-typed resident never diverges inside a turn (it needs a
guardedness check on self-calls and termination of the pure part); that decoded data
conforming to `R` is a typed term (stated per value, as `written_response_typed`, not
in general).

## The turn boundary

Inside a turn, recursion is the existing lazy `fix`: a turn may diverge (a blackhole)
or run out of ticks (a resource suspension, which is never a turn). Across turns, a
resident is a guarded fixed point: its self-call sits in an arm of a match on a
perform, so each unfolding past a yield costs one resume, and each resume is one
admitted turn. The kernel's activity record consumes one generation per resume
(`delivery_advances_generation`, `Kernel/ObjectiveResumeContract.lean:593`); the
checkpoint itself is pure and repeatable, so fencing duplicate resumes is the kernel's
job ([the resume contract](#the-resume-contract)).

## Events

An event is an admitted turn that resumes a resident with a typed response. The
resident yields a Plan, often an "await" naming what it waits for. The kernel turn
`deliver` ([below](#turns)) checks the response against the resident's declared
Response type, resumes the stored checkpoint, runs it to its next yield and commits
that Plan. Handlers are the arms of the match on the response. Ordering: one activity
has one generation chain, so resumes are totally ordered. Deduplication: every
delivery of one await shares one transaction id (`deliveryTransaction`,
`Kernel/ObjectiveActivity.lean:315`), so the exact retry replays and any other delivery
is a transaction conflict; the await's claim is spent once
(`resume_consumes_once`, `:2067`). There are no inboxes: an await on a `message` is
refused by name (`messageAwaitNeedsInbox`, `:726`).

The preview stands in for the kernel: give it a list of responses and it runs to each
yield, prints the Plan, checks and applies the next response, and reports for every
turn the checkpoint size, that it round-trips (executed) and that the yield was
quiescent. A response is whatever the program's Response type says; a program the
kernel can run uses the kernel's own shapes, below.

## The kernel activity

[Kernel/ObjectiveActivity](../Kernel/ObjectiveActivity.lean) (record, turns, fees),
[Kernel/AnswerSlot](../Kernel/AnswerSlot.lean),
[Kernel/ObjectiveActivityCell](../Kernel/ObjectiveActivityCell.lean) (cell role and
coordinates), [Kernel/ObjectState](../Kernel/ObjectState.lean),
[Kernel/ObjectRecord](../Kernel/ObjectRecord.lean),
[Kernel/ObjectiveTariff](../Kernel/ObjectiveTariff.lean) and, in `ObjectiveProofs`,
[Kernel/ObjectiveResumeContract](../Kernel/ObjectiveResumeContract.lean). Line numbers
are for main at 4795b657. Evidence class: compiled and proved; not integrated (see the
top of this page).

The reference program is [world/activity/Tally.obend](../world/activity/Tally.obend):
its entry has type `Start -> Activity<Plan, Resumed, Nat>`, its Plan is the sum
`await {write, on, patience}`, and its Response is `resumed {outcome, view}`. A birth
refuses a program whose response type is not that shape (`responseParts`,
`Kernel/ObjectiveActivity.lean:541`; `typeResponse`, `:669`).

### Cells and records

- **Cells.** An activity lives on an object (a cell with an
  [object record](#objects-and-their-law)). Every other cell the kernel writes is a
  registry cell of the one role `objectiveActivity` with a sub-role: `record`, `slot`,
  `state`, `package` or `object` (`Kernel/ObjectiveActivityCell.lean:43-53`). A cell sits
  at `coordinate domain role key` (`:88-91`), an id at or above 2^256 (`reservedBase`,
  `:85`) that no birth may use; the registry's loaded-and-final law pins each cell to
  its coordinate (`:14-20`), so nothing but the activity kernel's turns writes them.
- **The record** (`Record`, `Kernel/ObjectiveActivity.lean:147-166`; frame
  `ACTIVITY-RECORD/v5`, `:223`): object, activity id, the package identity (`pin`), the
  instantiating input, `generation`, `checkpoint` bytes and their digest, the escrow
  (payer, the Book account the purse returns to, the declared resume and timeout
  envelopes and their fees), `tried` (the largest envelope an exhausted attempt at the
  current await ran under) and the phase `awaiting await | done result | faulted reason`
  (`:141`).
- **The checkpoint** is `collect (settle forced)`
  (`ObjectiveBendDemandCollect.checkpoint`, `Theory/ObjectiveBendDemandCollect.lean:195`)
  of the state the Plan extraction left, as the token stream of `encodeState`
  (`runSegment`, `Kernel/ObjectiveActivity.lean:749-758`). The extraction state has every
  cell it forced stored as its value; `settle` makes a cached cell stop retaining the
  closure it was forced from; `collect` keeps only the cells the yielded Plan and the
  stack reach, compacted. So a checkpoint is storage-charged for what the continuation can
  use, not for the suspended computations that produced a Plan field.
- **An await** (`Await`, `:121`) has an id `H(record cell, generation, checkpoint
  digest)` (`awaitId`, `:305`), a source (`reply slot decider`, or `height due`, `:114`)
  and a mandatory deadline, the yield height plus the Plan's `patience` (bounded by
  `Config.maxPatience`, `:334`).
- **Answer slots** (`Kernel/AnswerSlot.lean`). A reply await names a slot whose name is
  `H(turn, record cell, generation)` (`:100`), so no submitter chooses it. A slot has one
  decider, fixed when it opens, one deadline and one terminal decision, written once:
  `open --decider, at or before the deadline--> decided (reply | refused | unknown |
  broken)` (`decide`, `:125`) or `open --anyone, after the deadline--> expired`
  (`expire`, `:136`). Theorems: `decide_single_decider` (`:144`), `decided_refuses`
  (`:165`), `expire_after_deadline` (`:173`), `stranger_refused` (`:188`). A decision is
  written against the slot's open root AND spends the slot's claim
  (`Kernel/ObjectiveActivity.lean:1358`), so a second decision is refused twice over
  (`slot_decided_once`, `:2088`; `slot_single_decider`, `:2098`).

### Plans and views

- **Resume with view.** The object's declared state cell holds an `ObjectState
  {version, value}` (`Kernel/ObjectState.lean:18`); every committed write installs the
  next version. A delivery resumes the activity with `resumed {outcome, view}`
  (`responseData`, `Kernel/ObjectiveActivity.lean:533`): the outcome its await settled to,
  exactly (never replaced, never dropped), and `view = {version, state}`, the declared
  state read IN THE RESUMING TURN. The outcome sum is `reply R | refused | unknown |
  timedOut | broken | upgraded` (`AwaitOutcome`, `:505`; `kernelOutcomes`, `:538`);
  staleness is not an outcome, and nothing on main produces `upgraded`.
- **Plans the kernel performs.** A yielded Plan is `await {write, on, patience}`
  (`decodePlan`, `:714`). `write` is a record of per-field edits `keep | set v | add n`
  (`Edit`, `:881`), applied by the kernel to the state the activity was resumed with
  (`stateWrite`, `:971`, the one point where a declared-state write is built),
  installing version + 1 against the root that state was read from. So no write is
  computed from a stale read: `moved_state_refuses` (`:2400`), `resume_view_current`
  (`:2338`), `yield_write_from_current_read` (`:2370`). A birth's first segment has seen
  no state: its write may `set` a field only when it creates the state cell
  (`blindWrite`, `:416`; `stateWrite_unviewed_never_sets`, `:2520`). `add`-only writes
  commute (`add_writes_commute`, `:2493`).
- **Typing data.** The kernel types the datum's closed Core4 term with the actual checker
  (`check`), annotating each injection with the constructor the declared type gives it,
  and requires the checked type to agree (`TypedData`, `:484`; `typeData`, `:489`).
  Inputs, replies and every delivered outcome go through it, so a delivered response
  carries exactly the premise of `typed_resume_preserved`.
- **The program is the front end's output.** `publish` stores an activity artifact AND
  the source package it names, only after the kernel re-ran the Lean front end on the
  package and the artifact's typed core is that replay's rendering (`publish`, `:1131`;
  `ObjectiveBendPublication.Replayed`). Every later turn reloads the pair and replays
  (`loadProgram`, `:622`): the term an activity runs is the front end's output on the
  stored sources, never a parse of the core bytes (`Program.runs_front_end_output`,
  `:651`). The package cell records its payer, a registered Book account that funds the
  cell's retention; `publish` refuses one that is not (`Stored.payer`, `:256`;
  `payerRegistered`, `:1124`).

### Turns

Nine turns; each is ONE `DataIntent` built by `intentOf` under the admitting receiver's
seal, so its writes commit all together or not at all
(`Kernel/ObjectiveActivity.lean:17-21`):

| Turn | What it does |
| --- | --- |
| `publish` (`:1131`) | stores the artifact and its source package at the package cell, after the front end's replay |
| `create` (`:1993`) | a holder of the object installs its `ObjectRecord`; refuses a second record and a pin naming an unpublished package (`create_refuses_existing`, `:2986`) |
| `birth` (`:1233`) | instantiates the pinned definition with typed input, runs to the first yield, commits the record, the declared-state write, the answer slot and the Book postings; the object must have a record and the birth must name its pinned package (`birth_refuses_non_object`, `:2933`; `birth_refuses_other_pin`, `:2943`) |
| `resolve` (`:1358`) | the slot's one decider decides it, typed against the activity's response type, at or before the deadline |
| `deliver` (`:1496`) | anyone: settles the await from its slot, due height or deadline (past the deadline an open slot expires in this turn), reads the view, resumes the decoded stored checkpoint with the typed outcome and view, runs to the next yield or end, commits the new record, the Plan's write, the next slot and the postings together |
| `exhaust` (`:1676`) | a delivery whose own run runs out of its declared envelope, committed as a paid turn ([metering](#metering-and-disposal)) |
| `abandon` (`:1817`) | anyone, after the deadline plus grace: disposes of an await nobody ended |
| `topUp` (`:1881`) | anyone funds an activity's purse |
| `writeState` (`:1942`) | a holder of the object writes its declared state directly: a new version, which the next delivery's view shows |

### The resume contract

A delivery spends the await as a nullifier bound to the checkpoint digest AND writes the
record cell against its current root, so consume-once is a compare-and-swap at
admission's decide point (`Kernel/ObjectiveActivity.lean:36-39`). Proved:
`resume_consumes_once` (`:2067`: after a delivery installs, no intent spending its await
is ever accepted, and its exact retry replays), `second_delivery_refused` (`:2080`),
`resume_outcome_preserved` (`:2311`: an await answered by its slot reaches the activity
exactly as decided), `resume_binds_checkpoint` (`:2531`), `resume_deterministic`
(`:2547`). In `ObjectiveProofs`: a delivery advances the record one generation
(`delivery_advances_generation`, `Kernel/ObjectiveResumeContract.lean:593`); the installed
record is stated per phase, awaiting: the record just written
(`Delivery.installed_record`, `:562`), ended: reclaimed (`Delivery.installed_record_ended`,
`:576`); a second delivery of one await is a hash collision
(`second_same_await_is_collision`, `:614`). The stored checkpoint is typed
(`birth_checkpoint_typed`, `:124`; `delivery_checkpoint_typed`, `:151`) and resuming it ends
every segment as resuming the extraction's state would (`runSegment_checkpoint`, `:258`).

`runSegment_stored_complete` (`:319`, resuming the stored checkpoint ends every segment the
program's own yield ends, alike, with heap headroom of the forced state's size) holds
under the OPEN premise `ForcingTransparent` (`:310`), sharing transparency of the Plan
extraction's forcing. It has a satisfying point, `forcingTransparent_tally` (`:501`), and
refuting ones: `not_forcingTransparent_lostStack` (`:506`), and a malformed yield for which
the extraction succeeds and the premise fails (`not_forcingTransparent_dangling`, `:652`;
`forcingTransparent_not_of_extraction`, `:672`). A premise naming every address a yield
holds (`LexicalInvariant yielded`) is what a discharge needs; that is lane
FORCING-TRANSPARENT's work.

Executed, not proved: `scripts/check-objective-proofs.sh transparency` resumes every
activity of the preview cohort and the Tally run
(`native/objective-emit/activity-cohort.json`) from the stored checkpoint and from its own
yield and compares them per segment (outcome, Plan or result data, ticks), plus a growth
leg: TallyTwelve's stored checkpoint has one byte count over segments 1..12; a planted
checkpoint that drops the stack's cells must go red (`scripts/check-objective-proofs.sh:14-22`).

### Fees on the Book

Fees are Book postings in the deployment's credit asset, paid to its collector. An
activity's purse is a Book account of its own (`heldAccount`, `:321`: the record cell's
id), registered by the birth with the payer's deposit. The price is the one public
tariff of a declared envelope (`Kernel/ObjectiveTariff.lean`, shared with native Objective
admission): a turn that runs Core4 pays `tariff.workOf` of its DECLARED envelope
(`Capacity`), never of measured work. A declared envelope must cover the kernel's fixed
heap, stack, type-checking fuel and Plan budget (`Config.covers`, `:345`). A yield reserves
the await's fee pair in the purse (`resumeFee`, `timeoutFee`; `yield_reserves_pair`,
`:2614`), refused with `awaitsFunding` when the purse cannot (the activity stays parked
until a `topUp`); the turn that ends the await uses one of the pair; the purse returns to
the payer when the activity ends (`end_returns_purse`, `:2626`). No amount depends on how
much computation ran (`refund_measurement_free`, `:2586`; `submitter_charge_declared`,
`:2606`). Every turn's postings are one `CanonicalResourceKernel.Batch` admitted on the
loaded Book, so every turn conserves every asset: `Birth.conserves` (`:1303`),
`Delivery.conserves` (`:1581`), `Exhaustion.conserves` (`:1744`),
`Abandonment.conserves` (`:1851`), `TopUp.conserves` (`:1907`).

### Metering and disposal

- **Exhaustion is a paid turn.** An attempt whose run exhausts its declared envelope
  commits (`exhaust`, `Kernel/ObjectiveActivity.lean:1587-1612`): the purse pays the declared envelope of the ending
  path the first time this await exhausts (`tried = 0`), the submitter pays the public
  price of the envelope it adds, and nothing else changes: the await, checkpoint,
  generation and slot stay, and `tried` rises to the envelope the attempt ran under.
  `deliver` and `exhaust` refuse an attempt at or below `tried` before it runs
  (`alreadyExhausted`), so no attempt is ever run or paid twice.
  `exhaustion_charges_declared` (`:2647`), `exhaustion_spends_nothing` (`:2674`),
  `exhaustion_excludes_delivery` (`:2683`: for one record, snapshot, height and added
  envelope an exhaustion and a delivery never both exist), `exhaustion_charge_measurement_free`
  (`:2713`).
- **Tombstones.** An ended activity's record cell and a settled slot are written to the
  empty-body cell (`vacant`, `:790`; `recordBody_ended`, `:2743`): `delivery_end_vacates`
  (`:2769`), `birth_end_vacates` (`:2782`), `settle_reclaims_slot` (`:2797`),
  `delivery_reclaims_slot` (`:2831`). A reclaimed cell reads as nothing, by name: a late
  delivery is refused `recordMissing`, a late decision `slotMissing` (`recordOfBody_vacant`,
  `:2738`; `slotOfBody_vacant`, `:2740`).
- **Abandonment.** An await nobody ended (its decider never decided, its timeout was never
  delivered, every attempt exhausted and nobody funded the next) may be abandoned by
  anyone once the height passes its deadline plus `Config.abandonGrace` (`:339`). It
  spends the await's claim (so it races deliveries under consume-once), reclaims the record
  and the slot (an open slot's decision claim is spent with it), pays the timeout fee (or
  what the purse still holds of it) to the collector and returns the rest of the purse to
  the payer. `abandon_returns_escrow` (`:2842`), `abandon_closes_open_slot` (`:2859`),
  `Abandonment.spends` (`:2873`), `abandon_delivery_exclusive` (`:2882`).
- **A program fault.** A resumed segment that diverges or refuses commits `faulted`
  (`runSegment`, `:761-762`), but a malformed Plan or an unextractable result is a refusal
  of the turn (`decodePlan`, `:714`; `planExtraction`, `resultExtraction`), which leaves
  the activity parked at its yield. Lane SCHOLAR-CALLS is in flight on that wedge.

### Objects and their law

A cell is an object to the kernel exactly when it has a record (`ObjectRecord`,
`Kernel/ObjectRecord.lean:62-70`: id, `pin`, `schemaVersion`, `law`, `upgrade` policy,
`continuity`, `payer`; installed by `create`). Every declared-state write, a birth's or a
delivery's yield or a direct `writeState`, is judged by the object's law over the old and
new state plus the request facts (`admitWrite`, `Kernel/ObjectRecord.lean:202-209`;
facts `subject`, `height`, `target`, `turn`: `Facts`, `:168-175`), with the record read in the
same turn and its cell guarded. A delivery's write is judged with the activity's principal
(its birth subject, the escrow's payer) as subject, never the deliverer. A law refusal
refuses the whole turn and names the failing clause (`WriteRefusal`, `:194-199`): nothing
commits and the activity stays at its yield. Proved for the three writers of the state
cell: `Birth.write_judged` (`Kernel/ObjectiveActivity.lean:2904`), `Delivery.write_judged`
(`:2915`), `StateWrite.write_judged` (`:2925`), `writeState_refuses_lawless` (`:2958`).
These are statements about this module's own turns; the receiver that would be the only
writer of the state cell does not exist on main. The law sees the value, not the write
version or the declared type: typing a write at a declared state type
([Kernel/ObjectStateType](../Kernel/ObjectStateType.lean): a strict `Ty` codec, closed
first-order typing `typedAt` and value subtyping `stateSubtype`) is defined but no turn
consumes it yet, and `ObjectRecord` has no state-type field. The record's upgrade policy
(`frozen | governed authority floors`, `:57-60`) has theorems but no turn consumes it; the
upgrade turn, `schemaVersion` migration and the `upgraded` outcome's producer are not
built (lane UPGRADE).

### Not on main

The native signed route (Host ops, `mini` verbs, the receiver) and its acceptance
(`scripts/pipeline/journey-rows:66-78` runs one when a driver exists; none does); a
storage charge for packages and checkpoints (the payer is recorded; lane RETENTION-PAYERS);
upgrade dispositions; sends, inboxes and `message` awaits; the turn gate every turn goes
through (CHECKPOINT-INVARIANT); the object's law pinned to its package at birth
([the laws pin](OBJECTIVE-BEND.md#which-code-wrote-the-objectiveartifact-slot-and-the-package-pin)).


## Compared with deos-js

Bread's `deos-js` crate is a SpiderMonkey host (with a boa twin
kept equal by a differential test) over Bread's embedded executor. A cell is an
applet: its model is its state, its affordances are named turn templates
`{name, required, apply}` where `apply` maps the model and one argument to slot writes
from a closed vocabulary (`AddToSlot`, `SubFromSlot`, `SetSlot`, `SetSlotFromArg`,
`SetRegisterFromArgs`). `app.fire(name, arg)` checks `required ⊆ held` and commits one
verified turn whose receipt chains to the last. View state (`app.view`) is never a
turn; `deos.ui` builds a view tree as data; `deos.world` and `deos.cell` reflect, which
confers no authority. The law it embodies: an affordance is a cap-gated turn template,
firing is a turn, history is the receipt chain.

| deos-js | Objective Bend |
| --- | --- |
| affordance `{name, required, apply}` | a method of an object; reflection lists it |
| `apply`: a closed `ApplyOp` vocabulary | arbitrary pure code producing a Plan |
| `required ⊆ held`, checked by the host | the kernel's `Invoke` cut under current law; a program cannot grant itself authority |
| `app.fire` commits a turn | the method performs; the yield is the firing boundary and the response resumes it |
| per-process ledger of receipts | Mini's accepted history |
| manifest JSON in the cell heap | an immutable source package and its elaborated core |
| `deos.cell(...).reflect()` | `reflect` / `metadata` on specifications; world observation is the `Observe` cut |

Bread's counter applet (`deos-js/tests/js_drives_substance.rs` in Bread's repository, not this one: `inc`/`dec`/`reset` on
slot 0, `reset` needing a Proof credential) is
[DeosCounter.obend](../tests/objective-bend-source/DeosCounter.obend). Each affordance
yields one write and returns the new count if it was written, the old one if refused.
`reset`'s Proof requirement is the object's law, not code: the program cannot see or
change it, and a refusal comes back as `refused`.

What Objective Bend cannot do yet: a view library (a View sum is expressible, but Plans
and responses must be non-recursive data, so lists of children wait); live authoring and governed evolution;
more than one action per yield (no multi-cell turn in one step); crawling the world
from inside a program; snapshot and rewind; a native route for the kernel's turns (above);
a guardedness check; string operations beyond equality; the `before`/`after` method
qualifiers (buildable on `perform`, refused by the elaborator); dynamic `get`.

## Checks

```
bash scripts/check-objective-frontend.sh          # every row through the Lean front end,
                                                  # incl. activity-replay (the kernel replays a stored package)
bash scripts/check-objective-proofs.sh proofs     # ObjectiveProofs + the statement/axiom snapshot
bash scripts/check-objective-proofs.sh transparency  # stored checkpoint vs the machine's own yield
```
