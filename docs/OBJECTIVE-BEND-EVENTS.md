# Objective Bend activities and events

An Objective Bend method can now be an **activity**: a computation that hands a
typed Plan to the kernel, waits, and continues with the kernel's typed response.
A long-lived object built this way is a **resident**, and an **event** is an admitted
turn that resumes it. This page describes the language construct, its semantics and
typing, what is proved, how events are handled, and how it compares with deos-js,
Bread's JavaScript host. Design record: [EVENTS-DESIGN.txt](../EVENTS-DESIGN.txt).

Evidence classes as in [OBJECTIVE-BEND.md](OBJECTIVE-BEND.md): *authored*,
*compiled*, *executed*, *integrated*, *deployed*. Everything below is compiled and,
where it says so, executed in the clear preview. The kernel half, which persists an
activity and delivers its responses, is [below](#the-kernel-activity): compiled; its
native signed-command route is executed on `lane/activity-native-wip` and **not yet
landed** (it waits for the object record).

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

All in `Theory/ObjectiveBend*.lean`, compiled, no `sorry`, axioms pinned.

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
admitted turn. The kernel's activity record consumes one generation per resume; the
checkpoint itself is pure and repeatable, so fencing duplicate resumes is the
kernel's job (Kernel/Contracts: `retry_cannot_reconsume_row`).

## Events

An event is an admitted turn that resumes a resident with a typed response. The
resident yields a Plan, often an "await" naming what it waits for. The kernel admits
an `Invoke` cut on the resident (sender, event bytes, current law), checks the response
against the resident's declared Response type, resumes it, runs it to its next yield
and admits that Plan. Handlers are the arms of the match on the response. Ordering:
one activity has one generation chain, so resumes are totally ordered and later events
wait in the resident's mailbox. Deduplication: a retry is a new `AttemptId` of the
same `InvocationId`; charging is per invocation and the generation row is consumed
once, so a duplicate delivery cannot resume twice.

The preview stands in for the kernel: give it a list of responses and it runs to each
yield, prints the Plan, checks and applies the next response, and reports for every
turn the checkpoint size, that it round-trips (executed) and that the yield was
quiescent.

## The kernel activity

[Kernel/ObjectiveActivity](../Kernel/ObjectiveActivity.lean),
[Kernel/AnswerSlot](../Kernel/AnswerSlot.lean),
[Kernel/ObjectiveActivityWire](../Kernel/ObjectiveActivityWire.lean),
[Kernel/ObjectiveActivityCell](../Kernel/ObjectiveActivityCell.lean) and, in
`ObjectiveProofs`, [Kernel/ObjectiveResumeContract](../Kernel/ObjectiveResumeContract.lean).
Design: `redregg/designs/MINI-PROGRAM-MODEL-20261004.md` §A, §B, §D (answer slots), §G, T1.

- **Objects and cells.** An activity lives on an object: a native resource cell the
  authority layer issues capabilities on. The activity's cells are registry cells of
  their own role (`CanonicalCellRegistry.Kind.objectiveActivity`): the record
  (`recordCell domain object activity`), its answer slots, the object's declared state
  (`stateCell domain object`) and published packages. Each sits at a coordinate that is
  a function of the deployment domain, the role and a key (`ObjectiveActivityCell.coordinate`);
  the registry's loaded-and-final law pins every such cell to its coordinate, no birth
  may install the role (`UserShape`), and nothing but the activity kernel's turns writes
  it: these are protected coordinates (ids at or above 2^256, which no birth may use).
- **The record.** The yielded machine state, collected
  ([Theory/ObjectiveBendDemandCollect](../Theory/ObjectiveBendDemandCollect.lean): only
  the cells the yielded Plan and the stack reach, compacted and renumbered), as
  checkpoint bytes (the token stream of `encodeState`), their digest, the pinned package identity, the instantiating input,
  the generation, the escrow terms, and its phase
  (`awaiting await | done result | faulted reason`). An await has an id
  `H(record cell, generation, checkpoint digest)`, a source (an answer slot with one
  decider, or a due height; a `message` await is refused by name until inboxes exist),
  and a mandatory deadline height (yield height + `patience`).
- **Resume with view** (ROOT ruling 10-05). The object's declared state cell holds an
  `ObjectState {version, value}` ([Kernel/ObjectState](../Kernel/ObjectState.lean));
  every committed write installs the next version. An activity is resumed with
  `resumed {outcome, view}`: the outcome its await settled to, exactly (never replaced,
  never dropped), and `view = {version, state}`, the object's declared state read IN THE
  RESUMING TURN. The outcome sum is `reply R | refused | unknown | timedOut | broken |
  upgraded`; staleness is not an outcome.
- **Plans the kernel performs.** A yielded Plan is `await {write, on, patience}`. `write`
  is a record of field edits (`keep | set v | add n`), applied by the kernel to the state
  the activity was resumed with (`stateWrite`, the single point where a declared-state
  write is built), installing version + 1 against the root that state was read from. So
  no write is computed from a stale read: a delivery prepared on one snapshot is refused
  on any snapshot where the state moved, and a fresh delivery sees the move. A birth's
  first segment has seen no state: its write may `set` a field only when it creates the
  state cell (`blindWrite`), and a first yield on an object with no state must create it.
  A birth is refused unless the program's response type is `resumed {outcome, view}`,
  types every kernel outcome at its outcome type, and (when it yields) types the view of
  the state it leaves.
- **Typing data.** The kernel types the datum's closed Core4 term with the actual
  checker (`check`), annotating each injection with the constructor the declared type
  gives it, and requires the checked type to agree (`TypedData`). Inputs, replies and
  every delivered outcome go through it, so a delivered response carries exactly the
  premise of `typed_resume_preserved`.
- **Turns** (each is one `DataIntent`, all writes or none, under the admitting
  receiver's seal): `publish`, `birth` (instantiate, run to the first yield, commit
  record + state + slot + Book postings), `resolve` (the slot's decider, at or before
  the deadline, typed reply; spends the slot claim), `deliver` (anyone; settles the
  await from its slot, due height or deadline, reads the view, decodes
  the record cell's checkpoint, resumes with the typed outcome and view, runs to the next yield
  or end, commits the new record, the Plan's write, the next slot and the Book postings
  together; spends the await claim), `topUp` (anyone funds a purse), `writeState` (a
  holder of the object writes its declared state: a new version, which the next
  delivery's view shows). Every
  delivery of one await shares one transaction id: the exact retry replays, any other
  is a transaction conflict.
- **Fees on the Book.** In the deployment's credit asset, paid to its collector. An
  activity's purse is a Book account of its own (the record cell's id), registered by
  the birth with the payer's deposit. Every Core4 run pays the public price of its
  declared envelope; a yield reserves the await's fee pair in the purse (refused,
  `awaitsFunding`, when the purse cannot: the activity stays parked until a `topUp`);
  the turn that ends the await takes one of the pair; the purse returns to the payer's
  account when the activity ends. Each turn's postings are one admitted
  `CanonicalResourceKernel.Batch` (`Birth.conserves`, `Delivery.conserves`).
- **No native route yet.** The signed route (`Kernel/ObjectiveActivityReceiver`,
  Host ops 210-214, `mini activity`, object and account ownership, the native
  acceptance) is on `lane/activity-native-wip`: it waits for the object record
  (`Kernel/ObjectRecord`: the object's one package pin and declared state type) before
  any native command may birth an activity or write declared state. Until then nothing
  outside the kernel's own modules constructs these turns.

Theorems (compiled, `#assert_axioms`, no `sorry`): `resume_consumes_once` (for every
seal: after a delivery installs, no intent spending its await is ever accepted, and its
exact retry replays), `second_delivery_refused`, `slot_decided_once`,
`slot_single_decider`, `resume_outcome_preserved` (an await answered by its slot reaches
the activity exactly as decided), `resume_view_current` (the view is the state cell at the
delivering snapshot, and an accepted delivery found that cell's root unmoved),
`yield_write_from_current_read` (every state post is the Plan's write applied to the
view, version + 1, against the view's root), `moved_state_refuses`,
`stateWrite_unviewed_never_sets`, `resume_binds_checkpoint`, `resume_deterministic`,
`refund_measurement_free`, `submitter_charge_declared`, `yield_reserves_pair`,
`end_returns_purse`, `Birth.conserves`, `Delivery.conserves`, `TopUp.conserves`; in `ObjectiveProofs`,
`birth_checkpoint_typed` and `delivery_checkpoint_typed` (the collected checkpoint is
typed: `typed_collect`), `runSegment_collect` (resuming the collected checkpoint ends
the segment exactly as resuming the uncollected one: the same Plan, result or fault;
from `collect_resume_segment`, `related_collect` and the lockstep simulation of
`Theory/ObjectiveBendDemandCollectProofs`).

Executed (on the WIP route, `lane/activity-native-wip`): the native acceptance drives
[world/activity/Tally.obend](../world/activity/Tally.obend) on a scratch native world,
every turn a signed command, 59 rows, before resume with view (ownership, slot decider, typed replies, retry and
conflict, conflict carrying the reply, funding park, timeout, Book conservation, reopen,
and the collected checkpoint's size across twelve resumes).

Not yet: the native route (above); the object record (L3); a theorem that `add`-only
writes commute (executed by the two-tallies acceptance scenario on the native route);
exhaustion charged at the declared envelope; disposal of ended and abandoned records;
upgrade dispositions (DRAIN/ABORT and the `upgraded` outcome's producer);
sends, inboxes and `message` awaits; the object's law judging its declared-state writes
(L4); a storage deposit for packages and checkpoints.

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
from inside a program; snapshot and rewind; kernel delivery on the native signed-command
route (the kernel itself is above); a guardedness check; string operations beyond equality; the
`before`/`after` method qualifiers (now buildable on perform); dynamic `get`.

## Checks

```
bun native/bend-source/objective-elaborate-tests.ts
bun tests/objective-bend-source/check-parser.ts
bun native/bend-source/objective-elaborate-tv.ts NEW_DIR lake env lean --run Host/ObjectiveBendElaborateRun.lean
bun tests/objective-bend-source/check-preview.ts tests/objective-bend-source/preview-cohort.json NEW_DIR LEAN OLEAN_ROOT
```
