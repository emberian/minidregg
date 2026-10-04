# Objective Bend activities and events

An Objective Bend method can now be an **activity**: a computation that hands a
typed Plan to the kernel, waits, and continues with the kernel's typed response.
A long-lived object built this way is a **resident**, and an **event** is an admitted
turn that resumes it. This page describes the language construct, its semantics and
typing, what is proved, how events are handled, and how it compares with deos-js,
Bread's JavaScript host. Design record: [EVENTS-DESIGN.txt](../EVENTS-DESIGN.txt).

Evidence classes as in [OBJECTIVE-BEND.md](OBJECTIVE-BEND.md): *authored*,
*compiled*, *executed*, *integrated*, *deployed*. Everything below is compiled and,
where it says so, executed in the clear preview. **No kernel delivers responses or
persists an activity yet** (not integrated).

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
and responses must be non-recursive data, so lists of children wait); `-` and `<`
(saturating decrement is written by recursion); live authoring and governed evolution;
more than one action per yield (no multi-cell turn in one step); crawling the world
from inside a program; snapshot and rewind; kernel delivery of responses and persisted
activity checkpoints; a guardedness check; string operations beyond equality; the
`before`/`after` method qualifiers (now buildable on perform); dynamic `get`.

## Checks

```
bun native/bend-source/objective-elaborate-tests.ts
bun tests/objective-bend-source/check-parser.ts
bun native/bend-source/objective-elaborate-tv.ts NEW_DIR lake env lean --run Host/ObjectiveBendElaborateRun.lean
bun tests/objective-bend-source/check-preview.ts tests/objective-bend-source/preview-cohort.json NEW_DIR LEAN OLEAN_ROOT
```
