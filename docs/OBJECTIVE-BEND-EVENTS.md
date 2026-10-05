# Objective Bend activities and the object kernel

Reference for activities: the language construct, its semantics and typing, and the kernel
that persists activities on objects, delivers their responses, and runs calls and sends
between objects. The overview is [OBJECTIVE-BEND.md](OBJECTIVE-BEND.md); the original design
record is [EVENTS-DESIGN.txt](../EVENTS-DESIGN.txt). Theorems are cited by name; each is in
`scripts/gates/objective-statements.snapshot` (Core4) or
`scripts/gates/objective-statements-mathlib.snapshot` (kernel).

## The construct

`Activity<P, R, A>` is a computation that may yield Plans of type `P` (a sum of first-order
data), is resumed with responses of type `R` (first-order data) and finishes with an `A`.
`perform(plan)` yields; it is allowed only in a definition whose result is an activity.
Matching on a `perform`, or on a call to another activity, sequences, and its arms are the
handlers; a pure tail is lifted with `done`. An activity is never a stored value: the front end
refuses, by name, `effect-as-argument`, `effect-in-field`, `effect-in-payload`,
`effect-in-plan`, `perform-outside-activity` and `nullary-activity` (a parameterless
definition is a shared lazy value, so its effect would run once and be cached). Worked
examples: [the overview](OBJECTIVE-BEND.md#activities), tutorial chapter 8, and the preview
cohort's `EventCounter`, `DocumentWatcher`, `TimerResident` and `DeosCounter`.

## Semantics and typing

| Term | Meaning |
| --- | --- |
| `perform plan` | not a value and never a reduction: a program whose next redex is a perform has yielded |
| `done v` | reduces to `v` |

Reference level (`Theory/ObjectiveBendOpenRecursion.lean`): `Yields t plan ctx` says the next
redex of `t` is `perform plan` in context `ctx`; a yielded term does not step
(`yields_no_step`), its plan and context are unique (`yields_deterministic`), and
`one_turn_interaction` is a worked turn.

Machine (`Theory/ObjectiveBendDemandMachine.lean`): `perform` with an update frame on the stack
(a shared cell being forced) is refused `sharedEffect` (`perform_under_update_refused`);
otherwise the Plan becomes one lazy heap cell and the state is `yielded`
(`perform_yields`). `resume response state` is defined only on a yielded state and sets the
control to the closed response, changing nothing else (`resume_requires_yield`,
`resume_keeps_heap_and_stack`). Plans and responses cross as Data, extracted by the same
budgeted materialization as any result.

Types (`Theory/ObjectiveBendTyping.lean`): `Ty.computation P R A` and three rules, `perform`
(the plan a sum of first-order data, the response data), `done`, and `effectCase`. An activity
type is never shareable, so every rule that allocates a heap cell refuses it
(`effect_as_argument_refused`, with control `pure_affine_argument_accepted`;
`effect_in_record_field_refused`, `effect_in_payload_refused`,
`effect_in_specification_refused`, `scalar_plan_refused`, `closure_response_refused`,
`pure_arm_without_done_refused`, `effect_case_accepted`, `sameType_isComputation`).

| Theorem | In words |
| --- | --- |
| `typed_stepRaw_preserved` | every step preserves typing, including perform, done and a yield |
| `checked_reachable_no_refusal` | a checked program never reaches a refusal, `sharedEffect` included |
| `typed_yield_quiescent` | at a typed yield no frame forces a shared cell and no cell is half-evaluated |
| `stack_activity_signature` | every yield carries the program's own Plan and Response types |
| `typed_resume_preserved` | resuming a typed yield with a closed, typed response gives a typed state; `written_response_typed` inhabits the premise |
| `state_roundTrip` | `decodeState (encodeState s) = some s` |
| `rawRun_terminating_resultControl` | a terminating pure source never yields |

Not proved: that a resident's segment terminates (no guardedness check), and that any decoded
data conforming to `R` is a typed term in general (the kernel types each datum with the checker
instead; below).

## The kernel

Modules: `Kernel/ObjectiveActivity.lean` (records, turns, fees), `ObjectiveActivityCell`,
`AnswerSlot`, `ObjectState`, `ObjectRecord`, `ObjectiveTariff`, `ObjectiveKernelConfig`,
`ObjectiveCall`, `ObjectiveSend`, `Inbox`, the receiver `ObjectiveActivityReceiver`, and in
`ObjectiveProofs` `ObjectiveResumeContract`, `ObjectiveCheckpointInvariant`,
`ObjectiveActivityGateRoute`. The reference resident is
[world/activity/Tally.obend](../world/activity/Tally.obend).

### Cells

An activity lives on an object, a cell with an `ObjectRecord`. Every other cell the kernel
writes has the one registry role `objectiveActivity` with a sub-role `record`, `slot`,
`state`, `package`, `object` or `inbox`, at a coordinate at or above 2^256 that no birth may
use. The ordinary route cannot write there: `ObjectiveActivityGate.ordinaryGate` refuses any
intent writing such a cell (`ordinaryGate_refuses`, `forged_protected_write_refused`), and
`NativeHost.Config.sourceGate` runs it for every facet but the object kernel's.

### Objects and their law

`ObjectRecord`: id, package `pin`, `schemaVersion`, `law`, `upgrade` policy, `continuity`,
`payer`; installed by `create`. The declared state cell holds `ObjectState {version, value}`;
each committed write installs the next version. Every declared-state write (a birth's or
delivery's yield, or a direct `writeState`) is judged by the object's law over the old and new
state and the request facts (`admitWrite`; facts `subject`, `height`, `target`, `turn`,
`caller`), with the record read in the same turn. A delivery's write is judged with the
activity's principal as subject, never the deliverer. A law refusal refuses the whole turn and
names the clause. Theorems: `Birth.write_judged`, `Delivery.write_judged`,
`StateWrite.write_judged`, `writeState_refuses_lawless`, `birth_refuses_non_object`,
`birth_refuses_other_pin`, `create_refuses_existing`.

### Records, checkpoints and awaits

- **Record** (frame `ACTIVITY-RECORD/v5`): object, activity id, package `pin`, input,
  `generation`, checkpoint bytes and digest, escrow (payer, purse account, declared resume and
  timeout envelopes and their fees), `tried` (the largest envelope an exhausted attempt at the
  current await ran under), and phase `awaiting await | done result | faulted reason`.
- **Checkpoint**: `collect (settle forced)` of the state the Plan extraction left
  (`ObjectiveBendDemandCollect.checkpoint`), as `encodeState` tokens. `settle` makes a forced
  cell stop retaining the closure it came from; `collect` keeps only what the Plan and stack
  reach. A checkpoint is sized by what the continuation can use.
- **Await**: id `H(record cell, generation, checkpoint digest)`, a source (`reply slot
  decider` or `height due`) and a mandatory deadline, the yield height plus the Plan's
  `patience` (at most `Config.maxPatience`).
- **Answer slots** (`Kernel/AnswerSlot.lean`): a name `H(turn, record cell, generation)` no
  submitter chooses; one decider fixed at opening (a subject, or for a message the role
  `delivery m`); one deadline; one terminal decision `reply | refused | unknown | broken`, or
  `expired` after the deadline. `decide_single_decider`, `decided_refuses`,
  `expire_after_deadline`, `stranger_refused`; the activity layer also spends the slot's claim
  (`slot_decided_once`, `slot_single_decider`).

### Plans and views

A kernel resident yields `await {write, on, patience}`: `write` is a record of per-field edits
`keep | set v | add n`, and `on` names the slot's decider or a height. It is resumed with
`resumed {outcome, view}`: the outcome exactly as settled
(`reply R | refused | unknown | timedOut | broken | upgraded`; nothing produces `upgraded`) and
`view = {version, state}` read **in the resuming turn**. A birth refuses a program whose
response type is not this shape. The kernel applies the edits to the state the activity was
resumed with, installing version + 1 against the root it was read from, so no write is computed
from a stale read (`resume_view_current`, `moved_state_refuses`,
`yield_write_from_current_read`); a birth's first segment has seen no state, so it may `set`
only when it creates the state cell (`stateWrite_unviewed_never_sets`); `add`-only writes
commute (`add_writes_commute`). An `await` on a message is refused `messageAwaitNeedsInbox`,
and the kernel performs no other Plan.

Every datum entering a program (inputs, replies, delivered outcomes) is typed by the actual
checker against the declared type (`TypedData`), so a delivered response carries exactly the
premise of `typed_resume_preserved`.

The program is the front end's output: `publish` stores an artifact and its source package only
after re-running the Lean front end, and every turn reloads and replays the pair
(`Program.runs_front_end_output`). The package cell records a registered payer.

### Turns

Eleven, each one `DataIntent` that commits all together or not at all, each a signed native
command (`Kernel/ObjectiveActivityReceiver.lean`: subject, nonce, authority root, turn, Ed25519
header; command edition `COMMAND/v4`; Host operations 210-214 plan, assemble, submit, lookup,
view; `mini activity`):

| Turn | Who | What |
| --- | --- | --- |
| `publish` | anyone | stores an artifact and its package after the front end's replay |
| `create` | an object holder | installs the `ObjectRecord`; refuses a second record or an unpublished pin |
| `birth` | an object holder with an account | instantiates the pinned definition with typed input, runs to the first yield, commits record, state write, slot and postings |
| `resolve` | the slot's decider | decides the slot, typed against the activity's response type, by the deadline |
| `deliver` | anyone | settles the await (from its slot, due height or deadline), reads the view, resumes the checkpoint, runs to the next yield or end, commits record, write, next slot and postings |
| `exhaust` | anyone | commits an attempt that ran out of its declared envelope as a paid turn |
| `abandon` | anyone, after deadline plus grace | disposes of an await nobody ended |
| `topUp` | anyone | funds an activity's purse |
| `writeState` | an object holder | writes the declared state directly, judged by the law |
| `invoke` | a capability holder with an account | a synchronous call tree (below) |
| `deliverMessage` | anyone | delivers the head of an inbox (below) |

The receiver writes only kernel cells and the Book (`intent_writes_activity_or_book`), and a
native birth runs only the pinned package (`native_birth_on_pinned_object`). Journey rows:
`activity` (`native/resource-client/objective-activity-native-acceptance.py`) and
`objectrecord` (`objectrecord-native-journey.py`), on scratch native worlds.

### The resume contract

A delivery spends the await as a nullifier bound to the checkpoint digest and writes the record
against its current root, so consume-once is a compare-and-swap at admission:
`resume_consumes_once` (and `native_delivery_consumes_once` at the receiver),
`resume_outcome_preserved`, `delivery_fields_bind_checkpoint`, `resume_deterministic`,
`delivery_advances_generation`, `Delivery.installed_record`, `Delivery.installed_record_ended`,
`second_same_await_is_collision`. The stored checkpoint is typed (`birth_checkpoint_typed`,
`delivery_checkpoint_typed`), and resuming it ends a segment as resuming the extraction's state
would (`runSegment_checkpoint`).

Across all reachable snapshots: `stored_checkpoints_typed`
(`Kernel/ObjectiveCheckpointInvariant.lean`) says every awaiting record's checkpoint is typed,
over a step relation of three kinds (an admitted kernel turn, an inert seat intent, a foreign
intent the ordinary gate admits); `derived_route` (`ObjectiveActivityGateRoute`) says every
record the replay walk admits is one of those kinds.

`runSegment_stored_complete`: resuming the stored checkpoint ends every segment the program's
own yield ends, alike, with heap headroom of the forced state's size, at every yield that names
only allocated addresses (`LexicalInvariant`). Its core is `forcingTransparent_of_yieldedPlan`:
a successful Plan extraction is a chain of finished closed demands, each a forcing chain
(`Theory/ObjectiveBendDemandForcingDemand.lean`, `demand_forces`), and along a forcing chain
the forced run ends every segment the lazy run ends (`Theory/ObjectiveBendDemandForcingExtract.lean`,
`forces_segment`). The first statement took `ForcingTransparent` as a premise of every yield
whose Plan extracts; that is refuted by a malformed yield for which the extraction succeeds and
the statement fails (`not_forcingTransparent_dangling`, `forcingTransparent_not_of_extraction`).
The repaired premise has poles (`lexicalInvariant_initialNat`, `not_lexicalInvariant_danglingYield`)
and is discharged for every checkpoint the kernel stores, since every such yield is typed:
`birth_stored_complete` (no premise), `delivery_stored_complete`, and on every reachable world
`reachable_delivery_stored_complete` (`Kernel/ObjectiveCheckpointInvariant.lean`, no premise but
the typed genesis). Not proved: the comparison runs the stored side with that heap headroom,
not under the kernel's own limits.
Executed, not proved: `scripts/check-objective-proofs.sh transparency` resumes every
activity of the preview cohort and `native/objective-emit/activity-cohort.json` both ways and
compares each segment (outcome, Data, ticks), plus a growth leg (TallyTwelve's checkpoint size
is constant over twelve replies; a planted checkpoint that drops the stack's cells must go red).

### Fees

Fees are Book postings in the deployment's credit asset. An activity's purse is a Book account
of its own. A turn that runs Core4 pays `Tariff.workOf` of its **declared** envelope, never of
measured work (`refund_measurement_free`, `submitter_charge_declared`); a declared envelope must
cover the kernel's fixed heap, stack, type fuel and Plan budget. A yield reserves the await's
resume/timeout fee pair in the purse (`yield_reserves_pair`), or the activity waits for a
`topUp` (`awaitsFunding`); the record also holds a refundable storage deposit priced by its size.
The purse returns to the payer when the activity ends (`end_returns_purse`). Every turn's
postings are one admitted Book batch and conserve every asset (`Birth.conserves`,
`Delivery.conserves`, `Exhaustion.conserves`, `Abandonment.conserves`, `TopUp.conserves`).
`publish`, `create`, `writeState`, `resolve` and `topUp` charge no tariff, and no turn charges for
storing packages, records or state.

### Metering, disposal and faults

- **Exhaustion is a paid turn.** An attempt that exhausts its declared envelope commits: the
  purse pays the ending path's envelope the first time this await exhausts, the submitter pays
  the price of the envelope it adds, `tried` rises to that envelope, and nothing else changes.
  `deliver` and `exhaust` refuse an attempt at or below `tried` before it runs
  (`alreadyExhausted`). `exhaustion_charges_declared`, `exhaustion_spends_nothing`,
  `exhaustion_excludes_delivery`, `exhaustion_charge_measurement_free`.
- **Retirement.** An ended record and a settled slot are written as the registry's retired
  image, so the id never returns; a late delivery is refused `recordRetired`, a late decision
  `slotRetired`. The ending turn sweeps the purse to the payer and closes it, and closes any
  seats the activity holds (`native_end_closes_held_seats`). `delivery_end_vacates`,
  `birth_end_vacates`, `settle_reclaims_slot`.
- **Abandonment.** Once the height passes the deadline plus `Config.abandonGrace`, anyone may
  abandon an await: it spends the await's claim (racing deliveries under consume-once),
  reclaims the record and slot, pays the timeout fee and returns the rest
  (`abandon_returns_escrow`, `abandon_closes_open_slot`, `Abandonment.spends`,
  `abandon_delivery_exclusive`).
- **Faults.** A resumed segment that diverges, refuses, yields a malformed Plan or bad
  patience, or ends with an unextractable result commits `faulted` and returns the unused
  escrow; it never refuses the turn, so a faulty program cannot park its activity
  (`resumedSegment_never_refuses_program_fault`). Running out of ticks is exhaustion, a fault
  only at the turn cap.

## Calls

`Kernel/ObjectiveCall.lean`. An `invoke` (`{kind: "invoke", object, objectCapability, method,
args, grants, envelope, postage, account, accountCapability}`) calls one method of one object,
which may call methods of other objects in the same turn, depth first, to `callDepth` 8.

- A method is a declaration of the object's pinned package, lowered by the kernel's own front
  end (`loadMethod`), of type `method(view: {version, state}, args: X) -> Activity<P, R,
  {result, write}>` with `P` labels among `call | send` and `R` among `returned | queued`.
  Every yield is answered in the same turn; a method whose Plan admits `await` is refused
  `notCallable`. Example: [world/call/Calls.obend](../world/call/Calls.obend).
- Re-entry is refused, naming the stack (`reentry_refused`; `invocation_reentry_free`).
- Writes apply at frame return, to the frame's own object, judged by that object's law on (the
  state the frame was shown, the new state); `invocation_writes_from_view`. Two calls to one
  object in one turn compose in order, and a callee never sees a caller's pending write.
- Authority: the root frame carries the signer, who must hold the object capability. A nested
  frame carries the signer as `request/subject` only under a scoped grant `{object, method,
  uses}`, spending one use (`grantSpent` when none is left); otherwise the subject is absent
  and every law atom reading it fails closed. `request/caller` names the calling object;
  `request/turn` is 5 in a call frame.
- One declared envelope covers the tree (`runCounted`, equal to `runBounded` by
  `runCounted_outcome`), paid at the tariff; exhaustion refuses the invocation and charges
  nothing. The root's result is the signing plan's `report` (`PLAN/v2`).

## Sends

`Kernel/ObjectiveSend.lean`, `Kernel/Inbox.lean`.

- A frame yields `send {to: object n | slot n, method, args}` and is answered at once with
  `queued {slot}`; the message id `H(turn, index)` also names its reply slot. The invocation's
  `postage` is the envelope each message is delivered under; each send escrows its price from
  the invocation's account into the purse of the queue holding it (`uncovered` otherwise).
- Inboxes are per-(sender, target) FIFO queues at a protected coordinate, at most
  `Inbox.bound` = 16 (`Inbox.Lawful`, `lawful_fifo`, `reorder_unlawful`, `Mail.inboxes_lawful`;
  `queueFull`).
- `deliverMessage {sender, target, message}` (anyone) pops the head and runs the target's
  method with `request/caller` the sender and no subject, under the escrowed envelope, paid from
  the inbox's purse only (`MessageDelivery.debits_only_purse`, `MessageDelivery.pops`). It
  decides the reply slot, whose decider is the role `delivery m` (`decide_delivery_refused`,
  `expire_delivery_refused`, `MessageDelivery.decides_own_slot`). A failed delivery (law, fault,
  exhaustion, not callable, a send from a delivered frame) pops, decides `broken` and commits no
  write (`MessageDelivery.failed_delivery_pops`).
- A send to `slot n` (the reply of an undelivered message) queues on that slot. The turn that
  decides the slot forwards each queued send into the inbox (its sender, n) when the reply is an
  object reference, moving its postage purse to purse; otherwise it is refunded. A send onto the
  reply of a send that is itself only queued on a slot is refused `notPipelinable`.

Evidence for calls and sends: compiled and proved; executed on scratch native worlds by
`native/resource-client/objective-call-native-journey.py` (C1-C8, world plants, a guard mutant
that commits 60 paid for 30 debited) and `objective-send-native-journey.py` (S1-S7). No journey
row of `scripts/pipeline/journey-rows` runs them.

## Not built

- A resident activity yielding `call` or `send`; an activity awaiting a message.
- Sends from a delivered message (refused as a failure: a delivery has no paying account);
  pipelining more than one level; objects holding capabilities.
- Upgrade: no upgrade turn, no producer of `upgraded`; `ObjectRecord` has no state-type field,
  and `Kernel/ObjectStateType` (a strict `Ty` codec, `typedAt`, `stateSubtype`) is consumed by
  no turn.
- A storage charge for packages, records, state cells, inboxes and decided slots.
- The package pin as an object's law: `Pred.objectivePin` exists, but no turn installs it and
  the object law view carries no `objective/artifact` slot
  ([overview](OBJECTIVE-BEND.md#native-admission-by-re-execution)).
- A guardedness check; the stored-checkpoint comparison under the kernel's own heap limits
  (it is proved with headroom of the forced state's size).

## Compared with deos-js

Bread's `deos-js` (a SpiderMonkey host over Bread's executor; not in this repository) treats a
cell as an applet: its affordances are named turn templates `{name, required, apply}`, where
`apply` maps the model and one argument to slot writes from a closed vocabulary, and
`app.fire(name, arg)` checks `required ⊆ held` and commits one turn.

| deos-js | Objective Bend |
| --- | --- |
| affordance `{name, required, apply}` | a method of an object |
| `apply`: a closed op vocabulary | arbitrary pure code producing a Plan |
| `required ⊆ held`, checked by the host | the object's law and the capability checks at admission; a program cannot grant itself authority |
| `app.fire` commits a turn | the method performs; the yield is the boundary, the response resumes it |
| a receipt chain | Mini's accepted history |
| `deos.cell(...).reflect()` | `reflect` / `metadata` on specifications |

Bread's counter applet is [DeosCounter.obend](../tests/objective-bend-source/DeosCounter.obend):
each affordance yields one write, and `reset`'s credential requirement is the object's law, not
code the program can see. Not expressible yet: a view library with lists of children (Plans
and responses are non-recursive data), more than one action per yield, crawling the world from
a program, snapshot and rewind.

## Checks

```text
bash scripts/check-objective-frontend.sh             # front end, incl. activity-replay
bash scripts/check-objective-proofs.sh proofs        # ObjectiveProofs + statement/axiom snapshots
bash scripts/check-objective-proofs.sh transparency  # stored checkpoint vs the machine's own yield
```
