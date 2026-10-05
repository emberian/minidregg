# Objective Bend roadmap status

Audited at `next` = `0b46b223` (batch c14 on main `259a2fb0`), 2026-10-05, by lane
OB-ROADMAP. Every row was checked at source (the named module, theorem, Host closure pin
`scripts/gates/host-closure.pin`, `protocol/host-operations.json`, parser and elaborator
forms), not from commit subjects. Sources of the items: the roadmap and "open" lists of
[OBJECTIVE-BEND.md](../OBJECTIVE-BEND.md) and its sibling pages, the completion wave
OB1-OB8 and the LTUO rows LT0-LT6 (`redregg/work/OB-COMPLETION-20261005.md`,
`OB-LTUO-20261005.md`).

**built**: on `next`, with the commit. **partial**: what is missing is named. **unbuilt**:
nothing on `next`. Owner = the lane that holds it.

## Kernel, objects and routes

| Item | Status | Evidence / what is missing | Owner |
| --- | --- | --- | --- |
| Activity kernel (records, answer slots, resume contract, resume with view, exhaustion, abandon) | built | `8194e09d` `f69f44e9` `67362781` `d1ce7b0c` `7dd88709` | — |
| Native signed activity route | built, integrated on scratch worlds | `Kernel/ObjectiveActivityReceiver` (`34d803f8`); Host ops 210-214 registered (`259a2fb0`); `mini activity`; `objective-activity-native-acceptance.py`, journey row `activity` | — |
| Object record (a cell is an object only with a record; law judges every declared-state write) | built | `de9c84f7`, `eac4b18c`; native: `native_birth_on_pinned_object`, journey row `objectrecord` (`7b97da60`) | — |
| Program fault never wedges an await | built | `resumedSegment_never_refuses_program_fault` (`3573afaf`, ported from SCHOLAR-CALLS `8d1d3c0e`) | — |
| The Receiver judges every written cell's law | built | `77df1dec`; activity cells are `kernelOnly [.objectiveActivity]` | — |
| Package pin as a law (`Pred.objectivePin`) | partial | the clause and its theorems exist (`2a7c372b`); no turn installs it on an object, and `ObjectRecord.views` carries no `objective/artifact` slot, so a pin inside an object's law refuses every kernel write | LAWS-RECEIVER follow-up (unowned) |
| One public tariff | built | `Kernel/ObjectiveTariff` (`bf28dd19`) | — |
| Retention: storage charge for packages and checkpoints | partial | Book half `deregisterAccount` landed (`c74f3120`); package cell records its payer (`b29361a3`); the charge itself (activity half, `lane/retention-payers-wip 63ab055a`) not landed | RETENTION-PAYERS |
| Upgrade (record v2: state type, upgrade turn, `schemaVersion` migration, producer of `upgraded`) | partial | wave 1 `Kernel/ObjectStateType` landed (`4795b657`), consumed by no turn; `ObjectRecord` has no state-type field; no upgrade turn; nothing produces `upgraded` | UPGRADE |
| Turn gate (`stored_checkpoints_typed`) | unbuilt | | CHECKPOINT-INVARIANT |
| `ForcingTransparent` discharged | partial | still an open premise (`Kernel/ObjectiveResumeContract.lean:309`); refuting instance for a malformed yield `2c746bf8`; executed by the `transparency` gate only | FORCING-TRANSPARENT |
| Seats on a native route | unbuilt | `Kernel.Seat`/`Kernel.Invitation` compiled and proved (`6347dcb4`), not in the Host closure; no seat driver; activities do not hold seats | SEATS-NATIVE |
| **OB7 synchronous cross-object `call`** | unbuilt | no turn lets one object's method reach another object | **in progress: lane OB-ROADMAP** |
| **OB8 sends, inboxes, `message` awaits** (decider as role, escrowed postage, bounded queues, forwarding at slot resolution) | unbuilt | | **in progress: lane OB-ROADMAP (after OB7)** |
| Guardedness: a well-typed resident never diverges inside a turn | unbuilt | no check on self-calls under `perform`; LT6 extends it to all demanded recursion | OB-LTUO (LT6) |

## Core4 machine and metatheory

| Item | Status | Evidence / what is missing | Owner |
| --- | --- | --- | --- |
| OB2 machine primitives `- / % < <=` (`>` `>=` via `ifBool`) | built | `0afaf7f2`, `606e4e17`; `$prelude` deleted; cohort pins tick counts | — |
| OB3 digest primitive | partial | `Theory/ObjectiveBendDigest` (`d8f7ca48`: `binds_or_collides`, hiding ASSUMED) and the C export `minidregg_obend_digest` (allowlisted, `73858824`); NOT a Core4 `Primitive` arm (code 9 reserved), no typing/machine/surface `digest(a, b)`, so no `.obend` program can call it; ballot hiding not wired (`3c541dd5` pending) | W30-CORE4-DIGEST |
| OB4 uniqueness | partial | `deepEvaluates_unique` (`1f812657`); `Compiler/Evaluator.lean:453` still says "not yet proved unique" and Core4 is an `Identity`, not a `registry` entry a program record can name | unowned |
| W18 `stepRaw` linear in the heap | unbuilt | | W18-STEPRAW-LINEAR |
| Resource bound for completeness | unbuilt | `machine_evaluation_complete` gives finite completion only | unowned |
| Quantities at run time (a consumed mark for linear values) | unbuilt | use counts are static only | unowned |
| `Representation` docstring | stale | `Theory/ObjectiveBendOpenRecursion.lean:420` says "no instance is claimed"; `coreRepresentation` is one (Lean file, not edited by this docs pass) | unowned |
| Composition associativity tied to `Term.mix` | unbuilt | `composition_associative` is on the list model only | OB-LTUO (LT4) |

## Language and front end

| Item | Status | Evidence / what is missing | Owner |
| --- | --- | --- | --- |
| Sums, `case`, `ifBool`, activities in the source | built | see OBJECTIVE-BEND.md "Landed since" | — |
| Declared ancestry, C4, `around`, `combine` | built | elaborator; vectors in `Compiler/ObjectiveBendC4Vectors.lean` | — |
| `OrderedPresentationInvariant` (C4 theorem) | unbuilt | a `def … : Prop` at `Compiler/ObjectiveBendC4.lean:150`, unproved | OB-LTUO (LT3) |
| `before` / `after` methods | unbuilt | refused, `Compiler/ObjectiveBendElaborate.lean:1155` | OB-LTUO (elaborator) |
| OB5 checked `requires` / final-self discharge | unbuilt | parsed (`ObjectiveBendParse.lean:710`), carried as a string | OB-LTUO (LT2) |
| OB5 laws as clauses (`invariant`/`guard`/`permit`/`forbid` → `Pred`) | unbuilt | the parser knows no admission clause; a program cannot state its object's law | unowned (OB5; LT6 owns `law` status) |
| OB5 dynamic selection by label, generative identity | unbuilt | no dynamic `get` constructor | unowned (core) |
| A surface form naming another package's root | unbuilt | | OB-LTUO (LT5) |
| OB6 sum-typed entry arguments, unary `!` | unbuilt | `typedArgument` (`Compiler/ObjectiveBendElaborate.lean:1264`) has no `variant` arm; no unary `!` in the parser | OB6 (Sonnet) |
| OB1 / LT3 surface semantics and elaborator correctness | unbuilt | no theorem relates `.obend` source to the core term | OB-LTUO (LT3) |
| LT0 probes, LT1 `Specification<T>` closed under compose, LT2 modular typing, LT4 reflection contract, LT5 ecosystem | unbuilt | | OB-LTUO |
| Sealing, `final`, field enumeration / has-field, fresh persistent instances, governed live upgrade, a cost law | unbuilt | unranked in the overview | unowned |

## Not Objective Bend's, recorded so nobody looks here

Private execution (oblivious, circuit, FHE) and proof carriers: Mini admits by
re-execution ([ZK.md](../ZK.md)); nothing runs Objective Bend privately on main.
