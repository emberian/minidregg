# Executable methods on world-resident kinds

After-core source construction, 2026-10-02. This is not part of the finite native
core receiving freeze and has not yet passed Lean or a native journey.

A runtime type descriptor describes operations as well as storage. Faré's
`poof-paper.md` §5.1.2–5.2 makes the useful distinction between a descriptor and
the prototype/composition that constructs it. The first world-kind carrier
provided typed storage and restrictive export laws. It did not yet provide
member-authored executable behavior. This construction connects that behavior
to Mini's existing evaluator instead of adding an interpreter or a poll switch.

## One method mechanism

A kind declares exactly one ROM bytes field whose semantic identity is
`dregg/world/method-table/v1`. Its key-zero value is a strict, canonical
`DREGG/WORLD/METHODS` v1 table. Each entry holds a unique name, unique immutable
program ID, and distinct mappings from evaluator output coordinates to world
`(semantic field, key)` addresses. Display names and numeric field choices are
not reserved. Duplicate marker fields, names, program aliases, output coordinates,
or target addresses refuse. Outputs may target only numeric non-ROM fields.

This uses existing descriptor/default/birth/ROM machinery. The definition can
be revised for future instances; an existing instance retains its actual method
table, descriptor, and program identity. A program ID covers evaluator, code,
ABI, parameters and library identities. Reusing a program in multiple kinds is
possible with each kind's own explicit output-address bindings. A future
prototype mechanism can construct/combine these tables; this first table is not
an implementation of open recursion, method combination or arbitrary dispatch.

`WorldKindMethods.writes` loads the table from the actual retained instance,
selects the signed run claim's program, and maps each exact create/write to the
existing `Eval.FieldWrite`. It rejects repeated writes, byte effects, erasure,
and read actions. It does not supply a post, patch, capability scope or law.
`ResourceTransaction.commandWrites` now receives actual pre-stores and the
claimed program. `checkClaim` then uses the same evaluator resolver, exact sample,
fuel, output/step check and output/write equality as other program invocations.
The soundness statement retains this actual source-derived effect extraction.

The physical/semantic mutation path stays `WorldKindInstance.prepare` →
`WorldKindCell.preparePatch`. Capabilities still see semantic field IDs from the
actual inner footprint, never evaluator output-coordinate numbers. Local law,
current kind exports, room exports, read guards and signature admission remain
mandatory. A restrictive `ran(program)` law can require a checked method; a
method table does not itself grant authority or prohibit separately authorized
manual changes.

## Ordinary authoring and invocation

Definition defaults accept a method table JSON array for the explicitly declared
ROM bytes slot; Host source encodes it. Signed kind/instance views expose parsed
methods. The instance view also exposes source-generated pre-state sample slots;
the client does not recreate projection formulas.

`instance call PROPOSAL INSTANCE METHOD` reads the signed instance, resolves its
method, obtains ABI metadata, prepares a claim through existing op134, maps output
coordinates through the signed method table, and prepares an ordinary world
transaction. `submit PROPOSAL` remains the actual invocation. Repeating the call
with its proposal ID reuses the retained intent; it does not rerun or reprice.
The first convenience command supports one participant and source state slots.
Multi-participant programs use the existing composed invocation representation.

Program registration still uses existing op131 and `workspace create --storage
nock --program VERDICT`. A general friendly program-authoring shell command and
the real poll method journey remain receiving work. Rust method binding tests
pass; this does not qualify the source receiver.

## Actual compute funding, not command-byte maxCost

Existing exact steps flow into `ResourceCost.proofWork`, then the durable global
lifetime deployment meter. That is not a per-subject daily allowance or Book
credit debit. Unauthenticated op134 also lacks a funding gate. The C5 TODO must
not be described as already implemented.

The after-core policy is 1,000,000 admitted steps per subject per authenticated
clock day free, then one credit per step. Quota belongs to the subject, independently
of an optional funding account. Reuse the existing system-owned PayCell and Book:
shared PayCell v5 union reserves tag12 for RAM computeUsage(subject→day,steps),
tag13 for authenticated activation. Paid V2 owns tags7–11; no independent v5.
Legacy lift leaves compute namespaces absent. A prospective authenticated
activation cut must close legacy execution before its boundary; historical
same-day use must never silently become zero.

The receiving extension must derive the marginal quote from the loaded clock and
PayCell, admit exact signed payer consent under its actual account capability and
current law, and create a canonical Book burn. It must commit quota update, Book
post and method effect in one durable intent with exact replay first. Funding
can be checked against signed claimed steps before re-execution, but settlement
must require the exact checked step count. Refused methods consume neither
admitted quota nor credits. Concurrent claims contend on the PayCell/Book roots.
The operator's lifetime meter remains a separate limit.

The existing account `.move` wire can express consent, but generic account scalar
mutation does not implement this system debit. Recognizing a funding leg requires
explicit profile semantics and the real receiver connection; merely parsing it
is insufficient. Dry-run service also needs an explicit bounded or authenticated
policy; an unauthenticated `caller` must never spend that subject's balance.

## Qualification still required

1. Scoped Lean elaboration of method codec/adapter and changed proof consumers.
2. Shared PayCell v5 source union, closed carry/activation, source funding and
   authority bridge, atomic `DataIntent`, audit re-admission and native consumer.
3. Profile identities reflecting changed source semantics, without changing the
   frozen transaction8 tuple silently.
4. Real member-created poll method: register tiny Nock program, inspect table,
   tally/close via `instance call`, refuse altered outputs/foreign mapping,
   enforce restrictive exports, preserve old method meaning after kind revision.
5. Threshold/day/concurrent/replay funding poles and native cold reopen. No
   expensive suite or third Lean seat is authorized merely by this checklist.
