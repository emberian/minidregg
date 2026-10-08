# Emergent Smalltalk capsules

Three presentations at each strict decimal budget: fewer than 1,000, 2,000 or
3,000 UTF-8 bytes, including the title, whitespace and scope statement. All are
ASCII. These are alternative descriptions of the same source semantics, not
language variants. Automatafl is a separate package.

| Presentation | <1 KB | <2 KB | <3 KB |
| --- | --- | --- | --- |
| Rewrite relation and evaluation contexts | [rewrite-1k.txt](rewrite-1k.txt) | [rewrite-2k.txt](rewrite-2k.txt) | [rewrite-3k.txt](rewrite-3k.txt) |
| Transition algebra | [algebra-1k.txt](algebra-1k.txt) | [algebra-2k.txt](algebra-2k.txt) | [algebra-3k.txt](algebra-3k.txt) |
| Resumable evaluator pseudocode | [machine-1k.txt](machine-1k.txt) | [machine-2k.txt](machine-2k.txt) | [machine-3k.txt](machine-3k.txt) |

The byte counts and SHA-256 hashes are in [manifest.json](manifest.json).
Run `bun docs/objective-bend/capsules/check.ts` from the repository root to
check the exact published files and budgets.

The 1 KB files explicitly describe a projection: open recursion, lazy records,
effects and the governed object boundary. They omit other constructors and
protocol detail. The 2 KB files cover the complete reference core dynamics,
including primitive edge cases, demand order, raw yields and resumption, with
a small object contract. The 3 KB files add typing constraints and durable
interaction rules. Their typing accounts have different emphases; none is a
complete checker, admission algorithm, source grammar or wire specification.
Budget is not a claim of completeness beyond each file's stated scope.

Start with the rewrite 3 KB capsule for the common agent contract. The machine
2 KB capsule is the most direct implementation prompt. Algebra is useful for
factoring demand rules and host admission into explicit mathematical relations.
These preferences are editorial judgments, not results of a blind reconstruction
test. The three authors consulted the implementation. The pseudocode has not
been run as an interpreter, and prose inspection is not an equivalence proof.

## Why payer is outside the object tuple

The abstract object is `(id, code pin, versioned state, law)`; invocation adds
an authenticated principal and authority. Host policy supplies execution and
retention resources. The tuple is a semantic projection, not Mini's serialized
record layout. Eliding storage accounting does not erase resource admission.

Mini's [ObjectRecord](../../../Kernel/ObjectRecord.lean) stores a Book account
that funds the record and state cell. `admitWrite_payer_irrelevant` and
`judge_payer_irrelevant` prove that changing that field does not change the
corresponding write judgment. This supports omitting it from the common object
description. It does not prove that changing funding preserves retention,
execution availability or every observable host behavior.

The activity [escrow](../../../Kernel/ObjectiveActivity.lean) also has a field
called `payer`, but that one is a `SubjectId` used as the activity principal in
`factsOf`. The authenticated principal must remain. A Mini adapter still must
populate all required accounts, signatures, reserves and principal fields;
these capsules do not change that implementation.

## A small multi-language repository

A standalone conformance repository is a good destination. Keep one normative
Lean semantics, independent implementations, a common corpus and named host
profiles. Initially pin the relevant Mini source rather than fork its semantic
authority. A proposed layout is:

```text
capsules/          these compact contracts and exact byte manifests
spec/              pinned Lean terms, reductions, yields, observations
impl/python/       small transparent reference interpreter
impl/c/            independent evaluator or imported existing backend
conformance/       canonical AST, scripts of replies, fixtures, shrinking
profiles/mini/     authority, durability, resource and transport binding
examples/automatafl/ two-player game package, separate from language
```

This is a proposed extraction, not a newly published repository. Mini already
contains [a Lean C emitter](../../../Compiler/ObjectiveBendEmitC.lean),
[a C demand machine](../../../native/objective-emit/runtime.c), and
[a Python differential harness](../../../native/objective-emit/differential.py).
The Python harness is not a Python language implementation. The C runtime is
derived from the demand machine design and depends on Lean-generated ROM; it
is useful existing work, not a blind independent reading of a capsule. Its
emitter explicitly records that C refinement is not proved. No C qualification
was rerun for this documentation experiment.

Use a canonical core AST first, so parser differences do not mask evaluator
differences. Compare ground observations, stuck outcomes, yielded plans and
resumed traces. Probe lazy records/closures by elimination rather than comparing
their implementation representations. Separate finite fuel exhaustion from
semantic divergence. Independent evaluators need not take the same number of
steps; the existing C backend's stricter state/tick comparison remains useful
for its particular claim of matching the Lean demand machine.

The next useful small swarm is a blind reconstruction experiment: one fresh
agent per capsule, with only that capsule and a common AST/protocol interface,
builds an interpreter. Score held-out behavioral cases and missing-rule reports,
not just successful parses. Count the shared interface separately: it must not
silently supply semantics omitted from the capsule. Include unused divergence,
duplicate fields, strict AND, a wrong-typed left primitive operand followed by
a yielding right operand, inherited methods seeing overridden self, and
resumption under nested contexts. Test host profiles separately with stale
roots, current law changes, duplicate resume and an unknown commit outcome.

The aim is the smallest contract from which independent agents reconstruct the
same behavior. Byte golfing is only one part of that measurement.

## Source anchors

- [Core terms, values, Step, Yields](../../../Theory/ObjectiveBendOpenRecursion.lean)
- [Types and usage safety](../../../Theory/ObjectiveBendTypes.lean)
- [Modular typing](../MODULAR-TYPING.md)
- [Durable interaction contract](../../OBJECTIVE-BEND-EVENTS.md)
- [Two-player Automatafl comparison](../../../world/automatafl/README.md)

The original [capsule](../EMERGENT-SMALLTALK.txt) remains as a prose-oriented
presentation; it now separates funding and fixes the typing/sharing shorthand.
