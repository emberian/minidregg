# Objective Bend

Objective Bend is Mini's primary authored language and live computing environment:
people and agents should be able to build and extend documents, tools, communities,
services and fictional worlds using the same governed resources as built-in code.
Its core idea is **compose behavior as first-class specifications, execute it under
an explicit semantic profile, and admit its effects under current world authority**.
Nock remains supported for existing programs and history.

The source tools already check composed programs and execute real examples.
The complete authored Studio/native-effect workflow is still being joined.
Use the [developer guide](DEVELOPING.md) for commands and the
[dated evidence index](evidence/2026-10-03-objective-bend.md) for qualification;
this page explains the design and the source contracts a developer builds on.

## Compose a specification

A partial specification provides methods and declares the methods it requires.
An interface is a selector plus its exact core type. A catalog can supply lookup;
a review can require lookup; an audit extension can strengthen review while
requiring an audit supplied by another author. The partial specification remains
useful before those requirements are complete.

Composition has two forms of method access:

| Reference | Resolution |
| --- | --- |
| `finalSelf` | The final composition's matching provider, including later overrides. |
| `super` | The matching provider in the strict prefix before the current layer. |

All layers share final self. Each layer's super depends on its position. The
behavior order preserves declared ancestry, includes a diamond ancestor once,
and determines which matching provider wins. It is distinct from the graph of
governing laws: inheriting behavior grants no additional authority.

[ObjectiveBendComposition](../Compiler/ObjectiveBendComposition.lean) defines these
interfaces and selections; [Order](../Compiler/ObjectiveBendOrder.lean) checks the
order. [Prototype](../Compiler/ObjectiveBendPrototype.lean) reflects retained
partial source into specifications. [Persistence](../Compiler/ObjectiveBendPersistence.lean)
replaces authoring-local labels with immutable source identities. Open requirements
are declarations, not executable placeholder bodies. Stored capture environments
need qualified Data loading; the current sealing bridge refuses unsupported
captures rather than serializing arbitrary closures.

### Worked example: extending a review tool

The [Workshop source](../world/Workshop/README.md) separates catalog, review, audit
and presentation. Its [reusable review wrapper](../world/Workshop/ReusableWorkshop.bend)
contains this real Bend body:

```text
def audited_review(inherited_review: @+key: Review.Candidate -> Review.Recommendation,
    audit: @+key: Review.Candidate -> Bool, +candidate: Review.Candidate) -> Review.Recommendation:
  strengthen(inherited_review(candidate), audit(candidate))
```

`strengthen` retains the candidate and policy and combines the inherited verdict
with the audit using Boolean conjunction. The linker supplies `super.review` as
`inherited_review` and `finalSelf.audit` as `audit`. A separate
[member extension](../world/Workshop/MemberExtension.bend) provides that audit:

```text
def audit(+candidate: Review.Candidate) -> Bool:
  match candidate:
    case Review.Candidate{source, program, revision}:
      match revision:
        case 0n:
          False{}
        case 1n+prior:
          True{}
```

The extension also changes presentation while calling the final review. The
source includes laws showing that revision zero fails audit and an already-denied
review stays denied. The [composition driver](../examples/objective-bend-workshop/Run.lean)
requires the incomplete composition to report missing `finalSelf.audit`, then
checks completion and alternate presentation. The
[exporter](../examples/objective-bend-workshop/Export.lean) evaluates whole Card
results through the source evaluator. Follow the
[checked-core recipe](DEVELOPING.md#check-the-authored-example); editing `.bend`
without regenerating its core Book does not test the edit.

A recommendation is still just a program result. Installing its proposed change
requires the exact reviewed revision and current native authority.

## Check the actual program

The starting semantics are the dependent affine calculus in
[`bend2/bendtt.lean`, revision 947db722](https://github.com/bendlang/bend/blob/947db722640c86247849343657bf2f7ef01cb7f1/bend2/bendtt.lean).
Mini retains [upstream provenance](../vendor/bend/PROVENANCE.json) and the
[adapted kernel](../Theory/BendTTSource.lean). Bend itself may be forked or changed
when a concrete use case needs it. The obligation is to version the changed
semantics and artifacts, preserve historical program interpretation, and prove or
explicitly qualify the relevant refinement—not to preserve upstream unchanged.

A **Book** contains definitions. Typing and live-use checking are separate;
execution follows `Eval` and `Walk`, rather than the checker's weak-head
normalizer. Quantities control live use: `Q0` is dead, `Q1` is affine, and `Q2`
permits copying immutable `Data`. Thus the example can inspect `+candidate` twice,
while its callback closures remain affine. The kernel's `Type : Type` and dead
material must not be confused with its live consistency guarantee.

The [linker](OBJECTIVE-BEND-LINKER.md) resolves demands against exact source
entries, orders live dependencies, preserves the original helpers and checks the
complete resulting Book. The admitted call discipline permits earlier definitions
and restricted descending self calls. Arbitrary mutual recursion cannot be added
by placing an unchecked dispatcher behind method metadata.

A [source package](../Compiler/BendWorldSource.lean) seals original module bytes
and imports. Its [program artifact](../Compiler/BendWorldProgramCodec.lean) binds
the emitted Book, entry, checker/elaborator/compiler, arithmetic, codecs, effects,
charging, disclosure and bounds. Checking that Book does not by itself prove the
surface elaborator or optimized native compiler correct.

### Representation is part of the contract

Structural naturals under the reference semantics use unary constructors. Encoding
a native 63-bit identifier that way is impractical. The identity-byte ABI work
represents native IDs as canonical `StreamCodec.nat` bytes carried in bounded
source byte lists, with byte-range, full-consumption and re-encoding checks.
Scalar Plan and Surface ABI v2 are being adapted to this representation; prior
numeric-ABI checks do not qualify the replacement.

Opaque identity bytes are not an arithmetic implementation. Efficient arithmetic,
word representations and deeper Bend changes need their own typed operations,
bounds and refinement. Source naturals, native bounded integers and approximate
numeric backends cannot silently share the same equality or overflow promise.

## Admit effects and retain results

A method receives authenticated input and computes a proposed result. The common
[Plan](../Compiler/BendWorldPlan.lean) carries ordered typed native payloads,
declared read guards and independent return slots. Invocation/profile data binds
its charge, interpretation and execution evidence. The receiving path must decode
the **actual execution result** and match its effects to the actual command.

Current grants, revocation, governing laws, schemas, source revisions, read roots,
payer consent and release policy decide admission. A reference is an address,
not a grant; a cached executable does not cache permission. The receiver retains
implicit authority and accounting dependencies as well as program-declared reads.

Typed effects preserve content, append, definition and object-operation semantics.
Money goes through the conserving Book/account operation. Fresh-resource lifecycle
and arbitrary effects require an actual common atomic transaction, not merely a
new Plan constructor. Speculative evaluation has no ambient host I/O rights.

Durable message proposals, their physical delivery and recipient execution are
separate obligations. Private return slots can retain a result independently of
public field mutations. Ciphertext custody, outcome agreement and currently
authorized release are also distinct. These contracts let the same method serve
a workdesk, community or shared world without recreating a journal per application.

## Keep the environment live

Source inspection should expose original modules, locked imports, selected
providers, diagnostics and the execution profile. Authored views consume admitted
observations and separately prepared intents. The [Surface contract](OBJECTIVE-BEND-SURFACE.md)
supports this separation; its public route and full Studio workflow are not yet
registered as a completed native authoring experience.

A persistent instance has identity, governed state and pinned behavior. An
**activity** additionally retains control, stack, environment, heap, pending
arguments, cost position, execution context and generation. Its continuation can
wait for an exact admitted outcome and resume with a result of the required type.
The [persistent-computation contract](BEND-PERSISTENT-COMPUTATION-20261003.txt)
uses Mini's existing store and durable barrier. Lost replies retain uncertainty
and the original operation identity; restoration cannot replay a possibly completed
external effect under a fresh identity.

Inspection, suspension, cancellation, export and migration have separate authority.
Invoking a method does not authorize a private heap dump. Governed evolution must
name the state translation and preserve pending obligations; current generation
must fence old workers. Restoring bytes never restores revoked rights.

## Execution and privacy

Backends compose under an explicit semantic and disclosure contract:

| Route | What must be established |
| --- | --- |
| Checked/reference or native | Exact program/input/result relation, numeric domain and canonical charging; optimized instruction counts need not match source steps. |
| Bounded oblivious controller | Result correspondence plus the declared bound on control and memory-access leakage. |
| General zkVM | A real verifier binds exact program, state/input commitments, bounds, result and charge. |
| Reusable circuit | Sound specialization of the actual entry and input domain, with exact output binding. |
| Homomorphic execution | Arithmetic, key generation, noise/capacity and authentic result custody, followed by authorized release. |

The fixed-access [controller](../Compiler/BendObliviousController.lean) covers all
12 controls of the closure machine; its compiled conformance checks cover 64
concrete state/codec cases. General controller/codec/source refinement and a
malicious private backend remain separate work. Likewise, the executed Bool/BFV
fragment is evidence for that fragment, not arbitrary Bend compilation.

A privacy profile names observers and permitted leakage from code identity,
dependencies, branches, access patterns, timing, output shape and failure. Canonical
charges and refunds must respect that profile. Traffic privacy additionally needs
the real delivery schedule; distributed effects need reservation authority,
agreement, recovery and physical installation across the relevant domains.
The [evidence index](evidence/2026-10-03-objective-bend.md) records these receiving
boundaries without making backend labels stand in for guarantees.

## Design sources

Rideau, Knauth and Amin's
[Prototypes: Object-Orientation, Functionally](https://fare.tunes.org/files/cs/poof.pdf)
provides the model of incremental definitions cooperating through final self and
prior super. Rideau's
[orthogonal persistence model](https://github.com/mighty-gerbils/gerbil-persist/blob/master/persist.md)
and [First-Class Implementations](https://fare.tunes.org/files/fci2017/fci.html)
connect persistence, bounded observation and implementation change. The
[Houyhnhnm essays](https://ngnghm.github.io/blog/2015/08/02/chapter-1-the-way-houyhnhnms-compute/)
frame the whole computing environment as the design unit. These inform Objective
Bend; the actual source contracts and receiving paths determine what Mini supports.
