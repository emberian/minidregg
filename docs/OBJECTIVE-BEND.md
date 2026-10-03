# Objective Bend

Objective Bend brings programmable behavior, composable specifications and
persistent computation into Mini's governed shared world. The intention is that
members can author and extend their environment as routinely as web authors use
JavaScript: a review instrument, a document view, a community institution, a
resident's tool or a fictional world's rules can all be programs.

This page describes the language contract and explains the checked construction.
The [evidence index](evidence/2026-10-03-objective-bend.md) says which parts have
actually reached source checking, execution and native admission. The
[developer guide](DEVELOPING.md) gives the corresponding entrypoints.

## Bend means a particular language

The foundation is [`bend2/bendtt.lean` at revision
947db722640c86247849343657bf2f7ef01cb7f1](https://github.com/bendlang/bend/blob/947db722640c86247849343657bf2f7ef01cb7f1/bend2/bendtt.lean),
a dependent affine calculus. This is not a generic claim about earlier Bend or
HVM implementations. Mini retains the original in
[vendor/bend](../vendor/bend/PROVENANCE.json), including its license and explicit
compatibility patch; [BendTTSource](../Theory/BendTTSource.lean) wraps it for Mini.

A **Book** is the collection of checked definitions. Typing and live-use checking
are separate. The live runtime uses the core's `Eval` and `Walk` relations;
checker weak-head normalization is not the execution semantics.

The quantities explain an important design choice:

- `Q0` marks dead positions: they participate in checking, not live evaluation.
- `Q1` is affine: a live value is used at most once.
- `Q2` permits copying values admitted as immutable `Data`; arbitrary closures
  do not become copyable merely because a programmer calls them an object.

A case-tree call unfolds only when its argument spine can walk the tree. An
underapplied call retains its reference and normalized arguments. The admitted
calling discipline permits earlier definitions and restricted descending self
calls; arbitrary mutually recursive method graphs cannot be smuggled in through
an unchecked host dispatcher.

Upstream uses `Type : Type` and allows inconsistency in dead material. Its live
consistency argument relies on the live discipline together with typing. This is
why a source-to-core check, the live execution relation and any erasure/compiler
refinement must be distinguished when making a claim about an executable.

## Compose behavior before creating an instance

A **partial specification** contributes definitions while declaring what it still
needs. For example, a review specification can provide `review` while requiring
`catalog`. Another specification can provide the catalog. A third can strengthen
review with an audit and leave `audit` for its eventual user to supply.

An interface pairs a selector with its exact type. Composition must resolve those
demands, validate the behavior order, preserve definition/body correspondence,
and reject an incomplete or ill-typed result. A list of method names and parent
IDs alone is insufficient.

Two references make cooperative composition useful:

| Reference | What a method sees |
| --- | --- |
| `finalSelf` | The completed composition, including later overrides and supplied requirements. |
| `super` | The preceding provider in the declared composition order for this method. |

An inherited presentation can therefore call the final review implementation,
while an audit wrapper calls the earlier review implementation once and
strengthens its answer. All layers share the same final self; each override has
its own prior-provider cursor. Order matters where providers cooperate or
override. Behavior inheritance and the governance-policy graph are different
structures.

The persistent representation keeps immutable specification/method references and
admitted Data captures. Calling a method constructs an affine runtime closure.
This avoids treating a reusable specification as a mutable closure duplicated
outside the calculus. Fresh instances have their own identity and state;
composing a specification does not alias all instances into one resource.

This approach is informed by Rideau, Knauth and Amin's
[Prototypes: Object-Orientation, Functionally](https://fare.tunes.org/files/cs/poof.pdf):
incremental definitions cooperate through a final result and a prior result.
Objective Bend must realize that idea under its checked affine semantics and
Mini's persistent authority boundary; the paper's untyped fixed-point construction
is not itself an admitted Bend implementation.

## A real example: independently extending a review tool

The Workshop example has a catalog, review policy, audit extension and
presentation. These are ordinary authored Bend bodies. The composition adapter
in [ObjectiveBendWorkshop](../Compiler/ObjectiveBendWorkshop.lean) resolves their symbolic demands against
actual checked core entries.

This excerpt from [ReusableWorkshop.bend](../world/Workshop/ReusableWorkshop.bend) preserves the candidate and policy and
strengthens the inherited verdict:

```text
def strengthen(prior: Review.Recommendation, audited: Bool) -> Review.Recommendation:
  match prior:
    case Review.Recommendation{candidate, policy, ready}:
      Review.Recommendation{candidate, policy, Bool.and(ready, audited)}

def audited_review(inherited_review: @+key: Review.Candidate -> Review.Recommendation,
    audit: @+key: Review.Candidate -> Bool, +candidate: Review.Candidate) -> Review.Recommendation:
  strengthen(inherited_review(candidate), audit(candidate))
```

The callback parameters are affine closures. `+candidate` is reusable Data, so
both calls can examine it. In the partial spec, `inherited_review` is the exact
`super.review` demand and `audit` is `finalSelf.audit`. A separately authored
[MemberExtension.bend](../world/Workshop/MemberExtension.bend) supplies the missing audit:

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

That module also supplies an alternate presentation which consumes the final
review and changes the authored label. The source has general laws for refusing
revision zero and accepting positive revisions. The reusable wrapper has laws
showing that a denied review stays denied and that a failed audit denies.

The driver checks three distinct cases: composition before the audit provider
must report the missing requirement; adding the provider must link; adding the
alternate presentation must preserve the composed review dependency. It checks
the actual resulting Book rather than accepting symbolic method metadata as
executable evidence. See [the source-check recipe](DEVELOPING.md#check-the-authored-example)
for the complete source and command.

This example deliberately computes a **recommendation**. A positive review is
neither an authorization grant nor proof that the reviewed statement is true.
Its next consumer must use the exact candidate/source revision and current policy
when proposing any real world action. The same composition mechanism can support
a community rule, a scientific review workflow or a story-world instrument without
turning all of them into the same user interface.

## From a method result to a world change

A published source package binds original module bytes, sealed imports, the exact
elaborated Book and entry, codecs, interpreter/compiler versions, arithmetic,
effect and disclosure contracts, charging and public bounds. Source provenance
and executable identity are related but distinct. Formatting can change the
source artifact without changing executable meaning; a publisher's signature
does not grant authority to install the program on someone else's object.

A world method computes over a kernel-created invocation sample and returns a
**typed Plan**. Its contract includes exact dependencies, ordered proposed
effects, message envelopes, independent result slots, status and charge evidence.
Speculation has no ambient filesystem, network, FFI or world-mutation right.
The receiver checks the actual Plan under current capabilities, revocation,
installed laws, schemas, roots, payer consent and release policy.

Typed output must preserve distinctions between scalar fields, byte payloads,
content operations, ordered append streams, definitions and lifecycle changes.
Representing them as constructors is useful only when decoding and lowering
produce the exact native prepared transaction. Fresh-resource birth/retirement
cannot be declared atomic with arbitrary effects merely by adding a Plan tag.
Money uses the actual conserving Book/account transition; a raw scalar account
write is not a transfer.

Every admission dependency matters, including authority, kind/source revision,
budget, audience and expected-preimage roots. A copied reference confers an
address, not a capability. A query can require these dependencies even when it
writes no ordinary field. Reusing a compiled artifact does not cache authority.

Durable messages are proposed atomically with their sender's effects. Delivery
is a separate physical obligation; recipients run fresh governed invocations.
An independent private return need not be encoded as a public field mutation.
Retaining its ciphertext, deciding its outcome, and releasing it to a currently
authorized audience are separate transitions.

## A live environment includes ongoing computation

Reflection should let an authorized person inspect original source, import locks,
selected definitions, their composition and the actual execution profile. Views
consume authorized observations; a source annotation does not authenticate an
arbitrary value. Editing, previewing a branch and installing a change are separate
operations. A preview does not settle against current shared state.

Persistent instances retain governed state. A persistent **activity** additionally
retains where execution is: control, stack, environment, heap, pending arguments,
source/cost position, execution context and generation. Keeping a document or an
application's process ID is not the same as preserving its computation.

The activity contract uses Mini's existing durable store. A generated continuation
can suspend with a prepared Plan, wait for its exact admitted outcome and resume
with a result of the required type. External effects become dispatchable only
after the durable barrier. Lost replies retain the original identity and
uncertainty; restoring a checkpoint must not run a possibly completed effect
again under a fresh identity. Old workers must be fenced by current generation.

Inspection, suspension, cancellation, export and implementation migration have
their own authority. Method invocation does not grant permission to dump a private
heap. Restoring data never resurrects revoked rights. Changing implementation
requires a translation preserving residual computation and pending obligations;
changing behavior additionally requires an authorized evolution/migration law.

Two sources clarify the goal: Rideau's
[orthogonal persistence model](https://github.com/mighty-gerbils/gerbil-persist/blob/master/persist.md)
separates persistence from publication and synchronization, while
[Reflection with First-Class Implementations](https://fare.tunes.org/files/fci2017/fci.html)
asks how an interrupted concrete computation can reach an observable abstract
state with bounded administrative work. Neither requirement is discharged by
serializing an arbitrary object graph. Mini must connect complete machine state,
source simulation, native safe points and durable admission.

## Execution and privacy

Execution choices form a composable plan. A method might run natively for a public
part, use a reusable circuit for another part, and retain an encrypted result.
Backend names do not establish equivalence, secrecy or authority.

| Route | Required relation and trust boundary |
| --- | --- |
| Reference / checked machine | Exact admitted Book, live semantics, bounded resources and canonical result. A diagnostic refusal is not automatically a semantic crash theorem. |
| Native compiler | Source-to-native result/refinement on the declared numeric domain. Optimizer steps need not equal source steps. |
| Bounded oblivious execution | Same result plus the declared leakage bound for memory accesses, control, output shape and resource behavior. |
| General zkVM | A real proof verifier binding program, input/state commitments, profile, bounds, canonical output and charge. |
| Reusable circuit | Exact entry/domain specialization and sound lowering to the checked constraint system, with output binding. |
| Homomorphic execution | Exact arithmetic encoding, key/generation and noise/capacity assumptions, authentic result custody and authorized release. Approximate arithmetic needs its own error relation. |

Structural BendTT naturals and native bounded naturals are different numeric
contracts. Floating-point encodings and NaN behavior also require explicit
semantics. Backend physical work is not canonical gas; secret-dependent refunds
or failure timing can reveal a branch even when the value stays encrypted.

The disclosure profile names observers and what they can learn: code identity,
dependency addresses, branch and access shape, run length, result dimensions,
failures, storage lifetime and release. Traffic privacy additionally concerns
endpoint, timing and size observations across the real delivery schedule.
Encrypted computation alone does not provide it. Ciphertext correctness, proof
validity, custody entitlement and current release authority are separate claims.

Distributed effects also need actual agreement among the relevant domains:
reservation authority, dependency ordering, decision recovery and physical
installation. An engine certificate does not manufacture permission from a source
resource. Honest ingress assumptions, fault thresholds, capacity and recovery
reserve belong beside the supported profile. The dated index records the current
construction boundary for each route.

## Design lineage

Faré's [Houyhnhnm computing essays](https://ngnghm.github.io/blog/2015/08/02/chapter-1-the-way-houyhnhnms-compute/)
invite reasoning about a whole computing environment, including persistence and
evolution, rather than leaving those obligations to every application. Objective
Bend takes that as a design stimulus, not a claim to implement the essays in full.

Preoscript/LeanUWWeave is related prior research into authored invariants,
coordination and disclosure contracts. It is not another name for Objective Bend,
and no automatic lowering or runtime merger is implied. A narrow prior data-only
projection does not supply such a merger. Useful contracts must be
connected explicitly to Bend programs, actual observations and native admission.
