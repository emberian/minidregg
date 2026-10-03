# Objective Bend source linking

`Compiler.ObjectiveBendLinker` constructs one checked BendTT Book from exact
source helper definitions and composed partial methods. It does not introduce an
object evaluator. `Compiler.ObjectiveBendWorkshop` is a consumer using the actual
`ReusableWorkshop` and `MemberExtension` source helpers.

Behavioral ancestry order resolves `finalSelf` and `super`. It differs from core
declaration order: a base method can demand a helper supplied by a later member.
The linker performs stable topological ordering on live definition dependencies,
checks full reference closure, encodes/parses/checks the resulting Book, and
retains exact helper and generated method definitions. Self calls remain subject
to BendTT structural descent checking. Non-self live cycles receive focused
blocked-definition diagnostics. This construction is conservative; it does not
claim to admit every ordering accepted by the kernel or arbitrary fixed points.

Dead type syntax can refer forward. Recursive Data declarations depend on this.
Q0 arguments, annotations' types, type constructors, equality payloads and rewrite
motives do not impose live ordering. Rewrite evidence remains live. Full dead and
live references still participate in closure checking.

`Linked` carries actual equalities for the whole admitted Book, every original
helper, and every generated method, plus a permutation certificate for all source
definitions. `fromEntry` builds callback partial applications from exact admitted
source entries; fresh handwritten bodies cannot masquerade as those helpers.
`ObjectiveBendConstruction.construct` also validates finite ancestry, completion
and captured Data to produce the existing OO `Construction` certificate.

The general refinement module derives Book lookup equivalence and transports
`Eval` and exact-count source `Trace` across declaration reordering. Checker
liveness depends on declaration indices and is independently rechecked.

## Running the workshop consumer

The committed `MemberExtension.bendtt` is static emitted source code from the
sealed `MemberExtension.bend` package, retaining its original helper closure.
Its SHA256 is `b7bc7c8e5445c2a810ba2e51f930e732cb6a84d42bac536a956296046e3e91bb`.
It passed actual parsing/checking. To regenerate, use the sealed source adapter;
the runner also accepts other exact emitted Book paths:

Prepare matching compiled imports through the project's bounded-build policy,
then run the narrow source consumer:

```sh
lake env lean --run examples/objective-bend-workshop/Run.lean examples/objective-bend-workshop/MemberExtension.bendtt
```

The runner requires a precise missing `finalSelf.audit` diagnostic for the first
four layers, successful third-member completion, and a later presentation
extension. These are real kernel checks of source-linked methods. The six layers
are Catalog, Review, SafetyReview, Presentation, MemberAudit and
AlternatePresentation. Policy/catalog/label are immutable Data; per-call callbacks
remain affine source computations.

An optional exporter also runs dynamic Candidates through the shared
proof-producing `BendLiveMachine.executeChecked`, compares the whole resulting
Card, and writes canonical linked core bytes and provider/diagnostic JSON:

```sh
lake env lean --run examples/objective-bend-workshop/Export.lean examples/objective-bend-workshop/MemberExtension.bendtt output-directory
```

The emitted provider records expose selector, owner/provider, original helper
entry, generated core entry and resolved self/super demands. This demonstration
uses local layer IDs and source-module indices. Persisted prototypes must instead
use canonical `Partial` artifacts, reflected immutable identities and an actual
sealed source Package; indices are not artifact provenance.

## Evidence and remaining boundaries

The linker and workshop modules passed scoped Lean checks and their named axiom
gates. The actual consumer admitted 91-definition completed and 92-definition
extended Books. Six dynamic whole-Card cases passed source execution, with source
step counts 38, 55 and 39 for revisions 0, 1 and 2 in each composition.

At this source snapshot, general refinement and executable full-construction
modules are authored and awaiting their scoped checks. This is not optimized
C/JS compiler refinement, native Plan/Surface receiving, private execution
qualification or a complete member authoring UI. Public test source step counts
are evidence; private outer fees/releases require their public padded capacity
and disclosure policy.
