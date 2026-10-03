# Bend representation efficiency

Two implementation improvements preserve the pinned BendTT source meaning.
They apply to ordinary clear execution/publication. Private execution continues
to use its fixed-access controller and separately declared capacity profile.

`Theory.BendBookIndex` prepares an exact first-definition HashMap once per
invocation. `lib_exact` proves every lookup equals ordered `Book.get`, including
missing names and duplicate declarations, without assuming an honest generator
or successful checker. `BendLiveMachine.executeChecked` shares this lookup
through every classifier and source transition. Existing direct classifier APIs
and `executeReference` retain ordered-list lookup. The general
`executeChecked_eq_reference` theorem equates the whole dependent Execution:
result or refused residual, exact prefix trace, count, reason, and value proof.
Classification ticks, source-step bounds, and refusal ordering remain unchanged.
Preparing the map consumes physical work; it adds no source transition and is
not silently converted into a public fee or private-branch resource disclosure.

`Compiler.BendClosureCompileIndexed` caches exact name/enumeration interning and
shares identical immutable Code instructions. `codeKey_injective` proves its
constructor-tag/quantity/all-fields key is injective. Hash collisions use full
key equality. Every source constructor survives, including arbitrary Q0 syntax,
rewrite motives and live rewrite evidence. Definition order is retained and the
runtime first-definition behavior remains unchanged. Exact source subterms can
share code while their closures retain separate environments.

The optimized compiler returns the existing `BendClosureCompile.Compiled`
certificate, using the existing actual `validateDefinitions` and `validateCode`
passes. Those checks construct complete `SourceCorrespondence` and `CodeDenotes`
proofs; compilation fails closed if a produced representation differs.
`compileChecked` consumes a real previously admitted `Book.check` theorem to
avoid repeating whole-Book checking. Standalone `compile` still runs Book.check.
There is no general compiler-completeness claim: success is source-certified,
and failed translation validation remains refusal.

The lowered compiler edition is `bendtt-indexed-code-v1`. Source Book and entry
identity remain unchanged. Compiled tables and controller-network bytes change;
retain their exact edition/digest and reconstruct the controller using the
actual new Compiled library. Existing certificates or old network hashes cannot
be reused for different arrays. Source cost and physical/public-ROM size are
distinct. Smaller tables can improve circuit costs within a declared profile;
they do not silently shrink heap/frame capacities or invent privacy guarantees.

## Qualification on October 3, 2026

Scoped Lean 4.30 checks passed with standard-three axiom gates for the lookup
law, full execution equality, injective code key and optimized producer. Tests
cover every source constructor/quantity, absent and duplicate names, zero and
insufficient classifier/source fuel, underapplication, rewrite evidence, exact
ordered-definition decoding, and actual standalone checked compilation.

The `--run` source-evaluator benchmark forces completion before taking the end
timestamp. These timings describe the Lean conformance evaluator, not native
Host deployment latency. Map preparation is included:

| Call-chain definitions | Ordered-list ms | Prepared-index ms |
|---:|---:|---:|
| 1,000 | 49 | 4 |
| 5,000 | 1,176 | 16 |
| 10,000 | 4,735 | 32 |

Actual captured frontend Books passed parser, Book.check and exact optimized
translation validation:

| Captured Book | Definitions | Original code rows | Shared code rows |
|---|---:|---:|---:|
| Complete workshop | 91 | 5,317 | 1,221 |
| Alternate workshop | 92 | 5,320 | 1,223 |
| SourceBool.choose | 3 | 25 | 20 |

Complete workshop source SHA256:
`9ac12cea3c8ac5928d292283d867ed5f54701d6cfe538aee02469af06475a163`.
Alternate workshop source SHA256:
`472ac8dfa9de86c654ade308e729ebfbf3e05cf376fb9e4a762c4470c5d49b74`.
Choose source SHA256:
`588ba33aa6891afd271d1b3bed11e561e2bdf849021983a2ae3c7d3a9bc0d5cd`.

A repeated exact immutable subtree at depth 16 used 131,071 original code rows
versus 17 shared rows. The actual source build took 22,232 ms; indexed build plus
full exact decoding took 266 ms. This isolates representation duplication; it
is not a claim that arbitrary programs enjoy the same factor.

The two Lean benchmark files are under `tests/bend-representation-efficiency`.
Use qualified warm dependencies and the project's bounded compiler controls.
The compiler benchmark accepts additional captured `.bendtt` paths as arguments.
Native Host integration and full optimized controller execution remain separate
receiving qualifications, owned by their corresponding runtime consumers.
