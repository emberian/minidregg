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

## Concrete receiver and edition retention

The composition consumer `BendObliviousExecutionIndexed.prepare` now consumes
this producer through the existing `ofCompiled` constructor and reconstructs
the actual full controller from that certified library. Its independent check
passed on the same public repeated-depth-5 source and H64/F16/A8/wordBits8
capacity profile: ROM rows 63→6, Boolean gates 517,424→416,205 and AND gates
212,149→161,020 (24.1% fewer). AND depth remains 43. This is actual component
receiving evidence; it does not establish malicious MPC or native Host latency.

`BendIndexedExecutionContext` uses the existing exact-table/bounds canonical
context codec, prefixing the explicit compiler edition in the native binding.
General laws prove exact context equality from equal encoded bytes, legacy
context inequality even when tables happen to match, historical checkpoint
refusal under the new expected context, and exact serialized pause/resume.
Old checkpoints remain intact for their explicit historical receiver; there is
no pointer relocation into a different ROM. Controller `ofCompiled` separately
retains equality to the actual reconstructed network. Its network/edition and
public capacities must remain in the backend's admitted exact circuit binding.

`BendIndexedActivityProgram` supplies a new explicitly versioned Source record:
original public Source plus compilerEdition. The canonical signed-source binding
is injective over BOTH fields. Preparation refuses unsupported editions and
performs original core/entry/invocation/capacity admission, while consuming the
already-proved checker result through compileChecked. The produced certificate
is the original activity Prepared type plus the explicit edition witness.
Its expected continuation bytes include that signed-source binding, the compiler
frame, exact tables and exact limits. It supplies no current authority/funding
or native action registration. Baseline Source/prepare remain supported.

The unchanged baseline BendActivityProgram producer was first-qualified
independently of the larger queued native receiver foundation; its source hash
is `d224fa9c32cbcb39bf6eea0563f0a6ba8600584be7315087955097604e6ea770`.
The indexed producer and context general axiom gates passed. An actual admitted
typed pair program executes through BOTH clear closure machines: ROM rows 64→7,
identical exact decoded source result, and unchanged canonical sourceSteps=1.
The matching indexed checkpoint restores exact state; an old compiler context
and changed generation both refuse. This is a focused execution/refusal/resume
join, not native lifecycle deployment.

Current canonical persisted workshop Books were checked independently and
produce the same measured row counts above. Their bytes have source hashes
`b534270021c36e7ec0fdd5647bdc1c145eadeaf859c39e70cbd8024213b6a6b2`
(complete) and
`71f5a97c9cd28fe0b812014d062c35673c53593269bb3d44def2d313ee781209`
(alternate). Each actual Book passed Book.check and full ordered-definition/
entry translation validation. These canonical byte identities are separate
from the earlier captured formatting/source hashes.

Native activation of the new signed profile is an explicit receiving task;
there is no automatic reinterpretation of an existing source/profile or a
fallback from indexed refusal to baseline execution. Baseline receiver defaults
remain unchanged. General compiler completeness and general closure-machine
simulation keep their existing, separately owned obligations.
