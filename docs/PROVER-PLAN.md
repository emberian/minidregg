# Native compute and proof construction plan

Status: 2026-08-09. [`PROJECT.md`](../PROJECT.md) is the design constitution and
[`GOAL.md`](../GOAL.md) is the evidence ledger. This file tracks only the boundary between
Lean-owned proof control and unverified native computation.

## Authority rule

Rust has no semantics in this project. There is therefore no Rust “implementation” of a Lean
semantics and no refinement theorem to seek. Lean owns:

- the typed request, authorization, effects, state transition, disclosure, and receipt relation;
- manifest and codec identifiers;
- proof statements and native-clause registry;
- phase and transcript order, challenges, and query schedule;
- all descriptor/root/result comparisons; and
- the only constructors for verified turns, releases, clauses, and history heads.

Native code receives a generated plan plus bounded buffers and returns candidate data or an
engineering error. `Compiler.NativeKernelPlan.arbitraryRunner_integrity` and
`Compiler.SemanticController.arbitraryOracle_integrity` are the present theorem shape: successful
Lean control implies the Lean relations for every possible native response, without an honesty,
determinism, or conformance premise.

## Surviving native surface

The `prover/` crate has been reduced to:

| Module | Allowed role |
|---|---|
| `field4`, `field6` | finite-field arithmetic on caller-selected canonical buffers |
| `binary_tower`, `binary_tower_256` | Fan--Paar tower arithmetic |
| `additive_ntt` | caller-parameterized additive transform arithmetic |
| `fri` | one multiplicative fold kernel with caller-supplied schedule |
| `mle_kernels` | Möbius, MLE, reversed-LCH, coefficient/word folds, linear dot |
| `gate_kernels` | emitted-op residual arithmetic and caller-driven affine/quadratic folds |
| `logup256_kernels` | incidence, equality weights, fraction trees, round messages, interpolation |
| `hash_kernels` | caller-parameterized cSHAKE framing, tree construction, path/root recomputation |
| `trace` | candidate wire generation only |
| `descriptor` | temporary data-only JSON transport DTO |
| `gpu` / `fri_fold_bench` | optional downstream fold experiment |

There is no surviving native proof object, prover/verifier API, transcript state machine, suite
selector, statement validator, descriptor-acceptance predicate, or final verification Boolean.
Hash customization strings, domains, frame tags, root widths, and expected-root equality belong to
the generated Lean artifact and controller.

## Deleted authority islands

The following handwritten native families were deliberately deleted after their arithmetic was
extracted where useful:

- one-call reference prover/verifier and benchmark;
- semantic turn/receipt/history/lookup adapters;
- committed and generic accumulator verifiers;
- sampled additive FRI, OOD, evaluation, and binary-history admission;
- Ext6 gate, sumcheck, trace-functional, and MLE-terminal proof protocols;
- Tower256 LogUp statement/transcript/proof/verifier;
- binary and Ext6 transcript implementations;
- legacy Poseidon/wide-digest commitment verifier; and
- Rust-side descriptor satisfaction and Merkle equality verdicts.

The sampled additive branch was not removed merely for architectural cleanliness: its verifier
never enforced the advertised coefficient bound, so it was not an LDT and allowed a false OOD
claim through a pointwise quotient. It stays absent until Lean-generated rate-aware control is
joined to the proved additive theorem.

## Lean-owned control spine

The active spine is:

1. `Theory.IndexedProgram`, `TypedAuthorization`, `AuthorizationDeclaration`,
   `EffectDeclaration`, `CellState`, `ReactiveController`, `DisclosureDeclaration`, and
   `PrivateComputationDeclaration` declare the semantic machine.
2. `Compiler.SemanticManifest` pins content-addressed codecs, carrier profiles, named bridges,
   native clauses, dimensions, and bounds.
3. `Compiler.SemanticArtifactBundle` emits first-order declaration and phase data.
4. `Compiler.BignumKernelABI` and `NativeKernelPlan` schedule bounded computation whose result is
   checked only by Lean relations.
5. `Compiler.SemanticController` constructs the current verified frame-nucleus token against an
   arbitrary oracle. Its scope must be extended to manifest-closed native clauses and the full
   typed receipt header.

## Ordered proof-system joins

1. **Generated codec and dispatch.** Materialize a concrete artifact bundle and generate the
   native DTO/dispatcher from it. The temporary handwritten descriptor DTO then disappears.
2. **Rate-aware additive controller.** Instantiate `AdditiveFriQuery` with generated roots-before-
   challenge order, caller-independent rate data, parameterized cSHAKE/Merkle kernels, and exact
   root comparisons in Lean.
3. **Gate commitment/LDT.** Extend the proved seven-operand/eta algebra with generated commitment,
   transcript, subfield, proximity, and final-LDT control. No native gate verifier is revived.
4. **Lookup clause.** Emit the `LogupIndexLink` relation and drive only the extracted Tower256
   arithmetic kernels; then extend indexed lookup to the chosen mutable RAM relation.
5. **Outer history PCS.** `SemanticHistoryAccumulator` already gives the proof-relevant typed
   append, folded `AccClaim`, and exact full-opening decider/extraction theorem. Instantiate the
   WARP/FACS-shaped transcript, recommitment PCS, sampled decider, and extractor without retaining
   the entry list. A hash chain is not an accumulator, and the current exact theorem is not yet a
   succinct protocol.
6. **Privacy and FHE.** Join hiding/ZK adapters and the exact BFV signed-limb/carry equations under
   the same request, representation, disclosure, and receipt identity.
7. **Final compression and benchmarks.** Only after one real history path exists, select the final
   light-client compressor and measure the protocol at its exact proved rate and security regime.

## Performance discipline

Optimization begins from the selected proof path. Native kernels may be SIMD/GPU/distributed and
may have diagnostic vector tests, but benchmark or verification matrices are not completion gates
for semantic work. The opt-in WGPU fold is disposable. Historical measurements are archived in
[`PERFORMANCE.md`](PERFORMANCE.md) and are not current runnable-protocol claims.
