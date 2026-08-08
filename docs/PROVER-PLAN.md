# The prover — our WGPU BabyBear⁴ backend, adopting breadstuffs' fold (not porting it)

ember steered (2026-08-08): **straight to the WGPU backend**, and **adopt breadstuffs' GPU work
into our own, don't raw-port**. This is the plan, grounded in a read of
`breadstuffs/circuit-prove/src/gpu_hidingfri_fold.rs` (388 lines) + `shaders/hidingfri_fold_ext4.wgsl`.

## Substrate, said out loud

The prover is **UNVERIFIED COMPUTE**. It is allowed to be Rust/WGSL because it **follows the
verified emit seam** — it consumes `ConstraintDescriptor` (whose faithfulness to the Lean AIR is
`Compiler/Emit.emit_faithful`, a theorem) and never authors a constraint. `[EMIT-sound]` stands:
"the prover accepted" inherits the FRI/STARK floor; it is not a verified statement. The value it
adds is *runnability + benchmarks*, not soundness — the soundness lives in the Lean formalization.

## What breadstuffs' fold actually is (so we adopt the right slice)

`gpu_hidingfri_fold.rs` is **narrow**: one operation, the FRI *matrix fold*
`fold_matrix(β, log_arity, matrix) → Vec<BabyBear⁴>`, plugged into Plonky3's
`TwoAdicFriFoldBackend`. The rest of the deployed prover (trace, commit, query, verify, the whole
PCS) is **upstream Plonky3 CPU**. The kernel:
- input: `values : &[BabyBear⁴]`, each element 4 canonical `u32` coefficients;
- twiddles: `halve_inv_powers` — `½·g⁻ⁱ` over the 2-adic subgroup, **bit-reversed** (the FRI
  fold's coset-shift factors), computed CPU-side;
- params: `[len, log_arity, β₀..β₃]`; output `len/arity` folded elements;
- dispatch: `output_len.div_ceil(256)` workgroups; CPU fallback = `CpuTwoAdicFriFold`.

**ADOPT** (take into our work): the WGSL fold math, the BabyBear⁴ = 4×u32 packing, the
bit-reversed twiddle layout, the buffer/dispatch/readback pattern. **DO NOT inherit**: the
Plonky3 `TwoAdicFriFoldBackend` trait, `p3-fri`/`p3-matrix` dependencies, the Plonky3 PCS around
it — those tie the fold to *their* protocol; ours is Loom-shaped.

## Our prover — the rungs (each testable; the FRI fold is the only GPU piece, like breadstuffs)

Crate `prover/` (new). Reads a serialized descriptor, emits a proof; a `--reference` CPU path
first (matches on any machine), then the WGSL fold for the hot loop.

1. **`[PROVER-serialize]`** — Lean side: serialize `ConstraintDescriptor` to a concrete format
   (a `ToJson`/byte writer in `Compiler/Emit`), + a Rust reader. The `[EMIT-backend]` wire-format,
   made concrete. Round-trip test: read-back = the Lean object.
2. **`[PROVER-trace]`** — descriptor + public inputs → the full wire vector (evaluate gates in
   dependency order, fill aux wires). Deterministic. Test: the trace satisfies `descriptorHolds`
   (the Rust re-check mirrors the Lean predicate — a cross-check, not a proof).
3. **`[PROVER-commit]`** — Merkle/hash commitment over the trace columns (Poseidon2, matching
   `AirHash`/`Loom/Commitment`). Test: openings verify.
4. **`[PROVER-sumcheck]`** — retire the gate constraints via sumcheck (matching `Loom/Sumcheck` +
   `Assurance/AirSumcheck(Quadratic)`: the same product-form claim the Lean proved sound). CPU.
5. **`[PROVER-fri]`** — the low-degree test (matching `Loom/Proximity`). The **matrix fold** is the
   WGSL kernel we adopt; commit/query/transcript are ours. BabyBear⁴ = our deployed field.
6. **`[PROVER-fs]`** — the Fiat-Shamir transcript (matching `Loom/FiatShamir` — sponge/Poseidon2),
   so the challenge schedule is the one the Lean grinding bound (`lightClientGrinding_sound`) prices.
7. **`[PROVER-e2e]`** — descriptor → proof → the light-client check (`Loom/LightClient`). The
   "it runs" milestone: a real proof over a real emitted note-spend descriptor. **Benchmarks need
   GPU hardware — flag ember when we reach the WGSL rung.**

## The honest seam to the formalization

Each rung *matches* a Lean-proved object (the commitment scheme, the sumcheck claim, the FRI LDT,
the FS schedule) — the prover computes what the Lean proved sound. It is a **conformance** target,
not a verified one: there is no formal semantics of Rust/WGSL, so "the prover matches Loom" is
tested by conformance vectors (the prover's transcript on a fixed descriptor equals a Lean-computed
reference), never called refinement or verification. `[PROVER-conformance]` — the vector harness —
is how we keep the compute honest to the proofs without overclaiming.
