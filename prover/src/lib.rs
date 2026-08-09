//! minidregg-prover — UNVERIFIED COMPUTE downstream of the verified emit seam.
//!
//! Substrate, said out loud: this crate reads the `ConstraintDescriptor` that
//! `Compiler/Emit.lean` emits (whose faithfulness to the Lean AIR is the theorem
//! `emit_faithful`) and NEVER authors a constraint. There is no formal semantics of
//! Rust, so nothing in this crate is verification or refinement: the tests are
//! conformance vectors — cross-checks against facts the Lean side established
//! (`Compiler/EmitSerialize.lean`'s decided examples), kept honest by running, not
//! by proof. "The prover accepted" inherits the FRI/STARK floor (`[EMIT-sound]`).
//!
//! Rungs here: `[PROVER-serialize]` reader (descriptor.rs), `[PROVER-trace]`
//! (trace.rs), `[PROVER-commit]` (poseidon.rs + commit.rs — the Poseidon2-style
//! permutation mirroring `Compiler/AirHash.lean`'s `permExec`, and the Merkle
//! commitment over the trace in `Loom/Commitment`'s `OpeningScheme` shape),
//! `[PROVER-sumcheck]` (sumcheck.rs — the degree-≤1 sumcheck engine mirroring
//! `Loom/MultilinearExtension.lean`'s `mle`/`roundSum`), and
//! `[PROVER-sumcheck-gates]` (gate_claim.rs — the descriptor's gates encoded as
//! the hypercube defect table whose sumcheck `Assurance/AirSumcheck(Quadratic)`
//! proved sound, so the engine proves the ACTUAL gate system), and
//! `[PROVER-fri-fold]` (field4.rs + fri.rs — BabyBear⁴ (X⁴ = 11) and the CPU
//! reference of breadstuffs' FRI fold kernel, ADOPTED into this crate and
//! conformant to `Loom/Proximity.lean`'s verified `fold` on the Lean-authored
//! vector `testdata/fri_conformance.json`), and `[PROVER-fri-wgsl]` (the
//! optional `wgpu-fold` conformance experiment in gpu.rs +
//! shaders/fri_fold.wgsl; it is not part of the protocol core), and
//! `[PROVER-fri]` (fri_protocol.rs — the FRI LDT protocol around that fold:
//! commit → fold rounds → query spot-checks → final constant check, matching
//! `Loom/Proximity.lean`'s tower descent, `mem_reedSolomonCode_one_iff` base
//! check, and the `FriQueryVerifierAir` fold-consistency formula; challenges
//! caller-supplied), and `[PROVER-fs]` (transcript.rs — the Poseidon2 duplex
//! transcript drawing the sumcheck challenges, FRI betas, and query positions
//! non-interactively in `Loom/FiatShamir.lean`'s absorb-the-prefix /
//! squeeze-the-challenge shape, conformant to the Lean sponge chain on
//! `testdata/fs_conformance.json`; the verifier re-derives every challenge
//! from the proof's own commitment stream — soundness pricing, the `(t + k)`
//! grinding factor, stays Loom's: `fsKeystone_proved` /
//! `lightClientGrinding_sound`).
//!
//! `[PROVER-e2e-reference]` (`protocol.rs`) is the first ONE-call composition
//! of those rungs.  Its proof carries the full trace and its verifier recomputes
//! the trace-derived RS word, so it is an honest non-succinct, non-ZK reference
//! path — not a production prover.  The succinct opening bridge is named there
//! as `[PROVER-e2e-succinct-openings]`.

pub mod accumulator;
pub mod accumulator_generic;
pub mod additive_fri_reference;
pub mod additive_fri_sampled;
pub mod additive_mle_terminal;
pub mod additive_mle_tower256;
pub mod additive_ntt;
pub mod additive_pcs_ood;
pub mod binary_evaluation_claim;
pub mod binary_evaluation_history_append;
pub mod binary_functional_append;
pub mod binary_hash;
pub mod binary_history_append;
pub mod binary_merkle;
pub mod binary_tower;
pub mod binary_tower_256;
pub mod binary_transcript;
pub mod commit;
pub mod committed_accumulator;
pub mod descriptor;
pub mod field4;
pub mod field6;
pub mod fri;
pub mod fri_ext6_reference;
pub mod fri_protocol;
pub mod functional_nextgen_receipt;
pub mod gate_claim;
pub mod gate_mle_ext6;
pub mod gate_oracle_commitment;
pub mod gate_sumcheck_ext6;
#[cfg(feature = "wgpu-fold")]
pub mod gpu;
pub mod logup_tower256;
pub mod multiplicative_mle_terminal;
pub mod nextgen_light_client;
pub mod outer_factored_gate;
pub mod poseidon;
pub mod proof_carrying_history;
pub mod protocol;
pub mod semantic_receipt;
pub mod semantic_receipt_relation;
pub mod succinct_factored_gate;
pub mod sumcheck;
pub mod sumcheck_generic;
pub mod sumcheck_streaming;
pub mod trace;
pub mod trace_linear_ext6;
pub mod trace_linear_gf2;
pub mod transcript;
pub mod transcript_ext6;
pub mod wide;
