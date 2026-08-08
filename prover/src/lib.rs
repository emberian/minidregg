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
//! proved sound, so the engine proves the ACTUAL gate system). The FRI/FS
//! rungs and the adopted WGSL fold come later, per docs/PROVER-PLAN.md.

pub mod commit;
pub mod descriptor;
pub mod gate_claim;
pub mod poseidon;
pub mod sumcheck;
pub mod trace;
