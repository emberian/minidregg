//! minidregg-prover — UNVERIFIED COMPUTE downstream of the verified emit seam.
//!
//! Rust has no semantics in this project. This crate is being reduced to native
//! arithmetic, transform, hash, Merkle, and buffer-management kernels invoked by
//! Lean-owned generated control. Native code may return data; it may not choose a
//! statement, transcript schedule, security profile, or final acceptance bit.

pub mod additive_ntt;
pub mod binary_hash;
pub mod binary_merkle;
pub mod binary_tower;
pub mod binary_tower_256;
pub mod commit;
pub mod descriptor;
pub mod field4;
pub mod field6;
pub mod fri;
pub mod gate_kernels;
#[cfg(feature = "wgpu-fold")]
pub mod gpu;
pub mod logup256_kernels;
pub mod mle_kernels;
pub mod outer_factored_gate;
pub mod poseidon;
pub mod trace;
pub mod wide;
