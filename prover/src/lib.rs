//! minidregg-prover — unverified native compute.
//!
//! This crate exposes arithmetic, transform, hash, Merkle, and buffer-management
//! kernels. Inputs are explicit low-level work data; outputs are buffers or local
//! execution errors.

pub mod additive_ntt;
pub mod binary_tower;
pub mod binary_tower_256;
pub mod field4;
pub mod field6;
pub mod fri;
pub mod gate_kernels;
#[cfg(feature = "wgpu-fold")]
pub mod gpu;
pub mod hash_kernels;
pub mod logup256_kernels;
pub mod mle_kernels;
