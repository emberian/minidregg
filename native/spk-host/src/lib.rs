//! Physical SPK execution primitives. Admission and RPC semantics belong to Mini
//! and `spk-rpc`; this crate only prepares a confined process and an inherited
//! Unix socketpair. The public binary deliberately has no app-launch command yet.

#[cfg(target_os = "linux")]
pub mod sandbox;
#[cfg(target_os = "linux")]
pub mod materialize;
