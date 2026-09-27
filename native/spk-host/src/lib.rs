//! Physical SPK execution primitives. Admission and RPC semantics belong to Mini
//! and `spk-rpc`; this crate only prepares a confined process and an inherited
//! Unix socketpair. The public binary deliberately has no app-launch command yet.

#[cfg(target_os = "linux")]
pub mod sandbox;
#[cfg(target_os = "linux")]
pub mod materialize;
#[cfg(target_os = "linux")]
pub mod hostd;
#[cfg(target_os = "linux")]
pub mod endpoint;
#[cfg(target_os = "linux")]
mod spawn_gate;
#[cfg(target_os = "linux")]
mod rpc_adapter;
#[cfg(target_os = "linux")]
mod http_response;
#[cfg(target_os = "linux")]
pub mod http_entrance;
#[cfg(target_os = "linux")]
mod native_dispatch;
#[cfg(target_os = "linux")]
mod dispatch_inspection;
#[cfg(target_os = "linux")]
mod dispatch_web_input;
#[cfg(target_os = "linux")]
mod dispatch_author;
#[cfg(target_os = "linux")]
mod dispatch_native;
#[cfg(target_os = "linux")]
mod dispatch_delivery;
