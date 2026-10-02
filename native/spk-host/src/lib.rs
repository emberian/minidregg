//! Physical SPK execution primitives. Admission and RPC semantics belong to Mini
//! and `spk-rpc`; this crate only prepares a confined process and an inherited
//! Unix socketpair. The public resident command requires a fresh source-bound
//! lifecycle claim before launching the app.

#[cfg(target_os = "linux")]
mod agent_api_custody;
#[cfg(target_os = "linux")]
mod agent_api_lifetime_v3;
#[cfg(target_os = "linux")]
mod agent_api_lifetime_reverse_v3;
#[cfg(target_os = "linux")]
mod agent_api_lifetime_custody_v3;
#[cfg(target_os = "linux")]
mod agent_api_lifetime_paid_native_v3;
#[cfg(target_os = "linux")]
mod agent_api_lifetime_dispatch_native_v3;
#[cfg(target_os = "linux")]
mod agent_api_lifetime_server_v3;
#[cfg(target_os = "linux")]
mod agent_api_lifetime_wire_v3;
#[cfg(target_os = "linux")]
mod agent_api_native;
#[cfg(target_os = "linux")]
mod agent_api_server;
#[cfg(target_os = "linux")]
mod agent_api_wire;
#[cfg(target_os = "linux")]
pub mod broker;
#[cfg(target_os = "linux")]
mod claim_descriptor;
#[cfg(target_os = "linux")]
mod claim_native;
#[cfg(target_os = "linux")]
mod completion_native;
#[cfg(target_os = "linux")]
mod descriptor_native;
#[cfg(target_os = "linux")]
mod dispatch_author;
#[cfg(target_os = "linux")]
mod dispatch_delivery;
#[cfg(target_os = "linux")]
mod dispatch_inspection;
#[cfg(target_os = "linux")]
pub mod dispatch_native;
#[cfg(target_os = "linux")]
mod dispatch_web_input;
#[cfg(target_os = "linux")]
pub mod endpoint;
#[cfg(target_os = "linux")]
pub mod hostd;
#[cfg(target_os = "linux")]
pub mod http_entrance;
#[cfg(target_os = "linux")]
mod http_response;
#[cfg(target_os = "linux")]
pub mod install_service;
#[cfg(target_os = "linux")]
pub mod launch_descriptor_native;
#[cfg(target_os = "linux")]
mod lifecycle_selector;
#[cfg(target_os = "linux")]
pub mod grain;
#[cfg(target_os = "linux")]
mod grain_export;
#[cfg(target_os = "linux")]
mod grain_route;
#[cfg(target_os = "linux")]
mod lifecycle_v3_claim_native;
#[cfg(target_os = "linux")]
mod lifecycle_v3_completion_native;
#[cfg(target_os = "linux")]
mod lifecycle_v3_native;
#[cfg(target_os = "linux")]
mod lifecycle_v3_report_native;
#[cfg(target_os = "linux")]
mod lifecycle_v3_stop_native;
#[cfg(target_os = "linux")]
mod lifecycle_v3_stop_claim_native;
#[cfg(target_os = "linux")]
mod lifecycle_v3_stop_begin_native;
#[cfg(target_os = "linux")]
mod lifecycle_v3_stop_assembly_native;
#[cfg(target_os = "linux")]
pub mod lifecycle_v3_stop_service;
#[cfg(target_os = "linux")]
pub mod materialize;
#[cfg(target_os = "linux")]
mod native_dispatch;
#[cfg(target_os = "linux")]
mod resident_begin_native;
#[cfg(target_os = "linux")]
mod resident_launch;
#[cfg(target_os = "linux")]
pub mod resident_service;
#[cfg(target_os = "linux")]
mod rpc_adapter;
#[cfg(target_os = "linux")]
pub mod sandbox;
#[cfg(target_os = "linux")]
pub mod seccomp;
#[cfg(target_os = "linux")]
mod setid_bound;
#[cfg(target_os = "linux")]
mod spawn_gate;
#[cfg(target_os = "linux")]
mod volume_custody;
#[cfg(target_os = "linux")]
mod web_socket;
#[cfg(target_os = "linux")]
mod stream_continuity;
