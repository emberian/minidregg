//! Resident-supervisor human dispatch. This function runs only in the process
//! that owns the actual app fd3 and its RpcDriver; a separate command must not
//! reopen fd3 or construct a new app-side WebSession from a historical reply.
#![allow(dead_code)] // Lifecycle-v2/SPK binding and resident service not enabled yet.

use crate::dispatch_author::FixedAuthoring;
use crate::dispatch_inspection::HttpProjection;
use crate::dispatch_native::{author_and_submit, PrivateOperator};
use crate::dispatch_web_input::{physical_open_input, physical_web_input};
use crate::hostd::Journal;
use crate::http_entrance::{CustodianPolicy, EntranceKind};
use crate::http_response;
use crate::rpc_adapter::RpcDriver;
use crate::web_socket::{cap_refusal, Limits, OpenSockets};
use std::os::unix::net::UnixStream;
use std::io;
use std::path::Path;
use std::time::Duration;

const MAX_APP_RESPONSE: usize = 8 * 1024 * 1024;
const APP_CALL_TIME: Duration = Duration::from_secs(30);

fn invalid(reason: &'static str) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidData, reason)
}

/// A single fresh human permit may reach fd3 once. Native op34 is committed
/// before physical delivery, so any failure thereafter retains the global
/// submit marker and/or DeliveryRequested tombstone for operator audit. The
/// caller must not retry this HTTP request after an uncertain result.
pub(crate) struct ResidentHuman<'a> {
    pub operator: &'a PrivateOperator,
    pub custody: &'a FixedAuthoring,
    pub journal: &'a Journal,
    pub rpc: &'a mut RpcDriver,
    pub display_name: &'a str,
    pub preferred_handle: &'a str,
    /// This generation's open WebSockets and its class caps.
    pub sockets: &'a OpenSockets,
    pub limits: Limits,
}

enum Physical {
    Exchange(crate::dispatch_web_input::PhysicalWebInput),
    Open(crate::dispatch_web_input::PhysicalOpenInput, crate::web_socket::Slot),
}

/// A WebSocket open the entrance validated: the client's stream (handed to
/// the fd3 worker on admission) and the handshake's accept value.
pub(crate) struct UpgradeRequest {
    pub client: UnixStream,
    pub accept: String,
}

impl ResidentHuman<'_> {
    pub(crate) fn deliver_once(
        &mut self,
        policy: &CustodianPolicy,
        http: &HttpProjection<'_>,
        attempt_parent: &Path,
        upgrade: Option<UpgradeRequest>,
    ) -> io::Result<Vec<u8>> {
        let kind = match http.route {
            crate::dispatch_inspection::Route::Browser => EntranceKind::Browser,
            crate::dispatch_inspection::Route::Api { .. } => EntranceKind::Api,
        };
        if policy.fixed_session_kind != kind
            || policy.fixed_app != self.custody.app
            || policy.fixed_subject != self.custody.subject
            || policy.fixed_session != self.custody.session
            || policy.fixed_ticket != self.custody.ticket_resource
        {
            return Err(invalid("HTTP entrance differs from fixed Mini custody"));
        }
        // The running claim/descriptor gate belongs to the resident supervisor;
        // this immediate check is the physical unit fence before a new Mini call.
        self.journal
            .read()?
            .ok_or_else(|| invalid("app journal absent"))?
            .verify_running_instance()?;
        // A WebSocket open takes its place in the grain's class cap before
        // any Mini write: the open past the cap is refused by name and
        // leaves no dispatch record.
        let slot = match &upgrade {
            Some(_) => match self.sockets.reserve(&self.limits) {
                Ok(slot) => Some(slot),
                Err(name) => {
                    eprintln!(
                        "spk-host: websocket open refused: {name} ({} open, class {} cap {})",
                        self.sockets.open(),
                        self.limits.class,
                        self.limits.max_open
                    );
                    return Ok(cap_refusal(name));
                }
            },
            None => None,
        };
        // The caller cannot choose or replay an operation ID. Even an
        // authoring refusal consumes this fsynced number across restarts.
        let operation_id = self.journal.allocate_dispatch_operation()?;
        let attempt_dir = attempt_parent.join(format!("dispatch-op-{operation_id}"));
        let committed = author_and_submit(
            self.operator,
            self.custody,
            http,
            &operation_id,
            &attempt_dir,
        )?;
        let base_path = format!("https://{}", policy.expected_host);
        // Projected before the durable DeliveryRequested, exactly as a GET.
        let physical = match (&upgrade, slot) {
            (None, _) => Physical::Exchange(physical_web_input(
                &committed.matched,
                http,
                self.display_name,
                self.preferred_handle,
                &base_path,
            )?),
            (Some(_), Some(slot)) => Physical::Open(
                physical_open_input(
                    &committed.matched,
                    http,
                    self.display_name,
                    self.preferred_handle,
                    &base_path,
                )?,
                slot,
            ),
            (Some(_), None) => return Err(invalid("WebSocket slot absent")),
        };
        let recorded = committed.record_delivery_requested(self.journal)?;
        if self
            .journal
            .read()?
            .ok_or_else(|| invalid("app journal absent"))?
            .verify_running_instance()
            .is_err()
        {
            let _ = recorded.finish(self.journal, false);
            return Err(invalid("app unit drift after durable DeliveryRequested"));
        }
        let physical = match (physical, upgrade) {
            (Physical::Exchange(physical), None) => physical,
            (Physical::Open(physical, slot), Some(upgrade)) => {
                // The worker calls `openWebSocket`, writes the 101 and owns
                // the client stream. The record finishes delivered once the
                // app accepted the open; frames and the close never return
                // here and write nothing to Mini.
                let opened = self.rpc.open_web_socket(
                    physical.binding,
                    physical.open,
                    upgrade.client,
                    upgrade.accept,
                    self.limits,
                    slot,
                    format!("op {operation_id}"),
                    APP_CALL_TIME,
                );
                return match opened {
                    Ok(()) => {
                        recorded.finish(self.journal, true)?;
                        Ok(Vec::new())
                    }
                    Err(error) => {
                        let _ = recorded.finish(self.journal, false);
                        Err(error)
                    }
                };
            }
            _ => {
                let _ = recorded.finish(self.journal, false);
                return Err(invalid("dispatch projection differs from the entrance request"));
            }
        };
        let head = http.method == "HEAD";
        let response = self.rpc.dispatch(
            physical.binding,
            physical.request,
            MAX_APP_RESPONSE,
            APP_CALL_TIME,
        );
        let origin = format!("https://{}", policy.expected_host);
        let serialized = response
            .and_then(|reply| http_response::serialize_for_origin(&reply, head, Some(&origin)));
        match serialized {
            Ok(bytes) => {
                recorded.finish(self.journal, true)?;
                Ok(bytes)
            }
            Err(error) => {
                let _ = recorded.finish(self.journal, false);
                Err(error)
            }
        }
    }
}
