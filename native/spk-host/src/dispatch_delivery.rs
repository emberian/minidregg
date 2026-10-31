//! Resident-supervisor human dispatch. This function runs only in the process
//! that owns the actual app fd3 and its RpcDriver; a separate command must not
//! reopen fd3 or construct a new app-side WebSession from a historical reply.

use crate::dispatch_author::FixedAuthoring;
use crate::dispatch_inspection::HttpProjection;
use crate::dispatch_native::{author_and_submit, renew_stream, ContinuityCustody, PrivateOperator};
use crate::dispatch_web_input::{physical_open_input, physical_web_input};
use crate::hostd::Journal;
use crate::http_entrance::{CustodianPolicy, EntranceKind};
use crate::http_response;
use crate::rpc_adapter::RpcDriver;
use crate::stream_continuity::{ContinuityBinding, ContinuityTip};
use crate::web_socket::{cap_refusal, Limits, OpenSockets, StreamLease};
use std::io;
use std::os::unix::net::UnixStream;
use std::path::Path;
use std::sync::atomic::AtomicBool;
use std::sync::Arc;
use std::time::Duration;

const MAX_APP_RESPONSE: usize = 8 * 1024 * 1024;
const APP_CALL_TIME: Duration = Duration::from_secs(30);

fn invalid(reason: &'static str) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidData, reason)
}

/// A single fresh human permit may reach fd3 once. Native op34 is committed
/// before physical delivery, so any failure thereafter retains this call's
/// submit marker and/or DeliveryRequested tombstone for operator audit. This
/// call is never resent; a new HTTP request is a new signed call.
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
    pub stream_lease_lifetime: Duration,
    pub continuity_namespace: &'a (String, String),
    /// Hot enrollment fixes the exact source identity for this transport route.
    /// Initial START routes retain their historical per-request admission path.
    pub route_binding: Option<&'a ContinuityBinding>,
}

enum Physical {
    Exchange(crate::dispatch_web_input::PhysicalWebInput),
    Open(
        crate::dispatch_web_input::PhysicalOpenInput,
        crate::web_socket::Slot,
    ),
}

/// A WebSocket open the entrance validated: the client's stream (handed to
/// the fd3 worker on admission) and the handshake's accept value.
/// Per-hop wall clock of one delivery, printed once when the delivery ends (answer or refusal):
/// `spk-host: dispatch-timing METHOD hops=name:ms,...`. Latency is published, never a gate; the
/// line is what names the hop a slow request spent its time in.
struct HopTrace {
    method: String,
    last: std::time::Instant,
    hops: Vec<(&'static str, u128)>,
}
impl HopTrace {
    fn new(method: &str) -> Self {
        Self { method: method.to_owned(), last: std::time::Instant::now(), hops: Vec::new() }
    }
    fn mark(&mut self, name: &'static str) {
        let now = std::time::Instant::now();
        self.hops.push((name, now.duration_since(self.last).as_millis()));
        self.last = now;
    }
}
impl Drop for HopTrace {
    fn drop(&mut self) {
        let hops: Vec<String> = self.hops.iter().map(|(name, ms)| format!("{name}:{ms}")).collect();
        eprintln!("spk-host: dispatch-timing {} hops={}", self.method, hops.join(","));
    }
}

pub(crate) struct UpgradeRequest {
    pub client: UnixStream,
    pub accept: String,
}

impl ResidentHuman<'_> {
    /// `export_capture` is the entrance's capture intent, carried beside the
    /// request rather than in its Mini-signed header list: the kernel admits
    /// only ordinary app headers, and capture is host/TLS custody of the
    /// response, never an app-visible input.
    pub(crate) fn deliver_once(
        &mut self,
        policy: &CustodianPolicy,
        http: &HttpProjection<'_>,
        export_capture: Option<&str>,
        attempt_parent: &Path,
        upgrade: Option<UpgradeRequest>,
    ) -> io::Result<Vec<u8>> {
        let mut trace = HopTrace::new(http.method);
        let export_capture = crate::export_receipt::requested(policy, http, export_capture)?;
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
        let base_path = format!("https://{}", policy.expected_host);
        // Everything the WebSession projection takes from the request itself
        // is checked here, before an operation number, Store record or
        // submit marker can exist. A refusal leaves no evidence.
        crate::dispatch_web_input::preflight_web_input(
            http,
            self.display_name,
            self.preferred_handle,
            &base_path,
            upgrade.is_some(),
        )?;
        trace.mark("preflight");
        // The running claim/descriptor gate belongs to the resident supervisor;
        // this immediate check is the physical unit fence before a new Mini call.
        self.journal
            .read()?
            .ok_or_else(|| invalid("app journal absent"))?
            .verify_running_instance()?;
        // The physical fd3 slot is one per generation: while hostd holds a
        // DeliveryRequested operation no other command may reach the app.
        match std::fs::symlink_metadata(attempt_parent.join("dispatch-active.json")) {
            Ok(_) => {
                return Err(io::Error::new(
                    io::ErrorKind::Interrupted,
                    "SPK physical delivery uncertain; exact recovery required",
                ))
            }
            Err(error) if error.kind() == io::ErrorKind::NotFound => {}
            Err(error) => return Err(error),
        }
        // The native fence is per signed call (dispatch_fence): an undecided
        // earlier call is looked up, never resent, and fences nobody else
        // until the journal's bound of undecided calls is reached.
        trace.mark("journal-fence");
        crate::dispatch_fence::admit_new_call(self.operator, attempt_parent)?;
        trace.mark("admit-new-call");
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
        // authoring refusal consumes this number across restarts.
        let operation_id = self.journal.allocate_dispatch_operation()?;
        trace.mark("allocate-operation");
        let attempt_dir = attempt_parent.join(format!("dispatch-op-{operation_id}"));
        // Anchor BEFORE native authoring/admission; late success never renews it.
        let lease = upgrade
            .as_ref()
            .map(|_| StreamLease::begin(self.stream_lease_lifetime))
            .transpose()?;
        let committed = author_and_submit(
            self.operator,
            self.custody,
            http,
            &operation_id,
            &attempt_dir,
            self.route_binding,
            self.continuity_namespace,
        )
        .inspect_err(|error| {
            // A failed current-authority check (including unavailable authority)
            // ends streams for this exact pinned custody, never another principal.
            // A lost tip race says nothing about authority and ends nothing.
            if crate::dispatch_fence::DispatchOutcome::of(error)
                .is_some_and(|outcome| outcome.status == crate::dispatch_fence::Status::Contention)
            {
                return;
            }
            self.rpc.invalidate_custody(
                &self.custody.app,
                &self.custody.subject,
                &self.custody.session,
                &self.custody.ticket_resource,
                self.route_binding,
            );
        })?;
        // From DeliveryRequested on, the journal holds this exact operation.
        // Every later outcome either finishes it Delivered, releases the
        // shared slot with a worker fence (the operation stays terminally
        // Uncertain), or, without a fence, keeps every marker for audit.
        trace.mark("author-and-submit");
        let recorded = committed.record_delivery_requested(self.journal)?;
        trace.mark("record-delivery");
        let uncertain = |error: io::Error| io::Error::new(io::ErrorKind::Interrupted, error);
        let prequeue = match self.rpc.prepare_cancellable(recorded.identity.clone()) {
            Ok(prequeue) => prequeue,
            Err(error) => {
                let _ = recorded.finish(self.journal, false);
                return Err(uncertain(error));
            }
        };
        let m = &recorded.matched;
        let current_binding = ContinuityBinding {
            domain: self.continuity_namespace.0.clone(),
            semantics: self.continuity_namespace.1.clone(),
            app: m.app.to_string(),
            app_generation: m.app_generation.to_string(),
            session: m.session_resource.clone(),
            session_generation: m.session_generation.clone(),
            subject: m.subject.clone(),
            ticket_resource: self.custody.ticket_resource.clone(),
            session_fingerprint: m.session_fingerprint,
        };
        let route_matches = route_binding_matches(self.route_binding, &current_binding);
        let continuity = lease.as_ref().map(|_| {
            (
                current_binding,
                ContinuityTip {
                    height: m.accepted_count.clone(),
                    chain: None,
                    world_root: m.after_world_root.clone(),
                },
            )
        });
        // Any refusal from here until the worker queue is a proven
        // never-enqueued command: release with the prequeue fence.
        let projected = (|| {
            if !route_matches {
                // Mini committed a valid current dispatch, but this immutable
                // route belongs to a different enrollment.
                return Err(invalid("dispatch differs from immutable route admission"));
            }
            self.journal
                .read()?
                .ok_or_else(|| invalid("app journal absent"))?
                .verify_running_instance()?;
            let physical = match (&upgrade, slot) {
                (None, _) => Physical::Exchange(physical_web_input(
                    m,
                    http,
                    self.display_name,
                    self.preferred_handle,
                    &base_path,
                )?),
                (Some(_), Some(slot)) => Physical::Open(
                    physical_open_input(
                        m,
                        http,
                        self.display_name,
                        self.preferred_handle,
                        &base_path,
                    )?,
                    slot,
                ),
                (Some(_), None) => return Err(invalid("WebSocket slot absent")),
            };
            Ok(match physical {
                Physical::Exchange(mut input) => {
                    input.binding.ticket_resource = Some(self.custody.ticket_resource.clone());
                    Physical::Exchange(input)
                }
                Physical::Open(mut input, slot) => {
                    input.binding.ticket_resource = Some(self.custody.ticket_resource.clone());
                    Physical::Open(input, slot)
                }
            })
        })();
        trace.mark("prepare-and-project");
        let physical = match projected {
            Ok(physical) => physical,
            Err(error) => {
                let fence = prequeue.abort_no_enqueue();
                let _ = recorded.release_uncertain(self.journal, fence);
                return Err(error);
            }
        };
        match (physical, upgrade) {
            (Physical::Exchange(physical), None) => {
                let head = http.method == "HEAD";
                #[cfg(feature = "integration-qualification")]
                crate::dispatch_native::qualification::delivery_event(&attempt_dir, None)?;
                let response = prequeue.dispatch(
                    physical.binding,
                    physical.request,
                    MAX_APP_RESPONSE,
                    APP_CALL_TIME,
                    Arc::new(AtomicBool::new(false)),
                );
                trace.mark("app-call");
                #[cfg(feature = "integration-qualification")]
                crate::dispatch_native::qualification::delivery_event(
                    &attempt_dir,
                    Some(response.is_ok()),
                )?;
                let (reply, fence) = match response {
                    Ok(delivered) => delivered,
                    Err(failure) => {
                        let (error, fence) = failure.into_parts();
                        match fence {
                            Some(fence) => {
                                let _ = recorded.release_uncertain(self.journal, fence);
                            }
                            None => {
                                let _ = recorded.finish(self.journal, false);
                            }
                        }
                        return Err(uncertain(error));
                    }
                };
                let origin = format!("https://{}", policy.expected_host);
                let serialized = http_response::serialize_for_origin(&reply, head, Some(&origin))
                    .and_then(|bytes| match &export_capture {
                        Some(capture) => crate::export_receipt::prepare(
                            bytes,
                            capture,
                            self.custody,
                            &recorded.identity,
                            http,
                        ),
                        None => Ok(bytes),
                    });
                match serialized {
                    Ok(bytes) => {
                        recorded.finish(self.journal, true)?;
                        Ok(bytes)
                    }
                    Err(error) => {
                        // The worker completed the command, but no response
                        // can be certified: release the slot, keep the
                        // operation Uncertain and nonreplayable.
                        let _ = recorded.release_uncertain(self.journal, fence);
                        Err(uncertain(error))
                    }
                }
            }
            (Physical::Open(physical, slot), Some(upgrade)) => {
                // The worker calls `openWebSocket`, writes the 101 and owns
                // the client stream. The record finishes delivered once the
                // app accepted the open; frames and the close never return
                // here and write nothing to Mini.
                let bound = (|| {
                    let lease = lease.ok_or_else(|| invalid("WebSocket lease absent"))?;
                    let (binding, tip) =
                        continuity.ok_or_else(|| invalid("continuity binding absent"))?;
                    lease.bind_continuity(binding, tip)?;
                    Ok::<_, io::Error>(lease)
                })();
                let lease = match bound {
                    Ok(lease) => lease,
                    Err(error) => {
                        let fence = prequeue.abort_no_enqueue();
                        let _ = recorded.release_uncertain(self.journal, fence);
                        return Err(uncertain(error));
                    }
                };
                let renewal = Box::pin(renew_stream(
                    lease.clone(),
                    ContinuityCustody {
                        operator: self.operator.clone(),
                        custody: self.custody.clone(),
                        attempt_parent: attempt_parent.to_path_buf(),
                    },
                ));
                match prequeue.open_web_socket(
                    physical.binding,
                    physical.open,
                    upgrade.client,
                    upgrade.accept,
                    self.limits,
                    slot,
                    lease,
                    renewal,
                    format!("op {operation_id}"),
                    APP_CALL_TIME,
                ) {
                    Ok(()) => {
                        recorded.finish(self.journal, true)?;
                        Ok(Vec::new())
                    }
                    Err(failure) => {
                        let (error, fence) = failure.into_parts();
                        match fence {
                            Some(fence) => {
                                let _ = recorded.release_uncertain(self.journal, fence);
                            }
                            None => {
                                let _ = recorded.finish(self.journal, false);
                            }
                        }
                        Err(uncertain(error))
                    }
                }
            }
            (physical, _) => {
                drop(physical);
                // The projection above matched the entrance's upgrade state.
                Err(invalid("dispatch projection differs from the entrance request"))
            }
        }
    }
}

fn route_binding_matches(
    expected: Option<&ContinuityBinding>,
    current: &ContinuityBinding,
) -> bool {
    expected.is_none_or(|expected| expected == current)
}

#[cfg(test)]
mod route_binding_tests {
    use super::*;
    fn binding() -> ContinuityBinding {
        ContinuityBinding {
            domain: "1".into(),
            semantics: "2".into(),
            app: "17".into(),
            app_generation: "4".into(),
            session: "27".into(),
            session_generation: "2".into(),
            subject: "8".into(),
            ticket_resource: "37".into(),
            session_fingerprint: [3; 32],
        }
    }
    #[test]
    fn hot_route_never_inherits_regrant_or_changed_fingerprint() {
        let expected = binding();
        assert!(route_binding_matches(Some(&expected), &expected));
        let mut regrant = expected.clone();
        regrant.session_generation = "3".into();
        assert!(!route_binding_matches(Some(&expected), &regrant));
        regrant = expected.clone();
        regrant.session_fingerprint[0] ^= 1;
        assert!(!route_binding_matches(Some(&expected), &regrant));
        regrant = expected.clone();
        regrant.ticket_resource = "38".into();
        assert!(!route_binding_matches(Some(&expected), &regrant));
        regrant = expected.clone();
        regrant.app_generation = "5".into();
        assert!(!route_binding_matches(Some(&expected), &regrant));
        let mut unrelated = expected.clone();
        unrelated.session = "28".into();
        unrelated.subject = "9".into();
        assert!(route_binding_matches(Some(&unrelated), &unrelated));
        assert!(route_binding_matches(None, &regrant));
    }
}
