//! Physical fd3 Sandstorm RPC driver. This module carries no Mini authority.
//!
//! A future native adapter must recheck current app generation, session,
//! subject-derived identity and effective bits for every request. Pending
//! lifecycle receipts and caller HTTP headers cannot authorize calls here.
#![allow(dead_code)] // Staged until Mini exposes a checked current-session projection.

use crate::hostd::DispatchIdentity;
use minidregg_spk_rpc::web_session_capnp;
use crate::web_socket::{pump, switching_protocols, Limits, Slot};
use minidregg_spk_rpc::{
    dispatch_web, open_web_socket, SessionParameters, SupervisorConnection, ViewInfo,
    WebRequest, WebResponse, WebSocketOpen,
};
use std::io::Write as _;
use std::collections::HashMap;
use std::io;
use std::os::unix::net::UnixStream;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::mpsc as sync_mpsc;
use std::sync::Arc;
use std::time::{Duration, Instant};
use tokio::runtime::Builder;
use tokio::sync::mpsc;
use tokio::task::LocalSet;

const MAX_RESPONSE_BYTES: usize = 8 * 1024 * 1024;
const MAX_CALL_TIME: Duration = Duration::from_secs(30);
const MAX_CACHED_SESSIONS: usize = 32;
const CANCEL_ACK_GRACE: Duration = Duration::from_secs(2);

fn invalid(message: &'static str) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidInput, message)
}

fn remaining(deadline: Instant) -> io::Result<Duration> {
    let left = deadline.saturating_duration_since(Instant::now());
    if left.is_zero() {
        Err(io::Error::new(
            io::ErrorKind::TimedOut,
            "SPK RPC operation deadline",
        ))
    } else {
        Ok(left)
    }
}

async fn wait_cancelled(cancelled: &AtomicBool) {
    while !cancelled.load(Ordering::Acquire) {
        tokio::time::sleep(Duration::from_millis(10)).await;
    }
}

/// Protocol routing after native authorization, not a role decision.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(crate) enum SessionKind {
    Web,
    Api,
}

/// Supplied only by a future source-owned current-session projection. The
/// fingerprint covers the current checked ticket/permission state, not caller
/// HTTP headers. This driver is fixed to one app process generation.
#[derive(Clone, Debug)]
pub(crate) struct SessionBinding {
    pub app: u64,
    pub process_generation: u64,
    pub session_resource: u64,
    pub subject: u64,
    pub projection_fingerprint: [u8; 32],
    pub kind: SessionKind,
    pub params: SessionParameters,
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
struct SessionKey {
    app: u64,
    generation: u64,
    session: u64,
    subject: u64,
    kind: SessionKind,
}

impl SessionBinding {
    fn key(&self) -> SessionKey {
        SessionKey {
            app: self.app,
            generation: self.process_generation,
            session: self.session_resource,
            subject: self.subject,
            kind: self.kind,
        }
    }
}

fn same_params(a: &SessionParameters, b: &SessionParameters) -> bool {
    a.identity_id == b.identity_id
        && a.display_name == b.display_name
        && a.preferred_handle == b.preferred_handle
        && a.permissions == b.permissions
        && a.tab_id == b.tab_id
        && a.base_path == b.base_path
        && a.user_agent == b.user_agent
        && a.acceptable_languages == b.acceptable_languages
}

struct CachedSession {
    fingerprint: [u8; 32],
    params: SessionParameters,
    client: web_session_capnp::web_session::Client,
    last_use: u64,
}

fn same_projection(
    fingerprint: &[u8; 32],
    params: &SessionParameters,
    binding: &SessionBinding,
) -> bool {
    *fingerprint == binding.projection_fingerprint && same_params(params, &binding.params)
}

fn cache_matches(cached: &CachedSession, binding: &SessionBinding) -> bool {
    same_projection(&cached.fingerprint, &cached.params, binding)
}

fn oldest_by_use<K: Copy>(entries: impl Iterator<Item = (K, u64)>) -> Option<K> {
    entries
        .min_by_key(|(_, last_use)| *last_use)
        .map(|(key, _)| key)
}

/// The app-side WebSession for one admitted binding: the cached one under an
/// unchanged source projection, or a new one (evicting the least recent).
#[allow(clippy::too_many_arguments)]
async fn session_for(
    supervisor: &SupervisorConnection,
    sessions: &mut HashMap<SessionKey, CachedSession>,
    sessions_created: &mut u64,
    use_clock: &mut u64,
    binding: &SessionBinding,
    deadline: Instant,
    cancelled: &AtomicBool,
) -> io::Result<web_session_capnp::web_session::Client> {
    let key = binding.key();
    if sessions
        .get(&key)
        .is_some_and(|cached| !cache_matches(cached, binding))
    {
        sessions.remove(&key);
    }
    *use_clock = use_clock.checked_add(1).ok_or_else(|| {
        invalid("SPK session use counter exhausted")
    })?;
    let session = if let Some(cached) = sessions.get_mut(&key) {
        cached.last_use = *use_clock;
        cached.client.clone()
    } else {
        let left = remaining(deadline)?;
        let client = tokio::select! {
            biased;
            _ = wait_cancelled(cancelled) => Err(io::Error::new(
                io::ErrorKind::Interrupted,
                "SPK caller disconnected during session setup")),
            result = tokio::time::timeout(left, async {
                match binding.kind {
                    SessionKind::Web => {
                        supervisor.new_web_session(&binding.params).await
                    }
                    SessionKind::Api => {
                        supervisor.new_api_session(&binding.params).await
                    }
                }
            }) => result.map_err(|_| {
                io::Error::new(io::ErrorKind::TimedOut,
                    "SPK session timeout")
            })?.map_err(io::Error::other),
        }?;
        if sessions.len() >= MAX_CACHED_SESSIONS {
            let old = oldest_by_use(
                sessions
                    .iter()
                    .map(|(key, cached)| (*key, cached.last_use)),
            )
            .ok_or_else(|| invalid("SPK session cache drift"))?;
            sessions.remove(&old);
        }
        sessions.insert(
            key,
            CachedSession {
                fingerprint: binding.projection_fingerprint,
                params: binding.params.clone(),
                client: client.clone(),
                last_use: *use_clock,
            },
        );
        *sessions_created =
            sessions_created.checked_add(1).ok_or_else(|| {
                invalid("SPK session creation counter exhausted")
            })?;
        client
    };
    Ok(session)
}

enum Command {
    View {
        deadline: Instant,
        reply: sync_mpsc::SyncSender<io::Result<ViewInfo>>,
    },
    Dispatch {
        binding: Box<SessionBinding>,
        request: Box<WebRequest>,
        max_response_bytes: usize,
        deadline: Instant,
        cancelled: Arc<AtomicBool>,
        reply: sync_mpsc::SyncSender<io::Result<WebResponse>>,
    },
    Stats {
        reply: sync_mpsc::SyncSender<RpcStats>,
    },
    OpenWebSocket {
        binding: Box<SessionBinding>,
        open: Box<WebSocketOpen>,
        client: UnixStream,
        accept: String,
        limits: Limits,
        slot: Slot,
        label: String,
        deadline: Instant,
        reply: sync_mpsc::SyncSender<io::Result<()>>,
    },
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) struct RpcStats {
    pub sessions_created: u64,
    pub cached_sessions: usize,
}

/// Physical command fence, not proof the app did not perform the operation.
/// The private constructor binds one exact journal coordinate to either a
/// proven absence from the worker queue or an acknowledged worker command
/// completion. Failed commands evict their app-side session before the ACK;
/// successful commands may retain it for another separately admitted request.
pub(crate) struct DispatchFence {
    identity: DispatchIdentity,
    worker_released: bool,
}

impl DispatchFence {
    pub(crate) fn matches_and_consume(self, expected: &DispatchIdentity) -> bool {
        self.identity == *expected
    }

    pub(crate) fn worker_released(&self) -> bool {
        self.worker_released
    }

    #[cfg(test)]
    pub(crate) fn test_worker_released_for(identity: DispatchIdentity) -> Self {
        Self {
            identity,
            worker_released: true,
        }
    }

    #[cfg(test)]
    pub(crate) fn test_no_enqueue_for(identity: DispatchIdentity) -> Self {
        Self {
            identity,
            worker_released: false,
        }
    }
}

pub(crate) struct CancellableFailure {
    error: io::Error,
    fence: Option<Box<DispatchFence>>,
}

/// Exclusive prequeue custody for one physical operation. A failed host-side
/// marker write may consume this guard to prove no command was enqueued; once
/// `dispatch` consumes it, only the worker's release ACK can clear the shared
/// app slot. Dropping the guard produces no witness.
pub(crate) struct PrequeueGuard<'a> {
    driver: &'a mut RpcDriver,
    identity: DispatchIdentity,
}

impl PrequeueGuard<'_> {
    pub(crate) fn abort_no_enqueue(self) -> DispatchFence {
        DispatchFence {
            identity: self.identity,
            worker_released: false,
        }
    }

    pub(crate) fn dispatch(
        self,
        binding: SessionBinding,
        request: WebRequest,
        max_response_bytes: usize,
        timeout: Duration,
        cancelled: Arc<AtomicBool>,
    ) -> Result<(WebResponse, DispatchFence), CancellableFailure> {
        self.driver.dispatch_cancellable(
            binding,
            request,
            max_response_bytes,
            timeout,
            self.identity,
            cancelled,
        )
    }
}

impl CancellableFailure {
    fn no_enqueue(error: io::Error, identity: DispatchIdentity) -> Self {
        Self {
            error,
            fence: Some(Box::new(DispatchFence {
                identity,
                worker_released: false,
            })),
        }
    }

    fn released(error: io::Error, identity: DispatchIdentity) -> Self {
        Self {
            error,
            fence: Some(Box::new(DispatchFence {
                identity,
                worker_released: true,
            })),
        }
    }

    fn unreleased(error: io::Error) -> Self {
        Self { error, fence: None }
    }

    pub(crate) fn into_parts(self) -> (io::Error, Option<DispatchFence>) {
        (self.error, self.fence.map(|fence| *fence))
    }
}

/// One connected fd3 for one app generation. A dedicated LocalSet drives
/// Cap'n Proto callbacks throughout its lifetime, including between calls.
/// A call without a worker release ACK poisons the driver. A released failed
/// call remains one-shot uncertain in its journal but does not block unrelated
/// participants from this shared app process.
pub(crate) struct RpcDriver {
    app: u64,
    generation: u64,
    sender: mpsc::Sender<Command>,
    uncertain: bool,
}

impl RpcDriver {
    pub(crate) fn prepare_cancellable(
        &mut self,
        identity: DispatchIdentity,
    ) -> io::Result<PrequeueGuard<'_>> {
        if self.uncertain || identity.app != self.app || identity.app_generation != self.generation
        {
            return Err(invalid("SPK RPC prequeue identity or driver state refused"));
        }
        Ok(PrequeueGuard {
            driver: self,
            identity,
        })
    }

    pub(crate) fn from_connected_stream(
        app: u64,
        generation: u64,
        stream: UnixStream,
    ) -> io::Result<Self> {
        let (sender, mut receiver) = mpsc::channel::<Command>(8);
        let (ready_tx, ready_rx) = sync_mpsc::sync_channel(1);
        std::thread::Builder::new()
            .name("mini-spk-rpc".into())
            .spawn(move || {
                let setup = (|| -> io::Result<_> {
                    stream.set_nonblocking(true)?;
                    let runtime = Builder::new_current_thread().enable_all().build()?;
                    let (supervisor, rpc) = {
                        let _entered = runtime.enter();
                        let stream = tokio::net::UnixStream::from_std(stream)?;
                        SupervisorConnection::from_connected_stream(stream)
                    };
                    Ok((runtime, supervisor, rpc))
                })();
                let (runtime, supervisor, rpc) = match setup {
                    Ok(value) => value,
                    Err(error) => {
                        let _ = ready_tx.send(Err(error.to_string()));
                        return;
                    }
                };
                let local = LocalSet::new();
                let _ = ready_tx.send(Ok(()));
                local.block_on(&runtime, async move {
                    let mut sessions: HashMap<SessionKey, CachedSession> = HashMap::new();
                    let mut sessions_created = 0_u64;
                    let mut use_clock = 0_u64;
                    tokio::task::spawn_local(async move {
                        let _ = rpc.await;
                    });
                    while let Some(command) = receiver.recv().await {
                        match command {
                            Command::View { deadline, reply } => {
                                let result = async {
                                    let left = remaining(deadline)?;
                                    tokio::time::timeout(left, supervisor.get_view_info())
                                        .await
                                        .map_err(|_| {
                                            io::Error::new(
                                                io::ErrorKind::TimedOut,
                                                "SPK view-info timeout",
                                            )
                                        })?
                                        .map_err(io::Error::other)
                                }
                                .await;
                                let _ = reply.send(result);
                            }
                            Command::Dispatch {
                                binding,
                                request,
                                max_response_bytes,
                                deadline,
                                cancelled,
                                reply,
                            } => {
                                let key = binding.key();
                                let result = async {
                                    if cancelled.load(Ordering::Acquire) {
                                        return Err(io::Error::new(
                                            io::ErrorKind::Interrupted,
                                            "SPK caller disconnected before RPC",
                                        ));
                                    }
                                    let session = session_for(
                                        &supervisor,
                                        &mut sessions,
                                        &mut sessions_created,
                                        &mut use_clock,
                                        &binding,
                                        deadline,
                                        &cancelled,
                                    )
                                    .await?;
                                    if cancelled.load(Ordering::Acquire) {
                                        return Err(io::Error::new(
                                            io::ErrorKind::Interrupted,
                                            "SPK caller disconnected before fd3 request",
                                        ));
                                    }
                                    let left = remaining(deadline)?;
                                    tokio::select! {
                                        biased;
                                        _ = wait_cancelled(&cancelled) => Err(io::Error::new(io::ErrorKind::Interrupted,
                                            "SPK caller disconnected; effect uncertain")),
                                        result = tokio::time::timeout(
                                            left,
                                            dispatch_web(&session, &request, max_response_bytes, left),
                                        ) => result.map_err(|_| {
                                            io::Error::new(io::ErrorKind::TimedOut,
                                                "SPK dispatch timeout")
                                        })?.map_err(io::Error::other),
                                    }
                                }
                                .await;
                                if result.is_err() {
                                    // A failed request may already have reached the app.
                                    // Retain its one-shot journal tombstone at the caller.
                                    // Before acknowledging command release, evict only this
                                    // app-side session; unrelated participants may continue
                                    // after the caller's exact journal fence is released.
                                    sessions.remove(&key);
                                }
                                let _ = reply.send(result);
                            }
                            Command::OpenWebSocket {
                                binding,
                                open,
                                client,
                                accept,
                                limits,
                                slot,
                                label,
                                deadline,
                                reply,
                            } => {
                                let key = binding.key();
                                let not_cancelled = AtomicBool::new(false);
                                let result = async {
                                    let session = session_for(
                                        &supervisor,
                                        &mut sessions,
                                        &mut sessions_created,
                                        &mut use_clock,
                                        &binding,
                                        deadline,
                                        &not_cancelled,
                                    )
                                    .await?;
                                    let left = remaining(deadline)?;
                                    let opened = open_web_socket(&session, &open, left)
                                        .await
                                        .map_err(io::Error::other)?;
                                    // The 101 is written here, before any app byte
                                    // can reach the client, and only after the app
                                    // accepted the open.
                                    let head = switching_protocols(&accept, &opened.protocols);
                                    client.set_nonblocking(false)?;
                                    (&client).write_all(&head)?;
                                    Ok(opened)
                                }
                                .await;
                                match result {
                                    Ok(opened) => {
                                        tokio::task::spawn_local(pump(
                                            client, opened, limits, slot, label,
                                        ));
                                        let _ = reply.send(Ok(()));
                                    }
                                    Err(error) => {
                                        sessions.remove(&key);
                                        drop(slot);
                                        let _ = reply.send(Err(error));
                                    }
                                }
                            }
                            Command::Stats { reply } => {
                                let _ = reply.send(RpcStats {
                                    sessions_created,
                                    cached_sessions: sessions.len(),
                                });
                            }
                        }
                    }
                });
            })?;
        match ready_rx.recv_timeout(Duration::from_secs(2)) {
            Ok(Ok(())) => Ok(Self {
                app,
                generation,
                sender,
                uncertain: false,
            }),
            Ok(Err(error)) => Err(io::Error::other(error)),
            Err(_) => Err(io::Error::new(
                io::ErrorKind::TimedOut,
                "SPK RPC worker initialization timeout",
            )),
        }
    }

    fn receive<T>(
        &mut self,
        reply: sync_mpsc::Receiver<io::Result<T>>,
        deadline: Instant,
    ) -> io::Result<T> {
        let left = match remaining(deadline) {
            Ok(left) => left,
            Err(error) => {
                self.uncertain = true;
                return Err(error);
            }
        };
        match reply.recv_timeout(left) {
            Ok(result) => {
                if result.is_err() {
                    self.uncertain = true;
                }
                result
            }
            Err(sync_mpsc::RecvTimeoutError::Timeout) => {
                self.uncertain = true;
                Err(io::Error::new(
                    io::ErrorKind::TimedOut,
                    "SPK RPC result uncertain; no automatic resend",
                ))
            }
            Err(sync_mpsc::RecvTimeoutError::Disconnected) => {
                self.uncertain = true;
                Err(io::Error::new(
                    io::ErrorKind::BrokenPipe,
                    "SPK RPC worker exited",
                ))
            }
        }
    }

    fn check_bound(&self, timeout: Duration) -> io::Result<Instant> {
        if self.uncertain || timeout.is_zero() || timeout > MAX_CALL_TIME {
            return Err(invalid("SPK RPC uncertain or timeout exceeds bound"));
        }
        Ok(Instant::now() + timeout)
    }

    fn receive_cancellable(
        &mut self,
        reply: sync_mpsc::Receiver<io::Result<WebResponse>>,
        deadline: Instant,
        cancelled: &AtomicBool,
        identity: DispatchIdentity,
    ) -> Result<(WebResponse, DispatchFence), CancellableFailure> {
        let mut cancellation_deadline = None;
        loop {
            if cancelled.load(Ordering::Acquire) && cancellation_deadline.is_none() {
                cancellation_deadline = Some(Instant::now() + CANCEL_ACK_GRACE);
            }
            let wait_until = cancellation_deadline.unwrap_or(deadline);
            let left = wait_until.saturating_duration_since(Instant::now());
            if left.is_zero() {
                self.uncertain = true;
                let message = if cancellation_deadline.is_some() {
                    "SPK caller canceled without worker release ACK"
                } else {
                    "SPK RPC deadline without worker release ACK"
                };
                return Err(CancellableFailure::unreleased(io::Error::new(
                    io::ErrorKind::TimedOut,
                    message,
                )));
            }
            match reply.recv_timeout(left.min(Duration::from_millis(10))) {
                Ok(result) => {
                    if cancelled.load(Ordering::Acquire) {
                        return Err(CancellableFailure::released(
                            io::Error::new(
                                io::ErrorKind::Interrupted,
                                "SPK caller disconnected; app effect remains uncertain",
                            ),
                            identity,
                        ));
                    }
                    return result
                        .map(|response| {
                            (
                                response,
                                DispatchFence {
                                    identity: identity.clone(),
                                    worker_released: true,
                                },
                            )
                        })
                        .map_err(|error| CancellableFailure::released(error, identity));
                }
                Err(sync_mpsc::RecvTimeoutError::Timeout) => {}
                Err(sync_mpsc::RecvTimeoutError::Disconnected) => {
                    self.uncertain = true;
                    return Err(CancellableFailure::unreleased(io::Error::new(
                        io::ErrorKind::BrokenPipe,
                        "SPK RPC worker exited without release ACK",
                    )));
                }
            }
        }
    }

    pub(crate) fn get_view_info(&mut self, timeout: Duration) -> io::Result<ViewInfo> {
        let deadline = self.check_bound(timeout)?;
        let (reply_tx, reply_rx) = sync_mpsc::sync_channel(1);
        self.sender
            .try_send(Command::View {
                deadline,
                reply: reply_tx,
            })
            .map_err(|_| invalid("SPK RPC worker queue unavailable"))?;
        self.receive(reply_rx, deadline)
    }

    /// One already-admitted operation. The same app-side WebSession survives
    /// requests under an unchanged source projection; any effective permission
    /// or identity drift discards it before another call.
    pub(crate) fn dispatch(
        &mut self,
        binding: SessionBinding,
        request: WebRequest,
        max_response_bytes: usize,
        timeout: Duration,
    ) -> io::Result<WebResponse> {
        self.dispatch_inner(
            binding,
            request,
            max_response_bytes,
            timeout,
            Arc::new(AtomicBool::new(false)),
        )
    }

    /// One admitted caller whose hard EOF fences only its command and cached
    /// app-side session. A release witness is returned only after the worker
    /// has left that command; it says nothing about app-side effect rollback.
    /// The durable operation marker remains one-shot on every uncertainty.
    pub(crate) fn dispatch_cancellable(
        &mut self,
        binding: SessionBinding,
        request: WebRequest,
        max_response_bytes: usize,
        timeout: Duration,
        identity: DispatchIdentity,
        cancelled: Arc<AtomicBool>,
    ) -> Result<(WebResponse, DispatchFence), CancellableFailure> {
        if cancelled.load(Ordering::Acquire) {
            return Err(CancellableFailure::no_enqueue(
                io::Error::new(
                    io::ErrorKind::Interrupted,
                    "SPK caller disconnected before queue",
                ),
                identity,
            ));
        }
        let deadline = self
            .check_bound(timeout)
            .map_err(|error| CancellableFailure::no_enqueue(error, identity.clone()))?;
        if binding.app != self.app
            || binding.process_generation != self.generation
            || binding.app != identity.app
            || binding.process_generation != identity.app_generation
            || binding.session_resource.to_string() != identity.session_resource
            || max_response_bytes == 0
            || max_response_bytes > MAX_RESPONSE_BYTES
        {
            return Err(CancellableFailure::no_enqueue(
                invalid("SPK dispatch identity or response bound refused"),
                identity,
            ));
        }
        let (reply_tx, reply_rx) = sync_mpsc::sync_channel(1);
        self.sender
            .try_send(Command::Dispatch {
                binding: Box::new(binding),
                request: Box::new(request),
                max_response_bytes,
                deadline,
                cancelled: Arc::clone(&cancelled),
                reply: reply_tx,
            })
            .map_err(|_| {
                CancellableFailure::no_enqueue(
                    invalid("SPK RPC worker queue unavailable"),
                    identity.clone(),
                )
            })?;
        self.receive_cancellable(reply_rx, deadline, &cancelled, identity)
    }

    fn dispatch_inner(
        &mut self,
        binding: SessionBinding,
        request: WebRequest,
        max_response_bytes: usize,
        timeout: Duration,
        cancelled: Arc<AtomicBool>,
    ) -> io::Result<WebResponse> {
        if cancelled.load(Ordering::Acquire) {
            return Err(io::Error::new(
                io::ErrorKind::Interrupted,
                "SPK caller disconnected before enqueue",
            ));
        }
        let deadline = self.check_bound(timeout)?;
        if binding.app != self.app
            || binding.process_generation != self.generation
            || max_response_bytes == 0
            || max_response_bytes > MAX_RESPONSE_BYTES
        {
            return Err(invalid("SPK dispatch response bound refused"));
        }
        let (reply_tx, reply_rx) = sync_mpsc::sync_channel(1);
        self.sender
            .try_send(Command::Dispatch {
                binding: Box::new(binding),
                request: Box::new(request),
                max_response_bytes,
                deadline,
                cancelled: Arc::clone(&cancelled),
                reply: reply_tx,
            })
            .map_err(|_| invalid("SPK RPC worker queue unavailable"))?;
        self.receive(reply_rx, deadline)
    }

    /// One already-admitted WebSocket open. On success the worker has written
    /// the 101 to `client` and owns it: its frames flow on the worker's
    /// LocalSet until either side closes, and nothing further reaches Mini.
    /// The slot holds the grain's concurrency place until then.
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn open_web_socket(
        &mut self,
        binding: SessionBinding,
        open: WebSocketOpen,
        client: UnixStream,
        accept: String,
        limits: Limits,
        slot: Slot,
        label: String,
        timeout: Duration,
    ) -> io::Result<()> {
        let deadline = self.check_bound(timeout)?;
        if binding.app != self.app || binding.process_generation != self.generation {
            return Err(invalid("SPK WebSocket open identity refused"));
        }
        let (reply_tx, reply_rx) = sync_mpsc::sync_channel(1);
        self.sender
            .try_send(Command::OpenWebSocket {
                binding: Box::new(binding),
                open: Box::new(open),
                client,
                accept,
                limits,
                slot,
                label,
                deadline,
                reply: reply_tx,
            })
            .map_err(|_| invalid("SPK RPC worker queue unavailable"))?;
        self.receive(reply_rx, deadline)
    }

    /// Internal fixture/operations diagnostic; it conveys no authority.
    pub(crate) fn stats(&self) -> io::Result<RpcStats> {
        let (reply_tx, reply_rx) = sync_mpsc::sync_channel(1);
        self.sender
            .try_send(Command::Stats { reply: reply_tx })
            .map_err(|_| invalid("SPK RPC worker queue unavailable"))?;
        reply_rx
            .recv_timeout(Duration::from_secs(1))
            .map_err(|_| io::Error::new(io::ErrorKind::TimedOut, "SPK RPC stats unavailable"))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn dispatch_identity() -> DispatchIdentity {
        DispatchIdentity {
            permit_sha256: "a".repeat(64),
            request_digest: "1".into(),
            app: 91,
            app_generation: 2,
            invocation_id: "b".repeat(32),
            operation_id: "17".into(),
            session_resource: "6208".into(),
            session_generation: "1".into(),
            dispatch_transaction: "18".into(),
            dispatch_event: "19".into(),
        }
    }

    fn binding() -> SessionBinding {
        SessionBinding {
            app: 91,
            process_generation: 2,
            session_resource: 6208,
            subject: 8,
            projection_fingerprint: [7; 32],
            kind: SessionKind::Web,
            params: SessionParameters {
                identity_id: [8; 32],
                display_name: "Friend".into(),
                preferred_handle: "friend".into(),
                permissions: vec![true, false],
                tab_id: vec![],
                base_path: "/".into(),
                user_agent: "Mini".into(),
                acceptable_languages: vec!["en".into()],
            },
        }
    }

    #[test]
    fn session_reuse_requires_current_projection_and_full_parameter_match() {
        let original = binding();
        assert!(same_projection(
            &original.projection_fingerprint,
            &original.params,
            &original
        ));
        let mut changed_bits = original.clone();
        changed_bits.params.permissions[1] = true;
        assert!(!same_projection(
            &original.projection_fingerprint,
            &original.params,
            &changed_bits
        ));
        let mut changed_ticket = original.clone();
        changed_ticket.projection_fingerprint = [9; 32];
        assert!(!same_projection(
            &original.projection_fingerprint,
            &original.params,
            &changed_ticket
        ));
        assert_ne!(
            original.key(),
            SessionKey {
                generation: 3,
                ..original.key()
            }
        );
    }

    #[test]
    fn zero_coordinates_are_source_domain_values_not_local_authority_tests() {
        let (supervisor, app) = UnixStream::pair().unwrap();
        drop(app);
        let mut driver = RpcDriver::from_connected_stream(0, 0, supervisor).unwrap();
        let mut zero = binding();
        zero.app = 0;
        zero.process_generation = 0;
        zero.session_resource = 0;
        zero.subject = 0;
        zero.projection_fingerprint = [0; 32];
        assert_eq!(zero.key().app, 0);
        // The disconnected bridge fails as transport, not because an
        // incidental fixture-era nonzero check rejected native Nat values.
        assert!(driver
            .dispatch(
                zero,
                WebRequest {
                    method: minidregg_spk_rpc::Method::Get,
                    path_and_query: "".into(),
                    context: minidregg_spk_rpc::RequestContext::default(),
                    body: None,
                },
                1,
                Duration::from_millis(100)
            )
            .is_err());
    }

    #[test]
    fn bounded_cache_evicts_oldest_session_instead_of_exhausting() {
        assert_eq!(
            oldest_by_use([(11, 3), (12, 1), (13, 2)].into_iter()),
            Some(12)
        );
        assert_eq!(
            oldest_by_use([(11, 3), (12, 4), (13, 2)].into_iter()),
            Some(13)
        );
        assert_eq!(oldest_by_use(std::iter::empty::<(u64, u64)>()), None);
    }

    #[test]
    fn disconnected_fd3_has_no_view_or_dispatch_authority() {
        let (supervisor, app) = UnixStream::pair().unwrap();
        drop(app);
        let mut driver = RpcDriver::from_connected_stream(91, 2, supervisor).unwrap();
        assert!(driver.get_view_info(Duration::from_millis(100)).is_err());
        assert!(driver.get_view_info(Duration::ZERO).is_err());
    }

    #[test]
    fn stalled_fd3_times_out_and_poisoned_driver_cannot_resend() {
        let (supervisor, _app) = UnixStream::pair().unwrap();
        let mut driver = RpcDriver::from_connected_stream(91, 2, supervisor).unwrap();
        let start = Instant::now();
        let error = driver.get_view_info(Duration::from_millis(50)).unwrap_err();
        assert_eq!(error.kind(), io::ErrorKind::TimedOut);
        assert!(start.elapsed() < Duration::from_secs(1));
        assert!(driver.uncertain);
        assert!(driver.get_view_info(Duration::from_secs(1)).is_err());
    }

    #[test]
    fn caller_disconnect_abandons_only_its_wait_and_keeps_shared_driver_available() {
        let (supervisor, _app) = UnixStream::pair().unwrap();
        let mut driver = RpcDriver::from_connected_stream(91, 2, supervisor).unwrap();
        let cancelled = Arc::new(AtomicBool::new(false));
        cancelled.store(true, Ordering::Release);
        let before_send = driver.dispatch_cancellable(
            binding(),
            WebRequest {
                method: minidregg_spk_rpc::Method::Get,
                path_and_query: String::new(),
                context: minidregg_spk_rpc::RequestContext::default(),
                body: None,
            },
            1024,
            Duration::from_secs(1),
            dispatch_identity(),
            Arc::clone(&cancelled),
        );
        let (error, fence) = before_send.err().unwrap().into_parts();
        assert_eq!(error.kind(), io::ErrorKind::Interrupted);
        let fence = fence.expect("proven no enqueue");
        assert!(!fence.worker_released());
        assert!(fence.matches_and_consume(&dispatch_identity()));
        assert_eq!(driver.stats().unwrap().cached_sessions, 0);
        cancelled.store(false, Ordering::Release);
        let signal = Arc::clone(&cancelled);
        let watcher = std::thread::spawn(move || {
            std::thread::sleep(Duration::from_millis(25));
            signal.store(true, Ordering::Release);
        });
        let start = Instant::now();
        let result = driver.dispatch_cancellable(
            binding(),
            WebRequest {
                method: minidregg_spk_rpc::Method::Get,
                path_and_query: "repo.git/info/refs".into(),
                context: minidregg_spk_rpc::RequestContext::default(),
                body: None,
            },
            1024,
            Duration::from_secs(2),
            dispatch_identity(),
            cancelled,
        );
        watcher.join().unwrap();
        let (error, fence) = result.err().unwrap().into_parts();
        assert_eq!(error.kind(), io::ErrorKind::Interrupted);
        let fence = fence.expect("worker release ACK");
        assert!(fence.worker_released());
        assert!(fence.matches_and_consume(&dispatch_identity()));
        assert!(start.elapsed() < Duration::from_secs(1));
        assert!(!driver.uncertain);
        assert_eq!(driver.stats().unwrap().cached_sessions, 0);
    }

    #[test]
    fn prequeue_guard_abort_mints_only_exact_no_enqueue_witness() {
        let (supervisor, _app) = UnixStream::pair().unwrap();
        let mut driver = RpcDriver::from_connected_stream(91, 2, supervisor).unwrap();
        let identity = dispatch_identity();
        let guard = driver.prepare_cancellable(identity.clone()).unwrap();
        let fence = guard.abort_no_enqueue();
        assert!(!fence.worker_released());
        assert!(fence.matches_and_consume(&identity));
        assert_eq!(driver.stats().unwrap().cached_sessions, 0);

        let mut wrong = identity;
        wrong.app_generation = 3;
        assert!(driver.prepare_cancellable(wrong).is_err());
    }

    #[test]
    fn missing_worker_ack_never_creates_release_witness() {
        let (supervisor, _app) = UnixStream::pair().unwrap();
        let mut driver = RpcDriver::from_connected_stream(91, 2, supervisor).unwrap();
        let (_held_reply, receiver) = sync_mpsc::sync_channel(1);
        let cancelled = AtomicBool::new(true);
        let start = Instant::now();
        let failure = driver
            .receive_cancellable(
                receiver,
                Instant::now() + Duration::from_secs(30),
                &cancelled,
                dispatch_identity(),
            )
            .err()
            .unwrap();
        let (error, fence) = failure.into_parts();
        assert_eq!(error.kind(), io::ErrorKind::TimedOut);
        assert!(fence.is_none());
        assert!(driver.uncertain);
        assert!(start.elapsed() >= CANCEL_ACK_GRACE);
        assert!(start.elapsed() < Duration::from_secs(4));
    }

    #[test]
    fn successful_worker_reply_carries_fence_for_later_format_failure() {
        let (supervisor, _app) = UnixStream::pair().unwrap();
        let mut driver = RpcDriver::from_connected_stream(91, 2, supervisor).unwrap();
        let (sender, receiver) = sync_mpsc::sync_channel(1);
        sender
            .send(Ok(WebResponse {
                result: minidregg_spk_rpc::WebResult::Content {
                    status: 200,
                    mime_type: "text/plain".into(),
                    encoding: String::new(),
                    language: String::new(),
                    etag: None,
                    body: b"ok".to_vec(),
                    download_name: None,
                },
                headers: Vec::new(),
                set_cookies: Vec::new(),
            }))
            .unwrap();
        let (reply, fence) = driver
            .receive_cancellable(
                receiver,
                Instant::now() + Duration::from_secs(1),
                &AtomicBool::new(false),
                dispatch_identity(),
            )
            .ok()
            .unwrap();
        assert!(matches!(
            reply.result,
            minidregg_spk_rpc::WebResult::Content { status: 200, .. }
        ));
        assert!(fence.worker_released());
        assert!(fence.matches_and_consume(&dispatch_identity()));
    }
}
