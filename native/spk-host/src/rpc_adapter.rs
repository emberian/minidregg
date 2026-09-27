//! Physical fd3 Sandstorm RPC driver. This module carries no Mini authority.
//!
//! A future native adapter must recheck current app generation, session,
//! subject-derived identity and effective bits for every request. Pending
//! lifecycle receipts and caller HTTP headers cannot authorize calls here.
#![allow(dead_code)] // Staged until Mini exposes a checked current-session projection.

use minidregg_spk_rpc::{
    dispatch_web, SessionParameters, SupervisorConnection, ViewInfo, WebRequest, WebResponse,
};
use minidregg_spk_rpc::web_session_capnp;
use std::collections::HashMap;
use std::io;
use std::os::unix::net::UnixStream;
use std::sync::mpsc as sync_mpsc;
use std::time::{Duration, Instant};
use tokio::runtime::Builder;
use tokio::sync::mpsc;
use tokio::task::LocalSet;

const MAX_RESPONSE_BYTES: usize = 8 * 1024 * 1024;
const MAX_CALL_TIME: Duration = Duration::from_secs(30);

fn invalid(message: &'static str) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidInput, message)
}

fn remaining(deadline: Instant) -> io::Result<Duration> {
    let left = deadline.saturating_duration_since(Instant::now());
    if left.is_zero() {
        Err(io::Error::new(io::ErrorKind::TimedOut, "SPK RPC operation deadline"))
    } else {
        Ok(left)
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
        reply: sync_mpsc::SyncSender<io::Result<WebResponse>>,
    },
    Stats {
        reply: sync_mpsc::SyncSender<RpcStats>,
    },
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) struct RpcStats {
    pub sessions_created: u64,
    pub cached_sessions: usize,
}

/// One connected fd3 for one app generation. A dedicated LocalSet drives
/// Cap'n Proto callbacks throughout its lifetime, including between calls.
/// A timeout poisons the driver: an uncertain write is never resent.
pub(crate) struct RpcDriver {
    app: u64,
    generation: u64,
    sender: mpsc::Sender<Command>,
    uncertain: bool,
}

impl RpcDriver {
    pub(crate) fn from_connected_stream(
        app: u64,
        generation: u64,
        stream: UnixStream,
    ) -> io::Result<Self> {
        if app == 0 || generation == 0 {
            return Err(invalid("invalid fixed app generation for fd3"));
        }
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
                                        .map_err(|_| io::Error::new(io::ErrorKind::TimedOut, "SPK view-info timeout"))?
                                        .map_err(io::Error::other)
                                }
                                .await;
                                let _ = reply.send(result);
                            }
                            Command::Dispatch {
                                binding, request, max_response_bytes, deadline, reply,
                            } => {
                                let result = async {
                                    let key = binding.key();
                                    if sessions
                                        .get(&key)
                                        .is_some_and(|cached| !cache_matches(cached, &binding))
                                    {
                                        sessions.remove(&key);
                                    }
                                    let session = if let Some(cached) = sessions.get(&key) {
                                        cached.client.clone()
                                    } else {
                                        if sessions.len() >= 32 {
                                            return Err(invalid("SPK live session cache full"));
                                        }
                                        let left = remaining(deadline)?;
                                        let client = tokio::time::timeout(left, async {
                                            match binding.kind {
                                                SessionKind::Web => supervisor.new_web_session(&binding.params).await,
                                                SessionKind::Api => supervisor.new_api_session(&binding.params).await,
                                            }
                                        })
                                        .await
                                        .map_err(|_| io::Error::new(io::ErrorKind::TimedOut, "SPK session timeout"))?
                                        .map_err(io::Error::other)?;
                                        sessions.insert(key, CachedSession {
                                            fingerprint: binding.projection_fingerprint,
                                            params: binding.params.clone(),
                                            client: client.clone(),
                                        });
                                        sessions_created += 1;
                                        client
                                    };
                                    let left = remaining(deadline)?;
                                    tokio::time::timeout(
                                        left,
                                        dispatch_web(&session, &request, max_response_bytes, left),
                                    )
                                    .await
                                    .map_err(|_| io::Error::new(io::ErrorKind::TimedOut, "SPK dispatch timeout"))?
                                    .map_err(io::Error::other)
                                }
                                .await;
                                let _ = reply.send(result);
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
            Ok(Ok(())) => Ok(Self { app, generation, sender, uncertain: false }),
            Ok(Err(error)) => Err(io::Error::other(error)),
            Err(_) => Err(io::Error::new(io::ErrorKind::TimedOut, "SPK RPC worker initialization timeout")),
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
                Err(io::Error::new(io::ErrorKind::TimedOut, "SPK RPC result uncertain; no automatic resend"))
            }
            Err(sync_mpsc::RecvTimeoutError::Disconnected) => {
                self.uncertain = true;
                Err(io::Error::new(io::ErrorKind::BrokenPipe, "SPK RPC worker exited"))
            }
        }
    }

    fn check_bound(&self, timeout: Duration) -> io::Result<Instant> {
        if self.uncertain || timeout.is_zero() || timeout > MAX_CALL_TIME {
            return Err(invalid("SPK RPC uncertain or timeout exceeds bound"));
        }
        Ok(Instant::now() + timeout)
    }

    pub(crate) fn get_view_info(&mut self, timeout: Duration) -> io::Result<ViewInfo> {
        let deadline = self.check_bound(timeout)?;
        let (reply_tx, reply_rx) = sync_mpsc::sync_channel(1);
        self.sender
            .try_send(Command::View { deadline, reply: reply_tx })
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
        let deadline = self.check_bound(timeout)?;
        if binding.app != self.app
            || binding.process_generation != self.generation
            || binding.session_resource == 0
            || binding.subject == 0
            || binding.projection_fingerprint == [0; 32]
            || max_response_bytes == 0
            || max_response_bytes > MAX_RESPONSE_BYTES
        {
            return Err(invalid("SPK dispatch response bound refused"));
        }
        let (reply_tx, reply_rx) = sync_mpsc::sync_channel(1);
        self.sender
            .try_send(Command::Dispatch {
                binding: Box::new(binding), request: Box::new(request),
                max_response_bytes, deadline, reply: reply_tx,
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
        reply_rx.recv_timeout(Duration::from_secs(1)).map_err(|_| {
            io::Error::new(io::ErrorKind::TimedOut, "SPK RPC stats unavailable")
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

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
        assert_ne!(original.key(), SessionKey {
            generation: 3,
            ..original.key()
        });
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
}
