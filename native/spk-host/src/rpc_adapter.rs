//! Physical fd3 Sandstorm RPC driver. This module carries no Mini authority.
//!
//! A future native adapter must recheck current app generation, session,
//! subject-derived identity and effective bits for every request. Pending
//! lifecycle receipts and caller HTTP headers cannot authorize calls here.
#![allow(dead_code)] // Staged until Mini exposes a checked current-session projection.

use minidregg_spk_rpc::{
    dispatch_web, SessionParameters, SupervisorConnection, ViewInfo, WebRequest, WebResponse,
};
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
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum SessionKind {
    Web,
    Api,
}

enum Command {
    View {
        deadline: Instant,
        reply: sync_mpsc::SyncSender<io::Result<ViewInfo>>,
    },
    Dispatch {
        kind: SessionKind,
        params: Box<SessionParameters>,
        request: Box<WebRequest>,
        max_response_bytes: usize,
        deadline: Instant,
        reply: sync_mpsc::SyncSender<io::Result<WebResponse>>,
    },
}

/// One connected fd3 for one app generation. A dedicated LocalSet drives
/// Cap'n Proto callbacks throughout its lifetime, including between calls.
/// A timeout poisons the driver: an uncertain write is never resent.
pub(crate) struct RpcDriver {
    sender: mpsc::Sender<Command>,
    uncertain: bool,
}

impl RpcDriver {
    pub(crate) fn from_connected_stream(stream: UnixStream) -> io::Result<Self> {
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
                                kind, params, request, max_response_bytes, deadline, reply,
                            } => {
                                let result = async {
                                    let left = remaining(deadline)?;
                                    let session = tokio::time::timeout(left, async {
                                        match kind {
                                            SessionKind::Web => supervisor.new_web_session(&params).await,
                                            SessionKind::Api => supervisor.new_api_session(&params).await,
                                        }
                                    })
                                    .await
                                    .map_err(|_| io::Error::new(io::ErrorKind::TimedOut, "SPK session timeout"))?
                                    .map_err(io::Error::other)?;
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
                        }
                    }
                });
            })?;
        match ready_rx.recv_timeout(Duration::from_secs(2)) {
            Ok(Ok(())) => Ok(Self { sender, uncertain: false }),
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

    /// One already-admitted operation. A fresh app-side session is created per
    /// request; generic stateful WebSession continuity is not claimed yet.
    pub(crate) fn dispatch(
        &mut self,
        kind: SessionKind,
        params: SessionParameters,
        request: WebRequest,
        max_response_bytes: usize,
        timeout: Duration,
    ) -> io::Result<WebResponse> {
        let deadline = self.check_bound(timeout)?;
        if max_response_bytes == 0 || max_response_bytes > MAX_RESPONSE_BYTES {
            return Err(invalid("SPK dispatch response bound refused"));
        }
        let (reply_tx, reply_rx) = sync_mpsc::sync_channel(1);
        self.sender
            .try_send(Command::Dispatch {
                kind, params: Box::new(params), request: Box::new(request),
                max_response_bytes, deadline, reply: reply_tx,
            })
            .map_err(|_| invalid("SPK RPC worker queue unavailable"))?;
        self.receive(reply_rx, deadline)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn disconnected_fd3_has_no_view_or_dispatch_authority() {
        let (supervisor, app) = UnixStream::pair().unwrap();
        drop(app);
        let mut driver = RpcDriver::from_connected_stream(supervisor).unwrap();
        assert!(driver.get_view_info(Duration::from_millis(100)).is_err());
        assert!(driver.get_view_info(Duration::ZERO).is_err());
    }

    #[test]
    fn stalled_fd3_times_out_and_poisoned_driver_cannot_resend() {
        let (supervisor, _app) = UnixStream::pair().unwrap();
        let mut driver = RpcDriver::from_connected_stream(supervisor).unwrap();
        let start = Instant::now();
        let error = driver.get_view_info(Duration::from_millis(50)).unwrap_err();
        assert_eq!(error.kind(), io::ErrorKind::TimedOut);
        assert!(start.elapsed() < Duration::from_secs(1));
        assert!(driver.uncertain);
        assert!(driver.get_view_info(Duration::from_secs(1)).is_err());
    }
}
