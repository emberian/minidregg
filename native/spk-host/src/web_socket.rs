//! WebSockets through a grain route (SPK-HOSTING row 6). A socket is ONE
//! admitted Mini dispatch, the open (method `WEBSOCKET`, a streamed dispatch);
//! its frames are opaque bytes inside that admitted session, like a streamed
//! body, and a close writes nothing to Mini. The stream is physically limited
//! by an admission-anchored authority lease; only checked private continuity can renew it. Frames are
//! unmetered by design,
//! so the grain's size class bounds them physically: at most `ws_max_open`
//! sockets per generation (`wsConcurrencyCap`, refused before any Mini write)
//! and `ws_bytes_per_minute` per socket (`wsByteCap`, the socket is cut).

use crate::broker::SizeClass;
use crate::stream_continuity::{ContinuityBinding, ContinuityTip, VerifiedContinuity};
use base64::Engine as _;
use minidregg_spk_rpc::{send_to_app, WebSocketSession};
use sha1::{Digest, Sha1};
use std::cell::RefCell;
use std::io;
use std::io::Read as _;
use std::rc::Rc;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Arc, Mutex, Weak};
use std::time::{Duration, Instant};
use tokio::io::{AsyncReadExt, AsyncWriteExt};

/// Physical attenuation, not a Mini promise of continuing authority. The clock
/// starts before admission, so a slow or queued open cannot extend stale access.
/// The default bounds silent revocation to one minute while permitting today's
/// ~15s Mini admission. Operators may choose another positive lifetime.
pub(crate) const DEFAULT_LEASE_SECONDS: u64 = 60;

struct LeaseState {
    lifetime: Duration,
    stream_nonce: [u8; 32],
    state: Mutex<LeaseCurrent>,
    changed: tokio::sync::watch::Sender<u64>,
}

struct LeaseCurrent {
    deadline: Instant,
    ended: bool,
    attempt: u64,
    pending: Option<[u8; 32]>,
    continuity: Option<(ContinuityBinding, ContinuityTip)>,
}

#[derive(Clone)]
pub(crate) struct StreamLease(Arc<LeaseState>);
pub(crate) struct WeakStreamLease(Weak<LeaseState>);

/// Single-use local challenge. Its deadline is anchored before any authoring,
/// and the old lease remains binding while the private probe is in flight.
pub(crate) struct RenewalChallenge {
    lease: Arc<LeaseState>,
    attempt: u64,
    nonce: [u8; 32],
    deadline: Instant,
    binding: ContinuityBinding,
    tip: ContinuityTip,
}

impl RenewalChallenge {
    pub(crate) fn binding(&self) -> &ContinuityBinding {
        &self.binding
    }
    pub(crate) fn minimum_tip(&self) -> &ContinuityTip {
        &self.tip
    }
    pub(crate) fn stream_nonce_hex(&self) -> String {
        nonce_hex(&self.lease.stream_nonce)
    }
    pub(crate) fn attempt_nonce_hex(&self) -> String {
        nonce_hex(&self.nonce)
    }
    /// The original live deadline continues to bound the entire probe. A
    /// revoked/expired challenge gives blocking IO no remaining time.
    pub(crate) fn response_deadline(&self) -> Instant {
        let mut current = self
            .lease
            .state
            .lock()
            .expect("stream lease mutex poisoned");
        if check_current(&mut current).is_err() {
            return Instant::now();
        }
        current.deadline.min(self.deadline)
    }
    pub(crate) fn check(&self) -> io::Result<()> {
        let mut current = self
            .lease
            .state
            .lock()
            .expect("stream lease mutex poisoned");
        check_current(&mut current)?;
        if current.attempt != self.attempt
            || current.pending != Some(self.nonce)
            || Instant::now() >= self.deadline
        {
            return Err(lease_ended());
        }
        Ok(())
    }
}

fn nonce_hex(bytes: &[u8]) -> String {
    use std::fmt::Write;
    bytes
        .iter()
        .fold(String::with_capacity(bytes.len() * 2), |mut s, b| {
            write!(s, "{b:02x}").expect("String write");
            s
        })
}

fn fresh_nonce() -> io::Result<[u8; 32]> {
    let mut nonce = [0; 32];
    std::fs::File::open("/dev/urandom")?.read_exact(&mut nonce)?;
    Ok(nonce)
}

fn lease_ended() -> io::Error {
    io::Error::new(io::ErrorKind::PermissionDenied, "wsAuthorityLeaseEnded")
}

fn check_current(current: &mut LeaseCurrent) -> io::Result<()> {
    if current.ended || Instant::now() >= current.deadline {
        current.ended = true;
        current.pending = None;
        Err(lease_ended())
    } else {
        Ok(())
    }
}

impl WeakStreamLease {
    pub(crate) fn upgrade(&self) -> Option<StreamLease> {
        self.0.upgrade().map(StreamLease)
    }
}

impl StreamLease {
    pub(crate) fn begin(lifetime: Duration) -> io::Result<Self> {
        let deadline = Instant::now()
            .checked_add(lifetime)
            .filter(|_| !lifetime.is_zero())
            .ok_or_else(|| refuse("WebSocket lease lifetime must be positive and representable"))?;
        Ok(Self(Arc::new(LeaseState {
            lifetime,
            stream_nonce: fresh_nonce()?,
            state: Mutex::new(LeaseCurrent {
                deadline,
                ended: false,
                attempt: 0,
                pending: None,
                continuity: None,
            }),
            changed: tokio::sync::watch::channel(0).0,
        })))
    }

    pub(crate) fn downgrade(&self) -> WeakStreamLease {
        WeakStreamLease(Arc::downgrade(&self.0))
    }

    pub(crate) fn revoke(&self) {
        let mut current = self.0.state.lock().expect("stream lease mutex poisoned");
        current.ended = true;
        current.pending = None;
        self.0
            .changed
            .send_modify(|version| *version = version.wrapping_add(1));
    }

    pub(crate) fn check(&self) -> io::Result<()> {
        check_current(&mut self.0.state.lock().expect("stream lease mutex poisoned"))
    }

    pub(crate) fn bound_to(&self, expected: &ContinuityBinding) -> bool {
        self.0
            .state
            .lock()
            .expect("stream lease mutex poisoned")
            .continuity
            .as_ref()
            .is_some_and(|(binding, _)| binding == expected)
    }

    /// Attach only the committed open's source identity, never caller input.
    /// A lease cannot change its identity or be rebound following revocation.
    pub(crate) fn bind_continuity(
        &self,
        binding: ContinuityBinding,
        tip: ContinuityTip,
    ) -> io::Result<()> {
        binding.validate()?;
        tip.validate()?;
        let mut current = self.0.state.lock().expect("stream lease mutex poisoned");
        check_current(&mut current)?;
        if current.continuity.is_some() {
            return Err(refuse("stream continuity already bound"));
        }
        current.continuity = Some((binding, tip));
        Ok(())
    }

    /// Renew halfway through the current interval. Admission and prior probe
    /// latency consume this interval; already inside the window means now.
    pub(crate) fn renewal_delay(&self) -> io::Result<Duration> {
        let mut current = self.0.state.lock().expect("stream lease mutex poisoned");
        check_current(&mut current)?;
        Ok(current
            .deadline
            .checked_sub(self.0.lifetime / 2)
            .unwrap_or_else(Instant::now)
            .saturating_duration_since(Instant::now()))
    }

    pub(crate) fn begin_renewal(&self) -> io::Result<RenewalChallenge> {
        // Capture before nonce generation, locking, and all private Mini work.
        let deadline = Instant::now()
            .checked_add(self.0.lifetime)
            .ok_or_else(lease_ended)?;
        let nonce = fresh_nonce()?;
        let mut current = self.0.state.lock().expect("stream lease mutex poisoned");
        check_current(&mut current)?;
        let (binding, tip) = current
            .continuity
            .clone()
            .ok_or_else(|| refuse("stream continuity unbound"))?;
        let attempt = current.attempt.checked_add(1).ok_or_else(lease_ended)?;
        current.attempt = attempt;
        current.pending = Some(nonce);
        Ok(RenewalChallenge {
            lease: Arc::clone(&self.0),
            attempt,
            nonce,
            deadline,
            binding,
            tip,
        })
    }

    /// No raw bytes or caller claims can extend a deadline. The only input is
    /// a single-use result checked against a private source inspection.
    pub(crate) fn renew(&self, grant: VerifiedContinuity) -> io::Result<()> {
        let (challenge, tip) = grant.into_parts();
        if !Arc::ptr_eq(&self.0, &challenge.lease) {
            return Err(lease_ended());
        }
        let mut current = self.0.state.lock().expect("stream lease mutex poisoned");
        check_current(&mut current)?;
        if current.attempt != challenge.attempt
            || current.pending != Some(challenge.nonce)
            || Instant::now() >= challenge.deadline
            || challenge.deadline <= current.deadline
        {
            return Err(lease_ended());
        }
        let (binding, old_tip) = current.continuity.as_ref().ok_or_else(lease_ended)?;
        if binding != &challenge.binding {
            return Err(lease_ended());
        }
        tip.follows(old_tip)?;
        current.deadline = challenge.deadline;
        current.pending = None;
        current.continuity = Some((challenge.binding, tip));
        self.0
            .changed
            .send_modify(|version| *version = version.wrapping_add(1));
        Ok(())
    }

    pub(crate) async fn ended(&self) {
        let mut changed = self.0.changed.subscribe();
        loop {
            // Mark before reading state so a concurrent extension cannot be
            // swallowed between the state snapshot and changed().
            changed.borrow_and_update();
            let deadline = {
                let mut current = self.0.state.lock().expect("stream lease mutex poisoned");
                if check_current(&mut current).is_err() {
                    return;
                }
                current.deadline
            };
            tokio::select! {
                biased;
                _ = changed.changed() => {},
                _ = tokio::time::sleep_until(deadline.into()) => {},
            }
        }
    }
}

/// RFC 6455 §1.3.
const ACCEPT_GUID: &str = "258EAFA5-E914-47DA-95CA-C5AB0DC85B11";
const READ_CHUNK: usize = 64 * 1024;
const NANOS_PER_MINUTE: u128 = 60_000_000_000;

fn refuse(reason: &'static str) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidData, reason)
}

/// The validated client half of an RFC 6455 opening handshake.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Handshake {
    /// `Sec-WebSocket-Accept` for the client's key.
    pub accept: String,
}

/// RFC 6455 §4.2.1: a GET with `Upgrade: websocket`, a `Connection` list
/// holding `upgrade`, a key that is the base64 of 16 bytes, and version 13.
pub(crate) fn client_handshake(
    connection: Option<&str>,
    upgrade: &str,
    key: Option<&str>,
    version: Option<&str>,
) -> io::Result<Handshake> {
    if !upgrade.eq_ignore_ascii_case("websocket") {
        return Err(refuse("unsupported HTTP upgrade"));
    }
    if !connection.is_some_and(|value| {
        value
            .split(',')
            .any(|token| token.trim().eq_ignore_ascii_case("upgrade"))
    }) {
        return Err(refuse("WebSocket upgrade without Connection: upgrade"));
    }
    if version != Some("13") {
        return Err(refuse("WebSocket version is not 13"));
    }
    let key = key.ok_or_else(|| refuse("WebSocket key missing"))?;
    let decoded = base64::engine::general_purpose::STANDARD
        .decode(key)
        .map_err(|_| refuse("WebSocket key is not base64"))?;
    if decoded.len() != 16 || key.len() != 24 {
        return Err(refuse("WebSocket key is not 16 bytes"));
    }
    Ok(Handshake {
        accept: accept_for(key),
    })
}

pub(crate) fn accept_for(key: &str) -> String {
    let mut hash = Sha1::new();
    hash.update(key.as_bytes());
    hash.update(ACCEPT_GUID.as_bytes());
    base64::engine::general_purpose::STANDARD.encode(hash.finalize())
}

/// The requested subprotocols, in order (`Sec-WebSocket-Protocol`).
pub(crate) fn protocols(header: Option<&str>) -> io::Result<Vec<String>> {
    let Some(header) = header else {
        return Ok(Vec::new());
    };
    let list: Vec<String> = header
        .split(',')
        .map(|token| token.trim().to_owned())
        .collect();
    if list.len() > 32
        || !list.iter().all(|token| {
            !token.is_empty()
                && token.len() <= 256
                && token
                    .bytes()
                    .all(|byte| byte.is_ascii_alphanumeric() || b"!#$%&'*+-.^_`|~".contains(&byte))
        })
    {
        return Err(refuse("WebSocket subprotocol list refused"));
    }
    Ok(list)
}

/// The 101 that completes the handshake. Hop-by-hop: `Upgrade` and
/// `Connection` are this hop's; nothing the app returned is forwarded except
/// its chosen subprotocol, and no extension is ever accepted.
pub(crate) fn switching_protocols(accept: &str, chosen: &[String]) -> Vec<u8> {
    let mut head = format!(
        "HTTP/1.1 101 Switching Protocols\r\nUpgrade: websocket\r\nConnection: Upgrade\r\nSec-WebSocket-Accept: {accept}\r\n"
    );
    if !chosen.is_empty() {
        head.push_str(&format!(
            "Sec-WebSocket-Protocol: {}\r\n",
            chosen.join(", ")
        ));
    }
    head.push_str("\r\n");
    head.into_bytes()
}

/// A named physical refusal the handshake can carry, before any Mini write.
pub(crate) fn cap_refusal(name: &str) -> Vec<u8> {
    let body = format!("{name}\n");
    format!(
        "HTTP/1.1 429 Too Many Requests\r\nContent-Type: text/plain; charset=utf-8\r\nContent-Length: {}\r\nX-Mini-Refusal: {name}\r\nCache-Control: no-store\r\nConnection: close\r\n\r\n{body}",
        body.len()
    )
    .into_bytes()
}

/// The grain's caps, from its size class.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct Limits {
    pub class: &'static str,
    pub max_open: usize,
    pub bytes_per_minute: u64,
}

impl From<SizeClass> for Limits {
    fn from(class: SizeClass) -> Self {
        Self {
            class: class.name,
            max_open: class.ws_max_open,
            bytes_per_minute: class.ws_bytes_per_minute,
        }
    }
}

/// The open sockets of one grain generation. A slot is reserved before the
/// open's Mini dispatch is authored, so the open past the cap never writes.
#[derive(Clone, Default)]
pub(crate) struct OpenSockets(Arc<AtomicUsize>);

impl OpenSockets {
    pub(crate) fn reserve(&self, limits: &Limits) -> Result<Slot, &'static str> {
        let mut current = self.0.load(Ordering::Acquire);
        loop {
            if current >= limits.max_open {
                return Err("wsConcurrencyCap");
            }
            match self
                .0
                .compare_exchange(current, current + 1, Ordering::AcqRel, Ordering::Acquire)
            {
                Ok(_) => return Ok(Slot(Arc::clone(&self.0))),
                Err(actual) => current = actual,
            }
        }
    }

    pub(crate) fn open(&self) -> usize {
        self.0.load(Ordering::Acquire)
    }
}

/// One held socket; dropping it frees the place.
pub(crate) struct Slot(Arc<AtomicUsize>);

impl Drop for Slot {
    fn drop(&mut self) {
        self.0.fetch_sub(1, Ordering::AcqRel);
    }
}

/// Bytes per minute as a token bucket that holds at most one minute's worth.
/// Tokens are kept scaled by nanoseconds-per-minute, so refill is exact.
pub(crate) struct ByteBudget {
    per_minute: u128,
    scaled: u128,
    last: Instant,
}

impl ByteBudget {
    pub(crate) fn new(per_minute: u64, now: Instant) -> Self {
        let per_minute = u128::from(per_minute);
        Self {
            per_minute,
            scaled: per_minute * NANOS_PER_MINUTE,
            last: now,
        }
    }

    /// Spend `bytes`; false when the socket has passed its cap.
    pub(crate) fn take(&mut self, bytes: usize, now: Instant) -> bool {
        let elapsed = now.saturating_duration_since(self.last).as_nanos();
        self.last = now;
        let full = self.per_minute * NANOS_PER_MINUTE;
        self.scaled = full.min(
            self.scaled
                .saturating_add(elapsed.saturating_mul(self.per_minute)),
        );
        let wanted = (bytes as u128) * NANOS_PER_MINUTE;
        if wanted > self.scaled {
            return false;
        }
        self.scaled -= wanted;
        true
    }
}

enum End {
    Client,
    App,
    Cut,
    Authority,
    Failed(String),
}

/// Closing the physical stream also stops its continuity worker, even when
/// that worker currently owns another strong lease reference.
struct CloseLeaseOnDrop(StreamLease);
impl Drop for CloseLeaseOnDrop {
    fn drop(&mut self) {
        self.0.revoke();
    }
}

/// Carry opaque bytes both ways until either side ends or the socket passes
/// its byte cap or authority lease. Each new byte chunk checks the lease before
/// forwarding; expiry also cancels stalled reads/writes. Bytes already handed
/// to the app/OS may finish after cancellation and are not rolled back. Ends the app side by dropping its `serverStream`; writes
/// nothing to Mini. Runs on the fd3 worker's LocalSet.
pub(crate) async fn pump(
    client: std::os::unix::net::UnixStream,
    session: WebSocketSession,
    limits: Limits,
    slot: Slot,
    label: String,
    lease: StreamLease,
) {
    let _slot = slot;
    let _close_lease = CloseLeaseOnDrop(lease.clone());
    let WebSocketSession {
        to_app,
        mut from_app,
        ..
    } = session;
    let stream = match client
        .set_nonblocking(true)
        .and_then(|()| tokio::net::UnixStream::from_std(client))
    {
        Ok(stream) => stream,
        Err(error) => {
            eprintln!("spk-host: websocket {label} transport unavailable: {error}");
            return;
        }
    };
    let (mut reader, mut writer) = stream.into_split();
    let budget = Rc::new(RefCell::new(ByteBudget::new(
        limits.bytes_per_minute,
        Instant::now(),
    )));
    let carried = Rc::new(RefCell::new((0_u64, 0_u64)));
    let up = {
        let budget = Rc::clone(&budget);
        let carried = Rc::clone(&carried);
        let to_app = to_app.clone();
        let lease = lease.clone();
        async move {
            let mut buffer = vec![0_u8; READ_CHUNK];
            loop {
                let count = match reader.read(&mut buffer).await {
                    Ok(0) => return End::Client,
                    Ok(count) => count,
                    Err(error) => return End::Failed(format!("client read: {error}")),
                };
                if !budget.borrow_mut().take(count, Instant::now()) {
                    return End::Cut;
                }
                if lease.check().is_err() {
                    return End::Authority;
                }
                carried.borrow_mut().0 += count as u64;
                if let Err(error) = send_to_app(&to_app, &buffer[..count]).await {
                    return End::Failed(format!("app sendBytes: {error}"));
                }
            }
        }
    };
    let down = {
        let budget = Rc::clone(&budget);
        let carried = Rc::clone(&carried);
        let lease = lease.clone();
        async move {
            while let Some(bytes) = from_app.recv().await {
                if !budget.borrow_mut().take(bytes.len(), Instant::now()) {
                    return End::Cut;
                }
                if lease.check().is_err() {
                    return End::Authority;
                }
                carried.borrow_mut().1 += bytes.len() as u64;
                if let Err(error) = writer.write_all(&bytes).await {
                    return End::Failed(format!("client write: {error}"));
                }
            }
            let _ = writer.shutdown().await;
            End::App
        }
    };
    let end = tokio::select! {
        biased;
        _ = lease.ended() => End::Authority,
        end = up => end,
        end = down => end,
    };
    drop(to_app);
    let (up_bytes, down_bytes) = *carried.borrow();
    match end {
        End::Authority => eprintln!("spk-host: websocket {label} cut: wsAuthorityLeaseEnded (carried {up_bytes} up, {down_bytes} down)"),
        End::Cut => eprintln!(
            "spk-host: websocket {label} cut: wsByteCap ({} bytes/min, class {}; carried {up_bytes} up, {down_bytes} down)",
            limits.bytes_per_minute, limits.class
        ),
        End::Failed(reason) => eprintln!(
            "spk-host: websocket {label} ended: {reason} (carried {up_bytes} up, {down_bytes} down)"
        ),
        End::Client | End::App => eprintln!(
            "spk-host: websocket {label} closed by the {} (carried {up_bytes} up, {down_bytes} down)",
            if matches!(end, End::Client) { "client" } else { "app" }
        ),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::time::Duration;

    fn renewable(lifetime: Duration) -> StreamLease {
        let lease = StreamLease::begin(lifetime).unwrap();
        lease
            .bind_continuity(
                crate::stream_continuity::ContinuityBinding {
                    domain: "1".into(),
                    semantics: "2".into(),
                    app: "91".into(),
                    app_generation: "2".into(),
                    session: "6208".into(),
                    session_generation: "1".into(),
                    subject: "8".into(),
                    ticket_resource: "6000".into(),
                    session_fingerprint: [0; 32],
                },
                crate::stream_continuity::ContinuityTip {
                    height: "10".into(),
                    chain: None,
                    world_root: "42".into(),
                },
            )
            .unwrap();
        lease
    }

    #[test]
    fn renewal_never_resurrects_and_pending_probe_does_not_delay_expiry() {
        let runtime = tokio::runtime::Builder::new_current_thread()
            .enable_all()
            .build()
            .unwrap();
        runtime.block_on(async {
            let l = renewable(Duration::from_millis(40));
            let challenge = l.begin_renewal().unwrap();
            let tip = challenge.minimum_tip().clone();
            let grant = VerifiedContinuity::fixture(challenge, tip);
            tokio::time::timeout(Duration::from_millis(200), l.ended())
                .await
                .unwrap();
            assert!(l.renew(grant).is_err());
            assert!(l.begin_renewal().is_err());
            assert!(l.check().is_err());
        });
    }

    #[test]
    fn renewal_schedule_and_io_remain_inside_old_deadline() {
        let lease = renewable(Duration::from_secs(2));
        let delay = lease.renewal_delay().unwrap();
        assert!(delay > Duration::from_millis(500) && delay <= Duration::from_secs(1));
        let challenge = lease.begin_renewal().unwrap();
        assert_eq!(
            challenge.response_deadline(),
            lease.0.state.lock().unwrap().deadline
        );
        lease.0.state.lock().unwrap().deadline = Instant::now() + Duration::from_millis(10);
        assert_eq!(lease.renewal_delay().unwrap(), Duration::ZERO);
        lease.revoke();
        assert!(challenge.response_deadline() <= Instant::now());
        assert!(lease.renewal_delay().is_err());
    }

    #[test]
    fn renewal_reply_uses_request_start_and_superseded_grant_is_single_use() {
        let lease = renewable(Duration::from_secs(5));
        let first = lease.begin_renewal().unwrap();
        let tip = first.minimum_tip().clone();
        let first = VerifiedContinuity::fixture(first, tip);
        let second = lease.begin_renewal().unwrap();
        let expected = second.deadline;
        let tip = second.minimum_tip().clone();
        let second = VerifiedContinuity::fixture(second, tip);
        assert!(lease.renew(first).is_err());
        std::thread::sleep(Duration::from_millis(10));
        lease.renew(second).unwrap();
        let state = lease.0.state.lock().unwrap();
        assert_eq!(state.deadline, expected);
        assert!(state.pending.is_none());
    }

    struct RecordingStream(tokio::sync::mpsc::UnboundedSender<Vec<u8>>);
    impl minidregg_spk_rpc::web_session_capnp::web_session::web_socket_stream::Server
        for RecordingStream
    {
        async fn send_bytes(
            self: capnp::capability::Rc<Self>,
            params: minidregg_spk_rpc::web_session_capnp::web_session::web_socket_stream::SendBytesParams,
        ) -> capnp::Result<()> {
            self.0
                .send(params.get()?.get_message()?.to_vec())
                .map_err(|_| capnp::Error::failed("closed".into()))
        }
    }

    #[test]
    fn pump_closure_ends_continuity_even_with_worker_reference() {
        let runtime = tokio::runtime::Builder::new_current_thread()
            .enable_all()
            .build()
            .unwrap();
        tokio::task::LocalSet::new().block_on(&runtime, async {
            let lease = renewable(Duration::from_secs(60));
            let (client, host) = std::os::unix::net::UnixStream::pair().unwrap();
            let (tx, _reads) = tokio::sync::mpsc::unbounded_channel();
            let (_writes, rx) = tokio::sync::mpsc::channel(16);
            let session = WebSocketSession {
                protocols: vec![],
                to_app: capnp_rpc::new_client(RecordingStream(tx)),
                from_app: rx,
            };
            let sockets = OpenSockets::default();
            let limits = Limits {
                class: "S",
                max_open: 2,
                bytes_per_minute: 1_000_000,
            };
            drop(client);
            tokio::time::timeout(
                Duration::from_millis(200),
                pump(
                    host,
                    session,
                    limits,
                    sockets.reserve(&limits).unwrap(),
                    "close-test".into(),
                    lease.clone(),
                ),
            )
            .await
            .unwrap();
            assert!(lease.check().is_err());
            assert!(lease.begin_renewal().is_err());
            assert_eq!(sockets.open(), 0);
        });
    }

    #[test]
    fn live_pump_survives_initial_deadline_then_revocation_cuts_both_directions() {
        let runtime = tokio::runtime::Builder::new_current_thread()
            .enable_all()
            .build()
            .unwrap();
        tokio::task::LocalSet::new().block_on(&runtime, async {
            let lease = renewable(Duration::from_secs(1));
            let (client, host) = std::os::unix::net::UnixStream::pair().unwrap();
            client.set_nonblocking(true).unwrap();
            let mut client = tokio::net::UnixStream::from_std(client).unwrap();
            let (tx, mut reads) = tokio::sync::mpsc::unbounded_channel();
            let (writes, rx) = tokio::sync::mpsc::channel(16);
            let session = WebSocketSession {
                protocols: vec![],
                to_app: capnp_rpc::new_client(RecordingStream(tx)),
                from_app: rx,
            };
            let sockets = OpenSockets::default();
            let limits = Limits {
                class: "S",
                max_open: 2,
                bytes_per_minute: 1_000_000,
            };
            let task = tokio::task::spawn_local(pump(
                host,
                session,
                limits,
                sockets.reserve(&limits).unwrap(),
                "renewal-test".into(),
                lease.clone(),
            ));
            for _ in 0..3 {
                tokio::time::sleep(Duration::from_millis(400)).await;
                let challenge = lease.begin_renewal().unwrap();
                let tip = challenge.minimum_tip().clone();
                lease
                    .renew(VerifiedContinuity::fixture(challenge, tip))
                    .unwrap();
                client.write_all(b"in").await.unwrap();
                assert_eq!(reads.recv().await.unwrap(), b"in");
                writes.send(b"out".to_vec()).await.unwrap();
                let mut out = [0; 3];
                client.read_exact(&mut out).await.unwrap();
                assert_eq!(&out, b"out");
            }
            assert!(lease.check().is_ok()); // 1200ms > the initial 1000ms deadline.
            client.write_all(b"forbidden").await.unwrap();
            writes.send(b"forbidden".to_vec()).await.unwrap();
            lease.revoke();
            tokio::time::timeout(Duration::from_millis(100), task)
                .await
                .unwrap()
                .unwrap();
            assert!(reads.recv().await.is_none());
            assert!(writes.send(b"later".to_vec()).await.is_err());
            assert_eq!(sockets.open(), 0);
            let mut out = [0; 32];
            assert!(!matches!(client.read(&mut out).await,Ok(n) if n > 0));
        });
    }

    #[test]
    fn rfc6455_sample_key_accepts() {
        // RFC 6455 §1.3's worked example.
        let handshake = client_handshake(
            Some("keep-alive, Upgrade"),
            "websocket",
            Some("dGhlIHNhbXBsZSBub25jZQ=="),
            Some("13"),
        )
        .unwrap();
        assert_eq!(handshake.accept, "s3pPLMBiTxaQ9kYGzzhZRbK+xOo=");
    }

    #[test]
    fn malformed_handshakes_refuse() {
        let key = Some("dGhlIHNhbXBsZSBub25jZQ==");
        assert!(client_handshake(Some("upgrade"), "h2c", key, Some("13")).is_err());
        assert!(client_handshake(Some("keep-alive"), "websocket", key, Some("13")).is_err());
        assert!(client_handshake(None, "websocket", key, Some("13")).is_err());
        assert!(client_handshake(Some("upgrade"), "websocket", key, Some("8")).is_err());
        assert!(client_handshake(Some("upgrade"), "websocket", None, Some("13")).is_err());
        assert!(
            client_handshake(Some("upgrade"), "websocket", Some("c2hvcnQ="), Some("13")).is_err()
        );
    }

    #[test]
    fn subprotocols_are_tokens_in_order() {
        assert_eq!(protocols(None).unwrap(), Vec::<String>::new());
        assert_eq!(
            protocols(Some("chat, superchat")).unwrap(),
            ["chat", "superchat"]
        );
        assert!(protocols(Some("chat, ")).is_err());
        assert!(protocols(Some("a b")).is_err());
    }

    #[test]
    fn switching_protocols_head_is_hop_by_hop_only() {
        let head = String::from_utf8(switching_protocols("abc=", &[])).unwrap();
        assert_eq!(
            head,
            "HTTP/1.1 101 Switching Protocols\r\nUpgrade: websocket\r\nConnection: Upgrade\r\nSec-WebSocket-Accept: abc=\r\n\r\n"
        );
        assert!(
            String::from_utf8(switching_protocols("abc=", &["chat".into()]))
                .unwrap()
                .contains("\r\nSec-WebSocket-Protocol: chat\r\n")
        );
        assert!(String::from_utf8(cap_refusal("wsConcurrencyCap"))
            .unwrap()
            .starts_with("HTTP/1.1 429 Too Many Requests\r\n"));
    }

    /// Both poles of the class cap: class S admits its 32nd open and refuses
    /// the 33rd by name; a closed socket frees its place.
    #[test]
    fn class_s_admits_the_32nd_open_and_refuses_the_33rd() {
        let limits = Limits::from(crate::broker::class("S").unwrap());
        assert_eq!(limits.max_open, 32);
        let open = OpenSockets::default();
        let mut held: Vec<Slot> = (0..31).map(|_| open.reserve(&limits).unwrap()).collect();
        held.push(open.reserve(&limits).expect("the 32nd open is admitted"));
        assert_eq!(open.open(), 32);
        assert_eq!(open.reserve(&limits).err(), Some("wsConcurrencyCap"));
        assert_eq!(open.open(), 32);
        held.pop();
        assert_eq!(open.open(), 31);
        held.push(open.reserve(&limits).expect("a freed place is reusable"));
        assert_eq!(open.reserve(&limits).err(), Some("wsConcurrencyCap"));
    }

    /// Both poles of the byte cap: a socket may carry one minute's bytes at
    /// once, is cut one byte past it, and refills at the class rate.
    #[test]
    fn byte_budget_cuts_one_byte_past_a_minute_and_refills() {
        let per_minute = crate::broker::class("S").unwrap().ws_bytes_per_minute;
        let t0 = Instant::now();
        let mut budget = ByteBudget::new(per_minute, t0);
        assert!(budget.take(per_minute as usize, t0));
        assert!(!budget.take(1, t0));
        let one_second = t0 + Duration::from_secs(1);
        let refill = (per_minute / 60) as usize;
        assert!(budget.take(refill, one_second));
        assert!(!budget.take(1, one_second));
        let later = one_second + Duration::from_secs(3600);
        assert!(budget.take(per_minute as usize, later));
        assert!(!budget.take(1, later));
    }
}
