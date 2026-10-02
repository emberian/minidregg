//! WebSockets through a grain route (SPK-HOSTING row 6). A socket is ONE
//! admitted Mini dispatch, the open (method `WEBSOCKET`, a streamed dispatch);
//! its frames are opaque bytes inside that admitted session, like a streamed
//! body, and a close writes nothing to Mini. The stream is physically limited
//! by an admission-anchored authority lease; it never renews itself. Frames are
//! unmetered by design,
//! so the grain's size class bounds them physically: at most `ws_max_open`
//! sockets per generation (`wsConcurrencyCap`, refused before any Mini write)
//! and `ws_bytes_per_minute` per socket (`wsByteCap`, the socket is cut).

use crate::broker::SizeClass;
use base64::Engine as _;
use minidregg_spk_rpc::{send_to_app, WebSocketSession};
use sha1::{Digest, Sha1};
use std::cell::RefCell;
use std::io;
use std::rc::Rc;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Arc, Weak};
use std::time::{Duration, Instant};
use tokio::io::{AsyncReadExt, AsyncWriteExt};

/// Physical attenuation, not a Mini promise of continuing authority. The clock
/// starts before admission, so a slow or queued open cannot extend stale access.
/// The default bounds silent revocation to one minute while permitting today's
/// ~15s Mini admission. Operators may choose another positive lifetime.
pub(crate) const DEFAULT_LEASE_SECONDS: u64 = 60;

struct LeaseState {
    deadline: Instant,
    revoked: tokio::sync::watch::Sender<bool>,
}

#[derive(Clone)]
pub(crate) struct StreamLease(Arc<LeaseState>);

pub(crate) struct WeakStreamLease(Weak<LeaseState>);

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
            deadline,
            revoked: tokio::sync::watch::channel(false).0,
        })))
    }

    pub(crate) fn downgrade(&self) -> WeakStreamLease {
        WeakStreamLease(Arc::downgrade(&self.0))
    }

    pub(crate) fn revoke(&self) {
        self.0.revoked.send_replace(true);
    }

    pub(crate) fn check(&self) -> io::Result<()> {
        if *self.0.revoked.borrow() || Instant::now() >= self.0.deadline {
            Err(io::Error::new(
                io::ErrorKind::PermissionDenied,
                "wsAuthorityLeaseEnded",
            ))
        } else {
            Ok(())
        }
    }

    pub(crate) async fn ended(&self) {
        let mut revoked = self.0.revoked.subscribe();
        tokio::select! {
            biased;
            _ = async {
                while !*revoked.borrow_and_update() {
                    if revoked.changed().await.is_err() { break; }
                }
            } => {},
            _ = tokio::time::sleep_until(self.0.deadline.into()) => {},
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
        head.push_str(&format!("Sec-WebSocket-Protocol: {}\r\n", chosen.join(", ")));
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
            match self.0.compare_exchange(
                current,
                current + 1,
                Ordering::AcqRel,
                Ordering::Acquire,
            ) {
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
        self.scaled = full.min(self.scaled.saturating_add(elapsed.saturating_mul(self.per_minute)));
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
                if lease.check().is_err() { return End::Authority; }
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
                if lease.check().is_err() { return End::Authority; }
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
        assert!(client_handshake(Some("upgrade"), "websocket", Some("c2hvcnQ="), Some("13")).is_err());
    }

    #[test]
    fn subprotocols_are_tokens_in_order() {
        assert_eq!(protocols(None).unwrap(), Vec::<String>::new());
        assert_eq!(protocols(Some("chat, superchat")).unwrap(), ["chat", "superchat"]);
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
        assert!(String::from_utf8(switching_protocols("abc=", &["chat".into()]))
            .unwrap()
            .contains("\r\nSec-WebSocket-Protocol: chat\r\n"));
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
