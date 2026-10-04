# Private browser WebSocket transport

`spk-browser-proxy DIR PORT` serves the fixed `DIR/http.sock` custodian over
loopback TLS. It accepts at most 136 concurrent connections (class L's 128
WebSocket slots plus eight HTTP/handshake connections). The custodian still
checks the browser cookie, same-origin open, Mini dispatch admission and grain
class limits. The proxy adds no authorization path and interprets no frames.

An upstream HTTP 101 for an actual WebSocket upgrade switches to a bounded,
bidirectional TLS/Unix pump. Any first frame read alongside the response head
is retained. A slow consumer applies backpressure; upgraded streams have no
idle deadline. Client half-close drains pending bytes, closes the upstream write half, and
allows five seconds for the app to finish its reply/close frame; upstream EOF
sends TLS close-notify and releases the slot. STOP's WebSocket close-frame behavior remains the
resident's responsibility. Ordinary HTTP and refused upgrades retain bounded
buffering and deadlines. Initial admission still has a 30-second response-head
deadline; this transport change does not fix kernel admission latency.

The entrance is TLS 1.3 with one key-exchange group, X25519MLKEM768 (hybrid X25519 +
ML-KEM-768; rustls aws-lc-rs provider). A browser that offers no hybrid group (or only
TLS 1.2) fails the handshake: there is no classical fallback. Current Chrome, Edge and
Firefox offer it; a client built on OpenSSL older than 3.5 does not.

There is one rustls owner per connection. Its poll loop uses a 64 KiB plaintext
queue toward the app and a 64 KiB rustls outgoing buffer toward the browser.
This prevents a held socket from monopolizing the accept loop or accumulating
unbounded data. Connection slots are released on all worker exits.

Narrow test command (on Linux/build host):

```
cargo test --manifest-path native/spk-host/Cargo.toml --bin spk-browser-proxy
```

Tests use genuine TLS over TCP and an independent Unix peer: 101 plus first
frame, payloads larger than the queue in both directions, last bytes before
client close, final reply after client half-close, upstream close, ordinary HTTP, rejected/unexpected upgrades and
slot exhaustion/reuse. The committed localhost certificate/key under
`native/spk-host/tests/fixtures` are public test fixtures, never deployment
credentials. Actual app/browser qualification is a separate journey.

Browser session projection reuses the custodian's host[:port] grammar. A
loopback origin such as `https://localhost:18443` therefore reaches the app
unchanged; paths, userinfo, invalid ports and malformed hostnames still refuse.
