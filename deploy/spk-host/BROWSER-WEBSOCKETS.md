# Private browser WebSocket transport

`spk-browser-proxy DIR PORT` serves the fixed `DIR/http.sock` custodian over
loopback TLS. It accepts at most 136 concurrent connections (class L's 128
WebSocket slots plus eight HTTP/handshake connections). The custodian still
checks the browser cookie, same-origin open, Mini dispatch admission and grain
class limits. The proxy adds no authorization path and interprets no frames.

An upstream HTTP 101 for an actual WebSocket upgrade switches to a bounded,
bidirectional TLS/Unix pump. Any first frame read alongside the response head
is retained. A slow consumer applies backpressure; upgraded streams have no
idle deadline. Client close releases the upstream and its slot, and upstream
close sends TLS close-notify. STOP's WebSocket close-frame behavior remains the
resident's responsibility. Ordinary HTTP and refused upgrades retain bounded
buffering and deadlines. Initial admission still has a 30-second response-head
deadline; this transport change does not fix kernel admission latency.

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
client close, upstream close, ordinary HTTP, rejected/unexpected upgrades and
slot exhaustion/reuse. The committed localhost certificate/key under
`native/spk-host/tests/fixtures` are public test fixtures, never deployment
credentials. Actual app/browser qualification is a separate journey.
