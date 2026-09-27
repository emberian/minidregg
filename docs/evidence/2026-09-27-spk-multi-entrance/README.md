# One resident SPK, separate participant entrances

The staged resident start profile `mini-spk-resident-start-v2` allows 1–8
operator-pinned entrance directories. Each has its own private custodian
credential and fixed Mini app/subject/session/kind/ticket binding. Preflight
checks every directory against the app UID, checks the binding and distinct
origin/session tuples, and reads the custody files before consuming the
one-shot op26 claim. The signed bridge must expose the API path if any API
entrance is configured. Acceptance for shared use still requires two distinct
participants. The HTTP parser emits canonical relative paths; an API request
for `/` maps through the signed `/repo.git/` prefix to `repo.git/`.

After source-confirmed START completion op38 and a fresh physical unit check,
the resident binds each private Unix HTTP socket and polls them in one process.
Every accepted request uses its entrance's fixed signer/policy and the same
resident journal and fd3 RpcDriver. The transport does not select Mini subject
or permission from a cookie/bearer spelling. Dispatch still requires its own
source-owned Mini admission per request. This loop serves one request at a
time; there is no per-participant availability guarantee if one bounded
request occupies the shared app driver.

This is source/component qualification only. The public binary has no
`resident-run` command, no SPK was launched, and no native Store was changed.
The private hbox snapshot retained earlier versions of separately owned
`rpc_adapter.rs`, `sandbox.rs`, and `spawn_gate.rs`. `cargo nextest run --locked
--offline` passed 76/76 tests; strict all-target Clippy passed with two build
jobs. The poll test selected only the ready channel when two private sockets
were present. A parser-to-resident projection test checked `GET /` and
`GET /info/refs?service=git-upload-pack` against the signed API prefix. The
complete two-participant Mini GitWeb journey
remains pending the fresh INSTALL/START native lifecycle and ticket grants.

After the 76-test run, the disabled agent API parser was widened to accept
the empty canonical relative path for the signed API root. Its focused parser
test and the parser-to-resident API-root test passed 2/2, and strict all-target
Clippy passed again on the final source. The full 76-test run predates this
last parser change.

Source SHA-256s:

| File | SHA-256 |
| --- | --- |
| `native/spk-host/src/resident_service.rs` | `4562e9191f2244eba9f01a7621a9b254c85e4a882b429cd367012f3c77b89ee2` |
| `native/spk-host/src/dispatch_inspection.rs` | `5a77c6ea9b3d781efb2a54e8d2e3306acd0b9b9bb9ca3725081234e0db8353c7` |
| `native/spk-host/src/http_entrance.rs` | `d63771159d39c5e7403b5c499635c2da62e76e14e3579f3ee1fa95ca526f4a75` |
| `native/spk-host/src/agent_api_wire.rs` | `3ef7c0f40582b311f3b23d16ace8a2e8c7b25969f5a2130b2bce7d327a4fbfbe` |
| `native/spk-host/src/lib.rs` | `65bf6faa6422b4487400d28054935a030d503ee864a6e5dda8f9fe3eff94a8de` |
