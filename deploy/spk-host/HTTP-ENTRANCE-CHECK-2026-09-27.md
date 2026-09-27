# Private HTTP entrance component check — 2026-09-27

The staged `spk-hostd serve-http-unavailable` entrance accepts one bounded
HTTP/1.1 request on an owner-private Unix socket. A browser cookie or distinct
API bearer authenticates use of a fixed participant custodian; browser writes
also require the exact configured HTTPS Origin. Fetch Metadata must report
`same-origin` when present, except a safe direct GET/HEAD navigation with
`Sec-Fetch-Site: none`. Cookie issuance is a separate missing boundary.
Credential and caller `X-Sandstorm-*` fields are never forwarded. Every
authenticated request returns 503, because the native participant authoring,
special dispatch receiver and source-owned checked projection are not wired.
This check does **not** qualify Mini-authorized app access.

Source snapshot on Persvati:
`/tmp/minidregg-gitweb-smoke-20260927/source/native/spk-host`.
`http_entrance.rs` SHA-256
`67b620449225b761c6d01aa9e85a45d484c0c3d7a30ea78d3cf1146cb5e0e398`;
`lib.rs` SHA-256
`cf9f17272797b80447fd72231400883d8ef354bd919a97963c24d484ea936141`;
`bin/spk-hostd.rs` SHA-256
`30b04ab695e7e9b7660eddac04ec7cc58a7d5db809fce84f0955d0a45ae4d17a`.
The runtime source snapshot uses the pinned hardened Bread parser and the
committed `spk-rpc` crate; this component did not launch an SPK.

On Persvati, `CARGO_BUILD_JOBS=2 cargo nextest run --locked --lib -E
'test(http_entrance)'` passed 6/6 tests. They cover fixed browser/API
credentials, exact Origin/Fetch Metadata and forbidden headers, zero-length
browser POST, bodyless HEAD, control-byte refusal, a same-UID private Unix
listener with second-instance refusal and socket cleanup, a 503 response,
safe direct bookmark navigation plus cross-site refusal, and an incomplete-frame
absolute-deadline refusal. `CARGO_BUILD_JOBS=2 cargo
clippy --locked --all-targets -- -D warnings` passed. The earlier full
library suite passed 26/26 before the deadline and bookmark tests were added; it was
not rerun for this checkpoint.

No live Mini Store, signed app state, public listener, SPK process or other
service changed during this component check.
